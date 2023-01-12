(* Distributed under the terms of the MIT license. *)
From Coq Require Import Uint63 FloatOps FloatAxioms.
From MetaCoq.Common Require Import config utils AstUtils MonadAst MonadBasicAst Primitive EnvMap.
From MetaCoq.Common Require.CommonProgram.
From MetaCoq.Common Require.CommonMonad.Core.
From MetaCoq.Common Require Import.CommonMonad.Common monad_utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICPrimitive PCUICCases PCUICProgram.CommonToPCUIC.

Import MCMonadNotation.

Section with_tc.
  Context {TM : TMInstance}.
  Local Notation.CommonMonad := (.CommonMonad TM).
  Context {M : Monad.CommonMonad}.

  Section helpers.
    Context (monad_trans : Ast.term ->.CommonMonad term).

    Definition monad_trans_decl' (d : Ast.Env.context_decl) :=
      decl_body <- monad_option_map monad_trans d.(decl_body);;
      decl_type <- monad_trans d.(decl_type);;
      ret {| decl_name := d.(decl_name);
            decl_body := decl_body;
            decl_type := decl_type |}.

    Definition monad_trans_local' Γ := monad_map monad_trans_decl' Γ.

    Definition monad_trans_constructor_body' (d : Ast.Env.constructor_body) :=
      cstr_args <- monad_trans_local' d.(Ast.Env.cstr_args);;
      cstr_indices <- monad_map monad_trans d.(Ast.Env.cstr_indices);;
      cstr_type <- monad_trans d.(Ast.Env.cstr_type);;
      ret {| cstr_name := d.(Ast.Env.cstr_name);
            cstr_args := cstr_args;
            cstr_indices := cstr_indices;
            cstr_type := cstr_type;
            cstr_arity := d.(Ast.Env.cstr_arity) |}.
    Definition monad_trans_projection_body' (d : Ast.Env.projection_body) :=
      proj_type <- monad_trans d.(Ast.Env.proj_type);;
      ret {| proj_name := d.(Ast.Env.proj_name);
            proj_type := proj_type;
            proj_relevance := d.(Ast.Env.proj_relevance) |}.

    Definition monad_trans_one_ind_body' (d : Ast.Env.one_inductive_body) :=
      ind_indices <- monad_trans_local' d.(Ast.Env.ind_indices);;
      ind_type <- monad_trans d.(Ast.Env.ind_type);;
      ind_ctors <- monad_map monad_trans_constructor_body' d.(Ast.Env.ind_ctors);;
      ind_projs <- monad_map monad_trans_projection_body' d.(Ast.Env.ind_projs);;
      ret {| ind_name := d.(Ast.Env.ind_name);
            ind_relevance := d.(Ast.Env.ind_relevance);
            ind_indices := ind_indices;
            ind_sort := d.(Ast.Env.ind_sort);
            ind_type := ind_type;
            ind_kelim := d.(Ast.Env.ind_kelim);
            ind_ctors := ind_ctors;
            ind_projs := ind_projs |}.

    Definition monad_trans_constant_body' bd :=
      cst_type <- monad_trans bd.(Ast.Env.cst_type);;
      cst_body <- monad_option_map monad_trans bd.(Ast.Env.cst_body);;
      ret {| cst_type := cst_type;
            cst_body := cst_body;
            cst_universes := bd.(Ast.Env.cst_universes);
            cst_relevance := bd.(Ast.Env.cst_relevance) |}.

    Definition monad_trans_minductive_body' md :=
      ind_params <- monad_trans_local' md.(Ast.Env.ind_params);;
      ind_bodies <- monad_map monad_trans_one_ind_body' md.(Ast.Env.ind_bodies);;
      ret {| ind_finite := md.(Ast.Env.ind_finite);
            ind_npars := md.(Ast.Env.ind_npars);
            ind_params := ind_params;
            ind_bodies := ind_bodies;
            ind_universes := md.(Ast.Env.ind_universes);
            ind_variance := md.(Ast.Env.ind_variance) |}.

    Definition monad_trans_global_decl' (d : Ast.Env.global_decl) :=
      match d with
      | Ast.Env.ConstantDecl bd => bd <- monad_trans_constant_body' bd;; ret (ConstantDecl bd)
      | Ast.Env.InductiveDecl bd => bd <- monad_trans_minductive_body' bd;; ret (InductiveDecl bd)
      end.

    Definition tmQuoteInductive' (mind : kername) :.CommonMonad mutual_inductive_body :=
      bd <- tmQuoteInductive TM mind;;
      monad_trans_minductive_body' bd.

    Definition TransLookup_lookup_inductive' (ind : inductive) :.CommonMonad (mutual_inductive_body × one_inductive_body) :=
      mdecl <- tmQuoteInductive' (inductive_mind ind);;
      match nth_error (ind_bodies mdecl) (inductive_ind ind) with
      | Some idecl => ret (mdecl, idecl)
      | None => tmFail TM "TransLookup.lookup_inductive: nth_error: Not_found"
      end.

  End helpers.

  Section with_helper.
    Context (TransLookup_lookup_inductive' : inductive ->.CommonMonad (mutual_inductive_body × one_inductive_body)).

    Fixpoint monad_trans' (t : Ast.term) :.CommonMonad term
      := match t with
         | Ast.tRel n => ret (tRel n)
         | Ast.tVar n => ret (tVar n)
         | Ast.tEvar ev args => args <- monad_map monad_trans' args;; ret (tEvar ev args)
         | Ast.tSort u => ret (tSort u)
         | Ast.tConst c u => ret (tConst c u)
         | Ast.tInd c u => ret (tInd c u)
         | Ast.tConstruct c k u => ret (tConstruct c k u)
         | Ast.tLambda na T M => T <- monad_trans' T;; M <- monad_trans' M;; ret (tLambda na T M)
         | Ast.tApp u v => u <- monad_trans' u;; v <- monad_map monad_trans' v;; ret (mkApps u v)
         | Ast.tProd na A B => A <- monad_trans' A;; B <- monad_trans' B;; ret (tProd na A B)
         | Ast.tCast c kind t => t <- monad_trans' t;; c <- monad_trans' c;; ret (tApp (tLambda (mkBindAnn nAnon Relevant) t (tRel 0)) c)
         | Ast.tLetIn na b t b' => b <- monad_trans' b;; t <- monad_trans' t;; b' <- monad_trans' b';; ret (tLetIn na b t b')
         | Ast.tCase ci p c brs =>
             p' <- monad_map_predicate ret monad_trans' monad_trans' p;;
             brs' <- monad_map (monad_map_branch monad_trans') brs;;
             '(mdecl, idecl) <- TransLookup_lookup_inductive' ci.(ci_ind);;
             let tp := trans_predicate ci.(ci_ind) mdecl idecl p'.(Ast.pparams) p'.(Ast.puinst) p'.(Ast.pcontext) p'.(Ast.preturn) in
             let tbrs :=
               map2 (fun cdecl br => trans_branch ci.(ci_ind) mdecl cdecl br.(Ast.bcontext) br.(Ast.bbody))
                    idecl.(ind_ctors) brs' in
             c <- monad_trans' c;;
             ret (tCase ci tp c tbrs)
         | Ast.tProj p c => c <- monad_trans' c;; ret (tProj p c)
         | Ast.tFix mfix idx =>
             mfix' <- monad_map (monad_map_def monad_trans' monad_trans') mfix;;
             ret (tFix mfix' idx)
         | Ast.tCoFix mfix idx =>
             mfix' <- monad_map (monad_map_def monad_trans' monad_trans') mfix;;
             ret (tCoFix mfix' idx)
         | Ast.tInt n => ret (tPrim (primInt; primIntModel n))
         | Ast.tFloat n => ret (tPrim (primFloat; primFloatModel n))
         end.
  End with_helper.
End with_tc.

Import.CommonMonad.Core.

Definition monad_trans : Ast.term ->.CommonMonad term
  := tmFix (fun monad_trans => @monad_trans' TypeInstance.CommonMonad_Monad (@TransLookup_lookup_inductive' TypeInstance.CommonMonad_Monad monad_trans)).

Definition monad_trans_decl := @monad_trans_decl' TypeInstance.CommonMonad_Monad monad_trans.
Definition monad_trans_local := @monad_trans_local' TypeInstance.CommonMonad_Monad monad_trans.
Definition monad_trans_constructor_body := @monad_trans_constructor_body' TypeInstance.CommonMonad_Monad monad_trans.
Definition monad_trans_projection_body := @monad_trans_projection_body' TypeInstance.CommonMonad_Monad monad_trans.
Definition monad_trans_one_ind_body := @monad_trans_one_ind_body' TypeInstance.CommonMonad_Monad monad_trans.
Definition monad_trans_constant_body := @monad_trans_constant_body' TypeInstance.CommonMonad_Monad monad_trans.
Definition monad_trans_minductive_body := @monad_trans_minductive_body' TypeInstance.CommonMonad_Monad monad_trans.
Definition monad_trans_global_decl := @monad_trans_global_decl' TypeInstance.CommonMonad_Monad monad_trans.
Definition tmQuoteInductive := @tmQuoteInductive' TypeInstance.CommonMonad_Monad monad_trans.
