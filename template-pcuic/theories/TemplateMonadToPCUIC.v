(* Distributed under the terms of the MIT license. *)
From Coq Require Import Uint63 FloatOps FloatAxioms.
From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import config Primitive EnvMap.
From MetaCoq.Common Require Import MonadBasicAst.
From MetaCoq.Template Require Import AstUtils MonadAst.
From MetaCoq.Template Require TemplateProgram.
From MetaCoq.Template Require TemplateMonad.Core.
From MetaCoq.Template Require Import TemplateMonad.Common.
From MetaCoq.PCUIC Require Import PCUICAst PCUICPrimitive PCUICCases PCUICProgram.
From MetaCoq.TemplatePCUIC Require Import TemplateToPCUIC.

Import MCMonadNotation.
Local Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.

Section with_tc.
  Universes t u.
  Context {T : Type@{t} -> Type@{u}}.
  Context {M : Monad@{t u} T}.

  Section helpers.
    Context (monad_trans : Ast.term -> T term)
      (tmQuoteInductive : kername -> T Ast.Env.mutual_inductive_body)
      (tmFail : forall {A:Type@{t}}, string -> T A).

    Definition monad_trans_decl' (d : Ast.Env.context_decl) :=
      decl_body <- monad_option_map@{t u t t} monad_trans d.(decl_body);;
      decl_type <- monad_trans d.(decl_type);;
      ret {| decl_name := d.(decl_name);
            decl_body := decl_body;
            decl_type := decl_type |}.

    Definition monad_trans_local' Γ := monad_map monad_trans_decl' Γ.

    Definition monad_trans_constructor_body' (d : Ast.Env.constructor_body) :=
      cstr_args <- monad_trans_local' d.(Ast.Env.cstr_args);;
      cstr_indices <- monad_map@{t u t t} monad_trans d.(Ast.Env.cstr_indices);;
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
      ind_ctors <- monad_map@{t u t t} monad_trans_constructor_body' d.(Ast.Env.ind_ctors);;
      ind_projs <- monad_map@{t u t t} monad_trans_projection_body' d.(Ast.Env.ind_projs);;
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
      cst_body <- monad_option_map@{t u t t} monad_trans bd.(Ast.Env.cst_body);;
      ret {| cst_type := cst_type;
            cst_body := cst_body;
            cst_universes := bd.(Ast.Env.cst_universes);
            cst_relevance := bd.(Ast.Env.cst_relevance) |}.

    Definition monad_trans_minductive_body' md :=
      ind_params <- monad_trans_local' md.(Ast.Env.ind_params);;
      ind_bodies <- monad_map@{t u t t} monad_trans_one_ind_body' md.(Ast.Env.ind_bodies);;
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

    Definition tmQuoteInductive' (mind : kername) : T mutual_inductive_body :=
      bd <- tmQuoteInductive mind;;
      monad_trans_minductive_body' bd.

    Definition TransLookup_lookup_inductive' (ind : inductive) : T (mutual_inductive_body × one_inductive_body) :=
      mdecl <- tmQuoteInductive' (inductive_mind ind);;
      match nth_error (ind_bodies mdecl) (inductive_ind ind) with
      | Some idecl => ret (mdecl, idecl)
      | None => tmFail _ "TransLookup.lookup_inductive: nth_error: Not_found"
      end.

  End helpers.

  Section with_helper.
    Context (TransLookup_lookup_inductive' : inductive -> T (mutual_inductive_body × one_inductive_body))
      (tmEval : forall {A:Type@{t}}, A -> T A).

    Fixpoint monad_trans' (t : Ast.term) : T term
      := match t with
         | Ast.tRel n => ret (tRel n)
         | Ast.tVar n => ret (tVar n)
         | Ast.tEvar ev args => args <- monad_map@{t u t t} monad_trans' args;; ret (tEvar ev args)
         | Ast.tSort u => ret (tSort u)
         | Ast.tConst c u => ret (tConst c u)
         | Ast.tInd c u => ret (tInd c u)
         | Ast.tConstruct c k u => ret (tConstruct c k u)
         | Ast.tLambda na T M => T <- monad_trans' T;; M <- monad_trans' M;; ret (tLambda na T M)
         | Ast.tApp u v => u <- monad_trans' u;; v <- monad_map@{t u t t} monad_trans' v;; ret (mkApps u v)
         | Ast.tProd na A B => A <- monad_trans' A;; B <- monad_trans' B;; ret (tProd na A B)
         | Ast.tCast c kind t => t <- monad_trans' t;; c <- monad_trans' c;; ret (tApp (tLambda (mkBindAnn nAnon Relevant) t (tRel 0)) c)
         | Ast.tLetIn na b t b' => b <- monad_trans' b;; t <- monad_trans' t;; b' <- monad_trans' b';; ret (tLetIn na b t b')
         | Ast.tCase ci p c brs =>
             p' <- monad_map_predicate ret monad_trans' monad_trans' p;;
             brs' <- monad_map@{t u t t} (monad_map_branch monad_trans') brs;;
             '(mdecl, idecl) <- TransLookup_lookup_inductive' ci.(ci_ind);;
             tp <- tmEval _ (trans_predicate ci.(ci_ind) mdecl idecl p'.(Ast.pparams) p'.(Ast.puinst) p'.(Ast.pcontext) p'.(Ast.preturn));;
             tbrs <- tmEval
                       _ (map2 (fun cdecl br => trans_branch ci.(ci_ind) mdecl cdecl br.(Ast.bcontext) br.(Ast.bbody))
                            idecl.(ind_ctors) brs');;
             c <- monad_trans' c;;
             ret (tCase ci tp c tbrs)
         | Ast.tProj p c => c <- monad_trans' c;; ret (tProj p c)
         | Ast.tFix mfix idx =>
             mfix' <- monad_map@{t u t t} (monad_map_def monad_trans' monad_trans') mfix;;
             ret (tFix mfix' idx)
         | Ast.tCoFix mfix idx =>
             mfix' <- monad_map@{t u t t} (monad_map_def monad_trans' monad_trans') mfix;;
             ret (tCoFix mfix' idx)
         | Ast.tInt n => ret (tPrim (primInt; primIntModel n))
         | Ast.tFloat n => ret (tPrim (primFloat; primFloatModel n))
         end.
  End with_helper.
End with_tc.

Import TemplateMonad.Core.

Definition monad_trans@{t u} : Ast.term -> TemplateMonad@{t u} term
  := tmFix@{u u t u}
       (fun monad_trans v
        => v <- @monad_trans'@{t u} TemplateMonad TemplateMonad_Monad
                  (@TransLookup_lookup_inductive' TemplateMonad TemplateMonad_Monad monad_trans tmQuoteInductive (@tmFail))
                  (@tmEval cbv)
                  v;;
           tmEval cbv v).

Definition monad_trans_decl@{t u} := @monad_trans_decl'@{t u} TemplateMonad TemplateMonad_Monad monad_trans.
Definition monad_trans_local@{t u} := @monad_trans_local'@{t u} TemplateMonad TemplateMonad_Monad monad_trans.
Definition monad_trans_constructor_body@{t u} := @monad_trans_constructor_body'@{t u} TemplateMonad TemplateMonad_Monad monad_trans.
Definition monad_trans_projection_body@{t u} := @monad_trans_projection_body'@{t u} TemplateMonad TemplateMonad_Monad monad_trans.
Definition monad_trans_one_ind_body@{t u} := @monad_trans_one_ind_body'@{t u} TemplateMonad TemplateMonad_Monad monad_trans.
Definition monad_trans_constant_body@{t u} := @monad_trans_constant_body'@{t u} TemplateMonad TemplateMonad_Monad monad_trans.
Definition monad_trans_minductive_body@{t u} := @monad_trans_minductive_body'@{t u} TemplateMonad TemplateMonad_Monad monad_trans.
Definition monad_trans_global_decl@{t u} := @monad_trans_global_decl'@{t u} TemplateMonad TemplateMonad_Monad monad_trans.
Definition tmQuoteInductive@{t u} := @tmQuoteInductive'@{t u} TemplateMonad TemplateMonad_Monad monad_trans tmQuoteInductive.
