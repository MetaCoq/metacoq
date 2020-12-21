(* Distributed under the terms of the MIT license. *)
From Coq Require Import Int63 FloatOps FloatAxioms.
From MetaCoq.Template Require Import config utils AstUtils.
From MetaCoq.PCUIC Require Import PCUICAst.

Lemma to_Z_bounded_bool (i : Int63.int) : 
  ((0 <=? φ (i)%int63) && (φ (i)%int63 <? wB))%Z.
Proof.
  generalize (to_Z_bounded i).
  now intros [->%Z.leb_le ->%Z.ltb_lt].
Qed.

Definition uint63_to_model (i : Int63.int) : uint63_model :=
  exist _ (Int63.to_Z i) (to_Z_bounded_bool i).

Definition float64_to_model (f : PrimFloat.float) : float64_model :=
  exist _ (FloatOps.Prim2SF f) (FloatAxioms.Prim2SF_valid f).

Fixpoint trans (t : Ast.term) : term :=
  match t with
  | Ast.tRel n => tRel n
  | Ast.tVar n => tVar n
  | Ast.tEvar ev args => tEvar ev (List.map trans args)
  | Ast.tSort u => tSort u
  | Ast.tConst c u => tConst c u
  | Ast.tInd c u => tInd c u
  | Ast.tConstruct c k u => tConstruct c k u
  | Ast.tLambda na T M => tLambda na (trans T) (trans M)
  | Ast.tApp u v => mkApps (trans u) (List.map trans v)
  | Ast.tProd na A B => tProd na (trans A) (trans B)
  | Ast.tCast c kind t => tApp (tLambda (mkBindAnn nAnon Relevant) (trans t) (tRel 0)) (trans c)
  | Ast.tLetIn na b t b' => tLetIn na (trans b) (trans t) (trans b')
  | Ast.tCase ind p c brs =>
    let p' := map_predicate id trans trans p in
    let brs' := List.map (map_branch trans) brs in
    tCase ind p' (trans c) brs'
  | Ast.tProj p c => tProj p (trans c)
  | Ast.tFix mfix idx =>
    let mfix' := List.map (map_def trans trans) mfix in
    tFix mfix' idx
  | Ast.tCoFix mfix idx =>
    let mfix' := List.map (map_def trans trans) mfix in
    tCoFix mfix' idx
  | Ast.tInt n => tPrim (primInt; primIntModel (uint63_to_model n))
  | Ast.tFloat n => tPrim (primFloat; primFloatModel (float64_to_model n))
  end.

Definition trans_decl (d : Ast.context_decl) :=
  let 'Ast.mkdecl na b t := d in
  {| decl_name := na;
     decl_body := option_map trans b;
     decl_type := trans t |}.

Definition trans_local Γ := List.map trans_decl Γ.

Definition trans_constructor_body (d : Ast.constructor_body) :=
  {| cstr_name := d.(Ast.cstr_name); 
     cstr_args := trans_local d.(Ast.cstr_args);
     cstr_indices := map trans d.(Ast.cstr_indices); 
     cstr_type := trans d.(Ast.cstr_type);
     cstr_arity := d.(Ast.cstr_arity) |}.

Definition trans_one_ind_body (d : Ast.one_inductive_body) :=
  {| ind_name := d.(Ast.ind_name);
     ind_relevance := d.(Ast.ind_relevance);
     ind_indices := trans_local d.(Ast.ind_indices);
     ind_sort := d.(Ast.ind_sort);
     ind_type := trans d.(Ast.ind_type);
     ind_kelim := d.(Ast.ind_kelim);
     ind_ctors := List.map trans_constructor_body d.(Ast.ind_ctors);
     ind_projs := List.map (fun '(x, y) => (x, trans y)) d.(Ast.ind_projs) |}.

Definition trans_constant_body bd :=
  {| cst_type := trans bd.(Ast.cst_type); cst_body := option_map trans bd.(Ast.cst_body);
     cst_universes := bd.(Ast.cst_universes) |}.

Definition trans_minductive_body md :=
  {| ind_finite := md.(Ast.ind_finite);
     ind_npars := md.(Ast.ind_npars);
     ind_params := trans_local md.(Ast.ind_params);
     ind_bodies := map trans_one_ind_body md.(Ast.ind_bodies);
     ind_universes := md.(Ast.ind_universes);
     ind_variance := md.(Ast.ind_variance) |}.

Definition trans_global_decl (d : Ast.global_decl) :=
  match d with
  | Ast.ConstantDecl bd => ConstantDecl (trans_constant_body bd)
  | Ast.InductiveDecl bd => InductiveDecl (trans_minductive_body bd)
  end.

Definition trans_global_decls (d : Ast.global_env) :=
  List.map (on_snd trans_global_decl) d.

Definition trans_global (Σ : Ast.global_env_ext) :=
  (trans_global_decls (fst Σ), snd Σ).
