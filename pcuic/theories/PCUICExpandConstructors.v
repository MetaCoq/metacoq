(* Distributed under the terms of the MIT license. *)
From Coq Require Import Int63 FloatOps FloatAxioms.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICTyping.

(** This translation expands all constructor applications. It is useful for compilation 
    phases that might want to remove constructor parameters.
    In a second phase, we can selectively apply beta reduction to the eta-expanded terms 
    to recover nicer terms without unnecessary beta-redexes. *)

Section Trans.
  Context (Σ : global_env).

  Definition eta_expand c k u := 
    match lookup_constructor Σ c k with
    | Some (mdecl, idecl, cdecl) =>
      let ctx := subst_context (inds (inductive_mind c) u mdecl.(ind_bodies)) 0 (mdecl.(ind_params) ,,, cdecl.(cstr_args)) in
      it_mkLambda_or_LetIn ctx
        (mkApps (tConstruct c k u) (to_extended_list ctx))
    | None => tConstruct c k u
    end.

  Fixpoint trans (t : term) : term :=
    match t with
    | tRel n => tRel n
    | tVar n => tVar n
    | tEvar ev args => tEvar ev (List.map trans args)
    | tSort u => tSort u
    | tConst c u => tConst c u
    | tInd c u => tInd c u
    | tConstruct c k u => eta_expand c k u
    | tLambda na T M => tLambda na (trans T) (trans M)
    | tApp u v => tApp (trans u) (trans v)
    | tProd na A B => tProd na (trans A) (trans B)
    | tLetIn na b t b' => tLetIn na (trans b) (trans t) (trans b')
    | tCase ind p c brs =>
      let p' := map_predicate id trans trans (map_context trans) p in
      let brs' := List.map (map_branch trans (map_context trans)) brs in
      tCase ind p' (trans c) brs'
    | tProj p c => tProj p (trans c)
    | tFix mfix idx =>
      let mfix' := List.map (map_def trans trans) mfix in
      tFix mfix' idx
    | tCoFix mfix idx =>
      let mfix' := List.map (map_def trans trans) mfix in
      tCoFix mfix' idx
    | tPrim i => tPrim i
    end.

  Notation trans_decl := (map_decl trans).

  Definition trans_local Γ := List.map trans_decl Γ.

  Definition trans_constructor_body (d : PCUICEnvironment.constructor_body) :=
    let args' := trans_local d.(cstr_args) in
    let indices' := map trans d.(cstr_indices) in
    {| cstr_name := d.(PCUICEnvironment.cstr_name);     
       cstr_args := args';
       cstr_indices := indices';
       cstr_type := trans d.(cstr_type);
       cstr_arity := d.(PCUICEnvironment.cstr_arity) |}.
          
  Definition trans_one_ind_body (d : PCUICEnvironment.one_inductive_body) :=
    {| ind_name := d.(PCUICEnvironment.ind_name);
      ind_relevance := d.(PCUICEnvironment.ind_relevance);
      ind_indices := trans_local d.(PCUICEnvironment.ind_indices);
      ind_type := trans d.(PCUICEnvironment.ind_type);
      ind_sort := d.(PCUICEnvironment.ind_sort);
      ind_kelim := d.(PCUICEnvironment.ind_kelim);
      ind_ctors := List.map trans_constructor_body d.(PCUICEnvironment.ind_ctors);
      ind_projs := List.map (fun '(x, y) => (x, trans y)) d.(PCUICEnvironment.ind_projs) |}.

  Definition trans_minductive_body md :=
    {| ind_finite := md.(PCUICEnvironment.ind_finite);
      ind_npars := md.(PCUICEnvironment.ind_npars);
      ind_params := trans_local md.(PCUICEnvironment.ind_params);
      ind_bodies := map trans_one_ind_body md.(PCUICEnvironment.ind_bodies);
      ind_universes := md.(PCUICEnvironment.ind_universes);
      ind_variance := md.(PCUICEnvironment.ind_variance)
    |}.

  Definition trans_constant_body bd :=
    {| cst_type := trans bd.(PCUICEnvironment.cst_type); cst_body := option_map trans bd.(PCUICEnvironment.cst_body);
       cst_universes := bd.(PCUICEnvironment.cst_universes) |}.

  Definition trans_global_decl (d : PCUICEnvironment.global_decl) :=
    match d with
    | PCUICEnvironment.ConstantDecl bd => ConstantDecl (trans_constant_body bd)
    | PCUICEnvironment.InductiveDecl bd => InductiveDecl (trans_minductive_body bd)
    end.

End Trans.

Section TransGlobal.
  Fixpoint trans_global_decls Σ : global_env :=
    match Σ with
    | [] => []
    | decl :: Σ => 
      let Σ' := trans_global_decls Σ in    
      on_snd (trans_global_decl Σ') decl :: Σ'
    end.

  Definition trans_global (Σ : PCUICEnvironment.global_env_ext) : global_env_ext :=
    (trans_global_decls (fst Σ), snd Σ).

End TransGlobal.
