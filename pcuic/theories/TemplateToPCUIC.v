(* Distributed under the terms of the MIT license. *)
From Coq Require Import Uint63 FloatOps FloatAxioms Logic.Decidable.
From MetaCoq.Template Require Import config utils AstUtils Primitive EnvMap.
From MetaCoq.Template Require TemplateProgram.
From MetaCoq.PCUIC Require Import PCUICAst PCUICPrimitive PCUICCases PCUICProgram.

Lemma to_Z_bounded_bool (i : Uint63.int) :
  ((0 <=? Uint63.to_Z i) && (Uint63.to_Z i <? wB))%Z.
Proof.
  generalize (Uint63.to_Z_bounded i).
  now intros [->%Z.leb_le ->%Z.ltb_lt].
Qed.

Definition uint63_to_model (i : Uint63.int) : uint63_model :=
  exist (Uint63.to_Z i) (to_Z_bounded_bool i).

Definition float64_to_model (f : PrimFloat.float) : float64_model :=
  exist (FloatOps.Prim2SF f) (FloatAxioms.Prim2SF_valid f).

Section Map2Bias.
  Context {A B C} (f : A -> B -> C) (default : B).

  Fixpoint map2_bias_left (l : list A) (l' : list B) : list C :=
    match l, l' with
    | [], [] => []
    | a :: as_, b :: bs => (f a b) :: map2_bias_left as_ bs
    | a :: as_, [] => (f a default) :: map2_bias_left as_ []
    | _, _ => []
    end.

  Lemma map2_bias_left_length l l' : #|map2_bias_left l l'| = #|l|.
  Proof using Type.
    induction l in l' |- *; destruct l'; simpl; auto; now rewrite IHl.
  Qed.

  Lemma map2_map2_bias_left l l' : #|l| = #|l'| -> map2_bias_left l l' = map2 f l l'.
  Proof using Type.
    induction l in l' |- *; destruct l'; simpl; auto.
    - discriminate.
    - intros [= hlen]. rewrite IHl; tas. reflexivity.
  Qed.
End Map2Bias.

Section Trans.
  Context (Σ : global_env_map).

  Definition dummy_decl : context_decl :=
    vass {| binder_name := nAnon; binder_relevance := Relevant |} (tSort Universe.type0).

  Definition trans_predicate ind mdecl idecl pparams puinst pcontext preturn :=
    let pctx := map2_bias_left set_binder_name dummy_decl pcontext (ind_predicate_context ind mdecl idecl) in
    {| pparams := pparams;
       puinst := puinst;
       pcontext := pctx;
       preturn := preturn |}.

  Definition trans_branch ind mdecl cdecl bcontext bbody :=
    let bctx := map2_bias_left set_binder_name dummy_decl bcontext (cstr_branch_context ind mdecl cdecl) in
    {| bcontext := bctx;
       bbody := bbody |}.

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
  | Ast.tCase ci p c brs =>
    let p' := Ast.map_predicate id trans trans p in
    let brs' := List.map (Ast.map_branch trans) brs in
    match TransLookup.lookup_inductive Σ ci.(ci_ind) with
    | Some (mdecl, idecl) =>
      let tp := trans_predicate ci.(ci_ind) mdecl idecl p'.(Ast.pparams) p'.(Ast.puinst) p'.(Ast.pcontext) p'.(Ast.preturn) in
      let tbrs :=
        map2 (fun cdecl br => trans_branch ci.(ci_ind) mdecl cdecl br.(Ast.bcontext) br.(Ast.bbody))
                  idecl.(ind_ctors) brs' in
      tCase ci tp (trans c) tbrs
    | None =>
      (** We build an ill-formed case if the term + environment are not well-formed.
          But we still give the right length to the context so that all syntactic operations
          still work. *)
      tCase ci {| pparams := p'.(Ast.pparams);
                  puinst := p'.(Ast.puinst);
                  pcontext := map (fun na => vass na (tSort Universe.type0)) p'.(Ast.pcontext);
                  preturn := p'.(Ast.preturn) |}
          (trans c) []
    end
  | Ast.tProj p c => tProj p (trans c)
  | Ast.tFix mfix idx =>
    let mfix' := List.map (map_def trans trans) mfix in
    tFix mfix' idx
  | Ast.tCoFix mfix idx =>
    let mfix' := List.map (map_def trans trans) mfix in
    tCoFix mfix' idx
  | Ast.tInt n => tPrim (primInt; primIntModel n)
  | Ast.tFloat n => tPrim (primFloat; primFloatModel n)
  end.

  Definition trans_decl (d : Ast.Env.context_decl) :=
    {| decl_name := d.(decl_name);
      decl_body := option_map trans d.(decl_body);
      decl_type := trans d.(decl_type) |}.

  Definition trans_local Γ := List.map trans_decl Γ.

  Definition trans_constructor_body (d : Ast.Env.constructor_body) :=
    {| cstr_name := d.(Ast.Env.cstr_name);
      cstr_args := trans_local d.(Ast.Env.cstr_args);
      cstr_indices := map trans d.(Ast.Env.cstr_indices);
      cstr_type := trans d.(Ast.Env.cstr_type);
      cstr_arity := d.(Ast.Env.cstr_arity) |}.
  Definition trans_projection_body (d : Ast.Env.projection_body) :=
    {| proj_name := d.(Ast.Env.proj_name);
        proj_type := trans d.(Ast.Env.proj_type);
        proj_relevance := d.(Ast.Env.proj_relevance) |}.

  Definition trans_one_ind_body (d : Ast.Env.one_inductive_body) :=
    {| ind_name := d.(Ast.Env.ind_name);
      ind_relevance := d.(Ast.Env.ind_relevance);
      ind_indices := trans_local d.(Ast.Env.ind_indices);
      ind_sort := d.(Ast.Env.ind_sort);
      ind_type := trans d.(Ast.Env.ind_type);
      ind_kelim := d.(Ast.Env.ind_kelim);
      ind_ctors := List.map trans_constructor_body d.(Ast.Env.ind_ctors);
      ind_projs := List.map trans_projection_body d.(Ast.Env.ind_projs) |}.

  Definition trans_constant_body bd :=
    {| cst_type := trans bd.(Ast.Env.cst_type);
       cst_body := option_map trans bd.(Ast.Env.cst_body);
       cst_universes := bd.(Ast.Env.cst_universes);
       cst_relevance := bd.(Ast.Env.cst_relevance) |}.

  Definition trans_minductive_body md :=
    {| ind_finite := md.(Ast.Env.ind_finite);
      ind_npars := md.(Ast.Env.ind_npars);
      ind_params := trans_local md.(Ast.Env.ind_params);
      ind_bodies := map trans_one_ind_body md.(Ast.Env.ind_bodies);
      ind_universes := md.(Ast.Env.ind_universes);
      ind_variance := md.(Ast.Env.ind_variance) |}.

      (* kn := Coq.Init.M := (Coq.Init, M) *)
  Definition kn_append (kn: kername) (id: ident) : kername := ((MPdot kn.1 kn.2), id).

  Inductive kn_extends : kername -> kername -> Prop :=
  | kn_extends_one kn id : kn_extends kn (kn_append kn id)
  | kn_extends_step id kn kn' (H: kn_extends kn kn') : kn_extends kn (kn_append kn' id).

  Lemma kn_extends_exists : forall kn kn', kn_extends kn kn' -> exists l: list ident,
    l <> [] /\ fold_right (fun id kn => kn_append kn id) kn l = kn'.
  Proof.
    intros kn kn' Hext.
    induction Hext.
    - exists [id]. split; auto. discriminate.
    - destruct IHHext as [l [Hne H]].
      exists (id::l).
      split. simpl. discriminate.
      simpl. now rewrite <- H.
  Qed.

  Lemma kn_append_neq : forall kn id, kn_append kn id <> kn.
  Proof.
    intros [mp i]. revert i.
    induction mp; try discriminate.
    intros i' id'.
    unfold kn_append in *; simpl in *.
    intros contra. inversion contra; subst.
    assert ((MPdot mp id, id) = (mp, id)) by now rewrite H0.
    apply IHmp in H. apply H.
  Qed.

  Lemma kn_extends' : forall id kn kn',
  kn_extends (kn_append kn id) kn' -> kn_extends kn kn'.
  Proof.
    intros id kn kn' H.
    remember (kn_append kn id) as knid.
    induction H; subst.
    - apply kn_extends_step. apply kn_extends_one.
    - assert (kn_extends kn kn') by now apply IHkn_extends.
      now apply kn_extends_step.
  Qed.

  Lemma kn_extends_trans : forall kn kn' kn'',
  kn_extends kn kn' -> kn_extends kn' kn'' -> kn_extends kn kn''.
  Proof.
    intros kn kn' kn'' H1 H2.
    generalize dependent kn''.
    induction H1.
    - remember (kn_append kn id) as knid.
      intros kn'' H2. induction H2; subst.
      -- apply kn_extends_step. apply kn_extends_one.
      -- assert (kn_extends kn kn') by now apply IHkn_extends.
        now apply kn_extends_step.
    - intros kn'' H2. apply IHkn_extends.
      remember (kn_append kn' id) as kn'id.
      induction H2; subst.
      -- apply kn_extends_step. apply kn_extends_one.
      -- apply kn_extends_step.
        assert (kn_extends kn (kn_append kn'0 id0)). {
          apply IHkn_extends. apply kn_extends_step.
          now apply kn_extends' with (id := id).
        }
        now apply IHkn_extends0.
  Qed.

  Lemma kn_extends_inversion_true : forall mp mp' i i' id id',
    kn_extends (MPdot mp i, id) (MPdot mp' i', id') -> kn_extends (mp, i) (mp', i').
  Proof.
    intros. inversion H; subst.
    - apply kn_extends_one.
    - destruct kn' as [mp' i']; cbn in *.
      apply (kn_extends' id).
      apply H2.
  Qed.

  Lemma kn_appended_is_mpdot : forall kn id,
  exists mp i, (kn_append kn id) = (MPdot mp i, id).
  Proof.
    intros. unfold kn_append. now exists kn.1, kn.2.
  Qed.

  Lemma kn_extends_is_mpdot : forall kn kn', kn_extends kn kn' -> exists mp i, kn'.1 = (MPdot mp i).
  Proof.
    intros. apply kn_extends_exists in H as [l [Hne H]].
    destruct l. contradiction.
    simpl in H. remember (fold_right (fun (id : ident) (kn : kername) => kn_append kn id) kn l) as kn''.
    pose proof (kn_appended_is_mpdot kn'' i) as [mp [id Hdot]].
    exists mp, id.
    subst kn'. rewrite Hdot. reflexivity.
  Qed.

  Lemma kn_extends_irrefl : forall kn, ~(kn_extends kn kn).
  Proof.
    intros [mp id].
    revert id.
    induction mp.
    - intros id contra. apply kn_extends_is_mpdot in contra as [? [? ?]].
      discriminate.
    - intros id' contra. apply kn_extends_is_mpdot in contra as [? [? ?]].
      discriminate.
    - intros id' H. inversion H; subst.
      -- rewrite H2 in H. now apply IHmp in H.
      -- destruct kn' as [mp i]; cbn in *.
        apply kn_extends_inversion_true in H.
        now apply IHmp in H.
  Qed.

  Lemma kn_extends_neq : forall kn kn', kn_extends kn kn' -> kn <> kn'.
  Proof.
    intros kn kn' H contra.
    rewrite contra in H.
    now apply kn_extends_irrefl in H.
  Qed.

  (**
    Claim: The aliasing is a tree.
    Reason:
      1. One can only alias backwards to a already defined module.
      2. As a naive implementation, aliasing is (deep) copying.

      We can than verify the claim inductively: an actual module is a
      single-node tree. For the inductive step, suppose we already have a tree
      of aliases. Then a new alias can only refer to a node on the tree, forming
      a tree.

      For the case of aliasing of submodules such as:
      Module M.
        Module A.
          Module B: End B.
        End A.
        Module C: End C.
      End M.

        M
       / \
      A,L C
        \
         B

      The "submodule" relation can also be considered as a different directed
      edge on the tree, and will not affect the tree structure (because cannot
      have self-reference). Once one proves the submodule relationship forms a
      tree (identical to above), one can prove "aliasing with submodules" form
      a tree too, inductively:

      Base case: A module is a tree.
      Inductive case: Suppose an alias refers to a certain (sub)module (aliased or not)
      on the existing tree, which refers to a whole subtree identifiable by a node
      (technically: kername). Call the node K and its parent K'. The aliasing is
      equivalent to copying K to a sibling L under K', where L is the new aliased
      module. This is still a tree. Qed.
  *)

  (**
    Therefore, strategy:
    Build and store such a tree.
    In technical terms, all of these are [structure_body]s.
    We can use sfmod with fullstruct.
    Finding the correct branch is tree-traversal given a path (kername).
    However, every time a subtree is aliased, we add the aliased name to the
    list of labels for that root node.

    [([idents...], tree), ([idents...], tree), ... ]

  *)

  Fixpoint trans_structure_field kn id (sf : Ast.Env.structure_field) :=
    let kn' := kn_append kn id in
    match sf with
    | Ast.Env.sfconst c => [(kn', ConstantDecl (trans_constant_body c))]
    | Ast.Env.sfmind m => [(kn', InductiveDecl (trans_minductive_body m))]
    | Ast.Env.sfmod mi sb => match mi with
      | Ast.Env.mi_fullstruct => trans_structure_body kn' sb
      | Ast.Env.mi_struct s => trans_structure_body kn' s
      | _ => trans_module_impl kn' mi
      end
    | Ast.Env.sfmodtype _ => []
    end
  with trans_module_impl kn (mi: Ast.Env.module_implementation) :=
    match mi with
    | Ast.Env.mi_abstract => []
    | Ast.Env.mi_algebraic kn' => []
      (* let target := find_target_structure_body kn' in trans_structure_body kn' target *)
    | Ast.Env.mi_struct sb => trans_structure_body kn sb
    | Ast.Env.mi_fullstruct => []
    end
  with trans_structure_body kn (sb: Ast.Env.structure_body) :=
    match sb with
    | Ast.Env.sb_nil => []
    | Ast.Env.sb_cons id sf tl =>
      trans_structure_field kn id sf ++ trans_structure_body kn tl
    end.

  Definition trans_modtype_decl := trans_structure_body.

  Definition trans_module_decl kn (m: Ast.Env.module_decl) : list(kername × global_decl) :=
    match m with
    | (Ast.Env.mi_fullstruct, mt) => trans_modtype_decl kn mt
    | (mi, _) => trans_module_impl kn mi
    end.


  Lemma translated_structure_field_all_kn_extends:
  forall sf kn id, Forall (fun '(kn', _) => kn_extends kn kn') (trans_structure_field kn id sf).
  Proof.
    set (P := fun sf => forall kn id, Forall (fun '(kn', _) => kn_extends kn kn') (trans_structure_field kn id sf)).
    set (P0 := fun mi => forall kn, Forall (fun '(kn', _) => kn_extends kn kn') (trans_module_impl kn mi)).
    set (P1 := fun sb => forall kn, Forall (fun '(kn', _) => kn_extends kn kn') (trans_structure_body kn sb)).
    apply (Ast.Env.sf_mi_sb_mutind P P0 P1); subst P P0 P1; cbn; try auto.
    - intros c kn id. rewrite Forall_forall.
      intros [kn' d] [].
      inversion H.
      constructor.
      inversion H.
    - intros m kn id. rewrite Forall_forall.
      intros [kn' d] [].
      inversion H.
      constructor.
      inversion H.
    - intros mi Hmi sb Hsb kn id.
      rewrite Forall_forall. intros [kn' d].
      destruct mi; cbn; try auto.
      -- intros Hin. specialize (Hmi (kn_append kn id)).
        rewrite Forall_forall in Hmi.
        specialize (Hmi (kn', d)).
        simpl in Hmi. specialize (Hmi Hin).
        apply kn_extends_trans with (kn' := (kn_append kn id)); auto.
        constructor.
      -- intros Hin. specialize (Hsb (kn_append kn id)).
        rewrite Forall_forall in Hsb.
        specialize (Hsb (kn', d)).
        simpl in Hsb. specialize (Hsb Hin).
        apply kn_extends_trans with (kn' := (kn_append kn id)); auto.
        constructor.
    - intros i sf Hsf sb Hsb kn.
      apply Forall_forall.
      intros [kn' d] Hin.
      apply in_app_or in Hin. destruct Hin.
      -- specialize (Hsf kn i).
        rewrite Forall_forall in Hsf.
        specialize (Hsf (kn', d)).
        simpl in Hsf. apply (Hsf H).
      -- specialize (Hsb kn).
        rewrite Forall_forall in Hsb.
        specialize (Hsb (kn', d)).
        simpl in Hsb. apply (Hsb H).
  Qed.

  Lemma translated_module_impl_all_kn_extends:
  forall mi kn, Forall (fun '(kn', _) => kn_extends kn kn') (trans_module_impl kn mi).
  Proof.
    set (P := fun sf => forall kn id, Forall (fun '(kn', _) => kn_extends kn kn') (trans_structure_field kn id sf)).
    set (P0 := fun mi => forall kn, Forall (fun '(kn', _) => kn_extends kn kn') (trans_module_impl kn mi)).
    set (P1 := fun sb => forall kn, Forall (fun '(kn', _) => kn_extends kn kn') (trans_structure_body kn sb)).
    apply (Ast.Env.sf_mi_sb_mutind P P0 P1); subst P P0 P1; cbn; try auto.
    - intros c kn id. rewrite Forall_forall.
      intros [kn' d] [].
      inversion H.
      constructor.
      inversion H.
    - intros m kn id. rewrite Forall_forall.
      intros [kn' d] [].
      inversion H.
      constructor.
      inversion H.
    - intros mi Hmi sb Hsb kn id.
      rewrite Forall_forall. intros [kn' d].
      destruct mi; cbn; try auto.
      -- intros Hin. specialize (Hmi (kn_append kn id)).
        rewrite Forall_forall in Hmi.
        specialize (Hmi (kn', d)).
        simpl in Hmi. specialize (Hmi Hin).
        apply kn_extends_trans with (kn' := (kn_append kn id)); auto.
        constructor.
      -- intros Hin. specialize (Hsb (kn_append kn id)).
        rewrite Forall_forall in Hsb.
        specialize (Hsb (kn', d)).
        simpl in Hsb. specialize (Hsb Hin).
        apply kn_extends_trans with (kn' := (kn_append kn id)); auto.
        constructor.
    - intros i sf Hsf sb Hsb kn.
      apply Forall_forall.
      intros [kn' d] Hin.
      apply in_app_or in Hin. destruct Hin.
      -- specialize (Hsf kn i).
        rewrite Forall_forall in Hsf.
        specialize (Hsf (kn', d)).
        simpl in Hsf. apply (Hsf H).
      -- specialize (Hsb kn).
        rewrite Forall_forall in Hsb.
        specialize (Hsb (kn', d)).
        simpl in Hsb. apply (Hsb H).
  Qed.

  Lemma translated_structure_body_all_kn_extends:
  forall sb kn, Forall (fun '(kn', _) => kn_extends kn kn') (trans_structure_body kn sb).
  Proof.
    set (P := fun sf => forall kn id, Forall (fun '(kn', _) => kn_extends kn kn') (trans_structure_field kn id sf)).
    set (P0 := fun mi => forall kn, Forall (fun '(kn', _) => kn_extends kn kn') (trans_module_impl kn mi)).
    set (P1 := fun sb => forall kn, Forall (fun '(kn', _) => kn_extends kn kn') (trans_structure_body kn sb)).
    apply (Ast.Env.sf_mi_sb_mutind P P0 P1); subst P P0 P1; cbn; try auto.
    - intros c kn id. rewrite Forall_forall.
      intros [kn' d] [].
      inversion H.
      constructor.
      inversion H.
    - intros m kn id. rewrite Forall_forall.
      intros [kn' d] [].
      inversion H.
      constructor.
      inversion H.
    - intros mi Hmi sb Hsb kn id.
      rewrite Forall_forall. intros [kn' d].
      destruct mi; cbn; try auto.
      -- intros Hin. specialize (Hmi (kn_append kn id)).
        rewrite Forall_forall in Hmi.
        specialize (Hmi (kn', d)).
        simpl in Hmi. specialize (Hmi Hin).
        apply kn_extends_trans with (kn' := (kn_append kn id)); auto.
        constructor.
      -- intros Hin. specialize (Hsb (kn_append kn id)).
        rewrite Forall_forall in Hsb.
        specialize (Hsb (kn', d)).
        simpl in Hsb. specialize (Hsb Hin).
        apply kn_extends_trans with (kn' := (kn_append kn id)); auto.
        constructor.
    - intros i sf Hsf sb Hsb kn.
      apply Forall_forall.
      intros [kn' d] Hin.
      apply in_app_or in Hin. destruct Hin.
      -- specialize (Hsf kn i).
        rewrite Forall_forall in Hsf.
        specialize (Hsf (kn', d)).
        simpl in Hsf. apply (Hsf H).
      -- specialize (Hsb kn).
        rewrite Forall_forall in Hsb.
        specialize (Hsb (kn', d)).
        simpl in Hsb. apply (Hsb H).
  Qed.

  Lemma translated_module_decl_all_kn_extends:
  forall m kn, Forall (fun '(kn', _) => kn_extends kn kn') (trans_module_decl kn m).
  Proof.
    destruct m as [[] mt]; cbn; auto; apply translated_structure_body_all_kn_extends.
  Qed.

  Lemma translated_modtype_decl_all_kn_neq:
  forall mt kn, Forall (fun '(kn', _) => kn <> kn') (trans_modtype_decl kn mt).
  Proof.
    intros mt kn; apply (Forall_impl (P := (fun '(kn', _) => kn_extends kn kn'))).
    apply translated_structure_body_all_kn_extends.
    intros [kn' _]; apply kn_extends_neq.
  Qed.

  Lemma translated_module_decl_all_kn_neq:
  forall m kn, Forall (fun '(kn', _) => kn <> kn') (trans_module_decl kn m).
  Proof.
    destruct m as [[] mt]; cbn; auto; apply translated_modtype_decl_all_kn_neq.
  Qed.

  Definition trans_global_decl (d : kername × Ast.Env.global_decl) :=
    let (kn, decl) := d in match decl with
    | Ast.Env.ConstantDecl bd => [(kn, ConstantDecl (trans_constant_body bd))]
    | Ast.Env.InductiveDecl bd => [(kn, InductiveDecl (trans_minductive_body bd))]
    | Ast.Env.ModuleDecl bd => trans_module_decl kn bd
    | Ast.Env.ModuleTypeDecl _ => []
    end.
End Trans.

Program Definition add_global_decl (d : kername × global_decl) (env : global_env_map) :=
  {| trans_env_env := add_global_decl d env.(trans_env_env);
     trans_env_map := EnvMap.add d.1 d.2 env.(trans_env_map) |}.
Next Obligation.
  pose proof env.(trans_env_repr).
  red in H. rewrite H. reflexivity.
Qed.

Definition trans_global_decls env (d : Ast.Env.global_declarations) : global_env_map :=
  fold_right (fun decl Σ' =>
    let decls := (trans_global_decl Σ' decl) in
    fold_right add_global_decl Σ' decls) env d.

Definition empty_trans_env univs retro :=
  let init_global_env := {| universes := univs; declarations := []; retroknowledge := retro |} in
    {| trans_env_env := init_global_env;
       trans_env_map := EnvMap.empty;
       trans_env_repr := fun y => eq_refl |}.

Definition trans_global_env (d : Ast.Env.global_env) : global_env_map :=
  let init := empty_trans_env d.(Ast.Env.universes) d.(Ast.Env.retroknowledge) in
  trans_global_decls init d.(Ast.Env.declarations).

Definition trans_global (Σ : Ast.Env.global_env_ext) : global_env_ext_map :=
  (trans_global_env (fst Σ), snd Σ).

Definition trans_template_program (p : TemplateProgram.template_program) : pcuic_program :=
  let Σ' := trans_global (Ast.Env.empty_ext p.1) in
  (Σ', trans Σ' p.2).

