From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICRelevance
  PCUICClosedTyp PCUICGlobalEnv
  PCUICTyping PCUICInversion PCUICConversion PCUICCumulProp PCUICWeakeningTyp PCUICValidity PCUICWellScopedCumulativity BDUnique.

Require Import ssreflect.
From Equations Require Import Equations.

Definition relevance_from_term_from_type {cf : checker_flags} (Σ : global_env_ext) Γ t T :=
  forall rel, isTermRel Σ (marks_of_context Γ) t rel <~> isTypeRel Σ Γ T rel.

Lemma cumul_sort_relevance {cf : checker_flags} (Σ : global_env_ext) Γ T s1 s2 :
  wf Σ.1 ->
  Σ ;;; Γ |- T : tSort s1 -> Σ ;;; Γ |- T : tSort s2 -> relevance_of_sort s1 = relevance_of_sort s2.
Proof.
  intros wfΣ Hs1 Hs2.
  destruct (principal_type _ Hs1) as (ss & Hs & Hty); tea.
  apply Hs in Hs1, Hs2.
  eapply cumul_sort_confluence with (1 := Hs1) in Hs2 as (s & _ & le1 & le2).
  transitivity (relevance_of_sort s). 
  * eapply leq_relevance => //. tea.
  * eapply geq_relevance => //. tea.
Qed.

Lemma isTypeRel2_relevance {cf : checker_flags} Σ Γ T rel1 rel2 :
  wf Σ.1 ->
  isTypeRel Σ Γ T rel1 -> isTypeRel Σ Γ T rel2 -> rel1 = rel2.
Proof.
  intros wfΣ (s1 & <- & Hs1) (s2 & <- & Hs2).
  now eapply cumul_sort_relevance.
Qed.

Lemma ind_arity_relevant {cf : checker_flags} (Σ : global_env_ext) mdecl idecl :
  wf Σ.1 ->
  let ind_type := it_mkProd_or_LetIn (ind_params mdecl) (it_mkProd_or_LetIn (ind_indices idecl) (tSort (ind_sort idecl))) in
  isType Σ [] ind_type ->
  isTypeRel Σ [] ind_type Relevant.
Proof.
  intros wfΣ ind_type (s & e & Hs).
  eexists; split => //; tea.
  rewrite /ind_type in Hs.
  rewrite -it_mkProd_or_LetIn_app in Hs.
  assert (wfΓ : wf_local Σ []) by pcuic.
  revert wfΓ Hs. generalize ((ind_indices idecl ++ ind_params mdecl : context)) as l, ([]: context) as Γ.
  induction l using rev_ind.
  * cbn. intros Γ wfΓ Hty; apply inversion_Sort in Hty as (_ & _ & le); tea.
    apply ws_cumul_pb_Sort_inv in le.
    eapply leq_relevance; tea.
    now destruct ind_sort.
  * rewrite it_mkProd_or_LetIn_app; cbn.
    destruct x, decl_body; cbn.
    - intros Γ wfΓ Hty; pose proof Hty; apply inversion_LetIn in Hty as (? & ? & ? & ? & ? & ? & le); tea.
      assert (wfΓ' : wf_local Σ (Γ,, vdef decl_name t decl_type)) by auto with pcuic.
      eapply IHl. apply wfΓ'.
      econstructor; eauto with pcuic. constructor; eauto with pcuic.
      apply ws_cumul_pb_LetIn_l_inv in le.
      unshelve epose proof (PCUICSpine.all_rels_subst_lift (Γ := Γ) (Δ := [vdef decl_name t decl_type]) (t := x0) (Δ' := []) _ _ _) => //=.
      all: change (Γ,,, [vdef decl_name t decl_type]) with (Γ ,, vdef decl_name t decl_type); tea.
      1,2: fvs.
      simpl in X0. rewrite PCUICLiftSubst.lift0_id in X0. rewrite PCUICLiftSubst.subst_empty in X0.
      change (subst0 _ _) with ((lift 1 1 x0) {0 := lift0 1 t}) in X0.
      rewrite -PCUICLiftSubst.distr_lift_subst10 in X0.
      eapply PCUICContextConversion.ws_cumul_pb_eq_le in X0.
      eapply cumulAlgo_cumulSpec.
      etransitivity. 1: apply X0.
      change (tSort _) with (lift0 1 (tSort s)).
      eapply (weakening_ws_cumul_pb (Γ' := []) (Γ'' := [vdef _ _ _]) le). fvs.
    - intros Γ wfΓ Hty; pose proof Hty; apply inversion_Prod in Hty as (? & s' & ? & ? & ? & le); tea.
      assert (wfΓ' : wf_local Σ (Γ,, vass decl_name decl_type)) by auto with pcuic.
      eapply IHl. apply wfΓ'.
      econstructor; eauto with pcuic. constructor; eauto with pcuic.
      eapply cumulAlgo_cumulSpec.
      etransitivity. 2: eapply (weakening_ws_cumul_pb (Γ' := []) (Γ'' := [vass _ _]) le); fvs.
      cbn.
      constructor. 1-3: fvs.
      constructor. apply leq_universe_product.
Qed.

Lemma nth_error_arities_context mdecl i idecl :
  nth_error (List.rev mdecl.(ind_bodies)) i = Some idecl ->
  nth_error (arities_context mdecl.(ind_bodies)) i =
    Some {| decl_name := {| binder_name := nNamed idecl.(ind_name); binder_relevance := Relevant |};
            decl_body := None;
            decl_type := idecl.(ind_type) |}.
  Proof using Type.
  generalize mdecl.(ind_bodies) => l.
  intros hnth.
  epose proof (nth_error_Some_length hnth). autorewrite with len in H.
  rewrite nth_error_rev in hnth. now autorewrite with len.
  rewrite List.rev_involutive in hnth. autorewrite with len in hnth.
  unfold arities_context.
  rewrite rev_map_spec.
  rewrite nth_error_rev; autorewrite with len; auto.
  rewrite List.rev_involutive nth_error_map.
  rewrite hnth. simpl. reflexivity.
Qed.

Lemma inversion_Rel_wt {cf : checker_flags} :
forall {Σ : global_env_ext} {Γ n T} {wfΣ : wf Σ},
  Σ ;;; Γ |- tRel n : T ->
  ∑ decl,
    [× wf_local Σ Γ,
      nth_error Γ n = Some decl,
      isTypeRel Σ Γ (lift0 (S n) (decl_type decl)) decl.(decl_name).(binder_relevance) &
      Σ ;;; Γ ⊢ lift0 (S n) (decl_type decl) ≤ T].
Proof.
  intros Σ Γ n T wfΣ h. depind h.
  - exists decl.
    assert (isTypeRel Σ Γ (lift0 (S n) (decl_type decl)) (binder_relevance (decl_name decl))).
    { destruct (PCUICTyping.nth_error_All_local_env e a); eauto. cbn in o.
      apply isTypeRelOpt_lift in l => //. 1:{ pose proof (nth_error_Some_length e). lia. } }
    split => //.
    apply isType_ws_cumul_pb_refl. destruct X as [s [_ Hs]]. now exists s.
  - destruct (IHh1 wfΣ) as [decl []]. exists decl; split => //.
    etransitivity; tea. eapply cumulSpec_typed_cumulAlgo; tea => //.
Qed.

Lemma isTypeRel_cstr_type {cf : checker_flags} Σ mdecl idecl cdecl n :
  wf Σ.1 ->
  nth_error (ind_bodies mdecl) n = Some idecl ->
  (cstr_type cdecl =
        it_mkProd_or_LetIn
          (mdecl.(ind_params) ,,, cdecl.(cstr_args))
          (mkApps (tRel (#|mdecl.(ind_params) ,,, cdecl.(cstr_args)| + (#|ind_bodies mdecl| - S n)))
            (to_extended_list_k mdecl.(ind_params) #|cdecl.(cstr_args)| ++
            cdecl.(cstr_indices)))) ->
    idecl.(ind_type)
      = it_mkProd_or_LetIn mdecl.(ind_params)
          (it_mkProd_or_LetIn idecl.(ind_indices) (tSort idecl.(ind_sort))) ->
    isSortRel idecl.(ind_sort) idecl.(ind_relevance) ->
    ctx_inst (typing Σ) (arities_context mdecl.(ind_bodies) ,,, mdecl.(ind_params) ,,, cdecl.(cstr_args))
      cdecl.(cstr_indices)
      (List.rev (lift_context #|cdecl.(cstr_args)| 0 idecl.(ind_indices))) ->
  isType Σ (arities_context mdecl.(ind_bodies)) (cstr_type cdecl) ->
  isTypeRel Σ (arities_context mdecl.(ind_bodies)) (cstr_type cdecl) idecl.(ind_relevance).
Proof.
  intros wfΣ H -> e1 <- c (s & _ & Hs); exists s; split => //=.
  eapply PCUICSpine.inversion_it_mkProd_or_LetIn in Hs.
  eapply inversion_mkApps in Hs as [tyapp [Happ Hsp]].
  eapply inversion_Rel_wt in Happ as [cdecl' [wfl hnth ht cum]] => //.
  rewrite nth_error_app_ge in hnth. lia.
  replace (#|ind_params mdecl,,, cstr_args cdecl| + (#|ind_bodies mdecl| - S n) - #|ind_params mdecl,,, cstr_args cdecl|) with (#|ind_bodies mdecl| - S n) in hnth by lia.
  pose proof (nth_error_Some_length H) as hlen. rewrite nth_error_rev // in H.
  eapply nth_error_arities_context in H. rewrite hnth in H.
  eapply PCUICSpine.typing_spine_strengthen in Hsp; tea. noconf H. clear cum hnth.
  cbn in Hsp.
  rewrite e1 !PCUICLiftSubst.lift_it_mkProd_or_LetIn -it_mkProd_or_LetIn_app /= in Hsp.
  eapply PCUICSpine.arity_typing_spine in Hsp as [_ leqs _]. now eapply leq_relevance; tea.
  destruct ht as [s' [_ hs]]. now exists s'.
Qed.

Lemma isType_of_constructor {cf : checker_flags} Σ mdecl idecl cdecl cstr u Γ :
  wf Σ.1 -> wf_local Σ Γ -> declared_constructor Σ.1 cstr mdecl idecl cdecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  isTypeRel Σ Γ (type_of_constructor mdecl cdecl cstr u) idecl.(ind_relevance).
Proof.
  intros wfΣ wfΓ isdecl h_cuu.
  pose proof (PCUICWeakeningEnvTyp.on_declared_constructor isdecl) as ((? & []) & ? & ? & []).
  eapply infer_typing_sort_impl with _ on_ctype; [apply relevance_subst_opt|]; intros Hty.
  instantiate (1 := u).
  replace Γ with ([] ,,, Γ) by apply app_context_nil_l.
  replace (type_of_constructor _ _ _ _) with (lift0 #|Γ| (type_of_constructor mdecl cdecl cstr u)).
  2: { rewrite PCUICLiftSubst.lift_closed //. eapply (PCUICClosedTyp.declared_constructor_closed_type isdecl). }
  change (tSort _) with (lift0 #|Γ| (tSort on_ctype.π1)@[u]).
  eapply @weakening with (Γ := []) => //.
  rewrite app_context_nil_l => //.
  destruct Σ as (Σ & φ).
  eapply PCUICUnivSubstitutionTyp.typing_subst_instance' in Hty => //=; tea. 
  change ((tSort _)@[u]) with (subst0 (inds (inductive_mind cstr.1) u (ind_bodies mdecl)) (tSort on_ctype.π1)@[u]).
  eapply @PCUICSubstitution.substitution with (Δ := []); tea.
  2: rewrite app_context_nil_l; apply Hty.
  2: { epose proof (PCUICWeakeningEnv.weaken_lookup_on_global_env' _ _ (InductiveDecl mdecl) wfΣ _); eauto. now split. Unshelve. 2: apply isdecl.p1.p1. }
  rewrite /inds /arities_context.
  clear -h_cuu isdecl wfΣ wfΓ.
  pose proof (PCUICClosedTyp.declared_minductive_closed isdecl.p1.p1).
  rewrite /PCUICClosed.closed_inductive_decl in H. move/andb_and: H => [] _ H.
  apply forallb_All in H.
  assert (Alli (fun i x => declared_inductive Σ {| inductive_mind := inductive_mind cstr.1; inductive_ind := i |} mdecl x) 0 (ind_bodies mdecl)).
  {
    apply forall_nth_error_Alli; intros.
    unfold declared_inductive.
    split => //=.
    apply isdecl.p1.p1.
  }
  induction (ind_bodies mdecl) using rev_ind => //=.
  - constructor.
  - rewrite rev_map_app app_length Nat.add_1_r => //=.
    apply All_app in H as (H & H1).
    apply Alli_app in X as (X & X1).
    constructor => //=; auto.
    clear H X IHl.
    inv H1. inv X1. clear X X0.
    rewrite /PCUICClosed.closed_inductive_body in H. rtoProp.
    rewrite PCUICClosed.subst_closedn.
    rewrite PCUICClosed.closedn_subst_instance => //.
    eapply type_Ind; eauto with pcuic.
    now rewrite Nat.add_0_r in H0.
Qed.

Lemma isTypeRel_subst_instance_decl {cf : checker_flags} {Σ Γ T r c decl u} :
  wf Σ.1 ->
  lookup_env Σ.1 c = Some decl ->
  isTypeRel (Σ.1, universes_decl_of_decl decl) Γ T r ->
  consistent_instance_ext Σ (universes_decl_of_decl decl) u ->
  isTypeRel Σ (subst_instance u Γ) (subst_instance u T) r.
Proof using Type.
  intros wfΣ look isty cu.
  eapply infer_typing_sort_impl with _ isty; [apply relevance_subst_opt|].
  intros Hs.
  eapply (PCUICUnivSubstitutionTyp.typing_subst_instance_decl _ _ _ (tSort _)) in Hs; tea.
Qed.

Lemma declared_projection_type_inst {cf:checker_flags} {Σ : global_env_ext} {mdecl idecl p cdecl pdecl Γ c u args} :
  wf Σ.1 ->
  declared_projection Σ p mdecl idecl cdecl pdecl ->
  Σ;;; Γ |- c : mkApps (tInd (proj_ind p) u) args ->
  isTypeRel Σ (PCUICInductives.projection_context p.(proj_ind) mdecl idecl u) 
    pdecl.(proj_type)@[u] pdecl.(proj_relevance).
Proof.
  intros wfΣ declp hc.
  eapply validity in hc.
  assert (wfΓ : wf_local Σ Γ) by pcuic.
  epose proof (PCUICInductives.isType_mkApps_Ind_inv wfΣ declp wfΓ hc) as [pars [argsub [? ? ? ? cu]]].
  epose proof (PCUICInductives.declared_projection_type wfΣ declp).
  rewrite -(PCUICInductiveInversion.projection_context_gen_inst declp cu).
  eapply isTypeRel_subst_instance_decl; tea. eapply declp. apply X.
  apply cu.
Qed.

Lemma isTypeRel_weaken {cf:checker_flags} {Σ : global_env_ext} {Γ Δ ty rel} :
  wf Σ -> wf_local Σ Γ ->
  isTypeRel Σ Δ ty rel ->
  isTypeRel Σ (Γ ,,, Δ) ty rel.
Proof.
  intros wfΣ wfΓ [s [hrel hty]].
  exists s; split => //.
  now eapply weaken_ctx.
Qed.

Lemma isTypeRel_projection {cf : checker_flags} Σ mdecl idecl cdecl pdecl p c args u Γ :
  wf Σ.1 -> declared_projection Σ.1 p mdecl idecl cdecl pdecl ->
  Σ;;; Γ |- c : mkApps (tInd (proj_ind p) u) args -> #|args| = ind_npars mdecl ->
  isTypeRel Σ Γ (subst0 (c :: List.rev args) (proj_type pdecl)@[u]) pdecl.(proj_relevance).
Proof.
  intros wfΣ declp declc hargs.
  epose proof (declared_projection_type_inst wfΣ declp declc).
  eapply (PCUICSubstitution.isTypeRel_substitution (Δ := [])).
  2:{ cbn. eapply isTypeRel_weaken; tea. pcuic. }
  eapply PCUICInductives.projection_subslet; tea.
  now eapply validity.
Qed.

Section OnInductives.
  Context {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ}.
    
  Context {mdecl ind idecl}
    (decli : declared_inductive Σ ind mdecl idecl).
  
Lemma on_minductive_wf_params_indices_inst_weaken {Γ} (u : Instance.t) :
consistent_instance_ext Σ (ind_universes mdecl) u ->
wf_local Σ Γ ->
wf_local Σ (Γ ,,, (ind_params mdecl ,,, ind_indices idecl)@[u]).
Proof.
intros. eapply weaken_wf_local; tea.
eapply PCUICInductives.on_minductive_wf_params_indices_inst; tea.
Qed.
End OnInductives.

Lemma spine_subst_alpha {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} Γ args inst Δ Δ' : 
  PCUICSpine.spine_subst Σ Γ args inst Δ ->
  All2 (PCUICEquality.compare_decls eq eq) Δ Δ' ->
  PCUICSpine.spine_subst Σ Γ args inst Δ'.
Proof.
  intros [] eqd.
  split => //.
  eapply PCUICSpine.wf_local_alpha; tea. eapply All2_app; trea.
  2:{ eapply PCUICSpine.subslet_eq_context_alpha; tea. }
  move: inst_ctx_subst. clear -eqd.
  induction 1 in Δ', eqd |- *; depelim eqd; try constructor; depelim c; subst.
  - constructor. now apply IHinst_ctx_subst.
  - constructor. eauto.
Qed.

Import PCUICAlpha.

Lemma arity_spine_alpha {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} Γ args T T' T'' : 
  isType Σ Γ T'' ->
  PCUICSpine.arity_spine Σ Γ T args T'' ->
  T ≡α T' ->
  PCUICSpine.arity_spine Σ Γ T' args T''.
Proof.
  intros isty sp. revert T'. induction sp; intros.
  - intros. constructor. auto.
    pose proof (isType_alpha _ _ _ isty X).
    eapply PCUICContextConversion.ws_cumul_pb_eq_le.
    destruct isty as [? []].
    constructor; fvs. red. apply PCUICEquality.upto_names_impl_eq_term. now symmetry.
  - intros. constructor => //.
    transitivity ty => //.
    eapply PCUICContextConversion.ws_cumul_pb_eq_le.
    constructor; fvs. 
    eapply PCUICConfluence.eq_term_upto_univ_napp_on_free_vars; tea. fvs.
    apply PCUICEquality.upto_names_impl_eq_term. now symmetry.
  - depelim X.
    constructor. eapply IHsp => //.
    eapply PCUICEquality.eq_term_upto_univ_subst; tc; auto.
  - depelim X.
    constructor.
    pose proof (validity t).
    eapply isType_alpha in X; tea. destruct X as [s [_ Hs]].
    econstructor; tea. eapply convSpec_cumulSpec. now apply eq_term_upto_univ_cumulSpec, PCUICEquality.upto_names_impl_eq_term.
    eapply IHsp => //. eapply PCUICEquality.eq_term_upto_univ_subst; tc; auto. reflexivity.
Qed.

Lemma eq_term_upto_univ_it_mkProd_or_LetIn (Γ Γ' : context) T : 
  All2 (PCUICEquality.compare_decls eq eq) Γ Γ' ->
  it_mkProd_or_LetIn Γ T ≡α it_mkProd_or_LetIn Γ' T.
Proof.
  induction Γ in Γ' |- * using PCUICInduction.ctx_length_rev_ind.
  - intros a; depelim a. reflexivity.
  - intros a.
    eapply All2_app_inv_l in a as [? [? [? []]]]. subst.
    depelim a0. depelim a0.
    rewrite !it_mkProd_or_LetIn_app.
    depelim c; subst; constructor; cbn; auto; try reflexivity.
    apply X => //.
    apply X => //.
Qed.

Lemma arity_spine_mkProd_alpha {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ args} {Δ Δ' : context} {T T'} : 
  isType Σ Γ T' ->
  PCUICSpine.arity_spine Σ Γ (it_mkProd_or_LetIn Δ T) args T' ->
  All2 (PCUICEquality.compare_decls eq eq) Δ Δ' ->
  PCUICSpine.arity_spine Σ Γ (it_mkProd_or_LetIn Δ' T) args T'.
Proof.
  intros isty sp eq.
  eapply arity_spine_alpha => //. exact sp.
  now apply eq_term_upto_univ_it_mkProd_or_LetIn.
Qed.

Lemma eq_annots_expand_lets_ctx (Γ : list aname) (Δ Δ' : context) :
  PCUICEquality.eq_annots Γ (expand_lets_ctx Δ Δ') <-> PCUICEquality.eq_annots Γ Δ'.
Proof.
  rewrite /expand_lets_ctx /expand_lets_k_ctx.
  etransitivity. eapply PCUICEquality.eq_annots_subst_context.
  eapply PCUICEquality.eq_annots_lift_context.
Qed.

Lemma eq_annots_ind_predicate_context ind mdecl idecl (pctx : list aname) :
  PCUICEquality.eq_annots pctx (ind_predicate_context ind mdecl idecl) ->
  PCUICEquality.eq_annots pctx (idecl_binder idecl :: ind_indices idecl).
Proof.
  rewrite /ind_predicate_context.
  intros eq. depelim eq; cbn in *.
  constructor => //.
  now eapply eq_annots_expand_lets_ctx.
Qed.

Lemma apply_predctx {cf : checker_flags} {Σ : global_env_ext} Γ (ci : case_info) p indices c ps mdecl idecl {wfΣ : wf Σ.1} :
  declared_inductive Σ ci mdecl idecl ->
  wf_predicate mdecl idecl p ->
  All2 (PCUICEquality.compare_decls eq eq) (pcontext p) (ind_predicate_context ci mdecl idecl) ->
  ctx_inst (typing Σ) Γ (pparams p ++ indices) (List.rev (ind_params mdecl,,, ind_indices idecl)@[puinst p]) ->
  Σ;;; Γ |- c : mkApps (tInd ci (puinst p)) (pparams p ++ indices) ->
  let predctx := case_predicate_context ci mdecl idecl p in
  let ptm := it_mkLambda_or_LetIn predctx (preturn p) in
  Σ;;; Γ,,, predctx |- preturn p : tSort ps -> Σ ;;; Γ |- mkApps ptm (indices ++ [c]) : tSort ps.
Proof.
  intros decli wfp hpctx ctxi hd predctx ptm hret.
  pose proof (validity hd) as ist.
  pose proof (PCUICInductiveInversion.isType_mkApps_Ind_smash decli ist). forward X. apply wfp.
  destruct X as [sppars [spinds cu]].
  eapply type_mkApps_arity. subst ptm. eapply PCUICGeneration.type_it_mkLambda_or_LetIn; tea.
  assert (wfΓ : wf_local Σ Γ) by pcuic.
  assert (wfu : wf_universe Σ ps). now eapply PCUICWfUniverses.typing_wf_universe in hret.
  unshelve epose proof (PCUICInductives.arity_spine_case_predicate (ci:=ci) (indices:=indices) wfΓ decli cu wfu sppars _ hd).
  now rewrite PCUICSR.smash_context_subst_context_let_expand in spinds.
  unshelve eapply (arity_spine_mkProd_alpha _ X).
  { now eapply PCUICArities.isType_Sort. }
  unfold predctx. unfold case_predicate_context, case_predicate_context_gen.
  symmetry; eapply PCUICCasesContexts.eq_binder_annots_eq.
  now eapply wf_pre_case_predicate_context_gen.
Qed.

Lemma relevance_term_to_type {cf : checker_flags} :
  env_prop relevance_from_term_from_type
    (fun Σ Γ => All_local_env (lift_typing relevance_from_term_from_type Σ) Γ).
Proof using Type.
  apply typing_ind_env; intros Σ wfΣ Γ wfΓ; intros **; rename_all_hyps; auto.
  - eapply All_local_env_impl.
    eapply All_local_env_over_2; tea.
    intros ??? H; apply lift_typing_impl with (1 := H); now intros ? [].
  - split; intro H.
    + depelim H. rewrite nth_error_map heq_nth_error in e. inv e.
      destruct (PCUICTyping.nth_error_All_local_env heq_nth_error wfΓ); eauto.
      apply isTypeRelOpt_lift => //.
      pose proof (nth_error_Some_length heq_nth_error); lia.
    + constructor. rewrite nth_error_map heq_nth_error /option_map.
      pose proof (PCUICTyping.nth_error_All_local_env heq_nth_error wfΓ).1; eauto.
      apply isTypeRelOpt_lift in X0 => //. 2: { pose proof (nth_error_Some_length heq_nth_error); lia. }
      eapply f_equal, isTypeRel2_relevance; tea.
  - split; intro Hr => //.
    + inv Hr.
      eexists; split.
      2: { constructor; tea. eauto with pcuic. }
      apply relevance_super.
    + destruct Hr as (s & <- & Hty) => //.
      apply inversion_Sort in Hty as (_ & _ & le) => //.
      eapply ws_cumul_pb_Sort_inv, leq_relevance in le => //.
      rewrite le relevance_super. constructor.
  - split; intro Hr.
    + inv Hr.
      eexists; split.
      2: { constructor; tea. eauto with pcuic. }
      apply relevance_super.
    + destruct Hr as (s & <- & Hty) => //.
      apply inversion_Sort in Hty as (_ & _ & le) => //.
      eapply ws_cumul_pb_Sort_inv, leq_relevance in le => //.
      rewrite le relevance_super. constructor.
  - split; intro Hr => //.
    + inv Hr.
      eapply X3 in X0 as (s & e & Hs).
      eexists; split.
      2: { constructor; tea. }
      destruct s, s1 => //.
    + destruct Hr as (s & <- & Hs).
      constructor. edestruct X3 as (_ & IH); eapply IH.
      apply inversion_Prod in Hs as (s1' & s2 & e1 & _ & Hty & le) => //.
      eexists; split; tea.
      eapply ws_cumul_pb_Sort_inv, leq_relevance in le => //.
      destruct s1', s2 => //.
  - split; intro Hr => //.
    + inv Hr.
      eapply X5 in X0 as (s & e & Hs).
      exists s; split => //.
      econstructor; tea.
      eapply type_LetIn; eauto. constructor; eauto with pcuic. do 2 constructor. apply cumul_zeta.
    + destruct Hr as (s & <- & Hs).
      constructor. edestruct X5 as (_ & IH); eapply IH.
      assert (wf_universe Σ s) by eauto with pcuic.
      apply inversion_LetIn in Hs as (s1' & s2 & e1 & ? & ? & Hty & le) => //.
      eapply ws_cumul_pb_Sort_r_inv in le as (ss & red & le) => //.
      eexists; split; tea.
      reflexivity.
      econstructor; eauto with pcuic. constructor; eauto with pcuic.
      eapply cumul_Trans. 4: apply cumul_Sort, le. 1,2: fvs.
      apply cumulAlgo_cumulSpec.
      apply invert_red_letin in red as [(? & ? & ? & []) | ?]; try discriminate.
      unshelve epose proof (PCUICSpine.all_rels_subst_lift (Γ := Γ) (Δ := [vdef na b b_ty]) (t := s2) (Δ' := []) _ _ _) => //=.
      all: change (Γ ,,, [_]) with (Γ ,, vdef na b b_ty). pcuic. fvs. fvs.
      simpl in X0. rewrite PCUICLiftSubst.lift0_id in X0. rewrite PCUICLiftSubst.subst_empty in X0.
      change (subst0 _ _) with ((lift 1 1 s2) {0 := lift0 1 b}) in X0.
      rewrite -PCUICLiftSubst.distr_lift_subst10 in X0.
      apply PCUICContextConversion.ws_cumul_pb_eq_le in X0.
      etransitivity. 1: apply X0.
      change (tSort ss) with (lift0 1 (tSort ss)).
      eapply red_conv in c.
      eapply (weakening_ws_cumul_pb (Γ' := []) (Γ'' := [vdef _ _ _]) c). fvs.
  - split; intro Hr => //.
    + inv Hr. eapply X3 in X0 as (s' & e & Hs).
      assert (wf_universe Σ s') by auto with pcuic.
      apply inversion_Prod in Hs as (? & ss & ? & ? & ? & le); tea.
      exists s'; split => //.
      econstructor; tea. instantiate (1 := tSort ss). 2: constructor; eauto with pcuic.
      2: { apply cumul_Sort. apply ws_cumul_pb_Sort_inv in le. etransitivity. apply leq_universe_product. tea. }
      change (tSort ss) with ((tSort ss) { 0 := u }).
      eapply PCUICSubstitution.substitution0; tea.
    + destruct Hr as (s' & <- & Hs).
      constructor. edestruct X3 as (_ & IH); eapply IH; clear IH.
      assert (wf_universe Σ s') by eauto with pcuic.
      exists s; split => //.
      apply inversion_Prod in IHB as (s1 & s2 & ? & ? & Hty & le) => //.
      eapply (PCUICSubstitution.substitution0 Hty) in typeu; tea. cbn in typeu.
      transitivity (relevance_of_sort s2).
      2: eapply cumul_sort_relevance; tea.
      apply ws_cumul_pb_Sort_inv in le; destruct s2, s1, s => //.
  - apply PCUICWeakeningEnvTyp.on_declared_constant in H as H'; tea. unfold on_constant_decl in H'.
    split; intro Hr => //.
    + inv Hr.
      assert (decl = decl0). { unfold declared_constant in H, H0. rewrite H in H0. now do 2 inversion H. } subst decl0.
      destruct H' as (H' & _).
      eapply infer_typing_sort_impl with _ H' => //; [apply relevance_subst_opt|]. intro Hty.
      apply (weaken_ctx (Γ := [])); tea.
      destruct Σ as (Σ & φ); unfold fst in *.
      instantiate (1 := u).
      eapply (PCUICUnivSubstitutionTyp.typing_subst_instance' _ _ [] _ (tSort H'.π1) u _); tea.
      unshelve epose proof (PCUICWeakeningEnv.weaken_lookup_on_global_env' _ _ (ConstantDecl decl) wf _); eauto.
      now split.
    + enough (cst_relevance decl = rel) by (subst rel; constructor => //).
      destruct H' as (H' & _).
      destruct Hr as (s1 & <- & Hs1), H' as (s2 & <- & Hs2).
      erewrite <- relevance_subst_eq.
      eapply cumul_sort_relevance; tea.
      apply (weaken_ctx (Γ := [])); tea.
      destruct Σ as (Σ & φ); unfold fst in *. instantiate (1 := u).
      eapply (PCUICUnivSubstitutionTyp.typing_subst_instance' _ _ [] _ (tSort _) u _); tea.
      unshelve epose proof (PCUICWeakeningEnv.weaken_lookup_on_global_env' _ _ (ConstantDecl decl) wf _); eauto.
      now split.
  - pose proof (onArity (PCUICWeakeningEnvTyp.on_declared_inductive isdecl).2).
    destruct Σ as (Σ & φ); unfold fst in *.
    split; intro Hr => //.
    + inv Hr.
      eapply infer_typing_sort_impl with _ X1; [apply relevance_subst_opt|]; intros Hty.
      eapply PCUICUnivSubstitutionTyp.typing_subst_instance' in Hty.
      eapply (weaken_ctx (Γ := [])) in Hty.
      apply Hty.
      all: tea.
      unshelve epose proof (PCUICWeakeningEnv.weaken_lookup_on_global_env' _ _ (InductiveDecl mdecl) wf isdecl.p1); eauto. now split.
    + enough (Relevant = rel) by (subst rel; constructor => //).
      destruct Hr as (s1 & <- & Hs1), X1 as (s2 & <- & Hs2).
      eapply PCUICUnivSubstitutionTyp.typing_subst_instance' in Hs2.
      eapply (weaken_ctx (Γ := [])) in Hs2.
      all: tea.
      2: { epose proof (PCUICWeakeningEnv.weaken_lookup_on_global_env' _ _ (InductiveDecl mdecl) wf isdecl.p1); eauto. now split. }
      erewrite <- relevance_subst_eq.
      eapply cumul_sort_relevance; tea. apply wf.
  - pose proof (declared_constructor_lookup isdecl).
    destruct (PCUICWeakeningEnvTyp.on_declared_constructor isdecl) as ([[] []] & cu & ? & []); tea.
    split; intro Hr => //.
    + inv Hr.
      assert (idecl = idecl0). { clear -H0 isdecl. destruct H0 as ((H0m & H0i) & H0c), isdecl as ((Hm & Hi) & Hc). unfold declared_minductive in Hm, H0m. rewrite H0m in Hm. do 2 inversion Hm. subst mdecl0. rewrite H0i in Hi. now inversion Hi. } subst idecl0.
      destruct Σ as (Σ & φ); unfold fst, snd in *.
      apply isType_of_constructor; tea.
    + enough (idecl.(ind_relevance) = rel) by (subst rel; econstructor; apply isdecl).
      destruct Σ as (Σ & φ); unfold fst, snd in *.
      eassert (isTypeRel (Σ, φ) _ (type_of_constructor mdecl cdecl (ind, i) u) (idecl.(ind_relevance))) by (apply isType_of_constructor; tea).
      eapply isTypeRel2_relevance; tea. apply wf.
  - assert (Σ ;;; Γ |- mkApps ptm (indices ++ [c]) : tSort ps). 
    { apply apply_predctx => //. eapply ctx_inst_impl with (2 := X5) => ???[] //. }
    split; intro Hr => //.
    + inv Hr.
      exists ps; split => //.
    + enough (rel = ci.(ci_relevance)) by (subst rel; constructor).
      eapply isTypeRel2_relevance; tea.
      exists ps; split => //.
  - pose proof (declared_projection_lookup isdecl).
    assert (isTypeRel Σ Γ (subst0 (c :: List.rev args) (proj_type pdecl)@[u]) (pdecl.(proj_relevance))) by (eapply isTypeRel_projection; tea).
    split; intro Hr => //.
    + inv Hr.
      destruct (declared_projection_inj isdecl H0) as [? [? []]]; subst mdecl0 idecl0 cdecl0 pdecl0.
      assumption.
    + enough (pdecl.(proj_relevance) = rel) by (subst rel; econstructor; apply isdecl).
      eapply isTypeRel2_relevance; tea.
  - eapply All_nth_error in X0, X1; tea.
    rewrite /on_def_type /on_def_body /lift_typing2 in X0, X1.
    split; intro Hr => //.
    + inv Hr. rewrite H0 in heq_nth_error; inversion heq_nth_error; subst def.
      apply lift_typing_impl with (1 := X0); now intros ? [].
    + eenough (rel = _) by (erewrite H0; constructor; tea).
      eapply isTypeRel2_relevance; tea.
      apply infer_typing_sort_impl with id X0 => //.
      now intros [].
  - eapply All_nth_error in X0, X1; tea.
    rewrite /on_def_type /on_def_body /lift_typing2 in X0, X1.
    split; intro Hr => //.
    + inv Hr. rewrite H0 in heq_nth_error; inversion heq_nth_error; subst def.
      apply lift_typing_impl with (1 := X0); now intros ? [].
    + eenough (rel = _) by (erewrite H0; constructor; tea).
      eapply isTypeRel2_relevance; tea.
      apply infer_typing_sort_impl with id X0 => //.
      now intros [].
  - split; intro Hr => //.
    + eexists; split; tea.
      apply X1 in Hr as (s' & <- & Hs').
      enough (cumul_prop Σ Γ (tSort s) (tSort s')).
      { apply PCUICCumulProp.cumul_sort_inv in X0. now destruct s, s'. }
      pose proof (cumulSpec_typed_cumulAlgo typet typeB cumulA).
      apply ws_cumul_pb_forget, PCUICCumulativity.cumul_alt in X0 as (A' & B' & [[red1 red2] leq]).
      eapply PCUICSR.subject_reduction in red1, red2; tea.
      eapply typing_leq_term_prop; tea.
    + apply X1.
      pose proof typet.
      apply validity in X0 as (s' & _ & Hty).
      eexists; split; tea.
      enough (relevance_of_sort s = relevance_of_sort s').
      { cbn; rewrite -H. destruct Hr as (ss & <- & Hss). eapply cumul_sort_relevance; tea. }
      enough (cumul_prop Σ Γ (tSort s) (tSort s')).
      { apply PCUICCumulProp.cumul_sort_inv in X0. now destruct s, s'. }
      pose proof (cumulSpec_typed_cumulAlgo typet typeB cumulA).
      apply ws_cumul_pb_forget, PCUICCumulativity.cumul_alt in X0 as (A' & B' & [[red1 red2] leq]).
      eapply PCUICSR.subject_reduction in red1, red2; tea.
      eapply typing_leq_term_prop; tea.
Qed.


Theorem relevance_from_type {cf : checker_flags} (Σ : global_env_ext) Γ t T rel :
  wf Σ -> Σ ;;; Γ |- t : T ->
  isTermRel Σ (marks_of_context Γ) t rel <~> isTypeRel Σ Γ T rel.
Proof.
  intros wfΣ Hty.
  pose proof relevance_term_to_type.
  eapply env_prop_typing in X; tea.
  apply X.
Qed.
