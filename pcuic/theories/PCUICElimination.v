(* Distributed under the terms of the MIT license. *)
From Coq Require Import ssrbool.
From MetaCoq.Template Require Import config utils Universes.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTactics PCUICCasesContexts
     PCUICTyping PCUICGlobalEnv
     PCUICLiftSubst PCUICInductives PCUICGeneration PCUICSpine
     PCUICWeakeningEnv PCUICWeakeningEnvTyp
     PCUICSubstitution PCUICUnivSubst PCUICUnivSubstitutionConv PCUICUnivSubstitutionTyp
     PCUICConversion PCUICCumulativity PCUICConfluence PCUICContexts
     PCUICSR PCUICInversion PCUICValidity PCUICSafeLemmata
     PCUICContextConversion PCUICContextConversionTyp
     PCUICCumulProp PCUICWellScopedCumulativity PCUICArities.
From MetaCoq.PCUIC Require Import PCUICInductiveInversion PCUICOnFreeVars PCUICEquality.

Require Equations.Prop.DepElim.
From Equations Require Import Equations.
Require Import ssreflect.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

Definition Is_proof `{cf : checker_flags} Σ Γ t := ∑ T u, Σ ;;; Γ |- t : T × Σ ;;; Γ |- T : tSort u ×
  (Universe.is_prop u || Universe.is_sprop u).

Definition SingletonProp `{cf : checker_flags} (Σ : global_env_ext) (ind : inductive) :=
  forall mdecl idecl,
    declared_inductive (fst Σ) ind mdecl idecl ->
    forall Γ args u n (Σ' : global_env_ext),
      wf Σ' ->
      extends_decls Σ Σ' ->
      welltyped Σ' Γ (mkApps (tConstruct ind n u) args) ->
      ∥Is_proof Σ' Γ (mkApps (tConstruct ind n u) args)∥ /\
       #|ind_ctors idecl| <= 1 /\
       squash (All (Is_proof Σ' Γ) (skipn (ind_npars mdecl) args)).

Definition Computational `{cf : checker_flags} (Σ : global_env_ext) (ind : inductive) :=
  forall mdecl idecl,
    declared_inductive (fst Σ) ind mdecl idecl ->
    forall Γ args u n (Σ' : global_env_ext),
      wf Σ' ->
      extends_decls Σ Σ' ->
      welltyped Σ' Γ (mkApps (tConstruct ind n u) args) ->
      Is_proof Σ' Γ (mkApps (tConstruct ind n u) args) -> False.

Definition Informative `{cf : checker_flags} (Σ : global_env_ext) (ind : inductive) :=
  forall mdecl idecl,
    declared_inductive (fst Σ) ind mdecl idecl ->
    forall Γ args u n (Σ' : global_env_ext),
      wf_ext Σ' ->
      extends_decls Σ Σ' ->
      Is_proof Σ' Γ (mkApps (tConstruct ind n u) args) ->
       #|ind_ctors idecl| <= 1 /\
       squash (All (Is_proof Σ' Γ) (skipn (ind_npars mdecl) args)).


Lemma typing_spine_case_predicate {cf: checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ} {ci : case_info}
  {mdecl idecl} {u params indices ps} {c} :
  wf_local Σ Γ ->
  declared_inductive Σ ci mdecl idecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  wf_universe Σ ps ->
  spine_subst Σ Γ params (List.rev params)
    (smash_context [] (subst_instance u (ind_params mdecl))) ->
  spine_subst Σ Γ indices (List.rev indices)
    (subst_context_let_expand (List.rev params)
        (subst_instance u (ind_params mdecl))
        (smash_context [] (subst_instance u (ind_indices idecl)))) ->
  Σ ;;; Γ |- c : mkApps (tInd ci u) (params ++ indices) ->
  typing_spine Σ Γ
    (it_mkProd_or_LetIn
      (pre_case_predicate_context_gen ci mdecl idecl params u)
      (tSort ps))
    (indices ++ [c]) (tSort ps).
Proof.
  intros.
  apply wf_arity_spine_typing_spine; split.
  now eapply isType_case_predicate.
  now eapply arity_spine_case_predicate; auto.
Qed.


Lemma pre_case_predicate_context_gen_eq {cf: checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ} {ci : case_info}
  {mdecl idecl} {ps} {p} :
  wf_local Σ Γ ->
  declared_inductive Σ ci mdecl idecl ->
  consistent_instance_ext Σ (ind_universes mdecl) (puinst p) ->
  wf_universe Σ ps ->
  spine_subst Σ Γ (pparams p) (List.rev (pparams p))
    (smash_context [] (ind_params mdecl)@[puinst p]) ->
  Σ ⊢ Γ ,,, pre_case_predicate_context_gen ci mdecl idecl (pparams p) (puinst p) =
      Γ ,,, case_predicate_context' ci mdecl idecl p.
Proof.
  intros wf decli cu wfps sp.
  eapply alpha_eq_context_ws_cumul_ctx_pb.
  * eapply All2_app. 2:reflexivity.
    rewrite /pre_case_predicate_context_gen /inst_case_context /ind_predicate_context.
    rewrite /case_predicate_context' /=. cbn.
    rewrite subst_context_snoc; len.
    constructor. constructor; cbn. reflexivity.
    rewrite subst_instance_mkApps subst_mkApps. f_equal. cbn.
    now rewrite [subst_instance_instance _ _](subst_instance_id_mdecl _ _ _ cu).
    rewrite [to_extended_list _]to_extended_list_k_app; len; rewrite !map_app.
    f_equal.
    rewrite subst_instance_to_extended_list_k.
    erewrite subst_to_extended_list_k. reflexivity.
    eapply inst_ctx_subst in sp.
    eapply PCUICContextSubst.make_context_subst_spec_inv. rewrite List.rev_involutive.
    now rewrite subst_instance_smash.
    rewrite subst_instance_to_extended_list_k /=.
    rewrite /expand_lets_ctx /expand_lets_k_ctx /=.
    rewrite subst_instance_subst_context subst_instance_lift_context.
    rewrite to_extended_list_k_subst to_extended_list_k_lift_context.
    rewrite PCUICLiftSubst.map_subst_instance_to_extended_list_k.
    erewrite <-to_extended_list_k_map_subst. reflexivity. lia.
    eapply All2_refl. reflexivity.
  * epose proof (isType_case_predicate (puinst p) (pparams p) ps wf decli cu wfps sp).
    eapply isType_it_mkProd_or_LetIn_inv in X.
    eapply isType_wf_local in X. fvs.
Qed.

Lemma elim_restriction_works_kelim1 {cf : checker_flags} {Σ : global_env_ext}
  {Γ T ci p c brs mdecl idecl} :
  check_univs ->
  wf_ext Σ ->
  declared_inductive Σ ci.(ci_ind) mdecl idecl ->
  Σ ;;; Γ |- tCase ci p c brs : T ->
  (Is_proof Σ Γ (tCase ci p c brs) -> False) ->
  ind_kelim idecl = IntoAny \/ ind_kelim idecl = IntoSetPropSProp.
Proof.
  intros cu wfΣ. intros.
  assert (HT := X).
  eapply inversion_Case in X as [mdecl' [idecl' [isdecl' [indices [data cum]]]]]; eauto.
  destruct data.
  eapply declared_inductive_inj in isdecl' as []. 2:exact H. subst.
  enough (~ (Universe.is_prop ps \/ Universe.is_sprop ps)).
  { clear -cu wfΣ allowed_elim H1.
    apply wf_ext_consistent in wfΣ as (val&sat).
    unfold is_allowed_elimination, is_lSet, eq_universe, eq_levelalg in *.
    rewrite cu in allowed_elim.
    destruct (ind_kelim idecl); auto; destruct ps; cbn in *; try discriminate;
    intuition congruence. }
  intros Huf. apply H0.
  red. exists (mkApps ptm (indices ++ [c])); intuition auto.
  exists ps.
  assert (Σ;;; Γ |- tCase ci p c brs : mkApps ptm (indices ++ [c])).
  econstructor; eauto. repeat (split; auto).
  repeat split; auto. split; auto. split; auto. clear brs_ty.
  eapply type_mkApps. rewrite /ptm.
  eapply type_it_mkLambda_or_LetIn; tea.
  assert (wf Σ) by apply wfΣ.
  pose proof (PCUICInductiveInversion.isType_mkApps_Ind_smash H (validity scrut_ty)).
  forward X1. apply (wf_predicate_length_pars wf_pred).
  simpl in X1. destruct X1 as [sppars [spargs cu']].
  assert (eqctx' : All2 (PCUICEquality.compare_decls eq eq)
  (Γ,,, case_predicate_context' ci mdecl idecl p)
  (Γ,,, predctx)).
  { eapply All2_app. 2:eapply All2_refl; reflexivity.
    eapply case_predicate_context_alpha => //; tea.
    destruct wf_pred. eapply Forall2_All2 in H2.
    depelim H2. rewrite H3. constructor; auto. }
  assert (Σ ⊢ Γ ,,, pre_case_predicate_context_gen ci mdecl idecl (pparams p) (puinst p) = Γ ,,, predctx).
  { transitivity (Γ ,,, case_predicate_context' ci mdecl idecl p); revgoals.
    * symmetry. eapply alpha_eq_context_ws_cumul_ctx_pb => //; fvs. now symmetry.
    * eapply pre_case_predicate_context_gen_eq; tea. pcuic.
      now eapply PCUICWfUniverses.typing_wf_universe in pret_ty. }
  unshelve epose proof (typing_spine_case_predicate (ps:=ps) _ H cons _ sppars). 1-2:shelve.
  * pcuic.
  * now eapply PCUICWfUniverses.typing_wf_universe in pret_ty.
  * rewrite -smash_context_subst_context_let_expand in X2.
    specialize (X2 spargs scrut_ty).
    eapply typing_spine_strengthen; tea; revgoals.
    + eapply ws_cumul_pb_it_mkProd_or_LetIn.
      eapply ws_cumul_ctx_pb_rel_app.
      now symmetry.
      apply ws_cumul_pb_refl; fvs.
    + eapply validity in pret_ty.
      eapply isType_it_mkProd_or_LetIn; tea.
  * destruct Huf as [Huf|Huf]; rewrite Huf // orb_true_r //.
Qed.

Lemma elim_sort_intype {cf:checker_flags} Σ mdecl ind idecl ind_indices ind_sort cdecls :
  Universe.is_prop ind_sort ->
  elim_sort_prop_ind cdecls = IntoAny ->
  on_constructors cumulSpec0 (lift_typing typing)
    (Σ, ind_universes mdecl) mdecl
    (inductive_ind ind) idecl ind_indices
    (ind_ctors idecl) cdecls ->
  (#|ind_ctors idecl| = 0) +
  (∑ cdecl cdecl_sorts,
    (ind_ctors idecl = [cdecl]) *
    (cdecls = [cdecl_sorts]) *
    (Forall is_propositional cdecl_sorts) *
    (on_constructor cumulSpec0 (lift_typing typing) (Σ, ind_universes mdecl) mdecl
        (inductive_ind ind) idecl ind_indices cdecl cdecl_sorts))%type.
Proof.
  intros uf lein onc.
  induction onc; simpl in *.
  left; auto.
  destruct l' as [|c cs].
  - simpl in *. depelim onc.
    right.
    destruct forallb eqn:fo => //.
    eapply forallb_Forall in fo.
    eexists; eauto.
  - discriminate.
Qed.

Lemma typing_spine_it_mkProd_or_LetIn_full_inv {cf:checker_flags} Σ Γ Δ s args s' :
  wf Σ.1 ->
  typing_spine Σ Γ (it_mkProd_or_LetIn Δ (tSort s)) args (tSort s') ->
  leq_universe (global_ext_constraints Σ) s s'.
Proof.
  intros wfΣ.
  induction Δ using PCUICInduction.ctx_length_rev_ind in args |- *.
  - simpl. intros sp; dependent elimination sp as [spnil _ _ e|spcons isty isty' e _ sp].
    now eapply ws_cumul_pb_Sort_inv in e.
    now eapply ws_cumul_pb_Sort_Prod_inv in e.
  - rewrite it_mkProd_or_LetIn_app; destruct d as [na [b|] ty]; simpl.
    * intros sp.
      specialize (H (subst_context [b] 0 Γ0) ltac:(now autorewrite with len)).
      eapply PCUICArities.typing_spine_letin_inv in sp; auto.
      rewrite /subst1 subst_it_mkProd_or_LetIn in sp. simpl in sp. eauto.
    * intros sp. dependent elimination sp as [spnil _ _ e|spcons isty isty' e tyhd sp];
        [now eapply ws_cumul_pb_Prod_Sort_inv in e|].
      specialize (H (subst_context [hd0] 0 Γ0) ltac:(now autorewrite with len) tl0).
      apply H.
      eapply PCUICArities.isType_tProd in isty as [? ?]; auto. cbn in *.
      eapply ws_cumul_pb_Prod_Prod_inv in e as [eqann conv cum]; auto. simpl in *.
      eapply typing_spine_strengthen; eauto; revgoals.
      eapply (substitution0_ws_cumul_pb (t:=hd0)) in cum; auto.
      simpl in cum.
      now rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r in cum.
      unshelve eapply (isType_subst (Δ := [vass _ _]) [hd0]) in i0; pcuic.
      now rewrite subst_it_mkProd_or_LetIn in i0.
      eapply subslet_ass_tip. eapply (type_ws_cumul_pb (pb:=Conv)); tea. now symmetry.
Qed.

Inductive All_local_assum (P : context -> term -> Type) : context -> Type :=
| localassum_nil :
    All_local_assum P []

| localassum_cons_abs Γ na t :
    All_local_assum P Γ ->
    P Γ t ->
    All_local_assum P (Γ ,, vass na t)

| localassum_cons_def Γ na b t :
    All_local_assum P Γ ->
    All_local_assum P (Γ ,, vdef na b t).

Derive Signature for All_local_assum.

Lemma All_local_assum_app P Γ Δ : All_local_assum P (Γ ++ Δ) ->
  All_local_assum P Δ *
  All_local_assum (fun Γ' => P (Δ ,,, Γ')) Γ.
Proof.
  induction Γ; simpl; constructor; intuition auto.
  constructor. depelim X; apply IHΓ; auto.
  depelim X; constructor; try apply IHΓ; auto.
Qed.

Lemma All_local_assum_subst {cf:checker_flags} (P Q : context -> term -> Type) c n k :
  All_local_assum Q c ->
  (forall Γ t,
      Q Γ t ->
      P (subst_context n k Γ) (subst n (#|Γ| + k) t)
  ) ->
  All_local_assum P (subst_context n k c).
Proof.
  intros Hq Hf.
  induction Hq in |- *; try econstructor; eauto;
    simpl; unfold snoc; rewrite subst_context_snoc; econstructor; eauto.
Qed.

Lemma wf_ext_wf {cf:checker_flags} Σ : wf_ext Σ -> wf Σ.
Proof. move=> wfe; apply wfe. Qed.
#[global]
Hint Resolve wf_ext_wf : core.

Lemma is_propositional_subst_instance u s :
  is_propositional (subst_instance_univ u s) = is_propositional s.
Proof. destruct s => //. Qed.

Lemma leq_universe_propositional_l {cf:checker_flags} ϕ u1 u2 :
  check_univs ->
  prop_sub_type = false ->
  consistent ϕ ->
  leq_universe ϕ u1 u2 -> is_propositional u1 -> u1 = u2.
Proof.
  intros Hcf ps cu le.
  unfold is_propositional.
  destruct (Universe.is_prop u1) eqn:eq.
  apply leq_universe_prop_no_prop_sub_type in le; auto.
  simpl. now destruct u1, u2.
  simpl. intros sp.
  apply leq_universe_sprop_l in le; auto.
  now destruct u1, u2.
Qed.

Lemma isType_ws_cumul_ctx_pb {cf Σ Γ Δ T} {wfΣ : wf Σ}:
  isType Σ Γ T ->
  wf_local Σ Δ ->
  Σ ⊢ Γ = Δ ->
  isType Σ Δ T.
Proof.
  intros HT wf eq.
  apply infer_sort_impl with id HT; intros Hs.
  eapply closed_context_conversion; tea.
Qed.

Lemma typing_spine_proofs {cf:checker_flags} Σ Γ Δ ind u args' args T' s :
  check_univs ->
  wf_ext Σ ->
  Σ ;;; Γ |-  T' : tSort s ->
  typing_spine Σ Γ (it_mkProd_or_LetIn Δ (mkApps (tInd ind u) args')) args T' ->
  ((All_local_assum (fun Γ' t =>
      (∑ s, (Σ ;;; Γ ,,, Γ' |- t : tSort s) * is_propositional s)%type) Δ ->
    ∥ All (Is_proof Σ Γ) args ∥) *
    (forall mdecl idecl
    (Hdecl : declared_inductive Σ.1 ind mdecl idecl),
      consistent_instance_ext Σ (ind_universes mdecl) u ->
      ((is_propositional s -> s = subst_instance_univ u idecl.(ind_sort)) /\
       (prop_sub_type = false ->
        is_propositional (subst_instance_univ u idecl.(ind_sort)) ->
        s = subst_instance_univ u idecl.(ind_sort)))))%type.
Proof.
  intros checku wfΣ Ht.
  induction Δ using PCUICInduction.ctx_length_rev_ind in Γ, args', args, T', Ht |- *; simpl; intros sp.
  - dependent elimination sp as [spnil _ _ e|spcons isty isty' e _ sp].
    split; [repeat constructor|].
    * eapply ws_cumul_pb_Ind_l_inv in e as [ui' [l' [red Req argeq]]] => //; auto.
      intros mdecl idecl decli cu.
      destruct (on_declared_inductive decli) as [onmind oib].
      eapply subject_reduction_closed in Ht; eauto.
      eapply inversion_mkApps in Ht as [A [tInd sp]]; auto.
      eapply inversion_Ind in tInd as [mdecl' [idecl' [wfΓ [decli' [cu' cum]]]]]; auto.
      destruct (declared_inductive_inj decli decli'); subst mdecl' idecl'.
      clear decli'.
      eapply typing_spine_strengthen in sp. 3:tea.
      rewrite (oib.(ind_arity_eq)) in sp.
      rewrite !subst_instance_it_mkProd_or_LetIn in sp.
      rewrite -it_mkProd_or_LetIn_app in sp.
      eapply typing_spine_it_mkProd_or_LetIn_full_inv in sp; auto.
      split.
      intros Hs.
      destruct s => //.
      eapply leq_universe_prop_r in sp; auto.
      rewrite (is_prop_subst_instance_univ ui') in sp => //.
      now destruct (ind_sort idecl).
      apply wfΣ.
      eapply leq_universe_sprop_r in sp; auto.
      rewrite (is_sprop_subst_instance_univ ui') in sp => //.
      now destruct (ind_sort idecl).
      apply wfΣ.
      intros propsub props.
      rewrite is_propositional_subst_instance in props.
      apply leq_universe_propositional_l in sp; eauto. subst s.
      now destruct (ind_sort idecl).
      now destruct (ind_sort idecl).
      now eapply declared_inductive_valid_type.

    * now eapply invert_cumul_ind_prod in e.

  - destruct d as [na [b|] ty].
    + rewrite it_mkProd_or_LetIn_app in sp.
      simpl in sp.
      eapply PCUICArities.typing_spine_letin_inv in sp => //; auto.
      rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r in sp.
      specialize (H (subst_context [b] 0 Γ0) ltac:(now autorewrite with len)).
      rewrite subst_mkApps in sp.
      specialize (H _ _ _ _ Ht sp).
      split.
      * intros prs;eapply All_local_assum_app in prs as [prd prs].
        depelim prd.
        apply H.
        clear -wfΣ prs.
        eapply All_local_assum_subst; eauto.
        simpl. intros.
        destruct X as [s [Ht2 isp]].
        exists s; pcuicfo.
        rewrite Nat.add_0_r. eapply (substitution (Γ' := [vdef na b ty]) (s := [b]) (Δ := Γ1) (T:=tSort s)); auto.
        eapply subslet_def_tip.
        eapply typing_wf_local in Ht2.
        rewrite app_context_assoc in Ht2. eapply All_local_env_app_inv in Ht2 as [Ht2 _].
        depelim Ht2. apply l0.
        now rewrite app_context_assoc in Ht2.
      * intros mdecl idec decli.
        now apply H.
    + rewrite it_mkProd_or_LetIn_app in sp.
      destruct args. split; [repeat constructor|].
      * dependent elimination sp as [spnil _ _ e].
        unfold mkProd_or_LetIn in e; simpl in e.
        eapply ws_cumul_pb_Prod_l_inv in e as [na' [dom' [codom' [red eqann conv cum]]]]; auto.
        eapply subject_reduction_closed in Ht; eauto.
        intros.
        pose proof (PCUICWfUniverses.typing_wf_universe wfΣ Ht).
        eapply inversion_Prod in Ht as [s1 [s2 [dom [codom cum']]]]; auto.
        specialize (H Γ0 ltac:(reflexivity) (Γ ,, vass na' dom') args' []).
        eapply (type_Cumul _ _ _ _ (tSort s)) in codom; cycle 1; eauto.
        { econstructor; pcuic. }
        { eapply ws_cumul_pb_Sort_inv in cum'.
          eapply cumul_Sort.  etransitivity; eauto. eapply leq_universe_product. }
        specialize (H _ codom).
        have eqctx : Σ ⊢ Γ ,, vass na ty = Γ ,, vass na' dom'.
        { constructor. apply ws_cumul_ctx_pb_refl. fvs. constructor; auto. }
        forward H.
        { constructor. eapply (isType_it_mkProd_or_LetIn_inv (Δ := [_])) in i.
          eapply isType_ws_cumul_ctx_pb; tea. pcuic.
          eapply isType_red in i0. 2:exact red.
          now eapply isType_tProd in i0 as [].
          eapply ws_cumul_pb_ws_cumul_ctx. now symmetry in eqctx. assumption. }
        destruct H. eapply a; tea.

      * simpl in sp. dependent elimination sp as [spcons isty isty' e tyhd sp].
        eapply ws_cumul_pb_Prod_Prod_inv in e as [eqna conv cum]; auto. cbn in *.
        eapply isType_tProd in isty as [].
        have tyt : Σ ;;; Γ |- hd0 : ty.
        { eapply (type_ws_cumul_pb _ (U:=ty)) in tyhd => //. now symmetry. }
        eapply (isType_subst (Δ := [_])) in i0; revgoals.
        { now eapply subslet_ass_tip. }
        eapply typing_spine_strengthen in sp; eauto.
        2:{ eapply (substitution0_ws_cumul_pb (t:=hd0)) in cum => //. }
        rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r in sp.
        specialize (H (subst_context [hd0] 0 Γ0) ltac:(now autorewrite with len)).
        rewrite subst_mkApps in sp. simpl in sp.
        specialize (H _ _ _ _ Ht sp).
        split.
        intros prs;eapply All_local_assum_app in prs as [prd prs].
        depelim prd.
        eapply (type_ws_cumul_pb (pb:=Conv) _ (U:=ty)) in tyhd.
        2:{ destruct s0 as [s' [Hs' _]]. exists s'; auto. }
        2:now symmetry.
        destruct H as [H _].
        forward H. {
          clear -wfΣ prs tyt.
          eapply All_local_assum_subst; eauto.
          simpl. intros.
          destruct X as [s [Ht2 isp]].
          exists s; pcuicfo auto.
          rewrite Nat.add_0_r. eapply (substitution (Γ' := [vass na ty]) (s:=[hd0]) (Δ := Γ1) (T := tSort s)); auto.
          now eapply subslet_ass_tip.
          now rewrite app_context_assoc in Ht2. }
        sq. constructor; auto.
        red. destruct s0 as [s' [Ht' sprop]].
        exists ty, s'. intuition auto.
        intros. now eapply H; tea.
Qed.

Lemma check_ind_sorts_is_propositional {cf:checker_flags} (Σ : global_env_ext) mdecl idecl ind
  (onib : on_ind_body cumulSpec0 (lift_typing typing) (Σ.1, ind_universes mdecl)
    (inductive_mind ind) mdecl (inductive_ind ind) idecl) :
  (ind_kelim idecl <> IntoPropSProp /\ ind_kelim idecl <> IntoSProp) ->
  is_propositional (ind_sort idecl) ->
  check_ind_sorts (lift_typing typing) (Σ.1, ind_universes mdecl)
    (PCUICEnvironment.ind_params mdecl) (PCUICEnvironment.ind_kelim idecl)
    (ind_indices idecl) (ind_cunivs onib) (ind_sort idecl) ->
  (#|ind_cunivs onib| <= 1) * All (fun cs => All is_propositional cs) (ind_cunivs onib).
Proof.
  intros kelim isp.
  unfold check_ind_sorts. simpl.
  destruct Universe.is_prop eqn:isp'.
  + induction (ind_cunivs onib); simpl; auto; try discriminate.
    destruct l; simpl. intros; split; eauto. constructor; [|constructor].
    destruct forallb eqn:fo. eapply forallb_All in fo.
    eapply All_impl; eauto; simpl.
    destruct (ind_kelim idecl); intuition cbn in H; try congruence.
    intros leb.
    destruct (ind_kelim idecl); simpl in *; intuition congruence.
  + destruct Universe.is_sprop eqn:issp.
    induction (ind_cunivs onib); simpl; auto; try discriminate.
    destruct (ind_kelim idecl); simpl in *; intuition congruence.
    unfold is_propositional in isp.
    now rewrite isp' issp in isp.
Qed.

Lemma sorts_local_ctx_All_local_assum_impl {cf:checker_flags} Σ
  (P : context -> context -> term -> Type) {Γ Δ cs} :
  (forall Γ' t s, In s cs -> Σ ;;; Γ ,,, Γ' |- t : tSort s  -> P Γ Γ' t) ->
  sorts_local_ctx (lift_typing typing) Σ Γ Δ cs ->
  All_local_assum (P Γ) Δ.
Proof.
  intros H.
  induction Δ in cs, H |- *; simpl; intros. constructor; intuition auto.
  destruct a as [na [b|] ty]; constructor; intuition auto.
  destruct cs => //; eauto.
  destruct cs => //; eauto. destruct X.
  eapply IHΔ. intros. apply (H Γ' t1 s0). right; eauto. all:auto.
  destruct cs => //. destruct X.
  eapply H. left; eauto. eauto.
Qed.

Lemma In_map {A B} (f : A -> B) (l : list A) x :
  In x (map f l) ->
  exists y, In y l /\ x = f y.
Proof.
  induction l; simpl; auto.
  intros [<-|inl].
  - eexists; intuition eauto.
  - destruct (IHl inl). exists x0; intuition eauto.
Qed.

(* We prove that if the (partial) constructor application's type lands in Prop
   then the inductive type is in Prop and hence the constructor's sort is
   Prop. Finally, all its arguments are in Prop because we additionally know
   that elimination to any type is allowed. *)

Lemma Is_proof_mkApps_tConstruct `{cf : checker_flags} (Σ : global_env_ext) Γ ind n u mdecl idecl args :
  check_univs ->
  wf_ext Σ ->
  declared_inductive (fst Σ) ind mdecl idecl ->
  (ind_kelim idecl <> IntoPropSProp /\ ind_kelim idecl <> IntoSProp) ->
  Is_proof Σ Γ (mkApps (tConstruct ind n u) args) ->
  #|ind_ctors idecl| <= 1 /\ ∥ All (Is_proof Σ Γ) (skipn (ind_npars mdecl) args) ∥.
Proof.
  intros checkunivs HΣ decli kelim [tyc [tycs [hc [hty hp]]]].
  assert (wfΣ : wf Σ) by apply HΣ.
  eapply inversion_mkApps in hc as [? [hc hsp]]; auto.
  eapply inversion_Construct in hc as [mdecl' [idecl' [cdecl' [wfΓ [declc [cu cum']]]]]]; auto.
  destruct (on_declared_constructor declc) as [[oi oib] [cs [Hnth onc]]].
  set (onib := declared_inductive_inv _ _ _ _) in *.
  clearbody onib. clear oib.
  eapply typing_spine_strengthen in hsp; eauto.
  pose proof (declared_inductive_inj decli (proj1 declc)) as [-> ->].
  assert (isType Σ Γ (type_of_constructor mdecl cdecl' (ind, n) u)).
  { eapply PCUICInductiveInversion.declared_constructor_valid_ty in declc; eauto. }
  move: X hsp.
  unfold type_of_constructor.
  rewrite (onc.(cstr_eq)).
  rewrite !subst_instance_it_mkProd_or_LetIn !subst_it_mkProd_or_LetIn.
  rewrite - {1}(firstn_skipn (ind_npars mdecl) args).
  rewrite !subst_instance_mkApps.
  simpl.
  autorewrite with len.
  rewrite !subst_mkApps.
  rewrite !subst_inds_concl_head.
  destruct decli. now apply nth_error_Some_length in H0.
  destruct (le_dec (ind_npars mdecl) #|args|).
  * intros X hsp.
    eapply PCUICSpine.typing_spine_inv in hsp as [parsub [sub sp]]; auto.
    2:{ rewrite context_assumptions_subst context_assumptions_subst_instance.
        rewrite firstn_length_le //. symmetry; eapply onNpars. eauto. }
    rewrite !subst_it_mkProd_or_LetIn in X, sp.
    rewrite !subst_mkApps in sp.
    simpl in sp.
    eapply typing_spine_proofs in sp; eauto.
    destruct sp.
    specialize (a _ _ declc cu) as [a a'].
    specialize (a hp).

    pose proof (onc.(on_cargs)).
    pose proof (onib.(ind_sorts)).
    assert (Universe.is_prop (ind_sort idecl) || Universe.is_sprop (ind_sort idecl)).
    { rewrite -(is_prop_subst_instance_univ u) -(is_sprop_subst_instance_univ u) => //. now subst tycs. }
    apply check_ind_sorts_is_propositional in X1 as [nctors X1]; eauto.
    assert(#|ind_cunivs onib| = #|ind_ctors idecl|).
    clear X. clear -onib. pose proof (onib.(onConstructors)).
    eapply All2_length in X. now rewrite X.
    rewrite H0 in nctors; split; auto.

    eapply nth_error_all in X1; eauto. simpl in X1.
    eapply sorts_local_ctx_instantiate in X0. 4:eapply cu.
    all: eauto.
    rewrite subst_instance_app in X0.
    eapply weaken_sorts_local_ctx in X0; eauto.
    eapply (subst_sorts_local_ctx _ _) in X0; eauto.
    3:{ eapply subslet_app.
      2:{ eapply weaken_subslet; auto. eapply PCUICArities.subslet_inds; eauto. }
      eapply sub. }
    2:{ eapply PCUICWeakeningTyp.weaken_wf_local; auto.
        edestruct (PCUICInductiveInversion.on_constructor_inst declc); eauto.
        destruct s0 as [inst [sp _]].
        rewrite !subst_instance_app in sp.
        now eapply wf_local_app_l in sp. }

    apply s.
    rewrite subst_app_context in X0.
    rewrite -(PCUICContextSubst.context_subst_length sub) in X0.
    autorewrite with len in X0.
    eapply (sorts_local_ctx_All_local_assum_impl Σ
      (fun Γ Γ' t =>
      ∑ s0 : Universe.t, Σ;;; Γ ,,, Γ' |- t : tSort s0 × is_propositional s0)).
    2:eauto.
    intros. exists s0. intuition auto.
    eapply In_map in H1 as [cs' [ins ->]].
    rewrite is_propositional_subst_instance.
    eapply All_In in X1; eauto.
    sq. apply X1.

  * intros _ sp.
    rewrite List.skipn_all2. lia.
    split; [|repeat constructor].
    pose proof (onc.(on_cargs)).
    pose proof (onib.(ind_sorts)).
    eapply check_ind_sorts_is_propositional in X0 as [nctors X1]; eauto.
    assert(#|ind_cunivs onib| = #|ind_ctors idecl|).
    clear -onib. pose proof (onib.(onConstructors)).
    eapply All2_length in X. now rewrite X. now rewrite -H.
    rewrite -it_mkProd_or_LetIn_app in sp.
    eapply typing_spine_proofs in sp; eauto.
    destruct sp as [_ sp].
    specialize (sp _ _ decli cu) as [a a'].
    specialize (a hp).
    subst tycs. rewrite -(is_propositional_subst_instance u) //.
  * now eapply declared_constructor_valid_ty.
Qed.

Lemma elim_restriction_works_kelim `{cf : checker_flags} (Σ : global_env_ext) ind mind idecl :
  check_univs ->
  wf_ext Σ ->
  declared_inductive (fst Σ) ind mind idecl ->
  (ind_kelim idecl <> IntoPropSProp /\ ind_kelim idecl <> IntoSProp) -> Informative Σ ind.
Proof.
  intros cu HΣ H indk.
  assert (wfΣ : wf Σ) by apply HΣ.
  destruct (on_declared_inductive H) as [[]]; eauto.
  intros ?. intros.
  eapply declared_inductive_inj in H as []; eauto; subst idecl0 mind.
  eapply Is_proof_mkApps_tConstruct in X1; tea.
  assert (wf Σ') by auto.
  now eapply weakening_env_declared_inductive; tc.
Qed.

Lemma elim_restriction_works `{cf : checker_flags} (Σ : global_env_ext) Γ T (ci : case_info) p c brs mind idecl :
  check_univs ->
  wf_ext Σ ->
  declared_inductive (fst Σ) ci mind idecl ->
  Σ ;;; Γ |- tCase ci p c brs : T ->
  (Is_proof Σ Γ (tCase ci p c brs) -> False) -> Informative Σ ci.(ci_ind).
Proof.
  intros cu wfΣ decli HT H.
  eapply elim_restriction_works_kelim1 in HT; eauto.
  eapply elim_restriction_works_kelim; eauto.
  destruct (ind_kelim idecl); intuition congruence.
Qed.

Lemma declared_projection_projs_nonempty `{cf : checker_flags} {Σ : global_env_ext} {p mdecl idecl cdecl pdecl} :
  wf Σ ->
  declared_projection Σ p mdecl idecl cdecl pdecl ->
  ind_projs idecl <> [].
Proof.
  intros. destruct H. destruct H0.
  destruct (ind_projs idecl); try congruence. destruct p.
  cbn in *. destruct proj_arg; inv H0.
Qed.

Lemma elim_restriction_works_proj_kelim1 `{cf : checker_flags} (Σ : global_env_ext) Γ T p c mind idecl :
  wf Σ ->
  declared_inductive (fst Σ) p.(proj_ind) mind idecl ->
  Σ ;;; Γ |- tProj p c : T ->
  (Is_proof Σ Γ (tProj p c) -> False) -> ind_kelim idecl = IntoAny.
Proof.
  intros X H X0 H0.
  eapply inversion_Proj in X0 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ?) ; auto.
  destruct (declared_inductive_inj H d.p1) as [-> ->].
  destruct x2. cbn in *.
  pose proof (declared_projection_projs_nonempty X d).
  pose proof (on_declared_projection d) as [_ onp].
  simpl in onp. subst.
  destruct ind_cunivs as [|? []]; try contradiction.
  1,3:now destruct onp as (((? & ?) & ?) & ?).
  destruct onp as (((? & ?) & ?) & ?). now inv o.
Qed.

Lemma elim_restriction_works_proj `{cf : checker_flags} (Σ : global_env_ext) Γ  p c mind idecl T :
  check_univs -> wf_ext Σ ->
  declared_inductive (fst Σ) p.(proj_ind) mind idecl ->
  Σ ;;; Γ |- tProj p c : T ->
  (Is_proof Σ Γ (tProj p c) -> False) -> Informative Σ p.(proj_ind).
Proof.
  intros cu; intros. eapply elim_restriction_works_kelim; eauto.
  eapply elim_restriction_works_proj_kelim1 in H0; eauto.
  intuition congruence.
Qed.

Section no_prop_leq_type.

Context `{cf : checker_flags}.
Variable Hcf : prop_sub_type = false.
Variable Hcf' : check_univs.

Lemma leq_term_prop_sorted_l {Σ Γ v v' u u'} :
  wf_ext Σ ->
  PCUICEquality.leq_term Σ (global_ext_constraints Σ) v v' ->
  Σ;;; Γ |- v : tSort u ->
  Σ;;; Γ |- v' : tSort u' -> Universe.is_prop u ->
  leq_universe (global_ext_constraints Σ) u' u.
Proof using Hcf Hcf'.
  intros wfΣ leq hv hv' isp.
  eapply typing_leq_term_prop in leq; eauto.
  apply leq_prop_prop; intuition auto.
  eapply cumul_prop_sym in leq.
  eapply cumul_prop_props in leq; eauto. auto. apply wfΣ.
Qed.

Lemma leq_term_prop_sorted_r {Σ Γ v v' u u'} :
  wf_ext Σ ->
  PCUICEquality.leq_term Σ (global_ext_constraints Σ) v v' ->
  Σ;;; Γ |- v : tSort u ->
  Σ;;; Γ |- v' : tSort u' -> Universe.is_prop u' ->
  leq_universe (global_ext_constraints Σ) u u'.
Proof using Hcf Hcf'.
  intros wfΣ leq hv hv' isp.
  eapply typing_leq_term_prop in leq; eauto.
  apply leq_prop_prop; intuition auto.
  apply cumul_prop_props in leq; auto. apply wfΣ.
Qed.

Lemma leq_term_sprop_sorted_l {Σ Γ v v' u u'} :
  wf_ext Σ ->
  PCUICEquality.leq_term Σ (global_ext_constraints Σ) v v' ->
  Σ;;; Γ |- v : tSort u ->
  Σ;;; Γ |- v' : tSort u' -> Universe.is_sprop u ->
  leq_universe (global_ext_constraints Σ) u' u.
Proof using Hcf Hcf'.
  intros wfΣ leq hv hv' isp.
  eapply typing_leq_term_prop in leq; eauto.
  apply leq_sprop_sprop; intuition auto.
  eapply cumul_prop_sym in leq.
  eapply cumul_sprop_props in leq; auto. eauto. auto. apply wfΣ.
Qed.

Lemma leq_term_propositional_sorted_l {Σ Γ v v' u u'} :
  wf_ext Σ ->
  PCUICEquality.leq_term Σ (global_ext_constraints Σ) v v' ->
  Σ;;; Γ |- v : tSort u ->
  Σ;;; Γ |- v' : tSort u' -> is_propositional u ->
  leq_universe (global_ext_constraints Σ) u' u.
Proof using Hcf Hcf'.
  intros wfΣ leq hv hv' isp.
  eapply orb_true_iff in isp as [isp | isp].
  - eapply leq_term_prop_sorted_l; eauto.
  - eapply leq_term_sprop_sorted_l; eauto.
Qed.

Lemma leq_term_sprop_sorted_r {Σ Γ v v' u u'} :
  wf_ext Σ ->
  PCUICEquality.leq_term Σ (global_ext_constraints Σ) v v' ->
  Σ;;; Γ |- v : tSort u ->
  Σ;;; Γ |- v' : tSort u' -> Universe.is_sprop u' ->
  leq_universe (global_ext_constraints Σ) u u'.
Proof using Hcf Hcf'.
  intros wfΣ leq hv hv' isp.
  eapply typing_leq_term_prop in leq; eauto.
  apply leq_sprop_sprop; intuition auto.
  apply cumul_sprop_props in leq; auto. apply wfΣ.
Qed.

Lemma cumul_prop_inv (Σ : global_env_ext) Γ A B u u' :
  wf_ext Σ ->
  Universe.is_prop u ->
  (((Σ ;;; Γ |- A : tSort u) * (Σ ;;; Γ |- B : tSort u')) +
   ((Σ ;;; Γ |- B : tSort u) * (Σ ;;; Γ |- A : tSort u')))%type ->
  Σ ;;; Γ |- A <= B ->
  ((Σ ;;; Γ |- A : tSort u) * (Σ ;;; Γ |- B : tSort u))%type.
Proof using Hcf Hcf'.
  intros wfΣ propu.
  intros [[HA HB]|[HB HA]] cum; split; auto;
  apply cumul_alt in cum as [v [v' [[redv redv'] leq]]].
  - eapply type_Cumul' with (tSort u'); eauto.
    eapply PCUICArities.isType_Sort.
    now eapply PCUICWfUniverses.typing_wf_universe in HA.
    pcuic. eapply cumul_Sort.
    eapply subject_reduction in redv; eauto.
    eapply subject_reduction in redv'; eauto.
    eapply leq_term_prop_sorted_l; eauto.
  - eapply subject_reduction in redv; eauto.
    eapply subject_reduction in redv'; eauto.
    eapply leq_term_prop_sorted_r in leq; eauto.
    eapply type_Cumul' with (tSort u'); eauto.
    eapply PCUICArities.isType_Sort.
    now eapply PCUICWfUniverses.typing_wf_universe in HB.
    pcuic. eapply cumul_Sort; auto.
Qed.

Lemma cumul_sprop_inv (Σ : global_env_ext) Γ A B u u' :
  wf_ext Σ ->
  Universe.is_sprop u ->
  (((Σ ;;; Γ |- A : tSort u) * (Σ ;;; Γ |- B : tSort u')) +
   ((Σ ;;; Γ |- B : tSort u) * (Σ ;;; Γ |- A : tSort u')))%type ->
  Σ ;;; Γ |- A <= B ->
  ((Σ ;;; Γ |- A : tSort u) * (Σ ;;; Γ |- B : tSort u))%type.
Proof using Hcf Hcf'.
  intros wfΣ propu.
  intros [[HA HB]|[HB HA]] cum; split; auto;
  apply cumul_alt in cum as [v [v' [[redv redv'] leq]]].
  - eapply type_Cumul' with (tSort u'); eauto.
    eapply isType_Sort.
    1: now destruct u.
    1: pcuic.
    eapply cumul_Sort.
    eapply subject_reduction in redv; eauto.
    eapply subject_reduction in redv'; eauto.
    eapply leq_term_sprop_sorted_l; eauto.
  - eapply subject_reduction in redv; eauto.
    eapply subject_reduction in redv'; eauto.
    eapply leq_term_sprop_sorted_r in leq; eauto.
    eapply type_Cumul' with (tSort u'); eauto.
    eapply PCUICArities.isType_Sort.
    1: now destruct u.
    1: now pcuic.
    now eapply cumul_Sort.
Qed.

Lemma unique_sorting_equality_prop_l {pb} {Σ : global_env_ext} {Γ T U s s'} :
  wf_ext Σ ->
  Σ ;;; Γ |- T : tSort s ->
  Σ ;;; Γ |- U : tSort s' ->
  Σ ;;; Γ ⊢ T ≤[pb] U ->
  Universe.is_prop s -> Universe.is_prop s'.
Proof using Hcf Hcf'.
  intros wfΣ HT HU cum isp.
  eapply PCUICSpine.ws_cumul_pb_le_le in cum.
  eapply ws_cumul_pb_alt_closed in cum as [v [v' [eqv]]].
  eapply subject_reduction_closed in HT; tea.
  eapply subject_reduction_closed in HU; tea.
  eapply leq_term_prop_sorted_l in c0; tea. all:eauto with pcuic.
  eapply leq_universe_prop_r; tea; eauto with pcuic.
Qed.

Lemma unique_sorting_equality_prop_r {pb} {Σ : global_env_ext} {Γ T U s s'} :
  wf_ext Σ ->
  Σ ;;; Γ |- T : tSort s ->
  Σ ;;; Γ |- U : tSort s' ->
  Σ ;;; Γ ⊢ T ≤[pb] U ->
  Universe.is_prop s' -> Universe.is_prop s.
Proof using Hcf Hcf'.
  intros wfΣ HT HU cum isp.
  eapply PCUICSpine.ws_cumul_pb_le_le in cum.
  eapply ws_cumul_pb_alt_closed in cum as [v [v' [eqv]]].
  eapply subject_reduction_closed in HT; tea.
  eapply subject_reduction_closed in HU; tea.
  eapply leq_term_prop_sorted_r in c0; tea. all:eauto with pcuic.
  eapply leq_universe_prop_r; tea; eauto with pcuic.
Qed.

Lemma unique_sorting_equality_prop {pb} {Σ : global_env_ext} {Γ T U s s'} :
  wf_ext Σ ->
  Σ ;;; Γ |- T : tSort s ->
  Σ ;;; Γ |- U : tSort s' ->
  Σ ;;; Γ ⊢ T ≤[pb] U ->
  Universe.is_prop s = Universe.is_prop s'.
Proof using Hcf Hcf'.
  intros wfΣ HT HU cum.
  apply iff_is_true_eq_bool.
  split.
  now eapply unique_sorting_equality_prop_l; tea.
  now eapply unique_sorting_equality_prop_r; tea.
Qed.

Lemma unique_sorting_equality_sprop_l {pb} {Σ : global_env_ext} {Γ T U s s'} :
  wf_ext Σ ->
  Σ ;;; Γ |- T : tSort s ->
  Σ ;;; Γ |- U : tSort s' ->
  Σ ;;; Γ ⊢ T ≤[pb] U ->
  Universe.is_sprop s -> Universe.is_sprop s'.
Proof using Hcf Hcf'.
  intros wfΣ HT HU cum isp.
  eapply PCUICSpine.ws_cumul_pb_le_le in cum.
  eapply ws_cumul_pb_alt_closed in cum as [v [v' [eqv]]].
  eapply subject_reduction_closed in HT; tea.
  eapply subject_reduction_closed in HU; tea.
  eapply leq_term_sprop_sorted_l in c0; tea. all:eauto with pcuic.
  eapply leq_universe_sprop_r; tea; eauto with pcuic.
Qed.

Lemma unique_sorting_equality_sprop_r {pb} {Σ : global_env_ext} {Γ T U s s'} :
  wf_ext Σ ->
  Σ ;;; Γ |- T : tSort s ->
  Σ ;;; Γ |- U : tSort s' ->
  Σ ;;; Γ ⊢ T ≤[pb] U ->
  Universe.is_sprop s' -> Universe.is_sprop s.
Proof using Hcf Hcf'.
  intros wfΣ HT HU cum isp.
  eapply PCUICSpine.ws_cumul_pb_le_le in cum.
  eapply ws_cumul_pb_alt_closed in cum as [v [v' [eqv]]].
  eapply subject_reduction_closed in HT; tea.
  eapply subject_reduction_closed in HU; tea.
  eapply leq_term_sprop_sorted_r in c0; tea. all:eauto with pcuic.
  eapply leq_universe_sprop_r; tea; eauto with pcuic.
Qed.

Lemma unique_sorting_equality_sprop {pb} {Σ : global_env_ext} {Γ T U s s'} :
  wf_ext Σ ->
  Σ ;;; Γ |- T : tSort s ->
  Σ ;;; Γ |- U : tSort s' ->
  Σ ;;; Γ ⊢ T ≤[pb] U ->
  Universe.is_sprop s = Universe.is_sprop s'.
Proof using Hcf Hcf'.
  intros wfΣ HT HU cum.
  apply iff_is_true_eq_bool.
  split.
  now eapply unique_sorting_equality_sprop_l; tea.
  now eapply unique_sorting_equality_sprop_r; tea.
Qed.

Lemma unique_sorting_equality_propositional {pb} {Σ : global_env_ext} {Γ T U s s'} :
  wf_ext Σ ->
  Σ ;;; Γ |- T : tSort s ->
  Σ ;;; Γ |- U : tSort s' ->
  Σ ;;; Γ ⊢ T ≤[pb] U ->
  is_propositional s = is_propositional s'.
Proof using Hcf Hcf'.
  intros wfΣ HT HU cum.
  unfold is_propositional.
  destruct (Universe.is_prop s) eqn:isp => /=. symmetry.
  - apply orb_true_intro; left.
    now rewrite (unique_sorting_equality_prop wfΣ HT HU cum) in isp.
  - destruct (Universe.is_sprop s) eqn:isp' => /=. symmetry.
    apply orb_true_intro; right.
    now rewrite (unique_sorting_equality_sprop wfΣ HT HU cum) in isp'.
    rewrite (unique_sorting_equality_prop wfΣ HT HU cum) in isp.
    rewrite (unique_sorting_equality_sprop wfΣ HT HU cum) in isp'.
    rewrite isp isp' //.
Qed.

Lemma cumul_prop1 (Σ : global_env_ext) Γ A B u :
  wf_ext Σ ->
  Universe.is_prop u ->
  isType Σ Γ A ->
  Σ ;;; Γ |- B : tSort u ->
  Σ ;;; Γ |- A <= B ->
  Σ ;;; Γ |- A : tSort u.
Proof using Hcf Hcf'.
  intros.
  destruct X0 as [s Hs].
  eapply cumul_prop_inv in H. 4:eauto. pcuicfo. auto.
  right; eauto.
Qed.

Lemma cumul_prop2 (Σ : global_env_ext) Γ A B u :
  wf_ext Σ ->
  Universe.is_prop u ->
  isType Σ Γ B ->
  Σ ;;; Γ |- A <= B ->
  Σ ;;; Γ |- A : tSort u ->
  Σ ;;; Γ |- B : tSort u.
Proof using Hcf Hcf'.
  intros.
  destruct X0 as [s Hs].
  eapply cumul_prop_inv in H. 4:eauto. pcuicfo. auto.
  left; eauto.
Qed.

Lemma cumul_sprop1 (Σ : global_env_ext) Γ A B u :
  wf_ext Σ ->
  Universe.is_sprop u ->
  isType Σ Γ A ->
  Σ ;;; Γ |- B : tSort u ->
  Σ ;;; Γ |- A <= B ->
  Σ ;;; Γ |- A : tSort u.
Proof using Hcf Hcf'.
  intros.
  destruct X0 as [s Hs].
  eapply cumul_sprop_inv in H. 4:eauto. pcuicfo. auto.
  right; eauto.
Qed.

Lemma cumul_sprop2 (Σ : global_env_ext) Γ A B u :
  wf_ext Σ ->
  Universe.is_sprop u ->
  isType Σ Γ B ->
  Σ ;;; Γ |- A <= B ->
  Σ ;;; Γ |- A : tSort u ->
  Σ ;;; Γ |- B : tSort u.
Proof using Hcf Hcf'.
  intros.
  destruct X0 as [s Hs].
  eapply cumul_sprop_inv in H. 4:eauto. pcuicfo. auto.
  left; eauto.
Qed.

End no_prop_leq_type.
