From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICRelevance
  PCUICClosedTyp PCUICGlobalEnv
  PCUICTyping PCUICInversion PCUICConversion PCUICCumulProp PCUICWeakeningTyp PCUICValidity PCUICWellScopedCumulativity 
  PCUICInductives PCUICInductiveInversion BDUnique.

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
    { apply PCUICAlpha.apply_predctx => //. eapply ctx_inst_impl with (1 := X5) => ??[] //. }
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
