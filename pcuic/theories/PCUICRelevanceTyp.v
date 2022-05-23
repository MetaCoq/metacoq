From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICRelevance
  PCUICClosedTyp PCUICGlobalEnv
  PCUICTyping PCUICInversion PCUICConversion PCUICCumulProp PCUICWeakeningTyp PCUICValidity PCUICWellScopedCumulativity BDUnique.

Require Import ssreflect.

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
  (* epose proof (nth_error_arities_context mdecl (#|ind_bodies mdecl| - S cstr.1.(inductive_ind)) idecl _).
  Unshelve. 2: { rewrite nth_error_rev. len. apply nth_error_Some_length in di. lia. rewrite List.rev_involutive. replace _ with (inductive_ind cstr.1); tea. len. apply nth_error_Some_length in di. lia. }
  rewrite e1 in H; clear e1. *)
  admit.
Admitted.

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

Lemma isType_of_projection {cf : checker_flags} Σ mdecl idecl cdecl pdecl p c args u Γ :
  wf Σ.1 -> declared_projection Σ.1 p mdecl idecl cdecl pdecl ->
  Σ;;; Γ |- c : mkApps (tInd (proj_ind p) u) args -> #|args| = ind_npars mdecl ->
  isTypeRel Σ Γ (subst0 (c :: List.rev args) (proj_type pdecl)@[u]) pdecl.(proj_relevance).
Proof.
  admit.
Admitted.

Lemma apply_predctx {cf : checker_flags} Σ Γ ci p indices c ps mdecl idecl {wfΣ : wf Σ.1} :
  wf_predicate mdecl idecl p ->
  All2 (PCUICEquality.compare_decls eq eq) (pcontext p) (ind_predicate_context ci mdecl idecl) ->
  ctx_inst (typing Σ) Γ (pparams p ++ indices) (List.rev (ind_params mdecl,,, ind_indices idecl)@[puinst p]) ->
  Σ;;; Γ |- c : mkApps (tInd ci (puinst p)) (pparams p ++ indices) ->
  let predctx := case_predicate_context ci mdecl idecl p in
  let ptm := it_mkLambda_or_LetIn predctx (preturn p) in
  Σ;;; Γ,,, predctx |- preturn p : tSort ps -> Σ ;;; Γ |- mkApps ptm (indices ++ [c]) : tSort ps.
Proof.
  admit.
Admitted.


Lemma relevance_term_to_type {cf : checker_flags} :
  env_prop relevance_from_term_from_type
    (fun Σ Γ => All_local_env (lift_typing relevance_from_term_from_type Σ) Γ).
Proof using Type.
  apply typing_ind_env; intros Σ wfΣ Γ wfΓ; intros **; rename_all_hyps; auto.
  - eapply All_local_env_impl.
    eapply All_local_env_over_2; tea.
    intros ??? H; apply lift_typing_impl with (1 := H); now intros ? [].
  - split; intro H.
    + rewrite /relevance_of_term nth_error_map heq_nth_error /option_map /option_default /id in H.
      rewrite -H.
      destruct (PCUICTyping.nth_error_All_local_env heq_nth_error wfΓ); eauto.
      apply isTypeRelOpt_lift => //.
      pose proof (nth_error_Some_length heq_nth_error); lia.
    + rewrite /relevance_of_term nth_error_map heq_nth_error /option_map /option_default /id.
      pose proof (PCUICTyping.nth_error_All_local_env heq_nth_error wfΓ).1; eauto.
      apply isTypeRelOpt_lift in X0 => //. 2: { pose proof (nth_error_Some_length heq_nth_error); lia. }
      eapply isTypeRel2_relevance; tea.
  - split; unfold relevance_of_term; intro Hr => //.
    + eexists; split.
      2: { constructor; tea. eauto with pcuic. }
      destruct u => //.
    + destruct Hr as (s & <- & Hty) => //.
      apply inversion_Sort in Hty as (_ & _ & le) => //.
      eapply ws_cumul_pb_Sort_inv, leq_relevance in le => //.
      destruct u => //.
  - split; unfold relevance_of_term; intro Hr => //.
    + rewrite -Hr.
      eexists; split.
      2: { constructor; tea. eauto with pcuic. }
      destruct s2, s1 => //.
    + destruct Hr as (s & <- & Hty) => //.
      apply inversion_Sort in Hty as (_ & _ & le) => //.
      eapply ws_cumul_pb_Sort_inv, leq_relevance in le => //.
      destruct s2, s1 => //.
  - split; intro Hr => //.
    + eapply X3 in Hr as (s & e & Hs).
      eexists; split.
      2: { constructor; tea. }
      destruct s, s1 => //.
    + destruct Hr as (s & <- & Hs).
      edestruct X3 as (_ & IH); eapply IH.
      apply inversion_Prod in Hs as (s1' & s2 & e1 & _ & Hty & le) => //.
      eexists; split; tea.
      eapply ws_cumul_pb_Sort_inv, leq_relevance in le => //.
      destruct s1', s2 => //.
  - split; intro Hr => //.
    + eapply X5 in Hr as (s & e & Hs).
      exists s; split => //.
      econstructor; tea.
      eapply type_LetIn; eauto. constructor; eauto with pcuic. do 2 constructor. apply cumul_zeta.
    + destruct Hr as (s & <- & Hs).
      edestruct X5 as (_ & IH); eapply IH.
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
    + eapply X3 in Hr as (s' & e & Hs).
      assert (wf_universe Σ s') by auto with pcuic.
      apply inversion_Prod in Hs as (? & ss & ? & ? & ? & le); tea.
      exists s'; split => //.
      econstructor; tea. instantiate (1 := tSort ss). 2: constructor; eauto with pcuic.
      2: { apply cumul_Sort. apply ws_cumul_pb_Sort_inv in le. etransitivity. apply leq_universe_product. tea. }
      change (tSort ss) with ((tSort ss) { 0 := u }).
      eapply PCUICSubstitution.substitution0; tea.
    + destruct Hr as (s' & <- & Hs).
      edestruct X3 as (_ & IH); eapply IH; clear IH.
      assert (wf_universe Σ s') by eauto with pcuic.
      exists s; split => //.
      apply inversion_Prod in IHB as (s1 & s2 & ? & ? & Hty & le) => //.
      eapply (PCUICSubstitution.substitution0 Hty) in typeu; tea. cbn in typeu.
      transitivity (relevance_of_sort s2).
      2: eapply cumul_sort_relevance; tea.
      apply ws_cumul_pb_Sort_inv in le; destruct s2, s1, s => //.
  - apply PCUICWeakeningEnvTyp.on_declared_constant in H as H'; tea. unfold on_constant_decl in H'.
    split; intro Hr => //.
    + unfold relevance_of_term, relevance_of_constant in Hr.
      rewrite (declared_constant_lookup H) in Hr; rewrite -Hr.
      destruct H' as (H' & _).
      eapply infer_typing_sort_impl with _ H' => //; [apply relevance_subst_opt|]. intro Hty.
      apply (weaken_ctx (Γ := [])); tea.
      destruct Σ as (Σ & φ); unfold fst in *.
      instantiate (1 := u).
      eapply (PCUICUnivSubstitutionTyp.typing_subst_instance' _ _ [] _ (tSort H'.π1) u _); tea.
      unshelve epose proof (PCUICWeakeningEnv.weaken_lookup_on_global_env' _ _ (ConstantDecl decl) wf _); eauto.
      now split.
    + unfold relevance_of_term, relevance_of_constant.
      rewrite (declared_constant_lookup H).
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
    + unfold relevance_of_term in Hr; subst rel.
      eapply infer_typing_sort_impl with _ X1; [apply relevance_subst_opt|]; intros Hty.
      eapply PCUICUnivSubstitutionTyp.typing_subst_instance' in Hty.
      eapply (weaken_ctx (Γ := [])) in Hty.
      apply Hty.
      all: tea.
      unshelve epose proof (PCUICWeakeningEnv.weaken_lookup_on_global_env' _ _ (InductiveDecl mdecl) wf isdecl.p1); eauto. now split.
    + unfold relevance_of_term.
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
    + unfold relevance_of_term, relevance_of_constructor in Hr; subst rel.
      destruct Σ as (Σ & φ); unfold fst, snd in *.
      rewrite H.
      apply isType_of_constructor; tea.
    + unfold relevance_of_term, relevance_of_constructor. destruct Σ as (Σ & φ); unfold fst, snd in *.
      rewrite H.
      eassert (isTypeRel (Σ, φ) _ (type_of_constructor mdecl cdecl (ind, i) u) (idecl.(ind_relevance))) by (apply isType_of_constructor; tea).
      eapply isTypeRel2_relevance; tea. apply wf.
  - assert (Σ ;;; Γ |- mkApps ptm (indices ++ [c]) : tSort ps). 
    { apply apply_predctx => //. apply ctx_inst_impl with (1 := X5) => ??[] //. }
    split; intro Hr => //.
    + unfold relevance_of_term in Hr; subst rel.
      exists ps; split => //.
    + unfold relevance_of_term.
      eapply isTypeRel2_relevance; tea.
      exists ps; split => //.
  - pose proof (declared_projection_lookup isdecl).
    assert (isTypeRel Σ Γ (subst0 (c :: List.rev args) (proj_type pdecl)@[u]) (pdecl.(proj_relevance))) by (eapply isType_of_projection; tea).
    split; intro Hr => //.
    + unfold relevance_of_term, relevance_of_projection in Hr; subst rel.
      now rewrite H.
    + unfold relevance_of_term, relevance_of_projection.
      rewrite H.
      eapply isTypeRel2_relevance; tea.
  - eapply All_nth_error in X0, X1; tea.
    rewrite /on_def_type /on_def_body /lift_typing2 in X0, X1.
    split; intro Hr => //.
    + rewrite /relevance_of_term heq_nth_error /option_default in Hr; subst rel.
      apply lift_typing_impl with (1 := X0); now intros ? [].
    + rewrite /relevance_of_term heq_nth_error /option_default.
      eapply isTypeRel2_relevance; tea.
      apply infer_typing_sort_impl with id X0 => //.
      now intros [].
  - eapply All_nth_error in X0, X1; tea.
    rewrite /on_def_type /on_def_body /lift_typing2 in X0, X1.
    split; intro Hr => //.
    + rewrite /relevance_of_term heq_nth_error /option_default in Hr; subst rel.
      apply lift_typing_impl with (1 := X0); now intros ? [].
    + rewrite /relevance_of_term heq_nth_error /option_default.
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
