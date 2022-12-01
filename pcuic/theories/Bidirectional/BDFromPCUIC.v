From Coq Require Import Bool List Arith Lia.
From MetaCoq.Template Require Import config utils monad_utils.
From MetaCoq.PCUIC Require Import PCUICGlobalEnv PCUICAst PCUICAstUtils PCUICInduction PCUICLiftSubst PCUICTyping PCUICEquality PCUICArities PCUICInversion PCUICInductives PCUICInductiveInversion PCUICReduction PCUICSubstitution PCUICConversion PCUICCumulativity PCUICWfUniverses PCUICValidity PCUICContextConversion PCUICSpine PCUICOnFreeVars PCUICWfUniverses PCUICClosed PCUICWellScopedCumulativity PCUICSR PCUICClosedTyp PCUICUnivSubstitutionConv PCUICWeakeningEnvTyp PCUICWeakeningEnv.
From MetaCoq.PCUIC Require Import BDTyping BDToPCUIC.

Require Import ssreflect.
From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

(** Preliminary lemmas missing from MetaCoq *)
Lemma is_allowed_elimination_monotone `{checker_flags} Σ s1 s2 allowed :
  leq_universe Σ s1 s2 -> is_allowed_elimination Σ allowed s2 -> is_allowed_elimination Σ allowed s1.
Proof.
  destruct allowed, s2; cbnr; trivial;
  destruct s1; cbnr; intros H1 H2; trivial; try now destruct H1.
  { now left. }
  destruct H2 as [|H2]; [now left|right].
  unfold_univ_rel.
  specialize (H1 v Hv); specialize (H2 v Hv).
  cbn in H2.
  lia.
Qed.

Lemma ctx_inst_length {ty Σ Γ args Δ} :
PCUICTyping.ctx_inst ty Σ Γ args Δ ->
#|args| = context_assumptions Δ.
Proof.
induction 1; simpl; auto.
rewrite /subst_telescope in IHX.
rewrite context_assumptions_mapi in IHX. congruence.
rewrite context_assumptions_mapi in IHX. congruence.
Qed.


Lemma ctx_inst_app_impl {P Q Σ Γ} {Δ : context} {Δ' args} (c : PCUICTyping.ctx_inst P Σ Γ args (Δ ++ Δ')) :
  (forall Γ' t T, P Σ Γ' t T -> Q Σ Γ' t T) ->
  PCUICTyping.ctx_inst Q Σ Γ (firstn (context_assumptions Δ) args) Δ.
Proof.
  revert args Δ' c.
  induction Δ using ctx_length_ind; intros.
  1: constructor.
  depelim c; simpl.
  - specialize (X (subst_telescope [i] 0 Γ0) ltac:(now rewrite /subst_telescope mapi_length)).
    rewrite subst_telescope_app in c.
    specialize (X _ _ c).
    rewrite context_assumptions_subst_telescope in X.
    constructor; auto.
  - specialize (X (subst_telescope [b] 0 Γ0) ltac:(now rewrite /subst_telescope mapi_length)).
    rewrite subst_telescope_app in c.
    specialize (X _ _ c).
    rewrite context_assumptions_subst_telescope in X.
    constructor; auto.
Qed.

(** Lemmas to get checking and constrained inference from inference + cumulativity. Relies on confluence + injectivity of type constructors *)

Lemma conv_check `{checker_flags} Σ (wfΣ : wf Σ) Γ t T :
  (∑ T' : term, Σ ;;; Γ |- t ▹ T' × Σ ;;; Γ ⊢ T' ≤ T) ->
  Σ ;;; Γ |- t ◃ T.
Proof.
  intros (?&?&?).
  econstructor ; tea.
  now apply ws_cumul_pb_forget_cumul.
Qed.

Lemma conv_infer_sort `{checker_flags} Σ (wfΣ : wf Σ) Γ t s :
  Σ ;;; Γ |- t : tSort s ->
  (∑ T' : term, Σ ;;; Γ |- t ▹ T' × Σ ;;; Γ ⊢ T' ≤ tSort s) ->
  {s' & Σ ;;; Γ |- t ▹□ s' × leq_universe Σ s' s}.
Proof.
  intros tyt (T'&?&Cumt).
  apply ws_cumul_pb_Sort_r_inv in Cumt as (?&?&?) ; auto.
  eexists.
  split ; tea.
  econstructor ; tea.
  now apply closed_red_red.
Qed.

Lemma conv_infer_prod `{checker_flags} Σ (wfΣ : wf Σ) Γ t na A B :
  Σ ;;; Γ |- t : tProd na A B ->
  (∑ T', (Σ ;;; Γ |- t ▹ T') × (Σ ;;; Γ ⊢ T' ≤ tProd na A B)) ->
  ∑ na' A' B', [× Σ ;;; Γ |- t ▹Π (na',A',B'),
    eq_binder_annot na na', Σ ;;; Γ ⊢ A' = A & Σ ;;; Γ ,, vass na A ⊢ B' ≤ B].
Proof.
  intros tyt (T'&?&Cumt).
  apply ws_cumul_pb_Prod_r_inv in Cumt as (?&?&?&[]) ; auto.
  do 3 eexists. split ; tea.
  econstructor ; tea.
  now apply closed_red_red.
Qed.

Lemma conv_infer_ind `{checker_flags} Σ (wfΣ : wf Σ) Γ t ind ui args :
  Σ ;;; Γ |- t : mkApps (tInd ind ui) args ->
  (∑ T', (Σ ;;; Γ |- t ▹ T') × (Σ ;;; Γ ⊢ T' ≤ mkApps (tInd ind ui) args)) ->
  ∑ ui' args', [× Σ ;;; Γ |- t ▹{ind} (ui',args'),
      R_global_instance Σ (eq_universe Σ) (leq_universe Σ) (IndRef ind) #|args| ui' ui
      & ws_cumul_pb_terms Σ Γ args' args].
Proof.
  intros tyt (T'&?&Cumt).
  apply ws_cumul_pb_Ind_r_inv in Cumt as (?&?&[]) ; auto.
  do 2 eexists. split ; tea.
  econstructor ; tea.
  now apply closed_red_red.
Qed.

Section BDFromPCUIC.


(** The big theorem*)
Lemma bidirectional_from_pcuic `{checker_flags} :
      env_prop (fun Σ Γ t T => {T' & Σ ;;; Γ |- t ▹ T' × Σ ;;; Γ ⊢ T' ≤ T})
        (fun Σ Γ => wf_local_bd Σ Γ).
Proof.
  apply typing_ind_env.

  all: intros Σ wfΣ Γ wfΓ.

  - intros bdwfΓ.
    induction bdwfΓ.
    all: constructor ; auto.
    + apply conv_infer_sort in Hs ; auto.
      2: by destruct tu.
      destruct Hs as (?&?&?).
      eexists.
      eassumption.
    + apply conv_check in Hc ; auto.
      apply conv_infer_sort in Hs ; auto.
      2: by destruct tu.
      destruct Hs as (?&?&?).
      1: eexists.
      all: eassumption.
    + by apply conv_check in Hc.

  - intros.
    eexists.
    split.
    2: by eapply typing_ws_cumul_pb ; tea ; constructor.
    constructor.
    eassumption.

  - intros.
    eexists.
    split.
    2: by eapply typing_ws_cumul_pb ; tea ; constructor.
    constructor.
    assumption.

  - intros n A B ? ? ? ? CumA ? CumB.
    apply conv_infer_sort in CumA ; auto.
    destruct CumA as (?&?&?).
    apply conv_infer_sort in CumB ; auto.
    destruct CumB as (?&?&?).
    eexists.
    split.
    + constructor ; eassumption.
    + constructor ; cbn ; auto.
      1: by apply wf_local_closed_context.
      constructor.
      apply leq_universe_product_mon.
      all: assumption.

  - intros n A t ? ? ? ? CumA ? (?&?&?).
    apply conv_infer_sort in CumA ; auto.
    destruct CumA as (?&?&?).
    eexists.
    split.
    + econstructor. all: eassumption.
    + apply ws_cumul_pb_Prod ; auto.
      eapply isType_ws_cumul_pb_refl.
      by eexists ; eauto.

  - intros n t A u ? ? ? ? CumA ? Cumt ? (?&?&?).
    apply conv_infer_sort in CumA ; auto.
    destruct CumA as (?&?&?).
    apply conv_check in Cumt ; auto.
    eexists.
    split.
    + econstructor.
      all: eassumption.
    + apply ws_cumul_pb_LetIn_bo.
      eassumption.

  - intros t na A B u ? ? ? ? ? Cumt ? (?&?&?).
    apply conv_infer_prod in Cumt ; auto.
    destruct Cumt as (?&?&?&[]).
    eexists.
    split.
    + econstructor ; eauto.
      econstructor ; eauto.
      apply ws_cumul_pb_forget_cumul.
      etransitivity ; tea.
      now apply ws_cumul_pb_eq_le.
    + now eapply substitution_ws_cumul_pb_vass.

  - intros.
    eexists.
    split.
    1: econstructor ; tea.
    apply ws_cumul_pb_refl.
    1: fvs.
    rewrite on_free_vars_subst_instance.
    now eapply closed_on_free_vars, declared_constant_closed_type.

  - intros.
    eexists.
    split.
    1: econstructor ; tea.
    apply ws_cumul_pb_refl.
    1: fvs.
    rewrite on_free_vars_subst_instance.
    now eapply closed_on_free_vars, declared_inductive_closed_type.

  - intros.
    eexists.
    split.
    1: econstructor ; tea.
    apply ws_cumul_pb_refl.
    1: fvs.
    now eapply closed_on_free_vars, declared_constructor_closed_type.

  - intros ci p c brs indices ps mdecl idecl isdecl wfΣ' wfbΓ epar ? predctx wfpred ? ? ty_p Cump ? ? Hinst ty_c Cumc ? ? ? ty_br.

    apply conv_infer_sort in Cump as (?&?&?) ; auto.
    apply conv_infer_ind in Cumc as (?&?&[]) ; auto.
    eexists.
    split.
    + econstructor.
      all: tea.
      * by eapply All_local_app_rel.
      * eapply is_allowed_elimination_monotone.
        all: eassumption.
      * rewrite subst_instance_app_ctx rev_app_distr in Hinst.
        replace (pparams p) with (firstn (context_assumptions (List.rev (subst_instance (puinst p)(ind_params mdecl)))) (pparams p ++ indices)).
        eapply ctx_inst_app_impl ; tea.
        1: intros ??? [] ; by apply conv_check.
        rewrite context_assumptions_rev context_assumptions_subst_instance.
        erewrite PCUICGlobalMaps.onNpars.
        2: eapply on_declared_minductive ; eauto.
        rewrite firstn_app_left //.
        now destruct wfpred.

      * replace #|x1| with #|pparams p ++ indices|.
        1: assumption.
        symmetry.
        eapply All2_length.
        eassumption.
      * move: (a) => /All2_length alen.
        rewrite -(firstn_skipn (ci_npar ci) x1) in a.
        eapply All2_app_inv in a as [].
        1: now eapply All2_impl ; tea ; intros ; eapply ws_cumul_pb_forget_conv.
        rewrite -epar ; destruct wfpred as [->].
        apply ctx_inst_length in Hinst; tea.
        move: alen.
        rewrite Hinst context_assumptions_rev context_assumptions_subst_instance
          context_assumptions_app -(declared_minductive_ind_npars isdecl) => alen.
        rewrite firstn_length_le.
        all: lia.

      * eapply All2i_impl.
        1: eassumption.
        intros j cdecl br (?&Hbr).
        split ; [assumption|..].
        intros brctxty.
        fold predctx in brctxty.
        fold ptm in brctxty.
        fold brctxty in Hbr.
        destruct Hbr as (?&(?&Cumbody)&?&?&?).
        apply conv_check in Cumbody ; auto.
        split ; auto.
        by apply All_local_app_rel.

    + apply ws_cumul_pb_mkApps ; auto.
      * apply ws_cumul_pb_it_mkLambda_or_LetIn.
        -- apply ws_cumul_ctx_pb_refl.
           unfold predctx.
           eapply wf_local_closed_context, wf_case_predicate_context ; eauto.
           eapply validity ; eassumption.
        -- apply ws_cumul_pb_refl.
           1: eapply wf_local_closed_context, wf_case_predicate_context ; eauto.
           1: eapply validity ; eassumption.
           eapply subject_is_open_term ; tea.
      * apply All2_app.
        -- replace indices with (skipn (ci_npar ci) (pparams p ++ indices)).
           2: by apply skipn_all_app_eq ; rewrite <- epar ; destruct wfpred as [->].
           by apply All2_skipn.
        -- constructor ; auto.
           eapply ws_cumul_pb_refl.
           1: apply wf_local_closed_context ; tea.
           eapply subject_is_open_term ; tea.

  - intros ? c u mdecl idecl cdecl pdecl isdecl args ? ? ? Cumc ?.
    apply conv_infer_ind in Cumc as (ui'&args'&[]) ; auto.
    eexists.
    split.
    + econstructor.
      1-2: eassumption.
      etransitivity.
      2: eassumption.
      eapply All2_length.
      eassumption.

    + assert (Σ ;;; Γ |- c : mkApps (tInd p.(proj_ind) ui') args')
        by (apply infering_ind_typing in i ; auto).
      assert (consistent_instance_ext Σ (ind_universes mdecl) u).
        { destruct isdecl.
          apply validity in X1 as [].
          eapply invert_type_mkApps_ind ; eauto.
          apply H1.p1.
        }
      assert (consistent_instance_ext Σ (ind_universes mdecl) ui').
        { destruct isdecl.
          apply validity in X2 as [] ; auto.
          eapply invert_type_mkApps_ind ; eauto.
          eapply H2.p1.
        }
      unshelve epose proof (wf_projection_context _ _ _ _) ; eauto.
      change Γ with (Γ,,, subst_context (c :: List.rev args') 0 []).
      change 0 with #|[] : context| at 2 3.
      eapply PCUICConversion.substitution_ws_cumul_pb_subst_conv.
      * eapply subslet_untyped_subslet, projection_subslet.
        4: eapply validity.
        all: eassumption.
      * eapply subslet_untyped_subslet, projection_subslet.
        4: eapply validity.
        all: eassumption.
      * constructor.
        2: by apply All2_rev.
        eapply ws_cumul_pb_refl ;
          [apply wf_local_closed_context |eapply subject_is_open_term] ; tea.
      * apply wf_local_closed_context.
        apply PCUICWeakeningTyp.weaken_wf_local ; auto.
        eapply wf_projection_context ; eauto.
      * cbn -[projection_context].
        apply weaken_ws_cumul_pb ; auto.
        1: apply wf_local_closed_context ; auto.
        eapply projection_cumulative_indices ; eauto.
        2: now easy.
        eapply (weaken_lookup_on_global_env' _ _ (InductiveDecl _)); eauto.
        apply isdecl.

  - intros mfix n decl types ? ? ? Alltypes Allbodies.
    eexists.
    split.
    2:{
      apply isType_ws_cumul_pb_refl.
      eapply nth_error_all in Alltypes as [? []] ; tea.
      eexists ; tea.
    }
    constructor ; eauto.
    + apply (All_impl Alltypes).
      intros ? [? [? s]].
      apply conv_infer_sort in s as [? []] ; auto.
      eexists ; eauto.
    + apply (All_impl Allbodies).
      intros ? [? s].
      by apply conv_check in s ; auto.

  - intros mfix n decl types ? ? ? Alltypes Allbodies.
    eexists.
    split.
    2:{
      apply isType_ws_cumul_pb_refl.
      eapply nth_error_all in Alltypes as [? []] ; tea.
      eexists ; tea.
    }
    constructor ; eauto.
    + apply (All_impl Alltypes).
      intros ? [? [? s]].
      apply conv_infer_sort in s as [? []] ; auto.
      eexists ; eauto.
    + apply (All_impl Allbodies).
      intros ? [? s].
      by apply conv_check in s ; auto.

  - intros p prim_ty cdecl wfΓ' hp hdecl pinv.
    eexists. split; [econstructor; tea|].
    eapply ws_cumul_pb_refl; fvs.

  - intros ? ? ? ? ? ? (?&?&?) ? (?&?&?) ?.
    eexists.
    split.
    1: eassumption.
    etransitivity ; eauto.
    now eapply cumulSpec_typed_cumulAlgo.
Qed.

End BDFromPCUIC.

(** The direct consequence on typing *)
Lemma typing_infering `{checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ t T} :
  Σ ;;; Γ |- t : T -> ∑ T', Σ ;;; Γ |- t ▹ T' × Σ ;;; Γ ⊢ T' ≤ T.
Proof.
  intros.
  apply bidirectional_from_pcuic.
  all: assumption.
Qed.

Lemma typing_checking `{checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ t T} :
  Σ ;;; Γ |- t : T -> Σ ;;; Γ |- t ◃ T.
Proof.
  move => /typing_infering [T' [? ?]].
  econstructor ; tea.
  now apply ws_cumul_pb_forget_cumul.
Qed.

Lemma typing_infering_sort `{checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ t u} :
  Σ ;;; Γ |- t : tSort u -> ∑ u', Σ ;;; Γ |- t ▹□ u' × leq_universe Σ u' u.
Proof.
  intros.
  apply conv_infer_sort ; tea.
  now apply typing_infering.
Qed.

Lemma isType_infering_sort `{checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ t} :
  isType Σ Γ t -> ∑ u', Σ ;;; Γ |- t ▹□ u'.
Proof.
  intros [? ty].
  eapply typing_infering_sort in ty as [? []]; tea.
  now eexists.
Qed.

Lemma typing_infer_prod `{checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ t na A B} :
  Σ ;;; Γ |- t : tProd na A B ->
  ∑ na' A' B', [× Σ ;;; Γ |- t ▹Π (na',A',B'),
    eq_binder_annot na na', Σ ;;; Γ ⊢ A' = A & Σ ;;; Γ ,, vass na A ⊢ B' ≤ B].
Proof.
  intros.
  apply conv_infer_prod ; tea.
  now apply typing_infering.
Qed.

Lemma typing_infer_ind `{checker_flags} Σ (wfΣ : wf Σ) Γ t ind ui args :
  Σ ;;; Γ |- t : mkApps (tInd ind ui) args ->
  ∑ ui' args', [× Σ ;;; Γ |- t ▹{ind} (ui',args'),
      R_global_instance Σ (eq_universe Σ) (leq_universe Σ) (IndRef ind) #|args| ui' ui
      & ws_cumul_pb_terms Σ Γ args' args].
Proof.
  intros.
  apply conv_infer_ind ; tea.
  now apply typing_infering.
Qed.

Lemma wf_local_wf_local_bd `{checker_flags} {Σ} (wfΣ : wf Σ) {Γ} :
  wf_local Σ Γ ->
  wf_local_bd Σ Γ.
Proof.
  intros.
  eapply bidirectional_from_pcuic ; tea.
  now eapply type_Prop_wf.
Qed.

Lemma wf_local_rel_wf_local_bd `{checker_flags} {Σ} (wfΣ : wf Σ) {Γ Γ'} :
  wf_local_rel Σ Γ Γ' ->
  wf_local_bd_rel Σ Γ Γ'.
Proof.
  intros wfΓ'.
  induction Γ' as [|[? [] ?]] in wfΓ' |- *.
  all: constructor ; inversion wfΓ' ; subst ; cbn in *.
  1,4: now apply IHΓ'.
  - now apply isType_infering_sort.
  - now apply typing_checking.
  - now apply isType_infering_sort.
Qed.

Theorem ctx_inst_typing_bd `{checker_flags} (Σ : global_env_ext) Γ l Δ (wfΣ : wf Σ) :
  PCUICTyping.ctx_inst typing Σ Γ l Δ ->
  PCUICTyping.ctx_inst checking Σ Γ l Δ.
Proof.
  intros inl.
  induction inl.
  all: constructor ; tea.
  now apply typing_checking.
Qed.
