(* Distributed under the terms of the MIT license. *)
From Coq Require Import Morphisms.
From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import config.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTactics PCUICCases PCUICInduction
  PCUICLiftSubst PCUICUnivSubst
  PCUICTyping PCUICReduction PCUICCumulativity
  PCUICEquality PCUICGlobalEnv PCUICClosed PCUICClosedConv PCUICClosedTyp PCUICEquality PCUICWeakeningEnvConv PCUICWeakeningEnvTyp
  PCUICSigmaCalculus PCUICRenameDef PCUICRenameConv PCUICWeakeningConv PCUICWeakeningTyp PCUICInstDef PCUICInstConv
  PCUICGuardCondition PCUICUnivSubstitutionConv PCUICOnFreeVars PCUICOnFreeVarsConv PCUICClosedTyp PCUICClosedTyp.

Require Import ssreflect ssrbool.
From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.
Set Equations With UIP.
Set Keyed Unification.
Set Default Goal Selector "!".
Implicit Types cf : checker_flags.

(** * Type preservation for σ-calculus instantiation *)

Open Scope sigma_scope.

Definition well_subst_usubst {cf} (Σ:global_env_ext) (wfΣ : wf Σ) Γ σ Δ :
  is_closed_context Δ ->
  Σ ;;; Δ ⊢ σ : Γ ->
  usubst Γ σ Δ.
Proof.
  intuition eauto with *.
Defined.

Definition well_subst_closed_subst {cf} (Σ:global_env_ext) (wfΣ : wf Σ) Γ σ Δ :
  is_closed_context Δ ->
  Σ ;;; Δ ⊢ σ : Γ ->
  closed_subst Γ σ Δ.
Proof.
  intros hΔ [typed_σ hσ]. repeat split; tea.
  intros x decl hnth. specialize (typed_σ x decl hnth) as htype.
  pose proof (typing_wf_local htype). pose (wf_local_closed_context X).
  apply closedn_on_free_vars. eapply subject_closed; eauto.
Defined.

Lemma inst_context_on_free_vars σ n l  :
on_free_vars_ctx (closedP n xpredT) l ->
inst_context (⇑^n σ) l = l.
Proof.
  intro Hclosed.
  unfold on_free_vars_ctx in Hclosed.
  unfold inst_context, fold_context_k.
  induction l; eauto.
  cbn in *. rewrite alli_app in Hclosed. toProp Hclosed.
  destruct Hclosed as [H Hclosed].
  rewrite mapi_rec_app. rewrite List.distr_rev.
  rewrite IHl; eauto.
  cbn in *. f_equal.
  toProp Hclosed. replace (#|List.rev l| + 0) with (#|List.rev l|) in * by lia.
  destruct Hclosed as [Hclosed _].
  destruct a; unfold map_decl; cbn.
  unfold on_free_vars_decl in Hclosed.
  unfold test_decl in Hclosed.
  toProp Hclosed. cbn in Hclosed.
  destruct Hclosed as [Hbody Htype].
  f_equal.
  - destruct decl_body; eauto; cbn in *.
    f_equal. rewrite closedP_shiftnP in Hbody.
    rewrite <- Upn_Upn.
    rewrite shiftnP_add in Hbody.
    apply inst_on_free_vars; eauto.
  - rewrite closedP_shiftnP in Htype.
    rewrite shiftnP_add in Htype. rewrite <- Upn_Upn.
    apply inst_on_free_vars; eauto.
Defined.

Lemma inst_case_predicate_context_inst σ p :
  on_free_vars_ctx (closedP #|pparams p| xpredT) (pcontext p) ->
  PCUICCases.inst_case_predicate_context (inst_predicate σ p) =
  inst_context σ (PCUICCases.inst_case_predicate_context p).
Proof.
  intro Hclosed. unfold PCUICCases.inst_case_predicate_context.
  unfold pparams at 1. cbn.
  replace (pcontext p) with
  (inst_context (⇑^#|pparams p| σ) (pcontext p)) at 1.
  - rewrite <- inst_inst_case_context; eauto.
  - apply inst_context_on_free_vars; eauto.
Defined.

Lemma inst_case_branch_context_inst σ p x :
on_free_vars_ctx (closedP #|pparams p| xpredT) (bcontext x) ->
inst_case_branch_context (inst_predicate σ p)
     (inst_branch σ x) =
     inst_context σ (inst_case_branch_context p x).
Proof.
  intro Hclosed. unfold inst_case_branch_context. cbn.
  replace (bcontext x) with
  (inst_context (⇑^#|pparams p| σ) (bcontext x)) at 1.
  - rewrite <- inst_inst_case_context; eauto.
  - apply inst_context_on_free_vars; eauto.
Defined.

Lemma inst_cumulSpec {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {pb Γ Δ σ A B} :
  closed_subst Γ σ Δ ->
  is_closed_context Γ ->
  is_open_term Γ A ->
  is_open_term Γ B ->
  Σ ;;; Γ ⊢ A ≤s[pb] B ->
  Σ ;;; Δ ⊢ A.[σ] ≤s[pb] B.[σ].
Proof.
  intros hσ HΓ HfreeA HfreeB e.
  revert pb Γ A B e Δ σ hσ HΓ HfreeA HfreeB e.
  induction 1; intros.
  all: repeat inv_on_free_vars.
  all: lazymatch goal with
       | [ H : cumul_predicate_dep _ _ _ |- _ ] => apply cumul_predicate_undep in H
       | _ => idtac
       end.
  all: repeat match goal with
         | [ H : All2_dep _ _ |- _ ] => apply All2_undep in H
         end.
  - rewrite subst10_inst. sigma. solve [econstructor].
  - rewrite subst10_inst. sigma. solve [econstructor].
  - destruct (nth_error Γ i) eqn:hnth; noconf pf.
    red in hσ. destruct hσ as [_ [_ hσ]]. specialize (hσ _ _ hnth) as IH.
    specialize IH with (1:=H) as [[x' [decl' [hi [hnth' eqbod]]]]|eqr].
    * rewrite /= hi. sigma.
      destruct (decl_body decl') eqn:hdecl => //. noconf eqbod.
      let H1 := match goal with H : rename _ _ = _ |- _ => H end in
      rewrite -H1. sigma.
      relativize (t.[_]); [eapply cumul_rel|].
      { now rewrite hnth' /= hdecl. }
      rewrite lift0_inst. now sigma.
    * rewrite /= eqr. sigma. reflexivity.
  - cbn. rewrite inst_mkApps. simpl.
    rewrite inst_iota_red //.
    * rewrite skipn_length; lia.
    * change (bcontext br) with (bcontext (inst_branch σ br)).
      rewrite closedn_ctx_on_free_vars.
      eapply nth_error_forallb in p4; tea. simpl in p4.
      move/andP: p4 => [] clbctx clbod.
      now rewrite test_context_k_closed_on_free_vars_ctx in clbctx.
    * eapply cumul_iota.
      + rewrite nth_error_map Hbrs /= //.
      + simpl. now len.
    - rewrite 2!inst_mkApps. simpl.
      eapply cumul_fix.
      + eapply inst_unfold_fix. eassumption.
      + eapply is_constructor_inst. assumption.
    - simpl. rewrite !inst_mkApps. simpl.
      eapply cumul_cofix_case.
      eapply inst_unfold_cofix. eassumption.
    - simpl. rewrite 2!inst_mkApps. simpl.
      eapply cumul_cofix_proj.
      eapply inst_unfold_cofix. eassumption.
    - simpl.
      rewrite inst_closed0.
      * rewrite closedn_subst_instance.
        eapply declared_constant_closed_body. all: eauto.
      * eapply cumul_delta; eauto.
    - simpl. rewrite inst_mkApps. simpl.
      eapply cumul_proj; rewrite nth_error_map. rewrite Hargs. reflexivity.
    - pose proof hσ.1.
      eapply cumul_Trans; try eapply X0; try eapply X2; eauto.
      eapply inst_is_open_term; eauto.
    - eapply cumul_Sym; try eapply X0; eauto.
    - eapply cumul_Refl; eauto.
  - cbn. eapply cumul_Evar. cbn in *.
    repeat toAll. eapply All2_impl. 1:tea. cbn; intros.
    eapply X0.1.2; intuition.
  - eapply cumul_App; try apply IHe1; try apply IHe2; eauto.
  - pose proof hσ.1. cbn; eapply cumul_Lambda; try apply IHe1; try apply IHe2; eauto;
    try rewrite shiftnP_S; eauto.
    * eapply closed_subst_up_vass; eauto. eapply inst_is_open_term; eauto.
    * rewrite on_free_vars_ctx_snoc. apply andb_and; split; eauto.
  - eapply cumul_Prod; try apply IHe1; try apply IHe2; eauto;
    try rewrite shiftnP_S; eauto.
    * eapply closed_subst_up_vass; eauto. eapply inst_is_open_term; eauto.
    * rewrite on_free_vars_ctx_snoc. apply andb_and; split; eauto.
  - eapply cumul_LetIn; try apply IHe1; try apply IHe2; eauto; try apply IHe3;
    try rewrite shiftnP_S; eauto.
    * eapply closed_subst_up_vdef; eauto; eapply inst_is_open_term; eauto.
    * rewrite on_free_vars_ctx_snoc_def; eauto.
  - rename p0 into Hp'; rename p1 into Hreturn'; rename p2 into Hcontext'; rename p3 into Hc'; rename p4 into Hbrs'.
    rename Hp into Hpold.
    rename p5 into Hp; rename p6 into Hreturn; rename p7 into Hcontext; rename p8 into Hc; rename p9 into Hbrs.
    eapply cumul_Case; fold inst.
    * unfold cumul_predicate in *; destruct_head'_prod.
      repeat split; eauto.
      + eapply All2_map. repeat toAll.
        eapply All2_impl. 1: tea. cbn; intros. destruct_head'_prod; eauto.
      + unfold preturn. cbn.
        unshelve erewrite (All2_fold_length _ : #|pcontext _| = #|pcontext _|); shelve_unifiable; tea.
        exactly_once (idtac; multimatch goal with H : _ |- _ => eapply H end); eauto.
        ++ unshelve erewrite <- (All2_fold_length _ : #|pcontext _| = #|pcontext _|); shelve_unifiable; tea.
           rewrite <- inst_case_predicate_context_length.
            rewrite inst_case_predicate_context_inst; eauto.
            eapply closed_subst_ext. 2: symmetry; apply up_Upn.
            eapply closed_subst_app; eauto. rewrite inst_inst_case_context; eauto.
            rewrite on_free_vars_ctx_inst_case_context_nil; eauto.
            +++ rewrite forallb_map. eapply forallb_impl. 2:tea. cbn; intros.
                eapply inst_is_open_term; eauto.
            +++ rewrite map_length. rewrite inst_context_on_free_vars ; eauto.
        ++ unfold PCUICCases.inst_case_predicate_context.
            apply on_free_vars_ctx_inst_case_context; eauto.
        ++ unfold PCUICCases.inst_case_predicate_context.
            unfold is_open_term. rewrite app_length.
            rewrite <- shiftnP_add.
            rewrite inst_case_predicate_context_length.
            eassumption.
        ++ unfold PCUICCases.inst_case_predicate_context.
            unfold is_open_term. rewrite app_length.
            rewrite <- shiftnP_add.
            rewrite inst_case_predicate_context_length.
            unshelve erewrite (All2_fold_length _ : #|pcontext _| = #|pcontext _|); shelve_unifiable; tea.
    * eauto.
    * rename Hbody into Hbrsbrs'.
      repeat toAll.
      eapply All2_impl. 1: tea. cbn; intros; destruct_head'_prod.
      unshelve erewrite (All2_fold_length _ : #|bcontext _| = #|bcontext _|); shelve_unifiable; tea.
      split; eauto.
      repeat match goal with H : is_true (andb _ _) |- _ => apply andb_and in H; destruct H end.
      rewrite -> test_context_k_closed_on_free_vars_ctx in *.
      exactly_once (idtac; multimatch goal with H : _ |- _ => eapply H end); eauto.
      + unshelve erewrite <- (All2_fold_length _ : #|bcontext _| = #|bcontext _|); shelve_unifiable; tea.
      rewrite <- (inst_case_branch_context_length p).
      rewrite inst_case_branch_context_inst; eauto.
      eapply closed_subst_ext. 2: symmetry; apply up_Upn.
      eapply closed_subst_app; eauto.
      rewrite inst_inst_case_context_wf; eauto.
        ++ rewrite test_context_k_closed_on_free_vars_ctx; tea.
        ++  rewrite on_free_vars_ctx_inst_case_context_nil; eauto.
          +++ repeat toAll. eapply All_impl; tea. simpl; intros.
              eapply inst_is_open_term; eauto.
          +++ rewrite map_length. tea.
      + unfold PCUICCases.inst_case_predicate_context.
        apply on_free_vars_ctx_inst_case_context; eauto.
        repeat toAll; eauto.
      + unfold PCUICCases.inst_case_predicate_context.
        unfold is_open_term. rewrite app_length.
        rewrite <- shiftnP_add.
        rewrite inst_case_branch_context_length.
        eassumption.
      + unfold PCUICCases.inst_case_predicate_context.
        unfold is_open_term. rewrite app_length.
        rewrite <- shiftnP_add.
        rewrite inst_case_branch_context_length.
        unshelve erewrite (All2_fold_length _ : #|bcontext _| = #|bcontext _|); shelve_unifiable; tea.
   - eapply cumul_Proj; try apply X0; eauto.
   - cbn. eapply cumul_Fix. cbn in HfreeA, HfreeB.
     repeat toAll. eapply All2_impl. 1: tea. cbn; intros.
     destruct_head'_prod.
     repeat split; eauto.
     * exactly_once (idtac; multimatch goal with H : _ |- _ => eapply H end); eauto.
       all: cbv [test_def] in *; cbn in *.
       all: repeat match goal with H : is_true (andb _ _) |- _ => apply andb_and in H; destruct H end.
       all: tea.
     * rewrite <- (All2_length X).
       exactly_once (idtac; multimatch goal with H : _ |- _ => eapply H end); eauto.
       all: cbv [test_def] in *; cbn in *.
       all: repeat match goal with H : is_true (andb _ _) |- _ => apply andb_and in H; destruct H end.
       + rewrite inst_fix_context_up.
       rewrite <- fix_context_length.
       eapply closed_subst_ext. 2: symmetry; apply up_Upn.
       apply closed_subst_app; eauto. rewrite <- inst_fix_context.
        apply on_free_vars_fix_context.
         apply All_map.
         eapply All2_All_left. 1: tea. cbn ; intros.
         destruct X0 as [[Hx0 _] _].
         unfold test_def. unfold test_def in Hx0.
         apply andb_and in Hx0. destruct Hx0 as [Hx0type Hx0body].
         apply andb_and. cbn. split.
         ++ eapply inst_is_open_term; eauto.
         ++ rewrite map_length.
            rewrite <- fix_context_length. rewrite <- up_Upn.
            eapply usubst_on_free_vars_shift; eauto.
            rewrite fix_context_length; eauto.
        + rewrite on_free_vars_ctx_app.
         apply andb_and; split; eauto.
         apply on_free_vars_fix_context.
         eapply All2_All_left. 1: tea. cbn; intros.
         apply X0.1.
         + unfold is_open_term. rewrite app_length.
         rewrite <- shiftnP_add.
         rewrite fix_context_length. eauto.
         + unfold is_open_term. rewrite app_length.
         rewrite <- shiftnP_add.
         rewrite fix_context_length.
         rewrite (All2_length X). eauto.
   - cbn. rewrite (All2_length X).
     eapply cumul_CoFix. cbn in HfreeA, HfreeB.
     repeat toAll.
     eapply All2_impl. 1: tea. cbn; intros.
     destruct_head'_prod.
     repeat split; eauto.
     * exactly_once (idtac; multimatch goal with H : _ |- _ => eapply H end); eauto.
       all: cbv [test_def] in *; cbn in *.
       all: repeat match goal with H : is_true (andb _ _) |- _ => apply andb_and in H; destruct H end.
       all: eauto.
     * rewrite <- (All2_length X).
       exactly_once (idtac; multimatch goal with H : _ |- _ => eapply H end); eauto.
       all: cbv [test_def] in *; cbn in *.
       all: repeat match goal with H : is_true (andb _ _) |- _ => apply andb_and in H; destruct H end.
       + rewrite inst_fix_context_up.
       rewrite <- fix_context_length.
       eapply closed_subst_ext. 2: symmetry; apply up_Upn.
       apply closed_subst_app; eauto. rewrite <- inst_fix_context.
        apply on_free_vars_fix_context.
         apply All_map.
         eapply All2_All_left. 1: tea. cbn ; intros.
         destruct X0 as [[Hx0 _] _].
         unfold test_def. unfold test_def in Hx0.
         apply andb_and in Hx0. destruct Hx0 as [Hx0type Hx0body].
         apply andb_and. cbn. split.
         ++ eapply inst_is_open_term; eauto.
         ++ rewrite map_length.
            rewrite <- fix_context_length. rewrite <- up_Upn.
            eapply usubst_on_free_vars_shift; eauto.
            rewrite fix_context_length; eauto.
        + rewrite on_free_vars_ctx_app.
         apply andb_and; split; eauto.
         apply on_free_vars_fix_context.
         eapply All2_All_left. 1: tea. cbn; intros.
         apply X0.1.
         + unfold is_open_term. rewrite app_length.
         rewrite <- shiftnP_add.
         rewrite fix_context_length. eauto.
         + unfold is_open_term. rewrite app_length.
         rewrite <- shiftnP_add.
         rewrite fix_context_length.
         rewrite (All2_length X). eauto.
   - cbn. eapply cumul_Prim. depelim X; cbn in HfreeA, HfreeB; rtoProp; constructor; cbn; eauto. solve_all.
   - cbn. repeat rewrite inst_mkApps. eapply cumul_Ind.
     * repeat rewrite map_length; eauto.
     * repeat toAll.
       eapply All2_impl. 1: tea. cbn; intros.
       destruct_head'_prod.
       eauto.
   - cbn. repeat rewrite inst_mkApps. eapply cumul_Construct.
     * repeat rewrite map_length; eauto.
     * repeat toAll.
       eapply All2_impl. 1: tea. cbn; intros.
       destruct_head'_prod.
       eauto.
   - eapply cumul_Sort; eauto.
   - eapply cumul_Const; eauto.
Defined.

Lemma inst_convSpec {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Δ σ A B} :
  closed_subst Γ σ Δ ->
  is_closed_context Γ ->
  is_open_term Γ A ->
  is_open_term Γ B ->
  Σ ;;; Γ |- A =s B ->
  Σ ;;; Δ |- A.[σ] =s B.[σ].
Proof.
  apply inst_cumulSpec.
Qed.

Lemma inst_prim_type σ p pty : (prim_type p pty).[σ] = prim_type (map_prim (inst σ) p) pty.
Proof.
  destruct p as [? []] => //.
Qed.

Lemma type_inst {cf : checker_flags} : env_prop
  (fun Σ Γ t A =>
    forall Δ σ,
    wf_local Σ Δ ->
    Σ ;;; Δ ⊢ σ : Γ ->
    Σ ;;; Δ |- t.[σ] : A.[σ])
  (fun Σ Γ =>
    All_local_env
    (lift_typing (fun (Σ : global_env_ext) (Γ : context) (t T : term)
    =>
    forall Δ σ,
    wf_local Σ Δ ->
    Σ ;;; Δ ⊢ σ : Γ ->
    Σ ;;; Δ |- t.[σ] : T.[σ]) Σ) Γ).
Proof.
  apply typing_ind_env.

  - intros Σ wfΣ Γ wfΓ. auto.
    induction 1; constructor; tas.
    all: apply infer_typing_sort_impl with id tu; auto.
  - intros Σ wfΣ Γ wfΓ n decl e X Δ σ hΔ hσ. simpl.
    eapply hσ. assumption.
  - intros Σ wfΣ Γ wfΓ l X H0 Δ σ hΔ hσ. simpl.
    econstructor. all: assumption.
  - intros Σ wfΣ Γ wfΓ na A B s1 s2 X hA ihA hB ihB Δ σ hΔ hσ.
    autorewrite with sigma. simpl.
    econstructor.
    + eapply ihA ; auto.
    + eapply ihB.
      * econstructor ; auto.
        eexists. eapply ihA ; auto.
      * eapply well_subst_Up. 2: assumption.
        econstructor ; auto.
        eexists. eapply ihA. all: auto.
  - intros Σ wfΣ Γ wfΓ na A t s1 bty X hA ihA ht iht Δ σ hΔ hσ.
    autorewrite with sigma.
    econstructor.
    + eapply ihA ; auto.
    + eapply iht.
      * econstructor ; auto.
        eexists. eapply ihA ; auto.
      * eapply well_subst_Up. 2: assumption.
        constructor. 1: assumption.
        eexists. eapply ihA. all: auto.
  - intros Σ wfΣ Γ wfΓ na b B t s1 A X hB ihB hb ihb ht iht Δ σ hΔ hσ.
    autorewrite with sigma.
    econstructor.
    + eapply ihB. all: auto.
    + eapply ihb. all: auto.
    + eapply iht.
      * econstructor. all: auto.
        -- eexists. eapply ihB. all: auto.
        -- simpl. eapply ihb. all: auto.
      * eapply well_subst_Up'; try assumption.
        constructor; auto.
        ** exists s1. apply ihB; auto.
        ** apply ihb; auto.
  - intros Σ wfΣ Γ wfΓ t na A B s u X hty ihty ht iht hu ihu Δ σ hΔ hσ.
    autorewrite with sigma.
    econstructor.
    * specialize (ihty _ _ hΔ hσ).
      simpl in ihty. eapply meta_conv_term; [eapply ihty|].
      now rewrite up_Up.
    * specialize (iht _ _ hΔ hσ).
      simpl in iht. eapply meta_conv; [eapply iht|].
      now rewrite up_Up.
    * eapply ihu; auto.
  - intros Σ wfΣ Γ wfΓ cst u decl X X0 isdecl hconst Δ σ hΔ hσ.
    autorewrite with sigma. simpl.
    eapply meta_conv; [econstructor; eauto|].
    eapply declared_constant_closed_type in isdecl; eauto.
    rewrite inst_closed0; auto.
    now rewrite closedn_subst_instance.
  - intros Σ wfΣ Γ wfΓ ind u mdecl idecl isdecl X X0 hconst Δ σ hΔ hσ.
    eapply meta_conv; [econstructor; eauto|].
    eapply declared_inductive_closed_type in isdecl; eauto.
    rewrite inst_closed0; auto.
    now rewrite closedn_subst_instance.
  - intros Σ wfΣ Γ wfΓ ind i u mdecl idecl cdecl isdecl X X0 hconst Δ σ hΔ hσ.
    eapply meta_conv; [econstructor; eauto|].
    eapply declared_constructor_closed_type in isdecl; eauto.
    rewrite inst_closed0; eauto.
  - intros Σ wfΣ Γ wfΓ ci p c brs indices ps mdecl idecl isdecl HΣ.
    intros IHΔ ci_npar eqpctx predctx wfp cup Hpctx Hpret
      IHpret IHpredctx isallowed.
    intros IHctxi Hc IHc iscof ptm wfbrs Hbrs Δ f HΔ Hf.
    autorewrite with sigma. simpl.
    rewrite map_app. simpl.
    rewrite /ptm. rewrite inst_it_mkLambda_or_LetIn.
    relativize #|predctx|.
    * erewrite inst_predicate_preturn.
      rewrite /predctx.
      rewrite inst_case_predicate_context //.
      eapply type_Case; eauto;
       rewrite - ?inst_case_predicate_context //.
      3,4 : constructor; eauto;
        rewrite - ?inst_case_predicate_context //.
      + apply All_local_env_app_inv in Hpctx as [].
        apply All_local_env_app_inv in IHpredctx as [].
        eapply IHpret.
        ++ eapply wf_local_app_inst; eauto.
           apply a2.
        ++ relativize #|pcontext p|; [eapply well_subst_app_up|] => //; rewrite /predctx; len.
           2:{ rewrite case_predicate_context_length //. }
           eapply wf_local_app_inst; eauto. apply a2.
      + simpl. unfold id.
        specialize (IHc _ _ HΔ Hf).
        now rewrite inst_mkApps map_app in IHc.
      + now eapply inst_wf_predicate.
      + simpl.
        apply All_local_env_app_inv in Hpctx as [].
        eapply wf_local_app_inst; eauto.
        apply All_local_env_app_inv in IHpredctx as [].
        apply a2.
      + revert IHctxi.
        rewrite /= /id -map_app.
        rewrite -{2}[subst_instance _ _](inst_closedn_ctx f 0).
        { pose proof (declared_inductive_closed_pars_indices isdecl).
          now rewrite closedn_subst_instance_context. }
        rewrite inst_context_telescope.
        rewrite inst_telescope_upn0.
        clear -Δ f HΔ Hf.
        induction 1.
        { constructor; auto. }
        { destruct t0; simpl. rewrite inst_telescope_cons.
          constructor; cbn; eauto.
          now rewrite inst_subst_telescope /= in IHIHctxi. }
        { simpl. rewrite inst_telescope_cons.
          constructor; cbn; eauto.
          now rewrite inst_subst_telescope /= in IHIHctxi. }
      + now eapply inst_wf_branches.
      + eapply Forall2_All2 in wfbrs.
        eapply All2i_All2_mix_left in Hbrs; eauto.
        eapply All2i_nth_hyp in Hbrs.
        eapply All2i_map_right, (All2i_impl Hbrs) => i cdecl br.
        set (brctxty := case_branch_type _ _ _ _ _ _ _ _).
        intros (Hnth & wfbr & Hconv & Hbrctx & (Hbr & IHbr) & Hbty & IHbty).
        split => //.
        rewrite -(inst_closed_constructor_body mdecl cdecl f).
        { eapply (declared_constructor_closed (c:=(ci.(ci_ind),i))); eauto.
          split; eauto. }
        rewrite inst_case_predicate_context //.
        rewrite inst_case_branch_type //.
        rewrite -/brctxty. intros brctx'.
        assert (wf_local Σ (Δ,,, brctx'.1)).
        { rewrite /brctx'. cbn.
          apply All_local_env_app_inv in Hbrctx as [].
          eapply wf_local_app_inst; tea. apply a0. }
        split => //. split.
        ++ eapply IHbr => //.
          rewrite /brctx' /brctxty; cbn.
          relativize #|bcontext br|.
          { eapply well_subst_app_up => //. }
          rewrite /case_branch_type /=.
          rewrite case_branch_context_length //.
        ++ eapply IHbty=> //.
          rewrite /brctx'; cbn.
          relativize #|bcontext br|.
          { eapply well_subst_app_up => //. }
          rewrite /brctxty /= case_branch_context_length //.
    * rewrite /predctx case_predicate_context_length //.
  - intros Σ wfΣ Γ wfΓ p c u mdecl idecl cdecl pdecl isdecl args X X0 hc ihc e
           Δ σ hΔ hσ.
    simpl.
    eapply meta_conv; [econstructor|].
    * eauto.
    * specialize (ihc _ _ hΔ hσ).
      rewrite inst_mkApps in ihc. eapply ihc.
    * now rewrite map_length.
    * autorewrite with sigma.
      eapply declared_projection_closed in isdecl; auto.
      move: isdecl.
      rewrite -(closedn_subst_instance _ _ u).
      eapply inst_ext_closed.
      intros x Hx.
      rewrite subst_consn_lt /=; len; try lia.
      rewrite Upn_comp; cbn; try now repeat len.
      rewrite subst_consn_lt /=; cbn; len; try lia.
      now rewrite map_rev.
  - intros Σ wfΣ Γ wfΓ mfix n decl types hguard hnth htypes hmfix ihmfix wffix Δ σ hΔ hσ.
    simpl. eapply meta_conv; [econstructor;eauto|].
    * now eapply fix_guard_inst.
    * now rewrite nth_error_map hnth.
    * solve_all.
      apply infer_typing_sort_impl with id a; intros [_ IH].
      now apply IH.
    * solve_all. destruct b as [? b0].
      len. rewrite /types in b0. len in b0.
      pose proof (inst_fix_context mfix σ).
      setoid_rewrite <-up_Upn at 1 in H. rewrite H.
      eapply All_local_env_app_inv in htypes as [].
      eapply meta_conv; [eapply b0; eauto|].
      + eapply wf_local_app_inst; eauto. eapply a1.
      + rewrite -(fix_context_length mfix).
        eapply well_subst_app_up => //.
        eapply wf_local_app_inst; eauto. apply a1.
      + rewrite lift0_inst. now sigma.
    * now apply inst_wf_fixpoint.
    * reflexivity.

  - intros Σ wfΣ Γ wfΓ mfix n decl types hguard hnth htypes hmfix ihmfix wffix Δ σ hΔ hσ.
    simpl. eapply meta_conv; [econstructor;eauto|].
    * now eapply cofix_guard_inst.
    * now rewrite nth_error_map hnth.
    * solve_all.
      apply infer_typing_sort_impl with id a; intros [_ IH].
      now apply IH.
    * solve_all. destruct b as [? b0].
      len. rewrite /types in b0. len in b0.
      pose proof (inst_fix_context mfix σ).
      setoid_rewrite <-up_Upn at 1 in H. rewrite H.
      eapply All_local_env_app_inv in htypes as [].
      eapply meta_conv; [eapply b0; eauto|].
      + eapply wf_local_app_inst; eauto. eapply a1.
      + rewrite -(fix_context_length mfix).
        eapply well_subst_app_up => //.
        eapply wf_local_app_inst; eauto. apply a1.
      + rewrite lift0_inst. now sigma.
    * now apply inst_wf_cofixpoint.
    * reflexivity.

  - intros Σ wfΣ Γ wfΓ p pty cdecl _ hp hdecl pinv hty hind Δ σ hΔ hσ.
    cbn. rewrite inst_prim_type. econstructor; tea.
    1-2:now rewrite prim_val_tag_map.
    depelim hind; constructor; cbn; eauto. solve_all.

  - intros Σ wfΣ Γ wfΓ t A B X hwf ht iht hB ihB hcum Δ σ hΔ hσ.
    eapply type_Cumul.
    + eapply iht. all: auto.
    + eapply ihB. all: auto.
    + eapply inst_cumulSpec => //.
      * eapply well_subst_closed_subst; tea. eapply wf_local_closed_context; tea.
      * eapply wf_local_closed_context; tea.
      * eapply type_closed in ht.
        now eapply closedn_on_free_vars.
      * eapply subject_closed in hB.
        now eapply closedn_on_free_vars.
      * apply hcum.
Qed.

Lemma typing_inst {cf : checker_flags} Σ Γ t A Δ σ {wfΣ : wf Σ.1} :
  wf_local Σ Δ ->
  Σ ;;; Δ ⊢ σ : Γ ->
  Σ ;;; Γ |- t : A ->
  Σ ;;; Δ |- t.[σ] : A.[σ].
Proof.
  intros a b c; revert a b. eapply type_inst; eauto.
Qed.
