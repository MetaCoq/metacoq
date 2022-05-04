(* Distributed under the terms of the MIT license. *)
From Coq Require Import Morphisms.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICOnOne PCUICAstUtils PCUICCases PCUICInduction
  PCUICLiftSubst PCUICUnivSubst PCUICRelevance PCUICCumulativity
  PCUICReduction PCUICGlobalEnv PCUICClosed PCUICEquality PCUICRenameDef PCUICWeakeningEnvConv
  PCUICSigmaCalculus PCUICClosed PCUICOnFreeVars PCUICGuardCondition
  PCUICWeakeningEnvTyp PCUICClosedConv PCUICClosedTyp PCUICViews
  PCUICTyping PCUICRenameTerm.

Require Import ssreflect ssrbool.
From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.
Set Equations With UIP.

(** * Type preservation for σ-calculus operations *)

Open Scope sigma_scope.
Set Keyed Unification.

Set Default Goal Selector "!".

Section Renaming2.

Context `{cf : checker_flags}.

Lemma rename_iota_red :
  forall f p pars args br,
  #|skipn pars args| = context_assumptions br.(bcontext) ->
  closedn_ctx #|pparams p| br.(bcontext) ->
  rename f (iota_red pars p args br) =
  iota_red pars (rename_predicate f p) (map (rename f) args) (rename_branch f br).
Proof using Type.
  intros f p pars args br hlen hlen'.
  unfold iota_red.
  rewrite rename_subst0 map_rev map_skipn. f_equal.
  rewrite List.rev_length /expand_lets /expand_lets_k.
  rewrite rename_subst0. len.
  rewrite shiftn_add -hlen Nat.add_comm rename_shiftnk.
  rewrite hlen.
  relativize (context_assumptions _); [erewrite rename_extended_subst|now len].
  f_equal. f_equal.
  rewrite rename_inst_case_context. f_equal. f_equal.
  rewrite /inst_case_branch_context.
  now rewrite rename_closedn_ctx.
Qed.

Lemma red1_rename :
  forall P Σ Γ Δ u v f,
    wf Σ ->
    urenaming P Δ Γ f ->
    on_free_vars P u ->
    red1 Σ Γ u v ->
    red1 Σ Δ (rename f u) (rename f v).
Proof using cf.
  intros P Σ Γ Δ u v f wfΣ hf hav h.
  induction h using red1_ind_all in P, f, Δ, hav, hf |- *.
  all: try solve [
    try (cbn in hav; rtoProp);
    simpl ; constructor ; eapply IHh ;
    try eapply urenaming_vass ;
    try eapply urenaming_vdef ;
    eassumption
  ].
  all:simpl in hav |- *; try toAll.
  - rewrite rename_subst10. constructor.
  - rewrite rename_subst10. constructor.
  - destruct (nth_error Γ i) eqn:hnth; noconf H.
    unfold urenaming in hf.
    specialize hf with (1 := hav) (2 := hnth).
    destruct hf as [decl' [e' [? [hr hbo]]]].
    rewrite H /= in hbo.
    rewrite lift0_rename.
    destruct (decl_body decl') eqn:hdecl => //. noconf hbo.
    sigma in H0. sigma. rewrite H0.
    relativize (t.[_]).
    2:{ setoid_rewrite rshiftk_S. rewrite -rename_inst.
        now rewrite -(lift0_rename (S (f i)) _). }
    constructor. now rewrite e' /= hdecl.
  - rewrite rename_mkApps. simpl.
    rewrite rename_iota_red //.
    * rewrite skipn_length; lia.
    * change (bcontext br) with (bcontext (rename_branch f br)).
      move/and5P: hav => [_ _ _ _ hbrs].
      eapply nth_error_forallb in hbrs; tea. simpl in hbrs.
      move/andP: hbrs => [] clbctx clbod.
      rewrite closedn_ctx_on_free_vars.
      now rewrite test_context_k_closed_on_free_vars_ctx in clbctx.
    * constructor.
      + rewrite nth_error_map H /= //.
      + simpl. now len.
  - rewrite 2!rename_mkApps. simpl.
    econstructor.
    + eapply rename_unfold_fix. eassumption.
    + rewrite -is_constructor_rename. assumption.
  - rewrite 2!rename_mkApps. simpl.
    eapply red_cofix_case.
    eapply rename_unfold_cofix. eassumption.
  - rewrite 2!rename_mkApps. simpl.
    eapply red_cofix_proj.
    eapply rename_unfold_cofix. eassumption.
  - rewrite rename_subst_instance.
    econstructor.
    + eassumption.
    + rewrite rename_closed. 2: assumption.
      eapply declared_constant_closed_body. all: eauto.
  - rewrite rename_mkApps. simpl.
    econstructor. rewrite nth_error_map. rewrite H. reflexivity.
  - move/and4P: hav=> [hpars hret hc hbrs].
    rewrite rename_predicate_set_pparams. econstructor.
    simpl. eapply OnOne2_map. repeat toAll.
    eapply OnOne2_All_mix_left in X; eauto. solve_all. red; eauto.
  - move/and4P: hav=> [_ hret hpctx _].
    rewrite rename_predicate_set_preturn.
    eapply case_red_return; eauto.
    simpl.
    eapply IHh; eauto.
    rewrite /inst_case_predicate_context. rewrite /= /id.
    rewrite -rename_inst_case_context_wf //.
    relativize #|pcontext p|; [apply urenaming_context; tea|].
    now len.
  - move/and5P: hav=> [_ _ _ _ hbrs].
    eapply case_red_brs; eauto.
    eapply OnOne2_map. toAll.
    eapply OnOne2_All_mix_left in X; tea. clear hbrs.
    solve_all.
    simpl. red. split; auto.
    rewrite /inst_case_branch_context /=.
    rewrite -b0 //.
    eapply b1; tea.
    rewrite -rename_inst_case_context_wf //.
    relativize #|bcontext x|; [apply urenaming_context; tea|].
    now len.
  - eapply OnOne2_All_mix_left in X; eauto.
    constructor.
    eapply OnOne2_map. solve_all. red. eauto.
  - eapply OnOne2_All_mix_left in X; eauto.
    apply OnOne2_length in X as hl. rewrite <- hl. clear hl.
    generalize #|mfix0|. intro n.
    constructor. eapply OnOne2_map. solve_all.
    red. simpl. destruct x, y; simpl in *; noconf b0. split; auto.
    rewrite /test_def /= in b. move/andP: b => [hty hbod].
    eauto.
  - eapply OnOne2_All_mix_left in X; eauto.
    apply OnOne2_length in X as hl. rewrite <- hl. clear hl.
    eapply fix_red_body. eapply OnOne2_map. solve_all.
    red. simpl. destruct x, y; simpl in *; noconf b0. split; auto.
    rewrite /test_def /= in b. move/andP: b => [hty hbod].
    eapply b1.
    * rewrite rename_fix_context. rewrite <- fix_context_length.
      now eapply urenaming_context.
    * now len.
  - eapply OnOne2_All_mix_left in X; eauto.
    apply OnOne2_length in X as hl. rewrite <- hl. clear hl.
    generalize #|mfix0|. intro n.
    constructor. eapply OnOne2_map. solve_all.
    red. simpl. destruct x, y; simpl in *; noconf b0. split; auto.
    rewrite /test_def /= in b. move/andP: b => [hty hbod].
    eauto.
  - eapply OnOne2_All_mix_left in X; eauto.
    apply OnOne2_length in X as hl. rewrite <- hl. clear hl.
    eapply cofix_red_body. eapply OnOne2_map. solve_all.
    red. simpl. destruct x, y; simpl in *; noconf b0. split; auto.
    rewrite /test_def /= in b. move/andP: b => [hty hbod].
    eapply b1.
    * rewrite rename_fix_context. rewrite <- fix_context_length.
      now eapply urenaming_context.
    * now len.
Qed.

Lemma red_on_free_vars {P : nat -> bool} {Σ:global_env_ext} {Γ u v} {wfΣ : wf Σ} :
  on_ctx_free_vars P Γ ->
  on_free_vars P u ->
  red Σ Γ u v ->
  on_free_vars P v.
Proof using Type.
  intros onΓ on r.
  induction r; auto.
  now eapply red1_on_free_vars.
Qed.

Lemma red_rename :
  forall P (Σ : global_env_ext) Γ Δ u v f,
    wf Σ ->
    urenaming P Δ Γ f ->
    on_ctx_free_vars P Γ ->
    on_free_vars P u ->
    red Σ Γ u v ->
    red Σ Δ (rename f u) (rename f v).
Proof using Type.
  intros.
  induction X1.
  - constructor. now eapply red1_rename.
  - reflexivity.
  - etransitivity.
    * eapply IHX1_1. eauto.
    * eapply IHX1_2. eapply red_on_free_vars; eauto.
Qed.

Lemma conv_renameP :
  forall P Σ Γ Δ f A B,
    wf Σ.1 ->
    urenaming P Δ Γ f ->
    on_free_vars P A ->
    on_free_vars P B ->
    on_ctx_free_vars P Γ ->
    Σ ;;; Γ |- A = B ->
    Σ ;;; Δ |- rename f A = rename f B.
Proof using Type.
  intros P Σ Γ Δ f A B hΣ hf hA hB hΓ h.
  induction h.
  - eapply cumul_refl. eapply eq_term_upto_univ_rename. assumption.
  - eapply cumul_red_l.
    + eapply red1_rename. all: try eassumption.
    + apply IHh.
      * eapply red1_on_free_vars; tea.
      * auto.
  - eapply cumul_red_r.
    + eapply IHh; eauto. eapply (red1_on_free_vars); tea.
    + eapply red1_rename. all: try eassumption.
Qed.

Lemma cumul_renameP :
  forall P Σ Γ Δ f A B,
    wf Σ.1 ->
    urenaming P Δ Γ f ->
    on_free_vars P A ->
    on_free_vars P B ->
    on_ctx_free_vars P Γ ->
    Σ ;;; Γ |- A <= B ->
    Σ ;;; Δ |- rename f A <= rename f B.
Proof using Type.
  intros P Σ Γ Δ f A B hΣ hf hA hB hΓ h.
  induction h.
  - eapply cumul_refl. eapply eq_term_upto_univ_rename. assumption.
  - eapply cumul_red_l.
    + eapply red1_rename. all: try eassumption.
    + apply IHh.
      * eapply red1_on_free_vars; tea.
      * auto.
  - eapply cumul_red_r.
    + eapply IHh; eauto. eapply red1_on_free_vars; tea.
    + eapply red1_rename. all: try eassumption.
Qed.

End Renaming2.
