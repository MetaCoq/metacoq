(* Distributed under the terms of the MIT license. *)
From MetaCoq.Utils Require Import MCUtils utils.
From MetaCoq.Common Require Import config.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
  PCUICWeakeningConfig PCUICEquality PCUICReduction PCUICCumulativity PCUICCumulativitySpec
  (* PCUICContextSubst *) (* PCUICUnivSubst *) (* PCUICCases *) (* PCUICTyping *)
  (* PCUICGuardCondition *) (* PCUICGlobalEnv *).
From Equations Require Import Equations.

Require Import ssreflect.

Set Default Goal Selector "!".
Implicit Types (cf : checker_flags).

Lemma compare_term_config_impl {cf1 cf2} pb Σ φ t t'
  : config.impl cf1 cf2
    -> @compare_term cf1 pb Σ φ t t' -> @compare_term cf2 pb Σ φ t t'.
Proof.
  intro H. apply eq_term_upto_univ_impl; auto.
  all: repeat change (@eq_universe ?cf) with (@compare_universe cf Conv).
  all: repeat change (@leq_universe ?cf) with (@compare_universe cf Cumul).
  3: destruct pb.
  4: transitivity (@compare_universe cf1 Cumul φ); tc.
  all: intros ??; now eapply cmp_universe_config_impl.
Qed.

Lemma eq_term_config_impl {cf1 cf2} Σ φ t t'
  : config.impl cf1 cf2 -> @compare_term cf1 Conv Σ φ t t' -> @compare_term cf2 Conv Σ φ t t'.
Proof. eapply compare_term_config_impl with (pb := Conv). Qed.

Lemma leq_term_config_impl {cf1 cf2} Σ ctrs t u
  : config.impl cf1 cf2 -> @compare_term cf1 Cumul Σ ctrs t u -> @compare_term cf2 Cumul Σ ctrs t u.
Proof. apply compare_term_config_impl with (pb := Cumul). Qed.

Lemma compare_decl_config_impl {cf1 cf2} pb Σ φ d d'
  : config.impl cf1 cf2
    -> @compare_decl cf1 pb Σ φ d d' -> @compare_decl cf2 pb Σ φ d d'.
Proof.
  intros Hcf []; constructor; eauto using (@compare_term_config_impl cf1 cf2).
Qed.

Lemma compare_context_config_impl {cf1 cf2} pb Σ φ Γ Γ'
  : config.impl cf1 cf2
    -> @compare_context cf1 pb Σ φ Γ Γ' -> @compare_context cf2 pb Σ φ Γ Γ'.
Proof.
  intros Hcf. induction 1; constructor; auto; eapply (@compare_decl_config_impl cf1 cf2); eassumption.
Qed.

(* TODO: Factor with PCUICWeakeningEnvConv.R_global_instance_weaken_env *)
Lemma R_global_instance_weaken_subrel Σ Re Re' Rle Rle' gr napp :
  RelationClasses.subrelation Re Re' ->
  RelationClasses.subrelation Rle Rle' ->
  RelationClasses.subrelation Re Rle' ->
  subrelation (R_global_instance Σ Re Rle gr napp) (R_global_instance Σ Re' Rle' gr napp).
Proof.
  intros he hle hele t t'.
  rewrite /R_global_instance_gen /R_opt_variance.
  destruct global_variance_gen as [v|] eqn:look.
  - induction t in v, t' |- *; destruct v, t'; simpl; auto.
    intros []; split; auto.
    destruct t0; simpl; auto.
  - eauto using R_universe_instance_impl'.
Qed.

(* TODO: Factor with PCUICWeakeningEnvConv.eq_term_upto_univ_weaken_env *)
#[global]
Instance eq_term_upto_univ_weaken_subrel Σ Re Re' Rle Rle' napp :
  RelationClasses.subrelation Re Re' ->
  RelationClasses.subrelation Rle Rle' ->
  RelationClasses.subrelation Re Rle' ->
  CRelationClasses.subrelation (eq_term_upto_univ_napp Σ Re Rle napp)
    (eq_term_upto_univ_napp Σ Re' Rle' napp).
Proof.
  intros he hele hle t t'.
  induction t in napp, t', Rle, Rle', hle, hele |- * using PCUICInduction.term_forall_list_ind;
    try (inversion 1; subst; constructor;
         eauto using R_universe_instance_impl'; fail).
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
  - inversion 1; subst; constructor.
    eapply R_global_instance_weaken_subrel; [ .. | eassumption ]. all:eauto.
  - inversion 1; subst; constructor.
    eapply R_global_instance_weaken_subrel; [ .. | eassumption ]. all:eauto.
  - inversion 1; subst; destruct X as [? [? ?]]; constructor; eauto.
    * destruct X2 as [? [? ?]].
      constructor; intuition auto; solve_all.
      + eauto using R_universe_instance_impl'.
    * eapply All2_impl'; tea.
      eapply All_impl; eauto.
      cbn. intros x [? ?] y [? ?]. split; eauto.
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x [? ?] y [[[? ?] ?] ?]. repeat split; eauto.
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x [? ?] y [[[? ?] ?] ?]. repeat split; eauto.
Qed.

Lemma weakening_config_cumul_gen {cf1 cf2} pb Σ Γ M N :
  config.impl cf1 cf2 ->
  @cumulAlgo_gen cf1 Σ Γ pb M N ->
  @cumulAlgo_gen cf2 Σ Γ pb M N.
Proof.
  intro Hcf; induction 1; simpl; trivial.
  all: now econstructor; try eassumption; eapply (@compare_term_config_impl cf1 cf2); eassumption.
Qed.

Lemma weakening_config_conv {cf1 cf2} Σ Γ M N :
  config.impl cf1 cf2 ->
  @cumulAlgo_gen cf1 Σ Γ Conv M N ->
  @cumulAlgo_gen cf2 Σ Γ Conv M N.
Proof. apply weakening_config_cumul_gen with (pb := Conv). Qed.

Lemma weakening_config_cumul {cf1 cf2} Σ Γ M N :
  config.impl cf1 cf2 ->
  @cumulAlgo_gen cf1 Σ Γ Cumul M N ->
  @cumulAlgo_gen cf2 Σ Γ Cumul M N.
Proof. apply weakening_config_cumul_gen with (pb := Cumul). Qed.

Lemma weakening_config_cumulSpec0 {cf1 cf2} Σ Γ pb M N :
  config.impl cf1 cf2 ->
  @cumulSpec0 cf1 Σ Γ pb M N ->
  @cumulSpec0 cf2 Σ Γ pb M N.
Proof.
  intros Hcf.
  induction 1.
  all:intros; try solve [econstructor; try eassumption; intuition auto].
  all: lazymatch goal with
       | [ H : cumul_predicate_dep _ _ _ |- _ ] => apply cumul_predicate_undep in H
       | _ => idtac
       end.
  - eapply cumul_Evar. solve_all.
  - eapply cumul_Case.
    * cbv [cumul_predicate] in *; destruct_head'_prod. repeat split; tas.
      + eapply R_universe_instance_impl';
          [ hnf; intros * ?; eapply (@cmp_universe_config_impl cf1 cf2) | ];
          eassumption.
    * solve_all.
    * solve_all.
  - eapply cumul_Fix. solve_all.
  - eapply cumul_CoFix; solve_all.
  - eapply cumul_Ind; eauto. 2:solve_all.
    eapply @R_global_instance_weaken_subrel; [ .. | eassumption ].
    all: repeat change (@eq_universe ?cf) with (@compare_universe cf Conv).
    all: repeat change (@leq_universe ?cf) with (@compare_universe cf Cumul).
    3: destruct pb.
    all: try (hnf; intros *; eapply (@cmp_universe_config_impl cf1 cf2); eassumption).
    all: now etransitivity; [ | hnf; intros *; eapply (@cmp_universe_config_impl cf1 cf2); eassumption ]; tc.
  - eapply cumul_Construct; eauto. 2:solve_all.
    eapply @R_global_instance_weaken_subrel; [ .. | eassumption ].
    all: repeat change (@eq_universe ?cf) with (@compare_universe cf Conv).
    all: repeat change (@leq_universe ?cf) with (@compare_universe cf Cumul).
    3: destruct pb.
    all: try (hnf; intros *; eapply (@cmp_universe_config_impl cf1 cf2); eassumption).
    all: now etransitivity; [ | hnf; intros *; eapply (@cmp_universe_config_impl cf1 cf2); eassumption ]; tc.
  - eapply cumul_Sort. eapply (@cmp_universe_config_impl cf1 cf2); eassumption.
  - eapply cumul_Const. eapply R_universe_instance_impl'; eauto; tc.
    hnf; intros *; eapply (@cmp_universe_config_impl cf1 cf2); eassumption.
Defined.

Lemma weakening_config_convSpec {cf1 cf2} Σ Γ M N :
  config.impl cf1 cf2 ->
  @convSpec cf1 Σ Γ M N ->
  @convSpec cf2 Σ Γ M N.
Proof. apply weakening_config_cumulSpec0 with (pb := Conv). Qed.

Lemma weakening_config_cumulSpec {cf1 cf2} Σ Γ M N :
  config.impl cf1 cf2 ->
  @cumulSpec cf1 Σ Γ M N ->
  @cumulSpec cf2 Σ Γ M N.
Proof. apply weakening_config_cumulSpec0 with (pb := Cumul). Qed.

Lemma weakening_config_conv_decls {cf1 cf2 Σ Γ Γ'} :
  config.impl cf1 cf2 ->
  CRelationClasses.subrelation (conv_decls (@cumulSpec0 cf1) Σ Γ Γ') (conv_decls (@cumulSpec0 cf2) Σ Γ Γ').
Proof.
  intros Hcf d d' Hd; depelim Hd; constructor; tas;
    eapply (@weakening_config_convSpec cf1 cf2); tea.
Qed.

Lemma weakening_config_cumul_decls {cf1 cf2 Σ Γ Γ'} :
  config.impl cf1 cf2 ->
  CRelationClasses.subrelation (cumul_decls (@cumulSpec0 cf1) Σ Γ Γ') (cumul_decls (@cumulSpec0 cf2) Σ Γ Γ').
Proof.
  intros Hcf d d' Hd; depelim Hd; constructor; tas;
    (eapply (@weakening_config_convSpec cf1 cf2) || eapply (@weakening_config_cumulSpec cf1 cf2)); tea.
Qed.

Lemma weakening_config_conv_ctx {cf1 cf2 Σ Γ Δ} :
  config.impl cf1 cf2 ->
  conv_context (@cumulSpec0 cf1) Σ Γ Δ ->
  conv_context (@cumulSpec0 cf2) Σ Γ Δ.
Proof.
  intros Hcf.
  intros; eapply All2_fold_impl; tea => Γ0 Γ' d d'.
  now eapply weakening_config_conv_decls.
Qed.


Lemma weakening_config_cumul_ctx {cf1 cf2 Σ Γ Δ} :
  config.impl cf1 cf2 ->
  cumul_context (@cumulSpec0 cf1) Σ Γ Δ ->
  cumul_context (@cumulSpec0 cf2) Σ Γ Δ.
Proof.
  intros Hcf.
  intros; eapply All2_fold_impl; tea => Γ0 Γ' d d'.
  now eapply weakening_config_cumul_decls.
Qed.

(*
#[global] Hint Resolve weakening_config_conv_ctx : config.
#[global] Hint Resolve weakening_config_cumul_ctx : config.
*)
