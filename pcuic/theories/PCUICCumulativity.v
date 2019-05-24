(* Distributed under the terms of the MIT license.   *)
From Equations Require Import Equations.
From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From MetaCoq.Template Require Import config utils AstUtils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICWeakeningEnv PCUICWeakening
     PCUICClosed PCUICReduction.
Require Import ssreflect ssrbool.
Require Import String.
Require Import LibHypsNaming.
Local Open Scope string_scope.
Set Asymmetric Patterns.
Require Import CRelationClasses.
Require Import Equations.Type.Relation Equations.Type.Relation_Properties.

Existing Instance config.default_checker_flags.

Reserved Notation " Σ ;;; Γ |- t == u " (at level 50, Γ, t, u at next level).

Lemma cumul_alt Σ Γ t u :
  Σ ;;; Γ |- t <= u <~> { v & { v' & (red Σ Γ t v * red Σ Γ u v' * leq_term (snd Σ) v v')%type } }.
Proof.
  split.
  { induction 1. exists t, u. intuition auto; constructor.
    destruct IHX as (v' & v'' & (redv & redv') & leqv).
    exists v', v''. intuition auto. now eapply red_step.
    destruct IHX as (v' & v'' & (redv & redv') & leqv).
    exists v', v''. intuition auto. now eapply red_step. }
  { intros [v [v' [[redv redv'] Hleq]]]. apply red_alt in redv. apply red_alt in redv'.
    apply clos_rt_rt1n in redv.
    apply clos_rt_rt1n in redv'.
    induction redv. induction redv'. constructor; auto.
    econstructor 3; eauto.
    econstructor 2; eauto. }
Qed.

Lemma red_cumul {Σ : global_context} {Γ t u} : red Σ Γ t u -> Σ ;;; Γ |- t <= u.
Proof.
  intros. apply red_alt in X. apply clos_rt_rt1n in X.
  induction X. apply cumul_refl'.
  econstructor 2; eauto.
Qed.

Lemma red_cumul_inv {Σ : global_context} {Γ t u} : red Σ Γ t u -> Σ ;;; Γ |- u <= t.
Proof.
  intros. apply red_alt in X. apply clos_rt_rt1n in X.
  induction X. apply cumul_refl'.
  econstructor 3; eauto.
Qed.


Lemma eq_universe_refl φ s : eq_universe φ s s.
Proof.
  intros vH; reflexivity.
Qed.

Lemma eq_universe'_refl `{checker_flags} φ s : eq_universe' φ s s.
Proof.
  unfold eq_universe'; destruct check_univs; [apply eq_universe_refl|constructor].
Qed.

Lemma leq_universe_refl φ s : leq_universe φ s s.
Proof.
  intros vH; reflexivity.
Qed.

Lemma leq_universe'_refl `{checker_flags} φ s : leq_universe' φ s s.
Proof.
  unfold leq_universe'; destruct check_univs; [apply leq_universe_refl|constructor].
Qed.

Lemma eq_term_upto_univ_refl R (HR : RelationClasses.Reflexive R) t
  : eq_term_upto_univ R t t.
Proof.
  induction t using term_forall_list_ind; simpl;
    try constructor; try apply Forall_Forall2, All_Forall; try easy;
      try now apply Forall_All, Forall_True.
  - destruct p. constructor; try assumption.
    apply Forall_Forall2, All_Forall.
    eapply All_impl ; try eassumption.
    intros. split ; auto.
  - eapply All_impl. eassumption. now intros x [? ?].
  - eapply All_impl. eassumption. now intros x [? ?].
Qed.

Lemma eq_term_refl `{checker_flags} φ t : eq_term φ t t.
Proof.
  apply eq_term_upto_univ_refl.
  intro; apply eq_universe'_refl.
Qed.


Lemma leq_term_refl `{checker_flags} φ t : leq_term φ t t.
Proof.
  apply eq_term_upto_univ_refl.
  intro; apply leq_universe'_refl.
Qed.


Lemma eq_universe_leq_universe φ t u : eq_universe φ t u -> leq_universe φ t u.
Proof.
  intros H v Hv. rewrite (H v Hv). apply BinInt.Z.le_refl.
Qed.

Lemma eq_universe'_leq_universe' `{checker_flags} φ t u
  : eq_universe' φ t u -> leq_universe' φ t u.
Proof.
  unfold eq_universe', leq_universe'; destruct check_univs.
  apply eq_universe_leq_universe. intuition.
Qed.


Lemma eq_term_leq_term `{checker_flags} φ t u : eq_term φ t u -> leq_term φ t u.
Proof.
  induction t in u |- * using term_forall_list_ind; simpl; inversion 1;
    subst; constructor; try (now unfold eq_term, leq_term in * );
  try eapply Forall2_impl'. all: try easy.
  now apply All_Forall.
  now apply eq_universe'_leq_universe'.
  all: try (apply Forall_True, eq_universe'_leq_universe').
  eapply Forall_impl. eapply All_Forall. eassumption.
  intros x HH y [? ?]. split ; auto. apply HH. assumption.
  eapply Forall_impl. eapply All_Forall. eassumption.
  cbn. intros x [HH HH'] y [? [? ?]].
  repeat split ; [now apply HH|now apply HH' | assumption].
  eapply Forall_impl. eapply All_Forall. eassumption.
  cbn. intros x [HH HH'] y [? [? ?]].
  repeat split; [now apply HH|now apply HH'|assumption].
Qed.

Lemma eq_term_App `{checker_flags} φ f f' :
  eq_term φ f f' ->
  isApp f = isApp f'.
Proof.
  inversion 1; reflexivity.
Qed.

Lemma eq_term_mkApps `{checker_flags} φ f l f' l' :
  eq_term φ f f' ->
  Forall2 (eq_term φ) l l' ->
  eq_term φ (mkApps f l) (mkApps f' l').
Proof.
  induction l in l', f, f' |- *; intro e; inversion_clear 1.
  - assumption.
  - cbn. eapply IHl. constructor; assumption. assumption.
Qed.

Lemma leq_term_App `{checker_flags} φ f f' :
  leq_term φ f f' ->
  isApp f = isApp f'.
Proof.
  inversion 1; reflexivity.
Qed.

Lemma leq_term_mkApps `{checker_flags} φ f l f' l' :
  leq_term φ f f' ->
  Forall2 (leq_term φ) l l' ->
  leq_term φ (mkApps f l) (mkApps f' l').
Proof.
  induction l in l', f, f' |- *; intro e; inversion_clear 1.
  - assumption.
  - cbn. apply IHl. constructor; assumption. assumption.
Qed.

Lemma leq_term_antisym Σ t u : leq_term Σ t u -> leq_term Σ u t -> eq_term Σ t u.
Proof.
Admitted.

Lemma eq_term_sym Σ t u : eq_term Σ t u -> eq_term Σ u t.
Proof.
Admitted.

Inductive conv_alt `{checker_flags} (Σ : global_context) (Γ : context) : term -> term -> Type :=
| conv_alt_refl t u : eq_term (snd Σ) t u -> Σ ;;; Γ |- t == u
| conv_alt_red_l t u v : red1 (fst Σ) Γ t v -> Σ ;;; Γ |- v == u -> Σ ;;; Γ |- t == u
| conv_alt_red_r t u v : Σ ;;; Γ |- t == v -> red1 (fst Σ) Γ u v -> Σ ;;; Γ |- t == u
where " Σ ;;; Γ |- t == u " := (@conv_alt _ Σ Γ t u) : type_scope.

Lemma red_conv_alt Σ Γ t u : red (fst Σ) Γ t u -> Σ ;;; Γ |- t == u.
Proof.
  intros. apply red_alt in X. apply clos_rt_rt1n_iff in X.
  induction X. constructor. apply eq_term_refl.
  apply clos_rt_rt1n_iff in X. apply red_alt in X.
  econstructor 2; eauto.
Qed.
Hint Resolve red_conv_alt.

Lemma cumul_refl' Σ Γ t : cumul Σ Γ t t.
Proof. apply cumul_refl, leq_term_refl. Qed.

Hint Resolve leq_term_refl cumul_refl' : core.

Lemma cumul_conv_alt Σ Γ t u :
  Σ ;;; Γ |- t <= u -> Σ ;;; Γ |- u <= t -> Σ ;;; Γ |- t == u.
             (* (forall v, Σ ;;; Γ |- u == v -> Σ ;;; Γ |- t == v). *)
Proof.
  intros H. apply cumul_alt in H.
  destruct H as (v & v' & (redv & redv') & leqv).
  intros H'. apply cumul_alt in H'.
  destruct H' as (v0 & v'0 & (redv0 & redv'0) & leqv0).
  (** Needs confluence to show the two redexes can be joined *)
Admitted.



Lemma conv_conv_alt Σ Γ t u : Σ ;;; Γ |- t = u <~> Σ ;;; Γ |- t == u.
Proof.
  split; induction 1. apply cumul_conv_alt in b; auto.
  constructor; constructor. now eapply eq_term_leq_term.
  eapply eq_term_leq_term; now apply eq_term_sym.
  constructor. econstructor 2; eauto. apply IHX.
  econstructor 3. 2:eauto. apply IHX.
  constructor. econstructor 3. 2:eauto. apply IHX.
  econstructor 2; eauto. apply IHX.
Qed.
