(* Distributed under the terms of the MIT license.   *)
From Equations Require Import Equations.
From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import config utils univ.
From PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICWeakeningEnv PCUICWeakening
     PCUICSubstitution PCUICClosed.
Require Import ssreflect ssrbool.
Require Import String.
Require Import LibHypsNaming.
Local Open Scope string_scope.
Set Asymmetric Patterns.

Existing Instance config.default_checker_flags.

Reserved Notation " Σ ;;; Γ |- t == u " (at level 50, Γ, t, u at next level).

Lemma red_step Σ Γ t u v : red1 Σ Γ t u -> red Σ Γ u v -> red Σ Γ t v.
Proof.
  induction 2. econstructor; auto. constructor. apply X.
  econstructor 2; eauto.
Qed.

Require Import Equations.Type.Relation Equations.Type.Relation_Properties.

Lemma red_alt@{i j +} Σ Γ t u : red Σ Γ t u <~> clos_refl_trans@{i j} (red1 Σ Γ) t u.
Proof.
  split. intros H. apply clos_rt_rtn1_iff.
  induction H; econstructor; eauto.
  intros H. apply clos_rt_rtn1_iff in H.
  induction H; econstructor; eauto.
Qed.

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

Inductive conv_alt `{checker_flags} (Σ : global_context) (Γ : context) : term -> term -> Type :=
| conv_alt_refl t u : eq_term (snd Σ) t u = true -> Σ ;;; Γ |- t == u
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

Lemma red1_red (Σ : global_context) Γ t u : red1 (fst Σ) Γ t u -> red (fst Σ) Γ t u.
Proof. econstructor; eauto. constructor. Qed.
Hint Resolve red1_red.

Lemma leq_term_antisym Σ t u : leq_term Σ t u -> leq_term Σ u t -> eq_term Σ t u.
Proof.
Admitted.

Lemma leq_term_refl Σ t : leq_term Σ t t.
Proof. apply eq_term_leq_term, eq_term_refl. Qed.

Lemma eq_term_sym Σ t u : eq_term Σ t u -> eq_term Σ u t.
Proof.
Admitted.

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
