(* Distributed under the terms of the MIT license.   *)
From Equations Require Import Equations.
From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import config utils AstUtils univ.
From PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
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

Lemma eq_term_refl `{checker_flags} φ t : eq_term φ t t.
Proof.
  induction t using term_forall_list_ind; simpl; try reflexivity; try discriminate;
    try (rewrite -> ?IHt1, ?IHt2, ?IHt3; reflexivity).

  - apply Nat.eqb_refl.
  - apply eq_string_refl.
  - apply Nat.eqb_refl.
  - rewrite /eq_evar eq_nat_refl.
    simpl. induction H0; simpl; auto. now rewrite p IHAll.
  - apply eq_universe_refl.
  - unfold eq_constant. rewrite eq_string_refl.
    apply eq_universe_instance_refl.
  - rewrite eq_ind_refl. apply eq_universe_instance_refl.
  - rewrite eq_ind_refl. rewrite /eq_nat Nat.eqb_refl. apply eq_universe_instance_refl.
  - destruct p. simpl.
    rewrite eq_ind_refl eq_nat_refl IHt1 IHt2.
    simpl. induction l.
    reflexivity.
    simpl. destruct a. inv X. simpl in H0. rewrite H0.
    rewrite IHl; auto.
  - now rewrite eq_projection_refl IHt.
  - rewrite eq_nat_refl.
    induction m. reflexivity.
    inv X. intuition.
    simpl. rewrite a0 b. simpl. apply H0.
  - rewrite Nat.eqb_refl.
    induction m. reflexivity.
    inv X. intuition.
    simpl. rewrite a0 b. simpl. apply H0.
Qed.

Lemma eq_term_leq_term `{checker_flags} φ t u : eq_term φ t u = true -> leq_term φ t u = true.
Proof.
  induction t in u |- * using term_forall_list_ind; simpl; intros; auto; try reflexivity; try discriminate;
    try (merge_All; close_Forall; intuition auto);
    try (rewrite -> ?IHt1, ?IHt2, ?IHt3; reflexivity).

  - destruct u; auto. now apply eq_universe_leq_universe.
  - destruct u; try discriminate.
    rewrite -> andb_true_iff in *. intuition.
  - destruct u; try discriminate.
    rewrite -> andb_true_iff in *. intuition.
  - destruct u; try discriminate.
    rewrite -> andb_true_iff in *. intuition.
Qed.

Lemma eq_term_App `{checker_flags} φ f f' :
  eq_term φ f f' ->
  isApp f = isApp f'.
Proof.
  destruct f, f'; simpl; try congruence.
  destruct p; congruence.
Qed.

Lemma eq_term_mkApps `{checker_flags} φ f l f' l' :
  eq_term φ f f' ->
  forallb2 (eq_term φ) l l' ->
  eq_term φ (mkApps f l) (mkApps f' l').
Proof.
  induction l in f, f', l' |- *; destruct l'; try (simpl; congruence).
  intros.
  apply andb_and in H1 as [Ht Hl].
  apply (IHl (tApp f a) (tApp f' t) l').
  simpl; now rewrite H0 Ht.
  apply Hl.
Qed.

Lemma leq_term_mkApps `{checker_flags} φ f l f' l' :
  eq_term φ f f' ->
  forallb2 (eq_term φ) l l' ->
  leq_term φ (mkApps f l) (mkApps f' l').
Proof.
  induction l in f, f', l' |- *; destruct l'; try (simpl; congruence).
  intros. simpl. now apply eq_term_leq_term.
  intros H0 H1. apply andb_and in H1 as [Ht Hl].
  apply (IHl (tApp f a) (tApp f' t) l').
  simpl; now rewrite H0 Ht.
  apply Hl.
Qed.

Lemma leq_term_antisym Σ t u : leq_term Σ t u -> leq_term Σ u t -> eq_term Σ t u.
Proof.
Admitted.

Lemma leq_term_refl Σ t : leq_term Σ t t.
Proof. apply eq_term_leq_term, eq_term_refl. Qed.

Lemma eq_term_sym Σ t u : eq_term Σ t u -> eq_term Σ u t.
Proof.
Admitted.

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
