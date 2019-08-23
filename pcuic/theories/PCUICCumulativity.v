(* Distributed under the terms of the MIT license.   *)
From Equations Require Import Equations.
From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From MetaCoq.Template Require Import config utils AstUtils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICUnivSubst PCUICEquality PCUICTyping PCUICWeakeningEnv
     PCUICWeakening PCUICClosed PCUICReduction.
Require Import ssreflect ssrbool.
Require Import String.
From MetaCoq Require Import LibHypsNaming.
Local Open Scope string_scope.
Set Asymmetric Patterns.
Require Import CRelationClasses.
Require Import Equations.Type.Relation Equations.Type.Relation_Properties.

Reserved Notation " Σ ;;; Γ |- t == u " (at level 50, Γ, t, u at next level).

Lemma cumul_alt `{cf : checker_flags} Σ Γ t u :
  Σ ;;; Γ |- t <= u <~> { v & { v' & (red Σ Γ t v * red Σ Γ u v' * leq_term (global_ext_constraints Σ) v v')%type } }.
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

Lemma cumul_refl' {cf : checker_flags} Σ Γ t : Σ ;;; Γ |- t <= t.
Proof.
  eapply cumul_alt. exists t, t; intuition eauto. eapply leq_term_refl.
Qed.

Lemma conv_refl' {cf : checker_flags} Σ Γ t : Σ ;;; Γ |- t = t.
Proof.
  split; apply cumul_refl'.
Qed.

Lemma red_cumul `{cf : checker_flags} {Σ : global_env_ext} {Γ t u} :
  red Σ Γ t u ->
  Σ ;;; Γ |- t <= u.
Proof.
  intros. apply red_alt in X. apply clos_rt_rt1n in X.
  induction X. apply cumul_refl'.
  econstructor 2; eauto.
Qed.

Lemma red_cumul_inv `{cf : checker_flags} {Σ : global_env_ext} {Γ t u} :
  red Σ Γ t u ->
  Σ ;;; Γ |- u <= t.
Proof.
  intros. apply red_alt in X. apply clos_rt_rt1n in X.
  induction X. apply cumul_refl'.
  econstructor 3; eauto.
Qed.

Lemma red_cumul_cumul `{cf : checker_flags} {Σ : global_env_ext} {Γ t u v} :
  red Σ Γ t u -> Σ ;;; Γ |- u <= v -> Σ ;;; Γ |- t <= v.
Proof.
  intros. apply red_alt in X. apply clos_rt_rt1n in X.
  induction X. auto.
  econstructor 2; eauto.
Qed.

Lemma red_cumul_cumul_inv `{cf : checker_flags} {Σ : global_env_ext} {Γ t u v} :
  red Σ Γ t v -> Σ ;;; Γ |- u <= v -> Σ ;;; Γ |- u <= t.
Proof.
  intros. apply red_alt in X. apply clos_rt_rt1n in X.
  induction X. auto.
  econstructor 3. eapply IHX. eauto. eauto.
Qed.

Lemma red_conv {cf:checker_flags} (Σ : global_env_ext) Γ t u : red Σ Γ t u -> Σ ;;; Γ |- t = u.
Proof.
  intros. split; [apply red_cumul|apply red_cumul_inv]; auto.
Qed.

Lemma conv_cumul {cf:checker_flags} Σ Γ t u :
  Σ ;;; Γ |- t = u -> (Σ ;;; Γ |- t <= u) * (Σ ;;; Γ |- u <= t).
Proof. trivial. Qed.

(* todo: move *)
Lemma All_All2_refl {A : Type} {R} {l : list A} : All (fun x : A => R x x) l -> All2 R l l.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma eq_term_App `{checker_flags} φ f f' :
  eq_term φ f f' ->
  isApp f = isApp f'.
Proof.
  inversion 1; reflexivity.
Qed.

Lemma eq_term_mkApps `{checker_flags} φ f l f' l' :
  eq_term φ f f' ->
  All2 (eq_term φ) l l' ->
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
  All2 (eq_term φ) l l' ->
  leq_term φ (mkApps f l) (mkApps f' l').
Proof.
  induction l in l', f, f' |- *; intro e; inversion_clear 1.
  - assumption.
  - cbn. apply IHl. constructor; try assumption. assumption.
Qed.

Inductive conv_alt `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
| conv_alt_refl t u : eq_term (global_ext_constraints Σ) t u -> Σ ;;; Γ |- t == u
| conv_alt_red_l t u v : red1 Σ Γ t v -> Σ ;;; Γ |- v == u -> Σ ;;; Γ |- t == u
| conv_alt_red_r t u v : Σ ;;; Γ |- t == v -> red1 (fst Σ) Γ u v -> Σ ;;; Γ |- t == u
where " Σ ;;; Γ |- t == u " := (@conv_alt _ Σ Γ t u) : type_scope.

Lemma red_conv_alt `{cf : checker_flags} Σ Γ t u :
  red (fst Σ) Γ t u ->
  Σ ;;; Γ |- t == u.
Proof.
  intros. apply red_alt in X. apply clos_rt_rt1n_iff in X.
  induction X. constructor. apply eq_term_refl.
  apply clos_rt_rt1n_iff in X. apply red_alt in X.
  econstructor 2; eauto.
Qed.
Hint Resolve red_conv_alt.

Hint Resolve leq_term_refl cumul_refl' : core.

Lemma red_conv_conv `{cf : checker_flags} Σ Γ t u v :
  red (fst Σ) Γ t u -> Σ ;;; Γ |- u == v -> Σ ;;; Γ |- t == v.
Proof.
  intros. apply red_alt in X. apply clos_rt_rt1n_iff in X.
  induction X; auto.
  econstructor 2; eauto.
Qed.

Lemma red_conv_conv_inv `{cf : checker_flags} Σ Γ t u v :
  red (fst Σ) Γ t u -> Σ ;;; Γ |- v == u -> Σ ;;; Γ |- v == t.
Proof.
  intros. apply red_alt in X. apply clos_rt_rt1n_iff in X.
  induction X; auto.
  now econstructor 3; [eapply IHX|]; eauto.
Qed.

Lemma conv_alt_sym `{cf : checker_flags} (Σ : global_env_ext) Γ t u :
  wf Σ ->
  Σ ;;; Γ |- t == u -> Σ ;;; Γ |- u == t.
Proof.
  intros wfΣ X.
  induction X.
  - eapply eq_term_sym in e; now constructor.
  - eapply red_conv_conv_inv. eapply red1_red in r. eauto. eauto.
  - eapply red_conv_conv. eapply red1_red in r. eauto. eauto.
Qed.

Lemma conv_alt_red {cf : checker_flags} {Σ : global_env_ext} {Γ : context} {t u : term} :
  Σ;;; Γ |- t == u <~> (∑ v v' : term, (red Σ Γ t v × red Σ Γ u v') × eq_term (global_ext_constraints Σ) v v').
Proof.
  split. induction 1. exists t, u; intuition auto.
  destruct IHX as [? [? [? ?]]].
  exists x, x0; intuition auto. eapply red_step; eauto.
  destruct IHX as [? [? [? ?]]].
  exists x, x0; intuition auto. eapply red_step; eauto.
  intros.
  destruct X as [? [? [[? ?] ?]]].
  eapply red_conv_conv; eauto.
  eapply red_conv_conv_inv; eauto. now constructor.
Qed.

Lemma conv_alt_cumul `{cf : checker_flags} (Σ : global_env_ext) Γ t u : wf Σ ->
  Σ ;;; Γ |- t == u -> Σ ;;; Γ |- t <= u.
Proof.
  intros wfΣ H.
  apply conv_alt_red in H as [v [v' [[l r] eq]]].
  apply cumul_alt.
  exists v, v'; intuition auto. now eapply eq_term_leq_term.
Qed.

Lemma conv_alt_conv `{cf : checker_flags} (Σ : global_env_ext) Γ t u : wf Σ ->
  Σ ;;; Γ |- t == u -> Σ ;;; Γ |- t = u.
Proof.
  intros wfΣ H. split. now apply conv_alt_cumul.
  apply conv_alt_sym in H; auto. now apply conv_alt_cumul.
Qed.

Inductive conv_pb :=
| Conv
| Cumul.

Definition conv `{cf : checker_flags} leq Σ Γ u v :=
  match leq with
  | Conv => ∥ Σ ;;; Γ |- u == v ∥
  | Cumul => ∥ Σ ;;; Γ |- u <= v ∥
  end.

Lemma conv_conv_l `{cf : checker_flags} :
  forall (Σ : global_env_ext) leq Γ u v, wf Σ ->
      Σ ;;; Γ |- u == v ->
      conv leq Σ Γ u v.
Proof.
  intros Σ [] Γ u v h.
  - cbn. constructor. assumption.
  - cbn. constructor. now apply conv_alt_cumul.
Qed.

Lemma conv_conv_r `{cf : checker_flags} :
  forall (Σ : global_env_ext) leq Γ u v, wf Σ ->
      Σ ;;; Γ |- u == v ->
      conv leq Σ Γ v u.
Proof.
  intros Σ [] Γ u v wfΣ h.
  - cbn. constructor. apply conv_alt_sym; auto.
  - cbn. constructor. apply conv_alt_cumul. auto. now apply conv_alt_sym.
Qed.

Lemma cumul_App_l `{cf : checker_flags} :
  forall {Σ Γ f g x},
    Σ ;;; Γ |- f <= g ->
    Σ ;;; Γ |- tApp f x <= tApp g x.
Proof.
  intros Σ Γ f g x h.
  induction h.
  - eapply cumul_refl. constructor.
    + assumption.
    + apply eq_term_refl.
  - eapply cumul_red_l ; try eassumption.
    econstructor. assumption.
  - eapply cumul_red_r ; try eassumption.
    econstructor. assumption.
Qed.
