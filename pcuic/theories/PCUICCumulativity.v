(* Distributed under the terms of the MIT license.   *)

From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst
     PCUICEquality PCUICTyping
     PCUICReduction PCUICPosition.
Local Open Scope string_scope.
Set Asymmetric Patterns.
Require Import CRelationClasses.
Require Import Equations.Type.Relation Equations.Type.Relation_Properties.

Set Default Goal Selector "!".

Reserved Notation " Σ ;;; Γ |- t == u " (at level 50, Γ, t, u at next level).

Lemma cumul_alt `{cf : checker_flags} Σ Γ t u :
  Σ ;;; Γ |- t <= u <~> { v & { v' & (red Σ Γ t v * red Σ Γ u v' * 
  leq_term Σ (global_ext_constraints Σ) v v')%type } }.
Proof.
  split.
  - induction 1.
    + exists t, u. intuition auto.
    + destruct IHX as (v' & v'' & (redv & redv') & leqv).
      exists v', v''. intuition auto. now eapply red_step.
    + destruct IHX as (v' & v'' & (redv & redv') & leqv).
      exists v', v''. intuition auto. now eapply red_step.
    + todoeta.
    + todoeta.
  - intros [v [v' [[redv redv'] Hleq]]]. apply red_alt in redv. apply red_alt in redv'.
    apply clos_rt_rt1n in redv.
    apply clos_rt_rt1n in redv'.
    induction redv.
    * induction redv'.
    ** constructor; auto.
    ** econstructor 3; eauto.
    * econstructor 2; eauto.
Qed.

Instance cumul_refl' {cf:checker_flags} Σ Γ : Reflexive (cumul Σ Γ).
Proof.
  intro; constructor. reflexivity.
Qed.

Instance conv_refl' {cf:checker_flags} Σ Γ : Reflexive (conv Σ Γ).
Proof.
  intro; constructor. reflexivity.
Qed.

Lemma red_cumul `{cf : checker_flags} {Σ : global_env_ext} {Γ t u} :
  red Σ Γ t u ->
  Σ ;;; Γ |- t <= u.
Proof.
  intros. apply red_alt in X. apply clos_rt_rt1n in X.
  induction X.
  - apply cumul_refl'.
  - econstructor 2. all: eauto.
Qed.

Lemma red_cumul_inv `{cf : checker_flags} {Σ : global_env_ext} {Γ t u} :
  red Σ Γ t u ->
  Σ ;;; Γ |- u <= t.
Proof.
  intros. apply red_alt in X. apply clos_rt_rt1n in X.
  induction X.
  - apply cumul_refl'.
  - econstructor 3. all: eauto.
Qed.

Lemma red_cumul_cumul `{cf : checker_flags} {Σ : global_env_ext} {Γ t u v} :
  red Σ Γ t u -> Σ ;;; Γ |- u <= v -> Σ ;;; Γ |- t <= v.
Proof.
  intros. apply red_alt in X. apply clos_rt_rt1n in X.
  induction X. 1: auto.
  econstructor 2; eauto.
Qed.

Lemma red_cumul_cumul_inv `{cf : checker_flags} {Σ : global_env_ext} {Γ t u v} :
  red Σ Γ t v -> Σ ;;; Γ |- u <= v -> Σ ;;; Γ |- u <= t.
Proof.
  intros. apply red_alt in X. apply clos_rt_rt1n in X.
  induction X. 1: auto.
  econstructor 3.
  - eapply IHX. eauto.
  - eauto.
Qed.


Lemma conv_cumul2 {cf:checker_flags} Σ Γ t u :
  Σ ;;; Γ |- t = u -> (Σ ;;; Γ |- t <= u) * (Σ ;;; Γ |- u <= t).
Proof.
  induction 1.
  - split; constructor; now apply eq_term_leq_term.
  - destruct IHX as [H1 H2]. split.
    * econstructor 2; eassumption.
    * econstructor 3; eassumption.
  - destruct IHX as [H1 H2]. split.
    * econstructor 3; eassumption.
    * econstructor 2; eassumption.
  - destruct IHX as [H1 H2]. split.
    * econstructor 4; eassumption.
    * econstructor 5; eassumption.
  - destruct IHX as [H1 H2]. split.
    * econstructor 5; eassumption.
    * econstructor 4; eassumption.
Qed.

Lemma conv_cumul {cf:checker_flags} Σ Γ t u :
  Σ ;;; Γ |- t = u -> Σ ;;; Γ |- t <= u.
Proof.
  intro H; now apply conv_cumul2 in H.
Qed.

Lemma conv_cumul_inv {cf:checker_flags} Σ Γ t u :
  Σ ;;; Γ |- u = t -> Σ ;;; Γ |- t <= u.
Proof.
  intro H; now apply conv_cumul2 in H.
Qed.

Lemma red_conv {cf:checker_flags} (Σ : global_env_ext) Γ t u
  : red Σ Γ t u -> Σ ;;; Γ |- t = u.
Proof.
  intros H%red_alt%clos_rt_rt1n_iff.
  induction H.
  - reflexivity.
  - econstructor 2; eauto. 
Qed.

Hint Resolve red_conv : core.

Lemma eq_term_App `{checker_flags} Σ φ f f' :
  eq_term Σ φ f f' ->
  isApp f = isApp f'.
Proof.
  inversion 1; reflexivity.
Qed.

Lemma eq_term_mkApps `{checker_flags} Σ φ f l f' l' :
  eq_term Σ φ f f' ->
  All2 (eq_term Σ φ) l l' ->
  eq_term Σ φ (mkApps f l) (mkApps f' l').
Proof.
  induction l in l', f, f' |- *; intro e; inversion_clear 1.
  - assumption.
  - cbn. eapply IHl.
    + constructor; assumption.
    + assumption.
Qed.

Lemma leq_term_App `{checker_flags} Σ φ f f' :
  leq_term Σ φ f f' ->
  isApp f = isApp f'.
Proof.
  inversion 1; reflexivity.
Qed.

Lemma leq_term_mkApps `{checker_flags} Σ φ f l f' l' :
  leq_term Σ φ f f' ->
  All2 (eq_term Σ φ) l l' ->
  leq_term Σ φ (mkApps f l) (mkApps f' l').
Proof.
  induction l in l', f, f' |- *; intro e; inversion_clear 1.
  - assumption.
  - cbn. apply IHl.
    + constructor; try assumption.
    + assumption.
Qed.

Hint Resolve leq_term_refl cumul_refl' : core.

Lemma red_conv_conv `{cf : checker_flags} Σ Γ t u v :
  red (fst Σ) Γ t u -> Σ ;;; Γ |- u = v -> Σ ;;; Γ |- t = v.
Proof.
  intros. apply red_alt in X. apply clos_rt_rt1n_iff in X.
  induction X; auto.
  econstructor 2; eauto.
Qed.

Lemma red_conv_conv_inv `{cf : checker_flags} Σ Γ t u v :
  red (fst Σ) Γ t u -> Σ ;;; Γ |- v = u -> Σ ;;; Γ |- v = t.
Proof.
  intros. apply red_alt in X. apply clos_rt_rt1n_iff in X.
  induction X; auto.
  now econstructor 3; [eapply IHX|]; eauto.
Qed.

Instance conv_sym `{cf : checker_flags} (Σ : global_env_ext) Γ :
  Symmetric (conv Σ Γ).
Proof.
  intros t u X. induction X.
  - eapply eq_term_sym in e; now constructor.
  - eapply red_conv_conv_inv.
    + eapply red1_red in r. eauto.
    + eauto.
  - eapply red_conv_conv.
    + eapply red1_red in r. eauto.
    + eauto.
  - eapply conv_eta_r. all: eassumption.
  - eapply conv_eta_l. all: eassumption.
Qed.

Lemma conv_alt_red {cf : checker_flags} {Σ : global_env_ext} {Γ : context} {t u : term} :
  Σ;;; Γ |- t = u <~> (∑ v v' : term, (red Σ Γ t v × red Σ Γ u v') × 
    eq_term Σ (global_ext_constraints Σ) v v').
Proof.
  split.
  - induction 1.
    * exists t, u; intuition auto.
    * destruct IHX as [? [? [? ?]]].
      exists x, x0; intuition auto. eapply red_step; eauto.
    * destruct IHX as [? [? [? ?]]].
      exists x, x0; intuition auto. eapply red_step; eauto.
    * todoeta.
    * todoeta.
  - destruct 1 as [? [? [[? ?] ?]]].
    eapply red_conv_conv; eauto.
    eapply red_conv_conv_inv; eauto. now constructor.
Qed.

Inductive conv_pb :=
| Conv
| Cumul.

Definition conv_cum `{cf : checker_flags} leq Σ Γ u v :=
  match leq with
  | Conv => ∥ Σ ;;; Γ |- u = v ∥
  | Cumul => ∥ Σ ;;; Γ |- u <= v ∥
  end.

Lemma conv_conv_cum_l `{cf : checker_flags} :
  forall (Σ : global_env_ext) leq Γ u v, wf Σ ->
      Σ ;;; Γ |- u = v ->
      conv_cum leq Σ Γ u v.
Proof.
  intros Σ [] Γ u v h.
  - cbn. constructor. assumption.
  - cbn. constructor. now apply conv_cumul.
Qed.

Lemma conv_conv_cum_r `{cf : checker_flags} :
  forall (Σ : global_env_ext) leq Γ u v, wf Σ ->
      Σ ;;; Γ |- u = v ->
      conv_cum leq Σ Γ v u.
Proof.
  intros Σ [] Γ u v wfΣ h.
  - cbn. constructor. apply conv_sym; auto.
  - cbn. constructor. apply conv_cumul.
    now apply conv_sym.
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
  - eapply cumul_eta_l. 2: eassumption.
    destruct e as [na [A [f [π [? ?]]]]]. subst.
    exists na, A, f, (stack_cat π (App x ε)).
    rewrite 2!zipc_stack_cat. cbn. intuition reflexivity.
  - eapply cumul_eta_r. 1: eassumption.
    destruct e as [na [A [f [π [? ?]]]]]. subst.
    exists na, A, f, (stack_cat π (App x ε)).
    rewrite 2!zipc_stack_cat. cbn. intuition reflexivity.
Qed.
