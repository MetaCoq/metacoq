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
Require Import Equations.Prop.DepElim.


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
  induction X. reflexivity.
  econstructor 2; eauto.
Qed.

Lemma red_cumul_inv `{cf : checker_flags} {Σ : global_env_ext} {Γ t u} :
  red Σ Γ t u ->
  Σ ;;; Γ |- u <= t.
Proof.
  intros. apply red_alt in X. apply clos_rt_rt1n in X.
  induction X. reflexivity.
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

Lemma red_conv {cf:checker_flags} (Σ : global_env_ext) Γ t u :
  red Σ Γ t u -> Σ ;;; Γ |- t = u.
Proof.
  intros. apply red_alt in X. apply clos_rt_rt1n in X.
  induction X. reflexivity.
  econstructor 2; eauto.
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

Lemma cumul2_conv {cf:checker_flags} Σ Γ t u :
  (Σ ;;; Γ |- t <= u) * (Σ ;;; Γ |- u <= t) -> Σ ;;; Γ |- t = u.
Proof.
Admitted.


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

Instance conv_sym `{cf : checker_flags} (Σ : global_env_ext) Γ : Symmetric (conv Σ Γ).
Proof.
  intros t u; induction 1.
  - eapply eq_term_sym in e; now constructor.
  - eapply red_conv_conv_inv. eapply red1_red in r. eauto. eauto.
  - eapply red_conv_conv. eapply red1_red in r. eauto. eauto.
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
  - cbn. constructor. apply conv_cumul. auto. now apply conv_sym.
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
