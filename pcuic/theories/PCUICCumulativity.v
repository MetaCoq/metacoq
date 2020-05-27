(* Distributed under the terms of the MIT license.   *)

From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst
     PCUICEquality PCUICTyping PCUICBasicStrengthening PCUICReduction
     PCUICEtaReduction PCUICPosition PCUICInduction PCUICWeakening.
Local Open Scope string_scope.
Set Asymmetric Patterns.
Require Import ssrbool List CRelationClasses Arith Lia.
From Equations.Type Require Import Relation Relation_Properties.
From Equations.Prop Require Import DepElim.

Import ListNotations. Open Scope list_scope.

Set Default Goal Selector "!".

Reserved Notation " Σ ;;; Γ |- t == u " (at level 50, Γ, t, u at next level).


(** ** Properties of Cumulativity relying on eta-postponment
       but not on confluence ** *)


(* todo move *)
Lemma eta_cumul_cumul {cf:checker_flags} {Σ : global_env_ext} {Γ t u v} :
  eta t u -> Σ ;;; Γ |- u <= v -> Σ ;;; Γ |- t <= v.
Proof.
  induction 1 in v |- *; auto.
  intro. econstructor 4; eassumption.
Qed.

Lemma eta_cumul_cumul_inv {cf:checker_flags} {Σ : global_env_ext} {Γ t u v} :
  eta t v -> Σ ;;; Γ |- u <= v -> Σ ;;; Γ |- u <= t.
Proof.
  induction 1 in u |- *; auto.
  intro. econstructor 5; eassumption.
Qed.

Lemma beta_eta_cumul_cumul {cf:checker_flags} {Σ : global_env_ext} {Γ t u v} :
  beta_eta Σ Γ t u -> Σ ;;; Γ |- u <= v -> Σ ;;; Γ |- t <= v.
Proof.
  induction 1 in v |- *; auto.
  destruct r; [eauto using red_cumul_cumul|].
  apply eta_cumul_cumul; eta.
Qed.

Lemma beta_eta_cumul_cumul_inv {cf:checker_flags} {Σ : global_env_ext} {Γ t u v} :
  beta_eta Σ Γ t v -> Σ ;;; Γ |- u <= v -> Σ ;;; Γ |- u <= t.
Proof.
  induction 1 in u |- *; auto.
  destruct r; [eauto using red_cumul_cumul_inv|].
  apply eta_cumul_cumul_inv; eta.
Qed.


Lemma cumul_alt `{cf : checker_flags} Σ Γ t u :
  Σ ;;; Γ |- t <= u <~>
  ∑ t' u' v, beta_eta Σ Γ t t' ×
             beta_eta Σ Γ u u' ×
             leq_term Σ t' v ×
             upto_domain v u'.
Proof.
  split.
  - induction 1.
    + exists t, v, u; beta_eta.
    + destruct IHX as (t' & u' & v0 & ? & ? & ? & ?).
      exists t', u', v0; beta_eta.
    + destruct IHX as (t' & u' & v0 & ? & ? & ? & ?).
      exists t', u', v0; beta_eta.
    + destruct IHX as (t' & u' & v0 & ? & ? & ? & ?).
      exists t', u', v0; beta_eta.
    + destruct IHX as (t' & u' & v0 & ? & ? & ? & ?).
      exists t', u', v0; beta_eta.
  - intros (t' & u' & ? & ? & ? & ? & ?).
    eapply beta_eta_cumul_cumul; tea.
    eapply beta_eta_cumul_cumul_inv; tea.
    econstructor; tea.
Qed.

(* Lemma cumul_alt `{cf : checker_flags} Σ Γ t u : *)
(*   Σ ;;; Γ |- t <= u <~> *)
(*   ∑ t' t'' u' u'' v, red Σ Γ t t' × *)
(*                      eta t' t'' × *)
(*                      red Σ Γ u u' × *)
(*                      eta u' u'' × *)
(*                      leq_term Σ t'' v × *)
(*                      upto_domain v u''. *)
(* Proof. *)
(*   split. *)
(*   - induction 1. *)
(*     + exists t, t, v, v, u. intuition auto; reflexivity. *)
(*     + destruct IHX as (t' & t'' & u' & u'' & v0 & ? & ? & ? & ? & ? & ?). *)
(*       exists t', t'', u', u'', v0. intuition auto. eapply red_step; tea. *)
(*     + destruct IHX as (t' & t'' & u' & u'' & v0 & ? & ? & ? & ? & ? & ?). *)
(*       exists t', t'', u', u'', v0. intuition auto. eapply red_step; tea. *)
(*     + todoeta.  (* eta postponment *) *)
(*     + todoeta.  (* eta postponment *) *)
(*   - intros (t' & t'' & u' & u'' & ? & ? & ? & ? & ? & ? & ?). *)
(*     eapply red_cumul_cumul; tea. *)
(*     eapply red_cumul_cumul_inv; tea. *)
(*     eapply eta_cumul_cumul; tea. *)
(*     eapply eta_cumul_cumul_inv; tea. *)
(*     econstructor; tea. *)
(* Qed. *)


Lemma upto_domain_eq_term_com {cf:checker_flags} {φ t u v} :
  upto_domain t u ->
  eq_term φ u v ->
  ∑ u', eq_term φ t u' × upto_domain u' v.
Proof.
  induction t in u, v |- * using term_forall_list_ind;
    intro e; invs e; intro e'; invs e'.
  all: try (edestruct IHt as [? [? ?]]; tea).
  5,7-15: try (edestruct IHt1 as [? [? ?]]; tea).
  all: try (edestruct IHt2 as [? [? ?]]; tea).
  all: try (edestruct IHt3 as [? [? ?]]; tea).
  all: try (eexists; split; econstructor; tea; fail).
  - enough (∑ l', All2 (eq_term_upto_univ (eq_universe φ) (eq_universe φ)) l l'
                  × All2 upto_domain l' args'0) as XX. {
      destruct XX as [? [? ?]]; eexists; split; econstructor; eassumption. }
    induction X0 in X, args'0, X1 |- *; invs X; invs X1.
    + exists []; split; constructor.
    + edestruct X2 as [? [? ?]]; tea.
      edestruct IHX0 as [? [? ?]]; tea.
      eexists (_ :: _); split; econstructor; tea.
  - enough (∑ l', All2 (fun x0 y => x0.1 = y.1
            × eq_term_upto_univ (eq_universe φ) (eq_universe φ) x0.2 y.2) l l'
            × All2 (fun x0 y  => x0.1 = y.1 × upto_domain x0.2 y.2) l' brs'0) as XX. {
      destruct XX as [? [? ?]]; eexists; split; econstructor; tea. }
    clear -X X2 X5.
    induction X2 in X, brs'0, X5 |- *; invs X; invs X5.
    + exists []; split; constructor.
    + edestruct X0 as [A [? ?]]; [intuition eauto ..|].
      edestruct IHX2 as [B [? ?]]; tea.
      eexists ((_, A) :: B); split; econstructor; rdest; tea.
  - enough (∑ l', All2 (fun x y =>
     (eq_term_upto_univ (eq_universe φ) (eq_universe φ) (dtype x) (dtype y)
      × eq_term_upto_univ (eq_universe φ) (eq_universe φ) (dbody x) (dbody y))
     × rarg x = rarg y) m l'
            × All2 (fun x y  => upto_domain (dtype x) (dtype y)
    × upto_domain (dbody x) (dbody y) × rarg x = rarg y) l' mfix'0) as XX. {
      destruct XX as [? [? ?]]; eexists; split; econstructor; tea. }
    clear -X X0 X1.
    induction X0 in X, mfix'0, X1 |- *; invs X; invs X1.
    + exists []; split; constructor.
    + edestruct X2 as [[A [? ?]] [B [? ?]]]; [intuition eauto ..|].
      edestruct IHX0 as [C [? ?]]; tea.
      eexists (mkdef term _ A B _ :: C); split; econstructor; rdest; tea.
  - enough (∑ l', All2 (fun x y =>
     (eq_term_upto_univ (eq_universe φ) (eq_universe φ) (dtype x) (dtype y)
      × eq_term_upto_univ (eq_universe φ) (eq_universe φ) (dbody x) (dbody y))
     × rarg x = rarg y) m l'
            × All2 (fun x y  => upto_domain (dtype x) (dtype y)
    × upto_domain (dbody x) (dbody y) × rarg x = rarg y) l' mfix'0) as XX. {
      destruct XX as [? [? ?]]; eexists; split; econstructor; tea. }
    clear -X X0 X1.
    induction X0 in X, mfix'0, X1 |- *; invs X; invs X1.
    + exists []; split; constructor.
    + edestruct X2 as [[A [? ?]] [B [? ?]]]; [intuition eauto ..|].
      edestruct IHX0 as [C [? ?]]; tea.
      eexists (mkdef term _ A B _ :: C); split; econstructor; rdest; tea.
  (* lambda *)
  - eexists; split; econstructor; tea. reflexivity.
    Unshelve.
    all: constructor.
Qed.

Lemma conv_cumul2 {cf:checker_flags} Σ Γ t u :
  Σ ;;; Γ |- t = u -> (Σ ;;; Γ |- t <= u) * (Σ ;;; Γ |- u <= t).
Proof.
  induction 1.
  - split.
    + econstructor; try apply eq_term_leq_term; eassumption.
    + symmetry in e. symmetry in u0.
      destruct (upto_domain_eq_term_com u0 e) as [? p].
      econstructor; try apply p.
      apply eq_term_leq_term; apply p.
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

Lemma cumul2_conv {cf:checker_flags} Σ Γ t u :
  (Σ ;;; Γ |- t <= u) * (Σ ;;; Γ |- u <= t) -> Σ ;;; Γ |- t = u.
Proof.
  intros [H1 H2]; revert H2. induction H1.
Abort.


Instance conv_sym `{cf : checker_flags} (Σ : global_env_ext) Γ :
  Symmetric (conv Σ Γ).
Proof.
  intros t u X. induction X.
  - symmetry in e. symmetry in u0.
    destruct (upto_domain_eq_term_com u0 e).
    econstructor; apply p.
  - eapply red_conv_conv_inv.
    + eapply red1_red in r. eauto.
    + eauto.
  - eapply red_conv_conv.
    + eapply red1_red in r. eauto.
    + eauto.
  - eapply conv_eta_r. all: eassumption.
  - eapply conv_eta_l. all: eassumption.
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
  - cbn. eapply IHl.
    + constructor; assumption.
    + assumption.
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
  - cbn. apply IHl.
    + constructor; try assumption.
    + assumption.
Qed.

Hint Resolve leq_term_refl cumul_refl' : core.
Hint Resolve red_conv : core.


Lemma cumul_App_l {cf:checker_flags} {Σ Γ f g x}:
  Σ ;;; Γ |- f <= g -> Σ ;;; Γ |- tApp f x <= tApp g x.
Proof.
  (* intro H. *)
  (* cut (H = H); [|reflexivity]. *)
  (* induction H. *)
  induction 1;
    [econstructor 1|econstructor 2|econstructor 3|econstructor 4|econstructor 5];
    tea; econstructor; tea; try reflexivity .
Defined.
