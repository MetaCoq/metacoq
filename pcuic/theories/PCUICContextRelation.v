From Equations Require Import Equations.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICLiftSubst.

From Coq Require Import CRelationClasses.

Ltac pcuic :=
  try repeat red; cbn in *;
   try (solve [ intuition auto; eauto with pcuic || (try lia || congruence) ]).

Lemma context_relation_refl P : (forall Δ x, P Δ Δ x x) ->
  forall Δ, context_relation P Δ Δ.
Proof.
  intros HP.
  induction Δ.
   constructor; auto.
   destruct a as [? [?|] ?]; constructor; auto.
Qed.

Lemma context_relation_trans P :
  (forall Γ Γ' Γ'' x y z,
      context_relation P Γ Γ' ->
      context_relation P Γ' Γ'' ->
      context_relation P Γ Γ'' ->
      P Γ Γ' x y -> P Γ' Γ'' y z -> P Γ Γ'' x z) ->
  Transitive (context_relation P).
Proof.
  intros HP x y z H. induction H in z |- *; auto;
  intros H'; unfold context in *; depelim H';
    try constructor; eauto; hnf in H0; noconf H0; eauto.
Qed.

Lemma context_relation_sym P :
  (forall Γ Γ' x y,
      context_relation P Γ Γ' ->
      context_relation P Γ' Γ ->
      P Γ Γ' x y -> P Γ' Γ y x) ->
  Symmetric (context_relation P).
Proof.
  intros HP x y H.
  induction H; constructor; auto.
Qed.

Lemma context_relation_app {P} Γ Γ' Δ Δ' :
  #|Δ| = #|Δ'| ->
  context_relation P (Γ ,,, Δ) (Γ' ,,, Δ') ->
  context_relation P Γ Γ' * context_relation (fun Δ Δ' => P (Γ ,,, Δ) (Γ' ,,, Δ')) Δ Δ'.
Proof.
  intros H.
  induction Δ in H, Δ', Γ, Γ' |- *;
  destruct Δ'; try discriminate.
  intuition auto. constructor.
  intros H'. simpl in H.
  specialize (IHΔ Γ Γ' Δ' ltac:(lia)).
  depelim H'; specialize (IHΔ H'); intuition auto;
  constructor; auto.
Qed.

Lemma context_relation_app_inv {P} Γ Γ' Δ Δ' :
  #|Δ| = #|Δ'| ->
  context_relation P Γ Γ' -> context_relation (fun Δ Δ' => P (Γ ,,, Δ) (Γ' ,,, Δ')) Δ Δ' ->
  context_relation P (Γ ,,, Δ) (Γ' ,,, Δ').
Proof.
  intros H.
  induction 2; simpl; auto.
  constructor. apply IHX0. simpl in H. lia.
  apply p.
  constructor. apply IHX0. simpl in H; lia.
  apply p.
Qed.
