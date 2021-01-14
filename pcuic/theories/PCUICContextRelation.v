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

Lemma context_relation_app_inv {P} Γ Γ' Δ Δ' :
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

Lemma context_relation_app_inv_l {P} Γ Γ' Δ Δ' :
  #|Γ| = #|Γ'| ->
  context_relation P (Γ ,,, Δ) (Γ' ,,, Δ') ->
  context_relation P Γ Γ' * context_relation (fun Δ Δ' => P (Γ ,,, Δ) (Γ' ,,, Δ')) Δ Δ'.
Proof.
  intros H.
  induction Δ in H, Δ', Γ, Γ' |- *;
  destruct Δ'; try discriminate.
  intuition auto. constructor.
  intros H'; generalize (context_relation_length H'). simpl. len. lia.
  intros H'; generalize (context_relation_length H'). simpl. len. lia.
  intros H'. simpl in H.
  specialize (IHΔ Γ Γ' Δ' ltac:(lia)).
  depelim H'; specialize (IHΔ H'); intuition auto;
  constructor; auto.
Qed.

Lemma context_relation_app {P} Γ Γ' Δ Δ' :
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

Lemma context_relation_impl_onctx P P' Γ Δ Q :  
  onctx Q Γ ->
  context_relation P Γ Δ ->
  (forall Γ Δ d d', 
    context_relation P Γ Δ -> 
    P Γ Δ d d' ->
    ondecl Q d ->
    P' Γ Δ d d') ->
  context_relation P' Γ Δ.
Proof.
  intros onc cr Hcr.
  induction cr; depelim onc; constructor; intuition eauto.
  eapply Hcr; eauto. red. split; simpl; auto.
  eapply Hcr; eauto. split; eauto.
Qed.

Lemma context_relation_mapi P Γ Δ f g : 
  context_relation (fun Γ Δ d d' =>
    P (mapi_context f Γ) (mapi_context g Δ) (map_decl (f #|Γ|) d) (map_decl (g #|Γ|) d')) Γ Δ 
  <~> context_relation P (mapi_context f Γ) (mapi_context g Δ).
Proof.
  split.
  - induction 1; simpl; constructor; intuition auto;
    now rewrite <-(context_relation_length X).
  - induction Γ as [|[na [b|] ty] Γ] in Δ |- *; destruct Δ as [|[na' [b'|] ty'] Δ]; simpl; intros H;
    depelim H; constructor; simpl in *; auto.
    * pose proof (context_relation_length H). len in H0.
      now rewrite <- H0 in p.
    * pose proof (context_relation_length H). len in H0.
      now rewrite <- H0 in p.
Qed.

Lemma context_relation_map P Γ Δ f g : 
  context_relation (fun Γ Δ d d' =>
    P (map_context f Γ) (map_context g Δ) (map_decl f d) (map_decl g d')) Γ Δ <~>
  context_relation P (map_context f Γ) (map_context g Δ).
Proof.
  split.
  - induction 1; simpl; constructor; intuition auto;
    now rewrite <-(context_relation_length X).
  - induction Γ as [|[na [b|] ty] Γ] in Δ |- *; destruct Δ as [|[na' [b'|] ty'] Δ]; simpl; intros H;
      depelim H; constructor; auto.
Qed.

Lemma context_relation_forallb2 (P : context_decl -> context_decl -> bool) Γ Δ : 
  context_relation (fun _ _ => P) Γ Δ ->
  forallb2 P Γ Δ.
Proof.
  induction 1; simpl; auto; now rewrite p, IHX.
Qed.
