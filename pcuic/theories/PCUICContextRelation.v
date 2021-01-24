From Equations Require Import Equations.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICLiftSubst.

From Coq Require Import CRelationClasses.

Ltac pcuic :=
  try repeat red; cbn in *;
   try (solve [ intuition auto; eauto with pcuic || (try lia || congruence) ]).

Lemma All2_fold_All2 (P : context_decl -> context_decl -> Type) Γ Δ : 
  All2_fold (fun _ _ => P) Γ Δ <~>
  All2 P Γ Δ.
Proof.
  split; induction 1; simpl; constructor; auto.
Qed.
 
Lemma All2_fold_refl P : (forall Δ x, P Δ Δ x x) ->
  forall Δ, All2_fold P Δ Δ.
Proof.
  intros HP.
  induction Δ.
   constructor; auto.
   destruct a as [? [?|] ?]; constructor; auto.
Qed.

Lemma All2_fold_trans P :
  (forall Γ Γ' Γ'' x y z,
      All2_fold P Γ Γ' ->
      All2_fold P Γ' Γ'' ->
      All2_fold P Γ Γ'' ->
      P Γ Γ' x y -> P Γ' Γ'' y z -> P Γ Γ'' x z) ->
  Transitive (All2_fold P).
Proof.
  intros HP x y z H. induction H in z |- *; auto;
  intros H'; unfold context in *; depelim H';
    try constructor; eauto; hnf in H0; noconf H0; eauto.
Qed.

Lemma All2_fold_sym P :
  (forall Γ Γ' x y,
      All2_fold P Γ Γ' ->
      All2_fold P Γ' Γ ->
      P Γ Γ' x y -> P Γ' Γ y x) ->
  Symmetric (All2_fold P).
Proof.
  intros HP x y H.
  induction H; constructor; auto.
Qed.

Lemma All2_fold_app_inv {P} Γ Γ' Δ Δ' :
  #|Δ| = #|Δ'| ->
  All2_fold P (Γ ,,, Δ) (Γ' ,,, Δ') ->
  All2_fold P Γ Γ' * All2_fold (fun Δ Δ' => P (Γ ,,, Δ) (Γ' ,,, Δ')) Δ Δ'.
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

Lemma All2_fold_app_inv_l {P} Γ Γ' Δ Δ' :
  #|Γ| = #|Γ'| ->
  All2_fold P (Γ ,,, Δ) (Γ' ,,, Δ') ->
  All2_fold P Γ Γ' * All2_fold (fun Δ Δ' => P (Γ ,,, Δ) (Γ' ,,, Δ')) Δ Δ'.
Proof.
  intros H.
  induction Δ in H, Δ', Γ, Γ' |- *;
  destruct Δ'; try discriminate.
  intuition auto. constructor.
  intros H'; generalize (All2_fold_length H'). simpl. len. lia.
  intros H'; generalize (All2_fold_length H'). simpl. len. lia.
  intros H'. simpl in H.
  specialize (IHΔ Γ Γ' Δ' ltac:(lia)).
  depelim H'; specialize (IHΔ H'); intuition auto;
  constructor; auto.
Qed.

Lemma All2_fold_app {P} Γ Γ' Δ Δ' :
  #|Δ| = #|Δ'| ->
  All2_fold P Γ Γ' -> All2_fold (fun Δ Δ' => P (Γ ,,, Δ) (Γ' ,,, Δ')) Δ Δ' ->
  All2_fold P (Γ ,,, Δ) (Γ' ,,, Δ').
Proof.
  intros H.
  induction 2; simpl; auto.
  constructor. apply IHX0. simpl in H. lia.
  apply p.
Qed.

Lemma All2_fold_impl_onctx P P' Γ Δ Q :  
  onctx Q Γ ->
  All2_fold P Γ Δ ->
  (forall Γ Δ d d', 
    All2_fold P Γ Δ -> 
    P Γ Δ d d' ->
    ondecl Q d ->
    P' Γ Δ d d') ->
  All2_fold P' Γ Δ.
Proof.
  intros onc cr Hcr.
  induction cr; depelim onc; constructor; intuition eauto.
Qed.

Lemma All2_fold_impl_ind P P' Γ Δ :  
  All2_fold P Γ Δ ->
  (forall Γ Δ d d', 
    All2_fold P Γ Δ -> 
    All2_fold P' Γ Δ ->
    P Γ Δ d d' ->
    P' Γ Δ d d') ->
  All2_fold P' Γ Δ.
Proof.
  intros cr Hcr.
  induction cr; constructor; intuition eauto.
Qed.

Lemma All2_fold_mapi P Γ Δ f g : 
  All2_fold (fun Γ Δ d d' =>
    P (mapi_context f Γ) (mapi_context g Δ) (map_decl (f #|Γ|) d) (map_decl (g #|Γ|) d')) Γ Δ 
  <~> All2_fold P (mapi_context f Γ) (mapi_context g Δ).
Proof.
  split.
  - induction 1; simpl; constructor; intuition auto;
    now rewrite <-(All2_fold_length X).
  - induction Γ as [|d Γ] in Δ |- *; destruct Δ as [|d' Δ]; simpl; intros H;
    depelim H; constructor; simpl in *; auto.
    pose proof (All2_fold_length H). len in H0.
    now rewrite <- H0 in p.
Qed.

Lemma All2_fold_map P Γ Δ f g : 
  All2_fold (fun Γ Δ d d' =>
    P (map_context f Γ) (map_context g Δ) (map_decl f d) (map_decl g d')) Γ Δ <~>
  All2_fold P (map_context f Γ) (map_context g Δ).
Proof.
  split.
  - induction 1; simpl; constructor; intuition auto;
    now rewrite <-(All2_fold_length X).
  - induction Γ as [|d Γ] in Δ |- *; destruct Δ as [|d' Δ]; simpl; intros H;
      depelim H; constructor; auto.
Qed.

Lemma All2_fold_cst_map P Γ Δ f g : 
  All2_fold (fun _ _ d d' => P (f d) (g d')) Γ Δ <~>
  All2_fold (fun _ _ => P) (map f Γ) (map g Δ).
Proof.
  split.
  - induction 1; simpl; constructor; intuition auto;
    now rewrite <-(All2_fold_length X).
  - induction Γ as [|d Γ] in Δ |- *; destruct Δ as [|d' Δ]; simpl; intros H;
      depelim H; constructor; auto.
Qed.

Lemma All2_fold_forallb2 (P : context_decl -> context_decl -> bool) Γ Δ : 
  All2_fold (fun _ _ => P) Γ Δ ->
  forallb2 P Γ Δ.
Proof.
  induction 1; simpl; auto; now rewrite p, IHX.
Qed.

Lemma All2_fold_nth {P n Γ Γ' d} :
  All2_fold P Γ Γ' -> nth_error Γ n = Some d ->
  { d' & ((nth_error Γ' n = Some d') *
          let Γs := skipn (S n) Γ in
          let Γs' := skipn (S n) Γ' in
          All2_fold P Γs Γs' *
          P Γs Γs' d d')%type }.
Proof.
  induction n in Γ, Γ', d |- *; destruct Γ; intros Hrel H; noconf H.
  - depelim Hrel.
    simpl. eexists; intuition eauto.
  - depelim Hrel.
    destruct (IHn _ _ _ Hrel H).
    cbn -[skipn] in *.
    eexists; intuition eauto.
Qed.

Lemma All2_fold_nth_r {P n Γ Γ' d'} :
  All2_fold P Γ Γ' -> nth_error Γ' n = Some d' ->
  { d & ((nth_error Γ n = Some d) *
        let Γs := skipn (S n) Γ in
        let Γs' := skipn (S n) Γ' in
        All2_fold P Γs Γs' *
        P Γs Γs' d d')%type }.
Proof.
  induction n in Γ, Γ', d' |- *; destruct Γ'; intros Hrel H; noconf H.
  - depelim Hrel.
    simpl. eexists; intuition eauto.
  - depelim Hrel.
    destruct (IHn _ _ _ Hrel H).
    cbn -[skipn] in *.
    eexists; intuition eauto.
Qed.
