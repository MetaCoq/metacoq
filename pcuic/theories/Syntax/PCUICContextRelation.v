From Equations Require Import Equations.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICLiftSubst.
From MetaCoq.PCUIC Require Export PCUICTactics.
From Coq Require Import CRelationClasses.

Lemma All2_fold_impl_onctx (P : context -> context -> context_decl -> context_decl -> Type) P' Γ Δ Q :  
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

Lemma All2_fold_mapi (P : context -> context -> context_decl -> context_decl -> Type) (Γ Δ : context) f g : 
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

Lemma All2_fold_map {P : context -> context -> context_decl -> context_decl -> Type} {Γ Δ : context} f g : 
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

Lemma All2_fold_cst_map {P : context_decl -> context_decl -> Type} {Γ Δ : context} {f g} : 
  All2_fold (fun _ _ d d' => P (f d) (g d')) Γ Δ <~>
  All2_fold (fun _ _ => P) (map f Γ) (map g Δ).
Proof.
  split.
  - induction 1; simpl; constructor; intuition auto;
    now rewrite <-(All2_fold_length X).
  - induction Γ as [|d Γ] in Δ |- *; destruct Δ as [|d' Δ]; simpl; intros H;
      depelim H; constructor; auto.
Qed.