(* Distributed under the terms of the MIT license.   *)
From Equations Require Import Equations.
From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICWeakeningEnv PCUICWeakening
     PCUICSubstitution PCUICClosed.
Require Import ssreflect ssrbool.
Require Import String.
From MetaCoq.Template Require Import LibHypsNaming.
Local Open Scope string_scope.
Set Asymmetric Patterns.

Existing Instance config.default_checker_flags.

Definition isWfArity_or_Type Σ Γ T : Type := (isWfArity typing Σ Γ T + isType Σ Γ T).

Inductive typing_spine `{checker_flags} (Σ : global_context) (Γ : context) : term -> list term -> term -> Type :=
| type_spine_nil ty : typing_spine Σ Γ ty [] ty
| type_spine_cons hd tl na A B T B' :
    isWfArity_or_Type Σ Γ (tProd na A B) ->
    Σ ;;; Γ |- T <= tProd na A B ->
    Σ ;;; Γ |- hd : A ->
    typing_spine Σ Γ (subst10 hd B) tl B' ->
    typing_spine Σ Γ T (cons hd tl) B'.

Lemma type_mkApps Σ Γ t u T t_ty :
  Σ ;;; Γ |- t : t_ty ->
  typing_spine Σ Γ t_ty u T ->
  Σ ;;; Γ |- mkApps t u : T.
Proof.
  intros Ht Hsp.
  revert t Ht. induction Hsp; simpl; auto.

  intros.
  specialize (IHHsp (tApp t0 hd)). apply IHHsp.
  eapply type_App.
  eapply type_Conv; eauto. eauto.
Qed.
