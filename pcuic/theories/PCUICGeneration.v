(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool List.
From MetaCoq.Template Require Import utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICLiftSubst PCUICTyping.
Set Asymmetric Patterns.

Import ListNotations.

Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

Derive NoConfusion NoConfusionHom for term.
Derive NoConfusion NoConfusionHom for context_decl.
Derive NoConfusion NoConfusionHom for list.
Derive NoConfusion NoConfusionHom for option.

Section Generation.
  Context `{cf : config.checker_flags}.

  Definition isWfArity_or_Type Σ Γ T : Type := (isWfArity typing Σ Γ T + isType Σ Γ T).

  Inductive typing_spine (Σ : global_env_ext) (Γ : context) :
    term -> list term -> term -> Type :=
  | type_spine_nil ty ty' :
      isWfArity_or_Type Σ Γ ty' ->
      Σ ;;; Γ |- ty <= ty' ->
      typing_spine Σ Γ ty [] ty'

  | type_spine_cons hd tl na A B T B' :
      isWfArity_or_Type Σ Γ (tProd na A B) ->
      Σ ;;; Γ |- T <= tProd na A B ->
      Σ ;;; Γ |- hd : A ->
      typing_spine Σ Γ (subst10 hd B) tl B' ->
      typing_spine Σ Γ T (hd :: tl) B'.

  Lemma type_mkApps Σ Γ t u T t_ty :
    Σ ;;; Γ |- t : t_ty ->
    typing_spine Σ Γ t_ty u T ->
    Σ ;;; Γ |- mkApps t u : T.
  Proof.
    intros Ht Hsp.
    revert t Ht. induction Hsp; simpl; auto.
    intros t Ht. eapply type_Cumul; eauto.

    intros.
    specialize (IHHsp (tApp t0 hd)). apply IHHsp.
    eapply type_App.
    eapply type_Cumul; eauto. eauto.
  Qed.

  Lemma type_it_mkLambda_or_LetIn :
    forall Σ Γ Δ t A,
      Σ ;;; Γ ,,, Δ |- t : A ->
      Σ ;;; Γ |- it_mkLambda_or_LetIn Δ t : it_mkProd_or_LetIn Δ A.
  Proof.
    intros Σ Γ Δ t A h.
    induction Δ as [| [na [b|] B] Δ ih ] in t, A, h |- *.
    - assumption.
    - simpl. cbn. eapply ih.
      simpl in h. pose proof (typing_wf_local h) as hc.
      dependent induction hc.
      econstructor; try eassumption. exact t0.π2.
    - simpl. cbn. eapply ih.
      pose proof (typing_wf_local h) as hc. cbn in hc.
      dependent induction hc.
      econstructor; try eassumption. exact t0.π2.
  Qed.

End Generation.
