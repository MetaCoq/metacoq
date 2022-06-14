(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICLiftSubst PCUICTyping.

Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

Section Generation.
  Context `{cf : config.checker_flags}.

  Inductive typing_spine (Σ : global_env_ext) (Γ : context) :
    term -> list term -> term -> Type :=
  | type_spine_nil ty ty' :
      isType Σ Γ ty' ->
      Σ ;;; Γ |- ty <=s ty' ->
      typing_spine Σ Γ ty [] ty'

  | type_spine_cons hd tl na A B T B' :
      isType Σ Γ (tProd na A B) ->
      Σ ;;; Γ |- T <=s tProd na A B ->
      Σ ;;; Γ |- hd : A ->
      typing_spine Σ Γ (subst10 hd B) tl B' ->
      typing_spine Σ Γ T (hd :: tl) B'.

  Lemma type_mkApps Σ Γ t u T t_ty :
    Σ ;;; Γ |- t : t_ty ->
    typing_spine Σ Γ t_ty u T ->
    Σ ;;; Γ |- mkApps t u : T.
  Proof using Type.
    intros Ht Hsp.
    revert t Ht. induction Hsp; simpl; auto.
    intros t Ht. eapply type_Cumul; eauto. eapply i.π2.

    intros.
    specialize (IHHsp (tApp t0 hd)). apply IHHsp.
    destruct i as [s Hs].
    eapply type_App; eauto.
    eapply type_Cumul; eauto.
  Qed.

  Lemma type_it_mkLambda_or_LetIn :
    forall Σ Γ Δ t A,
      Σ ;;; Γ ,,, Δ |- t : A ->
      Σ ;;; Γ |- it_mkLambda_or_LetIn Δ t : it_mkProd_or_LetIn Δ A.
  Proof using Type.
    intros Σ Γ Δ t A h.
    induction Δ as [| [na [b|] B] Δ ih ] in t, A, h |- *.
    - assumption.
    - simpl. cbn. eapply ih.
      simpl in h. pose proof (typing_wf_local h) as hc.
      dependent induction hc.
      econstructor; try eassumption. exact t0.π2.
    - simpl. cbn. eapply ih.
      pose proof (typing_wf_local h) as hc. cbn in hc.
      dependent induction hc;
      econstructor; try eassumption. exact t0.π2.
  Qed.

End Generation.
