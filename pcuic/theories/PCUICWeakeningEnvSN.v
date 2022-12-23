From Coq Require Import ssreflect Wellfounded.Inclusion.
From MetaCoq.PCUIC Require Import PCUICAst PCUICSN PCUICTyping PCUICSafeLemmata PCUICWeakeningEnvTyp.
Import PCUICEnvironment.

(* It would be nice to prove this, but I'm not sure how -Jason Gross *)
Class NormalisationInAdjustUniversesIn {cf} {no} (Σ : global_env_ext) :=
  normalisation_in_adjust_universes
    : forall kn cb,
      lookup_env Σ.1 kn = Some (ConstantDecl cb) ->
      PCUICTyping.wf_ext Σ ->
      PCUICTyping.wf_ext (Σ.1, cst_universes cb) ->
      @NormalisationIn cf no Σ -> @NormalisationIn cf no (Σ.1, cst_universes cb).

Lemma weakening_env_normalisation_in {cf} {no}
  Σ Σ' ϕ (Hext : extends Σ Σ')
  (HΣ : PCUICTyping.wf Σ)
  (HΣ' : PCUICTyping.wf Σ')
  : @PCUICSN.NormalisationIn cf no (Σ', ϕ) -> @PCUICSN.NormalisationIn cf no (Σ, ϕ).
Proof.
  cbv [PCUICSN.NormalisationIn].
  intros normalisation_in Γ t1 [T Hwt]; specialize (normalisation_in Γ t1); move: normalisation_in.
  cbn in *.
  move => normalisation_in.
  eapply Acc_incl; [ | eapply normalisation_in; econstructor; instantiate (1:=T); revert Hwt ].
  { repeat match goal with H : wf_ext _ |- _ => apply wf_ext_wf in H end.
    hnf; eapply weakening_env_cored; eassumption. }
  intro Hty.
  destruct (weakening_env _ _ _ _ _ Hty) as (_&_&H').
  cbn in *.
  repeat match goal with H : wf_ext _ |- _ => apply wf_ext_wf in H end.
  eapply H'; eauto.
Qed.
