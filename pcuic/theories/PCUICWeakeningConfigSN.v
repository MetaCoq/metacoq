From Coq Require Import ssreflect Wellfounded.Inclusion.
From MetaCoq.Utils Require Import utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICSN PCUICTyping PCUICSafeLemmata PCUICWeakeningConfigTyp.
Import PCUICEnvironment.

Lemma weakening_config_normalisation_in {cf1 cf2} {no1 no2}
  Σ
  (Hcf : config.impl cf2 cf1)
  : @PCUICSN.NormalisationIn cf1 no1 Σ -> @PCUICSN.NormalisationIn cf2 no2 Σ.
Proof.
  cbv [PCUICSN.NormalisationIn].
  intros normalisation_in Γ t1 [T Hwt]; specialize (normalisation_in Γ t1).
  eapply Acc_incl; [ | eapply normalisation_in; econstructor; instantiate (1:=T); revert Hwt ].
  { hnf; trivial. }
  eapply (@weakening_config cf2 cf1); assumption.
Qed.
