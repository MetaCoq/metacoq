(* Distributed under the terms of the MIT license.   *)
From Equations Require Import Equations.
From Coq Require Import Bool String List BinPos Compare_dec Omega Lia.
Require Import Coq.Program.Syntax Coq.Program.Basics.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICLiftSubst PCUICUnivSubst
     PCUICTyping PCUICWeakeningEnv PCUICClosed PCUICReduction.
Require Import ssreflect ssrbool.

(** * Type preservation for σ-calculus *)

Set Asymmetric Patterns.

Section Sigma.

Context `{checker_flags}.

Open Scope sigma_scope.

(* Well-typedness of a substitution *)

Definition well_subst Σ (Γ : context) σ (Δ : context) :=
  forall x decl,
    nth_error Γ x = Some decl ->
    Σ ;;; Δ |- σ x : ((lift0 (S x)) (decl_type decl)).[ σ ].

Notation "Σ ;;; Δ ⊢ σ : Γ" :=
  (well_subst Σ Γ σ Δ) (at level 50, Δ, σ, Γ at next level).

Lemma well_subst_Up :
  forall Σ Γ Δ σ na A,
    Σ ;;; Δ ⊢ σ : Γ ->
    Σ ;;; Δ ,, vass na A.[σ] ⊢ ⇑ σ : Γ ,, vass na A.
Proof.
  intros Σ Γ Δ σ na A h [|n] decl e.
  - simpl in *. inversion e. subst. clear e. simpl.
    (* NEED commutation lemma between lift and inst *)
    admit.
  - simpl in *.
    specialize (h _ _ e).
Admitted.

Lemma type_inst :
  forall Σ Γ Δ σ t A,
    wf Σ.1 ->
    wf_local Σ Γ ->
    wf_local Σ Δ ->
    Σ ;;; Δ ⊢ σ : Γ ->
    Σ ;;; Γ |- t : A ->
    Σ ;;; Δ |- t.[σ] : A.[σ].
Proof.
  intros Σ Γ Δ σ t A hΣ hΓ hΔ hσ h.
  revert Σ hΣ Γ hΓ t A h Δ σ hΔ hσ.
  apply (typing_ind_env (fun Σ Γ t T => forall Δ σ,
    wf_local Σ Δ ->
    Σ ;;; Δ ⊢ σ : Γ ->
    Σ ;;; Δ |- t.[σ] : T.[σ]
  )).
  - intros Σ wfΣ Γ wfΓ n decl e X Δ σ hΔ hσ. simpl.
    eapply hσ. assumption.
  - intros Σ wfΣ Γ wfΓ l X H0 Δ σ hΔ hσ. simpl.
    econstructor. all: assumption.
  - intros Σ wfΣ Γ wfΓ na A B s1 s2 X hA ihA hB ihB Δ σ hΔ hσ.
    autorewrite with sigma. simpl.
    econstructor.
    + eapply ihA ; auto.
    + eapply ihB.
      * econstructor ; auto.
        eexists. eapply ihA ; auto.
      * eapply well_subst_Up. assumption.
Admitted.

End Sigma.