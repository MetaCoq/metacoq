(* Distributed under the terms of the MIT license. *)
From Coq Require Import ssreflect ssrbool.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICTyping PCUICCumulativity
     PCUICReduction PCUICWeakeningConv PCUICWeakeningTyp PCUICEquality PCUICUnivSubstitutionConv
     PCUICSigmaCalculus PCUICContextReduction
     PCUICParallelReduction PCUICParallelReductionConfluence PCUICClosedConv PCUICClosedTyp
     PCUICRedTypeIrrelevance PCUICOnFreeVars PCUICConfluence PCUICSubstitution
     PCUICWellScopedCumulativity PCUICArities.

Require Import CRelationClasses CMorphisms.
Require Import Equations.Prop.DepElim.
Require Import Equations.Type.Relation Equations.Type.Relation_Properties.
From Equations Require Import Equations.

(* High-level lemmas about well-typed ws_cumul_pb *)

Notation " Σ ;;; Γ ⊢ t ≤[ le ] u ✓" := (wt_cumul_pb le Σ Γ t u) (at level 50, Γ, t, u at next level,
  format "Σ  ;;;  Γ  ⊢  t  ≤[ le ]  u  ✓").

Coercion wt_cumul_pb_ws_cumul_pb : wt_cumul_pb >-> equality.

Section WtEquality.
  Context {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ}.

  Lemma type_wt_cumul_pb {le Γ t} T {U} :
    Σ ;;; Γ |- t : T ->
    Σ ;;; Γ ⊢ T ≤[le] U ✓ ->
    Σ ;;; Γ |- t : U.
  Proof.
    intros.
    eapply type_ws_cumul_pb; tea. apply X0. exact X0. apply X0.π2.
    destruct le.
    - now eapply (cumulAlgo_cumulSpec Σ (pb:=Cumul)).
    - eapply ws_cumul_pb_eq_le in X1.
      now eapply cumulAlgo_cumulSpec in X1.
  Qed.

  Lemma wt_cumul_pb_subst {le Γ Δ Γ' s t u} :
    wt_cumul_pb le Σ (Γ ,,, Δ ,,, Γ') t u ->
    wt_cumul_pb le Σ (Γ ,,, subst_context s 0 Γ') (subst s #|Γ'| t) (subst s #|Γ'| u).
  Proof.
    intros [].
