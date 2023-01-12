(* Distributed under the terms of the MIT license. *)
From Coq Require Import ssreflect.
From MetaCoq.Common Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICTyping PCUICEquality PCUICAst PCUICAstUtils
  PCUICWeakeningConv PCUICWeakeningTyp PCUICSubstitution PCUICGeneration PCUICArities
  PCUICWcbvEval PCUICSR PCUICInversion
  PCUICUnivSubstitutionConv PCUICUnivSubstitutionTyp
  PCUICElimination PCUICSigmaCalculus PCUICContextConversion
  PCUICUnivSubst PCUICWeakeningEnvConv PCUICWeakeningEnvTyp
  PCUICCumulativity PCUICConfluence
  PCUICInduction PCUICLiftSubst PCUICContexts PCUICSpine
  PCUICConversion PCUICValidity PCUICInductives PCUICConversion
  PCUICInductiveInversion PCUICNormal PCUICSafeLemmata
  PCUICParallelReductionConfluence
  PCUICWcbvEval PCUICClosed PCUICClosedTyp
  PCUICReduction PCUICCSubst PCUICOnFreeVars PCUICWellScopedCumulativity
  PCUICWcbvEval PCUICCanonicity PCUICProgress PCUICSN.

From Equations Require Import Equations.

From MetaCoq Require Import PCUICSN.


Lemma wh_normalization {cf:checker_flags} {no:normalizing_flags} {Σ} {normalisation:NormalisationIn Σ} {t} : wf_ext Σ -> axiom_free Σ ->
welltyped Σ [] t  -> exists v, squash (whnf RedFlags.default Σ [] v * red Σ [] t v).
Proof.
intros Hwf Hax Hwt.
eapply PCUICSN.normalisation_in in Hwt as HSN; eauto.
induction HSN as [t H IH].
destruct Hwt as [A HA].
edestruct progress as [_ [_ [[t' Ht'] | Hval]]]; eauto.
- eapply wcbv_red1_red1 in Ht' as Hred. 2:{ change 0 with (#|@nil context_decl|). eapply subject_closed. eauto. }
  edestruct IH as [v Hv]. econstructor. eauto.
  econstructor. eapply subject_reduction; eauto.
  exists v. sq. destruct Hv. split; eauto. eapply red_step; eauto.
- exists t. sq. split; eauto. eapply value_whnf; eauto.
  eapply @subject_closed with (Γ := []); eauto.
Defined.

Lemma wcbv_normalization {cf:checker_flags} {no:normalizing_flags} {Σ} {normalisation:NormalisationIn Σ} {t} : wf_ext Σ -> axiom_free Σ ->
  welltyped Σ [] t  -> exists v, squash (eval Σ t v).
Proof.
  intros Hwf Hax Hwt.
  eapply PCUICSN.normalisation_in in Hwt as HSN; eauto.
  induction HSN as [t H IH].
  destruct Hwt as [A HA].
  edestruct progress as [_ [_ [[t' Ht'] | Hval]]]; eauto.
  - eapply wcbv_red1_red1 in Ht' as Hred. 2:{ change 0 with (#|@nil context_decl|). eapply subject_closed. eauto. }
    edestruct IH as [v Hv]. econstructor. eauto.
    econstructor. eapply subject_reduction; eauto.
    exists v. sq. eapply wcbv_red1_eval; eauto.
    now eapply subject_closed in HA.
  - exists t. sq. eapply value_final; eauto.
Qed.

From MetaCoq Require Import PCUICFirstorder.

Lemma firstorder_value_irred {cf:checker_flags} Σ t t' :
  firstorder_value Σ [] t ->
  PCUICReduction.red1 Σ [] t t' -> False.
Proof.
  intros H.
  revert t'. pattern t. revert t H.
  eapply firstorder_value_inds.
  intros i n ui u args pandi Hty Hargs IH Hprop t' Hred.
  eapply red1_mkApps_tConstruct_inv in Hred as (x & -> & Hone).
  solve_all.
  clear - IH Hone. induction IH as [ | ? ? []] in x, Hone |- *.
  - invs Hone.
  - invs Hone; eauto.
Qed.

Definition ws_empty f : ws_context f.
Proof.
  unshelve econstructor.
  exact nil.
  reflexivity.
Defined.

Lemma irred_equal Σ Γ t t' :
  Σ ;;; Γ ⊢ t ⇝ t' ->
  (forall v', PCUICReduction.red1 Σ Γ t v' -> False) ->
  t = t'.
Proof.
  intros Hred Hirred. destruct Hred.
  clear clrel_ctx clrel_src.
  induction clrel_rel.
  - edestruct Hirred; eauto.
  - reflexivity.
  - assert (x = y) as <- by eauto. eauto.
Qed.

Lemma ws_wcbv_standardization {cf:checker_flags} {no:normalizing_flags} {Σ} {normalisation:NormalisationIn Σ} {i u args mind} {t v : ws_term (fun _ => false)} : wf_ext Σ -> axiom_free Σ ->
  Σ ;;; [] |- t : mkApps (tInd i u) args ->
  lookup_env Σ (i.(inductive_mind)) = Some (InductiveDecl mind) ->
  @firstorder_ind Σ (firstorder_env Σ) i ->
  closed_red Σ [] t v ->
  (forall v', PCUICReduction.red1 Σ [] v v' -> False) ->
  squash (eval Σ t v).
Proof.
  intros Hwf Hax Hty Hdecl Hfo Hred Hirred.
  destruct (@wcbv_normalization _ no Σ normalisation t) as (v' & Hv'); eauto.
  1:{ eexists; eauto. }
  sq.
  assert (Σ;;; [] |- t ⇝* v') as Hred' by now eapply wcbeval_red.
  eapply closed_red_confluence in Hred as Hred_. destruct Hred_ as (v'' & H1 & H2).
  2:{ econstructor; eauto. eapply subject_is_open_term. eauto. }
  destruct v as [v Hv].
  assert (v = v'') as <- by (eapply irred_equal; eauto).
  assert (firstorder_value Σ [] v'). {
    eapply firstorder_value_spec; eauto.
    eapply subject_reduction_eval; eauto.
    eapply eval_to_value. eauto.
  }
  enough (v' = v) as -> by eauto.
  eapply irred_equal. eauto.
  intros. eapply firstorder_value_irred; eauto.
Qed.

Lemma wcbv_standardization {cf:checker_flags} {no:normalizing_flags} {Σ} {normalisation:NormalisationIn Σ} {i u args mind} {t v : term} : wf_ext Σ -> axiom_free Σ ->
  Σ ;;; [] |- t : mkApps (tInd i u) args ->
  lookup_env Σ (i.(inductive_mind)) = Some (InductiveDecl mind) ->
  @firstorder_ind Σ (firstorder_env Σ) i ->
  red Σ [] t v ->
  (forall v', PCUICReduction.red1 Σ [] v v' -> False) ->
  ∥ eval Σ t v ∥.
Proof.
  intros Hwf Hax Hty Hdecl Hfo Hred Hirred.
  unshelve edestruct @ws_wcbv_standardization.
  1-7: shelve.
  1: exists t; shelve.
  1: exists v; shelve.
  all: sq; eauto.
  cbn.
  econstructor; eauto.
  eapply subject_is_open_term. eauto.
  Unshelve.
  all: rewrite -closed_on_free_vars_none.
  - now eapply subject_closed in Hty.
  - eapply @subject_closed with (Γ := []); eauto.
    eapply subject_reduction; eauto.
Qed.
