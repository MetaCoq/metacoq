(* Distributed under the terms of the MIT license. *)
From Coq Require Import ssreflect.
From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import config.
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
  PCUICWcbvEval PCUICCanonicity PCUICSN PCUICNormalization.

From Equations Require Import Equations.

Definition Prop_univ := Universe.of_levels (inl PropLevel.lProp).

Definition False_oib : one_inductive_body :=
  {| ind_name := "False";
     ind_indices := [];
     ind_sort := Prop_univ;
     ind_type := tSort Prop_univ;
     ind_kelim := IntoAny;
     ind_ctors := [];
     ind_projs := [];
     ind_relevance := Relevant |}.

Definition False_mib : mutual_inductive_body :=
  {| ind_finite := BiFinite;
     ind_npars := 0;
     ind_params := [];
     ind_bodies := [False_oib];
     ind_universes := Monomorphic_ctx;
     ind_variance := None |}.

Theorem pcuic_consistent  {cf:checker_flags} {nor : normalizing_flags} Σ
  {normalisation_in: NormalisationIn Σ} t False_pcuic :
  declared_inductive Σ False_pcuic False_mib False_oib ->
  wf_ext Σ -> axiom_free Σ ->
  Σ ;;; [] |- t : tInd False_pcuic []  -> False.
Proof.
  intros Hdecl wfΣ axΣ typ_false. pose proof (_ ; typ_false) as wt.
  destruct Hdecl as [Hdecl Hidecl].
  destruct False_pcuic as [kn n]. destruct n; cbn in *; [| now rewrite nth_error_nil in Hidecl].
  eapply wh_normalization in wt ; eauto. destruct wt as [empty [Hnormal Hempty]].
  pose proof (Hempty_ := Hempty).
  eapply subject_reduction in typ_false; eauto.
  eapply ind_whnf_canonicity with (indargs := []) in typ_false as ctor; auto.
  - unfold isConstruct_app in ctor.
    destruct decompose_app eqn:decomp.
    apply decompose_app_inv in decomp.
    rewrite decomp in typ_false.
    destruct t0; try discriminate ctor.
    apply PCUICValidity.inversion_mkApps in typ_false as H; auto.
    destruct H as (?&typ_ctor&_).
    apply inversion_Construct in typ_ctor as (?&?&?&?&?&?&?); auto.
    eapply Construct_Ind_ind_eq with (args' := []) in typ_false; tea.
    2: eauto.
    destruct (on_declared_constructor d).
    destruct p.
    destruct s.
    destruct p.
    destruct typ_false as (((((->&_)&_)&_)&_)&_).
    clear -Hdecl d wfΣ. destruct wfΣ.
    cbn in *.
    destruct d as ((?&?)&?).
    unshelve eapply declared_minductive_to_gen in Hdecl; eauto.
    unshelve eapply declared_minductive_to_gen in H; eauto.
    red in H, Hdecl. cbn in *. rewrite Hdecl in H; noconf H.
    cbn in H0. noconf H0.
    cbn in H1. rewrite nth_error_nil in H1.
    discriminate.
  - unfold notCoInductive, check_recursivity_kind. destruct wfΣ.
    unshelve eapply declared_minductive_to_gen in Hdecl; eauto.
    red in Hdecl. cbn. rewrite Hdecl; cbn. auto.
Qed.