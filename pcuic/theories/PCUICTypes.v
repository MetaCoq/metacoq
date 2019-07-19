(* Distributed under the terms of the MIT license.   *)
Set Warnings "-notation-overridden".

From Equations Require Import Equations.
Require Import Equations.Tactics.
From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia CRelationClasses.
From MetaCoq Require Import LibHypsNaming.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICWeakeningEnv PCUICWeakening
     PCUICSubstitution PCUICClosed PCUICCumulativity PCUICGeneration
     PCUICSubstitution PCUICClosed PCUICCumulativity PCUICGeneration PCUICReduction
     PCUICParallelReduction PCUICEquality
     PCUICValidity PCUICParallelReductionConfluence PCUICConfluence
     PCUICContextConversion
     PCUICConversion PCUICInversion PCUICPrincipality.

Require Import ssreflect ssrbool.
Require Import String.
Set Asymmetric Patterns.
Set SimplIsCbn.

Inductive is_type {cf : checker_flags} (Σ : global_env_ext) (Γ : context) : term -> Type :=
| is_type_Rel i d :
    nth_error Γ i = Some d ->
    is_type Σ Γ d.(decl_type) ->
    is_type Σ Γ (tRel i)

| is_type_Sort s : is_type Σ Γ (tSort s)

| is_type_Prod na dom codom :
    is_type Σ Γ dom -> is_type Σ (Γ ,, vass na dom) codom ->
    is_type Σ Γ (tProd na dom codom)

| is_type_LetIn na b B t :
    is_type Σ Γ B -> is_type Σ (Γ ,, vdef na b B) t ->
    is_type Σ Γ (tLetIn na b B t)

| is_type_App f u na dom codom :
    Σ ;;; Γ |- f : tProd na dom codom ->
    Σ ;;; Γ |- u : dom ->
    is_type Σ Γ (codom {0 := u}) ->
    is_type Σ Γ (tApp f u)

| is_type_Const c u decl :
    declared_constant Σ c decl ->
    is_type Σ Γ (subst_instance_constr u decl.(cst_type)) ->
    is_type Σ Γ (tConst c u)

| is_type_Ind i u : is_type Σ Γ (tInd i u)

| is_type_Case indp p c brs :
    is_type Σ Γ p ->
    is_type Σ Γ (tCase indp p c brs)

| is_type_Proj p c u mdecl idecl pdecl args :
    declared_projection Σ.1 mdecl idecl p pdecl ->
    Σ;;; Γ |- c : mkApps (tInd p.1.1 u) args ->
    is_type Σ Γ (subst_instance_constr u pdecl.2) ->
    is_type Σ Γ (tProj p c)

| is_type_Fix mfix n decl :
    nth_error mfix n = Some decl ->
    is_type Σ Γ decl.(dtype) ->
    is_type Σ Γ (tFix mfix n)

| is_type_Cumul T T' :
    is_type Σ Γ T ->
    isWfArity_or_Type Σ Γ T' ->
    Σ ;;; Γ |- T <= T' ->
    is_type Σ Γ T'

| is_type_Cumul_inv T T' :
    is_type Σ Γ T' ->
    isWfArity_or_Type Σ Γ T ->
    Σ ;;; Γ |- T <= T' ->
    is_type Σ Γ T.

(* cofixpoints always produce a value in the coinductive type:
   they cannot be types *)

Lemma inversion_type_Sort {cf : checker_flags} (Σ : global_env_ext) (Γ : context) T s :
  Σ ;;; Γ |- T : tSort s -> ∑ ty, (Σ ;;; Γ |- T : ty) * (Σ ;;; Γ |- ty <= tSort s).
Proof.
  intros.
  exists (tSort s).
  split; auto.
Qed.

Lemma isType_red {cf : checker_flags} (Σ : global_env_ext) (Γ : context) T T' :
  isWfArity_or_Type Σ Γ T ->
  red Σ Γ T T' -> is_type Σ Γ T' -> is_type Σ Γ T.
Proof.
  intros.
Admitted.


Lemma is_type_sound {cf : checker_flags} (Σ : global_env_ext) (Γ : context) T :
  isType Σ Γ T -> is_type Σ Γ T.
Proof.
  intros [s Hs].
  eapply inversion_type_Sort in Hs as [U [HU Us]].
  revert s Us. induction HU; intros s' Us; try solve [econstructor; eauto].
  - econstructor; eauto.
    destruct decl as [na d ty]; try discriminate.
    simpl in Us.
    eapply cumul_Sort_r_inv in Us as [s [reds ?]]. simpl.
    eapply is_type_Cumul with (tSort s). constructor; auto. admit.
    admit.

  - now eapply cumul_Prod_Sort_inv in Us.

  - constructor. eapply IHHU1; eauto.
    eapply IHHU3 with s'. admit.

  - eapply is_type_App; eauto.
    eapply is_type_Cumul_inv; eauto. constructor. admit.

  - econstructor. eauto.
    eapply is_type_Cumul_inv; eauto. constructor. admit.

  - admit. (* Impossible *)
  - constructor. eapply IHHU1.
    admit.

  - admit.
  - admit.
  - admit.
  - eapply IHHU.
    eapply transitivity; eauto. eapply c. eapply Us.
Admitted.