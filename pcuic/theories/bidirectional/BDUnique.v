From Coq Require Import Bool List Arith Lia.
From MetaCoq.Template Require Import config utils monad_utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICLiftSubst PCUICTyping PCUICEquality PCUICArities PCUICInversion PCUICReduction PCUICSubstitution PCUICConversion PCUICCumulativity PCUICGeneration PCUICWfUniverses PCUICContextConversion PCUICContextSubst PCUICContexts PCUICWeakening PCUICWeakeningEnv PCUICSpine PCUICWfUniverses PCUICUnivSubst PCUICUnivSubstitution PCUICClosed PCUICInductives PCUICValidity PCUICInductiveInversion PCUICConfluence PCUICWellScopedCumulativity.
From MetaCoq.PCUIC Require Import BDEnvironmentTyping BDTyping BDToPCUIC BDFromPCUIC.

Require Import ssreflect ssrbool.
From Equations Require Import Equations.
Require Import Equations.Type.Relation Equations.Type.Relation_Properties.
Require Import Equations.Prop.DepElim.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

Lemma eq_universe_sort_of_product `{checker_flags} Σ s1 s1' s2 s2' :
  eq_universe Σ s1 s1' -> eq_universe Σ s2 s2' ->
  eq_universe Σ (Universe.sort_of_product s1 s2) (Universe.sort_of_product s1' s2').
Proof.
  intros e e'.
  unfold eq_universe in *.
  destruct check_univs ; auto.
  unfold eq_universe0 in *.
  intros v sat.
  specialize (e v sat).
  specialize (e' v sat).
  unfold Universe.univ_val in *.
  destruct s1 ; destruct s2 ; destruct s1' ; destruct s2' ; cbn in * ; auto.
  all: inversion e.
  all: inversion e'.
  f_equal.
  rewrite !val_sup.
  rewrite H1 H2.
  reflexivity.
Qed.

(* a version for cumulativity only is in PCUICInductiveInversion… *)
Lemma projection_cumulative_indices {cf} {Σ} {wfΣ : wf Σ} {le} :
  forall {mdecl idecl cdecl p pdecl u u' },
  declared_projection Σ p mdecl idecl cdecl pdecl ->
  on_udecl_prop Σ (ind_universes mdecl) ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  consistent_instance_ext Σ (ind_universes mdecl) u' ->
  R_global_instance Σ (eq_universe Σ) (if le then leq_universe Σ else eq_universe Σ) (IndRef p.1.1) (ind_npars mdecl) u u' ->
  Σ ;;; projection_context p.1.1 mdecl idecl u ⊢
    subst_instance u pdecl.2 ≤[le] subst_instance u' pdecl.2.
Proof.
  destruct le.
  1:{
    intros.
    eapply PCUICInductiveInversion.projection_cumulative_indices.
    all: eassumption.
  }
Admitted.

Lemma equality_Prod_r `{checker_flags} {Σ} {wfΣ : wf Σ} {Γ na na' M1 M2 N2 le} :
eq_binder_annot na na' ->
is_open_term Γ M1 ->
Σ ;;; (Γ ,, vass na M1) ⊢ M2 ≤[le] N2 ->
Σ ;;; Γ ⊢ (tProd na M1 M2) ≤[le] (tProd na' M1 N2).
Proof.
intros.
eapply equality_Prod ; auto.
eapply equality_refl ; auto with fvs.
apply equality_is_closed_context in X.
rewrite PCUICOnFreeVars.on_free_vars_ctx_snoc in X.
move: X => /andP [] //.
Qed.

Section BDUnique.

Context `{cf : checker_flags}.
Context (Σ : global_env_ext).
Context (wfΣ : wf Σ).

Let Pinfer Γ t T :=
  wf_local Σ Γ -> forall T', Σ ;;; Γ |- t ▹ T' -> Σ ;;; Γ ⊢ T = T'.

Let Psort Γ t u :=
  wf_local Σ Γ -> forall u', Σ ;;; Γ |- t ▹□ u' -> eq_universe Σ u u'.

Let Pprod Γ t (na : aname) A B :=
  wf_local Σ Γ -> forall na' A' B', Σ ;;; Γ |- t ▹Π (na',A',B') ->
  [× eq_binder_annot na na', Σ ;;; Γ ⊢ A = A'
      & Σ ;;; Γ,, vass na' A' ⊢ B = B'].

Let Pind Γ ind t u args :=
  wf_local Σ Γ -> forall ind' u' args', Σ ;;; Γ |- t ▹{ind'} (u',args') ->
  [× ind = ind',
      R_global_instance Σ (eq_universe Σ) (eq_universe Σ) (IndRef ind) #|args| u u',
      is_closed_context Γ &
      All2 (fun a a' => Σ ;;; Γ ⊢ a = a') args args'].

Let Pcheck (Γ : context) (t T : term) := True.

Let PΓ (Γ : context) := True.

Let PΓ_rel (Γ Γ' : context) := True.

Theorem bidirectional_unique : env_prop_bd Σ Pcheck Pinfer Psort Pprod Pind PΓ PΓ_rel.
Proof.

  apply bidir_ind_env.

  all: intros ; red ; auto.
  1-9,11-13: intros ? T' ty_T' ; inversion_clear ty_T'.
  14-16: intros.

  - rewrite H in H0.
    inversion H0. subst. clear H0.
    eapply typing_equality.
    1: assumption.
    by constructor.

  - eapply typing_equality.
    1: assumption.
    by constructor.

  - apply H in X2 ; auto.
    apply H0 in X3.
    2:{ constructor ; auto. apply infering_sort_typing in X ; auto. eexists. eassumption. }
    apply into_equality.
    3,4: reflexivity.
    + constructor.
      constructor. 
      apply eq_universe_sort_of_product.
      all: auto.
    + by apply wf_local_closed_context.


  - apply equality_Prod_r => //.
    1: by eapply subject_is_open_term, infering_sort_typing ; eauto.
    apply X1 in X4 ; auto.
    constructor ; auto.
    apply infering_sort_typing in X ; auto.
    eexists. eassumption.

  - apply equality_LetIn_bo ; auto.
    apply X2 in X6 ; auto.
    constructor ; auto.
    + apply infering_sort_typing in X ; auto. eexists. eassumption.
    + apply checking_typing ; auto. eexists. apply infering_sort_typing; eauto.

  - apply X0 in X3 as [] ; auto.
    eapply substitution_equality_vass.
    + eapply checking_typing ; auto.
      2: eexact X1.
      eapply isType_tProd, validity, infering_prod_typing ; eauto.
    + eapply equality_equality_ctx.
      2: eassumption.
      constructor.
      1: by apply context_equality_refl, wf_local_closed_context.
      constructor ; eauto.


  - replace decl0 with decl by (eapply declared_constant_inj ; eassumption).
    eapply typing_equality => //.
    constructor ; eassumption.

  - replace idecl0 with idecl by (eapply declared_inductive_inj ; eassumption).
    eapply typing_equality => //.
    econstructor ; eassumption.
  
  - replace cdecl0 with cdecl by (eapply declared_constructor_inj ; eassumption).
    replace mdecl0 with mdecl by (eapply declared_constructor_inj ; eassumption).
    eapply typing_equality => //.
    econstructor ; eassumption.
  
  - move: (H1) => /declared_projection_inj /(_ H) [? [? [? ?]]].
    subst mdecl0 idecl0 pdecl0 ty ty0.
    change Γ with (Γ ,,, subst_context (c :: List.rev args) 0 []).

    assert (consistent_instance_ext Σ (ind_universes mdecl) u0).
    {
      apply infering_ind_typing in X2 ; auto.
      apply validity in X2 as [] ; auto.
      eapply invert_type_mkApps_ind ; eauto.
      exact H1.
    }

    assert (consistent_instance_ext Σ (ind_universes mdecl) u).
    {
      apply infering_ind_typing in X ; auto.
      apply validity in X as [] ; auto.
      eapply invert_type_mkApps_ind ; eauto.
      exact H1.
    }

    eapply (PCUICConversion.substitution_equality_subst_conv (Δ := [])).

    + eapply subslet_untyped_subslet, projection_subslet ; eauto.
      2: eapply validity.
      all: eapply infering_ind_typing ; eauto.
    + eapply subslet_untyped_subslet, projection_subslet ; eauto.
      2: eapply validity.
      all: eapply infering_ind_typing ; eauto.
    + constructor.
      1:{
        eapply equality_refl.
        1: by apply wf_local_closed_context.
        eapply subject_is_open_term, infering_ind_typing ; eauto.
      }
      apply All2_rev.
      eapply X0 ; eauto.
    
    + apply wf_local_closed_context.
      repeat apply PCUICWeakening.weaken_wf_local ; auto.
      eapply wf_projection_context.
      all: eauto.

    + cbn -[projection_context].
      apply weaken_equality ; auto.
      1: by apply wf_local_closed_context.
      eapply projection_cumulative_indices ; eauto.
      * eapply (weaken_lookup_on_global_env' _ _ (InductiveDecl _)) ; auto.
        apply H.
      * rewrite -H0.
        apply X0 in X2 ; auto.
        apply X2.

  - rewrite H0 in H3.
    inversion H3 ; subst ; clear H3.
    eapply typing_equality => //.
    assert (All (fun d => isType Σ Γ (dtype d)) mfix).
    { eapply All_impl.
      1: exact X2.
      intros ? [].
      eexists.
      eapply infering_sort_typing ; eauto.
    }
    econstructor ; eauto.
    eapply All_impl.
    1: eapply All_mix ; [exact X2 | exact X3].
    intros ? [[s ] ].
    apply checking_typing ; auto.
    + apply All_mfix_wf ; auto.
    + exists s.
      change (tSort _) with (lift0 #|fix_context mfix| (tSort s)).
      apply weakening ; auto.
      1: by apply All_mfix_wf.
      by apply infering_sort_typing.
    
  - rewrite H0 in H3.
    inversion H3 ; subst ; clear H3.
    eapply typing_equality => //.
    assert (All (fun d => isType Σ Γ (dtype d)) mfix).
    { eapply All_impl.
      1: exact X2.
      intros ? [].
      eexists.
      eapply infering_sort_typing ; eauto.
    }
    eapply type_CoFix ; eauto.
    eapply All_impl.
    1: eapply All_mix ; [exact X2 | exact X3].
    intros ? [[s ] ].
    apply checking_typing ; auto.
    + apply All_mfix_wf ; auto.
    + exists s.
      change (tSort _) with (lift0 #|fix_context mfix| (tSort s)).
      apply weakening ; auto.
      1: by apply All_mfix_wf.
      by apply infering_sort_typing.
   
  - intros ? T' ty_T'.
    inversion ty_T'.
    move: (isdecl) => /declared_inductive_inj /(_ isdecl0) [? ?].
    subst.
    apply equality_mkApps.
    + apply equality_refl.
      1: by apply wf_local_closed_context.
      apply infering_typing, type_is_open_term in ty_T' ; auto.
      move: ty_T'.
      rewrite PCUICOnFreeVars.on_free_vars_mkApps.
      move => /andP [] -> //.
      
    + apply All2_app.
      * apply All2_skipn.
        eapply X3 ; eauto.
      * constructor ; auto.
        apply equality_refl.
        1: by apply wf_local_closed_context.
        apply infering_typing, subject_is_open_term in ty_T' ; auto.
        move: ty_T' => /= /andP [_ ] /andP [_ ] /andP [_ ] /andP [] //.

  - inversion_clear X3.
    eapply (equality_Sort_inv false).
    eapply equality_red_r_inv.
    2: eassumption.
    eapply equality_red_l_inv.
    2: eassumption.
    auto.

  - inversion_clear X3.
    eapply equality_Prod_Prod_inv.
    eapply equality_red_r_inv.
    2: eassumption.
    eapply equality_red_l_inv.
    2: eassumption.
    auto.

  - inversion_clear X3.
    eapply (@equality_Ind_inv _ _ _ false).
    eapply equality_red_r_inv.
    2: eassumption.
    eapply equality_red_l_inv.
    2: eassumption.
    auto.
Qed.

End BDUnique.

Theorem uniqueness_inferred `{checker_flags} Σ (wfΣ : wf Σ) Γ (wfΓ : wf_local Σ Γ) t T T' :
  Σ ;;; Γ |- t ▹ T -> Σ ;;; Γ |- t ▹ T' -> Σ ;;; Γ ⊢ T = T'.
Proof.
  intros.
  pose proof (bidirectional_unique Σ wfΣ) as bdu.
  repeat destruct bdu as [? bdu].
  eauto.
Qed.

Corollary principal_type `{checker_flags} Σ (wfΣ : wf Σ) Γ t T :
  Σ ;;; Γ |- t : T ->
  ∑ T',
    (forall T'', Σ ;;; Γ |- t : T'' -> Σ ;;; Γ ⊢ T' ≤ T'') × Σ ;;; Γ |- t : T'.
Proof.
  intros ty.
  assert (wf_local Σ Γ) by (eapply typing_wf_local ; eauto).
  apply typing_infering in ty as (S & infS & _); auto.
  exists S.
  repeat split.
  2: by apply infering_typing.
  intros T' ty.
  apply typing_infering in ty as (S' & infS' & cum'); auto.
  etransitivity ; eauto.
  apply equality_eq_le.
  eapply uniqueness_inferred.
  all: eauto.
Qed.








