From Coq Require Import Bool List Arith Lia.
From MetaCoq.Template Require Import config utils monad_utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICLiftSubst PCUICTyping PCUICEquality PCUICArities PCUICInversion PCUICReduction PCUICSubstitution PCUICConversion PCUICCumulativity PCUICGeneration PCUICWfUniverses PCUICContextConversion PCUICContextSubst PCUICContexts PCUICWeakening PCUICWeakeningEnv PCUICSpine PCUICWfUniverses PCUICUnivSubst PCUICUnivSubstitution PCUICClosed PCUICInductives PCUICValidity PCUICInductiveInversion PCUICSR PCUICConfluence.
From MetaCoq.Bidirectional Require Import BDEnvironmentTyping BDTyping BDToPCUIC.

Require Import ssreflect.
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

Lemma conv_Prod_inv `{cf:checker_flags} Σ Γ na na' A B A' B' :
  wf Σ.1 -> wf_local Σ Γ ->
  Σ ;;; Γ |- tProd na A B = tProd na' A' B' ->
  eq_binder_annot na na' × Σ ;;; Γ |- A = A' × Σ ;;; Γ ,, vass na' A' |- B = B'.
Proof.
  intros wfΣ wfΓ H; depind H.
  - depelim e.
    splits; auto.
    all: now constructor.

  - depelim r.
    + solve_discr.
    + specialize (IHconv _ _ _ _ _ _ wfΣ wfΓ eq_refl).
      intuition auto.
      econstructor 2; eauto.
    + specialize (IHconv _ _ _ _ _ _ wfΣ wfΓ eq_refl).
      intuition auto. apply conv_trans with N2.
      * auto.
      * eapply conv_conv_ctx; eauto.
        -- econstructor 2. 1: reflexivity.
           constructor ; auto.
      * auto.

  - depelim r.
    + solve_discr.
    + specialize (IHconv _ _ _ _ _ _ wfΣ wfΓ eq_refl).
      intuition auto.
      * econstructor 3. 2:eauto. auto.
      * eapply conv_conv_ctx in b0. 1: eauto. 1: auto.
        constructor. 1: eapply conv_ctx_refl.
        constructor; auto. eapply conv_sym; auto.
    + specialize (IHconv _ _ _ _ _ _ wfΣ wfΓ eq_refl).
      intuition auto. apply conv_trans with N2. 1-2: auto.
      eapply conv_red_r; eauto.
Qed.

Lemma conv_alt `{cf : checker_flags} Σ Γ t u :
  Σ ;;; Γ |- t = u <~> { v & { v' & red Σ Γ t v × red Σ Γ u v' × 
  eq_term Σ (global_ext_constraints Σ) v v'} }.
Proof.
  split.
  - induction 1.
    + exists t, u. intuition auto.
    + destruct IHX as (v' & v'' & redv & redv' & eqv).
      exists v', v''. intuition auto. now eapply red_step.
    + destruct IHX as (v' & v'' & redv & redv' & eqv).
      exists v', v''. intuition auto. now eapply red_step.
  - intros (v & v' & redv & redv' & Hleq).
    apply clos_rt_rt1n in redv.
    apply clos_rt_rt1n in redv'.
    induction redv.
    * induction redv'.
    ** constructor; auto.
    ** econstructor 3; eauto.
    * econstructor 2; eauto.
Qed.

Lemma invert_conv_ind_ind `{cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ}
  {Γ ind ind' u u' args args'} :
  Σ ;;; Γ |- mkApps (tInd ind u) args = mkApps (tInd ind' u') args' ->
  Reflect.eqb ind ind' ×
  PCUICEquality.R_global_instance Σ (eq_universe Σ) (eq_universe Σ) (IndRef ind) #|args| u u' × All2 (conv Σ Γ) args args'.
Proof.
  intros h.
  eapply conv_alt in h as (v & v' & redv & redv' & eqvv').
  eapply red_mkApps_tInd in redv as [l' [? ha]]; auto. subst.
  eapply eq_term_upto_univ_mkApps_l_inv in eqvv' as (v & l'' & (e & ?) & ?).
  subst.
  dependent destruction e.
  eapply red_mkApps_tInd in redv' as (?&eq&?); auto.
  solve_discr. noconf H. subst.
  repeat split.
  - apply eq_inductive_refl.
  - by rewrite (All2_length ha).
  - etransitivity.
    1:{ eapply All2_impl.
        1: eassumption.
        by apply red_conv.
    }
    etransitivity.
    1:{ eapply All2_impl.
        1: eassumption.
        by constructor.
    }
    symmetry.
    eapply All2_impl.
    1: eassumption.
    by apply red_conv.
Qed.

Lemma projection_convertible_indices {cf:checker_flags} {Σ : global_env_ext} (wfΣ : wf Σ.1) :
  forall {mdecl idecl p pdecl u u' },
  declared_projection Σ p mdecl idecl pdecl ->
  on_udecl_prop Σ (ind_universes mdecl) ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  consistent_instance_ext Σ (ind_universes mdecl) u' ->
  R_global_instance Σ (eq_universe Σ) (eq_universe Σ) (IndRef p.1.1) (ind_npars mdecl) u u' ->
  Σ ;;; projection_context mdecl idecl p.1.1 u |- 
    subst_instance u pdecl.2 = subst_instance u' pdecl.2.
Proof.
  todo "case".
Qed.


Section BDUnique.

Context `{cf : checker_flags}.
Context (Σ : global_env_ext).
Context (wfΣ : wf Σ).

Let Pinfer Γ t T :=
  wf_local Σ Γ -> forall T', Σ ;;; Γ |- t ▹ T' -> Σ ;;; Γ |- T = T'.

Let Psort Γ t u :=
  wf_local Σ Γ -> forall u', Σ ;;; Γ |- t ▹□ u' -> eq_universe Σ u u'.

Let Pprod Γ t (na : aname) A B :=
  wf_local Σ Γ -> forall na' A' B', Σ ;;; Γ |- t ▹Π (na',A',B') ->
  eq_binder_annot na na' × Σ ;;; Γ |- A = A' × Σ ;;; Γ ,, vass na' A' |- B = B'.

Let Pind Γ ind t u args :=
  wf_local Σ Γ -> forall ind' u' args', Σ ;;; Γ |- t ▹{ind'} (u',args') ->
  eqb ind ind' ×
  R_global_instance Σ (eq_universe Σ) (eq_universe Σ) (IndRef ind) #|args| u u' ×
  conv_terms Σ Γ args args'.

Let Pcheck (Γ : context) (t T : term) := True.

Let PΓ (Γ : context) := True.

Theorem bidirectional_unique : env_prop_bd Σ Pcheck Pinfer Psort Pprod Pind PΓ.
Proof.

  apply bidir_ind_env.

  all: intros ; red ; auto.
  1-9,11-13: intros ? T' ty_T' ; inversion_clear ty_T'.
  14-16: intros.

  - rewrite H in H0.
    inversion_clear H0.
    reflexivity.

  - reflexivity.

  - apply H in X2 ; auto.
    apply H0 in X3.
    2:{ constructor ; auto. apply infering_sort_typing in X ; auto. eexists. eassumption. }
    constructor. constructor.
    apply eq_universe_sort_of_product.
    all: auto.

  - apply conv_Prod_r.
    apply X1 in X4 ; auto.
    constructor ; auto.
    apply infering_sort_typing in X ; auto.
    eexists. eassumption.

  - apply conv_LetIn_bo ; auto.
    apply X2 in X6 ; auto.
    constructor ; auto.
    + apply infering_sort_typing in X ; auto. eexists. eassumption.
    + apply checking_typing ; auto. eexists. apply infering_sort_typing; eauto.

  - change Γ with (Γ ,,, subst_context [u] 0 []).

    assert (isType Σ Γ A0).
    {
      apply infering_prod_typing in X3 ; eauto.
      apply validity in X3.
      inversion X3.
      apply inversion_Prod in X5 as (?&_&?&_); auto.
      eexists.
      eassumption.
    }
    assert (subslet Σ Γ [u] [vass na0 A0]).
    {
      constructor.
      1: constructor.
      rewrite subst_empty.
      apply checking_typing ; eauto.
    }
    eapply subst_conv ; eauto.
    + constructor ; auto.
    + apply X0 in X3 as (?&?&?); eauto.
  
  - replace decl0 with decl.
    1: reflexivity.
    eapply declared_constant_inj.
    all: eauto.
  
  - replace idecl0 with idecl.
    1: reflexivity.
    eapply declared_inductive_inj.
    all: eauto.
  
  - replace cdecl0 with cdecl.
    replace mdecl0 with mdecl.
    1: reflexivity.
    2: eapply declared_constructor_inj.
    1: eapply declared_inductive_inj.
    all: eauto.
  
  - change Γ with (Γ ,,, subst_context (c :: List.rev args) 0 []).
    unfold ty, ty0 in *.
    replace mdecl0 with mdecl in * by (eapply declared_projection_inj ; eauto).
    replace idecl0 with idecl in * by (eapply declared_projection_inj ; eauto).
    replace pdecl0 with pdecl in * by (eapply declared_projection_inj ; eauto).

    assert (consistent_instance_ext Σ (ind_universes mdecl) u).
    {
      apply infering_ind_typing in X ; auto.
      apply validity in X as [] ; auto.
      eapply invert_type_mkApps_ind ; eauto.
      eapply declared_projection_inductive ; eauto.
    }

    eapply subst_conv ; eauto.

    + eapply projection_subslet ; eauto.
      2: eapply validity.
      all: eapply infering_ind_typing ; eauto.
    + eapply projection_subslet ; eauto.
      2: eapply validity.
      all: eapply infering_ind_typing ; eauto.
    + constructor.
      1: reflexivity.
      apply X0 in X2 as (?&?&?) ; auto.
      apply All2_rev.
      assumption.
    + repeat apply PCUICWeakening.weaken_wf_local ; auto.
      eapply wf_projection_context.
      all: eauto.
    + cbn -[projection_context].
      apply weaken_conv ; auto.
      * eapply closed_wf_local ; eauto.
        eapply wf_projection_context ; eauto.
      * unfold ty.
        rewrite /projection_context /= smash_context_length /= subst_instance_assumptions.
        erewrite onNpars.
        2: eapply PCUICInductives.oi ; eapply declared_projection_inductive ; eauto.
        rewrite closedn_subst_instance.
        eapply declared_projection_closed_type.
        eassumption.
      * unfold ty0.
        rewrite /projection_context /= smash_context_length /= subst_instance_assumptions.
        erewrite onNpars.
        2: eapply PCUICInductives.oi ; eapply declared_projection_inductive ; eauto.
        rewrite closedn_subst_instance.
        eapply declared_projection_closed_type.
        eassumption.
      * apply projection_convertible_indices.
        all: auto.
        -- destruct H as [[]].
           eapply (weaken_lookup_on_global_env' _ _ (InductiveDecl _)) ; eauto.
        -- apply infering_ind_typing in X2 ; auto.
          apply validity in X2 as [] ; auto.
          eapply invert_type_mkApps_ind ; eauto.
          eapply declared_projection_inductive ; eauto.
        -- apply X0 in X2 ; auto.
           rewrite -H0.
           apply X2.        

  - rewrite H0 in H3.
    inversion_clear H3.
    reflexivity.
    
  - rewrite H0 in H3.
    inversion_clear H3.
    reflexivity.
   
  - intros ? T' ty_T'.
    inversion ty_T'.
    subst.
    fold predctx1 in predctx2.
    subst predctx2.
    apply mkApps_conv_args ; auto.
    + unfold ptm, ptm0.
      apply it_mkLambda_or_LetIn_conv ; auto.
      eapply conv_context_trans ; eauto.
      apply conv_context_sym ; eauto.

    + apply All2_app.
      2: constructor ; auto.
      apply All2_skipn.
      eapply X4 ; eauto.

  - inversion_clear X3.
    assert (conv_ty : Σ ;;; Γ |- tSort u = tSort u').
    {
      etransitivity.
      1: symmetry ; apply red_conv ; eassumption.
      etransitivity.
      2: apply red_conv ; eassumption.
      apply X0 ; auto.
    }
    depind conv_ty.
    + now inversion e.
    + depelim r. solve_discr.
    + depelim r. solve_discr.
   
  - inversion_clear X3.
    assert (conv_ty : Σ ;;; Γ |- tProd na A B = tProd na' A' B').
    {
      etransitivity.
      1: symmetry ; apply red_conv ; eassumption.
      etransitivity.
      2: apply red_conv ; eassumption.
      apply X0 ; auto.
    }
    apply conv_Prod_inv; auto.

  - inversion_clear X3.
    assert (conv_ty : Σ ;;; Γ |- mkApps (tInd ind ui) args = mkApps (tInd ind' u') args'). 
    {
      etransitivity.
      1: symmetry ; apply red_conv ; eassumption.
      etransitivity.
      2: apply red_conv ; eassumption.
      apply X0 ; auto.
    }
    apply invert_conv_ind_ind ; auto.
Qed.







