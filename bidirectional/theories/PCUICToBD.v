From Coq Require Import Bool List Arith Lia.
From MetaCoq.Template Require Import config utils monad_utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICLiftSubst PCUICTyping.
From MetaCoq.PCUIC Require Import PCUICEquality PCUICArities PCUICInversion PCUICInductives PCUICInductiveInversion PCUICReduction PCUICSubstitution PCUICConversion PCUICCumulativity PCUICWfUniverses PCUICValidity PCUICSR PCUICContextConversion.
From MetaCoq.Bidirectional Require Import BDEnvironmentTyping BDMinimalTyping BDMinimalToPCUIC.

Require Import ssreflect.
From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.
     

Lemma conv_infer_sort `{checker_flags} (Σ : global_env_ext) Γ t s :
  (∑ T' : term, Σ ;;; Γ |- t ▹ T' × Σ ;;; Γ |- T' <= tSort s) ->
  {s' & Σ ;;; Γ |- t ▸□ s' × leq_universe Σ s' s}.
Proof.
  intros (?&?&Cumt).
  apply cumul_Sort_r_inv in Cumt ; auto.
  destruct Cumt as (?&?&?).
  eexists. split.
  1: econstructor.
  all: eassumption.
Qed.

Lemma conv_check `{checker_flags} (Σ : global_env_ext) Γ t T :
  (∑ T' : term, Σ ;;; Γ |- t ▹ T' × Σ ;;; Γ |- T' <= T) ->
  Σ ;;; Γ |- t ◃ T.
Proof.
  intros (?&?&Cumt).
  econstructor.
  all: eassumption.
Qed.

Lemma conv_infer_prod `{checker_flags} (Σ : global_env_ext) (wfΣ : PT.wf Σ) Γ t n A B:
  (∑ T', (Σ ;;; Γ |- t ▹ T') × (Σ ;;; Γ |- T' <= tProd n A B)) ->
  ∑ n' A' B', Σ ;;; Γ |- t ▸Π (n',A',B')
      × (Σ ;;; Γ |- A' = A) × (Σ ;;; Γ ,, vass n A |- B' <= B).
Proof.
  intros (?&?&Cumt).
  apply cumul_Prod_r_inv in Cumt ; auto.
  destruct Cumt as (?&?&?&((?&?)&?)&?).
  eexists. eexists. eexists. repeat split.
  1: econstructor.
  all: eassumption.
Qed.

Lemma conv_infer_ind `{checker_flags} (Σ : global_env_ext) (wfΣ : PT.wf Σ) Γ t ind ui args :
  (∑ T', (Σ ;;; Γ |- t ▹ T') × (Σ ;;; Γ |- T' <= mkApps (tInd ind ui) args)) ->
  ∑ ui' args', Σ ;;; Γ |- t ▸{ind} (ui',args')
      × (PCUICEquality.R_global_instance Σ (eq_universe Σ) (leq_universe Σ) (IndRef ind) #|args| ui' ui)
      × (All2 (fun a a' => Σ ;;; Γ |- a = a') args args').
Proof.
  intros (?&?&Cumt).
  apply invert_cumul_ind_r in Cumt ; auto.
  destruct Cumt as (?&?&?&?&?).
  eexists. eexists. repeat split.
  1: econstructor.
  all:eassumption.
Qed.

Section PCUICToBD.

Lemma typing_infering `{checker_flags} :
        PT.env_prop (fun Σ Γ t T => {T' & Σ ;;; Γ |- t ▹ T' × Σ ;;; Γ |- T' <= T})
         (fun Σ Γ _ => MT.wf_local Σ Γ).
Proof.
  apply PT.typing_ind_env.

  all: intros Σ wfΣ Γ wfΓ.

  - intros MTwfΓ.
    induction MTwfΓ.
    all: constructor ; auto.
    + apply conv_infer_sort in p ; auto.
      destruct p as (?&?&?).
      eexists.
      eassumption.
    + apply conv_check in p ; auto.
      apply conv_infer_sort in p0 ; auto.
      destruct p0 as (?&?&?).
      split.
      1: eexists.
      all: eassumption.
  
  - intros.
    eexists.
    split.
    2: by reflexivity.
    constructor.
    eassumption.
    
  - intros.
    eexists.
    split.
    2: by reflexivity.
    constructor. assumption.

  - intros n A B ? ? ? ? CumA ? CumB.
    apply conv_infer_sort in CumA ; auto.
    destruct CumA as (?&?&?).
    apply conv_infer_sort in CumB ; auto.
    destruct CumB as (?&?&?).
    eexists.
    split.
    + constructor ; eassumption.
    + constructor.
      constructor.
      apply leq_universe_product_mon.
      all: assumption.

  - intros n A t ? ? ? ? CumA ? (?&?&?).
    apply conv_infer_sort in CumA ; auto.
    destruct CumA as (?&?&?).
    eexists.
    split.
    + econstructor. all: eassumption.
    + apply congr_cumul_prod.
      all: by auto.

  - intros n t A u ? ? ? ? CumA ? Cumt ? (?&?&?).
    apply conv_infer_sort in CumA ; auto.
    destruct CumA as (?&?&?).
    apply conv_check in Cumt ; auto.
    eexists.
    split.
    + econstructor.
      all: eassumption.
    + apply cumul_LetIn_bo.
      eassumption.

  - intros t na A B u ? ? Cumt ? (?&?&?).
    apply conv_infer_prod in Cumt ; auto.
    destruct Cumt as (?&?&?&?&?&?).
    eexists.
    split.
    + econstructor ; eauto.
      econstructor ; eauto.
      eapply cumul_trans ; eauto.
      apply conv_cumul.
      by apply conv_sym.
    + eapply substitution_cumul0.
      all: eassumption.
  
  - intros.
    eexists.
    split.
    2: by reflexivity.
    econstructor.
    all: eassumption.
    
  - intros.
    eexists.
    split.
    2: by reflexivity.
    econstructor.
    all: eassumption.
    
  - intros.
    eexists.
    split.
    2: reflexivity.
    econstructor.
    all: eassumption.
    
  - admit.


  - intros ? c u mdecl idecl [] isdecl args ? ? ? Cumc ? ty.
    apply conv_infer_ind in Cumc as (ui'&args'&?&?&?) ; auto.
    eexists.
    split.
    + econstructor.
      1-2: eassumption.
      etransitivity.
      2: eassumption.
      symmetry.
      eapply All2_length.
      eassumption.

    + assert (Σ ;;; Γ |- c : mkApps (tInd p.1.1 ui') args').
      { apply infering_ind_typing in i0 ; auto. admit. }
      assert (PT.consistent_instance_ext Σ (ind_universes mdecl) u).
        { destruct isdecl.
          apply validity_term in X1 as [] ; auto.
          eapply PCUICInductives.invert_type_mkApps_ind ; eauto.
        }
      assert (PT.consistent_instance_ext Σ (ind_universes mdecl) ui').
        { destruct isdecl.
          apply validity_term in X2 as [] ; auto.
          eapply PCUICInductives.invert_type_mkApps_ind ; eauto.
        }
      unshelve epose proof (PCUICInductives.wf_projection_context _ _ _ _) ; eauto.
      change Γ with (Γ,,, subst_context (c :: List.rev args') 0 []).
      eapply subst_cumul.
      * assumption.
      * eapply PCUICInductives.projection_subslet.
        4: eapply validity_term.
        all: eassumption.
      * eapply PCUICInductives.projection_subslet.
        4: eapply validity_term.
        all: eassumption.
      * constructor.
        1: reflexivity.
        apply All2_rev.
        symmetry.
        assumption.
      * repeat apply PCUICWeakening.weaken_wf_local.
        all: auto.

      * change (Γ ,,, _ ,,, _) with (Γ,,, (PCUICInductives.projection_context mdecl idecl p.1.1 ui')).
        apply weaken_cumul ; auto.
        --by eapply PCUICClosed.closed_wf_local ; eauto.
        --simpl. len. simpl.
          rewrite (PCUICWeakeningEnv.on_declared_projection _ isdecl).1.(PT.onNpars).
          rewrite PCUICClosed.closedn_subst_instance_constr.
          change t with (i,t).2.
          eapply PCUICClosed.declared_projection_closed ; eauto.
        --simpl. len. simpl.
          rewrite (PCUICWeakeningEnv.on_declared_projection _ isdecl).1.(PT.onNpars).
          rewrite PCUICClosed.closedn_subst_instance_constr.
          change t with (i,t).2.
          eapply PCUICClosed.declared_projection_closed ; eauto.
        --eapply projection_cumulative_indices ; auto.
          1: eapply (PCUICWeakeningEnv.weaken_lookup_on_global_env' _ _ _ _ (proj1 (proj1 isdecl))).
          by rewrite <- H0.

  - intros mfix n decl types ? ? ? Alltypes Allbodies.
    eexists.
    split.
    2: reflexivity.
    constructor ; eauto.
    + clear -Alltypes.
      induction Alltypes.
      all: constructor ; auto.
      destruct p as (?&_&p).
      apply conv_infer_sort in p as (?&?&?).
      eexists. eassumption.
    + clear -Allbodies.
      fold types.
      clearbody types.
      induction Allbodies.
      all: constructor ; auto.
      destruct p as ((_&?)&p).
      apply conv_check in p.
      split ; auto.
  
  - intros mfix n decl types ? ? ? Alltypes Allbodies.
    eexists.
    split.
    2: reflexivity.
    constructor ; eauto.
    + clear -Alltypes.
      induction Alltypes.
      all: constructor ; auto.
      destruct p as (?&_&p).
      apply conv_infer_sort in p as (?&?&?).
      eexists. eassumption.
    + clear -Allbodies.
      fold types.
      clearbody types.
      induction Allbodies.
      all: constructor ; auto.
      destruct p as (_&p).
      by apply conv_check in p.
  
  - intros ? ? ? ? ? ? (?&?&?) ? (?&?&?) ?.
    eexists.
    split.
    1: eassumption.
    eapply cumul_trans ; eauto.

Admitted.






