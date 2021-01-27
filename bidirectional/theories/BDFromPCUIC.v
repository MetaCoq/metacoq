From Coq Require Import Bool List Arith Lia.
From MetaCoq.Template Require Import config utils monad_utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICTyping.
From MetaCoq.PCUIC Require Import PCUICEquality PCUICArities PCUICInversion PCUICInductives PCUICInductiveInversion PCUICReduction PCUICSubstitution PCUICConversion PCUICCumulativity PCUICWfUniverses PCUICValidity PCUICSR PCUICContextConversion PCUICWeakening PCUICWeakeningEnv.
From MetaCoq.Bidirectional Require Import BDEnvironmentTyping BDTyping BDToPCUIC.

Require Import ssreflect.
From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

Lemma is_allowed_elimination_monotone `{checker_flags} Σ s1 s2 allowed :
  leq_universe Σ s1 s2 -> is_allowed_elimination Σ s2 allowed -> is_allowed_elimination Σ s1 allowed.
Proof.
  intros le elim.
  unfold is_allowed_elimination in elim |- *.
  red in le.
  destruct check_univs ; auto.
  unfold is_allowed_elimination0 in elim |- *.
  intros v satisf.
  specialize (le v satisf).
  specialize (elim v satisf).
  destruct allowed ; auto.
  all: destruct (⟦s1⟧_v)%u.
  all: destruct (⟦s2⟧_v)%u.
  all: auto.
  all: red in le ; auto.
  rewrite Z.sub_0_r in le.
  apply Nat2Z.inj_le in le.
  destruct le ; auto.
Qed.

Lemma conv_infer_sort `{checker_flags} (Σ : global_env_ext) Γ t s :
  (∑ T' : term, Σ ;;; Γ |- t ▹ T' × Σ ;;; Γ |- T' <= tSort s) ->
  {s' & Σ ;;; Γ |- t ▹□ s' × leq_universe Σ s' s}.
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

Lemma conv_infer_prod `{checker_flags} (Σ : global_env_ext) (wfΣ : wf Σ) Γ t n A B:
  (∑ T', (Σ ;;; Γ |- t ▹ T') × (Σ ;;; Γ |- T' <= tProd n A B)) ->
  ∑ n' A' B', Σ ;;; Γ |- t ▹Π (n',A',B')
      × (Σ ;;; Γ |- A' = A) × (Σ ;;; Γ ,, vass n A |- B' <= B).
Proof.
  intros (?&?&Cumt).
  apply cumul_Prod_r_inv in Cumt ; auto.
  destruct Cumt as (?&?&?&((?&?)&?)&?).
  eexists. eexists. eexists. repeat split.
  1: econstructor.
  all: eassumption.
Qed.

Lemma conv_infer_ind `{checker_flags} (Σ : global_env_ext) (wfΣ : wf Σ) Γ t ind ui args :
  (∑ T', (Σ ;;; Γ |- t ▹ T') × (Σ ;;; Γ |- T' <= mkApps (tInd ind ui) args)) ->
  ∑ ui' args', Σ ;;; Γ |- t ▹{ind} (ui',args')
      × (R_global_instance Σ (eq_universe Σ) (leq_universe Σ) (IndRef ind) #|args| ui' ui)
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
        env_prop (fun Σ Γ t T => {T' & Σ ;;; Γ |- t ▹ T' × Σ ;;; Γ |- T' <= T})
         (fun Σ Γ => wf_local_bd Σ Γ).
Proof.
  apply typing_ind_env.

  all: intros Σ wfΣ Γ wfΓ.

  - intros bdwfΓ.
    induction bdwfΓ.
    all: constructor ; auto.
    + apply conv_infer_sort in p ; auto.
      destruct p as (?&?&?).
      eexists.
      eassumption.
    + apply conv_check in p ; auto.
      apply conv_infer_sort in p0 ; auto.
      destruct p0 as (?&?&?).
      1: eexists.
      all: eassumption.
    + by apply conv_check in p.
      
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

  - intros t na A B u ? ? ? ? ? Cumt ? (?&?&?).
    apply conv_infer_prod in Cumt ; auto.
    destruct Cumt as (?&?&?&?&?&?).
    eexists.
    split.
    + econstructor ; eauto.
      econstructor ; eauto.
      etransitivity ; eauto.
      apply conv_cumul.
      by symmetry.
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
    
  - intros ci p c brs indices ps mdecl idecl isdecl wfΣ' wfbΓ epar predctx wfpred ? ? ty_p Cump ? ? ty_c Cumc ? ? ? ty_br.

    assert (wf_universe Σ ps).
    { eapply validity_term in ty_p; eauto.
      apply isType_wf_universes in ty_p; auto.
      now apply (ssrbool.elimT PCUICWfUniverses.wf_universe_reflect) in ty_p.
    }

    apply conv_infer_sort in Cump as (?&?&?).
    apply conv_infer_ind in Cumc as (?&?&?&?&?) ; auto.
    eexists.
    split.
    + econstructor.
      all: try eassumption.
      * eapply is_allowed_elimination_monotone.
        all: eassumption.
      * apply cumul_mkApps_cum ; auto.
        -- constructor.
           replace #|x1| with #|pparams p ++ indices|.
           1: assumption.
           eapply All2_length.
           eassumption.

        -- rewrite -{1}(firstn_skipn (ci_npar ci) x1).
           apply All2_app.
           2: apply eq_terms_conv_terms ; reflexivity.
           symmetry.
           replace (pparams p) with (firstn (ci_npar ci) (pparams p ++ indices)).
           1: by apply All2_firstn.
           rewrite {2}(app_nil_end (pparams p)) -(firstn_O indices).
           apply firstn_app_left.
           rewrite <- epar.
           destruct wfpred as [->].
           by apply plus_n_O.

      * eapply All2i_impl.
        1: eassumption.
        intros j cdecl br Hbr brctxty.
        cbn in Hbr.
        fold predctx in brctxty.
        fold ptm in brctxty.
        fold brctxty in Hbr.
        destruct Hbr as ((?&?)&(?&?)&Cumbody&?&Cumty).
        apply conv_check in Cumbody.
        apply conv_check in Cumty.
        repeat split ; auto.
        admit. (*should use build_branches_type_wt, but it is not good enough…*)

    + apply cumul_mkApps ; auto.
      1: reflexivity.
      apply All2_app.
      2: constructor ; auto.
      replace indices with (skipn (ci_npar ci) (pparams p ++ indices)).
      1: by apply All2_skipn ; symmetry.
      apply skipn_all_app_eq.
      rewrite <- epar.
      by destruct wfpred as [->].

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

    + assert (Σ ;;; Γ |- c : mkApps (tInd p.1.1 ui') args') by (apply infering_ind_typing in i0 ; auto).
      assert (consistent_instance_ext Σ (ind_universes mdecl) u).
        { destruct isdecl.
          apply validity_term in X1 as [] ; auto.
          eapply invert_type_mkApps_ind ; eauto.
        }
      assert (consistent_instance_ext Σ (ind_universes mdecl) ui').
        { destruct isdecl.
          apply validity_term in X2 as [] ; auto.
          eapply invert_type_mkApps_ind ; eauto.
        }
      unshelve epose proof (wf_projection_context _ _ _ _) ; eauto.
      change Γ with (Γ,,, subst_context (c :: List.rev args') 0 []).
      eapply subst_cumul.
      * assumption.
      * eapply projection_subslet.
        4: eapply validity_term.
        all: eassumption.
      * eapply projection_subslet.
        4: eapply validity_term.
        all: eassumption.
      * constructor.
        1: reflexivity.
        apply All2_rev.
        symmetry.
        assumption.
      * apply wf_local_app.
        2: by constructor.
        by apply PCUICWeakening.weaken_wf_local.

      * change (Γ ,,, _ ,,, _) with (Γ,,, (projection_context mdecl idecl p.1.1 ui')).
        apply weaken_cumul ; auto.
        --by eapply PCUICClosed.closed_wf_local ; eauto.
        --simpl. len. simpl.
          rewrite (PCUICWeakeningEnv.on_declared_projection isdecl).1.(onNpars).
          rewrite PCUICClosed.closedn_subst_instance.
          change t with (i,t).2.
          eapply PCUICClosed.declared_projection_closed ; eauto.
        --simpl. len. simpl.
          rewrite (PCUICWeakeningEnv.on_declared_projection isdecl).1.(onNpars).
          rewrite PCUICClosed.closedn_subst_instance.
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
      destruct p as (?&p).
      apply conv_check in p.
      auto.
  
  - intros mfix n decl types ? ? ? Alltypes Allbodies wfmfix.
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
    etransitivity ; eauto.
Admitted.






