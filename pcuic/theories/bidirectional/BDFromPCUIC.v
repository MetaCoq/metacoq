From Coq Require Import Bool List Arith Lia.
From MetaCoq.Template Require Import config utils monad_utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICLiftSubst PCUICTyping PCUICEquality PCUICArities PCUICInversion PCUICInductives PCUICInductiveInversion PCUICReduction PCUICSubstitution PCUICConversion PCUICCumulativity PCUICWfUniverses PCUICValidity PCUICContextConversion PCUICWeakening PCUICWeakeningEnv PCUICSpine PCUICWfUniverses PCUICUnivSubstitution PCUICClosed PCUICWellScopedCumulativity.
(* From MetaCoq.PCUIC Require Import PCUICSR. *)
From MetaCoq.PCUIC Require Import BDEnvironmentTyping BDTyping BDToPCUIC.
(** The dependency on BDToPCUIC is minimal, it is only used in conjuction with validity to avoid having to prove well-formedness of inferred types simultaneously with bidirectional -> undirected *)

Require Import ssreflect.
From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

(** Preliminary lemmata missing from MetaCoq *)
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

Lemma ctx_inst_app_impl {P Q Σ Γ} {Δ : context} {Δ' args} (c : PCUICTyping.ctx_inst P Σ Γ args (Δ ++ Δ')) :
  (forall Γ' t T, P Σ Γ' t T -> Q Σ Γ' t T) ->
  PCUICTyping.ctx_inst Q Σ Γ (firstn (context_assumptions Δ) args) Δ.
Proof.
  revert args Δ' c.
  induction Δ using ctx_length_ind; intros.
  1: constructor.
  depelim c; simpl.
  - specialize (X (subst_telescope [i] 0 Γ0) ltac:(now rewrite /subst_telescope mapi_length)).
    rewrite subst_telescope_app in c.
    specialize (X _ _ c).
    rewrite context_assumptions_subst_telescope in X.
    constructor; auto.
  - specialize (X (subst_telescope [b] 0 Γ0) ltac:(now rewrite /subst_telescope mapi_length)).
    rewrite subst_telescope_app in c.
    specialize (X _ _ c).
    rewrite context_assumptions_subst_telescope in X.
    constructor; auto.
Qed.

Lemma conv_sym `{checker_flags} Σ Γ :
  CRelationClasses.Symmetric (equality false Σ Γ).
Proof.
  intros t t' co.
  induction co.
  + constructor ; auto. by cbn ; symmetry.
  + try solve [econstructor ; eauto].
  + try solve [econstructor ; eauto].
Qed.

(** Lemmata to get checking and constrained inference from inference + cumulativity. Relies on confluence + injectivity of type constructors *)

Lemma conv_check `{checker_flags} Σ (wfΣ : wf Σ) Γ t T :
  (∑ T' : term, Σ ;;; Γ |- t ▹ T' × Σ ;;; Γ ⊢ T' ≤ T) ->
  Σ ;;; Γ |- t ◃ T.
Proof.
  intros (?&?&?).
  econstructor.
  1: eassumption.
  by apply equality_forget_cumul.
Qed.

Lemma conv_infer_sort `{checker_flags} Σ (wfΣ : wf Σ) Γ t s :
  wf_local Σ Γ ->
  Σ ;;; Γ |- t : tSort s ->
  (∑ T' : term, Σ ;;; Γ |- t ▹ T' × Σ ;;; Γ ⊢ T' ≤ tSort s) ->
  {s' & Σ ;;; Γ |- t ▹□ s' × leq_universe Σ s' s}.
Proof.
  intros ? tyt (T'&?&Cumt).
  apply equality_Sort_r_inv in Cumt as (?&?&?) ; auto.
  eexists. split ; [idtac|eassumption].
  econstructor ; [eassumption|..].
  by apply closed_red_red.
Qed.

Lemma conv_infer_prod `{checker_flags} Σ (wfΣ : wf Σ) Γ t n A B :
  wf_local Σ Γ ->
  Σ ;;; Γ |- t : tProd n A B ->
  (∑ T', (Σ ;;; Γ |- t ▹ T') × (Σ ;;; Γ ⊢ T' ≤ tProd n A B)) ->
  ∑ n' A' B', Σ ;;; Γ |- t ▹Π (n',A',B')
      × (Σ ;;; Γ ⊢ A' = A) × (Σ ;;; Γ ,, vass n A ⊢ B' ≤ B).
Proof.
  intros ? tyt (T'&?&Cumt).
  apply equality_Prod_r_inv in Cumt as (?&?&?&[]) ; auto.
  do 3 eexists. repeat split ; tea.
  econstructor ; tea.
  by eapply closed_red_red ; eauto.
Qed.

Lemma conv_infer_ind `{checker_flags} Σ (wfΣ : wf Σ) Γ t ind ui args :
  wf_local Σ Γ ->
  Σ ;;; Γ |- t : mkApps (tInd ind ui) args ->
  (∑ T', (Σ ;;; Γ |- t ▹ T') × (Σ ;;; Γ ⊢ T' ≤ mkApps (tInd ind ui) args)) ->
  ∑ ui' args', Σ ;;; Γ |- t ▹{ind} (ui',args')
      × (R_global_instance Σ (eq_universe Σ) (leq_universe Σ) (IndRef ind) #|args| ui' ui)
      × equality_terms Σ Γ args' args.
Proof.
  intros ? tyt (T'&?&Cumt).
  apply equality_Ind_r_inv in Cumt as (?&?&[]) ; auto.
  do 2 eexists. repeat split ; tea.
  econstructor ; tea.
  by eapply closed_red_red ; eauto.
Qed.

Section BDFromPCUIC.


(** The big theorem*)
Lemma bidirectional_from_pcuic `{checker_flags} :
      env_prop (fun Σ Γ t T => {T' & Σ ;;; Γ |- t ▹ T' × Σ ;;; Γ ⊢ T' ≤ T})
        (fun Σ Γ => wf_local_bd Σ Γ).
Proof.
  apply typing_ind_env.

  all: intros Σ wfΣ Γ wfΓ.

  - intros bdwfΓ.
    induction bdwfΓ.
    all: constructor ; auto.
    + apply conv_infer_sort in p ; auto.
      2: by destruct tu.
      destruct p as (?&?&?).
      eexists.
      eassumption.
    + apply conv_check in p ; auto.
      apply conv_infer_sort in p0 ; auto.
      2: by destruct tu.
      destruct p0 as (?&?&?).
      1: eexists.
      all: eassumption.
    + by apply conv_check in p.
      
  - intros.
    eexists.
    split.
    2: by eapply typing_equality ; tea ; constructor.
    constructor.
    eassumption.
    
  - intros.
    eexists.
    split.
    2: by eapply typing_equality ; tea ; constructor.
    constructor.
    assumption.

  - intros n A B ? ? ? ? CumA ? CumB.
    apply conv_infer_sort in CumA ; auto.
    destruct CumA as (?&?&?).
    apply conv_infer_sort in CumB ; auto.
    destruct CumB as (?&?&?).
    eexists.
    split.
    + constructor ; eassumption.
    + constructor ; cbn ; auto.
      1: by apply wf_local_closed_context.
      constructor.
      apply leq_universe_product_mon.
      all: assumption.
    + constructor ; [assumption|..].
      eexists ; eassumption.  

  - intros n A t ? ? ? ? CumA ? (?&?&?).
    apply conv_infer_sort in CumA ; auto.
    destruct CumA as (?&?&?).
    eexists.
    split.
    + econstructor. all: eassumption.
    + apply equality_Prod ; auto.
      eapply isType_equality_refl.
      by eexists ; eauto.

  - intros n t A u ? ? ? ? CumA ? Cumt ? (?&?&?).
    apply conv_infer_sort in CumA ; auto.
    destruct CumA as (?&?&?).
    apply conv_check in Cumt ; auto.
    eexists.
    split.
    + econstructor.
      all: eassumption.
    + apply equality_LetIn_bo.
      eassumption.

  - intros t na A B u ? ? ? ? ? Cumt ? (?&?&?).
    apply conv_infer_prod in Cumt ; auto.
    destruct Cumt as (?&?&?&?&?&?).
    eexists.
    split.
    + econstructor ; eauto.
      econstructor ; eauto.
      apply equality_forget_cumul.
      etransitivity ; eauto.
      eapply equality_le_le.
      by symmetry.
    + eapply substitution_equality_vass.
      all: eassumption.
  
  - intros.
    eexists.
    split.
    2: by eapply typing_equality ; tea ; constructor ; eauto.
    econstructor.
    all: eassumption.
    
  - intros.
    eexists.
    split.
    2: by eapply typing_equality ; tea ; econstructor ; eauto.
    econstructor.
    all: eassumption.
    
  - intros.
    eexists.
    split.
    2: by eapply typing_equality ; tea ; econstructor ; eauto.
    econstructor.
    all: eassumption.
    
  - intros ci p c brs indices ps mdecl idecl isdecl wfΣ' wfbΓ epar ? predctx wfpred ? ? ty_p Cump ? ? _ Hinst ty_c Cumc ? ? ? ty_br.

    (* assert (wf_universe Σ ps).
    { apply validity in ty_p.
      apply isType_wf_universes in ty_p; auto.
      now apply (ssrbool.elimT wf_universe_reflect) in ty_p.
    } *)

    apply conv_infer_sort in Cump as (?&?&?) ; auto.
    apply conv_infer_ind in Cumc as (?&?&?&?&?) ; auto.
    eexists.
    split.
    + econstructor.
      all: tea.
      * by eapply All_local_app_rel.
      * eapply is_allowed_elimination_monotone.
        all: eassumption.
      * rewrite subst_instance_app_ctx rev_app_distr in Hinst.
        replace (pparams p) with (firstn (context_assumptions (List.rev (subst_instance (puinst p)(ind_params mdecl)))) (pparams p ++ indices)).
        eapply ctx_inst_app_impl ; tea.
        1: intros ; by apply conv_check.
        rewrite context_assumptions_rev context_assumptions_subst_instance.
        erewrite PCUICDeclarationTyping.onNpars.
        2: eapply on_declared_minductive ; eauto.
        rewrite (firstn_app_left _ 0).
        1: by rewrite Nat.add_0_r ; destruct wfpred.
        by apply app_nil_r.

      * apply equality_forget_cumul.
        apply equality_mkApps_eq ; auto.
        
        -- by apply wf_local_closed_context.
           
        -- constructor.
           replace #|x1| with #|pparams p ++ indices|.
           1: assumption.
           symmetry.
           eapply All2_length.
           eassumption.

        -- rewrite -{1}(firstn_skipn (ci_npar ci) x1).
           apply All2_app.
           ++ replace (pparams p) with (firstn (ci_npar ci) (pparams p ++ indices)).
              1: by apply All2_firstn.
              rewrite {2}(app_nil_end (pparams p)) -(firstn_O indices).
              apply firstn_app_left.
              rewrite <- epar.
              destruct wfpred as [->].
              by apply plus_n_O.
           ++ apply All2_skipn.
              eapply All_All2.
              1: eapply All2_All_left ; tea.
              1: intros ; eapply equality_is_open_term_left ; tea.
              cbn ; intros.
              apply equality_refl ; auto.
              by apply wf_local_closed_context.

      * eapply All2i_impl.
        1: eassumption.
        intros j cdecl br (?&Hbr).
        split ; [assumption|..].
        intros brctxty.
        fold predctx in brctxty.
        fold ptm in brctxty.
        fold brctxty in Hbr.
        destruct Hbr as (?&?&?Cumbody&?&?).
        apply conv_check in Cumbody ; auto.
        split ; auto.
        by apply All_local_app_rel.

    + apply equality_mkApps ; auto.
      * apply equality_it_mkLambda_or_LetIn.
        -- apply context_equality_refl.
           unfold predctx.
           eapply wf_local_closed_context, wf_case_predicate_context ; eauto.
           eapply validity ; eassumption.
        -- apply equality_refl.
           1: eapply wf_local_closed_context, wf_case_predicate_context ; eauto.
           1: eapply validity ; eassumption.
           eapply subject_is_open_term ; tea.
      * apply All2_app.
        -- replace indices with (skipn (ci_npar ci) (pparams p ++ indices)).
           2: by apply skipn_all_app_eq ; rewrite <- epar ; destruct wfpred as [->].
           by apply All2_skipn.
        -- constructor ; auto.
           eapply equality_refl.
           1: apply wf_local_closed_context ; tea.
           eapply subject_is_open_term ; tea.

  - intros ? c u mdecl idecl [] isdecl args ? ? ? Cumc ? ty.
    apply conv_infer_ind in Cumc as (ui'&args'&?&?&?) ; auto.
    eexists.
    split.
    + econstructor.
      1-2: eassumption.
      etransitivity.
      2: eassumption.
      eapply All2_length.
      eassumption.

    + assert (Σ ;;; Γ |- c : mkApps (tInd p.1.1 ui') args') by (apply infering_ind_typing in i0 ; auto).
      assert (consistent_instance_ext Σ (ind_universes mdecl) u).
        { destruct isdecl.
          apply validity in X1 as [].
          eapply invert_type_mkApps_ind ; eauto.
        }
      assert (consistent_instance_ext Σ (ind_universes mdecl) ui').
        { destruct isdecl.
          apply validity in X2 as [] ; auto.
          eapply invert_type_mkApps_ind ; eauto.
        }
      unshelve epose proof (wf_projection_context _ _ _ _) ; eauto.
      change Γ with (Γ,,, subst_context (c :: List.rev args') 0 []).
      change 0 with #|[] : context| at 2 3.
      eapply substitution_equality_subst_conv.
      * eapply projection_subslet.
        4: eapply validity.
        all: eassumption.
      * eapply projection_subslet.
        4: eapply validity.
        all: eassumption.
      * constructor.
        2: by apply All2_rev.
        eapply equality_refl ;
          [apply wf_local_closed_context |eapply subject_is_open_term] ; tea.
      * apply wf_local_closed_context.
        apply PCUICWeakening.weaken_wf_local ; auto.
        eapply wf_projection_context ; eauto.
      * cbn -[projection_context].
        apply weaken_equality ; auto.
        1: apply wf_local_closed_context ; auto.
        change t with (i,t).2.
        eapply projection_cumulative_indices ; auto.
        1: eapply (weaken_lookup_on_global_env' _ _ _ _ (proj1 (proj1 isdecl))).
        by rewrite <- H0.

  - intros mfix n decl types ? ? ? Alltypes Allbodies.
    eexists.
    split.
    2:{
      apply isType_equality_refl.
      eapply nth_error_all in Alltypes as [? []] ; tea.
      eexists ; tea.
    }
    constructor ; eauto.
    + apply (All_impl Alltypes).
      intros ? [? [? s]].
      apply conv_infer_sort in s as [? []] ; auto.
      eexists ; eauto.
    + apply (All_impl Allbodies).
      intros ? [? s].
      by apply conv_check in s ; auto.
  
  - intros mfix n decl types ? ? ? Alltypes Allbodies.
    eexists.
    split.
    2:{
      apply isType_equality_refl.
      eapply nth_error_all in Alltypes as [? []] ; tea.
      eexists ; tea.
    }
    constructor ; eauto.
    + apply (All_impl Alltypes).
      intros ? [? [? s]].
      apply conv_infer_sort in s as [? []] ; auto.
      eexists ; eauto.
    + apply (All_impl Allbodies).
      intros ? [? s].
      by apply conv_check in s ; auto.
  
  - intros ? ? ? ? ? ? (?&?&?) ? (?&?&?) ?.
    eexists.
    split.
    1: eassumption.
    etransitivity ; eauto.
    eapply wt_cum_equality ; tea.
Qed.

End BDFromPCUIC.

(** The direct consequence on typing *)
Lemma typing_infering `{checker_flags} (Σ : global_env_ext) Γ t T (wfΣ : wf Σ) :
  Σ ;;; Γ |- t : T -> {T' & Σ ;;; Γ |- t ▹ T' × Σ ;;; Γ ⊢ T' ≤ T}.
Proof.
  intros ty.
  apply bidirectional_from_pcuic.
  all: assumption.
Qed.