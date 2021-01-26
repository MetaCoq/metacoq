From Coq Require Import Bool List Arith Lia.
From MetaCoq.Template Require Import config utils monad_utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICTyping.
From MetaCoq.PCUIC Require Import PCUICEquality PCUICArities PCUICInversion PCUICInductives PCUICInductiveInversion PCUICReduction PCUICSubstitution PCUICConversion PCUICCumulativity PCUICWfUniverses PCUICValidity PCUICSR PCUICContextConversion PCUICWeakening PCUICWeakeningEnv.
From MetaCoq.Bidirectional Require Import BDEnvironmentTyping BDTyping BDToPCUIC.

Require Import ssreflect.
From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

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

Lemma conv_infer_prod `{checker_flags} (Σ : global_env_ext) (wfΣ : wf Σ) Γ t n A B:
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

Lemma conv_infer_ind `{checker_flags} (Σ : global_env_ext) (wfΣ : wf Σ) Γ t ind ui args :
  (∑ T', (Σ ;;; Γ |- t ▹ T') × (Σ ;;; Γ |- T' <= mkApps (tInd ind ui) args)) ->
  ∑ ui' args', Σ ;;; Γ |- t ▸{ind} (ui',args')
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

Definition non_cumul (Σ : global_env) :=
  Forall (fun d => match d.2 with | InductiveDecl m => ind_variance m = None | _ => True end) Σ.

Lemma build_case_predicate_conv : forall `{cf : checker_flags} Σ (wfΣ : wf Σ) Γ ind mdecl idecl params params' u u' ps pty,
  declared_inductive Σ.1 mdecl ind idecl ->
  conv_terms Σ Γ params params' -> R_universe_instance (eq_universe Σ) u u' ->
  build_case_predicate_type ind mdecl idecl params u ps = Some pty ->
  {pty' & build_case_predicate_type ind mdecl idecl params' u' ps = Some pty' × Σ ;;; Γ |- pty = pty'}.
Admitted.


  Lemma typing_infering `{checker_flags} :
        env_prop (fun Σ Γ t T => {T' & Σ ;;; Γ |- t ▹ T' × Σ ;;; Γ |- T' <= T})
         (fun Σ Γ _ => wf_local_bd Σ Γ).
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
    
  - intros ind u npar p c brs args mdecl idecl isdecl wfΣ' wfbΓ ? params ps pty pred ty_p Cump ? ? ? Cumc ? ? ty_br.

    assert (∑ pctx, destArity [] pty =  Some (pctx, ps)) as [? ari].
    { unshelve eapply (build_case_predicate_type_spec (Σ.1, ind_universes mdecl)) in pred as [parsubst [_ ->]].
      1: eapply (on_declared_inductive) in isdecl as [? ?] ; eauto.
      eexists. rewrite !destArity_it_mkProd_or_LetIn; simpl. reflexivity. }

    assert (wf_universe Σ ps).
    { eapply validity in ty_p; eauto.
      apply isType_wf_universes in ty_p; auto.
      apply destArity_spec_Some in ari.
      cbn in ari.
      subst pty.
      rewrite wf_universes_it_mkProd_or_LetIn in ty_p.
      move/andb_and: ty_p => [_ ty_p].
      now apply (ssrbool.elimT PCUICWfUniverses.wf_universe_reflect) in ty_p.
    }

    apply conv_check in Cump.
    apply conv_infer_ind in Cumc as (?&?&?&?&?) ; auto.
    eexists.
    split.
    + econstructor.
      * eassumption.
      * eassumption.
      * eassumption.
      * eassumption.
      * admit. (*build_case_predicate_type on convertible arguments*)
      * eassumption.
      * eassumption.
      * eassumption.
      * admit. (*build_brandches_type on convertible arguments*)
      * clear -ty_br.
        induction ty_br.
        1:
        admit. (*all branches are well-typed*)
    + apply cumul_mkApps ; auto.
      1: reflexivity.
      apply All2_app.
      2: constructor ; auto.
      symmetry.
      apply All2_skipn.
      assumption.

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
        by apply weaken_wf_local.

      * change (Γ ,,, _ ,,, _) with (Γ,,, (projection_context mdecl idecl p.1.1 ui')).
        apply weaken_cumul ; auto.
        --by eapply PCUICClosed.closed_wf_local ; eauto.
        --simpl. len. simpl.
          rewrite (PCUICWeakeningEnv.on_declared_projection _ isdecl).1.(onNpars).
          rewrite PCUICClosed.closedn_subst_instance_constr.
          change t with (i,t).2.
          eapply PCUICClosed.declared_projection_closed ; eauto.
        --simpl. len. simpl.
          rewrite (PCUICWeakeningEnv.on_declared_projection _ isdecl).1.(onNpars).
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
    eapply cumul_trans ; eauto.

Admitted.






