From Coq Require Import Bool List Arith Lia.
From MetaCoq.Template Require Import config utils monad_utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICTyping PCUICInversion PCUICInductiveInversion PCUICEquality.
From MetaCoq.PCUIC Require Import PCUICWeakening PCUICClosed PCUICSubstitution PCUICPrincipality PCUICValidity PCUICCumulativity PCUICInductives PCUICWfUniverses PCUICSR PCUICWeakeningEnv PCUICContexts.
From MetaCoq.Bidirectional Require Import BDEnvironmentTyping BDTyping.
From MetaCoq.SafeChecker Require Import PCUICSafeRetyping.

Require Import ssreflect.
From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.

Lemma All2i_mix (A B : Type) (P Q : nat -> A -> B -> Type) (n : nat) (l : list A) (l' : list B) :
  All2i P n l l' -> All2i Q n l l' -> All2i (fun i x y => (P i x y) × (Q i x y)) n l l'.
Proof.
  intros AP.
  dependent induction AP.
  1: constructor.
  intros AQ.
  inversion_clear AQ.
  constructor ; auto.
Qed.

Lemma All_local_env_app_l P Γ Γ' : All_local_env P (Γ ,,, Γ') -> All_local_env P Γ.
Proof.
  induction Γ'.
  1: auto.
  cbn.
  intros all.
  inversion all ; auto.
Qed.

Lemma wf_local_rel_subst1 `{checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} Δ Γ na b t Γ' :
      wf_local_rel Σ Δ (Γ ,,, [],, vdef na b t ,,, Γ') ->
      wf_local_rel Σ Δ (Γ ,,, subst_context [b] 0 Γ').
Proof.
  induction Γ' as [|d Γ']; [now inversion 1|].
  change (d :: Γ') with (Γ' ,, d).
  destruct d as [na' [bd|] ty]; rewrite !app_context_cons; intro HH.
  - rewrite subst_context_snoc0. simpl.
    inversion HH; subst; cbn in *. destruct X0 as [s X0].
    change (Γ,, vdef na b t ,,, Γ') with (Γ ,,, [vdef na b t] ,,, Γ') in *.
    assert (subslet Σ (Δ ,,, Γ) [b] [vdef na b t]). {
      pose proof (cons_let_def Σ (Δ ,,, Γ) [] [] na b t) as XX.
      rewrite !subst_empty in XX. apply XX. constructor.
      apply All_local_env_app_l in X. inversion X; subst; cbn in * ; assumption.
    }
    constructor; cbn; auto.
    1: apply IHΓ' ; exact X.
    1: exists s.
    1: change (tSort s) with (subst [b] #|Γ'| (tSort s)).
    all: rewrite app_context_assoc.
    all: eapply substitution; tea.
    1: rewrite !app_context_assoc in X0 ; assumption.
    rewrite !app_context_assoc in X1 ; assumption.
  - rewrite subst_context_snoc0. simpl.
    inversion HH; subst; cbn in *. destruct X0 as [s X0].
    change (Γ,, vdef na b t ,,, Γ') with (Γ ,,, [vdef na b t] ,,, Γ') in *.
    assert (subslet Σ (Δ ,,, Γ) [b] [vdef na b t]). {
      pose proof (cons_let_def Σ (Δ ,,, Γ) [] [] na b t) as XX.
      rewrite !subst_empty in XX. apply XX. constructor.
      apply All_local_env_app_l in X. inversion X; subst; cbn in *; assumption. }
    constructor; cbn; auto.
    1: apply IHΓ' ; exact X.
    exists s.
    change (tSort s) with (subst [b] #|Γ'| (tSort s)).
    rewrite app_context_assoc.
    all: eapply substitution; tea.
    rewrite !app_context_assoc in X0. eassumption.
Qed.

Lemma wf_rel_weak `{checker_flags} (Σ : global_env_ext) (wfΣ : wf Σ) Γ (wfΓ : wf_local Σ Γ) Γ' :
  wf_local Σ Γ' -> wf_local_rel Σ Γ Γ'.
Proof.
  induction Γ' as [|[? []] ?].
  - by constructor.
  - intros wfl. inversion_clear wfl.
    constructor.
    + apply IHΓ'. assumption.
    + destruct X0.
      eexists.
      apply weaken_ctx ; eauto.
    + apply weaken_ctx ; auto.
  - intros wfl. inversion_clear wfl.
    constructor.
    + apply IHΓ'. assumption.
    + destruct X0.
      eexists.
      apply weaken_ctx ; eauto.
Qed.      

Lemma wf_rel_def `{checker_flags} Σ Γ na i t Δ : wf_local_rel Σ (Γ ,, vass na t) Δ -> wf_local_rel Σ (Γ ,, vdef na i t) Δ.
Proof.
  intros.
  eapply All_local_env_impl.
  1: eassumption.
  intros Γ' t' [] ty ; cbn in *.
Admitted.


Section BDToPCUICTyping.

  Context `{cf : checker_flags}.
  Context (Σ : global_env_ext).
  Context (wfΣ : wf Σ).

  Let Pcheck Γ t T :=
    wf_local Σ Γ -> isType Σ Γ T -> Σ ;;; Γ |- t : T.

  Let Pinfer Γ t T :=
    wf_local Σ Γ -> Σ ;;; Γ |- t : T.

  Let Psort Γ t u :=
    wf_local Σ Γ -> Σ ;;; Γ |- t : (tSort u).

  Let Pprod Γ t na A B :=
    wf_local Σ Γ -> Σ ;;; Γ |- t : tProd na A B.

  Let Pind Γ ind t u args :=
    wf_local Σ Γ -> Σ ;;; Γ |- t : mkApps (tInd ind u) args.

  Let PΓ Γ :=
    wf_local Σ Γ.

Lemma bd_wf_local Γ (all: wf_local_bd Σ Γ) :
  All_local_env_over_sorting checking infering_sort 
    (fun Σ Γ _ t T _ => Pcheck Γ t T)
    (fun Σ Γ _ t u _ => Psort Γ t u) 
    Σ Γ all ->
  wf_local Σ Γ.
Proof.
  intros allo ; induction allo.
  all: constructor.
  1,3: assumption.
  all: red.
  - simpl in tu. eexists.
    auto.
  - destruct tu. eexists.
    auto.
  - destruct tu.
    apply c ; auto.
    eexists. red. auto.
Qed.

Lemma type_local_ctx_impl Γ Δ u (wfΓ : wf_local Σ Γ):
  type_local_ctx (lift_sorting (fun _ => Pcheck) (fun _ => Psort)) Σ Γ Δ u -> type_local_ctx (lift_typing typing) Σ Γ Δ u.
Proof.
  intros HΔ.
  induction Δ as [|[? []]].
  1: auto.
  all: simpl.
  1: destruct HΔ as (?&[]&?).
  2: destruct HΔ.
  all: have wfΓΔ : wf_local Σ (Γ ,,, Δ) by eapply type_local_ctx_wf_local ; eauto.
  all: repeat split ; auto.
  - eexists. eauto.
  - apply l.
    2: eexists ; eapply p.
    all: eauto.
  - apply l.
    1: assumption.
    eexists.
    constructor ; auto.
    clear - t.
    induction Δ as [|[? []]].
    1: assumption.
    all: intuition.
Qed.


Lemma ctx_inst_impl Γ (wfΓ : wf_local Σ Γ) (Δ : context) (wfΔ : wf_local_rel Σ Γ (List.rev Δ)) : 
  forall args, ctx_inst (fun _ => Pcheck) Σ Γ args Δ -> ctx_inst typing Σ Γ args Δ.
Proof.
  revert wfΔ.
  induction Δ using PCUICInduction.ctx_length_ind.
  1: intros _ ? d ; inversion_clear d ; constructor.
  intros wfΔ args ctxi ; inversion ctxi.
  - subst d.
    subst.
    assert (isType Σ Γ t).
    {
      eapply wf_local_rel_app_inv in wfΔ as [wfd _].
      inversion_clear wfd.
      eassumption.
    }
    constructor ; auto.
    apply X ; auto.
    1: by rewrite PCUICSpine.subst_telescope_length ; reflexivity.
    rewrite -(rev_involutive Γ0) -PCUICSpine.subst_context_telescope.
    rewrite <- app_nil_r.
    eapply wf_local_rel_subst1.
    cbn in wfΔ |- *.
    eapply wf_local_rel_app.
    + econstructor ; eauto.
      1: destruct X2 ; eexists ; eauto.
      eapply X0 ; auto.
    + apply wf_local_rel_app_inv in wfΔ as [_ ?].
      apply wf_rel_def.
      eassumption.
      
  - subst d.
    subst.
    assert (isType Σ Γ t).
    {
      eapply wf_local_rel_app_inv in wfΔ as [wfd _].
      inversion_clear wfd.
      eassumption.
    }
    constructor ; auto.
    apply X ; auto.
    1: by rewrite PCUICSpine.subst_telescope_length ; reflexivity.
    rewrite -(rev_involutive Γ0) -PCUICSpine.subst_context_telescope.
    rewrite <- app_nil_r.
    eapply wf_local_rel_subst1.
    cbn in wfΔ |- *.
    eassumption.
Qed.
  
Theorem bidirectional_to_PCUIC : env_prop_bd Σ Pcheck Pinfer Psort Pprod Pind PΓ.
Proof.
  apply bidir_ind_env.

  { intros. eapply bd_wf_local. eassumption. }

  - red ; intros ; econstructor ; eauto.

  - red ; intros ; econstructor ; eauto.

  - red ; intros ; econstructor ; eauto.
    apply X2.
    constructor. 1: by auto.
    eexists. eauto.

  - red ; intros ; econstructor ; eauto.
    apply X2.
    constructor. 1: by auto.
    eexists. eauto.
  
  - red ; intros ; econstructor ; eauto.
    + apply X2 ; auto.
      eexists.
      red. eauto.
  
    + apply X4.
      constructor ; auto.
      * eexists. eauto.
      * apply X2 ; auto. eexists. red. eauto.
  
  - red ; intros.
    eapply type_App' ; auto.
    apply X2 ; auto.
    specialize (X0 X3).
    apply validity in X0 as [? X0].
    apply inversion_Prod in X0 as (? & ? & ? & _).
    2: done.
    eexists. eassumption.

  - red ; intros ; econstructor ; eauto.

  - red ; intros ; econstructor ; eauto.

  - red ; intros ; econstructor ; eauto.

  - intros ; intro.

    assert (cparams : ctx_inst typing Σ Γ (pparams p) (List.rev (subst_instance (puinst p) (ind_params mdecl)))).
    { apply ctx_inst_impl ; auto.
      rewrite rev_involutive.
      apply wf_rel_weak ; auto.
      
      apply (PCUICUnivSubstitution.wf_local_subst_instance_decl _ _ (inductive_mind ci) (InductiveDecl mdecl)) ; eauto.
      - by destruct isdecl.
      - eapply wf_local_app_inv.
        eapply on_minductive_wf_params_indices ; eauto.
    }

    assert (cindices : ctx_inst typing Σ Γ (skipn (ci_npar ci) args) (subst_telescope (PCUICSpine.ctx_inst_sub cparams) 0
       (List.rev (subst_instance (puinst p) (ind_indices idecl))))).
    {
      apply validity in X7 as [? ty_args] ; auto.
      eapply invert_type_mkApps_ind in ty_args as [ty_args _] ; eauto.
      admit.
    }

    assert (cpar_ind :
      ctx_inst typing Σ Γ (pparams p ++ skipn (ci_npar ci) args) (List.rev (subst_instance (puinst p) (ind_params mdecl ,,, ind_indices idecl)))).
    {
      admit.
    }

    assert (isType Σ Γ (mkApps (tInd ci (puinst p)) (pparams p ++ skipn (ci_npar ci) args))) as [].
    {
      eexists.
      eapply type_mkApps_arity.
      1: econstructor ; eauto.
      erewrite PCUICDeclarationTyping.ind_arity_eq.
      2: by eapply PCUICInductives.oib ; eauto.
      rewrite !PCUICUnivSubst.subst_instance_it_mkProd_or_LetIn.
      eapply PCUICSpine.arity_spine_it_mkProd_or_LetIn ; auto.
      - unshelve apply PCUICSpine.ctx_inst_spine_subst ; auto.
        apply PCUICWeakening.weaken_wf_local ; auto.
        eapply PCUICArities.on_minductive_wf_params ; eauto.
      - cbn.
        rewrite subst_it_mkProd_or_LetIn.
        cbn.
        eapply PCUICSpine.arity_spine_it_mkProd_or_LetIn_Sort.
        1: by eapply on_inductive_sort_inst ; eauto.
        1: reflexivity.
      
        rewrite PCUICSpine.subst_context_telescope.
        unshelve apply PCUICSpine.ctx_inst_spine_subst ; auto.
        1:{
          apply validity in X7  as [? ty_args]; auto.
          eapply invert_type_mkApps_ind in ty_args as [] ; eauto.
          rewrite rev_involutive.
          assumption.
        }

        rewrite <- PCUICSpine.subst_context_telescope.
        eapply substitution_wf_local ; auto.
        * eapply PCUICSpine.inst_subslet.
          apply PCUICSpine.ctx_inst_spine_subst ; auto.
          apply PCUICWeakening.weaken_wf_local ; auto.
          eapply wf_local_app_inv.
          rewrite <- PCUICUnivSubstitution.subst_instance_app_ctx.
          eapply on_minductive_wf_params_indices_inst ; eauto.
        * rewrite <- app_context_assoc.
          apply PCUICWeakening.weaken_wf_local ; auto.
          rewrite <- PCUICUnivSubstitution.subst_instance_app_ctx.
          eapply on_minductive_wf_params_indices_inst ; eauto.
    }

    econstructor ; eauto.
    1: by eapply type_Cumul ; eauto.

    eapply All2i_impl.
    1:{ apply All2i_mix ; [eassumption|idtac].
        eapply build_branches_type_wt ; eauto.
        econstructor.
        3: eassumption.
        all: eauto.
    }
    intros * Hprod ?.
    fold predctx in brctxty.
    fold ptm in brctxty.
    cbv beta zeta in Hprod.
    fold brctxty in Hprod.
    destruct Hprod as ((?&?&?&?&?&?&Hbody)&?).
    repeat split.
    all: auto.
    apply Hbody ; auto.
    eexists.
    eassumption.
      
  - red ; intros ; econstructor ; eauto.

  - red ; intros ; econstructor ; eauto.

    + clear H H0 H1 X0.
      induction X.
      all: constructor ; auto.
      destruct p as (? & ? & ?).
      eexists.
      apply p.
      auto.

    + have Htypes : All (fun d => isType Σ Γ (dtype d)) mfix.
      { clear H H0 H1 X0.
        induction X.
        all: constructor ; auto.
        destruct p as (? & ? & ?).
        eexists.
        apply p.
        auto.
      }
      have wfΓ' : wf_local Σ (Γ,,,fix_context mfix) by apply All_mfix_wf.

      remember (fix_context mfix) as Γ'.
      clear H H0 H1 HeqΓ'.
      induction X0.
      all: constructor ; auto.
      2:{ inversion_clear X. apply IHX0 ; auto. inversion_clear Htypes. auto. }
      destruct p.
      apply p ; auto.
      inversion_clear Htypes as [| ? ? [u]].
      exists u.
      change (tSort u) with (lift0 #|Γ'| (tSort u)).
      apply weakening.
      all: auto.

  - red ; intros ; econstructor ; eauto.
    + clear H H0 H1 X0.
      induction X.
      all: constructor ; auto.
      destruct p as (? & ? & ?).
      eexists.
      apply p.
      auto.

    + have Htypes : All (fun d => isType Σ Γ (dtype d)) mfix.
      { clear H H0 H1 X0.
        induction X.
        all: constructor ; auto.
        destruct p as (? & ? & ?).
        eexists.
        apply p.
        auto.
      }
      have wfΓ' : wf_local Σ (Γ,,,fix_context mfix) by apply All_mfix_wf ; auto.
      remember (fix_context mfix) as Γ'.
      clear H H0 H1 HeqΓ'.
      induction X0.
      all: constructor ; auto.
      2:{ inversion_clear X. apply IHX0 ; auto. inversion_clear Htypes. auto. }
      destruct p.
      apply p ; auto.
      inversion_clear Htypes as [| ? ? [u]].
      exists u.
      change (tSort u) with (lift0 #|Γ'| (tSort u)).
      apply weakening.
      all: auto.

  - red ; intros ; econstructor ; eauto.
    2: by apply red_cumul.
    constructor ; auto.
    eapply isType_Sort_inv.
    1: done.
    eapply isType_red.
    2: eassumption.
    eapply validity.
    eauto.
  
  - red ; intros.
    have [] : (isType Σ Γ (tProd na A B)).
    { eapply isType_red.
      2: eassumption.
      eapply validity.
      eauto.
    }
    econstructor.
    + by auto.
    + by eassumption.
    + by apply red_cumul. 
  
  - red ; intros.
    have [] : (isType Σ Γ (mkApps (tInd ind ui) args)).
    { eapply isType_red.
      2: eassumption.
      eapply validity.
      eauto.
    }

    econstructor.
    + by auto.
    + by eassumption.
    + by apply red_cumul. 

  - intros. red. intros ? [].
    econstructor.
    all:by eauto.

Admitted.

End BDToPCUICTyping.

Theorem infering_typing `{checker_flags} (Σ : global_env_ext) Γ t T (wfΣ : wf Σ) :
  wf_local Σ Γ -> Σ ;;; Γ |- t ▹ T -> Σ ;;; Γ |- t : T.
Proof.
  intros.
  apply bidirectional_to_PCUIC.
  all: assumption.
Qed.

Theorem checking_typing `{checker_flags} (Σ : global_env_ext) Γ t T (wfΣ : wf Σ) :
  wf_local Σ Γ -> isType Σ Γ T -> Σ ;;; Γ |- t ◃ T -> Σ ;;; Γ |- t : T.
Proof.
  intros wfΓ HT Ht. revert wfΓ HT.
  apply bidirectional_to_PCUIC.
  all: assumption.
Qed.

Theorem infering_sort_typing `{checker_flags} (Σ : global_env_ext) Γ t u (wfΣ : wf Σ) :
  wf_local Σ Γ -> Σ ;;; Γ |- t ▹□ u -> Σ ;;; Γ |- t : tSort u.
Proof.
  intros wfΓ Ht. revert Ht wfΓ.
  apply bidirectional_to_PCUIC.
  assumption.
Qed.

Theorem infering_prod_typing `{checker_flags} (Σ : global_env_ext) Γ t na A B (wfΣ : wf Σ) :
  wf_local Σ Γ -> Σ ;;; Γ |- t ▹Π (na,A,B) -> Σ ;;; Γ |- t : tProd na A B.
Proof.
  intros wfΓ Ht. revert Ht wfΓ.
  apply bidirectional_to_PCUIC.
  assumption.
Qed.

Theorem infering_ind_typing `{checker_flags} (Σ : global_env_ext) Γ t ind u args (wfΣ : wf Σ) :
wf_local Σ Γ -> Σ ;;; Γ |- t ▹{ind} (u,args) -> Σ ;;; Γ |- t : mkApps (tInd ind u) args.
Proof.
  intros wfΓ Ht. revert Ht wfΓ.
  apply bidirectional_to_PCUIC.
  assumption.
Qed.

Theorem wf_local_bd_typing `{checker_flags} (Σ : global_env_ext) Γ (wfΣ : wf Σ) :
  wf_local_bd Σ Γ -> wf_local Σ Γ.
Proof.
  apply bidirectional_to_PCUIC.
  assumption.
Qed.