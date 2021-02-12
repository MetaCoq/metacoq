From Coq Require Import Bool List Arith Lia.
From MetaCoq.Template Require Import config utils monad_utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICLiftSubst PCUICTyping PCUICInversion PCUICInductives PCUICInductiveInversion PCUICEquality PCUICUnivSubst PCUICUnivSubstitution PCUICWeakening PCUICClosed PCUICSubstitution PCUICValidity PCUICCumulativity PCUICInductives PCUICWfUniverses PCUICSR PCUICWeakeningEnv PCUICContexts PCUICSpine.
From MetaCoq.PCUIC Require Import BDEnvironmentTyping BDTyping.

Require Import ssreflect.
From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.

(** Various generic lemmatas missing from the MetaCoq library *)

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

Lemma wf_local_local_rel `{checker_flags} Σ Γ Γ' : wf_local Σ (Γ ,,, Γ') -> wf_local_rel Σ Γ Γ'.
Proof.
  induction Γ'.
  1: constructor.
  cbn.
  intros wfΓ.
  inversion_clear wfΓ.
  all: constructor ; auto.
  all: apply IHΓ' ; eassumption.
Qed.


Section BDToPCUICTyping.

  (** We work in a fixed, well-formed global environment*)

  Context `{cf : checker_flags}.
  Context (Σ : global_env_ext).
  Context (wfΣ : wf Σ).

  (** The predicates we wish to prove, note the extra well-formedness hypothesis depending on the modding of the judgement *)

  Let Pinfer Γ t T :=
    wf_local Σ Γ -> Σ ;;; Γ |- t : T.

  Let Psort Γ t u :=
    wf_local Σ Γ -> Σ ;;; Γ |- t : (tSort u).

  Let Pprod Γ t na A B :=
    wf_local Σ Γ -> Σ ;;; Γ |- t : tProd na A B.

  Let Pind Γ ind t u args :=
    wf_local Σ Γ -> Σ ;;; Γ |- t : mkApps (tInd ind u) args.

  Let Pcheck Γ t T :=
    wf_local Σ Γ -> isType Σ Γ T -> Σ ;;; Γ |- t : T.

  Let PΓ Γ :=
    wf_local Σ Γ.

  (** Preliminary lemmata to go from a bidirectional judgement to the corresponding undirected one *)

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

  Lemma ctx_inst_impl Γ (wfΓ : wf_local Σ Γ) (Δ : context) (wfΔ : wf_local_rel Σ Γ (List.rev Δ)) : 
    forall args, PCUICTyping.ctx_inst (fun _ => Pcheck) Σ Γ args Δ -> ctx_inst Σ Γ args Δ.
  Proof.
    revert wfΔ.
    induction Δ using ctx_length_ind.
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
      1: by rewrite subst_telescope_length ; reflexivity.
      rewrite -(rev_involutive Γ0) -subst_context_telescope.
      cbn in wfΔ.
      apply wf_local_rel_app_inv in wfΔ as [].
      apply wf_local_local_rel.
      eapply substitution_wf_local ; eauto.
      1: repeat constructor.
      1: rewrite subst_empty ; eauto.
      apply wf_local_app.
      1: constructor ; eauto.
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
      1: by rewrite subst_telescope_length ; reflexivity.
      rewrite -(rev_involutive Γ0) -subst_context_telescope.
      rewrite <- app_nil_r.
      eapply wf_local_rel_subst1.
      cbn in wfΔ |- *.
      eassumption.
  Qed.
    
  (** The big theorem, proven by mutual induction using the custom induction principle *)
  Theorem bidirectional_to_pcuic : env_prop_bd Σ Pcheck Pinfer Psort Pprod Pind PΓ.
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

      assert (cparams : ctx_inst Σ Γ (pparams p) (List.rev (subst_instance (puinst p) (ind_params mdecl)))).
      { apply ctx_inst_impl ; auto.
        rewrite rev_involutive.
        apply wf_rel_weak ; auto.
        
        apply (wf_local_subst_instance_decl _ _ (inductive_mind ci) (InductiveDecl mdecl)) ; eauto.
        - by destruct isdecl.
        - eapply wf_local_app_inv.
          eapply on_minductive_wf_params_indices ; eauto.
      }

      assert (ctx_inst Σ Γ (pparams p ++ skipn (ci_npar ci) args)
              (List.rev (subst_instance (puinst p) (ind_params mdecl,,, ind_indices idecl)))).
      {
        rewrite -H.
        eapply ctx_inst_app_weak ; eauto.
        1: eapply validity ; auto.
        rewrite H.
        assumption.
      }
      
      assert (isType Σ Γ (mkApps (tInd ci (puinst p)) (pparams p ++ skipn (ci_npar ci) args))) as [].
      {
        eexists.
        eapply type_mkApps_arity.
        1: econstructor ; eauto.
        erewrite PCUICDeclarationTyping.ind_arity_eq.
        2: by eapply PCUICInductives.oib ; eauto.
        rewrite !subst_instance_it_mkProd_or_LetIn -it_mkProd_or_LetIn_app -subst_instance_app - (app_nil_r (pparams p ++ skipn (ci_npar ci) args)).
        eapply arity_spine_it_mkProd_or_LetIn ; auto.
        - unshelve apply ctx_inst_spine_subst ; auto.
          apply PCUICWeakening.weaken_wf_local ; auto.
          eapply on_minductive_wf_params_indices_inst ; eauto.
        - cbn.
          constructor.
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

  Qed.

End BDToPCUICTyping.

(** The user-facing theorems, directly following from the previous one *)

Theorem infering_typing `{checker_flags} (Σ : global_env_ext) Γ t T (wfΣ : wf Σ) :
  wf_local Σ Γ -> Σ ;;; Γ |- t ▹ T -> Σ ;;; Γ |- t : T.
Proof.
  intros.
  apply bidirectional_to_pcuic.
  all: assumption.
Qed.

Theorem checking_typing `{checker_flags} (Σ : global_env_ext) Γ t T (wfΣ : wf Σ) :
  wf_local Σ Γ -> isType Σ Γ T -> Σ ;;; Γ |- t ◃ T -> Σ ;;; Γ |- t : T.
Proof.
  intros wfΓ HT Ht. revert wfΓ HT.
  apply bidirectional_to_pcuic.
  all: assumption.
Qed.

Theorem infering_sort_typing `{checker_flags} (Σ : global_env_ext) Γ t u (wfΣ : wf Σ) :
  wf_local Σ Γ -> Σ ;;; Γ |- t ▹□ u -> Σ ;;; Γ |- t : tSort u.
Proof.
  intros wfΓ Ht. revert Ht wfΓ.
  apply bidirectional_to_pcuic.
  assumption.
Qed.

Theorem infering_prod_typing `{checker_flags} (Σ : global_env_ext) Γ t na A B (wfΣ : wf Σ) :
  wf_local Σ Γ -> Σ ;;; Γ |- t ▹Π (na,A,B) -> Σ ;;; Γ |- t : tProd na A B.
Proof.
  intros wfΓ Ht. revert Ht wfΓ.
  apply bidirectional_to_pcuic.
  assumption.
Qed.

Theorem infering_ind_typing `{checker_flags} (Σ : global_env_ext) Γ t ind u args (wfΣ : wf Σ) :
wf_local Σ Γ -> Σ ;;; Γ |- t ▹{ind} (u,args) -> Σ ;;; Γ |- t : mkApps (tInd ind u) args.
Proof.
  intros wfΓ Ht. revert Ht wfΓ.
  apply bidirectional_to_pcuic.
  assumption.
Qed.

Theorem wf_local_bd_typing `{checker_flags} (Σ : global_env_ext) Γ (wfΣ : wf Σ) :
  wf_local_bd Σ Γ -> wf_local Σ Γ.
Proof.
  apply bidirectional_to_pcuic.
  assumption.
Qed.