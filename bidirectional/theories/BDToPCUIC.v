From Coq Require Import Bool List Arith Lia.
From MetaCoq.Template Require Import config utils monad_utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICTyping PCUICInversion PCUICInductiveInversion.
From MetaCoq.PCUIC Require Import PCUICWeakening PCUICClosed PCUICSubstitution PCUICPrincipality PCUICValidity PCUICCumulativity PCUICInductives PCUICWfUniverses PCUICSR PCUICWeakeningEnv PCUICContexts.
From MetaCoq.Bidirectional Require Import BDEnvironmentTyping BDTyping.

Require Import ssreflect.
From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.

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

  Let PΓ Γ (wfΓ : wf_local_bd Σ Γ) :=
    wf_local Σ Γ.

  Lemma wf_arities_context' :
    forall (mdecl : mutual_inductive_body),
      All (fun idecl => on_type (lift_typing typing) Σ [] (ind_type idecl)) (ind_bodies mdecl) ->
      wf_local Σ (arities_context (ind_bodies mdecl)).
  Proof.
    intros mdecl Hdecl.
    unfold arities_context.
    revert Hdecl.
    induction (ind_bodies mdecl) using rev_ind. 1: constructor.
    intros Ha.
    rewrite rev_map_app.
    simpl.    
    apply All_app in Ha as [Hl Hx].
    inv Hx. clear X0.
    destruct X as [s Hs].
    specialize (IHl Hl).
    econstructor; eauto.
    fold (arities_context l) in *.
    unshelve epose proof (weakening Σ [] (arities_context l) _ _ wfΣ _ Hs).
    1: now rewrite app_context_nil_l.
    simpl in X.
    simpl.
    eapply (env_prop_typing _ _ typecheck_closed) in Hs; eauto.
    rewrite -> andb_and in Hs. destruct Hs as [Hs Ht].
    simpl in Hs. apply (lift_closed #|arities_context l|) in Hs.
    rewrite -> Hs, app_context_nil_l in X. simpl. exists s.
    apply X.
  Qed.

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

(* Lemma bd_wf : Forall_decls_sorting Pcheck Psort Σ -> PT.wf Σ.
Proof.
  intros wfΣ. induction wfΣ.
  all: constructor.
  - assumption.
  - assumption.
  - constructor ; intuition.
  - destruct d as [[? [] ?]|].
    + inversion o0 as [[u Hty] Hb].
      apply Hb.
      1: constructor.
      exists u.
      simpl.
      eapply Hty.
      constructor.
    + inversion o0. eexists.
      eauto.
    + destruct o0.
      have wf_arities : PT.wf_local (Σ,udecl) (arities_context (ind_bodies m)).
      { apply wf_arities_context'.
        1: assumption.
        induction onInductives.
        all: constructor ; auto.
        destruct p.
        destruct onArity as [? onArity].
        eexists.
        eapply onArity.
        constructor. }
      have wf_params : PT.wf_local (Σ,udecl) (ind_params m).
      { clear - onParams.
        induction onParams.
        all: constructor.
        all: auto.
        1: by destruct t0 ; eexists ; eauto.
        1: by destruct t0 as ((? & ?) & ?) ; eexists ; eauto.
        destruct t0 as ((? & ?)&c).
        apply c.
        1: auto.
        eexists. red. eauto. }
      constructor ; auto.
      
      remember (ind_bodies m) as l in onInductives |- *.
      clear - IHwfΣ onInductives wf_arities wf_params.
      induction onInductives.
      all: constructor ; auto.
      destruct p.
      unshelve econstructor.
      * exact ind_indices.
      * exact ind_sort.
      * eapply map.
        2: exact ind_cshapes.
        intros [].
        constructor ; auto.
      * assumption.
      * destruct onArity as [? onArity].
        eexists.
        eapply onArity.
        constructor.
      * apply All2_map_right.
        eapply All2_impl.
        1: exact onConstructors.
        intros [[] ?] [] [] ; simpl in *.
        have wf_args : PT.wf_local (Σ,udecl) (arities_context (ind_bodies m),,,(ind_params m),,, cshape_args).
        { eapply PCUICContexts.type_local_ctx_wf_local.
          1: by apply weaken_wf_local.
          eapply type_local_ctx_impl ; eauto.
          by apply weaken_wf_local. }
        constructor ; auto ; simpl in *.
        --destruct on_ctype as [? on_ctype].
          eexists.
          apply on_ctype.
          1: eassumption.
        --apply type_local_ctx_impl ; eauto.
          apply weaken_wf_local.
          all: auto.
        --match goal with |- PT.ctx_inst _ _ ?ctx _ _ => remember ctx as Γ' end.
          clear -on_cindices wf_args.
          induction on_cindices.
          all: constructor.
          2-3: assumption.
          apply l0 ; auto.
          destruct l.
          eexists. red. eauto.
        --clear - on_ctype_positive.
          cbn in on_ctype_positive |- *.
          induction on_ctype_positive.
          all: constructor ; auto.
          clear - p. induction p.
          ++constructor ; assumption.
          ++econstructor 2 ; eauto.
          ++constructor 3 ; auto.
          ++constructor 4 ; auto.
        --clear - on_ctype_variance.
          intros v e.
          specialize (on_ctype_variance v e).
          unfold cstr_respects_variance in on_ctype_variance.
          unfold PT.cstr_respects_variance.
          destruct (variance_universes (PCUICEnvironment.ind_universes m)) ; simpl in * ; auto.
          destruct p as [[]]. intuition.
          induction a.
          all: constructor ; auto.
        
      * intros projs ; specialize (onProjections projs).
        clear - onProjections.
        induction ind_cshapes.
        1: auto.
        simpl in *.
        destruct ind_cshapes.
        { destruct a. simpl in *.
          destruct onProjections. constructor ; intuition. }
        assumption.
      * clear -ind_sorts wf_params.
        cbn in *.
        red in ind_sorts |- *.
        destruct (universe_family ind_sort).
        --induction ind_cshapes ; auto.
        --induction ind_cshapes ; auto.
          simpl in *.
          destruct ind_cshapes ; auto.
          simpl in *.
          destruct a ; auto.
        --destruct ind_sorts. split.
          { apply Forall_map.
            eapply Forall_impl. 1: eassumption.
            intros [] ? ; assumption. }
          destruct indices_matter ; auto.
          apply type_local_ctx_impl.
          all: auto.
        --destruct ind_sorts. split.
          { apply Forall_map.
            eapply Forall_impl. 1: eassumption.
            intros [] ? ; assumption. }
          destruct indices_matter ; auto.
          apply type_local_ctx_impl.
          all: auto.
      *  clear -onIndices.
        intros v e. specialize (onIndices v e).
        unfold ind_respects_variance in onIndices.
        unfold PT.ind_respects_variance.
        destruct (PCUICEnvironment.ind_universes m) ; simpl in * ; auto.
        destruct cst.
        replace (PT.level_var_instance 0 l) with (level_var_instance 0 l).
        2:{ by induction l ; auto. }
        match goal with |- context [PT.lift_instance ?len ?list] =>
        replace (PT.lift_instance len list) with (lift_instance len list) end.
        2:{ apply map_ext. intros []. all: reflexivity. }
        induction onIndices.
        all: constructor ; auto.
Qed. *)
  
Theorem bidirectional_to_PCUIC : env_prop_bd Σ Pcheck Pinfer Psort Pprod Pind (@PΓ).
Proof.
  apply bidir_ind_env.

  { intros. eapply bd_wf_local. eassumption. }

(*   1-14: intros ; red ; econstructor ; eauto. *)

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
    apply validity in X0.
    2: done.
    destruct X0 as [? X0].
    apply inversion_Prod in X0.
    2: done.
    destruct X0 as (? & ? & ? & _).
    eexists. eassumption.

  - red ; intros ; econstructor ; eauto.

  - red ; intros ; econstructor ; eauto.

  - red ; intros ; econstructor ; eauto.

  - red ; intros ; econstructor ; eauto.
    + apply X2 ; auto.
      suff [] : @isWfArity cf Σ Γ pty by done.
      eapply WfArity_build_case_predicate_type ; eauto.
      * eapply validity.
        all: by auto. 
      * subst npar. assumption.
    + subst npar.
      
      assert (isType Σ Γ pty).
      { eapply WfArity_build_case_predicate_type; eauto.
        by eapply validity_term ; auto.
      }

      assert (∑ pctx, destArity [] pty =  Some (pctx, ps)) as [].
      { unshelve eapply (build_case_predicate_type_spec (Σ.1, ind_universes mdecl)) in H2 as [parsubst [_ ->]].
        1: eapply (on_declared_inductive) in isdecl as [? ?] ; eauto.
        eexists. rewrite !destArity_it_mkProd_or_LetIn; simpl. reflexivity. }

      assert (All (fun bty => isType Σ Γ bty.2) btys).
      { by eapply build_branches_type_wt ; eauto. }

      clear H4. 
      induction X3.
      all: constructor ; auto.
      all: inversion_clear X6.
      2: auto.
      destruct r as (? & ? & ?).
      repeat split ; auto.

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
    eapply validity_term.
    all: auto.
  
  - red ; intros.
    have [] : (isType Σ Γ (tProd na A B)).
    { eapply isType_red.
      2: eassumption.
      eapply validity_term.
      all: auto.
    }
    econstructor.
    + by auto.
    + by eassumption.
    + by apply red_cumul. 
  
  - red ; intros.
    have [] : (isType Σ Γ (mkApps (tInd ind ui) args)).
    { eapply isType_red.
      2: eassumption.
      eapply validity_term.
      all: auto.
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
  wf_local Σ Γ -> Σ ;;; Γ |- t ▸□ u -> Σ ;;; Γ |- t : tSort u.
Proof.
  intros wfΓ Ht. revert Ht wfΓ.
  apply bidirectional_to_PCUIC.
  assumption.
Qed.

Theorem infering_prod_typing `{checker_flags} (Σ : global_env_ext) Γ t na A B (wfΣ : wf Σ) :
  wf_local Σ Γ -> Σ ;;; Γ |- t ▸Π (na,A,B) -> Σ ;;; Γ |- t : tProd na A B.
Proof.
  intros wfΓ Ht. revert Ht wfΓ.
  apply bidirectional_to_PCUIC.
  assumption.
Qed.

Theorem infering_ind_typing `{checker_flags} (Σ : global_env_ext) Γ t ind u args (wfΣ : wf Σ) :
wf_local Σ Γ -> Σ ;;; Γ |- t ▸{ind} (u,args) -> Σ ;;; Γ |- t : mkApps (tInd ind u) args.
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