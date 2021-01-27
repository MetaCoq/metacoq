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

  Let PΓ Γ :=
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
    apply validity_term in X0.
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
    + eapply type_Cumul ; eauto.
      admit. (*the convertible inductive type is well-formed*)

    + remember (ind_ctors idecl) as ctors.
      eapply All2i_impl.
      1: eassumption.
      intros.
      cbn in X11.
      fold brctxty in X11.
      destruct X11 as (?&?&?&?&?&?&Hbody&?&Htype).

      assert (Σ ;;; Γ ,,, brctxty.1 |- brctxty.2 : tSort ps).
      { apply Htype.
        1: auto.
        eexists.
        constructor.
        1: auto.
        eapply isType_Sort_inv ; auto.
        apply validity_term in X5 ; eauto.
      }
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