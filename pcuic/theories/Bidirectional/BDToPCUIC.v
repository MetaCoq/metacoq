From Coq Require Import Bool List Arith Lia.
From MetaCoq.Template Require Import config utils monad_utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICLiftSubst PCUICTyping PCUICInversion PCUICInductives PCUICInductiveInversion PCUICEquality PCUICUnivSubst PCUICClosed PCUICSubstitution PCUICValidity PCUICCumulativity PCUICInductives PCUICWfUniverses PCUICContexts PCUICSpine PCUICSR PCUICWellScopedCumulativity PCUICConversion PCUICOnFreeVars PCUICWeakeningTyp PCUICUnivSubstitutionTyp PCUICClosedTyp PCUICUnivSubstitutionConv.
From MetaCoq.PCUIC Require Import BDTyping.

Require Import ssreflect ssrbool.
From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.

(** Various generic lemmas missing from the MetaCoq library *)

Lemma All2i_prod (A B : Type) (P Q : nat -> A -> B -> Type) (n : nat) (l : list A) (l' : list B) :
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
    + apply infer_typing_sort_impl with id X0; intros Hs.
      apply weaken_ctx ; eauto.
    + apply weaken_ctx ; auto.
  - intros wfl. inversion_clear wfl.
    constructor.
    + apply IHΓ'. assumption.
    + apply infer_typing_sort_impl with id X0; intros Hs.
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

  (** The predicates we wish to prove, note the extra well-formedness hypothesis on the context
  and type whenever they are inputs to the algorithm *)

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

  Let PΓ_rel Γ Γ' :=
    wf_local Σ Γ -> wf_local_rel Σ Γ Γ'.

  (** Preliminary lemmas to go from a bidirectional judgement to the corresponding undirected one *)

  Lemma bd_wf_local Γ (all: wf_local_bd Σ Γ) :
    All_local_env_over_sorting checking infering_sort
      (fun Σ Γ _ t T _ => Pcheck Γ t T)
      (fun Σ Γ _ t s _ => Psort Γ t s)
      Σ Γ all ->
    wf_local Σ Γ.
  Proof using Type.
    intros allo ; induction allo.
    all: constructor.
    1,3: assumption.
    all: do 2 red.
    3: apply Hc; auto.
    all: apply infer_sort_impl with id tu; now intros Ht.
  Qed.

  Lemma bd_wf_local_rel Γ (wfΓ : wf_local Σ Γ) Γ' (all: wf_local_bd_rel Σ Γ Γ') :
    All_local_env_over_sorting
      (fun Σ Δ => checking Σ (Γ,,,Δ))
      (fun Σ Δ => infering_sort Σ (Γ,,,Δ))
      (fun Σ Δ _ t T _ => Pcheck (Γ,,,Δ) t T)
      (fun Σ Δ _ t s _ => Psort (Γ,,,Δ) t s)
      Σ Γ' all ->
    wf_local_rel Σ Γ Γ'.
  Proof using Type.
    intros allo ; induction allo.
    all: constructor.
    1,3: assumption.
    all: red.
    3: apply Hc; [by apply wf_local_app|].
    all: apply infer_sort_impl with id tu; intros Ht.
    all: now apply Hs, wf_local_app.
  Qed.

  Lemma ctx_inst_impl Γ (wfΓ : wf_local Σ Γ) (Δ : context) (wfΔ : wf_local_rel Σ Γ (List.rev Δ)) :
    forall args, PCUICTyping.ctx_inst (fun _ => Pcheck) Σ Γ args Δ -> ctx_inst Σ Γ args Δ.
  Proof using wfΣ.
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
  Theorem bidirectional_to_pcuic : env_prop_bd Σ Pcheck Pinfer Psort Pprod Pind PΓ PΓ_rel.
  Proof using wfΣ.
    apply bidir_ind_env.

    - intros. eapply bd_wf_local. eassumption.

    - intros. intro. eapply bd_wf_local_rel ; eassumption.

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
        eexists. eauto.

      + apply X4.
        constructor ; auto.
        * eexists. eauto.
        * apply X2 ; auto. eexists. eauto.

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

      assert (cparams : ctx_inst Σ Γ (pparams p) (List.rev (ind_params mdecl)@[puinst p])).
      { apply ctx_inst_impl ; auto.
        rewrite rev_involutive.
        apply wf_rel_weak ; auto.
        move: (H) => [? ?].
        eapply wf_local_subst_instance_decl ; eauto.
        eapply wf_local_app_inv.
        now eapply on_minductive_wf_params_indices.
      }

      assert (cum : Σ;;; Γ ⊢ mkApps (tInd ci u) args ≤
        mkApps (tInd ci (puinst p)) (pparams p ++ skipn (ci_npar ci) args)).
      {
        eapply ws_cumul_pb_mkApps_eq.
        1-3: fvs.
        - now constructor.
        - eapply type_is_open_term in X0 ; eauto.
          move: X0.
          rewrite on_free_vars_mkApps -{-3}(firstn_skipn (ci_npar ci) args)
          forallb_app /= => /andP [? ?].
          apply All2_app ; tea.
          + assert (forallb (is_open_term Γ) p.(pparams)).
            {
              eapply All_forallb'.
              1: now eapply ctx_inst_closed.
              intros.
              by rewrite -is_open_term_closed.
            }
            solve_all.
            eapply into_ws_cumul_pb ; tea.
            fvs.
          + now apply ws_cumul_pb_terms_refl ; fvs.
      }

      assert (ctx_inst Σ Γ (pparams p ++ skipn (ci_npar ci) args)
        (List.rev (subst_instance (puinst p) (ind_params mdecl,,, ind_indices idecl)))).
      {
        rewrite -H0.
        eapply ctx_inst_app_weak ; eauto.
        1: eapply validity ; auto.
        now rewrite H0.
      }

      assert (isType Σ Γ (mkApps (tInd ci (puinst p))
        (pparams p ++ skipn (ci_npar ci) args))) as [? tyapp].
      {
        eexists.
        eapply type_mkApps_arity.
        1: econstructor ; eauto.
        erewrite PCUICGlobalMaps.ind_arity_eq.
        2: by eapply PCUICInductives.oib ; eauto.
        rewrite !subst_instance_it_mkProd_or_LetIn -it_mkProd_or_LetIn_app -subst_instance_app - (app_nil_r (pparams p ++ skipn (ci_npar ci) args)).
        eapply arity_spine_it_mkProd_or_LetIn ; auto.
        - unshelve apply ctx_inst_spine_subst ; auto.
          apply weaken_wf_local ; auto.
          eapply on_minductive_wf_params_indices_inst ; eauto.
        - cbn.
          constructor.
      }

      assert (wf_local Σ (Γ,,,case_predicate_context ci mdecl idecl p)).
      {
        eapply wf_case_predicate_context ; tea.
        eexists ; tea.
      }

      econstructor ; eauto.
      2-3: split ; eauto.
      1: now eapply type_Cumul ; eauto ; apply cumulAlgo_cumulSpec in cum.

      eapply All2i_impl.
      1:{ apply All2i_prod ; [eassumption|idtac].
          eapply wf_case_branches_types' ; eauto.
          econstructor.
          eauto.
      }
      intros * ((?&?&?&?&Hbody)&[]).
      split ; tea.
      intros brctxty.
      fold predctx in brctxty.
      fold ptm in brctxty.
      repeat split ; auto.
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

    - red; intros.
      now econstructor.

    - red ; intros.
      now eapply type_reduction.

    - red ; intros.
      now eapply type_reduction.

    - red ; intros.
      now eapply type_reduction.

    - red ; intros.
      destruct X3.
      econstructor ; eauto.
      eapply (cumulAlgo_cumulSpec _ (pb := Cumul)), into_ws_cumul_pb ; tea.
      + fvs.
      + now eapply type_is_open_term.
      + now eapply subject_is_open_term.
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

Theorem infering_sort_isType `{checker_flags} (Σ : global_env_ext) Γ t u (wfΣ : wf Σ) :
  wf_local Σ Γ -> Σ ;;; Γ |- t ▹□ u -> isType Σ Γ t.
Proof.
  intros wfΓ Ht.
  exists u.
  now apply infering_sort_typing.
Qed.

Theorem einfering_sort_isType `{checker_flags} (Σ : global_env_ext) Γ t (wfΣ : wf Σ) :
  wf_local Σ Γ -> (∑ u, Σ ;;; Γ |- t ▹□ u) -> isType Σ Γ t.
Proof.
  intros wfΓ [u Ht].
  now eapply infering_sort_isType.
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

Theorem wf_local_bd_rel_typing `{checker_flags} (Σ : global_env_ext) Γ Γ' (wfΣ : wf Σ) :
  wf_local Σ Γ -> wf_local_bd_rel Σ Γ Γ' -> wf_local_rel Σ Γ Γ'.
Proof.
  intros.
  now apply bidirectional_to_pcuic.
Qed.

Theorem ctx_inst_bd_typing `{checker_flags} (Σ : global_env_ext) Γ l Δ (wfΣ : wf Σ) :
  wf_local Σ (Γ,,,Δ) ->
  PCUICTyping.ctx_inst checking Σ Γ l (List.rev Δ) ->
  PCUICTyping.ctx_inst typing Σ Γ l (List.rev Δ).
Proof.
  intros wfΓ inl.
  rewrite -(List.rev_involutive Δ) in wfΓ.
  remember (List.rev Δ) as Δ'.
  clear HeqΔ'.
  induction inl in wfΓ |- *.
  - constructor.
  - assert (Σ ;;; Γ |- i : t).
    {
      rewrite /= app_context_assoc in wfΓ.
      eapply wf_local_app_inv in wfΓ as [wfΓ _].
      inversion wfΓ ; subst.
      now apply checking_typing.
    }
    constructor ; tea.
    eapply IHinl.
    rewrite /= app_context_assoc in wfΓ.
    rewrite -subst_context_rev_subst_telescope.
    eapply substitution_wf_local ; tea.
    constructor.
    1: constructor.
    now rewrite subst_empty.
  - constructor.
    eapply IHinl.
    rewrite /= app_context_assoc in wfΓ.
    rewrite -subst_context_rev_subst_telescope.
    eapply substitution_wf_local ; tea.
    rewrite -{1}(subst_empty 0 b).
    constructor.
    1: constructor.
    rewrite !subst_empty.
    eapply wf_local_app_inv in wfΓ as [wfΓ _].
    now inversion wfΓ ; subst.
Qed.
