(* Distributed under the terms of the MIT license. *)
From Coq Require Import Morphisms.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICInduction
  PCUICLiftSubst PCUICUnivSubst PCUICContextRelation
  PCUICTyping PCUICReduction PCUICCumulativity 
  PCUICEquality PCUICGlobalEnv PCUICClosed PCUICClosedConv PCUICClosedTyp PCUICEquality PCUICWeakeningEnvConv PCUICWeakeningEnvTyp
  PCUICSigmaCalculus PCUICRenameDef PCUICRenameConv PCUICWeakeningConv PCUICWeakeningTyp PCUICInstDef PCUICInstConv
  PCUICGuardCondition PCUICUnivSubstitutionConv PCUICOnFreeVars.

Require Import ssreflect ssrbool.
From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.
Set Equations With UIP.
Set Keyed Unification.
Set Default Goal Selector "!".
Implicit Types cf : checker_flags.

(** * Type preservation for σ-calculus instantiation *)

Open Scope sigma_scope.

Lemma inst_cumulSpec {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {P Γ Δ σ A B} :
  usubst Γ σ Δ ->
  on_free_vars P A ->
  on_free_vars P B ->
  on_ctx_free_vars P Γ ->
  Σ ;;; Γ |- A <=s B ->
  Σ ;;; Δ |- A.[σ] <=s B.[σ].
Admitted. 

Lemma type_inst {cf : checker_flags} : env_prop
  (fun Σ Γ t A =>
    forall Δ σ,
    wf_local Σ Δ ->
    Σ ;;; Δ ⊢ σ : Γ ->
    Σ ;;; Δ |- t.[σ] : A.[σ])
  (fun Σ Γ =>
    All_local_env
    (lift_typing (fun (Σ : global_env_ext) (Γ : context) (t T : term)
    =>
    forall Δ σ,
    wf_local Σ Δ ->
    Σ ;;; Δ ⊢ σ : Γ ->
    Σ ;;; Δ |- t.[σ] : T.[σ]) Σ) Γ).
Proof.
  apply typing_ind_env.

  - intros Σ wfΣ Γ wfΓ. auto.
    induction 1; constructor; firstorder auto.
  - intros Σ wfΣ Γ wfΓ n decl e X Δ σ hΔ hσ. simpl.
    eapply hσ. assumption.
  - intros Σ wfΣ Γ wfΓ l X H0 Δ σ hΔ hσ. simpl.
    econstructor. all: assumption.
  - intros Σ wfΣ Γ wfΓ na A B s1 s2 X hA ihA hB ihB Δ σ hΔ hσ.
    autorewrite with sigma. simpl.
    econstructor.
    + eapply ihA ; auto.
    + eapply ihB.
      * econstructor ; auto.
        eexists. eapply ihA ; auto.
      * eapply well_subst_Up. 2: assumption.
        econstructor ; auto.
        eexists. eapply ihA. all: auto.
  - intros Σ wfΣ Γ wfΓ na A t s1 bty X hA ihA ht iht Δ σ hΔ hσ.
    autorewrite with sigma.
    econstructor.
    + eapply ihA ; auto.
    + eapply iht.
      * econstructor ; auto.
        eexists. eapply ihA ; auto.
      * eapply well_subst_Up. 2: assumption.
        constructor. 1: assumption.
        eexists. eapply ihA. all: auto.
  - intros Σ wfΣ Γ wfΓ na b B t s1 A X hB ihB hb ihb ht iht Δ σ hΔ hσ.
    autorewrite with sigma.
    econstructor.
    + eapply ihB. all: auto.
    + eapply ihb. all: auto.
    + eapply iht.
      * econstructor. all: auto.
        -- eexists. eapply ihB. all: auto.
        -- simpl. eapply ihb. all: auto.
      * eapply well_subst_Up'; try assumption.
        constructor; auto.
        ** exists s1. apply ihB; auto.
        ** apply ihb; auto.
  - intros Σ wfΣ Γ wfΓ t na A B s u X hty ihty ht iht hu ihu Δ σ hΔ hσ.
    autorewrite with sigma.
    econstructor.
    * specialize (ihty _ _ hΔ hσ).
      simpl in ihty. eapply meta_conv_term; [eapply ihty|].
      now rewrite up_Up.
    * specialize (iht _ _ hΔ hσ).
      simpl in iht. eapply meta_conv; [eapply iht|].
      now rewrite up_Up.
    * eapply ihu; auto.
  - intros Σ wfΣ Γ wfΓ cst u decl X X0 isdecl hconst Δ σ hΔ hσ.
    autorewrite with sigma. simpl.
    eapply meta_conv; [econstructor; eauto|].
    eapply declared_constant_closed_type in isdecl; eauto.
    rewrite inst_closed0; auto.
    now rewrite closedn_subst_instance.
  - intros Σ wfΣ Γ wfΓ ind u mdecl idecl isdecl X X0 hconst Δ σ hΔ hσ.
    eapply meta_conv; [econstructor; eauto|].
    eapply declared_inductive_closed_type in isdecl; eauto.
    rewrite inst_closed0; auto.
    now rewrite closedn_subst_instance.
  - intros Σ wfΣ Γ wfΓ ind i u mdecl idecl cdecl isdecl X X0 hconst Δ σ hΔ hσ.
    eapply meta_conv; [econstructor; eauto|].
    eapply declared_constructor_closed_type in isdecl; eauto.
    rewrite inst_closed0; eauto.
  - intros Σ wfΣ Γ wfΓ ci p c brs indices ps mdecl idecl isdecl HΣ.
    intros IHΔ ci_npar eqpctx predctx wfp cup Hpctx Hpret
      IHpret IHpredctx isallowed.
    intros Hctxi IHctxi Hc IHc iscof ptm wfbrs Hbrs Δ f HΔ Hf.
    autorewrite with sigma. simpl.
    rewrite map_app. simpl.
    rewrite /ptm. rewrite inst_it_mkLambda_or_LetIn.
    relativize #|predctx|.
    * erewrite inst_predicate_preturn.
      rewrite /predctx.
      rewrite inst_case_predicate_context //.
      eapply type_Case; eauto;
       rewrite - ?inst_case_predicate_context //.
      + now eapply inst_wf_predicate.
      + simpl.
        apply All_local_env_app_inv in Hpctx as [].
        eapply wf_local_app_inst; eauto.
        apply All_local_env_app_inv in IHpredctx as [].
        apply a2.
      + apply All_local_env_app_inv in Hpctx as [].
        apply All_local_env_app_inv in IHpredctx as [].
        eapply IHpret.
        ++ eapply wf_local_app_inst; eauto.
           apply a2.
        ++ relativize #|pcontext p|; [eapply well_subst_app_up|] => //; rewrite /predctx; len.
           2:{ rewrite case_predicate_context_length //. }
           eapply wf_local_app_inst; eauto. apply a2.
      + revert IHctxi.
        rewrite /= /id -map_app.
        rewrite -{2}[subst_instance _ _](inst_closedn_ctx f 0).
        { pose proof (declared_inductive_closed_pars_indices isdecl).
          now rewrite closedn_subst_instance_context. }
        rewrite inst_context_telescope.
        rewrite inst_telescope_upn0.
        clear -Δ f HΔ Hf.
        induction 1.
        { constructor; auto. }
        { simpl. rewrite inst_telescope_cons.
          constructor; cbn; eauto.
          now rewrite inst_subst_telescope /= in IHIHctxi. }
        { simpl. rewrite inst_telescope_cons.
          constructor; cbn; eauto.
          now rewrite inst_subst_telescope /= in IHIHctxi. }
      + simpl. unfold id.
        specialize (IHc _ _ HΔ Hf).
        now rewrite inst_mkApps map_app in IHc.
      + now eapply inst_wf_branches.
      + eapply Forall2_All2 in wfbrs.
        eapply All2i_All2_mix_left in Hbrs; eauto.
        eapply All2i_nth_hyp in Hbrs.
        eapply All2i_map_right, (All2i_impl Hbrs) => i cdecl br.
        set (brctxty := case_branch_type _ _ _ _ _ _ _ _).
        move=> [Hnth [wfbr [Hconv [Hbrctx [Hbr [IHbr [Hbty IHbty]]]]]]].
        split => //.
        rewrite -(inst_closed_constructor_body mdecl cdecl f).
        { eapply (declared_constructor_closed (c:=(ci.(ci_ind),i))); eauto.
          split; eauto. }
        rewrite inst_case_predicate_context //.
        rewrite inst_case_branch_type //.
        rewrite -/brctxty. intros brctx'.
        assert (wf_local Σ (Δ,,, brctx'.1)).
        { rewrite /brctx'. cbn.
          apply All_local_env_app_inv in Hbrctx as [].
          eapply wf_local_app_inst; tea. apply a0. }
        split => //. split.
        ++ eapply IHbr => //.
          rewrite /brctx' /brctxty; cbn.
          relativize #|bcontext br|.
          { eapply well_subst_app_up => //. }
          rewrite /case_branch_type /=.
          rewrite case_branch_context_length //.
        ++ eapply IHbty=> //.
          rewrite /brctx'; cbn.
          relativize #|bcontext br|.
          { eapply well_subst_app_up => //. }
          rewrite /brctxty /= case_branch_context_length //.
    * rewrite /predctx case_predicate_context_length //.
  - intros Σ wfΣ Γ wfΓ p c u mdecl idecl cdecl pdecl isdecl args X X0 hc ihc e ty
           Δ σ hΔ hσ.
    simpl.
    eapply meta_conv; [econstructor|].
    * eauto.
    * specialize (ihc _ _ hΔ hσ).
      rewrite inst_mkApps in ihc. eapply ihc.
    * now rewrite map_length.
    * autorewrite with sigma.
      eapply declared_projection_closed in isdecl; auto.
      move: isdecl.
      rewrite -(closedn_subst_instance _ _ u).
      rewrite /ty.
      eapply inst_ext_closed.
      intros x Hx.
      rewrite subst_consn_lt /=; len; try lia.
      (rewrite Upn_comp; try now repeat len); [].
      rewrite subst_consn_lt /=; len; try lia.
      now rewrite map_rev.
  - intros Σ wfΣ Γ wfΓ mfix n decl types hguard hnth htypes hmfix ihmfix wffix Δ σ hΔ hσ.
    simpl. eapply meta_conv; [econstructor;eauto|].
    * now eapply fix_guard_inst.
    * now rewrite nth_error_map hnth.
    * solve_all.
      destruct a as [s [Hs IH]].
      exists s; eapply IH; eauto.
    * solve_all.
      len. rewrite /types in b0. len in b0.
      pose proof (inst_fix_context mfix σ).
      setoid_rewrite <-up_Upn at 1 in H. rewrite H.
      eapply All_local_env_app_inv in htypes as [].
      eapply meta_conv; [eapply b0; eauto|].
      + eapply wf_local_app_inst; eauto. eapply a2.
      + rewrite -(fix_context_length mfix).
        eapply well_subst_app_up => //.
        eapply wf_local_app_inst; eauto. apply a2.
      + rewrite lift0_inst. now sigma.
    * now apply inst_wf_fixpoint.
    * reflexivity.

  - intros Σ wfΣ Γ wfΓ mfix n decl types hguard hnth htypes hmfix ihmfix wffix Δ σ hΔ hσ.
    simpl. eapply meta_conv; [econstructor;eauto|].
    * now eapply cofix_guard_inst.
    * now rewrite nth_error_map hnth.
    * solve_all.
      destruct a as [s [Hs IH]].
      exists s; eapply IH; eauto.
    * solve_all.
      len. rewrite /types in b0. len in b0.
      pose proof (inst_fix_context mfix σ).
      setoid_rewrite <-up_Upn at 1 in H. rewrite H.
      eapply All_local_env_app_inv in htypes as [].
      eapply meta_conv; [eapply b0; eauto|].
      + eapply wf_local_app_inst; eauto. eapply a2.
      + rewrite -(fix_context_length mfix).
        eapply well_subst_app_up => //.
        eapply wf_local_app_inst; eauto. apply a2.
      + rewrite lift0_inst. now sigma.
    * now apply inst_wf_cofixpoint.
    * reflexivity.

  - intros Σ wfΣ Γ wfΓ t A B X hwf ht iht hB ihB hcum Δ σ hΔ hσ.
    eapply type_Cumul.
    + eapply iht. all: auto.
    + eapply ihB. all: auto.
    + eapply inst_cumulSpec => //.
      * exact hσ.
      * eapply type_closed in ht.
        now eapply closedn_on_free_vars.
      * eapply subject_closed in hB.
        now eapply closedn_on_free_vars.
      * eapply closed_wf_local in wfΓ; tea.
        rewrite closedn_ctx_on_free_vars in wfΓ.
        now rewrite -on_free_vars_ctx_on_ctx_free_vars in wfΓ.
      * apply hcum.
Qed.
