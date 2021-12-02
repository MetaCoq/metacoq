(* Distributed under the terms of the MIT license. *)
From Coq Require Import Morphisms.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICInduction
  PCUICLiftSubst PCUICUnivSubst PCUICContextRelation PCUICCumulativity
  PCUICTyping PCUICReduction PCUICGlobalEnv PCUICClosed PCUICEquality PCUICRenameDef 
  PCUICSigmaCalculus PCUICClosed PCUICOnFreeVars PCUICGuardCondition PCUICTyping
  PCUICWeakeningEnvConv PCUICWeakeningEnvTyp PCUICClosedConv PCUICClosedTyp PCUICRenameConv
  PCUICWellScopedCumulativity.

Require Import ssreflect ssrbool.
From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.
Set Equations With UIP.

(** * Type preservation for σ-calculus operations *)

Open Scope sigma_scope.
Set Keyed Unification.

Set Default Goal Selector "!".


Section Renaming.

Context `{cf : checker_flags}.

Lemma renaming_vass :
  forall P Σ Γ Δ na A f,
    wf_local Σ (Γ ,, vass na (rename f A)) ->
    renaming P Σ Γ Δ f ->
    renaming (shiftnP 1 P) Σ (Γ ,, vass na (rename f A)) (Δ ,, vass na A) (shiftn 1 f).
Proof.
  intros P Σ Γ Δ na A f hΓ [? h].
  split. 1: auto.
  eapply urenaming_vass; assumption.
Qed.

Lemma renaming_vdef :
  forall P Σ Γ Δ na b B f,
    wf_local Σ (Γ ,, vdef na (rename f b) (rename f B)) ->
    renaming P Σ Γ Δ f ->
    renaming (shiftnP 1 P) Σ (Γ ,, vdef na (rename f b) (rename f B)) (Δ ,, vdef na b B) (shiftn 1 f).
Proof.
  intros P Σ Γ Δ na b B f hΓ [? h].
  split. 1: auto.
  eapply urenaming_vdef; assumption.
Qed.

Lemma rename_ind_predicate_context {Σ : global_env_ext} {wfΣ : wf Σ} {f ind mdecl idecl} :
  declared_inductive Σ ind mdecl idecl ->
  rename_context (shiftn (context_assumptions (ind_params mdecl)) f) (ind_predicate_context ind mdecl idecl) =
  ind_predicate_context ind mdecl idecl.
Proof.
  intros isdecl.
  generalize (declared_inductive_closed_pars_indices isdecl).
  rewrite closedn_ctx_app => /andP [] clpars /= clinds.
  rewrite /ind_predicate_context.
  rewrite /expand_lets_ctx /expand_lets_k_ctx.
  rewrite !rename_context_snoc /= /map_decl /= /snoc. f_equal.
  - f_equal. len.
    rewrite rename_mkApps /=. f_equal.
    rewrite shiftn_add.
    relativize (#|_| + _).
    1:now erewrite -> rename_to_extended_list.
    now len.
  - rewrite rename_context_subst.
    rewrite rename_closed_extended_subst //. f_equal.
    rewrite shiftn_add Nat.add_comm. len.
    rewrite rename_context_lift. f_equal. 
    rewrite rename_closedn_ctx //.
Qed.

Lemma rename_case_predicate_context {Σ : global_env_ext} {wfΣ : wf Σ} {ind mdecl idecl f p} :
  declared_inductive Σ ind mdecl idecl ->
  wf_predicate mdecl idecl p ->
  rename_context f (case_predicate_context ind mdecl idecl p) =
  case_predicate_context ind mdecl idecl (rename_predicate f p).
Proof.
  intros decli wfp.
  unfold case_predicate_context. simpl.
  unfold id. unfold case_predicate_context_gen.
  rewrite rename_context_set_binder_name.
  - len.
    now rewrite -(wf_predicate_length_pcontext wfp).
  - f_equal. rewrite /pre_case_predicate_context_gen.
    rewrite rename_inst_case_context.
    rewrite (wf_predicate_length_pars wfp) (declared_minductive_ind_npars decli).
    now rewrite (rename_ind_predicate_context decli).
Qed.

Lemma rename_case_branch_type {Σ : global_env_ext} {wfΣ : wf Σ} f (ci : case_info) mdecl idecl p br i cdecl :
  declared_inductive Σ ci mdecl idecl ->
  wf_predicate mdecl idecl p ->
  wf_branch cdecl br ->
  let ptm := it_mkLambda_or_LetIn (case_predicate_context ci mdecl idecl p) (preturn p) in
  let p' := rename_predicate f p in
  let ptm' := it_mkLambda_or_LetIn (case_predicate_context ci mdecl idecl p') (preturn p') in
  case_branch_type ci mdecl idecl
     (rename_predicate f p)
     (map_branch_shift rename shiftn f br)
     ptm' i (rename_constructor_body mdecl f cdecl) =
  map_pair (rename_context f) (rename (shiftn #|bcontext br| f))
  (case_branch_type ci mdecl idecl p br ptm i cdecl).
Proof.
  intros decli wfp wfb ptm p' ptm'.
  rewrite /case_branch_type /case_branch_type_gen /map_pair /=.
  rewrite rename_case_branch_context_gen //.
  { eapply (declared_inductive_closed_params decli). }
  { len; now apply wf_branch_length. }
  { rewrite -(declared_minductive_ind_npars decli).
    apply (wf_predicate_length_pars wfp). }
  f_equal.
  rewrite rename_mkApps map_app map_map_compose.
  rewrite (wf_branch_length wfb).
  f_equal.
  * rewrite /ptm' /ptm !lift_it_mkLambda_or_LetIn !rename_it_mkLambda_or_LetIn.
    rewrite !lift_rename. f_equal.
    ++ rewrite /p'. len.
      epose proof (rename_context_lift f #|cstr_args cdecl| 0).
        rewrite Nat.add_0_r in H.
        rewrite H. len.
        rewrite shiftn0 //. f_equal.
        rewrite rename_case_predicate_context //.
    ++ rewrite /p'. rewrite Nat.add_0_r. simpl. len.
      rewrite map2_length //. 1:{ len. now rewrite (wf_predicate_length_pcontext wfp). }
      rewrite - !lift_rename; len. rewrite case_predicate_context_length // shiftn_add.
      now rewrite -rename_shiftnk Nat.add_comm.
  * rewrite /= rename_mkApps /=. f_equal.
    ++ rewrite !map_map_compose /id. apply map_ext => t.
      rewrite /expand_lets /expand_lets_k.
      rewrite -rename_subst_instance. len.
      rewrite -shiftn_add -shiftn_add.
      rewrite rename_subst map_rev. f_equal.
      rewrite List.rev_length rename_subst.
      rewrite (wf_predicate_length_pars wfp).
      rewrite (declared_minductive_ind_npars decli).
      rewrite -{2}(context_assumptions_subst_instance (puinst p) (ind_params mdecl)).
      rewrite rename_closed_extended_subst.
      { rewrite closedn_subst_instance_context.
        apply (declared_inductive_closed_params decli). }
      f_equal. len. rewrite !shiftn_add.
      rewrite (Nat.add_comm _ (context_assumptions _)) rename_shiftnk.
      f_equal. rewrite Nat.add_comm rename_subst.
      rewrite rename_inds. f_equal.
      rewrite shiftn_add. len. lia_f_equal.
    ++ unfold id. f_equal. f_equal.
       rewrite map_app map_map_compose.
       rewrite map_map_compose.
       setoid_rewrite rename_shiftn. len. f_equal.
       rewrite rename_to_extended_list.
       now rewrite /to_extended_list /to_extended_list_k reln_fold.
Qed.

Lemma shiftnP_S P n : shiftnP (S n) P =1 shiftnP 1 (shiftnP n P).
  Admitted.

Lemma on_free_vars_rename P f t :
  on_free_vars P (rename f t) = on_free_vars (P ∘ f) t.
Admitted. 

Lemma rename_on_free_vars n t f :
  on_free_vars (shiftnP n xpred0) t -> rename (shiftn n f) t = t.
Admitted.

Lemma urename_on_free_vars_shift P Γ Δ f u (Ξ:list context_decl) : 
   let sP := shiftnP #|Γ| P in
   urenaming sP Δ Γ f -> 
   is_closed_context Γ -> 
   is_closed_context Δ -> 
   on_free_vars (shiftnP #|Ξ| (shiftnP #|Γ| xpred0)) u -> 
   on_free_vars (shiftnP #|Ξ| (shiftnP #|Δ| xpred0)) 
                (rename (shiftn #|Ξ| f) u).
   intros sP hf HΓ HΔ Hu. rewrite on_free_vars_rename.
   eapply on_free_vars_impl. 2: tea. clear Hu. intros n Hn.
   apply urenaming_context with (Ξ:=Ξ) in hf. 
   unfold urenaming in hf. 
   specialize (hf n). destruct (nth_error (Γ,,, Ξ) n) eqn : Hnth.
   - specialize (hf c); cbn in hf. forward hf. 
     * unfold shiftnP in Hn. unfold sP , shiftnP.
       toProp. toProp Hn. destruct Hn.
       + intuition.
       + right. toProp. toProp H. destruct H; intuition.       
     * destruct (hf eq_refl) as [decl' [Hfn _]].
       clear hf Hn. unfold sP , shiftnP. rewrite orb_false_r. 
       assert (shiftn #|Ξ| f n < #|Δ,,, rename_context f Ξ|). 
       { eapply nth_error_Some'. exists decl'. eauto. }
       rewrite app_context_length in H.
       rewrite rename_context_length in H.
       toProp. clear -H.
       repeat rewrite PeanoNat.Nat.ltb_lt. lia. 
  - rewrite nth_error_None in Hnth. rewrite app_context_length in Hnth. unfold shiftnP in *. toProp Hn. toProp. unfold shiftn.
    clear -Hn Hnth. destruct Hn.
    * toProp H. intuition.
    * toProp H. destruct H; [toProp H |]; intuition.      
Defined.  

Lemma urename_is_open_term P Γ Δ f u : let sP := shiftnP #|Γ| P in
   urenaming sP Δ Γ f -> is_closed_context Γ -> is_closed_context Δ -> is_open_term Γ u -> is_open_term Δ (rename f u).
Proof.
  intros sP hf HΓ HΔ Hu.
  unfold is_open_term.
  rewrite <- (shiftnP0 (shiftnP #|Δ| xpred0)).
  rewrite <- (shiftn0 f).
  eapply urename_on_free_vars_shift with (Ξ:=[]); eauto.
  rewrite shiftnP0; eauto. 
Defined. 

Lemma on_free_vars_ctx_inst_case_context 
  P (Γ : list context_decl) (pars : list term)
  (puinst : Instance.t) (pctx : list context_decl) :
  forallb (on_free_vars (shiftnP #|Γ| P)) pars ->
  on_free_vars_ctx (closedP #|pars| xpredT) pctx ->
  on_free_vars_ctx P Γ ->
  on_free_vars_ctx P (Γ,,, inst_case_context pars puinst pctx).
Proof.
  intros. rewrite on_free_vars_ctx_app H1 /=.
  eapply on_free_vars_ctx_inst_case_context; trea; solve_all.
  rewrite test_context_k_closed_on_free_vars_ctx //.
Qed.


Lemma rename_context_on_free_vars f (p : predicate term) l  :
on_free_vars_ctx (closedP #|pparams p| xpredT) l ->  
rename_context (shiftn #|pparams p| f) l = l.
Proof.
  intro Hclosed. 
  unfold on_free_vars_ctx in Hclosed. 
  unfold rename_context, fold_context_k. 
  induction l; eauto.
  cbn in *. rewrite alli_app in Hclosed. toProp Hclosed.
  destruct Hclosed as [H Hclosed]. 
  rewrite mapi_rec_app. rewrite List.distr_rev.
  rewrite IHl; eauto.
  cbn in *. f_equal.
  toProp Hclosed. destruct Hclosed as [Hclosed _].
  destruct a; unfold map_decl; cbn.
  unfold on_free_vars_decl in Hclosed. 
  unfold test_decl in Hclosed.
  toProp Hclosed. cbn in Hclosed.
  destruct Hclosed as [Hbody Htype].
  f_equal.
  - destruct decl_body; eauto; cbn in *. 
    f_equal. rewrite closedP_shiftnP in Hbody.
    rewrite shiftnP_add in Hbody. rewrite shiftn_add.
    apply rename_on_free_vars; eauto.
  - rewrite closedP_shiftnP in Htype.
    rewrite shiftnP_add in Htype. rewrite shiftn_add.
    apply rename_on_free_vars; eauto.
Defined.

Lemma inst_case_predicate_context_rename f p :  
  on_free_vars_ctx (closedP #|pparams p| xpredT) (pcontext p) ->
  inst_case_predicate_context (rename_predicate f p) = rename_context f (inst_case_predicate_context p).
Proof. 
  intro Hclosed. unfold inst_case_predicate_context.
  unfold pparams at 1. cbn.
  replace (pcontext p) with 
  (rename_context (shiftn #|(pparams p)| f) (pcontext p)) at 1.
  - rewrite <- rename_inst_case_context. reflexivity.
  - apply rename_context_on_free_vars; eauto.
Defined.   

Lemma inst_case_branch_context_rename f p x :
on_free_vars_ctx (closedP #|pparams p| xpredT) (bcontext x) ->  
inst_case_branch_context (rename_predicate f p) 
     (rename_branch f x) =
     rename_context f (inst_case_branch_context p x).
Proof.
  intro Hclosed. unfold inst_case_branch_context. cbn. 
  replace (bcontext x) with 
  (rename_context (shiftn #|(pparams p)| f) (bcontext x)) at 1.
  - rewrite <- rename_inst_case_context. reflexivity.
  - apply rename_context_on_free_vars; eauto.
Defined.     

Lemma convSpec_renameP P Σ Γ Δ f A B : let sP := shiftnP #|Γ| P in
    wf Σ.1 ->
    urenaming sP Δ Γ f ->
    is_closed_context Γ ->
    is_open_term Γ A ->
    is_open_term Γ B ->
    is_closed_context Δ ->
    Σ ;;; Γ |- A =s B ->
    Σ ;;; Δ |- rename f A =s rename f B.
Proof. 
  intros sP wfΣ Hren HfreeA HfreeB HΓ HΔ e. 
  revert Γ A B e sP Δ f wfΣ Hren HfreeA HfreeB HΓ HΔ e. 
  eapply (convSpec0_ind_all Σ.1 (eq_universe (global_ext_constraints Σ)) 
  (fun Γ A B => forall Δ f, let sP := shiftnP #|Γ| P in
  wf Σ.1 ->
  urenaming sP Δ Γ f ->
  is_closed_context Γ ->
  is_open_term Γ A ->
  is_open_term Γ B ->
  is_closed_context Δ ->
  Σ ;;; Γ |- A =s B ->
  Σ ;;; Δ |- rename f A =s rename f B)); intros; cbn.
  - rewrite rename_subst10. solve [econstructor].
  - rewrite rename_subst10. solve [econstructor].
  - rename X0 into hf. unfold urenaming in hf.
    destruct (nth_error Γ i) eqn:hnth; noconf H.
    assert (hav : sP i = true).
    { clear -H1; unfold sP, shiftnP in *. cbn in *. rewrite orb_false_r in H1. intuition. }
    clear H1. 
    specialize hf with (1 := hav) (2 := hnth).
    destruct hf as [decl' [e' [? [hr hbo]]]].
    rewrite H /= in hbo.
    rewrite lift0_rename.
    destruct (decl_body decl') eqn:hdecl => //. noconf hbo.
    sigma in H1. sigma. rewrite H1.
    relativize (t.[_]).
    2:{ setoid_rewrite rshiftk_S. rewrite -rename_inst.
        now rewrite -(lift0_rename (S (f i)) _). }
     eapply cumul_rel. now rewrite e' /= hdecl.
   - rewrite rename_mkApps. simpl.
     rewrite rename_iota_red //.
    * change (bcontext br) with (bcontext (rename_branch f br)).
     move/and5P: H2 => [_ _ _ _ hbrs].
     eapply nth_error_forallb in hbrs; tea. simpl in hbrs.
     move/andP: hbrs => [] clbctx clbod.
     rewrite closedn_ctx_on_free_vars.
     now rewrite test_context_k_closed_on_free_vars_ctx in clbctx.
   * eapply cumul_iota.
     + rewrite nth_error_map H /= //.
     + simpl. now len.
   - rewrite 2!rename_mkApps. simpl.
     eapply cumul_fix.
     + eapply rename_unfold_fix. eassumption.
     + eapply is_constructor_rename. assumption.
   - rewrite 2!rename_mkApps. simpl.
     eapply cumul_cofix_case.
     eapply rename_unfold_cofix. eassumption.
   - rewrite 2!rename_mkApps. simpl.
     eapply cumul_cofix_proj.
     eapply rename_unfold_cofix. eassumption.
   - rewrite rename_subst_instance.
     eapply cumul_delta. 
     + eassumption.
     + rewrite rename_closed. 2: assumption.
       eapply declared_constant_closed_body. all: eauto.
   - rewrite rename_mkApps. simpl.
     eapply cumul_proj. rewrite nth_error_map. rewrite H. reflexivity.
   - eapply cumul_Trans; try apply X0; try apply X2; eauto. eapply urename_is_open_term; eauto. 
   - eapply cumul_Sym; intuition; eauto.
   - eapply cumul_Refl; intuition; eauto.
   - eapply cumul_Evar. cbn in *. 
     apply forallb_All in H0, H1. 
     eapply All2_All_mix_left in X; tea.
     eapply All2_All_mix_right in X; tea.
     eapply All2_map. eapply All2_impl. 1:tea. cbn; intros.
     eapply X3.1.2; intuition.
   - cbn in *. apply andb_and in H0 , H1. destruct H0 , H1.
     eapply cumul_App; try apply X0; try apply X2; eauto.         
   - cbn in H1, H2. apply andb_and in H1 , H2. destruct H1 , H2.
     eapply cumul_Lambda; try apply X0; try apply X2; eauto;
     try rewrite shiftnP_S; eauto. 
     * eapply urenaming_impl. 1: intro; rewrite shiftnP_S; eauto. apply urenaming_vass; eauto. 
     * rewrite on_free_vars_ctx_snoc. apply andb_and; split; eauto.
     * rewrite on_free_vars_ctx_snoc. apply andb_and; split; eauto.
       cbn. eapply urename_is_open_term; eauto.  
   - cbn in H1, H2. apply andb_and in H1, H2. destruct H1 , H2.
     eapply cumul_Prod; try apply X0; try apply X2; eauto;
     try rewrite shiftnP_S; eauto.
     * eapply urenaming_impl. 1: intro; rewrite shiftnP_S; eauto. apply urenaming_vass; eauto. 
     * rewrite on_free_vars_ctx_snoc. apply andb_and; split; eauto.
     * rewrite on_free_vars_ctx_snoc. apply andb_and; split; eauto.
       cbn. eapply urename_is_open_term; eauto.  
   - cbn in H1, H2. apply andb_and in H1, H2. destruct H1 , H2. 
     apply andb_and in H4, H5. destruct H4 , H5.
     eapply cumul_LetIn; try apply X0; try apply X2; eauto; try apply X4; 
     try rewrite shiftnP_S; eauto.
     * eapply urenaming_impl. 1: intro; rewrite shiftnP_S; eauto. apply urenaming_vdef; eauto. 
     * rewrite on_free_vars_ctx_snoc_def; eauto.
     * rewrite on_free_vars_ctx_snoc_def; eauto. 
       all: eapply urename_is_open_term; eauto.
   - cbn in H0, H1. 
     rename H into HΓ; rename H0 into H; rename H1 into H'.  
     apply andb_andI in H; apply andb_andI in H'; destruct H as [Hp H]; destruct H' as [Hp' H'].
     apply andb_andI in H; apply andb_andI in H'; destruct H as [Hreturn H]; destruct H' as [Hreturn' H'].
     apply andb_andI in H; apply andb_andI in H'; destruct H as [Hcontext H]; destruct H' as [Hcontext' H'].
     apply andb_andI in H; apply andb_andI in H'; destruct H as [Hc Hbrs]; destruct H' as [Hc' Hbrs']. 
     eapply cumul_Case.
     * unfold cumul_predicate. unfold cumul_predicate in X. destruct X as [Xparam [Xuniv [Xcontext [Xeq Xreturn]]]].
       repeat split; eauto. 
       + eapply All2_map. apply forallb_All in Hp, Hp'. eapply (All2_All_mix_left Hp) in Xparam. 
         eapply (All2_All_mix_right Hp') in Xparam.
         eapply All2_impl. 1: tea. cbn; intros. destruct X as [[X [X''' X']] X'']. apply X'; eauto.
       + unfold preturn. cbn. rewrite (All2_fold_length Xcontext). eapply Xreturn; eauto.
         ++ rewrite app_context_length.
            eapply urenaming_ext; try apply shiftnP_add; try reflexivity. 
            rewrite <- (All2_fold_length Xcontext).
            rewrite <- inst_case_predicate_context_length.
            rewrite test_context_k_closed_on_free_vars_ctx in Hcontext. 
            rewrite inst_case_predicate_context_rename; eauto. 
            apply urenaming_context; eauto.
         ++ rewrite test_context_k_closed_on_free_vars_ctx in Hcontext.
            unfold inst_case_predicate_context. 
            apply on_free_vars_ctx_inst_case_context; eauto.
         ++ unfold inst_case_predicate_context.
            unfold is_open_term. rewrite app_length.
            rewrite <- shiftnP_add. 
            rewrite inst_case_predicate_context_length.   
            eassumption.
         ++ unfold inst_case_predicate_context.
            unfold is_open_term. rewrite app_length.
            rewrite <- shiftnP_add. 
            rewrite inst_case_predicate_context_length.   
            rewrite (All2_fold_length Xcontext). eassumption.
         ++ rewrite test_context_k_closed_on_free_vars_ctx in Hcontext.
            unfold inst_case_predicate_context. apply on_free_vars_ctx_inst_case_context; eauto.
            +++ eapply All_forallb. apply All_map. apply forallb_All in Hp; eapply All_impl. 1: tea.
                cbn; intros. eapply urename_is_open_term; eauto.
            +++ unfold pparams. cbn. rewrite map_length. exact Hcontext.
     * apply X1; eauto. 
     * rename X2 into Hbrsbrs'.
       apply forallb_All in Hbrs, Hbrs'. apply (All2_All_mix_left Hbrs) in Hbrsbrs'. clear Hbrs.   
       apply (All2_All_mix_right Hbrs') in Hbrsbrs'. clear Hbrs'.
       apply All2_map. eapply All2_impl. 1: tea. cbn; intros x y [[Hx Heqxy ] Hy].
       destruct Heqxy as [[Hbcontext Hbody] Heqxy]. rewrite (All2_fold_length Hbcontext).
       split; eauto. 
       apply andb_and in Hx. destruct Hx as [Hx Hbodyx].
       apply andb_and in Hy. destruct Hy as [Hy Hbodyy].
       apply Heqxy; eauto.
       + rewrite app_context_length.
       eapply urenaming_ext; try apply shiftnP_add; try reflexivity. 
       rewrite <- (All2_fold_length Hbcontext).
       rewrite <- (inst_case_branch_context_length p).
       rewrite test_context_k_closed_on_free_vars_ctx in Hx. 
       rewrite inst_case_branch_context_rename; eauto. 
       apply urenaming_context; eauto.
       + rewrite test_context_k_closed_on_free_vars_ctx in Hx.
         unfold inst_case_predicate_context.
         apply on_free_vars_ctx_inst_case_context; eauto.
      + unfold inst_case_predicate_context.
         unfold is_open_term. rewrite app_length.
        rewrite <- shiftnP_add. 
        rewrite inst_case_branch_context_length.   
        eassumption.
      + unfold inst_case_predicate_context.
        unfold is_open_term. rewrite app_length.
        rewrite <- shiftnP_add. 
        rewrite inst_case_branch_context_length.    
        rewrite (All2_fold_length Hbcontext). eassumption.
      + rewrite test_context_k_closed_on_free_vars_ctx in Hcontext.
        unfold inst_case_predicate_context. apply on_free_vars_ctx_inst_case_context; eauto.
       ++ eapply All_forallb. apply All_map. apply forallb_All in Hp; eapply All_impl. 1: tea.
           cbn; intros. eapply urename_is_open_term; eauto.
       ++ unfold pparams. rewrite test_context_k_closed_on_free_vars_ctx in Hx.
        cbn. rewrite map_length. eassumption.
  - cbn in H0, H1. eapply cumul_Proj; try apply X0; eauto.
  - rewrite (All2_length X).
    eapply cumul_Fix. cbn in H0, H1.         
    apply forallb_All in H0, H1. 
    apply (All2_All_mix_left H0) in X. clear H0.   
    apply (All2_All_mix_right H1) in X. clear H1.
    apply All2_map. eapply All2_impl. 1: tea. cbn; intros.
    destruct X3 as [[Hx [[[_Htype [Htype Hbody_]] [Hbody Harg]] Hname]] Hy].
    repeat split; eauto.
    * eapply Htype; eauto. 
      + cbn in Hx; eapply andb_and in Hx. intuition.
      + cbn in Hy; eapply andb_and in Hy. intuition.
    * eapply Hbody; eauto. 
      + rewrite app_context_length.
      eapply urenaming_ext; try apply shiftnP_add; try reflexivity. 
      rewrite <- (All2_length X).
      rewrite rename_fix_context.
      rewrite <- fix_context_length.
      apply urenaming_context; eauto. 
      + rewrite on_free_vars_ctx_app. 
        apply andb_and; split; eauto.
        apply on_free_vars_fix_context.
        eapply All2_All_left. 1: tea. cbn; intros.
        apply X3.1.  
      + unfold test_def in Hx. apply andb_and in Hx. 
        destruct Hx as [_ Hx]. 
        unfold is_open_term. rewrite app_length.
        rewrite <- shiftnP_add. 
        rewrite fix_context_length. exact Hx.    
      + unfold test_def in Hy. apply andb_and in Hy. 
        destruct Hy as [_ Hy]. 
        unfold is_open_term. rewrite app_length.
        rewrite <- shiftnP_add. 
        rewrite fix_context_length. 
        rewrite (All2_length X). exact Hy.    
      + rewrite on_free_vars_ctx_app.   
        apply andb_and; split; eauto.
        apply on_free_vars_fix_context.
        apply All_map. 
        eapply All2_All_left. 1: tea. cbn ; intros.
        destruct X3 as [[Hx0 _] _].
        unfold test_def. unfold test_def in Hx0.
        apply andb_and in Hx0. destruct Hx0 as [Hx0type Hx0body].
        apply andb_and. cbn. split. 
        ++ eapply urename_is_open_term; eauto.
        ++ rewrite map_length. rewrite <-(All2_length X).
           rewrite <- fix_context_length.
           eapply urename_on_free_vars_shift; eauto.
           rewrite fix_context_length; eauto. 
  - rewrite (All2_length X).
    eapply cumul_CoFix. cbn in H0, H1.         
    apply forallb_All in H0, H1. 
    apply (All2_All_mix_left H0) in X. clear H0.   
    apply (All2_All_mix_right H1) in X. clear H1.
    apply All2_map. eapply All2_impl. 1: tea. cbn; intros.
    destruct X3 as [[Hx [[[_Htype [Htype Hbody_]] [Hbody Harg]] Hname]] Hy].
    repeat split; eauto.
    * eapply Htype; eauto. 
      + cbn in Hx; eapply andb_and in Hx. intuition.
      + cbn in Hy; eapply andb_and in Hy. intuition.
    * eapply Hbody; eauto. 
      + rewrite app_context_length.
      eapply urenaming_ext; try apply shiftnP_add; try reflexivity. 
      rewrite <- (All2_length X).
      rewrite rename_fix_context.
      rewrite <- fix_context_length.
      apply urenaming_context; eauto. 
      + rewrite on_free_vars_ctx_app. 
        apply andb_and; split; eauto.
        apply on_free_vars_fix_context.
        eapply All2_All_left. 1: tea. cbn; intros.
        apply X3.1.  
      + unfold test_def in Hx. apply andb_and in Hx. 
        destruct Hx as [_ Hx]. 
        unfold is_open_term. rewrite app_length.
        rewrite <- shiftnP_add. 
        rewrite fix_context_length. exact Hx.    
      + unfold test_def in Hy. apply andb_and in Hy. 
        destruct Hy as [_ Hy]. 
        unfold is_open_term. rewrite app_length.
        rewrite <- shiftnP_add. 
        rewrite fix_context_length. 
        rewrite (All2_length X). exact Hy.    
      + rewrite on_free_vars_ctx_app.   
        apply andb_and; split; eauto.
        apply on_free_vars_fix_context.
        apply All_map. 
        eapply All2_All_left. 1: tea. cbn ; intros.
        destruct X3 as [[Hx0 _] _].
        unfold test_def. unfold test_def in Hx0.
        apply andb_and in Hx0. destruct Hx0 as [Hx0type Hx0body].
        apply andb_and. cbn. split. 
        ++ eapply urename_is_open_term; eauto.
        ++ rewrite map_length. rewrite <-(All2_length X).
           rewrite <- fix_context_length.
           eapply urename_on_free_vars_shift; eauto.
           rewrite fix_context_length; eauto. 
  - repeat rewrite rename_mkApps. eapply cumul_Ind.
    * repeat rewrite map_length; eauto.
    * rewrite on_free_vars_mkApps in H1; 
      rewrite on_free_vars_mkApps in H2.
      apply andb_and in H1, H2. destruct H1 as [_ Hargs], H2 as [_ Hargs'].
      eapply forallb_All in Hargs, Hargs'.   
      apply (All2_All_mix_left Hargs) in X. clear Hargs.   
      apply (All2_All_mix_right Hargs') in X. clear Hargs'.
      apply All2_map. eapply All2_impl. 1: tea. cbn; intros.
      destruct X3 as [[Hx [Hxy_ Hxy]] Hy].    
      eapply Hxy; eauto.
  - repeat rewrite rename_mkApps. eapply cumul_Construct.
    * repeat rewrite map_length; eauto.
    * rewrite on_free_vars_mkApps in H1; 
      rewrite on_free_vars_mkApps in H2.
      apply andb_and in H1, H2. destruct H1 as [_ Hargs], H2 as [_ Hargs'].
      eapply forallb_All in Hargs, Hargs'.   
      apply (All2_All_mix_left Hargs) in X. clear Hargs.   
      apply (All2_All_mix_right Hargs') in X. clear Hargs'.
      apply All2_map. eapply All2_impl. 1: tea. cbn; intros.
      destruct X3 as [[Hx [Hxy_ Hxy]] Hy].    
      eapply Hxy; eauto.   
  - eapply cumul_Sort; eauto.
  - eapply cumul_Const; eauto.
Defined. 

Lemma cumulSpec_renameP P Σ Γ Δ f A B : let sP := shiftnP #|Γ| P in
    wf Σ.1 ->
    urenaming sP Δ Γ f ->
    is_closed_context Γ ->
    is_open_term Γ A ->
    is_open_term Γ B ->
    is_closed_context Δ ->
    Σ ;;; Γ |- A <=s B ->
    Σ ;;; Δ |- rename f A <=s rename f B.
Proof. 
  intros sP wfΣ Hren HfreeA HfreeB HΓ HΔ e. 
  revert Γ A B e sP Δ f wfΣ Hren HfreeA HfreeB HΓ HΔ e. 
  eapply (cumulSpec0_ind_all Σ.1 (eq_universe (global_ext_constraints Σ)) 
  (fun Rle Γ A B => forall Δ f, let sP := shiftnP #|Γ| P in
  wf Σ.1 ->
  urenaming sP Δ Γ f ->
  is_closed_context Γ ->
  is_open_term Γ A ->
  is_open_term Γ B ->
  is_closed_context Δ ->
  cumulSpec0 Σ.1 (eq_universe (global_ext_constraints Σ)) Rle Γ A B ->
  cumulSpec0 Σ.1 (eq_universe (global_ext_constraints Σ)) Rle Δ (rename f A) (rename f B))); intros; cbn.
  - rewrite rename_subst10. solve [econstructor].
  - rewrite rename_subst10. solve [econstructor].
  - rename X0 into hf. unfold urenaming in hf.
    destruct (nth_error Γ i) eqn:hnth; noconf H.
    assert (hav : sP i = true).
    { clear -H1; unfold sP, shiftnP in *. cbn in *. rewrite orb_false_r in H1. intuition. }
    clear H1. 
    specialize hf with (1 := hav) (2 := hnth).
    destruct hf as [decl' [e' [? [hr hbo]]]].
    rewrite H /= in hbo.
    rewrite lift0_rename.
    destruct (decl_body decl') eqn:hdecl => //. noconf hbo.
    sigma in H1. sigma. rewrite H1.
    relativize (t.[_]).
    2:{ setoid_rewrite rshiftk_S. rewrite -rename_inst.
        now rewrite -(lift0_rename (S (f i)) _). }
     eapply cumul_rel. now rewrite e' /= hdecl.
   - rewrite rename_mkApps. simpl.
     rewrite rename_iota_red //.
    * change (bcontext br) with (bcontext (rename_branch f br)).
     move/and5P: H2 => [_ _ _ _ hbrs].
     eapply nth_error_forallb in hbrs; tea. simpl in hbrs.
     move/andP: hbrs => [] clbctx clbod.
     rewrite closedn_ctx_on_free_vars.
     now rewrite test_context_k_closed_on_free_vars_ctx in clbctx.
   * eapply cumul_iota.
     + rewrite nth_error_map H /= //.
     + simpl. now len.
   - rewrite 2!rename_mkApps. simpl.
     eapply cumul_fix.
     + eapply rename_unfold_fix. eassumption.
     + eapply is_constructor_rename. assumption.
   - rewrite 2!rename_mkApps. simpl.
     eapply cumul_cofix_case.
     eapply rename_unfold_cofix. eassumption.
   - rewrite 2!rename_mkApps. simpl.
     eapply cumul_cofix_proj.
     eapply rename_unfold_cofix. eassumption.
   - rewrite rename_subst_instance.
     eapply cumul_delta. 
     + eassumption.
     + rewrite rename_closed. 2: assumption.
       eapply declared_constant_closed_body. all: eauto.
   - rewrite rename_mkApps. simpl.
     eapply cumul_proj. rewrite nth_error_map. rewrite H. reflexivity.
   - eapply cumul_Trans; try apply X0; try apply X2; eauto. eapply urename_is_open_term; eauto. 
   - eapply cumul_Sym; intuition; eauto.
   - eapply cumul_Refl; intuition; eauto.
   - eapply cumul_Evar. cbn in *. 
     apply forallb_All in H0, H1. 
     eapply All2_All_mix_left in X; tea.
     eapply All2_All_mix_right in X; tea.
     eapply All2_map. eapply All2_impl. 1:tea. cbn; intros.
     eapply X3.1.2; intuition.
   - cbn in *. apply andb_and in H0 , H1. destruct H0 , H1.
     eapply cumul_App; try apply X0; try apply X2; eauto.         
   - cbn in H1, H2. apply andb_and in H1 , H2. destruct H1 , H2.
     eapply cumul_Lambda; try apply X0; try apply X2; eauto;
     try rewrite shiftnP_S; eauto. 
     * eapply urenaming_impl. 1: intro; rewrite shiftnP_S; eauto. apply urenaming_vass; eauto. 
     * rewrite on_free_vars_ctx_snoc. apply andb_and; split; eauto.
     * rewrite on_free_vars_ctx_snoc. apply andb_and; split; eauto.
       cbn. eapply urename_is_open_term; eauto.  
   - cbn in H1, H2. apply andb_and in H1, H2. destruct H1 , H2.
     eapply cumul_Prod; try apply X0; try apply X2; eauto;
     try rewrite shiftnP_S; eauto.
     * eapply urenaming_impl. 1: intro; rewrite shiftnP_S; eauto. apply urenaming_vass; eauto. 
     * rewrite on_free_vars_ctx_snoc. apply andb_and; split; eauto.
     * rewrite on_free_vars_ctx_snoc. apply andb_and; split; eauto.
       cbn. eapply urename_is_open_term; eauto.  
   - cbn in H1, H2. apply andb_and in H1, H2. destruct H1 , H2. 
     apply andb_and in H4, H5. destruct H4 , H5.
     eapply cumul_LetIn; try apply X0; try apply X2; eauto; try apply X4; 
     try rewrite shiftnP_S; eauto.
     * eapply urenaming_impl. 1: intro; rewrite shiftnP_S; eauto. apply urenaming_vdef; eauto. 
     * rewrite on_free_vars_ctx_snoc_def; eauto.
     * rewrite on_free_vars_ctx_snoc_def; eauto. 
       all: eapply urename_is_open_term; eauto.
   - cbn in H0, H1. 
     rename H into HΓ; rename H0 into H; rename H1 into H'.  
     apply andb_andI in H; apply andb_andI in H'; destruct H as [Hp H]; destruct H' as [Hp' H'].
     apply andb_andI in H; apply andb_andI in H'; destruct H as [Hreturn H]; destruct H' as [Hreturn' H'].
     apply andb_andI in H; apply andb_andI in H'; destruct H as [Hcontext H]; destruct H' as [Hcontext' H'].
     apply andb_andI in H; apply andb_andI in H'; destruct H as [Hc Hbrs]; destruct H' as [Hc' Hbrs']. 
     eapply cumul_Case.
     * unfold cumul_predicate. unfold cumul_predicate in X. destruct X as [Xparam [Xuniv [Xcontext [Xeq Xreturn]]]].
       repeat split; eauto. 
       + eapply All2_map. apply forallb_All in Hp, Hp'. eapply (All2_All_mix_left Hp) in Xparam. 
         eapply (All2_All_mix_right Hp') in Xparam.
         eapply All2_impl. 1: tea. cbn; intros. destruct X as [[X [X''' X']] X'']. apply X'; eauto.
       + unfold preturn. cbn. rewrite (All2_fold_length Xcontext). eapply Xreturn; eauto.
         ++ rewrite app_context_length.
            eapply urenaming_ext; try apply shiftnP_add; try reflexivity. 
            rewrite <- (All2_fold_length Xcontext).
            rewrite <- inst_case_predicate_context_length.
            rewrite test_context_k_closed_on_free_vars_ctx in Hcontext. 
            rewrite inst_case_predicate_context_rename; eauto. 
            apply urenaming_context; eauto.
         ++ rewrite test_context_k_closed_on_free_vars_ctx in Hcontext.
            unfold inst_case_predicate_context. 
            apply on_free_vars_ctx_inst_case_context; eauto.
         ++ unfold inst_case_predicate_context.
            unfold is_open_term. rewrite app_length.
            rewrite <- shiftnP_add. 
            rewrite inst_case_predicate_context_length.   
            eassumption.
         ++ unfold inst_case_predicate_context.
            unfold is_open_term. rewrite app_length.
            rewrite <- shiftnP_add. 
            rewrite inst_case_predicate_context_length.   
            rewrite (All2_fold_length Xcontext). eassumption.
         ++ rewrite test_context_k_closed_on_free_vars_ctx in Hcontext.
            unfold inst_case_predicate_context. apply on_free_vars_ctx_inst_case_context; eauto.
            +++ eapply All_forallb. apply All_map. apply forallb_All in Hp; eapply All_impl. 1: tea.
                cbn; intros. eapply urename_is_open_term; eauto.
            +++ unfold pparams. cbn. rewrite map_length. exact Hcontext.
     * apply X1; eauto. 
     * rename X2 into Hbrsbrs'.
       apply forallb_All in Hbrs, Hbrs'. apply (All2_All_mix_left Hbrs) in Hbrsbrs'. clear Hbrs.   
       apply (All2_All_mix_right Hbrs') in Hbrsbrs'. clear Hbrs'.
       apply All2_map. eapply All2_impl. 1: tea. cbn; intros x y [[Hx Heqxy ] Hy].
       destruct Heqxy as [[Hbcontext Hbody] Heqxy]. rewrite (All2_fold_length Hbcontext).
       split; eauto. 
       apply andb_and in Hx. destruct Hx as [Hx Hbodyx].
       apply andb_and in Hy. destruct Hy as [Hy Hbodyy].
       apply Heqxy; eauto.
       + rewrite app_context_length.
       eapply urenaming_ext; try apply shiftnP_add; try reflexivity. 
       rewrite <- (All2_fold_length Hbcontext).
       rewrite <- (inst_case_branch_context_length p).
       rewrite test_context_k_closed_on_free_vars_ctx in Hx. 
       rewrite inst_case_branch_context_rename; eauto. 
       apply urenaming_context; eauto.
       + rewrite test_context_k_closed_on_free_vars_ctx in Hx.
         unfold inst_case_predicate_context.
         apply on_free_vars_ctx_inst_case_context; eauto.
      + unfold inst_case_predicate_context.
         unfold is_open_term. rewrite app_length.
        rewrite <- shiftnP_add. 
        rewrite inst_case_branch_context_length.   
        eassumption.
      + unfold inst_case_predicate_context.
        unfold is_open_term. rewrite app_length.
        rewrite <- shiftnP_add. 
        rewrite inst_case_branch_context_length.    
        rewrite (All2_fold_length Hbcontext). eassumption.
      + rewrite test_context_k_closed_on_free_vars_ctx in Hcontext.
        unfold inst_case_predicate_context. apply on_free_vars_ctx_inst_case_context; eauto.
       ++ eapply All_forallb. apply All_map. apply forallb_All in Hp; eapply All_impl. 1: tea.
           cbn; intros. eapply urename_is_open_term; eauto.
       ++ unfold pparams. rewrite test_context_k_closed_on_free_vars_ctx in Hx.
        cbn. rewrite map_length. eassumption.
  - cbn in H0, H1. eapply cumul_Proj; try apply X0; eauto.
  - rewrite (All2_length X).
    eapply cumul_Fix. cbn in H0, H1.         
    apply forallb_All in H0, H1. 
    apply (All2_All_mix_left H0) in X. clear H0.   
    apply (All2_All_mix_right H1) in X. clear H1.
    apply All2_map. eapply All2_impl. 1: tea. cbn; intros.
    destruct X3 as [[Hx [[[_Htype [Htype Hbody_]] [Hbody Harg]] Hname]] Hy].
    repeat split; eauto.
    * eapply Htype; eauto. 
      + cbn in Hx; eapply andb_and in Hx. intuition.
      + cbn in Hy; eapply andb_and in Hy. intuition.
    * eapply Hbody; eauto. 
      + rewrite app_context_length.
      eapply urenaming_ext; try apply shiftnP_add; try reflexivity. 
      rewrite <- (All2_length X).
      rewrite rename_fix_context.
      rewrite <- fix_context_length.
      apply urenaming_context; eauto. 
      + rewrite on_free_vars_ctx_app. 
        apply andb_and; split; eauto.
        apply on_free_vars_fix_context.
        eapply All2_All_left. 1: tea. cbn; intros.
        apply X3.1.  
      + unfold test_def in Hx. apply andb_and in Hx. 
        destruct Hx as [_ Hx]. 
        unfold is_open_term. rewrite app_length.
        rewrite <- shiftnP_add. 
        rewrite fix_context_length. exact Hx.    
      + unfold test_def in Hy. apply andb_and in Hy. 
        destruct Hy as [_ Hy]. 
        unfold is_open_term. rewrite app_length.
        rewrite <- shiftnP_add. 
        rewrite fix_context_length. 
        rewrite (All2_length X). exact Hy.    
      + rewrite on_free_vars_ctx_app.   
        apply andb_and; split; eauto.
        apply on_free_vars_fix_context.
        apply All_map. 
        eapply All2_All_left. 1: tea. cbn ; intros.
        destruct X3 as [[Hx0 _] _].
        unfold test_def. unfold test_def in Hx0.
        apply andb_and in Hx0. destruct Hx0 as [Hx0type Hx0body].
        apply andb_and. cbn. split. 
        ++ eapply urename_is_open_term; eauto.
        ++ rewrite map_length. rewrite <-(All2_length X).
           rewrite <- fix_context_length.
           eapply urename_on_free_vars_shift; eauto.
           rewrite fix_context_length; eauto. 
  - rewrite (All2_length X).
    eapply cumul_CoFix. cbn in H0, H1.         
    apply forallb_All in H0, H1. 
    apply (All2_All_mix_left H0) in X. clear H0.   
    apply (All2_All_mix_right H1) in X. clear H1.
    apply All2_map. eapply All2_impl. 1: tea. cbn; intros.
    destruct X3 as [[Hx [[[_Htype [Htype Hbody_]] [Hbody Harg]] Hname]] Hy].
    repeat split; eauto.
    * eapply Htype; eauto. 
      + cbn in Hx; eapply andb_and in Hx. intuition.
      + cbn in Hy; eapply andb_and in Hy. intuition.
    * eapply Hbody; eauto. 
      + rewrite app_context_length.
      eapply urenaming_ext; try apply shiftnP_add; try reflexivity. 
      rewrite <- (All2_length X).
      rewrite rename_fix_context.
      rewrite <- fix_context_length.
      apply urenaming_context; eauto. 
      + rewrite on_free_vars_ctx_app. 
        apply andb_and; split; eauto.
        apply on_free_vars_fix_context.
        eapply All2_All_left. 1: tea. cbn; intros.
        apply X3.1.  
      + unfold test_def in Hx. apply andb_and in Hx. 
        destruct Hx as [_ Hx]. 
        unfold is_open_term. rewrite app_length.
        rewrite <- shiftnP_add. 
        rewrite fix_context_length. exact Hx.    
      + unfold test_def in Hy. apply andb_and in Hy. 
        destruct Hy as [_ Hy]. 
        unfold is_open_term. rewrite app_length.
        rewrite <- shiftnP_add. 
        rewrite fix_context_length. 
        rewrite (All2_length X). exact Hy.    
      + rewrite on_free_vars_ctx_app.   
        apply andb_and; split; eauto.
        apply on_free_vars_fix_context.
        apply All_map. 
        eapply All2_All_left. 1: tea. cbn ; intros.
        destruct X3 as [[Hx0 _] _].
        unfold test_def. unfold test_def in Hx0.
        apply andb_and in Hx0. destruct Hx0 as [Hx0type Hx0body].
        apply andb_and. cbn. split. 
        ++ eapply urename_is_open_term; eauto.
        ++ rewrite map_length. rewrite <-(All2_length X).
           rewrite <- fix_context_length.
           eapply urename_on_free_vars_shift; eauto.
           rewrite fix_context_length; eauto. 
  - repeat rewrite rename_mkApps. eapply cumul_Ind.
    * repeat rewrite map_length; eauto.
    * rewrite on_free_vars_mkApps in H1; 
      rewrite on_free_vars_mkApps in H2.
      apply andb_and in H1, H2. destruct H1 as [_ Hargs], H2 as [_ Hargs'].
      eapply forallb_All in Hargs, Hargs'.   
      apply (All2_All_mix_left Hargs) in X. clear Hargs.   
      apply (All2_All_mix_right Hargs') in X. clear Hargs'.
      apply All2_map. eapply All2_impl. 1: tea. cbn; intros.
      destruct X3 as [[Hx [Hxy_ Hxy]] Hy].    
      eapply Hxy; eauto.
  - repeat rewrite rename_mkApps. eapply cumul_Construct.
    * repeat rewrite map_length; eauto.
    * rewrite on_free_vars_mkApps in H1; 
      rewrite on_free_vars_mkApps in H2.
      apply andb_and in H1, H2. destruct H1 as [_ Hargs], H2 as [_ Hargs'].
      eapply forallb_All in Hargs, Hargs'.   
      apply (All2_All_mix_left Hargs) in X. clear Hargs.   
      apply (All2_All_mix_right Hargs') in X. clear Hargs'.
      apply All2_map. eapply All2_impl. 1: tea. cbn; intros.
      destruct X3 as [[Hx [Hxy_ Hxy]] Hy].    
      eapply Hxy; eauto.   
  - eapply cumul_Sort; eauto.
  - eapply cumul_Const; eauto.
Defined. 

(* Lemma cumul_decls_renameP {P Σ Γ Γ' Δ Δ' f} d d' :
    wf Σ.1 ->
    urenaming P Δ Γ f ->
    urenaming P Δ' Γ' f ->
    on_free_vars_decl P d ->
    on_free_vars_decl P d' ->
    on_ctx_free_vars P Γ ->
    cumul_decls Σ Γ Γ' d d' ->
    cumul_decls Σ Δ Δ' (rename_decl f d) (rename_decl f d').
Proof.
  intros wf uren uren' ond ond' onΓ Hd; depelim Hd; constructor; tas;
    (eapply convSpec_renameP || eapply cumulSpec_renameP); tea.
  * now move/andP: ond => [].
  * now move/andP: ond' => [].
  * now move/andP: ond => [].
  * now move/andP: ond' => [].
Qed.

Lemma conv_decls_renameP {P Σ Γ Γ' Δ Δ' f} d d' :
    wf Σ.1 ->
    urenaming P Δ Γ f ->
    urenaming P Δ' Γ' f ->
    on_free_vars_decl P d ->
    on_free_vars_decl P d' ->
    on_ctx_free_vars P Γ ->
    conv_decls Σ Γ Γ' d d' ->
    conv_decls Σ Δ Δ' (rename_decl f d) (rename_decl f d').
Proof.
  intros wf uren uren' ond ond' onΓ Hd; depelim Hd; constructor; tas;
    (eapply convSpec_renameP || eapply cumulSpec_renameP); tea.
  * now move/andP: ond => [].
  * now move/andP: ond' => [].
  * now move/andP: ond => [].
  * now move/andP: ond' => [].
Qed. *)

Lemma on_free_vars_ctx_onctx_k P ctx :
  reflectT (onctx_k (fun k => on_free_vars (shiftnP k P)) 0 ctx)
    (on_free_vars_ctx P ctx).
Proof.
  rewrite -test_context_k_on_free_vars_ctx.
  apply (onctx_k_P reflectT_pred2).
Qed.

Lemma Alli_helper Q Γ :
  Alli (fun (i : nat) (d : context_decl) => ondecl (Q (#|Γ| - i + 0)) d) 1 Γ ->
  onctx_k Q 0 Γ.
Proof.
  move/(Alli_shiftn_inv 0 _ 1) => H.
  eapply Alli_impl; tea => n x /=.
  now replace (#|Γ| - S n + 0) with (Nat.pred #|Γ| - n + 0) by lia.
Qed.

Lemma All2_fold_impl_ind_onctx_k Q P P' Γ Δ :
  onctx_k Q 0 Γ ->
  onctx_k Q 0 Δ ->
  All2_fold P Γ Δ ->
  (forall Γ Δ d d',
    All2_fold P Γ Δ ->
    onctx_k Q 0 Γ ->
    All2_fold P' Γ Δ ->
    ondecl (Q #|Γ|) d ->
    ondecl (Q #|Δ|) d' ->
    P Γ Δ d d' ->
    P' Γ Δ d d') ->
  All2_fold P' Γ Δ.
Proof.
  intros qΓ qΔ cr Hcr.
  induction cr in qΓ, qΔ |- *; constructor; depelim qΓ; depelim qΔ; intuition eauto;
  rewrite -> Nat.sub_0_r, Nat.add_0_r in *;
  apply Alli_helper in qΓ; apply Alli_helper in qΔ;
  simpl in *; eauto.
Qed.

Lemma ondecl_on_free_vars_decl P d :
  ondecl (on_free_vars P) d ->
  on_free_vars_decl P d.
Proof.
  rewrite /on_free_vars_decl.
  now case: (ondeclP reflectT_pred).
Qed.

(* Lemma conv_ctx_renameP {Σ : global_env_ext} {P} {Γ Δ} {L R} f :
  wf Σ.1 ->
  urenaming P Δ Γ f ->
  on_free_vars_ctx P L ->
  on_free_vars_ctx P R ->
  on_ctx_free_vars P Γ ->
  conv_context Σ (Γ ,,, L) (Γ ,,, R) ->
  conv_context Σ (Δ ,,, rename_context f L) (Δ ,,, rename_context f R).
Proof.
  intros wf uren onL onL' onΓ H.
  rewrite /rename_context - !mapi_context_fold.
  pose proof (All2_fold_length H) as hlen.
  len in hlen. assert (#|L| = #|R|) by lia.
  eapply All2_fold_app_inv in H as [_ H] => //.
  eapply All2_fold_app; len => //; pcuic.
  { eapply conv_ctx_refl'. }
  move/on_free_vars_ctx_onctx_k: onL => onL.
  move/on_free_vars_ctx_onctx_k: onL' => onR.

  eapply All2_fold_mapi.
  eapply All2_fold_impl_ind_onctx_k; tea =>
    /= L' R' d d' IH onL' IH' ond ond'.
  simpl.
  rewrite !mapi_context_fold -/(rename_context f L') -/(rename_context f R').
  eapply conv_decls_renameP; eauto.
  + now eapply urenaming_context.
  + rewrite (All2_fold_length IH).
    now eapply urenaming_context.
  + now eapply ondecl_on_free_vars_decl.
  + rewrite (All2_fold_length IH').
    now eapply ondecl_on_free_vars_decl.
  + rewrite on_ctx_free_vars_extend // onΓ.
    now move/on_free_vars_ctx_onctx_k: onL'.
Qed. *)


(* Lemma cumul_ctx_renameP {Σ : global_env_ext} {P} {Γ Δ} {L R} f :
  wf Σ.1 ->
  urenaming P Δ Γ f ->
  on_free_vars_ctx P L ->
  on_free_vars_ctx P R ->
  on_ctx_free_vars P Γ ->
  cumul_context Σ (Γ ,,, L) (Γ ,,, R) ->
  cumul_context Σ (Δ ,,, rename_context f L) (Δ ,,, rename_context f R).
Proof.
  intros wf uren onL onL' onΓ H.
  rewrite /rename_context - !mapi_context_fold.
  pose proof (All2_fold_length H) as hlen.
  len in hlen. assert (#|L| = #|R|) by lia.
  eapply All2_fold_app_inv in H as [_ H] => //.
  eapply All2_fold_app; len => //; pcuic.
  { eapply cumul_ctx_refl'. }
  move/on_free_vars_ctx_onctx_k: onL => onL.
  move/on_free_vars_ctx_onctx_k: onL' => onR.

  eapply All2_fold_mapi.
  eapply All2_fold_impl_ind_onctx_k; tea =>
    /= L' R' d d' IH onL' IH' ond ond'.
  simpl.
  rewrite !mapi_context_fold -/(rename_context f L') -/(rename_context f R').
  eapply cumul_decls_renameP; eauto.
  + now eapply urenaming_context.
  + rewrite (All2_fold_length IH).
    now eapply urenaming_context.
  + now eapply ondecl_on_free_vars_decl.
  + rewrite (All2_fold_length IH').
    now eapply ondecl_on_free_vars_decl.
  + rewrite on_ctx_free_vars_extend // onΓ.
    now move/on_free_vars_ctx_onctx_k: onL'.
Qed. *)

Lemma subst1_inst :
  forall t n u,
    t{ n := u } = t.[⇑^n (u ⋅ ids)].
Proof.
  intros t n u.
  unfold subst1. rewrite subst_inst.
  eapply inst_ext. intro i.
  unfold Upn, subst_compose, subst_consn.
  destruct (Nat.ltb_spec0 i n).
  - rewrite -> nth_error_idsn_Some by assumption. reflexivity.
  - rewrite -> nth_error_idsn_None by lia.
    rewrite idsn_length.
    destruct (Nat.eqb_spec (i - n) 0).
    + rewrite e. simpl. reflexivity.
    + replace (i - n) with (S (i - n - 1)) by lia. simpl.
      destruct (i - n - 1) eqn: e.
      * simpl. reflexivity.
      * simpl. reflexivity.
Qed.
(* Hint Rewrite @subst1_inst : sigma. *)

Lemma rename_predicate_preturn f p :
  rename (shiftn #|p.(pcontext)| f) (preturn p) =
  preturn (rename_predicate f p).
Proof. reflexivity. Qed.

Lemma wf_local_app_renaming P Σ Γ Δ :
  All_local_env (lift_typing (fun (Σ : global_env_ext) (Γ' : context) (t T : term) =>
    forall P (Δ : PCUICEnvironment.context) (f : nat -> nat),
    renaming (shiftnP #|Γ ,,, Γ'| P) Σ Δ (Γ ,,, Γ') f -> Σ ;;; Δ |- rename f t : rename f T) Σ)
    Δ ->
  forall Δ' f,
  renaming (shiftnP #|Γ| P) Σ Δ' Γ f ->
  wf_local Σ (Δ' ,,, rename_context f Δ).
Proof.
  intros. destruct X0.
  induction X.
  - apply a.
  - simpl. destruct t0 as [s Hs].
    rewrite rename_context_snoc /=. constructor; auto.
    red. simpl. exists s.
    eapply (Hs P (Δ' ,,, rename_context f Γ0) (shiftn #|Γ0| f)).
    split => //.
    eapply urenaming_ext.
    { len. now rewrite -shiftnP_add. }
    { reflexivity. } now eapply urenaming_context.
  - destruct t0 as [s Hs]. red in t1.
    rewrite rename_context_snoc /=. constructor; auto.
    * red. exists s.
      apply (Hs P (Δ' ,,, rename_context f Γ0) (shiftn #|Γ0| f)).
      split => //.
      eapply urenaming_ext.
      { len; now rewrite -shiftnP_add. }
      { reflexivity. } now eapply urenaming_context.
    * red. apply (t1 P). split => //.
      eapply urenaming_ext.
      { len; now rewrite -shiftnP_add. }
      { reflexivity. } now eapply urenaming_context.
Qed.

Lemma rename_decompose_prod_assum f Γ t :
    decompose_prod_assum (rename_context f Γ) (rename (shiftn #|Γ| f) t)
    = let '(Γ, t) := decompose_prod_assum Γ t in (rename_context f Γ, rename (shiftn #|Γ| f) t).
Proof.
  induction t in Γ |- *. all: try reflexivity.
  - specialize (IHt2 (Γ ,, vass na t1)).
    rewrite rename_context_snoc /= in IHt2.
    simpl. now rewrite shiftn_add IHt2.
  - specialize (IHt3 (Γ ,, vdef na t1 t2)).
    rewrite rename_context_snoc /= in IHt3.
    simpl. now rewrite shiftn_add IHt3.
Qed.

Lemma rename_app_context f Γ Δ :
  rename_context f (Γ ,,, Δ) =
  rename_context f Γ ,,, rename_context (shiftn #|Γ| f) Δ.
Proof.
  rewrite /rename_context fold_context_k_app /app_context. f_equal.
  apply fold_context_k_ext. intros i x. now rewrite shiftn_add.
Qed.

Lemma rename_smash_context f Γ Δ :
  rename_context f (smash_context Γ Δ) =
  smash_context (rename_context (shiftn #|Δ| f) Γ) (rename_context f Δ).
Proof.
  induction Δ as [|[na [b|] ty] Δ] in Γ |- *; simpl; auto;
    rewrite ?shiftn0 // ?rename_context_snoc IHΔ /=; len.
  - f_equal. now rewrite rename_context_subst /= shiftn_add.
  - f_equal. rewrite rename_app_context /map_decl /= /app_context.
    f_equal.
    * now rewrite shiftn_add.
    * rewrite /rename_context fold_context_k_tip /map_decl /=. do 2 f_equal.
      now rewrite shiftn0.
Qed.

Lemma nth_error_rename_context f Γ n :
  nth_error (rename_context f Γ) n =
  option_map (map_decl (rename (shiftn (#|Γ| - S n) f))) (nth_error Γ n).
Proof.
  induction Γ in n |- *; intros.
  - simpl. unfold rename_context, fold_context_k; simpl; rewrite nth_error_nil. easy.
  - simpl. destruct n; rewrite rename_context_snoc.
    + simpl. lia_f_equal.
    + simpl. rewrite IHΓ; simpl in *. 
      assert (e : #|Γ| - S n = S #|Γ| - S (S n)). { lia. }
      rewrite e. reflexivity.
Qed.

Lemma rename_check_one_fix f (mfix : mfixpoint term) d x :
  check_one_fix d = Some x ->
  check_one_fix (map_def (rename f) (rename (shiftn #|mfix| f)) d) = Some x.
Proof.
  destruct d; simpl.
  move: (rename_decompose_prod_assum f [] dtype).
  rewrite shiftn0. intros ->.
  destruct decompose_prod_assum.
  rewrite -(rename_smash_context f []).
  destruct nth_error eqn:hnth => //.
  pose proof (nth_error_Some_length hnth). len in H.
  simpl in H.
  destruct (nth_error (List.rev (rename_context _ _)) _) eqn:hnth'.
  2:{ eapply nth_error_None in hnth'. len in hnth'. simpl in hnth'. lia. }
  rewrite nth_error_rev_inv in hnth; len; auto.
  len in hnth. simpl in hnth.
  rewrite nth_error_rev_inv in hnth'; len; auto.
  len in hnth'. simpl in hnth'.
  rewrite nth_error_rename_context /= hnth /= in hnth'. noconf hnth'.
  simpl.
  destruct decompose_app eqn:da. len.
  destruct t0 => /= //.
  eapply decompose_app_inv in da. rewrite da.
  rewrite rename_mkApps. simpl. rewrite decompose_app_mkApps //.
Qed.

Lemma rename_check_one_cofix f (mfix : mfixpoint term) d x :
  check_one_cofix d = Some x ->
  check_one_cofix (map_def (rename f) (rename (shiftn #|mfix| f)) d) = Some x.
Proof.
  destruct d; simpl.
  move: (rename_decompose_prod_assum f [] dtype).
  rewrite shiftn0. intros ->.
  destruct decompose_prod_assum.
  destruct decompose_app eqn:da.
  destruct t0 => /= //.
  eapply decompose_app_inv in da. rewrite da /=.
  rewrite rename_mkApps. simpl. rewrite decompose_app_mkApps //.
Qed.

Lemma rename_wf_fixpoint Σ f mfix :
  wf_fixpoint Σ mfix ->
  wf_fixpoint Σ (map (map_def (rename f) (rename (shiftn #|mfix| f))) mfix).
Proof.
  unfold wf_fixpoint.
  rewrite map_map_compose.
  destruct (map_option_out (map check_one_fix mfix)) as [[]|] eqn:hmap => //.
  eapply map_option_out_impl in hmap.
  2:{ intros x y. apply (rename_check_one_fix f mfix). }
  now rewrite hmap.
Qed.

Lemma rename_wf_cofixpoint Σ f mfix :
  wf_cofixpoint Σ mfix ->
  wf_cofixpoint Σ (map (map_def (rename f) (rename (shiftn #|mfix| f))) mfix).
Proof.
  rewrite /wf_cofixpoint map_map_compose.
  destruct (map_option_out (map check_one_cofix mfix)) as [[]|] eqn:hmap => //.
  eapply map_option_out_impl in hmap.
  2:{ intros x y. apply (rename_check_one_cofix f mfix). }
  now rewrite hmap.
Qed.

Lemma rename_subst_telescope f s Γ :
  rename_telescope f (subst_telescope s 0 Γ) =
  subst_telescope (map (rename f) s) 0
    (rename_telescope (shiftn #|s| f) Γ).
Proof.
  rewrite /rename_telescope /subst_telescope.
  rewrite !mapi_compose. apply mapi_ext => k' d.
  rewrite !compose_map_decl; apply map_decl_ext => t'.
  now rewrite Nat.add_0_r rename_subst.
Qed.

Instance rename_telescope_ext : Proper (`=1` ==> `=1`) rename_telescope.
Proof.
  intros f g Hfg Γ.
  rewrite /rename_telescope. apply mapi_ext => n x.
  now rewrite Hfg.
Qed.

Lemma rename_telescope_shiftn0 f Γ : rename_telescope (shiftn 0 f) Γ = rename_telescope f Γ.
Proof. now sigma. Qed.

Lemma rename_telescope_cons f d Γ :
  rename_telescope f (d :: Γ) = rename_decl f d :: rename_telescope (shiftn 1 f) Γ.
Proof.
  rewrite /rename_telescope mapi_cons /rename_decl.
  f_equal; sigma => //.
  apply mapi_ext => i x. now rewrite shiftn_add Nat.add_1_r.
Qed.

Hint Rewrite <- Upn_ren : sigma.

(** For an unconditional renaming defined on all variables in the source context *)
Lemma typing_rename_prop : env_prop
  (fun Σ Γ t A =>
    forall P Δ f,
    renaming (shiftnP #|Γ| P) Σ Δ Γ f ->
    Σ ;;; Δ |- rename f t : rename f A)
   (fun Σ Γ =>
    wf_local Σ Γ ×
   All_local_env
   (lift_typing (fun (Σ : global_env_ext) (Γ : context) (t T : term)
    =>
    forall P (Δ : PCUICEnvironment.context) (f : nat -> nat),
    renaming (shiftnP #|Γ| P) Σ Δ Γ f ->
    Σ;;; Δ |- rename f t : rename f T) Σ) Γ).
Proof.
  apply typing_ind_env.

  - intros Σ wfΣ Γ wfΓ HΓ. split; auto.
    induction HΓ; constructor; firstorder eauto.

  - intros Σ wfΣ Γ wfΓ n decl isdecl ihΓ P Δ f hf.
    simpl in *.
    eapply hf in isdecl as h => //.
    2:{ rewrite /shiftnP. eapply nth_error_Some_length in isdecl. now nat_compare_specs. }
    destruct h as [decl' [isdecl' [? [h1 h2]]]].
    rewrite lift0_rename rename_compose h1 -lift0_rename.
    econstructor. all: auto. apply hf.

  - intros Σ wfΣ Γ wfΓ l X H0 P Δ f [hΔ hf].
    simpl. constructor. all: auto.

  - intros Σ wfΣ Γ wfΓ na A B s1 s2 X hA ihA hB ihB P Δ f hf.
    rewrite /=. econstructor.
    + eapply ihA; eauto.
    + eapply ihB; eauto.
      simpl.
      eapply renaming_extP. { now rewrite -(shiftnP_add 1). }
      eapply renaming_vass. 2: eauto.
      constructor.
      * destruct hf as [hΔ hf]. auto.
      * simpl. exists s1. eapply ihA; eauto.
  - intros Σ wfΣ Γ wfΓ na A t s1 B X hA ihA ht iht P Δ f hf.
    simpl.
     (* /andP [_ havB]. *)
    simpl. econstructor.
    + eapply ihA; eauto.
    + eapply iht; eauto; simpl.
      eapply renaming_extP. { now rewrite -(shiftnP_add 1). }
      eapply renaming_vass. 2: eauto.
      constructor.
      * destruct hf as [hΔ hf]. auto.
      * simpl. exists s1. eapply ihA; eauto.
  - intros Σ wfΣ Γ wfΓ na b B t s1 A X hB ihB hb ihb ht iht P Δ f hf.
    simpl. econstructor.
    + eapply ihB; tea.
    + eapply ihb; tea.
    + eapply iht; tea.
      eapply renaming_extP. { now rewrite -(shiftnP_add 1). }
      eapply renaming_vdef. 2: eauto.
      constructor.
      * destruct hf. assumption.
      * simpl. eexists. eapply ihB; tea.
      * simpl. eapply ihb; tea.
  - intros Σ wfΣ Γ wfΓ t na A B s u X hty ihty ht iht hu ihu P Δ f hf.
    simpl. eapply meta_conv.
    + eapply type_App.
      * simpl in ihty. eapply ihty; tea.
      * simpl in iht. eapply iht. eassumption.
      * eapply ihu. eassumption.
    + autorewrite with sigma. rewrite !subst1_inst. sigma.
      eapply inst_ext => i.
      unfold subst_cons, ren, shiftn, subst_compose. simpl.
      destruct i.
      * simpl. reflexivity.
      * simpl. replace (i - 0) with i by lia.
        reflexivity.
  - intros Σ wfΣ Γ wfΓ cst u decl X X0 isdecl hconst P Δ f hf.
    simpl. eapply meta_conv.
    + constructor. all: eauto. apply hf.
    + rewrite rename_subst_instance. f_equal.
      rewrite rename_closed. 2: auto.
      eapply declared_constant_closed_type. all: eauto.
  - intros Σ wfΣ Γ wfΓ ind u mdecl idecl isdecl X X0 hconst P Δ σ hf.
    simpl. eapply meta_conv.
    + econstructor. all: eauto. apply hf.
    + rewrite rename_subst_instance. f_equal.
      rewrite rename_closed. 2: auto.
      eapply declared_inductive_closed_type. all: eauto.
  - intros Σ wfΣ Γ wfΓ ind i u mdecl idecl cdecl isdecl X X0 hconst P Δ f hf.
    simpl. eapply meta_conv.
    + econstructor. all: eauto. apply hf.
    + rewrite rename_closed. 2: reflexivity.
      eapply declared_constructor_closed_type. all: eauto.
  - intros Σ wfΣ Γ wfΓ ci p c brs indices ps mdecl idecl isdecl HΣ.
    intros [_ IHΔ] ci_npar eqpctx predctx wfp cup wfpctx Hpret IHpret [_ IHpredctx] isallowed.
    intros Hcxti IHctxi Hc IHc iscof ptm wfbrs Hbrs P Δ f Hf.
    simpl.
    rewrite rename_mkApps.
    rewrite map_app. simpl.
    rewrite /ptm. rewrite rename_it_mkLambda_or_LetIn.
    relativize #|predctx|.
    * erewrite rename_predicate_preturn.
      rewrite rename_case_predicate_context //.
      eapply type_Case; eauto; tea; rewrite - ?rename_case_predicate_context.
      all:tea.
      + now eapply rename_wf_predicate.
      + simpl. eauto.
        apply All_local_env_app_inv in IHpredctx as [].
        eapply wf_local_app_renaming; eauto. apply a0.
      + simpl. eapply IHpret.
        split.
        ++ apply All_local_env_app_inv in IHpredctx as [].
          eapply wf_local_app_renaming; eauto. apply a0.
        ++ rewrite /predctx.
           eapply urenaming_ext.
           { len. now rewrite -shiftnP_add. }
           { reflexivity. }
          relativize #|pcontext p|; [eapply urenaming_context|].
          { apply Hf. }
          now rewrite case_predicate_context_length.
      + revert IHctxi.
        rewrite /= /id -map_app.
        rewrite -{2}[subst_instance _ _](rename_closedn_ctx f 0).
        { pose proof (declared_inductive_closed_pars_indices isdecl).
          now rewrite closedn_subst_instance_context. }
        rewrite rename_context_telescope.
        rewrite rename_telescope_shiftn0.
        clear -P Δ f Hf.
        induction 1.
        { constructor; auto. }
        { simpl. rewrite rename_telescope_cons.
          constructor; cbn; eauto.
          now rewrite rename_subst_telescope /= in IHIHctxi. }
        { simpl. rewrite rename_telescope_cons.
          constructor; cbn; eauto.
          now rewrite rename_subst_telescope /= in IHIHctxi. }
      + simpl. unfold id.
        specialize (IHc _ _ _ Hf).
        now rewrite rename_mkApps map_app in IHc.
      + now eapply rename_wf_branches.
      + eapply Forall2_All2 in wfbrs.
        eapply All2i_All2_mix_left in Hbrs; eauto.
        eapply All2i_nth_hyp in Hbrs.
        eapply All2i_map_right, (All2i_impl Hbrs) => i cdecl br.
        set (brctxty := case_branch_type _ _ _ _ _ _ _ _).
        move=> [Hnth [wfbr [eqbctx [[wfbctx IHbctx] [Hbod [IHbod [Hbty IHbty]]]]]]].
        rewrite -(rename_closed_constructor_body mdecl cdecl f).
        { eapply (declared_constructor_closed (c:=(ci.(ci_ind),i))); eauto.
          split; eauto. }
        split; auto.
        { simpl. rewrite -rename_cstr_branch_context //.
          1:eapply (declared_inductive_closed_params isdecl).
          rewrite rename_closedn_ctx //.
          eapply closed_cstr_branch_context. split; tea. }
        cbn -[case_branch_type].
        rewrite case_branch_type_fst.
        rewrite -rename_case_branch_context_gen //.
        2-3:len.
        1:exact (declared_inductive_closed_params isdecl).
        1:rewrite (wf_branch_length wfbr) //.
        1:rewrite (wf_predicate_length_pars wfp).
        1:now rewrite (declared_minductive_ind_npars isdecl).
        set (brctx' := rename_context f _).
        assert (wf_local Σ (Δ ,,, brctx')).
        { apply All_local_env_app_inv in IHbctx as [].
          eapply wf_local_app_renaming; tea. simpl. apply a0. }
        split => //.
        rewrite rename_case_predicate_context // rename_case_branch_type //.
        split.
        { eapply IHbod => //.
          split => //.
          * eapply urenaming_ext.
          { now rewrite app_context_length -shiftnP_add. }
          { reflexivity. }
          relativize #|bcontext br|; [eapply urenaming_context|].
          1:apply Hf. rewrite /brctxty case_branch_type_fst case_branch_context_length //. }
        { eapply IHbty. split=> //.
          rewrite /brctx' case_branch_type_fst.
          rewrite (wf_branch_length wfbr).
          eapply urenaming_ext.
          { now rewrite app_context_length -shiftnP_add. }
          { reflexivity. }
          rewrite -(wf_branch_length wfbr).
          rewrite -/(rename_context f _).
          relativize #|bcontext br|; [eapply urenaming_context, Hf|len].
          now rewrite case_branch_context_length. }
    * rewrite /predctx case_predicate_context_length //.
  - intros Σ wfΣ Γ wfΓ p c u mdecl idecl cdecl pdecl isdecl args X X0 hc ihc e ty
           P Δ f hf.
    simpl. eapply meta_conv.
    + econstructor.
      * eassumption.
      * eapply meta_conv.
        -- eapply ihc; tea.
        -- rewrite rename_mkApps. simpl. reflexivity.
      * rewrite map_length. assumption.
    + rewrite rename_subst0. simpl. rewrite map_rev. f_equal.
      rewrite rename_subst_instance. f_equal.
      rewrite rename_closedn. 2: reflexivity.
      eapply declared_projection_closed_type in isdecl.
      rewrite List.rev_length. rewrite e. assumption.

  - intros Σ wfΣ Γ wfΓ mfix n decl types H1 hdecl [_ X] ihmfixt ihmfixb wffix P Δ f hf.
    apply All_local_env_app_inv in X as [_ X].
    eapply wf_local_app_renaming in X; tea.
    simpl. eapply meta_conv.
    + eapply type_Fix.
      * destruct hf; eapply fix_guard_rename; eauto.
      * rewrite nth_error_map. rewrite hdecl. simpl. reflexivity.
      * apply hf.
      * apply All_map, (All_impl ihmfixt).
        intros x [s [Hs IHs]].
        exists s. now eapply IHs.
      * apply All_map, (All_impl ihmfixb).
        intros x [Hb IHb].
        destruct x as [na ty bo rarg]. simpl in *.
        rewrite rename_fix_context.
        eapply meta_conv.
        ++ apply (IHb P (Δ ,,, rename_context f types) (shiftn #|mfix| f)).
          split; auto. subst types. rewrite -(fix_context_length mfix).
          eapply urenaming_ext.
          { now rewrite app_context_length -shiftnP_add. }
          { reflexivity. }
          apply urenaming_context; auto. apply hf.
        ++ len. now sigma.
      * now eapply rename_wf_fixpoint.
    + reflexivity.

  - intros Σ wfΣ Γ wfΓ mfix n decl types guard hdecl [_ X] ihmfixt ihmfixb wfcofix P Δ f hf.
    apply All_local_env_app_inv in X as [_ X].
    eapply wf_local_app_renaming in X; eauto.
    simpl. eapply meta_conv.
    + eapply type_CoFix; auto.
      * destruct hf; eapply cofix_guard_rename; eauto.
      * rewrite nth_error_map. rewrite hdecl. simpl. reflexivity.
      * apply hf.
      * apply All_map, (All_impl ihmfixt).
        intros x [s [Hs IHs]].
        exists s. now eapply IHs.
      * apply All_map, (All_impl ihmfixb).
        intros x [Hb IHb].
        destruct x as [na ty bo rarg]. simpl in *.
        rewrite rename_fix_context.
        eapply meta_conv.
        ++ apply (IHb P (Δ ,,, rename_context f types) (shiftn #|mfix| f)).
            split; auto. subst types. rewrite -(fix_context_length mfix).
            eapply urenaming_ext.
            { now rewrite app_context_length -shiftnP_add. }
            { reflexivity. }
            apply urenaming_context; auto. apply hf.
        ++ len. now sigma.
      * now eapply rename_wf_cofixpoint.
    + reflexivity.

  - intros Σ wfΣ Γ wfΓ t A B X hwf ht iht htB ihB cum P Δ f hf.
    eapply type_Cumul.
    + eapply iht; tea.
    + eapply ihB; tea.
    + eapply cumulSpec_renameP.  all: try eassumption.
      * apply hf.
      * apply wf_local_closed_context; eauto. 
      * pose proof (type_closed ht). 
        now eapply closedn_on_free_vars in H. 
      * pose proof (subject_closed htB).
        now eapply closedn_on_free_vars in H.
      * pose proof (closed_ctx_on_free_vars P _ (closed_wf_local _ (typing_wf_local ht))).
        destruct hf as [HΔ _]. apply wf_local_closed_context; eauto. 
Qed.

Lemma typing_rename_P {P Σ Γ Δ f t A} {wfΣ : wf Σ.1} :
  renaming (shiftnP #|Γ| P) Σ Δ Γ f ->
  Σ ;;; Γ |- t : A ->
  Σ ;;; Δ |- rename f t : rename f A.
Proof.
  intros hf h.
  revert Σ wfΣ Γ t A h P Δ f hf.
  apply typing_rename_prop.
Qed.

Lemma typing_rename {Σ Γ Δ f t A} {wfΣ : wf Σ.1} :
  renaming (closedP #|Γ| xpredT) Σ Δ Γ f ->
  Σ ;;; Γ |- t : A ->
  Σ ;;; Δ |- rename f t : rename f A.
Proof.
  intros hf h.
  eapply (typing_rename_P (P:=fun _ => false)) ; eauto.
Qed.

End Renaming.
