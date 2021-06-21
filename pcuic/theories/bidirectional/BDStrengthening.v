From Coq Require Import Bool List Arith Lia.
From Coq Require String.
From MetaCoq.Template Require Import config utils monad_utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
  PCUICLiftSubst PCUICUnivSubst PCUICEquality PCUICUtils
  PCUICPosition PCUICTyping PCUICSigmaCalculus PCUICRename PCUICOnFreeVars PCUICClosed PCUICConfluence PCUICSpine PCUICInductiveInversion PCUICParallelReductionConfluence.

From MetaCoq.PCUIC Require Import BDEnvironmentTyping BDTyping BDToPCUIC BDFromPCUIC.

Require Import ssreflect ssrbool.
Require Import Coq.Program.Equality.

Lemma addnP_strengthenP0 i P : addnP i (strengthenP 0 i P) =1 P.
Proof.
  intros ?.
  rewrite /addnP /strengthenP.
  repeat nat_compare_specs.
  by rewrite minus_plus.
Qed.

Lemma on_ctx_free_vars_strengthenP P Γ Γ' Γ'':
  on_ctx_free_vars P Γ ->
  on_ctx_free_vars P Γ'' ->
  on_ctx_free_vars (strengthenP #|Γ''| #|Γ'| P) (Γ,,,Γ',,,lift_context #|Γ'| 0 Γ'').
Proof.
  intros hΓ hΓ''.
  rewrite !PCUICInst.on_ctx_free_vars_app.
  repeat (apply /andP ; split).
  - admit.
  - rewrite lift_context_length.
    rewrite /on_ctx_free_vars.
    apply alli_Alli.
    eapply forall_nth_error_Alli.
    intros i ? ?.
    assert (i < #|Γ'|) by (apply nth_error_Some ; congruence).
    rewrite /addnP /strengthenP /=.
    by repeat nat_compare_specs.
  - rewrite addnP_add lift_context_length.
    
Admitted.

Lemma on_free_vars_ctx_tip P d : on_free_vars_ctx P [d] = on_free_vars_decl P d.
Proof. cbn; rewrite andb_true_r // shiftnP0 //. Qed.

Lemma on_free_vars_it_mkLambda_or_LetIn {P Δ t} : 
  on_free_vars P (it_mkLambda_or_LetIn Δ t) = 
    on_free_vars_ctx P Δ && on_free_vars (shiftnP #|Δ| P) t.
Proof.
  move: P. induction Δ using rev_ind => P.
  - cbn. now rewrite shiftnP0.
  - destruct x as [na [b|] ty]; rewrite it_mkLambda_or_LetIn_app /= /mkLambda_or_LetIn /=.
    rewrite on_free_vars_ctx_app /= IHΔ !lengths /= shiftnP_add on_free_vars_ctx_tip /= 
      /on_free_vars_decl /test_decl /=. ring.
    rewrite on_free_vars_ctx_app /= IHΔ !lengths /= shiftnP_add on_free_vars_ctx_tip /= 
     /on_free_vars_decl /test_decl /=. ring.
Qed.

Lemma on_free_vars_case_predicate_context `{checker_flags} Σ ci mdecl idecl p P :
  wf Σ ->
  declared_inductive Σ ci mdecl idecl ->
  forallb (on_free_vars P) (pparams p) ->
  wf_predicate mdecl idecl p ->
  All2 (compare_decls eq eq) (pcontext p) (ind_predicate_context ci mdecl idecl) ->
  on_free_vars_ctx P (case_predicate_context ci mdecl idecl p).
Proof.
  intros.
  rewrite /case_predicate_context /case_predicate_context_gen /pre_case_predicate_context_gen /inst_case_context.
  erewrite <- on_free_vars_map2_cstr_args.
  2: rewrite fold_context_k_length !map_length ; eapply All2_length ; tea.
  apply on_free_vars_ctx_subst_context.
  2: by rewrite forallb_rev.
  rewrite on_free_vars_subst_instance_context List.rev_length.
  apply closedn_ctx_on_free_vars_shift.
  replace #|pparams p| with (context_assumptions (ind_params mdecl)).
  1: eapply closed_ind_predicate_context ; tea ; eapply declared_minductive_closed ; eauto.
  erewrite wf_predicate_length_pars ; tea.
  eapply PCUICDeclarationTyping.onNpars, PCUICWeakeningEnv.on_declared_minductive ; eauto.
Qed.

Definition unlift_renaming n k i := if i <? k then i else i - n.
Definition unlift n k := rename (unlift_renaming n k).

Lemma lift_unlift n k : (unlift_renaming n k) ∘ (lift_renaming n k) =1 ren_id.
Proof.
  intros i.
  rewrite /unlift_renaming /lift_renaming /ren_id.
  repeat nat_compare_specs.
Qed.

Corollary lift_unlift_term {n k} t : unlift n k (lift n k t) = t.
Proof.
  by rewrite lift_rename /unlift rename_compose lift_unlift rename_ren_id.
Qed.

Corollary lift_unlift_context {n k} Γ :
  rename_context (unlift_renaming n k) (rename_context (lift_renaming n k) Γ) = Γ.
Proof.
  etransitivity.
  2: by apply fold_context_k_id.
  rewrite /rename_context fold_context_k_compose.
  apply fold_context_k_proper => //.
  intros ? ?.
  etransitivity.
  2: by apply rename_ren_id.
  rewrite rename_compose.
  apply rename_proper => //.
  intros ?.
  rewrite /shiftn /unlift_renaming /lift_renaming /ren_id.
  repeat nat_compare_specs.
Qed.

Lemma urenaming_strengthen P Γ Γ' Γ'' :
  urenaming (strengthenP #|Γ''| #|Γ'| P) (Γ,,,Γ'') (Γ ,,, Γ' ,,, lift_context #|Γ'| 0 Γ'') (unlift_renaming #|Γ'| #|Γ''|).
Proof.
  rewrite <- PCUICWeakening.rename_context_lift_context.
  intros i decl' pi nthi.
  rewrite /strengthenP in pi.
  destruct (Nat.ltb_spec0 i #|Γ''|) as [iΓ''|iΓ''].
  - rewrite nth_error_app_context_lt in nthi.
    1: by rewrite fold_context_k_length.
    rewrite nth_error_rename_context in nthi.
    apply option_map_Some in nthi as [decl'' []].
    subst.
    eexists ; split ; [idtac|split ; [idtac|split]].
    + rewrite /unlift_renaming.
      move: (iΓ'') => /Nat.ltb_spec0 ->.
      rewrite nth_error_app_context_lt //.
      eassumption.
    + reflexivity.
    + rewrite /= rename_compose.
      apply rename_proper ; auto.
      intros x.
      rewrite !rshiftk_S lift_renaming_spec -(shiftn_rshiftk _ _ _) !shiftn_add -lift_renaming_spec.
      rewrite Nat.add_0_r le_plus_minus_r.
      1: lia.
      rewrite (lift_unlift _ _ _) /ren_id /unlift_renaming.
      nat_compare_specs.
    + cbn ; destruct (decl_body decl'') ; rewrite //=.
      f_equal.
      rewrite rename_compose.
      apply rename_proper ; auto.
      intros x.
      change (S (i + _)) with
        (rshiftk (S i) (shiftn (#|Γ''| - S i) (lift_renaming #|Γ'| 0) x)).
      rewrite shiftn_lift_renaming lift_renaming_spec -(shiftn_rshiftk _ _ _) shiftn_add.
      rewrite -lift_renaming_spec Nat.add_0_r le_plus_minus_r.
      1: lia.
      rewrite (lift_unlift _ _ _) /unlift_renaming.
      nat_compare_specs.
      reflexivity.

  - rewrite -app_context_assoc /= in nthi.
    destruct (Nat.ltb_spec0 i (#|Γ''| + #|Γ'|)) as [iΓ'|iΓ'] ; cbn in * ; [congruence|..].
    apply Nat.nlt_ge in iΓ'.
    rewrite nth_error_app_context_ge app_length /= rename_context_length // in nthi.
    eexists ; repeat split.
    + rewrite /unlift_renaming.
      nat_compare_specs.
      rewrite nth_error_app_context_ge ; [lia|..].
      rewrite -nthi.
      f_equal.
      lia.
    + apply rename_proper ; auto.
      intros x.
      rewrite /unlift_renaming.
      repeat nat_compare_specs.
    + destruct (decl_body decl') ; rewrite //=.
      f_equal.
      apply rename_proper ; auto.
      intros x.
      rewrite /unlift_renaming.
      repeat nat_compare_specs.
Qed.

Section OnFreeVars.

  Context `{cf : checker_flags} (Σ : global_env_ext) (wfΣ : wf Σ).

  Let Pinfer Γ t T :=
    forall P,
    on_ctx_free_vars P Γ ->
    on_free_vars P t ->
    on_free_vars P T.

  Let Psort (Γ : context) (t : term) (u : Universe.t) := True.

  Let Pprod Γ t (na : aname) A B :=
    forall P,
    on_ctx_free_vars P Γ ->
    on_free_vars P t ->
    on_free_vars P A × on_free_vars (shiftnP 1 P) B.

  Let Pind Γ (ind : inductive) t (u : Instance.t) args :=
    forall P,
    on_ctx_free_vars P Γ ->
    on_free_vars P t ->
    All (on_free_vars P) args.

  Let Pcheck (Γ : context) (t : term) (T : term) := True.

  Let PΓ (Γ : context) :=
    True.

  Let PΓ_rel (Γ Γ' : context) := True.

  Theorem bidirectional_on_free_vars : env_prop_bd Σ Pcheck Pinfer Psort Pprod Pind PΓ PΓ_rel.
  Proof.
    apply bidir_ind_env.

    - constructor.

    - constructor.

    - intros. red.
      intros P HΓ Hn. 
      eapply alli_Alli, Alli_nth_error in HΓ ; tea.
      apply on_free_vars_lift0.
      by move: HΓ => /implyP /(_ Hn) /andP [].

    - easy.
    - easy.
    - intros until bty.
      move => _ _ _ Hbty ? ? /= /andP [] ? ?.
      apply /andP ; split ; tea.
      apply Hbty ; tea.
      rewrite on_ctx_free_vars_snoc.
      apply /andP ; split ; tea.

    - intros until A.
      move => _ _ _ _ _ Ht ? ? /= /andP [] ? /andP [] ? ?.
      repeat (apply /andP ; split ; tea).
      apply Ht ; tea.
      rewrite on_ctx_free_vars_snoc.
      repeat (apply /andP ; split ; tea).

    - intros until u.
      move => _ HAB _ _ ? ? /= /andP [] ? ?.
      edestruct HAB ; tea.
      apply on_free_vars_subst1 ; tea.

    - intros.
      intros ? ? ?.
      eapply closed_on_free_vars.
      rewrite closedn_subst_instance.
      eapply declared_constant_closed_type ; tea.

    - intros.
      intros ? ? ?.
      eapply closed_on_free_vars.
      rewrite closedn_subst_instance.
      eapply declared_inductive_closed_type ; tea.

    - intros.
      intros ? ? ?.
      eapply closed_on_free_vars.
      eapply declared_constructor_closed_type ; tea.

    - intros.
      move => ? ? /= /and5P [] ? ? Hctx ? ?.
      rewrite on_free_vars_mkApps.
      apply /andP ; split.
      + rewrite on_free_vars_it_mkLambda_or_LetIn.
        rewrite test_context_k_closed_on_free_vars_ctx -closedn_ctx_on_free_vars in Hctx.
        apply /andP ; split.
        2: by rewrite case_predicate_context_length.
        eapply on_free_vars_case_predicate_context ; eassumption.
        
      + rewrite forallb_app.
        apply /andP ; split.
        2: by rewrite /= andb_true_r.
        apply All_forallb, All_skipn.
        auto.
    
    - intros until args.
      move => ? _ ? largs ? ? ? ?.
      apply on_free_vars_subst.
      + cbn ; apply /andP ; split ; auto.
        rewrite forallb_rev.
        apply All_forallb.
        auto.
      + eapply closedn_on_free_vars.
        rewrite closedn_subst_instance /= List.rev_length largs.
        eapply declared_projection_closed_type ; tea. 

    - intros until decl.
      move => ? ndec ? ? ? ? ? /= Hmfix.
      eapply forallb_nth_error in Hmfix.
      erewrite ndec in Hmfix.
      cbn in Hmfix.
      by move: Hmfix => /andP [].

    - intros until decl.
      move => ? ndec ? ? ? ? ? /= Hmfix.
      eapply forallb_nth_error in Hmfix.
      erewrite ndec in Hmfix.
      cbn in Hmfix.
      by move: Hmfix => /andP [].
    
    - easy.

    - intros ? ? ? ? ? ? _ HT Hred.
      intros ? HΓ Ht.
      specialize (HT _ HΓ Ht).
      eapply red_on_free_vars in Hred ; tea.
      by move: Hred => /= /andP [].
    - intros ? ? ? ? ? ? _ HT Hred.

      intros ? HΓ Ht.
      specialize (HT _ HΓ Ht).
      eapply red_on_free_vars in Hred ; tea.
      rewrite on_free_vars_mkApps in Hred.
      by move: Hred => /= /forallb_All.

    - easy.

  Qed.

  Lemma infering_on_free_vars P Γ t T :
    on_ctx_free_vars P Γ ->
    on_free_vars P t ->
    Σ ;;; Γ |- t ▹ T ->
    on_free_vars P T.
  Proof.
    intros.
    edestruct bidirectional_on_free_vars as (_&_&_&p&_).
    eapply p ; eauto.
  Qed.

  Lemma infering_prod_on_free_vars P Γ t na A B :
    on_ctx_free_vars P Γ ->
    on_free_vars P t ->
    Σ ;;; Γ |- t ▹Π (na,A,B) ->
    on_free_vars P A × on_free_vars (shiftnP 1 P) B.
  Proof.
    intros.
    eapply bidirectional_on_free_vars ; eauto.
  Qed.

End OnFreeVars.

Lemma on_free_vars_type `{checker_flags} P Σ (wfΣ : wf Σ.1) Γ t T :
  on_ctx_free_vars P Γ ->
  on_free_vars P t ->
  Σ ;;; Γ |- t : T ->
  ∑ T', on_free_vars P T' × Σ ;;; Γ |- t : T'.
Proof.
  intros oΓ ot ty.
  assert (wf_local Σ Γ) by (eapply typing_wf_local ; tea). 
  apply typing_infering in ty as [T' []] ; tea.
  exists T' ; split.
  - edestruct bidirectional_on_free_vars as (_&_&_&?&_).
    all: eauto.
  - by apply infering_typing.
Qed.

Axiom fix_guard_rename : forall P Σ Γ Δ mfix f,
  urenaming P Γ Δ f ->
  let mfix' := map (map_def (rename f) (rename (shiftn (List.length mfix) f))) mfix in
  fix_guard Σ Δ mfix ->
  fix_guard Σ Γ mfix'.

Axiom cofix_guard_rename : forall P Σ Γ Δ mfix f,
  urenaming P Γ Δ f ->
  let mfix' := map (map_def (rename f) (rename (shiftn (List.length mfix) f))) mfix in
  cofix_guard Σ Δ mfix ->
  cofix_guard Σ Γ mfix'.

Section BDRenaming.

Context `{cf : checker_flags}.
Context (Σ : global_env_ext).
Context (wfΣ : wf Σ).

Let Pinfer Γ t T :=
  forall P Δ f,
  urenaming P Δ Γ f ->
  on_ctx_free_vars P Γ ->
  on_free_vars P t ->
  Σ ;;; Δ |- rename f t ▹ rename f T.

Let Psort Γ t u :=
  forall P Δ f,
  urenaming P Δ Γ f ->
  on_ctx_free_vars P Γ ->
  on_free_vars P t ->
  Σ ;;; Δ |- rename f t ▹□ u.

Let Pprod Γ t na A B :=
  forall P Δ f,
  urenaming P Δ Γ f ->
  on_ctx_free_vars P Γ ->
  on_free_vars P t ->
  Σ ;;; Δ |- rename f t ▹Π (na,rename f A,rename (shiftn 1 f) B).

Let Pind Γ ind t u args :=
  forall P Δ f,
  urenaming P Δ Γ f ->
  on_ctx_free_vars P Γ ->
  on_free_vars P t ->
  Σ ;;; Δ |- rename f t ▹{ind} (u, map (rename f) args).
  

Let Pcheck Γ t T :=
  forall P Δ f,
  urenaming P Δ Γ f ->
  on_ctx_free_vars P Γ ->
  on_free_vars P t ->
  on_free_vars P T ->
  Σ ;;; Δ |- rename f t ◃ rename f T.

Let PΓ :=
  All_local_env (lift_sorting (fun _ => Pcheck) (fun _ => Psort) Σ).

Let PΓ_rel Γ Γ' :=
  forall P Δ f,
  urenaming P Δ Γ f ->
  on_ctx_free_vars P Γ ->
  on_free_vars_ctx P Γ' ->
  wf_local_bd_rel Σ Δ (rename_context f Γ').

Theorem bidirectional_renaming : env_prop_bd Σ Pcheck Pinfer Psort Pprod Pind PΓ PΓ_rel.
Proof.
  apply bidir_ind_env.

  - intros Γ wfΓ hΓ. red.
    induction hΓ.
    + constructor.
    + constructor ; tea.
      eexists ; eauto.
    + constructor ; tea.
      eexists ; eauto.

  - intros Γ Γ' wfΓ' allΓ'. red. move => P Δ f hf hΓ hΓ'.
    induction allΓ'.
    + constructor.
    + rewrite rename_context_snoc.
      rewrite on_free_vars_ctx_snoc in hΓ'.
      move: hΓ' => /andP [] ? ?.
      constructor ; eauto.
      1: by eapply IHallΓ' ; eauto.
      eexists.
      eapply s.
      * eapply urenaming_context ; tea.
      * rewrite on_ctx_free_vars_concat.
        apply /andP ; split ; tea.
        by rewrite on_free_vars_ctx_on_ctx_free_vars.
      * eassumption.
    + rewrite rename_context_snoc.
      rewrite on_free_vars_ctx_snoc in hΓ'.
      move: hΓ' => /andP [] ? /andP /= [] ? ?.
      constructor ; eauto.
      * by eapply IHallΓ' ; eauto.
      * eexists.
        eapply s.
        1: eapply urenaming_context ; tea.
        2: eauto.
        rewrite on_ctx_free_vars_concat.
        apply /andP ; split ; tea.
        by rewrite on_free_vars_ctx_on_ctx_free_vars.
      * eapply c.
        1: eapply urenaming_context ; tea.
        all: auto.
        rewrite on_ctx_free_vars_concat.
        apply /andP ; split ; tea.
        by rewrite on_free_vars_ctx_on_ctx_free_vars.
  
  - intros Γ n decl isdecl P Δ f hf hΓ ht.
    eapply hf in isdecl as h => //.
    destruct h as [decl' [isdecl' [? [h1 h2]]]].
    rewrite lift0_rename rename_compose h1 -lift0_rename.
    econstructor. all: auto.

  - intros. red. intros. cbn in *.
    by constructor.
    
  - intros. red. move => P Δ f hf hΓ /= /andP [] ? ?.
    econstructor ; eauto.
    eapply X2 ; tea.
    1: by apply urenaming_vass.
    rewrite on_ctx_free_vars_snoc /=.
    apply /andP ; split ; tea.
    
  - intros. red. move => P Δ f hf hΓ /= /andP [] ? ?.
    econstructor ; eauto.
    eapply X2 ; tea.
    1: by apply urenaming_vass.
    rewrite on_ctx_free_vars_snoc /=.
    apply /andP ; split ; tea.

  - intros. red. move => P Δ f hf hΓ /= /andP [] ? /andP [] ? ?.
    econstructor ; eauto.
    eapply X4 ; tea.
    1: by apply urenaming_vdef.
    rewrite on_ctx_free_vars_snoc.
    repeat (apply /andP ; split ; tea).

  - intros. red. move => P Δ f hf hΓ /= /andP [] ? ?.
    rewrite rename_subst0 ; cbn.
    econstructor ; eauto.
    eapply X2 ; tea.
    eapply infering_prod_on_free_vars.
    4: eassumption.
    all: assumption.

  - intros. red. move => P Δ f hf hΓ /= _.
    rewrite rename_subst_instance.
    erewrite rename_closed.
    2: by eapply declared_constant_closed_type ; tea.
    econstructor ; tea.

  - intros. red. move => P Δ f hf hΓ /= _.
    rewrite rename_subst_instance.
    erewrite rename_closed.
    2: by eapply declared_inductive_closed_type ; tea.
    econstructor ; tea.
  
  - intros. red. move => P Δ f hf hΓ /= _.
    erewrite rename_closed.
    2: by eapply declared_constructor_closed_type ; tea.
    econstructor ; tea.

  - intros. red. move => P Δ f hf hΓ /= /andP [] on_pars /andP [] ? /andP [] ? /andP [] ? /forallb_All on_brs.
    rewrite rename_mkApps rename_it_mkLambda_or_LetIn map_app map_skipn /=.
    rewrite rename_case_predicate_context // case_predicate_context_length // rename_predicate_preturn.
    econstructor ; eauto.
    + by eapply rename_wf_predicate.
    + rewrite -rename_case_predicate_context ; tea.
      eapply X1 ; tea.
      eapply on_free_vars_case_predicate_context ; tea.
    + eapply X3 ; tea.
      * rewrite -rename_case_predicate_context //.
        erewrite <- case_predicate_context_length ; tea.
        apply urenaming_context ; assumption.
      * erewrite <- case_predicate_context_length ; tea.
        rewrite /predctx.
        erewrite on_ctx_free_vars_concat.
        apply /andP ; split ; tea.
        rewrite on_free_vars_ctx_on_ctx_free_vars.
        eapply on_free_vars_case_predicate_context ; tea.
    + revert X7.
      rewrite -{2}[subst_instance _ _](rename_closedn_ctx f 0).
      { pose proof (declared_inductive_closed_params isdecl).
        now rewrite closedn_subst_instance_context. }
      rewrite rename_context_telescope rename_telescope_shiftn0 /=.
      assert (on_free_vars_ctx P (subst_instance (puinst p) (ind_params mdecl))).
      { admit. }
      clear -on_pars.
      (* induction 1.
      * constructor.
      * constructor.   *)
      admit.
    + rewrite /= /id -map_skipn -map_app.
      eapply cumul_renameP in X8 ; tea.
      * by rewrite !rename_mkApps /= in X8.
      * rewrite on_free_vars_mkApps /=.
        eapply All_forallb, bidirectional_on_free_vars ; tea.
      * rewrite on_free_vars_mkApps /=.
        rewrite forallb_app ; apply /andP ; split ; tea.
        apply forallb_skipn.
        eapply All_forallb, bidirectional_on_free_vars ; tea.
    + by apply rename_wf_branches.
    + eapply Forall2_All2 in H4.
      eapply All2i_All2_mix_left in X9; eauto.
      eapply All2i_All_mix_right in X9 ; eauto.
      eapply All2i_nth_hyp in X9.
      eapply All2i_map_right, (All2i_impl X9) => i cdecl br.
      set (brctxty := case_branch_type _ _ _ _ _ _ _ _).
      move=> [Hnth [ [wfbr [eqbctx [wfbctx [IHbctx [Hbod IHbod]]]]] /andP [on_ctx on_bod] ]].
      rewrite -(rename_closed_constructor_body mdecl cdecl f).
      { eapply (declared_constructor_closed (c:=(ci.(ci_ind),i))); eauto.
        split; eauto. }
      split; auto.
      { simpl. rewrite -rename_cstr_branch_context //.
        1:eapply (declared_inductive_closed_params isdecl).
        rewrite rename_closedn_ctx //.
        eapply closed_cstr_branch_context.
        1:by eapply declared_minductive_closed ; eauto.
        eapply (declared_constructor_closed (c:=(ci.(ci_ind),i))). split; tea.
      }
      cbn -[case_branch_type case_predicate_context].
      rewrite case_branch_type_fst.
      rewrite -rename_case_branch_context_gen //.
      2-3:len.
      1:exact (declared_inductive_closed_params isdecl).
      1:rewrite (wf_branch_length wfbr) //.
      1:rewrite (wf_predicate_length_pars H0).
      1:erewrite declared_minductive_ind_npars ; eauto.
      assert (on_free_vars_ctx P brctxty.1).
      { rewrite test_context_k_closed_on_free_vars_ctx in on_ctx.        
        admit. }
      set (brctx' := rename_context f _).
      split.
      1:by eapply IHbctx ; eauto.
      rewrite rename_case_branch_type //.
      eapply IHbod.
      * rewrite case_branch_type_fst /=.
        relativize #|bcontext br| ; [eapply urenaming_context|] ; tea.
        by rewrite case_branch_context_length.
      * rewrite case_branch_context_length ; tea.
        relativize (#|bcontext br|).
        1: erewrite on_ctx_free_vars_concat.
        2: rewrite case_branch_type_length //.
        2: erewrite wf_branch_length ; eauto.
        apply /andP ; split ; tea.
        by rewrite on_free_vars_ctx_on_ctx_free_vars.
      * rewrite case_branch_type_length //.
        erewrite <- wf_branch_length ; eauto.
      * rewrite case_branch_context_length //.
        admit.
  
  - intros. red. move => P Δ f hf hΓ /= ?.
    rewrite rename_subst0 /= rename_subst_instance map_rev List.rev_length.
    erewrite rename_closedn.
    2: rewrite H0 ; eapply declared_projection_closed_type ; tea.
    econstructor ; eauto.
    by rewrite map_length.    

  - intros. red. move => P Δ f hf hΓ /= /forallb_All ht.
    erewrite map_dtype.
    econstructor.
    + eapply fix_guard_rename ; tea.
    + by rewrite nth_error_map H0 /=.
    + eapply All_mix in X ; tea.
      eapply All_map, All_impl ; tea.
      move => ? [] /andP [] ? ? [] ? [] ? p.
      rewrite -map_dtype.
      eexists.
      eapply p ; tea.
    + eapply All_mix in X0 ; tea.
      eapply All_map, All_impl ; tea.
      move => ? [] /andP [] ? ? [] ? p.
      rewrite -map_dbody -map_dtype rename_fix_context rename_context_length -(fix_context_length mfix) -rename_shiftn.
      eapply p ; tea.
      * rewrite -(fix_context_length mfix).
        eapply urenaming_context ; tea.
      * by apply on_ctx_free_vars_fix_context.
      * rewrite -(Nat.add_0_r (#|mfix|)) fix_context_length.
        apply on_free_vars_lift_impl.
        by rewrite shiftnP0.
    + by apply rename_wf_fixpoint. 

  - intros. red. move => P Δ f hf hΓ /= /forallb_All ht.
    erewrite map_dtype.
    econstructor.
    + eapply cofix_guard_rename ; tea.
    + by rewrite nth_error_map H0 /=.
    + eapply All_mix in X ; tea.
      eapply All_map, All_impl ; tea.
      move => ? [] /andP [] ? ? [] ? [] ? p.
      rewrite -map_dtype.
      eexists.
      eapply p ; tea.
    + eapply All_mix in X0 ; tea.
      eapply All_map, All_impl ; tea.
      move => ? [] /andP [] ? ? [] ? p.
      rewrite -map_dbody -map_dtype rename_fix_context rename_context_length -(fix_context_length mfix) -rename_shiftn.
      eapply p ; tea.
      * rewrite -(fix_context_length mfix).
        eapply urenaming_context ; tea.
      * by apply on_ctx_free_vars_fix_context.
      * rewrite -(Nat.add_0_r (#|mfix|)) fix_context_length.
        apply on_free_vars_lift_impl.
        by rewrite shiftnP0.
    + by apply rename_wf_cofixpoint. 
  
  - intros. red. intros P Δ f hf ht.
    econstructor ; eauto.
    rewrite -/(rename f (tSort u)).
    eapply red_rename ; tea.
    eapply infering_on_free_vars ; tea.

  - intros. red. intros P Δ f hf hΓ ht.
    econstructor ; eauto.
    rewrite -/(rename f (tProd na A B)).
    eapply red_rename ; tea.
    eapply infering_on_free_vars ; tea.

  - intros. red. intros P Δ f hf hΓ ht.
    econstructor ; eauto.
    rewrite -/(rename f (tInd ind ui)) -rename_mkApps.
    eapply red_rename ; tea.
    eapply infering_on_free_vars ; tea.

  - intros. red. intros P Δ f hf hΓ ht.
    econstructor ; eauto.
    eapply cumul_renameP ; tea.
    eapply infering_on_free_vars.
    4: eassumption.
    all: assumption.

Admitted.

End BDRenaming.

Lemma closedn_ctx_lift_inv n k k' Γ :
  k <= k' -> closedn_ctx (k' + n) (lift_context n k Γ) ->
  closedn_ctx k' Γ.
Proof.
  intros le.
  induction Γ as [|d ?]; cbn; auto; rewrite lift_context_snoc !closedn_ctx_cons /=;
    move/andP=> [clΓ cld]; rewrite IHΓ //;
  autorewrite with len in cld.
  move: cld; rewrite /test_decl /=.
  replace (k' + n + #|Γ|) with (#|Γ| + k' + n) in * by lia.
  move/andP=> [clb clt]; apply andb_and; split.
  - destruct (decl_body d) => /= //. cbn in clb |- *.
    eapply closedn_lift_inv in clb => //.
    lia.
  - eapply closedn_lift_inv in clt => //.
    lia.
Qed.
  
Lemma strengthening `{cf: checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} Γ Γ' Γ'' t T :
  Σ ;;; Γ ,,, Γ' ,,, lift_context #|Γ'| 0 Γ'' |- lift #|Γ'| #|Γ''| t : T ->
  ∑ T', Σ ;;; Γ ,,, Γ'' |- t : T'.
Proof.
  intros Hty.
  assert (wfΓ : wf_local Σ Γ).
    {
    do 2 eapply wf_local_app_l.
    eapply typing_wf_local.
    eassumption.
    }
  generalize Hty.
  intros Hinfer ; apply typing_infering in Hinfer as [T' [? _]] ; tea.
  erewrite <- (lift_unlift_term t).
  eexists.
  eapply infering_typing ; tea.
  - eapply wf_local_app ; tea.
    eapply bidirectional_to_pcuic ; tea.
    erewrite <- (lift_unlift_context Γ'' ).
    rewrite PCUICWeakening.rename_context_lift_context.
    eapply bidirectional_renaming ; tea.
    + eapply All_local_app_rel, bidirectional_from_pcuic ; tea.
    + eapply (urenaming_strengthen _ Γ Γ' []).
    + change (Γ,,, Γ') with (Γ,,, Γ' ,,, []).
      apply on_ctx_free_vars_strengthenP => //.
      erewrite on_free_vars_ctx_on_ctx_free_vars.
      eapply closed_ctx_on_free_vars, closed_wf_local ; tea.
    + rewrite -on_free_vars_ctx_lift_context.
      eapply closedn_ctx_on_free_vars_shift.
      eapply typing_wf_local, closed_wf_local in Hty => //.
      rewrite closedn_ctx_app in Hty.
      move: Hty => /andP [] _ Hty.
      rewrite app_length /= Nat.add_comm in Hty.
      eapply closedn_ctx_lift_inv ; tea.
      lia.
  - eapply bidirectional_renaming ; tea.
    + eapply urenaming_strengthen.
    + eapply on_ctx_free_vars_strengthenP.
      * erewrite on_free_vars_ctx_on_ctx_free_vars.
        eapply closed_ctx_on_free_vars, closed_wf_local ; tea.
      * erewrite shiftnP_add, Nat.add_comm, <- shiftnP_add.
        erewrite on_free_vars_ctx_on_ctx_free_vars.
        eapply closedn_ctx_on_free_vars_shift.
        eapply (closedn_ctx_lift_inv #|Γ'| 0).
        1: lia.
        apply typing_wf_local, closed_wf_local in Hty => //.
        rewrite closedn_ctx_app /= app_context_length Nat.add_comm in Hty.
        move: Hty => /andP [] //.
    + erewrite shiftnP_add, on_free_vars_lift.
      apply closedn_on_free_vars.
      eapply (closedn_lift_inv #|Γ'| #|Γ''|).
      1: lia.
      apply subject_closed in Hty.
      rewrite !app_context_length lift_context_length in Hty.
      by rewrite Nat.add_comm Nat.add_assoc Nat.add_comm.
  
  Unshelve.
  all: exact xpredT.
Qed.