(* Distributed under the terms of the MIT license.   *)
Set Warnings "-notation-overridden".

Require Import Equations.Prop.DepElim.
From Coq Require Import Bool List Program Lia Arith.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICWeakeningEnv PCUICWeakening
     PCUICSubstitution PCUICClosed PCUICCumulativity PCUICGeneration PCUICReduction
     PCUICAlpha PCUICEquality
     PCUICValidity PCUICConfluence
     PCUICContextConversion PCUICUnivSubstitution
     PCUICConversion PCUICInversion PCUICPrincipality PCUICContexts PCUICArities
     PCUICParallelReduction. 

Require Import ssreflect.
Set Asymmetric Patterns.
Set SimplIsCbn.

Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

Derive Signature for typing_spine.

Ltac rename_hyp h ht ::= my_rename_hyp h ht.

Lemma reln_app acc Γ Δ k : reln acc k (Γ ++ Δ) = 
  reln (reln acc k Γ) (#|Γ| + k) Δ.
Proof.
  induction Γ in acc, Δ, k |- *; simpl; auto.
  destruct a as [na [b|] ty]. rewrite IHΓ. f_equal. lia.
  simpl. rewrite IHΓ. f_equal. lia.
Qed.

Lemma reln_acc acc k Γ : reln acc k Γ = reln [] k Γ ++ acc.
Proof.
  induction Γ in acc, k |- *; simpl; auto.
  destruct a as [na [b|] ty]. rewrite IHΓ. f_equal.
  rewrite IHΓ. rewrite [reln [_] _ _]IHΓ. 
  now rewrite -app_assoc.
Qed.

Lemma to_extended_list_k_app Γ Δ k : to_extended_list_k (Γ ++ Δ) k = 
  to_extended_list_k Δ (#|Γ| + k) ++ to_extended_list_k Γ k.
Proof.
  unfold to_extended_list_k. now rewrite reln_app reln_acc.
Qed.

(* Commented otherwise extraction would produce an axiom making the whole
   extracted code unusable *)

Arguments Universe.sort_of_product : simpl nomatch.

Lemma mkApps_inj f a f' l :
  tApp f a = mkApps f' l -> l <> [] ->
  f = mkApps f' (removelast l) /\ (a = last l a).
Proof.
  induction l in f' |- *; simpl; intros H. noconf H. intros Hf. congruence.
  intros . destruct l; simpl in *. now noconf H.
  specialize (IHl _ H). forward IHl by congruence.
  apply IHl.
Qed.

Lemma isWAT_tProd {cf:checker_flags} {Σ : global_env_ext} (HΣ' : wf Σ)
      {Γ} (HΓ : wf_local Σ Γ) {na A B}
  : isWfArity_or_Type Σ Γ (tProd na A B)
    <~> (isType Σ Γ A × isWfArity_or_Type Σ (Γ,, vass na A) B).
Proof.
  split; intro HH.
  - destruct HH as [[ctx [s [H1 H2]]]|[s H]].
    + cbn in H1. apply destArity_app_Some in H1.
      destruct H1 as [ctx' [H1 HH]]; subst ctx.
      rewrite app_context_assoc in H2. split.
      * apply wf_local_app in H2. inversion H2; subst. assumption.
      * left. exists ctx', s. split; tas.
    + apply inversion_Prod in H; tas. destruct H as [s1 [s2 [HA [HB Hs]]]].
      split.
      * eexists; tea.
      * right. eexists; tea.
  - destruct HH as [HA [[ctx [s [H1 H2]]]|HB]].
    + left. exists ([vass na A] ,,, ctx), s. split.
      * cbn. now rewrite destArity_app H1.
      * now rewrite app_context_assoc.
    + right. destruct HA as [sA HA], HB as [sB HB].
      eexists. econstructor; eassumption.
Defined.

Lemma type_tFix_inv {cf:checker_flags} (Σ : global_env_ext) Γ mfix idx T : wf Σ ->
  Σ ;;; Γ |- tFix mfix idx : T ->
  { T' & { rarg & {f & (unfold_fix mfix idx = Some (rarg, f)) * (Σ ;;; Γ |- f : T') * (Σ ;;; Γ |- T' <= T) }}}%type.
Proof.
  intros wfΣ H. depind H.
  - unfold unfold_fix. rewrite e.
    specialize (nth_error_all e a0) as [s Hs].
    specialize (nth_error_all e a1) as [Hty ->].
    simpl.
    destruct decl as [name ty body rarg]; simpl in *.
    clear e.
    eexists _, _, _. split.
    + split.
      * eauto.
      * eapply (substitution _ _ _ _ [] _ _ wfΣ); simpl; eauto with wf.
        rename i into hguard. clear -a a0 a1 hguard.
        pose proof a1 as a1'. apply All_rev in a1'.
        unfold fix_subst, fix_context. simpl.
        revert a1'. rewrite <- (@List.rev_length _ mfix).
        rewrite rev_mapi. unfold mapi.
        assert (#|mfix| >= #|List.rev mfix|) by (rewrite List.rev_length; lia).
        assert (He :0 = #|mfix| - #|List.rev mfix|) by (rewrite List.rev_length; auto with arith).
        rewrite {3}He. clear He. revert H.
        assert (forall i, i < #|List.rev mfix| -> nth_error (List.rev mfix) i = nth_error mfix (#|List.rev mfix| - S i)).
        { intros. rewrite nth_error_rev. 1: auto.
          now rewrite List.rev_length List.rev_involutive. }
        revert H.
        generalize (List.rev mfix).
        intros l Hi Hlen H.
        induction H.
        ++ simpl. constructor.
        ++ simpl. constructor.
          ** unfold mapi in IHAll.
              simpl in Hlen. replace (S (#|mfix| - S #|l|)) with (#|mfix| - #|l|) by lia.
              apply IHAll.
              --- intros. simpl in Hi. specialize (Hi (S i)). apply Hi. lia.
              --- lia.
          ** clear IHAll. destruct p.
              simpl in Hlen. assert ((Nat.pred #|mfix| - (#|mfix| - S #|l|)) = #|l|) by lia.
              rewrite H0. rewrite simpl_subst_k.
              --- clear. induction l; simpl; auto with arith.
              --- eapply type_Fix; auto.
                  simpl in Hi. specialize (Hi 0). forward Hi.
                  +++ lia.
                  +++ simpl in Hi.
                      rewrite Hi. f_equal. lia.

    + rewrite simpl_subst_k.
      * now rewrite fix_context_length fix_subst_length.
      * reflexivity.
  - destruct (IHtyping wfΣ) as [T' [rarg [f [[unf fty] Hcumul]]]].
    exists T', rarg, f. intuition auto.
    + eapply cumul_trans; eauto.
    + destruct b. eapply cumul_trans; eauto.
Qed.

Lemma type_tCoFix_inv {cf:checker_flags} (Σ : global_env_ext) Γ mfix idx T : wf Σ ->
  Σ ;;; Γ |- tCoFix mfix idx : T ->
  (allow_cofix = true) * { T' & { rarg & {f & (unfold_cofix mfix idx = Some (rarg, f)) *
   (Σ ;;; Γ |- f : T') * (Σ ;;; Γ |- T' <= T) }}}%type.
Proof.
  intros wfΣ H. depind H.
  - unfold unfold_cofix. rewrite e. split; auto.
    specialize (nth_error_all e a1) as Hty.
    destruct decl as [name ty body rarg]; simpl in *.
    clear e.
    eexists _, _, _. split.
    + split.
      * eauto.
      * eapply (substitution _ _ _ _ [] _ _ wfΣ); simpl; eauto with wf.
        rename i into hguard. clear -a a0 a1 hguard.
        pose proof a1 as a1'. apply All_rev in a1'.
        unfold cofix_subst, fix_context. simpl.
        revert a1'. rewrite <- (@List.rev_length _ mfix).
        rewrite rev_mapi. unfold mapi.
        assert (#|mfix| >= #|List.rev mfix|) by (rewrite List.rev_length; lia).
        assert (He :0 = #|mfix| - #|List.rev mfix|) by (rewrite List.rev_length; auto with arith).
        rewrite {3}He. clear He. revert H.
        assert (forall i, i < #|List.rev mfix| -> nth_error (List.rev mfix) i = nth_error mfix (#|List.rev mfix| - S i)).
        { intros. rewrite nth_error_rev. 1: auto.
          now rewrite List.rev_length List.rev_involutive. }
        revert H.
        generalize (List.rev mfix).
        intros l Hi Hlen H.
        induction H.
        ++ simpl. constructor.
        ++ simpl. constructor.
          ** unfold mapi in IHAll.
              simpl in Hlen. replace (S (#|mfix| - S #|l|)) with (#|mfix| - #|l|) by lia.
              apply IHAll.
              --- intros. simpl in Hi. specialize (Hi (S i)). apply Hi. lia.
              --- lia.
          ** clear IHAll.
              simpl in Hlen. assert ((Nat.pred #|mfix| - (#|mfix| - S #|l|)) = #|l|) by lia.
              rewrite H0. rewrite simpl_subst_k.
              --- clear. induction l; simpl; auto with arith.
              --- eapply type_CoFix; auto.
                  simpl in Hi. specialize (Hi 0). forward Hi.
                  +++ lia.
                  +++ simpl in Hi.
                      rewrite Hi. f_equal. lia.
    + rewrite simpl_subst_k.
      * now rewrite fix_context_length cofix_subst_length.
      * reflexivity.
  - destruct (IHtyping wfΣ) as [IH [T' [rarg [f [[unf fty] Hcumul]]]]].
    split; auto.
    exists T', rarg, f. intuition auto.
    + eapply cumul_trans; eauto.
    + destruct b. eapply cumul_trans; eauto.
Qed.

Arguments subst_context !s _ !Γ.
Arguments it_mkProd_or_LetIn !l _.

Lemma build_case_predicate_type_spec {cf:checker_flags} Σ ind mdecl idecl pars u ps pty :
  forall (o : on_ind_body (lift_typing typing) Σ (inductive_mind ind) mdecl (inductive_ind ind) idecl),
  build_case_predicate_type ind mdecl idecl pars u ps = Some pty ->
  ∑ parsubst, (context_subst (subst_instance_context u (ind_params mdecl)) pars parsubst *
  (pty = it_mkProd_or_LetIn (subst_context parsubst 0 (subst_instance_context u o.(ind_indices))) 
      (tProd (nNamed (ind_name idecl))
          (mkApps (tInd ind u) (map (lift0 #|o.(ind_indices)|) pars ++ to_extended_list o.(ind_indices))) 
          (tSort ps)))).
Proof.
  intros []. unfold build_case_predicate_type.
  destruct instantiate_params eqn:Heq=> //.
  eapply instantiate_params_make_context_subst in Heq =>  /=.
  destruct destArity eqn:Har => //.
  move=> [=] <-. destruct Heq as [ctx'  [ty'' [s' [? [? ?]]]]].
  subst t. exists s'. split. apply make_context_subst_spec in H0.
  now rewrite List.rev_involutive in H0.
  clear onProjections. clear onConstructors.
  assert (p.1 = subst_context s' 0 (subst_instance_context u ind_indices)) as ->.
  move: H. rewrite ind_arity_eq subst_instance_constr_it_mkProd_or_LetIn.
  rewrite decompose_prod_n_assum_it_mkProd app_nil_r => [=].
  move=> Hctx' Hty'.
  subst ty''  ctx'.
  move: Har. rewrite subst_instance_constr_it_mkProd_or_LetIn subst_it_mkProd_or_LetIn.
  rewrite destArity_it_mkProd_or_LetIn. simpl. move=> [=] <- /=. 
  now rewrite app_context_nil_l.
  f_equal. rewrite subst_context_length subst_instance_context_length.
  simpl.
  f_equal. f_equal.  f_equal.
  unfold to_extended_list.
  rewrite to_extended_list_k_subst PCUICSubstitution.map_subst_instance_constr_to_extended_list_k.
  reflexivity.
Qed.

(*
  Lemma type_Case_valid_btys {cf:checker_flags} Σ Γ ind u npar p c args :
    forall mdecl idecl (isdecl : declared_inductive Σ.1 mdecl ind idecl),
    wf Σ.1 ->
    mdecl.(ind_npars) = npar ->
    let params := List.firstn npar args in
    forall ps pty, build_case_predicate_type ind mdecl idecl params u ps =
                Some pty ->                
    Σ ;;; Γ |- p : pty ->
    existsb (leb_sort_family (universe_family ps)) (ind_kelim idecl) ->
    Σ ;;; Γ |- c : mkApps (tInd ind u) args ->
    forall btys, map_option_out (build_branches_type ind mdecl idecl params u p) =
                Some btys ->
    All (fun br => Σ ;;; Γ |- br.2 : tSort ps) btys.
Proof.
  intros mdecl idecl isdecl wfΣ H0 pars ps pty X typ Hps tyc btys brtys.
  unfold build_case_predicate_type in X.
  destruct instantiate_params eqn:Heq; [|simpl; discriminate].
  simpl monad_utils.bind in X.
  pose proof isdecl as isdecl'.
  apply PCUICWeakeningEnv.on_declared_inductive in isdecl' as [oind oc]; auto.
  rewrite oc.(ind_arity_eq) in Heq.
  pose proof (PCUICClosed.destArity_spec [] t) as Hpty.
  move: X Hpty. destruct destArity eqn:da => // [=] Hpty. subst pty.


  unfold build_branches_type in H2.
  eapply map_option_out_All; tea. clear H2.
  apply All_mapi.
  pose proof oc.(onConstructors) as oc'.
  eapply Alli_impl. eapply All2_All_left_pack. tea. cbn.
  intros n [[id ct] k] [cs [Hnth [Hct1 Hct2]]]; cbn in *.
  case_eq (instantiate_params (subst_instance_context u (ind_params mdecl)) pars
             ((subst0 (inds (inductive_mind ind) u (ind_bodies mdecl)))
                (subst_instance_constr u ct))); [|simpl; trivial].
  intros ct' Hct'. 
  case_eq (decompose_prod_assum [] ct'); intros sign ccl e1.
  case_eq (chop (ind_npars mdecl) (decompose_app ccl).2);
  intros paramrels args0 e2; cbn.
  destruct Hct2 as [cs' Hcs'].
  destruct cs'. simpl in *. subst ct.
  eapply instantiate_params_make_context_subst in Hct'.
  destruct Hct' as [ctx' [ty'' [parinst Hct']]].
  rewrite !subst_instance_constr_it_mkProd_or_LetIn in Hct'.
  rewrite !subst_it_mkProd_or_LetIn in Hct'.
  rewrite -(subst_context_length  (inds (inductive_mind ind) u
     (ind_bodies mdecl)) 0) in Hct'.
  rewrite decompose_prod_n_assum_it_mkProd app_nil_r in Hct'.
  destruct Hct' as [[= eqs eqs'] [eqpars ->]].
  subst ctx' ty''.
  rewrite !subst_it_mkProd_or_LetIn in e1.
  eapply inversion_Ind_app in cty as [inds [Hsp [argapp [indannot Hu]]]]; eauto.
  rewrite decompose_prod_assum_it_mkProd in e1.
  rewrite !subst_context_length !subst_instance_context_length !Nat.add_0_r.
  rewrite subst_cstr_concl_head.
   intuition auto. 
  rewrite subst_mkApps. simpl. apply is_ind_app_head_mkApps.
  noconf e1. simpl in e2. 
  rewrite !subst_context_length app_nil_r !subst_instance_context_length.
  rewrite !subst_context_length.
  rewrite Nat.add_0_r !subst_context_length !subst_instance_context_length in e2.
  rewrite subst_instance_constr_mkApps !subst_mkApps /cshape_concl_head in e2.
  rewrite decompose_app_mkApps in e2.
  rewrite !Nat.add_0_r.
  rewrite subst_inds_concl_head. auto. simpl. trivial.
  simpl in e2. 
  rewrite !map_map_compose in e2.
  apply make_context_subst_spec in eqpars.
  rewrite List.rev_involutive in eqpars.
  assert(type_local_ctx (lift_typing typing) Σ Γ
  (subst_context parinst 0
     (subst_context
        (PCUICTyping.inds (inductive_mind ind) u (ind_bodies mdecl))
        (#|ind_params mdecl| + 0) (subst_instance_context u cshape_args)))
  (subst_instance_univ u cs)).
  { eapply typing_wf_local in X.
    destruct oc.
    clear -X Hu eqpars isdecl wfΣ Hcs' ind_sorts.
    eapply type_local_ctx_instantiate in Hcs'; eauto.
    2:{ eapply isdecl. }
    rewrite PCUICUnivSubstitution.subst_instance_context_app in Hcs'.
    eapply weaken_type_local_ctx in Hcs'. 3:eapply X. all:auto.
    eapply subst_type_local_ctx in Hcs'. all:auto.
    revert Hcs'. instantiate (1:= (parinst ++ (inds (inductive_mind ind) u (ind_bodies mdecl)))%list).
    rewrite subst_app_context.
    rewrite Nat.add_0_r. assert (#|parinst| = #|ind_params mdecl|).
    eapply context_subst_length in eqpars. now rewrite subst_instance_context_length in eqpars.
    now rewrite H.
    clear -wfΣ X isdecl Hu.
    pose proof isdecl as [declm _].
    eapply on_declared_inductive in isdecl as [onm oni]; auto.
    destruct onm.
    eapply (weaken_wf_local Γ); auto.
    pose proof (wf_arities_context _ _ _ wfΣ declm).
    eapply weaken_wf_local; auto.
    eapply wf_local_instantiate; eauto.
    red in onParams.
    eapply wf_local_instantiate; eauto.
    eapply subslet_app. admit.
    eapply (weaken_subslet ), subslet_inds; eauto.
    eapply on_declared_inductive in isdecl as [onm oni]; auto.
    destruct onm. red in onParams.
    eapply closed_wf_local in onParams; auto.
    now rewrite closedn_subst_instance_context. }
  eapply type_Cumul with (tSort (Universe.sort_of_product (subst_instance_univ u cs) ps)).
  eapply type_it_mkProd_or_LetIn; eauto.
  2:{ left. exists [], ps; intuition eauto using typing_wf_local. }
  2:{ repeat constructor. apply eq_universe_leq_universe. admit. }
      (* apply sort_of_product_idem. } *)
  red in oc'.
  rewrite !subst_instance_context_length Nat.add_0_r.
  rewrite map_app in e2.
  rewrite chop_n_app in e2.
  { rewrite !map_length to_extended_list_k_length.
    destruct oind. auto. }
  noconf e2.
  rewrite Nat.add_0_r in X0.
  pose proof (typing_wf_local X).
  eapply type_mkApps. all:eauto.
  red in car.
  assert(Σ ;;; Γ |- p : it_mkProd_or_LetIn ({|
  decl_name := nNamed (ind_name idecl);
  decl_body := None;
  decl_type := mkApps (tInd ind u)
                 (map (lift0 #|indctx|) pars ++ to_extended_list indctx) |}
  :: indctx) (tSort ps)).
  { eapply type_Cumul. eauto. left; eexists _, _; intuition eauto.
    rewrite destArity_it_mkProd_or_LetIn. reflexivity.
    rewrite app_context_nil_l /=. constructor.
  }

  eapply weakening_gen; eauto.
  - now rewrite !subst_context_length !subst_instance_context_length.
  - eapply typing_wf_local in X.
    subst pars.
    eapply type_local_ctx_wf_local in X0; auto.
  - red in car.
    depelim car. depelim e.
    destruct y as [na [b|] ty]; simpl in *. intuition auto.
    destruct e as [_ e]. rewrite /mkProd_or_LetIn /=.
    rewrite lift_it_mkProd_or_LetIn /= Nat.add_0_r.
    eapply typing_spine_it_mkProd_or_LetIn; eauto.
    
                  
    admit.
  

    induction l'. simpl. depelim car. simpl in *.
    destruct cshape_indices. simpl.
    * econstructor. 2:eauto.
      left. eexists _, _; intuition eauto.
      simpl. constructor.
      eapply type_local_ctx_wf_local in X0. apply X0. eauto using typing_wf_local.
      simpl in X. rewrite /mkProd_or_LetIn in X. simpl in X.
      rewrite app_nil_r in e0.
      eapply validity in X as [_ X]; auto.
      eapply isWAT_tProd in X as [dom _]; auto.
      destruct dom as [s'' Hs']. exists s''.
      eapply (weakening_gen _ _ _ _ _ _ #|cshape_args|) in Hs'. simpl in Hs'.
      eapply Hs'. now rewrite !subst_context_length subst_instance_context_length. all:auto.
      now eapply type_local_ctx_wf_local in X0.
      eapply type_mkApps. econstructor; eauto.
      now eapply type_local_ctx_wf_local in X0.
      split. eauto. intuition eauto.
      unfold type_of_constructor. simpl.
      rewrite app_nil_r !subst_instance_constr_it_mkProd_or_LetIn.
      rewrite /subst1 !subst_it_mkProd_or_LetIn !subst_instance_context_length Nat.add_0_r.
      eapply typing_spine_it_mkProd_or_LetIn; eauto.
      pose proof (context_subst_length _ _ _ eqpars).
      rewrite subst_instance_context_length in H. rewrite H.
      rewrite -map_map_compose.
      rewrite subst_instance_to_extended_list_k.
      rewrite -map_map_compose.
      rewrite -to_extended_list_k_map_subst. rewrite subst_instance_context_length; lia.
      rewrite (subst_to_extended_list_k _ _ pars). 
      apply make_context_subst_spec_inv. now rewrite List.rev_involutive.
      eapply make_context_subst_spec_inv.
      instantiate (1 := map (lift0 #|cshape_args|) parinst).
      rewrite List.rev_involutive.
      assert(closed_ctx (subst_instance_context u (ind_params mdecl)) = true).
      { eapply closed_wf_local; eauto.
        eapply (on_minductive_wf_params _ mdecl); intuition eauto.
        eapply isdecl. }
      rewrite closed_ctx_subst //.
      eapply (context_subst_lift _ _ _ #|cshape_args|) in eqpars => //.
      rewrite closed_ctx_lift // in eqpars.
      rewrite subst_it_mkProd_or_LetIn !subst_context_length !subst_instance_context_length !Nat.add_0_r /=.
      eapply typing_spine_weaken_concl. auto.
      eapply typing_spine_it_mkProd_or_LetIn_close; eauto.
      2:{ rewrite to_extended_list_k_length.
          now rewrite !context_assumptions_subst. }
      apply make_context_subst_spec_inv.
      rewrite /to_extended_list !to_extended_list_k_subst.
      rewrite -subst_instance_to_extended_list_k.
      rewrite List.rev_involutive.
      eapply make_context_subst_spec. shelve. shelve.
      assert (#|ind_params mdecl| = #|parinst|).
      { eapply context_subst_length in eqpars. 
        now rewrite subst_instance_context_length in eqpars. }
      rewrite subst_instance_constr_mkApps.
      rewrite !subst_mkApps.
      rewrite subst_cstr_concl_head.
      rewrite -subst_app_simpl'. now rewrite map_length.

      eapply isWAT_it_mkProd_or_LetIn_app.
      instantiate (1:=mapi (fun i x => tRel i) cshape_args).
      rewrite PCUICUnivSubst.map_subst_instance_constr_to_extended_list_k.

      pose (unfold_nat cshape_args).
      rewrite (subst_to_extended_list_k _ _ pars). 
      rewrite -to_extended_list_k_map_subst. rewrite subst_instance_context_length; lia.

      rewrite -map_map_compose.
      rewrite -to_extended_list_k_map_subst. lia. 
      shelve.
      
      rewrite -map_map_compose.

      admit. admit.
      now rewrite map_length context_assumptions_subst subst_instance_context_assumptions
        to_extended_list_k_length.
      rewrite /subst1 /=. constructor.
      left; exists [], ps; intuition auto.
      now apply type_local_ctx_wf_local in X0.
      reflexivity.

Admitted.
*)

Hint Resolve conv_ctx_refl : pcuic.

Definition branch_type ind mdecl (idecl : one_inductive_body) params u p i (br : ident * term * nat) :=
  let inds := inds ind.(inductive_mind) u mdecl.(ind_bodies) in
  let '(id, t, ar) := br in
  let ty := subst0 inds (subst_instance_constr u t) in
  match instantiate_params (subst_instance_context u mdecl.(ind_params)) params ty with
  | Some ty =>
  let '(sign, ccl) := decompose_prod_assum [] ty in
  let nargs := List.length sign in
  let allargs := snd (decompose_app ccl) in
  let '(paramrels, args) := chop mdecl.(ind_npars) allargs in
  let cstr := tConstruct ind i u in
  let args := (args ++ [mkApps cstr (paramrels ++ to_extended_list sign)])%list in
  Some (ar, it_mkProd_or_LetIn sign (mkApps (lift0 nargs p) args))
| None => None
end.

Lemma nth_map_option_out {A B} (f : nat -> A -> option B) l l' i t : map_option_out (mapi f l) = Some l' ->
  nth_error l' i = Some t -> 
  (∑ x, (nth_error l i = Some x) * (f i x = Some t)).
Proof.
  unfold mapi.
  rewrite -{3}(Nat.add_0_r i).
  generalize 0.
  induction l in i, l' |- *; intros n; simpl. intros [= <-]. rewrite nth_error_nil; discriminate.
  simpl. destruct (f n a) eqn:Heq => //.
  destruct (map_option_out (mapi_rec f l (S n))) eqn:Heq' => //.
  intros [= <-].
  destruct i; simpl. intros [= ->]. now exists a.
  specialize (IHl _ i _ Heq').
  now rewrite plus_n_Sm.
Qed.

Lemma nth_branches_type ind mdecl idecl args u p i t btys : map_option_out (build_branches_type ind mdecl idecl args u p) = Some btys ->
  nth_error btys i = Some t -> 
  (∑ br, (nth_error idecl.(ind_ctors) i = Some br) *
    (branch_type ind mdecl idecl args u p i br = Some t)).
Proof.
  intros Htys Hnth.
  eapply nth_map_option_out in Htys; eauto.
Qed.

Lemma map_option_out_length {A} (l : list (option A)) l' : map_option_out l = Some l' -> #|l| = #|l'|.
Proof.
  induction l in l' |- * => /=.
  now move=> [=] <-.
  simpl. destruct a; try discriminate.
  destruct map_option_out eqn:Heq; try discriminate.
  move=> [=] <-. by rewrite (IHl l0 eq_refl).
Qed.

Lemma build_branches_type_lookup {cf:checker_flags} Σ Γ ind mdecl idecl cdecl pars u p (brs :  list (nat * term)) btys : 
  declared_inductive Σ.1 mdecl ind idecl ->
  map_option_out (build_branches_type ind mdecl idecl pars u p) = Some btys ->
  All2 (fun br bty => (br.1 = bty.1) * (Σ ;;; Γ |- br.2 : bty.2))%type brs btys ->
  forall c, nth_error (ind_ctors idecl) c = Some cdecl ->
  ∑ nargs br bty, 
    (nth_error brs c = Some (nargs, br)) *
    (nth_error btys c = Some (nargs, bty)) *
    (Σ ;;; Γ |- br : bty) * (branch_type ind mdecl idecl pars u p c cdecl = Some (nargs, bty)).
Proof.
  intros decli Hbrs Hbrtys c Hc.
  destruct decli as [declmi decli].
  pose proof (map_option_out_length _ _ Hbrs) as hlen. 
  rewrite mapi_length in hlen.
  assert (H:∑ t', nth_error btys c = Some t').
  pose proof (All2_length _ _ Hbrtys) as e. eapply nth_error_Some_length in Hc.
  destruct (nth_error_spec btys c). eexists; eauto. elimtype False; lia.
  destruct H as [[argty bty] Hbty].
  assert (H:∑ t', nth_error brs c = Some t').
  pose proof (All2_length _ _ Hbrtys) as e. eapply nth_error_Some_length in Hc.
  destruct (nth_error_spec brs c). eexists; eauto. elimtype False; lia.
  destruct H as [[argbr br] Hbr].
  eapply All2_nth_error in Hbrtys; eauto.
  destruct Hbrtys as [Harg tybr]. simpl in *. subst.
  eapply nth_branches_type in Hbrs; eauto.
  destruct Hbrs as [[[id brty] nargs] [Hnth' Hbrty]].
  exists argty, br, bty.
  intuition auto. rewrite -Hbrty. f_equal.
  congruence.
Qed.

Arguments cshape_indices {mdecl i idecl ctype cargs}.
Import PCUICEnvironment.

From MetaCoq.PCUIC Require Import PCUICCtxShape.

Lemma branch_type_spec {cf:checker_flags} Σ ind mdecl idecl cdecl pars u p c nargs bty : 
  declared_inductive Σ mdecl ind idecl ->
  forall (omib : on_inductive (lift_typing typing) (Σ, ind_universes mdecl) (inductive_mind ind) mdecl),
  forall (oib : on_ind_body (lift_typing typing) (Σ, ind_universes mdecl) (inductive_mind ind) mdecl (inductive_ind ind) idecl),
  forall csort (cs : on_constructor (lift_typing typing) (Σ, ind_universes mdecl) mdecl (inductive_ind ind) idecl (ind_indices oib) cdecl csort),
  branch_type ind mdecl idecl pars u p c cdecl = Some (nargs, bty) ->
  forall parsubst, 
  context_subst (subst_instance_context u (PCUICAst.ind_params mdecl)) pars parsubst ->
  let cshape := cshape cs in
  let indsubst := (inds (inductive_mind ind) u (ind_bodies mdecl)) in
  let nargs' := #|cshape.(cshape_args)| in
  let npars := #|ind_params mdecl| in
  let substargs := (subst_context parsubst 0 
    (subst_context indsubst npars (map_context (subst_instance_constr u) cshape.(cshape_args)))) in
  nargs = context_assumptions cshape.(cshape_args) /\
  bty = 
  it_mkProd_or_LetIn substargs
    (mkApps (lift0 nargs' p)
      (map (subst parsubst nargs' ∘ subst indsubst (nargs' + npars) ∘ subst_instance_constr u) cshape.(cshape_indices) ++ 
       [mkApps (tConstruct ind c u)
         (map (lift0 nargs') pars ++         
          to_extended_list substargs)])).
Proof.
  move=> decli onmib [] indices ps aeq onAr indsorts onC onP inds.
  intros cs onc brty parsubst Hpars cshape' indsubst nargs' na. simpl in onc, cshape'.
  clear onP.
  assert(lenbodies: inductive_ind ind < #|ind_bodies mdecl|).
  { destruct decli as [_ Hnth]. now apply nth_error_Some_length in Hnth. }
  clear decli.
  destruct onc=> /=.
  simpl in cshape'. subst cshape'.
  destruct cshape as [args argslen head indi eqdecl] => /=. simpl in *. 
  rewrite eqdecl in on_ctype.
  unfold branch_type in brty.
  destruct cdecl as [[id ty] nargs'']. simpl in *.
  destruct instantiate_params eqn:Heq => //.
  eapply instantiate_params_make_context_subst in Heq.
  destruct Heq as [ctx' [ty'' [s' [? [? ?]]]]].
  subst t. move: H.
  rewrite eqdecl subst_instance_constr_it_mkProd_or_LetIn subst_it_mkProd_or_LetIn.
  rewrite -(subst_context_length (PCUICTyping.inds (inductive_mind ind) u (ind_bodies mdecl)) 0).
  rewrite decompose_prod_n_assum_it_mkProd.
  move=> H;noconf H.
  move: brty.
  rewrite !subst_context_length !subst_instance_context_length
    subst_instance_constr_it_mkProd_or_LetIn !subst_it_mkProd_or_LetIn.
  rewrite subst_context_length subst_instance_context_length Nat.add_0_r.
  rewrite subst_instance_constr_mkApps !subst_mkApps.
  rewrite Nat.add_0_r.
  assert((subst s' #|args|
  (subst
     (PCUICTyping.inds (inductive_mind ind) u
        (PCUICAst.ind_bodies mdecl))
     (#|args| + #|PCUICAst.ind_params mdecl|)
     (subst_instance_constr u head))) = tInd ind u).
  rewrite /head. simpl subst_instance_constr.
  erewrite (subst_rel_eq _ _ (#|ind_bodies mdecl| -  S (inductive_ind ind))); try lia.
  2:{ rewrite inds_spec nth_error_rev.
      rewrite List.rev_length mapi_length; try lia.
      rewrite List.rev_involutive List.rev_length mapi_length; try lia.
      rewrite nth_error_mapi. simpl.
      elim: (nth_error_spec _ _). simpl. reflexivity.
      lia. }
  simpl. f_equal. destruct ind as [mind k]=> /=.
  f_equal. simpl in lenbodies. lia.
  rewrite H.
  rewrite decompose_prod_assum_it_mkProd ?is_ind_app_head_mkApps //.
  rewrite decompose_app_mkApps //.
  simpl.
  rewrite !map_map_compose map_app.
  rewrite chop_n_app.
  rewrite map_length to_extended_list_k_length.
  by rewrite (onmib.(onNpars _ _ _ _)).
  move=> [=] Hargs Hbty. subst nargs. split;auto. rewrite -Hbty.
  clear Hbty bty.
  rewrite app_nil_r.
  pose proof (make_context_subst_spec _ _ _ H0) as csubst.
  rewrite rev_involutive in csubst.
  pose proof (context_subst_fun csubst Hpars). subst s'. clear csubst.
  f_equal.
  rewrite !subst_context_length subst_instance_context_length.
  f_equal. f_equal. f_equal. f_equal.
  f_equal. rewrite -map_map_compose.
  rewrite subst_instance_to_extended_list_k.
  rewrite -map_map_compose.
  rewrite -to_extended_list_k_map_subst. rewrite subst_instance_context_length; lia.
  now rewrite (subst_to_extended_list_k _ _ pars).
Qed.

Lemma isWAT_tLetIn_red {cf:checker_flags} {Σ : global_env_ext} (HΣ' : wf Σ)
      {Γ} (HΓ : wf_local Σ Γ) {na t A B}
  : isWfArity_or_Type Σ Γ (tLetIn na t A B) -> isWfArity_or_Type Σ Γ (B {0:=t}).
Proof.
  intro HH.
  destruct HH as [[ctx [s [H1 H2]]]|[s H]].
  + cbn in H1. apply destArity_app_Some in H1.
    destruct H1 as [ctx' [H1 HH]]; subst ctx.
    rewrite app_context_assoc in H2.
    left. 
    generalize (subst_destArity [] B [t] 0). rewrite H1.
    simpl. move=> H. do 2 eexists; intuition eauto.
    unfold snoc in H2.
    eapply substitution_wf_local. eauto. 2:eauto.
    eapply All_local_env_app in H2 as [wf _].
    inv wf. red in X1. 
    epose proof (cons_let_def _ _ _ [] _ _ _ (emptyslet _ _)).
    rewrite !subst_empty in X2. eapply (X2 X1).
  + right. exists s. 
    apply inversion_LetIn in H; tas. destruct H as [s1 [A' [HA [Ht [HB H]]]]].
    eapply type_Cumul with (A' {0 := t}). eapply substitution_let in HB; eauto.
    * left. apply cumul_Sort_r_inv in H.
      destruct H as [s' [H H']]. exists [], s; intuition auto.
    * eapply cumul_Sort_r_inv in H.
      destruct H as [s' [H H']].
      eapply cumul_trans with (tSort s'); eauto.
      eapply red_cumul.
      apply invert_red_letin in H as [H|H] => //.
      destruct H as [na' [d' [ty' [b' [[[reds ?] ?] ?]]]]].
      eapply invert_red_sort in reds. discriminate.
      now repeat constructor.
Qed.

Lemma isWAT_tLetIn_dom {cf:checker_flags} {Σ : global_env_ext} (HΣ' : wf Σ)
      {Γ} (HΓ : wf_local Σ Γ) {na t A B}
  : isWfArity_or_Type Σ Γ (tLetIn na t A B) -> Σ ;;; Γ |- t : A.
Proof.
  intro HH.
  destruct HH as [[ctx [s [H1 H2]]]|[s H]].
  + cbn in H1. apply destArity_app_Some in H1.
    destruct H1 as [ctx' [H1 HH]]; subst ctx.
    rewrite app_context_assoc in H2.
    eapply All_local_env_app in H2 as [wf _].
    now inv wf.
  + apply inversion_LetIn in H; tas. now destruct H as [s1 [A' [HA [Ht [HB H]]]]].
Qed.

Lemma typing_spine_it_mkProd_or_LetIn_gen {cf:checker_flags} Σ Γ Δ Δ' T args s s' args' T' : 
  wf Σ.1 ->
  make_context_subst (List.rev Δ) args s' = Some s -> 
  typing_spine Σ Γ (subst0 s T) args' T' ->
  #|args| = context_assumptions Δ ->
  subslet Σ Γ s (Δ' ,,, Δ) ->
  isWfArity_or_Type Σ Γ (it_mkProd_or_LetIn Δ' (it_mkProd_or_LetIn Δ T)) ->
  typing_spine Σ Γ (subst0 s' (it_mkProd_or_LetIn Δ T)) (args ++ args') T'.
Proof.
  intros wfΣ.
  generalize (le_n #|Δ|).
  generalize (#|Δ|) at 2.
  induction n in Δ, Δ', args, s, s', T |- *.
  - destruct Δ using rev_ind.
    + intros le Hsub Hsp.
      destruct args; simpl; try discriminate.
      simpl in Hsub. now depelim Hsub.
    + rewrite app_length /=; intros; elimtype False; lia.
  - destruct Δ using rev_ind.
    1:intros le Hsub Hsp; destruct args; simpl; try discriminate;
    simpl in Hsub; now depelim Hsub.
  clear IHΔ.
  rewrite app_length /=; intros Hlen Hsub Hsp Hargs.
  rewrite context_assumptions_app in Hargs.
  destruct x as [na [b|] ty]; simpl in *.
  * rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /=.
    rewrite Nat.add_0_r in Hargs.
    rewrite rev_app_distr in Hsub. simpl in Hsub.
    intros subs. rewrite app_context_assoc in subs.
    specialize (IHn Δ _ T args s _ ltac:(lia) Hsub Hsp Hargs subs).
    intros Har. forward IHn.
    rewrite it_mkProd_or_LetIn_app.
    now simpl.
    eapply typing_spine_letin; auto.
    rewrite /subst1.
    now rewrite -subst_app_simpl.
  * rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /=.
    rewrite rev_app_distr in Hsub. 
    simpl in Hsub. destruct args; try discriminate.
    simpl in Hargs. rewrite Nat.add_1_r in Hargs. noconf Hargs. simpl in H; noconf H.
    intros subs. rewrite app_context_assoc in subs.    
    specialize (IHn Δ _ T args s _ ltac:(lia) Hsub Hsp H subs).
    intros Har.
    forward IHn. now rewrite it_mkProd_or_LetIn_app.
    eapply subslet_app_inv in subs as [subsl subsr].
    depelim subsl; simpl in H1; noconf H1.
    have Hskip := make_context_subst_skipn Hsub. 
    rewrite List.rev_length in Hskip. rewrite Hskip in H0; noconf H0.
    simpl; eapply typing_spine_prod; auto; first
    now rewrite /subst1 -subst_app_simpl.
    eapply isWAT_it_mkProd_or_LetIn_app in Har; eauto.
Qed.

Lemma typing_spine_it_mkProd_or_LetIn {cf:checker_flags} Σ Γ Δ T args s args' T' : 
  wf Σ.1 ->
  make_context_subst (List.rev Δ) args [] = Some s -> 
  typing_spine Σ Γ (subst0 s T) args' T' ->
  #|args| = context_assumptions Δ ->
  subslet Σ Γ s Δ ->
  isWfArity_or_Type Σ Γ (it_mkProd_or_LetIn Δ T) ->
  typing_spine Σ Γ (it_mkProd_or_LetIn Δ T) (args ++ args') T'.
Proof.
  intros. 
  pose proof (typing_spine_it_mkProd_or_LetIn_gen Σ Γ Δ [] T args s [] args' T'); auto.
  now rewrite subst_empty app_context_nil_l in X3.
Qed.

Record spine_subst {cf:checker_flags} Σ Γ inst s Δ := mkSpineSubst {
  spine_dom_wf : wf_local Σ Γ;
  spine_codom_wf : wf_local Σ (Γ ,,, Δ);
  inst_ctx_subst :> context_subst Δ inst s;
  inst_subslet :> subslet Σ Γ s Δ }.
Arguments inst_ctx_subst {cf Σ Γ inst s Δ}.
Arguments inst_subslet {cf Σ Γ inst s Δ}.
Hint Resolve inst_ctx_subst inst_subslet : pcuic.

Lemma typing_spine_it_mkProd_or_LetIn' {cf:checker_flags} Σ Γ Δ T args s args' T' : 
  wf Σ.1 ->
  spine_subst Σ Γ args s Δ ->
  typing_spine Σ Γ (subst0 s T) args' T' ->
  isWfArity_or_Type Σ Γ (it_mkProd_or_LetIn Δ T) ->
  typing_spine Σ Γ (it_mkProd_or_LetIn Δ T) (args ++ args') T'.
Proof.
  intros. destruct X0.
  eapply typing_spine_it_mkProd_or_LetIn; eauto.
  eapply make_context_subst_spec_inv. now rewrite List.rev_involutive.
  now pose proof (context_subst_length2 inst_ctx_subst0).
Qed.

Lemma typing_spine_strengthen {cf:checker_flags} Σ Γ T args U : 
  wf Σ.1 ->
  typing_spine Σ Γ T args U ->
  forall T', Σ ;;; Γ |- T' <= T ->
  typing_spine Σ Γ T' args U.
Proof.
  induction 2 in |- *; intros T' (*WAT*)redT.
  - constructor. eauto. transitivity ty; auto.
  - specialize (IHX0 (B {0 := hd})).
    forward IHX0. { reflexivity. }
    eapply type_spine_cons with na A B; auto.
    etransitivity; eauto.
Qed.

Inductive arity_spine {cf : checker_flags} (Σ : PCUICAst.global_env_ext) (Γ : PCUICAst.context) : 
  term -> list term -> term -> Type :=
  | arity_spine_nil ty ty' :
    isWfArity_or_Type Σ Γ ty' ->
    Σ ;;; Γ |- ty <= ty' ->
    arity_spine Σ Γ ty [] ty'
  | arity_spine_def : forall (tl : list term) 
                        (na : name) (A a B B' : term),                      
                      arity_spine Σ Γ (B {0 := a}) tl B' ->
                      arity_spine Σ Γ (tLetIn na a A B) tl B'
  | arity_spine_ass : forall (hd : term) (tl : list term) 
                        (na : name) (A B B' : term),
                      Σ;;; Γ |- hd : A ->
                      arity_spine Σ Γ (B {0 := hd}) tl B' ->
                      arity_spine Σ Γ (tProd na A B) (hd :: tl) B'.


Record wf_arity_spine {cf:checker_flags} Σ Γ T args T' :=
  { wf_arity_spine_wf : isWfArity_or_Type Σ Γ T;
    wf_arity_spine_spine : arity_spine Σ Γ T args T' }.

Lemma wf_arity_spine_typing_spine {cf:checker_flags} Σ Γ T args T' :
  wf Σ.1 ->
  wf_arity_spine Σ Γ T args T' ->
  typing_spine Σ Γ T args T'.
Proof.
  intros wfΣ [wf sp].
  have wfΓ := isWAT_wf_local wf.
  induction sp; try constructor; auto.
  eapply isWAT_tLetIn_red in wf; auto.
  specialize (IHsp wf).
  eapply typing_spine_strengthen; eauto.
  apply red_cumul. apply red1_red. constructor.
  
  econstructor; eauto. reflexivity. apply IHsp.
  eapply isWAT_tProd in wf => //.
  destruct wf as [wfA wfB].
  unshelve eapply (@isWAT_subst _ _ wfΣ Γ [vass na A] _ _ [hd]) in wfB => //.
  constructor; auto.
  constructor. constructor. now rewrite subst_empty.
Qed.

Lemma typing_spine_it_mkProd_or_LetIn_close {cf:checker_flags} Σ Γ Δ T args s : 
  wf Σ.1 ->
  make_context_subst (List.rev Δ) args [] = Some s -> 
  #|args| = context_assumptions Δ ->
  subslet Σ Γ s Δ ->
  isWfArity_or_Type Σ Γ (it_mkProd_or_LetIn Δ T) ->
  typing_spine Σ Γ (it_mkProd_or_LetIn Δ T) args (subst0 s T).
Proof.
  intros. 
  pose proof (typing_spine_it_mkProd_or_LetIn_gen Σ Γ Δ [] T args s [] []); auto.
  rewrite app_nil_r subst_empty in X2. apply X2; eauto.
  constructor. 2:eauto.
  eapply isWAT_it_mkProd_or_LetIn_app; eauto with pcuic. pcuic.
  now rewrite app_context_nil_l.
Qed.

Lemma typing_spine_it_mkProd_or_LetIn_close_eq {cf:checker_flags} Σ Γ Δ T args s T' : 
  wf Σ.1 ->
  make_context_subst (List.rev Δ) args [] = Some s -> 
  #|args| = context_assumptions Δ ->
  subslet Σ Γ s Δ ->
  isWfArity_or_Type Σ Γ (it_mkProd_or_LetIn Δ T) ->
  T' = (subst0 s T) ->
  typing_spine Σ Γ (it_mkProd_or_LetIn Δ T) args T'.
Proof.
  intros; subst; now apply typing_spine_it_mkProd_or_LetIn_close.
Qed. 

Lemma typing_spine_it_mkProd_or_LetIn_close' {cf:checker_flags} Σ Γ Δ T args s T' : 
  wf Σ.1 ->
  spine_subst Σ Γ args s Δ ->
  isWfArity_or_Type Σ Γ (it_mkProd_or_LetIn Δ T) ->
  T' = (subst0 s T) ->
  typing_spine Σ Γ (it_mkProd_or_LetIn Δ T) args T'.
Proof.
  intros wfΣ [].
  intros; eapply typing_spine_it_mkProd_or_LetIn_close_eq; eauto.
  eapply make_context_subst_spec_inv.
  now rewrite List.rev_involutive.
  now eapply context_subst_length2 in inst_ctx_subst0.
Qed. 


Lemma subst_inds_concl_head ind u mdecl (arity : context) :
  let head := tRel (#|ind_bodies mdecl| - S (inductive_ind ind) + #|ind_params mdecl| + #|arity|) in
  let s := (inds (inductive_mind ind) u (ind_bodies mdecl)) in
  inductive_ind ind < #|ind_bodies mdecl| ->
  subst s (#|arity| + #|ind_params mdecl|)
        (subst_instance_constr u head)
  = tInd ind u.
Proof.
  intros.
  subst head. simpl subst_instance_constr.
  rewrite (subst_rel_eq _ _ (#|ind_bodies mdecl| - S (inductive_ind ind)) (tInd ind u)) //; try lia.
  subst s. rewrite inds_spec rev_mapi nth_error_mapi /=.
  elim nth_error_spec. 
  + intros. simpl.
    f_equal. destruct ind; simpl. f_equal. f_equal. simpl in H. lia.
  + rewrite List.rev_length. lia.
Qed.

Lemma declared_constructor_valid_ty {cf:checker_flags} Σ Γ mdecl idecl i n cdecl u :
  wf Σ.1 ->
  wf_local Σ Γ ->
  declared_constructor Σ.1 mdecl idecl (i, n) cdecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  isType Σ Γ (type_of_constructor mdecl cdecl (i, n) u).
Proof.
  move=> wfΣ wfΓ declc Hu.
  epose proof (env_prop_typing _ _ validity Σ wfΣ Γ (tConstruct i n u)
    (type_of_constructor mdecl cdecl (i, n) u)).
  forward X by eapply type_Construct; eauto.
  simpl in X.
  destruct X.
  2:eauto.
  destruct i0 as [ctx [s [Hs ?]]].
  unfold type_of_constructor in Hs.
  destruct (on_declared_constructor _ declc); eauto.
  destruct s0 as [csort [Hsorc Hc]].
  destruct Hc as [cshape [cs Hcs] _ _].
  destruct cshape.
  rewrite cshape_eq in Hs. clear -declc Hs.
  rewrite /subst1 !subst_instance_constr_it_mkProd_or_LetIn
  !subst_it_mkProd_or_LetIn in Hs.
  rewrite !subst_instance_constr_mkApps !subst_mkApps in Hs.
  rewrite !subst_instance_context_length Nat.add_0_r in Hs.
  rewrite subst_inds_concl_head in Hs.
  + simpl. destruct declc as [[onm oni] ?].
    now eapply nth_error_Some_length in oni.
  + now rewrite !destArity_it_mkProd_or_LetIn destArity_app /= destArity_tInd in Hs.
Qed.

Lemma declared_inductive_unique {Σ ind mdecl mdecl' idecl idecl'} : 
  declared_inductive Σ mdecl ind idecl ->
  declared_inductive Σ mdecl' ind idecl' ->
  (mdecl = mdecl') * (idecl = idecl').
Proof.
  unfold declared_inductive, declared_minductive.
  intros [-> ?] [eq ?].
  noconf eq. split; congruence.
Qed.

Lemma declared_constructor_unique {Σ c mdecl mdecl' idecl idecl' cdecl cdecl'} : 
  declared_constructor Σ mdecl idecl c cdecl ->
  declared_constructor Σ mdecl' idecl' c cdecl' ->
  (mdecl = mdecl') * (idecl = idecl') * (cdecl = cdecl').
Proof.
  unfold declared_constructor.
  intros [? ?] [eq ?]. destruct (declared_inductive_unique H eq).
  subst mdecl' idecl'. rewrite H0 in H1. intuition congruence.
Qed.

Lemma subst_context_nil s n : subst_context s n [] = [].
Proof. reflexivity. Qed.

Lemma context_subst_subst Δ inst0 s Γ inst s'  :
  context_subst Δ inst0 s ->
  context_subst (subst_context s 0 Γ) inst s' ->
  context_subst (Δ ,,, Γ) (inst0 ++ inst) (s' ++ s).
Proof.
  induction Γ in inst, s' |- *.
  + intros HΔ Hi. depelim Hi.
    now rewrite app_nil_r.
  + intros H' Hsub. 
    rewrite subst_context_snoc0 in Hsub.
    destruct a as [na [b|] ty];
    depelim Hsub; simpl in H; noconf H.
    - specialize (IHΓ _ _ H' Hsub).
      assert(#|Γ| = #|s0|) as ->.
      { apply context_subst_length in Hsub.
        now rewrite subst_context_length in Hsub. }
      rewrite -(subst_app_simpl s0 s 0 b).
      simpl. now constructor.
    - specialize (IHΓ _ _ H' Hsub).
      assert(#|Γ| = #|s0|).
      { apply context_subst_length in Hsub.
        now rewrite subst_context_length in Hsub. }
      rewrite app_assoc /=. now constructor.
Qed.

Lemma subslet_app {cf:checker_flags} Σ Γ s s' Δ Δ' : 
  subslet Σ Γ s (subst_context s' 0 Δ) ->
  subslet Σ Γ s' Δ' ->
  subslet Σ Γ (s ++ s') (Δ' ,,, Δ).
Proof.
  induction Δ in s, s', Δ' |- *; simpl; auto; move=> sub'.
  - depelim sub'. auto.
  - rewrite subst_context_snoc in sub' => sub''.
    move:(subslet_length sub') => /=.
    rewrite /snoc /= subst_context_length /= => Hlen.
    destruct a as [na [b|] ty].
    * depelim sub'; simpl in H; noconf H.
      simpl in t0, Hlen.
      rewrite -subst_app_simpl' /=. lia.
      constructor. eauto.
      now rewrite - !subst_app_simpl' in t0; try lia.
    * rewrite /subst_decl /map_decl /snoc /= in sub'.
      depelim sub'; simpl in H; noconf H. simpl in Hlen.
      rewrite - !subst_app_simpl' in t0; try lia.
      simpl; constructor; eauto.
Qed.

Lemma mkApps_ind_typing_spine {cf:checker_flags} Σ Γ Γ' ind i
  inst ind' i' args args' : 
  wf Σ.1 ->
  wf_local Σ Γ ->
  isWfArity_or_Type Σ Γ (it_mkProd_or_LetIn Γ' (mkApps (tInd ind i) args)) ->
  typing_spine Σ Γ (it_mkProd_or_LetIn Γ' (mkApps (tInd ind i) args)) inst 
    (mkApps (tInd ind' i') args') ->
  ∑ instsubst, (make_context_subst (List.rev Γ') inst [] = Some instsubst) *
  (#|inst| = context_assumptions Γ' /\ ind = ind' /\ 
  R_universe_instance (eq_universe (global_ext_constraints Σ)) i i') *
  All2 (fun par par' => Σ ;;; Γ |- par = par') (map (subst0 instsubst) args) args' *
  (subslet Σ Γ instsubst Γ').
Proof.
  intros wfΣ wfΓ; revert args args' ind i ind' i' inst.
  revert Γ'. refine (ctx_length_rev_ind _ _ _); simpl.
  - intros args args' ind i ind' i' inst wat Hsp.
    depelim Hsp.
    eapply invert_cumul_ind_l in c as [i'' [args'' [? ?]]]; auto.
    eapply invert_red_ind in r as [? [eq ?]]. solve_discr. exists nil.
    intuition auto. clear i0.
    revert args' a. clear -b wfΣ wfΓ. induction b; intros args' H; depelim H; constructor.
    rewrite subst_empty.
    transitivity y; auto. symmetry.
    now eapply red_conv. now eauto.
    eapply invert_cumul_prod_r in c as [? [? [? [[? ?] ?]]]]; auto.
    eapply invert_red_ind in r as [? [eq ?]]. now solve_discr.
  - intros d Γ' IH args args' ind i ind' i' inst wat Hsp.
    rewrite it_mkProd_or_LetIn_app in Hsp.
    destruct d as [na [b|] ty]; simpl in *; rewrite /mkProd_or_LetIn /= in Hsp.
    + rewrite context_assumptions_app /= Nat.add_0_r.
      eapply typing_spine_letin_inv in Hsp; auto.
      rewrite /subst1 subst_it_mkProd_or_LetIn /= in Hsp.
      specialize (IH (subst_context [b] 0 Γ')).
      forward IH by rewrite subst_context_length; lia.
      rewrite subst_mkApps Nat.add_0_r in Hsp.
      specialize (IH (map (subst [b] #|Γ'|) args) args' ind i ind' i' inst).
      forward IH. {
        move: wat; rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /= => wat.
        eapply isWAT_tLetIn_red in wat; auto.
        now rewrite /subst1 subst_it_mkProd_or_LetIn subst_mkApps Nat.add_0_r
        in wat. }
      rewrite context_assumptions_subst in IH.
      intuition auto.
      destruct X as [isub [[[Hisub Hinst] Hargs] Hs]].
      eexists. intuition auto.
      eapply make_context_subst_spec in Hisub.
      eapply make_context_subst_spec_inv.
      rewrite List.rev_app_distr. simpl.
      rewrite List.rev_involutive.
      eapply (context_subst_subst [{| decl_name := na; decl_body := Some b;  decl_type := ty |}] [] [b] Γ').
      rewrite -{2}  (subst_empty 0 b). eapply context_subst_def. constructor.
      now rewrite List.rev_involutive in Hisub.
      rewrite map_map_compose in Hargs.
      assert (map (subst0 isub ∘ subst [b] #|Γ'|) args = map (subst0 (isub ++ [b])) args) as <-.
      { eapply map_ext => x. simpl.
        assert(#|Γ'| = #|isub|).
        { apply make_context_subst_spec in Hisub.
          apply context_subst_length in Hisub.
          now rewrite List.rev_involutive subst_context_length in Hisub. }
        rewrite H0.
        now rewrite -(subst_app_simpl isub [b] 0). }
      exact Hargs. 
      eapply subslet_app; eauto. rewrite -{1}(subst_empty 0 b). repeat constructor.
      rewrite !subst_empty.
      rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /= in wat.
      now eapply isWAT_tLetIn_dom in wat.
    + rewrite context_assumptions_app /=.
      pose proof (typing_spine_WAT_concl Hsp).
      depelim Hsp.
      eapply invert_cumul_prod_l in c as [? [? [? [[? ?] ?]]]]; auto.
      eapply invert_red_ind in r as [? [eq ?]]. now solve_discr.
      eapply cumul_Prod_inv in c as [conva cumulB].
      eapply (substitution_cumul0 _ _ _ _ _ _ hd) in cumulB; auto.
      rewrite /subst1 subst_it_mkProd_or_LetIn /= in cumulB.
      specialize (IH (subst_context [hd] 0 Γ')).
      forward IH by rewrite subst_context_length; lia.
      specialize (IH (map (subst [hd] #|Γ'|) args) args' ind i ind' i' tl). all:auto.
      have isWATs: isWfArity_or_Type Σ Γ
      (it_mkProd_or_LetIn (subst_context [hd] 0 Γ')
          (mkApps (tInd ind i) (map (subst [hd] #|Γ'|) args))). {
        move: wat; rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /= => wat.
        eapply isWAT_tProd in wat; auto. destruct wat as [isty wat].
        epose proof (isWAT_subst wfΣ (Γ:=Γ) (Δ:=[vass na ty])).
        forward X0. constructor; auto.
        specialize (X0 (it_mkProd_or_LetIn Γ' (mkApps (tInd ind i) args)) [hd]).
        forward X0. constructor. constructor. rewrite subst_empty; auto.
        eapply isWAT_tProd in i0; auto. destruct i0. 
        eapply type_Cumul with A; auto. now eapply conv_cumul.
        now rewrite /subst1 subst_it_mkProd_or_LetIn subst_mkApps Nat.add_0_r
        in X0. }
      rewrite subst_mkApps Nat.add_0_r in cumulB. simpl in *. 
      rewrite context_assumptions_subst in IH.
      eapply typing_spine_strengthen in Hsp.
      3:eapply cumulB. all:eauto.
      intuition auto.
      destruct X1 as [isub [[[Hisub [Htl [Hind Hu]]] Hargs] Hs]].
      exists (isub ++ [hd]). rewrite List.rev_app_distr.
      intuition auto. 2:lia.
      * apply make_context_subst_spec_inv.
        apply make_context_subst_spec in Hisub.
        rewrite List.rev_app_distr !List.rev_involutive in Hisub |- *.
        eapply (context_subst_subst [{| decl_name := na; decl_body := None; decl_type := ty |}] [hd] [hd] Γ'); auto.
        eapply (context_subst_ass _ [] []). constructor.
      * assert (map (subst0 isub ∘ subst [hd] #|Γ'|) args = map (subst0 (isub ++ [hd])) args) as <-.
      { eapply map_ext => x. simpl.
        assert(#|Γ'| = #|isub|).
        { apply make_context_subst_spec in Hisub.
          apply context_subst_length in Hisub.
          now rewrite List.rev_involutive subst_context_length in Hisub. }
        rewrite H.
        now rewrite -(subst_app_simpl isub [hd] 0). }
        now rewrite map_map_compose in Hargs.
      * eapply subslet_app; auto.
        constructor. constructor. rewrite subst_empty.
        rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /= in wat.
        eapply isWAT_tProd in wat as [Hty _]; auto.
        eapply type_Cumul; eauto. now eapply conv_cumul.
Qed.

Lemma firstn_app_left (A : Type) (n : nat) (l1 l2 : list A) k :
  k = #|l1| + n ->
  firstn k (l1 ++ l2) = l1 ++ firstn n l2.
Proof. intros ->; apply firstn_app_2.  Qed.

Lemma map_subst_app_to_extended_list_k s s' ctx k  :
  k = #|s| ->
  map (subst0 (s ++ s')) (to_extended_list_k ctx k) = 
  map (subst0 s') (to_extended_list_k ctx 0).
Proof.
  intros ->.
  induction ctx in s, s' |- *; simpl; auto.
  destruct a as [na [b|] ty]. simpl.
Admitted.  

Lemma map_lift0 l : map (lift0 0) l = l.
Proof. induction l; simpl; auto. now rewrite lift0_id. Qed.

Lemma map_context_length f l : #|map_context f l| = #|l|.
Proof. now rewrite /map_context map_length. Qed.

Lemma skipn_all_app_eq {A} n (l l' : list A) : n = #|l| -> skipn n (l ++ l') = l'.
Proof.
  move->. apply skipn_all_app.
Qed.

Lemma rev_case {A} (P : list A -> Type) :
  P nil -> (forall l x, P (l ++ [x])) -> forall l, P l.
Proof.
  intros; now apply rev_ind.
Qed.

Lemma firstn_length_le_inv {A} n (l : list A) : #|firstn n l| = n -> n <= #|l|.
Proof.
  induction l in n |- *; simpl; auto with arith;
  destruct n; simpl; auto with arith. discriminate.
Qed.

Hint Rewrite subst_context_length subst_instance_context_assumptions subst_instance_context_length 
  app_context_length map_context_length map_length app_length lift_context_length : len.


Lemma context_subst_app_inv {ctx ctx' : list PCUICAst.context_decl} {args s : list term} :
  context_subst (subst_context (skipn #|ctx| s) 0 ctx)
    (skipn (PCUICAst.context_assumptions ctx') args) 
    (firstn #|ctx| s)
  × context_subst ctx' (firstn (PCUICAst.context_assumptions ctx') args)	(skipn #|ctx| s) ->
  context_subst (ctx ++ ctx') args s.
Proof.
  move=> [Hl Hr].
  rewrite -(firstn_skipn (context_assumptions ctx') args).
  assert (lenctx' : context_assumptions ctx' + context_assumptions ctx = #|args|).
  { assert (lenctx'' : context_assumptions ctx' <= #|args|).
    move: (context_subst_assumptions_length _ _ _ Hr).
    rewrite firstn_length; lia.
    move: (context_subst_assumptions_length _ _ _ Hr).
    move: (context_subst_assumptions_length _ _ _ Hl).
    rewrite firstn_length skipn_length; try lia.
    intros H1 H2. rewrite context_assumptions_subst in H1. lia. }
  move: args s ctx' lenctx' Hl Hr.
  induction ctx => args s ctx' lenctx' Hl Hr.
  - simpl in *. depelim Hl. rewrite H app_nil_r. now rewrite skipn_0 in Hr.
  - simpl in *. destruct s as [|u s];
    simpl in *; rewrite subst_context_snoc0 in Hl; depelim Hl.
    simpl in H. noconf H.
    * destruct a as [na [b|] ty]; simpl in *; noconf H.
      rewrite skipn_S in Hl, Hr. destruct args using rev_case. rewrite skipn_nil in H0.
      apply (f_equal (@length _)) in H0. simpl in H0. autorewrite with len in H0.
      simpl in H0; lia. rewrite H0.
      rewrite skipn_app in H0.
      rewrite app_length /= in lenctx'.
      specialize (IHctx args s ctx'). forward IHctx by lia.
      assert (context_assumptions ctx' - #|args| = 0) by lia.
      rewrite H skipn_0 in H0. apply app_inj_tail in H0 as [Ha xu]. subst x.
      rewrite -Ha.
      rewrite -Ha in Hl. specialize (IHctx Hl).
      rewrite firstn_app in Hr |- *.
      rewrite H [firstn _ [u]]firstn_0 // app_nil_r in Hr |- *.
      specialize (IHctx Hr). rewrite app_assoc.
      now econstructor.
    * destruct a as [na' [b'|] ty']; simpl in *; simpl in H; noconf H. simpl in H.
      rewrite skipn_S in Hl, Hr, H. rewrite -H.
      pose proof (context_subst_length _ _ _ Hl). rewrite subst_context_length in H0.
      rewrite {3}H0 -subst_app_simpl [firstn #|ctx| _ ++ _]firstn_skipn. constructor.
      apply IHctx => //.
Qed.

Lemma arity_typing_spine {cf:checker_flags} Σ Γ Γ' s inst s' : 
  wf Σ.1 ->
  wf_local Σ (Γ ,,, Γ') ->
  typing_spine Σ Γ (it_mkProd_or_LetIn Γ' (tSort s)) inst (tSort s') ->
  (#|inst| = context_assumptions Γ') * leq_universe (global_ext_constraints Σ) s s' *
  ∑ instsubst, spine_subst Σ Γ inst instsubst Γ'.
Proof.
  intros wfΣ wfΓ'; revert s inst s'.
  assert (wf_local Σ Γ). now apply wf_local_app in wfΓ'. move X after wfΓ'.
  rename X into wfΓ.
  generalize (le_n #|Γ'|).
  generalize (#|Γ'|) at 2.
  induction n in Γ', wfΓ' |- *.
  - destruct Γ' using rev_ind; try clear IHΓ'; simpl; intros len s inst s' Hsp.
    + depelim Hsp.
      ++ intuition auto.
         now eapply cumul_Sort_inv.
         exists []. split; try constructor; auto.
      ++ now eapply cumul_Sort_Prod_inv in c.
    + rewrite app_length /= in len; elimtype False; lia.
  - intros len s inst s' Hsp.
    destruct Γ' using rev_ind; try clear IHΓ'.
    -- depelim Hsp. 1:intuition auto.
      --- now eapply cumul_Sort_inv.
      --- exists []; split; try constructor; auto.
      --- now eapply cumul_Sort_Prod_inv in c.
    -- rewrite app_length /= in len.
      rewrite it_mkProd_or_LetIn_app in Hsp.
      destruct x as [na [b|] ty]; simpl in *; rewrite /mkProd_or_LetIn /= in Hsp.
      + rewrite PCUICCtxShape.context_assumptions_app /= Nat.add_0_r.
        eapply typing_spine_letin_inv in Hsp; auto.
        rewrite /subst1 subst_it_mkProd_or_LetIn /= in Hsp.
        specialize (IHn (subst_context [b] 0 l)).
        forward IHn. {
          rewrite app_context_assoc in wfΓ'.
          apply All_local_env_app in wfΓ' as [wfb wfa].
          depelim wfb. simpl in H; noconf H. simpl in H. noconf H.
          eapply substitution_wf_local. eauto. 
          epose proof (cons_let_def Σ Γ [] [] na b ty ltac:(constructor)).
          rewrite !subst_empty in X. eapply X. auto.
          eapply All_local_env_app_inv; split.
          constructor; auto. apply wfa. }
        forward IHn by rewrite subst_context_length; lia.
        specialize (IHn s inst s' Hsp). 
        split. now rewrite context_assumptions_subst in IHn.
        destruct IHn as [[instlen leq] [instsubst [wfdom wfcodom cs subi]]].
        exists (instsubst ++ [subst0 [] b]).
        split; auto.
        * apply context_subst_app_inv. cbn.
          rewrite !skipn_0 {1}subst_empty.
          assert(#|l| <= n) by lia.
          rewrite context_assumptions_subst in instlen.
          pose proof (context_subst_length _ _ _ cs). rewrite subst_context_length in H0.
          rewrite !(firstn_app_left _ 0). lia. simpl. rewrite !app_nil_r.
          split. now rewrite H0 skipn_all_app.
          rewrite H0 skipn_all_app. repeat constructor.
        * apply subslet_app. now rewrite subst_empty.
          repeat constructor.
          rewrite app_context_assoc in wfΓ'. simpl in wfΓ'.
          apply wf_local_app in wfΓ'. depelim wfΓ'; simpl in H; noconf H.
          now rewrite !subst_empty.
      + rewrite PCUICCtxShape.context_assumptions_app /=.
        depelim Hsp. 
        now eapply cumul_Prod_Sort_inv in c.
        eapply cumul_Prod_inv in c as [conva cumulB].
        eapply (substitution_cumul0 _ _ _ _ _ _ hd) in cumulB; auto.
        rewrite /subst1 subst_it_mkProd_or_LetIn /= in cumulB.
        specialize (IHn (subst_context [hd] 0 l)).
        forward IHn. {
          rewrite app_context_assoc in wfΓ'.
          apply All_local_env_app in wfΓ' as [wfb wfa]; eauto.
          depelim wfb. simpl in H; noconf H.
          eapply substitution_wf_local. auto. 
          constructor. constructor. rewrite subst_empty.
          eapply type_Cumul. eapply t.
          right; eapply l0.
          eapply conv_cumul; auto. now symmetry. 
          eapply All_local_env_app_inv; eauto; split.
          constructor; eauto. eapply isWAT_tProd in i; intuition eauto.
          simpl in H; noconf H.
        }
        forward IHn by rewrite subst_context_length; lia.
        specialize (IHn s tl s'). 
        rewrite context_assumptions_subst in IHn.
        eapply typing_spine_strengthen in Hsp.
        3:eapply cumulB. all:eauto.
        simpl. specialize (IHn Hsp).
        destruct IHn as [[instlen leq] [instsubst [wfdom wfcodom cs subi]]].
        intuition auto. lia.
        exists (instsubst ++ [hd]).
        split; auto.
        * apply context_subst_app_inv. cbn.
          rewrite !skipn_S skipn_0.
          assert(#|l| <= n) by lia.
          pose proof (context_subst_length _ _ _ cs). rewrite subst_context_length in H0.
          rewrite !(firstn_app_left _ 0). lia. simpl. rewrite !app_nil_r.
          split. now rewrite H0 skipn_all_app.
          rewrite H0 skipn_all_app. apply (context_subst_ass _ []). constructor.
        * apply subslet_app => //.
          repeat constructor.
          rewrite app_context_assoc in wfΓ'. simpl in wfΓ'.
          apply wf_local_app in wfΓ'. depelim wfΓ'; simpl in H; noconf H.
          rewrite !subst_empty. red in l0.
          eapply type_Cumul; eauto. eapply conv_cumul. now symmetry.
Qed.

Lemma it_mkProd_or_LetIn_wf_local {cf:checker_flags} Σ Γ Δ T U : 
  wf Σ.1 ->
  Σ ;;; Γ |- it_mkProd_or_LetIn Δ T : U -> wf_local Σ (Γ ,,, Δ).
Proof.
  move=> wfΣ; move: Γ T U.
  induction Δ using rev_ind => Γ T U.
  + simpl. intros. now eapply typing_wf_local in X.
  + rewrite it_mkProd_or_LetIn_app.
    destruct x as [na [b|] ty]; cbn; move=> H.
    * apply inversion_LetIn in H as (s1 & A & H0 & H1 & H2 & H3); auto.
      eapply All_local_env_app_inv; split; pcuic. now apply typing_wf_local in H0.
      eapply All_local_env_app_inv. split. repeat constructor. now exists s1.
      auto. apply IHΔ in H2.
      eapply All_local_env_app in H2. intuition auto.
      eapply All_local_env_impl; eauto. simpl. intros.
      now rewrite app_context_assoc.
    * apply inversion_Prod in H as (s1 & A & H0 & H1 & H2); auto.
      eapply All_local_env_app_inv; split; pcuic. now apply typing_wf_local in H0.
      eapply All_local_env_app_inv. split. repeat constructor. now exists s1.
      apply IHΔ in H1.
      eapply All_local_env_app in H1. intuition auto.
      eapply All_local_env_impl; eauto. simpl. intros.
      now rewrite app_context_assoc.
Qed.

Lemma isWAT_it_mkProd_or_LetIn_wf_local {cf:checker_flags} Σ Γ Δ T : 
  wf Σ.1 ->
  isWfArity_or_Type Σ Γ (it_mkProd_or_LetIn Δ T) -> wf_local Σ (Γ ,,, Δ).
Proof.
  move=> wfΣ [[ctx [s [Hs Hwf]]]|[s Hs]].
  - rewrite destArity_it_mkProd_or_LetIn app_context_nil_l in Hs.
    eapply destArity_app_Some in Hs as [ctx' [? eq]]. subst ctx.
    rewrite app_context_assoc in Hwf.
    now eapply All_local_env_app in Hwf as [Hwf _].
  - now eapply it_mkProd_or_LetIn_wf_local in Hs.
Qed.

Lemma on_minductive_wf_params_indices {cf : checker_flags} (Σ : global_env) mdecl ind idecl :
  wf Σ ->
  declared_minductive Σ (inductive_mind ind) mdecl ->
  forall (oib : on_ind_body (lift_typing typing) (Σ, ind_universes mdecl) (inductive_mind ind)
    mdecl (inductive_ind ind) idecl),
  wf_local (Σ, ind_universes mdecl) (ind_params mdecl ,,, ind_indices oib).
Proof.
  intros.
  eapply on_declared_minductive in H; auto.
  pose proof (oib.(onArity)).
  rewrite oib.(ind_arity_eq) in X0.
  destruct X0 as [s Hs].
  rewrite -it_mkProd_or_LetIn_app in Hs.
  eapply it_mkProd_or_LetIn_wf_local in Hs. 
  now rewrite app_context_nil_l in Hs. now simpl.
Qed.

Lemma on_minductive_wf_params_indices_inst {cf : checker_flags} (Σ : global_env × universes_decl)
    mdecl (u : Instance.t) ind idecl :
   wf Σ.1 ->
   declared_minductive Σ.1 (inductive_mind ind) mdecl ->
   forall (oib : on_ind_body (lift_typing typing) (Σ.1, ind_universes mdecl) (inductive_mind ind)
      mdecl (inductive_ind ind) idecl),
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  wf_local Σ (subst_instance_context u (ind_params mdecl ,,, ind_indices oib)).
Proof.
  intros.
  eapply (wf_local_instantiate _ (InductiveDecl mdecl)); eauto.
  now apply on_minductive_wf_params_indices.
Qed.

Lemma isWAT_weaken {cf:checker_flags} Σ Γ T :
  wf Σ.1 -> wf_local Σ Γ ->
  isWfArity_or_Type Σ [] T ->
  isWfArity_or_Type Σ Γ T.
Proof.
  move=> wfΣ wfΓ [[ctx [s eq]]|[s hs]].
  - left; exists ctx, s. intuition pcuic.
    rewrite app_context_nil_l in b.
    eapply weaken_wf_local=> //.
  - right. exists s.
    unshelve epose proof (subject_closed _ _ _ _ _ hs); eauto.
    eapply (weakening _ _ Γ) in hs => //.
    rewrite lift_closed in hs => //.
    now rewrite app_context_nil_l in hs.
    now rewrite app_context_nil_l.
Qed.

Lemma on_inductive_inst {cf:checker_flags} Σ Γ ind u mdecl idecl : 
  wf Σ.1 -> 
  wf_local Σ Γ ->
  declared_minductive Σ.1 (inductive_mind ind) mdecl ->
  on_inductive (lift_typing typing) (Σ.1, ind_universes mdecl) (inductive_mind ind) mdecl ->
  forall (oib : on_ind_body (lift_typing typing) (Σ.1, ind_universes mdecl) (inductive_mind ind) mdecl 
           (inductive_ind ind) idecl),
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  isWfArity_or_Type Σ Γ (it_mkProd_or_LetIn (subst_instance_context u (ind_params mdecl ,,, oib.(ind_indices)))
        (tSort (subst_instance_univ u oib.(ind_sort)))).
Proof.
  move=> wfΣ wfΓ declm oi oib cext.
  pose proof (oib.(onArity)) as ar.
  rewrite oib.(ind_arity_eq) in ar.
  destruct ar as [s ar].
  eapply isWAT_weaken => //.
  rewrite -(subst_instance_constr_it_mkProd_or_LetIn u _ (tSort _)).
  rewrite -it_mkProd_or_LetIn_app in ar.
  eapply (typing_subst_instance_decl Σ [] _ _ _ (InductiveDecl mdecl) u) in ar.
  right. eexists _. eapply ar. all:eauto.
Qed.

Definition wf_global_ext `{cf:checker_flags} Σ ext :=
  (wf_ext_wk (Σ, ext) * sub_context_set (monomorphic_udecl ext) (global_context_set Σ))%type.

Lemma wf_local_subst_instance {cf:checker_flags} Σ Γ ext u :
  wf_global_ext Σ.1 ext ->
  consistent_instance_ext Σ ext u ->
  wf_local (Σ.1, ext) Γ ->
  wf_local Σ (subst_instance_context u Γ).
Proof.
  destruct Σ as [Σ φ]. intros X X0 X1. simpl in *.
  induction X1; cbn; constructor; auto.
  - destruct t0 as [s Hs]. hnf.
    eapply typing_subst_instance'' in Hs; eauto; apply X.
  - destruct t0 as [s Hs]. hnf.
    eapply typing_subst_instance'' in Hs; eauto; apply X. 
  - hnf in t1 |- *.
    eapply typing_subst_instance'' in t1; eauto; apply X.
Qed.

Lemma wf_local_subst_instance_decl {cf:checker_flags} Σ Γ c decl u :
  wf Σ.1 ->
  lookup_env Σ.1 c = Some decl ->
  wf_local (Σ.1, universes_decl_of_decl decl) Γ ->
  consistent_instance_ext Σ (universes_decl_of_decl decl) u ->
  wf_local Σ (subst_instance_context u Γ).
Proof.
  destruct Σ as [Σ φ]. intros X X0 X1 X2.
  induction X1; cbn; constructor; auto.
  - destruct t0 as [s Hs]. hnf.
    eapply typing_subst_instance_decl in Hs; eauto.
  - destruct t0 as [s Hs]. hnf.
    eapply typing_subst_instance_decl in Hs; eauto.
  - hnf in t1 |- *.
    eapply typing_subst_instance_decl in t1; eauto.
Qed.

Lemma nth_error_rev_map {A B} (f : A -> B) l i : 
  i < #|l| ->
  nth_error (rev_map f l) (#|l| - S i) = 
  option_map f (nth_error l i).
Proof.
  move=> Hi.
  rewrite rev_map_spec. rewrite -(map_length f l) -nth_error_rev ?map_length //.
  now rewrite nth_error_map.
Qed.
  
Lemma nth_errror_arities_context {cf:checker_flags} (Σ : global_env_ext) mdecl ind idecl decl : 
  wf Σ.1 ->
  declared_inductive Σ mdecl ind idecl ->
  on_inductive (lift_typing typing) (Σ.1, ind_universes mdecl)
    (inductive_mind ind) mdecl ->
  on_ind_body (lift_typing typing) (Σ.1, ind_universes mdecl)
    (inductive_mind ind) mdecl (inductive_ind ind) idecl ->
  nth_error (arities_context (ind_bodies mdecl)) (#|ind_bodies mdecl| - S (inductive_ind ind)) = Some decl ->
  decl.(decl_type) = idecl.(ind_type).
Proof.
  move=> wfΣ decli oni onib.
  unfold arities_context.
  rewrite nth_error_rev_map.
  destruct decli as [declm decli]. now apply nth_error_Some_length in decli.
  destruct nth_error eqn:Heq; try discriminate.
  destruct decli. rewrite H0 in Heq. noconf Heq.
  simpl. move=> [] <-. now simpl.
Qed.


Lemma declared_inductive_minductive Σ ind mdecl idecl :
  declared_inductive Σ mdecl ind idecl -> declared_minductive Σ (inductive_mind ind) mdecl.
Proof. now intros []. Qed.
Hint Resolve declared_inductive_minductive : pcuic.

Ltac pcuic ::= intuition eauto with pcuic ||
  (try repeat red; cbn in *;
    try (solve
    [ intuition auto; eauto with pcuic || (try lia || congruence) ])).

Lemma spine_subst_app_inv {cf:checker_flags} Σ Γ Δ Δ' inst inst' insts :
  wf Σ.1 -> 
  #|inst| = context_assumptions Δ ->
  spine_subst Σ Γ (inst ++ inst') insts (Δ ,,, Δ') ->
  spine_subst Σ Γ inst (skipn #|Δ'| insts) Δ *
  spine_subst Σ Γ inst' (firstn #|Δ'| insts) (subst_context (skipn #|Δ'| insts) 0 Δ').
Proof.
  intros wfΣ len sp.
  destruct sp as [wfdom wfcodom cs subs].
  eapply context_subst_app in cs as [csl csr].
  rewrite skipn_all_app_eq in csl => //.
  rewrite (firstn_app_left _ 0) in csr => //. lia.
  rewrite firstn_0 in csr => //. rewrite app_nil_r in csr.
  eapply subslet_app_inv in subs as [sl sr].
  split; split; auto. rewrite app_context_assoc in wfcodom.
  now eapply All_local_env_app in wfcodom as [? ?].
  eapply substitution_wf_local; eauto.
  now rewrite app_context_assoc in wfcodom.
Qed.
(* 
Lemma typing_spine_it_mkProd_or_LetIn_extlist {cf:checker_flags} Σ Γ Δ Δ' T args T' : 
  wf Σ.1 ->
  typing_spine Σ (Γ ,,, Δ ,,, Δ')
     (it_mkProd_or_LetIn Δ T) (to_extended_list_k Δ #|Δ'| ++ args) T' ->
  closedn #|Δ| T ->
  typing_spine Σ (Γ ,,, Δ ,,, Δ') (lift0 #|Δ'| T) args T'.
Proof.
  intros wfΣ. 
  unfold to_extended_list_k. rewrite -reln_acc.
  revert Δ' T.
  pose proof (firstn_all Δ).
  rewrite -{2 3 4}H.
  assert(#|Δ| <= #|Δ|) by reflexivity.
  clear H. revert H0.
  generalize #|Δ| at -2. intros n; revert Δ.
  induction n;intros Δ le Δ' T Hty cl; simpl.
  rewrite firstn_0 in cl => //.
  rewrite lift_closed => //.

  destruct Δ using rev_case.
  simpl in *.
  rewrite lift_closed => //.
  rewrite firstn_app in cl.
  rewrite app_length in le. simpl in le. 


  induction Δ at 2 3 4 using ctx_length_rev_ind; intros Δ' T Hty cl; simpl.
  rewrite lift_closed => //.
  rewrite it_mkProd_or_LetIn_app in Hty.
  destruct d as [na [b|] ty]; simpl in *.
  rewrite app_length in cl. simpl in cl.
  rewrite reln_app in Hty.
  simpl in Hty. eapply typing_spine_strengthen in

  specialize (X _ _ _ _ )
 Qed. *)
(*
Lemma ctx_inst_spine_subst {cf:checker_flags} Σ Γ inst Δ : 
  wf Σ.1 ->
  wf_local Σ Γ ->
  ctx_inst (lift_typing typing) Σ Γ inst (List.rev Δ) ->
  ∑ insts, spine_subst Σ Γ inst insts Δ.
Proof.
  move=> wfΣ wfΓ.
  remember (List.rev Δ) as Δ'.
  rewrite -(List.rev_involutive Δ). rewrite -HeqΔ'. clear Δ HeqΔ'.
  induction 1.
  - exists []; constructor; auto.
  - simpl. destruct IHX as [insts sp]. *)


  
Lemma on_constructor_subst' {cf:checker_flags} Σ ind mdecl idecl csort cdecl : 
  wf Σ -> 
  declared_inductive Σ mdecl ind idecl ->
  on_inductive (lift_typing typing) (Σ, ind_universes mdecl) (inductive_mind ind) mdecl ->
  forall (oib : on_ind_body (lift_typing typing) (Σ, ind_universes mdecl) (inductive_mind ind) mdecl 
           (inductive_ind ind) idecl)
        (onc : on_constructor (lift_typing typing) (Σ, ind_universes mdecl)
          mdecl (inductive_ind ind) idecl (ind_indices oib) cdecl csort),
  wf_global_ext Σ (ind_universes mdecl) *
  wf_local (Σ, ind_universes mdecl)
   (arities_context (ind_bodies mdecl) ,,, ind_params mdecl ,,, cshape_args onc.(cshape)) *
  ctx_inst (lift_typing typing) (Σ, ind_universes mdecl)
             (arities_context (ind_bodies mdecl) ,,, ind_params mdecl ,,,
              cshape_args (cshape onc))
             (cshape_indices (cshape onc)) 
            (List.rev (lift_context #|cshape_args (cshape onc)| 0 (ind_indices oib))). 
Proof.
  move=> wfΣ declm oi oib onc.
  pose proof (on_cargs onc). simpl in X.
  split.
  - split. split.
    2:{ eapply (weaken_lookup_on_global_env'' _ _ (InductiveDecl mdecl)); pcuic. destruct declm; pcuic. }
    red. split; eauto. simpl. eapply (weaken_lookup_on_global_env' _ _ (InductiveDecl mdecl)); eauto.
    destruct declm; pcuic. 
    eapply type_local_ctx_wf_local in X => //. clear X.
    eapply weaken_wf_local => //.
    eapply wf_arities_context; eauto. destruct declm; eauto.
    now eapply onParams.
  - apply (on_cindices onc).
Qed.
(*
  rewrite onc.(cshape).(cshape_eq) in t.
  rewrite -it_mkProd_or_LetIn_app in t.
  eapply inversion_it_mkProd_or_LetIn in t => //.
  unfold cshape_concl_head in t. simpl in t.
  eapply inversion_mkApps in t as [A [U [ta [sp cum]]]].
  eapply inversion_Rel in ta as [decl [wfΓ [nth cum']]].
  rewrite nth_error_app_ge in nth. autorewrite with len. lia.
  autorewrite with len in nth.
  all:auto.
  assert ( (#|ind_bodies mdecl| - S (inductive_ind ind) + #|ind_params mdecl| +
  #|cshape_args onc.2.π1| -
  (#|cshape_args onc.2.π1| + #|ind_params mdecl|)) = #|ind_bodies mdecl| - S (inductive_ind ind)) by lia.
  move: nth; rewrite H; clear H. destruct nth_error eqn:Heq => //.
  simpl.
  move=> [=] Hdecl. eapply (nth_errror_arities_context (Σ, ind_universes mdecl)) in Heq; eauto.
  subst decl.
  rewrite Heq in cum'; clear Heq c.
  assert(closed (ind_type idecl)).
  { pose proof (oib.(onArity)). rewrite (oib.(ind_arity_eq)) in X0 |- *.
    destruct X0 as [s Hs]. now apply subject_closed in Hs. } 
  rewrite lift_closed in cum' => //.
  eapply typing_spine_strengthen in sp; pcuic.
  eapply typing_spine_weaken_concl in sp; eauto. 2:left; eexists [], _; intuition auto.
  clear cum' A. move: sp. 
  rewrite (oib.(ind_arity_eq)).
  rewrite -it_mkProd_or_LetIn_app.
  move=> sp. simpl in sp.
  apply (arity_typing_spine (Σ, ind_universes mdecl)) in sp as [[Hlen Hleq] [inst Hinst]] => //.
  clear Hlen.
  rewrite [_ ,,, _]app_context_assoc in Hinst.
  now exists inst.
  apply weaken_wf_local => //.

  rewrite [_ ,,, _]app_context_assoc in wfΓ.
  eapply All_local_env_app in wfΓ as [? ?].
  apply on_minductive_wf_params_indices => //. pcuic.
Qed.
*)

Lemma on_constructor_subst {cf:checker_flags} Σ ind mdecl idecl csort cdecl : 
  wf Σ -> 
  declared_inductive Σ mdecl ind idecl ->
  on_inductive (lift_typing typing) (Σ, ind_universes mdecl) (inductive_mind ind) mdecl ->
  forall (oib : on_ind_body (lift_typing typing) (Σ, ind_universes mdecl) (inductive_mind ind) mdecl 
           (inductive_ind ind) idecl)
        (onc : on_constructor (lift_typing typing) (Σ, ind_universes mdecl)
          mdecl (inductive_ind ind) idecl (ind_indices oib) cdecl csort),
  wf_global_ext Σ (ind_universes mdecl) *
  wf_local (Σ, ind_universes mdecl)
   (arities_context (ind_bodies mdecl) ,,, ind_params mdecl ,,, cshape_args onc.(cshape)) *
  ∑ inst,
  spine_subst (Σ, ind_universes mdecl)
             (arities_context (ind_bodies mdecl) ,,, ind_params mdecl ,,,
              cshape_args onc.(cshape))
             ((to_extended_list_k (ind_params mdecl) #|cshape_args onc.(cshape)|) ++
              (cshape_indices onc.(cshape))) inst
          (ind_params mdecl ,,, ind_indices oib). 
Proof.
  move=> wfΣ declm oi oib onc.
  pose proof (onc.(on_cargs)). simpl in X.
  split. split. split.
  2:{ eapply (weaken_lookup_on_global_env'' _ _ (InductiveDecl mdecl)); pcuic. destruct declm; pcuic. }
  red. split; eauto. simpl. eapply (weaken_lookup_on_global_env' _ _ (InductiveDecl mdecl)); eauto.
  destruct declm; pcuic. 
  eapply type_local_ctx_wf_local in X => //. clear X.
  eapply weaken_wf_local => //.
  eapply wf_arities_context; eauto. destruct declm; eauto.
  now eapply onParams.
  destruct (on_ctype onc).
  rewrite ((onc.(cshape)).(cshape_eq)) in t.
  rewrite -it_mkProd_or_LetIn_app in t.
  eapply inversion_it_mkProd_or_LetIn in t => //.
  unfold cshape_concl_head in t. simpl in t.
  eapply inversion_mkApps in t as [A [U [ta [sp cum]]]].
  eapply inversion_Rel in ta as [decl [wfΓ [nth cum']]].
  rewrite nth_error_app_ge in nth. autorewrite with len. lia.
  autorewrite with len in nth.
  all:auto.
  assert ( (#|ind_bodies mdecl| - S (inductive_ind ind) + #|ind_params mdecl| +
  #|cshape_args onc.(cshape)| -
  (#|cshape_args onc.(cshape)| + #|ind_params mdecl|)) = #|ind_bodies mdecl| - S (inductive_ind ind)) by lia.
  move: nth; rewrite H; clear H. destruct nth_error eqn:Heq => //.
  simpl.
  move=> [=] Hdecl. eapply (nth_errror_arities_context (Σ, ind_universes mdecl)) in Heq; eauto.
  subst decl.
  rewrite Heq in cum'; clear Heq c.
  assert(closed (ind_type idecl)).
  { pose proof (oib.(onArity)). rewrite (oib.(ind_arity_eq)) in X0 |- *.
    destruct X0 as [s Hs]. now apply subject_closed in Hs. } 
  rewrite lift_closed in cum' => //.
  eapply typing_spine_strengthen in sp; pcuic.
  eapply typing_spine_weaken_concl in sp; eauto. 2:left; eexists [], _; intuition auto.
  clear cum' A. move: sp. 
  rewrite (oib.(ind_arity_eq)).
  rewrite -it_mkProd_or_LetIn_app.
  move=> sp. simpl in sp.
  apply (arity_typing_spine (Σ, ind_universes mdecl)) in sp as [[Hlen Hleq] [inst Hinst]] => //.
  clear Hlen.
  rewrite [_ ,,, _]app_context_assoc in Hinst.
  now exists inst.
  apply weaken_wf_local => //.

  rewrite [_ ,,, _]app_context_assoc in wfΓ.
  eapply All_local_env_app in wfΓ as [? ?].
  apply on_minductive_wf_params_indices => //. pcuic.
Qed.

Lemma spine_subst_inst {cf:checker_flags} Σ ext u Γ i s Δ  :
  spine_subst (Σ.1, ext) Γ i s Δ ->
  consistent_instance_ext Σ ext u ->
  spine_subst Σ (subst_instance_context u Γ)
    (map (subst_instance_constr u) i)
    (map (subst_instance_constr u) s)
    (subst_instance_context u Δ).
Admitted.


Notation ctx_inst Σ Γ i Δ := (ctx_inst (lift_typing typing) Σ Γ i Δ).

Lemma ctx_inst_inst {cf:checker_flags} Σ ext u Γ i Δ  :
  ctx_inst (Σ.1, ext) Γ i Δ ->
  consistent_instance_ext Σ ext u ->
  ctx_inst Σ (subst_instance_context u Γ)
    (map (subst_instance_constr u) i)
    (subst_instance_context u Δ).
Admitted.

Lemma on_constructor_inst {cf:checker_flags} Σ ind u mdecl idecl csort cdecl : 
  wf Σ.1 -> 
  declared_inductive Σ.1 mdecl ind idecl ->
  on_inductive (lift_typing typing) (Σ.1, ind_universes mdecl) (inductive_mind ind) mdecl ->
  forall (oib : on_ind_body (lift_typing typing) (Σ.1, ind_universes mdecl) (inductive_mind ind) mdecl 
           (inductive_ind ind) idecl)
        (onc : on_constructor (lift_typing typing) (Σ.1, PCUICAst.ind_universes mdecl)
          mdecl (inductive_ind ind) idecl (ind_indices oib) cdecl csort), 
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  wf_local Σ (subst_instance_context u
    (arities_context (ind_bodies mdecl) ,,, ind_params mdecl ,,, cshape_args onc.(cshape))) *
  ∑ inst,
  spine_subst Σ
          (subst_instance_context u
             (arities_context (ind_bodies mdecl) ,,, ind_params mdecl ,,,
              cshape_args onc.(cshape)))
          (map (subst_instance_constr u)
             (to_extended_list_k (ind_params mdecl) #|cshape_args onc.(cshape)|) ++
           map (subst_instance_constr u) (cshape_indices onc.(cshape))) inst
          (subst_instance_context u (ind_params mdecl) ,,,
           subst_instance_context u (ind_indices oib)). 
Proof.
  move=> wfΣ declm oi oib onc cext.
  destruct (on_constructor_subst Σ.1 ind mdecl idecl _ cdecl wfΣ declm oi oib onc) as [[wfext wfl] [inst sp]].
  eapply wf_local_subst_instance in wfl; eauto. split=> //.
  eapply spine_subst_inst in sp; eauto.
  rewrite map_app in sp. rewrite -subst_instance_context_app.
  eexists ; eauto.
Qed.

Lemma isWAT_mkApps_Ind {cf:checker_flags} {Σ Γ ind u args} (wfΣ : wf Σ.1)
  {mdecl idecl} (declm : declared_inductive Σ.1 mdecl ind idecl) :
  wf_local Σ Γ ->
  isWfArity_or_Type Σ Γ (mkApps (tInd ind u) args) ->
  ∑ parsubst argsubst,
    let oib := (on_declared_inductive wfΣ declm).2 in
    let parctx := (subst_instance_context u (ind_params mdecl)) in
    let argctx := (subst_context parsubst 0 (subst_instance_context u (oib.(ind_indices)))) in
    spine_subst Σ Γ (firstn (ind_npars mdecl) args) parsubst parctx *
    spine_subst Σ Γ (skipn (ind_npars mdecl) args) argsubst argctx *
    consistent_instance_ext Σ (ind_universes mdecl) u.
Proof.
  move=> wfΓ isWAT.
  destruct isWAT.
  destruct i as [ctx [s Hs]].
  destruct Hs. rewrite destArity_tInd in e => //.
  destruct i as [s Hs].
  eapply inversion_mkApps in Hs as [A [U [tyc [tyargs tycum]]]]; auto.
  eapply typing_spine_weaken_concl in tyargs; eauto.
  2:left; exists [], s; eauto.
  clear tycum.
  eapply inversion_Ind in tyc as [mdecl' [idecl' [wfl [decli [cu cum]]]]] => //.
  pose proof (declared_inductive_unique decli declm) as [? ?]; subst mdecl' idecl'.
  clear decli. rename declm into decli.
  eapply typing_spine_strengthen in tyargs; eauto.
  set (decli' := on_declared_inductive _ _). clearbody decli'.
  destruct decli' as [declm decli'].
  pose proof (decli'.(onArity)) as ar. 
  rewrite decli'.(ind_arity_eq) in tyargs, ar. clear cum A.
  hnf in ar. destruct ar as [s' ar].
  rewrite !subst_instance_constr_it_mkProd_or_LetIn in tyargs.
  simpl in tyargs. rewrite -it_mkProd_or_LetIn_app in tyargs.
  eapply arity_typing_spine in tyargs as [[argslen leqs] [instsubst [wfdom wfcodom cs subs]]] => //.
  apply context_subst_app in cs as [parsubst argsubst].
  eexists _, _. move=> lk parctx argctx. subst lk.
  rewrite subst_instance_context_assumptions in argsubst, parsubst.
  rewrite declm.(onNpars _ _ _ _) in argsubst, parsubst.
  eapply subslet_app_inv in subs as [subp suba].
  rewrite subst_instance_context_length in subp, suba.
  subst parctx argctx.
  repeat split; eauto; rewrite ?subst_instance_context_length => //.
  rewrite app_context_assoc in wfcodom. now apply All_local_env_app in wfcodom as [? ?].
  simpl.
  eapply substitution_wf_local; eauto. now rewrite app_context_assoc in wfcodom.
  unshelve eapply on_inductive_inst in declm; pcuic.
  rewrite subst_instance_context_app in declm.
  now eapply isWAT_it_mkProd_or_LetIn_wf_local in declm.
Qed.


Lemma subst_type_local_ctx {cf:checker_flags} Σ Γ Γ' Δ Δ' s ctxs : 
  wf Σ.1 ->
  wf_local Σ (Γ ,,, Δ ,,, Γ') ->
  type_local_ctx (lift_typing typing) Σ (Γ ,,, Δ ,,, Γ') Δ' ctxs ->
  subslet Σ Γ s Δ ->
  type_local_ctx (lift_typing typing) Σ (Γ ,,, subst_context s 0 Γ') (subst_context s #|Γ'| Δ') ctxs.
Proof.
  induction Δ' in Γ' |- *; simpl; auto.
  destruct a as [na [b|] ty]; simpl; intuition auto.
  + destruct a0; simpl; rewrite subst_context_snoc /= /subst_decl /map_decl /=.
    intuition auto.
    - exists x; auto.
      rewrite -app_context_assoc in t.
      eapply substitution in t; eauto.
      rewrite subst_context_app app_context_assoc in t.
      simpl in t. rewrite Nat.add_0_r in t. 
      now rewrite app_context_length in t.
    - rewrite -app_context_assoc in b1.
      eapply substitution in b1; eauto.
      rewrite subst_context_app app_context_assoc Nat.add_0_r in b1.
      now rewrite app_context_length in b1.
  + rewrite subst_context_snoc /= /subst_decl /map_decl /=.
      intuition auto.
      rewrite -app_context_assoc in b.
      eapply substitution in b; eauto.
      rewrite subst_context_app app_context_assoc in b.
      rewrite Nat.add_0_r in b. 
      now rewrite app_context_length in b.
Qed.

Lemma Construct_Ind_ind_eq {cf:checker_flags} {Σ} (wfΣ : wf Σ.1):
  forall {Γ n i args u i' args' u' mdecl idecl cdecl},
  Σ ;;; Γ |- mkApps (tConstruct i n u) args : mkApps (tInd i' u') args' ->
  forall (Hdecl : declared_constructor Σ.1 mdecl idecl (i, n) cdecl),
  let '(onind, oib, existT cs (hnth, onc)) := on_declared_constructor wfΣ Hdecl in
  (i = i') * 
  (* Universe instances match *)
  R_universe_instance (eq_universe (global_ext_constraints Σ)) u u' *
  consistent_instance_ext Σ (ind_universes mdecl) u' *    
  (#|args| = (ind_npars mdecl + context_assumptions onc.(cshape).(cshape_args))%nat) *
  ∑ parsubst argsubst parsubst' argsubst',
    let parctx := (subst_instance_context u (ind_params mdecl)) in
    let parctx' := (subst_instance_context u' (ind_params mdecl)) in
    let argctx := (subst_context parsubst 0
    ((subst_context (inds (inductive_mind i) u mdecl.(ind_bodies)) #|ind_params mdecl|
    (subst_instance_context u onc.(cshape).(cshape_args))))) in
    let argctx' := (subst_context parsubst' 0 (subst_instance_context u' oib.(ind_indices))) in
    
    spine_subst Σ Γ (firstn (ind_npars mdecl) args) parsubst parctx *
    spine_subst Σ Γ (firstn (ind_npars mdecl) args') parsubst' parctx' *
    spine_subst Σ Γ (skipn (ind_npars mdecl) args) argsubst argctx *
    spine_subst Σ Γ (skipn (ind_npars mdecl) args')  argsubst' argctx' *

    ∑ s, type_local_ctx (lift_typing typing) Σ Γ argctx s *
    (** Parameters match *)
    (All2 (fun par par' => Σ ;;; Γ |- par = par') 
      (firstn mdecl.(ind_npars) args) 
      (firstn mdecl.(ind_npars) args') * 

    (** Indices match *)
    All2 (fun par par' => Σ ;;; Γ |- par = par') 
      (map (subst0 (argsubst ++ parsubst) ∘ 
      subst (inds (inductive_mind i) u mdecl.(ind_bodies)) (#|onc.(cshape).(cshape_args)| + #|ind_params mdecl|)
      ∘ (subst_instance_constr u)) 
        onc.(cshape).(cshape_indices))
      (skipn mdecl.(ind_npars) args')).

Proof.
  intros Γ n i args u i' args' u' mdecl idecl cdecl h declc.
  unfold on_declared_constructor.
  destruct (on_declared_constructor _ declc). destruct s as [? [_ onc]].
  unshelve epose proof (env_prop_typing _ _ validity _ _ _ _ _ h) as vi'; eauto using typing_wf_local.
  eapply type_mkApps_inv in h; auto.
  destruct h as [T [U [[hC hs] hc]]].
  apply inversion_Construct in hC
    as [mdecl' [idecl' [cdecl' [hΓ [isdecl [const htc]]]]]]; auto.
  assert (vty:=declared_constructor_valid_ty _ _ _ _ _ _ _ _ wfΣ hΓ isdecl const). 
  eapply typing_spine_strengthen in hs. 3:eapply htc. all:eauto.
  eapply typing_spine_weaken_concl in hs.
  3:{ eapply cumul_trans; eauto with pcuic. } all:auto.
  clear hc htc.
  destruct (declared_constructor_unique isdecl declc) as [[? ?] ?].
  subst mdecl' idecl' cdecl'. clear isdecl.
  destruct p as [onmind onind]. clear onc.
  destruct declc as [decli declc].
  remember (on_declared_inductive wfΣ decli). clear onmind onind.
  destruct p.
  rename o into onmind. rename o0 into onind.
  destruct declared_constructor_inv as [? [_ onc]].
  simpl in onc. unfold on_declared_inductive in Heqp.
  injection Heqp. intros indeq _. 
  move: onc Heqp. rewrite -indeq.
  intros onc Heqp.
  pose proof (on_constructor_inst _ _ _ _ _ _ _ wfΣ decli onmind onind onc const).
  destruct onc as [cshape [cs' t] cargs cinds]; simpl.
  simpl in *. 
  unfold type_of_constructor in hs. simpl in hs.
  rewrite (cshape_eq cshape) in hs.  
  rewrite !subst_instance_constr_it_mkProd_or_LetIn in hs.
  rewrite !subst_it_mkProd_or_LetIn subst_instance_context_length Nat.add_0_r in hs.
  rewrite subst_instance_constr_mkApps subst_mkApps subst_instance_context_length in hs.
  assert (Hind : inductive_ind i < #|ind_bodies mdecl|).
  { red in decli. destruct decli. clear -e.
    now eapply nth_error_Some_length in e. }
  rewrite (subst_inds_concl_head i) in hs => //.
  rewrite -it_mkProd_or_LetIn_app in hs.
  assert(ind_npars mdecl = PCUICAst.context_assumptions (ind_params mdecl)).
  { now pose (onNpars _ _ _ _ onmind). }
  assert (closed_ctx (ind_params mdecl)).
  { destruct onmind.
    red in onParams. clear Heqp; now apply closed_wf_local in onParams. }
  eapply mkApps_ind_typing_spine in hs as [isubst [[[Hisubst [Hargslen [Hi Hu]]] Hargs] Hs]]; auto.
  subst i'.
  eapply (isWAT_mkApps_Ind wfΣ decli) in vi' as (parsubst & argsubst & (spars & sargs) & cons) => //.
  unfold on_declared_inductive in sargs. simpl in sargs. rewrite -indeq in sargs. clear indeq Heqp.
  split=> //. split=> //.
  now rewrite Hargslen context_assumptions_app !context_assumptions_subst !subst_instance_context_assumptions; lia.

  exists (skipn #|cshape.(cshape_args)| isubst), (firstn #|cshape.(cshape_args)| isubst).
  apply make_context_subst_spec in Hisubst.
  move: Hisubst.
  rewrite List.rev_involutive.
  move/context_subst_app.
  rewrite !subst_context_length !subst_instance_context_length.
  rewrite context_assumptions_subst subst_instance_context_assumptions -H.
  move=>  [argsub parsub].
  rewrite closed_ctx_subst in parsub.
  now rewrite closedn_subst_instance_context.
  eapply subslet_app_inv in Hs.
  move: Hs. autorewrite with len. intuition auto.
  rewrite closed_ctx_subst in a0 => //.
  now rewrite closedn_subst_instance_context.

  (*rewrite -Heqp in spars sargs. simpl in *. clear Heqp. *)
  exists parsubst, argsubst.
  assert(wfar : wf_local Σ
  (Γ ,,, subst_instance_context u (arities_context (ind_bodies mdecl)))).
  { eapply weaken_wf_local => //.
    eapply wf_local_instantiate => //; destruct decli; eauto.
    eapply wf_arities_context => //; eauto. }
  assert(wfpars : wf_local Σ (subst_instance_context u (ind_params mdecl))).
    { eapply on_minductive_wf_params => //; eauto.
      destruct decli; eauto. }
      
  intuition auto; try split; auto.
  - apply weaken_wf_local => //.
  - pose proof (subslet_length a0). rewrite subst_instance_context_length in H1.
    rewrite -H1 -subst_app_context.
    eapply (substitution_wf_local _ _ (subst_instance_context u (arities_context (ind_bodies mdecl) ,,, ind_params mdecl))); eauto.
    rewrite subst_instance_context_app; eapply subslet_app; eauto.
    now rewrite closed_ctx_subst ?closedn_subst_instance_context.
    eapply weaken_subslet => //.
    now eapply subslet_inds; eauto.
    rewrite -app_context_assoc.
    eapply weaken_wf_local => //.
    rewrite -subst_instance_context_app. 
    apply a.
  - exists (subst_instance_univ u x0). split.
    move/onParams: onmind. rewrite /on_context.
    pose proof (wf_local_instantiate Σ (InductiveDecl mdecl) (ind_params mdecl) u).
    move=> H'. eapply X in H'; eauto.
    2:destruct decli; eauto.
    clear -wfar wfpars wfΣ hΓ const decli t cargs H0 H' a a0.
    eapply (subst_type_local_ctx _ _ [] 
      (subst_context (inds (inductive_mind i) u (ind_bodies mdecl)) 0 (subst_instance_context u (ind_params mdecl)))) => //.
    simpl. eapply weaken_wf_local => //.
    rewrite closed_ctx_subst => //.
    now rewrite closedn_subst_instance_context.
    simpl. rewrite -(subst_instance_context_length u (ind_params mdecl)).
    eapply (subst_type_local_ctx _ _ _ (subst_instance_context u (arities_context (ind_bodies mdecl)))) => //.
    eapply weaken_wf_local => //.
    rewrite -app_context_assoc.
    eapply weaken_type_local_ctx => //.
    rewrite -subst_instance_context_app.
    eapply type_local_ctx_instantiate => //; destruct decli; eauto.
    eapply weaken_subslet => //.
    now eapply subslet_inds; eauto.
    now rewrite closed_ctx_subst ?closedn_subst_instance_context.

    move: (All2_firstn  _ _ _ _ _ mdecl.(ind_npars) Hargs).
    move: (All2_skipn  _ _ _ _ _ mdecl.(ind_npars) Hargs).
    clear Hargs.
    rewrite !map_map_compose !map_app.
    rewrite -map_map_compose.
    rewrite (firstn_app_left _ 0).
    rewrite PCUICUnivSubst.map_subst_instance_constr_to_extended_list_k.
    rewrite -map_map_compose.
    rewrite -to_extended_list_k_map_subst; first lia.
    now rewrite map_length to_extended_list_k_length.
    rewrite /= app_nil_r.
    rewrite skipn_all_app_eq.
    autorewrite with len. 
    rewrite to_extended_list_k_length. lia.
    rewrite !map_map_compose.
    assert (#|cshape.(cshape_args)| <= #|isubst|).
    apply context_subst_length in argsub.
    autorewrite with len in argsub.
    now apply firstn_length_le_inv.

    rewrite -(firstn_skipn #|cshape.(cshape_args)| isubst).
    rewrite -[map _ (to_extended_list_k _ _)]map_map_compose.
    rewrite subst_instance_to_extended_list_k.
    rewrite -[map _ (to_extended_list_k _ _)]map_map_compose. 
    rewrite -to_extended_list_k_map_subst.
    rewrite subst_instance_context_length. lia.
    rewrite map_subst_app_to_extended_list_k.
    rewrite firstn_length_le => //.
    
    erewrite subst_to_extended_list_k.
    rewrite map_lift0. split. eauto.
    rewrite firstn_skipn. rewrite firstn_skipn in All2_skipn.
    now rewrite firstn_skipn.

    apply make_context_subst_spec_inv. now rewrite List.rev_involutive.

  - rewrite it_mkProd_or_LetIn_app.
    right. unfold type_of_constructor in vty.
    rewrite cshape.(cshape_eq) in vty. move: vty.
    rewrite !subst_instance_constr_it_mkProd_or_LetIn.
    rewrite !subst_it_mkProd_or_LetIn subst_instance_context_length Nat.add_0_r.
    rewrite subst_instance_constr_mkApps subst_mkApps subst_instance_context_length.
    rewrite subst_inds_concl_head. all:simpl; auto.
Qed.

Lemma map_subst_lift_id s l : map (subst0 s ∘ lift0 #|s|) l = l.
Proof.
  induction l; simpl; auto.
  rewrite -{1}(Nat.add_0_r #|s|) simpl_subst'; auto.
  now rewrite lift0_id IHl.  
Qed.

Lemma subslet_wf_local {cf:checker_flags} Σ Γ Δ :
  wf_local Σ (Γ ,,, Δ) ->
  ∑ s, type_local_ctx (lift_typing typing) Σ Γ Δ s.
Proof.
  induction Δ. simpl. 
  intros _. exists Universe.type0m. exact I.
  intros H; depelim H. red in l.
  destruct l as [u Hu].
  destruct (IHΔ H) as [s Hs].
  exists (Universe.sup u s).
  constructor.
Admitted.

Lemma mkApps_conv_args `{checker_flags} Σ Γ f f' u v :
  wf Σ.1 ->
  Σ ;;; Γ |- f = f' ->
  All2 (fun x y => Σ ;;; Γ |- x = y) u v ->
  Σ ;;; Γ |- mkApps f u = mkApps f' v.
Proof.
  move=> wfΣ cf cuv. induction cuv in f, f', cf |- *.
  - auto.
  - simpl. apply IHcuv.
    now apply App_conv.
Qed.

Lemma context_relation_impl {P Q Γ Γ'} :
  (forall Γ  Γ' d d', P Γ Γ' d d' -> Q Γ Γ' d d') ->
  context_relation P Γ Γ' -> context_relation Q Γ Γ'.
Proof.
  induction 2; constructor; auto.
Qed.

Lemma cum_LetIn `{cf:checker_flags} Σ Γ na1 na2 t1 t2 A1 A2 u1 u2 :
  wf Σ.1 ->
  Σ;;; Γ |- t1 = t2 ->
  Σ;;; Γ |- A1 = A2 ->
  cumul Σ (Γ ,, vdef na1 t1 A1) u1 u2 ->
  cumul Σ Γ (tLetIn na1 t1 A1 u1) (tLetIn na2 t2 A2 u2).
Proof.
  intros wfΣ X H H'.
  - eapply cumul_trans => //.
    + eapply cumul_LetIn_bo. eassumption.
    + etransitivity.
      * eapply conv_cumul. eapply conv_LetIn_tm. eassumption.
      * eapply conv_cumul, conv_LetIn_ty with (na := na1). assumption.
Qed.

Lemma cumul_it_mkProd_or_LetIn {cf : checker_flags} (Σ : PCUICAst.global_env_ext)
  (Δ Γ Γ' : PCUICAst.context) (B B' : term) :
  wf Σ.1 ->
  context_relation (fun Γ Γ' => conv_decls Σ (Δ ,,, Γ) (Δ  ,,, Γ')) Γ Γ' ->
  Σ ;;; Δ ,,, Γ |- B <= B' ->
  Σ ;;; Δ |- PCUICAst.it_mkProd_or_LetIn Γ B <= PCUICAst.it_mkProd_or_LetIn Γ' B'.
Proof.
  move=> wfΣ; move: B B' Γ' Δ.
  induction Γ as [|d Γ] using rev_ind; move=> B B' Γ' Δ; 
  destruct Γ' as [|d' Γ'] using rev_ind; try clear IHΓ';
    move=> H; try solve [simpl; auto].
  + depelim H. apply app_eq_nil in H; intuition discriminate.
  + depelim H. apply app_eq_nil in H; intuition discriminate.
  + assert (clen : #|Γ| = #|Γ'|). 
    { apply context_relation_length in H.
      autorewrite with len in H; simpl in H. lia. }
    apply context_relation_app in H as [cd cctx] => //.
    depelim cd. depelim c.
    - rewrite !it_mkProd_or_LetIn_app => //=.
      simpl. move=> HB. apply congr_cumul_prod => //.
      eapply IHΓ.
      * unshelve eapply (context_relation_impl _ cctx). 
        simpl. intros * X. rewrite !app_context_assoc in X.
        destruct X; constructor; auto.
      * now rewrite app_context_assoc in HB.
    - rewrite !it_mkProd_or_LetIn_app => //=.
      simpl. intros HB. apply cum_LetIn => //.
      depelim c; auto. depelim c; auto.
      eapply IHΓ.
      * unshelve eapply (context_relation_impl _ cctx). 
        simpl. intros * X. rewrite !app_context_assoc in X.
        destruct X; constructor; auto.
      * now rewrite app_context_assoc in HB.
Qed.

Lemma substitution_conv `{cf : checker_flags} (Σ : global_env_ext) Γ Γ' Γ'' s M N :
  wf Σ -> wf_local Σ (Γ ,,, Γ' ,,, Γ'') -> subslet Σ Γ s Γ' ->
  Σ ;;; Γ ,,, Γ' ,,, Γ'' |- M = N ->
  Σ ;;; Γ ,,, subst_context s 0 Γ'' |- subst s #|Γ''| M = subst s #|Γ''| N.
Proof.
  intros wfΣ wfΓ Hs. induction 1.
  - constructor.
    now apply subst_eq_term.
  - eapply substitution_let_red in r. 4:eauto. all:eauto with wf.
    eapply red_conv_conv; eauto.
  - eapply substitution_let_red in r. 4:eauto. all:eauto with wf.
    eapply red_conv_conv_inv; eauto.
  - eapply conv_eta_l. 2: eassumption.
    eapply eta_expands_subst. assumption.
  - eapply conv_eta_r. 1: eassumption.
    eapply eta_expands_subst. assumption.
Qed.

Lemma red_subst_conv {cf:checker_flags} (Σ : global_env_ext) Γ Δ Γ' s s' b : wf Σ ->
  All2 (red Σ Γ) s s' ->
  untyped_subslet Γ s Δ ->
  conv Σ (Γ ,,, Γ') (subst s #|Γ'| b) (subst s' #|Γ'| b).
Proof.
  move=> wfΣ eqsub subs.
  apply red_conv. now eapply red_red.
Qed.

Derive Signature for untyped_subslet.
(* 
Lemma untyped_subslet_conv  {cf:checker_flags} (Σ : global_env_ext) Γ Δ s s' : wf Σ ->
  All2 (conv Σ Γ) s s' ->
  untyped_subslet Γ s Δ -> untyped_subslet Γ s' Δ.
Proof.
  move=> wfΣ convs subs.
  induction subs in s', convs |- *; depelim convs; try econstructor; auto.
  econstructor.
   *)
Lemma conv_subst_conv {cf:checker_flags} (Σ : global_env_ext) Γ Δ Δ' Γ' s s' b : wf Σ ->
  All2 (conv Σ Γ) s s' ->
  untyped_subslet Γ s Δ ->
  untyped_subslet Γ s' Δ' ->
  conv Σ (Γ ,,, Γ') (subst s #|Γ'| b) (subst s' #|Γ'| b).
Proof.
  move=> wfΣ eqsub subs subs'.
  assert(∑ s0 s'0, All2 (red Σ Γ) s s0 * All2 (red Σ Γ) s' s'0 * All2 (eq_term Σ) s0 s'0)
    as [s0 [s'0 [[redl redr] eqs]]].
  { induction eqsub in Δ, subs |- *.
    depelim subs. exists [], []; split; auto.
    depelim subs.
    - specialize (IHeqsub _ subs) as [s0 [s'0 [[redl redr] eqs0]]].
      eapply conv_alt_red in r as [v [v' [[redv redv'] eqvv']]].
      exists (v :: s0), (v' :: s'0). repeat split; constructor; auto.
    - specialize (IHeqsub _ subs) as [s0 [s'0 [[redl redr] eqs0]]].
      eapply conv_alt_red in r as [v [v' [[redv redv'] eqvv']]].
      exists (v :: s0), (v' :: s'0). repeat split; constructor; auto. }
  eapply conv_trans => //. apply red_conv. eapply red_red => //; eauto.
  eapply conv_sym, conv_trans => //. apply red_conv. eapply red_red => //; eauto.
  apply conv_refl. red. apply eq_term_upto_univ_substs. typeclasses eauto.
  reflexivity. now symmetry.
Qed.

Lemma subslet_untyped_subslet {cf:checker_flags} Σ Γ s Γ' : subslet Σ Γ s Γ' -> untyped_subslet Γ s Γ'.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma subst_conv {cf:checker_flags} {Σ} Γ Γ0 Γ1 Δ s s' T U : 
  wf Σ.1 ->
  subslet Σ Γ s Γ0 ->
  subslet Σ Γ s' Γ1 ->
  All2 (conv Σ Γ) s s' ->
  wf_local Σ (Γ ,,, Γ0 ,,, Δ) ->
  Σ;;; Γ ,,, Γ0 ,,, Δ |- T = U ->
  Σ;;; Γ ,,, subst_context s 0 Δ |- subst s #|Δ| T = subst s' #|Δ| U.
Proof.
  move=> wfΣ subss subss' eqsub wfctx eqty.
  eapply conv_trans => //.
  eapply substitution_conv => //. eapply wfctx. auto. 
  apply eqty. clear eqty.
  rewrite -(subst_context_length s 0 Δ).
  eapply conv_subst_conv => //; eauto using subslet_untyped_subslet.
Qed.

Lemma context_relation_subst {cf:checker_flags} {Σ} Γ Γ0 Γ1 Δ Δ' s s' : 
  wf Σ.1 ->
  wf_local Σ (Γ ,,, Γ0 ,,, Δ) ->
  subslet Σ Γ s Γ0 ->
  subslet Σ Γ s' Γ1 ->
  All2 (conv Σ Γ) s s' ->
  context_relation
  (fun Γ0 Γ' : PCUICAst.context => conv_decls Σ (Γ ,,, Γ0) (Γ ,,, Γ'))
  (Γ0 ,,, Δ)
  (Γ1 ,,, Δ') ->
  context_relation
  (fun Γ0 Γ' : PCUICAst.context => conv_decls Σ (Γ ,,, Γ0) (Γ ,,, Γ'))
  (subst_context s 0 Δ)
  (subst_context s' 0 Δ').
Proof.
  move=> wfΣ wfl subss subss' eqsub ctxr.
  assert (hlen: #|Γ0| = #|Γ1|).
  { rewrite -(subslet_length subss) -(subslet_length subss').
    now apply All2_length in eqsub. }
  assert(clen := context_relation_length _ _ _ ctxr).
  autorewrite with len in clen. rewrite hlen in clen.
  assert(#|Δ| = #|Δ'|) by lia.
  clear clen. 
  move: Δ' wfl ctxr H.
  induction Δ as [|d Δ]; intros * wfl ctxr len0; destruct Δ' as [|d' Δ']; simpl in len0; try lia.
  - constructor.
  - rewrite !subst_context_snoc. specialize (IHΔ Δ'). depelim wfl; specialize (IHΔ wfl);
    depelim ctxr; simpl in H; noconf H; noconf len0; simpl in H; noconf H;
    depelim c; simpl.
    * constructor; auto. constructor. simpl.
      rewrite !Nat.add_0_r. rewrite -H.
      eapply subst_conv; eauto. now rewrite -app_context_assoc.
    * constructor; auto. constructor; simpl;
      rewrite !Nat.add_0_r -H;
      eapply subst_conv; eauto; now rewrite -app_context_assoc.
    * constructor; auto. constructor; simpl;
      rewrite !Nat.add_0_r -H;
      eapply subst_conv; eauto; now rewrite -app_context_assoc.
Qed.  

Lemma weaken_conv {cf:checker_flags} {Σ Γ t u} Δ : 
  wf Σ.1 -> wf_local Σ Δ -> wf_local Σ Γ ->
  closedn #|Γ| t -> closedn #|Γ| u ->
  Σ ;;; Γ |- t = u ->
  Σ ;;; Δ ,,, Γ |- t = u.
Proof.
  intros wfΣ wfΔ wfΓ clt clu ty.
  epose proof (weakening_conv Σ [] Γ Δ t u wfΣ).
  rewrite !app_context_nil_l in X.
  forward X by eauto using typing_wf_local.
  pose proof (closed_wf_local _ _ wfΣ wfΓ).
  rewrite closed_ctx_lift in X; auto.
  rewrite !lift_closed in X => //.
Qed.

Lemma conv_subst_instance {cf:checker_flags} (Σ : global_env_ext) Γ u A B univs :
  forallb (fun x => negb (Level.is_prop x)) u ->
  valid_constraints (global_ext_constraints (Σ.1, univs))
                    (subst_instance_cstrs u Σ) ->
  Σ ;;; Γ |- A = B ->
  (Σ.1,univs) ;;; subst_instance_context u Γ
                   |- subst_instance_constr u A = subst_instance_constr u B.
Proof.
  intros Hu HH X0. induction X0.
  - econstructor.
    eapply eq_term_subst_instance; tea.
  - econstructor 2. 1: eapply red1_subst_instance; cbn; eauto. eauto.
  - econstructor 3. 1: eauto. eapply red1_subst_instance; cbn; eauto.
  - eapply conv_eta_l. 2: eauto.
    eapply eta_expands_subst_instance_constr. assumption.
  - eapply conv_eta_r. 1: eauto.
    eapply eta_expands_subst_instance_constr. assumption.
Qed.

Lemma context_relation_subst_instance {cf:checker_flags} {Σ} Γ Δ u u' : 
  wf Σ.1 ->
  wf_local Σ Γ -> wf_local Σ (subst_instance_context u Δ) ->
  R_universe_instance (eq_universe (global_ext_constraints Σ)) u u' ->
  context_relation
  (fun Γ0 Γ' : PCUICAst.context => conv_decls Σ (Γ ,,, Γ0) (Γ ,,, Γ'))
  (subst_instance_context u Δ)
  (subst_instance_context u' Δ).
Proof.
  move=> wfΣ wf wf0 equ.
  assert (cl := closed_wf_local _ _ _ wf0).
  rewrite closedn_subst_instance_context in cl.
  induction Δ as [|d Δ] in cl, wf0 |- *.
  - constructor.
  - simpl.
    apply closedn_ctx_cons in cl. apply andP in cl as [clctx cld].
    simpl in wf0.
    destruct d as [na [b|] ty] => /=.
    * depelim wf0; simpl in H; noconf H; simpl in *.
      simpl in cld. unfold closed_decl in cld. simpl in cld. simpl.
      apply andP in cld as [clb clty].
      constructor; auto. constructor. apply weaken_conv; auto.
      autorewrite with len. now rewrite closedn_subst_instance_constr.
      autorewrite with len. now rewrite closedn_subst_instance_constr.
      constructor. red.
      apply eq_term_upto_univ_subst_instance_constr; try typeclasses eauto. auto.
      constructor. red.
      apply eq_term_upto_univ_subst_instance_constr; try typeclasses eauto. auto.
    * depelim wf0; simpl in H; noconf H; simpl in *.
      simpl in cld. unfold closed_decl in cld. simpl in cld. simpl.
      constructor; auto. constructor. apply weaken_conv; auto.
      autorewrite with len. now rewrite closedn_subst_instance_constr.
      autorewrite with len. now rewrite closedn_subst_instance_constr.
      constructor. red.
      apply eq_term_upto_univ_subst_instance_constr; try typeclasses eauto. auto.
Qed.

Lemma context_relation_over_same {cf:checker_flags} Σ Γ Δ Δ' :
  context_relation (fun Γ0 Γ'  => conv_decls Σ (Γ ,,, Γ0) (Γ ,,, Γ')) Δ Δ' ->
  context_relation (conv_decls Σ) (Γ ,,, Δ) (Γ ,,, Δ').
Proof.
  induction 1; simpl; try constructor; pcuic.
Qed.

Lemma context_relation_over_same_app {cf:checker_flags} Σ Γ Δ Δ' :
  context_relation (conv_decls Σ) (Γ ,,, Δ) (Γ ,,, Δ') ->
  context_relation (fun Γ0 Γ' => conv_decls Σ (Γ ,,, Γ0) (Γ ,,, Γ')) Δ Δ'.
Proof.
  move=> H. pose (context_relation_length _ _ _ H).
  autorewrite with len in e. assert(#|Δ| = #|Δ'|) by lia.
  move/context_relation_app: H => H.
  now specialize (H H0) as [_ H].
Qed.

Lemma All2_refl {A} {P : A -> A -> Type} l : 
  (forall x, P x x) ->
  All2 P l l.
Proof.
  intros HP. induction l; constructor; auto.
Qed.

Lemma conv_inds {cf:checker_flags} Σ Γ u u' ind mdecl :
  R_universe_instance (eq_universe (global_ext_constraints Σ)) u u' ->
  All2 (conv Σ Γ) (inds (inductive_mind ind) u (ind_bodies mdecl))
    (inds (inductive_mind ind) u' (ind_bodies mdecl)).
Proof.
  move=> equ.
  unfold inds. generalize #|ind_bodies mdecl|.
  induction n; constructor; auto.
  clear IHn.
  now repeat constructor.
Qed.

Lemma spine_subst_conv {cf:checker_flags} Σ Γ inst insts Δ inst' insts' Δ' :
  wf Σ.1 ->
  spine_subst Σ Γ inst insts Δ ->
  spine_subst Σ Γ inst' insts' Δ' ->
  context_relation (fun Δ Δ' => conv_decls Σ (Γ ,,, Δ) (Γ ,,, Δ')) Δ Δ' ->
  All2 (conv Σ Γ) inst inst' -> All2 (conv Σ Γ) insts insts'.
Proof.
  move=> wfΣ [_ wf cs sl] [_ _ cs' sl'] cv.
  move: inst insts cs wf sl inst' insts' cs' sl'.
  induction cv; intros; depelim cs ; depelim cs';
    try (simpl in H; noconf H); try (simpl in H0; noconf H0).
  - constructor; auto.    
  - eapply All2_app_inv in X as [[l1 l2] [[? ?] ?]].
    depelim a2. depelim a2. apply app_inj_tail in e as [? ?]; subst.
    depelim sl; depelim sl'; simpl in H; noconf H; simpl in H0; noconf H0;
      try (simpl in H1; noconf H1).
    depelim wf; simpl in H; noconf H.
    specialize (IHcv _ _ cs wf sl _ _ cs' sl' a1).
    constructor; auto.
  - depelim sl; depelim sl'; simpl in H; noconf H; simpl in H0; noconf H0;
      try (simpl in H1; noconf H1); try (simpl in H2; noconf H2).
    depelim wf; simpl in H; noconf H.
    specialize (IHcv _ _ cs wf sl _ _ cs' sl' X).
    constructor; auto.
    eapply (subst_conv _ _ _ []); eauto.
    depelim p; pcuic.
Qed.

Lemma weakening_conv_gen :
  forall {cf : checker_flags} (Σ : global_env × universes_decl)
    (Γ Γ' Γ'' : PCUICAst.context) (M N : term) k,
  wf Σ.1 -> k = #|Γ''| ->
  Σ;;; Γ ,,, Γ' |- M = N ->
  Σ;;; Γ ,,, Γ'' ,,, lift_context k 0 Γ' |- lift k #|Γ'| M = lift k #|Γ'| N.
Proof.
  intros; subst k; now eapply weakening_conv.
Qed.

Lemma to_extended_list_k_eq Γ Γ' n : same_ctx_shape Γ Γ' -> 
  to_extended_list_k Γ n = to_extended_list_k Γ' n.
Proof.
  unfold to_extended_list_k.
  intros s.
  generalize (@nil term). induction s in n |- *; simpl; auto.
Qed.

Lemma to_extended_list_eq Γ Γ' : same_ctx_shape Γ Γ' -> 
  to_extended_list Γ = to_extended_list Γ'.
Proof.
  unfold to_extended_list. apply to_extended_list_k_eq.
Qed.

Lemma same_ctx_shape_refl Γ : same_ctx_shape Γ Γ.
Proof. induction Γ. constructor; auto.
  destruct a as [? [?|] ?]; constructor; simpl; auto.
Qed.

Lemma same_ctx_shape_map Γ Γ' f f' : same_ctx_shape Γ Γ' ->
  same_ctx_shape (map_context f Γ) (map_context f' Γ').
Proof. induction 1; constructor; auto. Qed.

Lemma same_ctx_shape_subst Γ Γ' s k s' k' : same_ctx_shape Γ Γ' ->
  same_ctx_shape (subst_context s k Γ) (subst_context s' k' Γ').
Proof. move=> same. induction same in s, k |- *. constructor; auto.
  rewrite !subst_context_snoc. constructor; auto. apply IHsame.
  rewrite !subst_context_snoc. constructor; auto. apply IHsame.
Qed.

Notation "⋆" := ltac:(solve [pcuic]) (only parsing).

Lemma consistent_instance_ext_eq {cf:checker_flags} Σ ext u u' :
  consistent_instance_ext Σ ext u ->
  R_universe_instance (eq_universe Σ) u u' ->
  consistent_instance_ext Σ ext u'.
Proof. Admitted.

Lemma spine_subst_subst {cf:checker_flags} Σ Γ Γ0 Γ' i s Δ sub : 
  wf Σ.1 ->
  spine_subst Σ (Γ ,,, Γ0 ,,, Γ') i s Δ ->
  subslet Σ Γ sub Γ0 ->
  spine_subst Σ (Γ ,,, subst_context sub 0 Γ') (map (subst sub #|Γ'|) i) (map (subst sub #|Γ'|) s)
   (subst_context sub #|Γ'| Δ).
Proof.
  move=> wfΣ [wfl wfΔ cs subl] subs.
  split.
  eapply substitution_wf_local; eauto.
  pose proof (subst_context_app sub 0 Γ' Δ). rewrite Nat.add_0_r in H. rewrite -app_context_assoc -H.
  clear H.
  eapply substitution_wf_local; eauto. now rewrite app_context_assoc.
  clear subl wfl wfΔ.
  induction cs in Γ, Γ0, Γ', subs |- *; rewrite ?subst_context_snoc ?map_app; simpl; try constructor.
  eapply IHcs; eauto.
  specialize (IHcs _ _ Γ' subs).
  epose proof (context_subst_def _ _ _ na (subst sub (#|Γ1| + #|Γ'|) b) (subst sub (#|Γ1| + #|Γ'|) t) IHcs).
  rewrite /subst_decl /map_decl /=.
  rewrite distr_subst. 
  now rewrite (context_subst_length _ _ _ cs) in X |- *.
  clear cs wfΔ.
  induction subl; rewrite ?subst_context_snoc ?map_app; simpl; try constructor; auto.
  - eapply substitution in t0; eauto. simpl.
    rewrite -(subslet_length subl).
    now rewrite -distr_subst.
  - eapply substitution in t0; eauto. simpl.
    rewrite -(subslet_length subl).
    rewrite !distr_subst in t0.
    epose proof (cons_let_def _  _ _ _ _  _ _ IHsubl t0).
    now rewrite - !distr_subst in X.
Qed.

Lemma weaken_subslet {cf:checker_flags} Σ s Δ Γ Γ' :
  wf Σ.1 ->
  wf_local Σ Γ -> wf_local Σ Γ' ->
  subslet Σ Γ' s Δ -> subslet Σ (Γ ,,, Γ') s Δ.
Proof.
  intros wfΣ wfΔ wfΓ'.
  induction 1; constructor; auto.
  + eapply (weaken_ctx Γ); eauto.
  + eapply (weaken_ctx Γ); eauto.
Qed.

Lemma spine_subst_weaken {cf:checker_flags} Σ Γ i s Δ Γ' : 
  wf Σ.1 ->
  wf_local Σ Γ' ->
  spine_subst Σ Γ i s Δ ->
  spine_subst Σ (Γ' ,,, Γ) i s Δ.
Proof.
  move=> wfΣ wfl [cs subl].
  split; auto.
  eapply weaken_wf_local => //.
  rewrite -app_context_assoc. eapply weaken_wf_local => //.
  eapply weaken_subslet; eauto.
Qed.

Lemma weakening_wf_local {cf:checker_flags} {Σ Γ Δ} Δ' : 
  wf Σ.1 -> 
  wf_local Σ (Γ ,,, Δ) ->
  wf_local Σ (Γ ,,, Δ') ->
  wf_local Σ (Γ ,,, Δ ,,, lift_context #|Δ| 0 Δ').
Proof.
  intros wfΣ wfΔ. 
  induction Δ'; auto. 
  intros wfl. depelim wfl;
  rewrite lift_context_snoc; simpl; constructor; auto;
  red in l |- *; destruct l as [s Hs]; rewrite Nat.add_0_r.
    
  exists s.
  change (tSort s) with (lift #|Δ| #|Δ'| (tSort s)).
  eapply weakening_typing; eauto.

  exists s.
  change (tSort s) with (lift #|Δ| #|Δ'| (tSort s)).
  eapply weakening_typing; eauto.

  eapply weakening_typing; eauto.
Qed.

Lemma subslet_lift {cf:checker_flags} Σ (Γ Δ : context) s Δ' :
  wf Σ.1 -> wf_local Σ (Γ ,,, Δ) ->
  subslet Σ Γ s Δ' ->
  subslet Σ (Γ ,,, Δ) (map (lift0 #|Δ|) s) (lift_context #|Δ| 0 Δ').
Proof.
  move=> wfΣ wfl.
  induction 1; rewrite ?lift_context_snoc /=; try constructor; auto.
  simpl.
  rewrite -(subslet_length X).
  rewrite -distr_lift_subst. apply weakening; eauto.

  rewrite -(subslet_length X).
  rewrite distr_lift_subst. constructor; auto.
  rewrite - !distr_lift_subst. apply weakening; eauto.
Qed.

Lemma spine_subst_weakening {cf:checker_flags} Σ Γ i s Δ Γ' : 
  wf Σ.1 ->
  wf_local Σ (Γ ,,, Γ') ->
  spine_subst Σ Γ i s Δ ->
  spine_subst Σ (Γ ,,, Γ') (map (lift0 #|Γ'|) i) (map (lift0 #|Γ'|) s) (lift_context #|Γ'| 0 Δ).
Proof.
  move=> wfΣ wfl [cs subl].
  split; auto.
  eapply weakening_wf_local; eauto.
  now apply context_subst_lift.
  now apply subslet_lift.
Qed.

Lemma subst_telescope_cons s k d Γ : 
  subst_telescope s k (d :: Γ) = 
  map_decl (subst s k) d :: subst_telescope s (S k) Γ.
Proof.
  simpl. rewrite Nat.add_0_r; f_equal.
  unfold subst_telescope, mapi.
  rewrite mapi_rec_Sk. apply mapi_rec_ext.
  intros. simpl. now rewrite Nat.add_succ_r.
Qed.

Lemma subst_telescope_comm_rec s k s' k' Γ:
  subst_telescope (map (subst s' k) s) k' (subst_telescope s' (#|s| + k' + k) Γ) =
  subst_telescope s' (k' + k) (subst_telescope s k' Γ).
Proof.
  induction Γ in k, k' |- *; rewrite ?subst_telescope_cons; simpl; auto.
  f_equal. unfold map_decl. simpl.
  f_equal. destruct a as [na [b|] ty]; simpl; auto.
  f_equal. now rewrite distr_subst_rec.
  now rewrite distr_subst_rec.
  specialize (IHΓ k (S k')). now rewrite Nat.add_succ_r in IHΓ.
Qed.

Lemma subst_telescope_comm s k s' Γ:
  subst_telescope (map (subst s' k) s) 0 (subst_telescope s' (#|s| + k) Γ) =
  subst_telescope s' k (subst_telescope s 0 Γ).
Proof.
  now rewrite -(subst_telescope_comm_rec _ _ _ 0) Nat.add_0_r.
Qed.

Lemma ctx_inst_subst {cf:checker_flags} Σ Γ Γ0 Γ' i Δ sub : 
  wf Σ.1 ->
  ctx_inst Σ (Γ ,,, Γ0 ,,, Γ') i Δ ->
  subslet Σ Γ sub Γ0 ->
  ctx_inst Σ (Γ ,,, subst_context sub 0 Γ') (map (subst sub #|Γ'|) i) (subst_telescope sub #|Γ'| Δ).
Proof.
  move=> wfΣ ctxinst subs.
  induction ctxinst in sub, subs |- *.
  - simpl; intros; constructor; auto.
  - intros. rewrite subst_telescope_cons; simpl; constructor.
    * red in p |- *. simpl. eapply substitution; eauto.
    * specialize (IHctxinst _ subs).
      now rewrite (subst_telescope_comm [i]).
  - intros. rewrite subst_telescope_cons; simpl; constructor.
    specialize (IHctxinst _ subs).
    now rewrite (subst_telescope_comm [b]).
Qed.

Lemma ctx_inst_weaken {cf:checker_flags} Σ Γ i Δ Γ' : 
  wf Σ.1 ->
  wf_local Σ Γ' ->
  ctx_inst Σ Γ i Δ ->
  ctx_inst Σ (Γ' ,,, Γ) i Δ.
Proof.
  move=> wfΣ wfl subl.
  induction subl; constructor; auto.
  red in p |- *. now eapply (weaken_ctx Γ').
Qed.

Lemma make_context_subst_tele s s' Δ inst sub : 
  make_context_subst (subst_telescope s' #|s| Δ) inst s = Some sub ->
  make_context_subst Δ inst (s ++ s') = Some (sub ++ s').
Proof.
  induction Δ in s, s', sub, inst |- *.
  simpl. destruct inst; try discriminate.
  intros [= ->]. reflexivity.
  rewrite subst_telescope_cons.
  destruct a as [na [b|] ty]; simpl in *.
  intros. specialize (IHΔ _ _ _ _ H).
  now rewrite -subst_app_simpl in IHΔ.
  destruct inst. discriminate.
  intros. now specialize (IHΔ _ _ _ _ H).
Qed.

Fixpoint ctx_inst_sub {cf:checker_flags} {Σ Γ Δ args} (c : ctx_inst Σ Γ args Δ) {struct c} : list term :=
  match c return _ with
  | ctx_inst_nil => []
  | ctx_inst_ass na t i inst Δ P c => ctx_inst_sub c ++ [i]
  | ctx_inst_def na b t inst Δ c => ctx_inst_sub c ++ [b]
  end.

Lemma ctx_inst_sub_spec {cf:checker_flags} {Σ Γ Δ args} (c : ctx_inst Σ Γ args Δ) : 
  make_context_subst Δ args [] = Some (ctx_inst_sub c).
Proof.
  induction c; simpl; auto.
  now apply (make_context_subst_tele [] [i]) in IHc.
  apply (make_context_subst_tele [] [b]) in IHc.
  now rewrite subst_empty.
Qed.
  
Lemma subst_telescope_empty k Δ : subst_telescope [] k Δ = Δ.
Proof.
  unfold subst_telescope, mapi. generalize 0. induction Δ; simpl; auto.
  intros.
  destruct a as [na [b|] ty]; unfold map_decl at 1; simpl; rewrite !subst_empty.
  f_equal. apply IHΔ.
  f_equal. apply IHΔ.
Qed.

Lemma mapi_rec_add {A B : Type} (f : nat -> A -> B) (l : list A) (n k : nat) :
  mapi_rec f l (n + k) = mapi_rec (fun (k : nat) (x : A) => f (n + k) x) l k.
Proof.
  induction l in n, k |- *; simpl; auto.
  f_equal. rewrite (IHl (S n) k). rewrite mapi_rec_Sk.
  eapply mapi_rec_ext. intros. f_equal. lia.
Qed.

Lemma subst_telescope_app s k Γ Δ : subst_telescope s k (Γ ++ Δ) = subst_telescope s k Γ ++ 
  subst_telescope s (#|Γ| + k) Δ.
Proof.
  rewrite /subst_telescope /mapi.
  rewrite mapi_rec_app. f_equal. rewrite mapi_rec_add.
  apply mapi_rec_ext. intros. destruct x as [na [b|] ty]; simpl; f_equal; f_equal; lia.
Qed.
  
Lemma context_assumptions_subst_telescope s k Δ : context_assumptions (subst_telescope s k Δ) = 
  context_assumptions Δ.
Proof.
  rewrite /subst_telescope /mapi. generalize 0. 
  induction Δ; simpl; auto.
  destruct a as [na [b|] ty]; simpl; auto.
Qed.

Lemma subst_app_telescope s s' k Γ : 
  subst_telescope (s ++ s') k Γ = subst_telescope s k (subst_telescope s' (#|s| + k) Γ).
Proof.
  rewrite /subst_telescope /mapi.
  rewrite mapi_rec_compose.
  apply mapi_rec_ext. intros. destruct x as [na [b|] ty]; simpl; unfold map_decl; simpl; f_equal.
  rewrite subst_app_simpl. f_equal; f_equal. f_equal. lia.
  rewrite subst_app_simpl. f_equal; f_equal. lia.
  rewrite subst_app_simpl. f_equal; f_equal. lia.
Qed.

Lemma make_context_subst_length Γ args acc sub : make_context_subst Γ args acc = Some sub ->
  #|sub| = #|Γ| + #|acc|.
Proof.
  induction Γ in args, acc, sub |- *; simpl.
  destruct args; try discriminate. now intros [= ->].
  destruct a as [? [b|] ty] => /=. intros H.
  specialize (IHΓ _ _ _ H). simpl in IHΓ. lia.
  destruct args; try discriminate.
  intros H.
  specialize (IHΓ _ _ _ H). simpl in IHΓ. lia.
Qed.

Lemma subst_telescope_length s k Γ : #|subst_telescope s k Γ| = #|Γ|.
Proof.
  now rewrite /subst_telescope mapi_length.
Qed.


Lemma arity_spine_it_mkProd_or_LetIn {cf:checker_flags} Σ Γ Δ T args s args' T' : 
  wf Σ.1 ->
  spine_subst Σ Γ args s Δ ->
  arity_spine Σ Γ (subst0 s T) args' T' ->
  arity_spine Σ Γ (it_mkProd_or_LetIn Δ T) (args ++ args') T'.
Proof.
  intros wfΣ sp asp. destruct sp as [wfΓ _ cs subsl].
  move: Δ args s T cs subsl asp.
  induction Δ using ctx_length_rev_ind => args s T cs subsl asp.
  - depelim cs. depelim  subsl.
    now rewrite subst_empty in asp.
  - rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /=.
    destruct d as [na [b|] ty]; simpl in *.
    * constructor. rewrite /subst1 subst_it_mkProd_or_LetIn.
      rewrite Nat.add_0_r.
      apply subslet_app_inv in subsl as [subsl subsl'].
      depelim subsl; simpl in H0; noconf H0. depelim subsl.
      apply context_subst_app in cs as [cs cs'].
      simpl in *. rewrite skipn_0 in cs.
      specialize (X (subst_context (skipn #|Γ0| s) 0 Γ0) ltac:(now autorewrite with len) _ _ 
        (subst [b] #|Γ0| T) cs subsl').
      rewrite subst_empty in H.
      rewrite H in X. apply X.
      rewrite -subst_app_simpl'.
      apply subslet_length in subsl'.
      now autorewrite with len in subsl'.
      rewrite -H.  now rewrite firstn_skipn.
    * apply subslet_app_inv in subsl as [subsl subsl'].
      depelim subsl; simpl in H0; noconf H0. depelim subsl.
      apply context_subst_app in cs as [cs cs'].
      simpl in *.
      destruct args. depelim cs'; simpl in H; noconf H.
      depelim cs'. discriminate.
      simpl in *. rewrite skipn_S skipn_0 in cs.
      rewrite subst_empty in t0.
      depelim cs'; simpl in H; noconf H. depelim cs'. noconf H0.
      rewrite H1 in H2. noconf H2.
      constructor; auto.
      rewrite /subst1 subst_it_mkProd_or_LetIn.
      rewrite Nat.add_0_r.
      specialize (X (subst_context (skipn #|Γ0| s) 0 Γ0) ltac:(now autorewrite with len) _ _ 
      (subst [t1] #|Γ0| T) cs subsl').
      rewrite -{1}H1. apply X.
      rewrite -subst_app_simpl'.
      apply subslet_length in subsl'.
      now autorewrite with len in subsl'.
      rewrite -H1. now rewrite firstn_skipn.
Qed.


Lemma ctx_inst_app {cf:checker_flags} {Σ Γ} {Δ : context} {Δ' args} (c : ctx_inst Σ Γ args (Δ ++ Δ')) :
  ∑ (dom : ctx_inst Σ Γ (firstn (context_assumptions Δ) args) Δ),
    ctx_inst Σ Γ (skipn (context_assumptions Δ) args) (subst_telescope (ctx_inst_sub dom) 0 Δ').    
Proof.
  revert args Δ' c.
  induction Δ using ctx_length_ind; intros.
  simpl. unshelve eexists. constructor.
  simpl. rewrite skipn_0. now rewrite subst_telescope_empty.
  depelim c; simpl.
  - specialize (X (subst_telescope [i] 0 Γ0) ltac:(now rewrite /subst_telescope mapi_length)).
    rewrite subst_telescope_app in c.
    specialize (X _ _ c).
    rewrite context_assumptions_subst_telescope in X.
    destruct X as [dom codom].
    unshelve eexists.
    constructor; auto. simpl.
    pose proof (ctx_inst_sub_spec dom) as Hsub.
    simpl in *. rewrite Nat.add_0_r in codom. rewrite skipn_S.
    rewrite subst_app_telescope.
    apply make_context_subst_length in Hsub.
    rewrite subst_telescope_length Nat.add_0_r in Hsub.
    now rewrite Hsub Nat.add_0_r.
  - specialize (X (subst_telescope [b] 0 Γ0) ltac:(now rewrite /subst_telescope mapi_length)).
    rewrite subst_telescope_app in c.
    specialize (X _ _ c).
    rewrite context_assumptions_subst_telescope in X.
    destruct X as [dom codom].
    unshelve eexists.
    constructor; auto. simpl.
    pose proof (ctx_inst_sub_spec dom) as Hsub.
    simpl in *. rewrite Nat.add_0_r in codom.
    rewrite subst_app_telescope.
    apply make_context_subst_length in Hsub.
    rewrite subst_telescope_length Nat.add_0_r in Hsub.
    now rewrite Hsub Nat.add_0_r.
Qed.

Lemma ctx_inst_sub_eq {cf:checker_flags} {Σ Γ} {Δ : context} {Δ' args args'} (c : ctx_inst Σ Γ args Δ) (d : ctx_inst Σ Γ args' Δ') :
  args' = args ->
  Δ = Δ' -> ctx_inst_sub c = ctx_inst_sub d.
Proof.
  intros -> ->.
  induction c; depelim d; auto; simpl in H; noconf H.
  simpl in *. subst d0. simpl. now rewrite (IHc d).
  simpl in *. subst d0; simpl. now rewrite (IHc d).
Qed.

Lemma ctx_inst_subst_length {cf:checker_flags} {Σ Γ} {Δ : context} {args} (c : ctx_inst Σ Γ args Δ) :
  #|ctx_inst_sub c| = #|Δ|.
Proof.
  induction c; simpl; auto; try lia.
  rewrite app_length IHc subst_telescope_length /=; lia.
  rewrite app_length IHc subst_telescope_length /=; lia.
Qed.

Lemma ctx_inst_app_len {cf:checker_flags} {Σ Γ} {Δ : context} {Δ' args} (c : ctx_inst Σ Γ args (Δ ++ Δ')) :
  let (dom, codom) := ctx_inst_app c in
  ctx_inst_sub c = ctx_inst_sub codom ++ ctx_inst_sub dom.
Proof.
  destruct (ctx_inst_app c).
  induction Δ using ctx_length_ind in Δ', c, x, args, c0 |- *. simpl in *. depelim x. simpl in *.
  rewrite app_nil_r; apply ctx_inst_sub_eq. now rewrite skipn_0.
  now rewrite subst_telescope_empty.
  simpl in *. destruct d as [na [b|] ty]; simpl in *.
  depelim c; simpl in H0; noconf H0; simpl in *. subst c0; simpl.
  depelim x; simpl in H; noconf H; simpl in *.
  injection H0. discriminate. injection H0. discriminate.
  noconf H0. simpl in *.
  subst x0. simpl.
  specialize (H (subst_telescope [b] 0 Γ0) ltac:(now rewrite /subst_telescope mapi_length)).
  revert c. rewrite subst_telescope_app.
  intros c.
  specialize (H  _ _ c). simpl in *.
  revert H. rewrite context_assumptions_subst_telescope.
  intros.
  specialize (H x).
  revert c1. rewrite subst_app_telescope.
  rewrite (ctx_inst_subst_length x) subst_telescope_length.
  intros c1.
  now rewrite (H c1) app_assoc.
  
  depelim c; simpl in H0; noconf H0; simpl in *. subst c0; simpl.
  depelim x; simpl in H; noconf H; simpl in *. noconf H0; simpl in *.
  subst x0. simpl.
  specialize (H (subst_telescope [i] 0 Γ0) ltac:(now rewrite /subst_telescope mapi_length)).
  revert c. rewrite subst_telescope_app. intros c.
  specialize (H _ _ c). simpl in *.
  revert H. rewrite context_assumptions_subst_telescope.
  intros. 
  specialize (H x).
  revert c1. rewrite subst_app_telescope.
  rewrite (ctx_inst_subst_length x) subst_telescope_length.
  intros c1.
  now rewrite (H c1) app_assoc.
  noconf H0.
Qed.

Lemma context_assumptions_rev Γ : context_assumptions (List.rev Γ) = context_assumptions Γ.
Proof.
  induction Γ; simpl; auto. rewrite context_assumptions_app IHΓ /=.
  destruct (decl_body a); simpl; lia.
Qed.

Lemma ctx_inst_def {cf:checker_flags} {Σ Γ args na b t} (c : ctx_inst Σ Γ args [vdef na b t]) :
  ((args = []) * (ctx_inst_sub c = [b]))%type.
Proof.
  depelim c; simpl in H; noconf H.
  simpl in c. depelim c; simpl in *. subst c0. constructor; simpl in *; auto.
Qed.

Lemma ctx_inst_ass {cf:checker_flags} {Σ Γ args na t} (c : ctx_inst Σ Γ args [vass na t]) : 
  ∑ i, ((args = [i]) * (lift_typing typing Σ Γ i (Some t)) * (ctx_inst_sub c = [i]))%type.
Proof.
  depelim c; simpl in H; noconf H; simpl in *. subst c0.
  depelim c. exists i; constructor; auto.
Qed.

Lemma ctx_inst_spine_subst {cf:checker_flags} Σ Γ Δ args : 
  wf Σ.1 -> wf_local Σ Γ -> 
  wf_local Σ (Γ ,,, Δ) ->
  forall ci : ctx_inst Σ Γ args (List.rev Δ),
  spine_subst Σ Γ args (ctx_inst_sub ci) Δ.
Proof.
  move=> wfΣ wfΓ wfΔ ci.
  pose proof (ctx_inst_sub_spec ci) as msub.
  eapply make_context_subst_spec in msub.
  rewrite List.rev_involutive in msub.
  split; auto.
  move: ci msub.
  induction Δ in wfΔ, args |- *.
  simpl. intros ci. depelim ci. constructor.
  intros. simpl in ci.
  pose proof (ctx_inst_app_len ci).
  destruct (ctx_inst_app ci). rewrite H in msub |- *.
  clear ci H.
  simpl in c.
  apply (@context_subst_app [a]) in msub.
  simpl in msub.
  destruct a as [na [b|] ty]; simpl in *.
  - pose proof (ctx_inst_def c) as [Hargs Hinst].
    rewrite Hinst in msub |- *. simpl in *.
    destruct msub as [subl subr].
    rewrite skipn_S skipn_0 in subr.
    generalize dependent x. rewrite context_assumptions_rev.
    intros.
    depelim wfΔ; simpl in H; noconf H.
    specialize (IHΔ _ wfΔ _ subr). constructor; auto.
    red in l0. eapply (substitution _ _ _ _ []); eauto.
  - pose proof (ctx_inst_ass c) as [i [[Hargs Hty] Hinst]].
    rewrite Hinst in msub |- *. simpl in *.
    destruct msub as [subl subr].
    rewrite skipn_S skipn_0 in subr subl.
    generalize dependent x. rewrite context_assumptions_rev.
    intros.
    depelim wfΔ; simpl in H; noconf H.
    specialize (IHΔ _ wfΔ _ subr). constructor; auto.
Qed.

Lemma subst_instance_context_rev u Γ :
  subst_instance_context u (List.rev Γ) = List.rev (subst_instance_context u Γ).
Proof.
  now rewrite /subst_instance_context /map_context List.map_rev.
Qed.

Lemma subst_telescope_subst_context s k Γ :
  subst_telescope s k (List.rev Γ) = List.rev (subst_context s k Γ).
Proof.
  rewrite /subst_telescope subst_context_alt.
  rewrite rev_mapi. apply mapi_rec_ext.
  intros n [na [b|] ty] le le'; rewrite /= /subst_decl /map_decl /=; 
  rewrite List.rev_length Nat.add_0_r in le'; 
  f_equal. f_equal. f_equal. lia. f_equal; lia.
  f_equal; lia. 
Qed.

Lemma lift_context_subst_context n s Γ: lift_context n 0 (subst_context s 0 Γ) =
  subst_context s n (lift_context n 0 Γ). 
Proof.
  induction Γ in n, s |- *.
  - reflexivity.
  - rewrite !subst_context_snoc.
    rewrite !lift_context_snoc !subst_context_snoc.
    f_equal; auto.
    rewrite /lift_decl /subst_decl /map_decl.
    simpl. f_equal. unfold option_map. destruct (decl_body a).
    rewrite !subst_context_length lift_context_length Nat.add_0_r.
    rewrite commut_lift_subst_rec; auto. reflexivity.
    rewrite !subst_context_length lift_context_length Nat.add_0_r.
    rewrite commut_lift_subst_rec; auto.
Qed.

Lemma subst_app_context_gen s s' k Γ : subst_context (s ++ s') k Γ = subst_context s k (subst_context s' (k + #|s|) Γ).
Proof.
  induction Γ in k |- *; simpl; auto.
  rewrite !subst_context_snoc /= /subst_decl /map_decl /=. simpl.
  rewrite IHΓ. f_equal. f_equal.
  - destruct a as [na [b|] ty]; simpl; auto.
    f_equal. rewrite subst_context_length.
    now rewrite subst_app_simpl.
  - rewrite subst_context_length.
    now rewrite subst_app_simpl.
Qed.

Lemma closed_ctx_subst n k ctx : closedn_ctx k ctx = true -> subst_context n k ctx = ctx.
Proof.
  induction ctx in n, k |- *; auto.
  unfold closed_ctx, id.
  rewrite mapi_app forallb_app List.rev_length /= Nat.add_0_r.
  move/andb_and => /= [Hctx /andb_and [Ha _]].
  rewrite subst_context_snoc /snoc /= IHctx // subst_decl_closed //.
  now apply: closed_decl_upwards.
Qed.

Fixpoint all_rels (Γ : context) (n : nat) (k : nat) :=
  match Γ with
  | nil => nil
  | cons d vs =>
    match decl_body d with
    | Some b =>
      let s := all_rels vs (S n) k in
      (subst0 s (lift k #|s| b)) :: s
    | None => tRel n :: all_rels vs (S n) k
    end
  end.

Definition expand_lets Γ :=
  all_rels Γ 0 #|Γ|.

Lemma all_rels_length Γ n k : #|all_rels Γ n k| = #|Γ|.
Proof.
  induction Γ in n, k |- *; simpl; auto.
  now destruct a as [? [?|] ?] => /=; simpl; rewrite IHΓ. 
Qed.
   
(* Lemma all_rels_lift Γ n k : all_rels Γ n k = map (lift0 n) (all_rels Γ 0 k).
Proof.
  induction Γ in n, k |- *; simpl; auto.
  destruct a as [? [?|] ?] => /=.
  simpl.
  f_equal.
  rewrite !all_rels_length.
  rewrite (IHΓ (S n)).
  rewrite distr_lift_subst. f_equal.
  rewrite all_rels_length.
  rewrite simpl_lift //. lia. lia. admit.
  now rewrite (IHΓ n (S n')).
  simpl. rewrite {1}[n'+n]Nat.add_comm.
  f_equal. now rewrite (IHΓ n (S n')).
Qed. 

Lemma all_rels_lift Γ n n' k : all_rels Γ (n' + n) k = map (lift0 n) (all_rels Γ n' k).
Proof.
  induction Γ in n, n', k |- *; simpl; auto.
  destruct a as [? [?|] ?] => /=.
  simpl.
  f_equal.
  rewrite !all_rels_length.
  rewrite (IHΓ n (S n')).
  rewrite distr_lift_subst. f_equal.
  rewrite all_rels_length.
  rewrite simpl_lift //. lia. lia. admit.
  now rewrite (IHΓ n (S n')).
  simpl. rewrite {1}[n'+n]Nat.add_comm.
  f_equal. now rewrite (IHΓ n (S n')).
Qed.  *)

Lemma nth_error_all_rels_spec Γ n k x i : nth_error (all_rels Γ n k) i = Some x ->
  ∑ decl, (nth_error Γ i = Some decl) *
    match decl_body decl with
    | Some b => x = subst0 (all_rels (skipn (S i) Γ) (S n + i) k) (lift k (#|Γ| - S i) b)
    | None => x = tRel (n + i)
    end.
Proof.
  induction Γ in n, k, i, x |- *.
  simpl. destruct i; simpl; discriminate.
  destruct i; simpl.
  destruct a as [? [?|] ?]; simpl.
  intros [= <-].
  eexists; split; eauto. simpl.
  now rewrite skipn_S skipn_0 Nat.add_0_r Nat.sub_0_r all_rels_length.
  intros [= <-].
  eexists; split; eauto. simpl.
  now rewrite Nat.add_0_r.
  intros. destruct (decl_body a);  try discriminate.
  rewrite skipn_S. 
  specialize  (IHΓ _ _ _ _ H).
  rewrite Nat.add_succ_r. apply IHΓ.
  rewrite skipn_S. 
  specialize  (IHΓ _ _ _ _ H).
  rewrite Nat.add_succ_r. apply IHΓ.
Qed.

Lemma def_subst {cf:checker_flags} Σ Γ t :
  wf Σ.1 -> wf_local Σ Γ ->
  forall n b, option_map decl_body (nth_error Γ n) = Some (Some b) ->
  Σ ;;; Γ |- t = subst [b] (S n) (lift 1 n t).
Proof.
  intros.
  apply red_conv.
  rewrite -{1}Nat.add_1_r.
  rewrite -commut_lift_subst_rec. lia.
  induction t.
  simpl.
  destruct (leb_spec_Set n n0).
  destruct (eq_dec n0 n). subst.
  rewrite Nat.sub_diag.
  simpl.
  rewrite simpl_lift; try lia.
  simpl. unshelve eapply (red_rel (fst_ctx Σ)) in H; eauto.
  assert(n < n0) by lia.
  assert(n0 - n = S (Nat.pred n0 - n)) by lia.
  rewrite H1 /=. rewrite nth_error_nil.
  simpl. destruct (leb_spec_Set n (n0 -1)).
  assert(S (n0 -1) = n0) as -> by lia.
  constructor. lia.
  simpl.
  simpl. destruct (leb_spec_Set n n0). lia. constructor.
  constructor.
Admitted.  

Lemma rel_subst {cf:checker_flags} Σ Γ t :
  wf Σ.1 -> wf_local Σ Γ ->
  forall n, option_map decl_body (nth_error Γ n) = Some None ->
  Σ ;;; Γ |- t = subst [tRel 0] n (lift 1 (S n) t).
Proof.
  intros.
  apply red_conv.
  induction t.
  simpl.
  destruct (leb_spec_Set (S n) n0).
  cbn -[minus].
  destruct (leb_spec_Set n (S n0)).
  destruct (eq_dec (S n0 - n) 0). rewrite e.
  simpl. f_equal; lia.
  edestruct (nth_error_None [tRel 0]).
  rewrite H1. simpl. destruct n; lia.
  simpl. f_equal. rewrite Nat.sub_0_r. constructor.
  lia.
  simpl.

  destruct (leb_spec_Set n n0).
  assert(n0 - n = 0) by lia. rewrite H0.
  simpl. assert (n0 = n) by lia.
  subst n0. rewrite Nat.add_0_r. constructor.
  constructor.
Admitted.
(* 
Lemma all_rels_subst {cf:checker_flags} Σ Δ Γ Δ' t :
  wf Σ.1 -> wf_local Σ (Γ ,,, Δ) ->
  Σ ;;; Γ ,,, Δ ,,, Δ' |- lift0 #|Δ'| t =
   subst0 (all_rels Δ #|Δ'| (#|Δ| + #|Δ'|)) (lift (#|Δ| + #|Δ'|) #|Δ| t).
Proof.
  intros.
  apply red_conv.
  remember (all_rels Δ _ _) as s.
  pose proof (all_rels_length Δ #|Δ'| (#|Δ| + #|Δ'|)).
  rewrite -Heqs in H.
  induction s. simpl in H.
  rewrite -H. simpl. now rewrite subst_empty.
  simpl in H.
  rewrite (subst_app_simpl [a] s). simpl.
  simpl. 
 *)

Require Import PCUICParallelReductionConfluence.

Lemma subst_lift_lift s k t : subst0 (map (lift0 k) s) (lift k #|s| t) = lift0 k (subst0 s t).
Proof.
  now rewrite (distr_lift_subst_rec _ _ _ 0 0).
Qed.
Hint Rewrite all_rels_length : len.

Lemma all_rels_lift (Δ : context) n : all_rels Δ n (n + #|Δ|) = map (lift0 n) (all_rels Δ 0 #|Δ|).
Proof.
  rewrite -{1}(Nat.add_0_r n).
  generalize 0 at 1 3. revert n.
  induction Δ at 1 3.
  simpl. auto.
  intros n n'.
  destruct a as [na [?|] ?]. simpl.
  f_equal.
  specialize (IHc n (S n')).
  rewrite Nat.add_succ_r in IHc.
  rewrite {1}IHc.
  rewrite all_rels_length.
  assert(#|all_rels c (S n') #|Δ| | = #|c|) by now autorewrite with len.
  rewrite -(simpl_lift _ _ _ _ #|c|); try lia.
  rewrite -{1}H.
  epose proof (distr_lift_subst _ _ n 0).
  rewrite Nat.add_0_r in H0. now erewrite <-H0.
  specialize (IHc n (S n')).
  now rewrite -IHc.
  simpl.
  f_equal.
  specialize (IHc n (S n')).
  now rewrite -IHc.
Qed.

Lemma all_rels_subst {cf:checker_flags} Σ Δ Γ t :
  wf Σ.1 -> wf_local Σ (Γ ,,, Δ) ->
  red Σ.1 (Γ ,,, Δ) t (subst0 (all_rels Δ 0 #|Δ|) (lift #|Δ| #|Δ| t)).
Proof.
  intros wfΣ wf.
  induction t using term_forall_ctx_list_ind.
  simpl.
  destruct (leb_spec_Set #|Δ| n); simpl; rewrite Nat.sub_0_r.
  * destruct (nth_error_spec (all_rels Δ 0 #|Δ|) (#|Δ| + n));
    rewrite all_rels_length in l0 |- *. lia.
    assert (#|Δ| + n - #|Δ| = n) as -> by lia.
    constructor.
  * destruct (nth_error_spec (all_rels Δ 0 #|Δ|) n);
    rewrite all_rels_length in l0 |- *; try lia.
    eapply nth_error_all_rels_spec in e.
    destruct e as [decl [Hnth Hdecl]].
    destruct decl as [? [?|] ?]; simpl in Hdecl; subst x;
    rewrite lift0_id. 2:auto.
    etransitivity.
    eapply red1_red. constructor.
    rewrite nth_error_app_lt; auto.
    rewrite Hnth. reflexivity.
    rewrite -{1 3 4}(firstn_skipn (S n) Δ).
    rewrite app_context_assoc.
    assert (Hf:#|firstn (S n) Δ| = S n) by now rewrite firstn_length_le; lia.
    rewrite app_length Hf.
    rewrite all_rels_lift.

    erewrite <-(simpl_lift _ _ _ _ #|skipn (S n) Δ|); try lia.
  
    epose proof (distr_lift_subst (lift #|skipn (S n) Δ| (#|Δ| - S n) t) 
     (all_rels (skipn (S n) Δ) 0 #|skipn (S n) Δ|) (S n) 0).
    rewrite Nat.add_0_r in H.
    autorewrite with len in H.
    rewrite -{}H.
    rewrite -{3 4}Hf.
    eapply (weakening_red _ _ []); auto. simpl.
    rewrite skipn_length. lia.
    simpl.
    admit.
    rewrite skipn_length; lia.

  * simpl. constructor.
  * simpl.   
    
Admitted.


Lemma all_rels_subst_lift {cf:checker_flags} Σ Δ Γ Δ' t :
  wf Σ.1 -> wf_local Σ (Γ ,,, Δ) ->
  Σ ;;; Γ ,,, Δ ,,, Δ' |- lift0 #|Δ'| t =
   subst0 (all_rels Δ #|Δ'| (#|Δ| + #|Δ'|)) (lift (#|Δ| + #|Δ'|) #|Δ| t).
Proof.
  intros.
  rewrite Nat.add_comm.
  erewrite <-(simpl_lift _ _ _ _ #|Δ|); try lia.
  rewrite all_rels_lift.
  epose proof (distr_lift_subst (lift #|Δ| #|Δ| t) (all_rels Δ 0 #|Δ|) #|Δ'| 0).
  rewrite Nat.add_0_r in H.
  rewrite -{2}(all_rels_length Δ 0 #|Δ|).
  rewrite -H.
  apply red_conv.
  eapply (weakening_red _ _ []); auto. clear H.
  simpl.
  eapply all_rels_subst; auto.
Qed.

Lemma app_tip_assoc {A} (l : list A) x l' : (l ++ [x]) ++ l' = l ++ (x :: l').
Proof. now rewrite -app_assoc. Qed.

Lemma spine_subst_to_extended_list_k {cf:checker_flags} Σ Δ Γ :
  wf Σ.1 -> wf_local Σ (Γ ,,, Δ) ->
  spine_subst Σ (Γ ,,, Δ) (reln [] 0 Δ) (all_rels Δ 0 #|Δ|)
    (lift_context #|Δ| 0 Δ).
Proof.
  move=> wfΣ wf.
  split; auto.
  apply weakening_wf_local; auto.
  clear wf.
  generalize 0 at 2 3.
  induction Δ at 2 3 4; intros n; rewrite ?lift_context_snoc0; simpl; auto.
  destruct a as [na [?|] ?]  => /=;
  rewrite /lift_decl /= /map_decl /=.
  specialize (IHc (S n)).
  eapply (context_subst_def _ _ _ _ (lift #|Δ| (#|c| + 0) t)) in IHc.
  rewrite Nat.add_1_r.
  rewrite all_rels_length.
  rewrite Nat.add_0_r in IHc |- *.
  apply IHc.
  rewrite reln_acc.
  constructor.
  specialize (IHc (S n)).
  now rewrite Nat.add_1_r.

  generalize (@eq_refl _ Δ).
  change Δ with ([] ++ Δ) at 1.
  change 0 with (length (@nil context_decl)) at 1.
  generalize (@nil context_decl).
  induction Δ at 1 4 7; rewrite /= => l eql.
  - constructor.
  - specialize (IHc (l ++ [a])).
    rewrite -app_assoc in IHc. specialize (IHc eql).
    destruct a as [na [?|] ?]  => /=;
    rewrite lift_context_snoc /lift_decl /map_decl /=.
    * rewrite app_length /= Nat.add_1_r in IHc. 
      rewrite all_rels_length Nat.add_0_r.
      constructor; auto.
      assert (Some (Some t) = option_map decl_body (nth_error Δ #|l|)).
      destruct (nth_error_spec Δ #|l|).
      rewrite -eql in e.
      rewrite nth_error_app_ge in e. lia.
      rewrite Nat.sub_diag in e. simpl in e. noconf e. simpl. reflexivity.
      rewrite -eql in l0. autorewrite with len in l0. simpl  in l0. lia.
      eapply (substitution _ _ _ _ [] _ _ _ IHc); auto.
      simpl.
      pose proof wf as wf'.
      rewrite -eql in wf'.
      rewrite app_context_assoc in wf'.
      apply wf_local_app in wf'. depelim wf'; simpl in H0; noconf H0.
      eapply (weakening_typing); auto.
    * rewrite app_length /= Nat.add_1_r in IHc.
      constructor; auto.
    
      pose proof wf as wf'.
      rewrite -eql in wf'.
      rewrite app_context_assoc in wf'.
      apply wf_local_app in wf'. depelim wf'; simpl in H; noconf H.
      rewrite Nat.add_0_r.

      eapply type_Cumul.
      constructor. auto.
      rewrite -eql.
      rewrite nth_error_app_lt.
      rewrite app_length /=. lia.
      rewrite nth_error_app_ge //.
      rewrite Nat.sub_diag //.
      destruct l0.
      right; exists x.
      change (tSort x) with  
        (subst0 (all_rels c (S #|l|) #|Δ|) (lift #|Δ| #|c| (tSort x))).
      { eapply (substitution _ _ (lift_context #|Δ| 0 c) _ []); simpl; auto.
        change (tSort x) with (lift #|Δ| #|c| (tSort x)).
        eapply (weakening_typing _ _ c); eauto. }
      eapply conv_cumul. simpl.
      rewrite -{1}eql. simpl.
      rewrite !app_context_assoc.
      rewrite /app_context !app_assoc.
      
      epose proof (all_rels_subst_lift Σ c Γ 
      (l ++ [{|decl_name := na; decl_body := None; decl_type := decl_type0|}]) decl_type0).
      assert (#|Δ| = #|c| + S #|l|).
      { rewrite -eql. autorewrite with len. simpl. lia. }
      rewrite H. rewrite app_length /= in X.
      rewrite Nat.add_1_r in X.
      unfold app_context in X.
      rewrite !app_tip_assoc /= in X.
      rewrite -app_assoc.
      apply X; auto.
Qed.

Lemma subst_context_decompo s s' Γ k : 
  subst_context (s ++ s') k Γ =
  subst_context s' k (subst_context (map (lift0 #|s'|) s) k Γ).
Proof.
  intros.
  rewrite !subst_context_alt !mapi_compose.
  apply mapi_ext => i x.
  destruct x as [na [b|] ty] => //.
  - rewrite /subst_decl /map_decl /=; f_equal.
    + rewrite !mapi_length. f_equal.
      now rewrite subst_app_decomp.
    + rewrite mapi_length.
      now rewrite subst_app_decomp.
  - rewrite /subst_decl /map_decl /=; f_equal.
    rewrite !mapi_length. now rewrite subst_app_decomp.
Qed.

Lemma compose_map_decl f g x : map_decl f (map_decl g x) = map_decl (f ∘ g) x.
Proof.
  destruct x as [? [?|] ?]; reflexivity.
Qed.

Lemma map_decl_ext f g x : f =1 g -> map_decl f x = map_decl g x.
Proof.
  intros H; destruct x as [? [?|] ?]; rewrite /map_decl /=; f_equal; auto.
  now rewrite (H t).
Qed.

Lemma subst_instance_lift_context u n k Γ : 
  subst_instance_context u (lift_context n k Γ) = lift_context n k (subst_instance_context u Γ).
Proof.
  rewrite /subst_instance_context /map_context !lift_context_alt.
  rewrite map_mapi mapi_map. apply mapi_rec_ext.
  intros. rewrite /lift_decl !compose_map_decl. apply map_decl_ext => ?.
  rewrite map_length. now rewrite lift_subst_instance_constr.
Qed.

Lemma subst_lift_above s n k x : k = #|s| -> subst0 s (lift0 (n + k) x) = lift0 n x.
Proof.
  intros. rewrite Nat.add_comm. subst k. now rewrite simpl_subst.
Qed.

Lemma lift_to_extended_list_k n Γ : map (lift n #|Γ|) (to_extended_list_k Γ 0) = 
  to_extended_list_k Γ 0.
Proof.
  rewrite /to_extended_list_k.
  change [] with (map (lift n #|Γ|) []) at 2.
  rewrite -(Nat.add_0_r #|Γ|).
  generalize 0.
  move:(@nil term).
  induction Γ; simpl; auto.
  intros l n'.
  destruct a as [? [?|] ?].
  specialize (IHΓ l (S n')).
  rewrite Nat.add_succ_r in IHΓ.
  now rewrite Nat.add_1_r IHΓ.
  specialize (IHΓ (tRel n' :: l) (S n')).
  rewrite Nat.add_succ_r in IHΓ.
  rewrite Nat.add_1_r IHΓ. simpl.
  destruct (leb_spec_Set (S (#|Γ| + n')) n'). lia.
  reflexivity.
Qed.
 
Lemma reln_subst acc s Γ k : 
  reln (map (subst s (k + #|Γ|)) acc) k (subst_context s 0 Γ) = 
  map (subst s (k + #|Γ|)) (reln acc k Γ).
Proof.
  induction Γ in acc, s, k |- *; simpl; auto.
  rewrite subst_context_snoc.
  simpl.
  destruct a as [? [?|] ?]; simpl in *.
  specialize (IHΓ acc s (S k)).
  rewrite Nat.add_succ_r !Nat.add_1_r -IHΓ.
  f_equal.
  specialize (IHΓ (tRel k :: acc) s (S k)).
  rewrite Nat.add_succ_r !Nat.add_1_r -IHΓ.
  f_equal.
  simpl.
  destruct (leb_spec_Set (S (k + #|Γ|)) k). lia.
  reflexivity.
Qed.

Lemma subst_context_telescope s k Γ : subst_context s k Γ = List.rev (subst_telescope s k (List.rev Γ)).
Proof.
  now rewrite subst_telescope_subst_context List.rev_involutive.
Qed.

Lemma ctx_inst_sub_to_extended_list_k {cf:checker_flags} Σ Γ args Δ : 
  forall inst : ctx_inst Σ Γ args Δ,
  map (subst0 (ctx_inst_sub inst)) (to_extended_list_k (List.rev Δ) 0) = args.
Proof.
  induction inst; simpl; auto.
  rewrite reln_app. simpl.
  have len := ctx_inst_subst_length inst0.
  rewrite subst_telescope_length in len.
  rewrite List.rev_length.
  f_equal.
  rewrite nth_error_app_ge. lia.
  assert(#|Δ| + 0 - 0 - #|ctx_inst_sub inst0| = 0) as -> by lia.
  cbn. apply lift0_id.
  rewrite -{2}IHinst.
  rewrite -map_subst_app_simpl.
  rewrite -map_map_compose. f_equal.
  simpl. unfold to_extended_list_k.
  epose proof (reln_subst [] [i] (List.rev Δ) 0). simpl in H.
  rewrite subst_context_telescope in H.
  rewrite List.rev_involutive in H. rewrite H.
  now rewrite List.rev_length len.

  rewrite reln_app. simpl.
  have len := ctx_inst_subst_length inst0.
  rewrite subst_telescope_length in len.
  rewrite -{2}IHinst.
  rewrite -map_subst_app_simpl.
  rewrite -map_map_compose. f_equal.
  simpl. unfold to_extended_list_k.
  epose proof (reln_subst [] [b] (List.rev Δ) 0). simpl in H.
  rewrite subst_context_telescope in H.
  rewrite List.rev_involutive in H. rewrite H.
  now rewrite List.rev_length len.
Qed.

Lemma reln_lift n k Γ : reln [] (n + k) Γ = map (lift0 n) (reln [] k Γ).
Proof.
  induction Γ in n, k |- *; simpl; auto.
  destruct a as [? [?|] ?]; simpl.
  now rewrite -IHΓ Nat.add_assoc.
  rewrite reln_acc  [reln [tRel k] _ _]reln_acc map_app /=.
  f_equal. now rewrite -IHΓ Nat.add_assoc.
Qed.

Lemma spine_subst_subst_to_extended_list_k {cf:checker_flags} {Σ Γ args s Δ} : 
  spine_subst Σ Γ args s Δ ->
  map (subst0 s) (to_extended_list_k Δ 0) = args.
Proof.
  intros [_ _ sub _].
  rewrite /to_extended_list_k.
  rewrite -(map_lift0 args).
  generalize 0 at 1 2 3.
  induction sub; simpl; auto.
  intros n.
  rewrite reln_acc.
  rewrite !map_app.
  simpl. rewrite Nat.leb_refl Nat.sub_diag /=.
  simpl.
  f_equal. rewrite -IHsub.
  rewrite reln_lift.
  rewrite (reln_lift 1).
  rewrite -{4}(Nat.add_0_r n).
  rewrite (reln_lift n 0).
  rewrite !map_map_compose.
  apply map_ext.
  intros x. unfold compose.
  rewrite (subst_app_decomp [a] s).
  f_equal. simpl.
  rewrite -(commut_lift_subst_rec _ _ _ 0)  //.
  rewrite simpl_subst_k //.

  intros n.
  rewrite -IHsub.
  rewrite reln_lift.
  rewrite (reln_lift 1).
  rewrite -{4}(Nat.add_0_r n).
  rewrite (reln_lift n 0).
  rewrite !map_map_compose.
  apply map_ext.
  intros x. unfold compose.
  rewrite (subst_app_decomp [subst0 s b] s).
  f_equal. simpl.
  rewrite -(commut_lift_subst_rec _ _ _ 0)  //.
  rewrite simpl_subst_k //.
Qed.

Lemma mapi_rec_ext (f g : nat -> context_decl -> context_decl) (l : context) n k' :
  closedn_ctx k' l ->
  (forall k x, n <= k -> k < length l + n -> 
    closed_decl (k' + #|l|) x ->
    f k x = g k x) ->
  mapi_rec f l n = mapi_rec g l n.
Proof.
  intros cl Hfg.
  induction l in n, cl, Hfg |- *; simpl; try congruence.
  intros. rewrite Hfg; simpl; try lia.
  simpl in cl. rewrite mapi_rec_app /= forallb_app in cl.
  move/andP: cl => [cll clr]. simpl in clr. unfold id in clr.
  rewrite List.rev_length in clr. rewrite Nat.add_0_r in clr.
  move/andP : clr => [clr _]. eapply closed_decl_upwards; eauto. lia.
  f_equal.
  rewrite IHl; auto.
  simpl in cl. rewrite mapi_rec_app /= forallb_app in cl.
  move/andP: cl => [cll _]. simpl in cll.
  apply cll.
  intros. apply Hfg. simpl; lia. simpl. lia. simpl.
  eapply closed_decl_upwards; eauto. lia.
Qed.

Lemma map_decl_ext' f g k d : closed_decl k d -> 
  (forall x, closedn k x -> f x = g x) -> 
  map_decl f d = map_decl g d.
Proof.
  destruct d as [? [?|] ?] => /= cl Hfg;
  unfold map_decl; simpl; f_equal.
  rewrite Hfg => //. unfold closed_decl in cl.
  simpl in cl. now move/andP: cl => []. 
  move/andP: cl => [cl cl']. now rewrite Hfg.
  now rewrite Hfg.
Qed.


Lemma to_extended_list_k_fold_context f Γ k : 
  to_extended_list_k (fold_context f Γ) k = to_extended_list_k Γ k.
Proof.
  rewrite /to_extended_list_k.
  generalize (@nil term).
  induction Γ in k |- *.
  simpl; auto.
  intros.
  rewrite fold_context_snoc0. simpl.
  destruct a as [? [?|] ?] => /=; now rewrite IHΓ.  
Qed.

Lemma simpl_map_lift x n k :
   map (lift0 n ∘ lift0 k) x = 
  map (lift k n ∘ lift0 n) x.
Proof.
  apply map_ext => t.
  rewrite simpl_lift => //. lia.
  rewrite simpl_lift; try lia.
  now rewrite Nat.add_comm.
Qed.

Lemma spine_subst_eq {cf:checker_flags} {Σ Γ inst s Δ Δ'} : 
  spine_subst Σ Γ inst s Δ ->
  Δ = Δ' ->
  spine_subst Σ Γ inst s Δ'.
Proof.
  now intros sp ->.
Qed.

Lemma All2_eq_eq {A} (l l' : list A) : l = l' -> All2 (fun x y => x = y) l l'.
Proof.
  intros ->. induction l';  constructor; auto.
Qed.

Lemma lift_context_lift_context n k Γ : lift_context n 0 (lift_context k 0 Γ) =
  lift_context (n + k) 0 Γ.
Proof. rewrite !lift_context_alt.
  rewrite mapi_compose.
  apply mapi_ext.
  intros n' x.
  rewrite /lift_decl compose_map_decl.
  apply map_decl_ext => y.
  rewrite mapi_length; autorewrite with  len.
  rewrite simpl_lift. lia. lia. reflexivity.
Qed.

Lemma distr_lift_subst_context n k s Γ : lift_context n k (subst_context s 0 Γ) =
  subst_context (map (lift n k) s) 0 (lift_context n (#|s| + k) Γ).
Proof.
  rewrite !lift_context_alt !subst_context_alt.
  rewrite !mapi_compose.
  apply mapi_ext.
  intros n' x.
  rewrite /lift_decl /subst_decl !compose_map_decl.
  apply map_decl_ext => y.
  rewrite !mapi_length; autorewrite with len.
  rewrite Nat.add_0_r.
  rewrite distr_lift_subst_rec. f_equal. f_equal. lia.
Qed.


Lemma closed_ctx_lift n k ctx : closedn_ctx k ctx -> lift_context n k ctx = ctx.
Proof.
  induction ctx in n, k |- *; auto.
  unfold closed_ctx, id. rewrite lift_context_snoc.
  simpl.
  rewrite mapi_rec_app forallb_app List.rev_length /= /snoc Nat.add_0_r.
  move/andb_and => /= [Hctx /andb_and [Ha _]].
  f_equal. rewrite lift_decl_closed. apply: closed_decl_upwards; eauto. lia. 
  reflexivity.
  rewrite IHctx // lift_decl_closed //. 
Qed.

Lemma map_lift_lift n k l : map (fun x => lift0 n (lift0 k x)) l = map (lift0 (n + k)) l.
Proof. apply map_ext => x.
  rewrite simpl_lift; try lia. reflexivity.
Qed.

Lemma arity_spine_eq {cf:checker_flags} Σ Γ T T' :
  isWfArity_or_Type Σ Γ T' ->
T = T' -> arity_spine Σ Γ T [] T'.
Proof. intros H  ->; constructor;auto. reflexivity. Qed.

Lemma map_subst_lift_id_eq s l k : k = #|s| -> map (subst0 s ∘ lift0 k) l = l.
Proof. intros ->; apply map_subst_lift_id. Qed.

Lemma build_branches_type_red {cf:checker_flags} (p p' : term) (ind : inductive)
	(mdecl : PCUICAst.mutual_inductive_body)
    (idecl : PCUICAst.one_inductive_body) (pars : list term) 
    (u : Instance.t) (brtys : list (nat × term)) Σ Γ :
  wf Σ ->
  red1 Σ Γ p p' ->
  map_option_out (build_branches_type ind mdecl idecl pars u p) = Some brtys ->
  ∃ brtys' : list (nat × term),
    map_option_out (build_branches_type ind mdecl idecl pars u p') =
    Some brtys' × All2 (on_Trel_eq (red1 Σ Γ) snd fst) brtys brtys'.
Proof.
  intros wfΣ redp.
  unfold build_branches_type.
  unfold mapi.
  generalize 0 at 3 6.
  induction (ind_ctors idecl) in brtys |- *. simpl.
  intros _ [= <-]. exists []; split; auto.
  simpl. intros n.
  destruct a. destruct p0.
  destruct (instantiate_params (subst_instance_context u (PCUICAst.ind_params mdecl))
  pars
  (subst0 (inds (inductive_mind ind) u (PCUICAst.ind_bodies mdecl))
     (subst_instance_constr u t))).
  destruct decompose_prod_assum.
  destruct chop.
  destruct map_option_out eqn:Heq.
  specialize (IHl _ _ Heq).
  destruct IHl. intros [= <-].
  exists ((n0,
  PCUICAst.it_mkProd_or_LetIn c
    (mkApps (lift0 #|c| p')
       (l1 ++
        [mkApps (tConstruct ind n u) (l0 ++ PCUICAst.to_extended_list c)]))) :: x).
  destruct p0 as [l' r'].
  rewrite {}l'.
  split; auto.
  constructor; auto. simpl. split; auto.
  2:discriminate. clear Heq.
  2:discriminate.
  eapply red1_it_mkProd_or_LetIn.
  eapply red1_mkApps_f.
  eapply (weakening_red1 Σ Γ [] c) => //.
Qed.


Lemma OnOne2_All2_All2 (A : Type) (l1 l2 l3 : list A) (R1 R2 R3  : A -> A -> Type) :
  OnOne2 R1 l1 l2 ->
  All2 R2 l1 l3 ->
  (forall x y, R2 x y -> R3 x y) ->
  (forall x y z : A, R1 x y -> R2 x z -> R3 y z) ->
  All2 R3 l2 l3.
Proof.
  intros o. induction o in l3 |- *.
  intros H; depelim H.
  intros Hf Hf'. specialize (Hf'  _ _ _ p r). constructor; auto.
  eapply All2_impl; eauto.
  intros H; depelim H.
  intros Hf. specialize (IHo _ H Hf).
  constructor; auto.
Qed.

Lemma OnOne2_All_All (A : Type) (l1 l2 : list A) (R1  : A -> A -> Type) (R2 R3 : A -> Type) :
  OnOne2 R1 l1 l2 ->
  All R2 l1 ->
  (forall x, R2 x -> R3 x) ->
  (forall x y : A, R1 x y -> R2 x -> R3 y) ->
  All R3 l2.
Proof.
  intros o. induction o.
  intros H; depelim H.
  intros Hf Hf'. specialize (Hf' _ _ p r). constructor; auto.
  eapply All_impl; eauto.
  intros H; depelim H.
  intros Hf. specialize (IHo H Hf).
  constructor; auto.
Qed.

Lemma context_relation_refl P : (forall Δ x, P Δ Δ x x) ->
  forall Δ, context_relation P Δ Δ.
Proof.
  intros HP.
  induction Δ.
   constructor; auto.
   destruct a as [? [?|] ?]; constructor; auto.
Qed.

Lemma conv_decls_fix_context_gen {cf:checker_flags} Σ Γ mfix mfix1 :
  wf Σ.1 ->
  All2 (fun d d' => conv Σ Γ d.(dtype) d'.(dtype)) mfix mfix1 ->
  forall Γ' Γ'',
  conv_context Σ (Γ ,,, Γ') (Γ ,,, Γ'') ->
  context_relation (fun Δ Δ' : PCUICAst.context => conv_decls Σ (Γ ,,, Γ' ,,, Δ) (Γ ,,, Γ'' ,,, Δ'))
    (fix_context_gen #|Γ'| mfix) (fix_context_gen #|Γ''| mfix1).
Proof.    
  intros wfΣ.
  induction 1. constructor. simpl.
  intros Γ' Γ'' convctx.

  assert(conv_decls Σ (Γ ,,, Γ' ,,, []) (Γ ,,, Γ'' ,,, [])
  (PCUICAst.vass (dname x) (lift0 #|Γ'| (dtype x)))
  (PCUICAst.vass (dname y) (lift0 #|Γ''| (dtype y)))).
  { constructor.
  pose proof (context_relation_length _ _ _  convctx).
  rewrite !app_length in H. assert(#|Γ'|  = #|Γ''|) by lia.
  rewrite -H0.
  apply (weakening_conv _ _ []); auto. }

  apply context_relation_app_inv. rewrite !List.rev_length; autorewrite with len.
  rewrite !mapi_rec_length.
  now apply All2_length in X.
  constructor => //. constructor. 
  eapply (context_relation_impl (P:= (fun Δ Δ' : PCUICAst.context =>
  conv_decls Σ
  (Γ ,,, (vass (dname x) (lift0 #|Γ'| (dtype x)) :: Γ') ,,, Δ)
  (Γ ,,, (vass (dname y) (lift0 #|Γ''| (dtype y)) :: Γ'') ,,, Δ')))).
  intros. now rewrite !app_context_assoc.
  eapply IHX. simpl.
  constructor => //.
Qed.

Lemma assumption_context_fix_context_gen k Γ : assumption_context (fix_context_gen k Γ).
Proof.
  rewrite /fix_context_gen. revert k.
  induction Γ using rev_ind.
  constructor. intros.
  rewrite mapi_rec_app /= List.rev_app_distr /=. constructor.
  apply IHΓ.
Qed.

Lemma All_local_env_fix_OnOne2_gen {cf:checker_flags} Σ P Q R Γ mfix mfix1 :
  wf Σ.1 ->
  (forall (Γ' Γ'' Δ Δ': context) (t : term) (T : option term),
    conv_context Σ (Γ ,,, Γ' ,,, Δ) (Γ ,,, Γ'' ,,, Δ') ->
    lift_typing P Σ (Γ ,,, Γ' ,,, Δ) t T ->
    All_local_env (lift_typing (fun Σ Δ => R Σ (Γ ,,, Δ)) Σ) (Γ''  ,,, Δ') ->
    lift_typing R Σ (Γ ,,, Γ'' ,,, Δ') t T) ->
  (forall hd hd', Q hd hd' -> conv Σ Γ (dtype hd) (dtype hd')) ->
  (forall Γ' Γ'' hd hd', Q hd hd' ->
    conv_context Σ (Γ ,,, Γ') (Γ ,,, Γ'') ->
    All_local_env (lift_typing (fun Σ Δ => R Σ (Γ ,,, Δ)) Σ) Γ'' ->
    lift_typing P Σ (Γ ,,, Γ') (lift0 #|Γ'| (dtype hd)) None ->
    lift_typing R Σ (Γ ,,, Γ'') (lift0 #|Γ'| (dtype hd')) None
    ) -> 
  OnOne2 Q mfix mfix1 ->
  forall Γ' Γ'',
  conv_context Σ (Γ ,,, Γ') (Γ ,,, Γ'') ->
  All_local_env (lift_typing R Σ) (Γ ,,, Γ'') ->
  All_local_env (lift_typing (fun Σ Δ => P Σ (Γ ,,, Γ' ,,, Δ)) Σ) (fix_context_gen #|Γ'| mfix) ->
  All_local_env (lift_typing (fun Σ Δ => R Σ (Γ ,,, Γ'' ,,, Δ)) Σ) (fix_context_gen #|Γ'| mfix1).
Proof.    
  intros wfΣ PR Qconv QPR o.
  induction o; intros Γ' Γ'' convctx wfΓ' a'.
  simpl in a' |- *.
  apply All_local_env_app in a' as [r r'].
  depelim r; simpl in H; noconf H.
  apply All_local_env_app_inv. split.
  constructor. constructor. simpl.
  apply All_local_env_app in wfΓ' as [wfΓ wfΓ'].
  eapply (QPR _ _ _ _ p convctx wfΓ' l).
  revert r'. fold (fix_context_gen (S #|Γ'|) tl).
  generalize (assumption_context_fix_context_gen (S #|Γ'|) tl).
  generalize (fix_context_gen (S #|Γ'|) tl).
  induction 2.
  - constructor.
  - forward IHr'. now depelim H; simpl in H0; noconf H0. auto.
    constructor; auto.
    unfold  lift_typing in PR, t0 |- *.
    simpl. eapply (PR _ _ _ _ _ None). 2:eapply t0.
    apply context_relation_app_inv; simpl; auto.
    now rewrite !app_context_length.
    apply context_relation_app_inv; simpl; auto.
    constructor. constructor. constructor.
    apply (weakening_conv _ _ []); auto.
    apply context_relation_refl. intros.
    destruct x as [? [?|] ?]; constructor; apply conv_refl'.
    eapply All_local_env_app_inv.
    split; auto. now apply All_local_env_app in wfΓ' as [? ?].
    eapply All_local_env_app_inv.
    split; auto.
    constructor. constructor. 
    apply All_local_env_app in wfΓ' as [wfΓ wfΓ'].
    apply (QPR _ _ _ _ p convctx wfΓ' l).
    eapply All_local_env_impl. eapply  IHr'.
    simpl; intros. unfold lift_typing in X.
    now rewrite app_context_assoc.
    
  - elimtype False. depelim H; simpl in H0; noconf H0.

  - simpl in a'.
    apply All_local_env_app in a' as [r r'].
    depelim r; simpl in H; noconf H.
    simpl.
    apply All_local_env_app_inv. split.
    constructor. constructor. simpl.
    unfold lift_typing in PR. eapply (PR _ _ [] [] _ None); eauto.
    now apply All_local_env_app in wfΓ' as [? ?].

    specialize (IHo (Γ' ,,, [PCUICAst.vass (dname hd) (lift0 #|Γ'| (dtype hd))])
      (Γ'' ,,, [vass (dname hd) (lift0 #|Γ''| (dtype hd))])).
    simpl in IHo.
    assert (#|Γ'| = #|Γ''|).
    move/context_relation_length: convctx. rewrite !app_context_length; lia.
    forward IHo. constructor. auto.
    constructor. 
    rewrite  -H.
    apply (weakening_conv _ _ []); auto.
    forward IHo.
    constructor. apply wfΓ'. rewrite -H. unfold lift_typing in l |- *.
    eapply (PR _ _ [] [] _ None); eauto.
    now apply All_local_env_app in wfΓ' as [? ?].

    eapply All_local_env_impl; [eapply IHo|].
    unfold lift_typing. intros *. 
    eapply All_local_env_impl. eapply r'.
    simpl; intros. unfold lift_typing in X |- *.
    rewrite !app_context_assoc in X. apply X.
    unfold lift_typing. intros *.
    now rewrite !app_context_assoc -H. 
Qed.

Lemma All_local_env_fix_OnOne2 {cf:checker_flags} Σ P Q R Γ mfix mfix1 :
  wf Σ.1 ->
  (forall (Γ' Γ'' Δ Δ': context) (t : term) (T : option term),
  conv_context Σ (Γ ,,, Γ' ,,, Δ) (Γ ,,, Γ'' ,,, Δ') ->
  lift_typing P Σ (Γ ,,, Γ' ,,, Δ) t T ->
  All_local_env (lift_typing (fun Σ Δ => R Σ (Γ ,,, Δ)) Σ) (Γ''  ,,, Δ') ->
  lift_typing R Σ (Γ ,,, Γ'' ,,, Δ') t T) ->
  (forall hd hd', Q hd hd' -> conv Σ Γ (dtype hd) (dtype hd')) ->
  (forall Γ' Γ'' hd hd', Q hd hd' ->
    conv_context Σ (Γ ,,, Γ') (Γ ,,, Γ'') ->
    All_local_env (lift_typing (fun Σ Δ => R Σ (Γ ,,, Δ)) Σ) Γ'' ->
    lift_typing P Σ (Γ ,,, Γ') (lift0 #|Γ'| (dtype hd)) None ->
    lift_typing R Σ (Γ ,,, Γ'') (lift0 #|Γ'| (dtype hd')) None
    ) -> 
  OnOne2 Q mfix mfix1 ->
  All_local_env (lift_typing R Σ) Γ ->
  All_local_env (lift_typing (fun Σ Δ => P Σ (Γ ,,, Δ)) Σ) (fix_context mfix) ->
  All_local_env (lift_typing (fun Σ Δ => R Σ (Γ ,,, Δ)) Σ) (fix_context mfix1).
Proof.    
  intros wfΣ PR Qconv QPR o wfΓ.
  have H:= (All_local_env_fix_OnOne2_gen Σ P Q R Γ mfix mfix1 wfΣ PR Qconv QPR o [] []).
  apply H. apply conv_ctx_refl. assumption.
Qed.
  
Lemma conv_decls_fix_context {cf:checker_flags} Σ Γ mfix mfix1 :
  wf Σ.1 ->
  All2 (fun d d' => conv Σ Γ d.(dtype) d'.(dtype)) mfix mfix1 ->
  context_relation (fun Δ Δ' : PCUICAst.context => conv_decls Σ (Γ ,,, Δ) (Γ ,,, Δ'))
    (fix_context mfix) (fix_context mfix1).
Proof.    
  intros wfΣ a.
  apply (conv_decls_fix_context_gen _ _  _ _ wfΣ a [] []).
  apply conv_ctx_refl. 
Qed.

Lemma OnOne2_nth_error Σ Γ mfix mfix' n decl :
  OnOne2
  (fun x y : def term =>
  red1 Σ Γ (dtype x) (dtype y)
  × (dname x, dbody x, rarg x) = (dname y, dbody y, rarg y)) mfix mfix' ->        
  nth_error mfix n = Some decl ->
  ∑ decl', (nth_error mfix' n = Some decl') *
  ((dname decl, dbody decl, rarg decl) = (dname decl', dbody decl', rarg decl')) *
  ((dtype decl = dtype decl') + (red1 Σ Γ (dtype decl) (dtype decl'))).
Proof.
  induction 1 in n |- *.
  destruct n; simpl.
  - intros [= ->]. exists hd'; intuition auto.
  - exists decl. intuition auto.
  - destruct n; simpl; auto.
    intros [= ->]. exists decl; intuition auto.
Qed.

(** The subject reduction property of the system: *)

Definition SR_red1 {cf:checker_flags} (Σ : global_env_ext) Γ t T :=
  forall u (Hu : red1 Σ Γ t u), Σ ;;; Γ |- u : T.

Lemma sr_red1 {cf:checker_flags} : allow_cofix = false -> 
  env_prop SR_red1
      (fun Σ Γ wfΓ =>
        All_local_env_over typing (fun  Σ Γ _ t T _ => SR_red1 Σ Γ t T) Σ Γ wfΓ).
Proof.
  intros allow_cofix.
  apply typing_ind_env; intros Σ wfΣ Γ wfΓ; unfold SR_red1; intros **; rename_all_hyps; auto;
    match goal with
    | [H : (_ ;;; _ |- _ <= _) |- _ ] => idtac
    | _ =>
      depelim Hu; try solve [apply mkApps_Fix_spec in x; noconf x];
      try solve [econstructor; eauto] ;
      try solve [
        match goal with
        | h : _ = mkApps _ ?args |- _ =>
          let e := fresh "e" in
          apply (f_equal nApp) in h as e ; simpl in e ;
          rewrite nApp_mkApps in e ; simpl in e ;
          destruct args ; discriminate
        end
      ]
    end.

  - (* Rel *)
    rewrite heq_nth_error in e. destruct decl as [na b ty]; noconf e.
    simpl.
    pose proof (nth_error_All_local_env_over heq_nth_error X); eauto.
    destruct lookup_wf_local_decl; cbn in *.
    rewrite <- (firstn_skipn (S n) Γ).
    eapply weakening_length; auto.
    { rewrite firstn_length_le; auto. apply nth_error_Some_length in heq_nth_error. auto with arith. }
    now unfold app_context; rewrite firstn_skipn.
    apply o.

  - (* Prod *)
    constructor; eauto.
    eapply (context_conversion _ wf _ _ _ typeb).
    constructor; auto with pcuic.
    constructor; auto. exists s1; auto.

  - (* Lambda *)
    eapply type_Cumul. eapply type_Lambda; eauto.
    eapply (context_conversion _ wf _ _ _ typeb).
    constructor; auto with pcuic.
    constructor; auto. exists s1; auto.
    assert (Σ ;;; Γ |- tLambda n t b : tProd n t bty). econstructor; eauto.
    edestruct (validity _ wf _ _ _ X0). apply i.
    eapply cumul_red_r.
    apply cumul_refl'. constructor. apply Hu.

  - (* LetIn body *)
    eapply type_Cumul.
    apply (substitution_let _ Γ n b b_ty b' b'_ty wf typeb').
    specialize (typing_wf_local typeb') as wfd.
    assert (Σ ;;; Γ |- tLetIn n b b_ty b' : tLetIn n b b_ty b'_ty). econstructor; eauto.
    edestruct (validity _ wf _ _ _ X0). apply i.
    eapply cumul_red_r.
    apply cumul_refl'. constructor.

  - (* LetIn value *)
    eapply type_Cumul.
    econstructor; eauto.
    eapply (context_conversion _ wf _ _ _ typeb').
    constructor. auto with pcuic. constructor; eauto. constructor; auto.
    now exists s1. red. auto.
    assert (Σ ;;; Γ |- tLetIn n b b_ty b' : tLetIn n b b_ty b'_ty). econstructor; eauto.
    edestruct (validity _ wf _ _ _ X0). apply i.
    eapply cumul_red_r.
    apply cumul_refl'. now constructor.

  - (* LetIn type annotation *)
    specialize (forall_u _ Hu).
    eapply type_Cumul.
    econstructor; eauto.
    eapply type_Cumul. eauto. right; exists s1; auto.
    apply red_cumul; eauto.
    eapply (context_conversion _ wf _ _ _ typeb').
    constructor. auto with pcuic. constructor; eauto. constructor; auto.
    exists s1; auto. red; eauto.
    eapply type_Cumul. eauto. right. exists s1; auto. eapply red_cumul. now eapply red1_red.
    assert (Σ ;;; Γ |- tLetIn n b b_ty b' : tLetIn n b b_ty b'_ty). econstructor; eauto.
    edestruct (validity _ wf _ _ _ X0). apply i.
    eapply cumul_red_r.
    apply cumul_refl'. now constructor.

  - (* Application *)
    eapply substitution0; eauto.
    pose proof typet as typet'.
    eapply inversion_Lambda in typet' as [s1 [B' [Ht [Hb HU]]]]=>//.
    apply cumul_Prod_inv in HU as [eqA leqB] => //.
    destruct (validity _ wf _ _ _ typet).

    eapply type_Cumul; eauto.
    unshelve eapply (context_conversion _ wf _ _ _ Hb); eauto with wf.
    constructor. auto with pcuic. constructor ; eauto.
    constructor; auto with pcuic. red; eauto.
    eapply isWAT_tProd in i as [Hs _]; auto.
    eapply isWAT_tProd in i as [_ Hs]; intuition auto.

  - (* Fixpoint unfolding *)
    assert (args <> []) by (destruct args; simpl in *; congruence).
    apply mkApps_inj in H as [-> Hu]; auto.
    rewrite mkApps_nonempty; auto.
    epose (last_nonempty_eq H0). rewrite <- Hu in e1. rewrite <- e1.
    clear e1.
    specialize (type_mkApps_inv _ _ _ _ _ wf typet) as [T' [U' [[appty spty] Hcumul]]].
    specialize (validity _ wf _ _ _ appty) as [_ vT'].
    eapply type_tFix_inv in appty as [T [arg [fn' [[Hnth Hty]]]]]; auto.
    rewrite e in Hnth. noconf Hnth.
    eapply type_App.
    eapply type_Cumul.
    eapply type_mkApps. eapply type_Cumul; eauto. eapply spty.
    eapply validity; eauto.
    eauto. eauto.

  - (* Congruence *)
    eapply type_Cumul; [eapply type_App| |]; eauto with wf.
    eapply validity. eauto. eauto.
    eapply type_App; eauto. eapply red_cumul_inv.
    eapply (red_red Σ Γ [vass na A] [] [u] [N2]); auto.
    constructor. constructor.

  - (* Constant unfolding *)
    unshelve epose proof (declared_constant_inj decl decl0 _ _); tea; subst decl.
    destruct decl0 as [ty body' univs]; simpl in *; subst body'.
    eapply on_declared_constant in H; tas; cbn in H.
    rewrite <- (app_context_nil_l Γ).
    apply typecheck_closed in H as H'; tas.
    destruct H' as [_ H']. apply andb_and in H'.
    replace (subst_instance_constr u body)
      with (lift0 #|Γ| (subst_instance_constr u body)).
    replace (subst_instance_constr u ty)
      with (lift0 #|Γ| (subst_instance_constr u ty)).
    2-3: rewrite lift_subst_instance_constr lift_closed; cbnr; apply H'.
    eapply weakening; tea.
    now rewrite app_context_nil_l.
    eapply typing_subst_instance_decl with (Γ0:=[]); tea.

  - (* iota reduction *)
    subst npar.
    clear forall_u forall_u0 X X0.
    pose proof typec as typec''.
    unfold iota_red. rename args into iargs. rename args0 into cargs.
    pose proof typec as typec'.
    eapply inversion_mkApps in typec as [A [U [tyc [tyargs tycum]]]]; auto.
    eapply (inversion_Construct Σ wf) in tyc as [mdecl' [idecl' [cdecl' [wfl [declc [Hu tyc]]]]]].
    unshelve eapply Construct_Ind_ind_eq in typec'; eauto.
    unfold on_declared_constructor in typec'.
    destruct declc as [decli declc].
    unfold on_declared_inductive in typec'.
    destruct declared_constructor_inv as [cs [Hnth onc]].
    simpl in typec'.
    destruct (declared_inductive_unique isdecl decli) as []; subst mdecl' idecl'.
    set(oib := declared_inductive_inv _ _ _ _ _ _ _ _ _) in *. clearbody oib.
    eapply (build_branches_type_lookup _  Γ ind mdecl idecl cdecl' _ _ _ brs) in heq_map_option_out; eauto.
    2:{ eapply All2_impl; eauto. simpl; intuition eauto. }
    unshelve eapply build_case_predicate_type_spec in heq_build_case_predicate_type as 
      [parsubst [csubst ptyeq]]. 2:exact oib. subst pty.
    destruct heq_map_option_out as [nargs [br [brty [[[Hbr Hbrty] brbrty] brtys]]]].
    unshelve eapply (branch_type_spec Σ.1) in brtys; auto.
    destruct (PCUICParallelReductionConfluence.nth_nth_error (@eq_refl _ (nth c0 brs (0, tDummy)))) => //.
    assert (H : ∑ t', nth_error btys c0 = Some t').
    pose proof (All2_length _ _ X5). eapply nth_error_Some_length in e. rewrite H in e.
    destruct (nth_error_spec btys c0). eexists; eauto. elimtype False; lia.
    destruct H as [t' Ht'].
    rewrite Hbr in e. noconf e. simpl in H. rewrite <- H. simpl.  
    clear H.
    destruct brtys as [-> ->].
    eapply type_mkApps. eauto.
    set argctx := cshape_args (cshape onc).
    clear Hbr brbrty Hbrty X5 Ht'.
    destruct typec' as [[[[_ equ] cu] eqargs] [cparsubst [cargsubst [iparsubst [iidxsubst ci]]]]].
    destruct ci as ((([cparsubst0 iparsubst0] & idxsubst0) & subsidx) & [s [typectx [Hpars Hargs]]]).
    pose proof (context_subst_fun csubst (iparsubst0.(inst_ctx_subst))). subst iparsubst.
    assert(leq:Σ ;;; Γ |- (it_mkProd_or_LetIn
    (subst_context parsubst 0
       (subst_context (inds (inductive_mind ind) u (ind_bodies mdecl))
          #|ind_params mdecl| (map_context (subst_instance_constr u) argctx)))
    (mkApps ((lift0 #|argctx|) p)
       (map
          (fun x : term =>
           subst parsubst #|argctx|
             (subst (inds (inductive_mind ind) u (ind_bodies mdecl))
                (#|argctx| + #|ind_params mdecl|) (subst_instance_constr u x)))
          (cshape_indices onc.(cshape)) ++
        [mkApps (tConstruct ind c0 u)
           (map (lift0 #|argctx|) (firstn (PCUICAst.ind_npars mdecl) iargs) ++
            to_extended_list 
              (subst_context parsubst 0
              (subst_context (inds (inductive_mind ind) u (ind_bodies mdecl))
                 #|ind_params mdecl| (map_context (subst_instance_constr u) argctx))))])))
           <=
    (it_mkProd_or_LetIn
     (subst_context cparsubst 0
        (subst_context (inds (inductive_mind ind) u1 (ind_bodies mdecl))
           #|ind_params mdecl| (map_context (subst_instance_constr u1) argctx)))
     (mkApps ((lift0 #|argctx|) p)
        (map
           (fun x : term =>
            subst cparsubst #|argctx|
              (subst (inds (inductive_mind ind) u1 (ind_bodies mdecl))
                 (#|argctx| + #|ind_params mdecl|) (subst_instance_constr u1 x)))
           (cshape_indices onc.(cshape)) ++
         [mkApps (tConstruct ind c0 u1)
            (map (lift0 #|argctx|) (firstn (PCUICAst.ind_npars mdecl) cargs) ++
             to_extended_list 
             (subst_context cparsubst 0
             (subst_context (inds (inductive_mind ind) u1 (ind_bodies mdecl))
                #|ind_params mdecl| (map_context (subst_instance_constr u1) argctx))))])))).
    { pose proof (subslet_inds _ _ u _ _ wf isdecl cu).
      pose proof (subslet_inds _ _ u1 _ _ wf ⋆ ⋆).
      assert(wfpararms : wf_local Σ (subst_instance_context u (ind_params mdecl))).
      { eapply (on_minductive_wf_params _ mdecl); intuition eauto. eapply isdecl. }
      assert(closed_ctx (subst_instance_context u (ind_params mdecl)) = true).
      { eapply closed_wf_local; eauto. }
      assert (closed_ctx (subst_instance_context u1 (ind_params mdecl)) = true).
      { eapply closed_wf_local; eauto.
        eapply (on_minductive_wf_params _ mdecl); intuition eauto.
        eapply isdecl. }
     assert(subslet Σ Γ (parsubst ++ inds (inductive_mind ind) u (ind_bodies mdecl))
        (subst_instance_context u
          (arities_context (ind_bodies mdecl) ,,, ind_params mdecl))).
      { rewrite subst_instance_context_app. eapply subslet_app.
        rewrite closed_ctx_subst; pcuic.
        eapply (weaken_subslet _  _ _ _ []) => //; eauto. }
      assert(subslet Σ Γ (cparsubst ++ inds (inductive_mind ind) u1 (ind_bodies mdecl))
        (subst_instance_context u1
          (arities_context (ind_bodies mdecl) ,,, ind_params mdecl))).
      { rewrite subst_instance_context_app. eapply subslet_app.
        rewrite closed_ctx_subst; pcuic.
        eapply (weaken_subslet _ _ _ _ []) => //; eauto. }
      assert (lenipar := context_subst_length _ _ _ iparsubst0).
      rewrite subst_instance_context_length in lenipar. 
      assert (lencpar := context_subst_length _ _ _ cparsubst0).
      rewrite subst_instance_context_length in lencpar. 
      assert (All2 (conv Σ Γ) (parsubst ++ inds (inductive_mind ind) u (ind_bodies mdecl))
        (cparsubst ++ inds (inductive_mind ind) u1 (ind_bodies mdecl))).
      { eapply All2_app.
        * eapply spine_subst_conv; eauto.
          eapply context_relation_subst_instance; eauto.
          now rewrite closedn_subst_instance_context in H.
          now symmetry.
        * now apply conv_inds. }
      pose proof (on_declared_inductive wf isdecl) as [onind _].
      eapply cumul_it_mkProd_or_LetIn => //.
      clear csubst. subst argctx.
      rewrite {1}lenipar. rewrite {1}lencpar.
      clear lenipar lencpar.
      rewrite - !subst_app_context.

      eapply (context_relation_subst _ 
        (subst_instance_context u (arities_context (ind_bodies mdecl) ,,, ind_params mdecl))
        (subst_instance_context u1 (arities_context (ind_bodies mdecl) ,,, ind_params mdecl))); eauto with pcuic.
      rewrite -app_context_assoc - [subst_instance_context _ _ ,,, _]subst_instance_context_app.
      apply weaken_wf_local => //.
      eapply on_constructor_inst; pcuic.
      - do 2 rewrite - [subst_instance_context _ _ ,,, _]subst_instance_context_app.
        eapply context_relation_subst_instance => //.
        eapply on_constructor_inst; pcuic.
        now symmetry.
      - apply conv_cumul.
        apply mkApps_conv_args => //. apply conv_refl'.
        eapply All2_app.
        eapply All2_map. eapply All2_refl. intros x.
        rewrite {1 2}lenipar.
        rewrite -subst_app_simpl. rewrite lencpar.
        rewrite -subst_app_simpl. rewrite -subst_app_context.
        rewrite -(subst_instance_context_length u argctx).
        eapply subst_conv => //; eauto.
        rewrite -app_context_assoc - [subst_instance_context _ _ ,,, _]subst_instance_context_app.
        apply weaken_wf_local => //.
        eapply on_constructor_inst; pcuic.
        rewrite -app_context_assoc - [subst_instance_context _ _ ,,, _]subst_instance_context_app.
        constructor.
        apply eq_term_upto_univ_subst_instance_constr; try typeclasses eauto.
        now symmetry.
        constructor. 2:constructor.
        apply mkApps_conv_args => //.
        do 2 constructor. now symmetry.
        apply All2_app.
        * eapply All2_map.
          eapply All2_impl. 
          apply All2_sym. eapply Hpars.
          simpl. intros x y conv.
          eapply (weakening_conv_gen _ Γ []); auto.
          now autorewrite with len. now symmetry.
        * set (r := (subst_context cparsubst _ _)).
          rewrite (to_extended_list_eq _ r). subst r.
          do 2 apply same_ctx_shape_subst.
          apply same_ctx_shape_map. apply same_ctx_shape_refl.
          apply All2_refl.
          intros. reflexivity. }
    unshelve eapply typing_spine_strengthen. 4:eapply leq. all:auto.
    clear leq. 
    set(cindices := map
    (fun x : term =>
     subst cparsubst #|argctx|
       (subst (inds (inductive_mind ind) u1 (ind_bodies mdecl))
          (#|argctx| + #|ind_params mdecl|)
          (subst_instance_constr u1 x)))
    (cshape_indices onc.(cshape))) in *.
    
    eapply (typing_spine_weaken_concl (S:=
      (mkApps p (map (subst0 cargsubst) cindices ++ [mkApps (tConstruct ind c0 u1) cargs])))) => //.
    2:{ eapply conv_cumul; auto.
        eapply mkApps_conv_args; auto with pcuic.
        eapply All2_app; auto with pcuic.
        unfold cindices. rewrite !map_map_compose.
        eapply All2_trans. eapply conv_trans. auto.
        2:eauto. eapply All2_map. eapply All2_refl. intros x.
        rewrite subst_app_simpl. simpl.
        pose proof (context_subst_length _ _ _ idxsubst0).
        autorewrite with len in H. rewrite H. reflexivity. }
    eapply typing_spine_it_mkProd_or_LetIn_close_eq; eauto.
    * eapply make_context_subst_spec_inv. rewrite List.rev_involutive.
      apply idxsubst0.
    * pose proof (on_declared_minductive _ (declared_inductive_minductive _ _ _ _ decli)) as onmind.
      pose proof (onNpars _ _ _ _ onmind).
      pose proof (context_assumptions_length_bound (ind_params mdecl)).
      rewrite skipn_length; try lia.
      rewrite !context_assumptions_subst subst_instance_context_assumptions.
      rewrite eqargs. auto with arith.
    * apply idxsubst0.
    * right.
      pose proof (on_declared_inductive wf isdecl) as [onmind _].
      destruct (on_constructor_subst' _ _ _ _ _ _ wf isdecl onmind oib onc) as [[wfext wfc] insts].
      (* eapply (spine_subst_inst _ _ u1) in insts.
      2:{ eapply consistent_instance_ext_eq; eauto. now symmetry. }
      rewrite !subst_instance_context_app map_app in insts.
      eapply spine_subst_app_inv in insts as [instl instr]. 2:auto.
      2:{ rewrite map_length to_extended_list_k_length. now autorewrite with len. } *)
      eexists.
      assert(wfparinds : wf_local Σ
        (Γ ,,, subst_instance_context u (ind_params mdecl) ,,,
          subst_instance_context u (ind_indices oib))). 
      admit.
      assert(wfparinds' : wf_local Σ
        (Γ ,,, subst_instance_context u1 (ind_params mdecl) ,,,
          subst_instance_context u1 (ind_indices oib))).
      admit.
      assert(wfparu : wf_local Σ (subst_instance_context u (ind_params mdecl))). 
      { eapply on_minductive_wf_params; eauto. destruct decli; eauto. }
      assert(wfparu1 : wf_local Σ (subst_instance_context u1 (ind_params mdecl))). 
      { eapply on_minductive_wf_params; eauto. destruct decli; eauto. }
      eapply type_it_mkProd_or_LetIn; eauto. 
      eapply type_mkApps.
      assert (Σ ;;; Γ |- p : 
      PCUICAst.it_mkProd_or_LetIn
      (subst_context cparsubst 0
         (subst_instance_context u1 (ind_indices oib)))
      (tProd (nNamed (PCUICAst.ind_name idecl))
         (mkApps (tInd ind u1)
            (map (lift0 #|ind_indices oib|)
               (firstn (PCUICAst.ind_npars mdecl) cargs) ++
             PCUICAst.to_extended_list (ind_indices oib))) 
         (tSort ps))).
      { eapply type_Cumul. eauto. left.
        eexists _, ps. rewrite destArity_it_mkProd_or_LetIn.
        simpl. split. reflexivity. rewrite app_context_nil_l. simpl.
        constructor.
        eapply substitution_wf_local; eauto. eapply cparsubst0 => //.
        red. admit.
        eapply cumul_it_mkProd_or_LetIn => //.
        eapply context_relation_subst => //. 2:eapply iparsubst0. 2:eapply cparsubst0. auto.
        eapply spine_subst_conv; eauto. eapply context_relation_subst_instance; eauto.
        now symmetry. now symmetry.
        rewrite - !subst_instance_context_app.
        eapply context_relation_subst_instance; eauto.
        eapply on_minductive_wf_params_indices_inst => //. destruct decli; eauto.
        now symmetry.
        eapply congr_cumul_prod.
        eapply mkApps_conv_args => //.
        constructor. constructor. now symmetry.
        apply All2_app. eapply All2_map.
        apply All2_sym. eapply All2_impl. eauto. simpl.
        intros x y Hx. eapply (weakening_conv_gen _ _ []) => //.
        now autorewrite with len. now apply conv_sym.
        eapply All2_refl. intros x. reflexivity. apply cumul_refl'. }  
      clear typep.
      eapply weakening_gen in X. eauto.
      now autorewrite with len. auto. 
      eapply type_local_ctx_wf_local in typectx; auto.
      unfold to_extended_list.
      rewrite !to_extended_list_k_subst.
      rewrite PCUICSubstitution.map_subst_instance_constr_to_extended_list_k.
      rewrite lift_it_mkProd_or_LetIn.
      subst cindices.
      simpl.
      assert (closed_ctx (subst_instance_context u1 (ind_params mdecl)) = true).
      { eapply closed_wf_local; eauto. }
      assert (lencpar := context_subst_length _ _ _ cparsubst0).
      rewrite subst_instance_context_length in lencpar. rewrite lencpar.
      
      eapply (ctx_inst_inst _ _ u1) in insts.
      2:{ eapply consistent_instance_ext_eq; eauto. now symmetry. }
      rewrite !subst_instance_context_app in insts.
      eapply (ctx_inst_weaken _ _ _ _ Γ) in insts => //.
      rewrite app_context_assoc in insts.
      eapply ctx_inst_subst in insts => //.
      2:{ eapply subslet_app. 2:{ eapply (weaken_subslet _ _ _ _ []) => //. eapply subslet_inds => //. pcuic. }
          rewrite closed_ctx_subst => //. eapply cparsubst0. }
      rewrite subst_app_context in insts.
      rewrite subst_instance_context_rev in insts.
      rewrite subst_telescope_subst_context in insts.
      autorewrite with len in insts. simpl in insts.
      epose proof (ctx_inst_spine_subst _ _  _ _ wf _  _ insts) as instsp.
      rewrite {2}subst_instance_lift_context in instsp.
      rewrite -lift_context_subst_context in instsp.
      rewrite subst_app_context in instsp.
      assert(closedind : closedn_ctx #|ind_params mdecl| (subst_instance_context u1 (ind_indices oib))).
      unshelve epose proof (on_minductive_wf_params_indices _ _ _ _ _ _ oib); simpl; auto.
      destruct decli; auto.
      eapply closed_wf_local in X. rewrite closedn_ctx_app in X.
      move/andP: X => [_ X]. now rewrite closedn_subst_instance_context.
      simpl;  auto.
      rewrite (closed_ctx_subst _ _ (subst_instance_context u1 (ind_indices oib))) in instsp.    
      now rewrite -lencpar.
      
      assert((map (subst (cparsubst ++ inds (inductive_mind ind) u1 (PCUICAst.ind_bodies mdecl)) #|cshape_args (cshape onc)|)
      (map (subst_instance_constr u1) (cshape_indices (cshape onc)))) = 
      (map
      (fun x : term =>
      subst cparsubst #|argctx|
        (subst (inds (inductive_mind ind) u1 (ind_bodies mdecl)) (#|argctx| + #|cparsubst|) (subst_instance_constr u1 x)))
     (cshape_indices (cshape onc)))).
      rewrite map_map_compose. apply map_ext=> x.
      unfold Basics.compose. now rewrite subst_app_simpl.
      rewrite H0 in insts, instsp. clear H0.
      apply wf_arity_spine_typing_spine => //.
      split.
      ** left.
         eexists _, _.
         rewrite destArity_it_mkProd_or_LetIn /=. split; [reflexivity|].
         rewrite app_context_nil_l. simpl.         
         constructor; auto. apply (spine_codom_wf _ _ _ _ _ instsp).
         red.
         autorewrite with len; rewrite Nat.add_0_r.
         rewrite lift_mkApps /=.
         rewrite !map_app !map_map_compose.
         exists (subst_instance_univ u1 (ind_sort oib)).
         eapply type_mkApps. econstructor; eauto.
         apply (spine_codom_wf _ _ _ _ _ instsp).
         apply wf_arity_spine_typing_spine => //.
         split.
         destruct (oib.(onArity)) as [s' Hs].
         eapply (instantiate_minductive _ _ _ u1) in Hs; eauto.
         2:pcuic. right; exists (subst_instance_univ u1 s'). red.
         eapply weaken_ctx in Hs. simpl in Hs. eauto. auto.
         now eapply spine_codom_wf.
         
         rewrite oib.(ind_arity_eq).
         rewrite subst_instance_constr_it_mkProd_or_LetIn.
         eapply arity_spine_it_mkProd_or_LetIn; eauto.
         { set (foo:=map (lift #|argctx| #|ind_indices oib| ∘ lift0 #|ind_indices oib|)
            cparsubst).
          clear -instsp wf cparsubst0 H.
          eapply (spine_subst_weakening _ _ _ _ _ (subst_context cparsubst 0
            (subst_context (inds (inductive_mind ind) u1 (ind_bodies mdecl))
              #|cparsubst| (map_context (subst_instance_constr u1) argctx)))) in cparsubst0; auto.
          rewrite closed_ctx_lift in cparsubst0 => //.
          autorewrite with len in cparsubst0.
          eapply (spine_subst_weakening _ _ _ _ _
            (lift_context #|argctx| 0
              (subst_context cparsubst 0 (subst_instance_context u1 (ind_indices oib)))))
              in cparsubst0 => //.
          autorewrite with len in cparsubst0.
          rewrite (closed_ctx_lift #|ind_indices oib|) in cparsubst0 => //.
          rewrite !map_map_compose in cparsubst0.
          rewrite - !simpl_map_lift. apply cparsubst0.
          apply (spine_codom_wf _ _ _ _ _ instsp).
          apply (spine_dom_wf _ _ _ _ _ instsp). }
        rewrite subst_instance_constr_it_mkProd_or_LetIn subst_it_mkProd_or_LetIn.
        simpl.
        rewrite lift_to_extended_list_k.
        rewrite -(app_nil_r (to_extended_list_k _ _)).
        eapply arity_spine_it_mkProd_or_LetIn; [auto|auto|constructor].
        assert ((subst_context
        (map
           (fun x : term =>
            lift #|argctx| #|ind_indices oib| (lift0 #|ind_indices oib| x))
           cparsubst) 0 (subst_instance_context u1 (ind_indices oib))) = 
          (lift_context #|ind_indices oib| 0
           (lift_context #|argctx| 0
            (subst_context cparsubst 0 (subst_instance_context u1 (ind_indices oib)))))).
        { rewrite -simpl_map_lift.
          rewrite lift_context_lift_context distr_lift_subst_context.
          rewrite map_lift_lift. f_equal.
          rewrite closed_ctx_lift -?lencpar ?Nat.add_0_r; auto. }
        rewrite simpl_map_lift.
        rewrite H0.
        have sps := spine_subst_to_extended_list_k Σ (lift_context #|argctx| 0
        (subst_context cparsubst 0 (subst_instance_context u1 (ind_indices oib)))).
        autorewrite with len in sps.
        rewrite [reln _ _ _]to_extended_list_k_fold_context in sps.
        rewrite to_extended_list_k_fold_context in sps.
        rewrite PCUICSubstitution.map_subst_instance_constr_to_extended_list_k in sps.
        apply sps; auto.
        apply (spine_codom_wf _ _ _ _ _ instsp).
        left; eexists _, _; split;  simpl; eauto.
        apply (spine_codom_wf _ _ _ _ _ instsp).
        reflexivity.

      ** eapply arity_spine_it_mkProd_or_LetIn; eauto.
         simpl. rewrite -(app_nil_r [mkApps _ _]).
         constructor; [|constructor].
         2:{ left; eexists _, _; simpl; split; eauto. apply (spine_dom_wf _ _ _ _ _ instsp). }
         2:{ simpl; reflexivity. }
         rewrite lift_mkApps subst_mkApps /=.
         autorewrite with len.
         eapply type_mkApps. econstructor; eauto; pcuic.
         apply (spine_dom_wf _ _ _ _ _ instsp).
         simpl.
         apply wf_arity_spine_typing_spine => //.
         split.
         epose proof (declared_constructor_valid_ty _ _ _ _ _ _ _ u1 wf (spine_dom_wf _ _ _ _ _ instsp) _ Hu).
         right; eauto.
         
         unfold type_of_constructor.
         rewrite {1}onc.(cshape).(cshape_eq).
         rewrite subst_instance_constr_it_mkProd_or_LetIn subst_it_mkProd_or_LetIn.
         eapply arity_spine_it_mkProd_or_LetIn; eauto.
         rewrite (closed_ctx_subst (inds _ _ _) 0) => //.
         rewrite -(closed_ctx_lift #|argctx| 0 (subst_instance_context u1 (ind_params mdecl))) => //.
         eapply (spine_subst_weakening _ _ _ _ _ (subst_context cparsubst 0
         (subst_context (inds (inductive_mind ind) u1 (ind_bodies mdecl))
            #|cparsubst| (map_context (subst_instance_constr u1) argctx)))) in cparsubst0; auto.
         autorewrite with len in cparsubst0. apply cparsubst0.
         eapply (spine_dom_wf _ _ _ _ _ instsp).
         rewrite subst_instance_constr_it_mkProd_or_LetIn !subst_it_mkProd_or_LetIn.
         autorewrite with len.
         rewrite subst_instance_constr_mkApps !subst_mkApps.
         rewrite -(app_nil_r (to_extended_list_k argctx 0)).
         eapply arity_spine_it_mkProd_or_LetIn; auto.
         *** have sps := spine_subst_to_extended_list_k Σ 
           ( subst_context cparsubst 0
           (subst_context (inds (inductive_mind ind) u1 (ind_bodies mdecl))
              #|cparsubst| (map_context (subst_instance_constr u1) argctx))) Γ wf
              (spine_dom_wf _ _ _ _ _ instsp)
              .
              autorewrite with len in sps.
              rewrite [reln _ _ _]to_extended_list_k_fold_context in sps.
              rewrite to_extended_list_k_fold_context in sps.
              rewrite PCUICSubstitution.map_subst_instance_constr_to_extended_list_k in sps.
              eapply (spine_subst_eq sps).
              rewrite distr_lift_subst_context.
              rewrite !Nat.add_0_r -lencpar. rewrite closed_ctx_lift => //.
              eapply (wf_local_instantiate _ (InductiveDecl mdecl) _ u1) in wfc; eauto.
              2:{ destruct decli; eauto.  }
              clear -wf wfc isdecl Hu. rewrite !subst_instance_context_app in wfc.
              epose proof (substitution_wf_local Σ [] (subst_instance_context u1 (arities_context (ind_bodies mdecl)))).
              specialize (X (inds (inductive_mind ind) u1 (ind_bodies mdecl))
                (subst_instance_context u1 (ind_params mdecl) ,,, (map_context (subst_instance_constr u1) argctx)) wf).
              rewrite app_context_nil_l in X.
              forward X by eapply subslet_inds; eauto.
              rewrite app_context_assoc in X.
              specialize(X wfc). rewrite app_context_nil_l in X.
              eapply closed_wf_local in X; eauto.
              rewrite subst_context_app in X.
              rewrite closedn_ctx_app in X.
              autorewrite with len in X. simpl in X. rewrite Nat.add_0_r in X.
              now move/andP: X => [_ X].
          *** rewrite !map_map_compose !map_app.
              assert ((map (subst0 (ctx_inst_sub insts) ∘ lift #|argctx| #|ind_indices oib| ∘ lift0 #|ind_indices oib|)
                (firstn (PCUICAst.ind_npars mdecl) cargs)) = 
              map (lift #|argctx| 0) (firstn (PCUICAst.ind_npars mdecl) cargs)).
              { apply map_ext => x. 
                rewrite simpl_lift => //. lia.
                rewrite subst_lift_above => //.
                rewrite (ctx_inst_subst_length insts); auto.
                now rewrite List.rev_length; autorewrite with len. }
              rewrite !Nat.add_0_r !map_map_compose {}H0.
              assert ((map (subst0 (ctx_inst_sub insts) ∘ lift #|argctx| #|ind_indices oib|)
                (to_extended_list_k (ind_indices oib) 0)) = 
              (map
              (fun x : term =>
                subst cparsubst #|argctx|
                  (subst (inds (inductive_mind ind) u1 (ind_bodies mdecl))
                    (#|argctx| + #|cparsubst|) (subst_instance_constr u1 x)))
              (cshape_indices (cshape onc)))).
              { rewrite -map_map_compose.
                rewrite lift_to_extended_list_k.
                pose proof (ctx_inst_sub_to_extended_list_k _ _ _ _ insts).
                rewrite List.rev_involutive in H0.
                rewrite to_extended_list_k_subst in H0.
                rewrite PCUICSubstitution.map_subst_instance_constr_to_extended_list_k in H0.
                rewrite /lift_context to_extended_list_k_fold_context in H0.
                rewrite H0. reflexivity. }
              rewrite {}H0.
              constructor.
              { right. exists (subst_instance_univ u1 (ind_sort oib)).
                eapply type_mkApps. econstructor; eauto.
                apply (spine_dom_wf _ _ _ _ _ instsp).
                destruct (oib.(onArity)) as [s' Hs].
                eapply wf_arity_spine_typing_spine => //.
                split.
                eapply (instantiate_minductive _ _ _ u1) in Hs; eauto.
                2:pcuic.
                eapply weaken_ctx in Hs. simpl in Hs. right; exists (subst_instance_univ u1 s'). red. eauto. auto.
                now eapply spine_dom_wf.
                rewrite oib.(ind_arity_eq).
                rewrite subst_instance_constr_it_mkProd_or_LetIn.
                eapply arity_spine_it_mkProd_or_LetIn; eauto.
                { set (foo:=map (lift #|argctx| #|ind_indices oib| ∘ lift0 #|ind_indices oib|)
                    cparsubst).
                  clear -instsp wf cparsubst0 H.
                  eapply (spine_subst_weakening _ _ _ _ _ (subst_context cparsubst 0
                    (subst_context (inds (inductive_mind ind) u1 (ind_bodies mdecl))
                      #|cparsubst| (map_context (subst_instance_constr u1) argctx)))) in cparsubst0; auto.
                  rewrite closed_ctx_lift in cparsubst0 => //.
                  autorewrite with len in cparsubst0.
                  eapply cparsubst0.                  
                  apply (spine_dom_wf _ _ _ _ _ instsp). }
                rewrite subst_instance_constr_it_mkProd_or_LetIn subst_it_mkProd_or_LetIn.
                rewrite -(app_nil_r (map _ (cshape_indices _))).
                eapply arity_spine_it_mkProd_or_LetIn; [auto|auto|constructor].
                2:{ left; eexists _, _; split; simpl; eauto. now eapply spine_dom_wf. }
                eapply (spine_subst_eq instsp).
                rewrite distr_lift_subst_context.
                rewrite closed_ctx_lift ?Nat.add_0_r -?lencpar //.
                simpl. reflexivity. }

              rewrite subst_mkApps.
              apply conv_cumul.
              rewrite /cshape_concl_head.
              rewrite subst_inds_concl_head.
              { simpl. destruct decli. now eapply nth_error_Some_length in H2. }
              simpl. apply mkApps_conv_args; auto.
               
              rewrite map_app. eapply All2_app.
              ****
                eapply (All2_impl (P:=fun x y => x = y)).
                2:{ intros ? ? ->. reflexivity. }
                eapply All2_eq_eq.
                rewrite -map_map_compose.
                rewrite subst_instance_to_extended_list_k.
                rewrite -map_map_compose.
                rewrite -(subst_instance_context_length u1 (ind_params mdecl)).
                rewrite -to_extended_list_k_map_subst; [lia|].
                erewrite subst_to_extended_list_k.
                2:{ eapply make_context_subst_spec_inv. rewrite List.rev_involutive.
                    rewrite -[subst_instance_context _ _](closed_ctx_lift #|argctx| 0) => //.
                      apply context_subst_lift.
                    apply (cparsubst0.(inst_ctx_subst)). }
                rewrite map_map_compose.
                rewrite map_subst_lift_id_eq. now autorewrite with len.
                reflexivity.
              ****
                set (instargctx := subst_context cparsubst 0 (subst_context _ #|cparsubst| _)) in *.
                rewrite -{1}lencpar in instsp.
                assert(#|instargctx| = #|argctx|).
                { subst instargctx  ; now  autorewrite with len. }
                unfold argctx in H0.
                rewrite -{3}H0 -(all_rels_length instargctx 0 #|argctx|).
                rewrite -(map_map_compose _ _ _ _ (subst cparsubst #|argctx|)).
                rewrite -map_map_compose.
                rewrite -map_map_compose.
                rewrite map_map_compose.
                eapply All2_map. rewrite -lencpar.
                rewrite !map_map_compose.
                apply All2_refl.
                intros.
                unfold compose.
                rewrite all_rels_length.
                epose proof (all_rels_subst Σ instargctx Γ _ wf (spine_dom_wf _ _ _ _ _ instsp)).
                eapply red_conv in X.
                assert(subst (map (lift0 #|argctx|) cparsubst) #|instargctx| x =
                  (lift #|argctx| #|argctx| (subst cparsubst #|argctx| x))).
                  epose proof (distr_lift_subst_rec _ _ #|argctx| #|argctx| 0).
                  rewrite Nat.add_0_r in H2. rewrite H2. f_equal. now rewrite H0.
                  admit.
                  rewrite H2.
                  rewrite H0 in X.
                  symmetry in X.
                  apply X.
          
          

    * rewrite subst_mkApps.
      pose proof (context_subst_length _ _ _ idxsubst0).
      rewrite !subst_context_length subst_instance_context_length in H.
      rewrite -{1}(Nat.add_0_r #|argctx|) (simpl_subst' _ _ 0 _ #|argctx|) /argctx; try lia; auto.
      rewrite lift0_id. f_equal.
      rewrite map_app /= subst_mkApps. f_equal.
      f_equal. simpl. f_equal.
      rewrite map_app -{1}(firstn_skipn (ind_npars mdecl) cargs).  
      f_equal. rewrite map_map_compose.
      now rewrite H map_subst_lift_id.
      unfold to_extended_list.
      erewrite subst_to_extended_list_k. rewrite map_id_f. intros x; apply lift0_id.
      reflexivity.
      apply make_context_subst_spec_inv. rewrite List.rev_involutive.
      apply idxsubst0.
    * right.
      exists ps.
      eapply type_mkApps. eauto.
      eapply wf_arity_spine_typing_spine => //.
      split.
      ** now eapply validity in typep.
      ** eapply arity_spine_it_mkProd_or_LetIn => //.
         eauto.
         simpl. constructor.
         2:constructor; auto; pcuic.
         2:{ left; eexists [], ps; intuition auto. }
        rewrite subst_mkApps. 
        rewrite map_app.
        pose proof (subslet_length subsidx).
        autorewrite with len in H. rewrite -H.
        rewrite map_map_compose map_subst_lift_id.
        pose proof (spine_subst_subst_to_extended_list_k subsidx).
        rewrite to_extended_list_k_fold_context in H0.
        rewrite PCUICSubstitution.map_subst_instance_constr_to_extended_list_k  in H0.
        rewrite {}H0. now rewrite firstn_skipn /=.
    * simpl in Hbr. rewrite Hbr in a. intuition discriminate.
    * eapply on_declared_minductive => //. pcuic.

  - (* Case congruence: on a cofix, impossible *)
    clear -wf typec heq_allow_cofix.
    eapply type_mkApps_inv in typec as [? [? [[tcof _] _]]] =>  //.
    eapply type_tCoFix_inv in tcof as [allowc _] => //.
    rewrite allowc in heq_allow_cofix. discriminate.

  - (* Case congruence on the predicate *) 
    eapply (type_Cumul _ _ _ (mkApps p' (skipn npar args ++ [c]))).
    eapply build_branches_type_red in heq_map_option_out as [brtys' [eqbrtys alleq]]; eauto.
    eapply type_Case; eauto.
    * eapply All2_trans'; eauto. simpl.
      intros.
      intuition auto. now transitivity y.1.
      eapply type_Cumul; eauto.
      now eapply conv_cumul, red_conv, red1_red.
    * right.
      pose proof typec as typec'.
      eapply (env_prop_typing _ _ validity) in typec' as wat; auto.
      unshelve eapply isWAT_mkApps_Ind in wat as [parsubst [argsubst wat]]; eauto.
      set (oib := on_declared_inductive wf isdecl) in *. clearbody oib.
      destruct oib as [onind oib].
      destruct wat  as [[spars sargs] cu].
      unshelve eapply (build_case_predicate_type_spec (Σ.1, _)) in heq_build_case_predicate_type as [parsubst' [cparsubst Hpty]]; eauto.
      rewrite {}Hpty in typep.
      exists ps.
      subst npar.
      pose proof (context_subst_fun cparsubst spars). subst parsubst'. clear cparsubst.
      eapply type_mkApps. eauto.
      eapply wf_arity_spine_typing_spine; eauto.
      split. apply (env_prop_typing _ _ validity) in typep as ?; eauto.
      eapply arity_spine_it_mkProd_or_LetIn; eauto.
      simpl. constructor; [ |constructor].
      2:{ left; eexists _, _; split. simpl; eauto. auto. }
      2:reflexivity.
      rewrite subst_mkApps. simpl.
      rewrite map_app. rewrite map_map_compose.
      rewrite map_subst_lift_id_eq. now rewrite (subslet_length sargs); autorewrite with len.
      move: (spine_subst_subst_to_extended_list_k sargs).
      rewrite to_extended_list_k_subst PCUICSubstitution.map_subst_instance_constr_to_extended_list_k.
      move->. now rewrite firstn_skipn.
    * now eapply conv_cumul, conv_sym, red_conv, red_mkApps_f, red1_red.

  - (* Case congruence on discriminee *) 
    eapply type_Cumul. eapply type_Case; eauto.
    * solve_all.
    * right.
      pose proof typec as typec'.
      eapply (env_prop_typing _ _ validity) in typec' as wat; auto.
      unshelve eapply isWAT_mkApps_Ind in wat as [parsubst [argsubst wat]]; eauto.
      set (oib := on_declared_inductive wf isdecl) in *. clearbody oib.
      destruct oib as [onind oib].
      destruct wat  as [[spars sargs] cu].
      unshelve eapply (build_case_predicate_type_spec (Σ.1, _)) in heq_build_case_predicate_type as [parsubst' [cparsubst Hpty]]; eauto.
      rewrite {}Hpty in typep.
      exists ps.
      subst npar.
      pose proof (context_subst_fun cparsubst spars). subst parsubst'. clear cparsubst.
      eapply type_mkApps. eauto.
      eapply wf_arity_spine_typing_spine; eauto.
      split. apply (env_prop_typing _ _ validity) in typep; eauto.
      eapply arity_spine_it_mkProd_or_LetIn; eauto.
      simpl. constructor; [ |constructor].
      2:{ left; eexists _, _; split. simpl; eauto. auto. }
      2:reflexivity.
      rewrite subst_mkApps. simpl.
      rewrite map_app. rewrite map_map_compose.
      rewrite map_subst_lift_id_eq. now rewrite (subslet_length sargs); autorewrite with len.
      move: (spine_subst_subst_to_extended_list_k sargs).
      rewrite to_extended_list_k_subst PCUICSubstitution.map_subst_instance_constr_to_extended_list_k.
      move->. now rewrite firstn_skipn.
    * eapply conv_cumul, conv_sym, red_conv, red_mkApps; auto.
      eapply All2_app; [eapply All2_refl; reflexivity|now constructor].

  - (* Case congruence on branches *)
    eapply type_Case; eauto.
    eapply (OnOne2_All2_All2 _ _ _ _ _ _ _ o X5).
    intros [] []; simpl. intros.
    intuition auto. subst.
    intros [] [] []; simpl. intros.
    intuition auto. subst.    
    reflexivity.

  - (* Proj CoFix congruence *)
    epose proof (env_prop_typing _ _  validity _ _ _ _ _ typec).
    eapply type_mkApps_inv in typec as [? [? [[tcof tsp] cum]]]; auto.
    eapply type_tCoFix_inv in tcof as [allow [?  [? [? [[unf tyunf] cum']]]]]; auto.
    rewrite e in unf. noconf unf.
    eapply typing_spine_strengthen in tsp; eauto.
    eapply typing_spine_weaken_concl in tsp; eauto.
    eapply type_Cumul; [econstructor|..]; eauto.
    eapply type_mkApps. eauto. eauto. admit.
    (** Essential here that projection types cannot refer to the coinductive object  
        directly but only through projections, so that SR is preserved.
        Will need to add an invariant to the projections typing. *)
    rewrite allow in heq_allow_cofix. discriminate.

  - (* Proj Constructor reduction *) 
    epose proof (env_prop_typing _ _ validity _ _ _ _ _ typec).
    simpl in typec.
    pose proof typec as typec'.
    eapply inversion_mkApps in typec as [A [U [tyc [tyargs tycum]]]]; auto.
    eapply (inversion_Construct Σ wf) in tyc as [mdecl' [idecl' [cdecl' [wfl [declc [Hu tyc]]]]]].
    unshelve eapply Construct_Ind_ind_eq in typec'; eauto.
    unfold on_declared_constructor in typec'.
    destruct declc as [decli declc].
    unfold on_declared_inductive in typec'.
    destruct declared_constructor_inv as [cs [Hnth onc]].
    simpl in typec'.
    destruct declared_inductive_inv. simpl in  *.
    pose proof isdecl as isdecl'.
    destruct isdecl' as [decli' [H0 Hi]].
    destruct (declared_inductive_unique decli' decli) as []; subst mdecl' idecl'.
    forward onProjections.
    eapply nth_error_Some_length in H0. simpl in H0.
    intros Hp. apply (f_equal (@length _)) in Hp. rewrite  Hp /=   in H0. lia.
    simpl in H0.
    simpl in *.
    destruct typec' as [[[[_ equ] cu] eqargs] [cparsubst [cargsubst [iparsubst [iidxsubst ci]]]]].
    destruct ci as ((([cparsubst0 iparsubst0] & idxsubst0) & subsidx) & [s [typectx [Hpars Hargs]]]).
    clear Hnth.
    destruct onProjections.
    eapply nth_error_alli in on_projs; eauto.
    destruct on_projs. simpl in t.
    eapply typing_spine_strengthen in tyargs; eauto.
    eapply typing_spine_weaken_concl in tyargs; eauto.
    rewrite -(firstn_skipn (ind_npars mdecl) args0) in tyargs, e |- *.
    subst pars.
    assert(#|firstn (ind_npars mdecl) args0| = ind_npars mdecl).
    rewrite firstn_length_le. lia. lia.
    rewrite nth_error_app_ge in e. lia.
    rewrite H in e. replace (ind_npars mdecl + narg - ind_npars mdecl) with narg in e by lia.
    unfold type_of_constructor in tyargs.
    rewrite onc.(cshape).(cshape_eq) in tyargs.
    rewrite !subst_instance_constr_it_mkProd_or_LetIn !subst_it_mkProd_or_LetIn in tyargs.
    (** Will need inversion lemmas on typing_spine *)
    admit.


  - (* Proj congruence *) 
    eapply type_Cumul; [econstructor|..]; eauto.
    admit.
    eapply conv_cumul.
    (* eapply (conv_subst_conv. *)
    admit.

  - (* Fix congruence *)
    symmetry in H0; apply mkApps_Fix_spec in H0. simpl in H0. subst args.
    simpl. destruct narg; discriminate.
  
  - assert(fixl :#|fix_context mfix| = #|fix_context mfix1|) by now (rewrite !fix_context_length; apply (OnOne2_length o)).
    assert(convctx : conv_context Σ (Γ ,,, fix_context mfix) (Γ ,,, fix_context mfix1)).
    { clear -wf X o fixl.
      eapply context_relation_app_inv => //.
      apply conv_ctx_refl. clear X.
      apply conv_decls_fix_context => //.
      induction o; constructor.
      destruct p. now apply red_conv, red1_red.
      apply All2_refl. reflexivity.
      reflexivity. apply IHo. }
    assert (wf_local Σ (Γ ,,, fix_context mfix1)).
    { apply All_local_env_app_inv. split; auto.
      apply All_local_env_app in X as [l r].
      
      eapply (All_local_env_fix_OnOne2 _ (
        fun Σ Γ0 t T =>
        Σ;;; Γ0 |- t : T
        × (forall u : term, red1 Σ Γ0 t u -> Σ;;; Γ0 |- u : T))); eauto.
      all: simpl; intros *; auto.
      * unfold lift_typing at 1.
        destruct T.
        ** intros conv [tyt _] wfΔ'.
          eapply context_conversion in tyt as [_ tyt]; eauto.
          eapply tyt; eauto. rewrite -app_context_assoc. apply All_local_env_app_inv; split; auto.
          now eapply typing_wf_local in tyt.
        ** intros conv [s [tyt _]] wfΔ'.
          eapply context_conversion in tyt as [_ tyt]; eauto.
          exists s.
          eapply tyt; eauto.
          rewrite -app_context_assoc. apply All_local_env_app_inv; split; auto.
          now eapply typing_wf_local in tyt.
      * intros [red _]. now apply red_conv. 
      * intros [red _] conv wfΓ'' [s [ty Hred]].
        exists s. specialize (Hred (lift0 #|Γ'| (dtype hd'))).
        forward Hred. eapply (weakening_red1 _ _ []) => //.
        eapply context_conversion in Hred as [_ Hred]; eauto.
        eapply Hred; eauto. eapply All_local_env_app_inv; split; auto.
        now eapply typing_wf_local in ty.
      }

    destruct (OnOne2_nth_error _ _ _ _ _ decl o heq_nth_error) as [decl' [[eqnth  eqs] disj]].
    eapply type_Cumul.
    econstructor; eauto.
     (* Need  to update fix_guard *)
    admit.
    apply (OnOne2_All_All _ _ _ _ _ _ o X0).
    simpl; intros x [[ty isl] Hred].
    split; auto. eapply  context_conversion. 4:eapply convctx.
    all:eauto. now eapply typing_wf_local in ty.
    now rewrite -fixl.
    intros [] [] [Hred Heq] [[ty isl] Hred'].
    simpl in *. noconf Heq.
    rewrite -fixl. split; eauto.
    eapply  context_conversion. 4:eapply convctx.
    all:eauto. now eapply typing_wf_local in ty.
    now rewrite -fixl.
    intros [] [] 
    rewrite 
    eapply ty.


    clear -X X0 convctx X1 o fixl.
    revert o X0. generalize mfix at 1 7.
    generalize mfix1 at 1 4.
    induction 1; constructor.
    depelim X0.
    destruct p0 as [[ty eqbody] red].
    destruct p as [Hred Heq]. noconf Heq. simpl in H; noconf H.
    rewrite -eqbody H0. split; auto.
    rewrite -fixl -H0.
    eapply context_conversion.
    3:{  } _ _ _ _ _ _ _ _ (fix_context mfix)). 3:eauto.



    eapply OnOne2_All_mix_left in o; eauto.
    clear o. 



  - (* Fix congruence in body *)
    admit.
  - (* CoFix congruence type *)
    admit.
  - (* CoFix congruence body *)
    admit.
  - (* Conversion *)
    specialize (forall_u _ Hu).
    eapply type_Cumul; eauto.
    destruct X2 as [[wf' _]|[s Hs]].
    now left.
    now right.
Admitted.

Definition sr_stmt {cf:checker_flags} (Σ : global_env_ext) Γ t T :=
  forall u, red Σ Γ t u -> Σ ;;; Γ |- u : T.

Theorem subject_reduction {cf:checker_flags} : forall (Σ : global_env_ext) Γ t u T,
  wf Σ -> Σ ;;; Γ |- t : T -> red Σ Γ t u -> Σ ;;; Γ |- u : T.
Proof.
  intros * wfΣ Hty Hred.
  induction Hred. auto.
  eapply sr_red1 in IHHred; eauto with wf. now apply IHHred.
Qed.

Lemma subject_reduction1 {cf:checker_flags} {Σ Γ t u T}
  : wf Σ.1 -> Σ ;;; Γ |- t : T -> red1 Σ.1 Γ t u -> Σ ;;; Γ |- u : T.
Proof.
  intros. eapply subject_reduction; try eassumption.
  now apply red1_red.
Defined.

Section SRContext.
  Context {cf:checker_flags}.

  (* todo: rename wf_local_app *)
  Definition wf_local_app' {Σ Γ1 Γ2} :
    wf_local Σ Γ1 -> wf_local_rel Σ Γ1 Γ2
    -> wf_local Σ (Γ1 ,,, Γ2).
  Proof.
    intros H1 H2. apply wf_local_local_rel.
    apply wf_local_rel_local in H1.
    apply wf_local_rel_app_inv; tas.
    now rewrite app_context_nil_l.
  Qed.

  Definition cumul_red_l' `{checker_flags} :
    forall Σ Γ t u,
      wf Σ.1 ->
      red (fst Σ) Γ t u ->
      Σ ;;; Γ |- t <= u.
  Proof.
    intros Σ Γ t u hΣ h.
    induction h.
    - eapply cumul_refl'.
    - eapply PCUICConversion.cumul_trans ; try eassumption.
      eapply cumul_red_l.
      + eassumption.
      + eapply cumul_refl'.
  Defined.

  Hint Constructors OnOne2_local_env : aa.
  Hint Unfold red1_ctx : aa.


  Lemma red1_ctx_app Σ Γ Γ' Δ :
    red1_ctx Σ Γ Γ' ->
    red1_ctx Σ (Γ ,,, Δ) (Γ' ,,, Δ).
  Proof.
    induction Δ. trivial.
    intro H. simpl. constructor. now apply IHΔ.
  Qed.

  Lemma red1_red_ctx Σ Γ Γ' :
    red1_ctx Σ Γ Γ' ->
    red_ctx Σ Γ Γ'.
  Proof.
    induction 1; cbn in *.
    - constructor. reflexivity. cbn; eauto using red1_red.
    - constructor. reflexivity.
      destruct p as [[? []]|[? []]]; cbn; eauto using red1_red.
    - destruct d as [na [bo|] ty]; constructor; eauto.
      split; eapply refl_red.
      apply refl_red.
  Qed.

  Lemma nth_error_red1_ctx Σ Γ Γ' n decl :
    wf Σ ->
    nth_error Γ n = Some decl ->
    red1_ctx Σ Γ Γ' ->
    ∑ decl', nth_error Γ' n = Some decl'
              × red Σ Γ' (lift0 (S n) (decl_type decl))
              (lift0 (S n) (decl_type decl')).
  Proof.
    intros wfΣ h1 h2; induction h2 in n, h1 |- *.
    - destruct n.
      + inversion h1; subst. exists (vass na t').
        split; cbnr.
        eapply (weakening_red_0 wfΣ _ [_]); tas; cbnr.
        apply red1_red; tas.
      + exists decl. split; tas. apply refl_red.
    - destruct n.
      + inversion h1; subst.
        destruct p as [[? []]|[? []]].
        -- exists (vdef na b' t).
           split; cbnr.
        -- exists (vdef na b t').
           split; cbnr.
           eapply (weakening_red_0 wfΣ _ [_]); tas; cbnr.
           apply red1_red; tas.
      + exists decl. split; tas. apply refl_red.
    - destruct n.
      + exists d. split; cbnr. inv h1; apply refl_red.
      + cbn in h1. specialize (IHh2 _ h1).
        destruct IHh2 as [decl' [X1 X2]].
        exists decl'. split; tas.
        rewrite !(simpl_lift0 _ (S n)).
        eapply (weakening_red_0 wfΣ _ [_]); tas; cbnr.
  Qed.


  Lemma wf_local_isType_nth Σ Γ n decl :
    wf Σ.1 ->
    wf_local Σ Γ ->
    nth_error Γ n = Some decl ->
    ∑ s, Σ ;;; Γ |- lift0 (S n) (decl_type decl) : tSort s.
  Proof.
    induction n in Γ, decl |- *; intros hΣ hΓ e; destruct Γ;
      cbn; inversion e; inversion hΓ; subst.
    all: try (destruct X0 as [s Ht]; exists s;
              eapply (weakening _ _ [_] _ (tSort s)); tas).
    - eapply IHn in H0; tas. destruct H0 as [s Ht]. exists s.
      rewrite simpl_lift0.
      eapply (weakening _ _ [_] _ (tSort s)); tas; cbnr.
    - eapply IHn in H0; tas. destruct H0 as [s Ht]. exists s.
      rewrite simpl_lift0.
      eapply (weakening _ _ [_] _ (tSort s)); tas; cbnr.
  Qed.

  Ltac invs H := inversion H; subst.
  Ltac invc H := inversion H; subst; clear H.

  Lemma subject_reduction_ctx :
    env_prop (fun Σ Γ t A => forall Γ', red1_ctx Σ Γ Γ' -> Σ ;;; Γ' |- t : A).
  Proof.
    assert (X: forall Σ Γ wfΓ, All_local_env_over typing
                          (fun Σ Γ (_ : wf_local Σ Γ)  t T (_ : Σ;;; Γ |- t : T) =>
                             forall Γ', red1_ctx Σ Γ Γ' -> Σ;;; Γ' |- t : T) Σ Γ wfΓ
                          -> wf Σ -> forall Γ', red1_ctx Σ Γ Γ' -> wf_local Σ Γ'). {
      induction 1.
      - intros hΣ Γ' r. inv r.
      - intros hΣ Γ' r. inv r.
        + constructor; tas.
          destruct tu as [s Ht]. exists s. eapply subject_reduction1; tea.
        + constructor; tas. eapply IHX; tas.
          eexists. now eapply p.
      - intros hΣ Γ' r. inv r.
        + destruct X0 as [[? []]|[? []]]; constructor; cbn; tas.
          eapply subject_reduction1; tea.
          destruct tu as [s Ht]. exists s. eapply subject_reduction1; tea.
          econstructor; tea.
          2: eauto using red_cumul.
          right. destruct tu as [s ?]; exists s; eapply subject_reduction1; tea.
        + constructor; tas. eapply IHX; tas.
          eexists. now eapply p0.
          now eapply p. }
    eapply typing_ind_env; cbn; intros; try solve [econstructor; eauto with aa].
    - assert (X2: ∑ decl', nth_error Γ' n = Some decl'
             × red Σ.1 Γ' (lift0 (S n) (decl_type decl))
             (lift0 (S n) (decl_type decl'))) by now eapply nth_error_red1_ctx.
      destruct X2 as [decl' [H1 H2]].
      eapply type_Cumul. econstructor. eauto. exact H1.
      2: now eapply red_cumul_inv.
      right.
      clear decl' H1 H2.
      induction X1 in wfΓ, n, H, X0 |- *; cbn in *.
      + destruct n; cbn in *.
        * invc H. invs wfΓ. destruct X2 as [s Ht]; exists s.
          eapply (weakening _ _ [_] _ (tSort _)); tas; cbnr.
          constructor; tas. exists s.
          eapply subject_reduction; tea; auto.
        * invc H. invs wfΓ.
          eapply wf_local_isType_nth in H1; tea.
          destruct H1 as [s Ht]. exists s.
          rewrite simpl_lift0.
          eapply (weakening _ _ [_] _ (tSort _)); tas; cbnr.
          constructor; tas. destruct X2 as [s' ?]; exists s'.
          eapply subject_reduction; tea; auto.
      + destruct n; cbn in *.
        * invc H. invs wfΓ. destruct X2 as [s Ht]; exists s.
          eapply (weakening _ _ [_] _ (tSort _)); tas; cbnr.
          destruct p as [[? []]|[? []]]; constructor; cbn; tas.
          now exists s.
          eapply subject_reduction; tea; auto.
          exists s. eapply subject_reduction; tea; auto.
          econstructor; tea.
          2: eauto using red_cumul.
          right. exists s; eapply subject_reduction1; tea.
        * invc H. invs wfΓ.
          eapply wf_local_isType_nth in H1; tea.
          destruct H1 as [s Ht]. exists s.
          rewrite simpl_lift0.
          eapply (weakening _ _ [_] _ (tSort _)); tas; cbnr.
          destruct p as [[? []]|[? []]]; constructor; cbn; tas.
          eapply subject_reduction; tea; auto.
          destruct X2 as [s' Ht']. exists s'.
          eapply subject_reduction; tea; auto.
          econstructor; tea.
          2: eauto using red_cumul.
          right. destruct X2 as [s' ?]; exists s'; eapply subject_reduction1; tea.
      + destruct n; cbn in *.
        * invc H. clear IHX1. invs wfΓ.
          -- invs X0. destruct tu as [s Ht]; exists s.
             eapply (weakening _ _ [_] _ (tSort _)); tas; cbnr.
             eapply (X _ _ wfΓ); tea. now constructor.
             eauto.
          -- invs X0. destruct tu as [s Ht]; exists s.
             eapply (weakening _ _ [_] _ (tSort _)); tas; cbnr.
             eapply (X _ _ wfΓ); tea. now constructor.
             eauto.
        * invs wfΓ; inv X0.
          -- specialize (IHX1 _ _ H X4).
             destruct IHX1 as [s ?]; exists s.
             rewrite simpl_lift0.
             eapply (weakening _ _ [_] _ (tSort _)); tas; cbnr.
             constructor. eauto.
             exists tu.π1. eauto.
          -- specialize (IHX1 _ _ H X5).
             destruct IHX1 as [s ?]; exists s.
             rewrite simpl_lift0.
             eapply (weakening _ _ [_] _ (tSort _)); tas; cbnr.
             constructor. eauto.
             exists tu.π1. eauto. cbn. eauto.
    - econstructor; tea; eauto.
      eapply All2_impl; tea; cbn.
      intros; rdest; eauto.
    - assert (XX: red1_ctx Σ.1 (Γ ,,, fix_context mfix) (Γ' ,,, fix_context mfix))
        by now eapply red1_ctx_app.
      econstructor; tea.
      + set (Δ := Γ ,,, fix_context mfix) in *.
        assert (ZZ: ∑ wfΔ, All_local_env_over typing
                            (fun Σ Γ (_ : wf_local Σ Γ)  t T (_ : Σ;;; Γ |- t : T) =>
                               forall Γ', red1_ctx Σ Γ Γ' -> Σ;;; Γ' |- t : T) Σ Δ wfΔ). {
          clearbody Δ; clear -X0.
          induction X0.
          - eexists; constructor.
          - destruct t0 as [? [? ?]].
            eexists; unshelve econstructor; tea.
            exact IHX0.π1.
            eexists; eassumption.
            exact IHX0.π2. eassumption.
          - destruct IHX0 as [X1 X2].
            destruct t0 as [s [Y1 Y2]], t1 as [Y3 Y4].
            eexists.
            unshelve econstructor; tea. eexists; eassumption.
            eauto. }
        eapply X with (Γ ,,, fix_context mfix) ZZ.π1; tea. exact ZZ.π2.
      + eapply All_impl; tea.
        intros; rdest; eauto.
    - assert (XX: red1_ctx Σ.1 (Γ ,,, fix_context mfix) (Γ' ,,, fix_context mfix))
        by now eapply red1_ctx_app.
      econstructor; tea.
      + set (Δ := Γ ,,, fix_context mfix) in *.
        assert (ZZ: ∑ wfΔ, All_local_env_over typing
                            (fun Σ Γ (_ : wf_local Σ Γ)  t T (_ : Σ;;; Γ |- t : T) =>
                               forall Γ', red1_ctx Σ Γ Γ' -> Σ;;; Γ' |- t : T) Σ Δ wfΔ). {
          clearbody Δ; clear -X0.
          induction X0.
          - eexists; constructor.
          - destruct t0 as [? [? ?]].
            eexists; unshelve econstructor; tea.
            exact IHX0.π1.
            eexists; eassumption.
            exact IHX0.π2. eassumption.
          - destruct IHX0 as [X1 X2].
            destruct t0 as [s [Y1 Y2]], t1 as [Y3 Y4].
            eexists.
            unshelve econstructor; tea. eexists; eassumption.
            eauto. }
        eapply X with (Γ ,,, fix_context mfix) ZZ.π1; tea. exact ZZ.π2.
      + eapply All_impl; tea.
        intros; rdest; eauto.
    - econstructor.
      + now eapply X2.
      + destruct X3 as [[[ctx [s [H1 H2]]] X3]|X3]; [left|right].
        * cbn in *. exists ctx, s. split; eauto.
          eapply X; tea.
          now apply red1_ctx_app.
        * rdest; eauto.
      + eapply cumul_red_ctx; tea. now apply red1_red_ctx.
  Qed.


  Lemma wf_local_red1 {Σ Γ Γ'} :
    wf Σ.1 ->
    red1_ctx Σ.1 Γ Γ' -> wf_local Σ Γ -> wf_local Σ Γ'.
  Proof.
    intro hΣ. induction 1; cbn in *.
    - intro e. inversion e; subst; cbn in *.
      constructor; tas. destruct X0 as [s Ht]. exists s.
      eapply subject_reduction1; tea.
    - intro e. inversion e; subst; cbn in *.
      destruct p as [[? []]|[? []]]; constructor; cbn; tas.
      + eapply subject_reduction1; tea.
      + destruct X0; eexists; eapply subject_reduction1; tea.
      + econstructor; tea.
        right; destruct X0; eexists; eapply subject_reduction1; tea.
        econstructor 2. eassumption. reflexivity.
    - intro H; inversion H; subst; constructor; cbn in *; auto.
      + destruct X1 as [s Ht]. exists s.
        eapply subject_reduction_ctx; tea.
      + destruct X1 as [s Ht]. exists s.
        eapply subject_reduction_ctx; tea.
      + eapply subject_reduction_ctx; tea.
  Qed.

  Lemma eq_context_upto_names_upto_names Γ Δ :
    eq_context_upto_names Γ Δ -> Γ ≡Γ Δ.
  Proof.
    induction 1; cbnr; try constructor; eauto.
    destruct x as [? [] ?], y as [? [] ?]; cbn in *; subst; inversion e.
    all: constructor; cbnr; eauto.
  Qed.


  Lemma wf_local_red {Σ Γ Γ'} :
    wf Σ.1 ->
    red_ctx Σ.1 Γ Γ' -> wf_local Σ Γ -> wf_local Σ Γ'.
  Proof.
    intros hΣ h. apply red_ctx_clos_rt_red1_ctx in h.
    induction h; eauto using wf_local_red1.
    apply eq_context_upto_names_upto_names in e.
    eauto using wf_local_alpha.
  Qed.


  Lemma wf_local_subst1 Σ (wfΣ : wf Σ.1) Γ na b t Γ' :
      wf_local Σ (Γ ,,, [],, vdef na b t ,,, Γ') ->
      wf_local Σ (Γ ,,, subst_context [b] 0 Γ').
  Proof.
    induction Γ' as [|d Γ']; [now inversion 1|].
    change (d :: Γ') with (Γ' ,, d).
    destruct d as [na' [bd|] ty]; rewrite !app_context_cons; intro HH.
    - rewrite subst_context_snoc0. simpl.
      inversion HH; subst; cbn in *. destruct X0 as [s X0].
      change (Γ,, vdef na b t ,,, Γ') with (Γ ,,, [vdef na b t] ,,, Γ') in *.
      assert (subslet Σ Γ [b] [vdef na b t]). {
        pose proof (cons_let_def Σ Γ [] [] na b t) as XX.
        rewrite !subst_empty in XX. apply XX. constructor.
        apply wf_local_app in X. inversion X; subst; cbn in *; assumption.
      }
      constructor; cbn; auto.
      1: exists s. 1: unfold PCUICTerm.tSort.
      1: change (tSort s) with (subst [b] #|Γ'| (tSort s)).
      all: eapply substitution_alt; tea.
    - rewrite subst_context_snoc0. simpl.
      inversion HH; subst; cbn in *. destruct X0 as [s X0].
      change (Γ,, vdef na b t ,,, Γ') with (Γ ,,, [vdef na b t] ,,, Γ') in *.
      assert (subslet Σ Γ [b] [vdef na b t]). {
        pose proof (cons_let_def Σ Γ [] [] na b t) as XX.
        rewrite !subst_empty in XX. apply XX. constructor.
        apply wf_local_app in X. inversion X; subst; cbn in *; assumption. }
      constructor; cbn; auto. exists s.
      unfold PCUICTerm.tSort.
      change (tSort s) with (subst [b] #|Γ'| (tSort s)).
      all: eapply substitution_alt; tea.
  Qed.


  Lemma red_ctx_app_context_l {Σ Γ Γ' Δ}
    : red_ctx Σ Γ Γ' -> red_ctx Σ (Γ ,,, Δ) (Γ' ,,, Δ).
  Proof.
    induction Δ as [|[na [bd|] ty] Δ]; [trivial| |];
      intro H; simpl; constructor; cbn; eauto; now apply IHΔ.
  Qed.


   Lemma isWfArity_red1 {Σ Γ A B} :
     wf Σ.1 ->
       red1 (fst Σ) Γ A B ->
       isWfArity typing Σ Γ A ->
       isWfArity typing Σ Γ B.
   Proof.
     intro wfΣ. induction 1 using red1_ind_all.
     all: intros [ctx [s [H1 H2]]]; cbn in *; try discriminate.
     - rewrite destArity_app in H1.
       case_eq (destArity [] b'); [intros [ctx' s']|]; intro ee;
         [|rewrite ee in H1; discriminate].
       pose proof (subst_destArity [] b' [b] 0) as H; cbn in H.
       rewrite ee in H. eexists _, s'. split. eassumption.
       rewrite ee in H1. cbn in *. inversion H1; subst.
       rewrite app_context_assoc in H2.
       now eapply wf_local_subst1.
     - rewrite destArity_tFix in H1; discriminate.
     - rewrite destArity_app in H1.
       case_eq (destArity [] b'); [intros [ctx' s']|]; intro ee;
         rewrite ee in H1; [|discriminate].
       eexists _, s'; split. cbn. rewrite destArity_app ee. reflexivity.
       cbn in H1. inversion H1; subst.
       eapply wf_local_red; try exact H2; tas.
       rewrite !app_context_assoc. apply red_ctx_app_context_l.
       constructor; cbn. reflexivity. split; auto.
     - rewrite destArity_app in H1.
       case_eq (destArity [] b'); [intros [ctx' s']|]; intro ee;
         rewrite ee in H1; [|discriminate].
       eexists _, s'; split. cbn. rewrite destArity_app ee. reflexivity.
       cbn in H1. inversion H1; subst.
       eapply wf_local_red; try exact H2; tas.
       rewrite !app_context_assoc. apply red_ctx_app_context_l.
       constructor; cbn. reflexivity. split; auto.
     - rewrite destArity_app in H1.
       case_eq (destArity [] b'); [intros [ctx' s']|]; intro ee;
         rewrite ee in H1; [|discriminate].
       forward IHX. {
         eexists _, s'; split; tea. cbn in H1.
         inversion H1; subst. now rewrite app_context_assoc in H2. }
       destruct IHX as [ctx'' [s'' [ee' ?]]].
       eexists _, s''; split. cbn. rewrite destArity_app ee'. reflexivity.
       now rewrite app_context_assoc.
     - rewrite destArity_app in H1.
       case_eq (destArity [] M2); [intros [ctx' s']|]; intro ee;
         rewrite ee in H1; [|discriminate].
       eexists _, s'; split. cbn. rewrite destArity_app ee. reflexivity.
       cbn in H1. inversion H1; subst.
       eapply wf_local_red; try exact H2; tas.
       rewrite !app_context_assoc. apply red_ctx_app_context_l.
       constructor; cbn. reflexivity. auto.
     - rewrite destArity_app in H1.
       case_eq (destArity [] M2); [intros [ctx' s']|]; intro ee;
         rewrite ee in H1; [|discriminate].
       forward IHX. {
         eexists _, s'; split; tea. cbn in H1.
         inversion H1; subst. now rewrite app_context_assoc in H2. }
       destruct IHX as [ctx'' [s'' [ee' ?]]].
       eexists _, s''; split. cbn. rewrite destArity_app ee'. reflexivity.
       now rewrite app_context_assoc.
   Qed.

   Lemma isWfArity_red {Σ Γ A B} :
     wf Σ.1 ->
     red (fst Σ) Γ A B ->
     isWfArity typing Σ Γ A ->
     isWfArity typing Σ Γ B.
   Proof.
     induction 2.
     - easy.
     - intro. now eapply isWfArity_red1.
   Qed.

   Lemma isWfArity_or_Type_red {Σ Γ A B} :
     wf Σ.1 ->
     red (fst Σ) Γ A B ->
     isWfArity_or_Type Σ Γ A ->
     isWfArity_or_Type Σ Γ B.
   Proof.
     intros ? ? [?|[? ?]]; [left|right].
     eapply isWfArity_red; eassumption.
     eexists. eapply subject_reduction; tea.
   Qed.

  Lemma type_reduction {Σ Γ t A B}
    : wf Σ.1 -> wf_local Σ Γ -> Σ ;;; Γ |- t : A -> red (fst Σ) Γ A B -> Σ ;;; Γ |- t : B.
  Proof.
    intros HΣ' HΓ Ht Hr.
    econstructor. eassumption.
    2: now eapply cumul_red_l'.
    destruct (validity_term HΣ' HΓ Ht).
    - left. eapply isWfArity_red; try eassumption.
    - destruct i as [s HA]. right.
      exists s. eapply subject_reduction; eassumption.
  Defined.

End SRContext.
