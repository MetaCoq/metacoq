(* Distributed under the terms of the MIT license.   *)
Set Warnings "-notation-overridden".

Require Import Equations.Prop.DepElim.
From Coq Require Import Bool String List Lia Arith.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICUtils
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICWeakeningEnv PCUICWeakening
     PCUICSubstitution PCUICClosed PCUICCumulativity PCUICGeneration PCUICReduction
     PCUICAlpha PCUICEquality PCUICValidity PCUICParallelReductionConfluence
     PCUICConfluence PCUICContextConversion PCUICUnivSubstitution
     PCUICConversion PCUICInversion PCUICContexts PCUICArities
     PCUICParallelReduction PCUICSpine PCUICInductives
     PCUICCtxShape.
     
Close Scope string_scope.

Require Import ssreflect. 

Set Asymmetric Patterns.
Set SimplIsCbn.

From Equations Require Import Equations.

Derive Signature for OnOne2_local_env.

Ltac rename_hyp h ht ::= my_rename_hyp h ht.
Ltac pcuic := intuition eauto 5 with pcuic ||
  (try solve [repeat red; cbn in *; intuition auto; eauto 5 with pcuic || (try lia || congruence)]).

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
  destruct s0 as [cshape [Hsorc Hc]].
  destruct Hc as [_ chead cstr_eq [cs Hcs] _ _].
  destruct cshape. rewrite /cdecl_type in cstr_eq.
  rewrite cstr_eq in Hs. clear -declc Hs.
  rewrite /subst1 !subst_instance_constr_it_mkProd_or_LetIn
  !subst_it_mkProd_or_LetIn in Hs.
  rewrite !subst_instance_constr_mkApps !subst_mkApps in Hs.
  rewrite !subst_instance_context_length Nat.add_0_r in Hs.
  rewrite subst_inds_concl_head in Hs.
  + simpl. destruct declc as [[onm oni] ?].
    now eapply nth_error_Some_length in oni.
  + now rewrite !destArity_it_mkProd_or_LetIn destArity_app /= destArity_tInd in Hs.
Qed.

Lemma on_constructor_subst' {cf:checker_flags} Σ ind mdecl idecl cshape cdecl : 
  wf Σ -> 
  declared_inductive Σ mdecl ind idecl ->
  on_inductive (lift_typing typing) (Σ, ind_universes mdecl) (inductive_mind ind) mdecl ->
  forall (oib : on_ind_body (lift_typing typing) (Σ, ind_universes mdecl) (inductive_mind ind) mdecl 
           (inductive_ind ind) idecl)
        (onc : on_constructor (lift_typing typing) (Σ, ind_universes mdecl)
          mdecl (inductive_ind ind) idecl (ind_indices oib) cdecl cshape),
  wf_global_ext Σ (ind_universes mdecl) *
  wf_local (Σ, ind_universes mdecl)
   (arities_context (ind_bodies mdecl) ,,, ind_params mdecl ,,, cshape_args cshape) *
  ctx_inst (Σ, ind_universes mdecl)
             (arities_context (ind_bodies mdecl) ,,, ind_params mdecl ,,,
              cshape_args cshape)
             (cshape_indices cshape) 
            (List.rev (lift_context #|cshape_args cshape| 0 (ind_indices oib))). 
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

Lemma on_constructor_subst {cf:checker_flags} Σ ind mdecl idecl cshape cdecl : 
  wf Σ -> 
  declared_inductive Σ mdecl ind idecl ->
  on_inductive (lift_typing typing) (Σ, ind_universes mdecl) (inductive_mind ind) mdecl ->
  forall (oib : on_ind_body (lift_typing typing) (Σ, ind_universes mdecl) (inductive_mind ind) mdecl 
           (inductive_ind ind) idecl)
        (onc : on_constructor (lift_typing typing) (Σ, ind_universes mdecl)
          mdecl (inductive_ind ind) idecl (ind_indices oib) cdecl cshape),
  wf_global_ext Σ (ind_universes mdecl) *
  wf_local (Σ, ind_universes mdecl)
   (arities_context (ind_bodies mdecl) ,,, ind_params mdecl ,,, cshape_args cshape) *
  ∑ inst,
  spine_subst (Σ, ind_universes mdecl)
             (arities_context (ind_bodies mdecl) ,,, ind_params mdecl ,,,
              cshape_args cshape)
             ((to_extended_list_k (ind_params mdecl) #|cshape_args cshape|) ++
              (cshape_indices cshape)) inst
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
  rewrite onc.(cstr_eq) in t.
  rewrite -it_mkProd_or_LetIn_app in t.
  eapply inversion_it_mkProd_or_LetIn in t => //.
  unfold cstr_concl_head in t. simpl in t.
  eapply inversion_mkApps in t as [A [U [ta [sp cum]]]].
  eapply inversion_Rel in ta as [decl [wfΓ [nth cum']]].
  rewrite nth_error_app_ge in nth. autorewrite with len. lia.
  autorewrite with len in nth.
  all:auto.
  assert ( (#|ind_bodies mdecl| - S (inductive_ind ind) + #|ind_params mdecl| +
  #|cshape_args cshape| -
  (#|cshape_args cshape| + #|ind_params mdecl|)) = #|ind_bodies mdecl| - S (inductive_ind ind)) by lia.
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

Lemma on_constructor_inst {cf:checker_flags} Σ ind u mdecl idecl cshape cdecl : 
  wf Σ.1 -> 
  declared_inductive Σ.1 mdecl ind idecl ->
  on_inductive (lift_typing typing) (Σ.1, ind_universes mdecl) (inductive_mind ind) mdecl ->
  forall (oib : on_ind_body (lift_typing typing) (Σ.1, ind_universes mdecl) (inductive_mind ind) mdecl 
           (inductive_ind ind) idecl)
        (onc : on_constructor (lift_typing typing) (Σ.1, PCUICAst.ind_universes mdecl)
          mdecl (inductive_ind ind) idecl (ind_indices oib) cdecl cshape), 
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  wf_local Σ (subst_instance_context u
    (arities_context (ind_bodies mdecl) ,,, ind_params mdecl ,,, cshape_args cshape)) *
  ∑ inst,
  spine_subst Σ
          (subst_instance_context u
             (arities_context (ind_bodies mdecl) ,,, ind_params mdecl ,,,
              cshape_args cshape))
          (map (subst_instance_constr u)
             (to_extended_list_k (ind_params mdecl) #|cshape_args cshape|) ++
           map (subst_instance_constr u) (cshape_indices cshape)) inst
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
    eapply red_mkApps_tInd in r as [? [eq ?]]; auto. solve_discr.
    exists nil.
    intuition auto. clear i0.
    revert args' a. clear -b wfΣ wfΓ. induction b; intros args' H; depelim H; constructor.
    rewrite subst_empty.
    transitivity y; auto. symmetry.
    now eapply red_conv. now eauto.
    eapply invert_cumul_prod_r in c as [? [? [? [[? ?] ?]]]]; auto.
    eapply red_mkApps_tInd in r as [? [eq ?]]; auto. now solve_discr.
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
      eapply red_mkApps_tInd in r as [? [eq ?]]; auto. now solve_discr.
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
      exists (isub ++ [hd])%list. rewrite List.rev_app_distr.
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

Lemma Construct_Ind_ind_eq {cf:checker_flags} {Σ} (wfΣ : wf Σ.1):
  forall {Γ n i args u i' args' u' mdecl idecl cdecl},
  Σ ;;; Γ |- mkApps (tConstruct i n u) args : mkApps (tInd i' u') args' ->
  forall (Hdecl : declared_constructor Σ.1 mdecl idecl (i, n) cdecl),
  let '(onind, oib, existT cshape (hnth, onc)) := on_declared_constructor wfΣ Hdecl in
  (i = i') * 
  (* Universe instances match *)
  R_universe_instance (eq_universe (global_ext_constraints Σ)) u u' *
  consistent_instance_ext Σ (ind_universes mdecl) u' *    
  (#|args| = (ind_npars mdecl + context_assumptions cshape.(cshape_args))%nat) *
  ∑ parsubst argsubst parsubst' argsubst',
    let parctx := (subst_instance_context u (ind_params mdecl)) in
    let parctx' := (subst_instance_context u' (ind_params mdecl)) in
    let argctx := (subst_context parsubst 0
    ((subst_context (inds (inductive_mind i) u mdecl.(ind_bodies)) #|ind_params mdecl|
    (subst_instance_context u cshape.(cshape_args))))) in
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
      subst (inds (inductive_mind i) u mdecl.(ind_bodies)) (#|cshape.(cshape_args)| + #|ind_params mdecl|)
      ∘ (subst_instance_constr u)) 
        cshape.(cshape_indices))
      (skipn mdecl.(ind_npars) args')).

Proof.
  intros Γ n i args u i' args' u' mdecl idecl cdecl h declc.
  unfold on_declared_constructor.
  destruct (on_declared_constructor _ declc). destruct s as [? [_ onc]].
  unshelve epose proof (env_prop_typing _ _ validity _ _ _ _ _ h) as vi'; eauto using typing_wf_local.
  eapply inversion_mkApps in h; auto.
  destruct h as [T [U [hC [hs hc]]]].
  apply inversion_Construct in hC
    as [mdecl' [idecl' [cdecl' [hΓ [isdecl [const htc]]]]]]; auto.
  assert (vty:=declared_constructor_valid_ty _ _ _ _ _ _ _ _ wfΣ hΓ isdecl const). 
  eapply typing_spine_strengthen in hs. 3:eapply htc. all:eauto.
  eapply typing_spine_weaken_concl in hs.
  3:{ eapply cumul_trans; eauto with pcuic. } all:auto.
  clear hc htc.
  destruct (declared_constructor_inj isdecl declc) as [? [? ?]].
  subst mdecl' idecl' cdecl'. clear isdecl.
  destruct p as [onmind onind]. clear onc.
  destruct declc as [decli declc].
  remember (on_declared_inductive wfΣ decli). clear onmind onind.
  destruct p.
  rename o into onmind. rename o0 into onind.
  destruct declared_constructor_inv as [cshape [_ onc]].
  simpl in onc. unfold on_declared_inductive in Heqp.
  injection Heqp. intros indeq _. 
  move: onc Heqp. rewrite -indeq.
  intros onc Heqp. clear Heqp. simpl in onc.
  pose proof (on_constructor_inst _ _ _ _ _ _ _ wfΣ decli onmind onind onc const).
  destruct onc as [argslength conclhead cshape_eq [cs' t] cargs cinds]; simpl.
  simpl in *. 
  unfold type_of_constructor in hs. simpl in hs.
  unfold cdecl_type in cshape_eq.
  rewrite cshape_eq in hs.  
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
    red in onParams. now apply closed_wf_local in onParams. }
  eapply mkApps_ind_typing_spine in hs as [isubst [[[Hisubst [Hargslen [Hi Hu]]] Hargs] Hs]]; auto.
  subst i'.
  eapply (isWAT_mkApps_Ind wfΣ decli) in vi' as (parsubst & argsubst & (spars & sargs) & cons) => //.
  unfold on_declared_inductive in sargs. simpl in sargs. rewrite -indeq in sargs. clear indeq.
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
    eapply (weaken_subslet _ _ _ _ []) => //.
    now eapply subslet_inds; eauto.
    rewrite -app_context_assoc.
    eapply weaken_wf_local => //.
    rewrite -subst_instance_context_app. 
    apply a.
  - exists (subst_instance_univ u (cshape_sort cshape)). split.
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
    eapply (weaken_subslet _ _ _ _ []) => //.
    now eapply subslet_inds; eauto.
    now rewrite closed_ctx_subst ?closedn_subst_instance_context.

    move: (All2_firstn  _ _ _ _ _ mdecl.(ind_npars) Hargs).
    move: (All2_skipn  _ _ _ _ _ mdecl.(ind_npars) Hargs).
    clear Hargs.
    rewrite !map_map_compose !map_app.
    rewrite -map_map_compose.
    rewrite (firstn_app_left _ 0).
    { rewrite !map_length to_extended_list_k_length. lia. }
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
    rewrite -[map _ (to_extended_list_k _ _)]
               (map_map_compose _ _ _ (subst_instance_constr u)
                              (fun x => subst _ _ (subst _ _ x))).
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
    rewrite cshape_eq in vty. move: vty.
    rewrite !subst_instance_constr_it_mkProd_or_LetIn.
    rewrite !subst_it_mkProd_or_LetIn subst_instance_context_length Nat.add_0_r.
    rewrite subst_instance_constr_mkApps subst_mkApps subst_instance_context_length.
    rewrite subst_inds_concl_head. all:simpl; auto.
Qed.

Notation "⋆" := ltac:(solve [pcuic]) (only parsing).

Lemma build_branches_type_red {cf:checker_flags} (p p' : term) (ind : inductive)
	(mdecl : PCUICAst.mutual_inductive_body)
    (idecl : PCUICAst.one_inductive_body) (pars : list term) 
    (u : Instance.t) (brtys : list (nat × term)) Σ Γ :
  wf Σ ->
  red1 Σ Γ p p' ->
  map_option_out (build_branches_type ind mdecl idecl pars u p) = Some brtys ->
  ∑ brtys' : list (nat × term),
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
  now apply All2_length in X.
  constructor => //.
  eapply (context_relation_impl (P:= (fun Δ Δ' : PCUICAst.context =>
  conv_decls Σ
  (Γ ,,, (vass (dname x) (lift0 #|Γ'| (dtype x)) :: Γ') ,,, Δ)
  (Γ ,,, (vass (dname y) (lift0 #|Γ''| (dtype y)) :: Γ'') ,,, Δ')))).
  intros. now rewrite !app_context_assoc.
  eapply IHX. simpl.
  constructor => //.
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

Lemma isLambda_red1 Σ Γ b b' : isLambda b -> red1 Σ Γ b b' -> isLambda b'.
Proof.
  destruct b; simpl; try discriminate.
  intros _ red.
  depelim red.
  symmetry in H; apply mkApps_Fix_spec in H. simpl in H. intuition.
  constructor. constructor.
Qed.

Lemma ctx_inst_closed {cf:checker_flags} Σ Γ i Δ : 
  wf Σ.1 -> ctx_inst Σ Γ i Δ -> All (closedn #|Γ|) i.
Proof.
  intros wfΣ; induction 1; auto; constructor; auto.
  now eapply subject_closed in p.
Qed.

Lemma typing_spine_nth_error {cf:checker_flags} {Σ Γ Δ T args n arg concl} : 
  wf Σ.1 ->
  isWfArity_or_Type Σ Γ (it_mkProd_or_LetIn Δ T) ->
  typing_spine Σ Γ (it_mkProd_or_LetIn Δ T) args concl ->
  nth_error args n = Some arg ->
  (n < context_assumptions Δ) ->
  ∑ decl, (nth_error (smash_context [] Δ) (context_assumptions Δ - S n) = Some decl) * 
    (Σ ;;; Γ |- arg : subst0 (List.rev (firstn n args)) (decl_type decl)).
Proof.
  intros wfΣ. revert n args T.
  induction Δ using ctx_length_rev_ind => /= // n args T.
  - simpl. lia.
  - rewrite it_mkProd_or_LetIn_app context_assumptions_app.
    destruct d as [na [b|] ty]; simpl.
    + move=> wat. rewrite /= Nat.add_0_r. simpl.
      move=>  sp.
      eapply typing_spine_letin_inv in sp => //.
      eapply isWAT_tLetIn_red in wat => //.
      rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r in sp, wat.
      specialize (X (subst_context [b] 0 Γ0) ltac:(autorewrite with len; lia) n args _ wat sp).
      rewrite context_assumptions_subst in X.
      move=> Hnth Hn. specialize (X Hnth Hn) as [decl [nthsmash Hty]].
      exists decl; split; auto.
      rewrite smash_context_app. simpl.
      now rewrite -(smash_context_subst []) /= subst_context_nil.
      now eapply isWAT_wf_local in wat.
    + simpl.
      move=> wat sp.
      depelim sp. rewrite nth_error_nil //.
      destruct n as [|n']; simpl.
      * move=> [=] eq; subst hd.
        move=> Hctx. exists {| decl_name := na; decl_body := None; decl_type := ty |}.
        rewrite smash_context_app. simpl.
        rewrite nth_error_app_ge; rewrite smash_context_length /=. lia.
        assert(context_assumptions Γ0 + 1 - 1 - context_assumptions Γ0 = 0) as -> by lia.
        split; auto. rewrite subst_empty.
        pose proof (isWAT_wf_local i).
        eapply cumul_Prod_inv in c as [conv cum]; auto.
        eapply type_Cumul; eauto.
        eapply isWAT_tProd in wat as [dom codom]; auto.
        now apply conv_cumul, conv_sym.
      * move=> Hnth Hn'.
        pose proof  (isWAT_wf_local i).
        eapply isWAT_tProd in wat as [dom' codom']; auto.
        eapply cumul_Prod_inv in c as [conv cum]; auto.
        unshelve eapply (isWAT_subst wfΣ (Δ:=[vass na ty]) _ [hd]) in codom'.
        constructor; auto.
        2:{ repeat constructor. rewrite subst_empty.
            eapply type_Cumul; eauto. now eapply conv_cumul, conv_sym. }
        specialize (X (subst_context [hd] 0 Γ0) ltac:(autorewrite with len; lia)).
        unshelve eapply (substitution_cumul0 _ _ _ _ _ _ hd) in cum; auto.
        rewrite subst_it_mkProd_or_LetIn in codom'.
        specialize (X n' tl _ codom').
        forward X.
        rewrite -subst_it_mkProd_or_LetIn.
        eapply typing_spine_strengthen; eauto.
        rewrite /subst1 in cum.
        specialize (X Hnth).
        forward X by (rewrite context_assumptions_subst; lia).
        destruct X as [decl [Hnth' Hty]].
        rewrite (smash_context_subst []) nth_error_subst_context in Hnth'.
        rewrite smash_context_app. simpl.
        rewrite context_assumptions_subst in Hnth'.
        replace (context_assumptions Γ0  + 1 - S (S n')) with
          (context_assumptions Γ0 - S n') by lia.
        rewrite nth_error_app_context_lt ?smash_context_length. lia.
        destruct (nth_error (smash_context [] Γ0) _) eqn:Heq; try discriminate.
        simpl in Hnth'. exists c; split; auto.
        noconf Hnth'. 
        rewrite /= smash_context_length /= in Hty.
        replace ((context_assumptions Γ0 - S (context_assumptions Γ0 - S n') + 0))
          with n' in Hty by lia.
        rewrite subst_app_simpl /= List.rev_length firstn_length_le.
        now eapply nth_error_Some_length in Hnth.
        assumption.
Qed.

Hint Rewrite smash_context_length Nat.add_0_r List.rev_length extended_subst_length 
  projs_length : len.

Lemma extended_subst_subst_instance_constr u Γ n :
  map (subst_instance_constr u) (extended_subst Γ n) =
  extended_subst (subst_instance_context u Γ) n.
Proof.
  induction Γ as [|[?[]?] ?] in n |- *; simpl; auto.
  - autorewrite with len.
    f_equal; auto.
    rewrite -subst_subst_instance_constr.
    rewrite -lift_subst_instance_constr.
    rewrite subst_instance_context_assumptions.
    f_equal. apply IHΓ.
  - f_equal; auto.
Qed.

Lemma subst_instance_constr_projs u i p n :
  map (subst_instance_constr u) (projs i p n) = projs i p n.
Proof.
  induction n; simpl; auto. f_equal; auto.
Qed.

Lemma subslet_skipn {cf:checker_flags} Σ Γ s Δ n : 
  subslet Σ Γ s Δ ->
  subslet Σ Γ (skipn n s) (skipn n Δ).
Proof.
  induction n in s, Δ |- *.
  - now rewrite !skipn_0.
  - intros H; depelim H.
    * rewrite !skipn_nil. constructor.
    * rewrite !skipn_S. auto.
    * rewrite !skipn_S. auto.
Qed.

Lemma untyped_subslet_skipn Γ s Δ n : 
  untyped_subslet Γ s Δ ->
  untyped_subslet Γ (skipn n s) (skipn n Δ).
Proof.
  induction n in s, Δ |- *.
  - now rewrite !skipn_0.
  - intros H; depelim H.
    * rewrite !skipn_nil. constructor.
    * rewrite !skipn_S. auto.
    * rewrite !skipn_S. auto.
Qed.

Lemma untyped_subslet_eq_subst Γ s s' Δ : 
  untyped_subslet Γ s Δ -> s = s' ->
  untyped_subslet Γ s' Δ.
Proof. now intros H ->. Qed.

Lemma subslet_projs {cf:checker_flags} (Σ : global_env_ext) Γ u i mdecl idecl args0 :
  forall (wfΣ : wf Σ.1) 
  (Hdecl : declared_inductive Σ.1 mdecl i idecl),
  let oib := declared_inductive_inv weaken_env_prop_typing wfΣ wfΣ Hdecl in
  let indsubst := inds (inductive_mind i) u (ind_bodies mdecl) in
  match ind_cshapes oib return Type with
  | [cs] => 
    on_projections mdecl (inductive_mind i) (inductive_ind i) 
     idecl (ind_indices oib) cs -> 
  untyped_subslet (Γ ,,,
   subst_context indsubst 0
     (subst_instance_context u (PCUICEnvironment.ind_params mdecl)))
  (map
     (fun x : term =>
        (subst0
              [mkApps (tConstruct i 0 u)
                 (map (lift0 #|ind_params mdecl|) args0)] x))
     (projs i (ind_npars mdecl) (context_assumptions (cshape_args cs))))
     (smash_context []
        (subst_context (inds (inductive_mind i) u (ind_bodies mdecl))
           #|ind_params mdecl| (subst_instance_context u (cshape_args cs))))
  | _ => True
  end.
Proof.
  intros wfΣ Hdecl oib indsubst.
  destruct ind_cshapes as [|cs []] eqn:Heq; trivial.
  intros onp.
  rewrite (smash_context_subst []).
  destruct onp.
  assert (#|PCUICEnvironment.ind_projs idecl| >=
  PCUICEnvironment.context_assumptions (cshape_args cs)). lia.
  clear on_projs_all.
  induction (cshape_args cs) as [|[? [] ?] ?].
  - simpl. constructor.
  - simpl. apply IHc. now simpl in H.
  - simpl. rewrite smash_context_acc /=.
    rewrite subst_context_snoc.
    rewrite /subst_decl {2}/map_decl /=.
    simpl in H. constructor. apply IHc. lia.
Qed.

Lemma skipn_projs n i npars k : 
  skipn n (projs i npars k) = projs i npars (k - n).
Proof.
  induction k in n |- *; simpl.
  - now rewrite skipn_nil.
  - destruct n. now rewrite skipn_0.
    now  rewrite skipn_S.
Qed.

Fixpoint projs_inst ind npars k x : list term :=
  match k with
  | 0 => []
  | S k' => tProj (ind, npars, k') x :: projs_inst ind npars k' x
  end.

Lemma subst_projs_inst ind npars k x : map (subst0 [x]) (projs ind npars k) = projs_inst ind npars k x.
Proof.
  induction k; simpl; auto.
  rewrite lift0_id. f_equal; auto.
Qed.

Lemma projs_inst_length ind npars k x : #|projs_inst ind npars k x| = k.
Proof. induction k; simpl; auto. Qed.

Hint Rewrite projs_inst_length : len.

Lemma projs_inst_lift ind npars k x n : 
  projs_inst ind npars k (lift0 n x) = 
  map (lift0 n) (projs_inst ind npars k x).
Proof.
  induction k; simpl; auto.
  f_equal; auto.
Qed.

Lemma nth_error_projs_inst ind npars k x n :
  n < k ->
  nth_error (projs_inst ind npars k x) n = Some (tProj (ind, npars, k - S n) x).
Proof.
  induction k in n |- *; simpl; auto. lia.
  destruct n.
  + simpl. now rewrite Nat.sub_0_r.
  + intros Hlt. simpl. apply IHk; lia.  
Qed.

Lemma simpl_lift_ext n k p i :
  i <= k + n -> k <= i ->
  lift p i ∘ lift n k =1 lift (p + n) k.
Proof. intros ? ? ?; now apply simpl_lift. Qed.

Lemma map_subst_lift_ext N n p k l :
  k = #|N| -> p <= n ->
  map (subst N p ∘ lift0 (k + n)) l = map (lift0 n) l.
Proof.
  intros -> pn.
  apply map_ext => x. now apply simpl_subst'.
Qed.

Lemma closed_map_subst_instance n u l : 
  forallb (closedn n) (map (subst_instance_constr u) l) = 
  forallb (closedn n) l.
Proof.
  induction l; simpl; auto.
  now rewrite closedn_subst_instance_constr IHl.
Qed.

Lemma skipn_mapi_rec {A B} n (f : nat -> A -> B) k (l : list A) : 
  skipn n (mapi_rec f l k) = 
  mapi_rec f (skipn n l) (n + k).
Proof.
  induction n in f, l, k |- *.
  - now rewrite !skipn_0.
  - destruct l.
    * simpl. rewrite !skipn_nil. reflexivity.
    * simpl. rewrite !skipn_S IHn.
      now rewrite Nat.add_succ_r.
Qed.

Lemma skipn_subst_context n s k Γ : skipn n (subst_context s k Γ) = 
  subst_context s k (skipn n Γ).
Proof.
  rewrite !subst_context_alt.
  rewrite skipn_mapi_rec. rewrite mapi_rec_add /mapi.
  apply mapi_rec_ext. intros.
  f_equal.
  rewrite List.skipn_length. lia.
Qed.

Lemma instantiate_inds {cf:checker_flags} Σ u mind mdecl :
  wf Σ.1 ->
  declared_minductive Σ.1 mind mdecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  subst_instance u
     (inds mind (PCUICLookup.abstract_instance (PCUICEnvironment.ind_universes mdecl))
        (ind_bodies mdecl)) = 
  inds mind u (ind_bodies mdecl).
Proof.
  intros wfΣ declm cu.
  rewrite subst_instance_inds.
  f_equal. apply subst_instance_instance_id.
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
    specialize (inversion_mkApps wf typet) as [T' [U' [appty [spty Hcumul]]]].
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
    destruct (declared_inductive_inj isdecl decli) as []; subst mdecl' idecl'.
    set(oib := declared_inductive_inv _ _ _ _) in *. clearbody oib.
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
    destruct brtys as [-> brtys].
    specialize (brtys  _ csubst).
    simpl in brtys. subst brty.
    eapply type_mkApps. eauto.
    set argctx := cshape_args cs.
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
          (cshape_indices cs) ++
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
           (cshape_indices cs) ++
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
    (cshape_indices cs)) in *.

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
      eexists.
      assert(wfparinds : wf_local Σ
        (subst_instance_context u (ind_params mdecl) ,,,
          subst_instance_context u (ind_indices oib))). 
      { unshelve epose proof (on_minductive_wf_params_indices_inst _ _ u _ _ wf _ oib cu); pcuic.
        now rewrite -subst_instance_context_app. }
      assert(wfΓparinds : wf_local Σ
        (Γ ,,, subst_instance_context u (ind_params mdecl) ,,,
          subst_instance_context u (ind_indices oib))). 
      { rewrite -app_context_assoc.
        eapply weaken_wf_local; auto. }
      assert(wfparinds' : wf_local Σ (subst_instance_context u1 (ind_params mdecl) ,,,
          subst_instance_context u1 (ind_indices oib))).
      { unshelve epose proof (on_minductive_wf_params_indices_inst _ _ u1 _ _ wf _ oib Hu); pcuic.
        now rewrite -subst_instance_context_app. }
      assert(wfΓparinds' : wf_local Σ
        (Γ ,,, subst_instance_context u1 (ind_params mdecl) ,,,
          subst_instance_context u1 (ind_indices oib))).
      { rewrite -app_context_assoc. eapply weaken_wf_local; auto. }
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
        red.
        { exists (subst_instance_univ u1 (ind_sort oib)).
          eapply type_mkApps. econstructor; eauto.
          eapply substitution_wf_local; eauto. eapply cparsubst0.
          eapply wf_arity_spine_typing_spine; auto.
          split.
          + pose proof oib.(onArity). right. red in X.
            destruct X.
            eapply (instantiate_minductive _ _ _ u1) in t; eauto.
            eexists. eapply weaken_ctx in t. simpl in t. eapply t; eauto.
            all:pcuic. eapply substitution_wf_local; eauto. eapply cparsubst0.
          + rewrite oib.(ind_arity_eq).
            rewrite subst_instance_constr_it_mkProd_or_LetIn.
            eapply arity_spine_it_mkProd_or_LetIn => //.
            eapply (spine_subst_weakening _ _ _ _ _ 
             (subst_context cparsubst 0 (subst_instance_context u1 (ind_indices oib)))) in cparsubst0 => //.
            autorewrite with len in cparsubst0.
            rewrite closed_ctx_lift in cparsubst0.
            now eapply closed_wf_local. apply cparsubst0.
            eapply substitution_wf_local; eauto. apply cparsubst0.
            rewrite subst_instance_constr_it_mkProd_or_LetIn subst_it_mkProd_or_LetIn /=.
            rewrite -(app_nil_r (to_extended_list _)).
            eapply arity_spine_it_mkProd_or_LetIn => //.
            epose proof (spine_subst_to_extended_list_k Σ (subst_context cparsubst 0 (subst_instance_context u1 (ind_indices oib)))
                Γ wf). forward X.
            eapply substitution_wf_local; eauto. apply cparsubst0.
            autorewrite with len in X. 
            fold (to_extended_list_k (subst_context cparsubst 0
               (subst_instance_context u1 (ind_indices oib))) 0) in X.
            rewrite to_extended_list_k_fold_context in X.
            rewrite distr_lift_subst_context in X.
            rewrite closed_ctx_lift in X. rewrite Nat.add_0_r.
            rewrite (subslet_length cparsubst0) subst_instance_context_length.
            apply closed_wf_local in wfparinds' => //.
            rewrite closedn_ctx_app in wfparinds'.
            autorewrite with len in wfparinds'. now move/andP: wfparinds' => [_ ?].
            now rewrite PCUICSubstitution.map_subst_instance_constr_to_extended_list_k in X.
            simpl. constructor. left; eexists _, _; intuition eauto. simpl.
            eapply substitution_wf_local; eauto; apply cparsubst0.
            reflexivity. }
        eapply cumul_it_mkProd_or_LetIn => //.
        eapply context_relation_subst => //. 2:eapply iparsubst0. 2:eapply cparsubst0. auto.
        eapply spine_subst_conv; eauto. eapply context_relation_subst_instance; eauto.
        now symmetry. now symmetry.
        rewrite - !subst_instance_context_app.
        eapply context_relation_subst_instance; eauto.
        eapply on_minductive_wf_params_indices_inst => //. destruct decli; eauto.
        now symmetry.
        eapply congr_cumul_prod; eauto.
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
      
      eapply (ctx_inst_inst _ _ u1) in insts; eauto.
      rewrite !subst_instance_context_app in insts.
      assert(closedindices : All (fun x => closedn (#|cshape_args cs| + #|ind_params mdecl|) x)
        (map
      (subst
         (inds (inductive_mind (ind, c0).1) u1
            (PCUICAst.ind_bodies mdecl))
         (#|cshape_args cs| + #|ind_params mdecl|))
      (map (subst_instance_constr u1) (cshape_indices cs)))).
      { rewrite -[_ ,,, _ ,,, _](app_context_nil_l _) in insts.
        rewrite -[subst_instance_context _ _ ,,, _ ,,, _]app_context_assoc in insts.
        rewrite app_context_assoc in insts.
        eapply (ctx_inst_subst _ []) in insts => //.
        2:{ eapply subslet_inds => //. pcuic. }
        rewrite app_context_nil_l in insts.
        autorewrite with len in insts.
        apply ctx_inst_closed in insts => //.
        now autorewrite with len in insts. }

      eapply (ctx_inst_weaken _ _ _ _ Γ) in insts => //.
      rewrite app_context_assoc in insts.
      eapply ctx_inst_subst in insts => //.
      2:{ eapply subslet_app. 2:{ eapply (weaken_subslet _ _ _ _ []) => //. eapply subslet_inds => //. pcuic. }
          rewrite closed_ctx_subst => //. eapply cparsubst0. }          
      rewrite subst_app_context in insts.
      rewrite subst_instance_context_rev in insts.
      rewrite subst_telescope_subst_context in insts.
      autorewrite with len in insts. simpl in insts.
      unshelve epose proof (ctx_inst_spine_subst _ _  _ _ wf _  _ insts) as instsp; eauto.
      { rewrite -lencpar. apply (spine_codom_wf _ _ _ _ _ idxsubst0). }
      { rewrite -lencpar.
        have w := spine_codom_wf _ _ _ _ _ idxsubst0.
        assert(wf_local Σ (subst_instance_context u1 (arities_context (ind_bodies mdecl)))).
        { eapply (wf_local_instantiate _ (InductiveDecl mdecl));pcuic. destruct isdecl; eauto.
          simpl. rewrite -app_context_assoc in wfc; now apply All_local_env_app in wfc. }
        eapply (weaken_wf_local (subst_instance_context u1 (arities_context (ind_bodies mdecl)))) in wfparinds'; eauto.
        rewrite app_context_assoc in wfparinds'.
        eapply (weaken_wf_local Γ) in wfparinds'; eauto.
        rewrite app_context_assoc in wfparinds'.
        unshelve epose proof (substitution_wf_local _ _ _ _ _ wf _ wfparinds') as w'. shelve.
        eapply subslet_app; first last. eapply (weaken_subslet _ _ _ _ []); eauto. eapply subslet_inds; eauto.
        rewrite closed_ctx_subst. auto. eapply cparsubst0.
        move: (weakening_wf_local _ _ _ _ wf w' w).
        autorewrite with len.
        clear -w lencpar. rewrite lencpar.
        rewrite -subst_app_context. rewrite lift_context_subst_context.
        now rewrite -subst_instance_lift_context. }
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

      assert((map (subst (cparsubst ++ inds (inductive_mind ind) u1 (PCUICAst.ind_bodies mdecl)) #|cshape_args cs|)
      (map (subst_instance_constr u1) (cshape_indices cs))) = 
      (map
      (fun x : term =>
      subst cparsubst #|argctx|
        (subst (inds (inductive_mind ind) u1 (ind_bodies mdecl)) (#|argctx| + #|cparsubst|) (subst_instance_constr u1 x)))
     (cshape_indices cs))).
      rewrite map_map_compose. apply map_ext=> x.
      now rewrite subst_app_simpl.
      rewrite H0 in insts, instsp. clear H0.

      apply wf_arity_spine_typing_spine => //.
      split.
      ** left.
         eexists _, _.
         rewrite destArity_it_mkProd_or_LetIn /=. split; [reflexivity|].
         rewrite app_context_nil_l. simpl.         
         constructor; auto. apply (spine_codom_wf _ _ _ _ _ instsp).
         red.
         autorewrite with len.
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
         unshelve epose proof (declared_constructor_valid_ty _ _ _ _ _ _ _ u1 wf (spine_dom_wf _ _ _ _ _ instsp) _ Hu); eauto.
         split; eauto.
         right; eauto.
         
         unfold type_of_constructor.
         rewrite {1}[cdecl'.1.2]onc.(cstr_eq).
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
              pose proof (substitution_wf_local Σ [] (subst_instance_context u1 (arities_context (ind_bodies mdecl)))).
              specialize (X (inds (inductive_mind ind) u1 (ind_bodies mdecl))
                (subst_instance_context u1 (ind_params mdecl) ,,, (map_context (subst_instance_constr u1) argctx)) wf).
              rewrite app_context_nil_l in X.
              forward X by eapply subslet_inds; eauto.
              rewrite app_context_assoc in X.
              specialize(X wfc). rewrite app_context_nil_l in X.
              eapply closed_wf_local in X; eauto.
              rewrite subst_context_app in X.
              rewrite closedn_ctx_app in X.
              autorewrite with len in X. simpl in X.
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
              rewrite !map_map_compose {}H0.
              assert ((map (subst0 (ctx_inst_sub insts) ∘ lift #|argctx| #|ind_indices oib|)
                (to_extended_list_k (ind_indices oib) 0)) = 
              (map
              (fun x : term =>
                subst cparsubst #|argctx|
                  (subst (inds (inductive_mind ind) u1 (ind_bodies mdecl))
                    (#|argctx| + #|cparsubst|) (subst_instance_constr u1 x)))
              (cshape_indices cs))).
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
              rewrite /cstr_concl_head.
              rewrite subst_inds_concl_head.
              { simpl. destruct decli. now eapply nth_error_Some_length in H2. }
              simpl. apply mkApps_conv_args; auto.
               
              rewrite map_app. eapply All2_app.
              ****
                eapply (All2_impl (P:=fun x y => x = y)).
                2:{ intros ? ? ->. reflexivity. }
                eapply All2_eq_eq.
                rewrite -(map_map_compose _ _ _ (subst_instance_constr _)
                                          (fun x => subst _ _ (subst _ _ x))).
                rewrite subst_instance_to_extended_list_k.
                rewrite -(map_map_compose _ _ _ (subst _ _)).
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
                rewrite -(map_map_compose _ _ _ (subst_instance_constr u1)).
                rewrite -(map_map_compose _ _ _
                                          (subst _ _ ∘ (subst_instance_constr u1))).
                rewrite map_map_compose.
                eapply All2_map. rewrite -lencpar.
                rewrite !map_map_compose.
                assert (All (fun x => closedn (#|cparsubst| + #|instargctx|) x) (map
                (subst (inds (inductive_mind ind) u1 (PCUICAst.ind_bodies mdecl))
                   (#|cshape_args cs| + #|ind_params mdecl|)
                 ∘ subst_instance_constr u1) (cshape_indices cs))).
                { rewrite map_map_compose in closedindices.
                  eapply (All_impl closedindices).
                  intros. now rewrite -lencpar H0 Nat.add_comm. }  
                apply (All_All2 X).
                intros. rewrite all_rels_length.
                pose proof (all_rels_subst Σ instargctx Γ (subst cparsubst #|argctx| x) wf (spine_dom_wf _ _ _ _ _ instsp)).
                eapply red_conv in X0.
                assert(subst (map (lift0 #|argctx|) cparsubst) #|instargctx| x =
                  (lift #|argctx| #|argctx| (subst cparsubst #|argctx| x))).
                { epose proof (distr_lift_subst_rec _ _ #|argctx| #|argctx| 0) as l.
                  rewrite Nat.add_0_r in l. rewrite -> l. f_equal. now rewrite H0.
                  rewrite H0 in H2. subst argctx.
                  rewrite lift_closed. eapply closed_upwards; eauto. lia. reflexivity. }
                rewrite H3.
                rewrite H0 in X0.
                symmetry in X0.
                apply X0.

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
    eapply inversion_mkApps in typec as [? [? [tcof [_ _]]]] =>  //.
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
    eapply (OnOne2_All2_All2 o X5).
    intros [] []; simpl. intros.
    intuition auto. subst.
    intros [] [] []; simpl. intros.
    intuition auto. subst.    
    reflexivity.

  - (* Proj CoFix congruence *)
    pose proof (env_prop_typing _ _  validity _ _ _ _ _ typec).
    eapply inversion_mkApps in typec as [? [? [tcof [tsp cum]]]]; auto.
    eapply type_tCoFix_inv in tcof as [allow [?  [? [? [[unf tyunf] cum']]]]]; auto.
    (*
    rewrite e in unf. noconf unf.
    eapply typing_spine_strengthen in tsp; eauto.
    eapply typing_spine_weaken_concl in tsp; eauto.
    eapply type_Cumul; [econstructor|..]; eauto.
    eapply type_mkApps. eauto. eauto. admit.*)
    (** Essential here that projection types cannot refer to the coinductive object  
        directly but only through projections, so that SR is preserved.
        Will need to add an invariant to the projections typing. *)
    rewrite allow in heq_allow_cofix. discriminate.

  - (* Proj Constructor reduction *) 
    pose proof (env_prop_typing _ _ validity _ _ _ _ _ typec).
    simpl in typec.
    pose proof typec as typec'.
    eapply inversion_mkApps in typec as [A [U [tyc [tyargs tycum]]]]; auto.
    eapply (inversion_Construct Σ wf) in tyc as [mdecl' [idecl' [cdecl' [wfl [declc [Hu tyc]]]]]].
    pose proof typec' as typec''.
    unshelve eapply Construct_Ind_ind_eq in typec'; eauto.
    unfold on_declared_constructor in typec'.
    destruct declc as [decli declc].
    unfold on_declared_inductive in typec'.
    destruct declared_constructor_inv as [cs [Hnth onc]].
    simpl in typec'.
    pose proof isdecl as isdecl'.
    destruct isdecl' as [decli' [H0 Hi]].
    destruct (declared_inductive_inj decli' decli) as []; subst mdecl' idecl'.
    simpl in decli'.
    set (pdecl' := conj decli isdecl.p2 : declared_projection Σ.1 mdecl idecl (i, pars, narg) pdecl).
    epose proof (declared_projection_type_and_eq wf pdecl').
    simpl in X2.
    pose proof (subslet_projs Σ Γ u1 _ _ _ args0 _ decli) as projsubsl.
    destruct declared_inductive_inv. simpl in *.
    forward onProjections. clear pdecl'.
    eapply nth_error_Some_length in H0. simpl in H0.
    intros Hp. apply (f_equal (@length _)) in Hp. rewrite  Hp /=   in H0. lia.
    simpl in H0.
    simpl in *.
    destruct typec' as [[[[_ equ] cu] eqargs] [cparsubst [cargsubst [iparsubst [iidxsubst ci]]]]].
    destruct ci as ((([cparsubst0 iparsubst0] & idxsubst0) & subsidx) & [s [typectx [Hpars Hargs]]]).
    destruct ind_cshapes as [|? []]; try contradiction.
    destruct X2 as [projty projeq].
    destruct k; simpl in *; try discriminate. noconf Hnth.
    2:{ rewrite nth_error_nil in Hnth. discriminate. }
    specialize (projsubsl onProjections).
    destruct onProjections.
    pose proof (on_declared_minductive wf isdecl.p1.p1) as onmind.
    eapply nth_error_alli in on_projs; eauto.
    eapply typing_spine_strengthen in tyargs; eauto.
    eapply typing_spine_weaken_concl in tyargs; eauto.
    rewrite -(firstn_skipn (ind_npars mdecl) args0) in tyargs, e |- *.
    subst pars.
    assert(#|firstn (ind_npars mdecl) args0| = ind_npars mdecl).
    rewrite firstn_length_le. lia. lia.
    rewrite nth_error_app_ge in e. lia.
    rewrite H in e. replace (ind_npars mdecl + narg - ind_npars mdecl) with narg in e by lia.
    epose proof (declared_constructor_valid_ty _ _ _ _ _ 0 cdecl' _ wf wfΓ) as Hty.
    forward Hty by (split; eauto).
    forward Hty. eapply Hu.
    unfold type_of_constructor in tyargs, Hty.
    rewrite [cdecl'.1.2]onc.(cstr_eq) in tyargs, Hty.
    rewrite !subst_instance_constr_it_mkProd_or_LetIn !subst_it_mkProd_or_LetIn in tyargs, Hty.
    eapply typing_spine_inv in tyargs as [arg_sub [[spargs iswat] sp]]; eauto.
    3:{ right; simpl; auto. }
    2:{ rewrite !context_assumptions_fold.
        rewrite subst_instance_context_assumptions. rewrite H.
        apply onNpars in onmind. lia. }
    clear Hty.
    rewrite subst_it_mkProd_or_LetIn in sp, iswat.
    rewrite !subst_instance_constr_mkApps !subst_mkApps in sp, iswat.
    eapply typing_spine_nth_error in sp; eauto.
    clear iswat.
    2:{ rewrite !context_assumptions_fold. rewrite subst_instance_context_assumptions.
        clear iswat sp. eapply nth_error_Some_length in H0. lia. }
    destruct sp as [decl [Hnth Hu0]].
    simpl in on_projs. red in on_projs.
    eapply type_Cumul; eauto.
    * rewrite firstn_skipn.
      eapply (isType_subst_instance_decl Σ _ _ _ _ u wf isdecl.p1.p1) in projty; eauto.
      right. destruct projty as [s' Hs].
      exists s'. red in Hs.
      rewrite /= /map_decl /= in Hs.
      eapply (weaken_ctx Γ) in Hs; auto.
      rewrite (subst_app_simpl [_]).
      eapply (substitution0 _ _ _ _ _ _ (tSort s')). auto.
      simpl.
      eapply (substitution _ Γ (subst_instance_context u (smash_context [] (ind_params mdecl)))
        _ [vass _ _] _ (tSort s')); eauto.
      rewrite firstn_all2 in iparsubst0. lia.
      eapply spine_subst_smash in iparsubst0; auto.
      rewrite subst_instance_context_smash.
      eapply iparsubst0. simpl.
      rewrite subst_instance_constr_mkApps subst_mkApps /=.
      rewrite subst_instance_instance_id subst_instance_to_extended_list.
      rewrite firstn_all2 in iparsubst0. lia.
      eapply spine_subst_smash in iparsubst0; auto.
      rewrite subst_instance_context_smash /=.
      rewrite /to_extended_list (spine_subst_subst_to_extended_list_k iparsubst0).
      assumption.
    * eapply conv_cumul.
      rewrite !context_assumptions_fold subst_instance_context_assumptions in Hnth.
      rewrite firstn_skipn.
      rewrite smash_context_app smash_context_acc in on_projs.
      rewrite nth_error_app_lt in on_projs.
      { autorewrite with len. simpl. 
        eapply nth_error_Some_length in Hnth. autorewrite with len in Hnth.
        rewrite !context_assumptions_fold in Hnth.
        now rewrite subst_instance_context_assumptions in Hnth. }
      rewrite nth_error_subst_context in on_projs.
      epose proof (nth_error_lift_context_eq _ (smash_context [] (ind_params mdecl))).
      autorewrite with len in H1. simpl in H1.
      erewrite -> H1 in on_projs. clear H1.
      rewrite (smash_context_subst []) in Hnth.
      rewrite (smash_context_subst []) in Hnth.
      rewrite -(subst_instance_context_smash u1 _ []) in Hnth.
      rewrite !nth_error_subst_context in Hnth.
      rewrite nth_error_map in Hnth.
      destruct projeq as [decl' [[[Hdecl wfdecl] Hty1] Hty2]].
      rewrite Hdecl in on_projs, Hnth.
      simpl in on_projs, Hnth.
      destruct on_projs as [declna decltyeq].
      noconf Hnth. simpl in *.
      autorewrite with len in Hu0, decltyeq |- *.
      simpl in Hu0, decltyeq |- *.
      move: Hu0 decltyeq.
      assert (narg < context_assumptions (cshape_args cs)).
      eapply nth_error_Some_length in H0. lia.
      replace (context_assumptions (cshape_args cs) -
        S (context_assumptions (cshape_args cs) - S narg))
        with narg by lia.
      move=> Hu0 decltyeq.
      rewrite -Hty1. clear decltyeq.
      rewrite Hty2.
      unfold projection_type'.
      set (indsubst1 := inds _ _ _).
      set (indsubst := inds _ _ _).
      set (projsubst := projs _ _ _).
      rewrite - !subst_subst_instance_constr.
      rewrite -lift_subst_instance_constr.
      rewrite - !subst_subst_instance_constr.
      epose proof (commut_lift_subst_rec _ _ 1 narg narg).
      rewrite Nat.add_1_r in H2. rewrite <- H2 => //. clear H2.
      rewrite (subst_app_decomp [_]).
      autorewrite with len. rewrite heq_length.
      simpl. rewrite lift_mkApps. simpl.
      rewrite (distr_subst [_]). simpl.
      autorewrite with len. rewrite {2}/projsubst projs_length.
      rewrite simpl_subst_k // subst_instance_constr_projs.
      epose proof (subst_app_simpl (List.rev (firstn narg (skipn (ind_npars mdecl) args0))) _ 0).
      autorewrite with len in H2.  simpl in H2.
      assert(#|firstn narg (skipn (ind_npars mdecl) args0)| = narg).
      { rewrite firstn_length_le. rewrite skipn_length. lia. lia. lia. }
      rewrite H3 in H2. rewrite <- H2. clear H2.
      rewrite subst_app_decomp.
      epose proof (subst_app_simpl 
      (map
      (subst0
         [mkApps (tConstruct i 0 u1) (map (lift0 (ind_npars mdecl)) args0)])
      (projs i (ind_npars mdecl) narg))).
      autorewrite with len in H2.
      rewrite -H2. clear H2.
      rewrite subst_app_decomp.
      autorewrite with len.
      rewrite (distr_subst (List.rev args)).
      autorewrite with len.
      assert (map (subst0 (List.rev args))
      (map (subst_instance_constr u) (extended_subst (ind_params mdecl) 0))  = 
        iparsubst) as ->. 
      { rewrite firstn_all2 in iparsubst0. lia.
        rewrite extended_subst_subst_instance_constr.
        pose proof (inst_ctx_subst iparsubst0).
        eapply context_subst_extended_subst in X2.
        rewrite X2. eapply map_ext.
        intros. now rewrite subst_inst Upn_0. }
      eapply (subst_conv _ _ _ []).
      { auto. }
      { eapply spargs. } 
      { eapply iparsubst0. }
      { eapply spine_subst_conv. auto. 
        eapply spargs. eapply iparsubst0.
        rewrite closed_ctx_subst.
        eapply closed_wf_local; eauto.
        eapply on_minductive_wf_params; eauto. eapply decli.
        eapply context_relation_subst_instance; eauto.
        eapply on_minductive_wf_params; eauto. eapply decli.
        eapply Hpars. }
      { simpl.
        eapply weaken_wf_local; auto.
        rewrite closed_ctx_subst.
        eapply closed_wf_local; eauto.
        eapply on_minductive_wf_params; eauto. eapply decli.
        eapply on_minductive_wf_params; eauto. eapply decli. }
      simpl.
      rewrite distr_subst. autorewrite with len.
      simpl.
      do 2 rewrite map_map_compose.
      pose proof (subslet_length spargs).
      set (real_args0 := skipn (ind_npars mdecl) args0) in *.
      eapply firstn_length_le_inv in H3.
      assert (narg = #|real_args0| - (#|real_args0| - narg)) by lia.
      assert ((map
        (fun x : term =>
        subst (List.rev args) #|ind_params mdecl|
          (lift0 #|ind_params mdecl|
              (subst0
                [mkApps (tConstruct i 0 u1)
                    (map (lift0 (ind_npars mdecl)) args0)] x)))
        (projs i (ind_npars mdecl) narg))  = 
        (map
        (fun x : term =>
          (subst0
              [mkApps (tConstruct i 0 u1) (map (lift0 #|ind_params mdecl|) args0)] x))
            (projs i (ind_npars mdecl) narg))) as ->.
      { clear -eqargs heq_length.
        induction narg. simpl. reflexivity.
        simpl. f_equal. 2:auto.
        f_equal. rewrite !lift0_id.
        rewrite lift_mkApps subst_mkApps /=. f_equal.
        rewrite [map (lift0 _) _]map_map_compose.
        rewrite map_lift_lift. rewrite Nat.add_comm.
        rewrite map_map_compose.
        rewrite map_subst_lift_ext //.
        now autorewrite with len. }
      assert(wfctx : wf_local Σ
      (Γ ,,,
       subst_context (inds (inductive_mind i) u1 (ind_bodies mdecl)) 0
         (subst_instance_context u1 (PCUICEnvironment.ind_params mdecl)) ,,,
       lift_context
         #|subst_context (inds (inductive_mind i) u1 (ind_bodies mdecl)) 0
             (subst_instance_context u1 (PCUICEnvironment.ind_params mdecl))| 0
         (skipn (#|real_args0| - narg)
            (smash_context []
               (subst_context cparsubst 0
                  (subst_context (inds (inductive_mind i) u1 (ind_bodies mdecl))
                     #|ind_params mdecl|
                     (subst_instance_context u1 (cshape_args cs)))))))).
      { autorewrite with len.
        simpl. 
        fold indsubst1 in |- *.
        epose proof (weakening_wf_local Σ Γ _ (subst_context indsubst1 0 (subst_instance_context u1 (ind_params mdecl)))).
        autorewrite with len in X2.
        eapply X2; clear X2; auto.
        2:eapply spine_codom_wf; eauto.
        eapply All_local_env_app_inv. split; auto.
        eapply All_local_env_skipn.
        eapply wf_local_rel_smash_context; auto.
        eapply spine_codom_wf; eauto. }
      eapply (untyped_subst_conv (Γ ,,, _) _ _ []); auto.
      + move idxsubst0 at bottom.
        rewrite H2.
        eapply subslet_untyped_subslet.
        eapply subslet_lift; auto. apply wf. auto. eapply (spine_codom_wf _ _ _ _ _ spargs).
        eapply spine_subst_smash in idxsubst0.
        2:auto.
        eapply inst_subslet in idxsubst0.
        rewrite {1}H4. rewrite -skipn_rev.
        eapply subslet_skipn in idxsubst0. eapply idxsubst0.
      + eapply (untyped_subslet_skipn _ _ _ (#|real_args0| - narg)) in projsubsl.
        eapply untyped_subslet_eq_subst.
        eapply projsubsl.
        rewrite -map_skipn skipn_projs.
        rewrite /real_args0 skipn_length. lia.
        f_equal. f_equal. lia.
      + rewrite /real_args0.
        rewrite H2; autorewrite with len.
        rewrite H4 -skipn_projs map_skipn -skipn_rev map_skipn.
        eapply All2_skipn.
        rewrite /real_args0.
        rewrite skipn_length. lia.

        rewrite subst_projs_inst.
        change (tConstruct i 0 u1) with (lift0 #|ind_params mdecl| (tConstruct i 0 u1)).
        rewrite -lift_mkApps projs_inst_lift. eapply All2_map.
        eapply (All2_impl (P:=fun x y => Σ ;;; Γ |- x = y)).
        2:{ intros. epose proof (weakening_conv _ Γ [] (subst_context (inds (inductive_mind i) u1 (ind_bodies mdecl)) 0
            (subst_instance_context u1 (ind_params mdecl)))).
            autorewrite with len in X3. eapply X3. auto. assumption. }
        eapply All2_from_nth_error.
        autorewrite with len. rewrite skipn_length //; lia.
        move=> n x1 x2. autorewrite with len. rewrite skipn_length //; try lia.
        move=> Hn Hx1. rewrite nth_error_projs_inst //.
        move=> [=] h. subst x2. rewrite eqargs minus_plus.
        eapply conv_sym. eapply red_conv.
        eapply red1_red, red_proj.
        rewrite -{}Hx1.
        rewrite (nth_error_rev (List.rev _)). autorewrite with len.
        rewrite skipn_length //; lia.
        rewrite List.rev_involutive nth_error_skipn.
        autorewrite with len. f_equal.
        f_equal. rewrite skipn_length //; lia. 
      + simpl; auto.
      + assert (closedn (narg + #|ind_bodies mdecl| + #|ind_params mdecl|) (decl_type decl')).
        { clear projsubsl.
          eapply closed_wf_local in wfdecl.
          rewrite closedn_ctx_app in wfdecl.
          move/andP: wfdecl => [_ wfdecl].
          autorewrite with len in wfdecl. rewrite arities_context_length in wfdecl.
          simpl in wfdecl.
          eapply closedn_ctx_decl in wfdecl; eauto.
          autorewrite with len in wfdecl.
          simpl in wfdecl.
          move/andP: wfdecl => [_ clty].
          eapply closed_upwards. eauto.
          lia. auto. }
      rewrite (subst_closedn (List.rev args)).
      eapply (closedn_subst _ 0).
      epose proof (PCUICSigmaCalculus.declared_inductive_closed_inds _ _ _ _ _ wf decli).
      rewrite closed_map_subst_instance. eapply H6.
      rewrite /indsubst; autorewrite with len.
      rewrite inds_length. rewrite closedn_subst_instance_constr.
      eapply closed_upwards; eauto; lia.
      autorewrite with len.
      pose proof(context_subst_length _ _ _ cparsubst0).
      autorewrite with len in H6. rewrite {2}H6.
      autorewrite with len in wfctx. move: wfctx.
      rewrite {2}H6.
      rewrite - !subst_app_context.
      rewrite !(smash_context_subst []).
      rewrite skipn_subst_context.
      rewrite subst_context_decompo.
      rewrite lift_context_subst_context.
      set(argctx := lift_context _ _ _) in *. move=> wfargctx.
      simpl.
      epose proof (untyped_subst_conv Γ _ _ (subst_instance_context u1 (ind_params mdecl) ,,, argctx) _ _ _ _); auto.
      rewrite subst_context_app in X2. autorewrite with len in X2.
      assert (#|argctx| = narg).
      rewrite /argctx; autorewrite with len.
      rewrite List.skipn_length. autorewrite with len. simpl.
      rewrite /real_args0 List.skipn_length eqargs. lia.
      rewrite H7 in X2.
      rewrite !app_context_assoc in X2.
      change (map (subst_instance_constr u)) with (subst_instance (A:=list term) u).
      rewrite /indsubst. 
      rewrite instantiate_inds; auto. eapply decli.
      eapply X2; clear X2; auto.
      ** eapply subslet_untyped_subslet.
        eapply PCUICArities.weaken_subslet; eauto.
        eapply subslet_inds; eauto.
      ** eapply subslet_untyped_subslet.
        eapply PCUICArities.weaken_subslet; eauto.
        eapply subslet_inds; eauto.
      ** eapply conv_inds => //.
      ** fold indsubst1 in |- *.
        eapply (wf_local_instantiate _ _ _ _ _ wf decli'.p1) in wfdecl.
        2:eapply Hu.
        eapply (weaken_wf_local Γ) in wfdecl; eauto.
        rewrite !subst_instance_context_app !app_context_assoc in wfdecl.
        apply All_local_env_app in wfdecl as [wfarpars wfsmash].
        epose proof (weakening_wf_local Σ (Γ ,,, subst_instance_context u1 (arities_context (ind_bodies mdecl))) _ 
          (subst_instance_context u1 (ind_params mdecl))).
        autorewrite with len in X2.
        rewrite /argctx. eapply X2; clear X2. all:auto.
        eapply substitution_wf_local; eauto.
        eapply spine_subst_weakening in cparsubst0; eauto.
        2:{ eapply All_local_env_app in wfarpars as [wfars _]. eapply wfars. }
        autorewrite with len in cparsubst0.
        rewrite inds_length. rewrite arities_context_length in cparsubst0. apply cparsubst0.
        rewrite closed_ctx_lift. eapply closed_wf_local. eauto.
        eapply on_minductive_wf_params; eauto. eapply decli. auto.
        eapply All_local_env_app_inv. split; auto.
        eapply All_local_env_skipn.
        now rewrite -(subst_instance_context_smash _ _ []).
      ** constructor.
        apply eq_term_upto_univ_subst_instance_constr; try typeclasses eauto.
        apply equ.

  - (* Proj congruence: discriminee reduction *) 
    eapply type_Cumul; [econstructor|..]; eauto.
    eapply validity; eauto.
    instantiate (1:= tProj p c).
    econstructor; eauto.
    eapply conv_cumul.
    rewrite (subst_app_simpl [c']) (subst_app_simpl [c]).
    eapply (untyped_subst_conv Γ [vass nAnon (mkApps (tInd p.1.1 u) args)] 
      [vass nAnon (mkApps (tInd p.1.1 u) args)] []); auto.
    repeat constructor. repeat constructor. constructor.
    now apply conv_sym, red_conv, red1_red. constructor.
    simpl. constructor. auto.
    eapply validity in typec; auto.
    destruct typec; auto.
    destruct i as [ctx [s [dA _]]].
    rewrite destArity_tInd in dA. discriminate.

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
      reflexivity. apply IHo. rewrite !fix_context_length in fixl |- *; simpl in *. lia. }
    assert(All (fun d => isType Σ Γ (dtype d)) mfix).
    { apply (All_impl X0).
      now intros x [s' [Hs' _]]; exists s'. }
    assert(All (fun d => isType Σ Γ (dtype d)) mfix1).
    { apply (OnOne2_All_All o X0).
      * intros x [s [Hs IH]].
        now exists s.
      * intros x y [red eq] [s [Hs IH]].
        now exists s; apply IH. }
    assert (wf_local Σ (Γ ,,, fix_context mfix1)).
    { apply All_mfix_wf; auto. }
    destruct (OnOne2_nth_error _ _ _ decl _ o heq_nth_error) as [decl' [eqnth disj]].
    eapply type_Cumul.
    econstructor; eauto.
    * eapply (fix_guard_red1 _ _ _ _ 0); eauto.
      constructor; eauto.
    * eapply (OnOne2_All_mix_left X0) in o.
      apply (OnOne2_All_All o X1).
      + intros x [[Hb Hlam] IH].
        split; auto.
        eapply context_conversion'; eauto.
        now rewrite -fixl.
      + move=> [na ty b rarg] [na' ty' b' rarg'] /= [[red eq] [s [Hs IH]]] [[Hb Hlam] IH'].
        noconf eq. split; auto.
        eapply context_conversion'; eauto.
        rewrite -fixl.
        eapply type_Cumul. eapply Hb.
        right. exists s. specialize (IH _ red).
        eapply (weakening _ _ _ _ (tSort _)); auto.
        apply All_mfix_wf; auto. 
        apply (weakening_cumul _ _ []); auto.
        now apply red_cumul, red1_red.

    * eapply All_nth_error in X2; eauto.
    * apply conv_cumul, conv_sym, red_conv. destruct disj as [<-|red].
      constructor. apply red1_red. apply red.

  - (* Fix congruence in body *)
    assert(fixl :#|fix_context mfix| = #|fix_context mfix1|) by now (rewrite !fix_context_length; apply (OnOne2_length o)).
    assert(convctx : fix_context mfix = fix_context mfix1).
    { clear -wf o.
      change fix_context with (fix_context_gen 0).
      generalize 0. induction o.
      destruct p as [_ eq]. noconf eq. simpl in H; noconf H.
      simpl. intros. now rewrite H H0.
      simpl. intros n; f_equal. apply IHo. }
    assert(All (fun d => isType Σ Γ (dtype d)) mfix).
    { apply (All_impl X0).
      now intros x [s' [Hs' _]]; exists s'. }
    assert(All (fun d => isType Σ Γ (dtype d)) mfix1).
    { apply (OnOne2_All_All o X0).
      * intros x [s [Hs IH]].
        now exists s.
      * intros x y [red eq] [s [Hs IH]].
        noconf eq. simpl in H0; noconf H0. rewrite -H1.
        now exists s; apply Hs. }
    assert (wf_local Σ (Γ ,,, fix_context mfix1)).
    { apply All_mfix_wf; auto. }
    destruct (OnOne2_nth_error _ _ _ decl _ o heq_nth_error) as [decl' [eqnth disj]].
    eapply type_Cumul.
    econstructor; eauto.
    * eapply (fix_guard_red1 _ _ _ _ 0); eauto.
      apply fix_red_body; eauto.
    * eapply (OnOne2_All_mix_left X0) in o.
       apply (OnOne2_All_All o X1).
      + intros x [[Hb Hlam] IH].
        split; auto.
        eapply context_conversion'; eauto.
        now rewrite -fixl.
        rewrite convctx. apply conv_ctx_refl.
      + move=> [na ty b rarg] [na' ty' b' rarg'] /= [[red eq] [s [Hs IH]]] [[Hb Hlam] IH'].
        noconf eq.
        rewrite -convctx. split; auto.
        now eapply isLambda_red1.
    * eapply All_nth_error in X2; eauto.
    * apply conv_cumul, conv_sym, red_conv. destruct disj as [<-|[_ eq]].
      constructor. noconf eq. simpl in H0; noconf H0. rewrite H1; constructor.

  - (* CoFix congruence type *)
    assert(fixl :#|fix_context mfix| = #|fix_context mfix1|) by now (rewrite !fix_context_length; apply (OnOne2_length o)).
    assert(convctx : conv_context Σ (Γ ,,, fix_context mfix) (Γ ,,, fix_context mfix1)).
    { clear -wf X o fixl.
      eapply context_relation_app_inv => //.
      apply conv_ctx_refl. clear X.
      apply conv_decls_fix_context => //.
      induction o; constructor.
      destruct p. now apply red_conv, red1_red.
      apply All2_refl. reflexivity.
      reflexivity. apply IHo. rewrite !fix_context_length /= in fixl |- *; lia. }
    assert(All (fun d => isType Σ Γ (dtype d)) mfix).
    { apply (All_impl X0).
      now intros x [s' [Hs' _]]; exists s'. }
    assert(All (fun d => isType Σ Γ (dtype d)) mfix1).
    { apply (OnOne2_All_All o X0).
      * intros x [s [Hs IH]].
        now exists s.
      * intros x y [red eq] [s [Hs IH]].
        now exists s; apply IH. }
    assert (wf_local Σ (Γ ,,, fix_context mfix1)).
    { apply All_mfix_wf; auto. }
    destruct (OnOne2_nth_error _ _ _ decl _ o heq_nth_error) as [decl' [eqnth disj]].
    eapply type_Cumul.
    econstructor; eauto.
    * eapply (OnOne2_All_mix_left X0) in o.
      apply (OnOne2_All_All o X1).
      + intros x [Hb IH].
        eapply context_conversion'; eauto.
        now rewrite -fixl.
      + move=> [na ty b rarg] [na' ty' b' rarg'] /= [[red eq] [s [Hs IH]]] [Hb IH'].
        noconf eq. 
        eapply context_conversion'; eauto.
        rewrite -fixl.
        eapply type_Cumul. eapply Hb.
        right. exists s. specialize (IH _ red).
        eapply (weakening _ _ _ _ (tSort _)); auto.
        apply All_mfix_wf; auto. 
        apply (weakening_cumul _ _ []); auto.
        now apply red_cumul, red1_red.
    * eapply All_nth_error in X2; eauto.
    * apply conv_cumul, conv_sym, red_conv. destruct disj as [<-|red].
      constructor. apply red1_red. apply red.


  - (* CoFix congruence in body *)
    assert(fixl :#|fix_context mfix| = #|fix_context mfix1|) by now (rewrite !fix_context_length; apply (OnOne2_length o)).
    assert(convctx : fix_context mfix = fix_context mfix1).
    { clear -wf o.
      change fix_context with (fix_context_gen 0).
      generalize 0. induction o.
      destruct p as [_ eq]. noconf eq. simpl in H; noconf H.
      simpl. intros. now rewrite H H0.
      simpl. intros n; f_equal. apply IHo. }
    assert(All (fun d => isType Σ Γ (dtype d)) mfix).
    { apply (All_impl X0).
      now intros x [s' [Hs' _]]; exists s'. }
    assert(All (fun d => isType Σ Γ (dtype d)) mfix1).
    { apply (OnOne2_All_All o X0).
      * intros x [s [Hs IH]].
        now exists s.
      * intros x y [red eq] [s [Hs IH]].
        noconf eq. simpl in H; noconf H. rewrite -H1.
        now exists s; apply Hs. }
    assert (wf_local Σ (Γ ,,, fix_context mfix1)).
    { apply All_mfix_wf; auto. }
    destruct (OnOne2_nth_error _ _ _ decl _ o heq_nth_error) as [decl' [eqnth disj]].
    eapply type_Cumul.
    econstructor; eauto.
    * eapply (OnOne2_All_mix_left X0) in o.
      apply (OnOne2_All_All o X1).
      + intros x [Hb IH].
        now rewrite -convctx.
      + move=> [na ty b rarg] [na' ty' b' rarg'] /= [[red eq] [s [Hs IH]]] [Hb IH'].
        noconf eq.
        now rewrite -convctx. 
    * eapply All_nth_error in X2; eauto.
    * apply conv_cumul, conv_sym, red_conv. destruct disj as [<-|[_ eq]].
      constructor. noconf eq. simpl in H; noconf H. rewrite H1; constructor.
 
  - (* Conversion *)
    specialize (forall_u _ Hu).
    eapply type_Cumul; eauto.
    destruct X2 as [[wf' _]|[s Hs]].
    now left.
    now right.
Qed.

Print Assumptions sr_red1.

Definition sr_stmt {cf:checker_flags} (Σ : global_env_ext) Γ t T :=
  forall u, red Σ Γ t u -> Σ ;;; Γ |- u : T.

Theorem subject_reduction {cf:checker_flags} : 
  forall (Σ : global_env_ext) Γ t u T, wf Σ -> Σ ;;; Γ |- t : T -> red Σ Γ t u -> Σ ;;; Γ |- u : T.
Proof.
  intros * wfΣ Hty Hred.
  induction Hred. auto.
  eapply sr_red1 in IHHred; eauto with wf. todo "allow_cofix"%string.
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

  Lemma subject_reduction_ctx Σ Γ Γ' t T :
    wf Σ.1 ->
    red1_ctx Σ.1 Γ Γ' ->
    Σ ;;; Γ |- t : T -> Σ ;;; Γ' |- t : T.
  Proof.
    assert(OnOne2_local_env
      (on_one_decl
         (fun (Δ : PCUICAst.context) (t t' : term) => red1 Σ.1 Δ t t')) Γ Γ' ->
         conv_context Σ Γ Γ').
    { clear. induction 1.
      - red in p. constructor; auto.
        apply conv_ctx_refl. constructor. now apply red_conv, red1_red.
      - destruct p. constructor.
        apply conv_ctx_refl. destruct p as [red ->].
        constructor; auto; now apply red_conv, red1_red.
        constructor.
        apply conv_ctx_refl. destruct p as [red ->].
        constructor; auto; now apply red_conv, red1_red.
      - destruct d as [na [b|] ?]; constructor; auto; constructor; auto. }
    intros wfΣ r H.
    specialize (X r).
    assert(wf_local Σ Γ').
    apply typing_wf_local in H.
    induction H in Γ', r, X |-  *; depelim r; simpl in H; noconf H.
    - constructor; auto. red in o.
      destruct t2 as [s Hs]. exists s.
      eapply subject_reduction1 in Hs; eauto.
    - depelim X; simpl in H; noconf H; simpl in H0; noconf H0.
      constructor; auto. 
      destruct t1 as [s Hs]. exists s.
      eapply context_conversion; eauto.
    - depelim X; simpl in H; noconf H; simpl in H0; noconf H0.
      red in o. destruct t2 as [s Hs].
      simpl in t3.
      destruct o as [[r ->]|[r <-]].

      constructor; auto. exists s; auto.
      eapply subject_reduction1; eauto.
      constructor; auto. exists s; eapply subject_reduction1; eauto.
      eapply type_Cumul; eauto. right. exists s.
      eapply subject_reduction1; eauto.
      now apply red_cumul, red1_red.
    - depelim X; simpl in H; noconf H; simpl in H0; noconf H0.
      destruct t2 as [s Hs].
      simpl in t3.

      constructor; auto. exists s; auto.
      eapply context_conversion; eauto.
      red; eapply context_conversion; eauto.

    - eapply context_conversion; eauto.
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
      all: eapply substitution; tea.
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
      all: eapply substitution; tea.
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
    : wf Σ.1 ->  Σ ;;; Γ |- t : A -> red (fst Σ) Γ A B -> Σ ;;; Γ |- t : B.
  Proof.
    intros HΣ' Ht Hr.
    econstructor. eassumption.
    2: now eapply cumul_red_l'.
    destruct (validity_term HΣ' Ht).
    - left. eapply isWfArity_red; try eassumption.
    - destruct i as [s HA]. right.
      exists s. eapply subject_reduction; eassumption.
  Defined.

End SRContext.
