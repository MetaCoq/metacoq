(* Distributed under the terms of the MIT license.   *)
Set Warnings "-notation-overridden".

Require Import Equations.Prop.DepElim.
From Coq Require Import Bool String List Lia Arith.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICWeakeningEnv PCUICWeakening
     PCUICSubstitution PCUICClosed PCUICCumulativity PCUICGeneration PCUICReduction
     PCUICEquality PCUICConfluence PCUICParallelReductionConfluence
     PCUICContextConversion PCUICUnivSubstitution
     PCUICConversion PCUICInversion PCUICContexts PCUICArities
     PCUICParallelReduction PCUICCtxShape PCUICSpine PCUICInductives PCUICValidity.
     
Close Scope string_scope.

Require Import ssreflect. 

Set Asymmetric Patterns.
Set SimplIsCbn.

From Equations Require Import Equations.

Ltac pcuic := intuition eauto 5 with pcuic ||
  (try solve [repeat red; cbn in *; intuition auto; eauto 5 with pcuic || (try lia || congruence)]).

(** Inversion principles on inductive/coinductives types following from validity. *)

Lemma isWAT_it_mkProd_or_LetIn_mkApps_Ind_isType {cf:checker_flags} {Σ Γ ind u args} Δ :
  wf Σ.1 ->
  isWfArity_or_Type Σ Γ (it_mkProd_or_LetIn Δ (mkApps (tInd ind u) args)) ->
  isType Σ Γ (it_mkProd_or_LetIn Δ (mkApps (tInd ind u) args)).
Proof.
  intros wfΣ.
  intros [[ctx [s eq]]|H]; auto.
  rewrite destArity_it_mkProd_or_LetIn in eq.
  destruct eq as [da _].
  apply destArity_app_Some in da as [ctx' [da _]].
  rewrite destArity_tInd in da. discriminate.
Qed.

Lemma isWAT_mkApps_Ind_isType {cf:checker_flags} Σ Γ ind u args :
  wf Σ.1 ->
  isWfArity_or_Type Σ Γ (mkApps (tInd ind u) args) ->
  isType Σ Γ (mkApps (tInd ind u) args).
Proof.
  intros wfΣ H.
  now apply (isWAT_it_mkProd_or_LetIn_mkApps_Ind_isType [] wfΣ).
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
  unfold type_of_constructor in X |- *.
  destruct (on_declared_constructor _ declc); eauto.
  destruct s as [cshape [Hsorc Hc]].
  destruct Hc as [_ chead cstr_eq [cs Hcs] _ _].
  destruct cshape. rewrite /cdecl_type in cstr_eq.
  rewrite cstr_eq in X |- *. clear -wfΣ declc X.
  move: X. simpl.
  rewrite /subst1 !subst_instance_constr_it_mkProd_or_LetIn !subst_it_mkProd_or_LetIn.
  rewrite !subst_instance_constr_mkApps !subst_mkApps.
  rewrite !subst_instance_context_length Nat.add_0_r.
  rewrite subst_inds_concl_head.
  + simpl. destruct declc as [[onm oni] ?].
    now eapply nth_error_Some_length in oni.
  + rewrite -it_mkProd_or_LetIn_app. apply isWAT_it_mkProd_or_LetIn_mkApps_Ind_isType. auto.
Qed.

Lemma declared_inductive_valid_type {cf:checker_flags} Σ Γ mdecl idecl i u :
  wf Σ.1 ->
  wf_local Σ Γ ->
  declared_inductive Σ.1 mdecl i idecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  isType Σ Γ (subst_instance_constr u (ind_type idecl)).
Proof.
  move=> wfΣ wfΓ declc Hu.
  pose declc as declc'.
  apply on_declared_inductive in declc' as [onmind onind]; auto.
  apply onArity in onind.
  destruct onind as [s Hs].
  epose proof (PCUICUnivSubstitution.typing_subst_instance_decl Σ) as s'.
  destruct declc.
  specialize (s' [] _ _ _ _ u wfΣ H Hs Hu).
  simpl in s'. eexists; eauto.
  eapply (PCUICWeakening.weaken_ctx (Γ:=[]) Γ); eauto.
Qed.

Lemma type_tFix_inv {cf:checker_flags} (Σ : global_env_ext) Γ mfix idx T : wf Σ ->
  Σ ;;; Γ |- tFix mfix idx : T ->
  { T' & { rarg & {f & (unfold_fix mfix idx = Some (rarg, f))  *
    wf_fixpoint Σ.1  mfix
  * (Σ ;;; Γ |- f : T') * (Σ ;;; Γ |- T' <= T) }}}%type.
Proof.
  intros wfΣ H. depind H.
  - unfold unfold_fix. rewrite e.
    specialize (nth_error_all e a0) as [s Hs].
    specialize (nth_error_all e a1) as [Hty Hlam].
    simpl.
    destruct decl as [name ty body rarg]; simpl in *.
    clear e.
    eexists _, _, _. split.
    + split.
      * eauto.
      * eapply (substitution _ _ _ _ [] _ _ wfΣ); simpl; eauto with wf.
        rename i into hguard. clear -i0 a a0 a1 hguard.
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

Lemma subslet_cofix {cf:checker_flags} (Σ : global_env_ext) Γ mfix :
  wf_local Σ Γ ->
  cofix_guard mfix ->
  All (fun d : def term => ∑ s : Universe.t, Σ;;; Γ |- dtype d : tSort s) mfix ->
  All
  (fun d : def term =>
   Σ;;; Γ ,,, fix_context mfix |- dbody d
   : lift0 #|fix_context mfix| (dtype d)) mfix ->
  wf_cofixpoint Σ.1 mfix -> subslet Σ Γ (cofix_subst mfix) (fix_context mfix).
Proof.
  intros wfΓ hguard types bodies wfcofix.
  pose proof bodies as X1. apply All_rev in X1.
  unfold cofix_subst, fix_context. simpl.
  revert X1. rewrite <- (@List.rev_length _ mfix).
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
Qed.

Lemma type_tCoFix_inv {cf:checker_flags} (Σ : global_env_ext) Γ mfix idx T : wf Σ ->
  Σ ;;; Γ |- tCoFix mfix idx : T ->
  ∑ d, (nth_error mfix idx = Some d) *
    wf_cofixpoint Σ.1 mfix *
    (Σ ;;; Γ |- subst0 (cofix_subst mfix) (dbody d) : (dtype d)) *
    (Σ ;;; Γ |- dtype d <= T).
Proof.
  intros wfΣ H. depind H.
  - exists decl. 
    specialize (nth_error_all e a1) as Hty.
    destruct decl as [name ty body rarg]; simpl in *.
    intuition auto.
    * eapply (substitution _ _ _ (cofix_subst mfix) [] _ _ wfΣ) in Hty. simpl; eauto with wf.
      simpl in Hty.
      rewrite subst_context_nil /= in Hty.
      eapply refine_type; eauto.
      rewrite simpl_subst_k //. now autorewrite with len.
      apply subslet_cofix; auto. 
    * reflexivity.
  - destruct (IHtyping wfΣ) as [d [[[Hnth wfcofix] ?] ?]].
    exists d. intuition auto.
    + eapply cumul_trans; eauto.
    + eapply cumul_trans; eauto.
Qed.

Lemma wf_cofixpoint_all {cf:checker_flags} (Σ : global_env_ext) mfix :
  wf_cofixpoint Σ.1 mfix ->
  ∑ mind, check_recursivity_kind Σ.1 mind CoFinite *
  All (fun d => ∑ ctx i u args, (dtype d) = it_mkProd_or_LetIn ctx (mkApps (tInd {| inductive_mind := mind; inductive_ind := i |} u) args)) mfix.
Proof.
  unfold wf_cofixpoint.
  destruct mfix. discriminate.
  simpl.
  destruct (check_one_cofix d) as [ind|] eqn:hcof.
  intros eqr.
  exists ind.
  destruct (map_option_out (map check_one_cofix mfix)) eqn:eqfixes.
  move/andP: eqr => [eqinds rk].
  split; auto.
  constructor.
  - move: hcof. unfold check_one_cofix.
    destruct d as [dname dbody dtype rarg] => /=.
    destruct (decompose_prod_assum [] dbody) as [ctx concl] eqn:Hdecomp.
    apply decompose_prod_assum_it_mkProd_or_LetIn in Hdecomp.
    destruct (decompose_app concl) eqn:dapp.
    destruct (destInd t) as [[ind' u]|] eqn:dind.
    destruct ind' as [mind ind'].
    move=> [=] Hmind. subst mind.
    exists ctx, ind', u, l0.
    simpl in Hdecomp. rewrite Hdecomp.
    f_equal.
    destruct t; try discriminate.
    simpl in dind. noconf dind.
    apply decompose_app_inv in dapp => //.
    discriminate.
  - clear rk hcof.
    induction mfix in l, eqfixes, eqinds |- *. constructor.
    simpl in *.
    destruct (check_one_cofix a) eqn:hcof; try discriminate.
    destruct (map_option_out (map check_one_cofix mfix)) eqn:hcofs; try discriminate.
    noconf eqfixes.
    specialize (IHmfix _ eq_refl).
    simpl in eqinds.
    move/andP: eqinds => [eqk eql0].
    constructor; auto. clear IHmfix hcofs d.
    destruct a as [dname dbody dtype rarg] => /=.
    unfold check_one_cofix in hcof.
    destruct (decompose_prod_assum [] dbody) as [ctx concl] eqn:Hdecomp.
    apply decompose_prod_assum_it_mkProd_or_LetIn in Hdecomp.
    destruct (decompose_app concl) eqn:dapp.
    destruct (destInd t) as [[ind' u]|] eqn:dind.
    destruct ind' as [mind ind']. noconf hcof.
    exists ctx, ind', u, l.
    simpl in Hdecomp. rewrite Hdecomp.
    f_equal.
    destruct t; try discriminate.
    simpl in dind. noconf dind.
    apply decompose_app_inv in dapp => //.
    rewrite dapp. do 3 f_equal.
    symmetry.
    change (eq_kername ind k) with (PCUICReflect.eqb ind k) in eqk.
    destruct (PCUICReflect.eqb_spec ind k); auto. discriminate.
    discriminate.
  - discriminate.
  - discriminate.
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
  eapply inversion_mkApps in t as [A [ta sp]].
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
  move: sp. 
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

Definition R_ind_universes  {cf:checker_flags} (Σ : global_env_ext) ind i i' :=
  R_global_instance Σ (eq_universe (global_ext_constraints Σ)) (leq_universe (global_ext_constraints Σ)) (inductive_mind ind) i i'.

Lemma mkApps_ind_typing_spine {cf:checker_flags} Σ Γ Γ' ind i
  inst ind' i' args args' : 
  wf Σ.1 ->
  wf_local Σ Γ ->
  isWfArity_or_Type Σ Γ (it_mkProd_or_LetIn Γ' (mkApps (tInd ind i) args)) ->
  typing_spine Σ Γ (it_mkProd_or_LetIn Γ' (mkApps (tInd ind i) args)) inst 
    (mkApps (tInd ind' i') args') ->
  ∑ instsubst, (make_context_subst (List.rev Γ') inst [] = Some instsubst) *
  (#|inst| = context_assumptions Γ' /\ ind = ind' /\ R_ind_universes Σ ind i i') *
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

Lemma wf_cofixpoint_typing_spine {cf:checker_flags} (Σ : global_env_ext) Γ ind u mfix idx d args args' : 
  wf Σ.1 -> wf_local Σ Γ ->
  wf_cofixpoint Σ.1 mfix ->
  nth_error mfix idx = Some d ->
  isWfArity_or_Type Σ Γ (dtype d) ->
  typing_spine Σ Γ (dtype d) args (mkApps (tInd ind u) args') ->
  check_recursivity_kind Σ (inductive_mind ind) CoFinite.
Proof.
  intros wfΣ wfΓ wfcofix Hnth wat sp.
  apply wf_cofixpoint_all in wfcofix.
  destruct wfcofix as [mind [cr allfix]].
  eapply nth_error_all in allfix; eauto.
  simpl in allfix.
  destruct allfix as [ctx [i [u' [args'' eqty]]]].
  rewrite {}eqty in sp wat.
  eapply mkApps_ind_typing_spine in sp; auto.
  destruct sp as [instsub [[[makes [Hargs [Hind Hu]]] subs] subsl]].
  now subst ind.
Qed.

Lemma Construct_Ind_ind_eq {cf:checker_flags} {Σ} (wfΣ : wf Σ.1):
  forall {Γ n i args u i' args' u' mdecl idecl cdecl},
  Σ ;;; Γ |- mkApps (tConstruct i n u) args : mkApps (tInd i' u') args' ->
  forall (Hdecl : declared_constructor Σ.1 mdecl idecl (i, n) cdecl),
  let '(onind, oib, existT cshape (hnth, onc)) := on_declared_constructor wfΣ Hdecl in
  (i = i') * 
  (* Universe instances match *)
  R_ind_universes Σ i u u' *
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
  destruct h as [T [hC hs]].
  apply inversion_Construct in hC
    as [mdecl' [idecl' [cdecl' [hΓ [isdecl [const htc]]]]]]; auto.
  assert (vty:=declared_constructor_valid_ty _ _ _ _ _ _ _ _ wfΣ hΓ isdecl const). 
  eapply typing_spine_strengthen in hs. 3:eapply htc. all:eauto.
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

Lemma Case_Construct_ind_eq {cf:checker_flags} Σ (hΣ : ∥ wf Σ.1 ∥) 
  {Γ ind ind' npar pred i u brs args} :
  (∑ T, Σ ;;; Γ |- tCase (ind, npar) pred (mkApps (tConstruct ind' i u) args) brs : T) ->
  ind = ind'.
Proof.
  destruct hΣ as [wΣ].
  intros [A h].
  apply inversion_Case in h as ih ; auto.
  destruct ih
    as [uni [args' [mdecl [idecl [pty [indctx [pctx [ps [btys [? [? [? [? [ht0 [? ?]]]]]]]]]]]]]]].
    pose proof ht0 as typec.
    eapply inversion_mkApps in typec as [A' [tyc tyargs]]; auto.
    eapply (inversion_Construct Σ wΣ) in tyc as [mdecl' [idecl' [cdecl' [wfl [declc [Hu tyc]]]]]].
    epose proof (PCUICInductiveInversion.Construct_Ind_ind_eq _ ht0 declc); eauto.
    destruct on_declared_constructor as [[onmind oib] [cs [? ?]]].
    simpl in *.
    intuition auto.
Qed.

Lemma Proj_Constuct_ind_eq {cf:checker_flags} Σ (hΣ : ∥ wf Σ.1 ∥) {Γ i i' pars narg c u l} :
  (∑ T, Σ ;;; Γ |- tProj (i, pars, narg) (mkApps (tConstruct i' c u) l) : T) ->
  i = i'.
Proof.
  destruct hΣ as [wΣ].
  intros [T h].
  apply inversion_Proj in h ; auto.
  destruct h as [uni [mdecl [idecl [pdecl [args' [? [hc [? ?]]]]]]]].
  pose proof hc as typec.
  eapply inversion_mkApps in typec as [A' [tyc tyargs]]; auto.
  eapply (inversion_Construct Σ wΣ) in tyc as [mdecl' [idecl' [cdecl' [wfl [declc [Hu tyc]]]]]].
  epose proof (PCUICInductiveInversion.Construct_Ind_ind_eq _ hc declc); eauto.
  destruct on_declared_constructor as [[onmind oib] [cs [? ?]]].
  simpl in *.
  intuition auto.
Qed.

Lemma Proj_Constuct_projargs {cf:checker_flags} Σ (hΣ : ∥ wf Σ.1 ∥) {Γ i pars narg c u l} :
  (∑ T, Σ ;;; Γ |- tProj (i, pars, narg) (mkApps (tConstruct i c u) l) : T) ->
  pars + narg < #|l|.
Proof.
  destruct hΣ as [wΣ].
  intros [T h].
  apply inversion_Proj in h ; auto.
  destruct h as [uni [mdecl [idecl [pdecl [args' [? [hc [? ?]]]]]]]].
  clear c0.
  pose proof hc as typec.
  eapply inversion_mkApps in typec as [A' [tyc tyargs]]; auto.
  eapply (inversion_Construct Σ wΣ) in tyc as [mdecl' [idecl' [cdecl' [wfl [declc [Hu tyc]]]]]].
  pose proof (declared_inductive_inj d.p1 declc.p1) as [? ?]; subst mdecl' idecl'.
  set (declc' :=  
   (conj (let (x, _) := d in x) declc.p2) : declared_constructor Σ.1  mdecl idecl (i, c) cdecl').
  epose proof (PCUICInductiveInversion.Construct_Ind_ind_eq _ hc declc'); eauto.
  simpl in X.
  destruct (on_declared_projection wΣ d).
  set (oib := declared_inductive_inv _ _ _ _) in *.
  simpl in *. 
  set (foo := (All2_nth_error_Some _ _ _ _)) in X.
  clearbody foo.
  destruct (ind_cshapes oib) as [|? []] eqn:Heq; try contradiction.
  destruct foo as [t' [ntht' onc]].
  destruct c; simpl in ntht'; try discriminate.
  noconf ntht'.
  2:{ rewrite nth_error_nil in ntht'. discriminate. }
  destruct X as [[[_ Ru] Hl] Hpars]. rewrite Hl.
  destruct d as [decli [nthp parseq]].
  simpl in *. rewrite parseq.
  destruct y as [[_ onps] onp]. lia.
Qed.
