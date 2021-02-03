(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICWeakeningEnv PCUICWeakening
     PCUICSigmaCalculus (* for smash_context lemmas, to move *)
     PCUICSubstitution PCUICClosed PCUICCumulativity PCUICGeneration PCUICReduction
     PCUICEquality PCUICConfluence
     PCUICContextConversion PCUICContextSubst PCUICUnivSubstitution
     PCUICConversion PCUICInversion PCUICContexts PCUICArities
     PCUICSpine PCUICInductives PCUICValidity.

From Equations Require Import Equations.
Require Import Equations.Type.Relation_Properties.
Require Import Equations.Prop.DepElim.
Require Import ssreflect.

Local Set SimplIsCbn.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

Hint Rewrite reln_length : len.

Ltac substu := autorewrite with substu => /=.

Tactic Notation "substu" "in" hyp(id) :=
  autorewrite with substu in id; simpl in id.

Lemma conv_eq_ctx {cf:checker_flags} Σ Γ Γ' T U : Σ ;;; Γ |- T = U -> Γ = Γ' -> Σ ;;; Γ' |- T = U.
Proof. now intros H ->. Qed.

(* TODO Move *)
Lemma context_subst_subst_extended_subst inst s Δ : 
  context_subst Δ inst s ->
  s = map (subst0 (List.rev inst)) (extended_subst Δ 0).
Proof.
  intros sp.
  induction sp.
  - simpl; auto.
  - rewrite List.rev_app_distr /= lift0_id. f_equal.
    rewrite lift_extended_subst.
    rewrite map_map_compose. rewrite IHsp. apply map_ext.
    intros. rewrite (subst_app_decomp [_]). f_equal.
    simpl. rewrite simpl_subst ?lift0_id //.
  - simpl. len.
    f_equal; auto.
    rewrite IHsp.
    rewrite distr_subst. f_equal.
    simpl; len.
    pose proof (context_subst_length2 sp).
    rewrite -H. rewrite -(List.rev_length args).
    rewrite -(Nat.add_0_r #|List.rev args|).
    rewrite simpl_subst_rec; try lia.
    now rewrite lift0_id.
Qed.

Lemma spine_subst_extended_subst {cf:checker_flags} {Σ Γ inst s Δ} : 
  spine_subst Σ Γ inst s Δ ->
  s = map (subst0 (List.rev inst)) (extended_subst Δ 0).
Proof.
  intros [_ _ sp _]. now apply context_subst_subst_extended_subst in sp.
Qed.

(* Lemma spine_subst_extended_subst {cf:checker_flags} {Σ Γ inst s Δ} : 
  spine_subst Σ Γ inst s Δ ->
  forall Γ', subst_context s 0 Γ' s = map (subst0 (List.rev inst)) (extended_subst Δ 0).
Proof.
  intros [_ _ sp _]. now apply context_subst_subst_extended_subst in sp.
Qed.
 *)

Definition ind_subst mdecl ind u := inds (inductive_mind ind) u (ind_bodies mdecl).

Ltac pcuic := intuition eauto 5 with pcuic ||
  (try solve [repeat red; cbn in *; intuition auto; eauto 5 with pcuic || (try lia || congruence)]).

(** Inversion principles on inductive/coinductives types following from validity. *)

Lemma declared_constructor_valid_ty {cf:checker_flags} Σ Γ mdecl idecl i n cdecl u :
  wf Σ.1 ->
  wf_local Σ Γ ->
  declared_constructor Σ.1 (i, n) mdecl idecl cdecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  isType Σ Γ (type_of_constructor mdecl cdecl (i, n) u).
Proof.
  move=> wfΣ wfΓ declc Hu.
  eapply validity. eapply type_Construct; eauto.
Qed.

Lemma declared_inductive_valid_type {cf:checker_flags} Σ Γ mdecl idecl i u :
  wf Σ.1 ->
  wf_local Σ Γ ->
  declared_inductive Σ.1 i mdecl idecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  isType Σ Γ (subst_instance u (ind_type idecl)).
Proof.
  move=> wfΣ wfΓ declc Hu.
  pose declc as declc'.
  destruct (on_declared_inductive declc') as [onmind onind]; auto.
  apply onArity in onind.
  destruct onind as [s Hs].
  epose proof (PCUICUnivSubstitution.typing_subst_instance_decl Σ) as s'.
  destruct declc.
  specialize (s' [] _ _ _ _ u wfΣ d Hs Hu).
  simpl in s'. eexists; eauto.
  eapply (PCUICWeakening.weaken_ctx (Γ:=[]) Γ); eauto.
Qed.

Hint Resolve f_equal_nat : arith.

Lemma type_tFix_inv {cf:checker_flags} (Σ : global_env_ext) Γ mfix idx T : wf Σ ->
  Σ ;;; Γ |- tFix mfix idx : T ->
  { T' & { rarg & {f & (unfold_fix mfix idx = Some (rarg, f))  *
    wf_fixpoint Σ.1  mfix
  * (Σ ;;; Γ |- f : T') * (Σ ;;; Γ |- T' <= T) }}}%type.
Proof.
  intros wfΣ H. depind H.
  - unfold unfold_fix. rewrite e.
    specialize (nth_error_all e a0) as [s Hs].
    specialize (nth_error_all e a1) as Hty.
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
          ** clear IHAll.
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
  - destruct (IHtyping1 wfΣ) as [T' [rarg [f [[unf fty] Hcumul]]]].
    exists T', rarg, f. intuition auto.
    + eapply cumul_trans; eauto.
Qed.

Lemma subslet_cofix {cf:checker_flags} (Σ : global_env_ext) Γ mfix :
  wf_local Σ Γ ->
  cofix_guard Σ Γ mfix ->
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
      rewrite simpl_subst_k //. now len.
      apply subslet_cofix; auto. 
    * reflexivity.
  - destruct (IHtyping1 wfΣ) as [d [[[Hnth wfcofix] ?] ?]].
    exists d. intuition auto.
    eapply cumul_trans; eauto.
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
  move/andb_and: eqr => [eqinds rk].
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
    move/andb_and: eqinds => [eqk eql0].
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
    change (eq_kername ind k) with (Reflect.eqb ind k) in eqk.
    destruct (Reflect.eqb_spec ind k); auto. discriminate.
    discriminate.
  - discriminate.
  - discriminate.
Qed.

Section OnConstructor.
  Context {cf:checker_flags} {Σ : global_env} {ind mdecl idecl cdecl}
    {wfΣ: wf Σ} (declc : declared_constructor Σ ind mdecl idecl cdecl).

  Lemma on_constructor_wf_args : 
    wf_local (Σ, ind_universes mdecl)
    (arities_context (ind_bodies mdecl) ,,, ind_params mdecl ,,, cstr_args cdecl).
  Proof.
    pose proof (on_declared_constructor declc) as [[onmind oib] [cunivs [hnth onc]]].
    pose proof (on_cargs onc). simpl in X.
    eapply sorts_local_ctx_wf_local in X => //. clear X.
    eapply weaken_wf_local => //.
    eapply wf_arities_context; eauto. eapply declc.
    now eapply onParams.
  Qed.

  Lemma on_constructor_subst :
    wf_global_ext Σ (ind_universes mdecl) *
    wf_local (Σ, ind_universes mdecl)
    (arities_context (ind_bodies mdecl) ,,, ind_params mdecl ,,, cstr_args cdecl) *
    ∑ inst,
    spine_subst (Σ, ind_universes mdecl)
              (arities_context (ind_bodies mdecl) ,,, ind_params mdecl ,,,
                cstr_args cdecl)
              ((to_extended_list_k (ind_params mdecl) #|cstr_args cdecl|) ++
                (cstr_indices cdecl)) inst
            (ind_params mdecl ,,, ind_indices idecl). 
  Proof.
    pose proof (on_declared_constructor declc) as [[onmind oib] [cunivs [hnth onc]]].
    pose proof (onc.(on_cargs)). simpl in X.
    split. split. split.
    2:{ eapply (weaken_lookup_on_global_env'' _ _ (InductiveDecl mdecl)); tea.
        eapply declc. }
    red. split; eauto. simpl. 
    eapply (weaken_lookup_on_global_env' _ _ (InductiveDecl mdecl)); eauto.
    eapply declc.
    eapply sorts_local_ctx_wf_local in X => //. clear X.
    eapply weaken_wf_local => //.
    eapply wf_arities_context; eauto; eapply declc.
    now eapply onParams.
    destruct (on_ctype onc).
    rewrite onc.(cstr_eq) in t.
    rewrite -it_mkProd_or_LetIn_app in t.
    eapply inversion_it_mkProd_or_LetIn in t => //.
    unfold cstr_concl_head in t. simpl in t.
    eapply inversion_mkApps in t as [A [ta sp]].
    eapply inversion_Rel in ta as [decl [wfΓ [nth cum']]].
    rewrite nth_error_app_ge in nth. len. lia.
    autorewrite with len in nth.
    all:auto.
    assert ((#|ind_bodies mdecl| - S (inductive_ind ind.1) + #|ind_params mdecl| +
    #|cstr_args cdecl| -
    (#|cstr_args cdecl| + #|ind_params mdecl|)) = #|ind_bodies mdecl| - S (inductive_ind ind.1)) by lia.
    move: nth; rewrite H; clear H.
    case: nth_error_spec => // /= decl' Hdecl Hlen.
    intros [= ->].
    eapply (nth_errror_arities_context (Σ := (Σ, ind_universes mdecl)) declc) in Hdecl; eauto.
    rewrite Hdecl in cum'; clear Hdecl.
    assert(closed (ind_type idecl)).
    { pose proof (oib.(onArity)). rewrite (oib.(ind_arity_eq)) in X0 |- *.
      destruct X0 as [s Hs]. now apply subject_closed in Hs. } 
    rewrite lift_closed in cum' => //.
    eapply typing_spine_strengthen in sp; simpl. 2:pcuic.
    2:tea.
    move: sp. 
    rewrite (oib.(ind_arity_eq)).
    rewrite -it_mkProd_or_LetIn_app.
    move=> sp. simpl in sp.
    apply (arity_typing_spine (Σ, ind_universes mdecl)) in sp as [[Hlen' Hleq] [inst Hinst]] => //.
    clear Hlen'.
    rewrite [_ ,,, _]app_context_assoc in Hinst.
    now exists inst.
    apply weaken_wf_local => //.

    rewrite [_ ,,, _]app_context_assoc in wfΓ.
    eapply All_local_env_app_inv in wfΓ as [? ?].
    eapply on_minductive_wf_params_indices, declc.
  Qed.
End OnConstructor.

Section OnConstructorExt.
  Context {cf:checker_flags} {Σ : global_env_ext} {ind mdecl idecl cdecl}
    {wfΣ: wf Σ} (declc : declared_constructor Σ ind mdecl idecl cdecl).

  Lemma on_constructor_inst u : 
    consistent_instance_ext Σ (ind_universes mdecl) u ->
    wf_local Σ (subst_instance u
      (arities_context (ind_bodies mdecl) ,,, ind_params mdecl ,,, cstr_args cdecl)) *
    ∑ inst,
    spine_subst Σ
            (subst_instance u
              (arities_context (ind_bodies mdecl) ,,, ind_params mdecl ,,,
                cstr_args cdecl))
            (map (subst_instance u)
              (to_extended_list_k (ind_params mdecl) #|cstr_args cdecl|) ++
            map (subst_instance u) (cstr_indices cdecl)) inst
            (subst_instance u (ind_params mdecl) ,,,
            subst_instance u (ind_indices idecl)). 
  Proof.
    intros cu.
    destruct (on_constructor_subst declc) as [[wfext wfl] [inst sp]].
    eapply wf_local_subst_instance in wfl; eauto. split=> //.
    eapply spine_subst_inst in sp; eauto.
    rewrite map_app in sp. rewrite -subst_instance_app_ctx.
    eexists ; eauto.
  Qed.
End OnConstructorExt.

Hint Rewrite subst_instance_assumptions to_extended_list_k_length : len.

Require Import ssrbool.

Lemma smash_context_app_def Γ na b ty :
  smash_context [] (Γ ++ [{| decl_name := na; decl_body := Some b; decl_type := ty |}]) =
  smash_context [] (subst_context [b] 0 Γ).
Proof.
  now rewrite smash_context_app smash_context_acc /= subst_empty lift0_id lift0_context /=
    subst_context_nil app_nil_r (smash_context_subst []).
Qed.

Lemma smash_context_app_ass Γ na ty :
  smash_context [] (Γ ++ [{| decl_name := na; decl_body := None; decl_type := ty |}]) =
  smash_context [] Γ ++ [{| decl_name := na; decl_body := None; decl_type := ty |}].
Proof.
  now rewrite smash_context_app smash_context_acc /= subst_context_lift_id.
Qed.

Lemma lift_context_add k k' n Γ : lift_context (k + k') n Γ = lift_context k n (lift_context k' n Γ).
Proof.
  induction Γ => //.
  rewrite !lift_context_snoc IHΓ; f_equal.
  destruct a as [na [b|] ty]; rewrite /lift_decl /map_decl /=; simpl; f_equal;
  len; rewrite simpl_lift //; try lia.
Qed.

Lemma distr_lift_subst_context_rec n k s Γ k' : lift_context n (k' + k) (subst_context s k' Γ) =
  subst_context (map (lift n k) s) k' (lift_context n (#|s| + k + k') Γ).
Proof.
  rewrite !lift_context_alt !subst_context_alt.
  rewrite !mapi_compose.
  apply mapi_ext.
  intros n' x.
  rewrite /lift_decl /subst_decl !compose_map_decl.
  apply map_decl_ext => y. len.
  replace (Nat.pred #|Γ| - n' + (#|s| + k + k'))
    with ((Nat.pred #|Γ| - n' + k') + #|s| + k) by lia.
  rewrite -distr_lift_subst_rec. f_equal. lia.
Qed.

Lemma subst_context_lift_id Γ k : subst_context [tRel 0] k (lift_context 1 (S k) Γ) = Γ.
Proof.
  rewrite subst_context_alt lift_context_alt.
  rewrite mapi_compose.
  replace Γ with (mapi (fun k x => x) Γ) at 2.
  2:unfold mapi; generalize 0; induction Γ; simpl; intros; auto; congruence.
  apply mapi_ext.
  len.
  intros n [? [?|] ?]; unfold lift_decl, subst_decl, map_decl; simpl.
  generalize (Nat.pred #|Γ| - n).
  intros. 
  now rewrite !Nat.add_succ_r !subst_rel0_lift_id.
  now rewrite !Nat.add_succ_r !subst_rel0_lift_id.
Qed.

Lemma assumption_context_app_inv Γ Δ : assumption_context Γ -> assumption_context Δ ->  
  assumption_context (Γ ++ Δ).
Proof.
  induction 1; try constructor; auto.
Qed.

Lemma closedn_ctx_upwards k k' Γ : 
  closedn_ctx k Γ -> k <= k' ->
  closedn_ctx k' Γ.
Proof.
  induction Γ; auto. rewrite !closed_ctx_decl /=.
  move/andb_and => [cla clΓ] le.
  rewrite (IHΓ clΓ le).
  rewrite (closed_decl_upwards _ _ cla) //. lia.
Qed.

Lemma closedn_expand_lets k (Γ : context) t : 
  closedn (k + context_assumptions Γ) (expand_lets Γ t) -> 
  closedn (k + #|Γ|) t.
Proof.
  revert k t.
  induction Γ as [|[na [b|] ty] Γ] using ctx_length_rev_ind; intros k t; simpl; auto.
  - now rewrite /expand_lets /expand_lets_k subst_empty lift0_id.
  - len.
    rewrite !expand_lets_vdef.
    specialize (H (subst_context [b] 0 Γ) ltac:(len; lia)).
    autorewrite with len in H.
    intros cl.
    specialize (H _ _ cl).
    eapply (closedn_subst_eq' _ k) in H.
    simpl in *. now rewrite Nat.add_assoc.
  - len.
    rewrite !expand_lets_vass. simpl. intros cl.
    specialize (H Γ ltac:(len; lia)).
    rewrite (Nat.add_comm _ 1) Nat.add_assoc in cl.
    now rewrite (Nat.add_comm _ 1) Nat.add_assoc.
Qed.

Ltac len' := rewrite_strat (topdown (repeat (old_hints len))).

Tactic Notation "len'" "in" hyp(id) :=
  rewrite_strat (topdown (repeat (old_hints len))) in id.

Lemma closedn_expand_lets_eq k (Γ : context) k' t :
  closedn_ctx k Γ ->
  closedn (k + k' + context_assumptions Γ) (expand_lets_k Γ k' t) =
  closedn (k + k' + #|Γ|) t.
Proof.
  revert k k' t.
  induction Γ as [|[na [b|] ty] Γ] using ctx_length_rev_ind; intros k k' t;
    rewrite ?closedn_ctx_app /= /id /=; simpl; auto.
  - now rewrite /expand_lets /expand_lets_k /= subst_empty lift0_id.
  - move/andb_and=> [cld clΓ]. len'.
    rewrite !expand_lets_k_vdef.
    simpl in cld |- *. move/andb_and: cld => /= [clb _].
    specialize (H (subst_context [b] 0 Γ) ltac:(len; lia)).
    len' in H; simpl in H. len.
    rewrite H /=.
    relativize k. eapply closedn_ctx_subst. simpl. 3:rewrite Nat.add_0_r //.
    now rewrite Nat.add_0_r. now rewrite /= clb.
    rewrite -Nat.add_assoc -closedn_subst_eq. simpl. now rewrite clb.
    simpl; lia_f_equal.
  - len'. move/andb_and => [clty clΓ]. 
    rewrite !expand_lets_k_vass. simpl.
    specialize (H Γ ltac:(len; lia) (S k)).
    rewrite Nat.add_assoc !Nat.add_succ_r !Nat.add_0_r. apply H.
    now rewrite Nat.add_1_r in clΓ.
Qed.

Lemma closedn_ctx_expand_lets k Γ Δ :
  closedn_ctx k Γ ->
  closedn_ctx (k + #|Γ|) Δ ->
  closedn_ctx (k + context_assumptions Γ) (expand_lets_ctx Γ Δ).
Proof.
  intros clΓ clΔ.
  rewrite /expand_lets_ctx /expand_lets_k_ctx.
  rewrite -(Nat.add_0_r (k + context_assumptions Γ)).
  eapply closedn_ctx_subst; len; simpl.
  replace (k + context_assumptions Γ + #|Γ|) with (context_assumptions Γ + (k + #|Γ|)) by lia.
  eapply closedn_ctx_lift => //.
  eapply forallb_impl. 2:eapply closedn_extended_subst_gen; eauto.
  simpl; auto.
Qed.

Lemma closedn_to_extended_list_k k Γ k' : 
  k' + #|Γ| <= k ->
  forallb (closedn k) (to_extended_list_k Γ k').
Proof.
  move=> le. rewrite /to_extended_list_k.
  eapply Forall_forallb; eauto. 2:{ intros x H; eapply H. }
  eapply Forall_impl. eapply reln_list_lift_above. constructor.
  simpl; intros.
  destruct H as [n [-> leq]]. simpl.
  eapply Nat.ltb_lt. lia.
Qed.

Lemma map_subst_extended_subst Γ k : 
  map (subst0 (List.rev (to_extended_list_k Γ k))) (extended_subst Γ 0) = 
  all_rels Γ k 0.
Proof.
  unfold to_extended_list_k.
  
  induction Γ in k |- *; simpl; auto.
  destruct a as [na [b|] ty]; simpl.
  f_equal. len.
  rewrite lift0_id.
  rewrite distr_subst. len.
  rewrite simpl_subst_k. now len. 
  rewrite IHΓ. now rewrite Nat.add_1_r.
  rewrite IHΓ. now rewrite Nat.add_1_r.
  rewrite nth_error_rev. len => /= //. simpl; lia.
  len. simpl.
  rewrite Nat.sub_succ. rewrite List.rev_involutive.
  change (0 - 0) with 0. rewrite Nat.sub_0_r.
  f_equal.
  rewrite reln_acc nth_error_app_ge; len => //.
  simpl. now rewrite Nat.sub_diag /=.
  rewrite -IHΓ. simpl.
  rewrite reln_acc List.rev_app_distr /=. 
  rewrite (map_subst_app_decomp [tRel k]).
  simpl. rewrite lift_extended_subst.
  rewrite map_map_compose. apply map_ext.
  intros x. f_equal. now rewrite Nat.add_1_r.
  len. simpl.
  rewrite simpl_subst // lift0_id //.
Qed.

Lemma subst_ext_list_ext_subst Γ k' k t :
  subst (List.rev (to_extended_list_k Γ k)) k'
    (subst (extended_subst Γ 0) k'
      (lift (context_assumptions Γ) (k' + #|Γ|) t)) =
  subst (all_rels Γ k 0) k' t.
Proof.
  epose proof (distr_subst_rec _ _ _ 0 _).
  rewrite Nat.add_0_r in H. rewrite -> H. clear H.
  len.
  rewrite simpl_subst_k. now len. 
  now rewrite map_subst_extended_subst.
Qed.

Lemma expand_lets_ctx_o_lets Γ k k' Δ :
  subst_context (List.rev (to_extended_list_k Γ k)) k' (expand_lets_k_ctx Γ k' Δ) = 
  subst_context (all_rels Γ k 0) k' Δ.
Proof.
  revert k k'; induction Δ using rev_ind; simpl; auto.
  intros k k'; rewrite expand_lets_k_ctx_decl /map_decl /=.
  rewrite !subst_context_app /=.
  simpl; unfold app_context.
  f_equal. specialize (IHΔ k (S k')). simpl in IHΔ.
  rewrite -IHΔ.
  destruct x; simpl.
  destruct decl_body; simpl in * => //.
  unfold subst_context, fold_context_k; simpl.
  f_equal.
  unfold expand_lets_k, subst_context => /=. 
  unfold map_decl; simpl. unfold map_decl. simpl. f_equal.
  destruct (decl_body x); simpl. f_equal.
  now rewrite subst_ext_list_ext_subst. auto.
  now rewrite subst_ext_list_ext_subst.
Qed.

Lemma subst_subst_context s k s' Γ : 
  subst_context s k (subst_context s' 0 Γ) = 
  subst_context (map (subst s k) s') 0 (subst_context s (#|s'| + k) Γ).
Proof.
  rewrite !subst_context_alt.
  rewrite !mapi_compose; len.
  eapply mapi_ext. intros n x.
  rewrite /subst_decl !compose_map_decl.
  apply map_decl_ext. intros t.
  rewrite Nat.add_0_r.
  remember (Nat.pred #|Γ| - n) as i.
  rewrite distr_subst_rec. lia_f_equal.
Qed.

Lemma closed_ctx_subst n k ctx : closedn_ctx k ctx = true -> subst_context n k ctx = ctx.
Proof.
  induction ctx in n, k |- *; auto.
  simpl.
  move/andb_and => /= [Hctx Hd].
  rewrite subst_context_snoc /snoc /= IHctx // subst_decl_closed //.
Qed.

Lemma expand_lets_k_ctx_subst_id' Γ k Δ : 
  closed_ctx Γ ->
  closedn_ctx #|Γ| Δ -> 
  expand_lets_k_ctx Γ k (subst_context (List.rev (to_extended_list_k Γ k)) 0 
    (expand_lets_ctx Γ Δ)) =
  subst_context (List.rev (to_extended_list_k (smash_context [] Γ) k)) 0
    (expand_lets_ctx Γ Δ).
Proof.
  intros clΓ clΔ.
  rewrite {1}/expand_lets_k_ctx.
  rewrite closed_ctx_lift.
  rewrite -(Nat.add_0_r (k + #|Γ|)).
  eapply closedn_ctx_subst. simpl; len'.
  eapply closedn_ctx_expand_lets. eapply closedn_ctx_upwards; eauto. lia.
  eapply closedn_ctx_upwards; eauto. lia.
  rewrite forallb_rev. now eapply closedn_to_extended_list_k.
  rewrite subst_subst_context. len'.
  rewrite map_rev extended_subst_to_extended_list_k.
  rewrite (closed_ctx_subst _ (context_assumptions Γ + k)) //.
  rewrite Nat.add_comm. eapply closedn_ctx_expand_lets => //.
  eapply closedn_ctx_upwards; eauto. lia.
  eapply closedn_ctx_upwards; eauto. lia.
Qed.

Lemma subst_extended_lift Γ k : 
  closed_ctx Γ ->
  map (subst0 (List.rev (to_extended_list_k (smash_context [] Γ) k)))
    (extended_subst Γ 0) = extended_subst Γ k.
Proof.
  induction Γ in k |- *; intros cl; simpl; auto.
  destruct a as [na [b|] ty] => /=.
  len.
  rewrite closed_ctx_decl in cl. move/andb_and: cl => [cld clΓ].
  simpl. f_equal.
  rewrite distr_subst. len.
  simpl in cld.
  rewrite IHΓ //. f_equal. rewrite simpl_subst_k.
  len. rewrite PCUICSubstitution.context_assumptions_smash_context /= //.
  rewrite lift_closed //. now move/andb_and: cld => /= //.
  rewrite IHΓ //.

  simpl map.
  rewrite Nat.sub_diag. rewrite nth_error_rev.
  len. simpl.  rewrite context_assumptions_smash_context /=. lia.
  len'. rewrite List.rev_involutive /= context_assumptions_smash_context /=.
  rewrite smash_context_acc /=.
  f_equal; auto. rewrite reln_acc /=.
  rewrite nth_error_app_ge. len. simpl.
  rewrite context_assumptions_smash_context /=. lia.
  len. simpl.
  rewrite context_assumptions_smash_context /=.
  replace (S (context_assumptions Γ) - 1 - context_assumptions Γ) with 0 by lia.
  now simpl.
  rewrite reln_acc List.rev_app_distr /=.
  rewrite lift_extended_subst.
  rewrite map_map_compose.
  rewrite map_subst_lift1.
  rewrite closed_ctx_decl in cl. move/andb_and: cl => [cld clΓ].
  now rewrite IHΓ // Nat.add_1_r.
Qed.
From MetaCoq.PCUIC Require Import PCUICInst.

(* Lemma Upn_rshiftk n s k : ⇑^n s ∘s shiftk k =1 shiftk k ∘s (idsn n ⋅n s).
Proof.
  intros i. rewrite Upn_eq; sigma.
  destruct (leb_spec_Set (S i) n).
  - rewrite subst_consn_lt'. len; try lia.
    cbn.
    rewrite /subst_fn nth_error_map /= idsn_lt /shiftk; len; try lia.
    rewrite subst_consn_lt'; len; try lia.
    simpl.
  now destruct nth_error => /= //; len. 
  reflexivity. *)

Lemma closed_subst_map_lift s n k t :
  closedn (#|s| + k) t ->
  subst (map (lift0 n) s) k t = subst s (n + k) (lift n k t).
Proof.
  intros cl.
  sigma.
  eapply PCUICInst.inst_ext_closed; tea.
  intros x Hx.
  rewrite -Upn_Upn. Nat.add_comm Upn_Upn Upn_compose. shiftn_Upn; sigma.
  now rewrite !Upn_subst_consn_lt; len; try lia.
Qed.

Lemma subst_map_lift_lift_context (Γ : context) k s : 
  closedn_ctx #|s| Γ ->
  subst_context (map (lift0 k) s) 0 Γ = 
  subst_context s k (lift_context k 0 Γ).
Proof.
  induction Γ as [|[? [] ?] ?] in k |- *; intros cl; auto;
    rewrite lift_context_snoc !subst_context_snoc /= /subst_decl /map_decl /=;
    rewrite closed_ctx_decl in cl;  move/andb_and: cl => [cld clΓ].
  - rewrite IHΓ //. f_equal. f_equal. f_equal;
    len.
    rewrite closed_subst_map_lift //. now move/andb_and: cld => /=.
    lia_f_equal.
    len.
    rewrite closed_subst_map_lift //. now move/andb_and: cld => /=.
    lia_f_equal.
  - f_equal. apply IHΓ => //.
    f_equal; len. rewrite closed_subst_map_lift //.
    lia_f_equal.
Qed.

Lemma subst_context_lift_context_comm (Γ : context) n k k' s : 
  k' = k + n ->
  subst_context s k' (lift_context n k Γ) =
  lift_context n k (subst_context s k Γ).
Proof.
  intros ->; induction Γ as [|[? [] ?] ?] in |- *; auto;
    rewrite !lift_context_snoc !subst_context_snoc !lift_context_snoc /= 
      /subst_decl /lift_decl /map_decl /=.
  - rewrite IHΓ //. f_equal. f_equal. f_equal; len.
    rewrite commut_lift_subst_rec. lia. lia_f_equal.
    len.
    rewrite commut_lift_subst_rec. lia. lia_f_equal.
  - f_equal. apply IHΓ => //.
    f_equal; len. rewrite commut_lift_subst_rec //; try lia.
    lia_f_equal.
Qed.

Lemma on_constructor_inst_pars_indices {cf:checker_flags} {Σ ind u mdecl idecl cdecl Γ pars parsubst} : 
  wf Σ.1 -> 
  declared_constructor Σ.1 ind mdecl idecl cdecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  spine_subst Σ Γ pars parsubst (subst_instance u (ind_params mdecl)) ->
  wf_local Σ (subst_instance u (ind_params mdecl) ,,,
    subst_context (inds (inductive_mind ind.1) u (ind_bodies mdecl)) #|ind_params mdecl|
    (subst_instance u (cstr_args cdecl))) *
  ∑ inst,
  spine_subst Σ
          (Γ ,,, subst_context parsubst 0 (subst_context (ind_subst mdecl ind.1 u) #|ind_params mdecl|
            (subst_instance u (cstr_args cdecl))))
          (map (subst parsubst #|cstr_args cdecl|)
            (map (subst (ind_subst mdecl ind.1 u) (#|cstr_args cdecl| + #|ind_params mdecl|))
              (map (subst_instance u) (cstr_indices cdecl))))
          inst
          (lift_context #|cstr_args cdecl| 0
          (subst_context parsubst 0 (subst_instance u (ind_indices idecl)))). 
Proof.
  move=> wfΣ declc cext sp.
  (* destruct (on_declared_constructor declc) as []. .declm oi oib onc *)
  destruct (on_constructor_inst declc u) as [wfl [inst sp']]; auto.
  rewrite !subst_instance_app in sp'.
  eapply spine_subst_app_inv in sp' as [spl spr]; auto.
  rewrite (spine_subst_extended_subst spl) in spr.
  rewrite subst_context_map_subst_expand_lets in spr; try now len.
  rewrite subst_instance_to_extended_list_k in spr.
  2:now len.
  rewrite lift_context_subst_context.
  rewrite app_assoc in spr.
  eapply spine_subst_subst_first in spr; eauto.
  2:eapply subslet_inds; eauto; eapply declc.
  autorewrite with len in spr.
  rewrite subst_context_app in spr.
  assert (closed_ctx (subst_instance u (ind_params mdecl)) /\ closedn_ctx #|ind_params mdecl| (subst_instance u (ind_indices idecl)))
  as [clpars clinds].
  { pose proof (on_minductive_wf_params_indices declc).
    eapply closed_wf_local in X => //.
    rewrite closedn_ctx_app in X; simpl; eauto;
    move/andb_and: X; intuition auto;
    now rewrite closedn_subst_instance_context. }
  assert (closedn_ctx (#|ind_params mdecl| + #|cstr_args cdecl|) (subst_instance u (ind_indices idecl))) 
    as clinds'.
  { eapply closedn_ctx_upwards; eauto. lia. }
  rewrite closed_ctx_subst // in spr.
  rewrite (closed_ctx_subst (inds (inductive_mind ind.1) u (ind_bodies mdecl)) _ (subst_context (List.rev _) _ _)) in spr.
  { len.
    rewrite -(Nat.add_0_r (#|cstr_args cdecl| + #|ind_params mdecl|)).
    eapply closedn_ctx_subst. len.
    rewrite -(subst_instance_assumptions u).
    eapply closedn_ctx_expand_lets. eapply closedn_ctx_upwards; eauto. lia.
    len. eapply closedn_ctx_upwards; eauto. lia.
    rewrite forallb_rev. eapply closedn_to_extended_list_k.
    now len. }
  autorewrite with len in spr.
  split.
  { autorewrite with len in spr. apply spr. }
  eapply spine_subst_weaken in spr.
  3:eapply (spine_dom_wf _ _ _ _ _ sp); eauto. 2:eauto.
  rewrite app_context_assoc in spr.
  eapply spine_subst_subst in spr; eauto. 2:eapply sp.
  autorewrite with len in spr.
  rewrite {4}(spine_subst_extended_subst sp) in spr.
  rewrite subst_context_map_subst_expand_lets_k in spr; try now len.
  rewrite List.rev_length. now rewrite -(context_subst_length2 sp).
  rewrite expand_lets_k_ctx_subst_id' in spr. now len. now len.
  rewrite -subst_context_map_subst_expand_lets_k in spr; try len.
  rewrite context_assumptions_smash_context /=. now len.
  rewrite subst_subst_context in spr. autorewrite with len in spr.
  rewrite subst_extended_lift // in spr.
  rewrite lift_extended_subst in spr.
  rewrite (map_map_compose _ _ _ _ (subst (List.rev pars) _)) in spr.
  assert (map
              (fun x : term =>
               subst (List.rev pars) #|cstr_args cdecl|
                 (lift0 #|cstr_args cdecl| x))
              (extended_subst (subst_instance u (ind_params mdecl)) 0) = 
              (map
              (fun x : term =>
              (lift0 #|cstr_args cdecl|
                (subst (List.rev pars) 0 x)))
              (extended_subst (subst_instance u (ind_params mdecl)) 0))
              ).
  eapply map_ext => x.
  now rewrite -(commut_lift_subst_rec _ _ _ 0).
  rewrite H in spr. clear H.
  rewrite -(map_map_compose  _ _  _ _ (lift0 #|cstr_args cdecl|)) in spr.
  rewrite -(spine_subst_extended_subst sp) in spr.
  rewrite subst_map_lift_lift_context in spr.
  rewrite -(context_subst_length sp).
  len.
  rewrite closed_ctx_subst //. 
  rewrite (closed_ctx_subst (List.rev pars)) // in spr.
  eexists. eauto.
Qed.

Definition R_ind_universes  {cf:checker_flags} (Σ : global_env_ext) ind n i i' :=
  R_global_instance Σ (eq_universe (global_ext_constraints Σ))
    (leq_universe (global_ext_constraints Σ)) (IndRef ind) n i i'.



Lemma mkApps_ind_typing_spine {cf:checker_flags} Σ Γ Γ' ind i
  inst ind' i' args args' : 
  wf Σ.1 ->
  wf_local Σ Γ ->
  isType Σ Γ (it_mkProd_or_LetIn Γ' (mkApps (tInd ind i) args)) ->
  typing_spine Σ Γ (it_mkProd_or_LetIn Γ' (mkApps (tInd ind i) args)) inst 
    (mkApps (tInd ind' i') args') ->
  ∑ instsubst, (make_context_subst (List.rev Γ') inst [] = Some instsubst) *
  (#|inst| = context_assumptions Γ' /\ ind = ind' /\ R_ind_universes Σ ind #|args| i i') *
  All2 (fun par par' => Σ ;;; Γ |- par = par') (map (subst0 instsubst) args) args' *
  (subslet Σ Γ instsubst Γ').
Proof.
  intros wfΣ wfΓ; revert args args' ind i ind' i' inst.
  revert Γ'. refine (ctx_length_rev_ind _ _ _); simpl.
  - intros args args' ind i ind' i' inst wat Hsp.
    depelim Hsp.
    eapply invert_cumul_ind_l in c as [i'' [args'' [? ?]]]; auto.
    eapply red_mkApps_tInd in r as [? [eq ?]]; auto. solve_discr.
    noconf H. noconf H0.
    exists nil.
    intuition auto. clear i0.
    revert args' a. clear -b wfΣ wfΓ. induction b; intros args' H; depelim H; constructor.
    rewrite subst_empty.
    transitivity y; auto. symmetry.
    now eapply red_conv. now eauto.
    eapply invert_cumul_prod_r in c as [? [? [? [[[? ?] ?] ?]]]]; auto.
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
        eapply isType_tLetIn_red in wat; auto.
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
      now autorewrite with len in H2.
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
      now eapply isType_tLetIn_dom in wat.
    + rewrite context_assumptions_app /=.
      pose proof (typing_spine_WAT_concl Hsp).
      depelim Hsp.
      eapply invert_cumul_prod_l in c as [? [? [? [[[? ?] ?] ?]]]]; auto.
      eapply red_mkApps_tInd in r as [? [eq ?]]; auto. now solve_discr.
      eapply cumul_Prod_inv in c as [conva cumulB].
      eapply (substitution_cumul0 _ _ _ _ _ _ hd) in cumulB; auto.
      rewrite /subst1 subst_it_mkProd_or_LetIn /= in cumulB.
      specialize (IH (subst_context [hd] 0 Γ')).
      forward IH by rewrite subst_context_length; lia.
      specialize (IH (map (subst [hd] #|Γ'|) args) args' ind i ind' i' tl). all:auto.
      have isTypes: isType Σ Γ
      (it_mkProd_or_LetIn (subst_context [hd] 0 Γ')
          (mkApps (tInd ind i) (map (subst [hd] #|Γ'|) args))). {
        move: wat; rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /= => wat.
        eapply isType_tProd in wat; auto. destruct wat as [isty wat].
        epose proof (isType_subst wfΣ (Γ:=Γ) (Δ:=[vass na ty])).
        forward X0. constructor; auto.
        specialize (X0 (it_mkProd_or_LetIn Γ' (mkApps (tInd ind i) args)) [hd]).
        forward X0. constructor. constructor. rewrite subst_empty; auto.
        eapply isType_tProd in i0; auto. destruct i0. 
        eapply type_Cumul'; eauto. now eapply conv_cumul.
        now rewrite /subst1 subst_it_mkProd_or_LetIn subst_mkApps Nat.add_0_r
        in X0. }
      rewrite subst_mkApps Nat.add_0_r in cumulB. simpl in *. 
      rewrite context_assumptions_subst in IH.
      eapply typing_spine_strengthen in Hsp.
      3:eapply cumulB. all:eauto.
      intuition auto.
      destruct X1 as [isub [[[Hisub [Htl [Hind Hu]]] Hargs] Hs]].
      exists (isub ++ [hd]). rewrite List.rev_app_distr.
      autorewrite with len in Hu.
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
        eapply isType_tProd in wat as [Hty _]; auto.
        eapply type_Cumul'; eauto. now eapply conv_cumul.
Qed.

Lemma wf_cofixpoint_typing_spine {cf:checker_flags} (Σ : global_env_ext) Γ ind u mfix idx d args args' : 
  wf Σ.1 -> wf_local Σ Γ ->
  wf_cofixpoint Σ.1 mfix ->
  nth_error mfix idx = Some d ->
  isType Σ Γ (dtype d) ->
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
  declared_constructor Σ.1 (i, n) mdecl idecl cdecl ->
  (i = i') * 
  (* Universe instances match *)
  R_ind_universes Σ i (context_assumptions (ind_params mdecl) + #|cstr_indices cdecl|) u u' *
  consistent_instance_ext Σ (ind_universes mdecl) u' *    
  (#|args| = (ind_npars mdecl + context_assumptions cdecl.(cstr_args))%nat) *
  ∑ parsubst argsubst parsubst' argsubst',
    let parctx := (subst_instance u (ind_params mdecl)) in
    let parctx' := (subst_instance u' (ind_params mdecl)) in
    let argctx := (subst_context parsubst 0
    ((subst_context (inds (inductive_mind i) u mdecl.(ind_bodies)) #|ind_params mdecl|
    (subst_instance u cdecl.(cstr_args))))) in
    let argctx2 := (subst_context parsubst' 0
    ((subst_context (inds (inductive_mind i) u' mdecl.(ind_bodies)) #|ind_params mdecl|
    (subst_instance u' cdecl.(cstr_args))))) in
    let argctx' := (subst_context parsubst' 0 (subst_instance u' idecl.(ind_indices))) in
    
    spine_subst Σ Γ (firstn (ind_npars mdecl) args) parsubst parctx *
    spine_subst Σ Γ (firstn (ind_npars mdecl) args') parsubst' parctx' *
    spine_subst Σ Γ (skipn (ind_npars mdecl) args) argsubst argctx *
    spine_subst Σ Γ (skipn (ind_npars mdecl) args')  argsubst' argctx' *

    ∑ s, sorts_local_ctx (lift_typing typing) Σ Γ argctx2 s *
    (** Parameters match *)
    (All2 (fun par par' => Σ ;;; Γ |- par = par') 
      (firstn mdecl.(ind_npars) args) 
      (firstn mdecl.(ind_npars) args') * 

    (** Indices match *)
    All2 (fun par par' => Σ ;;; Γ |- par = par') 
      (map (subst0 (argsubst ++ parsubst) ∘ 
      subst (inds (inductive_mind i) u mdecl.(ind_bodies)) (#|cdecl.(cstr_args)| + #|ind_params mdecl|)
      ∘ (subst_instance u)) 
        cdecl.(cstr_indices))
      (skipn mdecl.(ind_npars) args')).
Proof.
  intros Γ n i args u i' args' u' mdecl idecl cdecl h declc.
  destruct (on_declared_constructor declc) as [[onmind onind] [? [_ onc]]].
  unshelve epose proof (env_prop_typing _ _ validity_env _ _ _ _ _ h) as vi'; eauto using typing_wf_local.
  eapply inversion_mkApps in h; auto.
  destruct h as [T [hC hs]].
  apply inversion_Construct in hC
    as [mdecl' [idecl' [cdecl' [hΓ [isdecl [const htc]]]]]]; auto.
  assert (vty:=declared_constructor_valid_ty _ _ _ _ _ _ _ _ wfΣ hΓ isdecl const). 
  eapply typing_spine_strengthen in hs. 3:eapply htc. all:eauto.
  destruct (declared_constructor_inj isdecl declc) as [? [? ?]].
  subst mdecl' idecl' cdecl'. clear isdecl.
  pose proof (on_constructor_inst declc _ const).
  destruct declc as [decli declc].
  destruct onc as [argslength conclhead cdecl_eq [cs' t] cargs cinds]; simpl.
  simpl in *. 
  unfold type_of_constructor in hs. simpl in hs.
  rewrite cdecl_eq in hs.  
  rewrite !subst_instance_it_mkProd_or_LetIn in hs.
  rewrite !subst_it_mkProd_or_LetIn subst_instance_length Nat.add_0_r in hs.
  rewrite subst_instance_mkApps subst_mkApps subst_instance_length in hs.
  assert (Hind : inductive_ind i < #|ind_bodies mdecl|).
  { destruct decli.
    now eapply nth_error_Some_length in H0. }
  rewrite (subst_inds_concl_head i) in hs => //.
  rewrite -it_mkProd_or_LetIn_app in hs.
  assert(ind_npars mdecl = context_assumptions (ind_params mdecl)).
  { now pose (onNpars onmind). }
  assert (closed_ctx (ind_params mdecl)).
  { destruct onmind.
    red in onParams. now apply closed_wf_local in onParams. }
  eapply mkApps_ind_typing_spine in hs as [isubst [[[Hisubst [Hargslen [Hi Hu]]] Hargs] Hs]]; auto.
  subst i'.
  eapply (isType_mkApps_Ind wfΣ decli) in vi' as (parsubst & argsubst & (spars & sargs) & cons) => //.
  split=> //. split=> //.
  split; auto. split => //.
  now autorewrite with len in Hu.
  now rewrite Hargslen context_assumptions_app !context_assumptions_subst !subst_instance_assumptions; lia.

  exists (skipn #|cdecl.(cstr_args)| isubst), (firstn #|cdecl.(cstr_args)| isubst).
  apply make_context_subst_spec in Hisubst.
  move: Hisubst.
  rewrite List.rev_involutive.
  move/context_subst_app.
  rewrite !subst_context_length !subst_instance_length.
  rewrite context_assumptions_subst subst_instance_assumptions -H.
  move=>  [argsub parsub].
  rewrite closed_ctx_subst in parsub.
  now rewrite closedn_subst_instance_context.
  eapply subslet_app_inv in Hs.
  move: Hs. len. intuition auto.
  rewrite closed_ctx_subst in a0 => //.
  now rewrite closedn_subst_instance_context.

  (*rewrite -Heqp in spars sargs. simpl in *. clear Heqp. *)
  exists parsubst, argsubst.
  assert(wfar : wf_local Σ
  (Γ ,,, subst_instance u' (arities_context (ind_bodies mdecl)))).
  { eapply weaken_wf_local => //.
    eapply wf_local_instantiate => //; destruct decli; eauto.
    eapply wf_arities_context => //; eauto. }
  assert(wfpars : wf_local Σ (subst_instance u (ind_params mdecl))).
    { eapply on_minductive_wf_params => //; eauto. }

  intuition auto; try split; auto.
  - apply weaken_wf_local => //.
  - pose proof (subslet_length a0). rewrite subst_instance_length in H1.
    rewrite -H1 -subst_app_context.
    eapply (substitution_wf_local _ _ (subst_instance u (arities_context (ind_bodies mdecl) ,,, ind_params mdecl))); eauto.
    rewrite subst_instance_app; eapply subslet_app; eauto.
    now rewrite closed_ctx_subst ?closedn_subst_instance_context.
    eapply (weaken_subslet _ _ _ _ []) => //.
    now eapply subslet_inds; eauto.
    rewrite -app_context_assoc.
    eapply weaken_wf_local => //.
    rewrite -subst_instance_app_ctx. 
    apply a.
  - exists (map (subst_instance_univ u') x). split.
    move/onParams: onmind. rewrite /on_context.
    pose proof (wf_local_instantiate Σ (InductiveDecl mdecl) (ind_params mdecl) u').
    move=> H'. eapply X in H'; eauto.
    2:destruct decli; eauto.
    clear -wfar wfpars wfΣ hΓ cons decli t cargs sargs H0 H' a spars a0.
    eapply (subst_sorts_local_ctx _ _ []
      (subst_context (inds (inductive_mind i) u' (ind_bodies mdecl)) 0 
        (subst_instance u' (ind_params mdecl)))) => //.
    simpl. eapply weaken_wf_local => //.
    rewrite closed_ctx_subst => //.
    now rewrite closedn_subst_instance_context.
    simpl. rewrite -(subst_instance_length u' (ind_params mdecl)).
    eapply (subst_sorts_local_ctx _ _ _ (subst_instance u' (arities_context (ind_bodies mdecl)))) => //.
    eapply weaken_wf_local => //.
    rewrite -app_context_assoc.
    eapply weaken_sorts_local_ctx => //.
    rewrite -subst_instance_app_ctx.
    eapply sorts_local_ctx_instantiate => //; destruct decli; eauto.
    eapply (weaken_subslet _ _ _ _ []) => //.
    now eapply subslet_inds; eauto.
    rewrite closed_ctx_subst ?closedn_subst_instance_context. auto.
    apply spars.
    
    move: (All2_firstn  _ _ _ _ _ mdecl.(ind_npars) Hargs).
    move: (All2_skipn  _ _ _ _ _ mdecl.(ind_npars) Hargs).
    clear Hargs.
    rewrite !map_map_compose !map_app.
    rewrite -map_map_compose.
    rewrite (firstn_app_left _ 0).
    { rewrite !map_length to_extended_list_k_length. lia. }
    rewrite /= app_nil_r.
    rewrite skipn_all_app_eq.
    len.  lia.
    rewrite !map_map_compose.
    assert (#|cdecl.(cstr_args)| <= #|isubst|).
    apply context_subst_length in argsub.
    autorewrite with len in argsub.
    now apply firstn_length_le_inv.

    rewrite -(firstn_skipn #|cdecl.(cstr_args)| isubst).
    rewrite -[map _ (to_extended_list_k _ _)]
               (map_map_compose _ _ _ (subst_instance u)
                              (fun x => subst _ _ (subst _ _ x))).
    rewrite subst_instance_to_extended_list_k.
    rewrite -[map _ (to_extended_list_k _ _)]map_map_compose. 
    rewrite -to_extended_list_k_map_subst.
    rewrite subst_instance_length. lia.
    rewrite map_subst_app_to_extended_list_k.
    rewrite firstn_length_le => //.
    
    erewrite subst_to_extended_list_k.
    rewrite map_lift0. split. eauto.
    rewrite firstn_skipn. rewrite firstn_skipn in All2_skipn.
    now rewrite firstn_skipn.

    apply make_context_subst_spec_inv. now rewrite List.rev_involutive.

  - rewrite it_mkProd_or_LetIn_app.
    unfold type_of_constructor in vty.
    rewrite cdecl_eq in vty. move: vty.
    rewrite !subst_instance_it_mkProd_or_LetIn.
    rewrite !subst_it_mkProd_or_LetIn subst_instance_length Nat.add_0_r.
    rewrite subst_instance_mkApps subst_mkApps subst_instance_length.
    rewrite subst_inds_concl_head. all:simpl; auto.
Qed.

Notation "⋆" := ltac:(solve [pcuic]) (only parsing).

(*Lemma build_branches_type_red {cf:checker_flags} (p p' : term) (ind : inductive)
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
  destruct (instantiate_params (subst_instance u (PCUICAst.ind_params mdecl))
  pars
  (subst0 (inds (inductive_mind ind) u (PCUICAst.ind_bodies mdecl))
     (subst_instance u t))).
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
*)
Lemma conv_decls_fix_context_gen {cf:checker_flags} Σ Γ mfix mfix1 :
  wf Σ.1 ->
  All2 (fun d d' => conv Σ Γ d.(dtype) d'.(dtype) * eq_binder_annot d.(dname) d'.(dname)) mfix mfix1 ->
  forall Γ' Γ'',
  conv_context Σ (Γ ,,, Γ') (Γ ,,, Γ'') ->
  All2_fold (fun Δ Δ' : context => conv_decls Σ (Γ ,,, Γ' ,,, Δ) (Γ ,,, Γ'' ,,, Δ'))
    (fix_context_gen #|Γ'| mfix) (fix_context_gen #|Γ''| mfix1).
Proof.    
  intros wfΣ.
  induction 1. constructor. simpl.
  intros Γ' Γ'' convctx.
  destruct r as [r eqann].

  assert(conv_decls Σ (Γ ,,, Γ' ,,, []) (Γ ,,, Γ'' ,,, [])
    (vass (dname x) (lift0 #|Γ'| (dtype x)))
    (vass (dname y) (lift0 #|Γ''| (dtype y)))).
  { constructor; tas.
    pose proof (All2_fold_length convctx).
    rewrite !app_length in H. assert(#|Γ'|  = #|Γ''|) by lia.
    rewrite -H0.
    apply (weakening_conv _ _ []); auto. }

  apply All2_fold_app. len'; cbn.
  now apply All2_length in X.  
  constructor => //. constructor.
  eapply (All2_fold_impl (P:= (fun Δ Δ' : context =>
  conv_decls Σ
  (Γ ,,, (vass (dname x) (lift0 #|Γ'| (dtype x)) :: Γ') ,,, Δ)
  (Γ ,,, (vass (dname y) (lift0 #|Γ''| (dtype y)) :: Γ'') ,,, Δ')))).
  intros. 
  eapply IHX. simpl.
  constructor => //.
  intros. now rewrite !app_context_assoc.
Qed.

Lemma conv_decls_fix_context {cf:checker_flags} Σ Γ mfix mfix1 :
  wf Σ.1 ->
  All2 (fun d d' => conv Σ Γ d.(dtype) d'.(dtype) * eq_binder_annot d.(dname) d'.(dname)) mfix mfix1 ->
  All2_fold (fun Δ Δ' : context => conv_decls Σ (Γ ,,, Δ) (Γ ,,, Δ'))
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

Lemma declared_inductive_unique {Σ mdecl idecl p} (q r : declared_inductive Σ p mdecl idecl) : q = r.
Proof.
  unfold declared_inductive in q, r.
  destruct q, r.
  now rewrite (uip e e0) (uip d d0).
Qed.

Lemma declared_inductive_unique_sig {cf:checker_flags} {Σ ind mib decl mib' decl'}
      (decl1 : declared_inductive Σ ind mib decl)
      (decl2 : declared_inductive Σ ind mib' decl') :
  @sigmaI _ (fun '(m, d) => declared_inductive Σ ind m d)
          (mib, decl) decl1 =
  @sigmaI _ _ (mib', decl') decl2.
Proof.
  pose proof (declared_inductive_inj decl1 decl2) as (<-&<-).
  pose proof (declared_inductive_unique decl1 decl2) as ->.
  reflexivity.
Qed.

Lemma conv_context_rel_context_assumptions {cf:checker_flags} P Γ Δ Δ' :
  conv_context_rel P Γ Δ Δ' ->
  context_assumptions Δ = context_assumptions Δ'.
Proof.
  induction 1; auto.
  cbn.
  depelim p; cbn; lia.
Qed.

Lemma invert_Case_Construct {cf:checker_flags} Σ (hΣ : ∥ wf Σ.1 ∥) 
  {Γ ci ind' pred i u brs args T} :
  Σ ;;; Γ |- tCase ci pred (mkApps (tConstruct ind' i u) args) brs : T ->
  ci.(ci_ind) = ind' /\
  exists br,
    nth_error brs i = Some br /\
    (#|args| = ci.(ci_npar) + context_assumptions br.(bcontext))%nat.
Proof.
  destruct hΣ as [wΣ].
  intros h.
  apply inversion_Case in h as ih ; auto.
  destruct ih
    as [mdecl [idecl [isdecl [indices [cinv cum]]]]].
  destruct cinv.
  pose proof scrut_ty as typec.
  eapply inversion_mkApps in typec as [A' [tyc tyargs]]; auto.
  eapply (inversion_Construct Σ wΣ) in tyc as [mdecl' [idecl' [cdecl' [wfl [declc [Hu tyc]]]]]].
  epose proof (PCUICInductiveInversion.Construct_Ind_ind_eq _ scrut_ty declc); eauto.
  simpl in *.
  intuition auto.
  subst.
  destruct declc as (decli&nthctor).
  cbn in nthctor.
  pose proof (declared_inductive_unique_sig isdecl decli) as H; noconf H.
  eapply All2i_nth_error_l in nthctor as H; eauto.
  destruct H as (br&nth&(?&cc)&?).
  exists br.
  split; auto.
  apply conv_context_rel_app in cc.
  cbn in cc.
  unfold case_branch_type, case_branch_type_gen, case_branch_context_gen in cc.
  cbn in cc.
  apply conv_context_rel_context_assumptions in cc.
  unfold expand_lets_ctx, expand_lets_k_ctx in cc.
  repeat (rewrite ?context_assumptions_subst_context
                  ?context_assumptions_lift_context
                  ?context_assumptions_subst_instance in cc).
  rewrite map2_set_binder_name_context_assumptions in cc; [|lia].
  rewrite forget_types_length.
  apply wf_branch_length.
  eapply Forall2_All2 in wf_brs.
  eapply All2_nth_error_Some_r in nth; eauto.
  destruct nth as (?&?&?).
  congruence.
Qed.

Lemma Proj_Construct_ind_eq {cf:checker_flags} Σ (hΣ : ∥ wf Σ.1 ∥) {Γ i i' pars narg c u l T} :
  Σ ;;; Γ |- tProj (i, pars, narg) (mkApps (tConstruct i' c u) l) : T ->
  i = i'.
Proof.
  destruct hΣ as [wΣ].
  intros h.
  apply inversion_Proj in h ; auto.
  destruct h as [uni [mdecl [idecl [pdecl [args' [? [hc [? ?]]]]]]]].
  pose proof hc as typec.
  eapply inversion_mkApps in typec as [A' [tyc tyargs]]; auto.
  eapply (inversion_Construct Σ wΣ) in tyc as [mdecl' [idecl' [cdecl' [wfl [declc [Hu tyc]]]]]].
  epose proof (PCUICInductiveInversion.Construct_Ind_ind_eq _ hc declc); eauto.
  intuition auto.
Qed.

Lemma invert_Proj_Construct {cf:checker_flags} Σ (hΣ : ∥ wf Σ.1 ∥) {Γ i i' pars narg c u l T} :
  Σ ;;; Γ |- tProj (i, pars, narg) (mkApps (tConstruct i' c u) l) : T ->
  i = i' /\ c = 0 /\ pars + narg < #|l|.
Proof.
  intros h.
  assert (h' := h).
  apply Proj_Construct_ind_eq in h' as <-; auto.
  destruct hΣ as [wΣ].
  split; [reflexivity|].
  apply inversion_Proj in h ; auto.
  destruct h as [uni [mdecl [idecl [pdecl [args' [? [hc [? ?]]]]]]]].
  clear c0.
  pose proof hc as typec.
  eapply inversion_mkApps in typec as [A' [tyc tyargs]]; auto.
  eapply (inversion_Construct Σ wΣ) in tyc as [mdecl' [idecl' [cdecl' [wfl [declc [Hu tyc]]]]]].
  pose proof (declared_inductive_unique_sig d.p1 declc.p1) as H; noconf H.
  clear H.
  epose proof (PCUICInductiveInversion.Construct_Ind_ind_eq _ hc declc); eauto.
  simpl in X.
  destruct (on_declared_projection d).
  set (oib := declared_inductive_inv _ _ _ _) in *.
  simpl in *.
  destruct declc.
  destruct (ind_ctors idecl) as [|? []] eqn:hctor in y; try contradiction.
  simpl in H.
  rewrite hctor /= in H0.
  destruct y as [[[? ?] ?] ?].
  destruct (ind_cunivs oib) as [|? []] eqn:Heq; try contradiction.
  destruct c; simpl in H0 => //. noconf H0.
  intuition auto.
  2:{ rewrite nth_error_nil in H0. noconf H0. }
  rewrite b0.
  destruct d as [decli [nthp parseq]].
  simpl in *. rewrite parseq. lia.
Qed.

Ltac unf_env := 
  change PCUICEnvironment.it_mkProd_or_LetIn with it_mkProd_or_LetIn in *; 
  change PCUICEnvironment.to_extended_list_k with to_extended_list_k in *; 
  change PCUICEnvironment.ind_params with ind_params in *.

Derive Signature for positive_cstr.

Lemma positive_cstr_it_mkProd_or_LetIn mdecl i Γ Δ t : 
  positive_cstr mdecl i Γ (it_mkProd_or_LetIn Δ t) ->
  All_local_env (fun Δ ty _ => positive_cstr_arg mdecl  (Γ ,,, Δ) ty)
    (smash_context [] Δ) *
  positive_cstr mdecl i (Γ ,,, smash_context [] Δ) (expand_lets Δ t).
Proof.
  revert Γ t; unfold expand_lets, expand_lets_k;
   induction Δ as [|[na [b|] ty] Δ] using ctx_length_rev_ind; intros Γ t.
  - simpl; intuition auto. now rewrite subst_empty lift0_id.
  - rewrite it_mkProd_or_LetIn_app /=; intros H; depelim H.
    solve_discr. rewrite smash_context_app_def.
    rewrite /subst1 subst_it_mkProd_or_LetIn in H.
    specialize (X (subst_context [b] 0 Δ) ltac:(len; lia) _ _ H).
    simpl; autorewrite with len in X |- *.
    destruct X; split; auto. simpl.
    rewrite extended_subst_app /= !subst_empty !lift0_id lift0_context.
    rewrite subst_app_simpl; len => /=.
    simpl.
    epose proof (distr_lift_subst_rec _ [b] (context_assumptions Δ) #|Δ| 0).
    rewrite !Nat.add_0_r in H0. now erewrite <- H0.
  - rewrite it_mkProd_or_LetIn_app /=; intros H; depelim H.
    solve_discr. rewrite smash_context_app_ass.
    specialize (X Δ ltac:(len; lia) _ _ H).
    simpl; autorewrite with len in X |- *.
    destruct X; split; auto. simpl.
    eapply All_local_env_app; split.
    constructor; auto.
    eapply (All_local_env_impl _ _ _ a). intros; auto.
    now rewrite app_context_assoc. simpl.
    rewrite extended_subst_app /=.
    rewrite subst_app_simpl; len => /=.
    simpl.
    rewrite subst_context_lift_id.
    rewrite Nat.add_comm Nat.add_1_r subst_reli_lift_id. 
    apply context_assumptions_length_bound. now rewrite app_context_assoc.
Qed.

Lemma positive_cstr_closed_indices {cf:checker_flags} {Σ : global_env_ext} (wfΣ : wf Σ.1):
  forall {i mdecl idecl cdecl},
  declared_constructor Σ.1 i mdecl idecl cdecl ->
  All (closedn (context_assumptions (ind_params mdecl ,,, cstr_args cdecl)))
    (map (expand_lets (cstr_args cdecl ++ ind_params mdecl)) (cstr_indices cdecl)).
Proof.
  intros.
  pose proof (on_declared_constructor H) as [[onmind oib] [cs [hnth onc]]].
  pose proof (onc.(on_ctype_positive)).
  rewrite onc.(cstr_eq) in X. unf_env.
  rewrite -it_mkProd_or_LetIn_app in X.
  eapply positive_cstr_it_mkProd_or_LetIn in X as [hpars hpos].
  rewrite app_context_nil_l in hpos.
  rewrite expand_lets_mkApps in hpos.
  unfold cstr_concl_head in hpos.
  have subsrel := expand_lets_tRel (#|ind_bodies mdecl| - S (inductive_ind i.1)) (cstr_args cdecl  ++ ind_params mdecl).
  rewrite app_length (Nat.add_comm #|(cstr_args cdecl)|) Nat.add_assoc in subsrel. 
  rewrite {}subsrel in hpos.
  rewrite context_assumptions_app in hpos. depelim hpos; solve_discr.
  noconf H1. noconf H2.
  eapply All_map_inv in a.
  eapply All_app in a as [ _ a].
  eapply All_map; eapply (All_impl a); clear; intros x H; len in H; simpl in H.
  now rewrite context_assumptions_app.
Qed.


Lemma positive_cstr_arg_subst_instance {mdecl Γ} {t} u :
  positive_cstr_arg mdecl Γ t ->
  positive_cstr_arg mdecl (subst_instance u Γ) (subst_instance u t).
Proof.
  induction 1.
  - constructor 1; len.
    now rewrite closedn_subst_instance.
  - rewrite subst_instance_mkApps. econstructor 2; len => //; eauto.
    eapply All_map; solve_all.
    now rewrite closedn_subst_instance.
  - simpl. constructor 3; len => //.
    now rewrite subst_instance_subst in IHX.
  - simpl. constructor 4; len => //.
    now rewrite closedn_subst_instance.
Qed.


Lemma declared_inductive_lookup_inductive {Σ ind mdecl idecl} :
  declared_inductive Σ ind mdecl idecl ->
  lookup_inductive Σ ind = Some (mdecl, idecl).
Proof.
  rewrite /declared_inductive /lookup_inductive.
  intros []. red in H. now rewrite /lookup_minductive H H0.
Qed.

Lemma declared_inductive_type {cf} {Σ} {wfΣ : wf Σ} {ind mdecl idecl} :
  declared_inductive Σ ind mdecl idecl ->
  ind_type idecl = it_mkProd_or_LetIn (ind_params mdecl ,,, ind_indices idecl) (tSort (ind_sort idecl)).
Proof.
  move/on_declared_inductive => [onmind oib].
  rewrite oib.(ind_arity_eq). 
  now rewrite -it_mkProd_or_LetIn_app.
Qed.

Notation red_terms Σ Γ := (All2 (red Σ Γ)).

Lemma red_terms_conv_terms {cf:checker_flags} {Σ : global_env_ext} Γ u u' : 
  All2 (red Σ Γ) u u' -> All2 (conv Σ Γ) u u'.
Proof.
  move=> Hu; eapply All2_impl; eauto.
Qed.

Lemma eq_terms_conv_terms {cf:checker_flags} {Σ : global_env_ext} Γ u u' : 
  All2 (eq_term Σ Σ) u u' -> All2 (conv Σ Γ) u u'.
Proof.
  move=> Hu; eapply All2_impl; eauto.
  intros. now constructor.
Qed.

Instance conv_terms_sym {cf:checker_flags} {Σ : global_env_ext} Γ : CRelationClasses.Symmetric (conv_terms Σ Γ).
Proof.
  move=> u u' Hu; eapply All2_symmetry; eauto. typeclasses eauto.
Qed.

Instance conv_terms_trans {cf:checker_flags} {Σ : global_env_ext} {Γ} {wfΣ : wf Σ}: 
  CRelationClasses.Transitive (conv_terms Σ Γ).
Proof.
  move=> x y z Hu; eapply All2_transitivity; eauto.
  eapply conv_trans. typeclasses eauto.
Qed.

Lemma cumul_mkApps_tRel {cf:checker_flags} {Σ : global_env_ext} Γ n d u u' : 
  wf Σ -> nth_error Γ n = Some d -> decl_body d = None ->
  Σ ;;; Γ |- mkApps (tRel n) u <= mkApps (tRel n) u' -> 
  All2 (conv Σ Γ) u u'.
Proof.
  intros wfΣ Hnth Hd cum.
  eapply cumul_alt in cum as [v' [v [[redl redr] leq]]].
  eapply red_mkApps_tRel in redl as [args' [-> conv]]; eauto.
  eapply red_mkApps_tRel in redr as [args'' [-> conv']]; eauto.
  eapply All2_trans. apply _.
  now eapply red_terms_conv_terms.
  eapply eq_term_upto_univ_mkApps_l_inv in leq as [u'' [l' [[eqrel eqargs] eq']]].
  depelim eqrel. eapply mkApps_eq_inj in eq' as [_ ->] => //.
  etransitivity; [|symmetry; eapply red_terms_conv_terms]; eauto.
  now eapply eq_terms_conv_terms.
Qed.

Lemma nth_error_subst_instance u Γ n : 
  nth_error (subst_instance u Γ) n = 
  option_map (map_decl (subst_instance u)) (nth_error Γ n).
Proof.
  now rewrite nth_error_map.
Qed.

Lemma conv_terms_confl {cf:checker_flags} {Σ : global_env_ext} Γ u u' : 
  wf Σ -> conv_terms Σ Γ u u' ->
  ∑ nf nf', (red_terms Σ Γ u nf * red_terms Σ Γ u' nf') * (All2 (eq_term Σ Σ) nf nf').
Proof.
  intros wfΣ cv.
  induction cv.
  - exists [], []; intuition auto.
  - destruct IHcv as [nf [nf' [[redl redr] eq]]].
    eapply conv_alt_red in r as [x' [y' [[redx redy] eq']]].
    exists (x' :: nf), (y' :: nf'); intuition auto.
Qed.

Lemma cumul_mkApps_cum {cf:checker_flags} {Σ : global_env_ext} Γ f f' u u' : 
  wf Σ -> 
  eq_term_upto_univ_napp Σ (eq_universe Σ) (leq_universe Σ) #|u| f f' ->
  conv_terms Σ Γ u u' ->
  Σ ;;; Γ |- mkApps f u <= mkApps f' u'.
Proof.
  intros wfΣ eqf equ.
  eapply cumul_alt.
  eapply conv_terms_confl in equ as [nf [nf' [[redl redr] eq]]] => //.
  exists (mkApps f nf), (mkApps f' nf').
  intuition idtac.
  eapply red_mkApps; eauto.
  eapply red_mkApps; eauto.
  eapply eq_term_upto_univ_napp_mkApps.
  now rewrite Nat.add_0_r -(All2_length redl).
  apply eq.
Qed.

Lemma cumul_LetIn_inv {cf:checker_flags} {Σ : global_env_ext} {Γ na na' b b' ty ty' t t'} :
  wf Σ -> 
  Σ ;;; Γ |- tLetIn na b ty t <= tLetIn na' b' ty' t' ->
  Σ ;;; Γ |- t {0 := b} <= t' {0 := b'}.
Proof.
  intros wfΣ cum.
  eapply invert_cumul_letin_l; eauto.
  eapply invert_cumul_letin_r; eauto.
Qed.

Lemma cumul_LetIn_subst {cf:checker_flags} {Σ : global_env_ext} {Γ na na' b b' ty ty' t t'} :
  wf Σ -> 
  Σ ;;; Γ |- t {0 := b} <= t' {0 := b'} ->
  Σ ;;; Γ |- tLetIn na b ty t <= tLetIn na' b' ty' t'.
Proof.
  intros wfΣ cum.
  transitivity (t {0 := b}).
  eapply red_cumul. eapply red1_red. econstructor.
  transitivity (t' {0 := b'}) => //.
  eapply conv_cumul, conv_sym, red_conv.
  eapply red1_red; constructor. 
Qed.

Lemma cumul_Prod_inv_l {cf:checker_flags} Σ Γ na na' A B A' B' :
  wf Σ.1 -> wf_local Σ Γ ->
  Σ ;;; Γ |- tProd na A B <= tProd na' A' B' ->
   (eq_binder_annot na na' * (Σ ;;; Γ |- A = A') * (Σ ;;; Γ ,, vass na A |- B <= B'))%type.
Proof.
  intros wfΣ wfΓ H; depind H.
  - depelim l.
    split; [split|]; auto.
    all: now constructor.

  - depelim r.
    + solve_discr.
    + specialize (IHcumul _ _ _ _ _ _ wfΣ wfΓ eq_refl).
      intuition auto.
      econstructor 2; eauto.
      eapply cumul_conv_ctx; eauto. constructor; pcuic.
      constructor. reflexivity. symmetry. now eapply red_conv, red1_red.
    + specialize (IHcumul _ _ _ _ _ _ wfΣ wfΓ eq_refl).
      intuition auto. apply cumul_trans with N2.
      * auto.
      * eapply cumul_conv_ctx; eauto.
        -- econstructor 2. 1: eauto.
           constructor. reflexivity.
        -- constructor. 1: now apply conv_ctx_refl.
           constructor; auto. reflexivity.
      * auto.

  - depelim r.
    + solve_discr.
    + specialize (IHcumul _ _ _ _ _ _ wfΣ wfΓ eq_refl).
      intuition auto.
      * econstructor 3. 2:eauto. auto.
    + specialize (IHcumul _ _ _ _ _ _ wfΣ wfΓ eq_refl).
      intuition auto. apply cumul_trans with N2. 1-2: auto.
      eapply cumul_conv_ctx; eauto.
      eapply cumul_red_r; eauto. reflexivity.
      constructor; pcuic.
      constructor; now symmetry.
Qed.

Lemma positive_cstr_arg_subst {cf:checker_flags} {Σ : global_env_ext} {ind mdecl idecl Γ t u u'} :
  wf Σ -> 
  declared_inductive Σ ind mdecl idecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  R_opt_variance (eq_universe Σ) (leq_universe Σ) (ind_variance mdecl) u u' ->
  wf_local Σ (subst_instance u (ind_arities mdecl) ,,, subst_instance u Γ) ->
  closedn_ctx #|ind_arities mdecl| Γ ->
  Σ ;;; subst_instance u (ind_arities mdecl) ,,, subst_instance u Γ |- (subst_instance u t) <= (subst_instance u' t) ->
  isType Σ (subst_instance u (ind_arities mdecl) ,,, subst_instance u Γ) (subst_instance u t) ->
  positive_cstr_arg mdecl Γ t ->
  (Σ ;;; subst_context (ind_subst mdecl ind u) 0 (subst_instance u Γ) |- (subst (ind_subst mdecl ind u) #|Γ| (subst_instance u t)) <=
    subst (ind_subst mdecl ind u') #|Γ| (subst_instance u' t)).
Proof.
  intros wfΣ decli cu ru cl wf cum isty pos.
  pose proof (proj1 decli) as declm.
  induction pos.
  - rewrite -(app_context_nil_l (_ ,,, _)) app_context_assoc in cum.
    rewrite -(app_context_nil_l (_ ,,, _)) app_context_assoc in isty.
    eapply substitution_cumul in cum; eauto.
    2:rewrite app_context_nil_l //.
    2:{ eapply subslet_inds; eauto. }
    eapply isType_subst_gen in isty; eauto.
    2:{ eapply subslet_inds; eauto. }
    rewrite !subst_closedn ?closedn_subst_instance //.
    rewrite !subst_closedn ?closedn_subst_instance // in cum; len; auto.
    now rewrite app_context_nil_l in cum.

  - rewrite !subst_instance_mkApps !subst_mkApps in cum |- *.
    simpl in cum. eapply cumul_mkApps_tRel in cum; eauto; cycle 1.
    { rewrite nth_error_app_ge // subst_instance_length //
         nth_error_subst_instance.
      unfold ind_arities, arities_context.
      rewrite rev_map_spec -map_rev.
      rewrite nth_error_map e /=. reflexivity. }
    1:trivial.
    eapply cumul_mkApps_cum => //; len.
    * simpl. destruct (Nat.leb #|ctx| k) eqn:eqle.
      eapply Nat.leb_le in eqle.
      rewrite /ind_subst !inds_spec !rev_mapi !nth_error_mapi.
      rewrite e /=. simpl. constructor. simpl.
      unfold R_global_instance. simpl.
      assert(declared_inductive Σ {|
      inductive_mind := inductive_mind ind;
      inductive_ind := Nat.pred #|ind_bodies mdecl| - (k - #|ctx|) |} mdecl i).
      { split; auto. simpl. rewrite -e nth_error_rev; lia_f_equal. }
      rewrite (declared_inductive_lookup_inductive H) //.
      destruct (on_declared_inductive H) as [onmind onind] => //. simpl in *.
      rewrite e0 /ind_realargs /PCUICTypingDef.destArity.
      rewrite !onind.(ind_arity_eq).
      rewrite !destArity_it_mkProd_or_LetIn /=; len; simpl.
      rewrite (Nat.leb_refl) //. eapply Nat.leb_nle in eqle. lia.
    * rewrite -(app_context_nil_l (_ ,,, _)) app_context_assoc in cum.
      eapply conv_terms_subst in cum.
      4:{ eapply (subslet_inds _ _ u); eauto. }
      4:{ eapply (subslet_inds _ _ u); eauto. }
      all:eauto.
      3:{ eapply All2_refl. intros x; eapply conv_refl'. }
      rewrite app_context_nil_l // in cum. autorewrite with len in cum.
      rewrite /ind_subst.
      { do 2 eapply All2_map. do 2 eapply All2_map_inv in cum.
        eapply All2_All in cum. apply All_All2_refl.
        solve_all. autorewrite with len in b.
        now rewrite !subst_closedn ?closedn_subst_instance // in b |- *. }
      now rewrite app_context_nil_l.
    
  - simpl in cum |- *.
    eapply cumul_LetIn_subst; eauto.
    rewrite !subst_instance_subst /= in IHpos.
    rewrite !distr_subst /= in IHpos. rewrite /subst1.
    eapply IHpos => //.
    eapply cumul_LetIn_inv in cum; eauto.
    eapply isType_tLetIn_red in isty; eauto.

  - simpl in cum |- *.
    eapply cumul_Prod_inv_l in cum as [dom codom]; eauto.
    eapply congr_cumul_prod; eauto.
    * rewrite -(app_context_nil_l (_ ,,, _)) app_context_assoc in dom.
      destruct dom as [_ dom].
      eapply substitution_conv in dom; rewrite ?app_context_nil_l; eauto.
      2:{ eapply subslet_inds; eauto. }
      rewrite ?app_context_nil_l ?closedn_subst_instance // in dom.
      rewrite !subst_closedn ?closedn_subst_instance // in dom; len; auto.
      now rewrite !subst_closedn ?closedn_subst_instance.
    * cbn -[closedn_ctx] in IHpos. rewrite subst_context_snoc in IHpos.
      rewrite map_length Nat.add_0_r in IHpos. eapply IHpos; eauto.
      simpl; constructor; auto.
      simpl in isty. eapply isType_tProd in isty as [Hty Ht]; eauto.
      rewrite closedn_ctx_cons /=. apply/andb_and; split; auto. simpl.
      eapply closed_upwards; eauto; lia.
      simpl in isty. eapply isType_tProd in isty as [Hty Ht]; eauto.
Qed.

Definition wt_cumul_ctx_rel {cf:checker_flags} Σ Γ Δ Δ' :=
  (cumul_ctx_rel Σ Γ Δ Δ' * wf_local Σ (Γ ,,, Δ))%type.

Lemma wt_cumul_ctx_rel_cons {cf:checker_flags} Σ Γ Δ Δ' na ty na' ty' :
  wt_cumul_ctx_rel Σ Γ Δ Δ' -> 
  Σ ;;; (Γ ,,, Δ) |- ty <= ty' -> 
  eq_binder_annot na na' ->
  wf_local Σ (Γ ,,, Δ ,, vass na ty) ->
  wt_cumul_ctx_rel Σ Γ (vass na ty :: Δ) (vass na' ty' :: Δ').
Proof.
  intros []; split; simpl; try constructor; auto.
  all:now depelim X0; auto; constructor.
Qed.

Lemma positive_cstr_closed_args_subst_arities {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ.1} {u u' Γ}
   {i ind mdecl idecl cdecl ind_indices cs} :
  declared_inductive Σ ind mdecl idecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  on_constructor (lift_typing typing) (Σ.1, ind_universes mdecl) mdecl i idecl ind_indices cdecl cs -> 
  R_opt_variance (eq_universe Σ) (leq_universe Σ) (ind_variance mdecl) u u' ->
  closed_ctx (subst_instance u (ind_params mdecl)) ->
  wf_local Σ (subst_instance u (ind_arities mdecl ,,, smash_context [] (ind_params mdecl) ,,, Γ)) ->
  All_local_env
    (fun (Γ : PCUICEnvironment.context) (t : term) (_ : option term) =>
           positive_cstr_arg mdecl ([] ,,, (smash_context [] (ind_params mdecl) ,,, Γ)) t)
      Γ ->
  assumption_context Γ ->
  cumul_ctx_rel Σ (subst_instance u (ind_arities mdecl) ,,,
      subst_instance u
        (smash_context [] (PCUICEnvironment.ind_params mdecl)))
   (subst_instance u Γ) (subst_instance u' Γ) -> 
  
  wt_cumul_ctx_rel Σ (subst_instance u (smash_context [] (PCUICEnvironment.ind_params mdecl)))
    (subst_context (ind_subst mdecl ind u) (context_assumptions (ind_params mdecl)) (subst_instance u Γ))
    (subst_context (ind_subst mdecl ind u') (context_assumptions (ind_params mdecl)) (subst_instance u' Γ)).
Proof.
  intros * decli cu onc onv cl wf cpos ass.
  intros cum.
  split.
  2:{ rewrite !subst_instance_app_ctx in wf.
      rewrite -app_context_assoc -(app_context_nil_l (_ ,,, _)) app_context_assoc in wf.
      eapply substitution_wf_local in wf; eauto.
      2:{ eapply subslet_inds; eauto. }
      rewrite app_context_nil_l in wf.
      rewrite subst_context_app in wf.
      rewrite closed_ctx_subst in wf.
      rewrite closedn_subst_instance_context closedn_smash_context //.
      now rewrite closedn_subst_instance_context in cl.
      now len in wf. } 
  revert cum.
  induction cpos; simpl; rewrite ?subst_context_nil ?subst_context_snoc; try solve [constructor; auto].
  all:rewrite ?map_length; intros cv; depelim cv; depelim wf.
  assert (isType Σ
  (subst_instance u (ind_arities mdecl) ,,,
   subst_instance u (smash_context [] (ind_params mdecl) ,,, Γ))
  (subst_instance u t)).
  { rewrite subst_instance_app_ctx app_context_assoc. simpl in l.
    now rewrite ![map _ _]subst_instance_app_ctx subst_instance_app_ctx in l. }
  depelim c.
  all:constructor.
  - eapply IHcpos. auto. now depelim ass. eapply cv.
  - constructor; auto.
    rewrite app_context_nil_l in t0.
    eapply positive_cstr_arg_subst in t0; eauto.
    move: t0; rewrite ?app_context_length ?smash_context_length; simpl.
    * rewrite subst_instance_smash /=.
      rewrite subst_instance_app_ctx subst_instance_smash subst_context_app.
      rewrite closed_ctx_subst ?closedn_subst_instance // ?closedn_smash_context; eauto.
      now len; simpl.
    * rewrite ![map _ _]subst_instance_app_ctx subst_instance_app_ctx in wf.
      now rewrite subst_instance_app_ctx app_context_assoc.
    * eapply closed_wf_local in wf; eauto.
      rewrite closedn_subst_instance_context app_assoc in wf.
      now rewrite closedn_ctx_app /= in wf; move/andb_and: wf => [wfars wf].
    * now rewrite subst_instance_app_ctx app_context_assoc.
  - elimtype False; now depelim ass.
  - elimtype False; now depelim ass.
Qed.

Lemma positive_cstr_closed_args {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ.1} {u u'} 
  {ind mdecl idecl cdecl} :
  declared_constructor Σ ind mdecl idecl cdecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  R_opt_variance (eq_universe Σ) (leq_universe Σ) (ind_variance mdecl) u u' ->
 cumul_ctx_rel Σ (subst_instance u (ind_arities mdecl) ,,,
    subst_instance u
      (smash_context [] (PCUICEnvironment.ind_params mdecl)))
 (smash_context []
    (subst_instance u
       (expand_lets_ctx (PCUICEnvironment.ind_params mdecl)
          (cstr_args cdecl))))
 (smash_context []
    (subst_instance u'
       (expand_lets_ctx (PCUICEnvironment.ind_params mdecl)
          (cstr_args cdecl)))) ->
  
  wt_cumul_ctx_rel Σ (subst_instance u (smash_context [] (PCUICEnvironment.ind_params mdecl)))
      (subst_context (inds (inductive_mind ind.1) u (ind_bodies mdecl)) (context_assumptions (ind_params mdecl))
       (smash_context []
          (subst_instance u
             (expand_lets_ctx (PCUICEnvironment.ind_params mdecl)
                (cstr_args cdecl)))))
       (subst_context (inds (inductive_mind ind.1) u' (ind_bodies mdecl)) (context_assumptions (ind_params mdecl))
           ((smash_context []
          (subst_instance u'
             (expand_lets_ctx (PCUICEnvironment.ind_params mdecl)
                (cstr_args cdecl)))))).
Proof.
  intros * declc cu Ru cx.
  pose proof (on_declared_constructor declc) as [[onmind oib] [cs [? onc]]].
  pose proof (onc.(on_ctype_positive)) as cpos.
  rewrite onc.(cstr_eq) in cpos. unf_env.
  rewrite -it_mkProd_or_LetIn_app in cpos.
  eapply positive_cstr_it_mkProd_or_LetIn in cpos as [hpars _].
  rewrite smash_context_app_expand in hpars.
  eapply All_local_env_app_inv in hpars as [_hpars hargs].
  rewrite expand_lets_smash_context /= expand_lets_k_ctx_nil /= in hargs.
  eapply positive_cstr_closed_args_subst_arities in hargs; eauto.
  split.
  - rewrite !subst_instance_smash /ind_subst /= in hargs |- *.
    eapply hargs; eauto.
  - destruct hargs as [hargs hwf]. now rewrite !subst_instance_smash in hwf |- *.
  - eapply declc.
  - eapply closed_wf_local; eauto; eapply on_minductive_wf_params; eauto; eapply declc.
  - rewrite -app_context_assoc. rewrite -(expand_lets_smash_context _ []).
    rewrite -smash_context_app_expand subst_instance_app_ctx subst_instance_smash.
    eapply wf_local_smash_end; eauto.
    rewrite -subst_instance_app_ctx app_context_assoc.
    now epose proof (on_constructor_inst declc _ cu) as [wfarpars _].
  - eapply smash_context_assumption_context. constructor.
  - now rewrite !(subst_instance_smash _ (expand_lets_ctx _ _)).
Qed.

Lemma red_subst_instance {cf:checker_flags} (Σ : global_env) (Γ : context) (u : Instance.t) (s t : term) :
  red Σ Γ s t ->
  red Σ (subst_instance u Γ) (subst_instance u s)
            (subst_instance u t).
Proof.
  intros H; apply clos_rt_rt1n in H.
  apply clos_rt1n_rt.
  induction H. constructor.
  eapply red1_subst_instance in r.
  econstructor 2. eapply r. auto.
Qed.

From MetaCoq.PCUIC Require Import PCUICParallelReductionConfluence.
(* for nth_error lemma. should move *)

Lemma nth_error_decl_body_ass_ctx {Γ Δ i body} : 
  assumption_context Γ ->
  option_map decl_body (nth_error (Γ ,,, Δ) i) = Some (Some body) ->
  i < #|Δ|.
Proof.
  intros ass.
  destruct nth_error eqn:eq.
  simpl.
  destruct (i <? #|Δ|) eqn:lt.
  eapply Nat.ltb_lt in lt => //.
  eapply Nat.ltb_nlt in lt => //.
  rewrite nth_error_app_ge in eq. lia.
  eapply nth_error_assumption_context in eq; eauto. rewrite eq //.
  by [].
Qed.
  
Lemma red1_assumption_context_irrelevant Σ Γ Δ Γ' t t' : 
  red1 Σ (Γ ,,, Δ) t t' ->
  assumption_context Γ ->
  #|Γ| = #|Γ'| ->
  red1 Σ (Γ' ,,, Δ) t t'. 
Proof.
  (* subsummed by red_type_irrelevance *)
  (*remember (Γ ,,, Δ) as ctx.
  intros H; revert Γ Δ Heqctx Γ'. 
  induction H using red1_ind_all; intros; subst; try solve [econstructor; eauto; try solve_all].
  
  - pose proof (nth_error_decl_body_ass_ctx H0 H).
    rewrite nth_error_app_lt // in H |- *.
    constructor. rewrite nth_error_app_lt //.
  - econstructor; eauto; eapply (IHred1 Γ0 (Δ ,, vass na N) ltac:(reflexivity)) => //.
  - econstructor; eauto; eapply (IHred1 Γ0 (Δ ,, vdef na b t) ltac:(reflexivity)) => //.
  - econstructor; eauto; eapply (IHred1 Γ0 (Δ ,, vass na M1) ltac:(reflexivity)) => //.
  - eapply fix_red_body. solve_all.
    specialize (b0 Γ0 (Δ ,,, fix_context mfix0) ltac:(rewrite app_context_assoc; reflexivity) _ H H0).
    now rewrite app_context_assoc in b0.
  - eapply cofix_red_body. solve_all.
    specialize (b0 Γ0 (Δ ,,, fix_context mfix0) ltac:(rewrite app_context_assoc; reflexivity) _ H H0).
    now rewrite app_context_assoc in b0.*)
Admitted.

Lemma red_assumption_context_app_irrelevant Σ Γ Δ Γ' t t' : 
  red Σ (Γ ,,, Δ) t t' ->
  assumption_context Γ ->
  #|Γ| = #|Γ'| ->
  red Σ (Γ' ,,, Δ) t t'. 
Proof.
  intros r ass eqc.
  eapply clos_rt_rt1n in r.
  eapply clos_rt1n_rt.
  induction r; [constructor|econstructor 2].
  eapply red1_assumption_context_irrelevant; eauto. apply IHr.
Qed.

Lemma red_assumption_context_irrelevant Σ Γ Γ' t t' : 
  red Σ Γ t t' ->
  assumption_context Γ ->
  #|Γ| = #|Γ'| ->
  red Σ Γ' t t'. 
Proof.
  intros r ass eqc.
  now eapply (red_assumption_context_app_irrelevant _ _ [] Γ').
Qed.

Lemma assumption_context_map f Γ :
  assumption_context Γ -> assumption_context (map_context f Γ).
Proof.
  induction 1; constructor; auto.
Qed.

Lemma assumption_context_subst_instance u Γ :
  assumption_context Γ -> assumption_context (subst_instance u Γ).
Proof. apply assumption_context_map. Qed.

Lemma eq_term_upto_univ_napp_impl {cf:checker_flags} (Σ : global_env) 
  (Re Re' Rle Rle' : Relation_Definitions.relation Universe.t) u u' t t' : 
  (forall x y : Universe.t, Re x y -> Re' (subst_instance_univ u x) (subst_instance_univ u' y)) ->
  (forall x y : Universe.t, Rle x y -> Rle' (subst_instance_univ u x) (subst_instance_univ u' y)) ->
  (forall x y : Instance.t, R_universe_instance Re x y -> R_universe_instance Re' (subst_instance u x) 
    (subst_instance u' y)) ->
  (forall r n (x y : Instance.t), R_global_instance Σ Re Rle r n x y -> 
    R_global_instance Σ Re' Rle' r n (subst_instance u x) (subst_instance u' y)) ->
  (forall r n (x y : Instance.t), R_global_instance Σ Re Re r n x y -> 
    R_global_instance Σ Re' Re' r n (subst_instance u x) (subst_instance u' y)) ->
  forall n, eq_term_upto_univ_napp Σ Re Rle n t t' ->
  eq_term_upto_univ_napp Σ Re' Rle' n (subst_instance u t) (subst_instance u' t').
Proof.
  intros Heq Hle Hi Hgil Hgie.
  induction t in t', Re, Re', Rle, Rle', Heq, Hle, Hi, Hgil, Hgie |- * using 
    PCUICInduction.term_forall_list_ind; simpl; intros n' H; depelim H. 
  all:simpl; try solve [constructor; eauto; try solve_all].
  todo "case".
Qed.

Section Betweenu.
  Context (start : nat) (k : nat).

  Definition betweenu_level (l : Level.t) :=
    match l with
    | Level.Var n => (start <=? n) && (n <? start + k)%nat
    | _ => true
    end.

  Definition betweenu_level_expr (s : UnivExpr.t) :=
    betweenu_level (UnivExpr.get_level s).

  Definition betweenu_universe0 (u : Universe.t0) :=
    UnivExprSet.for_all betweenu_level_expr u.
  
  Definition betweenu_universe (u : Universe.t) :=
    match u with 
    | Universe.lProp | Universe.lSProp => true 
    | Universe.lType l => betweenu_universe0 l
    end.

  Definition betweenu_instance (u : Instance.t) :=
    forallb betweenu_level u.

End Betweenu.

(** Universe-closed terms are unaffected by universe substitution. *)
Section UniverseClosedSubst.
  Lemma closedu_subst_instance_level_app u u' l
  : closedu_level #|u'| l -> subst_instance_level (u' ++ u) l = subst_instance_level u' l.
  Proof.
    destruct l; cbnr.
    intros Hn % Nat.ltb_lt.
    rewrite app_nth1 //.
  Qed.

  Lemma closedu_subst_instance_level_lift u u' l
  : closedu_level #|u| l -> subst_instance_level (u' ++ u) (lift_level #|u'| l) = subst_instance_level u l.
  Proof.
    destruct l; cbnr.
    intros Hn % Nat.ltb_lt.
    rewrite app_nth2; try lia.
    lia_f_equal.
  Qed.
  
  Definition lift_npl (k : nat) (e : Level.t) : Level.t :=
    match e with
    | Level.lSet => Level.lSet
    | Level.Level s => Level.Level s
    | Level.Var n => Level.Var (k + n)
    end.

  (* Definition lift_expr (n : nat) (e : UnivExpr.t) : UnivExpr.t. *)

  Lemma closedu_subst_instance_level_expr_app u u' e
    : closedu_level_expr #|u'| e -> subst_instance_level_expr (u' ++ u) e = subst_instance_level_expr u' e.
  Proof.
    destruct e as [[] b]; cbnr.
    intros Hn % Nat.ltb_lt.
    rewrite nth_error_app_lt //.
  Qed.


  (* Lemma closedu_subst_instance_level_expr_lilft u u' e
    : closedu_level_expr #|u| e -> subst_instance_level_expr (u' ++ u) (lift_expr e = subst_instance_level_expr u' e.
  Proof.
    destruct e as [|[[] b]]; cbnr.
    intros Hn % Nat.ltb_lt.
    rewrite nth_error_app_lt //.
  Qed. *)
  
  Lemma closedu_subst_instance_app u u' t
    : closedu_instance #|u'| t -> subst_instance (u' ++ u) t = subst_instance u' t.
  Proof.
    intro H. eapply forallb_All in H. apply All_map_eq.
    solve_all. now eapply closedu_subst_instance_level_app.
  Qed.
  
  Lemma closedu_subst_instance_lift u u' t
    : closedu_instance #|u| t -> subst_instance (u' ++ u) (lift_instance #|u'| t) = subst_instance u t.
  Proof.
    intro H. eapply forallb_All in H.
    rewrite /subst_instance /subst_instance_instance /lift_instance map_map_compose. apply All_map_eq.
    solve_all. now eapply closedu_subst_instance_level_lift.
  Qed.
  
End UniverseClosedSubst.

Lemma level_var_instance_length n i : #|level_var_instance n i| = #|i|.
Proof. now rewrite /level_var_instance; len. Qed.
Hint Rewrite level_var_instance_length : len.

Lemma lift_instance_length n i : #|lift_instance n i| = #|i|.
Proof. now rewrite /lift_instance; len. Qed.
Hint Rewrite lift_instance_length : len.

Lemma variance_universes_insts {mdecl l v i i'} :
  on_variance (ind_universes mdecl) (Some l) ->
  variance_universes (PCUICEnvironment.ind_universes mdecl) l = Some (v, i, i') ->
  (constraints_of_udecl v = match ind_universes mdecl with
  | Monomorphic_ctx (_, cstrs) => cstrs
  | Polymorphic_ctx (inst, cstrs) => 
    ConstraintSet.union (ConstraintSet.union cstrs (lift_constraints #|i| cstrs)) (variance_cstrs l i i')
  end) /\
  #|i| = #|i'| /\ #|l| = #|i| /\
  i' = abstract_instance (ind_universes mdecl) /\
  closedu_instance #|i'| i' /\ i = lift_instance #|i'| i'.
Proof.
  unfold variance_universes.
  destruct (ind_universes mdecl); simpl.
  - intros H; noconf H; split; eauto.
  - destruct cst as [inst cstrs]. simpl; len. intros Hll.
    intros H; noconf H. len. simpl. intuition auto.
    rewrite /closedu_instance /level_var_instance forallb_mapi //.
    intros i hi. simpl. now eapply Nat.ltb_lt.
Qed.

Lemma consistent_instance_length {cf:checker_flags} {Σ : global_env_ext} {univs u} :
  consistent_instance_ext Σ univs u ->
  #|u| = #|abstract_instance univs|. 
Proof.
  rewrite /consistent_instance_ext /consistent_instance.
  destruct univs; simpl; auto.
  intros [_ [H _]].
  destruct cst; simpl in *.
  now rewrite H; len.
Qed.

Lemma consistent_instance_poly_length {cf:checker_flags} {Σ : global_env_ext} {inst cstrs u} :
  consistent_instance_ext Σ (Polymorphic_ctx (inst, cstrs)) u ->
  #|u| = #|inst|. 
Proof.
  rewrite /consistent_instance_ext /consistent_instance.
  intuition auto.
Qed.
 
Lemma consistent_instance_valid {cf:checker_flags} {Σ : global_env_ext} {inst cstrs u} :
  consistent_instance_ext Σ (Polymorphic_ctx (inst, cstrs)) u ->
  check_univs = true ->
  forall v, satisfies v (global_ext_constraints Σ) -> satisfies v (subst_instance_cstrs u cstrs).
Proof. rewrite /consistent_instance_ext /=; intros [_ [_ v]] cu.
    red in v. now rewrite cu in v.
Qed.

Definition closedu_cstr k (cstr : (Level.t * ConstraintType.t * Level.t)) :=
  let '(l1, p, l2) := cstr in
  closedu_level k l1 && closedu_level k l2. 

Definition closedu_cstrs k (cstrs : CS.t) :=
  CS.For_all (closedu_cstr k) cstrs.

Lemma LSet_in_poly_bounded l inst cstrs : LevelSet.In l (levels_of_udecl (Polymorphic_ctx (inst, cstrs))) ->
  closedu_level #|inst| l.
Proof.
  simpl.
  rewrite /mapi.
  change (#|inst|) with (0 + #|inst|).
  generalize 0.
  induction inst; simpl; auto.
  intros n emp. now eapply LevelSetFact.empty_iff in emp.
  intros n Hl.
  rewrite -> LS.add_spec in Hl.
  destruct Hl. subst.  simpl. apply Nat.ltb_lt; lia.
  specialize (IHinst _ H). now rewrite Nat.add_succ_r.
Qed.

Lemma LSet_in_global_bounded {cf:checker_flags} {Σ : global_env} {l} k : 
  wf Σ -> LevelSet.In l (global_levels Σ) ->
  closedu_level k l.
Proof.
  simpl.
  intros wf. eapply not_var_global_levels in wf.
  intros hin. specialize (wf _ hin). simpl in wf.
  destruct l; simpl in *; congruence.
Qed.

Lemma on_udecl_prop_poly_bounded {cf:checker_flags} Σ inst cstrs :
  wf Σ ->
  on_udecl_prop Σ (Polymorphic_ctx (inst, cstrs)) ->
  closedu_cstrs #|inst| cstrs.
Proof.
  rewrite /on_udecl_prop. intros wfΣ [nlevs _].
  red.
  rewrite /closedu_cstrs.
  intros x incstrs.
  specialize (nlevs x incstrs).
  destruct x as [[l1 p] l2].
  destruct nlevs.
  apply LevelSetProp.Dec.F.union_1 in H.
  apply LevelSetProp.Dec.F.union_1 in H0.
  destruct H. eapply LSet_in_poly_bounded in H.
  destruct H0. eapply LSet_in_poly_bounded in H0. simpl. now rewrite H H0.
  eapply (LSet_in_global_bounded #|inst|) in H0 => //. simpl.
  now rewrite H H0.
  eapply (LSet_in_global_bounded #|inst|) in H => //. simpl.
  destruct H0. eapply LSet_in_poly_bounded in H0. simpl. now rewrite H H0.
  eapply (LSet_in_global_bounded #|inst|) in H0 => //. simpl.
  now rewrite H H0.
Qed.

Lemma closedu_subst_instance_cstrs_app u u' cstrs :
  closedu_cstrs #|u| cstrs -> 
  CS.Equal (subst_instance_cstrs (u ++ u') cstrs) (subst_instance_cstrs u cstrs).
Proof.
  intros clcstra.
  intros c.
  rewrite !In_subst_instance_cstrs.
  firstorder eauto.
  subst c; exists x; split; auto.
  specialize (clcstra _ H0).
  simpl in *.
  destruct x as [[l c] r]; rewrite /subst_instance_cstr; simpl.
  move/andb_and: clcstra => [cll clr].
  rewrite !closedu_subst_instance_level_app //.

  subst c; exists x; split; auto.
  specialize (clcstra _ H0).
  simpl in *.
  destruct x as [[l c] r]; rewrite /subst_instance_cstr; simpl.
  move/andb_and: clcstra => [cll clr].
  rewrite !closedu_subst_instance_level_app //.
Qed.


Lemma In_lift_constraints u c ctrs :
  CS.In c (lift_constraints u ctrs)
  <-> exists c', c = lift_constraint u c' /\ CS.In c' ctrs.
Proof.
  unfold lift_constraints.
  rewrite CS.fold_spec.
  transitivity (CS.In c CS.empty \/
                exists c', c = lift_constraint u c'
                      /\ In c' (CS.elements ctrs)).
  - generalize (CS.elements ctrs), CS.empty.
    induction l; cbn.
    + firstorder.
    + intros t. etransitivity. 1: eapply IHl.
      split; intros [HH|HH].
      * destruct a as [[l1 a] l2]. apply CS.add_spec in HH.
        destruct HH as [HH|HH]. 2: now left.
        right; eexists. split; [|left; reflexivity]. assumption.
      * destruct HH as [c' ?]. right; exists c'; intuition auto.
      * left. destruct a as [[l1 a] l2]. apply CS.add_spec.
        now right.
      * destruct HH as [c' [HH1 [?|?]]]; subst.
        -- left. destruct c' as [[l1 c'] l2];
           apply CS.add_spec; now left.
        -- right. exists c'. intuition.
  - rewrite ConstraintSetFact.empty_iff.
    transitivity (exists c', c = lift_constraint u c'
                        /\ In c' (CS.elements ctrs)).
    1: intuition.
    apply iff_ex; intro. apply and_iff_compat_l. symmetry.
    etransitivity. 1: eapply CS.elements_spec1.
    etransitivity. 1: eapply SetoidList.InA_alt.
    split; intro; eauto.
    now destruct H as [? [[] ?]].
Qed.


Lemma closedu_subst_instance_cstrs_lift u u' cstrs :
  closedu_cstrs #|u'| cstrs -> 
  CS.Equal (subst_instance_cstrs (u ++ u') (lift_constraints #|u| cstrs)) (subst_instance_cstrs u' cstrs).
Proof.
  intros clcstra.
  intros c.
  rewrite !In_subst_instance_cstrs.
  firstorder eauto.
  - subst c.
    rewrite -> In_lift_constraints in H0.
    destruct H0 as [c' [-> inc']].
    exists c'. split; auto.
    specialize (clcstra _ inc').
    simpl in *.
    destruct c' as [[l c] r]; rewrite /subst_instance_cstr; simpl.
    move/andb_and: clcstra => [cll clr].
    rewrite !closedu_subst_instance_level_lift //.

  - subst c.
    exists (lift_constraint #|u| x).
    rewrite -> In_lift_constraints.
    pcuicfo eauto.
    specialize (clcstra _ H0).
    simpl in *.
    destruct x as [[l c] r]; rewrite /subst_instance_cstr; simpl.
    move/andb_and: clcstra => [cll clr].
    rewrite !closedu_subst_instance_level_lift //.
Qed.

Lemma subst_instance_cstrs_add u x c : 
  CS.Equal (subst_instance_cstrs u (ConstraintSet.add x c))
    (ConstraintSet.add (subst_instance_cstr u x) (subst_instance_cstrs u c)).
Proof.
  intros cc.
  rewrite ConstraintSetFact.add_iff.
  rewrite !In_subst_instance_cstrs.
  intuition auto.
  destruct H as [c' [-> inc']].
  rewrite -> ConstraintSetFact.add_iff in inc'.
  destruct inc'; subst; intuition auto.
  right. eexists; intuition eauto.
  subst.
  exists x; intuition eauto.
  now rewrite ConstraintSetFact.add_iff.
  destruct H0 as [c' [-> ?]].
  eexists c'; split; firstorder eauto.
  now rewrite ConstraintSetFact.add_iff.
Qed.

Lemma subst_instance_variance_cstrs l u i i' :
  CS.Equal (subst_instance_cstrs u (variance_cstrs l i i'))
    (variance_cstrs l (subst_instance u i) (subst_instance u i')).
Proof.
  induction l in u, i, i' |- *; simpl; auto;
  destruct i, i'; simpl => //.
  destruct a.
  - apply (IHl u i i').
  - rewrite -IHl.
    now rewrite subst_instance_cstrs_add.
  - rewrite -IHl.
    now rewrite subst_instance_cstrs_add.
Qed.

(** Morally, if variance_universes l = v i i' and R_universe_instance_variance l u u' then
  i and i' can be substituted respectively by u and u'.
    The hard part is to show that (Σ.1, v) can also be turned into Σ by instanciating
  i and i' by u and u'.
*)

Lemma cumul_inst_variance {cf:checker_flags} (Σ : global_env_ext) mdecl l v i i' u u' Γ : 
  wf Σ ->
  on_udecl_prop Σ (ind_universes mdecl) ->
  on_variance (ind_universes mdecl) (Some l) ->
  variance_universes (PCUICEnvironment.ind_universes mdecl) l = Some (v, i, i') ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  consistent_instance_ext Σ (ind_universes mdecl) u' ->
  R_universe_instance_variance (eq_universe Σ) (leq_universe Σ) l u u' ->
  forall t t',
  cumul (Σ.1, v) (subst_instance i Γ) (subst_instance i t) (subst_instance i' t') ->
  cumul Σ (subst_instance u Γ)
    (subst_instance u t) (subst_instance u' t').
Proof.
  intros wfΣ onu onv vari cu cu' Ru t t'.
  intros cum.
  destruct Σ as [Σ univs].
  pose proof (variance_universes_insts onv vari) as (cstrs & leni & lenl & eqi' & ci' & eqi).
  subst i.
  pose proof (consistent_instance_length cu).
  pose proof (consistent_instance_length cu').
  rewrite -eqi' in H, H0.
  rewrite -H0 in cum.
  assert (subst_instance (u' ++ u) (lift_instance #|u'| i') = u) as subsu.
  { rewrite closedu_subst_instance_lift //.
    now rewrite H. rewrite eqi'.
    erewrite subst_instance_id_mdecl => //. eauto. }
  assert (subst_instance (u' ++ u) i' = u') as subsu'.
  { rewrite closedu_subst_instance_app //.
    rewrite H0 //. rewrite eqi' //.
    erewrite subst_instance_id_mdecl => //. eauto. } 
  eapply (cumul_subst_instance (Σ, v) _ (u' ++ u)) in cum; auto.
  rewrite subst_instance_two in cum.
  rewrite !subst_instance_two in cum.
  rewrite subst_instance_two_context in cum.
  now rewrite subsu subsu' in cum.
  unfold valid_constraints. destruct check_univs eqn:checku => //.
  unfold valid_constraints0.
  intros v0 sat.
  rewrite satisfies_subst_instance_ctr //.
  simpl in sat.
  generalize sat.
  unfold global_ext_constraints.
  rewrite satisfies_union /= => [[satcstrs satglob]].
  rewrite satisfies_union. split; auto.
  2:{ rewrite -satisfies_subst_instance_ctr //.
      rewrite equal_subst_instance_cstrs_mono //.
      red; apply monomorphic_global_constraint; auto. }
  rewrite cstrs.
  destruct (ind_universes mdecl) as [[inst cstrs']|[inst cstrs']].
  { simpl in vari => //. }
  rewrite !satisfies_union. len.
  autorewrite with len in lenl.
  intuition auto.
  - rewrite -satisfies_subst_instance_ctr //.
    assert(ConstraintSet.Equal (subst_instance_cstrs u' cstrs')
        (subst_instance_cstrs (u' ++ u) cstrs')) as <-.
    { rewrite closedu_subst_instance_cstrs_app //.
      rewrite (consistent_instance_poly_length cu').
      eapply on_udecl_prop_poly_bounded; eauto. }
    eapply consistent_instance_valid in cu'; eauto.
  - rewrite -satisfies_subst_instance_ctr // -H0.
    assert(ConstraintSet.Equal (subst_instance_cstrs u cstrs')
        (subst_instance_cstrs (u' ++ u) (lift_constraints #|u'| cstrs'))) as <-.
    { rewrite closedu_subst_instance_cstrs_lift //.
      rewrite H -H0 (consistent_instance_poly_length cu').
      eapply on_udecl_prop_poly_bounded; eauto. }
    eapply consistent_instance_valid in cu; eauto.
  - rewrite -satisfies_subst_instance_ctr //.
    rewrite subst_instance_variance_cstrs //.
    rewrite -H0 subsu subsu'.
    assert (#|u| = #|u'|) as lenu by lia.
    assert (#|l| = #|u|) as lenlu. now rewrite lenl H.
    clear -checku Ru sat lenu lenlu.
    induction l in u, u', Ru, lenu, lenlu |- *. simpl in *. destruct u, u';
    intro; rewrite ConstraintSetFact.empty_iff //.
    destruct u, u' => //; simpl in *.
    destruct Ru as [Ra Rl].
    specialize (IHl u u' Rl). do 2 forward IHl by lia.
    destruct a => //; intros x; rewrite ConstraintSetFact.add_iff;
    intros [<-|inx]; auto.
    + do 2 red in Ra; rewrite checku in Ra;
      specialize (Ra _ sat); simpl in Ra.
      constructor. lia.
    + do 2 red in Ra. rewrite checku in Ra.
      specialize  (Ra _ sat).
      constructor. now rewrite !Universes.Universe.val_make in Ra.
Qed.

Lemma conv_inst_variance {cf:checker_flags} (Σ : global_env_ext) mdecl l v i i' u u' Γ : 
  wf Σ ->
  on_udecl_prop Σ (ind_universes mdecl) ->
  on_variance (ind_universes mdecl) (Some l) ->
  variance_universes (PCUICEnvironment.ind_universes mdecl) l = Some (v, i, i') ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  consistent_instance_ext Σ (ind_universes mdecl) u' ->
  R_universe_instance_variance (eq_universe Σ) (leq_universe Σ) l u u' ->
  forall t t',
  conv (Σ.1, v) (subst_instance i Γ) (subst_instance i t) (subst_instance i' t') ->
  conv Σ (subst_instance u Γ)
    (subst_instance u t) (subst_instance u' t').
Proof.
  intros wfΣ onu onv vari cu cu' Ru t t'.
  intros cum.
  destruct Σ as [Σ univs].
  pose proof (variance_universes_insts onv vari) as (cstrs & leni & lenl & eqi' & ci' & eqi).
  subst i.
  pose proof (consistent_instance_length cu).
  pose proof (consistent_instance_length cu').
  rewrite -eqi' in H, H0.
  rewrite -H0 in cum.
  assert (subst_instance (u' ++ u) (lift_instance #|u'| i') = u) as subsu.
  { rewrite closedu_subst_instance_lift //.
    now rewrite H. rewrite eqi'.
    erewrite subst_instance_id_mdecl => //. eauto. }
  assert (subst_instance (u' ++ u) i' = u') as subsu'.
  { rewrite closedu_subst_instance_app //.
    rewrite H0 //. rewrite eqi' //.
    erewrite subst_instance_id_mdecl => //. eauto. } 
  eapply (conv_subst_instance (Σ, v) _ (u' ++ u)) in cum; auto.
  rewrite subst_instance_two in cum.
  rewrite !subst_instance_two subst_instance_two_context in cum.
  now rewrite subsu subsu' in cum.
  unfold valid_constraints. destruct check_univs eqn:checku => //.
  unfold valid_constraints0.
  intros v0 sat.
  rewrite satisfies_subst_instance_ctr //.
  simpl in sat.
  generalize sat.
  unfold global_ext_constraints.
  rewrite satisfies_union /= => [[satcstrs satglob]].
  rewrite satisfies_union. split; auto.
  2:{ rewrite -satisfies_subst_instance_ctr //.
      rewrite equal_subst_instance_cstrs_mono //.
      red; apply monomorphic_global_constraint; auto. }
  rewrite cstrs.
  destruct (ind_universes mdecl) as [[inst cstrs']|[inst cstrs']].
  { simpl in vari => //. }
  rewrite !satisfies_union. len.
  autorewrite with len in lenl.
  intuition auto.
  - rewrite -satisfies_subst_instance_ctr //.
    assert(ConstraintSet.Equal (subst_instance_cstrs u' cstrs')
        (subst_instance_cstrs (u' ++ u) cstrs')) as <-.
    { rewrite closedu_subst_instance_cstrs_app //.
      rewrite (consistent_instance_poly_length cu').
      eapply on_udecl_prop_poly_bounded; eauto. }
    eapply consistent_instance_valid in cu'; eauto.
  - rewrite -satisfies_subst_instance_ctr // -H0.
    assert(ConstraintSet.Equal (subst_instance_cstrs u cstrs')
        (subst_instance_cstrs (u' ++ u) (lift_constraints #|u'| cstrs'))) as <-.
    { rewrite closedu_subst_instance_cstrs_lift //.
      rewrite H -H0 (consistent_instance_poly_length cu').
      eapply on_udecl_prop_poly_bounded; eauto. }
    eapply consistent_instance_valid in cu; eauto.
  - rewrite -satisfies_subst_instance_ctr //.
    rewrite subst_instance_variance_cstrs //.
    rewrite -H0 subsu subsu'.
    assert (#|u| = #|u'|) as lenu by lia.
    assert (#|l| = #|u|) as lenlu. now rewrite lenl H.
    clear -checku Ru sat lenu lenlu.
    induction l in u, u', Ru, lenu, lenlu |- *. simpl in *. destruct u, u';
    intro; rewrite ConstraintSetFact.empty_iff //.
    destruct u, u' => //; simpl in *.
    destruct Ru as [Ra Rl].
    specialize (IHl u u' Rl). do 2 forward IHl by lia.
    destruct a => //; intros x; rewrite ConstraintSetFact.add_iff;
    intros [<-|inx]; auto.
    + do 2 red in Ra; rewrite checku in Ra;
      specialize (Ra _ sat); simpl in Ra.
      constructor. now lia.
    + do 2 red in Ra. rewrite checku in Ra.
      specialize  (Ra _ sat).
      constructor. now rewrite !Universes.Universe.val_make in Ra.
Qed.

Lemma All2_fold_inst {cf:checker_flags} (Σ : global_env_ext) mdecl l v i i' u u' Γ' Γ : 
  wf Σ ->  
  on_udecl_prop Σ (ind_universes mdecl) ->
  on_variance (ind_universes mdecl) (Some l) ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  consistent_instance_ext Σ (ind_universes mdecl) u' ->
  variance_universes (PCUICEnvironment.ind_universes mdecl) l = Some (v, i, i') ->
  R_universe_instance_variance (eq_universe Σ) (leq_universe Σ) l u u' ->
  cumul_ctx_rel (Σ.1, v) (subst_instance i Γ') (subst_instance i Γ) (subst_instance i' Γ) ->
  cumul_ctx_rel Σ (subst_instance u Γ') (subst_instance u Γ) (subst_instance u' Γ).
Proof.
  unfold cumul_ctx_rel.
  intros wfΣ onu onv cu cu' vari Ru.
  induction Γ as [|[na [b|] ty] tl]; simpl.
  constructor. intros H; depelim H.
  econstructor; auto.
  depelim c. simpl.
  rewrite -subst_instance_app_ctx in c, c0. simpl in c0 |- *.
  rewrite -subst_instance_app_ctx.
  constructor. reflexivity.
  eapply conv_inst_variance; eauto.
  eapply cumul_inst_variance; eauto.

  intros H; depelim H; simpl in *. depelim c.
  constructor; auto. constructor; auto.
  rewrite -subst_instance_app_ctx in c.
  rewrite -subst_instance_app_ctx.
  eapply cumul_inst_variance; eauto.
Qed.

Lemma forallb_closed_upwards k k' s : 
  forallb (closedn k) s ->
  k <= k' ->
  forallb (closedn k') s.
Proof.
  intros H Hk.
  eapply All_forallb.
  eapply forallb_All in H. solve_all.
  eapply closed_upwards; eauto.
Qed.

Lemma subst_context_subst_context s k s' Γ :
  subst_context s k (subst_context s' 0 Γ) =
  subst_context (map (subst s k) s') 0 (subst_context s (k + #|s'|) Γ).
Proof.
  induction Γ as [|[na [b|] ty] Γ']; simpl; auto; 
    rewrite !subst_context_snoc /= /subst_decl /map_decl /=; f_equal; 
    auto; f_equal; len;
  rewrite distr_subst_rec; lia_f_equal.
Qed.

Lemma subst_context_subst_context_comm s k k' s' Γ :
  k' = k + #|s| ->
  subst_context s k (subst_context s' k' Γ) =
  subst_context s' k (subst_context (map (lift0 #|s'|) s) k Γ).
Proof.
  intros ->.
  induction Γ as [|[na [b|] ty] Γ']; simpl; auto; 
    rewrite !subst_context_snoc /= /subst_decl /map_decl /=; f_equal; 
    auto; f_equal; len;
    now rewrite Nat.add_assoc -subst_app_simpl subst_app_decomp.
Qed.
 
Lemma subst_context_lift_context_cancel s k n Γ :
  n = #|s| ->
  subst_context s k (lift_context n k Γ) = Γ.
Proof.
  intros ->.
  induction Γ as [|[na [b|] ty] Γ']; auto;
    rewrite !lift_context_snoc !subst_context_snoc /= /subst_decl /map_decl /snoc /=; simpl; f_equal;
    auto; f_equal; len;
    rewrite -(Nat.add_0_r #|s|) simpl_subst_rec /= // ?lift0_id //; lia.
Qed.

(* Lemma All2_fold_impl' (P Q : context -> context -> term -> term -> Type)
  (par par' : context) :
  All2_fold P par par' ->
  (forall (par0 par'0 : context) (o : option (term * term)) (x y : term),
  P par0 par'0 o x y -> Q par0 par'0 o x y) ->
  All2_fold Q par par'.
Proof.
  intros H HP; induction H; constructor; auto.
Qed. *)

Lemma map_map_subst_expand_lets (s : list term) (Γ : context) l k :
  context_assumptions Γ = #|s| ->
  map (subst (map (subst0 s) (extended_subst Γ 0)) k) l = map (subst s k ∘ expand_lets_k Γ k) l.
Proof. move=> ca; apply map_ext => x; apply map_subst_expand_lets_k => //. Qed.

Lemma expand_lets_k_app (Γ Γ' : context) t k : expand_lets_k (Γ ++ Γ') k t =
  expand_lets_k Γ' (k + context_assumptions Γ) (expand_lets_k Γ k t).
Proof.
  revert Γ k t.
  induction Γ' as [|[na [b|] ty] Γ'] using ctx_length_rev_ind; intros Γ k t.
  - simpl. now rewrite /expand_lets_k /= subst_empty lift0_id app_nil_r.
  - simpl; rewrite app_assoc !expand_lets_k_vdef /=; len; simpl.
    rewrite subst_context_app. specialize (H (subst_context [b] 0 Γ') ltac:(now len)).
    specialize (H (subst_context [b] #|Γ'| Γ)). rewrite Nat.add_0_r /app_context H; len.
    f_equal.
    rewrite /expand_lets_k; len.
    rewrite -Nat.add_assoc.
    rewrite distr_subst_rec; len.
    epose proof (subst_extended_subst_k [b] Γ #|Γ'| 0).
    rewrite Nat.add_0_r Nat.add_comm in H0. rewrite -H0. f_equal.
    rewrite commut_lift_subst_rec. lia. lia_f_equal.
  - simpl. rewrite app_assoc !expand_lets_k_vass /=; len; simpl.
    now rewrite (H Γ' ltac:(reflexivity)).
Qed.

Lemma expand_lets_app Γ Γ' t : expand_lets (Γ ++ Γ') t =
  expand_lets_k Γ' (context_assumptions Γ) (expand_lets Γ t).
Proof.
  now rewrite /expand_lets expand_lets_k_app.
Qed.

Hint Rewrite closedn_subst_instance : pcuic.

Lemma subst_conv_closed {cf : checker_flags} {Σ : global_env_ext}
  {Γ Γ0 Γ1 Δ : context} {s s' : list term} {T U : term} :
  wf Σ.1 ->
  subslet Σ Γ s Γ0 ->
  subslet Σ Γ s' Γ1 ->
  #|s| = #|s'| ->
  closedn #|Δ| T ->
  closedn #|Δ| U ->
  wf_local Σ (Γ ,,, Γ0 ,,, Δ) ->
  Σ;;; Γ ,,, Γ0 ,,, Δ |- T = U ->
  Σ;;; Γ ,,, subst_context s 0 Δ |- subst s #|Δ| T = subst s' #|Δ| U.
Proof.
  intros wfΣ subs subs' eqs clT clU wf.
  intros cum.
  pose proof (substitution_conv Σ _ _ _ s _ _ wfΣ  wf subs cum).
  transitivity (subst s #|Δ| U) => //.
  clear X.
  rewrite !subst_closedn //.
  reflexivity.
Qed.

Lemma subst_instance_expand_lets u Γ t :
  subst_instance u (expand_lets Γ t) = 
  expand_lets (subst_instance u Γ) (subst_instance u t).
Proof.
  rewrite /expand_lets /expand_lets_k.
  rewrite subst_instance_subst.
  rewrite subst_instance_extended_subst.
  f_equal.
  rewrite subst_instance_lift. len; f_equal.
Qed.

Hint Rewrite subst_instance_expand_lets closedn_subst_instance : substu.

Lemma subst_instance_expand_lets_ctx u Γ Δ :
  subst_instance u (expand_lets_ctx Γ Δ) =
  expand_lets_ctx (subst_instance u Γ) (subst_instance u Δ).
Proof.
  rewrite /expand_lets_ctx /expand_lets_k_ctx.
  rewrite !subst_instance_subst_context !subst_instance_lift_context; len.
  now rewrite -subst_instance_extended_subst.
Qed.

Lemma inductive_cumulative_indices {cf:checker_flags} {Σ : global_env_ext} (wfΣ : wf Σ.1) :
  forall {ind mdecl idecl u u' napp},
  declared_inductive Σ ind mdecl idecl ->
  on_udecl_prop Σ (ind_universes mdecl) ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  consistent_instance_ext Σ (ind_universes mdecl) u' ->
  R_global_instance Σ (eq_universe Σ) (leq_universe Σ) (IndRef ind) napp u u' ->
  forall Γ pars pars' parsubst parsubst',
  spine_subst Σ Γ pars parsubst (subst_instance u (ind_params mdecl)) ->
  spine_subst Σ Γ pars' parsubst' (subst_instance u' (ind_params mdecl)) ->  
  All2 (conv Σ Γ) pars pars' ->
  let indctx := subst_instance u idecl.(ind_indices) in
  let indctx' := subst_instance u' idecl.(ind_indices) in
  let pindctx := subst_context parsubst 0 indctx in
  let pindctx' := subst_context parsubst' 0 indctx' in
  cumul_ctx_rel Σ Γ (smash_context [] pindctx) (smash_context [] pindctx').
Proof.
  intros * decli.
  destruct (on_declared_inductive decli) as [onmind oib].
  intros onu cu cu' Ru Γ * spu spu' cpars *. move: Ru.
  unfold R_global_instance.
  pose proof decli as decli'.
  assert (closed_ctx
    (subst_instance u
      (PCUICEnvironment.ind_params mdecl))) as clpu.
  { eapply closed_wf_local; eauto; eapply on_minductive_wf_params; eauto. }
  assert (closed_ctx
  (subst_instance u'
    (PCUICEnvironment.ind_params mdecl)))  as clpu'.
  {  eapply closed_wf_local; eauto; eapply on_minductive_wf_params; eauto. }
  assert (closed_ctx
    (subst_instance u
      (smash_context [] (PCUICEnvironment.ind_params mdecl)))) as clspu.
  { rewrite subst_instance_smash. now eapply closedn_smash_context. }
  clear decli'.
  assert (wf_local Σ
  (smash_context []
     (subst_instance u (PCUICEnvironment.ind_params mdecl)) ,,,
   smash_context []
     (subst_instance u
        (expand_lets_ctx (PCUICEnvironment.ind_params mdecl)
           (ind_indices idecl))))).
  { pose proof (on_minductive_wf_params_indices_inst decli _ cu) as wf.
    eapply wf_local_smash_context in wf; auto.
    rewrite subst_instance_app_ctx smash_context_app_expand in wf.
    rewrite expand_lets_smash_context expand_lets_k_ctx_nil in wf.
    now rewrite subst_instance_expand_lets_ctx. }
  destruct global_variance eqn:gv.
  { move:gv.
    simpl. rewrite (declared_inductive_lookup_inductive decli).
    rewrite oib.(ind_arity_eq). 
    rewrite !destArity_it_mkProd_or_LetIn. simpl.
    rewrite app_context_nil_l context_assumptions_app.
    elim: leb_spec_Set => // comp.
    destruct ind_variance eqn:indv => //.
    move=> [=] eq. subst l0.
    pose proof (oib.(onIndices)) as respv.
    specialize (respv _ indv).
    simpl in respv.
    unfold ind_respects_variance in respv.
    destruct variance_universes as [[[v i] i']|] eqn:vu => //.
    simpl => Ru.
    pose proof (onVariance onmind) as onvari.
    rewrite indv in onvari.
    eapply All2_fold_inst in respv.
    8:eauto. all:eauto. move: respv.
    rewrite !expand_lets_smash_context.
    autorewrite with pcuic.
    rewrite !subst_instance_smash /= => args.
    eapply (weaken_cumul_ctx _ Γ) in args => //.
    4:eapply spu.
    2:{ eapply closed_wf_local; eauto. }
    2:{ rewrite closedn_ctx_app; apply /andb_and. split => //. simpl.
        len. simpl. eapply closedn_smash_context => //.
        len; simpl. 
        pose proof (on_minductive_wf_params_indices_inst decli _ cu') as wf'.
        eapply closed_wf_local in wf'; eauto.
        rewrite subst_instance_app_ctx in wf'.
        rewrite closedn_ctx_app in wf'. move/andb_and: wf'=> [_ clargs].
        simpl in clargs; autorewrite with len in clargs.
        eapply closedn_smash_context => //.
        rewrite closedn_subst_instance_context.
        rewrite -(Nat.add_0_l (context_assumptions (ind_params _))).
        eapply closedn_ctx_expand_lets.
        now rewrite -(closedn_subst_instance_context (u:=u)).
        now rewrite closedn_subst_instance_context in clargs. }
    pose proof (spine_subst_smash wfΣ spu) as sspu.
    pose proof (spine_subst_smash wfΣ spu') as sspu'.
    eapply (cumul_ctx_subst _ Γ _ _ [] _ _ (List.rev pars) (List.rev pars')) in args; eauto.
    3:{ eapply All2_rev => //. }
    3:{ eapply subslet_untyped_subslet. eapply sspu. }
    3:{ eapply subslet_untyped_subslet. eapply sspu'. }
    2:{ rewrite - !app_context_assoc. eapply weaken_wf_local; eauto.
        eapply spu. now rewrite app_context_nil_l. }
    move: args.
    rewrite subst_context_nil /= - !smash_context_subst /= subst_context_nil; len.
    rewrite !subst_instance_subst_context.
    rewrite !subst_instance_extended_subst.
    rewrite (subst_context_subst_context (List.rev pars)) /=; len.
    rewrite -(spine_subst_extended_subst spu).
    rewrite !subst_instance_lift_context. len.
    rewrite subst_context_lift_context_cancel.
    len. rewrite (context_subst_length2 spu); len; lia.
    rewrite (subst_context_subst_context (List.rev pars')) /=; len.
    rewrite -(spine_subst_extended_subst spu').
    len. rewrite subst_context_lift_context_cancel.
    len. rewrite (context_subst_length2 spu'); len; lia.
    now rewrite subst_context_nil. }
  simpl. intros.
  { rewrite /pindctx /pindctx' /indctx /indctx'.
    rewrite !(smash_context_subst []).
    eapply (cumul_ctx_subst _ _ _ _ []); eauto.
    4:eapply subslet_untyped_subslet; eapply spu.
    4:eapply subslet_untyped_subslet; eapply spu'.
    { simpl. eapply wf_local_smash_end; eauto.
      rewrite -app_context_assoc. eapply weaken_wf_local; eauto. eapply spu.
      rewrite -subst_instance_app_ctx.
      apply (on_minductive_wf_params_indices_inst decli _ cu). }
    2:{ eapply spine_subst_conv; eauto.
      eapply All2_fold_subst_instance; eauto. apply spu.
      eapply on_minductive_wf_params; eauto. }
    simpl.
    rewrite -(subst_instance_smash u _ []).
    rewrite -(subst_instance_smash u' _ []).
    eapply cumul_ctx_subst_instance => //.
    eapply weaken_wf_local; pcuic. eapply spu.
    eapply on_minductive_wf_params; eauto. }
Qed.

Hint Resolve declared_inductive_minductive : core.
Hint Resolve declared_constructor_inductive : core.

Lemma constructor_cumulative_indices {cf:checker_flags} {Σ : global_env_ext} (wfΣ : wf Σ.1) :
  forall {c mdecl idecl cdecl u u' napp},
  declared_constructor Σ c mdecl idecl cdecl ->
  on_udecl_prop Σ (ind_universes mdecl) ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  consistent_instance_ext Σ (ind_universes mdecl) u' ->
  R_global_instance Σ (eq_universe Σ) (leq_universe Σ) (IndRef c.1) napp u u' ->
  forall Γ pars pars' parsubst parsubst',
  spine_subst Σ Γ pars parsubst (subst_instance u (ind_params mdecl)) ->
  spine_subst Σ Γ pars' parsubst' (subst_instance u' (ind_params mdecl)) ->  
  All2 (conv Σ Γ) pars pars' ->
  let argctx := 
      (subst_context (ind_subst mdecl c.1 u) #|ind_params mdecl| (subst_instance u (cstr_args cdecl)))
  in
  let argctx' :=
     (subst_context (ind_subst mdecl c.1 u') #|ind_params mdecl| (subst_instance u' (cstr_args cdecl)))
  in
  let pargctx := subst_context parsubst 0 argctx in
  let pargctx' := subst_context parsubst' 0 argctx' in
  cumul_ctx_rel Σ Γ (smash_context [] pargctx) (smash_context [] pargctx') *
  All2 (conv Σ (Γ ,,, smash_context [] pargctx))
    (map (subst parsubst (context_assumptions (cstr_args cdecl)))
      (map (expand_lets argctx) (map (subst_instance u) (cstr_indices cdecl))))
    (map (subst parsubst' (context_assumptions (cstr_args cdecl)))
      (map (expand_lets argctx') (map (subst_instance u') (cstr_indices cdecl)))).
Proof.
  intros * declc.
  destruct (on_declared_constructor declc) as [[onmind oib] [cs [hnth onc]]].
  intros onu cu cu' Ru Γ * spu spu' cpars *. move: Ru.
  unfold R_global_instance.
  assert (closed_ctx
    (subst_instance u
      (PCUICEnvironment.ind_params mdecl))) as clpu.
  { eapply closed_wf_local; eauto; eapply on_minductive_wf_params; eauto. }
  assert (closed_ctx
  (subst_instance u'
    (PCUICEnvironment.ind_params mdecl)))  as clpu'.
  {  eapply closed_wf_local; eauto; eapply on_minductive_wf_params; eauto. }
  assert (closed_ctx
    (subst_instance u
      (smash_context [] (PCUICEnvironment.ind_params mdecl)))) as clspu.
  { rewrite subst_instance_smash. now eapply closedn_smash_context. }
  destruct global_variance eqn:gv.
  { move:gv.
    simpl. rewrite (declared_inductive_lookup_inductive declc).
    rewrite oib.(ind_arity_eq). 
    rewrite !destArity_it_mkProd_or_LetIn. simpl.
    rewrite app_context_nil_l context_assumptions_app.
    elim: leb_spec_Set => // comp.
    destruct ind_variance eqn:indv => //.
    move=> [=] eq. subst l0.
    pose proof (onc.(on_ctype_variance)) as respv.
    specialize (respv _ indv).
    simpl in respv.
    unfold cstr_respects_variance in respv.
    destruct variance_universes as [[[v i] i']|] eqn:vu => //.
    destruct respv as [args idx].
    simpl => Ru.
    pose proof (onVariance onmind) as onvari.
    rewrite indv in onvari.
    split.
    { eapply All2_fold_inst in args.
      8:eauto. all:eauto.
      rewrite !expand_lets_smash_context in args.
      autorewrite with pcuic in args.
      rewrite !subst_instance_smash /= in args.
      rewrite subst_instance_app_ctx in args.
      eapply positive_cstr_closed_args in args; eauto.
      2:{ rewrite indv. now simpl. }  
      rewrite - !smash_context_subst !subst_context_nil in args.
      destruct args as [args wfargs].
      eapply (weaken_cumul_ctx _ Γ) in args => //.
      4:eapply spu.
      2:{ eapply closed_wf_local; eauto. }
      2:{ rewrite closedn_ctx_app; apply /andb_and. split => //. simpl.
          len. simpl. eapply closedn_smash_context.
          rewrite -(Nat.add_0_l (context_assumptions _)).
          eapply closedn_ctx_subst. len; simpl.
          2:{ eapply declared_minductive_closed_inds; eauto. }
          epose proof (on_constructor_wf_args declc) as wf'; eauto.
          eapply closed_wf_local in wf'; eauto.
          rewrite closedn_ctx_app in wf'. move/andb_and: wf'=> [_ clargs].
          simpl in clargs; autorewrite with len in clargs.
          rewrite closedn_subst_instance_context.
          rewrite Nat.add_comm.
          eapply closedn_ctx_expand_lets.
          rewrite -(closedn_subst_instance_context (u:=u)).
          eapply closedn_ctx_upwards; eauto. lia.
          now rewrite Nat.add_comm. }
      pose proof (spine_subst_smash wfΣ spu) as sspu.
      pose proof (spine_subst_smash wfΣ spu') as sspu'.
      eapply (cumul_ctx_subst _ Γ _ _ [] _ _ (List.rev pars) (List.rev pars')) in args; eauto.
      3:{ eapply All2_rev => //. }
      3:{ rewrite subst_instance_smash /=.
          eapply subslet_untyped_subslet. eapply sspu. }
      3:{ eapply subslet_untyped_subslet. eapply sspu'. }
      2:{ rewrite - !app_context_assoc. eapply weaken_wf_local; eauto.
          eapply spu. now rewrite app_context_nil_l. }
      move: args.
      rewrite subst_context_nil /= - !smash_context_subst /= subst_context_nil; len.
      rewrite !subst_instance_subst_context.
      rewrite !subst_instance_extended_subst.
      rewrite (subst_context_subst_context (inds  _ u _)); len.
      rewrite (subst_context_subst_context (inds  _ u' _)); len.
      rewrite -(subst_instance_assumptions u).
      rewrite -(subst_extended_subst).
      rewrite (closed_ctx_subst (inds _ _ _)) //.
      rewrite (subst_instance_assumptions u).
      rewrite -(subst_instance_assumptions u').
      rewrite -(subst_extended_subst).
      rewrite (closed_ctx_subst (inds _ u' _)) //.
      rewrite (subst_instance_assumptions u').
      rewrite (subst_context_subst_context (List.rev pars)) /=; len.
      rewrite -(spine_subst_extended_subst spu).
      rewrite !subst_instance_lift_context. len.
      rewrite (subst_context_subst_context_comm (List.rev _)).
      len. rewrite (context_subst_length2 spu); len; lia.
      len. rewrite subst_context_lift_context_cancel.
      len. rewrite (context_subst_length2 spu); len; lia.
      rewrite (subst_context_subst_context (List.rev pars')) /=; len.
      rewrite -(spine_subst_extended_subst spu').
      rewrite (subst_context_subst_context_comm (List.rev pars')).
      len. rewrite (context_subst_length2 spu'); len; lia.
      len. rewrite subst_context_lift_context_cancel.
      len. rewrite (context_subst_length2 spu'); len; lia.
      now rewrite subst_context_nil.
    }
    { rewrite /pargctx /pargctx' (smash_context_subst []).
      rewrite (spine_subst_extended_subst spu) (spine_subst_extended_subst spu').
      rewrite !subst_context_map_subst_expand_lets_k.
      now rewrite -(context_subst_length2 spu); len.
      rewrite map_map_subst_expand_lets.
      now rewrite -(context_subst_length2 spu); len.
      rewrite -map_map_compose.
      rewrite map_map_subst_expand_lets.
      now rewrite -(context_subst_length2 spu'); len.
      simpl.
      rewrite -(map_map_compose _ _ _ _ (subst (List.rev pars') _)).
      evar (k : nat).
      replace (context_assumptions (cstr_args cdecl)) with k. subst k.
      unshelve eapply (conv_terms_subst _ _ _ _ _ _ _ _ _ wfΣ _ (spine_subst_smash wfΣ spu) (spine_subst_smash wfΣ spu')).
      { rewrite -app_context_assoc -smash_context_app_expand. eapply wf_local_smash_end; eauto.
        rewrite /argctx. apply weaken_wf_local; eauto. eapply spu.
        destruct (on_constructor_inst declc _ cu) as [wfparargs _].
        rewrite !subst_instance_app_ctx in wfparargs.
        rewrite -app_context_assoc in wfparargs.
        rewrite -(app_context_nil_l (subst_instance _ _ ,,, _)) in wfparargs.
        rewrite app_context_assoc in wfparargs.
        eapply (substitution_wf_local _ []) in wfparargs; eauto.
        2:{ eapply subslet_inds; eauto. }
        rewrite subst_context_app /= app_context_nil_l in wfparargs.
        len in wfparargs.
        rewrite closed_ctx_subst // in wfparargs. }
      eapply All2_rev; eauto.
      2:{ subst k; len. now rewrite /argctx; len. }
      len. simpl.
      rewrite !map_map_compose; eapply All2_map.
      eapply All2_map_inv in idx.
      epose proof (positive_cstr_closed_indices _ declc) as cli.
      eapply All_map_inv in cli.
      eapply All2_All in idx.
      eapply All_mix in idx; tea. clear cli.
      eapply All_All2; tea. solve_all.
      rename a into clx; rename b into cxy.
      rewrite -app_context_assoc; eapply weaken_conv; eauto.
      { destruct (on_constructor_inst_pars_indices _ declc cu spu) as [wfparargs _].
        rewrite -smash_context_app_expand. 
        eapply closed_wf_local; eauto.
        eapply wf_local_smash_context; eauto. }
      { len. simpl. rewrite expand_lets_app in clx.
        rewrite -(subst_instance_assumptions u (ind_params _)).
        rewrite (closedn_expand_lets_eq 0) // /=; len.
        rewrite context_assumptions_app in clx.
        rewrite (closedn_expand_lets_eq 0 (ind_params _)) // /= in clx; len.
        now erewrite <- (closedn_subst_instance_context (u:=u)).
        rewrite Nat.add_comm. 
        epose proof (closedn_expand_lets_eq #|ind_params mdecl| _ 0 _).
        rewrite Nat.add_0_r in H. rewrite /expand_lets. rewrite -> H;
        rewrite Nat.add_comm in clx; eapply closedn_expand_lets in clx.
        substu. now rewrite /argctx; len.
        rewrite /argctx.
        rewrite -(Nat.add_0_l #|ind_params mdecl|).
        eapply closedn_ctx_subst; cbn. rewrite /ind_subst; len.
        epose proof (on_constructor_inst declc _ cu) as [wfarpars _]; auto.
        move/closed_wf_local: wfarpars. rewrite !subst_instance_app_ctx closedn_ctx_app.
        now move/andb_and; len.
        rewrite /ind_subst. eapply declared_minductive_closed_inds; eauto. }
      { len. simpl. rewrite expand_lets_app in clx.
        rewrite -(subst_instance_assumptions u' (ind_params _)).
        rewrite (closedn_expand_lets_eq 0) // /=; len.
        rewrite context_assumptions_app in clx.
        rewrite (closedn_expand_lets_eq 0 (ind_params _)) // /= in clx; len.
        now erewrite <- (closedn_subst_instance_context (u := u')).
        rewrite Nat.add_comm. 
        epose proof (closedn_expand_lets_eq #|ind_params mdecl| _ 0 _).
        rewrite Nat.add_0_r in H. rewrite /expand_lets.
        relativize (context_assumptions argctx). rewrite -> H.
        rewrite Nat.add_comm in clx; eapply closedn_expand_lets in clx.
        substu. now rewrite /argctx'; len.
        rewrite /argctx'.
        rewrite -(Nat.add_0_l #|ind_params mdecl|).
        eapply closedn_ctx_subst; cbn. rewrite /ind_subst; len.
        epose proof (on_constructor_inst declc _ cu') as [wfarpars _]; auto.
        move/closed_wf_local: wfarpars. rewrite !subst_instance_app_ctx closedn_ctx_app.
        now move/andb_and; len.
        rewrite /ind_subst. eapply declared_minductive_closed_inds; eauto.
        now rewrite /argctx /argctx'; len. }
      rewrite smash_context_app smash_context_acc in cxy.
      autorewrite with len in cxy.
      eapply conv_inst_variance in cxy.
      8:eauto. all:eauto.
      rewrite subst_instance_app_ctx in cxy.
      epose proof (subst_conv_closed (Γ := []) wfΣ) as X3.
      rewrite !app_context_nil_l in X3. eapply X3 in cxy; clear X3; cycle 1.
      { eapply (subslet_inds _ _ u); eauto. }
      { eapply (subslet_inds _ _ u'); eauto. }
      { now len. }
      { len. simpl. autorewrite with pcuic. now rewrite -context_assumptions_app. }
      { len. simpl. autorewrite with pcuic. now rewrite -context_assumptions_app. }
      { destruct (on_constructor_inst declc _ cu) as [wfparargs _].
        rewrite subst_instance_app_ctx subst_instance_smash /=.
        rewrite subst_instance_subst_context subst_instance_lift_context subst_instance_smash.
        rewrite subst_instance_extended_subst.
        rewrite -(subst_instance_assumptions u (ind_params mdecl)).
        rewrite -(subst_instance_length u (ind_params mdecl)).
        rewrite -smash_context_app_expand. eapply wf_local_smash_end; eauto.
        now rewrite - !subst_instance_app_ctx app_context_assoc. }
      len in cxy; substu in cxy.
      rewrite -context_assumptions_app in cxy.
      rewrite -{1}(subst_instance_assumptions u (_ ++ _)) in cxy.
      rewrite -{1}(subst_instance_assumptions u' (_ ++ _)) in cxy.
      rewrite -(expand_lets_subst_comm' _ _ 0) in cxy.
      { len. substu; cbn. eapply (closedn_expand_lets 0) in clx.
        red; rewrite -clx; now len. }
      rewrite -(expand_lets_subst_comm' _ _ 0) in cxy.
        { len. substu; cbn. eapply (closedn_expand_lets 0) in clx.
          red; rewrite -clx; now len. }
      rewrite !subst_instance_app_ctx in cxy.
      rewrite !subst_context_app in cxy. len in cxy.
      rewrite (closed_ctx_subst (inds _ _ _ )) // in cxy.
      rewrite (closed_ctx_subst (inds _ _ _ ) _ (subst_instance u (ind_params mdecl))) // in cxy.
      rewrite (closed_ctx_subst (inds _ _ _ ) _ (subst_instance u' (ind_params mdecl))) // in cxy.
      rewrite {2 4}/argctx; len.
      rewrite !expand_lets_app in cxy; len in cxy.
      rewrite {2}/argctx /argctx'.
      eapply conv_eq_ctx; eauto.
      rewrite subst_instance_smash /=; f_equal.
      rewrite subst_instance_subst_context subst_instance_lift_context subst_instance_smash /=.
      rewrite /argctx /expand_lets_k_ctx.
      rewrite subst_instance_extended_subst.
      rewrite subst_context_subst_context.
      rewrite -(subst_instance_assumptions u).
      rewrite -(subst_extended_subst).
      rewrite subst_instance_assumptions.
      rewrite (closed_ctx_subst (inds _ _ _ )) //. f_equal.
      len. simpl.
      rewrite (smash_context_subst []).
      now rewrite subst_context_lift_context_comm; try lia. }
  } 
  { simpl.
    assert (wf_local Σ Γ) by apply spu.
    epose proof (on_constructor_inst declc _ cu) as [wfargs spinst].
    intros Ru; split.
    { rewrite /pargctx /pargctx' /argctx /argctx'.
      rewrite !(smash_context_subst []).
      eapply (cumul_ctx_subst _ _ _ _ []); eauto.
      4:eapply subslet_untyped_subslet; eapply spu.
      4:eapply subslet_untyped_subslet; eapply spu'.
      { simpl.
        rewrite -app_context_assoc. eapply weaken_wf_local; eauto.
        rewrite !subst_instance_app_ctx in wfargs.
        rewrite -app_context_assoc in wfargs.
        rewrite -(app_context_nil_l (subst_instance _ _ ,,, _)) in wfargs.
        rewrite app_context_assoc in wfargs.
        eapply (substitution_wf_local _ []) in wfargs; eauto.
        2:{ eapply subslet_inds; eauto. }
        rewrite subst_context_app /= app_context_nil_l in wfargs.
        autorewrite with len  in wfargs.
        rewrite closed_ctx_subst // in wfargs.
        rewrite -(smash_context_subst []).
        eapply wf_local_smash_end => //. }
      2:{ eapply spine_subst_conv; eauto.
          eapply All2_fold_subst_instance; eauto.
          eapply on_minductive_wf_params; eauto. }
      simpl.
      assert (subst_context (ind_subst mdecl c.1 u) 0 (subst_instance u (ind_params mdecl)) = 
        (subst_instance u (ind_params mdecl))) as ispars.
      { rewrite closed_ctx_subst; eauto. }
      rewrite -ispars.
      rewrite -(subst_instance_length u (ind_params mdecl)).
      eapply (cumul_ctx_subst _ Γ); eauto.
      4:{ eapply subslet_untyped_subslet. eapply PCUICArities.weaken_subslet; eauto; eapply subslet_inds; eauto. }
      4:{ eapply subslet_untyped_subslet. eapply PCUICArities.weaken_subslet; eauto; eapply subslet_inds; eauto. }
      { simpl.
        rewrite - !app_context_assoc. eapply weaken_wf_local; eauto.
        rewrite app_context_assoc. eapply wf_local_smash_end; auto.
        now rewrite !subst_instance_app_ctx in wfargs. }
      2:now eapply conv_inds.
      rewrite - !(subst_instance_smash _ _ []).
      eapply cumul_ctx_subst_instance => //.
      rewrite -app_context_assoc. eapply weaken_wf_local; eauto.
      rewrite !subst_instance_app_ctx in wfargs.
      now eapply All_local_env_app_inv in wfargs as [wfargs _].
    }
    { rewrite /pargctx.
      rewrite (smash_context_subst []).
      evar (i : nat).
      replace (context_assumptions (cstr_args cdecl)) with i. subst i.
      unshelve eapply (conv_terms_subst _ _ _ _ _ _ _ _ _ wfΣ _ spu spu'); eauto.
      { rewrite -app_context_assoc. eapply weaken_wf_local; eauto.
        rewrite !subst_instance_app_ctx in wfargs.
        rewrite -app_context_assoc in wfargs.
        rewrite -(app_context_nil_l (subst_instance _ _ ,,, _)) in wfargs.
        rewrite app_context_assoc in wfargs.
        eapply (substitution_wf_local _ []) in wfargs; eauto.
        2:{ eapply subslet_inds; eauto. }
        rewrite subst_context_app /= app_context_nil_l in wfargs.
        autorewrite with len  in wfargs.
        rewrite closed_ctx_subst // in wfargs.
        rewrite /argctx.
        eapply wf_local_smash_end => //. }
      eapply spine_subst_conv; eauto.
      eapply All2_fold_subst_instance; eauto.
      eapply on_minductive_wf_params; eauto.
      2:subst i; len; rewrite /argctx; len; reflexivity.
      rewrite /expand_lets /expand_lets_k.
      rewrite !map_map_compose.
      eapply All2_map. eapply All2_refl.
      intros.
      constructor.
      rewrite /argctx /argctx' /=; len.
      rewrite !subst_extended_subst_k.
      rewrite - !subst_instance_extended_subst. len.
      eapply eq_term_upto_univ_substs; eauto. typeclasses eauto.
      eapply eq_term_upto_univ_lift.
      eapply eq_term_upto_univ_subst_instance; eauto; typeclasses eauto.
      do 2 eapply All2_map. eapply All2_refl.
      intros x'.
      eapply eq_term_upto_univ_substs. typeclasses eauto.
      eapply eq_term_upto_univ_subst_instance; eauto; typeclasses eauto.
      eapply eq_term_inds; eauto. }
  } 
Qed.

Lemma declared_projection_constructor {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ.1} :
  forall {mdecl idecl p pdecl},
  declared_projection Σ p mdecl idecl pdecl ->
  ∑ cdecl, declared_constructor Σ (p.1.1, 0) mdecl idecl cdecl.
Proof.
  intros * declp.
  set (onp := on_declared_projection declp).
  set (oib := declared_inductive_inv _ _ _ _) in *.
  clearbody onp.
  destruct oib. simpl in *. destruct onp.
  destruct ind_ctors as [|? []] eqn:cseq => //.
  destruct y as [[[? ?] ?] ?].
  destruct ind_cunivs as [|? []] eqn:cseq' => //.
  depelim onConstructors. exists c.
  split; eauto. eapply declp. simpl. now rewrite cseq.
Qed.

Lemma length_nil {A} (l : list A) : #|l| = 0 -> l = [].
Proof. destruct l => //. Qed.

Lemma assumption_context_expand_lets_ctx Γ Δ :
  assumption_context Δ ->
  assumption_context (expand_lets_ctx Γ Δ).
Proof.
  intros ass.
  rewrite /expand_lets_ctx /expand_lets_k_ctx.
  now do 2 apply assumption_context_fold.
Qed.

Lemma assumption_context_subst_context s k Γ : 
  assumption_context Γ ->
  assumption_context (subst_context s k Γ).
Proof. apply assumption_context_fold. Qed.

Lemma assumption_context_lift_context s k Γ : 
  assumption_context Γ ->
  assumption_context (lift_context s k Γ).
Proof. apply assumption_context_fold. Qed.

Hint Resolve assumption_context_fold assumption_context_expand_lets_ctx 
  smash_context_assumption_context assumption_context_nil assumption_context_subst_instance 
  assumption_context_subst_context assumption_context_lift_context : pcuic.

Lemma subst_inds_smash_params {cf:checker_flags} {Σ : global_env_ext} {mdecl ind idecl u} {wfΣ : wf Σ} :
  declared_inductive Σ ind mdecl idecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  subst_context (inds (inductive_mind ind) u (ind_bodies mdecl)) 0
    (subst_instance u (smash_context [] (PCUICEnvironment.ind_params mdecl))) =
    (subst_instance u (smash_context [] (PCUICEnvironment.ind_params mdecl))).
Proof.
  intros decli cu.
  rewrite closed_ctx_subst //.
  eapply closed_wf_local; eauto.
  rewrite subst_instance_smash /= //.
  eapply wf_local_smash_context; auto.
  now eapply on_minductive_wf_params; pcuic.
Qed.

Lemma nth_error_expand_lets Γ Δ n : 
  nth_error (expand_lets_ctx Γ Δ) n = 
  option_map (map_decl (expand_lets_k Γ (#|Δ| - S n))) (nth_error Δ n).
Proof.
  rewrite /expand_lets_ctx /expand_lets_k_ctx nth_error_subst_context; len.
  relativize (context_assumptions Γ).
  erewrite (nth_error_lift_context_eq _ (smash_context [] Γ)).
  2:len; simpl; lia.
  simpl. destruct nth_error; simpl; auto.
  f_equal.
  rewrite /expand_lets_k /subst_decl /lift_decl compose_map_decl.
  eapply map_decl_ext => t.
  now len.
Qed.


Lemma subslet_projs_smash {cf:checker_flags} (Σ : global_env_ext) i mdecl idecl :
  forall (wfΣ : wf Σ.1) 
  (Hdecl : declared_inductive Σ.1 i mdecl idecl),
  match ind_ctors idecl return Type with
  | [cdecl] => 
    on_projections mdecl (inductive_mind i) (inductive_ind i) 
     idecl (ind_indices idecl) cdecl -> 
     forall Γ t u,
     let indsubst := inds (inductive_mind i) u (ind_bodies mdecl) in
     untyped_subslet Γ
     (projs_inst i (ind_npars mdecl) (context_assumptions (cstr_args cdecl)) t)
     (lift_context 1 0 (subst_context (inds (inductive_mind i) u (ind_bodies mdecl))
        (context_assumptions (ind_params mdecl))
        (subst_instance u (expand_lets_ctx (ind_params mdecl) (smash_context [] (cstr_args cdecl))))))
  | _ => True
  end.
Proof.
  intros wfΣ Hdecl.
  destruct ind_ctors as [|cdecl []] eqn:hcdecl => //.
  intros onp. simpl. intros Γ t u. 
  destruct onp.
  assert (#|PCUICEnvironment.ind_projs idecl| >=
  PCUICEnvironment.context_assumptions (cstr_args cdecl)). lia.
  clear on_projs_all.
  induction (cstr_args cdecl) as [|[? [] ?] ?].
  - simpl. constructor.
  - simpl. apply IHc. now simpl in H.
  - simpl. rewrite smash_context_acc /=. simpl.
    rewrite /subst_decl {2}/map_decl /=.
    rewrite /expand_lets_ctx {1}/map_decl /= /expand_lets_k_ctx.
    rewrite !lift_context_snoc /= subst_context_snoc /=; len.
    rewrite !subst_context_snoc.
    rewrite lift_context_snoc.
    constructor. apply IHc. simpl in H. lia.
Qed.

Lemma skipn_lift_context (m n : nat) (k : nat) (Γ : context) :
  skipn m (lift_context n k Γ) = lift_context n k (skipn m Γ).
Proof.
  rewrite !lift_context_alt.
  rewrite skipn_mapi_rec. rewrite mapi_rec_add /mapi.
  apply mapi_rec_ext. intros.
  f_equal. rewrite List.skipn_length. lia.
Qed.

Lemma projs_inst_0 ind n k : projs_inst ind n k (tRel 0) = projs ind n k.
Proof.
  induction k in n |- * => /= //.
  simpl. now f_equal.
Qed.

From MetaCoq.PCUIC Require Import PCUICContextRelation.

Lemma projection_cumulative_indices {cf:checker_flags} {Σ : global_env_ext} (wfΣ : wf Σ.1) :
  forall {mdecl idecl p pdecl u u' },
  declared_projection Σ p mdecl idecl pdecl ->
  on_udecl_prop Σ (ind_universes mdecl) ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  consistent_instance_ext Σ (ind_universes mdecl) u' ->
  R_global_instance Σ (eq_universe Σ) (leq_universe Σ) (IndRef p.1.1) (ind_npars mdecl) u u' ->
  Σ ;;; projection_context mdecl idecl p.1.1 u |- 
    subst_instance u pdecl.2 <= subst_instance u' pdecl.2.
Proof.
  intros * declp onudecl cu cu' Ru.
  epose proof (declared_projection_constructor declp) as [cdecl declc].
  destruct (on_declared_constructor declc) as [_ [sort onc]].
  destruct declc. simpl in d.
  pose proof (declared_inductive_unique d (let (x, _) := declp in x)). subst d.
  epose proof (declared_projection_type_and_eq wfΣ declp).
  destruct (on_declared_projection declp).
  set (oib := declared_inductive_inv _ _ _ _) in *. simpl in X, y.
  destruct ind_ctors as [|? []] eqn:cstors => //.
  destruct y as [[[H onps] onidx] onproj].
  simpl in *.
  destruct ind_cunivs as [|? []] eqn:cseq => //.
  simpl in *. destruct onc as [eqs onc]. noconf e. noconf eqs.
  simpl in X.
  destruct X as [_ [idecl' [[[idecl'nth _] pty] pty']]].
  rewrite -pty.
  unfold R_global_instance in Ru.
  unfold global_variance, lookup_inductive, lookup_minductive in Ru.
  pose proof declp as declp'.
  destruct declp' as [[? ?] ?]. red in H0.
  rewrite H0 H1 in Ru.
  rewrite oib.(ind_arity_eq) in Ru.
  rewrite !destArity_it_mkProd_or_LetIn /= in Ru.
    
  destruct (context_assumptions _ <=? _) eqn:eq.
  2:{ 
    rewrite app_context_nil_l context_assumptions_app in eq.
    eapply Nat.leb_nle in eq.
    destruct onps. len in eq.
    apply length_nil in on_projs_noidx. 
    rewrite on_projs_noidx in eq. simpl in *.
    rewrite o.(onNpars) in eq. lia. }
  destruct (ind_variance mdecl) eqn:eqv.
  { simpl in Ru.
    epose proof (on_ctype_variance onc _ eqv).
    red in X.
    destruct variance_universes as [[[udecl i] i']|] eqn:vu => //.
    destruct X as [onctx _]. simpl in onctx.
    eapply (All2_fold_inst _ _ _ _ _ _ u u') in onctx; eauto.
    2:{ rewrite -eqv. 
      destruct (on_declared_projection declp).
      now apply (onVariance o). }
    rewrite subst_instance_app_ctx in onctx.
    have declc : declared_constructor Σ (p.1.1, 0) mdecl idecl cdecl.
    { split; simpl; eauto. eapply declp. now rewrite cstors. }
    epose proof (positive_cstr_closed_args declc cu).
    rewrite eqv in X; simpl in X.
    specialize (X Ru).
    rewrite - !(subst_instance_smash _ _ []) in X.
    rewrite - !(expand_lets_smash_context _ []) in X.
    apply X in onctx. clear X.
    destruct onctx as [onctx wfctx].
    eapply PCUICRedTypeIrrelevance.All2_fold_nth_ass in onctx.
    2:{ rewrite nth_error_subst_context; len.
      simpl. rewrite nth_error_map nth_error_expand_lets.
      erewrite idecl'nth. simpl. reflexivity. }
    2:pcuic.
    move:onctx => [decl' []].
    destruct idecl' as [na [b|] ty]; simpl => //.
    intros Hd [[] Hd'']; discriminate. simpl.
    rewrite nth_error_subst_context nth_error_map nth_error_expand_lets idecl'nth.
    rewrite !subst_instance_length !expand_lets_ctx_length !smash_context_length /=.
    simpl. move=> [= <-]. simpl.
    move=> [[Hd _] Hty]. 
    depelim Hty; simpl in *. rename c into Hty.
    unfold PCUICConversionPar.cumul in Hty.
    move: Hty.
    rewrite subst_instance_smash. len. simpl.
    epose proof (subslet_projs_smash _ _ _ _ wfΣ (let (x, _) := declp in x)). simpl in X.
    rewrite cstors in X.
    unfold projection_context.
    set (ind_decl := vass _ _).
    specialize (X onps (smash_context [] (subst_instance u (ind_params mdecl)) ,, ind_decl) (tRel 0) u).
    simpl in X.
    eapply untyped_subslet_skipn in X.
    rewrite skipn_lift_context in X.
    move => Hty.
    eapply (weakening_cumul _ _ _ [ind_decl]) in Hty; auto.
    simpl in Hty. len in Hty.
    eapply (substitution_untyped_cumul _ _ _ []) in Hty. 3:eapply X. 2:eauto.
    move: Hty; rewrite subst_context_nil /=.
    rewrite skipn_length. len. simpl. lia. len.
    rewrite /projection_type /=.
    fold (expand_lets_k (ind_params mdecl) p.2 ty).
    rewrite projs_inst_skipn.
    assert (context_assumptions (cstr_args cdecl) - 
      S (context_assumptions (cstr_args cdecl) - S p.2) = p.2) as -> by lia.
    clear X.
    rewrite subst_instance_subst.
    rewrite (subst_instance_subst u').
    rewrite !subst_instance_subst [subst_instance _ (projs _ _ _)]subst_instance_projs.
    rewrite - !subst_instance_subst.
    fold (expand_lets_k (ind_params mdecl) p.2 ty).
    rewrite commut_lift_subst_rec. lia.
    rewrite commut_lift_subst_rec. lia.
    rewrite distr_subst projs_subst_above. lia.
    rewrite (instantiate_inds _ u _ mdecl wfΣ (proj1 (proj1 declp)) cu).
    rewrite subst_instance_subst.
    rewrite (instantiate_inds _ u' _ mdecl wfΣ (proj1 (proj1 declp)) cu').
    rewrite subst_instance_subst.
    rewrite ![subst_instance _ (projs _ _ _)]subst_instance_projs.
    rewrite distr_subst projs_subst_above. lia.
    rewrite projs_length !Nat.add_succ_r Nat.add_0_r /= //.
    rewrite !subst_instance_lift // projs_inst_0 //.
    rewrite o.(onNpars) //. }
  { simpl in Ru.
    constructor. eapply eq_term_leq_term.
    eapply eq_term_upto_univ_subst_instance; eauto. all:typeclasses eauto.
  }
Qed.

Lemma wt_ind_app_variance {cf:checker_flags} {Σ : global_env_ext} {Γ ind u l}:
  wf Σ.1 ->
  isType Σ Γ (mkApps (tInd ind u) l) ->
  ∑ mdecl, (lookup_inductive Σ ind = Some mdecl) *
  (global_variance Σ (IndRef ind) #|l| = ind_variance (fst mdecl)).
Proof.
  move=> wfΣ.
  move => [s wat].
  red in wat. eapply inversion_mkApps in wat as [ty [Hind Hargs]]; auto.
  eapply inversion_Ind in Hind as [mdecl [idecl [wfΓ [decli [cu cum]]]]]; auto.
  eapply typing_spine_strengthen in Hargs; eauto. clear cum.
  exists (mdecl, idecl).
  assert (lookup_inductive Σ ind = Some (mdecl, idecl)).
  { destruct decli as [decli declmi].
    rewrite /lookup_inductive. red in decli. rewrite /lookup_minductive decli.
    now rewrite declmi. }
  split; auto.
  simpl. rewrite H.
  destruct (on_declared_inductive decli) as [onmi oni]; auto.
  rewrite oni.(ind_arity_eq) in Hargs |- *.
  rewrite !destArity_it_mkProd_or_LetIn. simpl.
  rewrite app_context_nil_l.
  rewrite !subst_instance_it_mkProd_or_LetIn in Hargs.
  rewrite -it_mkProd_or_LetIn_app in Hargs.
  eapply arity_typing_spine in Hargs; auto.
  destruct Hargs as [[Hl Hleq] ?]. rewrite Hl.
  len. now rewrite context_assumptions_app Nat.leb_refl.
  eapply weaken_wf_local; auto.
  rewrite -[_ ++ _]subst_instance_app_ctx.
  eapply on_minductive_wf_params_indices_inst; eauto with pcuic.
Qed.

Lemma spine_subst_app {cf:checker_flags} Σ Γ Δ Δ' inst inst' insts :
  wf Σ.1 -> 
  #|inst| = context_assumptions Δ ->
  wf_local Σ (Γ ,,, Δ ,,, Δ') ->
  spine_subst Σ Γ inst (skipn #|Δ'| insts) Δ *
  spine_subst Σ Γ inst' (firstn #|Δ'| insts) (subst_context (skipn #|Δ'| insts) 0 Δ') ->
  spine_subst Σ Γ (inst ++ inst') insts (Δ ,,, Δ').
Proof.
  intros wfΣ len wf [[wfdom wfcodom cs subst] [wfdom' wfcodom' cs' subst']].
  split; auto.
  now rewrite app_context_assoc.
  eapply context_subst_app_inv; split; auto.
  rewrite skipn_all_app_eq; try lia. auto.
  rewrite (firstn_app_left _ 0) ?Nat.add_0_r // firstn_0 // app_nil_r //.
  rewrite -(firstn_skipn #|Δ'| insts).
  eapply subslet_app; auto. 
Qed.
Lemma context_assumptions_lift {n k Γ} : context_assumptions (lift_context n k Γ) = context_assumptions Γ.
Proof. apply context_assumptions_fold. Qed.
Lemma context_assumptions_subst {n k Γ} : context_assumptions (subst_context n k Γ) = context_assumptions Γ.
Proof. apply context_assumptions_fold. Qed.
Hint Rewrite @context_assumptions_lift @context_assumptions_subst : len.

Lemma invert_cumul_ind_ind {cf} {Σ} {wfΣ : wf Σ} {Γ ind ind' u u' args args'} :
  Σ ;;; Γ |- mkApps (tInd ind u) args <= mkApps (tInd ind' u') args' ->
  (Reflect.eqb ind ind' * PCUICEquality.R_global_instance Σ (eq_universe Σ) (leq_universe Σ) (IndRef ind) #|args| u u' *
    All2 (conv Σ Γ) args args').
Proof.
  intros ht; eapply invert_cumul_ind_l in ht as (? & ? & ? & ? & ?); auto.
  eapply red_mkApps_tInd in r as (? & ? & ?); auto. solve_discr.
  noconf H. subst.
  intuition auto. eapply eq_inductive_refl.
  transitivity x1; auto. symmetry. now eapply red_terms_conv_terms.
Qed.

Lemma ctx_inst_app {cf:checker_flags} {Σ Γ} {Δ : context} {Δ' args args'} 
  (dom : ctx_inst Σ Γ args Δ) :
  ctx_inst Σ Γ args' (subst_telescope (ctx_inst_sub dom) 0 Δ') ->
  ctx_inst Σ Γ (args ++ args') (Δ ++ Δ').
Proof.
  induction dom in args', Δ' |- *; simpl.
  - now rewrite subst_telescope_empty.
  - rewrite subst_app_telescope /= ctx_inst_subst_length /= subst_telescope_length Nat.add_0_r /=.
    move/IHdom => IH.
    constructor => //.
    now rewrite subst_telescope_app Nat.add_0_r.
  - rewrite subst_app_telescope /= ctx_inst_subst_length /= subst_telescope_length Nat.add_0_r /=.
    move/IHdom => IH.
    constructor => //.
    now rewrite subst_telescope_app Nat.add_0_r.
Qed.

Lemma cumul_ctx_rel_context_assumptions {cf} {Σ} {Γ} {Δ Δ'} : 
  cumul_ctx_rel Σ Γ Δ Δ' ->
  context_assumptions Δ = context_assumptions Δ'.
Proof.
  induction 1; auto.
  depelim p; simpl; auto. lia.
Qed.

(* Lemma subslet_subs {cf} {Σ} {wfΣ : wf Σ} {Γ i Δ Δ'} :
cumul_ctx_rel Σ Γ Δ Δ' ->
ctx_inst Σ Γ i (Li *)

Lemma cumul_expand_lets {cf} {Σ} {wfΣ : wf Σ} {Γ} {Δ} {T T'} : 
  wf_local Σ (Γ ,,, Δ) ->
  Σ ;;; Γ ,,, Δ |- T <= T' ->
  Σ ;;; Γ ,,, smash_context [] Δ |- expand_lets Δ T <= expand_lets Δ T'.
Proof.
  intros wf cum.
  eapply (weakening_cumul _ _ _ (smash_context [] Δ)) in cum; tea.
  rewrite /expand_lets /expand_lets_k.
  eapply (substitution_cumul _ _ _ []) in cum; tea. len in cum; tea.
  destruct (wf_local_app_inv wf).
  simpl.
  eapply weakening_wf_local => //.
  now eapply wf_local_smash_end.
  len.
  now eapply PCUICContexts.subslet_extended_subst.
Qed.

Lemma conv_expand_lets {cf} {Σ} {wfΣ : wf Σ} {Γ} {Δ} {T T'} : 
  wf_local Σ (Γ ,,, Δ) ->
  Σ ;;; Γ ,,, Δ |- T = T' ->
  Σ ;;; Γ ,,, smash_context [] Δ |- expand_lets Δ T = expand_lets Δ T'.
Proof.
  intros wf cum.
  eapply (weakening_conv _ _ _ (smash_context [] Δ)) in cum; tea.
  rewrite /expand_lets /expand_lets_k.
  eapply (substitution_conv _ _ _ []) in cum; tea. len in cum; tea.
  destruct (wf_local_app_inv wf).
  simpl.
  eapply weakening_wf_local => //.
  now eapply wf_local_smash_end.
  len.
  now eapply PCUICContexts.subslet_extended_subst.
Qed.

Lemma cumul_context_app {cf:checker_flags} {Σ Γ Δ Δ'} :
  cumul_ctx_rel Σ Γ Δ Δ' ->
  cumul_context Σ (Γ ,,, Δ) (Γ ,,, Δ').
Proof.
  intros HΔ.
  eapply All2_fold_app.
  * apply (length_of HΔ).
  * reflexivity.
  * apply HΔ.
Qed.

Lemma conv_terms_lift {cf:checker_flags} {Σ} {wfΣ : wf Σ} {Γ Δ args args'} :
  conv_terms Σ Γ args args' ->
  conv_terms Σ (Γ ,,, Δ) (map (lift0 #|Δ|) args) (map (lift0 #|Δ|) args').
Proof.
  intros conv.
  eapply All2_map.
  eapply (All2_impl conv).
  intros x y eqxy.
  now eapply (weakening_conv _ _ []).
Qed.

Lemma subslet_cumul_ctx {cf:checker_flags} {Σ} {wfΣ : wf Σ} {Γ Γ' Δ Δ'} {s} :
  wf_local Σ (Γ ,,, Δ) ->
  wf_local Σ (Γ ,,, Δ') ->
  cumul_ctx_rel Σ Γ Δ' Δ ->
  subslet Σ (Γ ,,, Δ) s Γ' ->
  subslet Σ (Γ ,,, Δ') s Γ'.
Proof.
  intros wfl wfr cumul.
  induction 1; constructor; auto.
  * eapply context_cumulativity; tea.
    now eapply cumul_context_app.
  * eapply context_cumulativity; tea.
    now eapply cumul_context_app.
Qed.

Lemma cumul_ctx_rel_conv_extended_subst {cf:checker_flags} {Σ} {wfΣ : wf Σ} {Γ Δ Δ'} :
  wf_local Σ (Γ ,,, Δ) ->
  wf_local Σ (Γ ,,, Δ') ->
  cumul_ctx_rel Σ Γ Δ Δ' ->
  conv_terms Σ (Γ ,,, smash_context [] Δ) (extended_subst Δ 0) (extended_subst Δ' 0) ×
  cumul_ctx_rel Σ Γ (smash_context [] Δ) (smash_context [] Δ').
Proof.
  intros wfl wfr cum.
  induction cum in |- *; simpl; auto.
  - split; constructor.
  - depelim p; simpl;
    depelim wfl; depelim wfr;
    specialize (IHcum wfl wfr) as [conv cum'].
    * split; try constructor; auto.
      + rewrite smash_context_acc /=.
        rewrite !(lift_extended_subst _ 1).
        now eapply (conv_terms_lift (Δ := [_])).
      + simpl; rewrite !(smash_context_acc _ [_]) /=;
        constructor; auto.
        constructor; simpl; auto.
        eapply cumul_expand_lets in c; tea.
        etransitivity;tea. rewrite /expand_lets /expand_lets_k. simpl.
        red.
        rewrite -(length_of cum).
        rewrite -(cumul_ctx_rel_context_assumptions cum).
        move: (context_assumptions_smash_context [] Γ0); cbn => <-. simpl.
        change (Γ ,,, smash_context [] Γ0) with (Γ ,,, smash_context [] Γ0 ,,, []).
        eapply (cumul_subst_conv _ _ _ _ []); tea.
        { eapply subslet_untyped_subslet. 
          now eapply PCUICContexts.subslet_extended_subst. }
        { eapply subslet_untyped_subslet.
          eapply subslet_cumul_ctx. 3:tea.
          now eapply wf_local_smash_end.
          now eapply wf_local_smash_end.
          now eapply PCUICContexts.subslet_extended_subst. }
    * split; auto.
      constructor; auto.
      len.
      eapply conv_expand_lets in c; tea.
      etransitivity; tea. 
      rewrite /expand_lets /expand_lets_k. simpl.
      rewrite -(length_of cum).
      rewrite -(cumul_ctx_rel_context_assumptions cum).
      move: (context_assumptions_smash_context [] Γ0); cbn => <-. simpl.
      change (smash_context [] Γ0 ++ Γ) with (Γ ,,, smash_context [] Γ0 ,,, []).
      eapply (conv_subst_conv _ _ _ _ []); tea.
      { eapply subslet_untyped_subslet. 
        now eapply PCUICContexts.subslet_extended_subst. }
      { eapply subslet_untyped_subslet.
        eapply subslet_cumul_ctx. 3:tea.
        now eapply wf_local_smash_end.
        now eapply wf_local_smash_end.
        now eapply PCUICContexts.subslet_extended_subst. }
Qed.

Lemma cumul_ctx_rel_smash {cf:checker_flags} {Σ} {wfΣ : wf Σ} {Γ Δ Δ'} :
  wf_local Σ (Γ ,,, Δ) ->
  wf_local Σ (Γ ,,, Δ') ->
  cumul_ctx_rel Σ Γ Δ Δ' ->
  cumul_ctx_rel Σ Γ (smash_context [] Δ) (smash_context [] Δ').
Proof.
  now intros; apply cumul_ctx_rel_conv_extended_subst.
Qed.

Lemma conv_terms_cumul_ctx {cf:checker_flags} {Σ} {wfΣ : wf Σ} {Γ Δ Δ'} {ts ts'} :
  wf_local Σ (Γ ,,, Δ) ->
  wf_local Σ (Γ ,,, Δ') ->
  cumul_ctx_rel Σ Γ Δ Δ' ->
  conv_terms Σ (Γ ,,, Δ') ts ts' ->
  conv_terms Σ (Γ ,,, Δ) ts ts'.
Proof.
  intros wfl wfr cum conv.
  eapply (All2_impl conv).
  intros x y xy.
  eapply conv_cumul_ctx; tea.
  now eapply cumul_context_app.
Qed.

Lemma cumul_expand_lets_cumul_ctx {cf} {Σ} {wfΣ : wf Σ} {Γ} {Δ Δ'} {T T'} : 
  wf_local Σ (Γ ,,, Δ) ->
  wf_local Σ (Γ ,,, Δ') ->
  Σ ;;; Γ ,,, Δ |- T <= T' ->
  cumul_ctx_rel Σ Γ Δ Δ' ->
  Σ ;;; Γ ,,, smash_context [] Δ |- expand_lets Δ T <= expand_lets Δ' T'.
Proof.
  intros wfl wfr cum cumΓ.
  rewrite /expand_lets /expand_lets_k.
  rewrite -(length_of cumΓ).
  rewrite -(cumul_ctx_rel_context_assumptions cumΓ).
  change (Γ ,,, smash_context [] Δ) with (Γ ,,, smash_context [] Δ ,,, []).
  eapply (subst_cumul _ _ _ []); tea.
  3:{ eapply cumul_ctx_rel_conv_extended_subst; tea. }
  * eapply PCUICContexts.subslet_extended_subst; tea.
  * eapply subslet_cumul_ctx; cycle 2.
    + eapply cumul_ctx_rel_smash; tea.
    + eapply PCUICContexts.subslet_extended_subst; tea.
    + now eapply wf_local_smash_end.
    + now eapply wf_local_smash_end.
  * simpl.
    rewrite -[context_assumptions _](smash_context_length [] Δ).
    eapply weakening_wf_local; tea.
    now apply wf_local_smash_end.
  * simpl.
    rewrite -[context_assumptions _](smash_context_length [] Δ).
    now eapply weakening_cumul.
Qed.

Lemma ctx_inst_cumul {cf} {Σ} {wfΣ : wf Σ} {Γ i Δ Δ'} :
  cumul_ctx_rel Σ Γ Δ Δ' ->
  ctx_inst Σ Γ i (List.rev Δ) ->
  wf_local_rel Σ Γ Δ ->
  wf_local_rel Σ Γ Δ' ->
  ctx_inst Σ Γ i (List.rev Δ').
Proof.
  induction 1 in i |- *; intros ci. 
  - depelim ci. constructor.
  - simpl in ci. eapply PCUICSpine.ctx_inst_app in ci as [dom codom].
    depelim p.
    * simpl in codom. depelim codom.
      simpl in codom. depelim codom. simpl in t0.
      destruct i as [|i t] using rev_case. 
      { rewrite skipn_nil in H => //. }
      assert (context_assumptions (List.rev Γ0) = #|i|).
      apply (f_equal (@length _)) in H. simpl in H.
      rewrite List.skipn_length app_length /= in H. lia.
      rewrite skipn_all_app_eq // in H. noconf H.
      intros HΔ; depelim HΔ.
      intros HΔ'; depelim HΔ'.
      destruct l0 as [s Hs]. simpl.
      rewrite (ctx_inst_sub_subst dom) in t0.
      rewrite (firstn_app_left _ 0) ?firstn_0 // ?Nat.add_0_r // app_nil_r in dom.
      specialize (IHX _ dom HΔ HΔ').
      eapply (ctx_inst_app IHX).
      simpl. constructor; [|constructor].
      rewrite (ctx_inst_sub_subst IHX).
      rewrite (firstn_app_left _ 0) ?firstn_0 // ?Nat.add_0_r // app_nil_r in t0.
      simpl.
      rewrite context_assumptions_rev in H0.
      assert (context_assumptions Γ' = #|i|) by now rewrite -(cumul_ctx_rel_context_assumptions X).
      rewrite map_subst_expand_lets in t0; len=> //.
      rewrite map_subst_expand_lets; len=> //.
      unshelve epose proof (ctx_inst_spine_subst _ IHX); tea.
      now eapply typing_wf_local in Hs.
      eapply spine_subst_smash in X0; tea.
      econstructor; tea.
      + red in Hs.
        eapply typing_expand_lets in Hs.
        eapply (substitution _ _ _ (List.rev i) []) in Hs; tea.
        simpl in Hs. now rewrite subst_context_nil /= in Hs.
        exact X0.
      + unshelve epose proof (ctx_inst_spine_subst _ dom); tea.
        eapply wf_local_app; tea. now eapply typing_wf_local.
        pose proof (spine_codom_wf _ _ _ _ _ X1).
        eapply spine_subst_smash in X1; tea.
        unshelve eapply (substitution_cumul _ _ _ [] _ _ _ _ _ X1).
        simpl. eapply X1. simpl.
        eapply cumul_expand_lets_cumul_ctx; tea.
        now eapply typing_wf_local in Hs.
  * simpl in codom. depelim codom.
    simpl in codom. depelim codom. 
    assert (context_assumptions (List.rev Γ0) = #|i|).
    pose proof (ctx_inst_length _ _ _ _ dom).
    apply (f_equal (@length _)) in H. simpl in H.
    rewrite List.skipn_length /= in H.
    apply firstn_length_le_inv in H0. lia.
    rewrite H0 in H, dom. rewrite firstn_all in dom.
    intros HΔ; depelim HΔ.
    intros HΔ'; depelim HΔ'.
    destruct l as [s Hs]. simpl in l0.
    red in Hs, l0.
    specialize (IHX _ dom).
    forward IHX. apply wf_local_app_inv; pcuic.
    forward IHX. apply wf_local_app_inv; pcuic.
    simpl.
    rewrite -(app_nil_r i).
    eapply (ctx_inst_app IHX). simpl.
    rewrite (ctx_inst_sub_subst IHX) /=.
    constructor. constructor.
Qed.

(* Fixpoint smash_telescope (Γ Δ : telescope) : telescope :=
  match Δ with
  | ({| decl_body := None |} as d) :: Δ => 
    d :: smash_telescope Δ
  | {| decl_body := Some b |} :: Δ =>
    subst_telescope [b] 0 Δ *)

Lemma subst_context_rev_subst_telescope s k Γ :
  subst_context s k (List.rev Γ) = List.rev (subst_telescope s k Γ).
Proof.
  induction Γ in s, k |- *.
  - simpl; auto.
  - rewrite subst_telescope_cons /= subst_context_app IHΓ.
    reflexivity.
Qed.

Lemma ctx_inst_smash_acc {cf} {Σ} {Γ i Δ} : 
  ctx_inst Σ Γ i Δ <~> 
  ctx_inst Σ Γ i (List.rev (smash_context [] (List.rev Δ))).
Proof.
  split.
  - induction 1. 
    + constructor.
    + simpl.
      rewrite smash_context_app_ass. len.
      rewrite List.rev_app_distr /=.
      constructor. auto.
      rewrite subst_telescope_subst_context.
      rewrite -smash_context_subst /=; len.
      now rewrite subst_context_rev_subst_telescope.
    + simpl. rewrite smash_context_app_def.
      now rewrite subst_context_rev_subst_telescope.
  - induction Δ using ctx_length_ind in i |- *; simpl; auto.
    destruct d as [na [b|] ty] => /=.
    * rewrite smash_context_app_def /=.
      rewrite subst_context_rev_subst_telescope.
      intros ctxi. constructor.
      apply X => //. now rewrite subst_telescope_length //.
    * rewrite smash_context_app_ass List.rev_app_distr /=.
      intros ctxi; depelim ctxi.
      constructor => //.
      apply X. rewrite subst_telescope_length //.
      rewrite subst_telescope_subst_context in ctxi.
      rewrite -(smash_context_subst []) in ctxi.
      now rewrite subst_context_rev_subst_telescope in ctxi.
Qed.

Lemma ctx_inst_smash {cf} {Σ} {Γ i Δ} : 
  ctx_inst Σ Γ i (List.rev Δ) <~> 
  ctx_inst Σ Γ i (List.rev (smash_context [] Δ)).
Proof.
  split; intros.
  - apply (fst ctx_inst_smash_acc) in X. now rewrite List.rev_involutive in X.
  - apply (snd ctx_inst_smash_acc). now rewrite List.rev_involutive.
Qed.

Lemma ctx_inst_app_weak `{checker_flags} Σ (wfΣ : wf Σ.1) ind mdecl idecl (isdecl : declared_inductive Σ.1 ind mdecl idecl)Γ (wfΓ : wf_local Σ Γ) params args u v:
  isType Σ Γ (mkApps (tInd ind u) args) ->
  consistent_instance_ext Σ (ind_universes mdecl) v ->
  ctx_inst Σ Γ params (List.rev (subst_instance v (ind_params mdecl))) ->
  Σ ;;; Γ |- mkApps (tInd ind u) args <= mkApps (tInd ind v) (params ++ skipn (ind_npars mdecl) args) ->
  ctx_inst Σ Γ (params ++ skipn (ind_npars mdecl) args) 
    (List.rev (subst_instance v (ind_params mdecl ,,, ind_indices idecl))).
Proof.
  intros [? ty_args] ? cparams cum.
  pose proof (wt_ind_app_variance _ (x; ty_args)) as [mdecl' [idecl' gv]].
  rewrite (declared_inductive_lookup_inductive isdecl) in idecl'. noconf idecl'.
  eapply invert_type_mkApps_ind in ty_args as [ty_args ?] ; eauto.
  erewrite ind_arity_eq in ty_args.
  2: eapply PCUICInductives.oib ; eauto.

  assert (#|args| = ind_npars mdecl + context_assumptions (ind_indices idecl)).
  {
    repeat rewrite PCUICUnivSubst.subst_instance_it_mkProd_or_LetIn in ty_args.
    rewrite -it_mkProd_or_LetIn_app in ty_args.
    apply arity_typing_spine in ty_args as ((eq&_)&_) ; auto.
    2:{ apply PCUICWeakening.weaken_wf_local ; eauto.
        rewrite -/app_context -PCUICUnivSubstitution.subst_instance_app.
        eapply on_minductive_wf_params_indices_inst ; eauto.
    }
    rewrite context_assumptions_app !context_assumptions_subst_instance in eq.
    erewrite declared_minductive_ind_npars.
    2: eapply declared_inductive_minductive ; eauto.
    lia.
  }

  assert (cindices : ctx_inst Σ Γ (skipn (ind_npars mdecl) args) (subst_telescope (ctx_inst_sub cparams) 0
    (List.rev (subst_instance v (ind_indices idecl))))).
  {
    rewrite PCUICUnivSubst.subst_instance_it_mkProd_or_LetIn in ty_args.
    erewrite <- (firstn_skipn _ args) in ty_args.
    apply typing_spine_ctx_inst in ty_args as (cparargs&?&ty_indices) ; auto.
    2:{ rewrite firstn_length_le.
        2:{ rewrite context_assumptions_subst_instance.
            symmetry.
            eapply PCUICDeclarationTyping.onNpars.
            eapply on_declared_inductive ; eauto.
        }
        lia.
    }
    2:{ rewrite <- PCUICUnivSubst.subst_instance_it_mkProd_or_LetIn.
        erewrite <- ind_arity_eq.
        2: eapply PCUICInductives.oib ; eauto.
        eapply declared_inductive_valid_type ; eauto.
    }

    pose proof (declared_minductive_ind_npars isdecl).
    eapply invert_cumul_ind_ind in cum as [[_ Ruv] conv].
    rewrite -{1}(firstn_skipn (ind_npars mdecl) args) in conv.
    eapply All2_app_inv in conv as [convpars _].
    2:{ apply ctx_inst_length in cparams.
        rewrite context_assumptions_rev in cparams. len in cparams.
        rewrite List.firstn_length. lia. }
    unshelve epose proof (inductive_cumulative_indices _ isdecl _ c H0 Ruv Γ).
    { eapply (weaken_lookup_on_global_env' _ _ (InductiveDecl mdecl) _ (proj1 isdecl)). }
    specialize (X (firstn (ind_npars mdecl) args) params).
    unshelve epose proof (ctx_inst_spine_subst _ cparams); tea.
    { eapply weaken_wf_local; tea. eapply (on_minductive_wf_params isdecl); tea. }
    unshelve epose proof (ctx_inst_spine_subst _ cparargs); tea.
    { eapply weaken_wf_local; tea. eapply (on_minductive_wf_params isdecl); tea. }
    specialize (X _ _ X1 X0 convpars). simpl in X.
    rewrite subst_telescope_subst_context.
    eapply ctx_inst_smash.
    rewrite subst_instance_it_mkProd_or_LetIn in ty_indices.
    rewrite subst_it_mkProd_or_LetIn in ty_indices.
    rewrite -(app_nil_r (skipn (ind_npars mdecl) args)) in ty_indices.
    eapply typing_spine_ctx_inst in ty_indices as [argsi [isty sp]]; tea.
    - eapply ctx_inst_cumul; tea.
      apply (ctx_inst_smash.1 argsi).
      { apply wf_local_app_inv. apply wf_local_smash_end; tea.
        eapply substitution_wf_local; tea. eapply X1.
        rewrite -app_context_assoc -subst_instance_app_ctx.
        eapply weaken_wf_local; tea.
        eapply (on_minductive_wf_params_indices_inst isdecl _ c). }
      { apply wf_local_app_inv. apply wf_local_smash_end; tea.
        eapply substitution_wf_local; tea. eapply X0.
        rewrite -app_context_assoc -subst_instance_app_ctx.
        eapply weaken_wf_local; tea.
        eapply (on_minductive_wf_params_indices_inst isdecl _ H0). }
    - len. rewrite List.skipn_length. lia.
    - simpl. now rewrite subst_instance_it_mkProd_or_LetIn subst_it_mkProd_or_LetIn in i.
  }

  rewrite subst_instance_app_ctx List.rev_app_distr.
  now eapply (ctx_inst_app cparams).
Qed.

Lemma wf_local_vass {cf:checker_flags} Σ {Γ na A} s :
  Σ ;;; Γ |- A : tSort s -> wf_local Σ (Γ ,, vass na A).
Proof.
  intro X; apply typing_wf_local in X as Y.
  constructor; tea. eexists; eassumption.
Qed.

Lemma isType_it_mkProd_or_LetIn {cf:checker_flags} {Σ Γ Δ T} : 
  wf Σ.1 ->
  isType Σ (Γ ,,, Δ) T ->
  isType Σ Γ (it_mkProd_or_LetIn Δ T).
Proof.
  intros wfΣ. revert T.
  induction Δ as [|[na [b|] ty] Δ].
  - now simpl.
  - intros T [s Hs].
    rewrite /= /mkProd_or_LetIn /=.
    eapply IHΔ.
    red in Hs.
    exists s.
    have wf := typing_wf_local Hs.
    depelim wf.
    unfold PCUICTypingDef.typing.
    destruct l as [s1 Hs1]. red in l0.
    eapply type_Cumul'.
    econstructor; eauto. eapply isType_Sort; eauto.
    now eapply PCUICWfUniverses.typing_wf_universe in Hs.
    eapply red_cumul. repeat constructor.
  - intros T [s Hs].
    apply IHΔ.
    red.
    unfold PCUICTypingDef.typing in *.
    have wf := typing_wf_local Hs.
    depelim wf.
    destruct l as [s1 Hs1].
    exists (Universe.sort_of_product s1 s).
    econstructor; eauto.
Qed.

Lemma WfArity_build_case_predicate_type {cf:checker_flags} Σ
      Γ ind u args mdecl idecl p ps :
  wf Σ.1 ->
  declared_inductive Σ.1 ind mdecl idecl ->
  isType Σ Γ (mkApps (tInd ind u) args) ->
  let params := firstn (ind_npars mdecl) args in
  wf_universe Σ ps ->
  isWfArity Σ Γ (it_mkProd_or_LetIn (case_predicate_context ind mdecl idecl p) (tSort ps)).  
Proof.
  todo "case".
(*  
  intros wfΣ isdecl X params wfps XX. unfold build_case_predicate_type in XX.
  case_eq (instantiate_params
             (subst_instance u (ind_params mdecl))
             params (subst_instance u (ind_type idecl)));
    [|intro e; rewrite e in XX; discriminate].
  intros ipars Hipars; rewrite Hipars in XX. cbn -[it_mkProd_or_LetIn] in XX.
  case_eq (destArity [] ipars);
    [|intro e; rewrite e in XX; discriminate].
  intros [ictx iu] Hictxs; rewrite Hictxs in XX; apply some_inj in XX.
  subst pty. cbn -[it_mkProd_or_LetIn].
  split.
  2:{ eexists _, _. rewrite destArity_it_mkProd_or_LetIn. reflexivity. }
  eapply isType_it_mkProd_or_LetIn; eauto.
  eapply isType_Sort; auto.
  simpl. eapply wf_local_vass.
  assert (wfΓ : wf_local Σ Γ). { destruct X as [s Hs]; pcuic. }
  move:Hipars.
  rewrite instantiate_params_.
  destruct instantiate_params_subst as [[parsubst ty]|] eqn:ip => // => [= eqip].
  subst ipars.
  pose proof (PCUICWeakeningEnv.on_declared_inductive wfΣ as isdecl) [onind oib].
  rewrite oib.(ind_arity_eq) in ip.
  eapply PCUICSubstitution.instantiate_params_subst_make_context_subst in ip as 
    [ctx' [mparsubst dp]].
  rewrite subst_instance_it_mkProd_or_LetIn in dp.
  rewrite List.rev_length in dp.
  rewrite decompose_prod_n_assum_it_mkProd in dp. noconf dp.
  rewrite subst_instance_it_mkProd_or_LetIn PCUICSubstitution.subst_it_mkProd_or_LetIn in Hictxs.
  rewrite destArity_it_mkProd_or_LetIn /= app_context_nil_l in Hictxs. noconf Hictxs.
  destruct X as [s Hs].
  eapply invert_type_mkApps_ind in Hs as [spargs cu]; eauto.
  rewrite oib.(ind_arity_eq) in spargs.
  rewrite !subst_instance_it_mkProd_or_LetIn in spargs.
  rewrite -it_mkProd_or_LetIn_app in spargs.
  eapply arity_typing_spine in spargs as [[lenargs leqs] [instsubst spsubst]]; auto.
  2:{ eapply weaken_wf_local; pcuic. rewrite -[_ ++ _]subst_instance_app_ctx.
      eapply on_minductive_wf_params_indices_inst; eauto. }
  have onp := onind.(onNpars). len in lenargs.
  eapply make_context_subst_spec in mparsubst. rewrite List.rev_involutive in mparsubst.
  rewrite -(firstn_skipn (ind_npars mdecl) args) in spsubst.
  eapply spine_subst_app_inv in spsubst as [sppars spargs]; auto.
  2:{ len. rewrite firstn_length_le; lia. }
  pose proof (PCUICContexts.context_subst_fun mparsubst sppars). subst parsubst.
  len in sppars; len in spargs. len.
  set (parsubst := skipn #|ind_indices idecl| instsubst) in *.
  eapply type_mkApps; eauto.
  * econstructor; eauto. len.
    eapply spargs.
  * rewrite oib.(ind_arity_eq). cbn. instantiate (1 := iu). len.
    rewrite -it_mkProd_or_LetIn_app.
    rewrite subst_instance_it_mkProd_or_LetIn.
    eapply typing_spine_it_mkProd_or_LetIn_close'; eauto.
    rewrite subst_instance_app_ctx.
    eapply (spine_subst_weakening _ _ _ _ _ (subst_context _ 0 (subst_instance u (ind_indices idecl)))) in sppars; eauto.
    len in sppars.
    2:{ eapply spargs. }
    eapply spine_subst_app; eauto. 3:split.
    + rewrite /params; len. rewrite firstn_length_le; lia.
    + rewrite -app_context_assoc.
      eapply weaken_wf_local; eauto. len in spargs. eapply spargs.
      rewrite -subst_instance_app_ctx.
      eapply on_minductive_wf_params_indices_inst; eauto.
    + len. rewrite map_skipn in sppars.
      rewrite closed_ctx_lift in sppars.
      eapply PCUICClosed.closed_wf_local; eauto.
      eapply on_minductive_wf_params; pcuic. eapply isdecl.
      instantiate (1 := all_rels (subst_context parsubst 0 (subst_instance u (ind_indices idecl))) 0 
        #|_| ++
         map (lift0 #|ind_indices idecl|) (skipn #|ind_indices idecl| instsubst)).
      rewrite skipn_all_app_eq; len => //.
      rewrite map_skipn. eapply sppars.
    + rewrite firstn_app; len. rewrite Nat.sub_diag [firstn 0 _]firstn_0 /= // app_nil_r.
      rewrite -> firstn_all2 by (len; lia).
      rewrite skipn_all_app_eq; len => //.
      relativize (subst_context (map _ _) _ _).
      eapply spine_subst_to_extended_list_k; eauto.
      eapply spargs.
      len. rewrite subst_map_lift_lift_context.
      fold parsubst. move: (context_subst_length sppars); len => <-.
      epose proof (on_minductive_wf_params_indices_inst _ _ _ _ _ wfΣ (proj1 isdecl) oib cu).
      eapply PCUICClosed.closed_wf_local in X; auto. move: X.
      now rewrite subst_instance_app_ctx PCUICClosed.closedn_ctx_app /=; len => /andb_and [_ H].
      rewrite lift_context_subst_context //.
    + eapply isType_weakening; eauto.
      eapply spargs.
      move: (f_equal (subst_instance u) oib.(ind_arity_eq)).
      rewrite -it_mkProd_or_LetIn_app subst_instance_it_mkProd_or_LetIn => <-.
      eapply declared_inductive_valid_type; eauto.*)
Qed.

(*
Lemma leb_elim_prop_sort shapes f n cs : 
  allowed_eliminations_subset f (elim_sort_prop_ind shapes) ->
  nth_error shapes n = Some cs ->
  allowed_eliminations_subset f (if is_propositional cs.(cdecl_sort) then IntoAny else IntoPropSProp).
Proof.
  destruct shapes as [|? []]; simpl.
  - rewrite nth_error_nil => //.
  - destruct n => // /= leb. simpl. now intros [= ->].
    simpl. rewrite nth_error_nil //.
  - destruct f => //.
    destruct is_propositional => //.
Qed.
*)

Lemma arity_spine_eq {cf:checker_flags} {Σ Γ T T'} : T = T' -> arity_spine Σ Γ T [] T'.
Proof.
  intros ->; constructor.
Qed.

Lemma build_branches_type_wt {cf : checker_flags}	{Σ : global_env_ext} {wfΣ : wf Σ}
  {Γ ind mdecl idecl ci p c} (pty : term) ps (args : list term) brs :
  Σ ;;; Γ |- c : mkApps (tInd ci.(ci_ind) p.(puinst)) args ->
  let predctx := case_predicate_context ind mdecl idecl p in
  Σ;;; Γ ,,, predctx |- p.(preturn) : tSort ps ->
  is_allowed_elimination (global_ext_constraints Σ) ps (ind_kelim idecl) ->
  let ptm := it_mkLambda_or_LetIn predctx p.(preturn) in
  All2i (fun i cdecl br => 
    let brctxty := case_branch_type ci.(ci_ind) mdecl idecl p br ptm i cdecl in
    isType Σ (Γ ,,, brctxty.1) brctxty.2) 
    0 (ind_ctors idecl) brs.
Proof.
  todo "case".
(*
  intros wfΣ decli Hc da bc Hp lebs Hb.
  eapply forall_nth_error_All.
  intros n [narg brty] nth.
  eapply nth_branches_type in Hb as [br [Hbth Hbr]]; eauto.
  simpl.
  assert (declared_constructor Σ.1 (ind, n) mdecl idecl br).
  split; eauto.
  destruct (on_declared_constructor wfΣ H) as [[onind oib] [cs [nthc onc]]].
  clear oib. set (oib := declared_inductive_inv _ _ _ _) in *.
  eapply branch_type_spec in Hbr; eauto.
  unshelve eapply build_case_predicate_type_spec in bc. 2:eauto.
  destruct bc as [parsubst [csub ptyeq]].
  destruct Hbr as [hnarg Hbr].
  specialize (Hbr _ csub).
  simpl in Hbr. subst brty.
  move: (destArity_spec [] pty). rewrite da.
  simpl. intros ->. clear nth.
  eapply (f_equal (destArity [])) in ptyeq.
  rewrite !destArity_it_mkProd_or_LetIn /= in ptyeq. noconf ptyeq.
  rewrite !app_context_nil_l in H0. subst pctx.
  eapply PCUICValidity.validity in Hc; eauto.
  destruct Hc as [s Hs].
  eapply invert_type_mkApps_ind in Hs as [spargs cu]; eauto.
  rewrite oib.(ind_arity_eq) in spargs.
  rewrite !subst_instance_it_mkProd_or_LetIn in spargs.
  rewrite -it_mkProd_or_LetIn_app in spargs.
  eapply arity_typing_spine in spargs as [[lenargs leqs] [instsubst spsubst]]; auto.
  2:{ eapply weaken_wf_local; pcuic. rewrite -[_ ++ _]subst_instance_app_ctx.
      eapply on_minductive_wf_params_indices_inst; eauto. }
  epose proof onind.(onNpars) as npars.
  rewrite -(firstn_skipn (ind_npars mdecl) args) in spsubst.
  len in lenargs.
  eapply spine_subst_app_inv in spsubst; auto.
  2:{ len. rewrite firstn_length_le. lia. lia. }
  len in spsubst. destruct spsubst as [sppars spargs].
  destruct (on_constructor_inst _ wfΣ decli onind _ onc cu) as [wf _].
  assert (wfps : wf_universe Σ ps).
  { eapply validity in Hp; auto.
    eapply PCUICWfUniverses.isType_wf_universes in Hp.
    rewrite PCUICWfUniverses.wf_universes_it_mkProd_or_LetIn in Hp.
    move/andb_and: Hp => [_ Hp].
    now apply (ssrbool.elimT PCUICWfUniverses.wf_universe_reflect) in Hp. auto. }
  rewrite !subst_instance_app_ctx in wf.
  assert (sorts_local_ctx (lift_typing typing) Σ Γ
  (subst_context parsubst 0
        (subst_context
           (inds (inductive_mind ind) u (PCUICEnvironment.ind_bodies mdecl))
           #|ind_params mdecl|
           (map_context (subst_instance u)
              (cstr_args cdecl))))
  (List.map (subst_instance_univ u) (cdecl_sorts cs))).
  { pose proof (onc.(on_cargs)).
    eapply sorts_local_ctx_instantiate in X; eauto.
    rewrite subst_instance_app_ctx in X.
    rewrite -(app_context_nil_l (_ ,,, _)) app_context_assoc in X.
    eapply (subst_sorts_local_ctx) in X; simpl in *; eauto.
    3:{ eapply subslet_inds; eauto. }
    2:{ rewrite app_context_nil_l.
        now eapply All_local_env_app_inv in wf as [? ?]. }
    simpl in X. len in X.
    eapply weaken_sorts_local_ctx in X. 2:eauto. 2:eapply typing_wf_local; eauto.
    rewrite app_context_nil_l in X.
    rewrite closed_ctx_subst in X.
    eapply closed_wf_local; eauto.
    eapply on_minductive_wf_params; pcuic.
    eapply decli.
    eapply (subst_sorts_local_ctx _ _ []) in X; simpl in *; eauto.
    eapply weaken_wf_local; pcuic.
    eapply on_minductive_wf_params; pcuic. eapply decli.
    rewrite (context_subst_fun csub sppars).
    eapply sppars. }
  eexists.
  set (binder := vass _ _) in *.
  (* assert (wfcs : wf_universe Σ (subst_instance u (cdecl_sort cs))).
  { eapply type_local_ctx_wf in X; pcuic. } *)
  eapply type_it_mkProd_or_LetIn_sorts. eauto. eapply X.
  eapply sorts_local_ctx_wf_local in X.
  eapply type_mkApps.
  relativize #|cstr_args cdecl|.
  eapply weakening; eauto. now len.
  len. rewrite lift_it_mkProd_or_LetIn /=.
  epose proof (on_constructor_inst_pars_indices wfΣ decli onind _ onc cu sppars) as 
  [wfparspargs [instps spinst]].
  pose proof (context_subst_fun csub sppars); subst parsubst.
  set (parsubst := skipn #|ind_indices idecl| instsubst) in *.
  eapply wf_arity_spine_typing_spine; eauto.
  assert(wf_local Σ
  (Γ ,,,
   subst_context (skipn #|ind_indices idecl| instsubst) 0
     (subst_context
        (inds (inductive_mind ind) u (PCUICEnvironment.ind_bodies mdecl))
        #|PCUICEnvironment.ind_params mdecl|
        (PCUICEnvironment.map_context (subst_instance u)
           (cstr_args cdecl))) ,,,
   lift_context #|cstr_args cdecl| 0
     (subst_context (skipn #|ind_indices idecl| instsubst) 0
        (subst_instance u (ind_indices idecl))) ,,,
   [lift_decl #|cstr_args cdecl| #|ind_indices idecl| binder])).
  { constructor. 
    relativize #|cstr_args cdecl|.
    eapply weakening_wf_local; eauto. eapply spargs. now len.
    red. set (sort := subst_instance_univ u (ind_sort oib)). exists sort.
    simpl.
    change (tSort sort) with (lift #|cstr_args cdecl| #|ind_indices idecl| (tSort sort)).
    change (skipn #|ind_indices idecl| instsubst) with parsubst.
    relativize #|cstr_args cdecl|. 
    change #|ind_indices _| with #|ind_indices idecl|.
    relativize #|ind_indices idecl|.
    eapply weakening_typing; eauto. all:len => //.
    eapply type_mkApps.
    econstructor; eauto. eapply spargs.
    rewrite oib.(ind_arity_eq) !subst_instance_it_mkProd_or_LetIn -it_mkProd_or_LetIn_app.
    eapply typing_spine_it_mkProd_or_LetIn_close'; eauto.
    2:{ rewrite -[_ ++ _]subst_instance_app_ctx -subst_instance_it_mkProd_or_LetIn
          it_mkProd_or_LetIn_app.
        rewrite -oib.(ind_arity_eq). eapply declared_inductive_valid_type; eauto.
        eapply spargs. }
    eapply spine_subst_app; eauto. len.
    rewrite firstn_length_le; lia.
    rewrite -app_context_assoc.
    eapply weaken_wf_local; eauto. eapply spargs.
    rewrite -subst_instance_app_ctx; eapply on_minductive_wf_params_indices_inst; eauto.
    len. split.
    * eapply (spine_subst_weakening _ _ _ _ _ (subst_context _ 0 (subst_instance u (ind_indices idecl)))) in sppars; eauto.
      len in sppars. 2:{ eapply spargs. }
      len. rewrite map_skipn in sppars.
      rewrite closed_ctx_lift in sppars.
      eapply PCUICClosed.closed_wf_local; eauto.
      eapply on_minductive_wf_params; pcuic. eapply decli.
      instantiate (1 := all_rels (subst_context parsubst 0 (subst_instance u (ind_indices idecl))) 0 
        #|_| ++
         map (lift0 #|ind_indices idecl|) (skipn #|ind_indices idecl| instsubst)).
      rewrite skipn_all_app_eq; len => //.
      rewrite map_skipn. eapply sppars.
    * rewrite firstn_app; len. rewrite Nat.sub_diag [firstn 0 _]firstn_0 /= // app_nil_r.
      rewrite -> firstn_all2 by (len; lia).
      rewrite skipn_all_app_eq; len => //.
      relativize (subst_context (map _ _) _ _).
      rewrite /to_extended_list -(PCUICSubstitution.map_subst_instance_to_extended_list_k u).
      rewrite -(to_extended_list_k_subst parsubst 0).
      eapply spine_subst_to_extended_list_k; eauto.
      eapply spargs.
      len. rewrite subst_map_lift_lift_context.
      fold parsubst. move: (context_subst_length sppars); len => <-.
      epose proof (on_minductive_wf_params_indices_inst _ _ _ _ _ wfΣ (proj1 decli) oib cu).
      eapply PCUICClosed.closed_wf_local in X0; auto. move: X0.
      now rewrite subst_instance_app_ctx PCUICClosed.closedn_ctx_app /=; len => /andb_and [_ ?].
      rewrite lift_context_subst_context //. }
  split.
  { eapply isType_it_mkProd_or_LetIn; eauto.
    eapply isType_Sort; eauto.
    subst binder. rewrite lift_context_snoc. simpl. len. exact X0. }
  eapply (arity_spine_it_mkProd_or_LetIn_Sort _ _ _ _ _ ([_] ++ instps)); eauto.
  rewrite lift_context_snoc /=. len.
  eapply (spine_subst_app _ _ _ [_]); len; auto.
  move: (context_subst_length2 spinst). now len.
  simpl; split.
  2:{ 
    rewrite /lift_decl /map_decl; simpl. unfold subst_context at 5.
    rewrite /fold_context_k /= /map_decl /=.
    constructor; auto. constructor; auto.
    red. simpl. rewrite lift_mkApps subst_mkApps /=.
    rewrite skipn_S skipn_0.
    depelim X0. red in l. simpl in l.
    destruct l as [s' Hs]. exists s'.
    eapply (substitution _ _ _ instps []) in Hs; eauto.
    2:eapply spinst.
    now rewrite lift_mkApps subst_mkApps /= in Hs.
    eapply (context_subst_ass [] [] []). constructor.
    repeat constructor.
    rewrite subst_empty skipn_S skipn_0.
    rewrite lift_mkApps subst_mkApps !map_app /=.
    assert (eqpars : map (subst0 instps)
    (map (lift #|cstr_args cdecl| #|ind_indices idecl|)
       (map (lift0 #|ind_indices idecl|) (firstn (ind_npars mdecl) args))) = 
       map (lift0 #|cstr_args cdecl|) (firstn (ind_npars mdecl) args)).    
    { rewrite (map_map_compose _ _ _ _ (lift _ _)).
      rewrite -simpl_map_lift /=.
      rewrite -(map_map_compose _ _ _ _ (lift _ _)).
      rewrite map_map_compose.
      change #|ind_indices _| with #|ind_indices idecl|.
      relativize #|ind_indices idecl|.
      rewrite -> map_subst_lift_id.
      2:{ rewrite -(context_subst_length spinst). now len. }
      reflexivity. }
    rewrite eqpars.
    eapply type_mkApps. econstructor; eauto.
    eapply wf_arity_spine_typing_spine; eauto.
    split.
    apply (declared_constructor_valid_ty _ _ _ _ _ _ _ _ wfΣ (spinst.(spine_dom_wf _ _ _ _ _)) H cu).
    pose proof onc.(cstr_eq). unfold cstr_type in H0.
    unfold type_of_constructor; rewrite {}H0.
    rewrite !subst_instance_it_mkProd_or_LetIn !subst_it_mkProd_or_LetIn.
    rewrite -it_mkProd_or_LetIn_app. len.
    rewrite -(app_nil_r (map _ _ ++ _)).
    eapply arity_spine_it_mkProd_or_LetIn; eauto.
    eapply spine_subst_app; eauto. len. rewrite firstn_length_le; lia.
    { rewrite -app_context_assoc. eapply weaken_wf_local; eauto.
      rewrite closed_ctx_subst. eapply closed_wf_local; eauto. eapply on_minductive_wf_params; eauto.
      apply wfparspargs. }
    split. len.
    rewrite (closed_ctx_subst  _ _ (subst_instance _ _)).
    eapply closed_wf_local; eauto. eapply on_minductive_wf_params; eauto.
    instantiate (1 := all_rels _ _ _ ++ (map (lift0 #|cstr_args cdecl|) (skipn #|ind_indices idecl| instsubst))).
    rewrite -(closed_ctx_lift #|cstr_args cdecl| 0 (subst_instance _ _)).
    eapply closed_wf_local; eauto. eapply on_minductive_wf_params; eauto.
    rewrite skipn_all_app_eq. all:cycle 1.
    relativize #|cstr_args cdecl|.
    eapply spine_subst_weakening; eauto. len. reflexivity.
    simpl. len.
    rewrite (firstn_app_left _ 0) // ?firstn_0 //. all:cycle 1.
    rewrite app_nil_r.
    rewrite skipn_all_app_eq. all:cycle 1.
    relativize (subst_context (map (lift0 _) _) 0 _).
    eapply spine_subst_to_extended_list_k; eauto. len.
    { rewrite subst_map_lift_lift_context. 
      rewrite -(context_subst_length sppars). len.
      eapply (closedn_ctx_subst 0). len. simpl.
      2:eapply declared_minductive_closed_inds; eauto.
      eapply closed_wf_local in wf; eauto. move: wf.
      now rewrite !closedn_ctx_app /=; len => /andb_and [_ ?].
      now rewrite lift_context_subst_context. } 
    len.
    rewrite (subst_cstr_concl_head ind u mdecl (cstr_args cdecl) _ _).
    destruct decli. now eapply nth_error_Some_length in H1.
    rewrite subst_mkApps /= map_app.
    eapply arity_spine_conv.
    { depelim X0.
      destruct l as [s' Hs]. exists s'. red.
      simpl in Hs.
      eapply (substitution _ _ _ _ []) in Hs; eauto.
      2:{ eapply spinst. }
      simpl in Hs. rewrite lift_mkApps subst_mkApps !map_app /= in Hs.
      move: Hs. now rewrite eqpars. }
    eapply conv_cumul. eapply mkApps_conv_args; eauto.
    eapply All2_app.
    * rewrite map_subst_app_to_extended_list_k. now len.
      eapply spine_subst_weakening in sppars. all:auto.
      2:{ eapply X. }
      len in sppars.
      move: (spine_subst_subst_to_extended_list_k sppars).
      rewrite to_extended_list_k_fold_context_k.
      rewrite PCUICSubstitution.map_subst_instance_to_extended_list_k => ->.
      eapply All2_refl. intros; reflexivity.
    * epose proof (to_extended_list_map_lift _ 0 _). rewrite Nat.add_0_r in H0.
      
      move: (context_subst_length spinst). len => hlen.
      rewrite <- H0.
      move: (spine_subst_subst_to_extended_list_k spinst).
      rewrite !to_extended_list_k_fold_context_k PCUICSubstitution.map_subst_instance_to_extended_list_k.
      move=> ->.
      set (argctx := cstr_args cdecl) in *.
      change (skipn #|ind_indices idecl| instsubst) with parsubst in spinst, X0 |- *.
      assert (All (fun x => closedn (#|parsubst| + #|argctx|) x) (map
      (subst (inds (inductive_mind ind) u (PCUICAst.ind_bodies mdecl))
         (#|cstr_args cdecl| + #|ind_params mdecl|)
       ∘ subst_instance u) (cstr_indices cs))).
      { pose proof (positive_cstr_closed_indices wfΣ onc).
        eapply All_map.
        eapply All_map_inv in X1.
        eapply (All_impl X1) => x' cl.
        eapply (closedn_expand_lets 0) in cl.
        rewrite subst_closedn closedn_subst_instance.
        now len in cl. rewrite /parsubst.
        rewrite -(context_subst_length sppars).
        autorewrite with len. now rewrite Nat.add_comm; len in cl. }  
      eapply All2_map. rewrite !map_map_compose. 
      apply (All_All2 X1).
      intros x cl.
      rewrite subst_app_simpl. len.
      epose proof (all_rels_subst Σ _ _ (subst parsubst #|argctx| x) wfΣ (spine_dom_wf _ _ _ _ _ spinst)).
      len in X1.
      etransitivity.
      2:symmetry; eapply red_conv; eauto.
      len.
      assert(subst (map (lift0 #|argctx|) parsubst) #|cstr_args cdecl| x =
      (lift #|argctx| #|argctx| (subst parsubst #|argctx| x))) as <-.
      { epose proof (distr_lift_subst_rec _ _ #|argctx| #|argctx| 0) as l.
        rewrite Nat.add_0_r in l. rewrite -> l. f_equal.
        rewrite lift_closed. eapply closed_upwards; eauto.
        rewrite /argctx.
        lia. reflexivity. }
      symmetry. now simpl.
    * now len.
    * now len.
    * now len. 
    }
    rewrite skipn_S skipn_0.
    now rewrite !map_map_compose in spinst. pcuic. *)
Qed.
