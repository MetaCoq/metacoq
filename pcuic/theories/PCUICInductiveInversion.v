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

Ltac len := autorewrite with len.
Hint Rewrite reln_length : len.


Lemma consistent_instance_ext_noprop {cf:checker_flags} {Σ univs u} : 
  consistent_instance_ext Σ univs u ->
  forallb (fun x1 : Level.t => negb (Level.is_prop x1)) u.
Proof.
  unfold consistent_instance_ext, consistent_instance.
  destruct univs. destruct u; simpl; try discriminate; auto.
  firstorder.
Qed.

Hint Resolve consistent_instance_ext_noprop : pcuic.

(* TODO Move *)
Definition expand_lets_k Γ k t := 
  (subst (extended_subst Γ 0) k (lift (context_assumptions Γ) (k + #|Γ|) t)).

Definition expand_lets Γ t := expand_lets_k Γ 0 t.

Definition expand_lets_k_ctx Γ k Δ := 
  (subst_context (extended_subst Γ 0) k (lift_context (context_assumptions Γ) (k + #|Γ|) Δ)).

Definition expand_lets_ctx Γ Δ := expand_lets_k_ctx Γ 0 Δ.

Lemma subst_consn_ids_ren n k f : (idsn n ⋅n (tRel k ⋅ ren f) =1 ren (ren_ids n ⋅n (subst_cons_gen k f)))%sigma.
Proof.
  intros i.
  destruct (Nat.leb_spec n i).
  - rewrite subst_consn_ge idsn_length. auto.
    unfold ren. f_equal. rewrite subst_consn_ge ren_ids_length; auto.
    unfold subst_cons_gen. destruct (i - n) eqn:eqin. simpl. auto. simpl. reflexivity.
  - assert (Hr:i < #|ren_ids n|) by (rewrite ren_ids_length; lia).
    assert (Hi:i < #|idsn n|) by (rewrite idsn_length; lia).
    destruct (subst_consn_lt Hi) as [x' [Hnth He]].
    destruct (subst_consn_lt Hr) as [x'' [Hnth' He']].
    rewrite (idsn_lt H) in Hnth.
    rewrite (ren_ids_lt H) in Hnth'.
    injection Hnth as <-. injection Hnth' as <-. rewrite He.
    unfold ren. now rewrite He'.
Qed.

Lemma subst_reli_lift_id i n t : i <= n ->
  subst [tRel i] n (lift (S i) (S n) t) = (lift i n t).
Proof.
  intros ltin.
  sigma.
  apply inst_ext.
  unfold Upn. sigma. unfold shiftk at 1 => /=.
  simpl.
  rewrite ren_shiftk. rewrite subst_consn_ids_ren.
  unfold lift_renaming. rewrite compose_ren.
  intros i'. unfold ren, ids; simpl. f_equal.
  elim: Nat.leb_spec => H'. unfold subst_consn, subst_cons_gen.
  elim: nth_error_spec => [i'' e l|].
  rewrite ren_ids_length /= in l. lia.
  rewrite ren_ids_length /=.
  intros Hn. destruct (S (i + i') - n) eqn:?. lia.
  elim: (Nat.leb_spec n i'). lia. lia.
  unfold subst_consn, subst_cons_gen.
  elim: nth_error_spec => [i'' e l|].
  rewrite (@ren_ids_lt n i') in e. rewrite ren_ids_length in l. auto.
  noconf e. rewrite ren_ids_length in l. 
  elim: Nat.leb_spec; try lia.
  rewrite ren_ids_length /=.
  intros. destruct (i' - n) eqn:?; try lia.
  elim: Nat.leb_spec; try lia.
Qed.

Lemma expand_lets_k_vass Γ na ty k t : 
  expand_lets_k (Γ ++ [{| decl_name := na; decl_body := None; decl_type := ty |}]) k t =
  expand_lets_k Γ k t.
Proof.
  rewrite /expand_lets /expand_lets_k; len.
  rewrite extended_subst_app /=.
  rewrite subst_app_simpl. simpl. len.
  rewrite !Nat.add_1_r.
  rewrite subst_context_lift_id. f_equal.
  rewrite Nat.add_succ_r.
  rewrite subst_reli_lift_id //.
  move: (context_assumptions_length_bound Γ); lia.
Qed.

Lemma expand_lets_vass Γ na ty t : 
  expand_lets (Γ ++ [{| decl_name := na; decl_body := None; decl_type := ty |}]) t =
  expand_lets Γ t.
Proof.
  rewrite /expand_lets; apply expand_lets_k_vass.
Qed.

Lemma expand_lets_k_vdef Γ na b ty k t : 
  expand_lets_k (Γ ++ [{| decl_name := na; decl_body := Some b; decl_type := ty |}]) k t =
  expand_lets_k (subst_context [b] 0 Γ) k (subst [b] (k + #|Γ|) t).
Proof.
  rewrite /expand_lets /expand_lets_k; len.
  rewrite extended_subst_app /=.
  rewrite subst_app_simpl. simpl. len.
  rewrite !subst_empty lift0_id lift0_context.
  epose proof (distr_lift_subst_rec _ [b] (context_assumptions Γ) (k + #|Γ|) 0).
  rewrite !Nat.add_0_r in H.
  f_equal. simpl in H. rewrite Nat.add_assoc.
  rewrite <- H.
  reflexivity.
Qed.

Lemma expand_lets_vdef Γ na b ty t : 
  expand_lets (Γ ++ [{| decl_name := na; decl_body := Some b; decl_type := ty |}]) t =
  expand_lets (subst_context [b] 0 Γ) (subst [b] #|Γ| t).
Proof.
  rewrite /expand_lets; apply expand_lets_k_vdef.
Qed.

Definition expand_lets_k_ctx_vass Γ k Δ na ty :
  expand_lets_k_ctx Γ k (Δ ++ [{| decl_name := na; decl_body := None; decl_type := ty |}]) =
  expand_lets_k_ctx Γ (S k) Δ ++ [{| decl_name := na; decl_body := None; decl_type :=
    expand_lets_k Γ k ty |}].
Proof. 
  now  rewrite /expand_lets_k_ctx lift_context_app subst_context_app /=; simpl.
Qed.

Definition expand_lets_k_ctx_decl Γ k Δ d :
  expand_lets_k_ctx Γ k (Δ ++ [d]) = expand_lets_k_ctx Γ (S k) Δ ++ [map_decl (expand_lets_k Γ k) d].
Proof. 
  rewrite /expand_lets_k_ctx lift_context_app subst_context_app /=; simpl.
  unfold app_context. simpl.
  rewrite /subst_context /fold_context /=.
  f_equal. rewrite compose_map_decl. f_equal.
Qed.

Lemma expand_lets_subst_comm Γ s : 
  expand_lets (subst_context s 0 Γ) ∘ subst s #|Γ| =1 subst s (context_assumptions Γ) ∘ expand_lets Γ.
Proof.
  unfold expand_lets, expand_lets_k; simpl; intros x.
  len.
  rewrite !subst_extended_subst.
  rewrite distr_subst. f_equal.
  len.
  now rewrite commut_lift_subst_rec.
Qed.

Lemma map_expand_lets_subst_comm Γ s :
  map (expand_lets (subst_context s 0 Γ)) ∘ (map (subst s #|Γ|)) =1 
  map (subst s (context_assumptions Γ)) ∘ (map (expand_lets Γ)).
Proof.
  intros l. rewrite !map_map_compose.
  apply map_ext. intros x; apply expand_lets_subst_comm.
Qed.

Lemma map_subst_expand_lets s Γ : 
  context_assumptions Γ = #|s| ->
  subst0 (map (subst0 s) (extended_subst Γ 0)) =1 subst0 s ∘ expand_lets Γ.
Proof.
  intros Hs x; unfold expand_lets, expand_lets_k.
  rewrite distr_subst. f_equal.
  len.
  simpl. rewrite simpl_subst_k //.
Qed.

Lemma map_subst_expand_lets_k s Γ k x : 
  context_assumptions Γ = #|s| ->
  subst (map (subst0 s) (extended_subst Γ 0)) k x = (subst s k ∘ expand_lets_k Γ k) x.
Proof.
  intros Hs; unfold expand_lets, expand_lets_k.
  epose proof (distr_subst_rec _ _ _ 0 _). rewrite -> Nat.add_0_r in H.
  rewrite -> H. clear H. f_equal.
  len.
  simpl. rewrite simpl_subst_k //.
Qed.

Lemma subst_context_map_subst_expand_lets s Γ Δ : 
  context_assumptions Γ = #|s| ->
  subst_context (map (subst0 s) (extended_subst Γ 0)) 0 Δ = subst_context s 0 (expand_lets_ctx Γ Δ).
Proof.
  intros Hs. rewrite !subst_context_alt.
  unfold expand_lets_ctx, expand_lets_k_ctx.
  rewrite subst_context_alt lift_context_alt. len.
  rewrite !mapi_compose. apply mapi_ext.
  intros n x. unfold subst_decl, lift_decl.
  rewrite !compose_map_decl. apply map_decl_ext.
  intros. simpl. rewrite !Nat.add_0_r.
  generalize (Nat.pred #|Δ| - n). intros.
  rewrite map_subst_expand_lets_k //.
Qed.

Lemma subst_context_map_subst_expand_lets_k s Γ Δ k : 
  context_assumptions Γ = #|s| ->
  subst_context (map (subst0 s) (extended_subst Γ 0)) k Δ = subst_context s k (expand_lets_k_ctx Γ k Δ).
Proof.
  intros Hs. rewrite !subst_context_alt.
  unfold expand_lets_ctx, expand_lets_k_ctx.
  rewrite subst_context_alt lift_context_alt. len.
  rewrite !mapi_compose. apply mapi_ext.
  intros n x. unfold subst_decl, lift_decl.
  rewrite !compose_map_decl. apply map_decl_ext.
  intros. simpl.
  rewrite map_subst_expand_lets_k //. f_equal.
  rewrite /expand_lets_k. lia_f_equal.
Qed.

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
      rewrite simpl_subst_k //. now len.
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
  rewrite nth_error_app_ge in nth. len. lia.
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
Hint Rewrite subst_instance_context_assumptions to_extended_list_k_length : len.

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


Definition option_all (p : term -> bool) (o : option term) : bool :=
  match o with
  | None => true
  | Some b => p b
  end.

Definition test_decl (p : term -> bool) d :=
  p d.(decl_type) && option_all p d.(decl_body).

Lemma option_all_map f g x : option_all f (option_map g x) = option_all (f ∘ g) x.
Proof.
  destruct x; reflexivity.
Qed.

Lemma test_decl_map_decl f g x : test_decl f (map_decl g x) = test_decl (f ∘ g) x.
Proof.
  now rewrite /test_decl /map_decl /= option_all_map.
Qed.

Lemma option_all_ext f g x : f =1 g -> option_all f x = option_all g x.
Proof.
  move=> Hf; destruct x; simpl => //; rewrite Hf; reflexivity.
Qed.

Lemma test_decl_eq f g x : f =1 g -> test_decl f x = test_decl g x.
Proof.
  intros Hf; rewrite /test_decl (Hf (decl_type x)) (option_all_ext f g) //.
Qed.


Lemma option_all_impl (f g : term -> bool) x : (forall x, f x -> g x) -> option_all f x -> option_all g x.
Proof.
  move=> Hf; destruct x; simpl => //; apply Hf.
Qed.

Lemma test_decl_impl (f g : term -> bool) x : (forall x, f x -> g x) -> test_decl f x -> test_decl g x.
Proof.
  intros Hf; rewrite /test_decl.
  move/andP=> [Hd Hb].
  apply/andP; split; eauto.
  eapply option_all_impl; eauto.
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
  move/andP => [cla clΓ] le.
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
  unfold subst_context, fold_context; simpl.
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
  eapply closedn_ctx_subst. simpl; len.
  eapply closedn_ctx_expand_lets. eapply closedn_ctx_upwards; eauto. lia.
  eapply closedn_ctx_upwards; eauto. lia.
  rewrite forallb_rev. now eapply closedn_to_extended_list_k.
  rewrite subst_subst_context. len.
  rewrite map_rev extended_subst_to_extended_list_k.
  rewrite (closed_ctx_subst _ (context_assumptions Γ + k)).
  rewrite Nat.add_comm; eapply closedn_ctx_expand_lets => //.
  eapply closedn_ctx_upwards; eauto. lia.
  eapply closedn_ctx_upwards; eauto. lia.
  reflexivity.
Qed.

Lemma subst_extended_lift Γ k : 
  closed_ctx Γ ->
  map (subst0 (List.rev (to_extended_list_k (smash_context [] Γ) k)))
    (extended_subst Γ 0) = extended_subst Γ k.
Proof.
  induction Γ in k |- *; intros cl; simpl; auto.
  destruct a as [na [b|] ty] => /=.
  len.
  rewrite closed_ctx_decl in cl. move/andP: cl => [cld clΓ].
  simpl. f_equal.
  rewrite distr_subst. len.
  simpl in cld.
  rewrite IHΓ //. f_equal. rewrite simpl_subst_k.
  len. rewrite context_assumptions_smash_context /= //.
  rewrite lift_closed //. now move/andP: cld => /= //.
  rewrite IHΓ //.

  simpl map.
  rewrite Nat.sub_diag. rewrite nth_error_rev.
  len. simpl.  rewrite context_assumptions_smash_context /=. lia.
  len. rewrite List.rev_involutive /= context_assumptions_smash_context /=.
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
  rewrite closed_ctx_decl in cl. move/andP: cl => [cld clΓ].
  now rewrite IHΓ // Nat.add_1_r.
Qed.

Lemma closed_subst_map_lift s n k t :
  closedn (#|s| + k) t ->
  subst (map (lift0 n) s) k t = subst s (n + k) (lift n k t).
Proof.
  remember (#|s| + k) as n'.
  intros cl; revert n' t cl k Heqn'.
  eapply (term_closedn_list_ind (fun n' t => forall k, n' = #|s| + k -> 
  subst (map (lift0  n) s) k t = subst s (n + k) (lift n k t)));
  intros; simpl; solve_all; eauto.
  - subst k.
    simpl.
    destruct (Nat.leb_spec k0 n0).
    rewrite nth_error_map.
    replace (n + n0 - (n + k0)) with (n0 - k0) by lia.
    destruct nth_error eqn:eq => /= //.
    destruct (Nat.leb_spec (n + k0) (n + n0)); try lia.
    rewrite simpl_lift; try lia. lia_f_equal.
    destruct (Nat.leb_spec (n + k0) (n + n0)); try lia.
    len.
    eapply nth_error_None in eq. lia.
    destruct (Nat.leb_spec (n + k0) n0); try lia.
    reflexivity.

  - simpl. f_equal. rewrite map_map_compose. solve_all.
  - simpl; f_equal; eauto.
    rewrite (H0 (S k0)). lia. lia_f_equal.
  - simpl. f_equal; eauto.
    rewrite (H0 (S k0)). lia. lia_f_equal.
  - simpl. f_equal; eauto.
    rewrite (H1 (S k0)). lia. lia_f_equal.
  - simpl. f_equal; eauto.
    rewrite map_map_compose. solve_all.
  - simpl. f_equal; eauto.
    rewrite map_map_compose. len.
    solve_all. rewrite map_def_map_def.
    specialize (a _ H). specialize (b (#|fix_context m| + k0)).
    forward b by lia. eapply map_def_eq_spec; auto.
    autorewrite with len in b.
    rewrite  b. lia_f_equal.
  - simpl. f_equal; eauto.
    rewrite map_map_compose. len.
    solve_all. rewrite map_def_map_def.
    specialize (a _ H). specialize (b (#|fix_context m| + k0)).
    forward b by lia. eapply map_def_eq_spec; auto.
    autorewrite with len in b.
    rewrite b. lia_f_equal.
Qed.

Lemma subst_map_lift_lift_context (Γ : context) k s : 
  closedn_ctx #|s| Γ ->
  subst_context (map (lift0 k) s) 0 Γ = 
  subst_context s k (lift_context k 0 Γ).
Proof.
  induction Γ as [|[? [] ?] ?] in k |- *; intros cl; auto;
    rewrite lift_context_snoc !subst_context_snoc /= /subst_decl /map_decl /=;
    rewrite closed_ctx_decl in cl;  move/andP: cl => [cld clΓ].
  - rewrite IHΓ //. f_equal. f_equal. f_equal;
    len.
    rewrite closed_subst_map_lift //. now move/andP: cld => /=.
    lia_f_equal.
    len.
    rewrite closed_subst_map_lift //. now move/andP: cld => /=.
    lia_f_equal.
  - f_equal. apply IHΓ => //.
    f_equal; len. rewrite closed_subst_map_lift //.
    lia_f_equal.
Qed.


Lemma on_constructor_inst_pars_indices {cf:checker_flags} Σ ind u mdecl idecl cshape cdecl Γ pars parsubst : 
  wf Σ.1 -> 
  declared_inductive Σ.1 mdecl ind idecl ->
  on_inductive (lift_typing typing) (Σ.1, ind_universes mdecl) (inductive_mind ind) mdecl ->
  forall (oib : on_ind_body (lift_typing typing) (Σ.1, ind_universes mdecl) (inductive_mind ind) mdecl 
           (inductive_ind ind) idecl)
        (onc : on_constructor (lift_typing typing) (Σ.1, PCUICAst.ind_universes mdecl)
          mdecl (inductive_ind ind) idecl (ind_indices oib) cdecl cshape), 
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  spine_subst Σ Γ pars parsubst (subst_instance_context u (ind_params mdecl)) ->
  ∑ inst,
  spine_subst Σ
          (Γ ,,, subst_context parsubst 0 (subst_context (ind_subst mdecl ind u) #|ind_params mdecl|
            (subst_instance_context u (cshape_args cshape))))
          (map (subst parsubst #|cshape_args cshape|)
            (map (subst (ind_subst mdecl ind u) (#|cshape_args cshape| + #|ind_params mdecl|))
              (map (subst_instance_constr u) (cshape_indices cshape))))
          inst
          (lift_context #|cshape_args cshape| 0
          (subst_context parsubst 0 (subst_instance_context u (ind_indices oib)))). 
Proof.
  move=> wfΣ declm oi oib onc cext sp.
  destruct (on_constructor_inst Σ ind u mdecl idecl _ cdecl wfΣ declm oi oib onc) as [wfl [inst sp']]; auto.
  rewrite !subst_instance_context_app in sp'.
  eapply spine_subst_app_inv in sp' as [spl spr]; auto.
  rewrite (spine_subst_extended_subst spl) in spr.
  rewrite subst_context_map_subst_expand_lets in spr; try now len.
  rewrite subst_instance_to_extended_list_k in spr.
  2:now len.
  rewrite lift_context_subst_context.
  rewrite -app_context_assoc in spr.
  eapply spine_subst_subst_first in spr; eauto.
  2:eapply subslet_inds; eauto.
  autorewrite with len in spr.
  rewrite subst_context_app in spr.
  assert (closed_ctx (subst_instance_context u (ind_params mdecl)) /\ closedn_ctx #|ind_params mdecl| (subst_instance_context u (ind_indices oib)))
  as [clpars clinds].
  { unshelve epose proof (on_minductive_wf_params_indices _  _ _ _ wfΣ _ oib).
    pcuic. eapply closed_wf_local in X => //.
    rewrite closedn_ctx_app in X; simpl; eauto.
    move/andP: X; intuition auto;
    now rewrite closedn_subst_instance_context. }
  assert (closedn_ctx (#|ind_params mdecl| + #|cshape_args cshape|) (subst_instance_context u (ind_indices oib))) 
    as clinds'.
  { eapply closedn_ctx_upwards; eauto. lia. }
  rewrite closed_ctx_subst // in spr.
  rewrite (closed_ctx_subst(inds (inductive_mind ind) u (ind_bodies mdecl)) _ (subst_context (List.rev _) _ _)) in spr.
  { len.
    rewrite -(Nat.add_0_r (#|cshape_args cshape| + #|ind_params mdecl|)).
    eapply closedn_ctx_subst. len.
    rewrite -(subst_instance_context_assumptions u).
    eapply closedn_ctx_expand_lets. eapply closedn_ctx_upwards; eauto. lia.
    len. eapply closedn_ctx_upwards; eauto. lia.
    rewrite forallb_rev. eapply closedn_to_extended_list_k.
    now len. }
  autorewrite with len in spr.
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
               subst (List.rev pars) #|cshape_args cshape|
                 (lift0 #|cshape_args cshape| x))
              (extended_subst (subst_instance_context u (ind_params mdecl)) 0) = 
              (map
              (fun x : term =>
              (lift0 #|cshape_args cshape|
                (subst (List.rev pars) 0 x)))
              (extended_subst (subst_instance_context u (ind_params mdecl)) 0))
              ).
  eapply map_ext => x.
  now rewrite -(commut_lift_subst_rec _ _ _ 0).
  rewrite H in spr. clear H.
  rewrite -(map_map_compose  _ _  _ _ (lift0 #|cshape_args cshape|)) in spr.
  rewrite -(spine_subst_extended_subst sp) in spr.
  rewrite subst_map_lift_lift_context in spr.
  rewrite -(context_subst_length _ _ _ sp).
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
  isWfArity_or_Type Σ Γ (it_mkProd_or_LetIn Γ' (mkApps (tInd ind i) args)) ->
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
  R_ind_universes Σ i (context_assumptions (ind_params mdecl) + #|cshape_indices cshape|) u u' *
  consistent_instance_ext Σ (ind_universes mdecl) u' *    
  (#|args| = (ind_npars mdecl + context_assumptions cshape.(cshape_args))%nat) *
  ∑ parsubst argsubst parsubst' argsubst',
    let parctx := (subst_instance_context u (ind_params mdecl)) in
    let parctx' := (subst_instance_context u' (ind_params mdecl)) in
    let argctx := (subst_context parsubst 0
    ((subst_context (inds (inductive_mind i) u mdecl.(ind_bodies)) #|ind_params mdecl|
    (subst_instance_context u cshape.(cshape_args))))) in
    let argctx2 := (subst_context parsubst' 0
    ((subst_context (inds (inductive_mind i) u' mdecl.(ind_bodies)) #|ind_params mdecl|
    (subst_instance_context u' cshape.(cshape_args))))) in
    let argctx' := (subst_context parsubst' 0 (subst_instance_context u' oib.(ind_indices))) in
    
    spine_subst Σ Γ (firstn (ind_npars mdecl) args) parsubst parctx *
    spine_subst Σ Γ (firstn (ind_npars mdecl) args') parsubst' parctx' *
    spine_subst Σ Γ (skipn (ind_npars mdecl) args) argsubst argctx *
    spine_subst Σ Γ (skipn (ind_npars mdecl) args')  argsubst' argctx' *

    ∑ s, type_local_ctx (lift_typing typing) Σ Γ argctx2 s *
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
  split; auto. split => //.
  now autorewrite with len in Hu.
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
  move: Hs. len. intuition auto.
  rewrite closed_ctx_subst in a0 => //.
  now rewrite closedn_subst_instance_context.

  (*rewrite -Heqp in spars sargs. simpl in *. clear Heqp. *)
  exists parsubst, argsubst.
  assert(wfar : wf_local Σ
  (Γ ,,, subst_instance_context u' (arities_context (ind_bodies mdecl)))).
  { eapply weaken_wf_local => //.
    eapply wf_local_instantiate => //; destruct decli; eauto.
    eapply wf_arities_context => //; eauto. }
  assert(wfpars : wf_local Σ (subst_instance_context u (ind_params mdecl))).
    { eapply on_minductive_wf_params => //; eauto. }
      
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
  - exists (subst_instance_univ u' (cshape_sort cshape)). split.
    move/onParams: onmind. rewrite /on_context.
    pose proof (wf_local_instantiate Σ (InductiveDecl mdecl) (ind_params mdecl) u').
    move=> H'. eapply X in H'; eauto.
    2:destruct decli; eauto.
    clear -wfar wfpars wfΣ hΓ cons decli t cargs sargs H0 H' a spars a0.
    eapply (subst_type_local_ctx _ _ [] 
      (subst_context (inds (inductive_mind i) u' (ind_bodies mdecl)) 0 (subst_instance_context u' (ind_params mdecl)))) => //.
    simpl. eapply weaken_wf_local => //.
    rewrite closed_ctx_subst => //.
    now rewrite closedn_subst_instance_context.
    simpl. rewrite -(subst_instance_context_length u' (ind_params mdecl)).
    eapply (subst_type_local_ctx _ _ _ (subst_instance_context u' (arities_context (ind_bodies mdecl)))) => //.
    eapply weaken_wf_local => //.
    rewrite -app_context_assoc.
    eapply weaken_type_local_ctx => //.
    rewrite -subst_instance_context_app.
    eapply type_local_ctx_instantiate => //; destruct decli; eauto.
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

  apply context_relation_app_inv. rewrite !List.rev_length; len.
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

Ltac unf_env := 
  change PCUICEnvironment.it_mkProd_or_LetIn with it_mkProd_or_LetIn in *; 
  change PCUICEnvironment.to_extended_list_k with to_extended_list_k in *; 
  change PCUICEnvironment.ind_params with ind_params in *.

Derive Signature for positive_cstr.


Lemma positive_cstr_it_mkProd_or_LetIn mdecl i Γ Δ t : 
  positive_cstr mdecl i Γ (it_mkProd_or_LetIn Δ t) ->
  All_local_env (fun Δ ty _ => positive_cstr_arg mdecl i (Γ ,,, Δ) ty)
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
    eapply All_local_env_app_inv; split.
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


Lemma expand_lets_it_mkProd_or_LetIn Γ Δ k t : 
  expand_lets_k Γ k (it_mkProd_or_LetIn Δ t) = 
  it_mkProd_or_LetIn (expand_lets_k_ctx Γ k Δ) (expand_lets_k Γ (k + #|Δ|) t).
Proof.
  revert k; induction Δ as [|[na [b|] ty] Δ] using ctx_length_rev_ind; simpl; auto; intros k.
  - now rewrite /expand_lets_k_ctx /= Nat.add_0_r.
  - rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /=.
    rewrite /expand_lets_ctx expand_lets_k_ctx_decl /= it_mkProd_or_LetIn_app.
    simpl. f_equal. rewrite app_length /=.
    simpl. rewrite Nat.add_1_r Nat.add_succ_r.
    now rewrite -(H Δ ltac:(lia) (S k)).
  - rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /=.
    rewrite /expand_lets_ctx expand_lets_k_ctx_decl /= it_mkProd_or_LetIn_app.
    simpl. f_equal. rewrite app_length /=.
    simpl. rewrite Nat.add_1_r Nat.add_succ_r.
    now rewrite -(H Δ ltac:(lia) (S k)).
Qed.

Lemma expand_lets_k_mkApps Γ k f args : 
  expand_lets_k Γ k (mkApps f args) =
  mkApps (expand_lets_k Γ k f) (map (expand_lets_k Γ k) args).
Proof.
  now rewrite /expand_lets_k lift_mkApps subst_mkApps map_map_compose.
Qed.
Lemma expand_lets_mkApps Γ f args : 
  expand_lets Γ (mkApps f args) =
  mkApps (expand_lets Γ f) (map (expand_lets Γ) args).
Proof.
  now rewrite /expand_lets expand_lets_k_mkApps.
Qed.  
 
Lemma expand_lets_cstr_head k Γ : 
  expand_lets Γ (tRel (k + #|Γ|)) = tRel (k + context_assumptions Γ).
Proof.
  rewrite /expand_lets /expand_lets_k. 
  rewrite lift_rel_ge. lia.
  rewrite subst_rel_gt. len. lia.
  len. lia_f_equal.
Qed.

Lemma positive_cstr_closed_indices {cf:checker_flags} {Σ : global_env_ext} (wfΣ : wf Σ.1):
  forall {i mdecl idecl cdecl ind_indices cs},
  on_constructor (lift_typing typing) (Σ.1, ind_universes mdecl) mdecl i idecl ind_indices cdecl cs -> 
  All (closedn (#|ind_params mdecl| + #|cshape_args cs|)) (cshape_indices cs).
Proof.
  intros.
  pose proof (X.(on_ctype_positive)).
  rewrite X.(cstr_eq) in X0. unf_env.
  rewrite -it_mkProd_or_LetIn_app in X0.
  eapply positive_cstr_it_mkProd_or_LetIn in X0 as [hpars hpos].
  rewrite app_context_nil_l in hpos.
  rewrite expand_lets_mkApps in hpos.
  unfold cstr_concl_head in hpos.
  have subsrel := expand_lets_cstr_head (#|ind_bodies mdecl| - S i) (cshape_args cs  ++ ind_params mdecl).
  rewrite app_length (Nat.add_comm #|(cshape_args cs)|) Nat.add_assoc in subsrel. rewrite {}subsrel in hpos.
  rewrite context_assumptions_app in hpos. depelim hpos; solve_discr.
  simpl in H; noconf H.
  eapply All_map_inv in a.
  eapply All_app in a as [ _ a].
  eapply (All_impl a).
  clear. intros.
  autorewrite with len in H; simpl in H.
  rewrite -context_assumptions_app in H.
  apply (closedn_expand_lets 0) in H => //.
  autorewrite with len in H.
  now rewrite Nat.add_comm.
Qed.

Lemma declared_inductive_lookup_inductive {Σ ind mdecl idecl} :
  declared_inductive Σ mdecl ind idecl ->
  lookup_inductive Σ ind = Some (mdecl, idecl).
Proof.
  rewrite /declared_inductive /lookup_inductive.
  intros []. red in H. now rewrite /lookup_minductive H H0.
Qed.

Require Import Equations.Type.Relation_Properties.
Lemma red_subst_instance {cf:checker_flags} (Σ : global_env) (Γ : context) (u : Instance.t) (s t : term) :
  red Σ Γ s t ->
  red Σ (subst_instance_context u Γ) (subst_instance_constr u s)
            (subst_instance_constr u t).
Proof.
  intros H; apply red_alt, clos_rt_rt1n in H.
  apply red_alt, clos_rt1n_rt.
  induction H. constructor.
  eapply red1_subst_instance in r.
  econstructor 2. eapply r.
  auto.
Qed.

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
  remember (Γ ,,, Δ) as ctx.
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
    now rewrite app_context_assoc in b0.
Qed.

Lemma red_assumption_context_app_irrelevant Σ Γ Δ Γ' t t' : 
  red Σ (Γ ,,, Δ) t t' ->
  assumption_context Γ ->
  #|Γ| = #|Γ'| ->
  red Σ (Γ' ,,, Δ) t t'. 
Proof.
  intros r ass eqc.
  eapply red_alt, clos_rt_rt1n in r.
  eapply red_alt. eapply clos_rt1n_rt.
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
  assumption_context Γ -> assumption_context (subst_instance_context u Γ).
Proof. apply assumption_context_map. Qed.

Lemma eq_term_upto_univ_napp_impl {cf:checker_flags} (Σ : global_env) 
  (Re Re' Rle Rle' : Relation_Definitions.relation Universe.t) u u' t t' : 
  (forall x y : Universe.t, Re x y -> Re' (subst_instance_univ u x) (subst_instance_univ u' y)) ->
  (forall x y : Universe.t, Rle x y -> Rle' (subst_instance_univ u x) (subst_instance_univ u' y)) ->
  (forall x y : Instance.t, R_universe_instance Re x y -> R_universe_instance Re' (subst_instance_instance u x) 
    (subst_instance_instance u' y)) ->
  (forall r n (x y : Instance.t), R_global_instance Σ Re Rle r n x y -> 
    R_global_instance Σ Re' Rle' r n (subst_instance_instance u x) (subst_instance_instance u' y)) ->
  (forall r n (x y : Instance.t), R_global_instance Σ Re Re r n x y -> 
    R_global_instance Σ Re' Re' r n (subst_instance_instance u x) (subst_instance_instance u' y)) ->
  forall n, eq_term_upto_univ_napp Σ Re Rle n t t' ->
  eq_term_upto_univ_napp Σ Re' Rle' n (subst_instance_constr u t) (subst_instance_constr u' t').
Proof.
  intros Heq Hle Hi Hgil Hgie.
  induction t in t', Re, Re', Rle, Rle', Heq, Hle, Hi, Hgil, Hgie |- * using 
    PCUICInduction.term_forall_list_ind; simpl; intros n' H; depelim H. 
  all:simpl; try solve [constructor; eauto; try solve_all].
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

  Definition betweenu_universe (u : Universe.t) :=
    UnivExprSet.for_all betweenu_level_expr u.

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
  
  Definition lift_npl (k : nat) (e : NoPropLevel.t) : NoPropLevel.t :=
    match e with
    | NoPropLevel.lSet => NoPropLevel.lSet
    | NoPropLevel.Level s => NoPropLevel.Level s
    | NoPropLevel.Var n => NoPropLevel.Var (k + n)
    end.

  (* Definition lift_expr (n : nat) (e : UnivExpr.t) : UnivExpr.t. *)

  Lemma closedu_subst_instance_level_expr_app u u' e
    : closedu_level_expr #|u'| e -> subst_instance_level_expr (u' ++ u) e = subst_instance_level_expr u' e.
  Proof.
    destruct e as [|[[] b]]; cbnr.
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
  
  Lemma closedu_subst_instance_instance_app u u' t
    : closedu_instance #|u'| t -> subst_instance_instance (u' ++ u) t = subst_instance_instance u' t.
  Proof.
    intro H. eapply forallb_All in H. apply All_map_eq.
    solve_all. now eapply closedu_subst_instance_level_app.
  Qed.
  
  Lemma closedu_subst_instance_instance_lift u u' t
    : closedu_instance #|u| t -> subst_instance_instance (u' ++ u) (lift_instance #|u'| t) = subst_instance_instance u t.
  Proof.
    intro H. eapply forallb_All in H.
    rewrite /subst_instance_instance /lift_instance map_map_compose. apply All_map_eq.
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
  intros [_ [_ [H _]]].
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
Proof. rewrite /consistent_instance_ext /=; intros [_ [_ [_ v]]] cu.
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

Lemma LSet_in_global_bounded {cf:checker_flags} {Σ l} k : 
  wf Σ -> LevelSet.In l (global_levels Σ) ->
  closedu_level k l.
Proof.
  simpl.
  intros wf. eapply not_var_global_levels in wf.
  intros hin. specialize (wf _ hin). simpl in wf.
  destruct l; simpl in *; congruence.
Qed.

Lemma on_udecl_poly_bounded {cf:checker_flags} Σ inst cstrs :
  wf Σ ->
  on_udecl Σ (Polymorphic_ctx (inst, cstrs)) ->
  closedu_cstrs #|inst| cstrs.
Proof.
  rewrite /on_udecl. intros wfΣ [_ [nlevs _]].
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
  move/andP: clcstra => [cll clr].
  rewrite !closedu_subst_instance_level_app //.

  subst c; exists x; split; auto.
  specialize (clcstra _ H0).
  simpl in *.
  destruct x as [[l c] r]; rewrite /subst_instance_cstr; simpl.
  move/andP: clcstra => [cll clr].
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
    move/andP: clcstra => [cll clr].
    rewrite !closedu_subst_instance_level_lift //.

  - subst c.
    exists (lift_constraint #|u| x).
    rewrite -> In_lift_constraints.
    firstorder eauto.
    specialize (clcstra _ H0).
    simpl in *.
    destruct x as [[l c] r]; rewrite /subst_instance_cstr; simpl.
    move/andP: clcstra => [cll clr].
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
  firstorder eauto.
  subst. exists x0; firstorder.
Qed.

Lemma subst_instance_variance_cstrs l u i i' :
  CS.Equal (subst_instance_cstrs u (variance_cstrs l i i'))
    (variance_cstrs l (subst_instance_instance u i) (subst_instance_instance u i')).
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
  on_udecl Σ (ind_universes mdecl) ->
  on_variance (ind_universes mdecl) (Some l) ->
  variance_universes (PCUICEnvironment.ind_universes mdecl) l = Some (v, i, i') ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  consistent_instance_ext Σ (ind_universes mdecl) u' ->
  R_universe_instance_variance (eq_universe Σ) (leq_universe Σ) l u u' ->
  forall t t',
  cumul (Σ.1, v) (subst_instance_context i Γ) (subst_instance_constr i t) (subst_instance_constr i' t') ->
  cumul Σ (subst_instance_context u Γ)
    (subst_instance_constr u t) (subst_instance_constr u' t').
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
  assert (forallb (fun x : Level.t => ~~ Level.is_prop x) (u' ++ u)).
  { rewrite forallb_app; erewrite !consistent_instance_ext_noprop; eauto. }
  assert (subst_instance_instance (u' ++ u) (lift_instance #|u'| i') = u) as subsu.
  { rewrite closedu_subst_instance_instance_lift //.
    now rewrite H. rewrite eqi'.
    erewrite subst_instance_instance_id => //. eauto. }
  assert (subst_instance_instance (u' ++ u) i' = u') as subsu'.
  { rewrite closedu_subst_instance_instance_app //.
    rewrite H0 //. rewrite eqi' //.
    erewrite subst_instance_instance_id => //. eauto. } 
  eapply (cumul_subst_instance (Σ, v) _ (u' ++ u)) in cum; auto.
  rewrite subst_instance_context_two in cum.
  rewrite !subst_instance_constr_two in cum.
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
      eapply on_udecl_poly_bounded; eauto. }
    eapply consistent_instance_valid in cu'; eauto.
  - rewrite -satisfies_subst_instance_ctr // -H0.
    assert(ConstraintSet.Equal (subst_instance_cstrs u cstrs')
        (subst_instance_cstrs (u' ++ u) (lift_constraints #|u'| cstrs'))) as <-.
    { rewrite closedu_subst_instance_cstrs_lift //.
      rewrite H -H0 (consistent_instance_poly_length cu').
      eapply on_udecl_poly_bounded; eauto. }
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
      constructor. now rewrite !Universes.UnivExpr.val_make in Ra.
    + do 2 red in Ra. rewrite checku in Ra.
      specialize  (Ra _ sat).
      constructor. now rewrite !Universes.Universe.val_make in Ra.
Qed.

Lemma All2_local_env_inst {cf:checker_flags} (Σ : global_env_ext) mdecl l v i i' u u' Γ' Γ : 
  wf Σ ->  
  on_udecl Σ (ind_universes mdecl) ->
  on_variance (ind_universes mdecl) (Some l) ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  consistent_instance_ext Σ (ind_universes mdecl) u' ->
  variance_universes (PCUICEnvironment.ind_universes mdecl) l = Some (v, i, i') ->
  R_universe_instance_variance (eq_universe Σ) (leq_universe Σ) l u u' ->
  cumul_ctx_rel (Σ.1, v) (subst_instance_context i Γ') (subst_instance_context i Γ) (subst_instance_context i' Γ) ->
  cumul_ctx_rel Σ (subst_instance_context u Γ') (subst_instance_context u Γ) (subst_instance_context u' Γ).
Proof.
  unfold cumul_ctx_rel.
  intros wfΣ onu onv cu cu' vari Ru.
  induction Γ as [|[na [b|] ty] tl]; simpl.
  constructor.
  intros H; depelim H; simpl in H0; noconf H0; simpl in H1; noconf H1.
  econstructor; auto. red.
  destruct o.
  rewrite -subst_instance_context_app in c, c0. simpl in c0 |- *.
  rewrite -subst_instance_context_app.
  split; eapply cumul_inst_variance; eauto.

  intros H; depelim H; simpl in H0; noconf H0; simpl in H1; noconf H1.
  simpl in *.
  constructor; auto.
  red. simpl.
  rewrite -subst_instance_context_app in o.
  rewrite -subst_instance_context_app.
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

Lemma constructor_cumulative_indices {cf:checker_flags} {Σ : global_env_ext} (wfΣ : wf Σ.1) :
  forall {ind mdecl idecl cdecl cs u u' napp},
  declared_inductive Σ mdecl ind idecl ->
  forall (oib : on_ind_body (lift_typing typing) (Σ.1, ind_universes mdecl) (inductive_mind ind) mdecl 
    (inductive_ind ind) idecl),
  on_constructor (lift_typing typing) (Σ.1, ind_universes mdecl) mdecl (inductive_ind ind) idecl 
    (ind_indices oib) cdecl cs -> 
  on_udecl Σ (ind_universes mdecl) ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  consistent_instance_ext Σ (ind_universes mdecl) u' ->
  R_global_instance Σ (eq_universe Σ) (leq_universe Σ) (IndRef ind) napp u u' ->
  forall Γ pars pars' parsubst parsubst',
  spine_subst Σ Γ pars parsubst (subst_instance_context u (ind_params mdecl)) ->
  spine_subst Σ Γ pars' parsubst' (subst_instance_context u' (ind_params mdecl)) ->  
  All2 (conv Σ Γ) pars pars' ->
  let argctx := 
      (subst_context (ind_subst mdecl ind u) #|ind_params mdecl| (subst_instance_context u (cshape_args cs)))
  in
  let argctx' :=
     (subst_context (ind_subst mdecl ind u') #|ind_params mdecl| (subst_instance_context u' (cshape_args cs)))
  in
  let pargctx := subst_context parsubst 0 argctx in
  let pargctx' := subst_context parsubst' 0 argctx' in
  All2_local_env (fun Γ' _ _ x y => Σ ;;; Γ ,,, Γ' |- x <= y) 
    (smash_context [] pargctx) (smash_context [] pargctx') *
  All2 (conv Σ (Γ ,,, smash_context [] pargctx))
    (map (subst parsubst (context_assumptions (cshape_args cs)))
      (map (expand_lets argctx) (map (subst_instance_constr u) (cshape_indices cs))))
    (map (subst parsubst' (context_assumptions (cshape_args cs)))
      (map (expand_lets argctx') (map (subst_instance_constr u') (cshape_indices cs)))).
Proof.
  intros. move: H3.
  unfold R_global_instance.
  simpl. rewrite (declared_inductive_lookup_inductive H).
  pose proof H as decli.
  eapply on_declared_inductive in H as [onind _]; eauto.
  rewrite oib.(ind_arity_eq). 
  rewrite !destArity_it_mkProd_or_LetIn. simpl.
  rewrite app_context_nil_l context_assumptions_app.
  elim: leb_spec_Set => comp.
  destruct ind_variance eqn:indv.
  pose proof (X.(on_ctype_variance)) as respv.
  specialize (respv _ indv).
  simpl in respv.
  unfold respects_variance in respv.
  destruct variance_universes as [[[v i] i']|] eqn:vu => //.
  destruct respv as [args idx].
  simpl.
  intros Ru.
  { split.
    { eapply All2_local_env_inst in args.
      8:eauto. all:eauto.
      2:{ pose proof (onVariance _ _ _ _ onind).
          now rewrite -indv. }
      rewrite -smash_context_subst subst_context_nil in args.
      rewrite !subst_instance_context_smash /= in args.
      rewrite subst_instance_context_app in args.
      epose proof (cumul_ctx_subst _ [] _ _ _ _ _ _).
      rewrite app_context_nil_l in X3. eapply X3 in args; clear X3.
      rewrite app_context_nil_l in args.
      autorewrite with len in args. simpl in args.
      5:{ eapply subslet_untyped_subslet. eapply subslet_inds; eauto. }
      5:{ eapply subslet_untyped_subslet. eapply subslet_inds; eauto. }
      4:{ eapply conv_inds. admit. }
      all:eauto.
      2:admit.
      
      rewrite - !smash_context_subst !subst_context_nil in args.
      assert (closed_ctx
        (subst_instance_context u
          (smash_context [] (PCUICEnvironment.ind_params mdecl)))) by admit.
      rewrite closed_ctx_subst // in args.
      eapply (weaken_cumul_ctx _ Γ) in args => //.
      4:eapply X0.
      2:{ rewrite closedn_ctx_app; apply /andP. split => //. simpl.
          len. simpl. eapply closedn_smash_context.
          rewrite -(Nat.add_0_l (context_assumptions _)).
          eapply closedn_ctx_subst. len; simpl.
          2:{ eapply declared_minductive_closed_inds; eauto. }
          epose proof (on_constructor_subst' _ _ _ _ _ _ wfΣ decli onind oib X) as [[_ wf'] _].
          eapply closed_wf_local in wf'.
          rewrite closedn_ctx_app in wf'. move/andP: wf'=> [_ clargs].
          simpl in clargs; autorewrite with len in clargs.
          rewrite closedn_subst_instance_context.
          rewrite -(Nat.add_0_r (context_assumptions _ + _)).
          eapply closedn_ctx_subst. len.
          eapply closedn_ctx_upwards; eauto. lia.
          eapply forallb_closed_upwards. eapply closedn_extended_subst; try lia.
          2:lia. rewrite -(closedn_subst_instance_context (u:=u)).
          eapply closed_wf_local; eauto. eapply on_minductive_wf_params; eauto. auto. }
      2:{ rewrite closedn_ctx_app; apply /andP. split => //. simpl.
          len. simpl. eapply closedn_smash_context.
          rewrite -(Nat.add_0_l (context_assumptions _)).
          eapply closedn_ctx_subst. len; simpl.
          2:{ eapply declared_minductive_closed_inds; eauto. }
          epose proof (on_constructor_subst' _ _ _ _ _ _ wfΣ decli onind oib X) as [[_ wf'] _].
          eapply closed_wf_local in wf'.
          rewrite closedn_ctx_app in wf'. move/andP: wf'=> [_ clargs].
          simpl in clargs; autorewrite with len in clargs.
          rewrite closedn_subst_instance_context.
          rewrite -(Nat.add_0_r (context_assumptions _ + _)).
          eapply closedn_ctx_subst. len.
          eapply closedn_ctx_upwards; eauto. lia.
          eapply forallb_closed_upwards. eapply closedn_extended_subst; try lia.
          2:lia. rewrite -(closedn_subst_instance_context (u:=u)).
          eapply closed_wf_local; eauto. eapply on_minductive_wf_params; eauto. auto. }
      eapply spine_subst_smash in X0 => //.
      eapply spine_subst_smash in X1 => //.
      eapply (cumul_ctx_subst _ Γ _ _ [] _ _ (List.rev pars) (List.rev pars')) in args; eauto.
      3:{ eapply All2_rev => //. }
      3:{ rewrite subst_instance_context_smash /=.
          eapply subslet_untyped_subslet. eapply X0. }
      3:{ eapply subslet_untyped_subslet. eapply X1. }
      2:admit.
      move: args.
      rewrite subst_context_nil /= - !smash_context_subst /= subst_context_nil.
      len.
      rewrite !subst_instance_subst_context.
      generalize (subst_app_context_gen (List.rev pars)).
      rewrite -(context_subst_length _ _ _ X0). len; simpl.
      move=> subs. rewrite -(subs _ 0).
      


      eapply 


(*  Real problem here: the args hypothesis could perfectly prove that Ind I@{u} (X := Type@{u}) : Type@{u} := foo : X -> I@{u}
  with u irrelevant. The cumulativity test *must* smash the  parameters sright away.
*)

      eapply (cumul_ctx_subst _ Γ _ []) in args.
      5:{ eapply subslet_untyped_subslet. eapply X0. }
      all:auto.
      3:{ eapply  }
      autorewrite with len in args. simpl in args.
      
      
        

      }



     }
  }

  2:{ simpl. }
  2:{ simpl. }

  (* We need to strengthen respects variance to allow arbitrary parameter substitutions *)
Admitted.

  
Lemma wt_ind_app_variance {cf:checker_flags} {Σ : global_env_ext} {Γ ind u l}:
  wf Σ.1 ->
  isWfArity_or_Type Σ Γ (mkApps (tInd ind u) l) ->
  ∑ mdecl, (lookup_inductive Σ ind = Some mdecl) *
  (global_variance Σ (IndRef ind) #|l| = ind_variance (fst mdecl)).
Proof.
  move=> wfΣ.
  move/isWAT_mkApps_Ind_isType => [s wat].
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
  pose proof decli as decli'.
  eapply on_declared_inductive in decli' as [onmi oni]; auto.
  rewrite oni.(ind_arity_eq) in Hargs |- *.
  rewrite !destArity_it_mkProd_or_LetIn. simpl.
  rewrite app_context_nil_l.
  rewrite !subst_instance_constr_it_mkProd_or_LetIn in Hargs.
  rewrite -it_mkProd_or_LetIn_app in Hargs.
  eapply arity_typing_spine in Hargs; auto.
  destruct Hargs as [[Hl Hleq] ?]. rewrite Hl.
  len. now rewrite context_assumptions_app Nat.leb_refl.
  eapply weaken_wf_local; auto.
  rewrite -[_ ++ _]subst_instance_context_app.
  eapply on_minductive_wf_params_indices_inst; eauto with pcuic.
Qed.
