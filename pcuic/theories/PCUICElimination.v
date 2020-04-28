(* Distributed under the terms of the MIT license.   *)

From Coq Require Import String Arith Bool List Lia.
From MetaCoq.Template Require Import config utils Universes.
From MetaCoq.PCUIC Require Import PCUICTyping PCUICAst PCUICAstUtils
     PCUICLiftSubst PCUICInductives PCUICGeneration PCUICSpine PCUICWeakeningEnv
     PCUICSubstitution PCUICUnivSubst PCUICUnivSubstitution
     PCUICCtxShape PCUICConversion PCUICCumulativity PCUICConfluence PCUICContexts
     PCUICSR PCUICInversion PCUICValidity PCUICSafeLemmata PCUICContextConversion
     PCUICPrincipality.
Require Equations.Prop.DepElim.
From Equations Require Import Equations.
Require Import ssreflect.

Lemma consistent_instance_ext_noprop {cf:checker_flags} {Σ univs u} : 
  consistent_instance_ext Σ univs u ->
  forallb (fun x1 : Level.t => negb (Level.is_prop x1)) u.
Proof.
  unfold consistent_instance_ext, consistent_instance.
  destruct univs. destruct u; simpl; try discriminate; auto.
  firstorder.
Qed.

Lemma not_prop_not_leq_prop sf : sf <> InProp -> ~ leb_sort_family sf InProp.
Proof.
  destruct sf; simpl; try congruence.
Qed.

Definition Is_proof `{cf : checker_flags} Σ Γ t := ∑ T u, Σ ;;; Γ |- t : T × Σ ;;; Γ |- T : tSort u × Universe.is_prop u.


Definition SingletonProp `{cf : checker_flags} (Σ : global_env_ext) (ind : inductive) :=
  forall mdecl idecl,
    declared_inductive (fst Σ) mdecl ind idecl ->
    forall Γ args u n (Σ' : global_env_ext),
      wf Σ' ->
      PCUICWeakeningEnv.extends Σ Σ' ->
      welltyped Σ' Γ (mkApps (tConstruct ind n u) args) ->
      ∥Is_proof Σ' Γ (mkApps (tConstruct ind n u) args)∥ /\
       #|ind_ctors idecl| <= 1 /\
       squash (All (Is_proof Σ' Γ) (skipn (ind_npars mdecl) args)).

Definition Computational `{cf : checker_flags} (Σ : global_env_ext) (ind : inductive) :=
  forall mdecl idecl,
    declared_inductive (fst Σ) mdecl ind idecl ->
    forall Γ args u n (Σ' : global_env_ext),
      wf Σ' ->
      PCUICWeakeningEnv.extends Σ Σ' ->
      welltyped Σ' Γ (mkApps (tConstruct ind n u) args) ->
      Is_proof Σ' Γ (mkApps (tConstruct ind n u) args) -> False.

Definition Informative `{cf : checker_flags} (Σ : global_env_ext) (ind : inductive) :=
  forall mdecl idecl,
    declared_inductive (fst Σ) mdecl ind idecl ->
    forall Γ args u n (Σ' : global_env_ext),
      wf Σ' ->
      PCUICWeakeningEnv.extends Σ Σ' ->
      Is_proof Σ' Γ (mkApps (tConstruct ind n u) args) ->
       #|ind_ctors idecl| <= 1 /\
       squash (All (Is_proof Σ' Γ) (skipn (ind_npars mdecl) args)).

Lemma leb_sort_family_intype sf : leb_sort_family InType sf -> sf = InType.
Proof.
  destruct sf; simpl; auto; discriminate.
Qed.

Lemma elim_restriction_works_kelim1 `{cf : checker_flags} (Σ : global_env_ext) Γ T ind npar p c brs mind idecl : wf Σ ->
  declared_inductive (fst Σ) mind ind idecl ->
  Σ ;;; Γ |- tCase (ind, npar) p c brs : T ->
  (Is_proof Σ Γ (tCase (ind, npar) p c brs) -> False) ->
  ind_kelim idecl = InType \/ ind_kelim idecl = InSet.
Proof.
  intros wfΣ. intros.
  assert (HT := X).
  eapply inversion_Case in X as [uni [args [mdecl [idecl' [ps [pty [btys
                                   [? [? [? [? [? [? [ht0 [? ?]]]]]]]]]]]]]]]; auto.
  repeat destruct ?; try congruence. subst.
  eapply declared_inductive_inj in d as []. 2:exact H. subst.
  enough (universe_family ps <> InProp).
  { clear -i H1.
    unfold universe_family in *.
    unfold leb_sort_family in i.
    destruct (Universe.is_prop ps); auto. congruence.
    destruct (Universe.is_small ps);
    destruct (ind_kelim idecl); intuition congruence. }
  intros Huf. apply H0.
  red. exists (mkApps p (skipn (ind, npar).2 args ++ [c])); intuition auto.
  exists ps.
  intuition auto.
  econstructor; eauto.
  assert (watiapp := env_prop_typing  _ _ validity _ _ _ _ _ t0).
  simpl in watiapp.
  eapply (isWAT_mkApps_Ind wfΣ H) in watiapp as [psub [asub [[spp spa] cuni]]]; eauto.
  2:eapply typing_wf_local; eauto.
  destruct on_declared_inductive as [oi oib] in *. simpl in *.
  eapply (build_case_predicate_type_spec _ _ _ _ _ _ _ _ oib) in e0 as [parsubst [cs eq]].
  rewrite eq in t.
  eapply PCUICGeneration.type_mkApps. eauto.
  eapply wf_arity_spine_typing_spine; auto.
  split; auto.
  now eapply validity in t.
  eapply arity_spine_it_mkProd_or_LetIn; eauto.
  subst npar.
  pose proof (PCUICContexts.context_subst_fun cs spp). subst psub. clear cs.
  eapply spa.
  simpl. constructor.
  rewrite PCUICLiftSubst.subst_mkApps. simpl.
  rewrite map_app map_map_compose.
  rewrite PCUICLiftSubst.map_subst_lift_id_eq. 
  { rewrite - (PCUICSubstitution.context_subst_length _ _ _ spa).
      now autorewrite with len. }
  { unfold to_extended_list. 
    rewrite (spine_subst_subst_to_extended_list_k_gen spa).
    unfold subst_context; rewrite to_extended_list_k_fold_context.
    apply PCUICSubstitution.map_subst_instance_constr_to_extended_list_k.
    subst npar.
    now rewrite firstn_skipn. }
  - constructor.
    * left; eexists _, _; intuition eauto. simpl.
      eapply typing_wf_local; eauto.
    * reflexivity.
  - unfold universe_family in Huf.
    destruct (Universe.is_prop ps); auto.
    destruct (Universe.is_small ps); discriminate.
Qed.

Lemma family_InProp u : universe_family u = InProp <-> Universe.is_prop u.
Proof.
  unfold universe_family.
  split; destruct (Universe.is_prop u); try congruence;
    destruct (Universe.is_small u); try congruence.
Qed.

Lemma elim_sort_intype {cf:checker_flags} Σ mdecl ind idecl ind_indices ind_sort sorts :
  universe_family ind_sort = InProp ->
  leb_sort_family InType (elim_sort_prop_ind sorts) ->
  on_constructors (lift_typing typing)
    (Σ, ind_universes mdecl) mdecl 
    (inductive_ind ind) idecl ind_indices
    (ind_ctors idecl) sorts ->
  (#|ind_ctors idecl| = 0) + 
  (∑ cdecl sort, 
    (ind_ctors idecl = [cdecl]) * 
    (sorts = [sort]) * 
    (universe_family sort = InProp) *
    (on_constructor (lift_typing typing) (Σ, ind_universes mdecl) mdecl 
        (inductive_ind ind) idecl ind_indices cdecl sort))%type.
Proof.
  intros uf lein onc.
  induction onc; simpl in *.
  left; auto.
  destruct l' as [|c cs].
  - simpl in *. depelim onc.
    right.
    destruct (universe_family y) eqn:heq; try discriminate.
    eexists; eauto.
  - discriminate.
Qed.

Lemma typing_spine_it_mkProd_or_LetIn_full_inv {cf:checker_flags} Σ Γ Δ s args s' : 
  wf Σ.1 ->
  typing_spine Σ Γ (it_mkProd_or_LetIn Δ (tSort s)) args (tSort s') -> 
  leq_universe (global_ext_constraints Σ) s s'.
Proof.
  intros wfΣ.
  induction Δ using ctx_length_rev_ind in args |- *.
  - simpl. intros sp; depelim sp.
    now eapply cumul_Sort_inv in c.
    now eapply cumul_Sort_Prod_inv in c.
  - rewrite it_mkProd_or_LetIn_app; destruct d as [na [b|] ty]; simpl.
    * intros sp.
      specialize (H (subst_context [b] 0 Γ0) ltac:(now autorewrite with len)).
      eapply PCUICArities.typing_spine_letin_inv in sp; auto.
      rewrite /subst1 subst_it_mkProd_or_LetIn in sp. simpl in sp. eauto.
    * intros sp. depelim sp.
      now eapply cumul_Prod_Sort_inv in c.
      specialize (H (subst_context [hd] 0 Γ0) ltac:(now autorewrite with len) tl).
      apply H.
      eapply typing_spine_strengthen; eauto.
      eapply cumul_Prod_Prod_inv in c as [conv cum]. simpl in *.
      eapply (substitution_cumul _ Γ [vass na0 A] [] [hd]) in cum; auto.
      simpl in cum.
      now rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r in cum.
      constructor; auto. now eapply typing_wf_local.
      eapply PCUICArities.isWAT_tProd in i; auto. destruct i as [? ?]; auto.
      eapply typing_wf_local; eauto. constructor. constructor. now rewrite subst_empty.
      auto.
Qed.

Inductive All_local_assum (P : context -> term -> Type) : context -> Type :=
| localassum_nil :
    All_local_assum P []

| localassum_cons_abs Γ na t :
    All_local_assum P Γ ->
    P Γ t ->
    All_local_assum P (Γ ,, vass na t)

| localassum_cons_def Γ na b t :
    All_local_assum P Γ ->
    All_local_assum P (Γ ,, vdef na b t).

Derive Signature for All_local_assum.

Lemma All_local_assum_app P Γ Δ : All_local_assum P (Γ ++ Δ) ->
  All_local_assum P Δ *
  All_local_assum (fun Γ' => P (Δ ,,, Γ')) Γ.
Proof.
  induction Γ; simpl; constructor; intuition auto.
  constructor. depelim X; apply IHΓ; auto.
  depelim X; constructor; try apply IHΓ; auto.
Qed.

Lemma All_local_assum_subst {cf:checker_flags} (P Q : context -> term -> Type) c n k :
  All_local_assum Q c ->
  (forall Γ t,
      Q Γ t ->
      P (subst_context n k Γ) (subst n (#|Γ| + k) t)
  ) ->
  All_local_assum P (subst_context n k c).
Proof.
  intros Hq Hf.
  induction Hq in |- *; try econstructor; eauto;
    simpl; unfold snoc; rewrite subst_context_snoc; econstructor; eauto.
Qed.

Lemma typing_spine_proofs {cf:checker_flags} Σ Γ Δ ind u args' args T' s :
  wf Σ.1 ->
  Σ ;;; Γ |-  T' : tSort s ->
  typing_spine Σ Γ (it_mkProd_or_LetIn Δ (mkApps (tInd ind u) args')) args T' ->
  ((All_local_assum (fun Γ' t =>
      (∑ s, (Σ ;;; Γ ,,, Γ' |- t : tSort s) * Universe.is_prop s)%type) Δ ->
    ∥ All (Is_proof Σ Γ) args ∥) *
    (forall mdecl idecl 
    (Hdecl : declared_inductive Σ.1 mdecl ind idecl)
    (oib : on_ind_body (lift_typing typing) (Σ.1, ind_universes mdecl)
      (inductive_mind ind) mdecl (inductive_ind ind) idecl),
      leq_universe (global_ext_constraints Σ)
        (subst_instance_univ u oib.(ind_sort)) s))%type.
Proof.
  intros wfΣ Ht.
  induction Δ using ctx_length_rev_ind in Γ, args', args, T', Ht |- *; simpl; intros sp.
  - depelim sp. repeat constructor. 
    * eapply invert_cumul_ind_l in c as [ui' [l' [red  [Req argeq]]]] => //.
      intros mdecl idecl decli oib.
      eapply subject_reduction in Ht; eauto.
      eapply inversion_mkApps in Ht as [A [U [tInd [sp cum]]]]; auto.
      eapply PCUICArities.typing_spine_weaken_concl in sp; eauto.
      2:{ left; exists [], s; simpl; intuition auto. now eapply typing_wf_local. }
      clear cum.
      eapply inversion_Ind in tInd as [mdecl' [idecl' [wfΓ [decli' [cu cum]]]]]; auto.
      destruct (declared_inductive_inj decli decli'); subst mdecl' idecl'.
      clear decli'.
      eapply typing_spine_strengthen in sp; eauto.
      rewrite (oib.(ind_arity_eq)) in sp.
      rewrite !subst_instance_constr_it_mkProd_or_LetIn in sp.
      rewrite -it_mkProd_or_LetIn_app in sp.
      eapply typing_spine_it_mkProd_or_LetIn_full_inv in sp; auto.
      transitivity (subst_instance_univ ui' (ind_sort oib)).
      apply eq_universe_leq_universe.
      eapply Build_SubstUnivPreserving. 
      eapply PCUICEquality.R_universe_instance_impl.
      2:eauto. typeclasses eauto. eapply sp.
      
    * eapply cumul_Prod_r_inv in c; auto.
      destruct c as [na' [dom' [codom' [[red _] ?]]]].
      eapply red_mkApps_tInd in red as [? [? ?]] => //. solve_discr.

  - destruct d as [na [b|] ty].
    + rewrite it_mkProd_or_LetIn_app in sp.
      simpl in sp.
      eapply PCUICArities.typing_spine_letin_inv in sp => //.
      rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r in sp.
      specialize (H (subst_context [b] 0 Γ0) ltac:(now autorewrite with len)).
      rewrite subst_mkApps in sp.
      specialize (H _ _ _ _ Ht sp).
      split.
      * intros prs;eapply All_local_assum_app in prs as [prd prs].
      depelim prd; simpl in H0; noconf H0.
      apply H.
      clear -wfΣ prs.
      eapply All_local_assum_subst; eauto.
      simpl. intros.
      destruct X as [s [Ht2 isp]].
      exists s; firstorder.
      rewrite Nat.add_0_r. eapply (substitution _ Γ [vdef na b ty] [b] Γ1 _ (tSort s)); auto.
      rewrite -{1}(subst_empty 0 b).
      repeat (constructor; auto). rewrite !subst_empty.
      eapply typing_wf_local in Ht2.
      rewrite app_context_assoc in Ht2. eapply All_local_env_app in Ht2 as [Ht2 _].
      depelim Ht2; simpl in H; noconf H. apply l0.
      now rewrite app_context_assoc in Ht2.
      * intros mdecl idec decli oib.
        now apply H.
    + rewrite it_mkProd_or_LetIn_app in sp.
      destruct args. repeat constructor.
      * simpl in sp. depelim sp.
        unfold mkProd_or_LetIn in c; simpl in c.
        eapply cumul_Prod_l_inv in c as [na' [dom' [codom' [[red conv] cum]]]]; auto.
        eapply subject_reduction in Ht; eauto.
        intros. eapply inversion_Prod in Ht as [s1 [s2 [dom [codom cum']]]]; auto.
        specialize (H Γ0 ltac:(reflexivity) (Γ ,, vass na' dom') args' []).
        eapply (type_Cumul _ _ _ _ (tSort s)) in codom; cycle 1; eauto.
        { left. eexists _, _; simpl; intuition eauto. now eapply typing_wf_local. }
        { eapply cumul_Sort_inv in cum'.
          do 2 constructor. etransitivity; eauto. eapply leq_universe_product. }
        specialize (H _ codom).
        forward H.
        { constructor. now right; exists s.
          eapply cumul_conv_ctx; eauto. constructor; auto.
          apply conv_ctx_refl. now constructor. }
        destruct H.
        apply l. auto.
      * simpl in sp. depelim sp.
        eapply cumul_Prod_inv in c as [conv cum]; auto. 2:eauto using typing_wf_local.
        eapply typing_spine_strengthen in sp; auto.
        2:{ eapply (substitution_cumul0 _ _ _ _ _ _ t) in cum. eapply cum. auto. }
        rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r in sp.
        specialize (H (subst_context [t] 0 Γ0) ltac:(now autorewrite with len)).
        rewrite subst_mkApps in sp. simpl in sp.
        specialize (H _ _ _ _ Ht sp).
        split.
        intros prs;eapply All_local_assum_app in prs as [prd prs].
        depelim prd; simpl in H0; noconf H0.
        eapply (type_Cumul _ _ _ _ ty) in t0.
        2:{ right. destruct s0 as [s' [Hs' _]]. exists s'; auto. }
        2:{ eapply conv_cumul. now symmetry. }
        destruct H as [H _].
        forward H. { 
          clear -wfΣ prs t0.
          eapply All_local_assum_subst; eauto.
          simpl. intros.
          destruct X as [s [Ht2 isp]].
          exists s; firstorder.
          rewrite Nat.add_0_r. eapply (substitution _ Γ [vass na ty] [t] Γ1 _ (tSort s)); auto.
          repeat (constructor; auto). now rewrite subst_empty.
          now rewrite app_context_assoc in Ht2. }
        sq. constructor; auto. simpl in conv.
        red. destruct s0 as [s' [Ht' sprop]].
        exists ty, s'. intuition auto.
        destruct H as [_ H].
        intros. now apply H.
Qed.

Lemma check_ind_sorts_is_prop {cf:checker_flags} (Σ : global_env_ext) mdecl idecl ind
  (onib : on_ind_body (lift_typing typing) (Σ.1, ind_universes mdecl)
    (inductive_mind ind) mdecl (inductive_ind ind) idecl) : 
  ind_kelim idecl <> InProp ->
  Universe.is_prop (ind_sort onib) -> 
  check_ind_sorts (lift_typing typing) (Σ.1, ind_universes mdecl)
    (PCUICEnvironment.ind_params mdecl) (PCUICEnvironment.ind_kelim idecl)
    (ind_indices onib) (ind_ctors_sort onib) (ind_sort onib) ->
  (#|ind_ctors_sort onib| <= 1) * All Universe.is_prop (ind_ctors_sort onib).
Proof.
  intros kelim isp.
  unfold check_ind_sorts, universe_family. simpl.
  rewrite isp. simpl.
  induction (ind_ctors_sort onib); simpl; auto; try discriminate.
  apply not_prop_not_leq_prop in kelim.
  destruct l; simpl in *; try contradiction.
  destruct (universe_family a) eqn:Heq; try contradiction.
  intros leb.
  apply family_InProp in Heq. now constructor.
Qed.
 
Lemma type_local_ctx_All_local_assum_impl {cf:checker_flags} Σ 
  (P : context -> context -> term -> Type) {Γ Δ cs} : 
  (forall Γ' t, Σ ;;; Γ ,,, Γ' |- t : tSort cs  -> P Γ Γ' t) ->
  type_local_ctx (lift_typing typing) Σ Γ Δ cs ->
  All_local_assum (P Γ) Δ.
Proof.
  intros H.
  induction Δ; simpl; intros. constructor; intuition auto.
  destruct a as [na [b|] ty]; constructor; intuition auto.
Qed.

(* We prove that if the (partial) constructor application's type lands in Prop
   then the inductive type is in Prop and hence the constructor's sort is 
   Prop. Finally, all its arguments are in Prop because we additionally know
   that elimination to any type is allowed. *)

Lemma Is_proof_mkApps_tConstruct `{cf : checker_flags} (Σ : global_env_ext) Γ ind n u mdecl idecl args :
  check_univs = true ->
  wf Σ ->
  declared_inductive (fst Σ) mdecl ind idecl ->
  ind_kelim idecl <> InProp ->
  Is_proof Σ Γ (mkApps (tConstruct ind n u) args) ->
  #|ind_ctors idecl| <= 1 /\ ∥ All (Is_proof Σ Γ) (skipn (ind_npars mdecl) args) ∥.
Proof.
  intros checkunivs wfΣ decli kelim [tyc [tycs [hc [hty hp]]]].
  eapply inversion_mkApps in hc as [? [? [hc [hsp hcum]]]]; auto.
  eapply inversion_Construct in hc as [mdecl' [idecl' [cdecl' [wfΓ [declc [cu cum']]]]]]; auto.
  destruct (on_declared_constructor _ declc) as [[oi oib] [cs [Hnth onc]]].
  set (onib := declared_inductive_inv _ _ _ _ _ _ _ _ _) in *.
  clearbody onib. clear oib.
  eapply typing_spine_strengthen in hsp; eauto.
  eapply PCUICArities.typing_spine_weaken_concl in hsp; eauto.
  2:{ right; eexists; eauto. }
  pose proof (declared_inductive_inj decli (proj1 declc)) as [-> ->].
  assert (isWfArity_or_Type Σ Γ (type_of_constructor mdecl cdecl' (ind, n) u)).
  { eapply declared_constructor_valid_ty in declc; eauto. now right. }
  move: X hsp.
  unfold type_of_constructor.
  rewrite (onc.(cshape).(cshape_eq)).
  rewrite !subst_instance_constr_it_mkProd_or_LetIn !subst_it_mkProd_or_LetIn.
  rewrite - {1}(firstn_skipn (ind_npars mdecl) args).
  rewrite !subst_instance_constr_mkApps.
  simpl.
  autorewrite with len.
  rewrite !subst_mkApps Nat.add_0_r.
  rewrite !subst_inds_concl_head.
  destruct decli. now apply nth_error_Some_length in H0.
  destruct (le_dec (ind_npars mdecl) #|args|).
  * intros X hsp.
    eapply PCUICSpine.typing_spine_inv in hsp as [parsub [[sub wat] sp]]; auto.
    2:{ rewrite context_assumptions_subst subst_instance_context_assumptions.
        autorewrite with len.
        rewrite firstn_length_le //. symmetry; eapply onNpars. eauto. }
    rewrite !subst_it_mkProd_or_LetIn in X, sp.
    rewrite !subst_mkApps in sp.
    simpl in sp.
    eapply typing_spine_proofs in sp; eauto.
    destruct sp.
    specialize (l0 _ _ (proj1 declc) onib).
    pose proof (onc.(on_cargs)).
    pose proof (onib.(ind_sorts)).
    assert (Universe.is_prop (ind_sort onib)).
    { rewrite -(is_prop_subst_instance_univ u).
      apply (consistent_instance_ext_noprop cu).
      eapply leq_universe_prop in l0; intuition eauto. }
    eapply check_ind_sorts_is_prop in X1 as [nctors X1]; eauto.
    assert(#|ind_ctors_sort onib| = #|ind_ctors idecl|).
    clear wat X. clear -onib. pose proof (onib.(onConstructors)).
    eapply All2_length in X. now rewrite X. 
    rewrite H0 in nctors; split; auto.

    eapply nth_error_all in X1; eauto. simpl in X1.
    eapply type_local_ctx_instantiate in X0. 4:eapply cu.
    all: eauto. 2: destruct decli; eauto.
    rewrite subst_instance_context_app in X0.
    eapply weaken_type_local_ctx in X0; eauto.
    eapply (subst_type_local_ctx _ _) in X0; eauto.
    3:{ eapply subslet_app. 
      2:{ eapply (weaken_subslet _ _ _ _ []), PCUICArities.subslet_inds; eauto. } 
      eapply sub. }
    2:{ eapply PCUICWeakening.weaken_wf_local; auto.
        unshelve eapply on_constructor_inst in oi; eauto.
        destruct oi as [oi _].
        rewrite !subst_instance_context_app in oi.
        now eapply wf_local_app in oi. }

    apply s.
    rewrite subst_app_context in X0.
    rewrite -(context_subst_length _ _ _ sub) in X0.
    autorewrite with len in X0.
    eapply (type_local_ctx_All_local_assum_impl Σ 
      (fun Γ Γ' t => 
      ∑ s0 : Universe.t, Σ;;; Γ ,,, Γ' |- t : tSort s0 × Universe.is_prop s0)).
    2:eauto.
    intros. exists (subst_instance_univ u cs). intuition auto.
    now eapply is_prop_subst_instance.
  * intros _ sp.
    rewrite List.skipn_all2. lia.
    split; [|repeat constructor].
    pose proof (onc.(on_cargs)).
    pose proof (onib.(ind_sorts)).
    eapply check_ind_sorts_is_prop in X0 as [nctors X1]; eauto.
    assert(#|ind_ctors_sort onib| = #|ind_ctors idecl|).
    clear -onib. pose proof (onib.(onConstructors)).
    eapply All2_length in X. now rewrite X. now rewrite -H.
    rewrite -it_mkProd_or_LetIn_app in sp.
    eapply typing_spine_proofs in sp; eauto.
    { rewrite -(is_prop_subst_instance_univ u).
      apply (consistent_instance_ext_noprop cu).
      destruct sp as [_ Hs].
      specialize (Hs _ _ decli onib).
      eapply leq_universe_prop in Hs; intuition eauto. }
Qed.
    
Lemma elim_restriction_works_kelim `{cf : checker_flags} (Σ : global_env_ext) ind mind idecl :
  check_univs = true ->
  wf Σ ->
  declared_inductive (fst Σ) mind ind idecl ->
  ind_kelim idecl <> InProp -> Informative Σ ind.
Proof.
  intros cu wfΣ H indk.
  destruct (PCUICWeakeningEnv.on_declared_inductive wfΣ H) as [[]]; eauto.
  intros ?. intros.
  eapply declared_inductive_inj in H as []; eauto; subst idecl0 mind.
  eapply Is_proof_mkApps_tConstruct in X1; eauto.
  now eapply weakening_env_declared_inductive.
Qed.

Lemma elim_restriction_works `{cf : checker_flags} (Σ : global_env_ext) Γ T ind npar p c brs mind idecl : 
  check_univs = true ->
  wf Σ ->
  declared_inductive (fst Σ) mind ind idecl ->
  Σ ;;; Γ |- tCase (ind, npar) p c brs : T ->
  (Is_proof Σ Γ (tCase (ind, npar) p c brs) -> False) -> Informative Σ ind.
Proof.
  intros cu wfΣ decli HT H.
  eapply elim_restriction_works_kelim1 in HT; eauto.
  eapply elim_restriction_works_kelim; eauto.
  destruct HT; congruence.
Qed.

Lemma declared_projection_projs_nonempty `{cf : checker_flags} {Σ : global_env_ext} { mind ind p a} :
  wf Σ ->
  declared_projection Σ mind ind p a ->
  ind_projs ind <> [].
Proof.
  intros. destruct H. destruct H0.
  destruct (ind_projs ind); try congruence. destruct p.
  cbn in *. destruct n; inv H0.
Qed.

Lemma elim_restriction_works_proj_kelim1 `{cf : checker_flags} (Σ : global_env_ext) Γ T p c mind idecl :
  wf Σ ->
  declared_inductive (fst Σ) mind (fst (fst p)) idecl ->
  Σ ;;; Γ |- tProj p c : T ->
  (Is_proof Σ Γ (tProj p c) -> False) -> ind_kelim idecl = InType.
Proof.
  intros X H X0 H0.
  destruct p. destruct p. cbn in *.
  eapply inversion_Proj in X0 as (? & ? & ? & ? & ? & ? & ? & ? & ?) ; auto.
  destruct x2. cbn in *.
  pose (d' := d). destruct d' as [? _].
  eapply declared_inductive_inj in H as []; eauto. subst.
  pose proof (declared_projection_projs_nonempty X d).
  eapply PCUICWeakeningEnv.on_declared_projection in d; eauto.
  destruct d as (? & ? & ?). destruct p.
  inv o. inv o0.
  forward onProjections. eauto.
  inversion onProjections.
  clear - on_projs_elim. revert on_projs_elim. generalize (ind_kelim x1).
  intros. induction on_projs_elim; subst.
  - cbn. eauto.
Qed. (* elim_restriction_works_proj *)

Lemma elim_restriction_works_proj `{cf : checker_flags} (Σ : global_env_ext) Γ  p c mind idecl T :
  check_univs = true -> wf Σ ->
  declared_inductive (fst Σ) mind (fst (fst p)) idecl ->
  Σ ;;; Γ |- tProj p c : T ->
  (Is_proof Σ Γ (tProj p c) -> False) -> Informative Σ (fst (fst p)).
Proof.
  intros cu; intros. eapply elim_restriction_works_kelim; eauto.
  eapply elim_restriction_works_proj_kelim1 in H0; eauto.
  congruence.
Qed.

Lemma length_of_btys {ind mdecl' idecl' args' u' p} :
  #|build_branches_type ind mdecl' idecl' args' u' p| = #|ind_ctors idecl'|.
Proof.
  unfold build_branches_type. now rewrite mapi_length.
Qed.

Lemma length_map_option_out {A} l l' :
  @map_option_out A l = Some l' -> #|l| = #|l'|.
Proof.
  induction l as [|[x|] l] in l' |- *.
  - destruct l'; [reflexivity|discriminate].
  - cbn. destruct (map_option_out l); [|discriminate].
    destruct l'; [discriminate|]. inversion 1; subst; cbn; eauto.
  - discriminate.
Qed.

Lemma map_option_Some X (L : list (option X)) t : map_option_out L = Some t -> All2 (fun x y => x = Some y) L t.
Proof.
  intros. induction L in t, H |- *; cbn in *.
  - inv H. econstructor.
  - destruct a. destruct ?. all:inv H. eauto.
Qed.

Lemma tCase_length_branch_inv `{cf : checker_flags} (Σ : global_env_ext) Γ ind npar p n u args brs T m t :
  wf Σ ->
  Σ ;;; Γ |- tCase (ind, npar) p (mkApps (tConstruct ind n u) args) brs : T ->
  nth_error brs n = Some (m, t) ->
  (#|args| = npar + m)%nat.
Proof.
  intros. eapply inversion_Case in X0 as (u' & args' & mdecl' & idecl' & ps' & pty' & btys' & ? & ? & ? & ? & ? & ? & ? & ? & ?); eauto.
  subst. unfold build_case_predicate_type  in *.
  pose proof t1 as t1'.
  eapply inversion_mkApps in t1' as [A [_ [tc _]]]; auto.
  eapply inversion_Construct in tc as [mdecl [idecl [cdecl [_ [declc _]]]]]; auto. clear A.
  unshelve eapply Construct_Ind_ind_eq in t1; eauto.
  destruct on_declared_constructor as [[onind oib] [cs [Hnth onc]]].
  destruct t1 as [[t1 ->] _]. simpl in e. rewrite <- e.
  destruct (declared_inductive_inj d (proj1 declc)); subst mdecl' idecl'.
  f_equal. clear Hnth.
  eapply build_branches_type_lookup in e1. eauto.
  2:eauto.
  3:destruct declc; eauto.
  2:{ eapply (All2_impl a); firstorder. }
  destruct e1 as [nargs [br [brty [[[Hnth Hnth'] brtyped]]]]].
  epose proof (All2_nth_error _ _ _ a H).
  specialize (X0 Hnth').
  simpl in X0. destruct X0 as [[X0 _] _]. subst m.
  clear e0.
  set (decli := declared_inductive_inv _ _ _  _ _ _ _ _ _) in *.
  clear oib. clearbody decli.
  unshelve eapply branch_type_spec in e1; eauto.
  now destruct e1 as [e1 _].
Qed.

Section no_prop_leq_type.

Context `{cf : checker_flags}.
Variable Hcf : prop_sub_type = false.
Variable Hcf' : check_univs = true.


Lemma typing_leq_term (Σ : global_env_ext) Γ t t' T T' : 
  wf Σ.1 ->
  Σ ;;; Γ |- t : T ->
  Σ ;;; Γ |- t' : T' ->
  PCUICEquality.leq_term Σ t' t ->
  Σ ;;; Γ |- t' : T.
Proof.
  intros wfΣ Ht.
  revert Σ wfΣ Γ t T Ht t' T'.
  eapply (typing_ind_env 
  (fun Σ Γ t T =>
    forall t' T' : term, Σ ;;; Γ |- t' : T' -> PCUICEquality.leq_term Σ t' t -> Σ;;; Γ |- t' : T)
  (fun Σ Γ wfΓ => wf_local Σ Γ)); auto;intros Σ wfΣ Γ wfΓ; intros.
    1-13:match goal with
    [ H : PCUICEquality.leq_term _ _ _ |- _ ] => depelim H
    end.
  all:try solve [econstructor; eauto].
  13:{ eapply type_Cumul.
       eapply X1. eauto. eauto. 
       destruct X2; [left|right].
       red in i. apply i.
       exists s.π1. apply s.π2. auto.
    }
  - eapply inversion_Sort in X0 as [l' [_ [Inl' [-> ?]]]].
    eapply type_Cumul with (tSort (Universe.super l')).
    constructor; auto. left; eexists _, _; simpl; intuition eauto.
    constructor. constructor. apply leq_universe_super.
    apply x. auto.

  - eapply inversion_Prod in X4 as [s1' [s2' [Ha [Hb Hs]]]]; auto.
    specialize (X1 _ _ Ha). 
    specialize (X1 (PCUICEquality.eq_term_leq_term _ _ _ X5_1)).
    eapply context_conversion in Hb. 3:{ constructor. apply conv_ctx_refl. constructor.
      constructor; eauto. }
    all:eauto.
    2:{ constructor; eauto. now exists s1. }
    specialize (X3 _ _ Hb X5_2).
    econstructor; eauto.
    eapply context_conversion; eauto.
    constructor; pcuic. constructor. symmetry;  now constructor.
    constructor; pcuic.

  - eapply inversion_Lambda in X4 as (s & B & dom & codom & cum); auto.
    specialize (X1 _ _ dom (PCUICEquality.eq_term_leq_term _ _ _ X5_1)).
    assert(conv_context Σ (Γ ,, vass na ty) (Γ ,, vass n t)).
    { repeat constructor; pcuic. }
    specialize (X3 t0 B).
    forward X3 by eapply context_conversion; eauto; pcuic.
    econstructor.
    econstructor. eauto. instantiate (1 := bty).
    eapply context_conversion; eauto; pcuic.
    constructor; pcuic. constructor; pcuic. symmetry; constructor; auto.
    have tyl := type_Lambda _ _ _ _ _ _ _ X0 X2.
    now eapply PCUICValidity.validity in tyl.
    eapply congr_cumul_prod; eauto.
    constructor; auto. reflexivity.
    
  - eapply inversion_LetIn in X6 as (s1' & A & dom & bod & codom & cum); auto.
    specialize (X1 _ _ dom (PCUICEquality.eq_term_leq_term _ _ _ X7_2)).
    specialize (X3 _ _ bod (PCUICEquality.eq_term_leq_term _ _ _ X7_1)).
    assert(conv_context Σ (Γ ,, vdef na t ty) (Γ ,, vdef n b b_ty)).
    { repeat constructor; pcuic. }
    specialize (X5 u A).
    forward X5 by eapply context_conversion; eauto; pcuic.
    specialize (X5 X7_3).
    econstructor.
    econstructor. eauto. eauto.
    instantiate (1 := b'_ty).
    eapply context_conversion; eauto.
    apply conv_context_sym; auto.
    pcuic. eapply PCUICValidity.validity; eauto.
    econstructor; eauto.
    eapply cum_LetIn; pcuic.
    
  - eapply inversion_App in X4 as (na' & A' & B' & hf & ha & cum); auto.
    specialize (X1 _ _ hf X5_1).
    specialize (X3 _ _ ha (PCUICEquality.eq_term_leq_term _ _ _ X5_2)).
    econstructor.
    econstructor; [eapply X1|eapply X3].
    eapply PCUICValidity.validity; pcuic.
    eapply type_App; eauto.
    eapply conv_cumul. eapply (subst_conv Γ [vass na A] [vass na A] []); pcuic.
    repeat constructor. now rewrite subst_empty.
    repeat constructor. now rewrite subst_empty.
    eapply PCUICValidity.validity in X0; auto.
    apply PCUICArities.isWAT_tProd in X0 as [tyA]; auto.
    constructor; auto.

  - eapply inversion_Const in X1 as [decl' [wf [declc [cu cum]]]]; auto.
    econstructor; eauto.
    econstructor; eauto.
    eapply PCUICValidity.validity; eauto.
    econstructor; eauto.
    eapply conv_cumul. constructor.
    pose proof (declared_constant_inj _ _ H declc); subst decl'.
    eapply eq_term_upto_univ_subst_instance_constr; eauto; typeclasses eauto.
  
  - eapply inversion_Ind in X1 as [decl' [idecl' [wf [declc [cu cum]]]]]; auto.
    econstructor; eauto.
    econstructor; eauto.
    eapply PCUICValidity.validity; eauto.
    econstructor; eauto.
    eapply conv_cumul. constructor.
    pose proof (declared_inductive_inj isdecl declc) as [-> ->].
    eapply eq_term_upto_univ_subst_instance_constr; eauto; typeclasses eauto.
  
  - eapply inversion_Construct in X1 as [decl' [idecl' [cdecl' [wf [declc [cu cum]]]]]]; auto.
    econstructor; eauto.
    econstructor; eauto.
    eapply PCUICValidity.validity; eauto.
    econstructor; eauto.
    pose proof (declared_constructor_inj isdecl declc) as [-> [-> ->]].
    unfold type_of_constructor.
    transitivity (subst0 (inds (inductive_mind (ind, i).1) u (ind_bodies mdecl))
    (subst_instance_constr u0 cdecl'.1.2)).
    * eapply conv_cumul.
      eapply (conv_subst_conv _ Γ _ _ []); eauto.
      { unfold inds.
        generalize #|ind_bodies mdecl|.
        induction n; simpl; constructor; auto.
        constructor. constructor. auto. }
      eapply subslet_untyped_subslet.
      eapply (weaken_subslet _ _ _ Γ []); eauto.
      eapply PCUICArities.subslet_inds; eauto.
      destruct declc; eauto.
      eapply subslet_untyped_subslet.
      eapply (weaken_subslet _ _ _ Γ []); eauto.
      eapply PCUICArities.subslet_inds; eauto.
      destruct declc; eauto.
    * constructor. eapply PCUICEquality.subst_leq_term.
      eapply PCUICEquality.eq_term_leq_term.
      eapply eq_term_upto_univ_subst_instance_constr; eauto; typeclasses eauto.

  - eapply inversion_Case in X6 as (u' & args' & mdecl' & idecl' & ps' & pty' & btys' & inv); auto.
    intuition auto.
    intuition auto.
    eapply type_Cumul.
    econstructor; eauto.
    eapply PCUICValidity.validity; eauto.
    eapply (type_Case _ _ (ind, npar)). eapply isdecl.
    all:eauto.
    eapply (All2_impl X5); firstorder.
    eapply conv_cumul.
    eapply mkApps_conv_args; pcuic.
    eapply All2_app. simpl in *.
    2:constructor; pcuic.
    eapply All2_skipn.
    clear -wfΣ a5 X4 X7_2.
    specialize (X4 _ _ a5 (PCUICEquality.eq_term_leq_term _ _ _ X7_2)).
    eapply (principal_type_ind a5 X4).
    
  - eapply inversion_Proj in X3 as (u' & mdecl' & idecl' & pdecl' & args' & inv); auto.
    intuition auto.
    eapply type_Cumul.
    econstructor; eauto.
    eapply PCUICValidity.validity; eauto.
    eapply type_Proj; eauto.
    specialize (X2 _ _ a0 (PCUICEquality.eq_term_leq_term _ _ _ X4)).
    pose proof (principal_type_ind X2 a0) as [Ruu' X3].
    transitivity (subst0 (c :: List.rev args) (subst_instance_constr u' pdecl'.2)).
    eapply conv_cumul.
    destruct (on_declared_projection wfΣ a) as [[oni oib] onp].
    destruct p as [[ind n] k].
    red in onp. simpl in onp.
    match goal with 
    [ _ : on_type _ _ ?Γ _ |- _ ] => set(ctx := Γ) in *
    end.
    eapply (conv_subst_conv _ Γ ctx ctx []); eauto.
    constructor. now constructor.
    eapply All2_rev. apply All2_sym. apply (All2_impl X3). intros; now symmetry.
    eapply subslet_untyped_subslet; eauto.
    eapply projection_subslet; eauto.
    eapply subslet_untyped_subslet; eauto.
    eapply projection_subslet; eauto.
    constructor. eapply PCUICEquality.subst_leq_term.
    destruct (declared_projection_inj a isdecl) as [<- [<- <-]].
    subst ty.
    eapply PCUICEquality.eq_term_leq_term.
    eapply eq_term_upto_univ_subst_instance_constr; eauto; try typeclasses eauto.
    now symmetry.

  - eapply inversion_Fix in X2 as (decl' & fixguard' & Hnth & types' & bodies & cum); auto.
    eapply type_Cumul.
    econstructor; eauto.
    eapply PCUICValidity.validity; eauto.
    econstructor. 2:eapply H0. all:eauto.
    eapply (All_impl X0); firstorder.
    eapply (All_impl X1); firstorder.
    eapply All2_nth_error in a; eauto.
    destruct a as [[eqty _] _].
    constructor. now apply PCUICEquality.eq_term_leq_term.
  
  - eapply inversion_CoFix in X2 as (decl' & fixguard' & Hnth & types' & bodies & cum); auto.
    eapply type_Cumul.
    econstructor; eauto.
    eapply PCUICValidity.validity; eauto.
    eapply type_CoFix. 2:eapply H. all:eauto.
    eapply (All_impl X0); firstorder.
    eapply (All_impl X1); firstorder.
    eapply All2_nth_error in a; eauto.
    destruct a as [[eqty _] _].
    constructor. now apply PCUICEquality.eq_term_leq_term.
Qed.

Lemma is_prop_bottom {Σ Γ T s s'} :
  wf Σ.1 ->
  Σ ;;; Γ |- T <= tSort s ->
  Σ ;;; Γ |- T <= tSort s' ->
  Universe.is_prop s -> Universe.is_prop s'.
Proof.
  intros wfΣ hs hs'.
  destruct (cumul_sort_confluence _ wfΣ hs hs') as [x' [conv [leq leq']]].
  intros isp.
  unshelve eapply (leq_prop_is_prop _ _ leq'); auto.
  now unshelve eapply (leq_prop_is_prop _ _ leq).
Qed.

Lemma leq_term_prop_sorted_l {Σ Γ v v' u u'} :
  wf Σ.1 ->
  PCUICEquality.leq_term (global_ext_constraints Σ) v v' ->
  Σ;;; Γ |- v : tSort u ->
  Σ;;; Γ |- v' : tSort u' -> Universe.is_prop u -> 
  leq_universe (global_ext_constraints Σ) u' u.
Proof.
  intros wfΣ leq hv hv' isp.
  pose proof hv as hv0.
  eapply typing_leq_term in hv. 4:eapply leq. all:eauto.
  destruct (principal_typing _ wfΣ hv hv0) as [C [cum0 [cum1 tyC]]].
  pose proof (is_prop_bottom wfΣ cum1 cum0 isp).
  apply leq_prop_prop; auto.
Qed.

Lemma leq_term_prop_sorted_r {Σ Γ v v' u u'} :
  wf Σ.1 ->
  PCUICEquality.leq_term (global_ext_constraints Σ) v v' ->
  Σ;;; Γ |- v : tSort u ->
  Σ;;; Γ |- v' : tSort u' -> Universe.is_prop u' -> 
  leq_universe (global_ext_constraints Σ) u u'.
Proof.
  intros wfΣ leq hv hv' isp.
  pose proof hv as hv0.
  eapply typing_leq_term in hv. 4:eapply leq. all:eauto.
  destruct (principal_typing _ wfΣ hv hv0) as [C [cum0 [cum1 tyC]]].
  pose proof (is_prop_bottom wfΣ cum0 cum1 isp).
  now apply leq_prop_prop.
Qed.

Lemma cumul_prop (Σ : global_env_ext) Γ A B u u' :
  wf Σ ->
  Universe.is_prop u ->
  (((Σ ;;; Γ |- A : tSort u) * (Σ ;;; Γ |- B : tSort u')) + 
   ((Σ ;;; Γ |- B : tSort u) * (Σ ;;; Γ |- A : tSort u')))%type ->
  Σ ;;; Γ |- A <= B ->
  ((Σ ;;; Γ |- A : tSort u) * (Σ ;;; Γ |- B : tSort u))%type.
Proof.
  intros wfΣ propu.
  intros [[HA HB]|[HB HA]] cum; split; auto;
  apply cumul_alt in cum as [v [v' [[redv redv'] leq]]].
  - eapply type_Cumul with (tSort u'); eauto.
    left; eexists _, _; simpl; intuition eauto. now apply typing_wf_local in HA.
    constructor. constructor.
    eapply subject_reduction in redv; eauto.
    eapply subject_reduction in redv'; eauto.
    eapply leq_term_prop_sorted_l; eauto.
  - eapply subject_reduction in redv; eauto.
    eapply subject_reduction in redv'; eauto.
    eapply leq_term_prop_sorted_r in leq; eauto.
    eapply type_Cumul with (tSort u'); eauto.
    left; eexists _, _; simpl; intuition eauto. now apply typing_wf_local in HA.
    constructor. constructor. auto.
Qed.

Lemma cumul_prop_r_is_type (Σ : global_env_ext) Γ A B u :
  wf Σ ->
  Universe.is_prop u ->
  isWfArity_or_Type Σ Γ A ->
  Σ ;;; Γ |- B : tSort u ->
  Σ ;;; Γ |- A <= B ->
  isType Σ Γ A.
Proof.
  intros.
  destruct X0; eauto.
  destruct i as [ctx [s [Hd eq]]].
  exists u.
  apply PCUICArities.destArity_spec_Some in Hd.
  simpl in Hd. subst A.
  revert u H Γ eq B X1 X2. revert ctx. intros ctx.
  change (list context_decl) with context in ctx.
  induction ctx using ctx_length_rev_ind; simpl in *; intros.
  - elimtype False.
    eapply invert_cumul_sort_l in X2 as [u' [red leq]]; auto.
    eapply subject_reduction in red; eauto.
    eapply inversion_Sort in red as [l [wf [inl [eq' lt]]]]; auto.
    subst u'.
    eapply cumul_Sort_inv in lt.
    now apply is_prop_gt in lt.
  - rewrite app_context_assoc in eq.
    pose proof eq as eq'.
    eapply All_local_env_app in eq' as [wfΓ wf']. depelim wfΓ;
    rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /= in X2 |- *.
    + eapply invert_cumul_prod_l in X2 as (na' & A & B' & (red & conv) & cum).
      eapply subject_reduction in X1. 3:eassumption. all:auto.
      eapply inversion_Prod in X1 as (s1 & s2 & tA & tB' & cum'); auto.
      eapply cumul_Sort_inv in cum'.
      specialize (X0 Γ ltac:(reflexivity) u H _ eq B').
      forward X0.
      eapply type_Cumul.
      eapply context_conversion; eauto.
      constructor; pcuic. constructor. now symmetry.
      constructor; auto.
      left. eexists _, _; simpl; intuition eauto. constructor; pcuic.
      do 2 constructor. etransitivity; eauto.
      eapply leq_universe_product.
      specialize (X0 cum).
      eapply type_Cumul.
      econstructor; eauto. eapply l.π2.
      left; eexists _, _; simpl; intuition auto.
      do 2 constructor. now eapply impredicative_product.
    + eapply invert_cumul_letin_l in X2; auto.
      eapply type_Cumul.
      econstructor; eauto. eapply l.π2.
      instantiate (1 := (tSort u)).
      eapply X0; auto.
      eapply (PCUICWeakening.weakening _ _ [vdef na b t]) in X1. simpl in X1.
      eapply X1. all:eauto.
      constructor; auto.
      eapply (PCUICWeakening.weakening_cumul _ _ [] [vdef na b t]) in X2; auto. simpl in X2.
      etransitivity; eauto.
      eapply red_cumul. apply PCUICSpine.red_expand_let.
      constructor; pcuic.
      left; eexists _, _; simpl; intuition eauto.
      eapply red_cumul, PCUICReduction.red1_red.
      constructor.
Qed.

Lemma cumul_prop_l_is_type (Σ : global_env_ext) Γ A B u :
  wf Σ ->
  Universe.is_prop u ->
  isWfArity_or_Type Σ Γ B ->
  Σ ;;; Γ |- A : tSort u ->
  Σ ;;; Γ |- A <= B ->
  isType Σ Γ B.
Proof.
  intros.
  destruct X0; eauto.
  destruct i as [ctx [s [Hd eq]]].
  exists u.
  apply PCUICArities.destArity_spec_Some in Hd.
  simpl in Hd. subst B.
  revert u H Γ eq A X1 X2. revert ctx. intros ctx.
  change (list context_decl) with context in ctx.
  induction ctx using ctx_length_rev_ind; simpl in *; intros.
  - elimtype False.
    eapply invert_cumul_sort_r in X2 as [u' [red leq]]; auto.
    eapply subject_reduction in red; eauto.
    eapply inversion_Sort in red as [l [wf [inl [eq' lt]]]]; auto.
    subst u'.
    eapply cumul_Sort_inv in lt.
    now apply is_prop_gt in lt.
  - rewrite app_context_assoc in eq.
    pose proof eq as eq'.
    eapply All_local_env_app in eq' as [wfΓ wf']. depelim wfΓ;
    rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /= in X2 |- *.
    + eapply invert_cumul_prod_r in X2 as (na' & A' & B' & (red & conv) & cum).
      eapply subject_reduction in X1. 3:eassumption. all:auto.
      eapply inversion_Prod in X1 as (s1 & s2 & tA & tB' & cum'); auto.
      eapply cumul_Sort_inv in cum'.
      specialize (X0 Γ ltac:(reflexivity) u H _ eq B').
      forward X0.
      eapply type_Cumul.
      eapply context_conversion; eauto.
      constructor; pcuic. constructor. now symmetry.
      constructor; auto.
      left. eexists _, _; simpl; intuition eauto. constructor; pcuic.
      do 2 constructor. etransitivity; eauto.
      eapply leq_universe_product.
      specialize (X0 cum).
      eapply type_Cumul.
      econstructor; eauto. eapply l.π2.
      left; eexists _, _; simpl; intuition auto.
      do 2 constructor. now eapply impredicative_product.
    + eapply invert_cumul_letin_r in X2; auto.
      eapply type_Cumul.
      econstructor; eauto. eapply l.π2.
      instantiate (1 := (tSort u)).
      eapply X0; auto.
      eapply (PCUICWeakening.weakening _ _ [vdef na b t]) in X1. simpl in X1.
      eapply X1. all:eauto.
      constructor; auto.
      eapply (PCUICWeakening.weakening_cumul _ _ [] [vdef na b t]) in X2; auto. simpl in X2.
      etransitivity; eauto.
      eapply conv_cumul, conv_sym, red_conv. apply PCUICSpine.red_expand_let.
      constructor; pcuic.
      left; eexists _, _; simpl; intuition eauto.
      eapply red_cumul, PCUICReduction.red1_red.
      constructor.
Qed.

Lemma cumul_prop1 (Σ : global_env_ext) Γ A B u :
  wf Σ ->
  Universe.is_prop u ->
  isWfArity_or_Type Σ Γ A ->
  Σ ;;; Γ |- B : tSort u ->
  Σ ;;; Γ |- A <= B ->
  Σ ;;; Γ |- A : tSort u.
Proof.
  intros.
  eapply cumul_prop_r_is_type in X0; eauto.
  destruct X0 as [s Hs].
  eapply cumul_prop in H. 4:eauto. firstorder. auto.
  right; eauto.
Qed.

Lemma cumul_prop2 (Σ : global_env_ext) Γ A B u :
  wf Σ ->
  Universe.is_prop u ->
  isWfArity_or_Type Σ Γ B ->
  Σ ;;; Γ |- A <= B ->
  Σ ;;; Γ |- A : tSort u ->
  Σ ;;; Γ |- B : tSort u.
Proof.
  intros.
  eapply cumul_prop_l_is_type in X0; eauto.
  destruct X0 as [s Hs].
  eapply cumul_prop in H. 4:eauto. firstorder. auto.
  left; eauto.
Qed.

End no_prop_leq_type.
