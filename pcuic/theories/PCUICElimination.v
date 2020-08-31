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
      wf_ext Σ' ->
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
                                   [? [? [? [? [? [? [ht0 [? [? ?]]]]]]]]]]]]]]]]; auto.
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
  assert (watiapp := env_prop_typing  _ _ validity _ _ _ _ _ ht0).
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

Lemma elim_sort_intype {cf:checker_flags} Σ mdecl ind idecl ind_indices ind_sort cshapes :
  universe_family ind_sort = InProp ->
  leb_sort_family InType (elim_sort_prop_ind cshapes) ->
  on_constructors (lift_typing typing)
    (Σ, ind_universes mdecl) mdecl 
    (inductive_ind ind) idecl ind_indices
    (ind_ctors idecl) cshapes ->
  (#|ind_ctors idecl| = 0) + 
  (∑ cdecl cshape, 
    (ind_ctors idecl = [cdecl]) * 
    (cshapes = [cshape]) * 
    (universe_family cshape.(cshape_sort) = InProp) *
    (on_constructor (lift_typing typing) (Σ, ind_universes mdecl) mdecl 
        (inductive_ind ind) idecl ind_indices cdecl cshape))%type.
Proof.
  intros uf lein onc.
  induction onc; simpl in *.
  left; auto.
  destruct l' as [|c cs].
  - simpl in *. depelim onc.
    right.
    destruct (universe_family y.(cshape_sort)) eqn:heq; try discriminate.
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

Lemma wf_ext_wf {cf:checker_flags} Σ : wf_ext Σ -> wf Σ.
Proof. move=> wfe; apply wfe. Qed.
Hint Resolve wf_ext_wf : core.

Lemma typing_spine_proofs {cf:checker_flags} Σ Γ Δ ind u args' args T' s :
  check_univs ->
  wf_ext Σ ->
  Σ ;;; Γ |-  T' : tSort s ->
  typing_spine Σ Γ (it_mkProd_or_LetIn Δ (mkApps (tInd ind u) args')) args T' ->
  ((All_local_assum (fun Γ' t =>
      (∑ s, (Σ ;;; Γ ,,, Γ' |- t : tSort s) * Universe.is_prop s)%type) Δ ->
    ∥ All (Is_proof Σ Γ) args ∥) *
    (forall mdecl idecl 
    (Hdecl : declared_inductive Σ.1 mdecl ind idecl)
    (oib : on_ind_body (lift_typing typing) (Σ.1, ind_universes mdecl)
      (inductive_mind ind) mdecl (inductive_ind ind) idecl),
      consistent_instance_ext Σ (ind_universes mdecl) u ->
      Universe.is_prop s -> Universe.is_prop (subst_instance_univ u oib.(ind_sort))))%type.
Proof.
  intros checku wfΣ Ht.
  induction Δ using ctx_length_rev_ind in Γ, args', args, T', Ht |- *; simpl; intros sp.
  - depelim sp. repeat constructor. 
    * eapply invert_cumul_ind_l in c as [ui' [l' [red  [Req argeq]]]] => //.
      intros mdecl idecl decli oib cu.
      eapply subject_reduction in Ht; eauto.
      eapply inversion_mkApps in Ht as [A [tInd sp]]; auto.
      eapply inversion_Ind in tInd as [mdecl' [idecl' [wfΓ [decli' [cu' cum]]]]]; auto.
      destruct (declared_inductive_inj decli decli'); subst mdecl' idecl'.
      clear decli'.
      eapply typing_spine_strengthen in sp; eauto.
      rewrite (oib.(ind_arity_eq)) in sp.
      rewrite !subst_instance_constr_it_mkProd_or_LetIn in sp.
      rewrite -it_mkProd_or_LetIn_app in sp.
      eapply typing_spine_it_mkProd_or_LetIn_full_inv in sp; auto.
      rewrite (is_prop_subst_instance_univ u).
      apply (consistent_instance_ext_noprop cu).
      intros props; eapply leq_universe_prop in sp; eauto.
      rewrite (is_prop_subst_instance_univ ui') in sp => //.
      now apply (consistent_instance_ext_noprop cu'). apply wfΣ.
      
    * eapply cumul_Prod_r_inv in c; auto.
      destruct c as [na' [dom' [codom' [[red _] ?]]]].
      eapply red_mkApps_tInd in red as [? [? ?]] => //; auto. solve_discr.

  - destruct d as [na [b|] ty].
    + rewrite it_mkProd_or_LetIn_app in sp.
      simpl in sp.
      eapply PCUICArities.typing_spine_letin_inv in sp => //; auto.
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
      depelim Ht2; simpl in H3; noconf H3. apply l0.
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
        destruct H; auto.
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
    (ind_indices onib) (ind_cshapes onib) (ind_sort onib) ->
  (#|ind_cshapes onib| <= 1) * All (fun cs => Universe.is_prop cs.(cshape_sort)) (ind_cshapes onib).
Proof.
  intros kelim isp.
  unfold check_ind_sorts, universe_family. simpl.
  rewrite isp. simpl.
  induction (ind_cshapes onib); simpl; auto; try discriminate.
  apply not_prop_not_leq_prop in kelim.
  destruct l; simpl in *; try contradiction.
  destruct (universe_family a.(cshape_sort)) eqn:Heq; try contradiction.
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
  wf_ext Σ ->
  declared_inductive (fst Σ) mdecl ind idecl ->
  ind_kelim idecl <> InProp ->
  Is_proof Σ Γ (mkApps (tConstruct ind n u) args) ->
  #|ind_ctors idecl| <= 1 /\ ∥ All (Is_proof Σ Γ) (skipn (ind_npars mdecl) args) ∥.
Proof.
  intros checkunivs HΣ decli kelim [tyc [tycs [hc [hty hp]]]].
  assert (wfΣ : wf Σ) by apply HΣ.
  eapply inversion_mkApps in hc as [? [hc hsp]]; auto.
  eapply inversion_Construct in hc as [mdecl' [idecl' [cdecl' [wfΓ [declc [cu cum']]]]]]; auto.
  destruct (on_declared_constructor _ declc) as [[oi oib] [cs [Hnth onc]]].
  set (onib := declared_inductive_inv _ _ _ _) in *.
  clearbody onib. clear oib.
  eapply typing_spine_strengthen in hsp; eauto.
  pose proof (declared_inductive_inj decli (proj1 declc)) as [-> ->].
  assert (isWfArity_or_Type Σ Γ (type_of_constructor mdecl cdecl' (ind, n) u)).
  { eapply PCUICInductiveInversion.declared_constructor_valid_ty in declc; eauto. now right. }
  move: X hsp.
  unfold type_of_constructor.
  rewrite [cdecl'.1.2](onc.(cstr_eq)).
  rewrite !subst_instance_constr_it_mkProd_or_LetIn !subst_it_mkProd_or_LetIn.
  rewrite - {1}(firstn_skipn (ind_npars mdecl) args).
  rewrite !subst_instance_constr_mkApps.
  simpl.
  autorewrite with len.
  rewrite !subst_mkApps.
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
    specialize (i _ _ (proj1 declc) onib cu hp). 
    
    pose proof (onc.(on_cargs)).
    pose proof (onib.(ind_sorts)).
    assert (Universe.is_prop (ind_sort onib)).
    { rewrite -(is_prop_subst_instance_univ u) => //.
      now apply (consistent_instance_ext_noprop cu). }
    eapply check_ind_sorts_is_prop in X1 as [nctors X1]; eauto.
    assert(#|ind_cshapes onib| = #|ind_ctors idecl|).
    clear wat X. clear -onib. pose proof (onib.(onConstructors)).
    eapply All2_length in X. now rewrite X. 
    rewrite H0 in nctors; split; auto.

    eapply nth_error_all in X1; eauto. simpl in X1.
    eapply type_local_ctx_instantiate in X0. 4:eapply cu.
    all: eauto.
    rewrite subst_instance_context_app in X0.
    eapply weaken_type_local_ctx in X0; eauto.
    eapply (subst_type_local_ctx _ _) in X0; eauto.
    3:{ eapply subslet_app. 
      2:{ eapply (weaken_subslet _ _ _ _ []), PCUICArities.subslet_inds; eauto. } 
      eapply sub. }
    2:{ eapply PCUICWeakening.weaken_wf_local; auto.
        unshelve eapply PCUICInductiveInversion.on_constructor_inst in oi; eauto.
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
    intros. exists (subst_instance_univ u cs.(cshape_sort)). intuition auto.
    now eapply is_prop_subst_instance.
  * intros _ sp.
    rewrite List.skipn_all2. lia.
    split; [|repeat constructor].
    pose proof (onc.(on_cargs)).
    pose proof (onib.(ind_sorts)).
    eapply check_ind_sorts_is_prop in X0 as [nctors X1]; eauto.
    assert(#|ind_cshapes onib| = #|ind_ctors idecl|).
    clear -onib. pose proof (onib.(onConstructors)).
    eapply All2_length in X. now rewrite X. now rewrite -H.
    rewrite -it_mkProd_or_LetIn_app in sp.
    eapply typing_spine_proofs in sp; eauto.
    destruct sp as [_ sp]. specialize (sp _ _ decli onib cu hp).
    { rewrite -(is_prop_subst_instance_univ u) //.
      now apply (consistent_instance_ext_noprop cu). }
Qed.
    
Lemma elim_restriction_works_kelim `{cf : checker_flags} (Σ : global_env_ext) ind mind idecl :
  check_univs = true ->
  wf_ext Σ ->
  declared_inductive (fst Σ) mind ind idecl ->
  ind_kelim idecl <> InProp -> Informative Σ ind.
Proof.
  intros cu HΣ H indk.
  assert (wfΣ : wf Σ) by apply HΣ.
  destruct (PCUICWeakeningEnv.on_declared_inductive wfΣ H) as [[]]; eauto.
  intros ?. intros.
  eapply declared_inductive_inj in H as []; eauto; subst idecl0 mind.
  eapply Is_proof_mkApps_tConstruct in X1; tea.
  now eapply weakening_env_declared_inductive.
Qed.

Lemma elim_restriction_works `{cf : checker_flags} (Σ : global_env_ext) Γ T ind npar p c brs mind idecl : 
  check_univs = true ->
  wf_ext Σ ->
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
  pose proof (PCUICWeakeningEnv.on_declared_projection X d) as [oni onp].
  simpl in onp. destruct ind_cshapes as [|? []]; try contradiction.
  destruct onp as (((? & ?) & ?) & ?).
  inv o. auto.
Qed. (* elim_restriction_works_proj *)

Lemma elim_restriction_works_proj `{cf : checker_flags} (Σ : global_env_ext) Γ  p c mind idecl T :
  check_univs = true -> wf_ext Σ ->
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
  intros. eapply inversion_Case in X0 as (u' & args' & mdecl' & idecl' & ps' & pty' & btys' & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?); eauto.
  subst. unfold build_case_predicate_type  in *.
  pose proof t1 as t1'.
  eapply inversion_mkApps in t1' as [A [tc _]]; auto.
  eapply inversion_Construct in tc as [mdecl [idecl [cdecl [_ [declc _]]]]]; auto. clear A.
  unshelve eapply PCUICInductiveInversion.Construct_Ind_ind_eq in t1; eauto.
  destruct on_declared_constructor as [[onind oib] [cs [Hnth onc]]].
  destruct t1 as [[t1 ->] _]. simpl in e. rewrite <- e.
  destruct (declared_inductive_inj d (proj1 declc)); subst mdecl' idecl'.
  f_equal. clear Hnth.
  eapply build_branches_type_lookup in e2. eauto.
  2:eauto.
  3:destruct declc; eauto.
  2:{ eapply (All2_impl a); firstorder. }
  destruct e2 as [nargs [br [brty [[[Hnth Hnth'] brtyped]]]]].
  epose proof (All2_nth_error _ _ _ a H).
  specialize (X0 Hnth').
  simpl in X0. destruct X0 as [[X0 _] _]. subst m.
  clear e0.
  set (decli := declared_inductive_inv _ _ _ _) in *.
  clear oib. clearbody decli.
  unshelve eapply branch_type_spec in e2; eauto.
  now destruct e2 as [e2 _].
Qed.

Section no_prop_leq_type.

Context `{cf : checker_flags}.
Variable Hcf : prop_sub_type = false.
Variable Hcf' : check_univs = true.



Lemma is_prop_bottom {Σ Γ T s s'} :
  wf_ext Σ ->
  Σ ;;; Γ |- T <= tSort s ->
  Σ ;;; Γ |- T <= tSort s' ->
  Universe.is_prop s -> Universe.is_prop s'.
Proof.
  intros wfΣ hs hs'.
  destruct (cumul_sort_confluence _ wfΣ.1 hs hs') as [x' [conv [leq leq']]].
  intros isp.
  unshelve eapply (leq_prop_is_prop _ _ _ _ leq'); auto.
  now unshelve eapply (leq_prop_is_prop _ _ _ _ leq).
Qed.

Lemma prop_sort_eq {Σ Γ u u'} : Universe.is_prop u -> Universe.is_prop u' -> Σ ;;; Γ |- tSort u = tSort u'.
Proof.
  move=> isp isp'.
  constructor. constructor. 
  red. rewrite Hcf'.
  red. intros. now rewrite (is_prop_val _ isp) (is_prop_val _ isp').
Qed.

Lemma is_prop_cum_r {Σ Γ T s} : 
  wf_ext Σ ->
  Universe.is_prop s ->
  Σ ;;; Γ |- T <= tSort s <~> Σ ;;; Γ |- T = tSort s.
Proof.
  move=> isp; split=> Ht.
  eapply invert_cumul_sort_r in Ht as [u' [hr leq]].
  eapply conv_trans with (tSort u'); eauto.
  eapply leq_prop_is_prop in leq; eauto.
  now eapply prop_sort_eq.
  now eapply conv_cumul.
Qed.  

Lemma is_prop_cum_l {Σ Γ T s} : 
  wf_ext Σ ->
  Universe.is_prop s ->
  Σ ;;; Γ |- tSort s <= T <~> Σ ;;; Γ |- T = tSort s.
Proof.
  move=> isp; split=> Ht.
  eapply invert_cumul_sort_l in Ht as [u' [hr leq]].
  eapply conv_trans with (tSort u'); eauto.
  eapply leq_prop_is_prop in leq; eauto.
  now eapply prop_sort_eq.
  now eapply conv_cumul.
Qed.

Lemma is_prop_cum_sym {Σ Γ T s} : 
  wf_ext Σ ->
  Universe.is_prop s ->
  Σ ;;; Γ |- tSort s <= T <~> Σ ;;; Γ |- T <= tSort s.
Proof.
  move=> isp; split=> Ht.
  eapply is_prop_cum_l in  Ht; eauto.
  eapply is_prop_cum_r; eauto.
  eapply is_prop_cum_l; eauto.
  eapply is_prop_cum_r; eauto.
Qed.

Require Import PCUICReduction.

Lemma is_prop_arity_cum_sym {Σ Γ T s Δ} : 
  wf_ext Σ ->
  Universe.is_prop s ->
  Σ ;;; Γ |- it_mkProd_or_LetIn Δ (tSort s) <= T <~>
  Σ ;;; Γ |- T <= it_mkProd_or_LetIn Δ (tSort s).
Proof.
  move=> wfext isp.
  revert Γ T; induction Δ using ctx_length_rev_ind; intros Γ' T.
  - simpl. now eapply is_prop_cum_sym.
  - destruct d as [na [b|] ty]; simpl;
      rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /=.
    + split => HT.
      eapply invert_cumul_letin_l in HT; auto.
      rewrite /subst1 subst_it_mkProd_or_LetIn /= in HT.
      specialize (X (subst_context [b] 0 Γ) ltac:(autorewrite with len; auto)).
      eapply cumul_trans. 2:eapply X. auto. auto.
      eapply red_cumul_cumul_inv. eapply red1_red; repeat constructor.
      now rewrite /subst1 subst_it_mkProd_or_LetIn.

      eapply invert_cumul_letin_r in HT; auto.
      rewrite /subst1 subst_it_mkProd_or_LetIn /= in HT.
      specialize (X (subst_context [b] 0 Γ) ltac:(autorewrite with len; auto) ).
      eapply cumul_trans. auto. 2:eapply X.
      eapply red_cumul_cumul. eapply red1_red; repeat constructor.
      now rewrite /subst1 subst_it_mkProd_or_LetIn. assumption.

    + split => HT.
      eapply invert_cumul_prod_l in HT as [? [? [? [[red eq] leq]]]]; auto.
      eapply cumul_trans with (tProd x x0 x1); auto.
      eapply red_cumul; auto. eapply cumul_trans. auto. eapply cumul_Prod_l.
      symmetry; eauto.  eapply cumul_Prod_r.
      specialize (X Γ ltac:(reflexivity)). now eapply X.

      eapply invert_cumul_prod_r in HT as [? [? [? [[red eq] leq]]]]; auto.
      eapply cumul_trans with (tProd na ty x1); auto.
      2:{ eapply red_cumul_cumul_inv. eauto. eapply cumul_Prod_l; auto. }
      eapply cumul_Prod_r. 
      specialize (X Γ ltac:(reflexivity)). now eapply X.
Qed.

Lemma is_prop_arity_cum_l_eq {Σ Γ T s Δ} : 
  wf_ext Σ ->
  Universe.is_prop s ->
  Σ ;;; Γ |- it_mkProd_or_LetIn Δ (tSort s) <= T ->
  Σ ;;; Γ |- it_mkProd_or_LetIn Δ (tSort s) = T.
Proof.
  move=> wfext isp.
  revert Γ T; induction Δ using ctx_length_rev_ind; intros Γ' T.
  - simpl. intros Hs; eapply is_prop_cum_l in Hs. now symmetry. auto. auto.
  - destruct d as [na [b|] ty]; simpl;
      rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /= => HT.
    eapply invert_cumul_letin_l in HT; auto.
    rewrite /subst1 subst_it_mkProd_or_LetIn /= in HT.
    specialize (X (subst_context [b] 0 Γ) ltac:(autorewrite with len; auto)).
    eapply conv_trans. 3:eapply X. auto.
    eapply red_conv, red_trans. eapply red1_red. constructor.
    now rewrite /subst1 subst_it_mkProd_or_LetIn.
    apply HT.

    eapply invert_cumul_prod_l in HT as [? [? [? [[red eq] leq]]]]; auto.
    eapply conv_trans with (tProd na ty x1); auto.
    eapply conv_Prod_r.
    specialize (X Γ ltac:(reflexivity)). now eapply X.
    eapply conv_trans. auto. eapply conv_Prod_l. eauto.
    now symmetry; eapply red_conv.
Qed.    

Lemma is_prop_arity_cum_r_eq {Σ Γ T s Δ} : 
  wf_ext Σ ->
  Universe.is_prop s ->
  Σ ;;; Γ |- T <= it_mkProd_or_LetIn Δ (tSort s) ->
  Σ ;;; Γ |- it_mkProd_or_LetIn Δ (tSort s) = T.
Proof.
  move=> wfext isp HT.
  eapply is_prop_arity_cum_sym in HT; auto.
  now eapply is_prop_arity_cum_l_eq.
Qed.

Lemma conv_sort_inv Σ Γ s s' :
  Σ ;;; Γ |- tSort s = tSort s' ->
  eq_universe (global_ext_constraints Σ) s s'.
Proof.
  intros H.
  eapply conv_alt_red in H as [v [v' [[redv redv'] eqvv']]].
  eapply invert_red_sort in redv.
  eapply invert_red_sort in redv'. subst.
  now depelim eqvv'.
Qed.

Definition is_prop_arity Σ Γ T := 
  ∑ Δ s, (Σ ;;; Γ |- T = it_mkProd_or_LetIn Δ (tSort s)) * (Universe.is_prop s).

Lemma is_prop_arity_cum_l Σ Γ A B : 
  wf_ext Σ ->
  is_prop_arity Σ Γ A -> 
  Σ ;;; Γ |- A <= B ->
  is_prop_arity Σ Γ B.
Proof.
  intros wfΣ [Δ [s [conv isp]]] cum.
  symmetry in conv; eapply conv_cumul in conv.
  unshelve epose proof (cumul_trans _ _ _ _ _ _ conv cum); auto.
  eapply is_prop_arity_cum_l_eq in X; auto.
  exists Δ, s. split; pcuic. now symmetry.
Qed.

Lemma is_prop_arity_cum_r Σ Γ A B : 
  wf_ext Σ ->
  is_prop_arity Σ Γ A -> 
  Σ ;;; Γ |- B <= A ->
  is_prop_arity Σ Γ B.
Proof.
  intros wfΣ [Δ [s [conv isp]]] cum.
  symmetry in conv; eapply conv_cumul in conv.
  eapply is_prop_arity_cum_sym in conv; auto.
  unshelve epose proof (cumul_trans _ _ _ _ _ _ cum conv); auto.
  eapply is_prop_arity_cum_r_eq in X; auto.
  exists Δ, s. split; pcuic. now symmetry.
Qed.

Lemma conv_sort_it_mkProd_or_LetIn {Σ Γ s Δ s'}:
  wf Σ.1 -> 
  Σ ;;; Γ |- tSort s = it_mkProd_or_LetIn Δ (tSort s') ->
  Σ ;;; Γ |- tSort s = tSort s'.
Proof.
  move=> wfΣ.
  induction Δ using ctx_length_rev_ind.
  - simpl. auto.
  - destruct d as [na [b|] ty]; simpl;
      rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /= => HT.
    eapply invert_conv_letin_r in HT; auto.
    rewrite /subst1 subst_it_mkProd_or_LetIn /= in HT.
    specialize (X (subst_context [b] 0 Γ0) ltac:(autorewrite with len; auto)). auto.
    eapply conv_cumul in HT. now eapply cumul_Sort_Prod_inv in HT.
Qed.

Lemma is_prop_arity_sort {Σ Γ s} :
  wf_ext Σ -> is_prop_arity Σ Γ (tSort s) <~> Universe.is_prop s.
Proof.
  intros wfΣ; split.
  - intros [Δ [s' [eqs isp]]]. eapply conv_sort_it_mkProd_or_LetIn in eqs => //.
    eapply conv_sort_inv in eqs. eapply eq_universe_leq_universe in eqs.
    eapply leq_universe_prop in eqs; eauto. apply wfΣ.
  - intros iss; exists [], s. split; auto.
Qed.

Lemma is_prop_superE {Σ l} : wf_ext Σ -> Universe.is_prop (Universe.super l) -> False.
Proof.
  intros wfΣ. 
  eapply is_prop_gt; eauto.
  eapply leq_universe_refl.
Qed.
  
Lemma is_prop_prod {s s'} : Universe.is_prop s' -> Universe.is_prop (Universe.sort_of_product s s').
Proof.
  intros isp.
  unfold Universe.sort_of_product. rewrite isp. auto.
Qed.

Lemma red_arity_it_mkProd_or_LetIn_inv (Σ : global_env_ext) Γ Δ s codom : 
  wf Σ.1 ->
  red Σ Γ (it_mkProd_or_LetIn Δ (tSort s)) codom ->
  ∑ Δ', codom = it_mkProd_or_LetIn Δ' (tSort s).
Proof.
  intros wfΣ; induction Δ in Γ, codom |- * using ctx_length_rev_ind => /= Hred.
  - eapply invert_red_sort in Hred; exists []; auto.
  - destruct d as [na' [b'|] ty'] ;
    rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /= in Hred.
    + eapply invert_red_letin in Hred as [(? & ? & ? & ? &(((eq & ?) & ?) & ?))|Hred] => //.
      subst.
      specialize (X Γ0 ltac:(now easy) _ _ r1) as [Δ' eq].
      exists (Δ' ++ [vdef x x0 x1]). simpl. rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /=.
      congruence.
      specialize (X (subst_context [b'] 0 Γ0) ltac:(now autorewrite with len)).
      rewrite /subst1 subst_it_mkProd_or_LetIn in Hred.
      now specialize (X _ _ Hred).
    + eapply invert_red_prod in Hred as [A' [B' [[eq rA] rB]]]; auto.
      noconf eq. specialize (X Γ0 ltac:(reflexivity) _ _ rB) as [Δ' eq].
      exists (Δ' ++ [vass na' A']).
      rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /=. congruence.
Qed.

Lemma red_arity_Prod_inv (Σ : global_env_ext) Γ Δ s na dom codom : 
  wf Σ.1 ->
  red Σ Γ (it_mkProd_or_LetIn Δ (tSort s)) (tProd na dom codom) ->
  ∑ Δ', codom = it_mkProd_or_LetIn Δ' (tSort s).
Proof.
  intros wfΣ Hred.
  eapply red_arity_it_mkProd_or_LetIn_inv in Hred; auto.
  destruct Hred as [Δ' eq].
  destruct Δ' using rev_ind; simpl in eq => //; rewrite it_mkProd_or_LetIn_app in eq.
  destruct x as [na' [b'|] ty']; rewrite /= /mkProd_or_LetIn /= in eq => //.
  noconf eq. exists l; auto.
Qed.

Lemma invert_conv_letin_l_alt {Σ Γ C na d ty b} :
  wf Σ.1 -> wf_local Σ (Γ ,, vdef na d ty) ->
  Σ ;;; Γ |- tLetIn na d ty b = C ->
  Σ ;;; Γ,, vdef na d ty |- b = lift0 1 C.
Proof.
  intros wfΣ wf Hlet.
  epose proof (red_expand_let _ _ _ _ b wf).
  eapply conv_trans. auto. eapply red_conv, X. 
  eapply (PCUICWeakening.weakening_conv _ Γ [] [vdef _ _ _]); auto.
  now eapply invert_conv_letin_l in Hlet.
Qed.

Lemma is_prop_arity_it_mkProd {Σ Γ Δ b} : 
    wf_ext Σ -> 
    wf_local Σ (Γ ,,, Δ) ->
    is_prop_arity Σ Γ (it_mkProd_or_LetIn Δ b) <~> is_prop_arity Σ (Δ ++ Γ) b.
Proof.
  intros wfΣ wf; split; intros [Δ' [s [eq isp]]]. move wf after eq.
  induction Δ in Γ, Δ', b, eq, wf |- * using ctx_length_rev_ind. simpl in eq.
  - exists Δ', s; intuition auto.
  - destruct d as [na' [b'|] ty'] ;
     rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /= in eq. 
    + rewrite -[_ ,,, _]app_assoc in wf |- *.
      eapply invert_conv_letin_l_alt in eq; auto.
      rewrite PCUICWeakening.lift_it_mkProd_or_LetIn in eq.
      specialize (X Γ0 ltac:(autorewrite with len; auto)).
      specialize (X _ _ _ eq). now rewrite -app_assoc.
      now eapply All_local_env_app in wf as [? _].  
    + specialize (X Γ0 ltac:(autorewrite with len; auto)). auto.
      eapply conv_Prod_l_inv in eq; auto.
      destruct eq as (na'' & dom' & codom' & (r & eqdom) & cum).
      rewrite -app_assoc.
      eapply red_arity_Prod_inv in r as [Δ'' eq].
      eapply (X _ _ Δ'').
      eapply conv_trans with codom' => //; auto.
      subst codom'. reflexivity. 2:auto.
      now rewrite /app_context app_assoc.
  - red. exists (Δ' ++ Δ), s. intuition auto.
    rewrite it_mkProd_or_LetIn_app.
    now eapply conv_alt_it_mkProd_or_LetIn.
Qed.

Lemma is_prop_arity_Prod {Σ Γ na dom b} : 
    wf_ext Σ -> 
    wf_local Σ (Γ ,, vass na dom)  ->
    is_prop_arity Σ Γ (tProd na dom b) <~> is_prop_arity Σ (vass na dom :: Γ) b.
Proof.
  intros; apply (is_prop_arity_it_mkProd (Δ:=[vass na dom])) => //.
Qed.

Lemma is_prop_arity_LetIn {Σ Γ na dom def b} : 
    wf_ext Σ -> 
    wf_local Σ (Γ ,, vdef na dom def) ->
    is_prop_arity Σ Γ (tLetIn na dom def b) <~> is_prop_arity Σ (vdef na dom def :: Γ) b.
Proof.
  intros. apply (is_prop_arity_it_mkProd (Δ:=[vdef na dom def])) => //.
Qed.

Lemma is_prop_arity_conv_context {Σ Γ Γ' T} :
  wf Σ.1 ->
  is_prop_arity Σ Γ T ->
  conv_context Σ Γ Γ' ->
  is_prop_arity Σ Γ' T.
Proof.
  intros wfΣ [Δ [s [eq isp]]] H.
  exists Δ, s; split => //.
  now eapply conv_conv_ctx.
Qed.

Lemma is_prop_arity_subst {Σ Γ na ty T u} : 
  wf Σ.1 ->
  wf_local Σ (Γ ,, vass na ty) ->
  is_prop_arity Σ (Γ ,, vass na ty) T ->
  Σ ;;; Γ |- u : ty ->
  is_prop_arity Σ Γ (T {0 := u}).
Proof.
  intros wfΣ wf [Δ [s [eq isp]]] Hu.
  eapply (substitution_conv _ Γ [vass na ty] []) in eq; eauto.
  2:constructor; [constructor|rewrite subst_empty; eauto].
  simpl in eq.
  rewrite subst_it_mkProd_or_LetIn in eq.
  exists (subst_context [u] 0 Δ), s; auto.
Qed.
(* 
Lemma is_prop_arity_subst_inv {Σ Γ na ty T u} : s
  wf Σ.1 ->
  wf_local Σ (Γ ,, vass na ty) ->
  Σ ;;; Γ |- u : ty ->
  is_prop_arity Σ Γ (T {0 := u}) ->
  is_prop_arity Σ (Γ ,, vass na ty) T.
Proof.
  intros wfΣ wf Hu [Δ [s [eq isp]]].
  eapply (substitution_conv _ Γ [vass na ty] []) in eq; eauto.
  2:constructor; [constructor|rewrite subst_empty; eauto].
  simpl in eq.
  rewrite subst_it_mkProd_or_LetIn in eq.
  exists (subst_context [u] 0 Δ), s; auto.
Qed. *)
(* 
Lemma is_prop_arity_fixed {Σ Γ u na A B} :  
  is_prop_arity Σ Γ (B {0 := u}) ->
  is_prop_arity Σ (Γ ,, vass na A) B.
Proof.
  intros. red in X. *)
(* T = (fun X : Type 1 => X) Prop 

*)
 
(* Definition equiv_arities Σ Γ T T' :=
  forall Δ Δ' s s', Σ ;;; Γ |- T = it_mkProd_or_LetIn Δ (tSort s) ->
    Σ ;;; Γ |- T' = it_mkProd_or_LetIn Δ' (tSort s') ->
    forall inst inst', subst0 inst  
    (forall )
    (Universe.is_prop s <-> Universe.is_prop s') *)

Definition eq_univ_prop (u v : Universe.t) :=
  Universe.is_prop u <-> Universe.is_prop v.

Definition eq_term_prop (Σ : global_env) napp :=
  PCUICEquality.eq_term_upto_univ_napp Σ eq_univ_prop eq_univ_prop napp.

Reserved Notation " Σ ;;; Γ |- t ~ u " (at level 50, Γ, t, u at next level).

Inductive cumul_prop `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
  | cumul_refl t u : eq_term_prop Σ.1 0 t u -> Σ ;;; Γ |- t ~ u
  | cumul_red_l t u v : red1 Σ.1 Γ t v -> Σ ;;; Γ |- v ~ u -> Σ ;;; Γ |- t ~ u
  | cumul_red_r t u v : Σ ;;; Γ |- t ~ v -> red1 Σ.1 Γ u v -> Σ ;;; Γ |- t ~ u
  
where " Σ ;;; Γ |- t ~ u " := (cumul_prop Σ Γ t u) : type_scope.

Lemma eq_term_prop_impl Σ Re Rle t u :
  wf_ext Σ ->
  forall n,
  PCUICEquality.eq_term_upto_univ_napp Σ.1 Re Rle n t u ->
  subrelation Re eq_univ_prop ->
  subrelation Rle eq_univ_prop ->
  eq_term_prop Σ n t u.
Proof.
  intros wfΣ n eq.
  intros.
  eapply PCUICEquality.eq_term_upto_univ_impl in eq. eauto.
  all:auto. 
Qed.

Lemma subrelation_eq_universe_eq_prop Σ : 
  wf_ext Σ ->
  subrelation (eq_universe Σ) eq_univ_prop.
Proof.
  intros wfΣ x y eq'. red.
  split; intros.
  eapply eq_universe_leq_universe in eq'.
  now eapply leq_universe_prop_no_prop_sub_type in eq'.
  eapply eq_universe_leq_universe in eq'.
  now eapply leq_universe_prop in eq'.
Qed.

Lemma subrelation_leq_universe_eq_prop Σ : 
  wf_ext Σ ->
  subrelation (leq_universe Σ) eq_univ_prop.
Proof.
  intros wfΣ x y eq'. red.
  split; intros.
  now eapply leq_universe_prop_no_prop_sub_type in eq'.
  now eapply leq_universe_prop in eq'.
Qed.

Lemma eq_term_eq_term_prop_impl Σ t u :
  wf_ext Σ ->
  forall n,
  PCUICEquality.eq_term_upto_univ_napp Σ.1 (eq_universe Σ) (eq_universe Σ) n t u ->
  eq_term_prop Σ n t u.
Proof.
  intros wfΣ n eq. eapply eq_term_prop_impl; eauto.
  now apply subrelation_eq_universe_eq_prop.
  now apply subrelation_eq_universe_eq_prop.
Qed.

Lemma leq_term_eq_term_prop_impl Σ t u :
  wf_ext Σ ->
  forall n,
  PCUICEquality.eq_term_upto_univ_napp Σ.1 (eq_universe Σ) (leq_universe Σ) n t u ->
  eq_term_prop Σ n t u.
Proof.
  intros wfΣ n eq. eapply eq_term_prop_impl; eauto.
  now apply subrelation_eq_universe_eq_prop.
  now apply subrelation_leq_universe_eq_prop.
Qed.

Lemma cumul_cumul_prop Σ Γ A B : 
  wf_ext Σ ->
  Σ ;;; Γ |- A <= B ->
  Σ ;;; Γ |- A ~ B.
Proof.
  intros wfΣ. induction 1.
  - constructor. now apply leq_term_eq_term_prop_impl in l.
  - econstructor 2; eauto.
  - econstructor 3; eauto.
  - todoeta.
  - todoeta.  
Qed.

Lemma conv_cumul_prop Σ Γ A B : 
  wf_ext Σ ->
  Σ ;;; Γ |- A = B ->
  Σ ;;; Γ |- A ~ B.
Proof.
  intros wfΣ. induction 1.
  - constructor. now apply eq_term_eq_term_prop_impl in e.
  - econstructor 2; eauto.
  - econstructor 3; eauto.
  - todoeta.
  - todoeta.  
Qed.
Require Import Equations.Type.Relation Equations.Type.Relation_Properties.

Lemma cumul_prop_alt Σ Γ T U :
  Σ ;;; Γ |- T ~ U <~>
  ∑ nf nf', (red Σ Γ T nf * red Σ Γ U nf' * eq_term_prop Σ 0 nf nf').
Proof.
  split.
  - induction 1.
    exists t, u. intuition pcuic.
    destruct IHX as [nf [nf' [[redl redr] eq]]].
    exists nf, nf'; intuition pcuic.
    now transitivity v.
    destruct IHX as [nf [nf' [[redl redr] eq]]].
    exists nf, nf'; intuition pcuic.
    now transitivity v.
  - intros [nf [nf' [[redv redv'] eq]]].
    apply red_alt in redv. apply red_alt in redv'.
    apply clos_rt_rt1n in redv.
    apply clos_rt_rt1n in redv'.
    induction redv.
    * induction redv'.
    ** constructor; auto.
    ** econstructor 3; eauto.
    * econstructor 2; eauto.
Qed.

Lemma cumul_prop_props Σ Γ u u' : 
  Universe.is_prop u ->
  Σ ;;; Γ |- tSort u ~ tSort u' ->
  Universe.is_prop u'.
Proof.
  intros isp equiv.
  eapply cumul_prop_alt in equiv as [nf [nf' [[redl redr] eq]]].
  eapply invert_red_sort in redl. apply invert_red_sort in redr.
  subst.
  depelim eq. red in e. intuition auto.
Qed.

Instance refl_eq_univ_prop : RelationClasses.Reflexive eq_univ_prop.
Proof.
  intros x. red. intuition.
Qed.

Instance sym_eq_univ_prop : RelationClasses.Symmetric eq_univ_prop.
Proof.
  intros x y; unfold eq_univ_prop; intuition.
Qed.

Instance trans_eq_univ_prop : RelationClasses.Transitive eq_univ_prop.
Proof.
  intros x y; unfold eq_univ_prop; intuition.
Qed.

Lemma UnivExprSet_For_all (P : UnivExpr.t -> Prop) (u : Universe.t) :
  UnivExprSet.For_all P u <->
  Forall P (UnivExprSet.elements u).
Proof.
  rewrite UnivExprSet_For_all_exprs.
  pose proof (Universe.exprs_spec u).
  destruct (Universe.exprs u). rewrite -H. simpl.
  split. constructor; intuition.
  intros H'; inv H'; intuition.
Qed.

Lemma univ_expr_set_in_elements e s : 
  UnivExprSet.In e s <-> In e (UnivExprSet.elements s).
Proof.
  rewrite -UnivExprSet.elements_spec1. generalize (UnivExprSet.elements s).
  now eapply InA_In_eq.
Qed.

Lemma univ_epxrs_elements_map g s : 
  forall e, In e (UnivExprSet.elements (Universe.map g s)) <->
      In e (map g (UnivExprSet.elements s)).
Proof.
  intros e.
  unfold Universe.map.
  pose proof (Universe.exprs_spec s).
  destruct (Universe.exprs s) as [e' l] eqn:eq.  
  rewrite -univ_expr_set_in_elements Universe.add_list_spec.
  rewrite -H. simpl. rewrite UnivExprSet.singleton_spec.
  intuition auto.
Qed.
  
Lemma Forall_elements_in P s : Forall P (UnivExprSet.elements s) <-> 
  (forall x, UnivExprSet.In x s -> P x).
Proof.
  setoid_rewrite univ_expr_set_in_elements.
  generalize (UnivExprSet.elements s).
  intros.
  split; intros.
  induction H; depelim H0; subst => //; auto.
  induction l; constructor; auto.
  apply H. repeat constructor.
  apply IHl. intros x inxl. apply H. right; auto.
Qed.

Lemma univ_exprs_map_all P g s : 
  Forall P (UnivExprSet.elements (Universe.map g s)) <->
  Forall (fun x => P (g x)) (UnivExprSet.elements s).
Proof.
  rewrite !Forall_elements_in.
  setoid_rewrite Universe.map_spec.
  intuition auto.
  eapply H. now exists x.
  destruct H0 as [e' [ins ->]]. apply H; auto.
Qed.

Lemma expr_set_forall_map f g s : 
  UnivExprSet.for_all f (Universe.map g s) <->
  UnivExprSet.for_all (fun e => f (g e)) s.
Proof.
  rewrite /is_true !UnivExprSet.for_all_spec !UnivExprSet_For_all.
  apply univ_exprs_map_all.
Qed.

Lemma univ_is_prop_make x : Universe.is_prop (Universe.make x) = Level.is_prop x.
Proof.
  destruct x; simpl; auto.
Qed.

Lemma is_prop_subst_level_expr u1 u2 s : 
  Forall2 (fun x y : Level.t => eq_univ_prop (Universe.make x) (Universe.make y)) u1 u2  ->
  UnivExpr.is_prop (subst_instance_level_expr u1 s) = UnivExpr.is_prop (subst_instance_level_expr u2 s).
Proof.
  intros hu. destruct s; simpl; auto.
  destruct e as [[] ?]; simpl; auto.
  destruct (nth_error u1 n) eqn:E.
  eapply Forall2_nth_error_Some_l in hu; eauto.
  destruct hu as [t' [-> eq]].
  red in eq. rewrite !univ_is_prop_make in eq.
  eapply eq_iff_eq_true in eq.
  destruct t, t'; simpl in eq => //.
  eapply Forall2_nth_error_None_l in hu; eauto.
  now rewrite hu.
Qed.

Instance substuniv_eq_univ_prop : SubstUnivPreserving eq_univ_prop.
Proof.
  intros s u1 u2 hu.
  red in hu.
  eapply Forall2_map_inv in hu.
  rewrite /subst_instance_univ.
  red.
  unfold Universe.is_prop in *.
  rewrite !expr_set_forall_map.
  rewrite /is_true !UnivExprSet.for_all_spec !UnivExprSet_For_all.
  generalize (UnivExprSet.elements s).
  induction l. split; constructor.
  split; intros H; inv H; constructor; auto.
  rewrite -(is_prop_subst_level_expr u1 u2) => //.
  now apply IHl.
  rewrite (is_prop_subst_level_expr u1 u2) => //.
  now apply IHl.
Qed.

Lemma cumul_prop_sym Σ Γ T U : 
  wf Σ.1 ->
  Σ ;;; Γ |- T ~ U ->
  Σ ;;; Γ |- U ~ T.
Proof.
  intros wfΣ Hl.
  eapply cumul_prop_alt in Hl as [t' [u' [[tt' uu'] eq]]].
  eapply cumul_prop_alt.
  exists u', t'; intuition auto.
  now symmetry.
Qed.

Lemma cumul_prop_trans Σ Γ T U V : 
  wf_ext Σ ->
  Σ ;;; Γ |- T ~ U ->
  Σ ;;; Γ |- U ~ V ->
  Σ ;;; Γ |- T ~ V.
Proof.
  intros wfΣ Hl Hr.
  eapply cumul_prop_alt in Hl as [t' [u' [[tt' uu'] eq]]].
  eapply cumul_prop_alt in Hr as [u'' [v' [[uu'' vv'] eq']]].
  eapply cumul_prop_alt. destruct wfΣ as [wfΣ onu] .
  destruct (red_confluence wfΣ uu' uu'') as [u'nf [ul ur]].
  eapply red_eq_term_upto_univ_r in ul as [tnf [redtnf ?]]; tea; tc.
  eapply red_eq_term_upto_univ_l in ur as [unf [redunf ?]]; tea; tc.
  exists tnf, unf.
  intuition auto.
  - now transitivity t'.
  - now transitivity v'.
  - now transitivity u'nf.
Qed.

Instance cumul_prop_transitive Σ Γ : wf_ext Σ -> CRelationClasses.Transitive (cumul_prop Σ Γ).
Proof. intros. red. intros. now eapply cumul_prop_trans. Qed.
Existing Class wf_ext.

Lemma cumul_prop_cum_l Σ Γ A T B : 
  wf_ext Σ ->
  Σ ;;; Γ |- A ~ T -> 
  Σ ;;; Γ |- A <= B ->
  Σ ;;; Γ |- B ~ T.
Proof.
  intros wfΣ HT cum.
  eapply cumul_cumul_prop in cum; auto.
  eapply CRelationClasses.transitivity ; eauto.
  eapply cumul_prop_sym; eauto.
Qed.

Lemma cumul_prop_cum_r Σ Γ A T B : 
  wf_ext Σ ->
  Σ ;;; Γ |- A ~ T -> 
  Σ ;;; Γ |- B <= A ->
  Σ ;;; Γ |- B ~ T.
Proof.
  intros wfΣ HT cum.
  eapply cumul_cumul_prop in cum; auto.
  eapply CRelationClasses.transitivity ; eauto.
Qed.

Lemma cumul_prop_conv_l Σ Γ A T B : 
  wf_ext Σ ->
  Σ ;;; Γ |- A ~ T -> 
  Σ ;;; Γ |- A = B ->
  Σ ;;; Γ |- B ~ T.
Proof.
  intros wfΣ HT cum.
  eapply conv_cumul_prop in cum; auto.
  eapply CRelationClasses.transitivity ; eauto.
  eapply cumul_prop_sym; eauto.
Qed.

Lemma cumul_prop_conv_r Σ Γ A T B : 
  wf_ext Σ ->
  Σ ;;; Γ |- A ~ T -> 
  Σ ;;; Γ |- B = A ->
  Σ ;;; Γ |- B ~ T.
Proof.
  intros wfΣ HT cum.
  eapply conv_cumul_prop in cum; auto.
  eapply CRelationClasses.transitivity ; eauto.
Qed.

Definition conv_decls_prop (Σ : global_env_ext) (Γ Γ' : context) (c d : context_decl) :=
  match decl_body c, decl_body d with
  | None, None => True
  | Some b, Some b' => b = b'
  | _, _ => False
  end.

Notation conv_ctx_prop Σ := (context_relation (conv_decls_prop Σ)).

Lemma conv_ctx_prop_refl Σ Γ :
  conv_ctx_prop Σ Γ Γ.
Proof.
  induction Γ as [|[na [b|] ty]]; constructor; eauto => //.
Qed.

Lemma conv_ctx_prop_app Σ Γ Γ' Δ :
  conv_ctx_prop Σ Γ Γ' ->
  conv_ctx_prop Σ (Γ ,,, Δ) (Γ' ,,, Δ).
Proof.
  induction Δ; simpl; auto.
  destruct a as [na  [b|] ty]; intros; constructor => //.
  now eapply IHΔ.
  now eapply IHΔ.
Qed.

Lemma red1_upto_conv_ctx_prop Σ Γ Γ' t t' :
  red1 Σ.1 Γ t t' ->
  conv_ctx_prop Σ Γ Γ' ->
  red1 Σ.1 Γ' t t'.
Proof.
  intros Hred; induction Hred using red1_ind_all in Γ' |- *; 
    try solve [econstructor; eauto;
      try solve [solve_all]].
  - econstructor. destruct (nth_error Γ i) eqn:eq; simpl in H => //.
    noconf H; simpl in H; noconf H.
    eapply context_relation_nth in X; eauto.
    destruct X as [d' [Hnth [ctxrel cp]]].
    red in cp. rewrite H in cp. rewrite Hnth /=.
    destruct (decl_body d'); subst => //.
  - econstructor. eapply IHHred. constructor; simpl; auto => //.
  - econstructor. eapply IHHred. constructor; simpl => //.
  - econstructor. eapply IHHred; constructor => //.
  - intros. eapply fix_red_body. solve_all.
    eapply b0. now eapply conv_ctx_prop_app.
  - intros. eapply cofix_red_body. solve_all.
    eapply b0. now eapply conv_ctx_prop_app.
Qed.

Lemma red_upto_conv_ctx_prop Σ Γ Γ' t t' :
  red Σ.1 Γ t t' ->
  conv_ctx_prop Σ Γ Γ' ->
  red Σ.1 Γ' t t'.
Proof.
  intros Hred. eapply red_alt in Hred.
  intros convctx. eapply red_alt.
  induction Hred; eauto.
  constructor. now eapply red1_upto_conv_ctx_prop.
  eapply rt_trans; eauto.
Qed.

Lemma cumul_prop_prod_inv Σ Γ na A B na' A' B' :
  wf Σ.1 ->
  Σ ;;; Γ |- tProd na A B ~ tProd na' A' B' ->
  Σ ;;; Γ ,, vass na A |- B ~ B'.
Proof.
  intros wfΣ H; eapply cumul_prop_alt in H as [nf [nf' [[redv redv'] eq]]].
  eapply invert_red_prod in redv as (? & ? & (? & ?) & ?).
  eapply invert_red_prod in redv' as (? & ? & (? & ?) & ?).
  subst. all:auto.
  eapply cumul_prop_alt.
  exists x0, x2. intuition auto.
  eapply red_upto_conv_ctx_prop; eauto.
  constructor; auto => //. apply conv_ctx_prop_refl.
  depelim eq. apply eq2.
Qed.
Require Import PCUICEquality.

Lemma substitution_untyped_cumul_prop Σ Γ Δ Γ' s M N :
  wf Σ.1 -> untyped_subslet Γ s Δ ->
  Σ ;;; (Γ ,,, Δ ,,, Γ') |- M ~ N ->
  Σ ;;; (Γ ,,, subst_context s 0 Γ') |- (subst s #|Γ'| M) ~ (subst s #|Γ'| N).
Proof.
  intros wfΣ subs Hcum.
  eapply cumul_prop_alt in Hcum as [nf [nf' [[redl redr] eq']]].
  eapply substitution_untyped_red in redl; eauto.
  eapply substitution_untyped_red in redr; eauto.
  eapply cumul_prop_alt.
  eexists _, _; intuition eauto.
  eapply PCUICEquality.eq_term_upto_univ_substs => //.
  eapply All2_refl.
  intros x. eapply PCUICEquality.eq_term_upto_univ_refl; typeclasses eauto.
Qed.

Lemma substitution_untyped_cumul_prop_equiv Σ Γ Δ Γ' s s' M :
  wf Σ.1 -> 
  untyped_subslet Γ s Δ ->
  untyped_subslet Γ s' Δ ->
  All2 (eq_term_prop Σ.1 0) s s' ->
  Σ ;;; (Γ ,,, subst_context s 0 Γ') |- (subst s #|Γ'| M) ~ (subst s' #|Γ'| M).
Proof.
  intros wfΣ subs subs' Heq.
  eapply cumul_prop_alt.
  eexists _, _; intuition eauto.
  eapply PCUICEquality.eq_term_upto_univ_substs => //.
  reflexivity.
Qed.

Lemma cumul_prop_args (Σ : global_env_ext) {Γ args args'} :
  wf_ext Σ ->
  All2 (cumul_prop Σ Γ) args args' ->
  ∑ nf nf', All2 (red Σ Γ) args nf * All2 (red Σ Γ) args' nf' *
    All2 (eq_term_prop Σ 0) nf nf'.
Proof.
  intros wfΣ a.
  induction a. exists [], []; intuition auto.
  destruct IHa as (nfa & nfa' & (redl & redr) & eq).
  eapply cumul_prop_alt in r as (nf & nf' & ((redl' & redr') & eq'')).
  exists (nf :: nfa), (nf' :: nfa'); intuition auto.
Qed.

Lemma substitution_untyped_cumul_prop_cumul Σ Γ Δ Γ' Δ' s s' M :
  wf_ext Σ -> 
  untyped_subslet Γ s Δ ->
  untyped_subslet Γ s' Δ' ->
  All2 (cumul_prop Σ Γ) s s' ->
  Σ ;;; (Γ ,,, subst_context s 0 Γ') |- (subst s #|Γ'| M) ~ (subst s' #|Γ'| M).
Proof.
  intros wfΣ subs subs' Heq.
  eapply cumul_prop_args in Heq as (nf & nf' & (redl & redr) & eq) => //.
  eapply cumul_prop_alt.
  eexists (subst nf #|Γ'| M), (subst nf' #|Γ'| M); intuition eauto.
  rewrite -(subst_context_length s 0 Γ').
  eapply red_red => //; eauto.
  rewrite -(subst_context_length s 0 Γ').
  eapply red_red => //; eauto.
  eapply PCUICEquality.eq_term_upto_univ_substs => //.
  reflexivity.
Qed.

Lemma substitution1_untyped_cumul_prop Σ Γ na t u M N :
  wf Σ.1 -> 
  Σ ;;; (Γ ,, vass na t) |- M ~ N ->
  Σ ;;; Γ |- M {0 := u} ~ N {0 := u}.
Proof.
  intros wfΣ Hcum.
  eapply (substitution_untyped_cumul_prop Σ Γ [_] []) in Hcum; auto.
  2:repeat constructor.
  eapply Hcum.
Qed.

Lemma cext_negb_is_prop Σ univs u :
  consistent_instance_ext Σ univs u ->
  forallb (fun x => negb  (Level.is_prop x)) u.
Proof.
  destruct univs; simpl.
  destruct u => //.
  intuition.
Qed.

Lemma is_prop_subst_instance_level u l
      (Hu : forallb (negb ∘ Level.is_prop) u)
  : Universe.is_prop (Universe.make (subst_instance_level u l)) = Universe.is_prop (Universe.make l).
Proof.
  assert (He : forall a, UnivExpr.is_prop (subst_instance_level_expr u a)
                    = UnivExpr.is_prop a). {
    clear l. intros [|[l b]]; cbnr.
    destruct l; cbnr.
    apply nth_error_forallb with (n0:=n) in Hu.
    destruct nth_error; cbnr.
    destruct t; cbnr. discriminate. }
  apply iff_is_true_eq_bool.
  split; intro H; apply UnivExprSet.for_all_spec in H; proper;
    apply UnivExprSet.for_all_spec; proper; intros e Xe.
  - rewrite <- He. apply H. 
    rewrite -subst_instance_univ_make.
    eapply UnivExprSet.singleton_spec.
    eapply UnivExprSet.singleton_spec in Xe. now subst.
  - eapply UnivExprSet.singleton_spec in Xe. subst.
    specialize (He (UnivExpr.make l)).
    unfold Universe.make in H.
    eapply UnivExprSet_For_all_exprs in H as [H _]. simpl in H.
    rewrite H in He.
    rewrite -He.
    f_equal.
    destruct l; simpl; auto.
    rewrite MCList.nth_nth_error.
    destruct nth_error; reflexivity.
Qed.

Lemma R_opt_variance_impl Re Rle v x y : 
  subrelation Re Rle ->
  R_universe_instance Re x y ->
  R_opt_variance Re Rle v x y.
Proof.
  intros sub.
  destruct v; simpl; auto.
  intros H. eapply Forall2_map_inv in H.
  induction H in l |- *; simpl; auto.
  destruct l. auto.
  split. destruct t; simpl; auto.
  eauto.
Qed.
  

Lemma cumul_prop_subst_instance_instance Σ univs u u' i : 
  wf Σ.1 ->
  consistent_instance_ext Σ univs u ->
  consistent_instance_ext Σ univs u' ->
  R_universe_instance eq_univ_prop (subst_instance_instance u i)
    (subst_instance_instance u' i).
Proof.
  intros wfΣ cu cu'. red.
  eapply All2_Forall2, All2_map.
  unfold subst_instance_instance.
  eapply All2_map. eapply All2_refl.
  intros x. red.
  rewrite is_prop_subst_instance_level; eauto using cext_negb_is_prop.
  now rewrite is_prop_subst_instance_level; eauto using cext_negb_is_prop.
Qed.

Lemma cumul_prop_subst_instance_constr Σ Γ univs u u' T : 
  wf Σ.1 ->
  consistent_instance_ext Σ univs u ->
  consistent_instance_ext Σ univs u' ->
  Σ ;;; Γ |- subst_instance_constr u T ~ subst_instance_constr u' T.
Proof.
  intros wfΣ cu cu'.
  eapply cumul_prop_alt.
  eexists _, _; intuition eauto.
  induction T using PCUICInduction.term_forall_list_ind; simpl; intros;
    try solve [constructor; eauto; solve_all].
  - constructor. red.
    rewrite is_prop_subst_instance_univ; eauto using cext_negb_is_prop.
    now rewrite is_prop_subst_instance_univ; eauto using cext_negb_is_prop.
  - constructor. eapply PCUICEquality.eq_term_upto_univ_impl in IHT1; eauto.
    all:try typeclasses eauto.
    apply IHT2.
  - constructor. now eapply cumul_prop_subst_instance_instance.
  - constructor. red. apply R_opt_variance_impl. intros x y; auto.
    now eapply cumul_prop_subst_instance_instance. 
  - constructor. red. apply R_opt_variance_impl. intros x y; auto.
    now eapply cumul_prop_subst_instance_instance. 
Qed.

Lemma All_All_All2 {A} (P Q : A -> Prop) l l' : 
  All P l -> All Q l' -> #|l| = #|l'| -> All2 (fun x y => P x /\ Q y) l l'.
Proof.
  induction l in l' |- *; destruct l'; simpl; auto => //.
  intros ha hb. specialize (IHl l'); depelim ha; depelim hb.
  constructor; auto.
Qed.

Lemma R_eq_univ_prop_consistent_instances Σ univs u u' : 
  wf Σ.1 ->
  consistent_instance_ext Σ univs u ->
  consistent_instance_ext Σ univs u' ->
  R_universe_instance eq_univ_prop u u'.
Proof.
  intros wfΣ cu cu'.
  destruct univs; simpl in *.
  - destruct u, u' => /= //. red.
    simpl. constructor.
  - intuition.
    eapply Forall2_map.
    eapply All2_Forall2.
    solve_all.
    eapply All2_impl.
    eapply All_All_All2; eauto. lia.
    simpl; intros.
    intuition. red; rewrite !univ_is_prop_make.
    unfold negb in a. destruct (Level.is_prop x) => //.
    destruct (Level.is_prop y) => //.
Qed.

Lemma untyped_subslet_inds Γ ind u u' mdecl :
  untyped_subslet Γ (inds (inductive_mind ind) u (ind_bodies mdecl))
    (subst_instance_context u' (arities_context (ind_bodies mdecl))).
Proof.
  generalize (le_n #|ind_bodies mdecl|).
  generalize (ind_bodies mdecl) at 1 3 4.
  unfold inds.
  induction l using rev_ind; simpl; first constructor.
  simpl. rewrite app_length /= => Hlen.
  unfold arities_context.
  simpl. rewrite /arities_context rev_map_spec /=.
  rewrite map_app /= rev_app_distr /=. 
  rewrite {1}/map_decl /= Nat.add_1_r /=.
  constructor.
   rewrite -rev_map_spec. apply IHl. lia.
Qed.

Hint Resolve conv_ctx_prop_refl : core.

Lemma cumul_prop_tProd {Σ : global_env_ext} {Γ na t ty na' t' ty'} : 
  wf_ext Σ ->
  eq_term Σ.1 Σ t t' ->
  Σ ;;; Γ ,, vass na t |- ty ~ ty' ->
  Σ ;;; Γ |- tProd na t ty ~ tProd na' t' ty'.
Proof.
  intros wfΣ eq cum.
  eapply cumul_prop_alt in cum as (nf & nf' & ((redl & redr) & eq')).
  eapply cumul_prop_alt. eexists (tProd na t nf), (tProd na' t' nf'); intuition eauto.
  eapply red_prod; auto. eapply red_prod; auto.
  eapply red_upto_conv_ctx_prop; eauto.
  repeat (constructor; auto).
  repeat (constructor; auto).
  eapply eq_term_eq_term_prop_impl; auto.
Qed.

Lemma cumul_prop_tLetIn (Σ : global_env_ext) {Γ na t d ty na' t' d' ty'} : 
  wf_ext Σ ->
  eq_term Σ.1 Σ t t' ->
  eq_term Σ.1 Σ d d' ->
  Σ ;;; Γ ,, vdef na d t |- ty ~ ty' ->
  Σ ;;; Γ |- tLetIn na d t ty ~ tLetIn na' d' t' ty'.
Proof.
  intros wfΣ eq eq' cum.
  eapply cumul_prop_alt in cum as (nf & nf' & ((redl & redr) & eq'')).
  eapply cumul_prop_alt. 
  assert(eq_context_upto Σ (eq_universe Σ) (Γ ,, vdef na d t) (Γ ,, vdef na' d' t')).
  { repeat constructor; pcuic. eapply eq_context_upto_refl. typeclasses eauto. }
  eapply red_eq_context_upto_l in redr; eauto. all:try typeclasses eauto.
  destruct redr as [v' [redv' eq''']].
  eexists (tLetIn na d t nf), (tLetIn na' d' t' v'); intuition eauto.
  eapply red_letin; auto. eapply red_letin; auto.
  constructor; eauto using eq_term_eq_term_prop_impl.
  apply eq_term_eq_term_prop_impl; auto.
  apply eq_term_eq_term_prop_impl; auto.
  transitivity nf'. auto. now eapply eq_term_eq_term_prop_impl.
Qed.

Lemma cumul_prop_mkApps (Σ : global_env_ext) {Γ f args f' args'} :
  wf_ext Σ ->
  eq_term Σ.1 Σ f f' ->
  All2 (cumul_prop Σ Γ) args args' ->
  Σ ;;; Γ |- mkApps f args ~ mkApps f' args'.
Proof.
  intros wfΣ eq eq'.
  eapply cumul_prop_alt.
  eapply cumul_prop_args in eq' as (nf & nf' & (redl & redr) & eq').
  exists (mkApps f nf), (mkApps f' nf'); intuition auto.
  eapply red_mkApps; auto.
  eapply red_mkApps; auto.
  eapply eq_term_upto_univ_mkApps.
  eapply eq_term_upto_univ_impl.
  5:eapply eq. all:auto. 4:lia.
  all:now eapply subrelation_eq_universe_eq_prop.
Qed.

Lemma red_cumul_prop (Σ : global_env_ext) Γ : CRelationClasses.subrelation (red Σ Γ) (cumul_prop Σ Γ).
Proof.
  intros x y r. eapply cumul_prop_alt. exists y, y.
  intuition auto. apply eq_term_upto_univ_refl; typeclasses eauto.
Qed.

Lemma eq_term_prop_mkApps_inv (Σ : global_env_ext) {ind u args ind' u' args'} :
  wf_ext Σ ->
  forall n, eq_term_prop Σ n (mkApps (tInd ind u) args) (mkApps (tInd ind' u') args') ->
  All2 (eq_term_prop Σ 0) args args'.
Proof.
  intros wfΣ. revert args'.
  induction args using rev_ind; intros args' n; simpl.
  intros H; destruct args' using rev_case.
  constructor.
  depelim H. solve_discr. eapply app_eq_nil in H1 as [_ H]. congruence.
  intros H.
  destruct args' using rev_case. depelim H. solve_discr.
  apply app_eq_nil in H1 as [_ H]; discriminate.
  rewrite - !mkApps_nested /= in H. depelim H.
  eapply All2_app => //.
  eapply IHargs; eauto. repeat constructor.
  red. apply H0.
Qed.

Lemma cumul_prop_mkApps_Ind_inv (Σ : global_env_ext) {Γ ind u args ind' u' args'} :
  wf_ext Σ ->
  Σ ;;; Γ |- mkApps (tInd ind u) args ~ mkApps (tInd ind' u') args' ->
  All2 (cumul_prop Σ Γ) args args'.
Proof.
  intros wfΣ eq.
  eapply cumul_prop_alt in eq as (nf & nf' & (redl & redr) & eq').
  eapply red_mkApps_tInd in redl as [args'' [-> eqargs]].
  eapply red_mkApps_tInd in redr as [args''' [-> eqargs']]. all:auto.
  eapply All2_trans. typeclasses eauto.
  eapply All2_impl; eauto. eapply red_cumul_prop.
  eapply All2_trans. typeclasses eauto.
  2:{ eapply All2_symP. intros x y H; now eapply cumul_prop_sym.
      eapply All2_impl; eauto. eapply red_cumul_prop. } 
  eapply All2_impl; eauto.
  eapply eq_term_prop_mkApps_inv in eq' => //.
  eapply All2_impl; eauto. now constructor.
Qed.
  
Instance cumul_prop_sym' Σ Γ : wf Σ.1 -> CRelationClasses.Symmetric (cumul_prop Σ Γ).
Proof.
  now intros wf x y; eapply cumul_prop_sym.
Qed.

Lemma typing_leq_term_prop (Σ : global_env_ext) Γ t t' T T' :
  wf Σ.1 ->
  Σ ;;; Γ |- t : T ->
  on_udecl Σ.1 Σ.2 ->
  Σ ;;; Γ |- t' : T' ->
  forall n, leq_term_napp Σ n t' t ->
  Σ ;;; Γ |- T ~ T'.
Proof.
  intros wfΣ Ht.
  revert Σ wfΣ Γ t T Ht t' T'.
  eapply (typing_ind_env 
  (fun Σ Γ t T =>
  forall t' T' : term,
  on_udecl Σ.1 Σ.2 ->
  Σ;;; Γ |- t' : T' ->
  forall n, leq_term_napp Σ n t' t ->
  Σ ;;; Γ |- T ~ T')%type 
  (fun Σ Γ wfΓ => wf_local Σ Γ)); auto;intros Σ wfΣ Γ wfΓ; intros.

  1-13:match goal with
  [ H : leq_term_napp _ _ _ _ |- _ ] => depelim H
  end; assert (wf_ext Σ) by (split; assumption).

  14:{ specialize (X1 _ _ H X4 _ X5).
      now eapply cumul_prop_cum_l. }

  6:{ eapply inversion_App in X4 as (na' & A' & B' & hf & ha & cum); auto.
      specialize (X1 _ _ H hf _ X5_1).
      specialize (X3 _ _ H ha _ (eq_term_upto_univ_napp_leq X5_2)).
      eapply cumul_cumul_prop in cum; auto.
      transitivity (B' {0 := u0}) => //.
      eapply cumul_prop_prod_inv in X1 => //.
      transitivity (B' {0 := u}).
      now eapply substitution1_untyped_cumul_prop in X1.
      constructor.
      eapply eq_term_eq_term_prop_impl => //.
      eapply PCUICEquality.eq_term_upto_univ_substs.
      all:try typeclasses eauto. 
      eapply PCUICEquality.eq_term_upto_univ_refl. all:try typeclasses eauto.
      constructor. 2:constructor. now symmetry. }

  - eapply inversion_Rel in X0 as [decl' [wfΓ' [Hnth Hcum]]]; auto.
    rewrite Hnth in H; noconf H. now eapply cumul_cumul_prop in Hcum.

  - eapply inversion_Sort in X0 as [l' [_ [Inl' [-> ?]]]]; auto.
    apply subrelation_leq_universe_eq_prop in x => //.
    apply cumul_cumul_prop in c => //.
    eapply cumul_prop_trans; eauto.
    constructor. constructor. symmetry.
    split; intros H'; now eapply is_prop_superE in H'.

  - eapply inversion_Prod in X4 as [s1' [s2' [Ha [Hb Hs]]]]; auto.
    specialize (X1 _ _ H Ha). 
    specialize (X1 _ (eq_term_upto_univ_napp_leq X5_1)).
    eapply context_conversion in Hb. 3:{ constructor. apply conv_ctx_refl. constructor.
      constructor. eauto. }
    all:eauto.
    2:{ constructor; eauto. now exists s1. }
    specialize (X3 _ _ H Hb _ X5_2).
    eapply cumul_cumul_prop in Hs => //.
    eapply cumul_prop_trans; eauto.
    constructor. constructor.
    red.
    split; intros Hs'; apply is_prop_sort_prod in Hs'; eapply is_prop_prod; eapply cumul_prop_props; eauto.
    now eapply cumul_prop_sym; eauto.

  - eapply inversion_Lambda in X4 as (s & B & dom & bod & cum).
    specialize (X1 _ _ H dom _ (eq_term_upto_univ_napp_leq X5_1)).
    specialize (X3 t0 B H). 
    assert(conv_context Σ (Γ ,, vass na ty) (Γ ,, vass n t)).
    { repeat constructor; pcuic. eapply conv_ctx_refl. }
    forward X3 by eapply context_conversion; eauto; pcuic.
    specialize (X3 _ X5_2). eapply cumul_cumul_prop in cum; eauto.
    eapply cumul_prop_trans; eauto.
    eapply cumul_prop_tProd; eauto. now symmetry. auto.

  - eapply inversion_LetIn in X6 as (s1' & A & dom & bod & codom & cum); auto.
    specialize (X1 _ _ H dom _ (eq_term_upto_univ_napp_leq X7_2)).
    specialize (X3 _ _ H bod _  (eq_term_upto_univ_napp_leq X7_1)).
    assert(conv_context Σ (Γ ,, vdef na t ty) (Γ ,, vdef n b b_ty)).
    { repeat constructor; pcuic. eapply conv_ctx_refl. }
    specialize (X5 u A H).
    forward X5 by eapply context_conversion; eauto; pcuic.
    specialize (X5 _ X7_3).
    eapply cumul_cumul_prop in cum; eauto.
    eapply cumul_prop_trans; eauto.
    eapply cumul_prop_tLetIn; auto. now symmetry.
    now symmetry.

  - eapply inversion_Const in X1 as [decl' [wf [declc [cu cum]]]]; auto.
    eapply cumul_cumul_prop in cum; eauto.
    eapply cumul_prop_trans; eauto.
    pose proof (PCUICWeakeningEnv.declared_constant_inj _ _ H declc); subst decl'.
    eapply cumul_prop_subst_instance_constr; eauto.

  - eapply inversion_Ind in X1 as [decl' [idecl' [wf [declc [cu cum]]]]]; auto.
    pose proof (PCUICWeakeningEnv.declared_inductive_inj isdecl declc) as [-> ->].
    eapply cumul_cumul_prop in cum; eauto.
    eapply cumul_prop_trans; eauto. do 2 red in H.
    now eapply cumul_prop_subst_instance_constr.

  - eapply inversion_Construct in X1 as [decl' [idecl' [cdecl' [wf [declc [cu cum]]]]]]; auto.
    pose proof (PCUICWeakeningEnv.declared_constructor_inj isdecl declc) as [-> [-> ->]].
    eapply cumul_cumul_prop in cum; eauto.
    eapply cumul_prop_trans; eauto.
    unfold type_of_constructor.
    etransitivity. 
    eapply (substitution_untyped_cumul_prop_equiv _ Γ (subst_instance_context u (arities_context mdecl.(ind_bodies))) []); auto.
    eapply untyped_subslet_inds. eapply (untyped_subslet_inds _ ind u0 u).
    simpl. generalize (ind_bodies mdecl).
    induction l; simpl; constructor; auto.
    constructor. simpl. eapply R_opt_variance_impl. now intros x.
    eapply R_eq_univ_prop_consistent_instances; eauto. simpl.
    eapply (substitution_untyped_cumul_prop _ Γ (subst_instance_context u0 (arities_context mdecl.(ind_bodies))) []) => //.
    eapply untyped_subslet_inds. simpl.
    eapply cumul_prop_subst_instance_constr => //; eauto.

  - eapply inversion_Case in X6 as (u' & args' & mdecl' & idecl' & ps' & pty' & btys' & inv); auto.
    intuition auto.
    intuition auto.
    eapply cumul_cumul_prop in b; eauto.
    eapply cumul_prop_trans; eauto. simpl.
    specialize (X4 _ _ H4 a6 _ (eq_term_upto_univ_napp_leq X7_2)).
    eapply cumul_prop_sym => //.
    eapply cumul_prop_mkApps => //.
    eapply All2_app. 2:(repeat constructor; auto using eq_term_eq_term_prop_impl).
    eapply All2_skipn. eapply cumul_prop_mkApps_Ind_inv in X4 => //.
    eapply All2_symP => //. typeclasses eauto.
    
  - eapply inversion_Proj in X3 as (u' & mdecl' & idecl' & pdecl' & args' & inv); auto.
    intuition auto.
    specialize (X2 _ _  H0 a0 _ (eq_term_upto_univ_napp_leq X4)).
    eapply eq_term_upto_univ_napp_leq in X4.
    eapply cumul_cumul_prop in b; eauto.
    eapply cumul_prop_trans; eauto.
    eapply cumul_prop_mkApps_Ind_inv in X2 => //.
    destruct (PCUICWeakeningEnv.declared_projection_inj a isdecl) as [<- [<- <-]].
    subst ty. 
    transitivity (subst0 (c0 :: List.rev args') (subst_instance_constr u pdecl'.2)).
    eapply (substitution_untyped_cumul_prop_cumul Σ Γ (projection_context mdecl idecl p.1.1 u) []) => //.
    epose proof (projection_subslet Σ _ _ _ _ _ _ _ _ isdecl wfΣ X1).
    eapply subslet_untyped_subslet. eapply X3, validity; eauto.
    epose proof (projection_subslet Σ _ _ _ _ _ _ _ _ a wfΣ a0).
    eapply subslet_untyped_subslet. eapply X3, validity; eauto.
    constructor => //. symmetry; constructor => //.
    now eapply leq_term_eq_term_prop_impl.
    now eapply All2_rev.
    eapply (substitution_untyped_cumul_prop Σ Γ (projection_context mdecl idecl p.1.1 u') []) => //.
    epose proof (projection_subslet Σ _ _ _ _ _ _ _ _ a wfΣ a0).
    eapply subslet_untyped_subslet. eapply X3, validity; eauto.
    destruct a.
    eapply validity, (isWAT_mkApps_Ind wfΣ H1) in X1 as [ps [argss [_ cu]]]; eauto.
    eapply validity, (isWAT_mkApps_Ind wfΣ H1) in a0 as [? [? [_ cu']]]; eauto.
    eapply cumul_prop_subst_instance_constr; eauto.

  - eapply inversion_Fix in X2 as (decl' & fixguard' & Hnth & types' & bodies & wffix & cum); auto.
    eapply cumul_cumul_prop in cum; eauto.
    eapply cumul_prop_trans; eauto.
    eapply All2_nth_error in a; eauto.
    destruct a as [[a _] _].
    constructor. eapply eq_term_eq_term_prop_impl; eauto.
    now eapply eq_term_sym in a.
  
  - eapply inversion_CoFix in X2 as (decl' & fixguard' & Hnth & types' & bodies & wfcofix & cum); auto.
    eapply cumul_cumul_prop in cum; eauto.
    eapply cumul_prop_trans; eauto.
    eapply All2_nth_error in a; eauto.
    destruct a as [[a _] _].
    constructor. eapply eq_term_eq_term_prop_impl; eauto.
    now eapply eq_term_sym in a.
Qed.

Lemma leq_term_prop_sorted_l {Σ Γ v v' u u'} :
  wf_ext Σ ->
  PCUICEquality.leq_term Σ (global_ext_constraints Σ) v v' ->
  Σ;;; Γ |- v : tSort u ->
  Σ;;; Γ |- v' : tSort u' -> Universe.is_prop u -> 
  leq_universe (global_ext_constraints Σ) u' u.
Proof.
  intros wfΣ leq hv hv' isp.
  eapply typing_leq_term_prop in leq; eauto.
  apply leq_prop_prop; intuition auto.
  eapply cumul_prop_sym in leq.
  eapply cumul_prop_props in leq; eauto. auto. apply wfΣ.
Qed.

Lemma leq_term_prop_sorted_r {Σ Γ v v' u u'} :
  wf_ext Σ ->
  PCUICEquality.leq_term Σ (global_ext_constraints Σ) v v' ->
  Σ;;; Γ |- v : tSort u ->
  Σ;;; Γ |- v' : tSort u' -> Universe.is_prop u' -> 
  leq_universe (global_ext_constraints Σ) u u'.
Proof.
  intros wfΣ leq hv hv' isp.
  eapply typing_leq_term_prop in leq; eauto.
  apply leq_prop_prop; intuition auto.
  apply cumul_prop_props in leq; auto. apply wfΣ.
Qed.

Lemma cumul_prop_inv (Σ : global_env_ext) Γ A B u u' :
  wf_ext Σ ->
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
  wf_ext Σ ->
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
      eapply (PCUICWeakening.weakening_cumul _ _ [] [vdef na b t]) in X2; auto.
      simpl in X2. assert (wf Σ) by apply X.
      etransitivity; eauto.
      eapply red_cumul. apply PCUICSpine.red_expand_let.
      constructor; pcuic.
      left; eexists _, _; simpl; intuition eauto.
      eapply red_cumul, PCUICReduction.red1_red.
      constructor.
Qed.

Lemma cumul_prop_l_is_type (Σ : global_env_ext) Γ A B u :
  wf_ext Σ ->
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
    apply is_prop_gt in lt; auto.
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
      eapply (PCUICWeakening.weakening_cumul _ _ [] [vdef na b t]) in X2; auto.
      simpl in X2. assert (wf Σ) by apply X.
      etransitivity; eauto.
      eapply conv_cumul, conv_sym, red_conv. apply PCUICSpine.red_expand_let.
      constructor; pcuic.
      left; eexists _, _; simpl; intuition eauto.
      eapply red_cumul, PCUICReduction.red1_red.
      constructor.
Qed.

Lemma cumul_prop1 (Σ : global_env_ext) Γ A B u :
  wf_ext Σ ->
  Universe.is_prop u ->
  isWfArity_or_Type Σ Γ A ->
  Σ ;;; Γ |- B : tSort u ->
  Σ ;;; Γ |- A <= B ->
  Σ ;;; Γ |- A : tSort u.
Proof.
  intros.
  eapply cumul_prop_r_is_type in X0; eauto.
  destruct X0 as [s Hs].
  eapply cumul_prop_inv in H. 4:eauto. firstorder. auto.
  right; eauto.
Qed.

Lemma cumul_prop2 (Σ : global_env_ext) Γ A B u :
  wf_ext Σ ->
  Universe.is_prop u ->
  isWfArity_or_Type Σ Γ B ->
  Σ ;;; Γ |- A <= B ->
  Σ ;;; Γ |- A : tSort u ->
  Σ ;;; Γ |- B : tSort u.
Proof.
  intros.
  eapply cumul_prop_l_is_type in X0; eauto.
  destruct X0 as [s Hs].
  eapply cumul_prop_inv in H. 4:eauto. firstorder. auto.
  left; eauto.
Qed.

End no_prop_leq_type.
