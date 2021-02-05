(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils Universes.
From MetaCoq.PCUIC Require Import PCUICTyping PCUICAst PCUICAstUtils
     PCUICLiftSubst PCUICInductives PCUICGeneration PCUICSpine PCUICWeakeningEnv
     PCUICSubstitution PCUICUnivSubst PCUICUnivSubstitution
     PCUICConversion PCUICCumulativity PCUICConfluence PCUICContexts
     PCUICSR PCUICInversion PCUICValidity PCUICSafeLemmata PCUICContextConversion
     PCUICCumulProp.

Require Equations.Prop.DepElim.
From Equations Require Import Equations.
Require Import ssreflect.

Definition Is_proof `{cf : checker_flags} Σ Γ t := ∑ T u, Σ ;;; Γ |- t : T × Σ ;;; Γ |- T : tSort u × 
  (Universe.is_prop u || Universe.is_sprop u).

Definition SingletonProp `{cf : checker_flags} (Σ : global_env_ext) (ind : inductive) :=
  forall mdecl idecl,
    declared_inductive (fst Σ) ind mdecl idecl ->
    forall Γ args u n (Σ' : global_env_ext),
      wf Σ' ->
      extends Σ Σ' ->
      welltyped Σ' Γ (mkApps (tConstruct ind n u) args) ->
      ∥Is_proof Σ' Γ (mkApps (tConstruct ind n u) args)∥ /\
       #|ind_ctors idecl| <= 1 /\
       squash (All (Is_proof Σ' Γ) (skipn (ind_npars mdecl) args)).

Definition Computational `{cf : checker_flags} (Σ : global_env_ext) (ind : inductive) :=
  forall mdecl idecl,
    declared_inductive (fst Σ) ind mdecl idecl ->
    forall Γ args u n (Σ' : global_env_ext),
      wf Σ' ->
      extends Σ Σ' ->
      welltyped Σ' Γ (mkApps (tConstruct ind n u) args) ->
      Is_proof Σ' Γ (mkApps (tConstruct ind n u) args) -> False.

Definition Informative `{cf : checker_flags} (Σ : global_env_ext) (ind : inductive) :=
  forall mdecl idecl,
    declared_inductive (fst Σ) ind mdecl idecl ->
    forall Γ args u n (Σ' : global_env_ext),
      wf_ext Σ' ->
      extends Σ Σ' ->
      Is_proof Σ' Γ (mkApps (tConstruct ind n u) args) ->
       #|ind_ctors idecl| <= 1 /\
       squash (All (Is_proof Σ' Γ) (skipn (ind_npars mdecl) args)).

Lemma elim_restriction_works_kelim1 {cf : checker_flags} {Σ : global_env_ext} 
  {Γ T ci p c brs mdecl idecl} :
  check_univs ->
  wf_ext Σ ->
  declared_inductive Σ ci.(ci_ind) mdecl idecl ->
  Σ ;;; Γ |- tCase ci p c brs : T ->
  (Is_proof Σ Γ (tCase ci p c brs) -> False) ->
  ind_kelim idecl = IntoAny \/ ind_kelim idecl = IntoSetPropSProp.
Proof.
  intros cu wfΣ. intros.
  assert (HT := X).
  eapply inversion_Case in X as [mdecl' [idecl' [indices [data cum]]]]; eauto.
  destruct data.
  eapply declared_inductive_inj in isdecl as []. 2:exact H. subst.
  enough (~ (Universe.is_prop ps \/ Universe.is_sprop ps)).
  { clear -cu wfΣ i H1.
    apply wf_ext_consistent in wfΣ as (val&sat).
    unfold is_allowed_elimination, is_allowed_elimination0 in *.
    rewrite cu in i.
    specialize (i _ sat).
    destruct (ind_kelim idecl); auto;
      destruct ⟦ps⟧_val%u eqn:v; try easy;
        try apply val_is_sprop in v;
        try apply val_is_prop in v;
        intuition congruence. }
  intros Huf. apply H0.
  (*
  red. exists (mkApps ptm (indices ++ [c])); intuition auto.
  exists ps.
  intuition auto.
  assert (watiapp := env_prop_typing  _ _ validity_env _ _ _ _ _ t0).
  simpl in watiapp.
  eapply (isType_mkApps_Ind wfΣ H) in watiapp as [psub [asub [[spp spa] cuni]]]; eauto.
  eapply typing_wf_local; eauto.
  destruct (on_declared_inductive H) as [mib oib].
  clear a1.
  (* eapply (build_case_predicate_type_spec _ _ _ _ _ _ _ _ oib) in e0 as [parsubst [cs eq]].
  rewrite eq in t. *)
  assert (Σ ;;; Γ |- it_mkLambda_or_LetIn predctx (preturn p) : it_mkProd_or_LetIn predctx (tSort ps)).
  eapply type_it_mkLambda_or_LetIn. eauto.*)
  (* eapply PCUICGeneration.type_mkApps; tea.
  eapply wf_arity_spine_typing_spine; auto.
  split; auto.
  now eapply validity_term in X; eauto. *)
  all:todo "case".
  (* eapply arity_spine_it_mkProd_or_LetIn; eauto.
  pose proof (wf_predicate_length_pars w).
  rewrite skipn_all_app_eq in spa; auto.
  rewrite /predctx.
  rewrite /case_predicate_context /case_predicate_context_gen.
  todo "case". simpl. todo "case". *)
(*   
  eapply spa.
  simpl. constructor.
  rewrite PCUICLiftSubst.subst_mkApps. simpl.
  rewrite map_app map_map_compose.
  rewrite PCUICLiftSubst.map_subst_lift_id_eq. 
  { rewrite - (PCUICSubstitution.context_subst_length spa).
      now autorewrite with len. }
  { unfold to_extended_list. 
    rewrite (spine_subst_subst_to_extended_list_k_gen spa).
    unfold subst_context; rewrite to_extended_list_k_fold_context_k.
    apply PCUICSubstitution.map_subst_instance_to_extended_list_k.
    subst npar.
    now rewrite firstn_skipn. } *)
  (* - rewrite H1; auto. *)
  (* - rewrite H1 Bool.orb_true_r; auto. *)
Qed.

Lemma elim_sort_intype {cf:checker_flags} Σ mdecl ind idecl ind_indices ind_sort cdecls :
  Universe.is_prop ind_sort ->  
  elim_sort_prop_ind cdecls = IntoAny ->
  on_constructors (lift_typing typing)
    (Σ, ind_universes mdecl) mdecl 
    (inductive_ind ind) idecl ind_indices
    (ind_ctors idecl) cdecls ->
  (#|ind_ctors idecl| = 0) + 
  (∑ cdecl cdecl_sorts, 
    (ind_ctors idecl = [cdecl]) * 
    (cdecls = [cdecl_sorts]) * 
    (Forall is_propositional cdecl_sorts) *
    (on_constructor (lift_typing typing) (Σ, ind_universes mdecl) mdecl 
        (inductive_ind ind) idecl ind_indices cdecl cdecl_sorts))%type.
Proof.
  intros uf lein onc.
  induction onc; simpl in *.
  left; auto.
  destruct l' as [|c cs].
  - simpl in *. depelim onc.
    right.
    destruct forallb eqn:fo => //.
    eapply forallb_Forall in fo.
    eexists; eauto.
  - discriminate.
Qed.

Lemma typing_spine_it_mkProd_or_LetIn_full_inv {cf:checker_flags} Σ Γ Δ s args s' : 
  wf Σ.1 ->
  typing_spine Σ Γ (it_mkProd_or_LetIn Δ (tSort s)) args (tSort s') -> 
  leq_universe (global_ext_constraints Σ) s s'.
Proof.
  intros wfΣ.
  induction Δ using PCUICInduction.ctx_length_rev_ind in args |- *.
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
      eapply cumul_Prod_Prod_inv in c as [eqann [conv cum]]; auto. simpl in *.
      eapply (substitution_cumul _ Γ [vass na0 A] [] [hd]) in cum; auto.
      simpl in cum.
      now rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r in cum.
      constructor; auto. now eapply typing_wf_local.
      eapply PCUICArities.isType_tProd in i; auto. destruct i as [? ?]; auto.
      eapply typing_wf_local; eauto. constructor. constructor. now rewrite subst_empty.
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

Lemma is_propositional_subst_instance u s :
  is_propositional (subst_instance_univ u s) = is_propositional s.
Proof. destruct s => //. Qed.

Lemma leq_universe_propositional_l {cf:checker_flags} ϕ u1 u2 :
  check_univs ->
  prop_sub_type = false ->
  consistent ϕ ->
  leq_universe ϕ u1 u2 -> is_propositional u1 -> u1 = u2.
Proof.
  intros Hcf ps cu le.
  unfold is_propositional.
  destruct (Universe.is_prop u1) eqn:eq.
  apply leq_universe_prop_no_prop_sub_type in le; auto.
  simpl. now destruct u1, u2.
  simpl. intros sp.
  apply leq_universe_sprop_l in le; auto.
  now destruct u1, u2.
Qed.

Lemma typing_spine_proofs {cf:checker_flags} Σ Γ Δ ind u args' args T' s :
  check_univs ->
  wf_ext Σ ->
  Σ ;;; Γ |-  T' : tSort s ->
  typing_spine Σ Γ (it_mkProd_or_LetIn Δ (mkApps (tInd ind u) args')) args T' ->
  ((All_local_assum (fun Γ' t =>
      (∑ s, (Σ ;;; Γ ,,, Γ' |- t : tSort s) * is_propositional s)%type) Δ ->
    ∥ All (Is_proof Σ Γ) args ∥) *
    (forall mdecl idecl 
    (Hdecl : declared_inductive Σ.1 ind mdecl idecl),
      consistent_instance_ext Σ (ind_universes mdecl) u ->
      ((is_propositional s -> s = subst_instance_univ u idecl.(ind_sort)) /\ 
       (prop_sub_type = false ->
        is_propositional (subst_instance_univ u idecl.(ind_sort)) -> 
        s = subst_instance_univ u idecl.(ind_sort)))))%type.
Proof.
  intros checku wfΣ Ht.
  induction Δ using PCUICInduction.ctx_length_rev_ind in Γ, args', args, T', Ht |- *; simpl; intros sp.
  - depelim sp. split; [repeat constructor|].
    * eapply invert_cumul_ind_l in c as [ui' [l' [red  [Req argeq]]]] => //; auto.
      intros mdecl idecl decli cu.
      destruct (on_declared_inductive decli) as [onmind oib].
      eapply subject_reduction in Ht; eauto.
      eapply inversion_mkApps in Ht as [A [tInd sp]]; auto.
      eapply inversion_Ind in tInd as [mdecl' [idecl' [wfΓ [decli' [cu' cum]]]]]; auto.
      destruct (declared_inductive_inj decli decli'); subst mdecl' idecl'.
      clear decli'.
      eapply typing_spine_strengthen in sp; eauto.
      rewrite (oib.(ind_arity_eq)) in sp.
      rewrite !subst_instance_it_mkProd_or_LetIn in sp.
      rewrite -it_mkProd_or_LetIn_app in sp.
      eapply typing_spine_it_mkProd_or_LetIn_full_inv in sp; auto.
      split.
      intros Hs.
      destruct s => //.
      eapply leq_universe_prop_r in sp; auto.
      rewrite (is_prop_subst_instance_univ ui') in sp => //.
      now destruct (ind_sort idecl).
      apply wfΣ.
      eapply leq_universe_sprop_r in sp; auto.
      rewrite (is_sprop_subst_instance_univ ui') in sp => //.
      now destruct (ind_sort idecl).
      apply wfΣ.
      intros propsub props.
      rewrite is_propositional_subst_instance in props.
      apply leq_universe_propositional_l in sp; eauto. subst s.
      now destruct (ind_sort idecl).
      now destruct (ind_sort idecl).
      
    * eapply cumul_Prod_r_inv in c; auto.
      destruct c as [na' [dom' [codom' [[[red _] _] ?]]]].
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
        depelim prd.
        apply H.
        clear -wfΣ prs.
        eapply All_local_assum_subst; eauto.
        simpl. intros.
        destruct X as [s [Ht2 isp]].
        exists s; pcuicfo.
        rewrite Nat.add_0_r. eapply (substitution _ Γ [vdef na b ty] [b] Γ1 _ (tSort s)); auto.
        rewrite -{1}(subst_empty 0 b).
        repeat (constructor; auto). rewrite !subst_empty.
        eapply typing_wf_local in Ht2.
        rewrite app_context_assoc in Ht2. eapply All_local_env_app_inv in Ht2 as [Ht2 _].
        depelim Ht2. apply l0.
        now rewrite app_context_assoc in Ht2.
      * intros mdecl idec decli.
        now apply H.
    + rewrite it_mkProd_or_LetIn_app in sp.
      destruct args. split; [repeat constructor|].
      * simpl in sp. depelim sp.
        unfold mkProd_or_LetIn in c; simpl in c.
        eapply cumul_Prod_l_inv in c as [na' [dom' [codom' [[[red eqann] conv] cum]]]]; auto.
        eapply subject_reduction in Ht; eauto.
        intros.
        pose proof (PCUICWfUniverses.typing_wf_universe wfΣ Ht).
        eapply inversion_Prod in Ht as [s1 [s2 [dom [codom cum']]]]; auto.
        specialize (H Γ0 ltac:(reflexivity) (Γ ,, vass na' dom') args' []).
        eapply (type_Cumul _ _ _ _ (tSort s)) in codom; cycle 1; eauto.
        { econstructor; pcuic. }
        { eapply cumul_Sort_inv in cum'.
          do 2 constructor. etransitivity; eauto. eapply leq_universe_product. }
        specialize (H _ codom).
        forward H.
        { constructor. now exists s.
          eapply cumul_conv_ctx; eauto. constructor; auto.
          apply conv_ctx_refl. constructor; auto. }
        destruct H. eapply a; tea.
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
        depelim prd.
        eapply (type_Cumul' _ (T':=ty)) in t0.
        2:{ destruct s0 as [s' [Hs' _]]. exists s'; auto. }
        2:{ eapply conv_cumul. now symmetry. }
        destruct H as [H _].
        forward H. { 
          clear -wfΣ prs t0.
          eapply All_local_assum_subst; eauto.
          simpl. intros.
          destruct X as [s [Ht2 isp]].
          exists s; pcuicfo auto.
          rewrite Nat.add_0_r. eapply (substitution _ Γ [vass na ty] [t] Γ1 _ (tSort s)); auto.
          repeat (constructor; auto). now rewrite subst_empty.
          now rewrite app_context_assoc in Ht2. }
        sq. constructor; auto. simpl in conv.
        red. destruct s0 as [s' [Ht' sprop]].
        exists ty, s'. intuition auto.
        intros. now eapply H; tea.
Qed.

Lemma check_ind_sorts_is_propositional {cf:checker_flags} (Σ : global_env_ext) mdecl idecl ind
  (onib : on_ind_body (lift_typing typing) (Σ.1, ind_universes mdecl)
    (inductive_mind ind) mdecl (inductive_ind ind) idecl) : 
  (ind_kelim idecl <> IntoPropSProp /\ ind_kelim idecl <> IntoSProp) ->
  is_propositional (ind_sort idecl) -> 
  check_ind_sorts (lift_typing typing) (Σ.1, ind_universes mdecl)
    (PCUICEnvironment.ind_params mdecl) (PCUICEnvironment.ind_kelim idecl)
    (ind_indices idecl) (ind_cunivs onib) (ind_sort idecl) ->
  (#|ind_cunivs onib| <= 1) * All (fun cs => All is_propositional cs) (ind_cunivs onib).
Proof.
  intros kelim isp.
  unfold check_ind_sorts. simpl.
  destruct Universe.is_prop eqn:isp'.
  + induction (ind_cunivs onib); simpl; auto; try discriminate.
    destruct l; simpl. intros; split; eauto. constructor; [|constructor].
    destruct forallb eqn:fo. eapply forallb_All in fo.
    eapply All_impl; eauto; simpl.
    destruct (ind_kelim idecl); intuition cbn in H; try congruence.
    intros leb.
    destruct (ind_kelim idecl); simpl in *; intuition congruence.
  + destruct Universe.is_sprop eqn:issp.
    induction (ind_cunivs onib); simpl; auto; try discriminate.
    destruct (ind_kelim idecl); simpl in *; intuition congruence.
    unfold is_propositional in isp.
    now rewrite isp' issp in isp.
Qed.
 
Lemma sorts_local_ctx_All_local_assum_impl {cf:checker_flags} Σ 
  (P : context -> context -> term -> Type) {Γ Δ cs} : 
  (forall Γ' t s, In s cs -> Σ ;;; Γ ,,, Γ' |- t : tSort s  -> P Γ Γ' t) ->
  sorts_local_ctx (lift_typing typing) Σ Γ Δ cs ->
  All_local_assum (P Γ) Δ.
Proof.
  intros H.
  induction Δ in cs, H |- *; simpl; intros. constructor; intuition auto.
  destruct a as [na [b|] ty]; constructor; intuition auto.
  destruct cs => //; eauto.
  destruct cs => //; eauto. destruct X.
  eapply IHΔ. intros. apply (H Γ' t1 s0). right; eauto. all:auto.
  destruct cs => //. destruct X.
  eapply H. left; eauto. eauto.
Qed.

Lemma In_map {A B} (f : A -> B) (l : list A) x : 
  In x (map f l) -> 
  exists y, In y l /\ x = f y.
Proof.
  induction l; simpl; auto.
  intros [<-|inl].
  - eexists; intuition eauto.
  - destruct (IHl inl). exists x0; intuition eauto.
Qed.

(* We prove that if the (partial) constructor application's type lands in Prop
   then the inductive type is in Prop and hence the constructor's sort is 
   Prop. Finally, all its arguments are in Prop because we additionally know
   that elimination to any type is allowed. *)

Lemma Is_proof_mkApps_tConstruct `{cf : checker_flags} (Σ : global_env_ext) Γ ind n u mdecl idecl args :
  check_univs = true ->
  wf_ext Σ ->
  declared_inductive (fst Σ) ind mdecl idecl ->
  (ind_kelim idecl <> IntoPropSProp /\ ind_kelim idecl <> IntoSProp) ->
  Is_proof Σ Γ (mkApps (tConstruct ind n u) args) ->
  #|ind_ctors idecl| <= 1 /\ ∥ All (Is_proof Σ Γ) (skipn (ind_npars mdecl) args) ∥.
Proof.
  intros checkunivs HΣ decli kelim [tyc [tycs [hc [hty hp]]]].
  assert (wfΣ : wf Σ) by apply HΣ.
  eapply inversion_mkApps in hc as [? [hc hsp]]; auto.
  eapply inversion_Construct in hc as [mdecl' [idecl' [cdecl' [wfΓ [declc [cu cum']]]]]]; auto.
  destruct (on_declared_constructor declc) as [[oi oib] [cs [Hnth onc]]].
  set (onib := declared_inductive_inv _ _ _ _) in *.
  clearbody onib. clear oib.
  eapply typing_spine_strengthen in hsp; eauto.
  pose proof (declared_inductive_inj decli (proj1 declc)) as [-> ->].
  assert (isType Σ Γ (type_of_constructor mdecl cdecl' (ind, n) u)).
  { eapply PCUICInductiveInversion.declared_constructor_valid_ty in declc; eauto. }
  move: X hsp.
  unfold type_of_constructor.
  rewrite (onc.(cstr_eq)).
  rewrite !subst_instance_it_mkProd_or_LetIn !subst_it_mkProd_or_LetIn.
  rewrite - {1}(firstn_skipn (ind_npars mdecl) args).
  rewrite !subst_instance_mkApps.
  simpl.
  autorewrite with len.
  rewrite !subst_mkApps.
  rewrite !subst_inds_concl_head.
  destruct decli. now apply nth_error_Some_length in H0.
  destruct (le_dec (ind_npars mdecl) #|args|).
  * intros X hsp.
    eapply PCUICSpine.typing_spine_inv in hsp as [parsub [[sub wat] sp]]; auto.
    2:{ rewrite context_assumptions_subst subst_instance_assumptions.
        autorewrite with len.
        rewrite firstn_length_le //. symmetry; eapply onNpars. eauto. }
    rewrite !subst_it_mkProd_or_LetIn in X, sp.
    rewrite !subst_mkApps in sp.
    simpl in sp.
    eapply typing_spine_proofs in sp; eauto.
    destruct sp.
    specialize (a _ _ declc cu) as [a a'].
    specialize (a hp). 
    
    pose proof (onc.(on_cargs)).
    pose proof (onib.(ind_sorts)).
    assert (Universe.is_prop (ind_sort idecl) || Universe.is_sprop (ind_sort idecl)).
    { rewrite -(is_prop_subst_instance_univ u) -(is_sprop_subst_instance_univ u) => //. now subst tycs. }
    apply check_ind_sorts_is_propositional in X1 as [nctors X1]; eauto.
    assert(#|ind_cunivs onib| = #|ind_ctors idecl|).
    clear wat X. clear -onib. pose proof (onib.(onConstructors)).
    eapply All2_length in X. now rewrite X. 
    rewrite H0 in nctors; split; auto.

    eapply nth_error_all in X1; eauto. simpl in X1.
    eapply sorts_local_ctx_instantiate in X0. 4:eapply cu.
    all: eauto.
    rewrite subst_instance_app in X0.
    eapply weaken_sorts_local_ctx in X0; eauto.
    eapply (subst_sorts_local_ctx _ _) in X0; eauto.
    3:{ eapply subslet_app. 
      2:{ eapply (weaken_subslet _ _ _ _ []), PCUICArities.subslet_inds; eauto. } 
      eapply sub. }
    2:{ eapply PCUICWeakening.weaken_wf_local; auto.
        edestruct (PCUICInductiveInversion.on_constructor_inst declc); eauto.
        destruct s0 as [inst [sp _]].
        rewrite !subst_instance_app in sp.
        now eapply wf_local_app_l in sp. }

    apply s.
    rewrite subst_app_context in X0.
    rewrite -(PCUICContextSubst.context_subst_length sub) in X0.
    autorewrite with len in X0.
    eapply (sorts_local_ctx_All_local_assum_impl Σ 
      (fun Γ Γ' t => 
      ∑ s0 : Universe.t, Σ;;; Γ ,,, Γ' |- t : tSort s0 × is_propositional s0)).
    2:eauto.
    intros. exists s0. intuition auto.
    eapply In_map in H1 as [cs' [ins ->]].
    rewrite is_propositional_subst_instance.
    eapply All_In in X1; eauto.
    sq. apply X1.
    
  * intros _ sp.
    rewrite List.skipn_all2. lia.
    split; [|repeat constructor].
    pose proof (onc.(on_cargs)).
    pose proof (onib.(ind_sorts)).
    eapply check_ind_sorts_is_propositional in X0 as [nctors X1]; eauto.
    assert(#|ind_cunivs onib| = #|ind_ctors idecl|).
    clear -onib. pose proof (onib.(onConstructors)).
    eapply All2_length in X. now rewrite X. now rewrite -H.
    rewrite -it_mkProd_or_LetIn_app in sp.
    eapply typing_spine_proofs in sp; eauto.
    destruct sp as [_ sp].
    specialize (sp _ _ decli cu) as [a a'].
    specialize (a hp).
    subst tycs. rewrite -(is_propositional_subst_instance u) //.
Qed.
    
Lemma elim_restriction_works_kelim `{cf : checker_flags} (Σ : global_env_ext) ind mind idecl :
  check_univs = true ->
  wf_ext Σ ->
  declared_inductive (fst Σ) ind mind idecl ->
  (ind_kelim idecl <> IntoPropSProp /\ ind_kelim idecl <> IntoSProp) -> Informative Σ ind.
Proof.
  intros cu HΣ H indk.
  assert (wfΣ : wf Σ) by apply HΣ.
  destruct (PCUICWeakeningEnv.on_declared_inductive  H) as [[]]; eauto.
  intros ?. intros.
  eapply declared_inductive_inj in H as []; eauto; subst idecl0 mind.
  eapply Is_proof_mkApps_tConstruct in X1; tea.
  now eapply weakening_env_declared_inductive.
Qed.

Lemma elim_restriction_works `{cf : checker_flags} (Σ : global_env_ext) Γ T (ci : case_info) p c brs mind idecl : 
  check_univs = true ->
  wf_ext Σ ->
  declared_inductive (fst Σ) ci mind idecl ->
  Σ ;;; Γ |- tCase ci p c brs : T ->
  (Is_proof Σ Γ (tCase ci p c brs) -> False) -> Informative Σ ci.(ci_ind).
Proof.
  intros cu wfΣ decli HT H.
  eapply elim_restriction_works_kelim1 in HT; eauto.
  eapply elim_restriction_works_kelim; eauto.
  destruct (ind_kelim idecl); intuition congruence.
Qed.

Lemma declared_projection_projs_nonempty `{cf : checker_flags} {Σ : global_env_ext} { mind ind p a} :
  wf Σ ->
  declared_projection Σ p mind ind a ->
  ind_projs ind <> [].
Proof.
  intros. destruct H. destruct H0.
  destruct (ind_projs ind); try congruence. destruct p.
  cbn in *. destruct n; inv H0.
Qed.

Lemma elim_restriction_works_proj_kelim1 `{cf : checker_flags} (Σ : global_env_ext) Γ T p c mind idecl :
  wf Σ ->
  declared_inductive (fst Σ) (fst (fst p)) mind idecl ->
  Σ ;;; Γ |- tProj p c : T ->
  (Is_proof Σ Γ (tProj p c) -> False) -> ind_kelim idecl = IntoAny.
Proof.
  intros X H X0 H0.
  destruct p. destruct p. cbn in *.
  eapply inversion_Proj in X0 as (? & ? & ? & ? & ? & ? & ? & ? & ?) ; auto.
  destruct x2. cbn in *.
  pose (d' := d). destruct d' as [? _].
  eapply declared_inductive_inj in H as []; eauto. subst. simpl in *.
  pose proof (declared_projection_projs_nonempty X d).
  pose proof (PCUICWeakeningEnv.on_declared_projection d) as [_ onp].
  simpl in onp.
  destruct ind_ctors as [|? []]; try contradiction.
  destruct ind_cunivs as [|? []]; try contradiction.
  now destruct onp as (((? & ?) & ?) & ?).
  all:destruct onp as (((? & ?) & ?) & ?); now inv o.
Qed.

Lemma elim_restriction_works_proj `{cf : checker_flags} (Σ : global_env_ext) Γ  p c mind idecl T :
  check_univs = true -> wf_ext Σ ->
  declared_inductive (fst Σ) (fst (fst p)) mind idecl ->
  Σ ;;; Γ |- tProj p c : T ->
  (Is_proof Σ Γ (tProj p c) -> False) -> Informative Σ (fst (fst p)).
Proof.
  intros cu; intros. eapply elim_restriction_works_kelim; eauto.
  eapply elim_restriction_works_proj_kelim1 in H0; eauto.
  intuition congruence.
Qed.

(* Lemma length_of_btys {ind mdecl' idecl' args' u' p} :
  #|build_branches_type ind mdecl' idecl' args' u' p| = #|ind_ctors idecl'|.
Proof.
  unfold build_branches_type. now rewrite mapi_length.
Qed. *)

Lemma length_map_option_out {A} l l' :
  @map_option_out A l = Some l' -> #|l| = #|l'|.
Proof.
  induction l as [|[x|] l] in l' |- *.
  - destruct l'; [reflexivity|discriminate].
  - cbn. destruct (map_option_out l); [|discriminate].
    destruct l'; [discriminate|]. inversion 1; subst; cbn; eauto.
    noconf H. now specialize (IHl l' eq_refl).
  - discriminate.
Qed.

Lemma map_option_Some X (L : list (option X)) t : map_option_out L = Some t -> All2 (fun x y => x = Some y) L t.
Proof.
  intros. induction L in t, H |- *; cbn in *.
  - inv H. econstructor.
  - destruct a. destruct ?. all:inv H. eauto.
Qed.

Section no_prop_leq_type.

Context `{cf : checker_flags}.
Variable Hcf : prop_sub_type = false.
Variable Hcf' : check_univs = true.

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

Lemma leq_term_sprop_sorted_l {Σ Γ v v' u u'} :
  wf_ext Σ ->
  PCUICEquality.leq_term Σ (global_ext_constraints Σ) v v' ->
  Σ;;; Γ |- v : tSort u ->
  Σ;;; Γ |- v' : tSort u' -> Universe.is_sprop u -> 
  leq_universe (global_ext_constraints Σ) u' u.
Proof.
  intros wfΣ leq hv hv' isp.
  eapply typing_leq_term_prop in leq; eauto.
  apply leq_sprop_sprop; intuition auto.
  eapply cumul_prop_sym in leq.
  eapply cumul_sprop_props in leq; auto. eauto. auto. apply wfΣ.
Qed.

Lemma leq_term_sprop_sorted_r {Σ Γ v v' u u'} :
  wf_ext Σ ->
  PCUICEquality.leq_term Σ (global_ext_constraints Σ) v v' ->
  Σ;;; Γ |- v : tSort u ->
  Σ;;; Γ |- v' : tSort u' -> Universe.is_sprop u' -> 
  leq_universe (global_ext_constraints Σ) u u'.
Proof.
  intros wfΣ leq hv hv' isp.
  eapply typing_leq_term_prop in leq; eauto.
  apply leq_sprop_sprop; intuition auto.
  apply cumul_sprop_props in leq; auto. apply wfΣ.
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
  - eapply type_Cumul' with (tSort u'); eauto.
    eapply PCUICArities.isType_Sort.
    now eapply PCUICWfUniverses.typing_wf_universe in HA.
    pcuic.
    constructor. constructor.
    eapply subject_reduction in redv; eauto.
    eapply subject_reduction in redv'; eauto.
    eapply leq_term_prop_sorted_l; eauto.
  - eapply subject_reduction in redv; eauto.
    eapply subject_reduction in redv'; eauto.
    eapply leq_term_prop_sorted_r in leq; eauto.
    eapply type_Cumul' with (tSort u'); eauto.
    eapply PCUICArities.isType_Sort.
    now eapply PCUICWfUniverses.typing_wf_universe in HB.
    pcuic.
    constructor. constructor. auto.
Qed.

Lemma cumul_sprop_inv (Σ : global_env_ext) Γ A B u u' :
  wf_ext Σ ->
  Universe.is_sprop u ->
  (((Σ ;;; Γ |- A : tSort u) * (Σ ;;; Γ |- B : tSort u')) + 
   ((Σ ;;; Γ |- B : tSort u) * (Σ ;;; Γ |- A : tSort u')))%type ->
  Σ ;;; Γ |- A <= B ->
  ((Σ ;;; Γ |- A : tSort u) * (Σ ;;; Γ |- B : tSort u))%type.
Proof.
  intros wfΣ propu.
  intros [[HA HB]|[HB HA]] cum; split; auto;
  apply cumul_alt in cum as [v [v' [[redv redv'] leq]]].
  - eapply type_Cumul' with (tSort u'); eauto.
    eapply PCUICArities.isType_Sort; pcuic.
    now eapply PCUICWfUniverses.typing_wf_universe in HA.
    constructor. constructor.
    eapply subject_reduction in redv; eauto.
    eapply subject_reduction in redv'; eauto.
    eapply leq_term_sprop_sorted_l; eauto.
  - eapply subject_reduction in redv; eauto.
    eapply subject_reduction in redv'; eauto.
    eapply leq_term_sprop_sorted_r in leq; eauto.
    eapply type_Cumul' with (tSort u'); eauto.
    eapply PCUICArities.isType_Sort; pcuic. 
    now eapply PCUICWfUniverses.typing_wf_universe in HB.
    constructor. constructor. auto.
Qed.


(*
Lemma cumul_prop_r_is_type (Σ : global_env_ext) Γ A B u :
  wf_ext Σ ->
  Universe.is_prop u ->
  isType Σ Γ A ->
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
    eapply All_local_env_app_inv in eq' as [wfΓ wf']. depelim wfΓ;
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
    eapply All_local_env_app_inv in eq' as [wfΓ wf']. depelim wfΓ;
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
Qed. *)

Lemma cumul_prop1 (Σ : global_env_ext) Γ A B u :
  wf_ext Σ ->
  Universe.is_prop u ->
  isType Σ Γ A ->
  Σ ;;; Γ |- B : tSort u ->
  Σ ;;; Γ |- A <= B ->
  Σ ;;; Γ |- A : tSort u.
Proof.
  intros.
  destruct X0 as [s Hs].
  eapply cumul_prop_inv in H. 4:eauto. pcuicfo. auto.
  right; eauto.
Qed.

Lemma cumul_prop2 (Σ : global_env_ext) Γ A B u :
  wf_ext Σ ->
  Universe.is_prop u ->
  isType Σ Γ B ->
  Σ ;;; Γ |- A <= B ->
  Σ ;;; Γ |- A : tSort u ->
  Σ ;;; Γ |- B : tSort u.
Proof.
  intros.
  destruct X0 as [s Hs].
  eapply cumul_prop_inv in H. 4:eauto. pcuicfo. auto.
  left; eauto.
Qed.

Lemma cumul_sprop1 (Σ : global_env_ext) Γ A B u :
  wf_ext Σ ->
  Universe.is_sprop u ->
  isType Σ Γ A ->
  Σ ;;; Γ |- B : tSort u ->
  Σ ;;; Γ |- A <= B ->
  Σ ;;; Γ |- A : tSort u.
Proof.
  intros.
  destruct X0 as [s Hs].
  eapply cumul_sprop_inv in H. 4:eauto. pcuicfo. auto.
  right; eauto.
Qed.

Lemma cumul_sprop2 (Σ : global_env_ext) Γ A B u :
  wf_ext Σ ->
  Universe.is_sprop u ->
  isType Σ Γ B ->
  Σ ;;; Γ |- A <= B ->
  Σ ;;; Γ |- A : tSort u ->
  Σ ;;; Γ |- B : tSort u.
Proof.
  intros.
  destruct X0 as [s Hs].
  eapply cumul_sprop_inv in H. 4:eauto. pcuicfo. auto.
  left; eauto.
Qed.

End no_prop_leq_type.
