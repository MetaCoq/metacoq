(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
  PCUICReduction
  PCUICClosed PCUICTyping PCUICWcbvEval PCUICLiftSubst PCUICInversion PCUICArities
  PCUICSR PCUICGeneration PCUICSubstitution PCUICElimination
  PCUICWeakeningEnvConv PCUICWeakeningEnvTyp
  PCUICWellScopedCumulativity
  PCUICContextConversion PCUICConversion PCUICCanonicity
  PCUICSpine PCUICInductives PCUICInductiveInversion PCUICConfluence 
  PCUICArities PCUICPrincipality.

Require Import ssreflect.
From MetaCoq.Erasure Require Import Extract.
  
Require Import Program.
From Equations Require Import Equations.

Local Existing Instance extraction_checker_flags.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

Lemma isErasable_Proof Σ Γ t :
  Is_proof Σ Γ t -> isErasable Σ Γ t.
Proof.
  intros. destruct X as (? & ? & ? & ? & ?). exists x. split. eauto. right.
  eauto.
Qed.

Lemma isType_red:
  forall (Σ : global_env_ext) (Γ : context) (T : term), wf Σ -> wf_local Σ Γ ->
    isType Σ Γ T -> forall x5 : term, red Σ Γ T x5 -> isType Σ Γ x5.
Proof.
  intros. destruct X1 as [].
  eexists. eapply subject_reduction ; eauto.
Qed.

Lemma it_mkProd_isArity:
  forall (l : list context_decl) A,
    isArity A ->
    isArity (it_mkProd_or_LetIn l A).
Proof.
  induction l; cbn; intros; eauto.
  eapply IHl. destruct a, decl_body; cbn; eauto.
Qed.

Lemma isArity_ind_type (Σ : global_env_ext) mind ind idecl :
  wf Σ ->
  declared_inductive (fst Σ) ind mind idecl ->
  isArity (ind_type idecl).
Proof.
  intros. 
  eapply (declared_inductive_inv weaken_env_prop_typing) in H; eauto.
  - inv H. rewrite ind_arity_eq.
    change PCUICEnvironment.it_mkProd_or_LetIn with it_mkProd_or_LetIn.
    rewrite <- it_mkProd_or_LetIn_app.
    clear.
    eapply it_mkProd_isArity. econstructor.
Qed.

Lemma isWfArity_prod_inv (Σ : global_env_ext) (Γ : context) (x : aname) (x0 x1 : term) :
    wf Σ ->
    isWfArity Σ Γ (tProd x x0 x1) -> (isType Σ Γ x0 × isWfArity Σ (Γ,, vass x x0) x1).
Proof.
  intros wfΣ (? & ? & ? & ?). cbn in e.
  eapply isType_tProd in i as [dom codom]; auto.
  split; auto.
  split; auto.
  clear dom codom.
  eapply destArity_app_Some in e as (? & ? & ?); subst.
  eexists. eexists; eauto.
Qed.

Lemma inds_nth_error ind u l n t :
  nth_error (inds ind u l) n = Some t -> exists n, t = tInd {| inductive_mind := ind ; inductive_ind := n |} u.
Proof.
  unfold inds in *. generalize (#|l|). clear. revert t.
  induction n; intros.
  - destruct n. cbn in H. congruence. cbn in H. inv H.
    eauto.
  - destruct n0. cbn in H. congruence. cbn in H.
    eapply IHn. eauto.
Qed.

Lemma it_mkProd_arity :
  forall (l : list context_decl) (A : term), isArity (it_mkProd_or_LetIn l A) -> isArity A.
Proof.
  induction l; cbn; intros.
  - eauto.
  - eapply IHl in H. destruct a, decl_body; cbn in *; eauto.
Qed.

Lemma isArity_mkApps t L : isArity (mkApps t L) -> isArity t /\ L = [].
Proof.
  revert t; induction L; cbn; intros.
  - eauto.
  - eapply IHL in H. cbn in H. tauto.
Qed.

Lemma typing_spine_red (Σ : global_env_ext) Γ (args args' : list PCUICAst.term) 
  (X : All2 (red Σ Γ) args args') (wfΣ : wf Σ)
  (T x x0 : PCUICAst.term) 
  (t0 : typing_spine Σ Γ x args x0) 
  (c : Σ;;; Γ ⊢ x0 ≤ T) x1
  (c0 : Σ;;; Γ ⊢ x1 ≤ x) :
  isType Σ Γ x1 ->
  isType Σ Γ T -> 
  typing_spine Σ Γ x1 args' T.
Proof.
  intros ? ?. revert args' X.
  dependent induction t0; intros.
  - inv X. econstructor; eauto. transitivity ty => //.
    now transitivity ty'.
  - inv X. econstructor; tea.
    + transitivity ty => //.
    + eapply subject_reduction; eauto.
    + eapply IHt0; eauto.
      eapply red_ws_cumul_pb_inv.
      unfold subst1.
      eapply isType_tProd in i0 as [dom codom]. 
      eapply (closed_red_red_subst (Δ := [vass na A]) (Γ' := [])); auto.
      simpl. eapply isType_wf_local in codom. fvs.
      constructor; auto. eapply into_closed_red; auto. fvs. fvs.
      repeat constructor. eapply isType_is_open_term in codom; fvs.
      eapply isType_apply in i0; tea.
      eapply subject_reduction; tea.
Qed.

Lemma it_mkProd_red_Arity {Σ : global_env_ext} {Γ c0 i u l} {wfΣ : wf Σ} : 
  ~ Is_conv_to_Arity Σ Γ (it_mkProd_or_LetIn c0 (mkApps (tInd i u) l)).
Proof.
  intros (? & [] & ?). eapply red_it_mkProd_or_LetIn_mkApps_Ind in X as (? & ? & ?). subst.
  eapply it_mkProd_arity in H. eapply isArity_mkApps in H as [[] ]. 
Qed.

Lemma invert_it_Ind_eq_prod:
  forall (u : Instance.t) (i : inductive) (x : aname) (x0 x1 : term) (x2 : context) (x3 : list term),
    tProd x x0 x1 = it_mkProd_or_LetIn x2 (mkApps (tInd i u) x3) -> exists (L' : context) (l' : list term), x1 = it_mkProd_or_LetIn L' (mkApps (tInd i u) l').
Proof.
  intros u i x x0 x1 x2 x3 H0.
  revert x0 x3 x1 x H0. induction x2 using rev_ind; intros.
  - cbn. assert (decompose_app (tProd x x0 x1) = decompose_app (mkApps (tInd i u) x3)) by now rewrite H0.
    rewrite decompose_app_mkApps in H; cbn; eauto. cbn in H. inv H.
  - rewrite it_mkProd_or_LetIn_app in H0. cbn in *.
    destruct x, decl_body; cbn in H0; try now inv H0.
Qed.

(* if a constructor is a type or proof, it is a proof *)

Lemma declared_constructor_type_not_arity {Σ : global_env_ext} {wfΣ : wf Σ} {Γ} {ind n mdecl idecl cdecl u} :
  declared_constructor Σ (ind, n) mdecl idecl cdecl ->
  ~ Is_conv_to_Arity Σ Γ (type_of_constructor mdecl cdecl (ind, n) u).
Proof.
  intros decl; sq.
  unfold type_of_constructor.
  destruct (on_declared_constructor decl) as [XX [s [XX1 Ht]]].
  rewrite (cstr_eq Ht). clear -wfΣ decl.
  rewrite !PCUICUnivSubst.subst_instance_it_mkProd_or_LetIn !subst_it_mkProd_or_LetIn.
  rewrite /cstr_concl.
  rewrite /cstr_concl_head. len.
  rewrite subst_cstr_concl_head.
  destruct decl as [[] ?]. now eapply nth_error_Some_length in H0.
  rewrite -it_mkProd_or_LetIn_app.
  now eapply it_mkProd_red_Arity.
Qed.

Lemma conv_to_arity_cumul {Σ : global_env_ext} {wfΣ : wf Σ} :
  forall (Γ : context) (C : term) T,
    Is_conv_to_Arity Σ Γ T ->
    Σ;;; Γ ⊢ C ≤ T ->
    Is_conv_to_Arity Σ Γ C.
Proof.
  intros Γ C T [? []] cum. sq.
  eapply invert_cumul_arity_r_gen; tea.
  exists x. split; auto. now sq.
Qed.

Lemma typing_spine_mkApps_Ind_ex {Σ : global_env_ext} {wfΣ : wf Σ} Γ Δ ind u args args' T' :
  typing_spine Σ Γ (it_mkProd_or_LetIn Δ (mkApps (tInd ind u) args)) args' T' ->
  ∑ Δ' args', Σ ;;; Γ ⊢ it_mkProd_or_LetIn Δ' (mkApps (tInd ind u) args') ≤ T'.
Proof.
  induction Δ in args, args' |- * using PCUICInduction.ctx_length_rev_ind.
  - simpl. intros sp.
    dependent elimination sp as [spnil i i' e|spcons i i' e e' c].
    * now exists [], args.
    * now eapply invert_cumul_ind_prod in e.
  - rewrite it_mkProd_or_LetIn_app /=; destruct d as [na [b|] ty].
    * rewrite /mkProd_or_LetIn /=. simpl => /= sp.
      eapply typing_spine_letin_inv in sp; eauto.
      rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r subst_mkApps /= in sp.
      apply (X (subst_context [b] 0 Γ0) ltac:(now len) _ _ sp).
    * rewrite /mkProd_or_LetIn /=. simpl => /= sp.
      simpl.
      dependent elimination sp as [spnil i i' e|spcons i i' e e' sp].
      { exists (Γ0 ++ [vass na ty]). 
        exists args. now rewrite it_mkProd_or_LetIn_app. }
      eapply ws_cumul_pb_Prod_Prod_inv in e as [eqna dom codom]; pcuic.
      eapply (substitution0_ws_cumul_pb (t:=hd0)) in codom; eauto.
      eapply typing_spine_strengthen in sp. 3:tea.
      rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r subst_mkApps /= in sp.
      apply (X (subst_context [hd0] 0 Γ0) ltac:(len; reflexivity) _ _ sp).
      eapply isType_apply in i; tea.
      eapply (type_ws_cumul_pb (pb:=Conv)); tea. 2:now symmetry.
      now eapply isType_tProd in i as [].
Qed.

Lemma typing_spine_Is_conv_to_Arity {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Δ ind u args args' T'} :
  typing_spine Σ Γ (it_mkProd_or_LetIn Δ (mkApps (tInd ind u) args)) args' T' ->
  ~ Is_conv_to_Arity Σ Γ T'.
Proof.
  move/typing_spine_mkApps_Ind_ex => [Δ' [args'' cum]].
  intros iscv.
  eapply invert_cumul_arity_r_gen in iscv; tea.
  now eapply it_mkProd_red_Arity in iscv.
Qed.

Lemma declared_constructor_typing_spine_not_arity {Σ : global_env_ext} {wfΣ : wf Σ} {Γ} {ind n mdecl idecl cdecl u args' T'} :
  declared_constructor Σ (ind, n) mdecl idecl cdecl ->
  typing_spine Σ Γ (type_of_constructor mdecl cdecl (ind, n) u) args' T' ->
  ~ Is_conv_to_Arity Σ Γ T'.
Proof.
  intros decl; sq.
  unfold type_of_constructor.
  destruct (on_declared_constructor decl) as [XX [s [XX1 Ht]]].
  rewrite (cstr_eq Ht). clear -wfΣ decl.
  rewrite !PCUICUnivSubst.subst_instance_it_mkProd_or_LetIn !subst_it_mkProd_or_LetIn.
  rewrite /cstr_concl.
  rewrite /cstr_concl_head. len.
  rewrite subst_cstr_concl_head.
  destruct decl as [[] ?]. now eapply nth_error_Some_length in H0.
  rewrite -it_mkProd_or_LetIn_app.
  apply typing_spine_Is_conv_to_Arity.
Qed.

Lemma type_mkApps_tConstruct_n_conv_arity (Σ : global_env_ext) Γ ind c u x1 T : wf Σ ->
  Σ ;;; Γ |- mkApps (tConstruct ind c u) x1 : T ->
  ~ Is_conv_to_Arity Σ Γ T.
Proof.
  intros.
  eapply PCUICValidity.inversion_mkApps in X0 as (? & ? & ?); eauto.
  eapply inversion_Construct in t as (? & ? & ? & ? & ? & ? & ?) ; auto.
  eapply typing_spine_strengthen in t0. 3:tea.
  eapply declared_constructor_typing_spine_not_arity in t0; tea.
  eapply PCUICValidity.validity. econstructor; eauto.
Qed.

Lemma nIs_conv_to_Arity_nArity {Σ : global_env_ext} {wfΣ : wf Σ} {Γ T} : 
  isType Σ Γ T ->
  ~ Is_conv_to_Arity Σ Γ T -> ~ isArity T.
Proof.
  intros isty nisc isa. apply nisc.
  exists T. split => //. sq.
  destruct isty as [s Hs].
  eapply wt_closed_red_refl; tea.
Qed.

Lemma tConstruct_no_Type (Σ : global_env_ext) Γ ind c u x1 : wf Σ ->
  isErasable Σ Γ (mkApps (tConstruct ind c u) x1) ->
  Is_proof Σ Γ (mkApps (tConstruct ind c u) x1).
Proof.
  intros wfΣ (? & ? & [ | (? & ? & ?)]).
  - exfalso. 
    eapply nIs_conv_to_Arity_nArity; tea.
    eapply PCUICValidity.validity; tea.
    eapply type_mkApps_tConstruct_n_conv_arity in t; auto.
  - exists x, x0. eauto.
Qed.                      

(* if a cofixpoint is a type or proof, it is a proof *)

Lemma tCoFix_no_Type (Σ : global_env_ext) Γ mfix idx x1 : wf Σ ->
  isErasable Σ Γ (mkApps (tCoFix mfix idx) x1) ->
  Is_proof Σ Γ (mkApps (tCoFix mfix idx) x1).
Proof.
  intros wfΣ (? & ? & [ | (? & ? & ?)]).
  - exfalso.
    eapply PCUICValidity.inversion_mkApps in t as (? & ? & ?); eauto.
    pose proof (typing_spine_isType_codom t0).
    assert(c0 : Σ ;;; Γ ⊢ x ≤ x) by now eapply (isType_ws_cumul_pb_refl).
    revert c0 t0 i. generalize x at 1 3.
    intros x2 c0 t0 i.
    assert (HWF : isType Σ Γ x2).
    { eapply PCUICValidity.validity.
      eapply type_mkApps. 2:eauto. eauto.
    }
    eapply inversion_CoFix in t as (? & ? & ? & ? & ? & ? & ?) ; auto.
    eapply invert_cumul_arity_r in c0; eauto.
    eapply typing_spine_strengthen in t0. 3:eauto.
    eapply wf_cofixpoint_spine in i1; eauto.
    2-3:eapply nth_error_all in a; eauto; simpl in a; eauto.
    destruct i1 as (Γ' & T & DA & ind & u & indargs & (eqT & ck) & cum).
    destruct (Nat.ltb #|x1| (context_assumptions Γ')).
    eapply invert_cumul_arity_r_gen in c0; eauto.
    destruct c0. destruct H as [[r] isA].
    move: r; rewrite subst_it_mkProd_or_LetIn eqT; autorewrite with len.
    rewrite PCUICSigmaCalculus.expand_lets_mkApps subst_mkApps /=.
    move/red_it_mkProd_or_LetIn_mkApps_Ind => [ctx' [args' eq]].
    subst x4. now eapply it_mkProd_arity, isArity_mkApps in isA.
    move: cum => [] Hx1; rewrite eqT PCUICSigmaCalculus.expand_lets_mkApps subst_mkApps /= => cum.
    eapply invert_cumul_arity_r_gen in c0; eauto.
    now eapply Is_conv_to_Arity_ind in c0.
  - eexists _, _; intuition eauto.
Qed.

Lemma typing_spine_wat (Σ : global_env_ext) (Γ : context) (L : list term)
  (x x0 : term) :
    wf Σ ->
    typing_spine Σ Γ x L x0 -> 
    isType Σ Γ x0.
Proof.
  intros wfΣ; induction 1; auto.
Qed.

Section Elim'.

Context `{cf : checker_flags}.
Context {Σ : global_env_ext} {wfΣ : wf_ext Σ}.
Variable Hcf : prop_sub_type = false.
Variable Hcf' : check_univs.

Lemma cumul_prop1 Γ A B u :
  Universe.is_prop u ->
  isType Σ Γ A ->
  Σ ;;; Γ |- B : tSort u ->
  Σ ;;; Γ ⊢ A ≤ B ->
  Σ ;;; Γ |- A : tSort u.
Proof.
  intros; eapply cumul_prop1; tea.
  now apply ws_cumul_pb_forget in X1.
Qed.

Lemma cumul_prop2 Γ A B u :
  Universe.is_prop u ->
  isType Σ Γ B ->
  Σ ;;; Γ ⊢ A ≤ B ->
  Σ ;;; Γ |- A : tSort u ->
  Σ ;;; Γ |- B : tSort u.
Proof.
  intros. eapply cumul_prop2; tea.
  now apply ws_cumul_pb_forget in X0.
Qed.

Lemma cumul_sprop1 Γ A B u :
  Universe.is_sprop u ->
  isType Σ Γ A ->
  Σ ;;; Γ |- B : tSort u ->
  Σ ;;; Γ ⊢ A ≤ B ->
  Σ ;;; Γ |- A : tSort u.
Proof.
  intros. eapply cumul_sprop1; tea.
  now apply ws_cumul_pb_forget in X1.
Qed.

Lemma cumul_sprop2 Γ A B u :
  Universe.is_sprop u ->
  isType Σ Γ B ->
  Σ ;;; Γ ⊢ A ≤ B ->
  Σ ;;; Γ |- A : tSort u ->
  Σ ;;; Γ |- B : tSort u.
Proof.
  intros. eapply cumul_sprop2; tea.
  now apply ws_cumul_pb_forget in X0.
Qed.
End Elim'.

Lemma cumul_propositional (Σ : global_env_ext) Γ A B u :
  wf_ext Σ ->
  is_propositional u ->
  isType Σ Γ B ->
  Σ ;;; Γ ⊢ A ≤ B ->
  Σ ;;; Γ |- A : tSort u ->
  Σ ;;; Γ |- B : tSort u.
Proof.
  intros wf.
  destruct u => //.
  intros _ [s Hs] cum Ha.
  eapply cumul_prop2; eauto. now exists s.
  intros _ [s Hs] cum Ha.
  eapply cumul_sprop2; eauto. now exists s.
Qed.

Lemma sort_typing_spine:
  forall (Σ : global_env_ext) (Γ : context) (L : list term) (u : Universe.t) (x x0 : term),
    wf_ext Σ ->
    is_propositional u ->
    typing_spine Σ Γ x L x0 -> 
    Σ;;; Γ |- x : tSort u -> 
    ∑ u', Σ;;; Γ |- x0 : tSort u' × is_propositional u'.
Proof.
  intros Σ Γ L u x x0 HΣ ? t1 c0.
  assert (X : wf Σ) by apply HΣ.
  revert u H c0.
  induction t1; intros.
  - destruct u => //. eapply cumul_prop2 in c0; eauto.
    eapply cumul_sprop2 in c0; eauto.
  - eapply cumul_propositional in c0; auto. 2-3: tea.
    eapply inversion_Prod in c0 as (? & ? & ? & ? & e0) ; auto.
    eapply ws_cumul_pb_Sort_inv in e0.
    unfold is_propositional in H.
    destruct (Universe.is_prop u) eqn:isp => //.
    eapply leq_universe_prop_r in e0 as H0; cbn; eauto.
    eapply is_prop_sort_prod in H0. eapply IHt1; [unfold is_propositional; now rewrite -> H0|].
    change (tSort x0) with ((tSort x0) {0 := hd}).
    eapply substitution0; eauto.
    eapply leq_universe_sprop_r in e0 as H0; cbn; eauto.
    eapply is_sprop_sort_prod in H0. eapply IHt1; [unfold is_propositional; now rewrite -> H0, orb_true_r|].
    change (tSort x0) with ((tSort x0) {0 := hd}).
    eapply substitution0; eauto.
Qed.

Lemma arity_type_inv (Σ : global_env_ext) Γ t T1 T2 : wf_ext Σ -> wf_local Σ Γ ->
  Σ ;;; Γ |- t : T1 -> isArity T1 -> Σ ;;; Γ |- t : T2 -> Is_conv_to_Arity Σ Γ T2.
Proof.
  intros wfΣ wfΓ. intros. 
  destruct (common_typing _ _ X X0) as (? & e & ? & ?). 
  eapply invert_cumul_arity_l_gen; tea.
  eapply invert_cumul_arity_r_gen. 2:exact e.
  exists T1. split; auto. sq.
  eapply PCUICValidity.validity in X as [s Hs].
  eapply wt_closed_red_refl; eauto.
Qed.

Lemma cumul_prop1' (Σ : global_env_ext) Γ A B u :
  check_univs ->
  wf_ext Σ ->
  isType Σ Γ A ->
  is_propositional u ->
  Σ ;;; Γ |- B : tSort u ->
  Σ ;;; Γ ⊢ A ≤ B ->
  Σ ;;; Γ |- A : tSort u.
Proof.
  intros.
  destruct X0 as [s Hs].
  destruct u => //.
  eapply cumul_prop1 in X2; eauto. now exists s.
  eapply cumul_sprop1 in X2; eauto. now exists s.
Qed.

Lemma cumul_prop2' (Σ : global_env_ext) Γ A B u :
  check_univs ->
  wf_ext Σ ->
  isType Σ Γ A ->
  is_propositional u ->
  Σ ;;; Γ |- B : tSort u ->
  Σ ;;; Γ ⊢ B ≤ A ->
  Σ ;;; Γ |- A : tSort u.
Proof.
  intros.
  destruct X0 as [s Hs].
  destruct u => //.
  eapply cumul_prop2 in X2; eauto. now exists s.
  eapply cumul_sprop2 in X2; eauto. now exists s.
Qed.

Lemma leq_term_propositional_sorted_l {Σ Γ v v' u u'} :
  wf_ext Σ ->
  PCUICEquality.leq_term Σ (global_ext_constraints Σ) v v' ->
  Σ;;; Γ |- v : tSort u ->
  Σ;;; Γ |- v' : tSort u' -> is_propositional u -> 
  leq_universe (global_ext_constraints Σ) u' u.
Proof.
  intros wf leq Hv Hv' isp.
  unfold is_propositional in isp.
  destruct u => //.
  eapply leq_term_prop_sorted_l; eauto.
  eapply leq_term_sprop_sorted_l; eauto.
Qed.

Lemma leq_term_propopositional_sorted_r {Σ Γ v v' u u'} :
  wf_ext Σ ->
  PCUICEquality.leq_term Σ (global_ext_constraints Σ) v v' ->
  Σ;;; Γ |- v : tSort u ->
  Σ;;; Γ |- v' : tSort u' -> is_propositional u' -> 
  leq_universe (global_ext_constraints Σ) u u'.
Proof.
  intros wfΣ leq hv hv' isp.
  unfold is_propositional in isp.
  destruct u' => //.
  eapply leq_term_prop_sorted_r; eauto.
  eapply leq_term_sprop_sorted_r; eauto.
Qed.

Lemma Is_type_app (Σ : global_env_ext) Γ t L T :
  wf_ext Σ ->
  wf_local Σ Γ ->
  Σ ;;; Γ |- mkApps t L : T ->
  isErasable Σ Γ t ->
  ∥isErasable Σ Γ (mkApps t L)∥.
Proof.
  intros wfΣ wfΓ ? ?.
  assert (HW : isType Σ Γ T). eapply PCUICValidity.validity; eauto.
  eapply PCUICValidity.inversion_mkApps in X as (? & ? & ?); auto.
  destruct X0 as (? & ? & [ | [u]]).
  - eapply common_typing in t2 as (? & e & e0 & ?). 2:eauto. 2:exact t0.
    eapply invert_cumul_arity_r in e0; eauto.
    destruct e0 as (? & ? & ?). destruct H as [].
    eapply ws_cumul_pb_red_l_inv in e. 2:exact X.
    eapply type_reduction_closed in t2; tea.
    eapply typing_spine_strengthen in t1. 3:tea.
    unshelve epose proof (isArity_typing_spine wfΓ t1).
    2:{ eapply PCUICValidity.validity in t2; tea; pcuic. }
    forward H. eapply arity_type_inv; tea.
    destruct H as [T' [[]]].
    sq. exists T'. split. eapply type_mkApps; tea.
    eapply typing_spine_weaken_concl; tea.
    now eapply red_conv.
    eapply isType_red; tea; pcuic. exact X0.
    now left.
  - destruct p.
    eapply PCUICPrincipality.common_typing in t2 as (? & e & e0 & ?). 2:eauto. 2:exact t0.
    eapply cumul_prop1' in e0; eauto.
    eapply cumul_propositional in e; eauto.
    econstructor. exists T. split. eapply type_mkApps. 2:eassumption. eassumption. right.
    eapply sort_typing_spine in t1; eauto.
    now eapply PCUICValidity.validity in t0.
    now apply PCUICValidity.validity in t2.
Qed.

Lemma leq_universe_propositional_r {cf : checker_flags} (ϕ : ConstraintSet.t) (u1 u2 : Universe.t_) :
  check_univs ->
  consistent ϕ ->
  leq_universe ϕ u1 u2 -> is_propositional u2 -> is_propositional u1.
Proof.
  intros cu cons leq; unfold is_propositional.
  destruct u2 => //.
  apply leq_universe_prop_r in leq => //.
  now rewrite leq.
  intros _.
  apply leq_universe_sprop_r in leq => //.
  now rewrite leq orb_true_r.
Qed.

Lemma leq_universe_propositional_l {cf : checker_flags} (ϕ : ConstraintSet.t) (u1 u2 : Universe.t_) :
  check_univs ->
  prop_sub_type = false ->
  consistent ϕ ->
  leq_universe ϕ u1 u2 -> is_propositional u1 -> is_propositional u2.
Proof.
  intros cu ps cons leq; unfold is_propositional.
  destruct u1 => //.
  eapply leq_universe_prop_no_prop_sub_type in leq => //.
  now rewrite leq.
  intros _.
  apply leq_universe_sprop_l in leq => //.
  now rewrite leq orb_true_r.
Qed.

Lemma is_propositional_sort_prod x2 x3 :
  is_propositional (Universe.sort_of_product x2 x3) -> is_propositional x3.
Proof.
  unfold is_propositional.
  destruct (Universe.is_prop (Universe.sort_of_product x2 x3)) eqn:eq => //.
  simpl.
  intros _.
  apply is_prop_sort_prod in eq. now rewrite eq.
  destruct (Universe.is_sprop (Universe.sort_of_product x2 x3)) eqn:eq' => //.
  apply is_sprop_sort_prod in eq'. now rewrite eq' !orb_true_r.
Qed.

Lemma Is_type_lambda (Σ : global_env_ext) Γ na T1 t :
  wf_ext Σ ->
  wf_local Σ Γ ->
  isErasable Σ Γ (tLambda na T1 t) ->
  ∥isErasable Σ (vass na T1 :: Γ) t∥.
Proof.
  intros ? ? (T & ? & ?).
  eapply inversion_Lambda in t0 as (? & ? & ? & ? & e); auto.
  destruct s as [ | (u & ? & ?)].
  - eapply invert_cumul_arity_r in e; eauto. destruct e as (? & [] & ?).
    eapply invert_red_prod in X1 as (? & ? & []); eauto; subst. cbn in H.
    econstructor. exists x3. econstructor. 
    eapply type_reduction_closed; eauto. econstructor; eauto.
  - sq. eapply cumul_prop1' in e; eauto.
    eapply inversion_Prod in e as (? & ? & ? & ? & e) ; auto.
    eapply ws_cumul_pb_Sort_inv in e.
    eapply leq_universe_propositional_r in e as H0; cbn; eauto.
    eexists. split. eassumption. right. eexists. split. eassumption.
    eapply is_propositional_sort_prod in H0; eauto.
    eapply type_Lambda in t1; eauto. 
    now apply PCUICValidity.validity in t1.
Qed.

Lemma Is_type_red (Σ : global_env_ext) Γ t v:
  wf Σ ->
  red Σ Γ t v ->
  isErasable Σ Γ t ->
  isErasable Σ Γ v.
Proof.
  intros ? ? (T & ? & ?).
  exists T. split.
  - eapply subject_reduction; eauto.
  - eauto.
Qed.

Lemma Is_type_eval (Σ : global_env_ext) t v:
  wf Σ ->
  eval Σ t v ->
  isErasable Σ [] t ->
  isErasable Σ [] v.
Proof.
  intros; eapply Is_type_red. eauto.
  red in X1. destruct X1 as [T [HT _]].
  eapply wcbeval_red; eauto. assumption.
Qed.

(* Thanks to the restriction to Prop </= Type, erasability is also closed by expansion 
  on well-typed terms. *)

Lemma Is_type_eval_inv (Σ : global_env_ext) t v:
  wf_ext Σ ->
  PCUICSafeLemmata.welltyped Σ [] t ->
  PCUICWcbvEval.eval Σ t v ->
  isErasable Σ [] v ->
  ∥ isErasable Σ [] t ∥.
Proof.
  intros wfΣ [T HT] ev [vt [Ht Hp]].
  eapply wcbeval_red in ev; eauto.
  pose proof (subject_reduction _ _ _ _ _ wfΣ.1 HT ev).
  pose proof (common_typing _ wfΣ Ht X) as [P [Pvt [Pt vP]]].
  destruct Hp.
  eapply arity_type_inv in X. 5:eauto. all:eauto.
  red in X. destruct X as [T' [[red] isA]].
  eapply type_reduction_closed in HT; eauto.
  sq. exists T'; intuition auto.
  sq. exists T. intuition auto. right.
  destruct s as [u [vtu isp]].
  exists u; intuition auto.
  eapply cumul_propositional; eauto. now eapply PCUICValidity.validity in HT.
  eapply cumul_prop1'; eauto. now eapply PCUICValidity.validity in vP.
Qed.

Lemma isType_closed_red_refl {Σ} {wfΣ : wf Σ} {Γ T} :
  isType Σ Γ T -> Σ ;;; Γ ⊢ T ⇝ T.
Proof.
  intros [s hs]; eapply wt_closed_red_refl; tea.
Qed.

Lemma nIs_conv_to_Arity_isWfArity_elim {Σ} {wfΣ : wf Σ} {Γ x} : 
  ~ Is_conv_to_Arity Σ Γ x ->
  isWfArity Σ Γ x ->
  False.
Proof.
  intros nis [isTy [ctx [s da]]]. apply nis.
  red. exists (it_mkProd_or_LetIn ctx (tSort s)).
  split. sq. apply destArity_spec_Some in da.
  simpl in da. subst x.
  eapply isType_closed_red_refl; pcuic.
  now eapply it_mkProd_isArity.
Qed.

Definition isErasable_Type (Σ : global_env_ext) Γ T := 
  (Is_conv_to_Arity Σ Γ T +
    (∑ u : Universe.t, Σ;;; Γ |- T : tSort u × is_propositional u))%type.

Lemma isErasable_any_type {Σ} {wfΣ : wf_ext Σ} {Γ t T} : 
  isErasable Σ Γ t ->
  Σ ;;; Γ |- t : T ->
  isErasable_Type Σ Γ T.
Proof.
  intros [T' [Ht Ha]].
  intros HT.
  destruct (PCUICPrincipality.common_typing _ wfΣ Ht HT) as [P [le [le' tC]]]. sq.
  destruct Ha.
  left. eapply arity_type_inv. 3:exact Ht. all:eauto using typing_wf_local.
  destruct s as [u [Hu isp]].
  right.
  exists u; split; auto.
  eapply cumul_propositional; eauto. eapply PCUICValidity.validity; eauto.
  eapply cumul_prop1'; eauto. eapply PCUICValidity.validity; eauto.
Qed.
