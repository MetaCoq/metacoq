(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils 
  PCUICClosed PCUICTyping PCUICWcbvEval PCUICLiftSubst PCUICInversion PCUICArities
  PCUICSR PCUICGeneration PCUICSubstitution PCUICElimination
  PCUICContextConversion PCUICConversion PCUICCanonicity
  PCUICSpine PCUICInductives PCUICInductiveInversion PCUICConfluence PCUICPrincipality.

Require Import ssreflect.
From MetaCoq.Erasure Require Import Extract.
  
Require Import Program.
From Equations Require Import Equations.

Local Existing Instance extraction_checker_flags.

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
  eapply (PCUICWeakeningEnv.declared_inductive_inv PCUICWeakeningEnv.weaken_env_prop_typing) in H; eauto.
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
  eapply isType_tProd in i as [dom codom]; auto. 2:pcuic.
  split; auto.
  split; auto. 2:{ now eapply isType_wf_local in i. }
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

Lemma typing_spine_red :
  forall (Σ : global_env_ext) Γ (args args' : list PCUICAst.term) (X : All2 (red Σ Γ) args args') (bla : wf Σ)
    (T x x0 : PCUICAst.term) (t0 : typing_spine Σ Γ x args x0) (c : Σ;;; Γ |- x0 <= T) (x1 : PCUICAst.term)
    (c0 : Σ;;; Γ |- x1 <= x), isType Σ Γ T -> typing_spine Σ Γ x1 args' T.
Proof.
  intros Σ Γ args args' X wf T x x0 t0 c x1 c0 ?. revert args' X.
  dependent induction t0; intros.
  - inv X. econstructor. eauto. eapply cumul_trans. assumption.
    eauto. eapply cumul_trans. assumption. eauto. eauto.
  - inv X. econstructor.
    + eauto.
    + eapply cumul_trans ; eauto.
    + eapply subject_reduction; eauto.
    + eapply IHt0; eauto.
      eapply PCUICCumulativity.red_cumul_inv.
      unfold subst1.
      eapply (red_red Σ Γ [_] [] [_] [_]).
      eauto. econstructor. eauto. econstructor. econstructor. econstructor.
      Grab Existential Variables. all: repeat econstructor.
Qed.


Lemma invert_it_Ind_red1 Σ L i u l t Γ : wf Σ ->
  red1 Σ Γ (it_mkProd_or_LetIn L (mkApps (tInd i u) l)) t -> exists L' l', t = it_mkProd_or_LetIn L' (mkApps (tInd i u) l').
Proof.
  intros wfΣ.
  revert l t Γ. induction L using rev_ind; intros.
  - cbn in *. exists []. cbn. revert t X. induction l  using rev_ind; intros.
    + cbn in *. depelim X. assert (decompose_app (tInd i u) = decompose_app (mkApps (tFix mfix idx) args)) by now rewrite H.
        rewrite decompose_app_mkApps in H0; cbn; eauto. cbn in H0. inv H0.
    +   rewrite <- mkApps_nested in X. cbn in X.
        dependent destruction X.
        -- eapply (f_equal decompose_app) in x.
           rewrite decompose_app_mkApps in x; cbn; eauto. cbn in x. inv x.
        -- eapply (f_equal decompose_app) in x.
           rewrite !decompose_app_mkApps in x; cbn; eauto.
           change (tApp (mkApps (tInd i u) l) x0) with (mkApps (mkApps (tInd i u) l) [x0]) in x.
           rewrite mkApps_nested in x.
           rewrite !decompose_app_mkApps in x; cbn; eauto. cbn in x. inv x.
        -- eapply IHl in X as [].  subst.
           exists (x0 ++ [x]). now rewrite <- mkApps_nested.
        -- exists (l ++ [N2]). now rewrite <- mkApps_nested.
  - rewrite it_mkProd_or_LetIn_app in X.
    cbn in X.
    destruct x, decl_body; cbn in *.
    + dependent destruction X.
      * unfold subst1. rewrite subst_it_mkProd_or_LetIn subst_mkApps. eauto.
      * destruct args using rev_ind; try rewrite <- mkApps_nested in x; cbn in x; inv x.
      * eexists (l ++ [mkdecl decl_name (Some r) decl_type]), l0.
        now rewrite it_mkProd_or_LetIn_app.
      * eexists (l ++ [mkdecl decl_name (Some t0) r]), l0.
        now rewrite it_mkProd_or_LetIn_app.
      * eapply IHL in X as (? & ? & ?). subst.
        eexists (x ++ [mkdecl decl_name (Some t0) decl_type]), x0.
        rewrite it_mkProd_or_LetIn_app. reflexivity.
    + dependent destruction X.
      * eapply (f_equal decompose_app) in x.
        rewrite decompose_app_mkApps in x; cbn; eauto. cbn in x. inv x.
      * eexists (l ++ [mkdecl decl_name None N1]), l0.
        now rewrite it_mkProd_or_LetIn_app.
      * eapply IHL in X as (? & ? & ?). subst.
        eexists (x ++ [mkdecl decl_name None decl_type]), x0.
        rewrite it_mkProd_or_LetIn_app. reflexivity.
Qed.

Lemma invert_it_Ind_red Σ L i u l t Γ : wf Σ ->
  red Σ Γ (it_mkProd_or_LetIn L (mkApps (tInd i u) l)) t
  -> exists L' l', t = it_mkProd_or_LetIn L' (mkApps (tInd i u) l').
Proof.
  intros. induction X0 using red_rect'.
  - eauto.
  - destruct IHX0 as (? & ? & ->).
    eapply invert_it_Ind_red1 in X1 as (? & ? & ?); eauto.
Qed.

Lemma it_mkProd_red_Arity Σ Γ c0 i u l : wf Σ ->
  ~ Is_conv_to_Arity Σ Γ (it_mkProd_or_LetIn c0 (mkApps (tInd i u) l)).
Proof.
  intros HS (? & [] & ?). eapply invert_it_Ind_red in X as (? & ? & ?). subst.
  eapply it_mkProd_arity in H. eapply isArity_mkApps in H as [[] ]. eauto.
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

Lemma tConstruct_no_Type (Σ : global_env_ext) Γ ind c u x1 : wf Σ ->
  isErasable Σ Γ (mkApps (tConstruct ind c u) x1) ->
  Is_proof Σ Γ (mkApps (tConstruct ind c u) x1).
Proof.
  intros wfΣ (? & ? & [ | (? & ? & ?)]).
  - exfalso.
    pose proof (PCUICValidity.validity_term wfΣ t).
    eapply PCUICValidity.inversion_mkApps in t as (? & ? & ?); eauto.
    assert(c0 : Σ ;;; Γ |- x <= x) by reflexivity.
    revert c0 t0 i. generalize x at 1 3.
    intros x2 c0 t0 i.
    assert (HWF : isType Σ Γ x2).
    { eapply PCUICValidity.validity.
      - eauto.
      - eapply type_mkApps. 2:eauto. eauto.
    }
    eapply inversion_Construct in t as (? & ? & ? & ? & ? & ? & ?) ; auto. (* destruct x5. destruct p. cbn in *. *)
    assert (HL : #|ind_bodies x3| > 0).
    { destruct d. destruct H. destruct (ind_bodies x3); cbn; try lia.
      rewrite nth_error_nil in H1. inv H1.
    }
    eapply invert_cumul_arity_r in c0; eauto.
    (* eapply isArity_typing_spine_inv in t0; eauto. *)
    (* destruct t0 as (? & [] & ?). *)
    (* eapply PCUICCumulativity.red_cumul in X. *)
    destruct (PCUICWeakeningEnv.on_declared_constructor d) as [XX [s [XX1 Ht]]].
    destruct x5 as []; cbn in *; subst.
    destruct Ht; cbn in *. subst.
    change PCUICEnvironment.it_mkProd_or_LetIn with it_mkProd_or_LetIn in c2.
    change PCUICEnvironment.ind_params with ind_params in *.
    change PCUICEnvironment.to_extended_list_k with to_extended_list_k in *.
    rewrite <- it_mkProd_or_LetIn_app in c2.
    rewrite PCUICUnivSubst.subst_instance_it_mkProd_or_LetIn in c2.
    rewrite PCUICUnivSubst.subst_instance_mkApps in c2.
    rewrite subst_it_mkProd_or_LetIn in c2.
    rewrite subst_mkApps in c2.
    cbn in c2.
    rewrite subst_instance_length in c2.
    rewrite app_length in c2.
    destruct (Nat.leb_spec (#|cstr_args0| + #|ind_params x3| + 0) (#|ind_bodies x3| - S (inductive_ind ind) + #|ind_params x3| + #|cstr_args0|)). 2:lia.
    clear H.
    assert ((#|ind_bodies x3| - S (inductive_ind ind) + #|ind_params x3| +
    #|cstr_args0| - (#|cstr_args0| + #|ind_params x3| + 0)) < #|inds (inductive_mind ind) u (ind_bodies x3)|).
    { rewrite inds_length. lia. }
    eapply nth_error_Some in H.
    destruct (nth_error (inds _ _ _) _) eqn:Heq; try congruence.
    eapply inds_nth_error in Heq as [].
    subst. cbn in *. revert c2.
    match goal with
    | |- context [ it_mkProd_or_LetIn ?c _ ] =>
      generalize c
    end.
    match goal with
    | |- context [ mkApps _ ?l ] =>
      generalize l
    end.
    match goal with
    | |- context [ tInd ?i _ ] =>
      generalize i
    end.
    clear -a wfΣ HWF t0 c0. intros.
    destruct c0 as (? & [] & ?).
    eapply typing_spine_red in t0. 3:auto. 2:{ eapply All_All2_refl. clear. induction x1; eauto. }
    2: eapply PCUICCumulativity.red_cumul. 2: eassumption. 2:eapply PCUICCumulativity.cumul_refl'.
    clear - wfΣ t0 H c2.
    2:{ eapply isType_red; eauto. }

    (* assert ((Σ;;; [] |- it_mkProd_or_LetIn c (mkApps (tInd i u) l) <= x0) + (Σ;;; [] |- x0 <= it_mkProd_or_LetIn c (mkApps (tInd i u) l))) by eauto. clear c2. *)
    rename c2 into X.
    revert c l X H.
    depind t0; intros; subst.
    + eapply (cumul_trans _ _ _ _ _) in c; tea.
      eapply invert_cumul_arity_r in c; eauto.
      eapply it_mkProd_red_Arity; eauto.
    + eapply (cumul_trans _ _ _ _ _) in c; tea.
      eapply invert_cumul_prod_r in c as (? & ? & ? & [] & ?); eauto.
      destruct p.

      eapply invert_it_Ind_red in r as (? & ? & ?); eauto.
      eapply invert_it_Ind_eq_prod in H0 as (? & ? & ?).
      subst.
      eapply IHt0; eauto.

      eapply (substitution_untyped_cumul Σ Γ [_] [] [hd]) in c1.
      cbn in c1. 2:eauto. 2:{ repeat econstructor. }
      rewrite subst_it_mkProd_or_LetIn in c1.
      rewrite subst_mkApps in c1. eassumption.
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
    assert(c0 : Σ ;;; Γ |- x <= x) by reflexivity.
    revert c0 t0 i. generalize x at 1 3.
    intros x2 c0 t0 i.
    assert (HWF : isType Σ Γ x2).
    { eapply PCUICValidity.validity.
      - eauto.
      - eapply type_mkApps. 2:eauto. eauto.
    }
    eapply inversion_CoFix in t as (? & ? & ? & ? & ? & ? & ?) ; auto.
    eapply invert_cumul_arity_r in c0; eauto.
    eapply typing_spine_strengthen in t0; eauto.
    eapply wf_cofixpoint_spine in i1; eauto.
    2:eapply nth_error_all in a; eauto; simpl in a; eauto.
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
    destruct c0 as [? [[r] isA]].
    eapply red_mkApps_tInd in r as [args' [eq _]]; auto.
    subst x4.
    now eapply isArity_mkApps in isA.
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

Lemma cumul_propositional (Σ : global_env_ext) Γ A B u :
  wf_ext Σ ->
  is_propositional u ->
  isType Σ Γ B ->
  Σ ;;; Γ |- A <= B ->
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
    eapply inversion_Prod in c0 as (? & ? & ? & ? & ?) ; auto.
    eapply cumul_Sort_inv in c0.
    unfold is_propositional in H.
    destruct (Universe.is_prop u) eqn:isp => //.
    eapply leq_universe_prop_r in c0 as H0; cbn; eauto.
    eapply is_prop_sort_prod in H0. eapply IHt1; [unfold is_propositional; now rewrite -> H0|].
    change (tSort x0) with ((tSort x0) {0 := hd}).
    eapply substitution0; eauto.
    eapply leq_universe_sprop_r in c0 as H0; cbn; eauto.
    eapply is_sprop_sort_prod in H0. eapply IHt1; [unfold is_propositional; now rewrite -> H0, orb_true_r|].
    change (tSort x0) with ((tSort x0) {0 := hd}).
    eapply substitution0; eauto.
Qed.

Lemma arity_type_inv (Σ : global_env_ext) Γ t T1 T2 : wf_ext Σ -> wf_local Σ Γ ->
  Σ ;;; Γ |- t : T1 -> isArity T1 -> Σ ;;; Γ |- t : T2 -> Is_conv_to_Arity Σ Γ T2.
Proof.
  intros wfΣ wfΓ. intros. 
  eapply common_typing in X as (? & ? & ? & ?). 2:eauto. 2:exact X0.

  eapply invert_cumul_arity_r in c0 as (? & X & ?); eauto. sq.
  eapply PCUICCumulativity.red_cumul_inv in X.
  eapply (cumul_trans _ _ _ _ _) in c; tea.

  eapply invert_cumul_arity_l in c as (? & ? & ?); eauto. sq.
  exists x1; split; sq; eauto.
Qed.

Lemma cumul_prop1' (Σ : global_env_ext) Γ A B u :
  check_univs = true ->
  wf_ext Σ ->
  isType Σ Γ A ->
  is_propositional u ->
  Σ ;;; Γ |- B : tSort u ->
  Σ ;;; Γ |- A <= B ->
  Σ ;;; Γ |- A : tSort u.
Proof.
  intros.
  destruct X0 as [s Hs].
  destruct u => //.
  eapply cumul_prop1 in X2; eauto. now exists s.
  eapply cumul_sprop1 in X2; eauto. now exists s.
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
  - eapply common_typing in t2 as (? & ? & ? & ?). 2:eauto. 2:exact t0.
    eapply invert_cumul_arity_r in c0; eauto.
    destruct c0 as (? & ? & ?). destruct H as [].
    eapply PCUICCumulativity.red_cumul_inv in X.

    eapply invert_cumul_arity_l in H0 as (? & ? & ?).
    2: eapply cumul_trans; eauto.
    destruct H.
    eapply typing_spine_red in t1. 2:{ eapply All_All2_refl.
                                                  clear. induction L; eauto. }

    2:eauto. 2:reflexivity. 2: eapply PCUICCumulativity.red_cumul_inv. 2:eauto. 2:eauto.

    assert (t11 := t1).
    eapply isArity_typing_spine in t1 as (? & ? & ?). 2:eauto. 2:eauto. 2:eauto.
    sq. exists x4. split. eapply type_mkApps. eapply type_reduction in t0; eauto. 2:eauto.
    eapply typing_spine_red. eapply All_All2_refl.
    clear. induction L; eauto. eauto. eauto. 2:eapply PCUICCumulativity.cumul_refl'.
    eapply PCUICCumulativity.red_cumul. eauto.

    eapply isType_red; eauto. exists x3; split; sq; eauto.
  - destruct p.
    eapply PCUICPrincipality.common_typing in t2 as (? & ? & ? & ?). 2:eauto. 2:exact t0.
    eapply cumul_prop1' in c0; eauto.
    eapply cumul_propositional in c; eauto.
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
  eapply inversion_Lambda in t0 as (? & ? & ? & ? & ?); auto.
  destruct s as [ | (u & ? & ?)].
  - eapply invert_cumul_arity_r in c; eauto. destruct c as (? & [] & ?).
    eapply invert_red_prod in X1 as (? & ? & [] & ?); eauto; subst. cbn in H.
    econstructor. exists x3. econstructor. 
    eapply type_reduction; eauto. econstructor; eauto.
  - sq. eapply cumul_prop1' in c; eauto.
    eapply inversion_Prod in c as (? & ? & ? & ? & ?) ; auto.
    eapply cumul_Sort_inv in c.
    eapply leq_universe_propositional_r in c as H0; cbn; eauto.
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
  eapply type_reduction in HT; eauto.
  sq. exists T'; intuition auto.
  sq. exists T. intuition auto. right.
  destruct s as [u [vtu isp]].
  exists u; intuition auto.
  eapply cumul_propositional; eauto. now eapply PCUICValidity.validity in HT.
  eapply cumul_prop1'; eauto. now eapply PCUICValidity.validity in vP.
Qed.

Lemma nIs_conv_to_Arity_isWfArity_elim {Σ : global_env_ext} {Γ x} : 
  ~ Is_conv_to_Arity Σ Γ x ->
  isWfArity Σ Γ x ->
  False.
Proof.
  intros nis [isTy [ctx [s da]]]. apply nis.
  red. exists (it_mkProd_or_LetIn ctx (tSort s)).
  split. sq. apply destArity_spec_Some in da.
  simpl in da. subst x.
  reflexivity.
  now eapply it_mkProd_isArity.
Qed.

Definition isErasable_Type (Σ : global_env_ext) Γ T := 
  (Is_conv_to_Arity Σ Γ T +
    (∑ u : Universe.t, Σ;;; Γ |- T : tSort u × is_propositional u))%type.

Lemma isErasable_any_type {Σ Γ t T} : 
  wf_ext Σ -> 
  isErasable Σ Γ t ->
  Σ ;;; Γ |- t : T ->
  isErasable_Type Σ Γ T.
Proof.
  intros wfΣ [T' [Ht Ha]].
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
