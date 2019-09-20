
From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From MetaCoq.Template Require Import config utils monad_utils BasicAst AstUtils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICTyping PCUICMetaTheory PCUICWcbvEval PCUICLiftSubst PCUICInversion PCUICSR PCUICNormal PCUICSafeLemmata PCUICPrincipality PCUICGeneration PCUICSubstitution PCUICElimination PCUICEquality PCUICContextConversion PCUICConversion.
From MetaCoq.SafeChecker Require Import PCUICSafeReduce PCUICSafeChecker.

From MetaCoq.Erasure Require EAst ELiftSubst ETyping EWcbvEval Extract.
From Equations Require Import Equations.
Require Import String.
Local Open Scope string_scope.
Set Asymmetric Patterns.
Import MonadNotation.

Require Import Extract.

Local Existing Instance extraction_checker_flags.

Lemma isErasable_Proof Σ Γ t :
  Is_proof Σ Γ t -> isErasable Σ Γ t.
Proof.
  intros. destruct X as (? & ? & ? & ? & ?). exists x. split. eauto. right. eauto.
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
  declared_inductive (fst Σ) mind ind idecl ->
  isArity (ind_type idecl).
Proof.
  intros. eapply PCUICWeakeningEnv.declared_inductive_inv with (P := typing) in H; eauto.
  - inv H. rewrite ind_arity_eq. rewrite <- it_mkProd_or_LetIn_app.
    clear.
    eapply it_mkProd_isArity. econstructor.
  - eapply PCUICWeakeningEnv.weaken_env_prop_typing.
Qed.

Lemma isWfArity_prod_inv:
  forall (Σ : global_env_ext) (Γ : context) (x : name) (x0 x1 : term),
    isWfArity typing Σ Γ (tProd x x0 x1) -> (∑ s : universe, Σ;;; Γ |- x0 : tSort s) ×   isWfArity typing Σ (Γ,, vass x x0) x1
.
  intros. destruct X as (? & ? & ? & ?). cbn in e.
  eapply destArity_app_Some in e as (? & ? & ?); subst.
  split.
  - unfold snoc, app_context in *. rewrite <- app_assoc in *.
    clear H. induction x4.
    + inv a. eauto.
    + cbn in a. inv a.
      * eapply IHx4. eauto.
      * eapply IHx4. eauto.
  - eexists. eexists. split; eauto. subst.
    unfold snoc, app_context in *. rewrite <- app_assoc in *. eassumption.
Qed.

Lemma isArity_subst:
  forall x2 : term, forall s n, isArity x2 -> isArity (subst s n x2).
Proof.
  induction x2; cbn in *; try tauto; intros; eauto.
Qed.

Lemma isArity_typing_spine:
  forall (Σ : global_env_ext) (Γ : context) (L : list term) (T x4 : term),
    wf Σ -> wf_local Σ Γ ->
    Is_conv_to_Arity Σ Γ x4 -> typing_spine Σ Γ x4 L T -> Is_conv_to_Arity Σ Γ T.
Proof.
  intros.
  depind X1.
  - destruct H as (? & ? & ?). sq.
    eapply PCUICCumulativity.red_cumul_inv in X1.
    eapply (cumul_trans _ _ _ _ _) in c; tea.
    eapply invert_cumul_arity_l in c; eauto.
  - eapply IHX1.
    destruct H as (? & ? & ?). sq.
    eapply PCUICCumulativity.red_cumul_inv in X2.
    eapply (cumul_trans _ _ _ _ _) in c; tea.
    eapply invert_cumul_arity_l in c; eauto.
    destruct c as (? & ? & ?). sq.
    eapply invert_red_prod in X3 as (? & ? & [] & ?); eauto; subst.
    exists (x2 {0 := hd}). split; sq.
    eapply (PCUICSubstitution.substitution_red Σ Γ [_] [] [_]). eauto. econstructor. econstructor.
    rewrite subst_empty. eassumption. eauto. cbn. eassumption. cbn in H1.
    now eapply isArity_subst.
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
  forall (Σ : PCUICAst.global_env_ext) Γ (args args' : list PCUICAst.term) (X : All2 (red Σ Γ) args args') (bla : wf Σ)
    (T x x0 : PCUICAst.term) (t0 : typing_spine Σ Γ x args x0) (c : Σ;;; Γ |- x0 <= T) (x1 : PCUICAst.term)
    (c0 : Σ;;; Γ |- x1 <= x), isWfArity_or_Type Σ Γ T -> typing_spine Σ Γ x1 args' T.
Proof.
  intros Σ Γ args args' X wf T x x0 t0 c x1 c0 ?. revert args' X.
  dependent induction t0; intros.
  - inv X. econstructor. eauto. eapply PCUICConversion.cumul_trans. assumption.
    eauto. eapply PCUICConversion.cumul_trans. assumption. eauto. eauto.
  - inv X. econstructor.
    + eauto.
    + eapply PCUICConversion.cumul_trans ; eauto.
    + eapply subject_reduction; eauto.
    + eapply IHt0; eauto.
      eapply PCUICCumulativity.red_cumul_inv.
      unfold PCUICLiftSubst.subst1.
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
           exists (x0 ++ [x])%list. now rewrite <- mkApps_nested.
        -- exists (l ++ [N2])%list. now rewrite <- mkApps_nested.
  - rewrite it_mkProd_or_LetIn_app in X.
    cbn in X.
    destruct x, decl_body; cbn in *.
    + dependent destruction X.
      * unfold subst1. rewrite subst_it_mkProd_or_LetIn, subst_mkApps. eauto.
      * destruct args using rev_ind; try rewrite <- mkApps_nested in x; cbn in x; inv x.
      * eexists (l ++ [Build_context_decl decl_name (Some r) decl_type])%list, l0.
        now rewrite it_mkProd_or_LetIn_app.
      * eexists (l ++ [Build_context_decl decl_name (Some t0) r])%list, l0.
        now rewrite it_mkProd_or_LetIn_app.
      * eapply IHL in X as (? & ? & ?). subst.
        eexists (x ++ [Build_context_decl decl_name (Some t0) decl_type])%list, x0.
        rewrite it_mkProd_or_LetIn_app. reflexivity.
    + dependent destruction X.
      * eapply (f_equal decompose_app) in x.
        rewrite decompose_app_mkApps in x; cbn; eauto. cbn in x. inv x.
      * eexists (l ++ [Build_context_decl decl_name None N1])%list, l0.
        now rewrite it_mkProd_or_LetIn_app.
      * eapply IHL in X as (? & ? & ?). subst.
        eexists (x ++ [Build_context_decl decl_name None decl_type])%list, x0.
        rewrite it_mkProd_or_LetIn_app. reflexivity.
Qed.

Lemma invert_it_Ind_red Σ L i u l t Γ : wf Σ ->
  red Σ Γ (it_mkProd_or_LetIn L (mkApps (tInd i u) l)) t -> exists L' l', t = it_mkProd_or_LetIn L' (mkApps (tInd i u) l').
Proof.
  intros. induction X0.
  - eauto.
  - destruct IHX0 as (? & ? & ->).
    eapply invert_it_Ind_red1 in r as (? & ? & ?); eauto.
Qed.

Lemma it_mkProd_red_Arity Σ  c0 i u l : wf Σ ->
  ~ Is_conv_to_Arity Σ [] (it_mkProd_or_LetIn c0 (mkApps (tInd i u) l)).
Proof.
  intros HS (? & [] & ?). eapply invert_it_Ind_red in X as (? & ? & ?). subst.
  eapply it_mkProd_arity in H. eapply isArity_mkApps in H as [[] ]. eauto.
Qed.

Lemma invert_it_Ind_eq_prod:
  forall (u : universe_instance) (i : inductive) (x : name) (x0 x1 : term) (x2 : context) (x3 : list term),
    tProd x x0 x1 = it_mkProd_or_LetIn x2 (mkApps (tInd i u) x3) -> exists (L' : context) (l' : list term), x1 = it_mkProd_or_LetIn L' (mkApps (tInd i u) l').
Proof.
  intros u i x x0 x1 x2 x3 H0.
  revert x0 x3 x1 x H0. induction x2 using rev_ind; intros.
  - cbn. assert (decompose_app (tProd x x0 x1) = decompose_app (mkApps (tInd i u) x3)) by now rewrite H0.
    rewrite decompose_app_mkApps in H; cbn; eauto. cbn in H. inv H.
  - rewrite it_mkProd_or_LetIn_app in *. cbn in *.
    destruct x, decl_body; cbn in H0; try now inv H0.
Qed.


Lemma tConstruct_no_Type (Σ : global_env_ext) ind c u x1 : wf Σ ->
  isErasable Σ [] (mkApps (tConstruct ind c u) x1) ->
  Is_proof Σ [] (mkApps (tConstruct ind c u) x1).
Proof.
  intros wfΣ (? & ? & [ | (? & ? & ?)]).
  - exfalso. eapply type_mkApps_inv in t as (? & ? & [] & ?); eauto.
    assert (HWF : isWfArity_or_Type Σ [] x2). eapply PCUICValidity.validity. eauto. econstructor.
    eapply type_mkApps. 2:eauto. eauto.
    eapply inversion_Construct in t as (? & ? & ? & ? & ? & ? & ?) ; auto. (* destruct x5. destruct p. cbn in *. *)
    assert (HL : #|ind_bodies x3| > 0). destruct d. destruct H. destruct (ind_bodies x3); cbn; try omega. rewrite nth_error_nil in H1. inv H1.
    eapply invert_cumul_arity_r in c0; eauto.
    (* eapply isArity_typing_spine_inv in t0; eauto. *)
    (* destruct t0 as (? & [] & ?). *)
    (* eapply PCUICCumulativity.red_cumul in X. *)
    eapply PCUICWeakeningEnv.declared_constructor_inv in d.
    2: eapply PCUICWeakeningEnv.weaken_env_prop_typing. 2:eauto. 2:eauto.
    cbn in d.
    (* eapply cumul_trans in X. 2:exact c2. *)
    (* eapply invert_cumul_arity_r in X; eauto. *)
    inv d. cbn in X0. destruct x5. destruct p. cbn in *.
    destruct X0. destruct x5. cbn in *. subst.
    unfold cshape_concl_head in *.

    rewrite <- it_mkProd_or_LetIn_app in c2.
    rewrite PCUICUnivSubst.subst_instance_constr_it_mkProd_or_LetIn in c2.
    rewrite PCUICUnivSubst.subst_instance_constr_mkApps in c2.
    rewrite PCUICSubstitution.subst_it_mkProd_or_LetIn in c2.
    rewrite subst_mkApps in c2.
    cbn in c2.
    rewrite PCUICUnivSubst.subst_instance_context_length in *.
    rewrite app_length in *.
    destruct (Nat.leb_spec (#|cshape_args| + #|ind_params x3| + 0) (#|ind_bodies x3| - S (inductive_ind ind) + #|ind_params x3| + #|cshape_args|)).
    2:omega. clear H.
    assert ((#|ind_bodies x3| - S (inductive_ind ind) + #|ind_params x3| +
                                                                         #|cshape_args| - (#|cshape_args| + #|ind_params x3| + 0)) < #|inds (inductive_mind ind) u (ind_bodies x3)|).
    rewrite inds_length. omega.
    eapply nth_error_Some in H.
    destruct ?; try congruence.
    (* destruct c2 as (? & [] & ?). *)
    eapply inds_nth_error in E as [].
    subst. cbn in *. revert c2.
    generalize (subst_context (inds (inductive_mind ind) u (ind_bodies x3)) 0
                              (PCUICUnivSubst.subst_instance_context u (cshape_args ++ ind_params x3)%list)).
    generalize ((map
             (subst (inds (inductive_mind ind) u (ind_bodies x3))
                (#|cshape_args| + #|ind_params x3| + 0))
             (map (PCUICUnivSubst.subst_instance_constr u)
                  (to_extended_list_k (ind_params x3) #|cshape_args| ++ cshape_indices)))).
    generalize ({| inductive_mind := inductive_mind ind; inductive_ind := x5 |}).
    clear - wfΣ HWF t0 c0. intros.
    destruct c0 as (? & [] & ?).
    eapply typing_spine_red in t0. 3:auto. 2:{ eapply PCUICCumulativity.All_All2_refl. clear. induction x1; eauto. }
    2: eapply PCUICCumulativity.red_cumul. 2: eassumption. 2:eapply PCUICCumulativity.cumul_refl'.
    clear - wfΣ t0 H c2.
    2:{ eapply isWfArity_or_Type_red; eassumption. }

    (* assert ((Σ;;; [] |- it_mkProd_or_LetIn c (mkApps (tInd i u) l) <= x0) + (Σ;;; [] |- x0 <= it_mkProd_or_LetIn c (mkApps (tInd i u) l))) by eauto. clear c2. *)
    rename c2 into X.
    revert c l X.
    depind t0; intros; subst.
    + eapply (cumul_trans _ _ _ _ _) in c; tea.
      eapply invert_cumul_arity_r in c; eauto.
      eapply it_mkProd_red_Arity; eauto.
    + eapply (cumul_trans _ _ _ _ _) in c; tea.
      eapply invert_cumul_prod_r in c as (? & ? & ? & [] & ?); eauto.

      eapply invert_it_Ind_red in r as (? & ? & ?); eauto.
      eapply invert_it_Ind_eq_prod in H0 as (? & ? & ?).
      subst.
      eapply IHt0; eauto.

      eapply (substitution_untyped_cumul Σ [] [_] [] [hd]) in c1.
      cbn in c1. 2:eauto. 2:{ repeat econstructor. }
      rewrite subst_it_mkProd_or_LetIn in c1.
      rewrite subst_mkApps in c1. eassumption.
  - exists x, x0. eauto.
Qed.                       (* if a constructor is a type or proof, it is a proof *)

Inductive conv_decls (Σ : global_env_ext) Γ (Γ' : context) : forall (x y : context_decl), Type :=
| conv_vass : forall (na na' : name) (T T' : term),
                (* isWfArity_or_Type Σ Γ' T' -> *)
                Σ;;; Γ |- T = T' -> conv_decls Σ Γ Γ' (vass na T) (vass na' T')
| conv_vdef_type : forall (na : name) (b T  : term),
    (* isWfArity_or_Type Σ Γ' T -> *)
    conv_decls Σ Γ Γ' (vdef na b T) (vdef na b T).

Lemma conv_context_refl (Σ : global_env_ext) Γ :
  wf Σ -> wf_local Σ Γ ->
  context_relation (@conv_decls Σ) Γ Γ.
Proof.
  induction Γ; try econstructor.
  intros wfΣ wfΓ; depelim wfΓ; econstructor; eauto;
  constructor; auto.
  - constructor; eapply cumul_refl; reflexivity.
Qed.

Lemma context_conversion_red1 (Σ : global_env_ext) Γ Γ' s t : wf Σ -> (* Σ ;;; Γ' |- t : T -> *)
   context_relation (@conv_decls Σ) Γ Γ' -> red1 Σ Γ s t -> red Σ Γ' s t.
Proof.
  intros HΣ HT X0. induction X0 using red1_ind_all in Γ', HΣ, HT |- *; eauto.
  Hint Constructors red red1.
  all:eauto.
  - econstructor. econstructor. econstructor.
    rewrite <- H.
    induction HT in i |- *; destruct i; eauto.
    now inv p.
  -
    eapply PCUICReduction.red_abs. eapply IHX0; eauto.  eauto.
  -
    eapply PCUICReduction.red_abs. eauto. eapply IHX0. eauto.
    eauto. econstructor. eauto. econstructor.
    eapply PCUICCumulativity.conv_refl'.
  -
    eapply PCUICReduction.red_letin. eapply IHX0; eauto.
    all:eauto.
  -
    eapply PCUICReduction.red_letin; eauto.
  -
    eapply PCUICReduction.red_letin; eauto. eapply IHX0; eauto.
    econstructor. eauto. econstructor.
  -     eapply PCUICReduction.reds_case; eauto. clear.
    eapply PCUICCumulativity.All_All2_refl. induction brs; eauto.
  -     eapply PCUICReduction.reds_case; eauto. clear.
    eapply PCUICCumulativity.All_All2_refl. induction brs; eauto.
  - destruct ind.
    eapply PCUICReduction.reds_case; eauto.
    clear - HΣ X HT.
    induction X.
    + econstructor. destruct p. destruct p.
      split; eauto.
      eapply PCUICCumulativity.All_All2_refl.
      induction tl; eauto.
    + econstructor.  repeat econstructor.
      eassumption.
  -
    eapply PCUICReduction.red_proj_c. eauto.
  -
    eapply PCUICReduction.red_app; eauto.
  -     eapply PCUICReduction.red_app; eauto.
  -
    eapply PCUICReduction.red_prod; eauto.
  -
    eapply PCUICReduction.red_prod; eauto. eapply IHX0. eauto. eauto.
    econstructor.
    eauto. econstructor. eapply PCUICCumulativity.conv_refl'.
  - eapply PCUICReduction.red_evar; eauto.
    induction X; eauto. econstructor. eapply p; eauto.
    induction tl; eauto.
  - eapply PCUICReduction.red_fix_one_ty.
    eapply OnOne2_impl ; eauto.
    intros [? ? ? ?] [? ? ? ?] [[r ih] e]. simpl in *.
    inversion e. subst. clear e.
    split ; auto.
  - eapply PCUICReduction.red_fix_one_body.
    eapply OnOne2_impl ; eauto.
    intros [? ? ? ?] [? ? ? ?] [[r ih] e]. simpl in *.
    inversion e. subst. clear e.
    split ; auto.
    eapply ih ; auto.
    clear - HT.
    induction (fix_context mfix0) as [| [na [b|] ty] Δ ihΔ].
    + auto.
    + simpl. constructor ; eauto.
      constructor.
    + simpl. constructor ; eauto.
      constructor. apply PCUICCumulativity.conv_refl'.
  - eapply PCUICReduction.red_cofix_one_ty.
    eapply OnOne2_impl ; eauto.
    intros [? ? ? ?] [? ? ? ?] [[r ih] e]. simpl in *.
    inversion e. subst. clear e.
    split ; auto.
  - eapply PCUICReduction.red_cofix_one_body.
    eapply OnOne2_impl ; eauto.
    intros [? ? ? ?] [? ? ? ?] [[r ih] e]. simpl in *.
    inversion e. subst. clear e.
    split ; auto.
    eapply ih ; auto.
    clear - HT.
    induction (fix_context mfix0) as [| [na [b|] ty] Δ ihΔ].
    + auto.
    + simpl. constructor ; eauto.
      constructor.
    + simpl. constructor ; eauto.
      constructor. apply PCUICCumulativity.conv_refl'.
Qed.

Lemma context_conversion_red (Σ : global_env_ext) Γ Γ' s t : wf Σ ->
  context_relation (@conv_decls Σ) Γ Γ' -> red Σ Γ s t -> red Σ Γ' s t.
Proof.
  intros. induction X1; eauto.
  etransitivity. eapply IHX1.
  eapply context_conversion_red1; eauto.
Qed.

Lemma isWfArity_or_Type_red:
  forall (Σ : global_env_ext) (Γ : context) (T : term), wf Σ -> wf_local Σ Γ ->
    isWfArity_or_Type Σ Γ T -> forall x5 : term, red Σ Γ T x5 -> isWfArity_or_Type Σ Γ x5.
Proof.
  intros. destruct X1 as [ | []].
  - left. eapply isWfArity_red ; eauto.
  - right. eexists. eapply subject_reduction ; eauto.
Qed.

Lemma is_prop_sort_sup:
  forall x1 x2 : universe, is_prop_sort (Universe.sup x1 x2) -> is_prop_sort x2.
Proof.
  induction x1; cbn; intros.
  - inv H.
  - inv H.
Qed.

Lemma is_prop_sort_prod x2 x3 :
  is_prop_sort (Universe.sort_of_product x2 x3) -> is_prop_sort x3.
Proof.
  intros. unfold Universe.sort_of_product in *. destruct ?; eauto.
  eapply is_prop_sort_sup in H. eauto.
Qed.

Lemma sort_typing_spine:
  forall (Σ : global_env_ext) (Γ : context) (L : list term) (u : universe) (x x0 : term),
    wf Σ ->
    is_prop_sort u ->
    typing_spine Σ Γ x L x0 -> Σ;;; Γ |- x : tSort u -> ∑ u', Σ;;; Γ |- x0 : tSort u' × is_prop_sort u'.
Proof.
  intros Σ Γ L u x x0 ? ? t1 c0.
  revert u H c0.
  depind t1; intros.
  - eapply cumul_prop2 in c0; eauto.
  - eapply cumul_prop2 in c0. 2:eauto. 2:auto. 2:eauto. 2:eauto.
    eapply invert_cumul_prod_r in c as (? & ? & ? & [] & ?); eauto.
    eapply subject_reduction in c0. 3:eauto. 2:eauto.
    eapply inversion_Prod in c0 as (? & ? & ? & ? & ?) ; auto.
    eapply PCUICConversion.cumul_Sort_inv in c0.
    eapply leq_universe_prop in c0 as []; cbn; eauto.

    eapply is_prop_sort_prod in H0. eapply IHt1. exact H0.
    change (tSort x3) with ((tSort x3) {0 := hd}).
    eapply PCUICSubstitution.substitution0. 2:eauto. eauto.
    econstructor. eassumption. 2: now destruct c. right; eauto.
Qed.

Lemma arity_type_inv (Σ : global_env_ext) Γ t T1 T2 : wf Σ -> wf_local Σ Γ ->
  Σ ;;; Γ |- t : T1 -> isArity T1 -> Σ ;;; Γ |- t : T2 -> Is_conv_to_Arity Σ Γ T2.
Proof.
  intros wfΣ wfΓ. intros. eapply principal_typing in X as (? & ? & ? & ?). 2:eauto. 2:exact X0.

  eapply invert_cumul_arity_r in c0 as (? & ? & ?); eauto. sq.
  eapply PCUICCumulativity.red_cumul_inv in X.
  eapply (cumul_trans _ _ _ _ _) in c; tea.

  eapply invert_cumul_arity_l in c as (? & ? & ?); eauto. sq.
  exists x1; split; sq; eauto.
Qed.

Lemma Is_type_app (Σ : global_env_ext) Γ t L T :
  wf Σ ->
  wf_local Σ Γ ->
  Σ ;;; Γ |- mkApps t L : T ->
  isErasable Σ Γ t ->
  ∥isErasable Σ Γ (mkApps t L)∥.
Proof.
  intros wfΣ wfΓ ? ?.
  assert (HW : isWfArity_or_Type Σ Γ T). eapply PCUICValidity.validity; eauto.
  eapply type_mkApps_inv in X as (? & ? & [] & ?); try eassumption.
  destruct X0 as (? & ? & [ | [u]]).
  - eapply PCUICPrincipality.principal_typing in t2 as (? & ? & ? & ?). 2:eauto. 2:exact t0.
    eapply invert_cumul_arity_r in c1; eauto.
    destruct c1 as (? & ? & ?). destruct H as [].
    eapply PCUICCumulativity.red_cumul_inv in X.

    eapply invert_cumul_arity_l in H0 as (? & ? & ?). 2:eauto. 2:eauto. 2: eapply PCUICConversion.cumul_trans; eauto.
    destruct H.
    eapply typing_spine_red in t1. 2:{ eapply PCUICCumulativity.All_All2_refl.
                                                  clear. induction L; eauto. }

    2:eauto. 2:eauto. 2: eapply PCUICCumulativity.red_cumul_inv. 2:eauto. 2:eauto.

    assert (t11 := t1).
    eapply isArity_typing_spine in t1 as (? & ? & ?). 2:eauto. 2:eauto. 2:eauto.
    sq. exists x5. split. eapply type_mkApps. eapply type_reduction in t0; eauto. 2:eauto.
    eapply typing_spine_red. eapply PCUICCumulativity.All_All2_refl.
    clear. induction L; eauto. eauto. eauto. 2:eapply PCUICCumulativity.cumul_refl'.
    eapply PCUICCumulativity.red_cumul. eauto.

    eapply isWfArity_or_Type_red; eauto. exists x4; split; sq; eauto.
  - destruct p.
    eapply PCUICPrincipality.principal_typing in t2 as (? & ? & ? & ?). 2:eauto. 2:exact t0.
    eapply cumul_prop1 in c1; eauto.
    eapply cumul_prop2 in c0; eauto.
    econstructor. exists x0. split. eapply type_mkApps. 2:eassumption. eassumption. right.
    eapply sort_typing_spine in t1; eauto.
Qed.

Lemma Is_type_lambda (Σ : global_env_ext) Γ na T1 t :
  wf Σ ->
  wf_local Σ Γ ->
  isErasable Σ Γ (tLambda na T1 t) ->
  ∥isErasable Σ (vass na T1 :: Γ) t∥.
Proof.
  intros ? ? (T & ? & ?).
  eapply inversion_Lambda in t0 as (? & ? & ? & ? & ?).
  destruct s as [ | (u & ? & ?)].
  - eapply invert_cumul_arity_r in c; eauto. destruct c as (? & [] & ?).
    eapply invert_red_prod in X1 as (? & ? & [] & ?); eauto; subst. cbn in H.
    econstructor. exists x3. econstructor. eapply type_reduction; eauto. econstructor; eauto. eexists; eauto.
    eauto.
  - sq. eapply cumul_prop1 in c; eauto.
    eapply inversion_Prod in c as (? & ? & ? & ? & ?) ; auto.
    eapply cumul_Sort_inv in c.
    eapply leq_universe_prop in c as []; cbn; eauto.
    eexists. split. eassumption. right. eexists. split. eassumption.
    unfold Universe.sort_of_product in H.
    destruct ?; eauto.

    eapply is_prop_sort_sup; eauto.
  - auto.
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

Lemma Is_type_eval (Σ : global_env_ext) Γ t v:
  wf Σ ->
  eval Σ Γ t v ->
  isErasable Σ Γ t ->
  isErasable Σ Γ v.
Proof.
  intros; eapply Is_type_red. eauto.
  eapply wcbeval_red; eauto. eauto.
Qed.
