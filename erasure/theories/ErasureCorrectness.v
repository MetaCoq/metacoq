(* Distributed under the terms of the MIT license. *)
From Coq Require Import Program.
From MetaCoq.Template Require Import config utils.
From MetaCoq.Erasure Require Import ELiftSubst ETyping EWcbvEval Extract Prelim
     ESubstitution EInversion EArities EDeps.
From MetaCoq.PCUIC Require Import PCUICTyping PCUICAst PCUICAstUtils
  PCUICWeakening PCUICSubstitution PCUICArities
  PCUICWcbvEval PCUICSR  PCUICInversion
  PCUICUnivSubstitution PCUICElimination PCUICCanonicity
  PCUICUnivSubst PCUICWeakeningEnv PCUICCumulativity PCUICSafeLemmata
  PCUICArities PCUICInductiveInversion
  PCUICOnFreeVars PCUICWellScopedCumulativity PCUICValidity.
Require Import Equations.Prop.DepElim.
Require Import ssreflect.

Local Set Keyed Unification.

Module PA := PCUICAst.
Module P := PCUICWcbvEval.

Local Existing Instance config.extraction_checker_flags.

(** ** Prelim on arities and proofs *)

Lemma isArity_subst_instance u T :
  isArity T ->
  isArity (subst_instance u T).
Proof.
  induction T; cbn; intros; tauto.
Qed.

Lemma wf_ext_wk_wf {cf:checker_flags} Σ : wf_ext_wk Σ -> wf Σ.
Proof. intro H; apply H. Qed.

#[global]
Hint Resolve wf_ext_wk_wf : core.

Lemma isErasable_subst_instance (Σ : global_env_ext) Γ T univs u :
  wf_ext_wk Σ ->  wf_local Σ Γ ->
  wf_local (Σ.1, univs) (subst_instance u Γ) ->
  isErasable Σ Γ T ->
  sub_context_set (monomorphic_udecl Σ.2) (global_ext_context_set (Σ.1, univs)) ->
  consistent_instance_ext (Σ.1,univs) (Σ.2) u ->
  isErasable (Σ.1,univs) (subst_instance u Γ) (subst_instance u T).
Proof.
  intros. destruct X2 as (? & ? & [ | (? & ? & ?)]).
  - eapply typing_subst_instance in t; eauto.
    eexists. split.
    + eapply t; tas.
    + left. eapply isArity_subst_instance. eauto.
  - eapply typing_subst_instance in t; eauto.
    eexists. split.
    + eapply t; tas.
    + right.
      eapply typing_subst_instance in t0; eauto.
      eexists. split.
      * eapply t0; tas.
      * now rewrite is_propositional_subst_instance.
Qed.

(** * Correctness of erasure  *)

Notation "Σ |-p s ▷ t" := (eval Σ s t) (at level 50, s, t at next level) : type_scope.
Notation "Σ ⊢ s ▷ t" := (Ee.eval Σ s t) (at level 50, s, t at next level) : type_scope.

(** ** Erasure is stable under context conversion *)

Lemma Is_type_conv_context (Σ : global_env_ext) (Γ : context) t (Γ' : context) :
  wf Σ -> wf_local Σ Γ -> wf_local Σ Γ' ->
  conv_context Σ Γ Γ' -> isErasable Σ Γ t -> isErasable Σ Γ' t.
Proof.
  intros.
  destruct X3 as (? & ? & ?). red.
  exists x. split. eapply PCUICContextConversion.context_conversion. 3:eapply X2. all:eauto.
  destruct s as [? | [u []]].
  - left. eauto.
  - right. exists u. split; eauto. eapply PCUICContextConversion.context_conversion in X2; eauto.
Qed.

Lemma wf_local_rel_conv:
  forall Σ : global_env × universes_decl,
    wf Σ.1 ->
    forall Γ Γ' : context,
      All2_fold (conv_decls Σ) Γ Γ' ->
      forall Γ0 : context, wf_local Σ Γ' -> wf_local_rel Σ Γ Γ0 -> wf_local_rel Σ Γ' Γ0.
Proof.
  intros Σ wfΣ Γ Γ' X1 Γ0 ? w0. induction w0.
  - econstructor.
  - econstructor; eauto. cbn in *.
    destruct t0. exists x. eapply PCUICContextConversion.context_conversion with (Γ ,,, Γ0); eauto.
    * eapply wf_local_app; eauto.
    * eapply conv_context_app; eauto.
      eapply typing_wf_local; eauto.
  - econstructor; eauto.
    + cbn in *.
      destruct t0. exists x. eapply PCUICContextConversion.context_conversion with (Γ ,,, Γ0); eauto.
      * eapply wf_local_app; eauto.
      * eapply conv_context_app; eauto.
        eapply typing_wf_local; eauto.
    + cbn in *. eapply PCUICContextConversion.context_conversion with (Γ ,,, Γ0); eauto.
      * eapply wf_local_app; eauto.
      * eapply conv_context_app; eauto.
        eapply typing_wf_local; eauto.
Qed.

#[global]
Hint Resolve Is_type_conv_context : core.

Lemma conv_context_wf_local_app A B A' Σ :
  wf_local Σ (A ,,, B) -> wf_local Σ A' -> conv_context Σ A A' -> wf_local Σ (A' ,,, B).
Proof.
  
Admitted.


Lemma erases_context_conversion :
  env_prop
  (fun (Σ : global_env_ext) (Γ : context) (t T : PCUICAst.term) =>
      forall Γ' : context,
        conv_context Σ Γ Γ' ->
        wf_local Σ Γ' ->
        forall t', erases Σ Γ t t' -> erases Σ Γ' t t')
  (fun Σ Γ => wf_local Σ Γ)
        .
Proof.
  apply typing_ind_env; intros Σ wfΣ Γ wfΓ; intros **; rename_all_hyps; auto.
  all: match goal with [ H : erases _ _ ?a _ |- ?G ] => tryif is_var a then idtac else invs H end.
  all: try now (econstructor; eauto).
  - econstructor. eapply h_forall_Γ'0.
    econstructor. eauto. now constructor.
    constructor; auto.
    exists s1.
    eapply PCUICContextConversion.context_conversion. 3:eauto. all:eauto.
  - econstructor. eauto. eapply h_forall_Γ'1.
    econstructor. eauto. now constructor.
    constructor; auto. exists s1.
    eapply PCUICContextConversion.context_conversion with Γ; eauto.
    eapply PCUICContextConversion.context_conversion with Γ; eauto.
    eassumption.
  - econstructor. eauto. eauto.
    eapply (All2i_All2_All2 X7 X0).
    intros ? ? ? [] (? & ? & ? & ? & ? & ?) (? & ?).
    split. 2: assumption.
    rewrite <- (PCUICCasesContexts.inst_case_branch_context_eq a).
    eapply e.
    + rewrite case_branch_type_fst.
      eapply conv_context_app; eauto.
    + eapply typing_wf_local.
      eapply PCUICContextConversion.context_conversion.
      * exact t1.
      * eapply conv_context_wf_local_app; eauto.
      * eapply conv_context_app; eauto.
    + now rewrite case_branch_type_fst (PCUICCasesContexts.inst_case_branch_context_eq a).
  - econstructor.

    eapply All2_impl. eapply All2_All_mix_left. eassumption. eassumption.
    intros. cbn in *.
    decompose [prod] X2. intuition auto.
    eapply b0.
    + subst types.
      eapply conv_context_app; auto.
    + eapply conv_context_wf_local_app; eauto.
    + assumption. 
  - econstructor.

    eapply All2_impl. eapply All2_All_mix_left. eassumption. eassumption.
    intros. cbn in *.
    decompose [prod] X2. intuition auto.
    eapply b0.
    + subst types. eapply conv_context_app; auto.
    + subst types. eapply conv_context_wf_local_app; eauto.
    + assumption.
Qed.

(** ** Erasure is stable under substituting universe constraints  *)

Lemma fix_context_subst_instance:
  forall (mfix : list (BasicAst.def term)) (u : Instance.t),
    map (map_decl (subst_instance u))
        (fix_context mfix) =
    fix_context
      (map
         (map_def (subst_instance u)
                  (subst_instance u)) mfix).
Proof.
  intros mfix. unfold fix_context. intros.
  rewrite map_rev.
  rewrite mapi_map.
  rewrite map_mapi. f_equal. eapply mapi_ext. intros. cbn.
  unfold map_decl. cbn. unfold vass.
  rewrite subst_instance_lift. reflexivity.
Qed.

Lemma erases_ext_eq Σ Σ' Γ Γ' t1 t1' t2 t2' :
  Σ ;;; Γ |- t1 ⇝ℇ t2 ->
  Σ = Σ'-> Γ = Γ' -> t1 = t1' -> t2 = t2' ->
  Σ' ;;; Γ' |- t1' ⇝ℇ t2'.
Proof.
  intros. now subst.
Qed.

Lemma erases_subst_instance0
  : env_prop (fun Σ Γ t T => wf_ext_wk Σ ->
                           forall t' u univs,
                             wf_local (Σ.1, univs) (subst_instance u Γ) ->
      sub_context_set (monomorphic_udecl Σ.2) (global_ext_context_set (Σ.1, univs)) ->
      consistent_instance_ext (Σ.1,univs) (Σ.2) u ->
    Σ ;;; Γ |- t ⇝ℇ t' ->
    (Σ.1,univs) ;;; (subst_instance u Γ) |- subst_instance u t ⇝ℇ t')
    (fun Σ Γ => wf_local Σ Γ).
Proof.
  apply typing_ind_env; intros; cbn -[subst_instance] in *; auto.
  all: match goal with [ H : erases _ _ ?a _ |- ?G ] => tryif is_var a then idtac else invs H end.
  all: try now (econstructor; eauto 2 using isErasable_subst_instance).
  - cbn. econstructor.
    eapply H0 in X2; eauto. apply X2.
    cbn. econstructor. eauto. cbn. econstructor.
    eapply typing_subst_instance in X0; eauto. apply snd in X0.
    cbn in X0. destruct X0. refine (t0 _ _ _ _ _); eauto.
  - cbn. econstructor.
    eapply H0 in X3; eauto.
    eapply H1 in X3; eauto. exact X3.
    cbn. econstructor. eauto. cbn. econstructor.
    eapply typing_subst_instance in X0; eauto. apply snd in X0.
    cbn in X0.
    eapply X0; eauto.
    cbn. eapply typing_subst_instance in X1; eauto. apply snd in X1.
    cbn in X1. eapply X1; eauto.
  - unfold subst_instance.
    cbn [PA.subst_instance_constr]. econstructor; eauto.
    eapply All2_map_left.
    eapply (All2i_All2_All2 X7 X10).
    intros ? ? [] [] (? & ? & ? & ? & ? & ?) (? & ?). split.
    2: now cbn in *.
    cbn -[app_context] in *. fold (subst_instance u bbody).
    eapply erases_ext_eq. 
    2, 4, 5: reflexivity. eapply e; eauto.
    + eapply typing_subst_instance_wf_local; eauto.
      destruct Σ; eassumption.
    + rewrite case_branch_type_fst PCUICCasesContexts.inst_case_branch_context_eq; eauto.
    + rewrite case_branch_type_fst PCUICCasesContexts.inst_case_branch_context_eq; eauto.
      rewrite subst_instance_app. unfold app_context. f_equal.
      now rewrite inst_case_branch_context_subst_instance.
  - assert (Hw :  wf_local (Σ.1, univs) (subst_instance u (Γ ,,, types))).
    { (* rewrite subst_instance_app. *)
      assert(All (fun d => isType Σ Γ (dtype d)) mfix).
      eapply (All_impl X0); pcuicfo.
      now destruct X5 as [s [Hs ?]]; exists s.
      eapply All_mfix_wf in X5; auto. subst types.
      
      revert X5. clear - wfΣ wfΓ H2 H3 X2 X3.
      induction 1.
      - eauto.
      - cbn. econstructor; eauto. cbn in *.
        destruct t0 as (? & ?). eexists.
        cbn. eapply typing_subst_instance in t0; eauto. apply snd in t0. cbn in t0.
        eapply t0; eauto.
      - cbn. econstructor; eauto. cbn in *.
        destruct t0 as (? & ?). eexists.
        cbn. eapply typing_subst_instance in t0; eauto. apply snd in t0.
        eapply t0; eauto.
        cbn in *. eapply typing_subst_instance in t1; eauto.
        apply snd in t1. eapply t1. all:eauto.
    }

    cbn. econstructor; eauto.
    eapply All2_map_left.
    eapply All2_impl. eapply All2_All_mix_left. eapply X1.
    exact X4.
    intros; cbn in *. destruct X5. destruct p0. destruct p0.
    destruct p. repeat split; eauto.
    eapply e2 in e1.
    rewrite subst_instance_app in e1. subst types. 2:eauto.
    eapply erases_ctx_ext. eassumption. unfold app_context.
    f_equal.
    eapply fix_context_subst_instance. all: eauto.

  - assert (Hw :  wf_local (Σ.1, univs) (subst_instance u (Γ ,,, types))).
  { (* rewrite subst_instance_app. *)
    assert(All (fun d => isType Σ Γ (dtype d)) mfix).
    eapply (All_impl X0); pcuicfo.
    destruct X5 as [s [Hs ?]]; now exists s.
    eapply All_mfix_wf in X5; auto. subst types.
    
    revert X5. clear - wfΣ wfΓ H2 H3 X2 X3.
    induction 1.
    - eauto.
    - cbn. econstructor; eauto. cbn in *.
      destruct t0 as (? & ?). eexists.
      cbn. eapply typing_subst_instance in t0; eauto. apply snd in t0. cbn in t0.
      eapply t0; eauto.
    - cbn. econstructor; eauto. cbn in *.
      destruct t0 as (? & ?). eexists.
      cbn. eapply typing_subst_instance in t0; eauto. apply snd in t0.
      eapply t0; eauto.
      cbn in *. eapply typing_subst_instance in t1; eauto.
      apply snd in t1. eapply t1. all:eauto.
  }

  cbn. econstructor; eauto.
  eapply All2_map_left.
  eapply All2_impl. eapply All2_All_mix_left. eapply X1.
  exact X4.
  intros; cbn in *. destruct X5. destruct p0. destruct p0.
  destruct p. repeat split; eauto.
  eapply e2 in e1.
  rewrite subst_instance_app in e1; eauto. subst types. 2:eauto.
  eapply erases_ctx_ext. eassumption. unfold app_context.
  f_equal.
  eapply fix_context_subst_instance. all: eauto.
Qed.

Lemma erases_subst_instance :
  forall Σ : global_env_ext, wf_ext_wk Σ ->
  forall Γ, wf_local Σ Γ ->
  forall t T, Σ ;;; Γ |- t : T ->
    forall t' u univs,
  wf_local (Σ.1, univs) (subst_instance u Γ) ->
sub_context_set (monomorphic_udecl Σ.2) (global_ext_context_set (Σ.1, univs)) ->      consistent_instance_ext (Σ.1,univs) (Σ.2) u ->
    Σ ;;; Γ |- t ⇝ℇ t' ->
    (Σ.1,univs) ;;; (subst_instance u Γ) |- subst_instance u t ⇝ℇ t'.
Proof.
  intros Σ X Γ X0 t T X1 t' u univs X2 H H0 H1.
  unshelve eapply (erases_subst_instance0 Σ _ Γ _ _ _); tea; eauto.
Qed.

Lemma erases_subst_instance'' Σ φ Γ t T u univs t' :
  wf_ext_wk (Σ, univs) ->
  (Σ, univs) ;;; Γ |- t : T ->
  sub_context_set (monomorphic_udecl univs) (global_context_set Σ) ->
  consistent_instance_ext (Σ, φ) univs u ->
  (Σ, univs) ;;; Γ |- t ⇝ℇ t' ->
  (Σ, φ) ;;; subst_instance u Γ
            |- subst_instance u t ⇝ℇ  t'.
Proof.
  intros X X0 X1. intros.
  eapply (erases_subst_instance (Σ, univs)); tas.
  eapply typing_wf_local; eassumption. eauto.
  eapply typing_wf_local.
  eapply typing_subst_instance''; eauto.
  etransitivity; tea. apply global_context_set_sub_ext.
Qed.

Lemma erases_subst_instance_decl Σ Γ t T c decl u t' :
  wf Σ.1 ->
  lookup_env Σ.1 c = Some decl ->
  (Σ.1, universes_decl_of_decl decl) ;;; Γ |- t : T ->
  consistent_instance_ext Σ (universes_decl_of_decl decl) u ->
  (Σ.1, universes_decl_of_decl decl) ;;; Γ |- t ⇝ℇ t' ->
   Σ ;;; subst_instance u Γ
            |- subst_instance u t ⇝ℇ  t'.
Proof.
  destruct Σ as [Σ φ]. intros X X0 X1 X2.
  eapply erases_subst_instance''; tea. split; tas.
  eapply weaken_lookup_on_global_env'; tea.
  eapply weaken_lookup_on_global_env''; tea.
Qed.

(** ** Erasure and applications  *)

Lemma erases_App (Σ : global_env_ext) Γ f L T t :
  Σ ;;; Γ |- tApp f L : T ->
  erases Σ Γ (tApp f L) t ->
  (t = EAst.tBox × squash (isErasable Σ Γ (tApp f L)))
  \/ exists f' L', t = EAst.tApp f' L' /\
             erases Σ Γ f f' /\
             erases Σ Γ L L'.
Proof.
  intros. generalize_eqs H.
  revert f L X.
  inversion H; intros; try congruence; subst.
  - invs H4. right. repeat eexists; eauto.
  - left. split; eauto. now sq.
Qed.

Lemma erases_mkApps (Σ : global_env_ext) Γ f f' L L' :
  erases Σ Γ f f' ->
  Forall2 (erases Σ Γ) L L' ->
  erases Σ Γ (mkApps f L) (EAst.mkApps f' L').
Proof.
  intros. revert f f' H; induction H0; cbn; intros; eauto.
  eapply IHForall2. econstructor. eauto. eauto.
Qed.

Lemma erases_mkApps_inv (Σ : global_env_ext) Γ f L T t :
  wf Σ ->
  Σ ;;; Γ |- mkApps f L : T ->
  Σ;;; Γ |- mkApps f L ⇝ℇ t ->
  (exists L1 L2 L2', L = L1 ++ L2 /\
                squash (isErasable Σ Γ (mkApps f L1)) /\
                erases Σ Γ (mkApps f L1) EAst.tBox /\
                Forall2 (erases Σ Γ) L2 L2' /\
                t = EAst.mkApps EAst.tBox L2'
  )
  \/ exists f' L', t = EAst.mkApps f' L' /\
             erases Σ Γ f f' /\
             Forall2 (erases Σ Γ) L L'.
Proof.
  intros wfΣ. intros. revert f X H ; induction L; cbn in *; intros.
  - right. exists t, []. cbn. repeat split; eauto.
  - eapply IHL in H; eauto.
    destruct H as [ (? & ? & ? & ? & [] & ? & ? & ?) | (? & ? & ? & ? & ?)].
    + subst. left. exists (a :: x), x0, x1. repeat split; eauto.
    + subst. eapply PCUICValidity.inversion_mkApps in X as (? & ? & ?); eauto.
      eapply erases_App in H0 as [ (-> & []) | (? & ? & ? & ? & ?)].
      * left. exists [a], L, x0. cbn. repeat split. eauto.
        econstructor; eauto.  eauto.
      * subst. right. exists x2, (x3 :: x0). repeat split.
        eauto. econstructor. eauto. eauto.
      * eauto.
Qed.

(** ** The correctness proof  *)

#[export] Hint Constructors PCUICWcbvEval.eval erases : core.

Definition EisConstruct_app :=
  fun t => match (EAstUtils.decompose_app t).1 with
        | E.tConstruct _ _ => true
        | _ => false
        end.

Lemma fst_decompose_app_rec t l : fst (EAstUtils.decompose_app_rec t l) = fst (EAstUtils.decompose_app t).
Proof.
  induction t in l |- *; simpl; auto. rewrite IHt1.
  unfold decompose_app. simpl. now rewrite (IHt1 [t2]).
Qed.

Lemma is_construct_erases Σ Γ t t' :
  Σ;;; Γ |- t ⇝ℇ t' ->
  negb (isConstruct_app t) -> negb (EisConstruct_app t').
Proof.
  induction 1; cbn; try congruence.
  - unfold isConstruct_app in *. clear IHerases2.
    cbn. rewrite PCUICAstUtils.fst_decompose_app_rec.
    unfold EisConstruct_app in *.
    cbn. rewrite fst_decompose_app_rec. eassumption.
Qed.

Lemma is_FixApp_erases Σ Γ t t' :
  Σ;;; Γ |- t ⇝ℇ t' ->
  negb (isFixApp t) -> negb (Ee.isFixApp t').
Proof.
  induction 1; cbn; try congruence.
  - unfold isFixApp in *. clear IHerases2.
    cbn. rewrite PCUICAstUtils.fst_decompose_app_rec.
    unfold Ee.isFixApp in *.
    cbn. rewrite fst_decompose_app_rec. eassumption.
Qed.

Lemma type_closed_subst {Σ t T} u : wf_ext Σ ->
  Σ ;;; [] |- t : T ->
  subst1 t 0 u = PCUICCSubst.csubst t 0 u.
Proof.
  intros wfΣ tc.
  apply PCUICClosed.subject_closed in tc; auto.
  rewrite PCUICCSubst.closed_subst; auto.
Qed.

Lemma erases_closed Σ Γ  a e : PCUICAst.closedn #|Γ| a -> Σ ;;; Γ |- a ⇝ℇ e -> ELiftSubst.closedn #|Γ| e.
Proof.
  remember #|Γ| as Γl eqn:Heq.
  intros cla era.
  revert Γ e era Heq.
  pattern Γl, a.
  match goal with 
  |- ?P Γl a => simpl; eapply (PCUICClosed.term_closedn_list_ind P); auto; clear
  end; simpl; intros; subst k;
    match goal with [H:erases _ _ _ _ |- _] => depelim H end; trivial;
    simpl; try solve [solve_all].
  - now apply Nat.ltb_lt.
  - apply andb_and. split; eauto.
    eapply All_forallb. unfold tCaseBrsProp_k in X0.
    eapply All2_All_mix_left in X1; eauto.
    close_Forall. intros [] []. cbn in *. intros.
    solve_all. subst. eapply b0. eauto. 
    rewrite app_context_length. cbn.
    now rewrite inst_case_branch_context_length.
  - epose proof (All2_length X0).
    solve_all. destruct y ;  simpl in *; subst.
    unfold EAst.test_def; simpl; eauto.
    rewrite <-H. rewrite fix_context_length in b0.
    eapply b0. eauto. now rewrite app_length fix_context_length.
  - epose proof (All2_length X0).
    solve_all. destruct y ;  simpl in *; subst.
    unfold EAst.test_def; simpl; eauto.
    rewrite <-H. rewrite fix_context_length in b0.
    eapply b0. eauto. now rewrite app_length fix_context_length.
Qed.

Lemma eval_to_mkApps_tBox_inv {wfl:WcbvFlags} Σ t argsv :
  Σ ⊢ t ▷ E.mkApps E.tBox argsv ->
  argsv = [].
Proof.
  intros ev.
  apply Ee.eval_to_value in ev.
  now apply value_app_inv in ev.
Qed.

Lemma Is_proof_ty Σ Γ t : 
  wf_ext Σ ->
  Is_proof Σ Γ t -> 
  forall t' ty, 
  Σ ;;; Γ |- t : ty ->
  Σ ;;; Γ |- t' : ty -> 
  Is_proof Σ Γ t'.
Proof.
  intros wfΣ [ty [u [Hty isp]]].
  intros t' ty' Hty'.
  epose proof (PCUICPrincipality.common_typing _ wfΣ Hty Hty') as [C [Cty [Cty' Ht'']]].
  intros Ht'.
  exists ty', u; intuition auto.
  eapply PCUICValidity.validity in Hty; eauto.
  eapply PCUICValidity.validity in Hty'; eauto.
  eapply PCUICValidity.validity in Ht''; eauto.
  eapply cumul_prop1' in Cty; eauto.
  eapply cumul_propositional in Cty'; eauto.
Qed.

Lemma Is_proof_app {Σ Γ t args ty} {wfΣ : wf_ext Σ} :
  Is_proof Σ Γ t -> 
  Σ ;;; Γ |- mkApps t args : ty ->
  Is_proof Σ Γ (mkApps t args).
Proof.
  intros [ty' [u [Hty [isp pu]]]] Htargs.
  eapply PCUICValidity.inversion_mkApps in Htargs as [A [Ht sp]].
  pose proof (PCUICValidity.validity Hty).  
  pose proof (PCUICValidity.validity Ht).  
  epose proof (PCUICPrincipality.common_typing _ wfΣ Hty Ht) as [C [Cty [Cty' Ht'']]].
  eapply PCUICSpine.typing_spine_strengthen in sp. 3:tea.
  edestruct (sort_typing_spine _ _ _ u _ _ _ pu sp) as [u' [Hty' isp']].
  eapply cumul_prop1'. 5:tea. all:eauto.
  eapply validity; eauto.
  exists ty, u'; split; auto.
  eapply PCUICSpine.type_mkApps; tea; eauto.
  now eapply validity.
Qed.


Lemma unfold_cofix_type Σ mfix idx args narg fn ty :
  wf Σ.1 ->
  Σ ;;; [] |- mkApps (tCoFix mfix idx) args : ty ->
  unfold_cofix mfix idx = Some (narg, fn) ->
  Σ ;;; [] |- mkApps fn args : ty.
Proof.
  intros wfΣ ht.
  pose proof (typing_wf_local ht).
  eapply PCUICValidity.inversion_mkApps in ht as (? & ? & ?); eauto.
  eapply inversion_CoFix in t; auto.
  destruct_sigma t.
  rewrite /unfold_cofix e => [=] harg hfn.
  subst fn.
  eapply PCUICSpine.typing_spine_strengthen in t0; eauto.
  eapply PCUICSpine.type_mkApps; eauto.
  pose proof a0 as a0'.
  eapply nth_error_all in a0'; eauto. simpl in a0'.
  eapply (substitution (Δ := [])) in a0'; eauto.
  2:{ eapply subslet_cofix_subst; pcuic. constructor; eauto. }
  rewrite PCUICLiftSubst.simpl_subst_k in a0'. now autorewrite with len.
  eapply a0'. now eapply nth_error_all in a; tea.
Qed.

Transparent PCUICParallelReductionConfluence.construct_cofix_discr.

Lemma isErasable_Propositional {Σ : global_env_ext} {Γ ind n u args} : 
  wf_ext Σ ->
  isErasable Σ Γ (mkApps (tConstruct ind n u) args) -> isPropositional Σ ind true.
Proof.
  intros wfΣ ise.
  eapply tConstruct_no_Type in ise; eauto.
  destruct ise as [T [s [HT [Ts isp]]]].
  unfold isPropositional.
  eapply PCUICValidity.inversion_mkApps in HT as (? & ? & ?); auto.
  eapply inversion_Construct in t as (? & ? & ? & ? & ? & ? & ?); auto.
  pose proof d as [decli ?]. pose proof decli as [-> ->].
  destruct (on_declared_constructor d).
  destruct p as [onind oib].
  rewrite oib.(ind_arity_eq).
  rewrite !destArity_it_mkProd_or_LetIn /=.
  eapply PCUICSpine.typing_spine_strengthen in t0; eauto.
  unfold type_of_constructor in t0.
  destruct s0 as [indctors [nthcs onc]].
  rewrite onc.(cstr_eq) in t0.
  rewrite !subst_instance_it_mkProd_or_LetIn !PCUICLiftSubst.subst_it_mkProd_or_LetIn in t0.
  len in t0.
  rewrite subst_cstr_concl_head in t0. 
  destruct decli. eapply nth_error_Some_length in H1; eauto.
  rewrite -it_mkProd_or_LetIn_app in t0.
  eapply PCUICElimination.typing_spine_proofs in Ts; eauto.
  destruct Ts as [_ Hs].
  specialize (Hs _ _ d c) as [Hs _].
  specialize (Hs isp). subst s. move: isp.
  now destruct (ind_sort x1).
  eapply validity. econstructor; tea.
Qed.

Lemma nisErasable_Propositional {Σ : global_env_ext} {Γ ind n u} : 
  wf_ext Σ ->
  welltyped Σ Γ (tConstruct ind n u) ->
  (isErasable Σ Γ (tConstruct ind n u) -> False) -> isPropositional Σ ind false.
Proof.
  intros wfΣ wt ise.
  destruct wt as [T HT].
  epose proof HT as HT'.
  eapply inversion_Construct in HT' as (? & ? & ? & ? & ? & ? & ?); auto.
  pose proof (declared_constructor_valid_ty _ _ _ _ _ _ _ _ wfΣ a d c).
  pose proof d as [decli ?].
  destruct (on_declared_constructor d).
  destruct p as [onind oib].
  red.
  rewrite (proj1 (proj1 d)) (proj2 (proj1 d)).
  rewrite oib.(ind_arity_eq).
  rewrite !destArity_it_mkProd_or_LetIn /=.
  destruct (is_propositional (ind_sort x0)) eqn:isp; auto.
  elimtype False; eapply ise.
  red. eexists; intuition eauto. right.
  unfold type_of_constructor in e, X.
  destruct s as [indctors [nthcs onc]].
  rewrite onc.(cstr_eq) in e, X.
  rewrite !subst_instance_it_mkProd_or_LetIn !PCUICLiftSubst.subst_it_mkProd_or_LetIn in e, X.
  len in e; len in X.
  rewrite subst_cstr_concl_head in e, X. 
  destruct decli. eapply nth_error_Some_length in H1; eauto.
  rewrite -it_mkProd_or_LetIn_app in e, X.
  exists (subst_instance_univ u (ind_sort x0)).
  rewrite is_propositional_subst_instance => //.
  split; auto.
  eapply cumul_propositional; eauto.
  rewrite is_propositional_subst_instance => //.
  eapply PCUICValidity.validity; eauto.
  destruct X as [cty ty].
  eapply type_Cumul'; eauto.
  eapply isType_Sort; pcuic.
  destruct (ind_sort x0) => //.
  eapply PCUICSpine.inversion_it_mkProd_or_LetIn in ty; eauto.
  epose proof (typing_spine_proofs _ _ [] _ _ _ [] _ _ eq_refl wfΣ ty).
  forward H0 by constructor. eexists; eauto.
  simpl. now exists cty. eapply PCUICConversion.equality_eq_le_gen, PCUICSR.wt_equality_refl; eauto.
  destruct H0 as [_ sorts].
  specialize (sorts _ _ decli c) as [sorts sorts'].
  forward sorts' by constructor.
  do 2 constructor.
  rewrite is_propositional_subst_instance in sorts, sorts' |- *.
  specialize (sorts' isp). rewrite -sorts'. reflexivity.
Qed.  

Lemma isPropositional_propositional Σ Σ' ind mdecl idecl mdecl' idecl' : 
  PCUICAst.declared_inductive Σ ind mdecl idecl ->
  ETyping.declared_inductive Σ' ind mdecl' idecl' ->
  erases_one_inductive_body idecl idecl' ->
  forall b, isPropositional Σ ind b -> is_propositional_ind Σ' ind = Some b.
Proof.
  intros [] [] [].
  intros b. unfold isPropositional, is_propositional_ind.
  rewrite H H1 H0 H2. destruct destArity eqn:da => //.
  destruct p as [ctx s].
  destruct H4 as [_ [_ [_ isP]]].
  red in isP. rewrite da in isP.
  rewrite isP. congruence.
Qed.

Lemma is_assumption_context_spec Γ :
is_true (is_assumption_context Γ) <-> PCUICLiftSubst.assumption_context Γ.
Proof.
 induction Γ; cbn.
 - split; econstructor.
 - split; intros H.
   + destruct a; cbn in *. destruct decl_body; inversion H. now econstructor.
   + invs H. cbn. now eapply IHΓ.
Qed.

Lemma expand_lets_erasure Σ mdecl idecl cdecl ind c brs p :
          wf Σ ->
          is_assumption_context (cstr_args cdecl) ->
          declared_constructor Σ (ind, c) mdecl idecl cdecl ->
          wf_branches idecl brs ->
          wf_predicate mdecl idecl p ->
          All (fun br => expand_lets (inst_case_branch_context p br) (bbody br) = bbody br) brs.
Admitted.


Lemma All2_rev (A B : Type) (P : A -> B -> Type) l l' :
All2 P l l' ->
All2 P (List.rev l) (List.rev l').
Proof.
induction 1. constructor.
simpl. eapply All2_app; auto.
Qed.
        
Lemma erases_subst0 (Σ : global_env_ext) Γ t s t' s' T :
wf Σ ->wf_local Σ Γ ->
Σ ;;; Γ |- t : T ->
Σ ;;; Γ |- t ⇝ℇ t' ->
subslet Σ [] s Γ ->
All2 (erases Σ []) s s' ->
Σ ;;; [] |- (subst s 0 t) ⇝ℇ ELiftSubst.subst s' 0 t'.
Proof.
  intros Hwf Hwfl Hty He Hall.
  change (@nil (BasicAst.context_decl term)) with (subst_context s 0 [] ++ nil).
  eapply erases_subst with (Γ' := Γ); eauto. 
  - cbn. unfold app_context. rewrite app_nil_r. eassumption.
  - cbn. unfold app_context. rewrite app_nil_r. eassumption.
Qed.

Lemma All_All2_flex {A B} (P : A -> Type) (Q : A -> B -> Type) l l' :
All P l ->
(forall x y, In y l' -> P x -> Q x y) ->
length l' = length l ->
All2 Q l l'.
Proof.
  intros H1 H2 Hl.
  induction H1 in l', H2, Hl |- *; destruct l'; invs Hl.
  - econstructor.
  - econstructor; firstorder. eapply IHAll; firstorder. 
Qed.

Lemma erases_correct (wfl := default_wcbv_flags) Σ t T t' v Σ' :
  wf_ext Σ ->
  Σ;;; [] |- t : T ->
  Σ;;; [] |- t ⇝ℇ t' ->  
  erases_deps Σ Σ' t' ->
  Σ |-p t ▷ v ->
  exists v', Σ;;; [] |- v ⇝ℇ v' /\ ∥ Σ' ⊢ t' ▷ v' ∥.
Proof.
  intros wfΣ Hty He Hed H.
  revert T Hty t' He Hed.
  induction H; intros T Hty t' He Hed.
  - assert (Hty' := Hty).
    assert (eval Σ (PCUICAst.tApp f a) res) by eauto.
    eapply inversion_App in Hty as (? & ? & ? & ? & ? & ?).
    invs He.

    + depelim Hed.
      eapply IHeval1 in H4 as (vf' & Hvf' & [He_vf']); eauto.
      eapply IHeval2 in H6 as (vu' & Hvu' & [He_vu']); eauto.
      pose proof (subject_reduction_eval t0 H).
      eapply inversion_Lambda in X0 as (? & ? & ? & ? & ?).
      assert (Σ ;;; [] |- a' : t). {
          eapply subject_reduction_eval; eauto.
          eapply PCUICConversion.equality_Prod_Prod_inv in e0 as [? ? ?].
          econstructor. eassumption. eauto. symmetry in e1.
          eapply equality_forget in e1. 
          now eapply conv_cumul. }
      assert (eqs := type_closed_subst b wfΣ X0).
      invs Hvf'.
      * assert (Σ;;; [] |- PCUICAst.subst1 a' 0 b ⇝ℇ ELiftSubst.subst1 vu' 0 t').
        eapply (erases_subst Σ [] [vass na t] [] b [a'] t'); eauto.
        econstructor. econstructor. rewrite PCUICLiftSubst.subst_empty. eassumption.
        rewrite eqs in H2.
        eapply IHeval3 in H2 as (v' & Hv' & [He_v']).
        -- exists v'. split; eauto.
           constructor.
           econstructor; eauto.
           rewrite ECSubst.closed_subst; auto.
           eapply erases_closed in Hvu'; auto.
           now eapply PCUICClosed.subject_closed in X0.
        -- rewrite <-eqs. eapply substitution0; eauto.
        -- eapply erases_deps_subst1; [now eauto|].
           eapply erases_deps_eval in He_vf'; [|now eauto].
           depelim He_vf'.
           assumption.
      * exists EAst.tBox. split.
        eapply Is_type_lambda in X1; eauto. destruct X1. econstructor.
        eapply (is_type_subst Σ [] [vass na _] [] _ [a']) in X1 ; auto.
        cbn in X1.
        eapply Is_type_eval; try assumption.
        eauto. eapply H1. rewrite <-eqs. eassumption.
        all: eauto. econstructor. econstructor. rewrite PCUICLiftSubst.subst_empty.
        eauto. constructor. econstructor. eauto. eauto.
      * auto.
    + exists EAst.tBox. split. 2:constructor; econstructor; eauto.
      econstructor.
      eapply Is_type_eval; eauto.
    + auto.
  - assert (Hty' := Hty).
    assert (Σ |-p tLetIn na b0 t b1 ▷ res) by eauto.
    eapply inversion_LetIn in Hty' as (? & ? & ? & ? & ? & ?); auto.
    invs He.     
    + depelim Hed.
      eapply IHeval1 in H6 as (vt1' & Hvt2' & [He_vt1']); eauto.
      assert (Hc : conv_context Σ ([],, vdef na b0 t) [vdef na b0' t]). {
        econstructor. econstructor. econstructor. reflexivity.
        eapply PCUICCumulativity.red_conv.
        now eapply wcbeval_red; eauto.
        reflexivity.
      }
      assert (Σ;;; [vdef na b0' t] |- b1 : x0). {
        cbn in *. eapply PCUICContextConversion.context_conversion. 3:eauto. all:cbn; eauto.
        econstructor. all: cbn; eauto. eapply subject_reduction_eval; auto. eauto. eauto.
      }
      assert (Σ;;; [] |- subst1 b0' 0 b1 ⇝ℇ ELiftSubst.subst1 vt1' 0 t2'). {
        eapply (erases_subst Σ [] [vdef na b0' t] [] b1 [b0'] t2'); eauto.
        enough (subslet Σ [] [subst [] 0 b0'] [vdef na b0' t]).
        now rewrite PCUICLiftSubst.subst_empty in X1.
        econstructor. econstructor.
        rewrite !PCUICLiftSubst.subst_empty.
        eapply subject_reduction_eval; eauto.
        eapply erases_context_conversion. 3:eassumption.
        all: cbn; eauto.
        econstructor. all: cbn; eauto.
        eapply subject_reduction_eval; eauto.
      }
      pose proof (subject_reduction_eval t1 H).
      assert (eqs := type_closed_subst b1 _ X1).
      rewrite eqs in H1.
      eapply IHeval2 in H1 as (vres & Hvres & [Hty_vres]); [| |now eauto].
      2:{ rewrite <-eqs. eapply substitution_let; eauto. }
      exists vres. split. eauto. constructor; econstructor; eauto.
      enough (ECSubst.csubst vt1' 0 t2' = ELiftSubst.subst10 vt1' t2') as ->; auto.
      eapply ECSubst.closed_subst. eapply erases_closed in Hvt2'; auto.
      eapply eval_closed. eauto. 2:eauto. now eapply PCUICClosed.subject_closed in t1.
    + exists EAst.tBox. split. 2:constructor; econstructor; eauto.
      econstructor. eapply Is_type_eval; eauto.

  - assert (Σ |-p tConst c u ▷ res) by eauto.
    eapply inversion_Const in Hty as (? & ? & ? & ? & ?); [|easy].
    invs He.
    + depelim Hed.
      assert (isdecl' := isdecl).
      eapply declared_constant_inj in H0; [|now eauto]; subst.
      unfold erases_constant_body in *. rewrite -> e in *.
      destruct ?; try tauto. cbn in *.
      eapply declared_constant_inj in d; [|now eauto]; subst.
      edestruct IHeval as (? & ? & [?]).
      * cbn in *.
        assert (isdecl'' := isdecl').
        eapply PCUICWeakeningEnv.declared_constant_inv in isdecl'; [| |now eauto|now apply wfΣ].
        2:eapply PCUICWeakeningEnv.weaken_env_prop_typing.
        unfold on_constant_decl in isdecl'. rewrite e in isdecl'. red in isdecl'.
        unfold declared_constant in isdecl''.
        now eapply typing_subst_instance_decl with (Σ0 := Σ) (Γ := []); eauto.
      * assert (isdecl'' := isdecl').
        eapply PCUICWeakeningEnv.declared_constant_inv in isdecl'; [| |now eauto|now apply wfΣ].
        unfold on_constant_decl in isdecl'. rewrite e in isdecl'. cbn in *.
        2:eapply PCUICWeakeningEnv.weaken_env_prop_typing.
        now eapply erases_subst_instance_decl with (Σ := Σ) (Γ := []); eauto.
      * now eauto.
      * exists x0. split; eauto. constructor; econstructor; eauto.
    + exists EAst.tBox. split. econstructor.
      eapply Is_type_eval. 3: eassumption. eauto. eauto. eauto. constructor. econstructor. eauto.

  - assert (Hty' := Hty).
  assert (Σ |-p tCase ci p discr brs ▷ res) by eauto.
  (* assert (Σ |-p tCase ci p discr brs ▷ res) by eauto.
 *)
  eapply inversion_Case in Hty' as (mdecl' & idecl' & di & indices & [] & c0); auto.

  rename ci into ind.
  pose proof d as d'. eapply declared_constructor_inductive in d'.
  edestruct (declared_inductive_inj d' di); subst. clear d'.
  
  assert (Σ ;;; [] |- mkApps (tConstruct ind c u) args :   mkApps (tInd ind (puinst p)) (pparams p ++ indices)).
  eapply subject_reduction_eval; eauto.
  eapply PCUICValidity.inversion_mkApps in X0 as (? & t1 & t2); eauto.
  eapply inversion_Construct in t1 as (mdecl' & idecl' & cdecl' & ? & ? & ? & ?); auto.
  assert (d1 := d0).
  destruct d0.
  edestruct (declared_inductive_inj H1 d). subst.
  pose proof (I). (* (@length_of_btys ind mdecl' idecl' (firstn pars args') u' p). *)
  pose proof (I). (* length_map_option_out _ _ ht0) as lenbtys. simpl in lenbtys. *)
  (* rewrite H3 in lenbtys.
 *)
  invs He.
  + depelim Hed.
    rename H1 into decli. rename H2 into decli'. rename H3 into er.
    pose proof (declared_inductive_inj decli H5) as [-> ->].
    eapply IHeval1 in H11 as (v' & Hv' & [He_v']); [|now eauto|now eauto].
    pose proof e as Hnth.
    eapply erases_mkApps_inv in Hv' as [(? & ? & ? & ? & [] & ? & ? & ?) | (? & ? & ? & ? & ?)]; eauto.
    3: eapply subject_reduction_eval; eauto.
    * subst.

      eapply Is_type_app in X1; auto. destruct X1.
      2:{ rewrite mkApps_nested. eapply subject_reduction_eval; eauto. }
      rewrite mkApps_nested in X1.

      eapply tConstruct_no_Type in X1; auto.
      
      eapply H10 in X1 as []; eauto. 2: exists []; now destruct Σ.

      destruct (ind_ctors idecl). cbn in *. destruct c; invs H6.
      destruct l; cbn in *; try lia. destruct c as [ | []]; cbn in *; invs H6.

      clear H8. rename H9 into H8.

      (* destruct btys as [ | ? []]; cbn in *; try lia. clear lenbtys H1.
       *)destruct H8.
      invs brs_ty. invs X0.
      invs X3. invs X4. destruct H11. destruct y, y0; cbn in *; subst.
      destruct X2 as (? & ? & ? & ?).
      
      edestruct IHeval2 as (? & ? & [?]).
      eapply subject_reduction. eauto. exact Hty.
      etransitivity.
      eapply PCUICReduction.red_case_c. eapply wcbeval_red; eauto.
      econstructor. econstructor.
      eauto. eauto.

      all:unfold iota_red in *. all:cbn in *.
      {
        assert (expand_lets (inst_case_branch_context p br) (br.(PCUICAst.bbody)) = br.(PCUICAst.bbody)) as ->. {
          unshelve edestruct @on_declared_constructor as (? & ? & ? & []). 8: exact d. all: eauto.
          pattern br.
          eapply All_nth_error. 
          eapply expand_lets_erasure; eauto.
          2: instantiate (1 := 0); cbn; eassumption.
          exact on_lets_in_type || todo "recompile".
        }
      invs e.
      eapply erases_subst0; eauto. rewrite case_branch_type_fst PCUICCasesContexts.inst_case_branch_context_eq; eauto.
      1:{ unfold app_context. cbn. rewrite app_nil_r. todo "subslet". }
      rewrite eq_npars in X1.
      revert X1.
      assert (ci_npar ind = length x0) as -> by todo "matthieu?".
      intros X1.
      (* eapply All2_rev. cbn.
      eapply Forall2_All2 in H3. eapply All2_impl. exact H3. intros. eauto. *)
        
      eapply All2_rev. (*  rewrite <- eq_npars. *)
      eapply All_All2_flex. exact X1.
      intros ? ? ? % repeat_spec. subst. intros. econstructor. now eapply isErasable_Proof.
      rewrite repeat_length. reflexivity.
       }
      

      2:{      
      exists x3. split; eauto. constructor. eapply eval_iota_sing => //. 3:eauto.
      pose proof (Ee.eval_to_value _ _ _ He_v').
      eapply value_app_inv in X0. subst. eassumption.
      depelim H2.
      eapply isErasable_Propositional in X0; eauto.
      eapply isPropositional_propositional; eauto.
      invs e. cbn in *.
      rewrite skipn_all_app in H8.

      todo "erases_substl".
      }

      depelim H4.
      cbn in H1.
      eapply erases_deps_subst. 2: eauto.
      eapply All_rev. eapply Forall_All.
      eapply All_Forall, All_repeat. econstructor.
    * subst. unfold iota_red in *.
      
      destruct (All2_nth_error_Some _ _ X0 Hnth) as (? & ? & ? & ?).
      destruct (All2i_nth_error_r _ _ _ _ _ _ brs_ty Hnth) as (? & ? & ? & ? & ? & ?).
      cbn in *. subst.
      edestruct IHeval2 as (? & ? & [?]).
      eapply subject_reduction. eauto. exact Hty.
      etransitivity.
      eapply PCUICReduction.red_case_c. eapply wcbeval_red. eauto.
      eauto. eauto.

      etransitivity. constructor. constructor.
      eauto. eauto.
      unfold iota_red. reflexivity. 

      {
        assert (expand_lets (inst_case_branch_context p br) (br.(PCUICAst.bbody)) = br.(PCUICAst.bbody)) as ->. {
          unshelve edestruct @on_declared_constructor as (? & ? & ? & []). 8: exact d. all: eauto.
          pattern br.
          eapply All_nth_error. 2: eauto.
          eapply expand_lets_erasure; eauto.
          exact on_lets_in_type || todo "recompile".
        } 
      eapply erases_subst0; eauto.  
      all: try rewrite case_branch_type_fst PCUICCasesContexts.inst_case_branch_context_eq; eauto.


      todo "subslet".
      eapply All2_rev. eapply All2_skipn. 
      eapply Forall2_All2 in H3. eapply All2_impl. exact H3. intros. eauto.
       }
      
      eapply nth_error_forall in H4; [|now eauto].
      eapply erases_deps_subst; eauto.
      eapply erases_deps_eval in He_v'; [|now eauto].
      eapply erases_deps_mkApps_inv in He_v' as (? & ?).
      now eapply All_rev, All_skipn, Forall_All.
      
      invs H2.
      -- exists x4. split; eauto.
         constructor. econstructor. eauto. 2:eauto. 3:{ unfold ETyping.iota_red.
         todo "erases_substl". }
         now eapply isPropositional_propositional; eauto.
         rewrite -e4 List.skipn_length - (Forall2_length H3) -List.skipn_length e0.
         eapply PCUICContexts.assumption_context_length.

          eapply is_assumption_context_spec.
          pose proof (@on_declared_constructor).
          specialize X1 with (Hdecl := d) (H := config.extraction_checker_flags).
          unshelve edestruct X1 as (? & ? & ? & []); eauto.

          cbn in on_lets_in_type.
          exact on_lets_in_type || todo "recompile".
      -- eapply Is_type_app in X1 as []; auto.
         2:{ eapply subject_reduction_eval. 2:eassumption. eauto. }
         assert (ispind : is_propositional_ind Σ' ind = Some true).
         { eapply isPropositional_propositional; eauto. eapply isErasable_Propositional; eauto. }

         eapply tConstruct_no_Type in X1; auto.
         eapply H10 in X1 as []; eauto. 2: exists []; now destruct Σ.

         destruct (ind_ctors idecl). cbn in *. destruct c; invs H6.
         destruct l; cbn in *; try lia. destruct c as [ | []]; cbn in *; invs H6.

         (* destruct btys as [ | ? []]; cbn in *; try discriminate. *)
         invs e4. destruct H11. destruct brs'; invs e2.
         invs brs_ty. 
         destruct X2 as (? & ? & ? & ?). invs X3.
         invs Hnth. cbn in *. invs X0. invs X2. destruct x2.

         edestruct IHeval2 as (? & ? & [?]).
         eapply subject_reduction. eauto. exact Hty.
         etransitivity.
         eapply PCUICReduction.red_case_c. eapply wcbeval_red. eauto.
         eauto. eauto.
         etransitivity. constructor. constructor. cbn. reflexivity.
         eauto.
         unfold iota_red. reflexivity.

         {
          assert (expand_lets (inst_case_branch_context p br) (br.(PCUICAst.bbody)) = br.(PCUICAst.bbody)) as ->. {
            unshelve edestruct @on_declared_constructor as (? & ? & ? & []). 8: exact d. all: eauto.
            pattern br.
            eapply All_nth_error. 
            eapply expand_lets_erasure; eauto.
            2: instantiate (1 := 0); cbn; eassumption.
            exact on_lets_in_type || todo "recompile".
          }
        invs e.
        eapply erases_subst0; eauto. rewrite case_branch_type_fst PCUICCasesContexts.inst_case_branch_context_eq; eauto.
        todo "subslet".   


        eapply All2_rev. cbn.
        rewrite -eq_npars.
        eapply All_All2_flex.
        exact X1.
        intros ? ? -> % repeat_spec.
        intros. econstructor. eapply isErasable_Proof. eauto.
        rewrite repeat_length. reflexivity.
        }

        (* 
         eapply erases_mkApps. eauto.
         instantiate (1 := repeat EAst.tBox _).
         eapply All2_Forall2.
         eapply All2_impl.
         eapply All2_All_mix_left. eassumption.
         2:{ intros. destruct X0. assert (y = EAst.tBox). exact y0. subst. econstructor.
             now eapply isErasable_Proof. }
 
         eapply All2_right_triv. 2:now rewrite repeat_length.
         now eapply All_repeat. *)
         
         
         depelim H4.
         eapply erases_deps_subst; eauto.
         eapply All_rev, All_repeat.
         econstructor.

         exists x0. split; eauto.
         constructor. eapply eval_iota_sing => //.
         pose proof (Ee.eval_to_value _ _ _ He_v').
         apply value_app_inv in X0; subst x1.
         apply He_v'.
         
         cbn in *.

         todo "erases_substl".
(* 

         
(*          enough (#|skipn (ind_npars mdecl) args| = n) as <- by eauto.
 *)
         eapply wf_ext_wf in wfΣ.
         eapply tCase_length_branch_inv in wfΣ.
         2:{ eapply subject_reduction. eauto.
             exact Hty.
             eapply PCUICReduction.red_case_c. eapply wcbeval_red; eauto. }
         2: reflexivity.

         enough (#|skipn (ind_npars mdecl) args| = n) as <- by eauto.
         rewrite skipn_length; lia. *)
    + exists EAst.tBox. split. econstructor.
      eapply Is_type_eval; eauto. constructor. econstructor; eauto.
  - pose (Hty' := Hty).
    eapply inversion_Proj in Hty' as (? & ? & ? & [] & ? & ? & ? & ? & ?); [|easy].
    invs He.

    + depelim Hed.
      rename H1 into decli. rename H2 into decli'. rename H3 into er. rename H4 into H3.
      eapply IHeval1 in H5 as (vc' & Hvc' & [Hty_vc']); eauto.
      eapply erases_mkApps_inv in Hvc'; eauto.
      2: eapply subject_reduction_eval; eauto.
      destruct Hvc' as [ (? & ? & ? & ? & [] & ? & ? & ?) | (? & ? & ? & ? & ?)]; subst.
      * exists EAst.tBox.
        assert (isprop : is_propositional_ind Σ' i = Some true).
        { eapply isPropositional_propositional; eauto. eapply isErasable_Propositional; eauto. }
        split.
        eapply Is_type_app in X as []; eauto. 2:{ rewrite mkApps_nested. eapply subject_reduction_eval; eauto. }
        rewrite mkApps_nested in X.

        eapply tConstruct_no_Type in X; eauto. eapply H3 in X as [? []]; eauto.
        2: now exists []; destruct Σ.
        destruct d as (? & ? & ?).
        destruct (declared_inductive_inj decli H5) as [<- <-].
        
        econstructor.
        eapply Is_type_eval; eauto.
        eapply nth_error_all.
        erewrite Prelim.nth_error_skipn. reflexivity. eassumption.
        eapply All_impl. assert (pars = ind_npars x0). now rewrite H7.
        subst.
        eassumption.
        eapply isErasable_Proof. constructor. eauto.

        eapply eval_proj_prop => //.
        pose proof (Ee.eval_to_value _ _ _ Hty_vc').
        eapply value_app_inv in X0. subst. eassumption.
      * rename H3 into Hinf.
        eapply Forall2_nth_error_Some in H4 as (? & ? & ?); eauto.
        assert (Σ ;;; [] |- mkApps (tConstruct i 0 u) args : mkApps (tInd i x) x3).
        eapply subject_reduction_eval; eauto.        
        eapply inversion_mkApps in X as (? & ? & ?); eauto.
        eapply typing_spine_inv in t1 as []; eauto.
        eapply IHeval2 in H3 as (? & ? & [?]); eauto.
        invs H2.
        -- exists x9. split; eauto. constructor. econstructor. eauto.
            now eapply isPropositional_propositional; eauto.
            rewrite <- nth_default_eq. unfold nth_default. now rewrite H1.
        -- exists EAst.tBox.
            assert (isprop : is_propositional_ind Σ' i = Some true).
            { eapply isPropositional_propositional; eauto; eapply (isErasable_Propositional (args:=[])); eauto. }
            split.
            eapply Is_type_app in X as []; eauto. 2:{ eapply subject_reduction_eval; [|eauto]; eauto. }

            eapply tConstruct_no_Type in X. eapply Hinf in X as [? []]; eauto.
            2: now destruct d. 2:eauto.
            destruct d as (? & ? & ?).
            destruct (declared_inductive_inj decli H5) as [<- <-].
    
            econstructor.
            eapply Is_type_eval; eauto.
            eapply nth_error_all.
            erewrite Prelim.nth_error_skipn. reflexivity. eassumption.
            eapply All_impl. assert (pars = ind_npars x0). now rewrite H7. subst.
            eassumption.
            eapply isErasable_Proof. eauto.

            constructor. eapply eval_proj_prop => //.
            pose proof (Ee.eval_to_value _ _ _ Hty_vc').
            eapply value_app_inv in X0. subst. eassumption.
        -- eapply erases_deps_eval in Hty_vc'; [|now eauto].
            eapply erases_deps_mkApps_inv in Hty_vc' as (? & ?).
            now eapply nth_error_forall in H1; eauto.
    + exists EAst.tBox. split. econstructor.
      eapply Is_type_eval. 3: eassumption. all:eauto. constructor. econstructor. eauto.   
  - assert (Hty' := Hty).
    assert (Hunf := H).
    assert (Hcon := H0).
    eapply inversion_App in Hty' as (? & ? & ? & ? & ? & ?); eauto.
    assert (Ht := t).
    eapply subject_reduction in t. 2:auto. 2:eapply wcbeval_red; eauto.
    assert (HT := t).
    apply PCUICValidity.inversion_mkApps in HT as (? & ? & ?); auto.
    assert (Ht1 := t1).
    apply inversion_Fix in t1 as Hfix; auto.
    destruct Hfix as (? & ? & ? & ? & ? & ? & ?).
    unfold cunfold_fix in e. rewrite e1 in e. invs e.
    depelim He; first last.
    
    + exists EAst.tBox. split; [|now constructor; constructor].
      econstructor.
      eapply Is_type_eval. 3:eapply X. eauto.
      eapply eval_fix; eauto.
      rewrite /cunfold_fix e1 //. now rewrite H3.
    + depelim Hed.
      eapply IHeval1 in He1 as (er_stuck_v & er_stuck & [ev_stuck]); eauto.
      eapply IHeval2 in He2 as (er_argv & er_arg & [ev_arg]); eauto.
      eapply erases_mkApps_inv in er_stuck; eauto.
      destruct er_stuck as [(? & ? & ? & -> & ? & ? & ? & ->)|
                            (? & ? & -> & ? & ?)].
      { exists E.tBox.
        eapply eval_to_mkApps_tBox_inv in ev_stuck as ?; subst.
        cbn in *.
        split; [|constructor; eauto].
        2:{ eapply (eval_box_apps _ _ [_]); eauto. }
        destruct H2.
        eapply (Is_type_app _ _ _ (x5 ++ [av])) in X as []; eauto; first last.
        - rewrite mkApps_nested app_assoc mkApps_snoc.
          eapply PCUICValidity.type_App'; eauto.
          eapply subject_reduction; eauto.
          eapply wcbeval_red; eauto.
        - eapply erases_box.
          eapply Is_type_eval; auto. 2:eauto.
          rewrite -mkApps_nested /=.
          eapply eval_fix.
          rewrite mkApps_nested. eapply value_final.
          eapply eval_to_value; eauto.
          eapply value_final, eval_to_value; eauto.
          rewrite /cunfold_fix e1 //. auto.
          now rewrite H3. auto. }

      invs H2.
      * assert (Hmfix' := X).
        eapply All2_nth_error_Some in X as (? & ? & ?); eauto.
        pose proof (closed_fix_substl_subst_eq (PCUICClosed.subject_closed t1) e1) as cls.
        destruct x3. cbn in *. subst.

        enough (Σ;;; [] ,,, subst_context (fix_subst mfix) 0 []
                |- subst (fix_subst mfix) 0 dbody
                ⇝ℇ ELiftSubst.subst (ETyping.fix_subst mfix') 0 (Extract.E.dbody x4)).
        destruct p. destruct p.

        clear e3. rename H into e3.
        -- cbn in e3. rename x5 into L.
           eapply (erases_mkApps _ _ _ _ (argsv ++ [av])) in H2; first last.
           { eapply Forall2_app.
             - exact H4.
             - eauto. }
           rewrite <- mkApps_nested in H2.
           rewrite EAstUtils.mkApps_app in H2.
           cbn in *. simpl in H2.
          rewrite cls in H2.
          eapply IHeval3 in H2 as (? & ? & [?]); cbn; eauto; cycle 1.
           { eapply subject_reduction. eauto. exact Hty.
             etransitivity.
             eapply PCUICReduction.red_app. eapply wcbeval_red; eauto. 
             eapply wcbeval_red; eauto.
             rewrite <- !mkApps_snoc.
             eapply PCUICReduction.red1_red.
             eapply red_fix.
             rewrite closed_unfold_fix_cunfold_eq.
             now eapply PCUICClosed.subject_closed in t1.
             rewrite /cunfold_fix e1 /= //.
             pose proof (eval_to_value _ _ _ e3) as vfix.
             eapply PCUICWcbvEval.stuck_fix_value_args in vfix; eauto.
             2:{ rewrite /cunfold_fix e1 //. }
             simpl in vfix. 
             subst. unfold is_constructor.
             rewrite nth_error_snoc. lia.
             assert(Σ ;;; [] |- mkApps (tFix mfix idx) (argsv ++ [av]) : subst [av] 0 x1).
             { rewrite -mkApps_nested. eapply PCUICValidity.type_App'; eauto.
               eapply subject_reduction_eval; eauto. }
             epose proof (fix_app_is_constructor Σ (args:=argsv ++ [av]) X).
             rewrite /unfold_fix e1 in X0.
             specialize (X0 eq_refl). simpl in X0.
             rewrite nth_error_snoc in X0. auto. apply X0.
             eapply value_axiom_free, eval_to_value; eauto.
             eapply value_whnf; eauto.
             eapply eval_closed; eauto. now eapply PCUICClosed.subject_closed in t0.
             eapply eval_to_value; eauto. }
           
           { constructor.
             - eapply erases_deps_eval in ev_stuck; [|now eauto].
               eapply erases_deps_mkApps_inv in ev_stuck as (? & ?).
               apply erases_deps_mkApps; [|now eauto].
               depelim H.
               eapply nth_error_forall in H as H'; eauto.
               apply erases_deps_subst; [|now eauto].
               now apply Forall_All, Forall_erases_deps_fix_subst; eauto.
             - now eapply erases_deps_eval in ev_arg; eauto. }

           exists x3. split. eauto.
           constructor. eapply Ee.eval_fix.
           ++ eauto.
           ++ eauto.
           ++ rewrite <- Ee.closed_unfold_fix_cunfold_eq.
              { unfold ETyping.unfold_fix. rewrite e -e4.
                now rewrite (Forall2_length H4). }
              eapply eval_closed in e3; eauto.
              clear -e3 Hmfix'.
              pose proof (All2_length Hmfix').
              rewrite closedn_mkApps in e3.
              apply andb_true_iff in e3 as (e3 & _).
              change (?a = true) with (is_true a) in e3.
              simpl in e3 |- *. solve_all.
              rewrite app_context_nil_l in b.
              eapply erases_closed in b. simpl in b.
              rewrite <- H.
              unfold EAst.test_def. 
              simpl in b.
              rewrite fix_context_length in b.
              now rewrite Nat.add_0_r.
              unfold test_def in a. apply andb_and in a as [_ Hbod].
              rewrite fix_context_length.
              now rewrite Nat.add_0_r in Hbod.
              eauto with pcuic.
              now eapply PCUICClosed.subject_closed in Ht.
          ++ auto.
           
        -- cbn. destruct p. destruct p.
           eapply (erases_subst Σ [] (fix_context mfix) [] dbody (fix_subst mfix)) in e5; cbn; eauto.
           ++ eapply subslet_fix_subst. now eapply wf_ext_wf. all: eassumption.
           ++ eapply nth_error_all in a1; eauto. cbn in a1.
              eapply a1.
           ++ eapply All2_from_nth_error.
              erewrite fix_subst_length, ETyping.fix_subst_length, All2_length; eauto.
              intros.
              rewrite fix_subst_nth in H3. now rewrite fix_subst_length in H2.
              rewrite efix_subst_nth in H5. rewrite fix_subst_length in H2.
              erewrite <- All2_length; eauto.
              invs H5; invs H3.
              erewrite All2_length; eauto.
      * eapply (Is_type_app _ _ _ (argsv ++ [av])) in X as []; tas.
        -- exists EAst.tBox.
           split.
           ++ econstructor.
              eapply Is_type_eval. 3:eauto. all:eauto.
              rewrite -mkApps_nested.
              eapply eval_fix; eauto. 
              1-2:eapply value_final, eval_to_value; eauto.
              rewrite /cunfold_fix e1 //. congruence.
           ++ constructor. eapply Ee.eval_box; [|now eauto].
              apply eval_to_mkApps_tBox_inv in ev_stuck as ?; subst.
              eauto.
        -- eauto.
        -- rewrite mkApps_snoc.
           eapply PCUICValidity.type_App'; eauto.
           eapply subject_reduction; eauto.
           eapply wcbeval_red; eauto.

  - apply inversion_App in Hty as Hty'; [|eauto].
    destruct Hty' as (? & ? & ? & ? & ? & ?).

    eapply subject_reduction in t as typ_stuck_fix; [|eauto|]; first last.
    { eapply wcbeval_red. 3:eauto. all:eauto. }

    eapply erases_App in He as He'; [|eauto].
    destruct He' as [(-> & [])|(? & ? & -> & ? & ?)].
    + exists E.tBox.
      split; [|now constructor; eauto using @Ee.eval].
      constructor.
      eapply Is_type_red.
      * eauto.
      * eapply PCUICReduction.red_app.
        -- eapply wcbeval_red; [eauto| |eauto]. eauto.
        -- eapply wcbeval_red; [eauto| |eauto]. eauto.
      * eauto.
    + depelim Hed.
      eapply subject_reduction in t0 as typ_arg; [|eauto|]; first last.
      { eapply wcbeval_red; [eauto| |eauto]. eauto. }

      eapply IHeval1 in H1 as (? & ? & [?]); [|now eauto|now eauto].
      eapply IHeval2 in H2 as (? & ? & [?]); [|now eauto|now eauto].
      eapply erases_mkApps_inv in H1; [|eauto|eauto].
      destruct H1 as [(? & ? & ? & -> & [] & ? & ? & ->)|(? & ? & -> & ? & ?)].
      * apply eval_to_mkApps_tBox_inv in H3 as ?; subst.
        depelim H5.
        rewrite -> !app_nil_r in *.
        cbn in *.
        exists E.tBox.
        split; [|now constructor; eauto using @Ee.eval].
        eapply (Is_type_app _ _ _ [av]) in X as [].
        -- constructor.
           apply X.
        -- eauto.
        -- eauto.
        -- cbn.
           eapply PCUICValidity.type_App'; eauto.
      * depelim H1.
        -- exists (E.tApp (E.mkApps (E.tFix mfix' idx) x7) x5).
           split; [eauto using erases_tApp, erases_mkApps|].
           unfold cunfold_fix in *.
           destruct (nth_error _ _) eqn:nth; [|congruence].
           eapply All2_nth_error_Some in X as (? & ? & ? & ? & ?); [|eauto].
           constructor. eapply Ee.eval_fix_value.
           ++ eauto.
           ++ eauto.
           ++ unfold Ee.cunfold_fix. now rewrite e1.
           ++ eapply Forall2_length in H5. noconf e. lia.
              
        -- exists E.tBox.
           apply eval_to_mkApps_tBox_inv in H3 as ?; subst.
           split; [|now constructor; eauto using @Ee.eval].
           eapply Is_type_app in X as [].
           ++ constructor.
              rewrite <- mkApps_snoc.
              exact X.
           ++ eauto.
           ++ eauto.
           ++ rewrite mkApps_snoc.
              eapply PCUICValidity.type_App'; eauto.

  - assert (Hty' := Hty).
    eapply inversion_Case in Hty' as [mdecl [idecl [decli [args' [[] ht0]]]]]; auto.
    assert (t0' := scrut_ty).
    eapply PCUICValidity.inversion_mkApps in t0' as (? & ? & ?); eauto.
    pose proof (PCUICClosed.subject_closed t) as clfix.
    eapply inversion_CoFix in t; destruct_sigma t; auto.
    eapply PCUICSpine.typing_spine_strengthen in t0; eauto.
    2:{ now eapply nth_error_all in a; tea. }
    eapply subject_reduction in Hty. 2:auto.
    2:{ eapply PCUICReduction.red1_red. eapply PCUICReduction.red_cofix_case. eauto.
        rewrite closed_unfold_cofix_cunfold_eq; eauto. }
    specialize (IHeval _ Hty).
    invs He; [eapply erases_mkApps_inv in H6; eauto; destruct H6 as [H6|H6]; destruct_sigma H6|].
    * depelim Hed.
      rename H0 into decli'. rename H1 into decli''. rename H2 into er. rename H3 into H0.
      destruct (declared_inductive_inj decli decli') as [<- <-].
      destruct H6 as (? & ? & ? & ? & ? & ? & ? & ?). subst.
      destruct H2.
      edestruct IHeval as (? & ? & [?]).
      { constructor; eauto.
        rewrite -mkApps_nested.
        eapply erases_mkApps. instantiate(1:=EAst.tBox).
        constructor.
        eapply isErasable_Proof.
        eapply tCoFix_no_Type in X0; auto.
        pose proof X0 as X0'. destruct X0' as [tyapp [u [Htyapp Hu]]].
        eapply Is_proof_ty; eauto.
        eapply unfold_cofix_type; eauto.
        move: e. rewrite -closed_unfold_cofix_cunfold_eq // /unfold_cofix e0.
        intros e; eapply e. eauto. }
      { now econstructor; eauto. }
      exists x3; split; [|constructor]; auto.
    * depelim Hed.
      rename H0 into decli'. rename H1 into decli''. rename H2 into er. rename H3 into H0.
      destruct (declared_inductive_inj decli decli') as [<- <-].
      destruct H6 as (? & ? & ? & ? & ?).
      subst c'.
      pose proof (erases_closed _ _ _ _ clfix H2) as clfix'.
      depelim H2.
      + pose proof X as X'. eapply All2_nth_error_Some in X'; eauto.
        destruct X' as (t' & Hnth & dn & rargeq & er').
        assert (e' := e).
        move: e'. rewrite -closed_unfold_cofix_cunfold_eq // /unfold_cofix e0.
        intros [= <- Heq].
        eapply (erases_subst Σ [] (fix_context mfix) [] (dbody decl) (cofix_subst mfix) _ (ETyping.cofix_subst mfix')) in er'; cbn; eauto.
        2:{ eapply subslet_cofix_subst; eauto. constructor; eauto. }
        simpl in er'. rewrite Heq in er'.
        3:{ eapply All2_from_nth_error.
            erewrite cofix_subst_length, ETyping.cofix_subst_length, All2_length; eauto.
            intros.
            rewrite cofix_subst_nth in H2. now rewrite cofix_subst_length in H1.
            rewrite ecofix_subst_nth in H4. rewrite cofix_subst_length in H1.
            erewrite <- All2_length; eauto.
            invs H2; invs H4.
            erewrite All2_length; eauto. }
        edestruct IHeval as (? & ? & [?]).
        { constructor; eauto.
          eapply erases_mkApps; eauto. }
        { apply erases_deps_mkApps_inv in Hed as (edcofix & edargs).
          depelim edcofix.
          econstructor; eauto.
          apply erases_deps_mkApps; [|now eauto].
          apply erases_deps_subst.
          - now apply Forall_All, Forall_erases_deps_cofix_subst; eauto.
          - now eapply nth_error_forall in H0; eauto. }
        eexists; intuition eauto.
        constructor; eapply Ee.red_cofix_case; eauto.
        rewrite /Ee.cunfold_cofix Hnth //. f_equal.
        erewrite (closed_cofix_substl_subst_eq); eauto.
        eapply nth_error_all in a0; eauto. simpl in a0. eauto.
      + apply erases_deps_mkApps_inv in Hed as (_ & edargs).
        edestruct IHeval as (? & ? & [?]).
        { constructor; eauto.
          eapply erases_mkApps. instantiate(1:=EAst.tBox).
          constructor.
          eapply isErasable_Proof.
          eapply (tCoFix_no_Type _ _ _ _ []) in X; auto.
          pose proof X as X'. destruct X' as [tyapp [u [Htyapp Hu]]].
          eapply Is_proof_ty; eauto.
          eapply (unfold_cofix_type _ _ _ []); eauto.
          move: e. rewrite -closed_unfold_cofix_cunfold_eq // /unfold_cofix e0.
          intros e; eapply e. eauto. }
        { econstructor; eauto.
          apply erases_deps_mkApps; [now constructor|now eauto]. }
        exists x0; split; [|constructor]; auto.
    * exists EAst.tBox; split; auto.
      2:repeat constructor.
      constructor.
      eapply Is_type_eval; eauto.
      eapply Is_type_red. 3:eauto. auto.
      eapply PCUICReduction.red1_red.
      eapply PCUICReduction.red_cofix_case.
      move: e. rewrite -closed_unfold_cofix_cunfold_eq // /unfold_cofix e0.
      intros e; eapply e.
        
  - assert (Hty' := Hty).
    eapply inversion_Proj in Hty' as (? & ? & ? & ? & [] & ? & ? & ? & ? & ?); auto.
    set (t0' := t0).
    eapply PCUICValidity.inversion_mkApps in t0' as (? & ? & ?); eauto.
    pose proof (PCUICClosed.subject_closed t0) as clfix.
    assert(clcof : PCUICAst.closedn 0 (tCoFix mfix idx)).
    { eapply PCUICClosed.subject_closed in t1; eauto. }
    eapply inversion_CoFix in t1; destruct_sigma t1; auto.
    eapply PCUICSpine.typing_spine_strengthen in t2; eauto.
    assert(Hty' := Hty).
    eapply subject_reduction in Hty'. 2:auto.
    2:{ eapply PCUICReduction.red1_red. eapply PCUICReduction.red_cofix_proj. eauto.
        rewrite closed_unfold_cofix_cunfold_eq; eauto. }
    specialize (IHeval _ Hty').
    invs He; [eapply erases_mkApps_inv in H4; eauto; destruct_sigma H4|]; eauto.
    destruct H4.
    * depelim Hed.
      rename H0 into decli. rename H1 into decli'. rename H2 into er. rename H3 into H2.
      rename H4 into H0.
      destruct (declared_inductive_inj decli (proj1 d)) as [<- <-].

      destruct H0 as (? & ? & ? & ? & ? & ? & ? & ?). subst.
      destruct H1.
      edestruct IHeval as (? & ? & [?]).
      { constructor; eauto.
        rewrite -mkApps_nested.
        eapply erases_mkApps. instantiate(1:=EAst.tBox).
        constructor.
        eapply isErasable_Proof.
        eapply tCoFix_no_Type in X; auto.
        pose proof X as X0'. destruct X0' as [tyapp [u [Htyapp Hu]]].
        eapply Is_proof_ty; eauto.
        eapply unfold_cofix_type; eauto.
        move: e. rewrite -closed_unfold_cofix_cunfold_eq // /unfold_cofix e2.
        intros e; eapply e. eauto. }
      { apply erases_deps_mkApps_inv in Hed as (_ & edargs).
        econstructor; eauto.
        apply erases_deps_mkApps; [now constructor|now eauto]. }
      exists x8; split; [|constructor]; auto.
    * destruct H0 as (? & ? & ? & ? & ?).
      subst c'.
      pose proof (erases_closed _ [] _ _ clcof H1) as clfix'.
      depelim H1.
      + depelim Hed.
        rename H0 into decli. rename H1 into decli'. rename H2 into erd. rename H3 into H2.
        rename H4 into H3.
        destruct (declared_inductive_inj decli (proj1 d)) as [<- <-].

        apply erases_deps_mkApps_inv in Hed as (edcofix & edargs).
        depelim edcofix.
        pose proof X as X'. eapply All2_nth_error_Some in X'; eauto.
        destruct X' as (t' & Hnth & dn & rargeq & er).
        assert (e' := e).
        move: e'. rewrite -closed_unfold_cofix_cunfold_eq // /unfold_cofix e2.
        intros [= <- Heq].
        eapply (erases_subst Σ [] (fix_context mfix) [] (dbody decl) (cofix_subst mfix) _ (ETyping.cofix_subst mfix')) in er; cbn; eauto.
        2:{ eapply subslet_cofix_subst; eauto. constructor; eauto. }
        simpl in er. rewrite Heq in er.
        3:{ eapply All2_from_nth_error.
            erewrite cofix_subst_length, ETyping.cofix_subst_length, All2_length; eauto.
            intros.
            rewrite cofix_subst_nth in H4. now rewrite cofix_subst_length in H1.
            rewrite ecofix_subst_nth in H5. rewrite cofix_subst_length in H1.
            erewrite <- All2_length; eauto.
            invs H4; invs H5.
            erewrite All2_length; eauto. }
        edestruct IHeval as (? & ? & [?]).
        { constructor; eauto. eapply erases_mkApps; eauto. }
        { econstructor; eauto.
          apply erases_deps_mkApps; [|now eauto].
          apply erases_deps_subst.
          - now apply Forall_All, Forall_erases_deps_cofix_subst; eauto.
          - now eapply nth_error_forall in H0; eauto. }
        eexists; intuition eauto.
        constructor. eapply Ee.red_cofix_proj; eauto.
        rewrite /Ee.cunfold_cofix Hnth //. f_equal.
        erewrite (closed_cofix_substl_subst_eq); eauto.
        eapply nth_error_all in a0; eauto. simpl in a0. eauto.
      + depelim Hed.
        apply erases_deps_mkApps_inv in Hed as (_ & edargs).
        edestruct IHeval as (? & ? & [?]).
        { constructor; eauto.
          eapply erases_mkApps. instantiate(1:=EAst.tBox).
          constructor.
          eapply isErasable_Proof.
          eapply (tCoFix_no_Type _ _ _ _ []) in X; auto.
          pose proof X as X'. destruct X' as [tyapp [u [Htyapp Hu]]].
          eapply Is_proof_ty; eauto.
          eapply (unfold_cofix_type _ _ _ []); eauto.
          move: e. rewrite -closed_unfold_cofix_cunfold_eq // /unfold_cofix e2.
          intros e; eapply e. exact H4. }
      { econstructor; eauto.
        apply erases_deps_mkApps; [now constructor|now eauto]. }
        exists x5; split; [|constructor]; auto.
    * exists EAst.tBox; split; auto.
      2:repeat constructor.
      constructor.
      eapply Is_type_eval; eauto.
      eapply Is_type_red. 3:eauto. auto.
      eapply PCUICReduction.red1_red.
      eapply PCUICReduction.red_cofix_proj.
      move: e. rewrite -closed_unfold_cofix_cunfold_eq // /unfold_cofix e2.
      intros e; eapply e.
    * now eapply nth_error_all in a; tea.
  
  - pose (Hty' := Hty).
    eapply inversion_App in Hty' as (? & ? & ? & ? & ? & ?); eauto.
    invs He.
    + depelim Hed.
      assert (t' := t). eapply IHeval1 in t as (? & ? & [?]); eauto.
      eapply IHeval2 in t0 as (? & ? & [?]); eauto.
      destruct (EAstUtils.isBox x2) eqn:E.
      * destruct x2; invs E. exists EAst.tBox. split. 2: now constructor; econstructor; eauto.
        pose proof (Is_type_app Σ [] f'[a']).
        inversion H1.
        edestruct H7; eauto. cbn. eapply subject_reduction. eauto.
        exact Hty. eapply PCUICReduction.red_app.
        eapply wcbeval_red; eauto.
        eapply inversion_App in Hty as [na [A [B [Hf [Ha _]]]]]; eauto.
        eapply wcbeval_red; eauto.
      * exists (E.tApp x2 x3).
        split; [econstructor; eauto|].
        constructor; eapply Ee.eval_app_cong; eauto.
        eapply ssrbool.negbT.
        repeat eapply orb_false_intro.
        -- destruct x2; try reflexivity.
          invs H1. invs i.
        -- destruct x2 eqn:Ex; try reflexivity.
          ++ cbn. invs H1. cbn in *.
            eapply ssrbool.negbTE, is_FixApp_erases.
            econstructor; eauto.
            now rewrite orb_false_r in i.
          ++ cbn in *.
            invs H1. invs i.
        -- eauto.
    + exists EAst.tBox. split. 2: now constructor; econstructor.
      econstructor.
      eapply inversion_App in Hty as [na [A [B [Hf [Ha _]]]]]; auto.
      eapply Is_type_red. 3:eauto. eauto.
      eapply PCUICReduction.red_app.
      eapply PCUICClosed.subject_closed in Hf; auto.
      eapply wcbeval_red; eauto.
      eapply PCUICClosed.subject_closed in Ha; auto.
      eapply wcbeval_red; eauto.

  - destruct t; try easy.
    + invs He. eexists. split; eauto. now constructor; econstructor.
    + invs He. eexists. split; eauto. now constructor; econstructor.
    + invs He.
      * eexists. split; eauto. now constructor; econstructor.
      * eexists. split. 2: now constructor; econstructor.
        econstructor; eauto.
    + invs He.
      * eexists. split. 2: now constructor; econstructor.
        econstructor; eauto.
    + invs He.
      * eexists. split. 2: now constructor; econstructor.
        econstructor; eauto.
      * eexists. split. 2: now constructor; econstructor.
        eauto.
    + invs He.
      * eexists. split; eauto. now constructor; econstructor.
      * eexists. split. 2: now constructor; econstructor.
        econstructor; eauto.
    + invs He.
      * eexists. split; eauto. now constructor; econstructor.
      * eexists. split. 2: now constructor; econstructor.
        econstructor; eauto.
Qed.

Print Assumptions erases_correct.
