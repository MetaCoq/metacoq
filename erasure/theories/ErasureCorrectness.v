(* Distributed under the terms of the MIT license. *)
From Coq Require Import Program.
From MetaCoq.Template Require Import config utils.
From MetaCoq.Erasure Require Import ELiftSubst EGlobalEnv EWcbvEval Extract Prelim
     ESubstitution EInversion EArities EDeps.
From MetaCoq.PCUIC Require Import PCUICTyping PCUICGlobalEnv PCUICAst
  PCUICAstUtils PCUICConversion PCUICSigmaCalculus
  PCUICClosed PCUICClosedTyp
  PCUICWeakeningEnvConv PCUICWeakeningEnvTyp
  PCUICWeakeningConv PCUICWeakeningTyp PCUICSubstitution PCUICArities
  PCUICWcbvEval PCUICSR PCUICInversion
  PCUICLiftSubst
  PCUICUnivSubstitutionConv PCUICUnivSubstitutionTyp
  PCUICElimination PCUICCanonicity
  PCUICUnivSubst
  PCUICCumulativity PCUICSafeLemmata
  PCUICArities PCUICInductiveInversion
  PCUICContextConversion PCUICContextConversionTyp
  PCUICOnFreeVars PCUICWellScopedCumulativity PCUICValidity
  PCUICContexts PCUICEquality PCUICSpine
  PCUICInductives.
From MetaCoq.PCUIC Require Import PCUICTactics.

Require Import Equations.Prop.DepElim.
Require Import ssreflect.

Local Set Keyed Unification.

Local Existing Instance config.extraction_checker_flags.

(** ** Prelim on arities and proofs *)

Lemma isErasable_subst_instance (Σ : global_env_ext) Γ T univs u :
  wf_ext_wk Σ ->  wf_local Σ Γ ->
  wf_local (Σ.1, univs) (subst_instance u Γ) ->
  isErasable Σ Γ T ->
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
  exists x. split. eapply context_conversion. 3:eapply X2. all:eauto.
  destruct s as [? | [u []]].
  - left. eauto.
  - right. exists u. split; eauto. eapply context_conversion in X2; eauto.
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
    destruct t0. exists x. eapply context_conversion with (Γ ,,, Γ0); eauto.
    * eapply wf_local_app; eauto.
    * eapply conv_context_app_same; eauto.
  - econstructor; eauto.
    + cbn in *.
      destruct t0. exists x. eapply context_conversion with (Γ ,,, Γ0); eauto.
      * eapply wf_local_app; eauto.
      * eapply conv_context_app_same; eauto.
    + cbn in *. eapply context_conversion with (Γ ,,, Γ0); eauto.
      * eapply wf_local_app; eauto.
      * eapply conv_context_app_same; eauto.
Qed.

#[global]
Hint Resolve Is_type_conv_context : core.

Lemma conv_context_wf_local_app {A B A'} {Σ : global_env_ext} {wfΣ : wf Σ} :
  wf_local Σ (A ,,, B) -> wf_local Σ A' -> conv_context Σ A A' -> wf_local Σ (A' ,,, B).
Proof.
  intros wfab wfa' cv.
  eapply wf_local_app => //.
  eapply wf_local_rel_conv; tea.
  now eapply wf_local_app_inv.
Qed.

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
    eapply context_conversion. 3:eauto. all:eauto.
  - econstructor. eauto. eapply h_forall_Γ'1.
    econstructor. eauto. now constructor.
    constructor; auto. exists s1.
    eapply context_conversion with Γ; eauto.
    eapply context_conversion with Γ; eauto.
    eassumption.
  - econstructor. eauto. eauto.
    eapply (All2i_All2_All2 X7 X6).
    intros ? ? ? [] (? & ? & ? & ? & ? & ?) (? & ?).
    split. 2: assumption.
    rewrite <- (PCUICCasesContexts.inst_case_branch_context_eq a).
    eapply e.
    + rewrite case_branch_type_fst.
      eapply conv_context_app_same; eauto.
    + eapply typing_wf_local.
      eapply context_conversion.
      * exact t1.
      * eapply conv_context_wf_local_app; eauto.
      * eapply conv_context_app_same; eauto.
    + now rewrite case_branch_type_fst (PCUICCasesContexts.inst_case_branch_context_eq a).
  - econstructor.

    eapply All2_impl. eapply All2_All_mix_left. eassumption. eassumption.
    intros. cbn in *.
    destruct X5 as [[Ht IH] []].
    split; intuition auto.
    eapply IH.
    + subst types.
      eapply conv_context_app_same; auto.
    + eapply conv_context_wf_local_app; eauto.
    + assumption. 
  - econstructor.

    eapply All2_impl. eapply All2_All_mix_left. eassumption. eassumption.
    intros. cbn in *.
    decompose [prod] X2. intuition auto.
    eapply b0.
    + subst types. eapply conv_context_app_same; auto.
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

Lemma isLambda_subst_instance t u : isLambda t -> isLambda t@[u].
Proof. destruct t => //. Qed.

Lemma erases_subst_instance0
  : env_prop (fun Σ Γ t T => wf_ext_wk Σ ->
                           forall t' u univs,
                             wf_local (Σ.1, univs) (subst_instance u Γ) ->
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
    cbn in X0. destruct X0. refine (t0 _ _ _ _); eauto.
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
    cbn [subst_instance_constr]. econstructor; eauto.
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
      
      revert X5. clear - wfΣ wfΓ H2 X2 X3.
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
    intros; cbn in *. destruct X5.
    destruct p as [p IH].
    destruct a. split; auto.
    now eapply isLambda_subst_instance.
    eapply IH in e1.
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
    
    revert X5. clear - wfΣ wfΓ H2 X2 X3.
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
   consistent_instance_ext (Σ.1,univs) (Σ.2) u ->
    Σ ;;; Γ |- t ⇝ℇ t' ->
    (Σ.1,univs) ;;; (subst_instance u Γ) |- subst_instance u t ⇝ℇ t'.
Proof.
  intros Σ X Γ X0 t T X1 t' u univs H H0 H1.
  unshelve eapply (erases_subst_instance0 Σ _ Γ _ _ _); tea; eauto.
Qed.

Lemma erases_subst_instance'' Σ φ Γ t T u univs t' :
  wf_ext_wk (Σ, univs) ->
  (Σ, univs) ;;; Γ |- t : T ->
  consistent_instance_ext (Σ, φ) univs u ->
  (Σ, univs) ;;; Γ |- t ⇝ℇ t' ->
  (Σ, φ) ;;; subst_instance u Γ
            |- subst_instance u t ⇝ℇ  t'.
Proof.
  intros X X0. intros.
  eapply (erases_subst_instance (Σ, univs)); tas.
  eapply typing_wf_local; eassumption. eauto.
  eapply typing_wf_local.
  eapply typing_subst_instance''; eauto.
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
  apply subject_closed in tc; auto.
  rewrite PCUICCSubst.closed_subst; auto.
Qed.

Lemma erases_closed Σ Γ  a e : PCUICAst.closedn #|Γ| a -> Σ ;;; Γ |- a ⇝ℇ e -> ELiftSubst.closedn #|Γ| e.
Proof.
  remember #|Γ| as Γl eqn:Heq.
  intros cla era.
  revert Γ e era Heq.
  pattern Γl, a.
  match goal with 
  |- ?P Γl a => simpl; eapply (term_closedn_list_ind P); auto; clear
  end; simpl; intros; subst k;
    match goal with [H:erases _ _ _ _ |- _] => depelim H end; trivial;
    simpl; try solve [solve_all].
  - now apply Nat.ltb_lt.
  - apply andb_and. split; eauto.
    eapply All_forallb. unfold tCaseBrsProp_k in X0.
    eapply All2_All_mix_left in X1; eauto.
    close_Forall. intros [] []. cbn in *. intros.
    solve_all. subst. rewrite map_length. eapply b0. eauto. 
    rewrite app_context_length. cbn.
    now rewrite inst_case_branch_context_length.
  - epose proof (All2_length X0).
    solve_all. destruct b. destruct y ;  simpl in *; subst.
    unfold EAst.test_def; simpl; eauto.
    rewrite <-H. rewrite fix_context_length in b0.
    eapply b0. eauto. now rewrite app_length fix_context_length.
  - epose proof (All2_length X0).
    solve_all. destruct y ;  simpl in *; subst.
    unfold EAst.test_def; simpl; eauto.
    rewrite <-H. rewrite fix_context_length in b0.
    eapply b0. eauto. now rewrite app_length fix_context_length.
Qed.

Section wellscoped.
  Import PCUICAst.
  
  Definition lookup_constant Σ kn := 
    match PCUICEnvironment.lookup_env Σ kn with
    | Some (ConstantDecl d) => Some d
    | _ => None
    end.

  Section Def.
  Context (Σ : global_env).
  Import ssrbool.

  Fixpoint wellformed (t : term) : bool :=
  match t with
  | tRel i => true
  | tEvar ev args => List.forallb (wellformed) args
  | tLambda _ N M => wellformed N && wellformed M
  | tApp u v => wellformed u && wellformed v
  | tLetIn na b ty b' => wellformed b && wellformed ty && wellformed b'
  | tCase ind p c brs => 
    let brs' := forallb (wellformed ∘ bbody) brs in
    isSome (lookup_inductive Σ ind.(ci_ind)) && wellformed c && brs'
  | tProj p c => isSome (lookup_inductive Σ p.1.1) && wellformed c
  | tFix mfix idx => 
    List.forallb (test_def (wellformed) (fun b => (isLambda b) && wellformed b)) mfix
  | tCoFix mfix idx =>
    List.forallb (test_def wellformed wellformed) mfix
  | tConst kn _ => isSome (lookup_constant Σ kn)
  | tConstruct ind c _ => isSome (lookup_constructor Σ ind c)
  | tVar _ => true
  | tInd ind _  => isSome (lookup_inductive Σ ind)
  | tSort _ => true
  | tProd na ty1 ty2 => wellformed ty1 && wellformed ty2
  end.
  End Def.

  (* TODO Move *)
  Lemma declared_constructor_lookup {Σ id mdecl idecl cdecl} :
    declared_constructor Σ id mdecl idecl cdecl -> 
    lookup_constructor Σ id.1 id.2 = Some (mdecl, idecl, cdecl).
  Proof.
    intros []. unfold lookup_constructor.
    rewrite (declared_inductive_lookup_inductive (Σ := empty_ext Σ) H) /= H0 //.
  Qed.

  Lemma typing_wellformed :
    env_prop (fun Σ Γ a A => wellformed Σ a)
        (fun Σ Γ => True).
  Proof.
    eapply typing_ind_env; cbn; intros => //.
    all:try rtoProp; intuition auto.
    - red in H0. rewrite /lookup_constant H0 //.
    - now rewrite (declared_inductive_lookup_inductive isdecl).
    - rewrite (declared_constructor_lookup isdecl) //.
    - now rewrite (declared_inductive_lookup_inductive isdecl).
    - red in H8. eapply Forall2_All2 in H8.
      eapply All2i_All2_mix_left in X5; tea. clear H8.
      solve_all.
    - now rewrite (declared_inductive_lookup_inductive isdecl).
    - move/andb_and: H2 => [] hb _.
      solve_all. destruct a as [s []].
      unfold test_def. len in b0.
      rewrite b0. now rewrite i b.
    - solve_all. destruct a as [s []].
      unfold test_def. len in b0. now rewrite i b0.
  Qed.

  Lemma welltyped_wellformed {Σ : global_env_ext} {wfΣ : wf Σ} {Γ a} : welltyped Σ Γ a -> wellformed Σ a.
  Proof.
    intros []. eapply typing_wellformed; tea.
  Qed.
  
End wellscoped.
Import ssrbool.

Section trans_lookups.
  Context {Σ : global_env_ext} {Σ'} (g : globals_erased_with_deps Σ Σ').

  Lemma trans_lookup_constant kn : isSome (lookup_constant Σ kn) -> isSome (EGlobalEnv.lookup_constant Σ' kn).
  Proof.
    unfold lookup_constant, EGlobalEnv.lookup_constant.
    destruct (lookup_env Σ kn) as [[]|] eqn:hl => //.
    eapply g in hl as [? []].
    unfold EGlobalEnv.declared_constant in H. rewrite H //.
  Qed.

  Lemma trans_lookup_inductive kn : isSome (lookup_inductive Σ kn) -> isSome (EGlobalEnv.lookup_inductive Σ' kn).
  Proof.
    destruct g.
    destruct (lookup_inductive Σ kn) as [[]|] eqn:hl => /= //.
    specialize (H0 kn m o). forward H0.
    move: hl. unfold lookup_inductive. 
    destruct lookup_minductive eqn:hl => //.
    destruct nth_error eqn:hnth => //. intros [= <- <-].
    split => //. unfold lookup_minductive in hl.
    unfold declared_minductive. destruct lookup_env as [[]|] => //. now noconf hl.
    destruct H0 as [mdecl' [idecl' ?]].
    unfold EGlobalEnv.lookup_inductive. cbn.
    destruct H0 as [[] ?]. red in H0. rewrite H0 H1 //.
  Qed.

  Lemma trans_lookup_constructor kn c : isSome (lookup_constructor Σ kn c) -> isSome (EGlobalEnv.lookup_constructor Σ' kn c).
  Proof.
    destruct g.
    unfold isSome. 
    destruct (lookup_constructor Σ kn c) as [[[]]|] eqn:hl => /= //.
    specialize (H0 kn m o).
    move: hl. unfold lookup_constructor, lookup_inductive. 
    destruct lookup_minductive eqn:hl => //.
    destruct nth_error eqn:hnth => //.
    destruct (nth_error (ind_ctors _) _) eqn:hnth' => //.
    intros [= <- <- <-].
    forward H0.
    split => //. unfold lookup_minductive in hl.
    unfold declared_minductive. destruct lookup_env as [[]|] => //. now noconf hl.
    intros _.
    destruct H0 as [mdecl' [idecl' ?]].
    unfold EGlobalEnv.lookup_inductive. cbn.
    destruct H0 as [[] ?]. red in H0. rewrite H0 H1 //.
    destruct H2. eapply Forall2_All2 in H2.
    eapply All2_nth_error_Some in H2 as [? []]; tea.
    destruct e0. eapply Forall2_All2 in H2. eapply All2_nth_error_Some in H2 as [? []]; tea.
    rewrite H1 in e. noconf e. rewrite e0 //.
  Qed.
End trans_lookups.

Lemma erases_isLambda {Σ Γ t u} :
  Σ ;;; Γ |- t ⇝ℇ u -> isLambda t -> EAst.isLambda u || EAstUtils.isBox u.
Proof.
  intros hf.
  induction hf => //.
Qed.

Lemma erases_wellformed {Σ : global_env_ext} {wfΣ : wf Σ} {Γ a e} : welltyped Σ Γ a -> Σ ;;; Γ |- a ⇝ℇ e -> 
  forall Σ', globals_erased_with_deps Σ Σ' -> @EWellformed.wellformed EWellformed.all_env_flags Σ' #|Γ| e.
Proof.
  intros wf.
  generalize (welltyped_wellformed wf).
  destruct wf. eapply subject_closed in X. move: X.
  remember #|Γ| as Γl eqn:Heq.
  intros cla wfa era.
  revert Γ e wfa era Heq.
  pattern Γl, a.
  match goal with 
  |- ?P Γl a => simpl; eapply (term_closedn_list_ind P); auto; clear
  end; simpl; intros; subst k;
    match goal with [H:erases _ _ _ _ |- _] => depelim H end; trivial;
    simpl; try solve [solve_all].
  - now apply Nat.ltb_lt.
  - eapply trans_lookup_constant in wfa; tea.
  - eapply trans_lookup_constructor in wfa; tea.
  - move/andP: wfa => [] /andP[] lookup wfc wfbrs.
    apply/andP. split. apply/andP. split; eauto.
    eapply trans_lookup_inductive; tea.
    eapply All_forallb. unfold tCaseBrsProp_k in X0.
    eapply All2_All_mix_left in X1; eauto.
    eapply forallb_All in wfbrs.
    eapply All2_All_mix_left in X1; eauto.
    close_Forall. intros [] []; move=> [] wf. cbn in *. intros.
    solve_all. subst. rewrite map_length. eapply b; eauto. 
    rewrite app_context_length. cbn.
    now rewrite inst_case_branch_context_length.
  - move/andP: wfa => [] hl hc.
    apply/andP; split.
    now eapply trans_lookup_inductive; tea. eauto.
  - epose proof (All2_length X0). eapply forallb_All in wfa.
    solve_all. destruct b.
    destruct y ;  simpl in *; subst.
    unfold EAst.test_def; simpl; eauto.
    rewrite <- H0. rewrite fix_context_length in b1.
    move/andP: b0 => //; eauto. move=> [] wft /andP[] isl wf; eauto.
    eapply b1; tea. now rewrite app_length fix_context_length.
  - epose proof (All2_length X0).
    solve_all. destruct y ;  simpl in *; subst.
    unfold EAst.test_def; simpl; eauto.
    rewrite <-H0. rewrite fix_context_length in b.
    eapply b. now move: b0 => /andP[]. eauto. now rewrite app_length fix_context_length. tea.
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

Lemma is_propositional_bottom {Σ Γ T s s'} :
  wf_ext Σ ->
  check_univs ->
  prop_sub_type = false ->
  Σ ;;; Γ ⊢ T ≤ tSort s ->
  Σ ;;; Γ ⊢ T ≤ tSort s' ->
  PCUICCumulProp.eq_univ_prop s s'.
Proof.
  intros wf cu pst h h'; rewrite /PCUICCumulProp.eq_univ_prop.
  split. split; eapply PCUICCumulProp.is_prop_bottom; tea.
  split; eapply PCUICCumulProp.is_sprop_bottom; tea.
Qed.

Lemma cumul_Sort_Prod_discr {Σ Γ T s na A B} :
  wf_ext Σ ->
  Σ ;;; Γ ⊢ T ≤ tSort s ->
  Σ ;;; Γ ⊢ T ≤ tProd na A B -> False.
Proof.
  intros wfΣ hs hs'.
  eapply ws_cumul_pb_Sort_r_inv in hs as [s' []].
  eapply ws_cumul_pb_Prod_r_inv in hs' as [dom' [codom' [T' []]]].
  destruct (closed_red_confluence c c1) as [nf []].
  eapply invert_red_sort in c2; subst.
  eapply invert_red_prod in c3 as [? [? []]]. discriminate.
Qed.

Import PCUICCumulProp.

Notation " Σ ;;; Γ |- t ~~ u " := (cumul_prop Σ Γ t u)  (at level 50, Γ, t, u at next level) : type_scope.

Lemma is_propositional_bottom' {Σ Γ T s s'} :
  wf_ext Σ ->
  check_univs ->
  prop_sub_type = false ->
  Σ ;;; Γ |- T ~~ tSort s ->
  Σ ;;; Γ |- T ~~ tSort s' ->
  PCUICCumulProp.eq_univ_prop s s'.
Proof.
  intros wf cu pst h h'; rewrite /PCUICCumulProp.eq_univ_prop.
  pose proof (cumul_prop_trans _ _ _ _ _ _ (cumul_prop_sym _ _ _ _ _ h') h).
  split. split; intros; eapply PCUICCumulProp.cumul_prop_props; tea. now symmetry.
  split; intros; eapply PCUICCumulProp.cumul_sprop_props; tea. now symmetry.
Qed.

Lemma is_propositional_lower {Σ s u u'} :
  consistent Σ ->
  leq_universe Σ s u ->
  leq_universe Σ s u' ->
  PCUICCumulProp.eq_univ_prop u u'.
Proof.
  intros wf leu leu'.
  unfold eq_univ_prop; split.
  - split. intros pu. eapply leq_universe_prop_r in leu; tea => //.
    eapply leq_universe_prop_no_prop_sub_type in leu'; trea => //.
    intros pu'. eapply leq_universe_prop_r in leu'; tea => //.
    eapply leq_universe_prop_no_prop_sub_type in leu; tea => //.
  - split. intros pu. eapply leq_universe_sprop_r in leu; tea => //.
    eapply leq_universe_sprop_l in leu'; tea => //.
    intros pu'. eapply leq_universe_sprop_r in leu'; tea => //.
    eapply leq_universe_sprop_l in leu; tea => //.
Qed.

Lemma typing_spine_inj {Σ Γ Δ s args args' u u'} : 
  wf_ext Σ ->
  check_univs ->
  prop_sub_type = false ->
  let T := it_mkProd_or_LetIn Δ (tSort s) in
  typing_spine Σ Γ T args (tSort u) ->
  typing_spine Σ Γ T args' (tSort u') ->
  PCUICCumulProp.eq_univ_prop u u'.
Proof.
  intros wf cu ips T.
  move/typing_spine_it_mkProd_or_LetIn_full_inv => su.
  move/typing_spine_it_mkProd_or_LetIn_full_inv => su'.
  eapply is_propositional_lower; tea. apply wf.
Qed.

Require Import ssrbool.

Lemma Is_proof_ind Σ Γ t : 
  wf_ext Σ ->
  Is_proof Σ Γ t -> 
  forall t' ind u args args', 
  Σ ;;; Γ |- t : mkApps (tInd ind u) args ->
  Σ ;;; Γ |- t' : mkApps (tInd ind u) args' -> 
  Is_proof Σ Γ t'.
Proof.
  intros wfΣ [ty [u [Hty isp]]].
  intros t' ind u' args args' Hty' Hty''.
  epose proof (PCUICPrincipality.common_typing _ wfΣ Hty Hty') as [C [Cty [Cty' Ht'']]].
  destruct isp.
  assert (Σ ;;; Γ |- C : tSort u).
  eapply cumul_prop1'; tea => //. now eapply validity.
  assert (Σ ;;; Γ |- mkApps (tInd ind u') args : tSort u).
  eapply cumul_prop2'; tea => //. now eapply validity.
  eapply inversion_mkApps in X0 as x1. destruct x1 as [? []].
  eapply inversion_Ind in t1 as [mdecl [idecl [wf [decli ?]]]]; eauto.
  destruct (validity Hty'') as [u'' tyargs'].
  eapply inversion_mkApps in X0 as x1. destruct x1 as [? []].
  eapply invert_type_mkApps_ind in X0 as [sp cum]; eauto.
  eapply invert_type_mkApps_ind in tyargs' as f; tea. destruct f as [sp' cum']; eauto.
  do 2 eexists. split => //. tea. instantiate (1 := u'').
  split => //.
  rewrite (declared_inductive_type decli) in sp, sp'.
  rewrite subst_instance_it_mkProd_or_LetIn /= in sp, sp'.
  eapply typing_spine_inj in sp. 5:exact sp'. all:eauto.
  destruct sp as [H H0]. apply/orP. rewrite H H0. now apply/orP.
Qed.

Lemma red_case_isproof {Σ : global_env_ext} {Γ ip p discr discr' brs T} {wfΣ : wf_ext Σ} :
  PCUICReduction.red Σ Γ (tCase ip p discr brs) (tCase ip p discr' brs) ->
  Σ ;;; Γ |- tCase ip p discr brs : T ->
  Is_proof Σ Γ discr -> Is_proof Σ Γ discr'.
Proof.
  intros hr hc.
  eapply subject_reduction in hr; tea; eauto.
  eapply inversion_Case in hc as [mdecl [idecl [isdecl [indices ?]]]]; eauto.
  eapply inversion_Case in hr as [mdecl' [idecl' [isdecl' [indices' ?]]]]; eauto.
  destruct (declared_inductive_inj isdecl isdecl'). subst mdecl' idecl'.
  intros hp. 
  epose proof (Is_proof_ind _ _ _ wfΣ hp).
  destruct p0 as [[] ?]. destruct p1 as [[] ?].
  exact (X _ _ _ _ _ scrut_ty scrut_ty0).
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
  eapply inversion_Construct in HT' as (? & ? & ? & ? & ? & ? & e); auto.
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
  eapply type_Cumul_alt; eauto.
  eapply isType_Sort. 2:eauto.
  destruct (ind_sort x0) => //.
  eapply PCUICSpine.inversion_it_mkProd_or_LetIn in ty; eauto.
  epose proof (typing_spine_proofs _ _ [] _ _ _ [] _ _ eq_refl wfΣ ty).
  forward H0 by constructor. eexists; eauto.
  simpl. now exists cty. eapply PCUICConversion.ws_cumul_pb_eq_le_gen, PCUICSR.wt_cumul_pb_refl; eauto.
  destruct H0 as [_ sorts].
  specialize (sorts _ _ decli c) as [sorts sorts'].
  forward sorts' by constructor.
  do 2 constructor.
  rewrite is_propositional_subst_instance in sorts, sorts' |- *.
  specialize (sorts' isp). rewrite -sorts'. reflexivity.
Qed.  

Lemma isPropositional_propositional Σ Σ' ind mdecl idecl mdecl' idecl' : 
  PCUICAst.declared_inductive Σ ind mdecl idecl ->
  EGlobalEnv.declared_inductive Σ' ind mdecl' idecl' ->
  erases_mutual_inductive_body mdecl mdecl' ->
  erases_one_inductive_body idecl idecl' ->
  forall b, isPropositional Σ ind b -> inductive_isprop_and_pars Σ' ind = Some (b, mdecl.(ind_npars)).
Proof.
  intros [] [] [_ indp] [].
  intros b. unfold isPropositional, inductive_isprop_and_pars, 
    EGlobalEnv.lookup_inductive, EGlobalEnv.lookup_minductive.
  rewrite H H0 H1 /= H2. destruct destArity eqn:da => //.
  destruct p as [ctx s].
  destruct H4 as [_ [_ [_ isP]]].
  red in isP. rewrite da in isP.
  rewrite isP. intros ->. f_equal. f_equal. now rewrite indp.
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

Lemma assumption_context_map2_binders nas Γ :
  assumption_context Γ ->
  assumption_context (map2 set_binder_name nas Γ).
Proof.
  induction 1 in nas |- *; cbn. destruct nas; cbn; auto; constructor.
  destruct nas; cbn; auto; constructor. auto.
Qed.

Lemma declared_constructor_assumption_context (wfl := default_wcbv_flags) {Σ c mdecl idecl cdecl} {wfΣ : wf_ext Σ} :
  declared_constructor Σ c mdecl idecl cdecl ->
  assumption_context (cstr_args cdecl).
Proof.
  intros.
  destruct (on_declared_constructor H) as [? [cu [_ onc]]].
  destruct onc. 
  now eapply is_assumption_context_spec.
Qed.

Lemma assumption_context_cstr_branch_context (wfl := default_wcbv_flags) {Σ} {wfΣ : wf_ext Σ} {c mdecl idecl cdecl} :
  declared_constructor Σ c mdecl idecl cdecl ->
  assumption_context (cstr_branch_context c.1 mdecl cdecl).
Proof.
  intros decl.
  eapply declared_constructor_assumption_context in decl.
  rewrite /cstr_branch_context. pcuic.
Qed.

Lemma expand_lets_erasure (wfl := default_wcbv_flags) {Σ mdecl idecl cdecl c brs p} {wfΣ : wf_ext Σ} :
  declared_constructor Σ c mdecl idecl cdecl ->
  wf_branches idecl brs ->
  All2i (fun i cdecl br => 
   All2 (PCUICEquality.compare_decls eq eq) (bcontext br)
      (cstr_branch_context c.1 mdecl cdecl)) 0 idecl.(ind_ctors) brs ->
  All (fun br => 
    expand_lets (inst_case_branch_context p br) (bbody br) = bbody br) brs.
Proof.
  intros decl wfbrs.
  red in wfbrs.
  eapply Forall2_All2 in wfbrs.
  intros ai.
  eapply All2i_nth_hyp in ai.
  eapply All2i_All2_mix_left in ai; tea. clear wfbrs.
  solve_all.
  red in a. red in a.
  erewrite <- PCUICCasesContexts.inst_case_branch_context_eq; tea.
  rewrite PCUICSigmaCalculus.expand_lets_assumption_context //.
  eapply assumption_context_map2_binders.
  rewrite /pre_case_branch_context_gen /inst_case_context.
  eapply assumption_context_subst_context.
  eapply assumption_context_subst_instance.
  destruct c. cbn.
  eapply (assumption_context_cstr_branch_context (c:=(i0, i))). split. exact decl. tea.
Qed.
        
Lemma erases_subst0 (Σ : global_env_ext) Γ t s t' s' T :
  wf Σ -> wf_local Σ Γ ->
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

Lemma smash_assumption_context Γ Δ : assumption_context Γ ->
  smash_context Δ Γ = Γ ,,, Δ.
Proof.
  intros ass; induction ass in Δ |- *; cbn; auto.
  - now rewrite app_context_nil_l.
  - rewrite smash_context_acc /app_context.
    rewrite IHass /=.
    rewrite -(app_tip_assoc Δ _ Γ). f_equal.
    rewrite -/(expand_lets_k_ctx Γ 0 _).
    rewrite [expand_lets_k_ctx _ _ _]expand_lets_ctx_assumption_context //.
Qed.

Lemma subslet_cstr_branch_context {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} 
  {Γ pars parsubst parsubst' s' inst' ind n mdecl idecl cdecl u p br napp} : 
  declared_constructor Σ (ind, n) mdecl idecl cdecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  consistent_instance_ext Σ (ind_universes mdecl) (puinst p) ->
  PCUICEquality.R_global_instance Σ (eq_universe Σ) (leq_universe Σ) (IndRef ind) napp u (puinst p) ->
  spine_subst Σ Γ pars parsubst (ind_params mdecl)@[u] ->
  spine_subst Σ Γ (pparams p) parsubst' (ind_params mdecl)@[puinst p] ->
  assumption_context cdecl.(cstr_args) ->
  ws_cumul_pb_terms Σ Γ pars (pparams p) ->
  wf_predicate mdecl idecl p ->
  wf_branch cdecl br ->
  PCUICSpine.spine_subst Σ Γ s' inst' 
    (subst_context parsubst 0 (subst_context (inds (inductive_mind ind) u (ind_bodies mdecl)) #|ind_params mdecl| (cstr_args cdecl)@[u])) ->
  subslet Σ Γ (List.rev s') (case_branch_context ind mdecl p (forget_types (bcontext br)) cdecl).
Proof.
  intros declc cu cu' hr sppars sppars' assargs eqp wfp wfbr spargs.
  rewrite /case_branch_context /case_branch_context_gen.
  eapply PCUICSpine.subslet_eq_context_alpha.
  symmetry. eapply PCUICCasesContexts.eq_binder_annots_eq.
  eapply wf_pre_case_branch_context_gen; tea.
  rewrite /pre_case_branch_context_gen /inst_case_context.
  rewrite /cstr_branch_context.
  rewrite subst_instance_expand_lets_ctx
    subst_instance_subst_context.
  rewrite PCUICInductives.instantiate_inds //. exact declc.
  epose proof (constructor_cumulative_indices declc cu cu' hr _ _ _ _ _ sppars sppars' eqp) as [eqctx _].
  cbn in eqctx.
  epose proof (spine_subst_smash spargs).
  eapply spine_subst_cumul in X. eapply X.
  pcuic. pcuic. apply X. 
  { eapply substitution_wf_local. eapply (spine_subst_smash sppars').
    eapply wf_local_expand_lets.
    rewrite -app_context_assoc.
    eapply weaken_wf_local => //. eapply sppars.
    eapply (PCUICSR.on_constructor_wf_args declc) => //. }
  rewrite /=.
  rewrite -(spine_subst_inst_subst sppars').
  assert (smash_context [] (cstr_args cdecl)@[puinst p] = (cstr_args cdecl)@[puinst p]).
  { rewrite smash_assumption_context //. pcuic. }
  rewrite -H.
  rewrite -smash_context_subst /= subst_context_nil.
  rewrite -smash_context_subst /= subst_context_nil. apply eqctx.
Qed.

Lemma firstn_app_left {A} n (l l' : list A) : 
  n = #|l| ->  
  firstn n (l ++ l') = l.
Proof.
  intros ->.
  rewrite firstn_app firstn_all Nat.sub_diag firstn_0 // app_nil_r //.
Qed.

Lemma assumption_context_compare_decls Γ Δ : 
  eq_context_upto_names Γ Δ ->
  assumption_context Γ ->
  assumption_context Δ.
Proof.
  induction 1; auto.
  intros H; depelim H. 
  depelim r; econstructor; auto.
Qed. 


Lemma eval_tCase {cf : checker_flags} {Σ : global_env_ext}  ci p discr brs res T :
  wf Σ ->
  Σ ;;; [] |- tCase ci p discr brs : T ->
  eval Σ (tCase ci p discr brs) res -> 
  ∑ c u args, PCUICReduction.red Σ [] (tCase ci p discr brs) (tCase ci p ((mkApps (tConstruct ci.(ci_ind) c u) args)) brs).
Proof.
  intros wf wt H. depind H; try now (cbn in *; congruence).
  - eapply inversion_Case in wt as (? & ? & ? & ? & cinv & ?); eauto.
    eexists _, _, _. eapply PCUICReduction.red_case_c. eapply wcbeval_red. 2: eauto. eapply cinv.
  - eapply inversion_Case in wt as wt'; eauto. destruct wt' as (? & ? & ? & ? & cinv & ?).
    assert (Hred1 : PCUICReduction.red Σ [] (tCase ip p discr brs) (tCase ip p (mkApps fn args) brs)). {
      etransitivity. { eapply PCUICReduction.red_case_c. eapply wcbeval_red. 2: eauto. eapply cinv. } 
      econstructor. econstructor.
      rewrite closed_unfold_cofix_cunfold_eq. eauto.
      enough (closed (mkApps (tCoFix mfix idx) args)) as Hcl by (rewrite closedn_mkApps in Hcl; solve_all).
      eapply eval_closed. eauto.
      2: eauto. eapply @subject_closed with (Γ := []); eauto. eapply cinv. eauto.
    }
    edestruct IHeval2 as (c & u & args0 & IH); eauto using subject_reduction.
    exists c, u, args0. etransitivity; eauto.
Qed.

(* Lemma invert_red1_case {Σ Γ ci discr discr' p brs} : 
  PCUICReduction.red1 Σ Γ (tCase ci p discr brs) (tCase ci p discr' brs) ->
  PCUICReduction.red1 Σ Γ discr discr'.
Proof.
  intros H; depelim H; solve_discr.
   *)


(*Lemma case_unique_type {cf : checker_flags} {Σ : global_env_ext} {Γ ci p discr discr' brs T} {wfΣ : wf Σ} :
  Σ ;;; Γ |- tCase ci p discr brs : T ->
  Σ ;;; Γ |- tCase ci p discr' brs : T ->
  ∑ T', Σ ;;; Γ |- discr : T' × Σ ;;; Γ |- discr' : T'.
Proof.
  intros c c'.
  eapply inversion_Case in c as (? & ? & ? & ? & [] & ?); eauto.
  eapply inversion_Case in c' as (? & ? & ? & ? & [] & ?); eauto.
  pose proof (validity scrut_ty).
  pose proof (validity scrut_ty0).
  have eqty : Σ ;;; Γ ⊢ mkApps (tInd ci (puinst p)) (pparams p ++ x6) = mkApps (tInd ci (puinst p)) (pparams p ++ x2).
  eapply ws_cumul_pb_mkApps.
  eapply ws_cumul_pb_refl => //. fvs.
  eapply isType_open in X. move: X; rewrite on_free_vars_mkApps forallb_app.
  move=> /andP[] _ /andP[] clpar clx2.
  eapply isType_open in X0. move: X0; rewrite on_free_vars_mkApps forallb_app.
  move=> /andP[] _ /andP[] _ clx6.
  eapply All2_app. eapply ws_cumul_pb_terms_refl; fvs.




  destruct X as [? X]. eapply PCUICValidity.inversion_mkApps in X as [? []].
  eapply typing_spine
*)

Lemma eval_empty_brs {wfl : Ee.WcbvFlags} Σ ci p e : Σ ⊢ E.tCase ci p [] ▷ e -> False.
Proof.
  intros He.
  depind He. 
  - clear -e0. now rewrite nth_error_nil in e0.
  - discriminate.
  - eapply IHHe2.
  - cbn in i. discriminate.
Qed.

Lemma eval_case_tBox_inv {wfl : Ee.WcbvFlags} {Σ ci e brs} : 
  Σ ⊢ E.tCase ci EAst.tBox brs ▷ e -> 
  ∑ n br, brs = [(n, br)] × inductive_isprop_and_pars Σ ci.1 = Some (true, ci.2) × 
  Σ ⊢ ECSubst.substl (repeat EAst.tBox #|n|) br ▷ e.
Proof.
  intros He.
  depind He. 
  - depelim He1. clear -H. symmetry in H. elimtype False.
    destruct args using rev_case. discriminate.
    rewrite EAstUtils.mkApps_app in H. discriminate.
  - exists n, f. intuition auto.
  - depelim He1. clear -H. symmetry in H. elimtype False.
    destruct args using rev_case. discriminate.
    rewrite EAstUtils.mkApps_app in H. discriminate.
  - cbn in i. discriminate.
Qed.

Lemma eval_case_eval_discr {wfl : Ee.WcbvFlags} {Σ ci c c' e brs} : 
  Σ ⊢ E.tCase ci c brs ▷ e -> 
  Σ ⊢ c ▷ c' ->
  Σ ⊢ E.tCase ci c' brs ▷ e.
Proof.
  intros He Hc.
  depind He. 
  - pose proof (Ee.eval_deterministic He1 Hc). subst c'.
    econstructor; eauto. now eapply Ee.value_final, Ee.eval_to_value.
  - pose proof (Ee.eval_deterministic He1 Hc). subst c'.
    eapply Ee.eval_iota_sing; tea. now constructor.
  - pose proof (Ee.eval_deterministic He1 Hc). subst c'.
    eapply Ee.eval_cofix_case; tea.
    now eapply Ee.value_final, Ee.eval_to_value.
  - cbn in i. discriminate.
Qed.

Lemma eval_trans {wfl : Ee.WcbvFlags} {Σ e e' e''} :
  Σ ⊢ e ▷ e' -> Σ ⊢ e' ▷ e'' -> e' = e''.
Proof.
  intros ev ev'.
  eapply Ee.eval_to_value in ev.
  eapply Ee.value_final in ev.
  eapply (Ee.eval_deterministic ev ev').
Qed.

Lemma eval_case_eval_inv_discr {wfl : Ee.WcbvFlags} {Σ ci c c' e brs} : 
  Σ ⊢ E.tCase ci c brs ▷ e -> 
  Σ ⊢ c' ▷ c ->
  Σ ⊢ E.tCase ci c' brs ▷ e.
Proof.
  intros He Hc.
  depind He. 
  - pose proof (eval_trans Hc He1); subst discr.
    econstructor; eauto.
  - pose proof (eval_trans Hc He1); subst discr.
    eapply Ee.eval_iota_sing; tea.
  - pose proof (eval_trans Hc He1); subst discr.
    eapply Ee.eval_cofix_case; tea.
  - cbn in i. discriminate.
Qed.

Lemma eval_proj_eval_inv_discr {wfl : Ee.WcbvFlags} {Σ p c c' e} : 
  Σ ⊢ E.tProj p c ▷ e -> 
  Σ ⊢ c' ▷ c ->
  Σ ⊢ E.tProj p c' ▷ e.
Proof.
  intros He Hc.
  depind He. 
  - pose proof (eval_trans Hc He1); subst discr.
    econstructor; eauto.
  - pose proof (eval_trans Hc He1); subst discr.
    eapply Ee.eval_proj; tea.
  - pose proof (eval_trans Hc He); subst discr.
    eapply Ee.eval_proj_prop; tea.
  - cbn in i. discriminate.
Qed.

Lemma Informative_cofix v ci p brs T (Σ : global_env_ext) :
   wf_ext Σ ->
   forall (mdecl : mutual_inductive_body) (idecl : one_inductive_body) mfix idx,
   declared_inductive Σ.1 ci.(ci_ind) mdecl idecl ->
   forall (args : list term), Informative Σ ci.(ci_ind) ->
   Σ ;;; [] |- tCase ci p (mkApps (tCoFix mfix idx) args) brs : T ->
   Σ |-p tCase ci p (mkApps (tCoFix mfix idx) args) brs ▷ v ->
   Is_proof Σ [] (mkApps (tCoFix mfix idx) args) ->
   #|ind_ctors idecl| <= 1.
Proof.
  intros. destruct Σ as [Σ1 Σ2]. cbn in *.
  eapply eval_tCase in X0 as X2'; eauto. destruct X2' as (? & ? & ? & ?).
  eapply subject_reduction in X0 as X2'; eauto.
  eapply inversion_Case in X2' as (? & ? & ? & ? & [] & ?); eauto.
  eapply inversion_Case in X0 as (? & ? & ? & ? & [] & ?); eauto.
  destruct (declared_inductive_inj x8 x4); subst.
  destruct (declared_inductive_inj x8 H); subst.
  eapply H0; eauto. reflexivity.
  eapply Is_proof_ind; tea.
Qed.


Lemma isErasable_unfold_cofix {Σ : global_env_ext} {Γ mfix idx} {wfΣ : wf Σ} decl :
  isErasable Σ Γ (tCoFix mfix idx) -> 
  nth_error mfix idx = Some decl ->
  isErasable Σ Γ (subst0 (cofix_subst mfix) (dbody decl)).
Proof.
  intros [Tty []] hred.
  exists Tty. split => //.
  eapply type_tCoFix_inv in t as t''; eauto.
  destruct t'' as [decl' [[[] h'] h'']].
  rewrite e in hred. noconf hred.
  eapply type_ws_cumul_pb; tea.
  now eapply validity.
Qed.

Lemma isErasable_red {Σ : global_env_ext} {Γ T U} {wfΣ : wf Σ} :
  isErasable Σ Γ T -> PCUICReduction.red Σ Γ T U -> isErasable Σ Γ U.
Proof.
  intros [Tty []] hred.
  exists Tty. split => //. eapply subject_reduction; tea.
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
      eapply inversion_Lambda in X0 as (? & ? & ? & ? & e0).
      assert (Σ ;;; [] |- a' : t). {
          eapply subject_reduction_eval; eauto.
          eapply PCUICConversion.ws_cumul_pb_Prod_Prod_inv in e0 as [? e1 e2].
          eapply type_Cumul_alt. eassumption. now exists x2.
          symmetry in e1.
          eapply ws_cumul_pb_forget in e1. 
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
           eapply erases_closed in Hvu'; auto; fvs.
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
        cbn in *. eapply context_conversion. 3:eauto. all:cbn; eauto.
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
      eapply eval_closed. eauto. 2:eauto. now eapply subject_closed in t1.
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
        eapply declared_constant_inv in isdecl'; [| |now eauto|now apply wfΣ].
        2:eapply weaken_env_prop_typing.
        unfold on_constant_decl in isdecl'. rewrite e in isdecl'. red in isdecl'.
        unfold declared_constant in isdecl''.
        now eapply @typing_subst_instance_decl with (Σ := Σ) (Γ := []); eauto.
      * assert (isdecl'' := isdecl').
        eapply declared_constant_inv in isdecl'; [| |now eauto|now apply wfΣ].
        unfold on_constant_decl in isdecl'. rewrite e in isdecl'. cbn in *.
        2:eapply weaken_env_prop_typing.
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
  assert (Hcstr := X0).
  eapply Construct_Ind_ind_eq in X0; tea. 2:pcuic.
  destruct X0 as (((([_ Ru] & cu) & cpu) & ?) & (parsubst & argsubst & parsubst' & argsubst' & [])).
  invs He.
  + depelim Hed.
    rename H1 into decli. rename H2 into decli'.
    rename H3 into em. rename Hed into er.
    edestruct (IHeval1 _ scrut_ty) as (v' & Hv' & [He_v']); eauto.
    pose proof e as Hnth.
    assert (lenppars : ind_npars mdecl = #|pparams p|).
    { now rewrite (wf_predicate_length_pars wf_pred). }
    destruct (declared_inductive_inj d decli); subst mdecl0 idecl0.
    eapply erases_mkApps_inv in Hv' as [(? & ? & ? & ? & [] & ? & ? & ?) | (? & ? & ? & ? & ?)]; eauto.
    * subst.
      eapply Is_type_app in X1; auto. destruct X1.
      2:{ rewrite -mkApps_app; tea. }
      rewrite -mkApps_app in X1.

      eapply tConstruct_no_Type in X1; auto.
      
      eapply H6 in X1 as []; eauto. 2: split; auto; exists []; now destruct Σ.

      destruct (ind_ctors idecl) eqn:hctors.
      { cbn in *. depelim brs_ty. rewrite nth_error_nil // in Hnth. }
      depelim brs_ty. cbn in H1. 
      destruct l; cbn in *; try lia.
      depelim brs_ty. depelim X0. depelim X0.
      destruct p1.
      destruct c; cbn in *. noconf Hnth. 2:{ rewrite nth_error_nil // in Hnth. }
      destruct p0 as (? & ? & ? & ?).
      assert (c1 = cdecl).
      { destruct d. rewrite hctors /= in H10. now noconf H10. }
      depelim H5.
      subst c1.
      destruct y0 as [n br']; cbn in *.
      edestruct IHeval2 as (? & ? & [?]).
      eapply subject_reduction. eauto. exact Hty.
      etransitivity.
      eapply PCUICReduction.red_case_c. eapply wcbeval_red; eauto.
      econstructor. econstructor.
      eauto. eauto.
      rename y into br.
      all:unfold iota_red in *. all:cbn in *.
      {
        assert (expand_lets (inst_case_branch_context p br) (br.(PCUICAst.bbody)) = br.(PCUICAst.bbody)) as ->. {
          unshelve edestruct @on_declared_constructor as (? & ? & ? & []). 8: exact d. all: eauto.
          pattern br.
          eapply All_nth_error.
          eapply (expand_lets_erasure (p:=p) d wf_brs); eauto.
          rewrite hctors; constructor.
          solve_all. constructor.
          instantiate (1 := 0); cbn; eassumption.
        }
        invs H9.
        eapply erases_subst0; eauto.
        rewrite [case_branch_context_gen _ _ _ _ _ _]PCUICCasesContexts.inst_case_branch_context_eq; eauto.
        1:{ unfold app_context. cbn. rewrite app_nil_r.
            eapply (subslet_cstr_branch_context (u:=u)); tea.
            - rewrite lenppars firstn_app_left // in s0. exact s0.
            - eapply (declared_constructor_assumption_context d).
            - destruct s3 as [Hs [_ []]].
              rewrite {2}lenppars [firstn _ (pparams p ++ _)]firstn_app_left // in a1.
            - red in wf_brs. rewrite hctors in wf_brs. now depelim wf_brs.
            - rewrite -eq_npars. exact s1. }
        eapply All2_rev.
        rewrite -eq_npars.
        eapply All_All2_flex; tea.
        2:{ instantiate (1 := repeat EAst.tBox #|skipn (ind_npars mdecl) (x ++ x0)|).
            now rewrite repeat_length. }
        intros ? ? ? % repeat_spec. subst.
        constructor.
        now eapply isErasable_Proof. }
      2:{      
      exists x2. split; eauto. constructor. eapply eval_iota_sing => //.
      pose proof (Ee.eval_to_value _ _ _ He_v').
      eapply value_app_inv in X0. subst. eassumption.
      depelim H2.
      eapply isErasable_Propositional in X0; eauto.
      rewrite -eq_npars.
      eapply isPropositional_propositional; eauto.
      invs e. cbn in *.
      rewrite -eq_npars in e0.
      rewrite skipn_length e0 in H11.
      rewrite map_length.
      rewrite (@assumption_context_assumptions (bcontext y)) // ?rev_repeat in H11 => //.
      { eapply assumption_context_compare_decls. symmetry in a. exact a.
        rewrite /cstr_branch_context. eapply assumption_context_expand_lets_ctx.
        eapply assumption_context_subst_context.
        apply (declared_constructor_assumption_context d). }
      rewrite ECSubst.substl_subst //.
      { eapply All_Forall, All_repeat. econstructor. }
      replace (ind_npars mdecl + #|bcontext y| - ind_npars mdecl) 
      with #|bcontext y| in H11 by lia. eauto.
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
      assert (declared_constructor Σ (ind, c) mdecl idecl x2).
      { split; tea. }
      destruct (declared_constructor_inj d H1) as [_ [_ <-]]. clear H1.
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
          eapply (expand_lets_erasure d wf_brs). solve_all.
        } 
        eapply erases_subst0; eauto.  
        all: try rewrite case_branch_type_fst PCUICCasesContexts.inst_case_branch_context_eq; eauto.
        rewrite app_context_nil_l. 
        erewrite <-PCUICCasesContexts.inst_case_branch_context_eq; eauto.
        1:{ eapply (subslet_cstr_branch_context (u:=u)); tea.
            - rewrite lenppars firstn_app_left // in s0. exact s0.
            - eapply (declared_constructor_assumption_context d).
            - destruct s3 as [Hs [_ []]].
              rewrite {2}lenppars [firstn _ (pparams p ++ _)]firstn_app_left // in a1.
            - red in wf_brs. eapply Forall2_All2 in wf_brs.
              eapply All2_nth_error in wf_brs; tea.
            - rewrite -eq_npars. exact s1. }
      eapply All2_rev. eapply All2_skipn. 
      eapply Forall2_All2 in H3. eapply All2_impl. exact H3. intros. eauto.
       }
      
      eapply nth_error_forall in H5; [|now eauto].
      eapply erases_deps_subst; eauto.
      eapply All_rev.
      eapply erases_deps_eval in He_v'; [|now eauto].
      eapply erases_deps_mkApps_inv in He_v' as (? & ?).
      now eapply All_skipn, Forall_All.
      
      invs H2.
      -- exists x2. split; eauto.
         constructor. econstructor. eauto. 2:eauto.
         3:{ unfold EGlobalEnv.iota_red.
          rewrite ECSubst.substl_subst //.
          eapply Forall_rev, Forall_skipn.
          assert (Forall (closedn 0) args).
          { move/eval_closed: H; tea.
            move/(_ (subject_closed scrut_ty)).
            rewrite closedn_mkApps /=. solve_all. } 
          solve_all. eapply (erases_closed _ []); tea. } 
         rewrite -eq_npars.
         eapply isPropositional_propositional; eauto.
         rewrite -e4 List.skipn_length - (Forall2_length H3) -List.skipn_length.
         rewrite skipn_length e0.
         replace (ci_npar ind + context_assumptions (bcontext br) - ci_npar ind)
    with (context_assumptions (bcontext br)) by lia.  
         rewrite map_length.
         eapply assumption_context_assumptions.
         eapply assumption_context_compare_decls. symmetry; tea.
         eapply (assumption_context_cstr_branch_context d).
      -- eapply Is_type_app in X1 as []; auto.
         2:{ eapply subject_reduction_eval. 2:eassumption. eauto. }
         assert (ispind : inductive_isprop_and_pars Σ' ind = Some (true, ind_npars mdecl)).
         { eapply isPropositional_propositional; eauto. eapply isErasable_Propositional; eauto. }

         eapply tConstruct_no_Type in X1; auto.
         eapply H6 in X1 as []; eauto. 2:reflexivity.

         destruct (ind_ctors idecl) eqn:hctors. cbn in *. destruct c; invs e5.
         destruct l; cbn in *; try lia. destruct c as [ | []]; cbn in *; invs e5.

         (* destruct btys as [ | ? []]; cbn in *; try discriminate. *)
         destruct brs'; invs e2.
         destruct brs; invs Hnth.
         destruct H9.
         depelim brs_ty. depelim brs_ty.
         depelim X0. depelim X0.
         destruct p0 as (? & ? & ? & ?).
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
            rewrite hctors. constructor; auto. constructor.
          }
        destruct p1.
        eapply erases_subst0; eauto.
        - rewrite case_branch_type_fst PCUICCasesContexts.inst_case_branch_context_eq; eauto.
        - rewrite app_context_nil_l.
          eapply subslet_cstr_branch_context. tea. exact cu. all:eauto.
          now rewrite lenppars firstn_app_left // in s0.
          eapply (declared_constructor_assumption_context d).
          destruct s3 as [? [? [eqp _]]].
          rewrite lenppars firstn_app_left // in eqp. congruence.
          move: wf_brs. now rewrite /wf_branches hctors => h; depelim h.
          rewrite -eq_npars. exact s1.
        - eapply All2_rev. cbn.
          rewrite -eq_npars.
          eapply All_All2_flex.
          exact X1.
          intros ? ? -> % repeat_spec.
          intros. econstructor. eapply isErasable_Proof. eauto.
          rewrite repeat_length. reflexivity.
        }

         depelim H5.
         eapply erases_deps_subst; eauto.
         eapply All_rev, All_repeat.
         econstructor.

         exists x. split; eauto.
         constructor.
         destruct x1 as [n br'].
         eapply eval_iota_sing => //.
         pose proof (Ee.eval_to_value _ _ _ He_v').
         apply value_app_inv in X0; subst x0.
         apply He_v'.
         now rewrite -eq_npars.
         
         cbn in *.

         rewrite ECSubst.substl_subst.
         { eapply All_Forall, All_repeat. econstructor. }

         rewrite rev_repeat in H10.
         
         enough (#|skipn (ind_npars mdecl) args| = #|n|) as <- by eauto.
         edestruct invert_Case_Construct as (? & ? & ? & ?).
         { econstructor. eauto. }
         { eapply subject_reduction. eauto. exact Hty.
           eapply PCUICReduction.red_case_c. eapply wcbeval_red; eauto. }

        rewrite eq_npars. rewrite List.skipn_length e0.
        replace (ci_npar ind + context_assumptions (bcontext br) - ci_npar ind)
    with (context_assumptions (bcontext br)) by lia.
        subst n. rewrite map_length. 
        rewrite assumption_context_assumptions //.
        eapply assumption_context_compare_decls. symmetry; tea.
        eapply (assumption_context_cstr_branch_context d).
    + exists EAst.tBox. split. econstructor.
      eapply Is_type_eval; eauto. constructor. econstructor; eauto.
  - pose (Hty' := Hty).
    eapply inversion_Proj in Hty' as (? & ? & ? & [] & ? & ? & ? & ? & ?); [|easy].
    assert (Hpars : pars = ind_npars x0).
    { destruct d as [? []]. now rewrite H3. }
    invs He.

    + depelim Hed.
      rename H1 into decli. rename H2 into decli'. rename H4 into er. rename H3 into em. rename H5 into H3.
      eapply IHeval1 in H6 as (vc' & Hvc' & [Hty_vc']); eauto.
      eapply erases_mkApps_inv in Hvc'; eauto.
      2: eapply subject_reduction_eval; eauto.
      destruct Hvc' as [ (? & ? & ? & ? & [] & ? & ? & ?) | (? & ? & ? & ? & ?)]; subst.
      * exists EAst.tBox.
        assert (isprop : inductive_isprop_and_pars Σ' i = Some (true, ind_npars mdecl)).
        { eapply isPropositional_propositional; eauto. eapply isErasable_Propositional; eauto. }
        destruct (declared_inductive_inj decli d) as [<- <-].
        split.
        eapply Is_type_app in X as []; eauto. 2:{ rewrite -mkApps_app. eapply subject_reduction_eval; eauto. }
        rewrite -mkApps_app in X.

        eapply tConstruct_no_Type in X; eauto. eapply H3 in X as [? []]; eauto.
        2: split; auto; now exists []; destruct Σ.
        destruct d as (? & ? & ?).
        
        econstructor.
        eapply Is_type_eval; eauto.
        eapply nth_error_all.
        erewrite nth_error_skipn. eassumption.
        eapply All_impl.
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
        eapply Prelim.typing_spine_inv in t1 as []; eauto.
        eapply IHeval2 in H3 as (? & ? & [?]); eauto.
        invs H2.
        -- exists x9. split; eauto. constructor. eapply Ee.eval_proj; eauto.
            destruct (declared_inductive_inj decli d); subst x0 x1.
            now eapply isPropositional_propositional; eauto.
            rewrite <- nth_default_eq. unfold nth_default. now rewrite H1.
        -- exists EAst.tBox.
            assert (isprop : inductive_isprop_and_pars Σ' i = Some (true, ind_npars mdecl)).
            { eapply isPropositional_propositional; eauto; eapply (isErasable_Propositional (args:=[])); eauto. }
            destruct (declared_inductive_inj decli d) as [<- <-].
            split.
            eapply Is_type_app in X as []; eauto. 2:{ eapply subject_reduction_eval; [|eauto]; eauto. }

            eapply tConstruct_no_Type in X. eapply Hinf in X as [? []]; eauto.
            2: now destruct d. 2:eauto.
            econstructor.
            eapply Is_type_eval; eauto.
            eapply nth_error_all.
            erewrite nth_error_skipn. eassumption.
            eapply All_impl.
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
    eapply inversion_App in Hty' as (? & ? & ? & ? & ? & e0); eauto.
    assert (Ht := t).
    eapply subject_reduction in t. 2:auto. 2:eapply wcbeval_red; eauto.
    assert (HT := t).
    apply PCUICValidity.inversion_mkApps in HT as (? & ? & ?); auto.
    assert (Ht1 := t1).
    apply inversion_Fix in t1 as Hfix; auto.
    destruct Hfix as (? & ? & ? & ? & ? & ? & e1).
    unfold cunfold_fix in e. rewrite e2 in e. invs e.
    depelim He; first last.
    
    + exists EAst.tBox. split; [|now constructor; constructor].
      econstructor.
      eapply Is_type_eval. 3:eapply X. eauto.
      eapply eval_fix; eauto.
      rewrite /cunfold_fix e2 //. now rewrite H3.
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
        - rewrite -mkApps_app app_assoc mkApps_snoc.
          eapply PCUICValidity.type_App'; eauto.
          eapply subject_reduction; eauto.
          eapply wcbeval_red; eauto.
        - eapply erases_box.
          eapply Is_type_eval; auto. 2:eauto.
          rewrite mkApps_app /=.
          eapply eval_fix.
          rewrite -mkApps_app. eapply value_final.
          eapply eval_to_value; eauto.
          eapply value_final, eval_to_value; eauto.
          rewrite /cunfold_fix e2 //. auto.
          now rewrite H3. auto. }

      invs H2.
      * assert (Hmfix' := X).
        eapply All2_nth_error_Some in X as (? & ? & ?); eauto.
        pose proof (closed_fix_substl_subst_eq (subject_closed t1) e2) as cls.
        destruct x3. cbn in *. subst.

        enough (Σ;;; [] ,,, subst_context (fix_subst mfix) 0 []
                |- subst (fix_subst mfix) 0 dbody
                ⇝ℇ ELiftSubst.subst (EGlobalEnv.fix_subst mfix') 0 (Extract.E.dbody x4)).
        destruct a2.

        clear e3. rename H into e3.
        -- cbn in e3. rename x5 into L.
           eapply (erases_mkApps _ _ _ _ (argsv ++ [av])) in H2; first last.
           { eapply Forall2_app.
             - exact H4.
             - eauto. }
           rewrite mkApps_app in H2.
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
             eapply PCUICReduction.red_fix.
             rewrite closed_unfold_fix_cunfold_eq.
             now eapply subject_closed in t1.
             rewrite /cunfold_fix e2 /= //.
             pose proof (eval_to_value _ _ _ e3) as vfix.
             eapply PCUICWcbvEval.stuck_fix_value_args in vfix; eauto.
             2:{ rewrite /cunfold_fix e2 //. }
             simpl in vfix. 
             subst. unfold is_constructor.
             rewrite nth_error_snoc. lia.
             assert(Σ ;;; [] |- mkApps (tFix mfix idx) (argsv ++ [av]) : subst [av] 0 x1).
             { rewrite mkApps_app. eapply PCUICValidity.type_App'; eauto.
               eapply subject_reduction_eval; eauto. }
             epose proof (fix_app_is_constructor (args:=argsv ++ [av]) X).
             rewrite /unfold_fix e2 in X0.
             specialize (X0 eq_refl). simpl in X0.
             rewrite nth_error_snoc in X0. auto. apply X0.
             eapply value_axiom_free, eval_to_value; eauto.
             eapply value_whnf; eauto.
             eapply eval_closed; eauto. now eapply subject_closed in t0.
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
           ++ eauto.
           ++ rewrite <- Ee.closed_unfold_fix_cunfold_eq.
              { unfold EGlobalEnv.unfold_fix. rewrite e -e4.
                now rewrite (Forall2_length H4). }
              eapply eval_closed in e3; eauto.
              clear -e3 Hmfix'.
              pose proof (All2_length Hmfix').
              rewrite closedn_mkApps in e3.
              apply andb_true_iff in e3 as (e3 & _).
              change (?a = true) with (is_true a) in e3.
              simpl in e3 |- *. solve_all.
              rewrite app_context_nil_l in b.
              destruct b as [eqb eqrar isl isl' e].
              eapply erases_closed in e. simpl in e.
              rewrite <- H.
              unfold EAst.test_def. 
              simpl in e.
              rewrite fix_context_length in e.
              now rewrite Nat.add_0_r.
              unfold test_def in a. apply andb_and in a as [_ Hbod].
              rewrite fix_context_length.
              now rewrite Nat.add_0_r in Hbod.
              eauto with pcuic.
              now eapply subject_closed in Ht.
          ++ auto.
           
        -- cbn. destruct a2 as [eqb eqrar isl isl' e5].
           eapply (erases_subst Σ [] (fix_context mfix) [] dbody (fix_subst mfix)) in e5; cbn; eauto.
           ++ eapply subslet_fix_subst. now eapply wf_ext_wf. all: eassumption.
           ++ eapply nth_error_all in a1; eauto. cbn in a1.
              eapply a1.
           ++ eapply All2_from_nth_error.
              erewrite fix_subst_length, EGlobalEnv.fix_subst_length, All2_length; eauto.
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
              rewrite mkApps_app.
              eapply eval_fix; eauto. 
              1-2:eapply value_final, eval_to_value; eauto.
              rewrite /cunfold_fix e2 //. congruence.
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
    { eapply wcbeval_red; eauto. }

    eapply erases_App in He as He'; [|eauto].
    destruct He' as [(-> & [])|(? & ? & -> & ? & ?)].
    + exists E.tBox.
      split; [|now constructor; eauto using @Ee.eval].
      constructor.
      eapply Is_type_red.
      * eauto.
      * eapply PCUICReduction.red_app.
        -- eapply wcbeval_red; revgoals; eauto.
        -- eapply wcbeval_red; revgoals; eauto.
      * eauto.
    + depelim Hed.
      eapply subject_reduction in t0 as typ_arg; [|eauto|]; first last.
      { eapply wcbeval_red; revgoals; eauto. }

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
           eapply All2_nth_error_Some in X as (?&?&[? ? ? ? ?]); [|eauto].
           constructor. eapply Ee.eval_fix_value.
           ++ eauto.
           ++ eauto.
           ++ eauto.
           ++ unfold EGlobalEnv.cunfold_fix. now rewrite e0.
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
    pose proof H as Heval.
    eapply subject_reduction_eval in t0' as t1. 2: eauto.
    eapply PCUICValidity.inversion_mkApps in t1 as (? & ? & ?); eauto.
    pose proof (subject_closed t) as clfix.
    assert (htcof : Σ ;;; [] |- tCase ip p (mkApps (tCoFix mfix idx) args) brs : T).
    { eapply subject_reduction; eauto. eapply PCUICReduction.red_case_c.
      eapply wcbeval_red in H; eauto. }
    assert (hredcasecof : 
      PCUICReduction.red Σ [] (tCase ip p (mkApps (tCoFix mfix idx) args) brs)
        (tCase ip p (mkApps fn args) brs)).
    { constructor; eapply PCUICReduction.red_cofix_case.
        move: e. rewrite closed_unfold_cofix_cunfold_eq; eauto. }
    assert (htcasefn : Σ ;;; [] |- tCase ip p (mkApps fn args) brs : T).
    { eapply subject_reduction; eauto. }
    assert (hredcasediscrcof : 
      PCUICReduction.red Σ [] (tCase ip p discr brs) res).
    { etransitivity. eapply PCUICReduction.red_case_c; tea.
      eapply wcbeval_red in H. tea. eauto.
      etransitivity; tea. eapply wcbeval_red; tea. }
    assert (htunfcof : Σ ;;; [] |- tCase ip p (mkApps fn args) brs : T).
    { eapply subject_reduction; eauto. }
    specialize (IHeval1 _ t0').
    specialize (IHeval2 _ htunfcof).
    eapply inversion_CoFix in t; destruct_sigma t; auto.
    eapply PCUICSpine.typing_spine_strengthen in t0; eauto. 
    2:{ now eapply nth_error_all in a; tea. }
    invs He.
    * edestruct IHeval1 as (? & ? & ?); eauto. now depelim Hed.
      depelim Hed.
      destruct (declared_inductive_inj H1 decli). subst mdecl0 idecl0.
      rename H0 into decli'. rename H1 into decli''. rename H2 into er. rename H3 into H0.
      eapply erases_mkApps_inv in H8; eauto.
      destruct H8 as [He|He]; destruct_sigma He.
      -- destruct He as (? & ? & ? & ? & ? & ? & ? & ?). subst. 
        destruct H9.
        edestruct IHeval2 as (? & ? & [?]).
        { destruct H2 as [i1]. constructor; eauto.
          rewrite mkApps_app.
          eapply erases_mkApps. instantiate(1:=EAst.tBox).
          constructor. 
          eapply isErasable_Proof.
          eapply tCoFix_no_Type in i1; auto.
          pose proof i1 as X0'. destruct X0' as [tyapp [u [Htyapp Hu]]].
          eapply Is_proof_ty; eauto.
          eapply unfold_cofix_type; eauto.
          move: e. rewrite -closed_unfold_cofix_cunfold_eq // /unfold_cofix e0.
          intros e; eapply e. eauto. }
        { destruct (declared_inductive_inj decli'' decli); subst.
          econstructor; eauto. }
        destruct H2.
        eapply tCoFix_no_Type in X0; auto.
        move: (eval_to_mkApps_tBox_inv _ _ _ H1). intros ->. depelim H8.
        rewrite -> app_nil_r in *.
        exists x0; split; [|constructor]; auto.
        eapply eval_case_eval_inv_discr; tea.
      -- destruct H9.
        destruct He as [f' [L' [-> [hcof hl']]]].
        have clfix' : ELiftSubst.closed f'.
        { now eapply erases_closed in hcof; tea. }
        depelim hcof.
        { eapply All2_nth_error_Some in X0 as X'; tea.
          destruct X' as [t' [nth' [bn [rar eb]]]].
          specialize (IHeval2 (E.tCase (ip, ci_npar ip) 
            (E.mkApps (ELiftSubst.subst0 (EGlobalEnv.cofix_subst mfix') (E.dbody t')) L') brs')).
          forward IHeval2.
          econstructor; eauto.
          eapply erases_mkApps.
          move: e0 e. rewrite -closed_unfold_cofix_cunfold_eq //.
          unfold unfold_cofix. intros hnth; rewrite hnth. intros [=].
          subst fn narg.
          eapply All_nth_error in a0 as a'; tea.
          eapply erases_subst0. eauto. 2:eauto. pcuic. all:tea.
          { rewrite app_context_nil_l. eapply subslet_cofix_subst; eauto.
            econstructor; eauto. }
          {eapply All2_from_nth_error.
            erewrite cofix_subst_length, EGlobalEnv.cofix_subst_length, All2_length; eauto.
            intros.
            rewrite cofix_subst_nth in H3. now rewrite cofix_subst_length in H2.
            rewrite ecofix_subst_nth in H8. rewrite cofix_subst_length in H2.
            erewrite <- All2_length; eauto.
            invs H3; invs H8.
            erewrite All2_length; eauto. }
          destruct IHeval2 as [v' [Hv' [ev]]].
          { econstructor; eauto.
            eapply erases_deps_eval in Hed. 2:tea.
            apply erases_deps_mkApps_inv in Hed as (edcofix & edargs).
            depelim edcofix.
            apply erases_deps_mkApps; [|now eauto].
            apply erases_deps_subst.
            - now apply Forall_All, Forall_erases_deps_cofix_subst; eauto.
            - now eapply nth_error_forall in H2; eauto. }
          exists v'. split => //. split.
          eapply Ee.eval_cofix_case; tea.
          rewrite /EGlobalEnv.cunfold_cofix nth' //. f_equal.
          f_equal.
          rewrite -(Ee.closed_cofix_substl_subst_eq (idx:=idx)) //. }
        { eapply eval_to_mkApps_tBox_inv in H1 as H'; subst L'; cbn in *. depelim hl'.
          edestruct IHeval1 as (? & ? & [?]); tea.
          pose proof (Ee.eval_deterministic H1 H3). subst x0.
          eapply erases_deps_eval in Hed; tea.
          specialize (IHeval2 (E.tCase (ip, ci_npar ip) E.tBox brs')).
          forward IHeval2.
          econstructor; eauto. cbn.
          move: e0 e. rewrite -closed_unfold_cofix_cunfold_eq //.
          unfold unfold_cofix. intros hnth; rewrite hnth. intros [=].
          subst fn narg.
          constructor.
          eapply isErasable_unfold_cofix; tea.
          destruct IHeval2 as [v' [Hv' [ev]]].
          { econstructor; eauto. }
          exists v'. split => //. split.
          eapply eval_case_eval_inv_discr; tea. } 
          
        -- eapply wcbeval_red in Heval; tea.
           eapply subject_reduction_eval. 2:tea. eauto.
                   
    * depelim Hed.
      exists E.tBox. split; repeat constructor; auto.
      assert (PCUICReduction.red Σ [] (tCase ip p discr brs) res).
      eapply wcbeval_red in Heval; tea.
      now eapply isErasable_red.

  - assert (Hty' := Hty).
    eapply inversion_Proj in Hty' as (? & ? & ? & ? & [] & ? & ? & ? & e0 & e1); auto.
    pose proof (t0' := t0).
    pose proof (subject_closed t0) as cldiscr.
    assert(clcof : PCUICAst.closedn 0 (mkApps (tCoFix mfix idx) args)).
    { eapply eval_closed; tea; eauto. }
    move: clcof; rewrite closedn_mkApps => /andP[] clcofix clargs.
    eapply subject_reduction_eval in t0 as t0''; tea.
    eapply inversion_mkApps in t0'' as (? & ? & ?).
    eapply type_tCoFix_inv in t1 as t1'; eauto.
    destruct_sigma t1'; auto.
    eapply inversion_CoFix in t1; destruct_sigma t1.
    destruct p0 as [[hnth wfcof] hdef].
    eapply PCUICSpine.typing_spine_strengthen in t2; eauto.
    2:{ now eapply validity. }
    assert(Hty' := Hty).
    eapply subject_reduction in Hty'. 2:auto.
    2:{ etransitivity. eapply PCUICReduction.red_proj_c.
        eapply wcbeval_red; tea.
        constructor. eapply PCUICReduction.red_cofix_proj. eauto.
        rewrite closed_unfold_cofix_cunfold_eq; eauto. }
    specialize (IHeval2 _ Hty').
    specialize (IHeval1 _ t0).
    invs He.
    * depelim Hed.
      rename H0 into decli. rename H1 into decli'.
      rename H2 into er. rename H3 into H2.
      rename H4 into H0.
      destruct (declared_inductive_inj d decli') as [<- <-].
      destruct (IHeval1 _ H6 Hed) as [dv' [? []]].
      eapply erases_mkApps_inv in H1 as []; eauto.
      3:{ eapply subject_reduction_eval. 2:tea. eauto. }
      { destruct H1 as (? & ? & ? & ? & ? & ? & ? & ?). subst.
        destruct H4.
        eapply eval_to_mkApps_tBox_inv in H3 as H'. subst. depelim H8.
        edestruct IHeval2 as (? & ? & [?]).
        { constructor; eauto.
          instantiate(1:=EAst.tBox).
          constructor.
          eapply isErasable_Proof.
          eapply tCoFix_no_Type in X; auto.
          pose proof X as X0'. destruct X0' as [tyapp [u [Htyapp Hu]]].
          eapply Is_proof_ty; eauto.
          move: e. rewrite -closed_unfold_cofix_cunfold_eq // /unfold_cofix e2.
          intros [= <- <-].
          eapply unfold_cofix_type; eauto.
          2:{ unfold unfold_cofix; erewrite e2. reflexivity. }
          now rewrite app_nil_r. }
        { eapply erases_deps_eval in Hed. 2:tea.
          apply erases_deps_mkApps_inv in Hed as (_ & edargs).
          econstructor; eauto. constructor. }
        exists x1; split; [|constructor]; auto.
        eapply eval_proj_eval_inv_discr; tea. }
      { destruct H1 as [f' [L' [-> [hcof hl']]]].
        have clfix' : ELiftSubst.closed f'.
        { now eapply erases_closed in hcof; tea. }
        depelim hcof.
        { eapply All2_nth_error_Some in X as X'; tea.
          destruct X' as [t' [nth' [bn [rar eb]]]].
          specialize (IHeval2 (E.tProj p
            (E.mkApps (ELiftSubst.subst0 (EGlobalEnv.cofix_subst mfix') (E.dbody t')) L'))).
          forward IHeval2.
          econstructor; eauto.
          eapply erases_mkApps.
          move: hnth e. rewrite -closed_unfold_cofix_cunfold_eq //.
          unfold unfold_cofix. intros hnth'; rewrite hnth'. intros [=].
          subst fn narg. rewrite hnth' in e2. noconf e2.
          eapply All_nth_error in a0 as a'; tea.
          eapply erases_subst0. eauto. 2:eauto. pcuic. all:tea.
          { rewrite app_context_nil_l. eapply subslet_cofix_subst; eauto.
            econstructor; eauto. }
          {eapply All2_from_nth_error.
            erewrite cofix_subst_length, EGlobalEnv.cofix_subst_length, All2_length; eauto.
            intros.
            rewrite cofix_subst_nth in H4. now rewrite cofix_subst_length in H1.
            rewrite ecofix_subst_nth in H7. rewrite cofix_subst_length in H1.
            erewrite <- All2_length; eauto.
            invs H4; invs H7.
            erewrite All2_length; eauto. }
          destruct IHeval2 as [v' [Hv' [ev]]].
          { econstructor; eauto.
            eapply erases_deps_eval in Hed. 2:tea.
            apply erases_deps_mkApps_inv in Hed as (edcofix & edargs).
            depelim edcofix.
            apply erases_deps_mkApps; [|now eauto].
            apply erases_deps_subst.
            - now apply Forall_All, Forall_erases_deps_cofix_subst; eauto.
            - now eapply nth_error_forall in H1; eauto. }
          exists v'. split => //. split.
          eapply Ee.eval_cofix_proj; tea.
          rewrite /EGlobalEnv.cunfold_cofix nth' //. f_equal.
          f_equal.
          rewrite -(Ee.closed_cofix_substl_subst_eq (idx:=idx)) //. }
        { eapply eval_to_mkApps_tBox_inv in H3 as H'; subst L'; cbn in *. depelim hl'.
          edestruct IHeval1 as (? & ? & [?]); tea.
          pose proof (Ee.eval_deterministic H3 H4). subst x0.
          eapply erases_deps_eval in Hed; tea.
          specialize (IHeval2 (E.tProj p E.tBox)).
          forward IHeval2.
          econstructor; eauto. cbn.
          move: hnth e. rewrite -closed_unfold_cofix_cunfold_eq //.
          unfold unfold_cofix. intros hnth; rewrite hnth. intros [=].
          subst fn narg.
          constructor.
          eapply isErasable_unfold_cofix; tea.
          destruct IHeval2 as [v' [Hv' [ev]]].
          { econstructor; eauto. }
          exists v'. split => //. split.
          eapply eval_proj_eval_inv_discr; tea. }
      } 
    
    * depelim Hed.
      exists E.tBox. split; repeat constructor; auto.
      assert (PCUICReduction.red Σ [] (tProj p discr) res).
      eapply wcbeval_red in H0; tea.
      etransitivity; tea.
      etransitivity. eapply PCUICReduction.red_proj_c.
      eapply wcbeval_red; tea.
      constructor. eapply PCUICReduction.red_cofix_proj.
      move: e. rewrite closed_unfold_cofix_cunfold_eq //. intros e; exact e.
      now eapply isErasable_red.
  
    * eauto.

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
      eapply subject_closed in Hf; auto.
      eapply wcbeval_red; eauto.
      eapply subject_closed in Ha; auto.
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
        Unshelve. all: repeat econstructor.      
Qed.

(* Print Assumptions erases_correct. *)

Lemma erases_global_closed_env {Σ : global_env} Σ' : wf Σ -> erases_global Σ Σ' -> closed_env Σ'.
Proof.
  destruct Σ as [univs Σ]; cbn in *.
  intros [onu wf] er; cbn in *.
  move: wf. red in er; cbn in er.
  induction er; intros wf.
  - constructor.
  - cbn. destruct cb' as [[]].
    cbn in *. depelim wf. 
    rewrite [forallb _ _](IHer wf) andb_true_r.
    red in H. destruct cb as [ty []]; cbn in *.
    unshelve eapply PCUICClosedTyp.subject_closed in o0. cbn. split; auto.
    eapply erases_closed in H; tea. elim H.
    cbn. apply IHer. now depelim wf.
  - depelim wf.
    cbn. apply IHer, wf.
Qed.

Lemma erases_global_decls_fresh univs {Σ : global_declarations} kn Σ' : fresh_global kn Σ -> erases_global_decls univs Σ Σ' -> EGlobalEnv.fresh_global kn Σ'.
Proof.
  induction 2; constructor; eauto; now depelim H.
Qed.

Import EWellformed.

Lemma erases_global_wf_glob {Σ : global_env} Σ' : wf Σ -> erases_global Σ Σ' -> @wf_glob all_env_flags Σ'.
Proof.
  destruct Σ as [univs Σ]; cbn in *.
  intros [onu wf] er; cbn in *.
  move: wf. red in er; cbn in er.
  induction er; intros wf.
  - constructor.
  - cbn. depelim wf.
    constructor; eauto.
    2:eapply erases_global_decls_fresh; tea.
    cbn. red in H.
    do 2 red in o0.
    destruct (cst_body cb).
    destruct (E.cst_body cb') => //. cbn.
    set (Σ'' := ({| universes := _ |}, _)) in *.
    assert (PCUICTyping.wf_ext Σ'').
    { split => //. }
    epose proof (erases_wellformed (Σ:=Σ'') (Γ := []) (a:=t)).
    forward H0. now eexists.
    specialize (H0 H Σ'). eapply H0.
    eapply erases_global_all_deps; tea. split => //.
    destruct (E.cst_body cb') => //. 
  - depelim wf.
    constructor; eauto.
    eapply erases_global_decls_fresh; tea.
Qed.
