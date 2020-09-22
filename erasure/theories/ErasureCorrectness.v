(* Distributed under the terms of the MIT license. *)

From Coq Require Import Bool String List Program.Basics Program.Tactics ZArith.
From MetaCoq.Template Require Import config utils monad_utils.
From MetaCoq.Erasure Require Import ELiftSubst ETyping EWcbvEval Extract Prelim
     ESubstitution EInversion EArities.
From MetaCoq.PCUIC Require Import PCUICTyping PCUICAst PCUICAstUtils
  PCUICWeakening PCUICSubstitution PCUICArities
  PCUICWcbvEval PCUICSR  PCUICInversion
  PCUICUnivSubstitution PCUICElimination PCUICCanonicity
  PCUICUnivSubst PCUICWeakeningEnv PCUICCumulativity.

Require Import Equations.Prop.DepElim.
Require Import ssreflect.
Local Open Scope string_scope.
Set Asymmetric Patterns.
Local Set Keyed Unification.

Import MonadNotation.

Require Import Lia.

Module PA := PCUICAst.
Module P := PCUICWcbvEval.

Local Existing Instance config.extraction_checker_flags.

(** ** Prelim on arities and proofs *)

Lemma isArity_subst_instance u T :
  isArity T ->
  isArity (PCUICUnivSubst.subst_instance_constr u T).
Proof.
  induction T; cbn; intros; tauto.
Qed.

Lemma wf_ext_wk_wf {cf:checker_flags} Σ : wf_ext_wk Σ -> wf Σ.
Proof. intro H; apply H. Qed.

Hint Resolve wf_ext_wk_wf : core.

Lemma isErasable_subst_instance (Σ : global_env_ext) Γ T univs u :
  wf_ext_wk Σ ->  wf_local Σ Γ ->
  wf_local (Σ.1, univs) (PCUICUnivSubst.subst_instance_context u Γ) ->
  isErasable Σ Γ T ->
  sub_context_set (monomorphic_udecl Σ.2) (global_ext_context_set (Σ.1, univs)) ->
  consistent_instance_ext (Σ.1,univs) (Σ.2) u ->
  isErasable (Σ.1,univs) (PCUICUnivSubst.subst_instance_context u Γ) (PCUICUnivSubst.subst_instance_constr u T).
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
      * now eapply is_prop_subst_instance.
Qed.

(** * Correctness of erasure  *)

Notation "Σ |-p s ▷ t" := (eval Σ s t) (at level 50, s, t at next level) : type_scope.
Notation "Σ ⊢ s ▷ t" := (Ee.eval Σ s t) (at level 50, s, t at next level) : type_scope.

(** ** Erasure is stable under context conversion *)

Lemma Is_type_conv_context (Σ : global_env_ext) (Γ : context) t (Γ' : context) :
  wf Σ -> wf_local Σ Γ -> wf_local Σ Γ' ->
  PCUICContextConversion.conv_context Σ Γ Γ' -> isErasable Σ Γ t -> isErasable Σ Γ' t.
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
      PCUICContextConversion.context_relation (PCUICContextConversion.conv_decls Σ) Γ Γ' ->
      forall Γ0 : context, wf_local Σ Γ' -> wf_local_rel Σ Γ Γ0 -> wf_local_rel Σ Γ' Γ0.
Proof.
  intros Σ wfΣ Γ Γ' X1 Γ0 ? w0. induction w0.
  - econstructor.
  - econstructor; eauto. cbn in *.
    destruct t0. exists x. eapply PCUICContextConversion.context_conversion with (Γ ,,, Γ0); eauto.
    eapply conv_context_app; eauto.
    eapply typing_wf_local; eauto.
    eapply PCUICSafeChecker.wf_local_app_inv; eauto.
  - econstructor; eauto.
    + cbn in *.
      destruct t0. exists x. eapply PCUICContextConversion.context_conversion with (Γ ,,, Γ0); eauto.
      eapply conv_context_app; eauto.
      eapply typing_wf_local; eauto.
      eapply PCUICSafeChecker.wf_local_app_inv; eauto.
    + cbn in *. eapply PCUICContextConversion.context_conversion with (Γ ,,, Γ0); eauto.
      eapply conv_context_app; eauto.
      eapply typing_wf_local; eauto.
      eapply PCUICSafeChecker.wf_local_app_inv; eauto.
Qed.

Hint Resolve Is_type_conv_context : core.

Lemma erases_context_conversion :
  env_prop
  (fun (Σ : PCUICAst.global_env_ext) (Γ : PCUICAst.context) (t T : PCUICAst.term) =>
      forall Γ' : PCUICAst.context,
        PCUICContextConversion.conv_context Σ Γ Γ' ->
        wf_local Σ Γ' ->
        forall t', erases Σ Γ t t' -> erases Σ Γ' t t')
  (fun Σ Γ wfΓ => wf_local Σ Γ)
        .
Proof.
  apply typing_ind_env; intros Σ wfΣ Γ wfΓ; intros **; rename_all_hyps; auto.
  all: match goal with [ H : erases _ _ ?a _ |- ?G ] => tryif is_var a then idtac else inv H end.
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
    eapply All2_All_left in X3. 2:{ idtac. intros ? ? [[[? e] ?] ?]. exact e. }

    eapply All2_impl. eapply All2_All_mix_left.
    all: firstorder.
  - econstructor.

    eapply All2_impl. eapply All2_All_mix_left. eassumption. eassumption.
    intros. cbn in *.
    decompose [prod] X2. intuition auto.
    eapply b0.
    subst types.
    eapply conv_context_app; auto. eapply typing_wf_local; eassumption.
    eapply typing_wf_local in a1. subst types.
    2:eauto.

    eapply All_local_env_app_inv.
    eapply All_local_env_app in a1. intuition auto.

    (* clear -wfΣ X2 a2 b4 X1. *)
    eapply All_local_env_impl; eauto. simpl; intros.
    destruct T. simpl in *.
    eapply PCUICContextConversion.context_conversion with (Γ ,,, Γ0); eauto.
    eapply conv_context_app; auto. eapply typing_wf_local; eauto.
    eapply typing_wf_local in X3.
    eapply PCUICSafeChecker.wf_local_app_inv.
    eauto. eapply wf_local_rel_local in X3.
    eapply wf_local_rel_app in X3 as []. rewrite app_context_nil_l in w0.


    eapply wf_local_rel_conv; eauto.
    destruct X3. exists x0.
    eapply PCUICContextConversion.context_conversion with (Γ ,,, Γ0); eauto.
    eapply conv_context_app; auto. eapply typing_wf_local; eauto.

    eapply typing_wf_local in t0.
    eapply PCUICSafeChecker.wf_local_app_inv.
    eauto. eapply wf_local_rel_local in t0.
    eapply wf_local_rel_app in t0 as []. rewrite app_context_nil_l in w0.
    eapply wf_local_rel_conv; eauto.
  - econstructor.

    eapply All2_impl. eapply All2_All_mix_left. eassumption. eassumption.
    intros. cbn in *.
    decompose [prod] X2. intuition auto.
    eapply b0.
    subst types.
    eapply conv_context_app; auto. eapply typing_wf_local; eassumption.
    eapply typing_wf_local in a0. subst types.
    2:eauto.

    eapply All_local_env_app_inv.
    eapply All_local_env_app in a0. intuition auto.

    (* clear -wfΣ X2 a2 b4 X1. *)
    eapply All_local_env_impl; eauto. simpl; intros.
    destruct T. simpl in *.
    eapply PCUICContextConversion.context_conversion with (Γ ,,, Γ0); eauto.
    eapply conv_context_app; auto. eapply typing_wf_local; eauto.
    eapply typing_wf_local in X3.
    eapply PCUICSafeChecker.wf_local_app_inv.
    eauto. eapply wf_local_rel_local in X3.
    eapply wf_local_rel_app in X3 as []. rewrite app_context_nil_l in w0.


    eapply wf_local_rel_conv; eauto.
    destruct X3. exists x0.
    eapply PCUICContextConversion.context_conversion with (Γ ,,, Γ0); eauto.
    eapply conv_context_app; auto. eapply typing_wf_local; eauto.

    eapply typing_wf_local in t0.
    eapply PCUICSafeChecker.wf_local_app_inv.
    eauto. eapply wf_local_rel_local in t0.
    eapply wf_local_rel_app in t0 as []. rewrite app_context_nil_l in w0.
    eapply wf_local_rel_conv; eauto.
Qed.

(** ** Erasure is stable under substituting universe constraints  *)

Lemma fix_context_subst_instance:
  forall (mfix : list (BasicAst.def term)) (u : Instance.t),
    map (map_decl (PCUICUnivSubst.subst_instance_constr u))
        (PCUICLiftSubst.fix_context mfix) =
    PCUICLiftSubst.fix_context
      (map
         (map_def (PCUICUnivSubst.subst_instance_constr u)
                  (PCUICUnivSubst.subst_instance_constr u)) mfix).
Proof.
  intros mfix. unfold PCUICLiftSubst.fix_context. intros.
  rewrite map_rev.
  rewrite mapi_map.
  rewrite map_mapi. f_equal. eapply mapi_ext. intros. cbn.
  unfold map_decl. cbn. unfold vass.
  rewrite PCUICUnivSubst.lift_subst_instance_constr. reflexivity.
Qed.



Lemma erases_subst_instance_constr0
  : env_prop (fun Σ Γ t T => wf_ext_wk Σ ->
                           forall t' u univs,
                             wf_local (Σ.1, univs) (PCUICUnivSubst.subst_instance_context u Γ) ->
sub_context_set (monomorphic_udecl Σ.2) (global_ext_context_set (Σ.1, univs)) ->
      consistent_instance_ext (Σ.1,univs) (Σ.2) u ->
    Σ ;;; Γ |- t ⇝ℇ t' ->
    (Σ.1,univs) ;;; (PCUICUnivSubst.subst_instance_context u Γ) |- PCUICUnivSubst.subst_instance_constr u t ⇝ℇ t')
    (fun Σ Γ wfΓ => wf_local Σ Γ).
Proof.
  apply typing_ind_env; intros; cbn -[PCUICUnivSubst.subst_instance_constr] in *; auto.
  all: match goal with [ H : erases _ _ ?a _ |- ?G ] => tryif is_var a then idtac else inv H end.
  all: try now (econstructor; eauto using isErasable_subst_instance).
  - cbn. econstructor.
    eapply H0 in X2; eauto.
    econstructor. eauto. cbn. econstructor.
    eapply typing_subst_instance in X0; eauto. apply snd in X0.
    cbn in X0. refine (X0 _ _ _ _ _); eauto.
  - cbn. econstructor.
    eapply H0 in X3; eauto.
    eapply H1 in X3; eauto. exact X3.
    econstructor. eauto. cbn. econstructor.
    eapply typing_subst_instance in X0; eauto. apply snd in X0.
    cbn in X0. refine (X0 _ _ _ _ _); eauto.
    cbn. eapply typing_subst_instance in X1; eauto. apply snd in X1.
    cbn in X1. refine (X1 _ _ _ _ _); eauto.
  - cbn. econstructor; eauto.
    eapply All2_map_left.
    eapply All2_impl. eapply All2_All_mix_left.
    eapply All2_All_left. exact X3. intros ? ? [[[? e] ?] ?].
    exact e. exact X6.
    intros; cbn in *. destruct H. destruct p0. split; eauto.
  - assert (Hw :  wf_local (Σ.1, univs) (subst_instance_context u (Γ ,,, types))).
    { (* rewrite subst_instance_context_app. *)
      assert(All (fun d => isType Σ Γ (dtype d)) mfix).
      eapply (All_impl X0); firstorder. 
      eapply All_mfix_wf in X5; auto. subst types.
      
      revert X5. clear - wfΣ wfΓ H2 H3 X2 X3.
      induction 1.
      - eauto.
      - cbn. econstructor; eauto. cbn in *.
        destruct t0 as (? & ?). eexists.
        cbn. eapply typing_subst_instance in t0; eauto. apply snd in t0. cbn in t0.
        rapply t0; eauto.
      - cbn. econstructor; eauto. cbn in *.
        destruct t0 as (? & ?). eexists.
        cbn. eapply typing_subst_instance in t0; eauto. apply snd in t0.
        rapply t0; eauto.
        cbn in *. eapply typing_subst_instance in t1; eauto.
        apply snd in t1. rapply t1. all:eauto.
    }

    cbn. econstructor; eauto.
    eapply All2_map_left.
    eapply All2_impl. eapply All2_All_mix_left. eapply X1.
    exact X4.
    intros; cbn in *. destruct X5. destruct p0. destruct p0.
    destruct p. destruct p. repeat split; eauto.
    eapply e2 in e1.
    unfold PCUICUnivSubst.subst_instance_context in *.
    unfold map_context in *. rewrite  ->map_app in *. subst types. 2:eauto.
    eapply erases_ctx_ext. eassumption. unfold app_context.
    f_equal.
    eapply fix_context_subst_instance. all: eauto.

  - assert (Hw :  wf_local (Σ.1, univs) (subst_instance_context u (Γ ,,, types))).
  { (* rewrite subst_instance_context_app. *)
    assert(All (fun d => isType Σ Γ (dtype d)) mfix).
    eapply (All_impl X0); firstorder. 
    eapply All_mfix_wf in X5; auto. subst types.
    
    revert X5. clear - wfΣ wfΓ H2 H3 X2 X3.
    induction 1.
    - eauto.
    - cbn. econstructor; eauto. cbn in *.
      destruct t0 as (? & ?). eexists.
      cbn. eapply typing_subst_instance in t0; eauto. apply snd in t0. cbn in t0.
      rapply t0; eauto.
    - cbn. econstructor; eauto. cbn in *.
      destruct t0 as (? & ?). eexists.
      cbn. eapply typing_subst_instance in t0; eauto. apply snd in t0.
      rapply t0; eauto.
      cbn in *. eapply typing_subst_instance in t1; eauto.
      apply snd in t1. rapply t1. all:eauto.
  }

  cbn. econstructor; eauto.
  eapply All2_map_left.
  eapply All2_impl. eapply All2_All_mix_left. eapply X1.
  exact X4.
  intros; cbn in *. destruct X5. destruct p0. destruct p0.
  destruct p. repeat split; eauto.
  eapply e2 in e1.
  unfold PCUICUnivSubst.subst_instance_context in *.
  unfold map_context in *. rewrite -> map_app in *. subst types. 2:eauto.
  eapply erases_ctx_ext. eassumption. unfold app_context.
  f_equal.
  eapply fix_context_subst_instance. all: eauto.
Qed.

Lemma erases_subst_instance_constr :
  forall Σ : global_env_ext, wf_ext_wk Σ ->
  forall Γ, wf_local Σ Γ ->
  forall t T, Σ ;;; Γ |- t : T ->
    forall t' u univs,
  wf_local (Σ.1, univs) (PCUICUnivSubst.subst_instance_context u Γ) ->
sub_context_set (monomorphic_udecl Σ.2) (global_ext_context_set (Σ.1, univs)) ->      consistent_instance_ext (Σ.1,univs) (Σ.2) u ->
    Σ ;;; Γ |- t ⇝ℇ t' ->
    (Σ.1,univs) ;;; (PCUICUnivSubst.subst_instance_context u Γ) |- PCUICUnivSubst.subst_instance_constr u t ⇝ℇ t'.
Proof.
  intros Σ X Γ X0 t T X1 t' u univs X2 H H0 H1.
  unshelve eapply (erases_subst_instance_constr0 Σ _ Γ _ _ _); tea; eauto.
Qed.

Lemma erases_subst_instance'' Σ φ Γ t T u univs t' :
  wf_ext_wk (Σ, univs) ->
  (Σ, univs) ;;; Γ |- t : T ->
  sub_context_set (monomorphic_udecl univs) (global_context_set Σ) ->
  consistent_instance_ext (Σ, φ) univs u ->
  (Σ, univs) ;;; Γ |- t ⇝ℇ t' ->
  (Σ, φ) ;;; subst_instance_context u Γ
            |- subst_instance_constr u t ⇝ℇ  t'.
Proof.
  intros X X0 X1. intros.
  eapply (erases_subst_instance_constr (Σ, univs)); tas.
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
   Σ ;;; subst_instance_context u Γ
            |- subst_instance_constr u t ⇝ℇ  t'.
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
  - inv H4. right. repeat eexists; eauto.
  - left. split; eauto. econstructor; eauto.
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
  (exists L1 L2 L2', L = (L1 ++ L2)%list /\
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

(** ** Global erasure  *)

Lemma lookup_env_erases (Σ : global_env_ext) c decl Σ' :
  wf Σ ->
  erases_global Σ Σ' ->
  lookup_env (fst Σ) c = Some (ConstantDecl decl) ->
  exists decl', ETyping.lookup_env Σ' c = Some (EAst.ConstantDecl decl') /\
           erases_constant_body (Σ.1, cst_universes decl)  decl decl'.
Proof.
  unfold erases_global. destruct Σ; simpl.
  intros. induction H; cbn in *.
  - inv H0.
  - unfold eq_kername in *; destruct ?.
    + inv H0.
      exists cb'. split; eauto. unfold erases_constant_body in *.
      destruct ?. destruct ?.
      * destruct decl.
        eapply (erases_extends (Σ, _)); simpl; eauto. now inv X.
        2:eexists [_]; simpl; eauto. cbn in *.
        inv X. cbn in X1.
        eassumption.
      * eassumption.
      * destruct ?; tauto.
    + edestruct IHerases_global_decls as (decl' & ? & ?).
      eapply wf_extends.
      eassumption. now eexists [_]. eauto.
      destruct decl. cbn in *.
      exists decl'. split. eauto.
      unfold erases_constant_body in *. clear H. destruct ?. destruct ?.
      eapply (@erases_extends (_, _)). 6: eassumption.
        eapply wf_extends.
        eassumption. now eexists [_]. eauto.
        eapply (declared_constant_inv Σ) in H0; eauto.
        unfold on_constant_decl in H0. rewrite E0 in H0. unfold lift_typing in H0. exact H0.
        eapply weaken_env_prop_typing. eapply wf_extends. eauto.
        eexists [_]. reflexivity. eapply wf_extends. eauto. now eexists [_].
        eauto. now eexists [_].
      * tauto.
      * destruct ?; tauto.
  - unfold eq_kername in *; destruct ?.
    + inv H0.
    + edestruct IHerases_global_decls as (decl' & ? & ?).
      eapply wf_extends.
      eassumption. now eexists [_]. eauto.
      exists decl'. split. eauto.
      unfold erases_constant_body in *. clear H. destruct ?. destruct ?.
      * eapply (@erases_extends (_,_)). 5: eassumption.
        eapply wf_extends.
        eassumption. now eexists [_]. eauto.
        eapply (declared_constant_inv Σ) in H0; eauto.
        unfold on_constant_decl in H0. rewrite E0 in H0. unfold lift_typing in H0. eassumption.
        eapply weaken_env_prop_typing. eapply wf_extends. eauto.
        eexists [_]. reflexivity. eapply wf_extends. eauto. now eexists [_].
        eauto. now eexists [_].
      * tauto.
      * destruct ?; tauto.
Qed.
(** ** The correctness proof  *)

Record extraction_pre (Σ : global_env_ext) : Type
  := Build_extraction_pre
  { extr_env_axiom_free' : axiom_free (fst Σ);
    extr_env_wf' : wf_ext Σ }.

Hint Constructors PCUICWcbvEval.eval erases : core.
Arguments extr_env_wf' {Σ}.
Arguments extr_env_axiom_free' {Σ}.

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
    cbn. rewrite PCUICInductives.fst_decompose_app_rec.
    unfold EisConstruct_app in *.
    cbn. rewrite fst_decompose_app_rec. eassumption.
Qed.

Lemma is_FixApp_erases Σ Γ t t' :
  Σ;;; Γ |- t ⇝ℇ t' ->
  negb (isFixApp t) -> negb (Ee.isFixApp t').
Proof.
  induction 1; cbn; try congruence.
  - unfold isFixApp in *. clear IHerases2.
    cbn. rewrite PCUICInductives.fst_decompose_app_rec.
    unfold Ee.isFixApp in *.
    cbn. rewrite fst_decompose_app_rec. eassumption.
Qed.

Lemma type_closed_subst {Σ t T} u : wf_ext Σ ->
  Σ ;;; [] |- t : T ->
  PCUICLiftSubst.subst1 t 0 u = PCUICCSubst.csubst t 0 u.
Proof.
  intros wfΣ tc.
  apply PCUICClosed.subject_closed in tc; auto.
  rewrite PCUICCSubst.closed_subst; auto.
Qed.

Lemma erases_closed Σ Γ  a e : PCUICLiftSubst.closedn #|Γ| a -> Σ ;;; Γ |- a ⇝ℇ e -> closedn #|Γ| e.
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
  - apply andb_and; split; eauto.
  - eapply andb_and; split; eauto.
    solve_all. destruct y ;  simpl in *; subst.
    unfold test_snd. simpl; eauto.
  - epose proof (All2_length _ _ X0).
    solve_all. destruct y ;  simpl in *; subst.
    unfold EAst.test_def; simpl; eauto.
    rewrite <-H. rewrite fix_context_length in b0.
    eapply b0. eauto. now rewrite app_length fix_context_length.
  - epose proof (All2_length _ _ X0).
    solve_all. destruct y ;  simpl in *; subst.
    unfold EAst.test_def; simpl; eauto.
    rewrite <-H. rewrite fix_context_length in b0.
    eapply b0. eauto. now rewrite app_length fix_context_length.
Qed.

Lemma eval_to_mkApps_tBox_inv Σ t argsv :
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
  epose proof (PCUICPrincipality.principal_typing _ wfΣ Hty Hty') as [C [Cty [Cty' Ht'']]].
  intros Ht'.
  exists ty', u; intuition auto.
  eapply PCUICValidity.validity in Hty; eauto.
  eapply PCUICValidity.validity in Hty'; eauto.
  eapply PCUICValidity.validity in Ht''; eauto.
  eapply PCUICElimination.cumul_prop1 in Cty; eauto.
  eapply PCUICElimination.cumul_prop2 in Cty'; eauto.
Qed.

Lemma Is_proof_app {Σ Γ t args ty} {wfΣ : wf_ext Σ} :
  Is_proof Σ Γ t -> 
  Σ ;;; Γ |- mkApps t args : ty ->
  Is_proof Σ Γ (mkApps t args).
Proof.
  intros [ty' [u [Hty [isp pu]]]] Htargs.
  eapply PCUICValidity.inversion_mkApps in Htargs as [A [Ht sp]].
  pose proof (PCUICValidity.validity_term wfΣ Hty).  
  pose proof (PCUICValidity.validity_term wfΣ Ht).  
  epose proof (PCUICPrincipality.principal_typing _ wfΣ Hty Ht) as [C [Cty [Cty' Ht'']]].
  eapply PCUICSpine.typing_spine_strengthen in sp; eauto.
  edestruct (sort_typing_spine _ _ _ u _ _ _ pu sp) as [u' [Hty' isp']].
  eapply PCUICElimination.cumul_prop1; eauto.
  eapply PCUICValidity.validity; eauto.
  exists ty, u'; split; auto.
  eapply PCUICGeneration.type_mkApps. 2:eauto. auto. auto.
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
  eapply PCUICGeneration.type_mkApps; eauto.
  pose proof a0 as a0'.
  eapply nth_error_all in a0'; eauto. simpl in a0'.
  eapply (substitution _ _ _ _ []) in a0'; eauto.
  2:{ eapply subslet_cofix_subst; pcuic.
      constructor; eauto. }
  rewrite PCUICLiftSubst.simpl_subst_k in a0'. now autorewrite with len.
  eapply a0'.
Qed.

Transparent PCUICParallelReductionConfluence.construct_cofix_discr.

Lemma erases_correct Σ t T t' v Σ' :
  extraction_pre Σ ->
  Σ;;; [] |- t : T ->
  Σ;;; [] |- t ⇝ℇ t' ->  
  erases_global Σ Σ' ->
  Σ |-p t ▷ v ->
  exists v', Σ;;; [] |- v ⇝ℇ v' /\ Σ' ⊢ t' ▷ v'.
Proof.
  intros pre Hty He Heg H.
  revert T Hty t' He.
  induction H; intros T Hty t' He; destruct pre as [axfree wfΣ].
  - assert (Hty' := Hty).
    assert (eval Σ (PCUICAst.tApp f a) res) by eauto.
    eapply inversion_App in Hty as (? & ? & ? & ? & ? & ?).
    inv He.

    + eapply IHeval1 in H4 as (vf' & Hvf' & He_vf'); eauto.
      eapply IHeval2 in H6 as (vu' & Hvu' & He_vu'); eauto.
      pose proof (subject_reduction_eval t0 H).
      eapply inversion_Lambda in X0 as (? & ? & ? & ? & ?).
      assert (Σ ;;; [] |- a' : t). {
          eapply subject_reduction_eval; eauto.
          eapply PCUICConversion.cumul_Prod_inv in c0 as [].
          econstructor. eassumption. eauto. eapply conv_sym in c0; eauto.
          now eapply conv_cumul. auto. auto. }
      assert (eqs := type_closed_subst b wfΣ X0).
      inv Hvf'.
      * assert (Σ;;; [] |- PCUICLiftSubst.subst1 a' 0 b ⇝ℇ subst1 vu' 0 t').
        eapply (erases_subst Σ [] [PCUICAst.vass na t] [] b [a'] t'); eauto.
        econstructor. econstructor. rewrite parsubst_empty. eassumption.
        rewrite eqs in H2.
        eapply IHeval3 in H2 as (v' & Hv' & He_v').
        -- exists v'. split; eauto.
           econstructor; eauto.
           rewrite ECSubst.closed_subst; auto.
           eapply erases_closed in Hvu'; auto.
           now eapply PCUICClosed.subject_closed in X0.
        -- rewrite <-eqs. eapply substitution0; eauto.
      * exists EAst.tBox. split.
        eapply Is_type_lambda in X1; eauto. destruct X1. econstructor.
        eapply (is_type_subst Σ [] [PCUICAst.vass na _] [] _ [a']) in X1 ; auto.
        cbn in X1.
        eapply Is_type_eval; try assumption.
        eauto. eapply H1. rewrite <-eqs. eassumption.
        all: eauto. econstructor. econstructor. rewrite parsubst_empty.
        eauto. econstructor. eauto. eauto.
      * auto.
    + exists EAst.tBox. split. 2:econstructor; eauto.
      econstructor.
      eapply Is_type_eval; eauto.
    + auto.
  - assert (Hty' := Hty).
    assert (Σ |-p tLetIn na b0 t b1 ▷ res) by eauto.
    eapply inversion_LetIn in Hty' as (? & ? & ? & ? & ? & ?); auto.
    inv He.     
    + eapply IHeval1 in H6 as (vt1' & Hvt2' & He_vt1'); eauto.
      assert (Hc : PCUICContextConversion.conv_context Σ ([],, vdef na b0 t) [vdef na b0' t]). {
        econstructor. econstructor. econstructor.
        eapply PCUICCumulativity.red_conv.
        now eapply wcbeval_red; eauto.
        reflexivity.
      }
      assert (Σ;;; [vdef na b0' t] |- b1 : x0). {
        cbn in *. eapply PCUICContextConversion.context_conversion. 3:eauto. all:cbn; eauto.
        econstructor. all: cbn; eauto. eapply subject_reduction_eval; auto. eauto. eauto.
      }
      assert (Σ;;; [] |- PCUICLiftSubst.subst1 b0' 0 b1 ⇝ℇ subst1 vt1' 0 t2'). {
        eapply (erases_subst Σ [] [PCUICAst.vdef na b0' t] [] b1 [b0'] t2'); eauto.
        enough (subslet Σ [] [PCUICLiftSubst.subst [] 0 b0'] [vdef na b0' t]).
        now rewrite parsubst_empty in X1.
        econstructor. econstructor.
        rewrite !parsubst_empty.
        eapply subject_reduction_eval; eauto.
        eapply erases_context_conversion. 3:eassumption.
        all: cbn; eauto.
        econstructor. all: cbn; eauto.
        eapply subject_reduction_eval; eauto.
      }
      pose proof (subject_reduction_eval t1 H).
      assert (eqs := type_closed_subst b1 _ X1).
      rewrite eqs in H1.
      eapply IHeval2 in H1 as (vres & Hvres & Hty_vres).
      2:{ rewrite <-eqs. eapply substitution_let; eauto. }
      exists vres. split. eauto. econstructor; eauto.
      enough (ECSubst.csubst vt1' 0 t2'  = t2' {0 := vt1'}) as ->; auto.
      eapply ECSubst.closed_subst. eapply erases_closed in Hvt2'; auto.
      eapply eval_closed. eauto. 2:eauto. now eapply PCUICClosed.subject_closed in t1.
    + exists EAst.tBox. split. 2:econstructor; eauto.
      econstructor. eapply Is_type_eval; eauto.

  - unfold erases_global in Heg.
    assert (Σ |-p tConst c u ▷ res) by eauto.
    eapply inversion_Const in Hty as (? & ? & ? & ? & ?); [|easy].
    inv He.
    + assert (isdecl' := isdecl).
      eapply lookup_env_erases in isdecl; eauto.
      destruct isdecl as (decl' & ? & ?).
      unfold erases_constant_body in *. rewrite -> e in *.
      destruct ?; try tauto. cbn in *.
      eapply declared_constant_inj in d; eauto; subst.
      edestruct IHeval.
      * cbn in *.
        assert (isdecl'' := isdecl').
        eapply PCUICWeakeningEnv.declared_constant_inv in isdecl'; eauto.
        2:eapply PCUICWeakeningEnv.weaken_env_prop_typing.
        unfold on_constant_decl in isdecl'. rewrite e in isdecl'. red in isdecl'.
        unfold declared_constant in isdecl''.
        eapply typing_subst_instance_decl with (Σ0 := Σ) (Γ := []); eauto.
        apply wfΣ.
      * assert (isdecl'' := isdecl').
        eapply PCUICWeakeningEnv.declared_constant_inv in isdecl'; eauto.
        unfold on_constant_decl in isdecl'. rewrite e in isdecl'. cbn in *.
        2:eapply PCUICWeakeningEnv.weaken_env_prop_typing.
        eapply erases_subst_instance_decl with (Σ := Σ) (Γ := []); eauto.
        apply wfΣ.
      * destruct H2. exists x0. split; eauto. econstructor; eauto.
    + exists EAst.tBox. split. econstructor.
      eapply Is_type_eval. 3: eassumption. eauto. eauto. eauto. econstructor. eauto.

  - destruct Σ as (Σ, univs).
    cbn in *.
    eapply axfree in isdecl. congruence.

  - assert (Hty' := Hty).
    assert (Σ |-p tCase (ind, pars) p discr brs ▷ res) by eauto.
    eapply inversion_Case in Hty' as [u' [args' [mdecl [idecl [ps [pty [btys 
                                    [? [? [? [? [? [_ [? [ht0 [? ?]]]]]]]]]]]]]]]]; auto.
    assert (Σ ;;; [] |- mkApps (tConstruct ind c u) args :  mkApps (tInd ind u') args').
    eapply subject_reduction_eval; eauto.
    eapply PCUICValidity.inversion_mkApps in X0 as (? & ? & ?); eauto.
    eapply inversion_Construct in t1 as (mdecl' & idecl' & cdecl & ? & ? & ? & ?); auto.
    assert (d1 := d0).
    destruct d0.
    edestruct (declared_inductive_inj H1 d). subst.
    pose proof (@length_of_btys ind mdecl' idecl' (firstn pars args') u' p).
    pose proof (length_map_option_out _ _ ht0) as lenbtys. simpl in lenbtys.
    rewrite H3 in lenbtys.

    inv He.
    + eapply IHeval1 in H11 as (v' & Hv' & He_v'); eauto.
      eapply erases_mkApps_inv in Hv' as [(? & ? & ? & ? & [] & ? & ? & ?) | (? & ? & ? & ? & ?)]; eauto.
      3: eapply subject_reduction_eval; eauto.
      * subst.

        eapply Is_type_app in X1; auto. destruct X1.
        2:{ rewrite mkApps_nested. eapply subject_reduction_eval; eauto. }
        rewrite mkApps_nested in X1.

        eapply tConstruct_no_Type in X1; auto.
        eapply H10 in X1 as []; eauto. 2: exists []; now destruct Σ.

        destruct (ind_ctors idecl'). cbn in H4. destruct c; inv H2.
        destruct l; cbn in *; try lia. destruct c as [ | []]; cbn in H2; inv H2.

        destruct btys as [ | ? []]; cbn in H3, lenbtys; try lia. clear H3 lenbtys H4.
        destruct H7.
        (* eapply H7 in d1. *) inv a. inv X0.
        inv X3. inv X4. destruct H7. destruct x3, y; cbn in *; subst.
        destruct X2. destruct p1; subst; cbn in *.
        destruct p0 as [narg bty]; simpl in *.

        edestruct (IHeval2) as (? & ? & ?).
        eapply subject_reduction. eauto. exact Hty.
        etransitivity.
        eapply PCUICReduction.red_case_c. eapply wcbeval_red; eauto.
        econstructor. econstructor.

        all:unfold iota_red in *. all:cbn in *.
        eapply erases_mkApps. eauto.
        instantiate (1 := repeat EAst.tBox _).
        eapply All2_Forall2.
        eapply All2_impl.
        eapply All2_All_mix_left. eassumption.
        2:{ intros. destruct X0. assert (y = EAst.tBox). exact y0. subst. econstructor.
            now eapply isErasable_Proof. }

        eapply All2_right_triv. 2: now rewrite repeat_length.
        now eapply All_repeat.

        (* destruct x4; cbn in e2; subst. destruct X2. destruct p0; cbn in e2; subst. cbn in *.  destruct y.  *)
        exists x3. split; eauto. eapply eval_iota_sing.  2:eauto.
        pose proof (Ee.eval_to_value _ _ _ He_v').
        eapply value_app_inv in H4. subst. eassumption.

        eapply wf_ext_wf in wfΣ.
        eapply tCase_length_branch_inv in wfΣ.
        2:{ eapply subject_reduction. eauto.
            exact Hty.
            eapply PCUICReduction.red_case_c. eapply wcbeval_red; eauto. }
        2: reflexivity.

        enough (#|skipn (ind_npars mdecl') (x0 ++ x1)| = narg) as <- by eauto.
        rewrite skipn_length; lia.
        
      * subst. unfold iota_red in *.
        destruct (nth_error brs c) eqn:Hnth.
        2:{ eapply nth_error_None in Hnth. erewrite All2_length in Hnth. 2:exact a.
            eapply nth_error_Some_length in H2. cbn in H2. lia. }
        rewrite <- nth_default_eq in *. unfold nth_default in *.
        rewrite -> Hnth in *.

        destruct (All2_nth_error_Some _ _ X0 Hnth) as (? & ? & ? & ?).
        destruct (All2_nth_error_Some _ _ a Hnth) as (? & ? & ? & ?).
         destruct p0, x3. cbn in *. subst.
        edestruct IHeval2 as (? & ? & ?).
        eapply subject_reduction. eauto. exact Hty.
        etransitivity.
        eapply PCUICReduction.red_case_c. eapply wcbeval_red. eauto.
        now eapply PCUICClosed.subject_closed in t0. eauto. eauto.

        etransitivity. constructor. constructor.
        unfold iota_red. rewrite <- nth_default_eq. unfold nth_default.
        rewrite Hnth. reflexivity.

        eapply erases_mkApps. eauto.
        eapply Forall2_skipn. eauto.
        inv H5.
        -- exists x3. split; eauto.
           econstructor. eauto. unfold ETyping.iota_red.
           rewrite <- nth_default_eq. unfold nth_default. rewrite e1. cbn. eauto.
        -- eapply Is_type_app in X1 as []; auto.
           2:{ eapply subject_reduction_eval. 2:eassumption. eauto. }

           eapply tConstruct_no_Type in X1; auto.
           eapply H10 in X1 as []; eauto. 2: exists []; now destruct Σ.

           destruct (ind_ctors idecl'). cbn in H5. destruct c; inv H2.
           destruct l; cbn in *; try lia. destruct c as [ | []]; cbn in H2; inv H2.

           destruct btys as [ | ? []]; cbn in e4; try discriminate.
           clear H5. destruct H8.
            inv a. inv X2. inv X3. inv X0. destruct H9. destruct x0, y; cbn in *; subst.
           inv X2. destruct p1. subst. destruct p0; cbn in *.
           destruct X4; subst n1. inv e1. simpl in *. inv Hnth. inv e4. cbn in *.

           edestruct (IHeval2) as (? & ? & ?).
           eapply subject_reduction. eauto. exact Hty.
           etransitivity.
           eapply PCUICReduction.red_case_c. eapply wcbeval_red. eauto.
           now eapply PCUICClosed.subject_closed in t0; eauto. eauto. eauto.
           etransitivity. constructor. constructor.
           unfold iota_red. rewrite <- nth_default_eq. reflexivity.

           eapply erases_mkApps. eauto.
           instantiate (1 := repeat EAst.tBox _).
           eapply All2_Forall2.
           eapply All2_impl.
           eapply All2_All_mix_left. eassumption.
           2:{ intros. destruct X0. assert (y = EAst.tBox). exact y0. subst. econstructor.
               now eapply isErasable_Proof. }

           eapply All2_right_triv. 2:now rewrite repeat_length.
           now eapply All_repeat.

           exists x0. split; eauto.
           eapply eval_iota_sing.
           pose proof (Ee.eval_to_value _ _ _ He_v').
           2:eauto. auto.
           apply value_app_inv in H8; subst x1.
           apply He_v'.
           enough (#|skipn (ind_npars mdecl') args| = n) as <- by eauto.

           eapply wf_ext_wf in wfΣ.
           eapply tCase_length_branch_inv in wfΣ.
           2:{ eapply subject_reduction. eauto.
               exact Hty.
               eapply PCUICReduction.red_case_c. eapply wcbeval_red; eauto. }
           2: reflexivity.

           enough (#|skipn (ind_npars mdecl') args| = n) as <- by eauto.
           rewrite skipn_length; lia.
    + exists EAst.tBox. split. econstructor.
      eapply Is_type_eval; eauto. econstructor; eauto.

  - pose (Hty' := Hty).
    eapply inversion_Proj in Hty' as (? & ? & ? & [] & ? & ? & ? & ? & ?); [|easy].
    inv He.

    + eapply IHeval1 in H5 as (vc' & Hvc' & Hty_vc'); eauto.
      eapply erases_mkApps_inv in Hvc'; eauto.
      2: eapply subject_reduction_eval; eauto.
      destruct Hvc' as [ (? & ? & ? & ? & [] & ? & ? & ?) | (? & ? & ? & ? & ?)]; subst.
      * exists EAst.tBox. split.

        eapply Is_type_app in X as []; eauto. 2:{ rewrite mkApps_nested. eapply subject_reduction_eval; eauto. }
        rewrite mkApps_nested in X.

        eapply tConstruct_no_Type in X; eauto. eapply H3 in X as [? []]; eauto.
        2: now destruct d. 2: now exists []; destruct Σ.

        econstructor.
        eapply Is_type_eval; eauto.
        eapply nth_error_all.
        erewrite nth_error_skipn. reflexivity. eassumption.
        eapply All_impl. assert (pars = ind_npars x0). destruct d as (? & ? & ?). now rewrite H7. subst.
        eassumption.
        eapply isErasable_Proof. eauto.

        eapply eval_proj_box.
        pose proof (Ee.eval_to_value _ _ _ Hty_vc').
        eapply value_app_inv in H1. subst. eassumption.
      * rename H3 into Hinf.
        eapply Forall2_nth_error_Some in H4 as (? & ? & ?); eauto.
        assert (Σ ;;; [] |- mkApps (tConstruct i 0 u) args : mkApps (tInd i x) x2).
        eapply subject_reduction_eval; eauto.
        eapply PCUICValidity.inversion_mkApps in X as (? & ? & ?); eauto.
        eapply typing_spine_inv in t2 as []; eauto.
        eapply IHeval2 in H3 as (? & ? & ?); eauto.
        inv H2.
        -- exists x8. split; eauto. econstructor. eauto.
           rewrite <- nth_default_eq. unfold nth_default. now rewrite H1.
        -- exists EAst.tBox. split.


           eapply Is_type_app in X as []; eauto. 2:{ eapply subject_reduction_eval; [|eauto]; eauto. }

           eapply tConstruct_no_Type in X. eapply Hinf in X as [? []]; eauto.
           2: now destruct d. 2: now exists []; destruct Σ.

           econstructor.
           eapply Is_type_eval; eauto.
           eapply nth_error_all.
           erewrite nth_error_skipn. reflexivity. eassumption.
           eapply All_impl. assert (pars = ind_npars x0). destruct d as (? & ? & ?). now rewrite H7. subst.
           eassumption.
           eapply isErasable_Proof. eauto.

           eapply eval_proj_box.
           pose proof (Ee.eval_to_value _ _ _ Hty_vc').
           eapply value_app_inv in H2. subst. eassumption.
    + exists EAst.tBox. split. econstructor.
      eapply Is_type_eval. 4: eassumption. all:eauto. econstructor. eauto.

  - assert (Hty' := Hty).
    assert (Hunf := H).
    assert (Hcon := H1).
    eapply inversion_App in Hty' as (? & ? & ? & ? & ? & ?); eauto.
    assert (Ht := t).
    eapply subject_reduction in t. 2:auto. 2:eapply wcbeval_red; eauto.
    assert (HT := t).
    apply PCUICValidity.inversion_mkApps in HT as (? & ? & ?); auto.
    assert (Ht1 := t1).
    apply inversion_Fix in t1 as Hfix; auto.
    destruct Hfix as (? & ? & ? & ? & ? & ? & ?).
    unfold cunfold_fix in e. rewrite e0 in e. inv e.
    depelim He; first last.
    
    + exists EAst.tBox. split; [|now constructor].
      econstructor.
      eapply Is_type_eval. 4:eapply X. eauto. eauto.
      eapply eval_fix; eauto.
      rewrite /cunfold_fix e0 //. congruence.
    + eapply IHeval1 in He1 as IH1; eauto.
      destruct IH1 as (er_stuck_v & er_stuck & ev_stuck).
      eapply IHeval2 in He2 as IH2; eauto.
      destruct IH2 as (er_argv & er_arg & ev_arg).
      eapply erases_mkApps_inv in er_stuck; eauto.
      destruct er_stuck as [(? & ? & ? & -> & ? & ? & ? & ->)|
                            (? & ? & -> & ? & ?)].
      { exists E.tBox.
        eapply eval_to_mkApps_tBox_inv in ev_stuck as ?; subst.
        cbn in *.
        split; [|eauto using Ee.eval].
        destruct H2.
        eapply (Is_type_app _ _ _ (x5 ++ [av])) in X as []; eauto; first last.
        - rewrite mkApps_nested app_assoc mkApps_snoc.
          eapply type_App; eauto.
          eapply subject_reduction; eauto.
          eapply wcbeval_red; eauto.
        - eapply erases_box.
          eapply Is_type_eval; auto. 2:eauto.
          rewrite -mkApps_nested /=.
          eapply eval_fix.
          rewrite mkApps_nested. eapply value_final.
          eapply eval_to_value; eauto.
          eapply value_final, eval_to_value; eauto.
          rewrite  /cunfold_fix e0 //. auto. auto.
          rewrite H3; eauto. auto. }

      inv H2.
      * assert (Hmfix' := X).
        eapply All2_nth_error_Some in X as (? & ? & ?); eauto.
        pose proof (closed_fix_substl_subst_eq (PCUICClosed.subject_closed _ t1) e0) as cls.
        destruct x3. cbn in *. subst.

        enough (Σ;;; [] ,,, PCUICLiftSubst.subst_context (fix_subst mfix) 0 []
                |- PCUICLiftSubst.subst (fix_subst mfix) 0 dbody
                ⇝ℇ subst (ETyping.fix_subst mfix') 0 (Extract.E.dbody x4)).
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
           eapply IHeval3 in H2 as (? & ? & ?); cbn; eauto; first last.
           { eapply subject_reduction. eauto. exact Hty.
             etransitivity.
             eapply PCUICReduction.red_app. eapply wcbeval_red; eauto. 
             eapply wcbeval_red; eauto.
             rewrite <- !mkApps_snoc.
             eapply PCUICReduction.red1_red.
             eapply red_fix.
             rewrite closed_unfold_fix_cunfold_eq.
             now eapply PCUICClosed.subject_closed in t1.
             rewrite /cunfold_fix e0 /= //.
             pose proof (eval_to_value _ _ _ e3) as vfix.
             eapply PCUICWcbvEval.stuck_fix_value_args in vfix; eauto.
             2:{ rewrite /cunfold_fix e0 //. }
             simpl in vfix. 
             subst. unfold is_constructor.
             rewrite nth_error_snoc. lia.
             assert(Σ ;;; [] |- mkApps (tFix mfix idx) (argsv ++ [av]) : PCUICLiftSubst.subst [av] 0 x1).
             { rewrite -mkApps_nested. eapply type_App; eauto. eapply subject_reduction_eval;eauto. }
             epose proof (fix_app_is_constructor Σ (args:=argsv ++ [av])%list axfree X).
             rewrite /unfold_fix e0 in X0.
             specialize (X0 eq_refl). simpl in X0.
             rewrite nth_error_snoc in X0. auto. apply X0.
             eapply value_whnf; eauto.
             eapply eval_closed; eauto. now eapply PCUICClosed.subject_closed in t0.
             eapply eval_to_value; eauto. }

           exists x3. split. eauto.
           eapply Ee.eval_fix.
           ++ eauto.
           ++ eauto.
           ++ rewrite <- Ee.closed_unfold_fix_cunfold_eq.
              { unfold ETyping.unfold_fix. rewrite e -e2.
                now rewrite (Forall2_length H4). }
              eapply eval_closed in e3; eauto.
              clear -e3 Hmfix'.
              pose proof (All2_length _ _ Hmfix').
              eapply PCUICClosed.closedn_mkApps_inv in e3.
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
              unfold test_def in a. apply andP in a as [_ Hbod].
              rewrite fix_context_length.
              now rewrite Nat.add_0_r in Hbod.
              eauto with pcuic.
              now eapply PCUICClosed.subject_closed in Ht.
          ++ auto.
           
        -- cbn. destruct p. destruct p.
           eapply (erases_subst Σ [] (PCUICLiftSubst.fix_context mfix) [] dbody (fix_subst mfix)) in e3; cbn; eauto.
           ++ eapply subslet_fix_subst. now eapply wf_ext_wf. all: eassumption.
           ++ eapply nth_error_all in a1; eauto. cbn in a1.
              eapply a1.
           ++ eapply All2_from_nth_error.
              erewrite fix_subst_length, ETyping.fix_subst_length, All2_length; eauto.
              intros.
              rewrite fix_subst_nth in H3. now rewrite fix_subst_length in H2.
              rewrite efix_subst_nth in H5. rewrite fix_subst_length in H2.
              erewrite <- All2_length; eauto.
              inv H5; inv H3.
              erewrite All2_length; eauto.
      * eapply (Is_type_app _ _ _ (argsv ++ [av])) in X as []; tas.
        -- exists EAst.tBox.
           split.
           ++ econstructor.
              eapply Is_type_eval. 4:eauto. all:eauto.
              rewrite -mkApps_nested.
              eapply eval_fix; eauto. 
              1-2:eapply value_final, eval_to_value; eauto.
              rewrite /cunfold_fix e0 //. congruence.
           ++ eapply Ee.eval_box; [|eauto].
              apply eval_to_mkApps_tBox_inv in ev_stuck as ?; subst.
              eauto.
        -- eauto.
        -- rewrite mkApps_snoc.
           eapply type_App; eauto.
           eapply subject_reduction; eauto.
           eapply wcbeval_red; eauto.

  - apply inversion_App in Hty as Hty'; [|eauto].
    destruct Hty' as (? & ? & ? & ? & ? & ?).

    eapply subject_reduction in t as typ_stuck_fix; [|eauto|]; first last.
    { eapply wcbeval_red. 4:eauto. all:eauto. }

    eapply erases_App in He as He'; [|eauto].
    destruct He' as [(-> & [])|(? & ? & -> & ? & ?)].
    + exists E.tBox.
      split; [|eauto using Ee.eval].
      constructor.
      eapply Is_type_red.
      * eauto.
      * eapply PCUICReduction.red_app.
        -- eapply wcbeval_red; [eauto|eauto| |eauto]. eauto.
        -- eapply wcbeval_red; [eauto|eauto| |eauto]. eauto.
      * eauto.
    + eapply subject_reduction in t0 as typ_arg; [|eauto|]; first last.
      { eapply wcbeval_red; [eauto|eauto| |eauto]. eauto. }

      eapply IHeval1 in H1 as (? & ? & ?); [|eauto].
      eapply IHeval2 in H2 as (? & ? & ?); [|eauto].
      eapply erases_mkApps_inv in H1; [|eauto|eauto].
      destruct H1 as [(? & ? & ? & -> & [] & ? & ? & ->)|(? & ? & -> & ? & ?)].
      * apply eval_to_mkApps_tBox_inv in H3 as ?; subst.
        depelim H5.
        rewrite -> !app_nil_r in *.
        cbn in *.
        exists E.tBox.
        split; [|eauto using Ee.eval].
        eapply (Is_type_app _ _ _ [av]) in X as [].
        -- constructor.
           apply X.
        -- eauto.
        -- eauto.
        -- cbn.
           eapply type_App; eauto.
      * depelim H1.
        -- exists (E.tApp (E.mkApps (E.tFix mfix' idx) x7) x5).
           split; [eauto using erases_tApp, erases_mkApps|].
           unfold cunfold_fix in *.
           destruct (nth_error _ _) eqn:nth; [|congruence].
           eapply All2_nth_error_Some in X as (? & ? & ? & ? & ?); [|eauto].
           eapply Ee.eval_fix_value.
           ++ eauto.
           ++ eauto.
           ++ unfold Ee.cunfold_fix.
              rewrite e0.
              reflexivity.
           ++ eapply Forall2_length in H5. noconf e. lia.
              
        -- exists E.tBox.
           apply eval_to_mkApps_tBox_inv in H3 as ?; subst.
           split; [|eauto using Ee.eval].
           eapply Is_type_app in X as [].
           ++ constructor.
              rewrite <- mkApps_snoc.
              exact X.
           ++ eauto.
           ++ eauto.
           ++ rewrite mkApps_snoc.
              eapply type_App; eauto.

  - destruct ip.
    assert (Hty' := Hty).
    eapply inversion_Case in Hty' as [u' [args' [mdecl [idecl [ps [pty [btys
                                   [? [? [? [? [? [_ [? [ht0 [? ?]]]]]]]]]]]]]]]];
    eauto.
    assert (t0' := t0).
    eapply PCUICValidity.inversion_mkApps in t0' as (? & ? & ?); eauto.
    pose proof (PCUICClosed.subject_closed wfΣ t1) as clfix.
    eapply inversion_CoFix in t1; destruct_sigma t1; auto.
    eapply PCUICSpine.typing_spine_strengthen in t2; eauto.
    assert(Hty' := Hty).
    assert(clcof : PCUICLiftSubst.closedn 0 (tCoFix mfix idx)).
    { eapply PCUICClosed.subject_closed in Hty; eauto. }
    eapply subject_reduction in Hty'. 2:auto.
    2:{ eapply PCUICReduction.red1_red. eapply PCUICReduction.red_cofix_case. eauto.
        rewrite closed_unfold_cofix_cunfold_eq; eauto. }
    specialize (IHeval _ Hty').
    inv He; [eapply erases_mkApps_inv in H7; eauto; destruct H7 as [H7|H7]; destruct_sigma H7|].
    * destruct H7 as (? & ? & ? & ? & ? & ? & ? & ?). subst.
      destruct H1.
      edestruct IHeval as (? & ? & ?).
      { constructor; eauto.
        rewrite -mkApps_nested.
        eapply erases_mkApps. instantiate(1:=EAst.tBox).
        constructor.
        eapply isErasable_Proof.
        eapply tCoFix_no_Type in X0; auto.
        pose proof X0 as X0'. destruct X0' as [tyapp [u [Htyapp Hu]]].
        eapply Is_proof_ty; eauto.
        eapply unfold_cofix_type; eauto.
        move: e. rewrite -closed_unfold_cofix_cunfold_eq // /unfold_cofix e2.
        intros e; eapply e. eauto. }
      exists x3; split; auto.
    * destruct H7 as (? & ? & ? & ? & ?).
      subst c'.
      pose proof (erases_closed _ _ _ _ clfix H1) as clfix'.
      depelim H1.
      + pose proof X as X'. eapply All2_nth_error_Some in X'; eauto.
        destruct X' as (t' & Hnth & dn & rargeq & er).
        assert (e' := e).
        move: e'. rewrite -closed_unfold_cofix_cunfold_eq // /unfold_cofix e2.
        intros [= <- Heq].
        eapply (erases_subst Σ [] (PCUICLiftSubst.fix_context mfix) [] (dbody decl) (cofix_subst mfix) _ (ETyping.cofix_subst mfix')) in er; cbn; eauto.
        2:{ eapply subslet_cofix_subst; eauto. constructor; eauto. }
        simpl in er. rewrite Heq in er.
        3:{ eapply All2_from_nth_error.
            erewrite cofix_subst_length, ETyping.cofix_subst_length, All2_length; eauto.
            intros.
            rewrite cofix_subst_nth in H1. now rewrite cofix_subst_length in H0.
            rewrite ecofix_subst_nth in H3. rewrite cofix_subst_length in H0.
            erewrite <- All2_length; eauto.
            inv H1; inv H3.
            erewrite All2_length; eauto. }
        edestruct IHeval as (? & ? & ?).
        constructor; eauto. eapply erases_mkApps; eauto.
        eexists; intuition eauto.
        eapply Ee.red_cofix_case; eauto.
        rewrite /Ee.cunfold_cofix Hnth //. f_equal.
        erewrite (closed_cofix_substl_subst_eq); eauto.
        eapply nth_error_all in a1; eauto. simpl in a1. eauto.
      + edestruct IHeval as (? & ? & ?).
        { constructor; eauto.
          eapply erases_mkApps. instantiate(1:=EAst.tBox).
          constructor.
          eapply isErasable_Proof.
          eapply (tCoFix_no_Type _ _ _ []) in X; auto.
          pose proof X as X'. destruct X' as [tyapp [u [Htyapp Hu]]].
          eapply Is_proof_ty; eauto.
          eapply (unfold_cofix_type _ _ _ []); eauto.
          move: e. rewrite -closed_unfold_cofix_cunfold_eq // /unfold_cofix e2.
          intros e; eapply e. eauto. }
        exists x0; split; auto.
    * exists EAst.tBox; split; auto.
      2:repeat constructor.
      constructor.
      eapply Is_type_eval; eauto.
      eapply Is_type_red. 3:eauto. auto.
      eapply PCUICReduction.red1_red.
      eapply PCUICReduction.red_cofix_case.
      move: e. rewrite -closed_unfold_cofix_cunfold_eq // /unfold_cofix e2.
      intros e; eapply e.
        
  - assert (Hty' := Hty).
    eapply inversion_Proj in Hty' as (? & ? & ? & [] & ? & ? & ? & ? & ?); auto.
    set (t0' := t0).
    eapply PCUICValidity.inversion_mkApps in t0' as (? & ? & ?); eauto.
    pose proof (PCUICClosed.subject_closed wfΣ t0) as clfix.
    assert(clcof : PCUICLiftSubst.closedn 0 (tCoFix mfix idx)).
    { eapply PCUICClosed.subject_closed in t1; eauto. }
    eapply inversion_CoFix in t1; destruct_sigma t1; auto.
    eapply PCUICSpine.typing_spine_strengthen in t2; eauto.
    assert(Hty' := Hty).
    eapply subject_reduction in Hty'. 2:auto.
    2:{ eapply PCUICReduction.red1_red. eapply PCUICReduction.red_cofix_proj. eauto.
        rewrite closed_unfold_cofix_cunfold_eq; eauto. }
    specialize (IHeval _ Hty').
    inv He; [eapply erases_mkApps_inv in H4; eauto; destruct_sigma H4|]; eauto.
    destruct H4.
    * destruct H0 as (? & ? & ? & ? & ? & ? & ? & ?). subst.
      destruct H1.
      edestruct IHeval as (? & ? & ?).
      { constructor; eauto.
        rewrite -mkApps_nested.
        eapply erases_mkApps. instantiate(1:=EAst.tBox).
        constructor.
        eapply isErasable_Proof.
        eapply tCoFix_no_Type in X; auto.
        pose proof X as X0'. destruct X0' as [tyapp [u [Htyapp Hu]]].
        eapply Is_proof_ty; eauto.
        eapply unfold_cofix_type; eauto.
        move: e. rewrite -closed_unfold_cofix_cunfold_eq // /unfold_cofix e1.
        intros e; eapply e. eauto. }
      exists x7; split; auto.
    * destruct H0 as (? & ? & ? & ? & ?).
      subst c'.
      pose proof (erases_closed _ [] _ _ clcof H1) as clfix'.
      depelim H1.
      + pose proof X as X'. eapply All2_nth_error_Some in X'; eauto.
        destruct X' as (t' & Hnth & dn & rargeq & er).
        assert (e' := e).
        move: e'. rewrite -closed_unfold_cofix_cunfold_eq // /unfold_cofix e1.
        intros [= <- Heq].
        eapply (erases_subst Σ [] (PCUICLiftSubst.fix_context mfix) [] (dbody decl) (cofix_subst mfix) _ (ETyping.cofix_subst mfix')) in er; cbn; eauto.
        2:{ eapply subslet_cofix_subst; eauto. constructor; eauto. }
        simpl in er. rewrite Heq in er.
        3:{ eapply All2_from_nth_error.
            erewrite cofix_subst_length, ETyping.cofix_subst_length, All2_length; eauto.
            intros.
            rewrite cofix_subst_nth in H1. now rewrite cofix_subst_length in H0.
            rewrite ecofix_subst_nth in H4. rewrite cofix_subst_length in H0.
            erewrite <- All2_length; eauto.
            inv H1; inv H4.
            erewrite All2_length; eauto. }
        edestruct IHeval as (? & ? & ?).
        constructor; eauto. eapply erases_mkApps; eauto.
        eexists; intuition eauto.
        eapply Ee.red_cofix_proj; eauto.
        rewrite /Ee.cunfold_cofix Hnth //. f_equal.
        erewrite (closed_cofix_substl_subst_eq); eauto.
        eapply nth_error_all in a0; eauto. simpl in a0. eauto.
      + edestruct IHeval as (? & ? & ?).
        { constructor; eauto.
          eapply erases_mkApps. instantiate(1:=EAst.tBox).
          constructor.
          eapply isErasable_Proof.
          eapply (tCoFix_no_Type _ _ _ []) in X; auto.
          pose proof X as X'. destruct X' as [tyapp [u [Htyapp Hu]]].
          eapply Is_proof_ty; eauto.
          eapply (unfold_cofix_type _ _ _ []); eauto.
          move: e. rewrite -closed_unfold_cofix_cunfold_eq // /unfold_cofix e1.
          intros e; eapply e. eauto. }
        exists x4; split; auto.
    * exists EAst.tBox; split; auto.
      2:repeat constructor.
      constructor.
      eapply Is_type_eval; eauto.
      eapply Is_type_red. 3:eauto. auto.
      eapply PCUICReduction.red1_red.
      eapply PCUICReduction.red_cofix_proj.
      move: e. rewrite -closed_unfold_cofix_cunfold_eq // /unfold_cofix e1.
      intros e; eapply e.
      
  - pose (Hty' := Hty).
    eapply inversion_App in Hty' as (? & ? & ? & ? & ? & ?); eauto.
    inv He.
    + assert (t' := t). eapply IHeval1 in t as (? & ? & ?); eauto.
      eapply IHeval2 in t0 as (? & ? & ?); eauto.
      destruct (EAstUtils.isBox x2) eqn:E.
      * destruct x2; inv E. exists EAst.tBox. split. 2: econstructor; eauto.
        pose proof (Is_type_app Σ [] f'[a']).
        inversion H1.
        edestruct H7; eauto. cbn. eapply subject_reduction. eauto.
        exact Hty. eapply PCUICReduction.red_app.
        eapply wcbeval_red; eauto.
        eapply inversion_App in Hty as [na [A [B [Hf [Ha _]]]]]; eauto.
        eapply wcbeval_red; eauto.
      * exists (E.tApp x2 x3).
        split. 2:{ eapply Ee.eval_app_cong; eauto.
                   eapply ssrbool.negbT.
                   repeat eapply orb_false_intro.
                   - destruct x2; try reflexivity.
                     inv H1. inv i.
                   - destruct x2 eqn:Ex; try reflexivity.
                     + cbn. inv H1. cbn in *.
                       eapply ssrbool.negbTE, is_FixApp_erases.
                       econstructor; eauto.
                       now rewrite orb_false_r in i.
                     + cbn in *.
                       inv H1. inv i.
                   - eauto. }
        econstructor; eauto.
    + exists EAst.tBox. split. 2: now econstructor.
      econstructor.
      eapply inversion_App in Hty as [na [A [B [Hf [Ha _]]]]]; auto.
      eapply Is_type_red. 3:eauto. eauto.
      eapply PCUICReduction.red_app.
      eapply PCUICClosed.subject_closed in Hf; auto.
      eapply wcbeval_red; eauto.
      eapply PCUICClosed.subject_closed in Ha; auto.
      eapply wcbeval_red; eauto.
      
  - destruct t; try easy.
    + inv He. eexists. split; eauto. now econstructor.
    + inv He. eexists. split; eauto. now econstructor.
    + inv He.
      * eexists. split; eauto. now econstructor.
      * eexists. split. 2: now econstructor.
        econstructor; eauto.
    + inv He.
      * eexists. split. 2: now econstructor.
        econstructor; eauto.
    + inv He.
      * eexists. split. 2: now econstructor.
        econstructor; eauto.
      * eexists. split. 2: now econstructor.
        eauto.
    + inv He.
      * eexists. split; eauto. now econstructor.
      * eexists. split. 2: now econstructor.
        econstructor; eauto.
    + inv He.
      * eexists. split; eauto. now econstructor.
      * eexists. split. 2: now econstructor.
        econstructor; eauto.
Qed.

Print Assumptions erases_correct.
