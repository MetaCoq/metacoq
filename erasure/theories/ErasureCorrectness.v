(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From MetaCoq.Template Require Import config utils monad_utils BasicAst AstUtils.
From MetaCoq.Erasure Require Import EAst ELiftSubst ETyping EWcbvEval Extract Prelim
     ESubstitution EInversion EArities.
From MetaCoq.PCUIC Require Import PCUICTyping PCUICAst PCUICAstUtils PCUICInduction
     PCUICWeakening PCUICSubstitution PCUICChecker PCUICRetyping PCUICMetaTheory
     PCUICWcbvEval PCUICSR  PCUICClosed PCUICInversion PCUICUnivSubstitution
     PCUICEquality PCUICConversion (* PCUICContextConversion *) PCUICElimination
     PCUICUnivSubst PCUICWeakeningEnv.

Require Import String.
Local Open Scope string_scope.
Set Asymmetric Patterns.
Local Set Keyed Unification.

Import MonadNotation.

Require Import Lia.

Module PA := PCUICAst.
Module P := PCUICWcbvEval.

Local Existing Instance config.extraction_checker_flags.

From MetaCoq.PCUIC Require Import PCUICCumulativity.

(** ** Prelim on arities and proofs *)

Lemma isArity_subst_instance u T :
  isArity T ->
  isArity (PCUICUnivSubst.subst_instance_constr u T).
Proof.
  induction T; cbn; intros; tauto.
Qed.

Lemma is_prop_subst_instance:
  forall (u : universe_instance) (x0 : universe), is_prop_sort x0 -> is_prop_sort (UnivSubst.subst_instance_univ u x0).
Proof.
  intros u x0 i. destruct x0; cbn in *; try congruence.
  unfold is_prop_sort in *. unfold Universe.level in *.
  destruct t. destruct t; cbn in *; try congruence.
  destruct b; cbn in *; try congruence.
Qed.


Lemma wf_ext_wk_wf {cf:checker_flags} Σ : wf_ext_wk Σ -> wf Σ.
Proof. intro H; apply H. Qed.

Hint Resolve wf_ext_wk_wf.

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
    eexists. split. eapply t; eauto.
    left. eapply isArity_subst_instance. eauto.
  - eapply typing_subst_instance in t; eauto.
    eexists. split. eapply t; eauto. right.
    eapply typing_subst_instance in t0; eauto.
    eexists. split. eapply t0; eauto.
    now eapply is_prop_subst_instance.
Qed.

(** * Correctness of erasure  *)

Notation "Σ ;;; Γ |- s ▷ t" := (eval Σ Γ s t) (at level 50, Γ, s, t at next level) : type_scope.
Notation "Σ ⊢ s ▷ t" := (Ee.eval Σ s t) (at level 50, s, t at next level) : type_scope.

(** ** Erasure is stable under context conversion *)

Lemma Is_type_conv_context (Σ : global_env_ext) (Γ : context) t (Γ' : context) :
  wf Σ -> wf_local Σ Γ -> wf_local Σ Γ' ->
  PCUICContextConversion.conv_context Σ Γ Γ' -> isErasable Σ Γ t -> isErasable Σ Γ' t.
Proof.
  intros.
  destruct X3 as (? & ? & ?). red.
  exists x. split. eapply PCUICContextConversion.context_conversion. 4:eapply X2. all:eauto.
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
    eapply typing_wf_local; eauto.
    eapply conv_context_app; eauto.
    eapply typing_wf_local; eauto.
    eapply PCUICSafeChecker.wf_local_app_inv; eauto.
  - econstructor; eauto.
    + cbn in *.
      destruct t0. exists x. eapply PCUICContextConversion.context_conversion with (Γ ,,, Γ0); eauto.
      eapply typing_wf_local; eauto.
      eapply conv_context_app; eauto.
      eapply typing_wf_local; eauto.
      eapply PCUICSafeChecker.wf_local_app_inv; eauto.
    + cbn in *. eapply PCUICContextConversion.context_conversion with (Γ ,,, Γ0); eauto.
      eapply typing_wf_local; eauto.
      eapply conv_context_app; eauto.
      eapply typing_wf_local; eauto.
      eapply PCUICSafeChecker.wf_local_app_inv; eauto.
Qed.

Lemma erases_context_conversion :
env_prop
  (fun (Σ : PCUICAst.global_env_ext) (Γ : PCUICAst.context) (t T : PCUICAst.term) =>
      forall Γ' : PCUICAst.context,
        PCUICContextConversion.conv_context Σ Γ Γ' ->
        wf_local Σ Γ' ->
        forall t', erases Σ Γ t t' -> erases Σ Γ' t t').
Proof.
  apply typing_ind_env; intros Σ wfΣ Γ wfΓ; intros **; rename_all_hyps.
  all: match goal with [ H : erases _ _ ?a _ |- ?G ] => tryif is_var a then idtac else inv H end.
  Hint Resolve isErasable_subst_instance.
  Hint Resolve Is_type_conv_context.
  all: try now (econstructor; eauto).
  - econstructor. eapply h_forall_Γ'0.
    econstructor. eauto. constructor. eapply conv_alt_refl, eq_term_refl.
    constructor; auto.
    exists s1.
    eapply PCUICContextConversion.context_conversion. 3:eauto. all:eauto.
  - econstructor. eauto. eapply h_forall_Γ'1.
    econstructor. eauto. constructor.
    eapply PCUICCumulativity.conv_alt_refl; reflexivity.
    constructor; auto. exists s1.
    eapply PCUICContextConversion.context_conversion with Γ; eauto.
    eapply PCUICContextConversion.context_conversion with Γ; eauto.
    eassumption.
  - econstructor. eauto. eauto.
    eapply All2_All_left in X4. 2:{ idtac. intros ? ? [[[? e] ?] ?]. exact e. }

    eapply All2_impl. eapply All2_All_mix_left.
    all: firstorder.
  - admit.
  - econstructor.

    eapply All2_impl. eapply All2_All_mix_left. eassumption. eassumption.
    intros. cbn in *.
    decompose [prod] X2. intuition auto.
    eapply b0.
    subst types.
    eapply conv_context_app; auto. now eapply typing_wf_local in a4.
    eapply typing_wf_local in a4. subst types.
    2:eauto.

    eapply All_local_env_app_inv.
    eapply All_local_env_app in a4. intuition auto.

    (* clear -wfΣ X2 a2 b4 X1. *)
    eapply All_local_env_impl; eauto. simpl; intros.
    destruct T. simpl in *.
    eapply PCUICContextConversion.context_conversion with (Γ ,,, Γ0); eauto.
    now eapply typing_wf_local; eauto.
    eapply conv_context_app; auto. eapply typing_wf_local; eauto.
    eapply typing_wf_local in X2.
    eapply PCUICSafeChecker.wf_local_app_inv.
    eauto. eapply wf_local_rel_local in X2.
    eapply wf_local_rel_app in X2 as []. rewrite app_context_nil_l in w0.


    eapply wf_local_rel_conv; eauto.
    destruct X2. exists x0.
    eapply PCUICContextConversion.context_conversion with (Γ ,,, Γ0); eauto.
    now eapply typing_wf_local; eauto.
    eapply conv_context_app; auto. eapply typing_wf_local; eauto.

    eapply typing_wf_local in t0.
    eapply PCUICSafeChecker.wf_local_app_inv.
    eauto. eapply wf_local_rel_local in t0.
    eapply wf_local_rel_app in t0 as []. rewrite app_context_nil_l in w0.
    eapply wf_local_rel_conv; eauto.
  - eauto.
Admitted.

(** ** Erasure is stable under substituting universe constraints  *)

Lemma fix_context_subst_instance:
  forall (mfix : list (BasicAst.def term)) (u : universe_instance),
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
    (Σ.1,univs) ;;; (PCUICUnivSubst.subst_instance_context u Γ) |- PCUICUnivSubst.subst_instance_constr u t ⇝ℇ t').
Proof.
  apply typing_ind_env; intros; cbn -[PCUICUnivSubst.subst_instance_constr] in *.
  all: match goal with [ H : erases _ _ ?a _ |- ?G ] => tryif is_var a then idtac else inv H end.
  Hint Resolve isErasable_subst_instance.
  all: try now (econstructor; eauto).
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
    eapply All2_All_left. exact X4. intros ? ? [[[? e] ?] ?].
    exact e. exact H15.
    intros; cbn in *. destruct H. destruct p0. split; eauto.
  - admit.
  - assert (Hw :  wf_local (Σ.1, univs) (subst_instance_context u (Γ ,,, types))).
    { (* rewrite subst_instance_context_app. *)
      apply All_local_env_app in X as [X Hfixc].

      revert Hfixc. clear - wfΣ wfΓ H1 H2 X1 X2.
      induction 1.
      - eauto.
      - cbn. econstructor; eauto. cbn in *.
        destruct t0 as (? & ? & ?). eexists.
        cbn. eapply typing_subst_instance in t0; eauto. apply snd in t0. cbn in t0.
        rapply t0; eauto.
        eapply typing_wf_local; eauto.
      - cbn. econstructor; eauto. cbn in *.
        destruct t0 as (? & ? & ?). destruct t1. eexists.
        cbn. eapply typing_subst_instance in t0; eauto. apply snd in t0.
        rapply t0; eauto.
        eapply typing_wf_local; eauto.
        cbn in *. destruct t1. eapply typing_subst_instance in t1; eauto.
        apply snd in t1. rapply t1. all:eauto.
        eapply typing_wf_local; eauto.
    }

    cbn. econstructor; eauto.
    eapply All2_map_left.
    eapply All2_impl. eapply All2_All_mix_left. eassumption.
    exact H7.
    intros; cbn in *. destruct X3. destruct p0. destruct p0.
    destruct p. destruct p. repeat split; eauto.
    eapply e2 in e1.
    unfold PCUICUnivSubst.subst_instance_context in *.
    unfold map_context in *. rewrite map_app in *. subst types. 2:eauto.
    eapply erases_ctx_ext. eassumption. unfold app_context.
    f_equal.
    eapply fix_context_subst_instance. all: eauto.
  - eauto.
Admitted.

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
  unshelve eapply (erases_subst_instance_constr0 Σ _ Γ _ _ _ _); tea; eauto.
Qed.


(** ** Erasure and applications  *)

Lemma erases_App (Σ : global_env_ext) Γ f L T t :
  Σ ;;; Γ |- tApp f L : T ->
  erases Σ Γ (tApp f L) t ->
  (t = tBox × squash (isErasable Σ Γ (tApp f L)))
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
                erases Σ Γ (mkApps f L1) tBox /\
                Forall2 (erases Σ Γ) L2 L2' /\
                t = EAst.mkApps tBox L2'
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
    + subst. eapply type_mkApps_inv in X as (? & ? & [] & ?); eauto.
      eapply erases_App in H0 as [ (-> & []) | (? & ? & ? & ? & ?)].
      * left. exists [a], L, x0. cbn. repeat split. eauto.
        econstructor; eauto.  eauto.
      * subst. right. exists x3, (x4 :: x0). repeat split.
        eauto. econstructor. eauto. eauto.
      * eauto.
Qed.

(** ** Global erasure  *)

Lemma lookup_env_erases (Σ : global_env_ext) c decl Σ' :
  wf Σ ->
  erases_global Σ Σ' ->
  PCUICTyping.lookup_env (fst Σ) c = Some (ConstantDecl c decl) ->
  exists decl', ETyping.lookup_env Σ' c = Some (EAst.ConstantDecl c decl') /\
           erases_constant_body (Σ.1, cst_universes decl)  decl decl'.
Proof.
  unfold erases_global. destruct Σ; simpl.
  intros. induction H; cbn in *.
  - inv H0.
  - destruct ?.
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
  - destruct ?.
    + inv H0.
    + edestruct IHerases_global_decls as (decl' & ? & ?).
      eapply wf_extends.
      eassumption. now eexists [_]. eauto.
      exists decl'. split. eauto.
      unfold erases_constant_body in *. clear H. destruct ?. destruct ?.
      * eapply (@erases_extends (_,_)). 6: eassumption.
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
  { (* extr_env_axiom_free' : is_true (axiom_free (fst Σ)); *)
    extr_env_wf' : wf Σ }.

Hint Constructors PCUICWcbvEval.eval erases.

Lemma erases_correct Σ t T t' v Σ' :
  extraction_pre Σ ->
  Σ;;; [] |- t : T ->
  Σ;;; [] |- t ⇝ℇ t' ->
   erases_global Σ Σ' ->
  Σ;;; [] |- t ▷ v ->
  exists v', Σ;;; [] |- v ⇝ℇ v' /\ Σ' ⊢ t' ▷ v'.
Proof.
  intros pre Hty He Heg H.
  revert T Hty t' He.
  induction H using PCUICWcbvEval.eval_evals_ind; intros T Hty t' He; inv pre.
  - assert (Hty' := Hty).
    assert (eval Σ [] (PCUICAst.tApp f a) res) by eauto.
    eapply inversion_App in Hty as (? & ? & ? & ? & ? & ?).

    inv He.
    + eapply IHeval1 in H4 as (vf' & Hvf' & He_vf'); eauto.
      eapply IHeval2 in H6 as (vu' & Hvu' & He_vu'); eauto.
      pose proof (subject_reduction_eval Σ [] _ _ _ extr_env_wf'0 t0 H).
        eapply inversion_Lambda in X0 as (? & ? & ? & ? & ?).
        assert (Σ ;;; [] |- a' : t). {
          eapply subject_reduction_eval; eauto.
          eapply cumul_Prod_inv in c0 as [].
          econstructor. eassumption. eauto. eapply conv_alt_sym in c0; eauto.
          now eapply conv_alt_cumul. auto. auto. }
      inv Hvf'.
      * assert (Σ;;; [] |- PCUICLiftSubst.subst1 a' 0 b ⇝ℇ subst1 vu' 0 t').
        eapply (erases_subst Σ [] [PCUICAst.vass na t] [] b [a'] t'); eauto.
        econstructor. econstructor. rewrite parsubst_empty. eassumption.
        eapply IHeval3 in H2 as (v' & Hv' & He_v').
        -- exists v'. split; eauto.
           econstructor; eauto.
        -- eapply substitution0; eauto.
      * exists tBox. split.
        eapply Is_type_lambda in X1; eauto. destruct X1. econstructor.
        eapply (is_type_subst Σ [] [PCUICAst.vass na _] [] _ [a']) in X1 ; auto.
        cbn in X1.
        eapply Is_type_eval.
        eauto. eapply H1. eassumption.
        all: eauto. econstructor. econstructor. rewrite parsubst_empty.
        eauto. econstructor. eauto. eauto.
      * auto.
    + exists tBox. split. 2:econstructor; eauto.
      econstructor.
      eapply Is_type_eval; eauto.
    + auto.
  - assert (Hty' := Hty).
    assert (Σ ;;; [] |- tLetIn na b0 t b1 ▷ res) by eauto.
    eapply inversion_LetIn in Hty' as (? & ? & ? & ? & ? & ?).

    inv He.
    + eapply IHeval1 in H6 as (vt1' & Hvt2' & He_vt1'); eauto.
      assert (Hc : PCUICContextConversion.conv_context Σ ([],, vdef na b0 t) [vdef na b0' t]). {
        econstructor. econstructor. econstructor.
        eapply PCUICCumulativity.red_conv_alt.
        eapply wcbeval_red; eauto.
        eapply PCUICCumulativity.conv_alt_refl; reflexivity.
      }
      assert (Σ;;; [vdef na b0' t] |- b1 : x0). {
        cbn in *. eapply PCUICContextConversion.context_conversion. 3:eauto. all:cbn; eauto.
        econstructor. all: cbn; eauto. constructor. constructor. red. exists x; auto.
        simpl. eapply subject_reduction_eval; auto. eauto. eauto.
      }
      assert (Σ;;; [] |- PCUICLiftSubst.subst1 b0' 0 b1 ⇝ℇ subst1 vt1' 0 t2'). {
        eapply (erases_subst Σ [] [PCUICAst.vdef na b0' t] [] b1 [b0'] t2'); eauto.
        enough (subslet Σ [] [PCUICLiftSubst.subst [] 0 b0'] [vdef na b0' t]).
        now rewrite parsubst_empty in X1.
        econstructor. econstructor.
        rewrite !parsubst_empty.
        eapply subject_reduction_eval; eauto.
        eapply erases_context_conversion. 4:eassumption.
        all: cbn; eauto.
        econstructor. all: cbn; eauto. now eapply typing_wf_local in X0.
      }
      eapply IHeval2 in H1 as (vres & Hvres & Hty_vres).
      2:{ eapply substitution_let; eauto. }
      exists vres. split. eauto. econstructor; eauto.
    + exists tBox. split. 2:econstructor; eauto.
      econstructor. eapply Is_type_eval; eauto.
    + auto.
  - destruct i; discriminate.
  - destruct i; discriminate.
  - destruct Σ as (Σ, univs).
    unfold erases_global in Heg.
    assert (Σ ;;; [] |- tConst c u ▷ res) by eauto.
    eapply inversion_Const in Hty as (? & ? & ? & ? & ?).
    inv He.
    + assert (H' := H).
      eapply lookup_env_erases in H; eauto.
      destruct H as (decl' & ? & ?).
      unfold erases_constant_body in H2. rewrite H0 in *.
      destruct ?; try tauto. cbn in *.
      eapply declared_constant_inj in d; eauto; subst.
      edestruct IHeval.
      * cbn in *.
        eapply declared_constant_inv in H'; eauto.
        unfold on_constant_decl in H'. rewrite H0 in H'. red in H'.
        eapply typing_subst_instance in H'; eauto.
        apply snd in H'; rapply H'; eauto.
        admit. admit.
        eapply weaken_env_prop_typing.
      * eapply declared_constant_inv in H'; eauto.
        unfold on_constant_decl in H'. rewrite H0 in H'. cbn in *.
        2:eapply weaken_env_prop_typing.
        eapply erases_subst_instance_constr in H'; eauto.
        admit. admit.
      * destruct H3. exists x0. split; eauto. econstructor; eauto.
    + exists tBox. split. econstructor.
      eapply Is_type_eval. 3: eassumption. eauto. eauto. econstructor. eauto.
    + auto.

  - destruct Σ as (Σ, univs).
    unfold erases_global in Heg.
    (* Axiom free hyp is missing *)
    admit.

  - assert (Hty' := Hty).
    assert (Σ ;;; [] |- tCase (ind, pars) p discr brs ▷ res) by eauto.
    eapply inversion_Case in Hty' as (u' & args' & mdecl & idecl & pty & indctx & pctx & ps & btys & ? & ? & ? & ? & ? & ? & ? & ? & ?).
    assert (Σ ;;; [] |- mkApps (tConstruct ind c u) args :  mkApps (tInd ind u') args').
    eapply subject_reduction_eval; eauto.
    eapply type_mkApps_inv in X0 as (? & ? & [] & ?); eauto.
    eapply inversion_Construct in t1 as (mdecl' & idecl' & cdecl & ? & ? & ? & ?).
    assert (d1 := d0).
    destruct d0.

    edestruct (declared_inductive_inj H1 d). subst.

    pose proof (length_of_btys e0).

    inv He.
    + eapply IHeval1 in H11 as (v' & Hv' & He_v'); eauto.
      eapply erases_mkApps_inv in Hv' as [(? & ? & ? & ? & [] & ? & ? & ?) | (? & ? & ? & ? & ?)]; eauto.
      3: eapply subject_reduction_eval; eauto.
      * subst.

        eapply Is_type_app in X0. destruct X0. 2:eauto. 2: econstructor. 2:{ rewrite mkApps_nested. eapply subject_reduction_eval; eauto. }
        rewrite mkApps_nested in X0.

        eapply tConstruct_no_Type in X0.
        eapply H10 in X0 as []; eauto. exists []; now destruct Σ. admit. admit.

        (* destruct (ind_ctors idecl'). cbn in H4. destruct c; inv H2. *)
        (* destruct l; cbn in *; try omega. destruct c as [ | []]; cbn in H2; inv H2. *)

        (* destruct btys as [ | ? []]; cbn in H3; try omega. clear H3 H4. destruct H7. *)
        (* (* eapply H7 in d1. *) inv a. inv X2. inv H12. inv H8. destruct H4. destruct x4, y; cbn in *; subst. *)
        (* destruct X1. subst. destruct p0; cbn in *. *)

        (* edestruct (IHeval2) as (? & ? & ?). *)
        (* eapply subject_reduction. eauto. exact Hty. *)
        (* etransitivity. *)
        (* eapply PCUICReduction.red_case_c. eapply wcbeval_red. eauto. *)
        (* econstructor. econstructor. econstructor. *)

        (* all:unfold iota_red in *. all:cbn in *. *)
        (* eapply erases_mkApps. eauto. *)
        (* instantiate (1 := repeat tBox _). *)
        (* eapply All2_Forall2. *)
        (* eapply All2_impl. *)
        (* eapply All2_All_mix_left. eassumption. *)
        (* 2:{ intros. destruct X1. assert (y = tBox). exact y0. subst. econstructor. *)
        (*     now eapply isErasable_Proof. } *)

        (* eapply All2_right_triv. 2: now rewrite repeat_length. *)

        (* now eapply All_repeat. *)

        (* (* destruct x4; cbn in e2; subst. destruct X2. destruct p0; cbn in e2; subst. cbn in *.  destruct y.  *) *)
        (* exists x4. split; eauto. eapply eval_iota_sing.  2:eauto. *)
        (* pose proof (Ee.eval_to_value _ _ _ He_v'). *)
        (* eapply value_app_inv in H4. subst. eassumption. 2:eauto. *)

        (* eapply tCase_length_branch_inv in extr_env_wf'0. *)
        (* 2:{ eapply subject_reduction. eauto. *)
        (*     exact Hty. *)
        (*     eapply PCUICReduction.red_case_c. eapply wcbeval_red. eauto.  } *)
        (* 2: reflexivity. *)

        (* enough (#|skipn (ind_npars mdecl') (x1 ++ x2)| = n) as <- by eauto. *)
        (* rewrite skipn_length. rewrite extr_env_wf'0. omega. *)
        (* rewrite extr_env_wf'0. omega. *)
      * subst. unfold iota_red in *.
        destruct (nth_error brs c) eqn:Hnth.
        2:{ eapply nth_error_None in Hnth. erewrite All2_length in Hnth. 2:exact a. rewrite H3 in Hnth.
            eapply nth_error_Some_length in H2. cbn in H2. omega.
        }
        rewrite <- nth_default_eq in *. unfold nth_default in *.
        rewrite Hnth in *.

        destruct (All2_nth_error_Some _ _ H12 Hnth) as (? & ? & ? & ?).
        destruct (All2_nth_error_Some _ _ a Hnth) as (? & ? & ? & ?).
        destruct p0, x4. cbn in *. subst.
        edestruct IHeval2 as (? & ? & ?).
        eapply subject_reduction. eauto. exact Hty.
        etransitivity.
        eapply PCUICReduction.red_case_c. eapply wcbeval_red. eauto.

        etransitivity. eapply trans_red. econstructor.
        econstructor. unfold iota_red. rewrite <- nth_default_eq. unfold nth_default.
        rewrite Hnth. econstructor.

        eapply erases_mkApps. eauto.
        eapply Forall2_skipn. eauto.
        inv H5.
        -- exists x4. split; eauto.
           econstructor. eauto. unfold ETyping.iota_red.
           rewrite <- nth_default_eq. unfold nth_default. rewrite e. cbn. eauto.
        -- eapply Is_type_app in X0 as[]. 2:eauto. 2:econstructor. 2:{ eapply subject_reduction_eval. 3:eassumption. all: eauto. }

           eapply tConstruct_no_Type in X0.
           eapply H10 in X0 as []; eauto. admit. admit. admit. (* 2: exists []; now destruct Σ. *)

           (* destruct (ind_ctors idecl'). cbn in H4. destruct c; inv H2. *)
           (* destruct l; cbn in *; try omega. destruct c as [ | []]; cbn in H2; inv H2. *)

           (* destruct btys as [ | ? []]; cbn in H3; try omega. clear H3 H4. destruct H8. *)
           (* (* eapply H7 in d1. *) inv a. inv X2. inv H12. inv H9. destruct H4. destruct x1, y; cbn in *; subst. *)
           (* destruct X1. subst. destruct p0; cbn in *. destruct x3. inv e. inv Hnth. cbn in *. *)

           (* edestruct (IHeval2) as (? & ? & ?). *)
           (* eapply subject_reduction. eauto. exact Hty. *)
           (* etransitivity. *)
           (* eapply PCUICReduction.red_case_c. eapply wcbeval_red. eauto. *)
           (* econstructor. econstructor. econstructor. *)

           (* eapply erases_mkApps. eauto. *)
           (* instantiate (1 := repeat tBox _). *)
           (* eapply All2_Forall2. *)
           (* eapply All2_impl. *)
           (* eapply All2_All_mix_left. eassumption. *)
           (* 2:{ intros. destruct X1. assert (y = tBox). exact y0. subst. econstructor. *)
           (*     now eapply isErasable_Proof. } *)

           (* eapply All2_right_triv. 2:now rewrite repeat_length. *)
           (* now eapply All_repeat. *)

           (* exists x1. split; eauto. *)
           (* eapply eval_iota_sing. *)
           (* pose proof (Ee.eval_to_value _ _ _ He_v'). *)
           (* eapply value_app_inv in H4. subst. eassumption. *)
           (* reflexivity. cbn in *. *)
           (* enough (#|skipn (ind_npars mdecl') args| = n0) as <- by eauto. *)

           (* eapply tCase_length_branch_inv in extr_env_wf'0. *)
           (* 2:{ eapply subject_reduction. eauto. *)
           (*     exact Hty. *)
           (*     eapply PCUICReduction.red_case_c. eapply wcbeval_red. eauto.  } *)
           (* 2: reflexivity. *)

           (* enough (#|skipn (ind_npars mdecl') args| = n0) as <- by eauto. *)
           (* rewrite skipn_length. rewrite extr_env_wf'0. omega. *)
           (* rewrite extr_env_wf'0. omega. eauto. *)
    + exists tBox. split. econstructor.
      eapply Is_type_eval; eauto. econstructor; eauto. admit. admit.
    + admit.
    + admit.
    + auto.
    + auto.
  - pose (Hty' := Hty).
    eapply inversion_Proj in Hty' as (? & ? & ? & [] & ? & ? & ? & ? & ?).
    inv He.
    + eapply IHeval1 in H6 as (vc' & Hvc' & Hty_vc'); eauto.
      eapply erases_mkApps_inv in Hvc'; eauto.
      2: eapply subject_reduction_eval; eauto.
      destruct Hvc' as [ (? & ? & ? & ? & [] & ? & ? & ?) | (? & ? & ? & ? & ?)]; subst.
      * exists tBox. split.

        eapply Is_type_app in X as []; eauto. 2:{ rewrite mkApps_nested. eapply subject_reduction_eval; eauto. }
        rewrite mkApps_nested in X.

        eapply tConstruct_no_Type in X. eapply H4 in X as [? []]; eauto.
        2: now destruct d. 2: now exists []; destruct Σ.

        econstructor.
        eapply Is_type_eval. eauto. eauto.
        eapply nth_error_all.
        erewrite nth_error_skipn. reflexivity. eassumption.
        eapply All_impl. assert (pars = ind_npars x0). destruct d as (? & ? & ?). now rewrite H8. subst.
        eassumption.
        eapply isErasable_Proof. eauto.

        eapply eval_proj_box.
        pose proof (Ee.eval_to_value _ _ _ Hty_vc').
        eapply value_app_inv in H2. subst. eassumption.
      * rename H4 into Hinf.
        eapply Forall2_nth_error_Some in H5 as (? & ? & ?); eauto.
        assert (Σ ;;; [] |- mkApps (tConstruct i k u) args : mkApps (tInd i x) x2).
        eapply subject_reduction_eval; eauto.
        eapply type_mkApps_inv in X as (? & ? & [] & ?); eauto.
        eapply typing_spine_inv in t2 as []; eauto.
        eapply IHeval2 in H4 as (? & ? & ?); eauto.
        inv H3.
        -- exists x9. split; eauto. econstructor. eauto.
           rewrite <- nth_default_eq. unfold nth_default. now rewrite H2.
        -- exists tBox. split.


           eapply Is_type_app in X as []; eauto. 2:{ eapply subject_reduction_eval. 3: eauto. eauto. eauto. }

           eapply tConstruct_no_Type in X. eapply Hinf in X as [? []]; eauto.
           2: now destruct d. 2: now exists []; destruct Σ.

           econstructor.
           eapply Is_type_eval. eauto. eauto.
           eapply nth_error_all.
           erewrite nth_error_skipn. reflexivity. eassumption.
           eapply All_impl. assert (pars = ind_npars x0). destruct d as (? & ? & ?). now rewrite H8. subst.
           eassumption.
           eapply isErasable_Proof. eauto.

           eapply eval_proj_box.
           pose proof (Ee.eval_to_value _ _ _ Hty_vc').
           eapply value_app_inv in H3. subst. eassumption.
    + exists tBox. split. econstructor.
      eapply Is_type_eval. 3: eassumption. eauto. eauto. econstructor. eauto.
    + auto.

  - assert (Hty' := Hty).
    assert (Hunf := H0).
    assert (Hcon := H1).
    assert (Σ ;;; [] |- mkApps f args ▷ res) by eauto.
    eapply type_mkApps_inv in Hty' as (? & ? & [] & ?); eauto.
    assert (HT := t).
    eapply subject_reduction_eval in t; eauto.
    eapply inversion_Fix in t as (? & ? & ? & ? & ? & ?).
    unfold unfold_fix in H0. rewrite e in H0.
    destruct ?. 2:{ discriminate. } all:eauto. inv H0.

    eapply erases_mkApps_inv in He as [(? & ? & ? & ? & [] & ? & ? & ?) | (? & ? & ? & ? & ?)]; eauto.
    + subst. assert (X100 := Hty).
      rewrite <- mkApps_nested in X100. eapply Is_type_app in X100 as[]. all:eauto.
      exists tBox. split. 2:{
        assert (exists x5, Forall2 (EWcbvEval.eval Σ') x4 x5) as [x5]. {
          eapply All2_app_inv in H3 as ([] & ? & ?). destruct p.
          clear a0. subst.
          assert (forall x n, nth_error x3 n = Some x -> ∑ T,  Σ;;; [] |- x : T).
          { intros. eapply typing_spine_inv with (arg := n + #|x2|) in t0 as [].
            2:{ rewrite nth_error_app2. 2:omega. rewrite Nat.add_sub. eassumption. }
            eauto.
          }
          clear - X3 a1 H6. revert X3 x4 H6; induction a1; intros.
          ** inv H6. exists []; eauto.
          ** inv H6. destruct (X3 x 0 eq_refl).
             eapply r in t as (? & ? & ?); eauto.
             eapply IHa1 in H3 as (? & ?); eauto.
             intros. eapply (X3 x2 (S n)). eassumption.
        }
        eapply eval_box_apps. eassumption. econstructor; eauto. }
      econstructor.
      eapply Is_type_eval. eauto. eassumption.
      rewrite <- mkApps_nested.  eassumption.
    + subst.
      specialize (IHeval1 _ HT _ H5).
      destruct IHeval1 as [v' [fixv' x2v']].
      admit.
      (*

      inv fixv'.
      * assert (Hmfix' := H4).
        eapply All2_nth_error_Some in H4 as (? & ? & ? & ? & ?); eauto.
        destruct x1. cbn in *. subst.

        enough(Σ;;; [] ,,, subst_context (fix_subst mfix) 0 [] |- PCUICLiftSubst.subst (fix_subst mfix) 0 dbody ⇝ℇ subst (ETyping.fix_subst mfix') 0 (Extract.E.dbody x2)). clear e3. rename H into e3.
        -- enough (exists L, Forall2 (erases Σ []) args' L /\ Forall2 (Ee.eval Σ') x3 L).
           ++ cbn in e3. destruct H as (L & ? & ?).
              assert (Hv : Forall Ee.value L).
              { eapply Forall2_Forall_right; eauto.
                intros. eapply EWcbvEval.eval_to_value. eauto.
              }

              eapply erases_mkApps in e3; eauto.
              eapply IHeval in e3 as (? & ? & ?); cbn; eauto.
              exists x1. split. eauto. admit.
              (*  econstructor. unfold ETyping.unfold_fix. *)
              (* rewrite e0. reflexivity. *)
              (* eassumption. *)
              (* all:eauto. *)
              (* ** unfold is_constructor in *. *)
              (*    (* destruct ?; inv H1. *) *)
              (*    (* unfold is_constructor_or_box. *) *)
              (*    eapply Forall2_nth_error_Some in H as (? & ? & ?); eauto. *)
              (*    rewrite H. *)

              (*    unfold isConstruct_app in H8. *)
              (*    destruct (decompose_app t) eqn:EEAst. *)
              (*    assert (E2 : fst (decompose_app t) = t1) by now rewrite EEAst. *)
              (*    destruct t1. *)
              (*    all:inv H8. *)
              (*    (* erewrite <- PCUICConfluence.fst_decompose_app_rec in E2. *) *)

              (*    pose proof (decompose_app_rec_inv EE). *)
              (*    cbn in H7. subst. *)
              (*    assert (∑ T, Σ ;;; [] |- mkApps (tConstruct ind n ui) l : T) as [T' HT']. *)
              (*    { eapply typing_spine_eval in t0; eauto. *)
              (*      eapply typing_spine_inv in t0; eauto. *)
              (*      eapply PCUICValidity.validity; eauto. *)
              (*    } *)
              (*    eapply erases_mkApps_inv in H1. *)
              (*    destruct H1 as [ (? & ? & ? & ? & [] & ? & ? & ?) | (? & ? & ? & ? & ?) ]. *)
              (*    --- subst. *)
              (*        eapply nth_error_forall in Hv; eauto. *)
              (*        eapply value_app_inv in Hv. subst. reflexivity. *)
              (*    --- subst. inv H7. *)
              (*        +++ eapply nth_error_forall in Hv; eauto. *)
              (*            destruct x6 using rev_ind; cbn - [EAstUtils.decompose_app]. reflexivity. *)
              (*            rewrite emkApps_snoc at 1. *)
              (*            generalize (x6 ++ [x4])%list. clear. intros. *)
              (*            rewrite Prelim.decompose_app_mkApps. reflexivity. *)
              (*            reflexivity. *)
              (*        +++ eapply nth_error_forall in Hv; eauto. *)
              (*            eapply value_app_inv in Hv. subst. eauto. *)
              (*    --- eauto. *)
              (*    --- eauto. *)

              ** eapply subject_reduction. eauto. exact Hty.
                 etransitivity.
                 eapply PCUICReduction.red_mkApps. econstructor.
                 eapply All2_impl. exact X. intros. now eapply wcbeval_red.
                 econstructor 2. econstructor.
                 econstructor. exact Hunf. exact Hcon.
           ++ clear - t0 H0 H5. revert x t0 x3 H5; induction H0; intros.
              ** inv H5. exists []; eauto.
              ** inv H5. inv t0. eapply r in H2 as (? & ? & ?); eauto.
                 eapply IHAll2 in X2 as (? & ? & ?); eauto.
        -- cbn.
           eapply (erases_subst Σ [] (PCUICLiftSubst.fix_context mfix) [] dbody (fix_subst mfix)) in e3; cbn; eauto.
           ++ eapply subslet_fix_subst. all: eassumption.
           ++ eapply nth_error_all in a0; eauto. cbn in a0.
              eapply a0.
           ++ eapply All2_from_nth_error.
              erewrite fix_subst_length, ETyping.fix_subst_length, All2_length; eauto.
              intros.
              rewrite fix_subst_nth in H3. 2:{ now rewrite fix_subst_length in H. }
              rewrite efix_subst_nth in H4. 2:{ rewrite fix_subst_length in H.
                                                erewrite <- All2_length; eauto. }
              inv H3; inv H4.
              erewrite All2_length; eauto.
      * eapply Is_type_app in X1 as [].
        exists tBox. split.
        econstructor.
        eapply Is_type_eval. eauto. eassumption.
        eauto.

        assert (exists x5, Forall2 (EWcbvEval.eval Σ') x3 x5) as [x5]. {
          assert (forall x n, nth_error args n = Some x -> ∑ T,  Σ;;; [] |- x : T).
          { intros. eapply typing_spine_inv with (arg := n) in t0 as [].
            2:{ eassumption. } eauto.
          }
          clear - X2 H0 H5. revert X2 x3 H5; induction H0; intros.
          ** inv H5. exists []; eauto.
          ** inv H5. destruct (X2 x 0 eq_refl).
             eapply r in t as (? & ? & ?); eauto.
             eapply IHAll2 in H4 as (? & ?); eauto.
             intros. eapply (X2 x2 (S n)). eassumption.
        }

        eapply eval_box_apps. eauto. econstructor. eauto. eauto. econstructor. eauto.
    + auto. *)
  - (* Stuck fixpoints are not possible *)
    unfold isStuckFix in H1.
    assert (Hty' := Hty).
    eapply type_mkApps_inv in Hty' as (? & ? & [] & ?); eauto.
    assert (HT := t).
    eapply subject_reduction_eval in t; eauto.
    eapply inversion_Fix in t as (? & ? & ? & ? & ? & ?).
    unfold unfold_fix in H1. rewrite e in H1.
    destruct ?; try discriminate. destruct p as [narg fn].
    destruct ?; try discriminate. inv E.
    2:auto.
    eapply nth_error_all in a0; eauto.
    simpl in a0.
    destruct a0.
    rewrite fix_context_length in t.
    unfold is_constructor in H1. destruct ?; try discriminate.
    * (* typing_spine x args x0 -> typing spine (dtype x1) args' x0' *)
      (* Inversions: typing_spine Σ [] (dtype x1) args' x0' -> nth_error args' n = Some t1 ->
       [ ] |- t1 : tInd _ _.
       []   |- t1 : tInd -> isConstructapp t1.
       *)
      admit.
    * simpl in H1.
      (* Under-applied fixpoint is a valid value *)
      specialize (IHeval _ HT).
      eapply erases_mkApps_inv in He as [(? & ? & ? & ? & [] & ? & ? & ?) | (? & ? & ? & ? & ?)]; eauto.
      ** subst.
         exists tBox. split; auto.
         admit.
         admit.
      ** subst.
         admit.

  - (* Case Cofix *) admit.
  - (* Proj cofix *) admit.
  - (* App congruence *) admit.
  - admit.
(*  - inv He.
    + eexists. split; eauto. econstructor. eauto. constructor.
    + eexists. split; eauto. now econstructor.
  - inv He. eexists. split; eauto. now econstructor.
  - inv He. eexists. split; eauto. now econstructor.
  - assert (Σ ;;; [] |- mkApps (tInd i u) l' : T).
    eapply subject_reduction_eval; eauto; econstructor; eauto.
    assert (Hty' := X0).
    eapply type_mkApps_inv in X0 as (? & ? & [] & ?); eauto.
    assert (Hty'' := Hty).
    eapply type_mkApps_inv in Hty'' as (? & ? & [] & ?); eauto.
    eapply inversion_Ind in t as (? & ? & ? & ? & ? & ?).
    eapply erases_mkApps_inv in Hty; eauto.
    destruct Hty as [ (? & ? & ? & ? & [] & ? & ? & ?) | (? & ? & ? & ? & ?)].
    + subst.
      assert (∥isErasable Σ [] (mkApps (tInd i u) l')∥).
      eapply All2_app_inv in X as ([] & [] & ?). subst.
      rewrite <- mkApps_nested.
      eapply Is_type_app. eauto. econstructor.
      rewrite mkApps_nested. eauto.
      eapply Is_type_eval. eauto.
      eapply eval_app_ind. eauto. eauto.
      eauto. destruct H1.
      exists tBox.
      split. 2:{

         assert (exists x5, Forall2 (EWcbvEval.eval Σ') x7 x5) as [x8]. {
          eapply All2_app_inv in H0 as ([] & ? & ?). destruct p.
          clear a1. subst.
          assert (forall x n, nth_error x6 n = Some x -> ∑ T,  Σ;;; [] |- x : T).
          { intros. eapply typing_spine_inv with (arg := n + #|x5|) in t2 as [].
            2:{ rewrite nth_error_app2. 2:omega. rewrite Nat.add_sub. eauto. }
            eauto.
          }
          clear - X2 a0 H3. revert X2 x7 H3; induction a0; intros.
          ** inv H3. exists []; eauto.
          ** inv H3. destruct (X2 x 0 eq_refl).
             eapply r in t as (? & ? & ?); eauto.
             eapply IHa0 in H4 as (? & ?); eauto.
             intros. eapply (X2 x2 (S n)). eassumption.
        }
        eapply eval_box_apps. eauto. now econstructor. }
      econstructor. eauto.
    + subst.
      eapply IHeval in H2 as (? & ? & ?).
      inv H1. eapply Is_type_app in X0 as [].
      exists tBox.
      split. econstructor.
      eauto.

      assert (exists x5, Forall2 (EWcbvEval.eval Σ') x6 x5) as [x8]. {
        assert (forall x n, nth_error l n = Some x -> ∑ T,  Σ;;; [] |- x : T).
        { intros. eapply typing_spine_inv. eassumption. eauto.
        }
        clear - X1 H0 H3. revert X1 x6 H3; induction H0; intros.
        ** inv H3. exists []; eauto.
        ** inv H3. destruct (X1 x 0 eq_refl).
           eapply r in t as (? & ? & ?); eauto.
           eapply IHAll2 in H5 as (? & ?); eauto.
           intros. eapply (X1 x2 (S n)). eassumption.
      }
      eapply eval_box_apps; eauto. eauto. eauto. eauto. eauto.
    + auto.
  - inv He.
    + eexists. split; eauto. now econstructor.
    + eexists. split. 2: now econstructor.
      econstructor; eauto.
  - assert (Hty' := Hty).
    assert (Hty'' : Σ ;;; [] |- mkApps (tConstruct i k u) l' : T). {
      eapply subject_reduction. eauto. eapply Hty.
      eapply PCUICReduction.red_mkApps.
      eapply wcbeval_red; eauto.
      eapply All2_impl. exact X. intros.
      eapply wcbeval_red; eauto.
    }
    eapply erases_mkApps_inv in Hty; eauto.
    destruct Hty as [ (? & ? & ? & ? & [] & ? & ? & ?) | (? & ? & ? & ? & ?)].
    + subst. eapply All2_app_inv in X as ( [] & [] & ?). subst.
      assert (∥isErasable Σ [] (mkApps (tConstruct i k u) (l ++ l0))∥).
      rewrite <- mkApps_nested.
      eapply Is_type_app. eauto. econstructor.
      rewrite mkApps_nested. eauto.
      eapply Is_type_red. eauto.
      eapply PCUICReduction.red_mkApps.
      eapply wcbeval_red; eauto.
      eapply All2_impl. exact a. intros.
      eapply wcbeval_red; eauto. eauto. destruct H1.
      exists tBox.
      split. 2:{
        eapply type_mkApps_inv in Hty' as (? & ? & [] & ?); eauto.
        assert (exists x5, Forall2 (EWcbvEval.eval Σ') x1 x5) as [x8]. {
          eapply All2_app_inv in H0 as ([] & ? & ?). destruct p.
          clear a2. subst.
          assert (forall x n, nth_error x0 n = Some x -> ∑ T,  Σ;;; [] |- x : T).
          { intros. eapply typing_spine_inv with (arg := n + #|x|) in t0 as [].
            2:{ rewrite nth_error_app2. 2:omega. rewrite Nat.add_sub. eauto. }
            eauto.
          }
          clear - X1 a1 H3. revert X1 x1 H3; induction a1; intros.
          ** inv H3. exists []; eauto.
          ** inv H3. destruct (X1 x 0 eq_refl).
             eapply r in t as (? & ? & ?); eauto.
             eapply IHa1 in H4 as (? & ?); eauto.
             intros. eapply (X1 x2 (S n)). eassumption.
        }

        eapply eval_box_apps. eauto. now econstructor. }
      eauto.
    + subst.
      eapply type_mkApps_inv in Hty' as (? & ? & [] & ?); eauto.
      eapply IHeval in H2 as (? & ? & ?); eauto.
      enough (exists l'', Forall2 (erases Σ []) l' l'' /\ Forall2 (Ee.eval Σ') x0 l'').
      * destruct H4 as [l''].
        inv H1.
        -- exists (EAst.mkApps (EAst.tConstruct i k) l''). split.
           eapply erases_mkApps; eauto.
           firstorder. eapply Ee.eval_mkApps_cong; eauto. firstorder.
        -- eapply Is_type_app in X0 as []; eauto. exists tBox.
           split.
           econstructor. eauto. eauto.
           eapply eval_box_apps. intuition eauto. eauto.
      * clear - t0 H0 H3. revert x1 x0 H3 t0. induction H0; intros.
        -- inv H3. eauto.
        -- inv H3. inv t0. eapply IHAll2 in H5 as (? & ? & ?).
           eapply r in H2 as (? & ? & ?); eauto.
           eauto. *)
Admitted.
