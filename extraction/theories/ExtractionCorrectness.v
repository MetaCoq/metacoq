(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From MetaCoq.Template Require Import config utils monad_utils BasicAst AstUtils.
From MetaCoq.Extraction Require Import EAst ELiftSubst ETyping EWcbvEval Extract Prelim ESubstitution EInversion EArities.
From MetaCoq.PCUIC Require Import PCUICTyping PCUICAst PCUICAstUtils PCUICInduction  PCUICWeakening PCUICSubstitution PCUICChecker PCUICRetyping PCUICMetaTheory PCUICWcbvEval PCUICSR  PCUICClosed PCUICInversion.


Require Import String.
Local Open Scope string_scope.
Set Asymmetric Patterns.
Import MonadNotation.

Module E := EAst.

Require Import Lia.

Existing Instance config.default_checker_flags.
Module PA := PCUICAst.
Module P := PCUICWcbvEval.

Lemma typing_subst_instance :
  forall Σ : global_env_ext, wf Σ ->
  forall Γ, wf_local Σ Γ ->
  forall t T, Σ ;;; Γ |- t : T ->
    forall u univs,
      consistent_instance_ext (Σ.1,univs) (Σ.2) u ->
      (Σ.1,univs) ;;; PCUICUnivSubst.subst_instance_context u Γ |- PCUICUnivSubst.subst_instance_constr u t : PCUICUnivSubst.subst_instance_constr u T.
Proof.
  apply (typing_ind_env (fun Σ Γ t T =>
                           forall u univs,
      consistent_instance_ext (Σ.1,univs) (Σ.2) u ->
      (Σ.1,univs) ;;; _ |- PCUICUnivSubst.subst_instance_constr u t : PCUICUnivSubst.subst_instance_constr u T)); intros; cbn -[PCUICUnivSubst.subst_instance_constr] in *.
Admitted.

(** ** Prelim on arities and proofs *)

Lemma isArity_subst_instance u T :
  isArity T ->
  isArity (PCUICUnivSubst.subst_instance_constr u T).
Proof.
  induction T; cbn; intros; tauto.
Qed.

Lemma isErasable_subst_instance (Σ : global_env_ext) Γ T univs u :
  wf Σ ->  wf_local Σ Γ ->
  isErasable Σ Γ T ->
  consistent_instance_ext (Σ.1,univs) (Σ.2) u ->
  isErasable (Σ.1,univs) (PCUICUnivSubst.subst_instance_context u Γ) (PCUICUnivSubst.subst_instance_constr u T).
Proof.
  intros. destruct X1 as (? & ? & [ | (? & ? & ?)]).
  - eapply typing_subst_instance in t; eauto.
    eexists. split. eauto. left. eapply isArity_subst_instance. eauto.
  - eapply typing_subst_instance in t; eauto.
    eexists. split. eauto. right.
    eapply typing_subst_instance in t0; eauto.
    eexists. split. eauto.

    Lemma is_prop_subst_instance:
      forall (u : universe_instance) (x0 : universe), is_prop_sort x0 -> is_prop_sort (UnivSubst.subst_instance_univ u x0).
    Proof.
      intros u x0 i. destruct x0; cbn in *; try congruence.
      unfold is_prop_sort in *. unfold Universe.level in *.
      destruct t. destruct t; cbn in *; try congruence.
      destruct b; cbn in *; try congruence.
    Qed.
    now eapply is_prop_subst_instance.
Qed.

(** * Correctness of erasure  *)

Notation "Σ ;;; Γ |- s ▷ t" := (eval Σ Γ s t) (at level 50, Γ, s, t at next level) : type_scope.
Notation "Σ ⊢ s ▷ t" := (Ee.eval Σ s t) (at level 50, s, t at next level) : type_scope.

(** ** Erasure is stable under context conversion *)

Lemma Is_type_conv_context (Σ : global_env_ext) (Γ : context) t (Γ' : context) :
  wf Σ -> wf_local Σ Γ ->
    conv_context Σ Γ Γ' -> isErasable Σ Γ t -> isErasable Σ Γ' t.
Proof.
  intros.
  destruct X2 as (? & ? & ?).
  exists x. split. eapply context_conversion; eauto.
  destruct s as [? | [u []]].
  - eauto.
  - right. exists u. split; eauto. eapply context_conversion; eauto.
Qed.

Lemma erases_context_conversion :
env_prop
  (fun (Σ : PCUICAst.global_env_ext) (Γ : PCUICAst.context) (t T : PCUICAst.term) =>
      forall Γ' : PCUICAst.context, conv_context Σ Γ Γ' -> forall t', erases Σ Γ t t' -> erases Σ Γ' t t').
Proof.
  apply typing_ind_env; intros Σ wfΣ Γ wfΓ; intros **; rename_all_hyps.
  all: match goal with [ H : erases _ _ ?a _ |- ?G ] => tryif is_var a then idtac else inv H end.
  Hint Resolve isErasable_subst_instance.
  Hint Resolve Is_type_conv_context.
  all: try now (econstructor; eauto).
  - econstructor. eapply h_forall_Γ'0.
    econstructor. eauto. econstructor. exists s1.
    eapply context_conversion; eauto. eapply conv_refl.
    eassumption.
  - econstructor. eauto. eapply h_forall_Γ'1.
    econstructor. eauto. econstructor. exists s1.
    eapply context_conversion; eauto. eapply conv_refl.
    eassumption.
  - econstructor. eauto. eauto.
    eapply All2_All_left in X3. 2:{ intros. destruct X1. exact e. }

    eapply All2_impl. eapply All2_All_mix_left.
    all: firstorder.
  - econstructor.

    eapply All2_impl. eapply All2_All_mix_left. eassumption. eassumption.
    intros. cbn in *.
    decompose [prod] X2. repeat split; eauto.
    eapply b0. 2:eauto. subst types.

    eapply conv_context_app. eauto. eapply typing_wf_local; eauto. eauto.
  - econstructor.

    eapply All2_impl. eapply All2_All_mix_left. eassumption. eassumption.
    intros. cbn in *.
    decompose [prod] X2. repeat split; eauto.
    eapply b0. 2:eauto. subst types.

    eapply conv_context_app. eauto. eapply typing_wf_local; eauto. eauto.
  - eauto.
Qed.

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

Lemma erases_subst_instance_constr :
  forall Σ : global_env_ext, wf Σ ->
  forall Γ, wf_local Σ Γ ->
  forall t T, Σ ;;; Γ |- t : T ->
    forall t' u univs,
      consistent_instance_ext (Σ.1,univs) (Σ.2) u ->
    Σ ;;; Γ |- t ⇝ℇ t' ->
    (Σ.1,univs) ;;; (PCUICUnivSubst.subst_instance_context u Γ) |- PCUICUnivSubst.subst_instance_constr u t ⇝ℇ t'.
Proof.
  apply (typing_ind_env (fun Σ Γ t T =>
                               forall t' u univs,
      consistent_instance_ext (Σ.1,univs) (Σ.2) u ->
    Σ ;;; Γ |- t ⇝ℇ t' ->
    (Σ.1,univs) ;;; (PCUICUnivSubst.subst_instance_context u Γ) |- PCUICUnivSubst.subst_instance_constr u t ⇝ℇ t')); intros; cbn -[PCUICUnivSubst.subst_instance_constr] in *.
  all: match goal with [ H : erases _ _ ?a _ |- ?G ] => tryif is_var a then idtac else inv H end.
  Hint Resolve isErasable_subst_instance.
  all: try now (econstructor; eauto).
  - cbn. econstructor.
    eapply H0 in H7; eauto.
  - cbn. econstructor.
    eapply H0 in H9; eauto.
    eapply H1 in H10. exact H10. eauto.
  - cbn. econstructor; eauto.
    eapply All2_map_left.
    eapply All2_impl. eapply All2_All_mix_left.
    eapply All2_All_left. exact X3. intros. destruct X4.
    exact e. exact H15.
    intros; cbn in *. destruct H. destruct p0. split; eauto.
  - cbn. econstructor; eauto.
    eapply All2_map_left.
    eapply All2_impl. eapply All2_All_mix_left. eassumption.
    exact H6.
    intros; cbn in *. destruct X1. destruct p0. destruct p0.
    destruct p. destruct p. repeat split; eauto.
    eapply e2 in e1.
    unfold PCUICUnivSubst.subst_instance_context in *.
    unfold map_context in *. rewrite map_app in *. subst types. 2:eauto.
    eapply erases_ctx_ext. eassumption. unfold app_context.
    f_equal.
    eapply fix_context_subst_instance.
  - cbn. econstructor; eauto.
    eapply All2_map_left.
    eapply All2_impl. eapply All2_All_mix_left. eassumption.
    exact H6.
    intros; cbn in *. destruct X1. destruct p0. destruct p0.
    destruct p. repeat split; eauto.
    eapply e2 in e1. unfold PCUICUnivSubst.subst_instance_context in *.
    unfold map_context in *. rewrite map_app in *. subst types. 2:eauto.
    eapply erases_ctx_ext. eassumption. unfold app_context.
    f_equal.
    eapply fix_context_subst_instance.
  - eauto.
Qed.

Lemma declared_constant_inj Σ c decl1 decl2 :
  declared_constant Σ c decl1 -> declared_constant Σ c decl2 -> decl1 = decl2.
Proof.
  intros. inv H. inv H0. rewrite H1 in H2. now inv H2.
Qed.

(** ** Erasure and applications  *)

Lemma erases_App (Σ : global_env_ext) Γ f L T t :
  Σ ;;; Γ |- tApp f L : T ->
  erases Σ Γ (tApp f L) t ->
  (t = tBox × squash (isErasable Σ Γ (tApp f L)))
  \/ exists f' L', t = E.tApp f' L' /\
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
  erases Σ Γ (mkApps f L) (E.mkApps f' L').
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
                t = E.mkApps tBox L2'
  )
  \/ exists f' L', t = E.mkApps f' L' /\
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
  exists decl', ETyping.lookup_env Σ' c = Some (E.ConstantDecl c decl') /\
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
        (* destruct decl. cbn. *)
        (* (* admit. admit. *)  *)
        (* 2:eapply PCUICWeakeningEnv.wf_extends. *)
        (* eassumption. now eexists [_]. eauto. *)
        { inv X. cbn in X1.
          eassumption. }
      * eassumption.
      * destruct ?; tauto.
    + edestruct IHerases_global_decls as (decl' & ? & ?).
      eapply PCUICWeakeningEnv.wf_extends.
      eassumption. now eexists [_]. eauto.
      destruct decl. cbn in *.
      exists decl'. split. eauto.
      unfold erases_constant_body in *. clear H. destruct ?. destruct ?.
      eapply (@erases_extends (_, _)). 6: eassumption.
        eapply PCUICWeakeningEnv.wf_extends.
        eassumption. now eexists [_]. eauto.
        eapply (PCUICWeakeningEnv.declared_constant_inv Σ) in H0; eauto.
        unfold on_constant_decl in H0. rewrite E0 in H0. unfold lift_typing in H0. exact H0.
        eapply PCUICWeakeningEnv.weaken_env_prop_typing. eapply PCUICWeakeningEnv.wf_extends. eauto.
        eexists [_]. reflexivity. eapply PCUICWeakeningEnv.wf_extends. eauto. now eexists [_].
        eauto. now eexists [_].
      * tauto.
      * destruct ?; tauto.
  - destruct ?.
    + inv H0.
    + edestruct IHerases_global_decls as (decl' & ? & ?).
      eapply PCUICWeakeningEnv.wf_extends.
      eassumption. now eexists [_]. eauto.
      exists decl'. split. eauto.
      unfold erases_constant_body in *. clear H. destruct ?. destruct ?.
      * eapply (@erases_extends (_,_)). 6: eassumption.
        eapply PCUICWeakeningEnv.wf_extends.
        eassumption. now eexists [_]. eauto.
        eapply (PCUICWeakeningEnv.declared_constant_inv Σ) in H0; eauto.
        unfold on_constant_decl in H0. rewrite E0 in H0. unfold lift_typing in H0. eassumption.
        eapply PCUICWeakeningEnv.weaken_env_prop_typing. eapply PCUICWeakeningEnv.wf_extends. eauto.
        eexists [_]. reflexivity. eapply PCUICWeakeningEnv.wf_extends. eauto. now eexists [_].
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
          econstructor. eassumption. eauto. eapply c0. auto. auto. }
      inv Hvf'.
      * assert (Σ;;; [] |- PCUICLiftSubst.subst1 a' 0 b ⇝ℇ subst1 vu' 0 t').
        eapply (erases_subst Σ [] [PCUICAst.vass na t] [] b [a'] t'); eauto.
        econstructor. econstructor. rewrite parsubst_empty. eassumption.
        eapply IHeval3 in H2 as (v' & Hv' & He_v').
        -- exists v'. split; eauto.
           econstructor; eauto.
        -- eapply substitution0; eauto. 
      * exists tBox. split.
        eapply Is_type_lambda in X1; eauto. destruct X1.  econstructor.
        eapply (is_type_subst Σ [] [PCUICAst.vass na _] [] _ [a']) in X1.
        cbn in X1.
        eapply Is_type_eval.
        eauto. eapply H1. eassumption.
        all: eauto. econstructor. econstructor. rewrite parsubst_empty.
        eauto. econstructor. eauto.
    + exists tBox. split. 2:econstructor; eauto.
      econstructor.
      eapply Is_type_eval; eauto.
  - assert (Hty' := Hty).
    assert (Σ ;;; [] |- tLetIn na b0 t b1 ▷ res) by eauto.
    eapply inversion_LetIn in Hty' as (? & ? & ? & ? & ? & ?).

    inv He.
    + eapply IHeval1 in H6 as (vt1' & Hvt2' & He_vt1'); eauto.
      assert (Hc :conv_context Σ ([],, vdef na b0 t) [vdef na b0' t]). {
        econstructor. econstructor. econstructor. econstructor. eauto. eapply subject_reduction_eval; eauto.
        eapply PCUICCumulativity.red_conv. 
        eapply wcbeval_red; eauto. eapply conv_refl.
      }
      assert (Σ;;; [vdef na b0' t] |- b1 : x0). {
        cbn in *. eapply context_conversion. 3:eauto. all:cbn; eauto.
        econstructor. all: cbn; eauto.
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
        econstructor. all: cbn; eauto.
      }
      eapply IHeval2 in H1 as (vres & Hvres & Hty_vres).
      2:{ eapply substitution_let; eauto. }
      exists vres. split. eauto. econstructor; eauto.
    + exists tBox. split. 2:econstructor; eauto.
      econstructor. eapply Is_type_eval; eauto.
  - inv isdecl.
  - inv isdecl.
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
        eapply H10 in X0 as []; eauto. 2: exists []; now destruct Σ.

        destruct (ind_ctors idecl'). cbn in H4. destruct c; inv H2.
        destruct l; cbn in *; try omega. destruct c as [ | []]; cbn in H2; inv H2.

        destruct btys as [ | ? []]; cbn in H3; try omega. clear H3 H4. destruct H7.
        (* eapply H7 in d1. *) inv a. inv X2. inv H12. inv H8. destruct H4. destruct x4, y; cbn in *; subst.
        destruct X1. subst. destruct p0; cbn in *.

        edestruct (IHeval2) as (? & ? & ?).
        eapply subject_reduction. eauto. exact Hty.
        etransitivity.
        eapply PCUICReduction.red_case_c. eapply wcbeval_red. eauto.
        econstructor. econstructor. econstructor.

        unfold iota_red. cbn.
        eapply erases_mkApps. eauto.
        instantiate (1 := repeat tBox _).
        eapply All2_Forall2.
        eapply All2_impl.
        eapply All2_All_mix_left. eassumption.
        2:{ intros. destruct X1. assert (y = tBox). exact y0. subst. econstructor.
            now eapply isErasable_Proof. }

        eapply All2_right_triv. 2: now rewrite repeat_length.

        now eapply All_repeat.

        (* destruct x4; cbn in e2; subst. destruct X2. destruct p0; cbn in e2; subst. cbn in *.  destruct y.  *)
        exists x4. split; eauto. eapply eval_iota_sing.  2:eauto.
        pose proof (Ee.eval_to_value _ _ _ He_v').
        eapply value_app_inv in H4. subst. eassumption.

        eapply tCase_length_branch_inv in extr_env_wf'0.
        2:{ eapply subject_reduction. eauto.
            exact Hty.
            eapply PCUICReduction.red_case_c. eapply wcbeval_red. eauto.  }
        2: reflexivity.

        enough (#|skipn (ind_npars mdecl') (x1 ++ x2)| = n) as <- by eauto.
        rewrite skipn_length. rewrite extr_env_wf'0. omega.
        rewrite extr_env_wf'0. omega. eauto.
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
           eapply H10 in X0 as []; eauto. 2: exists []; now destruct Σ.

           destruct (ind_ctors idecl'). cbn in H4. destruct c; inv H2.
           destruct l; cbn in *; try omega. destruct c as [ | []]; cbn in H2; inv H2.

           destruct btys as [ | ? []]; cbn in H3; try omega. clear H3 H4. destruct H8.
           (* eapply H7 in d1. *) inv a. inv X2. inv H12. inv H9. destruct H4. destruct x1, y; cbn in *; subst.
           destruct X1. subst. destruct p0; cbn in *. destruct x3. inv e. inv Hnth. cbn in *.

           edestruct (IHeval2) as (? & ? & ?).
           eapply subject_reduction. eauto. exact Hty.
           etransitivity.
           eapply PCUICReduction.red_case_c. eapply wcbeval_red. eauto.
           econstructor. econstructor. econstructor.

           eapply erases_mkApps. eauto.
           instantiate (1 := repeat tBox _).
           eapply All2_Forall2.
           eapply All2_impl.
           eapply All2_All_mix_left. eassumption.
           2:{ intros. destruct X1. assert (y = tBox). exact y0. subst. econstructor.
               now eapply isErasable_Proof. }

           eapply All2_right_triv. 2:now rewrite repeat_length.
           now eapply All_repeat.

           exists x1. split; eauto.
           eapply eval_iota_sing.
           pose proof (Ee.eval_to_value _ _ _ He_v').
           eapply value_app_inv in H4. subst. eassumption.
           reflexivity. cbn in *.
           enough (#|skipn (ind_npars mdecl') args| = n0) as <- by eauto.

           eapply tCase_length_branch_inv in extr_env_wf'0.
           2:{ eapply subject_reduction. eauto.
               exact Hty.
               eapply PCUICReduction.red_case_c. eapply wcbeval_red. eauto.  }
           2: reflexivity.

           enough (#|skipn (ind_npars mdecl') args| = n0) as <- by eauto.
           rewrite skipn_length. rewrite extr_env_wf'0. omega.
           rewrite extr_env_wf'0. omega. eauto.
    + exists tBox. split. econstructor.
      eapply Is_type_eval; eauto. econstructor; eauto.
  - assert (Hty' := Hty).
    assert (Hunf := H).
    assert (Hcon := H1).
    assert (Σ ;;; [] |- mkApps (tFix mfix idx) args ▷ res) by eauto.
    eapply type_mkApps_inv in Hty' as (? & ? & [] & ?); eauto.
    assert (HT := t).
    eapply inversion_Fix in t as (? & ? & ? & ? & ? & ?).
    unfold unfold_fix in H. rewrite e in H. inv H. 

    eapply erases_mkApps_inv in He as [(? & ? & ? & ? & [] & ? & ? & ?) | (? & ? & ? & ? & ?)]; eauto.
    + subst. assert (X100 := X1). eapply Is_type_app in X100 as[].
      exists tBox. split. 2:eapply eval_box_apps; econstructor; eauto.
      econstructor.
      eapply Is_type_eval. eauto. eassumption.
      rewrite <- mkApps_nested.  eassumption. eauto. econstructor.
      rewrite mkApps_nested; eauto.
    + subst.
      destruct ?; inv H4.
      inv H3.
      * assert (Hmfix' := H7).
        eapply All2_nth_error_Some in H7 as (? & ? & ? & ? & ?); eauto.
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
              exists x1. split. eauto. econstructor. unfold ETyping.unfold_fix.
              rewrite e0. reflexivity.
              eassumption.
              all:eauto.
              ** unfold is_constructor in *.
                 destruct ?; inv H1.
                 unfold is_constructor_or_box.
                 eapply Forall2_nth_error_Some in H as (? & ? & ?); eauto.
                 rewrite H.

                 unfold isConstruct_app in H8.
                 destruct (decompose_app t) eqn:EE.
                 assert (E2 : fst (decompose_app t) = t1) by now rewrite EE.
                 destruct t1.
                 all:inv H8.
                 (* erewrite <- PCUICConfluence.fst_decompose_app_rec in E2. *)

                 pose proof (decompose_app_rec_inv EE).
                 cbn in H7. subst.
                 assert (∑ T, Σ ;;; [] |- mkApps (tConstruct ind n ui) l : T) as [T' HT'].
                 { eapply typing_spine_eval in t0; eauto.
                   eapply typing_spine_inv in t0; eauto. 
                   eapply PCUICValidity.validity; eauto.
                 }
                 eapply erases_mkApps_inv in H1.
                 destruct H1 as [ (? & ? & ? & ? & [] & ? & ? & ?) | (? & ? & ? & ? & ?) ].
                 --- subst.
                     eapply nth_error_forall in Hv; eauto.
                     eapply value_app_inv in Hv. subst. reflexivity.
                 --- subst. inv H7.
                     +++ eapply nth_error_forall in Hv; eauto.
                         destruct x6 using rev_ind; cbn - [EAstUtils.decompose_app]. reflexivity.
                         rewrite emkApps_snoc at 1.
                         generalize (x6 ++ [x4])%list. clear. intros.
                         rewrite Prelim.decompose_app_mkApps. reflexivity.
                         reflexivity.
                     +++ eapply nth_error_forall in Hv; eauto.
                         eapply value_app_inv in Hv. subst. eauto.
                 --- eauto.
                 --- eauto.
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
           ++ eapply subslet_fix_subst. eassumption.
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
        eapply eval_box_apps. econstructor. eauto. eauto. econstructor. eauto.
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
        eapply PCUICWeakeningEnv.declared_constant_inv in H'; eauto.
        unfold on_constant_decl in H'. rewrite H0 in H'. red in H'.
        eapply typing_subst_instance in H'; eauto.
        eapply PCUICWeakeningEnv.weaken_env_prop_typing.
      * eapply PCUICWeakeningEnv.declared_constant_inv in H'; eauto.
        unfold on_constant_decl in H'. rewrite H0 in H'. cbn in *.
        2:eapply PCUICWeakeningEnv.weaken_env_prop_typing.
        eapply erases_subst_instance_constr in H'; eauto.        
      * destruct H3. exists x0. split; eauto. econstructor; eauto.
    + exists tBox. split. econstructor.
      eapply Is_type_eval. 3: eassumption. eauto. eauto. econstructor. eauto.
  - pose (Hty' := Hty).
    eapply inversion_Proj in Hty' as (? & ? & ? & [] & ? & ? & ? & ? & ?).
    inv He.
    + rename H7 into H6. eapply IHeval1 in H6 as (vc' & Hvc' & Hty_vc'); eauto.
      eapply erases_mkApps_inv in Hvc'; eauto.
      2: eapply subject_reduction_eval; eauto.
      destruct Hvc' as [ (? & ? & ? & ? & [] & ? & ? & ?) | (? & ? & ? & ? & ?)]; subst.
      * exists tBox. split.

        eapply Is_type_app in X as []; eauto. 2:{ rewrite mkApps_nested. eapply subject_reduction_eval; eauto. }
        rewrite mkApps_nested in X.

        eapply tConstruct_no_Type in X. eapply H5 in X as [? []]; eauto.
        2: now destruct d. 2: now exists []; destruct Σ.

        econstructor.
        eapply Is_type_eval. eauto. eauto.
        eapply nth_error_all.
        eapply nth_error_skipn. eassumption.
        eapply All_impl. assert (pars = ind_npars x0). destruct d as (? & ? & ?). now rewrite H9. subst.
        eassumption.
        eapply isErasable_Proof. eauto.

        eapply eval_proj_box.
        pose proof (Ee.eval_to_value _ _ _ Hty_vc').
        eapply value_app_inv in H3. subst. eassumption.
      * rename H5 into Hinf.
        rename H6 into H5.
        eapply Forall2_nth_error_Some in H5 as (? & ? & ?); eauto.
        assert (Σ ;;; [] |- mkApps (tConstruct i k u) args : mkApps (tInd i x) x2).
        eapply subject_reduction_eval; eauto.
        eapply type_mkApps_inv in X as (? & ? & [] & ?); eauto.
        eapply typing_spine_inv in t2 as []; eauto.
        eapply IHeval2 in H5 as (? & ? & ?); eauto.
        inv H4.
        -- exists x9. split; eauto. econstructor. eauto.
           rewrite <- nth_default_eq. unfold nth_default. now rewrite H3.
        -- exists tBox. split.


           eapply Is_type_app in X as []; eauto. 2:{ eapply subject_reduction_eval. 3: eauto. eauto. eauto. }
           
           eapply tConstruct_no_Type in X. eapply Hinf in X as [? []]; eauto.
           2: now destruct d. 2: now exists []; destruct Σ.

           econstructor.
           eapply Is_type_eval. eauto. eauto.
           eapply nth_error_all.
           eapply nth_error_skipn. eassumption.
           eapply All_impl. assert (pars = ind_npars x0). destruct d as (? & ? & ?). now rewrite H9. subst.
           eassumption.
           eapply isErasable_Proof. eauto.

           eapply eval_proj_box.
           pose proof (Ee.eval_to_value _ _ _ Hty_vc').
           eapply value_app_inv in H4. subst. eassumption.
    + exists tBox. split. econstructor.
      eapply Is_type_eval. 3: eassumption. eauto. eauto. econstructor. eauto.
  - inv He.
    + eexists. split; eauto. econstructor.
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
      split. 2:{ eapply eval_box_apps. now econstructor. }
      econstructor. eauto.      
    + subst.  
      eapply IHeval in H2 as (? & ? & ?).
      inv H1. eapply Is_type_app in X0 as [].
      exists tBox.
      split. econstructor. 
      eauto. 
      eapply eval_box_apps; eauto. eauto. econstructor. eauto. eauto.
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
      split. 2:{ eapply eval_box_apps. now econstructor. }
      eauto.
    + subst.
      eapply type_mkApps_inv in Hty' as (? & ? & [] & ?); eauto.
      eapply IHeval in H2 as (? & ? & ?); eauto.
      enough (exists l'', Forall2 (erases Σ []) l' l'' /\ Forall2 (Ee.eval Σ') x0 l'').
      * destruct H4 as [l''].
        inv H1.
        -- exists (E.mkApps (E.tConstruct i k) l''). split.
           eapply erases_mkApps; eauto.
           firstorder. econstructor; firstorder.
        -- eapply Is_type_app in X0 as []; eauto. exists tBox.
           split.
           econstructor. eauto. eauto.
           eapply eval_box_apps. eauto.
      * clear - t0 H0 H3. revert x1 x0 H3 t0. induction H0; intros.
        -- inv H3. eauto.
        -- inv H3. inv t0. eapply IHAll2 in H5 as (? & ? & ?).
           eapply r in H2 as (? & ? & ?); eauto.
           eauto.
Qed.
