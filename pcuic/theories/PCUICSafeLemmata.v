(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICConfluence
     PCUICCumulativity PCUICSR PCUICPosition PCUICEquality PCUICNameless
     PCUICAlpha PCUICNormal PCUICInversion PCUICReduction PCUICSubstitution
     PCUICConversion PCUICContextConversion PCUICValidity
     PCUICArities PCUICWeakeningEnv PCUICGeneration
     PCUICParallelReductionConfluence.

Require Import ssreflect ssrbool.
Require Import Equations.Prop.DepElim.
Set Equations With UIP.

Local Set Keyed Unification.

Set Default Goal Selector "!".

Section Lemmata.
  Context {cf : checker_flags}.
  Context (flags : RedFlags.t).

  (*
  Lemma eq_term_zipc_inv :
    forall Σ φ u v π,
      eq_term Σ φ (zipc u π) (zipc v π) ->
      eq_term Σ φ u v.
  Proof.
    intros Σ φ u v π h.
    induction π in u, v, h |- *.
    all: try solve [
             simpl in h ; try apply IHπ in h ;
             cbn in h ; inversion h ; subst ; assumption
           ].
    - simpl in h. apply IHπ in h.
      inversion h. subst.
      match goal with
      | h : All2 _ _ _ |- _ => rename h into a
      end.
      apply All2_app_inv_both in a. 2: reflexivity.
      destruct a as [_ a]. inversion a. subst.
      intuition eauto.
    - simpl in h. apply IHπ in h.
      inversion h. subst.
      match goal with
      | h : All2 _ _ _ |- _ => rename h into a
      end.
      apply All2_app_inv_both in a. 2: reflexivity.
      destruct a as [_ a]. inversion a. subst.
      intuition eauto.
    - simpl in h. apply IHπ in h.
      inversion h. subst.
      match goal with
      | h : All2 _ _ _ |- _ => rename h into a
      end.
      apply All2_app_inv_both in a. 2: reflexivity.
      destruct a as [_ a]. inversion a. subst.
      intuition eauto.
  Qed.

  Lemma eq_term_zipx_inv :
    forall φ Γ u v π,
      eq_term φ (zipx Γ u π) (zipx Γ v π) ->
      eq_term φ u v.
  Proof.
    intros Σ Γ u v π h.
    eapply eq_term_zipc_inv.
    eapply eq_term_it_mkLambda_or_LetIn_inv.
    eassumption.
  Qed.*)

  Instance All2_eq_refl Σ Re : 
    RelationClasses.Reflexive Re ->
    CRelationClasses.Reflexive (All2 (eq_term_upto_univ Σ Re Re)).
  Proof.
    intros h x. apply All2_same. reflexivity.
  Qed.

  Instance All2_br_eq_refl Σ Re :
    RelationClasses.Reflexive Re ->
    CRelationClasses.Reflexive (All2
      (fun x y : branch term =>
        eq_context_upto Σ Re Re (bcontext x) (bcontext y) *
        eq_term_upto_univ Σ Re Re (bbody x) (bbody y))).
  Proof.
    intros h x.
    apply All2_same; split; reflexivity.
  Qed.

  (*
  Lemma eq_term_upto_univ_zipc :
    forall Σ Re u v π,
      RelationClasses.Reflexive Re ->
      eq_term_upto_univ Σ Re Re u v ->
      eq_term_upto_univ Σ Re Re (zipc u π) (zipc v π).
  Proof.
    intros Σ Re u v π he h.
    induction π in u, v, h |- *.
    all: try solve [
               simpl ; try apply IHπ ;
               cbn ; constructor ; try reflexivity; try apply eq_term_upto_univ_refl ; assumption
             ].
    - assumption.
    - simpl. apply IHπ. constructor.
      + eapply eq_term_eq_term_napp; auto. apply _.
      + apply eq_term_upto_univ_refl; assumption.
    - simpl. apply IHπ. constructor.
      apply All2_app.
      + apply All2_same.
        intros. split ; auto. split; [split|]; auto. all: apply eq_term_upto_univ_refl.
        all: assumption.
      + constructor.
        * simpl. intuition eauto. reflexivity.
        * apply All2_same.
          intros. split ; auto. splits. all: apply eq_term_upto_univ_refl.
          all: assumption.
    - simpl. apply IHπ. constructor.
      apply All2_app.
      + apply All2_same.
        intros. split ; auto. splits. all: apply eq_term_upto_univ_refl.
        all: assumption.
      + constructor.
        * simpl. intuition eauto. reflexivity.
        * apply All2_same.
          intros. split ; auto. splits. all: apply eq_term_upto_univ_refl.
          all: assumption.
    - simpl. apply IHπ. constructor.
      apply All2_app.
      + apply All2_same.
        intros. split ; [split|]; auto. split. all: apply eq_term_upto_univ_refl.
        all: assumption.
      + constructor.
        * simpl. intuition eauto. reflexivity.
        * apply All2_same.
          intros. splits ; auto. all: apply eq_term_upto_univ_refl.
          all: assumption.
    - simpl. apply IHπ. constructor.
      apply All2_app.
      + apply All2_same.
        intros. splits ; auto. all: apply eq_term_upto_univ_refl.
        all: assumption.
      + constructor.
        * simpl. intuition eauto. reflexivity.
        * apply All2_same.
          intros. splits ; auto. all: apply eq_term_upto_univ_refl.
          all: assumption.
    - simpl. apply IHπ.
      constructor; try reflexivity.
      splits; simpl; try reflexivity.
      eapply All2_app; [reflexivity|].
      constructor; [tas|reflexivity].
    - simpl. apply IHπ.
      constructor; easy.
    - simpl. apply IHπ.
      constructor; try easy.
      apply All2_app; try reflexivity.
      constructor; easy.
  Qed.

  Lemma eq_term_zipc :
    forall (Σ : global_env_ext) u v π,
      eq_term Σ (global_ext_constraints Σ) u v ->
      eq_term Σ (global_ext_constraints Σ) (zipc u π) (zipc v π).
  Proof.
    intros Σ u v π h.
    eapply eq_term_upto_univ_zipc.
    - intro. eapply eq_universe_refl.
    - assumption.
  Qed.
*)

  Lemma eq_term_upto_univ_zipp :
    forall Σ Re u v π,
      RelationClasses.Reflexive Re ->
      eq_term_upto_univ Σ Re Re u v ->
      eq_term_upto_univ Σ Re Re (zipp u π) (zipp v π).
  Proof.
    intros Σ Re u v π he h.
    unfold zipp.
    case_eq (decompose_stack π). intros l ρ e.
    eapply eq_term_upto_univ_mkApps.
    - apply eq_term_eq_term_napp; try assumption; apply _.
    - apply All2_same. intro. reflexivity.
  Qed.

  Lemma eq_term_zipp :
    forall (Σ : global_env_ext) u v π,
      eq_term Σ (global_ext_constraints Σ) u v ->
      eq_term Σ (global_ext_constraints Σ) (zipp u π) (zipp v π).
  Proof.
    intros Σ u v π h.
    eapply eq_term_upto_univ_zipp.
    - intro. eapply eq_universe_refl.
    - assumption.
  Qed.

  (*
  Lemma eq_term_upto_univ_zipx :
    forall Σ Re Γ u v π,
      RelationClasses.Reflexive Re ->
      eq_term_upto_univ Σ Re Re u v ->
      eq_term_upto_univ Σ Re Re (zipx Γ u π) (zipx Γ v π).
  Proof.
    intros Σ Re Γ u v π he h.
    eapply eq_term_upto_univ_it_mkLambda_or_LetIn ; auto.
    eapply eq_term_upto_univ_zipc ; auto.
  Qed.

  Lemma eq_term_zipx :
    forall Σ φ Γ u v π,
      eq_term Σ φ u v ->
      eq_term Σ φ (zipx Γ u π) (zipx Γ v π).
  Proof.
    intros Σ Γ u v π h.
    eapply eq_term_upto_univ_zipx ; auto.
    intro. eapply eq_universe_refl.
  Qed.
*)


  (* red is the reflexive transitive closure of one-step reduction and thus
     can't be used as well order. We thus define the transitive closure,
     but we take the symmetric version.
   *)
  Inductive cored Σ Γ: term -> term -> Prop :=
  | cored1 : forall u v, red1 Σ Γ u v -> cored Σ Γ v u
  | cored_trans : forall u v w, cored Σ Γ v u -> red1 Σ Γ v w -> cored Σ Γ w u.

  Derive Signature for cored.

  Hint Resolve eq_term_upto_univ_refl : core.

  (* Lemma conv_context : *)
  (*   forall Σ Γ u v ρ, *)
  (*     wf Σ.1 -> *)
  (*     Σ ;;; Γ ,,, stack_context ρ |- u = v -> *)
  (*     Σ ;;; Γ |- zipc u ρ = zipc v ρ. *)
  (* Proof. *)
  (*   intros Σ Γ u v ρ hΣ h. *)
  (*   induction ρ in u, v, h |- *. *)
  (*   - assumption. *)
  (*   - simpl. eapply IHρ. eapply conv_App_l ; auto. *)
  (*   - simpl. eapply IHρ. eapply conv_App_r ; auto. *)
  (*   - simpl. eapply IHρ. eapply conv_App_r ; auto. *)
  (*   - simpl. eapply IHρ. eapply conv_Case_c ; auto. *)
  (*   - simpl. eapply IHρ. eapply conv_Proj_c ; auto. *)
  (*   - simpl. eapply IHρ. eapply conv_Prod_l ; auto. *)
  (*   - simpl. eapply IHρ. eapply conv_Prod_r ; auto. *)
  (*   - simpl. eapply IHρ. eapply conv_Lambda_l ; auto. *)
  (*   - simpl. eapply IHρ. eapply conv_Lambda_r ; auto. *)
  (*   - simpl. eapply IHρ. eapply conv_App_r ; auto. *)
  (* Qed. *)

  Context (Σ : global_env_ext).

  Inductive welltyped Σ Γ t : Prop :=
  | iswelltyped A : Σ ;;; Γ |- t : A -> welltyped Σ Γ t.

  Arguments iswelltyped {Σ Γ t A} h.

  Definition isType_welltyped {Γ T}
    : isType Σ Γ T -> welltyped Σ Γ T.
  Proof.
    intros []. now econstructor.
  Qed.
  Hint Resolve isType_welltyped : pcuic.

  Context (hΣ : ∥ wf Σ ∥).

  Lemma validity_wf {Γ t T} :
    ∥ Σ ;;; Γ |- t : T ∥ -> welltyped Σ Γ T.
  Proof.
    destruct hΣ as [wΣ]. intros [X].
    intros. eapply validity in X; try assumption.
    destruct X. now exists (tSort x).
  Defined.

  Lemma wat_welltyped {Γ T} :
    ∥ isType Σ Γ T ∥ -> welltyped Σ Γ T.
  Proof.
    destruct hΣ as [wΣ]. intros [X].
    now apply isType_welltyped.
  Defined.

  Lemma welltyped_alpha Γ u v :
      welltyped Σ Γ u ->
      eq_term_upto_univ [] eq eq u v ->
      welltyped Σ Γ v.
  Proof.
    intros [A h] e.
    destruct hΣ.
    exists A. eapply typing_alpha ; eauto.
  Qed.

  Lemma red_cored_or_eq :
    forall Γ u v,
      red Σ Γ u v ->
      cored Σ Γ v u \/ u = v.
  Proof.
    intros Γ u v h.
    induction h using red_rect'.
    - right. reflexivity.
    - destruct IHh.
      + left. eapply cored_trans ; eassumption.
      + subst. left. constructor. assumption.
  Qed.

  Lemma cored_it_mkLambda_or_LetIn :
    forall Γ Δ u v,
      cored Σ (Γ ,,, Δ) u v ->
      cored Σ Γ (it_mkLambda_or_LetIn Δ u)
               (it_mkLambda_or_LetIn Δ v).
  Proof.
    intros Γ Δ u v h.
    induction h.
    - constructor. apply red1_it_mkLambda_or_LetIn. assumption.
    - eapply cored_trans.
      + eapply IHh.
      + apply red1_it_mkLambda_or_LetIn. assumption.
  Qed.

  Lemma cored_welltyped :
    forall {Γ u v},
      welltyped Σ Γ u ->
      cored (fst Σ) Γ v u ->
      welltyped Σ Γ v.
  Proof.
    destruct hΣ as [wΣ]; clear hΣ.
    intros Γ u v h r.
    revert h. induction r ; intros h.
    - destruct h as [A h]. exists A.
      eapply subject_reduction1 ; eauto with wf.
    - specialize IHr with (1 := ltac:(eassumption)).
      destruct IHr as [A ?]. exists A.
      eapply subject_reduction1 ; eauto with wf.
  Qed.

  Lemma cored_trans' :
    forall {Γ u v w},
      cored Σ Γ u v ->
      cored Σ Γ v w ->
      cored Σ Γ u w.
  Proof.
    intros Γ u v w h1 h2. revert w h2.
    induction h1 ; intros z h2.
    - eapply cored_trans ; eassumption.
    - eapply cored_trans.
      + eapply IHh1. assumption.
      + assumption.
  Qed.

  (* This suggests that this should be the actual definition.
     ->+ = ->*.->
   *)
  Lemma cored_red_trans :
    forall Γ u v w,
      red Σ Γ u v ->
      red1 Σ Γ v w ->
      cored Σ Γ w u.
  Proof.
    intros Γ u v w h1 h2.
    revert w h2. induction h1 using red_rect'; intros w h2.
    - constructor. assumption.
    - eapply cored_trans.
      + eapply IHh1. eassumption.
      + assumption.
  Qed.

  Lemma cored_case :
    forall Γ ind p c c' brs,
      cored Σ Γ c c' ->
      cored Σ Γ (tCase ind p c brs) (tCase ind p c' brs).
  Proof.
    intros Γ ind p c c' brs h.
    revert ind p brs. induction h ; intros ind p brs.
    - constructor. constructor. assumption.
    - eapply cored_trans.
      + eapply IHh.
      + econstructor. assumption.
  Qed.

  Lemma cored_proj :
    forall Γ p c c',
      cored Σ Γ c c' ->
      cored Σ Γ (tProj p c) (tProj p c').
  Proof.
    intros Γ p c c' h.
    induction h in p |- *.
    - constructor. constructor. assumption.
    - eapply cored_trans.
      + eapply IHh.
      + econstructor. assumption.
  Qed.
  
  Arguments zip /.

  Lemma welltyped_fill_context_hole Γ π pcontext t :
    wf_local Σ (Γ,,, stack_context π,,, fill_context_hole pcontext t) ->
    welltyped Σ (Γ,,, stack_context π,,, context_hole_context pcontext) t.
  Proof.
    intros wfl.
    destruct pcontext as ((?&h)&?); simpl in *.
    apply wf_local_app_inv in wfl as (_&wf).
    apply wf_local_rel_app_inv in wf as (wf&_).
    destruct h; depelim wf; simpl in *.
    all: destruct l; econstructor; eauto.
  Qed.
  
  Lemma welltyped_context :
    forall Γ t,
      welltyped Σ Γ (zip t) ->
      welltyped Σ (Γ ,,, stack_context (snd t)) (fst t).
  Proof.
    destruct hΣ as [wΣ].
    intros Γ [t π] h. simpl.
    destruct h as [T h].
    induction π in Γ, t, T, h |- *.
    1: { econstructor; eauto. }
    destruct a; simpl in *.
    all: apply IHπ in h as (?&typ).
    all: try apply inversion_App in typ as (?&?&?&?&?&?); auto.
    all: try apply inversion_Proj in typ as (?&?&?&?&?&?&?&?&?); auto.
    all: try apply inversion_Prod in typ as (?&?&?&?&?); auto.
    all: try apply inversion_Lambda in typ as (?&?&?&?&?); auto.
    all: try apply inversion_LetIn in typ as (?&?&?&?&?&?); auto.
    all: try solve [econstructor; eauto].
    - apply inversion_Fix in typ as (?&?&?&?&?&?&?); eauto.
      destruct mfix as ((?&[])&?); simpl in *.
      + eapply All_app in a as (_&a).
        depelim a.
        eauto using isType_welltyped.
      + eapply All_app in a0 as (_&a0).
        depelim a0.
        rewrite fix_context_fix_context_alt in t0.
        rewrite map_app in t0.
        simpl in t0.
        rewrite app_context_assoc.
        econstructor; eauto.
    - apply inversion_CoFix in typ as (?&?&?&?&?&?&?); eauto.
      destruct mfix as ((?&[])&?); simpl in *.
      + eapply All_app in a as (_&a).
        depelim a.
        eauto using isType_welltyped.
      + eapply All_app in a0 as (_&a0).
        depelim a0.
        rewrite fix_context_fix_context_alt in t0.
        rewrite map_app in t0.
        simpl in t0.
        rewrite app_context_assoc.
        econstructor; eauto.
    - apply inversion_Case in typ as (?&?&?&cd&?); auto.
      rewrite app_context_assoc.
      destruct p; cbn in *.
      + destruct cd as [_ _ _ _ _ _ _ _ _ _ typ _ _ _ _].
        apply validity in typ as (?&typ).
        apply inversion_mkApps in typ as (?&_&spine); auto; simpl in *.
        clear -spine.
        rewrite -app_assoc -app_comm_cons in spine.
        revert spine; generalize (tSort x2); intros t' spine.
        induction params1 in spine, x3, t' |- *; cbn in *.
        * depelim spine.
          econstructor; eauto.
        * depelim spine; eauto.
      + destruct cd as [_ _ _ _ _ _ wfcontext _ _ _ _ _ _ _ _]; simpl in *.
        eauto using welltyped_fill_context_hole.
      + destruct cd as [? _ _ ? _ _ wfl cc typ _ _ _ _ _ _]; simpl in *.
        eapply conv_context_sym in cc; auto.
        eapply context_conversion in typ; eauto.
        econstructor; eauto.
    - apply inversion_Case in typ as (?&?&?&cd&?); auto.
      destruct cd.
      econstructor; eauto.
    - apply inversion_Case in typ as (?&?&?&cd&?); auto.
      destruct cd as [? _ _ ? _ _ _ _ _ _ _ _ ? _ wfbrs].
      destruct brs as ((?&?)&?).
      simpl fill_branches_hole in wfbrs.
      apply All2i_app_inv_r in wfbrs as (?&?&_&_&a).
      inv a.
      clear X0.
      destruct X as ((wfl&cc)&typ&_).
      unfold app_context.
      rewrite -app_assoc.
      destruct b; cbn in *.
      + eapply welltyped_fill_context_hole; eauto.
      + apply conv_context_sym in cc; auto.
        eapply context_conversion in typ; eauto.
        econstructor; eauto.
  Qed.

  Lemma cored_red :
    forall Γ u v,
      cored Σ Γ v u ->
      ∥ red Σ Γ u v ∥.
  Proof.
    intros Γ u v h.
    induction h.
    - constructor. now constructor.
    - destruct IHh as [r].
      constructor. etransitivity; eauto.
  Qed.

  Lemma cored_context :
    forall Γ t u π,
      cored Σ (Γ ,,, stack_context π) t u ->
      cored Σ Γ (zip (t, π)) (zip (u, π)).
  Proof.
    intros Γ t u π h. induction h.
    - constructor. eapply red1_context. assumption.
    - eapply cored_trans.
      + eapply IHh.
      + eapply red1_context. assumption.
  Qed.

  Lemma cored_zipx :
    forall Γ u v π,
      cored Σ (Γ ,,, stack_context π) u v ->
      cored Σ [] (zipx Γ u π) (zipx Γ v π).
  Proof.
    intros Γ u v π h.
    eapply cored_it_mkLambda_or_LetIn.
    eapply cored_context.
    rewrite app_context_nil_l.
    assumption.
  Qed.

  Lemma red_zipx :
    forall Γ u v π,
      red Σ (Γ ,,, stack_context π) u v ->
      red Σ [] (zipx Γ u π) (zipx Γ v π).
  Proof.
    intros Γ u v π h.
    eapply red_it_mkLambda_or_LetIn.
    eapply red_context_zip.
    now rewrite app_context_nil_l.
  Qed.

  Lemma cumul_zippx :
    forall Γ u v ρ,
      Σ ;;; (Γ ,,, stack_context ρ) |- u <= v ->
      Σ ;;; Γ |- zippx u ρ <= zippx v ρ.
  Proof.
    intros Γ u v ρ h.
    induction ρ in u, v, h |- *; auto.
    destruct a.
    all: try solve [
      unfold zippx ; simpl ;
      eapply cumul_it_mkLambda_or_LetIn ;
      assumption
    ].
    - unfold zippx. simpl.
      case_eq (decompose_stack ρ). intros l π e.
      unfold zippx in IHρ. rewrite e in IHρ.
      apply IHρ.
      eapply cumul_App_l. assumption.
    - unfold zippx. simpl.
      eapply cumul_it_mkLambda_or_LetIn. cbn.
      eapply cumul_Lambda_r.
      assumption.
    - unfold zippx. simpl.
      eapply cumul_it_mkLambda_or_LetIn. cbn.
      eapply cumul_Lambda_r.
      assumption.
    - unfold zippx. simpl.
      eapply cumul_it_mkLambda_or_LetIn. cbn.
      eapply cumul_LetIn_bo. assumption.
  Qed.

  Lemma conv_alt_it_mkLambda_or_LetIn :
    forall Δ Γ u v,
      Σ ;;; (Δ ,,, Γ) |- u = v ->
      Σ ;;; Δ |- it_mkLambda_or_LetIn Γ u = it_mkLambda_or_LetIn Γ v.
  Proof.
    intros Δ Γ u v h. revert Δ u v h.
    induction Γ as [| [na [b|] A] Γ ih ] ; intros Δ u v h.
    - assumption.
    - simpl. cbn. eapply ih.
      eapply conv_LetIn_bo. assumption.
    - simpl. cbn. eapply ih.
      eapply conv_Lambda_r. assumption.
  Qed.

  Lemma conv_alt_it_mkProd_or_LetIn :
    forall Δ Γ B B',
      Σ ;;; (Δ ,,, Γ) |- B = B' ->
      Σ ;;; Δ |- it_mkProd_or_LetIn Γ B = it_mkProd_or_LetIn Γ B'.
  Proof.
    intros Δ Γ B B' h.
    induction Γ as [| [na [b|] A] Γ ih ] in Δ, B, B', h |- *.
    - assumption.
    - simpl. cbn. eapply ih.
      eapply conv_LetIn_bo. assumption.
    - simpl. cbn. eapply ih.
      eapply conv_Prod_r. assumption.
  Qed.

  Lemma conv_zipp :
    forall Γ u v ρ,
      Σ ;;; Γ |- u = v ->
      Σ ;;; Γ |- zipp u ρ = zipp v ρ.
  Proof.
    intros Γ u v ρ h.
    unfold zipp.
    destruct decompose_stack.
    induction l in u, v, h |- *.
    - assumption.
    - simpl.  eapply IHl. eapply conv_App_l. assumption.
  Qed.

  Lemma cumul_zipp :
    forall Γ u v π,
      Σ ;;; Γ |- u <= v ->
      Σ ;;; Γ |- zipp u π <= zipp v π.
  Proof.
    intros Γ u v π h.
    unfold zipp.
    destruct decompose_stack as [l ρ].
    induction l in u, v, h |- *.
    - assumption.
    - simpl.  eapply IHl. eapply cumul_App_l. assumption.
  Qed.

  Lemma conv_cum_zipp' :
    forall leq Γ u v π,
      conv_cum leq Σ Γ u v ->
      conv_cum leq Σ Γ (zipp u π) (zipp v π).
  Proof.
    intros leq Γ u v π h.
    destruct leq.
    - destruct h. constructor. eapply conv_zipp. assumption.
    - destruct h. constructor. eapply cumul_zipp. assumption.
  Qed.

  Lemma conv_alt_zippx :
    forall Γ u v ρ,
      Σ ;;; (Γ ,,, stack_context ρ) |- u = v ->
      Σ ;;; Γ |- zippx u ρ = zippx v ρ.
  Proof.
    intros Γ u v ρ h.
    revert u v h. induction ρ ; intros u v h; auto.
    destruct a.
    all: try solve [
      unfold zippx ; simpl ;
      eapply conv_alt_it_mkLambda_or_LetIn ;
      assumption
    ].
    - unfold zippx. simpl.
      case_eq (decompose_stack ρ). intros l π e.
      unfold zippx in IHρ. rewrite e in IHρ.
      apply IHρ.
      eapply conv_App_l. assumption.
    - unfold zippx. simpl.
      eapply conv_alt_it_mkLambda_or_LetIn. cbn.
      eapply conv_Lambda_r.
      assumption.
    - unfold zippx. simpl.
      eapply conv_alt_it_mkLambda_or_LetIn. cbn.
      eapply conv_Lambda_r.
      assumption.
    - unfold zippx. simpl.
      eapply conv_alt_it_mkLambda_or_LetIn. cbn.
      eapply conv_LetIn_bo. assumption.
  Qed.

  Lemma conv_zippx :
    forall Γ u v ρ,
      Σ ;;; Γ ,,, stack_context ρ |- u = v ->
      Σ ;;; Γ |- zippx u ρ = zippx v ρ.
  Proof.
    intros Γ u v ρ uv. eapply conv_alt_zippx ; assumption.
  Qed.

  Lemma conv_cum_zippx' :
    forall Γ leq u v ρ,
      conv_cum leq Σ (Γ ,,, stack_context ρ) u v ->
      conv_cum leq Σ Γ (zippx u ρ) (zippx v ρ).
  Proof.
    intros Γ leq u v ρ h.
    destruct leq.
    - cbn in *. destruct h as [h]. constructor.
      eapply conv_alt_zippx ; assumption.
    - cbn in *. destruct h. constructor.
      eapply cumul_zippx. assumption.
  Qed.


  Derive Signature for Acc.

  Lemma wf_fun :
    forall A (R : A -> A -> Prop) B (f : B -> A),
      well_founded R ->
      well_founded (fun x y => R (f x) (f y)).
  Proof.
    intros A R B f h x.
    specialize (h (f x)).
    dependent induction h.
    constructor. intros y h.
    eapply H0 ; try reflexivity. assumption.
  Qed.

  Lemma Acc_fun :
    forall A (R : A -> A -> Prop) B (f : B -> A) x,
      Acc R (f x) ->
      Acc (fun x y => R (f x) (f y)) x.
  Proof.
    intros A R B f x h.
    dependent induction h.
    constructor. intros y h.
    eapply H0 ; try reflexivity. assumption.
  Qed.

  (* TODO Put more general lemma in Inversion *)
  Lemma welltyped_it_mkLambda_or_LetIn :
    forall Γ Δ t,
      welltyped Σ Γ (it_mkLambda_or_LetIn Δ t) ->
      welltyped Σ (Γ ,,, Δ) t.
  Proof.
    destruct hΣ as [wΣ].
    intros Γ Δ t h.
    induction Δ as [| [na [b|] A] Δ ih ] in Γ, t, h |- *.
    - assumption.
    - simpl. apply ih in h. cbn in h.
      destruct h as [T h].
      apply inversion_LetIn in h as hh ; auto.
      destruct hh as [s1 [A' [? [? [? ?]]]]].
      exists A'. assumption.
    - simpl. apply ih in h. cbn in h.
      destruct h as [T h].
      apply inversion_Lambda in h as hh ; auto.
      pose proof hh as [s1 [B [? [? ?]]]].
      exists B. assumption.
  Qed.

  Lemma it_mkLambda_or_LetIn_welltyped :
    forall Γ Δ t,
      welltyped Σ (Γ ,,, Δ) t ->
      welltyped Σ Γ (it_mkLambda_or_LetIn Δ t).
  Proof.
    intros Γ Δ t [T h].
    eexists. eapply PCUICGeneration.type_it_mkLambda_or_LetIn.
    eassumption.
  Qed.

  Lemma welltyped_it_mkLambda_or_LetIn_iff :
    forall Γ Δ t,
      welltyped Σ Γ (it_mkLambda_or_LetIn Δ t) <->
      welltyped Σ (Γ ,,, Δ) t.
  Proof.
    intros. split.
    - apply welltyped_it_mkLambda_or_LetIn.
    - apply it_mkLambda_or_LetIn_welltyped.
  Qed.

  Lemma welltyped_zipx :
    forall {Γ t π},
      welltyped Σ [] (zipx Γ t π) ->
      welltyped Σ Γ (zipc t π).
  Proof.
    intros Γ t π h.
    apply welltyped_it_mkLambda_or_LetIn in h.
    rewrite app_context_nil_l in h.
    assumption.
  Qed.

  Lemma welltyped_zipc_stack_context Γ t π ρ args
    : decompose_stack π = (args, ρ)
      -> welltyped Σ Γ (zipc t π)
      -> welltyped Σ (Γ ,,, stack_context π) (zipc t (appstack args [])).
  Proof.
    intros h h1.
    apply decompose_stack_eq in h. subst.
    rewrite stack_context_appstack.
    induction args in Γ, t, ρ, h1 |- *.
    - cbn in *.
      now apply (welltyped_context Γ (t, ρ)).
    - simpl. eauto.
  Qed.

  Lemma red_const :
    forall {Γ c u cty cb cu},
      Some (ConstantDecl {| cst_type := cty ; cst_body := Some cb ; cst_universes := cu |})
      = lookup_env Σ c ->
      red (fst Σ) Γ (tConst c u) (subst_instance u cb).
  Proof.
    intros Γ c u cty cb cu e.
    econstructor. econstructor.
    - symmetry in e. exact e.
    - reflexivity.
  Qed.

  Lemma cored_const :
    forall {Γ c u cty cb cu},
      Some (ConstantDecl {| cst_type := cty ; cst_body := Some cb ; cst_universes := cu |})
      = lookup_env Σ c ->
      cored (fst Σ) Γ (subst_instance u cb) (tConst c u).
  Proof.
    intros Γ c u cty cb cu e.
    symmetry in e.
    econstructor.
    econstructor.
    - exact e.
    - reflexivity.
  Qed.

  Derive Signature for cumul.
  Derive Signature for red1.

  Lemma app_cored_r :
    forall Γ u v1 v2,
      cored Σ Γ v1 v2 ->
      cored Σ Γ (tApp u v1) (tApp u v2).
  Proof.
    intros Γ u v1 v2 h.
    induction h.
    - constructor. constructor. assumption.
    - eapply cored_trans.
      + eapply IHh.
      + constructor. assumption.
  Qed.

  Fixpoint isAppProd (t : term) : bool :=
    match t with
    | tApp t l => isAppProd t
    | tProd na A B => true
    | _ => false
    end.

  Lemma isAppProd_mkApps :
    forall t l, isAppProd (mkApps t l) = isAppProd t.
  Proof.
    intros t l. revert t.
    induction l ; intros t.
    - reflexivity.
    - cbn. rewrite IHl. reflexivity.
  Qed.

  Lemma isProdmkApps :
    forall t l,
      isProd (mkApps t l) ->
      l = [].
  Proof.
    intros t l h.
    revert t h.
    induction l ; intros t h.
    - reflexivity.
    - cbn in h. specialize IHl with (1 := h). subst.
      cbn in h. discriminate h.
  Qed.

  Lemma isSortmkApps :
    forall t l,
      isSort (mkApps t l) ->
      l = [].
  Proof.
    intros t l h.
    revert t h.
    induction l ; intros t h.
    - reflexivity.
    - cbn in h. specialize IHl with (1 := h). subst.
      cbn in h. exfalso. discriminate.
  Qed.

  Lemma isAppProd_isProd :
    forall Γ t,
      isAppProd t ->
      welltyped Σ Γ t ->
      isProd t.
  Proof.
    destruct hΣ as [wΣ].
    intros Γ t hp hw.
    induction t in Γ, hp, hw |- *.
    all: try discriminate hp.
    - reflexivity.
    - simpl in hp.
      specialize IHt1 with (1 := hp).
      assert (welltyped Σ Γ t1) as h.
      { destruct hw as [T h].
        apply inversion_App in h as hh ; auto.
        destruct hh as [na [A' [B' [? [? ?]]]]].
        eexists. eassumption.
      }
      specialize IHt1 with (1 := h).
      destruct t1.
      all: try discriminate IHt1.
      destruct hw as [T hw'].
      apply inversion_App in hw' as ihw' ; auto.
      destruct ihw' as [na' [A' [B' [hP [? ?]]]]].
      apply inversion_Prod in hP as [s1 [s2 [? [? bot]]]] ; auto.
      apply PCUICConversion.invert_cumul_prod_r in bot ; auto.
      destruct bot as [? [? [? [[[r ?] ?] ?]]]].
      exfalso. clear - r wΣ.
      revert r. generalize (Universe.sort_of_product s1 s2). intro s. clear.
      intro r. eapply Relation_Properties.clos_rt_rt1n in r.
      dependent induction r.
      assert (h : y = tSort s).
      { clear - r. dependent destruction r.
        assert (h : isSort (mkApps (tFix mfix idx) args)).
        { rewrite <- H. constructor. }
        apply isSortmkApps in h. subst. cbn in H.
        discriminate.
      }
      subst.
      dependent destruction r.
      assert (h : isSort (mkApps (tFix mfix idx) args)).
      { rewrite <- H. constructor. }
      apply isSortmkApps in h. subst. cbn in H.
      discriminate.
  Qed.

  Lemma mkApps_Prod_nil :
    forall Γ na A B l,
      welltyped Σ Γ (mkApps (tProd na A B) l) ->
      l = [].
  Proof.
    intros Γ na A B l h.
    pose proof (isAppProd_isProd) as hh.
    specialize hh with (2 := h).
    rewrite isAppProd_mkApps in hh.
    specialize hh with (1 := eq_refl).
    apply isProdmkApps in hh. assumption.
  Qed.


  (* TODO MOVE or even replace old lemma *)
  Lemma decompose_stack_noStackApp :
    forall π l ρ,
      decompose_stack π = (l,ρ) ->
      isStackApp ρ = false.
  Proof.
    intros π l ρ e.
    destruct ρ; auto.
    destruct s.
    all: auto.
    exfalso. eapply decompose_stack_not_app. eassumption.
  Qed.
  
  (* TODO MOVE *)
  Lemma stack_context_decompose :
    forall π,
      stack_context (snd (decompose_stack π)) = stack_context π.
  Proof.
    intros π.
    case_eq (decompose_stack π). intros l ρ e.
    cbn. pose proof (decompose_stack_eq _ _ _ e). subst.
    rewrite stack_context_appstack. reflexivity.
  Qed.
  
  Lemma decompose_stack_stack_cat π π' :
    decompose_stack (π +++ π') =
    ((decompose_stack π).1 ++
     match (decompose_stack π).2 with
     | [] => (decompose_stack π').1
     | _ => []
     end,
     (decompose_stack π).2 +++
     match (decompose_stack π).2 with
     | [] => (decompose_stack π').2
     | _ => π'
     end).
  Proof.
    induction π in π' |- *; cbn in *; auto.
    - now destruct decompose_stack.
    - destruct a; auto.
      rewrite !IHπ.
      now destruct (decompose_stack π).
  Qed.

  Lemma zipp_stack_cat π π' t :
    isStackApp π = false ->
    zipp t (π' +++ π) = zipp t π'.
  Proof.
    intros no_stack_app.
    unfold zipp.
    rewrite decompose_stack_stack_cat.
    destruct (decompose_stack π') eqn:decomp.
    cbn.
    destruct s; try now rewrite app_nil_r.
    now destruct π as [|[] ?]; cbn in *; rewrite ?app_nil_r.
  Qed.
  
  Lemma zipp_appstack t args π :
    zipp t (appstack args π) = zipp (mkApps t args) π.
  Proof.
    unfold zipp.
    rewrite decompose_stack_appstack.
    rewrite <- mkApps_nested.
    now destruct decompose_stack.
  Qed.

  Lemma appstack_cons a args π :
    appstack (a :: args) π = App_l a :: appstack args π.
  Proof. reflexivity. Qed.
  
  Lemma fst_decompose_stack_nil π :
    isStackApp π = false ->
    (decompose_stack π).1 = [].
  Proof. now destruct π as [|[] ?]. Qed.
  
  Lemma zipp_as_mkApps t π :
    zipp t π = mkApps t (decompose_stack π).1.
  Proof.
    unfold zipp.
    now destruct decompose_stack.
  Qed.
  
  Lemma zipp_noStackApp t π :
    isStackApp π = false ->
    zipp t π = t.
  Proof.
    intros.
    now rewrite zipp_as_mkApps fst_decompose_stack_nil.
  Qed.
  
  Lemma it_mkLambda_or_LetIn_inj :
    forall Γ u v,
      it_mkLambda_or_LetIn Γ u =
      it_mkLambda_or_LetIn Γ v ->
      u = v.
  Proof.
    intros Γ u v e.
    revert u v e.
    induction Γ as [| [na [b|] A] Γ ih ] ; intros u v e.
    - assumption.
    - simpl in e. cbn in e.
      apply ih in e.
      inversion e. reflexivity.
    - simpl in e. cbn in e.
      apply ih in e.
      inversion e. reflexivity.
  Qed.

  Hint Resolve conv_refl conv_alt_red : core.
  Hint Resolve conv_refl : core.


  (*
  (* Let bindings are not injective, so it_mkLambda_or_LetIn is not either.
     However, when they are all lambdas they become injective for conversion.
     stack_contexts only produce lambdas so we can use this property on them.
     It only applies to stacks manipulated by conversion/reduction which are
     indeed let-free.
   *)
  Fixpoint let_free_context (Γ : context) :=
    match Γ with
    | [] => true
    | {| decl_name := na ; decl_body := Some b ; decl_type := B |} :: Γ => false
    | {| decl_name := na ; decl_body := None ; decl_type := B |} :: Γ =>
      let_free_context Γ
    end.

  Lemma let_free_context_app :
    forall Γ Δ,
      let_free_context (Γ ,,, Δ) = let_free_context Δ && let_free_context Γ.
  Proof.
    intros Γ Δ.
    induction Δ as [| [na [b|] B] Δ ih ] in Γ |- *.
    - simpl. reflexivity.
    - simpl. reflexivity.
    - simpl. apply ih.
  Qed.

  Lemma let_free_context_rev :
    forall Γ,
      let_free_context (List.rev Γ) = let_free_context Γ.
  Proof.
    intros Γ.
    induction Γ as [| [na [b|] B] Γ ih ].
    - reflexivity.
    - simpl. rewrite let_free_context_app. simpl.
      apply andb_false_r.
    - simpl. rewrite let_free_context_app. simpl.
      rewrite ih. rewrite andb_true_r. reflexivity.
  Qed.  

  Fixpoint let_free_stack (π : stack) :=
    match π with
    | ε => true
    | App u ρ => let_free_stack ρ
    | Fix f n args ρ => let_free_stack ρ
    | Fix_mfix_ty na bo ra mfix1 mfix2 idx ρ => let_free_stack ρ
    | Fix_mfix_bd na ty ra mfix1 mfix2 idx ρ => let_free_stack ρ
    | CoFix f n args ρ => let_free_stack ρ
    | CoFix_mfix_ty na bo ra mfix1 mfix2 idx ρ => let_free_stack ρ
    | CoFix_mfix_bd na ty ra mfix1 mfix2 idx ρ => let_free_stack ρ
    | Case_pars ci ppars1 ppars2 puinst pctx pret c brs ρ => let_free_stack ρ
    | Case_p ci ppars puinst pctx c brs ρ =>
      let_free_context pctx && let_free_stack ρ
    | Case ci p brs ρ => let_free_stack ρ
    | Case_brs ci p c brctx brs1 brs2 ρ => 
      let_free_context brctx && let_free_stack ρ
    | Proj p ρ => let_free_stack ρ
    | Prod_l na B ρ => let_free_stack ρ
    | Prod_r na A ρ => let_free_stack ρ
    | Lambda_ty na u ρ => let_free_stack ρ
    | Lambda_tm na A ρ => let_free_stack ρ
    | LetIn_bd na B u ρ => let_free_stack ρ
    | LetIn_ty na b u ρ => let_free_stack ρ
    | LetIn_in na b B ρ => false
    | coApp u ρ => let_free_stack ρ
    end.

  Lemma let_free_stack_context :
    forall π,
      let_free_stack π ->
      let_free_context (stack_context π).
  Proof.
    intros π h.
    induction π.
    all: try solve [ simpl ; rewrite ?IHπ // ].
    - simpl. rewrite let_free_context_app.
      rewrite IHπ => //. rewrite andb_true_r. rewrite let_free_context_rev.
      match goal with
      | |- context [ mapi ?f ?l ] =>
        generalize l
      end.
      intro l. unfold mapi.
      generalize 0 at 2. intro n.
      induction l in n |- *.
      + simpl. reflexivity.
      + simpl. apply IHl.
    - simpl. rewrite let_free_context_app.
      rewrite IHπ => //. rewrite andb_true_r. rewrite let_free_context_rev.
      match goal with
      | |- context [ mapi ?f ?l ] =>
        generalize l
      end.
      intro l. unfold mapi.
      generalize 0 at 2. intro n.
      induction l in n |- *.
      + simpl. reflexivity.
      + simpl. apply IHl.
    - simpl. rewrite let_free_context_app.
      cbn in h. move/andP: h => [-> h]. now apply IHπ.
    - simpl. rewrite let_free_context_app.
      cbn in h. move/andP: h => [-> h]. now apply IHπ.
  Qed.
*)

  Lemma cored_red_cored :
    forall Γ u v w,
      cored Σ Γ w v ->
      red Σ Γ u v ->
      cored Σ Γ w u.
  Proof.
    intros Γ u v w h1 h2.
    revert u h2. induction h1 ; intros t h2.
    - eapply cored_red_trans ; eassumption.
    - eapply cored_trans.
      + eapply IHh1. assumption.
      + assumption.
  Qed.

  Lemma red_neq_cored :
    forall Γ u v,
      red Σ Γ u v ->
      u <> v ->
      cored Σ Γ v u.
  Proof.
    intros Γ u v r n.
    destruct r using red_rect'.
    - exfalso. apply n. reflexivity.
    - eapply cored_red_cored ; try eassumption.
      constructor. assumption.
  Qed.

  Lemma red_welltyped :
    forall {Γ u v},
      welltyped Σ Γ u ->
      ∥ red (fst Σ) Γ u v ∥ ->
      welltyped Σ Γ v.
  Proof.
    destruct hΣ as [wΣ]; clear hΣ.
    intros Γ u v h [r].
    revert h. induction r using red_rect' ; intros h.
    - assumption.
    - specialize IHr with (1 := ltac:(eassumption)).
      destruct IHr as [A ?]. exists A.
      eapply subject_reduction1 ; eauto with wf.
  Qed.

  Lemma red_cored_cored :
    forall Γ u v w,
      red Σ Γ v w ->
      cored Σ Γ v u ->
      cored Σ Γ w u.
  Proof.
    intros Γ u v w h1 h2.
    revert u h2. induction h1 using red_rect' ; intros t h2.
    - assumption.
    - eapply cored_trans.
      + eapply IHh1. assumption.
      + assumption.
  Qed.

  Lemma Proj_red_cond :
    forall Γ i pars narg i' c u l,
      welltyped Σ Γ (tProj (i, pars, narg) (mkApps (tConstruct i' c u) l)) ->
      nth_error l (pars + narg) <> None.
  Proof.
    intros Γ i pars narg i' c u l [T h].
    apply PCUICInductiveInversion.invert_Proj_Construct in h as (<-&->&?); auto.
    now apply nth_error_Some.
  Qed.

  Lemma cored_zipc :
    forall Γ t u π,
      cored Σ (Γ ,,, stack_context π) t u ->
      cored Σ Γ (zipc t π) (zipc u π).
  Proof.
    intros Γ t u π h.
    do 2 zip fold. eapply cored_context. assumption.
  Qed.

  Lemma red_zipc :
    forall Γ t u π,
      red Σ (Γ ,,, stack_context π) t u ->
      red Σ Γ (zipc t π) (zipc u π).
  Proof.
    intros Γ t u π h.
    do 2 zip fold. eapply red_context_zip. assumption.
  Qed.

  Lemma welltyped_zipc_zipp :
    forall Γ t π,
      welltyped Σ Γ (zipc t π) ->
      welltyped Σ (Γ ,,, stack_context π) (zipp t π).
  Proof.
    intros Γ t π h.
    unfold zipp.
    case_eq (decompose_stack π). intros l ρ e.
    pose proof (decompose_stack_eq _ _ _ e). subst. clear e.
    rewrite zipc_appstack in h.
    zip fold in h.
    apply welltyped_context in h. simpl in h.
    rewrite stack_context_appstack.
    assumption.
  Qed.
  
  Lemma conv_cum_zipp leq Γ t t' π π' :
    conv_cum leq Σ Γ t t' ->
    ∥conv_terms Σ Γ (decompose_stack π).1 (decompose_stack π').1∥ ->
    conv_cum leq Σ Γ (zipp t π) (zipp t' π').
  Proof.
    intros conv conv_args.
    rewrite !zipp_as_mkApps.
    destruct leq; cbn in *.
    - sq.
      apply mkApps_conv_args; auto.
    - sq.
      apply cumul_mkApps; auto.
  Qed.

  Lemma whne_All2_fold f rel Γ Γ' t :
    (forall Γ Γ' c c', rel Γ Γ' c c' -> (decl_body c = None <-> decl_body c' = None)) ->
    whne f Σ Γ t ->
    All2_fold rel Γ Γ' ->
    whne f Σ Γ' t.
  Proof.
    intros behaves wh conv.
    induction wh; eauto using whne.
    destruct nth_error eqn:nth; [|easy].
    cbn in *.
    eapply All2_fold_nth in nth; eauto.
    destruct nth as (?&eq&?&?).
    constructor.
    rewrite eq.
    cbn.
    specialize (behaves _ _ _ _ r).
    f_equal.
    apply behaves.
    congruence.
  Qed.

  Lemma whnf_All2_fold f rel Γ Γ' t :
    (forall Γ Γ' c c', rel Γ Γ' c c' -> (decl_body c = None <-> decl_body c' = None)) ->
    whnf f Σ Γ t ->
    All2_fold rel Γ Γ' ->
    whnf f Σ Γ' t.
  Proof.
    intros behaves wh conv.
    destruct wh; eauto using whnf.
    apply whnf_ne.
    eapply whne_All2_fold; eauto.
  Qed.

  Lemma whne_conv_context f Γ Γ' t :
    whne f Σ Γ t ->
    conv_context Σ Γ Γ' ->
    whne f Σ Γ' t.
  Proof.
    apply whne_All2_fold.
    intros ? ? ? ? r.
    now depelim r.
  Qed.

  Lemma whnf_conv_context f Γ Γ' t :
    whnf f Σ Γ t ->
    conv_context Σ Γ Γ' ->
    whnf f Σ Γ' t.
  Proof.
    apply whnf_All2_fold.
    intros ? ? ? ? r.
    now depelim r.
  Qed.

  Lemma Case_Construct_ind_eq :
    forall {Γ ci ind' pred i u brs args},
      welltyped Σ Γ (tCase ci pred (mkApps (tConstruct ind' i u) args) brs) ->
      ci.(ci_ind) = ind'.
  Proof.
    destruct hΣ as [wΣ].
    intros Γ ci ind' pred i u brs args [A h].
    apply PCUICInductiveInversion.invert_Case_Construct in h; intuition auto.
  Qed.

  Lemma Proj_Construct_ind_eq :
    forall Γ i i' pars narg c u l,
      welltyped Σ Γ (tProj (i, pars, narg) (mkApps (tConstruct i' c u) l)) ->
      i = i'.
  Proof.
    destruct hΣ as [wΣ].
    intros Γ i i' pars narg c u l [T h].
    now apply PCUICInductiveInversion.invert_Proj_Construct in h.
  Qed.
  
End Lemmata.

Hint Resolve isType_welltyped : pcuic.
