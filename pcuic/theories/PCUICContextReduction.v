(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICLiftSubst PCUICEquality PCUICUnivSubst PCUICInduction 
     PCUICContextRelation PCUICReduction PCUICCases PCUICWeakening.

Require Import ssreflect.
Require Import Equations.Prop.DepElim.
From Equations.Type Require Import Relation Relation_Properties.
From Equations Require Import Equations.
Set Equations Transparent.
Set Default Goal Selector "!".

Section CtxReduction.
  Context {cf : checker_flags}.
  Context {Σ : global_env}.
  Context (wfΣ : wf Σ).

  Lemma weakening_red_0 Γ Γ' M N n :
    n = #|Γ'| ->
    red Σ Γ M N ->
    red Σ (Γ ,,, Γ') (lift0 n M) (lift0 n N).
  Proof. now move=> ->; apply (weakening_red Σ Γ [] Γ'). Qed.


  Lemma red_red_ctx Γ Δ t u :
    red Σ Γ t u ->
    red_ctx Δ Γ ->
    red Σ Δ t u.
  Proof.
    move=> H Hctx. induction H.
    revert Δ Hctx.
    induction r using red1_ind_all; intros Δ Hctx; try solve [eapply red_step; repeat (constructor; eauto)].
    - red in Hctx.
      eapply nth_error_pred1_ctx in Hctx; eauto.
      destruct Hctx as [x' [? ?]].
      eapply red_step. constructor. eauto.
      rewrite -(firstn_skipn (S i) Δ).
      eapply weakening_red_0; auto.
      rewrite firstn_length_le //.
      destruct (nth_error Δ) eqn:Heq => //.
      eapply nth_error_Some_length in Heq. lia.
    - repeat econstructor; eassumption.
    - repeat econstructor; eassumption.
    - repeat econstructor; eassumption.
    - repeat econstructor; eassumption.
    - eapply red_abs_alt. eauto. eauto.
    - eapply red_abs_alt. eauto. apply (IHr (Δ ,, vass na N)).
      constructor; auto. red. auto.
    - eapply red_letin; eauto.
    - eapply red_letin; eauto.
    - eapply red_letin_alt; eauto.
      eapply (IHr (Δ ,, vdef na b t)). constructor; eauto.
      red. split; eauto.
    - eapply red_case; eauto. unfold on_Trel; pcuic.
    - eapply red_case; eauto. unfold on_Trel; pcuic.
    - eapply red_case; eauto. unfold on_Trel; pcuic.
      eapply OnOne2_All2; eauto. simpl. intuition eauto.
    - eapply red_proj_c; eauto.
    - eapply red_app; eauto.
    - eapply red_app; eauto.
    - eapply red_prod_alt; eauto.
    - eapply red_prod_alt; eauto. apply (IHr (Δ ,, vass na M1)); constructor; auto.
      red; eauto.
    - eapply red_evar.
      eapply OnOne2_All2; simpl; eauto. simpl. intuition eauto.
    - eapply red_fix_one_ty.
      eapply OnOne2_impl ; eauto.
      intros [? ? ? ?] [? ? ? ?] [[r ih] e]. simpl in *.
      inversion e. subst. clear e.
      split ; auto.
    - eapply red_fix_one_body.
      eapply OnOne2_impl ; eauto.
      intros [? ? ? ?] [? ? ? ?] [[r ih] e]. simpl in *.
      inversion e. subst. clear e.
      split ; auto.
      eapply ih.
      clear - Hctx. induction (fix_context mfix0).
      + assumption.
      + simpl. destruct a as [na [b|] ty].
        * constructor ; pcuicfo (hnf ; auto).
        * constructor ; pcuicfo (hnf ; auto).
    - eapply red_cofix_one_ty.
      eapply OnOne2_impl ; eauto.
      intros [? ? ? ?] [? ? ? ?] [[r ih] e]. simpl in *.
      inversion e. subst. clear e.
      split ; auto.
    - eapply red_cofix_one_body.
      eapply OnOne2_impl ; eauto.
      intros [? ? ? ?] [? ? ? ?] [[r ih] e]. simpl in *.
      inversion e. subst. clear e.
      split ; auto.
      eapply ih.
      clear - Hctx. induction (fix_context mfix0).
      + assumption.
      + simpl. destruct a as [na [b|] ty].
        * constructor ; pcuicfo (hnf ; auto).
        * constructor ; pcuicfo (hnf ; auto).
    - auto.
    - eapply red_trans; eauto.
  Qed.

  
Lemma red_ctx_rel_red_context_rel Σ Γ : 
  CRelationClasses.relation_equivalence (red_ctx_rel Σ Γ) (red_context_rel Σ Γ).
Proof.
  rewrite /red_ctx_rel /red_context_rel; split.
  - induction 1.
    * admit.
    * eapply context_relation_refl => Δ [na [b|] ty]; constructor; auto; constructor 2.
    * eapply context_relation_trans; eauto.
      intros.
      depelim X4; depelim X5; constructor; etransitivity; eauto.



