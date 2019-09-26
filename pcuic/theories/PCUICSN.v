(* Distributed under the terms of the MIT license.   *)

 From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia
     Classes.CRelationClasses.
From MetaCoq.Template
Require Import config Universes monad_utils utils BasicAst AstUtils UnivSubst
     Universes.
From MetaCoq.Checker Require Import uGraph.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICReflect PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICPosition
     PCUICNormal PCUICInversion PCUICCumulativity PCUICSafeLemmata
     PCUICGeneration PCUICValidity PCUICSR PCUICAlpha PCUICNameless
     PCUICEquality PCUICConfluence.
From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.

Import MonadNotation.
Open Scope type_scope.

(* We assume normalisation of the reduction.
    We state is as well-foundedness of the reduction.
 *)

Section Normalisation.

  Context {cf : checker_flags}.
  Context (Σ : global_env_ext).

  Axiom normalisation :
    forall Γ t,
      welltyped Σ Γ t ->
      Acc (cored (fst Σ) Γ) t.

  Lemma Acc_cored_Prod Γ n t1 t2 :
    Acc (cored Σ Γ) t1 ->
    Acc (cored Σ (Γ,, vass n t1)) t2 ->
    Acc (cored Σ Γ) (tProd n t1 t2).
  Proof.
  Admitted.

  Lemma Acc_cored_LetIn Γ n t1 t2 t3 :
    Acc (cored Σ Γ) t1 ->
    Acc (cored Σ Γ) t2 -> Acc (cored Σ (Γ,, vdef n t1 t2)) t3 ->
    Acc (cored Σ Γ) (tLetIn n t1 t2 t3).
  Proof.
  Admitted.

  Lemma neq_mkApps u l : forall t, t <> tSort u -> mkApps t l <> tSort u.
  Proof.
    induction l; cbn; intros t e e'; try easy.
    eapply IHl. 2: eassumption. intros e''; discriminate e''.
  Qed.

  Corollary normalisation' :
    forall Γ t, wf Σ -> wellformed Σ Γ t -> Acc (cored (fst Σ) Γ) t.
  Proof.
    intros Γ t HΣ Ht. destruct Ht as [HH|[HH]].
    - now apply normalisation.
    - revert Γ HH; induction t;
        intros Γ [ctx [s [H1 H2]]]; cbn in *; try discriminate H1.
      + constructor. intros y Hy. cut False. intros [].
        dependent induction Hy.
        * inversion X. eapply neq_mkApps.
          2: eassumption. intro HH; discriminate HH.
        * easy.
      + eapply Acc_cored_Prod.
        * apply normalisation.
          apply destArity_app_Some in H1. destruct H1 as [ctx' [e1 e2]]; subst.
          rewrite app_context_assoc in H2. cbn in H2.
          apply wf_local_app in H2.
          destruct (wf_local_inv H2 _ _ eq_refl) as [_ [u [Ht1 _]]].
          econstructor; exact Ht1.
        * apply destArity_app_Some in H1. destruct H1 as [ctx' [e1 e2]]; subst.
          apply IHt2. exists ctx', s. split. assumption.
          now rewrite app_context_assoc in H2.
      + apply Acc_cored_LetIn.
        * apply normalisation.
          apply destArity_app_Some in H1. destruct H1 as [ctx' [e1 e2]]; subst.
          rewrite app_context_assoc in H2. cbn in H2.
          apply wf_local_app in H2.
          destruct (wf_local_inv H2 _ _ eq_refl) as [_ [_ [Ht1 _]]].
          econstructor; exact Ht1.
        * apply destArity_app_Some in H1. destruct H1 as [ctx' [e1 e2]]; subst.
          rewrite app_context_assoc in H2. cbn in H2.
          apply wf_local_app in H2.
          destruct (wf_local_inv H2 _ _ eq_refl) as [? [u [Ht1 _]]].
          apply validity_term in Ht1; cbn in Ht1; try assumption.
          destruct Ht1. now apply IHt2.
          apply normalisation. destruct i as [uu HH].
          econstructor; exact HH.
        * change (destArity ([vdef na t1 t2] ,,, []) t3 = Some (ctx, s)) in H1.
          apply destArity_app_Some in H1. destruct H1 as [ctx' [e1 e2]]; subst.
          apply IHt3. exists ctx', s. split. assumption.
          now rewrite app_context_assoc in H2.
  Admitted.

End Normalisation.


(* Since we are working with name annotations, reduction is sensitive to names.
   In this section we provide cored' which corresponds to reduction upto
   α-renaming, as well as the necessary lemmata to show it's well-founded and
   can be used instead of the usual reduction as a measure.
 *)
Section Alpha.

  Context {cf : checker_flags}.
  Context (Σ : global_env_ext).
  Context (hΣ : ∥ wf Σ ∥).

  Notation eqt u v :=
    (∥ eq_term (global_ext_constraints Σ) u v ∥).

  Definition cored' Γ u v :=
    exists u' v', cored Σ Γ u' v' /\ eqt u u' /\ eqt v v'.

  Lemma cored_alt :
    forall Γ u v,
      cored Σ Γ u v <~> ∥ Relation.trans_clos (red1 Σ Γ) v u ∥.
  Proof.
    intros Γ u v.
    split.
    - intro h. induction h.
      + constructor. constructor. assumption.
      + destruct IHh as [ih]. constructor.
        eapply Relation.t_trans.
        * eassumption.
        * constructor. assumption.
    - intros [h]. induction h.
      + constructor. assumption.
      + eapply cored_trans'. all: eassumption.
  Qed.

  Lemma cored'_postpone :
    forall Γ u v,
      cored' Γ u v ->
      exists u', cored Σ Γ u' v /\ eqt u u'.
  Proof.
    intros Γ u v [u' [v' [r [[hu] [hv]]]]].
    apply cored_alt in r.
    destruct r as [r].
    induction r in u, v, hu, hv.
    - eapply red1_eq_term_upto_univ_r in r. 9: eassumption.
      (* all: auto. *)
      (* They should be automatic... *)
      all: try eapply eq_universe_refl.
      all: try eapply eq_universe_sym.
      all: try eapply eq_universe_trans.
      + destruct r as [u' [r e]].
        exists u'. split.
        * constructor. assumption.
        * constructor. eapply eq_term_trans. 1: eauto.
          eapply eq_term_sym. assumption.
      + eapply leq_term_SubstUnivPreserving.
      + intros ? ?. auto.
    - specialize IHr1 with (1 := eq_term_refl _ _) (2 := hv).
      destruct IHr1 as [y' [h1 [e1]]].
      specialize IHr2 with (1 := hu) (2 := eq_term_sym _ _ _ e1).
      destruct IHr2 as [u' [h2 ?]].
      exists u'. split.
      + eapply cored_trans'. all: eauto.
      + assumption.
  Qed.

  Corollary cored_upto :
    forall Γ u v v',
      cored Σ Γ u v ->
      eq_term Σ v v' ->
      exists u', cored Σ Γ u' v' /\ eqt u u'.
  Proof.
    intros Γ u v v' h e.
    eapply cored'_postpone.
    exists u, v. intuition eauto.
    - constructor. apply eq_term_refl.
    - constructor. apply eq_term_sym. assumption.
  Qed.

  Lemma Acc_impl :
    forall A (R R' : A -> A -> Prop),
      (forall x y, R x y -> R' x y) ->
      forall x, Acc R' x -> Acc R x.
  Proof.
    intros A R R' h x hx.
    induction hx as [x h1 h2].
    constructor. intros y hy.
    eapply h2. eapply h. assumption.
  Qed.

  Lemma Acc_cored_cored' :
    forall Γ u,
      Acc (cored Σ Γ) u ->
      forall u', eq_term Σ u u' -> Acc (cored' Γ) u'.
  Proof.
    intros Γ u h. induction h as [u h ih].
    intros u' e. constructor. intros v [v' [u'' [r [[e1] [e2]]]]].
    assert (ee : eq_term Σ u'' u).
    { eapply eq_term_sym. eapply eq_term_trans. all: eassumption. }
    eapply cored_upto in r as hh. 2: exact ee.
    destruct hh as [v'' [r' [e']]].
    eapply ih.
    - eassumption.
    - eapply eq_term_sym. eapply eq_term_trans. all: eassumption.
  Qed.

  Lemma normalisation_upto :
    forall Γ u,
      wellformed Σ Γ u ->
      Acc (cored' Γ) u.
  Proof.
    destruct hΣ.
    intros Γ u h.
    apply normalisation' in h. 2: auto.
    eapply Acc_cored_cored'.
    - eassumption.
    - apply eq_term_refl.
  Qed.

  (* TODO Maybe switch to eq_context *)
  Lemma cored_eq_context_upto_names :
    forall Γ Δ u v,
      eq_context_upto_names Γ Δ ->
      cored Σ Γ u v ->
      cored Σ Δ u v.
  Proof.
    intros Γ Δ u v e h.
    apply cored_alt in h as [h].
    induction h in Δ, e |- *.
    - constructor. eapply red1_eq_context_upto_names. all: eauto.
    - eapply cored_trans'.
      + eapply IHh2. assumption.
      + eapply IHh1. assumption.
  Qed.

  Lemma cored_eq_term_upto :
    forall Re Rle Γ u v u',
      RelationClasses.Reflexive Re ->
      SubstUnivPreserving Re ->
      RelationClasses.Reflexive Rle ->
      RelationClasses.Symmetric Re ->
      RelationClasses.Transitive Re ->
      RelationClasses.Transitive Rle ->
      RelationClasses.subrelation Re Rle ->
      eq_term_upto_univ Re Rle u u' ->
      cored Σ Γ v u ->
      exists v', cored Σ Γ v' u' /\ ∥ eq_term_upto_univ Re Rle v v' ∥.
  Proof.
    intros Re Rle Γ u v u' X X0 X1 X2 X3 X4 X5 e h.
    apply cored_alt in h as [h].
    induction h in u', e |- *.
    - eapply red1_eq_term_upto_univ_l in r. 8: eauto. all: auto.
      destruct r as [? [? ?]].
      eexists. split.
      + constructor. eassumption.
      + constructor. assumption.
    - specialize (IHh1 _ e). destruct IHh1 as [y' [r1 [e1]]].
      specialize (IHh2 _ e1). destruct IHh2 as [z' [r2 [e2]]].
      exists z'. split.
      + eapply cored_trans'. all: eassumption.
      + constructor. assumption.
  Qed.

  Lemma cored_eq_context_upto :
    forall Re Γ Δ u v,
      RelationClasses.Reflexive Re ->
      RelationClasses.Symmetric Re ->
      RelationClasses.Transitive Re ->
      SubstUnivPreserving Re ->
      eq_context_upto Re Γ Δ ->
      cored Σ Γ u v ->
      exists u', cored Σ Δ u' v /\ ∥ eq_term_upto_univ Re Re u u' ∥.
  Proof.
    intros Re Γ Δ u v hRe1 hRe2 hRe3 hRe4 e h.
    apply cored_alt in h as [h].
    induction h.
    - eapply red1_eq_context_upto_l in r. all: eauto.
      destruct r as [? [? ?]].
      eexists. split.
      + constructor. eassumption.
      + constructor. assumption.
    - destruct IHh1 as [x' [r1 [e1]]].
      destruct IHh2 as [y' [r2 [e2]]].
      eapply cored_eq_term_upto in r2. 9: exact e1. all: auto.
      + destruct r2 as [y'' [r2' [e2']]].
        exists y''. split.
        * eapply cored_trans'. all: eassumption.
        * constructor. eapply eq_term_upto_univ_trans. all: eauto.
      + intros ? ? ?. assumption.
  Qed.

  Lemma eq_context_upto_nlctx :
    forall Γ,
      eq_context_upto eq Γ (nlctx Γ).
  Proof.
    intros Γ.
    induction Γ as [| [na [b|] A] Γ ih ].
    - constructor.
    - simpl. constructor.
      + eapply eq_term_upto_univ_tm_nl.
        all: auto.
      + simpl. eapply eq_term_upto_univ_tm_nl.
        all: auto.
      + assumption.
    - simpl. constructor.
      + simpl. eapply eq_term_upto_univ_tm_nl.
        all: auto.
      + assumption.
  Qed.

  Lemma cored_cored'_nl :
    forall Γ u v,
      cored Σ Γ u v ->
      cored' (nlctx Γ) (nl u) (nl v).
  Proof.
    intros Γ u v h.
    eapply cored_eq_context_upto in h.
    6: eapply eq_context_upto_nlctx.
    all: auto.
    - destruct h as [u' [r [e]]].
      eexists _, _. intuition eauto.
      + constructor. eapply eq_term_trans.
        * eapply eq_term_sym. eapply eq_term_tm_nl.
        * eapply upto_names_impl_eq_term. assumption.
      + constructor. eapply eq_term_sym. eapply eq_term_tm_nl.
    - intros ? ? ? []. auto.
    - intros ? ? ? r. apply Forall2_eq in r. apply map_inj in r.
      + subst. reflexivity.
      + intros ? ? H. inversion H. reflexivity.
  Qed.

  Lemma cored_cored' :
    forall Γ u v,
      cored Σ Γ u v ->
      cored' Γ u v.
  Proof.
    intros Γ u v h.
    exists u, v. intuition eauto.
    - constructor. eapply eq_term_refl.
    - constructor. eapply eq_term_refl.
  Qed.

End Alpha.
