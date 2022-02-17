(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import
  PCUICAst PCUICAstUtils PCUICTyping PCUICSafeLemmata PCUICValidity
  PCUICReduction PCUICEquality PCUICConfluence PCUICUnivSubstitutionConv
  PCUICUnivSubstitutionTyp.

Require Import Equations.Prop.DepElim.

(** We assume normalisation of the reduction.
    We state is as well-foundedness of the reduction.
*)

Record normalizing_flags {cf : checker_flags} : Prop :=
  { nor_check_univs :> check_univs }.

Existing Class normalizing_flags.

#[local] Instance default_normalizing :
  @normalizing_flags default_checker_flags.
Proof.
  now constructor.
Qed.

#[local] Instance extraction_normalizing :
  @normalizing_flags extraction_checker_flags.
Proof.
  now constructor.
Qed.

Section Normalisation.

  Context {cf : checker_flags} {no : normalizing_flags}.
  Context (Σ : global_env_ext).

  Axiom normalisation :
    wf_ext Σ ->
    forall Γ t,
      welltyped Σ Γ t ->
      Acc (cored Σ Γ) t.

End Normalisation.


(** Since we are working with name annotations, reduction is sensitive to names.
    In this section we provide cored' which corresponds to reduction up to
    α-renaming, as well as the necessary lemmata to show it is well-founded and
    can be used instead of the usual reduction as a measure.
*)
Section Alpha.

  Context {cf : checker_flags} {no : normalizing_flags}.
  Context (Σ : global_env_ext).
  Context (hΣ : ∥ wf_ext Σ ∥).

  Notation eqt u v :=
    (∥ eq_term Σ (global_ext_constraints Σ) u v ∥).

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
    - eapply red1_eq_term_upto_univ_r in r. 10: eassumption.
      all:tc.
      destruct r as [u' [r e]].
      exists u'. split.
      * constructor. assumption.
      * constructor. etransitivity. 1: eauto.
        now symmetry.
    - specialize (IHr1 y v).
      destruct IHr1 as [y' [h1 [e1]]]; auto. reflexivity.
      specialize (IHr2 u y').
      destruct IHr2 as [u' [h2 ?]]; auto. now symmetry.
      exists u'. split.
      + eapply cored_trans'. all: eauto.
      + assumption.
  Qed.

  Corollary cored_upto :
    forall Γ u v v',
      cored Σ Γ u v ->
      eq_term Σ Σ v v' ->
      exists u', cored Σ Γ u' v' /\ eqt u u'.
  Proof.
    intros Γ u v v' h e.
    eapply cored'_postpone.
    exists u, v. intuition eauto.
    - constructor. reflexivity.
    - constructor. now symmetry.
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
      forall u', eq_term Σ Σ u u' -> Acc (cored' Γ) u'.
  Proof.
    intros Γ u h. induction h as [u h ih].
    intros u' e. constructor. intros v [v' [u'' [r [[e1] [e2]]]]].
    assert (ee : eq_term Σ Σ u'' u).
    { symmetry. etransitivity. all: eassumption. }
    eapply cored_upto in r as hh. 2: exact ee.
    destruct hh as [v'' [r' [e']]].
    eapply ih.
    - eassumption.
    - symmetry; etransitivity; eassumption.
  Qed.

  Lemma normalisation_upto :
    forall Γ u,
      welltyped Σ Γ u ->
      Acc (cored' Γ) u.
  Proof.
    destruct hΣ.
    intros Γ u h.
    apply normalisation in h.
    2: assumption.
    eapply Acc_cored_cored'.
    - eassumption.
    - reflexivity.
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
      SubstUnivPreserving Rle ->
      RelationClasses.Symmetric Re ->
      RelationClasses.Transitive Re ->
      RelationClasses.Transitive Rle ->
      RelationClasses.subrelation Re Rle ->
      eq_term_upto_univ Σ Re Rle u u' ->
      cored Σ Γ v u ->
      exists v', cored Σ Γ v' u' /\ ∥ eq_term_upto_univ Σ Re Rle v v' ∥.
  Proof.
    intros Re Rle Γ u v u' X X0 X1 X2 X3 X4 X5 X6 e h.
    apply cored_alt in h as [h].
    induction h in u', e |- *.
    - eapply red1_eq_term_upto_univ_l in r. 9: eauto. all: auto.
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
      eq_context_upto Σ Re Re Γ Δ ->
      cored Σ Γ u v ->
      exists u', cored Σ Δ u' v /\ ∥ eq_term_upto_univ Σ Re Re u u' ∥.
  Proof.
    intros Re Γ Δ u v hRe1 hRe2 hRe3 hRe4 e h.
    apply cored_alt in h as [h].
    induction h.
    - eapply red1_eq_context_upto_l in r. all: eauto. 2:tc.
      destruct r as [? [? ?]].
      eexists. split.
      + constructor. eassumption.
      + constructor. assumption.
    - destruct IHh1 as [x' [r1 [e1]]].
      destruct IHh2 as [y' [r2 [e2]]].
      eapply cored_eq_term_upto in r2. 10: exact e1. all: auto.
      2:tc.
      destruct r2 as [y'' [r2' [e2']]].
      exists y''. split.
      * eapply cored_trans'. all: eassumption.
      * constructor. eapply eq_term_upto_univ_trans. all: eauto.
  Qed.

  (* Lemma eq_context_upto_nlctx :
    forall Γ,
      eq_context_upto Σ eq eq Γ (nlctx Γ).
  Proof.
    intros Γ.
    induction Γ as [| [na [b|] A] Γ ih ].
    - constructor.
    - simpl. constructor; simpl; try apply binder_anonymize; tas.
      + constructor; tas; auto. eapply eq_term_upto_univ_tm_nl.
        all: auto.
        eapply eq_term_upto_univ_tm_nl.
        all: auto.
    - simpl. constructor; auto. constructor.
      + apply binder_anonymize.
      + simpl. eapply eq_term_upto_univ_tm_nl.
        all: auto.
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
        * eapply eq_term_upto_univ_impl; eauto. all:typeclasses eauto.
      + constructor. eapply eq_term_sym. eapply eq_term_tm_nl.
    - intros ? ? ? []. auto.
    - intros ? ? ? r. apply Forall2_eq in r. apply map_inj in r.
      + subst. reflexivity.
      + apply Universe.make_inj.
  Qed. *)

  Lemma cored_cored' :
    forall Γ u v,
      cored Σ Γ u v ->
      cored' Γ u v.
  Proof.
    intros Γ u v h.
    exists u, v. intuition eauto.
    - constructor. reflexivity.
    - constructor. reflexivity.
  Qed.

End Alpha.
