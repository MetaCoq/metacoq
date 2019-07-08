(* Distributed under the terms of the MIT license.   *)
From Equations Require Import Equations.
From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From MetaCoq.Template Require Import config utils AstUtils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICWeakeningEnv PCUICWeakening
     PCUICClosed PCUICReduction.
Require Import ssreflect ssrbool.
Require Import String.
From MetaCoq.Template Require Import LibHypsNaming.
Local Open Scope string_scope.
Set Asymmetric Patterns.
Require Import CRelationClasses.
Require Import Equations.Type.Relation Equations.Type.Relation_Properties.

Reserved Notation " Σ ;;; Γ |- t == u " (at level 50, Γ, t, u at next level).

Lemma cumul_alt `{cf : checker_flags} Σ Γ t u :
  Σ ;;; Γ |- t <= u <~> { v & { v' & (red Σ Γ t v * red Σ Γ u v' * leq_term (snd Σ) v v')%type } }.
Proof.
  split.
  { induction 1. exists t, u. intuition auto; constructor.
    destruct IHX as (v' & v'' & (redv & redv') & leqv).
    exists v', v''. intuition auto. now eapply red_step.
    destruct IHX as (v' & v'' & (redv & redv') & leqv).
    exists v', v''. intuition auto. now eapply red_step. }
  { intros [v [v' [[redv redv'] Hleq]]]. apply red_alt in redv. apply red_alt in redv'.
    apply clos_rt_rt1n in redv.
    apply clos_rt_rt1n in redv'.
    induction redv. induction redv'. constructor; auto.
    econstructor 3; eauto.
    econstructor 2; eauto. }
Qed.

Lemma red_cumul `{cf : checker_flags} {Σ : global_context} {Γ t u} :
  red Σ Γ t u ->
  Σ ;;; Γ |- t <= u.
Proof.
  intros. apply red_alt in X. apply clos_rt_rt1n in X.
  induction X. apply cumul_refl'.
  econstructor 2; eauto.
Qed.

Lemma red_cumul_inv `{cf : checker_flags} {Σ : global_context} {Γ t u} :
  red Σ Γ t u ->
  Σ ;;; Γ |- u <= t.
Proof.
  intros. apply red_alt in X. apply clos_rt_rt1n in X.
  induction X. apply cumul_refl'.
  econstructor 3; eauto.
Qed.


Lemma eq_term_upto_univ_refl `{cf : checker_flags} Re Rle :
  CRelationClasses.Reflexive Re ->
  CRelationClasses.Reflexive Rle ->
  forall t, eq_term_upto_univ Re Rle t t.
Proof.
  intros hRe hRle.
  induction t in Rle, hRle |- * using term_forall_list_ind; simpl;
    try constructor; try solve [eapply All_All2; eauto]; try easy;
      try now apply All2_same.
  - destruct p. constructor; try easy.
    red in X. eapply All_All2; eauto.
  - eapply All_All2; eauto. simpl. intuition eauto.
  - eapply All_All2; eauto. simpl. intuition eauto.
Qed.

Lemma All_All2_refl {A : Type} {R} {l : list A} : All (fun x : A => R x x) l -> All2 R l l.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma eq_term_refl `{checker_flags} φ t : eq_term φ t t.
Proof.
  apply eq_term_upto_univ_refl ; intro ; apply eq_universe_refl.
Qed.

Lemma leq_term_refl `{checker_flags} φ t : leq_term φ t t.
Proof.
  apply eq_term_upto_univ_refl.
  - intro ; apply eq_universe_refl.
  - intro ; apply leq_universe_refl.
Qed.

Lemma eq_term_upto_univ_leq `{cf : checker_flags} :
  forall (Re Rle : universe -> universe -> Type) u v,
    (forall u u', Re u u' -> Rle u u') ->
    eq_term_upto_univ Re Re u v ->
    eq_term_upto_univ Re Rle u v.
Proof.
  intros Re Rle u v hR h.
  induction u in v, h |- * using term_forall_list_ind.
  all: simpl ; inversion h ;
       subst ; constructor ; try easy.
  all: eapply All2_impl ; eauto.
Qed.

Lemma eq_term_leq_term `{checker_flags} φ t u : eq_term φ t u -> leq_term φ t u.
Proof.
  intros h. eapply eq_term_upto_univ_leq ; eauto.
  eapply eq_universe_leq_universe.
Qed.

Lemma eq_term_App `{checker_flags} φ f f' :
  eq_term φ f f' ->
  isApp f = isApp f'.
Proof.
  inversion 1; reflexivity.
Qed.

Lemma eq_term_mkApps `{checker_flags} φ f l f' l' :
  eq_term φ f f' ->
  All2 (eq_term φ) l l' ->
  eq_term φ (mkApps f l) (mkApps f' l').
Proof.
  induction l in l', f, f' |- *; intro e; inversion_clear 1.
  - assumption.
  - cbn. eapply IHl. constructor; assumption. assumption.
Qed.

Lemma leq_term_App `{checker_flags} φ f f' :
  leq_term φ f f' ->
  isApp f = isApp f'.
Proof.
  inversion 1; reflexivity.
Qed.

Lemma leq_term_mkApps `{checker_flags} φ f l f' l' :
  leq_term φ f f' ->
  All2 (eq_term φ) l l' ->
  leq_term φ (mkApps f l) (mkApps f' l').
Proof.
  induction l in l', f, f' |- *; intro e; inversion_clear 1.
  - assumption.
  - cbn. apply IHl. constructor; try assumption. assumption.
Qed.

Lemma leq_term_antisym `{cf : checker_flags} Σ t u :
  leq_term Σ t u ->
  leq_term Σ u t ->
  eq_term Σ t u.
Proof.
Admitted.

Derive Signature for All2.

Lemma All2_sym {A} (P : A -> A -> Type) :
  CRelationClasses.Symmetric P ->
  CRelationClasses.Symmetric (All2 P).
Proof.
  intros hP x y h. induction h.
  - constructor.
  - constructor ; eauto.
Qed.

Lemma eq_term_upto_univ_sym :
  forall Re Rle,
    CRelationClasses.Symmetric Re ->
    CRelationClasses.Symmetric Rle ->
    CRelationClasses.Symmetric (eq_term_upto_univ Re Rle).
Proof.
  intros Re Rle he hle u v e.
  induction u in Rle, hle, v, e |- * using term_forall_list_ind.
  all: dependent destruction e.
  all: try solve [
    econstructor ; eauto ;
    try eapply All2_sym ; eauto
  ].
  - econstructor.
    eapply All2_All_mix_left in X as h; eauto.
    clear a X.
    induction h.
    + constructor.
    + destruct r as [h1 h2]. eapply h1 in h2 ; auto.
  - econstructor; eauto.
    eapply All2_All_mix_left in X as h; eauto.
    clear a X.
    induction h.
    + constructor.
    + destruct r as [h1 [h2 h3]]. eapply h1 in h3 ; auto.
  - econstructor.
    eapply All2_All_mix_left in X as h; eauto.
    clear a X.
    induction h.
    + constructor.
    + destruct r as [[h1 h2] [[h3 h4] h5]].
      eapply h1 in h3 ; auto.
  - econstructor.
    eapply All2_All_mix_left in X as h; eauto.
    clear a X.
    induction h.
    + constructor.
    + destruct r as [[h1 h2] [[h3 h4] h5]]. eapply h1 in h3 ; auto.
Qed.

Corollary eq_term_sym `{checker_flags} :
  forall G t u,
    eq_term G t u ->
    eq_term G u t.
Proof.
  intros G t u h.
  eapply eq_term_upto_univ_sym ; eauto.
  all: intros ? ? ? ; eapply eq_universe_sym ; eauto.
Qed.

Inductive conv_alt `{checker_flags} (Σ : global_context) (Γ : context) : term -> term -> Type :=
| conv_alt_refl t u : eq_term (snd Σ) t u -> Σ ;;; Γ |- t == u
| conv_alt_red_l t u v : red1 (fst Σ) Γ t v -> Σ ;;; Γ |- v == u -> Σ ;;; Γ |- t == u
| conv_alt_red_r t u v : Σ ;;; Γ |- t == v -> red1 (fst Σ) Γ u v -> Σ ;;; Γ |- t == u
where " Σ ;;; Γ |- t == u " := (@conv_alt _ Σ Γ t u) : type_scope.

Lemma red_conv_alt `{cf : checker_flags} Σ Γ t u :
  red (fst Σ) Γ t u ->
  Σ ;;; Γ |- t == u.
Proof.
  intros. apply red_alt in X. apply clos_rt_rt1n_iff in X.
  induction X. constructor. apply eq_term_refl.
  apply clos_rt_rt1n_iff in X. apply red_alt in X.
  econstructor 2; eauto.
Qed.
Hint Resolve red_conv_alt.

Lemma cumul_refl' `{cf : checker_flags} Σ Γ t : cumul Σ Γ t t.
Proof. apply cumul_refl, leq_term_refl. Qed.

Hint Resolve leq_term_refl cumul_refl' : core.

Lemma cumul_conv_alt `{cf : checker_flags} Σ Γ t u :
  Σ ;;; Γ |- t <= u -> Σ ;;; Γ |- u <= t -> Σ ;;; Γ |- t == u.
             (* (forall v, Σ ;;; Γ |- u == v -> Σ ;;; Γ |- t == v). *)
Proof.
  intros H. apply cumul_alt in H.
  destruct H as (v & v' & (redv & redv') & leqv).
  intros H'. apply cumul_alt in H'.
  destruct H' as (v0 & v'0 & (redv0 & redv'0) & leqv0).
  (** Needs confluence to show the two redexes can be joined *)
Admitted.

Lemma conv_conv_alt `{cf : checker_flags} Σ Γ t u :
  Σ ;;; Γ |- t = u <~> Σ ;;; Γ |- t == u.
Proof.
  split; induction 1. apply cumul_conv_alt in b; auto.
  constructor; constructor. now eapply eq_term_leq_term.
  eapply eq_term_leq_term; now apply eq_term_sym.
  constructor. econstructor 2; eauto. apply IHX.
  econstructor 3. 2:eauto. apply IHX.
  constructor. econstructor 3. 2:eauto. apply IHX.
  econstructor 2; eauto. apply IHX.
Qed.

Lemma conv_alt_red `{cf : checker_flags} :
  forall Σ Γ t u,
    Σ ;;; Γ |- t == u ->
    ∑ t' u',
      red Σ Γ t t' ×
      red Σ Γ u u' ×
      eq_term (snd Σ) t' u'.
Proof.
  intros Σ Γ t u h. induction h.
  - exists t, u. intuition auto.
  - destruct IHh as [t' [u' [? [? ?]]]].
    exists t', u'. intuition auto. now eapply red_step.
  - destruct IHh as [t' [u' [? [? ?]]]].
    exists t', u'. intuition auto. now eapply red_step.
Qed.

Lemma congr_cumul_prod : forall `{checker_flags} Σ Γ na na' M1 M2 N1 N2,
    conv Σ Γ M1 N1 ->
    cumul Σ (Γ ,, vass na M1) M2 N2 ->
    cumul Σ Γ (tProd na M1 M2) (tProd na' N1 N2).
Proof.
  intros.
Admitted.

Inductive conv_pb :=
| Conv
| Cumul.

Definition conv `{cf : checker_flags} leq Σ Γ u v :=
  match leq with
  | Conv => ∥ Σ ;;; Γ |- u = v ∥
  | Cumul => ∥ Σ ;;; Γ |- u <= v ∥
  end.

Lemma conv_conv_l `{cf : checker_flags} :
  forall Σ leq Γ u v,
      Σ ;;; Γ |- u = v ->
      conv leq Σ Γ u v.
Proof.
  intros Σ [] Γ u v [h1 h2].
  - cbn. constructor. constructor ; assumption.
  - cbn. constructor. assumption.
Qed.

Lemma conv_conv_r `{cf : checker_flags} :
  forall Σ leq Γ u v,
      Σ ;;; Γ |- u = v ->
      conv leq Σ Γ v u.
Proof.
  intros Σ [] Γ u v [h1 h2].
  - cbn. constructor. constructor ; assumption.
  - cbn. constructor. assumption.
Qed.

Lemma cumul_App_l `{cf : checker_flags} :
  forall {Σ Γ f g x},
    Σ ;;; Γ |- f <= g ->
    Σ ;;; Γ |- tApp f x <= tApp g x.
Proof.
  intros Σ Γ f g x h.
  induction h.
  - eapply cumul_refl. constructor.
    + assumption.
    + apply eq_term_refl.
  - eapply cumul_red_l ; try eassumption.
    econstructor. assumption.
  - eapply cumul_red_r ; try eassumption.
    econstructor. assumption.
Qed.

Lemma cumul_App_r `{cf : checker_flags} :
  forall {Σ Γ f u v},
    Σ ;;; Γ |- u = v ->
    Σ ;;; Γ |- tApp f u <= tApp f v.
Proof.
  intros Σ Γ f u v h.
  apply conv_conv_alt in h. induction h.
  - eapply cumul_refl. constructor.
    + apply leq_term_refl.
    + assumption.
  -  eapply cumul_red_l ; try eassumption.
    econstructor. assumption.
  - eapply cumul_red_r ; try eassumption.
    econstructor. assumption.
Qed.

Lemma conv_App_r `{cf : checker_flags} :
  forall {Σ Γ f x y},
    Σ ;;; Γ |- x = y ->
    Σ ;;; Γ |- tApp f x = tApp f y.
Proof.
  intros Σ Γ f x y h.
  eapply conv_conv_alt.
  apply conv_conv_alt in h. induction h.
  - constructor. constructor.
    + apply eq_term_refl.
    + assumption.
  - eapply conv_alt_red_l ; eauto.
    econstructor. assumption.
  - eapply conv_alt_red_r ; eauto.
    econstructor. assumption.
Qed.

Lemma conv_Prod_l `{cf : checker_flags} :
  forall {Σ Γ na na' A1 A2 B},
    Σ ;;; Γ |- A1 = A2 ->
    Σ ;;; Γ |- tProd na A1 B = tProd na' A2 B.
Proof.
  intros Σ Γ na na' A1 A2 B h.
  eapply conv_conv_alt.
  apply conv_conv_alt in h. induction h.
  - constructor. constructor.
    + assumption.
    + apply eq_term_refl.
  - eapply conv_alt_red_l ; eauto.
    econstructor. assumption.
  - eapply conv_alt_red_r ; eauto.
    econstructor. assumption.
Qed.

Lemma conv_Prod_r `{cf : checker_flags} :
  forall {Σ Γ na A B1 B2},
    Σ ;;; Γ ,, vass na A |- B1 = B2 ->
    Σ ;;; Γ |- tProd na A B1 = tProd na A B2.
Proof.
  intros Σ Γ na A B1 B2 h.
  eapply conv_conv_alt.
  apply conv_conv_alt in h. induction h.
  - constructor. constructor.
    + apply eq_term_refl.
    + assumption.
  - eapply conv_alt_red_l ; eauto.
    econstructor. assumption.
  - eapply conv_alt_red_r ; eauto.
    econstructor. assumption.
Qed.

Lemma cumul_Prod_r `{cf : checker_flags} :
  forall {Σ Γ na A B1 B2},
    Σ ;;; Γ ,, vass na A |- B1 <= B2 ->
    Σ ;;; Γ |- tProd na A B1 <= tProd na A B2.
Proof.
  intros Σ Γ na A B1 B2 h.
  induction h.
  - eapply cumul_refl. constructor.
    + apply eq_term_refl.
    + assumption.
  - eapply cumul_red_l ; try eassumption.
    econstructor. assumption.
  - eapply cumul_red_r ; try eassumption.
    econstructor. assumption.
Qed.

Lemma conv_cumul `{cf : checker_flags} :
  forall Σ Γ u v,
    Σ ;;; Γ |- u = v ->
    Σ ;;; Γ |- u <= v.
Proof.
  intros Σ Γ u v [? ?].
  assumption.
Qed.

Lemma conv_refl' `{cf : checker_flags} :
  forall Σ leq Γ t,
    conv leq Σ Γ t t.
Proof.
  intros Σ leq Γ t.
  destruct leq.
  - cbn. constructor. apply conv_refl.
  - cbn. constructor. apply cumul_refl'.
Qed.

Lemma conv_sym `{cf : checker_flags} :
  forall Σ Γ u v,
    Σ ;;; Γ |- u = v ->
    Σ ;;; Γ |- v = u.
Proof.
  intros Σ Γ u v [h1 h2].
  econstructor ; assumption.
Qed.

Lemma conv_conv `{cf : checker_flags} :
  forall {Σ Γ leq u v},
    ∥ Σ ;;; Γ |- u = v ∥ ->
    conv leq Σ Γ u v.
Proof.
  intros Σ Γ leq u v h.
  destruct leq.
  - assumption.
  - destruct h as [[h1 h2]]. cbn.
    constructor. assumption.
Qed.

Lemma eq_term_conv `{cf : checker_flags} :
  forall {Σ Γ u v},
    eq_term (snd Σ) u v ->
    Σ ;;; Γ |- u = v.
Proof.
  intros Σ Γ u v e.
  constructor.
  - eapply cumul_refl.
    eapply eq_term_leq_term. assumption.
  - eapply cumul_refl.
    eapply eq_term_leq_term.
    eapply eq_term_sym.
    assumption.
Qed.

Lemma conv_trans `{cf : checker_flags} :
  forall Σ Γ u v w,
    Σ ;;; Γ |- u = v ->
    Σ ;;; Γ |- v = w ->
    Σ ;;; Γ |- u = w.
Proof.
  intros Σ Γ u v w h1 h2.
  destruct h1, h2. constructor ; eapply cumul_trans ; eassumption.
Qed.

Lemma conv_trans' `{cf : checker_flags} :
  forall Σ leq Γ u v w,
    conv leq Σ Γ u v ->
    conv leq Σ Γ v w ->
    conv leq Σ Γ u w.
Proof.
  intros Σ leq Γ u v w h1 h2.
  destruct leq.
  - cbn in *. destruct h1, h2. constructor.
    eapply conv_trans ; eassumption.
  - cbn in *. destruct h1, h2. constructor. eapply cumul_trans ; eassumption.
Qed.

Lemma red_conv_l `{cf : checker_flags} :
  forall Σ leq Γ u v,
    red (fst Σ) Γ u v ->
    conv leq Σ Γ u v.
Proof.
  intros Σ leq Γ u v h.
  induction h.
  - apply conv_refl'.
  - eapply conv_trans' ; try eassumption.
    destruct leq.
    + simpl. constructor. constructor.
      * eapply cumul_red_l.
        -- eassumption.
        -- eapply cumul_refl'.
      * eapply cumul_red_r.
        -- eapply cumul_refl'.
        -- assumption.
    + simpl. constructor.
      eapply cumul_red_l.
      * eassumption.
      * eapply cumul_refl'.
Qed.

Lemma red_conv_r `{cf : checker_flags} :
  forall Σ leq Γ u v,
    red (fst Σ) Γ u v ->
    conv leq Σ Γ v u.
Proof.
  intros Σ leq Γ u v h.
  induction h.
  - apply conv_refl'.
  - eapply conv_trans' ; try eassumption.
    destruct leq.
    + simpl. constructor. constructor.
      * eapply cumul_red_r.
        -- eapply cumul_refl'.
        -- assumption.
      * eapply cumul_red_l.
        -- eassumption.
        -- eapply cumul_refl'.
    + simpl. constructor.
      eapply cumul_red_r.
      * eapply cumul_refl'.
      * assumption.
Qed.

Lemma conv_Prod `{cf : checker_flags} :
  forall Σ leq Γ na A1 A2 B1 B2,
    Σ ;;; Γ |- A1 = A2 ->
    conv leq Σ (Γ,, vass na A1) B1 B2 ->
    conv leq Σ Γ (tProd na A1 B1) (tProd na A2 B2).
Proof.
  intros Σ [] Γ na A1 A2 B1 B2 h1 h2.
  - simpl in *. destruct h2 as [h2]. constructor.
    eapply conv_trans.
    + eapply conv_Prod_r. eassumption.
    + eapply conv_Prod_l. eassumption.
  - simpl in *. destruct h2 as [h2]. constructor.
    eapply cumul_trans.
    + eapply cumul_Prod_r. eassumption.
    + eapply conv_cumul. eapply conv_Prod_l. assumption.
Qed.

Lemma cumul_Case_c `{cf : checker_flags} :
  forall Σ Γ indn p brs u v,
    Σ ;;; Γ |- u = v ->
    Σ ;;; Γ |- tCase indn p u brs <= tCase indn p v brs.
Proof.
  intros Σ Γ [ind n] p brs u v h.
  eapply conv_conv_alt in h.
  induction h.
  - constructor. constructor.
    + eapply eq_term_refl.
    + assumption.
    + eapply All2_same.
      intros. split ; eauto. eapply eq_term_refl.
  - eapply cumul_red_l ; eauto.
    constructor. assumption.
  - eapply cumul_red_r ; eauto.
    constructor. assumption.
Qed.

Lemma cumul_Proj_c `{cf : checker_flags} :
  forall Σ Γ p u v,
    Σ ;;; Γ |- u = v ->
    Σ ;;; Γ |- tProj p u <= tProj p v.
Proof.
  intros Σ Γ p u v h.
  eapply conv_conv_alt in h.
  induction h.
  - eapply cumul_refl. constructor. assumption.
  - eapply cumul_red_l ; try eassumption.
    econstructor. assumption.
  - eapply cumul_red_r ; try eassumption.
    econstructor. assumption.
Qed.

Lemma conv_App_l `{cf : checker_flags} :
  forall {Σ Γ f g x},
    Σ ;;; Γ |- f = g ->
    Σ ;;; Γ |- tApp f x = tApp g x.
Proof.
  intros Σ Γ f g x h.
  eapply conv_conv_alt.
  apply conv_conv_alt in h. induction h.
  - constructor. constructor.
    + assumption.
    + apply eq_term_refl.
  - eapply conv_alt_red_l ; eauto.
    econstructor. assumption.
  - eapply conv_alt_red_r ; eauto.
    econstructor. assumption.
Qed.

Lemma conv_Case_c `{cf : checker_flags} :
  forall Σ Γ indn p brs u v,
    Σ ;;; Γ |- u = v ->
    Σ ;;; Γ |- tCase indn p u brs = tCase indn p v brs.
Proof.
  intros Σ Γ [ind n] p brs u v h.
  eapply conv_conv_alt in h.
  apply conv_conv_alt.
  induction h.
  - constructor. constructor.
    + eapply eq_term_refl.
    + assumption.
    + eapply All2_same.
      intros. split ; eauto. eapply eq_term_refl.
  - eapply conv_alt_red_l ; eauto.
    constructor. assumption.
  - eapply conv_alt_red_r ; eauto.
    constructor. assumption.
Qed.

Lemma conv_Proj_c `{cf : checker_flags} :
  forall Σ Γ p u v,
    Σ ;;; Γ |- u = v ->
    Σ ;;; Γ |- tProj p u = tProj p v.
Proof.
  intros Σ Γ p u v h.
  eapply conv_conv_alt in h.
  apply conv_conv_alt.
  induction h.
  - eapply conv_alt_refl. constructor. assumption.
  - eapply conv_alt_red_l ; try eassumption.
    econstructor. assumption.
  - eapply conv_alt_red_r ; try eassumption.
    econstructor. assumption.
Qed.

Lemma conv_Lambda_l `{cf : checker_flags} :
  forall Σ Γ na A b na' A',
    Σ ;;; Γ |- A = A' ->
    Σ ;;; Γ |- tLambda na A b = tLambda na' A' b.
Proof.
  intros Σ Γ na A b na' A' h.
  eapply conv_conv_alt in h.
  apply conv_conv_alt.
  induction h.
  - eapply conv_alt_refl. constructor.
    + assumption.
    + eapply eq_term_refl.
  - eapply conv_alt_red_l ; try eassumption.
    econstructor. assumption.
  - eapply conv_alt_red_r ; try eassumption.
    econstructor. assumption.
Qed.

Lemma conv_Lambda_r `{cf : checker_flags} :
  forall Σ Γ na A b b',
    Σ ;;; Γ,, vass na A |- b = b' ->
    Σ ;;; Γ |- tLambda na A b = tLambda na A b'.
Proof.
  intros Σ Γ na A b b' h.
  eapply conv_conv_alt in h.
  apply conv_conv_alt.
  induction h.
  - eapply conv_alt_refl. constructor.
    + eapply eq_term_refl.
    + assumption.
  - eapply conv_alt_red_l ; try eassumption.
    econstructor. assumption.
  - eapply conv_alt_red_r ; try eassumption.
    econstructor. assumption.
Qed.

Lemma cumul_LetIn_bo `{cf : checker_flags} :
  forall Σ Γ na ty t u u',
    Σ ;;; Γ ,, vdef na ty t |- u <= u' ->
    Σ ;;; Γ |- tLetIn na ty t u <= tLetIn na ty t u'.
Proof.
  intros Σ Γ na ty t u u' h.
  induction h.
  - eapply cumul_refl. constructor.
    all: try eapply eq_term_refl.
    assumption.
  - eapply cumul_red_l ; try eassumption.
    econstructor. assumption.
  - eapply cumul_red_r ; try eassumption.
    econstructor. assumption.
Qed.

Lemma cumul_Lambda_r `{cf : checker_flags} :
  forall Σ Γ na A b b',
    Σ ;;; Γ,, vass na A |- b <= b' ->
    Σ ;;; Γ |- tLambda na A b <= tLambda na A b'.
Proof.
  intros Σ Γ na A b b' h.
  induction h.
  - eapply cumul_refl. constructor.
    + eapply eq_term_refl.
    + assumption.
  - eapply cumul_red_l ; try eassumption.
    econstructor. assumption.
  - eapply cumul_red_r ; try eassumption.
    econstructor. assumption.
Qed.

Lemma cumul_it_mkLambda_or_LetIn `{cf : checker_flags} :
  forall Σ Δ Γ u v,
    Σ ;;; (Δ ,,, Γ) |- u <= v ->
    Σ ;;; Δ |- it_mkLambda_or_LetIn Γ u <= it_mkLambda_or_LetIn Γ v.
Proof.
  intros Σ Δ Γ u v h. revert Δ u v h.
  induction Γ as [| [na [b|] A] Γ ih ] ; intros Δ u v h.
  - assumption.
  - simpl. cbn. eapply ih.
    eapply cumul_LetIn_bo. assumption.
  - simpl. cbn. eapply ih.
    eapply cumul_Lambda_r. assumption.
Qed.

Lemma cumul_it_mkProd_or_LetIn `{cf : checker_flags} :
  forall Σ Δ Γ B B',
    Σ ;;; (Δ ,,, Γ) |- B <= B' ->
    Σ ;;; Δ |- it_mkProd_or_LetIn Γ B <= it_mkProd_or_LetIn Γ B'.
Proof.
  intros Σ Δ Γ B B' h.
  induction Γ as [| [na [b|] A] Γ ih ] in Δ, B, B', h |- *.
  - assumption.
  - simpl. cbn. eapply ih.
    eapply cumul_LetIn_bo. assumption.
  - simpl. cbn. eapply ih.
    eapply cumul_Prod_r. assumption.
Qed.