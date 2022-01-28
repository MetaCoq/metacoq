(* Distributed under the terms of the MIT license. *)
From Coq Require Import CRelationClasses.
From Equations.Type Require Import Relation Relation_Properties.
From MetaCoq.Template Require Import config utils BasicAst.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICLiftSubst PCUICEquality PCUICUnivSubst
     PCUICReduction.

Set Default Goal Selector "!".

(** * Definition of cumulativity and conversion relations *)

Reserved Notation " Σ ;;; Γ |- t <=[ Rle ] u" (at level 50, Γ, t, u at next level,
  format "Σ  ;;;  Γ  |-  t  <=[ Rle ] u").

Definition leq_term_ext `{checker_flags} (Σ : global_env_ext) Rle t u := eq_term_upto_univ Σ (eq_universe Σ) Rle t u.

Notation " Σ ⊢ t <===[ Rle , napp ] u" := (eq_term_upto_univ Σ (eq_universe Σ) Rle t u) (at level 50, t, u at next level).

(** ** Cumulativity *)

Inductive cumulAlgo0 `{checker_flags} (Σ : global_env_ext) Rle (Γ : context) : term -> term -> Type :=
| cumul_refl t u : Σ ⊢ t <===[ Rle , 0] u -> Σ ;;; Γ |- t <=[Rle] u
| cumul_red_l t u v : Σ ;;; Γ |- t ⇝ v -> Σ ;;; Γ |- v <=[Rle] u -> Σ ;;; Γ |- t <=[Rle] u
| cumul_red_r t u v : Σ ;;; Γ |- t <=[Rle] v -> Σ ;;; Γ |- u ⇝ v -> Σ ;;; Γ |- t <=[Rle] u
where " Σ ;;; Γ |- t <=[ Rle ] u " := (cumulAlgo0 Σ Rle Γ t u) : type_scope.

Definition cumulAlgo `{checker_flags} Σ Γ t u := Σ ;;; Γ |- t <=[ leq_universe Σ ] u.

Definition convAlgo `{checker_flags} Σ Γ t u := Σ ;;; Γ |- t <=[ eq_universe Σ ] u.

Notation " Σ ;;; Γ |- t <= u " := (cumulAlgo Σ Γ t u) (at level 50, Γ, t, u at next level).
Notation " Σ ;;; Γ |- t = u " := (convAlgo Σ Γ t u) (at level 50, Γ, t, u at next level).

#[global]
Hint Resolve cumul_refl : pcuic.

Module PCUICConversionParAlgo <: EnvironmentTyping.ConversionParSig PCUICTerm PCUICEnvironment PCUICEnvTyping.
  Definition conv := @convAlgo.
  Definition cumul := @cumulAlgo.
End PCUICConversionParAlgo.

Module PCUICConversionAlgo := EnvironmentTyping.Conversion PCUICTerm PCUICEnvironment PCUICEnvTyping PCUICConversionParAlgo.
Include PCUICConversionAlgo.

Notation conv_context Σ Γ Γ' := (All2_fold (conv_decls Σ) Γ Γ').
Notation cumul_context Σ Γ Γ' := (All2_fold (cumul_decls Σ) Γ Γ').

#[global]
Instance conv_decls_refl {cf:checker_flags} Σ Γ Γ' : Reflexive (conv_decls Σ Γ Γ').
Proof.
  intros x. destruct x as [na [b|] ty]; constructor; auto.
  all:constructor; apply eq_term_refl.
Qed.

#[global]
Instance cumul_decls_refl {cf:checker_flags} Σ Γ Γ' : Reflexive (cumul_decls Σ Γ Γ').
Proof.
  intros x. destruct x as [na [b|] ty]; constructor; auto.
  all:constructor; apply eq_term_refl || apply leq_term_refl.
Qed.

Lemma cumul_alt `{cf : checker_flags} Σ Γ t u :
  Σ ;;; Γ |- t <= u <~> { v & { v' & (red Σ Γ t v * red Σ Γ u v' * 
  leq_term_ext Σ (leq_universe Σ) v v')%type } }.
Proof.
  split.
  - induction 1.
    + exists t, u. intuition auto.
    + destruct IHX as (v' & v'' & (redv & redv') & leqv).
      exists v', v''. intuition auto. now eapply red_step.
    + destruct IHX as (v' & v'' & (redv & redv') & leqv).
      exists v', v''. intuition auto. now eapply red_step.
  - intros [v [v' [[redv redv'] Hleq]]].
    apply clos_rt_rt1n in redv.
    apply clos_rt_rt1n in redv'.
    induction redv.
    * induction redv'.
    ** constructor; auto.
    ** econstructor 3; eauto. eapply IHredv'; eauto. 
    * econstructor 2; eauto. eapply IHredv; eauto.
Qed.

#[global]
Instance cumul_refl' {cf:checker_flags} Σ Γ : Reflexive (cumulAlgo Σ Γ).
Proof.
  intro; constructor. unfold leq_term_ext. reflexivity.
Qed.

#[global]
Instance conv_refl' {cf:checker_flags} Σ Γ : Reflexive (convAlgo Σ Γ).
Proof.
  intro; constructor. unfold leq_term_ext. reflexivity.
Qed.

Lemma red_cumul `{cf : checker_flags} {Σ : global_env_ext} {Γ t u} :
  red Σ Γ t u ->
  Σ ;;; Γ |- t <= u.
Proof.
  intros. apply clos_rt_rt1n in X.
  induction X.
  - reflexivity.
  - econstructor 2. all: eauto.
Qed.

Lemma red_cumul_inv `{cf : checker_flags} {Σ : global_env_ext} {Γ t u} :
  red Σ Γ t u ->
  Σ ;;; Γ |- u <= t.
Proof.
  intros. apply clos_rt_rt1n in X.
  induction X.
  - reflexivity.
  - econstructor 3. all: eauto.
Qed.

Lemma red_cumul_cumul `{cf : checker_flags} {Σ : global_env_ext} {Γ t u v} :
  red Σ Γ t u -> Σ ;;; Γ |- u <= v -> Σ ;;; Γ |- t <= v.
Proof.
  intros. apply clos_rt_rt1n in X.
  induction X. 1: auto.
  econstructor 2; eauto. eapply IHX; eauto.
Qed.

Lemma red_cumul_cumul_inv `{cf : checker_flags} {Σ : global_env_ext} {Γ t u v} :
  red Σ Γ t v -> Σ ;;; Γ |- u <= v -> Σ ;;; Γ |- u <= t.
Proof.
  intros. apply clos_rt_rt1n in X.
  induction X. 1: auto.
  econstructor 3.
  - eapply IHX. eauto.
  - eauto.
Qed.

Lemma conv_cumul2 {cf:checker_flags} Σ Γ t u :
  Σ ;;; Γ |- t = u -> (Σ ;;; Γ |- t <= u) * (Σ ;;; Γ |- u <= t).
Proof.
  induction 1.
  - split; constructor; now apply eq_term_leq_term.
  - destruct IHX as [H1 H2]. split.
    * econstructor 2; eassumption.
    * econstructor 3; eassumption.
  - destruct IHX as [H1 H2]. split.
    * econstructor 3; eassumption.
    * econstructor 2; eassumption.
Qed.

Lemma conv_cumul {cf:checker_flags} Σ Γ t u :
  Σ ;;; Γ |- t = u -> Σ ;;; Γ |- t <= u.
Proof.
  intro H; now apply conv_cumul2 in H.
Qed.

Lemma conv_cumul_inv {cf:checker_flags} Σ Γ t u :
  Σ ;;; Γ |- u = t -> Σ ;;; Γ |- t <= u.
Proof.
  intro H; now apply conv_cumul2 in H.
Qed.

Lemma red_conv {cf:checker_flags} (Σ : global_env_ext) Γ t u
  : red Σ Γ t u -> Σ ;;; Γ |- t = u.
Proof.
  intros H%clos_rt_rt1n_iff.
  induction H.
  - reflexivity.
  - econstructor 2; eauto. 
Qed.

#[global]
Hint Resolve red_conv : core.

Lemma eq_term_App `{checker_flags} Σ φ f f' :
  eq_term Σ φ f f' ->
  isApp f = isApp f'.
Proof.
  inversion 1; reflexivity.
Qed.

Lemma eq_term_eq_term_napp {cf:checker_flags} Σ ϕ napp t t' :
  eq_term Σ ϕ t t' -> 
  eq_term_upto_univ_napp Σ (eq_universe ϕ) (eq_universe ϕ) napp t t'.
Proof.
  intros. eapply eq_term_upto_univ_impl. 5:eauto.
  4:auto with arith. all:typeclasses eauto.
Qed.

Lemma leq_term_leq_term_napp {cf:checker_flags} Σ ϕ napp t t' :
  leq_term Σ ϕ t t' -> 
  eq_term_upto_univ_napp Σ (eq_universe ϕ) (leq_universe ϕ) napp t t'.
Proof.
  intros. eapply eq_term_upto_univ_impl. 5:eauto.
  4:auto with arith. all:typeclasses eauto.
Qed.

Lemma eq_term_mkApps `{checker_flags} Σ φ f l f' l' :
  eq_term Σ φ f f' ->
  All2 (eq_term Σ φ) l l' ->
  eq_term Σ φ (mkApps f l) (mkApps f' l').
Proof.
  induction l in l', f, f' |- *; intro e; inversion_clear 1.
  - assumption.
  - cbn. eapply IHl.
    + constructor; auto. now apply eq_term_eq_term_napp.
    + assumption.
Qed.

Lemma leq_term_App `{checker_flags} Σ φ f f' :
  leq_term Σ φ f f' ->
  isApp f = isApp f'.
Proof.
  inversion 1; reflexivity.
Qed.

Lemma leq_term_mkApps `{checker_flags} Σ φ f l f' l' :
  leq_term Σ φ f f' ->
  All2 (eq_term Σ φ) l l' ->
  leq_term Σ φ (mkApps f l) (mkApps f' l').
Proof.
  induction l in l', f, f' |- *; intro e; inversion_clear 1.
  - assumption.
  - cbn. apply IHl.
    + constructor; try assumption.
      now eapply leq_term_leq_term_napp.
    + assumption.
Qed.

#[global]
Hint Resolve leq_term_refl cumul_refl' : core.

Lemma red_conv_conv `{cf : checker_flags} Σ Γ t u v :
  red (fst Σ) Γ t u -> Σ ;;; Γ |- u = v -> Σ ;;; Γ |- t = v.
Proof.
  intros. apply clos_rt_rt1n_iff in X.
  induction X; auto.
  now econstructor 2.
Qed.

Lemma red_conv_conv_inv `{cf : checker_flags} Σ Γ t u v :
  red (fst Σ) Γ t u -> Σ ;;; Γ |- v = u -> Σ ;;; Γ |- v = t.
Proof.
  intros X%clos_rt_rt1n_iff.
  induction X; auto.
  now econstructor 3; [eapply IHX|]; eauto.
Qed.

#[global]
Instance conv_sym `{cf : checker_flags} (Σ : global_env_ext) Γ :
  Symmetric (convAlgo Σ Γ).
Proof.
  intros t u X. induction X.
  - eapply eq_term_sym in e; now constructor.
  - eapply red_conv_conv_inv.
    + eapply red1_red in r. eauto.
    + eauto.
  - eapply red_conv_conv.
    + eapply red1_red in r. eauto.
    + eauto.
Qed.

Lemma conv_alt_red {cf : checker_flags} {Σ : global_env_ext} {Γ : context} {t u : term} :
  Σ;;; Γ |- t = u <~> (∑ v v' : term, (red Σ Γ t v × red Σ Γ u v') × 
    eq_term Σ (global_ext_constraints Σ) v v').
Proof.
  split.
  - induction 1.
    * exists t, u; intuition auto.
    * destruct IHX as [? [? [? ?]]].
      exists x, x0; intuition auto. eapply red_step; eauto.
    * destruct IHX as [? [? [? ?]]].
      exists x, x0; intuition auto. eapply red_step; eauto.
  - destruct 1 as [? [? [[? ?] ?]]].
    eapply red_conv_conv; eauto.
    eapply red_conv_conv_inv; eauto. now constructor.
Qed.

Definition conv_pb_rel {cf:checker_flags} (pb : conv_pb) Σ :=
  match pb with
  | Conv => eq_universe Σ
  | Cumul => leq_universe Σ
  end.

Definition conv_pb_dir (pb : conv_pb) :=
  match pb with
  | Conv => false
  | Cumul => true
  end.

Coercion conv_pb_dir : conv_pb >-> bool.

Definition eq_termp_napp {cf:checker_flags} (leq : conv_pb) (Σ : global_env_ext) napp :=
  compare_term_napp leq Σ Σ napp.

Notation eq_termp leq Σ := (compare_term (conv_pb_dir leq) Σ Σ).

Lemma eq_term_eq_termp {cf:checker_flags} leq (Σ : global_env_ext) x y :
  eq_term Σ Σ x y ->
  eq_termp leq Σ x y.
Proof.
  destruct leq; [easy|].
  cbn.
  apply eq_term_upto_univ_leq; auto.
  typeclasses eauto.
Qed.

Lemma cumul_App_l {cf:checker_flags} :
  forall {Σ Γ f g x},
    Σ ;;; Γ |- f <= g ->
    Σ ;;; Γ |- tApp f x <= tApp g x.
Proof.
  intros Σ Γ f g x h.
  induction h.
  - eapply cumul_refl. constructor.
    + apply leq_term_leq_term_napp. assumption.
    + apply eq_term_refl.
  - eapply cumul_red_l ; try eassumption.
    econstructor. assumption.
  - eapply cumul_red_r ; try eassumption.
    econstructor. assumption.
Qed.

Section ContextConversion.
  Context {cf : checker_flags}.
  Context (Σ : global_env_ext).

  Notation conv_context Γ Γ' := (All2_fold (conv_decls Σ) Γ Γ').
  Notation cumul_context Γ Γ' := (All2_fold (cumul_decls Σ) Γ Γ').

  Global Instance conv_ctx_refl : Reflexive (All2_fold (conv_decls Σ)).
  Proof.
    intro Γ; induction Γ; try econstructor; auto.
    destruct a as [na [b|] ty]; constructor; auto; pcuic; eapply conv_refl'. 
  Qed.

  Global Instance cumul_ctx_refl : Reflexive (All2_fold (cumul_decls Σ)).
  Proof.
    intro Γ; induction Γ; try econstructor; auto.
    destruct a as [na [b|] ty];
     econstructor; eauto; pcuic; try eapply conv_refl'; eapply cumul_refl'.
  Qed.

  Definition conv_ctx_refl' Γ : conv_context Γ Γ
  := conv_ctx_refl Γ.

  Definition cumul_ctx_refl' Γ : cumul_context Γ Γ
    := cumul_ctx_refl Γ.

End ContextConversion.
