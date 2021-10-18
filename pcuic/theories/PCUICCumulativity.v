(* Distributed under the terms of the MIT license. *)
From Coq Require Import CRelationClasses.
From Equations.Type Require Import Relation Relation_Properties.
From MetaCoq.Template Require Import config utils BasicAst.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICLiftSubst PCUICEquality PCUICUnivSubst
     PCUICContextRelation PCUICReduction.

Set Default Goal Selector "!".

(** * Definition of cumulativity and conversion relations

The "natural" definition of conversion is given by [conv0]. It is the reflexive
symmetric transitive closure of beta redution + equality modulo universes.
It turns out to be equivalent to [conv1]: only beta reduction needs to be symmetrized.
Cumulativity is defined in the same style ([cumul1]), not symmetrizing [leq_term] because
it is oriented.

Those definitions are NOT used in the definition of typing. Instead we use [cumul] and
[conv] which are defined as "reducing to a common term". It tunrs out to be equivalent
to [conv1] and [cumul1] by confluence. It will be shown afterward, in PCUICConversion.v.
*)

Section ConvCumulDefs.
  Context {cf:checker_flags} (Σ : global_env_ext) (Γ : context).

  Definition conv0 : relation term
    := clos_refl_sym_trans (relation_disjunction (red1 Σ Γ) (eq_term Σ Σ)).

  Definition conv1 : relation term
    := clos_refl_trans (relation_disjunction (clos_sym (red1 Σ Γ)) (eq_term Σ Σ)).

  Lemma conv0_conv1 M N :
    conv0 M N <~> conv1 M N.
  Proof.
    split; intro H.
    - induction H.
      + constructor. now destruct r; [left; left|right].
      + reflexivity.
      + now apply clos_rt_trans_Symmetric.
      + etransitivity; eassumption.
    - induction H.
      + destruct r as [[]|].
        * now constructor; left.
        * now symmetry; constructor; left.
        * now constructor; right.
      + reflexivity.
      + etransitivity; eassumption.
  Defined.

  Definition cumul1 : relation term
    := clos_refl_trans (relation_disjunction (clos_sym (red1 Σ Γ)) (leq_term Σ Σ)).

End ConvCumulDefs.

(* todo mode typing notation *)
Reserved Notation " Σ ;;; Γ |- t : T " (at level 50, Γ, t, T at next level).
Reserved Notation " Σ ;;; Γ |- t <= u " (at level 50, Γ, t, u at next level).
Reserved Notation " Σ ;;; Γ |- t = u " (at level 50, Γ, t, u at next level).

(** ** Cumulativity *)

Inductive cumul `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
| cumul_refl t u : leq_term Σ.1 (global_ext_constraints Σ) t u -> Σ ;;; Γ |- t <= u
| cumul_red_l t u v : red1 Σ.1 Γ t v -> Σ ;;; Γ |- v <= u -> Σ ;;; Γ |- t <= u
| cumul_red_r t u v : Σ ;;; Γ |- t <= v -> red1 Σ.1 Γ u v -> Σ ;;; Γ |- t <= u

where " Σ ;;; Γ |- t <= u " := (cumul Σ Γ t u) : type_scope.

(** *** Conversion   
 *)

Inductive conv `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
| conv_refl t u : eq_term Σ.1 (global_ext_constraints Σ) t u -> Σ ;;; Γ |- t = u
| conv_red_l t u v : red1 Σ Γ t v -> Σ ;;; Γ |- v = u -> Σ ;;; Γ |- t = u
| conv_red_r t u v : Σ ;;; Γ |- t = v -> red1 (fst Σ) Γ u v -> Σ ;;; Γ |- t = u

where " Σ ;;; Γ |- t = u " := (@conv _ Σ Γ t u) : type_scope.

#[global]
Hint Resolve cumul_refl conv_refl : pcuic.

Module PCUICConversionPar <: EnvironmentTyping.ConversionParSig PCUICTerm PCUICEnvironment PCUICEnvTyping.
  Definition conv := @conv.
  Definition cumul := @cumul.
End PCUICConversionPar.

Module PCUICConversion := EnvironmentTyping.Conversion PCUICTerm PCUICEnvironment PCUICEnvTyping PCUICConversionPar.
Include PCUICConversion.

Notation conv_context Σ Γ Γ' := (All2_fold (conv_decls Σ) Γ Γ').
Notation cumul_context Σ Γ Γ' := (All2_fold (cumul_decls Σ) Γ Γ').

Instance conv_decls_refl {cf:checker_flags} Σ Γ Γ' : Reflexive (conv_decls Σ Γ Γ').
Proof.
  intros x. destruct x as [na [b|] ty]; constructor; auto.
  all:constructor; apply eq_term_refl.
Qed.

Instance cumul_decls_refl {cf:checker_flags} Σ Γ Γ' : Reflexive (cumul_decls Σ Γ Γ').
Proof.
  intros x. destruct x as [na [b|] ty]; constructor; auto.
  all:constructor; apply eq_term_refl || apply leq_term_refl.
Qed.

Lemma cumul_alt `{cf : checker_flags} Σ Γ t u :
  Σ ;;; Γ |- t <= u <~> { v & { v' & (red Σ Γ t v * red Σ Γ u v' * 
  leq_term Σ (global_ext_constraints Σ) v v')%type } }.
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
    ** econstructor 3; eauto.
    * econstructor 2; eauto.
Qed.

Instance cumul_refl' {cf:checker_flags} Σ Γ : Reflexive (cumul Σ Γ).
Proof.
  intro; constructor. reflexivity.
Qed.

Instance conv_refl' {cf:checker_flags} Σ Γ : Reflexive (conv Σ Γ).
Proof.
  intro; constructor. reflexivity.
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
  econstructor 2; eauto.
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
  econstructor 2; eauto.
Qed.

Lemma red_conv_conv_inv `{cf : checker_flags} Σ Γ t u v :
  red (fst Σ) Γ t u -> Σ ;;; Γ |- v = u -> Σ ;;; Γ |- v = t.
Proof.
  intros X%clos_rt_rt1n_iff.
  induction X; auto.
  now econstructor 3; [eapply IHX|]; eauto.
Qed.

Instance conv_sym `{cf : checker_flags} (Σ : global_env_ext) Γ :
  Symmetric (conv Σ Γ).
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
    destruct a as [na [b|] ty]; constructor; auto; pcuic.
  Qed.

  Global Instance cumul_ctx_refl : Reflexive (All2_fold (cumul_decls Σ)).
  Proof.
    intro Γ; induction Γ; try econstructor; auto.
    destruct a as [na [b|] ty]; econstructor; eauto; pcuic; eapply cumul_refl'.
  Qed.

  Definition conv_ctx_refl' Γ : conv_context Γ Γ
  := conv_ctx_refl Γ.

  Definition cumul_ctx_refl' Γ : cumul_context Γ Γ
    := cumul_ctx_refl Γ.

End ContextConversion.