(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia.

From MetaCoq.Template Require Import config utils Ast AstUtils Induction LiftSubst UnivSubst EnvironmentTyping.
From MetaCoq.Checker Require Import LibHypsNaming Reflect Reduction.

From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.
Require Import ssreflect.

(* Type-valued relations. *)
Require Import CRelationClasses.

Local Open Scope string_scope.
Set Asymmetric Patterns.

(** ** Term equality and cumulativity *)

(* ** Syntactic equality up-to universes

  We shouldn't look at printing annotations nor casts.
  It is however not possible to write a structurally recursive definition
  for syntactic equality up-to casts due to the [tApp (tCast f _ _) args] case.
  We hence implement first an equality which considers casts and do a stripping
  phase of casts before checking equality. *)


Inductive eq_term_upto_univ (Re Rle : universe -> universe -> Prop) : term -> term -> Prop :=
| eq_Rel n  :
    eq_term_upto_univ Re Rle (tRel n) (tRel n)

| eq_Evar e args args' :
    Forall2 (eq_term_upto_univ Re Re) args args' ->
    eq_term_upto_univ Re Rle (tEvar e args) (tEvar e args')

| eq_Var id :
    eq_term_upto_univ Re Rle (tVar id) (tVar id)

| eq_Sort s s' :
    Rle s s' ->
    eq_term_upto_univ Re Rle (tSort s) (tSort s')

| eq_Cast f f' k T T' :
    eq_term_upto_univ Re Re f f' ->
    eq_term_upto_univ Re Re T T' ->
    eq_term_upto_univ Re Rle (tCast f k T) (tCast f' k T')

| eq_App t t' args args' :
    eq_term_upto_univ Re Rle t t' ->
    Forall2 (eq_term_upto_univ Re Re) args args' ->
    eq_term_upto_univ Re Rle (tApp t args) (tApp t' args')

| eq_Const c u u' :
    Forall2 Rle (List.map Universe.make u) (List.map Universe.make u') ->
    eq_term_upto_univ Re Rle (tConst c u) (tConst c u')

| eq_Ind i u u' :
    Forall2 Rle (List.map Universe.make u) (List.map Universe.make u') ->
    eq_term_upto_univ Re Rle (tInd i u) (tInd i u')

| eq_Construct i k u u' :
    Forall2 Rle (List.map Universe.make u) (List.map Universe.make u') ->
    eq_term_upto_univ Re Rle (tConstruct i k u) (tConstruct i k u')

| eq_Lambda na na' ty ty' t t' :
    eq_term_upto_univ Re Re ty ty' ->
    eq_term_upto_univ Re Rle t t' ->
    eq_term_upto_univ Re Rle (tLambda na ty t) (tLambda na' ty' t')

| eq_Prod na na' a a' b b' :
    eq_term_upto_univ Re Re a a' ->
    eq_term_upto_univ Re Rle b b' ->
    eq_term_upto_univ Re Rle (tProd na a b) (tProd na' a' b')

| eq_LetIn na na' ty ty' t t' u u' :
    eq_term_upto_univ Re Re ty ty' ->
    eq_term_upto_univ Re Re t t' ->
    eq_term_upto_univ Re Rle u u' ->
    eq_term_upto_univ Re Rle (tLetIn na ty t u) (tLetIn na' ty' t' u')

| eq_Case ind par p p' c c' brs brs' :
    eq_term_upto_univ Re Re p p' ->
    eq_term_upto_univ Re Re c c' ->
    Forall2 (fun x y =>
      fst x = fst y /\
      eq_term_upto_univ Re Re (snd x) (snd y)
    ) brs brs' ->
    eq_term_upto_univ Re Rle (tCase (ind, par) p c brs) (tCase (ind, par) p' c' brs')

| eq_Proj p c c' :
    eq_term_upto_univ Re Re c c' ->
    eq_term_upto_univ Re Rle (tProj p c) (tProj p c')

| eq_Fix mfix mfix' idx :
    Forall2 (fun x y =>
      eq_term_upto_univ Re Re x.(dtype) y.(dtype) /\
      eq_term_upto_univ Re Re x.(dbody) y.(dbody) /\
      x.(rarg) = y.(rarg)
    ) mfix mfix' ->
    eq_term_upto_univ Re Rle (tFix mfix idx) (tFix mfix' idx)

| eq_CoFix mfix mfix' idx :
    Forall2 (fun x y =>
      eq_term_upto_univ Re Re x.(dtype) y.(dtype) /\
      eq_term_upto_univ Re Re x.(dbody) y.(dbody) /\
      x.(rarg) = y.(rarg)
    ) mfix mfix' ->
    eq_term_upto_univ Re Rle (tCoFix mfix idx) (tCoFix mfix' idx).

Definition eq_term `{checker_flags} φ :=
  eq_term_upto_univ (eq_universe φ) (eq_universe φ).

(* ** Syntactic cumulativity up-to universes

  We shouldn't look at printing annotations *)

Definition leq_term `{checker_flags} φ :=
  eq_term_upto_univ (eq_universe φ) (leq_universe φ).

Fixpoint strip_casts t :=
  match t with
  | tEvar ev args => tEvar ev (List.map strip_casts args)
  | tLambda na T M => tLambda na (strip_casts T) (strip_casts M)
  | tApp u v => mkApps (strip_casts u) (List.map (strip_casts) v)
  | tProd na A B => tProd na (strip_casts A) (strip_casts B)
  | tCast c kind t => strip_casts c
  | tLetIn na b t b' => tLetIn na (strip_casts b) (strip_casts t) (strip_casts b')
  | tCase ind p c brs =>
    let brs' := List.map (on_snd (strip_casts)) brs in
    tCase ind (strip_casts p) (strip_casts c) brs'
  | tProj p c => tProj p (strip_casts c)
  | tFix mfix idx =>
    let mfix' := List.map (map_def strip_casts strip_casts) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let mfix' := List.map (map_def strip_casts strip_casts) mfix in
    tCoFix mfix' idx
  | tRel _ | tVar _ | tSort _ | tConst _ _ | tInd _ _ | tConstruct _ _ _ => t
  end.

Definition eq_term_nocast `{checker_flags} (φ : constraints) (t u : term) :=
  eq_term φ (strip_casts t) (strip_casts u).

Definition leq_term_nocast `{checker_flags} (φ : constraints) (t u : term) :=
  leq_term φ (strip_casts t) (strip_casts u).

(** ** Cumulativity and Conversion ** *)

Reserved Notation " Σ ;;; Γ |- t <= u " (at level 50, Γ, t, u at next level).
Reserved Notation " Σ ;;; Γ |- t = u " (at level 50, Γ, t, u at next level).

Inductive cumul `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
| cumul_refl t u : leq_term (global_ext_constraints Σ) t u -> Σ ;;; Γ |- t <= u
| cumul_red_l t u v : red1 Σ.1 Γ t v -> Σ ;;; Γ |- v <= u -> Σ ;;; Γ |- t <= u
| cumul_red_r t u v : Σ ;;; Γ |- t <= v -> red1 Σ.1 Γ u v -> Σ ;;; Γ |- t <= u
where " Σ ;;; Γ |- t <= u " := (cumul Σ Γ t u) : type_scope.


Inductive conv `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
| conv_refl t u : eq_term (global_ext_constraints Σ) t u -> Σ ;;; Γ |- t = u
| conv_red_l t u v : red1 Σ Γ t v -> Σ ;;; Γ |- v = u -> Σ ;;; Γ |- t = u
| conv_red_r t u v : Σ ;;; Γ |- t = v -> red1 (fst Σ) Γ u v -> Σ ;;; Γ |- t = u
where " Σ ;;; Γ |- t = u " := (@conv _ Σ Γ t u) : type_scope.


Lemma cumul_alt {cf:checker_flags} Σ Γ t u :
  Σ ;;; Γ |- t <= u <~> ∑ v v', red Σ Γ t v × red Σ Γ u v' × leq_term Σ v v'.
Proof.
  split.
  { induction 1. exists t, u. intuition auto; constructor.
    destruct IHX as (v' & v'' & redv & redv' & leqv).
    exists v', v''. intuition auto. now eapply red_step.
    destruct IHX as (v' & v'' & redv & redv' & leqv).
    exists v', v''. intuition auto. now eapply red_step. }
  { intros [v [v' [redv [redv' Hleq]]]]. apply red_alt in redv.
    apply red_alt in redv'.
    apply clos_rt_rt1n in redv.
    apply clos_rt_rt1n in redv'.
    induction redv. induction redv'. constructor; auto.
    econstructor 3; eauto.
    econstructor 2; eauto. }
Qed.


Lemma conv_alt {cf:checker_flags} Σ Γ t u :
  Σ ;;; Γ |- t = u <~> ∑ v v', red Σ Γ t v × red Σ Γ u v' × eq_term Σ v v'.
Proof.
  split.
  { induction 1. exists t, u. intuition auto; constructor.
    destruct IHX as (v' & v'' & redv & redv' & leqv).
    exists v', v''. intuition auto. now eapply red_step.
    destruct IHX as (v' & v'' & redv & redv' & leqv).
    exists v', v''. intuition auto. now eapply red_step. }
  { intros [v [v' [redv [redv' Hleq]]]]. apply red_alt in redv.
    apply red_alt in redv'.
    apply clos_rt_rt1n in redv.
    apply clos_rt_rt1n in redv'.
    induction redv. induction redv'. constructor; auto.
    econstructor 3; eauto.
    econstructor 2; eauto. }
Qed.




(** ** Context conversion ** *)

Inductive context_relation
          (P : context -> context -> context_decl -> context_decl -> Type)
          : forall (Γ Γ' : context), Type :=
| ctx_rel_nil : context_relation P nil nil
| ctx_rel_vass na na' T U Γ Γ' :
    context_relation P Γ Γ' ->
    P Γ Γ' (vass na T) (vass na' U) ->
    context_relation P (vass na T :: Γ) (vass na' U :: Γ')
| ctx_rel_def na na' t T u U Γ Γ' :
    context_relation P Γ Γ' ->
    P Γ Γ' (vdef na t T) (vdef na' u U) ->
    context_relation P (vdef na t T :: Γ) (vdef na' u U :: Γ').
Derive Signature for context_relation.
Arguments context_relation P Γ Γ' : clear implicits.

Section ConvContext.

  Context {cf:checker_flags} (Σ : global_env_ext).

  Inductive conv_decls (Γ Γ' : context) : forall (x y : context_decl), Type :=
  | conv_vass na na' T T' :
      (* isType Σ Γ' T' -> *)
      Σ ;;; Γ |- T = T' ->
      conv_decls Γ Γ' (vass na T) (vass na' T')

  | conv_vdef_type na na' b T T' :
      (* isType Σ Γ' T' -> *)
      Σ ;;; Γ |- T = T' ->
      conv_decls Γ Γ' (vdef na b T) (vdef na' b T')

  | conv_vdef_body na na' b b' T T' :
      (* isType Σ Γ' T' -> *)
      (* Σ ;;; Γ' |- b' : T' -> *)
      Σ ;;; Γ |- b = b' ->
      Σ ;;; Γ |- T = T' ->
      conv_decls Γ Γ' (vdef na b T) (vdef na' b' T').

End ConvContext.

Notation conv_context Σ Γ Γ' := (context_relation (conv_decls Σ) Γ Γ').
