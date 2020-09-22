(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICInduction.

Require Import ssreflect.
From Equations Require Import Equations.

Open Scope pcuic.

(** Notion of reflection for Type-based properties *)

Inductive reflectT (A : Type) : bool -> Type :=
| ReflectT : A -> reflectT A true
| ReflectF : (A -> False) -> reflectT A false.

Lemma reflectT_reflect (A : Prop) b : reflectT A b -> reflect A b.
Proof.
  destruct 1; now constructor.
Qed.

Lemma reflect_reflectT (A : Prop) b : reflect A b -> reflectT A b.
Proof.
  destruct 1; now constructor.
Qed.

Lemma equiv_reflectT P (b : bool) : (P -> b) -> (b -> P) -> reflectT P b.
Proof.
  intros. destruct b; constructor; auto. intro. now discriminate H.
Qed.

Lemma reflectT_subrelation {A} {R} {r : A -> A -> bool} : (forall x y, reflectT (R x y) (r x y)) -> CRelationClasses.subrelation R r.
Proof.
  intros. intros x y h. destruct (X x y); auto.
Qed.

Lemma reflectT_subrelation' {A} {R} {r : A -> A -> bool} : (forall x y, reflectT (R x y) (r x y)) -> CRelationClasses.subrelation r R.
Proof.
  intros. intros x y h. destruct (X x y); auto. discriminate.
Qed.

(* Some reflection / EqDec lemmata *)

Class ReflectEq A := {
  eqb : A -> A -> bool ;
  eqb_spec : forall x y : A, reflect (x = y) (eqb x y)
}.

Lemma eqb_eq {A} `{PCUICReflect.ReflectEq A} (x y : A) : PCUICReflect.eqb x y -> x = y.
Proof.
  elim: PCUICReflect.eqb_spec; auto.
  discriminate.
Qed.

Instance ReflectEq_EqDec :
  forall A, ReflectEq A -> EqDec A.
Proof.
  intros A [eqb h] x y.
  destruct (h x y).
  - left. assumption.
  - right. assumption.
Defined.

Definition eq_dec_to_bool {A} `{EqDec A} x y :=
  match eq_dec x y with
  | left _ => true
  | right _ => false
  end.

(* Not an instance to avoid loops? *)
Lemma EqDec_ReflectEq : forall A `{EqDec A}, ReflectEq A.
Proof.
  intros A h.
  unshelve econstructor.
  - eapply eq_dec_to_bool.
  - unfold eq_dec_to_bool.
    intros x y. destruct (eq_dec x y).
    all: constructor ; assumption.
Defined.

Ltac nodec :=
  let bot := fresh "bot" in
  try solve [ constructor ; intro bot ; inversion bot ; subst ; tauto ].

Definition eq_option {A} `{ReflectEq A} (u v : option A) : bool :=
  match u, v with
  | Some u, Some v => eqb u v
  | None, None => true
  | _, _ => false
  end.

#[program] Instance reflect_option : forall {A}, ReflectEq A -> ReflectEq (option A) := {
  eqb := eq_option
}.
Next Obligation.
  destruct x, y.
  all: cbn.
  all: try solve [ constructor ; easy ].
  destruct (eqb_spec a a0) ; nodec.
  constructor. f_equal. assumption.
Defined.

Fixpoint eq_list {A} (eqA : A -> A -> bool) (l l' : list A) : bool :=
  match l, l' with
  | a :: l, a' :: l' =>
    if eqA a a' then eq_list eqA l l'
    else false
  | [], [] => true
  | _, _ => false
  end.

#[program] Instance reflect_list : forall {A}, ReflectEq A -> ReflectEq (list A) := {
  eqb := eq_list eqb
}.
Next Obligation.
  revert y; induction x ; intro y ; destruct y.
  - cbn. constructor. reflexivity.
  - cbn. constructor. discriminate.
  - cbn. constructor. discriminate.
  - cbn. destruct (eqb_spec a a0) ; nodec.
    destruct (IHx y) ; nodec.
    subst. constructor. reflexivity.
Defined.

Local Obligation Tactic := idtac.

#[program] Instance reflect_string : ReflectEq string := {
  eqb := eq_string
}.
Next Obligation.
  intros s s'. destruct (string_dec s s').
  - subst. rewrite eq_string_refl. constructor. reflexivity.
  - assert (string_compare s s' <> Eq).
    { intro bot. apply n. apply string_compare_eq. assumption. }
    unfold eq_string. destruct (string_compare s s').
    + tauto.
    + constructor. assumption.
    + constructor. assumption.
Defined.

Instance reflect_nat : ReflectEq nat := {
  eqb_spec := Nat.eqb_spec
}.

Definition eq_level l1 l2 :=
  match l1, l2 with
  | Level.lProp, Level.lProp => true
  | Level.lSet, Level.lSet => true
  | Level.Level s1, Level.Level s2 => eqb s1 s2
  | Level.Var n1, Level.Var n2 => eqb n1 n2
  | _, _ => false
  end.

#[program] Instance reflect_level : ReflectEq Level.t := {
  eqb := eq_level
}.
Next Obligation.
  intros x y. destruct x, y.
  all: unfold eq_level.
  all: try solve [ constructor ; reflexivity ].
  all: try solve [ constructor ; discriminate ].
  - destruct (eqb_spec s s0) ; nodec.
    constructor. f_equal. assumption.
  - destruct (eqb_spec n n0) ; nodec.
    constructor. subst. reflexivity.
Defined.

Definition eq_prod {A B} (eqA : A -> A -> bool) (eqB : B -> B -> bool) x y :=
  let '(a1, b1) := x in
  let '(a2, b2) := y in
  if eqA a1 a2 then eqB b1 b2
  else false.

#[program] Instance reflect_prod : forall {A B}, ReflectEq A -> ReflectEq B -> ReflectEq (A * B) := {
  eqb := eq_prod eqb eqb
}.
Next Obligation.
  intros A B RA RB [x y] [u v].
  unfold eq_prod.
  destruct (eqb_spec x u) ; nodec.
  destruct (eqb_spec y v) ; nodec.
  subst. constructor. reflexivity.
Defined.

Lemma eq_prod_refl :
  forall A B (eqA : A -> A -> bool) (eqB : B -> B -> bool),
    (forall a, eqA a a) ->
    (forall b, eqB b b) ->
    forall p, eq_prod eqA eqB p p.
Proof.
  intros A B eqA eqB eqA_refl eqB_refl [a b].
  simpl. rewrite eqA_refl. apply eqB_refl.
Qed.

Definition eq_bool b1 b2 : bool :=
  if b1 then b2 else negb b2.

#[program] Instance reflect_bool : ReflectEq bool := {
  eqb := eq_bool
}.
Next Obligation.
  intros x y. unfold eq_bool.
  destruct x, y.
  all: constructor.
  all: try reflexivity.
  all: discriminate.
Defined.

Definition eq_name na nb :=
  match na, nb with
  | nAnon, nAnon => true
  | nNamed a, nNamed b => eqb a b
  | _, _ => false
  end.

#[program] Instance reflect_name : ReflectEq name := {
  eqb := eq_name
}.
Next Obligation.
  intros x y. destruct x, y.
  - cbn. constructor. reflexivity.
  - cbn. constructor. discriminate.
  - cbn. constructor. discriminate.
  - unfold eq_name. destruct (eqb_spec i i0); nodec.
    constructor. f_equal. assumption.
Defined.


#[program] Instance reflect_kername : ReflectEq kername := {
  eqb := eq_kername
}.
Next Obligation.
  intros; unfold eq_kername; destruct kername_eq_dec; now constructor.
Qed.


#[program] Instance reflect_inductive : ReflectEq inductive := {
  eqb := eq_inductive
}.
Next Obligation.
  intros i i'. destruct i as [m n], i' as [m' n']; cbn.
  change (eq_kername m m') with (eqb m m').
  change (n =? n') with (eqb n n').
  destruct (eqb_spec m m') ; nodec.
  destruct (eqb_spec n n') ; nodec.
  cbn. constructor. subst. reflexivity.
Defined.

Definition eq_def {A : Set} `{ReflectEq A} (d1 d2 : def A) : bool :=
  match d1, d2 with
  | mkdef n1 t1 b1 a1, mkdef n2 t2 b2 a2 =>
    eqb n1 n2 && eqb t1 t2 && eqb b1 b2 && eqb a1 a2
  end.

#[program] Instance reflect_def : forall {A : Set} `{ReflectEq A}, ReflectEq (def A) := {
  eqb := eq_def
}.
Next Obligation.
  intros A RA x y. destruct x as [n1 t1 b1 a1], y as [n2 t2 b2 a2].
  unfold eq_def.
  destruct (eqb_spec n1 n2) ; nodec.
  destruct (eqb_spec t1 t2) ; nodec.
  destruct (eqb_spec b1 b2) ; nodec.
  destruct (eqb_spec a1 a2) ; nodec.
  cbn. constructor. subst. reflexivity.
Defined.

(* TODO: move *)
Lemma eq_universe_iff (u v : Universe.t) :
  u = v <-> u = v :> UnivExprSet.t.
Proof.
  destruct u, v; cbn; split. now inversion 1.
  intros ->. f_equal. apply uip.
Qed.
Lemma eq_universe_iff' (u v : Universe.t) :
  u = v <-> UnivExprSet.elements u = UnivExprSet.elements v.
Proof.
  etransitivity. apply eq_universe_iff.
  destruct u as [[u1 u2] ?], v as [[v1 v2] ?]; cbn; clear; split.
  now inversion 1. intros ->. f_equal. apply uip.
Qed.

(* move in Universes.v ?? *)
Instance eq_dec_UnivExpr : EqDec UnivExpr.t.
Proof. intros e e'. repeat decide equality. Qed.

Instance eq_dec_univ : EqDec Universe.t.
Proof.
  intros u v.
  assert (H : {UnivExprSet.elements u = UnivExprSet.elements v}
              + {~ UnivExprSet.elements u = UnivExprSet.elements v}). {
    repeat decide equality. }
  destruct H as [H|H]; [left; now apply eq_universe_iff' in H|right].
  intro X; apply H; now apply eq_universe_iff' in X.
Qed.

Local Ltac finish :=
  let h := fresh "h" in
  right ;
  match goal with
  | e : ?t <> ?u |- _ =>
    intro h ; apply e ; now inversion h
  end.

Local Ltac fcase c :=
  let e := fresh "e" in
  case c ; intro e ; [ subst ; try (left ; reflexivity) | finish ].

Local Ltac term_dec_tac term_dec :=
  repeat match goal with
         | t : term, u : term |- _ => fcase (term_dec t u)
         | u : Universe.t, u' : Universe.t |- _ => fcase (eq_dec u u')
         | x : Instance.t, y : Instance.t |- _ =>
           fcase (eq_dec x y)
         | x : list Level.t, y : Instance.t |- _ =>
           fcase (eq_dec x y)
         | n : nat, m : nat |- _ => fcase (Nat.eq_dec n m)
         | i : ident, i' : ident |- _ => fcase (string_dec i i')
         | i : kername, i' : kername |- _ => fcase (kername_eq_dec i i')
         | i : string, i' : kername |- _ => fcase (string_dec i i')
         | n : name, n' : name |- _ => fcase (eq_dec n n')
         | i : inductive, i' : inductive |- _ => fcase (eq_dec i i')
         | x : inductive * nat, y : inductive * nat |- _ =>
           fcase (eq_dec x y)
         | x : projection, y : projection |- _ => fcase (eq_dec x y)
         end.

Derive NoConfusion NoConfusionHom for term.

Instance EqDec_term : EqDec term.
Proof.
  intro x; induction x using term_forall_list_ind ; intro t ;
    destruct t ; try (right ; discriminate).
  all: term_dec_tac term_dec.
  - revert l0. rename X into H; induction H ; intro l0.
    + destruct l0.
      * left. reflexivity.
      * right. discriminate.
    + destruct l0.
      * right. discriminate.
      * destruct (IHAll l0) ; nodec.
        destruct (p t) ; nodec.
        subst. left. inversion e. reflexivity.
  - destruct (IHx1 t1) ; nodec.
    destruct (IHx2 t2) ; nodec.
    subst. left. reflexivity.
  - destruct (IHx1 t1) ; nodec.
    destruct (IHx2 t2) ; nodec.
    subst. left. reflexivity.
  - destruct (IHx1 t1) ; nodec.
    destruct (IHx2 t2) ; nodec.
    destruct (IHx3 t3) ; nodec.
    subst. left. reflexivity.
  - destruct (IHx1 t1) ; nodec.
    destruct (IHx2 t2) ; nodec.
    subst. left. reflexivity.
  - destruct (IHx1 t1) ; nodec.
    destruct (IHx2 t2) ; nodec.
    subst. revert brs. clear IHx1 IHx2.
    induction X ; intro l0.
    + destruct l0.
      * left. reflexivity.
      * right. discriminate.
    + destruct l0.
      * right. discriminate.
      * destruct (IHX l0) ; nodec.
        destruct (p (snd p0)) ; nodec.
        destruct (eq_dec (fst x) (fst p0)) ; nodec.
        destruct x, p0.
        left.
        cbn in *. subst. inversion e. reflexivity.
  - destruct (IHx t) ; nodec.
    left. subst. reflexivity.
  - revert mfix. induction X ; intro m0.
    + destruct m0.
      * left. reflexivity.
      * right. discriminate.
    + destruct p as [p1 p2].
      destruct m0.
      * right. discriminate.
      * destruct (p1 (dtype d)) ; nodec.
        destruct (p2 (dbody d)) ; nodec.
        destruct (IHX m0) ; nodec.
        destruct x, d ; subst. cbn in *.
        destruct (eq_dec dname dname0) ; nodec.
        subst. inversion e1. subst.
        destruct (eq_dec rarg rarg0) ; nodec.
        subst. left. reflexivity.
  - revert mfix. induction X ; intro m0.
    + destruct m0.
      * left. reflexivity.
      * right. discriminate.
    + destruct p as [p1 p2].
      destruct m0.
      * right. discriminate.
      * destruct (p1 (dtype d)) ; nodec.
        destruct (p2 (dbody d)) ; nodec.
        destruct (IHX m0) ; nodec.
        destruct x, d ; subst. cbn in *.
        destruct (eq_dec dname dname0) ; nodec.
        subst. inversion e1. subst.
        destruct (eq_dec rarg rarg0) ; nodec.
        subst. left. reflexivity.
Defined.

Instance reflect_term : ReflectEq term :=
  let h := EqDec_ReflectEq term in _.

Definition eq_sig_true {A f} `{ReflectEq A} (x y : { z : A | f z = true }) : bool :=
  let '(exist x hx) := x in
  let '(exist y hy) := y in
  eqb x y.

#[program] Instance reflect_sig_true {A f} `{ReflectEq A} : ReflectEq ({ z : A | f z = true }) := {
  eqb := eq_sig_true
}.
Next Obligation.
  intros A F RA [x hx] [y hy]. simpl.
  destruct (eqb_spec x y) ; nodec. subst.
  constructor. pose proof (uip hx hy). subst. reflexivity.
Defined.

Derive NoConfusion NoConfusionHom for sig.
Derive NoConfusion NoConfusionHom for prod.

Definition eqb_context_decl (x y : context_decl) :=
  let (na, b, ty) := x in
  let (na', b', ty') := y in
  eqb na na' && eqb b b' && eqb ty ty'.

Instance eq_ctx : ReflectEq context_decl.
Proof.
  refine {| eqb := eqb_context_decl |}.
  intros.
  destruct x as [na b ty], y as [na' b' ty']. cbn -[eqb].
  destruct (eqb_spec na na'); subst;
    destruct (eqb_spec b b'); subst;
      destruct (eqb_spec ty ty'); subst; constructor; congruence.
Qed.

Instance eqb_ctx : ReflectEq context := _.

Definition eqb_recursivity_kind r r' :=
  match r, r' with
  | Finite, Finite => true
  | CoFinite, CoFinite => true
  | BiFinite, BiFinite => true
  | _, _ => false
  end.

Instance reflect_recursivity_kind : ReflectEq recursivity_kind.
Proof.
  refine {| eqb := eqb_recursivity_kind |}.
  destruct x, y; simpl; constructor; congruence.
Defined.
