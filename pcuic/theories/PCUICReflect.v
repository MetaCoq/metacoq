From Coq Require Import Ascii String Bool OrderedType Lia List Program Arith.
From MetaCoq.Template Require Import utils AstUtils.
From MetaCoq.Template Require Import BasicAst.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction.
Import List.ListNotations.
Require Import ssreflect.

From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.

Set Asymmetric Patterns.

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

(* Some reflection / EqDec lemmata *)

Class ReflectEq A := {
  eqb : A -> A -> bool ;
  eqb_spec : forall x y : A, reflect (x = y) (eqb x y)
}.

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

Instance reflect_option : forall {A}, ReflectEq A -> ReflectEq (option A) := {
  eqb := eq_option
}.
Proof.
  intros x y. destruct x, y.
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

Instance reflect_list : forall {A}, ReflectEq A -> ReflectEq (list A) := {
  eqb := eq_list eqb
}.
Proof.
  intro x. induction x ; intro y ; destruct y.
  - cbn. constructor. reflexivity.
  - cbn. constructor. discriminate.
  - cbn. constructor. discriminate.
  - cbn. destruct (eqb_spec a a0) ; nodec.
    destruct (IHx y) ; nodec.
    subst. constructor. reflexivity.
Defined.

Instance reflect_string : ReflectEq string := {
  eqb := eq_string
}.
Proof.
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

Instance reflect_level : ReflectEq Level.t := {
  eqb := eq_level
}.
Proof.
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

Instance reflect_prod : forall {A B}, ReflectEq A -> ReflectEq B -> ReflectEq (A * B) := {
  eqb := eq_prod eqb eqb
}.
Proof.
  intros [x y] [u v].
  unfold eq_prod.
  destruct (eqb_spec x u) ; nodec.
  destruct (eqb_spec y v) ; nodec.
  subst. constructor. reflexivity.
Defined.

Definition eq_bool b1 b2 : bool :=
  if b1 then b2 else negb b2.

Instance reflect_bool : ReflectEq bool := {
  eqb := eq_bool
}.
Proof.
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

Instance reflect_name : ReflectEq name := {
  eqb := eq_name
}.
Proof.
  intros x y. destruct x, y.
  - cbn. constructor. reflexivity.
  - cbn. constructor. discriminate.
  - cbn. constructor. discriminate.
  - unfold eq_name. destruct (eqb_spec i i0); nodec.
    constructor. f_equal. assumption.
Defined.

Definition eq_inductive ind ind' :=
  match ind, ind' with
  | mkInd m n, mkInd m' n' =>
    eqb m m' && eqb n n'
  end.

Instance reflect_inductive : ReflectEq inductive := {
  eqb := eq_inductive
}.
Proof.
  intros i i'. destruct i as [m n], i' as [m' n'].
  unfold eq_inductive.
  destruct (eqb_spec m m') ; nodec.
  destruct (eqb_spec n n') ; nodec.
  cbn. constructor. subst. reflexivity.
Defined.

Lemma eq_inductive_refl i : eq_inductive i i.
Proof.
  destruct i as [mind k].
  unfold eq_inductive, eqb; cbn. now rewrite eq_string_refl Nat.eqb_refl.
Defined.

Definition eq_def {A : Set} `{ReflectEq A} (d1 d2 : def A) : bool :=
  match d1, d2 with
  | mkdef n1 t1 b1 a1, mkdef n2 t2 b2 a2 =>
    eqb n1 n2 && eqb t1 t2 && eqb b1 b2 && eqb a1 a2
  end.

Instance reflect_def : forall {A : Set} `{ReflectEq A}, ReflectEq (def A) := {
  eqb := eq_def
}.
Proof.
  intros x y. destruct x as [n1 t1 b1 a1], y as [n2 t2 b2 a2].
  unfold eq_def.
  destruct (eqb_spec n1 n2) ; nodec.
  destruct (eqb_spec t1 t2) ; nodec.
  destruct (eqb_spec b1 b2) ; nodec.
  destruct (eqb_spec a1 a2) ; nodec.
  cbn. constructor. subst. reflexivity.
Defined.

Fixpoint eq_non_empty_list {A : Set} (eqA : A -> A -> bool) (l l' : non_empty_list A) : bool :=
  match l, l' with
  | NEL.sing a, NEL.sing a' => eqA a a'
  | NEL.cons a l, NEL.cons a' l' => 
    eqA a a' && eq_non_empty_list eqA l l'
  | _, _ => false
  end.

Instance reflect_non_empty_list :
  forall {A : Set} `{ReflectEq A}, ReflectEq (non_empty_list A) :=
  { eqb := eq_non_empty_list eqb }.
Proof.
  induction x, y; cbn.
  destruct (eqb_spec a a0); constructor; congruence.
  constructor; congruence.
  constructor; congruence.
  destruct (eqb_spec a a0), (IHx y); constructor; congruence.
Defined.

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
         | u : universe, u' : universe |- _ => fcase (eq_dec u u')
         | x : universe_instance, y : universe_instance |- _ =>
           fcase (eq_dec x y)
         | x : list Level.t, y : universe_instance |- _ =>
           fcase (eq_dec x y)
         | n : nat, m : nat |- _ => fcase (Nat.eq_dec n m)
         | i : ident, i' : ident |- _ => fcase (string_dec i i')
         | i : kername, i' : kername |- _ => fcase (string_dec i i')
         | i : string, i' : kername |- _ => fcase (string_dec i i')
         | n : name, n' : name |- _ => fcase (eq_dec n n')
         | i : inductive, i' : inductive |- _ => fcase (eq_dec i i')
         | x : inductive * nat, y : inductive * nat |- _ =>
           fcase (eq_dec x y)
         | x : projection, y : projection |- _ => fcase (eq_dec x y)
         end.

Derive NoConfusion NoConfusionHom for term.

Derive EqDec for term.
Next Obligation.
  revert y.
  induction x using term_forall_list_rec ; intro t ;
    destruct t ; try (right ; discriminate).
  all: term_dec_tac term_dec.
  - revert l0. induction H ; intro l0.
    + destruct l0.
      * left. reflexivity.
      * right. discriminate.
    + destruct l0.
      * right. discriminate.
      * destruct (IHForallT l0) ; nodec.
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

Instance reflect_sig_true {A f} `{ReflectEq A} : ReflectEq ({ z : A | f z = true }) := {
  eqb := eq_sig_true
}.
Proof.
  intros [x hx] [y hy]. simpl.
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
