From Coq Require Import Ascii String Bool OrderedType Lia List Program Arith.
Import ListNotations.
From Template Require Import utils.
From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.

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
Qed.

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
Qed.

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
Qed.

Instance option_dec : forall {A}, EqDec A -> EqDec (option A).
Proof.
  intros A h.
  pose (EqDec_ReflectEq A).
  exact _.
Qed.

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
Qed.

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
Qed.

Instance reflect_nat : ReflectEq nat := {
  eqb_spec := Nat.eqb_spec
}.

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
Qed.

Definition eq_bool (b1 b2 : bool) : bool :=
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
Qed.