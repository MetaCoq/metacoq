(* Distributed under the terms of the MIT license. *)
(* For primitive integers and floats  *)
From Coq Require Numbers.Cyclic.Int63.Int63 Floats.PrimFloat Floats.FloatAxioms.
From MetaCoq.Template Require Import utils BasicAst Universes.
Require Import ssreflect.
From Equations Require Import Equations.

(* Some reflection / EqDec lemmata *)

Class ReflectEq A := {
  eqb : A -> A -> bool ;
  eqb_spec : forall x y : A, reflect (x = y) (eqb x y)
}.

Lemma eqb_eq {A} `{ReflectEq A} (x y : A) : eqb x y -> x = y.
Proof.
  elim: eqb_spec; auto.
  discriminate.
Qed.

#[global] Instance ReflectEq_EqDec :
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

#[global] (* Not an instance to avoid loops? *)
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

Definition eq_option {A} (eqA : A -> A -> bool) (u v : option A) : bool :=
  match u, v with
  | Some u, Some v => eqA u v
  | None, None => true
  | _, _ => false
  end.

#[global] Instance reflect_option : forall {A}, ReflectEq A -> ReflectEq (option A).
Proof.
  intros A RA. refine {| eqb := eq_option eqb |}.
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

#[global] Instance reflect_list : forall {A}, ReflectEq A -> ReflectEq (list A).
Proof.
  intros A RA. refine {| eqb := eq_list eqb |}.
  intro x. induction x ; intro y ; destruct y.
  - cbn. constructor. reflexivity.
  - cbn. constructor. discriminate.
  - cbn. constructor. discriminate.
  - cbn. destruct (eqb_spec a a0) ; nodec.
    destruct (IHx y) ; nodec.
    subst. constructor. reflexivity.
Defined.

#[global] Program Instance reflect_string : ReflectEq string := {
  eqb := eq_string
}.
Next Obligation.
  rename x into s, y into s'.
  destruct (string_dec s s').
  - subst. rewrite eq_string_refl. constructor. reflexivity.
  - assert (string_compare s s' <> Eq).
    { intro bot. apply n. apply string_compare_eq. assumption. }
    unfold eq_string. destruct (string_compare s s').
    + tauto.
    + constructor. assumption.
    + constructor. assumption.
Defined.

#[global] Instance reflect_nat : ReflectEq nat := {
  eqb_spec := Nat.eqb_spec
}.

#[program,global] Instance reflect_prim_int : ReflectEq Numbers.Cyclic.Int63.Int63.int :=
  { eqb := Numbers.Cyclic.Int63.Int63.eqb }.
Next Obligation.
  destruct (Int63.eqb x y) eqn:eq; constructor.
  now apply (Numbers.Cyclic.Int63.Int63.eqb_spec x y) in eq.
  now apply (Numbers.Cyclic.Int63.Int63.eqb_false_spec x y) in eq.
Qed.
 
Derive NoConfusion EqDec for SpecFloat.spec_float.

Local Obligation Tactic := idtac.

#[program,global] 
Instance reflect_prim_float : ReflectEq PrimFloat.float :=
  { eqb x y := eqb (ReflectEq := EqDec_ReflectEq SpecFloat.spec_float) (FloatOps.Prim2SF x) (FloatOps.Prim2SF y) }.
Next Obligation.
  intros. cbn -[eqb].
  destruct (eqb_spec (ReflectEq := EqDec_ReflectEq SpecFloat.spec_float) (FloatOps.Prim2SF x) (FloatOps.Prim2SF y)); constructor.
  now apply FloatAxioms.Prim2SF_inj.
  intros e; apply n. rewrite e.
  reflexivity.
Qed.

Definition eq_level l1 l2 :=
  match l1, l2 with
  | Level.lzero, Level.lzero => true
  | Level.Level s1, Level.Level s2 => eqb s1 s2
  | Level.Var n1, Level.Var n2 => eqb n1 n2
  | _, _ => false
  end.

#[global, program] Instance reflect_level : ReflectEq Level.t := {
  eqb := eq_level
}.
Next Obligation.
  destruct x, y.
  all: unfold eq_level.
  all: try solve [ constructor ; reflexivity ].
  all: try solve [ constructor ; discriminate ].
  - destruct (eqb_spec s s0) ; nodec.
    constructor. f_equal. assumption.
  - destruct (eqb_spec n n0) ; nodec.
    constructor. subst. reflexivity.
Defined.

Definition eq_prop_level l1 l2 :=
  match l1, l2 with
  | PropLevel.lProp, PropLevel.lProp => true
  | PropLevel.lSProp, PropLevel.lSProp => true
  | _, _ => false
  end.

#[global, program] Instance reflect_prop_level : ReflectEq PropLevel.t := {
  eqb := eq_prop_level
}.
Next Obligation.
  destruct x, y.
  all: unfold eq_prop_level.
  all: try solve [ constructor ; reflexivity ].
  all: try solve [ constructor ; discriminate ].
Defined.

Definition eq_levels (l1 l2 : PropLevel.t + Level.t) :=
  match l1, l2 with
  | inl l, inl l' => eqb l l'
  | inr l, inr l' => eqb l l'
  | _, _ => false
  end.

#[global, program] Instance reflect_levels : ReflectEq (PropLevel.t + Level.t) := {
  eqb := eq_levels
}.
Next Obligation.
  destruct x, y.
  cbn -[eqb]. destruct (eqb_spec t t0). subst. now constructor.
  all:try (constructor; cong).
  cbn -[eqb]. destruct (eqb_spec t t0). subst; now constructor.
  constructor; cong.
Defined.

Definition eq_prod {A B} (eqA : A -> A -> bool) (eqB : B -> B -> bool) x y :=
  let '(a1, b1) := x in
  let '(a2, b2) := y in
  if eqA a1 a2 then eqB b1 b2
  else false.

Local Obligation Tactic := idtac.
#[global, program] Instance reflect_prod : forall {A B}, ReflectEq A -> ReflectEq B -> ReflectEq (A * B) := {
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

#[global, program] Instance reflect_bool : ReflectEq bool := {
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

#[global, program] Instance reflect_name : ReflectEq name := {
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

Definition eq_relevance r r' :=
  match r, r' with
  | Relevant, Relevant => true
  | Irrelevant, Irrelevant => true
  | _, _ => false
  end.

#[global, program] Instance reflect_relevance : ReflectEq relevance := {
  eqb := eq_relevance
}.
Next Obligation.
  intros x y. destruct x, y.
  - cbn. constructor. reflexivity.
  - cbn. constructor. discriminate.
  - cbn. constructor. discriminate.
  - simpl. now constructor.
Defined.

Definition eq_aname (na nb : binder_annot name) :=
  eqb na.(binder_name) nb.(binder_name) &&
  eqb na.(binder_relevance) nb.(binder_relevance).
  
#[global, program] Instance reflect_aname : ReflectEq aname := {
  eqb := eq_aname
}.
Next Obligation.
  intros x y. unfold eq_aname.
  destruct (eqb_spec x.(binder_name) y.(binder_name));
  destruct (eqb_spec x.(binder_relevance) y.(binder_relevance));
  constructor; destruct x, y; simpl in *; cong.
Defined.

#[global, program] Instance reflect_kername : ReflectEq kername := {
  eqb := eq_kername
}.
Next Obligation.
  intros; unfold eq_kername; destruct kername_eq_dec; now constructor.
Qed.


#[global, program] Instance reflect_inductive : ReflectEq inductive := {
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

Definition eq_def {A} `{ReflectEq A} (d1 d2 : def A) : bool :=
  match d1, d2 with
  | mkdef n1 t1 b1 a1, mkdef n2 t2 b2 a2 =>
    eqb n1 n2 && eqb t1 t2 && eqb b1 b2 && eqb a1 a2
  end.

#[global, program] Instance reflect_def : forall {A} `{ReflectEq A}, ReflectEq (def A) := {
  eqb := eq_def
}.
Next Obligation.
  intros A RA.
  intros x y. destruct x as [n1 t1 b1 a1], y as [n2 t2 b2 a2].
  unfold eq_def.
  destruct (eqb_spec n1 n2) ; nodec.
  destruct (eqb_spec t1 t2) ; nodec.
  destruct (eqb_spec b1 b2) ; nodec.
  destruct (eqb_spec a1 a2) ; nodec.
  cbn. constructor. subst. reflexivity.
Defined.

Definition eq_cast_kind (c c' : cast_kind) : bool :=
  match c, c' with
  | VmCast, VmCast
  | NativeCast, NativeCast
  | Cast, Cast => true
  | RevertCast, RevertCast => true
  | _, _ => false
  end.

#[global, program] Instance reflect_cast_kind : ReflectEq cast_kind :=
  { eqb := eq_cast_kind }.
Next Obligation.
  induction x, y. all: cbn. all: nodec.
  all: left. all: reflexivity.
Defined.

(* TODO: move *)
Lemma eq_universe_iff (u v : Universe.nonEmptyUnivExprSet) :
  u = v <-> u = v :> UnivExprSet.t.
Proof.
  destruct u, v; cbn; split. now inversion 1.
  intros ->. f_equal. apply uip.
Qed.
Lemma eq_universe_iff' (u v : Universe.nonEmptyUnivExprSet) :
  u = v <-> UnivExprSet.elements u = UnivExprSet.elements v.
Proof.
  etransitivity. apply eq_universe_iff.
  destruct u as [[u1 u2] ?], v as [[v1 v2] ?]; cbn; clear; split.
  now inversion 1. intros ->. f_equal. apply uip.
Qed.

(* move in Universes.v ?? *)
#[global] Instance eq_dec_UnivExpr : EqDec UnivExpr.t.
Proof. intros e e'. repeat decide equality. Qed.

#[global] Instance eq_dec_univ0 : EqDec Universe.nonEmptyUnivExprSet.
Proof.
  intros u v.
  assert (H : {UnivExprSet.elements u = UnivExprSet.elements v}
              + {~ UnivExprSet.elements u = UnivExprSet.elements v}). {
    repeat decide equality. }
  destruct H as [H|H]; [left; now apply eq_universe_iff' in H|right].
  intro X; apply H; now apply eq_universe_iff' in X.
Defined.

#[global] Instance eq_dec_univ : EqDec Universe.t.
Proof.
  red. decide equality.
  apply eq_dec_univ0.
Defined.

#[global] Instance reflect_eq_univ : ReflectEq Universe.t := EqDec_ReflectEq _.

#[global] Instance reflect_case_info : ReflectEq case_info := EqDec_ReflectEq case_info.

Definition eq_sig_true {A f} `{ReflectEq A} (x y : { z : A | f z = true }) : bool :=
  let '(exist x hx) := x in
  let '(exist y hy) := y in
  eqb x y.

#[global, program] Instance reflect_sig_true {A f} `{ReflectEq A} : ReflectEq ({ z : A | f z = true }) := {
  eqb := eq_sig_true
}.
Next Obligation.
  intros A f RA. intros [x hx] [y hy]. simpl.
  destruct (eqb_spec x y) ; nodec. subst.
  constructor. pose proof (uip hx hy). subst. reflexivity.
Defined.

Derive NoConfusion NoConfusionHom for sig.
Derive NoConfusion NoConfusionHom for prod.

Definition eqb_context_decl {term : Type} (eqterm : term -> term -> bool) 
  (x y : BasicAst.context_decl term) :=
  let (na, b, ty) := x in
  let (na', b', ty') := y in
  eqb na na' && eq_option eqterm b b' && eqterm ty ty'.

#[global] Instance eq_decl_reflect {term} {Ht : ReflectEq term} : ReflectEq (BasicAst.context_decl term).
Proof.
  refine {| eqb := eqb_context_decl eqb |}.
  intros.
  destruct x as [na b ty], y as [na' b' ty']. cbn -[eqb].
  change (eq_option eqb b b') with (eqb b b').
  destruct (eqb_spec na na'); subst;
    destruct (eqb_spec b b'); subst;
      destruct (eqb_spec ty ty'); subst; constructor; congruence.
Qed.

Definition eqb_recursivity_kind r r' :=
  match r, r' with
  | Finite, Finite => true
  | CoFinite, CoFinite => true
  | BiFinite, BiFinite => true
  | _, _ => false
  end.

#[global] Instance reflect_recursivity_kind : ReflectEq recursivity_kind.
Proof.
  refine {| eqb := eqb_recursivity_kind |}.
  destruct x, y; simpl; constructor; congruence.
Defined.

Definition eqb_ConstraintType x y :=
  match x, y with
  | ConstraintType.Le n, ConstraintType.Le m => Z.eqb n m
  | ConstraintType.Eq, ConstraintType.Eq => true
  | _, _ => false
  end.

#[global] Instance reflect_ConstraintType : ReflectEq ConstraintType.t.
Proof.
  refine {| eqb := eqb_ConstraintType |}.
  destruct x, y; simpl; try constructor; try congruence.
  destruct (Z.eqb_spec z z0); constructor. now subst.
  cong.
Defined.
(* 
Definition eqb_ConstraintSet x y :=
  eqb (ConstraintSet.this x) (ConstraintSet.this y).

#[global] Instance reflect_ConstraintSet : ReflectEq ConstraintSet.t.
Proof.
  refine {| eqb := eqb_ConstraintSet |}.
  intros [thisx okx] [thisy oky].
  unfold eqb_ConstraintSet.
  cbn -[eqb].
  destruct (eqb_spec thisx thisy); subst; constructor.
  - f_equal; apply uip.
  - congruence.
Defined.
 *)
Definition eqb_LevelSet x y :=
  eqb (LevelSet.this x) (LevelSet.this y).

#[global] Instance reflect_LevelSet : ReflectEq LevelSet.t.
Proof.
  refine {| eqb := eqb_LevelSet |}.
  intros [thisx okx] [thisy oky].
  unfold eqb_LevelSet.
  cbn -[eqb].
  destruct (eqb_spec thisx thisy); subst; constructor.
  - f_equal; apply uip.
  - congruence.
Defined.
(* 
Definition eqb_universes_decl x y :=
  match x, y with
  | Monomorphic_ctx cx, Monomorphic_ctx cy => eqb cx cy
  | Polymorphic_ctx cx, Polymorphic_ctx cy => eqb cx cy
  | _, _ => false
  end. *)

Ltac finish_reflect :=
  (repeat
    match goal with
    | |- context[eqb ?a ?b] => destruct (eqb_spec a b); [subst|constructor; congruence]
    end);
  constructor; trivial; congruence.
(* 
#[global] Instance reflect_universes_decl : ReflectEq universes_decl.
Proof.
  refine {| eqb := eqb_universes_decl |}.
  unfold eqb_universes_decl.
  intros [] []; finish_reflect.
Defined. *)

Definition eqb_allowed_eliminations x y :=
  match x, y with
  | IntoSProp, IntoSProp
  | IntoPropSProp, IntoPropSProp
  | IntoSetPropSProp, IntoSetPropSProp
  | IntoAny, IntoAny => true
  | _, _ => false
  end.

#[global] Instance reflect_allowed_eliminations : ReflectEq allowed_eliminations.
Proof.
  refine {| eqb := eqb_allowed_eliminations |}.
  intros [] []; simpl; constructor; congruence.
Defined.

Local Infix "==?" := eqb (at level 20).

Definition eqb_Variance x y :=
  match x, y with
  | Variance.Irrelevant, Variance.Irrelevant
  | Variance.Covariant, Variance.Covariant
  | Variance.Invariant, Variance.Invariant => true
  | _, _ => false
  end.

#[global] Instance reflect_Variance : ReflectEq Variance.t.
Proof.
  refine {| eqb := eqb_Variance |}.
  intros [] []; constructor; congruence.
Defined.
