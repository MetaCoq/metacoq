(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import utils Universes BasicAst Primitive Reflect.
From MetaCoq.PCUIC Require Import Environment EnvironmentTyping.
From Equations Require Import Equations.
From Coq Require Import ssreflect.
From Coq Require Import Uint63 SpecFloat.

(** We don't enforce the type of the array here*)
Record array_model (term : Type) :=
  { array_instance : Instance.t;
    array_type : term;
    array_default : term;
    array_value : list term }.
Derive NoConfusion for array_model.
#[global]
Instance array_model_eqdec {term} (e : EqDec term) : EqDec (array_model term).
Proof. eqdec_proof. Qed.

Inductive prim_model (term : Type) : prim_tag -> Type :=
| primIntModel (i : PrimInt63.int) : prim_model term primInt
| primFloatModel (f : PrimFloat.float) : prim_model term primFloat.

(* | primIntModel (i : Int63.t) : prim_model term primInt *)
(* | primFloatModel (f : float64_model) : prim_model term primFloat. *)
(* | primArrayModel (a : array_model term) : prim_model term primArray. *)
Arguments primIntModel {term}.
Arguments primFloatModel {term}.
(* Arguments primArrayModel {term}. *)

Derive Signature NoConfusion for prim_model.

Definition prim_model_of (term : Type) (p : prim_tag) : Type :=
  match p with
  | primInt => PrimInt63.int
  | primFloat => PrimFloat.float
  (* | primArray => array_model term *)
  end.

Definition prim_val term := ∑ t : prim_tag, prim_model term t.
Definition prim_val_tag {term} (s : prim_val term) := s.π1.
Definition prim_val_model {term} (s : prim_val term) : prim_model term (prim_val_tag s) := s.π2.

Definition prim_model_val {term} (p : prim_val term) : prim_model_of term (prim_val_tag p) :=
  match prim_val_model p in prim_model _ t return prim_model_of term t with
  | primIntModel i => i
  | primFloatModel f => f
  (* | primArrayModel a => a *)
  end.

Lemma exist_irrel_eq {A} (P : A -> bool) (x y : sig P) : proj1_sig x = proj1_sig y -> x = y.
Proof.
  destruct x as [x p], y as [y q]; simpl; intros ->.
  now destruct (uip p q).
Qed.

#[global]
Instance reflect_eq_Z : ReflectEq Z := EqDec_ReflectEq _.

Local Obligation Tactic := idtac.
#[program]
#[global]
Instance reflect_eq_uint63 : ReflectEq uint63_model :=
  { eqb x y := Z.eqb (proj1_sig x) (proj1_sig y) }.
Next Obligation.
  cbn -[eqb].
  intros x y.
  elim: Z.eqb_spec. constructor.
  now apply exist_irrel_eq.
  intros neq; constructor => H'; apply neq; now subst x.
Qed.

#[global]
Instance reflect_eq_spec_float : ReflectEq SpecFloat.spec_float := EqDec_ReflectEq _.

Equations eqb_prim_model {term} {t : prim_tag} (x y : prim_model term t) : bool :=
  | primIntModel x, primIntModel y := ReflectEq.eqb x y
  | primFloatModel x, primFloatModel y := ReflectEq.eqb x y.

#[global, program]
Instance prim_model_reflecteq {term} {p : prim_tag} : ReflectEq (prim_model term p) :=
  {| ReflectEq.eqb := eqb_prim_model |}.
Next Obligation.
  intros. depelim x; depelim y; simp eqb_prim_model.
  case: ReflectEq.eqb_spec; constructor; subst; auto. congruence.
  case: ReflectEq.eqb_spec; constructor; subst; auto. congruence.
Qed.

#[global]
Instance prim_model_eqdec {term} : forall p : prim_tag, EqDec (prim_model term p) := _.

Equations eqb_prim_val {term} (x y : prim_val term) : bool :=
  | (primInt; i), (primInt; i') := ReflectEq.eqb i i'
  | (primFloat; f), (primFloat; f') := ReflectEq.eqb f f'
  | x, y := false.

#[global, program]
Instance prim_val_reflect_eq {term} : ReflectEq (prim_val term) :=
  {| ReflectEq.eqb := eqb_prim_val |}.
Next Obligation.
  intros. funelim (eqb_prim_val x y); simp eqb_prim_val.
  case: ReflectEq.eqb_spec; constructor; subst; auto. intros H; noconf H. cbn in n. auto.
  constructor. intros H; noconf H; auto.
  constructor. intros H; noconf H; auto.
  case: ReflectEq.eqb_spec; constructor; subst; auto. intros H; noconf H; auto.
Qed.

#[global]
Instance prim_tag_model_eqdec term : EqDec (prim_val term) := _.

(** Printing *)

Definition string_of_prim {term} (soft : term -> string) (p : prim_val term) : string :=
  match p.π2 return string with
  | primIntModel f => "(int: " ^ string_of_prim_int f ^ ")"
  | primFloatModel f => "(float: " ^ string_of_float f ^ ")"
  (* | primArrayModel a => "(array:" ^ ")" *)
  end.
