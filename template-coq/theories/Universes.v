(* Distributed under the terms of the MIT license.   *)

From Coq Require Import List String ZArith.
From Template Require Import utils Ast.
Import ListNotations.

Import Level ConstraintType.

Record valuation := 
  { valuation_mono : string -> positive ;
    valuation_poly : nat -> nat }.

Definition wf_univ (u : universe)
  := [] <> u.

Fixpoint val0 (v : valuation) (l : Level.t) : Z :=
  match l with
  | lProp => -1
  | lSet => 0
  | Level s => Zpos (v.(valuation_mono) s)
  | Var x => Z.of_nat (v.(valuation_poly) x)
  end.

Definition val1 v (e : Universe.Expr.t) : Z :=
  let n := val0 v (fst e) in
  if snd e then n + 1 else n.

Program Definition val (v : valuation) (u : universe) (Hu : wf_univ u) : Z :=
  match u with
  | [] => _
  | e :: u => List.fold_left (fun n e => Z.max (val1 v e) n) u (val1 v e)
  end.
Next Obligation.
  apply False_rect.
  apply Hu; reflexivity.
Defined.

Inductive satisfies0 (v : valuation) : univ_constraint -> Prop :=
| satisfies0_Lt l l' : (val0 v l < val0 v l')%Z -> satisfies0 v (l, Lt, l')
| satisfies0_Le l l' : (val0 v l <= val0 v l')%Z -> satisfies0 v (l, Le, l')
| satisfies0_Eq l l' : val0 v l = val0 v l' -> satisfies0 v (l, Eq, l').

Definition satisfies v : constraints -> Prop := 
  ConstraintSet.For_all (satisfies0 v).

Definition consistent ctrs := exists v, satisfies v ctrs.

Definition eq_universe (φ : uGraph.t) u Hu u' Hu' :=
  forall v : valuation, satisfies v (snd φ) -> val v u Hu = val v u' Hu'.

Definition leq_universe (φ : uGraph.t) u Hu u' Hu' :=
  forall v : valuation, satisfies v (snd φ) -> (val v u Hu <= val v u' Hu')%Z.

Definition lt_universe (φ : uGraph.t) u Hu u' Hu' :=
  forall v : valuation, satisfies v (snd φ) -> (val v u Hu < val v u' Hu')%Z.
