(* Distributed under the terms of the MIT license.   *)

From Coq Require Import List String ZArith.
From Template Require Import utils Ast.
Import ListNotations.

Import Level ConstraintType.

Definition valuation := string -> positive.

Inductive monomorphic : Level.t -> Prop :=
| monomorphic_Prop : monomorphic lProp
| monomorphic_Set : monomorphic lSet
| monomorphic_Level s : monomorphic (Level s).

Definition wf_univ (u : universe)
  := u <> [] /\ Forall (fun e => monomorphic (fst e)) u.

Program Fixpoint val0 (v : valuation) l (Hl : monomorphic l) : Z :=
  match l with
  | lProp => -1
  | lSet => 0
  | Level s => Zpos' (v s)
  | Var x => _
  end.
Next Obligation.
  apply False_rect. inversion Hl.
Defined.

Definition val1 v (e : Universe.Expr.t) (He : monomorphic (fst e)) : Z :=
  let n := val0 v (fst e) He in
  if snd e then n + 1 else n.

Program Fixpoint val (v : valuation) (u : universe) (Hu : wf_univ u) {struct u}
  : Z :=
  match u with
  | [] => _
  | e :: u => match u with
             | [] => val1 v e _
             | e' :: u' => Z.max (val1 v e _) (val v u _)
             end
  end.
Next Obligation.
  apply False_rect.
  apply Hu; reflexivity.
Defined.
Next Obligation.
  destruct Hu as [_ Hu]. now inversion Hu.
Defined.
Next Obligation.
  destruct Hu as [_ Hu]. now inversion Hu.
Defined.
Next Obligation.
  split.
  intro eq; inversion eq.
  destruct Hu as [_ Hu]. now inversion Hu.
Defined.

Inductive satisfies0 (v : valuation) : univ_constraint -> Prop :=
| satisfies0_Lt l l' : (v l < v l')%positive -> satisfies0 v (Level l, Lt, Level l')
| satisfies0_Le l l' : (v l <= v l')%positive -> satisfies0 v (Level l, Le, Level l')
| satisfies0_Eq l l' : v l = v l' -> satisfies0 v (Level l, Eq, Level l').

Definition satisfies v : constraints -> Prop := 
  ConstraintSet.For_all (satisfies0 v).

Definition consistent ctrs := exists v, satisfies v ctrs.

Definition eq_universe (φ : uGraph.t) u Hu u' Hu' :=
  forall v : valuation, satisfies v (snd φ) -> val v u Hu = val v u' Hu'.

Definition leq_universe (φ : uGraph.t) u Hu u' Hu' :=
  forall v : valuation, satisfies v (snd φ) -> (val v u Hu <= val v u' Hu')%Z.

Definition lt_universe (φ : uGraph.t) u Hu u' Hu' :=
  forall v : valuation, satisfies v (snd φ) -> (val v u Hu < val v u' Hu')%Z.
