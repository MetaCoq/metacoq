(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia
     Classes.RelationClasses.
From Template Require Import config univ monad_utils utils BasicAst AstUtils
     UnivSubst.
From PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICLiftSubst
     PCUICUnivSubst PCUICTyping PCUICSafeReduce.
From Equations Require Import Equations.

Require Import Equations.Prop.DepElim.

Import MonadNotation.

(** * Conversion for PCUIC without fuel

  Following PCUICSafereduce, we derive a fuel-free implementation of
  conversion (and cumulativity) checking for PCUIC.

 *)

Inductive conv_pb :=
| Conv
| Cumul.

Section Conversion.

  Context (flags : RedFlags.t).
  Context `{checker_flags}.
  Context (Σ : global_context).

  Definition nodelta_flags := RedFlags.mk true true true false true true.

  (* There seems to be a problem with reduce_stack!
     It shouldn't take an extra argument (tRel 0).
   *)
  Equations isconv (leq : conv_pb) (Γ : context)
            (t1 : term) (π1 : stack) (h1 : welltyped Σ Γ (zip (t1, π1)))
            (t2 : term) (π2 : stack) (h2 : welltyped Σ Γ (zip (t2, π2)))
    : bool :=
    isconv leq Γ t1 π1 h1 t2 π2 h2 :=
      let '(t1,π1) := reduce_stack nodelta_flags Σ Γ t1 (tRel 0) π1 h1 in
      let '(t2,π2) := reduce_stack nodelta_flags Σ Γ t2 (tRel 0) π2 h2 in
      isconv_prog leq Γ t1 π1 h1 t2 π2 h2
  where isconv_prog leq Γ t1 π1 h1 t2 π2 h2 : bool :=
        isconv_prog leq Γ t1 π1 h1 t2 π2 h2 := false.

End Conversion.