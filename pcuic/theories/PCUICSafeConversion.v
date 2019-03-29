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

  Definition conv leq Σ Γ u v :=
    match leq with
    | Conv => ∥ Σ ;;; Γ |- u = v ∥
    | Cumul => ∥ Σ ;;; Γ |- u <= v ∥
    end.

  Definition nodelta_flags := RedFlags.mk true true true false true true.

  Lemma red_welltyped :
    forall {Σ Γ u v},
      welltyped Σ Γ u ->
      ∥ red (fst Σ) Γ u v ∥ ->
      welltyped Σ Γ v.
  Proof.
    intros Σ' Γ u v h [r].
    revert h. induction r ; intros h.
    - assumption.
    - specialize IHr with (1 := ltac:(eassumption)).
      destruct IHr as [A ?]. exists A.
      eapply subject_reduction ; eassumption.
  Qed.

  Set Equations With UIP.

  Notation no := (exist _ false I).
  Notation yes := (exist _ true _).
  Notation rec isconv_prog leq Γ t1 π1 h1 t2 π2 h2 :=
    (let '(exist _ b h) := isconv_prog leq Γ t1 π1 h1 t2 π2 h2 in exist _ b _).

  Equations isconv (leq : conv_pb) (Γ : context)
            (t1 : term) (π1 : stack) (h1 : welltyped Σ Γ (zip (t1, π1)))
            (t2 : term) (π2 : stack) (h2 : welltyped Σ Γ (zip (t2, π2)))
    : { b : bool | if b then conv leq Σ Γ (zipc t1 π1) (zipc t2 π2) else True } :=
    isconv leq Γ t1 π1 h1 t2 π2 h2 :=
      let '(exist _ (t1,π1) eq1) :=
          inspect (reduce_stack nodelta_flags Σ Γ t1 π1 h1)
      in
      let '(exist _ (t2,π2) eq2) :=
          inspect (reduce_stack nodelta_flags Σ Γ t2 π2 h2)
      in
      rec isconv_prog leq Γ t1 π1 _ t2 π2 _
  where
    isconv_prog leq Γ t1 π1 (h1 : welltyped Σ Γ (zip (t1, π1)))
                      t2 π2 (h2 : welltyped Σ Γ (zip (t2, π2)))
    : { b : bool | if b then conv leq Σ Γ (zipc t1 π1) (zipc t2 π2) else True } :=

    (* isconv_prog leq Γ (tLambda na A1 t1) π1 h1 (tLambda _ A2 t2) π2 h2 *)
    (* with isconv leq Γ A1 Empty _ A2 Empty _ := { *)
    (* | @exist true h => rec isconv Conv (Γ,, vass na A1) t1 Empty _ t2 Empty _ ; *)
    (* | @exist false _ => no *)
    (* } ; *)

    isconv_prog leq Γ t1 π1 h1 t2 π2 h2 := no.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.

End Conversion.