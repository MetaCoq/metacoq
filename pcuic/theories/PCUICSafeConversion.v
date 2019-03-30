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

  Derive Subterm for term.
  Derive NoConfusion NoConfusionHom Subterm for stack.

  Notation no := (exist _ false I).
  Notation yes := (exist _ true _).
  Notation rec isconv_prog leq Γ t1 π1 h1 t2 π2 h2 :=
    (let '(exist _ b h) := isconv_prog leq Γ t1 π1 h1 t2 π2 h2 in exist _ b _).

  (* We have to devise an order for termination.
     It seems that we could somehow use the R from before, except that we would
     need to include more positions.
     So maybe, just lex cored subterm would work.

     Another solution would be to consider (t,π) ≤ (u,θ)
     when fst (reduce (t,π)) is a subterm of fst (reduce (u,θ)).

     If we need to speak about the stacks for the order, then we probably have
     to include a lot more stacks as well.
     That would be unfortunate.

     It seems that this approach is fine, except for a few (important) things:
     - the fallback terminates because we check reduction progressed
     - isconv_stacks needs to be able to reduce on the stack, so the order would
       have to mention it.

     A different point, we might need to update reduce in some way to assert
     that it cannot return an application, they must reside on the stack.

     Maybe implement a naive version first that reduces both sides (with delta
     or rather with provided flags).
     When two sides are equal, go to subterms (meaning stacks are empty by
     typing). When two sides are constants/variables, compare the stacks.
     This is fine for a lex order on subterm for the term and then subterm
     for the stack.
   *)

  Equations isconv (leq : conv_pb) (Γ : context)
            (t1 : term) (π1 : stack) (h1 : welltyped Σ Γ (zip (t1, π1)))
            (t2 : term) (π2 : stack) (h2 : welltyped Σ Γ (zip (t2, π2)))
    : { b : bool | if b then conv leq Σ Γ (zipc t1 π1) (zipc t2 π2) else True }
    by struct :=
    isconv leq Γ t1 π1 h1 t2 π2 h2
    with inspect (reduce_stack nodelta_flags Σ Γ t1 π1 h1) := {
    | @exist (t1',π1') eq1
      with inspect (reduce_stack nodelta_flags Σ Γ t2 π2 h2) := {
      | @exist (t2',π2') eq2 => rec isconv_prog leq Γ t1' π1' _ t2' π2' _
      }
    }

  where
    isconv_prog leq Γ t1 π1 (h1 : welltyped Σ Γ (zip (t1, π1)))
                      t2 π2 (h2 : welltyped Σ Γ (zip (t2, π2)))
    : { b : bool | if b then conv leq Σ Γ (zipc t1 π1) (zipc t2 π2) else True } :=

    isconv_prog leq Γ (tLambda na A1 t1) π1 h1 (tLambda _ A2 t2) π2 h2
    with isconv leq Γ A1 Empty _ A2 Empty _ := {
    | @exist true h => rec isconv Conv (Γ,, vass na A1) t1 Empty _ t2 Empty _ ;
    | @exist false _ => no
    } ;

    isconv_prog leq Γ t1 π1 h1 t2 π2 h2 := no.
  Next Obligation.
    eapply red_welltyped ; try eassumption.
    rewrite eq1.
    eapply reduce_stack_sound.
  Qed.
  Next Obligation.
    eapply red_welltyped.
    - eapply h2.
    - rewrite eq2.
      eapply reduce_stack_sound.
  Qed.
  Admit Obligations.

End Conversion.