Require Import String List.
Require Import MetaCoq.Template.All.

Import ListNotations MCMonadNotation.

Open Scope string.

Notation "'unfolded' d" :=
  ltac:(let y := eval unfold d in d in exact y) (at level 100, only parsing).

(* To be able to work with values in SProp we define boxing/unboxing *)
Inductive sBox (A : SProp) : Type :=
  sbox : A -> sBox A.

Arguments sbox {_}.

Definition ubox {A : SProp} (bA : sBox A) : A :=
  match bA with
    sbox x => x
  end.

Inductive sle : nat -> nat -> SProp :=
  sle_0 : forall n, sle 0 n
| sle_S : forall n m : nat, sle n m -> sle (S n) (S m).

Definition zero_leq_zero : sle 0 0 := sle_0 _.

MetaCoq Quote Recursively Definition zero_leq_zero_syn := zero_leq_zero.
MetaCoq Unquote Definition zero_leq_zero' := (snd zero_leq_zero_syn).

Check eq_refl : sbox zero_leq_zero = sbox zero_leq_zero'.

Lemma sle_irrelevant n m (p q : sle n m) : sbox p = sbox q.
Proof. reflexivity. Defined.

MetaCoq Quote Definition sle_irrelevant_syn := (unfolded sle_irrelevant).
Print sle_irrelevant_syn.

MetaCoq Run (t <- tmUnquoteTyped (forall n m (p q: sle n m), sbox p = sbox q) sle_irrelevant_syn ;;
            tmDefinition "sle_irrelevant'" t).

Example sle_irrelevant_sle_irrelevant' : forall n m p q, sle_irrelevant n m p q = sle_irrelevant' n m p q.
Proof. reflexivity. Qed.

Module foo.

  MetaCoq Run (t <- tmQuoteInductive (MPfile ["sprop_tests"; "TestSuite"; "MetaCoq"], "sle") ;;
              t <- tmEval all (mind_body_to_entry t) ;;
              tmPrint t ;;
              tmMkInductive false t
             ).

  Print sle.
End foo.
