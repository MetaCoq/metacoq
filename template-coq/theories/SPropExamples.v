Require Import MetaCoq.Template.Ast.
Require Import MetaCoq.Template.Loader.

Inductive sle : nat -> nat -> SProp :=
  sle_0 : forall n, sle 0 n
| sle_S : forall n m : nat, sle n m -> sle (S n) (S m).

Definition blah : sle 0 0 := sle_0 _.

Locate Relevant.
Locate nAnon.

MetaCoq Quote Recursively Definition zzz' := (fun x : nat => x).

MetaCoq Quote Recursively Definition zzz := blah.
