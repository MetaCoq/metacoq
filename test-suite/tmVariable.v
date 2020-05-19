Require Import List Arith String.
Require Import MetaCoq.Template.All.
Import ListNotations MonadNotation.

Section test.

  MetaCoq Run (tmVariable "bla" nat).
  Check (bla : nat).
  MetaCoq Run (tmDefinition "test" bla).
  MetaCoq Run (tmDefinition "test2" 0).


End test.

Check (test : nat -> nat).
Check (test2 : nat).
