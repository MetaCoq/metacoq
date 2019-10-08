Require Import List Arith String.
Require Import MetaCoq.Template.All.
Import ListNotations MonadNotation.

Section test.

  MetaCoq Run (tmVariable "bla" nat).
  MetaCoq Run (tmDefinition "test" bla).

End test.

Print test.
