Require Import List Arith String.
Require Import Template.All.
Import ListNotations MonadNotation.

Local Open Scope string_scope.

Quote Recursively Definition plus_syntax := plus.

Goal ∑ s1 t1 s2 t2, fst plus_syntax = [ConstantDecl s1 t1; InductiveDecl s2 t2].
Proof.
  repeat eexists.
Qed.
