Require Import List Arith String.
From MetaCoq Require Import Template.All.
Import ListNotations MonadNotation.

Local Open Scope string_scope.

MetaCoq Quote Recursively Definition plus_syntax := plus.

Goal ∑ s1 t1 s2 t2, fst plus_syntax = [(s1, ConstantDecl t1); (s2, InductiveDecl t2)].
Proof.
  repeat eexists.
Qed.
