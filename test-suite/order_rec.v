From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.

MetaCoq Quote Recursively Definition plus_syntax := plus.

Goal ∑ s1 t1 s2 t2, plus_syntax.1.(declarations) = [(s1, ConstantDecl t1); (s2, InductiveDecl t2)].
Proof.
  repeat eexists.
Qed.
