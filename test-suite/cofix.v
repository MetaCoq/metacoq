Require Import Template.Template.
Require Import Streams.

CoFixpoint ones := Cons 1 ones.

Quote Recursively Definition q_ones := ones.

