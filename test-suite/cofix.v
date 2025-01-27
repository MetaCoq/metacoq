From MetaCoq Require Import Template.Loader.
From Stdlib Require Import Streams.

CoFixpoint ones := Cons 1 ones.

MetaCoq Quote Recursively Definition q_ones := ones.

