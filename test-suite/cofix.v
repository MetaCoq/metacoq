Require Import MetaCoq.Template.Loader.
Require Import Streams.

CoFixpoint ones := Cons 1 ones.

MetaCoq Quote Recursively Definition q_ones := ones.

