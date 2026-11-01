From MetaRocq.Template Require Import Loader All.
Require  Import ssreflect.
(* above two lines can be run in either order *)

Parameter a : nat.
Axiom aa : a = a + a.

Goal a + a + a + a+ a+ a + a = a.
Proof.
  now rw -!aa.
Qed.
