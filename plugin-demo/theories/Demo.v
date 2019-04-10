Require Import Coq.Strings.String.
Declare ML Module "demo_plugin".

Record Point : Set :=
  { x: nat;
    y:nat
  }.

Make Lens Point.
(* process coq segmentation fault *)
    