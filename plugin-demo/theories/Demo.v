Require Import Coq.Strings.String.
Declare ML Module "demo_plugin".
Require Import Lens.Lens.

Set Primitive Projections.

Record Point : Set :=
  { x: nat;
    y:nat
  }.

Definition two:=1+2.
About plus.

LookupPrint two.


Fail Print zeroE.

Make Lens Point.

SearchAbout Point.

(*
(* process coq segmentation fault *)
    *)