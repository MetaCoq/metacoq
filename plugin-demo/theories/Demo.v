Require Import Coq.Strings.String.
Declare ML Module "demo_plugin".

Record Point : Set :=
  { x: nat;
    y:nat
  }.

Definition two:=1+2.
About plus.

LookupPrint two.


Showoff.
(*
(* process coq segmentation fault *)
    *)