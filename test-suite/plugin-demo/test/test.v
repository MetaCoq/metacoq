Require Import Coq.Strings.String.
From MetaCoq.ExtractedPluginDemo Require Import Lens Loader.

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

Search Point.

Module A.
  Showoff.
End A.
