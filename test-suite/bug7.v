Require Import MetaCoq.Template.Loader.

Axiom a_nat : nat.

MetaCoq Quote Recursively Definition qn := (a_nat + 1).

Polymorphic Axiom poly : forall x : Type, x.

MetaCoq Quote Recursively Definition qpoly := poly.
