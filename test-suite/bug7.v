Require Import Template.Template.

Axiom a_nat : nat.

Quote Recursively Definition qn := (a_nat + 1).

Polymorphic Axiom poly : forall x : Type, x.

Quote Recursively Definition qpoly := poly.
