From Stdlib Require Import Strings.String.
From MetaCoq Require Import Template.Loader.

Inductive U : Type :=
| TT : id U.

MetaCoq Quote Recursively Definition qU := U.
