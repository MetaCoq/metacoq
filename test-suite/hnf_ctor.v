Require Import Coq.Strings.String.
Require Import Template.Template.

Inductive U : Type :=
| TT : id U.

Quote Recursively Definition qU := U.
Print qU.