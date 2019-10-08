Require Import Coq.Strings.String.
Require Import MetaCoq.Template.Loader.

Inductive U : Type :=
| TT : id U.

MetaCoq Quote Recursively Definition qU := U.
Print qU.
