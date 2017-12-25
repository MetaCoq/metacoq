From Template Require Import Ast Typing Checker.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Set Extraction Optimize.

Extraction Blacklist Ast String List Nat Typing.

Extraction Library Specif.
Extraction Library PeanoNat.
Extraction Library Sumbool.
Extraction Library Induction.
Extraction Library LiftSubst.
Extraction Library Typing.
Extraction Library Checker.
