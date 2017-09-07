Require Import Template.Ast.
Require Import Template.Typing.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Set Extraction Optimize.

Extraction Blacklist Ast String List Nat Typing.

Extraction Library Specif.
Extraction Library PeanoNat.
Extraction Library Sumbool.
Extraction Library Typing.
