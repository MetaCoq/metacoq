From Template Require Import Ast AstUtils Typing Checker.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import ExtrOcamlZInt.

Set Extraction Optimize.

Extraction Blacklist uGraph univ Ast AstUtils String List Nat Typing.

Set Warnings "-extraction-opaque-accessed".

Extraction Library Specif.
Extraction Library PeanoNat.
Extraction Library Sumbool.
Extraction Library Induction.
Extraction Library LiftSubst.
Extraction Library UnivSubst.
Extraction Library Typing.
Extraction Library utils.
Extraction Library AstUtils.
Extraction Library Checker.
