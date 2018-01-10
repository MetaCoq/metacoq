(** Extraction setup for template-coq.
    
    Any extracted code planning to link with the plugin's OCaml reifier
    should use these same directives for consistency.
*)

Require Import Template.Ast.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Extraction Blacklist Ast String List Nat.

Set Warnings "-extraction-opaque-accessed".
Extraction Library List.
Extraction Library Datatypes.
Extraction Library Bool.
Extraction Library Nat.
Extraction Library BinNums.
Extraction Library BinNat.
Extraction Library BinPosDef.
Extraction Library BinPos.
Extraction Library String.
Extraction Library Ascii.
Extraction Library PeanoNat.
Extraction Library Specif.
Extraction Library Sumbool.
Extraction Library monad_utils.
Extraction Library Ast.
