(** Extraction setup for template-coq.
    
    Any extracted code planning to link with the plugin's OCaml reifier
    should use these same directives for consistency.
*)

From Template Require univ uGraph Ast.

Require Import FSets.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString ExtrOcamlZInt.

Extraction Blacklist uGraph univ Ast String List Nat.

Set Warnings "-extraction-opaque-accessed".
Extraction Library List.
Extraction Library Datatypes.
Extraction Library Bool.
Extraction Library Nat.
Extraction Library BinNums.
Extraction Library BinNat.
Extraction Library BinIntDef.
Extraction Library BinInt.
Extraction Library BinPosDef.
Extraction Library BinPos.
Extraction Library String.
Extraction Library Ascii.
Extraction Library PeanoNat.
Extraction Library Specif.
Extraction Library Sumbool.
Extraction Library Basics.
Extraction Library DecidableType.
Extraction Library Equalities.
Extraction Library MSetWeakList.
Extraction Library FSetWeakList.
Extraction Library FMapWeakList.
Extraction Library monad_utils.
Extraction Library univ.
Extraction Library uGraph.
Extraction Library Ast.
