(** Extraction setup for template-coq.
    
    Any extracted code planning to link with the plugin's OCaml reifier
    should use these same directives for consistency.
*)

From Template Require univ uGraph Ast.

Require Import FSets.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString (* ExtrOcamlZInt *).

Extraction Blacklist uGraph univ Ast String List Nat.
Print Extraction Blacklist.
Set Warnings "-extraction-opaque-accessed".
Recursive Extraction Library Ast.
