(** Extraction setup for template-coq.

    Any extracted code planning to link with the plugin's OCaml reifier
    should use these same directives for consistency.
*)

From Template Require All.

Require Import FSets.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString (* (* TODO add this when it will be fixed in Coq *) ExtrOcamlZInt *).

Extraction Blacklist uGraph univ Ast String List Nat UnivSubst Typing Checker.
Set Warnings "-extraction-opaque-accessed".
Recursive Extraction Library Checker.
