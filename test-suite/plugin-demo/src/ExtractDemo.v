From MetaRocq.Template Require Import Extraction.
From MetaRocq.ExtractedPluginDemo Require Import Lens MyPlugin.

Set Warnings "-extraction-opaque-accessed".
Set Warnings "-extraction-reserved-identifier".
(* dune expects the extracted files in the current directory *)
Set Warnings "-extraction-default-directory".
(* The specifications of the primitive integers and strings used by MetaRocq
   are axioms. *)
Set Warnings "-extraction-logical-axiom".

Extraction Library Lens.
Extraction Library MyPlugin.

