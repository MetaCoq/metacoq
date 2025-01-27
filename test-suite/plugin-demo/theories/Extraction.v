From MetaCoq.Template Require Import Extraction.
From Stdlib Require Import Lens MyPlugin.

Set Warnings "-extraction-opaque-accessed".
Set Warnings "-extraction-reserved-identifier".

Set Extraction Output Directory "gen-src".

Extraction Library Lens.
Extraction Library MyPlugin.

