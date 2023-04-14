From MetaCoq.Template Require Import Extraction.
Require Import Lens MyPlugin.

Set Warnings "-extraction-opaque-accessed".
Set Warnings "-extraction-reserved-identifier".

Cd "gen-src".

Extraction Library Lens.
Extraction Library MyPlugin.

Cd "..".
