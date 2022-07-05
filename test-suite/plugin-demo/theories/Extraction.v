From MetaCoq Require Import Template.Extraction.
Require Import Lens MyPlugin.

Cd "gen-src".

Extraction Library Lens.
Extraction Library MyPlugin.

Cd "..".
