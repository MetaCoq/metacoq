From MetaCoq.Template Require Import All Extraction.

Cd "../src".

Recursive Extraction Library TypingWf.
Recursive Extraction Library Checker.
Recursive Extraction Library Retyping.

Cd "../gen-src".