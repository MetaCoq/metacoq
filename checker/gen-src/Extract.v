From MetaCoq.Template Require Import All Extraction.

Cd "../src".

Separate Extraction BasicAst Ast Universes Extractable
  BinInt BinPos PeanoNat Equalities TypingWf Checker Retyping.
