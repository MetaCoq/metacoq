From Template Require Import
     Ast
     TemplateMonad.Extractable.


Definition showoff : TM unit :=
  tmMsg "running from an extracted plugin!".
