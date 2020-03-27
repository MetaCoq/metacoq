Require Import MetaCoq.Template.All.
Require Export String List.

Import MonadNotation.

Existing Class True.
Existing Instance I.

MetaCoq Run (tmInferInstance None True >>= tmPrint).
MetaCoq Run (tmInferInstance None False >>= tmPrint).
