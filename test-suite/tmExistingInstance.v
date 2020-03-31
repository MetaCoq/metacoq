Require Import MetaCoq.Template.All.
Require Export String List.

Fail MetaCoq Run (tmExistingInstance "I").

Existing Class True.

MetaCoq Run (tmExistingInstance "I").
Print Instances True.


