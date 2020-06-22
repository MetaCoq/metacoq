Require Import MetaCoq.Template.All.
Require Export String List.
Import MonadNotation.
MetaCoq Run (tmLocate1 "I" >>= tmDefinition "qI").

Fail MetaCoq Run (tmExistingInstance qI).

Existing Class True.

MetaCoq Run (tmExistingInstance qI).
Print Instances True.


