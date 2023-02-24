From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.
Import MCMonadNotation.

MetaCoq Run (tmLocate1 "I" >>= tmDefinition "qI").

Fail MetaCoq Run (tmExistingInstance global qI).

Existing Class True.

MetaCoq Run (tmExistingInstance global qI).
Print Instances True.
