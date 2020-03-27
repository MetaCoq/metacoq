Require Import MetaCoq.Template.All.
Require Export String List.
Open Scope string.
MetaCoq Run (tmLemma "test" (@nil nat = @nil nat)).
