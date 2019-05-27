Require Import MetaCoq.Template.All.
Require Export String List.
Open Scope string.
Run TemplateProgram (tmLemma "test" (@nil nat = @nil nat)).
