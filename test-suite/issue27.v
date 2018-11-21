Require Import Template.All.
Require Export String List.
Run TemplateProgram (tmLemma "test" nat).
Run TemplateProgram (tmLemma "test" (@nil nat = @nil nat)).
