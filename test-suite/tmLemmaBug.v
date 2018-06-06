Require Import Template.All.
Require Export String List.

Run TemplateProgram (tmLemma "test1" nat).
Next Obligation.
  exact 0.
Qed.
  
Run TemplateProgram (tmLemma "test" (@nil nat = nil)).

