Require Import MetaCoq.Template.All.
Require Export String List.

Fail Run TemplateProgram (tmExistingInstance "I").

Existing Class True.

Run TemplateProgram (tmExistingInstance "I").
Print Instances True.


