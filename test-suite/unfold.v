Require Import MetaCoq.Template.All.

Run TemplateProgram (tmBind (tmEval (unfold "negb") negb) tmPrint).
