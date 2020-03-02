Require Import MetaCoq.Template.All String.

Run TemplateProgram (tmBind (tmEval (unfold "negb") negb) tmPrint).
