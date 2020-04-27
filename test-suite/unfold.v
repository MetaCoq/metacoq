Require Import MetaCoq.Template.All String.

MetaCoq Run (tmBind (tmEval (unfold "negb") negb) tmPrint).
