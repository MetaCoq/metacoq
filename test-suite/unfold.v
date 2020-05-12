Require Import MetaCoq.Template.All String.

MetaCoq Test Quote negb.
MetaCoq Run (tmBind (tmEval (unfold (MPfile ["Datatypes"; "Init"; "Coq"]%list, "negb")) negb) tmPrint).
