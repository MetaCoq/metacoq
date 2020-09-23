From MetaCoq.Template Require Import utils All.

MetaCoq Test Quote negb.
MetaCoq Run (tmBind (tmEval (unfold (MPfile ["Datatypes"; "Init"; "Coq"], "negb")) negb) tmPrint).
