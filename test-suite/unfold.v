From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.
Import MCMonadNotation.

MetaCoq Test Quote negb.
MetaCoq Run (tmBind (tmEval (unfold (MPfile ["Datatypes"; "Init"; "Coq"], "negb")) negb) tmPrint).
