open Extractable
open Plugin_core
open BasicAst

open Quoter
open Ast_quoter


val interp_tm : Extractable.__ coq_TM -> Extractable.__ Plugin_core.tm

val run_vernac : 'a coq_TM -> unit
