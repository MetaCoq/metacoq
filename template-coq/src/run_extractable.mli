open Extractable
open Plugin_core
open BasicAst

open Quoter
open Ast_quoter

val interp_tm : Extractable.__ coq_TM -> Extractable.__ Plugin_core.tm

val run_vernac : pm:Plugin_core.coq_state -> 'a coq_TM -> Plugin_core.coq_state
