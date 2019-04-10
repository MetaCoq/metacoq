(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmp" i*)

open Entries
open Run_extractable
open Ltac_plugin
open Entries
open Names
open Tacexpr
open Tacinterp
open Misctypes
open Stdarg
open Tacarg
open Ast_quoter

DECLARE PLUGIN "demo_plugin"

VERNAC COMMAND EXTEND Make_vernac CLASSIFIED AS QUERY
   | [ "Showoff" ] ->
     [ Run_extractable.run_vernac Demo.genLensNInst ]
END;;

let quote_string s =
  let rec aux acc i =
    if i < 0 then acc
    else aux (s.[i] :: acc) (i - 1)
  in aux [] (String.length s - 1)

VERNAC COMMAND EXTEND Unquote_vernac CLASSIFIED AS SIDEFF
| [ "Make" "Lens" ident(name) ] ->
     [ Run_extractable.run_vernac (Demo.genLensN (quote_string (Names.Id.to_string name))) ]

END;;

