(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmp" i*)

open Entries
open Run_extractable

DECLARE PLUGIN "demo_plugin"

VERNAC COMMAND EXTEND Make_vernac CLASSIFIED AS QUERY
   | [ "Showoff" ] ->
     [ Run_extractable.run_vernac Demo.showoff ]
END;;
