From MetaCoq.Template Require Import Loader.
From MetaCoq.SafeChecker Require Import Loader.
Local Open Scope string_scope.
MetaCoq SafeCheck nat.
(*
Environment is well-formed and Ind(Coq.Init.Datatypes.nat,0,[]) has type: Sort([Set])
*)

MetaCoq SafeCheck 3.
MetaCoq SafeCheck (3 + 1).

Quote Definition foo := (3 + 1).

Time MetaCoq SafeCheck plus.

Require Import MetaCoq.SafeChecker.SafeTemplateChecker.


Definition bool_list := List.map negb (cons true (cons false nil)).
Set Printing Universes.
(* Universe issues: undeclared universes from sections *)
(* Quote Recursively Definition boolq := bool_list. *)
MetaCoq SafeCheck bool_list.


(* Even with universe checking disabled, we get:
Error: Type error: Msgundeclared level, while checking MetaCoq.Template.Universes.LevelSet.Raw.elt
*)
(* Time MetaCoq SafeCheck @infer_and_print_template_program. *)
(*
Error:
Type error: Terms are not <= for cumulativity: Sort([Coq.Init.Datatypes.23,Coq.Init.Datatypes.24]) Sort([Set]) after reduction: Sort([Coq.Init.Datatypes.23,Coq.Init.Datatypes.24]) Sort([Set]), while checking MetaCoq.Template.Universes.Universe.Expr.t
*)