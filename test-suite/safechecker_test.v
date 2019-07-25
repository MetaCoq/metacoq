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

(* Time MetaCoq SafeCheck @infer_and_print_template_program. *)
(*
Error:
Type error: Terms are not convertible: Ind(Coq.Init.Datatypes.nat,0,[]) App(Lambda(n,Ind(Coq.Init.Datatypes.nat,0,[]),Ind(Coq.Init.Datatypes.nat,0,[])),Construct(Coq.Init.Datatypes.nat,0,0,[])) after reduction: Ind(Coq.Init.Datatypes.nat,0,[]) Ind(Coq.Init.Datatypes.nat,0,[]), while checking Coq.Init.Nat.add
*)