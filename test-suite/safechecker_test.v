From MetaCoq.Template Require Import Loader.
From MetaCoq.SafeChecker Require Import Loader.
Require Import MetaCoq.SafeChecker.SafeTemplateChecker.

Local Open Scope string_scope.

MetaCoq SafeCheck nat.
(*
Environment is well-formed and Ind(Coq.Init.Datatypes.nat,0,[]) has type: Sort([Set])
*)

MetaCoq SafeCheck (3 + 1).

Definition bool_list := List.map negb (cons true (cons false nil)).
MetaCoq SafeCheck bool_list.
MetaCoq CoqCheck bool_list.

(* Time MetaCoq SafeCheck @infer_and_print_template_program. *)
(* Uses template polymorphism:
Error:
Type error: Terms are not <= for cumulativity: Sort([Coq.Init.Datatypes.23,Coq.Init.Datatypes.24]) Sort([Set]) after reduction: Sort([Coq.Init.Datatypes.23,Coq.Init.Datatypes.24]) Sort([Set]), while checking MetaCoq.Template.Universes.Universe.Expr.t
*)

(* Unset Universe Minimization ToSet. *)

(* From Coq Require Import Decimal. *)

Definition bignat : nat := Nat.of_num_uint 10000%uint.
MetaCoq SafeCheck bignat.
MetaCoq CoqCheck bignat.

From MetaCoq.TestSuite Require Import hott_example.

MetaCoq SafeCheck @issect'.

MetaCoq SafeCheck @ap_pp.
MetaCoq CoqCheck ap_pp.

Set MetaCoq Timing.

From MetaCoq.TestSuite Require Import hott_example.

(* FIXME TODO Private polymorphic universes *)
MetaCoq SafeCheck @isequiv_adjointify.
MetaCoq CoqCheck isequiv_adjointify.

MetaCoq SafeCheck @IsEquiv.
MetaCoq CoqCheck IsEquiv.
