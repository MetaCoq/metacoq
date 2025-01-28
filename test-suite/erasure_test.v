From MetaCoq.ErasurePlugin Require Import Loader.
From MetaCoq.Template Require Import Loader.
Set MetaCoq Timing.
Local Open Scope string_scope.

MetaCoq Erase -help.

MetaCoq Erase nat.
(*
Environment is well-formed and Ind(Stdlib.Init.Datatypes.nat,0,[]) has type: ⧆
*)

MetaCoq Erase I.
MetaCoq Erase true.
(*
Environment is well-formed and Construct(Stdlib.Init.Logic.True,0,0,[]) erases to:
⧆
Environment is well-formed and Construct(Stdlib.Init.Datatypes.bool,0,0,[]) erases to:
Construct(Stdlib.Init.Datatypes.bool,0,0)
*)

MetaCoq Erase (exist (fun x => x = 0) 0 (eq_refl)).

Definition test := (proj1_sig (exist (fun x => x = 0) 0 (eq_refl))).

MetaCoq Erase -typed test.

(** Cofix *)
From Stdlib Require Import StreamMemo.

MetaCoq Quote Recursively Definition memo := memo_make.

MetaCoq Erase -typed -unsafe memo_make.

MetaCoq Erase (3 + 1).

Universe i.
MetaCoq Erase ((fun (X : Set) (x : X) => x) nat).

(** Check that optimization of singleton pattern-matchings work *)
MetaCoq Erase  ((fun (X : Set) (x : X) (e : x = x) =>
                  match e in eq _ x' return bool with
                  | eq_refl => true
                  end)).

(* (** Check the treatment of Prop <= Type *) *)
MetaCoq Erase ((fun (X : Set) (x : X) => x) True I).
(* MetaCoq Quote Recursively Definition foo := List.map. *)

From Stdlib Require Import List.
Import ListNotations.
MetaCoq Erase (map negb [true; false]).

Set Warnings "-abstract-large-number".
(* Definition bignat := Eval compute in 10000. *)
Test MetaCoq Timing.

(* MetaCoq Erase bignat. *)

From MetaCoq.TestSuite Require Import vs.
MetaCoq Erase main.
