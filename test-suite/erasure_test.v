From MetaCoq.ErasurePlugin Require Import Loader.
From MetaCoq.Template Require Import Loader.
Set MetaCoq Timing.
Local Open Scope string_scope.

MetaCoq Erase nat.
(*
Environment is well-formed and Ind(Coq.Init.Datatypes.nat,0,[]) has type: ⧆
*)

MetaCoq Erase I.
MetaCoq Erase true.
(*
Environment is well-formed and Construct(Coq.Init.Logic.True,0,0,[]) erases to:
⧆
Environment is well-formed and Construct(Coq.Init.Datatypes.bool,0,0,[]) erases to:
Construct(Coq.Init.Datatypes.bool,0,0)
*)

MetaCoq Erase (exist _ 0 (eq_refl) : {x : nat | x = 0}).
(* (* *)
(* Environment is well-formed and exist nat (fun x : nat => eq nat x O) O (eq_refl nat O):sig nat (fun x : nat => eq nat x O) erases to: *)
(* (fun f => f) (exist ∎ ∎ O ∎) *)
(* *) *)
MetaCoq Erase (3 + 1).

Universe i.
MetaCoq Fast Erase ((fun (X : Set) (x : X) => x) nat).

(** Check that optimization of singleton pattern-matchings work *)
MetaCoq Erase ((fun (X : Set) (x : X) (e : x = x) =>
                  match e in eq _ x' return bool with
                  | eq_refl => true
                  end)).

(* (** Check the treatment of Prop <= Type *) *)
MetaCoq Erase ((fun (X : Set) (x : X) => x) True I).
(* MetaCoq Quote Recursively Definition foo := List.map. *)

Require Import List.
Import ListNotations.
MetaCoq Erase (map negb [true; false]).

Set Warnings "-abstract-large-number".
(* Definition bignat := Eval compute in 10000. *)
Test MetaCoq Timing.

(* MetaCoq Erase bignat. *)

From MetaCoq.TestSuite Require Import vs.
MetaCoq Erase main.
