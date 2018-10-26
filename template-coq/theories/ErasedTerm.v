(* Distributed under the terms of the MIT license.   *)

Require Import Coq.Strings.String.
Require Import Coq.PArith.BinPos.
Require Import List. Import ListNotations.
From Template Require Import monad_utils.
From Template Require Export univ uGraph Ast.

(** Erased terms

  These are the terms produced by erasure:
  compared to kernel terms, all proofs are translated to [tBox] and
  casts are removed.
*)

Inductive term : Set :=
| tBox       : term (* Represents all proofs *)
| tRel       : nat -> term
| tVar       : ident -> term (* For free variables (e.g. in a goal) *)
| tMeta      : nat -> term   (* NOTE: this will go away *)
| tEvar      : nat -> list term -> term
| tSort      : universe -> term
| tProd      : forall (_:name) (type:term) (body:term), term
| tLambda    : name -> term -> term -> term
| tLetIn     : forall (_:name) (term_:term) (type:term) (body:term), term
| tApp       : term -> list term -> term
| tConst     : kername -> universe_instance -> term
| tInd       : inductive -> universe_instance -> term
| tConstruct : inductive -> nat -> universe_instance -> term
| tCase      : forall (inductive_and_nb_params:inductive*nat) (type_info:term)
                      (discriminee:term) (branches : list (nat * term)), term
| tProj      : projection -> term -> term
| tFix       : mfixpoint term -> nat -> term
| tCoFix     : mfixpoint term -> nat -> term.
