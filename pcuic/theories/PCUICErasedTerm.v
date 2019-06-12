(* Distributed under the terms of the MIT license.   *)

Require Import Coq.Strings.String.
Require Import Coq.PArith.BinPos.
Require Import List. Import ListNotations.
From MetaCoq.Template Require Import monad_utils.
From MetaCoq.Template Require Export uGraph Ast.

(** Erased terms

  These are the terms produced by erasure:
  compared to kernel terms, all proofs are translated to [tBox] and
  casts are removed.
*)
Inductive term : Set :=
| tBox (t : term) (* Represents all proofs *)
| tRel (n : nat)
| tVar (id : ident) (* For free variables (e.g. in a goal) *)
| tEvar (ev : nat) (args : list term)
| tSort (s : universe)
| tProd (na : name) (ty : term) (body : term)
| tLambda (na : name) (ty : term) (body : term)
| tLetIn (na : name) (def : term) (def_ty : term) (body : term)
| tApp (f : term) (args : list term)
| tConst (c : kername) (u : universe_instance)
| tInd (ind : inductive) (u : universe_instance)
| tConstruct (ind : inductive) (idx : nat) (u : universe_instance)
| tCase (ind_and_nbparams: inductive*nat) (type_info:term)
        (discr:term) (branches : list (nat * term))
| tProj (proj : projection) (t : term)
| tFix (mfix : mfixpoint term) (idx : nat)
| tCoFix (mfix : mfixpoint term) (idx : nat).
