Require Import Coq.Strings.String.
Require Import Coq.PArith.BinPos.

Definition universe := positive.
Definition ident := string.

Inductive sort : Type :=
| sProp
| sSet
| sType (_ : universe).

Record ind : Type := {} .

Inductive name : Type :=
| nAnon
| nNamed (_ : ident).

Inductive cast_kind : Type :=
| VmCast
| NativeCast
| Cast
| RevertCast.

Inductive inductive : Type :=
| mkInd : string -> nat -> inductive.

Inductive term : Type :=
| tRel       : nat -> term
| tVar       : ident -> term
| tMeta      : nat -> term
| tEvar      : nat -> term
| tSort      : sort -> term
| tCast      : term -> cast_kind -> term -> term
| tProd      : name -> term -> term
| tLambda    : name -> term -> term
| tLetIn     : name -> term -> term -> term -> term
| tApp       : term -> list term -> term
| tConst     : string -> term
| tInd       : string -> nat -> term
| tConstruct : string -> nat -> nat -> term
| tCase      : term -> (** type info **) list (pattern * term) -> term
| tFix       : name -> list name -> nat -> term -> term
(*
| CoFix     of ('constr, 'types) pcofixpoint
*)
| tUnknown : string -> term
with pattern : Type :=
| pBind    : name -> pattern
| pHole    : pattern
| pCtor    : name -> list pattern -> pattern.