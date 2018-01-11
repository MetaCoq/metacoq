Require Import Ast.

Inductive iterm : Set :=
| iRel       : nat -> iterm
(* | iVar       : ident -> iterm *) (** For free variables (e.g. in a goal) *)
(* | iMeta      : nat -> iterm *)   (** NOTE: this can go away *)
(* | iEvar      : nat -> list iterm -> iterm *)
| iSort      : sort -> iterm
(* | iCast      : iterm -> cast_kind -> iterm -> iterm *)
| iProd      : name -> iterm (** the type **) -> iterm -> iterm
| iLambda    : name -> iterm (** type **) -> iterm (** type **) -> iterm -> iterm
(* | iLetIn     : name -> iterm (** the iterm **) -> iterm (** the type **) -> iterm -> iterm *)
(* | iApp       : iterm -> list iterm -> iterm *)
| iApp       : iterm -> name -> iterm (** type **) -> iterm (** type **) -> iterm -> iterm
(* | iConst     : string -> universe_instance -> iterm *)
(* | iInd       : inductive -> universe_instance -> iterm *)
(* | iConstruct : inductive -> nat -> universe_instance -> iterm *)
(* | iCase      : (inductive * nat) (* # of parameters *) -> iterm (** type info **) *)
(*                -> iterm (* discriminee *)-> *)
(*                list (nat * iterm) (* branches *) *)
(*                -> iterm *)
(* | iProj      : projection -> iterm -> iterm *)
(* | iFix       : mfixpoint iterm -> nat -> iterm *)
(* | iCoFix     : mfixpoint iterm -> nat -> iterm *)

(* For now we use our own syntax for equality, we don't need an eliminator
   thanks to reflection. *)
| iEq        : sort -> iterm -> iterm -> iterm -> iterm
| iRefl      : iterm -> iterm -> iterm
.