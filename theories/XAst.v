Require Import Ast.

Inductive xterm : Set :=
| tRel       : nat -> xterm
(* | tVar       : ident -> xterm *) (** For free variables (e.g. in a goal) *)
(* | tMeta      : nat -> xterm *)   (** NOTE: this can go away *)
(* | tEvar      : nat -> list xterm -> xterm *)
| tSort      : sort -> xterm
(* | tCast      : xterm -> cast_kind -> xterm -> xterm *)
| tProd      : name -> xterm (** the type **) -> xterm -> xterm
| tLambda    : name -> xterm (** type **) -> xterm (** type **) -> xterm -> xterm
(* | tLetIn     : name -> xterm (** the xterm **) -> xterm (** the type **) -> xterm -> xterm *)
(* | tApp       : xterm -> list xterm -> xterm *)
| tApp       : xterm -> xterm (** type **) -> xterm (** type **) -> xterm -> xterm
(* | tConst     : string -> universe_instance -> xterm *)
(* | tInd       : inductive -> universe_instance -> xterm *)
(* | tConstruct : inductive -> nat -> universe_instance -> xterm *)
(* | tCase      : (inductive * nat) (* # of parameters *) -> xterm (** type info **) *)
(*                -> xterm (* discriminee *)-> *)
(*                list (nat * xterm) (* branches *) *)
(*                -> xterm *)
(* | tProj      : projection -> xterm -> xterm *)
(* | tFix       : mfixpoint xterm -> nat -> xterm *)
(* | tCoFix     : mfixpoint xterm -> nat -> xterm *)
.