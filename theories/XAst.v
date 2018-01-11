Require Import Ast.

Inductive xterm : Set :=
| xRel       : nat -> xterm
(* | xVar       : ident -> xterm *) (** For free variables (e.g. in a goal) *)
(* | xMeta      : nat -> xterm *)   (** NOTE: this can go away *)
(* | xEvar      : nat -> list xterm -> xterm *)
| xSort      : sort -> xterm
(* | xCast      : xterm -> cast_kind -> xterm -> xterm *)
| xProd      : name -> xterm (** the type **) -> xterm -> xterm
| xLambda    : name -> xterm (** type **) -> xterm (** type **) -> xterm -> xterm
(* | xLetIn     : name -> xterm (** the xterm **) -> xterm (** the type **) -> xterm -> xterm *)
(* | xApp       : xterm -> list xterm -> xterm *)
| xApp       : xterm -> xterm (** type **) -> xterm (** type **) -> xterm -> xterm
(* | xConst     : string -> universe_instance -> xterm *)
(* | xInd       : inductive -> universe_instance -> xterm *)
(* | xConstruct : inductive -> nat -> universe_instance -> xterm *)
(* | xCase      : (inductive * nat) (* # of parameters *) -> xterm (** type info **) *)
(*                -> xterm (* discriminee *)-> *)
(*                list (nat * xterm) (* branches *) *)
(*                -> xterm *)
(* | xProj      : projection -> xterm -> xterm *)
(* | xFix       : mfixpoint xterm -> nat -> xterm *)
(* | xCoFix     : mfixpoint xterm -> nat -> xterm *)
.