(*! Common syntax to ITT and ETT *)

(* Preamble *)
Notation "'∑'  x .. y , P" := (sigT (fun x => .. (sigT (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity) : type_scope.

Require Import Ast.

Inductive sterm : Type :=
| sRel (n : nat)
| sSort (s : sort)
| sProd (nx : name) (A B : sterm)
| sLambda (nx : name) (A B t : sterm)
| sApp (u : sterm) (nx : name) (A B v : sterm)
(* Monogenous equality *)
| sEq (A u v : sterm)
| sRefl (A u : sterm)
| sJ (A u P w v p : sterm)
| sTransport (T1 T2 p t : sterm)
| sUip (A u v p q : sterm)
| sFunext (A B f g e : sterm)
(* Heterogenous equality *)
| sHeq (A a B b : sterm)
| sHeqToEq (A u v p : sterm)
| sHeqRefl (A a : sterm)
| sHeqSym (A a B b p : sterm)
| sHeqTrans (A a B b C c p q : sterm)
| sHeqTransport (A B p t : sterm)
| sCongProd (A1 A2 B1 B2 p q : sterm)
.