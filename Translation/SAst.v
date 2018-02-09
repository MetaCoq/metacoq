(*! Common syntax to ITT and ETT *)

(* Preamble *)
Notation "'∑'  x .. y , P" := (sigT (fun x => .. (sigT (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity) : type_scope.

From Template Require Import Ast.

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
(* Heterogenous equality *)
| sHeq (A a B b : sterm)
| sHeqToEq (p : sterm)
| sHeqRefl (A a : sterm)
| sHeqSym (p : sterm)
| sHeqTrans (p q : sterm)
| sHeqTransport (p t : sterm)
| sCongProd (B1 B2 pA pB : sterm)
| sCongLambda (B1 B2 t1 t2 pA pB pt : sterm)
| sCongApp (B1 B2 pu pA pB pv : sterm)
| sCongEq (pA pu pv : sterm)
| sCongRefl (pA pu : sterm)
| sEqToHeq (p : sterm)
| sHeqTypeEq (p : sterm)
(* Packing *)
| sPack (A1 A2 : sterm)
| sProjT1 (p : sterm)
| sProjT2 (p : sterm)
| sProjTe (p : sterm)
.