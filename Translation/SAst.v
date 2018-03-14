(*! Common syntax to ITT and ETT *)

Set Primitive Projections.

Record pp_sigT {A : Type} (P : A -> Type) : Type :=
  {
    pi1 : A;
    pi2 : P pi1
  }.

(* Preamble *)
Notation "'∑'  x .. y , P" := (pp_sigT (fun x => .. (pp_sigT (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity) : type_scope.

Record pp_prod (A B : Type) : Type := mk_pp_prod
  {
    pi1_ : A;
    pi2_ : B
  }.

Arguments mk_pp_prod {_ _} _ _.


Notation "x * y" := (pp_prod x y) : type_scope.

Definition fst {A B} (p : A * B) := pi1_ A B p.
Definition snd {A B} (p : A * B) := pi2_ A B p.

Notation "( x , y , .. , z )" := (mk_pp_prod .. (mk_pp_prod x y) .. z) : type_scope.

Definition on_fst {A B A'} (f : A -> A') (x : A * B) : A' * B :=
  let '(u,v) := x in (f u, v).

Definition on_snd {A B B'} (f : B -> B') (x : A * B) : A * B' :=
  let '(u,v) := x in (u, f v).

From Template Require Import Ast.

Definition sort := nat.

Inductive sterm : Type :=
| sRel (n : nat)
| sSort (s : sort)
| sProd (nx : name) (A B : sterm)
| sLambda (nx : name) (A B t : sterm)
| sApp (u : sterm) (nx : name) (A B v : sterm)
(* Homogenous equality *)
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
(* Inductives *)
| sInd (ind : inductive)
| sConstruct (ind : inductive) (n : nat)
| sCase (indn : inductive * nat) (p c : sterm) (brs : list (nat * sterm))
.