From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import Ast XAst Typing XLiftSubst.

Record context_decl := { decl_name : name ;
                         decl_body : option xterm ;
                         decl_type : xterm }.

Definition vass x A := {| decl_name := x; decl_body := None; decl_type := A |}.
Definition vdef x t A :=
  {| decl_name := x; decl_body := Some t; decl_type := A |}.

Definition context := (list context_decl).

Definition snoc (Γ : context) (d : context_decl) := d :: Γ.

Notation " Γ ,, d " := (snoc Γ d) (at level 20, d at next level) : x_scope.

Reserved Notation " Σ ;;; Γ |-- t : T " (at level 50, Γ, t, T at next level).
Reserved Notation " Σ ;;; Γ |-- t = u : T " (at level 50, Γ, t, u, T at next level).

Record squash (A : Set) : Prop := { _ : A }.

Inductive typing (Σ : global_context) (Γ : context) : xterm -> xterm -> Set :=
| type_Rel n : forall (isdecl : n < List.length Γ),
    Σ ;;; Γ |-- (xRel n) : lift0 (S n) (safe_nth Γ (exist _ n isdecl)).(decl_type)

| type_Sort s :
    Σ ;;; Γ |-- (xSort s) : xSort (succ_sort s)

| type_Prod n t b s1 s2 :
    Σ ;;; Γ |-- t : xSort s1 ->
    Σ ;;; Γ ,, vass n t |-- b : xSort s2 ->
    Σ ;;; Γ |-- (xProd n t b) : xSort (max_sort s1 s2)

| type_Lambda n n' t b s1 s2 bty :
    Σ ;;; Γ |-- t : xSort s1 ->
    Σ ;;; Γ ,, vass n t |-- bty : xSort s2 ->
    Σ ;;; Γ ,, vass n t |-- b : bty ->
    Σ ;;; Γ |-- (xLambda n t bty b) : xProd n' t bty

| type_App n s1 s2 t A B u :
    Σ ;;; Γ |-- A : xSort s1 ->
    Σ ;;; Γ ,, vass n A |-- B : xSort s2 ->
    Σ ;;; Γ |-- t : xProd n A B ->
    Σ ;;; Γ |-- u : A ->
    Σ ;;; Γ |-- (xApp t n A B u) : B{ 0 := u }

| type_Eq s A u v :
    Σ ;;; Γ |-- A : xSort s ->
    Σ ;;; Γ |-- u : A ->
    Σ ;;; Γ |-- v : A ->
    Σ ;;; Γ |-- xEq s A u v : xSort s

| type_Refl s A u :
    Σ ;;; Γ |-- A : xSort s ->
    Σ ;;; Γ |-- u : A ->
    Σ ;;; Γ |-- xRefl A u : xEq s A u u

| type_Conv t A B s :
    Σ ;;; Γ |-- t : A ->
    Σ ;;; Γ |-- B : xSort s ->
    Σ ;;; Γ |-- A = B : xSort s ->
    Σ ;;; Γ |-- t : B

where " Σ ;;; Γ |-- t : T " := (@typing Σ Γ t T) : x_scope

with eq_term (Σ : global_context) (Γ : context) : xterm -> xterm -> xterm -> Prop :=
| eq_reflexivity u A :
    Σ ;;; Γ |-- u : A ->
    Σ ;;; Γ |-- u = u : A

| eq_symmetry u v A :
    Σ ;;; Γ |-- u = v : A ->
    Σ ;;; Γ |-- v = u : A

| eq_transitivity u v w A :
    Σ ;;; Γ |-- u = v : A ->
    Σ ;;; Γ |-- v = w : A ->
    Σ ;;; Γ |-- u = w : A

| eq_beta s1 s2 n A B t u :
    Σ ;;; Γ |-- A : xSort s1 ->
    Σ ;;; Γ ,, vass n A |-- B : xSort s2 ->
    Σ ;;; Γ ,, vass n A |-- t : B ->
    Σ ;;; Γ |-- u : A ->
    Σ ;;; Γ |-- xApp (xLambda n A B t) n A B u = t{ 0 := u } : B{ 0 := u }

| eq_conv s T1 T2 t1 t2 :
    Σ ;;; Γ |-- t1 = t2 : T1 ->
    Σ ;;; Γ |-- T1 = T2 : xSort s ->
    Σ ;;; Γ |-- t1 = t2 : T2

| cong_Prod n1 n2 A1 A2 B1 B2 s1 s2 :
    Σ ;;; Γ |-- A1 = A2 : xSort s1 ->
    Σ ;;; Γ ,, vass n1 A1 |-- B1 = B2 : xSort s2 ->
    Σ ;;; Γ |-- (xProd n1 A1 B1) = (xProd n2 A2 B2) : xSort (max_sort s1 s2)

| cong_Lambda n1 n2 n' A1 A2 B1 B2 t1 t2 s1 s2 :
    Σ ;;; Γ |-- A1 = A2 : xSort s1 ->
    Σ ;;; Γ ,, vass n1 A1 |-- B1 = B2 : xSort s2 ->
    Σ ;;; Γ ,, vass n1 A1 |-- t1 = t2 : B1 ->
    Σ ;;; Γ |-- (xLambda n1 A1 B1 t1) = (xLambda n2 A2 B2 t2) : xProd n' A1 B1

| cong_App n1 n2 s1 s2 t1 t2 A1 A2 B1 B2 u1 u2 :
    Σ ;;; Γ |-- A1 = A2 : xSort s1 ->
    Σ ;;; Γ ,, vass n1 A1 |-- B1 = B2 : xSort s2 ->
    Σ ;;; Γ |-- t1 = t2 : xProd n1 A1 B1 ->
    Σ ;;; Γ |-- u1 = u2 : A1 ->
    Σ ;;; Γ |-- (xApp t1 n1 A1 B1 u1) = (xApp t2 n2 A2 B2 u2) : B1{ 0 := u1 }

| cong_Eq s A1 A2 u1 u2 v1 v2 :
    Σ ;;; Γ |-- A1 = A2 : xSort s ->
    Σ ;;; Γ |-- u1 = u2 : A1 ->
    Σ ;;; Γ |-- v1 = v2 : A1 ->
    Σ ;;; Γ |-- xEq s A1 u1 v1 = xEq s A2 u2 v2 : xSort s

| cong_Refl s A1 A2 u1 u2 :
    Σ ;;; Γ |-- A1 = A2 : xSort s ->
    Σ ;;; Γ |-- u1 = u2 : A1 ->
    Σ ;;; Γ |-- xRefl A1 u1 = xRefl A2 u2 : xEq s A1 u1 u1

| reflection s A u v e :
    Σ ;;; Γ |-- e : xEq s A u v ->
    Σ ;;; Γ |-- u = v : A

where " Σ ;;; Γ |-- t = u : T " := (@eq_term Σ Γ t u T) : x_scope.