From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import Ast IAst Typing ILiftSubst.

Record context_decl := { decl_name : name ;
                         decl_body : option iterm ;
                         decl_type : iterm }.

Definition vass x A := {| decl_name := x; decl_body := None; decl_type := A |}.
Definition vdef x t A :=
  {| decl_name := x; decl_body := Some t; decl_type := A |}.

Definition context := (list context_decl).

Definition snoc (Γ : context) (d : context_decl) := d :: Γ.

Notation " Γ ,, d " := (snoc Γ d) (at level 20, d at next level) : i_scope.

Reserved Notation " Σ ;;; Γ |-- t : T " (at level 50, Γ, t, T at next level).
Reserved Notation " Σ ;;; Γ |-- t = u : T " (at level 50, Γ, t, u, T at next level).

Record squash (A : Set) : Prop := { _ : A }.

Inductive typing (Σ : global_context) (Γ : context) : iterm -> iterm -> Set :=
| type_Rel n : forall (isdecl : n < List.length Γ),
    Σ ;;; Γ |-- (iRel n) : lift0 (S n) (safe_nth Γ (exist _ n isdecl)).(decl_type)

| type_Sort s :
    Σ ;;; Γ |-- (iSort s) : iSort (succ_sort s)

| type_Prod n t b s1 s2 :
    Σ ;;; Γ |-- t : iSort s1 ->
    Σ ;;; Γ ,, vass n t |-- b : iSort s2 ->
    Σ ;;; Γ |-- (iProd n t b) : iSort (max_sort s1 s2)

| type_Lambda n n' t b s1 s2 bty :
    Σ ;;; Γ |-- t : iSort s1 ->
    Σ ;;; Γ ,, vass n t |-- bty : iSort s2 ->
    Σ ;;; Γ ,, vass n t |-- b : bty ->
    Σ ;;; Γ |-- (iLambda n t bty b) : iProd n' t bty

| type_App n s1 s2 t A B u :
    Σ ;;; Γ |-- A : iSort s1 ->
    Σ ;;; Γ ,, vass n A |-- B : s2 ->
    Σ ;;; Γ |-- t : iProd n A B ->
    Σ ;;; Γ |-- u : A ->
    Σ ;;; Γ |-- (iApp t n A B u) : B{ 0 := u }

| type_Eq s A u v :
    Σ ;;; Γ |-- A : iSort s ->
    Σ ;;; Γ |-- u : A ->
    Σ ;;; Γ |-- v : A ->
    Σ ;;; Γ |-- iEq s A u v : iSort s

| type_Refl s A u :
    Σ ;;; Γ |-- A : iSort s ->
    Σ ;;; Γ |-- u : A ->
    Σ ;;; Γ |-- iRefl A u : iEq s A u u

| type_Conv t A B s :
    Σ ;;; Γ |-- t : A ->
    Σ ;;; Γ |-- B : iSort s ->
    Σ ;;; Γ |-- A = B : iSort s ->
    Σ ;;; Γ |-- t : B

where " Σ ;;; Γ |-- t : T " := (@typing Σ Γ t T) : i_scope

with eq_term (Σ : global_context) (Γ : context) : iterm -> iterm -> iterm -> Prop :=
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
    Σ ;;; Γ |-- A : iSort s1 ->
    Σ ;;; Γ ,, vass n A |-- B : iSort s2 ->
    Σ ;;; Γ ,, vass n A |-- t : B ->
    Σ ;;; Γ |-- u : A ->
    Σ ;;; Γ |-- iApp (iLambda n A B t) n A B u = t{ 0 := u } : B{ 0 := u }

| eq_conv s T1 T2 t1 t2 :
    Σ ;;; Γ |-- t1 = t2 : T1 ->
    Σ ;;; Γ |-- T1 = T2 : iSort s ->
    Σ ;;; Γ |-- t1 = t2 : T2

| cong_Prod n1 n2 A1 A2 B1 B2 s1 s2 :
    Σ ;;; Γ |-- A1 = A2 : iSort s1 ->
    Σ ;;; Γ ,, vass n1 A1 |-- B1 = B2 : iSort s2 ->
    Σ ;;; Γ |-- (iProd n1 A1 B1) = (iProd n2 A2 B2) : iSort (max_sort s1 s2)

| cong_Lambda n1 n2 n' A1 A2 B1 B2 t1 t2 s1 s2 :
    Σ ;;; Γ |-- A1 = A2 : iSort s1 ->
    Σ ;;; Γ ,, vass n1 A1 |-- B1 = B2 : iSort s2 ->
    Σ ;;; Γ ,, vass n1 A1 |-- t1 = t2 : B1 ->
    Σ ;;; Γ |-- (iLambda n1 A1 B1 t1) = (iLambda n2 A2 B2 t2) : iProd n' A1 B1

| cong_App n1 n2 s1 s2 t1 t2 A1 A2 B1 B2 u1 u2 :
    Σ ;;; Γ |-- A1 = A2 : iSort s1 ->
    Σ ;;; Γ ,, vass n1 A1 |-- B1 = B2 : s2 ->
    Σ ;;; Γ |-- t1 = t2 : iProd n1 A1 B1 ->
    Σ ;;; Γ |-- u1 = u2 : A1 ->
    Σ ;;; Γ |-- (iApp t1 n1 A1 B1 u1) = (iApp t2 n2 A2 B2 u2) : B1{ 0 := u1 }

| cong_Eq s A1 A2 u1 u2 v1 v2 :
    Σ ;;; Γ |-- A1 = A2 : iSort s ->
    Σ ;;; Γ |-- u1 = u2 : A1 ->
    Σ ;;; Γ |-- v1 = v2 : A1 ->
    Σ ;;; Γ |-- iEq s A1 u1 v1 = iEq s A2 u2 v2 : iSort s

| cong_Refl s A1 A2 u1 u2 :
    Σ ;;; Γ |-- A1 = A2 : iSort s ->
    Σ ;;; Γ |-- u1 = u2 : A1 ->
    Σ ;;; Γ |-- iRefl A1 u1 = iRefl A2 u2 : iEq s A1 u1 u1

where " Σ ;;; Γ |-- t = u : T " := (@eq_term Σ Γ t u T) : i_scope.