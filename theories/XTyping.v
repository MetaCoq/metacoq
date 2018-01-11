From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import Ast SAst Typing SLiftSubst SCommon.

Reserved Notation " Σ ;;; Γ |-- t : T " (at level 50, Γ, t, T at next level).
Reserved Notation " Σ ;;; Γ |-- t = u : T " (at level 50, Γ, t, u, T at next level).

Open Scope s_scope.

Inductive typing (Σ : global_context) (Γ : context) : sterm -> sterm -> Set :=
| type_Rel n : forall (isdecl : n < List.length Γ),
    Σ ;;; Γ |-- (sRel n) : lift0 (S n) (safe_nth Γ (exist _ n isdecl)).(decl_type)

| type_Sort s :
    Σ ;;; Γ |-- (sSort s) : sSort (succ_sort s)

| type_Prod n t b s1 s2 :
    Σ ;;; Γ |-- t : sSort s1 ->
    Σ ;;; Γ ,, vass n t |-- b : sSort s2 ->
    Σ ;;; Γ |-- (sProd n t b) : sSort (max_sort s1 s2)

| type_Lambda n n' t b s1 s2 bty :
    Σ ;;; Γ |-- t : sSort s1 ->
    Σ ;;; Γ ,, vass n t |-- bty : sSort s2 ->
    Σ ;;; Γ ,, vass n t |-- b : bty ->
    Σ ;;; Γ |-- (sLambda n t bty b) : sProd n' t bty

| type_App n s1 s2 t A B u :
    Σ ;;; Γ |-- A : sSort s1 ->
    Σ ;;; Γ ,, vass n A |-- B : sSort s2 ->
    Σ ;;; Γ |-- t : sProd n A B ->
    Σ ;;; Γ |-- u : A ->
    Σ ;;; Γ |-- (sApp t n A B u) : B{ 0 := u }

| type_Eq s A u v :
    Σ ;;; Γ |-- A : sSort s ->
    Σ ;;; Γ |-- u : A ->
    Σ ;;; Γ |-- v : A ->
    Σ ;;; Γ |-- sEq s A u v : sSort s

| type_Refl s A u :
    Σ ;;; Γ |-- A : sSort s ->
    Σ ;;; Γ |-- u : A ->
    Σ ;;; Γ |-- sRefl A u : sEq s A u u

| type_Conv t A B s :
    Σ ;;; Γ |-- t : A ->
    Σ ;;; Γ |-- B : sSort s ->
    Σ ;;; Γ |-- A = B : sSort s ->
    Σ ;;; Γ |-- t : B

where " Σ ;;; Γ |-- t : T " := (@typing Σ Γ t T) : x_scope

with eq_term (Σ : global_context) (Γ : context) : sterm -> sterm -> sterm -> Prop :=
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
    Σ ;;; Γ |-- A : sSort s1 ->
    Σ ;;; Γ ,, vass n A |-- B : sSort s2 ->
    Σ ;;; Γ ,, vass n A |-- t : B ->
    Σ ;;; Γ |-- u : A ->
    Σ ;;; Γ |-- sApp (sLambda n A B t) n A B u = t{ 0 := u } : B{ 0 := u }

| eq_conv s T1 T2 t1 t2 :
    Σ ;;; Γ |-- t1 = t2 : T1 ->
    Σ ;;; Γ |-- T1 = T2 : sSort s ->
    Σ ;;; Γ |-- t1 = t2 : T2

| cong_Prod n1 n2 A1 A2 B1 B2 s1 s2 :
    Σ ;;; Γ |-- A1 = A2 : sSort s1 ->
    Σ ;;; Γ ,, vass n1 A1 |-- B1 = B2 : sSort s2 ->
    Σ ;;; Γ |-- (sProd n1 A1 B1) = (sProd n2 A2 B2) : sSort (max_sort s1 s2)

| cong_Lambda n1 n2 n' A1 A2 B1 B2 t1 t2 s1 s2 :
    Σ ;;; Γ |-- A1 = A2 : sSort s1 ->
    Σ ;;; Γ ,, vass n1 A1 |-- B1 = B2 : sSort s2 ->
    Σ ;;; Γ ,, vass n1 A1 |-- t1 = t2 : B1 ->
    Σ ;;; Γ |-- (sLambda n1 A1 B1 t1) = (sLambda n2 A2 B2 t2) : sProd n' A1 B1

| cong_App n1 n2 s1 s2 t1 t2 A1 A2 B1 B2 u1 u2 :
    Σ ;;; Γ |-- A1 = A2 : sSort s1 ->
    Σ ;;; Γ ,, vass n1 A1 |-- B1 = B2 : sSort s2 ->
    Σ ;;; Γ |-- t1 = t2 : sProd n1 A1 B1 ->
    Σ ;;; Γ |-- u1 = u2 : A1 ->
    Σ ;;; Γ |-- (sApp t1 n1 A1 B1 u1) = (sApp t2 n2 A2 B2 u2) : B1{ 0 := u1 }

| cong_Eq s A1 A2 u1 u2 v1 v2 :
    Σ ;;; Γ |-- A1 = A2 : sSort s ->
    Σ ;;; Γ |-- u1 = u2 : A1 ->
    Σ ;;; Γ |-- v1 = v2 : A1 ->
    Σ ;;; Γ |-- sEq s A1 u1 v1 = sEq s A2 u2 v2 : sSort s

| cong_Refl s A1 A2 u1 u2 :
    Σ ;;; Γ |-- A1 = A2 : sSort s ->
    Σ ;;; Γ |-- u1 = u2 : A1 ->
    Σ ;;; Γ |-- sRefl A1 u1 = sRefl A2 u2 : sEq s A1 u1 u1

| reflection s A u v e :
    Σ ;;; Γ |-- e : sEq s A u v ->
    Σ ;;; Γ |-- u = v : A

where " Σ ;;; Γ |-- t = u : T " := (@eq_term Σ Γ t u T) : x_scope.