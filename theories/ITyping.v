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

(* Maybe it would be easier to go for inductives *)
| type_J nx ne s1 s2 A u v P p w :
    Σ ;;; Γ |-- A : sSort s1 ->
    Σ ;;; Γ |-- u : A ->
    Σ ;;; Γ |-- v : A ->
    Σ ;;; Γ ,, vass nx A ,, vass ne (sEq s1 A u (sRel 0)) |-- P : sSort s2 ->
    Σ ;;; Γ |-- p : sEq s1 A u v ->
    Σ ;;; Γ |-- w : P{ 1 := u }{ 0 := sRefl A u }

| type_Uip s A u v p q :
    Σ ;;; Γ |-- p : sEq s A u v ->
    Σ ;;; Γ |-- q : sEq s A u v ->
    Σ ;;; Γ |-- sUip A u v p q : sEq s (sEq s A u v) p q

| type_Funext s n1 n2 n3 A B f g e :
    Σ ;;; Γ |-- f : sProd n1 A B ->
    Σ ;;; Γ |-- g : sProd n2 A B ->
    Σ ;;; Γ |-- e : sProd n3 A (sEq s B (sApp (lift0 1 f) n1 (lift0 1 A) (lift 1 1 B) (sRel 0)) (sApp (lift0 1 g) n2 (lift0 1 A) (lift 1 1 B) (sRel 0))) ->
    Σ ;;; Γ |-- sFunext A B f g e : sEq s (sProd n1 A B) f g

| type_Sig n t b s1 s2 :
    Σ ;;; Γ |-- t : sSort s1 ->
    Σ ;;; Γ ,, vass n t |-- b : sSort s2 ->
    Σ ;;; Γ |-- (sSig n t b) : sSort (max_sort s1 s2)

| type_Pair s1 s2 n A B u v :
    Σ ;;; Γ |-- A : sSort s1 ->
    Σ ;;; Γ ,, vass n A |-- B : sSort s2 ->
    Σ ;;; Γ |-- u : A ->
    Σ ;;; Γ |-- v : B{ 0 := u } ->
    Σ ;;; Γ |-- sPair A B u v : sSig n A B

| type_SigLet s1 s2 s3 n np nx ny A B P p t :
    Σ ;;; Γ |-- A : sSort s1 ->
    Σ ;;; Γ ,, vass n A |-- B : sSort s2 ->
    Σ ;;; Γ |-- p : sSig n A B ->
    Σ ;;; Γ ,, vass np (sSig n A B) |-- P : sSort s3 ->
    Σ ;;; Γ ,, vass nx A ,, vass ny B  |-- t : P{ 0 := sPair A B (sRel 1) (sRel 0) } ->
    Σ ;;; Γ |-- sSigLet A B P p t : P{ 0 := p }

| type_Conv t A B s :
    Σ ;;; Γ |-- t : A ->
    Σ ;;; Γ |-- B : sSort s ->
    Σ ;;; Γ |-- A = B : sSort s ->
    Σ ;;; Γ |-- t : B

where " Σ ;;; Γ |-- t : T " := (@typing Σ Γ t T) : i_scope

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

| cong_J nx ne s1 s2 A1 A2 u1 u2 v1 v2 P1 P2 p1 p2 w1 w2 :
    Σ ;;; Γ |-- A1 = A2 : sSort s1 ->
    Σ ;;; Γ |-- u1 = u2 : A1 ->
    Σ ;;; Γ |-- v1 = v2 : A1 ->
    Σ ;;; Γ ,, vass nx A1 ,, vass ne (sEq s1 A1 u1 (sRel 0)) |-- P1 = P2 : sSort s2 ->
    Σ ;;; Γ |-- p1 = p2 : sEq s1 A1 u1 v1 ->
    Σ ;;; Γ |-- w1 = w2 : P1{ 1 := u1 }{ 0 := sRefl A1 u1 }

| cong_Uip s A1 A2 u1 u2 v1 v2 p1 p2 q1 q2 :
    Σ ;;; Γ |-- p1 = p2 : sEq s A1 u1 v1 ->
    Σ ;;; Γ |-- q1 = q2 : sEq s A1 u1 v1 ->
    Σ ;;; Γ |-- sUip A1 u1 v1 p1 q1 = sUip A2 u2 v2 p2 q2 : sEq s (sEq s A1 u1 v1) p1 q1

| cong_Funext s n1 n2 n3 A1 A2 B1 B2 f1 f2 g1 g2 e1 e2 :
    Σ ;;; Γ |-- f1 = f2 : sProd n1 A1 B1 ->
    Σ ;;; Γ |-- g1 = g2 : sProd n2 A1 B1 ->
    Σ ;;; Γ |-- e1 = e2 : sProd n3 A1 (sEq s B1 (sApp (lift0 1 f1) n1 (lift0 1 A1) (lift 1 1 B1) (sRel 0)) (sApp (lift0 1 g1) n2 (lift0 1 A1) (lift 1 1 B1) (sRel 0))) ->
    Σ ;;; Γ |-- sFunext A1 B1 f1 g1 e1 = sFunext A2 B2 f2 g2 e2 : sEq s (sProd n1 A1 B1) f1 g1

| cong_Sig n n' A1 A2 B1 B2 s1 s2 :
    Σ ;;; Γ |-- A1 = A2 : sSort s1 ->
    Σ ;;; Γ ,, vass n A1 |-- B1 = B2 : sSort s2 ->
    Σ ;;; Γ |-- sSig n A1 B1 = sSig n' A2 B2 : sSort (max_sort s1 s2)

| cong_Pair s1 s2 n A1 A2 B1 B2 u1 u2 v1 v2 :
    Σ ;;; Γ |-- A1 = A2 : sSort s1 ->
    Σ ;;; Γ ,, vass n A1 |-- B1 = B2 : sSort s2 ->
    Σ ;;; Γ |-- u1 = u2 : A1 ->
    Σ ;;; Γ |-- v1 = v2 : B1{ 0 := u1 } ->
    Σ ;;; Γ |-- sPair A1 B1 u1 v1 = sPair A2 B2 u2 v2 : sSig n A1 B1

| cong_SigLet s1 s2 s3 n np nx ny A1 A2 B1 B2 P1 P2 p1 p2 t1 t2 :
    Σ ;;; Γ |-- A1 = A2 : sSort s1 ->
    Σ ;;; Γ ,, vass n A1 |-- B1 = B2 : sSort s2 ->
    Σ ;;; Γ |-- p1 = p2 : sSig n A1 B1 ->
    Σ ;;; Γ ,, vass np (sSig n A1 B1) |-- P1 = P2 : sSort s3 ->
    Σ ;;; Γ ,, vass nx A1 ,, vass ny B1  |-- t1 = t2 : P1{ 0 := sPair A1 B1 (sRel 1) (sRel 0) } ->
    Σ ;;; Γ |-- sSigLet A1 B1 P1 p1 t1 = sSigLet A2 B2 P2 p2 t2 : P1{ 0 := p1 }

where " Σ ;;; Γ |-- t = u : T " := (@eq_term Σ Γ t u T) : i_scope.