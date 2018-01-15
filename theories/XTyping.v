From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import Ast SAst Typing SLiftSubst SCommon.

Reserved Notation " Σ ;;; Γ '|-x' t : T " (at level 50, Γ, t, T at next level).
Reserved Notation " Σ ;;; Γ '|-x' t = u : T " (at level 50, Γ, t, u, T at next level).

Open Scope s_scope.

Inductive typing (Σ : global_context) (Γ : scontext) : sterm -> sterm -> Set :=
| type_Rel n : forall (isdecl : n < List.length Γ),
    Σ ;;; Γ |-x (sRel n) : lift0 (S n) (safe_nth Γ (exist _ n isdecl)).(sdecl_type)

| type_Sort s :
    Σ ;;; Γ |-x (sSort s) : sSort (succ_sort s)

| type_Prod n t b s1 s2 :
    Σ ;;; Γ |-x t : sSort s1 ->
    Σ ;;; Γ ,, svass n t |-x b : sSort s2 ->
    Σ ;;; Γ |-x (sProd n t b) : sSort (max_sort s1 s2)

| type_Lambda n n' t b s1 s2 bty :
    Σ ;;; Γ |-x t : sSort s1 ->
    Σ ;;; Γ ,, svass n t |-x bty : sSort s2 ->
    Σ ;;; Γ ,, svass n t |-x b : bty ->
    Σ ;;; Γ |-x (sLambda n t bty b) : sProd n' t bty

| type_App n s1 s2 t A B u :
    Σ ;;; Γ |-x A : sSort s1 ->
    Σ ;;; Γ ,, svass n A |-x B : sSort s2 ->
    Σ ;;; Γ |-x t : sProd n A B ->
    Σ ;;; Γ |-x u : A ->
    Σ ;;; Γ |-x (sApp t n A B u) : B{ 0 := u }

| type_Eq s A u v :
    Σ ;;; Γ |-x A : sSort s ->
    Σ ;;; Γ |-x u : A ->
    Σ ;;; Γ |-x v : A ->
    Σ ;;; Γ |-x sEq s A u v : sSort s

| type_Refl s A u :
    Σ ;;; Γ |-x A : sSort s ->
    Σ ;;; Γ |-x u : A ->
    Σ ;;; Γ |-x sRefl A u : sEq s A u u

| type_Conv t A B s :
    Σ ;;; Γ |-x t : A ->
    Σ ;;; Γ |-x B : sSort s ->
    Σ ;;; Γ |-x A = B : sSort s ->
    Σ ;;; Γ |-x t : B

where " Σ ;;; Γ '|-x' t : T " := (@typing Σ Γ t T) : x_scope

with eq_term (Σ : global_context) (Γ : scontext) : sterm -> sterm -> sterm -> Prop :=
| eq_reflexivity u A :
    Σ ;;; Γ |-x u : A ->
    Σ ;;; Γ |-x u = u : A

| eq_symmetry u v A :
    Σ ;;; Γ |-x u = v : A ->
    Σ ;;; Γ |-x v = u : A

| eq_transitivity u v w A :
    Σ ;;; Γ |-x u = v : A ->
    Σ ;;; Γ |-x v = w : A ->
    Σ ;;; Γ |-x u = w : A

| eq_beta s1 s2 n A B t u :
    Σ ;;; Γ |-x A : sSort s1 ->
    Σ ;;; Γ ,, svass n A |-x B : sSort s2 ->
    Σ ;;; Γ ,, svass n A |-x t : B ->
    Σ ;;; Γ |-x u : A ->
    Σ ;;; Γ |-x sApp (sLambda n A B t) n A B u = t{ 0 := u } : B{ 0 := u }

| eq_conv s T1 T2 t1 t2 :
    Σ ;;; Γ |-x t1 = t2 : T1 ->
    Σ ;;; Γ |-x T1 = T2 : sSort s ->
    Σ ;;; Γ |-x t1 = t2 : T2

| cong_Prod n1 n2 A1 A2 B1 B2 s1 s2 :
    Σ ;;; Γ |-x A1 = A2 : sSort s1 ->
    Σ ;;; Γ ,, svass n1 A1 |-x B1 = B2 : sSort s2 ->
    Σ ;;; Γ |-x (sProd n1 A1 B1) = (sProd n2 A2 B2) : sSort (max_sort s1 s2)

| cong_Lambda n1 n2 n' A1 A2 B1 B2 t1 t2 s1 s2 :
    Σ ;;; Γ |-x A1 = A2 : sSort s1 ->
    Σ ;;; Γ ,, svass n1 A1 |-x B1 = B2 : sSort s2 ->
    Σ ;;; Γ ,, svass n1 A1 |-x t1 = t2 : B1 ->
    Σ ;;; Γ |-x (sLambda n1 A1 B1 t1) = (sLambda n2 A2 B2 t2) : sProd n' A1 B1

| cong_App n1 n2 s1 s2 t1 t2 A1 A2 B1 B2 u1 u2 :
    Σ ;;; Γ |-x A1 = A2 : sSort s1 ->
    Σ ;;; Γ ,, svass n1 A1 |-x B1 = B2 : sSort s2 ->
    Σ ;;; Γ |-x t1 = t2 : sProd n1 A1 B1 ->
    Σ ;;; Γ |-x u1 = u2 : A1 ->
    Σ ;;; Γ |-x (sApp t1 n1 A1 B1 u1) = (sApp t2 n2 A2 B2 u2) : B1{ 0 := u1 }

| cong_Eq s A1 A2 u1 u2 v1 v2 :
    Σ ;;; Γ |-x A1 = A2 : sSort s ->
    Σ ;;; Γ |-x u1 = u2 : A1 ->
    Σ ;;; Γ |-x v1 = v2 : A1 ->
    Σ ;;; Γ |-x sEq s A1 u1 v1 = sEq s A2 u2 v2 : sSort s

| cong_Refl s A1 A2 u1 u2 :
    Σ ;;; Γ |-x A1 = A2 : sSort s ->
    Σ ;;; Γ |-x u1 = u2 : A1 ->
    Σ ;;; Γ |-x sRefl A1 u1 = sRefl A2 u2 : sEq s A1 u1 u1

| reflection s A u v e :
    Σ ;;; Γ |-x e : sEq s A u v ->
    Σ ;;; Γ |-x u = v : A

where " Σ ;;; Γ '|-x' t = u : T " := (@eq_term Σ Γ t u T) : x_scope.