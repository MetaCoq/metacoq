From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import Ast SAst Typing SLiftSubst SCommon.

Reserved Notation " Σ ;;; Γ '|-i' t : T " (at level 50, Γ, t, T at next level).
Reserved Notation " Σ ;;; Γ '|-i' t = u : T " (at level 50, Γ, t, u, T at next level).

Open Scope s_scope.

Inductive typing (Σ : global_context) (Γ : scontext) : sterm -> sterm -> Set :=
| type_Rel n : forall (isdecl : n < List.length Γ),
    Σ ;;; Γ |-i (sRel n) : lift0 (S n) (safe_nth Γ (exist _ n isdecl)).(decl_type)

| type_Sort s :
    Σ ;;; Γ |-i (sSort s) : sSort (succ_sort s)

| type_Prod n t b s1 s2 :
    Σ ;;; Γ |-i t : sSort s1 ->
    Σ ;;; Γ ,, svass n t |-i b : sSort s2 ->
    Σ ;;; Γ |-i (sProd n t b) : sSort (max_sort s1 s2)

| type_Lambda n n' t b s1 s2 bty :
    Σ ;;; Γ |-i t : sSort s1 ->
    Σ ;;; Γ ,, svass n t |-i bty : sSort s2 ->
    Σ ;;; Γ ,, svass n t |-i b : bty ->
    Σ ;;; Γ |-i (sLambda n t bty b) : sProd n' t bty

| type_App n s1 s2 t A B u :
    Σ ;;; Γ |-i A : sSort s1 ->
    Σ ;;; Γ ,, svass n A |-i B : sSort s2 ->
    Σ ;;; Γ |-i t : sProd n A B ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i (sApp t n A B u) : B{ 0 := u }

| type_Eq s A u v :
    Σ ;;; Γ |-i A : sSort s ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i v : A ->
    Σ ;;; Γ |-i sEq s A u v : sSort s

| type_Refl s A u :
    Σ ;;; Γ |-i A : sSort s ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i sRefl A u : sEq s A u u

(* Maybe it would be easier to go for inductives *)
| type_J nx ne s1 s2 A u v P p w :
    Σ ;;; Γ |-i A : sSort s1 ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i v : A ->
    Σ ;;; Γ ,, svass nx A ,, svass ne (sEq s1 A u (sRel 0)) |-i P : sSort s2 ->
    Σ ;;; Γ |-i p : sEq s1 A u v ->
    Σ ;;; Γ |-i w : P{ 1 := u }{ 0 := sRefl A u } ->
    Σ ;;; Γ |-i sJ A u P w v p : P{ 1 := v }{ 0 := p }

| type_Uip s A u v p q :
    Σ ;;; Γ |-i p : sEq s A u v ->
    Σ ;;; Γ |-i q : sEq s A u v ->
    Σ ;;; Γ |-i sUip A u v p q : sEq s (sEq s A u v) p q

| type_Funext s n1 n2 n3 A B f g e :
    Σ ;;; Γ |-i f : sProd n1 A B ->
    Σ ;;; Γ |-i g : sProd n2 A B ->
    Σ ;;; Γ |-i e : sProd n3 A (sEq s B (sApp (lift0 1 f) n1 (lift0 1 A) (lift 1 1 B) (sRel 0)) (sApp (lift0 1 g) n2 (lift0 1 A) (lift 1 1 B) (sRel 0))) ->
    Σ ;;; Γ |-i sFunext A B f g e : sEq s (sProd n1 A B) f g

| type_Sig n t b s1 s2 :
    Σ ;;; Γ |-i t : sSort s1 ->
    Σ ;;; Γ ,, svass n t |-i b : sSort s2 ->
    Σ ;;; Γ |-i (sSig n t b) : sSort (max_sort s1 s2)

| type_Pair s1 s2 n A B u v :
    Σ ;;; Γ |-i A : sSort s1 ->
    Σ ;;; Γ ,, svass n A |-i B : sSort s2 ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i v : B{ 0 := u } ->
    Σ ;;; Γ |-i sPair A B u v : sSig n A B

| type_SigLet s1 s2 s3 n np nx ny A B P p t :
    Σ ;;; Γ |-i A : sSort s1 ->
    Σ ;;; Γ ,, svass n A |-i B : sSort s2 ->
    Σ ;;; Γ |-i p : sSig n A B ->
    Σ ;;; Γ ,, svass np (sSig n A B) |-i P : sSort s3 ->
    Σ ;;; Γ ,, svass nx A ,, svass ny B  |-i t : P{ 0 := sPair A B (sRel 1) (sRel 0) } ->
    Σ ;;; Γ |-i sSigLet A B P p t : P{ 0 := p }

| type_Conv t A B s :
    Σ ;;; Γ |-i t : A ->
    Σ ;;; Γ |-i B : sSort s ->
    Σ ;;; Γ |-i A = B : sSort s ->
    Σ ;;; Γ |-i t : B

where " Σ ;;; Γ '|-i' t : T " := (@typing Σ Γ t T) : i_scope

with eq_term (Σ : global_context) (Γ : scontext) : sterm -> sterm -> sterm -> Prop :=
| eq_reflexivity u A :
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i u = u : A

| eq_symmetry u v A :
    Σ ;;; Γ |-i u = v : A ->
    Σ ;;; Γ |-i v = u : A

| eq_transitivity u v w A :
    Σ ;;; Γ |-i u = v : A ->
    Σ ;;; Γ |-i v = w : A ->
    Σ ;;; Γ |-i u = w : A

| eq_beta s1 s2 n A B t u :
    Σ ;;; Γ |-i A : sSort s1 ->
    Σ ;;; Γ ,, svass n A |-i B : sSort s2 ->
    Σ ;;; Γ ,, svass n A |-i t : B ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i sApp (sLambda n A B t) n A B u = t{ 0 := u } : B{ 0 := u }

| eq_JRefl nx ne s1 s2 A u P w :
    Σ ;;; Γ |-i A : sSort s1 ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ ,, svass nx A ,, svass ne (sEq s1 A u (sRel 0)) |-i P : sSort s2 ->
    Σ ;;; Γ |-i w : P{ 1 := u }{ 0 := sRefl A u } ->
    Σ ;;; Γ |-i sJ A u P w u (sRefl A u) = w : P{ 1 := u }{ 0 := sRefl A u }

| eq_conv s T1 T2 t1 t2 :
    Σ ;;; Γ |-i t1 = t2 : T1 ->
    Σ ;;; Γ |-i T1 = T2 : sSort s ->
    Σ ;;; Γ |-i t1 = t2 : T2

| cong_Prod n1 n2 A1 A2 B1 B2 s1 s2 :
    Σ ;;; Γ |-i A1 = A2 : sSort s1 ->
    Σ ;;; Γ ,, svass n1 A1 |-i B1 = B2 : sSort s2 ->
    Σ ;;; Γ |-i (sProd n1 A1 B1) = (sProd n2 A2 B2) : sSort (max_sort s1 s2)

| cong_Lambda n1 n2 n' A1 A2 B1 B2 t1 t2 s1 s2 :
    Σ ;;; Γ |-i A1 = A2 : sSort s1 ->
    Σ ;;; Γ ,, svass n1 A1 |-i B1 = B2 : sSort s2 ->
    Σ ;;; Γ ,, svass n1 A1 |-i t1 = t2 : B1 ->
    Σ ;;; Γ |-i (sLambda n1 A1 B1 t1) = (sLambda n2 A2 B2 t2) : sProd n' A1 B1

| cong_App n1 n2 s1 s2 t1 t2 A1 A2 B1 B2 u1 u2 :
    Σ ;;; Γ |-i A1 = A2 : sSort s1 ->
    Σ ;;; Γ ,, svass n1 A1 |-i B1 = B2 : sSort s2 ->
    Σ ;;; Γ |-i t1 = t2 : sProd n1 A1 B1 ->
    Σ ;;; Γ |-i u1 = u2 : A1 ->
    Σ ;;; Γ |-i (sApp t1 n1 A1 B1 u1) = (sApp t2 n2 A2 B2 u2) : B1{ 0 := u1 }

| cong_Eq s A1 A2 u1 u2 v1 v2 :
    Σ ;;; Γ |-i A1 = A2 : sSort s ->
    Σ ;;; Γ |-i u1 = u2 : A1 ->
    Σ ;;; Γ |-i v1 = v2 : A1 ->
    Σ ;;; Γ |-i sEq s A1 u1 v1 = sEq s A2 u2 v2 : sSort s

| cong_Refl s A1 A2 u1 u2 :
    Σ ;;; Γ |-i A1 = A2 : sSort s ->
    Σ ;;; Γ |-i u1 = u2 : A1 ->
    Σ ;;; Γ |-i sRefl A1 u1 = sRefl A2 u2 : sEq s A1 u1 u1

| cong_J nx ne s1 s2 A1 A2 u1 u2 v1 v2 P1 P2 p1 p2 w1 w2 :
    Σ ;;; Γ |-i A1 = A2 : sSort s1 ->
    Σ ;;; Γ |-i u1 = u2 : A1 ->
    Σ ;;; Γ |-i v1 = v2 : A1 ->
    Σ ;;; Γ ,, svass nx A1 ,, svass ne (sEq s1 A1 u1 (sRel 0)) |-i P1 = P2 : sSort s2 ->
    Σ ;;; Γ |-i p1 = p2 : sEq s1 A1 u1 v1 ->
    Σ ;;; Γ |-i w1 = w2 : P1{ 1 := u1 }{ 0 := sRefl A1 u1 } ->
    Σ ;;; Γ |-i sJ A1 u1 P1 w1 v1 p1 = sJ A2 u2 P2 w2 v2 p2 : P1{ 1 := v1 }{ 0 := p1 }

| cong_Uip s A1 A2 u1 u2 v1 v2 p1 p2 q1 q2 :
    Σ ;;; Γ |-i p1 = p2 : sEq s A1 u1 v1 ->
    Σ ;;; Γ |-i q1 = q2 : sEq s A1 u1 v1 ->
    Σ ;;; Γ |-i sUip A1 u1 v1 p1 q1 = sUip A2 u2 v2 p2 q2 : sEq s (sEq s A1 u1 v1) p1 q1

| cong_Funext s n1 n2 n3 A1 A2 B1 B2 f1 f2 g1 g2 e1 e2 :
    Σ ;;; Γ |-i f1 = f2 : sProd n1 A1 B1 ->
    Σ ;;; Γ |-i g1 = g2 : sProd n2 A1 B1 ->
    Σ ;;; Γ |-i e1 = e2 : sProd n3 A1 (sEq s B1 (sApp (lift0 1 f1) n1 (lift0 1 A1) (lift 1 1 B1) (sRel 0)) (sApp (lift0 1 g1) n2 (lift0 1 A1) (lift 1 1 B1) (sRel 0))) ->
    Σ ;;; Γ |-i sFunext A1 B1 f1 g1 e1 = sFunext A2 B2 f2 g2 e2 : sEq s (sProd n1 A1 B1) f1 g1

| cong_Sig n n' A1 A2 B1 B2 s1 s2 :
    Σ ;;; Γ |-i A1 = A2 : sSort s1 ->
    Σ ;;; Γ ,, svass n A1 |-i B1 = B2 : sSort s2 ->
    Σ ;;; Γ |-i sSig n A1 B1 = sSig n' A2 B2 : sSort (max_sort s1 s2)

| cong_Pair s1 s2 n A1 A2 B1 B2 u1 u2 v1 v2 :
    Σ ;;; Γ |-i A1 = A2 : sSort s1 ->
    Σ ;;; Γ ,, svass n A1 |-i B1 = B2 : sSort s2 ->
    Σ ;;; Γ |-i u1 = u2 : A1 ->
    Σ ;;; Γ |-i v1 = v2 : B1{ 0 := u1 } ->
    Σ ;;; Γ |-i sPair A1 B1 u1 v1 = sPair A2 B2 u2 v2 : sSig n A1 B1

| cong_SigLet s1 s2 s3 n np nx ny A1 A2 B1 B2 P1 P2 p1 p2 t1 t2 :
    Σ ;;; Γ |-i A1 = A2 : sSort s1 ->
    Σ ;;; Γ ,, svass n A1 |-i B1 = B2 : sSort s2 ->
    Σ ;;; Γ |-i p1 = p2 : sSig n A1 B1 ->
    Σ ;;; Γ ,, svass np (sSig n A1 B1) |-i P1 = P2 : sSort s3 ->
    Σ ;;; Γ ,, svass nx A1 ,, svass ny B1  |-i t1 = t2 : P1{ 0 := sPair A1 B1 (sRel 1) (sRel 0) } ->
    Σ ;;; Γ |-i sSigLet A1 B1 P1 p1 t1 = sSigLet A2 B2 P2 p2 t2 : P1{ 0 := p1 }

where " Σ ;;; Γ '|-i' t = u : T " := (@eq_term Σ Γ t u T) : i_scope.