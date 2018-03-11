From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast utils Typing.
From Translation Require Import SAst SLiftSubst SCommon.

Reserved Notation " Σ ;;; Γ '|-i' t : T " (at level 50, Γ, t, T at next level).
Reserved Notation " Σ ;;; Γ '|-i' t = u : T " (at level 50, Γ, t, u, T at next level).

Open Scope s_scope.

Inductive typing (Σ : sglobal_context) : scontext -> sterm -> sterm -> Type :=
| type_Rel Γ n :
    wf Σ Γ ->
    forall (isdecl : n < List.length Γ),
      Σ ;;; Γ |-i (sRel n) : lift0 (S n) (safe_nth Γ (exist _ n isdecl)).(sdecl_type)

| type_Sort Γ s :
    wf Σ Γ ->
    Σ ;;; Γ |-i (sSort s) : sSort (succ_sort s)

| type_Prod Γ n t b s1 s2 :
    Σ ;;; Γ |-i t : sSort s1 ->
    Σ ;;; Γ ,, svass n t |-i b : sSort s2 ->
    Σ ;;; Γ |-i (sProd n t b) : sSort (max_sort s1 s2)

| type_Lambda Γ n n' t b s1 s2 bty :
    Σ ;;; Γ |-i t : sSort s1 ->
    Σ ;;; Γ ,, svass n t |-i bty : sSort s2 ->
    Σ ;;; Γ ,, svass n t |-i b : bty ->
    Σ ;;; Γ |-i (sLambda n t bty b) : sProd n' t bty

| type_App Γ n s1 s2 t A B u :
    Σ ;;; Γ |-i A : sSort s1 ->
    Σ ;;; Γ ,, svass n A |-i B : sSort s2 ->
    Σ ;;; Γ |-i t : sProd n A B ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i (sApp t n A B u) : B{ 0 := u }

| type_Eq Γ s A u v :
    Σ ;;; Γ |-i A : sSort s ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i v : A ->
    Σ ;;; Γ |-i sEq A u v : sSort s

| type_Refl Γ s A u :
    Σ ;;; Γ |-i A : sSort s ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i sRefl A u : sEq A u u

| type_J Γ nx ne s1 s2 A u v P p w :
    Σ ;;; Γ |-i A : sSort s1 ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i v : A ->
    Σ ;;; Γ ,, svass nx A ,, svass ne (sEq (lift0 1 A) (lift0 1 u) (sRel 0)) |-i P : sSort s2 ->
    Σ ;;; Γ |-i p : sEq A u v ->
    Σ ;;; Γ |-i w : P{ 1 := u }{ 0 := sRefl A u } ->
    Σ ;;; Γ |-i sJ A u P w v p : P{ 1 := v }{ 0 := p }

| type_Transport Γ s T1 T2 p t :
    Σ ;;; Γ |-i T1 : sSort s ->
    Σ ;;; Γ |-i T2 : sSort s ->
    Σ ;;; Γ |-i p : sEq (sSort s) T1 T2 ->
    Σ ;;; Γ |-i t : T1 ->
    Σ ;;; Γ |-i sTransport T1 T2 p t : T2

| type_Heq Γ A a B b s :
    Σ ;;; Γ |-i A : sSort s ->
    Σ ;;; Γ |-i B : sSort s ->
    Σ ;;; Γ |-i a : A ->
    Σ ;;; Γ |-i b : B ->
    Σ ;;; Γ |-i sHeq A a B b : sSort (succ_sort s)

| type_HeqToEq Γ A u v p s :
    Σ ;;; Γ |-i p : sHeq A u A v ->
    Σ ;;; Γ |-i A : sSort s ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i v : A ->
    Σ ;;; Γ |-i sHeqToEq p : sEq A u v

| type_HeqRefl Γ A a s :
    Σ ;;; Γ |-i A : sSort s ->
    Σ ;;; Γ |-i a : A ->
    Σ ;;; Γ |-i sHeqRefl A a : sHeq A a A a

| type_HeqSym Γ A a B b p s :
    Σ ;;; Γ |-i A : sSort s ->
    Σ ;;; Γ |-i B : sSort s ->
    Σ ;;; Γ |-i a : A ->
    Σ ;;; Γ |-i b : B ->
    Σ ;;; Γ |-i p : sHeq A a B b ->
    Σ ;;; Γ |-i sHeqSym p : sHeq B b A a

| type_HeqTrans Γ A a B b C c p q s :
    Σ ;;; Γ |-i A : sSort s ->
    Σ ;;; Γ |-i B : sSort s ->
    Σ ;;; Γ |-i C : sSort s ->
    Σ ;;; Γ |-i a : A ->
    Σ ;;; Γ |-i b : B ->
    Σ ;;; Γ |-i c : C ->
    Σ ;;; Γ |-i p : sHeq A a B b ->
    Σ ;;; Γ |-i q : sHeq B b C c ->
    Σ ;;; Γ |-i sHeqTrans p q : sHeq A a C c

| type_HeqTransport Γ A B p t s :
    Σ ;;; Γ |-i A : sSort s ->
    Σ ;;; Γ |-i B : sSort s ->
    Σ ;;; Γ |-i t : A ->
    Σ ;;; Γ |-i p : sEq (sSort s) A B ->
    Σ ;;; Γ |-i sHeqTransport p t : sHeq A t B (sTransport A B p t)

| type_CongProd Γ s z nx ny np A1 A2 B1 B2 pA pB :
    Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2 ->
    Σ ;;; Γ ,, svass np (sPack A1 A2)
    |-i pB : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                 (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ |-i A1 : sSort s ->
    Σ ;;; Γ |-i A2 : sSort s ->
    Σ ;;; Γ ,, svass nx A1 |-i B1 : sSort z ->
    Σ ;;; Γ ,, svass ny A2 |-i B2 : sSort z ->
    Σ ;;; Γ |-i sCongProd B1 B2 pA pB :
    sHeq (sSort (max_sort s z)) (sProd nx A1 B1)
         (sSort (max_sort s z)) (sProd ny A2 B2)

| type_CongLambda Γ s z nx ny np A1 A2 B1 B2 t1 t2 pA pB pt :
    Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2 ->
    Σ ;;; Γ ,, svass np (sPack A1 A2)
    |-i pB : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                 (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ ,, svass np (sPack A1 A2)
    |-i pt : sHeq ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                 ((lift 1 1 t1){ 0 := sProjT1 (sRel 0) })
                 ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) })
                 ((lift 1 1 t2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ |-i A1 : sSort s ->
    Σ ;;; Γ |-i A2 : sSort s ->
    Σ ;;; Γ ,, svass nx A1 |-i B1 : sSort z ->
    Σ ;;; Γ ,, svass ny A2 |-i B2 : sSort z ->
    Σ ;;; Γ ,, svass nx A1 |-i t1 : B1 ->
    Σ ;;; Γ ,, svass ny A2 |-i t2 : B2 ->
    Σ ;;; Γ |-i sCongLambda B1 B2 t1 t2 pA pB pt :
               sHeq (sProd nx A1 B1) (sLambda nx A1 B1 t1)
                    (sProd ny A2 B2) (sLambda ny A2 B2 t2)

| type_CongApp Γ s z nx ny np A1 A2 B1 B2 u1 u2 v1 v2 pA pB pu pv :
    Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2 ->
    Σ ;;; Γ ,, svass np (sPack A1 A2)
    |-i pB : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                 (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ |-i pu : sHeq (sProd nx A1 B1) u1 (sProd ny A2 B2) u2 ->
    Σ ;;; Γ |-i pv : sHeq A1 v1 A2 v2 ->
    Σ ;;; Γ |-i A1 : sSort s ->
    Σ ;;; Γ |-i A2 : sSort s ->
    Σ ;;; Γ ,, svass nx A1 |-i B1 : sSort z ->
    Σ ;;; Γ ,, svass ny A2 |-i B2 : sSort z ->
    Σ ;;; Γ |-i u1 : sProd nx A1 B1 ->
    Σ ;;; Γ |-i u2 : sProd ny A2 B2 ->
    Σ ;;; Γ |-i v1 : A1 ->
    Σ ;;; Γ |-i v2 : A2 ->
    Σ ;;; Γ |-i sCongApp B1 B2 pu pA pB pv :
               sHeq (B1{0 := v1}) (sApp u1 nx A1 B1 v1)
                    (B2{0 := v2}) (sApp u2 ny A2 B2 v2)

| type_CongEq Γ s A1 A2 u1 u2 v1 v2 pA pu pv :
    Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2 ->
    Σ ;;; Γ |-i pu : sHeq A1 u1 A2 u2 ->
    Σ ;;; Γ |-i pv : sHeq A1 v1 A2 v2 ->
    Σ ;;; Γ |-i A1 : sSort s ->
    Σ ;;; Γ |-i A2 : sSort s ->
    Σ ;;; Γ |-i u1 : A1 ->
    Σ ;;; Γ |-i u2 : A2 ->
    Σ ;;; Γ |-i v1 : A1 ->
    Σ ;;; Γ |-i v2 : A2 ->
    Σ ;;; Γ |-i sCongEq pA pu pv :
               sHeq (sSort s) (sEq A1 u1 v1) (sSort s) (sEq A2 u2 v2)

| type_CongRefl Γ s A1 A2 u1 u2 pA pu :
    Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2 ->
    Σ ;;; Γ |-i pu : sHeq A1 u1 A2 u2 ->
    Σ ;;; Γ |-i A1 : sSort s ->
    Σ ;;; Γ |-i A2 : sSort s ->
    Σ ;;; Γ |-i u1 : A1 ->
    Σ ;;; Γ |-i u2 : A2 ->
    Σ ;;; Γ |-i sCongRefl pA pu :
               sHeq (sEq A1 u1 u1) (sRefl A1 u1) (sEq A2 u2 u2) (sRefl A2 u2)

| type_EqToHeq Γ A u v p s :
    Σ ;;; Γ |-i p : sEq A u v ->
    Σ ;;; Γ |-i A : sSort s ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i v : A ->
    Σ ;;; Γ |-i sEqToHeq p : sHeq A u A v

| type_HeqTypeEq Γ A u B v p s :
    Σ ;;; Γ |-i p : sHeq A u B v ->
    Σ ;;; Γ |-i A : sSort s ->
    Σ ;;; Γ |-i B : sSort s ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i v : B ->
    Σ ;;; Γ |-i sHeqTypeEq p : sEq (sSort s) A B

| type_Pack Γ A1 A2 s :
    Σ ;;; Γ |-i A1 : sSort s ->
    Σ ;;; Γ |-i A2 : sSort s ->
    Σ ;;; Γ |-i sPack A1 A2 : sSort s

| type_ProjT1 Γ A1 A2 p s :
    Σ ;;; Γ |-i A1 : sSort s ->
    Σ ;;; Γ |-i A2 : sSort s ->
    Σ ;;; Γ |-i p : sPack A1 A2 ->
    Σ ;;; Γ |-i sProjT1 p : A1

| type_ProjT2 Γ A1 A2 p s :
    Σ ;;; Γ |-i A1 : sSort s ->
    Σ ;;; Γ |-i A2 : sSort s ->
    Σ ;;; Γ |-i p : sPack A1 A2 ->
    Σ ;;; Γ |-i sProjT2 p : A2

| type_ProjTe Γ A1 A2 p s :
    Σ ;;; Γ |-i A1 : sSort s ->
    Σ ;;; Γ |-i A2 : sSort s ->
    Σ ;;; Γ |-i p : sPack A1 A2 ->
    Σ ;;; Γ |-i sProjTe p : sHeq A1 (sProjT1 p) A2 (sProjT2 p)

| type_Ind Γ ind :
    wf Σ Γ ->
    forall univs decl (isdecl : sdeclared_inductive (fst Σ) ind univs decl),
      Σ ;;; Γ |-i sInd ind : decl.(sind_type)

| type_conv Γ t A B s :
    Σ ;;; Γ |-i t : A ->
    Σ ;;; Γ |-i B : sSort s ->
    Σ ;;; Γ |-i A = B : sSort s ->
    Σ ;;; Γ |-i t : B

where " Σ ;;; Γ '|-i' t : T " := (@typing Σ Γ t T) : i_scope

with wf (Σ : sglobal_context) : scontext -> Type :=
| wf_nil :
    wf Σ nil

| wf_snoc s Γ x A :
    wf Σ Γ ->
    Σ ;;; Γ |-i A : sSort s ->
    wf Σ (Γ ,, svass x A)

with eq_term (Σ : sglobal_context) : scontext -> sterm -> sterm -> sterm -> Type :=
| eq_reflexivity Γ u A :
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i u = u : A

| eq_symmetry Γ u v A :
    Σ ;;; Γ |-i u = v : A ->
    Σ ;;; Γ |-i v = u : A

| eq_transitivity Γ u v w A :
    Σ ;;; Γ |-i u = v : A ->
    Σ ;;; Γ |-i v = w : A ->
    Σ ;;; Γ |-i u = w : A

| eq_beta Γ s1 s2 n A B t u :
    Σ ;;; Γ |-i A : sSort s1 ->
    Σ ;;; Γ ,, svass n A |-i B : sSort s2 ->
    Σ ;;; Γ ,, svass n A |-i t : B ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i sApp (sLambda n A B t) n A B u = t{ 0 := u } : B{ 0 := u }

| eq_JRefl Γ nx ne s1 s2 A u P w :
    Σ ;;; Γ |-i A : sSort s1 ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ ,, svass nx A ,, svass ne (sEq (lift0 1 A) (lift0 1 u) (sRel 0)) |-i P : sSort s2 ->
    Σ ;;; Γ |-i w : P{ 1 := u }{ 0 := sRefl A u } ->
    Σ ;;; Γ |-i sJ A u P w u (sRefl A u) = w : P{ 1 := u }{ 0 := sRefl A u }

| eq_TransportRefl Γ s A t :
    Σ ;;; Γ |-i A : sSort s ->
    Σ ;;; Γ |-i t : A ->
    Σ ;;; Γ |-i sTransport A A (sRefl (sSort s) A) t = t : A

| eq_conv Γ s T1 T2 t1 t2 :
    Σ ;;; Γ |-i t1 = t2 : T1 ->
    Σ ;;; Γ |-i T1 = T2 : sSort s ->
    Σ ;;; Γ |-i t1 = t2 : T2

| cong_Prod Γ n1 n2 A1 A2 B1 B2 s1 s2 :
    Σ ;;; Γ |-i A1 = A2 : sSort s1 ->
    Σ ;;; Γ ,, svass n1 A1 |-i B1 = B2 : sSort s2 ->
    Σ ;;; Γ |-i (sProd n1 A1 B1) = (sProd n2 A2 B2) : sSort (max_sort s1 s2)

| cong_Lambda Γ n1 n2 n' A1 A2 B1 B2 t1 t2 s1 s2 :
    Σ ;;; Γ |-i A1 = A2 : sSort s1 ->
    Σ ;;; Γ ,, svass n1 A1 |-i B1 = B2 : sSort s2 ->
    Σ ;;; Γ ,, svass n1 A1 |-i t1 = t2 : B1 ->
    Σ ;;; Γ |-i (sLambda n1 A1 B1 t1) = (sLambda n2 A2 B2 t2) : sProd n' A1 B1

| cong_App Γ n1 n2 s1 s2 t1 t2 A1 A2 B1 B2 u1 u2 :
    Σ ;;; Γ |-i A1 = A2 : sSort s1 ->
    Σ ;;; Γ ,, svass n1 A1 |-i B1 = B2 : sSort s2 ->
    Σ ;;; Γ |-i t1 = t2 : sProd n1 A1 B1 ->
    Σ ;;; Γ |-i u1 = u2 : A1 ->
    Σ ;;; Γ |-i (sApp t1 n1 A1 B1 u1) = (sApp t2 n2 A2 B2 u2) : B1{ 0 := u1 }

| cong_Eq Γ s A1 A2 u1 u2 v1 v2 :
    Σ ;;; Γ |-i A1 = A2 : sSort s ->
    Σ ;;; Γ |-i u1 = u2 : A1 ->
    Σ ;;; Γ |-i v1 = v2 : A1 ->
    Σ ;;; Γ |-i sEq A1 u1 v1 = sEq A2 u2 v2 : sSort s

| cong_Refl Γ s A1 A2 u1 u2 :
    Σ ;;; Γ |-i A1 = A2 : sSort s ->
    Σ ;;; Γ |-i u1 = u2 : A1 ->
    Σ ;;; Γ |-i sRefl A1 u1 = sRefl A2 u2 : sEq A1 u1 u1

| cong_J Γ nx ne s1 s2 A1 A2 u1 u2 v1 v2 P1 P2 p1 p2 w1 w2 :
    Σ ;;; Γ |-i A1 = A2 : sSort s1 ->
    Σ ;;; Γ |-i u1 = u2 : A1 ->
    Σ ;;; Γ |-i v1 = v2 : A1 ->
    Σ ;;; Γ ,, svass nx A1 ,, svass ne (sEq (lift0 1 A1) (lift0 1 u1) (sRel 0)) |-i P1 = P2 : sSort s2 ->
    Σ ;;; Γ |-i p1 = p2 : sEq A1 u1 v1 ->
    Σ ;;; Γ |-i w1 = w2 : P1{ 1 := u1 }{ 0 := sRefl A1 u1 } ->
    Σ ;;; Γ |-i sJ A1 u1 P1 w1 v1 p1 = sJ A2 u2 P2 w2 v2 p2 : P1{ 1 := v1 }{ 0 := p1 }

| cong_Transport Γ s A1 A2 B1 B2 p1 p2 t1 t2 :
    Σ ;;; Γ |-i A1 = A2 : sSort s ->
    Σ ;;; Γ |-i B1 = B2 : sSort s ->
    Σ ;;; Γ |-i p1 = p2 : sEq (sSort s) A1 B1 ->
    Σ ;;; Γ |-i t1 = t2 : A1 ->
    Σ ;;; Γ |-i sTransport A1 B1 p1 t1 = sTransport A2 B2 p2 t2 : B1

| cong_Heq Γ A1 A2 a1 a2 B1 B2 b1 b2 s :
    Σ ;;; Γ |-i A1 = A2 : sSort s ->
    Σ ;;; Γ |-i B1 = B2 : sSort s ->
    Σ ;;; Γ |-i a1 = a2 : A1 ->
    Σ ;;; Γ |-i b1 = b2 : B1 ->
    Σ ;;; Γ |-i sHeq A1 a1 B1 b1 = sHeq A2 a2 B2 b2 : sSort (succ_sort s)

| cong_Pack Γ A1 B1 A2 B2 s :
    Σ ;;; Γ |-i A1 = B1 : sSort s ->
    Σ ;;; Γ |-i A2 = B2 : sSort s ->
    Σ ;;; Γ |-i sPack A1 A2 = sPack B1 B2 : sSort s

| cong_HeqToEq Γ A u v p1 p2 s :
    Σ ;;; Γ |-i p1 = p2 : sHeq A u A v ->
    Σ ;;; Γ |-i A : sSort s ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i v : A ->
    Σ ;;; Γ |-i sHeqToEq p1 = sHeqToEq p2 : sEq A u v

| cong_HeqRefl Γ A1 A2 a1 a2 s :
    Σ ;;; Γ |-i A1 = A2 : sSort s ->
    Σ ;;; Γ |-i a1 = a2 : A1 ->
    Σ ;;; Γ |-i sHeqRefl A1 a1 = sHeqRefl A2 a2 : sHeq A1 a1 A1 a1

| cong_HeqSym Γ A a B b p1 p2 s :
    Σ ;;; Γ |-i A : sSort s ->
    Σ ;;; Γ |-i B : sSort s ->
    Σ ;;; Γ |-i a : A ->
    Σ ;;; Γ |-i b : B ->
    Σ ;;; Γ |-i p1 = p2 : sHeq A a B b ->
    Σ ;;; Γ |-i sHeqSym p1 = sHeqSym p2 : sHeq B b A a

| cong_HeqTrans Γ A a B b C c p1 p2 q1 q2 s :
    Σ ;;; Γ |-i A : sSort s ->
    Σ ;;; Γ |-i B : sSort s ->
    Σ ;;; Γ |-i C : sSort s ->
    Σ ;;; Γ |-i a : A ->
    Σ ;;; Γ |-i b : B ->
    Σ ;;; Γ |-i c : C ->
    Σ ;;; Γ |-i p1 = p2 : sHeq A a B b ->
    Σ ;;; Γ |-i q1 = q2 : sHeq B b C c ->
    Σ ;;; Γ |-i sHeqTrans p1 q1 = sHeqTrans p2 q2 : sHeq A a C c

| cong_HeqTransport Γ A B p1 p2 t1 t2 s :
    Σ ;;; Γ |-i A : sSort s ->
    Σ ;;; Γ |-i B : sSort s ->
    Σ ;;; Γ |-i t1 = t2 : A ->
    Σ ;;; Γ |-i p1 = p2 : sEq (sSort s) A B ->
    Σ ;;; Γ |-i sHeqTransport p1 t1 = sHeqTransport p2 t2
             : sHeq A t1 B (sTransport A B p1 t1)

| cong_CongProd Γ s z nx ny np A1 A2 B1 B2 pA pB B1' B2' pA' pB' :
    Σ ;;; Γ |-i pA = pA' : sHeq (sSort s) A1 (sSort s) A2 ->
    Σ ;;; Γ ,, svass np (sPack A1 A2)
    |-i pB = pB' : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                       (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ |-i A1 : sSort s ->
    Σ ;;; Γ |-i A2 : sSort s ->
    Σ ;;; Γ ,, svass nx A1 |-i B1 = B1' : sSort z ->
    Σ ;;; Γ ,, svass ny A2 |-i B2 = B2' : sSort z ->
    Σ ;;; Γ |-i sCongProd B1 B2 pA pB = sCongProd B1' B2' pA' pB' :
    sHeq (sSort (max_sort s z)) (sProd nx A1 B1)
         (sSort (max_sort s z)) (sProd ny A2 B2)

| cong_CongLambda Γ s z nx ny np A1 A2 B1 B2 t1 t2 pA pB pt
                  B1' B2' t1' t2' pA' pB' pt' :
    Σ ;;; Γ |-i pA = pA' : sHeq (sSort s) A1 (sSort s) A2 ->
    Σ ;;; Γ ,, svass np (sPack A1 A2)
    |-i pB = pB' : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                       (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ ,, svass np (sPack A1 A2)
    |-i pt = pt' : sHeq ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                       ((lift 1 1 t1){ 0 := sProjT1 (sRel 0) })
                       ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) })
                       ((lift 1 1 t2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ |-i A1 : sSort s ->
    Σ ;;; Γ |-i A2 : sSort s ->
    Σ ;;; Γ ,, svass nx A1 |-i B1 = B1' : sSort z ->
    Σ ;;; Γ ,, svass ny A2 |-i B2 = B2' : sSort z ->
    Σ ;;; Γ ,, svass nx A1 |-i t1 = t1' : B1 ->
    Σ ;;; Γ ,, svass ny A2 |-i t2 = t2' : B2 ->
    Σ ;;; Γ |-i sCongLambda B1 B2 t1 t2 pA pB pt
             = sCongLambda B1' B2' t1' t2' pA' pB' pt' :
               sHeq (sProd nx A1 B1) (sLambda nx A1 B1 t1)
                    (sProd ny A2 B2) (sLambda ny A2 B2 t2)

| cong_CongApp Γ s z nx ny np A1 A2 B1 B2 u1 u2 v1 v2 pA pB pu pv
               B1' B2' pu' pA' pB' pv' :
    Σ ;;; Γ |-i pA = pA' : sHeq (sSort s) A1 (sSort s) A2 ->
    Σ ;;; Γ ,, svass np (sPack A1 A2)
    |-i pB = pB' : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                       (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ |-i pu = pu' : sHeq (sProd nx A1 B1) u1 (sProd ny A2 B2) u2 ->
    Σ ;;; Γ |-i pv = pv' : sHeq A1 v1 A2 v2 ->
    Σ ;;; Γ |-i A1 : sSort s ->
    Σ ;;; Γ |-i A2 : sSort s ->
    Σ ;;; Γ ,, svass nx A1 |-i B1 = B1' : sSort z ->
    Σ ;;; Γ ,, svass ny A2 |-i B2 = B2' : sSort z ->
    Σ ;;; Γ |-i u1 : sProd nx A1 B1 ->
    Σ ;;; Γ |-i u2 : sProd ny A2 B2 ->
    Σ ;;; Γ |-i v1 : A1 ->
    Σ ;;; Γ |-i v2 : A2 ->
    Σ ;;; Γ |-i sCongApp B1 B2 pu pA pB pv
             = sCongApp B1' B2' pu' pA' pB' pv' :
               sHeq (B1{0 := v1}) (sApp u1 nx A1 B1 v1)
                    (B2{0 := v2}) (sApp u2 ny A2 B2 v2)

| cong_CongEq Γ s A1 A2 u1 u2 v1 v2 pA pu pv pA' pu' pv' :
    Σ ;;; Γ |-i pA = pA' : sHeq (sSort s) A1 (sSort s) A2 ->
    Σ ;;; Γ |-i pu = pu' : sHeq A1 u1 A2 u2 ->
    Σ ;;; Γ |-i pv = pv' : sHeq A1 v1 A2 v2 ->
    Σ ;;; Γ |-i A1 : sSort s ->
    Σ ;;; Γ |-i A2 : sSort s ->
    Σ ;;; Γ |-i u1 : A1 ->
    Σ ;;; Γ |-i u2 : A2 ->
    Σ ;;; Γ |-i v1 : A1 ->
    Σ ;;; Γ |-i v2 : A2 ->
    Σ ;;; Γ |-i sCongEq pA pu pv = sCongEq pA' pu' pv' :
               sHeq (sSort s) (sEq A1 u1 v1) (sSort s) (sEq A2 u2 v2)

| cong_CongRefl Γ s A1 A2 u1 u2 pA pu pA' pu' :
    Σ ;;; Γ |-i pA = pA' : sHeq (sSort s) A1 (sSort s) A2 ->
    Σ ;;; Γ |-i pu = pu' : sHeq A1 u1 A2 u2 ->
    Σ ;;; Γ |-i A1 : sSort s ->
    Σ ;;; Γ |-i A2 : sSort s ->
    Σ ;;; Γ |-i u1 : A1 ->
    Σ ;;; Γ |-i u2 : A2 ->
    Σ ;;; Γ |-i sCongRefl pA pu = sCongRefl pA' pu' :
               sHeq (sEq A1 u1 u1) (sRefl A1 u1) (sEq A2 u2 u2) (sRefl A2 u2)

| cong_EqToHeq Γ A u v p1 p2 s :
    Σ ;;; Γ |-i p1 = p2 : sEq A u v ->
    Σ ;;; Γ |-i A : sSort s ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i v : A ->
    Σ ;;; Γ |-i sEqToHeq p1 = sEqToHeq p2 : sHeq A u A v

| cong_HeqTypeEq Γ A u B v p1 p2 s :
    Σ ;;; Γ |-i p1 = p2 : sHeq A u B v ->
    Σ ;;; Γ |-i A : sSort s ->
    Σ ;;; Γ |-i B : sSort s ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i v : B ->
    Σ ;;; Γ |-i sHeqTypeEq p1 = sHeqTypeEq p2 : sEq (sSort s) A B

| cong_ProjT1 Γ A1 A2 p1 p2 s :
    Σ ;;; Γ |-i A1 : sSort s ->
    Σ ;;; Γ |-i A2 : sSort s ->
    Σ ;;; Γ |-i p1 = p2 : sPack A1 A2 ->
    Σ ;;; Γ |-i sProjT1 p1 = sProjT1 p2 : A1

| cong_ProjT2 Γ A1 A2 p1 p2 s :
    Σ ;;; Γ |-i A1 : sSort s ->
    Σ ;;; Γ |-i A2 : sSort s ->
    Σ ;;; Γ |-i p1 = p2 : sPack A1 A2 ->
    Σ ;;; Γ |-i sProjT2 p1 = sProjT2 p2 : A2

| cong_ProjTe Γ A1 A2 p1 p2 s :
    Σ ;;; Γ |-i A1 : sSort s ->
    Σ ;;; Γ |-i A2 : sSort s ->
    Σ ;;; Γ |-i p1 = p2 : sPack A1 A2 ->
    Σ ;;; Γ |-i sProjTe p1 = sProjTe p2 : sHeq A1 (sProjT1 p1) A2 (sProjT2 p1)

| eq_HeqToEqRefl Γ s A u :
    Σ ;;; Γ |-i A : sSort s ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i sHeqToEq (sHeqRefl A u) = sRefl A u : sEq A u u

where " Σ ;;; Γ '|-i' t = u : T " := (@eq_term Σ Γ t u T) : i_scope.

Derive Signature for typing.
Derive Signature for wf.
Derive Signature for eq_term.

Delimit Scope i_scope with i.

Open Scope i_scope.

Definition isType (Σ : sglobal_context) (Γ : scontext) (t : sterm) :=
  ∑ s, Σ ;;; Γ |-i t : sSort s.

Inductive type_constructors (Σ : sglobal_context) (Γ : scontext) :
  list (ident * sterm * nat) -> Type :=
| type_cnstrs_nil : type_constructors Σ Γ []
| type_cnstrs_cons id t n l :
    isType Σ Γ t ->
    type_constructors Σ Γ l ->
    (** TODO: check it has n products ending in a tRel application *)
    type_constructors Σ Γ ((id, t, n) :: l).

Inductive type_projections (Σ : sglobal_context) (Γ : scontext) :
  list (ident * sterm) -> Type :=
| type_projs_nil : type_projections Σ Γ []
| type_projs_cons id t l :
    isType Σ Γ t ->
    type_projections Σ Γ l ->
    type_projections Σ Γ ((id, t) :: l).

Definition arities_context (l : list sone_inductive_body) :=
  List.map (fun ind => svass (nNamed ind.(sind_name)) ind.(sind_type)) l.

Definition isArity Σ Γ T :=
  isType Σ Γ T (* FIXME  /\ decompose_prod_n *).

Inductive type_inddecls (Σ : sglobal_context) (pars : scontext) (Γ : scontext) :
  list sone_inductive_body -> Type :=
| type_ind_nil : type_inddecls Σ pars Γ []
| type_ind_cons na ty cstrs projs kelim l :
    (** Arity is well-formed *)
    isArity Σ [] ty ->
    (** Constructors are well-typed *)
    type_constructors Σ Γ cstrs ->
    (** Projections are well-typed *)
    type_projections Σ (Γ ,,, pars ,, svass nAnon ty) projs ->
    (** The other inductives in the block are well-typed *)
    type_inddecls Σ pars Γ l ->
    (** TODO: check kelim*)
    type_inddecls Σ pars Γ (Build_sone_inductive_body na ty kelim cstrs projs :: l).

Definition type_inductive Σ inds :=
  (** FIXME: should be pars ++ arities w/o params *)
  type_inddecls Σ [] (arities_context inds) inds.

Definition type_global_decl Σ decl : Type :=
  match decl with  (* TODO universes *)
  | SConstantDecl id d => (* type_constant_decl Σ d *) ()
  | SInductiveDecl ind inds => type_inductive Σ inds.(sind_bodies)
  end.

Inductive fresh_global (s : string) : sglobal_declarations -> Prop :=
| fresh_global_nil : fresh_global s nil
| fresh_global_cons env g :
    fresh_global s env -> sglobal_decl_ident g <> s ->
    fresh_global s (cons g env).

Inductive type_global_env φ : sglobal_declarations -> Type :=
| globenv_nil : type_global_env φ []
| globenv_decl Σ id d :
    type_global_env φ Σ ->
    fresh_global id Σ ->
    type_global_decl (Σ, φ) d ->
    type_global_env φ (d :: Σ).

Definition type_glob (Σ : sglobal_context) : Type :=
  type_global_env (snd Σ) (fst Σ).

(* Lemmata about typing *)

Open Scope type_scope.
Open Scope i_scope.

(* Typing up to equality *)
Lemma meta_ctx_conv :
  forall {Σ Γ Δ t A},
    Σ ;;; Γ |-i t : A ->
    Γ = Δ ->
    Σ ;;; Δ |-i t : A.
Proof.
  intros Σ Γ Δ t A h e.
  rewrite <- e. exact h.
Defined.

Lemma meta_eqctx_conv :
  forall {Σ Γ Δ t1 t2 A},
    Σ ;;; Γ |-i t1 = t2 : A ->
    Γ = Δ ->
    Σ ;;; Δ |-i t1 = t2 : A.
Proof.
  intros Σ Γ Δ t1 t2 A h e.
  rewrite <- e. exact h.
Defined.

Lemma meta_conv :
  forall {Σ Γ t A B},
    Σ ;;; Γ |-i t : A ->
    A = B ->
    Σ ;;; Γ |-i t : B.
Proof.
  intros Σ Γ t A B h e.
  rewrite <- e. exact h.
Defined.

Lemma meta_eqconv :
  forall {Σ Γ t t' A B},
    Σ ;;; Γ |-i t = t' : A ->
    A = B ->
    Σ ;;; Γ |-i t = t' : B.
Proof.
  intros Σ Γ t t' A B h e.
  rewrite <- e. exact h.
Defined.

Lemma typing_wf :
  forall {Σ Γ t T},
    Σ ;;; Γ |-i t : T ->
    wf Σ Γ.
Proof.
  intros Σ Γ t T H. induction H ; easy.
Defined.

(* Lifting of context *)

Definition lift_decl n k d : scontext_decl :=
  {| sdecl_name := sdecl_name d ;
     sdecl_body := option_map (lift n k) (sdecl_body d) ;
     sdecl_type := lift n k (sdecl_type d)
  |}.

Fixpoint lift_context n Γ : scontext :=
  match Γ with
  | nil => nil
  | A :: Γ => (lift_decl n #|Γ| A) :: (lift_context n Γ)
  end.

Fact lift_decl0 :
  forall {d k}, lift_decl 0 k d = d.
Proof.
  intros d k.
  destruct d as [x b A].
  unfold lift_decl. cbn. rewrite lift00. f_equal.
  destruct b.
  - cbn. rewrite lift00. reflexivity.
  - reflexivity.
Defined.

Fact lift_context0 :
  forall {Γ}, lift_context 0 Γ = Γ.
Proof.
  intro Γ. induction Γ.
  - reflexivity.
  - cbn. rewrite lift_decl0. rewrite IHΓ. reflexivity.
Defined.

Fact lift_decl_svass :
  forall na A n k,
    lift_decl n k (svass na A) = svass na (lift n k A).
Proof.
  intros na A n k.
  reflexivity.
Defined.

Fact length_cat :
  forall {A} {Γ Δ : list A}, #|Γ ++ Δ| = (#|Γ| + #|Δ|)%nat.
Proof.
  intros A Γ. induction Γ ; intro Δ.
  - cbn. reflexivity.
  - cbn. f_equal. apply IHΓ.
Defined.

Fact lift_context_length :
  forall {k Ξ}, #|lift_context k Ξ| = #|Ξ|.
Proof.
  intros k Ξ.
  induction Ξ.
  - cbn. reflexivity.
  - cbn. f_equal. assumption.
Defined.

(* Should be in SCommon *)
Fact safe_nth_irr :
  forall {A n} {l : list A} {isdecl isdecl'},
    safe_nth l (exist _ n isdecl) =
    safe_nth l (exist _ n isdecl').
Proof.
  intros A n. induction n ; intro l ; destruct l ; try easy ; intros isdecl isdecl'.
  cbn. eapply IHn.
Defined.

Fact safe_nth_cong_irr :
  forall {A n m} {l : list A} {isdecl isdecl'},
    n = m ->
    safe_nth l (exist _ n isdecl) =
    safe_nth l (exist _ m isdecl').
Proof.
  intros A n m l isdecl isdecl' e.
  revert isdecl isdecl'.
  rewrite e. intros isdecl isdecl'.
  apply safe_nth_irr.
Defined.

Fact safe_nth_ge :
  forall {Γ Δ n} { isdecl : n < #|Γ ,,, Δ| } { isdecl' : n - #|Δ| < #|Γ| },
    n >= #|Δ| ->
    safe_nth (Γ ,,, Δ) (exist _ n isdecl) =
    safe_nth Γ (exist _ (n - #|Δ|) isdecl').
Proof.
  intros Γ Δ.
  induction Δ ; intros n isdecl isdecl' h.
  - cbn in *. revert isdecl'.
    replace (n - 0) with n by omega.
    intros isdecl'. apply safe_nth_irr.
  - destruct n.
    + cbn in *. inversion h.
    + cbn. apply IHΔ. cbn in *. omega.
Defined.

Definition ge_sub {Γ Δ n} (isdecl : n < #|Γ ,,, Δ|) :
  n >= #|Δ| ->  n - #|Δ| < #|Γ|.
Proof.
  intro h.
  rewrite length_cat in isdecl. omega.
Defined.

Fact safe_nth_ge' :
  forall {Γ Δ n} { isdecl : n < #|Γ ,,, Δ| } (h : n >= #|Δ|),
    safe_nth (Γ ,,, Δ) (exist _ n isdecl) =
    safe_nth Γ (exist _ (n - #|Δ|) (ge_sub isdecl h)).
Proof.
  intros Γ Δ n isdecl h.
  eapply safe_nth_ge. assumption.
Defined.

Fact safe_nth_lt :
  forall {n Γ Δ} { isdecl : n < #|Γ ,,, Δ| } { isdecl' : n < #|Δ| },
    safe_nth (Γ ,,, Δ) (exist _ n isdecl) =
    safe_nth Δ (exist _ n isdecl').
Proof.
  intros n. induction n ; intros Γ Δ isdecl isdecl'.
  - destruct Δ.
    + cbn in *. inversion isdecl'.
    + cbn. reflexivity.
  - destruct Δ.
    + cbn in *. inversion isdecl'.
    + cbn. eapply IHn.
Defined.

Fact safe_nth_lift_context :
  forall {Γ Δ : scontext} {n isdecl isdecl'},
    sdecl_type (safe_nth (lift_context #|Γ| Δ) (exist _ n isdecl)) =
    lift #|Γ| (#|Δ| - n - 1) (sdecl_type (safe_nth Δ (exist _ n isdecl'))).
Proof.
  intros Γ Δ. induction Δ.
  - cbn. easy.
  - intro n. destruct n ; intros isdecl isdecl'.
    + cbn. replace (#|Δ| - 0) with #|Δ| by omega. reflexivity.
    + cbn. erewrite IHΔ. reflexivity.
Defined.

Fact lift_context_ex :
  forall {Δ Ξ : scontext} {n isdecl isdecl'},
    lift0 (S n) (sdecl_type (safe_nth (lift_context #|Δ| Ξ) (exist _ n isdecl))) =
    lift #|Δ| #|Ξ| (lift0 (S n) (sdecl_type (safe_nth Ξ (exist _ n isdecl')))).
Proof.
  intros Δ Ξ n isdecl isdecl'.
  erewrite safe_nth_lift_context.
  rewrite <- liftP2 by omega.
  cbn.
  replace (S (n + (#|Ξ| - n - 1)))%nat with #|Ξ|.
  - reflexivity.
  - revert n isdecl isdecl'. induction Ξ ; intros n isdecl isdecl'.
    + cbn. easy.
    + cbn. f_equal.
      destruct n.
      * cbn. omega.
      * cbn. apply IHΞ.
        -- cbn in *. omega.
        -- cbn in *. omega.
Defined.

Ltac erewrite_assumption :=
  match goal with
  | H : _ = _ |- _ =>
    erewrite H by omega
  end.

Fact type_ctx_closed_above :
  forall {Σ Γ t T},
    Σ ;;; Γ |-i t : T ->
    closed_above #|Γ| t = true.
Proof.
  intros Σ Γ t T h.
  dependent induction h.
  all: try (cbn in * ; repeat erewrite_assumption ; reflexivity).
  unfold closed_above. case_eq (n <? #|Γ|) ; intro e ; bprop e ; try omega.
  reflexivity.
Defined.

Fact type_ctxempty_closed :
  forall {Σ t T},
    Σ ;;; [] |-i t : T ->
    closed t.
Proof.
  intros Σ t T h.
  unfold closed. eapply @type_ctx_closed_above with (Γ := []). eassumption.
Defined.

Ltac erewrite_close_above_lift_id :=
  match goal with
  | H : forall n k l, _ -> k >= l -> _ = _ |- _ =>
    erewrite H by (first [ eassumption | omega ])
  end.

Ltac destruct_andb :=
  match goal with
  | H : _ && _ = true |- _ =>
    destruct (andb_prop _ _ H) ; clear H
  end.

Fact closed_above_lift_id :
  forall t n k l,
    closed_above l t = true ->
    k >= l ->
    lift n k t = t.
Proof.
  intro t. induction t ; intros m k l clo h.
  all: try (cbn ; cbn in clo ; repeat destruct_andb ;
            repeat erewrite_close_above_lift_id ;
            reflexivity).
  unfold closed in clo. unfold closed_above in clo.
  bprop clo. cbn.
  case_eq (k <=? n) ; intro e ; bprop e ; try omega.
  reflexivity.
Defined.

Fact closed_lift :
  forall t n k,
    closed t ->
    lift n k t = t.
Proof.
  intros t n k h.
  unfold closed in h.
  eapply closed_above_lift_id.
  - eassumption.
  - omega.
Defined.

Fact typed_ind_type' :
  forall {Σ : sglobal_context} {decl'},
    type_inductive Σ (sind_bodies decl') ->
    forall {n decl},
      nth_error (sind_bodies decl') n = Some decl ->
      isType Σ [] (sind_type decl).
Proof.
  intros Σ decl' hind. unfold type_inductive in hind.
  induction hind.
  - intros n decl h.
    destruct n ; cbn in h ; inversion h.
  - intros n decl h.
    destruct n.
    + cbn in h. inversion h as [ e ]. subst. clear h.
      cbn. unfold isArity in i.
      assumption.
    + cbn in h. eapply IHhind.
      eassumption.
Defined.

Axiom cheating : forall {A}, A.
Tactic Notation "cheat" := apply cheating.

Fixpoint weak_glob_type {Σ ϕ Γ t A} (h : (Σ,ϕ) ;;; Γ |-i t : A) :
  forall d, (d::Σ, ϕ) ;;; Γ |-i t : A

with weak_glob_eq {Σ ϕ Γ t1 t2 A} (h : (Σ,ϕ) ;;; Γ |-i t1 = t2 : A) :
  forall d, (d::Σ, ϕ) ;;; Γ |-i t1 = t2 : A

with weak_glob_wf {Σ ϕ Γ} (h : wf (Σ,ϕ) Γ) :
  forall d, wf (d::Σ, ϕ) Γ.
Proof.
  (* weak_glob_type *)
  - { dependent destruction h ; intro d.
      all: try (econstructor ; try apply weak_glob_wf ;
                try apply weak_glob_type ;
                try apply weak_glob_eq ;
                eassumption
               ).
      - eapply type_HeqTrans with (B := B) (b := b).
        all: apply weak_glob_type ; eassumption.
      - eapply type_ProjT2 with (A1 := A1).
        all: apply weak_glob_type ; eassumption.
      - eapply type_Ind with (univs := univs).
        + apply weak_glob_wf. assumption.
        + destruct isdecl as [decl' [h1 [h2 h3]]].
          exists decl'. repeat split.
          * cbn in *. unfold sdeclared_minductive in *.
            unfold slookup_env.
            cheat.
          * assumption.
          * assumption.
    }

  (* weak_glob_eq *)
  - { dependent destruction h ; intro d.
      all: try (econstructor ; try apply weak_glob_wf ;
                try apply weak_glob_type ;
                try apply weak_glob_eq ;
                eassumption
               ).
      - eapply cong_HeqTrans with (B := B) (b := b).
        all: try apply weak_glob_eq ; try apply weak_glob_type ; eassumption.
      - eapply cong_ProjT2 with (A1 := A1).
        all: try apply weak_glob_eq ; try apply weak_glob_type ; eassumption.
    }

  (* weak_glob_wf *)
  - { dependent destruction h ; intro d.
      - constructor.
      - econstructor.
        + apply weak_glob_wf. assumption.
        + apply weak_glob_type. eassumption.
    }
Defined.

(* TODO: Prove weakening of global_context in order to drop
   the existential quantifier.
 *)
Fact typed_ind_type :
  forall {Σ : sglobal_context},
    type_glob Σ ->
    forall {ind decl univs},
      sdeclared_inductive (fst Σ) ind univs decl ->
      ∑ Σ', isType Σ' [] (sind_type decl).
Proof.
  intros Σ hg. destruct Σ as [Σ ϕ].
  dependent induction hg.
  - intros ind decl univs isdecl.
    cbn in *. destruct isdecl as [decl' [h1 [h2 h3]]].
    dependent destruction h1.
  - intros ind decl univs isdecl.
    destruct isdecl as [decl' [h1 [h2 h3]]].
    cbn in h1. unfold sdeclared_minductive in h1.
    cbn in h1.
    case_eq (ident_eq (inductive_mind ind) (sglobal_decl_ident d)).
    + intro e. rewrite e in h1.
      inversion h1 as [ h1' ]. subst.
      cbn in t. clear e.
      exists (Σ, ϕ). eapply typed_ind_type' ; eassumption.
    + intro e. rewrite e in h1.
      eapply IHhg. exists decl'. repeat split.
      * eassumption.
      * eassumption.
Defined.

Fact lift_ind_type :
  forall {Σ : sglobal_context},
    type_glob Σ ->
    forall {ind decl univs},
      sdeclared_inductive (fst Σ) ind univs decl ->
      forall n k,
        lift n k (sind_type decl) = sind_type decl.
Proof.
  intros Σ hg ind decl univs h n k.
  destruct (typed_ind_type hg h) as [Σ' [s hty]].
  eapply closed_lift.
  eapply type_ctxempty_closed.
  eassumption.
Defined.

Ltac ih h :=
  lazymatch goal with
  | [ type_lift :
        forall (Σ : sglobal_context) (Γ Δ Ξ : scontext) (t A : sterm),
          Σ;;; Γ ,,, Ξ |-i t : A ->
          type_glob Σ ->
          wf Σ (Γ ,,, Δ) ->
          Σ;;; Γ ,,, Δ ,,, lift_context #|Δ| Ξ
          |-i lift #|Δ| #|Ξ| t : lift #|Δ| #|Ξ| A,
      cong_lift :
        forall (Σ : sglobal_context) (Γ Δ Ξ : scontext) (t1 t2 A : sterm),
          Σ;;; Γ ,,, Ξ |-i t1 = t2 : A ->
          type_glob Σ ->
          wf Σ (Γ ,,, Δ) ->
          Σ;;; Γ ,,, Δ ,,, lift_context #|Δ| Ξ
          |-i lift #|Δ| #|Ξ| t1 = lift #|Δ| #|Ξ| t2 : lift #|Δ| #|Ξ| A
    |- _ ] =>
    lazymatch type of h with
    | _ ;;; ?Γ' ,,, ?Ξ' |-i _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_lift with (Γ := Γ') (Ξ := Ξ') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,,, ?Ξ'),, ?d' |-i _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_lift with (Γ := Γ') (Ξ := Ξ',, d') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,,, ?Ξ'),, ?d',, ?d'' |-i _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_lift with (Γ := Γ') (Ξ := (Ξ',, d'),, d'') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; ?Γ' ,,, ?Ξ' |-i _ = _ : ?T' =>
      eapply meta_eqconv ; [
        eapply meta_eqctx_conv ; [
          eapply cong_lift with (Γ := Γ') (Ξ := Ξ') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,,, ?Ξ'),, ?d' |-i _ = _ : ?T' =>
      eapply meta_eqconv ; [
        eapply meta_eqctx_conv ; [
          eapply cong_lift with (Γ := Γ') (Ξ := Ξ',, d') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,,, ?Ξ'),, ?d',, ?d'' |-i _ = _ : ?T' =>
      eapply meta_eqconv ; [
        eapply meta_eqctx_conv ; [
          eapply cong_lift with (Γ := Γ') (Ξ := (Ξ',, d'),, d'') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    end ; try (cbn ; reflexivity)
  | _ => fail "Cannot retrieve type_lift or cong_lift"
  end.

Ltac eih :=
  lazymatch goal with
  | h : _ ;;; _ |-i ?t : _ |- _ ;;; _ |-i lift _ _ ?t : _ => ih h
  | h : _ ;;; _ |-i ?t = _ : _ |- _ ;;; _ |-i lift _ _ ?t = _ : _ =>
    ih h
  | _ => fail "Not handled by eih"
  end.

Fixpoint type_lift {Σ Γ Δ Ξ t A} (h : Σ ;;; Γ ,,, Ξ |-i t : A) {struct h} :
  type_glob Σ ->
  wf Σ (Γ ,,, Δ) ->
  Σ ;;; Γ ,,, Δ ,,, lift_context #|Δ| Ξ |-i lift #|Δ| #|Ξ| t : lift #|Δ| #|Ξ| A

with cong_lift {Σ Γ Δ Ξ t1 t2 A} (h : Σ ;;; Γ ,,, Ξ |-i t1 = t2 : A) {struct h} :
  type_glob Σ ->
  wf Σ (Γ ,,, Δ) ->
  Σ ;;; Γ ,,, Δ ,,, lift_context #|Δ| Ξ |-i lift #|Δ| #|Ξ| t1
  = lift #|Δ| #|Ξ| t2 : lift #|Δ| #|Ξ| A

with wf_lift {Σ Γ Δ Ξ} (h : wf Σ (Γ ,,, Ξ)) {struct h} :
  type_glob Σ ->
  wf Σ (Γ ,,, Δ) ->
  wf Σ (Γ ,,, Δ ,,, lift_context #|Δ| Ξ)
.
Proof.
  - { dependent destruction h ; intros hΣ hwf.
      - cbn. case_eq (#|Ξ| <=? n) ; intro e ; bprop e.
        + rewrite liftP3 by omega.
          replace (#|Δ| + S n)%nat with (S (#|Δ| + n)) by omega.
          eapply meta_conv.
          * eapply type_Rel.
            eapply wf_lift ; assumption.
          * f_equal. f_equal.
            erewrite 3!safe_nth_ge'
              by (try rewrite lift_context_length ; omega).
            eapply safe_nth_cong_irr.
            rewrite lift_context_length. omega.
        + eapply meta_conv.
          * eapply type_Rel. eapply wf_lift ; assumption.
          * erewrite 2!safe_nth_lt.
            eapply lift_context_ex.
      - cbn. apply type_Sort. now apply wf_lift.
      - cbn. eapply type_Prod ; eih.
      - cbn. eapply type_Lambda ; eih.
      - cbn.
        change (lift #|Δ| #|Ξ| (B {0 := u}))
          with (lift #|Δ| (0 + #|Ξ|) (B { 0 := u })).
        rewrite substP1.
        eapply type_App ; eih.
      - cbn. apply type_Eq ; eih.
      - cbn. eapply type_Refl ; eih.
      - change (#|Ξ|) with (0 + #|Ξ|)%nat.
        rewrite substP1.
        replace (S (0 + #|Ξ|)) with (1 + #|Ξ|)%nat by omega.
        rewrite substP1.
        cbn. eapply type_J ; try eih.
        + instantiate (1 := ne). instantiate (1 := nx). cbn. unfold ssnoc.
          rewrite !lift_decl_svass. cbn.
          f_equal. f_equal. f_equal.
          * replace (S #|Ξ|) with (1 + #|Ξ|)%nat by omega.
            apply liftP2. omega.
          * replace (S #|Ξ|) with (1 + #|Ξ|)%nat by omega.
            apply liftP2. omega.
        + replace (S (S #|Ξ|)) with (1 + (S (0 + #|Ξ|)))%nat by omega.
          rewrite <- substP1.
          replace (1 + (0 + #|Ξ|))%nat with (S (0 + #|Ξ|))%nat by omega.
          change (sRefl (lift #|Δ| #|Ξ| A0) (lift #|Δ| #|Ξ| u))
            with (lift #|Δ| #|Ξ| (sRefl A0 u)).
          rewrite <- substP1. reflexivity.
      - cbn. eapply type_Transport ; eih.
      - cbn. eapply type_Heq ; eih.
      - cbn. eapply type_HeqToEq ; eih.
      - cbn. eapply type_HeqRefl ; eih.
      - cbn. eapply type_HeqSym ; eih.
      - cbn. eapply @type_HeqTrans with (B := lift #|Δ| #|Ξ| B) (b := lift #|Δ| #|Ξ| b) ; eih.
      - cbn. eapply type_HeqTransport ; eih.
      - cbn. eapply type_CongProd ; try eih.
        cbn. f_equal.
        + rewrite <- liftP2 by omega.
          change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1.
          rewrite substP1. cbn. reflexivity.
        + rewrite <- liftP2 by omega.
          change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1.
          rewrite substP1. cbn. reflexivity.
      - cbn. eapply type_CongLambda ; try eih.
        + cbn. f_equal.
          * rewrite <- liftP2 by omega.
            change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1.
            rewrite substP1. cbn. reflexivity.
          * rewrite <- liftP2 by omega.
            change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1.
            rewrite substP1. cbn. reflexivity.
        + cbn. f_equal.
          * rewrite <- liftP2 by omega.
            change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1.
            rewrite substP1. cbn. reflexivity.
          * rewrite <- liftP2 by omega.
            change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1.
            rewrite substP1. cbn. reflexivity.
          * rewrite <- liftP2 by omega.
            change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1.
            rewrite substP1. cbn. reflexivity.
          * rewrite <- liftP2 by omega.
            change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1.
            rewrite substP1. cbn. reflexivity.
      - cbn.
        change (lift #|Δ| #|Ξ| (B1 {0 := v1}))
          with (lift #|Δ| (0 + #|Ξ|) (B1 { 0 := v1 })).
        change (lift #|Δ| #|Ξ| (B2 {0 := v2}))
          with (lift #|Δ| (0 + #|Ξ|) (B2 { 0 := v2 })).
        rewrite 2!substP1.
        eapply type_CongApp ; eih.
        cbn. f_equal.
        + rewrite <- liftP2 by omega.
          change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1.
          rewrite substP1. cbn. reflexivity.
        + rewrite <- liftP2 by omega.
          change (S #|Ξ|) with (0 + (S #|Ξ|))%nat at 1.
          rewrite substP1. cbn. reflexivity.
      - cbn. eapply type_CongEq ; eih.
      - cbn. eapply type_CongRefl ; eih.
      - cbn. eapply type_EqToHeq ; eih.
      - cbn. eapply type_HeqTypeEq ; eih.
      - cbn. eapply type_Pack ; eih.
      - cbn. eapply @type_ProjT1 with (A2 := lift #|Δ| #|Ξ| A2) ; eih.
      - cbn. eapply @type_ProjT2 with (A1 := lift #|Δ| #|Ξ| A1) ; eih.
      - cbn. eapply type_ProjTe ; eih.
      - cbn. erewrite lift_ind_type by eassumption.
        eapply type_Ind.
        + now apply wf_lift.
        + eassumption.
      - eapply type_conv ; eih.
    }

  (* cong_lift *)
  - { intros hg hwf. dependent destruction h.
      - apply eq_reflexivity. apply type_lift ; assumption.
      - apply eq_symmetry. eapply cong_lift ; assumption.
      - eapply eq_transitivity ; eih.
      - change (lift #|Δ| #|Ξ| (t {0 := u}))
          with (lift #|Δ| (0 + #|Ξ|) (t { 0 := u })).
        change (lift #|Δ| #|Ξ| (B {0 := u}))
          with (lift #|Δ| (0 + #|Ξ|) (B { 0 := u })).
        rewrite 2!substP1. cbn.
        eapply eq_beta ; eih.
      - change (#|Ξ|) with (0 + #|Ξ|)%nat.
        rewrite substP1.
        replace (S (0 + #|Ξ|)) with (1 + #|Ξ|)%nat by omega.
        rewrite substP1. cbn.
        eapply eq_JRefl ; eih.
        + cbn. rewrite lift_decl_svass. unfold ssnoc.
          instantiate (1 := nx). instantiate (1 := ne). cbn.
          f_equal. f_equal. f_equal.
          * replace (S #|Ξ|) with (1 + #|Ξ|)%nat by omega.
            apply liftP2. omega.
          * replace (S #|Ξ|) with (1 + #|Ξ|)%nat by omega.
            apply liftP2. omega.
        + replace (S (S #|Ξ|)) with (1 + (S (0 + #|Ξ|)))%nat by omega.
          rewrite <- substP1.
          replace (1 + (0 + #|Ξ|))%nat with (S (0 + #|Ξ|))%nat by omega.
          change (sRefl (lift #|Δ| #|Ξ| A0) (lift #|Δ| #|Ξ| u))
            with (lift #|Δ| #|Ξ| (sRefl A0 u)).
          rewrite <- substP1. reflexivity.
      - cbn. eapply eq_TransportRefl ; eih.
      - eapply eq_conv ; eih.
      - cbn. eapply cong_Prod ; eih.
      - cbn. eapply cong_Lambda ; eih.
      - cbn.
        change (lift #|Δ| #|Ξ| (B1 {0 := u1}))
          with (lift #|Δ| (0 + #|Ξ|) (B1 { 0 := u1 })).
        rewrite substP1.
        eapply cong_App ; eih.
      - cbn. eapply cong_Eq ; eih.
      - cbn. eapply cong_Refl ; eih.
      - change (#|Ξ|) with (0 + #|Ξ|)%nat.
        rewrite substP1.
        replace (S (0 + #|Ξ|)) with (1 + #|Ξ|)%nat by omega.
        rewrite substP1. cbn.
        eapply cong_J ; eih.
        + cbn. rewrite lift_decl_svass. unfold ssnoc.
          instantiate (1 := nx). instantiate (1 := ne). cbn.
          f_equal. f_equal. f_equal.
          * replace (S #|Ξ|) with (1 + #|Ξ|)%nat by omega.
            apply liftP2. omega.
          * replace (S #|Ξ|) with (1 + #|Ξ|)%nat by omega.
            apply liftP2. omega.
        + replace (S (S #|Ξ|)) with (1 + (S (0 + #|Ξ|)))%nat by omega.
          rewrite <- substP1.
          replace (1 + (0 + #|Ξ|))%nat with (S (0 + #|Ξ|))%nat by omega.
          change (sRefl (lift #|Δ| #|Ξ| A1) (lift #|Δ| #|Ξ| u1))
            with (lift #|Δ| #|Ξ| (sRefl A1 u1)).
          rewrite <- substP1. reflexivity.
      - cbn. eapply cong_Transport ; eih.
      - cbn. eapply cong_Heq ; eih.
      - cbn. eapply cong_Pack ; eih.
      - cbn. eapply cong_HeqToEq ; eih.
      - cbn. eapply cong_HeqRefl ; eih.
      - cbn. eapply cong_HeqSym ; eih.
      - cbn. eapply cong_HeqTrans with (B := lift #|Δ| #|Ξ| B) (b := lift #|Δ| #|Ξ| b) ; eih.
      - cbn. eapply cong_HeqTransport ; eih.
      - cbn. eapply cong_CongProd ; eih.
        cbn. f_equal.
        + rewrite <- liftP2 by omega.
          replace (S #|Ξ|) with (0 + (S #|Ξ|))%nat by omega.
          rewrite substP1. cbn. reflexivity.
        + rewrite <- liftP2 by omega.
          replace (S #|Ξ|) with (0 + (S #|Ξ|))%nat by omega.
          rewrite substP1. cbn. reflexivity.
      - cbn. eapply cong_CongLambda ; eih.
        + cbn. f_equal.
          * rewrite <- liftP2 by omega.
            replace (S #|Ξ|) with (0 + (S #|Ξ|))%nat by omega.
            rewrite substP1. cbn. reflexivity.
          * rewrite <- liftP2 by omega.
            replace (S #|Ξ|) with (0 + (S #|Ξ|))%nat by omega.
            rewrite substP1. cbn. reflexivity.
        + cbn. f_equal.
          * rewrite <- liftP2 by omega.
            replace (S #|Ξ|) with (0 + (S #|Ξ|))%nat by omega.
            rewrite substP1. cbn. reflexivity.
          * rewrite <- liftP2 by omega.
            replace (S #|Ξ|) with (0 + (S #|Ξ|))%nat by omega.
            rewrite substP1. cbn. reflexivity.
          * rewrite <- liftP2 by omega.
            replace (S #|Ξ|) with (0 + (S #|Ξ|))%nat by omega.
            rewrite substP1. cbn. reflexivity.
          * rewrite <- liftP2 by omega.
            replace (S #|Ξ|) with (0 + (S #|Ξ|))%nat by omega.
            rewrite substP1. cbn. reflexivity.
      - cbn.
        change (lift #|Δ| #|Ξ| (B1 {0 := v1}))
          with (lift #|Δ| (0 + #|Ξ|) (B1 { 0 := v1 })).
        rewrite substP1.
        change (lift #|Δ| #|Ξ| (B2 {0 := v2}))
          with (lift #|Δ| (0 + #|Ξ|) (B2 { 0 := v2 })).
        rewrite substP1.
        eapply cong_CongApp ; eih.
        cbn. f_equal.
        + rewrite <- liftP2 by omega.
          replace (S #|Ξ|) with (0 + (S #|Ξ|))%nat by omega.
          rewrite substP1. cbn. reflexivity.
        + rewrite <- liftP2 by omega.
          replace (S #|Ξ|) with (0 + (S #|Ξ|))%nat by omega.
          rewrite substP1. cbn. reflexivity.
      - cbn. eapply cong_CongEq ; eih.
      - cbn. eapply cong_CongRefl ; eih.
      - cbn. eapply cong_EqToHeq ; eih.
      - cbn. eapply cong_HeqTypeEq ; eih.
      - cbn. eapply cong_ProjT1 with (A2 := lift #|Δ| #|Ξ| A2) ; eih.
      - cbn. eapply cong_ProjT2 with (A1 := lift #|Δ| #|Ξ| A1) ; eih.
      - cbn. eapply cong_ProjTe ; eih.
      - cbn. eapply eq_HeqToEqRefl ; eih.
    }

  (* wf_lift *)
  - { intros hg hwf.
      destruct Ξ.
      - cbn. assumption.
      - dependent destruction h.
        cbn. econstructor.
        + apply wf_lift ; assumption.
        + instantiate (1 := s0). cbn. change (sSort s0) with (lift #|Δ| #|Ξ| (sSort s0)).
          apply type_lift ; assumption.
    }

    Unshelve.
    all: try rewrite !length_cat ; try rewrite length_cat in isdecl ;
      try rewrite lift_context_length ; omega.
Defined.

Corollary typing_lift01 :
  forall {Σ Γ t A x B s},
    type_glob Σ ->
    Σ ;;; Γ |-i t : A ->
    Σ ;;; Γ |-i B : sSort s ->
    Σ ;;; Γ ,, svass x B |-i lift0 1 t : lift0 1 A.
Proof.
  intros Σ Γ t A x B s hg ht hB.
  apply (@type_lift _ _ [ svass x B ] nil _ _ ht hg).
  econstructor.
  - eapply typing_wf. eassumption.
  - eassumption.
Defined.

Corollary typing_lift02 :
  forall {Σ Γ t A x B s y C s'},
    type_glob Σ ->
    Σ ;;; Γ |-i t : A ->
    Σ ;;; Γ |-i B : sSort s ->
    Σ ;;; Γ ,, svass x B |-i C : sSort s' ->
    Σ ;;; Γ ,, svass x B ,, svass y C |-i lift0 2 t : lift0 2 A.
Proof.
  intros Σ Γ t A x B s y C s' hg ht hB hC.
  assert (eq : forall t, lift0 2 t = lift0 1 (lift0 1 t)).
  { intro u. rewrite lift_lift. reflexivity. }
  rewrite !eq. eapply typing_lift01.
  - assumption.
  - eapply typing_lift01  ; eassumption.
  - eassumption.
Defined.

Corollary cong_lift01 :
  forall {Σ Γ t1 t2 A x B s},
    type_glob Σ ->
    Σ ;;; Γ |-i t1 = t2 : A ->
    Σ ;;; Γ |-i B : sSort s ->
    Σ ;;; Γ ,, svass x B |-i lift0 1 t1 = lift0 1 t2 : lift0 1 A.
Proof.
  intros Σ Γ t1 t2 A x B s hg H H0.
  apply @cong_lift with (Δ := [ svass x B ]) (Ξ := nil).
  - cbn. assumption.
  - assumption.
  - econstructor.
    + eapply typing_wf. eassumption.
    + eassumption.
Defined.

(* Substitution in context *)

Definition subst_decl n u d : scontext_decl :=
  {| sdecl_name := sdecl_name d ;
     sdecl_body := option_map (subst u n) (sdecl_body d) ;
     sdecl_type := (sdecl_type d){ n := u }
  |}.

Fixpoint subst_context u Δ :=
  match Δ with
  | nil => nil
  | A :: Δ => (subst_decl #|Δ| u A) :: (subst_context u Δ)
  end.

Fact subst_decl_svass :
  forall na A n u,
    subst_decl n u (svass na A) = svass na (A{ n := u }).
Proof.
  intros na A n u.
  reflexivity.
Defined.

Fact subst_context_length :
  forall {u Ξ}, #|subst_context u Ξ| = #|Ξ|.
Proof.
  intros u Ξ.
  induction Ξ.
  - cbn. reflexivity.
  - cbn. f_equal. assumption.
Defined.

Fact safe_nth_subst_context :
  forall {Δ : scontext} {n u isdecl isdecl'},
    sdecl_type (safe_nth (subst_context u Δ) (exist _ n isdecl)) =
    (sdecl_type (safe_nth Δ (exist _ n isdecl'))) { #|Δ| - S n := u }.
Proof.
  intro Δ. induction Δ.
  - cbn. easy.
  - intro n. destruct n ; intros u isdecl isdecl'.
    + cbn. replace (#|Δ| - 0) with #|Δ| by omega. reflexivity.
    + cbn. erewrite IHΔ. reflexivity.
Defined.

(* Maybe have them somewhere else? *)
Ltac erewrite_close_above_subst_id :=
  match goal with
  | H : forall n l u, _ -> _ -> _ = _ |- _ =>
    erewrite H by (first [ eassumption | omega ])
  end.

Fact closed_above_subst_id :
  forall t n l u,
    closed_above l t = true ->
    n >= l ->
    t{ n := u } = t.
Proof.
  intro t. induction t ; intros m l u clo h.
  all: try (cbn ; cbn in clo ; repeat destruct_andb ;
            repeat erewrite_close_above_subst_id ;
            reflexivity).
  unfold closed in clo. unfold closed_above in clo.
  bprop clo. cbn.
  case_eq (m ?= n) ; intro e ; bprop e ; try omega.
  reflexivity.
Defined.

Fact closed_subst :
  forall t n u,
    closed t ->
    t{ n := u } = t.
Proof.
  intros t n u h.
  unfold closed in h.
  eapply closed_above_subst_id.
  - eassumption.
  - omega.
Defined.

Fact subst_ind_type :
  forall {Σ : sglobal_context},
    type_glob Σ ->
    forall {ind decl univs},
      sdeclared_inductive (fst Σ) ind univs decl ->
      forall n u,
        (sind_type decl){ n := u } = sind_type decl.
Proof.
  intros Σ hg ind decl univs h n u.
  destruct (typed_ind_type hg h) as [Σ' [s hty]].
  eapply closed_subst.
  eapply type_ctxempty_closed.
  eassumption.
Defined.

Ltac sh h :=
  lazymatch goal with
  | [ type_subst :
        forall (Σ : sglobal_context) (Γ Δ : scontext) (t A : sterm) (nx : name)
          (B u : sterm),
          Σ;;; Γ,, svass nx B ,,, Δ |-i t : A ->
          type_glob Σ ->
          Σ;;; Γ |-i u : B -> Σ;;; Γ ,,, subst_context u Δ |-i
          t {#|Δ| := u} : A {#|Δ| := u},
     cong_subst :
       forall (Σ : sglobal_context) (Γ Δ : scontext) (t1 t2 A : sterm) (nx : name)
         (B u : sterm),
         Σ;;; Γ,, svass nx B ,,, Δ |-i t1 = t2 : A ->
         type_glob Σ ->
         Σ;;; Γ |-i u : B -> Σ;;; Γ ,,, subst_context u Δ |-i
         t1 {#|Δ| := u} = t2 {#|Δ| := u} : A {#|Δ| := u}
    |- _ ] =>
    lazymatch type of h with
    | _ ;;; ?Γ' ,, svass ?nx' ?B' ,,, ?Δ' |-i _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_subst with (Γ := Γ') (Δ := Δ') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,, svass ?nx' ?B' ,,, ?Δ') ,, ?d' |-i _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_subst with (Γ := Γ') (Δ := Δ' ,, d') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,, svass ?nx' ?B' ,,, ?Δ') ,, ?d',, ?d'' |-i _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_subst with (Γ := Γ') (Δ := (Δ' ,, d') ,, d'') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; ?Γ' ,, svass ?nx' ?B' ,,, ?Δ' |-i _ = _ : ?T' =>
      eapply meta_eqconv ; [
        eapply meta_eqctx_conv ; [
          eapply cong_subst with (Γ := Γ') (Δ := Δ') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,, svass ?nx' ?B' ,,, ?Δ') ,, ?d' |-i _ = _ : ?T' =>
      eapply meta_eqconv ; [
        eapply meta_eqctx_conv ; [
          eapply cong_subst with (Γ := Γ') (Δ := Δ' ,, d') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,, svass ?nx' ?B' ,,, ?Δ') ,, ?d',, ?d'' |-i _ = _ : ?T' =>
      eapply meta_eqconv ; [
        eapply meta_eqctx_conv ; [
          eapply cong_subst with (Γ := Γ') (Δ := (Δ' ,, d') ,, d'') (A := T') ; [
            exact h
          | assumption
          | assumption
          ]
        | .. ]
      | .. ]
    end ; try (cbn ; reflexivity)
  | _ => fail "cannot find type_subst, cong_subst"
  end.

Ltac esh :=
  lazymatch goal with
  | h : _ ;;; _ |-i ?t : _ |- _ ;;; _ |-i ?t{ _ := _ } : _ => sh h
  | h : _ ;;; _ |-i ?t = _ : _ |- _ ;;; _ |-i ?t{ _ := _ } = _ : _ =>
    sh h
  | _ => fail "not handled by esh"
  end.

Fixpoint type_subst {Σ Γ Δ t A nx B u}
  (h : Σ ;;; Γ ,, svass nx B ,,, Δ |-i t : A) {struct h} :
  type_glob Σ ->
  Σ ;;; Γ |-i u : B ->
  Σ ;;; Γ ,,, subst_context u Δ |-i t{ #|Δ| := u } : A{ #|Δ| := u }

with cong_subst {Σ Γ Δ t1 t2 A nx B u}
  (h : Σ ;;; Γ ,, svass nx B ,,, Δ |-i t1 = t2 : A) {struct h} :
  type_glob Σ ->
  Σ ;;; Γ |-i u : B ->
  Σ ;;; Γ ,,, subst_context u Δ |-i t1{ #|Δ| := u }
  = t2{ #|Δ| := u } : A{ #|Δ| := u }

with wf_subst {Σ Γ Δ nx B u}
  (h : wf Σ (Γ ,, svass nx B ,,, Δ)) {struct h} :
  type_glob Σ ->
  Σ ;;; Γ |-i u : B ->
  wf Σ (Γ ,,, subst_context u Δ)
.
Proof.
  (* type_subst *)
  - { intros hg hu.
      dependent destruction h.
      - cbn. case_eq (#|Δ| ?= n) ; intro e ; bprop e.
        + assert (h : n >= #|Δ|) by omega.
          rewrite safe_nth_ge' with (h0 := h).
          assert (n - #|Δ| = 0) by omega.
          set (ge := ge_sub isdecl h).
          generalize ge.
          rewrite H. intro ge'.
          cbn. rewrite substP3 by omega.
          subst.
          replace #|Δ| with #|subst_context u Δ|
            by (now rewrite subst_context_length).
          eapply @type_lift with (Ξ := []) (Δ := subst_context u Δ).
          * cbn. assumption.
          * assumption.
          * eapply wf_subst ; eassumption.
        + assert (h : n >= #|Δ|) by omega.
          rewrite safe_nth_ge' with (h0 := h).
          set (ge := ge_sub isdecl h).
          destruct n ; try easy.
          rewrite substP3 by omega.
          generalize ge.
          replace (S n - #|Δ|) with (S (n - #|Δ|)) by omega.
          cbn. intro ge'.
          eapply meta_conv.
          * eapply type_Rel. eapply wf_subst ; eassumption.
          * erewrite safe_nth_ge'.
            f_equal. f_equal. eapply safe_nth_cong_irr.
            rewrite subst_context_length. reflexivity.
        + assert (h : n < #|Δ|) by omega.
          rewrite @safe_nth_lt with (isdecl' := h).
          match goal with
          | |- _ ;;; _ |-i _ : ?t{?d := ?u} =>
            replace (subst u d t) with (t{((S n) + (#|Δ| - (S n)))%nat := u})
              by (f_equal ; omega)
          end.
          rewrite substP2 by omega.
          eapply meta_conv.
          * eapply type_Rel.
            eapply wf_subst ; eassumption.
          * f_equal.
            erewrite safe_nth_lt.
            eapply safe_nth_subst_context.
      - cbn. apply type_Sort. eapply wf_subst ; eassumption.
      - cbn. eapply type_Prod ; esh.
      - cbn. eapply type_Lambda ; esh.
      - cbn.
        change ((B0 {0 := u0}) {#|Δ| := u})
          with ((B0 {0 := u0}) {0 + #|Δ| := u}).
        rewrite substP4. cbn.
        eapply type_App ; esh.
      - cbn. eapply type_Eq ; esh.
      - cbn. eapply type_Refl ; esh.
      - cbn.
        change (#|Δ|) with (0 + #|Δ|)%nat.
        rewrite substP4.
        replace (S (0 + #|Δ|)) with (1 + #|Δ|)%nat by omega.
        rewrite substP4.
        eapply type_J ; esh.
        + instantiate (1 := ne). instantiate (1 := nx0). cbn. unfold ssnoc.
          rewrite !subst_decl_svass. cbn.
          f_equal. f_equal. f_equal.
          * replace (S #|Δ|) with (1 + #|Δ|)%nat by omega.
            apply substP2. omega.
          * replace (S #|Δ|) with (1 + #|Δ|)%nat by omega.
            apply substP2. omega.
        + replace (S (S #|Δ|)) with (1 + (S (0 + #|Δ|)))%nat by omega.
          rewrite <- substP4.
          replace (1 + (0 + #|Δ|))%nat with (S (0 + #|Δ|))%nat by omega.
          change (sRefl (A0 {0 + #|Δ| := u}) (u0 {0 + #|Δ| := u}))
            with ((sRefl A0 u0){ 0 + #|Δ| := u}).
          rewrite <- substP4. reflexivity.
      - cbn. eapply type_Transport ; esh.
      - cbn. eapply type_Heq ; esh.
      - cbn. eapply type_HeqToEq ; esh.
      - cbn. eapply type_HeqRefl ; esh.
      - cbn. eapply type_HeqSym ; esh.
      - cbn. eapply type_HeqTrans with (B := B0{ #|Δ| := u }) (b := b{ #|Δ| := u }) ; esh.
      - cbn. eapply type_HeqTransport ; esh.
      - cbn. eapply type_CongProd ; esh.
        cbn. f_equal.
        + rewrite <- substP2 by omega.
          change (S #|Δ|) with (0 + (S #|Δ|))%nat at 1.
          rewrite substP4. cbn. reflexivity.
        + rewrite <- substP2 by omega.
          change (S #|Δ|) with (0 + (S #|Δ|))%nat at 1.
          rewrite substP4. cbn. reflexivity.
      - cbn. eapply type_CongLambda ; esh.
        + cbn. f_equal.
          * rewrite <- substP2 by omega.
            change (S #|Δ|) with (0 + (S #|Δ|))%nat at 1.
            rewrite substP4. cbn. reflexivity.
          * rewrite <- substP2 by omega.
            change (S #|Δ|) with (0 + (S #|Δ|))%nat at 1.
            rewrite substP4. cbn. reflexivity.
        + cbn. f_equal.
          * rewrite <- substP2 by omega.
            change (S #|Δ|) with (0 + (S #|Δ|))%nat at 1.
            rewrite substP4. cbn. reflexivity.
          * rewrite <- substP2 by omega.
            change (S #|Δ|) with (0 + (S #|Δ|))%nat at 1.
            rewrite substP4. cbn. reflexivity.
          * rewrite <- substP2 by omega.
            change (S #|Δ|) with (0 + (S #|Δ|))%nat at 1.
            rewrite substP4. cbn. reflexivity.
          * rewrite <- substP2 by omega.
            change (S #|Δ|) with (0 + (S #|Δ|))%nat at 1.
            rewrite substP4. cbn. reflexivity.
      - cbn.
        change #|Δ| with (0 + #|Δ|)%nat.
        rewrite 2!substP4. cbn.
        eapply type_CongApp ; esh.
        cbn. f_equal.
        + rewrite <- substP2 by omega.
          change (S #|Δ|) with (0 + (S #|Δ|))%nat at 1.
          rewrite substP4. cbn. reflexivity.
        + rewrite <- substP2 by omega.
          change (S #|Δ|) with (0 + (S #|Δ|))%nat at 1.
          rewrite substP4. cbn. reflexivity.
      - cbn. eapply type_CongEq ; esh.
      - cbn. eapply type_CongRefl ; esh.
      - cbn. eapply type_EqToHeq ; esh.
      - cbn. eapply type_HeqTypeEq ; esh.
      - cbn. eapply type_Pack ; esh.
      - cbn. eapply @type_ProjT1 with (A2 := A2{#|Δ| := u}) ; esh.
      - cbn. eapply @type_ProjT2 with (A1 := A1{#|Δ| := u}) ; esh.
      - cbn. eapply type_ProjTe ; esh.
      - cbn. erewrite subst_ind_type by eassumption.
        eapply type_Ind.
        + now eapply wf_subst.
        + eassumption.
      - cbn. eapply type_conv ; esh.
    }

  (* cong_subst *)
  - { intros hg hu.
      dependent destruction h.
      - constructor. esh.
      - constructor. esh.
      - eapply eq_transitivity ; esh.
      - cbn.
        change #|Δ| with (0 + #|Δ|)%nat.
        rewrite 2!substP4. cbn.
        eapply eq_beta ; esh.
      - cbn.
        change #|Δ| with (0 + #|Δ|)%nat.
        rewrite substP4.
        replace (S (0 + #|Δ|)) with (1 + #|Δ|)%nat by omega.
        rewrite substP4.
        eapply eq_JRefl ; esh.
        + instantiate (1 := ne). instantiate (1 := nx0). cbn. unfold ssnoc.
          rewrite !subst_decl_svass. cbn.
          f_equal. f_equal. f_equal.
          * replace (S #|Δ|) with (1 + #|Δ|)%nat by omega.
            apply substP2. omega.
          * replace (S #|Δ|) with (1 + #|Δ|)%nat by omega.
            apply substP2. omega.
        + replace (S (S #|Δ|)) with (1 + (S (0 + #|Δ|)))%nat by omega.
          rewrite <- substP4.
          replace (1 + (0 + #|Δ|))%nat with (S (0 + #|Δ|))%nat by omega.
          change (sRefl (A0 {0 + #|Δ| := u}) (u0 {#|Δ| := u}))
            with ((sRefl A0 u0){ 0 + #|Δ| := u}).
          rewrite <- substP4. reflexivity.
      - cbn. eapply eq_TransportRefl ; esh.
      - eapply eq_conv ; esh.
      - cbn. eapply cong_Prod ; esh.
      - cbn. eapply cong_Lambda ; esh.
      - cbn. change #|Δ| with (0 + #|Δ|)%nat.
        rewrite substP4. cbn.
        eapply cong_App ; esh.
      - cbn. eapply cong_Eq ; esh.
      - cbn. eapply cong_Refl ; esh.
      - cbn.
        change #|Δ| with (0 + #|Δ|)%nat.
        rewrite substP4.
        replace (S (0 + #|Δ|)) with (1 + #|Δ|)%nat by omega.
        rewrite substP4.
        eapply cong_J ; esh.
        + instantiate (1 := ne). instantiate (1 := nx0). cbn. unfold ssnoc.
          rewrite !subst_decl_svass. cbn.
          f_equal. f_equal. f_equal.
          * replace (S #|Δ|) with (1 + #|Δ|)%nat by omega.
            apply substP2. omega.
          * replace (S #|Δ|) with (1 + #|Δ|)%nat by omega.
            apply substP2. omega.
        + replace (S (S #|Δ|)) with (1 + (S (0 + #|Δ|)))%nat by omega.
          rewrite <- substP4.
          replace (1 + (0 + #|Δ|))%nat with (S (0 + #|Δ|))%nat by omega.
          change (sRefl (A1 {0 + #|Δ| := u}) (u1 {0 + #|Δ| := u}))
            with ((sRefl A1 u1){ 0 + #|Δ| := u}).
          rewrite <- substP4. reflexivity.
      - cbn. eapply cong_Transport ; esh.
      - cbn. eapply cong_Heq ; esh.
      - cbn. eapply cong_Pack ; esh.
      - cbn. eapply cong_HeqToEq ; esh.
      - cbn. eapply cong_HeqRefl ; esh.
      - cbn. eapply cong_HeqSym ; esh.
      - cbn. eapply cong_HeqTrans with (B := B0{ #|Δ| := u }) (b := b{ #|Δ| := u }) ; esh.
      - cbn. eapply cong_HeqTransport ; esh.
      - cbn. eapply cong_CongProd ; esh.
        cbn. f_equal.
        + rewrite <- substP2 by omega.
          replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
          rewrite substP4. cbn. reflexivity.
        + rewrite <- substP2 by omega.
          replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
          rewrite substP4. cbn. reflexivity.
      - cbn. eapply cong_CongLambda ; esh.
        + cbn. f_equal.
          * rewrite <- substP2 by omega.
            replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
            rewrite substP4. cbn. reflexivity.
          * rewrite <- substP2 by omega.
            replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
            rewrite substP4. cbn. reflexivity.
        + cbn. f_equal.
          * rewrite <- substP2 by omega.
            replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
            rewrite substP4. cbn. reflexivity.
          * rewrite <- substP2 by omega.
            replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
            rewrite substP4. cbn. reflexivity.
          * rewrite <- substP2 by omega.
            replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
            rewrite substP4. cbn. reflexivity.
          * rewrite <- substP2 by omega.
            replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
            rewrite substP4. cbn. reflexivity.
      - cbn. change #|Δ| with (0 + #|Δ|)%nat.
        rewrite !substP4. cbn.
        eapply cong_CongApp ; esh.
        cbn. f_equal.
        + rewrite <- substP2 by omega.
          replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
          rewrite substP4. cbn. reflexivity.
        + rewrite <- substP2 by omega.
          replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
          rewrite substP4. cbn. reflexivity.
      - cbn. eapply cong_CongEq ; esh.
      - cbn. eapply cong_CongRefl ; esh.
      - cbn. eapply cong_EqToHeq ; esh.
      - cbn. eapply cong_HeqTypeEq ; esh.
      - cbn. eapply cong_ProjT1 with (A2 := A2{ #|Δ| := u }) ; esh.
      - cbn. eapply cong_ProjT2 with (A1 := A1{ #|Δ| := u }) ; esh.
      - cbn. eapply cong_ProjTe ; esh.
      - cbn. eapply eq_HeqToEqRefl ; esh.
    }

  (* wf_subst *)
  - { intros hg hu.
      destruct Δ.
      - cbn. dependent destruction h. assumption.
      - dependent destruction h. cbn. rewrite subst_decl_svass. econstructor.
        + eapply wf_subst ; eassumption.
        + esh.
    }

  Unshelve.
  all: try rewrite !length_cat ; try rewrite !subst_context_length ; omega.
Defined.

Corollary typing_subst :
  forall {Σ Γ t A B u n},
    type_glob Σ ->
    Σ ;;; Γ ,, svass n A |-i t : B ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i t{ 0 := u } : B{ 0 := u }.
Proof.
  intros Σ Γ t A B u n hg ht hu.
  eapply @type_subst with (Δ := []) ; eassumption.
Defined.

Corollary typing_subst2 :
  forall {Σ Γ t A B C na nb u v},
    type_glob Σ ->
    Σ ;;; Γ ,, svass na A ,, svass nb B |-i t : C ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i v : B{ 0 := u } ->
    Σ ;;; Γ |-i t{ 1 := u }{ 0 := v } : C{ 1 := u }{ 0 := v }.
Proof.
  intros Σ Γ t A B C na nb u v hg ht hu hv.
  eapply @type_subst with (Δ := []).
  - eapply @type_subst with (Δ := [ svass nb B ]).
    + exact ht.
    + assumption.
    + assumption.
  - assumption.
  - cbn. assumption.
Defined.

Lemma cong_substs :
  forall {Σ Γ Δ t A nx B},
  Σ ;;; Γ ,, svass nx B ,,, Δ |-i t : A ->
  type_glob Σ ->
  forall {u1 u2},
    Σ ;;; Γ |-i u1 = u2 : B ->
    Σ ;;; Γ |-i u1 : B ->
    Σ ;;; Γ ,,, subst_context u1 Δ
    |-i t{ #|Δ| := u1 }
     = t{ #|Δ| := u2 } : A{ #|Δ| := u1 }.
Proof.
  intros Σ Γ Δ t A nx B ht hg.
  dependent induction ht ; intros uu1 uu2 huu huu1.
  - cbn. case_eq (#|Δ| ?= n) ; intro e ; bprop e.
    + assert (h : n >= #|Δ|) by omega.
      rewrite safe_nth_ge' with (h0 := h).
      set (ge := ge_sub isdecl h).
      rewrite substP3 by omega.
      generalize ge.
      replace (n - #|Δ|) with 0 by omega.
      intro ge'. cbn.
      subst.
      replace #|Δ| with #|subst_context uu1 Δ|
        by (now rewrite subst_context_length).
      eapply @cong_lift with (Ξ := []) (Δ := subst_context uu1 Δ).
      * cbn. assumption.
      * assumption.
      * eapply wf_subst ; eassumption.
    + assert (h : n >= #|Δ|) by omega.
      rewrite safe_nth_ge' with (h0 := h).
      set (ge := ge_sub isdecl h).
      destruct n ; try easy.
      rewrite substP3 by omega.
      generalize ge.
      replace (S n - #|Δ|) with (S (n - #|Δ|)) by omega.
      cbn. intro ge'.
      eapply meta_eqconv.
      * eapply eq_reflexivity. eapply type_Rel. eapply wf_subst ; eassumption.
      * erewrite safe_nth_ge'.
        f_equal. f_equal. eapply safe_nth_cong_irr.
        rewrite subst_context_length. reflexivity.
    + assert (h : n < #|Δ|) by omega.
      rewrite @safe_nth_lt with (isdecl' := h).
      match goal with
      | |- _ ;;; _ |-i _ = _ : ?t{?d := ?u} =>
        replace (subst u d t) with (t{((S n) + (#|Δ| - (S n)))%nat := u})
          by (f_equal ; omega)
      end.
      rewrite substP2 by omega.
      eapply meta_eqconv.
      * eapply eq_reflexivity. eapply type_Rel.
        eapply wf_subst ; eassumption.
      * f_equal.
        erewrite safe_nth_lt.
        eapply safe_nth_subst_context.
  - cbn. apply eq_reflexivity. apply type_Sort.
    eapply wf_subst ; eassumption.
  - cbn. eapply cong_Prod.
    + now apply IHht1.
    + specialize (IHht2 Γ0 (Δ ,, svass n t) b (sSort s2) nx B eq_refl).
      apply IHht2 ; assumption.
  - cbn. eapply cong_Lambda.
    + apply IHht1 ; eassumption.
    + eapply IHht2 with (Δ0 := Δ ,, svass n t) (A := sSort s2)
      ; [ reflexivity | eassumption .. ].
    + eapply IHht3 with (Δ0 := Δ ,, svass n t)
      ; [ reflexivity | eassumption .. ].
  - cbn. change #|Δ| with (0 + #|Δ|)%nat.
    rewrite substP4. cbn.
    eapply cong_App.
    + apply IHht1 ; eassumption.
    + eapply IHht2 with (Δ0 := Δ ,, svass n A) (A0 := sSort s2)
      ; [ reflexivity | eassumption .. ].
    + apply IHht3 ; eassumption.
    + apply IHht4 ; eassumption.
  - cbn. eapply cong_Eq.
    + apply IHht1 ; eassumption.
    + apply IHht2 ; eassumption.
    + apply IHht3 ; eassumption.
  - cbn. eapply cong_Refl.
    + apply IHht1 ; eassumption.
    + apply IHht2 ; eassumption.
  - cbn. change #|Δ| with (0 + #|Δ|)%nat.
    rewrite substP4.
    replace (S (0 + #|Δ|)) with (1 + #|Δ|)%nat by omega.
    rewrite substP4.
    eapply cong_J.
    + apply IHht1 ; eassumption.
    + apply IHht2 ; eassumption.
    + apply IHht3 ; eassumption.
    + eapply meta_eqctx_conv.
      * eapply IHht4
          with (Δ0 := (Δ ,, svass nx A),, svass ne (sEq (lift0 1 A) (lift0 1 u) (sRel 0)))
               (A0 := sSort s2)
        ; [ reflexivity | eassumption .. ].
      * instantiate (1 := ne). instantiate (1 := nx). cbn. unfold ssnoc.
        rewrite !subst_decl_svass. cbn. f_equal.
        f_equal. f_equal.
        -- replace (S #|Δ|) with (1 + #|Δ|)%nat by omega.
           apply substP2. omega.
        -- replace (S #|Δ|) with (1 + #|Δ|)%nat by omega.
           apply substP2. omega.
    + apply IHht5 ; eassumption.
    + eapply meta_eqconv.
      * apply IHht6 ; eassumption.
      * replace (S (S #|Δ|)) with (1 + (S (0 + #|Δ|)))%nat by omega.
        rewrite <- substP4.
        replace (1 + (0 + #|Δ|))%nat with (S (0 + #|Δ|))%nat by omega.
        change (sRefl (A {0 + #|Δ| := uu1}) (u {0 + #|Δ| := uu1}))
          with ((sRefl A u){ 0 + #|Δ| := uu1}).
        rewrite <- substP4. reflexivity.
  - cbn. eapply cong_Transport.
    + apply IHht1 ; eassumption.
    + apply IHht2 ; eassumption.
    + apply IHht3 ; eassumption.
    + apply IHht4 ; eassumption.
  - cbn. eapply cong_Heq.
    + apply IHht1 ; eassumption.
    + apply IHht2 ; eassumption.
    + apply IHht3 ; eassumption.
    + apply IHht4 ; eassumption.
  - cbn. eapply cong_HeqToEq.
    + apply IHht1 ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply type_subst ; eassumption.
    + eapply type_subst ; eassumption.
  - cbn. eapply cong_HeqRefl.
    + apply IHht1 ; eassumption.
    + apply IHht2 ; eassumption.
  - cbn. eapply cong_HeqSym.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply type_subst ; eassumption.
    + eapply type_subst ; eassumption.
    + apply IHht5 ; eassumption.
  - cbn. eapply cong_HeqTrans with (B := B{#|Δ| := uu1}).
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply type_subst ; eassumption.
    + eapply type_subst ; eassumption.
    + eapply type_subst ; eassumption.
    + apply IHht7 ; eassumption.
    + apply IHht8 ; eassumption.
  - cbn. eapply cong_HeqTransport.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + apply IHht3 ; eassumption.
    + apply IHht4 ; eassumption.
  - cbn. eapply cong_CongProd.
    + apply IHht1 ; eassumption.
    + eapply meta_eqconv.
      * eapply IHht2 with (Δ0 := Δ,, svass np (sPack A1 A2))
        ; [ reflexivity | eassumption .. ].
      * cbn. f_equal.
        -- rewrite <- substP2 by omega.
           replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
           rewrite substP4. cbn. reflexivity.
        -- rewrite <- substP2 by omega.
           replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
           rewrite substP4. cbn. reflexivity.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply meta_eqctx_conv.
      * eapply IHht5 with (Δ0 := Δ,, svass nx A1) (A := sSort z)
        ; [ reflexivity | eassumption .. ].
      * cbn. rewrite subst_decl_svass. reflexivity.
    + eapply meta_eqctx_conv.
      * eapply IHht6 with (Δ0 := Δ,, svass ny A2) (A := sSort z)
        ; [ reflexivity | eassumption .. ].
      * cbn. rewrite subst_decl_svass. reflexivity.
  - cbn. eapply cong_CongLambda.
    + apply IHht1 ; eassumption.
    + eapply meta_eqconv.
      * eapply IHht2 with (Δ0 := Δ,, svass np (sPack A1 A2))
        ; [ reflexivity | eassumption .. ].
      * cbn. f_equal.
        -- rewrite <- substP2 by omega.
           replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
           rewrite substP4. cbn. reflexivity.
        -- rewrite <- substP2 by omega.
           replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
           rewrite substP4. cbn. reflexivity.
    + eapply meta_eqconv.
      * eapply IHht3 with (Δ0 := Δ,, svass np (sPack A1 A2))
        ; [ reflexivity | eassumption .. ].
      * cbn. f_equal.
        -- rewrite <- substP2 by omega.
           replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
           rewrite substP4. cbn. reflexivity.
        -- rewrite <- substP2 by omega.
           replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
           rewrite substP4. cbn. reflexivity.
        -- rewrite <- substP2 by omega.
           replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
           rewrite substP4. cbn. reflexivity.
        -- rewrite <- substP2 by omega.
           replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
           rewrite substP4. cbn. reflexivity.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply meta_eqconv.
      * eapply IHht6 with (Δ0 := Δ,, svass nx A1)
        ; [ reflexivity | eassumption .. ].
      * cbn. reflexivity.
    + eapply meta_eqconv.
      * eapply IHht7 with (Δ0 := Δ,, svass ny A2)
        ; [ reflexivity | eassumption .. ].
      * reflexivity.
    + eapply IHht8 with (Δ0 := Δ,, svass nx A1)
      ; [ reflexivity | eassumption .. ].
    + eapply IHht9 with (Δ0 := Δ,, svass ny A2)
      ; [ reflexivity | eassumption .. ].
  - cbn. change #|Δ| with (0 + #|Δ|)%nat.
    rewrite 2!substP4. cbn.
    eapply cong_CongApp.
    + eapply IHht1 ; eassumption.
    + eapply meta_eqconv.
      * eapply IHht2 with (Δ0 := Δ,, svass np (sPack A1 A2))
        ; [ reflexivity | eassumption .. ].
      * cbn. f_equal.
        -- rewrite <- substP2 by omega.
           replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
           rewrite substP4. cbn. reflexivity.
        -- rewrite <- substP2 by omega.
           replace (S #|Δ|) with (0 + (S #|Δ|))%nat by omega.
           rewrite substP4. cbn. reflexivity.
    + apply IHht3 ; eassumption.
    + apply IHht4 ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply meta_eqconv.
      * eapply IHht7 with (Δ0 := Δ,, svass nx A1)
        ; [ reflexivity | eassumption .. ].
      * cbn. reflexivity.
    + eapply meta_eqconv.
      * eapply IHht8 with (Δ0 := Δ,, svass ny A2)
        ; [ reflexivity | eassumption .. ].
      * reflexivity.
    + eapply @type_subst with (A := sProd nx A1 B1) ; eassumption.
    + eapply @type_subst with (A := sProd ny A2 B2) ; eassumption.
    + eapply type_subst ; eassumption.
    + eapply type_subst ; eassumption.
  - cbn. eapply cong_CongEq.
    + apply IHht1 ; eassumption.
    + apply IHht2 ; eassumption.
    + apply IHht3 ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply type_subst ; eassumption.
    + eapply type_subst ; eassumption.
    + eapply type_subst ; eassumption.
    + eapply type_subst ; eassumption.
  - cbn. eapply cong_CongRefl.
    + apply IHht1 ; eassumption.
    + apply IHht2 ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply type_subst ; eassumption.
    + eapply type_subst ; eassumption.
  - cbn. eapply cong_EqToHeq.
    + apply IHht1 ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply type_subst ; eassumption.
    + eapply type_subst ; eassumption.
  - cbn. eapply cong_HeqTypeEq.
    + apply IHht1 ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply type_subst ; eassumption.
    + eapply type_subst ; eassumption.
  - cbn. eapply cong_Pack.
    + apply IHht1 ; eassumption.
    + apply IHht2 ; eassumption.
  - cbn. eapply cong_ProjT1 with (A2 :=  A2 {#|Δ| := uu1}).
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + apply IHht3 ; eassumption.
  - cbn. eapply cong_ProjT2 with (A1 :=  A1 {#|Δ| := uu1}).
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + apply IHht3 ; eassumption.
  - cbn. eapply cong_ProjTe.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + eapply @type_subst with (A := sSort s) ; eassumption.
    + apply IHht3 ; eassumption.
  - cbn. eapply eq_reflexivity.
    erewrite subst_ind_type by eassumption.
    eapply type_Ind.
    + eapply wf_subst ; eassumption.
    + eassumption.
  - eapply eq_conv.
    + eapply IHht1 ; assumption.
    + eapply @cong_subst with (A := sSort s) ; eassumption.
  Unshelve.
  all: try rewrite !length_cat ; try rewrite !subst_context_length ; omega.
Defined.

Corollary full_cong_subst :
  forall {Σ Γ nx B Δ t1 t2 u1 u2 A},
    type_glob Σ ->
    Σ ;;; Γ ,, svass nx B ,,, Δ |-i t1 = t2 : A ->
    Σ ;;; Γ |-i u1 = u2 : B ->
    Σ ;;; Γ ,, svass nx B ,,, Δ |-i t2 : A ->
    Σ ;;; Γ |-i u1 : B ->
    Σ ;;; Γ ,,, subst_context u1 Δ |-i
    t1{ #|Δ| := u1 } = t2{ #|Δ| := u2 } : A{ #|Δ| := u1 }.
Proof.
  intros Σ Γ nx B Δ t1 t2 u1 u2 A hg ht hu ht2 hu1.
  eapply eq_transitivity.
  - exact (cong_subst ht hg hu1).
  - exact (cong_substs ht2 hg hu hu1).
Defined.

Lemma pre_cong_subst1 :
  forall {Σ Γ t1 t2 A B u1 u2 n},
    type_glob Σ ->
    Σ ;;; Γ ,, svass n A |-i t1 = t2 : B ->
    Σ ;;; Γ |-i u1 = u2 : A ->
    Σ ;;; Γ ,, svass n A |-i t2 : B ->
    Σ ;;; Γ |-i u1 : A ->
    Σ ;;; Γ |-i t1{ 0 := u1 } = t2{ 0 := u2 } : B{ 0 := u1 }.
Proof.
  intros Σ Γ t1 t2 A B u1 u2 n hg ht hu ht2 hu1.
  eapply @full_cong_subst with (Δ := []) ; eassumption.
Defined.

Lemma pre_cong_subst2 :
  forall {Σ Γ t1 t2 A B C na nb u1 u2 v1 v2},
    type_glob Σ ->
    Σ ;;; Γ ,, svass na A ,, svass nb B |-i t1 = t2 : C ->
    Σ ;;; Γ |-i u1 = u2 : A ->
    Σ ;;; Γ |-i v1 = v2 : B{ 0 := u1 } ->
    Σ ;;; Γ ,, svass na A ,, svass nb B |-i t2 : C ->
    Σ ;;; Γ |-i u1 : A ->
    Σ;;; Γ,, svass nb (B {0 := u1}) |-i t2 {1 := u2} : C {1 := u1} ->
    Σ ;;; Γ |-i v1 : B{ 0 := u1 } ->
    Σ ;;; Γ |-i t1{ 1 := u1 }{ 0 := v1 }
             = t2{ 1 := u2 }{ 0 := v2 } : C{ 1 := u1 }{ 0 := v1 }.
Proof.
  intros Σ Γ t1 t2 A B C na nb u1 u2 v1 v2 hg ht hu hv ht2 hu1 hst2 hv1.
  eapply @full_cong_subst with (Δ := []).
  - assumption.
  - eapply @full_cong_subst with (Δ := [ svass nb B ]).
    + assumption.
    + exact ht.
    + assumption.
    + assumption.
    + assumption.
  - cbn. assumption.
  - cbn. assumption.
  - cbn. assumption.
Defined.

Inductive eqctx Σ : scontext -> scontext -> Type :=
| eqnil : eqctx Σ nil nil
| eqsnoc Γ na A Δ nb B s :
    eqctx Σ Γ Δ ->
    Σ ;;; Γ |-i A = B : sSort s ->
    eqctx Σ (Γ ,, svass na A) (Δ ,, svass nb B).

Fact eqctx_refl :
  forall {Σ Γ},
    wf Σ Γ ->
    eqctx Σ Γ Γ.
Proof.
  intros Σ Γ h.
  dependent induction Γ.
  - constructor.
  - dependent destruction h.
    econstructor.
    + now apply IHΓ.
    + now apply eq_reflexivity.
Defined.

(* Lemma ctx_conv : *)
(*   forall {Σ Γ Δ}, *)
(*     eqctx Σ Γ Δ -> *)
(*     forall {t A}, *)
(*       Σ ;;; Γ |-i t : A -> *)
(*       Σ ;;; Δ |-i t : A. *)
(* Proof. *)
  (* intros Σ Γ Δ eq. *)
  (* dependent induction eq ; intros t C h. *)
  (* - assumption. *)
  (* - dependent induction h. *)
  (*   + eapply type_Rel. *)
(* Admitted. *)

Lemma ctx_conv :
  forall {Σ Γ Δ t A},
    Σ ;;; Γ |-i t : A ->
    eqctx Σ Γ Δ ->
    Σ ;;; Δ |-i t : A.
Admitted.

Lemma eqctx_conv :
  forall {Σ Γ Δ t u A},
    Σ ;;; Γ |-i t = u : A ->
    eqctx Σ Γ Δ ->
    Σ ;;; Δ |-i t = u : A.
Admitted.

Lemma istype_type :
  forall {Σ Γ t T},
    type_glob Σ ->
    Σ ;;; Γ |-i t : T ->
    ∑ s, Σ ;;; Γ |-i T : sSort s.
Proof.
  intros Σ Γ t T hg H.
  induction H.
  - revert n isdecl. induction w ; intros n isdecl.
    + cbn in isdecl. easy.
    + destruct n.
      * cbn.
        exists s. change (sSort s) with (lift0 1 (sSort s)).
        eapply typing_lift01 ; eassumption.
      * assert (isdecl' : n < #|Γ|).
        -- auto with arith.
        -- destruct (IHw n isdecl') as [s' hh].
           exists s'. change (sSort s') with (lift0 1 (sSort s')).
           (* Take out as a lemma? *)
           assert (eq : forall t, lift0 (S (S n)) t = lift0 1 (lift0 (S n) t)).
           { intro t'. rewrite lift_lift. reflexivity. }
           rewrite eq. clear eq.
           eapply typing_lift01.
           ++ assumption.
           ++ erewrite eq_safe_nth. eassumption.
           ++ eassumption.
  - exists (succ_sort (succ_sort s)). now apply type_Sort.
  - exists (succ_sort (max_sort s1 s2)). apply type_Sort. apply (typing_wf H).
  - exists (max_sort s1 s2). apply type_Prod.
    + assumption.
    + eapply ctx_conv ; [ eassumption |].
      econstructor.
      * apply eqctx_refl. now apply (typing_wf H).
      * apply eq_reflexivity. eassumption.
  - exists s2. change (sSort s2) with ((sSort s2){ 0 := u }).
    eapply typing_subst ; eassumption.
  - exists (succ_sort s). apply type_Sort. apply (typing_wf H).
  - exists s. now apply type_Eq.
  - exists s2.
    change (sSort s2) with ((sSort s2){1 := v}{0 := p}).
    eapply typing_subst2.
    + assumption.
    + eassumption.
    + assumption.
    + cbn. rewrite !lift_subst, lift00.
      assumption.
  - eexists. eassumption.
  - exists (succ_sort (succ_sort s)). apply type_Sort. apply (typing_wf H).
  - exists s. apply type_Eq ; assumption.
  - exists (succ_sort s). apply type_Heq ; assumption.
  - exists (succ_sort s). apply type_Heq ; assumption.
  - exists (succ_sort s). apply type_Heq ; assumption.
  - exists (succ_sort s). apply type_Heq. all: try assumption.
    eapply type_Transport ; eassumption.
  - exists (succ_sort (succ_sort (max_sort s z))).
    apply type_Heq.
    + eapply type_Sort. apply (typing_wf H).
    + eapply type_Sort. apply (typing_wf H).
    + apply type_Prod ; assumption.
    + apply type_Prod ; assumption.
  - exists (succ_sort (max_sort s z)). apply type_Heq.
    + apply type_Prod ; assumption.
    + apply type_Prod ; assumption.
    + eapply type_Lambda ; eassumption.
    + eapply type_Lambda ; eassumption.
  - exists (succ_sort z). apply type_Heq.
    + change (sSort z) with ((sSort z){ 0 := v1 }).
      eapply typing_subst ; eassumption.
    + change (sSort z) with ((sSort z){ 0 := v2 }).
      eapply typing_subst ; eassumption.
    + eapply type_App ; eassumption.
    + eapply type_App ; eassumption.
  - exists (succ_sort (succ_sort s)). apply type_Heq.
    + apply type_Sort ; apply (typing_wf H).
    + apply type_Sort ; apply (typing_wf H).
    + apply type_Eq ; assumption.
    + apply type_Eq ; assumption.
  - exists (succ_sort s). apply type_Heq.
    + apply type_Eq ; assumption.
    + apply type_Eq ; assumption.
    + eapply type_Refl ; eassumption.
    + eapply type_Refl ; eassumption.
  - exists (succ_sort s). apply type_Heq ; assumption.
  - exists (succ_sort s). eapply type_Eq ; try assumption.
    apply type_Sort. apply (typing_wf H).
  - exists (succ_sort s). apply type_Sort. apply (typing_wf H).
  - exists s. assumption.
  - exists s. assumption.
  - exists (succ_sort s). apply type_Heq ; try assumption.
    + eapply type_ProjT1 ; eassumption.
    + eapply @type_ProjT2 with (A1 := A1) ; eassumption.
  - eexists. (* Now we need the weakening for global_context *)
  - eexists. eapply type_Sort. assumption.
  - exists s. assumption.
Defined.

Lemma eq_typing :
  forall {Σ Γ t u T},
    Σ ;;; Γ |-i t = u : T ->
    (Σ ;;; Γ |-i t : T) * (Σ ;;; Γ |-i u : T).
Proof.
  intros Σ Γ t u T h.
  induction h ;
    repeat match goal with
           | H : ?A * ?B |- _ => destruct H
           end ;
    split ; try (now constructor + easy).
  all: try (econstructor ; eassumption).
  - eapply type_conv.
    + econstructor ; try eassumption.
      eapply type_conv.
      * econstructor ; eassumption.
      * econstructor ; eassumption.
      * apply eq_reflexivity. constructor ; assumption.
    + instantiate (1 := s2).
      change (sSort s2) with ((sSort s2){ 0 := u }).
      eapply typing_subst ; eassumption.
    + apply eq_reflexivity.
      change (sSort s2) with ((sSort s2){ 0 := u }).
      eapply typing_subst ; eassumption.
  - eapply typing_subst ; eassumption.
  - econstructor ; try eassumption.
    econstructor ; eassumption.
  - econstructor ; try eassumption.
    econstructor ; try eassumption.
    econstructor. apply (typing_wf t1).
  - constructor ; try eassumption.
    eapply ctx_conv.
    + eassumption.
    + econstructor.
      * apply eqctx_refl. now apply (typing_wf pi1_0).
      * eassumption.
  - eapply type_conv.
    + econstructor.
      * eassumption.
      * eapply ctx_conv ; [ eassumption |].
        econstructor.
        -- eapply eqctx_refl. now apply (typing_wf pi1_1).
        -- eassumption.
      * eapply ctx_conv.
        -- eapply type_conv ; eassumption.
        -- econstructor.
           ++ apply eqctx_refl. now apply (typing_wf pi1_1).
           ++ eassumption.
    + econstructor.
      * eassumption.
      * eapply ctx_conv ; [ eassumption |].
        econstructor.
        -- apply eqctx_refl. now apply (typing_wf pi1_1).
        -- apply eq_reflexivity. eassumption.
    + apply eq_symmetry. apply cong_Prod.
      * assumption.
      * eapply eqctx_conv ; [ eassumption |].
        econstructor.
        -- apply eqctx_refl. now apply (typing_wf pi1_1).
        -- apply eq_reflexivity. eassumption.
  - econstructor.
    + econstructor.
      * eassumption.
      * eapply ctx_conv ; [ eassumption |].
        econstructor.
        -- apply eqctx_refl. now apply (typing_wf pi1_2).
        -- eassumption.
      * econstructor.
        -- eassumption.
        -- econstructor.
           ++ eassumption.
           ++ eapply ctx_conv ; [ eassumption |].
              econstructor.
              ** apply eqctx_refl. now apply (typing_wf pi1_2).
              ** eassumption.
        -- eapply cong_Prod ; eassumption.
      * econstructor ; eassumption.
    + instantiate (1 := s2).
      change (sSort s2) with ((sSort s2){ 0 := u1 }).
      eapply typing_subst ; eassumption.
    + change (sSort s2) with ((sSort s2){0 := u2}).
      eapply pre_cong_subst1.
      * eapply eq_symmetry. eassumption.
      * eapply eq_symmetry. assumption.
      * assumption.
      * assumption.
  - constructor.
    + assumption.
    + eapply type_conv ; eassumption.
    + eapply type_conv ; eassumption.
  - eapply type_conv ; [ eapply type_Refl | .. ].
    + eassumption.
    + eapply type_conv ; eassumption.
    + constructor ; eassumption.
    + apply eq_symmetry. apply cong_Eq ; assumption.
  - eapply type_conv ; [ econstructor | .. ].
    1: eassumption.
    all: try (econstructor ; eassumption).
    + eapply ctx_conv ; [ eassumption |].
      econstructor.
      * econstructor.
        -- apply eqctx_refl. now apply (typing_wf pi1_2).
        -- eassumption.
      * eapply cong_Eq.
        -- match goal with
           | |- _ ;;; _ |-i _ = _ : ?S =>
             change S with (lift0 1 S)
           end.
           eapply cong_lift01 ; eassumption.
        -- eapply cong_lift01 ; eassumption.
        -- apply eq_reflexivity.
           eapply type_conv ; [ eapply type_Rel | .. ].
           ++ econstructor.
              ** now apply (typing_wf pi1_2).
              ** eassumption.
           ++ instantiate (1 := s1).
              change (sSort s1) with (lift0 1 (sSort s1)).
              eapply typing_lift01 ; eassumption.
           ++ cbn. apply eq_reflexivity.
              change (sSort s1) with (lift0 1 (sSort s1)).
              eapply typing_lift01 ; eassumption.
    + eapply type_conv ; [ eassumption | .. ].
      * econstructor.
        -- eassumption.
        -- eapply type_conv ; eassumption.
        -- eapply type_conv ; eassumption.
      * apply cong_Eq ; eassumption.
    + eapply type_conv ; [ eassumption | .. ].
      * instantiate (1 := s2).
        change (sSort s2) with ((sSort s2){ 1 := u2 }{ 0 := sRefl A2 u2 }).
        eapply typing_subst2.
        -- eassumption.
        -- eassumption.
        -- cbn. rewrite !lift_subst, lift00.
           eapply type_conv ; [ eapply type_Refl | .. ].
           ++ eassumption.
           ++ eapply type_conv ; eassumption.
           ++ eapply type_Eq ; eassumption.
           ++ apply eq_symmetry. apply cong_Eq.
              ** assumption.
              ** assumption.
              ** apply eq_reflexivity. assumption.
      * match goal with
        | |- _ ;;; _ |-i _ = _ : ?S =>
          change S with (S{1 := u1}{0 := sRefl A1 u1})
        end.
        eapply pre_cong_subst2.
        -- eassumption.
        -- assumption.
        -- cbn. rewrite !lift_subst, lift00.
           eapply cong_Refl ; eassumption.
        -- assumption.
        -- assumption.
        -- cbn. rewrite !lift_subst, lift00.
           eapply ctx_conv.
           ++ eapply @type_subst with (A := sSort s2) (Δ := [ svass ne (sEq (lift0 1 A1) (lift0 1 u1) (sRel 0)) ]).
              ** exact pi2_1.
              ** assumption.
           ++ cbn. rewrite subst_decl_svass. cbn. rewrite !lift_subst, lift00.
              econstructor.
              ** eapply eqctx_refl. eapply typing_wf. eassumption.
              ** eapply eq_symmetry. eapply cong_Eq.
                 all: try eapply eq_reflexivity.
                 all: eassumption.
        -- cbn. rewrite !lift_subst, lift00.
           eapply type_Refl ; eassumption.
    + match goal with
      | |- _ ;;; _ |-i _ : ?S =>
        change S with (S{1 := v1}{0 := p1})
      end.
      eapply typing_subst2.
      * eassumption.
      * assumption.
      * cbn. rewrite !lift_subst, lift00. assumption.
    + eapply eq_symmetry.
      match goal with
      | |- _ ;;; _ |-i _ = _ : ?S =>
        change S with (S{1 := v1}{0 := p1})
      end.
      eapply pre_cong_subst2.
      * eassumption.
      * assumption.
      * cbn. rewrite !lift_subst, lift00. assumption.
      * assumption.
      * assumption.
      * cbn. rewrite !lift_subst, lift00.
        eapply ctx_conv.
        -- eapply @type_subst with (A := sSort s2) (Δ := [ svass ne (sEq (lift0 1 A1) (lift0 1 u1) (sRel 0)) ]).
           ++ exact pi2_1.
           ++ assumption.
        -- cbn. rewrite subst_decl_svass. cbn. rewrite !lift_subst, lift00.
           econstructor.
           ++ eapply eqctx_refl. eapply typing_wf. eassumption.
           ++ eapply eq_symmetry. eapply cong_Eq.
              all: try eapply eq_reflexivity.
              all: eassumption.
      * cbn. rewrite !lift_subst, lift00.
        assumption.
  - eapply type_conv.
    + eapply type_Transport ; try eassumption.
      * eapply type_conv.
        -- eassumption.
        -- apply type_Eq.
           ++ apply type_Sort. eapply typing_wf. eassumption.
           ++ assumption.
           ++ assumption.
        -- eapply cong_Eq.
           ++ eapply eq_reflexivity.
              apply type_Sort. eapply typing_wf. eassumption.
           ++ assumption.
           ++ assumption.
      * eapply type_conv ; eassumption.
    + eassumption.
    + eapply eq_symmetry. assumption.
  - eapply type_Heq ; try assumption.
    + eapply type_conv ; eassumption.
    + eapply type_conv ; eassumption.
      Unshelve. 1-3: exact nAnon. cbn. omega.
  - eapply type_conv.
    + eapply type_HeqRefl ; try eassumption.
      eapply type_conv ; eassumption.
    + eapply type_Heq ; try assumption ; eassumption.
    + eapply eq_symmetry. eapply cong_Heq ; assumption.
  - eapply type_HeqTrans with (B := B) (b := b) ; eassumption.
  - eapply type_HeqTrans with (B := B) (b := b) ; eassumption.
  - eapply type_conv.
    + eapply type_HeqTransport ; [ .. | eassumption ] ; eassumption.
    + eapply type_Heq ; try eassumption.
      eapply type_Transport ; eassumption.
    + eapply eq_symmetry.
      eapply cong_Heq ; try eapply eq_reflexivity ; try eassumption.
      eapply cong_Transport ; try eapply eq_reflexivity ; eassumption.
  - eapply type_conv.
    + eapply type_CongProd ; try eassumption.
      eapply type_conv ; try eassumption.
      * eapply type_Heq.
        -- eapply type_Sort. eapply typing_wf. eassumption.
        -- eapply type_Sort. eapply typing_wf. eassumption.
        -- eapply @typing_subst with (B := sSort z).
           ++ eapply @type_lift
                with (A := sSort z)
                     (Δ := [ svass np (sPack A1 A2) ])
                     (Ξ := [ svass nx A1 ]).
              ** assumption.
              ** econstructor.
                 --- eapply typing_wf. eassumption.
                 --- eapply type_Pack ; eassumption.
           ++ cbn. eapply @type_ProjT1 with (A2 := lift0 1 A2).
              ** eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                 eapply type_Pack ; eassumption.
              ** eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                 eapply type_Pack ; eassumption.
              ** refine (type_Rel _ _ _ _ _).
                 --- econstructor.
                     +++ eapply typing_wf. eassumption.
                     +++ eapply type_Pack ; eassumption.
                 --- cbn. omega.
        -- eapply @typing_subst with (B := sSort z).
           ++ eapply @type_lift
                with (A := sSort z)
                     (Δ := [ svass np (sPack A1 A2) ])
                     (Ξ := [ svass ny A2 ]).
              ** assumption.
              ** econstructor.
                 --- eapply typing_wf. eassumption.
                 --- eapply type_Pack ; eassumption.
           ++ cbn. eapply @type_ProjT2 with (A1 := lift0 1 A1).
              ** eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                 eapply type_Pack ; eassumption.
              ** eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                 eapply type_Pack ; eassumption.
              ** refine (type_Rel _ _ _ _ _).
                 --- econstructor.
                     +++ eapply typing_wf. eassumption.
                     +++ eapply type_Pack ; eassumption.
                 --- cbn. omega.
      * eapply cong_Heq. all: try eapply eq_reflexivity.
        -- eapply type_Sort. eapply typing_wf. eassumption.
        -- eapply type_Sort. eapply typing_wf. eassumption.
        -- eapply @pre_cong_subst1 with (B := sSort z).
           ++ eapply @cong_lift
                with (A := sSort z)
                     (Δ := [ svass np (sPack A1 A2) ])
                     (Ξ := [ svass nx A1 ]).
              ** assumption.
              ** econstructor.
                 --- eapply typing_wf. eassumption.
                 --- eapply type_Pack ; eassumption.
           ++ cbn. eapply @cong_ProjT1 with (A2 := lift0 1 A2).
              ** eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                 eapply type_Pack ; eassumption.
              ** eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                 eapply type_Pack ; eassumption.
              ** eapply eq_reflexivity.
                 refine (type_Rel _ _ _ _ _).
                 --- econstructor.
                     +++ eapply typing_wf. eassumption.
                     +++ eapply type_Pack ; eassumption.
                 --- cbn. omega.
           ++ cbn. eapply @type_lift
                     with (A := sSort z)
                          (Δ := [ svass np (sPack A1 A2) ])
                          (Ξ := [ svass nx A1 ]).
              ** assumption.
              ** econstructor.
                 --- eapply typing_wf. eassumption.
                 --- eapply type_Pack ; eassumption.
           ++ cbn. eapply @type_ProjT1 with (A2 := lift0 1 A2).
              ** eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                 eapply type_Pack ; eassumption.
              ** eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                 eapply type_Pack ; eassumption.
              ** refine (type_Rel _ _ _ _ _).
                 --- econstructor.
                     +++ eapply typing_wf. eassumption.
                     +++ eapply type_Pack ; eassumption.
                 --- cbn. omega.
        -- eapply @pre_cong_subst1 with (B := sSort z).
           ++ eapply @cong_lift
                with (A := sSort z)
                     (Δ := [ svass np (sPack A1 A2) ])
                     (Ξ := [ svass ny A2 ]).
              ** assumption.
              ** econstructor.
                 --- eapply typing_wf. eassumption.
                 --- eapply type_Pack ; eassumption.
           ++ cbn. eapply @cong_ProjT2 with (A1 := lift0 1 A1).
              ** eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                 eapply type_Pack ; eassumption.
              ** eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                 eapply type_Pack ; eassumption.
              ** eapply eq_reflexivity.
                 refine (type_Rel _ _ _ _ _).
                 --- econstructor.
                     +++ eapply typing_wf. eassumption.
                     +++ eapply type_Pack ; eassumption.
                 --- cbn. omega.
           ++ cbn. eapply @type_lift
                     with (A := sSort z)
                          (Δ := [ svass np (sPack A1 A2) ])
                          (Ξ := [ svass ny A2 ]).
              ** assumption.
              ** econstructor.
                 --- eapply typing_wf. eassumption.
                 --- eapply type_Pack ; eassumption.
           ++ cbn. eapply @type_ProjT2 with (A1 := lift0 1 A1).
              ** eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                 eapply type_Pack ; eassumption.
              ** eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                 eapply type_Pack ; eassumption.
              ** refine (type_Rel _ _ _ _ _).
                 --- econstructor.
                     +++ eapply typing_wf. eassumption.
                     +++ eapply type_Pack ; eassumption.
                 --- cbn. omega.
    + eapply type_Heq.
      * eapply type_Sort. eapply typing_wf. eassumption.
      * eapply type_Sort. eapply typing_wf. eassumption.
      * eapply type_Prod ; eassumption.
      * eapply type_Prod ; eassumption.
    + eapply eq_symmetry. eapply cong_Heq. all: try eapply eq_reflexivity.
      * eapply type_Sort. eapply typing_wf. eassumption.
      * eapply type_Sort. eapply typing_wf. eassumption.
      * eapply cong_Prod ; try eassumption.
        eapply eq_reflexivity. assumption.
      * eapply cong_Prod ; try eassumption.
        eapply eq_reflexivity. assumption.
  - eapply type_conv.
    + eapply type_CongLambda ; try eassumption.
      * eapply type_conv ; try eassumption.
        -- eapply type_Heq.
           ++ eapply type_Sort. eapply typing_wf. eassumption.
           ++ eapply type_Sort. eapply typing_wf. eassumption.
           ++ eapply @typing_subst with (B := sSort z).
              ** eapply @type_lift
                   with (A := sSort z)
                        (Δ := [ svass np (sPack A1 A2) ])
                        (Ξ := [ svass nx A1 ]).
                 --- assumption.
                 --- econstructor.
                     +++ eapply typing_wf. eassumption.
                     +++ eapply type_Pack ; eassumption.
              ** cbn. eapply @type_ProjT1 with (A2 := lift0 1 A2).
                 --- eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                     eapply type_Pack ; eassumption.
                 --- eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                     eapply type_Pack ; eassumption.
                 --- refine (type_Rel _ _ _ _ _).
                     +++ econstructor.
                         *** eapply typing_wf. eassumption.
                         *** eapply type_Pack ; eassumption.
                     +++ cbn. omega.
           ++ eapply @typing_subst with (B := sSort z).
              ** eapply @type_lift
                   with (A := sSort z)
                        (Δ := [ svass np (sPack A1 A2) ])
                        (Ξ := [ svass ny A2 ]).
                 --- assumption.
                 --- econstructor.
                     +++ eapply typing_wf. eassumption.
                     +++ eapply type_Pack ; eassumption.
              ** cbn. eapply @type_ProjT2 with (A1 := lift0 1 A1).
                 --- eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                     eapply type_Pack ; eassumption.
                 --- eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                     eapply type_Pack ; eassumption.
                 --- refine (type_Rel _ _ _ _ _).
                     +++ econstructor.
                         *** eapply typing_wf. eassumption.
                         *** eapply type_Pack ; eassumption.
                     +++ cbn. omega.
        -- eapply cong_Heq. all: try eapply eq_reflexivity.
           ** eapply type_Sort. eapply typing_wf. eassumption.
           ** eapply type_Sort. eapply typing_wf. eassumption.
           ** eapply @pre_cong_subst1 with (B := sSort z).
              --- eapply @cong_lift
                    with (A := sSort z)
                         (Δ := [ svass np (sPack A1 A2) ])
                         (Ξ := [ svass nx A1 ]).
                  +++ assumption.
                  +++ econstructor.
                      *** eapply typing_wf. eassumption.
                      *** eapply type_Pack ; eassumption.
              --- cbn. eapply @cong_ProjT1 with (A2 := lift0 1 A2).
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ eapply eq_reflexivity.
                      refine (type_Rel _ _ _ _ _).
                      *** econstructor.
                          ---- eapply typing_wf. eassumption.
                          ---- eapply type_Pack ; eassumption.
                      *** cbn. omega.
              --- eapply @type_lift
                    with (A := sSort z)
                         (Δ := [ svass np (sPack A1 A2) ])
                         (Ξ := [ svass nx A1 ]).
                  +++ assumption.
                  +++ econstructor.
                      *** eapply typing_wf. eassumption.
                      *** eapply type_Pack ; eassumption.
              --- cbn. eapply @type_ProjT1 with (A2 := lift0 1 A2).
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ refine (type_Rel _ _ _ _ _).
                      *** econstructor.
                          ---- eapply typing_wf. eassumption.
                          ---- eapply type_Pack ; eassumption.
                      *** cbn. omega.
           ** eapply @pre_cong_subst1 with (B := sSort z).
              --- eapply @cong_lift
                    with (A := sSort z)
                         (Δ := [ svass np (sPack A1 A2) ])
                         (Ξ := [ svass ny A2 ]).
                  +++ assumption.
                  +++ econstructor.
                      *** eapply typing_wf. eassumption.
                      *** eapply type_Pack ; eassumption.
              --- cbn. eapply @cong_ProjT2 with (A1 := lift0 1 A1).
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ eapply eq_reflexivity.
                      refine (type_Rel _ _ _ _ _).
                      *** econstructor.
                          ---- eapply typing_wf. eassumption.
                          ---- eapply type_Pack ; eassumption.
                      *** cbn. omega.
              --- eapply @type_lift
                    with (A := sSort z)
                         (Δ := [ svass np (sPack A1 A2) ])
                         (Ξ := [ svass ny A2 ]).
                  +++ assumption.
                  +++ econstructor.
                      *** eapply typing_wf. eassumption.
                      *** eapply type_Pack ; eassumption.
              --- cbn. eapply @type_ProjT2 with (A1 := lift0 1 A1).
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ refine (type_Rel _ _ _ _ _).
                      *** econstructor.
                          ---- eapply typing_wf. eassumption.
                          ---- eapply type_Pack ; eassumption.
                      *** cbn. omega.
      * eapply type_conv ; try eassumption.
        -- eapply type_Heq.
           ++ eapply @typing_subst with (B := sSort z).
              ** eapply @type_lift
                   with (A := sSort z)
                        (Δ := [ svass np (sPack A1 A2) ])
                        (Ξ := [ svass nx A1 ]).
                 --- assumption.
                 --- econstructor.
                     +++ eapply typing_wf. eassumption.
                     +++ eapply type_Pack ; eassumption.
              ** cbn. eapply @type_ProjT1 with (A2 := lift0 1 A2).
                 --- eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                     eapply type_Pack ; eassumption.
                 --- eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                     eapply type_Pack ; eassumption.
                 --- refine (type_Rel _ _ _ _ _).
                     +++ econstructor.
                         *** eapply typing_wf. eassumption.
                         *** eapply type_Pack ; eassumption.
                     +++ cbn. omega.
           ++ eapply @typing_subst with (B := sSort z).
              ** eapply @type_lift
                   with (A := sSort z)
                        (Δ := [ svass np (sPack A1 A2) ])
                        (Ξ := [ svass ny A2 ]).
                 --- assumption.
                 --- econstructor.
                     +++ eapply typing_wf. eassumption.
                     +++ eapply type_Pack ; eassumption.
              ** cbn. eapply @type_ProjT2 with (A1 := lift0 1 A1).
                 --- eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                     eapply type_Pack ; eassumption.
                 --- eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                     eapply type_Pack ; eassumption.
                 --- refine (type_Rel _ _ _ _ _).
                     +++ econstructor.
                         *** eapply typing_wf. eassumption.
                         *** eapply type_Pack ; eassumption.
                     +++ cbn. omega.
           ++ eapply typing_subst.
              ** eapply @type_lift
                   with (Δ := [ svass np (sPack A1 A2) ])
                        (Ξ := [ svass nx A1 ]).
                 --- eapply type_conv ; eassumption.
                 --- econstructor.
                     +++ eapply typing_wf. eassumption.
                     +++ eapply type_Pack ; eassumption.
              ** cbn. eapply @type_ProjT1 with (A2 := lift0 1 A2).
                 --- eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                     eapply type_Pack ; eassumption.
                 --- eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                     eapply type_Pack ; eassumption.
                 --- refine (type_Rel _ _ _ _ _).
                     +++ econstructor.
                         *** eapply typing_wf. eassumption.
                         *** eapply type_Pack ; eassumption.
                     +++ cbn. omega.
           ++ eapply typing_subst.
              ** eapply @type_lift
                   with (Δ := [ svass np (sPack A1 A2) ])
                        (Ξ := [ svass ny A2 ]).
                 --- eapply type_conv ; eassumption.
                 --- econstructor.
                     +++ eapply typing_wf. eassumption.
                     +++ eapply type_Pack ; eassumption.
              ** cbn. eapply @type_ProjT2 with (A1 := lift0 1 A1).
                 --- eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                     eapply type_Pack ; eassumption.
                 --- eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                     eapply type_Pack ; eassumption.
                 --- refine (type_Rel _ _ _ _ _).
                     +++ econstructor.
                         *** eapply typing_wf. eassumption.
                         *** eapply type_Pack ; eassumption.
                     +++ cbn. omega.
        -- eapply cong_Heq. all: try eapply eq_reflexivity.
           ** eapply @pre_cong_subst1 with (B := sSort z).
              --- eapply @cong_lift
                    with (A := sSort z)
                         (Δ := [ svass np (sPack A1 A2) ])
                         (Ξ := [ svass nx A1 ]).
                  +++ assumption.
                  +++ econstructor.
                      *** eapply typing_wf. eassumption.
                      *** eapply type_Pack ; eassumption.
              --- cbn. eapply @cong_ProjT1 with (A2 := lift0 1 A2).
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ eapply eq_reflexivity.
                      refine (type_Rel _ _ _ _ _).
                      *** econstructor.
                          ---- eapply typing_wf. eassumption.
                          ---- eapply type_Pack ; eassumption.
                      *** cbn. omega.
              --- eapply @type_lift
                    with (A := sSort z)
                         (Δ := [ svass np (sPack A1 A2) ])
                         (Ξ := [ svass nx A1 ]).
                  +++ assumption.
                  +++ econstructor.
                      *** eapply typing_wf. eassumption.
                      *** eapply type_Pack ; eassumption.
              --- cbn. eapply @type_ProjT1 with (A2 := lift0 1 A2).
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ refine (type_Rel _ _ _ _ _).
                      *** econstructor.
                          ---- eapply typing_wf. eassumption.
                          ---- eapply type_Pack ; eassumption.
                      *** cbn. omega.
           ** eapply @pre_cong_subst1 with (B := sSort z).
              --- eapply @cong_lift
                    with (A := sSort z)
                         (Δ := [ svass np (sPack A1 A2) ])
                         (Ξ := [ svass ny A2 ]).
                  +++ assumption.
                  +++ econstructor.
                      *** eapply typing_wf. eassumption.
                      *** eapply type_Pack ; eassumption.
              --- cbn. eapply @cong_ProjT2 with (A1 := lift0 1 A1).
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ eapply eq_reflexivity.
                      refine (type_Rel _ _ _ _ _).
                      *** econstructor.
                          ---- eapply typing_wf. eassumption.
                          ---- eapply type_Pack ; eassumption.
                      *** cbn. omega.
              --- eapply @type_lift
                    with (A := sSort z)
                         (Δ := [ svass np (sPack A1 A2) ])
                         (Ξ := [ svass ny A2 ]).
                  +++ assumption.
                  +++ econstructor.
                      *** eapply typing_wf. eassumption.
                      *** eapply type_Pack ; eassumption.
              --- cbn. eapply @type_ProjT2 with (A1 := lift0 1 A1).
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ refine (type_Rel _ _ _ _ _).
                      *** econstructor.
                          ---- eapply typing_wf. eassumption.
                          ---- eapply type_Pack ; eassumption.
                      *** cbn. omega.
           ** eapply @cong_subst with (Δ := []).
              --- eapply @cong_lift
                    with (Δ := [ svass np (sPack A1 A2) ])
                         (Ξ := [ svass nx A1 ]).
                  +++ assumption.
                  +++ econstructor.
                      *** eapply typing_wf. eassumption.
                      *** eapply type_Pack ; eassumption.
              --- cbn. eapply @type_ProjT1 with (A2 := lift0 1 A2).
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ refine (type_Rel _ _ _ _ _).
                      *** econstructor.
                          ---- eapply typing_wf. eassumption.
                          ---- eapply type_Pack ; eassumption.
                      *** cbn. omega.
           ** eapply @cong_subst with (Δ := []).
              --- eapply @cong_lift
                    with (Δ := [ svass np (sPack A1 A2) ])
                         (Ξ := [ svass ny A2 ]).
                  +++ assumption.
                  +++ econstructor.
                      *** eapply typing_wf. eassumption.
                      *** eapply type_Pack ; eassumption.
              --- cbn. eapply @type_ProjT2 with (A1 := lift0 1 A1).
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ refine (type_Rel _ _ _ _ _).
                      *** econstructor.
                          ---- eapply typing_wf. eassumption.
                          ---- eapply type_Pack ; eassumption.
                      *** cbn. omega.
      * eapply type_conv ; eassumption.
      * eapply type_conv ; eassumption.
    + eapply type_Heq.
      * eapply type_Prod ; eassumption.
      * eapply type_Prod ; eassumption.
      * eapply type_Lambda ; eassumption.
      * eapply type_Lambda ; eassumption.
    + eapply eq_symmetry. eapply cong_Heq.
      * eapply cong_Prod ; try eassumption.
        eapply eq_reflexivity. assumption.
      * eapply cong_Prod ; try eassumption.
        eapply eq_reflexivity. assumption.
      * eapply cong_Lambda ; try eassumption.
        eapply eq_reflexivity. eassumption.
      * eapply cong_Lambda ; try eassumption.
        eapply eq_reflexivity. eassumption.
  - eapply type_conv.
    + eapply type_CongApp ; try eassumption.
      * eapply type_conv ; try eassumption.
        -- eapply type_Heq.
           ++ eapply type_Sort. eapply typing_wf. eassumption.
           ++ eapply type_Sort. eapply typing_wf. eassumption.
           ++ eapply @typing_subst with (B := sSort z).
              ** eapply @type_lift
                   with (A := sSort z)
                        (Δ := [ svass np (sPack A1 A2) ])
                        (Ξ := [ svass nx A1 ]).
                 --- assumption.
                 --- econstructor.
                     +++ eapply typing_wf. eassumption.
                     +++ eapply type_Pack ; eassumption.
              ** cbn. eapply @type_ProjT1 with (A2 := lift0 1 A2).
                 --- eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                     eapply type_Pack ; eassumption.
                 --- eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                     eapply type_Pack ; eassumption.
                 --- refine (type_Rel _ _ _ _ _).
                     +++ econstructor.
                         *** eapply typing_wf. eassumption.
                         *** eapply type_Pack ; eassumption.
                     +++ cbn. omega.
           ++ eapply @typing_subst with (B := sSort z).
              ** eapply @type_lift
                   with (A := sSort z)
                        (Δ := [ svass np (sPack A1 A2) ])
                        (Ξ := [ svass ny A2 ]).
                 --- assumption.
                 --- econstructor.
                     +++ eapply typing_wf. eassumption.
                     +++ eapply type_Pack ; eassumption.
              ** cbn. eapply @type_ProjT2 with (A1 := lift0 1 A1).
                 --- eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                     eapply type_Pack ; eassumption.
                 --- eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                     eapply type_Pack ; eassumption.
                 --- refine (type_Rel _ _ _ _ _).
                     +++ econstructor.
                         *** eapply typing_wf. eassumption.
                         *** eapply type_Pack ; eassumption.
                     +++ cbn. omega.
        -- eapply cong_Heq. all: try eapply eq_reflexivity.
           ** eapply type_Sort. eapply typing_wf. eassumption.
           ** eapply type_Sort. eapply typing_wf. eassumption.
           ** eapply @cong_subst with (A := sSort z) (Δ := []).
              --- eapply @cong_lift
                    with (A := sSort z)
                         (Δ := [ svass np (sPack A1 A2) ])
                         (Ξ := [ svass nx A1 ]).
                  +++ assumption.
                  +++ econstructor.
                      *** eapply typing_wf. eassumption.
                      *** eapply type_Pack ; eassumption.
              --- cbn. eapply @type_ProjT1 with (A2 := lift0 1 A2).
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ refine (type_Rel _ _ _ _ _).
                      *** econstructor.
                          ---- eapply typing_wf. eassumption.
                          ---- eapply type_Pack ; eassumption.
                      *** cbn. omega.
           ** eapply @cong_subst with (A := sSort z) (Δ := []).
              --- eapply @cong_lift
                    with (A := sSort z)
                         (Δ := [ svass np (sPack A1 A2) ])
                         (Ξ := [ svass ny A2 ]).
                  +++ assumption.
                  +++ econstructor.
                      *** eapply typing_wf. eassumption.
                      *** eapply type_Pack ; eassumption.
              --- cbn. eapply @type_ProjT2 with (A1 := lift0 1 A1).
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ eapply @typing_lift01 with (A := sSort s) ; try eassumption.
                      eapply type_Pack ; eassumption.
                  +++ refine (type_Rel _ _ _ _ _).
                      *** econstructor.
                          ---- eapply typing_wf. eassumption.
                          ---- eapply type_Pack ; eassumption.
                      *** cbn. omega.
      * eapply type_conv.
        -- eassumption.
        -- eapply type_Heq.
           ++ eapply type_Prod ; eassumption.
           ++ eapply type_Prod ; eassumption.
           ++ eapply type_conv ; try exact t1.
              ** eapply type_Prod ; eassumption.
              ** eapply cong_Prod ; try eassumption.
                 eapply eq_reflexivity. assumption.
           ++ eapply type_conv ; try exact t2.
              ** eapply type_Prod ; eassumption.
              ** eapply cong_Prod ; try eassumption.
                 eapply eq_reflexivity. assumption.
        -- eapply cong_Heq.
           ** eapply cong_Prod ; try eassumption.
              eapply eq_reflexivity. assumption.
           ** eapply cong_Prod ; try eassumption.
              eapply eq_reflexivity. assumption.
           ** eapply eq_reflexivity. assumption.
           ** eapply eq_reflexivity. assumption.
      * eapply type_conv ; try eassumption.
        -- eapply type_Prod ; eassumption.
        -- eapply cong_Prod ; try eassumption.
           eapply eq_reflexivity. assumption.
      * eapply type_conv ; try eassumption.
        -- eapply type_Prod ; eassumption.
        -- eapply cong_Prod ; try eassumption.
           eapply eq_reflexivity. assumption.
    + eapply type_Heq.
      * eapply @typing_subst with (B := sSort z) ; eassumption.
      * eapply @typing_subst with (B := sSort z) ; eassumption.
      * eapply type_App ; eassumption.
      * eapply type_App ; eassumption.
    + eapply eq_symmetry. eapply cong_Heq.
      * eapply @cong_subst with (A := sSort z) (Δ := []).
        -- eassumption.
        -- assumption.
      * eapply @cong_subst with (A := sSort z) (Δ := []).
        -- eassumption.
        -- assumption.
      * eapply cong_App.
        all: try eapply eq_reflexivity.
        all: eassumption.
      * eapply cong_App.
        all: try eapply eq_reflexivity.
        all: eassumption.
  - eapply type_ProjT2 with (A1 := A1) ; eassumption.
  - eapply type_ProjT2 with (A1 := A1) ; eassumption.
  - eapply type_conv.
    + eapply type_ProjTe with (A1 := A1) (A2 := A2) ; eassumption.
    + eapply type_Heq ; try eassumption.
      * eapply type_ProjT1 with (A2 := A2) ; eassumption.
      * eapply type_ProjT2 with (A1 := A1) ; eassumption.
    + eapply eq_symmetry. eapply cong_Heq ; try eapply eq_reflexivity ; try eassumption.
      * eapply cong_ProjT1 with (A2 := A2) ; eassumption.
      * eapply cong_ProjT2 with (A1 := A1) ; eassumption.
  - eapply type_HeqToEq ; try eassumption.
    eapply type_HeqRefl ; eassumption.
Defined.

Corollary full_cong_subst' :
  forall {Σ Γ nx B Δ t1 t2 u1 u2 A},
    Σ ;;; Γ ,, svass nx B ,,, Δ |-i t1 = t2 : A ->
    Σ ;;; Γ |-i u1 = u2 : B ->
    Σ ;;; Γ ,,, subst_context u1 Δ |-i
    t1{ #|Δ| := u1 } = t2{ #|Δ| := u2 } : A{ #|Δ| := u1 }.
Proof.
  intros Σ Γ nx B Δ t1 t2 u1 u2 A ht hu.
  destruct (eq_typing ht) as [_ ht2].
  destruct (eq_typing hu) as [hu1 _].
  eapply eq_transitivity.
  - exact (cong_subst ht hu1).
  - exact (cong_substs ht2 hu hu1).
Defined.

Lemma cong_subst1 :
  forall {Σ Γ t1 t2 A B u1 u2 n},
    Σ ;;; Γ ,, svass n A |-i t1 = t2 : B ->
    Σ ;;; Γ |-i u1 = u2 : A ->
    Σ ;;; Γ |-i t1{ 0 := u1 } = t2{ 0 := u2 } : B{ 0 := u1 }.
Proof.
  intros Σ Γ t1 t2 A B u1 u2 n ht hu.
  eapply @full_cong_subst' with (Δ := []) ; eassumption.
Defined.

Lemma cong_subst2 :
  forall {Σ Γ t1 t2 A B C na nb u1 u2 v1 v2},
    Σ ;;; Γ ,, svass na A ,, svass nb B |-i t1 = t2 : C ->
    Σ ;;; Γ |-i u1 = u2 : A ->
    Σ ;;; Γ |-i v1 = v2 : B{ 0 := u1 } ->
    Σ ;;; Γ |-i t1{ 1 := u1 }{ 0 := v1 }
             = t2{ 1 := u2 }{ 0 := v2 } : C{ 1 := u1 }{ 0 := v1 }.
Proof.
  intros Σ Γ t1 t2 A B C na nb u1 u2 v1 v2 ht hu hv.
  eapply @full_cong_subst' with (Δ := []).
  - eapply @full_cong_subst' with (Δ := [ svass nb B ]).
    + exact ht.
    + assumption.
  - cbn. assumption.
Defined.

Lemma sorts_in_sort :
  forall {Σ Γ s1 s2 s},
    Σ ;;; Γ |-i sSort s1 : sSort s ->
    Σ ;;; Γ |-i sSort s2 : sSort s ->
    Σ ;;; Γ |-i sSort s1 = sSort s2 : sSort s.
Admitted.

(* Fixpoint strengthen_sort' {Σ Γ s A} (h : Σ ;;; Γ |-i sSort s : A) {struct h} : *)
(*   forall {z B}, *)
(*     Σ ;;; Γ |-i A = B : sSort z -> *)
(*     Σ ;;; [] |-i B : sSort z -> *)
(*     Σ ;;; [] |-i sSort s : B *)

(* with strengthen_eqsort {Σ Γ s z A} *)
(*   (h : Σ ;;; Γ |-i sSort s = A : sSort z) {struct h} : *)
(*   Σ ;;; [] |-i A : sSort z -> *)
(*   Σ ;;; [] |-i sSort s = A : sSort z. *)
(* Proof. *)
(*   - dependent destruction h ; intros z C he hC. *)
(*     + pose proof (strengthen_eqsort _ _ _ _ _ he hC). *)
(*       eapply type_conv. *)
(*       * eapply type_Sort. constructor. *)
(*       * eassumption. *)
(*       * assumption. *)
(*     + cheat. *)
(*   - cheat. *)
(* Defined. *)

(* Lemma strengthen_sort' : *)
(*   forall {Σ Γ s A}, *)
(*     Σ ;;; Γ |-i sSort s : A -> *)
(*     forall {z B}, *)
(*       Σ ;;; Γ |-i A = B : sSort z -> *)
(*       Σ ;;; [] |-i B : sSort z -> *)
(*       Σ ;;; [] |-i sSort s : B. *)
(* Proof. *)
(*   intros Σ Γ s A hs. *)
(*   dependent induction hs ; intros z C he hA. *)
(*   - eapply type_Sort. constructor. *)
(*   - *)


Lemma strengthen_sort :
  forall {Σ Γ Δ s z},
    Σ ;;; Γ |-i sSort s : sSort z ->
    wf Σ Δ ->
    Σ ;;; Δ |-i sSort s : sSort z.
Admitted.

Lemma strengthen_sort_eq :
  forall {Σ Γ Δ s1 s2 z},
    Σ ;;; Γ |-i sSort s1 = sSort s2 : sSort z ->
    wf Σ Δ ->
    Σ ;;; Δ |-i sSort s1 = sSort s2 : sSort z.
Admitted.

Lemma cong_succ_sort :
  forall {Σ Γ s1 s2 s3},
    Σ ;;; Γ |-i sSort s1 = sSort s2 : sSort s3 ->
    Σ ;;; Γ |-i sSort (succ_sort s1) = sSort (succ_sort s2) : sSort (succ_sort s3).
Admitted.

(* Lemma uniqueness_ctx : *)
(*   forall {Σ Γ u A}, *)
(*     Σ ;;; Γ |-i u : A -> *)
(*     forall {Δ} *)

Lemma uniqueness :
  forall {Σ Γ A B u},
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i u : B ->
    ∑ s, Σ ;;; Γ |-i A = B : sSort s.
Proof.
  (* intros Σ Γ A B u hu1. *)
  (* dependent induction hu1 ; intros hu2 ; dependent induction hu2. *)
  (* - eexists. cheat. *)
  (* - destruct (IHhu2_1 w isdecl) as [s' h']. *)
  (*   eexists. eapply eq_transitivity. *)
  (*   + exact h'. *)
  (*   + eapply eq_conv. *)
  (*     * exact e. *)
  (*     * (* This bit I usually use uniqueness to conclude... *)
  (*          This means we might need a stronger induction hypothesis to go. *)
  (*        *) *)
  (*       cheat. *)
  (* - *)
Admitted.

(* We state several inversion lemmata on a by need basis. *)

Lemma inversionRel :
  forall {Σ Γ n T},
    Σ ;;; Γ |-i sRel n : T ->
    ∑ isdecl s,
      let A := lift0 (S n) (safe_nth Γ (exist _ n isdecl)).(sdecl_type) in
      Σ ;;; Γ |-i A = T : sSort s.
Proof.
  intros Σ Γ n T h. dependent induction h.
  - exists isdecl.
    assert (Σ ;;; Γ |-i sRel n : lift0 (S n) (safe_nth Γ (exist _ n isdecl)).(sdecl_type)) by (now constructor).
    destruct (istype_type X) as [s hs].
    exists s. apply eq_reflexivity. eassumption.
  - destruct IHh1 as [isdecl [s' h]].
    exists isdecl, s'.
    eapply eq_transitivity.
    + exact h.
    + destruct (eq_typing e) as [hAs _].
      destruct (eq_typing h) as [_ hAs'].
      destruct (uniqueness hAs hAs') as [? ?].
      eapply eq_conv ; eassumption.
Defined.

Lemma inversionSort :
  forall {Σ Γ s T},
    Σ ;;; Γ |-i sSort s : T ->
    Σ ;;; Γ |-i sSort (succ_sort s) = T : sSort (succ_sort (succ_sort s)).
Proof.
  intros Σ Γ s T h.
  dependent induction h.

  - apply eq_reflexivity. apply type_Sort. assumption.

  - eapply eq_transitivity.
    + eassumption.
    + destruct (eq_typing e) as [hAs0 _].
      destruct (eq_typing IHh1) as [_ hAss].
      destruct (uniqueness hAs0 hAss) as [? ?].
      eapply eq_conv ; eassumption.
Defined.

Lemma inversionInd :
  forall {Σ Γ ind s T},
    Σ ;;; Γ |-i sInd ind s : T ->
    ∑ univs decl (isdecl : declared_inductive (fst Σ) ind univs decl),
      Σ ;;; Γ |-i sSort s = T : sSort (succ_sort s).
Proof.
  intros Σ Γ ind s T h.
  dependent induction h.

  - exists univs, decl, isdecl.
    apply eq_reflexivity. apply type_Sort. assumption.

  - destruct IHh1 as [univs [decl [isdecl eq]]].
    exists univs, decl, isdecl.
    eapply eq_transitivity.
    + eassumption.
    + destruct (eq_typing e) as [hAs _].
      destruct (eq_typing eq) as [_ hAss0].
      destruct (uniqueness hAs hAss0) as [? ?].
      eapply eq_conv ; eassumption.
Defined.

Lemma inversionProd :
  forall {Σ Γ n A B T},
    Σ ;;; Γ |-i sProd n A B : T ->
    ∑ s1 s2,
      (Σ ;;; Γ |-i A : sSort s1) *
      (Σ ;;; Γ ,, svass n A |-i B : sSort s2) *
      (Σ ;;; Γ |-i sSort (max_sort s1 s2) = T : sSort (succ_sort (max_sort s1 s2))).
Proof.
  intros Σ Γ n A B T h.
  dependent induction h.

  - exists s1, s2. repeat split.
    + assumption.
    + assumption.
    + apply eq_reflexivity. apply type_Sort. apply (typing_wf h1).

  - destruct IHh1 as [s1 [s2 [[? ?] ?]]].
    exists s1, s2. repeat split.
    + assumption.
    + assumption.
    + eapply eq_transitivity.
      * eassumption.
      * destruct (eq_typing e) as [hAs _].
        destruct (eq_typing pi2_0) as [_ hAsm].
        destruct (uniqueness hAs hAsm).
        eapply eq_conv ; eassumption.
Defined.

Lemma inversionLambda :
  forall {Σ Γ na A B t T},
      Σ ;;; Γ |-i sLambda na A B t : T ->
      ∑ s1 s2,
        (Σ ;;; Γ |-i A : sSort s1) *
        (Σ ;;; Γ ,, svass na A |-i B : sSort s2) *
        (Σ ;;; Γ ,, svass na A |-i t : B) *
        (Σ ;;; Γ |-i sProd na A B = T : sSort (max_sort s1 s2)).
Proof.
  intros Σ Γ na A B t T h.
  dependent induction h.

  - exists s1, s2. repeat split ; try eassumption.
    apply cong_Prod.
    all: apply eq_reflexivity ; assumption.

  - destruct IHh1 as [s1 [s2 [[[? ?] ?] ?]]].
    exists s1, s2. repeat split.
    all: try assumption.
    eapply eq_transitivity.
    + eassumption.
    + destruct (eq_typing e) as [i1 _].
      destruct (eq_typing pi2_1) as [_ i2].
      destruct (uniqueness i1 i2).
      eapply eq_conv ; eassumption.
Defined.

Lemma inversionApp :
  forall {Σ Γ t n A B u T},
    Σ ;;; Γ |-i sApp t n A B u : T ->
    ∑ s1 s2,
      (Σ ;;; Γ |-i A : sSort s1) *
      (Σ ;;; Γ ,, svass n A |-i B : sSort s2) *
      (Σ ;;; Γ |-i t : sProd n A B) *
      (Σ ;;; Γ |-i u : A) *
      (Σ ;;; Γ |-i B{ 0 := u } = T : sSort s2).
Proof.
  intros Σ Γ t n A B u T H.
  dependent induction H.

  - exists s1, s2.
    repeat split ; try easy.
    apply eq_reflexivity.
    change (sSort s2) with ((sSort s2){0 := u}).
    eapply typing_subst ; eassumption.

  - destruct IHtyping1 as [s1 [s2 [[[[? ?] ?] ?] ?]]].
    exists s1, s2. repeat split ; try easy.
    eapply eq_transitivity.
    + eassumption.
    + destruct (eq_typing e) as [hAs _].
      destruct (eq_typing pi2_2) as [_ hAs2].
      destruct (uniqueness hAs hAs2).
      eapply eq_conv ; eassumption.
Defined.

Lemma inversionEq :
  forall {Σ Γ A u v T},
    Σ ;;; Γ |-i sEq A u v : T ->
    ∑ s,
      (Σ ;;; Γ |-i A : sSort s) *
      (Σ ;;; Γ |-i u : A) *
      (Σ ;;; Γ |-i v : A) *
      (Σ ;;; Γ |-i sSort s = T : sSort (succ_sort s)).
Proof.
  intros Σ Γ A u v T h.
  dependent induction h.
  - exists s. repeat split ; try easy.
    eapply eq_reflexivity. apply type_Sort.
    apply (typing_wf h1).
  - destruct IHh1 as [s' [[[hA hu] hv] heq]].
    exists s'. repeat split ; try easy.
    eapply eq_transitivity.
    + exact heq.
    + destruct (eq_typing heq) as [_ hA01].
      destruct (eq_typing e) as [hA02 _].
      destruct (uniqueness hA02 hA01) as [s'' h''].
      eapply eq_conv ; eassumption.
Defined.

Lemma inversionRefl :
  forall {Σ Γ A u T},
    Σ ;;; Γ |-i sRefl A u : T ->
    ∑ s,
      (Σ ;;; Γ |-i A : sSort s) *
      (Σ ;;; Γ |-i u : A) *
      (Σ ;;; Γ |-i sEq A u u = T : sSort s).
Proof.
  intros Σ Γ A u T h.
  dependent induction h.

  - exists s. repeat split ; try easy.
    apply eq_reflexivity. apply type_Eq ; assumption.

  - destruct IHh1 as [s' [[hA hu] eq]].
    exists s'. repeat split ; try easy.
    destruct (eq_typing e) as [i1 _].
    destruct (eq_typing eq) as [_ i2].
    destruct (uniqueness i1 i2).
    eapply eq_transitivity.
    + eassumption.
    + eapply eq_conv ; eassumption.
Defined.

Lemma inversionJ :
  forall {Σ Γ A u P w v p T},
    Σ ;;; Γ |-i sJ A u P w v p : T ->
    ∑ s1 s2 nx ne,
      (Σ ;;; Γ |-i A : sSort s1) *
      (Σ ;;; Γ |-i u : A) *
      (Σ ;;; Γ |-i v : A) *
      (Σ ;;; Γ ,, svass nx A ,, svass ne (sEq (lift0 1 A) (lift0 1 u) (sRel 0)) |-i P : sSort s2) *
      (Σ ;;; Γ |-i p : sEq A u v) *
      (Σ ;;; Γ |-i w : (P {1 := u}){0 := sRefl A u}) *
      (Σ ;;; Γ |-i P{1 := v}{0 := p} = T : sSort s2).
Proof.
  intros Σ Γ A u P w v p T H.
  dependent induction H.

  - exists s1, s2, nx, ne. repeat split ; try easy.
    apply eq_reflexivity.
    change (sSort s2) with ((sSort s2){1 := v}{0 := p}).
    eapply typing_subst2.
    + eassumption.
    + assumption.
    + cbn. rewrite !lift_subst, lift00.
      assumption.

  - destruct IHtyping1
      as [s1 [s2 [nx [ne [[[[[[? ?] ?] ?] ?] ?] ?]]]]].
    exists s1, s2, nx, ne. repeat split ; try easy.
    eapply eq_transitivity.
    + eassumption.
    + destruct (eq_typing e) as [hAs _].
      destruct (eq_typing pi2_4) as [_ hAs2].
      destruct (uniqueness hAs hAs2).
      eapply eq_conv ; eassumption.
Defined.

Lemma inversionTransport :
  forall {Σ Γ A B p t T},
    Σ ;;; Γ |-i sTransport A B p t : T ->
    ∑ s,
      (Σ ;;; Γ |-i p : sEq (sSort s) A B) *
      (Σ ;;; Γ |-i t : A) *
      (Σ ;;; Γ |-i A : sSort s) *
      (Σ ;;; Γ |-i B : sSort s) *
      (Σ ;;; Γ |-i B = T : sSort s).
Proof.
  intros Σ Γ A B p t T h.
  dependent induction h.

  - exists s. repeat split ; try easy.
    apply eq_reflexivity. assumption.

  - destruct IHh1 as [s' [[[[? ?] ?] ?] ?]].
    exists s'. repeat split ; try easy.
    eapply eq_transitivity.
    + eassumption.
    + destruct (eq_typing e) as [hA1 _].
      destruct (eq_typing pi2_2) as [_ hA2].
      destruct (uniqueness hA1 hA2).
      eapply eq_conv ; eassumption.
Defined.

(* Lemma inversionUip *)
(* Lemma inversionFunext *)

Lemma inversionHeq :
  forall {Σ Γ A B a b T},
    Σ ;;; Γ |-i sHeq A a B b : T ->
    ∑ s,
      (Σ ;;; Γ |-i A : sSort s) *
      (Σ ;;; Γ |-i B : sSort s) *
      (Σ ;;; Γ |-i a : A) *
      (Σ ;;; Γ |-i b : B) *
      (Σ ;;; Γ |-i sSort (succ_sort s) = T : sSort (succ_sort (succ_sort s))).
Proof.
  intros Σ Γ A B a b T h.
  dependent induction h.

  - exists s. repeat split ; try easy.
    apply eq_reflexivity. apply type_Sort. apply (typing_wf h1).

  - destruct IHh1 as [s' [[[[? ?] ?] ?] ?]].
    exists s'. repeat split ; try easy.
    eapply eq_transitivity.
    + eassumption.
    + destruct (eq_typing e) as [i1 _].
      destruct (eq_typing pi2_2) as [_ i2].
      destruct (uniqueness i1 i2).
      eapply eq_conv ; eassumption.
Defined.

Lemma inversionPack :
  forall {Σ Γ A1 A2 T},
    Σ ;;; Γ |-i sPack A1 A2 : T ->
    ∑ s,
      (Σ ;;; Γ |-i A1 : sSort s) *
      (Σ ;;; Γ |-i A2 : sSort s) *
      (Σ ;;; Γ |-i sSort s = T : sSort (succ_sort s)).
Proof.
  intros Σ Γ A1 A2 T h.
  dependent induction h.

  - exists s. repeat split ; try easy.
    apply eq_reflexivity. apply type_Sort. apply (typing_wf h1).

  - destruct IHh1 as [s' [[? ?] ?]].
    exists s'. repeat split ; try easy.
    eapply eq_transitivity.
    + eassumption.
    + destruct (eq_typing e) as [i1 _].
      destruct (eq_typing pi2_0) as [_ i2].
      destruct (uniqueness i1 i2).
      eapply eq_conv ; eassumption.
Defined.

(* We state some admissible typing rules *)
Lemma type_conv' :
  forall {Σ Γ t A B s},
    Σ ;;; Γ |-i t : A ->
    Σ ;;; Γ |-i A = B : sSort s ->
    Σ ;;; Γ |-i t : B.
Proof.
  intros Σ Γ t A B s ht eq.
  eapply type_conv.
  - eassumption.
  - apply (eq_typing eq).
  - assumption.
Defined.

Lemma heq_sort :
  forall {Σ Γ s1 s2 A B p},
    Σ ;;; Γ |-i p : sHeq (sSort s1) A (sSort s2) B ->
    Σ ;;; Γ |-i p : sHeq (sSort s1) A (sSort s1) B.
Proof.
  intros Σ Γ s1 s2 A B p h.
  destruct (istype_type h) as [? i].
  destruct (inversionHeq i) as [? [[[[e1 e2] ?] ?] ?]].
  pose proof (sorts_in_sort e2 e1) as eq.
  eapply type_conv'.
  - eassumption.
  - apply cong_Heq.
    all: try (apply eq_reflexivity ; eassumption).
    assumption.
Defined.

Lemma type_HeqToEq' :
  forall {Σ Γ A u v p},
    Σ ;;; Γ |-i p : sHeq A u A v ->
    Σ ;;; Γ |-i sHeqToEq p : sEq A u v.
Proof.
  intros Σ Γ A u v p h.
  destruct (istype_type h) as [? i].
  destruct (inversionHeq i) as [? [[[[? ?] ?] ?] ?]].
  eapply type_HeqToEq ; eassumption.
Defined.

Fact sort_heq :
  forall {Σ Γ s1 s2 A B e},
    Σ ;;; Γ |-i e : sHeq (sSort s1) A (sSort s2) B ->
    Σ ;;; Γ |-i sHeqToEq e : sEq (sSort s1) A B.
Proof.
  intros Σ Γ s1 s2 A B e h.
  destruct (istype_type h) as [? hty].
  destruct (inversionHeq hty) as [? [[[[? ?] ?] ?] ?]].
  eapply type_HeqToEq'.
  eapply heq_sort. eassumption.
Defined.

Corollary sort_heq_ex :
  forall {Σ Γ s1 s2 A B e},
    Σ ;;; Γ |-i e : sHeq (sSort s1) A (sSort s2) B ->
    ∑ p, Σ ;;; Γ |-i p : sEq (sSort s1) A B.
Proof.
  intros Σ Γ s A B e h.
  eexists. now eapply sort_heq.
Defined.

Lemma type_HeqRefl' :
  forall {Σ Γ A a},
    Σ ;;; Γ |-i a : A ->
    Σ ;;; Γ |-i sHeqRefl A a : sHeq A a A a.
Proof.
  intros Σ Γ A a h.
  destruct (istype_type h).
  eapply type_HeqRefl ; eassumption.
Defined.

Lemma type_HeqSym' :
  forall {Σ Γ A a B b p},
    Σ ;;; Γ |-i p : sHeq A a B b ->
    Σ ;;; Γ |-i sHeqSym p : sHeq B b A a.
Proof.
  intros Σ Γ A a B b p h.
  destruct (istype_type h) as [? hty].
  destruct (inversionHeq hty) as [? [[[[? ?] ?] ?] ?]].
  now eapply type_HeqSym.
Defined.

Lemma type_HeqTrans' :
  forall {Σ Γ A a B b C c p q},
    Σ ;;; Γ |-i p : sHeq A a B b ->
    Σ ;;; Γ |-i q : sHeq B b C c ->
    Σ ;;; Γ |-i sHeqTrans p q : sHeq A a C c.
Proof.
  intros Σ Γ A a B b C c p q h1 h2.
  destruct (istype_type h1) as [? i1].
  destruct (inversionHeq i1) as [? [[[[? iB1] ?] ?] ?]].
  destruct (istype_type h2) as [? i2].
  destruct (inversionHeq i2) as [? [[[[iB2 ?] ?] ?] ?]].
  eapply type_HeqTrans. all: try eassumption.
  destruct (uniqueness iB2 iB1) as [? eq].
  eapply type_conv ; [ eassumption | idtac | eassumption ].
  apply (eq_typing eq).
Defined.

Lemma type_HeqTransport' :
  forall {Σ Γ s A B p t},
    Σ ;;; Γ |-i t : A ->
    Σ ;;; Γ |-i p : sEq (sSort s) A B ->
    Σ ;;; Γ |-i sHeqTransport p t : sHeq A t B (sTransport A B p t).
Proof.
  intros Σ Γ s A B p t ht hp.
  destruct (istype_type hp) as [? i].
  destruct (inversionEq i) as [? [[[? ?] ?] ?]].
  eapply type_HeqTransport ; eassumption.
Defined.

Lemma type_CongProd'' :
  forall {Σ Γ s z nx ny np A1 A2 B1 B2 pA pB},
    Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2 ->
    Σ ;;; Γ ,, svass np (sPack A1 A2)
    |-i pB : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ ,, svass nx A1 |-i B1 : sSort z ->
    Σ ;;; Γ ,, svass ny A2 |-i B2 : sSort z ->
    Σ ;;; Γ |-i sCongProd B1 B2 pA pB :
    sHeq (sSort (max_sort s z)) (sProd nx A1 B1)
         (sSort (max_sort s z)) (sProd ny A2 B2).
Proof.
  intros Σ Γ s z nx ny np A1 A2 B1 B2 pA pB hpA hpB hB1 hB2.
  destruct (istype_type hpA) as [? ipA].
  destruct (inversionHeq ipA) as [? [[[[? ?] ?] ?] ?]].
  destruct (istype_type hpB) as [? ipB].
  destruct (inversionHeq ipB) as [? [[[[? ?] ?] ?] ?]].
  eapply type_CongProd.
  all: eassumption.
Defined.

Lemma prod_sorts :
  forall {Σ Γ s1 s2 z1 z2 nx ny np A1 A2 B1 B2 pA pB},
    Σ ;;; Γ |-i pA : sHeq (sSort s1) A1 (sSort s2) A2 ->
    Σ ;;; Γ ,, svass np (sPack A1 A2)
    |-i pB : sHeq (sSort z1) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                (sSort z2) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ ,, svass nx A1 |-i B1 : sSort z1 ->
    Σ ;;; Γ ,, svass ny A2 |-i B2 : sSort z2 ->
    ∑ ss zz mm,
      (Σ ;;; Γ |-i sSort s1 = sSort s2 : sSort ss) *
      (Σ ;;; Γ ,, svass ny A2 |-i sSort z2 = sSort z1 : sSort zz) *
      (Σ ;;; Γ |-i sSort (max_sort s1 z1) = sSort (max_sort s2 z2) : sSort mm).
Proof.
  intros Σ Γ s1 s2 z1 z2 nx ny np A1 A2 B1 B2 pA pB hpA hpB hB1 hB2.
  assert (hs : ∑ ss, Σ ;;; Γ |-i sSort s1 = sSort s2 : sSort ss).
  { destruct (istype_type hpA) as [? ipA].
    destruct (inversionHeq ipA) as [? [[[[e1 e2] ?] ?] ?]].
    pose proof (sorts_in_sort e1 e2).
    eexists. eassumption.
  }
  destruct hs as [ss hss]. exists ss.
  assert (hz : ∑ zz, Σ;;; Γ,, svass ny A2 |-i sSort z2 = sSort z1 : sSort zz).
  { destruct (istype_type hpB) as [? ipB].
    destruct (inversionHeq ipB) as [? [[[[f1 f2] ?] ?] ?]].
    pose proof (sorts_in_sort f2 f1).
    eexists. eapply strengthen_sort_eq.
    - eassumption.
    - eapply typing_wf. eassumption.
  }
  destruct hz as [zz hzz]. exists zz.
  assert (hP1 : Σ ;;; Γ |-i sProd nx A1 B1 : sSort (max_sort s1 z1)).
  { destruct (istype_type hpA) as [? ipA].
    destruct (inversionHeq ipA) as [? [[[[e1 e2] ?] ?] ?]].
    apply type_Prod ; eassumption.
  }
  assert (hP2 : Σ ;;; Γ |-i sProd nx A1 B1 : sSort (max_sort s2 z2)).
  { destruct (istype_type hpA) as [? ipA].
    destruct (inversionHeq ipA) as [? [[[[e1 e2] ?] ?] ?]].
    apply type_Prod.
    - eapply type_conv' ; eassumption.
    - eapply type_conv'.
      + eassumption.
      + apply eq_symmetry.
        eapply strengthen_sort_eq.
        * eassumption.
        * eapply typing_wf. eassumption.
  }
  destruct (uniqueness hP1 hP2) as [mm hmm]. exists mm.
  repeat split.
  - assumption.
  - assumption.
  - assumption.
Defined.

Lemma type_CongProd' :
  forall {Σ Γ s1 s2 z1 z2 nx ny np A1 A2 B1 B2 pA pB},
    Σ ;;; Γ |-i pA : sHeq (sSort s1) A1 (sSort s2) A2 ->
    Σ ;;; Γ ,, svass np (sPack A1 A2)
    |-i pB : sHeq (sSort z1) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                (sSort z2) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ ,, svass nx A1 |-i B1 : sSort z1 ->
    Σ ;;; Γ ,, svass ny A2 |-i B2 : sSort z2 ->
    Σ ;;; Γ |-i sCongProd B1 B2 pA pB :
    sHeq (sSort (max_sort s1 z1)) (sProd nx A1 B1)
         (sSort (max_sort s2 z2)) (sProd ny A2 B2).
Proof.
  intros Σ Γ s1 s2 z1 z2 nx ny np A1 A2 B1 B2 pA pB hpA hpB hB1 hB2.
  destruct (prod_sorts hpA hpB hB1 hB2) as [ss [zz [mm [[e e0] e1]]]].
  eapply type_conv'.
  - eapply type_CongProd''.
    + eapply heq_sort. eassumption.
    + eapply heq_sort. eassumption.
    + eassumption.
    + eapply type_conv'.
      * eassumption.
      * eassumption.
  - apply cong_Heq.
    all: try apply eq_reflexivity.
    + apply type_Sort. eapply typing_wf. eassumption.
    + eapply eq_conv.
      * eassumption.
      * eapply eq_symmetry. eapply inversionSort.
        apply (eq_typing e1).
    + destruct (istype_type hpA) as [? ipA].
      destruct (inversionHeq ipA) as [? [[[[? ?] ?] ?] ?]].
      apply type_Prod ; eassumption.
    + destruct (istype_type hpA) as [? ipA].
      destruct (inversionHeq ipA) as [? [[[[? ?] ?] ?] ?]].
      apply type_Prod.
      * eapply type_conv'.
        -- eassumption.
        -- eapply eq_symmetry. eassumption.
      * eapply type_conv' ; eassumption.
Defined.

Lemma type_CongLambda'' :
  forall {Σ Γ s z nx ny np A1 A2 B1 B2 t1 t2 pA pB pt},
    Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2 ->
    Σ ;;; Γ ,, svass np (sPack A1 A2)
    |-i pB : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                 (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ ,, svass np (sPack A1 A2)
    |-i pt : sHeq ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                 ((lift 1 1 t1){ 0 := sProjT1 (sRel 0) })
                 ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) })
                 ((lift 1 1 t2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ ,, svass nx A1 |-i B1 : sSort z ->
    Σ ;;; Γ ,, svass ny A2 |-i B2 : sSort z ->
    Σ ;;; Γ ,, svass nx A1 |-i t1 : B1 ->
    Σ ;;; Γ ,, svass ny A2 |-i t2 : B2 ->
    Σ ;;; Γ |-i sCongLambda B1 B2 t1 t2 pA pB pt :
               sHeq (sProd nx A1 B1) (sLambda nx A1 B1 t1)
                    (sProd ny A2 B2) (sLambda ny A2 B2 t2).
Proof.
  intros Σ Γ s z nx ny np A1 A2 B1 B2 t1 t2 pA pB pt hpA hpB hpt hB1 hB2 ht1 ht2.
  destruct (istype_type hpA) as [? ipA].
  destruct (inversionHeq ipA) as [? [[[[? ?] ?] ?] ?]].
  destruct (istype_type hpB) as [? ipB].
  destruct (inversionHeq ipB) as [? [[[[? ?] ?] ?] ?]].
  destruct (istype_type hpt) as [? ipt].
  destruct (inversionHeq ipt) as [? [[[[? ?] ?] ?] ?]].
  eapply type_CongLambda ; eassumption.
Defined.

Lemma type_CongLambda' :
  forall {Σ Γ s1 s2 z1 z2 nx ny np A1 A2 B1 B2 t1 t2 pA pB pt},
    Σ ;;; Γ |-i pA : sHeq (sSort s1) A1 (sSort s2) A2 ->
    Σ ;;; Γ ,, svass np (sPack A1 A2)
    |-i pB : sHeq (sSort z1) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                 (sSort z2) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ ,, svass np (sPack A1 A2)
    |-i pt : sHeq ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                 ((lift 1 1 t1){ 0 := sProjT1 (sRel 0) })
                 ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) })
                 ((lift 1 1 t2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ ,, svass nx A1 |-i B1 : sSort z1 ->
    Σ ;;; Γ ,, svass ny A2 |-i B2 : sSort z2 ->
    Σ ;;; Γ ,, svass nx A1 |-i t1 : B1 ->
    Σ ;;; Γ ,, svass ny A2 |-i t2 : B2 ->
    Σ ;;; Γ |-i sCongLambda B1 B2 t1 t2 pA pB pt :
               sHeq (sProd nx A1 B1) (sLambda nx A1 B1 t1)
                    (sProd ny A2 B2) (sLambda ny A2 B2 t2).
Proof.
  intros Σ Γ s1 s2 z1 z2 nx ny np A1 A2 B1 B2 t1 t2 pA pB pt hpA hpB hpt
         hB1 hB2 ht1 ht2.
  destruct (prod_sorts hpA hpB hB1 hB2) as [ss [zz [mm [[e e0] e1]]]].
  eapply type_CongLambda''.
  - eapply heq_sort. eassumption.
  - eapply heq_sort. eassumption.
  - eassumption.
  - assumption.
  - eapply type_conv' ; eassumption.
  - assumption.
  - assumption.
Defined.

Lemma type_CongApp'' :
  forall {Σ Γ s z nx ny np A1 A2 B1 B2 u1 u2 v1 v2 pA pB pu pv},
    Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2 ->
    Σ ;;; Γ ,, svass np (sPack A1 A2)
    |-i pB : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                 (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ |-i pu : sHeq (sProd nx A1 B1) u1 (sProd ny A2 B2) u2 ->
    Σ ;;; Γ |-i pv : sHeq A1 v1 A2 v2 ->
    Σ ;;; Γ ,, svass nx A1 |-i B1 : sSort z ->
    Σ ;;; Γ ,, svass ny A2 |-i B2 : sSort z ->
    Σ ;;; Γ |-i sCongApp B1 B2 pu pA pB pv :
               sHeq (B1{0 := v1}) (sApp u1 nx A1 B1 v1)
                    (B2{0 := v2}) (sApp u2 ny A2 B2 v2).
Proof.
  intros Σ Γ s z nx ny np A1 A2 B1 B2 u1 u2 v1 v2 pA pB pu pv
         hpA hpB hpu hpv hB1 hB2.
  destruct (istype_type hpA) as [? ipA].
  destruct (inversionHeq ipA) as [? [[[[? ?] ?] ?] ?]].
  destruct (istype_type hpB) as [? ipB].
  destruct (inversionHeq ipB) as [? [[[[? ?] ?] ?] ?]].
  destruct (istype_type hpu) as [? ipu].
  destruct (inversionHeq ipu) as [? [[[[? ?] ?] ?] ?]].
  destruct (istype_type hpv) as [? ipv].
  destruct (inversionHeq ipv) as [? [[[[? ?] ?] ?] ?]].
  eapply type_CongApp ; eassumption.
Defined.

Lemma type_CongApp' :
  forall {Σ Γ s1 s2 z1 z2 nx ny np A1 A2 B1 B2 u1 u2 v1 v2 pA pB pu pv},
    Σ ;;; Γ |-i pA : sHeq (sSort s1) A1 (sSort s2) A2 ->
    Σ ;;; Γ ,, svass np (sPack A1 A2)
    |-i pB : sHeq (sSort z1) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                 (sSort z2) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ |-i pu : sHeq (sProd nx A1 B1) u1 (sProd ny A2 B2) u2 ->
    Σ ;;; Γ |-i pv : sHeq A1 v1 A2 v2 ->
    Σ ;;; Γ ,, svass nx A1 |-i B1 : sSort z1 ->
    Σ ;;; Γ ,, svass ny A2 |-i B2 : sSort z2 ->
    Σ ;;; Γ |-i sCongApp B1 B2 pu pA pB pv :
               sHeq (B1{0 := v1}) (sApp u1 nx A1 B1 v1)
                    (B2{0 := v2}) (sApp u2 ny A2 B2 v2).
Proof.
  intros Σ Γ s1 s2 z1 z2 nx ny np A1 A2 B1 B2 u1 u2 v1 v2 pA pB pu pv
         hpA hpB hpu hpv hB1 hB2.
  destruct (prod_sorts hpA hpB hB1 hB2) as [ss [zz [mm [[e e0] e1]]]].
  eapply type_CongApp'' ; try eassumption.
  - eapply heq_sort. eassumption.
  - eapply heq_sort. eassumption.
  - eapply type_conv' ; eassumption.
Defined.

Lemma type_CongEq'' :
  forall {Σ Γ s A1 A2 u1 u2 v1 v2 pA pu pv},
    Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2 ->
    Σ ;;; Γ |-i pu : sHeq A1 u1 A2 u2 ->
    Σ ;;; Γ |-i pv : sHeq A1 v1 A2 v2 ->
    Σ ;;; Γ |-i sCongEq pA pu pv :
               sHeq (sSort s) (sEq A1 u1 v1) (sSort s) (sEq A2 u2 v2).
Proof.
  intros Σ Γ s A1 A2 u1 u2 v1 v2 pA pu pv hpA hpu hpv.
  destruct (istype_type hpA) as [? iA].
  destruct (istype_type hpu) as [? iu].
  destruct (istype_type hpv) as [? iv].
  destruct (inversionHeq iA) as [? [[[[? ?] ?] ?] ?]].
  destruct (inversionHeq iu) as [? [[[[? ?] ?] ?] ?]].
  destruct (inversionHeq iv) as [? [[[[? ?] ?] ?] ?]].
  eapply type_CongEq.
  all: assumption.
Defined.

Lemma type_CongEq' :
  forall {Σ Γ s1 s2 A1 A2 u1 u2 v1 v2 pA pu pv},
    Σ ;;; Γ |-i pA : sHeq (sSort s1) A1 (sSort s2) A2 ->
    Σ ;;; Γ |-i pu : sHeq A1 u1 A2 u2 ->
    Σ ;;; Γ |-i pv : sHeq A1 v1 A2 v2 ->
    Σ ;;; Γ |-i sCongEq pA pu pv
             : sHeq (sSort s1) (sEq A1 u1 v1)
                    (sSort s2) (sEq A2 u2 v2).
Proof.
  intros Σ Γ s1 s2 A1 A2 u1 u2 v1 v2 pA pu pv hpA hpu hpv.
  destruct (istype_type hpA) as [? iA].
  destruct (istype_type hpu) as [? iu].
  destruct (istype_type hpv) as [? iv].
  destruct (inversionHeq iA) as [? [[[[? hs2] ?] hA2] ?]].
  destruct (inversionHeq iu) as [? [[[[? ?] ?] ?] ?]].
  destruct (inversionHeq iv) as [? [[[[? ?] ?] ?] ?]].
  eapply type_conv'.
  - eapply type_CongEq''.
    + eapply heq_sort. eassumption.
    + eassumption.
    + eassumption.
  - apply cong_Heq.
    all: try (apply eq_reflexivity).
    + eassumption.
    + apply sorts_in_sort ; assumption.
    + apply type_Eq ; assumption.
    + eapply type_conv'.
      * apply type_Eq ; [ apply hA2 | assumption .. ].
      * eapply sorts_in_sort ; [ apply hs2 | assumption ].
Defined.

Lemma type_CongRefl'' :
  forall {Σ Γ s A1 A2 u1 u2 pA pu},
    Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2 ->
    Σ ;;; Γ |-i pu : sHeq A1 u1 A2 u2 ->
    Σ ;;; Γ |-i sCongRefl pA pu :
               sHeq (sEq A1 u1 u1) (sRefl A1 u1) (sEq A2 u2 u2) (sRefl A2 u2).
Proof.
  intros Σ Γ s A1 A2 u1 u2 pA pu hpA hpu.
  destruct (istype_type hpA) as [? iA].
  destruct (istype_type hpu) as [? iu].
  destruct (inversionHeq iA) as [? [[[[? ?] ?] ?] ?]].
  destruct (inversionHeq iu) as [? [[[[? ?] ?] ?] ?]].
  eapply type_CongRefl.
  all: eassumption.
Defined.

Lemma type_CongRefl' :
  forall {Σ Γ s1 s2 A1 A2 u1 u2 pA pu},
    Σ ;;; Γ |-i pA : sHeq (sSort s1) A1 (sSort s2) A2 ->
    Σ ;;; Γ |-i pu : sHeq A1 u1 A2 u2 ->
    Σ ;;; Γ |-i sCongRefl pA pu :
               sHeq (sEq A1 u1 u1) (sRefl A1 u1) (sEq A2 u2 u2) (sRefl A2 u2).
Proof.
  intros Σ Γ s1 s2 A1 A2 u1 u2 pA pu hpA hpu.
  destruct (istype_type hpA) as [? iA].
  destruct (istype_type hpu) as [? iu].
  destruct (inversionHeq iA) as [? [[[[? ?] ?] ?] ?]].
  destruct (inversionHeq iu) as [? [[[[? ?] ?] ?] ?]].
  eapply type_CongRefl''.
  - eapply heq_sort. eassumption.
  - assumption.
Defined.

Lemma type_EqToHeq' :
  forall {Σ Γ A u v p},
    Σ ;;; Γ |-i p : sEq A u v ->
    Σ ;;; Γ |-i sEqToHeq p : sHeq A u A v.
Proof.
  intros Σ Γ A u v p h.
  destruct (istype_type h) as [? i].
  destruct (inversionEq i) as [? [[[? ?] ?] ?]].
  eapply type_EqToHeq ; eassumption.
Defined.

Lemma type_ProjT1' :
  forall {Σ Γ A1 A2 p},
    Σ ;;; Γ |-i p : sPack A1 A2 ->
    Σ ;;; Γ |-i sProjT1 p : A1.
Proof.
  intros Σ Γ A1 A2 p hp.
  destruct (istype_type hp) as [? i].
  destruct (inversionPack i) as [s [[? ?] ?]].
  eapply type_ProjT1 ; [.. | eassumption] ; eassumption.
Defined.

Lemma type_ProjT2' :
  forall {Σ Γ A1 A2 p},
    Σ ;;; Γ |-i p : sPack A1 A2 ->
    Σ ;;; Γ |-i sProjT2 p : A2.
Proof.
  intros Σ Γ A1 A2 p hp.
  destruct (istype_type hp) as [? i].
  destruct (inversionPack i) as [s [[? ?] ?]].
  eapply type_ProjT2 ; [.. | eassumption] ; eassumption.
Defined.

Lemma type_ProjTe' :
  forall {Σ Γ A1 A2 p},
    Σ ;;; Γ |-i p : sPack A1 A2 ->
    Σ ;;; Γ |-i sProjTe p : sHeq A1 (sProjT1 p) A2 (sProjT2 p).
Proof.
  intros Σ Γ A1 A2 p hp.
  destruct (istype_type hp) as [? i].
  destruct (inversionPack i) as [s [[? ?] ?]].
  eapply type_ProjTe ; [.. | eassumption] ; eassumption.
Defined.

Lemma type_Refl' :
  forall {Σ Γ A u},
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i sRefl A u : sEq A u u.
Proof.
  intros Σ Γ A u h.
  destruct (istype_type h) as [? i].
  eapply type_Refl ; eassumption.
Defined.

Lemma type_Transport' :
  forall {Σ Γ s T1 T2 p t},
    Σ ;;; Γ |-i p : sEq (sSort s) T1 T2 ->
    Σ ;;; Γ |-i t : T1 ->
    Σ ;;; Γ |-i sTransport T1 T2 p t : T2.
Proof.
  intros Σ Γ s T1 T2 p t hp ht.
  destruct (istype_type hp) as [? i].
  destruct (inversionEq i) as [? [[[? ?] ?] ?]].
  eapply type_Transport ; eassumption.
Defined.

Lemma type_HeqTypeEq' :
  forall {Σ Γ A u B v p s},
    Σ ;;; Γ |-i p : sHeq A u B v ->
    Σ ;;; Γ |-i A : sSort s ->
    Σ ;;; Γ |-i sHeqTypeEq p : sEq (sSort s) A B.
Proof.
  intros Σ Γ A u B v p s hp hA.
  destruct (istype_type hp) as [? i].
  destruct (inversionHeq i) as [? [[[[? ?] ?] ?] ?]].
  eapply type_HeqTypeEq ; try eassumption.
  destruct (uniqueness pi1_ hA).
  eapply type_conv' ; eassumption.
Defined.
