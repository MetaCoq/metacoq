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

| type_Construct Γ ind i :
    wf Σ Γ ->
    forall univs decl (isdecl : sdeclared_constructor (fst Σ) (ind, i) univs decl),
    Σ ;;; Γ |-i (sConstruct ind i)
             : stype_of_constructor (fst Σ) (ind, i) univs decl isdecl

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

(* Temporary:
   We define the notion of ETT compatibility to restrict the syntax
   to the one that is allowed in ETT.
 *)
Inductive Xcomp : sterm -> Type :=
| xcomp_Rel n : Xcomp (sRel n)
| xcomp_Sort s : Xcomp (sSort s)
| xcomp_Prod na A B :
    Xcomp A ->
    Xcomp B ->
    Xcomp (sProd na A B)
| xcomp_Lambda na A B t :
    Xcomp A ->
    Xcomp B ->
    Xcomp t ->
    Xcomp (sLambda na A B t)
| xcomp_App u na A B v :
    Xcomp u ->
    Xcomp A ->
    Xcomp B ->
    Xcomp v ->
    Xcomp (sApp u na A B v)
| xcomp_Eq A u v :
    Xcomp A ->
    Xcomp u ->
    Xcomp v ->
    Xcomp (sEq A u v)
| xcomp_Refl A u :
    Xcomp A ->
    Xcomp u ->
    Xcomp (sRefl A u)
| xcomp_Ind ind : Xcomp (sInd ind)
| xcomp_Construct ind i : Xcomp (sConstruct ind i)
.

Derive Signature for Xcomp.

Definition isType (Σ : sglobal_context) (Γ : scontext) (t : sterm) :=
  ∑ s, Σ ;;; Γ |-i t : sSort s.

Inductive type_constructors (Σ : sglobal_context) (Γ : scontext) :
  list (ident * sterm * nat) -> Type :=
| type_cnstrs_nil : type_constructors Σ Γ []
| type_cnstrs_cons id t n l :
    isType Σ Γ t ->
    Xcomp t ->
    type_constructors Σ Γ l ->
    (** TODO: check it has n products ending in a tRel application *)
    type_constructors Σ Γ ((id, t, n) :: l).

Inductive type_projections (Σ : sglobal_context) (Γ : scontext) :
  list (ident * sterm) -> Type :=
| type_projs_nil : type_projections Σ Γ []
| type_projs_cons id t l :
    isType Σ Γ t ->
    Xcomp t ->
    type_projections Σ Γ l ->
    type_projections Σ Γ ((id, t) :: l).

Definition rev {A} (l : list A) : list A :=
  let fix aux (l : list A) (acc : list A) : list A :=
    match l with
    | [] => acc
    | x :: l => aux l (x :: acc)
    end
  in aux l [].

Definition rev_map {A B} (f : A -> B) (l : list A) : list B :=
  let fix aux (l : list A) (acc : list B) : list B :=
    match l with
    | [] => acc
    | x :: l => aux l (f x :: acc)
    end
  in aux l [].

Definition arities_context (l : list sone_inductive_body) :=
  rev_map (fun ind => svass (nNamed ind.(sind_name)) ind.(sind_type)) l.

Definition isArity Σ Γ T :=
  isType Σ Γ T (* FIXME  /\ decompose_prod_n *).

Inductive type_inddecls (Σ : sglobal_context) (pars : scontext) (Γ : scontext) :
  list sone_inductive_body -> Type :=
| type_ind_nil : type_inddecls Σ pars Γ []
| type_ind_cons na ty cstrs projs kelim l :
    (** Arity is well-formed *)
    isArity Σ [] ty ->
    (** TMP: The type can be written in ETT *)
    Xcomp ty ->
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

Derive Signature for fresh_global.

Inductive type_global_env φ : sglobal_declarations -> Type :=
| globenv_nil : type_global_env φ []
| globenv_decl Σ d :
    type_global_env φ Σ ->
    fresh_global (sglobal_decl_ident d) Σ ->
    type_global_decl (Σ, φ) d ->
    type_global_env φ (d :: Σ).

Derive Signature for type_global_env.

Definition type_glob (Σ : sglobal_context) : Type :=
  type_global_env (snd Σ) (fst Σ).


Set Printing Depth 5000.

Scheme typing_ind' := Induction for typing Sort Type
  with wf_ind' := Induction for wf Sort Type
  with eq_term_ind' := Induction for eq_term Sort Type.

Lemma typing_all :
  forall (Σ : sglobal_context) (P : forall (s : scontext) (s0 s1 : sterm), Σ;;; s |-i s0 : s1 -> Type)
         (P0 : forall s : scontext, wf Σ s -> Type)
         (P1 : forall (s : scontext) (s0 s1 s2 : sterm), Σ;;; s |-i s0 = s1 : s2 -> Type),
       (forall (Γ : scontext) (n : nat) (w : wf Σ Γ),
        P0 Γ w ->
        forall isdecl : n < #|Γ|,
        P Γ (sRel n) (lift0 (S n) (sdecl_type (safe_nth Γ (exist (fun n0 : nat => n0 < #|Γ|) n isdecl)))) (type_Rel Σ Γ n w isdecl)) ->
       (forall (Γ : scontext) (s : sort) (w : wf Σ Γ), P0 Γ w -> P Γ (sSort s) (sSort (succ_sort s)) (type_Sort Σ Γ s w)) ->
       (forall (Γ : scontext) (n : name) (t b : sterm) (s1 s2 : sort) (t0 : Σ;;; Γ |-i t : sSort s1),
        P Γ t (sSort s1) t0 ->
        forall t1 : Σ;;; Γ,, svass n t |-i b : sSort s2,
        P (Γ,, svass n t) b (sSort s2) t1 -> P Γ (sProd n t b) (sSort (max_sort s1 s2)) (type_Prod Σ Γ n t b s1 s2 t0 t1)) ->
       (forall (Γ : scontext) (n n' : name) (t b : sterm) (s1 s2 : sort) (bty : sterm) (t0 : Σ;;; Γ |-i t : sSort s1),
        P Γ t (sSort s1) t0 ->
        forall t1 : Σ;;; Γ,, svass n t |-i bty : sSort s2,
        P (Γ,, svass n t) bty (sSort s2) t1 ->
        forall t2 : Σ;;; Γ,, svass n t |-i b : bty,
        P (Γ,, svass n t) b bty t2 -> P Γ (sLambda n t bty b) (sProd n' t bty) (type_Lambda Σ Γ n n' t b s1 s2 bty t0 t1 t2)) ->
       (forall (Γ : scontext) (n : name) (s1 s2 : sort) (t A B u : sterm) (t0 : Σ;;; Γ |-i A : sSort s1),
        P Γ A (sSort s1) t0 ->
        forall t1 : Σ;;; Γ,, svass n A |-i B : sSort s2,
        P (Γ,, svass n A) B (sSort s2) t1 ->
        forall t2 : Σ;;; Γ |-i t : sProd n A B,
        P Γ t (sProd n A B) t2 ->
        forall t3 : Σ;;; Γ |-i u : A, P Γ u A t3 -> P Γ (sApp t n A B u) (B {0 := u}) (type_App Σ Γ n s1 s2 t A B u t0 t1 t2 t3)) ->
       (forall (Γ : scontext) (s : sort) (A u v : sterm) (t : Σ;;; Γ |-i A : sSort s),
        P Γ A (sSort s) t ->
        forall t0 : Σ;;; Γ |-i u : A,
        P Γ u A t0 -> forall t1 : Σ;;; Γ |-i v : A, P Γ v A t1 -> P Γ (sEq A u v) (sSort s) (type_Eq Σ Γ s A u v t t0 t1)) ->
       (forall (Γ : scontext) (s : sort) (A u : sterm) (t : Σ;;; Γ |-i A : sSort s),
        P Γ A (sSort s) t -> forall t0 : Σ;;; Γ |-i u : A, P Γ u A t0 -> P Γ (sRefl A u) (sEq A u u) (type_Refl Σ Γ s A u t t0)) ->
       (forall (Γ : scontext) (nx ne : name) (s1 s2 : sort) (A u v P2 p w : sterm) (t : Σ;;; Γ |-i A : sSort s1),
        P Γ A (sSort s1) t ->
        forall t0 : Σ;;; Γ |-i u : A,
        P Γ u A t0 ->
        forall t1 : Σ;;; Γ |-i v : A,
        P Γ v A t1 ->
        forall t2 : Σ;;; (Γ,, svass nx A),, svass ne (sEq (lift0 1 A) (lift0 1 u) (sRel 0)) |-i P2 : sSort s2,
        P ((Γ,, svass nx A),, svass ne (sEq (lift0 1 A) (lift0 1 u) (sRel 0))) P2 (sSort s2) t2 ->
        forall t3 : Σ;;; Γ |-i p : sEq A u v,
        P Γ p (sEq A u v) t3 ->
        forall t4 : Σ;;; Γ |-i w : (P2 {1 := u}) {0 := sRefl A u},
        P Γ w ((P2 {1 := u}) {0 := sRefl A u}) t4 ->
        P Γ (sJ A u P2 w v p) ((P2 {1 := v}) {0 := p}) (type_J Σ Γ nx ne s1 s2 A u v P2 p w t t0 t1 t2 t3 t4)) ->
       (forall (Γ : scontext) (s : sort) (T1 T2 p t : sterm) (t0 : Σ;;; Γ |-i T1 : sSort s),
        P Γ T1 (sSort s) t0 ->
        forall t1 : Σ;;; Γ |-i T2 : sSort s,
        P Γ T2 (sSort s) t1 ->
        forall t2 : Σ;;; Γ |-i p : sEq (sSort s) T1 T2,
        P Γ p (sEq (sSort s) T1 T2) t2 ->
        forall t3 : Σ;;; Γ |-i t : T1, P Γ t T1 t3 -> P Γ (sTransport T1 T2 p t) T2 (type_Transport Σ Γ s T1 T2 p t t0 t1 t2 t3)) ->
       (forall (Γ : scontext) (A a B b : sterm) (s : sort) (t : Σ;;; Γ |-i A : sSort s),
        P Γ A (sSort s) t ->
        forall t0 : Σ;;; Γ |-i B : sSort s,
        P Γ B (sSort s) t0 ->
        forall t1 : Σ;;; Γ |-i a : A,
        P Γ a A t1 ->
        forall t2 : Σ;;; Γ |-i b : B, P Γ b B t2 -> P Γ (sHeq A a B b) (sSort (succ_sort s)) (type_Heq Σ Γ A a B b s t t0 t1 t2)) ->
       (forall (Γ : scontext) (A u v p : sterm) (s : sort) (t : Σ;;; Γ |-i p : sHeq A u A v),
        P Γ p (sHeq A u A v) t ->
        forall t0 : Σ;;; Γ |-i A : sSort s,
        P Γ A (sSort s) t0 ->
        forall t1 : Σ;;; Γ |-i u : A,
        P Γ u A t1 ->
        forall t2 : Σ;;; Γ |-i v : A, P Γ v A t2 -> P Γ (sHeqToEq p) (sEq A u v) (type_HeqToEq Σ Γ A u v p s t t0 t1 t2)) ->
       (forall (Γ : scontext) (A a : sterm) (s : sort) (t : Σ;;; Γ |-i A : sSort s),
        P Γ A (sSort s) t ->
        forall t0 : Σ;;; Γ |-i a : A, P Γ a A t0 -> P Γ (sHeqRefl A a) (sHeq A a A a) (type_HeqRefl Σ Γ A a s t t0)) ->
       (forall (Γ : scontext) (A a B b p : sterm) (s : sort) (t : Σ;;; Γ |-i A : sSort s),
        P Γ A (sSort s) t ->
        forall t0 : Σ;;; Γ |-i B : sSort s,
        P Γ B (sSort s) t0 ->
        forall t1 : Σ;;; Γ |-i a : A,
        P Γ a A t1 ->
        forall t2 : Σ;;; Γ |-i b : B,
        P Γ b B t2 ->
        forall t3 : Σ;;; Γ |-i p : sHeq A a B b,
        P Γ p (sHeq A a B b) t3 -> P Γ (sHeqSym p) (sHeq B b A a) (type_HeqSym Σ Γ A a B b p s t t0 t1 t2 t3)) ->
       (forall (Γ : scontext) (A a B b C c p q : sterm) (s : sort) (t : Σ;;; Γ |-i A : sSort s),
        P Γ A (sSort s) t ->
        forall t0 : Σ;;; Γ |-i B : sSort s,
        P Γ B (sSort s) t0 ->
        forall t1 : Σ;;; Γ |-i C : sSort s,
        P Γ C (sSort s) t1 ->
        forall t2 : Σ;;; Γ |-i a : A,
        P Γ a A t2 ->
        forall t3 : Σ;;; Γ |-i b : B,
        P Γ b B t3 ->
        forall t4 : Σ;;; Γ |-i c : C,
        P Γ c C t4 ->
        forall t5 : Σ;;; Γ |-i p : sHeq A a B b,
        P Γ p (sHeq A a B b) t5 ->
        forall t6 : Σ;;; Γ |-i q : sHeq B b C c,
        P Γ q (sHeq B b C c) t6 -> P Γ (sHeqTrans p q) (sHeq A a C c) (type_HeqTrans Σ Γ A a B b C c p q s t t0 t1 t2 t3 t4 t5 t6)) ->
       (forall (Γ : scontext) (A B p t : sterm) (s : sort) (t0 : Σ;;; Γ |-i A : sSort s),
        P Γ A (sSort s) t0 ->
        forall t1 : Σ;;; Γ |-i B : sSort s,
        P Γ B (sSort s) t1 ->
        forall t2 : Σ;;; Γ |-i t : A,
        P Γ t A t2 ->
        forall t3 : Σ;;; Γ |-i p : sEq (sSort s) A B,
        P Γ p (sEq (sSort s) A B) t3 ->
        P Γ (sHeqTransport p t) (sHeq A t B (sTransport A B p t)) (type_HeqTransport Σ Γ A B p t s t0 t1 t2 t3)) ->
       (forall (Γ : scontext) (s z : sort) (nx ny np : name) (A1 A2 B1 B2 pA pB : sterm)
          (t : Σ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2),
        P Γ pA (sHeq (sSort s) A1 (sSort s) A2) t ->
        forall
          t0 : Σ;;; Γ,, svass np (sPack A1 A2) |-i pB
               : sHeq (sSort z) ((lift 1 1 B1) {0 := sProjT1 (sRel 0)}) (sSort z) ((lift 1 1 B2) {0 := sProjT2 (sRel 0)}),
        P (Γ,, svass np (sPack A1 A2)) pB
          (sHeq (sSort z) ((lift 1 1 B1) {0 := sProjT1 (sRel 0)}) (sSort z) ((lift 1 1 B2) {0 := sProjT2 (sRel 0)})) t0 ->
        forall t1 : Σ;;; Γ |-i A1 : sSort s,
        P Γ A1 (sSort s) t1 ->
        forall t2 : Σ;;; Γ |-i A2 : sSort s,
        P Γ A2 (sSort s) t2 ->
        forall t3 : Σ;;; Γ,, svass nx A1 |-i B1 : sSort z,
        P (Γ,, svass nx A1) B1 (sSort z) t3 ->
        forall t4 : Σ;;; Γ,, svass ny A2 |-i B2 : sSort z,
        P (Γ,, svass ny A2) B2 (sSort z) t4 ->
        P Γ (sCongProd B1 B2 pA pB) (sHeq (sSort (max_sort s z)) (sProd nx A1 B1) (sSort (max_sort s z)) (sProd ny A2 B2))
          (type_CongProd Σ Γ s z nx ny np A1 A2 B1 B2 pA pB t t0 t1 t2 t3 t4)) ->
       (forall (Γ : scontext) (s z : sort) (nx ny np : name) (A1 A2 B1 B2 t1 t2 pA pB pt : sterm)
          (t : Σ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2),
        P Γ pA (sHeq (sSort s) A1 (sSort s) A2) t ->
        forall
          t0 : Σ;;; Γ,, svass np (sPack A1 A2) |-i pB
               : sHeq (sSort z) ((lift 1 1 B1) {0 := sProjT1 (sRel 0)}) (sSort z) ((lift 1 1 B2) {0 := sProjT2 (sRel 0)}),
        P (Γ,, svass np (sPack A1 A2)) pB
          (sHeq (sSort z) ((lift 1 1 B1) {0 := sProjT1 (sRel 0)}) (sSort z) ((lift 1 1 B2) {0 := sProjT2 (sRel 0)})) t0 ->
        forall
          t3 : Σ;;; Γ,, svass np (sPack A1 A2) |-i pt
               : sHeq ((lift 1 1 B1) {0 := sProjT1 (sRel 0)}) ((lift 1 1 t1) {0 := sProjT1 (sRel 0)})
                   ((lift 1 1 B2) {0 := sProjT2 (sRel 0)}) ((lift 1 1 t2) {0 := sProjT2 (sRel 0)}),
        P (Γ,, svass np (sPack A1 A2)) pt
          (sHeq ((lift 1 1 B1) {0 := sProjT1 (sRel 0)}) ((lift 1 1 t1) {0 := sProjT1 (sRel 0)})
             ((lift 1 1 B2) {0 := sProjT2 (sRel 0)}) ((lift 1 1 t2) {0 := sProjT2 (sRel 0)})) t3 ->
        forall t4 : Σ;;; Γ |-i A1 : sSort s,
        P Γ A1 (sSort s) t4 ->
        forall t5 : Σ;;; Γ |-i A2 : sSort s,
        P Γ A2 (sSort s) t5 ->
        forall t6 : Σ;;; Γ,, svass nx A1 |-i B1 : sSort z,
        P (Γ,, svass nx A1) B1 (sSort z) t6 ->
        forall t7 : Σ;;; Γ,, svass ny A2 |-i B2 : sSort z,
        P (Γ,, svass ny A2) B2 (sSort z) t7 ->
        forall t8 : Σ;;; Γ,, svass nx A1 |-i t1 : B1,
        P (Γ,, svass nx A1) t1 B1 t8 ->
        forall t9 : Σ;;; Γ,, svass ny A2 |-i t2 : B2,
        P (Γ,, svass ny A2) t2 B2 t9 ->
        P Γ (sCongLambda B1 B2 t1 t2 pA pB pt) (sHeq (sProd nx A1 B1) (sLambda nx A1 B1 t1) (sProd ny A2 B2) (sLambda ny A2 B2 t2))
          (type_CongLambda Σ Γ s z nx ny np A1 A2 B1 B2 t1 t2 pA pB pt t t0 t3 t4 t5 t6 t7 t8 t9)) ->
       (forall (Γ : scontext) (s z : sort) (nx ny np : name) (A1 A2 B1 B2 u1 u2 v1 v2 pA pB pu pv : sterm)
          (t : Σ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2),
        P Γ pA (sHeq (sSort s) A1 (sSort s) A2) t ->
        forall
          t0 : Σ;;; Γ,, svass np (sPack A1 A2) |-i pB
               : sHeq (sSort z) ((lift 1 1 B1) {0 := sProjT1 (sRel 0)}) (sSort z) ((lift 1 1 B2) {0 := sProjT2 (sRel 0)}),
        P (Γ,, svass np (sPack A1 A2)) pB
          (sHeq (sSort z) ((lift 1 1 B1) {0 := sProjT1 (sRel 0)}) (sSort z) ((lift 1 1 B2) {0 := sProjT2 (sRel 0)})) t0 ->
        forall t1 : Σ;;; Γ |-i pu : sHeq (sProd nx A1 B1) u1 (sProd ny A2 B2) u2,
        P Γ pu (sHeq (sProd nx A1 B1) u1 (sProd ny A2 B2) u2) t1 ->
        forall t2 : Σ;;; Γ |-i pv : sHeq A1 v1 A2 v2,
        P Γ pv (sHeq A1 v1 A2 v2) t2 ->
        forall t3 : Σ;;; Γ |-i A1 : sSort s,
        P Γ A1 (sSort s) t3 ->
        forall t4 : Σ;;; Γ |-i A2 : sSort s,
        P Γ A2 (sSort s) t4 ->
        forall t5 : Σ;;; Γ,, svass nx A1 |-i B1 : sSort z,
        P (Γ,, svass nx A1) B1 (sSort z) t5 ->
        forall t6 : Σ;;; Γ,, svass ny A2 |-i B2 : sSort z,
        P (Γ,, svass ny A2) B2 (sSort z) t6 ->
        forall t7 : Σ;;; Γ |-i u1 : sProd nx A1 B1,
        P Γ u1 (sProd nx A1 B1) t7 ->
        forall t8 : Σ;;; Γ |-i u2 : sProd ny A2 B2,
        P Γ u2 (sProd ny A2 B2) t8 ->
        forall t9 : Σ;;; Γ |-i v1 : A1,
        P Γ v1 A1 t9 ->
        forall t10 : Σ;;; Γ |-i v2 : A2,
        P Γ v2 A2 t10 ->
        P Γ (sCongApp B1 B2 pu pA pB pv) (sHeq (B1 {0 := v1}) (sApp u1 nx A1 B1 v1) (B2 {0 := v2}) (sApp u2 ny A2 B2 v2))
          (type_CongApp Σ Γ s z nx ny np A1 A2 B1 B2 u1 u2 v1 v2 pA pB pu pv t t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10)) ->
       (forall (Γ : scontext) (s : sort) (A1 A2 u1 u2 v1 v2 pA pu pv : sterm) (t : Σ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2),
        P Γ pA (sHeq (sSort s) A1 (sSort s) A2) t ->
        forall t0 : Σ;;; Γ |-i pu : sHeq A1 u1 A2 u2,
        P Γ pu (sHeq A1 u1 A2 u2) t0 ->
        forall t1 : Σ;;; Γ |-i pv : sHeq A1 v1 A2 v2,
        P Γ pv (sHeq A1 v1 A2 v2) t1 ->
        forall t2 : Σ;;; Γ |-i A1 : sSort s,
        P Γ A1 (sSort s) t2 ->
        forall t3 : Σ;;; Γ |-i A2 : sSort s,
        P Γ A2 (sSort s) t3 ->
        forall t4 : Σ;;; Γ |-i u1 : A1,
        P Γ u1 A1 t4 ->
        forall t5 : Σ;;; Γ |-i u2 : A2,
        P Γ u2 A2 t5 ->
        forall t6 : Σ;;; Γ |-i v1 : A1,
        P Γ v1 A1 t6 ->
        forall t7 : Σ;;; Γ |-i v2 : A2,
        P Γ v2 A2 t7 ->
        P Γ (sCongEq pA pu pv) (sHeq (sSort s) (sEq A1 u1 v1) (sSort s) (sEq A2 u2 v2))
          (type_CongEq Σ Γ s A1 A2 u1 u2 v1 v2 pA pu pv t t0 t1 t2 t3 t4 t5 t6 t7)) ->
       (forall (Γ : scontext) (s : sort) (A1 A2 u1 u2 pA pu : sterm) (t : Σ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2),
        P Γ pA (sHeq (sSort s) A1 (sSort s) A2) t ->
        forall t0 : Σ;;; Γ |-i pu : sHeq A1 u1 A2 u2,
        P Γ pu (sHeq A1 u1 A2 u2) t0 ->
        forall t1 : Σ;;; Γ |-i A1 : sSort s,
        P Γ A1 (sSort s) t1 ->
        forall t2 : Σ;;; Γ |-i A2 : sSort s,
        P Γ A2 (sSort s) t2 ->
        forall t3 : Σ;;; Γ |-i u1 : A1,
        P Γ u1 A1 t3 ->
        forall t4 : Σ;;; Γ |-i u2 : A2,
        P Γ u2 A2 t4 ->
        P Γ (sCongRefl pA pu) (sHeq (sEq A1 u1 u1) (sRefl A1 u1) (sEq A2 u2 u2) (sRefl A2 u2))
          (type_CongRefl Σ Γ s A1 A2 u1 u2 pA pu t t0 t1 t2 t3 t4)) ->
       (forall (Γ : scontext) (A u v p : sterm) (s : sort) (t : Σ;;; Γ |-i p : sEq A u v),
        P Γ p (sEq A u v) t ->
        forall t0 : Σ;;; Γ |-i A : sSort s,
        P Γ A (sSort s) t0 ->
        forall t1 : Σ;;; Γ |-i u : A,
        P Γ u A t1 ->
        forall t2 : Σ;;; Γ |-i v : A, P Γ v A t2 -> P Γ (sEqToHeq p) (sHeq A u A v) (type_EqToHeq Σ Γ A u v p s t t0 t1 t2)) ->
       (forall (Γ : scontext) (A u B v p : sterm) (s : sort) (t : Σ;;; Γ |-i p : sHeq A u B v),
        P Γ p (sHeq A u B v) t ->
        forall t0 : Σ;;; Γ |-i A : sSort s,
        P Γ A (sSort s) t0 ->
        forall t1 : Σ;;; Γ |-i B : sSort s,
        P Γ B (sSort s) t1 ->
        forall t2 : Σ;;; Γ |-i u : A,
        P Γ u A t2 ->
        forall t3 : Σ;;; Γ |-i v : B,
        P Γ v B t3 -> P Γ (sHeqTypeEq p) (sEq (sSort s) A B) (type_HeqTypeEq Σ Γ A u B v p s t t0 t1 t2 t3)) ->
       (forall (Γ : scontext) (A1 A2 : sterm) (s : sort) (t : Σ;;; Γ |-i A1 : sSort s),
        P Γ A1 (sSort s) t ->
        forall t0 : Σ;;; Γ |-i A2 : sSort s, P Γ A2 (sSort s) t0 -> P Γ (sPack A1 A2) (sSort s) (type_Pack Σ Γ A1 A2 s t t0)) ->
       (forall (Γ : scontext) (A1 A2 p : sterm) (s : sort) (t : Σ;;; Γ |-i A1 : sSort s),
        P Γ A1 (sSort s) t ->
        forall t0 : Σ;;; Γ |-i A2 : sSort s,
        P Γ A2 (sSort s) t0 ->
        forall t1 : Σ;;; Γ |-i p : sPack A1 A2, P Γ p (sPack A1 A2) t1 -> P Γ (sProjT1 p) A1 (type_ProjT1 Σ Γ A1 A2 p s t t0 t1)) ->
       (forall (Γ : scontext) (A1 A2 p : sterm) (s : sort) (t : Σ;;; Γ |-i A1 : sSort s),
        P Γ A1 (sSort s) t ->
        forall t0 : Σ;;; Γ |-i A2 : sSort s,
        P Γ A2 (sSort s) t0 ->
        forall t1 : Σ;;; Γ |-i p : sPack A1 A2, P Γ p (sPack A1 A2) t1 -> P Γ (sProjT2 p) A2 (type_ProjT2 Σ Γ A1 A2 p s t t0 t1)) ->
       (forall (Γ : scontext) (A1 A2 p : sterm) (s : sort) (t : Σ;;; Γ |-i A1 : sSort s),
        P Γ A1 (sSort s) t ->
        forall t0 : Σ;;; Γ |-i A2 : sSort s,
        P Γ A2 (sSort s) t0 ->
        forall t1 : Σ;;; Γ |-i p : sPack A1 A2,
        P Γ p (sPack A1 A2) t1 -> P Γ (sProjTe p) (sHeq A1 (sProjT1 p) A2 (sProjT2 p)) (type_ProjTe Σ Γ A1 A2 p s t t0 t1)) ->
       (forall (Γ : scontext) (ind : inductive) (w : wf Σ Γ),
        P0 Γ w ->
        forall (univs : universe_context) (decl : sone_inductive_body) (isdecl : sdeclared_inductive (fst Σ) ind univs decl),
        P Γ (sInd ind) (sind_type decl) (type_Ind Σ Γ ind w univs decl isdecl)) ->
       (forall (Γ : scontext) (ind : inductive) (i : nat) (w : wf Σ Γ),
        P0 Γ w ->
        forall (univs : universe_context) (decl : ident * sterm * nat) (isdecl : sdeclared_constructor (fst Σ) (ind, i) univs decl),
        P Γ (sConstruct ind i) (stype_of_constructor (fst Σ) (ind, i) univs decl isdecl)
          (type_Construct Σ Γ ind i w univs decl isdecl)) ->
       (forall (Γ : scontext) (t A B : sterm) (s : sort) (t0 : Σ;;; Γ |-i t : A),
        P Γ t A t0 ->
        forall t1 : Σ;;; Γ |-i B : sSort s,
        P Γ B (sSort s) t1 ->
        forall e : Σ;;; Γ |-i A = B : sSort s, P1 Γ A B (sSort s) e -> P Γ t B (type_conv Σ Γ t A B s t0 t1 e)) ->
       P0 [] (wf_nil Σ) ->
       (forall (s : sort) (Γ : scontext) (x : name) (A : sterm) (w : wf Σ Γ),
        P0 Γ w -> forall t : Σ;;; Γ |-i A : sSort s, P Γ A (sSort s) t -> P0 (Γ,, svass x A) (wf_snoc Σ s Γ x A w t)) ->
       (forall (Γ : scontext) (u A : sterm) (t : Σ;;; Γ |-i u : A), P Γ u A t -> P1 Γ u u A (eq_reflexivity Σ Γ u A t)) ->
       (forall (Γ : scontext) (u v A : sterm) (e : Σ;;; Γ |-i u = v : A), P1 Γ u v A e -> P1 Γ v u A (eq_symmetry Σ Γ u v A e)) ->
       (forall (Γ : scontext) (u v w A : sterm) (e : Σ;;; Γ |-i u = v : A),
        P1 Γ u v A e -> forall e0 : Σ;;; Γ |-i v = w : A, P1 Γ v w A e0 -> P1 Γ u w A (eq_transitivity Σ Γ u v w A e e0)) ->
       (forall (Γ : scontext) (s1 s2 : sort) (n : name) (A B t u : sterm) (t0 : Σ;;; Γ |-i A : sSort s1),
        P Γ A (sSort s1) t0 ->
        forall t1 : Σ;;; Γ,, svass n A |-i B : sSort s2,
        P (Γ,, svass n A) B (sSort s2) t1 ->
        forall t2 : Σ;;; Γ,, svass n A |-i t : B,
        P (Γ,, svass n A) t B t2 ->
        forall t3 : Σ;;; Γ |-i u : A,
        P Γ u A t3 -> P1 Γ (sApp (sLambda n A B t) n A B u) (t {0 := u}) (B {0 := u}) (eq_beta Σ Γ s1 s2 n A B t u t0 t1 t2 t3)) ->
       (forall (Γ : scontext) (nx ne : name) (s1 s2 : sort) (A u P2 w : sterm) (t : Σ;;; Γ |-i A : sSort s1),
        P Γ A (sSort s1) t ->
        forall t0 : Σ;;; Γ |-i u : A,
        P Γ u A t0 ->
        forall t1 : Σ;;; (Γ,, svass nx A),, svass ne (sEq (lift0 1 A) (lift0 1 u) (sRel 0)) |-i P2 : sSort s2,
        P ((Γ,, svass nx A),, svass ne (sEq (lift0 1 A) (lift0 1 u) (sRel 0))) P2 (sSort s2) t1 ->
        forall t2 : Σ;;; Γ |-i w : (P2 {1 := u}) {0 := sRefl A u},
        P Γ w ((P2 {1 := u}) {0 := sRefl A u}) t2 ->
        P1 Γ (sJ A u P2 w u (sRefl A u)) w ((P2 {1 := u}) {0 := sRefl A u}) (eq_JRefl Σ Γ nx ne s1 s2 A u P2 w t t0 t1 t2)) ->
       (forall (Γ : scontext) (s : sort) (A t : sterm) (t0 : Σ;;; Γ |-i A : sSort s),
        P Γ A (sSort s) t0 ->
        forall t1 : Σ;;; Γ |-i t : A,
        P Γ t A t1 -> P1 Γ (sTransport A A (sRefl (sSort s) A) t) t A (eq_TransportRefl Σ Γ s A t t0 t1)) ->
       (forall (Γ : scontext) (s : sort) (T1 T2 t1 t2 : sterm) (e : Σ;;; Γ |-i t1 = t2 : T1),
        P1 Γ t1 t2 T1 e ->
        forall e0 : Σ;;; Γ |-i T1 = T2 : sSort s, P1 Γ T1 T2 (sSort s) e0 -> P1 Γ t1 t2 T2 (eq_conv Σ Γ s T1 T2 t1 t2 e e0)) ->
       (forall (Γ : scontext) (n1 n2 : name) (A1 A2 B1 B2 : sterm) (s1 s2 : sort) (e : Σ;;; Γ |-i A1 = A2 : sSort s1),
        P1 Γ A1 A2 (sSort s1) e ->
        forall e0 : Σ;;; Γ,, svass n1 A1 |-i B1 = B2 : sSort s2,
        P1 (Γ,, svass n1 A1) B1 B2 (sSort s2) e0 ->
        P1 Γ (sProd n1 A1 B1) (sProd n2 A2 B2) (sSort (max_sort s1 s2)) (cong_Prod Σ Γ n1 n2 A1 A2 B1 B2 s1 s2 e e0)) ->
       (forall (Γ : scontext) (n1 n2 n' : name) (A1 A2 B1 B2 t1 t2 : sterm) (s1 s2 : sort) (e : Σ;;; Γ |-i A1 = A2 : sSort s1),
        P1 Γ A1 A2 (sSort s1) e ->
        forall e0 : Σ;;; Γ,, svass n1 A1 |-i B1 = B2 : sSort s2,
        P1 (Γ,, svass n1 A1) B1 B2 (sSort s2) e0 ->
        forall e1 : Σ;;; Γ,, svass n1 A1 |-i t1 = t2 : B1,
        P1 (Γ,, svass n1 A1) t1 t2 B1 e1 ->
        P1 Γ (sLambda n1 A1 B1 t1) (sLambda n2 A2 B2 t2) (sProd n' A1 B1)
          (cong_Lambda Σ Γ n1 n2 n' A1 A2 B1 B2 t1 t2 s1 s2 e e0 e1)) ->
       (forall (Γ : scontext) (n1 n2 : name) (s1 s2 : sort) (t1 t2 A1 A2 B1 B2 u1 u2 : sterm) (e : Σ;;; Γ |-i A1 = A2 : sSort s1),
        P1 Γ A1 A2 (sSort s1) e ->
        forall e0 : Σ;;; Γ,, svass n1 A1 |-i B1 = B2 : sSort s2,
        P1 (Γ,, svass n1 A1) B1 B2 (sSort s2) e0 ->
        forall e1 : Σ;;; Γ |-i t1 = t2 : sProd n1 A1 B1,
        P1 Γ t1 t2 (sProd n1 A1 B1) e1 ->
        forall e2 : Σ;;; Γ |-i u1 = u2 : A1,
        P1 Γ u1 u2 A1 e2 ->
        P1 Γ (sApp t1 n1 A1 B1 u1) (sApp t2 n2 A2 B2 u2) (B1 {0 := u1})
          (cong_App Σ Γ n1 n2 s1 s2 t1 t2 A1 A2 B1 B2 u1 u2 e e0 e1 e2)) ->
       (forall (Γ : scontext) (s : sort) (A1 A2 u1 u2 v1 v2 : sterm) (e : Σ;;; Γ |-i A1 = A2 : sSort s),
        P1 Γ A1 A2 (sSort s) e ->
        forall e0 : Σ;;; Γ |-i u1 = u2 : A1,
        P1 Γ u1 u2 A1 e0 ->
        forall e1 : Σ;;; Γ |-i v1 = v2 : A1,
        P1 Γ v1 v2 A1 e1 -> P1 Γ (sEq A1 u1 v1) (sEq A2 u2 v2) (sSort s) (cong_Eq Σ Γ s A1 A2 u1 u2 v1 v2 e e0 e1)) ->
       (forall (Γ : scontext) (s : sort) (A1 A2 u1 u2 : sterm) (e : Σ;;; Γ |-i A1 = A2 : sSort s),
        P1 Γ A1 A2 (sSort s) e ->
        forall e0 : Σ;;; Γ |-i u1 = u2 : A1,
        P1 Γ u1 u2 A1 e0 -> P1 Γ (sRefl A1 u1) (sRefl A2 u2) (sEq A1 u1 u1) (cong_Refl Σ Γ s A1 A2 u1 u2 e e0)) ->
       (forall (Γ : scontext) (nx ne : name) (s1 s2 : sort) (A1 A2 u1 u2 v1 v2 P2 P3 p1 p2 w1 w2 : sterm)
          (e : Σ;;; Γ |-i A1 = A2 : sSort s1),
        P1 Γ A1 A2 (sSort s1) e ->
        forall e0 : Σ;;; Γ |-i u1 = u2 : A1,
        P1 Γ u1 u2 A1 e0 ->
        forall e1 : Σ;;; Γ |-i v1 = v2 : A1,
        P1 Γ v1 v2 A1 e1 ->
        forall e2 : Σ;;; (Γ,, svass nx A1),, svass ne (sEq (lift0 1 A1) (lift0 1 u1) (sRel 0)) |-i P2 = P3 : sSort s2,
        P1 ((Γ,, svass nx A1),, svass ne (sEq (lift0 1 A1) (lift0 1 u1) (sRel 0))) P2 P3 (sSort s2) e2 ->
        forall e3 : Σ;;; Γ |-i p1 = p2 : sEq A1 u1 v1,
        P1 Γ p1 p2 (sEq A1 u1 v1) e3 ->
        forall e4 : Σ;;; Γ |-i w1 = w2 : (P2 {1 := u1}) {0 := sRefl A1 u1},
        P1 Γ w1 w2 ((P2 {1 := u1}) {0 := sRefl A1 u1}) e4 ->
        P1 Γ (sJ A1 u1 P2 w1 v1 p1) (sJ A2 u2 P3 w2 v2 p2) ((P2 {1 := v1}) {0 := p1})
          (cong_J Σ Γ nx ne s1 s2 A1 A2 u1 u2 v1 v2 P2 P3 p1 p2 w1 w2 e e0 e1 e2 e3 e4)) ->
       (forall (Γ : scontext) (s : sort) (A1 A2 B1 B2 p1 p2 t1 t2 : sterm) (e : Σ;;; Γ |-i A1 = A2 : sSort s),
        P1 Γ A1 A2 (sSort s) e ->
        forall e0 : Σ;;; Γ |-i B1 = B2 : sSort s,
        P1 Γ B1 B2 (sSort s) e0 ->
        forall e1 : Σ;;; Γ |-i p1 = p2 : sEq (sSort s) A1 B1,
        P1 Γ p1 p2 (sEq (sSort s) A1 B1) e1 ->
        forall e2 : Σ;;; Γ |-i t1 = t2 : A1,
        P1 Γ t1 t2 A1 e2 ->
        P1 Γ (sTransport A1 B1 p1 t1) (sTransport A2 B2 p2 t2) B1 (cong_Transport Σ Γ s A1 A2 B1 B2 p1 p2 t1 t2 e e0 e1 e2)) ->
       (forall (Γ : scontext) (A1 A2 a1 a2 B1 B2 b1 b2 : sterm) (s : sort) (e : Σ;;; Γ |-i A1 = A2 : sSort s),
        P1 Γ A1 A2 (sSort s) e ->
        forall e0 : Σ;;; Γ |-i B1 = B2 : sSort s,
        P1 Γ B1 B2 (sSort s) e0 ->
        forall e1 : Σ;;; Γ |-i a1 = a2 : A1,
        P1 Γ a1 a2 A1 e1 ->
        forall e2 : Σ;;; Γ |-i b1 = b2 : B1,
        P1 Γ b1 b2 B1 e2 ->
        P1 Γ (sHeq A1 a1 B1 b1) (sHeq A2 a2 B2 b2) (sSort (succ_sort s)) (cong_Heq Σ Γ A1 A2 a1 a2 B1 B2 b1 b2 s e e0 e1 e2)) ->
       (forall (Γ : scontext) (A1 B1 A2 B2 : sterm) (s : sort) (e : Σ;;; Γ |-i A1 = B1 : sSort s),
        P1 Γ A1 B1 (sSort s) e ->
        forall e0 : Σ;;; Γ |-i A2 = B2 : sSort s,
        P1 Γ A2 B2 (sSort s) e0 -> P1 Γ (sPack A1 A2) (sPack B1 B2) (sSort s) (cong_Pack Σ Γ A1 B1 A2 B2 s e e0)) ->
       (forall (Γ : scontext) (A u v p1 p2 : sterm) (s : sort) (e : Σ;;; Γ |-i p1 = p2 : sHeq A u A v),
        P1 Γ p1 p2 (sHeq A u A v) e ->
        forall t : Σ;;; Γ |-i A : sSort s,
        P Γ A (sSort s) t ->
        forall t0 : Σ;;; Γ |-i u : A,
        P Γ u A t0 ->
        forall t1 : Σ;;; Γ |-i v : A,
        P Γ v A t1 -> P1 Γ (sHeqToEq p1) (sHeqToEq p2) (sEq A u v) (cong_HeqToEq Σ Γ A u v p1 p2 s e t t0 t1)) ->
       (forall (Γ : scontext) (A1 A2 a1 a2 : sterm) (s : sort) (e : Σ;;; Γ |-i A1 = A2 : sSort s),
        P1 Γ A1 A2 (sSort s) e ->
        forall e0 : Σ;;; Γ |-i a1 = a2 : A1,
        P1 Γ a1 a2 A1 e0 -> P1 Γ (sHeqRefl A1 a1) (sHeqRefl A2 a2) (sHeq A1 a1 A1 a1) (cong_HeqRefl Σ Γ A1 A2 a1 a2 s e e0)) ->
       (forall (Γ : scontext) (A a B b p1 p2 : sterm) (s : sort) (t : Σ;;; Γ |-i A : sSort s),
        P Γ A (sSort s) t ->
        forall t0 : Σ;;; Γ |-i B : sSort s,
        P Γ B (sSort s) t0 ->
        forall t1 : Σ;;; Γ |-i a : A,
        P Γ a A t1 ->
        forall t2 : Σ;;; Γ |-i b : B,
        P Γ b B t2 ->
        forall e : Σ;;; Γ |-i p1 = p2 : sHeq A a B b,
        P1 Γ p1 p2 (sHeq A a B b) e -> P1 Γ (sHeqSym p1) (sHeqSym p2) (sHeq B b A a) (cong_HeqSym Σ Γ A a B b p1 p2 s t t0 t1 t2 e)) ->
       (forall (Γ : scontext) (A a B b C c p1 p2 q1 q2 : sterm) (s : sort) (t : Σ;;; Γ |-i A : sSort s),
        P Γ A (sSort s) t ->
        forall t0 : Σ;;; Γ |-i B : sSort s,
        P Γ B (sSort s) t0 ->
        forall t1 : Σ;;; Γ |-i C : sSort s,
        P Γ C (sSort s) t1 ->
        forall t2 : Σ;;; Γ |-i a : A,
        P Γ a A t2 ->
        forall t3 : Σ;;; Γ |-i b : B,
        P Γ b B t3 ->
        forall t4 : Σ;;; Γ |-i c : C,
        P Γ c C t4 ->
        forall e : Σ;;; Γ |-i p1 = p2 : sHeq A a B b,
        P1 Γ p1 p2 (sHeq A a B b) e ->
        forall e0 : Σ;;; Γ |-i q1 = q2 : sHeq B b C c,
        P1 Γ q1 q2 (sHeq B b C c) e0 ->
        P1 Γ (sHeqTrans p1 q1) (sHeqTrans p2 q2) (sHeq A a C c) (cong_HeqTrans Σ Γ A a B b C c p1 p2 q1 q2 s t t0 t1 t2 t3 t4 e e0)) ->
       (forall (Γ : scontext) (A B p1 p2 t1 t2 : sterm) (s : sort) (t : Σ;;; Γ |-i A : sSort s),
        P Γ A (sSort s) t ->
        forall t0 : Σ;;; Γ |-i B : sSort s,
        P Γ B (sSort s) t0 ->
        forall e : Σ;;; Γ |-i t1 = t2 : A,
        P1 Γ t1 t2 A e ->
        forall e0 : Σ;;; Γ |-i p1 = p2 : sEq (sSort s) A B,
        P1 Γ p1 p2 (sEq (sSort s) A B) e0 ->
        P1 Γ (sHeqTransport p1 t1) (sHeqTransport p2 t2) (sHeq A t1 B (sTransport A B p1 t1))
          (cong_HeqTransport Σ Γ A B p1 p2 t1 t2 s t t0 e e0)) ->
       (forall (Γ : scontext) (s z : sort) (nx ny np : name) (A1 A2 B1 B2 pA pB B1' B2' pA' pB' : sterm)
          (e : Σ;;; Γ |-i pA = pA' : sHeq (sSort s) A1 (sSort s) A2),
        P1 Γ pA pA' (sHeq (sSort s) A1 (sSort s) A2) e ->
        forall
          e0 : Σ;;; Γ,, svass np (sPack A1 A2) |-i pB = pB'
               : sHeq (sSort z) ((lift 1 1 B1) {0 := sProjT1 (sRel 0)}) (sSort z) ((lift 1 1 B2) {0 := sProjT2 (sRel 0)}),
        P1 (Γ,, svass np (sPack A1 A2)) pB pB'
          (sHeq (sSort z) ((lift 1 1 B1) {0 := sProjT1 (sRel 0)}) (sSort z) ((lift 1 1 B2) {0 := sProjT2 (sRel 0)})) e0 ->
        forall t : Σ;;; Γ |-i A1 : sSort s,
        P Γ A1 (sSort s) t ->
        forall t0 : Σ;;; Γ |-i A2 : sSort s,
        P Γ A2 (sSort s) t0 ->
        forall e1 : Σ;;; Γ,, svass nx A1 |-i B1 = B1' : sSort z,
        P1 (Γ,, svass nx A1) B1 B1' (sSort z) e1 ->
        forall e2 : Σ;;; Γ,, svass ny A2 |-i B2 = B2' : sSort z,
        P1 (Γ,, svass ny A2) B2 B2' (sSort z) e2 ->
        P1 Γ (sCongProd B1 B2 pA pB) (sCongProd B1' B2' pA' pB')
          (sHeq (sSort (max_sort s z)) (sProd nx A1 B1) (sSort (max_sort s z)) (sProd ny A2 B2))
          (cong_CongProd Σ Γ s z nx ny np A1 A2 B1 B2 pA pB B1' B2' pA' pB' e e0 t t0 e1 e2)) ->
       (forall (Γ : scontext) (s z : sort) (nx ny np : name) (A1 A2 B1 B2 t1 t2 pA pB pt B1' B2' t1' t2' pA' pB' pt' : sterm)
          (e : Σ;;; Γ |-i pA = pA' : sHeq (sSort s) A1 (sSort s) A2),
        P1 Γ pA pA' (sHeq (sSort s) A1 (sSort s) A2) e ->
        forall
          e0 : Σ;;; Γ,, svass np (sPack A1 A2) |-i pB = pB'
               : sHeq (sSort z) ((lift 1 1 B1) {0 := sProjT1 (sRel 0)}) (sSort z) ((lift 1 1 B2) {0 := sProjT2 (sRel 0)}),
        P1 (Γ,, svass np (sPack A1 A2)) pB pB'
          (sHeq (sSort z) ((lift 1 1 B1) {0 := sProjT1 (sRel 0)}) (sSort z) ((lift 1 1 B2) {0 := sProjT2 (sRel 0)})) e0 ->
        forall
          e1 : Σ;;; Γ,, svass np (sPack A1 A2) |-i pt = pt'
               : sHeq ((lift 1 1 B1) {0 := sProjT1 (sRel 0)}) ((lift 1 1 t1) {0 := sProjT1 (sRel 0)})
                   ((lift 1 1 B2) {0 := sProjT2 (sRel 0)}) ((lift 1 1 t2) {0 := sProjT2 (sRel 0)}),
        P1 (Γ,, svass np (sPack A1 A2)) pt pt'
          (sHeq ((lift 1 1 B1) {0 := sProjT1 (sRel 0)}) ((lift 1 1 t1) {0 := sProjT1 (sRel 0)})
             ((lift 1 1 B2) {0 := sProjT2 (sRel 0)}) ((lift 1 1 t2) {0 := sProjT2 (sRel 0)})) e1 ->
        forall t : Σ;;; Γ |-i A1 : sSort s,
        P Γ A1 (sSort s) t ->
        forall t0 : Σ;;; Γ |-i A2 : sSort s,
        P Γ A2 (sSort s) t0 ->
        forall e2 : Σ;;; Γ,, svass nx A1 |-i B1 = B1' : sSort z,
        P1 (Γ,, svass nx A1) B1 B1' (sSort z) e2 ->
        forall e3 : Σ;;; Γ,, svass ny A2 |-i B2 = B2' : sSort z,
        P1 (Γ,, svass ny A2) B2 B2' (sSort z) e3 ->
        forall e4 : Σ;;; Γ,, svass nx A1 |-i t1 = t1' : B1,
        P1 (Γ,, svass nx A1) t1 t1' B1 e4 ->
        forall e5 : Σ;;; Γ,, svass ny A2 |-i t2 = t2' : B2,
        P1 (Γ,, svass ny A2) t2 t2' B2 e5 ->
        P1 Γ (sCongLambda B1 B2 t1 t2 pA pB pt) (sCongLambda B1' B2' t1' t2' pA' pB' pt')
          (sHeq (sProd nx A1 B1) (sLambda nx A1 B1 t1) (sProd ny A2 B2) (sLambda ny A2 B2 t2))
          (cong_CongLambda Σ Γ s z nx ny np A1 A2 B1 B2 t1 t2 pA pB pt B1' B2' t1' t2' pA' pB' pt' e e0 e1 t t0 e2 e3 e4 e5)) ->
       (forall (Γ : scontext) (s z : sort) (nx ny np : name) (A1 A2 B1 B2 u1 u2 v1 v2 pA pB pu pv B1' B2' pu' pA' pB' pv' : sterm)
          (e : Σ;;; Γ |-i pA = pA' : sHeq (sSort s) A1 (sSort s) A2),
        P1 Γ pA pA' (sHeq (sSort s) A1 (sSort s) A2) e ->
        forall
          e0 : Σ;;; Γ,, svass np (sPack A1 A2) |-i pB = pB'
               : sHeq (sSort z) ((lift 1 1 B1) {0 := sProjT1 (sRel 0)}) (sSort z) ((lift 1 1 B2) {0 := sProjT2 (sRel 0)}),
        P1 (Γ,, svass np (sPack A1 A2)) pB pB'
          (sHeq (sSort z) ((lift 1 1 B1) {0 := sProjT1 (sRel 0)}) (sSort z) ((lift 1 1 B2) {0 := sProjT2 (sRel 0)})) e0 ->
        forall e1 : Σ;;; Γ |-i pu = pu' : sHeq (sProd nx A1 B1) u1 (sProd ny A2 B2) u2,
        P1 Γ pu pu' (sHeq (sProd nx A1 B1) u1 (sProd ny A2 B2) u2) e1 ->
        forall e2 : Σ;;; Γ |-i pv = pv' : sHeq A1 v1 A2 v2,
        P1 Γ pv pv' (sHeq A1 v1 A2 v2) e2 ->
        forall t : Σ;;; Γ |-i A1 : sSort s,
        P Γ A1 (sSort s) t ->
        forall t0 : Σ;;; Γ |-i A2 : sSort s,
        P Γ A2 (sSort s) t0 ->
        forall e3 : Σ;;; Γ,, svass nx A1 |-i B1 = B1' : sSort z,
        P1 (Γ,, svass nx A1) B1 B1' (sSort z) e3 ->
        forall e4 : Σ;;; Γ,, svass ny A2 |-i B2 = B2' : sSort z,
        P1 (Γ,, svass ny A2) B2 B2' (sSort z) e4 ->
        forall t1 : Σ;;; Γ |-i u1 : sProd nx A1 B1,
        P Γ u1 (sProd nx A1 B1) t1 ->
        forall t2 : Σ;;; Γ |-i u2 : sProd ny A2 B2,
        P Γ u2 (sProd ny A2 B2) t2 ->
        forall t3 : Σ;;; Γ |-i v1 : A1,
        P Γ v1 A1 t3 ->
        forall t4 : Σ;;; Γ |-i v2 : A2,
        P Γ v2 A2 t4 ->
        P1 Γ (sCongApp B1 B2 pu pA pB pv) (sCongApp B1' B2' pu' pA' pB' pv')
          (sHeq (B1 {0 := v1}) (sApp u1 nx A1 B1 v1) (B2 {0 := v2}) (sApp u2 ny A2 B2 v2))
          (cong_CongApp Σ Γ s z nx ny np A1 A2 B1 B2 u1 u2 v1 v2 pA pB pu pv B1' B2' pu' pA' pB' pv' e e0 e1 e2 t t0 e3 e4 t1 t2 t3
             t4)) ->
       (forall (Γ : scontext) (s : sort) (A1 A2 u1 u2 v1 v2 pA pu pv pA' pu' pv' : sterm)
          (e : Σ;;; Γ |-i pA = pA' : sHeq (sSort s) A1 (sSort s) A2),
        P1 Γ pA pA' (sHeq (sSort s) A1 (sSort s) A2) e ->
        forall e0 : Σ;;; Γ |-i pu = pu' : sHeq A1 u1 A2 u2,
        P1 Γ pu pu' (sHeq A1 u1 A2 u2) e0 ->
        forall e1 : Σ;;; Γ |-i pv = pv' : sHeq A1 v1 A2 v2,
        P1 Γ pv pv' (sHeq A1 v1 A2 v2) e1 ->
        forall t : Σ;;; Γ |-i A1 : sSort s,
        P Γ A1 (sSort s) t ->
        forall t0 : Σ;;; Γ |-i A2 : sSort s,
        P Γ A2 (sSort s) t0 ->
        forall t1 : Σ;;; Γ |-i u1 : A1,
        P Γ u1 A1 t1 ->
        forall t2 : Σ;;; Γ |-i u2 : A2,
        P Γ u2 A2 t2 ->
        forall t3 : Σ;;; Γ |-i v1 : A1,
        P Γ v1 A1 t3 ->
        forall t4 : Σ;;; Γ |-i v2 : A2,
        P Γ v2 A2 t4 ->
        P1 Γ (sCongEq pA pu pv) (sCongEq pA' pu' pv') (sHeq (sSort s) (sEq A1 u1 v1) (sSort s) (sEq A2 u2 v2))
          (cong_CongEq Σ Γ s A1 A2 u1 u2 v1 v2 pA pu pv pA' pu' pv' e e0 e1 t t0 t1 t2 t3 t4)) ->
       (forall (Γ : scontext) (s : sort) (A1 A2 u1 u2 pA pu pA' pu' : sterm)
          (e : Σ;;; Γ |-i pA = pA' : sHeq (sSort s) A1 (sSort s) A2),
        P1 Γ pA pA' (sHeq (sSort s) A1 (sSort s) A2) e ->
        forall e0 : Σ;;; Γ |-i pu = pu' : sHeq A1 u1 A2 u2,
        P1 Γ pu pu' (sHeq A1 u1 A2 u2) e0 ->
        forall t : Σ;;; Γ |-i A1 : sSort s,
        P Γ A1 (sSort s) t ->
        forall t0 : Σ;;; Γ |-i A2 : sSort s,
        P Γ A2 (sSort s) t0 ->
        forall t1 : Σ;;; Γ |-i u1 : A1,
        P Γ u1 A1 t1 ->
        forall t2 : Σ;;; Γ |-i u2 : A2,
        P Γ u2 A2 t2 ->
        P1 Γ (sCongRefl pA pu) (sCongRefl pA' pu') (sHeq (sEq A1 u1 u1) (sRefl A1 u1) (sEq A2 u2 u2) (sRefl A2 u2))
          (cong_CongRefl Σ Γ s A1 A2 u1 u2 pA pu pA' pu' e e0 t t0 t1 t2)) ->
       (forall (Γ : scontext) (A u v p1 p2 : sterm) (s : sort) (e : Σ;;; Γ |-i p1 = p2 : sEq A u v),
        P1 Γ p1 p2 (sEq A u v) e ->
        forall t : Σ;;; Γ |-i A : sSort s,
        P Γ A (sSort s) t ->
        forall t0 : Σ;;; Γ |-i u : A,
        P Γ u A t0 ->
        forall t1 : Σ;;; Γ |-i v : A,
        P Γ v A t1 -> P1 Γ (sEqToHeq p1) (sEqToHeq p2) (sHeq A u A v) (cong_EqToHeq Σ Γ A u v p1 p2 s e t t0 t1)) ->
       (forall (Γ : scontext) (A u B v p1 p2 : sterm) (s : sort) (e : Σ;;; Γ |-i p1 = p2 : sHeq A u B v),
        P1 Γ p1 p2 (sHeq A u B v) e ->
        forall t : Σ;;; Γ |-i A : sSort s,
        P Γ A (sSort s) t ->
        forall t0 : Σ;;; Γ |-i B : sSort s,
        P Γ B (sSort s) t0 ->
        forall t1 : Σ;;; Γ |-i u : A,
        P Γ u A t1 ->
        forall t2 : Σ;;; Γ |-i v : B,
        P Γ v B t2 -> P1 Γ (sHeqTypeEq p1) (sHeqTypeEq p2) (sEq (sSort s) A B) (cong_HeqTypeEq Σ Γ A u B v p1 p2 s e t t0 t1 t2)) ->
       (forall (Γ : scontext) (A1 A2 p1 p2 : sterm) (s : sort) (t : Σ;;; Γ |-i A1 : sSort s),
        P Γ A1 (sSort s) t ->
        forall t0 : Σ;;; Γ |-i A2 : sSort s,
        P Γ A2 (sSort s) t0 ->
        forall e : Σ;;; Γ |-i p1 = p2 : sPack A1 A2,
        P1 Γ p1 p2 (sPack A1 A2) e -> P1 Γ (sProjT1 p1) (sProjT1 p2) A1 (cong_ProjT1 Σ Γ A1 A2 p1 p2 s t t0 e)) ->
       (forall (Γ : scontext) (A1 A2 p1 p2 : sterm) (s : sort) (t : Σ;;; Γ |-i A1 : sSort s),
        P Γ A1 (sSort s) t ->
        forall t0 : Σ;;; Γ |-i A2 : sSort s,
        P Γ A2 (sSort s) t0 ->
        forall e : Σ;;; Γ |-i p1 = p2 : sPack A1 A2,
        P1 Γ p1 p2 (sPack A1 A2) e -> P1 Γ (sProjT2 p1) (sProjT2 p2) A2 (cong_ProjT2 Σ Γ A1 A2 p1 p2 s t t0 e)) ->
       (forall (Γ : scontext) (A1 A2 p1 p2 : sterm) (s : sort) (t : Σ;;; Γ |-i A1 : sSort s),
        P Γ A1 (sSort s) t ->
        forall t0 : Σ;;; Γ |-i A2 : sSort s,
        P Γ A2 (sSort s) t0 ->
        forall e : Σ;;; Γ |-i p1 = p2 : sPack A1 A2,
        P1 Γ p1 p2 (sPack A1 A2) e ->
        P1 Γ (sProjTe p1) (sProjTe p2) (sHeq A1 (sProjT1 p1) A2 (sProjT2 p1)) (cong_ProjTe Σ Γ A1 A2 p1 p2 s t t0 e)) ->
       (forall (Γ : scontext) (s : sort) (A u : sterm) (t : Σ;;; Γ |-i A : sSort s),
        P Γ A (sSort s) t ->
        forall t0 : Σ;;; Γ |-i u : A,
        P Γ u A t0 -> P1 Γ (sHeqToEq (sHeqRefl A u)) (sRefl A u) (sEq A u u) (eq_HeqToEqRefl Σ Γ s A u t t0)) ->
       (forall (Γ : scontext) (n : nat) (w : wf Σ Γ),
        P0 Γ w ->
        forall isdecl : n < #|Γ|,
        P Γ (sRel n) (lift0 (S n) (sdecl_type (safe_nth Γ (exist (fun n0 : nat => n0 < #|Γ|) n isdecl)))) (type_Rel Σ Γ n w isdecl)) ->
       (forall (Γ : scontext) (s : sort) (w : wf Σ Γ), P0 Γ w -> P Γ (sSort s) (sSort (succ_sort s)) (type_Sort Σ Γ s w)) ->
       (forall (Γ : scontext) (n : name) (t b : sterm) (s1 s2 : sort) (t0 : Σ;;; Γ |-i t : sSort s1),
        P Γ t (sSort s1) t0 ->
        forall t1 : Σ;;; Γ,, svass n t |-i b : sSort s2,
        P (Γ,, svass n t) b (sSort s2) t1 -> P Γ (sProd n t b) (sSort (max_sort s1 s2)) (type_Prod Σ Γ n t b s1 s2 t0 t1)) ->
       (forall (Γ : scontext) (n n' : name) (t b : sterm) (s1 s2 : sort) (bty : sterm) (t0 : Σ;;; Γ |-i t : sSort s1),
        P Γ t (sSort s1) t0 ->
        forall t1 : Σ;;; Γ,, svass n t |-i bty : sSort s2,
        P (Γ,, svass n t) bty (sSort s2) t1 ->
        forall t2 : Σ;;; Γ,, svass n t |-i b : bty,
        P (Γ,, svass n t) b bty t2 -> P Γ (sLambda n t bty b) (sProd n' t bty) (type_Lambda Σ Γ n n' t b s1 s2 bty t0 t1 t2)) ->
       (forall (Γ : scontext) (n : name) (s1 s2 : sort) (t A B u : sterm) (t0 : Σ;;; Γ |-i A : sSort s1),
        P Γ A (sSort s1) t0 ->
        forall t1 : Σ;;; Γ,, svass n A |-i B : sSort s2,
        P (Γ,, svass n A) B (sSort s2) t1 ->
        forall t2 : Σ;;; Γ |-i t : sProd n A B,
        P Γ t (sProd n A B) t2 ->
        forall t3 : Σ;;; Γ |-i u : A, P Γ u A t3 -> P Γ (sApp t n A B u) (B {0 := u}) (type_App Σ Γ n s1 s2 t A B u t0 t1 t2 t3)) ->
       (forall (Γ : scontext) (s : sort) (A u v : sterm) (t : Σ;;; Γ |-i A : sSort s),
        P Γ A (sSort s) t ->
        forall t0 : Σ;;; Γ |-i u : A,
        P Γ u A t0 -> forall t1 : Σ;;; Γ |-i v : A, P Γ v A t1 -> P Γ (sEq A u v) (sSort s) (type_Eq Σ Γ s A u v t t0 t1)) ->
       (forall (Γ : scontext) (s : sort) (A u : sterm) (t : Σ;;; Γ |-i A : sSort s),
        P Γ A (sSort s) t -> forall t0 : Σ;;; Γ |-i u : A, P Γ u A t0 -> P Γ (sRefl A u) (sEq A u u) (type_Refl Σ Γ s A u t t0)) ->
       (forall (Γ : scontext) (nx ne : name) (s1 s2 : sort) (A u v P2 p w : sterm) (t : Σ;;; Γ |-i A : sSort s1),
        P Γ A (sSort s1) t ->
        forall t0 : Σ;;; Γ |-i u : A,
        P Γ u A t0 ->
        forall t1 : Σ;;; Γ |-i v : A,
        P Γ v A t1 ->
        forall t2 : Σ;;; (Γ,, svass nx A),, svass ne (sEq (lift0 1 A) (lift0 1 u) (sRel 0)) |-i P2 : sSort s2,
        P ((Γ,, svass nx A),, svass ne (sEq (lift0 1 A) (lift0 1 u) (sRel 0))) P2 (sSort s2) t2 ->
        forall t3 : Σ;;; Γ |-i p : sEq A u v,
        P Γ p (sEq A u v) t3 ->
        forall t4 : Σ;;; Γ |-i w : (P2 {1 := u}) {0 := sRefl A u},
        P Γ w ((P2 {1 := u}) {0 := sRefl A u}) t4 ->
        P Γ (sJ A u P2 w v p) ((P2 {1 := v}) {0 := p}) (type_J Σ Γ nx ne s1 s2 A u v P2 p w t t0 t1 t2 t3 t4)) ->
       (forall (Γ : scontext) (s : sort) (T1 T2 p t : sterm) (t0 : Σ;;; Γ |-i T1 : sSort s),
        P Γ T1 (sSort s) t0 ->
        forall t1 : Σ;;; Γ |-i T2 : sSort s,
        P Γ T2 (sSort s) t1 ->
        forall t2 : Σ;;; Γ |-i p : sEq (sSort s) T1 T2,
        P Γ p (sEq (sSort s) T1 T2) t2 ->
        forall t3 : Σ;;; Γ |-i t : T1, P Γ t T1 t3 -> P Γ (sTransport T1 T2 p t) T2 (type_Transport Σ Γ s T1 T2 p t t0 t1 t2 t3)) ->
       (forall (Γ : scontext) (A a B b : sterm) (s : sort) (t : Σ;;; Γ |-i A : sSort s),
        P Γ A (sSort s) t ->
        forall t0 : Σ;;; Γ |-i B : sSort s,
        P Γ B (sSort s) t0 ->
        forall t1 : Σ;;; Γ |-i a : A,
        P Γ a A t1 ->
        forall t2 : Σ;;; Γ |-i b : B, P Γ b B t2 -> P Γ (sHeq A a B b) (sSort (succ_sort s)) (type_Heq Σ Γ A a B b s t t0 t1 t2)) ->
       (forall (Γ : scontext) (A u v p : sterm) (s : sort) (t : Σ;;; Γ |-i p : sHeq A u A v),
        P Γ p (sHeq A u A v) t ->
        forall t0 : Σ;;; Γ |-i A : sSort s,
        P Γ A (sSort s) t0 ->
        forall t1 : Σ;;; Γ |-i u : A,
        P Γ u A t1 ->
        forall t2 : Σ;;; Γ |-i v : A, P Γ v A t2 -> P Γ (sHeqToEq p) (sEq A u v) (type_HeqToEq Σ Γ A u v p s t t0 t1 t2)) ->
       (forall (Γ : scontext) (A a : sterm) (s : sort) (t : Σ;;; Γ |-i A : sSort s),
        P Γ A (sSort s) t ->
        forall t0 : Σ;;; Γ |-i a : A, P Γ a A t0 -> P Γ (sHeqRefl A a) (sHeq A a A a) (type_HeqRefl Σ Γ A a s t t0)) ->
       (forall (Γ : scontext) (A a B b p : sterm) (s : sort) (t : Σ;;; Γ |-i A : sSort s),
        P Γ A (sSort s) t ->
        forall t0 : Σ;;; Γ |-i B : sSort s,
        P Γ B (sSort s) t0 ->
        forall t1 : Σ;;; Γ |-i a : A,
        P Γ a A t1 ->
        forall t2 : Σ;;; Γ |-i b : B,
        P Γ b B t2 ->
        forall t3 : Σ;;; Γ |-i p : sHeq A a B b,
        P Γ p (sHeq A a B b) t3 -> P Γ (sHeqSym p) (sHeq B b A a) (type_HeqSym Σ Γ A a B b p s t t0 t1 t2 t3)) ->
       (forall (Γ : scontext) (A a B b C c p q : sterm) (s : sort) (t : Σ;;; Γ |-i A : sSort s),
        P Γ A (sSort s) t ->
        forall t0 : Σ;;; Γ |-i B : sSort s,
        P Γ B (sSort s) t0 ->
        forall t1 : Σ;;; Γ |-i C : sSort s,
        P Γ C (sSort s) t1 ->
        forall t2 : Σ;;; Γ |-i a : A,
        P Γ a A t2 ->
        forall t3 : Σ;;; Γ |-i b : B,
        P Γ b B t3 ->
        forall t4 : Σ;;; Γ |-i c : C,
        P Γ c C t4 ->
        forall t5 : Σ;;; Γ |-i p : sHeq A a B b,
        P Γ p (sHeq A a B b) t5 ->
        forall t6 : Σ;;; Γ |-i q : sHeq B b C c,
        P Γ q (sHeq B b C c) t6 -> P Γ (sHeqTrans p q) (sHeq A a C c) (type_HeqTrans Σ Γ A a B b C c p q s t t0 t1 t2 t3 t4 t5 t6)) ->
       (forall (Γ : scontext) (A B p t : sterm) (s : sort) (t0 : Σ;;; Γ |-i A : sSort s),
        P Γ A (sSort s) t0 ->
        forall t1 : Σ;;; Γ |-i B : sSort s,
        P Γ B (sSort s) t1 ->
        forall t2 : Σ;;; Γ |-i t : A,
        P Γ t A t2 ->
        forall t3 : Σ;;; Γ |-i p : sEq (sSort s) A B,
        P Γ p (sEq (sSort s) A B) t3 ->
        P Γ (sHeqTransport p t) (sHeq A t B (sTransport A B p t)) (type_HeqTransport Σ Γ A B p t s t0 t1 t2 t3)) ->
       (forall (Γ : scontext) (s z : sort) (nx ny np : name) (A1 A2 B1 B2 pA pB : sterm)
          (t : Σ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2),
        P Γ pA (sHeq (sSort s) A1 (sSort s) A2) t ->
        forall
          t0 : Σ;;; Γ,, svass np (sPack A1 A2) |-i pB
               : sHeq (sSort z) ((lift 1 1 B1) {0 := sProjT1 (sRel 0)}) (sSort z) ((lift 1 1 B2) {0 := sProjT2 (sRel 0)}),
        P (Γ,, svass np (sPack A1 A2)) pB
          (sHeq (sSort z) ((lift 1 1 B1) {0 := sProjT1 (sRel 0)}) (sSort z) ((lift 1 1 B2) {0 := sProjT2 (sRel 0)})) t0 ->
        forall t1 : Σ;;; Γ |-i A1 : sSort s,
        P Γ A1 (sSort s) t1 ->
        forall t2 : Σ;;; Γ |-i A2 : sSort s,
        P Γ A2 (sSort s) t2 ->
        forall t3 : Σ;;; Γ,, svass nx A1 |-i B1 : sSort z,
        P (Γ,, svass nx A1) B1 (sSort z) t3 ->
        forall t4 : Σ;;; Γ,, svass ny A2 |-i B2 : sSort z,
        P (Γ,, svass ny A2) B2 (sSort z) t4 ->
        P Γ (sCongProd B1 B2 pA pB) (sHeq (sSort (max_sort s z)) (sProd nx A1 B1) (sSort (max_sort s z)) (sProd ny A2 B2))
          (type_CongProd Σ Γ s z nx ny np A1 A2 B1 B2 pA pB t t0 t1 t2 t3 t4)) ->
       (forall (Γ : scontext) (s z : sort) (nx ny np : name) (A1 A2 B1 B2 t1 t2 pA pB pt : sterm)
          (t : Σ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2),
        P Γ pA (sHeq (sSort s) A1 (sSort s) A2) t ->
        forall
          t0 : Σ;;; Γ,, svass np (sPack A1 A2) |-i pB
               : sHeq (sSort z) ((lift 1 1 B1) {0 := sProjT1 (sRel 0)}) (sSort z) ((lift 1 1 B2) {0 := sProjT2 (sRel 0)}),
        P (Γ,, svass np (sPack A1 A2)) pB
          (sHeq (sSort z) ((lift 1 1 B1) {0 := sProjT1 (sRel 0)}) (sSort z) ((lift 1 1 B2) {0 := sProjT2 (sRel 0)})) t0 ->
        forall
          t3 : Σ;;; Γ,, svass np (sPack A1 A2) |-i pt
               : sHeq ((lift 1 1 B1) {0 := sProjT1 (sRel 0)}) ((lift 1 1 t1) {0 := sProjT1 (sRel 0)})
                   ((lift 1 1 B2) {0 := sProjT2 (sRel 0)}) ((lift 1 1 t2) {0 := sProjT2 (sRel 0)}),
        P (Γ,, svass np (sPack A1 A2)) pt
          (sHeq ((lift 1 1 B1) {0 := sProjT1 (sRel 0)}) ((lift 1 1 t1) {0 := sProjT1 (sRel 0)})
             ((lift 1 1 B2) {0 := sProjT2 (sRel 0)}) ((lift 1 1 t2) {0 := sProjT2 (sRel 0)})) t3 ->
        forall t4 : Σ;;; Γ |-i A1 : sSort s,
        P Γ A1 (sSort s) t4 ->
        forall t5 : Σ;;; Γ |-i A2 : sSort s,
        P Γ A2 (sSort s) t5 ->
        forall t6 : Σ;;; Γ,, svass nx A1 |-i B1 : sSort z,
        P (Γ,, svass nx A1) B1 (sSort z) t6 ->
        forall t7 : Σ;;; Γ,, svass ny A2 |-i B2 : sSort z,
        P (Γ,, svass ny A2) B2 (sSort z) t7 ->
        forall t8 : Σ;;; Γ,, svass nx A1 |-i t1 : B1,
        P (Γ,, svass nx A1) t1 B1 t8 ->
        forall t9 : Σ;;; Γ,, svass ny A2 |-i t2 : B2,
        P (Γ,, svass ny A2) t2 B2 t9 ->
        P Γ (sCongLambda B1 B2 t1 t2 pA pB pt) (sHeq (sProd nx A1 B1) (sLambda nx A1 B1 t1) (sProd ny A2 B2) (sLambda ny A2 B2 t2))
          (type_CongLambda Σ Γ s z nx ny np A1 A2 B1 B2 t1 t2 pA pB pt t t0 t3 t4 t5 t6 t7 t8 t9)) ->
       (forall (Γ : scontext) (s z : sort) (nx ny np : name) (A1 A2 B1 B2 u1 u2 v1 v2 pA pB pu pv : sterm)
          (t : Σ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2),
        P Γ pA (sHeq (sSort s) A1 (sSort s) A2) t ->
        forall
          t0 : Σ;;; Γ,, svass np (sPack A1 A2) |-i pB
               : sHeq (sSort z) ((lift 1 1 B1) {0 := sProjT1 (sRel 0)}) (sSort z) ((lift 1 1 B2) {0 := sProjT2 (sRel 0)}),
        P (Γ,, svass np (sPack A1 A2)) pB
          (sHeq (sSort z) ((lift 1 1 B1) {0 := sProjT1 (sRel 0)}) (sSort z) ((lift 1 1 B2) {0 := sProjT2 (sRel 0)})) t0 ->
        forall t1 : Σ;;; Γ |-i pu : sHeq (sProd nx A1 B1) u1 (sProd ny A2 B2) u2,
        P Γ pu (sHeq (sProd nx A1 B1) u1 (sProd ny A2 B2) u2) t1 ->
        forall t2 : Σ;;; Γ |-i pv : sHeq A1 v1 A2 v2,
        P Γ pv (sHeq A1 v1 A2 v2) t2 ->
        forall t3 : Σ;;; Γ |-i A1 : sSort s,
        P Γ A1 (sSort s) t3 ->
        forall t4 : Σ;;; Γ |-i A2 : sSort s,
        P Γ A2 (sSort s) t4 ->
        forall t5 : Σ;;; Γ,, svass nx A1 |-i B1 : sSort z,
        P (Γ,, svass nx A1) B1 (sSort z) t5 ->
        forall t6 : Σ;;; Γ,, svass ny A2 |-i B2 : sSort z,
        P (Γ,, svass ny A2) B2 (sSort z) t6 ->
        forall t7 : Σ;;; Γ |-i u1 : sProd nx A1 B1,
        P Γ u1 (sProd nx A1 B1) t7 ->
        forall t8 : Σ;;; Γ |-i u2 : sProd ny A2 B2,
        P Γ u2 (sProd ny A2 B2) t8 ->
        forall t9 : Σ;;; Γ |-i v1 : A1,
        P Γ v1 A1 t9 ->
        forall t10 : Σ;;; Γ |-i v2 : A2,
        P Γ v2 A2 t10 ->
        P Γ (sCongApp B1 B2 pu pA pB pv) (sHeq (B1 {0 := v1}) (sApp u1 nx A1 B1 v1) (B2 {0 := v2}) (sApp u2 ny A2 B2 v2))
          (type_CongApp Σ Γ s z nx ny np A1 A2 B1 B2 u1 u2 v1 v2 pA pB pu pv t t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10)) ->
       (forall (Γ : scontext) (s : sort) (A1 A2 u1 u2 v1 v2 pA pu pv : sterm) (t : Σ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2),
        P Γ pA (sHeq (sSort s) A1 (sSort s) A2) t ->
        forall t0 : Σ;;; Γ |-i pu : sHeq A1 u1 A2 u2,
        P Γ pu (sHeq A1 u1 A2 u2) t0 ->
        forall t1 : Σ;;; Γ |-i pv : sHeq A1 v1 A2 v2,
        P Γ pv (sHeq A1 v1 A2 v2) t1 ->
        forall t2 : Σ;;; Γ |-i A1 : sSort s,
        P Γ A1 (sSort s) t2 ->
        forall t3 : Σ;;; Γ |-i A2 : sSort s,
        P Γ A2 (sSort s) t3 ->
        forall t4 : Σ;;; Γ |-i u1 : A1,
        P Γ u1 A1 t4 ->
        forall t5 : Σ;;; Γ |-i u2 : A2,
        P Γ u2 A2 t5 ->
        forall t6 : Σ;;; Γ |-i v1 : A1,
        P Γ v1 A1 t6 ->
        forall t7 : Σ;;; Γ |-i v2 : A2,
        P Γ v2 A2 t7 ->
        P Γ (sCongEq pA pu pv) (sHeq (sSort s) (sEq A1 u1 v1) (sSort s) (sEq A2 u2 v2))
          (type_CongEq Σ Γ s A1 A2 u1 u2 v1 v2 pA pu pv t t0 t1 t2 t3 t4 t5 t6 t7)) ->
       (forall (Γ : scontext) (s : sort) (A1 A2 u1 u2 pA pu : sterm) (t : Σ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2),
        P Γ pA (sHeq (sSort s) A1 (sSort s) A2) t ->
        forall t0 : Σ;;; Γ |-i pu : sHeq A1 u1 A2 u2,
        P Γ pu (sHeq A1 u1 A2 u2) t0 ->
        forall t1 : Σ;;; Γ |-i A1 : sSort s,
        P Γ A1 (sSort s) t1 ->
        forall t2 : Σ;;; Γ |-i A2 : sSort s,
        P Γ A2 (sSort s) t2 ->
        forall t3 : Σ;;; Γ |-i u1 : A1,
        P Γ u1 A1 t3 ->
        forall t4 : Σ;;; Γ |-i u2 : A2,
        P Γ u2 A2 t4 ->
        P Γ (sCongRefl pA pu) (sHeq (sEq A1 u1 u1) (sRefl A1 u1) (sEq A2 u2 u2) (sRefl A2 u2))
          (type_CongRefl Σ Γ s A1 A2 u1 u2 pA pu t t0 t1 t2 t3 t4)) ->
       (forall (Γ : scontext) (A u v p : sterm) (s : sort) (t : Σ;;; Γ |-i p : sEq A u v),
        P Γ p (sEq A u v) t ->
        forall t0 : Σ;;; Γ |-i A : sSort s,
        P Γ A (sSort s) t0 ->
        forall t1 : Σ;;; Γ |-i u : A,
        P Γ u A t1 ->
        forall t2 : Σ;;; Γ |-i v : A, P Γ v A t2 -> P Γ (sEqToHeq p) (sHeq A u A v) (type_EqToHeq Σ Γ A u v p s t t0 t1 t2)) ->
       (forall (Γ : scontext) (A u B v p : sterm) (s : sort) (t : Σ;;; Γ |-i p : sHeq A u B v),
        P Γ p (sHeq A u B v) t ->
        forall t0 : Σ;;; Γ |-i A : sSort s,
        P Γ A (sSort s) t0 ->
        forall t1 : Σ;;; Γ |-i B : sSort s,
        P Γ B (sSort s) t1 ->
        forall t2 : Σ;;; Γ |-i u : A,
        P Γ u A t2 ->
        forall t3 : Σ;;; Γ |-i v : B,
        P Γ v B t3 -> P Γ (sHeqTypeEq p) (sEq (sSort s) A B) (type_HeqTypeEq Σ Γ A u B v p s t t0 t1 t2 t3)) ->
       (forall (Γ : scontext) (A1 A2 : sterm) (s : sort) (t : Σ;;; Γ |-i A1 : sSort s),
        P Γ A1 (sSort s) t ->
        forall t0 : Σ;;; Γ |-i A2 : sSort s, P Γ A2 (sSort s) t0 -> P Γ (sPack A1 A2) (sSort s) (type_Pack Σ Γ A1 A2 s t t0)) ->
       (forall (Γ : scontext) (A1 A2 p : sterm) (s : sort) (t : Σ;;; Γ |-i A1 : sSort s),
        P Γ A1 (sSort s) t ->
        forall t0 : Σ;;; Γ |-i A2 : sSort s,
        P Γ A2 (sSort s) t0 ->
        forall t1 : Σ;;; Γ |-i p : sPack A1 A2, P Γ p (sPack A1 A2) t1 -> P Γ (sProjT1 p) A1 (type_ProjT1 Σ Γ A1 A2 p s t t0 t1)) ->
       (forall (Γ : scontext) (A1 A2 p : sterm) (s : sort) (t : Σ;;; Γ |-i A1 : sSort s),
        P Γ A1 (sSort s) t ->
        forall t0 : Σ;;; Γ |-i A2 : sSort s,
        P Γ A2 (sSort s) t0 ->
        forall t1 : Σ;;; Γ |-i p : sPack A1 A2, P Γ p (sPack A1 A2) t1 -> P Γ (sProjT2 p) A2 (type_ProjT2 Σ Γ A1 A2 p s t t0 t1)) ->
       (forall (Γ : scontext) (A1 A2 p : sterm) (s : sort) (t : Σ;;; Γ |-i A1 : sSort s),
        P Γ A1 (sSort s) t ->
        forall t0 : Σ;;; Γ |-i A2 : sSort s,
        P Γ A2 (sSort s) t0 ->
        forall t1 : Σ;;; Γ |-i p : sPack A1 A2,
        P Γ p (sPack A1 A2) t1 -> P Γ (sProjTe p) (sHeq A1 (sProjT1 p) A2 (sProjT2 p)) (type_ProjTe Σ Γ A1 A2 p s t t0 t1)) ->
       (forall (Γ : scontext) (ind : inductive) (w : wf Σ Γ),
        P0 Γ w ->
        forall (univs : universe_context) (decl : sone_inductive_body) (isdecl : sdeclared_inductive (fst Σ) ind univs decl),
        P Γ (sInd ind) (sind_type decl) (type_Ind Σ Γ ind w univs decl isdecl)) ->
       (forall (Γ : scontext) (ind : inductive) (i : nat) (w : wf Σ Γ),
        P0 Γ w ->
        forall (univs : universe_context) (decl : ident * sterm * nat) (isdecl : sdeclared_constructor (fst Σ) (ind, i) univs decl),
        P Γ (sConstruct ind i) (stype_of_constructor (fst Σ) (ind, i) univs decl isdecl)
          (type_Construct Σ Γ ind i w univs decl isdecl)) ->
       (forall (Γ : scontext) (t A B : sterm) (s : sort) (t0 : Σ;;; Γ |-i t : A),
        P Γ t A t0 ->
        forall t1 : Σ;;; Γ |-i B : sSort s,
        P Γ B (sSort s) t1 ->
        forall e : Σ;;; Γ |-i A = B : sSort s, P1 Γ A B (sSort s) e -> P Γ t B (type_conv Σ Γ t A B s t0 t1 e)) ->
       P0 [] (wf_nil Σ) ->
       (forall (s : sort) (Γ : scontext) (x : name) (A : sterm) (w : wf Σ Γ),
        P0 Γ w -> forall t : Σ;;; Γ |-i A : sSort s, P Γ A (sSort s) t -> P0 (Γ,, svass x A) (wf_snoc Σ s Γ x A w t)) ->
       (forall (Γ : scontext) (u A : sterm) (t : Σ;;; Γ |-i u : A), P Γ u A t -> P1 Γ u u A (eq_reflexivity Σ Γ u A t)) ->
       (forall (Γ : scontext) (u v A : sterm) (e : Σ;;; Γ |-i u = v : A), P1 Γ u v A e -> P1 Γ v u A (eq_symmetry Σ Γ u v A e)) ->
       (forall (Γ : scontext) (u v w A : sterm) (e : Σ;;; Γ |-i u = v : A),
        P1 Γ u v A e -> forall e0 : Σ;;; Γ |-i v = w : A, P1 Γ v w A e0 -> P1 Γ u w A (eq_transitivity Σ Γ u v w A e e0)) ->
       (forall (Γ : scontext) (s1 s2 : sort) (n : name) (A B t u : sterm) (t0 : Σ;;; Γ |-i A : sSort s1),
        P Γ A (sSort s1) t0 ->
        forall t1 : Σ;;; Γ,, svass n A |-i B : sSort s2,
        P (Γ,, svass n A) B (sSort s2) t1 ->
        forall t2 : Σ;;; Γ,, svass n A |-i t : B,
        P (Γ,, svass n A) t B t2 ->
        forall t3 : Σ;;; Γ |-i u : A,
        P Γ u A t3 -> P1 Γ (sApp (sLambda n A B t) n A B u) (t {0 := u}) (B {0 := u}) (eq_beta Σ Γ s1 s2 n A B t u t0 t1 t2 t3)) ->
       (forall (Γ : scontext) (nx ne : name) (s1 s2 : sort) (A u P2 w : sterm) (t : Σ;;; Γ |-i A : sSort s1),
        P Γ A (sSort s1) t ->
        forall t0 : Σ;;; Γ |-i u : A,
        P Γ u A t0 ->
        forall t1 : Σ;;; (Γ,, svass nx A),, svass ne (sEq (lift0 1 A) (lift0 1 u) (sRel 0)) |-i P2 : sSort s2,
        P ((Γ,, svass nx A),, svass ne (sEq (lift0 1 A) (lift0 1 u) (sRel 0))) P2 (sSort s2) t1 ->
        forall t2 : Σ;;; Γ |-i w : (P2 {1 := u}) {0 := sRefl A u},
        P Γ w ((P2 {1 := u}) {0 := sRefl A u}) t2 ->
        P1 Γ (sJ A u P2 w u (sRefl A u)) w ((P2 {1 := u}) {0 := sRefl A u}) (eq_JRefl Σ Γ nx ne s1 s2 A u P2 w t t0 t1 t2)) ->
       (forall (Γ : scontext) (s : sort) (A t : sterm) (t0 : Σ;;; Γ |-i A : sSort s),
        P Γ A (sSort s) t0 ->
        forall t1 : Σ;;; Γ |-i t : A,
        P Γ t A t1 -> P1 Γ (sTransport A A (sRefl (sSort s) A) t) t A (eq_TransportRefl Σ Γ s A t t0 t1)) ->
       (forall (Γ : scontext) (s : sort) (T1 T2 t1 t2 : sterm) (e : Σ;;; Γ |-i t1 = t2 : T1),
        P1 Γ t1 t2 T1 e ->
        forall e0 : Σ;;; Γ |-i T1 = T2 : sSort s, P1 Γ T1 T2 (sSort s) e0 -> P1 Γ t1 t2 T2 (eq_conv Σ Γ s T1 T2 t1 t2 e e0)) ->
       (forall (Γ : scontext) (n1 n2 : name) (A1 A2 B1 B2 : sterm) (s1 s2 : sort) (e : Σ;;; Γ |-i A1 = A2 : sSort s1),
        P1 Γ A1 A2 (sSort s1) e ->
        forall e0 : Σ;;; Γ,, svass n1 A1 |-i B1 = B2 : sSort s2,
        P1 (Γ,, svass n1 A1) B1 B2 (sSort s2) e0 ->
        P1 Γ (sProd n1 A1 B1) (sProd n2 A2 B2) (sSort (max_sort s1 s2)) (cong_Prod Σ Γ n1 n2 A1 A2 B1 B2 s1 s2 e e0)) ->
       (forall (Γ : scontext) (n1 n2 n' : name) (A1 A2 B1 B2 t1 t2 : sterm) (s1 s2 : sort) (e : Σ;;; Γ |-i A1 = A2 : sSort s1),
        P1 Γ A1 A2 (sSort s1) e ->
        forall e0 : Σ;;; Γ,, svass n1 A1 |-i B1 = B2 : sSort s2,
        P1 (Γ,, svass n1 A1) B1 B2 (sSort s2) e0 ->
        forall e1 : Σ;;; Γ,, svass n1 A1 |-i t1 = t2 : B1,
        P1 (Γ,, svass n1 A1) t1 t2 B1 e1 ->
        P1 Γ (sLambda n1 A1 B1 t1) (sLambda n2 A2 B2 t2) (sProd n' A1 B1)
          (cong_Lambda Σ Γ n1 n2 n' A1 A2 B1 B2 t1 t2 s1 s2 e e0 e1)) ->
       (forall (Γ : scontext) (n1 n2 : name) (s1 s2 : sort) (t1 t2 A1 A2 B1 B2 u1 u2 : sterm) (e : Σ;;; Γ |-i A1 = A2 : sSort s1),
        P1 Γ A1 A2 (sSort s1) e ->
        forall e0 : Σ;;; Γ,, svass n1 A1 |-i B1 = B2 : sSort s2,
        P1 (Γ,, svass n1 A1) B1 B2 (sSort s2) e0 ->
        forall e1 : Σ;;; Γ |-i t1 = t2 : sProd n1 A1 B1,
        P1 Γ t1 t2 (sProd n1 A1 B1) e1 ->
        forall e2 : Σ;;; Γ |-i u1 = u2 : A1,
        P1 Γ u1 u2 A1 e2 ->
        P1 Γ (sApp t1 n1 A1 B1 u1) (sApp t2 n2 A2 B2 u2) (B1 {0 := u1})
          (cong_App Σ Γ n1 n2 s1 s2 t1 t2 A1 A2 B1 B2 u1 u2 e e0 e1 e2)) ->
       (forall (Γ : scontext) (s : sort) (A1 A2 u1 u2 v1 v2 : sterm) (e : Σ;;; Γ |-i A1 = A2 : sSort s),
        P1 Γ A1 A2 (sSort s) e ->
        forall e0 : Σ;;; Γ |-i u1 = u2 : A1,
        P1 Γ u1 u2 A1 e0 ->
        forall e1 : Σ;;; Γ |-i v1 = v2 : A1,
        P1 Γ v1 v2 A1 e1 -> P1 Γ (sEq A1 u1 v1) (sEq A2 u2 v2) (sSort s) (cong_Eq Σ Γ s A1 A2 u1 u2 v1 v2 e e0 e1)) ->
       (forall (Γ : scontext) (s : sort) (A1 A2 u1 u2 : sterm) (e : Σ;;; Γ |-i A1 = A2 : sSort s),
        P1 Γ A1 A2 (sSort s) e ->
        forall e0 : Σ;;; Γ |-i u1 = u2 : A1,
        P1 Γ u1 u2 A1 e0 -> P1 Γ (sRefl A1 u1) (sRefl A2 u2) (sEq A1 u1 u1) (cong_Refl Σ Γ s A1 A2 u1 u2 e e0)) ->
       (forall (Γ : scontext) (nx ne : name) (s1 s2 : sort) (A1 A2 u1 u2 v1 v2 P2 P3 p1 p2 w1 w2 : sterm)
          (e : Σ;;; Γ |-i A1 = A2 : sSort s1),
        P1 Γ A1 A2 (sSort s1) e ->
        forall e0 : Σ;;; Γ |-i u1 = u2 : A1,
        P1 Γ u1 u2 A1 e0 ->
        forall e1 : Σ;;; Γ |-i v1 = v2 : A1,
        P1 Γ v1 v2 A1 e1 ->
        forall e2 : Σ;;; (Γ,, svass nx A1),, svass ne (sEq (lift0 1 A1) (lift0 1 u1) (sRel 0)) |-i P2 = P3 : sSort s2,
        P1 ((Γ,, svass nx A1),, svass ne (sEq (lift0 1 A1) (lift0 1 u1) (sRel 0))) P2 P3 (sSort s2) e2 ->
        forall e3 : Σ;;; Γ |-i p1 = p2 : sEq A1 u1 v1,
        P1 Γ p1 p2 (sEq A1 u1 v1) e3 ->
        forall e4 : Σ;;; Γ |-i w1 = w2 : (P2 {1 := u1}) {0 := sRefl A1 u1},
        P1 Γ w1 w2 ((P2 {1 := u1}) {0 := sRefl A1 u1}) e4 ->
        P1 Γ (sJ A1 u1 P2 w1 v1 p1) (sJ A2 u2 P3 w2 v2 p2) ((P2 {1 := v1}) {0 := p1})
          (cong_J Σ Γ nx ne s1 s2 A1 A2 u1 u2 v1 v2 P2 P3 p1 p2 w1 w2 e e0 e1 e2 e3 e4)) ->
       (forall (Γ : scontext) (s : sort) (A1 A2 B1 B2 p1 p2 t1 t2 : sterm) (e : Σ;;; Γ |-i A1 = A2 : sSort s),
        P1 Γ A1 A2 (sSort s) e ->
        forall e0 : Σ;;; Γ |-i B1 = B2 : sSort s,
        P1 Γ B1 B2 (sSort s) e0 ->
        forall e1 : Σ;;; Γ |-i p1 = p2 : sEq (sSort s) A1 B1,
        P1 Γ p1 p2 (sEq (sSort s) A1 B1) e1 ->
        forall e2 : Σ;;; Γ |-i t1 = t2 : A1,
        P1 Γ t1 t2 A1 e2 ->
        P1 Γ (sTransport A1 B1 p1 t1) (sTransport A2 B2 p2 t2) B1 (cong_Transport Σ Γ s A1 A2 B1 B2 p1 p2 t1 t2 e e0 e1 e2)) ->
       (forall (Γ : scontext) (A1 A2 a1 a2 B1 B2 b1 b2 : sterm) (s : sort) (e : Σ;;; Γ |-i A1 = A2 : sSort s),
        P1 Γ A1 A2 (sSort s) e ->
        forall e0 : Σ;;; Γ |-i B1 = B2 : sSort s,
        P1 Γ B1 B2 (sSort s) e0 ->
        forall e1 : Σ;;; Γ |-i a1 = a2 : A1,
        P1 Γ a1 a2 A1 e1 ->
        forall e2 : Σ;;; Γ |-i b1 = b2 : B1,
        P1 Γ b1 b2 B1 e2 ->
        P1 Γ (sHeq A1 a1 B1 b1) (sHeq A2 a2 B2 b2) (sSort (succ_sort s)) (cong_Heq Σ Γ A1 A2 a1 a2 B1 B2 b1 b2 s e e0 e1 e2)) ->
       (forall (Γ : scontext) (A1 B1 A2 B2 : sterm) (s : sort) (e : Σ;;; Γ |-i A1 = B1 : sSort s),
        P1 Γ A1 B1 (sSort s) e ->
        forall e0 : Σ;;; Γ |-i A2 = B2 : sSort s,
        P1 Γ A2 B2 (sSort s) e0 -> P1 Γ (sPack A1 A2) (sPack B1 B2) (sSort s) (cong_Pack Σ Γ A1 B1 A2 B2 s e e0)) ->
       (forall (Γ : scontext) (A u v p1 p2 : sterm) (s : sort) (e : Σ;;; Γ |-i p1 = p2 : sHeq A u A v),
        P1 Γ p1 p2 (sHeq A u A v) e ->
        forall t : Σ;;; Γ |-i A : sSort s,
        P Γ A (sSort s) t ->
        forall t0 : Σ;;; Γ |-i u : A,
        P Γ u A t0 ->
        forall t1 : Σ;;; Γ |-i v : A,
        P Γ v A t1 -> P1 Γ (sHeqToEq p1) (sHeqToEq p2) (sEq A u v) (cong_HeqToEq Σ Γ A u v p1 p2 s e t t0 t1)) ->
       (forall (Γ : scontext) (A1 A2 a1 a2 : sterm) (s : sort) (e : Σ;;; Γ |-i A1 = A2 : sSort s),
        P1 Γ A1 A2 (sSort s) e ->
        forall e0 : Σ;;; Γ |-i a1 = a2 : A1,
        P1 Γ a1 a2 A1 e0 -> P1 Γ (sHeqRefl A1 a1) (sHeqRefl A2 a2) (sHeq A1 a1 A1 a1) (cong_HeqRefl Σ Γ A1 A2 a1 a2 s e e0)) ->
       (forall (Γ : scontext) (A a B b p1 p2 : sterm) (s : sort) (t : Σ;;; Γ |-i A : sSort s),
        P Γ A (sSort s) t ->
        forall t0 : Σ;;; Γ |-i B : sSort s,
        P Γ B (sSort s) t0 ->
        forall t1 : Σ;;; Γ |-i a : A,
        P Γ a A t1 ->
        forall t2 : Σ;;; Γ |-i b : B,
        P Γ b B t2 ->
        forall e : Σ;;; Γ |-i p1 = p2 : sHeq A a B b,
        P1 Γ p1 p2 (sHeq A a B b) e -> P1 Γ (sHeqSym p1) (sHeqSym p2) (sHeq B b A a) (cong_HeqSym Σ Γ A a B b p1 p2 s t t0 t1 t2 e)) ->
       (forall (Γ : scontext) (A a B b C c p1 p2 q1 q2 : sterm) (s : sort) (t : Σ;;; Γ |-i A : sSort s),
        P Γ A (sSort s) t ->
        forall t0 : Σ;;; Γ |-i B : sSort s,
        P Γ B (sSort s) t0 ->
        forall t1 : Σ;;; Γ |-i C : sSort s,
        P Γ C (sSort s) t1 ->
        forall t2 : Σ;;; Γ |-i a : A,
        P Γ a A t2 ->
        forall t3 : Σ;;; Γ |-i b : B,
        P Γ b B t3 ->
        forall t4 : Σ;;; Γ |-i c : C,
        P Γ c C t4 ->
        forall e : Σ;;; Γ |-i p1 = p2 : sHeq A a B b,
        P1 Γ p1 p2 (sHeq A a B b) e ->
        forall e0 : Σ;;; Γ |-i q1 = q2 : sHeq B b C c,
        P1 Γ q1 q2 (sHeq B b C c) e0 ->
        P1 Γ (sHeqTrans p1 q1) (sHeqTrans p2 q2) (sHeq A a C c) (cong_HeqTrans Σ Γ A a B b C c p1 p2 q1 q2 s t t0 t1 t2 t3 t4 e e0)) ->
       (forall (Γ : scontext) (A B p1 p2 t1 t2 : sterm) (s : sort) (t : Σ;;; Γ |-i A : sSort s),
        P Γ A (sSort s) t ->
        forall t0 : Σ;;; Γ |-i B : sSort s,
        P Γ B (sSort s) t0 ->
        forall e : Σ;;; Γ |-i t1 = t2 : A,
        P1 Γ t1 t2 A e ->
        forall e0 : Σ;;; Γ |-i p1 = p2 : sEq (sSort s) A B,
        P1 Γ p1 p2 (sEq (sSort s) A B) e0 ->
        P1 Γ (sHeqTransport p1 t1) (sHeqTransport p2 t2) (sHeq A t1 B (sTransport A B p1 t1))
          (cong_HeqTransport Σ Γ A B p1 p2 t1 t2 s t t0 e e0)) ->
       (forall (Γ : scontext) (s z : sort) (nx ny np : name) (A1 A2 B1 B2 pA pB B1' B2' pA' pB' : sterm)
          (e : Σ;;; Γ |-i pA = pA' : sHeq (sSort s) A1 (sSort s) A2),
        P1 Γ pA pA' (sHeq (sSort s) A1 (sSort s) A2) e ->
        forall
          e0 : Σ;;; Γ,, svass np (sPack A1 A2) |-i pB = pB'
               : sHeq (sSort z) ((lift 1 1 B1) {0 := sProjT1 (sRel 0)}) (sSort z) ((lift 1 1 B2) {0 := sProjT2 (sRel 0)}),
        P1 (Γ,, svass np (sPack A1 A2)) pB pB'
          (sHeq (sSort z) ((lift 1 1 B1) {0 := sProjT1 (sRel 0)}) (sSort z) ((lift 1 1 B2) {0 := sProjT2 (sRel 0)})) e0 ->
        forall t : Σ;;; Γ |-i A1 : sSort s,
        P Γ A1 (sSort s) t ->
        forall t0 : Σ;;; Γ |-i A2 : sSort s,
        P Γ A2 (sSort s) t0 ->
        forall e1 : Σ;;; Γ,, svass nx A1 |-i B1 = B1' : sSort z,
        P1 (Γ,, svass nx A1) B1 B1' (sSort z) e1 ->
        forall e2 : Σ;;; Γ,, svass ny A2 |-i B2 = B2' : sSort z,
        P1 (Γ,, svass ny A2) B2 B2' (sSort z) e2 ->
        P1 Γ (sCongProd B1 B2 pA pB) (sCongProd B1' B2' pA' pB')
          (sHeq (sSort (max_sort s z)) (sProd nx A1 B1) (sSort (max_sort s z)) (sProd ny A2 B2))
          (cong_CongProd Σ Γ s z nx ny np A1 A2 B1 B2 pA pB B1' B2' pA' pB' e e0 t t0 e1 e2)) ->
       (forall (Γ : scontext) (s z : sort) (nx ny np : name) (A1 A2 B1 B2 t1 t2 pA pB pt B1' B2' t1' t2' pA' pB' pt' : sterm)
          (e : Σ;;; Γ |-i pA = pA' : sHeq (sSort s) A1 (sSort s) A2),
        P1 Γ pA pA' (sHeq (sSort s) A1 (sSort s) A2) e ->
        forall
          e0 : Σ;;; Γ,, svass np (sPack A1 A2) |-i pB = pB'
               : sHeq (sSort z) ((lift 1 1 B1) {0 := sProjT1 (sRel 0)}) (sSort z) ((lift 1 1 B2) {0 := sProjT2 (sRel 0)}),
        P1 (Γ,, svass np (sPack A1 A2)) pB pB'
          (sHeq (sSort z) ((lift 1 1 B1) {0 := sProjT1 (sRel 0)}) (sSort z) ((lift 1 1 B2) {0 := sProjT2 (sRel 0)})) e0 ->
        forall
          e1 : Σ;;; Γ,, svass np (sPack A1 A2) |-i pt = pt'
               : sHeq ((lift 1 1 B1) {0 := sProjT1 (sRel 0)}) ((lift 1 1 t1) {0 := sProjT1 (sRel 0)})
                   ((lift 1 1 B2) {0 := sProjT2 (sRel 0)}) ((lift 1 1 t2) {0 := sProjT2 (sRel 0)}),
        P1 (Γ,, svass np (sPack A1 A2)) pt pt'
          (sHeq ((lift 1 1 B1) {0 := sProjT1 (sRel 0)}) ((lift 1 1 t1) {0 := sProjT1 (sRel 0)})
             ((lift 1 1 B2) {0 := sProjT2 (sRel 0)}) ((lift 1 1 t2) {0 := sProjT2 (sRel 0)})) e1 ->
        forall t : Σ;;; Γ |-i A1 : sSort s,
        P Γ A1 (sSort s) t ->
        forall t0 : Σ;;; Γ |-i A2 : sSort s,
        P Γ A2 (sSort s) t0 ->
        forall e2 : Σ;;; Γ,, svass nx A1 |-i B1 = B1' : sSort z,
        P1 (Γ,, svass nx A1) B1 B1' (sSort z) e2 ->
        forall e3 : Σ;;; Γ,, svass ny A2 |-i B2 = B2' : sSort z,
        P1 (Γ,, svass ny A2) B2 B2' (sSort z) e3 ->
        forall e4 : Σ;;; Γ,, svass nx A1 |-i t1 = t1' : B1,
        P1 (Γ,, svass nx A1) t1 t1' B1 e4 ->
        forall e5 : Σ;;; Γ,, svass ny A2 |-i t2 = t2' : B2,
        P1 (Γ,, svass ny A2) t2 t2' B2 e5 ->
        P1 Γ (sCongLambda B1 B2 t1 t2 pA pB pt) (sCongLambda B1' B2' t1' t2' pA' pB' pt')
          (sHeq (sProd nx A1 B1) (sLambda nx A1 B1 t1) (sProd ny A2 B2) (sLambda ny A2 B2 t2))
          (cong_CongLambda Σ Γ s z nx ny np A1 A2 B1 B2 t1 t2 pA pB pt B1' B2' t1' t2' pA' pB' pt' e e0 e1 t t0 e2 e3 e4 e5)) ->
       (forall (Γ : scontext) (s z : sort) (nx ny np : name) (A1 A2 B1 B2 u1 u2 v1 v2 pA pB pu pv B1' B2' pu' pA' pB' pv' : sterm)
          (e : Σ;;; Γ |-i pA = pA' : sHeq (sSort s) A1 (sSort s) A2),
        P1 Γ pA pA' (sHeq (sSort s) A1 (sSort s) A2) e ->
        forall
          e0 : Σ;;; Γ,, svass np (sPack A1 A2) |-i pB = pB'
               : sHeq (sSort z) ((lift 1 1 B1) {0 := sProjT1 (sRel 0)}) (sSort z) ((lift 1 1 B2) {0 := sProjT2 (sRel 0)}),
        P1 (Γ,, svass np (sPack A1 A2)) pB pB'
          (sHeq (sSort z) ((lift 1 1 B1) {0 := sProjT1 (sRel 0)}) (sSort z) ((lift 1 1 B2) {0 := sProjT2 (sRel 0)})) e0 ->
        forall e1 : Σ;;; Γ |-i pu = pu' : sHeq (sProd nx A1 B1) u1 (sProd ny A2 B2) u2,
        P1 Γ pu pu' (sHeq (sProd nx A1 B1) u1 (sProd ny A2 B2) u2) e1 ->
        forall e2 : Σ;;; Γ |-i pv = pv' : sHeq A1 v1 A2 v2,
        P1 Γ pv pv' (sHeq A1 v1 A2 v2) e2 ->
        forall t : Σ;;; Γ |-i A1 : sSort s,
        P Γ A1 (sSort s) t ->
        forall t0 : Σ;;; Γ |-i A2 : sSort s,
        P Γ A2 (sSort s) t0 ->
        forall e3 : Σ;;; Γ,, svass nx A1 |-i B1 = B1' : sSort z,
        P1 (Γ,, svass nx A1) B1 B1' (sSort z) e3 ->
        forall e4 : Σ;;; Γ,, svass ny A2 |-i B2 = B2' : sSort z,
        P1 (Γ,, svass ny A2) B2 B2' (sSort z) e4 ->
        forall t1 : Σ;;; Γ |-i u1 : sProd nx A1 B1,
        P Γ u1 (sProd nx A1 B1) t1 ->
        forall t2 : Σ;;; Γ |-i u2 : sProd ny A2 B2,
        P Γ u2 (sProd ny A2 B2) t2 ->
        forall t3 : Σ;;; Γ |-i v1 : A1,
        P Γ v1 A1 t3 ->
        forall t4 : Σ;;; Γ |-i v2 : A2,
        P Γ v2 A2 t4 ->
        P1 Γ (sCongApp B1 B2 pu pA pB pv) (sCongApp B1' B2' pu' pA' pB' pv')
          (sHeq (B1 {0 := v1}) (sApp u1 nx A1 B1 v1) (B2 {0 := v2}) (sApp u2 ny A2 B2 v2))
          (cong_CongApp Σ Γ s z nx ny np A1 A2 B1 B2 u1 u2 v1 v2 pA pB pu pv B1' B2' pu' pA' pB' pv' e e0 e1 e2 t t0 e3 e4 t1 t2 t3
             t4)) ->
       (forall (Γ : scontext) (s : sort) (A1 A2 u1 u2 v1 v2 pA pu pv pA' pu' pv' : sterm)
          (e : Σ;;; Γ |-i pA = pA' : sHeq (sSort s) A1 (sSort s) A2),
        P1 Γ pA pA' (sHeq (sSort s) A1 (sSort s) A2) e ->
        forall e0 : Σ;;; Γ |-i pu = pu' : sHeq A1 u1 A2 u2,
        P1 Γ pu pu' (sHeq A1 u1 A2 u2) e0 ->
        forall e1 : Σ;;; Γ |-i pv = pv' : sHeq A1 v1 A2 v2,
        P1 Γ pv pv' (sHeq A1 v1 A2 v2) e1 ->
        forall t : Σ;;; Γ |-i A1 : sSort s,
        P Γ A1 (sSort s) t ->
        forall t0 : Σ;;; Γ |-i A2 : sSort s,
        P Γ A2 (sSort s) t0 ->
        forall t1 : Σ;;; Γ |-i u1 : A1,
        P Γ u1 A1 t1 ->
        forall t2 : Σ;;; Γ |-i u2 : A2,
        P Γ u2 A2 t2 ->
        forall t3 : Σ;;; Γ |-i v1 : A1,
        P Γ v1 A1 t3 ->
        forall t4 : Σ;;; Γ |-i v2 : A2,
        P Γ v2 A2 t4 ->
        P1 Γ (sCongEq pA pu pv) (sCongEq pA' pu' pv') (sHeq (sSort s) (sEq A1 u1 v1) (sSort s) (sEq A2 u2 v2))
          (cong_CongEq Σ Γ s A1 A2 u1 u2 v1 v2 pA pu pv pA' pu' pv' e e0 e1 t t0 t1 t2 t3 t4)) ->
       (forall (Γ : scontext) (s : sort) (A1 A2 u1 u2 pA pu pA' pu' : sterm)
          (e : Σ;;; Γ |-i pA = pA' : sHeq (sSort s) A1 (sSort s) A2),
        P1 Γ pA pA' (sHeq (sSort s) A1 (sSort s) A2) e ->
        forall e0 : Σ;;; Γ |-i pu = pu' : sHeq A1 u1 A2 u2,
        P1 Γ pu pu' (sHeq A1 u1 A2 u2) e0 ->
        forall t : Σ;;; Γ |-i A1 : sSort s,
        P Γ A1 (sSort s) t ->
        forall t0 : Σ;;; Γ |-i A2 : sSort s,
        P Γ A2 (sSort s) t0 ->
        forall t1 : Σ;;; Γ |-i u1 : A1,
        P Γ u1 A1 t1 ->
        forall t2 : Σ;;; Γ |-i u2 : A2,
        P Γ u2 A2 t2 ->
        P1 Γ (sCongRefl pA pu) (sCongRefl pA' pu') (sHeq (sEq A1 u1 u1) (sRefl A1 u1) (sEq A2 u2 u2) (sRefl A2 u2))
          (cong_CongRefl Σ Γ s A1 A2 u1 u2 pA pu pA' pu' e e0 t t0 t1 t2)) ->
       (forall (Γ : scontext) (A u v p1 p2 : sterm) (s : sort) (e : Σ;;; Γ |-i p1 = p2 : sEq A u v),
        P1 Γ p1 p2 (sEq A u v) e ->
        forall t : Σ;;; Γ |-i A : sSort s,
        P Γ A (sSort s) t ->
        forall t0 : Σ;;; Γ |-i u : A,
        P Γ u A t0 ->
        forall t1 : Σ;;; Γ |-i v : A,
        P Γ v A t1 -> P1 Γ (sEqToHeq p1) (sEqToHeq p2) (sHeq A u A v) (cong_EqToHeq Σ Γ A u v p1 p2 s e t t0 t1)) ->
       (forall (Γ : scontext) (A u B v p1 p2 : sterm) (s : sort) (e : Σ;;; Γ |-i p1 = p2 : sHeq A u B v),
        P1 Γ p1 p2 (sHeq A u B v) e ->
        forall t : Σ;;; Γ |-i A : sSort s,
        P Γ A (sSort s) t ->
        forall t0 : Σ;;; Γ |-i B : sSort s,
        P Γ B (sSort s) t0 ->
        forall t1 : Σ;;; Γ |-i u : A,
        P Γ u A t1 ->
        forall t2 : Σ;;; Γ |-i v : B,
        P Γ v B t2 -> P1 Γ (sHeqTypeEq p1) (sHeqTypeEq p2) (sEq (sSort s) A B) (cong_HeqTypeEq Σ Γ A u B v p1 p2 s e t t0 t1 t2)) ->
       (forall (Γ : scontext) (A1 A2 p1 p2 : sterm) (s : sort) (t : Σ;;; Γ |-i A1 : sSort s),
        P Γ A1 (sSort s) t ->
        forall t0 : Σ;;; Γ |-i A2 : sSort s,
        P Γ A2 (sSort s) t0 ->
        forall e : Σ;;; Γ |-i p1 = p2 : sPack A1 A2,
        P1 Γ p1 p2 (sPack A1 A2) e -> P1 Γ (sProjT1 p1) (sProjT1 p2) A1 (cong_ProjT1 Σ Γ A1 A2 p1 p2 s t t0 e)) ->
       (forall (Γ : scontext) (A1 A2 p1 p2 : sterm) (s : sort) (t : Σ;;; Γ |-i A1 : sSort s),
        P Γ A1 (sSort s) t ->
        forall t0 : Σ;;; Γ |-i A2 : sSort s,
        P Γ A2 (sSort s) t0 ->
        forall e : Σ;;; Γ |-i p1 = p2 : sPack A1 A2,
        P1 Γ p1 p2 (sPack A1 A2) e -> P1 Γ (sProjT2 p1) (sProjT2 p2) A2 (cong_ProjT2 Σ Γ A1 A2 p1 p2 s t t0 e)) ->
       (forall (Γ : scontext) (A1 A2 p1 p2 : sterm) (s : sort) (t : Σ;;; Γ |-i A1 : sSort s),
        P Γ A1 (sSort s) t ->
        forall t0 : Σ;;; Γ |-i A2 : sSort s,
        P Γ A2 (sSort s) t0 ->
        forall e : Σ;;; Γ |-i p1 = p2 : sPack A1 A2,
        P1 Γ p1 p2 (sPack A1 A2) e ->
        P1 Γ (sProjTe p1) (sProjTe p2) (sHeq A1 (sProjT1 p1) A2 (sProjT2 p1)) (cong_ProjTe Σ Γ A1 A2 p1 p2 s t t0 e)) ->
       (forall (Γ : scontext) (s : sort) (A u : sterm) (t : Σ;;; Γ |-i A : sSort s),
        P Γ A (sSort s) t ->
        forall t0 : Σ;;; Γ |-i u : A,
        P Γ u A t0 -> P1 Γ (sHeqToEq (sHeqRefl A u)) (sRefl A u) (sEq A u u) (eq_HeqToEqRefl Σ Γ s A u t t0)) ->
       (forall (Γ : scontext) (n : nat) (w : wf Σ Γ),
        P0 Γ w ->
        forall isdecl : n < #|Γ|,
        P Γ (sRel n) (lift0 (S n) (sdecl_type (safe_nth Γ (exist (fun n0 : nat => n0 < #|Γ|) n isdecl)))) (type_Rel Σ Γ n w isdecl)) ->
       (forall (Γ : scontext) (s : sort) (w : wf Σ Γ), P0 Γ w -> P Γ (sSort s) (sSort (succ_sort s)) (type_Sort Σ Γ s w)) ->
       (forall (Γ : scontext) (n : name) (t b : sterm) (s1 s2 : sort) (t0 : Σ;;; Γ |-i t : sSort s1),
        P Γ t (sSort s1) t0 ->
        forall t1 : Σ;;; Γ,, svass n t |-i b : sSort s2,
        P (Γ,, svass n t) b (sSort s2) t1 -> P Γ (sProd n t b) (sSort (max_sort s1 s2)) (type_Prod Σ Γ n t b s1 s2 t0 t1)) ->
       (forall (Γ : scontext) (n n' : name) (t b : sterm) (s1 s2 : sort) (bty : sterm) (t0 : Σ;;; Γ |-i t : sSort s1),
        P Γ t (sSort s1) t0 ->
        forall t1 : Σ;;; Γ,, svass n t |-i bty : sSort s2,
        P (Γ,, svass n t) bty (sSort s2) t1 ->
        forall t2 : Σ;;; Γ,, svass n t |-i b : bty,
        P (Γ,, svass n t) b bty t2 -> P Γ (sLambda n t bty b) (sProd n' t bty) (type_Lambda Σ Γ n n' t b s1 s2 bty t0 t1 t2)) ->
       (forall (Γ : scontext) (n : name) (s1 s2 : sort) (t A B u : sterm) (t0 : Σ;;; Γ |-i A : sSort s1),
        P Γ A (sSort s1) t0 ->
        forall t1 : Σ;;; Γ,, svass n A |-i B : sSort s2,
        P (Γ,, svass n A) B (sSort s2) t1 ->
        forall t2 : Σ;;; Γ |-i t : sProd n A B,
        P Γ t (sProd n A B) t2 ->
        forall t3 : Σ;;; Γ |-i u : A, P Γ u A t3 -> P Γ (sApp t n A B u) (B {0 := u}) (type_App Σ Γ n s1 s2 t A B u t0 t1 t2 t3)) ->
       (forall (Γ : scontext) (s : sort) (A u v : sterm) (t : Σ;;; Γ |-i A : sSort s),
        P Γ A (sSort s) t ->
        forall t0 : Σ;;; Γ |-i u : A,
        P Γ u A t0 -> forall t1 : Σ;;; Γ |-i v : A, P Γ v A t1 -> P Γ (sEq A u v) (sSort s) (type_Eq Σ Γ s A u v t t0 t1)) ->
       (forall (Γ : scontext) (s : sort) (A u : sterm) (t : Σ;;; Γ |-i A : sSort s),
        P Γ A (sSort s) t -> forall t0 : Σ;;; Γ |-i u : A, P Γ u A t0 -> P Γ (sRefl A u) (sEq A u u) (type_Refl Σ Γ s A u t t0)) ->
       (forall (Γ : scontext) (nx ne : name) (s1 s2 : sort) (A u v P2 p w : sterm) (t : Σ;;; Γ |-i A : sSort s1),
        P Γ A (sSort s1) t ->
        forall t0 : Σ;;; Γ |-i u : A,
        P Γ u A t0 ->
        forall t1 : Σ;;; Γ |-i v : A,
        P Γ v A t1 ->
        forall t2 : Σ;;; (Γ,, svass nx A),, svass ne (sEq (lift0 1 A) (lift0 1 u) (sRel 0)) |-i P2 : sSort s2,
        P ((Γ,, svass nx A),, svass ne (sEq (lift0 1 A) (lift0 1 u) (sRel 0))) P2 (sSort s2) t2 ->
        forall t3 : Σ;;; Γ |-i p : sEq A u v,
        P Γ p (sEq A u v) t3 ->
        forall t4 : Σ;;; Γ |-i w : (P2 {1 := u}) {0 := sRefl A u},
        P Γ w ((P2 {1 := u}) {0 := sRefl A u}) t4 ->
        P Γ (sJ A u P2 w v p) ((P2 {1 := v}) {0 := p}) (type_J Σ Γ nx ne s1 s2 A u v P2 p w t t0 t1 t2 t3 t4)) ->
       (forall (Γ : scontext) (s : sort) (T1 T2 p t : sterm) (t0 : Σ;;; Γ |-i T1 : sSort s),
        P Γ T1 (sSort s) t0 ->
        forall t1 : Σ;;; Γ |-i T2 : sSort s,
        P Γ T2 (sSort s) t1 ->
        forall t2 : Σ;;; Γ |-i p : sEq (sSort s) T1 T2,
        P Γ p (sEq (sSort s) T1 T2) t2 ->
        forall t3 : Σ;;; Γ |-i t : T1, P Γ t T1 t3 -> P Γ (sTransport T1 T2 p t) T2 (type_Transport Σ Γ s T1 T2 p t t0 t1 t2 t3)) ->
       (forall (Γ : scontext) (A a B b : sterm) (s : sort) (t : Σ;;; Γ |-i A : sSort s),
        P Γ A (sSort s) t ->
        forall t0 : Σ;;; Γ |-i B : sSort s,
        P Γ B (sSort s) t0 ->
        forall t1 : Σ;;; Γ |-i a : A,
        P Γ a A t1 ->
        forall t2 : Σ;;; Γ |-i b : B, P Γ b B t2 -> P Γ (sHeq A a B b) (sSort (succ_sort s)) (type_Heq Σ Γ A a B b s t t0 t1 t2)) ->
       (forall (Γ : scontext) (A u v p : sterm) (s : sort) (t : Σ;;; Γ |-i p : sHeq A u A v),
        P Γ p (sHeq A u A v) t ->
        forall t0 : Σ;;; Γ |-i A : sSort s,
        P Γ A (sSort s) t0 ->
        forall t1 : Σ;;; Γ |-i u : A,
        P Γ u A t1 ->
        forall t2 : Σ;;; Γ |-i v : A, P Γ v A t2 -> P Γ (sHeqToEq p) (sEq A u v) (type_HeqToEq Σ Γ A u v p s t t0 t1 t2)) ->
       (forall (Γ : scontext) (A a : sterm) (s : sort) (t : Σ;;; Γ |-i A : sSort s),
        P Γ A (sSort s) t ->
        forall t0 : Σ;;; Γ |-i a : A, P Γ a A t0 -> P Γ (sHeqRefl A a) (sHeq A a A a) (type_HeqRefl Σ Γ A a s t t0)) ->
       (forall (Γ : scontext) (A a B b p : sterm) (s : sort) (t : Σ;;; Γ |-i A : sSort s),
        P Γ A (sSort s) t ->
        forall t0 : Σ;;; Γ |-i B : sSort s,
        P Γ B (sSort s) t0 ->
        forall t1 : Σ;;; Γ |-i a : A,
        P Γ a A t1 ->
        forall t2 : Σ;;; Γ |-i b : B,
        P Γ b B t2 ->
        forall t3 : Σ;;; Γ |-i p : sHeq A a B b,
        P Γ p (sHeq A a B b) t3 -> P Γ (sHeqSym p) (sHeq B b A a) (type_HeqSym Σ Γ A a B b p s t t0 t1 t2 t3)) ->
       (forall (Γ : scontext) (A a B b C c p q : sterm) (s : sort) (t : Σ;;; Γ |-i A : sSort s),
        P Γ A (sSort s) t ->
        forall t0 : Σ;;; Γ |-i B : sSort s,
        P Γ B (sSort s) t0 ->
        forall t1 : Σ;;; Γ |-i C : sSort s,
        P Γ C (sSort s) t1 ->
        forall t2 : Σ;;; Γ |-i a : A,
        P Γ a A t2 ->
        forall t3 : Σ;;; Γ |-i b : B,
        P Γ b B t3 ->
        forall t4 : Σ;;; Γ |-i c : C,
        P Γ c C t4 ->
        forall t5 : Σ;;; Γ |-i p : sHeq A a B b,
        P Γ p (sHeq A a B b) t5 ->
        forall t6 : Σ;;; Γ |-i q : sHeq B b C c,
        P Γ q (sHeq B b C c) t6 -> P Γ (sHeqTrans p q) (sHeq A a C c) (type_HeqTrans Σ Γ A a B b C c p q s t t0 t1 t2 t3 t4 t5 t6)) ->
       (forall (Γ : scontext) (A B p t : sterm) (s : sort) (t0 : Σ;;; Γ |-i A : sSort s),
        P Γ A (sSort s) t0 ->
        forall t1 : Σ;;; Γ |-i B : sSort s,
        P Γ B (sSort s) t1 ->
        forall t2 : Σ;;; Γ |-i t : A,
        P Γ t A t2 ->
        forall t3 : Σ;;; Γ |-i p : sEq (sSort s) A B,
        P Γ p (sEq (sSort s) A B) t3 ->
        P Γ (sHeqTransport p t) (sHeq A t B (sTransport A B p t)) (type_HeqTransport Σ Γ A B p t s t0 t1 t2 t3)) ->
       (forall (Γ : scontext) (s z : sort) (nx ny np : name) (A1 A2 B1 B2 pA pB : sterm)
          (t : Σ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2),
        P Γ pA (sHeq (sSort s) A1 (sSort s) A2) t ->
        forall
          t0 : Σ;;; Γ,, svass np (sPack A1 A2) |-i pB
               : sHeq (sSort z) ((lift 1 1 B1) {0 := sProjT1 (sRel 0)}) (sSort z) ((lift 1 1 B2) {0 := sProjT2 (sRel 0)}),
        P (Γ,, svass np (sPack A1 A2)) pB
          (sHeq (sSort z) ((lift 1 1 B1) {0 := sProjT1 (sRel 0)}) (sSort z) ((lift 1 1 B2) {0 := sProjT2 (sRel 0)})) t0 ->
        forall t1 : Σ;;; Γ |-i A1 : sSort s,
        P Γ A1 (sSort s) t1 ->
        forall t2 : Σ;;; Γ |-i A2 : sSort s,
        P Γ A2 (sSort s) t2 ->
        forall t3 : Σ;;; Γ,, svass nx A1 |-i B1 : sSort z,
        P (Γ,, svass nx A1) B1 (sSort z) t3 ->
        forall t4 : Σ;;; Γ,, svass ny A2 |-i B2 : sSort z,
        P (Γ,, svass ny A2) B2 (sSort z) t4 ->
        P Γ (sCongProd B1 B2 pA pB) (sHeq (sSort (max_sort s z)) (sProd nx A1 B1) (sSort (max_sort s z)) (sProd ny A2 B2))
          (type_CongProd Σ Γ s z nx ny np A1 A2 B1 B2 pA pB t t0 t1 t2 t3 t4)) ->
       (forall (Γ : scontext) (s z : sort) (nx ny np : name) (A1 A2 B1 B2 t1 t2 pA pB pt : sterm)
          (t : Σ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2),
        P Γ pA (sHeq (sSort s) A1 (sSort s) A2) t ->
        forall
          t0 : Σ;;; Γ,, svass np (sPack A1 A2) |-i pB
               : sHeq (sSort z) ((lift 1 1 B1) {0 := sProjT1 (sRel 0)}) (sSort z) ((lift 1 1 B2) {0 := sProjT2 (sRel 0)}),
        P (Γ,, svass np (sPack A1 A2)) pB
          (sHeq (sSort z) ((lift 1 1 B1) {0 := sProjT1 (sRel 0)}) (sSort z) ((lift 1 1 B2) {0 := sProjT2 (sRel 0)})) t0 ->
        forall
          t3 : Σ;;; Γ,, svass np (sPack A1 A2) |-i pt
               : sHeq ((lift 1 1 B1) {0 := sProjT1 (sRel 0)}) ((lift 1 1 t1) {0 := sProjT1 (sRel 0)})
                   ((lift 1 1 B2) {0 := sProjT2 (sRel 0)}) ((lift 1 1 t2) {0 := sProjT2 (sRel 0)}),
        P (Γ,, svass np (sPack A1 A2)) pt
          (sHeq ((lift 1 1 B1) {0 := sProjT1 (sRel 0)}) ((lift 1 1 t1) {0 := sProjT1 (sRel 0)})
             ((lift 1 1 B2) {0 := sProjT2 (sRel 0)}) ((lift 1 1 t2) {0 := sProjT2 (sRel 0)})) t3 ->
        forall t4 : Σ;;; Γ |-i A1 : sSort s,
        P Γ A1 (sSort s) t4 ->
        forall t5 : Σ;;; Γ |-i A2 : sSort s,
        P Γ A2 (sSort s) t5 ->
        forall t6 : Σ;;; Γ,, svass nx A1 |-i B1 : sSort z,
        P (Γ,, svass nx A1) B1 (sSort z) t6 ->
        forall t7 : Σ;;; Γ,, svass ny A2 |-i B2 : sSort z,
        P (Γ,, svass ny A2) B2 (sSort z) t7 ->
        forall t8 : Σ;;; Γ,, svass nx A1 |-i t1 : B1,
        P (Γ,, svass nx A1) t1 B1 t8 ->
        forall t9 : Σ;;; Γ,, svass ny A2 |-i t2 : B2,
        P (Γ,, svass ny A2) t2 B2 t9 ->
        P Γ (sCongLambda B1 B2 t1 t2 pA pB pt) (sHeq (sProd nx A1 B1) (sLambda nx A1 B1 t1) (sProd ny A2 B2) (sLambda ny A2 B2 t2))
          (type_CongLambda Σ Γ s z nx ny np A1 A2 B1 B2 t1 t2 pA pB pt t t0 t3 t4 t5 t6 t7 t8 t9)) ->
       (forall (Γ : scontext) (s z : sort) (nx ny np : name) (A1 A2 B1 B2 u1 u2 v1 v2 pA pB pu pv : sterm)
          (t : Σ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2),
        P Γ pA (sHeq (sSort s) A1 (sSort s) A2) t ->
        forall
          t0 : Σ;;; Γ,, svass np (sPack A1 A2) |-i pB
               : sHeq (sSort z) ((lift 1 1 B1) {0 := sProjT1 (sRel 0)}) (sSort z) ((lift 1 1 B2) {0 := sProjT2 (sRel 0)}),
        P (Γ,, svass np (sPack A1 A2)) pB
          (sHeq (sSort z) ((lift 1 1 B1) {0 := sProjT1 (sRel 0)}) (sSort z) ((lift 1 1 B2) {0 := sProjT2 (sRel 0)})) t0 ->
        forall t1 : Σ;;; Γ |-i pu : sHeq (sProd nx A1 B1) u1 (sProd ny A2 B2) u2,
        P Γ pu (sHeq (sProd nx A1 B1) u1 (sProd ny A2 B2) u2) t1 ->
        forall t2 : Σ;;; Γ |-i pv : sHeq A1 v1 A2 v2,
        P Γ pv (sHeq A1 v1 A2 v2) t2 ->
        forall t3 : Σ;;; Γ |-i A1 : sSort s,
        P Γ A1 (sSort s) t3 ->
        forall t4 : Σ;;; Γ |-i A2 : sSort s,
        P Γ A2 (sSort s) t4 ->
        forall t5 : Σ;;; Γ,, svass nx A1 |-i B1 : sSort z,
        P (Γ,, svass nx A1) B1 (sSort z) t5 ->
        forall t6 : Σ;;; Γ,, svass ny A2 |-i B2 : sSort z,
        P (Γ,, svass ny A2) B2 (sSort z) t6 ->
        forall t7 : Σ;;; Γ |-i u1 : sProd nx A1 B1,
        P Γ u1 (sProd nx A1 B1) t7 ->
        forall t8 : Σ;;; Γ |-i u2 : sProd ny A2 B2,
        P Γ u2 (sProd ny A2 B2) t8 ->
        forall t9 : Σ;;; Γ |-i v1 : A1,
        P Γ v1 A1 t9 ->
        forall t10 : Σ;;; Γ |-i v2 : A2,
        P Γ v2 A2 t10 ->
        P Γ (sCongApp B1 B2 pu pA pB pv) (sHeq (B1 {0 := v1}) (sApp u1 nx A1 B1 v1) (B2 {0 := v2}) (sApp u2 ny A2 B2 v2))
          (type_CongApp Σ Γ s z nx ny np A1 A2 B1 B2 u1 u2 v1 v2 pA pB pu pv t t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10)) ->
       (forall (Γ : scontext) (s : sort) (A1 A2 u1 u2 v1 v2 pA pu pv : sterm) (t : Σ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2),
        P Γ pA (sHeq (sSort s) A1 (sSort s) A2) t ->
        forall t0 : Σ;;; Γ |-i pu : sHeq A1 u1 A2 u2,
        P Γ pu (sHeq A1 u1 A2 u2) t0 ->
        forall t1 : Σ;;; Γ |-i pv : sHeq A1 v1 A2 v2,
        P Γ pv (sHeq A1 v1 A2 v2) t1 ->
        forall t2 : Σ;;; Γ |-i A1 : sSort s,
        P Γ A1 (sSort s) t2 ->
        forall t3 : Σ;;; Γ |-i A2 : sSort s,
        P Γ A2 (sSort s) t3 ->
        forall t4 : Σ;;; Γ |-i u1 : A1,
        P Γ u1 A1 t4 ->
        forall t5 : Σ;;; Γ |-i u2 : A2,
        P Γ u2 A2 t5 ->
        forall t6 : Σ;;; Γ |-i v1 : A1,
        P Γ v1 A1 t6 ->
        forall t7 : Σ;;; Γ |-i v2 : A2,
        P Γ v2 A2 t7 ->
        P Γ (sCongEq pA pu pv) (sHeq (sSort s) (sEq A1 u1 v1) (sSort s) (sEq A2 u2 v2))
          (type_CongEq Σ Γ s A1 A2 u1 u2 v1 v2 pA pu pv t t0 t1 t2 t3 t4 t5 t6 t7)) ->
       (forall (Γ : scontext) (s : sort) (A1 A2 u1 u2 pA pu : sterm) (t : Σ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2),
        P Γ pA (sHeq (sSort s) A1 (sSort s) A2) t ->
        forall t0 : Σ;;; Γ |-i pu : sHeq A1 u1 A2 u2,
        P Γ pu (sHeq A1 u1 A2 u2) t0 ->
        forall t1 : Σ;;; Γ |-i A1 : sSort s,
        P Γ A1 (sSort s) t1 ->
        forall t2 : Σ;;; Γ |-i A2 : sSort s,
        P Γ A2 (sSort s) t2 ->
        forall t3 : Σ;;; Γ |-i u1 : A1,
        P Γ u1 A1 t3 ->
        forall t4 : Σ;;; Γ |-i u2 : A2,
        P Γ u2 A2 t4 ->
        P Γ (sCongRefl pA pu) (sHeq (sEq A1 u1 u1) (sRefl A1 u1) (sEq A2 u2 u2) (sRefl A2 u2))
          (type_CongRefl Σ Γ s A1 A2 u1 u2 pA pu t t0 t1 t2 t3 t4)) ->
       (forall (Γ : scontext) (A u v p : sterm) (s : sort) (t : Σ;;; Γ |-i p : sEq A u v),
        P Γ p (sEq A u v) t ->
        forall t0 : Σ;;; Γ |-i A : sSort s,
        P Γ A (sSort s) t0 ->
        forall t1 : Σ;;; Γ |-i u : A,
        P Γ u A t1 ->
        forall t2 : Σ;;; Γ |-i v : A, P Γ v A t2 -> P Γ (sEqToHeq p) (sHeq A u A v) (type_EqToHeq Σ Γ A u v p s t t0 t1 t2)) ->
       (forall (Γ : scontext) (A u B v p : sterm) (s : sort) (t : Σ;;; Γ |-i p : sHeq A u B v),
        P Γ p (sHeq A u B v) t ->
        forall t0 : Σ;;; Γ |-i A : sSort s,
        P Γ A (sSort s) t0 ->
        forall t1 : Σ;;; Γ |-i B : sSort s,
        P Γ B (sSort s) t1 ->
        forall t2 : Σ;;; Γ |-i u : A,
        P Γ u A t2 ->
        forall t3 : Σ;;; Γ |-i v : B,
        P Γ v B t3 -> P Γ (sHeqTypeEq p) (sEq (sSort s) A B) (type_HeqTypeEq Σ Γ A u B v p s t t0 t1 t2 t3)) ->
       (forall (Γ : scontext) (A1 A2 : sterm) (s : sort) (t : Σ;;; Γ |-i A1 : sSort s),
        P Γ A1 (sSort s) t ->
        forall t0 : Σ;;; Γ |-i A2 : sSort s, P Γ A2 (sSort s) t0 -> P Γ (sPack A1 A2) (sSort s) (type_Pack Σ Γ A1 A2 s t t0)) ->
       (forall (Γ : scontext) (A1 A2 p : sterm) (s : sort) (t : Σ;;; Γ |-i A1 : sSort s),
        P Γ A1 (sSort s) t ->
        forall t0 : Σ;;; Γ |-i A2 : sSort s,
        P Γ A2 (sSort s) t0 ->
        forall t1 : Σ;;; Γ |-i p : sPack A1 A2, P Γ p (sPack A1 A2) t1 -> P Γ (sProjT1 p) A1 (type_ProjT1 Σ Γ A1 A2 p s t t0 t1)) ->
       (forall (Γ : scontext) (A1 A2 p : sterm) (s : sort) (t : Σ;;; Γ |-i A1 : sSort s),
        P Γ A1 (sSort s) t ->
        forall t0 : Σ;;; Γ |-i A2 : sSort s,
        P Γ A2 (sSort s) t0 ->
        forall t1 : Σ;;; Γ |-i p : sPack A1 A2, P Γ p (sPack A1 A2) t1 -> P Γ (sProjT2 p) A2 (type_ProjT2 Σ Γ A1 A2 p s t t0 t1)) ->
       (forall (Γ : scontext) (A1 A2 p : sterm) (s : sort) (t : Σ;;; Γ |-i A1 : sSort s),
        P Γ A1 (sSort s) t ->
        forall t0 : Σ;;; Γ |-i A2 : sSort s,
        P Γ A2 (sSort s) t0 ->
        forall t1 : Σ;;; Γ |-i p : sPack A1 A2,
        P Γ p (sPack A1 A2) t1 -> P Γ (sProjTe p) (sHeq A1 (sProjT1 p) A2 (sProjT2 p)) (type_ProjTe Σ Γ A1 A2 p s t t0 t1)) ->
       (forall (Γ : scontext) (ind : inductive) (w : wf Σ Γ),
        P0 Γ w ->
        forall (univs : universe_context) (decl : sone_inductive_body) (isdecl : sdeclared_inductive (fst Σ) ind univs decl),
        P Γ (sInd ind) (sind_type decl) (type_Ind Σ Γ ind w univs decl isdecl)) ->
       (forall (Γ : scontext) (ind : inductive) (i : nat) (w : wf Σ Γ),
        P0 Γ w ->
        forall (univs : universe_context) (decl : ident * sterm * nat) (isdecl : sdeclared_constructor (fst Σ) (ind, i) univs decl),
        P Γ (sConstruct ind i) (stype_of_constructor (fst Σ) (ind, i) univs decl isdecl)
          (type_Construct Σ Γ ind i w univs decl isdecl)) ->
       (forall (Γ : scontext) (t A B : sterm) (s : sort) (t0 : Σ;;; Γ |-i t : A),
        P Γ t A t0 ->
        forall t1 : Σ;;; Γ |-i B : sSort s,
        P Γ B (sSort s) t1 ->
        forall e : Σ;;; Γ |-i A = B : sSort s, P1 Γ A B (sSort s) e -> P Γ t B (type_conv Σ Γ t A B s t0 t1 e)) ->
       P0 [] (wf_nil Σ) ->
       (forall (s : sort) (Γ : scontext) (x : name) (A : sterm) (w : wf Σ Γ),
        P0 Γ w -> forall t : Σ;;; Γ |-i A : sSort s, P Γ A (sSort s) t -> P0 (Γ,, svass x A) (wf_snoc Σ s Γ x A w t)) ->
       (forall (Γ : scontext) (u A : sterm) (t : Σ;;; Γ |-i u : A), P Γ u A t -> P1 Γ u u A (eq_reflexivity Σ Γ u A t)) ->
       (forall (Γ : scontext) (u v A : sterm) (e : Σ;;; Γ |-i u = v : A), P1 Γ u v A e -> P1 Γ v u A (eq_symmetry Σ Γ u v A e)) ->
       (forall (Γ : scontext) (u v w A : sterm) (e : Σ;;; Γ |-i u = v : A),
        P1 Γ u v A e -> forall e0 : Σ;;; Γ |-i v = w : A, P1 Γ v w A e0 -> P1 Γ u w A (eq_transitivity Σ Γ u v w A e e0)) ->
       (forall (Γ : scontext) (s1 s2 : sort) (n : name) (A B t u : sterm) (t0 : Σ;;; Γ |-i A : sSort s1),
        P Γ A (sSort s1) t0 ->
        forall t1 : Σ;;; Γ,, svass n A |-i B : sSort s2,
        P (Γ,, svass n A) B (sSort s2) t1 ->
        forall t2 : Σ;;; Γ,, svass n A |-i t : B,
        P (Γ,, svass n A) t B t2 ->
        forall t3 : Σ;;; Γ |-i u : A,
        P Γ u A t3 -> P1 Γ (sApp (sLambda n A B t) n A B u) (t {0 := u}) (B {0 := u}) (eq_beta Σ Γ s1 s2 n A B t u t0 t1 t2 t3)) ->
       (forall (Γ : scontext) (nx ne : name) (s1 s2 : sort) (A u P2 w : sterm) (t : Σ;;; Γ |-i A : sSort s1),
        P Γ A (sSort s1) t ->
        forall t0 : Σ;;; Γ |-i u : A,
        P Γ u A t0 ->
        forall t1 : Σ;;; (Γ,, svass nx A),, svass ne (sEq (lift0 1 A) (lift0 1 u) (sRel 0)) |-i P2 : sSort s2,
        P ((Γ,, svass nx A),, svass ne (sEq (lift0 1 A) (lift0 1 u) (sRel 0))) P2 (sSort s2) t1 ->
        forall t2 : Σ;;; Γ |-i w : (P2 {1 := u}) {0 := sRefl A u},
        P Γ w ((P2 {1 := u}) {0 := sRefl A u}) t2 ->
        P1 Γ (sJ A u P2 w u (sRefl A u)) w ((P2 {1 := u}) {0 := sRefl A u}) (eq_JRefl Σ Γ nx ne s1 s2 A u P2 w t t0 t1 t2)) ->
       (forall (Γ : scontext) (s : sort) (A t : sterm) (t0 : Σ;;; Γ |-i A : sSort s),
        P Γ A (sSort s) t0 ->
        forall t1 : Σ;;; Γ |-i t : A,
        P Γ t A t1 -> P1 Γ (sTransport A A (sRefl (sSort s) A) t) t A (eq_TransportRefl Σ Γ s A t t0 t1)) ->
       (forall (Γ : scontext) (s : sort) (T1 T2 t1 t2 : sterm) (e : Σ;;; Γ |-i t1 = t2 : T1),
        P1 Γ t1 t2 T1 e ->
        forall e0 : Σ;;; Γ |-i T1 = T2 : sSort s, P1 Γ T1 T2 (sSort s) e0 -> P1 Γ t1 t2 T2 (eq_conv Σ Γ s T1 T2 t1 t2 e e0)) ->
       (forall (Γ : scontext) (n1 n2 : name) (A1 A2 B1 B2 : sterm) (s1 s2 : sort) (e : Σ;;; Γ |-i A1 = A2 : sSort s1),
        P1 Γ A1 A2 (sSort s1) e ->
        forall e0 : Σ;;; Γ,, svass n1 A1 |-i B1 = B2 : sSort s2,
        P1 (Γ,, svass n1 A1) B1 B2 (sSort s2) e0 ->
        P1 Γ (sProd n1 A1 B1) (sProd n2 A2 B2) (sSort (max_sort s1 s2)) (cong_Prod Σ Γ n1 n2 A1 A2 B1 B2 s1 s2 e e0)) ->
       (forall (Γ : scontext) (n1 n2 n' : name) (A1 A2 B1 B2 t1 t2 : sterm) (s1 s2 : sort) (e : Σ;;; Γ |-i A1 = A2 : sSort s1),
        P1 Γ A1 A2 (sSort s1) e ->
        forall e0 : Σ;;; Γ,, svass n1 A1 |-i B1 = B2 : sSort s2,
        P1 (Γ,, svass n1 A1) B1 B2 (sSort s2) e0 ->
        forall e1 : Σ;;; Γ,, svass n1 A1 |-i t1 = t2 : B1,
        P1 (Γ,, svass n1 A1) t1 t2 B1 e1 ->
        P1 Γ (sLambda n1 A1 B1 t1) (sLambda n2 A2 B2 t2) (sProd n' A1 B1)
          (cong_Lambda Σ Γ n1 n2 n' A1 A2 B1 B2 t1 t2 s1 s2 e e0 e1)) ->
       (forall (Γ : scontext) (n1 n2 : name) (s1 s2 : sort) (t1 t2 A1 A2 B1 B2 u1 u2 : sterm) (e : Σ;;; Γ |-i A1 = A2 : sSort s1),
        P1 Γ A1 A2 (sSort s1) e ->
        forall e0 : Σ;;; Γ,, svass n1 A1 |-i B1 = B2 : sSort s2,
        P1 (Γ,, svass n1 A1) B1 B2 (sSort s2) e0 ->
        forall e1 : Σ;;; Γ |-i t1 = t2 : sProd n1 A1 B1,
        P1 Γ t1 t2 (sProd n1 A1 B1) e1 ->
        forall e2 : Σ;;; Γ |-i u1 = u2 : A1,
        P1 Γ u1 u2 A1 e2 ->
        P1 Γ (sApp t1 n1 A1 B1 u1) (sApp t2 n2 A2 B2 u2) (B1 {0 := u1})
          (cong_App Σ Γ n1 n2 s1 s2 t1 t2 A1 A2 B1 B2 u1 u2 e e0 e1 e2)) ->
       (forall (Γ : scontext) (s : sort) (A1 A2 u1 u2 v1 v2 : sterm) (e : Σ;;; Γ |-i A1 = A2 : sSort s),
        P1 Γ A1 A2 (sSort s) e ->
        forall e0 : Σ;;; Γ |-i u1 = u2 : A1,
        P1 Γ u1 u2 A1 e0 ->
        forall e1 : Σ;;; Γ |-i v1 = v2 : A1,
        P1 Γ v1 v2 A1 e1 -> P1 Γ (sEq A1 u1 v1) (sEq A2 u2 v2) (sSort s) (cong_Eq Σ Γ s A1 A2 u1 u2 v1 v2 e e0 e1)) ->
       (forall (Γ : scontext) (s : sort) (A1 A2 u1 u2 : sterm) (e : Σ;;; Γ |-i A1 = A2 : sSort s),
        P1 Γ A1 A2 (sSort s) e ->
        forall e0 : Σ;;; Γ |-i u1 = u2 : A1,
        P1 Γ u1 u2 A1 e0 -> P1 Γ (sRefl A1 u1) (sRefl A2 u2) (sEq A1 u1 u1) (cong_Refl Σ Γ s A1 A2 u1 u2 e e0)) ->
       (forall (Γ : scontext) (nx ne : name) (s1 s2 : sort) (A1 A2 u1 u2 v1 v2 P2 P3 p1 p2 w1 w2 : sterm)
          (e : Σ;;; Γ |-i A1 = A2 : sSort s1),
        P1 Γ A1 A2 (sSort s1) e ->
        forall e0 : Σ;;; Γ |-i u1 = u2 : A1,
        P1 Γ u1 u2 A1 e0 ->
        forall e1 : Σ;;; Γ |-i v1 = v2 : A1,
        P1 Γ v1 v2 A1 e1 ->
        forall e2 : Σ;;; (Γ,, svass nx A1),, svass ne (sEq (lift0 1 A1) (lift0 1 u1) (sRel 0)) |-i P2 = P3 : sSort s2,
        P1 ((Γ,, svass nx A1),, svass ne (sEq (lift0 1 A1) (lift0 1 u1) (sRel 0))) P2 P3 (sSort s2) e2 ->
        forall e3 : Σ;;; Γ |-i p1 = p2 : sEq A1 u1 v1,
        P1 Γ p1 p2 (sEq A1 u1 v1) e3 ->
        forall e4 : Σ;;; Γ |-i w1 = w2 : (P2 {1 := u1}) {0 := sRefl A1 u1},
        P1 Γ w1 w2 ((P2 {1 := u1}) {0 := sRefl A1 u1}) e4 ->
        P1 Γ (sJ A1 u1 P2 w1 v1 p1) (sJ A2 u2 P3 w2 v2 p2) ((P2 {1 := v1}) {0 := p1})
          (cong_J Σ Γ nx ne s1 s2 A1 A2 u1 u2 v1 v2 P2 P3 p1 p2 w1 w2 e e0 e1 e2 e3 e4)) ->
       (forall (Γ : scontext) (s : sort) (A1 A2 B1 B2 p1 p2 t1 t2 : sterm) (e : Σ;;; Γ |-i A1 = A2 : sSort s),
        P1 Γ A1 A2 (sSort s) e ->
        forall e0 : Σ;;; Γ |-i B1 = B2 : sSort s,
        P1 Γ B1 B2 (sSort s) e0 ->
        forall e1 : Σ;;; Γ |-i p1 = p2 : sEq (sSort s) A1 B1,
        P1 Γ p1 p2 (sEq (sSort s) A1 B1) e1 ->
        forall e2 : Σ;;; Γ |-i t1 = t2 : A1,
        P1 Γ t1 t2 A1 e2 ->
        P1 Γ (sTransport A1 B1 p1 t1) (sTransport A2 B2 p2 t2) B1 (cong_Transport Σ Γ s A1 A2 B1 B2 p1 p2 t1 t2 e e0 e1 e2)) ->
       (forall (Γ : scontext) (A1 A2 a1 a2 B1 B2 b1 b2 : sterm) (s : sort) (e : Σ;;; Γ |-i A1 = A2 : sSort s),
        P1 Γ A1 A2 (sSort s) e ->
        forall e0 : Σ;;; Γ |-i B1 = B2 : sSort s,
        P1 Γ B1 B2 (sSort s) e0 ->
        forall e1 : Σ;;; Γ |-i a1 = a2 : A1,
        P1 Γ a1 a2 A1 e1 ->
        forall e2 : Σ;;; Γ |-i b1 = b2 : B1,
        P1 Γ b1 b2 B1 e2 ->
        P1 Γ (sHeq A1 a1 B1 b1) (sHeq A2 a2 B2 b2) (sSort (succ_sort s)) (cong_Heq Σ Γ A1 A2 a1 a2 B1 B2 b1 b2 s e e0 e1 e2)) ->
       (forall (Γ : scontext) (A1 B1 A2 B2 : sterm) (s : sort) (e : Σ;;; Γ |-i A1 = B1 : sSort s),
        P1 Γ A1 B1 (sSort s) e ->
        forall e0 : Σ;;; Γ |-i A2 = B2 : sSort s,
        P1 Γ A2 B2 (sSort s) e0 -> P1 Γ (sPack A1 A2) (sPack B1 B2) (sSort s) (cong_Pack Σ Γ A1 B1 A2 B2 s e e0)) ->
       (forall (Γ : scontext) (A u v p1 p2 : sterm) (s : sort) (e : Σ;;; Γ |-i p1 = p2 : sHeq A u A v),
        P1 Γ p1 p2 (sHeq A u A v) e ->
        forall t : Σ;;; Γ |-i A : sSort s,
        P Γ A (sSort s) t ->
        forall t0 : Σ;;; Γ |-i u : A,
        P Γ u A t0 ->
        forall t1 : Σ;;; Γ |-i v : A,
        P Γ v A t1 -> P1 Γ (sHeqToEq p1) (sHeqToEq p2) (sEq A u v) (cong_HeqToEq Σ Γ A u v p1 p2 s e t t0 t1)) ->
       (forall (Γ : scontext) (A1 A2 a1 a2 : sterm) (s : sort) (e : Σ;;; Γ |-i A1 = A2 : sSort s),
        P1 Γ A1 A2 (sSort s) e ->
        forall e0 : Σ;;; Γ |-i a1 = a2 : A1,
        P1 Γ a1 a2 A1 e0 -> P1 Γ (sHeqRefl A1 a1) (sHeqRefl A2 a2) (sHeq A1 a1 A1 a1) (cong_HeqRefl Σ Γ A1 A2 a1 a2 s e e0)) ->
       (forall (Γ : scontext) (A a B b p1 p2 : sterm) (s : sort) (t : Σ;;; Γ |-i A : sSort s),
        P Γ A (sSort s) t ->
        forall t0 : Σ;;; Γ |-i B : sSort s,
        P Γ B (sSort s) t0 ->
        forall t1 : Σ;;; Γ |-i a : A,
        P Γ a A t1 ->
        forall t2 : Σ;;; Γ |-i b : B,
        P Γ b B t2 ->
        forall e : Σ;;; Γ |-i p1 = p2 : sHeq A a B b,
        P1 Γ p1 p2 (sHeq A a B b) e -> P1 Γ (sHeqSym p1) (sHeqSym p2) (sHeq B b A a) (cong_HeqSym Σ Γ A a B b p1 p2 s t t0 t1 t2 e)) ->
       (forall (Γ : scontext) (A a B b C c p1 p2 q1 q2 : sterm) (s : sort) (t : Σ;;; Γ |-i A : sSort s),
        P Γ A (sSort s) t ->
        forall t0 : Σ;;; Γ |-i B : sSort s,
        P Γ B (sSort s) t0 ->
        forall t1 : Σ;;; Γ |-i C : sSort s,
        P Γ C (sSort s) t1 ->
        forall t2 : Σ;;; Γ |-i a : A,
        P Γ a A t2 ->
        forall t3 : Σ;;; Γ |-i b : B,
        P Γ b B t3 ->
        forall t4 : Σ;;; Γ |-i c : C,
        P Γ c C t4 ->
        forall e : Σ;;; Γ |-i p1 = p2 : sHeq A a B b,
        P1 Γ p1 p2 (sHeq A a B b) e ->
        forall e0 : Σ;;; Γ |-i q1 = q2 : sHeq B b C c,
        P1 Γ q1 q2 (sHeq B b C c) e0 ->
        P1 Γ (sHeqTrans p1 q1) (sHeqTrans p2 q2) (sHeq A a C c) (cong_HeqTrans Σ Γ A a B b C c p1 p2 q1 q2 s t t0 t1 t2 t3 t4 e e0)) ->
       (forall (Γ : scontext) (A B p1 p2 t1 t2 : sterm) (s : sort) (t : Σ;;; Γ |-i A : sSort s),
        P Γ A (sSort s) t ->
        forall t0 : Σ;;; Γ |-i B : sSort s,
        P Γ B (sSort s) t0 ->
        forall e : Σ;;; Γ |-i t1 = t2 : A,
        P1 Γ t1 t2 A e ->
        forall e0 : Σ;;; Γ |-i p1 = p2 : sEq (sSort s) A B,
        P1 Γ p1 p2 (sEq (sSort s) A B) e0 ->
        P1 Γ (sHeqTransport p1 t1) (sHeqTransport p2 t2) (sHeq A t1 B (sTransport A B p1 t1))
          (cong_HeqTransport Σ Γ A B p1 p2 t1 t2 s t t0 e e0)) ->
       (forall (Γ : scontext) (s z : sort) (nx ny np : name) (A1 A2 B1 B2 pA pB B1' B2' pA' pB' : sterm)
          (e : Σ;;; Γ |-i pA = pA' : sHeq (sSort s) A1 (sSort s) A2),
        P1 Γ pA pA' (sHeq (sSort s) A1 (sSort s) A2) e ->
        forall
          e0 : Σ;;; Γ,, svass np (sPack A1 A2) |-i pB = pB'
               : sHeq (sSort z) ((lift 1 1 B1) {0 := sProjT1 (sRel 0)}) (sSort z) ((lift 1 1 B2) {0 := sProjT2 (sRel 0)}),
        P1 (Γ,, svass np (sPack A1 A2)) pB pB'
          (sHeq (sSort z) ((lift 1 1 B1) {0 := sProjT1 (sRel 0)}) (sSort z) ((lift 1 1 B2) {0 := sProjT2 (sRel 0)})) e0 ->
        forall t : Σ;;; Γ |-i A1 : sSort s,
        P Γ A1 (sSort s) t ->
        forall t0 : Σ;;; Γ |-i A2 : sSort s,
        P Γ A2 (sSort s) t0 ->
        forall e1 : Σ;;; Γ,, svass nx A1 |-i B1 = B1' : sSort z,
        P1 (Γ,, svass nx A1) B1 B1' (sSort z) e1 ->
        forall e2 : Σ;;; Γ,, svass ny A2 |-i B2 = B2' : sSort z,
        P1 (Γ,, svass ny A2) B2 B2' (sSort z) e2 ->
        P1 Γ (sCongProd B1 B2 pA pB) (sCongProd B1' B2' pA' pB')
          (sHeq (sSort (max_sort s z)) (sProd nx A1 B1) (sSort (max_sort s z)) (sProd ny A2 B2))
          (cong_CongProd Σ Γ s z nx ny np A1 A2 B1 B2 pA pB B1' B2' pA' pB' e e0 t t0 e1 e2)) ->
       (forall (Γ : scontext) (s z : sort) (nx ny np : name) (A1 A2 B1 B2 t1 t2 pA pB pt B1' B2' t1' t2' pA' pB' pt' : sterm)
          (e : Σ;;; Γ |-i pA = pA' : sHeq (sSort s) A1 (sSort s) A2),
        P1 Γ pA pA' (sHeq (sSort s) A1 (sSort s) A2) e ->
        forall
          e0 : Σ;;; Γ,, svass np (sPack A1 A2) |-i pB = pB'
               : sHeq (sSort z) ((lift 1 1 B1) {0 := sProjT1 (sRel 0)}) (sSort z) ((lift 1 1 B2) {0 := sProjT2 (sRel 0)}),
        P1 (Γ,, svass np (sPack A1 A2)) pB pB'
          (sHeq (sSort z) ((lift 1 1 B1) {0 := sProjT1 (sRel 0)}) (sSort z) ((lift 1 1 B2) {0 := sProjT2 (sRel 0)})) e0 ->
        forall
          e1 : Σ;;; Γ,, svass np (sPack A1 A2) |-i pt = pt'
               : sHeq ((lift 1 1 B1) {0 := sProjT1 (sRel 0)}) ((lift 1 1 t1) {0 := sProjT1 (sRel 0)})
                   ((lift 1 1 B2) {0 := sProjT2 (sRel 0)}) ((lift 1 1 t2) {0 := sProjT2 (sRel 0)}),
        P1 (Γ,, svass np (sPack A1 A2)) pt pt'
          (sHeq ((lift 1 1 B1) {0 := sProjT1 (sRel 0)}) ((lift 1 1 t1) {0 := sProjT1 (sRel 0)})
             ((lift 1 1 B2) {0 := sProjT2 (sRel 0)}) ((lift 1 1 t2) {0 := sProjT2 (sRel 0)})) e1 ->
        forall t : Σ;;; Γ |-i A1 : sSort s,
        P Γ A1 (sSort s) t ->
        forall t0 : Σ;;; Γ |-i A2 : sSort s,
        P Γ A2 (sSort s) t0 ->
        forall e2 : Σ;;; Γ,, svass nx A1 |-i B1 = B1' : sSort z,
        P1 (Γ,, svass nx A1) B1 B1' (sSort z) e2 ->
        forall e3 : Σ;;; Γ,, svass ny A2 |-i B2 = B2' : sSort z,
        P1 (Γ,, svass ny A2) B2 B2' (sSort z) e3 ->
        forall e4 : Σ;;; Γ,, svass nx A1 |-i t1 = t1' : B1,
        P1 (Γ,, svass nx A1) t1 t1' B1 e4 ->
        forall e5 : Σ;;; Γ,, svass ny A2 |-i t2 = t2' : B2,
        P1 (Γ,, svass ny A2) t2 t2' B2 e5 ->
        P1 Γ (sCongLambda B1 B2 t1 t2 pA pB pt) (sCongLambda B1' B2' t1' t2' pA' pB' pt')
          (sHeq (sProd nx A1 B1) (sLambda nx A1 B1 t1) (sProd ny A2 B2) (sLambda ny A2 B2 t2))
          (cong_CongLambda Σ Γ s z nx ny np A1 A2 B1 B2 t1 t2 pA pB pt B1' B2' t1' t2' pA' pB' pt' e e0 e1 t t0 e2 e3 e4 e5)) ->
       (forall (Γ : scontext) (s z : sort) (nx ny np : name) (A1 A2 B1 B2 u1 u2 v1 v2 pA pB pu pv B1' B2' pu' pA' pB' pv' : sterm)
          (e : Σ;;; Γ |-i pA = pA' : sHeq (sSort s) A1 (sSort s) A2),
        P1 Γ pA pA' (sHeq (sSort s) A1 (sSort s) A2) e ->
        forall
          e0 : Σ;;; Γ,, svass np (sPack A1 A2) |-i pB = pB'
               : sHeq (sSort z) ((lift 1 1 B1) {0 := sProjT1 (sRel 0)}) (sSort z) ((lift 1 1 B2) {0 := sProjT2 (sRel 0)}),
        P1 (Γ,, svass np (sPack A1 A2)) pB pB'
          (sHeq (sSort z) ((lift 1 1 B1) {0 := sProjT1 (sRel 0)}) (sSort z) ((lift 1 1 B2) {0 := sProjT2 (sRel 0)})) e0 ->
        forall e1 : Σ;;; Γ |-i pu = pu' : sHeq (sProd nx A1 B1) u1 (sProd ny A2 B2) u2,
        P1 Γ pu pu' (sHeq (sProd nx A1 B1) u1 (sProd ny A2 B2) u2) e1 ->
        forall e2 : Σ;;; Γ |-i pv = pv' : sHeq A1 v1 A2 v2,
        P1 Γ pv pv' (sHeq A1 v1 A2 v2) e2 ->
        forall t : Σ;;; Γ |-i A1 : sSort s,
        P Γ A1 (sSort s) t ->
        forall t0 : Σ;;; Γ |-i A2 : sSort s,
        P Γ A2 (sSort s) t0 ->
        forall e3 : Σ;;; Γ,, svass nx A1 |-i B1 = B1' : sSort z,
        P1 (Γ,, svass nx A1) B1 B1' (sSort z) e3 ->
        forall e4 : Σ;;; Γ,, svass ny A2 |-i B2 = B2' : sSort z,
        P1 (Γ,, svass ny A2) B2 B2' (sSort z) e4 ->
        forall t1 : Σ;;; Γ |-i u1 : sProd nx A1 B1,
        P Γ u1 (sProd nx A1 B1) t1 ->
        forall t2 : Σ;;; Γ |-i u2 : sProd ny A2 B2,
        P Γ u2 (sProd ny A2 B2) t2 ->
        forall t3 : Σ;;; Γ |-i v1 : A1,
        P Γ v1 A1 t3 ->
        forall t4 : Σ;;; Γ |-i v2 : A2,
        P Γ v2 A2 t4 ->
        P1 Γ (sCongApp B1 B2 pu pA pB pv) (sCongApp B1' B2' pu' pA' pB' pv')
          (sHeq (B1 {0 := v1}) (sApp u1 nx A1 B1 v1) (B2 {0 := v2}) (sApp u2 ny A2 B2 v2))
          (cong_CongApp Σ Γ s z nx ny np A1 A2 B1 B2 u1 u2 v1 v2 pA pB pu pv B1' B2' pu' pA' pB' pv' e e0 e1 e2 t t0 e3 e4 t1 t2 t3
             t4)) ->
       (forall (Γ : scontext) (s : sort) (A1 A2 u1 u2 v1 v2 pA pu pv pA' pu' pv' : sterm)
          (e : Σ;;; Γ |-i pA = pA' : sHeq (sSort s) A1 (sSort s) A2),
        P1 Γ pA pA' (sHeq (sSort s) A1 (sSort s) A2) e ->
        forall e0 : Σ;;; Γ |-i pu = pu' : sHeq A1 u1 A2 u2,
        P1 Γ pu pu' (sHeq A1 u1 A2 u2) e0 ->
        forall e1 : Σ;;; Γ |-i pv = pv' : sHeq A1 v1 A2 v2,
        P1 Γ pv pv' (sHeq A1 v1 A2 v2) e1 ->
        forall t : Σ;;; Γ |-i A1 : sSort s,
        P Γ A1 (sSort s) t ->
        forall t0 : Σ;;; Γ |-i A2 : sSort s,
        P Γ A2 (sSort s) t0 ->
        forall t1 : Σ;;; Γ |-i u1 : A1,
        P Γ u1 A1 t1 ->
        forall t2 : Σ;;; Γ |-i u2 : A2,
        P Γ u2 A2 t2 ->
        forall t3 : Σ;;; Γ |-i v1 : A1,
        P Γ v1 A1 t3 ->
        forall t4 : Σ;;; Γ |-i v2 : A2,
        P Γ v2 A2 t4 ->
        P1 Γ (sCongEq pA pu pv) (sCongEq pA' pu' pv') (sHeq (sSort s) (sEq A1 u1 v1) (sSort s) (sEq A2 u2 v2))
          (cong_CongEq Σ Γ s A1 A2 u1 u2 v1 v2 pA pu pv pA' pu' pv' e e0 e1 t t0 t1 t2 t3 t4)) ->
       (forall (Γ : scontext) (s : sort) (A1 A2 u1 u2 pA pu pA' pu' : sterm)
          (e : Σ;;; Γ |-i pA = pA' : sHeq (sSort s) A1 (sSort s) A2),
        P1 Γ pA pA' (sHeq (sSort s) A1 (sSort s) A2) e ->
        forall e0 : Σ;;; Γ |-i pu = pu' : sHeq A1 u1 A2 u2,
        P1 Γ pu pu' (sHeq A1 u1 A2 u2) e0 ->
        forall t : Σ;;; Γ |-i A1 : sSort s,
        P Γ A1 (sSort s) t ->
        forall t0 : Σ;;; Γ |-i A2 : sSort s,
        P Γ A2 (sSort s) t0 ->
        forall t1 : Σ;;; Γ |-i u1 : A1,
        P Γ u1 A1 t1 ->
        forall t2 : Σ;;; Γ |-i u2 : A2,
        P Γ u2 A2 t2 ->
        P1 Γ (sCongRefl pA pu) (sCongRefl pA' pu') (sHeq (sEq A1 u1 u1) (sRefl A1 u1) (sEq A2 u2 u2) (sRefl A2 u2))
          (cong_CongRefl Σ Γ s A1 A2 u1 u2 pA pu pA' pu' e e0 t t0 t1 t2)) ->
       (forall (Γ : scontext) (A u v p1 p2 : sterm) (s : sort) (e : Σ;;; Γ |-i p1 = p2 : sEq A u v),
        P1 Γ p1 p2 (sEq A u v) e ->
        forall t : Σ;;; Γ |-i A : sSort s,
        P Γ A (sSort s) t ->
        forall t0 : Σ;;; Γ |-i u : A,
        P Γ u A t0 ->
        forall t1 : Σ;;; Γ |-i v : A,
        P Γ v A t1 -> P1 Γ (sEqToHeq p1) (sEqToHeq p2) (sHeq A u A v) (cong_EqToHeq Σ Γ A u v p1 p2 s e t t0 t1)) ->
       (forall (Γ : scontext) (A u B v p1 p2 : sterm) (s : sort) (e : Σ;;; Γ |-i p1 = p2 : sHeq A u B v),
        P1 Γ p1 p2 (sHeq A u B v) e ->
        forall t : Σ;;; Γ |-i A : sSort s,
        P Γ A (sSort s) t ->
        forall t0 : Σ;;; Γ |-i B : sSort s,
        P Γ B (sSort s) t0 ->
        forall t1 : Σ;;; Γ |-i u : A,
        P Γ u A t1 ->
        forall t2 : Σ;;; Γ |-i v : B,
        P Γ v B t2 -> P1 Γ (sHeqTypeEq p1) (sHeqTypeEq p2) (sEq (sSort s) A B) (cong_HeqTypeEq Σ Γ A u B v p1 p2 s e t t0 t1 t2)) ->
       (forall (Γ : scontext) (A1 A2 p1 p2 : sterm) (s : sort) (t : Σ;;; Γ |-i A1 : sSort s),
        P Γ A1 (sSort s) t ->
        forall t0 : Σ;;; Γ |-i A2 : sSort s,
        P Γ A2 (sSort s) t0 ->
        forall e : Σ;;; Γ |-i p1 = p2 : sPack A1 A2,
        P1 Γ p1 p2 (sPack A1 A2) e -> P1 Γ (sProjT1 p1) (sProjT1 p2) A1 (cong_ProjT1 Σ Γ A1 A2 p1 p2 s t t0 e)) ->
       (forall (Γ : scontext) (A1 A2 p1 p2 : sterm) (s : sort) (t : Σ;;; Γ |-i A1 : sSort s),
        P Γ A1 (sSort s) t ->
        forall t0 : Σ;;; Γ |-i A2 : sSort s,
        P Γ A2 (sSort s) t0 ->
        forall e : Σ;;; Γ |-i p1 = p2 : sPack A1 A2,
        P1 Γ p1 p2 (sPack A1 A2) e -> P1 Γ (sProjT2 p1) (sProjT2 p2) A2 (cong_ProjT2 Σ Γ A1 A2 p1 p2 s t t0 e)) ->
       (forall (Γ : scontext) (A1 A2 p1 p2 : sterm) (s : sort) (t : Σ;;; Γ |-i A1 : sSort s),
        P Γ A1 (sSort s) t ->
        forall t0 : Σ;;; Γ |-i A2 : sSort s,
        P Γ A2 (sSort s) t0 ->
        forall e : Σ;;; Γ |-i p1 = p2 : sPack A1 A2,
        P1 Γ p1 p2 (sPack A1 A2) e ->
        P1 Γ (sProjTe p1) (sProjTe p2) (sHeq A1 (sProjT1 p1) A2 (sProjT2 p1)) (cong_ProjTe Σ Γ A1 A2 p1 p2 s t t0 e)) ->
       (forall (Γ : scontext) (s : sort) (A u : sterm) (t : Σ;;; Γ |-i A : sSort s),
        P Γ A (sSort s) t ->
        forall t0 : Σ;;; Γ |-i u : A,
        P Γ u A t0 -> P1 Γ (sHeqToEq (sHeqRefl A u)) (sRefl A u) (sEq A u u) (eq_HeqToEqRefl Σ Γ s A u t t0)) ->
       (forall (s : scontext) (s0 s1 : sterm) (t : Σ;;; s |-i s0 : s1), P s s0 s1 t) *
       (forall (s : scontext) (w : wf Σ s), P0 s w) *
       (forall (s : scontext) (s0 s1 s2 : sterm) (e : Σ;;; s |-i s0 = s1 : s2), P1 s s0 s1 s2 e).
Proof.
  intros; repeat split ; [
  eapply typing_ind' | eapply wf_ind' | eapply eq_term_ind' ]; eauto.
Defined.

(* Lemma uniqueness : *)
(*   forall {Σ Γ A B u}, *)
(*     Σ ;;; Γ |-i u : A -> *)
(*     Σ ;;; Γ |-i u : B -> *)
(*     ∑ s, Σ ;;; Γ |-i A = B : sSort s. *)
(* Proof. *)
(*   intros Σ Γ A B u h1. revert B. revert Γ u A h1. *)
(*   match goal with *)
(*   | |- ?g => assert (P : g * (forall s : scontext, wf Σ s -> ()) * *)
(*   (forall (Γ : scontext) (A B s : sterm) (e : Σ;;; Γ |-i A = B : s), *)
(*          forall C s' : sterm, Σ;;; Γ |-i A = C : s' -> ∑ s_ : sort, Σ;;; Γ |-i s = s' : sSort s_)) *)
(*   end. *)
(*   - eapply typing_all with (Σ := Σ) (P0 := fun _ _ => unit)  *)
(*                            (P1 := fun (Γ : scontext) (A B s : sterm) (e : Σ;;; Γ |-i A = B : s) => *)
(*                                     forall C s' : sterm, Σ;;; Γ |-i A = C : s' -> ∑ s_ : sort, Σ;;; Γ |-i s = s' : sSort s_)  *)
(*                            (P := fun (Γ : scontext) (u A : sterm) (_ : Σ;;; Γ |-i u : A) =>  *)
(*                                    forall B : sterm, Σ;;; Γ |-i u : B -> ∑ s : sort, Σ;;; Γ |-i A = B : sSort s). *)
(*     Focus 2.  *)
(*     intros. inversion X. admit.  *)
(*     Focus 29.  *)
(* intros. specialize (X B0 X2). destruct X as [ss X]. exists ss. specialize (X1 B0 (sSort ss) X). admit.  *)
(* Focus 45. *)
(*     + intros Γ n w H isdecl B h. *)
(*       eapply typing_all with (Σ := Σ) (P0 := fun _ _ => unit) (P1 := fun (Γ : scontext) (A B s : sterm) (e : Σ;;; Γ |-i A = B : s) => *)
(*          forall C s' : sterm, Σ;;; Γ |-i B = C : s' -> ∑ s_ : sort, Σ;;; Γ |-i s = s' : sSort s_) (P := fun (Γ : scontext) (u A : sterm) (_ : Σ;;; Γ |-i u : A) => forall B : sterm, Σ;;; Γ |-i u : B -> ∑ s : sort, Σ;;; Γ |-i A = B : sSort s). *)
