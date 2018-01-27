From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import Ast SAst Typing SLiftSubst SCommon.

Reserved Notation " Σ ;;; Γ '|-i' t : T " (at level 50, Γ, t, T at next level).
Reserved Notation " Σ ;;; Γ '|-i' t = u : T " (at level 50, Γ, t, u, T at next level).

Open Scope s_scope.

Inductive typing (Σ : global_context) : scontext -> sterm -> sterm -> Type :=
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
    Σ ;;; Γ |-i sCongProd pA pB :
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
    Σ ;;; Γ |-i sCongLambda pA pB pt :
               sHeq (sProd nx A1 B1) (sLambda nx A1 B1 t1)
                    (sProd ny A2 B2) (sLambda ny A2 B2 t2)

| type_CongApp Γ s z nx ny np A1 A2 B1 B2 u1 u2 v1 v2 pA pB pu pv :
    Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2 ->
    Σ ;;; Γ ,, svass np (sPack A1 A2)
    |-i pB : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                 (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ |-i pu : sHeq (sProd nx A1 B1) u2 (sProd ny A2 B2) u2 ->
    Σ ;;; Γ |-i pv : sHeq A1 v2 A2 v2 ->
    Σ ;;; Γ |-i A1 : sSort s ->
    Σ ;;; Γ |-i A2 : sSort s ->
    Σ ;;; Γ ,, svass nx A1 |-i B1 : sSort z ->
    Σ ;;; Γ ,, svass ny A2 |-i B2 : sSort z ->
    Σ ;;; Γ |-i u1 : sProd nx A1 B1 ->
    Σ ;;; Γ |-i u2 : sProd ny A2 B2 ->
    Σ ;;; Γ |-i v1 : A1 ->
    Σ ;;; Γ |-i v2 : A2 ->
    Σ ;;; Γ |-i sCongApp pu pA pB pv :
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

| type_conv Γ t A B s :
    Σ ;;; Γ |-i t : A ->
    Σ ;;; Γ |-i B : sSort s ->
    Σ ;;; Γ |-i A = B : sSort s ->
    Σ ;;; Γ |-i t : B

where " Σ ;;; Γ '|-i' t : T " := (@typing Σ Γ t T) : i_scope

with wf (Σ : global_context) : scontext -> Type :=
| wf_nil :
    wf Σ nil

| wf_snoc Γ x A :
    wf Σ Γ ->
    (∑ s, Σ ;;; Γ |-i A : sSort s) ->
    wf Σ (Γ ,, svass x A)

with eq_term (Σ : global_context) : scontext -> sterm -> sterm -> sterm -> Type :=
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

where " Σ ;;; Γ '|-i' t = u : T " := (@eq_term Σ Γ t u T) : i_scope.

(* Lemmata about typing *)

Open Scope type_scope.
Open Scope i_scope.

Lemma typing_wf :
  forall {Σ Γ t T},
    Σ ;;; Γ |-i t : T ->
    wf Σ Γ.
Proof.
  intros Σ Γ t T H. induction H ; easy.
Defined.

Lemma typing_lift01 :
  forall {Σ Γ t A x B s},
    Σ ;;; Γ |-i t : A ->
    Σ ;;; Γ |-i B : sSort s ->
    Σ ;;; Γ ,, svass x B |-i lift0 1 t : lift0 1 A.
Admitted.

Lemma typing_lift02 :
  forall {Σ Γ t A x B s y C s'},
    Σ ;;; Γ |-i t : A ->
    Σ ;;; Γ |-i B : sSort s ->
    Σ ;;; Γ ,, svass x B |-i C : sSort s' ->
    Σ ;;; Γ ,, svass x B ,, svass y C |-i lift0 2 t : lift0 2 A.
Proof.
  intros Σ Γ t A x B s y C s' ht hB hC.
  assert (eq : forall t, lift0 2 t = lift0 1 (lift0 1 t)).
  { intro u. rewrite lift_lift. reflexivity. }
  rewrite !eq. eapply typing_lift01.
  - eapply typing_lift01  ; eassumption.
  - eassumption.
Defined.

Lemma typing_subst :
  forall {Σ Γ t A B u n},
    Σ ;;; Γ ,, svass n A |-i t : B ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i t{ 0 := u } : B{ 0 := u }.
Admitted.

Lemma typing_subst2 :
  forall {Σ Γ t A B C na nb u v},
    Σ ;;; Γ ,, svass na A ,, svass nb B |-i t : C ->
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i v : B{ 0 := u } ->
    Σ ;;; Γ |-i t{ 1 := u }{ 0 := v } : C{ 1 := u }{ 0 := v }.
Admitted.

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
    destruct s.
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
    Σ ;;; Γ |-i t : T ->
    ∑ s, Σ ;;; Γ |-i T : sSort s.
Proof.
  intros Σ Γ t T H.
  induction H.
  - revert n isdecl. induction w ; intros n isdecl.
    + cbn in isdecl. easy.
    + destruct n.
      * cbn. destruct s as [s h].
        exists s. change (sSort s) with (lift0 1 (sSort s)).
        eapply typing_lift01.
        -- assumption.
        -- eassumption.
      * assert (isdecl' : n < #|Γ|).
        -- auto with arith.
        -- destruct (IHw n isdecl') as [s' hh].
           destruct s as [s hs].
           exists s'. change (sSort s') with (lift0 1 (sSort s')).
           (* Take out as a lemma? *)
           assert (eq : forall t, lift0 (S (S n)) t = lift0 1 (lift0 (S n) t)).
           { intro t. rewrite lift_lift. reflexivity. }
           rewrite eq. clear eq.
           eapply typing_lift01.
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
    eapply typing_subst.
    + eassumption.
    + assumption.
  - exists (succ_sort s). apply type_Sort. apply (typing_wf H).
  - exists s. now apply type_Eq.
  - exists s2.
    change (sSort s2) with ((sSort s2){1 := v}{0 := p}).
    eapply typing_subst2.
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
  - exists (succ_sort s). apply type_Sort. apply (typing_wf H).
  - exists s. assumption.
  - exists s. assumption.
  - exists (succ_sort s). apply type_Heq ; try assumption.
    + eapply type_ProjT1 ; eassumption.
    + eapply @type_ProjT2 with (A1 := A1) ; eassumption.
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
      * apply eqctx_refl. now apply (typing_wf t1).
      * eassumption.
  - eapply type_conv.
    + econstructor.
      * eassumption.
      * eapply ctx_conv ; [ eassumption |].
        econstructor.
        -- eapply eqctx_refl. now apply (typing_wf t5).
        -- eassumption.
      * eapply ctx_conv.
        -- eapply type_conv ; eassumption.
        -- econstructor.
           ++ apply eqctx_refl. now apply (typing_wf t5).
           ++ eassumption.
    + econstructor.
      * eassumption.
      * eapply ctx_conv ; [ eassumption |].
        econstructor.
        -- apply eqctx_refl. now apply (typing_wf t5).
        -- apply eq_reflexivity. eassumption.
    + apply eq_symmetry. apply cong_Prod.
      * assumption.
      * eapply eqctx_conv ; [ eassumption |].
        econstructor.
        -- apply eqctx_refl. now apply (typing_wf t5).
        -- apply eq_reflexivity. eassumption.
  - econstructor.
    + econstructor.
      * eassumption.
      * eapply ctx_conv ; [ eassumption |].
        econstructor.
        -- apply eqctx_refl. now apply (typing_wf t7).
        -- eassumption.
      * econstructor.
        -- eassumption.
        -- econstructor.
           ++ eassumption.
           ++ eapply ctx_conv ; [ eassumption |].
              econstructor.
              ** apply eqctx_refl. now apply (typing_wf t7).
              ** eassumption.
        -- eapply cong_Prod ; eassumption.
      * econstructor ; eassumption.
    + instantiate (1 := s2).
      change (sSort s2) with ((sSort s2){ 0 := u1 }).
      eapply typing_subst ; eassumption.
    + (* We need a substitution lemma for conversion *)
      admit.
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
        -- apply eqctx_refl. now apply (typing_wf t7).
        -- eassumption.
      * eapply cong_Eq.
        -- (* We need conversion of lifts! *)
           admit.
        -- (* We need conversion of lifts! *)
           admit.
        -- apply eq_reflexivity.
           eapply type_conv ; [ eapply type_Rel | .. ].
           ++ econstructor.
              ** now apply (typing_wf t7).
              ** eexists ; eassumption.
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
      *
Admitted.

Lemma sorts_in_sort :
  forall {Σ Γ s1 s2 s},
    Σ ;;; Γ |-i sSort s1 : sSort s ->
    Σ ;;; Γ |-i sSort s2 : sSort s ->
    Σ ;;; Γ |-i sSort s1 = sSort s2 : sSort s.
Proof.
Admitted.

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

Lemma uniqueness :
  forall {Σ Γ A B u},
    Σ ;;; Γ |-i u : A ->
    Σ ;;; Γ |-i u : B ->
    ∑ s, Σ ;;; Γ |-i A = B : sSort s.
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
    destruct (istype_type H) as [s hs].
    exists s. apply eq_reflexivity. eassumption.
  - destruct (IHh1 n (eq_refl _)) as [isdecl [s' h]].
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

  - specialize (IHh1 s (eq_refl _)). eapply eq_transitivity.
    + eassumption.
    + destruct (eq_typing e) as [hAs0 _].
      destruct (eq_typing IHh1) as [_ hAss].
      destruct (uniqueness hAs0 hAss) as [? ?].
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

  - destruct (IHh1 n A B (eq_refl _)) as [s1 [s2 [[? ?] ?]]].
    exists s1, s2. repeat split.
    + assumption.
    + assumption.
    + eapply eq_transitivity.
      * eassumption.
      * destruct (eq_typing e) as [hAs _].
        destruct (eq_typing e0) as [_ hAsm].
        destruct (uniqueness hAs hAsm).
        eapply eq_conv ; eassumption.
Defined.

(* Lemma inversionLambda *)

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

  - destruct (IHtyping1 t n A B u (eq_refl _)) as [s1 [s2 [[[[? ?] ?] ?] ?]]].
    exists s1, s2. repeat split ; try easy.
    eapply eq_transitivity.
    + eassumption.
    + destruct (eq_typing e) as [hAs _].
      destruct (eq_typing e0) as [_ hAs2].
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
  - destruct (IHh1 A u v (eq_refl _)) as [s' [[[hA hu] hv] heq]].
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

  - destruct (IHh1 _ _ eq_refl) as [s' [[hA hu] eq]].
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

  - destruct (IHtyping1 A u P w v p (eq_refl _))
      as [s1 [s2 [nx [ne [[[[[[? ?] ?] ?] ?] ?] ?]]]]].
    exists s1, s2, nx, ne. repeat split ; try easy.
    eapply eq_transitivity.
    + eassumption.
    + destruct (eq_typing e) as [hAs _].
      destruct (eq_typing e0) as [_ hAs2].
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

  - destruct (IHh1 _ _ _ _ eq_refl) as [s' [[[[? ?] ?] ?] ?]].
    exists s'. repeat split ; try easy.
    eapply eq_transitivity.
    + eassumption.
    + destruct (eq_typing e) as [hA1 _].
      destruct (eq_typing e0) as [_ hA2].
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

  - destruct (IHh1 _ _ _ _ eq_refl) as [s' [[[[? ?] ?] ?] ?]].
    exists s'. repeat split ; try easy.
    eapply eq_transitivity.
    + eassumption.
    + destruct (eq_typing e) as [i1 _].
      destruct (eq_typing e0) as [_ i2].
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

  - destruct (IHh1 _ _ eq_refl) as [s' [[? ?] ?]].
    exists s'. repeat split ; try easy.
    eapply eq_transitivity.
    + eassumption.
    + destruct (eq_typing e) as [i1 _].
      destruct (eq_typing e0) as [_ i2].
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
    Σ ;;; Γ |-i sCongProd pA pB :
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

Lemma type_CongProd' :
  forall {Σ Γ s1 s2 z1 z2 nx ny np A1 A2 B1 B2 pA pB},
    Σ ;;; Γ |-i pA : sHeq (sSort s1) A1 (sSort s2) A2 ->
    Σ ;;; Γ ,, svass np (sPack A1 A2)
    |-i pB : sHeq (sSort z1) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                (sSort z2) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ ,, svass nx A1 |-i B1 : sSort z1 ->
    Σ ;;; Γ ,, svass ny A2 |-i B2 : sSort z2 ->
    Σ ;;; Γ |-i sCongProd pA pB :
    sHeq (sSort (max_sort s1 z1)) (sProd nx A1 B1)
         (sSort (max_sort s2 z2)) (sProd ny A2 B2).
Proof.
  intros Σ Γ s1 s2 z1 z2 nx ny np A1 A2 B1 B2 pA pB hpA hpB hB1 hB2.
  assert (hs : ∑ ss, Σ ;;; Γ |-i sSort s1 = sSort s2 : sSort ss).
  { destruct (istype_type hpA) as [? ipA].
    destruct (inversionHeq ipA) as [? [[[[e1 e2] ?] ?] ?]].
    pose proof (sorts_in_sort e1 e2).
    eexists. eassumption.
  }
  destruct hs.
  assert (hz : ∑ zz, Σ;;; Γ,, svass ny A2 |-i sSort z2 = sSort z1 : sSort zz).
  { destruct (istype_type hpB) as [? ipB].
    destruct (inversionHeq ipB) as [? [[[[f1 f2] ?] ?] ?]].
    pose proof (sorts_in_sort f2 f1).
    eexists. eapply strengthen_sort_eq.
    - eassumption.
    - eapply typing_wf. eassumption.
  }
  destruct hz.
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
    + destruct (uniqueness hP1 hP2).
      eapply eq_conv.
      * eassumption.
      * eapply eq_symmetry. eapply inversionSort.
        apply (eq_typing e1).
    + assumption.
    + destruct (istype_type hpA) as [? ipA].
      destruct (inversionHeq ipA) as [? [[[[e1 e2] ?] ?] ?]].
      apply type_Prod.
      * eapply type_conv'.
        -- eassumption.
        -- eapply eq_symmetry. eassumption.
      * eapply type_conv' ; eassumption.
Defined.

(* TODO later *)
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
    Σ ;;; Γ |-i sCongLambda pA pB pt :
               sHeq (sProd nx A1 B1) (sLambda nx A1 B1 t1)
                    (sProd ny A2 B2) (sLambda ny A2 B2 t2).
Admitted.

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
    Σ ;;; Γ |-i sCongLambda pA pB pt :
               sHeq (sProd nx A1 B1) (sLambda nx A1 B1 t1)
                    (sProd ny A2 B2) (sLambda ny A2 B2 t2).
Admitted.

Lemma type_CongApp'' :
  forall {Σ Γ s z nx ny np A1 A2 B1 B2 u1 u2 v1 v2 pA pB pu pv},
    Σ ;;; Γ |-i pA : sHeq (sSort s) A1 (sSort s) A2 ->
    Σ ;;; Γ ,, svass np (sPack A1 A2)
    |-i pB : sHeq (sSort z) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                 (sSort z) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ |-i pu : sHeq (sProd nx A1 B1) u2 (sProd ny A2 B2) u2 ->
    Σ ;;; Γ |-i pv : sHeq A1 v2 A2 v2 ->
    Σ ;;; Γ ,, svass nx A1 |-i B1 : sSort z ->
    Σ ;;; Γ ,, svass ny A2 |-i B2 : sSort z ->
    Σ ;;; Γ |-i sCongApp pu pA pB pv :
               sHeq (B1{0 := v1}) (sApp u1 nx A1 B1 v1)
                    (B2{0 := v2}) (sApp u2 ny A2 B2 v2).
Admitted.

Lemma type_CongApp' :
  forall {Σ Γ s1 s2 z1 z2 nx ny np A1 A2 B1 B2 u1 u2 v1 v2 pA pB pu pv},
    Σ ;;; Γ |-i pA : sHeq (sSort s1) A1 (sSort s2) A2 ->
    Σ ;;; Γ ,, svass np (sPack A1 A2)
    |-i pB : sHeq (sSort z1) ((lift 1 1 B1){ 0 := sProjT1 (sRel 0) })
                 (sSort z2) ((lift 1 1 B2){ 0 := sProjT2 (sRel 0) }) ->
    Σ ;;; Γ |-i pu : sHeq (sProd nx A1 B1) u2 (sProd ny A2 B2) u2 ->
    Σ ;;; Γ |-i pv : sHeq A1 v2 A2 v2 ->
    Σ ;;; Γ ,, svass nx A1 |-i B1 : sSort z1 ->
    Σ ;;; Γ ,, svass ny A2 |-i B2 : sSort z2 ->
    Σ ;;; Γ |-i sCongApp pu pA pB pv :
               sHeq (B1{0 := v1}) (sApp u1 nx A1 B1 v1)
                    (B2{0 := v2}) (sApp u2 ny A2 B2 v2).
Admitted.

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
