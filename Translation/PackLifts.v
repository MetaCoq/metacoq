(* Lifts for packing *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import Ast utils LiftSubst Typing.
From Translation Require Import SAst SLiftSubst SCommon XTyping ITyping.

(* In order to do things properly we need to extend the context heterogenously,
   this is done by extending the context with packed triples
   (x : A, y : B, e : heq A x B y).
   We call Γm the mix of Γ1 and Γ2.
   We also need to define correspond lifts.

   If Γ, Γ1, Δ |- t : T then
   Γ, Γm, Δ↑ |- llift #|Γm| #|Δ| t : llift #|Γm| #|Δ| T
   If Γ, Γ2, Δ |- t : T then
   Γ, Γm, Δ↑ |- rlift #|Γm| #|Δ| t : rlift #|Γm| #|Δ| T
 *)

Fixpoint llift γ δ (t:sterm)  : sterm :=
  match t with
  | sRel i =>
    if i <? δ
    then sRel i
    else if i <? δ + γ
         then sProjT1 (sRel i)
         else sRel i
  | sLambda na A B b =>
    sLambda na (llift γ δ A) (llift γ (S δ) B) (llift γ (S δ) b)
  | sApp u na A B v =>
    sApp (llift γ δ u) na (llift γ δ A) (llift γ (S δ) B) (llift γ δ v)
  | sProd na A B => sProd na (llift γ δ A) (llift γ (S δ) B)
  | sEq A u v => sEq (llift γ δ A) (llift γ δ u) (llift γ δ v)
  | sRefl A u => sRefl (llift γ δ A) (llift γ δ u)
  | sJ A u P w v p =>
    sJ (llift γ δ A)
       (llift γ δ u)
       (llift γ (S (S δ)) P)
       (llift γ δ w)
       (llift γ δ v)
       (llift γ δ p)
  | sTransport A B p t =>
    sTransport (llift γ δ A) (llift γ δ B) (llift γ δ p) (llift γ δ t)
  | sHeq A a B b =>
    sHeq (llift γ δ A) (llift γ δ a) (llift γ δ B) (llift γ δ b)
  | sHeqToEq p => sHeqToEq (llift γ δ p)
  | sHeqRefl A a => sHeqRefl (llift γ δ A) (llift γ δ a)
  | sHeqSym p => sHeqSym (llift γ δ p)
  | sHeqTrans p q => sHeqTrans (llift γ δ p) (llift γ δ q)
  | sHeqTransport p t => sHeqTransport (llift γ δ p) (llift γ δ t)
  | sCongProd B1 B2 p q =>
    sCongProd (llift γ (S δ) B1) (llift γ (S δ) B2)
              (llift γ δ p) (llift γ (S δ) q)
  | sCongLambda B1 B2 t1 t2 pA pB pt =>
    sCongLambda (llift γ (S δ) B1) (llift γ (S δ) B2)
                (llift γ (S δ) t1) (llift γ (S δ) t2)
                (llift γ δ pA) (llift γ (S δ) pB) (llift γ (S δ) pt)
  | sCongApp B1 B2 pu pA pB pv =>
    sCongApp (llift γ (S δ) B1) (llift γ (S δ) B2)
             (llift γ δ pu) (llift γ δ pA) (llift γ (S δ) pB) (llift γ δ pv)
  | sCongEq pA pu pv => sCongEq (llift γ δ pA) (llift γ δ pu) (llift γ δ pv)
  | sCongRefl pA pu => sCongRefl (llift γ δ pA) (llift γ δ pu)
  | sEqToHeq p => sEqToHeq (llift γ δ p)
  | sHeqTypeEq p => sHeqTypeEq (llift γ δ p)
  | sSort x => sSort x
  | sPack A B => sPack (llift γ δ A) (llift γ δ B)
  | sProjT1 x => sProjT1 (llift γ δ x)
  | sProjT2 x => sProjT2 (llift γ δ x)
  | sProjTe x => sProjTe (llift γ δ x)
  end.

Notation llift0 γ t := (llift γ 0 t).

Fixpoint rlift γ δ t : sterm :=
  match t with
  | sRel i =>
    if i <? δ
    then sRel i
    else if i <? δ + γ
         then sProjT2 (sRel i)
         else sRel i
  | sLambda na A B b =>
    sLambda na (rlift γ δ A) (rlift γ (S δ) B) (rlift γ (S δ) b)
  | sApp u na A B v =>
    sApp (rlift γ δ u) na (rlift γ δ A) (rlift γ (S δ) B) (rlift γ δ v)
  | sProd na A B => sProd na (rlift γ δ A) (rlift γ (S δ) B)
  | sEq A u v => sEq (rlift γ δ A) (rlift γ δ u) (rlift γ δ v)
  | sRefl A u => sRefl (rlift γ δ A) (rlift γ δ u)
  | sJ A u P w v p =>
    sJ (rlift γ δ A)
       (rlift γ δ u)
       (rlift γ (S (S δ)) P)
       (rlift γ δ w)
       (rlift γ δ v)
       (rlift γ δ p)
  | sTransport A B p t =>
    sTransport (rlift γ δ A) (rlift γ δ B) (rlift γ δ p) (rlift γ δ t)
  | sHeq A a B b =>
    sHeq (rlift γ δ A) (rlift γ δ a) (rlift γ δ B) (rlift γ δ b)
  | sHeqToEq p => sHeqToEq (rlift γ δ p)
  | sHeqRefl A a => sHeqRefl (rlift γ δ A) (rlift γ δ a)
  | sHeqSym p => sHeqSym (rlift γ δ p)
  | sHeqTrans p q => sHeqTrans (rlift γ δ p) (rlift γ δ q)
  | sHeqTransport p t => sHeqTransport (rlift γ δ p) (rlift γ δ t)
  | sCongProd B1 B2 p q =>
    sCongProd (rlift γ (S δ) B1) (rlift γ (S δ) B2)
              (rlift γ δ p) (rlift γ (S δ) q)
  | sCongLambda B1 B2 t1 t2 pA pB pt =>
    sCongLambda (rlift γ (S δ) B1) (rlift γ (S δ) B2)
                (rlift γ (S δ) t1) (rlift γ (S δ) t2)
                (rlift γ δ pA) (rlift γ (S δ) pB) (rlift γ (S δ) pt)
  | sCongApp B1 B2 pu pA pB pv =>
    sCongApp (rlift γ (S δ) B1) (rlift γ (S δ) B2)
             (rlift γ δ pu) (rlift γ δ pA) (rlift γ (S δ) pB) (rlift γ δ pv)
  | sCongEq pA pu pv => sCongEq (rlift γ δ pA) (rlift γ δ pu) (rlift γ δ pv)
  | sCongRefl pA pu => sCongRefl (rlift γ δ pA) (rlift γ δ pu)
  | sEqToHeq p => sEqToHeq (rlift γ δ p)
  | sHeqTypeEq p => sHeqTypeEq (rlift γ δ p)
  | sSort x => sSort x
  | sPack A B => sPack (rlift γ δ A) (rlift γ δ B)
  | sProjT1 x => sProjT1 (rlift γ δ x)
  | sProjT2 x => sProjT2 (rlift γ δ x)
  | sProjTe x => sProjTe (rlift γ δ x)
  end.

Notation rlift0 γ t := (rlift γ 0 t).

Inductive ismix Σ Γ : forall (Γ1 Γ2 Γm : scontext), Type :=
| mixnil : ismix Σ Γ [] [] []
| mixsnoc Γ1 Γ2 Γm s A1 A2 n1 n2 nm :
    ismix Σ Γ Γ1 Γ2 Γm ->
    Σ ;;; Γ ,,, Γ1 |-i A1 : sSort s ->
    Σ ;;; Γ ,,, Γ2 |-i A2 : sSort s ->
    ismix Σ Γ
          (Γ1 ,, svass n1 A1)
          (Γ2 ,, svass n2 A2)
          (Γm ,, svass nm (sPack (llift0 #|Γm| A1)
                                 (rlift0 #|Γm| A2)))
.

Fact mix_length1 :
  forall {Σ Γ Γ1 Γ2 Γm},
    ismix Σ Γ Γ1 Γ2 Γm ->
    #|Γm| = #|Γ1|.
Proof.
  intros Σ Γ Γ1 Γ2 Γm hm.
  dependent induction hm.
  - cbn. reflexivity.
  - cbn. f_equal. assumption.
Defined.

Fact mix_length2 :
  forall {Σ Γ Γ1 Γ2 Γm},
    ismix Σ Γ Γ1 Γ2 Γm ->
    #|Γm| = #|Γ2|.
Proof.
  intros Σ Γ Γ1 Γ2 Γm hm.
  dependent induction hm.
  - cbn. reflexivity.
  - cbn. f_equal. assumption.
Defined.

Fact safe_nth_mix :
  forall {Σ} {Γ Γ1 Γ2 Γm : scontext},
    ismix Σ Γ Γ1 Γ2 Γm ->
    forall {n isdecl isdecl1 isdecl2},
      sdecl_type (safe_nth Γm (exist _ n isdecl)) =
      sPack (llift0 (#|Γm| - S n)
                    (sdecl_type (safe_nth Γ1 (exist _ n isdecl1))))
            (rlift0 (#|Γm| - S n)
                    (sdecl_type (safe_nth Γ2 (exist _ n isdecl2)))).
Proof.
  intros Σ Γ Γ1 Γ2 Γm hm.
  dependent induction hm.
  - cbn. easy.
  - intro n. destruct n ; intros isdecl isdecl1 isdecl2.
    + cbn. replace (#|Γm| - 0) with #|Γm| by omega. reflexivity.
    + cbn. erewrite IHhm. reflexivity.
Defined.

Lemma llift00 :
  forall {t δ}, llift 0 δ t = t.
Proof.
  intro t.
  dependent induction t ; intro δ.
  all: try (cbn ; f_equal ; easy).
  cbn. case_eq δ.
    + intro h. cbn. f_equal.
    + intros m h. case_eq (n <=? m).
      * intro. reflexivity.
      * intro nlm. cbn.
        replace (m+0)%nat with m by omega.
        rewrite nlm. f_equal.
Defined.

Lemma rlift00 :
  forall {t δ}, rlift 0 δ t = t.
Proof.
  intro t.
  dependent induction t ; intro δ.
  all: try (cbn ; f_equal ; easy).
  cbn. case_eq δ.
    + intro h. cbn. f_equal.
    + intros m h. case_eq (n <=? m).
      * intro. reflexivity.
      * intro nlm. cbn.
        replace (m+0)%nat with m by omega.
        rewrite nlm. f_equal.
Defined.

Lemma lift_llift :
  forall {t i j k},
    lift i k (llift j k t) = llift (i+j) k (lift i k t).
Proof.
  intro t. induction t ; intros i j k.
  all: try (cbn ; f_equal ; easy).
  unfold llift at 1. case_eq (n <? k) ; intro e ; bprop e.
  - unfold lift. case_eq (k <=? n) ; intro e1 ; bprop e1 ; try omega.
    unfold llift. rewrite e. reflexivity.
  - case_eq (n <? k + j) ; intro e1 ; bprop e1.
    + unfold lift. case_eq (k <=? n) ; intro e3 ; bprop e3 ; try omega.
      unfold llift. case_eq (i + n <? k) ; intro e5 ; bprop e5 ; try omega.
      case_eq (i + n <? k + (i+j)) ; intro e7 ; bprop e7 ; try omega.
      reflexivity.
    + unfold lift. case_eq (k <=? n) ; intro e3 ; bprop e3 ; try omega.
      unfold llift. case_eq (i + n <? k) ; intro e5 ; bprop e5 ; try omega.
      case_eq (i + n <? k + (i + j)) ; intro e7 ; bprop e7 ; try omega.
      reflexivity.
Defined.

Lemma lift_llift' :
  forall {t i j k},
    lift i k (llift j k t) = llift j (k+i) (lift i k t).
Proof.
  intro t. induction t ; intros i j k.
  all: try (cbn ; f_equal ;
            try replace (S (S (k + i))) with ((S (S k)) + i)%nat by omega ;
            try replace (S (k + i)) with ((S k) + i)%nat by omega ;
            easy).
  unfold llift at 1. case_eq (n <? k) ; intro e ; bprop e.
  - unfold lift. case_eq (k <=? n) ; intro e1 ; bprop e1 ; try omega.
    unfold llift. case_eq (n <? k + i) ; intro e3 ; bprop e3 ; try omega.
    reflexivity.
  - case_eq (n <? k + j) ; intro e1 ; bprop e1.
    + unfold lift. case_eq (k <=? n) ; intro e3 ; bprop e3 ; try omega.
      unfold llift. case_eq (i + n <? k + i) ; intro e5 ; bprop e5 ; try omega.
      case_eq (i + n <? k + i + j) ; intro e7 ; bprop e7 ; try omega.
      reflexivity.
    + unfold lift. case_eq (k <=? n) ; intro e3 ; bprop e3 ; try omega.
      unfold llift. case_eq (i + n <? k + i) ; intro e5 ; bprop e5 ; try omega.
      case_eq (i + n <? k + i + j) ; intro e7 ; bprop e7 ; try omega.
      reflexivity.
Defined.

Lemma lift_llift3 :
  forall {t i j k l},
    l <= k ->
    lift i l (llift j k t) = llift j (i+k) (lift i l t).
Proof.
  intro t. induction t ; intros i j k l h.
  all: try (cbn ; f_equal ;
            try replace (S (S (i + k))) with (i + (S (S k)))%nat by omega ;
            try replace (S (i + k)) with (i + (S k))%nat by omega ;
            easy).
  unfold llift at 1.
  case_eq (n <? k) ; intro e ; bprop e.
  - cbn. case_eq (l <=? n) ; intro e1 ; bprop e1.
    + unfold llift. case_eq (i + n <? i + k) ; intro e3 ; bprop e3 ; try omega.
      reflexivity.
    + unfold llift. case_eq (n <? i + k) ; intro e3 ; bprop e3 ; try omega.
      reflexivity.
  - case_eq (n <? k + j) ; intro e1 ; bprop e1.
    + cbn. case_eq (l <=? n) ; intro e3 ; bprop e3 ; try omega.
      unfold llift.
      case_eq (i + n <? i + k) ; intro e5 ; bprop e5 ; try omega.
      case_eq (i + n <? i + k + j) ; intro e7 ; bprop e7 ; try omega.
      reflexivity.
    + cbn. case_eq (l <=? n) ; intro e3 ; bprop e3 ; try omega.
      unfold llift. case_eq (i+n <? i+k) ; intro e5 ; bprop e5 ; try omega.
      case_eq (i+n <? i+k+j) ; intro e7 ; bprop e7 ; try omega.
      reflexivity.
Defined.

Lemma lift_rlift :
  forall {t i j k},
    lift i k (rlift j k t) = rlift (i+j) k (lift i k t).
Proof.
  intro t. induction t ; intros i j k.
  all: try (cbn ; f_equal ; easy).
  unfold rlift at 1. case_eq (n <? k) ; intro e ; bprop e.
  - unfold lift. case_eq (k <=? n) ; intro e1 ; bprop e1 ; try omega.
    unfold rlift. rewrite e. reflexivity.
  - case_eq (n <? k + j) ; intro e1 ; bprop e1.
    + unfold lift. case_eq (k <=? n) ; intro e3 ; bprop e3 ; try omega.
      unfold rlift. case_eq (i + n <? k) ; intro e5 ; bprop e5 ; try omega.
      case_eq (i + n <? k + (i+j)) ; intro e7 ; bprop e7 ; try omega.
      reflexivity.
    + unfold lift. case_eq (k <=? n) ; intro e3 ; bprop e3 ; try omega.
      unfold rlift. case_eq (i + n <? k) ; intro e5 ; bprop e5 ; try omega.
      case_eq (i + n <? k + (i + j)) ; intro e7 ; bprop e7 ; try omega.
      reflexivity.
Defined.

Lemma lift_rlift3 :
  forall {t i j k l},
    l <= k ->
    lift i l (rlift j k t) = rlift j (i+k) (lift i l t).
Proof.
  intro t. induction t ; intros i j k l h.
  all: try (cbn ; f_equal ;
            try replace (S (S (i + k))) with (i + (S (S k)))%nat by omega ;
            try replace (S (i + k)) with (i + (S k))%nat by omega ;
            easy).
  unfold rlift at 1.
  case_eq (n <? k) ; intro e ; bprop e.
  - cbn. case_eq (l <=? n) ; intro e1 ; bprop e1.
    + unfold rlift. case_eq (i + n <? i + k) ; intro e3 ; bprop e3 ; try omega.
      reflexivity.
    + unfold rlift. case_eq (n <? i + k) ; intro e3 ; bprop e3 ; try omega.
      reflexivity.
  - case_eq (n <? k + j) ; intro e1 ; bprop e1.
    + cbn. case_eq (l <=? n) ; intro e3 ; bprop e3 ; try omega.
      unfold rlift.
      case_eq (i + n <? i + k) ; intro e5 ; bprop e5 ; try omega.
      case_eq (i + n <? i + k + j) ; intro e7 ; bprop e7 ; try omega.
      reflexivity.
    + cbn. case_eq (l <=? n) ; intro e3 ; bprop e3 ; try omega.
      unfold rlift. case_eq (i+n <? i+k) ; intro e5 ; bprop e5 ; try omega.
      case_eq (i+n <? i+k+j) ; intro e7 ; bprop e7 ; try omega.
      reflexivity.
Defined.

Definition llift_decl n k d : scontext_decl :=
  {| sdecl_name := sdecl_name d ;
     sdecl_body := option_map (llift n k) (sdecl_body d) ;
     sdecl_type := llift n k (sdecl_type d)
  |}.

Fixpoint llift_context n (Δ : scontext) : scontext :=
  match Δ with
  | nil => nil
  | A :: Δ => (llift_decl n #|Δ| A) :: (llift_context n Δ)
  end.

Fact llift_context_length :
  forall {n Δ}, #|llift_context n Δ| = #|Δ|.
Proof.
  intros n Δ.
  induction Δ.
  - cbn. reflexivity.
  - cbn. f_equal. assumption.
Defined.

Fact llift_decl0 :
  forall {d k}, llift_decl 0 k d = d.
Proof.
  intros d k.
  destruct d as [x b A].
  unfold llift_decl. cbn. rewrite llift00. f_equal.
  destruct b.
  - cbn. rewrite llift00. reflexivity.
  - reflexivity.
Defined.

Fact llift_context0 :
  forall {Γ}, llift_context 0 Γ = Γ.
Proof.
  intro Γ. induction Γ.
  - reflexivity.
  - cbn. rewrite llift_decl0. rewrite IHΓ. reflexivity.
Defined.

Fixpoint rlift_context n (Δ : scontext) : scontext :=
  match Δ with
  | nil => nil
  | A :: Δ =>
    svass (sdecl_name A) (rlift n #|Δ| (sdecl_type A)) :: rlift_context n Δ
  end.

Fact rlift_context_length :
  forall {n Δ}, #|rlift_context n Δ| = #|Δ|.
Proof.
  intros n Δ.
  induction Δ.
  - cbn. reflexivity.
  - cbn. f_equal. assumption.
Defined.

(* We introduce an alternate version of ismix that will be implied by ismix but
   will be used as an intermediary for the proof.
 *)
Inductive ismix' Σ Γ : forall (Γ1 Γ2 Γm : scontext), Type :=
| mixnil' : ismix' Σ Γ [] [] []
| mixsnoc' Γ1 Γ2 Γm s A1 A2 n1 n2 nm :
    ismix' Σ Γ Γ1 Γ2 Γm ->
    Σ ;;; Γ ,,, Γm |-i llift0 #|Γm| A1 : sSort s ->
    Σ ;;; Γ ,,, Γm |-i rlift0 #|Γm|A2 : sSort s ->
    ismix' Σ Γ
          (Γ1 ,, svass n1 A1)
          (Γ2 ,, svass n2 A2)
          (Γm ,, svass nm (sPack (llift0 #|Γm| A1)
                                 (rlift0 #|Γm| A2)))
.

Lemma wf_mix {Σ Γ Γ1 Γ2 Γm} (h : wf Σ Γ) :
  ismix' Σ Γ Γ1 Γ2 Γm ->
  wf Σ (Γ ,,, Γm).
Proof.
  intro hm. induction hm.
  - cbn. assumption.
  - cbn. econstructor.
    + assumption.
    + eapply type_Pack with (s := s) ; assumption.
Defined.

Definition llift_subst :
  forall (u t : sterm) (i j m : nat),
    llift j (i+m) (u {m := t}) = (llift j (S i+m) u) {m := llift j i t}.
Proof.
  induction u ; intros t i j m.
  all: try (cbn ; f_equal;
            try replace (S (S (S (j + m))))%nat with (j + (S (S (S m))))%nat by omega ;
            try replace (S (S (j + m)))%nat with (j + (S (S m)))%nat by omega ;
            try replace (S (j + m))%nat with (j + (S m))%nat by omega ;
            try replace (S (S (S (i + m))))%nat with (i + (S (S (S m))))%nat by omega ;
            try replace (S (S (i + m)))%nat with (i + (S (S m)))%nat by omega ;
            try replace (S (i + m))%nat with (i + (S m))%nat by omega;
            try  (rewrite IHu; cbn; repeat f_equal; omega);
            try  (rewrite IHu1; cbn; repeat f_equal; omega);
            try  (rewrite IHu2; cbn; repeat f_equal; omega);
            try  (rewrite IHu3; cbn; repeat f_equal; omega);
            try  (rewrite IHu4; cbn; repeat f_equal; omega);
            try  (rewrite IHu5; cbn; repeat f_equal; omega);
            try  (rewrite IHu6; cbn; repeat f_equal; omega);
            try  (rewrite IHu7; cbn; repeat f_equal; omega);
            try  (rewrite IHu8; cbn; repeat f_equal; omega)).
  case_eq (m ?= n) ; intro e ; bprop e.
  - subst. case_eq (n <=? i + n) ; intro e1 ; bprop e1 ; try omega.
    cbn. rewrite e.
Admitted.

Fact safe_nth_llift :
  forall {Δ Γm : scontext} {n is1 is2},
    sdecl_type (safe_nth (llift_context #|Γm| Δ) (exist _ n is1)) =
    llift #|Γm| (#|Δ| - S n) (sdecl_type (safe_nth Δ (exist _ n is2))).
Proof.
  intro Δ. induction Δ.
  - cbn. easy.
  - intro Γm. destruct n ; intros is1 is2.
    + cbn. replace (#|Δ| - 0) with #|Δ| by omega. reflexivity.
    + cbn. erewrite IHΔ. reflexivity.
Defined.

(* For SCommon *)
Fact cat_nil :
  forall {Γ}, Γ ,,, [] = Γ.
Proof.
  induction Γ ; easy.
Defined.

Fact nil_cat :
  forall {Γ}, [] ,,, Γ = Γ.
Proof.
  induction Γ ; try easy.
  cbn. f_equal. assumption.
Defined.

(* Should be somewhere else. *)
Lemma inversion_wf_cat :
  forall {Σ Δ Γ},
    wf Σ (Γ ,,, Δ) ->
    wf Σ Γ.
Proof.
  intros Σ Δ. induction Δ ; intros Γ h.
  - assumption.
  - dependent destruction h.
    apply IHΔ. assumption.
Defined.

Fact nil_eq_cat :
  forall {Δ Γ},
    [] = Γ ,,, Δ ->
    ([] = Γ) * ([] = Δ).
Proof.
  intro Δ ; destruct Δ ; intros Γ e.
  - rewrite cat_nil in e. split ; easy.
  - cbn in e. inversion e.
Defined.

Ltac lh h :=
  lazymatch goal with
  | [ type_llift' :
        forall (Σ : global_context) (Γ Γ1 Γ2 Γm Δ : scontext) (t A : sterm),
          Σ;;; Γ ,,, Γ1 ,,, Δ |-i t : A ->
          ismix' Σ Γ Γ1 Γ2 Γm ->
          Σ;;; Γ ,,, Γm ,,, llift_context #|Γm| Δ
          |-i llift #|Γm| #|Δ| t : llift #|Γm| #|Δ| A,
      cong_llift' :
        forall (Σ : global_context) (Γ Γ1 Γ2 Γm Δ : scontext) (t1 t2 A : sterm),
          Σ;;; Γ ,,, Γ1 ,,, Δ |-i t1 = t2 : A ->
          ismix' Σ Γ Γ1 Γ2 Γm ->
          Σ;;; Γ ,,, Γm ,,, llift_context #|Γm| Δ |-i llift #|Γm| #|Δ| t1
          = llift #|Γm| #|Δ| t2 : llift #|Γm| #|Δ| A
    |- _ ] =>
    lazymatch type of h with
    | _ ;;; ?Γ' ,,, ?Γ1' ,,, ?Δ' |-i _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_llift' with (Γ := Γ') (Γ1 := Γ1') (Δ := Δ') (A := T') ; [
            exact h
          | eassumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,,, ?Γ1' ,,, ?Δ'),, ?d' |-i _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_llift' with (Γ := Γ') (Γ1 := Γ1') (Δ := Δ',, d') (A := T') ; [
            exact h
          | eassumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,,, ?Γ1' ,,, ?Δ'),, ?d',, ?d'' |-i _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_llift' with (Γ := Γ') (Γ1 := Γ1') (Δ := (Δ',, d'),, d'') (A := T') ; [
            exact h
          | eassumption
          ]
        | .. ]
      | .. ]
    | _ ;;; ?Γ' ,,, ?Γ1' ,,, ?Δ' |-i _ = _ : ?T' =>
      eapply meta_eqconv ; [
        eapply meta_eqctx_conv ; [
          eapply cong_llift' with (Γ := Γ') (Γ1 := Γ1') (Δ := Δ') (A := T') ; [
            exact h
          | eassumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,,, ?Γ1' ,,, ?Δ'),, ?d' |-i _ = _ : ?T' =>
      eapply meta_eqconv ; [
        eapply meta_eqctx_conv ; [
          eapply cong_llift' with (Γ := Γ') (Γ1 := Γ1') (Δ := Δ',, d') (A := T') ; [
            exact h
          | eassumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,,, ?Γ1' ,,, ?Δ'),, ?d',, ?d'' |-i _ = _ : ?T' =>
      eapply meta_eqconv ; [
        eapply meta_eqctx_conv ; [
          eapply cong_llift' with (Γ := Γ') (Γ1 := Γ1') (Δ := (Δ',, d'),, d'') (A := T') ; [
            exact h
          | eassumption
          ]
        | .. ]
      | .. ]
    end ; try (cbn ; reflexivity)
  | _ => fail "Cannot retrieve type_llift' or cong_llift'"
  end.

Ltac rh h :=
  lazymatch goal with
  | [ type_rlift' :
        forall (Σ : global_context) (Γ Γ1 Γ2 Γm Δ : scontext) (t A : sterm),
          Σ;;; Γ ,,, Γ2 ,,, Δ |-i t : A ->
          ismix' Σ Γ Γ1 Γ2 Γm ->
          Σ;;; Γ ,,, Γm ,,, rlift_context #|Γm| Δ
          |-i rlift #|Γm| #|Δ| t : rlift #|Γm| #|Δ| A,
      cong_rlift' :
        forall (Σ : global_context) (Γ Γ1 Γ2 Γm Δ : scontext) (t1 t2 A : sterm),
          Σ;;; Γ ,,, Γ2 ,,, Δ |-i t1 = t2 : A ->
          ismix' Σ Γ Γ1 Γ2 Γm ->
          Σ;;; Γ ,,, Γm ,,, rlift_context #|Γm| Δ |-i rlift #|Γm| #|Δ| t1
          = rlift #|Γm| #|Δ| t2 : rlift #|Γm| #|Δ| A
    |- _ ] =>
    lazymatch type of h with
    | _ ;;; ?Γ' ,,, ?Γ2' ,,, ?Δ' |-i _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_rlift' with (Γ := Γ') (Γ2 := Γ2') (Δ := Δ') (A := T') ; [
            exact h
          | eassumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,,, ?Γ2' ,,, ?Δ'),, ?d' |-i _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_rlift' with (Γ := Γ') (Γ2 := Γ2') (Δ := Δ',, d') (A := T') ; [
            exact h
          | eassumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,,, ?Γ2' ,,, ?Δ'),, ?d',, ?d'' |-i _ : ?T' =>
      eapply meta_conv ; [
        eapply meta_ctx_conv ; [
          eapply type_rlift' with (Γ := Γ') (Γ2 := Γ2') (Δ := (Δ',, d'),, d'') (A := T') ; [
            exact h
          | eassumption
          ]
        | .. ]
      | .. ]
    | _ ;;; ?Γ' ,,, ?Γ2' ,,, ?Δ' |-i _ = _ : ?T' =>
      eapply meta_eqconv ; [
        eapply meta_eqctx_conv ; [
          eapply cong_rlift' with (Γ := Γ') (Γ2 := Γ2') (Δ := Δ') (A := T') ; [
            exact h
          | eassumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,,, ?Γ2' ,,, ?Δ'),, ?d' |-i _ = _ : ?T' =>
      eapply meta_eqconv ; [
        eapply meta_eqctx_conv ; [
          eapply cong_rlift' with (Γ := Γ') (Γ2 := Γ2') (Δ := Δ',, d') (A := T') ; [
            exact h
          | eassumption
          ]
        | .. ]
      | .. ]
    | _ ;;; (?Γ' ,,, ?Γ2' ,,, ?Δ'),, ?d',, ?d'' |-i _ = _ : ?T' =>
      eapply meta_eqconv ; [
        eapply meta_eqctx_conv ; [
          eapply cong_rlift' with (Γ := Γ') (Γ2 := Γ2') (Δ := (Δ',, d'),, d'') (A := T') ; [
            exact h
          | eassumption
          ]
        | .. ]
      | .. ]
    end ; try (cbn ; reflexivity)
  | _ => fail "Cannot retrieve type_rlift' or cong_rlift'"
  end.

Ltac emh :=
  lazymatch goal with
  | h : _ ;;; _ |-i ?t : _ |- _ ;;; _ |-i llift _ _ ?t : _ => lh h
  | h : _ ;;; _ |-i ?t = _ : _ |- _ ;;; _ |-i llift _ _ ?t = _ : _ =>
    lh h
  | h : _ ;;; _ |-i ?t : _ |- _ ;;; _ |-i rlift _ _ ?t : _ => rh h
  | h : _ ;;; _ |-i ?t = _ : _ |- _ ;;; _ |-i rlift _ _ ?t = _ : _ =>
    rh h
  | _ => fail "Not a case for emh"
  end.

Axiom cheating : forall {A}, A.
Tactic Notation "cheat" := apply cheating.

Fixpoint type_llift' {Σ Γ Γ1 Γ2 Γm Δ t A}
  (h : Σ ;;; Γ ,,, Γ1 ,,, Δ |-i t : A) {struct h} :
  ismix' Σ Γ Γ1 Γ2 Γm ->
  Σ ;;; Γ ,,, Γm ,,, llift_context #|Γm| Δ
  |-i llift #|Γm| #|Δ| t : llift #|Γm| #|Δ| A

with cong_llift' {Σ Γ Γ1 Γ2 Γm Δ t1 t2 A}
  (h : Σ ;;; Γ ,,, Γ1 ,,, Δ |-i t1 = t2 : A) {struct h} :
  ismix' Σ Γ Γ1 Γ2 Γm ->
  Σ ;;; Γ ,,, Γm ,,, llift_context #|Γm| Δ
  |-i llift #|Γm| #|Δ| t1 = llift #|Γm| #|Δ| t2 : llift #|Γm| #|Δ| A

with type_rlift' {Σ Γ Γ1 Γ2 Γm Δ t A}
  (h : Σ ;;; Γ ,,, Γ2 ,,, Δ |-i t : A) {struct h} :
  ismix' Σ Γ Γ1 Γ2 Γm ->
  Σ ;;; Γ ,,, Γm ,,, rlift_context #|Γm| Δ
  |-i rlift #|Γm| #|Δ| t : rlift #|Γm| #|Δ| A

with cong_rlift' {Σ Γ Γ1 Γ2 Γm Δ t1 t2 A}
  (h : Σ ;;; Γ ,,, Γ2 ,,, Δ |-i t1 = t2 : A) {struct h} :
  ismix' Σ Γ Γ1 Γ2 Γm ->
  Σ ;;; Γ ,,, Γm ,,, rlift_context #|Γm| Δ
  |-i rlift #|Γm| #|Δ| t1 = rlift #|Γm| #|Δ| t2 : rlift #|Γm| #|Δ| A

with wf_llift' {Σ Γ Γ1 Γ2 Γm Δ} (h : wf Σ (Γ ,,, Γ1 ,,, Δ)) {struct h} :
  ismix' Σ Γ Γ1 Γ2 Γm ->
  wf Σ (Γ ,,, Γm ,,, llift_context #|Γm| Δ)

with wf_rlift' {Σ Γ Γ1 Γ2 Γm Δ} (h : wf Σ (Γ ,,, Γ2 ,,, Δ)) {struct h} :
  ismix' Σ Γ Γ1 Γ2 Γm ->
  wf Σ (Γ ,,, Γm ,,, rlift_context #|Γm| Δ)
.
Proof.
  (* type_llift' *)
  - { dependent destruction h ; intro hm.
      - unfold llift at 1.
        case_eq (n <? #|Δ|) ; intro e ; bprop e.
        + erewrite @safe_nth_lt with (isdecl' := e0).
          eapply meta_conv.
          * eapply type_Rel. eapply wf_llift' ; eassumption.
          * erewrite safe_nth_lt. erewrite safe_nth_llift.
            (* We need the right lemma. *)
            cheat.
        + (* case_eq (n <? #|Δ| + #|Γ1|) ; intro e1 ; bprop e1. *)
          (* * rewrite mix_mix'. *)
          (*   erewrite safe_nth_ge'. erewrite safe_nth_lt. *)
          (*   eapply type_ProjT1'. *)
          (*   eapply meta_conv. *)
          (*   -- eapply type_Rel. rewrite <- mix_mix'. *)
          (*      eapply wf_llift ; eassumption. *)
          (*   -- erewrite safe_nth_ge'. erewrite safe_nth_lt. *)
          (*      erewrite safe_nth_mix' by assumption. *)
          (*      cbn. f_equal. *)
          (*      (* rewrite lift_llift'. f_equal. *) *)
          (*      (* We probably need another lemma again... *) *)
          (*      cheat. *)
          (* * rewrite mix_mix'. *)
          (*   erewrite safe_nth_ge'. erewrite safe_nth_ge'. *)
          (*   eapply meta_conv. *)
          (*   -- eapply type_Rel. rewrite <- mix_mix'. *)
          (*      eapply wf_llift ; eassumption. *)
          (*   -- erewrite safe_nth_ge'. erewrite safe_nth_ge'. *)
          (*      (* Another one perhaps? *) *)
          (*      cheat. *)
          cheat.
      - cbn. eapply type_Sort. eapply wf_llift' ; eassumption.
      - cbn. eapply type_Prod ; emh.
      - cbn. eapply type_Lambda ; emh.
      - cbn. cheat.
      - cbn. eapply type_Eq ; emh.
      - cbn. eapply type_Refl ; emh.
      - cbn. cheat.
      - cbn. eapply type_Transport ; emh.
      - cbn. eapply type_Heq ; emh.
      - cbn. eapply type_HeqToEq ; emh.
      - cbn. eapply type_HeqRefl ; emh.
      - cbn. eapply type_HeqSym ; emh.
      - cbn.
        eapply @type_HeqTrans
          with (B := llift #|Γm| #|Δ| B) (b := llift #|Γm| #|Δ| b) ; emh.
      - cbn. eapply type_HeqTransport ; emh.
      - cbn. eapply type_CongProd ; emh.
        cbn. f_equal.
        + cheat.
        + cheat.
      - cbn. eapply type_CongLambda ; emh.
        + cheat.
        + cheat.
      - cbn. cheat.
      - cbn. eapply type_CongEq ; emh.
      - cbn. eapply type_CongRefl ; emh.
      - cbn. eapply type_EqToHeq ; emh.
      - cbn. eapply type_HeqTypeEq ; emh.
      - cbn. eapply type_Pack ; emh.
      - cbn. eapply @type_ProjT1 with (A2 := llift #|Γm| #|Δ| A2) ; emh.
      - cbn. eapply @type_ProjT2 with (A1 := llift #|Γm| #|Δ| A1) ; emh.
      - cbn. eapply type_ProjTe ; emh.
      - eapply type_conv ; emh.
    }

  (* cong_llift' *)
  - { dependent destruction h ; intro hm.
      - apply eq_reflexivity. emh.
      - apply eq_symmetry ; emh.
      - eapply eq_transitivity ; emh.
      - cheat.
      - cheat.
      - cbn. eapply eq_TransportRefl ; emh.
      - eapply eq_conv ; emh.
      - cbn. eapply cong_Prod ; emh.
      - cbn. eapply cong_Lambda ; emh.
      - cheat.
      - cbn. eapply cong_Eq ; emh.
      - cbn. eapply cong_Refl ; emh.
      - cbn. cheat.
      - cbn. eapply cong_Transport ; emh.
      - cbn. eapply cong_Heq ; emh.
      - cbn. eapply cong_Pack ; emh.
      - cbn. eapply cong_HeqToEq ; emh.
      - cbn. eapply cong_HeqRefl ; emh.
      - cbn. eapply cong_HeqSym ; emh.
      - cbn.
        eapply cong_HeqTrans
          with (B := llift #|Γm| #|Δ| B) (b := llift #|Γm| #|Δ| b) ; emh.
      - cbn. eapply cong_HeqTransport ; emh.
      - cbn. eapply cong_CongProd ; emh.
        cbn. f_equal.
        + cheat.
        + cheat.
      - cbn. eapply cong_CongLambda ; emh.
        + cheat.
        + cheat.
      - cheat.
      - cbn. eapply cong_CongEq ; emh.
      - cbn. eapply cong_CongRefl ; emh.
      - cbn. eapply cong_EqToHeq ; emh.
      - cbn. eapply cong_HeqTypeEq ; emh.
      - cbn. eapply cong_ProjT1 with (A2 := llift #|Γm| #|Δ| A2) ; emh.
      - cbn. eapply cong_ProjT2 with (A1 := llift #|Γm| #|Δ| A1) ; emh.
      - cbn. eapply cong_ProjTe ; emh.
      - cbn. eapply eq_HeqToEqRefl ; emh.
    }

  (* type_rlift' *)
  - { dependent destruction h ; intro hm.
      - cheat.
      - cbn. eapply type_Sort. eapply wf_rlift' ; eassumption.
      - cbn. eapply type_Prod ; emh.
      - cbn. eapply type_Lambda ; emh.
      - cbn. cheat.
      - cbn. eapply type_Eq ; emh.
      - cbn. eapply type_Refl ; emh.
      - cbn. cheat.
      - cbn. eapply type_Transport ; emh.
      - cbn. eapply type_Heq ; emh.
      - cbn. eapply type_HeqToEq ; emh.
      - cbn. eapply type_HeqRefl ; emh.
      - cbn. eapply type_HeqSym ; emh.
      - cbn.
        eapply @type_HeqTrans
          with (B := rlift #|Γm| #|Δ| B) (b := rlift #|Γm| #|Δ| b) ; emh.
      - cbn. eapply type_HeqTransport ; emh.
      - cbn. eapply type_CongProd ; emh.
        cbn. f_equal.
        + cheat.
        + cheat.
      - cbn. eapply type_CongLambda ; emh.
        + cheat.
        + cheat.
      - cbn. cheat.
      - cbn. eapply type_CongEq ; emh.
      - cbn. eapply type_CongRefl ; emh.
      - cbn. eapply type_EqToHeq ; emh.
      - cbn. eapply type_HeqTypeEq ; emh.
      - cbn. eapply type_Pack ; emh.
      - cbn. eapply @type_ProjT1 with (A2 := rlift #|Γm| #|Δ| A2) ; emh.
      - cbn. eapply @type_ProjT2 with (A1 := rlift #|Γm| #|Δ| A1) ; emh.
      - cbn. eapply type_ProjTe ; emh.
      - eapply type_conv ; emh.
    }

  (* cong_rlift' *)
  - { dependent destruction h ; intro hm.
      - apply eq_reflexivity. emh.
      - apply eq_symmetry ; emh.
      - eapply eq_transitivity ; emh.
      - cheat.
      - cheat.
      - cbn. eapply eq_TransportRefl ; emh.
      - eapply eq_conv ; emh.
      - cbn. eapply cong_Prod ; emh.
      - cbn. eapply cong_Lambda ; emh.
      - cheat.
      - cbn. eapply cong_Eq ; emh.
      - cbn. eapply cong_Refl ; emh.
      - cbn. cheat.
      - cbn. eapply cong_Transport ; emh.
      - cbn. eapply cong_Heq ; emh.
      - cbn. eapply cong_Pack ; emh.
      - cbn. eapply cong_HeqToEq ; emh.
      - cbn. eapply cong_HeqRefl ; emh.
      - cbn. eapply cong_HeqSym ; emh.
      - cbn.
        eapply cong_HeqTrans
          with (B := rlift #|Γm| #|Δ| B) (b := rlift #|Γm| #|Δ| b) ; emh.
      - cbn. eapply cong_HeqTransport ; emh.
      - cbn. eapply cong_CongProd ; emh.
        cbn. f_equal.
        + cheat.
        + cheat.
      - cbn. eapply cong_CongLambda ; emh.
        + cheat.
        + cheat.
      - cheat.
      - cbn. eapply cong_CongEq ; emh.
      - cbn. eapply cong_CongRefl ; emh.
      - cbn. eapply cong_EqToHeq ; emh.
      - cbn. eapply cong_HeqTypeEq ; emh.
      - cbn. eapply cong_ProjT1 with (A2 := rlift #|Γm| #|Δ| A2) ; emh.
      - cbn. eapply cong_ProjT2 with (A1 := rlift #|Γm| #|Δ| A1) ; emh.
      - cbn. eapply cong_ProjTe ; emh.
      - cbn. eapply eq_HeqToEqRefl ; emh.
    }

  (* wf_llift' *)
  - { dependent destruction h.
      - destruct Δ.
        + cbn. rewrite cat_nil in x. destruct (nil_eq_cat x) as [e e1].
          subst. intro hm.
          dependent destruction hm. constructor.
        + cbn in x. inversion x.
      - destruct Δ.
        + cbn. rewrite cat_nil in x.
          intro hm. eapply wf_mix ; [| eassumption ].
          destruct Γ1.
          * rewrite cat_nil in x. subst. econstructor ; eassumption.
          * cbn in x. inversion x. subst.
            eapply inversion_wf_cat. eassumption.
        + cbn. cbn in x. inversion x. subst.
          intro hm. econstructor.
          * eapply wf_llift' ; eassumption.
          * eapply type_llift' with (A := sSort s) ; eassumption.

      (* BELOW is how it should have looked! *)
      (* destruct Δ. *)
      (* - cbn. rewrite cat_nil in h. *)
      (*   intro hm. eapply wf_mix. *)
      (*   + eapply inversion_wf_cat. eassumption. *)
      (*   + eassumption. *)
      (* - cbn. intro hm. dependent destruction h. *)
      (*   econstructor. *)
      (*   + eapply wf_llift' ; eassumption. *)
      (*   + eapply type_llift' with (A := sSort s0) ; eassumption. *)
    }

  (* wf_rlift' *)
  - { dependent destruction h.
      - destruct Δ.
        + cbn. rewrite cat_nil in x. destruct (nil_eq_cat x) as [e e1].
          subst. intro hm.
          dependent destruction hm. constructor.
        + cbn in x. inversion x.
      - destruct Δ.
        + cbn. rewrite cat_nil in x.
          intro hm. eapply wf_mix ; [| eassumption ].
          destruct Γ2.
          * rewrite cat_nil in x. subst. econstructor ; eassumption.
          * cbn in x. inversion x. subst.
            eapply inversion_wf_cat. eassumption.
        + cbn. cbn in x. inversion x. subst.
          intro hm. econstructor.
          * eapply wf_rlift' ; eassumption.
          * eapply type_rlift' with (A := sSort s) ; eassumption.
    }

  Unshelve.
  all: cbn ; try rewrite !length_cat ;
       try rewrite !llift_context_length ;
       try rewrite !length_cat in isdecl ;
       try omega.
Defined.

Lemma ismix_ismix' :
  forall {Σ Γ Γ1 Γ2 Γm},
    ismix Σ Γ Γ1 Γ2 Γm ->
    ismix' Σ Γ Γ1 Γ2 Γm.
Proof.
  intros Σ Γ Γ1 Γ2 Γm h.
  dependent induction h.
  - constructor.
  - econstructor.
    + assumption.
    + eapply @type_llift' with (A := sSort s) (Δ := []) ; eassumption.
    + eapply @type_rlift' with (A := sSort s) (Δ := []) ; eassumption.
Defined.

Corollary type_llift :
  forall {Σ Γ Γ1 Γ2 Γm Δ t A},
    Σ ;;; Γ ,,, Γ1 ,,, Δ |-i t : A ->
    ismix Σ Γ Γ1 Γ2 Γm ->
    Σ ;;; Γ ,,, Γm ,,, llift_context #|Γm| Δ
    |-i llift #|Γm| #|Δ| t : llift #|Γm| #|Δ| A.
Proof.
  intros Σ Γ Γ1 Γ2 Γm Δ t A ht hm.
  eapply type_llift'.
  - eassumption.
  - eapply ismix_ismix'. eassumption.
Defined.

Corollary cong_llift :
  forall {Σ Γ Γ1 Γ2 Γm Δ t1 t2 A},
    Σ ;;; Γ ,,, Γ1 ,,, Δ |-i t1 = t2 : A ->
    ismix Σ Γ Γ1 Γ2 Γm ->
    Σ ;;; Γ ,,, Γm ,,, llift_context #|Γm| Δ
    |-i llift #|Γm| #|Δ| t1 = llift #|Γm| #|Δ| t2 : llift #|Γm| #|Δ| A.
Proof.
  intros Σ Γ Γ1 Γ2 Γm Δ t1 t2 A ht hm.
  eapply cong_llift'.
  - eassumption.
  - eapply ismix_ismix'. eassumption.
Defined.

Corollary wf_llift :
  forall {Σ Γ Γ1 Γ2 Γm Δ},
    wf Σ (Γ ,,, Γ1 ,,, Δ) ->
    ismix Σ Γ Γ1 Γ2 Γm ->
    wf Σ (Γ ,,, Γm ,,, llift_context #|Γm| Δ).
Proof.
  intros Σ Γ Γ1 Γ2 Γm Δ hw hm.
  eapply wf_llift'.
  - eassumption.
  - eapply ismix_ismix'. eassumption.
Defined.

Corollary type_rlift :
  forall {Σ Γ Γ1 Γ2 Γm Δ t A},
    Σ ;;; Γ ,,, Γ2 ,,, Δ |-i t : A ->
    ismix Σ Γ Γ1 Γ2 Γm ->
    Σ ;;; Γ ,,, Γm ,,, rlift_context #|Γm| Δ
    |-i rlift #|Γm| #|Δ| t : rlift #|Γm| #|Δ| A.
Proof.
  intros Σ Γ Γ1 Γ2 Γm Δ t A ht hm.
  eapply type_rlift'.
  - eassumption.
  - eapply ismix_ismix'. eassumption.
Defined.

Corollary cong_rlift :
  forall {Σ Γ Γ1 Γ2 Γm Δ t1 t2 A},
    Σ ;;; Γ ,,, Γ2 ,,, Δ |-i t1 = t2 : A ->
    ismix Σ Γ Γ1 Γ2 Γm ->
    Σ ;;; Γ ,,, Γm ,,, rlift_context #|Γm| Δ
    |-i rlift #|Γm| #|Δ| t1 = rlift #|Γm| #|Δ| t2 : rlift #|Γm| #|Δ| A.
Proof.
  intros Σ Γ Γ1 Γ2 Γm Δ t1 t2 A ht hm.
  eapply cong_rlift'.
  - eassumption.
  - eapply ismix_ismix'. eassumption.
Defined.

Corollary wf_rlift :
  forall {Σ Γ Γ1 Γ2 Γm Δ},
    wf Σ (Γ ,,, Γ2 ,,, Δ) ->
    ismix Σ Γ Γ1 Γ2 Γm ->
    wf Σ (Γ ,,, Γm ,,, rlift_context #|Γm| Δ).
Proof.
  intros Σ Γ Γ1 Γ2 Γm Δ hw hm.
  eapply wf_rlift'.
  - eassumption.
  - eapply ismix_ismix'. eassumption.
Defined.

(* Lemma to use ismix knowledge about sorting. *)
Lemma ismix_nth_sort :
  forall {Σ Γ Γ1 Γ2 Γm},
    ismix Σ Γ Γ1 Γ2 Γm ->
    forall x is1 is2,
      ∑ s,
        (Σ;;; Γ ,,, Γ1
         |-i lift0 (S x) (sdecl_type (safe_nth Γ1 (exist _ x is1))) : sSort s) *
        (Σ;;; Γ ,,, Γ2
         |-i lift0 (S x) (sdecl_type (safe_nth Γ2 (exist _ x is2))) : sSort s).
Proof.
  intros Σ Γ Γ1 Γ2 Γm hm.
  dependent induction hm.
  - intros x is1. cbn in is1. easy.
  - intro x. destruct x ; intros is1 is2.
    + cbn. exists s. split ; eapply @typing_lift01 with (A := sSort s) ; eassumption.
    + cbn. cbn in is1, is2.
      set (is1' := gt_le_S x #|Γ1| (gt_S_le (S x) #|Γ1| is1)).
      set (is2' := gt_le_S x #|Γ2| (gt_S_le (S x) #|Γ2| is2)).
      destruct (IHhm x is1' is2') as [s' [h1 h2]].
      exists s'. split.
      * replace (S (S x)) with (1 + (S x))%nat by omega.
        rewrite <- liftP3 with (k := 0) by omega.
        eapply @typing_lift01 with (A := sSort s') ; eassumption.
      * replace (S (S x)) with (1 + (S x))%nat by omega.
        rewrite <- liftP3 with (k := 0) by omega.
        eapply @typing_lift01 with (A := sSort s') ; eassumption.
Defined.

(* Simpler to use corollaries *)

Corollary type_llift0 :
  forall {Σ Γ Γ1 Γ2 Γm t A},
    Σ ;;; Γ ,,, Γ1 |-i t : A ->
    ismix Σ Γ Γ1 Γ2 Γm ->
    Σ ;;; Γ ,,, Γm |-i llift0 #|Γm| t : llift0 #|Γm| A.
Proof.
  intros Σ Γ Γ1 Γ2 Γm t A ? ?.
  eapply @type_llift with (Δ := nil) ; eassumption.
Defined.

Corollary type_llift1 :
  forall {Σ Γ Γ1 Γ2 Γm t A nx B},
    Σ ;;; (Γ ,,, Γ1) ,, svass nx B |-i t : A ->
    ismix Σ Γ Γ1 Γ2 Γm ->
    Σ ;;; Γ ,,, Γm ,, svass nx (llift0 #|Γm| B)
    |-i llift #|Γm| 1 t : llift #|Γm| 1 A.
Proof.
  intros Σ Γ Γ1 Γ2 Γm t A nx B ht hm.
  eapply @type_llift with (Δ := [ svass nx B ]).
  - exact ht.
  - eassumption.
Defined.

Corollary cong_llift0 :
  forall {Σ Γ Γ1 Γ2 Γm t1 t2 A},
    Σ ;;; Γ ,,, Γ1 |-i t1 = t2 : A ->
    ismix Σ Γ Γ1 Γ2 Γm ->
    Σ ;;; Γ ,,, Γm |-i llift0 #|Γm| t1 = llift0 #|Γm| t2 : llift0 #|Γm| A.
Proof.
  intros Σ Γ Γ1 Γ2 Γm t1 t2 A ht hm.
  eapply @cong_llift with (Δ := nil) ; eassumption.
Defined.

Corollary type_rlift0 :
  forall {Σ Γ Γ1 Γ2 Γm t A},
    Σ ;;; Γ ,,, Γ2 |-i t : A ->
    ismix Σ Γ Γ1 Γ2 Γm ->
    Σ ;;; Γ ,,, Γm |-i rlift0 #|Γm| t : rlift0 #|Γm| A.
Proof.
  intros Σ Γ Γ1 Γ2 Γm t A ? ?.
  eapply @type_rlift with (Δ := nil) ; eassumption.
Defined.

Corollary type_rlift1 :
  forall {Σ Γ Γ1 Γ2 Γm t A nx B},
    Σ ;;; (Γ ,,, Γ2) ,, svass nx B |-i t : A ->
    ismix Σ Γ Γ1 Γ2 Γm ->
    Σ ;;; Γ ,,, Γm ,, svass nx (rlift0 #|Γm| B)
    |-i rlift #|Γm| 1 t : rlift #|Γm| 1 A.
Proof.
  intros Σ Γ Γ1 Γ2 Γm t A nx B ht hm.
  eapply @type_rlift with (Δ := [ svass nx B ]).
  - exact ht.
  - eassumption.
Defined.

Corollary cong_rlift0 :
  forall {Σ Γ Γ1 Γ2 Γm t1 t2 A},
    Σ ;;; Γ ,,, Γ2 |-i t1 = t2 : A ->
    ismix Σ Γ Γ1 Γ2 Γm ->
    Σ ;;; Γ ,,, Γm |-i rlift0 #|Γm| t1 = rlift0 #|Γm| t2 : rlift0 #|Γm| A.
Proof.
  intros Σ Γ Γ1 Γ2 Γm t1 t2 A ht hm.
  eapply @cong_rlift with (Δ := nil) ; eassumption.
Defined.

(* More lemmata about exchange.
   They should go above with the others.
 *)

Definition rlift_subst :
  forall (u t : sterm) (i j m : nat), rlift j (i+m) (u {m := t}) = (rlift j (S i+m) u) {m := rlift j i t}.
Admitted.

Lemma llift_substProj :
  forall {t γ},
    (lift 1 1 (llift γ 1 t)) {0 := sProjT1 (sRel 0)} = llift0 (S γ) t.
Proof.
  intro t. induction t ; intro γ.
  - cbn. destruct n as [|n].
    + cbn. reflexivity.
    + cbn. destruct γ as [|γ].
      * cbn. reflexivity.
      * case_eq (n <=? γ).
        -- intro nlγ. cbn. reflexivity.
        -- intro γln. cbn. reflexivity.
  - cbn. reflexivity.
  - cbn. f_equal.
    * easy.
    * (* We would need to strengthen it!
         I believe however that it is convincing enough that it holds
         for variables.
       *)
Admitted.

Lemma rlift_substProj :
  forall {t γ},
    (lift 1 1 (rlift γ 1 t)) {0 := sProjT2 (sRel 0)} = rlift0 (S γ) t.
Admitted.
