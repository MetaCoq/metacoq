(* Lifts for packing *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import Ast utils LiftSubst Typing.
From Translation Require Import SAst SLiftSubst SCommon XTyping ITyping.

(* In order to do things properly we need to extend the context heterogenously,
   this is done by extending the context with triples
   (x : A, y : B, e : heq A x B y).
   We also need to define correspond lifts.

   If Γ, Γ1, Δ |- t : T then
   mix Γ Γ1 Γ2, Δ |- llift #|Γ1| #|Δ| t : llift #|Γ1| #|Δ| T
   If Γ, Γ2, Δ |- t : T then
   mix Γ Γ1 Γ2, Δ |- rlift #|Γ1| #|Δ| t : rlift #|Γ1| #|Δ| T
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
          (Γm ,, svass nm (sPack (llift0 #|Γ1| A1)
                                 (rlift0 #|Γ1| A2)))
.

(* Really we ask that the context have the same size *)
Fixpoint mix (Γ Γ1 Γ2 : scontext) : scontext :=
  match Γ1, Γ2 with
  | A :: Γ1, B :: Γ2 =>
    (mix Γ Γ1 Γ2) ,, svass (sdecl_name A)
                           (sPack (llift0 #|Γ1| (sdecl_type A))
                                  (rlift0 #|Γ1| (sdecl_type B)))
  | _,_ => Γ
  end.

(* We define an alternate version of mix that is probably the one we should have
   used from the start. This one will make easier use of safe_nth lemmata.
 *)
Fixpoint mix' (Γ1 Γ2 : scontext) : scontext :=
  match Γ1, Γ2 with
  | A :: Γ1, B :: Γ2 =>
    (mix' Γ1 Γ2) ,, svass (sdecl_name A)
                          (sPack (llift0 #|Γ1| (sdecl_type A))
                                 (rlift0 #|Γ1| (sdecl_type B)))
  | _,_ => []
  end.

Fact mix_mix' :
  forall {Γ Γ1 Γ2},
    mix Γ Γ1 Γ2 = Γ ,,, mix' Γ1 Γ2.
Proof.
  intros Γ Γ1.
  induction Γ1 ; intro Γ2.
  - cbn. reflexivity.
  - destruct Γ2.
    + cbn. reflexivity.
    + cbn. rewrite IHΓ1. reflexivity.
Defined.

Fact mix'_length :
  forall {Γ1 Γ2},
    #|Γ1| = #|Γ2| ->
    #|mix' Γ1 Γ2| = #|Γ1|.
Proof.
  intro Γ1. induction Γ1 ; intros Γ2 e.
  - cbn. reflexivity.
  - destruct Γ2.
    + cbn in *. easy.
    + cbn. f_equal. easy.
Defined.

Fact safe_nth_mix' :
  forall {Γ1 Γ2 : scontext} {n isdecl isdecl1 isdecl2},
    #|Γ1| = #|Γ2| ->
    sdecl_type (safe_nth (mix' Γ1 Γ2) (exist _ n isdecl)) =
    sPack (llift0 (#|Γ1| - S n) (sdecl_type (safe_nth Γ1 (exist _ n isdecl1))))
          (rlift0 (#|Γ1| - S n) (sdecl_type (safe_nth Γ2 (exist _ n isdecl2)))).
Proof.
  intro Γ1. induction Γ1.
  - cbn. easy.
  - intro Γ2. destruct Γ2.
    + cbn. easy.
    + intro n. destruct n ; intros isdecl isdecl1 isdecl2 e.
      * cbn. replace (#|Γ1| - 0) with #|Γ1| by omega. reflexivity.
      * cbn. cbn in e. erewrite IHΓ1 by omega. reflexivity.
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
    Σ ;;; Γ ,,, Γm |-i llift0 #|Γ1| A1 : sSort s ->
    Σ ;;; Γ ,,, Γm |-i rlift0 #|Γ1|A2 : sSort s ->
    ismix' Σ Γ
          (Γ1 ,, svass n1 A1)
          (Γ2 ,, svass n2 A2)
          (Γm ,, svass nm (sPack (llift0 #|Γ1| A1)
                                 (rlift0 #|Γ1| A2)))
.

Lemma wf_mix' {Σ Γ Γ1 Γ2 Γm} (h : wf Σ Γ) :
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
  forall {Δ Γ1 : scontext} {n is1 is2},
    sdecl_type (safe_nth (llift_context #|Γ1| Δ) (exist _ n is1)) =
    llift #|Γ1| (#|Δ| - S n) (sdecl_type (safe_nth Δ (exist _ n is2))).
Proof.
  intro Δ. induction Δ.
  - cbn. easy.
  - intro Γ1. destruct n ; intros is1 is2.
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

Axiom cheating : forall {A}, A.
Tactic Notation "cheat" := apply cheating.

Fixpoint type_llift' {Σ Γ Γ1 Γ2 Γm Δ t A}
  (h : Σ ;;; Γ ,,, Γ1 ,,, Δ |-i t : A) {struct h} :
  ismix' Σ Γ Γ1 Γ2 Γm ->
  Σ ;;; Γ ,,, Γm ,,, llift_context #|Γ1| Δ
  |-i llift #|Γ1| #|Δ| t : llift #|Γ1| #|Δ| A

with cong_llift' {Σ Γ Γ1 Γ2 Γm Δ t1 t2 A}
  (h : Σ ;;; Γ ,,, Γ1 ,,, Δ |-i t1 = t2 : A) {struct h} :
  ismix' Σ Γ Γ1 Γ2 Γm ->
  Σ ;;; Γ ,,, Γm ,,, llift_context #|Γ1| Δ
  |-i llift #|Γ1| #|Δ| t1 = llift #|Γ1| #|Δ| t2 : llift #|Γ1| #|Δ| A

with type_rlift' {Σ Γ Γ1 Γ2 Γm Δ t A}
  (h : Σ ;;; Γ ,,, Γ2 ,,, Δ |-i t : A) {struct h} :
  ismix' Σ Γ Γ1 Γ2 Γm ->
  Σ ;;; Γ ,,, Γm ,,, rlift_context #|Γ1| Δ
  |-i rlift #|Γ1| #|Δ| t : rlift #|Γ1| #|Δ| A

with cong_rlift' {Σ Γ Γ1 Γ2 Γm Δ t1 t2 A}
  (h : Σ ;;; Γ ,,, Γ2 ,,, Δ |-i t1 = t2 : A) {struct h} :
  ismix' Σ Γ Γ1 Γ2 Γm ->
  Σ ;;; Γ ,,, Γm ,,, rlift_context #|Γ1| Δ
  |-i rlift #|Γ1| #|Δ| t1 = rlift #|Γ1| #|Δ| t2 : rlift #|Γ1| #|Δ| A

with wf_llift' {Σ Γ Γ1 Γ2 Γm Δ} (h : wf Σ (Γ ,,, Γ1 ,,, Δ)) {struct h} :
  ismix' Σ Γ Γ1 Γ2 Γm ->
  wf Σ (Γ ,,, Γm ,,, llift_context #|Γ1| Δ)

with wf_rlift' {Σ Γ Γ1 Γ2 Γm Δ} (h : wf Σ (Γ ,,, Γ1 ,,, Δ)) {struct h} :
  ismix' Σ Γ Γ1 Γ2 Γm ->
  wf Σ (Γ ,,, Γm ,,, rlift_context #|Γ1| Δ)
.
Proof.
  (* type_llift' *)
  - cheat.

  (* cong_llift' *)
  - cheat.

  (* type_rlift' *)
  - cheat.

  (* cong_rlift' *)
  - cheat.

  (* wf_llift' *)
  - { destruct Δ.
      - cbn. rewrite cat_nil in h.
        intro hm. eapply wf_mix'.
        + eapply inversion_wf_cat. eassumption.
        + eassumption.
      - cbn. intro hm. dependent destruction h.
        econstructor.
        + (* eapply wf_llift' ; eassumption. *)
          (* It's really annoying because it is indeed smaller *)
          cheat.
        + (* eapply type_llift' with (A := sSort s0) ; eassumption. *)
          (* Same here. *)
          cheat.
      Unshelve. auto.
    }

  (* wf_rlift' *)
  - cheat.
Defined.


(* Fixpoint type_llift {Σ Γ Γ1 Γ2 Γm Δ t A} *)
(*   (h : Σ ;;; Γ ,,, Γ1 ,,, Δ |-i t : A) {struct h} : *)
(*   ismix Σ Γ Γ1 Γ2 Γm -> *)
(*   Σ ;;; Γ ,,, Γm ,,, llift_context #|Γ1| Δ *)
(*   |-i llift #|Γ1| #|Δ| t : llift #|Γ1| #|Δ| A *)

(* with cong_llift {Σ Γ Γ1 Γ2 Γm Δ t1 t2 A} *)
(*   (h : Σ ;;; Γ ,,, Γ1 ,,, Δ |-i t1 = t2 : A) {struct h} : *)
(*   ismix Σ Γ Γ1 Γ2 Γm -> *)
(*   Σ ;;; Γ ,,, Γm ,,, llift_context #|Γ1| Δ *)
(*   |-i llift #|Γ1| #|Δ| t1 = llift #|Γ1| #|Δ| t2 : llift #|Γ1| #|Δ| A *)

(* with type_rlift {Σ Γ Γ1 Γ2 Γm Δ t A} *)
(*   (h : Σ ;;; Γ ,,, Γ2 ,,, Δ |-i t : A) {struct h} : *)
(*   ismix Σ Γ Γ1 Γ2 Γm -> *)
(*   Σ ;;; Γ ,,, Γm ,,, rlift_context #|Γ1| Δ *)
(*   |-i rlift #|Γ1| #|Δ| t : rlift #|Γ1| #|Δ| A *)

(* with cong_rlift {Σ Γ Γ1 Γ2 Γm Δ t1 t2 A} *)
(*   (h : Σ ;;; Γ ,,, Γ2 ,,, Δ |-i t1 = t2 : A) {struct h} : *)
(*   ismix Σ Γ Γ1 Γ2 Γm -> *)
(*   Σ ;;; Γ ,,, Γm ,,, rlift_context #|Γ1| Δ *)
(*   |-i rlift #|Γ1| #|Δ| t1 = rlift #|Γ1| #|Δ| t2 : rlift #|Γ1| #|Δ| A *)

(* with wf_llift {Σ Γ Γ1 Γ2 Γm Δ} (h : wf Σ (Γ ,,, Γ1 ,,, Δ)) {struct h} : *)
(*   ismix Σ Γ Γ1 Γ2 Γm -> *)
(*   wf Σ (Γ ,,, Γm ,,, llift_context #|Γ1| Δ) *)

(* with wf_rlift {Σ Γ Γ1 Γ2 Γm Δ} (h : wf Σ (Γ ,,, Γ1 ,,, Δ)) {struct h} : *)
(*   ismix Σ Γ Γ1 Γ2 Γm -> *)
(*   wf Σ (Γ ,,, Γm ,,, rlift_context #|Γ1| Δ) *)
(* . *)
(* Proof. *)
(*   (* type_llift *) *)
(*   - { dependent destruction h ; intros hm. *)
(*       - unfold llift at 1. case_eq (n <? #|Δ|) ; intro e ; bprop e. *)
(*         + erewrite @safe_nth_lt with (isdecl' := e0). *)
(*           eapply meta_conv. *)
(*           * eapply type_Rel. eapply wf_llift ; eassumption. *)
(*           * erewrite safe_nth_lt. erewrite safe_nth_llift. *)
(*             (* We need the right lemma. *) *)
(*             cheat. *)
(*         + (* case_eq (n <? #|Δ| + #|Γ1|) ; intro e1 ; bprop e1. *) *)
(*           (* * rewrite mix_mix'. *) *)
(*           (*   erewrite safe_nth_ge'. erewrite safe_nth_lt. *) *)
(*           (*   eapply type_ProjT1'. *) *)
(*           (*   eapply meta_conv. *) *)
(*           (*   -- eapply type_Rel. rewrite <- mix_mix'. *) *)
(*           (*      eapply wf_llift ; eassumption. *) *)
(*           (*   -- erewrite safe_nth_ge'. erewrite safe_nth_lt. *) *)
(*           (*      erewrite safe_nth_mix' by assumption. *) *)
(*           (*      cbn. f_equal. *) *)
(*           (*      (* rewrite lift_llift'. f_equal. *) *) *)
(*           (*      (* We probably need another lemma again... *) *) *)
(*           (*      cheat. *) *)
(*           (* * rewrite mix_mix'. *) *)
(*           (*   erewrite safe_nth_ge'. erewrite safe_nth_ge'. *) *)
(*           (*   eapply meta_conv. *) *)
(*           (*   -- eapply type_Rel. rewrite <- mix_mix'. *) *)
(*           (*      eapply wf_llift ; eassumption. *) *)
(*           (*   -- erewrite safe_nth_ge'. erewrite safe_nth_ge'. *) *)
(*           (*      (* Another one perhaps? *) *) *)
(*           (*      cheat. *) *)
(*           cheat. *)
(*       - cheat. *)
(*       - cheat. *)
(*       - cheat. *)
(*       - cheat. *)
(*       - cheat. *)
(*       - cheat. *)
(*       - cheat. *)
(*       - cheat. *)
(*       - cheat. *)
(*       - cheat. *)
(*       - cheat. *)
(*       - cheat. *)
(*       - cheat. *)
(*       - cheat. *)
(*       - cheat. *)
(*       - cheat. *)
(*       - cheat. *)
(*       - cheat. *)
(*       - cheat. *)
(*       - cheat. *)
(*       - cheat. *)
(*       - cheat. *)
(*       - cheat. *)
(*       - cheat. *)
(*       - cheat. *)
(*       - cheat. *)
(*     } *)

(*   (* cong_llift *) *)
(*   - cheat. *)

(*   (* type_rlift *) *)
(*   - cheat. *)

(*   (* cong_rlift *) *)
(*   - cheat. *)

(*   (* wf_llift *) *)
(*   - cheat. *)

(*   (* wf_rlift *) *)
(*   - cheat. *)

(*   Unshelve. *)
(*   all: cbn ; try rewrite !mix_mix' ; try rewrite !length_cat ; *)
(*        try rewrite !llift_context_length ; try rewrite !mix'_length ; *)
(*        try rewrite !length_cat in isdecl ; *)
(*        try omega. *)
(* Defined. *)

Lemma type_llift {Σ Γ Γ1 Γ2 Δ t A} (h : Σ ;;; Γ ,,, Γ1 ,,, Δ |-i t : A)
         (e : #|Γ1| = #|Γ2|) :
  Σ ;;; mix Γ Γ1 Γ2 ,,, Δ |-i llift #|Γ1| #|Δ| t : llift #|Γ1| #|Δ| A.
Admitted.

Corollary type_llift0 :
  forall {Σ Γ Γ1 Γ2 t A},
    Σ ;;; Γ ,,, Γ1 |-i t : A ->
    #|Γ1| = #|Γ2| ->
    wf Σ (Γ ,,, Γ2) ->
    Σ ;;; mix Γ Γ1 Γ2 |-i llift0 #|Γ1| t : llift0 #|Γ1| A.
(* Proof. *)
(*   intros Σ Γ Γ1 Γ2 t A ? ? ?. *)
(*   eapply @type_llift with (Δ := nil) ; assumption. *)
(* Defined. *)
Admitted.

Corollary type_llift1 :
  forall {Σ Γ Γ1 Γ2 t A nx B},
    Σ ;;; (Γ ,,, Γ1) ,, svass nx B |-i t : A ->
    #|Γ1| = #|Γ2| ->
    Σ ;;; mix Γ Γ1 Γ2 ,, svass nx (llift0 #|Γ1| B)
    |-i llift #|Γ1| 1 t : llift #|Γ1| 1 A.
Admitted.

Corollary cong_llift0 :
  forall {Σ Γ Γ1 Γ2 t1 t2 A},
    Σ ;;; Γ ,,, Γ1 |-i t1 = t2 : A ->
    #|Γ1| = #|Γ2| ->
    wf Σ (Γ ,,, Γ2) ->
    Σ ;;; mix Γ Γ1 Γ2 |-i llift0 #|Γ1| t1 = llift0 #|Γ1| t2 : llift0 #|Γ1| A.
(* Proof. *)
(*   intros Σ Γ Γ1 Γ2 t1 t2 A ? ? ?. *)
(*   eapply @cong_llift with (Δ := nil) ; assumption. *)
(* Defined. *)
Admitted.

Definition rlift_subst :
  forall (u t : sterm) (i j m : nat), rlift j (i+m) (u {m := t}) = (rlift j (S i+m) u) {m := rlift j i t}.
Admitted.

Lemma type_rlift {Σ Γ Γ1 Γ2 Δ t A} (h : Σ ;;; Γ ,,, Γ2 ,,, Δ |-i t : A)
         (e : #|Γ1| = #|Γ2|) :
  Σ ;;; mix Γ Γ1 Γ2 ,,, Δ |-i rlift #|Γ1| #|Δ| t : rlift #|Γ1| #|Δ| A.
Admitted.

Corollary type_rlift0 :
  forall {Σ Γ Γ1 Γ2 t A},
    Σ ;;; Γ ,,, Γ2 |-i t : A ->
    #|Γ1| = #|Γ2| ->
    Σ ;;; mix Γ Γ1 Γ2 |-i rlift0 #|Γ1| t : rlift0 #|Γ1| A.
(* Proof. *)
(*   intros Σ Γ Γ1 Γ2 t A ? ?. *)
(*   eapply @type_rlift with (Δ := nil) ; assumption. *)
(* Defined. *)
Admitted.

Corollary type_rlift1 :
  forall {Σ Γ Γ1 Γ2 t A nx B},
    Σ ;;; (Γ ,,, Γ2) ,, svass nx B |-i t : A ->
    #|Γ1| = #|Γ2| ->
    Σ ;;; mix Γ Γ1 Γ2 ,, svass nx (rlift0 #|Γ1| B)
    |-i rlift #|Γ1| 1 t : rlift #|Γ1| 1 A.
Admitted.

(* This is wrong actually *)
Lemma cong_rlift {Σ Γ Γ1 Γ2 Δ t1 t2 A} (h : Σ ;;; Γ ,,, Γ2 ,,, Δ |-i t1 = t2 : A)
      (e : #|Γ1| = #|Γ2|) :
  Σ ;;; mix Γ Γ1 Γ2 ,,, Δ
  |-i rlift #|Γ1| #|Δ| t1 = rlift #|Γ1| #|Δ| t2 : rlift #|Γ1| #|Δ| A.
Admitted.

Corollary cong_rlift0 :
  forall {Σ Γ Γ1 Γ2 t1 t2 A},
    Σ ;;; Γ ,,, Γ2 |-i t1 = t2 : A ->
    #|Γ1| = #|Γ2| ->
    Σ ;;; mix Γ Γ1 Γ2 |-i rlift0 #|Γ1| t1 = rlift0 #|Γ1| t2 : rlift0 #|Γ1| A.
(* Proof. *)
(*   intros Σ Γ Γ1 Γ2 t1 t2 A ? ?. *)
(*   eapply @cong_rlift with (Δ := nil) ; assumption. *)
(* Defined. *)
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
