(* Lifts for packing *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import Ast SAst LiftSubst SLiftSubst SCommon Typing
                             XTyping ITyping.

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
  | sCongProd p q => sCongProd (llift γ δ p) (llift γ (S (S (S δ))) q)
  | sCongLambda pA pB pt =>
    sCongLambda (llift γ δ pA) (llift γ (S δ) pB) (llift γ (S δ) pt)
  | sCongApp pu pA pB pv =>
    sCongApp (llift γ δ pu) (llift γ δ pA) (llift γ (S δ) pB) (llift γ δ pv)
  | sCongEq pA pu pv => sCongEq (llift γ δ pA) (llift γ δ pu) (llift γ δ pv)
  | sCongRefl pA pu => sCongRefl (llift γ δ pA) (llift γ δ pu)
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
  | sCongProd pA pB => sCongProd (rlift γ δ pA) (rlift γ (S (S (S δ))) pB)
  | sCongLambda pA pB pt =>
    sCongLambda (rlift γ δ pA) (rlift γ (S δ) pB) (rlift γ (S δ) pt)
  | sCongApp pu pA pB pv =>
    sCongApp (rlift γ δ pu) (rlift γ δ pA) (rlift γ (S δ) pB) (rlift γ δ pv)
  | sCongEq pA pu pv => sCongEq (rlift γ δ pA) (rlift γ δ pu) (rlift γ δ pv)
  | sCongRefl pA pu => sCongRefl (rlift γ δ pA) (rlift γ δ pu)
  | sSort x => sSort x
  | sPack A B => sPack (rlift γ δ A) (rlift γ δ B)
  | sProjT1 x => sProjT1 (rlift γ δ x)
  | sProjT2 x => sProjT2 (rlift γ δ x)
  | sProjTe x => sProjTe (rlift γ δ x)
  end.

Notation rlift0 γ t := (rlift γ 0 t).

(* Really we ask that the context have the same size *)
Fixpoint mix (Γ Γ1 Γ2 : scontext) : scontext :=
  match Γ1, Γ2 with
  | A :: Γ1, B :: Γ2 =>
    (mix Γ Γ1 Γ2) ,, svass (sdecl_name A)
                           (sPack (llift0 #|Γ1| (sdecl_type A))
                                  (rlift0 #|Γ1| (sdecl_type B)))
  | _,_ => Γ
  end.

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

Fixpoint llift_context n (Δ:scontext) : scontext :=
  match Δ with nil => nil
          | A :: Δ => svass (sdecl_name A) (llift n #|Δ| (sdecl_type A)) ::  llift_context n Δ
  end.


Definition llift_subst :
  forall (u t : sterm) (i j m : nat), llift j (i+m) (u {m := t}) = (llift j (S i+m) u) {m := llift j i t}.
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
  (* missing the sRel case *)
  admit.
Admitted.

Fixpoint type_llift {Σ Γ Γ1 Γ2 Δ t A} (h : Σ ;;; Γ ,,, Γ1 ,,, Δ |-i t : A)
         (e : #|Γ1| = #|Γ2|)  :
  Σ ;;; mix Γ Γ1 Γ2 ,,, llift_context #|Γ1| Δ |-i llift #|Γ1| #|Δ| t : llift #|Γ1| #|Δ| A
with wf_llift {Σ Γ Γ1 Γ2 Δ} (wf1: wf Σ (Γ ,,, Γ1 ,,, Δ))
         (e : #|Γ1| = #|Γ2|) :
   wf Σ (mix Γ Γ1 Γ2 ,,, llift_context #|Γ1| Δ).
Proof.
  generalize dependent Γ2.
  unshelve refine (typing_rect Σ (fun Γgen t A _ =>
                           forall Γ Γ1 Δ, Γ ,,, Γ1 ,,, Δ = Γgen ->
                                          forall Γ2 : list scontext_decl, #|Γ1| = #|Γ2| ->  Σ;;; mix Γ Γ1 Γ2 ,,, llift_context #|Γ1| Δ  |-i llift #|Γ1| #|Δ| t : llift #|Γ1| #|Δ| A) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Γ ,,, Γ1 ,,, Δ ) t A h _ _ _ eq_refl); cbn in *; clear -type_llift wf_llift.
  (* dependent induction h; cbn in *.  *)
  - intros. destruct H. generalize dependent Γ2. generalize dependent Γ1. induction Δ; cbn.
    + induction Γ1; cbn in *.
      * intros. rewrite llift00. refine (type_Rel _ _ _ _ _); auto.
      * admit.
    + admit.
  - intros. destruct H. apply type_Sort.
    apply wf_llift; assumption.
  - intros. destruct H1. eapply type_Prod.
    apply H; try reflexivity; try assumption.
    apply (H0 Γ0 Γ1 (Δ ,, svass n t) eq_refl Γ2 H2).
  - intros. destruct H2. eapply type_Lambda.
    apply H; try reflexivity; try assumption.
    apply (H0 Γ0 Γ1 (Δ ,, svass n t) eq_refl Γ2 H3).
    apply (H1 Γ0 Γ1 (Δ ,, svass n t) eq_refl Γ2 H3).
  - intros. destruct H3.
    pose (llift_subst B u #|Δ| #|Γ1| 0).
    rewrite <- plus_n_O in *. rewrite e.
    cbn. clear e. rewrite <- plus_n_O in *. unshelve eapply type_App.
    exact s1. exact s2.
    apply (H Γ0 Γ1 Δ eq_refl Γ2 H4).
    apply (H0 Γ0 Γ1 (Δ ,, svass n A) eq_refl Γ2 H4).
    apply (H1 Γ0 Γ1 Δ eq_refl Γ2 H4).
    apply (H2 Γ0 Γ1 Δ eq_refl Γ2 H4).
  - intros. destruct H2.
    eapply type_Eq.
    apply (H Γ0 Γ1 Δ eq_refl Γ2 H3).
    apply (H0 Γ0 Γ1 Δ eq_refl Γ2 H3).
    apply (H1 Γ0 Γ1 Δ eq_refl Γ2 H3).
  - (* and so on **)
Abort.

Lemma type_llift {Σ Γ Γ1 Γ2 Δ t A} (h : Σ ;;; Γ ,,, Γ1 ,,, Δ |-i t : A)
         (e : #|Γ1| = #|Γ2|) :
  Σ ;;; mix Γ Γ1 Γ2 ,,, Δ |-i llift #|Γ1| #|Δ| t : llift #|Γ1| #|Δ| A.
Proof.
  dependent induction h.
  - case_eq #|Δ|.
    + intros eqδ.
      destruct Δ ; try (now inversion eqδ). cbn in *.
      case_eq #|Γ1|.
      * intros eqγ. cbn. rewrite llift00.
        replace (n+0)%nat with n by omega.
        destruct Γ1 ; try (now inversion eqγ).
        destruct Γ2 ; try (now inversion eqγ).
        cbn.
        eapply type_Rel.
        cbn in w. assumption.
      * intros m eqγ. cbn.
        case_eq (n <=? m).
        -- intro nlm. induction n.
           ++ cbn.
Admitted.

Corollary type_llift0 :
  forall {Σ Γ Γ1 Γ2 t A},
    Σ ;;; Γ ,,, Γ1 |-i t : A ->
    #|Γ1| = #|Γ2| ->
    Σ ;;; mix Γ Γ1 Γ2 |-i llift0 #|Γ1| t : llift0 #|Γ1| A.
Proof.
  intros Σ Γ Γ1 Γ2 t A ? ?.
  eapply @type_llift with (Δ := nil) ; assumption.
Defined.

Corollary type_llift1 :
  forall {Σ Γ Γ1 Γ2 t A nx B},
    Σ ;;; (Γ ,,, Γ1) ,, svass nx B |-i t : A ->
    #|Γ1| = #|Γ2| ->
    Σ ;;; mix Γ Γ1 Γ2 ,, svass nx (llift0 #|Γ1| B)
    |-i llift #|Γ1| 1 t : llift #|Γ1| 1 A.
Admitted.

Lemma cong_llift {Σ Γ Γ1 Γ2 Δ t1 t2 A} (h : Σ ;;; Γ ,,, Γ1 ,,, Δ |-i t1 = t2 : A)
      (e : #|Γ1| = #|Γ2|) :
  Σ ;;; mix Γ Γ1 Γ2 ,,, Δ
  |-i llift #|Γ1| #|Δ| t1 = llift #|Γ1| #|Δ| t2 : llift #|Γ1| #|Δ| A.
Admitted.

Corollary cong_llift0 :
  forall {Σ Γ Γ1 Γ2 t1 t2 A},
    Σ ;;; Γ ,,, Γ1 |-i t1 = t2 : A ->
    #|Γ1| = #|Γ2| ->
    Σ ;;; mix Γ Γ1 Γ2 |-i llift0 #|Γ1| t1 = llift0 #|Γ1| t2 : llift0 #|Γ1| A.
Proof.
  intros Σ Γ Γ1 Γ2 t1 t2 A ? ?.
  eapply @cong_llift with (Δ := nil) ; assumption.
Defined.

Lemma type_rlift {Σ Γ Γ1 Γ2 Δ t A} (h : Σ ;;; Γ ,,, Γ2 ,,, Δ |-i t : A)
         (e : #|Γ1| = #|Γ2|) :
  Σ ;;; mix Γ Γ1 Γ2 ,,, Δ |-i rlift #|Γ1| #|Δ| t : rlift #|Γ1| #|Δ| A.
Admitted.

Corollary type_rlift0 :
  forall {Σ Γ Γ1 Γ2 t A},
    Σ ;;; Γ ,,, Γ2 |-i t : A ->
    #|Γ1| = #|Γ2| ->
    Σ ;;; mix Γ Γ1 Γ2 |-i rlift0 #|Γ1| t : rlift0 #|Γ1| A.
Proof.
  intros Σ Γ Γ1 Γ2 t A ? ?.
  eapply @type_rlift with (Δ := nil) ; assumption.
Defined.

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
Proof.
  intros Σ Γ Γ1 Γ2 t1 t2 A ? ?.
  eapply @cong_rlift with (Δ := nil) ; assumption.
Defined.

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
