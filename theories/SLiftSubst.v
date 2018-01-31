From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import Ast SAst LiftSubst.

(* Set Asymmetric Patterns. *)

Open Scope type_scope.

Fixpoint lift n k t : sterm :=
  match t with
  | sRel i => if Nat.leb k i then sRel (n + i) else sRel i
  | sLambda na T V M => sLambda na (lift n k T) (lift n (S k) V) (lift n (S k) M)
  | sApp u na A B v =>
    sApp (lift n k u) na (lift n k A) (lift n (S k) B) (lift n k v)
  | sProd na A B => sProd na (lift n k A) (lift n (S k) B)
  | sEq A u v => sEq (lift n k A) (lift n k u) (lift n k v)
  | sRefl A u => sRefl (lift n k A) (lift n k u)
  | sJ A u P w v p =>
    sJ (lift n k A)
       (lift n k u)
       (lift n (S (S k)) P)
       (lift n k w)
       (lift n k v)
       (lift n k p)
  | sTransport A B p t =>
    sTransport (lift n k A) (lift n k B) (lift n k p) (lift n k t)
  | sHeq A a B b =>
    sHeq (lift n k A) (lift n k a) (lift n k B) (lift n k b)
  | sHeqToEq p => sHeqToEq (lift n k p)
  | sHeqRefl A a => sHeqRefl (lift n k A) (lift n k a)
  | sHeqSym p => sHeqSym (lift n k p)
  | sHeqTrans p q => sHeqTrans (lift n k p) (lift n k q)
  | sHeqTransport p t => sHeqTransport (lift n k p) (lift n k t)
  | sCongProd B1 B2 pA pB =>
    sCongProd (lift n (S k) B1) (lift n (S k) B2)
              (lift n k pA) (lift n (S k) pB)
  | sCongLambda B1 B2 t1 t2 pA pB pt =>
    sCongLambda (lift n (S k) B1) (lift n (S k) B2)
                (lift n (S k) t1) (lift n (S k) t2)
                (lift n k pA) (lift n (S k) pB) (lift n (S k) pt)
  | sCongApp B1 B2 pu pA pB pv =>
    sCongApp (lift n (S k) B1) (lift n (S k) B2)
             (lift n k pu) (lift n k pA) (lift n (S k) pB) (lift n k pv)
  | sCongEq pA pu pv => sCongEq (lift n k pA) (lift n k pu) (lift n k pv)
  | sCongRefl pA pu => sCongRefl (lift n k pA) (lift n k pu)
  | sEqToHeq p => sEqToHeq (lift n k p)
  | sHeqTypeEq p => sHeqTypeEq (lift n k p)
  | sPack A1 A2 => sPack (lift n k A1) (lift n k A2)
  | sProjT1 p => sProjT1 (lift n k p)
  | sProjT2 p => sProjT2 (lift n k p)
  | sProjTe p => sProjTe (lift n k p)
  | sSort s => sSort s
  end.

Notation lift0 n t := (lift n 0 t).

Fixpoint subst t k u :=
  match u with
  | sRel n =>
    match nat_compare k n with
    | Datatypes.Eq => lift0 k t
    | Gt => sRel n
    | Lt => sRel (pred n)
    end
  | sLambda na T V M =>
    sLambda na (subst t k T) (subst t (S k) V) (subst t (S k) M)
  | sApp u na A B v =>
    sApp (subst t k u) na (subst t k A) (subst t (S k) B) (subst t k v)
  | sProd na A B => sProd na (subst t k A) (subst t (S k) B)
  | sEq A u v => sEq (subst t k A) (subst t k u) (subst t k v)
  | sRefl A u => sRefl (subst t k A) (subst t k u)
  | sJ A u P w v p =>
    sJ (subst t k A)
       (subst t k u)
       (subst t (S (S k)) P)
       (subst t k w)
       (subst t k v)
       (subst t k p)
  | sTransport A B p u =>
    sTransport (subst t k A) (subst t k B) (subst t k p) (subst t k u)
  | sHeq A a B b =>
    sHeq (subst t k A) (subst t k a) (subst t k B) (subst t k b)
  | sHeqToEq p => sHeqToEq (subst t k p)
  | sHeqRefl A a => sHeqRefl (subst t k A) (subst t k a)
  | sHeqSym p => sHeqSym (subst t k p)
  | sHeqTrans p q => sHeqTrans (subst t k p) (subst t k q)
  | sHeqTransport p u => sHeqTransport (subst t k p) (subst t k u)
  | sCongProd B1 B2 pA pB =>
    sCongProd (subst t (S k) B1) (subst t (S k) B2)
              (subst t k pA) (subst t (S k) pB)
  | sCongLambda B1 B2 t1 t2 pA pB pt =>
    sCongLambda (subst t (S k) B1) (subst t (S k) B2)
                (subst t (S k) t1) (subst t (S k) t2)
                (subst t k pA) (subst t (S k) pB) (subst t (S k) pt)
  | sCongApp B1 B2 pu pA pB pv =>
    sCongApp (subst t (S k) B1) (subst t (S k) B2)
             (subst t k pu) (subst t k pA) (subst t (S k) pB) (subst t k pv)
  | sCongEq pA pu pv => sCongEq (subst t k pA) (subst t k pu) (subst t k pv)
  | sCongRefl pA pu => sCongRefl (subst t k pA) (subst t k pu)
  | sEqToHeq p => sEqToHeq (subst t k p)
  | sHeqTypeEq p => sHeqTypeEq (subst t k p)
  | sPack A1 A2 => sPack (subst t k A1) (subst t k A2)
  | sProjT1 p => sProjT1 (subst t k p)
  | sProjT2 p => sProjT2 (subst t k p)
  | sProjTe p => sProjTe (subst t k p)
  | sSort s => sSort s
  end.

Notation subst0 t u := (subst t 0 u).
Notation "M { j := N }" := (subst N j M) (at level 10, right associativity) : s_scope.

Open Scope s_scope.

(* Lemmata regarding lifts and subst *)

Lemma lift_lift :
  forall t n m k,
    lift n k (lift m k t) = lift (n+m) k t.
Proof.
  intros t.
  induction t ; intros nn mm kk ; try (cbn ; f_equal ; easy).
  cbn. set (kkln := Nat.leb kk n).
  assert (eq : Nat.leb kk n = kkln) by reflexivity.
  destruct kkln.
  - cbn. set (kklmmn := kk <=? mm + n).
    assert (eq' : (kk <=? mm + n) = kklmmn) by reflexivity.
    destruct kklmmn.
    + auto with arith.
    + pose (h1 := leb_complete_conv _ _ eq').
      pose (h2 := leb_complete _ _ eq).
      omega.
  - cbn. rewrite eq. reflexivity.
Defined.

Lemma liftP1 :
  forall t i j k, lift k (j+i) (lift j i t) = lift (j+k) i t.
Proof.
  intro t.
  induction t ; intros i j k.
  all: try (cbn ; f_equal ; easy).
  all: try (cbn ; f_equal ;
            try replace (S (S (S (j+i))))%nat with (j + (S (S (S i))))%nat by omega ;
            try replace (S (S (j+i)))%nat with (j + (S (S i)))%nat by omega ;
            try replace (S (j+i))%nat with (j + (S i))%nat by omega ; easy).
  cbn. set (iln := i <=? n). assert (eq : (i <=? n) = iln) by reflexivity.
  destruct iln.
  + cbn. set (iln := j + i <=? j + n).
    assert (eq' : (j + i <=? j + n) = iln) by reflexivity.
    destruct iln.
    * f_equal. omega.
    * pose (h1 := leb_complete_conv _ _ eq').
      pose (h2 := leb_complete _ _ eq).
      omega.
  + cbn.
    assert (eq' : j + i <=? n = false).
    { apply leb_correct_conv.
      pose (h1 := leb_complete_conv _ _ eq).
      omega.
    }
    rewrite eq'. reflexivity.
Defined.

Lemma liftP2 :
  forall t i j k n,
    i <= n ->
    lift k (j+n) (lift j i t) = lift j i (lift k n t).
Proof.
  intro t.
  induction t ; intros i j k m H.
  all: try (cbn ; f_equal ; easy).
  all: try (cbn ; f_equal ;
            try replace (S (S (S (j + m))))%nat with (j + (S (S (S m))))%nat by omega ;
            try replace (S (S (j + m)))%nat with (j + (S (S m)))%nat by omega ;
            try replace (S (j + m))%nat with (j + (S m))%nat by omega ; easy).
  cbn. set (iln := i <=? n). assert (eq : (i <=? n) = iln) by reflexivity.
  set (mln := m <=? n). assert (eq' : (m <=? n) = mln) by reflexivity.
  destruct iln.
  + pose proof (leb_complete _ _ eq).
    destruct mln.
    * pose proof (leb_complete _ _ eq').
      cbn.
      assert (eq1 : j + m <=? j + n = true).
      { apply leb_correct.
        omega.
      }
      assert (eq2 : i <=? k + n = true).
      { apply leb_correct.
        omega.
      }
      rewrite eq1, eq2. f_equal. omega.
    * pose proof (leb_complete_conv _ _ eq').
      cbn.
      assert (eq1 : j + m <=? j + n = false).
      { apply leb_correct_conv.
        omega.
      }
      rewrite eq1, eq. reflexivity.
  + pose proof (leb_complete_conv _ _ eq).
    destruct mln.
    * pose proof (leb_complete _ _ eq').
      cbn.
      set (jmln := (j + m <=? n)).
      assert (eq0 : (j + m <=? n) = jmln) by reflexivity.
      set (ilkn := (i <=? k + n)).
      assert (eq1 : (i <=? k + n) = ilkn) by reflexivity.
      destruct jmln.
      -- pose proof (leb_complete _ _ eq0).
         destruct ilkn.
         ++ pose proof (leb_complete _ _ eq1).
            omega.
         ++ reflexivity.
      -- pose proof (leb_complete_conv _ _ eq0).
         omega.
    * cbn. rewrite eq.
      set (jmln := (j + m <=? n)).
      assert (eq0 : (j + m <=? n) = jmln) by reflexivity.
      destruct jmln.
      -- pose proof (leb_complete _ _ eq0).
         omega.
      -- reflexivity.
Defined.

Lemma lift_subst :
  forall {t n u},
    (lift 1 n t) {n := u} = t.
Proof.
  intro t.
  induction t ; intros m u.
  all: try (cbn ; f_equal ; easy).
  cbn. set (mln := m <=? n).
  assert (eq : (m <=? n) = mln) by reflexivity.
  destruct mln.
  - cbn.
    assert (eq' : (m ?= S n) = Lt).
    { apply Nat.compare_lt_iff.
      pose (h := leb_complete _ _ eq).
      omega.
    }
    rewrite eq'. reflexivity.
  - cbn.
    assert (eq' : (m ?= n) = Gt).
    { apply Nat.compare_gt_iff.
      pose (h := leb_complete_conv _ _ eq).
      omega.
    }
    rewrite eq'. reflexivity.
Defined.

Lemma lift00 :
  forall {t n}, lift 0 n t = t.
Proof.
  intros t. induction t ; intro m.
  all: cbn.
  all: repeat match goal with
           | H : forall n, _ = _ |- _ => rewrite H
           end.
  all: try reflexivity.
  destruct (m <=? n) ; reflexivity.
Defined.

Lemma liftP3 :
  forall t i k j n,
    i <= k ->
    k <= (i+n)%nat ->
    lift j k (lift n i t) = lift (j+n) i t.
Admitted.

Lemma substP2 :
  forall t u i j n,
    i <= n ->
    (lift j i t){ (j+n)%nat := u } = lift j i (t{ n := u }).
Proof.
  intros t.
  induction t ; intros u i j m h.
  all: try (cbn ; f_equal ;
            try replace (S (S (S (j + m))))%nat with (j + (S (S (S m))))%nat by omega ;
            try replace (S (S (j + m)))%nat with (j + (S (S m)))%nat by omega ;
            try replace (S (j + m))%nat with (j + (S m))%nat by omega ; easy).
  cbn.
  set (iln := i <=? n). assert (eq0 : (i <=? n) = iln) by reflexivity.
  set (men := m ?= n). assert (eq1 : (m ?= n) = men) by reflexivity.
  destruct iln.
  + pose proof (leb_complete _ _ eq0).
    destruct men.
    * pose proof (Nat.compare_eq _ _ eq1).
      subst. cbn.
      rewrite Nat.compare_refl.
      now rewrite liftP3 by omega.
    * pose proof (nat_compare_Lt_lt _ _ eq1).
      cbn.
      assert (eq2 : i <=? Init.Nat.pred n = true).
      { apply leb_correct. omega. }
      rewrite eq2.
      assert (eq3 : (j + m ?= j + n) = Lt).
      { apply nat_compare_lt. omega. }
      rewrite eq3.
      f_equal. omega.
    * pose proof (nat_compare_Gt_gt _ _ eq1).
      cbn. rewrite eq0.
      assert (eq3 : (j + m ?= j + n) = Gt).
      { apply nat_compare_gt. omega. }
      now rewrite eq3.
  + pose proof (leb_complete_conv _ _ eq0).
    destruct men.
    * pose proof (Nat.compare_eq _ _ eq1).
      subst. cbn.
      set (jnen := (j + n ?= n)).
      assert (eq2 : (j + n ?= n) = jnen) by reflexivity.
      destruct jnen.
      -- pose proof (Nat.compare_eq _ _ eq2).
         now rewrite liftP3.
      -- pose proof (nat_compare_Lt_lt _ _ eq2).
         omega.
      -- pose proof (nat_compare_Gt_gt _ _ eq2).
         omega.
    * pose proof (nat_compare_Lt_lt _ _ eq1).
      omega.
    * pose proof (nat_compare_Gt_gt _ _ eq1).
      cbn. set (jmen := (j + m ?= n)).
      assert (eq2 : (j + m ?= n) = jmen) by reflexivity.
      destruct jmen.
      -- pose proof (Nat.compare_eq _ _ eq2). omega.
      -- pose proof (nat_compare_Lt_lt _ _ eq2). omega.
      -- pose proof (nat_compare_Gt_gt _ _ eq2).
         rewrite eq0. reflexivity.
Defined.
