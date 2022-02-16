From Coq Require Import ssreflect Extraction OrderedType Orders Ascii String.
From Equations Require Import Equations.

Lemma CompareSpec_Proper : Proper (iff ==> iff ==> iff ==> Logic.eq ==> iff) CompareSpec.
Proof.
  intros A A' HA B B' HB C C' HC c c' [].
  destruct c; split; inversion 1; constructor; intuition.
Qed.

Definition compare_cont (c : comparison) (d : comparison) : comparison :=
  match c with
  | Datatypes.Lt => Datatypes.Lt
  | Datatypes.Eq => d
  | Datatypes.Gt => Datatypes.Gt
  end.
Extraction Inline compare_cont.

Local Notation " c ?? y " := (compare_cont c y) (at level 100).

Lemma compare_cont_CompOpp p q : CompOpp (compare_cont p q) = compare_cont (CompOpp p) (CompOpp q).
Proof.
  destruct p, q; cbn => //.
Qed.

Definition comparison_trans p q :=
  match p, q with
  | Datatypes.Eq, c => Some c
  | c, Datatypes.Eq => Some c
  | Datatypes.Lt, Datatypes.Gt => None 
  | Datatypes.Gt, Datatypes.Lt => None
  | c, _ => Some c
  end.
  
Lemma compare_cont_trans {A} (cmp : A -> A -> comparison) :
  (forall c x y z, cmp x y = c -> cmp y z = c -> cmp x z = c) ->
  (forall x y, cmp x y = Datatypes.Eq -> x = y) ->
  forall c x y z q q' q'',
  (forall c, q = c -> q' = c -> q'' = c) ->
  compare_cont (cmp x y) q = c -> compare_cont (cmp y z) q' = c -> compare_cont (cmp x z) q'' = c.
Proof.
  intros Hc He c x y z q q' q'' Hqs.
  destruct (cmp x y) eqn:e.
  apply He in e. subst y.
  cbn. intros ->.
  destruct (cmp x z) eqn:e'; cbn.
  apply He in e'. subst z. now apply Hqs.
  all:auto.

  cbn. intros <-.
  destruct (cmp y z) eqn:e'; cbn.
  apply He in e'. subst z. rewrite e /= //. intros _.
  rewrite (Hc _ _ _ _ e e') /= //.
  discriminate. cbn. intros <-.
  destruct (cmp y z) eqn:e'; cbn => //.
  eapply He in e'; subst. intros ->. rewrite e //.
  intros _. rewrite (Hc _ _ _ _ e e') //.
Qed.

(** Facts about booleans, characters and strings *)

Module BoolOT <: UsualOrderedType. 
  Definition t := bool.

  Definition compare (x y : bool) : comparison :=
    if x then if y then Eq else Gt else if y then Lt else Eq.
  
  Definition lt (x y : bool) :=
    if x then False else y = true.
  
  Definition compare_spec (x y : bool) : CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
  Proof.
    destruct x, y.
    - constructor 1. reflexivity.
    - constructor 3. reflexivity.
    - constructor 2. reflexivity.
    - constructor 1. reflexivity.
  Defined.

  Definition eq : t -> t -> Prop := eq.
  Definition eq_equiv : Equivalence eq := _.

  Definition eq_dec (l1 l2 : t) : {l1 = l2}+{l1 <> l2}.
  Proof.
    decide equality.
  Defined.
  
  Definition lt_strorder : StrictOrder lt.
  Proof.
    constructor.
    - intros []; cbn; unfold lt, complement; congruence.
    - intros x y z.
      destruct x, y, z; cbn; try congruence; auto.
  Qed.

  Definition lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof.
    intros x y e z t e'. unfold eq in *; subst. reflexivity.
  Qed.

  (* Bonus *)
  Definition eqb (l1 l2 : t) : bool
    := match compare l1 l2 with Eq => true | _ => false end.
  
  Definition eq_leibniz (x y : t) : eq x y -> x = y := id.

End BoolOT.

Notation bool_compare := BoolOT.compare.

Local Ltac trd := cbn in *; try reflexivity; try discriminate.

Module AsciiOT <: UsualOrderedType.
  Definition t := ascii.

  Definition eq : t -> t -> Prop := eq.
  Definition eq_equiv : Equivalence eq := _.

  Definition compare x y :=
    let 'Ascii a b c d e f g h := x in
    let 'Ascii a' b' c' d' e' f' g' h' := y in
    bool_compare a a'
      ?? bool_compare b b'
      ?? bool_compare c c'
      ?? bool_compare d d'
      ?? bool_compare e e'
      ?? bool_compare f f'
      ?? bool_compare g g'
      ?? bool_compare h h'.

  Ltac tryone a a' H :=
    destruct a, a'; simpl in H; try (reflexivity || discriminate).

  Lemma compare_eq : forall x y, compare x y = Eq <-> x = y.
  Proof.
    destruct x as [a b c d e f g h].
    destruct y as [a' b' c' d' e' f' g' h'].
    split. intros H.
    tryone a a' H;
      tryone b b' H;
      tryone c c' H;
      tryone d d' H;
      tryone e e' H;
      tryone f f' H;
      tryone g g' H;
      tryone h h' H; reflexivity.
    intros H; injection H. intros; subst.
    destruct a', b', c', d', e', f', g', h'; reflexivity.
  Qed.

  Lemma compare_refl x : compare x x = Eq.
  Proof.
    now apply compare_eq.
  Qed.

  Lemma compare_Lt x y : compare x y = Gt <-> compare y x = Lt.
  Proof.
    destruct x as [a b c d e f g h].
    destruct y as [a' b' c' d' e' f' g' h'].
    split.
    intros H.
    tryone a a' H;
      tryone b b' H;
      tryone c c' H;
      tryone d d' H;
      tryone e e' H;
      tryone f f' H;
      tryone g g' H;
      tryone h h' H; try reflexivity.
    intros H.
    tryone a a' H;
      tryone b b' H;
      tryone c c' H;
      tryone d d' H;
      tryone e e' H;
      tryone f f' H;
      tryone g g' H;
      tryone h h' H; try reflexivity.
  Qed.

  Definition lt x y := compare x y = Lt.

  Definition compare_spec (x y : t) : CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
  Proof.
    case_eq (compare x y).
    intros.
    - constructor 1.
      now apply compare_eq.
    - intros. apply CompLt.
      destruct x as [a b c d e f g h].
      destruct y as [a' b' c' d' e' f' g' h'].
      unfold lt. apply H.
    - intros. apply CompGt. red. now apply compare_Lt.
  Qed.
  
  Lemma compare_sym (x y : t) : compare x y = CompOpp (compare y x).
  Proof.
    destruct (compare_spec x y).
    - red in H; subst. now rewrite compare_refl.
    - symmetry. rewrite (proj2 (compare_Lt _ _)); auto.
    - symmetry. rewrite (proj1 (compare_Lt _ _)); auto.
      now apply compare_Lt.
  Qed.
  
  Lemma lt_irreflexive : Irreflexive lt.
  Proof.
    intro x. destruct x. unfold complement, lt; cbn.
    destruct b, b0, b1, b2, b3, b4, b5, b6; cbn; discriminate.
  Qed.
  
  Lemma lt_transitive : Transitive lt.
  Proof.
    intros [a b c d e f g h] [a' b' c' d' e' f' g' h']
          [a'' b'' c'' d'' e'' f'' g'' h''].
    unfold lt, compare.
    intros H1 H2.
    destruct a, a', a''; trd;
    destruct b, b', b''; trd;
    destruct c, c', c''; trd;
    destruct d, d', d''; trd;
    destruct e, e', e''; trd;
    destruct f, f', f''; trd;
    destruct g, g', g''; trd;
    destruct h, h', h''; trd;
    eapply transitive_bool_lt; eassumption.
  Qed.

  Global Instance lt_strorder : StrictOrder lt.
  Proof.
    split.
    - apply lt_irreflexive.
    - apply lt_transitive.
  Qed.

  Definition lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof.
    unfold eq. intros x y e z t e'. subst; reflexivity.
  Qed.
 
  (* Bonus *)
 Definition eqb (l1 l2 : t) : bool
 := match compare l1 l2 with Eq => true | _ => false end.

  Definition eq_leibniz (x y : t) : eq x y -> x = y := id.

  Definition eq_dec (l1 l2 : t) : {l1 = l2}+{l1 <> l2}.
  Proof.
    destruct (compare l1 l2) eqn:e.
    apply compare_eq in e. now left.
    right; intros eq. destruct (compare_spec l1 l2); try discriminate. subst. now apply irreflexivity in H.
    right; intros eq. destruct (compare_spec l1 l2); try discriminate. subst. now apply irreflexivity in H.
  Defined.

End AsciiOT.

Notation ascii_compare := AsciiOT.compare.

Module StringOT <: UsualOrderedType.
  Definition t := string.

  Definition eq : t -> t -> Prop := eq.
  Definition eq_equiv : Equivalence eq := _.

  Fixpoint compare x y :=
    match x, y with
    | EmptyString, EmptyString => Eq
    | String a s, String b s' =>
      match ascii_compare a b with
      | Eq => compare s s'
      | Lt => Lt
      | Gt => Gt
      end
    | EmptyString, String _ _ => Lt
    | String _ _, EmptyString => Gt
    end.
  
  Definition lt x y : Prop := compare x y = Lt.
  
  Lemma compare_eq : forall x y : string, compare x y = Eq <-> eq x y.
  Proof.
    split.
    induction x in y |- *.
    + destruct y. reflexivity.
      discriminate.
    + destruct y. discriminate.
      simpl. destruct (AsciiOT.compare_spec a a0); red in H; subst; try discriminate.
      intros eq. red. f_equal; auto. now apply IHx.
    + intros ->.
      induction y. reflexivity.
      simpl. now rewrite AsciiOT.compare_refl.
  Qed.
  
  Lemma compare_refl x : compare x x = Eq.
  Proof.
    now apply compare_eq.
  Qed.

  Lemma compare_lt : forall x y : string, compare x y = Lt <-> compare y x = Gt.
  Proof.
    split.
    - induction x in y |- *.
      + destruct y. discriminate.
        reflexivity.
      + destruct y. discriminate.
        simpl. destruct (AsciiOT.compare_spec a a0); intros H'; red in H; subst; try discriminate.
        rewrite AsciiOT.compare_refl //; auto.
        apply AsciiOT.compare_Lt in H. now rewrite H.
    - induction x in y |- *.
      + destruct y. discriminate.
        reflexivity.
      + destruct y. discriminate.
        simpl. rewrite (AsciiOT.compare_sym a a0).
        destruct (AsciiOT.compare_spec a0 a); cbn; try congruence.
        auto.
  Qed.

  Definition compare_spec (x y : t) : CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
  Proof.
    case_eq (compare x y); intros H.
    - apply CompEq. now apply compare_eq.
    - apply CompLt; assumption.
    - apply CompGt. red. now apply compare_lt.
  Qed.
  
  #[local] Instance lt_transitive : Transitive lt.
  Proof.
    red. unfold lt.
    intro s; induction s.
    - induction y; cbn.
      + intuition.
      + intros [|]. discriminate. reflexivity.
    - intros [|y1 y2]. discriminate.
      intros [|z1 z2]. discriminate.
      cbn. case_eq (ascii_compare a y1); try discriminate.
      + intro Ha; apply AsciiOT.compare_eq in Ha; subst.
        destruct (ascii_compare y1 z1); try discriminate.
        intros; eauto. reflexivity.
      + intros Ha _. case_eq (ascii_compare y1 z1); try discriminate.
        intros Hy1; apply AsciiOT.compare_eq in Hy1; subst. now rewrite Ha.
        intro Hy1. eapply AsciiOT.lt_transitive in Ha.
        specialize (Ha Hy1). now rewrite Ha.
  Qed.
  
  Lemma compare_sym (x y : string) : compare x y = CompOpp (compare y x).
  Proof.
    destruct (compare_spec x y).
    - red in H; subst.
      rewrite (proj2 (compare_eq _ _)); auto. reflexivity.
    - rewrite (proj1 (compare_lt _ _)); auto.
    - rewrite (proj2 (compare_lt _ _)); auto.
      red in H.
      now apply compare_lt.
  Qed.
  
  Lemma compare_trans (x y z : string) c : compare x y = c -> compare y z = c -> compare x z = c.
  Proof.
    destruct (compare_spec x y); subst; intros <-;
    destruct (compare_spec y z); subst; try congruence.
    eapply transitivity in H0. 2:eassumption. red in H0. subst. now rewrite compare_refl.
    eapply transitivity in H0. 2:eassumption. now red in H0.
    eapply transitivity in H. 2:eassumption.
    now apply compare_lt in H.
  Qed.
  
  Definition lt_irreflexive : Irreflexive lt.
  Proof.
    intro x. red; unfold lt.
    now rewrite compare_refl.
  Qed.

  Global Instance lt_strorder : StrictOrder lt.
  Proof.
    split.
    - apply lt_irreflexive.
    - apply lt_transitive.
  Qed.

  Definition lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof.
    unfold eq. intros x y e z t e'. subst; reflexivity.
  Qed.
 
  (* Bonus *)
  Definition eqb (l1 l2 : t) : bool := 
    match compare l1 l2 with Eq => true | _ => false end.

  Definition eq_leibniz (x y : t) : eq x y -> x = y := id.

  Definition eq_dec (l1 l2 : t) : {l1 = l2}+{l1 <> l2}.
  Proof.
    destruct (compare l1 l2) eqn:e.
    apply compare_eq in e. now left.
    right; intros eq. destruct (compare_spec l1 l2); try discriminate. subst. now apply irreflexivity in H.
    right; intros eq. destruct (compare_spec l1 l2); try discriminate. subst. now apply irreflexivity in H.
  Defined.

End StringOT.

Notation string_compare := StringOT.compare.
Notation string_compare_eq := StringOT.compare_eq.
Notation CompareSpec_string := StringOT.compare_spec.

Module ListOrderedType (A : UsualOrderedType) <: UsualOrderedType. 
  Definition t := list A.t.
  Import List. Import ListNotations.

  Fixpoint compare (l1 l2 : t) : comparison :=
    match l1, l2 with
    | [], [] => Eq
    | hd :: tl, hd' :: tl' => compare_cont (A.compare hd hd') (compare tl tl')
    | [], _ :: _ => Lt
    | _, [] => Gt
    end.

  Definition eq : t -> t -> Prop := eq.
  Definition eq_equiv : Equivalence eq := _.

  Definition eq_dec (l1 l2 : t) : {l1 = l2}+{l1 <> l2}.
  Proof.
    decide equality. apply A.eq_dec.
  Defined.

  Inductive lt_ : t -> t -> Prop :=
  | lt_nil_cons hd tl : lt_ [] (hd :: tl)
  | lt_cons_cons_hd hd tl hd' tl' : A.lt hd hd' -> lt_ (hd :: tl) (hd' :: tl')
  | lt_cons_cons_tl hd tl tl' : lt_ tl tl' -> lt_ (hd :: tl) (hd :: tl').
  Derive Signature for lt_.
  Local Hint Constructors lt_ : core.

  Definition lt := lt_.

  Global Instance lt_strorder : StrictOrder lt.
  Proof.
    constructor.
    - intros x X. depind X.
      * now eapply irreflexivity in H.
      * now apply IHX.
    - intros x y z.
      induction 1 in z |- *.
      * intros H; depelim H; constructor.
      * intros H'; depelim H'; constructor; auto.
        now transitivity hd'.
      * intros H'; depelim H'.
        + constructor; auto.
        + constructor 3. now apply IHlt_.
  Qed.

  Global Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof.
    intros x y e z t e'. unfold eq in *; subst. reflexivity.
  Qed.

  Definition compare_spec :
    forall x y : t, CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
  Proof.
    induction x; destruct y; repeat constructor.
    cbn.
    destruct (A.compare_spec a t0); subst.
    - cbn. eapply CompareSpec_Proper.
      5: eapply IHx. 4: reflexivity.
      intuition auto; congruence.
      * intuition auto.
        { depelim H; auto. now apply irreflexivity in H. }
        { now constructor 3. }
      * intuition auto.
        { depelim H; auto. now apply irreflexivity in H. }
        { constructor 3; auto. }
    - cbn. repeat constructor; auto.
    - cbn. repeat constructor; auto.
  Qed.

  Lemma compare_eq x y : compare x y = Eq -> x = y.
  Proof.
    destruct (compare_spec x y); auto; congruence.
  Qed.

  Lemma compare_refl x : compare x x = Eq.
  Proof. destruct (compare_spec x x); auto; now apply irreflexivity in H. Qed.

  Lemma compare_sym x y : compare x y = CompOpp (compare y x).
  Proof.
    destruct (compare_spec x y);
    destruct (compare_spec y x); simpl; auto; subst; try congruence.
    all:try now apply irreflexivity in H.
    all:try now apply irreflexivity in H0.
    pose proof (transitivity H H0). now apply irreflexivity in H1.
    pose proof (transitivity H H0). now apply irreflexivity in H1.
  Qed.

  Lemma compare_lt_lt x y : compare x y = Lt <-> lt x y.
  Proof.
    split.
    - destruct (compare_spec x y); subst; try congruence.
    - intros hlt.
      destruct (compare_spec x y); subst; auto.
      * now apply irreflexivity in hlt.
      * eapply transitivity in H; eauto. now apply irreflexivity in H.
  Qed.

  Lemma compare_trans x y z c : compare x y = c -> compare y z = c -> compare x z = c.
  Proof.
    destruct (compare_spec x y); subst; intros <-;
    destruct (compare_spec y z); subst; try congruence.
    eapply transitivity in H0. 2:eassumption. intros _; now apply compare_lt_lt.
    eapply transitivity in H. 2:eassumption.
    apply compare_lt_lt in H. rewrite compare_sym H //.
  Qed.
  
  (* Bonus *)
  Definition eqb (l1 l2 : t) : bool
    := match compare l1 l2 with Eq => true | _ => false end.
  
  Definition eq_leibniz (x y : t) : eq x y -> x = y := id.

End ListOrderedType.

