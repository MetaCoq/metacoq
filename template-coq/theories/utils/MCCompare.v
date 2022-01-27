From Coq Require Import OrderedType Ascii String.

(** Facts about booleans, characters and strings *)

Definition bool_compare (x y : bool) : comparison :=
  if x then if y then Eq else Gt else if y then Lt else Eq.

Definition bool_lt (x y : bool) :=
  if x then False else y = true.

Local Notation " c ?? y " := (match c with Eq => y | Lt => Lt | Gt => Gt end)
                               (at level 100).

Definition bool_Compare (x y : bool) : Compare bool_lt eq x y.
Proof.
  destruct x, y.
  - apply EQ. reflexivity.
  - apply GT. reflexivity.
  - apply LT. reflexivity.
  - apply EQ. reflexivity.
Defined.

Lemma transitive_bool_lt : Transitive (fun b b' => bool_compare b b' = Lt).
Proof.
  intros [] [] []; discriminate || reflexivity.
Qed.

Definition ascii_compare x y :=
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

Definition ascii_lt x y := ascii_compare x y = Lt.

Ltac tryone a a' H :=
  destruct a, a'; simpl in H; try (reflexivity || discriminate).

Lemma ascii_Compare_eq : forall x y, ascii_compare x y = Eq <-> x = y.
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

Lemma ascii_compare_Lt x y : ascii_compare x y = Gt <-> ascii_compare y x = Lt.
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

Definition ascii_Compare (x y : ascii) : Compare ascii_lt eq x y.
Proof.
  case_eq (ascii_compare x y).
  intros.
  - apply EQ.
    now apply ascii_Compare_eq.
  - intros. apply LT.
    destruct x as [a b c d e f g h].
    destruct y as [a' b' c' d' e' f' g' h'].
    unfold ascii_lt. apply H.
  - intros.
    apply GT. red. now apply ascii_compare_Lt.
Qed.

Local Ltac trd := cbn in *; try reflexivity; try discriminate.

Lemma transitive_ascii_lt : Transitive ascii_lt.
Proof.
  intros [a b c d e f g h] [a' b' c' d' e' f' g' h']
         [a'' b'' c'' d'' e'' f'' g'' h''].
  unfold ascii_lt, ascii_compare.
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

Fixpoint string_compare x y :=
  match x, y with
  | EmptyString, EmptyString => Eq
  | String a s, String b s' =>
    match ascii_compare a b with
    | Eq => string_compare s s'
    | Lt => Lt
    | Gt => Gt
    end
  | EmptyString, String _ _ => Lt
  | String _ _, EmptyString => Gt
  end.

Definition string_lt x y : Prop := string_compare x y = Lt.

Lemma string_compare_eq : forall x y : string, string_compare x y = Eq <-> eq x y.
Proof.
  split.
  induction x in y |- *.
  + destruct y. reflexivity.
    discriminate.
  + destruct y. discriminate.
    simpl. destruct (ascii_Compare a a0). red in a1. rewrite a1. discriminate.
    subst a0.
    pose (proj2 (ascii_Compare_eq a a) Logic.eq_refl).
    rewrite e. intros H. specialize (IHx _ H). rewrite IHx. reflexivity.
    red in a1. apply ascii_compare_Lt in a1. rewrite a1. discriminate.
  + intros ->.
    induction y. reflexivity.
    simpl. now rewrite (proj2 (ascii_Compare_eq a a) Logic.eq_refl).
Qed.

Lemma string_compare_lt : forall x y : string, string_compare x y = Lt <-> string_compare y x = Gt.
Proof.
  split.
  - induction x in y |- *.
    + destruct y. discriminate.
      reflexivity.
    + destruct y. discriminate.
      simpl. destruct (ascii_Compare a a0). red in a1. rewrite a1.
      apply ascii_compare_Lt in a1. rewrite a1. reflexivity.
      subst a0.
      pose (proj2 (ascii_Compare_eq a a) Logic.eq_refl).
      rewrite e. intros H. now specialize (IHx _ H).
      red in a1. rewrite a1. apply ascii_compare_Lt in a1. rewrite a1. discriminate.
  - induction x in y |- *.
    + destruct y. discriminate.
      reflexivity.
    + destruct y. discriminate.
      simpl. destruct (ascii_Compare a a0). red in a1. rewrite a1.
      apply ascii_compare_Lt in a1. rewrite a1. reflexivity.
      subst a0.
      pose (proj2 (ascii_Compare_eq a a) Logic.eq_refl).
      rewrite e. intros H. now specialize (IHx _ H).
      red in a1. rewrite a1. apply ascii_compare_Lt in a1. rewrite a1. discriminate.
Qed.

Definition string_Compare (x y : string) : Compare string_lt eq x y.
Proof.
  case_eq (string_compare x y); intros H.
  - apply EQ. now apply string_compare_eq.
  - apply LT; assumption.
  - apply GT. red. now apply string_compare_lt.
Qed.

#[local] Instance transitive_string_lt : Transitive string_lt.
Proof.
  red. unfold string_lt.
  intro s; induction s.
  - induction y; cbn.
    + intuition.
    + intros [|]. discriminate. reflexivity.
  - intros [|y1 y2]. discriminate.
    intros [|z1 z2]. discriminate.
    cbn. case_eq (ascii_compare a y1); try discriminate.
    + intro Ha; apply ascii_Compare_eq in Ha; subst.
      destruct (ascii_compare y1 z1); try discriminate.
      intros; eauto. reflexivity.
    + intros Ha _. case_eq (ascii_compare y1 z1); try discriminate.
      intros Hy1; apply ascii_Compare_eq in Hy1; subst. now rewrite Ha.
      intro Hy1. eapply transitive_ascii_lt in Ha.
      specialize (Ha Hy1). now rewrite Ha.
Qed.


Lemma CompareSpec_Proper : Proper (iff ==> iff ==> iff ==> Logic.eq ==> iff) CompareSpec.
  intros A A' HA B B' HB C C' HC c c' [].
  destruct c; split; inversion 1; constructor; intuition.
Qed.

Lemma CompareSpec_string s s'
  : CompareSpec (s = s') (string_lt s s') (string_lt s' s) (string_compare s s').
Proof.
  revert s'; induction s; intro s'; cbn.
  - destruct s'; constructor; reflexivity.
  - destruct s'. constructor; reflexivity.
    unfold string_lt. simpl.
    case_eq (ascii_compare a a0); intro H; try constructor.
    + apply ascii_Compare_eq in H; subst.
      rewrite (proj2 (ascii_Compare_eq a0 a0) eq_refl).
      eapply CompareSpec_Proper. 5: exact (IHs s').
      split; intro HH. now inversion HH. now subst.
      all: reflexivity.
    + reflexivity.
    + apply ascii_compare_Lt in H; now rewrite H.
Qed.

Lemma string_compare_Opp (x y : string) : string_compare x y = CompOpp (string_compare y x).
Proof.
  destruct (CompareSpec_string x y). subst.
  rewrite (proj2 (string_compare_eq _ _)); auto.
  rewrite (proj1 (string_compare_lt _ _)); auto.
  rewrite (proj2 (string_compare_lt _ _)); auto.
  red in H.
  now apply string_compare_lt.
Qed.

Definition ascii_lt_irreflexive : Irreflexive ascii_lt.
Proof.
  intro x. destruct x. unfold complement, ascii_lt; cbn.
  destruct b, b0, b1, b2, b3, b4, b5, b6; cbn; discriminate.
Qed.

Definition string_lt_irreflexive : Irreflexive string_lt.
Proof.
  intro x; induction x; intro X; inversion X.
  case_eq (ascii_compare a a).
  - intro e; rewrite e in H0; clear e. now apply IHx.
  - apply ascii_lt_irreflexive.
  - intro e; rewrite e in H0; clear e. discriminate.
Qed.

Lemma string_compare_trans (x y z : string) c : string_compare x y = c -> string_compare y z = c -> string_compare x z = c.
Proof.
  destruct (CompareSpec_string x y); subst; intros <-;
  destruct (CompareSpec_string y z); subst; try congruence.
  eapply transitivity in H0. 2:eassumption. now red in H0.
  eapply transitivity in H. 2:eassumption. red in H.
  now apply string_compare_lt in H.
Qed.