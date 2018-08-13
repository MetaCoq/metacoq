From Coq Require Import Bool Program List Ascii String OrderedType.
Import ListNotations.
Open Scope string_scope.

Class Fuel := { fuel : nat }.

(** Such a useful tactic it should be part of the stdlib. *)
Ltac forward_gen H tac :=
  match type of H with
  | ?X -> _ => let H' := fresh in assert (H':X) ; [tac|specialize (H H'); clear H']
  end.

Tactic Notation "forward" constr(H) := forward_gen H ltac:(idtac).
Tactic Notation "forward" constr(H) "by" tactic(tac) := forward_gen H tac.

Record squash (A : Type) : Prop := { _ : A }.

Definition string_of_nat n :=
  match n with
  | 0 => "0"
  | 1 => "1"
  | 2 => "2"
  | 3 => "3"
  | 4 => "4"
  | 5 => "5"
  | 6 => "6"
  | 7 => "7"
  | 8 => "8"
  | 9 => "9"
  | 10 => "10"
  | 11 => "11"
  | 12 => "12"
  | 13 => "13"
  | 14 => "14"
  | 15 => "15"
  | 16 => "16"
  | 17 => "17"
  | 18 => "18"
  | 19 => "19"
  | 20 => "20"
  | 21 => "21"
  | 22 => "22"
  | 23 => "23"
  | 24 => "24"
  | 25 => "25"
  | 26 => "26"
  | 27 => "27"
  | 28 => "28"
  | 29 => "29"
  | 30 => "30"
  | 31 => "31"
  | 32 => "32"
  | 33 => "33"
  | 34 => "34"
  | 35 => "35"
  | 36 => "36"
  | 37 => "37"
  | 38 => "38"
  | 39 => "39"
  | 40 => "40"
  | 41 => "41"
  | 42 => "42"
  | 43 => "43"
  | 44 => "44"
  | 45 => "45"
  | 46 => "46"
  | 47 => "47"
  | 48 => "48"
  | 49 => "49"
  | _ => "todo string_of_nat"
  end.

Hint Resolve String.string_dec Peano_dec.eq_nat_dec : eq_dec.

Definition option_get {A} (default : A) (x : option A) : A
  := match x with
     | Some x => x
     | None => default
     end.

Fixpoint fold_left_i_aux {A B} (f : A -> nat -> B -> A) (n0 : nat) (l : list B)
         (a0 : A) {struct l} : A
  := match l with
     | [] => a0
     | b :: l => fold_left_i_aux f (S n0) l (f a0 n0 b)
     end.
Definition fold_left_i {A B} f := @fold_left_i_aux A B f 0.


Fixpoint map_i_aux {A B} (f : nat -> A -> B) (n0 : nat) (l : list A) : list B
  := match l with
     | [] => []
     | x :: l => (f n0 x) :: (map_i_aux f (S n0) l)
     end.
Definition map_i {A B} f := @map_i_aux A B f 0.


Section Forallb2.
  Context {A} (f : A -> A -> bool).

  Fixpoint forallb2 l l' :=
    match l, l' with
    | hd :: tl, hd' :: tl' => f hd hd' && forallb2 tl tl'
    | [], [] => true
    | _, _ => false
    end.
End Forallb2.

Program Fixpoint safe_nth {A} (l : list A) (n : nat | n < List.length l) : A :=
  match l with
  | nil => !
  | hd :: tl =>
    match n with
    | 0 => hd
    | S n => safe_nth tl n
    end
  end.
Next Obligation.
  simpl in H. inversion H.
Defined.
Next Obligation.
  simpl in H. auto with arith.
Defined.


Lemma nth_error_safe_nth {A} n (l : list A) (isdecl : n < Datatypes.length l) :
  nth_error l n = Some (safe_nth l (exist _ n isdecl)).
Proof.
  revert n isdecl; induction l; intros.
  - inversion isdecl.
  - destruct n as [| n']; simpl.
    reflexivity.
    simpl in IHl.
    simpl in isdecl.
    now rewrite <- IHl.
Qed.

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

Fact rev_cons :
  forall {A} {l} {a : A},
    rev (a :: l) = (rev l ++ [a])%list.
Proof.
  intro A.
  unfold rev.
  match goal with
  | |- forall l a, ?faux _ _ = _ => set (aux := faux)
  end.
  assert (h : forall l acc, aux l acc = (aux l [] ++ acc)%list).
  { intro l. induction l ; intro acc.
    - cbn. reflexivity.
    - cbn. rewrite (IHl [a]). rewrite IHl.
      change (a :: acc) with ([a] ++ acc)%list.
      auto with datatypes.
  }
  intros l a.
  apply h.
Defined.

Fact rev_map_cons :
  forall {A B} {f : A -> B} {l} {a : A},
    rev_map f (a :: l) = (rev_map f l ++ [f a])%list.
Proof.
  intros A B f.
  unfold rev_map.
  match goal with
  | |- forall l a, ?faux _ _ = _ => set (aux := faux)
  end.
  assert (h : forall l acc, aux l acc = (aux l [] ++ acc)%list).
  { intro l. induction l ; intro acc.
    - cbn. reflexivity.
    - cbn. rewrite (IHl [f a]). rewrite IHl.
      change (f a :: acc) with ([f a] ++ acc)%list.
      auto with datatypes.
  }
  intros l a.
  apply h.
Defined.

Fact rev_length :
  forall {A} {l : list A},
    List.length (rev l) = List.length l.
Proof.
  intro A.
  unfold rev.
  match goal with
  | |- context [ List.length (?faux _ _) ] => set (aux := faux)
  end.
  assert (h : forall l acc, List.length (aux l acc) = (List.length acc + List.length l)%nat).
  { intro l. induction l ; intro acc.
    - cbn. auto with arith.
    - cbn. rewrite IHl. cbn. auto with arith.
  }
  intro l. apply h.
Defined.

Fact rev_map_length :
  forall {A B} {f : A -> B} {l : list A},
    List.length (rev_map f l) = List.length l.
Proof.
  intros A B f.
  unfold rev_map.
  match goal with
  | |- context [ List.length (?faux _ _) ] => set (aux := faux)
  end.
  assert (h : forall l acc, List.length (aux l acc) =
                       (List.length acc + List.length l)%nat).
  { intro l. induction l ; intro acc.
    - cbn. auto with arith.
    - cbn. rewrite IHl. cbn. auto with arith.
  }
  intro l. apply h.
Defined.

Fact rev_map_app :
  forall {A B} {f : A -> B} {l1 l2},
    (rev_map f (l1 ++ l2) = rev_map f l2 ++ rev_map f l1)%list.
Proof.
  intros A B f l1 l2. revert B f l2.
  induction l1 ; intros B f l2.
  - simpl. cbn. rewrite app_nil_r. reflexivity.
  - simpl. rewrite !rev_map_cons. rewrite IHl1.
    rewrite app_assoc. reflexivity.
Defined.

(** Facts about booleans, characters and strings *)

Definition bool_compare (x y : bool) : comparison :=
  if x then if y then Eq else Gt else if y then Lt else Eq.

Definition bool_lt (x y : bool) :=
  if x then False else y = true.

Local Notation " x =? y " := (bool_compare x y) (at level 10).
Local Notation " c ?? y " := (match c with Eq => y | Lt => Lt | Gt => Gt end) (at level 100).

Definition bool_Compare (x y : bool) : Compare bool_lt eq x y.
Proof.
  destruct x, y.
  - apply EQ. reflexivity.
  - apply GT. reflexivity.
  - apply LT. reflexivity.
  - apply EQ. reflexivity.
Defined.

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
  destruct a, a'; simpl in *; try (reflexivity || discriminate).

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
