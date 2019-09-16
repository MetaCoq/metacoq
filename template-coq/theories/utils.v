From Coq Require Import Bool Program List Ascii String OrderedType Arith Lia Omega
     ssreflect Utf8.
Global Set Asymmetric Patterns.

Import ListNotations.

(* Use \sum to input ∑ in Company Coq (it is not a sigma Σ). *)
Notation "'∑' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p%type)) ..))
  (at level 200, x binder, right associativity,
   format "'[' '∑'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Notation "( x ; y )" := (@existT _ _ x y).
Notation "( x ; y ; z )" := (x ; ( y ; z)).
Notation "( x ; y ; z ; t )" := (x ; ( y ; (z ; t))).
Notation "( x ; y ; z ; t ; u )" := (x ; ( y ; (z ; (t ; u)))).
Notation "( x ; y ; z ; t ; u ; v )" := (x ; ( y ; (z ; (t ; (u ; v))))).
Notation "x .π1" := (@projT1 _ _ x) (at level 3, format "x '.π1'").
Notation "x .π2" := (@projT2 _ _ x) (at level 3, format "x '.π2'").

Notation "p .1" := (fst p)
  (at level 2, left associativity, format "p .1") : pair_scope.
Notation "p .2" := (snd p)
  (at level 2, left associativity, format "p .2") : pair_scope.
Open Scope pair_scope.

Notation "x × y" := (prod x y )(at level 80, right associativity).

Notation "#| l |" := (List.length l) (at level 0, l at level 99, format "#| l |").

Tactic Notation "destruct" "?" :=
  let E := fresh "E" in
  match goal with
    [ |- context[match ?X with _ => _ end]] => destruct X eqn:E
  | [ H : context[match ?X with _ => _ end] |- _] => destruct X eqn:E
  end.

Tactic Notation "destruct" "?" "in" hyp(H) :=
  let e := fresh "E" in
  match type of H with context [match ?x with _ => _ end] => destruct x eqn:e
  end.

Notation "'eta_compose'" := (fun g f x => g (f x)).

(* \circ *)
Notation "g ∘ f" := (eta_compose g f).

Tactic Notation "destruct" "?" :=
  let E := fresh "E" in
  match goal with
    [ |- context[match ?X with _ => _ end]] => destruct X eqn:E
  | [ H : context[match ?X with _ => _ end] |- _] => destruct X eqn:E
  end.

Tactic Notation "destruct" "?" "in" hyp(H) :=
  let e := fresh "E" in
  match type of H with context [match ?x with _ => _ end] => destruct x eqn:e
  end.

Tactic Notation "apply*" constr(H) "in" hyp(H')
  := apply H in H'; [..|apply H].

Ltac cbnr := cbn; try reflexivity.

(* This is an attempt to overcome the fact that auto/eauto *)
(* do not deal with products *)
Ltac rdestruct :=
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  | H : _ × _ |- _ => destruct H
  | H : sigT _ |- _ => destruct H
  | |- _ /\ _ => split
  | |- _ × _ => split
  | |- sigT _ => eexists
  end.

Notation "'precompose'" := (fun R f x y => R (f x) (f y)) (only parsing).

Definition transport {A} (P : A -> Type) {x y : A} (e : x = y) : P x -> P y
  := fun u => eq_rect x P u y e.

Notation "p # x" := (transport _ p x) (right associativity, at level 65).

(** We cannot use ssrbool as it breaks extraction. *)
Coercion is_true : bool >-> Sortclass.

Definition pred (A : Type) := A -> bool.

Lemma andb_and b b' : is_true (b && b') <-> is_true b /\ is_true b'.
Proof. apply andb_true_iff. Qed.

Lemma andP {b b'} : is_true (b && b') -> is_true b /\ is_true b'.
Proof. apply andb_and. Qed.

Ltac toProp :=
  repeat match goal with
  | H : is_true (_ && _) |- _ => apply andb_and in H; destruct H
  | |- context [is_true (_ && _)] => rewrite andb_and
  end.

(** "Incoherent" notion of equivalence, that we only apply to hProps actually. *)
Record isEquiv (A B : Type) :=
  { equiv : A -> B;
    equiv_inv : B -> A}.

Infix "<~>" := isEquiv (at level 90).

Record squash (A : Type) : Prop := sq { _ : A }.

Notation "∥ T ∥" := (squash T) (at level 10).
Arguments sq {_} _.

Ltac sq :=
  repeat match goal with
  | H : ∥ _ ∥ |- _ => destruct H
  end; try eapply sq.

Definition on_snd {A B C} (f : B -> C) (p : A * B) :=
  (fst p, f (snd p)).

Definition test_snd {A B} (f : B -> bool) (p : A * B) :=
  f (snd p).

Definition option_get {A} (default : A) (x : option A) : A
  := match x with
     | Some x => x
     | None => default
     end.

Definition on_some {A} (P : A -> Type) (o : option A) :=
  match o with
  | Some t => P t
  | None => False
  end.

Definition option_default {A B} (f : A -> B) (o : option A) (b : B) :=
  match o with Some x => f x | None => b end.

Definition on_rel {A B} (R : A -> A -> Prop) (f : B -> A) : B -> B -> Prop :=
  fun x y => R (f x) (f y).

Definition on_Trel {A B} (R : A -> A -> Type) (f : B -> A) : B -> B -> Type :=
  fun x y => R (f x) (f y).

Class Fuel := fuel : nat.

(** Such a useful tactic it should be part of the stdlib. *)
Ltac forward_gen H tac :=
  match type of H with
  | ?X -> _ => let H' := fresh in assert (H':X) ; [tac|specialize (H H'); clear H']
  end.

Ltac inv H := inversion_clear H.

Tactic Notation "forward" constr(H) := forward_gen H ltac:(idtac).
Tactic Notation "forward" constr(H) "by" tactic(tac) := forward_gen H tac.

Definition string_of_nat n : string :=
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

Fixpoint fold_left_i_aux {A B} (f : A -> nat -> B -> A) (n0 : nat) (l : list B)
         (a0 : A) {struct l} : A
  := match l with
     | [] => a0
     | b :: l => fold_left_i_aux f (S n0) l (f a0 n0 b)
     end.
Definition fold_left_i {A B} f := @fold_left_i_aux A B f 0.



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

Local Notation " c ?? y " := (match c with Eq => y | Lt => Lt | Gt => Gt end) (at level 100).

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

Ltac trd := cbn in *; try reflexivity; try discriminate.

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

Lemma transitive_string_lt : Transitive string_lt.
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



(** Combinators *)

(** Forall combinators in Type to allow building them by recursion *)
Inductive All (A : Type) (P : A -> Type) : list A -> Type :=
    All_nil : All A P []
  | All_cons : forall (x : A) (l : list A),
                  P x -> All A P l -> All A P (x :: l).
Arguments All {A} P l.

Inductive Alli {A} (P : nat -> A -> Type) (n : nat) : list A -> Type :=
| Alli_nil : Alli P n []
| Alli_cons hd tl : P n hd -> Alli P (S n) tl -> Alli P n (hd :: tl).

Inductive All2 {A B : Type} (R : A -> B -> Type) : list A -> list B -> Type :=
  All2_nil : All2 R [] []
| All2_cons : forall (x : A) (y : B) (l : list A) (l' : list B),
    R x y -> All2 R l l' -> All2 R (x :: l) (y :: l').

Inductive OnOne2 {A : Type} (P : A -> A -> Type) : list A -> list A -> Type :=
| OnOne2_hd hd hd' tl : P hd hd' -> OnOne2 P (hd :: tl) (hd' :: tl)
| OnOne2_tl hd tl tl' : OnOne2 P tl tl' -> OnOne2 P (hd :: tl) (hd :: tl').

Fixpoint mapi_rec {A B} (f : nat -> A -> B) (l : list A) (n : nat) : list B :=
  match l with
  | [] => []
  | hd :: tl => f n hd :: mapi_rec f tl (S n)
  end.

Definition mapi {A B} (f : nat -> A -> B) (l : list A) := mapi_rec f l 0.

Lemma on_snd_on_snd {A B C D} (f : C -> D) (g : B -> C) (d : A * B) :
  on_snd f (on_snd g d) = on_snd (fun x => f (g x)) d.
Proof.
  destruct d; reflexivity.
Qed.

Lemma snd_on_snd {A B C} (f : B -> C) (p : A * B) : snd (on_snd f p) = f (snd p).
Proof. destruct p; reflexivity. Qed.

Lemma compose_on_snd {A B C D} (f : C -> D) (g : B -> C) :
  compose (A:=A * B) (on_snd f) (on_snd g) = on_snd (compose f g).
Proof.
  reflexivity.
Qed.

Lemma map_map_compose :
  forall (A B C : Type) (f : A -> B) (g : B -> C) (l : list A),
    map g (map f l) = map (compose g f) l.
Proof. apply map_map. Qed.
Hint Unfold compose : terms.

Lemma map_id_f {A} (l : list A) (f : A -> A) :
  (forall x, f x = x) ->
  map f l = l.
Proof.
  induction l; intros; simpl; try easy.
  rewrite H. f_equal. eauto.
Qed.

Lemma forall_map_spec {A B} {l} {f g : A -> B} :
  Forall (fun x => f x = g x) l <->
  map f l = map g l.
Proof.
  split.
  induction 1; simpl; trivial.
  now rewrite IHForall H.
  induction l => /= // [=] Ha Hl; constructor; auto.
Qed.

Lemma forall_map_id_spec {A} {P : A -> Prop} {l} {f : A -> A} :
  Forall (fun x => f x = x) l <-> map f l = l.
Proof.
  rewrite -{3}(map_id l). apply forall_map_spec.
Qed.

Lemma on_snd_eq_spec {A B C} (f g : B -> C) (x : A * B) :
  f (snd x) = g (snd x) <->
  on_snd f x = on_snd g x.
Proof.
  case: x => /=; rewrite /on_snd /=. split; congruence.
Qed.

Section Reverse_Induction.
  Context {A : Type}.
  Lemma rev_list_ind :
    forall P:list A-> Type,
      P [] ->
        (forall (a:A) (l:list A), P (List.rev l) -> P (List.rev (a :: l))) ->
        forall l:list A, P (List.rev l).
  Proof.
    induction l; auto.
  Qed.

  Theorem rev_ind :
    forall P:list A -> Type,
      P [] ->
      (forall (x:A) (l:list A), P l -> P (l ++ [x])) -> forall l:list A, P l.
  Proof.
    intros.
    generalize (rev_involutive l).
    intros E; rewrite <- E.
    apply (rev_list_ind P).
    auto.

    simpl.
    intros.
    apply (X0 a (List.rev l0)).
    auto.
  Qed.

End Reverse_Induction.

Lemma forallb_Forall {A} (p : pred A) l
  : Forall (is_true ∘ p) l <-> is_true (forallb p l).
Proof.
  split.
  induction 1; rewrite /= // H IHForall //.
  induction l; rewrite /= //. move/andP => [pa pl].
  constructor; auto.
Qed.

Lemma skipn_nil :
  forall {A} n, @skipn A n [] = [].
Proof.
  intros A [| n] ; reflexivity.
Qed.

Lemma skipn_S {A} a (l : list A) n : skipn (S n) (a :: l) = skipn n l.
Proof. reflexivity. Qed.

(** Generic strategy for dealing with Forall/forall, etc:

    1) Move all boolean foralls into All/All2 (in the goal and the context).
    2) Merge all context Foralls into one
    3) Apply Forall implication
    4) optionally simplify and call eauto.
*)

Lemma Forall_mix {A} (P Q : A -> Prop) : forall l, Forall P l -> Forall Q l -> Forall (fun x => P x /\ Q x) l.
Proof.
  intros l Hl Hq. induction Hl; inv Hq; constructor; auto.
Qed.

Lemma Forall_skipn {A} (P : A -> Prop) n l : Forall P l -> Forall P (skipn n l).
Proof.
  intros H. revert n; induction H; intros n. rewrite skipn_nil; auto.
  destruct n; simpl.
  - rewrite /skipn. constructor; auto.
  - now auto.
Qed.

Lemma Forall_firstn {A} (P : A -> Prop) n l : Forall P l -> Forall P (firstn n l).
Proof.
  intros H. revert n; induction H; intros n. rewrite firstn_nil; auto.
  destruct n; simpl.
  - constructor; auto.
  - constructor; auto.
Qed.

Lemma forallb2_All2 {A : Type} {p : A -> A -> bool}
      {l l' : list A} :
  is_true (forallb2 p l l') -> All2 (fun x y => is_true (p x y)) l l'.
Proof.
  induction l in l' |- *; destruct l'; simpl; intros; try congruence.
  - constructor.
  - constructor. revert H; rewrite andb_and; intros [px pl]. auto.
    apply IHl. revert H; rewrite andb_and; intros [px pl]. auto.
Qed.

Lemma All2_forallb2 {A : Type} {p : A -> A -> bool}
      {l l' : list A} :
  All2 (fun x y => is_true (p x y)) l l' -> is_true (forallb2 p l l').
Proof.
  induction 1; simpl; intros; try congruence.
  rewrite andb_and. intuition auto.
Qed.

Lemma forallb2_app {A} (p : A -> A -> bool) l l' q q' :
  is_true (forallb2 p l l' && forallb2 p q q')
  -> is_true (forallb2 p (l ++ q) (l' ++ q')).
Proof.
  induction l in l' |- *; destruct l'; simpl; try congruence.
  move=> /andP[/andP[pa pl] pq]. now rewrite pa IHl // pl pq.
Qed.

Lemma All2_map {A B C D} (R : C -> D -> Type) (f : A -> C) (g : B -> D) l l' :
  All2 (fun x y => R (f x) (g y)) l l' -> All2 R (map f l) (map g l').
Proof. induction 1; simpl; constructor; try congruence. Qed.

Lemma All2_map_inv {A B C D} (R : C -> D -> Type) (f : A -> C) (g : B -> D) l l' :
  All2 R (map f l) (map g l') -> All2 (fun x y => R (f x) (g y)) l l'.
Proof. induction l in l' |- *; destruct l'; simpl;
         move=> H;inv H; try constructor; try congruence. eauto.
Qed.

(* Lemma All2_List_Forall_mix_left {A : Type} {P : A -> Prop} {Q : A -> A -> Prop} *)
(*       {l l' : list A} : *)
(*     Forall P l -> All2 Q l l' -> All2 (fun x y => P x /\ Q x y) l l'. *)
(* Proof. *)
(*   induction 2; simpl; intros; constructor. *)
(*   inv H; intuition auto. *)
(*   apply IHX. inv H; intuition auto. *)
(* Qed. *)

(* Lemma All2_List_Forall_mix_right {A : Type} {P : A -> Prop} {Q : A -> A -> Prop} *)
(*       {l l' : list A} : *)
(*     Forall P l' -> All2 Q l l' -> All2 (fun x y => P y /\ Q x y) l l'. *)
(* Proof. *)
(*   induction 2; simpl; intros; constructor. *)
(*   inv H; intuition auto. *)
(*   apply IHX. inv H; intuition auto. *)
(* Qed. *)

Lemma All2_All_mix_left {A B} {P : A -> Type} {Q : A -> B -> Type}
      {l : list A} {l' : list B} :
  All P l -> All2 Q l l' -> All2 (fun x y => (P x * Q x y)%type) l l'.
Proof.
  induction 2; simpl; intros; constructor.
  inv X; intuition auto.
  apply IHX0. inv X; intuition auto.
Qed.

Lemma All2_All_mix_right {A B} {P : B -> Type} {Q : A -> B -> Type}
      {l : list A} {l' : list B} :
  All P l' -> All2 Q l l' -> All2 (fun x y => (Q x y * P y)%type) l l'.
Proof.
  induction 2; simpl; intros; constructor.
  inv X; intuition auto.
  apply IHX0. inv X; intuition auto.
Qed.

Lemma Forall_All {A : Type} (P : A -> Prop) l :
  Forall P l -> All P l.
Proof.
  induction l; intros H; constructor; auto. inv H. auto.
  apply IHl. inv H; auto.
Qed.

Lemma All_Forall {A : Type} (P : A -> Prop) l :
  All P l -> Forall P l.
Proof. induction 1; constructor; auto. Qed.

Lemma forallb_All {A} (p : pred A) l : is_true (forallb p l) -> All (is_true ∘ p) l.
Proof.
  move/forallb_Forall. apply Forall_All.
Qed.

Lemma All_forallb {A} (p : pred A) l : All (is_true ∘ p) l -> is_true (forallb p l).
Proof.
  move/All_Forall. apply forallb_Forall.
Qed.

Lemma OnOne2_All_mix_left {A} {P : A -> A -> Type} {Q : A -> Type} {l l'} :
  All Q l -> OnOne2 P l l' -> OnOne2 (fun x y => (P x y * Q x)%type) l l'.
Proof.
  intros H; induction 1; constructor; try inv H; intuition.
Qed.

Lemma OnOne2_app {A} (P : A -> A -> Type) l tl tl' : OnOne2 P tl tl' -> OnOne2 P (l ++ tl) (l ++ tl').
Proof. induction l; simpl; try constructor; auto. Qed.

Lemma OnOne2_length {A} {P} {l l' : list A} : OnOne2 P l l' -> #|l| = #|l'|.
Proof. induction 1; simpl; congruence. Qed.

Lemma OnOne2_mapP {A B} {P} {l l' : list A} (f : A -> B) :
  OnOne2 (on_rel P f) l l' -> OnOne2 P (map f l) (map f l').
Proof. induction 1; simpl; constructor; try congruence. apply p. Qed.

Lemma OnOne2_map {A B} {P : B -> B -> Type} {l l' : list A} (f : A -> B) :
  OnOne2 (on_Trel P f) l l' -> OnOne2 P (map f l) (map f l').
Proof. induction 1; simpl; constructor; try congruence. apply p. Qed.

Lemma OnOne2_sym {A} (P : A -> A -> Type) l l' : OnOne2 (fun x y => P y x) l' l -> OnOne2 P l l'.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma OnOne2_exist {A} (P : A -> A -> Type) (Q : A -> A -> Type) l l' :
  OnOne2 P l l' ->
  (forall x y, P x y -> ∑ z, Q x z × Q y z) ->
  ∑ r, (OnOne2 Q l r × OnOne2 Q l' r).
Proof.
  intros H HPQ. induction H.
  - destruct (HPQ _ _ p). destruct p0.
    now exists (x :: tl); intuition constructor.
               - destruct IHOnOne2 as [r [? ?]].
                 now exists (hd :: r); intuition constructor.
Qed.

Lemma All_firstn {A} {P : A -> Type} {l} {n} : All P l -> All P (firstn n l).
Proof. intros HPL; induction HPL in n |- * ; simpl; destruct n; try econstructor; eauto. Qed.

Lemma All_skipn {A} {P : A -> Type} {l} {n} : All P l -> All P (skipn n l).
Proof. intros HPL; induction HPL in n |- * ; simpl; destruct n; try econstructor; eauto. Qed.

Lemma All_app {A} {P : A -> Type} {l l'} : All P (l ++ l') -> All P l * All P l'.
Proof.
  induction l; simpl; auto. intros. constructor; auto. constructor.
  intros. inv X. intuition auto. constructor; auto.
Qed.

Lemma All_app_inv {A} (P : A -> Type) l l' : All P l -> All P l' -> All P (l ++ l').
Proof.
  intros Hl Hl'. induction Hl. apply Hl'.
  constructor; intuition auto.
Qed.

Lemma All_mix {A} {P : A -> Type} {Q : A -> Type} {l} :
  All P l -> All Q l -> All (fun x => (P x * Q x)%type) l.
Proof. induction 1; intros Hq; inv Hq; constructor; auto. Qed.

Lemma All2_All_left {A B} {P : A -> B -> Type} {Q : A -> Type} {l l'} :
  All2 P l l' ->
  (forall x y, P x y -> Q x) ->
  All Q l.
Proof.
  intros HF H. induction HF; constructor; eauto.
Qed.

Lemma All2_All_right {A B} {P : A -> B -> Type} {Q : B -> Type} {l l'} :
  All2 P l l' ->
  (forall x y, P x y -> Q y) ->
  All Q l'.
Proof.
  intros HF H. induction HF; constructor; eauto.
Qed.

Lemma All2_right {A B} {P : B -> Type} {l : list A} {l'} :
  All2 (fun x y => P y) l l' -> All P l'.
Proof.
  induction 1; constructor; auto.
Qed.

Hint Constructors All All2.

Lemma All_rev_map {A B} (P : A -> Type) f (l : list B) : All (compose P f) l -> All P (rev_map f l).
Proof. induction 1. constructor. rewrite rev_map_cons. apply All_app_inv; auto. Qed.

Lemma All_rev (A : Type) (P : A -> Type) (l : list A) : All P l -> All P (List.rev l).
Proof.
  induction l using rev_ind. constructor. rewrite rev_app_distr.
  simpl. intros X; apply All_app in X as [? ?]. depelim a0; intuition auto.
Qed.

Lemma All_rev_inv {A} (P : A -> Type) (l : list A) : All P (List.rev l) -> All P l.
Proof.
  induction l using rev_ind. constructor.
  intros. rewrite rev_app_distr in X. simpl.
  apply All_app in X as [Allx Alll]. inv Allx.
   apply All_app_inv; intuition eauto.
Qed.

Lemma All_impl {A} {P Q} {l : list A} : All P l -> (forall x, P x -> Q x) -> All Q l.
Proof. induction 1; try constructor; intuition auto. Qed.

Lemma Alli_impl {A} {P Q} (l : list A) {n} : Alli P n l -> (forall n x, P n x -> Q n x) -> Alli Q n l.
Proof. induction 1; try constructor; intuition auto. Defined.

Lemma All_map {A B} {P : B -> Type} {f : A -> B} {l : list A} :
  All (compose P f) l -> All P (map f l).
Proof. induction 1; constructor; auto. Qed.

Lemma All_map_inv {A B} (P : B -> Prop) (f : A -> B) l : All P (map f l) -> All (compose P f) l.
Proof. induction l; intros Hf; inv Hf; try constructor; eauto. Qed.

Lemma All_nth_error :
  forall A P l i x,
    @All A P l ->
    nth_error l i = Some x ->
    P x.
Proof.
  intros A P l i x h e.
  induction h in i, x, e |- *.
  - destruct i. all: discriminate.
  - destruct i.
    + simpl in e. inversion e. subst. clear e.
      assumption.
    + simpl in e. eapply IHh in e.
      assumption.
Qed.

Lemma Alli_mix {A} {P : nat -> A -> Type} {Q : nat -> A -> Type} {n l} :
  Alli P n l -> Alli Q n l -> Alli (fun n x => (P n x * Q n x)%type) n l.
Proof. induction 1; intros Hq; inv Hq; constructor; auto. Qed.

Lemma Alli_All {A} {P : nat -> A -> Type} {Q : A -> Type} {l n} :
  Alli P n l ->
  (forall n x, P n x -> Q x) ->
  All Q l.
Proof. induction 1; constructor; eauto. Qed.

Lemma Alli_app {A} (P : nat -> A -> Type) n l l' : Alli P n (l ++ l') -> Alli P n l * Alli P (length l + n) l'.
Proof.
  induction l in n, l' |- *; intros H. split; try constructor. apply H.
  inversion_clear H. split; intuition auto. constructor; auto. eapply IHl; eauto.
  simpl. replace (S (#|l| + n)) with (#|l| + S n) by lia.
  eapply IHl; eauto.
Qed.

Lemma Alli_nth_error :
  forall A P k l i x,
    @Alli A P k l ->
    nth_error l i = Some x ->
    P (k + i) x.
Proof.
  intros A P k l i x h e.
  induction h in i, x, e |- *.
  - destruct i. all: discriminate.
  - destruct i.
    + simpl in e. inversion e. subst. clear e.
      replace (n + 0) with n by lia.
      assumption.
    + simpl in e. eapply IHh in e.
      replace (n + S i) with (S n + i) by lia.
      assumption.
Qed.

Lemma map_eq_inj {A B} (f g : A -> B) l: map f l = map g l ->
                                         All (fun x => f x = g x) l.
Proof.
  induction l. simpl. constructor. simpl. intros [=]. constructor; auto.
Qed.

Lemma mapi_ext_size {A B} (f g : nat -> A -> B) l k :
  (forall k' x, k' < k + #|l| -> f k' x = g k' x) ->
  mapi_rec f l k = mapi_rec g l k.
Proof.
  intros Hl. generalize (le_refl k). generalize k at 1 3 4.
  induction l in k, Hl |- *. simpl. auto.
  intros. simpl in *. erewrite Hl; try lia.
  f_equal. eapply (IHl (S k)); try lia. intros. apply Hl. lia.
Qed.

Lemma map_ext_size {A B} (f g : nat -> A -> B) l :
  (forall k x, k < #|l| -> f k x = g k x) ->
  mapi f l = mapi g l.
Proof.
  intros Hl. unfold mapi. apply mapi_ext_size. simpl. auto.
Qed.

Lemma forall_nth_error_All :
  forall {A} (P : A -> Type) l,
    (forall i x, nth_error l i = Some x -> P x) ->
    All P l.
Proof.
  intros A P l h.
  induction l.
  - constructor.
  - constructor.
    + specialize (h 0 a eq_refl). assumption.
    + eapply IHl. intros i x e. eapply (h (S i)). assumption.
Qed.

Lemma forall_nth_error_Alli :
  forall {A} (P : nat -> A -> Type) k l,
    (forall i x, nth_error l i = Some x -> P (k + i) x) ->
    Alli P k l.
Proof.
  intros A P k l h.
  induction l in k, h |- *.
  - constructor.
  - constructor.
    + specialize (h 0 a eq_refl). now rewrite Nat.add_0_r in h.
    + apply IHl. intros. specialize (h (S i) x H).
      simpl. now replace (S (k + i)) with (k + S i) by lia.
Qed.

Lemma Alli_mapi {A B} {P : nat -> B -> Type} (f : nat -> A -> B) k l :
  Alli (fun n a => P n (f n a)) k l <~>
       Alli P k (mapi_rec f l k).
Proof.
  split.
  { induction 1. simpl. constructor.
    simpl. constructor; eauto. }
  { induction l in k |- *. simpl. constructor.
    simpl. intros. depelim X. constructor; eauto. }
Qed.

Lemma Alli_shift {A} {P : nat -> A -> Type} k l :
  Alli (fun x => P (S x)) k l ->
  Alli P (S k) l.
Proof.
  induction 1; simpl; constructor; auto.
Qed.

Lemma Alli_rev {A} {P : nat -> A -> Type} k l :
  Alli P k l ->
  Alli (fun k' => P (Nat.pred #|l| - k' + k)) 0 (List.rev l).
Proof.
  revert k.
  induction l using rev_ind; simpl; intros; try constructor.
  eapply Alli_app in X. intuition.
  rewrite rev_app_distr. rewrite app_length.
  simpl. constructor.
  replace (Nat.pred (#|l| + 1) - 0) with #|l| by lia.
  depelim b. eauto. specialize (IHl _ a).
  eapply Alli_shift. eapply Alli_impl. eauto.
  simpl; intros.
  now replace (Nat.pred (#|l| + 1) - S n) with (Nat.pred #|l| - n) by lia.
Qed.

Lemma Alli_All_mix {A} {P : nat -> A -> Type} (Q : A -> Type) k l :
  Alli P k l -> All Q l -> Alli (fun k x => (P k x) * Q x)%type k l.
Proof.
  induction 1; constructor; try depelim X0; intuition auto.
Qed.

Lemma OnOne2_impl {A} {P Q} {l l' : list A} :
  OnOne2 P l l' ->
  (forall x y, P x y -> Q x y) ->
  OnOne2 Q l l'.
Proof.
  induction 1; constructor; intuition eauto.
Qed.

Ltac toAll :=
  match goal with
  | H : is_true (forallb _ _) |- _ => apply forallb_All in H

  | |- is_true (forallb _ _) => apply All_forallb

  | H : Forall _ ?x |- _ => apply Forall_All in H

  | |- Forall _ _ => apply All_Forall

  | H : is_true (forallb2 _ _ _) |- _ => apply forallb2_All2 in H

  | |- is_true (forallb2 _ _ _) => apply All2_forallb2

  | H : All _ ?x, H' : All _ ?x |- _ =>
    apply (All_mix H) in H'; clear H

  | H : Alli _ _ ?x, H' : Alli _ _ ?x |- _ =>
    apply (Alli_mix H) in H'; clear H

  | H : All _ ?x, H' : All2 _ ?x _  |- _ =>
    apply (All2_All_mix_left H) in H'; clear H

  | H : All _ ?x, H' : All2 _ _ ?x  |- _ =>
    apply (All2_All_mix_right H) in H'; clear H

  | |- All _ (map _ _) => apply All_map

  | H : All _ (map _ _) |- _ => apply All_map_inv in H

  | |- All _ (rev_map _ _) => apply All_rev_map

  | |- All _ (List.rev _) => apply All_rev

  | |- All2 _ (map _ _) (map _ _) => apply All2_map
  end.

Lemma All_map_eq {A B} {l} {f g : A -> B} :
  All (fun x => f x = g x) l ->
  map f l = map g l.
Proof.
  induction 1; simpl; trivial.
  now rewrite IHX p.
Qed.

Lemma All_map_id {A} {l} {f : A -> A} :
  All (fun x => f x = x) l ->
  map f l = l.
Proof.
  induction 1; simpl; trivial.
  now rewrite IHX p.
Qed.

Ltac All_map :=
  match goal with
    |- map _ _ = map _ _ => apply All_map_eq
  | |- map _ _ = _ => apply All_map_id
  end.

Lemma forall_forallb_map_spec {A B : Type} {P : A -> Prop} {p : A -> bool}
      {l : list A} {f g : A -> B} :
    Forall P l -> is_true (forallb p l) ->
    (forall x : A, P x -> is_true (p x) -> f x = g x) -> map f l = map g l.
Proof.
  induction 1; simpl; trivial.
  rewrite andb_and. intros [px pl] Hx.
  f_equal. now apply Hx. now apply IHForall.
Qed.

Lemma forall_forallb_forallb_spec {A : Type} {P : A -> Prop} {p : A -> bool}
      {l : list A} {f : A -> bool} :
    Forall P l -> is_true (forallb p l) ->
    (forall x : A, P x -> is_true (p x) -> is_true (f x)) -> is_true (forallb f l).
Proof.
  induction 1; simpl; trivial.
  rewrite !andb_and. intros [px pl] Hx. eauto.
Qed.

Lemma on_snd_test_spec {A B C} (P : B -> Type) (p : B -> bool) (f g : B -> C) (x : A * B) :
  P (snd x) -> (forall x, P x -> is_true (p x) -> f x = g x) ->
  is_true (test_snd p x) ->
  on_snd f x = on_snd g x.
Proof.
  intros. destruct x. unfold on_snd. simpl.
  now rewrite H; auto.
Qed.

Lemma Forall_map {A B} (P : B -> Prop) (f : A -> B) l : Forall (Program.Basics.compose P f) l -> Forall P (map f l).
Proof.
  induction 1; constructor; auto.
Qed.

Lemma Forall_map_inv {A B} (P : B -> Prop) (f : A -> B) l : Forall P (map f l) -> Forall (compose P f) l.
Proof. induction l; intros Hf; inv Hf; try constructor; eauto. Qed.

Lemma Forall_impl {A} {P Q : A -> Prop} {l} :
  Forall P l -> (forall x, P x -> Q x) -> Forall Q l.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma All2_impl {A B} {P Q : A -> B -> Type} {l l'} :
    All2 P l l' ->
    (forall x y, P x y -> Q x y) ->
    All2 Q l l'.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma Forall_app {A} (P : A -> Prop) l l' : Forall P (l ++ l') -> Forall P l /\ Forall P l'.
Proof.
  induction l; intros H. split; try constructor. apply H.
  inversion_clear H. split; intuition auto.
Qed.


Lemma firstn_map {A B} n (f : A -> B) l : firstn n (map f l) = map f (firstn n l).
Proof.
  revert l; induction n. reflexivity.
  destruct l; simpl in *; congruence.
Qed.

Lemma All_safe_nth {A} {P : A -> Type} {Γ n} (isdecl : n < length Γ) : All P Γ ->
   P (safe_nth Γ (exist _ n isdecl)).
Proof.
  induction 1 in n, isdecl |- *. simpl. bang.
  destruct n. simpl. auto.
  simpl in *. eapply IHX.
Qed.

Definition size := nat.

(* Lemma Alli_mapi {A B} (P : nat -> B -> Type) (f : nat -> A -> B) (l : list A) n : *)
(*   Alli (fun n x => P n (f n x)) n l -> Alli P n (mapi f l). *)
(* Proof. induction 1; constructor; auto. Qed. *)

Section All_size.
  Context {A} (P : A -> Type) (fn : forall x1, P x1 -> size).
  Fixpoint all_size {l1 : list A} (f : All P l1) : size :=
  match f with
  | All_nil => 0
  | All_cons x l px pl => fn _ px + all_size pl
  end.
End All_size.

Section Alli_size.
  Context {A} (P : nat -> A -> Type) (fn : forall n x1, P n x1 -> size).
  Fixpoint alli_size {l1 : list A} {n} (f : Alli P n l1) : size :=
  match f with
  | Alli_nil => 0
  | Alli_cons x l px pl => fn _ _ px + alli_size pl
  end.
End Alli_size.

Section All2_size.
  Context {A} (P : A -> A -> Type) (fn : forall x1 x2, P x1 x2 -> size).
  Fixpoint all2_size {l1 l2 : list A} (f : All2 P l1 l2) : size :=
  match f with
  | All2_nil => 0
  | All2_cons x y l l' rxy rll' => fn _ _ rxy + all2_size rll'
  end.
End All2_size.

Ltac close_Forall :=
  match goal with
  | H : Forall _ _ |- Forall _ _ => apply (Forall_impl H); clear H; simpl
  | H : All _ _ |- All _ _ => apply (All_impl H); clear H; simpl
  | H : OnOne2 _ _ _ |- OnOne2 _ _ _ => apply (OnOne2_impl H); clear H; simpl
  | H : All2 _ _ _ |- All2 _ _ _ => apply (All2_impl H); clear H; simpl
  | H : All2 _ _ _ |- All _ _ =>
    (apply (All2_All_left H) || apply (All2_All_right H)); clear H; simpl
  end.

Lemma All2_non_nil {A B} (P : A -> B -> Type) (l : list A) (l' : list B) :
  All2 P l l' -> l <> nil -> l' <> nil.
Proof.
  induction 1; congruence.
Qed.

Lemma map_ext {A B : Type} (f g : A -> B) (l : list A) :
  (forall x, f x = g x) ->
  map f l = map g l.
Proof.
  intros.
  induction l; trivial.
  intros. simpl. rewrite H. congruence.
Defined.

Require Import ssreflect.

Lemma map_skipn {A B} (f : A -> B) (l : list A) (n : nat) : map f (skipn n l) = skipn n (map f l).
Proof.
  elim: n l => l // IHn.
  by case => //.
Qed.

Lemma nth_error_map {A B} (f : A -> B) n l : nth_error (map f l) n = option_map f (nth_error l n).
Proof.
  elim: n l; case => // IHn l /=.
  - by case: l => //.
  - by case => //.
Qed.

Lemma map_nil {A B} (f : A -> B) (l : list A) : l <> [] -> map f l <> [].
Proof. induction l; simpl; congruence. Qed.
Hint Resolve map_nil : wf.

Inductive BoolSpecSet (P Q : Prop) : bool -> Set :=
    BoolSpecT : P -> BoolSpecSet P Q true | BoolSpecF : Q -> BoolSpecSet P Q false.

Lemma leb_spec_Set : forall x y : nat, BoolSpecSet (x <= y) (y < x) (x <=? y).
Proof.
  intros.
  destruct (Nat.leb_spec0 x y).
  now constructor.
  constructor. now lia.
Qed.

Lemma some_inj {A} {x y : A} : Some x = Some y -> x = y.
Proof.
  now intros [=].
Qed.

Inductive nth_error_Spec {A} (l : list A) (n : nat) : option A -> Type :=
| nth_error_Spec_Some x : nth_error l n = Some x -> n < length l -> nth_error_Spec l n (Some x)
| nth_error_Spec_None : length l <= n -> nth_error_Spec l n None.

Lemma mapi_rec_eqn {A B} (f : nat -> A -> B) (l : list A) a n :
  mapi_rec f (a :: l) n = f n a :: mapi_rec f l (S n).
Proof. simpl. f_equal. Qed.

Lemma nth_error_mapi_rec {A B} (f : nat -> A -> B) n k l :
  nth_error (mapi_rec f l k) n = option_map (f (n + k)) (nth_error l n).
Proof.
  induction l in n, k |- *.
  - destruct n; reflexivity.
  - destruct n; simpl.
    + reflexivity.
    + rewrite IHl. by rewrite <- Nat.add_succ_comm.
Qed.

Lemma nth_error_mapi {A B} (f : nat -> A -> B) n l :
  nth_error (mapi f l) n = option_map (f n) (nth_error l n).
Proof.
  unfold mapi; rewrite nth_error_mapi_rec.
  now rewrite -> Nat.add_0_r.
Qed.

Lemma nth_error_Some_length {A} {l : list A} {n t} : nth_error l n = Some t -> n < length l.
Proof. rewrite <- nth_error_Some. destruct (nth_error l n); congruence. Qed.

Lemma nth_error_Some_non_nil {A} (l : list A) (n : nat) (x : A) : nth_error l n = Some x -> l <> [].
Proof.
  destruct l, n; simpl; congruence.
Qed.

Lemma nth_error_spec {A} (l : list A) (n : nat) : nth_error_Spec l n (nth_error l n).
Proof.
  destruct nth_error eqn:Heq.
  constructor; auto. now apply nth_error_Some_length in Heq.
  constructor; auto. now apply nth_error_None in Heq.
Qed.

Lemma nth_error_app_left {A} (l l' : list A) n t : nth_error l n = Some t -> nth_error (l ++ l') n = Some t.
Proof. induction l in n |- *; destruct n; simpl; try congruence. auto. Qed.

Lemma nth_error_nil {A} n : nth_error (@nil A) n = None.
Proof. destruct n; auto. Qed.
Hint Rewrite @nth_error_nil.

Lemma nth_error_forall {A} {P : A -> Prop} {l : list A} {n x} :
  nth_error l n = Some x -> Forall P l -> P x.
Proof.
  intros Hnth HPl. induction HPl in n, Hnth |- *. destruct n; discriminate.
  revert Hnth. destruct n. now intros [= ->].
  intros H'; eauto.
Qed.

Lemma nth_error_all {A} {P : A -> Type} {l : list A} {n x} :
  nth_error l n = Some x -> All P l -> P x.
Proof.
  intros Hnth HPl. induction HPl in n, Hnth |- *. destruct n; discriminate.
  revert Hnth. destruct n. now intros [= ->].
  intros H'; eauto.
Qed.
Require Import Arith.
Lemma nth_error_alli {A} {P : nat -> A -> Type} {l : list A} {n x} {k} :
  nth_error l n = Some x -> Alli P k l -> P (k + n) x.
Proof.
  intros Hnth HPl. induction HPl in n, Hnth |- *.
  destruct n; discriminate.
  revert Hnth. destruct n. intros [= ->]. now rewrite Nat.add_0_r.
  intros H'; eauto. rewrite <- Nat.add_succ_comm. eauto.
Qed.

Fixpoint chop {A} (n : nat) (l : list A) :=
  match n with
  | 0 => ([], l)
  | S n =>
    match l with
    | hd :: tl =>
      let '(l, r) := chop n tl in
      (hd :: l, r)
    | [] => ([], [])
    end
  end.

Lemma nth_map {A} (f : A -> A) n l d :
  (d = f d) ->
  nth n (map f l) d = f (nth n l d).
Proof.
  induction n in l |- *; destruct l; simpl; auto.
Qed.

Definition on_pi2 {A B C} (f : B -> B) (p : A * B * C) : A * B * C :=
  (fst (fst p), f (snd (fst p)), snd p).

Lemma All_map_id' {A} {P : A -> Type} {l} {f} :
  All P l ->
  (forall x, P x -> f x = x) ->
  map f l = l.
Proof.
  induction 1; simpl; f_equal; intuition auto.
  f_equal; auto.
Qed.

Lemma Alli_mapi_spec {A B} {P : nat -> A -> Type} {l} {f g : nat -> A -> B} {n} :
  Alli P n l -> (forall n x, P n x -> f n x = g n x) ->
  mapi_rec f l n = mapi_rec g l n.
Proof.
  induction 1; simpl; trivial.
  intros Heq. rewrite Heq; f_equal; auto.
Qed.

Lemma Alli_mapi_id {A} {P : nat -> A -> Type} {l} {f} {n} :
  Alli P n l ->
  (forall n x, P n x -> f n x = x) ->
  mapi_rec f l n = l.
Proof.
  induction 1; simpl; f_equal; intuition auto.
  f_equal; eauto.
Qed.

Lemma Alli_map_id {A} {P : nat -> A -> Type} {l} {f} {n} :
  Alli P n l ->
  (forall n x, P n x -> f x = x) ->
  map f l = l.
Proof.
  induction 1; simpl; f_equal; intuition auto.
  f_equal; eauto.
Qed.

Lemma nlt_map {A B} (l : list A) (f : A -> B) (n : {n | n < length l }) : `n < length (map f l).
Proof. destruct n. simpl. now rewrite map_length. Defined.

Lemma map_def_safe_nth {A B} (l : list A) (n : {n | n < length l}) (f : A -> B) :
  f (safe_nth l n) = safe_nth (map f l) (exist _ (`n) (nlt_map l f n)).
Proof.
  destruct n.
  induction l in x, l0 |- *. simpl. bang.
  simpl. destruct x. reflexivity. simpl.
  rewrite IHl. f_equal. f_equal. pi.
Qed.

Lemma mapi_map {A B C} (f : nat -> B -> C) (l : list A) (g : A -> B) :
  mapi f (map g l) = mapi (fun i x => f i (g x)) l.
Proof.
  unfold mapi. generalize 0. induction l; simpl; congruence.
Qed.

Lemma map_mapi {A B C} (f : nat -> A -> B) (l : list A) (g : B -> C) :
  map g (mapi f l) = mapi (fun i x => g (f i x)) l.
Proof.
  unfold mapi. generalize 0. induction l; simpl; congruence.
Qed.

Lemma chop_map {A B} (f : A -> B) n l l' l'' :
  chop n l = (l', l'') -> chop n (map f l) = (map f l', map f l'').
Proof.
  induction n in l, l', l'' |- *; destruct l; try intros [= <- <-]; simpl; try congruence.
  destruct (chop n l) eqn:Heq. specialize (IHn _ _ _ Heq).
  intros [= <- <-]. now rewrite IHn. Qed.

Lemma chop_n_app {A} {l l' : list A} {n} : n = length l -> chop n (l ++ l') = (l, l').
Proof.
  intros ->. induction l; simpl; try congruence.
  now rewrite IHl.
Qed.

Lemma mapi_mapi {A B C} (g : nat -> A -> B) (f : nat -> B -> C) (l : list A) :
  mapi f (mapi g l) = mapi (fun n x => f n (g n x)) l.
Proof. unfold mapi. generalize 0. induction l; simpl; try congruence. Qed.

Lemma mapi_rec_ext {A B} (f g : nat -> A -> B) (l : list A) n :
  (forall k x, n <= k -> k < length l + n -> f k x = g k x) ->
  mapi_rec f l n = mapi_rec g l n.
Proof.
  intros Hfg. induction l in n, Hfg |- *; simpl; try congruence.
  intros. rewrite Hfg; simpl; try lia. f_equal.
  rewrite IHl; auto. intros. apply Hfg. simpl; lia. simpl. lia.
Qed.

Lemma mapi_ext {A B} (f g : nat -> A -> B) (l : list A) :
  (forall n x, f n x = g n x) ->
  mapi f l = mapi g l.
Proof. intros; now apply mapi_rec_ext. Qed.

Lemma mapi_rec_app {A B} (f : nat -> A -> B) (l l' : list A) n :
  (mapi_rec f (l ++ l') n = mapi_rec f l n ++ mapi_rec f l' (length l + n))%list.
Proof.
  induction l in n |- *; simpl; try congruence.
  rewrite IHl. f_equal. now rewrite <- Nat.add_succ_comm.
Qed.

Lemma mapi_app {A B} (f : nat -> A -> B) (l l' : list A) :
  (mapi f (l ++ l') = mapi f l ++ mapi (fun n x => f (length l + n) x) l')%list.
Proof.
  unfold mapi; rewrite mapi_rec_app.
  f_equal. generalize 0.
  induction l'; intros. reflexivity. rewrite mapi_rec_eqn.
  change (S (length l + n)) with (S (length l) + n).
  rewrite (Nat.add_succ_comm _ n). now rewrite IHl'.
Qed.

Lemma mapi_rec_Sk {A B} (f : nat -> A -> B) (l : list A) k :
  mapi_rec f l (S k) = mapi_rec (fun n x => f (S n) x) l k.
Proof.
  induction l in k |- *; simpl; congruence.
Qed.

Lemma rev_mapi_rec {A B} (f : nat -> A -> B) (l : list A) n k : k <= n ->
  List.rev (mapi_rec f l (n - k)) = mapi_rec (fun k x => f (Nat.pred (length l) + n - k) x) (List.rev l) k.
Proof.
  unfold mapi. revert n k.
  induction l using rev_ind; simpl; try congruence.
  intros. rewrite rev_unit. simpl.
  rewrite mapi_rec_app rev_app_distr; simpl. rewrite IHl; auto. simpl.
  rewrite app_length. simpl. f_equal. f_equal. lia. rewrite mapi_rec_Sk.
  apply mapi_rec_ext. intros. f_equal. rewrite List.rev_length in H1.
  rewrite Nat.add_1_r. simpl; lia.
Qed.

Lemma rev_mapi {A B} (f : nat -> A -> B) (l : list A) :
  List.rev (mapi f l) = mapi (fun k x => f (Nat.pred (length l) - k) x) (List.rev l).
Proof.
  unfold mapi. change 0 with (0 - 0) at 1.
  rewrite rev_mapi_rec; auto. now rewrite Nat.add_0_r.
Qed.

Lemma mapi_rec_rev {A B} (f : nat -> A -> B) (l : list A) n :
  mapi_rec f (List.rev l) n = List.rev (mapi (fun k x => f (length l + n - S k) x) l).
Proof.
  unfold mapi. revert n.
  induction l using rev_ind; simpl; try congruence.
  intros. rewrite rev_unit. simpl.
  rewrite IHl mapi_rec_app.
  simpl. rewrite rev_unit. f_equal.
  rewrite app_length. simpl. f_equal. lia.
  rewrite app_length. simpl.
  f_equal. eapply mapi_rec_ext. intros.
  f_equal. lia.
Qed.

Lemma mapi_rev {A B} (f : nat -> A -> B) (l : list A) :
  mapi f (List.rev l) = List.rev (mapi (fun k x => f (length l - S k) x) l).
Proof. unfold mapi at 1. rewrite mapi_rec_rev. now rewrite Nat.add_0_r. Qed.

Lemma mapi_rec_length {A B} (f : nat -> A -> B) (l : list A) n :
  length (mapi_rec f l n) = length l.
Proof. induction l in n |- *; simpl; try congruence. Qed.

Lemma mapi_length {A B} (f : nat -> A -> B) (l : list A) :
  length (mapi f l) = length l.
Proof. apply mapi_rec_length. Qed.

Lemma skipn_length {A} n (l : list A) : n <= length l -> length (skipn n l) = length l - n.
Proof.
  induction l in n |- *; destruct n; simpl; auto.
  intros. rewrite IHl; auto with arith.
Qed.

Lemma forallb_map {A B} (f : A -> B) (l : list A) p :
  forallb p (map f l) = forallb (compose p f) l.
Proof.
  induction l in p, f |- *; unfold compose; simpl; rewrite ?andb_and;
    intuition (f_equal; auto). apply IHl.
Qed.

Lemma All_forallb' {A} P (l : list A) (p : pred A) :
  All P l ->
  (forall x, P x -> is_true (p x)) ->
  is_true (forallb p l).
Proof.
  induction 1 in p |- *; unfold compose; simpl; rewrite ?andb_and;
    intuition auto.
Qed.

Lemma forallb_Forall' {A} (P : A -> Prop) (l : list A) p :
  is_true (forallb p l) ->
  (forall x, is_true (p x) -> P x) ->
  Forall P l.
Proof.
  induction l in p |- *; unfold compose; simpl. constructor.
  intros. constructor; eauto; rewrite -> andb_and in H; intuition eauto.
Qed.

Lemma forallb_skipn {A} (p : A -> bool) n l :
  is_true (forallb p l) ->
  is_true (forallb p (skipn n l)).
Proof.
  induction l in n |- *; destruct n; simpl; try congruence.
  intros. apply IHl. rewrite -> andb_and in H; intuition.
Qed.

Lemma forallb_rev {A} (p : A -> bool) l :
  forallb p (List.rev l) = forallb p l.
Proof.
  induction l using rev_ind; simpl; try congruence.
  rewrite rev_unit forallb_app. simpl. rewrite <- IHl.
  now rewrite andb_comm andb_true_r.
Qed.

Lemma Forall_forallb_eq_forallb {A} (P : A -> Prop) (p q : A -> bool) l :
  Forall P l ->
  (forall x, P x -> p x = q x) ->
  forallb p l = forallb q l.
Proof.
  induction 1; simpl; intuition (f_equal; auto).
Qed.

Lemma forallb2_length {A} (p : A -> A -> bool) l l' : is_true (forallb2 p l l') -> length l = length l'.
Proof.
  induction l in l' |- *; destruct l'; simpl; try congruence.
  rewrite !andb_and. intros [Hp Hl]. erewrite IHl; eauto.
Qed.


Fixpoint map_option_out {A} (l : list (option A)) : option (list A) :=
  match l with
  | nil => Some nil
  | hd :: tl => match hd, map_option_out tl with
                | Some hd, Some tl => Some (hd :: tl)
                | _, _ => None
                end
  end.

Lemma map_option_out_map_option_map {A} (l : list (option A)) (f : A -> A) :
  map_option_out (map (option_map f) l) =
  option_map (map f) (map_option_out l).
Proof.
  induction l; simpl; auto.
  destruct (option_map f a) eqn:fa.
  rewrite IHl. destruct (map_option_out l). simpl in *.
  destruct a; simpl in *; congruence.
  simpl. destruct a; reflexivity.
  destruct a; simpl in *; congruence.
Qed.

Lemma Alli_map_option_out_mapi_Some_spec {A B} (f g : nat -> A -> option B) l t P :
  Alli P 0 l ->
  (forall i x t, P i x -> f i x = Some t -> g i x = Some t) ->
  map_option_out (mapi f l) = Some t ->
  map_option_out (mapi g l) = Some t.
Proof.
  unfold mapi. generalize 0.
  move => n Ha Hfg. move: t.
  induction Ha; try constructor; auto.
  move=> t /=. case E: (f n hd) => [b|]; try congruence.
  rewrite (Hfg n _ _ p E).
  case E' : map_option_out => [b'|]; try congruence.
  move=> [= <-]. now rewrite (IHHa _ E').
Qed.

Lemma combine_map_id {A B} (l : list (A * B)) :
 l = combine (map fst l) (map snd l).
Proof.
  induction l ; simpl; try easy.
  destruct a. now f_equal.
Qed.

Lemma Forall_forallb {A} P (l : list A) (p : pred A) :
  Forall P l ->
  (forall x, P x -> is_true (p x)) ->
  is_true (forallb p l).
Proof.
  induction 1 in p |- *; unfold compose; simpl; rewrite ?andb_and;
    intuition auto.
Qed.

Lemma Forall2_right {A B} (P : B -> Prop) (l : list A) (l' : list B) :
  Forall2 (fun x y => P y) l l' -> List.Forall (fun x => P x) l'.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma Forall2_non_nil {A B} (P : A -> B -> Prop) (l : list A) (l' : list B) :
  Forall2 P l l' -> l <> nil -> l' <> nil.
Proof.
  induction 1; congruence.
Qed.

Lemma Forall2_length {A B} {P : A -> B -> Prop} {l l'} : Forall2 P l l' -> #|l| = #|l'|.
Proof. induction 1; simpl; auto. Qed.

Lemma Forall2_app_r {A} (P : A -> A -> Prop) l l' r r' : Forall2 P (l ++ [r]) (l' ++ [r']) ->
                                                         (Forall2 P l l') /\ (P r r').
Proof.
  induction l in l', r |- *. simpl. intros. destruct l'. simpl in *.
  depelim H; intuition auto.
  depelim H. destruct l'; depelim H0.
  intros.
  depelim l'; depelim H. destruct l; depelim H0.
  specialize (IHl _ _ H0). intuition auto.
Qed.

Lemma Forall2_map_inv :
  forall {A B A' B'} (R : A' -> B' -> Prop) (f : A -> A')
    (g : B -> B') (l : list A) (l' : list B),
    Forall2 R (map f l) (map g l') ->
    Forall2 (fun x => R (f x) ∘ g) l l'.
Proof.
  intros A B A' B' R f g l l' h.
  induction l in l', h |- * ; destruct l' ; try solve [ inversion h ].
  - constructor.
  - constructor.
    + inversion h. subst. assumption.
    + eapply IHl. inversion h. assumption.
Qed.

Lemma All2_app_inv : forall (A B : Type) (R : A -> B -> Type),
    forall l l1 l2, All2 R (l1 ++ l2) l -> { '(l1',l2') : _ & (l = l1' ++ l2')%list * (All2 R l1 l1') * (All2 R l2 l2')}%type.
Proof.
  intros. revert l2 l X. induction l1; intros; cbn in *.
  - exists ([], l). eauto.
  - inversion X. subst.
    eapply IHl1 in X1 as ( [] & ? & ?). destruct p.  subst.
    eexists (y :: l, l0). repeat split; eauto.
Qed.

Lemma All2_ind_rev : forall (A B : Type) (R : A -> B -> Type) (P : forall (l : list A) (l0 : list B), Prop),
    P [] [] ->
    (forall (x : A) (y : B) (l : list A) (l' : list B) (r : R x y) (a : All2 R l l'),
        P l l' -> P (l ++ [x])%list (l' ++ [y]))%list ->
    forall (l : list A) (l0 : list B) (a : All2 R l l0), P l l0.
Proof.
  intros. revert l0 a. induction l using rev_ind; cbn; intros.
  - inv a. eauto.
  - eapply All2_app_inv in a as ([] & [[]]). subst.
    inv a0. inv X0. eauto.
Qed.

Ltac invs H := inversion H; subst; clear H.

Lemma last_inv A (l1 l2 : list A) x y :
  (l1 ++ [x] = l2 ++ [y] -> l1 = l2 /\ x = y)%list.
Proof.
  revert l2. induction l1; cbn; intros.
  - destruct l2; cbn in H; invs H. eauto. destruct l2; invs H2.
  - destruct l2; invs H. destruct l1; invs H2.
    eapply IHl1 in H2 as []. split; congruence.
Qed.

Lemma All2_app :
  forall (A B : Type) (R : A -> B -> Type),
  forall l1 l2 l1' l2',
    All2 R l1 l1' ->
    All2 R l2 l2' ->
    All2 R (l1 ++ l2) (l1' ++ l2').
Proof.
  induction 1 ; cbn ; eauto.
Qed.

Lemma All2_impl_In {A B} {P Q : A -> B -> Type} {l l'} :
  All2 P l l' ->
  (forall x y, In x l -> In y l' -> P x y -> Q x y) ->
  All2 Q l l'.
Proof.
  revert l'. induction l; intros; inversion X.
  - econstructor.
  - subst. econstructor.  eapply X0. firstorder. firstorder. eauto.
    eapply IHl. eauto. intros.
    eapply X0. now right. now right. eauto.
Qed.

Lemma Forall2_skipn A B (P : A -> B -> Prop) l l' n:
  Forall2 P l l' -> Forall2 P (skipn n l) (skipn n l').
Proof.
  revert l l'; induction n; intros.
  - unfold skipn. eauto.
  - cbv [skipn]. fold (@skipn A n). fold (@skipn B n).
    inversion H; subst. econstructor.
    eauto.
Qed.

Lemma All2_Forall2 {A B} {P : A -> B -> Prop} {l l'} :
  All2 P l l' -> Forall2 P l l'.
Proof.
  induction 1; eauto.
Qed.

Lemma Forall2_nth_error_Some {A B} {P : A -> B -> Prop} {l l'} n t :
  Forall2 P l l' ->
  nth_error l n = Some t ->
  exists t' : B, (nth_error l' n = Some t') /\ P t t'.
Proof.
  intros Hall. revert n.
  induction Hall; destruct n; simpl; try congruence. intros [= ->]. exists y. intuition auto.
  eauto.
Qed.

Lemma Forall2_impl {A B} {P Q : A -> B -> Prop} {l l'} :
    Forall2 P l l' ->
    (forall x y, P x y -> Q x y) ->
    Forall2 Q l l'.
Proof.
  induction 1; constructor; auto.
Qed.

Arguments skipn : simpl nomatch.

Lemma skipn_all2 :
  forall {A n} (l : list A),
    #|l| <= n ->
         skipn n l = [].
Proof.
  intros A n l h. revert l h.
  induction n ; intros l h.
  - destruct l.
    + reflexivity.
    + cbn in h. inversion h.
  - destruct l.
    + reflexivity.
    + simpl. apply IHn. cbn in h. omega.
Qed.

Lemma nat_rev_ind (max : nat) :
  forall (P : nat -> Prop),
    (forall n, n >= max -> P n) ->
    (forall n, n < max -> P (S n) -> P n) ->
    forall n, P n.
Proof.
  intros P hmax hS.
  assert (h : forall n, P (max - n)).
  { intros n. induction n.
    - apply hmax. omega.
    - destruct (Nat.leb_spec0 max n).
      + replace (max - S n) with 0 by omega.
        replace (max - n) with 0 in IHn by omega.
        assumption.
      + replace (max - n) with (S (max - S n)) in IHn by omega.
        apply hS.
        * omega.
        * assumption.
  }
  intro n.
  destruct (Nat.leb_spec0 max n).
  - apply hmax. omega.
  - replace n with (max - (max - n)) by omega. apply h.
Qed.

Lemma strong_nat_ind :
  forall (P : nat -> Prop),
    (forall n, (forall m, m < n -> P m) -> P n) ->
    forall n, P n.
Proof.
  intros P h n.
  assert (forall m, m < n -> P m).
  { induction n ; intros m hh.
    - omega.
    - destruct (Nat.eqb_spec n m).
      + subst. eapply h. assumption.
      + eapply IHn. omega.
  }
  eapply h. assumption.
Qed.
Lemma app_Forall :
  forall A P (l1 l2 : list A),
    Forall P l1 ->
    Forall P l2 ->
    Forall P (l1 ++ l2).
Proof.
  intros A P l1 l2 h1 h2.
  revert l2 h2.
  induction h1 ; intros l2 h2.
  - assumption.
  - cbn. constructor ; try assumption.
    eapply IHh1. assumption.
Qed.

Lemma rev_Forall :
  forall A P l,
    Forall P l ->
    Forall P (@List.rev A l).
Proof.
  intros A P l h.
  induction l.
  - cbn. constructor.
  - cbn. dependent destruction h.
    specialize (IHl ltac:(assumption)).
    eapply app_Forall ; try assumption.
    repeat constructor. assumption.
Qed.

Lemma Forall2_impl' {A B} {P Q : A -> B -> Prop} {l l'} :
    Forall2 P l l' ->
    Forall (fun x => forall y, P x y -> Q x y) l ->
    Forall2 Q l l'.
Proof.
  induction 1; constructor;
    inversion H1; intuition.
Qed.

Lemma Forall2_Forall {A R l} : @Forall2 A A R l l -> Forall (fun x => R x x) l.
Proof.
  induction l. constructor.
  inversion 1; constructor; intuition.
Qed.

Lemma All2_All {A R l} : @All2 A A R l l -> All (fun x => R x x) l.
Proof.
  induction l. constructor.
  inversion 1; constructor; intuition.
Qed.

Lemma Forall_Forall2 {A R l} : Forall (fun x => R x x) l -> @Forall2 A A R l l.
Proof.
  induction l. constructor.
  inversion 1; constructor; intuition.
Qed.

Lemma Forall_True {A} {P : A -> Prop} l : (forall x, P x) -> Forall P l.
Proof.
  intro H. induction l; now constructor.
Qed.

Lemma Forall2_True {A B} {R : A -> B -> Prop} l l'
  : (forall x y, R x y) -> #|l| = #|l'| -> Forall2 R l l'.
Proof.
  intro H. revert l'; induction l; simpl;
    intros [] e; try discriminate e; constructor.
  easy.
  apply IHl. now apply eq_add_S.
Qed.

Lemma Forall2_map {A B A' B'} (R : A' -> B' -> Prop) (f : A -> A') (g : B -> B') l l'
  : Forall2 (fun x y => R (f x) (g y)) l l' -> Forall2 R (map f l) (map g l').
Proof.
  induction 1; constructor; auto.
Qed.


Lemma Forall2_and {A B} (R R' : A -> B -> Prop) l l'
  : Forall2 R l l' -> Forall2 R' l l' -> Forall2 (fun x y => R x y /\ R' x y) l l'.
Proof.
  induction 1.
  intro; constructor.
  inversion_clear 1.
  constructor; intuition.
Defined.

Lemma Forall_Forall2_and {A B} {R : A -> B -> Prop} {P l l'}
  : Forall2 R l l' -> Forall P l -> Forall2 (fun x y => P x /\ R x y) l l'.
Proof.
  induction 1.
  intro; constructor.
  inversion_clear 1.
  constructor; intuition.
Defined.

Lemma Forall_Forall2_and' {A B} {R : A -> B -> Prop} {P l l'}
  : Forall2 R l l' -> Forall P l' -> Forall2 (fun x y => R x y /\ P y) l l'.
Proof.
  induction 1.
  intro; constructor.
  inversion_clear 1.
  constructor; intuition.
Defined.

(* Sorted lists without duplicates *)
Class ComparableType A := { compare : A -> A -> comparison }.
Arguments compare {A} {_} _ _.

Fixpoint insert {A} `{ComparableType A} (x : A) (l : list A) :=
  match l with
  | [] => [x]
  | y :: l' =>  match compare x y with
               | Eq => l
               | Lt => x :: l
               | Gt => y :: (insert x l')
               end
  end.

Definition list_union {A} `{ComparableType A} (l l' : list A) : list A
  := fold_left (fun l' x => insert x l') l l'.

Definition compare_bool b1 b2 :=
  match b1, b2 with
  | false, true => Lt
  | true, false => Gt
  | _, _ => Eq
  end.

Definition bool_lt' b1 b2 := match compare_bool b1 b2 with Lt => true | _ => false end.

Lemma Forall2_nth :
  forall A B P l l' n (d : A) (d' : B),
    Forall2 P l l' ->
    P d d' ->
    P (nth n l d) (nth n l' d').
Proof.
  intros A B P l l' n d d' h hd.
  induction n in l, l', h |- *.
  - destruct h.
    + assumption.
    + assumption.
  - destruct h.
    + assumption.
    + simpl. apply IHn. assumption.
Qed.

Arguments skipn : simpl nomatch.

Lemma Forall2_nth_error_Some_l :
  forall A B (P : A -> B -> Prop) l l' n t,
    nth_error l n = Some t ->
    Forall2 P l l' ->
    exists t',
      nth_error l' n = Some t' /\
      P t t'.
Proof.
  intros A B P l l' n t e h.
  induction n in l, l', t, e, h |- *.
  - destruct h.
    + cbn in e. discriminate.
    + cbn in e. inversion e. subst.
      exists y. split ; auto.
  - destruct h.
    + cbn in e. discriminate.
    + cbn in e. apply IHn with (l' := l') in e ; assumption.
Qed.

Lemma Forall2_nth_error_None_l :
  forall A B (P : A -> B -> Prop) l l' n,
    nth_error l n = None ->
    Forall2 P l l' ->
    nth_error l' n = None.
Proof.
  intros A B P l l' n e h.
  induction n in l, l', e, h |- *.
  - destruct h.
    + reflexivity.
    + cbn in e. discriminate e.
  - destruct h.
    + reflexivity.
    + cbn in e. cbn. eapply IHn ; eauto.
Qed.

Lemma Forall2_trans :
  forall A (P : A -> A -> Prop),
    Transitive P ->
    Transitive (Forall2 P).
Proof.
  intros A P hP l1 l2 l3 h1 h2.
  induction h1 in l3, h2 |- *.
  - inversion h2. constructor.
  - inversion h2. constructor.
    + eapply hP ; eauto.
    + eapply IHh1 ; eauto.
Qed.

Lemma Forall2_rev :
  forall A B R l l',
    @Forall2 A B R l l' ->
    Forall2 R (List.rev l) (List.rev l').
Proof.
  intros A B R l l' h.
  induction h.
  - constructor.
  - cbn. eapply Forall2_app ; eauto.
Qed.

(* Weak, would need some Forall2i *)
Lemma Forall2_mapi :
  forall A B A' B' (R : A' -> B' -> Prop) (f : nat -> A -> A') (g : nat -> B -> B') l l',
    Forall2 (fun x y => forall i, R (f i x) (g i y)) l l' ->
    Forall2 R (mapi f l) (mapi g l').
Proof.
  intros A B A' B' R f g l l' h.
  unfold mapi. generalize 0. intro i.
  induction h in i |- *.
  - constructor.
  - cbn. constructor ; eauto.
Qed.

Lemma All2_nth :
  forall A B P l l' n (d : A) (d' : B),
    All2 P l l' ->
    P d d' ->
    P (nth n l d) (nth n l' d').
Proof.
  intros A B P l l' n d d' h hd.
  induction n in l, l', h |- *.
  - destruct h.
    + assumption.
    + assumption.
  - destruct h.
    + assumption.
    + simpl. apply IHn. assumption.
Qed.

(* Induction principle on OnOne2 when the relation also depends
     on one of the lists, and should not change.
   *)
Lemma OnOne2_ind_l :
  forall A (R : list A -> A -> A -> Type)
    (P : forall L l l', OnOne2 (R L) l l' -> Type),
    (forall L x y l (r : R L x y), P L (x :: l) (y :: l) (OnOne2_hd _ _ _ l r)) ->
    (forall L x l l' (h : OnOne2 (R L) l l'),
        P L l l' h ->
        P L (x :: l) (x :: l') (OnOne2_tl _ x _ _ h)
    ) ->
    forall l l' h, P l l l' h.
Proof.
  intros A R P hhd htl l l' h. induction h ; eauto.
Qed.

Lemma All2_mapi :
  forall A B A' B' (R : A' -> B' -> Type) (f : nat -> A -> A') (g : nat -> B -> B') l l',
    All2 (fun x y => forall i, R (f i x) (g i y)) l l' ->
    All2 R (mapi f l) (mapi g l').
Proof.
  intros A B A' B' R f g l l' h.
  unfold mapi. generalize 0. intro i.
  induction h in i |- *.
  - constructor.
  - cbn. constructor ; eauto.
Qed.

Lemma OnOne2_impl_exist_and_All :
  forall A (l1 l2 l3 : list A) R1 R2 R3,
    OnOne2 R1 l1 l2 ->
    All2 R2 l3 l2 ->
    (forall x x' y, R1 x y -> R2 x' y -> ∑ z : A, R3 x z × R2 x' z) ->
    ∑ l4, OnOne2 R3 l1 l4 × All2 R2 l3 l4.
Proof.
  intros A l1 l2 l3 R1 R2 R3 h1 h2 h.
  induction h1 in l3, h2 |- *.
  - dependent destruction h2.
    specialize (h _ _ _ p r) as hh.
    destruct hh as [? [? ?]].
    eexists. constructor.
    + constructor. eassumption.
    + constructor ; eauto.
  - dependent destruction h2.
    specialize (IHh1 _ h2). destruct IHh1 as [? [? ?]].
    eexists. constructor.
    + eapply OnOne2_tl. eassumption.
    + constructor ; eauto.
Qed.

Lemma OnOne2_impl_exist_and_All_r :
  forall A (l1 l2 l3 : list A) R1 R2 R3,
    OnOne2 R1 l1 l2 ->
    All2 R2 l2 l3 ->
    (forall x x' y, R1 x y -> R2 y x' -> ∑ z : A, R3 x z × R2 z x') ->
    ∑ l4, ( OnOne2 R3 l1 l4 × All2 R2 l4 l3 ).
Proof.
  intros A l1 l2 l3 R1 R2 R3 h1 h2 h.
  induction h1 in l3, h2 |- *.
  - dependent destruction h2.
    specialize (h _ _ _ p r) as hh.
    destruct hh as [? [? ?]].
    eexists. split.
    + constructor. eassumption.
    + constructor ; eauto.
  - dependent destruction h2.
    specialize (IHh1 _ h2). destruct IHh1 as [? [? ?]].
    eexists. split.
    + eapply OnOne2_tl. eassumption.
    + constructor ; eauto.
Qed.

Lemma All2_skipn :
  forall A B R l l' n,
    @All2 A B R l l' ->
    @All2 A B R (skipn n l) (skipn n l').
Proof.
  intros A B R l l' n h.
  induction h in n |- *.
  all: destruct n ; try econstructor ; eauto.
Qed.

Lemma All2_rev (A : Type) (P : A -> A -> Type) (l l' : list A) :
  All2 P l l' ->
  All2 P (List.rev l) (List.rev l').
Proof.
  induction 1. constructor.
  simpl. eapply All2_app; auto.
Qed.


(** * Non Empty List *)
Module NEL.

  Inductive t (A : Set) :=
  | sing : A -> t A
  | cons : A -> t A -> t A.

  Arguments sing {A} _.
  Arguments cons {A} _ _.

  Infix "::" := cons : nel_scope.
  Notation "[ x ]" := (sing x) : nel_scope.
  Delimit Scope nel_scope with nel.
  Bind Scope nel_scope with t.

  Local Open Scope nel_scope.

  Fixpoint length {A} (l : t A) : nat :=
    match l with
    | [ _ ] => 1
    | _ :: l' => S (length l')
    end.

  Notation "[ x ; y ; .. ; z ; e ]" :=
    (cons x (cons y .. (cons z (sing e)) ..)) : nel_scope.

  Fixpoint to_list {A} (l : t A) : list A :=
    match l with
    | [x] => [x]
    | x :: l => x :: (to_list l)
    end.

  Fixpoint map {A B : Set} (f : A -> B) (l : t A) : t B :=
    match l with
    | [x] => [f x]
    | x :: l => f x :: map f l
    end.

  Fixpoint app {A} (l l' : t A) : t A :=
    match l with
    | [x] => x :: l'
    | x :: l => x :: (app l l')
    end.

  Infix "++" := app : nel_scope.

  Fixpoint app_r {A : Set} (l : list A) (l' : t A) : t A :=
    match l with
    | [] => l'
    | (x :: l)%list => x :: app_r l l'
    end.

  Fixpoint cons' {A : Set} (x : A) (l : list A) : t A :=
    match l with
    | [] => [x]
    | (y :: l)%list => x :: cons' y l
    end.

  Lemma cons'_spec {A : Set} (x : A) l
    : to_list (cons' x l) = (x :: l)%list.
  Proof.
    revert x; induction l; simpl.
    reflexivity.
    intro x; now rewrite IHl.
  Qed.

  Fixpoint fold_left {A} {B : Set} (f : A -> B -> A) (l : t B) (a0 : A) : A :=
    match l with
    | [b] => f a0 b
    | b :: l => fold_left f l (f a0 b)
    end.

  Fixpoint forallb {A : Set} (f : A -> bool) (l : t A) :=
    match l with
    | [x] => f x
    | hd :: tl => f hd && forallb f tl
    end.

  Fixpoint forallb2 {A : Set} (f : A -> A -> bool) (l l' : t A) :=
    match l, l' with
    | [x], [x'] => f x x'
    | hd :: tl, hd' :: tl' => f hd hd' && forallb2 f tl tl'
    | _, _ => false
    end.

  Lemma map_to_list {A B : Set} (f : A -> B) (l : t A)
    : to_list (map f l) = List.map f (to_list l).
  Proof.
    induction l; cbn; congruence.
  Qed.

  Lemma map_app {A B : Set} (f : A -> B) l l' :
    map f (l ++ l') = map f l ++ map f l'.
  Proof.
    induction l; cbn; congruence.
  Qed.

  Lemma map_map {A B C : Set} (f : A -> B) (g : B -> C) l :
    map g (map f l) = map (fun x => g (f x)) l.
  Proof.
    induction l; simpl; auto.
    rewrite IHl; auto.
  Qed.

  Lemma map_ext {A B : Set} (f g : A -> B) l :
    (forall x, f x = g x) -> map f l = map g l.
  Proof.
    intros.
    induction l; cbn; rewrite ?H; congruence.
  Defined.

End NEL.

Definition non_empty_list := NEL.t.


Lemma iff_forall {A} B C (H : forall x : A, B x <-> C x)
  : (forall x, B x) <-> (forall x, C x).
  firstorder.
Defined.

Lemma iff_ex {A} B C (H : forall x : A, B x <-> C x)
  : (ex B) <-> (ex C).
  firstorder.
Defined.

Lemma if_true_false (b : bool) : (if b then true else false) = b.
  destruct b; reflexivity.
Qed.

Lemma not_empty_map {A B} (f : A -> B) l : l <> [] -> map f l <> [].
Proof.
  intro H; destruct l; intro e; now apply H.
Qed.

Lemma Z_of_pos_alt p : Z.of_nat (Pos.to_nat p) = Z.pos p.
Proof.
  induction p using Pos.peano_ind.
  rewrite Pos2Nat.inj_1. reflexivity.
  rewrite Pos2Nat.inj_succ. cbn. f_equal. lia.
Qed.

Lemma All2_right_triv {A B} {l : list A} {l' : list B} P :
  All P l' -> #|l| = #|l'| -> All2 (fun _ b => P b) l l'.
Proof.
  induction 1 in l |- *; cbn; intros; destruct l; cbn in *; try omega; econstructor; eauto.
Qed.

Lemma All_repeat {A} {n P} x :
  P x -> @All A P (repeat x n).
Proof.
  induction n; cbn; econstructor; eauto.
Qed.

Lemma All2_map_left {A B C} (P : A -> C -> Type) l l' (f : B -> A) :
  All2 (fun x y => P (f x) y) l l' -> All2 P  (map f l) l'.
Proof. intros. rewrite <- (map_id l'). eapply All2_map; eauto. Qed.

Lemma All2_map_right {A B C} (P : A -> C -> Type) l l' (f : B -> C) :
  All2 (fun x y => P x (f y)) l l' -> All2 P  l (map f l').
Proof. intros. rewrite <- (map_id l). eapply All2_map; eauto. Qed.

Lemma Forall2_Forall_right {A B} {P : A -> B -> Prop} {Q : B -> Prop} {l l'} :
  Forall2 P l l' ->
  (forall x y, P x y -> Q y) ->
  Forall Q l'.
Proof.
  intros HF H. induction HF; constructor; eauto.
Qed.

Lemma All2_from_nth_error A B L1 L2 (P : A -> B -> Type) :
  #|L1| = #|L2| ->
                (forall n x1 x2, n < #|L1| -> nth_error L1 n = Some x1
                                      -> nth_error L2 n = Some x2
                                      -> P x1 x2) ->
                All2 P L1 L2.
Proof.
  revert L2; induction L1; cbn; intros.
  - destruct L2; inv H. econstructor.
  - destruct L2; inversion H. econstructor.
    eapply (X 0); cbn; eauto. omega.
    eapply IHL1. eauto.
    intros. eapply (X (S n)); cbn; eauto. omega.
Qed.

Lemma All2_nth_error {A B} {P : A -> B -> Type} {l l'} n t t' :
  All2 P l l' ->
  nth_error l n = Some t ->
  nth_error l' n = Some t' ->
  P t t'.
Proof.
  intros Hall. revert n.
  induction Hall; destruct n; simpl; try congruence.
  eauto.
Qed.

Lemma All_In X (P : X -> Type) (l : list X) x : All P l -> In x l -> squash (P x).
Proof.
  induction 1; cbn; intros; destruct H.
  - subst. econstructor. eauto.
  - eauto.
Qed.

Lemma nth_error_skipn_add A l m n (a : A) :
  nth_error l (m + n) = Some a ->
  nth_error (skipn m l) n = Some a.
Proof.
  induction m in n, l |- *.
  - cbn. destruct l; firstorder.
  - cbn. destruct l.
    + inversion 1.
    + eapply IHm.
Qed.

Lemma All2_swap :
  forall A B R l l',
    @All2 A B R l l' ->
    All2 (fun x y => R y x) l' l.
Proof.
  intros A B R l l' h.
  induction h ; eauto.
Qed.

Lemma All2_firstn :
  forall A B R l l' n,
    @All2 A B R l l' ->
    @All2 A B R (firstn n l) (firstn n l').
Proof.
  intros A B R l l' n h.
  induction h in n |- *.
  all: destruct n ; try econstructor ; eauto.
Qed.

Lemma skipn_all_app :
  forall A (l1 l2 : list A),
    skipn #|l1| (l1 ++ l2) = l2.
Proof.
  intros A l1 l2.
  induction l1 in l2 |- *.
  - reflexivity.
  - simpl. eauto.
Qed.

Lemma All2_app_inv_r :
  forall A B R l r1 r2,
    @All2 A B R l (r1 ++ r2) ->
    ∑ l1 l2,
      (l = l1 ++ l2)%list ×
      All2 R l1 r1 ×
      All2 R l2 r2.
Proof.
  intros A B R l r1 r2 h.
  exists (firstn #|r1| l), (skipn #|r1| l).
  split ; [| split].
  - rewrite firstn_skipn. reflexivity.
  - apply All2_firstn with (n := #|r1|) in h.
    rewrite firstn_app in h. rewrite firstn_all in h.
    replace (#|r1| - #|r1|) with 0 in h by omega. cbn in h.
    rewrite app_nil_r in h. assumption.
  - apply All2_skipn with (n := #|r1|) in h.
    rewrite skipn_all_app in h. assumption.
Qed.

Lemma rev_app :
  forall A (l l' : list A),
    (rev (l ++ l') = rev l' ++ rev l)%list.
Proof.
  intros A l l'.
  induction l in l' |- *.
  - simpl. change (rev (@nil A)) with (@nil A).
    rewrite app_nil_r. reflexivity.
  - simpl. rewrite rev_cons. rewrite IHl.
    rewrite rev_cons. rewrite app_assoc. reflexivity.
Qed.

Lemma rev_invol :
  forall A (l : list A),
    rev (rev l) = l.
Proof.
  intros A l. induction l ; eauto.
  rewrite rev_cons. rewrite rev_app. simpl.
  rewrite IHl. reflexivity.
Qed.

Lemma list_ind_rev :
  forall A (P : list A -> Prop),
    P nil ->
    (forall a l, P l -> P (l ++ [a])%list) ->
    forall l, P l.
Proof.
  intros A P h1 h2 l.
  rewrite <- rev_invol.
  generalize (rev l). clear l. intro l.
  induction l ; auto.
  rewrite rev_cons. eauto.
Qed.

Lemma list_rect_rev :
  forall A (P : list A -> Type),
    P nil ->
    (forall a l, P l -> P (l ++ [a])%list) ->
    forall l, P l.
Proof.
  intros A P h1 h2 l.
  rewrite <- rev_invol.
  generalize (rev l). clear l. intro l.
  induction l ; auto.
  rewrite rev_cons. eauto.
Qed.



Lemma last_app {A} (l l' : list A) d : l' <> [] -> last (l ++ l') d = last l' d.
Proof.
  revert l'. induction l; simpl; auto. intros.
  destruct l. simpl. destruct l'; congruence. simpl.
  specialize (IHl _ H). apply IHl.
Qed.

Lemma last_nonempty_eq {A} {l : list A} {d d'} : l <> [] -> last l d = last l d'.
Proof.
  induction l; simpl; try congruence.
  intros. destruct l; auto. apply IHl. congruence.
Qed.

Lemma nth_error_removelast {A} (args : list A) n :
  n < Nat.pred #|args| -> nth_error args n = nth_error (removelast args) n.
Proof.
  induction n in args |- *; destruct args; intros; auto.
  simpl. destruct args. depelim H. reflexivity.
  simpl. rewrite IHn. simpl in H. auto with arith.
  destruct args, n; reflexivity.
Qed.

Lemma nth_error_skipn {A} n (l : list A) i : nth_error (skipn n l) i = nth_error l (n + i).
Proof.
  induction l in n, i |- *; destruct n; simpl; auto.
    by case: i.
Qed.

Lemma skipn_skipn {A} n m (l : list A) : skipn n (skipn m l) = skipn (m + n) l.
Proof.
  induction m in n, l |- *. auto.
  simpl. destruct l. destruct n; reflexivity.
  now rewrite skipn_S skipn_S.
Qed.

Lemma skipn_nth_error {A} (l : list A) i :
  match nth_error l i with
  | Some a => skipn i l = a :: skipn (S i) l
  | None => skipn i l = []
  end.
Proof.
  induction l in i |- *. destruct i. reflexivity. reflexivity.
  destruct i. simpl. reflexivity.
  simpl. specialize (IHl i). destruct nth_error.
  rewrite [skipn _ _]IHl. reflexivity.
  rewrite [skipn _ _]IHl. reflexivity.
Qed.

Lemma nth_error_app_ge {A} (l l' : list A) (v : nat) :
  length l <= v ->
  nth_error (l ++ l') v = nth_error l' (v - length l).
Proof.
  revert v; induction l; simpl; intros.
  now rewrite Nat.sub_0_r.
  destruct v. lia.
  simpl. rewrite IHl; auto with arith.
Qed.

Lemma nth_error_app_lt {A} (l l' : list A) (v : nat) :
  v < length l ->
  nth_error (l ++ l') v = nth_error l v.
Proof.
  revert v; induction l; simpl; intros. easy.
  destruct v; trivial.
  simpl. rewrite IHl; auto with arith.
Qed.

Lemma nth_error_rev {A} (l : list A) i : i < #|l| ->
  nth_error l i = nth_error (List.rev l) (#|l| - S i).
Proof.
  revert l. induction i. destruct l; simpl; auto.
  induction l using rev_ind; simpl. auto.
  rewrite rev_app_distr. simpl.
  rewrite app_length. simpl.
  replace (#|l| + 1 - 0) with (S #|l|) by lia. simpl.
  rewrite Nat.sub_0_r in IHl. auto with arith.

  destruct l. simpl; auto. simpl. intros. rewrite IHi. lia.
  assert (#|l| - S i < #|l|) by lia.
  rewrite nth_error_app_lt. rewrite List.rev_length; auto.
  reflexivity.
Qed.

Ltac tas := try assumption.
Ltac tea := try eassumption.

Axiom todo : string -> forall {A}, A.
Ltac todo s := exact (todo s).
Extract Constant todo => "fun s -> failwith (String.concat """" (List.map (String.make 1) s))".

Lemma All2_trans {A} (P : A -> A -> Type) :
  CRelationClasses.Transitive P ->
  CRelationClasses.Transitive (All2 P).
Proof.
  intros HP x y z H. induction H in z |- *.
  intros Hyz. inv Hyz. constructor.
  intros Hyz. inv Hyz. constructor; auto.
  now transitivity y.
Qed.

Lemma All2_impl' {A B} {P Q : A -> B -> Type} {l : list A} {l' : list B}
  : All2 P l l' -> All (fun x => forall y, P x y -> Q x y) l -> All2 Q l l'.
Proof.
  induction 1. constructor.
  intro XX; inv XX.
  constructor; auto.
Defined.

Lemma All_All2 {A} {P : A -> A -> Type} {Q} {l : list A} :
  All Q l ->
  (forall x, Q x -> P x x) ->
  All2 P l l.
Proof.
  induction 1; constructor; auto.
Qed.

(* Should be All2_nth_error_Some_l *)
Lemma All2_nth_error_Some {A B} {P : A -> B -> Type} {l l'} n t :
  All2 P l l' ->
  nth_error l n = Some t ->
  { t' : B & (nth_error l' n = Some t') * P t t'}%type.
Proof.
  intros Hall. revert n.
  induction Hall; destruct n; simpl; try congruence.
  intros [= ->]. exists y. intuition auto.
  eauto.
Qed.

Lemma All2_nth_error_Some_r {A B} {P : A -> B -> Type} {l l'} n t' :
  All2 P l l' ->
  nth_error l' n = Some t' ->
  ∑ t, nth_error l n = Some t × P t t'.
Proof.
  intros Hall. revert n.
  induction Hall; destruct n; simpl; try congruence.
  intros [= ->]. exists x. intuition auto.
  eauto.
Qed.

Lemma All2_nth_error_None {A B} {P : A -> B -> Type} {l l'} n :
  All2 P l l' ->
  nth_error l n = None ->
  nth_error l' n = None.
Proof.
  intros Hall. revert n.
  induction Hall; destruct n; simpl; try congruence. auto.
Qed.

Lemma All2_length {A B} {P : A -> B -> Type} l l' : All2 P l l' -> #|l| = #|l'|.
Proof. induction 1; simpl; auto. Qed.

Lemma All2_same {A} (P : A -> A -> Type) l : (forall x, P x x) -> All2 P l l.
Proof. induction l; constructor; auto. Qed.

Notation Trel_conj R S :=
  (fun x y => R x y * S x y)%type.

Lemma All2_prod {A} P Q (l l' : list A) : All2 P l l' -> All2 Q l l' -> All2 (Trel_conj P Q) l l'.
Proof.
  induction 1; inversion 1; subst; auto.
Defined.

Lemma All2_prod_inv :
  forall A (P : A -> A -> Type) Q l l',
    All2 (Trel_conj P Q) l l' ->
    All2 P l l' × All2 Q l l'.
Proof.
  intros A P Q l l' h.
  induction h.
  - auto.
  - destruct IHh. destruct r.
    split ; constructor ; auto.
Qed.

Lemma All2_sym {A} (P : A -> A -> Type) l l' :
  All2 P l l' -> All2 (fun x y => P y x) l' l.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma All2_symP {A} (P : A -> A -> Type) :
  CRelationClasses.Symmetric P ->
  CRelationClasses.Symmetric (All2 P).
Proof.
  intros hP x y h. induction h.
  - constructor.
  - constructor ; eauto.
Qed.

Lemma All_All2_All2_mix {A B} (P : B -> B -> Type) (Q R : A -> B -> Type) l l' l'' :
  All (fun x => forall y z, Q x y -> R x z -> ∑ v, P y v * P z v) l -> All2 Q l l' -> All2 R l l'' ->
  ∑ l''', All2 P l' l''' * All2 P l'' l'''.
Proof.
  intros H; induction H in l', l'' |- *;
  intros H' H''; depelim H'; depelim H''; try solve [econstructor; eauto; constructor].
  simpl. destruct (IHAll _ _ H' H''). destruct (p _ _ q r).
  exists (x1 :: x0). split; constructor; intuition auto.
Qed.

Lemma All_forallb_map_spec {A B : Type} {P : A -> Type} {p : A -> bool}
      {l : list A} {f g : A -> B} :
    All P l -> forallb p l ->
    (forall x : A, P x -> p x -> f x = g x) -> map f l = map g l.
Proof.
  induction 1; simpl; trivial.
  rewrite andb_and. intros [px pl] Hx.
  f_equal. now apply Hx. now apply IHX.
Qed.

Lemma All_forallb_forallb_spec {A : Type} {P : A -> Type} {p : A -> bool}
      {l : list A} {f : A -> bool} :
    All P l -> forallb p l ->
    (forall x : A, P x -> p x -> f x) -> forallb f l.
Proof.
  induction 1; simpl; trivial.
  rewrite !andb_and. intros [px pl] Hx. eauto.
Qed.


Lemma forallb_nth {A} (l : list A) (n : nat) P d :
  forallb P l -> n < #|l| -> exists x, (nth n l d = x) /\ P x.
Proof.
  induction l in n |- *; destruct n; simpl; auto; try easy.
  move/andP => [pa pl] pn. exists a; easy.
  move/andP => [pa pl] pn. specialize (IHl n pl).
  forward IHl. lia. auto.
Qed.

Lemma forallb_nth' {A} {l : list A} {P} n d :
  forallb P l -> {exists x, (nth n l d = x) /\ P x} + {nth n l d = d}.
Proof.
  intro H. destruct (le_lt_dec #|l| n) as [HH|HH].
  - rewrite nth_overflow; tas; now right.
  - left. eapply forallb_nth; assumption.
Qed.

Lemma forallb_impl {A} (p q : pred A) l :
  (forall x, In x l -> p x -> q x) -> forallb p l -> forallb q l.
Proof.
  intros H0 H1. eapply forallb_forall. intros x H2. 
  eapply forallb_forall in H1; tea.
  now eapply H0.
Qed.

Lemma forallb_iff {A} (p q : pred A) l :
  (forall x, In x l -> p x <-> q x) -> forallb p l = forallb q l.
Proof.
  intros H0. eapply Forall_forallb_eq_forallb with (P:=fun x => In x l).
  - now apply Forall_forall.
  - intros; eapply eq_true_iff_eq; eauto.
Qed.

Lemma map_inj :
  forall A B (f : A -> B) l l',
    (forall x y, f x = f y -> x = y) ->
    map f l = map f l' ->
    l = l'.
Proof.
  intros A B f l l' h e.
  induction l in l', e |- *.
  - destruct l' ; try discriminate. reflexivity.
  - destruct l' ; try discriminate. inversion e.
    f_equal ; eauto.
Qed.

Lemma All2_eq :
  forall A (l l' : list A),
    All2 eq l l' ->
    l = l'.
Proof.
  intros A l l' h.
  induction h ; eauto. subst. reflexivity.
Qed.


Lemma All_prod_inv :
  forall A P Q l,
    All (fun x : A => P x × Q x) l ->
    All P l × All Q l.
Proof.
  intros A P Q l h.
  induction h.
  - split ; auto.
  - destruct IHh, p.
    split ; constructor ; auto.
Qed.


Lemma All_prod :
  forall A P Q l,
    All P l ->
    All Q l ->
    All (fun x : A => P x × Q x) l.
Proof.
  intros A P Q l h1 h2.
  induction h1 in h2 |- *.
  - constructor.
  - dependent destruction h2.
    forward IHh1 ; auto.
Qed.
