From Coq Require Import Bool.

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

Declare Scope pair_scope.

Notation "p .1" := (fst p)
  (at level 2, left associativity, format "p .1") : pair_scope.
Notation "p .2" := (snd p)
  (at level 2, left associativity, format "p .2") : pair_scope.
Open Scope pair_scope.

Notation "x × y" := (prod x y )(at level 80, right associativity).


Definition on_snd {A B C} (f : B -> C) (p : A * B) :=
  (fst p, f (snd p)).

Definition test_snd {A B} (f : B -> bool) (p : A * B) :=
  f (snd p).


Lemma on_snd_on_snd {A B C D} (f : C -> D) (g : B -> C) (d : A * B) :
  on_snd f (on_snd g d) = on_snd (fun x => f (g x)) d.
Proof.
  destruct d; reflexivity.
Qed.

Lemma snd_on_snd {A B C} (f : B -> C) (p : A * B) : snd (on_snd f p) = f (snd p).
Proof. destruct p; reflexivity. Qed.

Require Import Program.

Lemma compose_on_snd {A B C D} (f : C -> D) (g : B -> C) :
  compose (A:=A * B) (on_snd f) (on_snd g) = on_snd (compose f g).
Proof.
  reflexivity.
Qed.

Lemma on_snd_eq_spec {A B C} (f g : B -> C) (x : A * B) :
  f (snd x) = g (snd x) <->
  on_snd f x = on_snd g x.
Proof.
  destruct x; unfold on_snd; cbn. split; congruence.
Qed.

Lemma on_snd_test_spec {A B C} (P : B -> Type) (p : B -> bool) (f g : B -> C) (x : A * B) :
  P (snd x) -> (forall x, P x -> is_true (p x) -> f x = g x) ->
  is_true (test_snd p x) ->
  on_snd f x = on_snd g x.
Proof.
  intros. destruct x. unfold on_snd. simpl.
  now rewrite H; auto.
Qed.

Definition on_pi2 {A B C} (f : B -> B) (p : A * B * C) : A * B * C :=
  (fst (fst p), f (snd (fst p)), snd p).


Lemma andb_and b b' : is_true (b && b') <-> is_true b /\ is_true b'.
Proof. apply andb_true_iff. Qed.

Lemma andP {b b'} : is_true (b && b') -> is_true b /\ is_true b'.
Proof. apply andb_and. Qed.
