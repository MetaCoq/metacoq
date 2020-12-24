From Coq Require Import Bool RelationClasses.
Require Import ssreflect.

Local Coercion is_true : bool >-> Sortclass.

Declare Scope pair_scope.

Notation "p .1" := (fst p)
  (at level 2, left associativity, format "p .1") : pair_scope.
Notation "p .2" := (snd p)
  (at level 2, left associativity, format "p .2") : pair_scope.
Open Scope pair_scope.

Notation "x × y" := (prod x y ) (at level 80, right associativity).

Notation "p .p1" := (proj1 p) (at level 2, left associativity, format "p .p1").
Notation "p .p2" := (proj2 p) (at level 2, left associativity, format "p .p2").

Definition on_snd {A B C} (f : B -> C) (p : A * B) :=
  (fst p, f (snd p)).

Definition test_snd {A B} (f : B -> bool) (p : A * B) :=
  f (snd p).

Definition map_pair {A B C D} (f : A -> B) (g : C -> D) (p : A × C) : B × D :=
  (f p.1, g p.2).
  
Lemma on_snd_on_snd {A B C D} (f : C -> D) (g : B -> C) (d : A * B) :
  on_snd f (on_snd g d) = on_snd (fun x => f (g x)) d.
Proof.
  destruct d; reflexivity.
Qed.

Lemma snd_on_snd {A B C} (f : B -> C) (p : A * B) : snd (on_snd f p) = f (snd p).
Proof. destruct p; reflexivity. Qed.

Lemma compose_on_snd {A B C D} (f : C -> D) (g : B -> C) :
  (fun (x : A * B) => (on_snd f) (on_snd g x)) = on_snd (fun x => f (g x)).
Proof.
  reflexivity.
Qed.

Lemma on_snd_eq_spec {A B C} (f g : B -> C) (x : A * B) :
  f (snd x) = g (snd x) <->
  on_snd f x = on_snd g x.
Proof.
  destruct x; unfold on_snd; cbn. split; congruence.
Qed.

Definition on_pi2 {A B C} (f : B -> B) (p : A * B * C) : A * B * C :=
  (fst (fst p), f (snd (fst p)), snd p).

(** It would be tempting to import ssrbool here, however 
  https://github.com/coq/coq/issues/13486 prevents this. *)  
Lemma andb_and b b' : b && b' <-> b /\ b'.
Proof. apply andb_true_iff. Qed.

Lemma andb_andI {b b'} : b && b' -> b /\ b'.
Proof. apply andb_and. Qed.

Definition fst_eq {A B} {x x' : A} {y y' : B}
  : (x, y) = (x', y') -> x = x'.
Proof.
  inversion 1; reflexivity.
Qed.

Definition snd_eq {A B} {x x' : A} {y y' : B}
  : (x, y) = (x', y') -> y = y'.
Proof.
  inversion 1; reflexivity.
Qed.

Definition swap {A B : Type} (x : A * B) : B * A :=
  (snd x, fst x).
