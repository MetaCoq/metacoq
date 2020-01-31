From Coq Require Import Bool List String Program.
Global Set Asymmetric Patterns.


Require Export All_Forall
        MCArith
        MCCompare
        MCEquality
        MCList
        MCOption
        MCProd
        MCSquash
        MCRelations
        MCString
.

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

Tactic Notation "apply*" constr(H) "in" hyp(H')
  := apply H in H'; [..|apply H].

Ltac cbnr := cbn; try reflexivity.

Ltac rdestruct H :=
  match type of H with
  | _ \/ _ => destruct H as [H|H]; [rdestruct H|rdestruct H]
  | _ /\ _ => let H' := fresh H in
            destruct H as [H|H']; [rdestruct H|rdestruct H']
  | prod _ _ => let H' := fresh H in
            destruct H as [H H']; rdestruct H; rdestruct H'
  | sigT _ => let H' := fresh H in
             destruct H as [H H']; rdestruct H; rdestruct H'
  | _ => idtac
  end.

(* This is an attempt to overcome the fact that auto/eauto *)
(* do not deal with products *)
Ltac rdest :=
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  | H : prod _ _ |- _ => destruct H
  | H : sigT _ |- _ => destruct H
  | |- _ /\ _ => split
  | |- prod _ _ => split
  | |- sigT _ => eexists
  end.

(** We cannot use ssrbool as it breaks extraction. *)
Coercion is_true : bool >-> Sortclass.

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

Class Fuel := fuel : nat.

(** Such a useful tactic it should be part of the stdlib. *)
Ltac forward_gen H tac :=
  match type of H with
  | ?X -> _ => let H' := fresh in assert (H':X) ; [tac|specialize (H H'); clear H']
  end.

Ltac inv H := inversion_clear H.

Tactic Notation "forward" constr(H) := forward_gen H ltac:(idtac).
Tactic Notation "forward" constr(H) "by" tactic(tac) := forward_gen H tac.

Hint Resolve Peano_dec.eq_nat_dec : eq_dec.


Ltac invs H := inversion H; subst; clear H.

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




(** * Non Empty List : will go away *)
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

  Lemma forallb2_refl :
    forall (A : Set) (R : A -> A -> bool),
      (forall x, is_true (R x x)) ->
      forall l, is_true (forallb2 R l l).
  Proof.
    intros A R R_refl l.
    induction l.
    - simpl. apply R_refl.
    - simpl. rewrite R_refl. assumption.
  Qed.

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

Ltac tas := try assumption.
Ltac tea := try eassumption.

Axiom todo : String.string -> forall {A}, A.
Ltac todo s := exact (todo s).
Extract Constant todo => "fun s -> failwith (String.concat """" (List.map (String.make 1) s))".
