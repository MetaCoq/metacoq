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

Lemma iff_is_true_eq_bool (b b' : bool) :
  (b <-> b') -> b = b'.
Proof.
  destruct b, b'; cbnr; intros [H1 H2];
    try specialize (H1 eq_refl); try specialize (H2 eq_refl);
      discriminate.
Qed.

Lemma uip_bool (b1 b2 : bool) (p q : b1 = b2) : p = q.
Proof.
  destruct q. apply Eqdep_dec.UIP_refl_bool.
Qed.

Ltac tas := try assumption.
Ltac tea := try eassumption.

Axiom todo : String.string -> forall {A}, A.
Ltac todo s := exact (todo s).
Extract Constant todo => "fun s -> failwith (String.concat """" (List.map (String.make 1) s))".


Coercion is_left A B (u : {A} + {B}) := match u with left _ => true | _ => false end.
