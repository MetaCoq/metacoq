(* -*- coq-prog-args : ("-debug" "-type-in-type") -*-  *)

Require Import Template.Ast Template.translation_utils.
Require Import Template.tsl_fun.
Require Import Template.sigma.
Open Scope sigma_scope.
Declare ML Module "translation_plugin".

Let T := Type.
Check (T : T).

(* Translate pair. *)
(* (* Translate fst'. *) *)
(* (* Translate snd'. *) *)
(* Translate bool. *)
(* Translate true. *)
(* Translate false. *)

(* Definition n : (fun x => x) Type := nat. *)
Print Instances Translation.
Implement Existing nat. exact nat. Defined.

Implement Existing bool.
exact (bool*bool)%type.
Defined.

(* todo: fix the translation of inductives *)
Implement Existing true.
exact true.
Defined.

Definition t7 := fun x : nat => (fun y : bool => x).
Translate t7.


Definition g := prod Prop Type.
Definition f := g.

Axiom tr : nat.

Fail Translate tr.
Translate g.
Print gᵗ.
Translate f.
Print fᵗ.

Definition t6 := fun x : f => x.
Translate t6.

Implement t2 : bool as totot.
econstructor.
Defined.
Print t2.
Print totot.

Definition t4 := (t2, true).
Translate t4.

Implement t3 : t2 = t2.
econstructor.
Defined.

Definition t3' := Datatypes.pair t3 nat.
Translate t3'.
Print t3'ᵗ.

Implement nnnn : (nat -> nat).
econstructor; econstructor.
Defined.

Definition t5 := forall X:Set, X.
Translate t5.
Print t5ᵗ.

(* (* Axiom a : forall X, X. *) *)

(* Implement y : forall X:Set, X. *)
(* (* Print Sorted Universes. *) *)
(* refine (pair' _ _ _ _). *)
(* admit. econstructor. *)
(* Admitted. *)

(* Translate nat. *)
(* Translate unit. *)

(* Definition t := (fun x : nat => x). *)
(* Translate t.  *)

(* (* Set Primitive Projections. *) *)
(* (* Record prod' (A B : Set) : Set := *) *)
(* (*   pair' { fst' : A ; snd' : B }. *) *)
(* (* Arguments fst' {A B} _. *) *)
(* (* Arguments snd' {A B} _. *) *)

(* (* Translate prod'. *) *)
(* Definition mm := (pair' _ _ true tt).(fst'). *)
(* Translate mm. *)
(* Eval compute in mmᵗ. *)

(* (* Require Import BoolProd. *) *)

(* (* Declare ML Module "mTranslate". *) *)
(* (* Open Scope my_scope. *) *)


Tactic Notation "intro'" ident(X) := econstructor; [intro X|exact true].
Tactic Notation "intros'" := repeat (refine (mk_sig _ true); intro).
Tactic Notation "specialize'" hyp(H) uconstr(t) := apply π1 in H; specialize (H t).

(* Translate False. *)
(* Translate eq. *)

(* (* This translation allow to implement the negation of funext. *) *)
(* (* Test Quote  *) *)
Implement notFunext :
  ((forall (A B : Set) (f g : A -> B), (forall x:A, f x = g x) -> f = g) -> False).
Proof.
  intro' H.
  specialize' H unit.
  specialize' H unit.
  specialize' H (fun x => x; true).
  specialize' H (fun x => x; false). cbn in *.
  specialize' H (fun x => eq_refl; true).
  apply (f_equal (@π2 _ (fun _ => bool))) in H; cbn in H.
  discriminate H.
Defined.


(* (* (* A more constructive version on inhabited types. *) *) *)
(* (* Implement notFunext' : forall (A B : Type), *) *)
(* (*     B -> {f : A -> B & { g : A -> B & ((forall x, f x = g x) -> f = g) -> False}}. *) *)
(* (* Proof. *) *)
(* (*   intro' A. intro' B. intro' y. *) *)
(* (*   pose (f := fun _ : A => y). exists (f, true). exists (f, false). *) *)
(* (*   intro' H. *) *)
(* (*   specialize' H (fun x => eq_refl, true). *) *)
(* (*   apply (f_equal snd) in H; cbn in H. *) *)
(* (*   discriminate H. *) *)
(* (* Defined. *) *)


(* (* Check notFunext'. *) *)
(* (* Compute notFunext'ᶠ. *) *)


(* (* Definition notFunext'Nat := notFunext' nat nat. *) *)

(* (* (* If we want to prove some result about notFunext'Nat we first hae to extend the translation to it. *) *) *)
(* (* Translate notFunext'Nat. *) *)

(* (* (* Now we can postulate new principles about notFunext'Nat, always preserving consistency. *) *) *)
(* (* Implement notFunext'Nat01 : notFunext'Nat 0 = notFunext'Nat 1 -> False. *) *)
(* (* Proof. *) *)
(* (*   compute. refine (_, true). intro H. *) *)
(* (*   pose proof (f_equal (@projT1 _ _) H); cbn in *. *) *)
(* (*   apply (f_equal fst) in H0; cbn in *. *) *)
(* (*   assert ((fun _ : nat => 0) 0 = (fun _ : nat => 1) 0). *) *)
(* (*   change ((fun _ : nat => 0) 0 = (fun _ : nat => 1) 0). rewrite H0. reflexivity. *) *)
(* (*   discriminate H1. *) *)
(* (* Defined. *) *)



(* (* ** Some check of the translation on other types. *** *) *)

Implement f : forall (f : Type -> Type), f Type.
Abort.

Implement foo : forall A B : Type, forall (f g : A -> B), forall x, f x = g x.
Abort.

Implement wqd : forall (A : Type) (B : A -> Prop), forall x, B x.
Abort.

Implement foo : forall (A : Type) (a : A) (p : a = a), p = eq_refl a.
Abort.

