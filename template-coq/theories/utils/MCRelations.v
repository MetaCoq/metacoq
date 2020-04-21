
Notation "'precompose'" := (fun R f x y => R (f x) (f y)) (only parsing).

Definition on_rel {A B} (R : A -> A -> Prop) (f : B -> A) : B -> B -> Prop :=
  fun x y => R (f x) (f y).

Definition on_Trel {A B} (R : A -> A -> Type) (f : B -> A) : B -> B -> Type :=
  fun x y => R (f x) (f y).
Arguments on_Trel {_ _} _ _ _ _/.

Notation Trel_conj R S :=
  (fun x y => R x y * S x y)%type.

Notation on_Trel_eq R f g :=
  (fun x y => (R (f x) (f y) * (g x = g y)))%type.

(* Definition MR {T M} (R : M -> M -> Prop) (m : T -> M) (x y: T): Prop := R (m x) (m y). *)

(* From measure_wf of Program.Wf *)
Lemma wf_precompose {T M} (R : M -> M -> Prop) (m : T -> M) :
  well_founded R -> well_founded (precompose R m).
Proof with auto.
  unfold well_founded. intro wf.
  cut (forall (a: M) (a0: T), m a0 = a -> Acc (precompose R m) a0).
  + intros.
    apply (H (m a))...
  + apply (@well_founded_ind M R wf (fun mm => forall a, m a = mm -> Acc _ a)).
    intros. apply Acc_intro.
    intros. rewrite H0 in H1. apply (H (m y))...
Defined.

