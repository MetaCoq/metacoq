
Notation "'precompose'" := (fun R f x y => R (f x) (f y)) (only parsing).

Definition on_rel {A B} (R : A -> A -> Prop) (f : B -> A) : B -> B -> Prop :=
  fun x y => R (f x) (f y).

Definition on_Trel {A B} (R : A -> A -> Type) (f : B -> A) : B -> B -> Type :=
  fun x y => R (f x) (f y).

Notation Trel_conj R S :=
  (fun x y => R x y * S x y)%type.

Notation on_Trel_eq R f g :=
  (fun x y => (R (f x) (f y) * (g x = g y)))%type.
