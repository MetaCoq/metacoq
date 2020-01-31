
Definition transport {A} (P : A -> Type) {x y : A} (e : x = y) : P x -> P y
  := fun u => eq_rect x P u y e.

Notation "p # x" := (transport _ p x) (right associativity, at level 65).
