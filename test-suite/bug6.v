Require Import Template.Template.

Definition I (t:Type) (x:t) : t := x.
Definition II := I (forall t:Type, t -> t) I.
Quote Definition qII := Eval compute in II.
