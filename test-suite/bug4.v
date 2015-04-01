(** Reported by Randy Pollack **)
Require Import Template.Template.

Definition I (t:Type) (x:t) : t := x.
Definition II := I (forall t:Type, t -> t) I.
Quote Recursively Definition qII := II.
Print qII.

Section foo.
  Variable x : nat.

  Fail Quote Definition this_should_fail := x.
  Fail Quote Recursively Definition this_should_fail := x.
End foo.