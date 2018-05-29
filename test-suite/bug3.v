(** Reported by Randy Pollack **)
Require Import Template.Loader.

Section foo.
  Variable x : nat.

  Fail Quote Definition this_should_fail := x.
  Fail Quote Recursively Definition this_should_fail := x.
End foo.