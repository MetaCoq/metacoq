Require Import MetaCoq.Template.Loader.

Definition f := fun (n : nat) =>
  match n with
  | 0 => 0
  | S n => n
  end.


MetaCoq Quote Definition f_quoted :=
  ltac:(let t := eval cbv in f in exact t).

MetaCoq Unquote Definition f_from_syntax :=
  ltac:(let t := eval cbv in f_quoted in exact t).

Check eq_refl : f = f_from_syntax.
