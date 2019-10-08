Require Import MetaCoq.Template.Loader.

Local Open Scope string_scope.

Notation test := (let x := 2 in x).

MetaCoq Quote Definition letin_syntax := test.

MetaCoq Unquote Definition letin_from_syntax :=
  ltac:(let r := eval red in letin_syntax in exact r).

Check (eq_refl : letin_from_syntax = test).
