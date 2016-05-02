Require Import Template.Template.

Local Open Scope string_scope.

Notation test := (let x := 2 in x).

Quote Definition letin_syntax := test.

Make Definition letin_from_syntax :=
  ltac:(let r := eval red in letin_syntax in exact r).

Check (eq_refl : letin_from_syntax = test).