Require Import Template.All.
Require Import List String.
Import ListNotations MonadNotation.

Goal True.
  let k x := pose (y := x) in
  run_template_program (tmPrint "test" ;; tmQuote plus) k.
Abort.
