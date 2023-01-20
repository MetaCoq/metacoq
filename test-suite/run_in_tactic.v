From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.
Import MCMonadNotation.

Goal True.
  let k x := pose (y := x) in
  run_template_program (tmPrint "test" ;; tmQuote plus) k.

  Fail let k x := pose (y := x) in
  run_template_program (tmLemma "test" nat) k.
Abort.
