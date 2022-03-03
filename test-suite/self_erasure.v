From MetaCoq.Erasure Require Import Loader Erasure.
From MetaCoq.SafeChecker Require Import PCUICSafeChecker.
Set MetaCoq Timing.
(* 1sec *)
MetaCoq Fast Erase @erase_and_print_template_program.
(* 4sec *)
Time MetaCoq Erase @typecheck_program.
