From MetaCoq.Erasure Require Import Loader Erasure.
From MetaCoq.SafeChecker Require Import PCUICSafeChecker.

(* 32sec *)
MetaCoq Erase @erase_and_print_template_program.

(* 40sec *)
Time MetaCoq Erase @typecheck_program.
