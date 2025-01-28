(* -*- coq-prog-args : ("-type-in-type") -*-  *)
From MetaCoq Require Import Checker.Loader.
Definition foo := 2 * 2.

MetaCoq Check foo.


(* The following compiles with -type-in-type option, *)
Fail Definition bar := let T := Type in (T : T).
(* then this should fail with "Type error while checking: Top.bar" *)
Fail MetaCoq Check bar.