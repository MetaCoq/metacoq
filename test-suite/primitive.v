From Coq Require Import String.
From MetaCoq.Template Require Import monad_utils All.
From Coq.Numbers.Cyclic Require Import Int63.

Local Open Scope string_scope.
Import MCMonadNotation.

Definition bigint : Int63.int := 542985047%int63.

Notation eval_hnf := (tmEval hnf).
Notation eval := (tmEval all).

MetaCoq Run (eval_hnf bigint >>= 
            (fun x => tmQuote (x + 1)%int63) >>= 
            tmMkDefinition "foo").

Print foo.

MetaCoq Run (eval_hnf bigint >>= 
            (fun x => tmQuote (x + 1)%int63 >>= fun q =>
            tmUnquoteTyped int q >>= fun unq =>
            tmPrint unq >>= fun _ =>
            tmLemma "foo'" (bigint + 1 = unq)%int63 >>= 
            fun x => tmPrint x)).

From Coq Require Import Int63 PrimFloat.

Definition f := (of_int63 bigint / 3)%float.
Eval lazy in f.
MetaCoq Run (tmEval lazy f >>= 
            (fun x => tmQuote (x + 1)%float) >>= 
            tmMkDefinition "fplus1").

MetaCoq Run (tmUnquoteTyped float (tFloat f) >>= 
  (fun x : float => tmPrint x >>= 
   fun _ => tmQuote x >>= tmMkDefinition "somefloat")).
   Print somefloat.