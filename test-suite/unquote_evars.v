From MetaCoq.Template Require Import All.
Import MCMonadNotation.

(* Unquoting evars. *)
MetaCoq Run (mlet t <- tmUnquote (tEvar fresh_evar_id []) ;; tmPrint t).
MetaCoq Run (mlet t <- tmUnquoteTyped nat (tEvar fresh_evar_id []) ;; tmPrint t).

(* Unquoting evars, with typeclass resolution. *)
Existing Class nat.
Existing Instance O.

MetaCoq Quote Definition quoted_nat := nat.
MetaCoq Run (
  mlet t <- tmUnquote (tCast (tEvar fresh_evar_id []) Cast quoted_nat) ;;
  tmEval cbv t
).
MetaCoq Run (
  mlet t <- tmUnquoteTyped nat (tEvar fresh_evar_id []) ;;
  tmEval cbv t
).