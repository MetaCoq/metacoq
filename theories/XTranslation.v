From Template Require Import Ast XAst XLiftSubst Typing XTyping.

(* We'll see later if we really need weakening, uniqueness and inversion of
   typing.
 *)

Section Translation.

(* Transport in the target *)
(* We want transport to be a symbolic construction, do we need to be able to
   match on it? If so, we'll need to change the target syntax as well... *)
Context (transport : sort -> xterm -> xterm -> xterm -> xterm -> xterm).
Context (type_transport :
  forall Σ Γ s T1 T2 p t ,
    Σ ;;; Γ |-- p : xEq (succ_sort s) (xSort s) T1 T2 ->
    Σ ;;; Γ |-- t : T1 ->
    Σ ;;; Γ |-- transport s T1 T2 p t : T2
).

(*! Relation for translated expressions *)

End Translation.