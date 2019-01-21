(* Distributed under the terms of the MIT license.   *)

From Template Require Export
     utils         (* Utility functions *)
     monad_utils   (* Monadic notations *)
     Ast           (* The term AST *)
     TemplateMonad (* The TemplateMonad *)
     AstUtils      (* Utilities on the AST *)
     Loader        (* Declaration of the Template Coq plugin *)
     Induction     (* Induction *)
     LiftSubst     (* Lifting and substitution for terms *)
     WeakSubst     (* Weakening and substitution lemmas *)
     UnivSubst     (* Substitution of universe instances *)
     Typing        (* Typing judgment *)
     Checker       (* Partial typechecker implementation *)
     Retyping      (* Fast retyping judgment *).

(* note(gmm): i'm not exactly sure where this should go. *)
Notation "<% x %>" := (ltac:(let p y := exact y in quote_term x p)).
