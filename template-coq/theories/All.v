(* Distributed under the terms of the MIT license.   *)

From MetaCoq.Template Require Export
     utils         (* Utility functions *)
     monad_utils   (* Monadic notations *)
     BasicAst      (* The basic AST structures *)
     Ast           (* The term AST *)
     uGraph        (* The graph of universes *)
     TemplateMonad (* The TemplateMonad *)
     AstUtils      (* Utilities on the AST *)
     (* Loader        (* Declaration of the Template Coq plugin *) *)
     Induction     (* Induction *)
     LiftSubst     (* Lifting and substitution for terms *)
     UnivSubst     (* Substitution of universe instances *)
     Typing        (* Typing judgment *)
     Weakening     (* Weakening lemmas *)
     Checker       (* Partial typechecker implementation *)
     Retyping      (* Fast retyping judgment *).

(* note(gmm): i'm not exactly sure where this should go. *)
Notation "<% x %>" := (ltac:(let p y := exact y in quote_term x p))
  (only parsing).
