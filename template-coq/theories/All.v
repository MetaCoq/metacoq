(* Distributed under the terms of the MIT license.   *)

From MetaCoq.Template Require Export
     utils         (* Utility functions *)
     monad_utils   (* Monadic notations *)
     BasicAst      (* The basic AST structures *)
     Ast           (* The term AST *)
     AstUtils      (* Utilities on the AST *)
     Induction     (* Induction *)
     LiftSubst     (* Lifting and substitution for terms *)
     UnivSubst     (* Substitution of universe instances *)
     TemplateMonad (* The TemplateMonad *)
     Loader        (* The plugin *).

(* note(gmm): i'm not exactly sure where this should go. *)
Notation "<% x %>" := (ltac:(let p y := exact y in quote_term x p))
  (only parsing).
