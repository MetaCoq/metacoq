Require Template.TemplateMonad.Core.
Require Template.TemplateMonad.Extractable.
Require Template.BasicAst Template.Ast.

Declare ML Module "template_coq".

(* note(gmm): i'm not exactly sure where this should go. *)
Notation "<% x %>" := (ltac:(let p y := exact y in quote_term x p))
  (only parsing).
