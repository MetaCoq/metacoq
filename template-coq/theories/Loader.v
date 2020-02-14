From MetaCoq Require Template.TemplateMonad.Core
  Template.TemplateMonad.Extractable
  Template.BasicAst Template.Ast
  Template.Constants.

Declare ML Module "template_coq".

(* note(gmm): i'm not exactly sure where this should go. *)
Notation "<% x %>" := (ltac:(let p y := exact y in quote_term x p))
  (only parsing).
