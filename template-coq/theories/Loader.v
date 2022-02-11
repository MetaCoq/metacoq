(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require TemplateMonad.Core
  TemplateMonad.Extractable BasicAst Ast Constants.

Declare ML Module "coq-metacoq-template-coq.plugin".

Notation "<% x %>" := (ltac:(let p y := exact y in quote_term x p))
  (only parsing).
