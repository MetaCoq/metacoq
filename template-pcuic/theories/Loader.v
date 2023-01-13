(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import Loader.
From MetaCoq.TemplatePCUIC.PCUICTemplateMonad Require Core.
From MetaCoq.TemplatePCUIC Require Import.TemplateMonadToPCUIC.

Set Warnings "-notation-overridden".
(* Work around COQBUG(https://github.com/coq/coq/issues/16715) *)
Notation "<% x %>" := (match monad_trans return _ with monad_trans => ltac:(let p y := exact y in let p y := run_template_program (monad_trans y) p in quote_term x p) end)
  (only parsing).

(* Work around COQBUG(https://github.com/coq/coq/issues/16715) with [match] *)
(* Use [return _] to avoid running the program twice on failure *)
Notation "<# x #>" := (match PCUICTemplate.Monad.Core.tmQuoteRec x return _ with qx => ltac:(let p y := exact y in run_template_program qx p) end)
  (only parsing).
Set Warnings "+notation-overridden".
