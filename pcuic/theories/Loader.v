(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import Loader.
From MetaCoq.PCUIC.PCUICTemplateMonad Require Core.
From MetaCoq.PCUIC Require Import TemplateMonadToPCUIC.

Notation "<% x %>" := (ltac:(let p y := exact y in let p y := run_template_program (@monad_trans y) p in quote_term x p))
  (only parsing).
