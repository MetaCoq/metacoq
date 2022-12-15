(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import utils Ast AstUtils Common.
From MetaCoq.Template.TemplateMonad Require Export Core.
From MetaCoq.PCUIC Require Import PCUICAst TemplateMonadToPCUIC TemplateToPCUIC PCUICToTemplate.

Local Set Universe Polymorphism.
Import MCMonadNotation.

Definition tmQuote {A:Type} (a : A) : TemplateMonad PCUICAst.term := (qa <- tmQuote a;; monad_trans qa).
Definition tmQuoteRecTransp {A:Type} (a : A) (bypass_opacity : bool) : TemplateMonad PCUICProgram.pcuic_program :=
  (p <- tmQuoteRecTransp a bypass_opacity;; ret (trans_template_program p)).
Definition tmQuoteInductive (kn : kername) : TemplateMonad mutual_inductive_body := tmQuoteInductive kn.
Definition tmQuoteConstant (kn : kername) (bypass_opacity : bool) : TemplateMonad constant_body :=
  cb <- tmQuoteConstant kn bypass_opacity;; monad_trans_constant_body cb.
Definition tmMkInductive (b : bool) (mie : mutual_inductive_entry) : TemplateMonad unit
  := tmMkInductive b (trans_mutual_inductive_entry mie).
Definition tmUnquote (t : PCUICAst.term) : TemplateMonad typed_term := tmUnquote (PCUICToTemplate.trans t).
Definition tmUnquoteTyped A (t : PCUICAst.term) : TemplateMonad A := tmUnquoteTyped A (PCUICToTemplate.trans t).

(** We keep the original behaviour of [tmQuoteRec]: it quotes all the dependencies regardless of the opaqueness settings *)
Definition tmQuoteRec {A} (a : A) := tmQuoteRecTransp a true.

Definition tmMkDefinition (id : ident) (tm : PCUICAst.term) : TemplateMonad unit := tmMkDefinition id (PCUICToTemplate.trans tm).
