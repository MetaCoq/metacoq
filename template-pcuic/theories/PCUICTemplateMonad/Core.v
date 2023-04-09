(* Distributed under the terms of the MIT license. *)
From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import Ast AstUtils Common.
From MetaCoq.Template.TemplateMonad Require Export Core.
From MetaCoq.PCUIC Require Import PCUICAst.
From MetaCoq.TemplatePCUIC Require Import TemplateMonadToPCUIC TemplateToPCUIC PCUICToTemplate.

Local Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
Import MCMonadNotation.

Definition tmQuote@{t u} {A:Type@{t}} (a : A) : TemplateMonad@{t u} PCUICAst.term := qa <- tmQuote a;; monad_trans qa.
Definition tmQuoteRecTransp@{t u} {A:Type@{t}} (a : A) (bypass_opacity : bool) : TemplateMonad@{t u} PCUICProgram.pcuic_program :=
  (p <- tmQuoteRecTransp a bypass_opacity;; ret (trans_template_program p)).
Definition tmQuoteInductive@{t u} (kn : kername) : TemplateMonad@{t u} mutual_inductive_body := tmQuoteInductive@{t u} kn.
Definition tmQuoteConstant@{t u} (kn : kername) (bypass_opacity : bool) : TemplateMonad@{t u} constant_body :=
  cb <- tmQuoteConstant kn bypass_opacity;; monad_trans_constant_body cb.
Definition tmMkInductive@{t u} (b : bool) (mie : mutual_inductive_entry) : TemplateMonad@{t u} unit
  := mie <- ret (trans_mutual_inductive_entry mie);; tmMkInductive b mie.
Definition tmUnquote@{t u} (t : PCUICAst.term) : TemplateMonad@{t u} typed_term := t <- ret (PCUICToTemplate.trans t);; tmUnquote t.
Definition tmUnquoteTyped@{t u} A (t : PCUICAst.term) : TemplateMonad@{t u} A := t <- ret (PCUICToTemplate.trans t);; tmUnquoteTyped A t.

(** We keep the original behaviour of [tmQuoteRec]: it quotes all the dependencies regardless of the opaqueness settings *)
Definition tmQuoteRec {A} (a : A) := tmQuoteRecTransp a true.

Definition tmMkDefinition@{t u} (id : ident) (tm : PCUICAst.term) : TemplateMonad@{t u} unit := tm <- ret (PCUICToTemplate.trans tm);; tmMkDefinition id tm.
