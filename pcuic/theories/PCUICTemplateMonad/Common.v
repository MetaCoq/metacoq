(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import utils Ast.
From MetaCoq.Template.TemplateMonad Require Export Common.
From MetaCoq.PCUIC Require Import PCUICAst TemplateMonadToPCUIC TemplateToPCUIC PCUICToTemplate.

Local Set Universe Polymorphism.
Import MCMonadNotation.

Section with_tc.
  Context {TM : TMInstance}.
  Local Notation TemplateMonad := (@TemplateMonad TM).
  Context {M : Monad TemplateMonad}.

  Definition tmQuoteInductive (kn : kername) : TemplateMonad mutual_inductive_body := tmQuoteInductive kn.
  Definition tmQuoteConstant (kn : kername) (bypass_opacity : bool) : TemplateMonad constant_body :=
    cb <- tmQuoteConstant TM kn bypass_opacity;; monad_trans_constant_body cb.
  (*
Definition tmMkInductive (b : bool) (mie : mutual_inductive_entry) : TemplateMonad unit
  := tmMkInductive b (PCUICToTemplate.trans_mutual_inductive_entry mie).
   *)
End with_tc.
