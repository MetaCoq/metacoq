From MetaCoq.Template Require Import TypingWf.
From MetaCoq.Quotation.ToTemplate Require Import Init.
From MetaCoq.Quotation.ToTemplate Require Import (hints) Coq.Init.
From MetaCoq.Quotation.ToTemplate.Utils Require Import (hints) All_Forall.
From MetaCoq.Quotation.ToTemplate.Common Require Import (hints) BasicAst.
From MetaCoq.Quotation.ToTemplate.Template Require Import (hints) Ast WfAst.

#[export] Instance quote_wf_inductive_body {Σ idecl} : ground_quotable (@wf_inductive_body Σ idecl) := ltac:(destruct 1; exact _).
