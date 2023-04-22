From MetaCoq.Template Require Import Ast.
From MetaCoq.Quotation.ToTemplate Require Import Init.
From MetaCoq.Quotation.ToTemplate.QuotationOf.Common Require Import Environment.Sig.

Module qEnv <: QuotationOfEnvironment TemplateTerm Env.
  MetaCoq Run (tmMakeQuotationOfModule everything None "Env").
End qEnv.
