From MetaCoq.Template Require Import Ast.
From MetaCoq.Quotation.ToTemplate Require Import Init.
From MetaCoq.Quotation.ToTemplate.QuotationOf.Common Require Import Environment.Sig.

Module qTemplateTermUtils <: QuotationOfTermUtils TemplateTerm Env TemplateTermUtils.
  MetaCoq Run (tmMakeQuotationOfModule everything None "TemplateTermUtils").
End qTemplateTermUtils.
