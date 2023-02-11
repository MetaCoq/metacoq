From MetaCoq.Template Require Import Ast.
From MetaCoq.Quotation.ToTemplate Require Import Init.
From MetaCoq.Quotation.ToTemplate.QuotationOf.Common Require Import Environment.Sig.

Module qTemplateTerm <: QuotationOfTerm TemplateTerm.
  MetaCoq Run (tmMakeQuotationOfModule everything None "TemplateTerm").
End qTemplateTerm.
