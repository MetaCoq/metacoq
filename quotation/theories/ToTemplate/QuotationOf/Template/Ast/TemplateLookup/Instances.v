From MetaCoq.Template Require Import Ast.
From MetaCoq.Quotation.ToTemplate Require Import Init.
From MetaCoq.Quotation.ToTemplate.QuotationOf.Common Require Import EnvironmentTyping.Sig.

Module qTemplateLookup <: QuotationOfLookup TemplateTerm Env TemplateLookup.
  MetaCoq Run (tmMakeQuotationOfModule everything None "TemplateLookup").
End qTemplateLookup.
