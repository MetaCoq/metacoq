From MetaCoq.Template Require Import Ast Typing.
From MetaCoq.Quotation.ToTemplate Require Import Init.
From MetaCoq.Quotation.ToTemplate.QuotationOf.Common Require Import EnvironmentTyping.Sig.

Module qTemplateConversionPar <: QuotationOfConversionPar TemplateTerm Env TemplateTermUtils TemplateEnvTyping TemplateConversionPar.
  MetaCoq Run (tmMakeQuotationOfModule everything None "TemplateConversionPar").
End qTemplateConversionPar.
