From MetaCoq.Template Require Import Ast Typing.
From MetaCoq.Quotation.ToTemplate Require Import Init.
From MetaCoq.Quotation.ToTemplate.QuotationOf.Common Require Import EnvironmentTyping.Sig.

Module qTemplateTyping <: QuotationOfTyping TemplateTerm Env TemplateTermUtils TemplateEnvTyping TemplateConversion TemplateConversionPar TemplateTyping.
  MetaCoq Run (tmMakeQuotationOfModule everything None "TemplateTyping").
End qTemplateTyping.
