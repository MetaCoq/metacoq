From MetaCoq.Template Require Import Ast Typing.
From MetaCoq.Quotation.ToTemplate Require Import Init.
From MetaCoq.Quotation.ToTemplate.QuotationOf.Common Require Import EnvironmentTyping.Sig.

Module qTemplateConversion <: QuotationOfConversion TemplateTerm Env TemplateTermUtils TemplateEnvTyping TemplateConversion.
  MetaCoq Run (tmMakeQuotationOfModule everything None "TemplateConversion").
End qTemplateConversion.
