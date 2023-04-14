From MetaCoq.Template Require Import Ast Typing.
From MetaCoq.Quotation.ToTemplate Require Import Init.
From MetaCoq.Quotation.ToTemplate.QuotationOf.Common Require Import EnvironmentTyping.Sig.

Module qTemplateEnvTyping <: QuotationOfEnvTyping TemplateTerm Env TemplateTermUtils TemplateEnvTyping.
  MetaCoq Run (tmMakeQuotationOfModule everything None "TemplateEnvTyping").
End qTemplateEnvTyping.
