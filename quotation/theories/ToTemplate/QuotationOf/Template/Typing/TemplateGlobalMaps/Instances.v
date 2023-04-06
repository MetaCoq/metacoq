From MetaCoq.Template Require Import Ast Typing.
From MetaCoq.Quotation.ToTemplate Require Import Init.
From MetaCoq.Quotation.ToTemplate.QuotationOf.Common Require Import EnvironmentTyping.Sig.

Module qTemplateGlobalMaps <: QuotationOfGlobalMaps TemplateTerm Env TemplateTermUtils TemplateEnvTyping TemplateConversion TemplateLookup TemplateGlobalMaps.
  MetaCoq Run (tmMakeQuotationOfModule everything None "TemplateGlobalMaps").
End qTemplateGlobalMaps.
