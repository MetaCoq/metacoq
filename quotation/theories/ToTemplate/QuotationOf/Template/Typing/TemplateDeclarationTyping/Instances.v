From MetaCoq.Template Require Import Ast Typing.
From MetaCoq.Quotation.ToTemplate Require Import Init.
From MetaCoq.Quotation.ToTemplate.QuotationOf.Common Require Import EnvironmentTyping.Sig.

Module qTemplateDeclarationTyping <: QuotationOfDeclarationTyping TemplateTerm Env TemplateTermUtils TemplateEnvTyping TemplateConversion TemplateConversionPar TemplateTyping TemplateLookup TemplateGlobalMaps TemplateDeclarationTyping.
  MetaCoq Run (tmMakeQuotationOfModule everything None "TemplateDeclarationTyping").
End qTemplateDeclarationTyping.
