From MetaCoq.Template Require Import Ast ReflectAst.
From MetaCoq.Quotation.ToTemplate Require Import Init.
From MetaCoq.Quotation.ToTemplate.QuotationOf.Common Require Import Environment.Sig.

Module qEnvDecide <: QuotationOfEnvironmentDecide TemplateTerm Env EnvDecide.
  MetaCoq Run (tmMakeQuotationOfModule everything None "EnvDecide").
End qEnvDecide.
