From MetaCoq.Template Require Import Ast.
From MetaCoq.Quotation.ToTemplate Require Import Init.
From MetaCoq.Quotation.ToTemplate.Common Require Import Environment.

Module QuoteEnvHelper <: QuoteEnvironmentHelperSig TemplateTerm Env := QuoteEnvironmentHelper TemplateTerm Env.

Module qQuoteEnvHelper <: QuotationOfQuoteEnvironmentHelper TemplateTerm Env QuoteEnvHelper.
  MetaCoq Run (tmMakeQuotationOfModule everything None "QuoteEnvHelper").
End qQuoteEnvHelper.
