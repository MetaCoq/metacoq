From MetaCoq.PCUIC Require Import PCUICAst.
From MetaCoq.Quotation.ToPCUIC Require Import Init.
From MetaCoq.Quotation.ToPCUIC.Common Require Import Environment.

Module QuotePCUICEnvironmentHelper <: QuoteEnvironmentHelperSig PCUICTerm PCUICEnvironment := QuoteEnvironmentHelper PCUICTerm PCUICEnvironment.

Module qQuotePCUICEnvironmentHelper <: QuotationOfQuoteEnvironmentHelper PCUICTerm PCUICEnvironment QuotePCUICEnvironmentHelper.
  MetaCoq Run (tmMakeQuotationOfModule everything None "QuotePCUICEnvironmentHelper").
End qQuotePCUICEnvironmentHelper.
