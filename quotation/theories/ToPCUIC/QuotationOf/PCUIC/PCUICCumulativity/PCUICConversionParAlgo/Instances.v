From MetaCoq.PCUIC Require Import PCUICAst PCUICCumulativity.
From MetaCoq.Quotation.ToPCUIC Require Import Init.
From MetaCoq.Quotation.ToPCUIC.QuotationOf.Common Require Import EnvironmentTyping.Sig.

Module qPCUICConversionParAlgo <: QuotationOfConversionPar PCUICTerm PCUICEnvironment PCUICTermUtils PCUICEnvTyping PCUICConversionParAlgo.
  MetaCoq Run (tmMakeQuotationOfModule everything None "PCUICConversionParAlgo").
End qPCUICConversionParAlgo.
