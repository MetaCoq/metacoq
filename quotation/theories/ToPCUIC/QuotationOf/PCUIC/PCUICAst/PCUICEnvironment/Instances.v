From MetaCoq.PCUIC Require Import PCUICAst.
From MetaCoq.Quotation.ToPCUIC Require Import Init.
From MetaCoq.Quotation.ToPCUIC.QuotationOf.Common Require Import Environment.Sig.

Module qPCUICEnvironment <: QuotationOfEnvironment PCUICTerm PCUICEnvironment.
  MetaCoq Run (tmMakeQuotationOfModule everything None "PCUICEnvironment").
End qPCUICEnvironment.
