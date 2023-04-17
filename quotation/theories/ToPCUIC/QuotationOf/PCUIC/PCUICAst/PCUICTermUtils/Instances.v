From MetaCoq.PCUIC Require Import PCUICAst.
From MetaCoq.Quotation.ToPCUIC Require Import Init.
From MetaCoq.Quotation.ToPCUIC.QuotationOf.Common Require Import Environment.Sig.

Module qPCUICTermUtils <: QuotationOfTermUtils PCUICTerm PCUICEnvironment PCUICTermUtils.
  MetaCoq Run (tmMakeQuotationOfModule everything None "PCUICTermUtils").
End qPCUICTermUtils.
