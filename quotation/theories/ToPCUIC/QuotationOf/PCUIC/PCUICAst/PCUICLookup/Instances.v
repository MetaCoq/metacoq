From MetaCoq.PCUIC Require Import PCUICAst.
From MetaCoq.Quotation.ToPCUIC Require Import Init.
From MetaCoq.Quotation.ToPCUIC.QuotationOf.Common Require Import EnvironmentTyping.Sig.

Module qPCUICLookup <: QuotationOfLookup PCUICTerm PCUICEnvironment PCUICLookup.
  MetaCoq Run (tmMakeQuotationOfModule everything None "PCUICLookup").
End qPCUICLookup.
