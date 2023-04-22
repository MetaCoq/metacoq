From MetaCoq.PCUIC Require Import PCUICAst.
From MetaCoq.Quotation.ToPCUIC Require Import Init.
From MetaCoq.Quotation.ToPCUIC.QuotationOf.Common Require Import Environment.Sig.

Module qPCUICTerm <: QuotationOfTerm PCUICTerm.
  MetaCoq Run (tmMakeQuotationOfModule everything None "PCUICTerm").
End qPCUICTerm.
