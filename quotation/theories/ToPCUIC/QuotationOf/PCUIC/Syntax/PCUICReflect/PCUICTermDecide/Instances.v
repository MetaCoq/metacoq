From MetaCoq.PCUIC Require Import PCUICAst Syntax.PCUICReflect.
From MetaCoq.Quotation.ToPCUIC Require Import Init.
From MetaCoq.Quotation.ToPCUIC.QuotationOf.Common Require Import Environment.Sig.

Module qPCUICTermDecide <: QuotationOfTermDecide PCUICTerm PCUICTermDecide.
  MetaCoq Run (tmMakeQuotationOfModule everything None "PCUICTermDecide").
End qPCUICTermDecide.
