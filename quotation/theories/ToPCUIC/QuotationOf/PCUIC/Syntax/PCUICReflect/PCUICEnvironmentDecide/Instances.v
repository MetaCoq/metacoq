From MetaCoq.PCUIC Require Import PCUICAst Syntax.PCUICReflect.
From MetaCoq.Quotation.ToPCUIC Require Import Init.
From MetaCoq.Quotation.ToPCUIC.QuotationOf.Common Require Import Environment.Sig.

Module qPCUICEnvironmentDecide <: QuotationOfEnvironmentDecide PCUICTerm PCUICEnvironment PCUICEnvironmentDecide.
  MetaCoq Run (tmMakeQuotationOfModule everything None "PCUICEnvironmentDecide").
End qPCUICEnvironmentDecide.
