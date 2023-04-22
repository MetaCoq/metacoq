From MetaCoq.PCUIC Require Import PCUICAst.
From MetaCoq.Quotation.ToPCUIC Require Import Init.
From MetaCoq.Quotation.ToPCUIC.QuotationOf.Common Require Import EnvironmentTyping.Sig.

Module qPCUICGlobalMaps <: QuotationOfGlobalMaps PCUICTerm PCUICEnvironment PCUICTermUtils PCUICEnvTyping PCUICConversion PCUICLookup PCUICGlobalMaps.
  MetaCoq Run (tmMakeQuotationOfModule everything None "PCUICGlobalMaps").
End qPCUICGlobalMaps.
