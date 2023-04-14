From MetaCoq.Common Require Import Universes.
From MetaCoq.Quotation.ToPCUIC Require Import Init.
From MetaCoq.Quotation.ToPCUIC.QuotationOf.Coq.MSets Require Import MSetAVL.Sig.

Module qLevelSet <: MSetAVL.QuotationOfMake Level LevelSet.
  MetaCoq Run (tmMakeQuotationOfModule everything None "LevelSet").
End qLevelSet.
