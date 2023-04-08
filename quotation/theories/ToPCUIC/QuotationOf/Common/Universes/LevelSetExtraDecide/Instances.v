From MetaCoq.Common Require Import Universes.
From MetaCoq.Quotation.ToPCUIC Require Import Init.
From MetaCoq.Quotation.ToPCUIC.QuotationOf.Utils Require Import MCMSets.Sig.

Module qLevelSetExtraDecide <: MSetAVL.QuotationOfDecide LevelSet.E LevelSet LevelSetExtraDecide.
  MetaCoq Run (tmMakeQuotationOfModule everything None "LevelSetExtraDecide").
End qLevelSetExtraDecide.
