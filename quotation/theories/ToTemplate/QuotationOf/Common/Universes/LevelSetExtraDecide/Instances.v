From MetaCoq.Common Require Import Universes.
From MetaCoq.Quotation.ToTemplate Require Import Init.
From MetaCoq.Quotation.ToTemplate.QuotationOf.Utils Require Import MCMSets.Sig.

Module qLevelSetExtraDecide <: MSetAVL.QuotationOfDecide LevelSet.E LevelSet LevelSetExtraDecide.
  MetaCoq Run (tmMakeQuotationOfModule everything None "LevelSetExtraDecide").
End qLevelSetExtraDecide.
