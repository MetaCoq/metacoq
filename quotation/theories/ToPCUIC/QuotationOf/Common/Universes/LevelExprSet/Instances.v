From MetaCoq.Common Require Import Universes.
From MetaCoq.Quotation.ToPCUIC Require Import Init.
From MetaCoq.Quotation.ToPCUIC.QuotationOf.Stdlib.MSets Require Import MSetList.Sig.

Module qLevelExprSet <: MSetList.QuotationOfMakeWithLeibniz LevelExpr LevelExprSet.
  MetaCoq Run (tmMakeQuotationOfModule everything None "LevelExprSet").
End qLevelExprSet.
