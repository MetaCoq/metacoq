From MetaCoq.Common Require Import Universes.
From MetaCoq.Quotation.ToPCUIC Require Import Init.
From MetaCoq.Quotation.ToPCUIC.QuotationOf.Utils Require Import MCMSets.Sig.
Import List.ListNotations.
Local Open Scope list_scope.

Module qLevelSetExtraOrdProp <: QuotationOfExtraOrdProperties LevelSet LevelSetOrdProp LevelSetExtraOrdProp.
  Module qP <: QuotationOfWExtraPropertiesOn LevelSet.E LevelSet LevelSetOrdProp.P LevelSetExtraOrdProp.P.
    MetaCoq Run (tmMakeQuotationOfModule everything None "LevelSetExtraOrdProp.P").
  End qP.
  MetaCoq Run (tmMakeQuotationOfModule (all_submodules_except [["P"]]%bs) None "LevelSetExtraOrdProp").
End qLevelSetExtraOrdProp.
