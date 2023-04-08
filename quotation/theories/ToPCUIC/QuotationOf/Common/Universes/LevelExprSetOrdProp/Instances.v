From MetaCoq.Common Require Import Universes.
From MetaCoq.Quotation.ToPCUIC Require Import Init.
From MetaCoq.Quotation.ToPCUIC.QuotationOf.Coq.Structures Require Import Orders.Sig OrdersAlt.Sig OrdersFacts.Sig.
From MetaCoq.Quotation.ToPCUIC.QuotationOf.Coq.MSets Require Import MSetProperties.Sig MSetDecide.Sig MSetFacts.Sig.
Import List.ListNotations.
Local Open Scope list_scope.

Module qLevelExprSetOrdProp <: QuotationOfOrdProperties LevelExprSet LevelExprSetOrdProp.
  Module qME <: QuotationOfOrderedTypeFacts LevelExprSet.E LevelExprSetOrdProp.ME.
    MetaCoq Run (tmMakeQuotationOfModule everything None "LevelExprSetOrdProp.ME").
  End qME.
  Module qML. (* OrderedTypeLists(M.E). *)
    MetaCoq Run (tmMakeQuotationOfModule everything None "LevelExprSetOrdProp.ML").
  End qML.
  Module qP <: QuotationOfWProperties LevelExprSet LevelExprSetOrdProp.P.
    Module qDec <: QuotationOfWDecideOn LevelExpr LevelExprSet LevelExprSetOrdProp.P.Dec.
      MetaCoq Run (tmMakeQuotationOfModule everything None "LevelExprSetOrdProp.P.Dec").
    End qDec.
    Module qFM <: QuotationOfWFactsOn LevelExpr LevelExprSet LevelExprSetOrdProp.P.FM.
      MetaCoq Run (tmMakeQuotationOfModule everything None "LevelExprSetOrdProp.P.FM").
    End qFM.
    MetaCoq Run (tmMakeQuotationOfModule (all_submodules_except [["Dec"]; ["FM"]]%bs) None "LevelExprSetOrdProp.P").
  End qP.
  MetaCoq Run (tmMakeQuotationOfModule (all_submodules_except [["ME"]; ["ML"]; ["P"]]%bs) None "LevelExprSetOrdProp").
End qLevelExprSetOrdProp.
