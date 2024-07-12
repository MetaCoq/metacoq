From MetaCoq.Common Require Import Kernames.
From MetaCoq.Quotation.ToPCUIC Require Import Init.
From MetaCoq.Quotation.ToPCUIC.QuotationOf.Stdlib.Structures Require Import Orders.Sig OrdersAlt.Sig OrdersFacts.Sig.
From MetaCoq.Quotation.ToPCUIC.QuotationOf.Stdlib.MSets Require Import MSetProperties.Sig MSetDecide.Sig MSetFacts.Sig.
Import List.ListNotations.
Local Open Scope list_scope.

Module qKernameSetOrdProp <: QuotationOfOrdProperties KernameSet KernameSetOrdProp.
  Module qME <: QuotationOfOrderedTypeFacts KernameSet.E KernameSetOrdProp.ME.
    MetaCoq Run (tmMakeQuotationOfModule everything None "KernameSetOrdProp.ME").
  End qME.
  Module qML. (* OrderedTypeLists(M.E). *)
    MetaCoq Run (tmMakeQuotationOfModule everything None "KernameSetOrdProp.ML").
  End qML.
  Module qP <: QuotationOfWProperties KernameSet KernameSetOrdProp.P.
    Module qDec <: QuotationOfWDecideOn Kername KernameSet KernameSetOrdProp.P.Dec.
      MetaCoq Run (tmMakeQuotationOfModule everything None "KernameSetOrdProp.P.Dec").
    End qDec.
    Module qFM <: QuotationOfWFactsOn Kername KernameSet KernameSetOrdProp.P.FM.
      MetaCoq Run (tmMakeQuotationOfModule everything None "KernameSetOrdProp.P.FM").
    End qFM.
    MetaCoq Run (tmMakeQuotationOfModule (all_submodules_except [["Dec"]; ["FM"]]%bs) None "KernameSetOrdProp.P").
  End qP.
  MetaCoq Run (tmMakeQuotationOfModule (all_submodules_except [["ME"]; ["ML"]; ["P"]]%bs) None "KernameSetOrdProp").
End qKernameSetOrdProp.
