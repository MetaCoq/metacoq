From Stdlib.MSets Require Import MSetProperties.
From MetaCoq.Utils Require Import MCMSets.
From MetaCoq.Quotation.ToPCUIC Require Import Init.
From MetaCoq.Quotation.ToPCUIC.QuotationOf.Stdlib.Structures Require Import OrdersFacts.Sig.
From MetaCoq.Quotation.ToPCUIC.QuotationOf.Stdlib.MSets Require Import MSetFacts.Sig MSetDecide.Sig.
Import List.ListNotations.
Local Open Scope list_scope.

Module Export MSets.
  Module Type QuotationOfWPropertiesOn (E : DecidableType) (M : WSetsOn E) (F : WPropertiesOnSig E M).
    Module qDec := Nop <+ QuotationOfWDecideOn E M F.Dec.
    Module qFM := Nop <+ QuotationOfWFactsOn E M F.FM.
    Export (hints) qDec qFM.
    MetaCoq Run (tmDeclareQuotationOfModule (all_submodules_except [["Dec"]; ["FM"]]%bs) (Some export) "F").
  End QuotationOfWPropertiesOn.

  Module Type QuotationOfWProperties (M : WSets) (F : WPropertiesSig M) := QuotationOfWPropertiesOn M.E M F.

  Module Type QuotationOfOrdProperties (M : Sets) (F : OrdPropertiesSig M).
    Module qME := Nop <+ QuotationOfOrderedTypeFacts M.E F.ME.
    Module qML. (* OrderedTypeLists(M.E). *)
      MetaCoq Run (tmDeclareQuotationOfModule everything (Some export) "F.ML").
    End qML.
    Module qP := Nop <+ QuotationOfWProperties M F.P.
    Export (hints) qME qML qP.
    MetaCoq Run (tmDeclareQuotationOfModule (all_submodules_except [["ME"]; ["ML"]; ["P"]]%bs) (Some export) "F").
  End QuotationOfOrdProperties.
End MSets.
