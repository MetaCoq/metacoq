From Stdlib.MSets Require Import MSetFacts.
From MetaCoq.Utils Require Import MCMSets.
From MetaCoq.Quotation.ToPCUIC Require Import Init.

Module Export MSets.
  Module Type QuotationOfWFactsOn (E : DecidableType) (M : WSetsOn E) (F : WFactsOnSig E M).
    MetaCoq Run (tmDeclareQuotationOfModule everything (Some export) "F").
  End QuotationOfWFactsOn.

  Module Type QuotationOfWFacts (M : WSets) (F : WFactsSig M) := QuotationOfWFactsOn M.E M F.
End MSets.
