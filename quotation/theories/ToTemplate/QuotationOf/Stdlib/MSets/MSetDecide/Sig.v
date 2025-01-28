From Stdlib.MSets Require Import MSetInterface MSetDecide.
From MetaCoq.Utils Require Import MCMSets.
From MetaCoq.Quotation.ToTemplate Require Import Init.

Module Export MSets.
  Module Type QuotationOfWDecideOn (E : DecidableType) (M : WSetsOn E) (F : WDecideOnSig E M).
    MetaCoq Run (tmDeclareQuotationOfModule everything (Some export) "F").
  End QuotationOfWDecideOn.

  Module Type QuotationOfWDecide (M : WSets) (F : WDecideSig M) := QuotationOfWDecideOn M.E M F.
End MSets.
