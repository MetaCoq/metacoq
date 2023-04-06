From Coq.MSets Require Import MSetInterface MSetDecide.
From MetaCoq.Quotation.ToTemplate Require Import Init.

Module Export MSets.
  Module Type WDecideOnSig (E : DecidableType) (M : WSetsOn E) := Nop <+ WDecideOn E M.
  Module Type WDecideSig (M : WSets) := Nop <+ WDecide M.
  Module Type DecideSig (M : WSets) := Nop <+ Decide M.

  Module Type QuotationOfWDecideOn (E : DecidableType) (M : WSetsOn E) (F : WDecideOnSig E M).
    MetaCoq Run (tmDeclareQuotationOfModule everything (Some export) "F").
  End QuotationOfWDecideOn.

  Module Type QuotationOfWDecide (M : WSets) (F : WDecideSig M) := QuotationOfWDecideOn M.E M F.
End MSets.
