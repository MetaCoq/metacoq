From Coq.MSets Require Import MSetFacts.
From MetaCoq.Quotation.ToTemplate Require Import Init.

Module Export MSets.
  Module Type WFactsOnSig (E : DecidableType) (M : WSetsOn E) := Nop <+ WFactsOn E M.
  Module Type WFactsSig (M : WSets) := Nop <+ WFacts M.
  Module Type FactsSig (M : WSets) := Nop <+ Facts M.

  Module Type QuotationOfWFactsOn (E : DecidableType) (M : WSetsOn E) (F : WFactsOnSig E M).
    MetaCoq Run (tmDeclareQuotationOfModule everything (Some export) "F").
  End QuotationOfWFactsOn.

  Module Type QuotationOfWFacts (M : WSets) (F : WFactsSig M) := QuotationOfWFactsOn M.E M F.
End MSets.
