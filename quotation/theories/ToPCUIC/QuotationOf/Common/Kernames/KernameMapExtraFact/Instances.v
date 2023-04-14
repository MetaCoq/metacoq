From MetaCoq.Common Require Import Kernames.
From MetaCoq.Quotation.ToPCUIC Require Import Init.
From MetaCoq.Quotation.ToPCUIC.QuotationOf.Utils Require Import MCFSets.Sig.

Module qKernameMapExtraFact <: QuotationOfWFactsExtra_fun KernameMap.E KernameMap KernameMapFact.F KernameMapExtraFact.
  MetaCoq Run (tmMakeQuotationOfModule everything None "KernameMapExtraFact").
End qKernameMapExtraFact.
