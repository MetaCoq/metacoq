From MetaCoq.Common Require Import Kernames.
From MetaCoq.Quotation.ToPCUIC Require Import Init.
From MetaCoq.Quotation.ToPCUIC.QuotationOf.Coq.FSets Require Import FMapFacts.Sig.

Module qKernameMapFact.
  Module qF <: QuotationOfWFacts_fun Kername.OT KernameMap KernameMapFact.F.
    MetaCoq Run (tmMakeQuotationOfModule everything None "KernameMapFact.F").
  End qF.
End qKernameMapFact.
