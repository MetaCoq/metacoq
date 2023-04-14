From MetaCoq.Common Require Import Kernames.
From MetaCoq.Quotation.ToTemplate Require Import Init.
From MetaCoq.Quotation.ToTemplate.QuotationOf.Coq.FSets Require Import FMapFacts.Sig.

Module qKernameMapFact.
  Module qF <: QuotationOfWFacts_fun Kername.OT KernameMap KernameMapFact.F.
    MetaCoq Run (tmMakeQuotationOfModule everything None "KernameMapFact.F").
  End qF.
End qKernameMapFact.
