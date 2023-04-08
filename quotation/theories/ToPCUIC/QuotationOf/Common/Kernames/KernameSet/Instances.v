From MetaCoq.Common Require Import Kernames.
From MetaCoq.Quotation.ToPCUIC Require Import Init.
From MetaCoq.Quotation.ToPCUIC.QuotationOf.Coq.MSets Require Import MSetAVL.Sig.

Module qKernameSet <: MSetAVL.QuotationOfMake Kername KernameSet.
  MetaCoq Run (tmMakeQuotationOfModule everything None "KernameSet").
End qKernameSet.
