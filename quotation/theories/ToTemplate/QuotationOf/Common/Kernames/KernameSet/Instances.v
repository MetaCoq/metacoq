From MetaCoq.Common Require Import Kernames.
From MetaCoq.Quotation.ToTemplate Require Import Init.
From MetaCoq.Quotation.ToTemplate.QuotationOf.Stdlib.MSets Require Import MSetAVL.Sig.

Module qKernameSet <: MSetAVL.QuotationOfMake Kername KernameSet.
  MetaCoq Run (tmMakeQuotationOfModule everything None "KernameSet").
End qKernameSet.
