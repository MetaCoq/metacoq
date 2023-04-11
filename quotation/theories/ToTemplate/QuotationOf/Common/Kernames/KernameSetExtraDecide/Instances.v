From MetaCoq.Common Require Import Kernames.
From MetaCoq.Quotation.ToTemplate Require Import Init.
From MetaCoq.Quotation.ToTemplate.QuotationOf.Utils Require Import MCMSets.Sig.

Module qKernameSetExtraDecide <: MSetAVL.QuotationOfDecide KernameSet.E KernameSet KernameSetExtraDecide.
  MetaCoq Run (tmMakeQuotationOfModule everything None "KernameSetExtraDecide").
End qKernameSetExtraDecide.
