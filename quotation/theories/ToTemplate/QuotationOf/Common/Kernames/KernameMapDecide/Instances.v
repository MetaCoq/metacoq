From MetaCoq.Common Require Import Kernames.
From MetaCoq.Quotation.ToTemplate Require Import Init.
From MetaCoq.Quotation.ToTemplate.QuotationOf.Utils Require Import MCFSets.Sig.

Module qKernameMapDecide <: FMapAVL.QuotationOfDecide KernameMap.E KernameMap KernameMapDecide.
  MetaCoq Run (tmMakeQuotationOfModule everything None "KernameMapDecide").
End qKernameMapDecide.
