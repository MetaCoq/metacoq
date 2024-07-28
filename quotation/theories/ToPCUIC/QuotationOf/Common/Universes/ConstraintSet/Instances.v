From MetaCoq.Common Require Import Universes.
From MetaCoq.Quotation.ToPCUIC Require Import Init.
From MetaCoq.Quotation.ToPCUIC.QuotationOf.Stdlib.MSets Require Import MSetAVL.Sig.

Module qConstraintSet <: MSetAVL.QuotationOfMake UnivConstraint ConstraintSet.
  MetaCoq Run (tmMakeQuotationOfModule everything None "ConstraintSet").
End qConstraintSet.
