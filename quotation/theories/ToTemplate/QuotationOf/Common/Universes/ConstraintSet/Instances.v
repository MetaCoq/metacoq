From MetaCoq.Common Require Import Universes.
From MetaCoq.Quotation.ToTemplate Require Import Init.
From MetaCoq.Quotation.ToTemplate.QuotationOf.Stdlib.MSets Require Import MSetAVL.Sig.

Module qConstraintSet <: MSetAVL.QuotationOfMake UnivConstraint ConstraintSet.
  MetaCoq Run (tmMakeQuotationOfModule everything None "ConstraintSet").
End qConstraintSet.
