From MetaCoq.Common Require Import Universes.
From MetaCoq.Quotation.ToTemplate Require Import Init.
From MetaCoq.Quotation.ToTemplate.QuotationOf.Utils Require Import MCMSets.Sig.

Module qConstraintSetExtraDecide <: MSetAVL.QuotationOfDecide ConstraintSet.E ConstraintSet ConstraintSetExtraDecide.
  MetaCoq Run (tmMakeQuotationOfModule everything None "ConstraintSetExtraDecide").
End qConstraintSetExtraDecide.
