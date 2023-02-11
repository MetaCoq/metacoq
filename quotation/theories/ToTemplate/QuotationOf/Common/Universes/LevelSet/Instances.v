From MetaCoq.Common Require Import Universes.
From MetaCoq.Quotation.ToTemplate Require Import Init.
From MetaCoq.Quotation.ToTemplate.QuotationOf.Coq.MSets Require Import MSetAVL.Sig.

Module qLevelSet <: MSetAVL.QuotationOfMake Level LevelSet.
  MetaCoq Run (tmMakeQuotationOfModule everything None "LevelSet").
End qLevelSet.
