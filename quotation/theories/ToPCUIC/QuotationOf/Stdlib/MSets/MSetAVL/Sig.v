From Stdlib.Structures Require Import Orders.
From Stdlib.MSets Require Import MSetAVL.
From MetaCoq.Utils Require Import MCMSets.
From MetaCoq.Quotation.ToPCUIC Require Import Init.

Module MSetAVL.
  Module Type QuotationOfMake (T : OrderedType) (M : MSetAVL.MakeSig T).
    MetaCoq Run (tmDeclareQuotationOfModule everything (Some export) "M").
  End QuotationOfMake.
End MSetAVL.
