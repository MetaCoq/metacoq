From Coq.FSets Require Import FMapFacts.
From Coq.Structures Require Import Orders.
From MetaCoq.Utils Require Import MCFSets.
From MetaCoq.Quotation.ToPCUIC Require Import Init.

Module Export FSets.
  Module Type QuotationOfWFacts_fun (E : DecidableTypeOrig) (M : WSfun E) (F : WFacts_funSig E M).
    MetaCoq Run (tmDeclareQuotationOfModule everything (Some export) "F").
  End QuotationOfWFacts_fun.
End FSets.
