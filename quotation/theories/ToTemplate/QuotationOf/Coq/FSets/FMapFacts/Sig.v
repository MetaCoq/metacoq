From Coq.FSets Require Import FMapFacts.
From Coq.Structures Require Import Orders.
From MetaCoq.Quotation.ToTemplate Require Import Init.

Module Export FSets.
  Module Type WFacts_funSig (E : DecidableTypeOrig) (M : WSfun E) := Nop <+ WFacts_fun E M.

  Module Type QuotationOfWFacts_fun (E : DecidableTypeOrig) (M : WSfun E) (F : WFacts_funSig E M).
    MetaCoq Run (tmDeclareQuotationOfModule everything (Some export) "F").
  End QuotationOfWFacts_fun.
End FSets.
