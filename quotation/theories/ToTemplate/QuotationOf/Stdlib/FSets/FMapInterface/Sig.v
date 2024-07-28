From Coq.FSets Require Import FMapInterface.
From Coq.Structures Require Import Orders.
From MetaCoq.Quotation.ToTemplate Require Import Init.

Module Type QuotationOfWSfun (E : DecidableTypeOrig) (Import M : WSfun E).
  MetaCoq Run (tmDeclareQuotationOfModule everything (Some export) "M").
End QuotationOfWSfun.
