From Coq.Structures Require Import Orders OrdersAlt.
From Coq.FSets Require Import FMapInterface.
From MetaCoq.Utils Require Import MCFSets.
From MetaCoq.Quotation.ToPCUIC Require Import Init.

Module Type QuotationOfWFactsExtra_fun (E : DecidableTypeOrig) (W : WSfun E) (WFacts : WFacts_funSig E W) (WFactsExtra : WFactsExtra_funSig E W WFacts).
  MetaCoq Run (tmDeclareQuotationOfModule everything (Some export) "WFactsExtra").
End QuotationOfWFactsExtra_fun.

Module FMapAVL.
  Module Type QuotationOfDecide (T : OrderedTypeOrig) (M : FMapAVL.MakeSig T) (Dec : FMapAVL.DecideSig T M).
    MetaCoq Run (tmDeclareQuotationOfModule everything (Some export) "Dec").
  End QuotationOfDecide.
End FMapAVL.
