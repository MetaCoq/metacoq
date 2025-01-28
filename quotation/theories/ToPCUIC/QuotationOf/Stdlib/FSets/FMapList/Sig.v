From Stdlib.FSets Require Import FMapList.
From Stdlib.Structures Require Import Equalities OrdersAlt.
From MetaCoq.Utils Require Import MCFSets.
From MetaCoq.Quotation.ToPCUIC Require Import Init.
From MetaCoq.Quotation.ToPCUIC.QuotationOf.Stdlib.Structures Require Import OrdersAlt.Sig.
Import List.ListNotations.
Local Open Scope list_scope.

Module FMapList.
  Module Type QuotationOfRaw (T : OrderedTypeOrig) (M : FMapList.RawSig T).
    Module qMX := Nop <+ QuotationOfOrderedTypeOrigFacts T M.MX.
    Module qPX := Nop <+ QuotationOfKeyOrderedTypeOrig T M.PX.
    Export (hints) qMX qPX.
    MetaCoq Run (tmDeclareQuotationOfModule (all_submodules_except [["MX"]; ["PX"]]%bs) (Some export) "M").
  End QuotationOfRaw.
End FMapList.
