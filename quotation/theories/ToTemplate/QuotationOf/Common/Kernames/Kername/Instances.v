From MetaCoq.Common Require Import Kernames.
From MetaCoq.Quotation.ToTemplate Require Import Init.
From MetaCoq.Quotation.ToTemplate.QuotationOf.Stdlib.Structures Require Import Orders.Sig OrdersAlt.Sig.
Import List.ListNotations.
Local Open Scope list_scope.

Module qKername <: QuotationOfOrderedType Kername.
  Module qOT <: QuotationOfOrderedTypeOrig Kername.OT.
    MetaCoq Run (tmMakeQuotationOfModule everything None "Kername.OT").
  End qOT.
  MetaCoq Run (tmMakeQuotationOfModuleWorkAroundCoqBug17303 (all_submodules_except [["OT"]]%bs) (*None*) "Kername").
End qKername.
