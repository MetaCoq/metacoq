From MetaCoq.Common Require Import Universes.
From MetaCoq.Quotation.ToPCUIC Require Import Init.
From MetaCoq.Quotation.ToPCUIC.QuotationOf.Stdlib.Structures Require Import Orders.Sig OrdersAlt.Sig.
Import List.ListNotations.
Local Open Scope list_scope.

Module qLevel <: QuotationOfOrderedType Level.
  MetaCoq Run (tmMakeQuotationOfModuleWorkAroundCoqBug17303 everything (*None*) "Level").
End qLevel.
