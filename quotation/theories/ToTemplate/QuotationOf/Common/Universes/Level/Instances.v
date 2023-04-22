From MetaCoq.Common Require Import Universes.
From MetaCoq.Quotation.ToTemplate Require Import Init.
From MetaCoq.Quotation.ToTemplate.QuotationOf.Coq.Structures Require Import Orders.Sig OrdersAlt.Sig.
Import List.ListNotations.
Local Open Scope list_scope.

Module qLevel <: QuotationOfOrderedType Level.
  MetaCoq Run (tmMakeQuotationOfModuleWorkAroundCoqBug17303 everything (*None*) "Level").
End qLevel.
