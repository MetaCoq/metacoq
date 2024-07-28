From MetaCoq.Common Require Import Universes.
From MetaCoq.Quotation.ToTemplate Require Import Init.
From MetaCoq.Quotation.ToTemplate.QuotationOf.Stdlib.Structures Require Import Orders.Sig OrdersAlt.Sig.
Import List.ListNotations.
Local Open Scope list_scope.

Module qUnivConstraint <: QuotationOfOrderedType UnivConstraint.
  MetaCoq Run (tmMakeQuotationOfModuleWorkAroundCoqBug17303 everything (*None*) "UnivConstraint").
End qUnivConstraint.
