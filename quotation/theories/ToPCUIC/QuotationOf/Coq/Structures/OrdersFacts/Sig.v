From Coq.Structures Require Import Equalities Orders OrdersFacts.
From MetaCoq.Quotation.ToPCUIC Require Import Init.
From MetaCoq.Quotation.ToPCUIC.QuotationOf.Coq Require Export Structures.Orders.Sig.

Module Type QuotationOfCompareFacts (O : DecStrOrder) (F : CompareFacts O).
  MetaCoq Run (tmDeclareQuotationOfModule everything (Some export) "F").
End QuotationOfCompareFacts.

Module Type OrderedTypeFullFactsSig (O : OrderedTypeFull) := Nop <+ OrderedTypeFullFacts O.

Module Type QuotationOfOrderedTypeFullFacts (O : OrderedTypeFull) (F : OrderedTypeFullFactsSig O).
  MetaCoq Run (tmDeclareQuotationOfModule everything (Some export) "F").
End QuotationOfOrderedTypeFullFacts.

Module Type OrderedTypeFactsSig (O : Orders.OrderedType) := Nop <+ OrderedTypeFacts O.

Module Type QuotationOfOrderedTypeFacts (O : Orders.OrderedType) (F : OrderedTypeFactsSig O).
  MetaCoq Run (tmDeclareQuotationOfModule everything (Some export) "F").
End QuotationOfOrderedTypeFacts.

Module Type OrderedTypeRevSig (O : OrderedTypeFull) <: OrderedTypeFull := Nop <+ OrderedTypeRev O.
Module QuotationOfOrderedTypeRev (O : OrderedTypeFull) (S : OrderedTypeRevSig O) (Import qO : QuotationOfOrderedTypeFull O) <: QuotationOfOrderedTypeFull S.
  #[export] Instance qt : quotation_of S.t := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qeq : quotation_of S.eq := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qeq_equiv : quotation_of S.eq_equiv := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qeq_dec : quotation_of S.eq_dec := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qlt : quotation_of S.lt := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qle : quotation_of S.le := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qlt_strorder : quotation_of S.lt_strorder := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qlt_compat : quotation_of S.lt_compat := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qle_lteq : quotation_of S.le_lteq := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qcompare : quotation_of S.compare := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qcompare_spec : quotation_of S.compare_spec := ltac:(unfold_quotation_of (); exact _).
End QuotationOfOrderedTypeRev.

Module Type QuotationOfCompareBasedOrder (E : EqLtLe) (C : HasCmp E) (S : CompareBasedOrder E C).
  MetaCoq Run (tmDeclareQuotationOfModule everything (Some export) "S").
End QuotationOfCompareBasedOrder.

Module Type QuotationOfCompareBasedOrderFacts (E : EqLtLe) (C : HasCmp E) (O : CompareBasedOrder E C) (F : CompareBasedOrderFacts E C O).
  MetaCoq Run (tmDeclareQuotationOfModule everything (Some export) "F").
End QuotationOfCompareBasedOrderFacts.

Module Type QuotationOfBoolOrderFacts
  (E : EqLtLe)
  (C : HasCmp E)
  (F : HasBoolOrdFuns E)
  (O : CompareBasedOrder E C)
  (S : BoolOrdSpecs E F)
  (Facts : BoolOrderFacts E C F O S).
  MetaCoq Run (tmDeclareQuotationOfModule everything (Some export) "Facts").
End QuotationOfBoolOrderFacts.
