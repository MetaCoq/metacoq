From Coq.Structures Require Import Equalities Orders.
From Coq.MSets Require Import MSetList.
From MetaCoq.Utils Require Import MCMSets.
From MetaCoq.Quotation.ToTemplate Require Import Init.
From MetaCoq.Quotation.ToTemplate.QuotationOf.Coq.MSets Require Import MSetInterface.Sig.

Module Type QuotationOfOrderedTypeWithLeibniz (O : OrderedTypeWithLeibniz).
  MetaCoq Run (tmDeclareQuotationOfModule everything (Some export) "O").
End QuotationOfOrderedTypeWithLeibniz.

Module Type QuotationOfSWithLeibniz (S : SWithLeibniz).
  Include QuotationOfSetsOn S.E S.
  #[export] Declare Instance qeq_leibniz : quotation_of S.eq_leibniz.
End QuotationOfSWithLeibniz.

Module MSetList.
  Module Type QuotationOfMake (T : OrderedType) (M : MSetList.MakeSig T).
    MetaCoq Run (tmDeclareQuotationOfModule everything (Some export) "M").
  End QuotationOfMake.

  Module Type QuotationOfMakeWithLeibniz (T : OrderedTypeWithLeibniz) (M : MSetList.MakeWithLeibnizSig T).
    Include QuotationOfMake T M.
    #[export] Declare Instance qeq_leibniz_list : quotation_of M.eq_leibniz_list.
    #[export] Declare Instance qeq_leibniz : quotation_of M.eq_leibniz.
  End QuotationOfMakeWithLeibniz.
End MSetList.
