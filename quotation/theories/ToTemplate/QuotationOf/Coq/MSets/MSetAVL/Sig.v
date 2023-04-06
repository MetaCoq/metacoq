From Coq.Structures Require Import Orders.
From Coq.MSets Require Import MSetAVL.
From MetaCoq.Quotation.ToTemplate Require Import Init.

Module MSetAVL.
  Module Type MakeSig (T : OrderedType) := Nop <+ MSetAVL.Make T.

  Module Type QuotationOfMake (T : OrderedType) (M : MakeSig T).
    MetaCoq Run (tmDeclareQuotationOfModule everything (Some export) "M").
  End QuotationOfMake.
End MSetAVL.
