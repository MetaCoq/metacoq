From Stdlib.MSets Require Import MSetInterface.
From MetaCoq.Utils Require Import MCMSets.
From MetaCoq.Quotation.ToPCUIC Require Import Init.
Import List.ListNotations.
Local Open Scope list_scope.

Module Type QuotationOfWExtraPropertiesOn (E : DecidableType) (W : WSetsOn E) (WProperties : WPropertiesOnSig E W) (WExtraProperties : WExtraPropertiesOnSig E W WProperties).
  MetaCoq Run (tmDeclareQuotationOfModule everything (Some export) "WExtraProperties").
End QuotationOfWExtraPropertiesOn.

Module Type QuotationOfExtraOrdProperties (M : Sets) (MOrdProperties : OrdPropertiesSig M) (MExtraOrdProperties : ExtraOrdPropertiesSig M MOrdProperties).
  Module qP := Nop <+ QuotationOfWExtraPropertiesOn M.E M MOrdProperties.P MExtraOrdProperties.P.
  Export (hints) qP.
  MetaCoq Run (tmDeclareQuotationOfModule (all_submodules_except [["P"]%bs]) (Some export) "MExtraOrdProperties").
End QuotationOfExtraOrdProperties.

Module MSetAVL.
  Module Type QuotationOfDecide (T : OrderedType) (M : MSetAVL.MakeSig T) (Dec : MSetAVL.DecideSig T M).
    MetaCoq Run (tmDeclareQuotationOfModule everything (Some export) "Dec").
  End QuotationOfDecide.

  Module Type QuotationOfLtIrrel (T : OrderedType) (M : MSetAVL.MakeSig T) (TIrrel : IsLtIrrel T) (MIrrel : MSetAVL.LtIrrelSig T M TIrrel).
    MetaCoq Run (tmDeclareQuotationOfModule everything (Some export) "MIrrel").
  End QuotationOfLtIrrel.

  Module Type QuotationOfDecideWithLeibniz (T : OrderedType) (M : MSetAVL.MakeSig T) (L : IsLeibniz T) (I : IsLtIrrel T) (D : MSetAVL.DecideSig T M) (MI : MSetAVL.LtIrrelSig T M I) (DL : MSetAVL.DecideWithLeibnizSig T M L I D MI).
    MetaCoq Run (tmDeclareQuotationOfModule everything (Some export) "DL").
  End QuotationOfDecideWithLeibniz.
End MSetAVL.
