From MetaCoq.Common Require Import Kernames.
From MetaCoq.Quotation.ToTemplate Require Import Init.
From MetaCoq.Quotation.ToTemplate.QuotationOf.Utils Require Import MCMSets.Sig.
Import List.ListNotations.
Local Open Scope list_scope.

Module qKernameSetExtraOrdProp <: QuotationOfExtraOrdProperties KernameSet KernameSetOrdProp KernameSetExtraOrdProp.
  Module qP <: QuotationOfWExtraPropertiesOn KernameSet.E KernameSet KernameSetOrdProp.P KernameSetExtraOrdProp.P.
    MetaCoq Run (tmMakeQuotationOfModule everything None "KernameSetExtraOrdProp.P").
  End qP.
  MetaCoq Run (tmMakeQuotationOfModule (all_submodules_except [["P"]]%bs) None "KernameSetExtraOrdProp").
End qKernameSetExtraOrdProp.
