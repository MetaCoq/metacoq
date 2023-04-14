From MetaCoq.Common Require Import Kernames.
From MetaCoq.Quotation.ToTemplate Require Import Init.
From MetaCoq.Quotation.ToTemplate.QuotationOf.Coq.Structures Require Import Orders.Sig OrdersAlt.Sig OrdersFacts.Sig.
From MetaCoq.Quotation.ToTemplate.QuotationOf.Coq.FSets Require Import FMapAVL.Sig FMapList.Sig.
Import List.ListNotations.
Local Open Scope list_scope.

Module qKernameMap <: FMapAVL.QuotationOfMake Kername.OT KernameMap.
  Module qRaw.
    Module qProofs.
      Module qMX <: QuotationOfOrderedTypeOrigFacts Kername.OT KernameMap.Raw.Proofs.MX.
        MetaCoq Run (tmMakeQuotationOfModule everything None "KernameMap.Raw.Proofs.MX").
      End qMX.
      Module qPX <: QuotationOfKeyOrderedTypeOrig Kername.OT KernameMap.Raw.Proofs.PX.
        Module qMO <: QuotationOfOrderedTypeOrigFacts Kername.OT KernameMap.Raw.Proofs.PX.MO.
          MetaCoq Run (tmMakeQuotationOfModule everything None "KernameMap.Raw.Proofs.PX.MO").
        End qMO.
        MetaCoq Run (tmMakeQuotationOfModule (all_submodules_except [["MO"]]%bs) None "KernameMap.Raw.Proofs.PX").
      End qPX.
      Module qL <: FMapList.QuotationOfRaw Kername.OT KernameMap.Raw.Proofs.L.
        Module qMX <: QuotationOfOrderedTypeOrigFacts Kername.OT KernameMap.Raw.Proofs.L.MX.
          MetaCoq Run (tmMakeQuotationOfModule everything None "KernameMap.Raw.Proofs.L.MX").
        End qMX.
        Module qPX <: QuotationOfKeyOrderedTypeOrig Kername.OT KernameMap.Raw.Proofs.L.PX.
          Module qMO <: QuotationOfOrderedTypeOrigFacts Kername.OT KernameMap.Raw.Proofs.L.PX.MO.
            MetaCoq Run (tmMakeQuotationOfModule everything None "KernameMap.Raw.Proofs.L.PX.MO").
          End qMO.
          MetaCoq Run (tmMakeQuotationOfModule (all_submodules_except [["MO"]]%bs) None "KernameMap.Raw.Proofs.L.PX").
        End qPX.
        MetaCoq Run (tmMakeQuotationOfModule (all_submodules_except [["MX"]; ["PX"]]%bs) None "KernameMap.Raw.Proofs.L").
      End qL.
      MetaCoq Run (tmMakeQuotationOfModule (all_submodules_except [["MX"]; ["PX"]; ["L"]]%bs) None "KernameMap.Raw.Proofs").
    End qProofs.
    MetaCoq Run (tmMakeQuotationOfModule (all_submodules_except [["Proofs"]]%bs) None "KernameMap.Raw").
  End qRaw.
  MetaCoq Run (tmMakeQuotationOfModule (all_submodules_except [["Raw"]]%bs) None "KernameMap").
End qKernameMap.
