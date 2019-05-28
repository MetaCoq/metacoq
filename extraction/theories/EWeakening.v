Require Import Extract.

Lemma extract_extends (Σ Σ' : PCUICAst.global_context) (Γ Γ' : PCUICAst.context) (t T : PCUICAst.term) :
    wf Σ' ->
    (* wf_local Σ (Γ ,,, Γ') -> *)
    Σ;;; Γ |- t : T ->
    extract Σ Γ t = extract Σ' Γ t.
Admitted.

