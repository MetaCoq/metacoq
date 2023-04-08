From MetaCoq.Common Require Import config.
From MetaCoq.PCUIC Require Import PCUICAst PCUICTyping PCUICCumulativitySpec PCUICReduction.
From MetaCoq.Quotation.ToPCUIC.PCUIC Require PCUICAst PCUICTyping PCUICCumulativitySpec PCUICReduction.

(* without typing derivations *)
Module Raw.
  (* These are probably the only quotation functions that users of this development will want to use; other files should be considered internal to the development of quotation *)
  Definition quote_term : PCUICAst.term -> PCUICAst.term := PCUICAst.quote_term.
  Definition quote_typing {cf : checker_flags} {Σ Γ t T} : (Σ ;;; Γ |- t : T) -> PCUICAst.term := PCUICTyping.quote_typing.
  Definition quote_red {Σ Γ x y} : @red Σ Γ x y -> PCUICAst.term := PCUICReduction.quote_red.
  Definition quote_wf_local {cf : checker_flags} {Σ Γ} : wf_local Σ Γ -> PCUICAst.term := PCUICTyping.quote_wf_local.
  Definition quote_wf {cf Σ} : @wf cf Σ -> PCUICAst.term := PCUICTyping.quote_wf.
  Definition quote_wf_ext {cf Σ} : @wf_ext cf Σ -> PCUICAst.term := PCUICTyping.quote_wf_ext.
End Raw.

(* eventually we'll have proofs that the above definitions are well-typed *)
