From MetaCoq.Common Require Import config.
From MetaCoq.Template Require Import Ast Typing.
From MetaCoq.Template Require WfAst (*WfTyping*).
From MetaCoq.Quotation.ToTemplate.Template Require Ast Typing WfAst (*WfTyping*).

(* without typing derivations *)
Module Raw.
  (* These are probably the only quotation functions that users of this development will want to use; other files should be considered internal to the development of quotation *)
  Definition quote_term : Ast.term -> Ast.term := Ast.quote_term.
  Definition quote_typing {cf : checker_flags} {Σ Γ t T} : (Σ ;;; Γ |- t : T) -> Ast.term := Typing.quote_typing.
  Definition quote_wf_local {cf : checker_flags} {Σ Γ} : wf_local Σ Γ -> Ast.term := Typing.quote_wf_local.
  Definition quote_wf {cf Σ} : @wf cf Σ -> Ast.term := Typing.quote_wf.
  Definition quote_wf_ext {cf Σ} : @wf_ext cf Σ -> Ast.term := Typing.quote_wf_ext.
  Module WfAst.
    Definition quote_wf {Σ t} : @WfAst.wf Σ t -> Ast.term := WfAst.quote_wf.
  End WfAst.
  (* TODO: do we want anything from WfTyping? Is there anything else missing here? *)
End Raw.

(* eventually we'll have proofs that the above definitions are well-typed *)
