From MetaCoq.PCUIC Require Import PCUICAst Syntax.PCUICCases.
From MetaCoq.Quotation.ToPCUIC Require Import Init.
From MetaCoq.Quotation.ToPCUIC Require Import (hints) Coq.Init Coq.Lists(* Coq.Numbers Coq.Floats*).
From MetaCoq.Quotation.ToPCUIC.Utils Require Import (hints) (*utils*) All_Forall (* MCProd*).
From MetaCoq.Quotation.ToPCUIC.Common Require Import (hints) (*config*) BasicAst Kernames (*Universes Environment EnvironmentTyping Primitive Reflect*).
From MetaCoq.Quotation.ToPCUIC.PCUIC Require Import (hints) PCUICAst.
(*
From MetaCoq.Quotation.ToPCUIC.Utils Require Import (hints) utils All_Forall (* MCProd*).
From MetaCoq.Quotation.ToPCUIC.Common Require Import (hints) config BasicAst Universes Kernames Environment EnvironmentTyping Primitive Reflect.
(*From MetaCoq.Quotation.ToPCUIC.PCUIC Require Import (hints) PCUICAstUtils
  LiftSubst UnivSubst TermEquality WfAst.*)
From MetaCoq.Quotation.ToPCUIC.Common Require Import Environment EnvironmentTyping.
From MetaCoq.Quotation.ToPCUIC.QuotationOf.Common Require Import EnvironmentTyping.Sig.
From MetaCoq.Quotation.ToPCUIC.QuotationOf.PCUIC Require Import PCUICAst.Instances PCUICTyping.Instances.
 *)

#[export] Instance quote_wf_predicate_gen {mdecl idecl pparams pcontext} : ground_quotable (@wf_predicate_gen mdecl idecl pparams pcontext) := ltac:(cbv [wf_predicate_gen]; exact _).

#[export] Instance quote_wf_predicate {mdecl idecl p} : ground_quotable (@wf_predicate mdecl idecl p) := ltac:(cbv [wf_predicate]; exact _).

#[export] Instance quote_wf_branch_gen {cdecl bctx} : ground_quotable (@wf_branch_gen cdecl bctx) := ltac:(cbv [wf_branch_gen]; exact _).

#[export] Instance quote_wf_branch {cdecl b} : ground_quotable (@wf_branch cdecl b) := ltac:(cbv [wf_branch]; exact _).

#[export] Instance quote_wf_branches_gen {ctors brs} : ground_quotable (@wf_branches_gen ctors brs) := ltac:(cbv [wf_branches_gen]; exact _).

#[export] Instance quote_wf_branches {idecl brs} : ground_quotable (@wf_branches idecl brs) := ltac:(cbv [wf_branches]; exact _).
