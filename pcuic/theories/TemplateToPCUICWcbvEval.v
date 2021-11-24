(* Distributed under the terms of the MIT license. *)
From Coq Require Import ssreflect.
From MetaCoq.Template Require Import config utils.
From MetaCoq.Template Require Ast TypingWf WfAst TermEquality.
Set Warnings "-notation-overridden".
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCumulativity
     PCUICLiftSubst PCUICEquality PCUICUnivSubst PCUICTyping TemplateToPCUIC
     PCUICWeakening PCUICSubstitution PCUICGeneration.
Set Warnings "+notation-overridden".

From Equations.Prop Require Import DepElim.
Implicit Types cf : checker_flags.

(* Source = Template, Target (unqualified) = Coq *)

Module SEq := Template.TermEquality.
Module ST := Template.Typing.
Module SL := Template.LiftSubst.

From MetaCoq.PCUIC Require Import TemplateToPCUIC.
From MetaCoq.Template Require Import TypingWf WcbvEval.
From MetaCoq.PCUIC Require Import PCUICWcbvEval.

Existing Class ST.wf.

Lemma trans_wcbvEval {cf} {Σ} {wfΣ : ST.wf Σ} T U :
  WfAst.wf Σ T ->
  WcbvEval.eval Σ [] T U ->
  let Σ' := trans_global (Ast.Env.empty_ext Σ) in
  PCUICWcbvEval.eval Σ' (trans Σ' T) (trans Σ' U).
Proof.
  induction 2.
Admitted.

Check (fun (cf : checker_flags) Σ (wfΣ : ST.wf Σ) (T : Ast.term) =>
 trans_wcbvEval T T).

