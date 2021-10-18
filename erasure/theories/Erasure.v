(* Distributed under the terms of the MIT license. *)
From Coq Require Import Program.
From MetaCoq.Template Require Import config utils uGraph Pretty Environment Typing.
Set Warnings "-notation-overridden".
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping
     TemplateToPCUIC TemplateToPCUICCorrectness.
Set Warnings "+notation-overridden".
From MetaCoq.SafeChecker Require Import PCUICErrors.
From MetaCoq.Erasure Require Import EAstUtils ErasureFunction EPretty.
From MetaCoq.Erasure Require ErasureFunction EOptimizePropDiscr.

Existing Instance extraction_checker_flags.

(* This is the total erasure function + the optimization that removes all 
  pattern-matches on propositions. *)

Program Definition erase_template_program (p : Ast.Env.program) 
  (wfΣ : ∥ Typing.wf_ext (Ast.Env.empty_ext p.1) ∥)
  (wt : ∥ ∑ T, Typing.typing (Ast.Env.empty_ext p.1) [] p.2 T ∥)
  : (EAst.global_context * EAst.term) :=
  let Σ := (trans_global (Ast.Env.empty_ext p.1)).1 in
  let t := ErasureFunction.erase (empty_ext Σ) _ nil (trans Σ p.2) _ in
  let Σ' := ErasureFunction.erase_global (term_global_deps t) Σ _ in
  (EOptimizePropDiscr.optimize_env Σ', EOptimizePropDiscr.optimize Σ' t).

Next Obligation.
  sq. 
  apply (template_to_pcuic_env_ext (Ast.Env.empty_ext p.1) wfΣ).
Qed.

Next Obligation.
  sq. destruct wt as [T Ht].
  set (Σ' := empty_ext (trans_global_decls _)).
  exists (trans Σ'.1 T).
  change (@nil (@BasicAst.context_decl term)) with (trans_local Σ'.1 []).
  apply (template_to_pcuic_typing (Ast.Env.empty_ext p.1));simpl. apply wfΣ.
  apply Ht.
Defined.
Next Obligation.
  sq. apply (template_to_pcuic_env_ext (Ast.Env.empty_ext p.1) wfΣ).
Defined.
Local Open Scope string_scope.

(** This uses the retyping-based erasure and assumes that the global environment and term 
  are welltyped (for speed). As such this should only be used for testing, or when we know that 
  the environment is wellformed and the term well-typed (e.g. when it comes directly from a 
  Coq definition). *)
Program Definition erase_and_print_template_program {cf : checker_flags} (p : Ast.Env.program)
  : string :=
  let (Σ', t) := erase_template_program p (todo "wf_env") (todo "welltyped") in
  Pretty.print_term (Ast.Env.empty_ext p.1) [] true p.2 ^ nl ^
  " erases to: " ^ nl ^ print_term Σ' [] true false t.
