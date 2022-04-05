(* Distributed under the terms of the MIT license. *)
From Coq Require Import Program ssreflect ssrbool.
From MetaCoq.Template Require Import Transform bytestring config utils.
From MetaCoq.PCUIC Require PCUICAst PCUICAstUtils PCUICProgram.
From MetaCoq.Erasure Require EAstUtils ErasureFunction ErasureCorrectness EPretty Extract.
From MetaCoq.Erasure Require Import ETransform.

Import PCUICProgram.
Import TemplateProgram (template_eta_expand).
Import PCUICTransform (template_to_pcuic_transform, pcuic_expand_lets_transform).

Import bytestring.
Local Open Scope bs.
Local Open Scope string_scope2.

(* This is the total erasure function +
  let-expansion of constructor arguments and case branches +
  shrinking of the global environment dependencies +
  the optimization that removes all pattern-matches on propositions. *)

Import Transform.

Obligation Tactic := program_simpl.

#[local] Existing Instance extraction_checker_flags.

Import EWcbvEval.

Program Definition erasure_pipeline (efl := EWellformed.all_env_flags) :
 Transform.t TemplateProgram.template_program EProgram.eprogram 
  Ast.term EAst.term
  TemplateProgram.eval_template_program
  (EProgram.eval_eprogram {| with_prop_case := false; with_guarded_fix := false |}) := 
  (* Eta expansion of constructors and fixpoints *)
  template_eta_expand ▷
  (* Casts are removed, application is binary, case annotations are inferred from the global environment *)
  template_to_pcuic_transform ▷
  (* Branches of cases are expanded to bind only variables, constructor types are expanded accordingly *)
  pcuic_expand_lets_transform ▷
  (* Erasure of proofs terms in Prop and types *)
  erase_transform ▷
  (* Simulation of the guarded fixpoint rules with a single unguarded one: 
    the only "stuck" fixpoints remaining are unapplied. 
    This translation is a noop on terms and environments.  *)
  guarded_to_unguarded_fix eq_refl ▷
  (* Remove all constructor parameters *)
  remove_params_optimization ▷ 
  (* Remove all cases / projections on propositional content *)
  optimize_prop_discr_optimization (efl := ERemoveParams.switch_no_params EWellformed.all_env_flags) (hastrel := eq_refl) (hastbox := eq_refl).
(* At the end of erasure we get a well-formed program (well-scoped globally and localy), without 
   parameters in inductive declarations. The constructor applications are also expanded, and
   the evaluation relation does not need to consider guarded fixpoints or case analyses on propositional
   content. *)

Next Obligation.
  destruct H. split => //. sq.
  now eapply EProgram.expanded_eprogram_env_expanded_eprogram_cstrs. 
Qed.

Definition run_erase_program := run erasure_pipeline.

Program Definition erasure_pipeline_fast (efl := EWellformed.all_env_flags) := 
  template_eta_expand ▷
  template_to_pcuic_transform ▷
  pcuic_expand_lets_transform ▷
  erase_transform ▷ 
  guarded_to_unguarded_fix eq_refl ▷
  remove_params_fast_optimization _ ▷ 
  optimize_prop_discr_optimization (efl := ERemoveParams.switch_no_params EWellformed.all_env_flags) (hastrel := eq_refl) (hastbox := eq_refl).
Next Obligation.
  destruct H; split => //. now eapply EProgram.expanded_eprogram_env_expanded_eprogram_cstrs. 
Qed.

Definition run_erase_program_fast := run erasure_pipeline_fast.

Local Open Scope string_scope.

(** This uses the retyping-based erasure and assumes that the global environment and term 
  are welltyped (for speed). As such this should only be used for testing, or when we know that 
  the environment is wellformed and the term well-typed (e.g. when it comes directly from a 
  Coq definition). *)
Definition erase_and_print_template_program {cf : checker_flags} (p : Ast.Env.program)
  : string :=
  let p' := run_erase_program p (sq (todo "assuming quoted environment and term are well-typed")) in
  time "Pretty printing" EPretty.print_program p'.

Program Definition erase_fast_and_print_template_program {cf : checker_flags} (p : Ast.Env.program)
  : string :=
  let p' := run_erase_program_fast p (sq (todo "wf_env and welltyped term")) in
  time "pretty-printing" EPretty.print_program p'.
