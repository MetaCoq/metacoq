(* Distributed under the terms of the MIT license. *)
From Coq Require Import Program ssreflect ssrbool.
From MetaCoq.Template Require Import Transform bytestring config utils EtaExpand TemplateProgram.
From MetaCoq.PCUIC Require PCUICAst PCUICAstUtils PCUICProgram.
From MetaCoq.SafeChecker Require Import PCUICErrors PCUICWfEnvImpl.
From MetaCoq.Erasure Require EAstUtils ErasureFunction ErasureCorrectness EPretty Extract.
From MetaCoq.Erasure Require Import ETransform.

Import PCUICProgram.
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

Axiom assume_welltyped_template_program_expansion : 
  forall p (wtp : ∥ wt_template_program_env p ∥),
  let p' := EtaExpand.eta_expand_program p in
  ∥ wt_template_program p' ∥ /\ EtaExpand.expanded_program p'.

Axiom assume_preservation_template_program_env_expansion : 
  forall p (wtp : ∥ wt_template_program_env p ∥) v,
  eval_template_program_env p v ->
  ∥ eval_template_program (EtaExpand.eta_expand_program p) (EtaExpand.eta_expand p.1 [] v) ∥.

Program Definition eta_expand : Transform.t template_program_env template_program Ast.term Ast.term 
  eval_template_program_env eval_template_program :=
  {| name := "eta expand cstrs and fixpoints";
      pre := fun p => ∥ wt_template_program_env p ∥ ;
      transform p _ := EtaExpand.eta_expand_program p ;
      post := fun p => ∥ wt_template_program p ∥ /\ EtaExpand.expanded_program p;
      obseq p p' v v' := v' = EtaExpand.eta_expand p.1 [] v |}.
Next Obligation.
  destruct p. now apply assume_welltyped_template_program_expansion.
Qed.
Next Obligation.
  red. intros p v [wt] ev. 
  apply assume_preservation_template_program_env_expansion in ev as [ev']; eauto.
Qed.

Program Definition erasure_pipeline_gen {guard : abstract_guard_impl} (efl := EWellformed.all_env_flags) :
 Transform.t TemplateProgram.template_program EProgram.eprogram 
  Ast.term EAst.term
  TemplateProgram.eval_template_program
  (EProgram.eval_eprogram {| with_prop_case := false; with_guarded_fix := false; with_constructor_as_block := true |}) := 
  (* Build an efficient lookup map for the following eta-expansion phase *)
  build_template_program_env ▷
  (* Eta-expand constructors and fixpoint *)
  eta_expand ▷
  (* Casts are removed, application is binary, case annotations are inferred from the global environment *)
  template_to_pcuic_transform ▷
  (* Branches of cases are expanded to bind only variables, constructor types are expanded accordingly *)
  pcuic_expand_lets_transform ▷
  (* Erasure of proofs terms in Prop and types *)
  erase_transform ▷
  (* Simulation of the guarded fixpoint rules with a single unguarded one: 
    the only "stuck" fixpoints remaining are unapplied. 
    This translation is a noop on terms and environments.  *)
  guarded_to_unguarded_fix (wcon := eq_refl) eq_refl ▷
  (* Remove all constructor parameters *)
  remove_params_optimization (wcon := eq_refl) ▷ 
  (* Rebuild the efficient lookup table *)
  rebuild_wf_env_transform (efl := ERemoveParams.switch_no_params EWellformed.all_env_flags) true ▷
  (* Remove all cases / projections on propositional content *)
  optimize_prop_discr_optimization (efl := ERemoveParams.switch_no_params EWellformed.all_env_flags) (wcon := eq_refl) (hastrel := eq_refl) (hastbox := eq_refl) ▷
  (* Rebuild the efficient lookup table *)
  rebuild_wf_env_transform (efl := ERemoveParams.switch_no_params EWellformed.all_env_flags) true  ▷
  (* Inline projections to cases *)
  inline_projections_optimization (fl := EWcbvEval.target_wcbv_flags) (wcon := eq_refl) (hastrel := eq_refl) (hastbox := eq_refl) ▷
  let efl := EInlineProjections.disable_projections_env_flag (ERemoveParams.switch_no_params EWellformed.all_env_flags) in
  (* Rebuild the efficient lookup table *)
  rebuild_wf_env_transform (efl :=  efl) true ▷
  (* First-order constructor representation *)
  constructors_as_blocks_transformation efl (has_app := eq_refl) (has_pars := eq_refl) (has_cstrblocks := eq_refl).

(* At the end of erasure we get a well-formed program (well-scoped globally and localy), without 
   parameters in inductive declarations. The constructor applications are also transformed to a first-order
   "block"  application, of the right length, and the evaluation relation does not need to consider guarded 
   fixpoints or case analyses on propositional content. All fixpoint bodies start with a lambda as well.
   Finally, projections are inlined to cases, so no `tProj` remains. *)

Import EGlobalEnv EWellformed.

Next Obligation.
  destruct H. split => //. sq.
  now eapply ETransform.expanded_eprogram_env_expanded_eprogram_cstrs. 
Qed.

(* This includes an additional transformation from cofixpoints to fixpoints, thunking coinductive values *)

Program Definition erasure_pipeline {guard : abstract_guard_impl} (efl := EWellformed.all_env_flags) :
 Transform.t TemplateProgram.template_program EProgram.eprogram 
  Ast.term EAst.term
  TemplateProgram.eval_template_program
  (EProgram.eval_eprogram {| with_prop_case := false; with_guarded_fix := false; with_constructor_as_block := true |}) := 
  erasure_pipeline_gen ▷
  let efl := EInlineProjections.disable_projections_env_flag (ERemoveParams.switch_no_params EWellformed.all_env_flags) in
  (* Rebuild the efficient lookup table *)
  rebuild_wf_env_transform (fl := EConstructorsAsBlocks.block_wcbv_flags) (efl := EConstructorsAsBlocks.switch_cstr_as_blocks efl) false ▷
  (* Represent coinductive values as thunked inductive values *)
  coinductive_to_inductive_transformation (EConstructorsAsBlocks.switch_cstr_as_blocks efl) (has_box := eq_refl) (has_trel := eq_refl) (has_pars := eq_refl) (has_cstrblocks := eq_refl).

Definition run_erase_program {guard : abstract_guard_impl} := run erasure_pipeline.

Program Definition erasure_pipeline_fast {guard : abstract_guard_impl} (efl := EWellformed.all_env_flags) := 
  build_template_program_env ▷
  eta_expand ▷
  template_to_pcuic_transform ▷
  pcuic_expand_lets_transform ▷
  erase_transform ▷ 
  guarded_to_unguarded_fix (wcon := eq_refl) eq_refl ▷
  remove_params_fast_optimization (wcon := eq_refl)  _ ▷ 
  rebuild_wf_env_transform (efl := ERemoveParams.switch_no_params EWellformed.all_env_flags) true ▷
  optimize_prop_discr_optimization (efl := ERemoveParams.switch_no_params EWellformed.all_env_flags) (wcon := eq_refl) (hastrel := eq_refl) (hastbox := eq_refl) ▷
  rebuild_wf_env_transform (efl := ERemoveParams.switch_no_params EWellformed.all_env_flags) true ▷
  inline_projections_optimization (fl := EWcbvEval.target_wcbv_flags) (wcon := eq_refl) (hastrel := eq_refl) (hastbox := eq_refl) ▷
  let efl := EInlineProjections.disable_projections_env_flag (ERemoveParams.switch_no_params EWellformed.all_env_flags) in
  rebuild_wf_env_transform (efl :=  efl) true ▷
  constructors_as_blocks_transformation efl (has_app := eq_refl) (has_pars := eq_refl) (has_cstrblocks := eq_refl).
Next Obligation.
  destruct H; split => //. now eapply ETransform.expanded_eprogram_env_expanded_eprogram_cstrs. 
Qed.

Definition run_erase_program_fast {guard : abstract_guard_impl} := run erasure_pipeline_fast.

Local Open Scope string_scope.

Axiom fake_guard_impl_properties : 
forall (fix_cofix: PCUICTyping.FixCoFix)
       (Σ: PCUICAst.PCUICEnvironment.global_env_ext)
       (Γ: PCUICAst.PCUICEnvironment.context)
       (mfix: BasicAst.mfixpoint PCUICAst.term),
PCUICTyping.guard fix_cofix Σ Γ mfix <-> fake_guard_impl fix_cofix Σ Γ mfix.


Global Program Instance fake_guard_impl : abstract_guard_impl :=
{| guard_impl := fake_guard_impl |}.
Next Obligation. apply fake_guard_impl_properties. Qed.

(** This uses the retyping-based erasure and assumes that the global environment and term 
  are welltyped (for speed). As such this should only be used for testing, or when we know that 
  the environment is wellformed and the term well-typed (e.g. when it comes directly from a 
  Coq definition). *)


Axiom assume_that_we_only_erase_on_welltyped_programs : forall {cf : checker_flags},
  forall (p : Ast.Env.program), squash (TemplateProgram.wt_template_program p).

Program Definition erase_and_print_template_program (p : Ast.Env.program)
  : string :=
  let p' := run_erase_program p _ in
  time "Pretty printing" EPretty.print_program p'.
Next Obligation.
  now eapply assume_that_we_only_erase_on_welltyped_programs.
Qed.

Program Definition erase_fast_and_print_template_program (p : Ast.Env.program)
  : string :=
  let p' := run_erase_program_fast p _ in
  time "pretty-printing" EPretty.print_program p'.
Next Obligation.
  now eapply assume_that_we_only_erase_on_welltyped_programs.
Qed.