(* Distributed under the terms of the MIT license. *)
From Coq Require Import Program ssreflect ssrbool.
From MetaCoq.Template Require Import Transform bytestring config utils EtaExpand.
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

Program Definition erasure_pipeline {guard : abstract_guard_impl} (efl := EWellformed.all_env_flags) :
 Transform.t TemplateProgram.template_program EProgram.eprogram 
  Ast.term EAst.term
  TemplateProgram.eval_template_program
  (EProgram.eval_eprogram {| with_prop_case := false; with_guarded_fix := false |}) := 
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
  (* Rebuild the efficient lookup table *)
  rebuild_wf_env_transform (efl := ERemoveParams.switch_no_params EWellformed.all_env_flags) ▷
  (* Remove all cases / projections on propositional content *)
  optimize_prop_discr_optimization (efl := ERemoveParams.switch_no_params EWellformed.all_env_flags) (hastrel := eq_refl) (hastbox := eq_refl) ▷
  (* Rebuild the efficient lookup table *)
  rebuild_wf_env_transform (efl := EWellformed.all_env_flags) ▷
  (* Inline projections to cases *)
  inline_projections_optimization (fl := EWcbvEval.target_wcbv_flags) (hastrel := eq_refl) (hastbox := eq_refl).
(* At the end of erasure we get a well-formed program (well-scoped globally and localy), without 
   parameters in inductive declarations. The constructor applications are also expanded, and
   the evaluation relation does not need to consider guarded fixpoints or case analyses on propositional
   content. All fixpoint bodies start with a lambda as well. *)

Import EGlobalEnv EWellformed.

Lemma wf_global_switch_no_params (efl : EWellformed.EEnvFlags) Σ :
  wf_glob (efl := ERemoveParams.switch_no_params efl) Σ ->
  wf_glob (efl := efl) Σ.
Proof.
  induction 1; constructor; auto.
  destruct d; cbn in *. auto.
  move/andP: H0 => [] hasp. unfold wf_minductive.
  cbn in hasp. rewrite hasp. rewrite orb_true_r //.
Qed.

Lemma wf_eprogram_switch_no_params (p : EProgram.eprogram) : 
  EProgram.wf_eprogram (ERemoveParams.switch_no_params all_env_flags) p ->
  EProgram.wf_eprogram all_env_flags p.
Proof.
  destruct p as [Σ p].
  intros []; split; cbn in * => //.
  now eapply wf_global_switch_no_params.
Qed.

Next Obligation.
  destruct H. split => //. sq.
  now eapply ETransform.expanded_eprogram_env_expanded_eprogram_cstrs. 
Qed.
Next Obligation.
  split => //.
  now apply wf_eprogram_switch_no_params.
Qed.

Definition run_erase_program {guard : abstract_guard_impl} := run erasure_pipeline.

Program Definition erasure_pipeline_fast {guard : abstract_guard_impl} (efl := EWellformed.all_env_flags) := 
  template_to_pcuic_transform ▷
  pcuic_expand_lets_transform ▷
  erase_transform ▷ 
  guarded_to_unguarded_fix eq_refl ▷
  remove_params_fast_optimization _ ▷ 
  rebuild_wf_env_transform (efl := ERemoveParams.switch_no_params EWellformed.all_env_flags) ▷
  optimize_prop_discr_optimization (efl := ERemoveParams.switch_no_params EWellformed.all_env_flags) (hastrel := eq_refl) (hastbox := eq_refl).
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

Program Definition erase_and_print_template_program {cf : checker_flags} (p : Ast.Env.program)
  : string :=
  let p' := run_erase_program (eta_expand_program p) _ in
  time "Pretty printing" EPretty.print_program p'.
Next Obligation.
  assert (ht : ∥ TemplateProgram.wt_template_program p ∥) by eapply assume_that_we_only_erase_on_welltyped_programs.
  split; auto.  
  apply assume_that_we_only_erase_on_welltyped_programs.
  red.
  destruct ht as [[wfext [T ht]]].
  split; cbn. eapply EtaExpand.eta_expand_global_env_expanded. eapply wfext.
  eapply EtaExpand.expanded_env_irrel.
  epose proof (EtaExpand.eta_expand_expanded (Σ := Ast.Env.empty_ext p.1) [] [] p.2 T).
  forward H. apply wfext. specialize (H ht).
  forward H by constructor. cbn in H.
  destruct p as [ [] ]; cbn in *. exact H.
Qed.

Program Definition erase_fast_and_print_template_program {cf : checker_flags} (p : Ast.Env.program)
  : string :=
  let p' := run_erase_program_fast (eta_expand_program p) _ in
  time "pretty-printing" EPretty.print_program p'.
Next Obligation.
  assert (ht : ∥ TemplateProgram.wt_template_program p ∥) by eapply assume_that_we_only_erase_on_welltyped_programs.
  split; auto.  
  apply assume_that_we_only_erase_on_welltyped_programs.
  red.
  destruct ht as [[wfext [T ht]]].
  split; cbn. eapply EtaExpand.eta_expand_global_env_expanded. eapply wfext.
  eapply EtaExpand.expanded_env_irrel.
  epose proof (EtaExpand.eta_expand_expanded (Σ := Ast.Env.empty_ext p.1) [] [] p.2 T).
  forward H. apply wfext. specialize (H ht).
  forward H by constructor. cbn in H.
  destruct p as [ [] ]; cbn in *. exact H.
Qed.