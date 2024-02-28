(* Distributed under the terms of the MIT license. *)
From Coq Require Import Program ssreflect ssrbool.
From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import Transform config.
From MetaCoq.Template Require Import EtaExpand TemplateProgram.
From MetaCoq.PCUIC Require PCUICAst PCUICAstUtils PCUICProgram.
From MetaCoq.SafeChecker Require Import PCUICErrors PCUICWfEnvImpl.
From MetaCoq.Erasure Require EAstUtils ErasureFunction ErasureCorrectness EPretty Extract.
From MetaCoq.Erasure Require Import EProgram EInlining EBeta.
From MetaCoq.ErasurePlugin Require Import ETransform.

Import PCUICProgram.
Import PCUICTransform (template_to_pcuic_transform, pcuic_expand_lets_transform).

Import bytestring.
Local Open Scope bs.
Local Open Scope string_scope2.

(* This is the total erasure function +
  let-expansion of constructor arguments and case branches +
  shrinking of the global environment dependencies +
  the optimization that removes all pattern-matches on propositions. *)

Import Common.Transform.Transform.

#[local] Existing Instance extraction_checker_flags.
#[local] Existing Instance PCUICSN.extraction_normalizing.

Import EWcbvEval.

Local Obligation Tactic := program_simpl.

Record erasure_configuration := {
  enable_unsafe : bool;
  enable_typed_erasure : bool;
  enable_fast_remove_params : bool;
  dearging_config : dearging_config;
  inductives_mapping : EReorderCstrs.inductives_mapping;
  inlining : KernameSet.t
  }.

Definition default_dearging_config :=
  {| overridden_masks := fun _ => None;
      do_trim_const_masks := true;
      do_trim_ctor_masks := false |}.

(* This runs the cofix -> fix translation which is not entirely verified yet *)
Definition default_erasure_config :=
  {| enable_unsafe := true;
     dearging_config := default_dearging_config;
     enable_typed_erasure := true;
     enable_fast_remove_params := true;
     inductives_mapping := [];
     inlining := KernameSet.empty |}.

(* This runs only the verified phases without the typed erasure and "fast" remove params *)
Definition safe_erasure_config :=
  {| enable_unsafe := false;
     enable_typed_erasure := false;
     enable_fast_remove_params := false;
     dearging_config := default_dearging_config;
     inductives_mapping := [];
     inlining := KernameSet.empty |}.

Axiom assume_welltyped_template_program_expansion :
  forall p (wtp : ∥ wt_template_program_env p ∥),
  let p' := EtaExpand.eta_expand_program p in
  ∥ wt_template_program p' ∥ /\ EtaExpand.expanded_program p'.

Axiom assume_preservation_template_program_env_expansion :
  forall p (wtp : ∥ wt_template_program_env p ∥) v,
  eval_template_program_env p v ->
  ∥ eval_template_program (EtaExpand.eta_expand_program p) (EtaExpand.eta_expand p.1 [] v) ∥.

(** We kludge the normalization assumptions by parameterizing over a continuation of "what will be done to the program later" as well as what properties we'll need of it *)

Program Definition eta_expand K : Transform.t _ _ Ast.term Ast.term _ _
  eval_template_program_env eval_template_program :=
  {| name := "eta expand cstrs and fixpoints";
     pre := fun p => ∥ wt_template_program_env p ∥ /\ K (eta_expand_global_env p.1) ;
     transform p _ := EtaExpand.eta_expand_program p ;
     post := fun p => ∥ wt_template_program p ∥ /\ EtaExpand.expanded_program p /\ K p.1;
     obseq p hp p' v v' := v' = EtaExpand.eta_expand p.1 [] v |}.
Next Obligation.
  let p := match goal with H : program _ _ |- _ => H end in
  destruct p. split; [|split]; auto; now apply assume_welltyped_template_program_expansion.
Qed.
Next Obligation.
  red. intros p v [wt] ev.
  apply assume_preservation_template_program_env_expansion in ev as [ev']; eauto.
Qed.

Definition final_wcbv_flags := {|
  with_prop_case := false;
  with_guarded_fix := false;
  with_constructor_as_block := true |}.

Program Definition optional_unsafe_transforms econf :=
  let efl := EConstructorsAsBlocks.switch_cstr_as_blocks
  (EInlineProjections.disable_projections_env_flag (ERemoveParams.switch_no_params EWellformed.all_env_flags)) in
  ETransform.optional_self_transform econf.(enable_unsafe)
    ((* Rebuild the efficient lookup table *)
    rebuild_wf_env_transform (efl := efl) false false ▷
    (* Coinductives & cofixpoints are translated to inductive types and thunked fixpoints *)
    coinductive_to_inductive_transformation efl
      (has_app := eq_refl) (has_box := eq_refl) (has_rel := eq_refl) (has_pars := eq_refl) (has_cstrblocks := eq_refl) ▷
    reorder_cstrs_transformation efl final_wcbv_flags econf.(inductives_mapping) ▷
    rebuild_wf_env_transform (efl := efl) false false ▷
    unbox_transformation efl final_wcbv_flags ▷
    inline_transformation efl final_wcbv_flags econf.(inlining) ▷
    forget_inlining_info_transformation efl final_wcbv_flags ▷
    (* Heuristically do it twice for more beta-normal terms *)
    betared_transformation efl final_wcbv_flags ▷
    betared_transformation efl final_wcbv_flags).

Program Definition verified_lambdabox_pipeline {guard : abstract_guard_impl}
  (efl := EWellformed.all_env_flags)
  : Transform.t _ _ EAst.term EAst.term _ _
   (* Standard evaluation, with cases on prop, guarded fixpoints, applied constructors *)
   (EProgram.eval_eprogram_env default_wcbv_flags)
   (* Target evaluation, with no more cases on prop, unguarded fixpoints, constructors as block *)
   (EProgram.eval_eprogram final_wcbv_flags) :=

  (* Simulation of the guarded fixpoint rules with a single unguarded one:
    the only "stuck" fixpoints remaining are unapplied.
    This translation is a noop on terms and environments.  *)
  guarded_to_unguarded_fix (fl := default_wcbv_flags) (wcon := eq_refl) eq_refl ▷
  (* Remove all constructor parameters *)
  remove_params_optimization (wcon := eq_refl) ▷
  (* Rebuild the efficient lookup table *)
  rebuild_wf_env_transform (efl := ERemoveParams.switch_no_params EWellformed.all_env_flags) true false ▷
  (* Remove all cases / projections on propositional content *)
  remove_match_on_box_trans (efl := ERemoveParams.switch_no_params EWellformed.all_env_flags) (wcon := eq_refl) (hastrel := eq_refl) (hastbox := eq_refl) ▷
  (* Rebuild the efficient lookup table *)
  rebuild_wf_env_transform (efl := ERemoveParams.switch_no_params EWellformed.all_env_flags) true false ▷
  (* Inline projections to cases *)
  inline_projections_optimization (fl := EWcbvEval.target_wcbv_flags) (wcon := eq_refl) (hastrel := eq_refl) (hastbox := eq_refl) ▷
  (* Rebuild the efficient lookup table *)
  rebuild_wf_env_transform (efl := EInlineProjections.disable_projections_env_flag (ERemoveParams.switch_no_params EWellformed.all_env_flags)) true false ▷
  (* First-order constructor representation *)
  constructors_as_blocks_transformation
    (efl := EInlineProjections.disable_projections_env_flag (ERemoveParams.switch_no_params EWellformed.all_env_flags))
    (has_app := eq_refl) (has_pars := eq_refl) (has_rel := eq_refl) (has_box := eq_refl) (has_cstrblocks := eq_refl).

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

Program Definition verified_erasure_pipeline {guard : abstract_guard_impl} (efl := EWellformed.all_env_flags) :
 Transform.t _ _
  PCUICAst.term EAst.term _ _
  PCUICTransform.eval_pcuic_program
  (EProgram.eval_eprogram final_wcbv_flags) :=
  (* a bunch of nonsense for normalization preconditions *)
  let K ty (T : ty -> _) p
    := let p := T p in
       (PCUICTyping.wf_ext p -> PCUICSN.NormalizationIn p) /\
         (PCUICTyping.wf_ext p -> PCUICWeakeningEnvSN.normalizationInAdjustUniversesIn p) in
  let T1 (p:global_env_ext_map) := p in
  (* Branches of cases are expanded to bind only variables, constructor types are expanded accordingly *)
  pcuic_expand_lets_transform (K _ T1) ▷
  (* Erasure of proofs terms in Prop and types *)
  erase_transform ▷
  verified_lambdabox_pipeline.

Import EGlobalEnv EWellformed.

Definition transform_compose
  {env env' env'' term term' term'' value value' value'' : Type}
  {eval eval' eval''}
  (o : t env env' term term' value value' eval eval')
  (o' : t env' env'' term' term'' value' value'' eval' eval'')
  (pre : forall p, post o p -> pre o' p) :
  forall x p1, exists p3,
    transform (compose o o' pre) x p1 = transform o' (transform o x p1) p3.
Proof.
  cbn. intros.
  unfold run, time.
  eexists;reflexivity.
Qed.

Lemma verified_lambdabox_pipeline_extends {guard : abstract_guard_impl} (efl := EWellformed.all_env_flags) :
  TransformExt.t verified_lambdabox_pipeline (fun p p' => extends (EEnvMap.GlobalContextMap.global_decls p.1)
  (EEnvMap.GlobalContextMap.global_decls p'.1)) (fun p p' => extends p.1 p'.1).
Proof.
  unfold verified_lambdabox_pipeline. tc.
Qed.

Lemma verified_lambdabox_pipeline_extends' {guard : abstract_guard_impl} (efl := EWellformed.all_env_flags) :
  TransformExt.t verified_lambdabox_pipeline extends_eprogram_env extends_eprogram.
Proof.
  unfold verified_lambdabox_pipeline. tc.
Qed.

Program Definition pre_erasure_pipeline {guard : abstract_guard_impl} (efl := EWellformed.all_env_flags) :
 Transform.t _ _
  Ast.term PCUICAst.term _ _
  TemplateProgram.eval_template_program
   PCUICTransform.eval_pcuic_program :=
  (* a bunch of nonsense for normalization preconditions *)
  let K ty (T : ty -> _) p
    := let p := T p in
       (PCUICTyping.wf_ext p -> PCUICSN.NormalizationIn p) /\
         (PCUICTyping.wf_ext p -> PCUICWeakeningEnvSN.normalizationInAdjustUniversesIn p) in
  let T1 (p:global_env_ext_map) := p in
  let T2 (p:global_env_ext_map) := T1 (build_global_env_map (PCUICExpandLets.trans_global_env p.1), p.2) in
  let T3 (p:global_env) := T2 (TemplateToPCUIC.trans_global_env p, Monomorphic_ctx) in
  let T4 (p:GlobalEnvMap.t) := T3 (eta_expand_global_env p) in
  (* Build an efficient lookup map for the following eta-expansion phase *)
  build_template_program_env (K _ T4) ▷
  (* Eta-expand constructors and fixpoint *)
  eta_expand (K _ T3) ▷
  (* Casts are removed, application is binary, case annotations are inferred from the global environment *)
  template_to_pcuic_transform (K _ T2).

Program Definition erasure_pipeline {guard : abstract_guard_impl} (efl := EWellformed.all_env_flags) : Transform.t _ _
  Ast.term EAst.term _ _
  TemplateProgram.eval_template_program
  (EProgram.eval_eprogram final_wcbv_flags) :=
  pre_erasure_pipeline ▷
  verified_erasure_pipeline.

Program Definition verified_lambdabox_typed_pipeline {guard : abstract_guard_impl} (efl := EWellformed.all_env_flags) econf :
  Transform.t _ _ EAst.term EAst.term _ _
    (EProgram.eval_eprogram_env {| with_prop_case := false; with_guarded_fix := true; with_constructor_as_block := false |})
    (EProgram.eval_eprogram final_wcbv_flags) :=
   (* Simulation of the guarded fixpoint rules with a single unguarded one:
     the only "stuck" fixpoints remaining are unapplied.
     This translation is a noop on terms and environments.  *)
   guarded_to_unguarded_fix (fl := {| with_prop_case := false; with_guarded_fix := true; with_constructor_as_block := false |}) (wcon := eq_refl) eq_refl ▷
   (* Remove all constructor parameters *)
   remove_params_optimization (wcon := eq_refl) ▷
   (* Rebuild the efficient lookup table *)
   rebuild_wf_env_transform (efl := ERemoveParams.switch_no_params EWellformed.all_env_flags) true false ▷
   (* Inline projections to cases *)
   inline_projections_optimization (fl := EWcbvEval.target_wcbv_flags) (wcon := eq_refl) (hastrel := eq_refl) (hastbox := eq_refl) ▷
   (* Rebuild the efficient lookup table *)
   rebuild_wf_env_transform (efl := EInlineProjections.disable_projections_env_flag (ERemoveParams.switch_no_params EWellformed.all_env_flags)) true false ▷
   (* First-order constructor representation *)
   constructors_as_blocks_transformation
     (efl := EInlineProjections.disable_projections_env_flag (ERemoveParams.switch_no_params EWellformed.all_env_flags))
     (has_app := eq_refl) (has_pars := eq_refl) (has_rel := eq_refl) (has_box := eq_refl) (has_cstrblocks := eq_refl) ▷
   optional_unsafe_transforms econf.

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

Next Obligation.
  unfold optional_unsafe_transforms. cbn.
  destruct enable_unsafe => //.
Qed.

Local Obligation Tactic := intros; eauto.

Program Definition verified_typed_erasure_pipeline {guard : abstract_guard_impl}
  (efl := EWellformed.all_env_flags)
  econf :
  Transform.t _ _
   PCUICAst.term EAst.term _ _
   PCUICTransform.eval_pcuic_program
   (EProgram.eval_eprogram final_wcbv_flags) :=
   (* a bunch of nonsense for normalization preconditions *)
   let K ty (T : ty -> _) p
     := let p := T p in
        (PCUICTyping.wf_ext p -> PCUICSN.NormalizationIn p) /\
          (PCUICTyping.wf_ext p -> PCUICWeakeningEnvSN.normalizationInAdjustUniversesIn p) in
   let T1 (p:global_env_ext_map) := p in
   (* Branches of cases are expanded to bind only variables, constructor types are expanded accordingly *)
   pcuic_expand_lets_transform (K _ T1) ▷
   (* Erasure of proofs terms in Prop and types *)
   typed_erase_transform ▷
   (* Remove match on box early for dearging *)
   remove_match_on_box_typed_transform (wcon := eq_refl) (hastrel := eq_refl) (hastbox := eq_refl) ▷
   (* Check if the preconditions for dearging are valid, otherwise dearging will be the identity *)
   dearging_checks_transform econf.(dearging_config) (hastrel := eq_refl) (hastbox := eq_refl) ▷
   dearging_transform econf.(dearging_config) ▷
   rebuild_wf_env_transform true true ▷
   verified_lambdabox_typed_pipeline econf.

  Next Obligation.
    cbn in H. split; cbn; intuition eauto.
  Qed.
  Next Obligation.
    cbn in H |- *; intuition eauto.
  Qed.

Program Definition typed_erasure_pipeline {guard : abstract_guard_impl}
  (efl := EWellformed.all_env_flags)
  econf :
  Transform.t _ _
   Ast.term EAst.term _ _
   TemplateProgram.eval_template_program
   (EProgram.eval_eprogram final_wcbv_flags) :=
   pre_erasure_pipeline ▷
   verified_typed_erasure_pipeline econf.

(* At the end of erasure we get a well-formed program (well-scoped globally and localy), without
   parameters in inductive declarations. The constructor applications are also transformed to a first-order
   "block"  application, of the right length, and the evaluation relation does not need to consider guarded
   fixpoints or case analyses on propositional content. All fixpoint bodies start with a lambda as well.
   Finally, projections are inlined to cases, so no `tProj` remains. *)

Import EGlobalEnv EWellformed.

Program Definition erasure_pipeline_fast {guard : abstract_guard_impl} (efl := EWellformed.all_env_flags) econf :=
  (* a bunch of nonsense for normalization preconditions *)
  let K ty (T : ty -> _) p
    := let p := T p in
       (PCUICTyping.wf_ext p -> PCUICSN.NormalizationIn p) /\
         (PCUICTyping.wf_ext p -> PCUICWeakeningEnvSN.normalizationInAdjustUniversesIn p) in
  let T1 (p:global_env_ext_map) := p in
  let T2 (p:global_env_ext_map) := T1 (build_global_env_map (PCUICExpandLets.trans_global_env p.1), p.2) in
  let T3 (p:global_env) := T2 (TemplateToPCUIC.trans_global_env p, Monomorphic_ctx) in
  let T4 (p:GlobalEnvMap.t) := T3 (eta_expand_global_env p) in
  build_template_program_env (K _ T4) ▷
  eta_expand (K _ T3) ▷
  template_to_pcuic_transform (K _ T2) ▷
  pcuic_expand_lets_transform (K _ T1) ▷
  erase_transform ▷
  guarded_to_unguarded_fix (wcon := eq_refl) eq_refl ▷
  remove_params_fast_optimization (wcon := eq_refl)  ▷
  rebuild_wf_env_transform (efl := ERemoveParams.switch_no_params EWellformed.all_env_flags) true false ▷
  remove_match_on_box_trans (efl := ERemoveParams.switch_no_params EWellformed.all_env_flags) (wcon := eq_refl) (hastrel := eq_refl) (hastbox := eq_refl) ▷
  rebuild_wf_env_transform (efl := ERemoveParams.switch_no_params EWellformed.all_env_flags) true false ▷
  inline_projections_optimization (fl := EWcbvEval.target_wcbv_flags) (wcon := eq_refl) (hastrel := eq_refl) (hastbox := eq_refl) ▷
  let efl := EInlineProjections.disable_projections_env_flag (ERemoveParams.switch_no_params EWellformed.all_env_flags) in
  rebuild_wf_env_transform (efl :=  efl) true false ▷
  constructors_as_blocks_transformation (efl := efl) (has_app := eq_refl) (has_pars := eq_refl) (has_rel := eq_refl) (has_box := eq_refl) (has_cstrblocks := eq_refl) ▷
  optional_unsafe_transforms econf.
Next Obligation.
  destruct H; split => //. now eapply ETransform.expanded_eprogram_env_expanded_eprogram_cstrs.
Qed.
Next Obligation.
  cbn in H. split; cbn; intuition eauto.
Qed.
Next Obligation.
  cbn in H. split; cbn; intuition eauto.
Qed.
Next Obligation.
  cbn in H. split; cbn; intuition eauto.
Qed.
Next Obligation.
  cbn in H. split; cbn; intuition eauto.
Qed.
Next Obligation.
  cbn in H. split; cbn; intuition eauto.
Qed.
Next Obligation.
  cbn in H. unfold optional_unsafe_transforms. destruct enable_unsafe => //.
Qed.
Next Obligation.
  cbn in H. split; cbn; intuition eauto.
Qed.

Definition run_erase_program_fast {guard : abstract_guard_impl} (econf : erasure_configuration) :=
  run (erasure_pipeline_fast econf).

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

(** Ideally we'd have a MetaCoq template program that generates a proof of Strong Normalization for the particular program we're erasing.  For now we just axiomatize SN. *)
Axiom fake_normalization : PCUICSN.Normalization.
Global Existing Instance fake_normalization.

(** This uses the retyping-based erasure and assumes that the global environment and term
  are welltyped (for speed). As such this should only be used for testing, or when we know that
  the environment is wellformed and the term well-typed (e.g. when it comes directly from a
  Coq definition). *)


Axiom assume_that_we_only_erase_on_welltyped_programs : forall {cf : checker_flags},
  forall (p : Ast.Env.program), squash (TemplateProgram.wt_template_program p).

(* This also optionally runs the cofix to fix translation *)
Program Definition run_erase_program {guard : abstract_guard_impl} econf :=
  if econf.(enable_typed_erasure) then run (typed_erasure_pipeline econf)
  else if econf.(enable_fast_remove_params) then
    run (erasure_pipeline_fast econf)
  else run (erasure_pipeline ▷ (optional_unsafe_transforms econf)).
Next Obligation.
Proof.
  unfold optional_unsafe_transforms.
  destruct enable_unsafe => //.
Qed.

Program Definition erase_and_print_template_program econf (p : Ast.Env.program) : string :=
  let p' := run_erase_program econf p _ in
  time "Pretty printing" EPretty.print_program p'.
Next Obligation.
  split.
  now eapply assume_that_we_only_erase_on_welltyped_programs.
  cbv [PCUICWeakeningEnvSN.normalizationInAdjustUniversesIn].
  pose proof @PCUICSN.normalization.
  split; typeclasses eauto.
Qed.

Definition erasure_fast_config :=
  {| enable_unsafe := false;
     dearging_config := default_dearging_config;
     enable_typed_erasure := false;
     enable_fast_remove_params := true;
     inductives_mapping := [];
     inlining := KernameSet.empty |}.

Program Definition erase_fast_and_print_template_program (p : Ast.Env.program) : string :=
  erase_and_print_template_program erasure_fast_config p.

Definition typed_erasure_config :=
  {| enable_unsafe := false;
      dearging_config := default_dearging_config;
      enable_typed_erasure := true;
      enable_fast_remove_params := true;
      inductives_mapping := [];
      inlining := KernameSet.empty |}.

(* Parameterized by a configuration for dearging, allowing to, e.g., override masks. *)
Program Definition typed_erase_and_print_template_program (p : Ast.Env.program)
  : string :=
  erase_and_print_template_program typed_erasure_config p.
