(* Distributed under the terms of the MIT license. *)
From Coq Require Import Program ssreflect ssrbool.
From Equations Require Import Equations.
From MetaCoq.Template Require Import Transform bytestring config utils BasicAst uGraph.
From MetaCoq.Template Require Pretty Environment Typing WcbvEval EtaExpand.
Set Warnings "-notation-overridden".
From MetaCoq.PCUIC Require PCUICAst PCUICAstUtils PCUICProgram PCUICTransform.
Set Warnings "+notation-overridden".
From MetaCoq.SafeChecker Require Import PCUICErrors PCUICWfEnvImpl.
From MetaCoq.Erasure Require EAstUtils ErasureFunction ErasureCorrectness Extract
   EOptimizePropDiscr ERemoveParams EProgram.

Import PCUICAst (term) PCUICProgram PCUICTransform (eval_pcuic_program) Extract EProgram
    EAst Transform ERemoveParams.
Import EEnvMap EGlobalEnv EWellformed.

Definition build_wf_env_from_env {cf : checker_flags} (Σ : global_env_map) (wfΣ : ∥ PCUICTyping.wf Σ ∥) : wf_env := 
  {| wf_env_referenced := {| referenced_impl_env := Σ.(trans_env_env); referenced_impl_wf := wfΣ |} ;
     wf_env_map := Σ.(trans_env_map);
     wf_env_map_repr := Σ.(trans_env_repr);
 |}.

Program Definition erase_pcuic_program {guard : abstract_guard_impl} (p : pcuic_program) 
  (wfΣ : ∥ PCUICTyping.wf_ext (H := config.extraction_checker_flags) p.1 ∥)
  (wt : ∥ ∑ T, PCUICTyping.typing (H := config.extraction_checker_flags) p.1 [] p.2 T ∥) : eprogram_env :=
  let wfe := build_wf_env_from_env p.1.1 (map_squash (PCUICTyping.wf_ext_wf _) wfΣ) in
  let wfext := optim_make_wf_env_ext (guard:=guard) wfe p.1.2 _ in
  let t := ErasureFunction.erase (nor:=PCUICSN.extraction_normalizing) optimized_abstract_env_impl wfext nil p.2
    (fun Σ wfΣ => let '(sq (T; ty)) := wt in PCUICTyping.iswelltyped ty) in
  let Σ' := ErasureFunction.erase_global_fast optimized_abstract_env_impl
    (EAstUtils.term_global_deps t) wfe (p.1.(PCUICAst.PCUICEnvironment.declarations)) _ in
    (EEnvMap.GlobalContextMap.make Σ' _, t).

Next Obligation.
  eapply wf_glob_fresh.
  eapply ErasureFunction.erase_global_fast_wf_glob.
Qed.

Obligation Tactic := idtac.

Import Extract.

Definition erase_program {guard : abstract_guard_impl} (p : pcuic_program) 
  (wtp : ∥ wt_pcuic_program (cf:=config.extraction_checker_flags) p ∥) : eprogram_env :=
  erase_pcuic_program (guard := guard) p (map_squash fst wtp) (map_squash snd wtp).

Lemma expanded_erase_program {guard : abstract_guard_impl} 
  (cf := config.extraction_checker_flags) p (wtp : ∥ wt_pcuic_program p ∥) :
  PCUICEtaExpand.expanded_pcuic_program p ->
  EEtaExpandedFix.expanded_eprogram_env (erase_program (guard:=guard) p wtp).
Proof.
  intros [etaenv etat]. split;
  unfold erase_program, erase_pcuic_program; cbn.
  eapply ErasureFunction.expanded_erase_global_fast, etaenv; reflexivity.
  apply: (ErasureFunction.expanded_erase_fast (X_type:=optimized_abstract_env_impl)).
  reflexivity. exact etat.
Qed.

Lemma expanded_eprogram_env_expanded_eprogram_cstrs p :
  EEtaExpandedFix.expanded_eprogram_env p ->
  EEtaExpanded.expanded_eprogram_env_cstrs p.
Proof.
  move=> [] etaenv etat.
  apply /andP.
  split.
  - eapply EEtaExpanded.isEtaExpFix_env_isEtaExp_env. now eapply EEtaExpandedFix.expanded_global_env_isEtaExp_env.
  - eapply EEtaExpanded.isEtaExpFix_isEtaExp. now eapply EEtaExpandedFix.expanded_isEtaExp.
Qed.

Program Definition erase_transform {guard : abstract_guard_impl}  : Transform.t pcuic_program eprogram_env PCUICAst.term EAst.term 
  eval_pcuic_program (eval_eprogram_env EWcbvEval.default_wcbv_flags) :=
 {| name := "erasure";
    pre p :=  
      ∥ wt_pcuic_program (cf := config.extraction_checker_flags) p ∥ /\ PCUICEtaExpand.expanded_pcuic_program p ;
    transform p hp := erase_program (guard:=guard) p (proj1 hp) ;
    post p := [/\ wf_eprogram_env all_env_flags p & EEtaExpandedFix.expanded_eprogram_env p];
    obseq g g' v v' := let Σ := g.1 in Σ ;;; [] |- v ⇝ℇ v' |}.
Next Obligation.
  cbn -[erase_program].
  intros ? p [wtp etap].
  destruct erase_program eqn:e.
  split; cbn.
  - unfold erase_program, erase_pcuic_program in e. simpl. cbn in e. injection e. intros <- <-.
    split. 
    eapply ErasureFunction.erase_global_fast_wf_glob.
    apply: (ErasureFunction.erase_wellformed_fast (X_type:=optimized_abstract_env_impl)).
  - rewrite -e. cbn.
    now eapply expanded_erase_program.
Qed.

Next Obligation.
  red. move=> guard [Σ t] v [[wf [T HT]]]. unfold eval_pcuic_program, eval_eprogram.
  intros [ev].
  destruct erase_program eqn:e.
  unfold erase_program, erase_pcuic_program in e. simpl in e. injection e; intros <- <-.
  simpl. clear e. cbn in *.
  set (Σ' := build_wf_env_from_env _ _).
  assert (ev' :forall Σ0 : PCUICAst.PCUICEnvironment.global_env, Σ0 = Σ' -> PCUICWcbvEval.eval Σ0 t v).
  { intros; now subst. }
  eapply (ErasureFunction.erase_correct optimized_abstract_env_impl Σ' Σ.2 _ _ _ _ _ (EAstUtils.term_global_deps _)) in ev'.
  4:{ erewrite <- ErasureFunction.erase_global_deps_fast_spec. reflexivity. }
  all:trea.
  2:eapply Kernames.KernameSet.subset_spec; reflexivity.
  destruct ev' as [v' [he [hev]]]. exists v'; split => //.
  red. cbn.
  sq. exact hev. Unshelve. cbn; intros. now subst.
Qed.

(** This transformation is the identity on terms but changes the evaluation relation to one
    where fixpoints are not guarded. It requires eta-expanded fixpoints and evaluation 
    to use the guarded fixpoint rule as a precondition. *)

Import EWcbvEval (WcbvFlags, with_prop_case, with_guarded_fix).

Program Definition guarded_to_unguarded_fix {fl : EWcbvEval.WcbvFlags} {wcon : EWcbvEval.with_constructor_as_block = false} {efl : EEnvFlags} (wguard : with_guarded_fix) :
  Transform.t eprogram_env eprogram_env EAst.term EAst.term 
    (eval_eprogram_env fl) (eval_eprogram_env (EWcbvEval.switch_unguarded_fix fl)) :=
  {| name := "switching to unguarded fixpoints";
    transform p pre := p;
    pre p := wf_eprogram_env efl p /\ EEtaExpandedFix.expanded_eprogram_env p;
    post p := wf_eprogram_env efl p /\ EEtaExpandedFix.expanded_eprogram_env p;
    obseq g g' v v' := v' = v |}.
Next Obligation. cbn. eauto. Qed.
Next Obligation.
  cbn.
  move=> fl wcon efl wguard [Σ t] v [wfp [etae etat]]. cbn in *.
  intros [ev]. exists v. split => //.
  red. sq. cbn in *.
  unshelve eapply EEtaExpandedFix.eval_opt_to_target => //. auto. 2:apply wfp.
  now eapply EEtaExpandedFix.expanded_global_env_isEtaExp_env.
  now eapply EEtaExpandedFix.expanded_isEtaExp.
Qed.

Definition rebuild_wf_env {efl} (p : eprogram) (hwf : wf_eprogram efl p): eprogram_env :=
  (GlobalContextMap.make p.1 (wf_glob_fresh p.1 (proj1 hwf)), p.2).

Program Definition rebuild_wf_env_transform {fl : EWcbvEval.WcbvFlags} {efl} (with_exp : bool) : 
  Transform.t eprogram eprogram_env EAst.term EAst.term (eval_eprogram fl) (eval_eprogram_env fl) :=
  {| name := "rebuilding environment lookup table";
     pre p := wf_eprogram efl p /\ (with_exp ==> EEtaExpanded.expanded_eprogram_cstrs p);
     transform p pre := rebuild_wf_env p (proj1 pre);
     post p := wf_eprogram_env efl p /\ (with_exp ==> EEtaExpanded.expanded_eprogram_env_cstrs p);
     obseq g g' v v' := v = v' |}.
Next Obligation.
  cbn. intros fl efl [] input [wf exp]; cbn; split => //.
Qed.
Next Obligation.
  cbn. intros fl efl [] input v [] ev p'; exists v; split => //.
Qed.

Program Definition remove_params_optimization {fl : EWcbvEval.WcbvFlags} {wcon : EWcbvEval.with_constructor_as_block = false}
  (efl := all_env_flags): 
  Transform.t eprogram_env eprogram EAst.term EAst.term (eval_eprogram_env fl) (eval_eprogram fl) :=
  {| name := "stripping constructor parameters";
    transform p pre := ERemoveParams.strip_program p;
    pre p := wf_eprogram_env efl p /\ EEtaExpanded.expanded_eprogram_env_cstrs p;
    post p := wf_eprogram (switch_no_params efl) p /\ EEtaExpanded.expanded_eprogram_cstrs p;
    obseq g g' v v' := v' = (ERemoveParams.strip g.1 v) |}.
Next Obligation.
  move=> fl wcon efl [Σ t] [wfp etap].
  simpl.
  cbn -[ERemoveParams.strip] in *.
  split. now eapply ERemoveParams.strip_program_wf.
  now eapply ERemoveParams.strip_program_expanded.
Qed.

Next Obligation.
  red. move=> ? wcon [Σ t] /= v [[wfe wft] etap] [ev].
  unshelve eapply ERemoveParams.strip_eval in ev; eauto.
  eexists; split => /= //. now sq. cbn in *.
  now move/andP: etap.
  now eapply wellformed_closed_env.
  now eapply wellformed_closed.
  now move/andP: etap.
Qed.

Program Definition remove_params_fast_optimization (fl : EWcbvEval.WcbvFlags) {wcon : EWcbvEval.with_constructor_as_block = false}
  (efl := all_env_flags) :
  Transform.t eprogram_env eprogram EAst.term EAst.term (eval_eprogram_env fl) (eval_eprogram fl) :=
  {| name := "stripping constructor parameters (faster?)";
    transform p _ := (ERemoveParams.Fast.strip_env p.1, ERemoveParams.Fast.strip p.1 [] p.2);
    pre p := wf_eprogram_env efl p /\ EEtaExpanded.expanded_eprogram_env_cstrs p;
    post p := wf_eprogram (switch_no_params efl) p /\ EEtaExpanded.expanded_eprogram_cstrs p;
    obseq g g' v v' := v' = (ERemoveParams.strip g.1 v) |}.
Next Obligation.
  move=> fl wcon efl [Σ t] [wfp etap].
  simpl.
  cbn -[ERemoveParams.strip] in *.
  rewrite -ERemoveParams.Fast.strip_fast -ERemoveParams.Fast.strip_env_fast.
  split. 
  now eapply (ERemoveParams.strip_program_wf (Σ, t)).
  now eapply (ERemoveParams.strip_program_expanded (Σ, t)).
Qed.

Next Obligation.
  red. move=> ? wcon [Σ t] /= v [[wfe wft] etap] [ev].
  rewrite -ERemoveParams.Fast.strip_fast -ERemoveParams.Fast.strip_env_fast.
  unshelve eapply ERemoveParams.strip_eval in ev; eauto.
  eexists; split => /= //.
  now sq. cbn in *.
  now move/andP: etap.
  now eapply wellformed_closed_env.
  now eapply wellformed_closed.
  now move/andP: etap.
Qed.

Import EOptimizePropDiscr EWcbvEval.

Program Definition optimize_prop_discr_optimization {fl : WcbvFlags} {wcon : with_constructor_as_block = false} {efl : EEnvFlags} {hastrel : has_tRel} {hastbox : has_tBox} :
  Transform.t eprogram_env eprogram EAst.term EAst.term (eval_eprogram_env fl) (eval_eprogram (disable_prop_cases fl)) := 
  {| name := "optimize_prop_discr"; 
    transform p _ := optimize_program p ; 
    pre p := wf_eprogram_env efl p /\ EEtaExpanded.expanded_eprogram_env_cstrs p;
    post p := wf_eprogram efl p /\ EEtaExpanded.expanded_eprogram_cstrs p;
    obseq g g' v v' := v' = EOptimizePropDiscr.optimize g.1 v |}.

Next Obligation.
  move=> fl wcon efl hastrel hastbox [Σ t] [wfp etap].
  cbn in *. split.
  - now eapply optimize_program_wf.
  - now eapply optimize_program_expanded.
Qed.
Next Obligation.
  red. move=> fl wcon efl hastrel hastbox [Σ t] /= v [wfe wft] [ev].
  eapply EOptimizePropDiscr.optimize_correct in ev; eauto.
  eexists; split => //. red. sq; auto. cbn. apply wfe.
  eapply wellformed_closed_env, wfe.
  eapply wellformed_closed, wfe.
  Unshelve. eauto.
Qed.

From MetaCoq.Erasure Require Import EInlineProjections.

Program Definition inline_projections_optimization {fl : WcbvFlags} {wcon : EWcbvEval.with_constructor_as_block = false} (efl := switch_no_params all_env_flags)
  {hastrel : has_tRel} {hastbox : has_tBox} :
  Transform.t eprogram_env eprogram EAst.term EAst.term (eval_eprogram_env fl) (eval_eprogram fl) := 
  {| name := "primitive projection inlining"; 
    transform p _ := EInlineProjections.optimize_program p ; 
    pre p := wf_eprogram_env efl p /\ EEtaExpanded.expanded_eprogram_env_cstrs p;
    post p := wf_eprogram (disable_projections_env_flag efl) p /\ EEtaExpanded.expanded_eprogram_cstrs p;
    obseq g g' v v' := v' = EInlineProjections.optimize g.1 v |}.

Next Obligation.
  move=> fl wcon efl hastrel hastbox [Σ t] [wfp etap].
  cbn in *. split.
  - now eapply optimize_program_wf.
  - now eapply optimize_program_expanded.
Qed.
Next Obligation.
  red. move=> fl wcon hastrel hastbox [Σ t] /= v [wfe wft] [ev].
  eapply EInlineProjections.optimize_correct in ev; eauto.
  eexists; split => //. red. sq; auto. cbn. apply wfe.
  cbn. eapply wfe. Unshelve. auto.
Qed.

From MetaCoq.Erasure Require Import EConstructorsAsBlocks.

Program Definition constructors_as_blocks_transformation (efl : EEnvFlags)
  {has_app : has_tApp} {has_pars : has_cstr_params = false} {has_cstrblocks : cstr_as_blocks = false} :
  Transform.t eprogram_env eprogram EAst.term EAst.term (eval_eprogram_env target_wcbv_flags) (eval_eprogram block_wcbv_flags) := 
  {| name := "transforming to constuctors as blocks"; 
    transform p _ := EConstructorsAsBlocks.transform_blocks_program p ; 
    pre p := wf_eprogram_env efl p /\ EEtaExpanded.expanded_eprogram_env_cstrs p;
    post p := wf_eprogram (switch_cstr_as_blocks efl) p ;
    obseq g g' v v' := v' = EConstructorsAsBlocks.transform_blocks g.1 v |}.

Next Obligation.
  move=> efl hasapp haspars hascstrs [Σ t] [] [wftp wft] /andP [etap etat]. 
  cbn in *. split.
  - eapply transform_wf_global; eauto.
  - eapply transform_wellformed; eauto.
Qed.
Next Obligation.
  red. move=> efl hasapp haspars hascstrs [Σ t] /= v [[wfe1 wfe2] wft] [ev].
  eexists. split; [ | eauto].
  unfold EEtaExpanded.expanded_eprogram_env_cstrs in *.
  revert wft. move => /andP // [e1 e2]. 
  econstructor. 
  cbn -[transform_blocks].
  eapply transform_blocks_eval; cbn; eauto.
Qed.
