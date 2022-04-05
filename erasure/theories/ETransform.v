(* Distributed under the terms of the MIT license. *)
From Coq Require Import Program ssreflect ssrbool.
From Equations Require Import Equations.
From MetaCoq.Template Require Import Transform bytestring config utils BasicAst uGraph.
From MetaCoq.Template Require Pretty Environment Typing WcbvEval EtaExpand.
Set Warnings "-notation-overridden".
From MetaCoq.PCUIC Require PCUICAst PCUICAstUtils PCUICProgram PCUICTransform.
Set Warnings "+notation-overridden".
From MetaCoq.SafeChecker Require Import PCUICErrors PCUICWfEnvImpl.
From MetaCoq.Erasure Require EAstUtils ErasureFunction ErasureCorrectness EPretty Extract EOptimizePropDiscr ERemoveParams EProgram.

Import PCUICAst (term) PCUICProgram PCUICTransform (eval_pcuic_program) Extract EProgram
    EAst Transform ERemoveParams.
Import EEnvMap EGlobalEnv EWellformed.

Program Definition erase_transform : Transform.t pcuic_program eprogram_env PCUICAst.term EAst.term 
  eval_pcuic_program (eval_eprogram_env EWcbvEval.default_wcbv_flags) :=
 {| name := "erasure";
    pre p :=  
      ∥ wt_pcuic_program (cf := config.extraction_checker_flags) p ∥ /\ PCUICEtaExpand.expanded_pcuic_program p ;
    transform p hp := erase_program p (proj1 hp) ;
    post p := [/\ wf_eprogram_env all_env_flags p & expanded_eprogram_env p];
    obseq g g' v v' := let Σ := g.1 in Σ ;;; [] |- v ⇝ℇ v' |}.
Next Obligation.
  cbn -[erase_program].
  intros p [wtp etap].
  destruct erase_program eqn:e.
  split; cbn.
  - unfold erase_program, erase_pcuic_program in e. simpl. injection e. intros <- <-.
    split. 
    eapply ErasureFunction.erase_global_wf_glob. eapply ErasureFunction.erase_wellformed.
  - rewrite -e. cbn.
    now eapply expanded_erase_program.
Qed.

Next Obligation.
  red. move=> [Σ t] v [[wf [T HT]]]. unfold eval_pcuic_program, eval_eprogram.
  intros [ev].
  destruct erase_program eqn:e.
  unfold erase_program, erase_pcuic_program in e. simpl in e. injection e; intros <- <-.
  simpl. clear e. cbn in *.
  set (Σ' := build_wf_env_from_env _ _).
  eapply (ErasureFunction.erase_correct Σ' Σ.2 _ _ _ _ _ (EAstUtils.term_global_deps _)) in ev; try reflexivity.
  2:eapply Kernames.KernameSet.subset_spec; reflexivity.
  destruct ev as [v' [he [hev]]]. exists v'; split => //.
  red. cbn.
  sq. eexact hev.
Qed.

(** This transformation is the identity on terms but changes the evaluation relation to one
    where fixpoints are not guarded. It requires eta-expanded fixpoints and evaluation 
    to use the guarded fixpoint rule as a precondition. *)

Import EWcbvEval (WcbvFlags, with_prop_case, with_guarded_fix).

Program Definition guarded_to_unguarded_fix {fl : EWcbvEval.WcbvFlags} {efl : EEnvFlags} (wguard : with_guarded_fix) :
  Transform.t eprogram_env eprogram_env EAst.term EAst.term 
    (eval_eprogram_env fl) (eval_eprogram_env (EEtaExpandedFix.switch_unguarded_fix fl)) :=
  {| name := "switching to unguarded fixpoints";
    transform p pre := p;
    pre p := wf_eprogram_env efl p /\ expanded_eprogram_env p;
    post p := wf_eprogram_env efl p /\ expanded_eprogram_env p;
    obseq g g' v v' := v' = v |}.
Next Obligation. cbn. eauto. Qed.
Next Obligation.
  cbn.
  move=> fl efl wguard [Σ t] v [wfp /andP[etae etat]]. cbn in *.
  intros [ev]. exists v. split => //.
  red. sq. cbn in *.
  apply EEtaExpandedFix.eval_opt_to_target => //. apply wfp.
Qed.

Program Definition remove_params_optimization {fl : EWcbvEval.WcbvFlags} 
  (efl := all_env_flags): 
  Transform.t eprogram_env eprogram EAst.term EAst.term (eval_eprogram_env fl) (eval_eprogram fl) :=
  {| name := "stripping constructor parameters";
    transform p pre := ERemoveParams.strip_program p;
    pre p := wf_eprogram_env efl p /\ expanded_eprogram_env_cstrs p;
    post p := wf_eprogram (switch_no_params efl) p /\ expanded_eprogram_cstrs p;
    obseq g g' v v' := v' = (ERemoveParams.strip g.1 v) |}.
Next Obligation.
  move=> fl efl [Σ t] [wfp etap].
  simpl.
  cbn -[ERemoveParams.strip] in *.
  split. now eapply ERemoveParams.strip_program_wf.
  now eapply ERemoveParams.strip_program_expanded.
Qed.

Next Obligation.
  red. move=> ? [Σ t] /= v [[wfe wft] etap] [ev].
  eapply ERemoveParams.strip_eval in ev; eauto.
  eexists; split => /= //. now sq. cbn in *.
  now eapply wellformed_closed_env.
  now move/andP: etap.
  now eapply wellformed_closed.
  now move/andP: etap.
Qed.

Program Definition remove_params_fast_optimization (fl : EWcbvEval.WcbvFlags)
  (efl := all_env_flags) :
  Transform.t eprogram_env eprogram EAst.term EAst.term (eval_eprogram_env fl) (eval_eprogram fl) :=
  {| name := "stripping constructor parameters (faster?)";
    transform p _ := (ERemoveParams.Fast.strip_env p.1, ERemoveParams.Fast.strip p.1 [] p.2);
    pre p := wf_eprogram_env efl p /\ expanded_eprogram_env_cstrs p;
    post p := wf_eprogram (switch_no_params efl) p /\ expanded_eprogram_cstrs p;
    obseq g g' v v' := v' = (ERemoveParams.strip g.1 v) |}.
Next Obligation.
  move=> fl efl [Σ t] [wfp etap].
  simpl.
  cbn -[ERemoveParams.strip] in *.
  rewrite -ERemoveParams.Fast.strip_fast -ERemoveParams.Fast.strip_env_fast.
  split. 
  now eapply (ERemoveParams.strip_program_wf (Σ, t)).
  now eapply (ERemoveParams.strip_program_expanded (Σ, t)).
Qed.

Next Obligation.
  red. move=> ? [Σ t] /= v [[wfe wft] etap] [ev].
  rewrite -ERemoveParams.Fast.strip_fast -ERemoveParams.Fast.strip_env_fast.
  eapply ERemoveParams.strip_eval in ev; eauto.
  eexists; split => /= //.
  now sq. cbn in *.
  now eapply wellformed_closed_env.
  now move/andP: etap.
  now eapply wellformed_closed.
  now move/andP: etap.
Qed.

Import EOptimizePropDiscr EWcbvEval.

Program Definition optimize_prop_discr_optimization {fl : WcbvFlags} {efl : EEnvFlags} {hastrel : has_tRel} {hastbox : has_tBox} :
  self_transform eprogram EAst.term (eval_eprogram fl) (eval_eprogram (disable_prop_cases fl)) := 
  {| name := "optimize_prop_discr"; 
    transform p _ := optimize_program p ; 
    pre p := wf_eprogram efl p /\ expanded_eprogram_cstrs p;
    post p := wf_eprogram efl p /\ expanded_eprogram_cstrs p;
    obseq g g' v v' := v' = EOptimizePropDiscr.optimize g.1 v |}.

Next Obligation.
  move=> fl efl hastrel hastbox [Σ t] [wfp etap].
  cbn in *. split.
  - now eapply optimize_program_wf.
  - now eapply optimize_program_expanded.
Qed.
Next Obligation.
  red. move=> fl efl hastrel hastbox [Σ t] /= v [wfe wft] [ev].
  eapply EOptimizePropDiscr.optimize_correct in ev; eauto.
  eexists; split => //. red. sq; auto. cbn. apply wfe.
  eapply wellformed_closed_env, wfe.
  eapply wellformed_closed, wfe.
Qed.
