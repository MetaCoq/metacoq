(* Distributed under the terms of the MIT license. *)
From Coq Require Import Program ssreflect ssrbool.
From Equations Require Import Equations.
From MetaCoq.Template Require Import Transform bytestring config utils BasicAst uGraph.
From MetaCoq.Template Require Pretty Environment Typing WcbvEval EtaExpand.
Set Warnings "-notation-overridden".
From MetaCoq.PCUIC Require PCUICAst PCUICAstUtils PCUICProgram PCUICTransform.
Set Warnings "+notation-overridden".
From MetaCoq.SafeChecker Require Import PCUICErrors PCUICWfEnvImpl.
From MetaCoq.Erasure Require EAstUtils ErasureFunction ErasureCorrectness EPretty Extract EProgram.

Import PCUICAst (term) PCUICProgram PCUICTransform (eval_pcuic_program) Extract EProgram
    EAst Transform.
Import EEnvMap EGlobalEnv.

Program Definition erase_transform : Transform.t pcuic_program eprogram_env PCUICAst.term EAst.term 
  eval_pcuic_program (eval_eprogram_env EWcbvEval.default_wcbv_flags) :=
 {| name := "erasure";
    pre p :=  
      ∥ wt_pcuic_program (cf := config.extraction_checker_flags) p ∥ /\ PCUICEtaExpand.expanded_pcuic_program p ;
    transform p hp := erase_program p (proj1 hp) ;
    post p :=
      let decls := p.1.(GlobalContextMap.global_decls) in
      [/\ wf_glob decls, closed_eprogram_env p & expanded_eprogram p];
    obseq g g' v v' := let Σ := g.1 in Σ ;;; [] |- v ⇝ℇ v' |}.
Next Obligation.
  cbn -[erase_program].
  intros p [wtp etap].
  destruct erase_program eqn:e.
  split; cbn.
  - unfold erase_program, erase_pcuic_program in e. simpl. injection e. intros <- <-. 
    eapply ErasureFunction.erase_global_wf_glob.
  - apply/andP; split.
    * unfold erase_program, erase_pcuic_program in e. simpl. injection e. intros <- <-. 
      eapply ErasureFunction.erase_global_closed.
    * unfold erase_program, erase_pcuic_program in e. simpl. injection e. intros <- <-. 
      eapply (ErasureFunction.erases_closed _ []). eapply ErasureFunction.erases_erase.
      clear e. destruct wtp as [[wfΣ [T HT]]].
      now eapply (@PCUICClosedTyp.subject_closed _ _) in HT.
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

Program Definition guarded_to_unguarded_fix {fl : EWcbvEval.WcbvFlags} (wguard : with_guarded_fix) :
  Transform.t eprogram_env eprogram_env EAst.term EAst.term 
    (eval_eprogram_env fl) (eval_eprogram_env (EEtaExpandedFix.switch_unguarded_fix fl)) :=
  {| name := "switching to unguarded fixpoints";
    transform p pre := p;
    pre p := 
    let decls := p.1.(GlobalContextMap.global_decls) in
     [/\ wf_glob decls, closed_eprogram_env p & expanded_eprogram p ];
    post p := let decls := p.1.(GlobalContextMap.global_decls) in
     [/\ wf_glob decls, closed_eprogram_env p & expanded_eprogram p ];
    obseq g g' v v' := v' = v |}.
Next Obligation. cbn. eauto. Qed.
Next Obligation.
  cbn.
  move=> fl wguard [Σ t] v [wfe /andP[cle clt] /andP[etae etat]]. cbn in *.
  intros [ev]. exists v. split => //.
  red. sq. cbn in *.
  now apply EEtaExpandedFix.eval_opt_to_target.
Qed.

Program Definition remove_params (p : eprogram_env) : eprogram :=
  (ERemoveParams.strip_env p.1, ERemoveParams.strip p.1 p.2).

Program Definition remove_params_optimization {fl : EWcbvEval.WcbvFlags} : 
  Transform.t eprogram_env eprogram EAst.term EAst.term (eval_eprogram_env fl) (eval_eprogram fl) :=
  {| name := "stripping constructor parameters";
    transform p pre := remove_params p;
    pre p := 
    let decls := p.1.(GlobalContextMap.global_decls) in
     [/\ wf_glob decls, closed_eprogram_env p & expanded_eprogram_cstrs p ];
    post := closed_eprogram;
    obseq g g' v v' := v' = (ERemoveParams.strip g.1 v) |}.
Next Obligation.
  move=> fl [Σ t] [wfe /andP[cle clt] etap].
  simpl.
  cbn -[ERemoveParams.strip] in *.
  apply/andP; split; cbn.
  move: cle. unfold closed_env. unfold ERemoveParams.strip_env.
  rewrite forallb_map. eapply forallb_impl. intros.
  destruct x as [kn []]; cbn in * => //.
  destruct Extract.E.cst_body => //. cbn -[ERemoveParams.strip] in H0 |- *.
  now eapply ERemoveParams.closed_strip.
  now eapply ERemoveParams.closed_strip.
Qed.

Next Obligation.
  red. move=> ? [Σ t] /= v [wfe /andP[cle clt] etap] [ev].
  eapply ERemoveParams.strip_eval in ev; eauto.
  eexists; split => //. now sq.
  all:move/andP: etap => [] => //.
Qed.

Program Definition remove_params_fast_optimization (fl : EWcbvEval.WcbvFlags) :
  Transform.t eprogram_env eprogram EAst.term EAst.term (eval_eprogram_env fl) (eval_eprogram fl) :=
  {| name := "stripping constructor parameters (faster?)";
    transform p _ := (ERemoveParams.Fast.strip_env p.1, ERemoveParams.Fast.strip p.1 [] p.2);
    pre p := 
      let decls := p.1.(GlobalContextMap.global_decls) in
      [/\ wf_glob decls, closed_eprogram_env p & expanded_eprogram_cstrs p];
    post := closed_eprogram;
    obseq g g' v v' := v' = (ERemoveParams.strip g.1 v) |}.
Next Obligation.
  move=> fl [Σ t] [wfe /andP[cle clt] etap].
  simpl.
  apply/andP.
  rewrite -ERemoveParams.Fast.strip_fast -ERemoveParams.Fast.strip_env_fast.
  cbn -[ERemoveParams.strip] in *.
  split.
  move: cle. unfold closed_env. unfold ERemoveParams.strip_env.
  rewrite forallb_map. eapply forallb_impl. intros.
  destruct x as [kn []]; cbn in * => //.
  destruct Extract.E.cst_body => //. cbn -[ERemoveParams.strip] in H0 |- *.
  now eapply ERemoveParams.closed_strip.
  now eapply ERemoveParams.closed_strip.
Qed.
Next Obligation.
  red. move=> ? [Σ t] /= v [wfe /andP[cle clt] etap] [ev].
  rewrite -ERemoveParams.Fast.strip_fast -ERemoveParams.Fast.strip_env_fast.
  eapply ERemoveParams.strip_eval in ev; eauto.
  eexists; split => //. now sq.
  all:move/andP: etap => [] => //.
Qed.

Import EOptimizePropDiscr EWcbvEval.

Program Definition optimize_prop_discr_optimization {fl : WcbvFlags} : 
  self_transform eprogram EAst.term (eval_eprogram fl) 
    (eval_eprogram (disable_prop_cases fl)) := 
  {| name := "optimize_prop_discr"; 
    transform p _ := 
      (EOptimizePropDiscr.optimize_env p.1, EOptimizePropDiscr.optimize p.1 p.2);
    pre := closed_eprogram;
    post := closed_eprogram;
    obseq g g' v v' := v' = EOptimizePropDiscr.optimize g.1 v
    |}.

Next Obligation.
  move=> fl [Σ t] /andP[cle clt].
  cbn in *. apply/andP; split.
  move: cle. cbn. induction Σ at 1 3; cbn; auto.
  move/andP => [] cla clg. rewrite (IHg clg) andb_true_r.
  destruct a as [kn []]; cbn in * => //.
  destruct Extract.E.cst_body => //. cbn in cla |- *.
  now eapply EOptimizePropDiscr.closed_optimize.
  now eapply EOptimizePropDiscr.closed_optimize.
Qed.
Next Obligation.
  red. move=> fl [Σ t] /= v /andP[cle clt] [ev].
  eapply EOptimizePropDiscr.optimize_correct in ev; eauto.
  eexists; split => //. red. sq; auto.
Qed.
