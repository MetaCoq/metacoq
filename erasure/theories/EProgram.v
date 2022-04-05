(* Distributed under the terms of the MIT license. *)
From Coq Require Import Program ssreflect ssrbool.
From Equations Require Import Equations.
From MetaCoq.Template Require Import Transform bytestring config utils BasicAst.
From MetaCoq.PCUIC Require PCUICAst PCUICAstUtils PCUICProgram.
From MetaCoq.SafeChecker Require Import PCUICErrors PCUICWfEnvImpl.
From MetaCoq.Erasure Require EAstUtils ErasureFunction ErasureCorrectness EPretty Extract.
From MetaCoq.Erasure Require ErasureFunction EWellformed EEtaExpanded EWcbvEval EDeps.

Import bytestring.
Local Open Scope bs.
Local Open Scope string_scope2.

Import Transform.

Obligation Tactic := program_simpl.

Import PCUICProgram.

Definition build_wf_env_from_env {cf : checker_flags} (Σ : global_env_map) (wfΣ : ∥ PCUICTyping.wf Σ ∥) : wf_env := 
  {| wf_env_referenced := {| referenced_impl_env := Σ.(trans_env_env); referenced_impl_wf := wfΣ |} ;
     wf_env_map := Σ.(trans_env_map);
     wf_env_map_repr := Σ.(trans_env_repr);
 |}.

Import EGlobalEnv EWellformed.

Definition eprogram := (EAst.global_context * EAst.term).
Definition eprogram_env := (EEnvMap.GlobalContextMap.t * EAst.term).

Import EEnvMap.GlobalContextMap (make, global_decls).

Arguments EWcbvEval.eval {wfl} _ _ _.

Definition wf_eprogram (efl : EEnvFlags) (p : eprogram) :=
  @wf_glob efl p.1 /\ @wellformed efl p.1 0 p.2.
  
Definition wf_eprogram_env (efl : EEnvFlags) (p : eprogram_env) :=
  @wf_glob efl p.1.(global_decls) /\ @wellformed efl p.1.(global_decls) 0 p.2.

Definition eval_eprogram (wfl : EWcbvEval.WcbvFlags) (p : eprogram) (t : EAst.term) := 
  ∥ EWcbvEval.eval (wfl:=wfl) p.1 p.2 t ∥.

Definition closed_eprogram (p : eprogram) := 
  closed_env p.1 && ELiftSubst.closedn 0 p.2.

Definition closed_eprogram_env (p : eprogram_env) := 
  let Σ := p.1.(global_decls) in
  closed_env Σ && ELiftSubst.closedn 0 p.2.

Definition eval_eprogram_env (wfl : EWcbvEval.WcbvFlags) (p : eprogram_env) (t : EAst.term) := 
  ∥ EWcbvEval.eval (wfl:=wfl) p.1.(global_decls) p.2 t ∥.

Import EWellformed.

Lemma wf_glob_fresh {efl : EEnvFlags} Σ : wf_glob Σ -> EnvMap.EnvMap.fresh_globals Σ.
Proof.
  induction Σ. constructor; auto.
  intros wf; depelim wf. constructor; auto.
Qed.
  
Program Definition erase_pcuic_program (p : pcuic_program) 
  (wfΣ : ∥ PCUICTyping.wf_ext (H := config.extraction_checker_flags) p.1 ∥)
  (wt : ∥ ∑ T, PCUICTyping.typing (H := config.extraction_checker_flags) p.1 [] p.2 T ∥) : eprogram_env :=
  let wfe := build_wf_env_from_env p.1.1 (map_squash (PCUICTyping.wf_ext_wf _) wfΣ) in
  let wfe' := ErasureFunction.make_wf_env_ext wfe p.1.2 wfΣ in
  let t := ErasureFunction.erase wfe' nil p.2 _ in
  let Σ' := ErasureFunction.erase_global (EAstUtils.term_global_deps t) wfe in
  (EEnvMap.GlobalContextMap.make Σ' _, t).
  
Next Obligation.
  sq. destruct wt as [T Ht].
  cbn in *. subst. now exists T.
Qed.
Next Obligation.
  unfold ErasureFunction.erase_global.
  eapply wf_glob_fresh.
  eapply ErasureFunction.erase_global_decls_wf_glob.
Qed.

Obligation Tactic := idtac.

Import Extract.

Definition expanded_eprogram (p : eprogram) := 
  EEtaExpandedFix.isEtaExp_env p.1 && EEtaExpandedFix.isEtaExp p.1 [] p.2.

Definition expanded_eprogram_env (p : eprogram_env) := 
  let decls := p.1.(EEnvMap.GlobalContextMap.global_decls) in
  EEtaExpandedFix.isEtaExp_env decls && EEtaExpandedFix.isEtaExp decls [] p.2.

Definition expanded_eprogram_cstrs (p : eprogram) := 
  EEtaExpanded.isEtaExp_env p.1 && EEtaExpanded.isEtaExp p.1 p.2.

Definition expanded_eprogram_env_cstrs (p : eprogram_env) := 
  let decls := p.1.(EEnvMap.GlobalContextMap.global_decls) in
  EEtaExpanded.isEtaExp_env decls && EEtaExpanded.isEtaExp decls p.2.
  
Definition erase_program (p : pcuic_program) (wtp : ∥ wt_pcuic_program (cf:=config.extraction_checker_flags) p ∥) : eprogram_env :=
  erase_pcuic_program p (map_squash fst wtp) (map_squash snd wtp).

Lemma expanded_erase_program (cf := config.extraction_checker_flags) p (wtp : ∥ wt_pcuic_program p ∥) :
  PCUICEtaExpand.expanded_pcuic_program p ->
  expanded_eprogram_env (erase_program p wtp).
Proof.
  intros [etaenv etat]. apply /andP; split.
  eapply EEtaExpandedFix.expanded_global_env_isEtaExp_env, ErasureFunction.expanded_erase_global, etaenv.
  eapply EEtaExpandedFix.expanded_isEtaExp, ErasureFunction.expanded_erase, etat.
Qed.

Lemma expanded_eprogram_env_expanded_eprogram_cstrs p :
  expanded_eprogram_env p ->
  expanded_eprogram_env_cstrs p.
Proof.
  move=> /andP[] etaenv etat.
  apply /andP. split; [now eapply EEtaExpanded.isEtaExpFix_env_isEtaExp_env|
  now eapply EEtaExpanded.isEtaExpFix_isEtaExp].
Qed.

Lemma expanded_eprogram_expanded_eprogram_cstrs p :
  expanded_eprogram p ->
  expanded_eprogram_cstrs p.
Proof.
  move=> /andP[] etaenv etat.
  apply /andP. split; [now eapply EEtaExpanded.isEtaExpFix_env_isEtaExp_env|
  now eapply EEtaExpanded.isEtaExpFix_isEtaExp].
Qed.
