(* Distributed under the terms of the MIT license. *)
From Coq Require Import Program ssreflect.
From MetaCoq.Template Require Import config utils uGraph Pretty Environment Typing WcbvEval.
Set Warnings "-notation-overridden".
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping
     TemplateToPCUIC TemplateToPCUICCorrectness TemplateToPCUICWcbvEval.
From MetaCoq.PCUIC Require PCUICExpandLets PCUICExpandLetsCorrectness.
Set Warnings "+notation-overridden".
From MetaCoq.SafeChecker Require Import PCUICErrors PCUICWfEnv.
From MetaCoq.Erasure Require Import EAstUtils ErasureFunction ErasureCorrectness EPretty Extract.
From MetaCoq.Erasure Require ErasureFunction EOptimizePropDiscr EWcbvEval EDeps.

#[local] Instance extraction_checker_flags : checker_flags := 
  {| check_univs := true;
     prop_sub_type := false;
     indices_matter := false;
     lets_in_constructor_types := true |}.

(* This is the total erasure function +
  let-expansion of constructor arguments and case branches +
  shrinking of the global environment dependencies +
  the optimization that removes all pattern-matches on propositions. *)

Program Definition erase_template_program (p : Ast.Env.program) 
  (wfΣ : ∥ Typing.wf_ext (Ast.Env.empty_ext p.1) ∥)
  (wt : ∥ ∑ T, Typing.typing (Ast.Env.empty_ext p.1) [] p.2 T ∥)
  : (EAst.global_context * EAst.term) :=
  let Σ0 := (trans_global (Ast.Env.empty_ext p.1)).1 in
  let Σ := (PCUICExpandLets.trans_global_decls Σ0) in
  let wfΣ := map_squash (PCUICExpandLetsCorrectness.trans_wf_ext ∘
    (template_to_pcuic_env_ext (Ast.Env.empty_ext p.1))) wfΣ in
  let t := ErasureFunction.erase (build_wf_env_ext (empty_ext Σ) wfΣ) nil (PCUICExpandLets.trans (trans Σ0 p.2)) _ in
  let Σ' := ErasureFunction.erase_global (term_global_deps t) Σ (sq_wf_ext wfΣ) in
  (EOptimizePropDiscr.optimize_env Σ', EOptimizePropDiscr.optimize Σ' t).

Next Obligation.
  sq. destruct wt as [T Ht].
  cbn.
  set (Σ' := empty_ext _).
  exists (PCUICExpandLets.trans (trans (trans_global_decls p.1) T)).
  change Σ' with (PCUICExpandLets.trans_global (trans_global (Ast.Env.empty_ext p.1))).
  change (@nil (@BasicAst.context_decl term)) with (PCUICExpandLets.trans_local (trans_local (trans_global_decls p.1) [])).
  eapply (PCUICExpandLetsCorrectness.expand_lets_sound (cf := extraction_checker_flags)).
  apply (template_to_pcuic_typing (Ast.Env.empty_ext p.1));simpl. apply wfΣ0.
  apply Ht. Unshelve. now eapply template_to_pcuic_env.
Defined.

Import EOptimizePropDiscr.

(** The full correctness lemma of erasure from Template programs do λ-box *)

Lemma erase_template_program_correctness (wfl := EWcbvEval.default_wcbv_flags) {p : Ast.Env.program}
  (Σ := Ast.Env.empty_ext p.1)
  {wfΣ : ∥ Typing.wf_ext Σ ∥}
  {wt : ∥ ∑ T, Typing.typing (Ast.Env.empty_ext p.1) [] p.2 T ∥} {Σ' t'} :
  erase_template_program p wfΣ wt = (Σ', t') ->
  forall v, WcbvEval.eval p.1 p.2 v ->
  exists Σ'' v',
    PCUICExpandLets.trans_global (trans_global Σ) ;;; [] |- 
      PCUICExpandLets.trans (trans (trans_global Σ) v) ⇝ℇ v' /\ 
    ∥ EWcbvEval.eval (wfl := EWcbvEval.opt_wcbv_flags) Σ' t' (optimize Σ'' v') ∥.
Proof.
  unfold erase_template_program.
  intros [= <- <-] v ev.
  pose proof (erase_correct (PCUICExpandLets.trans_global (trans_global Σ))).
  set wftΣ : ∥ wf_ext (PCUICExpandLets.trans_global (trans_global Σ)) ∥ :=
    (map_squash (PCUICExpandLetsCorrectness.trans_wf_ext ∘ template_to_pcuic_env_ext (Ast.Env.empty_ext p.1)) wfΣ).
  specialize (H wftΣ (PCUICExpandLets.trans (trans (trans_global Σ) p.2)) (PCUICExpandLets.trans (trans (trans_global Σ) v))).
  set wtp : PCUICSafeLemmata.welltyped (PCUICExpandLets.trans_global (trans_global Σ)) [] 
    (PCUICExpandLets.trans (trans (trans_global Σ) p.2)) :=
    (erase_template_program_obligation_1 p wfΣ wt).
  set (t' := erase (build_wf_env_ext (empty_ext (PCUICExpandLets.trans_global (trans_global Σ)))
    wftΣ) [] (PCUICExpandLets.trans (trans (trans_global Σ) p.2)) wtp).
  set (deps := (term_global_deps _)).
  change (empty_ext (PCUICExpandLets.trans_global_decls (trans_global_decls p.1))) with
    (PCUICExpandLets.trans_global (trans_global Σ)) in *.
  specialize (H (erase_global deps (PCUICExpandLets.trans_global (trans_global Σ)) (sq_wf_ext wftΣ))).
  specialize (H _ deps wtp eq_refl).
  forward H. eapply Kernames.KernameSet.subset_spec. reflexivity.
  specialize (H eq_refl).
  destruct wt, wfΣ.
  have wfmid : wf (trans_global (Ast.Env.empty_ext p.1)).1.
  { now eapply template_to_pcuic_env. }
  forward H.
  { eapply PCUICExpandLetsCorrectness.trans_wcbveval.
    { destruct s as [T HT].
      eapply (PCUICClosedTyp.subject_closed (Γ := [])).
      unshelve apply (template_to_pcuic_typing (Ast.Env.empty_ext p.1) [] _ T);simpl; eauto.
      eapply w. }    
    unshelve eapply trans_wcbvEval; eauto.
    destruct s as [T HT].
    clear -w HT. now eapply TypingWf.typing_wf in HT. }  
  destruct H as [v' [Hv He]].
  sq.
  eapply EOptimizePropDiscr.optimize_correct in He.
  change (empty_ext (trans_global_decls p.1)) with (trans_global Σ).
  set (eΣ := erase_global _ _ _) in *. eexists; exists v'. split => //.
  constructor. exact He. eapply erase_global_closed.
  eapply (erases_closed _ []).
  2:eapply erases_erase.
  destruct s as [T HT].
  clear -w wftΣ HT; unshelve eapply (template_to_pcuic_typing _ []) in HT; eauto.
  unshelve eapply PCUICClosedTyp.subject_closed in HT.
  now eapply template_to_pcuic_env_ext. simpl in HT.
  now eapply PCUICExpandLetsCorrectness.trans_closedn.
Qed.

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
