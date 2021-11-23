(* Distributed under the terms of the MIT license. *)
From Coq Require Import Program ssreflect.
From MetaCoq.Template Require Import config utils uGraph Pretty Environment Typing WcbvEval.
Set Warnings "-notation-overridden".
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping
     TemplateToPCUIC TemplateToPCUICCorrectness TemplateToPCUICWcbvEval.
Set Warnings "+notation-overridden".
From MetaCoq.SafeChecker Require Import PCUICErrors.
From MetaCoq.Erasure Require Import EAstUtils ErasureFunction ErasureCorrectness EPretty Extract.
From MetaCoq.Erasure Require ErasureFunction EOptimizePropDiscr EWcbvEval EDeps.

#[global]
Existing Instance extraction_checker_flags.

(* This is the total erasure function + the optimization that removes all 
  pattern-matches on propositions. *)

Program Definition erase_template_program (p : Ast.Env.program) 
  (wfΣ : ∥ Typing.wf_ext (Ast.Env.empty_ext p.1) ∥)
  (wt : ∥ ∑ T, Typing.typing (Ast.Env.empty_ext p.1) [] p.2 T ∥)
  : (EAst.global_context * EAst.term) :=
  let Σ := (trans_global (Ast.Env.empty_ext p.1)).1 in
  let wfΣ := map_squash (template_to_pcuic_env_ext (Ast.Env.empty_ext p.1)) wfΣ in
  let t := ErasureFunction.erase (empty_ext Σ) wfΣ nil (trans Σ p.2) _ in
  let Σ' := ErasureFunction.erase_global (term_global_deps t) Σ (sq_wf_ext wfΣ) in
  (EOptimizePropDiscr.optimize_env Σ', EOptimizePropDiscr.optimize Σ' t).

Next Obligation.
  sq. destruct wt as [T Ht].
  set (Σ' := empty_ext (trans_global_decls _)).
  exists (trans Σ'.1 T).
  change (@nil (@BasicAst.context_decl term)) with (trans_local Σ'.1 []).
  apply (template_to_pcuic_typing (Ast.Env.empty_ext p.1));simpl. apply wfΣ0.
  apply Ht.
Defined.

Import EOptimizePropDiscr.

Lemma erase_template_program_correctness (wfl := EWcbvEval.default_wcbv_flags) {p : Ast.Env.program}
  (Σ := Ast.Env.empty_ext p.1)
  {wfΣ : ∥ Typing.wf_ext Σ ∥}
  {wt : ∥ ∑ T, Typing.typing (Ast.Env.empty_ext p.1) [] p.2 T ∥} {Σ' t'} :
  erase_template_program p wfΣ wt = (Σ', t') ->
  forall v, WcbvEval.eval p.1 [] p.2 v ->
  exists Σ'' v',
    (trans_global Σ) ;;; [] |- (trans (trans_global Σ) v) ⇝ℇ v' /\ 
    ∥ EWcbvEval.eval (wfl := EWcbvEval.opt_wcbv_flags) Σ' t' (optimize Σ'' v') ∥.
Proof.
  unfold erase_template_program.
  intros [= <- <-] v ev.
  pose proof (erase_correct (trans_global Σ)).
  set wftΣ : ∥ wf_ext (trans_global Σ) ∥ :=
    (map_squash (template_to_pcuic_env_ext (Ast.Env.empty_ext p.1)) wfΣ).
  specialize (H wftΣ (trans (trans_global Σ) p.2) (trans (trans_global Σ) v)).
  set wtp : PCUICSafeLemmata.welltyped (trans_global Σ) [] (trans (trans_global Σ) p.2) :=
    (erase_template_program_obligation_1 p wfΣ wt).
  set (t' := erase (trans_global Σ) wftΣ [] (trans (trans_global Σ) p.2) wtp).
  set (deps := (term_global_deps t')).
  specialize (H (erase_global deps (trans_global Σ) (sq_wf_ext wftΣ)) _ deps wtp eq_refl).
  forward H. eapply Kernames.KernameSet.subset_spec. reflexivity.
  specialize (H eq_refl).
  destruct wt, wfΣ.
  forward H.
  { unshelve eapply trans_wcbvEval; eauto. exact extraction_checker_flags.
    apply w.
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
  clear -w wftΣ HT; eapply (template_to_pcuic_typing _ []) in HT; eauto.
  unshelve eapply PCUICClosed.subject_closed in HT.
  now eapply template_to_pcuic_env_ext. eauto.
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
