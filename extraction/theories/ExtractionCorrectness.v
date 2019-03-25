(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import config utils monad_utils BasicAst AstUtils.
From PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICTyping PCUICWeakening PCUICSubstitution PCUICChecker PCUICRetyping PCUICMetaTheory PCUICWcbvEval.
From TemplateExtraction Require Import EAst ELiftSubst ETyping EWcbvEval Extract.
Require Import String.
Local Open Scope string_scope.
Set Asymmetric Patterns.
Import MonadNotation.

Existing Instance config.default_checker_flags.
Module PA := PCUICAst.
Module P := PCUICWcbvEval.


Inductive extr_pre (Σ : PA.global_context) t T :=
  { extr_typed : Σ ;;; [] |- t : T;
    extr_env_axiom_free : axiom_free (fst Σ) }.

Lemma is_type_or_proof `{F:Fuel} :
  env_prop (fun Σ Γ t T => Γ = [] -> { U & (type_of Σ [] t = Checked U) * cumul Σ [] U T }%type).
Proof.
  eapply typing_ind_env; simpl; intros **; try rewrite HeqΓ in *. rewrite H0 in *.

  + rewrite H. eexists. split; eauto.
    eapply cumul_refl. eapply eq_term_leq_term. apply eq_term_refl.

  + eexists; split; eauto. admit.

  + admit.
 (* + destruct IHX1 as [T [HT HTs]]. *)
 (*    destruct IHX2 as [U [HU HUs]]. *)
 (*    unfold type_of_as_sort. *)
 (*    rewrite HT. simpl. *)
 (*    destruct reduce_to_sort eqn:Heq'. *)
 (*    rewrite HU. *)
 (*    destruct (reduce_to_sort _ _ U) eqn:Heq''. *)
 (*    eexists; split; eauto. *)
 (*    admit. *)
 (*    admit. *)
 (*    admit. *)

Admitted.

Theorem erasure_correct : erasure_correctness.
Proof.
  intros Σ t T pre v.
  induction 1 using PCUICWcbvEval.eval_evals_ind; intros fuel Σ' t' Ht' HΣ'.

  simpl in Ht'.
  destruct Extract.is_type_or_proof eqn:Heq.
  destruct a0. injection Ht'. intros <-.
Admitted.