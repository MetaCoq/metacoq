(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Lia.
From MetaCoq.Template Require Import config utils monad_utils BasicAst AstUtils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICTyping
     PCUICWeakening PCUICSubstitution PCUICChecker PCUICRetyping PCUICMetaTheory
     PCUICWcbvEval PCUICSR PCUICValidity.
From MetaCoq.Erasure Require Import EAst EAstUtils ELiftSubst ETyping EWcbvEval Extract Prelim.

From Equations Require Import Equations.

Local Open Scope list_scope.
Set Asymmetric Patterns.
Import MonadNotation.

Module PA := PCUICAst.
Module P := PCUICWcbvEval.

Local Existing Instance default_checker_flags.

(** ** Inversion on eval *)


Notation type_Construct_inv := PCUICInversion.inversion_Construct.
Notation type_tFix_inv := PCUICInversion.inversion_Fix.

Derive Signature for Forall2.
Lemma eval_box_apps:
  forall (Σ' : list E.global_decl) (e : E.term) (x x' : list E.term),
    Forall2 (eval Σ') x x' ->
    eval Σ' e tBox -> eval Σ' (mkApps e x) tBox.
Proof.
  intros Σ' e x H2. revert e H2; induction x using rev_ind; cbn; intros; eauto using eval.
  eapply Forall2_app_inv_l in H as [l1' [l2' [H [H' eq]]]]. subst H2.
  depelim H'.
  specialize (IHx e _ H H0). simpl.
  rewrite mkApps_app. simpl. econstructor; eauto.
Qed.
