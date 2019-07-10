(* Distributed under the terms of the MIT license.   *)

(** * Universe Substitution lemmas for typing derivations. *)

From Coq Require Import Bool String List BinPos Compare_dec Arith Lia.
Require Import Coq.Program.Syntax Coq.Program.Basics.
From MetaCoq.Template Require Import utils config AstUtils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICLiftSubst
     PCUICUnivSubst PCUICTyping PCUICWeakeningEnv PCUICClosed
     PCUICReduction PCUICCumulativity PCUICWeakening.
Require Import ssreflect.

Lemma typing_subst_instance `{cf : checker_flags} :
  forall Σ : global_env_ext, wf Σ ->
  forall Γ, wf_local Σ Γ ->
  forall t T, Σ ;;; Γ |- t : T ->
    forall u univs,
      consistent_instance_ext (Σ.1,univs) (Σ.2) u ->
      (Σ.1,univs) ;;; PCUICUnivSubst.subst_instance_context u Γ |- PCUICUnivSubst.subst_instance_constr u t : PCUICUnivSubst.subst_instance_constr u T.
Proof.
  apply (typing_ind_env (fun Σ Γ t T =>
                           forall u univs,
      consistent_instance_ext (Σ.1,univs) (Σ.2) u ->
      (Σ.1,univs) ;;; _ |- PCUICUnivSubst.subst_instance_constr u t : PCUICUnivSubst.subst_instance_constr u T)); intros; cbn -[PCUICUnivSubst.subst_instance_constr] in *.
Admitted.
