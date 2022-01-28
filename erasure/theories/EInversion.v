(* Distributed under the terms of the MIT license. *)
From Coq Require Import Program.
From MetaCoq.Template Require Import config utils BasicAst AstUtils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICTyping
     PCUICSubstitution PCUICWcbvEval PCUICSR PCUICValidity.
From MetaCoq.Erasure Require Import EAstUtils ELiftSubst ETyping EWcbvEval
     Extract Prelim.

From Equations Require Import Equations.

(** * Inversion on eval *)

Notation type_Construct_inv := PCUICInversion.inversion_Construct.
Notation type_tFix_inv := PCUICInversion.inversion_Fix.

Derive Signature for Forall2.
Lemma eval_box_apps {wfl : WcbvFlags}:
  forall (Σ' : E.global_declarations) (e : E.term) (x x' : list E.term),
    All2 (eval Σ') x x' ->
    eval Σ' e EAst.tBox -> eval Σ' (EAst.mkApps e x) EAst.tBox.
Proof.
  intros Σ' e x H2. 
  revert e H2; induction x using rev_ind; cbn; intros; eauto.
  eapply All2_app_inv_l in X as (l1' & l2' & -> & H' & H2).
  depelim H2.
  specialize (IHx e _ H' H). simpl.
  rewrite mkApps_app. simpl. econstructor; eauto.
Qed.
