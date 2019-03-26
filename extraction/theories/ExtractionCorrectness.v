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

Ltac inv H := inversion H; subst; clear H.

Tactic Notation "destruct" "?" :=  let E := fresh "E" in
                                  match goal with [ |- context[match ?X with _ => _ end]] => destruct X eqn:E | [ H : context[match ?X with _ => _ end] |- _] => destruct X eqn:E end.

Lemma eval_is_type `{Fuel} (Σ : PCUICAst.global_context) (t v : PCUICAst.term) :
  PCUICWcbvEval.eval Σ [] t v -> Extract.is_type_or_proof Σ [] t = Extract.is_type_or_proof Σ [] v.
Proof.
  unfold Extract.is_type_or_proof.
Admitted.

Lemma is_type_eval `{Fuel} (Σ : PCUICAst.global_context) (t : PCUICAst.term) :
  Extract.is_type_or_proof Σ [] t = Checked true -> extract Σ [] t = Checked E.tBox.
Proof.
  intros H1.
  destruct t; simpl; try rewrite H1; try reflexivity.
  all: inversion H1.  
Qed.

Theorem erasure_correct : erasure_correctness.
Proof.
  intros Σ t T pre v. 
  induction 1 using PCUICWcbvEval.eval_evals_ind; intros fuel Σ' t' Ht' HΣ'.

  - simpl in Ht'.
    destruct Extract.is_type_or_proof eqn:Heq.
    destruct a0.
    + inv Ht'.
      exists tBox. split. 2: specialize (eval_box Σ' []); cbn; eauto.
      eapply is_type_eval. erewrite <- eval_is_type; eauto.
      econstructor; eauto.
    + destruct (extract Σ [] f) eqn:Ef; try congruence.
      destruct (extract Σ [] a) eqn:Ea; try congruence.
      inv Ht'.
      * eapply IHX1 in Ef as (? & ? & ?) ; eauto.
        eapply IHX2 in Ea as (? & ? & ?) ; eauto.

        simpl in H. erewrite <- eval_is_type in H.
        2:eauto.
        destruct ?; try now cbn in *; congruence.
        destruct a2.
        -- admit.
        -- destruct ?; try congruence.
           inv H. edestruct IHX3 as (? & ? & ?). admit.
           admit. eauto. exists x. split; eauto.
        -- inv pre. econstructor; eauto. 
        -- admit.
    + congruence.
  - simpl in Ht'.
    destruct Extract.is_type_or_proof eqn:Heq. destruct a; try congruence.
    + inv Ht'.
      exists tBox. split. 2: specialize (eval_box Σ' []); cbn; eauto.
      eapply is_type_eval. erewrite <- eval_is_type; eauto.
      econstructor; eauto.
    + admit.
    + congruence .
  - cbn in isdecl. inv isdecl.    
  - cbn in isdecl. inv isdecl.    
  - simpl in Ht'. destruct Extract.is_type_or_proof eqn:Heq.
    destruct a.
    + inv Ht'.
      exists tBox. split. 2: specialize (eval_box Σ' []); cbn; eauto.
      eapply is_type_eval. erewrite <- eval_is_type; eauto.
      econstructor; eauto.
    + destruct extract eqn:He; try congruence.
      destruct is_box eqn:Ea.
      * destruct a; inversion Ea; clear Ea.
        admit.
             
      * destruct monad_map eqn:Em; try congruence.
        inv Ht'.
        econstructor. econstructor.
        admit.
        admit.
    + congruence.
  - admit.
  - simpl in Ht'. destruct Extract.is_type_or_proof eqn:Heq. destruct a.
    + inv Ht'. exists tBox. split. 2: specialize (eval_box Σ' []); cbn; eauto.
      eapply is_type_eval. erewrite <- eval_is_type. 2:eapply X.
      admit.
    + inv Ht'. admit.
    + congruence.
  - simpl in Ht'. destruct Extract.is_type_or_proof eqn:Heq. destruct a.
    + inv Ht'. exists tBox. split. 2: specialize (eval_box Σ' []); cbn; eauto.
      eapply is_type_eval. erewrite <- eval_is_type. 2:eapply X2.
      admit.
    + destruct ?; try congruence. inv Ht'.
      eapply IHX1 in E as (? & ? & ?); eauto.
      eexists. split. admit. econstructor. admit.
      admit. admit.
    + congruence.
  - simpl in Ht'. destruct Extract.is_type_or_proof eqn:Heq. destruct a.
    + inv Ht'. exists tBox. split. 2: specialize (eval_box Σ' []); cbn; eauto.
      simpl. rewrite Heq. reflexivity.
    + destruct ?; try congruence.
      inv Ht'. eexists. split. 2:econstructor.
      simpl. now rewrite Heq, E.
    + congruence.
  - simpl in Ht'. destruct Extract.is_type_or_proof eqn:Heq. destruct a.
    + inv Ht'. exists tBox. split. 2: specialize (eval_box Σ' []); cbn; eauto.
      simpl. erewrite <- eval_is_type, Heq. 2:econstructor; eauto. reflexivity.
    + inv Ht'. exists tBox. split. 2: specialize (eval_box Σ' []); cbn; eauto.
      simpl. erewrite <- eval_is_type, Heq. 2:econstructor; eauto. reflexivity.
    + congruence. 
  - simpl in Ht'. destruct Extract.is_type_or_proof eqn:Heq. destruct a.
    + inv Ht'. exists tBox. split. 2: specialize (eval_box Σ' []); cbn; eauto. 
      simpl. rewrite Heq. reflexivity.
    + inv Ht'.  exists tBox. split. 2: specialize (eval_box Σ' []); cbn; eauto.
      simpl. rewrite Heq. reflexivity.
    + congruence.
  - admit.
  - simpl in Ht'. destruct Extract.is_type_or_proof eqn:Heq. destruct a.
    + inv Ht'. exists tBox. split. 2: specialize (eval_box Σ' []); cbn; eauto. 
      simpl. rewrite Heq. reflexivity.
    + inv Ht'. eexists. split.
      simpl. rewrite Heq. reflexivity. 
        specialize (eval_constr Σ
    + congruence.

    cbn in Ht'.
    destruct nth_error eqn:En.
    destruct is_arity eqn:Ea.
    inversion Ht'; subst.
    + econstructor. specialize (eval_box Σ' []). cbn. eauto.
    + destruct type_of eqn:Et.
      destruct reduce_to_sort eqn:Er.
      destruct is_prop_sort. inversion Ht'; subst.
      unfold reduce_to_sort in Er. destruct a; inversion Er.

  - cbn in Ht'.
    destruct nth_error eqn:En.
    destruct is_arity eqn:Ea.
    inversion Ht'; subst.
    + econstructor. specialize (eval_box Σ' []). cbn. eauto.
    + destruct type_of eqn:Et.
      destruct reduce_to_sort eqn:Er.
      destruct is_prop_sort. inversion Ht'; subst.
      unfold reduce_to_sort in Er. destruct a; inversion Er.

        
      
Admitted.
