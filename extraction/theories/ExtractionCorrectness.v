(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import config utils monad_utils BasicAst AstUtils.
From PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICTyping PCUICWeakening PCUICSubstitution PCUICChecker PCUICRetyping PCUICMetaTheory PCUICWcbvEval PCUICSR.
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

Tactic Notation "destruct" "?" :=
  let E := fresh "E" in
  match goal with
    [ |- context[match ?X with _ => _ end]] => destruct X eqn:E
  | [ H : context[match ?X with _ => _ end] |- _] => destruct X eqn:E
  end.

Lemma eval_is_type `{Fuel} (Σ : PCUICAst.global_context) (t v : PCUICAst.term) :
  PCUICWcbvEval.eval Σ [] t v -> Extract.is_type_or_proof Σ [] t = Checked true -> Extract.is_type_or_proof Σ [] v = Checked true.
Proof.
  unfold Extract.is_type_or_proof.
Admitted.

Lemma is_type_extract `{Fuel} (Σ : PCUICAst.global_context) Γ (t : PCUICAst.term) :
  Extract.is_type_or_proof Σ Γ t = Checked true -> extract Σ Γ t = Checked E.tBox.
Proof.
  intros H1.
  destruct t; simpl; try rewrite H1; try reflexivity.
  all: inversion H1.  
Qed.

(* Lemma is_proof_app `{Fuel} Σ f a : *)
(*   Extract.is_type_or_proof Σ [] f = Extract.is_type_or_proof Σ [] (PCUICAst.tApp f a). *)
(* Proof. *)
(*   unfold Extract.is_type_or_proof. cbn [type_of]. destruct type_of as [T|]; try reflexivity. *)
(*   unfold bind at 1 4. cbn -[bind]. *)
(*   unfold is_arity at 1.  *)
  
(* Admitted. *)


Theorem subject_reduction_eval : forall (Σ : PCUICAst.global_context) Γ t u T,
  wf Σ -> Σ ;;; Γ |- t : T -> PCUICWcbvEval.eval Σ Γ t u -> Σ ;;; Γ |- u : T.
Proof.
  intros * wfΣ Hty Hred % wcbeval_red. eapply subject_reduction; eauto.
Qed.

Lemma extract_subst1 
  (Σ : PCUICAst.global_context) (na : name) (t b a' : PCUICAst.term) (fuel : Fuel) (a0 : E.term) :
    extract Σ [PCUICAst.vass na t] b = Checked a0 ->
    forall vea : E.term,
      extract Σ [] a' = Checked vea -> extract Σ [] (PCUICLiftSubst.subst1 a' 0 b) = Checked (a0 {0 := vea}).
Proof.
  intros.
Admitted.

Lemma extract_subst1_vdef
      (Σ : PCUICAst.global_context) (na : name) (t b a' : PCUICAst.term) (fuel : Fuel) (a0 : E.term) a'' :
  PCUICWcbvEval.eval Σ [] a'' a' ->
    extract Σ [PCUICAst.vdef na a'' t] b = Checked a0 ->
    forall vea : E.term,
      extract Σ [] a' = Checked vea -> extract Σ [] (PCUICLiftSubst.subst1 a' 0 b) = Checked (a0 {0 := vea}).
Proof.
  intros.
Admitted.


Lemma is_type_or_proof_lambda `{Fuel} Σ Γ na t b :
  Extract.is_type_or_proof Σ Γ (PCUICAst.tLambda na t b) = Checked true ->
  Extract.is_type_or_proof Σ (Γ ,, PCUICAst.vass na t) b = Checked true.
Admitted.

Lemma is_type_subst `{Fuel} (Σ : PCUICAst.global_context) (na : name) (t b a' : PCUICAst.term) :
  Extract.is_type_or_proof Σ ([],, PCUICAst.vass na t) b = Checked true ->
  Extract.is_type_or_proof Σ [] (PCUICLiftSubst.subst1 a' 0 b) = Checked true.
Proof.
Admitted.

Lemma mkApps_snoc a l b :
  PCUICAst.mkApps a (l ++ [b]) = PCUICAst.tApp (PCUICAst.mkApps a l) b.
Proof.
  revert a; induction l; cbn; congruence.
Qed.

Lemma extract_Apps `{Fuel} Σ Γ a args x :
  extract Σ Γ (PCUICAst.mkApps a args) = Checked x -> { e : E.term & (extract Σ Γ a = Checked e) * (All (fun a => { e : _ & extract Σ Γ a = Checked e}) args)}%type.
Proof.
Admitted.
  
Theorem erasure_correct : erasure_correctness.
Proof.
  intros Σ t T pre v H. revert T pre.
  induction H using PCUICWcbvEval.eval_evals_ind; intros T pre fuel Σ' t' Ht' HΣ'.

  - simpl in Ht'.
    destruct Extract.is_type_or_proof eqn:Heq.
    destruct a0.
    + inv Ht'.
      exists tBox. split. 2:repeat econstructor.
      eapply is_type_extract. eapply eval_is_type. 2:eauto. econstructor;eauto.
    + destruct (extract Σ [] f) as [ ef | ] eqn:Ef ; try congruence.
      destruct (extract Σ [] a) as [ ea | ] eqn:Ea; try congruence.
      inv Ht'. 
      inv pre. edestruct (type_mkApps_inv Σ [] f [a] T) as (? & U & [? ?] & ?); eauto. 
      inv t1. inv X2. pose proof (subject_reduction_eval _ [] _ _ _ extr_env_wf t0 H).
      eapply type_Lambda_inv in X2 as (? & ? & [? ?] & ?).
      
      eapply IHeval1 in Ef as (vef & ? & ?) ; eauto.
      eapply IHeval2 in Ea as (vea & ? & ?) ; eauto.

      simpl in H2. destruct ?; try now cbn in *; congruence.
      destruct a0.
      * inv H2. eapply is_type_or_proof_lambda in E.
        edestruct (IHeval3) as (? & ? & ?).
        -- econstructor; eauto. eapply substitution0. eauto. eauto. eapply subject_reduction_eval; try eapply H0; eauto. 
           eapply cumul_trans in X0. 2:eauto. eapply cumul_Prod_inv in X0 as []. econstructor. eauto. eauto. eapply c1.
        -- eapply extract_subst1. eapply is_type_extract. eauto. eauto.
        -- eauto.
        -- exists tBox. cbn in H6. split. 2: eapply eval_box; eauto.
           eapply is_type_extract. eapply eval_is_type. eauto.
           eapply is_type_subst. eauto.
      * destruct ?; try congruence.
        inv H2. edestruct IHeval3 as (? & ? & ?).
        -- econstructor; eauto.
           eapply substitution0. eauto. eauto. eapply subject_reduction_eval; try eapply H0; eauto. 
           eapply cumul_trans in X0. 2:eauto. eapply cumul_Prod_inv in X0 as []. 
           econstructor. eauto. eauto. eapply c1. 
        -- shelve.
        -- eauto.
        -- exists x2. split. eauto. econstructor. eauto. exact H5. eauto.
           Unshelve. shelve. shelve. eapply extract_subst1; eauto.
      * econstructor; eauto.
      * econstructor; eauto.
    + congruence.
  - simpl in Ht'.
    destruct Extract.is_type_or_proof eqn:Heq. destruct a; try congruence.
    + inv Ht'.  exists tBox. split. 2: repeat econstructor.
      eapply is_type_extract. eapply eval_is_type. 2:eauto.
      econstructor; eauto.
    + destruct (extract _ _ b0) as [ eb0 | ] eqn:Eb0; try congruence.
      destruct (extract _ _ b1) as [ eb1 | ] eqn:Eb1; try congruence.
      inv Ht'. inv pre. eapply type_tLetIn_inv in extr_typed0 as (? & U & [[] ?] & ?); eauto.

      eapply IHeval1 in Eb0 as (veb0 & ? & ?). 3:eauto.
      eapply extract_subst1_vdef in Eb1. 2:eauto. 2:eauto.
      eapply IHeval2 in Eb1 as (veb1 & ? & ?). 3:eauto.
      -- exists veb1. split. eauto. econstructor; eauto.
      -- econstructor; eauto. eapply substitution_let; eauto.
         eapply context_conversion. 3: eassumption. all:eauto.
         econstructor. econstructor. econstructor 3. eapply subject_reduction_eval; eauto.
         admit.         
      -- econstructor; eauto.
    + congruence.
  - cbn in isdecl. inv isdecl.    
  - cbn in isdecl. inv isdecl.    
  - simpl in Ht'. destruct Extract.is_type_or_proof eqn:Heq.
    destruct a.
    + inv Ht'. exists tBox. split. 2: repeat econstructor.
      eapply is_type_extract. eapply eval_is_type. 2:eauto.
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
    + inv Ht'. exists tBox. split. 2: repeat econstructor.
      eapply is_type_extract. eapply eval_is_type. 2:eapply Heq.
      econstructor; eauto.
    + inv Ht'. inv pre. edestruct IHeval as (? & ? & ?).
      * econstructor; eauto. admit.
      * shelve.
      * eauto.
      * exists x. split. eauto. econstructor. 3:eauto. admit. admit.
    + congruence.
  - simpl in Ht'. destruct Extract.is_type_or_proof eqn:Heq. destruct a0.
    + inv Ht'. exists tBox. split. 2:repeat econstructor.
      eapply is_type_extract. eapply eval_is_type. 2:eapply Heq.
      econstructor; eauto.
    + destruct ?; try congruence. inv Ht'. inv pre.

      eapply IHeval1 in E as (? & ? & ?); eauto. clear IHeval1.
      eapply extract_Apps in H3 as (? & ? & ?).
      eapply nth_error_all in a1 as [] ; eauto.
      eapply IHeval2 in e0 as (? & ? & ?).
      * exists x2. split. eauto. econstructor.
        eapply eval_constr.
        

      
      induction args using rev_ind.
      * destruct pars; inv H0. destruct arg; inv H6.
      * rewrite mkApps_snoc in H3.
        simpl in H3.
        destruct ?. destruct a1.
        -- inv H3. 
        
      
      
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
      admit.
    + congruence.
  - simpl in Ht'. admit.      
Admitted.
