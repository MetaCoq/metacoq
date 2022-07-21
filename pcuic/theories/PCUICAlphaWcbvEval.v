(* Distributed under the terms of the MIT license. *)
From Coq Require Import ssreflect ssrbool CRelationClasses CMorphisms.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTactics
     PCUICLiftSubst PCUICTyping PCUICWeakeningConv PCUICWeakeningTyp 
     PCUICCumulativity PCUICEquality PCUICClosedTyp
     PCUICConversion PCUICContextConversion PCUICContextConversionTyp 
     PCUICValidity PCUICArities PCUICSpine
     PCUICInductives PCUICInductiveInversion PCUICOnFreeVars
     PCUICWellScopedCumulativity PCUICGuardCondition PCUICWcbvEval PCUICUnivSubstitutionConv.

From Equations Require Import Equations.


Implicit Types cf : checker_flags.

#[local] Hint Constructors eval : core.

Section fixR.

Variable R1 : (Universe.t -> Universe.t -> Prop).
Variable R2 : (Universe.t -> Universe.t -> Prop).
Context {HR1 : Reflexive R1}.
Existing Instance HR1.
Context {HR2 : Reflexive R2}.
Existing Instance HR2.
Context {Sub : RelationClasses.subrelation R1 R2}.

Lemma alpha_csubst x x' b b' n m :
  closed x -> closed x' ->
  eq_term_upto_univ_napp empty_global_env R1 R1 0 x x' ->
  eq_term_upto_univ_napp empty_global_env R1 R2 n b b' ->
  eq_term_upto_univ_napp empty_global_env R1 R2 n (PCUICCSubst.csubst x m b) (PCUICCSubst.csubst x' m b').
Proof.
  intros.
  rewrite !PCUICCSubst.closed_subst => //.
  eapply eq_term_upto_univ_substs => //.
  repeat econstructor => //.
Qed.    

End fixR.

Section fixR.

Variable R1 : (Universe.t -> Universe.t -> Prop).
Variable R2 : (Universe.t -> Universe.t -> Prop).
Context {HR1 : Reflexive R1}.
Existing Instance HR1.
Context {HR2 : Reflexive R2}.
Existing Instance HR2.
Context {Sub : RelationClasses.subrelation R1 R2}.
Context {HUniv1: SubstUnivPreserving R1}.
Context {HUniv2: SubstUnivPreserving R2}.

Lemma impl1 x y n :
  eq_term_upto_univ_napp empty_global_env R1 R1 n x y ->
  eq_term_upto_univ_napp empty_global_env R1 R2 n x y.
Proof.
  eapply eq_term_upto_univ_empty_impl. 1: reflexivity. 1-2: eauto.
Qed.

Hint Resolve impl1 : core.


Ltac rtoProp :=
  repeat match goal with
  | H : is_true (_ && _) |- _ => let H1 := fresh H in let H2 := fresh H in apply andb_and in H as [H1 H2]
  | |- context [is_true (_ && _)] => rewrite andb_and
  end.

Lemma eq_context_closedn :
  forall (l l0 : list context_decl) (n : nat),
  closedn_ctx n l0 -> eq_context_gen eq eq l l0 -> closedn_ctx n l.
Proof.
  induction 2; cbn; eauto; cbn in *; rtoProp.
  eapply All2_fold_length in X as ->.
  split. eauto. 
  invs p; cbn in *; unfold closed_decl in *; rtoProp; repeat split; cbn; eauto.
Qed.

Lemma eq_context_closedn' :
  forall (l l0 : list context_decl) (n : nat),
  closedn_ctx n l0 -> eq_context_gen eq eq l0 l -> closedn_ctx n l.
Proof.
  induction 2; cbn; eauto; cbn in *; rtoProp.
  eapply All2_fold_length in X as <-.
  split. eauto. 
  invs p; cbn in *; unfold closed_decl in *; rtoProp; repeat split; cbn; eauto.
Qed.


Lemma eq_term_upto_univ_napp_closedn n t t' :
  eq_term_upto_univ_napp empty_global_env R1 R2 n t t' ->
  forall k, closedn k t' -> closedn k t.
Proof.
  induction t using PCUICInduction.term_forall_list_ind in t', n |- *; intros H; depelim H; cbn; intros; rtoProp; eauto.
  all: try now solve_all.
  - destruct X as (? & ? & ?). destruct e as (? & ? & ? & ?). repeat split; eauto.
    + unfold test_predicate_k in *. rtoProp. eapply All2_length in a2 as l1. eapply All2_fold_length in a3 as l2. repeat split.
      * solve_all.
      * rewrite l1. eapply eq_context_closedn; eauto.        
      * rewrite l2. eauto. 
    + solve_all. unfold test_branch_k in *. rtoProp. eapply All2_length in a2 as l1. eapply All2_fold_length in a3 as l2. repeat split.
      * rewrite l1. eapply eq_context_closedn; eauto.       
      * eapply b1; eauto. eapply All2_fold_length in a0 as ->. eauto.
  - eapply All2_length in a as l. solve_all. unfold test_def in *. rtoProp. split.
    + eapply a; eauto.
    + eapply b1; eauto. rewrite l. eauto.
  - eapply All2_length in a as l. solve_all.  unfold test_def in *. rtoProp; split; eauto. 
    rewrite l. eauto.
Qed.  

Lemma eq_term_upto_univ_napp_closedn' n t t' :
  eq_term_upto_univ_napp empty_global_env R1 R2 n t t' ->
  forall k, closedn k t -> closedn k t'.
Proof.
  induction t using PCUICInduction.term_forall_list_ind in t', n |- *; intros H; depelim H; cbn; intros; rtoProp; eauto.
  all: try now solve_all.
  - destruct X as (? & ? & ?). destruct e as (? & ? & ? & ?). repeat split; eauto.
    + unfold test_predicate_k in *. rtoProp. eapply All2_length in a2 as l1. eapply All2_fold_length in a3 as l2. repeat split.
      * solve_all.
      * rewrite <- l1. eapply eq_context_closedn'; eauto.        
      * rewrite <- l2. eauto. 
    + solve_all. unfold test_branch_k in *. rtoProp. eapply All2_length in a2 as l1. eapply All2_fold_length in a3 as l2. repeat split.
      * rewrite <- l1. eapply eq_context_closedn'; eauto.        
      * eapply b; eauto. eapply All2_fold_length in a as <-. eauto.
  - eapply All2_length in a as l. solve_all. unfold test_def in *. rtoProp. split.
    + eapply a1; eauto.
    + eapply b; eauto. rewrite <- l. eauto.
  - eapply All2_length in a as l. solve_all. unfold test_def in *. rtoProp; split; eauto. 
    rewrite <- l. eauto.
Qed.

Local Hint Resolve eq_term_upto_univ_napp_closedn eq_term_upto_univ_napp_closedn' eval_closed : core.

Lemma alpha_eval {cf} Σ n t v t' :
  wf_ext Σ ->
  closed t ->
  eval Σ t v ->
  eq_term_upto_univ_napp empty_global_env R1 R2 n t t' ->
  ∑ v', eq_term_upto_univ_napp empty_global_env R1 R1 0 v v' × eval Σ t' v'.
Proof.
  intros Hwf Hcl He Ha.
  induction He in t', Hcl, Ha, n |- *; try (destruct t'; invs Ha; []); cbn in Hcl; rtoProp. 
  - edestruct IHHe1 as (? & ? & ?); eauto. invs e.
    edestruct IHHe2 as (? & ? & ?); eauto.
    edestruct IHHe3 as (? & ? & ?). rewrite PCUICCSubst.closed_subst. 1:eauto.
    1: eapply PCUICClosed.closedn_subst0. cbn. eapply andb_and. split; eauto.
    cbn. eapply eval_closed in e0; eauto. cbn in e0. rtoProp. eauto.  
    eapply alpha_csubst. 4-5: eauto. eauto. 1-2: eapply eval_closed; [ | | eauto]; eauto.
    eauto.
  - edestruct IHHe1 as (? & ? & ?); eauto.
    edestruct IHHe2 as (? & ? & ?). rewrite PCUICCSubst.closed_subst; eauto. eapply PCUICClosed.closedn_subst0; cbn. rtoProp; eauto. eauto. 
    eapply alpha_csubst. 4,5: eauto. all:eauto.
  - edestruct IHHe as (? & ? & ?). rewrite PCUICClosed.closedn_subst_instance. eapply declared_constant_closed_body; eauto.
    eapply impl1. eapply eq_term_upto_univ_subst_instance; eauto. reflexivity.
    eauto.
  - edestruct IHHe1 as (? & ? & ?); eauto.
    edestruct IHHe2 as (? & ? & ?). eapply eval_closed in He1 as Hc1; eauto. rewrite PCUICClosed.closedn_mkApps in Hc1. rtoProp. eapply PCUICClosed.closedn_subst0; cbn; eauto.
    {  solve_all. eapply All_skipn. solve_all. }
    {
      eapply PCUICClosed.closedn_subst0; cbn; eauto. solve_all. admit.
      len. admit.
    }
    eapply eq_term_upto_univ_substs; eauto. admit. admit.
    eexists. split. eauto.
    admit.
  - edestruct IHHe1 as (? & ? & ?); eauto.
    eapply eq_term_upto_univ_mkApps_l_inv in e1 as (? & ? & [] & ->). invs e1.
    eapply All2_nth_error_Some in a0 as a1; eauto. destruct a1 as (? & ? & ?).
    edestruct IHHe2 as (? & ? & ?); eauto.
    { eapply eval_closed in He1; eauto. rewrite PCUICClosed.closedn_mkApps in He1. rtoProp. solve_all.
    eapply All2_nth_error_Some in a0 as (? & ? & ? & ?); eauto. }
    eexists. split. eauto. econstructor; try eassumption. 
    rewrite <- e. symmetry. now eapply All2_length.
  - edestruct IHHe1 as (? & ? & ?); eauto.
    eapply eq_term_upto_univ_mkApps_l_inv in e0 as (? & ? & [] & ->). invs e0.
    unfold cunfold_fix in *. destruct nth_error eqn:Enth; try congruence.
    eapply All2_nth_error_Some in X1 as a1; eauto. destruct a1 as (? & ? & ((? & ?) & ?) & ?).
    edestruct IHHe2 as (? & ? & ?); eauto. invs e.
    edestruct IHHe3 as (? & ? & ?). { cbn.
      eapply eval_closed in He1; eauto. rewrite PCUICClosed.closedn_mkApps in He1. rtoProp.
      rewrite PCUICClosed.closedn_mkApps; rtoProp; repeat split; eauto.
      erewrite <- closed_fix_substl_subst_eq; eauto.
      eapply PCUICClosed.closedn_subst0. cbn in He0. solve_all. admit.
      cbn in He0. eapply forallb_nth_error in He0. setoid_rewrite Enth in He0. cbn in He0.
      unfold test_def in He0. rtoProp. revert He5. len.
    }
    econstructor; eauto.
    eapply eq_term_upto_univ_napp_mkApps; eauto.
    admit. eexists. split. eauto. eapply eval_fix; eauto. unfold cunfold_fix. rewrite e0. repeat f_equal. 
    eapply All2_length in a0; lia.
  - edestruct IHHe1 as (? & ? & ?); eauto.
    eapply eq_term_upto_univ_mkApps_l_inv in e0 as (? & ? & [] & ->). invs e0.
    unfold cunfold_fix in *. destruct nth_error eqn:Enth; try congruence.
    eapply All2_nth_error_Some in X1 as a1; eauto. destruct a1 as (? & ? & ((? & ?) & ?) & ?).
    edestruct IHHe2 as (? & ? & ?); eauto. invs e.
    eexists; split. 
    2:{ eapply eval_fix_value.
        3:{ unfold cunfold_fix. setoid_rewrite e0. reflexivity. }
        all: eauto. 
        eapply All2_length in a0. lia. }
    econstructor; eauto.
    eapply eq_term_upto_univ_napp_mkApps; eauto. econstructor. solve_all.
  - edestruct IHHe1 as (? & ? & ?); eauto.
    eapply eq_term_upto_univ_mkApps_l_inv in e0 as (? & ? & [] & ->). invs e0.
    unfold cunfold_cofix in *. destruct nth_error eqn:Enth; try congruence.
    eapply All2_nth_error_Some in X2 as a1; eauto. destruct a1 as (? & ? & ((? & ?) & ?) & ?). invs e.
    edestruct IHHe2 as (? & ? & ?). { cbn. rtoProp. repeat split; eauto. rewrite PCUICClosed.closedn_mkApps.
      eapply eval_closed in He1; eauto.  rewrite PCUICClosed.closedn_mkApps in He1. rtoProp. split; eauto.
      erewrite <- closed_cofix_substl_subst_eq; eauto. 
      eapply PCUICClosed.closedn_subst0; eauto. admit.
      cbn in He0. eapply forallb_nth_error in He0. setoid_rewrite Enth in He0. cbn in He0.
      unfold test_def in He0. rtoProp. revert He4. len.
    }
    econstructor; eauto. eapply eq_term_upto_univ_napp_mkApps; eauto. admit.
    eexists; split; eauto.
    eapply eval_cofix_case; eauto.
    unfold cunfold_cofix. now rewrite e0.
  - edestruct IHHe1 as (? & ? & ?); eauto.
    eapply eq_term_upto_univ_mkApps_l_inv in e0 as (? & ? & [] & ->). invs e0.
    unfold cunfold_cofix in *. destruct nth_error eqn:Enth; invs e.
    eapply All2_nth_error_Some in X0 as a1; eauto. destruct a1 as (? & ? & ((? & ?) & ?) & ?). 
    edestruct IHHe2 as (? & ? & ?). { cbn. eapply eval_closed in He1; eauto. rewrite !PCUICClosed.closedn_mkApps in He1 |- *. rtoProp; split; eauto.
    erewrite <- closed_cofix_substl_subst_eq; eauto. 
    eapply PCUICClosed.closedn_subst0; eauto. admit.
    cbn in He0. eapply forallb_nth_error in He0. setoid_rewrite Enth in He0. cbn in He0.
    unfold test_def in He0. rtoProp. revert He4. len.
    }
    econstructor; eauto. eapply eq_term_upto_univ_napp_mkApps; eauto. admit.
    eexists; split; eauto.
    eapply eval_cofix_proj; eauto.
    unfold cunfold_cofix. now rewrite e.
  - edestruct IHHe1 as (? & ? & ?); eauto.
    eapply eq_term_upto_univ_mkApps_l_inv in e as (? & ? & [] & ->). invs e.
    edestruct IHHe2 as (? & ? & ?). eauto. eauto.
    eexists; split.
    2:{ eapply eval_construct; eauto. eapply All2_length in a0. lia. }
    eapply eq_term_upto_univ_napp_mkApps.
    1: econstructor; eauto.
    eapply All2_app. 2: repeat econstructor. all: eauto.
  - edestruct IHHe1 as (? & ? & ?); eauto.
    edestruct IHHe2 as (? & ? & ?); eauto.
    eexists; split.
    2:{ eapply eval_app_cong; eauto. (* isLambda_eq_term_l *) admit. }
    econstructor; eauto.
    eapply eq_term_upto_univ_empty_impl. 4: eauto. all: reflexivity.
  - exists t'. split. eapply eq_term_upto_univ_empty_impl. 4: eauto. all: admit.
Admitted.