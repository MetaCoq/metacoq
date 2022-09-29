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

Lemma alpha_substl x x' b b' n :
  All (fun x => closed x) x -> Forall (fun x => closed x) x' ->
  All2 (eq_term_upto_univ_napp empty_global_env R1 R1 0) x x' ->
  eq_term_upto_univ_napp empty_global_env R1 R2 n b b' ->
  eq_term_upto_univ_napp empty_global_env R1 R2 n (substl x b) (substl x' b').
Proof.
  unfold substl.
  induction 1 in x', b, b' |- *; intros Hx' Hall Heq; invs Hall; cbn.
  - eauto.
  - eapply IHX. 
    + now invs Hx'.
    + eauto.
    + eapply alpha_csubst; eauto.
      now invs Hx'.
Qed.

End fixR.

Section fixR.

Variable R1 : (Universe.t -> Universe.t -> Prop).
Variable R2 : (Universe.t -> Universe.t -> Prop).
Context {HR1 : Reflexive R1}.
Existing Instance HR1.
Context {HR2 : Reflexive R2}.
Context {TranR1 : RelationClasses.Transitive R1}.
Context {TranR2 : RelationClasses.Transitive R2}.

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


Hint Resolve eq_term_upto_univ_napp_closedn eq_term_upto_univ_napp_closedn' eval_closed : core.

Lemma is_value_impl_eq_term f' x n :
  ~~ (isLambda f' || isFixApp f' || isArityHead f' || isConstructApp f' || isPrimApp f') ->
  eq_term_upto_univ_napp empty_global_env R1 R2 n f' x ->
  ~~ (isLambda x || isFixApp x || isArityHead x || isConstructApp x || isPrimApp x).
Proof.
  intros H1 H2.
  induction f' in n, x, H1, H2 |- * using PCUICInduction.term_ind_size_app; cbn in *; try congruence.
  all: invs H2; cbn in *; try congruence.
  specialize (IHf'1 t').
  specialize (IHf'2 t').
  unfold isFixApp, isConstructApp in *. rewrite -> head_tapp in *.
  rewrite -> orb_false_r in *.
  unfold head in *.
  rewrite -> (mkApps_decompose_app f'1) in *.
  eapply eq_term_upto_univ_napp_mkApps_l_inv in X as (? & ? & [] & ?). subst.
  revert H1.
  assert (~~ isApp (decompose_app f'1).1).
  { destruct (decompose_app f'1) eqn:E; cbn. 
    erewrite decompose_app_notApp; cbn; eauto. }
  rewrite !decompose_app_mkApps; eauto.
  - invs e; cbn; eauto. rewrite <- H2 in H0. cbn in *. tauto.
  - destruct (decompose_app f'1); try reflexivity.
    invs e; cbn; eauto.
    all: epose proof (mkApps_app _ l [f'2]) as Eqn; cbn in Eqn; rewrite <- Eqn.
    all: epose proof (mkApps_app _ x0 [u']) as Eqn'; cbn in Eqn'; rewrite <- Eqn'.
    all: rewrite !isPrimApp_mkApps; cbn; eauto.
    todo "prim, matthieu".    
Qed.

End fixR.

Section fixR.

Variable R1 : (Universe.t -> Universe.t -> Prop).
Variable R2 : (Universe.t -> Universe.t -> Prop).
Context {HR1 : Reflexive R1}.
Existing Instance HR1.
Context {HR2 : Reflexive R2}.
Context {TranR1 : RelationClasses.Transitive R1}.
Context {TranR2 : RelationClasses.Transitive R2}.

Existing Instance HR2.
Context {Sub : RelationClasses.subrelation R1 R2}.
Context {HUniv1: SubstUnivPreserving R1}.
Context {HUniv2: SubstUnivPreserving R2}.

Hint Resolve eq_term_upto_univ_napp_closedn eq_term_upto_univ_napp_closedn' eval_closed : core.

Lemma alpha_eval {cf} Σ n t v t' :
  wf_ext Σ ->
  closed t ->
  eval Σ t v ->
  eq_term_upto_univ_napp empty_global_env R1 R2 n t t' ->
  ∑ v', eq_term_upto_univ_napp empty_global_env R1 R2 0 v v' × eval Σ t' v'.
Proof.
  intros Hwf Hcl He Ha.
  induction He in t', Hcl, Ha, n, R2, HR2, TranR2, Sub, HUniv2 |- *; try (destruct t'; invs Ha; []); cbn in Hcl; rtoProp. 
  - edestruct IHHe1 as (? & ? & ?); eauto; []. invs e.
    edestruct IHHe2 as (? & ? & ?); cycle 4. eauto. eauto. 
    edestruct IHHe3 as (? & ? & ?); cycle 5.
    1:{ eapply alpha_csubst. eauto. 1-2: eapply eval_closed; [ | | eauto]; eauto. eapply eq_term_upto_univ_napp_closedn'.  2: eauto. all: eauto. reflexivity. }
    all: (typeclasses eauto || eauto). 
    rewrite PCUICCSubst.closed_subst. 1: now eauto.
    eapply PCUICClosed.closedn_subst0. cbn. eapply andb_and. split; eauto.
    cbn. eapply eval_closed in e0; eauto. cbn in e0. rtoProp. eauto.
  - edestruct IHHe1 as (? & ? & ?); cycle 4. eauto. eauto. 
    edestruct IHHe2 as (? & ? & ?); cycle 4.
    { rewrite PCUICCSubst.closed_subst; eauto. eapply PCUICClosed.closedn_subst0; cbn. rtoProp; eauto. eauto. }
    { eapply alpha_csubst; cycle 3; eauto. eapply eval_closed. 3: eauto. eauto.    
    eapply eq_term_upto_univ_napp_closedn'. 2: eauto. all: eauto; try reflexivity. }
    all: (typeclasses eauto || eauto).
  - edestruct IHHe as (? & ? & ?); cycle 4.
    { rewrite PCUICClosed.closedn_subst_instance. eapply declared_constant_closed_body; eauto. }
    { eapply impl1. eauto. eapply eq_term_upto_univ_subst_instance; eauto. reflexivity. }
    all: eauto.
  - edestruct IHHe1 as (? & ? & ?); cycle 4. 1-2: eauto.
    eapply eq_term_upto_univ_mkApps_l_inv in e3 as (? & ? & [] & ->). invs e3.
    eapply All2_nth_error_Some in e as Hnth. 2: eauto.
    destruct Hnth as (? & ? & ? & ?).
    edestruct IHHe2 as (? & ? & ?); cycle 4.
    { eapply eval_closed in He1 as Hc1; eauto. rewrite PCUICClosed.closedn_mkApps in Hc1. rtoProp. eapply PCUICClosed.closedn_subst0; cbn; eauto.
      - solve_all. eapply All_skipn. solve_all.
      - rewrite /expand_lets /expand_lets_k. eapply PCUICClosed.closedn_subst0; len.
        1-2: todo "matthieu".
    }
    eapply eq_term_upto_univ_substs; eauto.
    3:{ eexists. split. eauto. eapply eval_iota; eauto. 
      - eapply All2_length in a. lia.
      - rewrite e2. eapply PCUICConfluence.eq_context_gen_context_assumptions. eauto.
    }
    all: (typeclasses eauto || eauto).
    + rewrite /expand_lets /expand_lets_k.
      eapply eq_term_upto_univ_substs => //.
    { simpl. rewrite /inst_case_branch_context !inst_case_context_length.
      rewrite /inst_case_context !context_assumptions_subst_context
        !context_assumptions_subst_instance.
       have lenctxass := PCUICConfluence.eq_context_gen_context_assumptions a0.
       have lenctx := All2_fold_length a0.
       rewrite lenctxass lenctx.
      eapply eq_term_upto_univ_lift => //.
      eapply eq_term_upto_univ_leq; tea. lia. }
      eapply PCUICConfluence.eq_context_extended_subst; tea.
      rewrite /inst_case_branch_context.
      eapply eq_context_upto_subst_context; tc.
      eapply PCUICConfluence.eq_context_upto_univ_subst_instance'.
      all: eauto; try reflexivity. eapply X. 
      eapply All2_rev, X.
    + eapply All2_rev, All2_skipn. solve_all.
  - edestruct (IHHe1 R2) as (? & ? & ?); cycle 4. 1-2: eauto. eapply impl1; eauto.
    eapply eq_term_upto_univ_mkApps_l_inv in e1 as (? & ? & [] & ->). invs e1.
    eapply All2_nth_error_Some in a0 as a1. destruct a1 as (? & ? & ?).
    edestruct IHHe2 as (? & ? & ?); cycle 4.
    { eapply eval_closed in He1; eauto. rewrite PCUICClosed.closedn_mkApps in He1. rtoProp. solve_all.
    eapply All2_nth_error_Some in a0 as (? & ? & ? & ?); eauto. }
    2:{ eexists. split. eauto. econstructor; try eassumption. 
    rewrite <- e. symmetry. now eapply All2_length. }
    all: (typeclasses eauto || eauto). eapply impl1; eauto.
  - edestruct IHHe1 as (? & ? & ?); cycle 4. 1-2: eauto.
    eapply eq_term_upto_univ_mkApps_l_inv in e0 as (? & ? & [] & ->). invs e0.
    unfold cunfold_fix in *. destruct nth_error eqn:Enth; try congruence.
    eapply All2_nth_error_Some in X1 as a1; eauto. destruct a1 as (? & ? & ((? & ?) & ?) & ?).
    edestruct IHHe2 as (? & ? & ?); cycle 4. 1-2: eauto. invs e.
    edestruct IHHe3 as (? & ? & ?); cycle 4. { cbn.
      eapply eval_closed in He1; eauto. rewrite PCUICClosed.closedn_mkApps in He1. rtoProp.
      rewrite PCUICClosed.closedn_mkApps; rtoProp; repeat split; eauto.
      erewrite <- closed_fix_substl_subst_eq; eauto.
      eapply PCUICClosed.closedn_subst0.
      { solve_all.
        unfold fix_subst.
        move: #|mfix| => N.
        induction N. constructor.
        constructor; auto. }
      cbn in H1. eapply forallb_nth_error in H1. setoid_rewrite Enth in H1. cbn in H1.
      unfold test_def in H1. rtoProp. revert H4. len.
    }
    econstructor; eauto.
    eapply eq_term_upto_univ_napp_mkApps; eauto.
    2:{ eexists. split. eauto. eapply eval_fix; eauto. unfold cunfold_fix. rewrite e0. repeat f_equal. 
        eapply All2_length in a0; lia. }
    all: (typeclasses eauto || eauto).
    eapply alpha_substl; eauto.
    + unfold fix_subst.
      move: #|mfix| => N.
      induction N. constructor.
      constructor; auto.
      eapply eval_closed in He1; eauto.
      rewrite PCUICClosed.closedn_mkApps in He1. now rtoProp.
    + unfold fix_subst.
      move: #|mfix'| => N.
      induction N. constructor.
      constructor; auto.
      eapply eval_closed in e1; eauto.
      rewrite PCUICClosed.closedn_mkApps in e1. now rtoProp.
    + unfold fix_subst. erewrite <- (All2_length (l' := mfix')); eauto; [].
      move: #|mfix| => N.
      induction N. constructor.
      constructor; eauto.
      econstructor. eauto.
    + rewrite <- H2.  eapply eq_term_upto_univ_leq. 3: eauto. eauto. lia.
  - edestruct IHHe1 as (? & ? & ?); eauto.
    eapply eq_term_upto_univ_mkApps_l_inv in e0 as (? & ? & [] & ->). invs e0.
    unfold cunfold_fix in *. destruct nth_error eqn:Enth; try congruence.
    eapply All2_nth_error_Some in X1 as a1; eauto. destruct a1 as (? & ? & ((? & ?) & ?) & ?).
    edestruct IHHe2 as (? & ? & ?); cycle 4. 1-2: eauto. invs e.
    eexists; split. 
    2:{ eapply eval_fix_value.
        3:{ unfold cunfold_fix. setoid_rewrite e0. reflexivity. }
        all: eauto. 
        eapply All2_length in a0. lia. }
    econstructor; eauto.
    eapply eq_term_upto_univ_napp_mkApps; eauto. econstructor. solve_all.
    all: (typeclasses eauto || eauto).
  - edestruct IHHe1 as (? & ? & ?); eauto. eapply impl1; eauto.
    eapply eq_term_upto_univ_mkApps_l_inv in e0 as (? & ? & [] & ->). invs e0.
    unfold cunfold_cofix in *. destruct nth_error eqn:Enth; try congruence.
    eapply All2_nth_error_Some in X2 as a1; eauto. destruct a1 as (? & ? & ((? & ?) & ?) & ?). invs e.
    edestruct IHHe2 as (? & ? & ?); cycle 4. { cbn. rtoProp. repeat split; eauto. rewrite PCUICClosed.closedn_mkApps.
      eapply eval_closed in He1; eauto.  rewrite PCUICClosed.closedn_mkApps in He1. rtoProp. split; eauto.
      erewrite <- closed_cofix_substl_subst_eq; eauto. 
      eapply PCUICClosed.closedn_subst0; eauto. 
      { solve_all.
        unfold cofix_subst.
        move: #|mfix| => N.
        induction N. constructor.
        constructor; auto. }
        rename H2 into He0.
      cbn in He0. eapply forallb_nth_error in He0. setoid_rewrite Enth in He0. cbn in He0.
      unfold test_def in He0. rtoProp. revert H4. len.
    }
    econstructor; eauto. eapply eq_term_upto_univ_napp_mkApps; eauto.
    
    2:{ eexists; split; eauto.
        eapply eval_cofix_case; eauto.
        unfold cunfold_cofix. now rewrite e0. }
    all: eauto.

    eapply alpha_substl; eauto; try reflexivity.
    + unfold cofix_subst.
      move: #|mfix| => N.
      induction N. constructor.
      constructor; auto.
      eapply eval_closed in He1; eauto.
      rewrite PCUICClosed.closedn_mkApps in He1. now rtoProp.
    + unfold cofix_subst.
      move: #|mfix'| => N.
      induction N. constructor.
      constructor; auto.
      eapply eval_closed in e1; eauto.
      rewrite PCUICClosed.closedn_mkApps in e1. now rtoProp.
      eapply eq_term_upto_univ_napp_closedn'. 2: eauto. all: eauto; try reflexivity.
    + unfold cofix_subst. erewrite <- (All2_length (l' := mfix')); eauto; [].
      move: #|mfix| => N.
      induction N. constructor.
      constructor; eauto.
      econstructor. eauto.
    + eapply eq_term_upto_univ_leq. 3: eauto. reflexivity. lia.
  - edestruct IHHe1 as (? & ? & ?); eauto. eapply impl1; eauto.
    eapply eq_term_upto_univ_mkApps_l_inv in e0 as (? & ? & [] & ->). invs e0.
    unfold cunfold_cofix in *. destruct nth_error eqn:Enth; invs e.
    eapply All2_nth_error_Some in X0 as a1; eauto. destruct a1 as (? & ? & ((? & ?) & ?) & ?). 
    edestruct IHHe2 as (? & ? & ?); cycle 4. { cbn. eapply eval_closed in He1; eauto. rewrite !PCUICClosed.closedn_mkApps in He1 |- *. rtoProp; split; eauto.
    erewrite <- closed_cofix_substl_subst_eq; eauto. 
    eapply PCUICClosed.closedn_subst0; eauto. 
    { solve_all.
      unfold cofix_subst.
      move: #|mfix| => N.
      induction N. constructor.
      constructor; auto. }
      rename H into He0.
    cbn in He0. eapply forallb_nth_error in He0. setoid_rewrite Enth in He0. cbn in He0.
    unfold test_def in He0. rtoProp. revert H1. len.
    }
    econstructor; eauto. eapply eq_term_upto_univ_napp_mkApps; eauto.
    2:{ eexists; split; eauto.
        eapply eval_cofix_proj; eauto.
        unfold cunfold_cofix. now rewrite e. }
    all: eauto.

    eapply alpha_substl; eauto; try reflexivity.
    + unfold cofix_subst.
      move: #|mfix| => N.
      induction N. constructor.
      constructor; auto.
      eapply eval_closed in He1; eauto.
      rewrite PCUICClosed.closedn_mkApps in He1. now rtoProp.
    + unfold cofix_subst.
      move: #|mfix'| => N.
      induction N. constructor.
      constructor; auto.
      eapply eval_closed in e1; eauto.
      rewrite PCUICClosed.closedn_mkApps in e1. now rtoProp.
      eapply eq_term_upto_univ_napp_closedn'. 2: eauto. all: eauto; try reflexivity.
    + unfold cofix_subst. erewrite <- (All2_length (l' := mfix')); eauto; [].
      move: #|mfix| => N.
      induction N. constructor.
      constructor; eauto.
      econstructor. eauto.
    + eapply eq_term_upto_univ_leq. 3: eauto. reflexivity. lia.
  - edestruct IHHe1 as (? & ? & ?); eauto.
    eapply eq_term_upto_univ_mkApps_l_inv in e as (? & ? & [] & ->). invs e.
    edestruct IHHe2 as (? & ? & ?); cycle 4. 1-2: eauto.
    eexists; split.
    2:{ eapply eval_construct; eauto. eapply All2_length in a0. lia. }
    eapply eq_term_upto_univ_napp_mkApps.
    1: econstructor; eauto.
    eapply All2_app. 2: repeat econstructor.
    all: (typeclasses eauto || eauto).
  - edestruct IHHe1 as (? & ? & ?); eauto.
    edestruct IHHe2 as (? & ? & ?); cycle 4. 1-2: eauto.
    eexists; split.
    2:{ eapply eval_app_cong; eauto.

    eapply is_value_impl_eq_term; eauto. }
    all: eauto; try reflexivity.
    econstructor; eauto.
    eapply eq_term_upto_univ_impl. 5: eauto. 4: lia.
    all: eauto; try reflexivity.
  - exists t'. split. eapply eq_term_upto_univ_empty_impl. 4: eauto.
    all: eauto; try reflexivity. econstructor.
    unfold atom in *.
    invs Ha; cbn in *; congruence.
    Unshelve. all: constructor.
Qed.

End fixR.