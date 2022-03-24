(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils.
From MetaCoq.Erasure Require Import EAstUtils Extract EArities EWcbvEval.
From MetaCoq.PCUIC Require Import PCUICTyping PCUICAst PCUICAstUtils
     PCUICSubstitution PCUICLiftSubst PCUICClosedTyp
     PCUICReduction PCUICWcbvEval PCUICSR PCUICInversion PCUICGeneration
     PCUICContextConversion PCUICArities PCUICWellScopedCumulativity PCUICCanonicity.
From MetaCoq.SafeChecker Require Import PCUICErrors.
From Coq Require Import Program ssreflect.

Local Existing Instance extraction_checker_flags.

Ltac inv H := inversion H; subst; clear H.

Lemma typing_spine_inv args arg a Σ x2 x3 :
  nth_error args (arg) = Some a ->
  typing_spine Σ [] x2 args x3 ->
  {T & Σ;;; [] |- a : T}.
Proof.
  intros. revert arg H.
  dependent induction X; intros arg H17.
  - rewrite nth_error_nil in H17. congruence.
  - destruct (arg)%nat eqn:EAst.
    + cbn in H17. invs H17. eauto.
    + cbn in H17. eauto.
Qed.

Definition well_typed Σ Γ t := ∑ T, Σ ;;; Γ |- t : T.

Lemma typing_spine_wt args Σ x2 x3 :  wf Σ.1 ->
  typing_spine Σ [] x2 args x3 ->
  All (well_typed Σ []) args.
Proof.
  intros wfΣ sp.
  dependent induction sp; constructor; auto.
  now exists A.
Qed.

Lemma typing_spine_eval:
  forall (Σ : global_env_ext) (args args' : list PCUICAst.term) 
  (X : All2 (PCUICWcbvEval.eval Σ) args args') (bla : wf Σ)
    (T x x0 : PCUICAst.term) (t0 : typing_spine Σ [] x args x0) 
    (c : Σ;;; [] ⊢ x0 ≤ T) (x1 : PCUICAst.term)
    (c0 : Σ;;; [] ⊢ x1 ≤ x), isType Σ [] x1 -> isType Σ [] T -> typing_spine Σ [] x1 args' T.
Proof.
  intros. eapply typing_spine_red; eauto.
  eapply typing_spine_wt in t0; auto.
  eapply All2_All_mix_left in X; eauto. simpl in X.
  eapply All2_impl. eassumption. simpl. intros t u [ct et]. eapply wcbeval_red; eauto.
  eapply (projT2 ct).
Qed.

(** ** on mkApps *)

Lemma emkApps_snoc a l b :
  EAst.mkApps a (l ++ [b]) = EAst.tApp (EAst.mkApps a l) b.
Proof.
  revert a; induction l; cbn; congruence.
Qed.

Lemma mkApps_snoc a l b :
  PCUICAst.mkApps a (l ++ [b]) = PCUICAst.tApp (PCUICAst.mkApps a l) b.
Proof.
  revert a; induction l; cbn; congruence.
Qed.

Lemma mkAppBox_repeat n a :
  mkAppBox a n = EAst.mkApps a (repeat EAst.tBox n).
Proof.
  revert a; induction n; cbn; firstorder congruence.
Qed.

Lemma decompose_app_rec_inv2 {t l' f l} :
  decompose_app_rec t l' = (f, l) ->
  isApp f = false.
Proof.
  induction t in f, l', l |- *; try intros [= <- <-]; try reflexivity.
  simpl. apply IHt1.
Qed.

Module Ee := EWcbvEval.

Lemma fst_decompose_app_rec t l : fst (EAstUtils.decompose_app_rec t l) = fst (EAstUtils.decompose_app t).
Proof.
  induction t in l |- *; simpl; auto. rewrite IHt1.
  unfold decompose_app. simpl. now rewrite (IHt1 [t2]).
Qed.

Lemma value_app_inv {wfl : Ee.WcbvFlags} L :
  Ee.value (EAst.mkApps EAst.tBox L) ->
  L = nil.
Proof.
  intros. depelim X.
  - destruct L using rev_ind.
    reflexivity.
    rewrite emkApps_snoc in i. inv i.
  - destruct (EAstUtils.mkApps_elim t l). EAstUtils.solve_discr.
    rewrite Ee.value_head_spec in i.
    move/andb_and: i => [H H'].
    eapply Ee.atom_mkApps in H' as [H1 _].
    destruct n, L; discriminate.
  - unfold Ee.isStuckFix in i. destruct f; try now inversion i.
    assert (EAstUtils.decompose_app (EAst.mkApps (EAst.tFix m n) args) = EAstUtils.decompose_app (EAst.mkApps EAst.tBox L)) by congruence.
    rewrite !EAstUtils.decompose_app_mkApps in H; eauto. inv H.
Qed.

(** ** Prelim on fixpoints *)

Lemma fix_subst_nth mfix n :
  n < #|mfix| ->
  nth_error (fix_subst mfix) n = Some (tFix mfix (#|mfix| - n - 1)).
Proof.
  unfold fix_subst. generalize (#|mfix|).
  intros m. revert n. induction m; cbn; intros.
  - destruct n; inv H.
  - destruct n.
    + cbn. now rewrite Nat.sub_0_r.
    + cbn. rewrite IHm. lia. reflexivity.
Qed.

Lemma efix_subst_nth mfix n :
  n < #|mfix| ->
  nth_error (EGlobalEnv.fix_subst mfix) n = Some (EAst.tFix mfix (#|mfix| - n - 1)).
Proof.
  unfold EGlobalEnv.fix_subst. generalize (#|mfix|).
  intros m. revert n. induction m; cbn; intros.
  - destruct n; inv H.
  - destruct n.
    + cbn. now rewrite Nat.sub_0_r.
    + cbn. rewrite IHm. lia. reflexivity.
Qed.

Lemma subslet_fix_subst `{cf : checker_flags} Σ mfix1 T n :
  wf Σ.1 ->
  Σ ;;; [] |- tFix mfix1 n : T ->
  subslet Σ [] (fix_subst mfix1) (fix_context mfix1).
Proof.
  intro hΣ.
  unfold fix_subst, fix_context.
  assert (exists L, mfix1 = mfix1 ++ L) by (exists []; now simpl_list). revert H.
  generalize mfix1 at 2 5 6.  intros.
  induction mfix0 using rev_ind.
  - econstructor.
  - rewrite mapi_app. cbn in *. rewrite rev_app_distr. cbn in *.
    rewrite app_length. cbn. rewrite Nat.add_comm /=; econstructor.
    + eapply IHmfix0. destruct H as [L]. exists (x :: L). subst. now rewrite <- app_assoc.
    + rewrite <- plus_n_O.
      rewrite PCUICLiftSubst.simpl_subst_k. clear. induction l; cbn; try congruence.
      eapply inversion_Fix in X as (? & ? & ? & ? & ? & ? & ?) ; auto.
      econstructor; eauto. destruct H. subst.
      rewrite <- app_assoc, nth_error_app_ge; try lia.
      now rewrite Nat.sub_diag.
Qed.

Lemma cofix_subst_nth mfix n :
  n < #|mfix| ->
  nth_error (cofix_subst mfix) n = Some (tCoFix mfix (#|mfix| - n - 1)).
Proof.
  unfold cofix_subst. generalize (#|mfix|).
  intros m. revert n. induction m; cbn; intros.
  - destruct n; inv H.
  - destruct n.
    + cbn. now rewrite Nat.sub_0_r.
    + cbn. rewrite IHm; lia_f_equal.
Qed.

Lemma ecofix_subst_nth mfix n :
  n < #|mfix| ->
  nth_error (EGlobalEnv.cofix_subst mfix) n = Some (EAst.tCoFix mfix (#|mfix| - n - 1)).
Proof.
  unfold EGlobalEnv.cofix_subst. generalize (#|mfix|).
  intros m. revert n. induction m; cbn; intros.
  - destruct n; inv H.
  - destruct n.
    + cbn. now rewrite Nat.sub_0_r.
    + cbn. rewrite IHm. lia. reflexivity.
Qed.

Lemma subslet_cofix_subst `{cf : checker_flags} Σ mfix1 T n :
  wf Σ.1 ->
  Σ ;;; [] |- tCoFix mfix1 n : T ->
  subslet Σ [] (cofix_subst mfix1) (fix_context mfix1).
Proof.
  intro hΣ.
  unfold cofix_subst, fix_context.
  assert (exists L, mfix1 = mfix1 ++ L)%list by (exists []; now simpl_list). revert H.
  generalize mfix1 at 2 5 6.  intros.
  induction mfix0 using rev_ind.
  - econstructor.
  - rewrite mapi_app. cbn in *. rewrite rev_app_distr. cbn in *.
    rewrite app_length /= Nat.add_comm /=. econstructor.
    + eapply IHmfix0. destruct H as [L]. exists (x :: L). subst. now rewrite <- app_assoc.
    + rewrite <- plus_n_O.
      rewrite PCUICLiftSubst.simpl_subst_k. clear. induction l; cbn; try congruence.
      eapply inversion_CoFix in X as (? & ? & ? & ? & ? & ? & ?) ; auto.
      econstructor; eauto. destruct H. subst.
      rewrite <- app_assoc. rewrite nth_error_app_ge. lia.
      now rewrite Nat.sub_diag.
Qed.

(** ** Prelim on typing *)

Inductive red_decls Σ Γ Γ' : forall (x y : context_decl), Type :=
| conv_vass na na' T T' : isType Σ Γ' T' -> red Σ Γ T T' ->
  eq_binder_annot na na' ->
  red_decls Σ Γ Γ' (vass na T) (vass na' T')

| conv_vdef_type na na' b T T' : isType Σ Γ' T' -> red Σ Γ T T' ->
  eq_binder_annot na na' ->
  red_decls Σ Γ Γ' (vdef na b T) (vdef na' b T')

| conv_vdef_body na na' b b' T : isType Σ Γ' T ->
  eq_binder_annot na na' ->
  Σ ;;; Γ' |- b' : T -> red Σ Γ b b' ->
  red_decls Σ Γ Γ' (vdef na b T) (vdef na' b' T).

Notation red_context Σ := (All2_fold (red_decls Σ)).

Lemma conv_context_app (Σ : global_env_ext) (Γ1 Γ2 Γ1' : context) :
  wf Σ ->
  wf_local Σ (Γ1 ,,, Γ2) ->
  conv_context Σ Γ1 Γ1' -> conv_context Σ (Γ1 ,,, Γ2) (Γ1' ,,, Γ2).
Proof.
  intros. induction Γ2.
  - cbn; eauto.
  - destruct a. destruct decl_body.
    + cbn. econstructor. inv X0. apply IHΓ2. eauto.
      depelim X0; econstructor; reflexivity.
    + cbn. econstructor. inv X0. apply IHΓ2. eauto. now econstructor.
Qed.
