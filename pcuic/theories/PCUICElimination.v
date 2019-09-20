(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From MetaCoq.Template Require Import config utils monad_utils BasicAst AstUtils.
From MetaCoq.PCUIC Require Import PCUICTyping PCUICAst PCUICAstUtils PCUICInduction
     PCUICWeakening PCUICSubstitution PCUICRetyping PCUICMetaTheory PCUICWcbvEval
     PCUICSR PCUICClosed PCUICInversion PCUICGeneration PCUICSafeLemmata.

Definition Is_proof `{cf : checker_flags} Σ Γ t := ∑ T u, Σ ;;; Γ |- t : T × Σ ;;; Γ |- T : tSort u × is_prop_sort u.

Lemma declared_inductive_inj `{cf : checker_flags} {Σ mdecl mdecl' ind idecl idecl'} :
  declared_inductive Σ mdecl' ind idecl' ->
  declared_inductive Σ mdecl ind idecl ->
  mdecl = mdecl' /\ idecl = idecl'.
Proof.
  intros [] []. unfold declared_minductive in *.
  rewrite H in H1. inversion H1. subst. rewrite H2 in H0. inversion H0. eauto.
Qed.

Definition SingletonProp `{cf : checker_flags} (Σ : global_env_ext) (ind : inductive) :=
  forall mdecl idecl,
    declared_inductive (fst Σ) mdecl ind idecl ->
    forall Γ args u n (Σ' : global_env_ext),
      wf Σ' ->
      PCUICWeakeningEnv.extends Σ Σ' ->
      welltyped Σ' Γ (mkApps (tConstruct ind n u) args) ->
      ∥Is_proof Σ' Γ (mkApps (tConstruct ind n u) args)∥ /\
       #|ind_ctors idecl| <= 1 /\
       squash (All (Is_proof Σ' Γ) (skipn (ind_npars mdecl) args)).

Definition Computational `{cf : checker_flags} (Σ : global_env_ext) (ind : inductive) :=
  forall mdecl idecl,
    declared_inductive (fst Σ) mdecl ind idecl ->
    forall Γ args u n (Σ' : global_env_ext),
      wf Σ' ->
      PCUICWeakeningEnv.extends Σ Σ' ->
      welltyped Σ' Γ (mkApps (tConstruct ind n u) args) ->
      Is_proof Σ' Γ (mkApps (tConstruct ind n u) args) -> False.

Definition Informative`{cf : checker_flags} (Σ : global_env_ext) (ind : inductive) :=
  forall mdecl idecl,
    declared_inductive (fst Σ) mdecl ind idecl ->
    forall Γ args u n (Σ' : global_env_ext),
      wf Σ' ->
      PCUICWeakeningEnv.extends Σ Σ' ->
      Is_proof Σ' Γ (mkApps (tConstruct ind n u) args) ->
       #|ind_ctors idecl| <= 1 /\
       squash (All (Is_proof Σ' Γ) (skipn (ind_npars mdecl) args)).

Lemma elim_restriction_works_kelim1 `{cf : checker_flags} (Σ : global_env_ext) Γ T ind npar p c brs mind idecl : wf Σ ->
  declared_inductive (fst Σ) mind ind idecl ->
  Σ ;;; Γ |- tCase (ind, npar) p c brs : T ->
  (Is_proof Σ Γ (tCase (ind, npar) p c brs) -> False) -> In InType (ind_kelim idecl).
Proof.
  intros wfΣ. intros.
  assert (HT := X).
  eapply inversion_Case in X as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?); tas.
  unfold types_of_case in e0.
  repeat destruct ?; try congruence. subst. inv e0.
  eapply declared_inductive_inj in d as []. 2:exact H. subst.
  enough (universe_family x6 = InType). rewrite H1 in i.
  eapply existsb_exists in i as (? & ? & ?).
  destruct x1; tas; discriminate.

  destruct (universe_family x6) eqn:Eu.
  - exfalso. eapply H0. exists T. exists x6. split. admit.
    split. (* 2:{ eapply universe_family_is_prop_sort; eauto. } *)
    admit. admit.
  - admit. (* no idea what to do for Set *)
  - reflexivity.
Admitted.                       (* elim_restriction_works *)

Lemma elim_restriction_works_kelim2 `{cf : checker_flags} (Σ : global_env_ext) ind mind idecl : wf Σ ->
  declared_inductive (fst Σ) mind ind idecl ->
  In InType (ind_kelim idecl) -> Informative Σ ind.
Proof.
  intros.
  destruct (PCUICWeakeningEnv.on_declared_inductive X H) as [[]]; eauto.
  intros ?. intros. inversion o.
  eapply declared_inductive_inj in H as []; eauto; subst.
  clear - onConstructors ind_sorts. try dependent induction onConstructors.
  (* - cbn. split. omega. econstructor. admit. *)
  (* -  *)
Admitted.                       (* elim_restriction_works *)

Lemma elim_restriction_works `{cf : checker_flags} (Σ : global_env_ext) Γ T ind npar p c brs mind idecl : wf Σ ->
  declared_inductive (fst Σ) mind ind idecl ->
  Σ ;;; Γ |- tCase (ind, npar) p c brs : T ->
  (Is_proof Σ Γ (tCase (ind, npar) p c brs) -> False) -> Informative Σ ind.
Proof.
  intros. eapply elim_restriction_works_kelim2; eauto.
  eapply elim_restriction_works_kelim1; eauto.
Qed.

Lemma declared_projection_projs_nonempty `{cf : checker_flags} {Σ : global_env_ext} { mind ind p a} :
  wf Σ ->
  declared_projection Σ mind ind p a ->
  ind_projs ind <> [].
Proof.
  intros. destruct H. destruct H0.
  destruct (ind_projs ind); try congruence. destruct p.
  cbn in *. destruct n; inv H0.
Qed.

Lemma elim_restriction_works_proj_kelim1 `{cf : checker_flags} (Σ : global_env_ext) Γ T p c mind idecl :
  wf Σ ->
  declared_inductive (fst Σ) mind (fst (fst p)) idecl ->
  Σ ;;; Γ |- tProj p c : T ->
  (Is_proof Σ Γ (tProj p c) -> False) -> In InType (ind_kelim idecl).
Proof.
  intros X H X0 H0.
  destruct p. destruct p. cbn in *.
  eapply inversion_Proj in X0 as (? & ? & ? & ? & ? & ? & ? & ? & ?) ; auto.
  destruct x2. cbn in *.
  pose (d' := d). destruct d' as [? _].
  eapply declared_inductive_inj in H as []; eauto. subst.
  pose proof (declared_projection_projs_nonempty X d).
  eapply PCUICWeakeningEnv.on_declared_projection in d; eauto.
  destruct d as (? & ? & ?). destruct p.
  inv o. inv o0.
  forward onProjections. eauto.
  inversion onProjections.
  clear - on_projs_elim. revert on_projs_elim. generalize (ind_kelim x1).
  intros. induction on_projs_elim; subst.
  - cbn. eauto.
  - cbn. right. eauto.
Qed. (* elim_restriction_works_proj *)

Lemma elim_restriction_works_proj `{cf : checker_flags} (Σ : global_env_ext) Γ  p c mind idecl T :
  wf Σ ->
  declared_inductive (fst Σ) mind (fst (fst p)) idecl ->
  Σ ;;; Γ |- tProj p c : T ->
  (Is_proof Σ Γ (tProj p c) -> False) -> Informative Σ (fst (fst p)).
Proof.
  intros. eapply elim_restriction_works_kelim2; eauto.
  eapply elim_restriction_works_proj_kelim1; eauto.
Qed.

Lemma length_of_btys {ind mdecl' idecl' args' u' p pty indctx pctx ps btys} :
  types_of_case ind mdecl' idecl' (firstn (ind_npars mdecl') args') u' p pty = Some (indctx, pctx, ps, btys) ->
  #|btys| = #|ind_ctors idecl'|.
Proof.
  intros. unfold types_of_case in *.
  destruct ?; try congruence.
  destruct ?; try congruence.
  destruct ?; try congruence.
  destruct ?; try congruence.
  destruct ?; try congruence.
  destruct ?; try congruence. inversion H; subst.  unfold build_branches_type in *.
  unfold mapi in *.
  clear - E4. revert btys E4. generalize 0 at 3. induction ((ind_ctors idecl')); cbn; intros.
  - cbn in E4. inversion E4. subst. reflexivity.
  - cbn in E4.
    destruct ?; try congruence.
    destruct ?; try congruence.
    destruct ?; try congruence.
    destruct ?; try congruence.
    destruct ?; try congruence.
    destruct ?; try congruence.
    destruct ?; try congruence.
    subst. inversion E4. subst. cbn. f_equal.
    eapply IHl.  eauto.
Qed.

Lemma map_option_Some X (L : list (option X)) t : map_option_out L = Some t -> All2 (fun x y => x = Some y) L t.
Proof.
  intros. induction L in t, H |- *; cbn in *.
  - inv H. econstructor.
  - destruct a. destruct ?. all:inv H. eauto.
Qed.

Lemma tCase_length_branch_inv `{cf : checker_flags} (Σ : global_env_ext) Γ ind npar p n u args brs T m t :
  wf Σ ->
  Σ ;;; Γ |- tCase (ind, npar) p (mkApps (tConstruct ind n u) args) brs : T ->
  nth_error brs n = Some (m, t) ->
  (#|args| = npar + m)%nat.
Proof.
  intros.
  eapply inversion_Case in X0 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?). subst.
  pose proof (length_of_btys e0).
  eapply type_mkApps_inv in t1 as (? & ? & [] & ?); eauto.
  eapply inversion_Construct in t1 as (? & ? & ? & ? & ? & ? & ?); eauto.
  destruct d0. cbn in *.
  eapply declared_inductive_inj in d as []; eauto. subst.

  unfold types_of_case in e0.
  repeat destruct ?; try congruence. destruct p0, p1; subst. inv E3. inv E1. inv e0.
  unfold build_branches_type in *.
  assert (exists t', nth_error x7 n = Some (m, t')).
  eapply All2_nth_error_Some in H as (? & ?). 2:eassumption. destruct p0.
  rewrite e. destruct p0 as [[? ?] ?]. cbn in *. subst. destruct x1. cbn. eauto.
  destruct H3.
  eapply map_option_Some in E4.
  eapply All2_nth_error_Some_r in E4 as (? & ? & ?); eauto.
  subst.
  rewrite nth_error_mapi in e. destruct (nth_error (ind_ctors x11) n) eqn:E7; try now inv e.
  cbn in e. inv e. destruct p0. destruct p0.
  cbn in H3.
  eapply PCUICWeakeningEnv.on_declared_inductive in H1; eauto. destruct H1.
  depelim o0. cbn in *. unfold on_constructors in *.
  eapply nth_error_alli in E7; eauto. cbn in E7.
  depelim E7. cbn in *. destruct s.
  depelim x2. cbn in *.
  subst. admit. admit.

  (* clear - H0 E4. unfold mapi in *. *)
  (* revert n x7 H0 E4. generalize 0 at 3. induction (ind_ctors x2); intros. *)
  (* - cbn in E4. inv E4. destruct n0; inv H0. *)
  (* - cbn in E4. destruct a. destruct ?; try congruence. *)
  (*   destruct p0. *)
  (*   destruct ?; try congruence. *)
  (*   inv E4. destruct ?; try congruence. *)
  (*   destruct ?; try congruence. *)
  (*   destruct ?; try congruence. *)
  (*   inv E. destruct n0; cbn in H0. *)
  (*   + inversion H0. subst. destruct l. cbn in E0. inv E0. cbn in *. inv H0. *)
  (*   + eapply IHl in E0. eauto.  *)
Admitted.                       (* tCase_length_branch_inv *)

Section no_prop_leq_type.

Context `{cf : checker_flags}.
Variable Hcf : prop_sub_type = false.

Lemma cumul_prop1 (Σ : global_env_ext) Γ A B u :
  wf Σ ->
  is_prop_sort u -> Σ ;;; Γ |- B : tSort u ->
                                 Σ ;;; Γ |- A <= B -> Σ ;;; Γ |- A : tSort u.
Proof.
  intros. induction X1.
  - admit.
  - eapply IHX1 in X0. admit.
  - eapply IHX1. eapply subject_reduction. eauto. eassumption. eauto.
Admitted.                       (* cumul_prop1 *)

Lemma cumul_prop2 (Σ : global_env_ext) Γ A B u :
  wf Σ ->
  is_prop_sort u -> Σ ;;; Γ |- A <= B ->
                             Σ ;;; Γ |- A : tSort u -> Σ ;;; Γ |- B : tSort u.
Proof.
Admitted.                       (* cumul_prop2 *)

Lemma leq_universe_prop (Σ : global_env_ext) u1 u2 :
  @check_univs cf = true ->
  (* @prop_sub_type cf = false -> *)
  wf Σ ->
  @leq_universe cf (global_ext_constraints Σ) u1 u2 ->
  (is_prop_sort u1 \/ is_prop_sort u2) ->
  (is_prop_sort u1 /\ is_prop_sort u2).
Proof.
  intros. unfold leq_universe in *. (* rewrite H in H1. *)
  (* unfold leq_universe0 in H1. *)
  (* unfold leq_universe_n in H1. *)
Admitted.                       (* leq_universe_prop *)

End no_prop_leq_type.
