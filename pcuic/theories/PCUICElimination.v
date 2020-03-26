(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool List Program.
From MetaCoq.Template Require Import config utils Universes.
From MetaCoq.PCUIC Require Import PCUICTyping PCUICAst
     PCUICSR PCUICInversion PCUICSafeLemmata.

Definition Is_proof `{cf : checker_flags} Σ Γ t := ∑ T u, Σ ;;; Γ |- t : T × Σ ;;; Γ |- T : tSort u × Universe.is_prop u.

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

Lemma leb_sort_family_intype sf : leb_sort_family InType sf -> sf = InType.
Proof.
  destruct sf; simpl; auto; discriminate.
Qed.

Lemma elim_restriction_works_kelim1 `{cf : checker_flags} (Σ : global_env_ext) Γ T ind npar p c brs mind idecl : wf Σ ->
  declared_inductive (fst Σ) mind ind idecl ->
  Σ ;;; Γ |- tCase (ind, npar) p c brs : T ->
  (Is_proof Σ Γ (tCase (ind, npar) p c brs) -> False) -> ind_kelim idecl = InType.
Proof.
  intros wfΣ. intros.
  assert (HT := X).
  eapply inversion_Case in X as [uni [args [mdecl [idecl' [ps [pty [btys
                                   [? [? [? [? [? [? [ht0 [? ?]]]]]]]]]]]]]]]; auto.
  repeat destruct ?; try congruence. subst. inv e0.
  eapply declared_inductive_inj in d as []. 2:exact H. subst.
  enough (universe_family ps = InType). rewrite H1 in i.
  now apply leb_sort_family_intype in i. 
Admitted.                       (* elim_restriction_works *)

Lemma elim_restriction_works_kelim `{cf : checker_flags} (Σ : global_env_ext) ind mind idecl : wf Σ ->
  declared_inductive (fst Σ) mind ind idecl ->
  ind_kelim idecl = InType -> Informative Σ ind.
Proof.
  intros.
  destruct (PCUICWeakeningEnv.on_declared_inductive X H) as [[]]; eauto.
  intros ?. intros. inversion o.
  eapply declared_inductive_inj in H as []; eauto; subst.
  clear - onConstructors ind_sorts. try dependent induction onConstructors.
  (* - cbn. split. lia. econstructor. admit. *)
  (* -  *)
Admitted.                       (* elim_restriction_works *)

Lemma elim_restriction_works `{cf : checker_flags} (Σ : global_env_ext) Γ T ind npar p c brs mind idecl : wf Σ ->
  declared_inductive (fst Σ) mind ind idecl ->
  Σ ;;; Γ |- tCase (ind, npar) p c brs : T ->
  (Is_proof Σ Γ (tCase (ind, npar) p c brs) -> False) -> Informative Σ ind.
Admitted.

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
  (Is_proof Σ Γ (tProj p c) -> False) -> ind_kelim idecl = InType.
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
Qed. (* elim_restriction_works_proj *)

Lemma elim_restriction_works_proj `{cf : checker_flags} (Σ : global_env_ext) Γ  p c mind idecl T :
  wf Σ ->
  declared_inductive (fst Σ) mind (fst (fst p)) idecl ->
  Σ ;;; Γ |- tProj p c : T ->
  (Is_proof Σ Γ (tProj p c) -> False) -> Informative Σ (fst (fst p)).
Proof.
  intros. eapply elim_restriction_works_kelim; eauto.
  eapply elim_restriction_works_proj_kelim1; eauto.
Qed.

Lemma length_of_btys {ind mdecl' idecl' args' u' p} :
  #|build_branches_type ind mdecl' idecl' args' u' p| = #|ind_ctors idecl'|.
Proof.
  unfold build_branches_type. now rewrite mapi_length.
Qed.

Lemma length_map_option_out {A} l l' :
  @map_option_out A l = Some l' -> #|l| = #|l'|.
Proof.
  induction l as [|[x|] l] in l' |- *.
  - destruct l'; [reflexivity|discriminate].
  - cbn. destruct (map_option_out l); [|discriminate].
    destruct l'; [discriminate|]. inversion 1; subst; cbn; eauto.
  - discriminate.
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
  intros. eapply inversion_Case in X0 as (u' & args' & mdecl' & idecl' & ps' & pty' & btys' & ? & ? & ? & ? & ? & ? & ? & ? & ?); eauto.
  subst. unfold build_case_predicate_type  in *.
Admitted.

Section no_prop_leq_type.

Context `{cf : checker_flags}.
Variable Hcf : prop_sub_type = false.

Lemma cumul_prop (Σ : global_env_ext) Γ A B u :
  wf Σ ->
  Universe.is_prop u ->
  (Σ ;;; Γ |- A : tSort u + (Σ ;;; Γ |- B : tSort u))%type ->
  Σ ;;; Γ |- A <= B ->
  ((Σ ;;; Γ |- A : tSort u) * (Σ ;;; Γ |- B : tSort u))%type.
Admitted.

Lemma cumul_prop1 (Σ : global_env_ext) Γ A B u :
  wf Σ ->
  Universe.is_prop u ->
  Σ ;;; Γ |- B : tSort u ->
  Σ ;;; Γ |- A <= B ->
  Σ ;;; Γ |- A : tSort u.
Proof.
  intros. eapply cumul_prop in X1; eauto. firstorder.
Qed.

Lemma cumul_prop2 (Σ : global_env_ext) Γ A B u :
  wf Σ ->
  Universe.is_prop u ->
  Σ ;;; Γ |- A <= B ->
  Σ ;;; Γ |- A : tSort u ->
  Σ ;;; Γ |- B : tSort u.
Proof.
  intros. eapply cumul_prop in X0; eauto. firstorder.  
Qed.

Lemma leq_universe_prop (Σ : global_env_ext) u1 u2 :
  @check_univs cf = true ->
  (* @prop_sub_type cf = false -> *)
  wf Σ ->
  @leq_universe cf (global_ext_constraints Σ) u1 u2 ->
  (Universe.is_prop u1 \/ Universe.is_prop u2) ->
  (Universe.is_prop u1 /\ Universe.is_prop u2).
Proof.
  intros. unfold leq_universe in *.
Admitted.                       (* leq_universe_prop *)

End no_prop_leq_type.
