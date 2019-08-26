(* Distributed under the terms of the MIT license.   *)

(** * Universe Substitution lemmas for typing derivations. *)

From Coq Require Import Bool String List BinPos Compare_dec Arith Lia.
Require Import Coq.Program.Syntax Coq.Program.Basics.
From MetaCoq.Template Require Import utils config AstUtils UnivSubst.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICEquality
     PCUICUnivSubst PCUICTyping PCUICWeakeningEnv PCUICClosed
     PCUICReduction PCUICCumulativity PCUICWeakening PCUICUnivSubst.
(* Require Import ssreflect. *)

Local Set Keyed Unification.

Lemma fix_context_subst_instance:
  forall (mfix : list (def term)) (u : universe_instance),
    fix_context (map (map_def (subst_instance_constr u) (subst_instance_constr u)) mfix) =
    map (map_decl (subst_instance_constr u)) (fix_context mfix).
Proof.
  intros mfix u.
Admitted.

Lemma isWfArity_subst_instance:
  forall (cf : checker_flags) (Σ : global_env × universes_decl) (Γ : context) (B : term),
    isWfArity typing Σ Γ B ->
    forall (u : universe_instance) (univs : universes_decl),
      consistent_instance_ext (Σ.1, univs) Σ.2 u ->
      isWfArity typing (Σ.1, univs) (subst_instance_context u Γ) (subst_instance_constr u B).
Proof.
  intros cf Σ Γ B x u univs H.
Admitted.

Lemma subst_instance_constr_two u1 u2 t :
  subst_instance_constr u1 (subst_instance_constr u2 t) = subst_instance_constr (subst_instance_instance u1 u2) t.
Proof.
Admitted.

Lemma consistent_ext_trans:
  forall (cf : checker_flags) (Σ : global_env × universes_decl) (u : universe_instance) U,
    consistent_instance_ext Σ U u ->
    forall (u0 : universe_instance) (univs : universes_decl),
      consistent_instance_ext (Σ.1, univs) Σ.2 u0 ->
      consistent_instance_ext (Σ.1, univs) U (subst_instance_instance u0 u).
Proof.
  intros.
Admitted.

Hint Resolve consistent_ext_trans. 
(* Hint Resolve wf_local_subst_instance.  *)

Lemma subst_instance_univ_super:
  forall (l : Level.t) (u : universe_instance),
    subst_instance_univ u (Universe.super l) = Universe.super (subst_instance_level u l).
Proof.
  intros l u.
Admitted.


Lemma subst_instance_univ_make :
  forall (l : Level.t) (u : universe_instance),
    subst_instance_univ u (Universe.make l) = Universe.make (subst_instance_level u l).
Proof.
  intros l u.
Admitted.

Lemma LevelIn_subst_instance:
  forall (cf : checker_flags) (Σ : global_env × universes_decl) (l : Level.t),
    LevelSet.In l (global_ext_levels Σ) ->
    forall (u : universe_instance) (univs : universes_decl),
      consistent_instance_ext (Σ.1, univs) Σ.2 u ->
      LevelSet.In (subst_instance_level u l) (global_ext_levels (Σ.1, univs)).
Proof.
  intros cf Σ l H u univs H0.
Admitted.
    
Lemma product_subst_instance u s1 s2 :
  subst_instance_univ u (Universe.sort_of_product s1 s2) = Universe.sort_of_product (subst_instance_univ u s1) (subst_instance_univ u s2).
Admitted.

Lemma iota_red_subst_instance :
  forall (pars c : nat) (args : list term) (brs : list (nat × term)) u,
    subst_instance_constr u (iota_red pars c args brs) =
    iota_red pars c (map (subst_instance_constr u) args) (map (on_snd (subst_instance_constr u)) brs).
Proof.
  intros. unfold iota_red. rewrite !subst_instance_constr_mkApps. f_equal; auto using map_skipn.
  rewrite nth_map; simpl; auto.
Qed.

Lemma fix_subst_subst_instance:
  forall (u : universe_instance) (mfix : mfixpoint term),
    fix_subst (map (map_def (subst_instance_constr u) (subst_instance_constr u)) mfix) =
    map (subst_instance_constr u) (fix_subst mfix).
Proof.
  intros u mfix.
Admitted.


Lemma cofix_subst_subst_instance:
  forall (u : universe_instance) (mfix : mfixpoint term),
    cofix_subst (map (map_def (subst_instance_constr u) (subst_instance_constr u)) mfix) =
    map (subst_instance_constr u) (cofix_subst mfix).
Proof.
  intros u mfix.
Admitted.


Lemma isConstruct_app_subst_instance:
  forall (u : universe_instance) (t : term),
    isConstruct_app (subst_instance_constr u t) = isConstruct_app t.
Proof.
  intros u t.
Admitted.

Lemma red1_subst_instance {cf:checker_flags} (Σ : global_env_ext) Γ u s t :
  wf Σ -> 
  red1 Σ Γ s t ->
  red1 Σ (subst_instance_context u Γ) (subst_instance_constr u s) (subst_instance_constr u t).
Proof.
  intros. induction X0 using red1_ind_all.
  all: try now (cbn; econstructor; eauto).
  - cbn. rewrite <- subst_subst_instance_constr. econstructor.
  - cbn. rewrite <- subst_subst_instance_constr. econstructor.
  - cbn. rewrite <- lift_subst_instance_constr. econstructor.
    unfold subst_instance_context.
    unfold option_map in *. destruct (nth_error Γ) eqn:E; inversion H.
    unfold map_context. rewrite nth_error_map, E. cbn.
    rewrite map_decl_body. destruct c. cbn in H1. subst.
    reflexivity.
  - cbn. rewrite subst_instance_constr_mkApps. cbn.
    rewrite iota_red_subst_instance. econstructor.
  - cbn. rewrite !subst_instance_constr_mkApps. cbn.
    econstructor.
    + unfold unfold_fix in *. destruct (nth_error mfix idx) eqn:E.
      * destruct (isLambda (dbody d)) eqn:E2; inversion H.
        rewrite nth_error_map, E. cbn.
        destruct d. cbn in *. destruct dbody; cbn in *; try congruence.
        repeat f_equal. rewrite <- subst_subst_instance_constr.
        f_equal. eapply fix_subst_subst_instance.
        rewrite fix_subst_subst_instance.
        now rewrite subst_subst_instance_constr.
      * inversion H.
    + unfold is_constructor in *.
      destruct (nth_error args narg) eqn:E; inversion H0; clear H0.
      rewrite nth_error_map, E. cbn.
      eapply isConstruct_app_subst_instance.
  - cbn. rewrite !subst_instance_constr_mkApps.
    unfold unfold_cofix in *. destruct (nth_error mfix idx) eqn:E.
    inversion H.
    econstructor. fold subst_instance_constr.
    unfold unfold_cofix.
    rewrite nth_error_map, E. cbn.
    rewrite <- subst_subst_instance_constr.
    now rewrite cofix_subst_subst_instance.
    econstructor. fold subst_instance_constr.
    inversion H.
  - cbn. unfold unfold_cofix in *.
    destruct nth_error eqn:E; inversion H.
    rewrite !subst_instance_constr_mkApps.
    econstructor. fold subst_instance_constr.
    unfold unfold_cofix.
    rewrite nth_error_map. destruct nth_error; cbn.
    rewrite cofix_subst_subst_instance.
    rewrite subst_subst_instance_constr. all: now inversion E. 
  - cbn. rewrite subst_instance_constr_two. econstructor; eauto.
  - cbn. rewrite !subst_instance_constr_mkApps.
    econstructor. now rewrite nth_error_map, H.
  - cbn. econstructor; eauto.
    eapply OnOne2_map. eapply OnOne2_impl. eassumption.
    firstorder.
  - cbn; econstructor;
    eapply OnOne2_map; eapply OnOne2_impl; [ eassumption | firstorder].
  - cbn; econstructor;
      eapply OnOne2_map; eapply OnOne2_impl; [ eassumption | ].
    intros. destruct X1. destruct p. inversion e. destruct x, y; cbn in *; subst.
    red. split; cbn; eauto.
  - cbn. eapply fix_red_body.
      eapply OnOne2_map; eapply OnOne2_impl; [ eassumption | ].
    intros. destruct X1. destruct p. inversion e. destruct x, y; cbn in *; subst.
    red. split; cbn; eauto.
    rewrite fix_context_subst_instance.
    unfold subst_instance_context, map_context in *. rewrite map_app in *. eassumption.
  - cbn; econstructor;
      eapply OnOne2_map; eapply OnOne2_impl; [ eassumption | ].
    intros. destruct X1. destruct p. inversion e. destruct x, y; cbn in *; subst.
    red. split; cbn; eauto.
  - cbn. eapply cofix_red_body.
      eapply OnOne2_map; eapply OnOne2_impl; [ eassumption | ].
    intros. destruct X1. destruct p. inversion e. destruct x, y; cbn in *; subst.
    red. split; cbn; eauto.
    rewrite fix_context_subst_instance.
    unfold subst_instance_context, map_context in *. rewrite map_app in *. eassumption.
    Grab Existential Variables. all:repeat econstructor.                                  
Qed.

Lemma leq_term_subst_instance:
  forall (cf : checker_flags) (Σ : global_env_ext) (u : universe_instance)
    (univs : universes_decl),
    consistent_instance_ext (Σ.1, univs) Σ.2 u ->
    forall t u0 : term,
      leq_term (global_ext_constraints Σ) t u0 ->
      leq_term (global_ext_constraints (Σ.1, univs)) (subst_instance_constr u t)
               (subst_instance_constr u u0).
Proof.
  intros cf Σ u univs H t u0 l.
Admitted.

Lemma cumul_subst_instance {cf:checker_flags} (Σ : global_env_ext) Γ u A B univs :
  wf Σ ->
  consistent_instance_ext (Σ.1,univs) (Σ.2) u ->
  Σ ;;; Γ |- A <= B ->
  (Σ.1,univs) ;;; subst_instance_context u Γ |- (subst_instance_constr u A) <= (subst_instance_constr u B).
Proof.
  intros. induction X0.
  - econstructor. now eapply leq_term_subst_instance.    
  - econstructor 2. eapply red1_subst_instance; eauto. eauto.
  - econstructor 3. eauto. eapply red1_subst_instance; eauto.
Qed.

Lemma subst_instance_context_app u L1 L2 :
  subst_instance_context u (L1,,,L2) = subst_instance_context u L1 ,,, subst_instance_context u L2.
Proof.
  unfold subst_instance_context, map_context; now rewrite map_app.
Qed.

Lemma typing_subst_instance `{cf : checker_flags} :
  forall Σ : global_env_ext, wf Σ ->
  forall Γ, wf_local Σ Γ ->
  forall t T, Σ ;;; Γ |- t : T ->
    forall u univs,
      consistent_instance_ext (Σ.1,univs) (Σ.2) u ->
      wf_local (Σ.1, univs) (subst_instance_context u Γ) ->
      (Σ.1,univs) ;;; subst_instance_context u Γ |- subst_instance_constr u t : subst_instance_constr u T.
Proof.
  apply (typing_ind_env (fun Σ Γ t T =>
                           forall u univs,
                             consistent_instance_ext (Σ.1,univs) (Σ.2) u ->
                             wf_local (Σ.1, univs) (subst_instance_context u Γ) ->
      (Σ.1,univs) ;;; _ |- PCUICUnivSubst.subst_instance_constr u t : PCUICUnivSubst.subst_instance_constr u T)); intros; cbn -[PCUICUnivSubst.subst_instance_constr] in *.
  - cbn. rewrite <- lift_subst_instance_constr.
    rewrite map_decl_type. econstructor.
    eauto.
    unfold subst_instance_context, map_context.
    now rewrite nth_error_map, H.
  - cbn -[Universe.make]. rewrite subst_instance_univ_super, subst_instance_univ_make.
    econstructor. eauto. eapply LevelIn_subst_instance; eauto.
  - cbn. 

    rewrite product_subst_instance. econstructor. eapply X1; eauto.
    eapply X3; eauto. econstructor. eauto. cbn.
    econstructor. cbn in X1. eapply X1 in X4; eauto.
  - cbn. econstructor. eapply X1. eauto. eauto. eapply X3. eauto.
    econstructor.  cbn in X1. eauto. cbn. eapply X1 in X4; eauto.
  - cbn. econstructor; eauto. eapply X5. eauto.
    econstructor.  cbn in X1. eauto. cbn. eapply X1 in X6; eauto.
    cbn. eapply X3 in X6. eauto. eauto.
  - cbn. unfold subst1. rewrite <- subst_subst_instance_constr. cbn. econstructor.
    + cbn. eapply X1; eauto.
    + eapply X3; eauto.
  - cbn. rewrite subst_instance_constr_two. econstructor; eauto.
  - cbn. erewrite <- (@ind_type_map (fun _ => subst_instance_constr u)).
    erewrite <- (@ind_type_map (fun _ => subst_instance_constr u0)).
    destruct idecl as [a b c d e] eqn:E. cbn.       
    assert (b = (idecl.(ind_type))) as -> by now subst.
    
    rewrite subst_instance_constr_two. econstructor.
    2:{ rewrite E in *. clear E. cbn in *. eassumption. }
    2:{ rewrite E in *. clear E. cbn in *.         
        eapply consistent_ext_trans; eauto. }
    eauto.
  - cbn. admit.                  (* type of constructor *)
  - cbn. rewrite subst_instance_constr_mkApps in *.
    rewrite map_app. cbn. rewrite map_skipn. econstructor; eauto.
    + admit.                          (* types_of_case *)
    + admit.                          (* check_correct_arity *)
    + eapply X4 in H3. rewrite subst_instance_constr_mkApps in H3. eassumption. eauto.
    + eapply All2_map with (f := (on_snd (subst_instance_constr u0))) (g:= (on_snd (subst_instance_constr u0))). eapply All2_impl. eassumption. intros.
      destruct X7. destruct p0. split. cbn. eauto. cbn.
      destruct x, y; cbn in *; subst.
      eapply t. eauto. eauto.
  - cbn. unfold subst1. rewrite <- subst_subst_instance_constr. cbn.
    rewrite !subst_instance_constr_two.
    rewrite map_rev. econstructor; eauto. 2:now rewrite map_length.
    eapply X2 in H0. rewrite subst_instance_constr_mkApps in H0.
    eassumption. eauto.
  - cbn.

    assert (Hw :  wf_local (Σ.1, univs) (subst_instance_context u (Γ ,,, types))).
    { (* rewrite subst_instance_context_app. *)
      apply All_local_env_app in X as [X Hfixc].
      
      revert Hfixc. clear - H1 X1.
      induction 1.
      - eauto.
      - cbn. econstructor; eauto. cbn in *.
        destruct t0 as (? & ? & ?). eexists.
        eapply t1 in H1. eapply H1. eauto.
      - cbn. econstructor; eauto. cbn in *.
        destruct t0 as (? & ? & ?). eexists.
        eapply t2 in H1. eapply H1. eauto.
        cbn. eapply t1 in H1. eapply H1. eauto.
    } 

    erewrite map_dtype. econstructor. admit. (* fix_guard *)
    rewrite nth_error_map, H. cbn. reflexivity. destruct mfix. destruct n; inv H. eapply typing_wf_local.

    inv X0. destruct X2. eapply t in H1.
    
    unfold subst_instance_context, map_context, app_context in *.
    rewrite map_app in H1. subst types.
    rewrite fix_context_subst_instance. eassumption.
    
    eauto.
    
    eapply All_map. eapply All_impl. eassumption.
    intros. cbn in *. destruct X2. destruct p. split.
    + specialize (t u univs).  erewrite map_dbody in t.
      rewrite <- lift_subst_instance_constr in *. subst. rewrite fix_context_length, map_length in *.
      erewrite map_dtype with (d := x) in t.
      unfold subst_instance_context, map_context in *.
      rewrite map_app in *. subst types.

      rewrite fix_context_subst_instance.
      eapply t. eauto. eauto.
    + cbn. destruct x. cbn in *. destruct dbody; cbn in *; congruence.
  - cbn.
    
    assert (Hw :  wf_local (Σ.1, univs) (subst_instance_context u (Γ ,,, types))).
    { (* rewrite subst_instance_context_app. *)
      apply All_local_env_app in X as [X Hfixc].
      
      revert Hfixc. clear - H1 X1.
      induction 1.
      - eauto.
      - cbn. econstructor; eauto. cbn in *.
        destruct t0 as (? & ? & ?). eexists.
        eapply t1 in H1. eapply H1. eauto.
      - cbn. econstructor; eauto. cbn in *.
        destruct t0 as (? & ? & ?). eexists.
        eapply t2 in H1. eapply H1. eauto.
        cbn. eapply t1 in H1. eapply H1. eauto.
    } 

    erewrite map_dtype. econstructor. admit. (* fix_guard *)
    rewrite nth_error_map, H. cbn. reflexivity. destruct mfix. destruct n; inv H. eapply typing_wf_local.

    inv X0. destruct X2. eapply t0 in H1.
    
    unfold subst_instance_context, map_context, app_context in *.
    rewrite map_app in H1. subst types.
    rewrite fix_context_subst_instance. eassumption. eauto.
    
    eapply All_map. eapply All_impl. eassumption.
    intros. cbn in *. destruct X2. unfold compose.
    cbn. specialize (t0 u univs).  erewrite map_dbody in t0.
    rewrite <- lift_subst_instance_constr in *. subst. rewrite fix_context_length, map_length in *.
    erewrite map_dtype with (d := x) in t.
    unfold subst_instance_context, map_context in *.
    rewrite map_app in *. subst types.

    rewrite fix_context_subst_instance.
    eapply t0. eauto. eauto.
  - econstructor. eapply X1. eauto. eauto.
    + destruct X2.
      * destruct i as (? & ?). left. eapply isWfArity_subst_instance; eauto.
      * destruct s as (? & ? & ?). right. eexists. eapply t1. eauto. eauto.
    + eapply cumul_subst_instance; eauto.
Admitted.
