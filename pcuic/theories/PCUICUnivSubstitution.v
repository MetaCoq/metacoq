(* Distributed under the terms of the MIT license.   *)

(** * Universe Substitution lemmas for typing derivations. *)

From Coq Require Import Bool String List BinPos Compare_dec Arith Lia.
Require Import Coq.Program.Syntax Coq.Program.Basics.
From MetaCoq.Template Require Import utils config AstUtils UnivSubst.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICLiftSubst
     PCUICUnivSubst PCUICTyping PCUICWeakeningEnv PCUICClosed
     PCUICReduction PCUICCumulativity PCUICWeakening PCUICUnivSubst.
(* Require Import ssreflect. *)

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

Lemma wf_local_subst_instance:
  forall (cf : checker_flags) (Σ : global_env × universes_decl) (Γ : context),
    wf_local Σ Γ ->
    forall (u0 : universe_instance) (univs : universes_decl),
      consistent_instance_ext (Σ.1, univs) Σ.2 u0 -> wf_local (Σ.1, univs) (subst_instance_context u0 Γ).
Proof.
  intros cf Σ Γ wfΓ u0 univs H0.
Admitted. 

Hint Resolve consistent_ext_trans. 
Hint Resolve wf_local_subst_instance. 

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

Lemma typing_subst_instance `{cf : checker_flags} :
  forall Σ : global_env_ext, wf Σ ->
  forall Γ, wf_local Σ Γ ->
  forall t T, Σ ;;; Γ |- t : T ->
    forall u univs,
      consistent_instance_ext (Σ.1,univs) (Σ.2) u ->
      (Σ.1,univs) ;;; subst_instance_context u Γ |- subst_instance_constr u t : subst_instance_constr u T.
Proof.
  apply (typing_ind_env (fun Σ Γ t T =>
                           forall u univs,
      consistent_instance_ext (Σ.1,univs) (Σ.2) u ->
      (Σ.1,univs) ;;; _ |- PCUICUnivSubst.subst_instance_constr u t : PCUICUnivSubst.subst_instance_constr u T)); intros; cbn -[PCUICUnivSubst.subst_instance_constr] in *.
  - cbn. rewrite <- lift_subst_instance_constr.
    rewrite map_decl_type. econstructor. eauto.
    unfold subst_instance_context, map_context.
    now rewrite nth_error_map, H.
  - cbn -[Universe.make]. rewrite subst_instance_univ_super, subst_instance_univ_make.
    econstructor. eauto. eapply LevelIn_subst_instance; eauto.
  - cbn.

    rewrite product_subst_instance. econstructor. eapply X1; eauto.
    eapply X3; eauto.
  - cbn. econstructor. eapply X1. eauto. eapply X3. eauto.
  - cbn. econstructor; eauto. eapply X5. eauto.
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

    eapply wf_local_subst_instance; eauto.    
  - cbn. admit.                  (* type of constructor *)
  - cbn. rewrite subst_instance_constr_mkApps in *.
    rewrite map_app. cbn. rewrite map_skipn. econstructor; eauto.
    + admit.                          (* types_of_case *)
    + admit.                          (* check_correct_arity *)
    + eapply X4 in H3. rewrite subst_instance_constr_mkApps in H3. eassumption.
    + eapply All2_map with (f := (on_snd (subst_instance_constr u0))) (g:= (on_snd (subst_instance_constr u0))). eapply All2_impl. eassumption. intros.
      destruct X6. destruct p0. split. cbn. eauto. cbn. eapply t. eauto.
  - cbn. unfold subst1. rewrite <- subst_subst_instance_constr. cbn.
    rewrite !subst_instance_constr_two.
    rewrite map_rev. econstructor; eauto. 2:now rewrite map_length.
    eapply X2 in H0. rewrite subst_instance_constr_mkApps in H0.
    eassumption.
  - cbn. erewrite map_dtype. econstructor. admit. (* fix_guard *)
    rewrite nth_error_map, H. cbn. reflexivity. destruct mfix. destruct n; inv H. eapply typing_wf_local.

    inv X0. destruct X1. eapply t in H1.
    
    unfold subst_instance_context, map_context, app_context in *.
    rewrite map_app in H1. subst types.
    rewrite fix_context_subst_instance. eassumption.
    
    eapply All_map. eapply All_impl. eassumption.
    intros. cbn in *. destruct X1. destruct p. split.
    + specialize (t u univs).  erewrite map_dbody in t.
      rewrite <- lift_subst_instance_constr in *. subst. rewrite fix_context_length, map_length in *.
      erewrite map_dtype with (d := x) in t.
      unfold subst_instance_context, map_context in *.
      rewrite map_app in *. subst types.

      rewrite fix_context_subst_instance.
      eapply t. eauto.
    + cbn. destruct x. cbn in *. destruct dbody; cbn in *; congruence.
  - cbn. erewrite map_dtype. econstructor. admit. (* fix_guard *)
    rewrite nth_error_map, H. cbn. reflexivity. destruct mfix. destruct n; inv H. eapply typing_wf_local.

    inv X0. destruct X1. eapply t0 in H1.
    
    unfold subst_instance_context, map_context, app_context in *.
    rewrite map_app in H1. subst types.
    rewrite fix_context_subst_instance. eassumption.
    
    eapply All_map. eapply All_impl. eassumption.
    intros. cbn in *. destruct X1. unfold compose.
    cbn. specialize (t0 u univs).  erewrite map_dbody in t0.
    rewrite <- lift_subst_instance_constr in *. subst. rewrite fix_context_length, map_length in *.
    erewrite map_dtype with (d := x) in t.
    unfold subst_instance_context, map_context in *.
    rewrite map_app in *. subst types.

    rewrite fix_context_subst_instance.
    eapply t0. eauto.
  - econstructor. eapply X1. eauto.
    + destruct X2.
      * destruct i as (? & ?). left. eapply isWfArity_subst_instance; eauto.
      * destruct s as (? & ? & ?). right. eexists. eapply t1. eauto.
    + admit.                    (* cumul *)
Admitted.
