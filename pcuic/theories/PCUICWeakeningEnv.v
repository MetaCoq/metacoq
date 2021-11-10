(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
  PCUICEquality PCUICContextSubst PCUICUnivSubst PCUICCases
  PCUICTyping PCUICContextRelation PCUICGlobalEnv.
From Equations Require Import Equations.

Require Import ssreflect.

Set Default Goal Selector "!".
Implicit Types (cf : checker_flags).

Lemma global_ext_constraints_app Σ Σ' φ
  : ConstraintSet.Subset (global_ext_constraints (Σ, φ))
                         (global_ext_constraints (Σ' ++ Σ, φ)).
Proof.
  unfold global_ext_constraints; simpl.
  intros ctr Hc. apply ConstraintSet.union_spec in Hc.
  apply ConstraintSet.union_spec.
  destruct Hc as [Hc|Hc]; [now left|right]. clear φ.
  induction Σ' in ctr, Hc |- *.
  - now rewrite app_nil_l.
  - simpl. apply ConstraintSet.union_spec. right; eauto.
Qed.

Lemma satisfies_subset φ φ' val :
  ConstraintSet.Subset φ φ' ->
  satisfies val φ' ->
  satisfies val φ.
Proof.
  intros sub sat ? isin.
  apply sat, sub; auto.
Qed.

Lemma leq_universe_subset {cf:checker_flags} ctrs ctrs' t u
  : ConstraintSet.Subset ctrs ctrs'
    -> leq_universe ctrs t u -> leq_universe ctrs' t u.
Proof.
  intros Hctrs H. unfold leq_universe in *.
  destruct check_univs; [|trivial].
  intros v Hv. apply H.
  eapply satisfies_subset; eauto.
Qed.

Lemma eq_universe_subset {cf:checker_flags} ctrs ctrs' t u
  : ConstraintSet.Subset ctrs ctrs'
    -> eq_universe ctrs t u -> eq_universe ctrs' t u.
Proof.
  intros Hctrs H. unfold eq_universe in *.
  destruct check_univs; [|trivial].
  intros v Hv. apply H.
  eapply satisfies_subset; eauto.
Qed.

Lemma leq_term_subset {cf:checker_flags} Σ ctrs ctrs' t u
  : ConstraintSet.Subset ctrs ctrs' -> leq_term Σ ctrs t u -> leq_term Σ ctrs' t u.
Proof.
  intro H. apply eq_term_upto_univ_impl; auto.
  - intros t' u'. eapply eq_universe_subset; assumption.
  - intros t' u'. eapply leq_universe_subset; assumption.
  - intros t' u' eq. apply eq_universe_leq_universe'.
    eapply eq_universe_subset; eauto.
Qed.

(** * Weakening lemmas w.r.t. the global environment *)

Generalizable Variables Σ Γ t T.

Definition weaken_env_prop_full {cf:checker_flags}
  (P : global_env_ext -> context -> term -> term -> Type) :=
  forall (Σ : global_env_ext) (Σ' : global_env), wf Σ' -> extends Σ.1 Σ' ->
                                      forall Γ t T, P Σ Γ t T -> P (Σ', Σ.2) Γ t T.

Lemma weakening_env_global_ext_levels Σ Σ' φ (H : extends Σ Σ') l
  : LevelSet.In l (global_ext_levels (Σ, φ))
    -> LevelSet.In l (global_ext_levels (Σ', φ)).
Proof.
  unfold global_ext_levels; simpl.
  intros Hl. apply LevelSet.union_spec in Hl.
  apply LevelSet.union_spec.
  destruct Hl as [Hl|Hl]; [now left|right]. clear φ.
  destruct H as [Σ'' eq]; subst.
  induction Σ'' in l, Hl |- *.
  - now rewrite app_nil_l.
  - simpl. apply LevelSet.union_spec. right; eauto.
Qed.

Lemma weakening_env_global_ext_levels' Σ Σ' φ (H : extends Σ Σ') l
  : LevelSet.mem l (global_ext_levels (Σ, φ))
    -> LevelSet.mem l (global_ext_levels (Σ', φ)).
Proof.
  intro HH. apply LevelSet.mem_spec in HH.
  now eapply LevelSet.mem_spec, weakening_env_global_ext_levels.
Qed.


Lemma weakening_env_global_ext_constraints Σ Σ' φ (H : extends Σ Σ')
  : ConstraintSet.Subset (global_ext_constraints (Σ, φ))
                         (global_ext_constraints (Σ', φ)).
Proof.
  destruct H as [Σ'' eq]. subst.
  apply global_ext_constraints_app.
Qed.

Lemma eq_term_subset {cf:checker_flags} Σ φ φ' t t'
  : ConstraintSet.Subset φ φ'
    -> eq_term Σ φ t t' -> eq_term Σ φ' t t'.
Proof.
  intro H. apply eq_term_upto_univ_impl; auto.
  all: intros u u'; eapply eq_universe_subset; assumption.
Qed.

Lemma compare_term_subset {cf:checker_flags} le Σ φ φ' t t'
  : ConstraintSet.Subset φ φ'
    -> compare_term le Σ φ t t' -> compare_term le Σ φ' t t'.
Proof.
  destruct le; [apply leq_term_subset|apply eq_term_subset].
Qed.

Lemma eq_decl_subset {cf:checker_flags} le Σ φ φ' d d'
  : ConstraintSet.Subset φ φ'
    -> eq_decl le Σ φ d d' -> eq_decl le Σ φ' d d'.
Proof.
  intros Hφ []; constructor; destruct le;
  eauto using leq_term_subset, eq_term_subset.
Qed.

Lemma eq_context_subset {cf:checker_flags} le Σ φ φ' Γ Γ'
  : ConstraintSet.Subset φ φ'
    -> eq_context le Σ φ Γ Γ' ->  eq_context le Σ φ' Γ Γ'.
Proof.
  intros Hφ. induction 1; constructor; auto; eapply eq_decl_subset; eassumption.
Qed.

Ltac my_rename_hyp h th :=
  match th with
  | (extends ?t _) => fresh "ext" t
  | (extends ?t.1 _) => fresh "ext" t
  | (extends _ _) => fresh "ext"
  | _ => PCUICTyping.my_rename_hyp h th
  end.

Ltac rename_hyp h ht ::= my_rename_hyp h ht.

Lemma lookup_env_Some_fresh `{checker_flags} Σ c decl :
  lookup_env Σ c = Some decl -> ~ (fresh_global c Σ).
Proof.
  induction Σ; cbn. 1: congruence.
  unfold eq_kername; destruct kername_eq_dec; subst.
  - intros [= <-] H2. inv H2.
    contradiction.
  - intros H1 H2. apply IHΣ; tas.
    now inv H2.
Qed.

Lemma extends_lookup `{checker_flags} Σ Σ' c decl :
  wf Σ' ->
  extends Σ Σ' ->
  lookup_env Σ c = Some decl ->
  lookup_env Σ' c = Some decl.
Proof.
  intros wfΣ' [Σ'' ->]. simpl.
  induction Σ'' in wfΣ', c, decl |- *.
  - simpl. auto.
  - specialize (IHΣ'' c decl). forward IHΣ''.
    + inv wfΣ'. simpl in X0. apply X.
    + intros HΣ. specialize (IHΣ'' HΣ).
      inv wfΣ'. simpl in *.
      unfold eq_kername; destruct kername_eq_dec; subst; auto.
      apply lookup_env_Some_fresh in IHΣ''; contradiction.
Qed.
#[global]
Hint Resolve extends_lookup : extends.

Lemma weakening_env_declared_constant `{CF:checker_flags}:
  forall (Σ : global_env) cst (decl : constant_body),
    declared_constant Σ cst decl ->
    forall Σ' : global_env, wf Σ' -> extends Σ Σ' -> declared_constant Σ' cst decl.
Proof.
  intros Σ cst decl H0 Σ' X2 H2.
  eapply extends_lookup; eauto.
Qed.
#[global] Hint Resolve weakening_env_declared_constant : extends.

Lemma weakening_env_declared_minductive `{CF:checker_flags}:
  forall (Σ : global_env) ind decl,
    declared_minductive Σ ind decl ->
    forall Σ' : global_env, wf Σ' -> extends Σ Σ' -> declared_minductive Σ' ind decl.
Proof.
  intros Σ cst decl H0 Σ' X2 H2.
  eapply extends_lookup; eauto.
Qed.
#[global] Hint Resolve weakening_env_declared_minductive : extends.

Lemma weakening_env_declared_inductive:
  forall (H : checker_flags) (Σ : global_env) ind mdecl decl,
    declared_inductive Σ mdecl ind decl ->
    forall Σ' : global_env, wf Σ' -> extends Σ Σ' -> declared_inductive Σ' mdecl ind decl.
Proof.
  intros H Σ cst decl H0 [Hmdecl Hidecl] Σ' X2 H2. split; eauto with extends.
Qed.
#[global] Hint Resolve weakening_env_declared_inductive : extends.

Lemma weakening_env_declared_constructor :
  forall (H : checker_flags) (Σ : global_env) ind mdecl idecl decl,
    declared_constructor Σ idecl ind mdecl decl ->
    forall Σ' : global_env, wf Σ' -> extends Σ Σ' ->
    declared_constructor Σ' idecl ind mdecl decl.
Proof.
  intros H Σ cst mdecl idecl cdecl [Hidecl Hcdecl] Σ' X2 H2.
  split; eauto with extends.
Qed.
#[global] Hint Resolve weakening_env_declared_constructor : extends.

Lemma weakening_env_declared_projection :
  forall (H : checker_flags) (Σ : global_env) ind mdecl idecl cdecl pdecl,
    declared_projection Σ idecl ind mdecl cdecl pdecl ->
    forall Σ' : global_env, wf Σ' -> extends Σ Σ' ->
    declared_projection Σ' idecl ind mdecl cdecl pdecl.
Proof.
  intros H Σ cst mdecl idecl cdecl pdecl [Hidecl Hcdecl] Σ' X2 H2.
  split; eauto with extends.
Qed.
#[global] Hint Resolve weakening_env_declared_projection : extends.

Lemma extends_wf_local `{checker_flags} Σ Γ (wfΓ : wf_local Σ Γ) :
  All_local_env_over typing
      (fun Σ0 Γ0 wfΓ (t T : term) ty =>
         forall Σ' : global_env,
           wf Σ' ->
           extends Σ0 Σ' ->
           (Σ', Σ0.2);;; Γ0 |- t : T
      ) Σ Γ wfΓ ->
    forall Σ' : global_env, wf Σ' -> extends Σ Σ' -> wf_local (Σ', Σ.2) Γ.
Proof.
  intros X0 Σ' H0.
  induction X0 in H0 |- *; try econstructor; simpl in *; intuition auto.
  - destruct tu as [u Hu]; exists u; auto.
  - destruct tu as [u Hu]; exists u; auto.
Qed.
#[global]
Hint Resolve extends_wf_local : extends.

Lemma global_variance_sigma_mon {cf:checker_flags} {Σ Σ' gr napp v} : 
  wf Σ' -> extends Σ Σ' -> 
  global_variance Σ gr napp = Some v ->
  global_variance Σ' gr napp = Some v.
Proof.
  intros wf ext.
  rewrite /global_variance /lookup_constructor /lookup_inductive /lookup_minductive.
  destruct gr as [|ind|[ind i]|] => /= //.
  - destruct (lookup_env Σ ind) eqn:look => //.
    eapply extends_lookup in look; eauto. rewrite look //.
  - destruct (lookup_env Σ (inductive_mind i)) eqn:look => //.
    eapply extends_lookup in look; eauto. rewrite look //.
Qed.

(** The definition of [R_global_instance] is defined so that it is weakenable. *)
Lemma R_global_instance_weaken_env {cf:checker_flags} Σ Σ' Re Re' Rle Rle' gr napp :
  wf Σ' -> extends Σ Σ' ->
  RelationClasses.subrelation Re Re' ->
  RelationClasses.subrelation Rle Rle' ->
  RelationClasses.subrelation Re Rle' ->
  subrelation (R_global_instance Σ Re Rle gr napp) (R_global_instance Σ' Re' Rle' gr napp).
Proof.
  intros wfΣ ext he hle hele t t'.
  rewrite /R_global_instance /R_opt_variance.
  destruct global_variance as [v|] eqn:look.
  - rewrite (global_variance_sigma_mon wfΣ ext look).
    induction t in v, t' |- *; destruct v, t'; simpl; auto.
    intros []; split; auto.
    destruct t0; simpl; auto.
  - destruct (global_variance Σ' gr napp) => //.
    * induction t in l, t' |- *; destruct l,  t'; simpl; intros H; inv H; auto.
      split; auto. destruct t0; simpl; auto.
    * eauto using R_universe_instance_impl'.
Qed.

#[global]
Instance eq_term_upto_univ_weaken_env {cf:checker_flags} Σ Σ' Re Re' Rle Rle' napp :
  wf Σ' -> extends Σ Σ' ->
  RelationClasses.subrelation Re Re' ->
  RelationClasses.subrelation Rle Rle' ->
  RelationClasses.subrelation Re Rle' ->
  CRelationClasses.subrelation (eq_term_upto_univ_napp Σ Re Rle napp) 
    (eq_term_upto_univ_napp Σ' Re' Rle' napp).
Proof.
  intros wfΣ ext he hele hle t t'.
  induction t in napp, t', Rle, Rle', hle, hele |- * using PCUICInduction.term_forall_list_ind;
    try (inversion 1; subst; constructor;
         eauto using R_universe_instance_impl'; fail).
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
  - inversion 1; subst; constructor.
    eapply R_global_instance_weaken_env. 6:eauto. all:eauto.
  - inversion 1; subst; constructor.
    eapply R_global_instance_weaken_env. 6:eauto. all:eauto.
  - inversion 1; subst; destruct X as [? [? ?]]; constructor; eauto.
    * destruct X2 as [? [? ?]].
      constructor; intuition auto; solve_all.
      + eauto using R_universe_instance_impl'.
    * eapply All2_impl'; tea.
      eapply All_impl; eauto.
      cbn. intros x [? ?] y [? ?]. split; eauto.
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x [? ?] y [[[? ?] ?] ?]. repeat split; eauto.
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x [? ?] y [[[? ?] ?] ?]. repeat split; eauto.
Qed.

Lemma weakening_env_red1 `{CF:checker_flags} Σ Σ' Γ M N :
  wf Σ' ->
  extends Σ Σ' ->
  red1 Σ Γ M N ->
  red1 Σ' Γ M N.
Proof.
  induction 3 using red1_ind_all;
    try solve [econstructor; eauto with extends; solve_all].
Qed.

Lemma weakening_env_conv `{CF:checker_flags} Σ Σ' φ Γ M N :
  wf Σ' ->
  extends Σ Σ' ->
  conv (Σ, φ) Γ M N ->
  conv (Σ', φ) Γ M N.
Proof.
  intros wfΣ [Σ'' ->].
  induction 1; simpl.
  - econstructor. eapply eq_term_subset.
    + eapply global_ext_constraints_app.
    + simpl in *. eapply eq_term_upto_univ_weaken_env in e; simpl; eauto.
      1:exists Σ''; eauto.
      all:typeclasses eauto.
  - econstructor 2; eauto. eapply weakening_env_red1; eauto. exists Σ''; eauto.
  - econstructor 3; eauto. eapply weakening_env_red1; eauto. exists Σ''; eauto.
Qed.

Lemma weakening_env_cumul `{CF:checker_flags} Σ Σ' φ Γ M N :
  wf Σ' ->
  extends Σ Σ' ->
  cumul (Σ, φ) Γ M N ->
  cumul (Σ', φ) Γ M N.
Proof.
  intros wfΣ [Σ'' ->].
  induction 1; simpl.
  - econstructor. eapply leq_term_subset.
    + eapply global_ext_constraints_app.
    + simpl in *. eapply eq_term_upto_univ_weaken_env in l; simpl; eauto.
      1:exists Σ''; eauto.
      all:typeclasses eauto.
  - econstructor 2; eauto. eapply weakening_env_red1; eauto. exists Σ''; eauto.
  - econstructor 3; eauto. eapply weakening_env_red1; eauto. exists Σ''; eauto.
Qed.

Lemma weakening_env_conv_decls {cf} {Σ φ Σ' Γ Γ'} :
  wf Σ' -> extends Σ Σ' ->
  CRelationClasses.subrelation (conv_decls (Σ, φ) Γ Γ') (conv_decls (Σ', φ) Γ Γ').
Proof.
  intros wf ext d d' Hd; depelim Hd; constructor; tas;
    eapply weakening_env_conv; tea.
Qed.

Lemma weakening_env_cumul_decls {cf} {Σ φ Σ' Γ Γ'} :
  wf Σ' -> extends Σ Σ' ->
  CRelationClasses.subrelation (cumul_decls (Σ, φ) Γ Γ') (cumul_decls (Σ', φ) Γ Γ').
Proof.
  intros wf ext d d' Hd; depelim Hd; constructor; tas;
    (eapply weakening_env_conv || eapply weakening_env_cumul); tea.
Qed.

Lemma weakening_env_conv_ctx {cf} {Σ Σ' φ Γ Δ} :
  wf Σ' ->
  extends Σ Σ' ->
  conv_context (Σ, φ) Γ Δ ->
  conv_context (Σ', φ) Γ Δ.
Proof.
  intros wf ext.
  intros; eapply All2_fold_impl; tea => Γ0 Γ' d d'.
  now eapply weakening_env_conv_decls.
Qed.

#[global]
Hint Resolve weakening_env_conv_ctx : extends.

Lemma weakening_env_cumul_ctx {cf} {Σ Σ' φ Γ Δ} :
  wf Σ' ->
  extends Σ Σ' ->
  cumul_context (Σ, φ) Γ Δ ->
  cumul_context (Σ', φ) Γ Δ.
Proof.
  intros wf ext.
  intros; eapply All2_fold_impl; tea => Γ0 Γ' d d'.
  now eapply weakening_env_cumul_decls.
Qed.
#[global]
Hint Resolve weakening_env_cumul_ctx : extends.

Lemma weakening_env_is_allowed_elimination `{CF:checker_flags} Σ Σ' φ u allowed :
  wf Σ' -> extends Σ Σ' ->
  is_allowed_elimination (global_ext_constraints (Σ, φ)) u allowed ->
  is_allowed_elimination (global_ext_constraints (Σ', φ)) u allowed.
Proof.
  intros wfΣ [Σ'' ->] al.
  unfold is_allowed_elimination in *.
  destruct check_univs; auto.
  intros val sat.
  unshelve epose proof (al val _) as al.
  { eapply satisfies_subset; eauto.
    apply global_ext_constraints_app. }
  destruct allowed; auto; cbn in *; destruct ?; auto.
Qed.
#[global]
Hint Resolve weakening_env_is_allowed_elimination : extends.

Lemma weakening_All_local_env_impl `{checker_flags}
      (P Q : context -> term -> option term -> Type) l :
  All_local_env P l ->
  (forall Γ t T, P Γ t T -> Q Γ t T) ->
  All_local_env Q l.
Proof.
  induction 1; intros; simpl; econstructor; eauto.
Qed.

#[global]
Hint Resolve weakening_env_global_ext_levels : extends.

Lemma weakening_env_consistent_instance {cf:checker_flags} Σ Σ' φ ctrs u (H : extends Σ Σ')
  : consistent_instance_ext (Σ, φ) ctrs u
    -> consistent_instance_ext (Σ', φ) ctrs u.
Proof.
    unfold consistent_instance_ext, consistent_instance.
    intros X.
    destruct ctrs; tas.
    intuition auto.
    - eapply forallb_Forall in H0; eapply forallb_Forall, Forall_impl; tea.
      intros x ?; now eapply weakening_env_global_ext_levels'.
    - eapply valid_subset; tea;
      now eapply weakening_env_global_ext_constraints.
Qed.
#[global]
Hint Resolve weakening_env_consistent_instance : extends.

Lemma extends_check_recursivity_kind {cf:checker_flags} Σ ind k Σ' : extends Σ Σ' -> wf Σ' -> 
  check_recursivity_kind Σ ind k -> check_recursivity_kind Σ' ind k.
Proof.
  intros ext wfΣ'.
  rewrite /check_recursivity_kind.
  destruct lookup_env eqn:Heq => //.
  eapply extends_lookup in Heq; eauto.
  now rewrite Heq.
Qed.

Lemma extends_wf_fixpoint {cf:checker_flags} Σ mfix Σ' : extends Σ Σ' -> wf Σ' ->
  wf_fixpoint Σ mfix -> wf_fixpoint Σ' mfix.
Proof.
  intros ext wfΣ'.
  unfold wf_fixpoint.
  destruct map_option_out as [[|ind inds]|]; auto.
  move/andb_and => [->] /=.
  now apply extends_check_recursivity_kind.
Qed.

Lemma extends_wf_cofixpoint {cf:checker_flags} Σ mfix Σ' : extends Σ Σ' -> wf Σ' ->
  wf_cofixpoint Σ mfix -> wf_cofixpoint Σ' mfix.
Proof.
  intros ext wfΣ'.
  unfold wf_cofixpoint.
  destruct map_option_out as [[|ind inds]|]; auto.
  move/andb_and => [->] /=.
  now apply extends_check_recursivity_kind.
Qed.

Lemma global_levels_Set Σ : 
  LevelSet.In Level.lSet (global_levels Σ).
Proof.
  unfold global_levels.
  induction Σ; simpl; auto.
  - now apply LevelSet.singleton_spec.
  - apply LevelSet.union_spec. right; auto.
Qed.

Lemma global_levels_set Σ : 
  LevelSet.Equal (LevelSet.union (LevelSet.singleton Level.lSet) (global_levels Σ))
  (global_levels Σ).
Proof.
  apply LevelSetProp.union_subset_equal.
  intros x hin. eapply LevelSet.singleton_spec in hin; subst x.
  apply global_levels_Set.
Qed.

Lemma global_levels_ext {Σ Σ'} : 
  LevelSet.Equal (global_levels (Σ ++ Σ')) (LevelSet.union (global_levels Σ) (global_levels Σ')).
Proof.
  unfold global_levels at 1.
  induction Σ; simpl.
  - rewrite global_levels_set. reflexivity.
  - rewrite IHΣ. lsets.
Qed.

Lemma extends_wf_universe {cf:checker_flags} {Σ : global_env_ext} Σ' u : extends Σ Σ' -> wf Σ' ->
  wf_universe Σ u -> wf_universe (Σ', Σ.2) u.
Proof.
  destruct Σ as [Σ univ]; cbn.
  intros [Σ'' eq] wf.
  destruct u; simpl; auto.
  intros Hl.
  intros l inl; specialize (Hl l inl).
  cbn. rewrite eq /=.
  unfold global_ext_levels.
  eapply LevelSet.union_spec; simpl.
  apply LevelSet.union_spec in Hl as [Hl|Hl]; cbn in Hl.
  - simpl. simpl in Hl. now left.
  - right. rewrite global_levels_ext.
    eapply LevelSet.union_spec. right.
    apply Hl.
Qed.

#[global]
Hint Resolve extends_wf_fixpoint extends_wf_cofixpoint : extends.

Lemma weakening_env `{checker_flags} :
  env_prop (fun Σ Γ t T =>
              forall Σ', wf Σ' -> extends Σ.1 Σ' -> (Σ', Σ.2) ;;; Γ |- t : T)
           (fun Σ Γ =>
             forall Σ', wf Σ' -> extends Σ.1 Σ' -> wf_local (Σ', Σ.2) Γ).
Proof.
  apply typing_ind_env; intros;
    rename_all_hyps; try solve [econstructor; eauto 2 with extends].

  - induction X; constructor; eauto 2 with extends.
    + eexists; eapply p; eauto.
    + eexists; eapply p0; eauto.
    + eapply p; eauto.
  - econstructor; eauto 2 with extends.
    now apply extends_wf_universe.
  - econstructor; eauto 2 with extends.
    * revert X6. clear -Σ' wfΣ' extΣ.
      induction 1; constructor; eauto with extends.
    * close_Forall. intros; intuition eauto with extends.
  - econstructor; eauto with extends.
    + eapply fix_guard_extends; eauto.
    + specialize (forall_Σ' _ wfΣ' extΣ).
      now apply wf_local_app_inv in forall_Σ'.
    + eapply (All_impl X0); simpl; intuition eauto with extends.
      destruct X as [s Hs]; exists s. intuition eauto with extends.
    + eapply All_impl; eauto; simpl; intuition eauto with extends.
  - econstructor; eauto with extends.
    + eapply cofix_guard_extends; eauto.
    + specialize (forall_Σ' _ wfΣ' extΣ).
      now apply wf_local_app_inv in forall_Σ'.
    + eapply (All_impl X0); simpl; intuition eauto with extends.
      destruct X as [s Hs]; exists s. intuition eauto with extends.
    + eapply All_impl; eauto; simpl; intuition eauto with extends.
  - econstructor. 1: eauto.
    + eapply forall_Σ'1; eauto.
    + destruct Σ as [Σ φ]. eapply weakening_env_cumul in cumulA; eauto.
Qed.

Definition weaken_env_prop `{checker_flags}
           (P : global_env_ext -> context -> term -> option term -> Type) :=
  forall Σ Σ' φ, wf Σ' -> extends Σ Σ' -> forall Γ t T, P (Σ, φ) Γ t T -> P (Σ', φ) Γ t T.

Lemma weakening_on_global_decl `{checker_flags} P Σ Σ' φ kn decl :
  weaken_env_prop P ->
  wf Σ' -> extends Σ Σ' ->
  on_global_decl P (Σ, φ) kn decl ->
  on_global_decl P (Σ', φ) kn decl.
Proof.
  unfold weaken_env_prop.
  intros HPΣ wfΣ' Hext Hdecl.
  destruct decl.
  1:{
    destruct c as [? [] ?].
    - simpl in *.
      red in Hdecl |- *. simpl in *.
      eapply HPΣ; eauto.
    - eapply HPΣ; eauto.
  }
  simpl in *.
  destruct Hdecl as [onI onP onnP]; constructor; eauto.
  - eapply Alli_impl; eauto. intros.
    destruct X. unshelve econstructor; eauto.
    + unfold on_type in *; intuition eauto.
    + unfold on_constructors in *. eapply All2_impl; eauto.
      intros.
      destruct X as [? ? ? ?]. unshelve econstructor; eauto.
      * unfold on_type in *; eauto.
      * clear on_cindices cstr_eq cstr_args_length.
        revert on_cargs.
        induction (cstr_args x0) in y |- *; destruct y; simpl in *; eauto.
        ** destruct a as [na [b|] ty]; simpl in *; intuition eauto.
        ** destruct a as [na [b|] ty]; simpl in *; intuition eauto.
      * clear on_ctype on_cargs.
        revert on_cindices.
        generalize (List.rev (lift_context #|cstr_args x0| 0 (ind_indices x))).
        generalize (cstr_indices x0).
        induction 1; constructor; eauto.
      * simpl.
        intros v indv. specialize (on_ctype_variance v indv).
        simpl in *. move: on_ctype_variance.
        unfold cstr_respects_variance. destruct variance_universes as [[[univs u] u']|]; auto.
        intros [args idxs]. split.
        ** eapply (All2_fold_impl args); intros.
           inversion X; constructor; auto.
           ++ eapply weakening_env_cumul; eauto.
           ++ eapply weakening_env_conv; eauto.
           ++ eapply weakening_env_cumul; eauto.
        ** eapply (All2_impl idxs); intros.
          eapply weakening_env_conv; eauto.
    + unfold check_ind_sorts in *.
      destruct Universe.is_prop; auto.
      destruct Universe.is_sprop; auto.
      split; [apply fst in ind_sorts|apply snd in ind_sorts].
      * eapply Forall_impl; tea; cbn.
        intros. eapply Forall_impl; tea; simpl; intros.
        eapply leq_universe_subset; tea.
        apply weakening_env_global_ext_constraints; tea.
      * destruct indices_matter; [|trivial]. clear -ind_sorts HPΣ wfΣ' Hext.
        induction ind_indices; simpl in *; auto.
        -- eapply (extends_wf_universe (Σ:=(Σ,φ)) Σ'); auto.
        -- destruct a as [na [b|] ty]; simpl in *; intuition eauto.
    + intros v onv.
      move: (onIndices v onv). unfold ind_respects_variance.
      destruct variance_universes as [[[univs u] u']|] => //.
      intros idx; eapply (All2_fold_impl idx); simpl.
      intros par par' t t' d.
      inv d; constructor; auto.
      ++ eapply weakening_env_cumul; eauto.
      ++ eapply weakening_env_conv; eauto.
      ++ eapply weakening_env_cumul; eauto.
  - red in onP |- *. eapply All_local_env_impl; eauto.
Qed.

Lemma weakening_env_lookup_on_global_env `{checker_flags} P Σ Σ' c decl :
  weaken_env_prop P ->
  wf Σ' -> extends Σ Σ' -> on_global_env P Σ ->
  lookup_env Σ c = Some decl ->
  on_global_decl P (Σ', universes_decl_of_decl decl) c decl.
Proof.
  intros HP wfΣ Hext HΣ.
  induction HΣ; simpl. 1: congruence.
  assert (HH: extends Σ Σ'). {
    destruct Hext as [Σ'' HΣ''].
    exists (Σ'' ++ [(kn, d)]). now rewrite <- app_assoc.
  }
  unfold eq_kername; destruct kername_eq_dec; subst.
  - intros [= ->]. subst.
    clear Hext; eapply weakening_on_global_decl; eauto.
  - now apply IHHΣ.
Qed.

Lemma weaken_lookup_on_global_env `{checker_flags} P Σ c decl :
  weaken_env_prop P ->
  wf Σ -> on_global_env P Σ ->
  lookup_env Σ c = Some decl ->
  on_global_decl P (Σ, universes_decl_of_decl decl) c decl.
Proof.
  intros. eapply weakening_env_lookup_on_global_env; eauto.
  exists []; simpl; destruct Σ; eauto.
Qed.

Lemma declared_constant_inv `{checker_flags} Σ P cst decl :
  weaken_env_prop (lift_typing P) ->
  wf Σ -> Forall_decls_typing P Σ ->
  declared_constant Σ cst decl ->
  on_constant_decl (lift_typing P) (Σ, cst_universes decl) decl.
Proof.
  intros.
  eapply weaken_lookup_on_global_env in X1; eauto. apply X1.
Qed.


Lemma declared_minductive_inv `{checker_flags} {Σ P ind mdecl} :
  weaken_env_prop (lift_typing P) ->
  wf Σ -> Forall_decls_typing P Σ ->
  declared_minductive Σ ind mdecl ->
  on_inductive (lift_typing P) (Σ, ind_universes mdecl) ind mdecl.
Proof.
  intros.
  eapply weaken_lookup_on_global_env in X1; eauto. apply X1.
Qed.

Lemma declared_inductive_inv `{checker_flags} {Σ P ind mdecl idecl} :
  weaken_env_prop (lift_typing P) ->
  wf Σ -> Forall_decls_typing P Σ ->
  declared_inductive Σ ind mdecl idecl ->
  on_ind_body (lift_typing P) (Σ, ind_universes mdecl) (inductive_mind ind) mdecl (inductive_ind ind) idecl.
Proof.
  intros.
  destruct H0 as [Hmdecl Hidecl].
  eapply declared_minductive_inv in Hmdecl; eauto.
  apply onInductives in Hmdecl.
  eapply nth_error_alli in Hidecl; eauto.
  apply Hidecl.
Qed.

Lemma declared_constructor_inv `{checker_flags} {Σ P mdecl idecl ref cdecl}
  (HP : weaken_env_prop (lift_typing P))
  (wfΣ : wf Σ)
  (HΣ : Forall_decls_typing P Σ)
  (Hdecl : declared_constructor Σ ref mdecl idecl cdecl) :
  ∑ cs,
  let onib := declared_inductive_inv HP wfΣ HΣ (let (x, _) := Hdecl in x) in
  nth_error onib.(ind_cunivs) ref.2 = Some cs
  × on_constructor (lift_typing P) (Σ, ind_universes mdecl) mdecl
                   (inductive_ind ref.1) idecl idecl.(ind_indices) cdecl cs.
Proof.
  intros.
  destruct Hdecl as [Hidecl Hcdecl].
  set (declared_inductive_inv HP wfΣ HΣ Hidecl) as HH.
  clearbody HH. pose proof HH.(onConstructors) as HH'.
  eapply All2_nth_error_Some in Hcdecl; tea.
Defined.

Lemma declared_projection_inv `{checker_flags} {Σ P mdecl idecl cdecl ref pdecl} :
  forall (HP : weaken_env_prop (lift_typing P))
  (wfΣ : wf Σ)
  (HΣ : Forall_decls_typing P Σ)
  (Hdecl : declared_projection Σ ref mdecl idecl cdecl pdecl),
  match idecl.(ind_ctors) return Type with
  | [c] => 
    let oib := declared_inductive_inv HP wfΣ HΣ (let (x, _) := Hdecl in 
      let (x, _) := x in x) in
    (match oib.(ind_cunivs) with
     | [cs] => sorts_local_ctx (lift_typing P) (Σ, ind_universes mdecl) (arities_context (ind_bodies mdecl) ,,, ind_params mdecl) (cstr_args c) cs
     | _ => False
    end) *
    on_projections mdecl (inductive_mind ref.1.1) (inductive_ind ref.1.1) idecl (idecl.(ind_indices)) c *
    ((snd ref) < context_assumptions c.(cstr_args)) *
    on_projection mdecl (inductive_mind ref.1.1) (inductive_ind ref.1.1) c (snd ref) pdecl
  | _ => False
  end.
Proof.
  intros.
  destruct (declared_inductive_inv HP wfΣ HΣ (let (x, _) := Hdecl in let (x, _) := x in x)) in *.
  destruct Hdecl as [Hidecl [Hcdecl Hnpar]]. simpl.
  forward onProjections.    
  { eapply nth_error_Some_length in Hcdecl.
    destruct (ind_projs idecl); simpl in *; try lia. congruence. }
  destruct (ind_ctors idecl) as [|? []]; try contradiction.
  destruct ind_cunivs as [|? []]; try contradiction; depelim onConstructors.
  2:{ depelim onConstructors. }
  intuition auto.
  - destruct onProjections.
    destruct (ind_ctors idecl) as [|? []]; simpl in *; try discriminate.
    inv onConstructors. now eapply on_cargs in o.
  - destruct onProjections. eapply nth_error_Some_length in Hcdecl. lia.
  - destruct onProjections.
    eapply nth_error_alli in Hcdecl; eauto. 
    eapply Hcdecl.
Qed.

Lemma wf_extends `{checker_flags} {Σ Σ'} : wf Σ' -> extends Σ Σ' -> wf Σ.
Proof.
  intros HΣ' [Σ'' ->]. simpl in *.
  induction Σ''; auto.
  inv HΣ'. auto.
Qed.

Lemma weaken_env_prop_typing `{checker_flags} : weaken_env_prop (lift_typing typing).
Proof.
  red. intros * wfΣ' Hext *.
  destruct T; simpl.
  - intros Ht. pose proof (wf_extends wfΣ' Hext).
    eapply (weakening_env (_, _)); eauto.
  - intros [s Ht]. pose proof (wf_extends wfΣ' Hext). exists s.
    eapply (weakening_env (_, _)); eauto.
Qed.

#[global]
Hint Unfold weaken_env_prop : pcuic.

Lemma on_declared_constant `{checker_flags} {Σ cst decl} :
  wf Σ -> declared_constant Σ cst decl ->
  on_constant_decl (lift_typing typing) (Σ, cst_universes decl) decl.
Proof.
  intros.
  eapply declared_constant_inv; tea.
  apply weaken_env_prop_typing.
Qed.

Lemma weaken_wf_local `{checker_flags} (Σ : global_env_ext) Σ' Γ :
  extends Σ Σ' -> wf Σ' -> wf_local Σ Γ -> wf_local (Σ', Σ.2) Γ.
Proof.
  intros * Hext wfΣ' *.
  intros wfΓ.
  eapply (env_prop_wf_local weakening_env); eauto.
  now eapply wf_extends.
Qed.

#[global]
Hint Resolve weaken_wf_local | 100 : pcuic.

Lemma on_declared_minductive `{checker_flags} {Σ ref decl} :
  wf Σ ->
  declared_minductive Σ ref decl ->
  on_inductive (lift_typing typing) (Σ, ind_universes decl) ref decl.
Proof.
  intros wfΣ Hdecl.
  apply (declared_minductive_inv weaken_env_prop_typing wfΣ wfΣ Hdecl).
Qed.

Lemma on_declared_inductive `{checker_flags} {Σ ref mdecl idecl} {wfΣ : wf Σ} :
  declared_inductive Σ ref mdecl idecl ->
  on_inductive (lift_typing typing) (Σ, ind_universes mdecl) (inductive_mind ref) mdecl *
  on_ind_body (lift_typing typing) (Σ, ind_universes mdecl) (inductive_mind ref) mdecl (inductive_ind ref) idecl.
Proof.
  intros Hdecl.
  split.
  - destruct Hdecl as [Hmdecl _]. now apply on_declared_minductive in Hmdecl.
  - apply (declared_inductive_inv weaken_env_prop_typing wfΣ wfΣ Hdecl).
Defined.

Lemma on_declared_constructor `{checker_flags} {Σ ref mdecl idecl cdecl}
  {wfΣ : wf Σ}
  (Hdecl : declared_constructor Σ ref mdecl idecl cdecl) :
  on_inductive (lift_typing typing) (Σ, ind_universes mdecl)
               (inductive_mind (fst ref)) mdecl *
  on_ind_body (lift_typing typing) (Σ, ind_universes mdecl)
              (inductive_mind (fst ref)) mdecl (inductive_ind (fst ref)) idecl *
  ∑ ind_ctor_sort,
    let onib := declared_inductive_inv weaken_env_prop_typing wfΣ wfΣ (let (x, _) := Hdecl in x) in
     nth_error (ind_cunivs onib) ref.2 = Some ind_ctor_sort
    ×  on_constructor (lift_typing typing) (Σ, ind_universes mdecl)
                 mdecl (inductive_ind (fst ref))
                 idecl idecl.(ind_indices) cdecl ind_ctor_sort.
Proof.
  split.
  - apply (on_declared_inductive Hdecl).
  - apply (declared_constructor_inv weaken_env_prop_typing wfΣ wfΣ Hdecl).
Defined.

Lemma on_declared_projection `{checker_flags} {Σ ref mdecl idecl cdecl pdecl} {wfΣ : wf Σ} 
  (Hdecl : declared_projection Σ ref mdecl idecl cdecl pdecl) :
  on_inductive (lift_typing typing) (Σ, ind_universes mdecl) (inductive_mind (fst (fst ref))) mdecl *
  (idecl.(ind_ctors) = [cdecl]) *
  let oib := declared_inductive_inv weaken_env_prop_typing wfΣ wfΣ (let (x, _) := Hdecl in let (x, _) := x in x) in
  (match oib.(ind_cunivs) with
  | [cs] => sorts_local_ctx (lift_typing typing) (Σ, ind_universes mdecl)
      (arities_context (ind_bodies mdecl) ,,, ind_params mdecl) (cstr_args cdecl) cs
    | _ => False
  end) *
  on_projections mdecl (inductive_mind ref.1.1) (inductive_ind ref.1.1) idecl (idecl.(ind_indices)) cdecl *
  ((snd ref) < context_assumptions cdecl.(cstr_args)) *
  on_projection mdecl (inductive_mind ref.1.1) (inductive_ind ref.1.1) cdecl (snd ref) pdecl.
Proof.
  have hctors : idecl.(ind_ctors) = [cdecl].
  { pose proof (declared_projection_inv weaken_env_prop_typing wfΣ wfΣ Hdecl).
    move: X. destruct Hdecl. destruct d. cbn in *.
    move: e. destruct (ind_ctors idecl) as [|? []] => //.
    intros [= ->] => //. }
  split. 
  - split => //. 
    apply (on_declared_inductive Hdecl).
  - pose proof (declared_projection_inv weaken_env_prop_typing wfΣ wfΣ Hdecl).
    destruct Hdecl. cbn in *. destruct d; cbn in *.
    now rewrite hctors in X.
Qed.

Definition on_udecl_prop `{checker_flags} Σ (udecl : universes_decl)
  := let levels := levels_of_udecl udecl in
     let global_levels := global_levels Σ in
     let all_levels := LevelSet.union levels global_levels in
     ConstraintSet.For_all (fun '(l1,_,l2) => LevelSet.In l1 all_levels
                                             /\ LevelSet.In l2 all_levels)
                             (constraints_of_udecl udecl)
     /\ match udecl with
       | Monomorphic_ctx ctx => LevelSet.for_all (negb ∘ Level.is_var) ctx.1
                               /\ LevelSet.Subset ctx.1 global_levels
                               /\ ConstraintSet.Subset ctx.2 (global_constraints Σ)
                               /\ satisfiable_udecl Σ udecl
       | _ => True
       end.

Lemma weaken_lookup_on_global_env' `{checker_flags} Σ c decl :
  wf Σ ->
  lookup_env Σ c = Some decl ->
  on_udecl_prop Σ (universes_decl_of_decl decl).
Proof.
  intros wfΣ HH.
  induction wfΣ; simpl. 1: discriminate.
  cbn in HH. subst udecl.
  unfold eq_kername in HH; destruct kername_eq_dec; subst.
  - apply some_inj in HH; destruct HH. subst.
    clear -o. unfold on_udecl, on_udecl_prop in *.
    destruct o as [H1 [H2 [H3 H4]]]. repeat split.
    + clear -H2. intros [[? ?] ?] Hc. specialize (H2 _ Hc).
      destruct H2 as [H H']. simpl. split.
      * apply LevelSet.union_spec in H. apply LevelSet.union_spec.
        destruct H; [now left|right]. apply LevelSet.union_spec; now right.
      * apply LevelSet.union_spec in H'. apply LevelSet.union_spec.
        destruct H'; [now left|right]. apply LevelSet.union_spec; now right.
    + revert H3. case_eq (universes_decl_of_decl d); trivial.
      intros ctx eq Hctx. repeat split.
      * auto.
      * intros l Hl. simpl. replace (monomorphic_levels_decl d) with ctx.1.
        -- apply LevelSet.union_spec; now left.
        -- clear -eq. destruct d as [c|c]; cbn in *.
           all: destruct c; cbn in *; now rewrite eq.
      * simpl. replace (monomorphic_constraints_decl d) with ctx.2.
        -- intros c Hc; apply ConstraintSet.union_spec; now left.
        -- clear -eq. destruct d as [c|c]; cbn in *.
           all: destruct c; cbn in *; now rewrite eq.
      * clear -eq H4. destruct H4 as [v Hv]. exists v.
      intros c Hc; apply (Hv c).
      apply ConstraintSet.union_spec in Hc; destruct Hc as [Hc|Hc].
      2: apply ConstraintSet.union_spec in Hc; destruct Hc as [Hc|Hc].
      -- apply ConstraintSet.union_spec. simpl in *. left; now rewrite eq.
      -- apply ConstraintSet.union_spec; left. simpl.
         destruct d as [[? ? []]|[? ? ? ? []]]; simpl in *; tas;
           now apply ConstraintSet.empty_spec in Hc.
      -- apply ConstraintSet.union_spec; now right.
  - specialize (IHwfΣ HH). revert IHwfΣ o; clear.
    generalize (universes_decl_of_decl decl); intros d' HH Hd.
    unfold on_udecl_prop in *.
    destruct HH as [H1 H2]. split.
    + clear -H1. intros [[? ?] ?] Hc. specialize (H1 _ Hc).
      destruct H1 as [H H']. simpl. split.
      * apply LevelSet.union_spec in H. apply LevelSet.union_spec.
        destruct H; [now left|right]. apply LevelSet.union_spec; now right.
      * apply LevelSet.union_spec in H'. apply LevelSet.union_spec.
        destruct H'; [now left|right]. apply LevelSet.union_spec; now right.
    + destruct d'; trivial. repeat split.
      * destruct H2; auto.
      * intros l Hl. apply H2 in Hl.
        apply LevelSet.union_spec; now right.
      * intros c Hc. apply H2 in Hc.
        apply ConstraintSet.union_spec; now right.
      * destruct Hd as [_ [_ [_ Hd]]]; cbn in Hd.
        destruct Hd as [v Hv]. exists v. intros c Hc; apply Hv; clear v Hv.
          apply ConstraintSet.union_spec in Hc; destruct Hc as [Hc|Hc]; simpl in *.
          2: apply ConstraintSet.union_spec in Hc; destruct Hc as [Hc|Hc];
            simpl in *.
          -- apply H2 in Hc. apply ConstraintSet.union_spec; now right.
          -- clear -Hc. destruct d as [[? ? []]|[? ? ? ? []]]; cbn in *.
             all: try (apply ConstraintSet.empty_spec in Hc; contradiction).
             all: apply ConstraintSet.union_spec; now left.
          -- apply ConstraintSet.union_spec; now right.
Qed.

Lemma on_udecl_on_udecl_prop {cf:checker_flags} Σ ctx : 
  on_udecl Σ (Polymorphic_ctx ctx) -> on_udecl_prop Σ (Polymorphic_ctx ctx).
Proof.
  intros [? [? [_ ?]]]. red. split; auto.
Qed.
