(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
  PCUICEquality PCUICContextSubst PCUICUnivSubst PCUICCases
  PCUICReduction PCUICCumulativity PCUICTyping
  PCUICGuardCondition PCUICGlobalEnv.
From Equations Require Import Equations.

Require Import ssreflect.

Set Default Goal Selector "!".
Implicit Types (cf : checker_flags).

Lemma global_ext_constraints_app Σ Σ' φ
  : ConstraintSet.Subset (universes Σ).2 (universes Σ').2 ->
    ConstraintSet.Subset (global_ext_constraints (Σ, φ))
                         (global_ext_constraints (Σ', φ)).
Proof.
  unfold global_ext_constraints; simpl.
  intros sub ctr Hc. apply ConstraintSet.union_spec in Hc.
  apply ConstraintSet.union_spec.
  destruct Hc as [Hc|Hc]; [now left|right]. clear φ.
  unfold global_constraints in Hc.
  apply (sub _ Hc).
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
  forall (Σ : global_env_ext) (Σ' : global_env), 
    wf Σ -> wf Σ' -> extends Σ.1 Σ' ->
    forall Γ t T, P Σ Γ t T -> P (Σ', Σ.2) Γ t T.

Lemma weakening_env_global_ext_levels Σ Σ' φ (H : extends Σ Σ') l
  : LevelSet.In l (global_ext_levels (Σ, φ))
    -> LevelSet.In l (global_ext_levels (Σ', φ)).
Proof.
  unfold global_ext_levels; simpl.
  intros Hl. apply LevelSet.union_spec in Hl.
  apply LevelSet.union_spec.
  destruct Hl as [Hl|Hl]; [now left|right]. clear φ.
  destruct H as [[lsub csub] [Σ'' eq]]; subst.
  apply LevelSet.union_spec in Hl.
  apply LevelSet.union_spec; intuition auto.
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
  destruct H as [sub [Σ'' eq]]. subst.
  apply global_ext_constraints_app, sub.
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
  destruct le; [apply eq_term_subset|apply leq_term_subset].
Qed.

Lemma compare_decl_subset {cf:checker_flags} le Σ φ φ' d d'
  : ConstraintSet.Subset φ φ'
    -> compare_decl le Σ φ d d' -> compare_decl le Σ φ' d d'.
Proof.
  intros Hφ []; constructor; eauto using compare_term_subset.
Qed.

Lemma compare_context_subset {cf:checker_flags} le Σ φ φ' Γ Γ'
  : ConstraintSet.Subset φ φ'
    -> compare_context le Σ φ Γ Γ' ->  compare_context le Σ φ' Γ Γ'.
Proof.
  intros Hφ. induction 1; constructor; auto; eapply compare_decl_subset; eassumption.
Qed.

Ltac my_rename_hyp h th :=
  match th with
  | (extends ?t _) => fresh "ext" t
  | (extends ?t.1 _) => fresh "ext" t
  | (extends _ _) => fresh "ext"
  | _ => PCUICTyping.my_rename_hyp h th
  end.

Ltac rename_hyp h ht ::= my_rename_hyp h ht.

Lemma lookup_global_Some_fresh `{checker_flags} Σ c decl :
  lookup_global Σ c = Some decl -> ~ (fresh_global c Σ).
Proof.
  induction Σ; cbn. 1: congruence.
  unfold eq_kername; destruct kername_eq_dec; subst.
  - intros [= <-] H2. inv H2.
    contradiction.
  - intros H1 H2. apply IHΣ; tas.
    now inv H2.
Qed.

Lemma lookup_env_Some_fresh `{checker_flags} Σ c decl :
  lookup_env Σ c = Some decl -> ~ (fresh_global c Σ.(declarations)).
Proof.
  apply lookup_global_Some_fresh.
Qed.

Lemma extends_lookup `{checker_flags} Σ Σ' c decl :
  wf Σ' ->
  extends Σ Σ' ->
  lookup_env Σ c = Some decl ->
  lookup_env Σ' c = Some decl.
Proof.
  destruct Σ as [univs Σ], Σ' as [univs' Σ']; cbn.
  intros [hu hΣ].
  rewrite /lookup_env; intros [sub [Σ'' eq]]; cbn in *. subst Σ'.
  induction Σ'' in hΣ, c, decl |- *.
  - simpl. auto.
  - intros hl. depelim hΣ. specialize (IHΣ'' c decl hΣ hl).
    simpl in *.
    unfold eq_kername; destruct kername_eq_dec; subst; auto.
    apply lookup_global_Some_fresh in IHΣ''; contradiction.
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

Existing Class extends.

#[global] Instance subrel_extends_eq {cf} (Σ Σ' : global_env) (ϕ : universes_decl) : 
  extends Σ Σ' ->
  RelationClasses.subrelation (eq_universe (global_ext_constraints (Σ, ϕ))) 
    (eq_universe (global_ext_constraints (Σ', ϕ))).
Proof.
  intros ext u u'.
  apply eq_universe_subset.
  apply global_ext_constraints_app, ext.
Qed.

#[global] Instance subrel_extends_le {cf} (Σ Σ' : global_env) (ϕ : universes_decl) : 
  extends Σ Σ' ->
  RelationClasses.subrelation (leq_universe (global_ext_constraints (Σ, ϕ))) 
    (leq_universe (global_ext_constraints (Σ', ϕ))).
Proof.
  intros ext u u'.
  apply leq_universe_subset.
  apply global_ext_constraints_app, ext.
Qed.

#[global] Instance subrel_extends_eq_le {cf} (Σ Σ' : global_env) (ϕ : universes_decl) : 
  extends Σ Σ' ->
  RelationClasses.subrelation (eq_universe (global_ext_constraints (Σ, ϕ))) 
    (leq_universe (global_ext_constraints (Σ', ϕ))).
Proof.
  intros ext u u'. intros eq.
  eapply eq_universe_leq_universe.
  eapply eq_universe_subset; tea.
  apply global_ext_constraints_app, ext.
Qed.

Lemma weakening_env_conv `{CF:checker_flags} Σ Σ' φ Γ M N :
  wf Σ' ->
  extends Σ Σ' ->
  convAlgo (Σ, φ) Γ M N ->
  convAlgo (Σ', φ) Γ M N.
Proof.
  intros wfΣ ext.
  induction 1; simpl.
  - econstructor. eapply eq_term_subset.
    + now eapply global_ext_constraints_app.
    + simpl in *. eapply eq_term_upto_univ_weaken_env in c; simpl; eauto.
      all:typeclasses eauto.
  - econstructor 2; eauto. eapply weakening_env_red1; eauto.
  - econstructor 3; eauto. eapply weakening_env_red1; eauto.
Qed.

Lemma weakening_env_cumul `{CF:checker_flags} Σ Σ' φ Γ M N :
  wf Σ' ->
  extends Σ Σ' ->
  cumulAlgo (Σ, φ) Γ M N ->
  cumulAlgo (Σ', φ) Γ M N.
Proof.
  intros wfΣ ext.
  induction 1; simpl.
  - econstructor. eapply leq_term_subset.
    + now eapply global_ext_constraints_app.
    + simpl in *. eapply eq_term_upto_univ_weaken_env in c; simpl; eauto.
      all:typeclasses eauto.
  - econstructor 2; eauto. eapply weakening_env_red1; eauto.
  - econstructor 3; eauto. eapply weakening_env_red1; eauto.
Qed.

Lemma weakening_env_is_allowed_elimination `{CF:checker_flags} Σ Σ' φ u allowed :
  wf Σ' -> extends Σ Σ' ->
  is_allowed_elimination (global_ext_constraints (Σ, φ)) u allowed ->
  is_allowed_elimination (global_ext_constraints (Σ', φ)) u allowed.
Proof.
  intros wfΣ ext al.
  unfold is_allowed_elimination in *.
  destruct check_univs; auto.
  intros val sat.
  unshelve epose proof (al val _) as al.
  { eapply satisfies_subset; eauto.
    apply global_ext_constraints_app, ext. }
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
  check_recursivity_kind (lookup_env Σ) ind k -> check_recursivity_kind (lookup_env Σ') ind k.
Proof.
  intros ext wfΣ'.
  rewrite /check_recursivity_kind.
  destruct lookup_env eqn:Heq => //.
  eapply extends_lookup in Heq; eauto.
  now rewrite Heq.
Qed.

Lemma extends_wf_fixpoint {cf:checker_flags} (Σ Σ' : global_env_ext) mfix : extends Σ Σ' -> wf Σ' ->
  wf_fixpoint Σ mfix -> wf_fixpoint Σ' mfix.
Proof.
  intros ext wfΣ'.
  unfold wf_fixpoint, wf_fixpoint_gen.
  destruct map_option_out as [[|ind inds]|]; auto.
  move/andb_and => [->] /=.
  now apply extends_check_recursivity_kind.
Qed.

Lemma extends_wf_cofixpoint {cf:checker_flags} (Σ Σ' : global_env_ext) mfix : extends Σ Σ' -> wf Σ' ->
  wf_cofixpoint Σ mfix -> wf_cofixpoint Σ' mfix.
Proof.
  intros ext wfΣ'.
  unfold wf_cofixpoint, wf_cofixpoint_gen.
  destruct map_option_out as [[|ind inds]|]; auto.
  move/andb_and => [->] /=.
  now apply extends_check_recursivity_kind.
Qed.

Lemma global_levels_Set Σ :
  LevelSet.In Level.lzero (global_levels Σ).
Proof.
  unfold global_levels. lsets.
Qed.

Lemma global_levels_set Σ :
  LevelSet.Equal (LevelSet.union (LevelSet.singleton Level.lzero) (global_levels Σ))
  (global_levels Σ).
Proof.
  apply LevelSetProp.union_subset_equal.
  intros x hin. eapply LevelSet.singleton_spec in hin; subst x.
  apply global_levels_Set.
Qed.

Lemma global_levels_sub {univs univs'} : univs ⊂_cs univs' ->
  LevelSet.Subset (global_levels univs) (global_levels univs').
Proof.
  unfold global_levels => sub.
  intros x hin % LevelSet.union_spec. 
  apply LevelSet.union_spec. 
  intuition auto. left. now apply sub.
Qed.

Lemma extends_wf_universe {cf:checker_flags} {Σ : global_env_ext} Σ' u : extends Σ Σ' -> wf Σ' ->
  wf_universe Σ u -> wf_universe (Σ', Σ.2) u.
Proof.
  destruct Σ as [Σ univ]; cbn.
  intros [sub [Σ'' eq]] wf.
  destruct u; simpl; auto.
  intros Hl.
  intros l inl; specialize (Hl l inl).
  cbn.
  unfold global_ext_levels.
  eapply LevelSet.union_spec; simpl.
  apply LevelSet.union_spec in Hl as [Hl|Hl]; cbn in Hl.
  - simpl. simpl in Hl. now left.
  - right. eapply global_levels_sub; tea.
Qed.

#[global]
Hint Resolve extends_wf_fixpoint extends_wf_cofixpoint : extends.

(* Lemma wf_extends `{checker_flags} {Σ Σ'} : wf Σ' -> extends Σ Σ' -> wf Σ.
Proof.
  intros HΣ' [univs [Σ'' eq]]. simpl in *.
  split => //.
  - red.
  induction Σ''; auto.
  inv HΣ'. auto.
Qed. *)

Definition on_udecl_prop `{checker_flags} (Σ : global_env) (udecl : universes_decl)
  := let levels := levels_of_udecl udecl in
     let global_levels := global_levels Σ.(universes) in
     let all_levels := LevelSet.union levels global_levels in
     ConstraintSet.For_all (declared_cstr_levels all_levels) (constraints_of_udecl udecl).
     (* /\ match udecl with
       | Monomorphic_ctx ctx => LevelSet.for_all (negb ∘ Level.is_var) ctx.1
                               /\ LevelSet.Subset ctx.1 global_levels
                               /\ ConstraintSet.Subset ctx.2 (global_constraints Σ)
                               /\ satisfiable_udecl Σ.(universes) udecl
       | _ => True
       end. *)

Lemma in_global_levels l u : 
  LevelSet.In l (ContextSet.levels u) ->
  LevelSet.In l (global_levels u).
Proof.
  intros hin; now apply LevelSet.union_spec.
Qed.

Lemma weaken_lookup_on_global_env' `{checker_flags} Σ c decl :
  wf Σ ->
  lookup_env Σ c = Some decl ->
  on_udecl_prop Σ (universes_decl_of_decl decl).
Proof.
  intros [onu wfΣ] HH.
  destruct Σ as [univs Σ]; cbn in *.
  induction wfΣ; simpl. 1: discriminate.
  cbn in HH. subst udecl.
  unfold eq_kername in HH; destruct kername_eq_dec; subst.
  - apply some_inj in HH; destruct HH. subst.
    clear -o. unfold on_udecl, on_udecl_prop in *.
    destruct o as [H1 [H2 [H3 H4]]]. repeat split.
    clear -H2. intros [[? ?] ?] Hc. specialize (H2 _ Hc).
    destruct H2 as [H H']. simpl. split.
    * apply LevelSet.union_spec in H. apply LevelSet.union_spec.
      destruct H; [now left|right]; auto.
    * apply LevelSet.union_spec in H'. apply LevelSet.union_spec.
      destruct H'; [now left|right]; auto.
    (*+ revert H3. case_eq (universes_decl_of_decl d); trivial.
      intros ctx eq Hctx. repeat split.
      * auto.
      * intros l Hl. simpl. replace (monomorphic_levels_decl d) with ctx.1.
        -- apply in_global_levels. apply LevelSet.union_spec; now left.
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
      -- apply ConstraintSet.union_spec; now right.*)
  - specialize (IHwfΣ HH). revert IHwfΣ o; clear.
    generalize (universes_decl_of_decl decl); intros d' HH Hd.
    unfold on_udecl_prop in *.
    intros [[? ?] ?] Hc. specialize (HH _ Hc).
    destruct HH as [H' H'']. simpl. split.
    * apply LevelSet.union_spec in H'. apply LevelSet.union_spec.
      destruct H'; [now left|right]; auto.
    * apply LevelSet.union_spec in H''. apply LevelSet.union_spec.
      destruct H''; [now left|right]; auto.
      
    (*+ destruct d'; trivial. repeat split.
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
          -- apply ConstraintSet.union_spec; now right.*)
Qed.

Lemma declared_cstr_levels_sub l l' c : 
  LevelSet.Subset l l' ->
  declared_cstr_levels l c -> declared_cstr_levels l' c.
Proof.
  intros sub; unfold declared_cstr_levels.
  destruct c as [[l1 eq] l2]. intuition auto.
Qed.

Lemma on_udecl_on_udecl_prop {cf:checker_flags} (Σ : global_env) ctx :
  on_udecl Σ.(universes) (Polymorphic_ctx ctx) -> on_udecl_prop Σ (Polymorphic_ctx ctx).
Proof.
  intros [? [? ?]]. red.
  intros x hin. specialize (H0 x hin).
  eapply declared_cstr_levels_sub; tea.
  intros x' hin'.
  eapply LevelSet.union_spec. apply LevelSet.union_spec in hin'.
  intuition auto.
Qed.

Definition extends_decls (Σ Σ' : global_env) := 
  Σ.(universes) = Σ'.(universes) ×
  ∑ Σ'', declarations Σ' = Σ'' ++ Σ.(declarations).

Existing Class extends_decls.

#[global] Instance extends_decls_extends Σ Σ' : extends_decls Σ Σ' -> extends Σ Σ'.
Proof.
  intros []. split => //.
  rewrite e. split; [lsets|csets].
Qed.

Definition weaken_env_prop `{checker_flags}
           (P : global_env_ext -> context -> term -> option term -> Type) :=
  forall Σ Σ' φ, wf Σ -> wf Σ' -> extends Σ Σ' -> forall Γ t T, P (Σ, φ) Γ t T -> P (Σ', φ) Γ t T.

Definition weaken_env_decls_prop `{checker_flags}
  (P : global_env_ext -> context -> term -> option term -> Type) :=
  forall Σ Σ' φ, wf Σ' -> extends_decls Σ Σ' -> forall Γ t T, P (Σ, φ) Γ t T -> P (Σ', φ) Γ t T.

Lemma extends_decls_wf {cf} Σ Σ' : 
  wf Σ' -> extends_decls Σ Σ' -> wf Σ.
Proof.
  intros [onu ond] [eq [Σ'' eq']].
  split => //. 
  - red. rewrite eq. apply onu.
  - rewrite eq. rewrite eq' in ond.
    revert ond; clear.
    induction Σ''; cbn; auto.
    intros H; depelim H.
    apply IHΣ''. apply H.
Qed. 