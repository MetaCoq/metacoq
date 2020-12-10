(* Distributed under the terms of the MIT license. *)
From Coq Require Import RelationClasses.
From MetaCoq.Template Require Import config utils Ast AstUtils
     LibHypsNaming TermEquality Typing.
Require Import ssreflect.

(** * Weakening lemmas w.r.t. the global environment *)

Generalizable Variables Σ Γ t T.

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
Hint Resolve weakening_env_global_ext_levels : extends.

Lemma weakening_env_global_ext_levels' Σ Σ' φ (H : extends Σ Σ') l
  : LevelSet.mem l (global_ext_levels (Σ, φ))
    -> LevelSet.mem l (global_ext_levels (Σ', φ)).
Proof.
  intro HH. apply LevelSet.mem_spec in HH.
  now eapply LevelSet.mem_spec, weakening_env_global_ext_levels.
Qed.

Lemma lookup_env_Some_fresh Σ c decl :
  lookup_env Σ c = Some decl -> ~ (fresh_global c Σ).
Proof.
  induction Σ; cbn. congruence.
  unfold eq_kername. destruct (kername_eq_dec c a.1).
  - subst c. intros [= <-]. intros H2. inv H2. contradiction.
  - intros H1 H2. apply IHΣ; tas.
    now inv H2.
Qed.

Lemma extends_lookup `{checker_flags} Σ Σ' c decl :
  wf Σ' -> extends Σ Σ' -> lookup_env Σ c = Some decl -> lookup_env Σ' c = Some decl.
Proof.
  intros wfΣ' [Σ'' ->]. simpl.
  induction Σ'' in wfΣ', c, decl |- *. simpl. auto.
  specialize (IHΣ'' c decl). forward IHΣ''.
  inv wfΣ'. simpl in X0. apply X.
  intros HΣ. specialize (IHΣ'' HΣ).
  inv wfΣ'. simpl in *.
  unfold eq_kername; destruct kername_eq_dec; subst.
  eapply lookup_env_Some_fresh in IHΣ''; eauto. contradiction.
  assumption.
Qed.
Hint Resolve extends_lookup : extends.

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
Hint Resolve extends_wf_local : extends.

Lemma weakening_env_red1 `{CF:checker_flags} Σ Σ' Γ M N :
  wf Σ' ->
  extends Σ Σ' ->
  red1 Σ Γ M N ->
  red1 Σ' Γ M N.
Proof.
  induction 3 using red1_ind_all;
    try solve [econstructor; eauto;
               eapply (OnOne2_impl X1); simpl; intuition eauto].

  eapply extends_lookup in X0; eauto.
  econstructor; eauto.
Qed.

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

Lemma eq_term_subset {cf:checker_flags} Σ φ φ' t t'
  : ConstraintSet.Subset φ φ'
    -> eq_term Σ φ t t' ->  eq_term Σ φ' t t'.
Proof.
  intro H. apply eq_term_upto_univ_morphism.
  all: intros u u'; eapply eq_universe_subset; assumption.
Qed.

Lemma leq_term_subset {cf:checker_flags} Σ ctrs ctrs' t u
  : ConstraintSet.Subset ctrs ctrs' -> leq_term Σ ctrs t u -> leq_term Σ ctrs' t u.
Proof.
  intro H. apply eq_term_upto_univ_morphism.
  intros t' u'; eapply eq_universe_subset; assumption.
  intros t' u'; eapply leq_universe_subset; assumption.
Qed.

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

Instance eq_term_upto_univ_weaken_env {cf:checker_flags} Σ Σ' Re Re' Rle Rle' napp :
  wf Σ' -> extends Σ Σ' ->
  RelationClasses.subrelation Re Re' ->
  RelationClasses.subrelation Rle Rle' ->
  RelationClasses.subrelation Re Rle' ->
  CRelationClasses.subrelation (eq_term_upto_univ_napp Σ Re Rle napp) 
    (eq_term_upto_univ_napp Σ' Re' Rle' napp).
Proof.
  intros wfΣ ext he hele hle t t'.
  induction t in napp, t', Rle, Rle', hle, hele |- * using Induction.term_forall_list_rect;
    try (inversion 1; subst; constructor;
         eauto using R_universe_instance_impl'; fail).
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
  - inversion 1; subst; constructor.
    eapply IHt. 3:eauto. all:auto.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
  - inversion 1; subst; constructor.
    eapply R_global_instance_weaken_env. 6:eauto. all:eauto.
  - inversion 1; subst; constructor.
    eapply R_global_instance_weaken_env. 6:eauto. all:eauto.
  - inversion 1; subst; constructor; eauto.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x ? y [? ?]. split; eauto.
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x [? ?] y [[[? ?] ?] ?]. repeat split; eauto.
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x [? ?] y [[[? ?] ?] ?]. repeat split; eauto.
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
    + eapply eq_term_upto_univ_weaken_env; eauto. exists Σ''; eauto.
      all:typeclasses eauto.
  - econstructor 2; eauto. eapply weakening_env_red1; eauto. exists Σ''; eauto.
  - econstructor 3; eauto. eapply weakening_env_red1; eauto. exists Σ''; eauto.
Qed.

Lemma weakening_env_cumul `{CF:checker_flags} Σ Σ' φ Γ M N :
  wf Σ' -> extends Σ Σ' ->
  cumul (Σ, φ) Γ M N -> cumul (Σ', φ) Γ M N.
Proof.
  intros wfΣ [Σ'' ->].
  induction 1; simpl.
  - econstructor. eapply leq_term_subset.
    + eapply global_ext_constraints_app.
    + eapply eq_term_upto_univ_weaken_env; eauto. exists Σ''; eauto.
      all:typeclasses eauto.
  - econstructor 2; eauto. eapply weakening_env_red1; eauto. exists Σ''; eauto.
  - econstructor 3; eauto. eapply weakening_env_red1; eauto. exists Σ''; eauto.
Qed.

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
Hint Resolve weakening_env_is_allowed_elimination : extends.

Lemma weakening_env_declared_constant `{CF:checker_flags}:
  forall (Σ : global_env) cst (decl : constant_body),
    declared_constant Σ cst decl ->
    forall Σ' : global_env, wf Σ' -> extends Σ Σ' -> declared_constant Σ' cst decl.
Proof.
  intros Σ cst decl H0 Σ' X2 H2.
  eapply extends_lookup; eauto.
Qed.
Hint Resolve weakening_env_declared_constant : extends.

Lemma weakening_env_declared_minductive `{CF:checker_flags}:
  forall (Σ : global_env) ind decl,
    declared_minductive Σ ind decl ->
    forall Σ' : global_env, wf Σ' -> extends Σ Σ' -> declared_minductive Σ' ind decl.
Proof.
  intros Σ cst decl H0 Σ' X2 H2.
  eapply extends_lookup; eauto.
Qed.
Hint Resolve weakening_env_declared_minductive : extends.

Lemma weakening_env_declared_inductive:
  forall (H : checker_flags) (Σ : global_env) ind mdecl decl,
    declared_inductive Σ ind mdecl decl ->
    forall Σ' : global_env, wf Σ' -> extends Σ Σ' -> declared_inductive Σ' ind mdecl decl.
Proof.
  intros H Σ cst decl H0 [Hmdecl Hidecl] Σ' X2 H2. split; eauto with extends.
Qed.
Hint Resolve weakening_env_declared_inductive : extends.

Lemma weakening_env_declared_constructor :
  forall (H : checker_flags) (Σ : global_env) ind mdecl idecl decl,
    declared_constructor Σ ind mdecl idecl decl ->
    forall Σ' : global_env, wf Σ' -> extends Σ Σ' ->
    declared_constructor Σ' ind mdecl idecl decl.
Proof.
  intros H Σ cst mdecl idecl cdecl [Hidecl Hcdecl] Σ' X2 H2.
  split; eauto with extends.
Qed.
Hint Resolve weakening_env_declared_constructor : extends.

Lemma weakening_env_declared_projection :
  forall (H : checker_flags) (Σ : global_env) ind mdecl idecl decl,
    declared_projection Σ ind mdecl idecl decl ->
    forall Σ' : global_env, wf Σ' -> extends Σ Σ' ->
    declared_projection Σ' ind mdecl idecl decl.
Proof.
  intros H Σ cst mdecl idecl cdecl [Hidecl Hcdecl] Σ' X2 H2.
  split; eauto with extends.
Qed.
Hint Resolve weakening_env_declared_projection : extends.

Lemma weakening_All_local_env_impl `{checker_flags}
      (P Q : context -> term -> option term -> Type) l :
  All_local_env P l ->
  (forall Γ t T, P Γ t T -> Q Γ t T) ->
  All_local_env Q l.
Proof.
  induction 1; intros; simpl; econstructor; eauto.
Qed.

Lemma weakening_env_global_ext_constraints Σ Σ' φ (H : extends Σ Σ')
  : ConstraintSet.Subset (global_ext_constraints (Σ, φ))
                         (global_ext_constraints (Σ', φ)).
Proof.
  destruct H as [Σ'' eq]. subst.
  apply global_ext_constraints_app.
Qed.

Lemma eq_decl_subset {cf:checker_flags} Σ φ φ' d d'
  : ConstraintSet.Subset φ φ'
    -> eq_decl Σ φ d d' -> eq_decl Σ φ' d d'.
Proof.
  intros Hφ [H1 H2]. split; [|eapply eq_term_subset; eauto].
  destruct d as [na [bd|] ty], d' as [na' [bd'|] ty']; cbn in *; trivial.
  eapply eq_term_subset; eauto.
Qed.

Lemma eq_context_subset {cf:checker_flags} Σ φ φ' Γ Γ'
  : ConstraintSet.Subset φ φ'
    -> eq_context Σ φ Γ Γ' -> eq_context Σ φ' Γ Γ'.
Proof.
  intros Hφ. induction 1; constructor.
  eapply eq_decl_subset; eassumption. assumption.
Qed.

Lemma weakening_env_consistent_instance {cf:checker_flags} :
  forall Σ Σ' φ ctrs u,
    extends Σ Σ' ->
    consistent_instance_ext (Σ, φ) ctrs u ->
    consistent_instance_ext (Σ', φ) ctrs u.
Proof.
  intros Σ Σ' φ ctrs u he.
  unfold consistent_instance_ext, consistent_instance.
  intros hc.
  destruct ctrs=> //.
  destruct cst as [nas cst]; simpl in *.
  intuition auto.
  eapply forallb_Forall in H. eapply forallb_Forall, Forall_impl; tea.
  intros ? ? ; now eapply weakening_env_global_ext_levels'.
  eapply valid_subset; tea;
    now eapply weakening_env_global_ext_constraints.
Qed.
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

Hint Resolve extends_wf_fixpoint extends_wf_cofixpoint : extends.

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


Ltac typing_my_rename_hyp h th :=
  match th with
  | (wf ?E) => fresh "wf" E
  | (typing _ _ ?t _) => fresh "type" t
  | (@cumul _ _ _ ?t _) => fresh "cumul" t
  | (conv _ _ ?t _) => fresh "conv" t
  | (All_local_env (lift_typing (@typing _) _) ?G) => fresh "wf" G
  | (All_local_env (lift_typing (@typing _) _) _) => fresh "wf"
  | (All_local_env _ _ ?G) => fresh "H" G
  | context [typing _ _ (_ ?t) _] => fresh "IH" t
  end.

Ltac my_rename_hyp h th :=
  match th with
  | (extends ?t _) => fresh "ext" t
  | (extends ?t.1 _) => fresh "ext" t
  | (extends _ _) => fresh "ext"
  | _ => typing_my_rename_hyp h th
  end.

Ltac rename_hyp h ht ::= my_rename_hyp h ht.

Lemma weakening_env `{checker_flags} :
  env_prop (fun Σ Γ t T =>
              forall Σ', wf Σ' -> extends Σ.1 Σ' -> (Σ', Σ.2) ;;; Γ |- t : T).
Proof.
  apply typing_ind_env; intros;
    rename_all_hyps; try solve [econstructor; eauto 2 with extends].

  - econstructor; eauto 2 with extends.
    intuition auto. eapply extends_wf_universe; eauto.
  - econstructor; eauto 2 with extends.
    destruct Σ as [Σ φ].
    clear typet heq_isApp forall_Σ' hneq_l.
    induction X1. constructor. econstructor; eauto with extends.
    eapply weakening_env_cumul in cumul; eauto.
  - econstructor; eauto 2 with extends.
    close_Forall. intros; intuition eauto with extends.
    destruct b as [s [Hs IHs]]. exists s. eauto.
  - econstructor; eauto with extends.
    eapply fix_guard_extends; eauto.
    eapply (All_impl X0); intuition eauto.
    destruct X2 as [s Hs]; exists s; intuition eauto.
    eapply All_impl; eauto; simpl; intuition eauto with extends.

  - econstructor; eauto with extends. auto.
    eapply cofix_guard_extends; eauto.
    eapply (All_impl X0); intuition eauto.
    destruct X2 as [s Hs]; exists s; intuition eauto.
    eapply All_impl; eauto; simpl; intuition eauto with extends.
  - econstructor; eauto with extends.
    destruct Σ as [Σ φ]. eapply weakening_env_cumul in cumulA; eauto.
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
  destruct decl. destruct c. destruct cst_body. simpl in *.
  red in Hdecl |- *. simpl in *.
  eapply HPΣ; eauto.
  eapply HPΣ; eauto.
  simpl in *.
  destruct Hdecl as [onI onP onnP]; constructor; eauto.
  - eapply Alli_impl; eauto. intros.
    destruct X. unshelve econstructor; eauto.
    -- unfold on_type in *; intuition eauto.
    -- unfold on_constructors in *. eapply All2_impl; eauto.
      intros decl cs []. unshelve econstructor; eauto.
      red in on_ctype |- *. eauto.
      clear on_cindices cstr_eq cstr_args_length cstr_concl_head.
      revert on_cargs.
      generalize (cshape_sorts cs).
      induction (cshape_args cs); destruct l; simpl in *; auto.
      ** destruct a as [na [b|] ty]; simpl in *; intuition eauto.
      ** destruct a as [na [b|] ty]; simpl in *; intuition eauto.
      ** clear on_ctype on_cargs.
        revert on_cindices.
        generalize (List.rev (LiftSubst.lift_context #|cshape_args cs| 0 ind_indices)).
        generalize (cshape_indices cs). induction 1; constructor; eauto.
      ** simpl.
        intros v indv. specialize (on_ctype_variance v indv).
        simpl in *. move: on_ctype_variance.
        unfold cstr_respects_variance. destruct variance_universes as [[[univs u] u']|]; auto.
        intros [args idxs]. split.
        eapply (context_relation_impl args); intros.
        inversion X; constructor; auto.
        eapply weakening_env_cumul; eauto.
        eapply weakening_env_conv; eauto.
        eapply weakening_env_cumul; eauto.
        eapply (All2_impl idxs); intros.
        eapply weakening_env_conv; eauto.
    -- unfold check_ind_sorts in *.
       destruct Universe.is_prop; auto.
       destruct Universe.is_sprop; auto.
       split; [apply fst in ind_sorts|apply snd in ind_sorts].
       eapply Forall_impl; tea; cbn.
       intros. eapply Forall_impl; eauto; simpl.
       intros; eapply leq_universe_subset; tea.
       apply weakening_env_global_ext_constraints; tea.
       destruct indices_matter; [|trivial]. clear -ind_sorts HPΣ wfΣ' Hext.
       induction ind_indices; simpl in *; auto.
       ** eapply (extends_wf_universe (Σ:=(Σ,φ)) Σ'); auto.
       ** destruct a as [na [b|] ty]; simpl in *; intuition eauto.
      -- intros v onv.
          move: (onIndices v onv). unfold ind_respects_variance.
         destruct variance_universes as [[[univs u] u']|] => //.
         intros idx; eapply (context_relation_impl idx); simpl.
         intros par par' t t'.
         intros d. inv d; constructor; auto.
         eapply weakening_env_cumul; eauto.
         eapply weakening_env_conv; eauto.
         eapply weakening_env_cumul; eauto.
  - red in onP |- *. eapply All_local_env_impl; eauto.
Qed.

Lemma weakening_env_lookup_on_global_env `{checker_flags} P Σ Σ' c decl :
  weaken_env_prop P ->
  wf Σ' -> extends Σ Σ' -> on_global_env P Σ ->
  lookup_env Σ c = Some decl ->
  on_global_decl P (Σ', universes_decl_of_decl decl) c decl.
Proof.
  intros HP wfΣ Hext HΣ.
  induction HΣ; simpl. congruence.
  assert (HH: extends Σ Σ'). {
    destruct Hext as [Σ'' HΣ''].
    exists (Σ'' ++ [(kn, d)]). now rewrite <- app_assoc. }
  unfold eq_kername; destruct kername_eq_dec; subst.
  - intros [= ->].
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
  declared_inductive Σ mdecl ind idecl ->
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
  (Hdecl : declared_constructor Σ mdecl idecl ref cdecl) :
  ∑ cs,
  let onib := declared_inductive_inv HP wfΣ HΣ (proj1 Hdecl) in
  nth_error onib.(ind_cshapes) ref.2 = Some cs
  × on_constructor (lift_typing P) (Σ, ind_universes mdecl) mdecl
                   (inductive_ind ref.1) idecl onib.(ind_indices) cdecl cs.
Proof.
  intros.
  destruct Hdecl as [Hidecl Hcdecl].
  set (declared_inductive_inv HP wfΣ HΣ (proj1 (conj Hidecl Hcdecl))) as HH.
  clearbody HH. pose proof HH.(onConstructors) as HH'.
  eapply All2_nth_error_Some in Hcdecl; tea.
Qed.

Lemma declared_projection_inv `{checker_flags} {Σ P mdecl idecl ref pdecl} :
  forall (HP : weaken_env_prop (lift_typing P))
  (wfΣ : wf Σ)
  (HΣ : Forall_decls_typing P Σ)
  (Hdecl : declared_projection Σ mdecl idecl ref pdecl),
  let oib := declared_inductive_inv HP wfΣ HΣ (proj1 Hdecl) in
  match oib.(ind_cshapes) return Type with
  | [cs] => on_projection mdecl (inductive_mind ref.1.1) (inductive_ind ref.1.1) cs (snd ref) pdecl
  | _ => False
  end.
Proof.
  intros.
  destruct (declared_inductive_inv HP wfΣ HΣ (proj1 Hdecl)) in *.
  destruct Hdecl as [Hidecl [Hcdecl Hnpar]]. simpl. clearbody oib.
  forward onProjections.    
  { eapply nth_error_Some_length in Hcdecl.
    destruct (ind_projs idecl); simpl in *. lia. congruence. }
  destruct ind_cshapes as [|? []]; try contradiction.
  destruct onProjections.
  eapply nth_error_alli in Hcdecl; eauto. eapply Hcdecl.
Qed.

Lemma wf_extends `{checker_flags} {Σ Σ'} : wf Σ' -> extends Σ Σ' -> wf Σ.
Proof.
  intros HΣ' [Σ'' ->]. simpl in *.
  induction Σ''. auto.
  inv HΣ'. auto.
Qed.

Lemma weaken_env_prop_typing `{checker_flags} : weaken_env_prop (lift_typing typing).
Proof.
  red. intros * wfΣ' Hext *.
  destruct T; simpl.
  intros Ht. pose proof (wf_extends wfΣ' Hext).
  eapply (weakening_env (_, _)); eauto. eapply typing_wf_local in Ht; eauto.
  intros [s Ht]. pose proof (wf_extends wfΣ' Hext). exists s.
  eapply (weakening_env (_, _)); eauto. eapply typing_wf_local in Ht; eauto.
Qed.

Hint Unfold weaken_env_prop : pcuic.

Lemma on_declared_minductive `{checker_flags} {Σ ref decl} :
  wf Σ ->
  declared_minductive Σ ref decl ->
  on_inductive (lift_typing typing) (Σ, ind_universes decl) ref decl.
Proof.
  intros wfΣ Hdecl.
  apply (declared_minductive_inv weaken_env_prop_typing wfΣ wfΣ Hdecl).
Qed.

Lemma on_declared_inductive `{checker_flags} {Σ ref mdecl idecl} :
  wf Σ ->
  declared_inductive Σ mdecl ref idecl ->
  on_inductive (lift_typing typing) (Σ, ind_universes mdecl) (inductive_mind ref) mdecl *
  on_ind_body (lift_typing typing) (Σ, ind_universes mdecl) (inductive_mind ref) mdecl (inductive_ind ref) idecl.
Proof.
  intros wfΣ Hdecl.
  split. destruct Hdecl as [Hmdecl _]. now apply on_declared_minductive in Hmdecl.
  apply (declared_inductive_inv weaken_env_prop_typing wfΣ wfΣ Hdecl).
Qed.

Lemma on_declared_constructor `{checker_flags} {Σ ref mdecl idecl cdecl}
  (wfΣ : wf Σ)
  (Hdecl : declared_constructor Σ mdecl idecl ref cdecl) :
  on_inductive (lift_typing typing) (Σ, ind_universes mdecl)
               (inductive_mind (fst ref)) mdecl *
  on_ind_body (lift_typing typing) (Σ, ind_universes mdecl)
              (inductive_mind (fst ref)) mdecl (inductive_ind (fst ref)) idecl *
  ∑ ind_ctor_sort,
    let onib := declared_inductive_inv weaken_env_prop_typing wfΣ wfΣ (proj1 Hdecl) in
     nth_error (ind_cshapes onib) ref.2 = Some ind_ctor_sort
    ×  on_constructor (lift_typing typing) (Σ, ind_universes mdecl)
                 mdecl (inductive_ind (fst ref))
                 idecl onib.(ind_indices) cdecl ind_ctor_sort.
Proof.
  split. destruct Hdecl as [Hidecl Hcdecl].
  now apply on_declared_inductive in Hidecl.
  apply (declared_constructor_inv weaken_env_prop_typing wfΣ wfΣ Hdecl).
Qed.

Lemma on_declared_projection `{checker_flags} {Σ ref mdecl idecl pdecl} :
  forall (wfΣ : wf Σ) (Hdecl : declared_projection Σ mdecl idecl ref pdecl),
  on_inductive (lift_typing typing) (Σ, ind_universes mdecl) (inductive_mind (fst (fst ref))) mdecl *
  let oib := declared_inductive_inv weaken_env_prop_typing wfΣ wfΣ (proj1 Hdecl) in
  match oib.(ind_cshapes) return Type with
  | [cs] => on_projection mdecl (inductive_mind ref.1.1) (inductive_ind ref.1.1) cs (snd ref) pdecl
  | _ => False
  end.
Proof.
  intros wfΣ Hdecl.
  split. destruct Hdecl as [Hidecl Hcdecl]. now apply on_declared_inductive in Hidecl.
  apply (declared_projection_inv weaken_env_prop_typing wfΣ wfΣ Hdecl).
Qed.
