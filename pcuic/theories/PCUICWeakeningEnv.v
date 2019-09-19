(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia.
From MetaCoq.Template Require Import config utils AstUtils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICLiftSubst PCUICUnivSubst PCUICEquality PCUICTyping.
Require Import ssreflect ssrbool.
From Equations Require Import Equations.

Derive Signature for Alli.

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

Lemma leq_universe_subset {cf:checker_flags} ctrs ctrs' t u
  : ConstraintSet.Subset ctrs ctrs' -> leq_universe ctrs t u -> leq_universe ctrs' t u.
Proof.
  intros Hctrs H. unfold leq_universe in *.
  destruct check_univs; [|trivial].
  intros v Hv. apply H.
  intros ctr Hc. apply Hv.
  apply Hctrs; eauto.
Qed.

Lemma eq_universe_subset {cf:checker_flags} ctrs ctrs' t u
  : ConstraintSet.Subset ctrs ctrs'
    -> eq_universe ctrs t u -> eq_universe ctrs' t u.
Proof.
  intros Hctrs H. unfold eq_universe in *.
  destruct check_univs; [|trivial].
  intros v Hv. apply H.
  intros ctr Hc. apply Hv.
  apply Hctrs; eauto.
Qed.



Lemma leq_term_subset {cf:checker_flags} ctrs ctrs' t u
  : ConstraintSet.Subset ctrs ctrs' -> leq_term ctrs t u -> leq_term ctrs' t u.
Proof.
  intro H. apply eq_term_upto_univ_impl.
  intros t' u'; eapply eq_universe_subset; assumption.
  intros t' u'; eapply leq_universe_subset; assumption.
Qed.

(** * Weakening lemmas w.r.t. the global environment *)

Set Asymmetric Patterns.

Generalizable Variables Σ Γ t T.

Definition extends (Σ Σ' : global_env) :=
  { Σ'' & Σ' = (Σ'' ++ Σ)%list }.


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

Lemma eq_term_subset {cf:checker_flags} φ φ' t t'
  : ConstraintSet.Subset φ φ'
    -> eq_term φ t t' ->  eq_term φ' t t'.
Proof.
  intro H. apply eq_term_upto_univ_impl.
  all: intros u u'; eapply eq_universe_subset; assumption.
Qed.

Lemma eq_decl_subset {cf:checker_flags} φ φ' d d'
  : ConstraintSet.Subset φ φ'
    -> eq_decl φ d d' ->  eq_decl φ' d d'.
Proof.
  intros Hφ [H1 H2]. split; [|eapply eq_term_subset; eauto].
  destruct d as [na [bd|] ty], d' as [na' [bd'|] ty']; cbn in *; trivial.
  eapply eq_term_subset; eauto.
Qed.

Lemma eq_context_subset {cf:checker_flags} φ φ' Γ Γ'
  : ConstraintSet.Subset φ φ'
    -> eq_context φ Γ Γ' ->  eq_context φ' Γ Γ'.
Proof.
  intros Hφ. induction 1; constructor.
  eapply eq_decl_subset; eassumption. assumption.
Qed.

Lemma check_correct_arity_subset {cf:checker_flags} φ φ' decl ind u ctx pars pctx
  : ConstraintSet.Subset φ φ' -> check_correct_arity φ decl ind u ctx pars pctx
    -> check_correct_arity φ' decl ind u ctx pars pctx.
Proof.
  apply eq_context_subset.
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
  induction Σ; cbn. congruence.
  case_eq (ident_eq c (global_decl_ident a)).
  - intros H0 H1 H2. inv H2.
    rewrite <- (reflect_iff _ _ (ident_eq_spec _ _)) in H0.
    congruence.
  - intros H0 H1 H2. apply IHΣ; tas.
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
  destruct (ident_eq c (global_decl_ident a)) eqn:Heq'.
  eapply lookup_env_Some_fresh in IHΣ''; eauto.
  rewrite <- (reflect_iff _ _ (ident_eq_spec _ _)) in Heq'.
  rewrite <- Heq' in H0. contradiction.
  auto.
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
  wf Σ' -> extends Σ Σ' ->
  red1 Σ Γ M N ->
  red1 Σ' Γ M N.
Proof.
  induction 3 using red1_ind_all;
    try solve [econstructor; eauto;
               eapply (OnOne2_impl X1); simpl; intuition eauto].

  eapply extends_lookup in X0; eauto.
  econstructor; eauto.
Qed.

Lemma weakening_env_cumul `{CF:checker_flags} Σ Σ' φ Γ M N :
  wf Σ' -> extends Σ Σ' ->
  cumul (Σ, φ) Γ M N -> cumul (Σ', φ) Γ M N.
Proof.
  intros wfΣ [Σ'' ->].
  induction 1; simpl.
  - econstructor. eapply leq_term_subset. eapply global_ext_constraints_app.
    assumption.
  - econstructor 2; eauto. eapply weakening_env_red1; eauto. exists Σ''; eauto.
  - econstructor 3; eauto. eapply weakening_env_red1; eauto. exists Σ''; eauto.
Qed.

(* Lemma weakening_env_consistent_universe_context_instance `{checker_flags} : *)
(*   forall (Σ : global_env_ext) (u : list Level.t) univs, *)
(*     consistent_universe_context_instance (snd Σ) univs u -> *)
(*     forall Σ' : global_env_ext, *)
(*       extends Σ Σ' -> consistent_universe_context_instance (snd Σ') univs u. *)
(* Proof. *)
(*   intros Σ u univs H1 Σ' H2. destruct univs; simpl in *; eauto. *)
(*   all:(destruct UContext.dest; destruct H2 as [Σ'' ->]; simpl; auto). exact (fst ctx). *)
(* Qed. *)
(* Hint Resolve weakening_env_consistent_universe_context_instance : extends. *)
Lemma weakening_env_declared_constant `{CF:checker_flags}:
  forall (Σ : global_env) (cst : ident) (decl : constant_body),
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

Hint Resolve weakening_env_global_ext_levels : extends.

Lemma weakening_env_consistent_instance {cf:checker_flags} Σ Σ' φ ctrs u (H : extends Σ Σ')
  : consistent_instance_ext (Σ, φ) ctrs u
    -> consistent_instance_ext (Σ', φ) ctrs u.
Proof.
    unfold consistent_instance_ext, consistent_instance.
    intros X.
    destruct ctrs; tas. 2: destruct ctx as [cst _].
    all: destruct (AUContext.repr cst).
    all: destruct X as [X1 [X2 [X3 X4]]]; repeat split; tas.
    1,3: eapply forallb_Forall in X2; eapply forallb_Forall, Forall_impl; tea;
      intros x H0; now eapply weakening_env_global_ext_levels'.
    all: eapply valid_subset; tea;
      now eapply weakening_env_global_ext_constraints.
Qed.
Hint Resolve weakening_env_consistent_instance : extends.

Lemma weakening_env `{checker_flags} :
  env_prop (fun Σ Γ t T =>
              forall Σ', wf Σ' -> extends Σ.1 Σ' -> (Σ', Σ.2) ;;; Γ |- t : T).
Proof.
  apply typing_ind_env; intros;
    rename_all_hyps; try solve [econstructor; eauto 2 with extends].

  - econstructor; eauto 2 with extends.
    eapply check_correct_arity_subset; tea.
    apply weakening_env_global_ext_constraints; tas.
    close_Forall. intros; intuition eauto with extends.
  - econstructor; eauto with extends.
    eapply All_local_env_impl. eapply X.
    clear -wfΣ' extΣ. simpl; intros.
    unfold lift_typing in *; destruct T; intuition eauto with extends.
    destruct X as [u [tyu Hu]]. exists u. eauto.
    eapply All_impl; eauto; simpl; intuition eauto with extends.
  - econstructor; eauto with extends. auto.
    eapply All_local_env_impl. eapply X.
    clear -wfΣ' extΣ. simpl; intros.
    unfold lift_typing in *; destruct T; intuition eauto with extends.
    destruct X as [u [tyu Hu]]. exists u. eauto.
    eapply All_impl; eauto; simpl; intuition eauto with extends.
  - econstructor. eauto.
    destruct X2 as [isB|[u [Hu Ps]]].
    + left; auto. destruct isB. destruct x as [ctx [u [Heq Hu]]].
      exists ctx, u. split; eauto with extends.
    + right. exists u. eapply Ps; auto.
    + destruct Σ as [Σ φ]. eapply weakening_env_cumul in cumulA; eauto.
Qed.

Definition weaken_env_prop `{checker_flags}
           (P : global_env_ext -> context -> term -> option term -> Type) :=
  forall Σ Σ' φ, wf Σ' -> extends Σ Σ' -> forall Γ t T, P (Σ, φ) Γ t T -> P (Σ', φ) Γ t T.

Lemma weakening_on_global_decl `{checker_flags} P Σ Σ' φ decl :
  weaken_env_prop P ->
  wf Σ' -> extends Σ Σ' ->
  on_global_decl P (Σ, φ) decl ->
  on_global_decl P (Σ', φ) decl.
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
    unfold on_constructors in *. eapply Alli_impl_trans; eauto.
    intros ik [[id t] ar]. unfold on_constructor, on_type in *; intuition eauto.
    destruct b. exists x0.
    -- induction (cshape_args x0); simpl in *; auto.
       destruct a0 as [na [b|] ty]; simpl in *; intuition eauto.
    -- unfold on_type in *; intuition eauto.
    -- intros Hprojs; destruct onProjections; try constructor; auto.
       eapply Alli_impl; eauto. intros ip [id trm].
       unfold on_projection, on_type; eauto.
    -- unfold Alli_impl_trans. simpl.
       revert onConstructors ind_sorts. generalize (ind_ctors x).
       unfold Alli_rect.
       unfold check_ind_sorts. destruct universe_family; auto.
       --- intros ? onCs. depelim onCs; simpl; auto. depelim onCs; simpl; auto.
           destruct hd as [[? ?] ?]. unfold prod_rect; simpl.
           destruct o as [? [? ?]]. simpl. auto.
       --- intros ? onCs. clear onI. induction onCs; simpl; intuition auto.
           destruct hd as [[? ?] ?]. unfold prod_rect; simpl.
           destruct p as [? [? ?]]. simpl in *. auto.
           destruct Hext; subst; simpl; auto.
           clear H2.
           eapply leq_universe_subset; eauto.
           eapply global_ext_constraints_app; tas.
       --- intros ? onCs. clear onI. induction onCs; simpl; intuition auto.
           destruct hd as [[? ?] ?]. unfold prod_rect; simpl.
           destruct p as [? [? ?]]. simpl in *. auto.
           destruct Hext; subst; simpl; auto. clear H2.
           eapply leq_universe_subset; eauto.
           eapply global_ext_constraints_app; tas.
  - red in onP |- *. eapply All_local_env_impl; eauto.
Qed.

Lemma weakening_env_lookup_on_global_env `{checker_flags} P Σ Σ' c decl :
  weaken_env_prop P ->
  wf Σ' -> extends Σ Σ' -> on_global_env P Σ ->
  lookup_env Σ c = Some decl ->
  on_global_decl P (Σ', universes_decl_of_decl decl) decl.
Proof.
  intros HP wfΣ Hext HΣ.
  induction HΣ; simpl. congruence.
  assert (HH: extends Σ Σ'). {
    destruct Hext as [Σ'' HΣ''].
    exists ((Σ'' ++ [d])%list). now rewrite <- app_assoc. }
  destruct ident_eq.
  - intros [= ->].
    clear Hext; eapply weakening_on_global_decl; eauto.
  - now apply IHHΣ.
Qed.

Lemma weaken_lookup_on_global_env `{checker_flags} P Σ c decl :
  weaken_env_prop P ->
  wf Σ -> on_global_env P Σ ->
  lookup_env Σ c = Some decl ->
  on_global_decl P (Σ, universes_decl_of_decl decl) decl.
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

Lemma declared_minductive_inv `{checker_flags} Σ P ind mdecl :
  weaken_env_prop (lift_typing P) ->
  wf Σ -> Forall_decls_typing P Σ ->
  declared_minductive Σ ind mdecl ->
  on_inductive (lift_typing P) (Σ, ind_universes mdecl) ind mdecl.
Proof.
  intros.
  eapply weaken_lookup_on_global_env in X1; eauto. apply X1.
Qed.

Lemma declared_inductive_inv `{checker_flags} Σ P ind mdecl idecl :
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

Lemma declared_constructor_inv `{checker_flags} Σ P mdecl idecl ref cdecl :
  weaken_env_prop (lift_typing P) ->
  wf Σ -> Forall_decls_typing P Σ ->
  declared_constructor Σ mdecl idecl ref cdecl ->
  on_constructor (lift_typing P) (Σ, ind_universes mdecl) (inductive_mind (fst ref)) mdecl (inductive_ind (fst ref)) idecl (snd ref) cdecl.
Proof.
  intros.
  destruct H0 as [Hidecl Hcdecl].
  eapply declared_inductive_inv in Hidecl; eauto.
  apply onConstructors in Hidecl.
  eapply nth_error_alli in Hidecl; eauto.
Qed.

Lemma declared_projection_inv `{checker_flags} Σ P mdecl idecl ref pdecl :
  weaken_env_prop (lift_typing P) ->
  wf Σ -> Forall_decls_typing P Σ ->
  declared_projection Σ mdecl idecl ref pdecl ->
  on_projection (lift_typing P) (Σ, ind_universes mdecl) (inductive_mind (fst (fst ref))) mdecl
                (inductive_ind (fst (fst ref))) idecl (snd ref) pdecl.
Proof.
  intros.
  destruct H0 as [Hidecl [Hcdecl Hnpar]].
  eapply declared_inductive_inv in Hidecl; eauto.
  pose proof (onProjections Hidecl). apply on_projs in X2.
  eapply nth_error_alli in X2; eauto.
  eapply nth_error_Some_length in Hcdecl.
  destruct (ind_projs idecl); simpl in *. lia. congruence.
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

Lemma weaken_wf_local `{checker_flags} (Σ : global_env_ext) Σ' Γ :
  extends Σ Σ' -> wf Σ' -> wf_local Σ Γ -> wf_local (Σ', Σ.2) Γ.
Proof.
  intros * Hext wfΣ' *.
  induction 1; constructor; auto; destruct Σ; eauto using weaken_env_prop_typing.
Qed.
Hint Resolve 100 weaken_wf_local : pcuic.

Lemma on_declared_constant `{checker_flags} Σ cst decl :
  wf Σ -> declared_constant Σ cst decl ->
  on_constant_decl (lift_typing typing) (Σ, cst_universes decl) decl.
Proof.
  intros.
  eapply declared_constant_inv; tea.
  apply weaken_env_prop_typing.
Qed.

Lemma declared_constant_inj {Σ c} decl1 decl2 :
  declared_constant Σ c decl1 -> declared_constant Σ c decl2 -> decl1 = decl2.
Proof.
  intros. unfold declared_constant in *. rewrite H in H0.
  now inv H0.
Qed.

Lemma on_declared_minductive `{checker_flags} {Σ ref decl} :
  wf Σ ->
  declared_minductive Σ ref decl ->
  on_inductive (lift_typing typing) (Σ, ind_universes decl) ref decl.
Proof.
  intros wfΣ Hdecl.
  apply (declared_minductive_inv _ _ _ _ weaken_env_prop_typing wfΣ wfΣ Hdecl).
Qed.

Lemma on_declared_inductive `{checker_flags} {Σ ref mdecl idecl} :
  wf Σ ->
  declared_inductive Σ mdecl ref idecl ->
  on_inductive (lift_typing typing) (Σ, ind_universes mdecl) (inductive_mind ref) mdecl *
  on_ind_body (lift_typing typing) (Σ, ind_universes mdecl) (inductive_mind ref) mdecl (inductive_ind ref) idecl.
Proof.
  intros wfΣ Hdecl.
  split. destruct Hdecl as [Hmdecl _]. now apply on_declared_minductive in Hmdecl.
  apply (declared_inductive_inv _ _ _ mdecl idecl weaken_env_prop_typing wfΣ wfΣ Hdecl).
Qed.

Lemma on_declared_constructor `{checker_flags} {Σ ref mdecl idecl cdecl} :
  wf Σ ->
  declared_constructor Σ mdecl idecl ref cdecl ->
  on_inductive (lift_typing typing) (Σ, ind_universes mdecl) (inductive_mind (fst ref)) mdecl *
  on_ind_body (lift_typing typing) (Σ, ind_universes mdecl) (inductive_mind (fst ref)) mdecl (inductive_ind (fst ref)) idecl *
  on_constructor (lift_typing typing) (Σ, ind_universes mdecl) (inductive_mind (fst ref)) mdecl (inductive_ind (fst ref)) idecl (snd ref) cdecl.
Proof.
  intros wfΣ Hdecl.
  split. destruct Hdecl as [Hidecl Hcdecl]. now apply on_declared_inductive in Hidecl.
  apply (declared_constructor_inv _ _ mdecl idecl ref cdecl weaken_env_prop_typing wfΣ wfΣ Hdecl).
Qed.

Lemma on_declared_projection `{checker_flags} {Σ ref mdecl idecl pdecl} :
  wf Σ ->
  declared_projection Σ mdecl idecl ref pdecl ->
  on_inductive (lift_typing typing) (Σ, ind_universes mdecl) (inductive_mind (fst (fst ref))) mdecl *
  on_ind_body (lift_typing typing) (Σ, ind_universes mdecl) (inductive_mind (fst (fst ref))) mdecl (inductive_ind (fst (fst ref))) idecl *
  on_projection (lift_typing typing) (Σ, ind_universes mdecl) (inductive_mind (fst (fst ref))) mdecl
                (inductive_ind (fst (fst ref))) idecl (snd ref) pdecl.
Proof.
  intros wfΣ Hdecl.
  split. destruct Hdecl as [Hidecl Hcdecl]. now apply on_declared_inductive in Hidecl.
  apply (declared_projection_inv _ _ mdecl idecl ref pdecl weaken_env_prop_typing wfΣ wfΣ Hdecl).
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
  induction wfΣ; simpl. discriminate.
  cbn in HH. subst udecl. destruct (ident_eq c (global_decl_ident d)).
  - apply some_inj in HH; destruct HH.
    clear -o. unfold on_udecl, on_udecl_prop in *.
    destruct o as [H1 [H2 [H3 H4]]]. repeat split.
    + clear -H2. intros [[? ?] ?] Hc. specialize (H2 _ Hc).
      destruct H2 as [H H']. simpl. split.
      apply LevelSet.union_spec in H. apply LevelSet.union_spec.
      destruct H; [now left|right]. apply LevelSet.union_spec; now right.
      apply LevelSet.union_spec in H'. apply LevelSet.union_spec.
      destruct H'; [now left|right]. apply LevelSet.union_spec; now right.
    + revert H3. case_eq (universes_decl_of_decl d); trivial.
      intros ctx eq Hctx. repeat split.
      * auto.
      * intros l Hl. simpl. replace (monomorphic_levels_decl d) with ctx.1.
        -- apply LevelSet.union_spec; now left.
        -- clear -eq. destruct d as [? c|? c]; cbn in *.
           all: destruct c; cbn in *; now rewrite eq.
      * simpl. replace (monomorphic_constraints_decl d) with ctx.2.
        -- intros c Hc; apply ConstraintSet.union_spec; now left.
        -- clear -eq. destruct d as [? c|? c]; cbn in *.
           all: destruct c; cbn in *; now rewrite eq.
      * clear -eq H4. destruct H4 as [v Hv]. exists v.
      intros c Hc; apply (Hv c).
      apply ConstraintSet.union_spec in Hc; destruct Hc as [Hc|Hc].
      2: apply ConstraintSet.union_spec in Hc; destruct Hc as [Hc|Hc].
      -- apply ConstraintSet.union_spec. simpl in *. left; now rewrite eq.
      -- apply ConstraintSet.union_spec; left. simpl.
         destruct d as [? [? ? []]|? [? ? ? ? []]]; simpl in *; tas;
           now apply ConstraintSet.empty_spec in Hc.
      -- apply ConstraintSet.union_spec; now right.
  - specialize (IHwfΣ HH). revert IHwfΣ o; clear.
    generalize (universes_decl_of_decl decl); intros d' HH Hd.
    unfold on_udecl_prop in *.
    destruct HH as [H1 H2]. split.
    + clear -H1. intros [[? ?] ?] Hc. specialize (H1 _ Hc).
      destruct H1 as [H H']. simpl. split.
      apply LevelSet.union_spec in H. apply LevelSet.union_spec.
      destruct H; [now left|right]. apply LevelSet.union_spec; now right.
      apply LevelSet.union_spec in H'. apply LevelSet.union_spec.
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
          -- clear -Hc. destruct d as [? [? ? []]|? [? ? ? ? []]]; cbn in *.
             all: try (apply ConstraintSet.empty_spec in Hc; contradiction).
             all: apply ConstraintSet.union_spec; now left.
          -- apply ConstraintSet.union_spec; now right.
Qed.
