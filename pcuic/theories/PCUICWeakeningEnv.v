(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia.
From MetaCoq.Template Require Import config utils AstUtils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICLiftSubst PCUICUnivSubst PCUICTyping.
Require Import ssreflect ssrbool.
From Equations Require Import Equations.

(** * Weakening lemmas w.r.t. the global environment *)

Set Asymmetric Patterns.

Generalizable Variables Σ Γ t T.

Definition extends (Σ Σ' : global_context) :=
  { Σ'' & Σ' = (Σ'' ++ fst Σ, snd Σ)%list }.

Lemma lookup_env_Some_fresh `{checker_flags} Σ φ c decl :
  wf (Σ, φ) -> lookup_env Σ c = Some decl ->
  ~ (fresh_global c Σ).
Proof. unfold wf. unfold on_global_env; simpl.
  induction 1; simpl. congruence.
  destruct ident_eq eqn:Heq. intros [= ->].
  rewrite <- (reflect_iff _ _ (ident_eq_spec _ _)) in Heq.
  intro. inv H0. congruence.
  intros Hl; specialize (IHX Hl).
  intro. inv H0. contradiction.
Qed.

Lemma extends_lookup `{checker_flags} Σ Σ' c decl :
  wf Σ' -> extends Σ Σ' ->
  lookup_env (fst Σ) c = Some decl -> lookup_env (fst Σ') c = Some decl.
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

Lemma extends_wf_local:
  forall (H : checker_flags) (Σ : global_context) (Γ : context)
         (wfΓ : wf_local Σ Γ),
    All_local_env_over typing
      (fun Σ0 Γ0 wfΓ (t T : term) ty =>
         forall Σ' : global_context, wf Σ' -> extends Σ0 Σ' -> Σ';;; Γ0 |- t : T) Σ Γ wfΓ ->
    forall Σ' : global_context, wf Σ' -> extends Σ Σ' -> wf_local Σ' Γ.
Proof.
  intros H Σ Γ X X0 Σ' H0.
  induction X0; try econstructor; simpl in *; auto.
  destruct tu as [u Hu]; exists u; auto.
Qed.
Hint Resolve extends_wf_local : extends.

Lemma weakening_env_red1 `{CF:checker_flags} Σ Σ' Γ M N :
  wf Σ' -> extends Σ Σ' ->
  red1 (fst Σ) Γ M N ->
  red1 (fst Σ') Γ M N.
Proof.
  induction 3 using red1_ind_all;
    try solve [econstructor; eauto;
               eapply (OnOne2_impl X1); simpl; intuition eauto].

  eapply extends_lookup in X0; eauto.
  econstructor; eauto.
Qed.

Lemma weakening_env_cumul `{CF:checker_flags} Σ Σ' Γ M N :
  wf Σ' -> extends Σ Σ' ->
  cumul Σ Γ M N -> cumul Σ' Γ M N.
Proof.
  intros wfΣ [Σ'' ->].
  induction 1; simpl.

  econstructor; eauto.

  econstructor 2; eauto. eapply weakening_env_red1; eauto. exists Σ''; eauto.
  econstructor 3; eauto. eapply weakening_env_red1; eauto. exists Σ''; eauto.
Qed.

Lemma weakening_env_consistent_universe_context_instance:
  forall (Σ : global_context) (u : list Level.t) univs,
    consistent_universe_context_instance (snd Σ) univs u ->
    forall Σ' : global_context,
      extends Σ Σ' -> consistent_universe_context_instance (snd Σ') univs u.
Proof.
  intros Σ u univs H1 Σ' H2. destruct univs; simpl in *; eauto.
  all:(destruct UContext.dest; destruct H2 as [Σ'' ->]; simpl; auto). exact (fst ctx).
Qed.
Hint Resolve weakening_env_consistent_universe_context_instance : extends.

Lemma weakening_env_declared_constant:
  forall (H : checker_flags) (Σ : global_context) (cst : ident) (decl : constant_body),
    declared_constant (fst Σ) cst decl ->
    forall Σ' : global_context, wf Σ' -> extends Σ Σ' -> declared_constant (fst Σ') cst decl.
Proof.
  intros H Σ cst decl H0 Σ' X2 H2.
  eapply extends_lookup; eauto.
Qed.
Hint Resolve weakening_env_declared_constant : extends.

Lemma weakening_env_declared_minductive:
  forall (H : checker_flags) (Σ : global_context) ind decl,
    declared_minductive (fst Σ) ind decl ->
    forall Σ' : global_context, wf Σ' -> extends Σ Σ' -> declared_minductive (fst Σ') ind decl.
Proof.
  intros H Σ cst decl H0 Σ' X2 H2.
  eapply extends_lookup; eauto.
Qed.
Hint Resolve weakening_env_declared_minductive : extends.

Lemma weakening_env_declared_inductive:
  forall (H : checker_flags) (Σ : global_context) ind mdecl decl,
    declared_inductive (fst Σ) ind mdecl decl ->
    forall Σ' : global_context, wf Σ' -> extends Σ Σ' -> declared_inductive (fst Σ') ind mdecl decl.
Proof.
  intros H Σ cst decl H0 [Hmdecl Hidecl] Σ' X2 H2. split; eauto with extends.
Qed.
Hint Resolve weakening_env_declared_inductive : extends.

Lemma weakening_env_declared_constructor :
  forall (H : checker_flags) (Σ : global_context) ind mdecl idecl decl,
    declared_constructor (fst Σ) ind mdecl idecl decl ->
    forall Σ' : global_context, wf Σ' -> extends Σ Σ' ->
    declared_constructor (fst Σ') ind mdecl idecl decl.
Proof.
  intros H Σ cst mdecl idecl cdecl [Hidecl Hcdecl] Σ' X2 H2.
  split; eauto with extends.
Qed.
Hint Resolve weakening_env_declared_constructor : extends.

Lemma weakening_env_declared_projection :
  forall (H : checker_flags) (Σ : global_context) ind mdecl idecl decl,
    declared_projection (fst Σ) ind mdecl idecl decl ->
    forall Σ' : global_context, wf Σ' -> extends Σ Σ' ->
    declared_projection (fst Σ') ind mdecl idecl decl.
Proof.
  intros H Σ cst mdecl idecl cdecl [Hidecl Hcdecl] Σ' X2 H2.
  split; eauto with extends.
Qed.
Hint Resolve weakening_env_declared_projection : extends.

(* Lemma weakening_All_local_env_impl `{checker_flags} (P Q : context -> term -> option term -> Type) l : *)
(*   All_local_env (P Σ) l -> *)
(*   (forall Γ t T, P Σ Γ t T -> Q Σ' Γ t T) -> *)
(*   All_local_env (Q Σ') l. *)
(* Proof. induction 1; intros; simpl; econstructor; eauto. Qed. *)

Ltac my_rename_hyp h th :=
  match th with
  | (extends ?t _) => fresh "ext" t
  | _ => PCUICTyping.my_rename_hyp h th
  end.

Ltac rename_hyp h ht ::= my_rename_hyp h ht.

Lemma weakening_env `{checker_flags} :
  env_prop (fun Σ Γ t T =>
              forall Σ', wf Σ' -> extends Σ Σ' -> Σ' ;;; Γ |- t : T).
Proof.
  apply typing_ind_env; intros; rename_all_hyps; try solve [econstructor; eauto 2 with extends].

  - econstructor; eauto 2 with extends.
    destruct extΣ as [Σ'' ->]. simpl; auto.
    close_Forall. intros; intuition eauto with extends.
  - econstructor; eauto with extends.
    eapply All_local_env_impl. eapply X.
    clear -wfΣ' extΣ. simpl; intros.
    unfold lift_typing in *; destruct T; intuition eauto with extends.
    destruct X as [u [tyu Hu]]. exists u. eauto.
    eapply All_impl; eauto; simpl; intuition eauto with extends.
  - econstructor; eauto with extends.
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
    + eapply weakening_env_cumul in cumulA; eauto.
Qed.

Definition weaken_env_prop `{checker_flags}
           (P : global_context -> context -> term -> option term -> Type) :=
  forall Σ Σ', wf Σ' -> extends Σ Σ' -> forall Γ t T, P Σ Γ t T -> P Σ' Γ t T.

Lemma weakening_on_global_decl `{checker_flags} P Σ Σ' decl :
  weaken_env_prop P ->
  wf Σ' -> extends Σ Σ' ->
  on_global_decl P Σ decl ->
  on_global_decl P Σ' decl.
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
    destruct X. unshelve econstructor.
    unfold on_constructors in *. eapply Alli_impl_trans; eauto.
    intros ik [[id t] ar]. unfold on_constructor, on_type in *; intuition eauto.
    destruct b. exists x0.
    -- induction (cshape_args x0); simpl in *; auto.
       destruct a0 as [na [b|] ty]; simpl in *; intuition eauto.
    -- destruct onArity; constructor; unfold on_type in *; intuition eauto.
    -- intros Hprojs; destruct onProjections; try constructor; auto.
       eapply Alli_impl; eauto. intros ip [id trm].
       unfold on_projection, on_type; eauto.
       destruct decompose_prod_assum. intuition auto.
       eapply HPΣ; eauto.
    -- unfold Alli_impl_trans. simpl.
       destruct onkelim as [sf [Hsf Hsfle]].
       exists sf; intuition eauto. rewrite -{}Hsf.
       unfold elimination_topsort.
       destruct destArity as [[ctx s]|]; simpl; auto.
       destruct universe_family; auto.
       revert onConstructors. generalize (ind_ctors x).
       unfold Alli_rect.
       intros ? onCs. depelim onCs; auto. depelim onCs; simpl; auto.
       destruct hd as [[? ?] ?]. unfold prod_rect; simpl.
       destruct o as [? [? ?]]. simpl. reflexivity.
  - red in onP |- *. eapply All_local_env_impl; eauto.
Qed.

Lemma weakening_env_lookup_on_global_env `{checker_flags} P Σ Σ' c decl :
  weaken_env_prop P ->
  wf Σ' -> extends Σ Σ' -> on_global_env P Σ ->
  lookup_env (fst Σ) c = Some decl ->
  on_global_decl P Σ' decl.
Proof.
  intros HP wfΣ Hext HΣ. destruct Σ as [Σ graph].
  red in HΣ. simpl in *.
  induction HΣ; simpl. congruence.
  destruct ident_eq. intros [= ->].
  eapply weakening_on_global_decl. eauto. eauto. 2:{ eapply o. }
  destruct Hext. simpl in *. rewrite e.
  exists ((x ++ [decl])%list). simpl.
  now rewrite <- app_assoc.

  apply IHHΣ.
  destruct Hext as [Σ'' ->]. simpl. red.
  exists (Σ'' ++ [d])%list. simpl.
  now rewrite <- app_assoc.
Qed.

Lemma weaken_lookup_on_global_env `{checker_flags} P Σ c decl :
  weaken_env_prop P ->
  wf Σ -> on_global_env P Σ ->
  lookup_env (fst Σ) c = Some decl ->
  on_global_decl P Σ decl.
Proof.
  intros. eapply weakening_env_lookup_on_global_env; eauto.
  exists []; simpl; destruct Σ; eauto.
Qed.

Lemma declared_constant_inv `{checker_flags} Σ P cst decl :
  weaken_env_prop (lift_typing P) ->
  wf Σ -> Forall_decls_typing P Σ ->
  declared_constant (fst Σ) cst decl ->
  on_constant_decl (lift_typing P) Σ decl.
Proof.
  intros.
  eapply weaken_lookup_on_global_env in X1; eauto. apply X1.
Qed.

Lemma declared_minductive_inv `{checker_flags} Σ P ind mdecl :
  weaken_env_prop (lift_typing P) ->
  wf Σ -> Forall_decls_typing P Σ ->
  declared_minductive (fst Σ) ind mdecl ->
  on_inductive (lift_typing P) Σ ind mdecl.
Proof.
  intros.
  eapply weaken_lookup_on_global_env in X1; eauto. apply X1.
Qed.

Lemma declared_inductive_inv `{checker_flags} Σ P ind mdecl idecl :
  weaken_env_prop (lift_typing P) ->
  wf Σ -> Forall_decls_typing P Σ ->
  declared_inductive (fst Σ) mdecl ind idecl ->
  on_ind_body (lift_typing P) Σ (inductive_mind ind) mdecl (inductive_ind ind) idecl.
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
  declared_constructor (fst Σ) mdecl idecl ref cdecl ->
  on_constructor (lift_typing P) Σ (inductive_mind (fst ref)) mdecl (inductive_ind (fst ref)) idecl (snd ref) cdecl.
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
  declared_projection (fst Σ) mdecl idecl ref pdecl ->
  on_projection (lift_typing P) Σ (inductive_mind (fst (fst ref))) mdecl
                (inductive_ind (fst (fst ref))) idecl (snd ref) pdecl.
Proof.
  intros.
  destruct H0 as [Hidecl [Hcdecl Hnpar]].
  eapply declared_inductive_inv in Hidecl; eauto.
  apply onProjections, on_projs in Hidecl.
  eapply nth_error_alli in Hidecl; eauto.
  eapply nth_error_Some_length in Hcdecl.
  destruct (ind_projs idecl); simpl in *. lia. congruence.
Qed.

Lemma wf_extends `{checker_flags} {Σ Σ'} : wf Σ' -> extends Σ Σ' -> wf Σ.
Proof.
  unfold wf, on_global_env. unfold extends. simpl.
  intros HΣ' [Σ'' ->]. simpl in *.
  induction Σ''. auto.
  inv HΣ'. auto.
Qed.

Lemma weaken_env_prop_typing `{checker_flags} : weaken_env_prop (lift_typing typing).
Proof.
  red. intros * wfΣ' Hext *.
  destruct T; simpl.
  intros Ht. pose proof (wf_extends wfΣ' Hext).
  eapply weakening_env; eauto. eapply typing_wf_local in Ht; eauto.
  intros [s Ht]. pose proof (wf_extends wfΣ' Hext). exists s.
  eapply weakening_env; eauto. eapply typing_wf_local in Ht; eauto.
Qed.
Hint Unfold weaken_env_prop : pcuic.

Lemma weaken_wf_local `{checker_flags} Σ Σ' Γ : extends Σ Σ' -> wf Σ' -> wf_local Σ Γ -> wf_local Σ' Γ.
Proof.
  intros * wfΣ' Hext *.
  induction 1; constructor; auto; eauto using weaken_env_prop_typing.
Qed.
Hint Resolve 100 weaken_wf_local : pcuic.

Lemma on_declared_minductive `{checker_flags} {Σ ref decl} :
  wf Σ ->
  declared_minductive (fst Σ) ref decl ->
  on_inductive (lift_typing typing) Σ ref decl.
Proof.
  intros wfΣ Hdecl.
  apply (declared_minductive_inv _ _ _ _ weaken_env_prop_typing wfΣ wfΣ Hdecl).
Qed.

Lemma on_declared_inductive `{checker_flags} {Σ ref mdecl idecl} :
  wf Σ ->
  declared_inductive (fst Σ) mdecl ref idecl ->
  on_inductive (lift_typing typing) Σ (inductive_mind ref) mdecl *
  on_ind_body (lift_typing typing) Σ (inductive_mind ref) mdecl (inductive_ind ref) idecl.
Proof.
  intros wfΣ Hdecl.
  split. destruct Hdecl as [Hmdecl _]. now apply on_declared_minductive in Hmdecl.
  apply (declared_inductive_inv _ _ _ mdecl idecl weaken_env_prop_typing wfΣ wfΣ Hdecl).
Qed.

Lemma on_declared_constructor `{checker_flags} {Σ ref mdecl idecl cdecl} :
  wf Σ ->
  declared_constructor (fst Σ) mdecl idecl ref cdecl ->
  on_inductive (lift_typing typing) Σ (inductive_mind (fst ref)) mdecl *
  on_ind_body (lift_typing typing) Σ (inductive_mind (fst ref)) mdecl (inductive_ind (fst ref)) idecl *
  on_constructor (lift_typing typing) Σ (inductive_mind (fst ref)) mdecl (inductive_ind (fst ref)) idecl (snd ref) cdecl.
Proof.
  intros wfΣ Hdecl.
  split. destruct Hdecl as [Hidecl Hcdecl]. now apply on_declared_inductive in Hidecl.
  apply (declared_constructor_inv _ _ mdecl idecl ref cdecl weaken_env_prop_typing wfΣ wfΣ Hdecl).
Qed.

Lemma on_declared_projection `{checker_flags} {Σ ref mdecl idecl pdecl} :
  wf Σ ->
  declared_projection (fst Σ) mdecl idecl ref pdecl ->
  on_inductive (lift_typing typing) Σ (inductive_mind (fst (fst ref))) mdecl *
  on_ind_body (lift_typing typing) Σ (inductive_mind (fst (fst ref))) mdecl (inductive_ind (fst (fst ref))) idecl *
  on_projection (lift_typing typing) Σ (inductive_mind (fst (fst ref))) mdecl
                (inductive_ind (fst (fst ref))) idecl (snd ref) pdecl.
Proof.
  intros wfΣ Hdecl.
  split. destruct Hdecl as [Hidecl Hcdecl]. now apply on_declared_inductive in Hidecl.
  apply (declared_projection_inv _ _ mdecl idecl ref pdecl weaken_env_prop_typing wfΣ wfΣ Hdecl).
Qed.
