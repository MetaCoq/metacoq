(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
  PCUICEquality PCUICContextSubst PCUICUnivSubst PCUICCases
  PCUICReduction PCUICCumulativity PCUICTyping
  PCUICGuardCondition PCUICGlobalEnv
  PCUICWeakeningEnv PCUICWeakeningEnvConv.
From Equations Require Import Equations.

Require Import ssreflect.

Set Default Goal Selector "!".
Implicit Types (cf : checker_flags).

Ltac my_rename_hyp h th :=
  match th with
  | (extends ?t _) => fresh "ext" t
  | (extends ?t.1 _) => fresh "ext" t
  | (extends _ _) => fresh "ext"
  | _ => PCUICTyping.my_rename_hyp h th
  | _ => PCUICWeakeningEnv.my_rename_hyp h th
  end.

Ltac rename_hyp h ht ::= my_rename_hyp h ht.

Lemma extends_wf_local `{cf : checker_flags} Σ Γ (wfΓ : wf_local Σ Γ) :
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
  - apply infer_typing_sort_impl with id tu. intro; eauto.
  - apply infer_typing_sort_impl with id tu. intro; eauto.
Qed.
#[global]
Hint Resolve extends_wf_local : extends.

Lemma extends_check_recursivity_kind `{cf : checker_flags} Σ ind k Σ' : extends Σ Σ' -> wf Σ' ->
  check_recursivity_kind (lookup_env Σ) ind k -> check_recursivity_kind (lookup_env Σ') ind k.
Proof.
  intros ext wfΣ'.
  rewrite /check_recursivity_kind.
  destruct lookup_env eqn:Heq => //.
  eapply extends_lookup in Heq; eauto.
  now rewrite Heq.
Qed.

Lemma extends_wf_fixpoint `{cf : checker_flags} (Σ Σ' : global_env_ext) mfix : extends Σ Σ' -> wf Σ' ->
  wf_fixpoint Σ mfix -> wf_fixpoint Σ' mfix.
Proof.
  intros ext wfΣ'.
  unfold wf_fixpoint, wf_fixpoint_gen.
  move/andb_and => [] -> /=.
  destruct map_option_out as [[|ind inds]|]; auto.
  move/andb_and => [->] /=.
  now apply extends_check_recursivity_kind.
Qed.

Lemma extends_wf_cofixpoint `{cf : checker_flags} (Σ Σ' : global_env_ext) mfix : extends Σ Σ' -> wf Σ' ->
  wf_cofixpoint Σ mfix -> wf_cofixpoint Σ' mfix.
Proof.
  intros ext wfΣ'.
  unfold wf_cofixpoint, wf_cofixpoint_gen.
  destruct map_option_out as [[|ind inds]|]; auto.
  move/andb_and => [->] /=.
  now apply extends_check_recursivity_kind.
Qed.
#[global]
Hint Resolve extends_wf_fixpoint extends_wf_cofixpoint : extends.

Lemma extends_primitive_constant Σ Σ' p t :
  extends Σ Σ' ->
  primitive_constant Σ p = Some t ->
  primitive_constant Σ' p = Some t.
Proof.
  intros [_ _ ext].
  unfold primitive_constant.
  case: ext.
  destruct p; case => //.
  - move=> _. case => //.
  - move=> _; case => //.
  - case => //.
Qed.
Local Hint Resolve extends_primitive_constant : extends.

Lemma weakening_env `{checker_flags} :
  env_prop (fun Σ Γ t T =>
              forall Σ', wf Σ' -> extends Σ.1 Σ' -> (Σ', Σ.2) ;;; Γ |- t : T)
           (fun Σ Γ =>
             forall Σ', wf Σ' -> extends Σ.1 Σ' -> wf_local (Σ', Σ.2) Γ).
Proof.
  apply typing_ind_env; intros;
    rename_all_hyps; try solve [econstructor; eauto 2 with extends].

  - induction X; constructor; eauto 2 with extends.
    + apply infer_typing_sort_impl with id tu; intro; auto.
    + apply infer_typing_sort_impl with id tu; intro; auto.
    + eapply Hc; eauto.
  - econstructor; eauto 2 with extends.
    now apply extends_wf_universe.
  - econstructor; eauto 2 with extends. all: econstructor; eauto 2 with extends.
    * revert X5. clear -Σ' wfΣ' extΣ.
      induction 1; constructor; try destruct t0; eauto with extends.
    * close_Forall. intros; intuition eauto with extends.
  - econstructor; eauto with extends.
    + specialize (forall_Σ' _ wfΣ' extΣ).
      now apply wf_local_app_inv in forall_Σ'.
    + eapply fix_guard_extends; eauto.
    + eapply (All_impl X0); intros d X.
      apply (lift_typing_impl X); now intros ? [].
    + eapply (All_impl X1); intros d X.
      apply (lift_typing_impl X); now intros ? [].
  - econstructor; eauto with extends.
    + specialize (forall_Σ' _ wfΣ' extΣ).
      now apply wf_local_app_inv in forall_Σ'.
    + eapply cofix_guard_extends; eauto.
    + eapply (All_impl X0); intros d X.
      apply (lift_typing_impl X); now intros ? [].
    + eapply (All_impl X1); intros d X.
      apply (lift_typing_impl X); now intros ? [].
  - econstructor. 1: eauto.
    + eapply forall_Σ'1; eauto.
    + destruct Σ as [Σ φ]. eapply weakening_env_cumulSpec in cumulA; eauto.
Qed.

Lemma weakening_on_global_decl `{checker_flags} P Σ Σ' φ kn decl :
  weaken_env_prop cumulSpec0 (lift_typing typing) P ->
  wf Σ -> wf Σ' -> extends Σ Σ' ->
  on_global_decl cumulSpec0 P (Σ, φ) kn decl ->
  on_global_decl cumulSpec0 P (Σ', φ) kn decl.
Proof.
  unfold weaken_env_prop.
  intros HPΣ wfΣ wfΣ' Hext Hdecl.
  destruct decl.
  1:{
    destruct c. destruct cst_body0.
    - simpl in *.
      red in Hdecl |- *. simpl in *.
      eapply (HPΣ Σ Σ'); eauto.
    - eapply (HPΣ Σ Σ'); eauto.
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
           ++ eapply weakening_env_cumulSpec; eauto.
           ++ eapply weakening_env_convSpec; eauto.
           ++ eapply weakening_env_cumulSpec; eauto.
        ** eapply (All2_impl idxs); intros.
          eapply weakening_env_convSpec; eauto.
    + unfold check_ind_sorts in *.
      destruct Universe.is_prop; auto.
      destruct Universe.is_sprop; auto.
      split; [apply fst in ind_sorts|apply snd in ind_sorts].
      * eapply Forall_impl; tea; cbn.
        intros. eapply Forall_impl; tea; simpl; intros.
        eapply leq_universe_subset; tea.
        apply weakening_env_global_ext_constraints; tea.
      * destruct indices_matter; [|trivial]. clear -ind_sorts HPΣ wfΣ wfΣ' Hext.
        induction ind_indices; simpl in *; auto.
        -- eapply (extends_wf_universe (Σ:=(Σ,φ)) Σ'); auto.
        -- destruct a as [na [b|] ty]; simpl in *; intuition eauto.
    + destruct ind_variance => //.
      move: onIndices. unfold ind_respects_variance.
      destruct variance_universes as [[[univs u] u']|] => //.
      intros idx; eapply (All2_fold_impl idx); simpl.
      intros par par' t t' d.
      inv d; constructor; auto.
      ++ eapply weakening_env_cumulSpec; eauto.
      ++ eapply weakening_env_convSpec; eauto.
      ++ eapply weakening_env_cumulSpec; eauto.
  - red in onP |- *. eapply All_local_env_impl; eauto.
  - move: onVariance.
    rewrite /on_variance. destruct ind_universes => //.
    destruct ind_variance => //.
    intros [univs' [i [i' []]]]. exists univs', i, i'. split => //.
    all:eapply weakening_env_consistent_instance; tea.
Qed.

Lemma weakening_on_global_decl_ext `{checker_flags} P Σ Σ' φ kn decl :
  weaken_env_decls_prop cumulSpec0 (lift_typing typing) P ->
  wf Σ' -> extends_decls Σ Σ' ->
  on_global_decl cumulSpec0 P (Σ, φ) kn decl ->
  on_global_decl cumulSpec0 P (Σ', φ) kn decl.
Proof.
  unfold weaken_env_prop.
  intros HPΣ wfΣ' Hext Hdecl.
  pose proof (wfΣ := extends_decls_wf _ _ wfΣ' Hext).
  destruct decl.
  1:{
    destruct c. destruct cst_body0.
    - simpl in *.
      red in Hdecl |- *. simpl in *.
      eapply (HPΣ Σ Σ'); eauto.
    - eapply (HPΣ Σ Σ'); eauto.
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
           ++ eapply weakening_env_cumulSpec; eauto. tc.
           ++ eapply weakening_env_convSpec; eauto. tc.
           ++ eapply weakening_env_cumulSpec; eauto. tc.
        ** eapply (All2_impl idxs); intros.
          eapply weakening_env_convSpec; eauto. tc.
    + unfold check_ind_sorts in *.
      destruct Universe.is_prop; auto.
      destruct Universe.is_sprop; auto.
      split; [apply fst in ind_sorts|apply snd in ind_sorts].
      * eapply Forall_impl; tea; cbn.
        intros. eapply Forall_impl; tea; simpl; intros.
        eapply leq_universe_subset; tea.
        apply weakening_env_global_ext_constraints; tea. tc.
      * destruct indices_matter; [|trivial]. clear -ind_sorts HPΣ wfΣ wfΣ' Hext.
        induction ind_indices; simpl in *; auto.
        -- eapply (extends_wf_universe (Σ:=(Σ,φ)) Σ'); auto. tc.
        -- destruct a as [na [b|] ty]; simpl in *; intuition eauto.
    + destruct ind_variance => //.
      move: onIndices. unfold ind_respects_variance.
      destruct variance_universes as [[[univs u] u']|] => //.
      intros idx; eapply (All2_fold_impl idx); simpl.
      intros par par' t t' d.
      inv d; constructor; auto.
      ++ eapply weakening_env_cumulSpec; eauto; tc.
      ++ eapply weakening_env_convSpec; eauto; tc.
      ++ eapply weakening_env_cumulSpec; eauto; tc.
  - red in onP |- *. eapply All_local_env_impl; eauto.
  - move: onVariance.
    rewrite /on_variance. destruct ind_universes => //.
    destruct ind_variance => //.
    intros [univs' [i [i' []]]]. exists univs', i, i'. split => //.
    all:eapply weakening_env_consistent_instance; tea; tc.
Qed.

Lemma weakening_env_decls_lookup_on_global_env `{checker_flags} P Σ Σ' c decl :
  weaken_env_decls_prop cumulSpec0 (lift_typing typing) P ->
  wf Σ' -> extends_decls Σ Σ' -> on_global_env cumulSpec0 P Σ ->
  lookup_env Σ c = Some decl ->
  on_global_decl cumulSpec0 P (Σ', universes_decl_of_decl decl) c decl.
Proof.
  intros HP wfΣ' Hext HΣ.
  assert (wfΣ := extends_decls_wf _ _ wfΣ' Hext).
  destruct HΣ as [onu onΣ].
  destruct Σ as [univs Σ retro]; cbn in *.
  induction onΣ; simpl. 1: congruence.
  assert (HH: extends_decls {| universes := univs; declarations := Σ; retroknowledge := retro |} Σ'). {
    destruct Hext as [univs' [Σ'' HΣ'']]. split; eauto.
    exists (Σ'' ++ [(kn, d)]). now rewrite <- app_assoc.
  }
  case: eqb_specT; intro eq; subst.
  - intros [= ->]. subst. destruct o.
    clear Hext; eapply weakening_on_global_decl_ext. 3:tea. all:eauto.
  - destruct o. apply IHonΣ; auto.
    destruct wfΣ. split => //. now depelim o0.
Qed.

Lemma weakening_env_lookup_on_global_env `{checker_flags} P Σ Σ' c decl :
  weaken_env_prop cumulSpec0 (lift_typing typing) P ->
  wf Σ -> wf Σ' -> extends Σ Σ' -> on_global_env cumulSpec0 P Σ ->
  lookup_env Σ c = Some decl ->
  on_global_decl cumulSpec0 P (Σ', universes_decl_of_decl decl) c decl.
Proof.
  intros HP wfΣ wfΣ' Hext HΣ.
  destruct HΣ as [onu onΣ].
  destruct Σ as [univs Σ retro]; cbn in *.
  induction onΣ; simpl. 1: congruence.
  assert (HH: extends {| universes := univs; declarations := Σ; retroknowledge := retro |} Σ'). {
    destruct Hext as [univs' [Σ'' HΣ'']]. split; eauto.
    exists (Σ'' ++ [(kn, d)]). now rewrite <- app_assoc.
  }
  destruct o. case: eqb_specT; intro e; subst.
  - intros [= ->]. subst.
    clear Hext; eapply weakening_on_global_decl. 5:tea. all:eauto.
    destruct wfΣ. split => //. now depelim o0.
  - apply IHonΣ; auto.
    destruct wfΣ. split => //. now depelim o0.
Qed.

Lemma weaken_lookup_on_global_env `{checker_flags} P Σ c decl :
  weaken_env_prop cumulSpec0 (lift_typing typing) P ->
  wf Σ -> on_global_env cumulSpec0 P Σ ->
  lookup_env Σ c = Some decl ->
  on_global_decl cumulSpec0 P (Σ, universes_decl_of_decl decl) c decl.
Proof.
  intros. eapply weakening_env_lookup_on_global_env; eauto.
  split => //.
  - split; [lsets|csets].
  - exists []; simpl; destruct Σ; eauto.
  - apply Environment.Retroknowledge.extends_refl.
Qed.

Lemma weaken_decls_lookup_on_global_env `{checker_flags} P Σ c decl :
  weaken_env_decls_prop cumulSpec0 (lift_typing typing) P ->
  wf Σ -> on_global_env cumulSpec0 P Σ ->
  lookup_env Σ c = Some decl ->
  on_global_decl cumulSpec0 P (Σ, universes_decl_of_decl decl) c decl.
Proof.
  intros. eapply weakening_env_decls_lookup_on_global_env; eauto.
  split => //.
  - exists []; simpl; destruct Σ; eauto.
Qed.

Lemma declared_constant_inv `{checker_flags} Σ P cst decl :
  weaken_env_prop cumulSpec0 (lift_typing typing) (lift_typing P) ->
  wf Σ -> Forall_decls_typing P Σ ->
  declared_constant Σ cst decl ->
  on_constant_decl (lift_typing P) (Σ, cst_universes decl) decl.
Proof.
  intros.
  eapply weaken_lookup_on_global_env in X1; eauto. apply X1.
Qed.

Lemma declared_minductive_inv `{checker_flags} {Σ P ind mdecl} :
  weaken_env_prop cumulSpec0 (lift_typing typing) (lift_typing P) ->
  wf Σ -> Forall_decls_typing P Σ ->
  declared_minductive Σ ind mdecl ->
  on_inductive cumulSpec0 (lift_typing P) (Σ, ind_universes mdecl) ind mdecl.
Proof.
  intros.
  eapply weaken_lookup_on_global_env in X1; eauto. apply X1.
Qed.

Lemma declared_inductive_inv `{checker_flags} {Σ P ind mdecl idecl} :
  weaken_env_prop cumulSpec0 (lift_typing typing) (lift_typing P) ->
  wf Σ -> Forall_decls_typing P Σ ->
  declared_inductive Σ ind mdecl idecl ->
  on_ind_body cumulSpec0 (lift_typing P) (Σ, ind_universes mdecl) (inductive_mind ind) mdecl (inductive_ind ind) idecl.
Proof.
  intros.
  destruct H0 as [Hmdecl Hidecl].
  eapply declared_minductive_inv in Hmdecl; cbn in X; eauto.
  apply onInductives in Hmdecl.
  eapply nth_error_alli in Hidecl; eauto.
  apply Hidecl.
Qed.

Lemma declared_constructor_inv `{checker_flags} {Σ P mdecl idecl ref cdecl}
  (HP : weaken_env_prop cumulSpec0 (lift_typing typing) (lift_typing P))
  (wfΣ : wf Σ)
  (HΣ : Forall_decls_typing P Σ)
  (Hdecl : declared_constructor Σ ref mdecl idecl cdecl) :
  ∑ cs,
  let onib := declared_inductive_inv HP wfΣ HΣ (let (x, _) := Hdecl in x) in
  nth_error onib.(ind_cunivs) ref.2 = Some cs
  × on_constructor cumulSpec0 (lift_typing P) (Σ, ind_universes mdecl) mdecl
                   (inductive_ind ref.1) idecl idecl.(ind_indices) cdecl cs.
Proof.
  intros.
  destruct Hdecl as [Hidecl Hcdecl].
  set (declared_inductive_inv HP wfΣ HΣ Hidecl) as HH.
  clearbody HH. pose proof HH.(onConstructors) as HH'.
  eapply All2_nth_error_Some in Hcdecl; tea.
Defined.

Lemma declared_minductive_inv_decls `{checker_flags} {Σ P ind mdecl} :
  weaken_env_decls_prop cumulSpec0 (lift_typing typing) (lift_typing P) ->
  wf Σ -> Forall_decls_typing P Σ ->
  declared_minductive Σ ind mdecl ->
  on_inductive cumulSpec0 (lift_typing P) (Σ, ind_universes mdecl) ind mdecl.
Proof.
  intros.
  eapply weaken_decls_lookup_on_global_env in X1; eauto. apply X1.
Qed.

Lemma declared_inductive_inv_decls `{checker_flags} {Σ P ind mdecl idecl} :
  weaken_env_decls_prop cumulSpec0 (lift_typing typing) (lift_typing P) ->
  wf Σ -> Forall_decls_typing P Σ ->
  declared_inductive Σ ind mdecl idecl ->
  on_ind_body cumulSpec0 (lift_typing P) (Σ, ind_universes mdecl) (inductive_mind ind) mdecl (inductive_ind ind) idecl.
Proof.
  intros.
  destruct H0 as [Hmdecl Hidecl].
  eapply declared_minductive_inv_decls in Hmdecl; cbn in X; eauto.
  apply onInductives in Hmdecl.
  eapply nth_error_alli in Hidecl; eauto.
  apply Hidecl.
Qed.

Lemma declared_constructor_inv_decls `{checker_flags} {Σ P mdecl idecl ref cdecl}
  (HP : weaken_env_decls_prop cumulSpec0 (lift_typing typing) (lift_typing P))
  (wfΣ : wf Σ)
  (HΣ : Forall_decls_typing P Σ)
  (Hdecl : declared_constructor Σ ref mdecl idecl cdecl) :
  ∑ cs,
  let onib := declared_inductive_inv_decls HP wfΣ HΣ (let (x, _) := Hdecl in x) in
  nth_error onib.(ind_cunivs) ref.2 = Some cs
  × on_constructor cumulSpec0 (lift_typing P) (Σ, ind_universes mdecl) mdecl
                   (inductive_ind ref.1) idecl idecl.(ind_indices) cdecl cs.
Proof.
  intros.
  destruct Hdecl as [Hidecl Hcdecl].
  set (declared_inductive_inv_decls HP wfΣ HΣ Hidecl) as HH.
  clearbody HH. pose proof HH.(onConstructors) as HH'.
  eapply All2_nth_error_Some in Hcdecl; tea.
Defined.

Lemma declared_projection_inv `{checker_flags} {Σ P mdecl idecl cdecl ref pdecl} :
  forall (HP : weaken_env_prop cumulSpec0 (lift_typing typing) (lift_typing P))
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
    on_projections mdecl (inductive_mind ref.(proj_ind)) (inductive_ind ref.(proj_ind)) idecl (idecl.(ind_indices)) c *
    (ref.(proj_arg) < context_assumptions c.(cstr_args)) *
    on_projection mdecl (inductive_mind ref.(proj_ind)) (inductive_ind ref.(proj_ind)) c ref.(proj_arg) pdecl
  | _ => False
  end.
Proof.
  intros.
  destruct (declared_inductive_inv HP wfΣ HΣ (let (x, _) := Hdecl in let (x, _) := x in x)) in *.
  destruct Hdecl as [Hidecl [Hcdecl Hnpar]]. simpl.
  move: onProjections. generalize (nth_error_Some_length Hcdecl).
  case: (ind_projs idecl) => //= .
  { lia. }
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


Lemma weaken_env_prop_typing `{checker_flags} : weaken_env_prop cumulSpec0 (lift_typing typing) (lift_typing typing).
Proof.
  red. intros * wfΣ wfΣ' Hext Γ t T HT.
  apply lift_typing_impl with (1 := HT); intros ? Hty.
  eapply (weakening_env (_, _)).
  2: eauto.
  all: auto.
Qed.

Lemma weaken_env_decls_prop_typing `{checker_flags} : weaken_env_decls_prop cumulSpec0 (lift_typing typing) (lift_typing typing).
Proof.
  red. intros * wfΣ' Hext Γ t T HT.
  apply lift_typing_impl with (1 := HT); intros ? Hty.
  eapply (weakening_env (_, _)).
  2-4: eauto.
  * cbn; now eapply extends_decls_wf.
  * tc.
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
  wf Σ -> extends Σ Σ' -> wf Σ' -> wf_local Σ Γ -> wf_local (Σ', Σ.2) Γ.
Proof.
  intros * wfΣ Hext wfΣ' *.
  intros wfΓ.
  eapply (env_prop_wf_local weakening_env); eauto.
Qed.

#[global]
Hint Resolve weaken_wf_local | 100 : pcuic.

Lemma on_declared_minductive `{checker_flags} {Σ ref decl} :
  wf Σ ->
  declared_minductive Σ ref decl ->
  on_inductive cumulSpec0 (lift_typing typing) (Σ, ind_universes decl) ref decl.
Proof.
  intros wfΣ Hdecl.
  apply (declared_minductive_inv weaken_env_prop_typing wfΣ wfΣ Hdecl).
Qed.

Lemma on_declared_inductive `{checker_flags} {Σ ref mdecl idecl} {wfΣ : wf Σ} :
  declared_inductive Σ ref mdecl idecl ->
  on_inductive cumulSpec0 (lift_typing typing) (Σ, ind_universes mdecl) (inductive_mind ref) mdecl *
  on_ind_body cumulSpec0 (lift_typing typing) (Σ, ind_universes mdecl) (inductive_mind ref) mdecl (inductive_ind ref) idecl.
Proof.
  intros Hdecl.
  split.
  - destruct Hdecl as [Hmdecl _]. now apply on_declared_minductive in Hmdecl.
  - apply (declared_inductive_inv weaken_env_prop_typing wfΣ wfΣ Hdecl).
Defined.

Lemma on_declared_constructor `{checker_flags} {Σ ref mdecl idecl cdecl}
  {wfΣ : wf Σ}
  (Hdecl : declared_constructor Σ ref mdecl idecl cdecl) :
  on_inductive cumulSpec0 (lift_typing typing) (Σ, ind_universes mdecl)
               (inductive_mind (fst ref)) mdecl *
  on_ind_body cumulSpec0 (lift_typing typing) (Σ, ind_universes mdecl)
              (inductive_mind (fst ref)) mdecl (inductive_ind (fst ref)) idecl *
  ∑ ind_ctor_sort,
    let onib := declared_inductive_inv weaken_env_prop_typing wfΣ wfΣ (let (x, _) := Hdecl in x) in
     nth_error (ind_cunivs onib) ref.2 = Some ind_ctor_sort
    ×  on_constructor cumulSpec0 (lift_typing typing) (Σ, ind_universes mdecl)
                 mdecl (inductive_ind (fst ref))
                 idecl idecl.(ind_indices) cdecl ind_ctor_sort.
Proof.
  split.
  - apply (on_declared_inductive Hdecl).
  - apply (declared_constructor_inv weaken_env_prop_typing wfΣ wfΣ Hdecl).
Defined.

Lemma on_declared_projection `{checker_flags} {Σ ref mdecl idecl cdecl pdecl} {wfΣ : wf Σ}
  (Hdecl : declared_projection Σ ref mdecl idecl cdecl pdecl) :
  on_inductive cumulSpec0 (lift_typing typing) (Σ, ind_universes mdecl) (inductive_mind ref.(proj_ind)) mdecl *
  (idecl.(ind_ctors) = [cdecl]) *
  let oib := declared_inductive_inv weaken_env_prop_typing wfΣ wfΣ (let (x, _) := Hdecl in let (x, _) := x in x) in
  (match oib.(ind_cunivs) with
  | [cs] => sorts_local_ctx (lift_typing typing) (Σ, ind_universes mdecl)
      (arities_context (ind_bodies mdecl) ,,, ind_params mdecl) (cstr_args cdecl) cs
    | _ => False
  end) *
  on_projections mdecl (inductive_mind ref.(proj_ind)) (inductive_ind ref.(proj_ind)) idecl (idecl.(ind_indices)) cdecl *
  (ref.(proj_arg) < context_assumptions cdecl.(cstr_args)) *
  on_projection mdecl (inductive_mind ref.(proj_ind)) (inductive_ind ref.(proj_ind)) cdecl ref.(proj_arg) pdecl.
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
