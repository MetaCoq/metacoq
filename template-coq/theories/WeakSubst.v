(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import config utils Ast AstUtils Induction utils LiftSubst Typing.

(** * Weakening and substitution lemmas for typing derivations.

  *WIP*

  Standard structural lemmas on typing derivations. *)

Set Asymmetric Patterns.

Generalizable Variables Σ Γ t T.

Definition extends (Σ Σ' : global_context) :=
  exists Σ'', Σ' = (Σ'' ++ fst Σ, snd Σ)%list.

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
  forall (H : checker_flags) (Σ : global_context) (Γ : context),
    wf_local Σ Γ ->
    All_local_env
      (fun (Σ0 : global_context) (Γ0 : context) (t T : term) =>
         forall Σ' : global_context, wf Σ' -> extends Σ0 Σ' -> Σ';;; Γ0 |- t : T) Σ Γ ->
    forall Σ' : global_context, wf Σ' -> extends Σ Σ' -> wf_local Σ' Γ.
Proof.
  intros H Σ Γ X X0 Σ' H0.
  induction X; inv X0; try econstructor; auto.
Qed.
Hint Resolve extends_wf_local : extends.

Lemma weakening_env_red1 `{CF:checker_flags} Σ Σ' Γ M N :
  wf Σ' -> extends Σ Σ' ->
  red1 (fst Σ) Γ M N ->
  red1 (fst Σ') Γ M N.
Proof.
  induction 3 using red1_ind_all; try econstructor; eauto.
  eapply extends_lookup in H0; eauto.

  induction H0; constructor; intuition eauto.
  induction H0; constructor; intuition eauto.
  induction H0; constructor; intuition eauto.
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
    consistent_universe_context_instance Σ univs u ->
    forall Σ' : global_context,
      extends Σ Σ' -> consistent_universe_context_instance Σ' univs u.
Proof.
  intros Σ u univs H1 Σ' H2. destruct univs; simpl in *; eauto.
  destruct UContext.dest. destruct H2 as [Σ'' ->]. simpl. auto.
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

Lemma weakening_All_local_env_impl `{checker_flags}
      (P Q : global_context -> context -> term -> term -> Type) Σ Σ' l :
  All_local_env P Σ l ->
  (forall Γ t T, P Σ Γ t T -> Q Σ' Γ t T) ->
  All_local_env Q Σ' l.
Proof.
  induction 1; intros; simpl; econstructor; eauto. Qed.

Lemma weakening_env `{checker_flags} :
  env_prop (fun Σ Γ t T =>
              forall Σ', wf Σ' -> extends Σ Σ' -> Σ' ;;; Γ |- t : T).
Proof.
  apply typing_ind_env; intros; try solve [econstructor; eauto 2 with extends].

  - econstructor; eauto.
    clear H0 H1 X X0. induction X1 in wfΓ |- *; econstructor; eauto.
    eapply weakening_env_cumul in cumul; eauto.
  - econstructor; eauto 2 with extends.
    destruct H6 as [Σ'' ->]. simpl; auto.
    close_Forall. intros; intuition eauto with extends.
  - econstructor; eauto with extends.
    eapply weakening_All_local_env_impl. eapply X.
    clear -X1 H0. simpl; intros. intuition eauto with extends.
    eapply All_impl; eauto; simpl; intuition eauto with extends.
  - econstructor; eauto with extends.
    eapply weakening_All_local_env_impl. eapply X.
    clear -X1 H0. simpl; intros. intuition eauto with extends.
    eapply All_impl; eauto; simpl; intuition eauto with extends.
  - eapply weakening_env_cumul in H0; eauto. econstructor; eauto.
Qed.

Definition lift_decl n k (d : context_decl) := map_decl (lift n k) d.

Definition lift_context n k (Γ : context) : context :=
  List.rev (mapi (fun k' decl => lift_decl n (k + k') decl) (List.rev Γ)).

Lemma lift_decl0 k d : lift_decl 0 k d = d.
Proof.
  destruct d; destruct decl_body; unfold lift_decl, map_decl; simpl;
  f_equal; now rewrite ?lift0_id.
Qed.

Lemma lift0_context k Γ : lift_context 0 k Γ = Γ.
Proof.
  unfold lift_context.
  rewrite rev_mapi. rewrite List.rev_involutive.
  unfold mapi. generalize 0 at 2. generalize #|List.rev Γ|.
  induction Γ; intros; simpl; trivial.
  rewrite lift_decl0; f_equal; auto.
Qed.

Lemma lift_context_length n k Γ : #|lift_context n k Γ| = #|Γ|.
Proof.
  unfold lift_context. now rewrite !List.rev_length, mapi_length, List.rev_length.
Qed.
Hint Rewrite lift_context_length : lift.

Require Import Lia.

Lemma lift_context_snoc0 n k Γ d : lift_context n k (d :: Γ) = lift_context n k Γ ,, lift_decl n (#|Γ| + k) d.
Proof.
  unfold lift_context.
  rewrite !rev_mapi, !rev_involutive. unfold mapi; rewrite mapi_rec_eqn.
  unfold snoc. f_equal. now rewrite Nat.sub_0_r, Nat.add_comm, List.rev_length.
  rewrite mapi_rec_Sk. simpl. apply mapi_rec_ext. intros.
  rewrite app_length, !List.rev_length. simpl. f_equal. lia.
Qed.
Hint Rewrite lift_context_snoc0 : lift.

Lemma lift_context_snoc n k Γ d : lift_context n k (Γ ,, d) = lift_context n k Γ ,, lift_decl n (#|Γ| + k) d.
Proof.
  unfold snoc. apply lift_context_snoc0.
Qed.
Hint Rewrite lift_context_snoc : lift.

Lemma lift_context_alt n k Γ :
  lift_context n k Γ =
  mapi (fun k' d => lift_decl n (pred #|Γ| - k' + k) d) Γ.
Proof.
  unfold lift_context. rewrite rev_mapi. rewrite List.rev_involutive.
  apply mapi_ext. intros. f_equal. now rewrite List.rev_length.
Qed.

Lemma lift_context_app n k Γ Δ :
  lift_context n k (Γ ,,, Δ) = lift_context n k Γ ,,, lift_context n (#|Γ| + k) Δ.
Proof.
  unfold lift_context, app_context.
  rewrite List.rev_app_distr.
  rewrite mapi_app. rewrite <- List.rev_app_distr. f_equal. f_equal.
  apply mapi_ext. intros. f_equal. rewrite List.rev_length. lia.
Qed.

Lemma nth_error_app_ge v Γ Γ' : #|Γ'| <= v -> nth_error (Γ ,,, Γ') v = nth_error Γ (v - #|Γ'|).
Proof.
  revert v; induction Γ'; simpl; intros.
  now rewrite Nat.sub_0_r.
  destruct v. omega.
  simpl. rewrite IHΓ'; easy.
Qed.

Lemma nth_error_app_lt v Γ Γ' : v < #|Γ'| -> nth_error (Γ ,,, Γ') v = nth_error Γ' v.
Proof.
  revert v; induction Γ'; simpl; intros. easy.
  destruct v; trivial.
  simpl. rewrite IHΓ'; easy.
Qed.

Lemma nth_error_lift_context:
  forall (Γ' Γ'' : context) (v : nat),
    v < #|Γ'| -> forall nth k,
    nth_error Γ' v = Some nth ->
    nth_error (lift_context #|Γ''| k Γ') v = Some (lift_decl #|Γ''| (#|Γ'| - S v + k) nth).
Proof.
  induction Γ'; intros.
  - easy.
  - simpl. destruct v; rewrite lift_context_snoc0.
    + simpl. repeat f_equal; try lia. simpl in *. congruence.
    + simpl. apply IHΓ'; simpl in *; (lia || congruence).
Qed.

Lemma weaken_safe_nth_ge Γ Γ' v (isdecl : v < #|Γ ,,, Γ'|) Γ'' : #|Γ'| <= v ->
  { isdecl' : _ &
  safe_nth (Γ ,,, Γ') (exist (fun n0 : nat => n0 < #|Γ ,,, Γ'|) v isdecl) =
  safe_nth (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') (exist _ (#|Γ''| + v) isdecl') }.
Proof.
  simpl.
  assert(#|Γ''| + v < #|Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ'|).
  rewrite !app_context_length in *. autorewrite with lift. omega.
  exists H.
  apply some_inj; rewrite <- !nth_error_safe_nth.
  rewrite nth_error_app_ge; try easy.
  rewrite (nth_error_app_ge (_ + v)); rewrite ?lift_context_length; try easy.
  rewrite nth_error_app_ge; try easy.
Qed.

Lemma weaken_safe_nth_lt Γ Γ' v (isdecl : v < #|Γ ,,, Γ'|) Γ'' : v < #|Γ'| ->
  { isdecl' : _ &
  safe_nth (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') (exist _ v isdecl') =
  lift_decl #|Γ''| (#|Γ'| - S v)
       (safe_nth (Γ ,,, Γ') (exist (fun n0 : nat => n0 < #|Γ ,,, Γ'|) v isdecl)) }.
Proof.
  simpl. intros Hv.
  assert(v < #|Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ'|).
  rewrite !app_context_length in *. autorewrite with lift. omega.
  exists H.
  apply some_inj. rewrite <- !nth_error_safe_nth.
  rewrite nth_error_app_lt. 2:rewrite !app_context_length in H; autorewrite with lift; omega.
  remember (safe_nth (Γ ,,, Γ') (exist _ v isdecl)) as nth.
  apply (f_equal Some) in Heqnth. rewrite <- nth_error_safe_nth in Heqnth.
  rewrite nth_error_app_lt in Heqnth; try easy.
  replace (#|Γ'| - S v) with (#|Γ'| - S v + 0) by lia.
  eapply nth_error_lift_context; try lia. eauto.
Qed.

Lemma closedn_lift n k k' t : closedn k t = true -> closedn (k + n) (lift n k' t) = true.
Proof.
  revert k.
  induction t in n, k' |- * using term_forall_list_ind; intros;
    simpl in *; rewrite ?andb_true_iff in *;
    rewrite ?map_map_compose, ?compose_on_snd, ?compose_map_def;
    try (f_equal; apply_spec);  simpl closed in *;
      try rewrite ?map_length; intuition auto.

  - elim (Nat.leb_spec k' n0); intros. simpl.
    elim (Nat.ltb_spec); auto. apply Nat.ltb_lt in H. lia.
    simpl. elim (Nat.ltb_spec); auto. intros.
    apply Nat.ltb_lt in H. lia.
  - merge_Forall. rewrite forallb_map. eapply Forall_forallb in H0; intuition eauto.
  - specialize (IHt2 n (S k') _ H1). eauto.
  - specialize (IHt2 n (S k') _ H1). eauto.
  - specialize (IHt3 n (S k') _ H1). eauto.
  - merge_Forall. rewrite forallb_map. eapply Forall_forallb in H2; intuition eauto.
  - merge_Forall. rewrite forallb_map. eapply Forall_forallb in H2; intuition eauto.
    destruct x; unfold test_snd, compose, on_snd; simpl. eapply H1. auto.
  - merge_Forall. rewrite forallb_map. eapply Forall_forallb in H0; intuition eauto.
    unfold test_def, compose, map_def in *. simpl.
    rewrite !andb_true_iff in *. intuition auto.
    rewrite Nat.add_assoc. eauto.
  - merge_Forall. rewrite forallb_map. eapply Forall_forallb in H0; intuition eauto.
    unfold test_def, compose, map_def in *. simpl.
    rewrite !andb_true_iff in *. intuition auto.
    rewrite Nat.add_assoc. eauto.
Qed.

Lemma closedn_lift_inv n k k' t : k <= k' ->
                                   closedn (k' + n) (lift n k t) = true ->
                                   closedn k' t = true.
Proof.
  induction t in n, k, k' |- * using term_forall_list_ind; intros;
    simpl in *; rewrite ?andb_true_iff in *;
    rewrite ?map_map_compose, ?compose_on_snd, ?compose_map_def;
    try (f_equal; apply_spec);  simpl closed in *;
      try rewrite ?map_length; intuition eauto 2.

  - revert H0.
    elim (Nat.leb_spec k n0); intros. simpl in *.
    elim (Nat.ltb_spec); auto. apply Nat.ltb_lt in H1. intros. lia.
    revert H1. simpl. elim (Nat.ltb_spec); auto. intros. apply Nat.ltb_lt. lia.
    intros; discriminate.
  - rewrite forallb_map in H1. merge_Forall. eapply Forall_forallb; eauto.
    simpl; intuition eauto.
  - specialize (IHt2 n (S k) (S k')). eauto with arith.
  - specialize (IHt2 n (S k) (S k')). eauto with arith.
  - specialize (IHt3 n (S k) (S k')). eauto with arith.
  - rewrite forallb_map in H3. merge_Forall. eapply Forall_forallb; eauto. simpl; intuition eauto.
  - rewrite forallb_map in H3. merge_Forall. eapply Forall_forallb; eauto. simpl; intuition eauto.
    destruct x; unfold test_snd, compose, on_snd in *; simpl in *; eauto.
  - rewrite forallb_map in H1. merge_Forall. eapply Forall_forallb; intuition eauto.
    unfold test_def, compose, map_def in *. simpl in *.
    rewrite !andb_true_iff in *. rewrite !map_length in *. intuition eauto 2.
    rewrite Nat.add_assoc in H5. specialize (H4 n (#|m| + k) (#|m| + k')). forward H4 by lia.
    apply H4. auto.
  - rewrite forallb_map in H1. merge_Forall. eapply Forall_forallb; intuition eauto.
    unfold test_def, compose, map_def in *. simpl in *.
    rewrite !andb_true_iff in *. rewrite !map_length in *. intuition eauto 2.
    rewrite Nat.add_assoc in H5. specialize (H4 n (#|m| + k) (#|m| + k')). forward H4 by lia.
    apply H4. auto.
Qed.

Lemma closedn_mkApps k f u:
  closedn k f = true -> forallb (closedn k) u = true ->
  closedn k (mkApps f u) = true.
Proof.
  intros Hf Hu.
  induction u; simpl; auto.
  destruct f; simpl in *; try rewrite Hf, Hu; auto.
  rewrite forallb_app. simpl. rewrite Hu.
  rewrite andb_assoc. now rewrite Hf.
Qed.

Lemma closedn_mkApps_inv k f u:
  closedn k (mkApps f u) = true ->
  closedn k f && forallb (closedn k) u = true.
Proof.
  induction u; simpl; auto.
  - now rewrite andb_true_r.
  - intros. destruct f; simpl in *; auto.
    rewrite forallb_app in H. simpl in H.
    now rewrite andb_assoc in H.
Qed.

Lemma closedn_parsubst s k k' t :
  forallb (closedn k) s = true -> closedn (k + k' + #|s|) t = true ->
  closedn (k + k') (parsubst s k' t) = true.
Proof.
  induction t in k' |- * using term_forall_list_ind; intros;
    simpl in *; rewrite ?andb_true_iff in *;
    rewrite ?map_map_compose, ?compose_on_snd, ?compose_map_def;
    try (f_equal; apply_spec);  simpl closed in *;
      try rewrite ?map_length; intuition auto.

  - elim (Nat.leb_spec k' n); intros. simpl.
    apply Nat.ltb_lt in H0.
    destruct nth_error eqn:Heq.
    -- eapply closedn_lift. eapply forallb_Forall in H; eauto. 2:{ intros. apply H2. }
       now eapply nth_error_forall in Heq; simpl; eauto; simpl in *.
    -- simpl. elim (Nat.ltb_spec); auto. intros.
       apply nth_error_None in Heq. lia.
    -- simpl. apply Nat.ltb_lt in H0.
       apply Nat.ltb_lt. lia.

  - merge_Forall. rewrite forallb_map.
    eapply Forall_forallb; eauto. unfold compose; intuition eauto.
  - specialize (IHt2 (S k') H).
    rewrite <- Nat.add_succ_comm in IHt2. eauto.
  - specialize (IHt2 (S k') H).
    rewrite <- Nat.add_succ_comm in IHt2. eauto.
  - specialize (IHt3 (S k') H).
    rewrite <- Nat.add_succ_comm in IHt3. eauto.
  - merge_Forall.
    rewrite closedn_mkApps. eauto.
    now specialize (IHt k' H0).
    rewrite forallb_map. eapply Forall_forallb; eauto. simpl; intuition eauto.
  - merge_Forall. rewrite forallb_map. eapply Forall_forallb; eauto.
    simpl. intros [n trm]. unfold test_snd, on_snd, compose. intuition eauto.
  - merge_Forall. rewrite forallb_map. eapply Forall_forallb; eauto. simpl; intuition eauto.
    unfold test_def, compose, map_def in *. simpl.
    rewrite !andb_true_iff in *. intuition auto.
    rewrite Nat.add_assoc.
    specialize (H4 (#|m| + k')).
    rewrite <- H4; eauto.
    f_equal; lia. rewrite <- H5. f_equal; lia.
  - merge_Forall. rewrite forallb_map. eapply Forall_forallb; eauto. simpl; intuition eauto.
    unfold test_def, compose, map_def in *. simpl.
    rewrite !andb_true_iff in *. intuition auto.
    rewrite Nat.add_assoc.
    specialize (H4 (#|m| + k')).
    rewrite <- H4; eauto.
    f_equal; lia. rewrite <- H5. f_equal; lia.
Qed.

Lemma closedn_substl s k t :
  forallb (closedn k) s = true -> closedn (k + #|s|) t = true ->
  closedn k (substl s t) = true.
Proof.
  unfold substl.
  intros.
  generalize (closedn_parsubst s k 0 t H).
  rewrite Nat.add_0_r. eauto.
Qed.

Lemma closedn_subst_instance_constr k t u :
  closedn k (UnivSubst.subst_instance_constr u t) = closedn k t.
Proof.
  revert k.
  induction t in |- * using term_forall_list_ind; intros;
    simpl in *; rewrite ?andb_true_iff in *;
    rewrite ?map_map_compose, ?compose_on_snd, ?compose_map_def;
    try solve [repeat (f_equal; eauto)];  simpl closed in *;
      try rewrite ?map_length; intuition auto.

  - rewrite forallb_map; eapply Forall_forallb_eq_forallb; eauto.
  - rewrite forallb_map. f_equal; eauto using Forall_forallb_eq_forallb.
  - red in H. rewrite forallb_map. f_equal; eauto using Forall_forallb_eq_forallb.
    f_equal; eauto.
  - red in H. rewrite forallb_map.
    eapply Forall_forallb_eq_forallb; eauto.
    unfold test_def, compose, map_def. simpl.
    do 3 (f_equal; intuition eauto).
  - red in H. rewrite forallb_map.
    eapply Forall_forallb_eq_forallb; eauto.
    unfold test_def, compose, map_def. simpl.
    do 3 (f_equal; intuition eauto).
Qed.

Definition weaken_env_prop `{checker_flags}
           (P : global_context -> context -> option term -> term -> Type) :=
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
  do 2 red in Hdecl. eapply Alli_impl; eauto.
  intros.
  destruct X. constructor.
  unfold on_type in *; eauto.
  unfold on_constructors in *. eapply All_impl; eauto.
  intros [[id t] ar]. unfold on_constructor, on_type in *; eauto.
  destruct decompose_prod_assum. intuition.
  eapply All_impl; eauto. intros [id trm].
  unfold on_projection, on_type; eauto.
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
  destruct Hext. simpl in *. rewrite H0.
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

Lemma declared_minductive_inv `{checker_flags} Σ P ind mdecl :
  weaken_env_prop (lift_typing P) ->
  wf Σ -> Forall_decls_typing P Σ ->
  declared_minductive (fst Σ) ind mdecl ->
  on_inductive (lift_typing P) Σ ind
               (polymorphic_instance (ind_universes mdecl))
               (ind_npars mdecl) (ind_bodies mdecl).
Proof.
  intros.
  eapply weaken_lookup_on_global_env in X1; eauto. apply X1.
Qed.

Lemma declared_inductive_inv `{checker_flags} Σ P ind mdecl idecl :
  weaken_env_prop (lift_typing P) ->
  wf Σ -> Forall_decls_typing P Σ ->
  declared_inductive (fst Σ) ind mdecl idecl ->
  on_ind_body (lift_typing P) Σ (inductive_mind ind)
               (polymorphic_instance (ind_universes mdecl))
               (ind_npars mdecl) (arities_context (ind_bodies mdecl)) (inductive_ind ind) idecl.
Proof.
  intros.
  destruct H0 as [Hmdecl Hidecl].
  eapply declared_minductive_inv in Hmdecl; eauto.
  eapply nth_error_alli in Hidecl; eauto.
  apply Hidecl.
Qed.

Lemma typecheck_closed `{cf : checker_flags} :
  env_prop (fun Σ Γ t T =>
              closedn #|Γ| t && closedn #|Γ| T = true).
Proof.
  assert(weaken_env_prop (lift_typing (fun (_ : global_context) (Γ : context) (t T : term) =>
                                         closedn #|Γ| t && closedn #|Γ| T = true))).
  { repeat red. intros. destruct t; red in X0; eauto. }

  apply typing_ind_env; intros; simpl; rewrite ?andb_true_iff in *; try solve [intuition auto].
  - elim (Nat.ltb_spec n #|Γ|); intuition.
    eapply (All_local_env_lookup isdecl) in H. red in H.
    destruct decl_body.
    -- rewrite andb_true_iff in H; intuition.
       rewrite skipn_length in H2 by lia.
       eapply (closedn_lift (S n)) in H2.
       assert(#|Γ| - S n + S n = #|Γ|) by lia.
       rewrite H in H2. apply H2.
    -- destruct H as [s Hs].
       rewrite andb_true_iff in Hs; intuition.
       rewrite skipn_length in H by lia.
       eapply (closedn_lift (S n)) in H.
       assert(#|Γ| - S n + S n = #|Γ|) by lia.
       rewrite H2 in H. apply H.

  - destruct H. rewrite and_assoc. split. auto.
    clear X0 H H0 H1.
    induction X1; simpl. intuition auto.
    rewrite andb_true_iff in *. destruct p0. rewrite H.
    rewrite <- andb_true_iff. simpl.
    apply IHX1. unfold subst.
    pose proof (closedn_parsubst [hd] #|Γ| 0). rewrite Nat.add_0_r in H1.
    apply H1. simpl. now rewrite H.
    simpl. simpl in p. rewrite andb_true_iff in p. intuition auto.
    rewrite Nat.add_1_r. auto.

  - rewrite closedn_subst_instance_constr.
    eapply lookup_on_global_env in H; eauto.
    destruct H as [Σ' [HΣ' IH]].
    repeat red in IH. destruct decl, cst_body. simpl in *.
    rewrite andb_true_iff in IH. intuition.
    eauto using closed_upwards with arith.
    simpl in *.
    repeat red in IH. destruct IH as [s Hs].
    rewrite andb_true_iff in Hs. intuition.
    eauto using closed_upwards with arith.

  - rewrite closedn_subst_instance_constr.
    eapply declared_inductive_inv in X0; eauto.
    apply onArity in X0. repeat red in X0.
    destruct X0 as [s Hs]. rewrite andb_true_iff in Hs.
    intuition eauto using closed_upwards with arith.

  - destruct isdecl as [Hidecl Hcdecl].
    eapply declared_inductive_inv in X0; eauto.
    apply onConstructors in X0. repeat red in X0.
    eapply nth_error_all in Hcdecl; eauto.
    repeat red in Hcdecl.
    destruct Hcdecl as [s Hs]. rewrite andb_true_iff in Hs.
    destruct Hs as [Hdecl _].
    unfold type_of_constructor.
    apply closedn_substl.
    unfold inds. clear. simpl. induction #|ind_bodies mdecl|. constructor.
    simpl. now rewrite IHn.
    rewrite inds_length. unfold arities_context in Hdecl.
    rewrite rev_map_length in Hdecl.
    rewrite closedn_subst_instance_constr.
    eauto using closed_upwards with arith.

  - intuition auto.
    eapply Forall_forallb; eauto.
    eapply Forall2_Forall_left; eauto.
    simpl; intros. destruct X4. rewrite andb_true_iff in e. destruct e.
    apply H7. simpl; intros. eauto.
    apply closedn_mkApps; auto.
    rewrite forallb_app. simpl. rewrite H6.
    rewrite forallb_skipn; auto.
    now apply closedn_mkApps_inv in H11.

  - intuition. subst ty.
    apply closedn_substl.
    simpl. apply closedn_mkApps_inv in H2.
    rewrite forallb_rev, H1. apply H2.
    rewrite closedn_subst_instance_constr.
    destruct isdecl as [isdecl Hpdecl].
    eapply declared_inductive_inv in isdecl; eauto.
    apply onProjections in isdecl.
    destruct decompose_prod_assum eqn:Heq.
    destruct isdecl as [Hc isdecl].
    eapply nth_error_all in isdecl; eauto.
    destruct isdecl as [s Hs]. simpl in *.
    forward Hc. intro. rewrite H in Hpdecl; destruct (snd p); discriminate.
    rewrite <- Hc in H0. rewrite <- H0 in Hs.
    rewrite andb_true_r in Hs. rewrite List.rev_length.
    eauto using closed_upwards with arith.

  - split. eapply All_forallb; eauto.
    simpl; eauto. intros. intuition.
    destruct x; simpl in *.
    unfold test_def. simpl.
    rewrite andb_true_iff in *. destruct b.
    split.
    rewrite app_context_length in *. rewrite Nat.add_comm in *.
    eapply closedn_lift_inv in H0; eauto. lia.
    subst types.
    now rewrite app_context_length, fix_context_length in H.
    subst ty.
    eapply (All_safe_nth isdecl) in X1. simpl in X1.
    intuition.
    rewrite !andb_true_iff in b. intuition.
    subst types. rewrite app_context_length in H0.
    rewrite Nat.add_comm in H0.
    now eapply closedn_lift_inv in H0.

  - split. eapply All_forallb; eauto.
    simpl; eauto. intros. intuition.
    destruct x; simpl in *.
    unfold test_def. simpl.
    rewrite andb_true_iff in *. destruct b.
    split.
    rewrite app_context_length in *. rewrite Nat.add_comm in *.
    eapply closedn_lift_inv in H0; eauto. lia.
    subst types.
    now rewrite app_context_length, fix_context_length in H.
    subst ty.
    eapply (All_safe_nth isdecl) in X1. simpl in X1.
    intuition.
    rewrite !andb_true_iff in b. intuition.
    subst types. rewrite app_context_length in H0.
    rewrite Nat.add_comm in H0.
    now eapply closedn_lift_inv in H0.
Qed.

Lemma lift_simpl (Γ'' Γ' : context) i t : i < #|Γ'| ->
  lift0 (S i) (lift #|Γ''| (#|Γ'| - S i) t) = lift #|Γ''| #|Γ'| (lift0 (S i) t).
Proof.
  intros. assert (#|Γ'| = S i + (#|Γ'| - S i)) by easy.
  rewrite H0 at 2.
  rewrite <- permute_lift; try easy.
Qed.

Lemma lift_iota_red n k pars c args brs :
  lift n k (iota_red pars c args brs) =
  iota_red pars c (List.map (lift n k) args) (List.map (on_snd (lift n k)) brs).
Proof.
  unfold iota_red. rewrite !lift_mkApps. f_equal; auto using map_skipn.
  rewrite nth_map; simpl; auto.
Qed.

Definition lift_subst n k s :=
  List.fold_right (fun t l => lift n (List.length l + k) t :: l) [] s.

Lemma lift_subst_length n k s : #|lift_subst n k s| = #|s|.
Proof.
  induction s in n, k |- *; simpl; auto.
Qed.

Lemma fix_subst_length mfix : #|fix_subst mfix| = #|mfix|.
Proof.
  unfold fix_subst. generalize (tFix mfix). intros.
  induction mfix; simpl; auto.
Qed.

Lemma cofix_subst_length mfix : #|cofix_subst mfix| = #|mfix|.
Proof.
  unfold cofix_subst. generalize (tCoFix mfix). intros.
  induction mfix; simpl; auto.
Qed.

Require Import Compare_dec Lia.

Lemma parsubst_empty k a : Ast.wf a -> parsubst [] k a = a.
Proof.
  induction 1 in k |- * using term_wf_forall_list_ind; simpl; try congruence;
    try solve [f_equal; eauto; apply_spec; eauto].

  - elim (Nat.compare_spec k n); destruct (Nat.leb_spec k n); intros; try easy.
    subst. rewrite Nat.sub_diag. simpl. rewrite Nat.sub_0_r. reflexivity.
    assert (n - k > 0) by lia.
    assert (exists n', n - k = S n'). exists (pred (n - k)). lia.
    destruct H2. rewrite H2. simpl. now rewrite Nat.sub_0_r.
  - rewrite IHwf. rewrite mkApps_tApp; eauto with wf.
    f_equal; apply_spec. auto.
  - rewrite IHwf, IHwf0. f_equal. red in H. apply_spec. intros; eauto.
    destruct x; unfold on_snd; simpl in *; congruence.
  - f_equal. clear H0. red in H; apply_spec. intuition auto.
    destruct x; unfold map_def; simpl in *; congruence.
  - f_equal. red in H; apply_spec. intuition auto.
    destruct x; unfold map_def; simpl in *; congruence.
Qed.

Lemma lift_unfold_fix n k mfix idx narg fn :
  unfold_fix mfix idx = Some (narg, fn) ->
  unfold_fix (map (map_def (lift n k) (lift n (#|mfix| + k))) mfix) idx = Some (narg, lift n k fn).
Proof.
  unfold unfold_fix.
  rewrite nth_error_map. destruct (nth_error mfix idx) eqn:Hdef; try congruence.
  intros [= <- <-]. simpl. repeat f_equal. unfold substl.
  rewrite (distr_lift_subst_rec _ _ n 0 k).
  rewrite fix_subst_length. f_equal.
  unfold fix_subst. rewrite !map_length.
  generalize #|mfix| at 2 3. induction n0; auto. simpl.
  f_equal. apply IHn0.
Qed.
Hint Resolve lift_unfold_fix.

Lemma lift_unfold_cofix n k mfix idx narg fn :
  unfold_cofix mfix idx = Some (narg, fn) ->
  unfold_cofix (map (map_def (lift n k) (lift n (#|mfix| + k))) mfix) idx = Some (narg, lift n k fn).
Proof.
  unfold unfold_cofix.
  rewrite nth_error_map. destruct (nth_error mfix idx) eqn:Hdef; try congruence.
  intros [= <- <-]. simpl. repeat f_equal. unfold substl.
  rewrite (distr_lift_subst_rec _ _ n 0 k).
  rewrite cofix_subst_length. f_equal.
  unfold cofix_subst. rewrite !map_length.
  generalize #|mfix| at 2 3. induction n0; auto. simpl.
  f_equal. apply IHn0.
Qed.
Hint Resolve lift_unfold_cofix.

Lemma lift_is_constructor:
  forall (args : list term) (narg : nat) n k,
    is_constructor narg args = true -> is_constructor narg (map (lift n k) args) = true.
Proof.
  intros args narg.
  unfold is_constructor; intros.
  rewrite nth_error_map. destruct nth_error; try discriminate. simpl. intros.
  destruct t; try discriminate || reflexivity.
  destruct t; try discriminate || reflexivity.
Qed.
Hint Resolve lift_is_constructor.

Hint Rewrite UnivSubst.lift_subst_instance_constr : lift.
Hint Rewrite lift_mkApps : lift.
Hint Rewrite distr_lift_subst : lift.
Hint Rewrite lift_iota_red : lift.

Definition map_constant_body f decl :=
  {| cst_type := f decl.(cst_type);
     cst_body := option_map f decl.(cst_body);
     cst_universes := decl.(cst_universes) |}.

Lemma map_cst_type f decl : f (cst_type decl) = cst_type (map_constant_body f decl).
Proof. destruct decl; reflexivity. Qed.

Lemma map_cst_body f decl : option_map f (cst_body decl) = cst_body (map_constant_body f decl).
Proof. destruct decl; reflexivity. Qed.

Lemma map_dtype {A B : Set} (f : A -> B) (g : A -> B) (d : def A) :
  f (dtype d) = dtype (map_def f g d).
Proof. destruct d; reflexivity. Qed.

Lemma map_dbody {A B : Set} (f : A -> B) (g : A -> B) (d : def A) :
  g (dbody d) = dbody (map_def f g d).
Proof. destruct d; reflexivity. Qed.

Lemma lift_declared_constant `{checker_flags} Σ cst decl n k :
  wf Σ ->
  declared_constant (fst Σ) cst decl ->
  decl = map_constant_body (lift n k) decl.
Proof.
  unfold declared_constant.
  intros.
  eapply lookup_on_global_env in H0; eauto.
  destruct H0 as [Σ' [wfΣ' decl']].
  red in decl'. red in decl'.
  destruct decl. simpl in *. destruct cst_body. unfold map_constant_body. simpl.
  pose proof decl' as declty.
  apply typecheck_closed in declty; eauto.
  destruct declty as [declty Hcl].
  rewrite andb_true_iff in Hcl. destruct Hcl as [clb clty].
  pose proof (closed_upwards _ _ clb k).
  pose proof (closed_upwards _ _ clty k).
  simpl in *. forward H0 by lia. forward H1 by lia.
  apply (lift_closed n k) in H0.
  apply (lift_closed n k) in H1. rewrite H0, H1. reflexivity.
  constructor.
  red in decl'.
  destruct decl'.
  apply typecheck_closed in t. destruct t as [_ ccst].
  rewrite andb_true_iff in ccst. destruct ccst as [ccst _].
  eapply closed_upwards in ccst; simpl.
  apply (lift_closed n k) in ccst. unfold map_constant_body. simpl.
  rewrite ccst. reflexivity. lia. auto. constructor.
Qed.

Definition map_one_inductive_body mind u arities f n m :=
  match m with
  | Build_one_inductive_body ind_name ind_type ind_kelim ind_ctors ind_projs =>
    let '(ctx, _) := decompose_prod_assum [] (f [] ind_type) in
    let indty := mkApps (tInd (mkInd mind n) u) (to_extended_list ctx) in
    Build_one_inductive_body ind_name
                             (f [] ind_type)
                             ind_kelim
                             (map (on_pi2 (f arities)) ind_ctors)
                             (map (on_snd (f (ctx ,, vass (nNamed ind_name) indty))) ind_projs)
  end.

Definition map_mutual_inductive_body mind f m :=
  match m with
  | Build_mutual_inductive_body ind_npars ind_bodies ind_universes =>
    let arities := arities_context ind_bodies in
    let u := polymorphic_instance ind_universes in
    Build_mutual_inductive_body
      ind_npars
      (mapi (map_one_inductive_body mind u arities f) ind_bodies)
      ind_universes
  end.

Lemma ind_type_map f arities mind u n oib :
  ind_type (map_one_inductive_body mind u arities f n oib) = f [] (ind_type oib).
Proof. destruct oib. simpl. destruct decompose_prod_assum. reflexivity. Qed.

Lemma ind_ctors_map f arities mind u n oib :
  ind_ctors (map_one_inductive_body mind u arities f n oib) =
  map (on_pi2 (f arities)) (ind_ctors oib).
Proof. destruct oib; simpl; destruct decompose_prod_assum; reflexivity. Qed.

Lemma ind_projs_map f mind u arities n oib :
  ind_projs (map_one_inductive_body mind u arities f n oib) =
  let '(ctx, _) := decompose_prod_assum [] (f [] oib.(ind_type)) in
  map (on_snd (f (ctx ,, vass (nNamed oib.(ind_name))
      (mkApps (tInd (mkInd mind n) u) (to_extended_list ctx))))) (ind_projs oib).
Proof. destruct oib; simpl. destruct decompose_prod_assum. simpl. reflexivity. Qed.

Definition lift_mutual_inductive_body n k mind m :=
  map_mutual_inductive_body mind (fun Γ => lift n (#|Γ| + k)) m.

Lemma typed_liftn `{checker_flags} Σ Γ t T n k :
  wf Σ -> wf_local Σ Γ -> k >= #|Γ| ->
  Σ ;;; Γ |- t : T -> lift n k t = t.
Proof.
  intros wfΣ wfΓ Hk Hty.
  apply typecheck_closed in Hty; eauto.
  destruct Hty as [_ Hcl].
  rewrite andb_true_iff in Hcl. destruct Hcl as [clb clty].
  pose proof (closed_upwards _ _ clb k).
  simpl in *. forward H0 by lia.
  now apply (lift_closed n) in H0.
Qed.

Lemma lift_declared_minductive `{checker_flags} Σ cst decl n k :
  wf Σ ->
  declared_minductive (fst Σ) cst decl ->
  lift_mutual_inductive_body n k cst decl = decl.
Proof.
  unfold declared_minductive.
  intros.
  eapply lookup_on_global_env in H0; eauto.
  destruct H0 as [Σ' [wfΣ' decl']].
  do 2 red in decl'.
  destruct decl. simpl in *. f_equal.
  revert decl'. generalize ind_bodies at 2 4 5.
  intros.
  eapply Alli_map_id in decl'. eauto.
  clear decl'. intros.
  destruct x; simpl in *.
  destruct (decompose_prod_assum [] ind_type) eqn:Heq.
  destruct (decompose_prod_assum [] (lift n k ind_type)) eqn:Heq'.
  destruct X0. simpl in *.
  assert (lift n k ind_type = ind_type).
  destruct onArity as [s Hs].
  eapply typed_liftn; eauto. constructor. simpl; lia.
  rewrite H0 in Heq'. rewrite Heq in Heq'. revert Heq'; intros [= <- <-].
  f_equal; auto.
  apply (All_map_id onConstructors).
  intros [[x p] n']. intros [s Hty].
  unfold on_pi2; f_equal; f_equal. eapply typed_liftn. 4:eapply Hty. wf. wf. lia.
  rewrite Heq in onProjections. destruct onProjections as [_ onProjections].
  apply (All_map_id onProjections).
  intros [x p]. intros [s Hty].
  unfold on_snd; f_equal; f_equal.
  eapply typed_liftn. 4:eapply Hty. wf. wf. simpl. lia.
Qed.

Lemma lift_declared_inductive `{checker_flags} Σ ind mdecl idecl n k :
  wf Σ ->
  declared_inductive (fst Σ) ind mdecl idecl ->
  map_one_inductive_body (inductive_mind ind) (polymorphic_instance (mdecl.(ind_universes))) (arities_context mdecl.(ind_bodies)) (fun Γ => lift n (#|Γ| + k)) (inductive_ind ind) idecl = idecl.
Proof.
  unfold declared_inductive. intros wfΣ [Hmdecl Hidecl].
  destruct Σ. eapply (lift_declared_minductive _ _ _ n k) in Hmdecl.
  unfold lift_mutual_inductive_body in Hmdecl.
  destruct mdecl. simpl in *.
  injection Hmdecl. intros Heq.
  clear Hmdecl.
  pose proof Hidecl as Hidecl'.
  rewrite <- Heq in Hidecl'.
  rewrite nth_error_mapi in Hidecl'.
  clear Heq.
  unfold option_map in Hidecl'. rewrite Hidecl in Hidecl'.
  congruence. auto.
Qed.

Lemma substl_inds_lift ind u mdecl n k t :
  (substl (inds (inductive_mind ind) u (ind_bodies mdecl))
          (lift n (#|arities_context (ind_bodies mdecl)| + k) t)) =
  lift n k (substl (inds (inductive_mind ind) u (ind_bodies mdecl)) t).
Proof.
  unfold substl.
  rewrite (distr_lift_subst_rec _ _ n 0 k). simpl.
  unfold arities_context. rewrite rev_map_length, inds_length.
  f_equal. generalize (ind_bodies mdecl).
  clear. intros.
  induction l; unfold inds; simpl; auto. f_equal. auto.
Qed.

Lemma lift_declared_constructor `{checker_flags} Σ c u mdecl idecl cdecl n k :
  wf Σ ->
  declared_constructor (fst Σ) mdecl idecl c cdecl ->
  lift n k (type_of_constructor mdecl cdecl c u) = (type_of_constructor mdecl cdecl c u).
Proof.
  unfold declared_constructor. destruct c as [i ci]. intros wfΣ [Hidecl Hcdecl].
  destruct Σ. eapply (lift_declared_inductive _ _ _ _ n k) in Hidecl; eauto.
  unfold type_of_constructor. destruct cdecl as [[id t'] arity].
  destruct idecl; simpl in *.
  destruct (decompose_prod_assum [] _) eqn:Heq.
  injection Hidecl.
  intros.
  pose Hcdecl as Hcdecl'.
  rewrite <- H1 in Hcdecl'.
  rewrite nth_error_map in Hcdecl'. rewrite Hcdecl in Hcdecl'.
  simpl in Hcdecl'. injection Hcdecl'.
  intros.
  rewrite <- H3 at 2.
  rewrite <- UnivSubst.lift_subst_instance_constr.
  now rewrite substl_inds_lift.
Qed.

Lemma lift_fix_context:
  forall (mfix : list (def term)) (n k : nat),
    fix_context (map (map_def (lift n k) (lift n (#|mfix| + k))) mfix) = lift_context n k (fix_context mfix).
Proof.
  intros mfix n k. unfold fix_context.
  rewrite map_vass_map_def, rev_mapi.
  fold (fix_context mfix).
  rewrite (lift_context_alt n k (fix_context mfix)).
  unfold lift_decl. now rewrite mapi_length, fix_context_length.
Qed.

Lemma All_local_env_lift `{checker_flags} (P Q : global_context -> context -> term -> term -> Type) Σ c n k :
  All_local_env Q Σ c ->
  (forall Γ t T,
      Q Σ Γ t T -> P Σ (lift_context n k Γ) (lift n (#|Γ| + k) t) (lift n (#|Γ| + k) T)) ->
  All_local_env P Σ (lift_context n k c).
Proof.
  intros Hq Hf. induction Hq in |- *; try econstructor; eauto;
                  simpl; rewrite lift_context_snoc; econstructor; eauto.
  simpl. eapply (Hf _ _ (tSort u)). eauto.
Qed.

Lemma lift_destArity ctx t n k : Ast.wf t ->
        destArity (lift_context n k ctx) (lift n (#|ctx| + k) t) =
        match destArity ctx t with
        | Some (args, s) => Some (lift_context n k args, s)
        | None => None
        end.
Proof.
  intros wf; revert ctx.
  induction wf in n, k |- * using Template.Induction.term_wf_forall_list_ind; intros ctx; simpl; trivial.
  destruct Nat.leb; reflexivity.

  specialize (IHwf0 n k (ctx,, vass n0 t)). rewrite lift_context_snoc in IHwf0.
  simpl in IHwf0. unfold lift_decl, map_decl in IHwf0. unfold vass. simpl in IHwf0. rewrite IHwf0.
  reflexivity.
  specialize (IHwf1 n k (ctx,, vdef n0 t t0)). rewrite lift_context_snoc in IHwf1.
  unfold vdef, lift_decl, map_decl in *. simpl in *. rewrite IHwf1. reflexivity.
Qed.

Lemma lift_instantiate_params n k args t :
  lift n k (instantiate_params args t) =
  instantiate_params (map (lift n k) args) (lift n k t).
Proof.
  induction args in t, n, k |- *. reflexivity.
  simpl. destruct t; simpl; try congruence.
  - now destruct (Nat.leb k n0).
  - rewrite <- distr_lift_subst. eauto.
  - rewrite <- distr_lift_subst. eauto.
Qed.

(* bug eauto with let .. in hypothesis failing *)
Lemma lift_decompose_prod_assum_rec ctx t n k :
  let (ctx', t') := decompose_prod_assum ctx t in
  (lift_context n k ctx', lift n (length ctx' + k) t') =
  decompose_prod_assum (lift_context n k ctx) (lift n (length ctx + k) t).
Proof.
  induction t in n, k, ctx |- *; simpl;
    try rewrite Nat.sub_diag, Nat.add_0_r; try (eauto; congruence).
  - now destruct (Nat.leb (#|ctx| + k) n0).
  - eapply IHt1.
  - specialize (IHt2 (ctx ,, vass n0 t1) n k).
    destruct decompose_prod_assum. rewrite IHt2. simpl.
    rewrite lift_context_snoc. reflexivity.
  - specialize (IHt3 (ctx ,, vdef n0 t1 t2) n k).
    destruct decompose_prod_assum. rewrite IHt3. simpl.
    rewrite lift_context_snoc. reflexivity.
Qed.

Lemma lift_decompose_prod_assum t n k :
  let (ctx', t') := decompose_prod_assum [] t in
  (lift_context n k ctx', lift n (length ctx' + k) t') =
  decompose_prod_assum [] (lift n k t).
Proof. apply lift_decompose_prod_assum_rec. Qed.

Lemma decompose_app_lift n k t f a :
  decompose_app t = (f, a) -> decompose_app (lift n k t) = (lift n k f, map (lift n k) a).
Proof. destruct t; simpl; intros [= <- <-]; try reflexivity.
       simpl. now destruct (Nat.leb k n0). Qed.

Lemma lift_it_mkProd_or_LetIn n k ctx t :
  lift n k (it_mkProd_or_LetIn ctx t) =
  it_mkProd_or_LetIn (lift_context n k ctx) (lift n (length ctx + k) t).
Proof.
  induction ctx in n, k, t |- *; simpl; try congruence.
  pose (lift_context_snoc n k ctx a). unfold snoc in e. rewrite e. clear e.
  simpl. destruct decl_body. now rewrite IHctx.
  pose (lift_context_snoc n k ctx a). simpl. now rewrite IHctx.
Qed.

Lemma to_extended_list_lift n k c :
  to_extended_list (lift_context n k c) = to_extended_list c.
Proof.
  unfold to_extended_list. generalize 0 at 3 6. generalize (@nil term) at 1 2.
  induction c in n, k |- *; simpl; intros. reflexivity.
  rewrite lift_context_snoc0. unfold snoc. simpl.
  destruct a. destruct decl_body. unfold lift_decl, map_decl. simpl.
  now rewrite IHc. simpl. apply IHc.
Qed.

Fixpoint reln (l : list term) (p : nat) (Γ0 : list context_decl) {struct Γ0} : list term :=
  match Γ0 with
  | [] => l
  | {| decl_body := Some _ |} :: hyps => reln l (p + 1) hyps
  | {| decl_body := None |} :: hyps => reln (tRel p :: l) (p + 1) hyps
  end.

Lemma reln_list_lift_above l p Γ :
  Forall (fun x => exists n, x = tRel n /\ n < p + length Γ) l ->
  Forall (fun x => exists n, x = tRel n /\ n < p + length Γ) (reln l p Γ).
Proof.
  induction Γ in p, l |- *. simpl. auto.
  intros. destruct a. destruct decl_body. simpl.
  specialize (IHΓ l (S p)). rewrite <- Nat.add_succ_comm, Nat.add_1_r.
  eapply IHΓ. simpl in *. rewrite <- Nat.add_succ_comm in H. auto.
  simpl in *.
  specialize (IHΓ (tRel p :: l) (S p)). rewrite <- Nat.add_succ_comm, Nat.add_1_r.
  eapply IHΓ. simpl in *. rewrite <- Nat.add_succ_comm in H. auto.
  simpl in *.
  constructor. exists p. intuition lia. auto.
Qed.

Lemma to_extended_list_lift_above Γ :
  Forall (fun x => exists n, x = tRel n /\ n < length Γ) (to_extended_list Γ).
Proof.
  pose (reln_list_lift_above [] 0 Γ).
  unfold to_extended_list.
  forward f. constructor. apply f.
Qed.

Lemma to_extended_list_map_lift:
  forall (n k : nat) (c : context), to_extended_list c = map (lift n (#|c| + k)) (to_extended_list c).
Proof.
  intros n k c.
  pose proof (to_extended_list_lift_above c).
  symmetry. apply_spec. intros.
  destruct H0. intuition. subst x. simpl.
  destruct (leb_spec_Set (#|c| + k) x0). f_equal. lia. reflexivity.
Qed.

Lemma lift_types_of_case ind mdecl idecl args u p pty indctx pctx ps btys n k :
  let f ctx := lift n (#|ctx| + k) in
  let f_ctx := lift_context n k in
  Ast.wf pty -> Ast.wf (ind_type idecl) ->
  types_of_case ind mdecl idecl args u p pty = Some (indctx, pctx, ps, btys) ->
  types_of_case ind mdecl (map_one_inductive_body (inductive_mind ind) (polymorphic_instance mdecl.(ind_universes))
                                                  (arities_context mdecl.(ind_bodies)) f (inductive_ind ind) idecl)
                (map (f []) args) u (f [] p) (f [] pty) =
  Some (f_ctx indctx, f_ctx pctx, ps, map (on_snd (f [])) btys).
Proof.
  simpl. intros wfpty wfdecl. simpl.
  unfold types_of_case. simpl.
  pose proof (lift_destArity [] (ind_type idecl) n k wfdecl); trivial. simpl in H.
  unfold lift_context in H. simpl in H. rewrite ind_type_map. simpl. rewrite H. clear H.
  destruct destArity as [[ctx s] | ]; try congruence.
  pose proof (lift_destArity [] pty n k wfpty); trivial. simpl in H.
  unfold lift_context in H. simpl in H. rewrite H. clear H.
  destruct destArity as [[ctx' s'] | ]; try congruence.
  intros [= -> -> -> <-].
  f_equal. f_equal.
  unfold build_branches_type. simpl.
  rewrite ind_ctors_map.
  rewrite mapi_map, map_mapi. f_equal. extensionality i. extensionality x.
  destruct x as [[id t] arity]. simpl.
  rewrite <- UnivSubst.lift_subst_instance_constr.
  rewrite substl_inds_lift.
  rewrite <- lift_instantiate_params.
  remember (instantiate_params _ _) as instparams.
  epose proof (lift_decompose_prod_assum instparams n k).
  destruct (decompose_prod_assum [] instparams).
  rewrite <- H.
  destruct (decompose_app t0) as [fn arg] eqn:?.
  rewrite (decompose_app_lift _ _ _ fn arg); auto. simpl.
  destruct (chop _ arg) eqn:Heqchop. eapply chop_map in Heqchop.
  rewrite Heqchop. clear Heqchop.
  unfold on_snd. simpl. f_equal.
  rewrite lift_it_mkProd_or_LetIn, !lift_mkApps, map_app; simpl.
  rewrite !lift_mkApps, !map_app, lift_context_length.
  rewrite permute_lift by lia. repeat f_equal.
  now rewrite to_extended_list_lift, <- to_extended_list_map_lift.
Qed.

Lemma weakening_red1 `{CF:checker_flags} Σ Γ Γ' Γ'' M N :
  wf Σ ->
  red1 (fst Σ) (Γ ,,, Γ') M N ->
  red1 (fst Σ) (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') (lift #|Γ''| #|Γ'| M) (lift #|Γ''| #|Γ'| N).
Proof.
  intros wfΣ H.
  remember (Γ ,,, Γ') as Γ0. revert Γ Γ' Γ'' HeqΓ0.
  induction H using red1_ind_all in |- *; intros Γ0 Γ' Γ'' HeqΓ0; try subst Γ; simpl;
    autorewrite with lift;
    try solve [  econstructor; eauto ].

  - elim (leb_spec_Set); intros Hn.
    + rewrite simpl_lift; try lia. rewrite Nat.add_succ_r.
      destruct (weaken_safe_nth_ge _ _ _ isdecl Γ'' Hn) as [isdecl' Heq].
      rewrite Heq in H.
      unshelve econstructor; eauto.
    + destruct (weaken_safe_nth_lt _ _ _ isdecl Γ'' Hn) as [isdecl' Heq].
      rewrite <- lift_simpl by easy.
      econstructor.
      apply (f_equal decl_body) in Heq.
      rewrite Heq. unfold lift_decl. simpl. now rewrite H.

  - econstructor.
    eauto. rewrite H0. f_equal.
    eapply (lookup_on_global_env _ _ _ _ wfΣ) in H.
    destruct H as [Σ' [wfΣ' decl']].
    red in decl'. red in decl'.
    rewrite H0 in decl'.
    apply typecheck_closed in decl'; eauto. destruct decl'.
    rewrite andb_true_iff in e. destruct e as [Hclosed _].
    simpl in Hclosed.
    pose proof (closed_upwards _ _ Hclosed #|Γ'|).
    forward H by lia.
    apply (lift_closed #|Γ''| #|Γ'|) in H. auto.
    constructor.

  - simpl. rewrite <- nth_map by reflexivity.
    constructor.

  - constructor.
    specialize (IHred1 Γ0 (Γ' ,, vass na N) Γ'' eq_refl).
    rewrite lift_context_snoc, Nat.add_0_r in IHred1. apply IHred1.

  - constructor.
    specialize (IHred1 Γ0 (Γ' ,, vdef na b t) Γ'' eq_refl).
    rewrite lift_context_snoc, Nat.add_0_r in IHred1. apply IHred1.

  - constructor.
    induction H; constructor; auto.
    intuition; eauto.

  - constructor.
    induction H; constructor; auto.
    intuition; eauto.

  - constructor.
    specialize (IHred1 Γ0 (Γ' ,, vass na M1) Γ'' eq_refl).
    rewrite lift_context_snoc, Nat.add_0_r in IHred1. apply IHred1.

  - constructor.
    induction H; constructor; auto.
    intuition; eauto.
Qed.

Lemma lift_eq_term `{checker_flags} ϕ n k T U :
  eq_term ϕ T U = true ->
  eq_term ϕ (lift n k T) (lift n k U) = true.
Proof.
  intros Hleq.
  induction T in n, k, U, Hleq |- * using term_forall_list_ind; intros;
    destruct U; try discriminate;
  try solve [simpl; auto]; try
                             (destruct (mkApps_trans_wf _ _ H0) as [U' [V' ->]]; reflexivity);
  simpl in *; revert Hleq; try rewrite !andb_true_iff in *; intuition auto;
    try (merge_Forall; close_Forall; intuition auto).

  - intros. apply Nat.eqb_eq in Hleq. subst.
    destruct Nat.leb; simpl. apply Nat.eqb_eq. reflexivity. apply Nat.eqb_refl.
  - destruct p. destruct Nat.leb. discriminate. discriminate.
  - destruct p, p0. rewrite !andb_true_iff in *. intuition auto.
    red in H0. merge_Forall. close_Forall. intuition auto. destruct y. simpl. auto.
  - rewrite !andb_true_iff in *.
    destruct x, y; simpl in *; intuition auto.
    assert (#|m| = #|m0|). clear -H2. induction H2; simpl; auto. rewrite H4. auto.
  - rewrite !andb_true_iff in *.
    destruct x, y; simpl in *; intuition auto.
    assert (#|m| = #|m0|). clear -H2. induction H2; simpl; auto. rewrite H4. auto.
Qed.

Lemma lift_leq_term `{checker_flags} ϕ n k T U :
  leq_term ϕ T U = true ->
  leq_term ϕ (lift n k T) (lift n k U) = true.
Proof.
  intros Hleq.
  induction T in n, k, U, Hleq |- * using term_forall_list_ind; intros;
    destruct U; try discriminate;
  try solve [simpl; auto]; try
                             (destruct (mkApps_trans_wf _ _ H0) as [U' [V' ->]]; reflexivity);
  simpl in *; revert Hleq; try destruct p, p0; try rewrite !andb_true_iff in *;
    intuition auto using lift_eq_term;
    try (merge_Forall; close_Forall; intuition eauto using lift_eq_term).

  - intros. apply Nat.eqb_eq in Hleq. subst.
    destruct Nat.leb; simpl. apply Nat.eqb_eq. reflexivity. apply Nat.eqb_refl.
  - destruct p. destruct (Nat.leb k n0); discriminate.
  - destruct y. simpl. auto using lift_eq_term.
  - rewrite !andb_true_iff in *.
    destruct x, y; simpl in *; intuition auto using lift_eq_term.
    assert (#|m| = #|m0|). clear -H2. induction H2; simpl; auto. rewrite H4.
    auto using lift_eq_term.
  - rewrite !andb_true_iff in *.
    destruct x, y; simpl in *; intuition auto using lift_eq_term.
    assert (#|m| = #|m0|). clear -H2. induction H2; simpl; auto. rewrite H4.
    auto using lift_eq_term.
Qed.

Lemma weakening_cumul `{CF:checker_flags} Σ Γ Γ' Γ'' M N :
  wf Σ ->
  Σ ;;; Γ ,,, Γ' |- M <= N ->
  Σ ;;; Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ' |- lift #|Γ''| #|Γ'| M <= lift #|Γ''| #|Γ'| N.
Proof.
  intros wfΣ. induction 1.
  constructor.
  - now apply lift_leq_term.
  - eapply weakening_red1 in H; auto.
    econstructor 2; eauto.
  - eapply weakening_red1 in H0; auto.
    econstructor 3; eauto.
Qed.

Lemma lift_eq_context `{checker_flags} φ l l' n k :
  eq_context φ l l' = true ->
  eq_context φ (lift_context n k l) (lift_context n k l') = true.
Proof.
  induction l in l', n, k |- *; intros; destruct l'; rewrite ?lift_context_snoc0;
    try (discriminate || reflexivity).
  simpl in *. rewrite andb_true_iff in *.
  intuition. unfold eq_context in H2. apply forallb2_length in H2. rewrite <- H2.
  destruct a, c; try congruence.
  unfold eq_decl in *. simpl.
  destruct decl_body, decl_body0; simpl in *; try congruence.
  simpl in *. rewrite andb_true_iff in *.
  intuition auto using lift_eq_term.
  intuition auto using lift_eq_term.
Qed.

Lemma lift_check_correct_arity:
  forall (cf : checker_flags) (Σ : global_context) (Γ' : context) (ind : inductive) (u : universe_instance)
         (npar : nat) (args : list term) (idecl : one_inductive_body)
         (Γ'' : context) (indctx pctx : list context_decl),
    check_correct_arity (snd Σ) idecl ind u indctx (firstn npar args) pctx = true ->
    check_correct_arity
      (snd Σ) idecl ind u (lift_context #|Γ''| #|Γ'| indctx) (firstn npar (map (lift #|Γ''| #|Γ'|) args))
      (lift_context #|Γ''| #|Γ'| pctx) = true.
Proof.
  intros cf Σ Γ' ind u npar args idecl Γ'' indctx pctx.
  unfold check_correct_arity.
  destruct pctx in indctx |- *. simpl; try congruence. simpl.
  rewrite lift_context_snoc0. simpl.
  unfold eq_context.
  unfold UnivSubst.subst_instance_context.
  rewrite !andb_true_iff. intros.
  destruct H. split.
  destruct c. destruct decl_body; try discriminate.
  unfold eq_decl in *. simpl in *.
  assert (#|indctx| = #|pctx|) by now eapply forallb2_length in H0.
  rewrite <- H1.
  clear H0.
  eapply (lift_eq_term _ #|Γ''| (#|indctx| + #|Γ'|)) in H.
  rewrite lift_mkApps, map_app in H. simpl in H.
  rewrite firstn_map. rewrite to_extended_list_lift.
  erewrite <- (to_extended_list_map_lift #|Γ''|) in H.
  rewrite <- H. f_equal. f_equal. f_equal. rewrite lift_context_length.
  rewrite !map_map_compose. apply map_ext.
  intros. unfold compose. now rewrite permute_lift.
  eapply lift_eq_context in H0. eapply H0.
Qed.

Lemma lift_declared_projection `{checker_flags} Σ c mdecl idecl pdecl n k :
  wf Σ ->
  declared_projection (fst Σ) mdecl idecl c pdecl ->
  on_snd (lift n (S (ind_npars mdecl + k))) pdecl = pdecl.
Proof.
  unfold declared_projection. destruct c as [[i k'] ci]. intros wfΣ [Hidecl Hcdecl].
  simpl in *.
  pose proof Hidecl. destruct H0 as [Hmdecl Hidecl'].
  eapply lookup_on_global_env in Hmdecl; eauto.
  destruct Hmdecl as [Σ' [wfΣ' ongdecl]].
  red in ongdecl. red in ongdecl.
  eapply nth_error_alli in Hidecl'; eauto.
  apply onProjections in Hidecl'.
  destruct decompose_prod_assum eqn:Heq.
  destruct Hidecl' as [Hpars _].
  destruct Σ. eapply (lift_declared_inductive _ _ _ _ n k) in Hidecl; eauto.
  destruct pdecl as [id t'].
  destruct idecl; simpl in *.
  destruct (decompose_prod_assum _ _) eqn:Heq'.
  injection Hidecl.
  intros.
  rewrite <- H2 in Heq. rewrite Heq in Heq'. injection Heq'. intros <- <-.
  forward Hpars. destruct ind_projs; destruct ci; discriminate.
  rewrite Hpars in H0.
  pose proof Hcdecl as Hcdecl'.
  rewrite <- H0 in Hcdecl.
  rewrite nth_error_map in Hcdecl; eauto.
  rewrite Hcdecl' in Hcdecl. simpl in Hcdecl.
  congruence.
Qed.

Lemma weakening_typing `{cf : checker_flags} Σ Γ Γ' Γ'' (t : term) :
  wf Σ ->
  wf_local Σ (Γ ,,, Γ') ->
  wf_local Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') ->
  `(Σ ;;; Γ ,,, Γ' |- t : T ->
    Σ ;;; Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ' |-
    lift #|Γ''| #|Γ'| t : lift #|Γ''| #|Γ'| T).
Proof.
  intros HΣ HΓΓ' HΓ'' * H.
  generalize_eqs H. intros eqw. rewrite <- eqw in HΓΓ'.
  revert Γ Γ' Γ'' HΓ'' eqw.
  revert Σ HΣ Γ0 HΓΓ' t T H.
  apply (typing_ind_env (fun Σ Γ0 t T =>  forall Γ Γ' Γ'' : context,
    wf_local Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') ->
    Γ0 = Γ ,,, Γ' ->
    Σ;;; Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ' |- lift #|Γ''| #|Γ'| t : lift #|Γ''| #|Γ'| T));
    intros Σ wfΣ Γ0 wfΓ0; intros; subst Γ0; simpl in *; try solve [econstructor; eauto].

  - elim (leb_spec_Set); intros Hn.
    + destruct (weaken_safe_nth_ge _ _ _ isdecl Γ'' Hn) as [isdecl' ->].
      rewrite simpl_lift; try omega. rewrite Nat.add_succ_r.
      constructor. auto.
    + destruct (weaken_safe_nth_lt _ _ _ isdecl Γ'' Hn) as [isdecl' H'].
      apply (f_equal decl_type) in H'.
      unfold lift_decl in H'. simpl in H'.
      assert (forall t, lift0 (S n) (lift #|Γ''| (#|Γ'| - S n) t) = lift #|Γ''| #|Γ'| (lift0 (S n) t)).
      intros. assert (#|Γ'| = S n + (#|Γ'| - S n)) by easy.
      rewrite H at 2.
      rewrite <- permute_lift; try easy.
      rewrite <- H. rewrite <- H'. constructor. auto.

  - econstructor; auto.
    specialize (X2 Γ (Γ' ,, vass n t) Γ'').
    forward X2. rewrite lift_context_snoc. simpl. econstructor; eauto.
    simpl. rewrite Nat.add_0_r. eapply X0; auto.
    rewrite lift_context_snoc, plus_0_r in X2.
    eapply X2. reflexivity.

  - econstructor; auto.
    simpl.
    specialize (X2 Γ (Γ' ,, vass n t) Γ'').
    forward X2. rewrite lift_context_snoc. simpl; econstructor; eauto.
    simpl.  rewrite Nat.add_0_r. eapply X0; auto.
    rewrite lift_context_snoc, plus_0_r in X2.
    eapply X2. reflexivity.

  - econstructor; auto.
    specialize (X2 Γ Γ' Γ'' X5 eq_refl). simpl.
    specialize (X4 Γ (Γ' ,, vdef n b b_ty) Γ'').
    forward X4. rewrite lift_context_snoc. simpl; econstructor; eauto.
    simpl. rewrite Nat.add_0_r. auto.
    rewrite lift_context_snoc, plus_0_r in X4. apply X4. reflexivity.

  - econstructor; auto.
    now apply lift_isApp.
    now apply map_non_nil.
    clear X0 X H0 H.
    induction X1. econstructor; eauto.
    eapply type_spine_cons.
    simpl in p. apply p; auto.
    change (tProd na (lift #|Γ''| #|Γ'| A) (lift #|Γ''| (S #|Γ'|) B))
      with (lift #|Γ''| #|Γ'| (tProd na A B)).
    eapply weakening_cumul; eauto. auto.
    rewrite distr_lift_subst in IHX1. apply IHX1.

  - autorewrite with lift.
    rewrite map_cst_type. constructor; auto.
    erewrite <- lift_declared_constant; eauto.

  - autorewrite with lift.
    erewrite <- (ind_type_map (fun Γ => lift #|Γ''| (#|Γ| + #|Γ'|))).
    pose proof isdecl as isdecl'.
    destruct isdecl. intuition auto.
    eapply lift_declared_inductive in isdecl'.
    rewrite isdecl'.
    econstructor; try red; intuition eauto.
    auto.

  - rewrite (lift_declared_constructor _ (ind, i) u mdecl idecl cdecl _ _ wfΣ isdecl).
    econstructor; eauto.

  - rewrite lift_mkApps, map_app, map_skipn.
    specialize (X4 _ _ _ X6 eq_refl).
    specialize (X2 _ _ _ X6 eq_refl).
    specialize (X1 _ _ _ X6 eq_refl).
    simpl. econstructor.
    5:{ eapply lift_types_of_case in H2.
        simpl in H2. subst pars. rewrite firstn_map. eapply H2.

    -- eapply typing_wf in X0; wf.
    -- eapply typing_wf_sigma in wfΣ.
       destruct H0. red in H0.
       eapply (lookup_on_global_env _ _ _ _ wfΣ) in H0 as [Σ' [wfΣ' H0]]; eauto.
       red in H0. red in H0.
       eapply (nth_error_alli H5) in H0. apply onArity in H0; wf. }
    -- eauto.
    -- erewrite lift_declared_inductive; eauto.
    -- auto.
    -- auto.
    -- revert H3.
       subst pars.
       erewrite lift_declared_inductive; eauto.
       apply lift_check_correct_arity.
    -- destruct idecl; simpl in *; auto.
       destruct decompose_prod_assum. auto.
    -- now rewrite !lift_mkApps in X4.
    -- eapply Forall2_map. close_Forall. intros; intuition eauto.
       destruct x, y; simpl in *. eauto.

  - unfold substl. simpl.
    erewrite (distr_lift_subst_rec _ _ _ 0 #|Γ'|).
    simpl. rewrite map_rev.
    subst ty.
    rewrite List.rev_length, UnivSubst.lift_subst_instance_constr.
    replace (lift #|Γ''| (S (#|args| + #|Γ'|)) (snd pdecl))
      with (snd (on_snd (lift #|Γ''| (S (#|args| + #|Γ'|))) pdecl)) by now destruct pdecl.
    econstructor.
    red. split. apply (proj1 isdecl).
    rewrite (proj2 isdecl). f_equal.
    rewrite H.
    symmetry; eapply lift_declared_projection; eauto.
    specialize (X1 _ _ _ X2 eq_refl).
    rewrite lift_mkApps in X1. eapply X1.
    now rewrite map_length.

  - subst ty.
    erewrite map_dtype, map_def_safe_nth. simpl.
    assert (wf_local Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ' ,,, lift_context #|Γ''| #|Γ'| (fix_context mfix))).
    subst types.
    apply All_local_env_app in X as [X Hfixc].
    apply All_local_env_app_inv. intuition.
    revert Hfixc. clear X0 X.
    induction 1; simpl; auto; try constructor; rewrite lift_context_snoc. econstructor; auto.
    -- destruct t0 as [Ht IHt].
       specialize (IHt Γ (Γ' ,,, Γ0) Γ''). forward IHt.
       { apply All_local_env_app in X1.
         apply All_local_env_app_inv. intuition.
         rewrite lift_context_app.
         apply All_local_env_app_inv. intuition.
         rewrite Nat.add_0_r. eapply All_local_env_impl; eauto. intros.
         now unfold app_context in *; rewrite <- app_assoc. }
       rewrite lift_context_app, Nat.add_0_r in IHt.
       unfold app_context in *. rewrite <- !app_assoc, app_length in IHt.
       specialize (IHt eq_refl). apply IHt.
    -- destruct t0 as [Ht IHt].
       specialize (IHt Γ (Γ' ,,, Γ0) Γ''). forward IHt.
       { apply All_local_env_app in X1.
         apply All_local_env_app_inv. intuition.
         rewrite lift_context_app.
         apply All_local_env_app_inv. intuition.
         rewrite Nat.add_0_r. eapply All_local_env_impl; eauto. intros.
         now unfold app_context in *; rewrite <- app_assoc. }
       constructor; auto.
       rewrite lift_context_app, Nat.add_0_r in IHt.
       unfold app_context in *. rewrite <- !app_assoc, app_length in IHt.
       specialize (IHt eq_refl). simpl. apply IHt.
    -- eapply type_Fix.
       now rewrite lift_fix_context.
       rewrite lift_fix_context.
       apply All_map.
       clear X. eapply All_impl; eauto.
       clear X0. unfold compose; simpl; intros [na ty bod] [[Htyd Hlam] IH].
       simpl in *. intuition.
       specialize (IH Γ (Γ' ,,, fix_context mfix) Γ'').
       rewrite lift_context_app in IH.
       rewrite !app_context_assoc, Nat.add_0_r, !app_context_length, fix_context_length in IH.
       specialize (IH X2 eq_refl).
       rewrite permute_lift, lift_context_length, fix_context_length.
       subst types; rewrite fix_context_length in IH; apply IH.
       lia.
       now apply isLambda_lift.

  - subst ty.
    erewrite map_dtype, map_def_safe_nth. simpl.
    assert (wf_local Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ' ,,, lift_context #|Γ''| #|Γ'| (fix_context mfix))).
    subst types.
    apply All_local_env_app in X as [X Hfixc].
    apply All_local_env_app_inv. intuition.
    revert Hfixc. clear X0 X.
    induction 1; simpl; auto; try constructor; rewrite lift_context_snoc. econstructor; auto.
    -- destruct t0 as [Ht IHt].
       specialize (IHt Γ (Γ' ,,, Γ0) Γ''). forward IHt.
       { apply All_local_env_app in X1.
         apply All_local_env_app_inv. intuition.
         rewrite lift_context_app.
         apply All_local_env_app_inv. intuition.
         rewrite Nat.add_0_r. eapply All_local_env_impl; eauto. intros.
         now unfold app_context in *; rewrite <- app_assoc. }
       rewrite lift_context_app, Nat.add_0_r in IHt.
       unfold app_context in *. rewrite <- !app_assoc, app_length in IHt.
       specialize (IHt eq_refl). apply IHt.
    -- destruct t0 as [Ht IHt].
       specialize (IHt Γ (Γ' ,,, Γ0) Γ''). forward IHt.
       { apply All_local_env_app in X1.
         apply All_local_env_app_inv. intuition.
         rewrite lift_context_app.
         apply All_local_env_app_inv. intuition.
         rewrite Nat.add_0_r. eapply All_local_env_impl; eauto. intros.
         now unfold app_context in *; rewrite <- app_assoc. }
       constructor; auto.
       rewrite lift_context_app, Nat.add_0_r in IHt.
       unfold app_context in *. rewrite <- !app_assoc, app_length in IHt.
       specialize (IHt eq_refl). simpl. apply IHt.
    -- eapply type_CoFix.
       now rewrite lift_fix_context.
       rewrite lift_fix_context.
       apply All_map.
       clear X. eapply All_impl; eauto.
       clear X0. unfold compose; simpl; intros [na ty bod] [Htyd IH].
       simpl in *. intuition.
       specialize (IH Γ (Γ' ,,, fix_context mfix) Γ'').
       rewrite lift_context_app in IH.
       rewrite !app_context_assoc, Nat.add_0_r, !app_context_length, fix_context_length in IH.
       specialize (IH X2 eq_refl).
       rewrite permute_lift, lift_context_length, fix_context_length.
       subst types; rewrite fix_context_length in IH; apply IH.
       lia.

  - econstructor; eauto.
    now eapply weakening_cumul.
Qed.

Lemma weakening `{cf : checker_flags} Σ Γ Γ' (t : term) T :
  wf Σ -> wf_local Σ (Γ ,,, Γ') ->
  Σ ;;; Γ |- t : T ->
  Σ ;;; Γ ,,, Γ' |- lift0 #|Γ'| t : lift0 #|Γ'| T.
Proof.
  intros HΣ HΓΓ' * H.
  pose (weakening_typing Σ Γ [] Γ' t).
  forward t0; eauto.
  forward t0; eauto. now eapply wf_local_app in HΓΓ'.
Qed.

Inductive subs `{cf : checker_flags} Σ (Γ : context) : list term -> context -> Type :=
| emptys : subs Σ Γ [] []
| conss Δ s na t T : subs Σ Γ s Δ ->
              Σ ;;; Γ |- t : substl s T ->
              subs Σ Γ (t :: s) (Δ ,, vass na T).

Theorem substitution `{checker_flags} Σ Γ Γ' s Δ (t : term) T :
  wf Σ -> wf_local Σ Γ ->
  subs Σ Γ s Γ' ->
  Σ ;;; Γ ,,, Γ' ,,, Δ |- t : T ->
  Σ ;;; Γ ,,, map_context (substl s) Δ |- substl s t : substl s T.
Proof.
  intros HΣ HΓ * Ht Hu.
Admitted.

Lemma substitution0 `{checker_flags} Σ Γ n u U (t : term) :
  wf Σ -> wf_local Σ Γ ->
  `(Σ ;;; Γ ,, vass n U |- t : T -> Σ ;;; Γ |- u : U ->
    Σ ;;; Γ |- t {0 := u} : T {0 := u}).
Proof.
  intros HΣ HΓ * Ht Hu.
Admitted.
