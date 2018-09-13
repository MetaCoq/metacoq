(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import config utils Ast AstUtils Induction utils LiftSubst Typing.

(** * Weakening and substitution lemmas for typing derivations.

  *WIP*

  Standard structural lemmas on typing derivations. *)

Set Asymmetric Patterns.

Generalizable Variables Σ Γ t T.
Existing Instance default_checker_flags.

Lemma length_app_context Γ Γ' : #|Γ ,,, Γ'| = #|Γ| + #|Γ'|.
Proof.
  unfold app_context. rewrite app_length. omega.
Qed.

Definition map_decl (f : term -> term) (d : context_decl) : context_decl :=
  {| decl_name := d.(decl_name);
     decl_body := option_map f d.(decl_body);
     decl_type := f d.(decl_type) |}.

Definition lift_decl n k (d : context_decl) := map_decl (lift n k) d.

Definition lift_context_rec n k (Γ : context) : nat * context :=
  List.fold_right (fun decl '(k, Γ) => (S k, lift_decl n k decl :: Γ)) (k, []) Γ.

Definition lift_context n k Γ := snd (lift_context_rec n k Γ).

Lemma lift0_context k Γ : lift_context 0 k Γ = Γ.
Proof.
  unfold lift_context; induction Γ; simpl; trivial.
  simpl. destruct lift_context_rec. simpl in *.
  unfold lift_decl, map_decl. destruct a. simpl. rewrite IHΓ; f_equal.
  f_equal.
  now destruct decl_body; simpl; rewrite ?lift0_id.
  now rewrite ?lift0_id.
Qed.

Lemma lift_context_rec_fst n k Γ :
  fst (lift_context_rec n k Γ) = #|Γ| + k.
Proof.
  induction Γ; simpl; auto.
  destruct lift_context_rec; simpl in *.
  congruence.
Qed.
Hint Rewrite lift_context_rec_fst : lift.

Lemma lift_context_len n k Γ : #|lift_context n k Γ| = #|Γ|.
Proof.
  unfold lift_context; induction Γ; simpl; trivial.
  destruct lift_context_rec. simpl in *. auto with arith.
Qed.
Hint Rewrite lift_context_len : lift.

Lemma lift_context_snoc n k Γ d : lift_context n k (Γ ,, d) = lift_context n k Γ ,, lift_decl n (#|Γ| + k) d.
Proof.
  unfold lift_context.
  simpl.
  pose proof (lift_context_rec_fst n k Γ).
  revert H. destruct lift_context_rec. simpl.
  now intros ->.
Qed.
Hint Rewrite lift_context_snoc : lift.

Lemma some_inj {A} {x y : A} : Some x = Some y -> x = y.
Proof.
  now intros [=].
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

Lemma weaken_safe_nth_ge Γ Γ' v (isdecl : v < #|Γ ,,, Γ'|) Γ'' : #|Γ'| <= v ->
  { isdecl' : _ &
  safe_nth (Γ ,,, Γ') (exist (fun n0 : nat => n0 < #|Γ ,,, Γ'|) v isdecl) =
  safe_nth (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') (exist _ (#|Γ''| + v) isdecl') }.
Proof.
  simpl.
  assert(#|Γ''| + v < #|Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ'|).
  rewrite !length_app_context in *. autorewrite with lift. omega.
  exists H.
  apply some_inj; rewrite <- !nth_error_safe_nth.
  rewrite nth_error_app_ge; try easy.
  rewrite (nth_error_app_ge (_ + v)); rewrite ?lift_context_len; try easy.
  rewrite nth_error_app_ge; rewrite ?lift_context_len; try easy.
Qed.

Lemma weaken_safe_nth_lt Γ Γ' v (isdecl : v < #|Γ ,,, Γ'|) Γ'' : v < #|Γ'| ->
  { isdecl' : _ &
  safe_nth (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') (exist _ v isdecl') =
  lift_decl #|Γ''| (#|Γ'| - S v)
       (safe_nth (Γ ,,, Γ') (exist (fun n0 : nat => n0 < #|Γ ,,, Γ'|) v isdecl)) }.
Proof.
  simpl. intros Hv.
  assert(v < #|Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ'|).
  rewrite !length_app_context in *. autorewrite with lift. omega.
  exists H.
  apply some_inj. rewrite <- !nth_error_safe_nth.
  rewrite nth_error_app_lt. 2:rewrite !length_app_context in H; autorewrite with lift; omega.
  remember (safe_nth (Γ ,,, Γ') (exist _ v isdecl)) as nth.
  apply (f_equal Some) in Heqnth. rewrite <- nth_error_safe_nth in Heqnth.
  rewrite nth_error_app_lt in Heqnth; try easy.
  clear isdecl H Γ.
  revert Γ'' v Hv nth Heqnth.
  induction Γ'; intros.
  - easy.
  - simpl. destruct v.
    + simpl. unfold lift_context. simpl.
      destruct lift_context_rec eqn:Heq.
      pose proof (lift_context_rec_fst #|Γ''| 0 Γ'). rewrite Heq in H. simpl in H. subst n.
      simpl. rewrite Nat.add_0_r, Nat.sub_0_r.
      simpl in *. now injection Heqnth as ->.
    + simpl.
      unfold lift_context. simpl.
      destruct lift_context_rec eqn:Heq.
      pose proof (lift_context_rec_fst #|Γ''| 0 Γ'). rewrite Heq in H. simpl in H. subst n.
      simpl in *.
      assert (v < #|Γ'|) by easy.
      specialize (IHΓ' Γ'' v  H nth Heqnth).
      rewrite <- IHΓ'.
      f_equal. unfold lift_context. rewrite Heq. reflexivity.
Qed.

Lemma typecheck_closed `{cf : checker_flags} :
  env_prop (fun Σ Γ t T =>
              closedn #|Γ| t && closedn #|Γ| T = true).
Proof.
  apply typing_ind_env; intros; simpl; rewrite ?andb_true_iff in *; try solve [intuition auto].
  - elim (Nat.ltb_spec n #|Γ|); intuition.
    admit (* Need induction with IHs for environments *).
  - (* typing spine ind *) admit.
  - admit. (* easy now *)
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

Require Import Lia.

Lemma lift_simpl (Γ'' Γ' : context) i t : i < #|Γ'| ->
  lift0 (S i) (lift #|Γ''| (#|Γ'| - S i) t) = lift #|Γ''| #|Γ'| (lift0 (S i) t).
Proof.
  intros. assert (#|Γ'| = S i + (#|Γ'| - S i)) by easy.
  rewrite H0 at 2.
  rewrite <- permute_lift; try easy.
Qed.

Lemma nth_map {A} (f : A -> A) n l d :
  (d = f d) ->
  nth n (map f l) d = f (nth n l d).
Proof.
  induction n in l |- *; destruct l; simpl; auto.
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

Lemma declared_decl_info `{checker_flags} Σ c decl :
  type_global_env (snd Σ) (fst Σ) ->
  lookup_env (fst Σ) c = Some decl ->
  { Σ' & { wfΣ' : wf Σ' & type_global_decl Σ' decl } }.
Proof.
  induction 1; simpl. congruence.
  destruct ident_eq. intros [= ->].
  exists (Σ0, snd Σ). exists X. auto.
  apply IHX.
Qed.

Lemma lift_declared_constant `{checker_flags} Σ cst decl n k :
  wf Σ ->
  declared_constant (fst Σ) cst decl ->
  decl = map_constant_body (lift n k) decl.
Proof.
  unfold declared_constant.
  intros.
  eapply declared_decl_info in H0; auto.
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

Definition on_pi2 {A B C} (f : B -> B) (p : A * B * C) : A * B * C :=
  (fst (fst p), f (snd (fst p)), snd p).

Definition map_one_inductive_body params arities f m :=
  match m with
  | Build_one_inductive_body ind_name ind_type ind_kelim ind_ctors ind_projs =>
    Build_one_inductive_body ind_name
                             (f [] ind_type)
                             ind_kelim
                             (map (on_pi2 (f arities)) ind_ctors)
                             (map (on_snd (f (arities ,,, params ,, vass nAnon ind_type))) ind_projs)
  end.

Definition map_mutual_inductive_body f m :=
  match m with
  | Build_mutual_inductive_body ind_npars ind_bodies ind_universes =>
    let params := [] in (* FIXME *)
    let arities := arities_context ind_bodies in
    Build_mutual_inductive_body ind_npars
                                (map (map_one_inductive_body params arities f) ind_bodies)
                                ind_universes
  end.

Definition lift_mutual_inductive_body n k m :=
  map_mutual_inductive_body (fun Γ => lift n (#|Γ| + k)) m.

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

Lemma All_map_id {A} {P : A -> Type} {l} {f} :
  All P l ->
  (forall x, P x -> f x = x) ->
  map f l = l.
Proof.
  induction 1; simpl; f_equal; intuition auto.
  f_equal; auto.
Qed.

Lemma lift_declared_minductive `{checker_flags} Σ cst decl n k :
  wf Σ ->
  declared_minductive (fst Σ) cst decl ->
  lift_mutual_inductive_body n k decl = decl.
Proof.
  unfold declared_minductive.
  intros.
  eapply declared_decl_info in H0; auto.
  destruct H0 as [Σ' [wfΣ' decl']].
  do 2 red in decl'.
  destruct decl. simpl in *. f_equal.
  revert decl'. generalize ind_bodies at 2 4 5. induction 1. constructor.
  simpl. f_equal; auto. clear IHdecl'.
  f_equal.
  red in i. red in i. destruct i as [s tys].
  eapply typed_liftn; eauto. constructor. simpl; lia.
  red in t.
  apply (All_map_id t).
  intros [[x p] n']. intros [s Hty].
  unfold on_pi2; f_equal; f_equal. eapply typed_liftn; eauto with wf. lia.
  apply (All_map_id t0).
  intros [x p]. intros [s Hty].
  unfold on_snd; f_equal; f_equal.
  eapply typed_liftn. 4:eapply Hty. eauto with wf. eauto with wf. simpl. lia.
Qed.

Lemma ind_type_map f pars arities oib :
  ind_type (map_one_inductive_body pars arities f oib) = f [] (ind_type oib).
Proof. destruct oib; reflexivity. Qed.

Lemma lift_declared_inductive `{checker_flags} Σ ind mdecl idecl n k :
  wf Σ ->
  declared_inductive (fst Σ) ind mdecl idecl ->
  map_one_inductive_body [] (arities_context mdecl.(ind_bodies)) (fun Γ => lift n (#|Γ| + k)) idecl = idecl.
Proof.
  unfold declared_inductive. intros wfΣ [Hmdecl Hidecl].
  destruct Σ. eapply (lift_declared_minductive _ _ _ n k) in Hmdecl.
  unfold lift_mutual_inductive_body in Hmdecl.
  destruct mdecl. simpl in *.
  injection Hmdecl. intros Heq.
  clear Hmdecl.
  pose proof Hidecl as Hidecl'.
  rewrite <- Heq in Hidecl'.
  rewrite nth_error_map in Hidecl'.
  clear Heq.
  unfold option_map in Hidecl'. rewrite Hidecl in Hidecl'.
  congruence. auto.
Qed.

Lemma inds_length ind u l : #|inds ind u l| = #|l|.
Proof.
  unfold inds. induction l; simpl; congruence.
Qed.

Lemma lift_declared_constructor `{checker_flags} Σ c u mdecl idecl cdecl n k :
  wf Σ ->
  declared_constructor (fst Σ) mdecl idecl c cdecl ->
  lift n k (type_of_constructor mdecl cdecl c u) = (type_of_constructor mdecl cdecl c u).
Proof.
  unfold declared_constructor. destruct c as [i ci]. intros wfΣ [Hidecl Hcdecl].
  destruct Σ. eapply (lift_declared_inductive _ _ _ _ n k) in Hidecl; eauto.
  unfold type_of_constructor. destruct cdecl as [[id t] arity].
  destruct idecl; simpl in *. injection Hidecl.
  intros.
  pose Hcdecl as Hcdecl'.
  rewrite <- H1 in Hcdecl'.
  rewrite nth_error_map in Hcdecl'. rewrite Hcdecl in Hcdecl'.
  simpl in Hcdecl'. injection Hcdecl'.
  intros.
  rewrite <- H3 at 2.
  rewrite <- UnivSubst.lift_subst_instance_constr.
  unfold substl.
  rewrite (distr_lift_subst_rec _ _ n 0 k). simpl.
  unfold arities_context. rewrite rev_map_length, inds_length.
  f_equal. generalize (ind_bodies mdecl).
  clear. intros.
  induction l; unfold inds; simpl; auto. f_equal. auto.
Qed.

Lemma weakening_red1 `{CF:checker_flags} Σ Γ Γ' Γ'' M N :
  type_global_env (snd Σ) (fst Σ) ->
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
    eapply (declared_decl_info _ _ _ wfΣ) in H.
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
    apply H0. auto.

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
  type_global_env (snd Σ) (fst Σ) ->
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

Lemma nlt_map {A B} (l : list A) (f : A -> B) (n : {n | n < #|l| }) : `n < #|map f l|.
Proof. destruct n. simpl. now rewrite map_length. Defined.

Lemma map_def_safe_nth {A B} (l : list A) (n : {n | n < #|l| }) (f : A -> B) :
  f (safe_nth l n) = safe_nth (map f l) (exist _ (`n) (nlt_map l f n)).
Proof.
  destruct n.
  induction l in x, l0 |- *. simpl. bang.
  simpl. destruct x. reflexivity. simpl.
  rewrite IHl. f_equal. f_equal. pi.
Qed.

Lemma weakening_rec `{cf : checker_flags} Σ Γ Γ' Γ'' (t : term) :
  type_global_env (snd Σ) (fst Σ) ->
  wf_local Σ (Γ ,,, Γ') -> (* Not necessary now *)
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
    erewrite <- (ind_type_map (fun Γ => lift #|Γ''| (#|Γ| + #|Γ'|)) []).
    econstructor; eauto. red.
    pose proof isdecl as isdecl'.
    destruct isdecl. intuition auto.
    eapply lift_declared_inductive in isdecl'.
    rewrite isdecl'. auto. apply wfΣ.

  - rewrite (lift_declared_constructor _ (ind, i) u mdecl idecl cdecl _ _ wfΣ isdecl).
    econstructor; eauto.

  - rewrite map_app, map_skipn.
    specialize (X3 _ _ _ X5 eq_refl).
    specialize (X1 _ _ _ X5 eq_refl).
    specialize (X0 _ _ _ X5 eq_refl).
    simpl. econstructor; eauto 2.
    admit. admit.

    rewrite lift_mkApps in X3. eauto.
    eapply (Forall2_map _ _ (on_snd (lift #|Γ''| #|Γ'|)) brs btys). close_Forall.
    intros.
    intuition. destruct x, y; simpl in *. subst n0.
    apply b; auto.

  - unfold substl. simpl.
    erewrite (distr_lift_subst_rec _ _ _ 0 #|Γ'|).
    simpl. rewrite map_rev.
    subst ty.
    rewrite List.rev_length.
    replace (lift #|Γ''| (S (#|args| + #|Γ'|)) (snd pdecl))
      with (snd (on_snd (lift #|Γ''| (S (#|args| + #|Γ'|))) pdecl)) by now destruct pdecl.
    econstructor. admit.
    specialize (X0 _ _ _ X1 eq_refl).
    rewrite lift_mkApps in X0. eapply X0.

  - subst ty.
    erewrite map_dtype, map_def_safe_nth. simpl.
    eapply type_Fix. admit.
    admit.

  - subst ty.
    erewrite map_dtype, map_def_safe_nth. simpl.
    eapply type_CoFix. admit.
    admit.

  - econstructor; eauto.
    now eapply weakening_cumul.
Admitted.

Lemma weakening `{cf : checker_flags} Σ Γ Γ' (t : term) T :
  type_global_env (snd Σ) (fst Σ) -> wf_local Σ (Γ ,,, Γ') ->
  Σ ;;; Γ |- t : T ->
  Σ ;;; Γ ,,, Γ' |- lift0 #|Γ'| t : lift0 #|Γ'| T.
Proof.
  intros HΣ HΓΓ' * H.
  pose (weakening_rec Σ Γ [] Γ' t).
  forward t0; eauto.
  forward t0; eauto. now eapply wf_local_app in HΓΓ'.
Qed.

Inductive subs Σ (Γ : context) : list term -> context -> Type :=
| emptys : subs Σ Γ [] []
| conss Δ s na t T : subs Σ Γ s Δ ->
              Σ ;;; Γ |- t : substl s T ->
              subs Σ Γ (t :: s) (Δ ,, vass na T).

Theorem substitution `{checker_flags} Σ Γ Γ' s Δ (t : term) T :
  type_global_env (snd Σ) (fst Σ) -> wf_local Σ Γ ->
  subs Σ Γ s Γ' ->
  Σ ;;; Γ ,,, Γ' ,,, Δ |- t : T ->
  Σ ;;; Γ ,,, map_context (substl s) Δ |- substl s t : substl s T.
Proof.
  intros HΣ HΓ * Ht Hu.
Admitted.

Lemma substitution0 `{checker_flags} Σ Γ n u U (t : term) :
  type_global_env (snd Σ) (fst Σ) -> wf_local Σ Γ ->
  `(Σ ;;; Γ ,, vass n U |- t : T -> Σ ;;; Γ |- u : U ->
    Σ ;;; Γ |- t {0 := u} : T {0 := u}).
Proof.
  intros HΣ HΓ * Ht Hu.
Admitted.
