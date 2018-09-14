(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import config utils Ast AstUtils Induction utils LiftSubst Typing.

(** * Weakening and substitution lemmas for typing derivations.

  *WIP*

  Standard structural lemmas on typing derivations. *)

Set Asymmetric Patterns.

Generalizable Variables Σ Γ t T.

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

Lemma lift_context_snoc0 n k Γ d : lift_context n k (d :: Γ) = lift_context n k Γ ,, lift_decl n (#|Γ| + k) d.
Proof.
  unfold lift_context.
  simpl.
  pose proof (lift_context_rec_fst n k Γ).
  revert H. destruct lift_context_rec. simpl.
  now intros ->.
Qed.
Hint Rewrite lift_context_snoc0 : lift.

Lemma lift_context_snoc n k Γ d : lift_context n k (Γ ,, d) = lift_context n k Γ ,, lift_decl n (#|Γ| + k) d.
Proof.
  unfold lift_context.
  simpl.
  pose proof (lift_context_rec_fst n k Γ).
  revert H. destruct lift_context_rec. simpl.
  now intros ->.
Qed.
Hint Rewrite lift_context_snoc : lift.

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
  rewrite Heq in onProjections.
  apply (All_map_id onProjections).
  intros [x p]. intros [s Hty].
  unfold on_snd; f_equal; f_equal.
  eapply typed_liftn. 4:eapply Hty. wf. wf. simpl. lia.
Qed.

Lemma lift_declared_inductive `{checker_flags} Σ ind mdecl idecl n k :
  wf Σ ->
  declared_inductive (fst Σ) ind mdecl idecl ->
  map_one_inductive_body (inductive_mind ind) (polymorphic_instance (mdecl.(ind_universes))) (arities_context mdecl.(ind_bodies)) (fun Γ => lift n (#|Γ| + k))
                         (inductive_ind ind) idecl = idecl.
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

Lemma inds_length ind u l : #|inds ind u l| = #|l|.
Proof.
  unfold inds. induction l; simpl; congruence.
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
  rewrite !lift_mkApps, !map_app, lift_context_len.
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

Lemma forallb2_length {A} (p : A -> A -> bool) l l' : forallb2 p l l' = true -> length l = length l'.
Proof.
  induction l in l' |- *; destruct l'; simpl; try congruence.
  rewrite !andb_true_iff. intros [Hp Hl]. erewrite IHl; eauto.
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
  rewrite <- H. f_equal. f_equal. f_equal. rewrite lift_context_len.
  rewrite !map_map_compose. apply map_ext.
  intros. unfold compose. now rewrite permute_lift.
  eapply lift_eq_context in H0. eapply H0.
Qed.

Lemma lift_declared_projection `{checker_flags} Σ c mdecl idecl pdecl n k :
  wf Σ ->
  declared_projection (fst Σ) mdecl idecl c pdecl ->
  on_snd (lift n (S (#|arities_context (ind_bodies mdecl)| + k))) pdecl = pdecl.
Proof.
  unfold declared_projection. destruct c as [[i k'] ci]. intros wfΣ [Hidecl Hcdecl].
  destruct Σ. eapply (lift_declared_inductive _ _ _ _ n k) in Hidecl; eauto.
  destruct pdecl as [id t'].
  destruct idecl; simpl in *.
  destruct (decompose_prod_assum _ _) eqn:Heq.
  injection Hidecl.
  intros.
  pose Hcdecl as Hcdecl'.
  rewrite <- H0 in Hcdecl'.
  rewrite nth_error_map in Hcdecl'. rewrite Hcdecl in Hcdecl'.
  simpl in Hcdecl'. injection Hcdecl'.
  intros. unfold on_snd. simpl.

  rewrite H3.
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
    erewrite <- (ind_type_map (fun Γ => lift #|Γ''| (#|Γ| + #|Γ'|)) []).
    econstructor; eauto. red.
    pose proof isdecl as isdecl'.
    destruct isdecl. intuition auto.
    eapply lift_declared_inductive in isdecl'.
    rewrite isdecl'. auto. apply wfΣ.

  - rewrite (lift_declared_constructor _ (ind, i) u mdecl idecl cdecl _ _ wfΣ isdecl).
    econstructor; eauto.

  - rewrite lift_mkApps, map_app, map_skipn.
    specialize (X4 _ _ _ X6 eq_refl).
    specialize (X2 _ _ _ X6 eq_refl).
    specialize (X1 _ _ _ X6 eq_refl).
    simpl. econstructor. shelve. shelve. shelve. eauto.
    eapply lift_types_of_case in H2.
    simpl in H2. subst pars. rewrite firstn_map. eapply H2.

    -- eapply typing_wf in X0; wf.
    -- eapply typing_wf_sigma in wfΣ.
       destruct H0. red in H0.
       eapply (lookup_on_global_env _ _ _ _ wfΣ) in H0 as [Σ' [wfΣ' H0]]; eauto.
       red in H0. red in H0.
       eapply (nth_error_all H5) in H0. apply onArity in H0; wf.
    -- revert H3.
       subst pars.
       erewrite lift_declared_inductive; eauto.
       apply lift_check_correct_arity.
    -- destruct idecl; simpl in *; auto.
    -- now rewrite !lift_mkApps in X4.
    -- eapply Forall2_map. close_Forall. intros; intuition eauto.
      destruct x, y; simpl in *. eauto.

  - unfold substl. simpl.
    erewrite (distr_lift_subst_rec _ _ _ 0 #|Γ'|).
    simpl. rewrite map_rev.
    subst ty.
    rewrite List.rev_length.
    replace (lift #|Γ''| (S (#|args| + #|Γ'|)) (snd pdecl))
      with (snd (on_snd (lift #|Γ''| (S (#|args| + #|Γ'|))) pdecl)) by now destruct pdecl.
    econstructor.
    red. destruct isdecl. split. apply d.
    rewrite e. f_equal.
    pose lift_declared_projection.



    specialize (X1 _ _ _ X2 eq_refl).
    rewrite lift_mkApps in X1. eapply X1.

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
