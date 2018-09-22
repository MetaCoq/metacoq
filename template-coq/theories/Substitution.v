(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega Lia.
From Template Require Import config utils Ast AstUtils Induction utils LiftSubst Typing.
From Template Require Import WeakeningEnv Closed.

(** * Substitution lemmas for typing derivations. *)

Set Asymmetric Patterns.

Generalizable Variables Σ Γ t T.

Definition subst_decl s k (d : context_decl) := map_decl (subst s k) d.

Definition subst_context n k (Γ : context) : context :=
  List.rev (mapi (fun k' decl => subst_decl n (k + k') decl) (List.rev Γ)).

Definition wf_decl_pred : global_context -> context -> term -> term -> Type :=
  (fun _ _ t T => Ast.wf t /\ Ast.wf T).

Lemma subst_decl0 Σ Γ k d : on_local_decl wf_decl_pred Σ Γ d -> subst_decl [] k d = d.
Proof.
  unfold wf_decl_pred; intros Hd; destruct d; destruct decl_body;
    unfold on_local_decl in Hd; unfold subst_decl, map_decl; simpl in *;
    f_equal; simpl; rewrite subst_empty; intuition trivial.
  destruct Hd as [u Hu]; intuition trivial.
Qed.

Lemma nth_error_All_local_env `{checker_flags} {P Σ Γ n} (isdecl : n < #|Γ|) :
  All_local_env P Σ Γ ->
  on_some (on_local_decl P Σ (skipn (S n) Γ)) (nth_error Γ n).
Proof.
  induction 1 in n, isdecl |- *. red; simpl.
  - destruct n; simpl; inv isdecl.
  - destruct n. red; simpl. now exists u.
    simpl. apply IHX. simpl in isdecl. lia.
  - destruct n. auto.
    apply IHX. simpl in *. lia.
Qed.

Lemma All_local_env_wf_decl_inv:
  forall (H : checker_flags) (Σ : global_context) (a : context_decl) (Γ : list context_decl)
         (X : All_local_env wf_decl_pred Σ (a :: Γ)),
    on_local_decl wf_decl_pred Σ Γ a * All_local_env wf_decl_pred Σ Γ.
Proof.
  intros H Σ a Γ X.
  inv X; intuition; red; simpl; eauto.
Qed.

Lemma subst0_context `{checker_flags} Σ k Γ : All_local_env wf_decl_pred Σ Γ -> subst_context [] k Γ = Γ.
Proof.
  unfold subst_context.
  rewrite rev_mapi. rewrite List.rev_involutive.
  unfold mapi. generalize 0. generalize #|List.rev Γ|.
  induction Γ; intros; simpl; trivial.
  eapply All_local_env_wf_decl_inv in X as [Ha HΓ].
  erewrite subst_decl0; f_equal; eauto.
Qed.

Lemma subst_context_length s k Γ : #|subst_context s k Γ| = #|Γ|.
Proof.
  unfold subst_context. now rewrite !List.rev_length, mapi_length, List.rev_length.
Qed.
Hint Rewrite subst_context_length : subst.


Lemma subst_context_snoc s k Γ d : subst_context s k (d :: Γ) = subst_context s k Γ ,, subst_decl s (#|Γ| + k) d.
Proof.
  unfold subst_context.
  rewrite !rev_mapi, !rev_involutive. unfold mapi; rewrite mapi_rec_eqn.
  unfold snoc. f_equal. now rewrite Nat.sub_0_r, Nat.add_comm, List.rev_length.
  rewrite mapi_rec_Sk. simpl. apply mapi_rec_ext. intros.
  rewrite app_length, !List.rev_length. simpl. f_equal. lia.
Qed.
Hint Rewrite subst_context_snoc : subst.

Lemma subst_context_snoc0 s Γ d : subst_context s 0 (Γ ,, d) = subst_context s 0 Γ ,, subst_decl s #|Γ| d.
Proof.
  unfold snoc. now rewrite subst_context_snoc, Nat.add_0_r.
Qed.
Hint Rewrite subst_context_snoc : subst.

Lemma subst_context_alt s k Γ :
  subst_context s k Γ =
  mapi (fun k' d => subst_decl s (pred #|Γ| - k' + k) d) Γ.
Proof.
  unfold subst_context. rewrite rev_mapi. rewrite List.rev_involutive.
  apply mapi_ext. intros. f_equal. now rewrite List.rev_length.
Qed.

Lemma subst_context_app s k Γ Δ :
  subst_context s k (Γ ,,, Δ) = subst_context s k Γ ,,, subst_context s (#|Γ| + k) Δ.
Proof.
  unfold subst_context, app_context.
  rewrite List.rev_app_distr.
  rewrite mapi_app. rewrite <- List.rev_app_distr. f_equal. f_equal.
  apply mapi_ext. intros. f_equal. rewrite List.rev_length. lia.
Qed.

Lemma nth_error_subst_context (Γ' : context) s (v : nat) k :
    nth_error (subst_context s k Γ') v =
    option_map (subst_decl s (#|Γ'| - S v + k)) (nth_error Γ' v).
Proof.
  induction Γ' in v |- *; intros.
  - simpl. unfold subst_context; simpl; rewrite nth_error_nil. easy.
  - simpl. destruct v; rewrite subst_context_snoc.
    + simpl. repeat f_equal; try lia.
    + simpl. rewrite IHΓ'; simpl in *; (lia || congruence).
Qed.

Inductive subs `{cf : checker_flags} Σ (Γ : context) : list term -> context -> Type :=
| emptys : subs Σ Γ [] []
| cons_ass Δ s na t T : subs Σ Γ s Δ ->
              Σ ;;; Γ |- t : substl s T ->
                             subs Σ Γ (t :: s) (Δ ,, vass na T).
(* | cons_let Δ s na t T : subs Σ Γ s Δ -> *)
(*               Σ ;;; Γ |- substl s t : substl s T -> *)
(*               subs Σ Γ (substl s t :: s) (Δ ,, vdef na t T). *)

Lemma subst_length `{checker_flags} Σ Γ s Γ' : subs Σ Γ s Γ' -> #|s| = #|Γ'|.
Proof.
  induction 1; simpl; auto with arith.
Qed.

Hint Rewrite @app_context_length @subst_context_length : wf.

Lemma subs_nth_error_ge `{checker_flags} Σ Γ Γ' Γ'' v s :
  subs Σ Γ s Γ' ->
  #|Γ' ,,, Γ''| <= v ->
  nth_error (Γ ,,, Γ' ,,, Γ'') v =
  nth_error (Γ ,,, subst_context s 0 Γ'') (v - #|Γ'|).
Proof.
  simpl.
  intros. rewrite app_context_length in H0.
  rewrite !nth_error_app_ge; autorewrite with wf; f_equal; try lia.
Qed.

Lemma subs_nth_error_lt `{checker_flags} Σ Γ Γ' Γ'' v s :
  subs Σ Γ s Γ' ->
  v < #|Γ''| ->
  nth_error (Γ ,,, subst_context s 0 Γ'') v =
  option_map (map_decl (subst s (#|Γ''| - S v))) (nth_error (Γ ,,, Γ' ,,, Γ'') v).
Proof.
  simpl. intros Hs Hv.
  rewrite !nth_error_app_lt; autorewrite with wf; f_equal; try lia.
  erewrite nth_error_subst_context. f_equal. unfold subst_decl. rewrite Nat.add_0_r. reflexivity.
Qed.

Lemma subst_iota_red s k pars c args brs :
  subst s k (iota_red pars c args brs) =
  iota_red pars c (List.map (subst s k) args) (List.map (on_snd (subst s k)) brs).
Proof.
  unfold iota_red. rewrite !subst_mkApps. f_equal; auto using map_skipn.
  rewrite nth_map; simpl; auto.
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
Hint Rewrite fix_subst_length cofix_subst_length : wf.

Lemma subst_unfold_fix n k mfix idx narg fn :
  Forall Ast.wf n ->
  unfold_fix mfix idx = Some (narg, fn) ->
  unfold_fix (map (map_def (subst n k) (subst n (#|mfix| + k))) mfix) idx = Some (narg, subst n k fn).
Proof.
  unfold unfold_fix. intros wfn.
  rewrite nth_error_map. destruct (nth_error mfix idx) eqn:Hdef; try congruence.
  intros [= <- <-]. simpl. repeat f_equal. unfold substl.
  erewrite (distr_subst_rec _ _ _ wfn k 0).
  rewrite fix_subst_length. simpl. f_equal.
  unfold fix_subst. rewrite !map_length.
  generalize #|mfix| at 2 3. induction n0; auto. simpl.
  f_equal. apply IHn0.
Qed.
Hint Resolve subst_unfold_fix.

Lemma subst_unfold_cofix n k mfix idx narg fn :
  Forall Ast.wf n ->
  unfold_cofix mfix idx = Some (narg, fn) ->
  unfold_cofix (map (map_def (subst n k) (subst n (#|mfix| + k))) mfix) idx = Some (narg, subst n k fn).
Proof.
  unfold unfold_cofix. intros wfn.
  rewrite nth_error_map. destruct (nth_error mfix idx) eqn:Hdef; try congruence.
  intros [= <- <-]. simpl. repeat f_equal. unfold substl.
  erewrite (distr_subst_rec _ _ _ wfn k 0).
  rewrite cofix_subst_length. simpl. f_equal.
  unfold cofix_subst. rewrite !map_length.
  generalize #|mfix| at 2 3. induction n0; auto. simpl.
  f_equal. apply IHn0.
Qed.
Hint Resolve subst_unfold_cofix.

Lemma subst_is_constructor:
  forall (args : list term) (narg : nat) n k,
    is_constructor narg args = true -> is_constructor narg (map (subst n k) args) = true.
Proof.
  intros args narg.
  unfold is_constructor; intros.
  rewrite nth_error_map. destruct nth_error; try discriminate. simpl. intros.
  destruct t; try discriminate || reflexivity.
  destruct t; try discriminate || reflexivity. simpl.
  destruct l; auto.
Qed.
Hint Resolve subst_is_constructor.
Hint Constructors All_local_env.

Lemma typed_subst `{checker_flags} Σ Γ t T n k :
  wf Σ -> wf_local Σ Γ -> k >= #|Γ| ->
  Σ ;;; Γ |- t : T -> subst n k t = t.
Proof.
  intros wfΣ wfΓ Hk Hty.
  pose proof (typing_wf _ wfΣ _ wfΓ _ _ Hty) as [wft wfT].
  apply typecheck_closed in Hty; eauto.
  destruct Hty as [_ Hcl].
  rewrite andb_true_iff in Hcl. destruct Hcl as [clb clty].
  pose proof (closed_upwards _ _ clb k).
  simpl in *. forward H0 by lia.
  apply (subst_closedn n) in H0; auto.
Qed.

Lemma declared_decl_closed `{checker_flags} Σ cst decl :
  wf Σ ->
  lookup_env (fst Σ) cst = Some decl ->
  on_global_decl (fun Σ Γ b t =>
                    match b with Some b => Ast.wf b | None => True end /\ Ast.wf t /\
                    option_default (closedn #|Γ|) b true && closedn #|Γ| t = true) Σ decl.
Proof.
  intros.
  eapply weaken_lookup_on_global_env; try red; eauto.
  eapply on_global_decls_impl; cycle 1.
  eapply on_global_decls_mix.
  apply (env_prop_sigma _ typecheck_closed _ X).
  apply (env_prop_sigma _ typing_wf_gen _ X).
  intros.
  simpl in X1. destruct X1 as [Hcl Hwf]. red in Hcl, Hwf.
  destruct t; simpl; intuition auto.
  destruct Hwf; simpl; intuition auto.
  destruct Hwf; simpl; intuition auto.
  destruct Hcl; simpl; intuition auto.
  rewrite andb_true_iff in e. intuition.
Qed.

Lemma subst_declared_constant `{checker_flags} Σ cst decl n k u :
  wf Σ ->
  declared_constant (fst Σ) cst decl ->
  map_constant_body (subst n k) (map_constant_body (UnivSubst.subst_instance_constr u) decl) =
  map_constant_body (UnivSubst.subst_instance_constr u) decl.
Proof.
  intros.
  eapply declared_decl_closed in H0; eauto.
  unfold map_constant_body.
  do 2 red in H0. destruct decl as [ty [body|] univs]; simpl in *.
  rewrite andb_true_iff in H0. intuition.
  rewrite <- (closedn_subst_instance_constr 0 body u) in H2.
  rewrite <- (closedn_subst_instance_constr 0 ty u) in H4.
  f_equal. apply subst_closedn; eauto using closed_upwards with arith wf.
  f_equal. apply subst_closedn; eauto using closed_upwards with arith wf.
  red in H0. f_equal.
  intuition. simpl in H3.
  rewrite <- (closedn_subst_instance_constr 0 ty u) in H3.
  eapply subst_closedn; eauto using closed_upwards with arith wf.
Qed.

Definition subst_mutual_inductive_body n k mind m :=
  map_mutual_inductive_body mind (fun Γ => subst n (#|Γ| + k)) m.

Lemma subst_declared_minductive `{checker_flags} Σ cst decl n k :
  wf Σ ->
  declared_minductive (fst Σ) cst decl ->
  subst_mutual_inductive_body n k cst decl = decl.
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
  destruct (decompose_prod_assum [] (subst n k ind_type)) eqn:Heq'.
  destruct X0. simpl in *.
  assert (subst n k ind_type = ind_type).
  destruct onArity as [[s Hs] Hpars].
  eapply typed_subst; eauto. simpl; lia.
  rewrite H0 in Heq'. rewrite Heq in Heq'. revert Heq'; intros [= <- <-].
  f_equal; auto.
  apply (All_map_id onConstructors).
  intros [[x p] n']. intros [[s Hty] Hpars].
  unfold on_pi2; f_equal; f_equal. eapply typed_subst. 4:eapply Hty. wf. wf. lia.
  rewrite Heq in onProjections. destruct onProjections as [_ onProjections].
  apply (All_map_id onProjections).
  intros [x p]. intros [s Hty].
  unfold on_snd; f_equal; f_equal.
  eapply typed_subst. 4:eapply Hty. wf. wf. simpl. lia.
Qed.

Lemma subst_declared_inductive `{checker_flags} Σ ind mdecl idecl n k :
  wf Σ ->
  declared_inductive (fst Σ) ind mdecl idecl ->
  map_one_inductive_body (inductive_mind ind) (polymorphic_instance (mdecl.(ind_universes))) (arities_context mdecl.(ind_bodies)) (fun Γ => subst n (#|Γ| + k)) (inductive_ind ind) idecl = idecl.
Proof.
  unfold declared_inductive. intros wfΣ [Hmdecl Hidecl].
  destruct Σ. eapply (subst_declared_minductive _ _ _ n k) in Hmdecl.
  unfold subst_mutual_inductive_body in Hmdecl.
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

Lemma substl_inds_subst ind u mdecl n k t :
  Forall Ast.wf n ->
  (substl (inds (inductive_mind ind) u (ind_bodies mdecl))
          (subst n (#|arities_context (ind_bodies mdecl)| + k) t)) =
  subst n k (substl (inds (inductive_mind ind) u (ind_bodies mdecl)) t).
Proof.
  unfold substl. intros wfn.
  pose proof (distr_subst_rec t (inds (inductive_mind ind) u (ind_bodies mdecl)) n wfn k 0).
  simpl in H. rewrite H.
  unfold arities_context. rewrite rev_map_length, inds_length.
  f_equal. generalize (ind_bodies mdecl).
  clear. intros.
  induction l; unfold inds; simpl; auto. f_equal. auto.
Qed.

Lemma subst_declared_constructor `{checker_flags} Σ c u mdecl idecl cdecl n k :
  wf Σ -> Forall Ast.wf n ->
  declared_constructor (fst Σ) mdecl idecl c cdecl ->
  subst (map (UnivSubst.subst_instance_constr u) n) k (type_of_constructor mdecl cdecl c u) = (type_of_constructor mdecl cdecl c u).
Proof.
  unfold declared_constructor. destruct c as [i ci]. intros wfΣ wfn [Hidecl Hcdecl].
  destruct Σ. eapply (subst_declared_inductive _ _ _ _ n k) in Hidecl; eauto.
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
  rewrite <- substl_inds_subst. f_equal.
  now rewrite <- UnivSubst.subst_subst_instance_constr.
  apply Forall_map. unfold compose. eapply Forall_impl; eauto.
  intros. now apply wf_subst_instance_constr.
Qed.

Lemma subst_declared_projection `{checker_flags} Σ c mdecl idecl pdecl n k :
  wf Σ -> Forall Ast.wf n ->
  declared_projection (fst Σ) mdecl idecl c pdecl ->
  on_snd (subst n (S (ind_npars mdecl + k))) pdecl = pdecl.
Proof.
  unfold declared_projection. destruct c as [[i k'] ci].
  intros wfΣ wfn [Hidecl Hcdecl].
  simpl in *.
  pose proof Hidecl. destruct H0 as [Hmdecl Hidecl'].
  eapply lookup_on_global_env in Hmdecl; eauto.
  destruct Hmdecl as [Σ' [wfΣ' ongdecl]].
  red in ongdecl. red in ongdecl.
  eapply nth_error_alli in Hidecl'; eauto.
  apply onProjections in Hidecl'.
  destruct decompose_prod_assum eqn:Heq.
  destruct Hidecl' as [Hpars _].
  destruct Σ. eapply (subst_declared_inductive _ _ _ _ n k) in Hidecl; eauto.
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

Lemma map_vass_map_def g l n k :
  (mapi (fun i (d : def term) => vass (dname d) (lift0 i (dtype d)))
        (map (map_def (subst n k) g) l)) =
  (mapi (fun i d => map_decl (subst n (i + k)) d) (mapi (fun i (d : def term) => vass (dname d) (lift0 i (dtype d))) l)).
Proof.
  rewrite mapi_mapi, mapi_map. apply mapi_ext.
  intros. unfold map_decl, vass; simpl; f_equal.
  rewrite commut_lift_subst_rec. f_equal; lia. lia.
Qed.

Lemma subst_fix_context:
  forall (mfix : list (def term)) n (k : nat),
    fix_context (map (map_def (subst n k) (subst n (#|mfix| + k))) mfix) =
    subst_context n k (fix_context mfix).
Proof.
  intros mfix n k. unfold fix_context.
  rewrite map_vass_map_def, rev_mapi.
  fold (fix_context mfix).
  rewrite (subst_context_alt n k (fix_context mfix)).
  unfold subst_decl. now rewrite mapi_length, fix_context_length.
Qed.

Lemma All_local_env_subst `{checker_flags} (P Q : global_context -> context -> term -> term -> Type) Σ c n k :
  All_local_env Q Σ c ->
  (forall Γ t T,
      Q Σ Γ t T -> P Σ (subst_context n k Γ) (subst n (#|Γ| + k) t) (subst n (#|Γ| + k) T)) ->
  All_local_env P Σ (subst_context n k c).
Proof.
  intros Hq Hf. induction Hq in |- *; try econstructor; eauto;
                  simpl; unfold snoc; rewrite subst_context_snoc; econstructor; eauto.
  simpl. eapply (Hf _ _ (tSort u)). eauto.
Qed.

Lemma subst_destArity ctx t n k :
  Ast.wf t ->
  match destArity ctx t with
  | Some (args, s) =>
    destArity (subst_context n k ctx) (subst n (#|ctx| + k) t) = Some (subst_context n k args, s)
  | None => True
  end.
Proof.
  intros wf; revert ctx.
  induction wf in n, k |- * using Template.Induction.term_wf_forall_list_ind; intros ctx; simpl; trivial.

  - specialize (IHwf0 n k (ctx,, vass n0 t)). unfold snoc in IHwf0; rewrite subst_context_snoc in IHwf0.
    simpl in IHwf0. unfold subst_decl, map_decl in IHwf0. unfold vass in *. simpl in IHwf0.
    destruct destArity. destruct p. simpl in *. auto. exact I.
  - specialize (IHwf1 n k (ctx,, vdef n0 t t0)).
    unfold snoc in IHwf1; rewrite subst_context_snoc in IHwf1.
    unfold vdef, subst_decl, map_decl in *. simpl in *.
    destruct destArity as [[args s]|]. apply IHwf1. exact I.
Qed.

Lemma has_nparams_ex {nass t} :
  has_nparams nass t -> { p & decompose_prod_n_assum [] nass t = Some p }.
Proof.
  unfold has_nparams.
  destruct decompose_prod_n_assum. intros.
  exists p. reflexivity.
  congruence.
Qed.

Lemma decompose_prod_n_assum0 ctx t : decompose_prod_n_assum ctx 0 t = Some (ctx, t).
Proof. destruct t; simpl; reflexivity. Qed.

Lemma wf_strip_outer_cast t : Ast.wf t -> Ast.wf (strip_outer_cast t).
Proof.
  induction t; auto.
  simpl. intros H; now inv H.
Qed.

Lemma strip_outer_cast_tProd_tLetIn_subst t n k :
  match strip_outer_cast t with
  | tProd na A B =>
    strip_outer_cast (subst n k t) = tProd na (subst n k A) (subst n (S k) B)
  | tLetIn na b ty b' =>
    strip_outer_cast (subst n k t) = tLetIn na (subst n k b) (subst n k ty) (subst n (S k) b')
  | _ => True
  end.
Proof.
  induction t; simpl in *; auto.
Qed.

Lemma subst_decompose_prod_n_assum_rec ctx nass t n k ctx' t' :
  decompose_prod_n_assum ctx nass t = Some (ctx', t') ->
  decompose_prod_n_assum (subst_context n k ctx) nass (subst n (length ctx + k) t) =
  Some (subst_context n k ctx', subst n (length ctx' + k) t').
Proof.
  induction nass in n, k, t, ctx, ctx', t' |- *;
    try (rewrite !decompose_prod_n_assum0; intros [= -> ->]; reflexivity);
      (simpl; try congruence);
      try rewrite Nat.sub_diag, Nat.add_0_r; try (eauto; congruence).
  pose proof (strip_outer_cast_tProd_tLetIn_subst t n (#|ctx| + k)) as Hsubst.
  destruct (strip_outer_cast t) eqn:Ht; try congruence; rewrite Hsubst.
  - specialize (IHnass (ctx ,, vass n0 t0_1) t0_2 n k ctx' t').
    unfold snoc in IHnass; rewrite subst_context_snoc in IHnass. apply IHnass.
  - specialize (IHnass (ctx ,, vdef n0 t0_1 t0_2) t0_3 n k ctx' t').
    unfold snoc in IHnass; rewrite subst_context_snoc in IHnass. apply IHnass.
Qed.

Lemma subst_decompose_prod_n_assum nass t n k :
  has_nparams nass t ->
  match decompose_prod_n_assum [] nass t with
  | Some (ctx', t') =>
    decompose_prod_n_assum [] nass (subst n k t) = Some (subst_context n k ctx', subst n (length ctx' + k) t')
  | None => False
  end.
Proof.
  intros Hpars. apply has_nparams_ex in Hpars as [[ctx' t'] Heq].
  rewrite Heq. eapply subst_decompose_prod_n_assum_rec in Heq. apply Heq.
Qed.

Lemma subst_instantiate_params n k npars args t :
  Forall Ast.wf n ->
  forall t', instantiate_params npars args t = Some t' ->
             instantiate_params npars (map (subst n k) args) (subst n k t) = Some (subst n k t').
Proof.
  intros Hn.
  induction npars in args, Hn, t, n, k |- *.
  destruct args; simpl; intros t' [= ->]; reflexivity.

  intros t'. simpl.
  pose proof (strip_outer_cast_tProd_tLetIn_subst t n k) as Hsubst.
  destruct (strip_outer_cast t) eqn:Ht; try congruence; rewrite Hsubst.
  destruct args; simpl; try congruence; auto.
  - intros Ht'. specialize (IHnpars n k args (t0_2 {0 := t0}) Hn t' Ht').
    rewrite <- IHnpars. f_equal.
    unfold subst1. rewrite distr_subst; auto.
  - intros Ht'. specialize (IHnpars n k args (t0_3 {0 := t0_1}) Hn t' Ht').
    rewrite <- IHnpars. f_equal.
    unfold subst1. rewrite distr_subst; auto.
Qed.
Hint Rewrite subst_instantiate_params : subst.

Lemma decompose_prod_n_assum_subst_ind ctx0 ctx1 ctx2 ctx3 n t s t' :
  Forall Ast.wf s ->
  decompose_prod_n_assum (ctx0 ,,, ctx1 ,,, ctx2) n t =
  Some (ctx0 ,,, ctx1 ,,, ctx3, t') ->
  decompose_prod_n_assum (ctx0 ,,, subst_context s 0 ctx2) n (subst s #|ctx2| t) =
  Some (ctx0 ,,, subst_context s 0 ctx3, subst s #|ctx3| t').
Proof.
  induction n in ctx0, ctx1, ctx2, ctx3, t, t' |- *.
  simpl. intros.
  - injection H0. intros <- Heq.
    f_equal.
    unfold app_context in *.
    rewrite !app_assoc in Heq.
    repeat apply app_inv_tail in Heq. subst ctx2. reflexivity.
  - simpl.
    intros.
    pose proof (strip_outer_cast_tProd_tLetIn_subst t s #|ctx2|) as Hsubst.
    destruct (strip_outer_cast t); simpl in *; try discriminate; rewrite Hsubst.
    -- specialize (IHn ctx0 ctx1 (ctx2 ,, vass n0 t0_1) ctx3 t0_2 t' H).
       simpl in *. unfold snoc in H0.
       forward IHn. rewrite H0. reflexivity.
       now rewrite subst_context_snoc0 in IHn.
    -- specialize (IHn ctx0 ctx1 (ctx2 ,, vdef n0 t0_1 t0_2) ctx3 t0_3 t' H).
       simpl in *. unfold snoc in H0.
       forward IHn. rewrite H0. reflexivity.
       now rewrite subst_context_snoc0 in IHn.
Qed.
Close Scope string_scope.

Lemma decompose_prod_n_assum_ctx ctx n t ctx' t' :
  decompose_prod_n_assum ctx n t = Some (ctx', t') -> exists ctx'', ctx' = (ctx ,,, ctx'').
Proof.
  induction n in ctx, t, ctx', t' |- *. simpl. intros [= -> ->]. exists []; eauto.
  simpl.
  destruct (strip_outer_cast t); simpl; try congruence.
  intros H. apply IHn in H as [ctx'' ->].
  exists (ctx'' ++ [vass n0 t0_1]). unfold app_context, snoc.
  rewrite <- app_assoc. reflexivity.
  intros H. apply IHn in H as [ctx'' ->].
  exists (ctx'' ++ [vdef n0 t0_1 t0_2]). unfold app_context, snoc.
  rewrite <- app_assoc. reflexivity.
Qed.

Lemma decompose_prod_n_assum_subst ctx0 ctx1 ctx3 n t s t' :
  Forall Ast.wf s ->
  decompose_prod_n_assum (ctx0 ,,, ctx1) n t = Some (ctx0 ,,, ctx1 ,,, ctx3, t') ->
  decompose_prod_n_assum ctx0 n (subst s 0 t) =
  Some (ctx0 ,,, subst_context s 0 ctx3, subst s #|ctx3| t').
Proof.
  intros.
  pose proof (decompose_prod_n_assum_subst_ind ctx0 ctx1 [] ctx3 n t s t' H).
  simpl in *. specialize (H1 H0). auto.
Qed.

Lemma subst_instantiate_params_none n k npars args t :
  Forall Ast.wf n -> has_nparams npars t -> Forall Ast.wf args -> Ast.wf t ->
  instantiate_params npars args t = None ->
  instantiate_params npars (map (subst n k) args) (subst n k t) = None.
Proof.
  intros Hn Hp Hargs Ht.
  apply has_nparams_ex in Hp as [[ctx' t'] He].
  revert ctx' t' He. generalize (@nil context_decl).
  induction npars in args, Hargs, Hn, t, Ht, n, k |- *.
  destruct args; simpl. discriminate. reflexivity.

  simpl.
  pose proof (strip_outer_cast_tProd_tLetIn_subst t n k) as Hsubst.
  intros l' ctx' t'.
  destruct (strip_outer_cast t) eqn:Hstript; try congruence; try reflexivity; try rewrite Hsubst.
  destruct args; simpl; try congruence; auto.
  - intros Ht'.
    pose proof (decompose_prod_n_assum_ctx _ _ _ _ _ Ht') as [ctx'' ->].
    change (l',, vass n0 t0_1 ,,, ctx'') with (l' ,,, [vass n0 t0_1] ,,, ctx'') in Ht'.
    change (l' ,, vass n0 t0_1) with (l' ,,, [vass n0 t0_1]) in Ht'.
    eapply (decompose_prod_n_assum_subst _ _ _ _ _ [t0]) in Ht'.
    inv Hargs.
    assert (Ast.wf ((subst0 [t0]) t0_2)). apply wf_subst. wf.
    apply wf_strip_outer_cast in Ht. rewrite Hstript in Ht.
    now inv Ht.
    specialize (IHnpars n k args _ Hn H0 H1 _ _ _ Ht').
    unfold subst1 in *.
    intros. specialize (IHnpars H2).
    rewrite <- IHnpars. f_equal.
    now rewrite distr_subst.
    now inv Hargs.
  - intros Ht'.
    pose proof (decompose_prod_n_assum_ctx _ _ _ _ _ Ht') as [ctx'' ->].
    change (l',, vdef n0 t0_1 t0_2 ,,, ctx'') with (l' ,,, [vdef n0 t0_1 t0_2] ,,, ctx'') in Ht'.
    change (l' ,, vdef n0 t0_1 t0_2) with (l' ,,, [vdef n0 t0_1 t0_2]) in Ht'.
    eapply (decompose_prod_n_assum_subst _ _ _ _ _ [t0_1]) in Ht'.
    assert (Ast.wf ((subst0 [t0_1]) t0_3)).
    apply wf_strip_outer_cast in Ht. rewrite Hstript in Ht.
    inv Ht; now apply wf_subst.
    specialize (IHnpars n k args _ Hn Hargs H _ _ _ Ht').
    unfold subst1 in *.
    intros. specialize (IHnpars H0).
    rewrite <- IHnpars. f_equal.
    now rewrite distr_subst.
    apply wf_strip_outer_cast in Ht. rewrite Hstript in Ht.
    now inv Ht.
Qed.

Lemma subst_it_mkProd_or_LetIn n k ctx t :
  subst n k (it_mkProd_or_LetIn ctx t) =
  it_mkProd_or_LetIn (subst_context n k ctx) (subst n (length ctx + k) t).
Proof.
  induction ctx in n, k, t |- *; simpl; try congruence.
  pose (subst_context_snoc n k ctx a). unfold snoc in e. rewrite e. clear e.
  simpl. destruct decl_body. now rewrite IHctx.
  pose (subst_context_snoc n k ctx a). simpl. now rewrite IHctx.
Qed.

Lemma to_extended_list_subst n k c :
  to_extended_list (subst_context n k c) = to_extended_list c.
Proof.
  unfold to_extended_list. generalize 0. generalize (@nil term) at 1 2.
  induction c in n, k |- *; simpl; intros. reflexivity.
  rewrite subst_context_snoc. unfold snoc. simpl.
  destruct a. destruct decl_body. unfold subst_decl, map_decl. simpl.
  now rewrite IHc. simpl. apply IHc.
Qed.

Lemma to_extended_list_map_subst:
  forall n (k : nat) (c : context), to_extended_list c = map (subst n (#|c| + k)) (to_extended_list c).
Proof.
  intros n k c.
  pose proof (to_extended_list_lift_above c).
  symmetry. apply_spec. intros.
  destruct H0. intuition. subst x. simpl.
  destruct (leb_spec_Set (#|c| + k) x0). lia. reflexivity.
Qed.

Lemma subst_types_of_case ind mdecl idecl args u p pty indctx pctx ps btys n k :
  let f ctx := subst n (#|ctx| + k) in
  let f_ctx := subst_context n k in
  Forall Ast.wf n -> Forall Ast.wf args ->
  Ast.wf pty -> Ast.wf (ind_type idecl) ->
  types_of_case ind mdecl idecl args u p pty = Some (indctx, pctx, ps, btys) ->
  types_of_case ind mdecl (map_one_inductive_body (inductive_mind ind) (polymorphic_instance mdecl.(ind_universes))
                                                  (arities_context mdecl.(ind_bodies)) f (inductive_ind ind) idecl)
                (map (f []) args) u (f [] p) (f [] pty) =
  Some (f_ctx indctx, f_ctx pctx, ps, map (on_snd (f [])) btys).
Proof.
  simpl. intros wfn wfargs wfpty wfdecl. simpl.
  unfold types_of_case. simpl.
  pose proof (subst_destArity [] (ind_type idecl) n k wfdecl); trivial. simpl in H.
  unfold subst_context in H. simpl in H. rewrite ind_type_map. simpl.
  destruct destArity as [[ctx s] | ]; try congruence. rewrite H. clear H.
  pose proof (subst_destArity [] pty n k wfpty); trivial. simpl in H.
  unfold subst_context in H. simpl in H.
  destruct destArity as [[ctx' s'] | ]; try congruence.
  rewrite H; clear H.
  assert(forall brs,
         build_branches_type ind mdecl idecl args u p = brs ->
         (build_branches_type ind mdecl
         (map_one_inductive_body (inductive_mind ind) (polymorphic_instance (ind_universes mdecl))
            (arities_context (ind_bodies mdecl)) (fun ctx0 : list context_decl => subst n (#|ctx0| + k))
            (inductive_ind ind) idecl) (map (subst n k) args) u (subst n k p)) =
         map (option_map (on_snd (subst n k))) brs).
  unfold build_branches_type. simpl. intros brs. intros <-.
  rewrite ind_ctors_map.
  rewrite mapi_map, map_mapi. f_equal. extensionality i. extensionality x.
  destruct x as [[id t] arity]. simpl.
  rewrite <- UnivSubst.subst_subst_instance_constr.
  rewrite substl_inds_subst.
  assert (map (UnivSubst.subst_instance_constr u) n = n). admit.
  rewrite H. clear H.
  destruct (instantiate_params _ args) eqn:Heq.
  pose proof (subst_instantiate_params n k _ _ _ wfn _ Heq).
  2:{ eapply subst_instantiate_params_none in Heq.
      rewrite Heq. all:eauto. admit.
      apply wf_subst. apply wf_inds. apply wf_subst_instance_constr. admit. }
  rewrite H.
  destruct (decompose_prod_assum [] t0) eqn:Heq'.
  destruct (decompose_app t1) as [fn arg] eqn:?.
(*   rewrite (decompose_app_subst _ _ _ fn arg); auto. simpl. *)
(*   destruct (chop _ arg) eqn:Heqchop. eapply chop_map in Heqchop. *)
(*   rewrite Heqchop. clear Heqchop. *)
(*   unfold on_snd. simpl. f_equal. *)
(*   rewrite subst_it_mkProd_or_LetIn, !subst_mkApps, map_app; simpl. *)
(*   rewrite !subst_mkApps, !map_app, subst_context_length. *)
(*   rewrite permute_subst by lia. repeat f_equal. *)
(*   now rewrite to_extended_list_subst, <- to_extended_list_map_subst. *)
(*   simpl. reflexivity. *)
(*   specialize (H _ eq_refl). rewrite H. clear H. *)
(*   rewrite map_option_out_map_option_map. *)
(*   destruct (map_option_out (build_branches_type _ _ _ _ _ _)). *)
(*   intros [= -> -> -> <-]. reflexivity. congruence. *)
(* Qed. *)
Admitted.

Hint Unfold subst1 : subst.
Hint Rewrite subst_mkApps distr_subst: subst.

Lemma subs_nth_error `{checker_flags} Σ Γ s Δ decl n t :
  subs Σ Γ s Δ ->
  nth_error Δ n = Some decl ->
  nth_error s n = Some t ->
  match decl_body decl return Type with
  | Some t' => False
  | None =>
    let ty := substl (skipn (S n) s) (decl_type decl) in
    Σ ;;; Γ |- t : ty
  end.
Proof.
  induction 1 in n |- *; simpl; auto; destruct n; simpl; try congruence.
  - intros [= <-]. intros [= ->].
    simpl. exact t1.
  - apply IHX.
Qed.

Lemma red1_tApp_mkApps_l Σ Γ M1 N1 M2 :
  red1 Σ Γ M1 N1 -> red1 Σ Γ (tApp M1 M2) (mkApps N1 M2).
Proof. constructor. auto. Qed.
Lemma mkApp_mkApps f a l : mkApp (mkApps f l) a = mkApps f (l ++ [a]).
Proof.
  destruct l. simpl. reflexivity.
  rewrite <- mkApp_nested. reflexivity.
Qed.

Lemma red1_tApp_mkApp Σ Γ M1 N1 M2 :
  red1 Σ Γ M1 N1 -> red1 Σ Γ (tApp M1 [M2]) (mkApp N1 M2).
Proof.
  intros.
  change (mkApp N1 M2) with (mkApps N1 [M2]).
  apply app_red_l. auto.
Qed.

Lemma mkApp_tApp f u : isApp f = false -> mkApp f u = tApp f [u].
Proof. intros. destruct f; (discriminate || reflexivity). Qed.

Lemma red1_mkApp Σ Γ M1 N1 M2 :
  Ast.wf M1 ->
  red1 Σ Γ M1 N1 -> red1 Σ Γ (mkApp M1 M2) (mkApp N1 M2).
Proof.
  intros wfM1 H.
  destruct (isApp M1) eqn:Heq.
  destruct M1; try discriminate. simpl.
  revert wfM1. inv H. simpl. intros.
  rewrite mkApp_mkApps. constructor.

  intros. inv wfM1. simpl.
  econstructor; eauto.
  clear -H1.
  unfold is_constructor in *.
  destruct (nth_error l narg) eqn:Heq.
  eapply nth_error_app_left in Heq. now rewrite Heq. discriminate.

  intros. rewrite mkApp_mkApps. now constructor.

  intros. simpl.
  constructor. clear -H0. induction H0; constructor; auto.

  rewrite mkApp_tApp; auto.
  now apply red1_tApp_mkApp.
Qed.

Lemma red1_mkApps_l Σ Γ M1 N1 M2 :
  Ast.wf M1 -> Forall Ast.wf M2 ->
  red1 Σ Γ M1 N1 -> red1 Σ Γ (mkApps M1 M2) (mkApps N1 M2).
Proof.
  induction M2 in M1, N1 |- *. simpl; auto.
  intros. specialize (IHM2 (mkApp M1 a) (mkApp N1 a)).
  inv H0.
  forward IHM2. apply wf_mkApp; auto.
  forward IHM2. auto.
  rewrite <- !mkApps_mkApp; auto.
  apply IHM2.
  apply red1_mkApp; auto.
Qed.

Lemma red1_mkApps_r Σ Γ M1 M2 N2 :
  Ast.wf M1 -> Forall Ast.wf M2 ->
  OnOne2 (red1 Σ Γ) M2 N2 -> red1 Σ Γ (mkApps M1 M2) (mkApps M1 N2).
Proof.
  intros. induction H1 in M1, H, H0 |- *.
  inv H0.
  destruct (isApp M1) eqn:Heq. destruct M1; try discriminate.
  simpl. constructor. apply OnOne2_app. constructor. auto.
  rewrite mkApps_tApp; try congruence.
  rewrite mkApps_tApp; try congruence.
  constructor. constructor. auto.
  inv H0.
  specialize (IHOnOne2 (mkApp M1 hd)). forward IHOnOne2.
  apply wf_mkApp; auto. forward IHOnOne2; auto.
  now rewrite !mkApps_mkApp in IHOnOne2.
Qed.

Lemma substitution_red1 `{CF:checker_flags} Σ Γ Γ' Γ'' s M N :
  wf Σ -> Forall Ast.wf s -> subs Σ Γ s Γ' -> wf_local Σ Γ -> Ast.wf M ->
  red1 (fst Σ) (Γ ,,, Γ' ,,, Γ'') M N ->
  red1 (fst Σ) (Γ ,,, subst_context s 0 Γ'') (subst s #|Γ''| M) (subst s #|Γ''| N).
Proof.
  intros wfΣ wfs Hs wfΓ wfM H.
  remember (Γ ,,, Γ' ,,, Γ'') as Γ0. revert Γ Γ' Γ'' HeqΓ0 wfΓ Hs.
  induction H using red1_ind_all in |- *; intros Γ0 Γ' Γ'' HeqΓ0 wfΓ Hs; try subst Γ; simpl;
    autorewrite with subst;
    try solve [  econstructor; try inv wfM; eauto ].

  - unfold subst1. rewrite distr_subst; auto. constructor.
  - unfold subst1. rewrite distr_subst; auto. constructor.

  - pose proof (subst_length _ _ _ _ Hs).
    elim (leb_spec_Set); intros Hn.
    + destruct (nth_error s) eqn:Heq.
      ++ pose proof (nth_error_Some_length Heq).
         rewrite nth_error_app_ge in H by lia.
         rewrite nth_error_app_lt in H by lia.
         destruct nth_error eqn:HΓ'.
         eapply subs_nth_error in Heq; eauto.
         simpl in H. destruct decl_body; try contradiction.
         discriminate. discriminate.
      ++ apply nth_error_None in Heq.
         assert(S i = #|s| + (S (i - #|s|))) by lia.
         rewrite H1. rewrite simpl_subst; try lia.
         econstructor.
         rewrite nth_error_app_ge in H by lia.
         rewrite nth_error_app_ge in H by lia.
         rewrite nth_error_app_ge. 2:(autorewrite with wf; lia).
         rewrite <- H. f_equal. f_equal. autorewrite with wf. lia.
         rewrite !nth_error_app_ge in H by lia.
         destruct nth_error eqn:Hi.
         eapply nth_error_All_local_env in wfΓ. red in wfΓ.
         rewrite Hi in wfΓ. simpl in H.
         destruct c; simpl in H; try discriminate.
         injection H. intros ->. red in wfΓ. cbn in *. apply typing_wf in wfΓ. intuition eauto. eauto.
         eapply typing_wf_local in wfΓ; eauto.
         apply nth_error_Some_length in Hi. lia. discriminate.
    + rewrite nth_error_app_lt in H by lia.
      pose (commut_lift_subst_rec body s (S i) (#|Γ''| - S i) 0).
      assert(eq:(S i + (#|Γ''| - S i)) = #|Γ''|) by lia.
      rewrite eq in e. rewrite <- e by lia.
      constructor.
      rewrite nth_error_app_lt by (autorewrite with wf; lia).
      rewrite nth_error_subst_context.
      unfold subst_decl; now rewrite option_map_decl_body_map_decl, H, Nat.add_0_r.

  - rewrite subst_iota_red.
    constructor.

  - inv wfM. rewrite mkApps_tApp; simpl; auto with wf.
    rewrite mkApps_tApp; simpl; auto with wf.
    eapply red_fix. erewrite subst_unfold_fix; eauto.
    now apply subst_is_constructor.
    inv H3.
    unfold unfold_fix in H.
    destruct nth_error eqn:Heq.
    injection H. intros <- <-.
    eapply nth_error_forall in H5; eauto.
    destruct d as [na b ty]; simpl in *.
    destruct H5 as [_ [_ Hty]].
    destruct ty; try discriminate.
    discriminate.

  - pose proof (subst_declared_constant _ _ _ s #|Γ''| u wfΣ H).
    apply (f_equal cst_body) in H1.
    rewrite <- !map_cst_body in H1. rewrite H0 in H1. simpl in H1.
    injection H1. intros ->.
    econstructor. eauto. eauto.

  - inv wfM.
    simpl. constructor.
    now rewrite nth_error_map, H.

  - constructor.
    inv wfM.
    specialize (IHred1 H1 Γ0 Γ' (Γ'' ,, vass na N) eq_refl).
    now rewrite subst_context_snoc0 in IHred1.

  - constructor.
    inv wfM.
    specialize (IHred1 H2 Γ0 Γ' (Γ'' ,, _) eq_refl).
    now rewrite subst_context_snoc0 in IHred1.

  - inv wfM. constructor.
    induction H; constructor; auto.
    intuition; eauto.
    inv H2. specialize (H3 H4 _ _ _ eq_refl).
    destruct hd, hd'; simpl in *. now eapply H3.
    eapply IHOnOne2. inv H2; eauto.

  - inv wfM.
    specialize (IHred1 H2 _ _ _ eq_refl).
    specialize (IHred1 wfΓ Hs).
    apply red1_mkApps_l. apply wf_subst; auto.
    apply Forall_map; eapply Forall_impl. eauto.
    intros. now apply wf_subst.
    apply IHred1.

  - inv wfM.
    apply red1_mkApps_r; auto with wf.
    apply Forall_map. eapply Forall_impl; eauto. simpl; eauto with wf.
    clear -H H2 H3 wfΓ Hs.
    induction H; constructor; auto.
    inv H3. intuition.
    eapply H4; eauto.
    apply IHOnOne2. inv H3. eauto.

  - inv wfM.
    constructor. specialize (IHred1 H1 _ _ (Γ'' ,, vass na M1) eq_refl).
    now rewrite subst_context_snoc0 in IHred1.

  - inv wfM.
    constructor.
    induction H; constructor; auto.
    inv H0. intuition. eapply H3; eauto.
    apply IHOnOne2. now inv H0.
Qed.

Conjecture eq_universe_refl : forall `{checker_flags} φ u, eq_universe φ u u = true.
Conjecture eq_universe_instance_refl : forall `{checker_flags} φ u, eq_universe_instance φ u u = true.
Conjecture eq_universe_leq_universe : forall `{checker_flags} φ x y,
    eq_universe φ x y = true ->
    leq_universe φ x y = true.

Lemma eq_string_refl x : eq_string x x = true.
Proof. unfold eq_string. destruct string_dec; congruence. Qed.

Lemma eq_ind_refl i : eq_ind i i = true.
Proof.
  destruct i as [mind k].
  unfold eq_ind. now rewrite eq_string_refl, Nat.eqb_refl.
Qed.

Lemma eq_projection_refl i : eq_projection i i = true.
Proof.
  destruct i as [[mind k] p].
  unfold eq_projection.
  now rewrite eq_ind_refl, !Nat.eqb_refl.
Qed.

Lemma eq_term_refl `{checker_flags} φ t : eq_term φ t t = true.
Proof.
  induction t using term_forall_list_ind; simpl; try reflexivity; try discriminate;
    try (merge_Forall; close_Forall; intuition auto);
    try (rewrite ?IHt1, ?IHt2, ?IHt3; reflexivity).

  - apply Nat.eqb_refl.
  - apply eq_string_refl.
  - apply Nat.eqb_refl.
  - unfold eq_evar. rewrite Nat.eqb_refl.
    simpl. induction H0; simpl; auto. now rewrite H0, IHForall.
  - apply eq_universe_refl.
  - rewrite IHt; simpl.
    eapply (Forall_forallb _ _ (fun x => eq_term φ x x)) in H0.
    induction l; simpl; auto.
    simpl in H0. rewrite andb_true_iff in H0. intuition.
    auto.
  - unfold eq_constant. rewrite eq_string_refl.
    apply eq_universe_instance_refl.
  - rewrite eq_ind_refl. apply eq_universe_instance_refl.
  - rewrite eq_ind_refl. rewrite Nat.eqb_refl. apply eq_universe_instance_refl.
  - destruct p. simpl.
    rewrite eq_ind_refl, Nat.eqb_refl, IHt1, IHt2.
    simpl. induction l.
    reflexivity.
    simpl. destruct a. inv H0. simpl in H1. rewrite H1.
    rewrite IHl; auto.
  - now rewrite eq_projection_refl, IHt.
  - rewrite Nat.eqb_refl.
    induction m. reflexivity.
    inv H0. intuition.
    simpl. rewrite H0, H3. simpl. apply H1.
  - rewrite Nat.eqb_refl.
    induction m. reflexivity.
    inv H0. intuition.
    simpl. rewrite H0, H3. simpl. apply H1.
Qed.

Lemma eq_term_leq_term `{checker_flags} φ t u : eq_term φ t u = true -> leq_term φ t u = true.
Proof.
  induction t in u |- * using term_forall_list_ind; simpl; intros; auto; try reflexivity; try discriminate;
    try (merge_Forall; close_Forall; intuition auto);
    try (rewrite ?IHt1, ?IHt2, ?IHt3; reflexivity).

  - destruct u; auto. now apply eq_universe_leq_universe.
  - destruct u; try discriminate.
    rewrite andb_true_iff in *. intuition.
  - destruct u; try discriminate.
    rewrite andb_true_iff in *. intuition.
Qed.

Lemma eq_term_App `{checker_flags} φ f f' :
  eq_term φ f f' = true ->
  isApp f = isApp f'.
Proof.
  destruct f, f'; simpl; try congruence.
  destruct p; congruence.
Qed.

Lemma eq_term_mkApps `{checker_flags} φ f l f' l' :
  eq_term φ f f' = true ->
  forallb2 (eq_term φ) l l' = true ->
  eq_term φ (mkApps f l) (mkApps f' l') = true.
Proof.
  induction l in f, f' |- *; destruct l'; try (simpl; congruence).
  intros.
  destruct (isApp f) eqn:Hf.
  pose (eq_term_App _ _ _ H0). rewrite Hf in e.
  destruct f; try discriminate.
  destruct f'; try discriminate.
  simpl in *.
  rewrite andb_true_iff in *. intuition.
  rewrite forallb2_app; auto.
  simpl. now rewrite H3, H0, H4.

  rewrite !mkApps_tApp; auto. simpl. rewrite H0.
  apply H1.
  pose proof (eq_term_App _ _ _ H0). all:congruence.
Qed.

Lemma leq_term_mkApps `{checker_flags} φ f l f' l' :
  eq_term φ f f' = true ->
  forallb2 (eq_term φ) l l' = true ->
  leq_term φ (mkApps f l) (mkApps f' l') = true.
Proof.
  induction l in f, f' |- *; destruct l'; try (simpl; congruence).
  intros. simpl. apply eq_term_leq_term. auto.
  intros.
  destruct (isApp f) eqn:Hf.
  pose (eq_term_App _ _ _ H0). rewrite Hf in e.
  destruct f; try discriminate.
  destruct f'; try discriminate.
  simpl in *.
  rewrite andb_true_iff in *. intuition.
  rewrite forallb2_app; auto.
  simpl. now rewrite H3, H0, H4.

  rewrite !mkApps_tApp; auto. simpl. rewrite H0.
  apply H1.
  pose (eq_term_App _ _ _ H0). all:congruence.
Qed.

Lemma subst_eq_term `{checker_flags} ϕ n k T U :
  eq_term ϕ T U = true ->
  eq_term ϕ (subst n k T) (subst n k U) = true.
Proof.
  intros Hleq.
  induction T in n, k, U, Hleq |- * using term_forall_list_ind; intros;
    destruct U; try discriminate;
  try solve [simpl; auto]; try
                             (destruct (mkApps_trans_wf _ _ H0) as [U' [V' ->]]; reflexivity);
  simpl in *; revert Hleq; try rewrite !andb_true_iff in *; intuition auto;
    try (merge_Forall; close_Forall; intuition auto).

  - intros.
    apply Nat.eqb_eq in Hleq. subst.
    destruct (leb_spec_Set k n1).
    destruct nth_error eqn:Heq. apply eq_term_refl.
    apply eq_term_refl.
    apply eq_term_refl.

  - apply eq_term_mkApps. eauto. eauto.
    merge_Forall. eapply Forall2_impl; eauto.
    simpl; intros; intuition auto.

  - destruct p. destruct Nat.leb. discriminate. discriminate.
  - destruct p. discriminate.
  - destruct p, p0. rewrite !andb_true_iff in *. intuition auto.
    red in H0. merge_Forall. close_Forall. intuition auto. destruct y. simpl. auto.
  - rewrite !andb_true_iff in *.
    destruct x, y; simpl in *; intuition auto.
    assert (#|m| = #|m0|). clear -H2. induction H2; simpl; auto. rewrite H4. auto.
  - rewrite !andb_true_iff in *.
    destruct x, y; simpl in *; intuition auto.
    assert (#|m| = #|m0|). clear -H2. induction H2; simpl; auto. rewrite H4. auto.
Qed.

Lemma subst_leq_term `{checker_flags} ϕ n k T U :
  leq_term ϕ T U = true ->
  leq_term ϕ (subst n k T) (subst n k U) = true.
Proof.
  intros Hleq.
  induction T in n, k, U, Hleq |- * using term_forall_list_ind; intros;
    destruct U; try discriminate;
  try solve [simpl; auto]; try
                             (destruct (mkApps_trans_wf _ _ H0) as [U' [V' ->]]; reflexivity);
  simpl in *; revert Hleq; try destruct p, p0; try rewrite !andb_true_iff in *;
    intuition auto using subst_eq_term;
    try (merge_Forall; close_Forall; intuition eauto using subst_eq_term).

  - apply Nat.eqb_eq in Hleq. subst.
    destruct Nat.leb; simpl. destruct nth_error.
    eapply eq_term_leq_term. apply eq_term_refl. simpl.
    apply Nat.eqb_refl. apply Nat.eqb_refl.
  - apply leq_term_mkApps.
    now apply subst_eq_term.
    apply forallb2_forallb2; auto using subst_eq_term.
  - destruct p. discriminate.
  - destruct p; discriminate.
  - destruct y. simpl. auto using subst_eq_term.
  - rewrite !andb_true_iff in *.
    destruct x, y; simpl in *; intuition auto using subst_eq_term.
    assert (#|m| = #|m0|). clear -H2. induction H2; simpl; auto. rewrite H4.
    auto using subst_eq_term.
  - rewrite !andb_true_iff in *.
    destruct x, y; simpl in *; intuition auto using subst_eq_term.
    assert (#|m| = #|m0|). clear -H2. induction H2; simpl; auto. rewrite H4.
    auto using subst_eq_term.
Qed.

Lemma subst_eq_context `{checker_flags} φ l l' n k :
  eq_context φ l l' = true ->
  eq_context φ (subst_context n k l) (subst_context n k l') = true.
Proof.
  induction l in l', n, k |- *; intros; destruct l'; rewrite ?subst_context_snoc;
    try (discriminate || reflexivity).
  simpl in *. rewrite andb_true_iff in *.
  intuition. unfold eq_context in H2. apply forallb2_length in H2. rewrite <- H2.
  destruct a, c; try congruence.
  unfold eq_decl in *. simpl.
  destruct decl_body, decl_body0; simpl in *; try congruence.
  simpl in *. rewrite andb_true_iff in *.
  intuition auto using subst_eq_term.
  intuition auto using subst_eq_term.
Qed.

Lemma subst_check_correct_arity:
  forall (cf : checker_flags) (Σ : global_context) (ind : inductive) (u : universe_instance)
         (npar : nat) (args : list term) (idecl : one_inductive_body)
         (indctx pctx : list context_decl) s k,
    check_correct_arity (snd Σ) idecl ind u indctx (firstn npar args) pctx = true ->
    check_correct_arity
      (snd Σ) idecl ind u (subst_context s k indctx) (firstn npar (map (subst s k) args))
      (subst_context s k pctx) = true.
Proof.
  intros cf Σ ind u npar args idecl indctx pctx s k.
  unfold check_correct_arity.
  destruct pctx in indctx |- *. simpl; try congruence. simpl.
  rewrite subst_context_snoc. simpl.
  unfold eq_context.
  rewrite !andb_true_iff. intros.
  destruct H. split.
  destruct c. destruct decl_body; try discriminate.
  unfold eq_decl in *. simpl in *.
  assert (#|indctx| = #|pctx|) by now eapply forallb2_length in H0.
  rewrite <- H1.
  clear H0.
  eapply (subst_eq_term _ s (#|indctx| + k)) in H.
  rewrite subst_mkApps, map_app in H. simpl in H.
  rewrite firstn_map. rewrite to_extended_list_subst.
  erewrite <- (to_extended_list_map_subst s) in H.
  rewrite <- H. f_equal. f_equal. f_equal. rewrite subst_context_length.
  rewrite !map_map_compose. apply map_ext.
  intros. unfold compose. now rewrite commut_lift_subst_rec.
  eapply subst_eq_context in H0. eapply H0.
Qed.

Lemma subs_wf `{checker_flags} Σ Γ s Δ : wf Σ -> subs Σ Γ s Δ -> Forall Ast.wf s.
Proof.
  induction 2; constructor.
  apply typing_wf in t0; intuition auto with wf.
  eapply typing_wf_local in t0; eauto.
  auto.
Qed.

Lemma wf_red1_wf `{checker_flags} Σ Γ M N : wf Σ -> wf_local Σ Γ -> Ast.wf M -> red1 (fst Σ) Γ M N -> Ast.wf N.
Proof.
  intros wfΣ wfΓ wfM Hr.
  apply wf_red1 in Hr; eauto.
  apply typing_wf_sigma; auto.
  apply typing_all_wf_decl in wfΓ; eauto.
  eapply Forall_impl; eauto.
  intros x Hx. red in Hx. destruct decl_body; intuition.
Qed.

(** The cumulativity relation is substitutive, yay! *)

Lemma substitution_cumul `{CF:checker_flags} Σ Γ Γ' Γ'' s M N :
  wf Σ -> wf_local Σ (Γ ,,, Γ' ,,, Γ'') -> subs Σ Γ s Γ' -> Ast.wf M -> Ast.wf N ->
  Σ ;;; Γ ,,, Γ' ,,, Γ'' |- M <= N ->
  Σ ;;; Γ ,,, subst_context s 0 Γ'' |- subst s #|Γ''| M <= subst s #|Γ''| N.
Proof.
  intros wfΣ wfΓ Hs wfM wfN. induction 1.
  constructor.
  - now apply subst_leq_term.
  - pose proof H.
    apply wf_red1_wf in H1; eauto.
    eapply substitution_red1 in H. 4:eauto. all:auto.
    econstructor 2; eauto.
    eauto using subs_wf.
    eauto with wf.
  - pose proof H0.
    apply wf_red1_wf in H1; eauto.
    eapply substitution_red1 in H0. 4:eauto.
    all:eauto using subs_wf with wf.
    now econstructor 3.
Qed.

Lemma simpl_subst_k (N : list term) (M : term) :
  Ast.wf M -> forall k p, p = #|N| -> subst N k (lift p k M) = M.
Proof.
  intros. subst p. rewrite <- (Nat.add_0_r #|N|).
  rewrite simpl_subst_rec, lift0_id; auto. Qed.

Lemma subst_app_decomp l l' k t :
  Ast.wf t -> Forall Ast.wf l ->
  subst (l ++ l') k t = subst l' k (subst (List.map (lift0 (length l')) l) k t).
Proof.
  intros wft wfl.
  induction wft in k |- * using term_wf_forall_list_ind; simpl; auto;
    rewrite ?subst_mkApps;
    try (f_equal; rewrite ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length;
         eauto; apply_spec; eauto).

  - destruct (leb_spec_Set k n).
    elim nth_error_spec; rewrite app_length. intros a Heq Hl.
    elim nth_error_spec; rewrite map_length. intros a' Heq' Hl'.
    -- rewrite nth_error_map in Heq'. rewrite AstUtils.nth_error_app_lt in Heq by lia.
       rewrite Heq in Heq'. simpl in Heq'. injection Heq'. intros <-.
       rewrite permute_lift, Nat.add_0_r by lia.
       rewrite simpl_subst_k; auto. apply wf_lift.
       eapply nth_error_forall in Heq; eauto.
    -- intros Hnk. simpl.
       rewrite AstUtils.nth_error_app_ge in Heq by lia.
       elim leb_spec_Set; try lia. intros Hk.
       replace (n - #|l| - k) with (n - k - #|l|) by lia.
       now rewrite Heq.
    -- intros Hl.
       elim nth_error_spec; rewrite map_length.
       --- intros a Heq' Hnk. lia.
       --- intros Hl'. simpl.
           elim leb_spec_Set. intros Hk.
           elim nth_error_spec. intros a Heq'' Hnl. lia.
           intros Hl'n. f_equal. lia.
           lia.
    -- simpl.
       elim leb_spec_Set. intros. lia.
       reflexivity.
Qed.

Require Import Weakening.

Lemma All_local_env_wf_decl:
  forall (H : checker_flags) Σ (Γ : context),
    Forall wf_decl Γ -> All_local_env wf_decl_pred Σ Γ.
Proof.
  intros H Σ Γ X.
  induction Γ in X |- *.
  - constructor; eauto.
  - destruct a as [na [body|] ty].
    constructor. apply IHΓ. inv X; eauto.
    red. inv X. eauto.
    eapply (localenv_cons_abs _ _ _ _ _ (Universe.make Level.lProp)).
    apply IHΓ. inv X; eauto.
    red. inv X. red in H0. intuition eauto. constructor.
Qed.

Lemma refine_type `{checker_flags} Σ Γ t T U : Σ ;;; Γ |- t : T -> T = U -> Σ ;;; Γ |- t : U.
Proof. now intros Ht ->. Qed.

Lemma invert_type_App `{checker_flags} Σ Γ f u T :
  Σ ;;; Γ |- tApp f u : T ->
  { T' : term & { U' & ((Σ ;;; Γ |- f : T') * typing_spine Σ Γ T' u U' *
                        (isApp f <> true) * (u <> []) *
                        (Σ ;;; Γ |- U' <= T))%type } }.
Proof.
  intros Hty.
  dependent induction Hty.
  exists t_ty, t'. intuition.
  specialize (IHHty1 _ _ eq_refl) as [T' [U' [H' H'']]].
  exists T', U'. split; auto.
  eapply cumul_trans; eauto.
Qed.

Lemma type_mkApp `{checker_flags} Σ Γ f u T T' :
  Σ ;;; Γ |- f : T ->
  typing_spine Σ Γ T [u] T' ->
  Σ ;;; Γ |- mkApp f u : T'.
Proof.
  intros Hf Hu. inv Hu.
  simpl. destruct (isApp f) eqn:Happ.
  destruct f; try discriminate. simpl.
  eapply invert_type_App in Hf.
  destruct Hf as (T'' & U' & (((Hf & HU) & Happf) & Hunil) & Hcumul).
  eapply type_App; eauto. intro. apply Hunil.
  destruct l; simpl in *; congruence.
  inv X1. clear Happ Hf Hunil.
  induction HU. simpl. econstructor; eauto.
  eapply cumul_trans; eauto.
  econstructor. econstructor. eapply t. eauto. eauto.
  apply IHHU; eauto.
  rewrite mkApp_tApp; eauto.
  econstructor; eauto. rewrite Happ; auto. congruence.
  econstructor; eauto.
Qed.

Lemma type_mkApps `{checker_flags} Σ Γ f u T T' :
  Σ ;;; Γ |- f : T ->
  typing_spine Σ Γ T u T' ->
  Σ ;;; Γ |- mkApps f u : T'.
Proof.
  intros Hf Hu. induction Hu in f, Hf |- *. auto.
  rewrite <- mkApps_mkApp.
  eapply IHHu. eapply type_mkApp. eauto.
  econstructor; eauto. constructor.
Qed.

Lemma snd_on_snd {A B C} (f : B -> C) (p : A * B) : snd (on_snd f p) = f (snd p).
Proof. destruct p; reflexivity. Qed.

Lemma isLambda_subst (s : list term) k (bod : term) :
  isLambda bod = true -> isLambda (subst s k bod) = true.
Proof.
  intros. destruct bod; try discriminate. reflexivity.
Qed.

Theorem substitution `{checker_flags} Σ Γ Γ' s Δ (t : term) T :
  wf Σ -> subs Σ Γ s Γ' ->
  Σ ;;; Γ ,,, Γ' ,,, Δ |- t : T ->
  wf_local Σ (Γ ,,, subst_context s 0 Δ) ->
  Σ ;;; Γ ,,, subst_context s 0 Δ |- subst s #|Δ| t : subst s #|Δ| T.
Proof.
  intros HΣ Hs Ht.
  pose proof (typing_wf_local HΣ Ht).
  generalize_eqs Ht. intros eqw. rewrite <- eqw in X.
  revert Γ Γ' Δ s Hs eqw.
  revert Σ HΣ Γ0 X t T Ht.
  apply (typing_ind_env (fun Σ Γ0 t T =>
  forall (Γ Γ' Δ : context) (s : list term)
    (sub : subs Σ Γ s Γ') (eqΓ0 : Γ0 = Γ ,,, Γ' ,,, Δ)
    (wfsubs : wf_local Σ (Γ ,,, subst_context s 0 Δ)),
    Σ ;;; Γ ,,, subst_context s 0 Δ |- subst s #|Δ| t : subst s #|Δ| T));
    intros Σ wfΣ Γ0 wfΓ0; intros; subst Γ0; simpl in *; try solve [econstructor; eauto].

  - assert (wfcdecl : Ast.wf (decl_type decl)).
    { apply typing_all_wf_decl in X; eauto.
      eapply (nth_error_forall) in X; eauto. red in X. intuition. }
    elim (leb_spec_Set); intros Hn.
    elim nth_error_spec.
    + intros x Heq Hlt.
      pose proof (subst_length _ _ _ _ sub).
      rewrite Typing.nth_error_app_ge in H0 by lia.
      rewrite Typing.nth_error_app_lt in H0 by lia.
      eapply subs_nth_error in Heq; eauto.
      destruct decl_body; try contradiction.
      cbn -[skipn] in Heq.
      eapply refine_type.
      eapply (weakening _ _ (subst_context s 0 Δ)) in Heq; eauto with wf.
      rewrite subst_context_length in Heq. eapply Heq.
      unfold substl. rewrite commut_lift_subst_rec by lia.
      rewrite Nat.add_0_r.
      rewrite <- (firstn_skipn (S (n - #|Δ|)) s) at 2.
      rewrite subst_app_decomp. f_equal.
      replace (S n) with ((S n - #|Δ|) + #|Δ|) by lia.
      assert (eq:#|(map (lift0 #|skipn (S (n - #|Δ|)) s|) (firstn (S (n - #|Δ|)) s))| = S n - #|Δ|).
      rewrite map_length. rewrite firstn_length by lia. lia.
      rewrite <- eq. rewrite simpl_subst_rec; auto; try lia.
      auto with wf. eapply subs_wf in sub; eauto.
      now apply Forall_firstn.

    + intros Hs.
      pose proof (subst_length _ _ _ _ sub).
      rewrite H1 in Hs.
      assert (S n = #|s| + (S (n - #|s|))) by lia.
      rewrite H2. rewrite simpl_subst; auto; try lia.
      constructor; auto.
      rewrite nth_error_app_ge; rewrite subst_context_length.
      rewrite 2!nth_error_app_ge in H0 by lia.
      rewrite <- H0. f_equal. lia.
      lia.

    + eapply subs_nth_error_lt in sub; eauto.
      rewrite H0 in sub. simpl in sub.
      eapply refine_type. constructor; eauto.
      rewrite <- map_decl_type.
      rewrite commut_lift_subst_rec by lia.
      f_equal. lia.

  - econstructor; auto. eapply X0; eauto.
    specialize (X0 Γ Γ' Δ s sub eq_refl wfsubs).
    specialize (X2 Γ Γ' (Δ,, vass n t) s sub eq_refl).
    rewrite subst_context_snoc0 in X2. forward X2.
    now econstructor; simpl; eauto.
    eapply X2.

  - econstructor; auto. eapply X0; eauto.
    specialize (X0 Γ Γ' Δ s sub eq_refl wfsubs).
    specialize (X2 Γ Γ' (Δ,, vass n t) s sub eq_refl).
    rewrite subst_context_snoc0 in X2. forward X2.
    now econstructor; simpl; eauto.
    eapply X2.

  - specialize (X0 Γ Γ' Δ s sub eq_refl wfsubs).
    specialize (X2 Γ Γ' Δ s sub eq_refl wfsubs).
    specialize (X4 Γ Γ' (Δ,, vdef n b b_ty) s sub eq_refl).
    rewrite subst_context_snoc0 in X4. forward X4.
    now econstructor; simpl; eauto.
    econstructor; eauto.

  - specialize (X0 Γ Γ' Δ s0 sub eq_refl wfsubs).
    eapply type_mkApps; eauto.
    eapply typing_wf in X; eauto. destruct X.
    clear X0 H2 H0 H1.
    induction X1; try constructor; eauto.
    specialize (p Γ Γ' Δ s0 sub eq_refl wfsubs).
    specialize (p0 Γ Γ' Δ s0 sub eq_refl wfsubs).
    simpl in *. econstructor; eauto.
    change (tProd na (subst s0 #|Δ| A) (subst s0 (S #|Δ|) B))
      with (subst s0 #|Δ| (tProd na A B)).
    eapply substitution_cumul; eauto.
    eapply typing_wf in typrod; eauto. intuition.
    unfold subst1 in IHX1 |- *. rewrite distr_subst in IHX1.
    apply IHX1.
    apply wf_subst. constructor; auto.
    now apply typing_wf in ty.
    apply typing_wf in typrod; eauto.
    intuition. now inv H0.
    eauto using subs_wf.

  - eapply refine_type. constructor; eauto.
    rewrite !map_cst_type. eapply subst_declared_constant in H0 as ->; eauto.

  - eapply refine_type. econstructor; eauto.
    assert (s = map (UnivSubst.subst_instance_constr u) s). admit.
    rewrite H1.
    rewrite UnivSubst.subst_subst_instance_constr. f_equal.
    eapply subst_declared_inductive in isdecl.
    erewrite <- (ind_type_map (fun Γ t => subst s (#|Γ| + #|Δ|) t)).
    f_equal. symmetry. apply isdecl. eauto.

  - eapply refine_type. econstructor; eauto.
    assert (s = map (UnivSubst.subst_instance_constr u) s). admit.
    rewrite H1.
    erewrite (subst_declared_constructor _ (ind, i) u mdecl idecl cdecl _ _ wfΣ); eauto.
    (* eauto with wf. loops!*)
    eauto using subs_wf.

  - rewrite subst_mkApps, map_app, map_skipn.
    specialize (X1 Γ Γ' Δ s sub eq_refl wfsubs).
    specialize (X4 Γ Γ' Δ s sub eq_refl wfsubs).
    specialize (X2 Γ Γ' Δ s sub eq_refl wfsubs).
    simpl. econstructor.
    5:{ eapply subst_types_of_case in H3.
        simpl in H3. subst pars. rewrite firstn_map. eapply H3; eauto.
        -- now apply subs_wf in sub.
        -- subst pars. eapply Forall_firstn.
           apply typing_wf in X3 as [_ X3]; eauto.
           now apply wf_mkApps_inv in X3.
        -- eapply typing_wf in X0; wf.
        -- eapply typing_wf_sigma in wfΣ.
           red in H0.
           eapply (lookup_on_global_env _ _ _ _ wfΣ) in H0 as [Σ' [wfΣ' H0]]; eauto.
           destruct H1.
           eapply (nth_error_alli H6) in H0. apply onArity in H0; red in H0. wf. }
    -- eauto.
    -- erewrite subst_declared_inductive; eauto.
    -- auto.
    -- auto.
    -- revert H4. subst pars.
       erewrite subst_declared_inductive; eauto.
       apply subst_check_correct_arity.
    -- destruct idecl; simpl in *; auto.
       destruct decompose_prod_assum. auto.
    -- now rewrite !subst_mkApps in X4.
    -- eapply Forall2_map. close_Forall. intros; intuition eauto.
       destruct x, y; simpl in *. eauto.

  - unfold substl. simpl.
    specialize (X1 Γ Γ' Δ s sub eq_refl wfsubs).
    eapply refine_type. econstructor.
    eauto.
    rewrite subst_mkApps in X1. eauto.
    rewrite map_length; eauto.

    rewrite <- (Nat.add_0_l #|Δ|).
    pose proof (subs_wf _ _ _ _ wfΣ sub).
    erewrite distr_subst_rec. simpl.
    rewrite map_rev. subst ty.
    assert (eqs: s = map (UnivSubst.subst_instance_constr u) s). admit.
    rewrite eqs.
    rewrite List.rev_length, UnivSubst.subst_subst_instance_constr.
    rewrite <- eqs.
    unfold substl. f_equal. f_equal.
    eapply subst_declared_projection in isdecl. 2:eauto.
    rewrite <- isdecl at 1.
    rewrite snd_on_snd. rewrite <- H0. reflexivity. all:eauto.

  - assert (wf_local Σ (Γ ,,, subst_context s 0 Δ ,,, subst_context s #|Δ| (fix_context mfix))).
    subst types.
    apply All_local_env_app in X as [X Hfixc].
    apply All_local_env_app_inv. intuition.
    revert Hfixc. clear X0 X H0.
    induction 1; simpl; auto.
    + destruct t0 as [Ht IHt].
      specialize (IHt Γ Γ' (Δ ,,, Γ0) s sub). forward IHt. now rewrite app_context_assoc.
      rewrite app_context_length, subst_context_app, app_context_assoc, Nat.add_0_r in IHt.
      unfold snoc; rewrite subst_context_snoc; econstructor; auto;
        apply IHt; apply All_local_env_app_inv; intuition.
    + destruct t0 as [Ht IHt].
       specialize (IHt Γ Γ' (Δ ,,, Γ0) s sub). forward IHt. now rewrite app_context_assoc.
       rewrite app_context_length, subst_context_app, app_context_assoc, Nat.add_0_r in IHt.
       unfold snoc; rewrite subst_context_snoc; econstructor; auto;
       apply IHt; apply All_local_env_app_inv; intuition.
    + erewrite map_dtype. eapply type_Fix.
      * rewrite nth_error_map, H0. reflexivity.
      * now rewrite subst_fix_context.
      * rewrite subst_fix_context.
        apply All_map.
        clear X. eapply All_impl; eauto.
        clear X0. unfold compose; simpl; intros [na ty bod] [[Htyd Hlam] IH].
        simpl in *. intuition.
        specialize (IH Γ Γ' (Δ ,,, fix_context mfix) s sub).
        forward IH by now rewrite app_context_assoc.
        rewrite subst_context_app in IH.
        subst types.
        rewrite !app_context_assoc, Nat.add_0_r, !app_context_length, fix_context_length in IH.
        specialize (IH X1).
        rewrite subst_context_length, fix_context_length.
        now rewrite commut_lift_subst_rec.
        now apply isLambda_subst.


  - assert (wf_local Σ (Γ ,,, subst_context s 0 Δ ,,, subst_context s #|Δ| (fix_context mfix))).
    subst types.
    apply All_local_env_app in X as [X Hfixc].
    apply All_local_env_app_inv. intuition.
    revert Hfixc. clear X0 X H0.
    induction 1; simpl; auto.
    + destruct t0 as [Ht IHt].
      specialize (IHt Γ Γ' (Δ ,,, Γ0) s sub). forward IHt. now rewrite app_context_assoc.
      rewrite app_context_length, subst_context_app, app_context_assoc, Nat.add_0_r in IHt.
      unfold snoc; rewrite subst_context_snoc; econstructor; auto;
        apply IHt; apply All_local_env_app_inv; intuition.
    + destruct t0 as [Ht IHt].
       specialize (IHt Γ Γ' (Δ ,,, Γ0) s sub). forward IHt. now rewrite app_context_assoc.
       rewrite app_context_length, subst_context_app, app_context_assoc, Nat.add_0_r in IHt.
       unfold snoc; rewrite subst_context_snoc; econstructor; auto;
       apply IHt; apply All_local_env_app_inv; intuition.
    + erewrite map_dtype. eapply type_CoFix.
      * rewrite nth_error_map, H0. reflexivity.
      * now rewrite subst_fix_context.
      * rewrite subst_fix_context.
        apply All_map.
        clear X. eapply All_impl; eauto.
        clear X0. unfold compose; simpl; intros [na ty bod] [Htyd IH].
        simpl in *. intuition.
        specialize (IH Γ Γ' (Δ ,,, fix_context mfix) s sub).
        forward IH by now rewrite app_context_assoc.
        rewrite subst_context_app in IH.
        subst types.
        rewrite !app_context_assoc, Nat.add_0_r, !app_context_length, fix_context_length in IH.
        specialize (IH X1).
        rewrite subst_context_length, fix_context_length.
        now rewrite commut_lift_subst_rec.

  - econstructor; eauto.
    eapply substitution_cumul; eauto.
    now eapply typing_wf in X.
    now eapply typing_wf in X1.
Admitted. (* 3 subgoals remaining: univ substs *)

Theorem substitution_alt `{checker_flags} Σ Γ Γ' s Δ (t : term) T :
  wf Σ -> subs Σ Γ s Γ' ->
  Σ ;;; Γ ,,, Γ' ,,, Δ |- t : T ->
  Σ ;;; Γ ,,, subst_context s 0 Δ |- subst s #|Δ| t : subst s #|Δ| T.
Proof.
  intros.
  eapply substitution; eauto.
  eapply All_local_env_app_inv.
  apply typing_wf_local in X1; eauto.
  apply All_local_env_app in X1 as [X1 X2].
  apply All_local_env_app in X1. intuition.
  induction X2; simpl; rewrite ?subst_context_snoc0; econstructor; eauto.
  eapply substitution in t1; simpl in *; eauto.
  eapply All_local_env_app_inv; intuition.
  eapply substitution in t1; simpl in *; eauto.
  eapply All_local_env_app_inv; intuition.
Qed.

Lemma substitution0 `{checker_flags} Σ Γ n u U (t : term) T :
  wf Σ ->
  Σ ;;; Γ ,, vass n U |- t : T -> Σ ;;; Γ |- u : U ->
  Σ ;;; Γ |- t {0 := u} : T {0 := u}.
Proof.
  intros HΣ Ht Hu.
  assert (wfΓ : wf_local Σ Γ).
  apply typing_wf_local in Hu; eauto.
  pose proof (substitution_alt Σ Γ [vass n U] [u] [] t T HΣ) as thm.
  forward thm. constructor. constructor. unfold substl. rewrite subst_empty; auto.
  apply typing_wf in Hu; intuition.
  now apply (thm Ht).
Qed.