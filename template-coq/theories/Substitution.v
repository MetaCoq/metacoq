(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega Lia.
From Template Require Import config utils Ast AstUtils Induction utils LiftSubst UnivSubst Typing.
From Template Require Import WeakeningEnv Closed.

(** * Substitution lemmas for typing derivations. *)

Set Asymmetric Patterns.

Generalizable Variables Σ Γ t T.

Definition subst_decl s k (d : context_decl) := map_decl (subst s k) d.

Definition subst_context n k (Γ : context) : context :=
  fold_context (fun k' => subst n (k' + k)) Γ.

Definition wf_decl_pred : global_context -> context -> term -> term -> Type :=
  (fun _ _ t T => Ast.wf t /\ Ast.wf T).

Lemma subst_decl0 Σ Γ k d : on_local_decl wf_decl_pred Σ Γ d -> map_decl (subst [] k) d = d.
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
  forall (Σ : global_context) (a : context_decl) (Γ : list context_decl)
         (X : All_local_env wf_decl_pred Σ (a :: Γ)),
    on_local_decl wf_decl_pred Σ Γ a * All_local_env wf_decl_pred Σ Γ.
Proof.
  intros Σ a Γ X.
  inv X; intuition; red; simpl; eauto.
Qed.

Lemma subst0_context Σ k Γ : All_local_env wf_decl_pred Σ Γ -> subst_context [] k Γ = Γ.
Proof.
  unfold subst_context, fold_context.
  rewrite rev_mapi. rewrite List.rev_involutive.
  unfold mapi. generalize 0. generalize #|List.rev Γ|.
  induction Γ; intros; simpl; trivial.
  eapply All_local_env_wf_decl_inv in X as [Ha HΓ].
  erewrite subst_decl0; f_equal; eauto.
Qed.

Lemma fold_context_length f Γ : #|fold_context f Γ| = #|Γ|.
Proof.
  unfold fold_context. now rewrite !List.rev_length, mapi_length, List.rev_length.
Qed.

Lemma subst_context_length s k Γ : #|subst_context s k Γ| = #|Γ|.
Proof.
  unfold subst_context. apply fold_context_length.
Qed.
Hint Rewrite subst_context_length : subst.

Lemma subst_context_snoc s k Γ d : subst_context s k (d :: Γ) = subst_context s k Γ ,, subst_decl s (#|Γ| + k) d.
Proof.
  unfold subst_context, fold_context.
  rewrite !rev_mapi, !rev_involutive. unfold mapi; rewrite mapi_rec_eqn.
  unfold snoc. f_equal. now rewrite Nat.sub_0_r, List.rev_length.
  rewrite mapi_rec_Sk. simpl. apply mapi_rec_ext. intros.
  rewrite app_length, !List.rev_length. simpl. f_equal. f_equal. lia.
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
  unfold subst_context, fold_context. rewrite rev_mapi. rewrite List.rev_involutive.
  apply mapi_ext. intros. f_equal. now rewrite List.rev_length.
Qed.

Lemma subst_context_app s k Γ Δ :
  subst_context s k (Γ ,,, Δ) = subst_context s k Γ ,,, subst_context s (#|Γ| + k) Δ.
Proof.
  unfold subst_context, fold_context, app_context.
  rewrite List.rev_app_distr.
  rewrite mapi_app. rewrite <- List.rev_app_distr. f_equal. f_equal.
  apply mapi_ext. intros. f_equal. rewrite List.rev_length. f_equal. lia.
Qed.

Lemma nth_error_subst_context (Γ' : context) s (v : nat) k :
    nth_error (subst_context s k Γ') v =
    option_map (subst_decl s (#|Γ'| - S v + k)) (nth_error Γ' v).
Proof.
  induction Γ' in v |- *; intros.
  - simpl. unfold subst_context, fold_context; simpl; rewrite nth_error_nil. easy.
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
  Σ ;;; Γ |- t : T -> subst n k T = T /\ subst n k t = t.
Proof.
  intros wfΣ wfΓ Hk Hty.
  pose proof (typing_wf _ wfΣ _ wfΓ _ _ Hty) as [wft wfT].
  apply typecheck_closed in Hty; eauto.
  destruct Hty as [_ Hcl].
  rewrite andb_true_iff in Hcl. destruct Hcl as [clb clty].
  pose proof (closed_upwards _ _ clb k).
  simpl in *. forward H0 by lia.
  pose proof (closed_upwards _ _ clty k).
  simpl in *. forward H1 by lia.
  apply (subst_closedn n) in H0; apply (subst_closedn n) in H1; auto.
Qed.

Lemma subst_wf_local `{checker_flags} Σ Γ n k : wf Σ -> wf_local Σ Γ -> subst_context n k Γ = Γ.
Proof.
  intros wfΣ.
  induction 1; auto; unfold subst_context, snoc; rewrite fold_context_snoc0; auto; unfold snoc;
    f_equal; auto; unfold map_decl; simpl. unfold vass. simpl. f_equal.
  eapply typed_subst; eauto. lia. unfold vdef.
  f_equal. f_equal. eapply typed_subst; eauto. lia.
  eapply typed_subst in t0 as [Ht HT]; eauto. lia.
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
  2:apply (env_prop_sigma _ typecheck_closed _ X).
  2:apply (env_prop_sigma _ typing_wf_gen _ X).
  red; intros. unfold lift_typing in *. destruct b; intuition auto with wf.
  destruct X0 as [s0 Hs0]. exists s0. intuition auto with wf.
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
  map_mutual_inductive_body mind (fun k' => subst n (k' + k)) m.

Lemma subst_declared_minductive `{checker_flags} Σ cst decl n k :
  wf Σ ->
  declared_minductive (fst Σ) cst decl ->
  subst_mutual_inductive_body n k cst decl = decl.
Proof.
  unfold declared_minductive.
  intros.
  eapply lookup_on_global_env in H0; eauto.
  destruct H0 as [Σ' [wfΣ' decl']].
  red in decl'.
  destruct decl. simpl in *. f_equal.
  - eapply subst_wf_local; eauto.
    eapply onParams in decl'. auto.
  - apply onInductives in decl'.
    revert decl'. generalize ind_bodies at 2 4 5.
    intros.
    eapply Alli_mapi_id in decl'. eauto.
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
    apply (Alli_map_id onConstructors).
    intros n1 [[x p] n']. intros [[s Hty] Hpars].
    unfold on_pi2; f_equal; f_equal. eapply typed_subst. 4:eapply Hty. wf. wf. simpl. lia.
    rewrite Heq in onProjections. destruct onProjections as [_ onProjections].
    apply (Alli_map_id onProjections).
    intros n1 [x p]. intros [s Hty].
    unfold on_snd; f_equal; f_equal.
    eapply typed_subst. 4:eapply Hty. wf. wf. simpl. lia.
Qed.

Lemma subst_declared_inductive `{checker_flags} Σ ind mdecl idecl n k :
  wf Σ ->
  declared_inductive (fst Σ) ind mdecl idecl ->
  map_one_inductive_body (inductive_mind ind) (polymorphic_instance (mdecl.(ind_universes)))
                         (length (arities_context mdecl.(ind_bodies)))
                         (fun k' => subst n (k' + k)) (inductive_ind ind) idecl = idecl.
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
  red in ongdecl.
  eapply onInductives in ongdecl.
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

Definition strip_outer_cast_tProd_tLetIn_morph f :=
  forall t k,
  match strip_outer_cast t with
  | tProd na A B =>
    strip_outer_cast (f k t) = tProd na (f k A) (f (S k) B)
  | tLetIn na b ty b' =>
    strip_outer_cast (f k t) = tLetIn na (f k b) (f k ty) (f (S k) b')
  | _ => True
  end.

Lemma strip_outer_cast_tProd_tLetIn_subst n :
  strip_outer_cast_tProd_tLetIn_morph (subst n).
Proof.
  unfold strip_outer_cast_tProd_tLetIn_morph. intros t k.
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
  pose proof (strip_outer_cast_tProd_tLetIn_subst n t (#|ctx| + k)) as Hsubst.
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

Definition snoc_morph (f : nat -> term -> term) (f_ctx : nat -> context -> context) :=
  forall (k : nat) (Γ : list context_decl) (d : context_decl),
  f_ctx k (d :: Γ) = f_ctx k Γ,, map_decl (f (#|Γ| + k)) d.

Lemma decompose_prod_n_assum_rec_morph f f_ctx ctx nass t ctx' t' :
  snoc_morph f f_ctx ->
  strip_outer_cast_tProd_tLetIn_morph f ->
  forall k,
  decompose_prod_n_assum ctx nass t = Some (ctx', t') ->
  decompose_prod_n_assum (f_ctx k ctx) nass (f (length ctx + k) t) =
  Some (f_ctx k ctx', f (length ctx' + k) t').
Proof.
  induction nass in t, ctx, ctx', t' |- *;
    try (rewrite !decompose_prod_n_assum0; intros [= -> ->]; reflexivity);
      (simpl; try congruence);
      try rewrite Nat.sub_diag, Nat.add_0_r; try (eauto; congruence).
  intros Hsnoc Hstrip. red in Hstrip.
  intros k.
  pose proof (Hstrip t (#|ctx| + k)) as Hsubst.
  destruct (strip_outer_cast t) eqn:Ht; try congruence; rewrite Hsubst.
  - specialize (IHnass (ctx ,, vass n t0_1) t0_2 ctx' t' Hsnoc Hstrip k).
    unfold snoc in IHnass. red in Hsnoc. rewrite Hsnoc in IHnass. apply IHnass.
  - specialize (IHnass (ctx ,, vdef n t0_1 t0_2) t0_3 ctx' t' Hsnoc Hstrip k).
    unfold snoc in IHnass; rewrite Hsnoc in IHnass. apply IHnass.
Qed.

Lemma subst_decompose_prod_n_assum_morph f_ctx f nass t k :
  snoc_morph f f_ctx ->
  strip_outer_cast_tProd_tLetIn_morph f ->
  (forall k, f_ctx k [] = []) ->
  has_nparams nass t ->
  match decompose_prod_n_assum [] nass t with
  | Some (ctx', t') =>
    decompose_prod_n_assum [] nass (f k t) = Some (f_ctx k ctx', f (length ctx' + k) t')
  | None => False
  end.
Proof.
  intros Hsnoc Hstrip Hf Hpars. apply has_nparams_ex in Hpars as [[ctx' t'] Heq].
  rewrite Heq. eapply decompose_prod_n_assum_rec_morph in Heq; eauto. rewrite (Hf k) in Heq. eapply Heq.
Qed.

Lemma snoc_morph_subst_instance_constr u :
  snoc_morph (fun _ => subst_instance_constr u) (fun _ => subst_instance_context u).
Proof. red. intros. simpl. reflexivity. Qed.

Lemma strip_outer_cast_subst_instane_constr u t :
  strip_outer_cast (subst_instance_constr u t) =
  subst_instance_constr u (strip_outer_cast t).
Proof. induction t; simpl; auto. Qed.

Lemma strip_outer_cast_tProd_tLetIn_subst_instance_constr u :
  strip_outer_cast_tProd_tLetIn_morph (fun _ => subst_instance_constr u).
Proof.
  red. intros.
  destruct (strip_outer_cast t) eqn:Heq; try auto.
  rewrite strip_outer_cast_subst_instane_constr. now rewrite Heq.
  rewrite strip_outer_cast_subst_instane_constr. now rewrite Heq.
Qed.

Lemma subst_instance_constr_decompose_prod_n_assum nass t u :
  has_nparams nass t ->
  match decompose_prod_n_assum [] nass t with
  | Some (ctx', t') =>
    decompose_prod_n_assum [] nass (subst_instance_constr u t) =
    Some (subst_instance_context u ctx', subst_instance_constr u t')
  | None => False
  end.
Proof.
  eapply (subst_decompose_prod_n_assum_morph (fun _ => subst_instance_context u) (fun _ => subst_instance_constr u)).
  exact 0. apply snoc_morph_subst_instance_constr.
  apply strip_outer_cast_tProd_tLetIn_subst_instance_constr.
  reflexivity.
Qed.

Require Import Weakening.

Lemma subst_instantiate_params_subst n k params args s t :
  Forall Ast.wf n -> forall s' t',
    instantiate_params_subst params args s t = Some (s', t') ->
    instantiate_params_subst
      (mapi_rec (fun k' decl => subst_decl n (k' + k) decl) params #|s|)
      (map (subst n k) args) (map (subst n k) s) (subst n (#|s| + k) t) =
    Some (map (subst n k) s', subst n (#|s| + k + #|params|) t').
Proof.
  intros Hn.
  induction params in args, t, n, Hn, k, s |- *; intros ctx' t'.
  - destruct args; simpl; rewrite ?Nat.add_0_r; try congruence.
  - simpl.
    pose proof (strip_outer_cast_tProd_tLetIn_subst n t (#|s| + k)) as Hsubst.
    destruct a as [na [body|] ty]; simpl; try congruence;
    destruct (strip_outer_cast t); try congruence; rewrite Hsubst.
    -- intros Ht'.
       specialize (IHparams _ k _ _ _ Hn _ _ Ht').
       simpl in IHparams.
       replace (#|s| + k + S #|params|) with (S (#|s| + k + #|params|)) by lia.
       rewrite <- IHparams. f_equal.
       rewrite distr_subst. reflexivity. auto.
    -- intros Ht'. destruct args; try congruence. simpl.
       specialize (IHparams _ k _ _ _ Hn _ _ Ht').
       simpl in IHparams.
       replace (#|s| + k + S #|params|) with (S (#|s| + k + #|params|)) by lia.
       rewrite <- IHparams. f_equal.
Qed.

Require Import ssreflect ssrbool.

Lemma subst_decl_closed n k d : wf_decl d -> closed_decl k d -> subst_decl n k d = d.
Proof.
  case: d => na [body|] ty; rewrite /closed_decl /subst_decl /map_decl /wf_decl /= => [[wfb wfty]].
  move/andP => [cb cty]. rewrite !subst_closedn //.
  move=> cty; now rewrite !subst_closedn //.
Qed.

Lemma closed_decl_upwards k d : closed_decl k d -> forall k', k <= k' -> closed_decl k' d.
Proof.
  case: d => na [body|] ty; rewrite /closed_decl /=.
  move/andP => [cb cty] k' lek'. do 2 rewrite (closed_upwards k) //.
  move=> cty k' lek'; rewrite (closed_upwards k) //.
Qed.

Lemma closed_ctx_subst n k ctx : Forall wf_decl ctx -> closed_ctx ctx = true -> subst_context n k ctx = ctx.
Proof.
  induction ctx in n, k |- *; auto.
  unfold closed_ctx, id. intros wfctx. inv wfctx.
  rewrite mapi_app forallb_app List.rev_length /= Nat.add_0_r.
  move/andb_true_iff => /= [Hctx /andb_true_iff [Ha _]].
  rewrite subst_context_snoc /snoc /= IHctx // subst_decl_closed //.
  now apply: closed_decl_upwards.
Qed.

Lemma closed_tele_subst n k ctx :
  Forall wf_decl ctx -> closed_ctx ctx ->
  mapi (fun (k' : nat) (decl : context_decl) => subst_decl n (k' + k) decl) (List.rev ctx) = List.rev ctx.
Proof.
  rewrite /closed_ctx /mapi. generalize 0.
  induction ctx using rev_ind; try easy.
  move=> n0 /Forall_app [wfctx wfx]. inv wfx.
  rewrite /closed_ctx !rev_app_distr /id /=.
  move/andP => [closedx Hctx].
  rewrite subst_decl_closed //. rewrite (closed_decl_upwards n0) //; lia.
  f_equal. now rewrite IHctx.
Qed.

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
    pose proof (strip_outer_cast_tProd_tLetIn_subst s t #|ctx2|) as Hsubst.
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

Lemma decompose_prod_n_assum_extend_ctx {ctx n t ctx' t'} ctx'' :
  decompose_prod_n_assum ctx n t = Some (ctx', t') ->
  decompose_prod_n_assum (ctx ++ ctx'') n t = Some (ctx' ++ ctx'', t').
Proof.
  induction n in ctx, t, ctx', t', ctx'' |- *. simpl. intros [= -> ->]. eauto.
  simpl.
  destruct (strip_outer_cast t); simpl; try congruence.
  intros H. eapply (IHn _ _ _ _ ctx'' H).
  intros H. eapply (IHn _ _ _ _ ctx'' H).
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

Lemma subst_it_mkProd_or_LetIn n k ctx t :
  subst n k (it_mkProd_or_LetIn ctx t) =
  it_mkProd_or_LetIn (subst_context n k ctx) (subst n (length ctx + k) t).
Proof.
  induction ctx in n, k, t |- *; simpl; try congruence.
  pose (subst_context_snoc n k ctx a). unfold snoc in e. rewrite e. clear e.
  simpl. destruct decl_body. now rewrite IHctx.
  pose (subst_context_snoc n k ctx a). simpl. now rewrite IHctx.
Qed.

Lemma to_extended_list_k_subst n k c k' :
  to_extended_list_k (subst_context n k c) k' = to_extended_list_k c k'.
Proof.
  unfold to_extended_list_k. revert k'.
  generalize (@nil term) at 1 2.
  induction c in n, k |- *; simpl; intros. reflexivity.
  rewrite subst_context_snoc. unfold snoc. simpl.
  destruct a. destruct decl_body. unfold subst_decl, map_decl. simpl.
  now rewrite IHc. simpl. apply IHc.
Qed.

Lemma to_extended_list_k_map_subst:
  forall n (k : nat) (c : context) k',
    #|c| + k' <= k ->
    to_extended_list_k c k' = map (subst n k) (to_extended_list_k c k').
Proof.
  intros n k c k'.
  pose proof (to_extended_list_k_spec c k').
  symmetry. apply_spec. intros.
  destruct H1. intuition. subst x. simpl.
  destruct (leb_spec_Set k x0). lia. reflexivity.
Qed.

Lemma Alli_mapi_spec {A B} {P : nat -> A -> Type} {l} {f g : nat -> A -> B} {n} :
  Alli P n l -> (forall n x, P n x -> f n x = g n x) ->
  mapi_rec f l n = mapi_rec g l n.
Proof.
  induction 1; simpl; trivial.
  intros Heq. rewrite Heq; f_equal; auto.
Qed.

Lemma subst_instantiate_params_none n k params args s t :
  Forall Ast.wf n -> has_nparams #|params| t -> Forall Ast.wf args -> Ast.wf t ->
  instantiate_params_subst params args s t = None ->
  instantiate_params_subst params (map (subst n k) args) s (subst n k t) = None.
Proof.
  intros Hn Hp Hargs Ht.
  apply has_nparams_ex in Hp as [[ctx' t'] He].
  revert ctx' t' He. generalize (@nil context_decl).
  induction params in args, Hargs, Hn, t, Ht, n, k |- *.
  destruct args; simpl. discriminate. reflexivity.

  (* simpl. *)
  (* pose proof (strip_outer_cast_tProd_tLetIn_subst n t k) as Hsubst. *)
  (* intros l' ctx' t'. *)
  (* destruct (strip_outer_cast t) eqn:Hstript; try congruence; try reflexivity; try rewrite Hsubst. *)
  (* destruct args; simpl; try congruence; auto. *)
  (* unfold instantiate_params. simpl. *)
  (* - intros Ht'. *)
  (*   pose proof (decompose_prod_n_assum_ctx _ _ _ _ _ Ht') as [ctx'' ->]. *)
  (*   change (l',, vass n0 t0_1 ,,, ctx'') with (l' ,,, [vass n0 t0_1] ,,, ctx'') in Ht'. *)
  (*   change (l' ,, vass n0 t0_1) with (l' ,,, [vass n0 t0_1]) in Ht'. *)
  (*   eapply (decompose_prod_n_assum_subst _ _ _ _ _ [t0_1]) in Ht'. *)
  (*   inv Hargs. *)
  (*   assert (Ast.wf ((subst0 [t0_1]) t0_2)). apply wf_subst. admit. admit. *)
  (*   apply wf_strip_outer_cast in Ht. rewrite Hstript in Ht. *)
  (*   (* now inv Ht. *) *)
  (*   specialize (IHparams n k args _ Hn H0 H _ _ _ Ht'). *)
  (*   unfold subst1 in *. *)
  (*   intros. destruct (decl_body a); try congruence. specialize (IHparams H2). *)
  (*   rewrite <- IHparams. f_equal. *)
  (*   now rewrite distr_subst. *)
  (*   now inv Hargs. *)
  (* - intros Ht'. *)
  (*   pose proof (decompose_prod_n_assum_ctx _ _ _ _ _ Ht') as [ctx'' ->]. *)
  (*   change (l',, vdef n0 t0_1 t0_2 ,,, ctx'') with (l' ,,, [vdef n0 t0_1 t0_2] ,,, ctx'') in Ht'. *)
  (*   change (l' ,, vdef n0 t0_1 t0_2) with (l' ,,, [vdef n0 t0_1 t0_2]) in Ht'. *)
  (*   eapply (decompose_prod_n_assum_subst _ _ _ _ _ [t0_1]) in Ht'. *)
  (*   assert (Ast.wf ((subst0 [t0_1]) t0_3)). *)
  (*   apply wf_strip_outer_cast in Ht. rewrite Hstript in Ht. *)
  (*   inv Ht; now apply wf_subst. *)
  (*   specialize (IHparams n k args _ Hn Hargs H _ _ _ Ht'). *)
  (*   unfold subst1 in *. *)
  (*   intros. destruct (decl_body a); try congruence. specialize (IHparams H0). *)
  (*   rewrite <- IHparams. f_equal. *)
  (*   now rewrite distr_subst. *)
  (*   apply wf_strip_outer_cast in Ht. rewrite Hstript in Ht. *)
  (*   now inv Ht. *)
Admitted.

Lemma subst_instantiate_params n k params args t :
  Forall wf_decl params -> Forall Ast.wf n -> Forall Ast.wf args -> Ast.wf t ->
  closed_ctx params ->
  option_map (subst n k) (instantiate_params params args t) =
  instantiate_params params (map (subst n k) args) (subst n k t).
Proof.
  unfold instantiate_params.
  move=> wfparams wfn wfargs wft.
  move/(closed_tele_subst n k params)=> Heq.
  rewrite -{2}Heq //.
  specialize (subst_instantiate_params_subst n k (List.rev params) args [] t wfn).
  move=> /= Heq'.
  case E: (instantiate_params_subst (List.rev params) args)=> [[l' t']|] /= //.
  specialize (Heq' _ _ E). rewrite Heq'. f_equal.
  rewrite distr_subst //.
  move/instantiate_params_subst_length: E => -> /=. do 2 f_equal. lia.
  rewrite Heq; auto.
  eapply subst_instantiate_params_none in E. rewrite -> E. reflexivity. eauto. admit. auto. auto.
Admitted.
Hint Rewrite subst_instantiate_params : lift.

(* Lemma subst_instantiate_params n k params args t : *)
(*   Forall Ast.wf n -> closed_ctx params = true -> *)
(*   forall t', *)
(*     instantiate_params params args t = Some t' -> *)
(*     instantiate_params params (map (subst n k) args) (subst n k t) = *)
(*     Some (subst n k t'). *)
(* Proof. *)
(*   intros Hn Hpars t'. unfold instantiate_params. *)
(*   generalize (subst_instantiate_params_subst n k params args [] t Hn). *)
(*   destruct instantiate_params_subst as [[s' t'']|]. *)
(*   - intros Heq. specialize (Heq _ _ eq_refl). simpl in Heq. rewrite Heq. *)
(*     intros [= <-]. *)
(*     rewrite distr_subst; auto. eapply instantiate_params_subst_length in Heq. *)
(*     simpl in Heq; rewrite map_length in Heq. rewrite Heq. do 3 f_equal. lia. *)
(*   - congruence. *)
(* Qed. *)
(* Hint Rewrite subst_instantiate_params : subst. *)

Lemma has_nparams_subst n t s k : has_nparams n t -> has_nparams n (subst s k t).
Proof.
  intros H. eapply subst_decompose_prod_n_assum in H.
  destruct decompose_prod_n_assum. destruct p as [ctx' t'].
  red. rewrite -> H. congruence. elim H.
Qed.

Lemma has_nparams_subst_instance_constr n t u : has_nparams n t -> has_nparams n (subst_instance_constr u t).
Proof.
  intros H. eapply subst_instance_constr_decompose_prod_n_assum in H.
  destruct decompose_prod_n_assum. destruct p as [ctx' t'].
  red. rewrite -> H. congruence. elim H.
Qed.

Lemma subst_instance_constr_it_mkProd_or_LetIn u ctx t :
  subst_instance_constr u (it_mkProd_or_LetIn ctx t) =
  it_mkProd_or_LetIn (subst_instance_context u ctx) (subst_instance_constr u t).
Proof.
  induction ctx in u, t |- *; simpl; try congruence.
  rewrite IHctx. f_equal. destruct (decl_body a); eauto.
Qed.

Lemma subst_instance_context_length u ctx : #|subst_instance_context u ctx| = #|ctx|.
Proof. unfold subst_instance_context, map_context. now rewrite map_length. Qed.

Lemma arities_context_length l : #|arities_context l| = #|l|.
Proof. unfold arities_context. now rewrite rev_map_length. Qed.

Section Reverse_Induction.
  Context {A : Type}.
  Lemma rev_list_ind :
    forall P:list A-> Type,
      P [] ->
        (forall (a:A) (l:list A), P (List.rev l) -> P (List.rev (a :: l))) ->
        forall l:list A, P (List.rev l).
    Proof.
      induction l; auto.
    Qed.

    Theorem rev_ind :
      forall P:list A -> Type,
        P [] ->
        (forall (x:A) (l:list A), P l -> P (l ++ [x])) -> forall l:list A, P l.
    Proof.
      intros.
      generalize (rev_involutive l).
      intros E; rewrite <- E.
      apply (rev_list_ind P).
      auto.

      simpl.
      intros.
      apply (X0 a (List.rev l0)).
      auto.
    Qed.

  End Reverse_Induction.

Lemma Alli_app {A} (P : nat -> A -> Type) n l l' : Alli P n (l ++ l') -> Alli P n l * Alli P (length l + n) l'.
Proof.
  induction l in n, l' |- *; intros H. split; try constructor. apply H.
  inversion_clear H. split; intuition auto. constructor; auto. eapply IHl; eauto.
  simpl. replace (S (#|l| + n)) with (#|l| + S n) by lia.
  eapply IHl; eauto.
Qed.

Lemma app_context_nil_l Γ : [] ,,, Γ = Γ.
Proof. unfold app_context; now rewrite app_nil_r. Qed.

Require Import Weakening.

Lemma wf_arities_context `{checker_flags} Σ mind mdecl : wf Σ ->
  declared_minductive (fst Σ) mind mdecl -> wf_local Σ (arities_context mdecl.(ind_bodies)).
Proof.
  intros wfΣ Hdecl.
  eapply declared_minductive_inv in Hdecl. 2:apply weaken_env_prop_typing. all:eauto.
  apply onInductives in Hdecl.
  unfold arities_context.
  revert Hdecl.
  induction (ind_bodies mdecl) using rev_ind. constructor.
  intros Ha.
  rewrite rev_map_app.
  simpl. apply Alli_app in Ha as [Hl Hx].
  inv Hx. clear X0.
  destruct X as [[[s Hs] _] _ _].
  specialize (IHl Hl).
  econstructor; eauto.
  fold (arities_context l) in *.
  unshelve epose proof (weakening Σ [] (arities_context l) _ _ wfΣ _ Hs).
  now rewrite app_context_nil_l.
  simpl in X.
  eapply (env_prop_typing _ typecheck_closed) in Hs; eauto.
  rewrite -> andb_true_iff in Hs. destruct Hs as [Hs Ht].
  simpl in Hs. apply (lift_closed #|arities_context l|) in Hs.
  rewrite -> Hs, app_context_nil_l in X.
  apply X.
Qed.

Lemma on_constructor_closed `{checker_flags} {Σ mind mdecl u i idecl cdecl} :
  wf Σ ->
  on_constructor (lift_typing typing) Σ mdecl (inductive_ind mind) idecl i cdecl ->
  closed (substl (inds (inductive_mind mind) u (ind_bodies mdecl))
                 (subst_instance_constr u (snd (fst cdecl)))) = true.
Proof.
  intros wfΣ [[s Hs] Hparams].
  pose proof (typing_wf_local wfΣ Hs).
  destruct cdecl as [[id cty] car].
  eapply (env_prop_typing _ typecheck_closed) in Hs; eauto.
  rewrite arities_context_length in Hs.
  rewrite -> andb_true_iff in *. simpl in *.
  destruct Hs as [Hs _].
  unfold substl. eapply (closedn_subst _ 0 0).
  clear. unfold inds. induction #|ind_bodies mdecl|; simpl; try constructor; auto.
  simpl. now rewrite -> inds_length, closedn_subst_instance_constr.
Qed.

Lemma simpl_subst_k (N : list term) (M : term) :
  Ast.wf M -> forall k p, p = #|N| -> subst N k (lift p k M) = M.
Proof.
  intros. subst p. rewrite <- (Nat.add_0_r #|N|).
  rewrite -> simpl_subst_rec, lift0_id; auto. Qed.

Ltac nth_leb_simpl :=
  match goal with
    |- context [leb ?k ?n] => elim (leb_spec_Set k n); try lia; intros; simpl
  | |- context [nth_error ?l ?n] => elim (nth_error_spec l n); rewrite -> ?app_length, ?map_length;
                                    try lia; intros; simpl
  | H : context[nth_error (?l ++ ?l') ?n] |- _ =>
    (rewrite -> (AstUtils.nth_error_app_ge l l' n) in H by lia) ||
    (rewrite -> (AstUtils.nth_error_app_lt l l' n) in H by lia)
  | H : nth_error ?l ?n = Some _, H' : nth_error ?l ?n' = Some _ |- _ =>
    replace n' with n in H' by lia; rewrite -> H in H'; injection H'; intros; subst
  | _ => lia || congruence || solve [repeat (f_equal; try lia)]
  end.

Ltac change_Sk :=
  match goal with
    |- context [S (?x + ?y)] => progress change (S (x + y)) with (S x + y)
  end.

Lemma subst_app_decomp l l' k t :
  Ast.wf t -> Forall Ast.wf l ->
  subst (l ++ l') k t = subst l' k (subst (List.map (lift0 (length l')) l) k t).
Proof.
  intros wft wfl.
  induction wft in k |- * using term_wf_forall_list_ind; simpl; auto;
    rewrite ?subst_mkApps; try change_Sk;
    try (f_equal; rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length;
         eauto; apply_spec; eauto).

  - repeat nth_leb_simpl.
    rewrite nth_error_map in e0. rewrite e in e0.
    injection e0; intros <-.
    rewrite -> permute_lift, Nat.add_0_r by auto.
    rewrite <- (Nat.add_0_r #|l'|).
    rewrite -> simpl_subst_rec, lift0_id; auto with wf; try lia. apply wf_lift.
    eapply nth_error_forall in e; eauto.
Qed.

Lemma subst_app_simpl l l' k t :
  Ast.wf t -> Forall Ast.wf l -> Forall Ast.wf l' ->
  subst (l ++ l') k t = subst l k (subst l' (k + length l) t).
Proof.
  intros wft wfl wfl'.
  induction wft in k |- * using term_wf_forall_list_ind; simpl; eauto;
    rewrite ?subst_mkApps; try change_Sk;
    try (f_equal; rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length, ?Nat.add_assoc;
         eauto; apply_spec; eauto).

  - repeat nth_leb_simpl.
    rewrite -> Nat.add_comm, simpl_subst; eauto.
    eapply nth_error_forall in e; eauto.
Qed.

(** Linking a cantext (with let-ins) and a well-formed substitution for it. *)
Inductive context_subst : context -> list term -> list term -> Set :=
| context_subst_nil : context_subst [] [] []
| context_subst_ass Γ args s na t a :
    context_subst Γ args s ->
    context_subst (vass na t :: Γ) (args ++ [a]) (a :: s)
| context_subst_def Γ args s na b t :
    context_subst Γ args s ->
    context_subst (vdef na b t :: Γ) args (subst s 0 b :: s).

(* Fixpoint match_context (Γ : context) (a : list term) s := *)
(*   match Γ, a with *)
(*   | vass na t :: Γ, a :: args => match_context Γ args (a :: s) *)
(*   | vdef na b t :: Γ, args => match_context Γ args (subst s 0 b :: s) *)
(*   | [], [] => s *)
(*   end. *)

Lemma context_subst_length Γ a s : context_subst Γ a s -> #|Γ| = #|s|.
Proof. induction 1; simpl; congruence. Qed.

Lemma context_subst_assumptions_length Γ a s : context_subst Γ a s -> context_assumptions Γ = #|a|.
Proof. induction 1; simpl; try congruence. rewrite app_length /=. lia. Qed.

Lemma context_subst_app `{cf:checker_flags} Σ Γ Γ' a s :
  All_local_env (fun _ _ t T => Ast.wf t /\ Ast.wf T) Σ Γ' ->
  Forall Ast.wf a -> Forall Ast.wf s ->
  context_subst (Γ' ++ Γ) a s ->
  { a0 & { a1 & { s0 & { s1 & (context_subst Γ a0 s0 * context_subst (subst_context s0 0 Γ') a1 s1
                               * (a = a0 ++ a1) * (s = s1 ++ s0))%type } } } }.
Proof.
  induction Γ' in Γ, a, s |- *. simpl.
  exists a, [], s, []. rewrite app_nil_r; intuition.

  simpl. intros wfΓ wfa wfs Hs.
  revert wfΓ wfa wfs. inv Hs; intros wfΓ wfa wfs; inv wfΓ.
  - eapply Forall_app in wfa as [Hargs Ha1];
    eapply (Forall_app _ [a1]) in wfs as [Ha'' Hs0].
    specialize (IHΓ' _ _ _ H0 Hargs Hs0 H).
    destruct IHΓ' as (a0' & a1' & s1 & s2 & ((sa0 & sa1) & eqargs) & eqs0).
    subst. exists a0', (a1' ++ [a1]), s1, (a1 :: s2). intuition eauto.
    rewrite subst_context_snoc. constructor. auto. now rewrite app_assoc.
  - eapply (Forall_app _ [subst0 s0 b]) in wfs as [Ha'' Hs0].
    specialize (IHΓ' _ _ _ H0 wfa Hs0 H).
    destruct IHΓ' as (a0' & a1' & s1 & s2 & ((sa0 & sa1) & eqargs) & eqs0).
    subst. exists a0', a1', s1, (subst s2 0 (subst s1 #|Γ'| b) :: s2). intuition eauto.
    rewrite -> subst_context_snoc, Nat.add_0_r.
    unfold subst_decl; simpl. unfold map_decl. simpl.
    econstructor. auto. simpl. f_equal.
    rewrite -> subst_app_simpl; auto. simpl.
    pose proof(context_subst_length _ _ _ sa1) as Hs1.
    rewrite subst_context_length in Hs1. rewrite -> Hs1. auto. auto.
    apply Forall_app in Hs0. intuition.
    apply Forall_app in Hs0. intuition.
Qed.

Lemma it_mkProd_or_LetIn_app l l' t :
  it_mkProd_or_LetIn (l ++ l') t = it_mkProd_or_LetIn l' (it_mkProd_or_LetIn l t).
Proof. induction l in l', t |- *; simpl; auto. Qed.

(* Lemma instantiate_params_subst_pres {params args s t s' t'} : *)
(*     instantiate_params_subst params args s t = Some (s', t') -> *)
(*     {s'' & s' = s'' ++ s }. *)
(* Proof. *)
(*   induction params in args, s, t, s', t' |- *; simpl; intros. *)
(*   destruct args; try congruence. exists []. simpl; congruence. *)
(*   destruct (decl_body a); destruct (strip_outer_cast t); try congruence. *)
(*   destruct (IHparams _ _ _ _ _ H) as [s'' ->]. *)
(*   exists (s'' ++ [subst0 s t1_1]). now rewrite <- app_assoc. *)
(*   destruct args; try congruence. *)
(*   destruct (IHparams _ _ _ _ _ H) as [s'' ->]. *)
(*   exists (s'' ++ [t0]). now rewrite <- app_assoc. *)
(* Qed. *)

(* Lemma instantiate_params_context_subst `{cf:checker_flags} Σ args ctx ty s : *)
(*   Ast.wf ty -> *)
(*   Forall Ast.wf args -> Forall Ast.wf s -> *)
(*   context_subst ctx args s -> forall ctx' args' s' t' *)
(*   (wfctx' : All_local_env (fun _ _ t T => Ast.wf t /\ Ast.wf T) Σ ctx'), *)
(*   instantiate_params_subst (List.rev ctx') args' s ty = Some (s', t') -> *)
(*   (context_subst (ctx' ++ ctx) (args ++ args') s' * (ty = t'))%type. *)
(* Proof. *)
(*   intros wfty wfargs wfs Hs ctx'. *)
(*   revert ctx args wfargs ty wfty s wfs Hs. *)
(*   induction ctx' using rev_ind; intros. (* in ctx, args, s, ty, Hs |- *; intros. *) *)
(*   - simpl in H. destruct args'; try congruence. simpl. *)
(*     revert H. intros [= -> ->]. rewrite app_nil_r; intuition. *)
(*   - simpl in H. *)
(*     rewrite rev_app_distr in H. simpl in H. *)
(*     destruct x as [na [body|] ty']. simpl in *. *)
(*     destruct (strip_outer_cast ty) eqn:Heq; try discriminate. *)
(*     split. *)
(*     specialize (IHctx' (vdef na body ty' :: ctx) args wfargs ty'). *)
(*     forward IHctx'. admit. *)
(*     destruct (instantiate_params_subst_pres H) as [s'' ->]. *)
(*     specialize (IHctx' (subst0 s t1 :: s)). *)
(*     forward IHctx'. constructor; auto. apply wf_subst; auto. admit. *)
(*     forward IHctx'. constructor; auto. *)
(*     specialize (IHctx' args' _ _ H). *)
(*     rewrite <- app_assoc. simpl. *)

(* Lemma instantiate_params_context_subst `{cf:checker_flags} Σ args parctx ty s : *)
(*   All_local_env (fun _ _ t T => Ast.wf t /\ Ast.wf T) Σ parctx -> Ast.wf ty -> *)
(*   Forall Ast.wf args -> Forall Ast.wf s -> *)
(*   context_subst parctx args s -> *)
(*   forall parctx' s', parctx = subst_context s' 0 parctx' -> *)
(*   instantiate_params (List.rev parctx') args (it_mkProd_or_LetIn parctx ty) = Some (subst s 0 ty). *)
(* Proof. *)
(*   revert s args parctx ty. *)
(*   refine (well_founded_ind (measure_wf lt_wf (@length term)) _ _). *)
(*   intros s IH args parctx. destruct parctx using rev_ind; intros ty wfctx wfty wfargs wfs. *)

(* Lemma context_subst_instantiate_params `{cf:checker_flags} Σ args parctx ty s : *)
(*   All_local_env (fun _ _ t T => Ast.wf t /\ Ast.wf T) Σ parctx -> Ast.wf ty -> *)
(*   Forall Ast.wf args -> Forall Ast.wf s -> *)
(*   context_subst parctx args s -> *)
(*   forall parctx' s', parctx = subst_context s' 0 parctx' -> *)
(*   instantiate_params (List.rev parctx') args (it_mkProd_or_LetIn parctx ty) = Some (subst s 0 ty). *)
(* Proof. *)
(*   revert s args parctx ty. *)
(*   refine (well_founded_ind (measure_wf lt_wf (@length term)) _ _). *)
(*   intros s IH args parctx. destruct parctx using rev_ind; intros ty wfctx wfty wfargs wfs. *)
(*   - intros H; inv H. simpl; rewrite subst_empty; auto. *)
(*     intros. destruct parctx'; simpl in *; try congruence. rewrite -> subst_context_snoc in H. discriminate. *)
(*   - intros Hcsubst. clear IHparctx. *)
(*     apply All_local_env_app in wfctx as [wfd wfctx]. *)
(*     eapply context_subst_app in Hcsubst; eauto. *)
(*     destruct Hcsubst as (a0 & a1 & s0 & s1 & (((Hd & Hs1) & eqargs) & eqs)). *)
(*     rewrite it_mkProd_or_LetIn_app. simpl. *)
(*     intros parctx' s' Hparctx'. *)
(*     destruct x as [na [body|] dty]; simpl in *. *)
(*     destruct parctx' using rev_ind; *)
(*     [apply app_eq_nil in Hparctx'; intuition discriminate| *)
(*     clear IHparctx'; unfold subst_context in Hparctx'; simpl in Hparctx'; *)
(*     rewrite fold_context_app in Hparctx'; apply app_inj_tail in Hparctx' as [Hparctx' Hd']]. *)
(*     rewrite rev_app_distr. *)
(*     inversion wfd. *)
(*     -- subst Γ b t na0. simpl. simpl in Hd'. destruct x as [na' [body'|] ty']; try discriminate. simpl. *)
(*        injection Hd'. intros -> -> <-. *)
(*        unfold subst1. rewrite subst_it_mkProd_or_LetIn. *)
(*        subst s args. revert IH Hs1. inv Hd. inv H. intros IH Hs1. simpl. *)
(*        specialize (IH s1). *)
(*        forward IH. red. rewrite app_length. simpl. lia. *)
(*        rewrite subst_empty in *; intuition auto. *)
(*        specialize (IH a1 (subst_context [subst0 s' body'] 0 l) (subst [subst0 s' body'] #|l| ty)). *)
(*        eapply Forall_app in wfs as [wfs1 wfs0]. eapply Forall_app in wfargs as [wfa0 wfa1]. *)
(*        forward IH. *)
(*        { rewrite subst_context_alt. *)
(*          clear -wfctx wfs0 H. *)
(*          generalize #|l|. unfold mapi. generalize 0 at 3. *)
(*          induction wfctx; econstructor; intuition eauto with wf. } *)
(*        do 3 forward IH; intuition auto with wf. *)
(*        specialize (H2 l [subst0 s' body'] eq_refl). *)
(*        rewrite Nat.add_0_r. rewrite H2. *)
(*        f_equal. *)
(*        rewrite subst_app_simpl; auto. simpl. *)
(*        apply context_subst_length in Hs1. rewrite subst_context_length in Hs1. now rewrite Hs1. *)

(*     -- subst args s. simpl. revert IH wfs Hs1. inv Hd. inv H. intros. *)
(*        simpl. *)
(*        unfold subst1. rewrite subst_it_mkProd_or_LetIn. *)
(*        specialize (IH s1). *)
(*        forward IH. red. rewrite app_length. simpl. lia. *)
(*        specialize (IH a1 (subst_context [a] 0 l) (subst [a] #|l| ty)). *)
(*        eapply Forall_app in wfs as [wfs1 wfs0]. inv wfs0. eapply Forall_app in wfargs as [wfa0 wfa1]. *)
(*        forward IH. *)
(*        { rewrite subst_context_alt. *)
(*          clear -wfctx H. *)
(*          generalize #|l|. unfold mapi. generalize 0 at 2. *)
(*          induction wfctx; econstructor; intuition eauto with wf. } *)
(*        do 3 forward IH; intuition auto with wf. *)
(*        rewrite subst_context_length in H1. *)
(*        rewrite Nat.add_0_r, H1. f_equal. *)
(*        rewrite subst_app_simpl; auto. *)
(*        apply context_subst_length in Hs1. rewrite subst_context_length in Hs1. now rewrite Hs1. *)
(* Qed. *)

Fixpoint make_context_subst ctx args s :=
  match ctx with
  | [] => match args with
          | [] => Some s
          | a :: args => None
          end
  | d :: ctx =>
    match d.(decl_body) with
    | Some body => make_context_subst ctx args (subst0 s body :: s)
    | None => match args with
              | a :: args => make_context_subst ctx args (a :: s)
              | [] => None
              end
    end
  end.

Lemma make_context_subst_rec_spec ctx args s tele args' s' :
  context_subst ctx args s ->
  make_context_subst tele args' s = Some s' ->
  context_subst (List.rev tele ++ ctx) (args ++ args') s'.
Proof.
  induction tele in ctx, args, s, args', s' |- *.
  - move=> /= Hc. case: args'. move => [= <-].
    now rewrite app_nil_r.
    move=> a l //.
  - move=> Hc /=. case: a => [na [body|] ty] /=.
    -- specialize (IHtele (vdef na body ty :: ctx) args (subst0 s body :: s) args' s').
       move=> /=. rewrite <- app_assoc.
       move/(IHtele _). move=> H /=. apply H.
       constructor. auto.
    -- case: args' => [|a args']; try congruence.
       specialize (IHtele (vass na ty :: ctx) (args ++ [a]) (a :: s) args' s').
       move=> /=. rewrite <- app_assoc.
       move/(IHtele _). move=> H /=. simpl in H. rewrite <- app_assoc in H. apply H.
       constructor. auto.
Qed.

Lemma make_context_subst_spec tele args s' :
  make_context_subst tele args [] = Some s' ->
  context_subst (List.rev tele) args s'.
Proof.
  move/(make_context_subst_rec_spec [] [] [] _ _ _ context_subst_nil).
  rewrite app_nil_r /= //.
Qed.

Lemma instantiate_params_subst_make_context_subst ctx args s ty s' ty' :
  instantiate_params_subst ctx args s ty = Some (s', ty') ->
  exists ctx'',
  make_context_subst ctx args s = Some s' /\
  decompose_prod_n_assum [] (length ctx) ty = Some (ctx'', ty').
Proof.
  induction ctx in args, s, ty, s' |- *; simpl.
  case: args => [|a args'] // [= <- <-]. exists []; intuition congruence.
  case: a => [na [body|] ty''] /=.
  - destruct (strip_outer_cast ty); try congruence.
    intros. move: (IHctx _ _ _ _ H) => [ctx'' [Hmake Hdecomp]].
    eapply (decompose_prod_n_assum_extend_ctx [vdef n t1 t2]) in Hdecomp.
    unfold snoc. eexists; intuition eauto.
  - destruct (strip_outer_cast ty); try congruence.
    case: args => [|a args']; try congruence.
    move=> H. move: (IHctx _ _ _ _ H) => [ctx'' [Hmake Hdecomp]].
    eapply (decompose_prod_n_assum_extend_ctx [vass n t1]) in Hdecomp.
    unfold snoc. eexists; intuition eauto.
Qed.

Lemma instantiate_params_make_context_subst ctx args ty ty' :
  instantiate_params ctx args ty = Some ty' ->
  exists ctx' ty'' s',
    decompose_prod_n_assum [] (length ctx) ty = Some (ctx', ty'') /\
    make_context_subst (List.rev ctx) args [] = Some s' /\ ty' = subst0 s' ty''.
Proof.
  unfold instantiate_params.
  case E: instantiate_params_subst => [[s ty'']].
  move=> [= <-].
  eapply instantiate_params_subst_make_context_subst in E.
  destruct E as [ctx'' [Hs Hty'']].
  exists ctx'', ty'', s. split; auto.
  now rewrite -> List.rev_length in Hty''.
  congruence.
Qed.

Lemma decompose_prod_n_assum_it_mkProd ctx ctx' ty :
  decompose_prod_n_assum ctx #|ctx'| (it_mkProd_or_LetIn ctx' ty) = Some (ctx' ++ ctx, ty).
Proof.
  revert ctx ty. induction ctx' using rev_ind; move=> // ctx ty.
  rewrite app_length /= it_mkProd_or_LetIn_app /=.
  destruct x as [na [body|] ty'] => /=;
  now rewrite !Nat.add_1_r /= IHctx' -app_assoc.
Qed.

Definition is_ind_app_head t :=
  match t with
  | tInd _ _ => true
  | tApp (tInd _ _) _ => true
  | _ => false
  end.

Lemma is_ind_app_head_mkApps ind u l : is_ind_app_head (mkApps (tInd ind u) l).
Proof. now destruct l; simpl. Qed.

Lemma decompose_prod_assum_it_mkProd ctx ctx' ty :
  is_ind_app_head ty ->
  decompose_prod_assum ctx (it_mkProd_or_LetIn ctx' ty) = (ctx' ++ ctx, ty).
Proof.
  revert ctx ty. induction ctx' using rev_ind; move=> // ctx ty /=.
  destruct ty; simpl; try (congruence || reflexivity).
  move=> Hty. rewrite it_mkProd_or_LetIn_app /=.
  case: x => [na [body|] ty'] /=; by rewrite IHctx' // /snoc -app_assoc.
Qed.

Lemma inds_alt ind u l :
  inds ind u l = List.rev (mapi (fun i _ => tInd {| inductive_mind := ind; inductive_ind := i |} u) l).
Proof.
  unfold inds, mapi. induction l using rev_ind. simpl. reflexivity.
  now rewrite app_length /= Nat.add_1_r IHl mapi_rec_app /= rev_app_distr /= Nat.add_0_r.
Qed.

Lemma map_subst_instance_constr_to_extended_list_k u ctx k :
  map (subst_instance_constr u) (to_extended_list_k ctx k) = to_extended_list_k ctx k.
Proof.
  pose proof (to_extended_list_k_spec ctx k).
  apply_spec. intros. now destruct H0 as [n [-> _]].
Qed.

Lemma subst_cstr_concl_head ind u mdecl (arity : context) args :
  let head := tRel (#|ind_bodies mdecl| - S (inductive_ind ind) + #|ind_params mdecl| + #|arity|) in
  let s := (inds (inductive_mind ind) u (ind_bodies mdecl)) in
  inductive_ind ind < #|ind_bodies mdecl| ->
  subst s (#|arity| + #|ind_params mdecl|)
        (subst_instance_constr u (mkApps head (to_extended_list_k (ind_params mdecl) #|arity| ++ args)))
  = mkApps (tInd ind u) (to_extended_list_k (ind_params mdecl) #|arity| ++
                        map (subst s (#|arity| + #|ind_params mdecl|)) (map (subst_instance_constr u) args)).
Proof.
  intros.
  rewrite subst_instance_constr_mkApps subst_mkApps.
  f_equal.
  - subst head. simpl subst_instance_constr.
    rewrite (subst_rel_eq _ _ (#|ind_bodies mdecl| - S (inductive_ind ind)) (tInd ind u)) //; try lia.
    subst s. rewrite inds_alt rev_mapi nth_error_mapi /=.
    elim nth_error_spec. intros. simpl.
    f_equal. destruct ind; simpl. f_equal. f_equal. simpl in H. lia.
    rewrite List.rev_length. lia.
  - rewrite !map_app. f_equal.
    -- rewrite map_subst_instance_constr_to_extended_list_k.
       erewrite to_extended_list_k_map_subst at 2.
       now rewrite Nat.add_comm. lia.
Qed.

Lemma decompose_app_mkApps f l :
  isApp f = false -> decompose_app (mkApps f l) = (f, l).
Proof.
  intros.
  destruct l; simpl;
    destruct f; simpl; try (discriminate || reflexivity).
Qed.

Fixpoint reln_alt p Γ :=
  match Γ with
  | [] => []
  | {| decl_body := Some _ |} :: Γ => reln_alt (p + 1) Γ
  | {| decl_body := None |} :: Γ => tRel p :: reln_alt (p + 1) Γ
  end.

Lemma reln_alt_eq l Γ k : reln l k Γ = List.rev (reln_alt k Γ) ++ l.
Proof.
  induction Γ in l, k |- *; simpl; auto.
  destruct a as [na [body|] ty]; simpl.
  now rewrite IHΓ.
  now rewrite IHΓ -app_assoc.
Qed.

Lemma to_extended_list_k_cons d Γ k :
  to_extended_list_k (d :: Γ) k =
  match d.(decl_body) with
  | None => to_extended_list_k Γ (S k) ++ [tRel k]
  | Some b => to_extended_list_k Γ (S k)
  end.
Proof.
  rewrite /to_extended_list_k reln_alt_eq. simpl.
  destruct d as [na [body|] ty]. simpl.
  now rewrite reln_alt_eq Nat.add_1_r.
  simpl. rewrite reln_alt_eq.
  now rewrite -app_assoc !app_nil_r Nat.add_1_r.
Qed.

Lemma lift_to_extended_list_k Γ k : forall k',
    to_extended_list_k Γ (k' + k) = map (lift0 k') (to_extended_list_k Γ k).
Proof.
  unfold to_extended_list_k.
  intros k'. rewrite !reln_alt_eq !app_nil_r.
  induction Γ in k, k' |- *; simpl; auto.
  destruct a as [na [body|] ty].
  now rewrite -Nat.add_assoc (IHΓ (k + 1) k').
  simpl. now rewrite -Nat.add_assoc (IHΓ (k + 1) k') map_app.
Qed.

Lemma subst_to_extended_list_k s k args ctx :
  Forall Ast.wf s ->
  make_context_subst (List.rev ctx) args [] = Some s ->
  map (subst s k) (to_extended_list_k ctx k) = map (lift0 k) args.
Proof.
  move=> wfs.
  move/make_context_subst_spec. rewrite List.rev_involutive.
  move=> H; induction H; simpl; auto.
  - inv wfs.
    rewrite map_app -IHcontext_subst //.
    rewrite to_extended_list_k_cons /= !map_app.
    f_equal.
    rewrite (lift_to_extended_list_k _ _ 1) map_map_compose.
    pose proof (to_extended_list_k_spec Γ k).
    apply_spec. intros x [n [-> Hn]].
    rewrite /compose /lift (subst_app_decomp [a] s k); auto with wf.
    rewrite subst_rel_gt. simpl; lia.
    repeat (f_equal; simpl; try lia).
    now rewrite /map (subst_rel_eq _ _ 0 a).
  - inv wfs.
    rewrite -IHcontext_subst // to_extended_list_k_cons /=.
    rewrite (lift_to_extended_list_k _ _ 1) map_map_compose.
    pose proof (to_extended_list_k_spec Γ k).
    apply_spec. intros x [n [-> Hn]].
    rewrite /compose /lift (subst_app_decomp [subst0 s b] s k); auto with wf.
    rewrite subst_rel_gt. simpl; lia.
    repeat (f_equal; simpl; try lia).
Qed.

Lemma wf_context_subst ctx args s :
  Forall wf_decl ctx -> Forall Ast.wf args ->
  context_subst ctx args s -> Forall Ast.wf s.
Proof.
  move=> wfctx wfargs.
  induction 1. constructor.
  eapply Forall_app in wfargs as [wfargs wfa]. inv wfa. inv wfctx.
  constructor; intuition auto.
  inv wfctx. red in H0. constructor; intuition auto with wf.
Qed.

Lemma wf_make_context_subst ctx args s' :
  Forall wf_decl ctx -> Forall Ast.wf args ->
  make_context_subst (List.rev ctx) args [] = Some s' -> Forall Ast.wf s'.
Proof.
  move=> wfctx wfargs.
  move/make_context_subst_spec. rewrite rev_involutive.
  eauto using wf_context_subst.
Qed.

Lemma chop_n_app {A} {l l' : list A} {n} : n = length l -> chop n (l ++ l') = (l, l').
Proof.
  intros ->. induction l; simpl; try congruence.
  now rewrite IHl.
Qed.

(** check_correct_arity is probably wrong, w.r.t. let-ins reduced or not at least  *)
Lemma subst_types_of_case `{cf:checker_flags} Σ ind mdecl idecl args u p pty indctx pctx ps btys n k :
  let f (ctx : context) := subst n (#|ctx| + k) in
  let f_ctx := subst_context n k in
  wf Σ ->
  Forall Ast.wf n -> Forall Ast.wf args ->
  Ast.wf pty -> Ast.wf (ind_type idecl) ->
  declared_inductive (fst Σ) ind mdecl idecl ->
  types_of_case ind mdecl idecl args u p pty = Some (indctx, pctx, ps, btys) ->
  types_of_case ind mdecl idecl (map (f []) args) u (f [] p) (f [] pty) =
  Some (f_ctx indctx, f_ctx pctx, ps, map (on_snd (f [])) btys).
Proof.
  simpl. intros wfΣ wfn wfargs wfpty wfdecl wfidecl. simpl.
  epose proof (subst_declared_inductive _ ind mdecl idecl n k wfΣ).
  forward H. auto. rewrite <- H at 2.
  unfold types_of_case.
  pose proof (subst_destArity [] (ind_type idecl) n k wfdecl); trivial. simpl in H.
  unfold subst_context, fold_context in H0. simpl in H0. rewrite ind_type_map. simpl.
  destruct destArity as [[ctx s] | ]; try congruence.
  rewrite H0. clear H0.
  pose proof (subst_destArity [] pty n k wfpty); trivial. simpl in H.
  destruct (destArity [] pty) as [[ctx' s'] | ]; try congruence.
  unfold subst_context at 1 in H0. unfold fold_context in H0. simpl in H0.
  rewrite H0; clear H0.
  destruct map_option_out eqn:Hbrs; try congruence.
  intros [= -> -> -> ->].
  pose proof (on_declared_inductive _ _ _ _ wfΣ wfidecl) as [onmind onind].
  pose proof (onParams _ _ _ _ onmind) as Hparams.
  assert(closedparams : closed_ctx (ind_params mdecl)).
  eapply closed_wf_local; eauto.
  assert(wfparams : Forall wf_decl (ind_params mdecl)).
  eapply typing_all_wf_decl; eauto.
  assert(forall brs,
         build_branches_type ind mdecl idecl args u p = brs ->
         (build_branches_type ind mdecl
         (map_one_inductive_body (inductive_mind ind) (polymorphic_instance (ind_universes mdecl))
            (length (arities_context (ind_bodies mdecl))) (fun k' => subst n (k' + k))
            (inductive_ind ind) idecl) (map (subst n k) args) u (subst n k p)) =
         map (option_map (on_snd (subst n k))) brs).
  { intros brs <-.
    unfold build_branches_type.
    rewrite ind_ctors_map.
    rewrite mapi_map map_mapi.
    apply onConstructors in onind.
    red in onind. eapply (Alli_mapi_spec onind). clear onind.
    intros i [[id t] arity]. simpl.
    rewrite <- subst_subst_instance_constr.
    rewrite -> substl_inds_subst.
    assert (Hn:map (UnivSubst.subst_instance_constr u) n = n). admit.
    rewrite Hn. clear Hn.
    intros Honc.
    pose proof (on_constructor_closed wfΣ (u:=u) Honc).
    simpl in H0.
    rewrite <- subst_instantiate_params; auto with wf.
    remember (substl (inds (inductive_mind ind) u (ind_bodies mdecl)) (subst_instance_constr u t)) as
        ty.
    destruct (instantiate_params (ind_params mdecl) args ty) eqn:Heq; auto.
    eapply instantiate_params_make_context_subst in Heq.
    destruct Heq as [ctx' [ty'' [s' [Hty [Hsubst Ht0]]]]].
    subst t0. simpl.

    rewrite Heqty in Hty.
    destruct Honc. destruct c.
    simpl in *. rewrite cshape_eq in Hty.
    rewrite -> !subst_instance_constr_it_mkProd_or_LetIn in Hty.
    unfold substl in Hty. rewrite !subst_it_mkProd_or_LetIn in Hty.
    assert(#|subst_context (inds (inductive_mind ind) u (ind_bodies mdecl)) 0
             (subst_instance_context u (ind_params mdecl))| = #|ind_params mdecl|).
    now rewrite subst_context_length subst_instance_context_length.
    rewrite <- H1 in Hty.
    rewrite decompose_prod_n_assum_it_mkProd in Hty.
    injection Hty. clear Hty.
    intros Heqty'' <-. revert Heqty''.
    rewrite !subst_instance_context_length Nat.add_0_r.

    rewrite (subst_cstr_concl_head ind u mdecl cshape_arity cshape_args).
    destruct wfidecl as [Hmdecl Hnth].
    now apply nth_error_Some_length in Hnth.
    intros <-. rewrite !subst_it_mkProd_or_LetIn !subst_mkApps /=.
    rewrite !decompose_prod_assum_it_mkProd /=; try by rewrite is_ind_app_head_mkApps.
    rewrite !decompose_app_mkApps; try by reflexivity.
    simpl. rewrite !map_app !subst_context_length !subst_instance_context_length Nat.add_0_r.
    rewrite !(subst_to_extended_list_k _ _ args) //.
    eapply wf_make_context_subst in Hsubst; eauto.

    pose proof Hsubst as Hsubst'.
    apply make_context_subst_spec in Hsubst'.
    rewrite rev_involutive in Hsubst'.
    pose proof (context_subst_assumptions_length _ _ _ Hsubst').

    symmetry.
    case E: chop => [l l'].
    have chopm := (chop_map _ _ _ _ _ E).
    move: E chopm.
    rewrite chop_n_app ?map_length.
    rewrite <- H2. apply onNpars in onmind. lia.
    move=> [= <- <-] chopm.
    symmetry.
    move: {chopm}(chopm _ (subst n (#|cshape_arity| + k))).
    rewrite map_app.
    move=> chopm; rewrite {}chopm /=.
    rewrite !app_nil_r /on_snd /=.
    rewrite subst_it_mkProd_or_LetIn !subst_context_length !subst_mkApps
            !subst_instance_context_length !map_app.
    f_equal. f_equal. f_equal. f_equal.
    2:{ f_equal. simpl. f_equal.
        rewrite !subst_mkApps /= !map_app. f_equal.
        f_equal.
        rewrite /to_extended_list -to_extended_list_k_map_subst.
        rewrite !subst_context_length subst_instance_context_length. lia.
        now rewrite to_extended_list_k_subst. }
    rewrite commut_lift_subst_rec. lia. reflexivity.
    unfold substl. apply wf_subst. apply wf_inds. apply wf_subst_instance_constr.
    destruct Honc as [[s' Hty] _]. simpl in Hty. eapply typing_wf in Hty; intuition eauto with wf.
    apply Forall_map. eapply Forall_impl; eauto. apply wf_subst_instance_constr. }
  specialize (H0 _ eq_refl). rewrite H0.
  rewrite map_option_out_map_option_map. rewrite Hbrs.
  simpl. f_equal.
Admitted. (* only remaining goal is for subst_instance_constr in the substitution n *)

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
  eapply nth_error_app_left in Heq. now rewrite -> Heq. discriminate.

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
         rewrite -> nth_error_app_ge in H by lia.
         rewrite -> nth_error_app_lt in H by lia.
         destruct nth_error eqn:HΓ'.
         eapply subs_nth_error in Heq; eauto.
         simpl in H. destruct decl_body; try contradiction.
         discriminate. discriminate.
      ++ apply nth_error_None in Heq.
         assert(S i = #|s| + (S (i - #|s|))) by lia.
         rewrite H1. rewrite -> simpl_subst; try lia.
         econstructor.
         rewrite -> nth_error_app_ge in H by lia.
         rewrite -> nth_error_app_ge in H by lia.
         rewrite -> nth_error_app_ge. 2:(autorewrite with wf; lia).
         rewrite <- H. f_equal. f_equal. autorewrite with wf. lia.
         rewrite -> !nth_error_app_ge in H by lia.
         destruct nth_error eqn:Hi.
         eapply nth_error_All_local_env in wfΓ. red in wfΓ.
         rewrite -> Hi in wfΓ. simpl in H.
         destruct c; simpl in H; try discriminate.
         injection H. intros ->. red in wfΓ. cbn in *. apply typing_wf in wfΓ. intuition eauto. eauto.
         eapply typing_wf_local in wfΓ; eauto.
         apply nth_error_Some_length in Hi. lia. discriminate.
    + rewrite -> nth_error_app_lt in H by lia.
      pose (commut_lift_subst_rec body s (S i) (#|Γ''| - S i) 0).
      assert(eq:(S i + (#|Γ''| - S i)) = #|Γ''|) by lia.
      rewrite -> eq in e. rewrite <- e by lia.
      constructor.
      rewrite -> nth_error_app_lt by (autorewrite with wf; lia).
      rewrite -> nth_error_subst_context.
      unfold subst_decl; now rewrite -> option_map_decl_body_map_decl, H, Nat.add_0_r.

  - rewrite subst_iota_red.
    constructor.

  - inv wfM. rewrite mkApps_tApp; simpl; auto with wf.
    rewrite -> mkApps_tApp; simpl; auto with wf.
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
    now rewrite nth_error_map H.

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
  unfold eq_ind. now rewrite eq_string_refl Nat.eqb_refl.
Qed.

Lemma eq_nat_refl n : eq_nat n n = true.
Proof. by rewrite /eq_nat Nat.eqb_refl. Qed.

Lemma eq_projection_refl i : eq_projection i i = true.
Proof.
  destruct i as [[mind k] p].
  unfold eq_projection.
  now rewrite eq_ind_refl !eq_nat_refl.
Qed.

Lemma eq_term_refl `{checker_flags} φ t : eq_term φ t t = true.
Proof.
  induction t using term_forall_list_ind; simpl; try reflexivity; try discriminate;
    try (merge_Forall; close_Forall; intuition auto);
    try (rewrite -> ?IHt1, ?IHt2, ?IHt3; reflexivity).

  - apply Nat.eqb_refl.
  - apply eq_string_refl.
  - apply Nat.eqb_refl.
  - rewrite /eq_evar eq_nat_refl.
    simpl. induction H0; simpl; auto. now rewrite H0 IHForall.
  - apply eq_universe_refl.
  - rewrite IHt; simpl.
    eapply (Forall_forallb _ _ (fun x => eq_term φ x x)) in H0.
    induction l; simpl; auto.
    simpl in H0. rewrite -> andb_true_iff in H0. intuition.
    auto.
  - unfold eq_constant. rewrite eq_string_refl.
    apply eq_universe_instance_refl.
  - rewrite eq_ind_refl. apply eq_universe_instance_refl.
  - rewrite eq_ind_refl. rewrite /eq_nat Nat.eqb_refl. apply eq_universe_instance_refl.
  - destruct p. simpl.
    rewrite eq_ind_refl eq_nat_refl IHt1 IHt2.
    simpl. induction l.
    reflexivity.
    simpl. destruct a. inv H0. simpl in H1. rewrite H1.
    rewrite IHl; auto.
  - now rewrite eq_projection_refl IHt.
  - rewrite eq_nat_refl.
    induction m. reflexivity.
    inv H0. intuition.
    simpl. rewrite H0 H3. simpl. apply H1.
  - rewrite Nat.eqb_refl.
    induction m. reflexivity.
    inv H0. intuition.
    simpl. rewrite H0 H3. simpl. apply H1.
Qed.

Lemma eq_term_leq_term `{checker_flags} φ t u : eq_term φ t u = true -> leq_term φ t u = true.
Proof.
  induction t in u |- * using term_forall_list_ind; simpl; intros; auto; try reflexivity; try discriminate;
    try (merge_Forall; close_Forall; intuition auto);
    try (rewrite -> ?IHt1, ?IHt2, ?IHt3; reflexivity).

  - destruct u; auto. now apply eq_universe_leq_universe.
  - destruct u; try discriminate.
    rewrite -> andb_true_iff in *. intuition.
  - destruct u; try discriminate.
    rewrite -> andb_true_iff in *. intuition.
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
  pose (eq_term_App _ _ _ H0). rewrite -> Hf in e.
  destruct f; try discriminate.
  destruct f'; try discriminate.
  simpl in *.
  rewrite -> andb_true_iff in *. intuition.
  rewrite forallb2_app; auto.
  simpl. now rewrite H3 H0 H4.

  rewrite -> !mkApps_tApp; auto. simpl. rewrite -> H0.
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
  pose (eq_term_App _ _ _ H0). rewrite -> Hf in e.
  destruct f; try discriminate.
  destruct f'; try discriminate.
  simpl in *.
  rewrite -> andb_true_iff in *. intuition.
  rewrite forallb2_app; auto.
  simpl. now rewrite H3 H0 H4.

  rewrite -> !mkApps_tApp; auto. simpl. rewrite H0.
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
  simpl in *; revert Hleq; try rewrite -> !andb_true_iff in *; intuition auto;
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
  - destruct p, p0. rewrite -> !andb_true_iff in *. intuition auto.
    red in H0. merge_Forall. close_Forall. intuition auto. destruct y. simpl. auto.
  - rewrite -> !andb_true_iff in *.
    destruct x, y; simpl in *; intuition auto.
    assert (#|m| = #|m0|). clear -H2. induction H2; simpl; auto. rewrite H4. auto.
  - rewrite -> !andb_true_iff in *.
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
  simpl in *; revert Hleq; try destruct p, p0; try rewrite -> !andb_true_iff in *;
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
  - rewrite -> !andb_true_iff in *.
    destruct x, y; simpl in *; intuition auto using subst_eq_term.
    assert (#|m| = #|m0|). clear -H2. induction H2; simpl; auto. rewrite H4.
    auto using subst_eq_term.
  - rewrite -> !andb_true_iff in *.
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
  simpl in *. rewrite -> andb_true_iff in *.
  intuition. unfold eq_context in H2. apply forallb2_length in H2. rewrite <- H2.
  destruct a, c; try congruence.
  unfold eq_decl in *. simpl.
  destruct decl_body, decl_body0; simpl in *; try congruence.
  simpl in *. rewrite -> andb_true_iff in *.
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
  rewrite -> !andb_true_iff. intros.
  destruct H. split.
  destruct c. destruct decl_body; try discriminate.
  unfold eq_decl in *. simpl in *.
  assert (#|indctx| = #|pctx|) by now eapply forallb2_length in H0.
  rewrite <- H1.
  clear H0.
  eapply (subst_eq_term _ s (#|indctx| + k)) in H.
  rewrite subst_mkApps map_app in H. simpl in H.
  rewrite firstn_map. rewrite /to_extended_list to_extended_list_k_subst.
  unfold to_extended_list in H.
  erewrite <- (to_extended_list_k_map_subst s) in H.
  rewrite <- H. f_equal. f_equal. f_equal. rewrite subst_context_length.
  rewrite -> !map_map_compose. apply map_ext.
  intros. unfold compose. now rewrite commut_lift_subst_rec. lia.
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
  rewrite -> mkApp_tApp; eauto.
  econstructor; eauto. congruence.
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
      rewrite -> Typing.nth_error_app_ge in H0 by lia.
      rewrite -> Typing.nth_error_app_lt in H0 by lia.
      eapply subs_nth_error in Heq; eauto.
      destruct decl_body; try contradiction.
      cbn -[skipn] in Heq.
      eapply refine_type.
      eapply (weakening _ _ (subst_context s 0 Δ)) in Heq; eauto with wf.
      rewrite subst_context_length in Heq. eapply Heq.
      unfold substl. rewrite -> commut_lift_subst_rec by lia.
      rewrite Nat.add_0_r.
      rewrite <- (firstn_skipn (S (n - #|Δ|)) s) at 2.
      rewrite -> subst_app_decomp. f_equal.
      replace (S n) with ((S n - #|Δ|) + #|Δ|) by lia.
      assert (eq:#|(map (lift0 #|skipn (S (n - #|Δ|)) s|) (firstn (S (n - #|Δ|)) s))| = S n - #|Δ|).
      rewrite map_length. rewrite -> firstn_length by lia. lia.
      rewrite <- eq. rewrite -> simpl_subst_rec; auto; try lia.
      auto with wf. eapply subs_wf in sub; eauto.
      now apply Forall_firstn.

    + intros Hs.
      pose proof (subst_length _ _ _ _ sub).
      rewrite H1 in Hs.
      assert (S n = #|s| + (S (n - #|s|))) by lia.
      rewrite H2. rewrite simpl_subst; auto; try lia.
      constructor; auto.
      rewrite -> nth_error_app_ge; try lia; rewrite subst_context_length.
      rewrite -> 2!nth_error_app_ge in H0 by lia.
      rewrite <- H0. f_equal. lia.
      lia.

    + eapply subs_nth_error_lt in sub; eauto.
      rewrite H0 in sub. simpl in sub.
      eapply refine_type. constructor; eauto.
      rewrite <- map_decl_type.
      rewrite -> commut_lift_subst_rec by lia.
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
    unfold subst1 in IHX1 |- *. rewrite -> distr_subst in IHX1.
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
    eapply subst_declared_inductive in isdecl; eauto.
    erewrite <- (ind_type_map (fun Γ t => subst s (Γ + #|Δ|) t)).
    f_equal. symmetry. apply isdecl.

  - eapply refine_type. econstructor; eauto.
    assert (s = map (UnivSubst.subst_instance_constr u) s). admit.
    rewrite H1.
    erewrite (subst_declared_constructor _ (ind, i) u mdecl idecl cdecl _ _ wfΣ); eauto.
    (* eauto with wf. loops!*)
    eauto using subs_wf.

  - rewrite subst_mkApps map_app map_skipn.
    specialize (X1 Γ Γ' Δ s sub eq_refl wfsubs).
    specialize (X4 Γ Γ' Δ s sub eq_refl wfsubs).
    specialize (X2 Γ Γ' Δ s sub eq_refl wfsubs).
    simpl. econstructor.
    5:{ eapply subst_types_of_case in H3.
        simpl in H3. subst pars. rewrite firstn_map. eapply H3; eauto.
        all:eauto.
        -- now apply subs_wf in sub.
        -- subst pars. eapply Forall_firstn.
           apply typing_wf in X3 as [_ X3]; eauto.
           now apply wf_mkApps_inv in X3.
        -- eapply typing_wf in X0; wf.
        -- eapply on_declared_inductive in H1 as [Hmdecl Hidecl]; auto.
           apply onArity in Hidecl as [[s' Hty] _]. now eapply typing_wf in Hty; eauto. }
    -- eauto.
    -- eauto.
    -- eauto.
    -- eauto.
    -- revert H4. subst pars.
       apply subst_check_correct_arity.
    -- destruct idecl; simpl in *; auto.
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
    rewrite List.rev_length UnivSubst.subst_subst_instance_constr.
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
      rewrite app_context_length subst_context_app app_context_assoc Nat.add_0_r in IHt.
      unfold snoc; rewrite subst_context_snoc; econstructor; auto;
        apply IHt; apply All_local_env_app_inv; intuition.
    + destruct t0 as [Ht IHt].
       specialize (IHt Γ Γ' (Δ ,,, Γ0) s sub). forward IHt. now rewrite app_context_assoc.
       rewrite app_context_length subst_context_app app_context_assoc Nat.add_0_r in IHt.
       unfold snoc; rewrite subst_context_snoc; econstructor; auto;
       apply IHt; apply All_local_env_app_inv; intuition.
    + erewrite map_dtype. eapply type_Fix.
      * rewrite nth_error_map H0. reflexivity.
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
        rewrite !app_context_assoc Nat.add_0_r !app_context_length fix_context_length in IH.
        specialize (IH X1).
        rewrite subst_context_length fix_context_length.
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
      rewrite app_context_length subst_context_app app_context_assoc Nat.add_0_r in IHt.
      unfold snoc; rewrite subst_context_snoc; econstructor; auto;
        apply IHt; apply All_local_env_app_inv; intuition.
    + destruct t0 as [Ht IHt].
       specialize (IHt Γ Γ' (Δ ,,, Γ0) s sub). forward IHt. now rewrite app_context_assoc.
       rewrite app_context_length subst_context_app app_context_assoc Nat.add_0_r in IHt.
       unfold snoc; rewrite subst_context_snoc; econstructor; auto;
       apply IHt; apply All_local_env_app_inv; intuition.
    + erewrite map_dtype. eapply type_CoFix.
      * rewrite nth_error_map H0. reflexivity.
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
        rewrite !app_context_assoc Nat.add_0_r !app_context_length fix_context_length in IH.
        specialize (IH X1).
        rewrite subst_context_length fix_context_length.
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