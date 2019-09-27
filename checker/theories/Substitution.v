(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia.
From MetaCoq.Template Require Import config utils Ast AstUtils Induction utils LiftSubst UnivSubst.
From MetaCoq.Checker Require Import Typing TypingWf Generation WeakeningEnv Closed Weakening.
Require Import ssreflect.

(** * Substitution lemmas for typing derivations. *)

Set Asymmetric Patterns.
Close Scope string_scope.

Generalizable Variables Σ Γ t T.

Definition subst_decl s k (d : context_decl) := map_decl (subst s k) d.

Definition subst_context n k (Γ : context) : context :=
  fold_context (fun k' => subst n (k' + k)) Γ.

(** Well-typed substitution into a context with *no* let-ins *)

Inductive subs `{cf : checker_flags} Σ (Γ : context) : list term -> context -> Type :=
| emptys : subs Σ Γ [] []
| cons_ass Δ s na t T : subs Σ Γ s Δ ->
              Σ ;;; Γ |- t : subst0 s T ->
             subs Σ Γ (t :: s) (Δ ,, vass na T).
(* | cons_let Δ s na t T : subs Σ Γ s Δ -> *)
(*               Σ ;;; Γ |- subst0 s t : subst0 s T -> *)
(*               subs Σ Γ (subst0 s t :: s) (Δ ,, vdef na t T). *)

(** Linking a context (with let-ins), an instance (reversed substitution)
    for its assumptions and a well-formed substitution for it. *)

Inductive context_subst : context -> list term -> list term -> Set :=
| context_subst_nil : context_subst [] [] []
| context_subst_ass Γ args s na t a :
    context_subst Γ args s ->
    context_subst (vass na t :: Γ) (args ++ [a]) (a :: s)
| context_subst_def Γ args s na b t :
    context_subst Γ args s ->
    context_subst (vdef na b t :: Γ) args (subst s 0 b :: s).

(** Promoting a substitution for the non-let declarations of ctx into a
    substitution for the whole context *)

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

Lemma subst_decl0 Γ k d : on_local_decl wf_decl_pred Γ d -> map_decl (subst [] k) d = d.
Proof.
  unfold wf_decl_pred; intros Hd; destruct d; destruct decl_body;
    unfold on_local_decl in Hd; unfold subst_decl, map_decl; simpl in *;
    f_equal; simpl; rewrite subst_empty; intuition trivial.
Qed.

Lemma subst0_context k Γ : All_local_env wf_decl_pred Γ -> subst_context [] k Γ = Γ.
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
  unfold fold_context. now rewrite !List.rev_length mapi_length List.rev_length.
Qed.

Lemma subst_context_length s k Γ : #|subst_context s k Γ| = #|Γ|.
Proof.
  unfold subst_context. apply fold_context_length.
Qed.
Hint Rewrite subst_context_length : subst.

Lemma subst_context_snoc s k Γ d : subst_context s k (d :: Γ) = subst_context s k Γ ,, subst_decl s (#|Γ| + k) d.
Proof.
  unfold subst_context, fold_context.
  rewrite !rev_mapi !rev_involutive /mapi mapi_rec_eqn /snoc.
  f_equal. now rewrite Nat.sub_0_r List.rev_length.
  rewrite mapi_rec_Sk. simpl. apply mapi_rec_ext. intros.
  rewrite app_length !List.rev_length. simpl. f_equal. f_equal. lia.
Qed.
Hint Rewrite subst_context_snoc : subst.

Lemma subst_context_snoc0 s Γ d : subst_context s 0 (Γ ,, d) = subst_context s 0 Γ ,, subst_decl s #|Γ| d.
Proof.
  unfold snoc. now rewrite subst_context_snoc Nat.add_0_r.
Qed.
Hint Rewrite subst_context_snoc : subst.

Lemma subst_context_alt s k Γ :
  subst_context s k Γ =
  mapi (fun k' d => subst_decl s (Nat.pred #|Γ| - k' + k) d) Γ.
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

Lemma map_vass_map_def g l n k :
  (mapi (fun i (d : def term) => vass (dname d) (lift0 i (dtype d)))
        (map (map_def (subst n k) g) l)) =
  (mapi (fun i d => map_decl (subst n (i + k)) d) (mapi (fun i (d : def term) => vass (dname d) (lift0 i (dtype d))) l)).
Proof.
  rewrite mapi_mapi mapi_map. apply mapi_ext.
  intros. unfold map_decl, vass; simpl; f_equal.
  rewrite commut_lift_subst_rec. lia. f_equal; lia.
Qed.

Lemma All_local_env_subst  (P Q : context -> term -> option term -> Type) c n k :
  All_local_env Q c ->
  (forall Γ t T,
      Q Γ t T ->
      P (subst_context n k Γ) (subst n (#|Γ| + k) t)
        (option_map (subst n (#|Γ| + k)) T)
  ) ->
  All_local_env P (subst_context n k c).
Proof.
  intros Hq Hf.
  induction Hq in |- *; try econstructor; eauto;
    simpl; unfold snoc; rewrite subst_context_snoc; econstructor; eauto.
  - simpl. eapply (Hf _ _ None). eauto.
  - simpl. eapply (Hf _ _ None). eauto.
  - simpl. eapply (Hf _ _ (Some t)). eauto.
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
  All Ast.wf n ->
  unfold_fix mfix idx = Some (narg, fn) ->
  unfold_fix (map (map_def (subst n k) (subst n (#|mfix| + k))) mfix) idx = Some (narg, subst n k fn).
Proof.
  unfold unfold_fix. intros wfn.
  rewrite nth_error_map. destruct (nth_error mfix idx) eqn:Hdef; try congruence.
  move=> [= <- <-] /=. f_equal. f_equal.
  solve_all.
  erewrite (distr_subst_rec _ _ _ wfn k 0).
  rewrite fix_subst_length. simpl. f_equal.
  unfold fix_subst. rewrite !map_length.
  generalize #|mfix| at 2 3. induction n0; auto. simpl.
  f_equal. apply IHn0.
Qed.
Hint Resolve subst_unfold_fix.

Lemma subst_unfold_cofix n k mfix idx narg fn :
  All Ast.wf n ->
  unfold_cofix mfix idx = Some (narg, fn) ->
  unfold_cofix (map (map_def (subst n k) (subst n (#|mfix| + k))) mfix) idx = Some (narg, subst n k fn).
Proof.
  unfold unfold_cofix. intros wfn.
  rewrite nth_error_map. destruct (nth_error mfix idx) eqn:Hdef; try congruence.
  intros [= <- <-]. simpl. do 2 f_equal. solve_all.
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
  destruct args0; auto.
Qed.
Hint Resolve subst_is_constructor.
Hint Constructors All_local_env.

Lemma typed_subst `{checker_flags} Σ Γ t T n k :
  wf Σ.1 -> k >= #|Γ| ->
  Σ ;;; Γ |- t : T -> subst n k T = T /\ subst n k t = t.
Proof.
  intros wfΣ Hk Hty.
  pose proof (typing_wf_local Hty).
  pose proof (typing_wf _ wfΣ _ _ _ Hty) as [wft wfT].
  apply typecheck_closed in Hty; eauto.
  destruct Hty as [_ Hcl].
  rewrite -> andb_and in Hcl. destruct Hcl as [clb clty].
  pose proof (closed_upwards k clb).
  simpl in *. forward H0 by lia.
  pose proof (closed_upwards k clty).
  simpl in *. forward H1 by lia.
  apply (subst_closedn n) in H0; apply (subst_closedn n) in H1; auto.
Qed.

Lemma subst_wf_local `{checker_flags} Σ Γ n k :
  wf Σ.1 ->
  wf_local Σ Γ ->
  subst_context n k Γ = Γ.
Proof.
  intros wfΣ.
  induction 1; auto; unfold subst_context, snoc; rewrite fold_context_snoc0;
    auto; unfold snoc;
    f_equal; auto; unfold map_decl; simpl.
  - destruct t0 as [s Hs]. unfold vass. simpl. f_equal.
    eapply typed_subst; eauto. lia.
  - unfold vdef.
    f_equal.
    + f_equal. eapply typed_subst; eauto. lia.
    + eapply typed_subst in t1 as [Ht HT]; eauto. lia.
Qed.

Lemma subst_declared_constant `{H:checker_flags} Σ cst decl n k u :
  wf Σ ->
  declared_constant Σ cst decl ->
  map_constant_body (subst n k) (map_constant_body (UnivSubst.subst_instance_constr u) decl) =
  map_constant_body (UnivSubst.subst_instance_constr u) decl.
Proof.
  intros.
  eapply declared_decl_closed in H0; eauto.
  unfold map_constant_body.
  do 2 red in H0. destruct decl as [ty [body|] univs]; simpl in *.
  rewrite -> andb_and in H0. intuition.
  rewrite <- (closedn_subst_instance_constr 0 body u) in H2.
  rewrite <- (closedn_subst_instance_constr 0 ty u) in H4.
  f_equal. apply subst_closedn; eauto using closed_upwards with arith wf.
  f_equal. apply subst_closedn; eauto using closed_upwards with arith wf.
  red in H0. f_equal.
  intuition. simpl in H3.
  rewrite <- (closedn_subst_instance_constr 0 ty u) in H3.
  eapply subst_closedn; eauto using closed_upwards with arith wf.
  rewrite andb_true_r in H3. eauto using closed_upwards with arith wf.
Qed.

Definition subst_mutual_inductive_body n k m :=
  map_mutual_inductive_body (fun k' => subst n (k' + k)) m.

Lemma subst_declared_minductive `{cf:checker_flags} Σ cst decl n k :
  wf Σ ->
  declared_minductive Σ cst decl ->
  subst_mutual_inductive_body n k decl = decl.
Proof.
  unfold declared_minductive.
  intros.
  eapply lookup_on_global_env in H; eauto.
  destruct H as [Σ' [wfΣ' decl']].
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
    destruct onArity as [s Hs].
    eapply typed_subst; eauto. simpl; lia.
    rewrite H in Heq'. rewrite Heq in Heq'. revert Heq'; intros [= <- <-].
    f_equal; auto.
    apply (Alli_map_id onConstructors).
    intros n1 [[x p] n']. intros [[s Hty] Hpars].
    unfold on_pi2; f_equal; f_equal. eapply typed_subst. 3:eapply Hty. eauto. simpl. lia.
    assert((ind_projs = []) + (ind_projs <> [])) as [Hp|Hp].
    { destruct ind_projs; [left|right]; congruence. }
    subst; auto.
    specialize (onProjections Hp).
    apply on_projs in onProjections.
    apply (Alli_map_id onProjections).
    intros n1 [x p]. unfold on_projection; simpl.
    intros [s Hty].
    unfold on_snd; f_equal; f_equal.
    eapply typed_subst. 3:eapply Hty. eauto. simpl.
    rewrite smash_context_length context_assumptions_fold. simpl; lia.
Qed.

Lemma subst_declared_inductive `{checker_flags} Σ ind mdecl idecl n k :
  wf Σ ->
  declared_inductive Σ mdecl ind idecl ->
  map_one_inductive_body (context_assumptions mdecl.(ind_params))
                         (length (arities_context mdecl.(ind_bodies)))
                         (fun k' => subst n (k' + k)) (inductive_ind ind) idecl = idecl.
Proof.
  unfold declared_inductive. intros wfΣ [Hmdecl Hidecl].
  eapply (subst_declared_minductive _ _ _ n k) in Hmdecl.
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

Lemma subst0_inds_subst ind u mdecl n k t :
  All Ast.wf n ->
  (subst0 (inds (inductive_mind ind) u (ind_bodies mdecl))
          (subst n (#|arities_context (ind_bodies mdecl)| + k) t)) =
  subst n k (subst0 (inds (inductive_mind ind) u (ind_bodies mdecl)) t).
Proof.
   intros wfn.
  pose proof (distr_subst_rec t (inds (inductive_mind ind) u (ind_bodies mdecl)) n wfn k 0).
  simpl in H. rewrite H.
  unfold arities_context. rewrite rev_map_length inds_length.
  f_equal. generalize (ind_bodies mdecl).
  clear. intros.
  induction l; unfold inds; simpl; auto. f_equal. auto.
Qed.

Lemma subst_declared_constructor `{cf:checker_flags} Σ c u mdecl idecl cdecl n k :
  wf Σ -> All Ast.wf n ->
  declared_constructor Σ mdecl idecl c cdecl ->
  subst (map (UnivSubst.subst_instance_constr u) n) k (type_of_constructor mdecl cdecl c u) = (type_of_constructor mdecl cdecl c u).
Proof.
  unfold declared_constructor. destruct c as [i ci].
  intros wfΣ wfn [Hidecl Hcdecl].
  eapply (subst_declared_inductive _ _ _ _ n k) in Hidecl; eauto.
  unfold type_of_constructor. destruct cdecl as [[id t'] arity].
  destruct idecl; simpl in *.
  injection Hidecl. intros.
  pose Hcdecl as Hcdecl'.
  rewrite <- H0 in Hcdecl'.
  rewrite nth_error_map in Hcdecl'. rewrite Hcdecl in Hcdecl'.
  simpl in Hcdecl'. injection Hcdecl'.
  intros.
  rewrite <- H2 at 2.
  rewrite <- subst0_inds_subst. f_equal.
  now rewrite <- subst_subst_instance_constr.
  apply All_map. unfold compose. eapply All_impl; eauto.
  intros. now apply wf_subst_instance_constr.
Qed.

Lemma subst_declared_projection `{checker_flags} Σ c mdecl idecl pdecl n k :
  wf Σ -> All Ast.wf n ->
  declared_projection Σ mdecl idecl c pdecl ->
  on_snd (subst n (S (ind_npars mdecl + k))) pdecl = pdecl.
Proof.
  intros wfΣ wfn Hd.
  destruct Hd as [[Hmdecl Hidecl] [Hpdecl Hnpar]].
  eapply declared_decl_closed in Hmdecl; auto.
  simpl in Hmdecl.
  pose proof (onNpars _ _ _ _ Hmdecl) as Hnpars.
  apply onInductives in Hmdecl.
  eapply nth_error_alli in Hmdecl; eauto.
  assert (Hp : ind_projs idecl <> []).
  { now apply nth_error_Some_non_nil in Hpdecl. }
  pose proof (onProjections Hmdecl Hp) as onp.
  apply on_projs in onp; eauto.
  eapply nth_error_alli in onp; eauto.
  hnf in onp. simpl in onp.
  rewrite smash_context_length in onp. simpl in onp.
  rewrite Hnpars in onp.
  move: onp => [] _ [] wfty /andb_and[Hb Ht].
  destruct pdecl as [id ty]. unfold on_snd; simpl in *.
  f_equal. eapply subst_closedn; auto. eapply closed_upwards; eauto. lia.
Qed.

Lemma subst_fix_context:
  forall (mfix : list (def term)) n (k : nat),
    fix_context (map (map_def (subst n k) (subst n (#|mfix| + k))) mfix) =
    subst_context n k (fix_context mfix).
Proof.
  intros mfix n k. unfold fix_context.
  rewrite map_vass_map_def rev_mapi.
  fold (fix_context mfix).
  rewrite (subst_context_alt n k (fix_context mfix)).
   now rewrite /subst_decl mapi_length fix_context_length.
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
  induction wf in n, k |- * using term_wf_forall_list_ind; intros ctx; simpl; trivial.

  - specialize (IHwf0 n k (ctx,, vass n0 t)). unfold snoc in IHwf0; rewrite subst_context_snoc in IHwf0.
    simpl in IHwf0. unfold subst_decl, map_decl in IHwf0. unfold vass in *. simpl in IHwf0.
    destruct destArity. destruct p. simpl in *. auto. exact I.
  - specialize (IHwf1 n k (ctx,, vdef n0 t t0)).
    unfold snoc in IHwf1; rewrite subst_context_snoc in IHwf1.
    unfold vdef, subst_decl, map_decl in *. simpl in *.
    destruct destArity as [[args s]|]. apply IHwf1. exact I.
Qed.

Lemma decompose_prod_n_assum0 ctx t : decompose_prod_n_assum ctx 0 t = Some (ctx, t).
Proof. destruct t; simpl; reflexivity. Qed.

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

Lemma strip_outer_cast_subst_instance_constr u t :
  strip_outer_cast (subst_instance_constr u t) =
  subst_instance_constr u (strip_outer_cast t).
Proof. induction t; simpl; auto. Qed.

Lemma strip_outer_cast_tProd_tLetIn_subst_instance_constr u :
  strip_outer_cast_tProd_tLetIn_morph (fun _ => subst_instance_constr u).
Proof.
  red. intros.
  destruct (strip_outer_cast t) eqn:Heq; try auto.
  rewrite strip_outer_cast_subst_instance_constr. now rewrite Heq.
  rewrite strip_outer_cast_subst_instance_constr. now rewrite Heq.
Qed.

Lemma subst_instantiate_params_subst n k params args s t :
  All Ast.wf n -> forall s' t',
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
    destruct a as [na [body|] ty]; simpl; try congruence;
    destruct t; try congruence.
    -- intros Ht'.
       specialize (IHparams _ k _ _ _ Hn _ _ Ht').
       simpl in IHparams.
       replace (#|s| + k + S #|params|) with (S (#|s| + k + #|params|)) by lia.
       rewrite <- IHparams. f_equal.
       now rewrite distr_subst.
    -- intros Ht'. destruct args; try congruence. simpl.
       specialize (IHparams _ k _ _ _ Hn _ _ Ht').
       simpl in IHparams.
       replace (#|s| + k + S #|params|) with (S (#|s| + k + #|params|)) by lia.
       now rewrite <- IHparams.
Qed.

Lemma subst_decl_closed n k d : wf_decl d -> closed_decl k d -> subst_decl n k d = d.
Proof.
  case: d => na [body|] ty; rewrite /closed_decl /subst_decl /map_decl /wf_decl /= => [[wfb wfty]].
  move/andP => [cb cty]. rewrite !subst_closedn //.
  move=> cty; now rewrite !subst_closedn //.
Qed.

Lemma closed_ctx_subst n k ctx : All wf_decl ctx -> closed_ctx ctx = true -> subst_context n k ctx = ctx.
Proof.
  induction ctx in n, k |- *; auto.
  unfold closed_ctx, id. intros wfctx. inv wfctx.
  rewrite mapi_app forallb_app List.rev_length /= Nat.add_0_r.
  move/andb_and => /= [Hctx /andb_and [Ha _]].
  rewrite subst_context_snoc /snoc /= IHctx // subst_decl_closed //.
  now apply: closed_decl_upwards.
Qed.

Lemma closed_tele_subst n k ctx :
  All wf_decl ctx -> closed_ctx ctx ->
  mapi (fun (k' : nat) (decl : context_decl) => subst_decl n (k' + k) decl) (List.rev ctx) = List.rev ctx.
Proof.
  rewrite /closed_ctx /mapi. generalize 0.
  induction ctx using rev_ind; try easy.
  move=> n0 /All_app [wfctx wfx]. inv wfx.
  rewrite /closed_ctx !rev_app_distr /id /=.
  move/andP => [closedx Hctx].
  rewrite subst_decl_closed //. rewrite (closed_decl_upwards n0) //; lia.
  f_equal. now rewrite IHctx.
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

Lemma subst_it_mkProd_or_LetIn n k ctx t :
  subst n k (it_mkProd_or_LetIn ctx t) =
  it_mkProd_or_LetIn (subst_context n k ctx) (subst n (length ctx + k) t).
Proof.
  induction ctx in n, k, t |- *; simpl; try congruence.
  pose (subst_context_snoc n k ctx a). unfold snoc in e. rewrite e. clear e.
  simpl. rewrite -> IHctx.
  pose (subst_context_snoc n k ctx a). simpl. now destruct a as [na [b|] ty].
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
  symmetry. solve_all.
  destruct H as [x' [-> Hx']]. intuition. simpl.
  destruct (leb_spec_Set k x'). lia. reflexivity.
Qed.

Lemma subst_instantiate_params n k params args t ty :
  All wf_decl params -> All Ast.wf n -> All Ast.wf args -> Ast.wf t ->
  closed_ctx params ->
  instantiate_params params args t = Some ty ->
  instantiate_params params (map (subst n k) args) (subst n k t) = Some (subst n k ty).
Proof.
  unfold instantiate_params.
  move=> wfparams wfn wfargs wft.
  move/(closed_tele_subst n k params)=> Heq.
  rewrite -{2}Heq //.
  specialize (subst_instantiate_params_subst n k (List.rev params) args [] t wfn).
  move=> /= Heq'.
  case E: (instantiate_params_subst (List.rev params) args)=> [[l' t']|] /= //.
  specialize (Heq' _ _ E). rewrite Heq'. move=> [= <-]. f_equal.
  rewrite distr_subst //.
  move/instantiate_params_subst_length: E => -> /=. do 2 f_equal. lia.
Qed.
Hint Rewrite subst_instantiate_params : lift.

Lemma wf_arities_context `{checker_flags} Σ mind mdecl : wf Σ ->
  declared_minductive Σ mind mdecl -> wf_local (Σ, ind_universes mdecl) (arities_context mdecl.(ind_bodies)).
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
  apply onArity in X as [s Hs].
  specialize (IHl Hl).
  econstructor; eauto.
  fold (arities_context l) in *.
  unshelve epose proof (weakening (Σ, ind_universes mdecl) [] (arities_context l) _ _ wfΣ _ Hs).
  now rewrite app_context_nil_l.
  simpl in X.
  eapply (env_prop_typing _ typecheck_closed) in Hs; eauto.
  rewrite -> andb_and in Hs. destruct Hs as [Hs Ht].
  simpl in Hs. apply (lift_closed #|arities_context l|) in Hs.
  rewrite -> Hs, app_context_nil_l in X. simpl. exists s.
  apply X.
Qed.

Lemma on_constructor_closed_wf `{checker_flags} {Σ mind mdecl u i idecl cdecl} :
  wf Σ ->
  on_constructor (lift_typing typing) (Σ, ind_universes mdecl) (inductive_mind mind) mdecl (inductive_ind mind) idecl i cdecl ->
  let cty := subst0 (inds (inductive_mind mind) u (ind_bodies mdecl))
                    (subst_instance_constr u (snd (fst cdecl)))
  in closed cty = true /\ Ast.wf cty.
Proof.
  intros wfΣ [[s Hs] Hparams].
  pose proof (typing_wf_local Hs).
  destruct cdecl as [[id cty] car].
  pose proof (typing_wf (Σ, ind_universes mdecl) wfΣ _ _ _ Hs) as [wfty _].
  eapply (env_prop_typing _ typecheck_closed) in Hs; eauto.
  rewrite arities_context_length in Hs.
  rewrite -> andb_and in *. simpl in *.
  destruct Hs as [Hs _]. split; auto.
  eapply (closedn_subst _ 0 0).
  clear. unfold inds. induction #|ind_bodies mdecl|; simpl; try constructor; auto.
  simpl. now rewrite -> inds_length, closedn_subst_instance_constr.
  apply wf_subst; auto with wf.
Qed.

Lemma on_projection_closed_wf `{checker_flags} {Σ mind mdecl u i idecl pdecl} :
  wf Σ -> mdecl.(ind_npars) = context_assumptions mdecl.(ind_params) ->
  on_projection (lift_typing typing) (Σ, ind_universes mdecl) (inductive_mind mind) mdecl (inductive_ind mind) idecl i pdecl ->
  let pty := subst_instance_constr u (snd pdecl) in
  closedn (S (ind_npars mdecl)) pty = true /\ Ast.wf pty.
Proof.
  intros wfΣ Hpar.
  unfold on_projection.
  intros [s Hs].
  pose proof (typing_wf_local Hs).
  destruct pdecl as [id cty].
  eapply (env_prop_typing _ typing_wf_gen) in Hs as Hs'; eauto.
  eapply (env_prop_typing _ typecheck_closed) in Hs; eauto.
  rewrite -> andb_and in *. simpl in *.
  destruct Hs as [Hs _].
  rewrite smash_context_length in Hs. simpl in *.
  rewrite - Hpar in Hs. rewrite -> closedn_subst_instance_constr.
  split; auto with wf. now apply wf_subst_instance_constr.
Qed.

Lemma context_subst_length Γ a s : context_subst Γ a s -> #|Γ| = #|s|.
Proof. induction 1; simpl; congruence. Qed.

Lemma context_subst_assumptions_length Γ a s : context_subst Γ a s -> context_assumptions Γ = #|a|.
Proof. induction 1; simpl; try congruence. rewrite app_length /=. lia. Qed.

(* Lemma context_subst_app `{cf:checker_flags} Σ Γ Γ' a s : *)
(*   All_local_env (fun _ _ t T => Ast.wf t /\ Ast.wf T) Σ Γ' -> *)
(*   All Ast.wf a -> All Ast.wf s -> *)
(*   context_subst (Γ' ++ Γ) a s -> *)
(*   { a0 & { a1 & { s0 & { s1 & (context_subst Γ a0 s0 * context_subst (subst_context s0 0 Γ') a1 s1 *)
(*                                * (a = a0 ++ a1) * (s = s1 ++ s0))%type } } } }. *)
(* Proof. *)
(*   induction Γ' in Γ, a, s |- *. simpl. *)
(*   exists a, [], s, []. rewrite app_nil_r; intuition. *)

(*   simpl. intros wfΓ wfa wfs Hs. *)
(*   revert wfΓ wfa wfs. inv Hs; intros wfΓ wfa wfs; inv wfΓ. *)
(*   - eapply All_app in wfa as [Hargs Ha1]; *)
(*     eapply (All_app (l:=[a1])) in wfs as [Ha'' Hs0]. *)
(*     specialize (IHΓ' _ _ _ H0 Hargs Hs0 H). *)
(*     destruct IHΓ' as (a0' & a1' & s1 & s2 & ((sa0 & sa1) & eqargs) & eqs0). *)
(*     subst. exists a0', (a1' ++ [a1]), s1, (a1 :: s2). intuition eauto. *)
(*     rewrite subst_context_snoc. constructor. auto. now rewrite app_assoc. *)
(*   - eapply (All_app (l:=[subst0 s0 b])) in wfs as [Ha'' Hs0]. *)
(*     specialize (IHΓ' _ _ _ H0 wfa Hs0 H). *)
(*     destruct IHΓ' as (a0' & a1' & s1 & s2 & ((sa0 & sa1) & eqargs) & eqs0). *)
(*     subst. exists a0', a1', s1, (subst s2 0 (subst s1 #|Γ'| b) :: s2). intuition eauto. *)
(*     rewrite -> subst_context_snoc, Nat.add_0_r. *)
(*     unfold subst_decl; simpl. unfold map_decl. simpl. *)
(*     econstructor. auto. simpl. f_equal. *)
(*     rewrite -> subst_app_simpl; auto. simpl. *)
(*     pose proof(context_subst_length _ _ _ sa1) as Hs1. *)
(*     rewrite subst_context_length in Hs1. rewrite -> Hs1. auto. auto. *)
(*     apply All_app in Hs0. solve_all. *)
(*     apply All_app in Hs0. solve_all. *)
(* Qed. *)

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
  - destruct ty; try congruence.
    intros. move: (IHctx _ _ _ _ H) => [ctx'' [Hmake Hdecomp]].
    eapply (decompose_prod_n_assum_extend_ctx [vdef na0 ty1 ty2]) in Hdecomp.
    unfold snoc. eexists; intuition eauto.
  - destruct ty; try congruence.
    case: args => [|a args']; try congruence.
    move=> H. move: (IHctx _ _ _ _ H) => [ctx'' [Hmake Hdecomp]].
    eapply (decompose_prod_n_assum_extend_ctx [vass na0 ty1]) in Hdecomp.
    unfold snoc. eexists; intuition eauto.
Qed.

Lemma instantiate_params_make_context_subst ctx args ty ty' :
  instantiate_params ctx args ty = Some ty' ->
  exists ctx' ty'' s',
    decompose_prod_n_assum [] (length ctx) ty = Some (ctx', ty'') /\
    make_context_subst (List.rev ctx) args [] = Some s' /\ ty' = subst0 s' ty''.
Proof.
  unfold instantiate_params.
  case E: instantiate_params_subst => // [[s ty'']].
  move=> [= <-].
  eapply instantiate_params_subst_make_context_subst in E.
  destruct E as [ctx'' [Hs Hty'']].
  exists ctx'', ty'', s. split; auto.
  now rewrite -> List.rev_length in Hty''.
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
    subst s. rewrite inds_spec rev_mapi nth_error_mapi /=.
    elim nth_error_spec. intros. simpl.
    f_equal. destruct ind; simpl. f_equal. f_equal. simpl in H. lia.
    rewrite List.rev_length. lia.
  - rewrite !map_app. f_equal.
    -- rewrite map_subst_instance_constr_to_extended_list_k.
       erewrite to_extended_list_k_map_subst at 2.
       now rewrite Nat.add_comm. lia.
Qed.

Lemma subst_to_extended_list_k s k args ctx :
  All Ast.wf s ->
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
    solve_all. destruct H3 as [n [-> Hn]].
    rewrite /compose /lift (subst_app_decomp [a] s k); auto with wf.
    rewrite subst_rel_gt. simpl; lia.
    repeat (f_equal; simpl; try lia).
    now rewrite /map (subst_rel_eq _ _ 0 a).
  - inv wfs.
    rewrite -IHcontext_subst // to_extended_list_k_cons /=.
    rewrite (lift_to_extended_list_k _ _ 1) map_map_compose.
    pose proof (to_extended_list_k_spec Γ k).
    solve_all. destruct H3 as [n [-> Hn]].
    rewrite /compose /lift (subst_app_decomp [subst0 s b] s k); auto with wf.
    rewrite subst_rel_gt. simpl; lia.
    repeat (f_equal; simpl; try lia).
Qed.

Lemma wf_context_subst ctx args s :
  All wf_decl ctx -> All Ast.wf args ->
  context_subst ctx args s -> All Ast.wf s.
Proof.
  move=> wfctx wfargs.
  induction 1. constructor.
  eapply All_app in wfargs as [wfargs wfa]. inv wfa. inv wfctx.
  constructor; intuition auto.
  inv wfctx. red in H0. constructor; solve_all. apply wf_subst. solve_all. intuition auto with wf.
Qed.

Lemma wf_make_context_subst ctx args s' :
  All wf_decl ctx -> All Ast.wf args ->
  make_context_subst (List.rev ctx) args [] = Some s' -> All Ast.wf s'.
Proof.
  move=> wfctx wfargs.
  move/make_context_subst_spec. rewrite rev_involutive.
  eauto using wf_context_subst.
Qed.

Hint Resolve All_Forall : wf.

Lemma subst_types_of_case `{CF:checker_flags} Σ ind mdecl idecl args u p pty indctx pctx ps btys n k :
  let f (ctx : context) := subst n (#|ctx| + k) in
  let f_ctx := subst_context n k in
  wf Σ ->
  All Ast.wf n -> All Ast.wf args ->
  Ast.wf pty -> Ast.wf (ind_type idecl) ->
  declared_inductive Σ mdecl ind idecl ->
  types_of_case ind mdecl idecl args u p pty = Some (indctx, pctx, ps, btys) ->
  types_of_case ind mdecl idecl (map (f []) args) u (f [] p) (f [] pty) =
  Some (f_ctx indctx, f_ctx pctx, ps, map (on_snd (f [])) btys).
Proof.
  simpl. intros wfΣ wfn wfargs wfpty wfdecl wfidecl. simpl.
  pose proof (on_declared_inductive wfΣ wfidecl) as [onmind onind].
  apply onParams in onmind as Hparams.
  assert (wfparams : Forall wf_decl (ind_params mdecl)).
  { eapply typing_all_wf_decl ; eauto; tas. }
  assert(closedparams : closed_ctx (ind_params mdecl)).
  { eapply closed_wf_local; eauto. simpl. auto. }
  epose proof (subst_declared_inductive _ ind mdecl idecl n k wfΣ).
  forward H ; auto. rewrite <- H at 2.
  unfold types_of_case.
  pose proof (subst_instantiate_params n k (ind_params mdecl) args (ind_type idecl)) as hs.
  rewrite -> ind_type_map. simpl.
  case_eq (instantiate_params (ind_params mdecl) args (ind_type idecl)) ; try discriminate.
  intros ity eq. rewrite eq in hs. erewrite hs ; trivial.
  clear hs.
  pose proof (subst_destArity [] ity n k) ; trivial. simpl in H0.
  forward H0. eapply wf_instantiate_params. 4:eauto. all:eauto. solve_all.
  unfold subst_context, fold_context in H0. simpl in H0.
  destruct (destArity [] ity) as [[ctx'' s''] | ] ; try congruence.
  rewrite H0. clear H0.
  pose proof (subst_destArity [] pty n k); trivial. simpl in H0.
  unfold subst_context, fold_context in H0. simpl in H0. forward H0 by auto.
  destruct (destArity [] pty) as [[ctx' s'] | ]; try congruence. auto.
  rewrite H0. clear H0.
  destruct map_option_out eqn:Hbrs; try congruence.
  intros [= -> -> -> ->].
  assert(forall brs,
         map_option_out (build_branches_type ind mdecl idecl args u p) = Some brs ->
         map_option_out (build_branches_type ind mdecl
         (map_one_inductive_body (context_assumptions (ind_params mdecl))
            (length (arities_context (ind_bodies mdecl))) (fun k' => subst n (k' + k))
            (inductive_ind ind) idecl) (map (subst n k) args) u (subst n k p)) =
         Some (map (on_snd (subst n k)) brs)).
  { intros brs.
    unfold build_branches_type.
    rewrite ind_ctors_map.
    intros Heq. apply (f_equal (option_map (map (on_snd (subst n k))))) in Heq.
    simpl in Heq.
    rewrite <- map_option_out_map_option_map in Heq.
    rewrite map_mapi in Heq. rewrite mapi_map.
    apply onConstructors in onind.
    red in onind.
    eapply Alli_map_option_out_mapi_Some_spec in onind. eauto. 2:eauto.
    clear Heq onind.
    intros i [[id t] arity] [ar t']. simpl.
    rewrite <- subst_subst_instance_constr.
    rewrite -> subst0_inds_subst.
    intros Honc.
    destruct (on_constructor_closed_wf wfΣ (u:=u) Honc) as [clt wft].
    simpl in *.
    eapply (closed_upwards k) in clt; try lia.
    rewrite (subst_closedn (map (subst_instance_constr u) n) k _ wft clt).
    rewrite <- (subst_closedn n k _ wft clt) at 2.
    case Heq : instantiate_params => [ty|] /=; try congruence.
    remember (subst0 (inds (inductive_mind ind) u (ind_bodies mdecl)) (subst_instance_constr u t)) as
        ty'.
    eapply subst_instantiate_params in Heq as Heq'. rewrite -> Heq'. all:auto with wf.
    eapply instantiate_params_make_context_subst in Heq.
    destruct Heq as [ctx' [ty'' [s' [Hty [Hsubst Ht0]]]]].
    subst ty. simpl.
    rewrite Heqty' in Hty.
    destruct Honc as [o [c _]]. destruct c.
    simpl in *. rewrite cshape_eq in Hty.
    rewrite -> !subst_instance_constr_it_mkProd_or_LetIn in Hty.
    rewrite !subst_it_mkProd_or_LetIn in Hty.
    assert(#|subst_context (inds (inductive_mind ind) u (ind_bodies mdecl)) 0
             (subst_instance_context u (ind_params mdecl))| = #|ind_params mdecl|).
    now rewrite subst_context_length subst_instance_context_length.
    rewrite <- H0 in Hty.
    rewrite decompose_prod_n_assum_it_mkProd in Hty.
    injection Hty. clear Hty.
    intros Heqty'' <-. revert Heqty''.
    rewrite !subst_instance_context_length Nat.add_0_r.

    rewrite (subst_cstr_concl_head ind u mdecl cshape_args cshape_indices).
    destruct wfidecl as [Hmdecl Hnth].
    now apply nth_error_Some_length in Hnth.
    intros <-. rewrite !subst_it_mkProd_or_LetIn !subst_mkApps /=.
    rewrite !decompose_prod_assum_it_mkProd /=; try by rewrite is_ind_app_head_mkApps.
    rewrite !decompose_app_mkApps; try by reflexivity.
    simpl. rewrite !map_app !subst_context_length !subst_instance_context_length Nat.add_0_r.
    rewrite !(subst_to_extended_list_k _ _ args) //.
    eapply wf_make_context_subst in Hsubst; eauto. solve_all.

    pose proof Hsubst as Hsubst'.
    apply make_context_subst_spec in Hsubst'.
    rewrite rev_involutive in Hsubst'.
    pose proof (context_subst_assumptions_length _ _ _ Hsubst').

    case E: chop => [l l'].
    have chopm := (chop_map _ _ _ _ _ E).
    move: E chopm.
    rewrite chop_n_app ?map_length.
    rewrite <- H1. apply onNpars in onmind. lia.
    move=> [= <- <-] chopm.
    move: {chopm}(chopm _ (subst n (#|cshape_args| + k))).
    rewrite map_app.
    move=> chopm; rewrite {}chopm /=.
    move=> <-. f_equal.
    rewrite !app_nil_r /on_snd /=.
    rewrite subst_it_mkProd_or_LetIn !subst_context_length !subst_mkApps
            !subst_instance_context_length !map_app.
    f_equal. f_equal. f_equal.
    -- rewrite -> commut_lift_subst_rec. arith_congr. lia.
    -- f_equal. simpl. f_equal.
       rewrite !subst_mkApps /= !map_app. f_equal.
       f_equal.
       rewrite /to_extended_list -to_extended_list_k_map_subst.
       rewrite !subst_context_length subst_instance_context_length. lia.
       now rewrite to_extended_list_k_subst.
    -- solve_all.
    -- apply All_map. solve_all. now apply wf_subst_instance_constr. }
  specialize (H0 _ Hbrs). now rewrite H0.
  solve_all.
Qed.

Hint Unfold subst1 : subst.
Hint Rewrite subst_mkApps distr_subst: subst.

Lemma subs_nth_error `{checker_flags} Σ Γ s Δ decl n t :
  subs Σ Γ s Δ ->
  nth_error Δ n = Some decl ->
  nth_error s n = Some t ->
  match decl_body decl return Type with
  | Some t' => False
  | None =>
    let ty := subst0 (skipn (S n) s) (decl_type decl) in
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

Lemma red1_tApp_mkApp Σ Γ M1 N1 M2 :
  red1 Σ Γ M1 N1 -> red1 Σ Γ (tApp M1 [M2]) (mkApp N1 M2).
Proof.
  intros.
  change (mkApp N1 M2) with (mkApps N1 [M2]).
  apply app_red_l. auto.
Qed.

Lemma red1_mkApp Σ Γ M1 N1 M2 :
  Ast.wf M1 ->
  red1 Σ Γ M1 N1 -> red1 Σ Γ (mkApp M1 M2) (mkApp N1 M2).
Proof.
  intros wfM1 H.
  destruct (isApp M1) eqn:Heq.
  destruct M1; try discriminate. simpl.
  revert wfM1. inv H. simpl. intros.
  rewrite mkApp_mkApps. constructor.

  intros.
  econstructor; eauto.
  inv wfM1. simpl.
  clear -H1.
  unfold is_constructor in *.
  destruct (nth_error args narg) eqn:Heq.
  eapply nth_error_app_left in Heq. now rewrite -> Heq. discriminate.

  intros. rewrite mkApp_mkApps. now constructor.

  intros. simpl.
  constructor. clear -X. induction X; constructor; auto.

  rewrite mkApp_tApp; auto.
  now apply red1_tApp_mkApp.
Qed.

Lemma red1_mkApps_l Σ Γ M1 N1 M2 :
  Ast.wf M1 -> All Ast.wf M2 ->
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
  Ast.wf M1 -> All Ast.wf M2 ->
  OnOne2 (red1 Σ Γ) M2 N2 -> red1 Σ Γ (mkApps M1 M2) (mkApps M1 N2).
Proof.
  intros. induction X in M1, H, H0 |- *.
  inv H0.
  destruct (isApp M1) eqn:Heq. destruct M1; try discriminate.
  simpl. constructor. apply OnOne2_app. constructor. auto.
  rewrite mkApps_tApp; try congruence.
  rewrite mkApps_tApp; try congruence.
  constructor. constructor. auto.
  inv H0.
  specialize (IHX (mkApp M1 hd)). forward IHX.
  apply wf_mkApp; auto. forward IHX; auto.
  now rewrite !mkApps_mkApp in IHX.
Qed.

Lemma wf_fix :
  forall (mfix : list (def term)) (k : nat), Ast.wf (tFix mfix k) ->
    Forall
      (fun def : def term => Ast.wf (dtype def) /\ Ast.wf (dbody def) /\ isLambda (dbody def) = true)
      mfix.
Proof.
  intros. inv H. auto.
Defined.

Lemma wf_cofix :
  forall (mfix : list (def term)) (k : nat), Ast.wf (tCoFix mfix k) ->
    Forall
      (fun def : def term => Ast.wf (dtype def) /\ Ast.wf (dbody def))
      mfix.
Proof.
  intros. inv H. auto.
Defined.

Lemma substitution_red1 `{CF:checker_flags} Σ Γ Γ' Γ'' s M N :
  wf Σ.1 -> All Ast.wf s -> subs Σ Γ s Γ' -> wf_local Σ Γ -> Ast.wf M ->
  red1 (fst Σ) (Γ ,,, Γ' ,,, Γ'') M N ->
  red1 (fst Σ) (Γ ,,, subst_context s 0 Γ'') (subst s #|Γ''| M) (subst s #|Γ''| N).
Proof.
  intros wfΣ wfs Hs wfΓ wfM H.
  remember (Γ ,,, Γ' ,,, Γ'') as Γ0. revert Γ Γ' Γ'' HeqΓ0 wfΓ Hs.
  induction H using red1_ind_all in |- *; intros Γ0 Γ' Γ'' HeqΓ0 wfΓ Hs; try subst Γ; cbn -[iota_red];
  match goal with
    |- context [iota_red _ _ _ _] => idtac
  | |- _ => autorewrite with subst
  end; auto;
    try solve [  econstructor; ((forward IHred1; try inv wfM; eauto) || eauto) ].

  (* remember (Γ ,,, Γ' ,,, Γ'') as Γ0. revert Γ Γ' Γ'' HeqΓ0 wfΓ Hs. *)
  (* induction H using red1_ind_all in |- *; intros Γ0 Γ' Γ'' HeqΓ0 wfΓ Hs; try subst Γ; simpl; *)
  (*   autorewrite with subst; auto; *)
  (*   try solve [  econstructor; try eapply IHred1; try inv wfM; eauto; eauto ]. *)
  - autorewrite with subst. rewrite distr_subst; auto.
    eapply red_beta.

  - autorewrite with subst. rewrite distr_subst; auto.
    eapply red_zeta.

  - pose proof (subst_length _ _ _ _ Hs).
    elim (leb_spec_Set); intros Hn.
    + destruct (nth_error s) eqn:Heq.
      ++ pose proof (nth_error_Some_length Heq).
         rewrite -> nth_error_app_context_ge in H by lia.
         rewrite -> nth_error_app_context_lt in H by lia.
         destruct nth_error eqn:HΓ'.
         eapply subs_nth_error in Heq; eauto.
         simpl in H. destruct decl_body; try contradiction.
         discriminate. discriminate.
      ++ apply nth_error_None in Heq.
         assert(S i = #|s| + (S (i - #|s|))) by lia.
         rewrite H1. rewrite -> simpl_subst; try lia.
         econstructor.
         rewrite nth_error_app_context_ge // in H.
         rewrite nth_error_app_context_ge // in H. lia.
         rewrite -> nth_error_app_context_ge. 2:(autorewrite with wf; lia).
         rewrite <- H. f_equal. f_equal. autorewrite with wf. lia.
         rewrite -> !nth_error_app_context_ge in H by lia.
         destruct nth_error eqn:Hi.
         eapply nth_error_All_local_env in wfΓ. red in wfΓ.
         rewrite -> Hi in wfΓ. simpl in H.
         destruct c; simpl in H; try discriminate.
         injection H. intros ->. red in wfΓ. cbn in *. apply typing_wf in wfΓ. intuition eauto. eauto.
         apply nth_error_Some_length in Hi. lia. discriminate.
    + rewrite -> nth_error_app_context_lt in H by lia.
      pose (commut_lift_subst_rec body s (S i) (#|Γ''| - S i) 0).
      assert(eq:#|Γ''| - S i + S i = #|Γ''|) by lia.
      rewrite -> eq in e. rewrite <- e by lia.
      constructor.
      rewrite -> nth_error_app_context_lt by (autorewrite with wf; lia).
      rewrite -> nth_error_subst_context.
      unfold subst_decl; now rewrite -> option_map_decl_body_map_decl, H, Nat.add_0_r.

  - rewrite subst_iota_red.
    autorewrite with subst.
    constructor.

  - rewrite mkApps_tApp; simpl; auto with wf.
    inv wfM. auto with wf. rewrite -> mkApps_tApp; simpl.
    + eapply red_fix. erewrite subst_unfold_fix; eauto.
      now apply subst_is_constructor.
    + inv wfM. inv H3.
    unfold unfold_fix in H.
    destruct nth_error eqn:Heq.
    injection H. intros <- <-.
    eapply nth_error_forall in H5; eauto.
    destruct d as [na b ty]; simpl in *.
    destruct H5 as [_ [_ Hty]].
    destruct ty; try discriminate. reflexivity.
    discriminate.
    + apply not_empty_map. now inv wfM.

  - pose proof (subst_declared_constant _ _ _ s #|Γ''| u wfΣ H).
    apply (f_equal cst_body) in H1.
    rewrite <- !map_cst_body in H1. rewrite H0 in H1. simpl in H1.
    injection H1. intros ->.
    econstructor. eauto. eauto.

  - simpl. constructor.
    inv wfM.
    now rewrite nth_error_map H.

  - constructor.
    forward IHred1; try now inv wfM.
    specialize (IHred1 Γ0 Γ' (Γ'' ,, _) eq_refl).
    now rewrite subst_context_snoc0 in IHred1.

  - constructor.
    forward IHred1; try now inv wfM.
    specialize (IHred1 Γ0 Γ' (Γ'' ,, _) eq_refl).
    now rewrite subst_context_snoc0 in IHred1.

  - constructor.
    induction X; constructor; auto.
    intuition auto; eauto.
    forward b. inv wfM. now inv H1.
    specialize (b _ _ _ eq_refl).
    destruct hd, hd'; simpl in *. now eapply b.
    eapply IHX. inv wfM; eauto. inv H1; eauto with wf.

  - forward IHred1; try now inv wfM.
    assert(All (Ast.wf ∘ subst s #|Γ''|) M2).
    eapply (Forall_All (fun x => Ast.wf (subst s #|Γ''| x))). inv wfM; solve_all.
    apply wf_subst; auto. solve_all.
    specialize (IHred1 _ _ _ eq_refl).
    specialize (IHred1 wfΓ Hs).
    apply red1_mkApps_l; auto. inv wfM. apply wf_subst; auto. solve_all.
    solve_all.

  - assert(Ast.wf (subst s #|Γ''| M1)). inv wfM. apply wf_subst; auto with wf.
    assert(All (Ast.wf ∘ subst s #|Γ''|) M2).
    { apply (Forall_All (fun x => Ast.wf (subst s #|Γ''| x))).
      inv wfM.
      eapply Forall_impl; eauto. simpl; eauto with wf. }
    apply red1_mkApps_r; auto with wf.
    now apply All_map.
    assert(Ast.wf M1). now inv wfM.
    assert(All Ast.wf M2). eapply Forall_All. now inv wfM.
    clear -X H1 H2 wfΓ Hs.
    induction X; constructor; auto.
    intuition.
    eapply b; eauto. now inv H2.
    apply IHX. now inv H2.

  - forward IHred1. now inv wfM.
    constructor. specialize (IHred1 _ _ (Γ'' ,, vass na M1) eq_refl).
    now rewrite subst_context_snoc0 in IHred1.

  - constructor.
    induction X; constructor; auto.
    intuition. eapply b; eauto.
    inv wfM. now inv H.
    apply IHX. inv wfM. inv H; now constructor.

  - constructor.
    rewrite -> (OnOne2_length X). generalize (#|mfix1|).
    induction X; simpl; constructor; auto.
    intuition. eapply b; eauto.
    inv wfM. inv H. intuition; auto.
    apply IHX. inv wfM. inv H. intuition.

  - apply wf_fix in wfM.
    apply fix_red_body. rewrite !subst_fix_context.
    solve_all. apply (OnOne2_All_mix_left wfM) in X. clear wfM.
    rewrite <- (OnOne2_length X).
    eapply OnOne2_map. unfold on_Trel; solve_all.
    specialize (X Γ0 Γ' (Γ'' ,,, fix_context mfix0)).
    rewrite app_context_assoc in X. specialize (X eq_refl).
    rewrite -> app_context_length, fix_context_length in *.
    rewrite -> subst_context_app in *.
    rewrite -> app_context_assoc, Nat.add_0_r in *.
    auto.

  - apply wf_cofix in wfM. constructor.
    rewrite -> (OnOne2_length X). generalize (#|mfix1|).
    induction X; simpl; constructor; auto.
    intuition. eapply b; eauto. now inv wfM.
    apply IHX. now inv wfM; inv H0.

  - apply wf_cofix in wfM.
    apply cofix_red_body. rewrite !subst_fix_context.
    solve_all. apply (OnOne2_All_mix_left wfM) in X. clear wfM.
    rewrite <- (OnOne2_length X).
    eapply OnOne2_map. unfold on_Trel; solve_all.
    specialize (X Γ0 Γ' (Γ'' ,,, fix_context mfix0)).
    rewrite app_context_assoc in X. specialize (X eq_refl).
    rewrite -> app_context_length, fix_context_length in *.
    rewrite -> subst_context_app in *.
    rewrite -> app_context_assoc, Nat.add_0_r in *.
    auto.
Qed.

Lemma eq_term_upto_univ_refl Re Rle :
  RelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Rle ->
  forall t, eq_term_upto_univ Re Rle t t.
Proof.
  intros hRe hRle.
  induction t in Rle, hRle |- * using term_forall_list_ind; simpl;
    try constructor; try apply Forall_Forall2; try easy;
      try now apply Forall_True.
  - eapply Forall_impl ; try eassumption.
    intros. easy.
  - eapply Forall_impl ; try eassumption.
    intros. easy.
  - destruct p. constructor; try easy.
    apply Forall_Forall2. eapply Forall_impl ; try eassumption.
    intros. split ; auto.
  - eapply Forall_impl ; try eassumption.
    intros x [? ?]. repeat split ; auto.
  - eapply Forall_impl ; try eassumption.
    intros x [? ?]. repeat split ; auto.
Qed.

Lemma eq_term_refl `{checker_flags} φ t : eq_term φ t t.
Proof.
  apply eq_term_upto_univ_refl.
  - intro; apply eq_universe_refl.
  - intro; apply eq_universe_refl.
Qed.


Lemma leq_term_refl `{checker_flags} φ t : leq_term φ t t.
Proof.
  apply eq_term_upto_univ_refl.
  - intro; apply eq_universe_refl.
  - intro; apply leq_universe_refl.
Qed.


Lemma eq_term_leq_term `{checker_flags} φ t u : eq_term φ t u -> leq_term φ t u.
Proof.
  induction t in u |- * using term_forall_list_ind; simpl; inversion 1;
    subst; constructor; try (now unfold eq_term, leq_term in * );
  try eapply Forall2_impl'; try easy.
  now apply eq_universe_leq_universe.
  all: try (apply Forall_True, eq_universe_leq_universe).
Qed.

Lemma eq_term_upto_univ_App `{checker_flags} Re Rle f f' :
  eq_term_upto_univ Re Rle f f' ->
  isApp f = isApp f'.
Proof.
  inversion 1; reflexivity.
Qed.

Lemma eq_term_App `{checker_flags} φ f f' :
  eq_term φ f f' ->
  isApp f = isApp f'.
Proof.
  inversion 1; reflexivity.
Qed.

Lemma eq_term_upto_univ_mkApps `{checker_flags} Re Rle f l f' l' :
  eq_term_upto_univ Re Rle f f' ->
  Forall2 (eq_term_upto_univ Re Re) l l' ->
  eq_term_upto_univ Re Rle (mkApps f l) (mkApps f' l').
Proof.
  induction l in f, f' |- *; intro e; inversion_clear 1.
  - assumption.
  - pose proof (eq_term_upto_univ_App _ _ _ _ e).
    case_eq (isApp f).
    + intro X; rewrite X in H0.
      destruct f; try discriminate.
      destruct f'; try discriminate.
      cbn. inversion_clear e. constructor. assumption.
      apply Forall2_app. assumption.
      now constructor.
    + intro X; rewrite X in H0.
      rewrite !mkApps_tApp; eauto.
      intro; discriminate.
      intro; discriminate.
      constructor. assumption.
      now constructor.
Qed.

Lemma leq_term_mkApps `{checker_flags} φ f l f' l' :
  leq_term φ f f' ->
  Forall2 (eq_term φ) l l' ->
  leq_term φ (mkApps f l) (mkApps f' l').
Proof.
  eapply eq_term_upto_univ_mkApps.
Qed.

Lemma leq_term_App `{checker_flags} φ f f' :
  leq_term φ f f' ->
  isApp f = isApp f'.
Proof.
  inversion 1; reflexivity.
Qed.

Lemma subst_eq_term_upto_univ `{checker_flags} Re Rle n k T U :
  RelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Rle ->
  eq_term_upto_univ Re Rle T U ->
  eq_term_upto_univ Re Rle (subst n k T) (subst n k U).
Proof.
  intros hRe hRle h.
  induction T in n, k, U, h, Rle, hRle |- * using term_forall_list_ind.
  all: simpl ; inversion h ; simpl.
  all: try (eapply eq_term_upto_univ_refl ; easy).
  all: try (constructor ; easy).
  - constructor.
    eapply Forall2_map. eapply Forall2_impl' ; try eassumption.
    eapply Forall_impl ; try eassumption.
    cbn. intros x HH y HH'. now eapply HH.
  - subst. eapply eq_term_upto_univ_mkApps. all: try easy.
    eapply Forall2_map. eapply Forall2_impl' ; try eassumption.
    eapply Forall_impl ; try eassumption.
    cbn. intros x HH y HH'. now eapply HH.
  - constructor ; try easy.
    eapply Forall2_map.
    eapply Forall2_impl'. eassumption.
    eapply Forall_impl. easy.
    cbn. intros x HH y [? HH']. split ; [assumption | now apply HH].
  - constructor.
    eapply Forall2_map.
    eapply Forall2_impl'. eassumption.
    eapply Forall_impl. eassumption.
    cbn. rewrite (Forall2_length H4).
    intros x [] y []; now split.
  - constructor.
    eapply Forall2_map.
    eapply Forall2_impl'. eassumption.
    eapply Forall_impl. eassumption.
    cbn. rewrite (Forall2_length H4).
    intros x [] y []; now split.
Qed.

Lemma subst_eq_term `{checker_flags} ϕ n k T U :
  eq_term ϕ T U ->
  eq_term ϕ (subst n k T) (subst n k U).
Proof.
  intros Hleq.
  eapply subst_eq_term_upto_univ.
  - intro. eapply eq_universe_refl.
  - intro. eapply eq_universe_refl.
  - assumption.
Qed.

Lemma subst_leq_term `{checker_flags} ϕ n k T U :
  leq_term ϕ T U ->
  leq_term ϕ (subst n k T) (subst n k U).
Proof.
  intros Hleq.
  eapply subst_eq_term_upto_univ.
  - intro. eapply eq_universe_refl.
  - intro. eapply leq_universe_refl.
  - assumption.
Qed.


Lemma subst_eq_decl `{checker_flags} ϕ l k d d' :
  eq_decl ϕ d d' -> eq_decl ϕ (subst_decl l k d) (subst_decl l k d').
Proof.
  destruct d, d', decl_body, decl_body0;
    unfold eq_decl, map_decl; cbn; intuition auto using subst_eq_term.
Qed.

Lemma subst_eq_context `{checker_flags} φ l l' n k :
  eq_context φ l l' ->
  eq_context φ (subst_context n k l) (subst_context n k l').
Proof.
  induction l in l', n, k |- *; inversion 1. constructor.
  rewrite !subst_context_snoc. constructor.
  rewrite (Forall2_length (All2_Forall2 H5)).
  now apply subst_eq_decl.
  now apply IHl.
Qed.

Lemma subst_check_correct_arity:
  forall (cf : checker_flags) φ (ind : inductive) (u : universe_instance)
         (npar : nat) (args : list term) (idecl : one_inductive_body)
         (indctx pctx : list context_decl) s k,
    check_correct_arity φ idecl ind u indctx (firstn npar args) pctx ->
    check_correct_arity
      φ idecl ind u (subst_context s k indctx) (firstn npar (map (subst s k) args))
      (subst_context s k pctx).
Proof.
  intros cf φ ind u npar args idecl indctx pctx s k.
  unfold check_correct_arity.
  inversion_clear 1.
  rewrite subst_context_snoc. constructor.
  - apply All2_Forall2, Forall2_length in H1. destruct H1.
    apply (subst_eq_decl _ s (#|indctx| + k)) in H0.
    unfold subst_decl, map_decl in H0; cbn in H0.
    assert (XX : subst s (#|indctx| + k) (mkApps (tInd ind u) (map (lift0 #|indctx|) (firstn npar args) ++ to_extended_list indctx)) = mkApps (tInd ind u) (map (lift0 #|subst_context s k indctx|) (firstn npar (map (subst s k) args)) ++ to_extended_list (subst_context s k indctx)) );
      [|now rewrite XX in H0].
    clear H0.
    rewrite -> subst_mkApps; simpl. f_equal. rewrite map_app.
    rewrite -> firstn_map.
    rewrite !map_map_compose. cbn. f_equal.
    + eapply map_ext.
      intros. unfold compose. rewrite commut_lift_subst_rec. lia.
      rewrite subst_context_length. f_equal. lia.
    + rewrite /to_extended_list to_extended_list_k_subst.
      rewrite <- (to_extended_list_k_map_subst s). reflexivity. lia.
  - now apply subst_eq_context.
Qed.

Lemma subs_wf `{checker_flags} Σ Γ s Δ : wf Σ.1 -> subs Σ Γ s Δ -> All Ast.wf s.
Proof.
  induction 2; constructor.
  apply typing_wf in t0; intuition auto with wf.
  eapply typing_wf_local in t0; eauto.
Qed.

Lemma wf_red1_wf `{checker_flags} Σ Γ M N : wf Σ.1 -> wf_local Σ Γ -> Ast.wf M -> red1 (fst Σ) Γ M N -> Ast.wf N.
Proof.
  intros wfΣ wfΓ wfM Hr.
  apply wf_red1 in Hr; eauto.
  apply typing_wf_sigma; auto.
  apply typing_all_wf_decl in wfΓ; eauto.
Qed.

(** The cumulativity relation is substitutive, yay! *)

Lemma substitution_cumul `{CF:checker_flags} Σ Γ Γ' Γ'' s M N :
  wf Σ.1 -> wf_local Σ (Γ ,,, Γ' ,,, Γ'') -> subs Σ Γ s Γ' -> Ast.wf M -> Ast.wf N ->
  Σ ;;; Γ ,,, Γ' ,,, Γ'' |- M <= N ->
  Σ ;;; Γ ,,, subst_context s 0 Γ'' |- subst s #|Γ''| M <= subst s #|Γ''| N.
Proof.
  intros wfΣ wfΓ Hs wfM wfN. induction 1.
  constructor.
  - now apply subst_leq_term.
  - pose proof r.
    apply wf_red1_wf in X0; eauto.
    eapply substitution_red1 in r. 4:eauto. all:auto.
    econstructor 2; eauto.
    eauto using subs_wf.
    eauto with wf.
  - pose proof r.
    apply wf_red1_wf in X0; eauto.
    eapply substitution_red1 in r. 4:eauto.
    all:eauto using subs_wf with wf.
    now econstructor 3.
Qed.

Theorem substitution `{checker_flags} Σ Γ Γ' s Δ (t : term) T :
  wf Σ.1 -> subs Σ Γ s Γ' ->
  Σ ;;; Γ ,,, Γ' ,,, Δ |- t : T ->
  wf_local Σ (Γ ,,, subst_context s 0 Δ) ->
  Σ ;;; Γ ,,, subst_context s 0 Δ |- subst s #|Δ| t : subst s #|Δ| T.
Proof.
  intros HΣ Hs Ht.
  pose proof (typing_wf_local Ht).
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
    { clear X. apply typing_all_wf_decl in wfΓ0; eauto.
      eapply (nth_error_forall) in wfΓ0; eauto. red in wfΓ0. intuition. }
    elim (leb_spec_Set); intros Hn.
    elim nth_error_spec.
    + intros x Heq Hlt.
      pose proof (subst_length _ _ _ _ sub).
      rewrite -> nth_error_app_context_ge in H0 by lia.
      rewrite -> nth_error_app_context_lt in H0 by lia.
      eapply subs_nth_error in Heq; eauto.
      destruct decl_body; try contradiction.
      cbn -[skipn] in Heq.
      eapply refine_type.
      eapply (weakening _ _ (subst_context s 0 Δ)) in Heq; eauto with wf.
      rewrite subst_context_length in Heq. eapply Heq.
      rewrite -> commut_lift_subst_rec by lia.
      rewrite <- (firstn_skipn (S (n - #|Δ|)) s) at 2.
      rewrite -> subst_app_decomp. f_equal.
      replace (S n) with ((S n - #|Δ|) + #|Δ|) by lia.
      assert (eq:#|(map (lift0 #|skipn (S (n - #|Δ|)) s|) (firstn (S (n - #|Δ|)) s))| = S n - #|Δ|).
      rewrite map_length. rewrite -> firstn_length by lia. lia.
      rewrite <- eq. rewrite -> simpl_subst_rec; auto; try lia.
      auto with wf. eapply subs_wf in sub; eauto.
      now apply All_Forall, All_firstn.

    + intros Hs.
      pose proof (subst_length _ _ _ _ sub).
      rewrite H1 in Hs.
      assert (S n = #|s| + (S (n - #|s|))) by lia.
      rewrite H2. rewrite simpl_subst; auto; try lia.
      constructor; auto.
      rewrite -> nth_error_app_context_ge; try lia; rewrite subst_context_length.
      rewrite -> 2!nth_error_app_context_ge in H0 by lia.
      rewrite <- H0. f_equal. lia.
      lia.

    + eapply subs_nth_error_lt in sub; eauto.
      rewrite H0 in sub. simpl in sub.
      eapply refine_type. constructor; eauto.
      rewrite <- map_decl_type.
      rewrite -> commut_lift_subst_rec by lia.
      f_equal. lia.

  - econstructor; auto. eapply X1; eauto.
    specialize (X1 Γ Γ' Δ s sub eq_refl wfsubs).
    specialize (X3 Γ Γ' (Δ,, vass n t) s sub eq_refl).
    rewrite subst_context_snoc0 in X3. forward X3.
    now econstructor; simpl; eauto.
    eapply X3.

  - econstructor; auto. eapply X1; eauto.
    specialize (X1 Γ Γ' Δ s sub eq_refl wfsubs).
    specialize (X3 Γ Γ' (Δ,, vass n t) s sub eq_refl).
    rewrite subst_context_snoc0 in X3. forward X3.
    now econstructor; simpl; eauto.
    eapply X3.

  - specialize (X1 Γ Γ' Δ s sub eq_refl wfsubs).
    specialize (X3 Γ Γ' Δ s sub eq_refl wfsubs).
    specialize (X5 Γ Γ' (Δ,, vdef n b b_ty) s sub eq_refl).
    rewrite subst_context_snoc0 in X5. forward X5.
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
    eapply on_declared_inductive in isdecl as [on_mind on_ind]; auto.
    apply onArity in on_ind as [s' Hindty].
    pose proof (typing_wf (Σ.1, ind_universes mdecl) wfΣ _ _ _ Hindty) as [clty _].
    apply typecheck_closed in Hindty as [_ Hindty]; eauto. symmetry.
    move/andP/proj1: Hindty. rewrite -(closedn_subst_instance_constr _ _ u) => Hty.
    apply: (subst_closedn s #|Δ|); auto with wf.
    eapply closed_upwards. eauto. simpl; lia.

  - eapply refine_type. econstructor; eauto.
    symmetry.
    apply on_declared_constructor in isdecl as [_ onc]; auto.
    eapply on_constructor_closed_wf in onc as [clty wfty]; auto.
    unfold type_of_constructor.
    apply subst_closedn; eauto. eapply closed_upwards; eauto. lia.

  - rewrite subst_mkApps map_app map_skipn.
    specialize (X2 Γ Γ' Δ s sub eq_refl wfsubs).
    specialize (X4 Γ Γ' Δ s sub eq_refl wfsubs).
    simpl. econstructor.
    4:{ eapply subst_types_of_case in H1.
        simpl in H1. subst pars. rewrite firstn_map. eapply H1; eauto.
        all:eauto.
        -- now apply subs_wf in sub.
        -- subst pars. eapply All_firstn.
           apply typing_wf in X3 as [_ X3]; eauto.
           now (apply (Forall_All); apply wf_mkApps_inv in X3).
        -- eapply typing_wf in X1; wf.
        -- eapply on_declared_inductive in isdecl as [Hmdecl Hidecl]; auto.
           apply onArity in Hidecl as [s' Hty]. now eapply typing_wf in Hty; eauto. }
    -- eauto.
    -- eauto.
    -- eauto.
    -- revert H2. subst pars.
       apply subst_check_correct_arity.
    -- destruct idecl; simpl in *; auto.
    -- now rewrite !subst_mkApps in X4.
    -- solve_all.

  - specialize (X2 Γ Γ' Δ s sub eq_refl wfsubs).
    eapply refine_type. econstructor.
    eauto.
    rewrite subst_mkApps in X2. eauto.
    rewrite map_length; eauto.
    rewrite <- (Nat.add_0_l #|Δ|).
    pose proof (subs_wf _ _ _ _ wfΣ sub).
    erewrite distr_subst_rec. simpl.
    rewrite map_rev. subst ty.
    f_equal.
    apply on_declared_projection in isdecl as [? isdecl]; auto.
    eapply on_projection_closed_wf in isdecl as [clty wfty]; auto.
    symmetry. apply subst_closedn; eauto.
    rewrite List.rev_length H0. eapply closed_upwards; eauto. lia. auto.
    destruct p0. now pose proof (onNpars _ _ _ _ o).
    auto.

  - assert (wf_local Σ (Γ ,,, subst_context s 0 Δ ,,, subst_context s #|Δ| (fix_context mfix))).
    subst types.
    apply All_local_env_app in X as [X Hfixc].
    apply All_local_env_app_inv. intuition.
    revert Hfixc. clear X0 X H0.
    induction 1; simpl; auto.
    + destruct t0 as [u [Ht IHt]].
      specialize (IHt Γ Γ' (Δ ,,, Γ0) s sub). forward IHt. now rewrite app_context_assoc.
      rewrite app_context_length subst_context_app app_context_assoc Nat.add_0_r in IHt.
      unfold snoc; rewrite subst_context_snoc; econstructor; auto. exists u.
        apply IHt; apply All_local_env_app_inv; intuition.
    + destruct t0 as [s' [Ht IHt]].
      specialize (IHt Γ Γ' (Δ ,,, Γ0) s sub). forward IHt. now rewrite app_context_assoc.
      rewrite app_context_length subst_context_app app_context_assoc Nat.add_0_r in IHt.
      unfold snoc; rewrite subst_context_snoc; econstructor; auto; hnf; simpl.
      eexists _. apply IHt; apply All_local_env_app_inv; intuition.
      destruct t1 as [Ht' IHt'].
      specialize (IHt' Γ Γ' (Δ ,,, Γ0) s sub). forward IHt'. now rewrite app_context_assoc.
      rewrite app_context_length subst_context_app app_context_assoc Nat.add_0_r in IHt'.
      apply IHt'; apply All_local_env_app_inv; intuition.
    + erewrite map_dtype. eapply type_Fix.
      * eapply fix_guard_subst. assumption.
      * rewrite nth_error_map H1. reflexivity.
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
        rewrite commut_lift_subst_rec. lia. now rewrite (Nat.add_comm #|Δ|).
        now apply isLambda_subst.


  - assert (wf_local Σ (Γ ,,, subst_context s 0 Δ ,,, subst_context s #|Δ| (fix_context mfix))).
    subst types.
    apply All_local_env_app in X as [X Hfixc].
    apply All_local_env_app_inv. intuition.
    revert Hfixc. clear X0 X H0.
    induction 1; simpl; auto.
    + destruct t0 as [u [Ht IHt]].
      specialize (IHt Γ Γ' (Δ ,,, Γ0) s sub). forward IHt. now rewrite app_context_assoc.
      rewrite app_context_length subst_context_app app_context_assoc Nat.add_0_r in IHt.
      unfold snoc; rewrite subst_context_snoc; econstructor; auto. exists u.
        apply IHt; apply All_local_env_app_inv; intuition.
    + destruct t0 as [s' [Ht IHt]].
      specialize (IHt Γ Γ' (Δ ,,, Γ0) s sub). forward IHt. now rewrite app_context_assoc.
      rewrite app_context_length subst_context_app app_context_assoc Nat.add_0_r in IHt.
      unfold snoc; rewrite subst_context_snoc; econstructor; auto; hnf; simpl.
      eexists _. apply IHt; apply All_local_env_app_inv; intuition.
      destruct t1 as [Ht' IHt'].
      specialize (IHt' Γ Γ' (Δ ,,, Γ0) s sub). forward IHt'. now rewrite app_context_assoc.
      rewrite app_context_length subst_context_app app_context_assoc Nat.add_0_r in IHt'.
      apply IHt'; apply All_local_env_app_inv; intuition.
    + erewrite map_dtype. eapply type_CoFix. auto.
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
        rewrite commut_lift_subst_rec. lia. now rewrite (Nat.add_comm #|Δ|).

  - assert(wfB : Ast.wf B).
    { destruct X2 as [Bs|[u Hu]].
      destruct Bs as [[ctx [u [Hd IH]]]]. simpl in *.
      generalize (destArity_spec [] B); rewrite Hd.
      move => /= ->. clear -wfΣ IH.
      eapply (it_mkProd_or_LetIn_wf (Γ ,,, Γ' ,,, Δ)).
      rewrite -it_mkProd_or_LetIn_app.
      eapply (wf_it_mkProd_or_LetIn _ _ IH); auto.
      induction IH; constructor; auto.
      destruct t0. split; try constructor.
      eapply typing_wf in t0. intuition. auto.
      eapply typing_wf in t1. intuition. auto.
      eapply typing_wf in t1. intuition. auto. constructor.
      destruct Hu. apply typing_wf in t0; intuition auto. }
    econstructor; eauto.
    destruct X2 as [Bs|[u Hu]].
    + left. destruct Bs as [[ctx [u [Hd IH]]]]. simpl in *.
      exists (subst_context s #|Δ| ctx), u.
      pose proof (subst_destArity [] B s #|Δ|). rewrite Hd in H0.
      rewrite {}H0; auto.
      split; auto.
      apply All_local_env_app_inv; intuition auto.
      clear -sub wfsubs a.
      induction ctx; try constructor; depelim a.
      -- rewrite subst_context_snoc.
         unfold snoc.
         econstructor; auto.
         eapply IHctx. eapply a.
         simpl. destruct tu as [u tu]. exists u.
         specialize (t0 _ _ (Δ ,,, ctx) _ sub). forward t0.
         now rewrite app_context_assoc. simpl in t0.
         forward t0. rewrite subst_context_app app_context_assoc Nat.add_0_r.
         apply All_local_env_app_inv. split; auto.
         eapply IHctx. eapply a.
         now rewrite subst_context_app Nat.add_0_r app_context_assoc app_length in t0.
      -- rewrite subst_context_snoc.
         constructor; auto.
         ++ eapply IHctx. eapply a.
         ++ simpl.
            specialize (t1 _ _ (Δ ,,, ctx) _ sub).
            forward t1. 1: now rewrite app_context_assoc.
            simpl in t1.
            forward t1.
            { rewrite subst_context_app app_context_assoc Nat.add_0_r.
              apply All_local_env_app_inv. split; auto.
              eapply IHctx. eapply a.
            }
            now rewrite subst_context_app Nat.add_0_r app_context_assoc app_length in t1.
         ++ simpl.
            specialize (t0 _ _ (Δ ,,, ctx) _ sub). forward t0.
            1: now rewrite app_context_assoc. simpl in t0.
            forward t0.
            { rewrite subst_context_app app_context_assoc Nat.add_0_r.
              apply All_local_env_app_inv. split; auto.
              eapply IHctx. eapply a.
            }
            now rewrite subst_context_app Nat.add_0_r app_context_assoc app_length in t0.
    + right; exists u; intuition eauto.
    + eapply substitution_cumul; eauto.
      now eapply typing_wf in X0.
Qed.

Theorem substitution_alt `{checker_flags} Σ Γ Γ' s Δ (t : term) T :
  wf Σ.1 -> subs Σ Γ s Γ' ->
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
  - destruct t1. eapply substitution in t1; simpl in *; eauto.
    eapply All_local_env_app_inv; intuition.
  - destruct t1. eapply substitution in t1; simpl in *; eauto.
    eapply All_local_env_app_inv; intuition.
  - destruct t1. eapply substitution in t2; simpl in *; eauto.
    eapply All_local_env_app_inv; intuition.
Qed.

Lemma substitution0 `{checker_flags} Σ Γ n u U (t : term) T :
  wf Σ.1 ->
  Σ ;;; Γ ,, vass n U |- t : T -> Σ ;;; Γ |- u : U ->
  Σ ;;; Γ |- t {0 := u} : T {0 := u}.
Proof.
  intros HΣ Ht Hu.
  assert (wfΓ : wf_local Σ Γ).
  apply typing_wf_local in Hu; eauto.
  pose proof (substitution_alt Σ Γ [vass n U] [u] [] t T HΣ) as thm.
  forward thm. constructor. constructor. rewrite subst_empty; auto.
  apply typing_wf in Hu; intuition.
  now apply (thm Ht).
Qed.
