(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia.
From Template Require Import config utils BasicAst AstUtils.
From PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICWeakeningEnv PCUICClosed PCUICWeakening.
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

(** Linking a cantext (with let-ins), an instance (reversed substitution)
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

Lemma subst_decl0 k d : map_decl (subst [] k) d = d.
Proof.
  destruct d; destruct decl_body;
    unfold subst_decl, map_decl; simpl in *;
    f_equal; simpl; rewrite subst_empty; intuition trivial.
Qed.

Lemma subst0_context k Γ : subst_context [] k Γ = Γ.
Proof.
  unfold subst_context, fold_context.
  rewrite rev_mapi. rewrite List.rev_involutive.
  unfold mapi. generalize 0. generalize #|List.rev Γ|.
  induction Γ; intros; simpl; trivial.
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

Lemma map_vass_map_def_subst g l n k :
  (mapi (fun i (d : def term) => vass (dname d) (lift0 i (dtype d)))
        (map (map_def (subst n k) g) l)) =
  (mapi (fun i d => map_decl (subst n (i + k)) d) (mapi (fun i (d : def term) => vass (dname d) (lift0 i (dtype d))) l)).
Proof.
  rewrite mapi_mapi mapi_map. apply mapi_ext.
  intros. unfold map_decl, vass; simpl; f_equal.
  rewrite commut_lift_subst_rec. lia. f_equal; lia.
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
  unfold_fix mfix idx = Some (narg, fn) ->
  unfold_fix (map (map_def (subst n k) (subst n (#|mfix| + k))) mfix) idx = Some (narg, subst n k fn).
Proof.
  unfold unfold_fix.
  rewrite nth_error_map. destruct (nth_error mfix idx) eqn:Hdef; try congruence.
  move=> [= <- <-] /=. f_equal. f_equal.
  solve_all.
  erewrite (distr_subst_rec _ _ _ k 0).
  rewrite fix_subst_length. simpl. f_equal.
  unfold fix_subst. rewrite !map_length.
  generalize #|mfix| at 2 3. induction n0; auto. simpl.
  f_equal. apply IHn0.
Qed.
Hint Resolve subst_unfold_fix.

Lemma subst_unfold_cofix n k mfix idx narg fn :
  unfold_cofix mfix idx = Some (narg, fn) ->
  unfold_cofix (map (map_def (subst n k) (subst n (#|mfix| + k))) mfix) idx = Some (narg, subst n k fn).
Proof.
  unfold unfold_cofix.
  rewrite nth_error_map. destruct (nth_error mfix idx) eqn:Hdef; try congruence.
  intros [= <- <-]. simpl. do 2 f_equal. solve_all.
  erewrite (distr_subst_rec _ _ _ k 0).
  rewrite cofix_subst_length. simpl. f_equal.
  unfold cofix_subst. rewrite !map_length.
  generalize #|mfix| at 2 3. induction n0; auto. simpl.
  f_equal. apply IHn0.
Qed.
Hint Resolve subst_unfold_cofix.

Lemma decompose_app_rec_subst n k t l :
  let (f, a) := decompose_app_rec t l in
  subst n k f = f ->
  decompose_app_rec (subst n k t) (map (subst n k) l)  = (f, map (subst n k) a).
Proof.
  induction t in k, l |- *; simpl; auto; try congruence.

  destruct Nat.leb; try reflexivity. destruct nth_error. simpl. intros ->. simpl. reflexivity.
  intros ->. simpl. reflexivity.
  specialize (IHt1 k (t2 :: l)).
  destruct decompose_app_rec. intros H. rewrite IHt1; auto.
Qed.

Lemma decompose_app_subst n k t f a :
  decompose_app t = (f, a) -> subst n k f = f ->
  decompose_app (subst n k t) = (subst n k f, map (subst n k) a).
Proof.
  generalize (decompose_app_rec_subst n k t []).
  unfold decompose_app. destruct decompose_app_rec.
  move=> Heq [= <- <-] Heq'. now rewrite Heq' (Heq Heq').
Qed.
Hint Rewrite decompose_app_subst using auto : lift.

Lemma subst_is_constructor:
  forall (args : list term) (narg : nat) n k,
    is_constructor narg args = true -> is_constructor narg (map (subst n k) args) = true.
Proof.
  intros args narg.
  unfold is_constructor; intros.
  rewrite nth_error_map. destruct nth_error; try discriminate. simpl. intros.
  destruct (decompose_app t) eqn:Heq. eapply decompose_app_subst in Heq as ->.
  destruct t0; try discriminate || reflexivity.
  destruct t0; try discriminate || reflexivity.
Qed.
Hint Resolve subst_is_constructor.
Hint Constructors All_local_env.

Lemma typed_subst `{checker_flags} Σ Γ t T n k :
  wf Σ -> k >= #|Γ| ->
  Σ ;;; Γ |- t : T -> subst n k T = T /\ subst n k t = t.
Proof.
  intros wfΣ Hk Hty.
  pose proof (typing_wf_local Hty).
  apply typecheck_closed in Hty; eauto.
  destruct Hty as [_ Hcl].
  rewrite -> andb_and in Hcl. destruct Hcl as [clb clty].
  pose proof (closed_upwards k clb).
  simpl in *. forward H0 by lia.
  pose proof (closed_upwards k clty).
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

Lemma subst_declared_constant `{checker_flags} Σ cst decl n k u :
  wf Σ ->
  declared_constant (fst Σ) cst decl ->
  map_constant_body (subst n k) (map_constant_body (subst_instance_constr u) decl) =
  map_constant_body (subst_instance_constr u) decl.
Proof.
  intros.
  eapply declared_decl_closed in H0; eauto.
  unfold map_constant_body.
  do 2 red in H0. destruct decl as [ty [body|] univs]; simpl in *.
  rewrite -> andb_and in H0. intuition.
  rewrite <- (closedn_subst_instance_constr 0 body u) in H1.
  rewrite <- (closedn_subst_instance_constr 0 ty u) in H2.
  f_equal. apply subst_closedn; eauto using closed_upwards with arith wf.
  f_equal. apply subst_closedn; eauto using closed_upwards with arith wf.
  red in H0. f_equal.
  intuition. simpl in *.
  rewrite <- (closedn_subst_instance_constr 0 ty u) in H0.
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
    unfold on_pi2; f_equal; f_equal. eapply typed_subst. 3:eapply Hty. eauto. simpl. lia.
    apply (Alli_map_id onProjections).
    intros n1 [x p]. unfold on_projection; simpl.
    destruct decompose_prod_assum.
    intros [[s Hty] Hpars].
    unfold on_snd; f_equal; f_equal.
    eapply typed_subst. 3:eapply Hty. eauto. simpl. injection Heq. intros -> ->. lia.
Qed.

Lemma subst_declared_inductive `{checker_flags} Σ ind mdecl idecl n k :
  wf Σ ->
  declared_inductive (fst Σ) mdecl ind idecl ->
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

Lemma subst0_inds_subst ind u mdecl n k t :
  (subst0 (inds (inductive_mind ind) u (ind_bodies mdecl))
          (subst n (#|arities_context (ind_bodies mdecl)| + k) t)) =
  subst n k (subst0 (inds (inductive_mind ind) u (ind_bodies mdecl)) t).
Proof.
  pose proof (distr_subst_rec t (inds (inductive_mind ind) u (ind_bodies mdecl)) n k 0).
  simpl in H. rewrite H.
  unfold arities_context. rewrite rev_map_length inds_length.
  f_equal. generalize (ind_bodies mdecl).
  clear. intros.
  induction l; unfold inds; simpl; auto. f_equal. auto.
Qed.

Lemma subst_declared_constructor `{checker_flags} Σ c u mdecl idecl cdecl n k :
  wf Σ -> declared_constructor (fst Σ) mdecl idecl c cdecl ->
  subst (map (subst_instance_constr u) n) k (type_of_constructor mdecl cdecl c u) = (type_of_constructor mdecl cdecl c u).
Proof.
  unfold declared_constructor. destruct c as [i ci]. intros wfΣ [Hidecl Hcdecl].
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
  rewrite <- subst0_inds_subst. f_equal.
  now rewrite <- subst_subst_instance_constr.
Qed.

Lemma subst_declared_projection `{checker_flags} Σ c mdecl idecl pdecl n k :
  wf Σ ->
  declared_projection (fst Σ) mdecl idecl c pdecl ->
  on_snd (subst n (S (ind_npars mdecl + k))) pdecl = pdecl.
Proof.
  intros wfΣ Hd.
  destruct Hd as [[Hmdecl Hidecl] Hpdecl].
  eapply declared_decl_closed in Hmdecl.
  simpl in Hmdecl.
  apply onInductives in Hmdecl.
  eapply nth_error_alli in Hmdecl; eauto.
  eapply onProjections in Hmdecl; eauto.
  eapply nth_error_alli in Hmdecl; eauto.
  red in Hmdecl.
  destruct decompose_prod_assum eqn:Heq.
  case: Hmdecl => [/andb_and[Hb Ht] Hpars].
  intuition auto. destruct pdecl as [id ty]. unfold on_snd; simpl in *.
  f_equal. eapply subst_closedn; auto. rewrite <- Hpars. eapply closed_upwards; eauto. lia. auto.
Qed.

Lemma subst_fix_context:
  forall (mfix : list (def term)) n (k : nat),
    fix_context (map (map_def (subst n k) (subst n (#|mfix| + k))) mfix) =
    subst_context n k (fix_context mfix).
Proof.
  intros mfix n k. unfold fix_context.
  rewrite map_vass_map_def_subst rev_mapi.
  fold (fix_context mfix).
  rewrite (subst_context_alt n k (fix_context mfix)).
   now rewrite /subst_decl mapi_length fix_context_length.
Qed.

Lemma subst_destArity ctx t n k :
  match destArity ctx t with
  | Some (args, s) =>
    destArity (subst_context n k ctx) (subst n (#|ctx| + k) t) = Some (subst_context n k args, s)
  | None => True
  end.
Proof.
  revert ctx.
  induction t in n, k |- * using term_forall_list_ind; intros ctx; simpl; trivial.

  - move: (IHt2 n k (ctx,, vass n0 t1)).
    now rewrite subst_context_snoc /= /subst_decl /map_decl /vass /=.
  - move: (IHt3 n k (ctx,, vdef n0 t1 t2)).
    now rewrite subst_context_snoc /= /subst_decl /map_decl /vass /=.
Qed.

Lemma decompose_prod_n_assum0 ctx t : decompose_prod_n_assum ctx 0 t = Some (ctx, t).
Proof. destruct t; simpl; reflexivity. Qed.

(* Definition strip_outer_cast_tProd_tLetIn_morph f := *)
(*   forall t k, *)
(*   match strip_outer_cast t with *)
(*   | tProd na A B => *)
(*     strip_outer_cast (f k t) = tProd na (f k A) (f (S k) B) *)
(*   | tLetIn na b ty b' => *)
(*     strip_outer_cast (f k t) = tLetIn na (f k b) (f k ty) (f (S k) b') *)
(*   | _ => True *)
(*   end. *)

(* Lemma strip_outer_cast_tProd_tLetIn_subst n : *)
(*   strip_outer_cast_tProd_tLetIn_morph (subst n). *)
(* Proof. *)
(*   unfold strip_outer_cast_tProd_tLetIn_morph. intros t k. *)
(*   induction t; simpl in *; auto. *)
(* Qed. *)

(* Lemma strip_outer_cast_subst_instance_constr u t : *)
(*   strip_outer_cast (subst_instance_constr u t) = *)
(*   subst_instance_constr u (strip_outer_cast t). *)
(* Proof. induction t; simpl; auto. Qed. *)

(* Lemma strip_outer_cast_tProd_tLetIn_subst_instance_constr u : *)
(*   strip_outer_cast_tProd_tLetIn_morph (fun _ => subst_instance_constr u). *)
(* Proof. *)
(*   red. intros. *)
(*   destruct (strip_outer_cast t) eqn:Heq; try auto. *)
(*   rewrite strip_outer_cast_subst_instance_constr. now rewrite Heq. *)
(*   rewrite strip_outer_cast_subst_instance_constr. now rewrite Heq. *)
(* Qed. *)

Lemma subst_instantiate_params_subst n k params args s t :
  forall s' t',
    instantiate_params_subst params args s t = Some (s', t') ->
    instantiate_params_subst
      (mapi_rec (fun k' decl => subst_decl n (k' + k) decl) params #|s|)
      (map (subst n k) args) (map (subst n k) s) (subst n (#|s| + k) t) =
    Some (map (subst n k) s', subst n (#|s| + k + #|params|) t').
Proof.
  induction params in args, t, n, k, s |- *; intros ctx' t'.
  - destruct args; simpl; rewrite ?Nat.add_0_r; try congruence.
  - simpl.
    destruct a as [na [body|] ty]; simpl; try congruence;
    destruct t; try congruence.
    -- intros Ht'.
       specialize (IHparams n k _ _ _ _ _ Ht').
       simpl in IHparams.
       replace (#|s| + k + S #|params|) with (S (#|s| + k + #|params|)) by lia.
       rewrite <- IHparams. f_equal.
       now rewrite distr_subst.
    -- intros Ht'. destruct args; try congruence. simpl.
       specialize (IHparams n k _ _ _ _ _ Ht').
       simpl in IHparams.
       replace (#|s| + k + S #|params|) with (S (#|s| + k + #|params|)) by lia.
       now rewrite <- IHparams.
Qed.

Lemma subst_decl_closed n k d : closed_decl k d -> subst_decl n k d = d.
Proof.
  case: d => na [body|] ty; rewrite /closed_decl /subst_decl /map_decl /=.
  move/andP => [cb cty]. rewrite !subst_closedn //.
  move=> cty; now rewrite !subst_closedn //.
Qed.

Lemma closed_ctx_subst n k ctx : closed_ctx ctx = true -> subst_context n k ctx = ctx.
Proof.
  induction ctx in n, k |- *; auto.
  unfold closed_ctx, id.
  rewrite mapi_app forallb_app List.rev_length /= Nat.add_0_r.
  move/andb_and => /= [Hctx /andb_and [Ha _]].
  rewrite subst_context_snoc /snoc /= IHctx // subst_decl_closed //.
  now apply: closed_decl_upwards.
Qed.

Lemma closed_tele_subst n k ctx :
  closed_ctx ctx ->
  mapi (fun (k' : nat) (decl : context_decl) => subst_decl n (k' + k) decl) (List.rev ctx) = List.rev ctx.
Proof.
  rewrite /closed_ctx /mapi. generalize 0.
  induction ctx using rev_ind; try easy.
  move=> n0.
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
  destruct t; simpl; try congruence.
  intros H. eapply (IHn _ _ _ _ ctx'' H).
  intros H. eapply (IHn _ _ _ _ ctx'' H).
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
  symmetry. solve_all.
  destruct H as [x' [-> Hx']]. intuition. simpl.
  destruct (leb_spec_Set k x'). lia. reflexivity.
Qed.

Lemma subst_instantiate_params n k params args t ty :
  closed_ctx params ->
  instantiate_params params args t = Some ty ->
  instantiate_params params (map (subst n k) args) (subst n k t) = Some (subst n k ty).
Proof.
  unfold instantiate_params.
  move/(closed_tele_subst n k params)=> Heq.
  rewrite -{2}Heq //.
  specialize (subst_instantiate_params_subst n k (List.rev params) args [] t).
  move=> /= Heq'.
  case E: (instantiate_params_subst (List.rev params) args)=> [[l' t']|] /= //.
  specialize (Heq' _ _ E). rewrite Heq'. move=> [= <-]. f_equal.
  rewrite distr_subst //.
  move/instantiate_params_subst_length: E => -> /=. do 2 f_equal. lia.
Qed.
Hint Rewrite subst_instantiate_params : lift.

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
  rewrite -> andb_and in Hs. destruct Hs as [Hs Ht].
  simpl in Hs. apply (lift_closed #|arities_context l|) in Hs.
  rewrite -> Hs, app_context_nil_l in X.
  apply X.
Qed.

Lemma on_constructor_closed `{checker_flags} {Σ mind mdecl u i idecl cdecl} :
  wf Σ ->
  on_constructor (lift_typing typing) Σ (inductive_mind mind) mdecl (inductive_ind mind) idecl i cdecl ->
  let cty := subst0 (inds (inductive_mind mind) u (ind_bodies mdecl))
                    (subst_instance_constr u (snd (fst cdecl)))
  in closed cty.
Proof.
  intros wfΣ [[s Hs] Hparams].
  pose proof (typing_wf_local Hs).
  destruct cdecl as [[id cty] car].
  eapply (env_prop_typing _ typecheck_closed) in Hs; eauto.
  rewrite arities_context_length in Hs.
  rewrite -> andb_and in *. simpl in *.
  destruct Hs as [Hs _].
  eapply (closedn_subst _ 0 0).
  clear. unfold inds. induction #|ind_bodies mdecl|; simpl; try constructor; auto.
  simpl. now rewrite -> inds_length, closedn_subst_instance_constr.
Qed.

Lemma on_projection_closed `{checker_flags} {Σ mind mdecl u i idecl pdecl} :
  wf Σ ->
  on_projection (lift_typing typing) Σ (inductive_mind mind) mdecl (inductive_ind mind) idecl i pdecl ->
  let pty := subst_instance_constr u (snd pdecl) in
  closedn (S (ind_npars mdecl)) pty.
Proof.
  intros wfΣ. unfold on_projection.
  destruct decompose_prod_assum.
  intros [[s Hs] Hparams].
  pose proof (typing_wf_local Hs).
  destruct pdecl as [id cty].
  eapply (env_prop_typing _ typecheck_closed) in Hs; eauto.
  rewrite -> andb_and in *. simpl in *.
  destruct Hs as [Hs _].
  rewrite Hparams in Hs. now rewrite -> closedn_subst_instance_constr.
Qed.

Lemma context_subst_length Γ a s : context_subst Γ a s -> #|Γ| = #|s|.
Proof. induction 1; simpl; congruence. Qed.

Lemma context_subst_assumptions_length Γ a s : context_subst Γ a s -> context_assumptions Γ = #|a|.
Proof. induction 1; simpl; try congruence. rewrite app_length /=. lia. Qed.

(* Lemma context_subst_app `{cf:checker_flags} Γ Γ' a s : *)
(*   context_subst (Γ' ++ Γ) a s -> *)
(*   { a0 & { a1 & { s0 & { s1 & (context_subst Γ a0 s0 * context_subst (subst_context s0 0 Γ') a1 s1 *)
(*                                * (a = a0 ++ a1) * (s = s1 ++ s0))%type } } } }. *)
(* Proof. *)
(*   induction Γ' in Γ, a, s |- *. simpl. *)
(*   exists a, [], s, []. rewrite app_nil_r; intuition. constructor. *)

(*   simpl. intros Hs. *)
(*   inv Hs. *)
(*   - specialize (IHΓ' _ _ _ H). *)
(*     destruct IHΓ' as (a0' & a1' & s1 & s2 & ((sa0 & sa1) & eqargs) & eqs0). *)
(*     subst. exists a0', (a1' ++ [a1]), s1, (a1 :: s2). intuition eauto. *)
(*     rewrite subst_context_snoc. constructor. auto. now rewrite app_assoc. *)
(*   - specialize (IHΓ' _ _ _ H). *)
(*     destruct IHΓ' as (a0' & a1' & s1 & s2 & ((sa0 & sa1) & eqargs) & eqs0). *)
(*     subst. exists a0', a1', s1, (subst s2 0 (subst s1 #|Γ'| b) :: s2). intuition eauto. *)
(*     rewrite -> subst_context_snoc, Nat.add_0_r. *)
(*     unfold subst_decl; simpl. unfold map_decl. simpl. *)
(*     econstructor. auto. simpl. f_equal. *)
(*     rewrite -> subst_app_simpl; auto. simpl. *)
(*     pose proof(context_subst_length _ _ _ sa1) as Hs1. *)
(*     rewrite subst_context_length in Hs1. rewrite -> Hs1. auto. *)
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
    eapply (decompose_prod_n_assum_extend_ctx [vdef n ty1 ty2]) in Hdecomp.
    unfold snoc. eexists; intuition eauto.
  - destruct ty; try congruence.
    case: args => [|a args']; try congruence.
    move=> H. move: (IHctx _ _ _ _ H) => [ctx'' [Hmake Hdecomp]].
    eapply (decompose_prod_n_assum_extend_ctx [vass n ty1]) in Hdecomp.
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
  make_context_subst (List.rev ctx) args [] = Some s ->
  map (subst s k) (to_extended_list_k ctx k) = map (lift0 k) args.
Proof.
  move/make_context_subst_spec. rewrite List.rev_involutive.
  move=> H; induction H; simpl; auto.
  - rewrite map_app -IHcontext_subst //.
    rewrite to_extended_list_k_cons /= !map_app.
    f_equal.
    rewrite (lift_to_extended_list_k _ _ 1) map_map_compose.
    pose proof (to_extended_list_k_spec Γ k).
    solve_all. destruct H0 as [n [-> Hn]].
    rewrite /compose /lift (subst_app_decomp [a] s k); auto with wf.
    rewrite subst_rel_gt. simpl; lia.
    repeat (f_equal; simpl; try lia).
    now rewrite /map (subst_rel_eq _ _ 0 a).
  - rewrite -IHcontext_subst // to_extended_list_k_cons /=.
    rewrite (lift_to_extended_list_k _ _ 1) map_map_compose.
    pose proof (to_extended_list_k_spec Γ k).
    solve_all. destruct H0 as [n [-> Hn]].
    rewrite /compose /lift (subst_app_decomp [subst0 s b] s k); auto with wf.
    rewrite subst_rel_gt. simpl; lia.
    repeat (f_equal; simpl; try lia).
Qed.

(** check_correct_arity is probably wrong, w.r.t. let-ins reduced or not at least  *)
Lemma subst_types_of_case `{cf:checker_flags} Σ ind mdecl idecl args u p pty indctx pctx ps btys n k :
  let f (ctx : context) := subst n (#|ctx| + k) in
  let f_ctx := subst_context n k in
  wf Σ ->
  declared_inductive (fst Σ) mdecl ind idecl ->
  types_of_case ind mdecl idecl args u p pty = Some (indctx, pctx, ps, btys) ->
  types_of_case ind mdecl idecl (map (f []) args) u (f [] p) (f [] pty) =
  Some (f_ctx indctx, f_ctx pctx, ps, map (on_snd (f [])) btys).
Proof.
  simpl. intros wfΣ wfidecl. simpl.
  epose proof (subst_declared_inductive _ ind mdecl idecl n k wfΣ).
  forward H. auto. rewrite <- H at 2.
  unfold types_of_case.
  pose proof (subst_destArity [] (ind_type idecl) n k); trivial. simpl in H.
  unfold subst_context, fold_context in H0. simpl in H0. rewrite ind_type_map. simpl.
  destruct destArity as [[ctx s] | ]; try congruence.
  rewrite H0. clear H0.
  pose proof (subst_destArity [] pty n k); trivial. simpl in H.
  destruct (destArity [] pty) as [[ctx' s'] | ]; try congruence.
  unfold subst_context at 1 in H0. unfold fold_context in H0. simpl in H0.
  rewrite H0; clear H0.
  destruct map_option_out eqn:Hbrs; try congruence.
  intros [= -> -> -> ->].
  pose proof (on_declared_inductive wfΣ wfidecl) as [onmind onind].
  apply onParams in onmind as Hparams.
  assert(closedparams : closed_ctx (ind_params mdecl)).
  eapply closed_wf_local; eauto.
  assert(forall brs,
         map_option_out (build_branches_type ind mdecl idecl args u p) = Some brs ->
         map_option_out (build_branches_type ind mdecl
         (map_one_inductive_body (inductive_mind ind) (polymorphic_instance (ind_universes mdecl))
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
    pose proof (on_constructor_closed wfΣ (u:=u) Honc) as clt.
    simpl in *.
    eapply (closed_upwards k) in clt; try lia.
    rewrite (subst_closedn (map (subst_instance_constr u) n) k _ clt).
    rewrite <- (subst_closedn n k _ clt) at 2.
    case Heq : instantiate_params => [ty|] /=; try congruence.
    remember (subst0 (inds (inductive_mind ind) u (ind_bodies mdecl)) (subst_instance_constr u t)) as
        ty'.
    eapply subst_instantiate_params in Heq as Heq'. rewrite -> Heq'. all:auto with wf.
    eapply instantiate_params_make_context_subst in Heq.
    destruct Heq as [ctx' [ty'' [s' [Hty [Hsubst Ht0]]]]].
    subst ty. simpl.

    rewrite Heqty' in Hty.
    destruct Honc. destruct c.
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

    rewrite (subst_cstr_concl_head ind u mdecl cshape_arity cshape_args).
    destruct wfidecl as [Hmdecl Hnth].
    now apply nth_error_Some_length in Hnth.
    intros <-. rewrite !subst_it_mkProd_or_LetIn !subst_mkApps /=.
    rewrite !decompose_prod_assum_it_mkProd /=; try by rewrite is_ind_app_head_mkApps.
    rewrite !decompose_app_mkApps; try by reflexivity.
    simpl. rewrite !map_app !subst_context_length !subst_instance_context_length Nat.add_0_r.
    rewrite !(subst_to_extended_list_k _ _ args) //.

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
    move: {chopm}(chopm _ (subst n (#|cshape_arity| + k))).
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
       now rewrite to_extended_list_k_subst. }
  specialize (H0 _ Hbrs). now rewrite H0.
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

(* Lemma red1_mkApp Σ Γ M1 N1 M2 : *)
(*   red1 Σ Γ M1 N1 -> red1 Σ Γ (mkApp M1 M2) (mkApp N1 M2). *)
(* Proof. *)
(*   intros wfM1 H. *)
(*   destruct (isApp M1) eqn:Heq. *)
(*   destruct M1; try discriminate. simpl. *)
(*   revert wfM1. inv H. simpl. intros. *)
(*   rewrite mkApp_mkApps. constructor. *)

(*   intros. inv wfM1. simpl. *)
(*   econstructor; eauto. *)
(*   clear -H1. *)
(*   unfold is_constructor in *. *)
(*   destruct (nth_error l narg) eqn:Heq. *)
(*   eapply nth_error_app_left in Heq. now rewrite -> Heq. discriminate. *)

(*   intros. rewrite mkApp_mkApps. now constructor. *)

(*   intros. simpl. *)
(*   constructor. clear -H0. induction H0; constructor; auto. *)

(*   rewrite mkApp_tApp; auto. *)
(*   now apply red1_tApp_mkApp. *)
(* Qed. *)

Lemma red1_mkApps_l Σ Γ M1 N1 M2 :
  red1 Σ Γ M1 N1 -> red1 Σ Γ (mkApps M1 M2) (mkApps N1 M2).
Proof.
  induction M2 in M1, N1 |- *. simpl; auto.
  intros. specialize (IHM2 (tApp M1 a) (tApp N1 a)).
  forward IHM2. constructor. auto.
  simpl. auto.
Qed.

Lemma red1_mkApps_r Σ Γ M1 M2 N2 :
  OnOne2 (red1 Σ Γ) M2 N2 -> red1 Σ Γ (mkApps M1 M2) (mkApps M1 N2).
Proof.
  intros. induction X in M1 |- *.
  simpl. eapply red1_mkApps_l. constructor; auto.
  apply (IHX (tApp M1 hd)).
Qed.

Lemma substitution_red1 `{CF:checker_flags} Σ Γ Γ' Γ'' s M N :
  wf Σ -> subs Σ Γ s Γ' -> wf_local Σ Γ ->
  red1 (fst Σ) (Γ ,,, Γ' ,,, Γ'') M N ->
  red1 (fst Σ) (Γ ,,, subst_context s 0 Γ'') (subst s #|Γ''| M) (subst s #|Γ''| N).
Proof.
  intros wfΣ Hs wfΓ H.
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
    + rewrite -> nth_error_app_context_lt in H by lia.
      pose (commut_lift_subst_rec body s (S i) (#|Γ''| - S i) 0).
      assert(eq:#|Γ''| - S i + S i = #|Γ''|) by lia.
      rewrite -> eq in e. rewrite <- e by lia.
      constructor.
      rewrite -> nth_error_app_context_lt by (autorewrite with wf; lia).
      rewrite -> nth_error_subst_context.
      unfold subst_decl; now rewrite -> option_map_decl_body_map_decl, H, Nat.add_0_r.

  - rewrite subst_iota_red.
    constructor.

  - pose proof (subst_declared_constant _ _ _ s #|Γ''| u wfΣ H).
    apply (f_equal cst_body) in H1.
    rewrite <- !map_cst_body in H1. rewrite H0 in H1. simpl in H1.
    injection H1. intros ->.
    econstructor. eauto. eauto.

  - simpl. constructor.
    now rewrite nth_error_map H.

  - constructor.
    specialize (IHred1 Γ0 Γ' (Γ'' ,, vass na N) eq_refl).
    now rewrite subst_context_snoc0 in IHred1.

  - constructor.
    specialize (IHred1 Γ0 Γ' (Γ'' ,, _) eq_refl).
    now rewrite subst_context_snoc0 in IHred1.

  - constructor.
    induction X; constructor; auto.
    intuition; eauto.
    specialize (b0 _ _ _ eq_refl).
    destruct hd, hd'; simpl in *. now eapply b0.

  - constructor. specialize (IHred1 _ _ (Γ'' ,, vass na M1) eq_refl).
    now rewrite subst_context_snoc0 in IHred1.

  - constructor.
    induction X; constructor; auto.
    intuition. eapply b; eauto.

  - constructor.
    rewrite -> (OnOne2_length X). generalize (#|mfix1|).
    induction X; simpl; constructor; auto.
    intuition. eapply b; eauto.

  - apply fix_red_body. rewrite !subst_fix_context.
    solve_all.
    rewrite <- (OnOne2_length X).
    eapply OnOne2_map. unfold on_Trel; solve_all.
    specialize (b Γ0 Γ' (Γ'' ,,, fix_context mfix0)).
    rewrite app_context_assoc in b. specialize (b eq_refl).
    rewrite -> app_context_length, fix_context_length in *.
    rewrite -> subst_context_app in *.
    rewrite -> app_context_assoc, Nat.add_0_r in *.
    auto.

  - constructor.
    rewrite -> (OnOne2_length X). generalize (#|mfix1|).
    induction X; simpl; constructor; auto.
    intuition auto. eapply b; eauto.
    now rewrite <- !map_dbody, b0.

  - apply cofix_red_body. rewrite !subst_fix_context.
    solve_all.
    rewrite <- (OnOne2_length X).
    eapply OnOne2_map. unfold on_Trel; solve_all.
    specialize (b Γ0 Γ' (Γ'' ,,, fix_context mfix0)).
    rewrite app_context_assoc in b. specialize (b eq_refl).
    rewrite -> app_context_length, fix_context_length in *.
    rewrite -> subst_context_app in *.
    rewrite -> app_context_assoc, Nat.add_0_r in *.
    auto.
Qed.

Lemma eq_term_refl `{checker_flags} φ t : eq_term φ t t.
Proof.
  induction t using term_forall_list_ind; simpl; try reflexivity; try discriminate;
    try (rewrite -> ?IHt1, ?IHt2, ?IHt3; reflexivity).

  - apply Nat.eqb_refl.
  - apply eq_string_refl.
  - apply Nat.eqb_refl.
  - rewrite /eq_evar eq_nat_refl.
    simpl. induction H0; simpl; auto. now rewrite H0 IHForall.
  - apply eq_universe_refl.
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
    try (merge_All; close_Forall; intuition auto);
    try (rewrite -> ?IHt1, ?IHt2, ?IHt3; reflexivity).

  - destruct u; auto. now apply eq_universe_leq_universe.
  - destruct u; try discriminate.
    rewrite -> andb_true_iff in *. intuition.
  - destruct u; try discriminate.
    rewrite -> andb_true_iff in *. intuition.
  - destruct u; try discriminate.
    rewrite -> andb_true_iff in *. intuition.
Qed.

Lemma eq_term_App `{checker_flags} φ f f' :
  eq_term φ f f' ->
  isApp f = isApp f'.
Proof.
  destruct f, f'; simpl; try congruence.
  destruct p; congruence.
Qed.

Lemma eq_term_mkApps `{checker_flags} φ f l f' l' :
  eq_term φ f f' ->
  forallb2 (eq_term φ) l l' ->
  eq_term φ (mkApps f l) (mkApps f' l').
Proof.
  induction l in f, f', l' |- *; destruct l'; try (simpl; congruence).
  intros.
  apply andb_and in H1 as [Ht Hl].
  apply (IHl (tApp f a) (tApp f' t) l').
  simpl; now rewrite H0 Ht.
  apply Hl.
Qed.

Lemma leq_term_mkApps `{checker_flags} φ f l f' l' :
  eq_term φ f f' ->
  forallb2 (eq_term φ) l l' ->
  leq_term φ (mkApps f l) (mkApps f' l').
Proof.
  induction l in f, f', l' |- *; destruct l'; try (simpl; congruence).
  intros. simpl. now apply eq_term_leq_term.
  intros H0 H1. apply andb_and in H1 as [Ht Hl].
  apply (IHl (tApp f a) (tApp f' t) l').
  simpl; now rewrite H0 Ht.
  apply Hl.
Qed.

Lemma subst_eq_term `{checker_flags} ϕ n k T U :
  eq_term ϕ T U ->
  eq_term ϕ (subst n k T) (subst n k U).
Proof.
  intros Hleq.
  induction T in n, k, U, Hleq |- * using term_forall_list_ind; intros;
    destruct U; try discriminate;
  try solve [simpl; auto]; try
                             (destruct (mkApps_trans_wf _ _ H0) as [U' [V' ->]]; reflexivity);
  simpl in *; revert Hleq; try rewrite -> !andb_and in *; intuition auto;
    try solve [solve_all; intuition auto].

  - intros.
    apply Nat.eqb_eq in Hleq. subst.
    destruct (leb_spec_Set k n1).
    destruct nth_error eqn:Heq. apply eq_term_refl.
    apply eq_term_refl.
    apply eq_term_refl.

  - destruct p. destruct Nat.leb. discriminate. discriminate.
  - destruct p, p0. toProp; solve_all. solve_all. simpl. destruct y. simpl. auto.
  - assert (#|m| = #|m0|) as <-. solve_all. clear -H2. induction H2; simpl; auto.
    repeat (toProp; solve_all).
  - assert (#|m| = #|m0|) as <-. solve_all. clear -H2. induction H2; simpl; auto.
    repeat (toProp; solve_all).
Qed.

Lemma subst_leq_term `{checker_flags} ϕ n k T U :
  leq_term ϕ T U ->
  leq_term ϕ (subst n k T) (subst n k U).
Proof.
  intros Hleq.
  induction T in n, k, U, Hleq |- * using term_forall_list_ind; intros;
    destruct U; try discriminate;
  try solve [simpl; auto]; try
                             (destruct (mkApps_trans_wf _ _ H0) as [U' [V' ->]]; reflexivity);
  simpl in *; revert Hleq; try destruct p, p0; try rewrite -> !andb_and in *;
    intuition auto using subst_eq_term;
    try solve [solve_all; intuition eauto using subst_eq_term].

  - apply Nat.eqb_eq in Hleq. subst.
    destruct Nat.leb; simpl. destruct nth_error.
    eapply eq_term_leq_term. apply eq_term_refl. simpl.
    apply Nat.eqb_refl. apply Nat.eqb_refl.
  - destruct p. discriminate.
  - solve_all. destruct y. simpl. auto using subst_eq_term.
  - assert (#|m| = #|m0|) as <-. solve_all. clear -H2. induction H2; simpl; auto.
    repeat (toProp; solve_all); auto using subst_eq_term.
  - assert (#|m| = #|m0|) as <-. solve_all. clear -H2. induction H2; simpl; auto.
    repeat (toProp; solve_all); auto using subst_eq_term.
Qed.

Lemma subst_eq_context `{checker_flags} φ l l' n k :
  eq_context φ l l' ->
  eq_context φ (subst_context n k l) (subst_context n k l').
Proof.
  induction l in l', n, k |- *; intros; destruct l'; rewrite ?subst_context_snoc;
    try (discriminate || reflexivity).
  simpl in *. rewrite -> andb_and in *.
  intuition. unfold eq_context in H2. apply forallb2_length in H2. rewrite <- H2.
  destruct a, c; try congruence.
  unfold eq_decl in *. simpl.
  destruct decl_body, decl_body0; simpl in *; try congruence.
  simpl in *. rewrite -> andb_and in *.
  intuition auto using subst_eq_term.
  intuition auto using subst_eq_term.
Qed.

Lemma subst_check_correct_arity:
  forall (cf : checker_flags) (Σ : global_context) (ind : inductive) (u : universe_instance)
         (npar : nat) (args : list term) (idecl : one_inductive_body)
         (indctx pctx : list context_decl) s k,
    check_correct_arity (snd Σ) idecl ind u indctx (firstn npar args) pctx ->
    check_correct_arity
      (snd Σ) idecl ind u (subst_context s k indctx) (firstn npar (map (subst s k) args))
      (subst_context s k pctx).
Proof.
  intros cf Σ ind u npar args idecl indctx pctx s k.
  unfold check_correct_arity.
  destruct pctx in indctx |- *. simpl; try congruence. simpl.
  rewrite subst_context_snoc. simpl.
  unfold eq_context.
  rewrite -> !andb_and. intros.
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
  rewrite /is_true -H. f_equal. f_equal. f_equal. rewrite subst_context_length.
  rewrite -> !map_map_compose. apply map_ext.
  intros. unfold compose. now rewrite commut_lift_subst_rec. lia.
  eapply subst_eq_context in H0. eapply H0.
Qed.

(** The cumulativity relation is substitutive, yay! *)

Lemma substitution_cumul `{CF:checker_flags} Σ Γ Γ' Γ'' s M N :
  wf Σ -> wf_local Σ (Γ ,,, Γ' ,,, Γ'') -> subs Σ Γ s Γ' ->
  Σ ;;; Γ ,,, Γ' ,,, Γ'' |- M <= N ->
  Σ ;;; Γ ,,, subst_context s 0 Γ'' |- subst s #|Γ''| M <= subst s #|Γ''| N.
Proof.
  intros wfΣ wfΓ Hs. induction 1.
  constructor.
  - now apply subst_leq_term.
  - eapply substitution_red1 in r. 4:eauto. all:eauto.
    econstructor 2; eauto.
    eauto with wf.
  - eapply substitution_red1 in r. 4:eauto. all:eauto with wf.
    now econstructor 3.
Qed.

Theorem substitution `{checker_flags} Σ Γ Γ' s Δ (t : term) T :
  wf Σ -> subs Σ Γ s Γ' ->
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

  - elim (leb_spec_Set); intros Hn.
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

  - specialize (X1 Γ Γ' Δ s sub eq_refl wfsubs).
    eapply refine_type. econstructor; eauto.
    unfold subst1. rewrite -> distr_subst. simpl. reflexivity.

  - eapply refine_type. constructor; eauto.
    rewrite !map_cst_type. eapply subst_declared_constant in H0 as ->; eauto.

  - eapply refine_type. econstructor; eauto.
    eapply on_declared_inductive in isdecl as [on_mind on_ind]; auto.
    apply onArity in on_ind as [[s' Hindty] _].
    apply typecheck_closed in Hindty as [_ Hindty]; eauto. symmetry.
    move/andP/proj1: Hindty. rewrite -(closedn_subst_instance_constr _ _ u) => Hty.
    apply: (subst_closedn s #|Δ|); auto with wf.
    eapply closed_upwards. eauto. simpl; lia.

  - eapply refine_type. econstructor; eauto.
    symmetry.
    apply on_declared_constructor in isdecl as [_ onc]; auto.
    eapply on_constructor_closed in onc as clty; auto.
    unfold type_of_constructor.
    apply subst_closedn; eauto. eapply closed_upwards; eauto. lia.

  - rewrite subst_mkApps map_app map_skipn.
    specialize (X2 Γ Γ' Δ s sub eq_refl wfsubs).
    specialize (X5 Γ Γ' Δ s sub eq_refl wfsubs).
    specialize (X3 Γ Γ' Δ s sub eq_refl wfsubs).
    simpl. econstructor.
    4:{ eapply subst_types_of_case in H1.
        simpl in H1. subst pars. rewrite firstn_map. eapply H1; eauto.
        all:eauto. }
    -- eauto.
    -- eauto.
    -- eauto.
    -- revert H2. subst pars.
       apply subst_check_correct_arity.
    -- destruct idecl; simpl in *; auto.
    -- now rewrite !subst_mkApps in X5.
    -- solve_all.

  - specialize (X2 Γ Γ' Δ s sub eq_refl wfsubs).
    eapply refine_type. econstructor.
    eauto.
    rewrite subst_mkApps in X2. eauto.
    rewrite map_length; eauto.
    rewrite <- (Nat.add_0_l #|Δ|).
    erewrite distr_subst_rec. simpl.
    rewrite map_rev. subst ty.
    f_equal.
    apply on_declared_projection in isdecl as [_ isdecl]; auto.
    eapply on_projection_closed in isdecl as clty; auto.
    symmetry. apply subst_closedn; eauto.
    rewrite List.rev_length H0. eapply closed_upwards; eauto. lia.

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
        rewrite commut_lift_subst_rec. lia. now rewrite (Nat.add_comm #|Δ|).
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
        rewrite commut_lift_subst_rec. lia.
        now rewrite (Nat.add_comm #|Δ|).

  - econstructor; eauto.
    eapply substitution_cumul; eauto.
Qed.

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
  forward thm. constructor. constructor. rewrite subst_empty; auto.
  now apply (thm Ht).
Qed.
