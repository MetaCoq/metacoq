(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils Ast AstUtils Induction LiftSubst
     UnivSubst TermEquality Typing Reduction TypingWf.
From MetaCoq.Checker Require Import Generation Closed WeakeningEnv Weakening.

From Equations Require Import Equations.
Require Import ssreflect.

(** * Substitution lemmas for typing derivations. *)


Generalizable Variables Σ Γ t T.

Derive Signature for Ast.wf.

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

Inductive context_subst : context -> list term -> list term -> Type :=
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

Hint Rewrite subst_context_length : subst.
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


Lemma subst_decl_closed n k d : wf_decl d -> closed_decl k d -> subst_decl n k d = d.
Proof.
  case: d => na [body|] ty; rewrite /closed_decl /subst_decl /map_decl /wf_decl /= => [[wfb wfty]].
  move/andb_and => [cb cty]. rewrite !subst_closedn //.
  move=> cty; now rewrite !subst_closedn //.
Qed.

Lemma closed_ctx_subst n k ctx : All wf_decl ctx -> closed_ctx ctx = true -> subst_context n k ctx = ctx.
Proof.
  induction ctx in n, k |- *; auto.
  unfold closed_ctx, id. intros wfctx. inv wfctx.
  rewrite mapi_app forallb_app List.rev_length /= Nat.add_0_r.
  move/andb_and => /= [Hctx /andb_and [Ha _]].
  rewrite subst_context_snoc /snoc /= IHctx // /map_decl subst_decl_closed //.
  now apply: closed_decl_upwards.
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
  move=> [= <- <-] /=. 
  f_equal. f_equal.
  erewrite (distr_subst_rec _ _ _ wfn k 0).
  rewrite fix_subst_length. simpl. f_equal.
  unfold fix_subst. rewrite !map_length.
  generalize #|mfix| at 2 3. induction n0; auto. simpl.
  f_equal. apply IHn0.
Qed.
Hint Resolve subst_unfold_fix : core.

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
Hint Resolve subst_unfold_cofix : core.

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
Hint Resolve subst_is_constructor : core.
Hint Constructors All_local_env : core.

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

(* TODO MOVE *)
Lemma wf_Forall_decls_typing_wf `{checker_flags} :
  forall Σ,
    wf Σ ->
    Forall_decls_typing (fun (_ : global_env_ext) (_ : context) (t T : term) =>
      Ast.wf t /\ Ast.wf T
    ) Σ.
Proof.
  intros Σ h.
  apply typing_wf_sigma in h as ?.
  eapply on_global_env_impl. 2: eassumption.
  intros Σ' Γ t [T|] h1 h2. all: cbn in *.
  - hnf in h2. assumption.
  - hnf in h2. exists fresh_universe. intuition eauto.
    constructor.
Qed.

Lemma subst_declared_constant `{H:checker_flags} Σ cst decl n k u :
  wf Σ ->
  declared_constant Σ cst decl ->
  map_constant_body (subst n k) (map_constant_body (subst_instance_constr u) decl) =
  map_constant_body (subst_instance_constr u) decl.
Proof.
  intros wΣ h.
  apply declared_constant_wf in h as w.
  2: eapply wf_Forall_decls_typing_wf. 2: assumption.
  destruct w as [wty wbo].
  eapply declared_decl_closed in h ; eauto.
  unfold map_constant_body.
  do 2 red in h. destruct decl as [ty [body|] univs]. all: simpl in *.
  - rewrite -> andb_and in h. destruct h as [h1 h2].
    rewrite <- (closedn_subst_instance_constr 0 body u) in h1.
    rewrite <- (closedn_subst_instance_constr 0 ty u) in h2.
    f_equal.
    + apply subst_closedn.
      * apply wf_subst_instance_constr. assumption.
      * eauto using closed_upwards with arith wf.
    + f_equal. apply subst_closedn.
      * apply wf_subst_instance_constr. assumption.
      * eauto using closed_upwards with arith wf.
  - red in h. f_equal.
    simpl in *.
    rewrite <- (closedn_subst_instance_constr 0 ty u) in h.
    rewrite andb_true_r in h.
    eapply subst_closedn.
    + apply wf_subst_instance_constr. assumption.
    + eauto using closed_upwards with arith wf.
Qed.

Definition subst_mutual_inductive_body n k m :=
  map_mutual_inductive_body (fun k' => subst n (k' + k)) m.

(* Damnit we also need Ast.wf arguments in Template-coq... to use closedness *)  
Lemma subst_declared_minductive {cf:checker_flags} Σ cst decl n k :
  wf Σ ->
  declared_minductive Σ cst decl ->
  subst_mutual_inductive_body n k decl = decl.
Proof.
  intros wfΣ Hdecl.
  pose proof (on_declared_minductive wfΣ Hdecl). apply onNpars in X.
  unshelve epose proof (declared_inductive_closed (Σ:=(empty_ext Σ)) _ Hdecl). auto.
  unshelve epose proof (declared_minductive_wf (Σ:=(empty_ext Σ)) _ Hdecl) as [wfpars wfbodies]. auto.
  move: H.
  rewrite /closed_inductive_decl /lift_mutual_inductive_body.
  destruct decl; simpl in *.
  move/andb_and => [clpar clbodies]. f_equal.
  rewrite [fold_context _ _]closed_ctx_subst; try easy. 
  eapply Forall_All; eauto.
  eapply forallb_All in clbodies. apply Forall_All in wfbodies.
  eapply (All_mix wfbodies) in clbodies. clear wfbodies.
  eapply Alli_mapi_id.
  eapply (All_Alli clbodies). intros i oib [wfb clb]; eauto.
  2:{ intros. eapply X0. }
  simpl.
  move: clb. rewrite /closed_inductive_body.
  destruct oib; simpl. move=> /andb_and[/andb_and [ci ct] cp].
  destruct wfb; simpl in *.
  f_equal. rewrite subst_closedn; eauto.
  eapply closed_upwards; eauto; lia.
  eapply All_map_id. eapply forallb_All in ct.
  eapply Forall_All in wf_ind_ctors.
  eapply (All_mix wf_ind_ctors) in ct.
  eapply (All_impl ct). intros x [wf cl].
  destruct x as [[id ty] arg]; unfold on_pi2; simpl; repeat f_equal.
  apply subst_closedn. apply wf. unfold cdecl_type in cl; simpl in cl.
  eapply closed_upwards; eauto; lia.
  simpl in X. rewrite -X in cp.
  eapply forallb_All in cp.
  eapply Forall_All in wf_ind_projs. apply (All_mix wf_ind_projs) in cp.
  eapply All_map_id; eauto.
  eapply (All_impl cp); firstorder auto.
  destruct x; unfold on_snd; simpl; f_equal.
  apply subst_closedn; auto. rewrite context_assumptions_fold.
  eapply closed_upwards; eauto; lia.
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
  apply All_map. eapply All_impl; eauto.
  intros. now apply wf_subst_instance_constr.
Qed.

(* TODO MOVE *)
Lemma Forall_impl' :
  forall A (P Q : A -> Prop) l,
    @Forall A (fun x => P x -> Q x) l ->
    Forall P l ->
    Forall Q l.
Proof.
  intros A P Q l h1 h2.
  induction h2 in h1 |- *.
  - constructor.
  - inversion h1. subst. constructor.
    + eauto.
    + eauto.
Qed.

Lemma subst_declared_projection {cf:checker_flags} Σ c mdecl idecl pdecl n k :
  wf Σ ->
  declared_projection Σ mdecl idecl c pdecl ->
  on_snd (subst n (S (ind_npars mdecl + k))) pdecl = pdecl.
Proof.
  intros wfΣ Hd.
  eapply declared_projection_wf in Hd as w.
  2: eapply wf_Forall_decls_typing_wf. 2: assumption.
  eapply (declared_projection_closed (Σ:=empty_ext Σ)) in Hd. 2:auto.
  destruct pdecl; unfold on_snd; simpl; f_equal. apply subst_closedn; auto.
  eapply closed_upwards; eauto. lia.
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

Lemma closed_tele_subst n k ctx :
  All wf_decl ctx -> closed_ctx ctx ->
  mapi (fun (k' : nat) (decl : context_decl) => subst_decl n (k' + k) decl) (List.rev ctx) = List.rev ctx.
Proof.
  rewrite /closedn_ctx /mapi. simpl. generalize 0.
  induction ctx using rev_ind; try easy.
  move=> n0.
  rewrite /closedn_ctx !rev_app_distr /id /=.
  intro Hwf. move /andb_and => [closedx Hctx].
  apply All_app in Hwf as [? X]; inv X.
  rewrite subst_decl_closed //.
  rewrite (closed_decl_upwards n0) //; lia.
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

Lemma on_constructor_closed_wf `{checker_flags} {Σ mind mdecl u idecl indices cdecl cs} :
  wf Σ ->
  on_constructor (lift_typing typing) (Σ, ind_universes mdecl) mdecl (inductive_ind mind) idecl indices cdecl cs ->
  let cty := subst0 (inds (inductive_mind mind) u (ind_bodies mdecl))
                    (subst_instance_constr u (snd (fst cdecl)))
  in closed cty /\ Ast.wf cty.
Proof.
  intros wfΣ [cs' ? Hparams [s Hs]].
  pose proof (typing_wf_local Hs).
  apply typing_wf in Hs as w. 2: assumption.
  destruct w as [w _].
  destruct cdecl as [[id cty] car].
  eapply (env_prop_typing _ typecheck_closed) in Hs; eauto.
  rewrite arities_context_length in Hs.
  rewrite -> andb_and in *. simpl in *.
  destruct Hs as [Hs _]. split.
  - eapply (closedn_subst _ 0 0).
    + clear. unfold inds.
      induction #|ind_bodies mdecl|; simpl; try constructor; auto.
    + simpl. now rewrite -> inds_length, closedn_subst_instance_constr.
  - apply wf_subst.
    + auto with wf.
    + apply wf_subst_instance_constr. assumption.
Qed.
(*
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
*)
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
    rewrite to_extended_list_k_cons /= !map_app; unf_term.
    f_equal.
    rewrite (lift_to_extended_list_k _ _ 1) map_map_compose.
    pose proof (to_extended_list_k_spec Γ k); unf_term.
    solve_all. destruct H2 as [n [-> Hn]].
    rewrite /lift (subst_app_decomp [a] s k); auto with wf.
    rewrite subst_rel_gt. simpl; lia.
    repeat (f_equal; simpl; try lia).
    cbn -[subst]. f_equal. apply (subst_rel_eq _ _ 0 a); cbnr; lia.
  - inv wfs.
    rewrite -IHcontext_subst // to_extended_list_k_cons /=.
    rewrite (lift_to_extended_list_k _ _ 1) map_map_compose.
    pose proof (to_extended_list_k_spec Γ k).
    solve_all. destruct H2 as [n [-> Hn]].
    rewrite /lift (subst_app_decomp [subst0 s b] s k); auto with wf.
    rewrite subst_rel_gt. simpl; lia.
    repeat (unf_term; f_equal; simpl; try lia).
Qed.

Lemma wf_context_subst ctx args s :
  All wf_decl ctx -> All Ast.wf args ->
  context_subst ctx args s -> All Ast.wf s.
Proof.
  move=> wfctx wfargs.
  induction 1. constructor.
  eapply All_app in wfargs as [wfargs wfa]. inv wfa. inv wfctx.
  constructor; intuition auto.
  inv wfctx. red in H. constructor; solve_all. apply wf_subst. solve_all. intuition auto with wf.
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

(* TODO Duplicate of PCUICSubstitution *)
Lemma Alli_map_option_out_mapi_Some_spec' {A B} (f g : nat -> A -> option B) h l t P :
  All P l ->
  (forall i x t, P x -> f i x = Some t -> g i x = Some (h t)) ->
  map_option_out (mapi f l) = Some t ->
  map_option_out (mapi g l) = Some (map h t).
Proof.
  unfold mapi. generalize 0.
  move => n Ha Hfg. move: t.
  induction Ha in n |- *; try constructor; auto.
  destruct t; cbnr; discriminate.
  move=> t /=. case E: (f n x) => [b|]; try congruence.
  rewrite (Hfg n _ _ p E).
  case E' : map_option_out => [b'|]; try congruence.
  move=> [= <-]. now rewrite (IHHa _ _ E').
Qed.

Lemma on_constructor_closed {cf:checker_flags}  {Σ mind mdecl u idecl indices cdecl cs} :
  wf Σ ->
  on_constructor (lift_typing typing) (Σ, ind_universes mdecl) mdecl (inductive_ind mind) idecl indices cdecl cs ->
  let cty := subst0 (inds (inductive_mind mind) u (ind_bodies mdecl))
                    (subst_instance_constr u (snd (fst cdecl)))
  in closed cty.
Proof.
  intros wfΣ [cs' ? Hparams [s Hs] _].
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

(* TODO Duplicate of PCUICSubstitution? *)
Lemma map_subst_instance_constr_to_extended_list_k u ctx k :
  to_extended_list_k (subst_instance_context u ctx) k
  = to_extended_list_k ctx k.
Proof.
  unfold to_extended_list_k.
  cut (map (subst_instance_constr u) [] = []); [|reflexivity].
  generalize (@nil term); intros l Hl.
  induction ctx in k, l, Hl |- *; cbnr.
  destruct a as [? [] ?]; cbnr; eauto. apply IHctx.
  simpl. now rewrite Hl.
Qed.

Lemma subst_instance_context_assumptions u ctx :
  context_assumptions (subst_instance_context u ctx)
  = context_assumptions ctx.
Proof.
  induction ctx; cbnr.
  destruct (decl_body a); cbn; now rewrite IHctx.
Qed.


Lemma subst_build_case_predicate_type ind mdecl idecl u params ps pty n k :
  closed_ctx (subst_instance_context u (ind_params mdecl)) ->
  closed (ind_type idecl) ->
  build_case_predicate_type ind mdecl idecl params u ps = Some pty ->
  build_case_predicate_type ind mdecl
    (map_one_inductive_body (context_assumptions mdecl.(ind_params))
            (length (arities_context (ind_bodies mdecl))) (fun k' => subst n (k' + k))
            (inductive_ind ind) idecl)
    (map (subst n k) params) u ps
  = Some (subst n k pty).
Proof.
(*   intros closedparams closedtype. *)
(*   unfold build_case_predicate_type; simpl. *)
(*   case_eq (instantiate_params (subst_instance_context u (ind_params mdecl)) params *)
(*                               (subst_instance_constr u (ind_type idecl))); *)
(*     [|discriminate ]. *)
(*   intros ipars Hipars. *)
(*   apply (subst_instantiate_params n k) in Hipars; tas. *)
(*   rewrite ind_type_map. simpl. *)
(*   rewrite subst_closedn in Hipars. *)
(*   { rewrite closedn_subst_instance_constr; eapply closed_upwards; tea; lia. } *)
(*   rewrite subst_closedn; [eapply closed_upwards; tea; lia|]. *)
(*   rewrite Hipars. *)
(*   specialize (subst_destArity [] ipars n k); *)
(*     destruct (destArity [] ipars) as [[ctx s]|]; [|discriminate]. *)
(*   simpl. cbn. move => -> /some_inj-HH. simpl. f_equal. *)
(*   etransitivity. *)
(*   2: exact (f_equal (subst n k) HH). *)
(*   rewrite subst_it_mkProd_or_LetIn. simpl. f_equal. f_equal. *)
(*   { destruct idecl; reflexivity. } *)
(*   rewrite subst_mkApps; simpl. f_equal. *)
(*   rewrite map_app; f_equal. *)
(*   - rewrite !map_map; apply map_ext; clear; intro. *)
(*     rewrite subst_context_length. *)
(*     rewrite commut_lift_subst_rec. lia. *)
(*     f_equal. lia. *)
(*   - rewrite /to_extended_list to_extended_list_k_subst. *)
(*     rewrite <- to_extended_list_k_map_subst. reflexivity. lia. *)
(* Qed. *)
Admitted.

Lemma subst_build_branches_type {cf:checker_flags}
      n k Σ ind mdecl idecl indices args u p brs cs :
  wf Σ ->
  All Ast.wf args ->
  Ast.wf (ind_type idecl) ->
  All Ast.wf n ->
  declared_inductive Σ mdecl ind idecl ->
  closed_ctx (subst_instance_context u (ind_params mdecl)) ->
  on_inductive (lift_typing typing) (Σ, ind_universes mdecl)
               (inductive_mind ind) mdecl ->
  on_constructors (lift_typing typing) (Σ, ind_universes mdecl)
                  mdecl (inductive_ind ind) idecl indices (ind_ctors idecl) cs ->
  map_option_out (build_branches_type ind mdecl idecl args u p) = Some brs ->
  map_option_out (build_branches_type ind mdecl
         idecl (map (subst n k) args) u (subst n k p)) =
         Some (map (on_snd (subst n k)) brs).
Proof.
  intros wfΣ wargs widecl wn wfidecl closedparams onmind Honcs.
  assert (wc : Forall wf_decl (subst_instance_context u (ind_params mdecl))).
  { assert (h : Forall wf_decl (ind_params mdecl)).
    { eapply typing_all_wf_decl ; revgoals.
      - apply onParams in onmind.
        unfold on_context in onmind.
        change TemplateEnvironment.ind_params with ind_params in onmind.
        eassumption.
      - simpl. assumption.
    }
    clear - h. induction h. 1: constructor.
    simpl. constructor. 2: assumption.
    destruct x as [na [bo|] ty].
    all: unfold map_decl. all: unfold wf_decl in *. all: simpl in *.
    all: intuition eauto with wf.
  }
  rewrite !build_branches_type_. cbn.
  eapply Alli_map_option_out_mapi_Some_spec'.
  eapply All2_All_left; tea. intros x y u'; exact (y; u').
  clear Honcs brs.
  intros j [[id t] i] [t' k'] [cs' Honc].
  case_eq (instantiate_params (subst_instance_context u (ind_params mdecl)) args
                              (subst0 (inds (inductive_mind ind) u
                                            (ind_bodies mdecl))
                                      (subst_instance_constr u t)));
    [|discriminate].
  intros ty Heq; cbn.
  pose proof (on_constructor_closed_wf wfΣ (u:=u) Honc) as [clt wt].
  cbn in clt. cbn in wt.
  eapply (closed_upwards k) in clt; try lia.
  remember (subst0 (inds (inductive_mind ind) u (ind_bodies mdecl))
                   (subst_instance_constr u t)) as ty'.
  apply (subst_instantiate_params n k) in Heq as Heq'.
  all: auto using Forall_All with wf.
  erewrite subst_closedn in Heq'; tas.
  rewrite Heq'.
  eapply instantiate_params_make_context_subst in Heq.
  destruct Heq as [ctx' [ty'' [s' [Hty [Hsubst Ht0]]]]].
  subst ty; simpl.
  rewrite Heqty' in Hty.
  destruct Honc as [Hcshape_args ? cshape_eq Hty' _ _]; unfold cdecl_type in *; simpl in *.
  rewrite cshape_eq in Hty.
  rewrite -> !subst_instance_constr_it_mkProd_or_LetIn in Hty.
  rewrite !subst_it_mkProd_or_LetIn in Hty.
  assert (H0: #|subst_context (inds (inductive_mind ind) u (ind_bodies mdecl)) 0
                (subst_instance_context u (ind_params mdecl))|
          = #|subst_instance_context u (ind_params mdecl)|).
  { now rewrite subst_context_length. }
  rewrite <- H0 in Hty.
  rewrite decompose_prod_n_assum_it_mkProd in Hty.
  injection Hty. clear Hty.
  intros Heqty'' <-. revert Heqty''.
  rewrite !subst_instance_context_length Nat.add_0_r.
  rewrite subst_context_length subst_instance_context_length.
  rewrite (subst_cstr_concl_head ind u mdecl cs'.(cshape_args) cs'.(cshape_indices)).
  - destruct wfidecl as [Hmdecl Hnth].
    now apply nth_error_Some_length in Hnth.
  - intros <-. rewrite !subst_it_mkProd_or_LetIn !subst_mkApps /=.
    rewrite !decompose_prod_assum_it_mkProd /=;
          try by rewrite is_ind_app_head_mkApps.
    rewrite !decompose_app_mkApps; try by reflexivity.
    simpl. rewrite !map_app !subst_context_length
                  !subst_instance_context_length Nat.add_0_r.
    eapply subst_to_extended_list_k with (k:=#|cs'.(cshape_args)|) in Hsubst as XX.
    2:{ eapply wf_make_context_subst. 3: eassumption.
        all: auto using Forall_All with wf.
    }
    rewrite map_subst_instance_constr_to_extended_list_k in XX.
    rewrite !XX; clear XX.
    apply make_context_subst_spec in Hsubst as Hsubst'.
    rewrite rev_involutive in Hsubst'.
    pose proof (context_subst_assumptions_length _ _ _ Hsubst') as H1.
    case E: chop => [l l'].
    have chopm := (chop_map _ _ _ _ _ E).
    move: E chopm.
    rewrite chop_n_app ?map_length.
    { rewrite <- H1. apply onNpars in onmind.
      now rewrite subst_instance_context_assumptions.
    }
    move=> [= <- <-] chopm.
    move: {chopm}(chopm _ (subst n (#|cs'.(cshape_args)| + k))).
    rewrite map_app.
    move=> chopm; rewrite {}chopm /=.
    inversion 1; subst. f_equal. unfold on_snd; cbn; f_equal.
    rewrite !app_nil_r /on_snd /=.
    rewrite subst_it_mkProd_or_LetIn !subst_context_length !subst_mkApps
            !subst_instance_context_length !map_app.
    f_equal. f_equal.
    -- rewrite -> commut_lift_subst_rec. arith_congr. lia.
    -- f_equal. simpl. f_equal.
      rewrite !subst_mkApps /= !map_app. f_equal.
      f_equal.
      rewrite /to_extended_list -to_extended_list_k_map_subst.
      rewrite !subst_context_length subst_instance_context_length. lia.
      now rewrite to_extended_list_k_subst.
Qed.
(*
Lemma strip_casts_subst s k t : 
  Ast.wf t ->
  strip_casts (subst s k t) = subst (map strip_casts s) k (strip_casts t).
Proof.
  intros wf; revert s k.
  induction wf using term_wf_forall_list_ind; simpl; intros; auto; 
    rewrite ?map_map_compose  ?compose_on_snd ?compose_map_def ?map_length;
   f_equal; solve_all; eauto.
  - admit.
  - rewrite subst_mkApps.
    rewrite strip_casts_mkApps_wf; auto with wf. admit. admit.
    rewrite IHwf. f_equal. rewrite !map_map_compose. solve_all.


    pose proof (strip_casts_decompose_app (mkApps (subst s k t0) (map (subst s k) l))).
    forward H1. auto with wf. admit.
    destruct decompose_app eqn:eq.
    specialize (H1 _ _ Logic.eq_refl).
    rewrite map_map_compose.
    rewrite -IHwf H1. 
    pose proof (strip_casts_decompose_app (mkApps (strip_casts t0) (map strip_casts l))).
    forward H3. auto with wf. admit.
    destruct (decompose_app (mkApps (strip_casts t0) _)) eqn:eq'.
    specialize (H3 _ _ Logic.eq_refl).
    
 

    rewrite (strip_casts_mkApps_tApp t0) //.
    simpl. rewrite subst_mkApps -IHwf.
    rewrite map_map_compose.

  
  rewrite IHwf. strip_casts_mkApps. map_map_compose.  
    f_equal; solve_all.
Qed. *)

Lemma decompose_prod_assum_mkApps_nonnil ctx f a l : 
  decompose_prod_assum ctx (mkApps f (a :: l)) = (ctx, mkApps f (a :: l)).
Proof.
  induction f; simpl; auto.
Qed.


Hint Unfold subst1 : subst.
Hint Rewrite subst_mkApps distr_subst: subst.

Lemma subst_decompose_prod_assum_rec ctx t s k :
  let (ctx', t') := decompose_prod_assum ctx t in
  ∑ ctx'' t'',
    (decompose_prod_assum [] (subst s (#|ctx'| + k) t') = (ctx'', t'')) *
  (decompose_prod_assum (subst_context s k ctx) (subst s (length ctx + k) t) =
  (subst_context s k ctx' ,,, ctx'', t'')).
Proof.
  induction t in ctx, k |- *; simpl; try solve [ eexists _, _; firstorder eauto ].
  - elim: leb_spec_Set => comp.
    + destruct (nth_error s (n - (#|ctx| + k))) eqn:Heq.
      * destruct decompose_prod_assum eqn:Heq'.
        eexists _, _; intuition eauto.
        now rewrite decompose_prod_assum_ctx Heq'.
      * eexists _,_; firstorder eauto.
    + eexists _,_; firstorder eauto.
  - destruct decompose_prod_assum eqn:Heq.
    rewrite decompose_prod_assum_ctx in Heq.
    destruct (decompose_prod_assum [] t1) eqn:Heq'.
    noconf Heq.
    specialize (IHt1 ctx k).
    rewrite decompose_prod_assum_ctx in IHt1.
    rewrite Heq' in IHt1.
    destruct IHt1 as [ctx'' [t'' [eqt eqt1]]].
    exists ctx'', t''. rewrite -eqt.
    split.
    * unfold snoc; simpl. rewrite !app_context_length.
      simpl. lia_f_equal.
    * rewrite decompose_prod_assum_ctx in eqt1.
      rewrite decompose_prod_assum_ctx.
      destruct (decompose_prod_assum   [] (subst s _ t1)) eqn:Heq''.
      rewrite subst_context_app in eqt1.
      rewrite !subst_context_app.
      injection eqt1. intros <-.
      intros eqctx. f_equal.
      unfold app_context in eqctx.
      rewrite app_assoc in eqctx.
      apply app_inv_tail in eqctx.
      subst c. rewrite app_context_assoc.
      unfold snoc. simpl. lia_f_equal.
  - destruct decompose_prod_assum eqn:Heq.
    rewrite decompose_prod_assum_ctx in Heq.
    destruct (decompose_prod_assum [] t2) eqn:Heq'.
    noconf Heq.
    specialize (IHt2 ctx (S k)).
    rewrite decompose_prod_assum_ctx in IHt2.
    rewrite Heq' in IHt2.
    destruct IHt2 as [ctx'' [t'' [eqt eqt2]]].
    exists ctx'', t''. rewrite -eqt.
    split.
    * unfold snoc; simpl. rewrite !app_context_length.
      simpl. lia_f_equal.
    * rewrite decompose_prod_assum_ctx in eqt2.
      rewrite decompose_prod_assum_ctx.
      rewrite Nat.add_succ_r in eqt2.
      destruct (decompose_prod_assum   []  (subst s _ t2)) eqn:Heq''.
      rewrite subst_context_app in eqt2.
      rewrite !subst_context_app subst_context_snoc.
      injection eqt2. intros <-.
      intros eqctx. f_equal.
      unfold app_context in eqctx.
      rewrite app_assoc in eqctx.
      apply app_inv_tail in eqctx.
      subst c. rewrite app_context_assoc.
      unfold snoc. simpl. lia_f_equal.  

  - destruct decompose_prod_assum eqn:Heq.
    rewrite decompose_prod_assum_ctx in Heq.
    destruct (decompose_prod_assum [] t3) eqn:Heq'.
    noconf Heq.
    specialize (IHt3 ctx (S k)).
    rewrite decompose_prod_assum_ctx in IHt3.
    rewrite Heq' in IHt3.
    destruct IHt3 as [ctx'' [t'' [eqt eqt3]]].
    exists ctx'', t''. rewrite -eqt.
    split.
    * unfold snoc; simpl. rewrite !app_context_length.
      simpl. lia_f_equal.
    * rewrite decompose_prod_assum_ctx in eqt3.
      rewrite decompose_prod_assum_ctx.
      rewrite Nat.add_succ_r in eqt3.
      destruct (decompose_prod_assum   []  (subst s _ t3)) eqn:Heq''.
      rewrite subst_context_app in eqt3.
      rewrite !subst_context_app subst_context_snoc.
      injection eqt3. intros <-.
      intros eqctx. f_equal.
      unfold app_context in eqctx.
      rewrite app_assoc in eqctx.
      apply app_inv_tail in eqctx.
      subst c. rewrite app_context_assoc.
      unfold snoc. simpl. lia_f_equal.

  - destruct args.
    * simpl. specialize (IHt ctx k). destruct decompose_prod_assum eqn:da.
      destruct IHt as [ctx' [t' [dec dec']]].
      rewrite decompose_prod_assum_ctx in dec'.
      destruct (decompose_prod_assum [] (subst _ _ t)) eqn:da'.
      noconf dec'. eexists _, _; split => //.
      now rewrite decompose_prod_assum_ctx da'.
    * specialize (IHt ctx k). destruct decompose_prod_assum eqn:da.
      destruct IHt as [ctx' [t' [dec dec']]].
      rewrite decompose_prod_assum_ctx in dec'.
      destruct (decompose_prod_assum [] (subst _ _ t)) eqn:da'.
      noconf dec'.
      cbn [map]. rewrite decompose_prod_assum_mkApps_nonnil.
      eexists _, _; split => //.
      rewrite decompose_prod_assum_ctx.
      now rewrite decompose_prod_assum_mkApps_nonnil.
Qed.

Lemma map_option_out_impl {A B} (l : list A) (f g : A -> option B) x :
  (forall x y, f x = Some y -> g x = Some y) ->
  map_option_out (map f l) = Some x ->
  map_option_out (map g l) = Some x.
Proof.
  intros Hfg.
  induction l in x |- *; simpl; auto.
  destruct (f a) eqn:fa.
  - rewrite (Hfg _ _ fa).
    move: IHl; destruct map_option_out.
    * move=> H'. specialize (H' _ eq_refl).
      rewrite H'. congruence.
    * discriminate.
  - discriminate.
Qed.

Lemma smash_context_app Δ Γ Γ' :
  smash_context Δ (Γ ++ Γ') = smash_context (smash_context Δ Γ) Γ'.
Proof.
  revert Δ; induction Γ as [|[na [b|] ty]]; intros Δ; simpl; auto.
Qed.


Lemma strip_casts_decompose_app t : 
  Ast.wf t ->
  forall f l, decompose_app t = (f, l) ->
  strip_casts t = mkApps (strip_casts f) (map strip_casts l).
Proof.
  intros wf.
  induction wf using term_wf_forall_list_ind; simpl; intros; auto; noconf H;
  try noconf H0;
    rewrite ?map_map_compose  ?compose_on_snd ?compose_map_def ?map_length;
      f_equal; solve_all; eauto.

  - now noconf H3.
  - now noconf H3.
Qed.

Lemma substitution_check_one_fix s k mfix inds :
  map_option_out (map check_one_fix mfix) = Some inds ->
  map_option_out (map (fun x : def term =>
    check_one_fix (map_def (subst s k) (subst s (#|mfix| + k)) x)) mfix) = Some inds.
Proof.
  apply map_option_out_impl.
  move=> [na ty def rarg] /=.
  rewrite decompose_prod_assum_ctx.
  destruct (decompose_prod_assum _ (strip_casts ty)) eqn:decomp.
  rewrite decompose_prod_assum_ctx in decomp.
  destruct (decompose_prod_assum [] ty) eqn:decty.
  noconf decomp. rewrite !app_context_nil_l.
  pose proof (subst_decompose_prod_assum_rec [] ty s k).
  rewrite decty in X.
  destruct X as [ctx'' [t'' [dect decty']]].
  rewrite -> subst_context_nil in decty'. simpl in decty'.
Admitted.
  (*rewrite decty'. intros ind.
  rewrite smash_context_app.
   rewrite (smash_context_acc _ (smash_context _ _)).
  rewrite List.rev_app_distr.
  destruct (nth_error_spec (List.rev (smash_context [] c0)) rarg) => /= //;
  autorewrite with len in l; simpl in *.
  rewrite nth_error_app_lt; autorewrite with len; simpl; try lia.
  rewrite (smash_context_subst []) /=.
  rewrite nth_error_rev_inv; autorewrite with len; simpl; try lia.
  rewrite nth_error_subst_context /=.
  autorewrite with len.
  rewrite nth_error_rev_inv in e; autorewrite with len; auto.
  autorewrite with len in e. simpl in e. rewrite e.
  simpl.
  destruct (decompose_app (decl_type x)) eqn:Happ.
  destruct t0; try discriminate. simpl in *.
  erewrite decompose_app_subst; eauto. simpl. auto.
Qed. *)

Lemma decompose_prod_assum_mkApps ctx ind u args :
  decompose_prod_assum ctx (mkApps (tInd ind u) args) = (ctx, mkApps (tInd ind u) args).
Proof.
  apply (decompose_prod_assum_it_mkProd ctx []).
  now rewrite is_ind_app_head_mkApps.
Qed.


Lemma substitution_check_one_cofix s k mfix inds :
  map_option_out (map check_one_cofix mfix) = Some inds ->
  map_option_out (map (fun x : def term =>
     check_one_cofix (map_def (subst s k) (subst s (#|mfix| + k)) x)) mfix) = Some inds.
Proof.
  apply map_option_out_impl. move=> [na ty def rarg] /= ind.
  destruct (decompose_prod_assum [] ty) eqn:decty.
  destruct (decompose_app t) eqn:eqapp.
  destruct t0; try discriminate. simpl.
  pose proof (subst_decompose_prod_assum_rec [] ty s k).
  rewrite decty in X.
  destruct X as [ctx'' [t'' [dect decty']]].
Admitted.
  (* apply decompose_app_mkApps in eqapp. => //.
  subst t.
  rewrite subst_mkApps /= in dect.
  rewrite decompose_prod_assum_mkApps in dect. noconf dect.
  rewrite decompose_app_mkApps //.
Qed. *)


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

Lemma wf_fix :
  forall (mfix : list (def term)) (k : nat), Ast.wf (tFix mfix k) ->
    Forall
      (fun def : def term => Ast.wf (dtype def) /\ Ast.wf (dbody def))
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

Local Set Keyed Unification.

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
  (* - autorewrite with subst. rewrite distr_subst; auto.
    eapply red_beta.

  - autorewrite with subst. rewrite distr_subst; auto.
    eapply red_zeta. *)

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
    inv wfM. auto with wf.
    + eapply red_fix. erewrite subst_unfold_fix; eauto.
      now apply subst_is_constructor.

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
    induction X. all: simpl. all: constructor.
    + intuition auto. simpl. eapply b0. all: auto.
      inversion wfM. subst. inversion H5. subst. auto.
    + eapply IHX. inversion wfM. subst.
      constructor. all: auto.
      inversion H5. subst. assumption.

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
    clear -X H0 X1 wfΓ Hs.
    induction X; constructor; auto.
    intuition.
    eapply b; eauto. now inv X1.
    apply IHX. now inv X1.

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
    induction X. all: simpl. all: constructor. all: simpl.
    + intuition eauto.
      * eapply b0. all: eauto.
        inv wfM. inv H. intuition eauto.
      * inversion b. auto.
    + eapply IHX. constructor.
      apply wf_fix in wfM. inv wfM. assumption.

  - apply wf_fix in wfM.
    apply fix_red_body. rewrite !subst_fix_context.
    solve_all. apply (OnOne2_All_mix_left wfM) in X. (* clear wfM. *)
    rewrite <- (OnOne2_length X).
    eapply OnOne2_map. unfold on_Trel. solve_all.
    + specialize (X Γ0 Γ' (Γ'' ,,, fix_context mfix0)).
      rewrite app_context_assoc in X. specialize (X eq_refl).
      rewrite -> app_context_length, fix_context_length in *.
      rewrite -> subst_context_app in *.
      rewrite -> app_context_assoc, Nat.add_0_r in *.
      auto.
    + inversion b0. auto.

  - constructor.
    rewrite -> (OnOne2_length X). generalize (#|mfix1|).
    induction X. all: simpl. all: constructor. all: simpl.
    + intuition eauto.
      * eapply b0. all: eauto.
        inv wfM. inv H. intuition eauto.
      * inversion b. auto.
    + eapply IHX. constructor.
      apply wf_cofix in wfM. inv wfM. assumption.

    - apply wf_cofix in wfM.
      apply cofix_red_body. rewrite !subst_fix_context.
      solve_all. apply (OnOne2_All_mix_left wfM) in X. (* clear wfM. *)
      rewrite <- (OnOne2_length X).
      eapply OnOne2_map. unfold on_Trel. solve_all.
      + specialize (X Γ0 Γ' (Γ'' ,,, fix_context mfix0)).
        rewrite app_context_assoc in X. specialize (X eq_refl).
        rewrite -> app_context_length, fix_context_length in *.
        rewrite -> subst_context_app in *.
        rewrite -> app_context_assoc, Nat.add_0_r in *.
        auto.
      + inversion b0. auto.
Qed.

Lemma subst_eq_term_upto_univ `{checker_flags} Σ Re Rle napp n k T U :
  RelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Rle ->
  eq_term_upto_univ_napp Σ Re Rle napp T U ->
  eq_term_upto_univ_napp Σ Re Rle napp (subst n k T) (subst n k U).
Proof.
  intros hRe hRle h.
  induction T in napp, n, k, U, h, Rle, hRle |- * using term_forall_list_rect.
  all: simpl ; inversion h ; simpl.
  all: try (eapply eq_term_upto_univ_refl ; easy).
  all: try (constructor ; easy).
  - constructor.
    eapply All2_map. eapply All2_impl' ; try eassumption.
    eapply All_impl ; try eassumption.
    cbn. intros x HH y HH'. now eapply HH.
  - subst. eapply eq_term_upto_univ_mkApps.
    rewrite map_length. eauto.
    eapply All2_map. eapply All2_impl' ; try eassumption.
    eapply All_impl ; try eassumption.
    cbn. intros x HH y HH'. now eapply HH.
  - constructor ; try easy.
    eapply All2_map.
    eapply All2_impl'. eassumption.
    eapply All_impl. easy.
    cbn. intros x HH y [? HH']. split ; [assumption | now apply HH].
  - constructor.
    eapply All2_map.
    eapply All2_impl'. eassumption.
    eapply All_impl. eassumption.
    cbn. apply All2_length in X0 as e. rewrite e.
    intros x [] y []; now split.
  - constructor.
    eapply All2_map.
    eapply All2_impl'. eassumption.
    eapply All_impl. eassumption.
    cbn. apply All2_length in X0 as e. rewrite e.
    intros x [] y []; now split.
Qed.

Lemma subst_eq_term `{checker_flags} Σ ϕ n k T U :
  eq_term Σ ϕ T U ->
  eq_term Σ ϕ (subst n k T) (subst n k U).
Proof.
  intros Hleq.
  eapply subst_eq_term_upto_univ.
  - intro. eapply eq_universe_refl.
  - intro. eapply eq_universe_refl.
  - assumption.
Qed.

Lemma subst_leq_term `{checker_flags} Σ ϕ n k T U :
  leq_term Σ ϕ T U ->
  leq_term Σ ϕ (subst n k T) (subst n k U).
Proof.
  intros Hleq.
  eapply subst_eq_term_upto_univ.
  - intro. eapply eq_universe_refl.
  - intro. eapply leq_universe_refl.
  - assumption.
Qed.


Lemma subst_eq_decl `{checker_flags} Σ ϕ l k d d' :
  eq_decl Σ ϕ d d' -> eq_decl Σ ϕ (subst_decl l k d) (subst_decl l k d').
Proof.
  destruct d, d', decl_body, decl_body0;
    unfold eq_decl, map_decl; cbn; intuition auto using subst_eq_term.
Qed.

Lemma subst_eq_context `{checker_flags} Σ φ l l' n k :
  eq_context Σ φ l l' ->
  eq_context Σ φ (subst_context n k l) (subst_context n k l').
Proof.
  induction l in l', n, k |- *; inversion 1. constructor.
  rewrite !subst_context_snoc. constructor.
  apply All2_length in X1 as e. rewrite e.
  now apply subst_eq_decl.
  now apply IHl.
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

Lemma substitution_All_local_env_over `{cf : checker_flags} {Σ Γ Γ' Δ s} :
 wf Σ.1 ->
 forall wfΓ0 : wf_local Σ (Γ ,,, Γ' ,,, Δ),
 All_local_env_over typing
      (fun (Σ : global_env_ext) (Γ : context) (_ : wf_local Σ Γ) 
         (t T : term) (_ : Σ;;; Γ |- t : T) =>
       forall (Γ0 Γ' Δ : context) (s : list term),
       subs Σ Γ0 s Γ' ->
       Γ = Γ0 ,,, Γ' ,,, Δ ->
       Σ;;; Γ0 ,,, subst_context s 0 Δ |- subst s #|Δ| t : subst s #|Δ| T) Σ
      (Γ ,,, Γ' ,,, Δ) wfΓ0 ->
  subs Σ Γ s Γ' ->
  wf_local Σ (Γ ,,, subst_context s 0 Δ).
Proof.
  intros wfΣ wfΓ.
  induction Δ; simpl; intros Hwf.
  intros _. clear Hwf. simpl in wfΓ. now eapply All_local_env_app_inv in wfΓ.
  depelim Hwf;
  rewrite subst_context_snoc; simpl; constructor.
  eapply IHΔ; eauto. red. exists (tu.π1). simpl.
  rewrite Nat.add_0_r. eapply t0; eauto.
  eapply IHΔ; eauto. red. exists (tu.π1). simpl.
  rewrite Nat.add_0_r. eapply t1; eauto.
  simpl. rewrite Nat.add_0_r. eapply t0; eauto.
Qed.

Theorem substitution `{checker_flags} Σ Γ Γ' s Δ (t : term) T :
  wf Σ.1 -> subs Σ Γ s Γ' ->
  Σ ;;; Γ ,,, Γ' ,,, Δ |- t : T ->
  Σ ;;; Γ ,,, subst_context s 0 Δ |- subst s #|Δ| t : subst s #|Δ| T.
Proof.
  intros HΣ Hs Ht.
  pose proof (typing_wf_local Ht).
  generalize_eq Γ0 (Γ ,,, Γ' ,,, Δ). 
  revert Γ Γ' Δ s Hs. revert Σ HΣ Γ0 X t T Ht.
  apply (typing_ind_env (fun Σ Γ0 t T =>
  forall (Γ Γ' Δ : context) (s : list term)
    (sub : subs Σ Γ s Γ') (eqΓ0 : Γ0 = Γ ,,, Γ' ,,, Δ),
    Σ ;;; Γ ,,, subst_context s 0 Δ |- subst s #|Δ| t : subst s #|Δ| T));
    intros Σ wfΣ Γ0 wfΓ0; intros; subst Γ0; simpl in *;
    try ((epose proof (substitution_All_local_env_over wfΣ wfΓ0 X sub))
      || (epose proof (substitution_All_local_env_over wfΣ wfΓ0 X0 sub)));
    try solve [econstructor; eauto].

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
    specialize (X1 Γ Γ' Δ s sub eq_refl).
    specialize (X3 Γ Γ' (Δ,, vass n t) s sub eq_refl).
    now rewrite subst_context_snoc0 in X3.

  - econstructor; auto. eapply X1; eauto.
    specialize (X1 Γ Γ' Δ s sub eq_refl).
    specialize (X3 Γ Γ' (Δ,, vass n t) s sub eq_refl).
    now  rewrite subst_context_snoc0 in X3.

  - specialize (X1 Γ Γ' Δ s sub eq_refl).
    specialize (X3 Γ Γ' Δ s sub eq_refl).
    specialize (X5 Γ Γ' (Δ,, vdef n b b_ty) s sub eq_refl).
    rewrite subst_context_snoc0 in X5.
    econstructor; eauto.

  - specialize (X0 Γ Γ' Δ s0 sub eq_refl).
    eapply type_mkApps; eauto.
    eapply typing_wf in X; eauto. destruct X.
    clear X0 H2 H0 H1.
    induction X1; try constructor; eauto.
    specialize (p Γ Γ' Δ s0 sub eq_refl).
    specialize (p0 Γ Γ' Δ s0 sub eq_refl).
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
    move/andb_and/proj1: Hindty. rewrite -(closedn_subst_instance_constr _ _ u) => Hty.
    apply: (subst_closedn s #|Δ|); auto with wf.
    eapply closed_upwards. eauto. simpl; lia.

  - eapply refine_type. econstructor; eauto.
    symmetry.
    destruct (on_declared_constructor wfΣ isdecl) as [? [cs [? onc]]].
    eapply on_constructor_closed_wf in onc as [clty wty]; auto.
    unfold type_of_constructor.
    apply subst_closedn. 1: eauto with wf.
    eapply closed_upwards; eauto. lia.

  - rewrite subst_mkApps map_app map_skipn.
    specialize (X2 Γ Γ' Δ s sub eq_refl).
    specialize (X4 Γ Γ' Δ s sub eq_refl).
    assert (Hclos: closed_ctx (ind_params mdecl)). {
      destruct isdecl as [Hmdecl Hidecl].
      eapply on_declared_minductive in Hmdecl; eauto.
      eapply onParams in Hmdecl.
      eapply closed_wf_local in Hmdecl; eauto. }
    assert (Hclos': closed (ind_type idecl)). {
      eapply on_declared_inductive in isdecl; eauto.
      destruct isdecl as [_ oind]. clear -oind wfΣ.
      apply onArity in oind; destruct oind as [s HH]; cbn in *.
      apply typecheck_closed in HH; eauto.
      apply snd in HH. apply andb_and in HH; apply HH. }
    simpl. econstructor. all: eauto.
    -- eapply subst_build_case_predicate_type in H1; tea.
       simpl in *. subst params. rewrite firstn_map.
       etransitivity; [|eapply H1; eauto]. f_equal.
       now erewrite subst_declared_inductive.
       now rewrite closedn_subst_instance_context.
    -- now rewrite !subst_mkApps in X4.
    -- simpl.
       destruct (on_declared_inductive wfΣ isdecl) as [oind obod].
       pose obod.(onConstructors) as onc.
       eapply (subst_build_branches_type s #|Δ|) in H4; eauto.
       subst params. rewrite firstn_map. exact H4.
       4: now rewrite closedn_subst_instance_context.
       all: eauto with wf.
       subst params. eapply All_firstn.
       eapply typing_wf in X3; auto.
       destruct X3 as [wfc wfargs].
       eapply Forall_All.
       now eapply wf_mkApps_inv in wfargs.
       now eapply subs_wf in sub.
    -- solve_all.
       destruct b0 as [s' [Hs IHs]]; eauto.

  - specialize (X2 Γ Γ' Δ s sub eq_refl).
    eapply refine_type. econstructor.
    eauto.
    rewrite subst_mkApps in X2. eauto.
    rewrite map_length; eauto.
    rewrite <- (Nat.add_0_l #|Δ|).
    pose proof (subs_wf _ _ _ _ wfΣ sub).
    erewrite distr_subst_rec. simpl.
    rewrite map_rev. subst ty.
    f_equal.
    pose proof (declared_projection_closed wfΣ isdecl).
    pose proof (declared_projection_wf _ _ _ _ _ isdecl).
    pose proof (typing_wf_gen _ wfΣ _ localenv_nil _ _ (type_Prop _)) as [X' _].
    specialize (H2 X'). clear X'.
    symmetry; apply subst_closedn; eauto. now apply wf_subst_instance_constr.
    rewrite List.rev_length H0. rewrite closedn_subst_instance_constr.
    eapply closed_upwards; eauto. lia. auto.

  - rewrite -> (map_dtype _ (subst s (#|mfix| + #|Δ|))).
    eapply type_Fix; auto.
    * eapply fix_guard_subst ; eauto.
    * now rewrite -> nth_error_map, H1.
    * eapply All_map.
      eapply (All_impl X0); simpl.
      intros x [u [Hs Hs']]; exists u.
      now specialize (Hs' _ _ _ _ sub eq_refl).
    * eapply All_map.
      eapply (All_impl X1); simpl.
      intros x [Hb IH].
      rewrite subst_fix_context.
      specialize (IH Γ Γ' (Δ ,,,  (fix_context mfix)) _ sub).
      rewrite app_context_assoc in IH. specialize (IH eq_refl).
      rewrite subst_context_app Nat.add_0_r app_context_assoc in IH.
      rewrite app_context_length fix_context_length in IH.
      rewrite subst_context_length fix_context_length.
      rewrite commut_lift_subst_rec; try lia. now rewrite (Nat.add_comm #|Δ|).
    * move: H2.
      rewrite /wf_fixpoint.
      pose proof (substitution_check_one_fix s #|Δ| mfix).
      destruct map_option_out eqn:Heq => //.
      specialize (H2 _ eq_refl).
      rewrite map_map_compose. now rewrite H2.

  - rewrite -> (map_dtype _ (subst s (#|mfix| + #|Δ|))).
    eapply type_CoFix; auto.
    * eapply cofix_guard_subst; eauto.
    * now rewrite -> nth_error_map, H1.
    * eapply All_map.
      eapply (All_impl X0); simpl.
      intros x [u [Hs Hs']]; exists u.
      now specialize (Hs' _ _ _ _ sub eq_refl).
    * eapply All_map.
      eapply (All_impl X1); simpl.
      intros x [Hb IH].
      rewrite subst_fix_context.
      specialize (IH Γ Γ' (Δ ,,,  (fix_context mfix)) _ sub).
      rewrite app_context_assoc in IH. specialize (IH eq_refl).
      rewrite subst_context_app Nat.add_0_r app_context_assoc in IH.
      rewrite app_context_length fix_context_length in IH.
      rewrite subst_context_length fix_context_length.
      rewrite commut_lift_subst_rec; try lia. now rewrite (Nat.add_comm #|Δ|).
    * move: H2.
      rewrite /wf_cofixpoint.
      pose proof (substitution_check_one_cofix s #|Δ| mfix).
      destruct map_option_out eqn:Heq => //.
      specialize (H2 _ eq_refl).
      rewrite map_map_compose. now rewrite H2.

  - econstructor; eauto.
    eapply substitution_cumul; eauto.
    now eapply typing_wf in X0.
    now eapply typing_wf in X2.
Qed.

Lemma substitution0 `{checker_flags} Σ Γ n u U (t : term) T :
  wf Σ.1 ->
  Σ ;;; Γ ,, vass n U |- t : T -> Σ ;;; Γ |- u : U ->
  Σ ;;; Γ |- t {0 := u} : T {0 := u}.
Proof.
  intros HΣ Ht Hu.
  assert (wfΓ : wf_local Σ Γ).
  apply typing_wf_local in Hu; eauto.
  pose proof (substitution Σ Γ [vass n U] [u] [] t T HΣ) as thm.
  forward thm. constructor. constructor. rewrite subst_empty; auto.
  apply typing_wf in Hu; intuition.
  now apply (thm Ht).
Qed.
