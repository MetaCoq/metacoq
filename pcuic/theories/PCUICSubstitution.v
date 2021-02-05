(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import utils config.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICEquality PCUICPosition PCUICCases PCUICSigmaCalculus
     PCUICUnivSubst PCUICContextSubst PCUICTyping PCUICWeakeningEnv PCUICClosed
     PCUICReduction PCUICContextRelation PCUICContextReduction PCUICWeakening PCUICCumulativity PCUICUnivSubstitution
     PCUICRename PCUICInst.

Require Import ssreflect.
From Equations Require Import Equations.

(** * Substitution lemmas for typing derivations. *)

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

Local Set Keyed Unification.

Set Default Goal Selector "!".

Hint Rewrite @app_context_length : wf.

Generalizable Variables Σ Γ t T.

Local Open Scope sigma_scope.
 
(** Substitution in contexts is just a particular kind of instantiation. *)

Lemma subst_context_inst_context s k Γ :
  subst_context s k Γ = inst_context (⇑^k (s ⋅n ids)) Γ. 
Proof.
  rewrite /subst_context.
  now setoid_rewrite subst_inst'; setoid_rewrite Upn_Upn.
Qed.

(** Well-typed substitution into a context with *no* let-ins *)

Inductive subs {cf:checker_flags} (Σ : global_env_ext) (Γ : context) : list term -> context -> Type :=
| emptys : subs Σ Γ [] []
| cons_ass Δ s na t T : subs Σ Γ s Δ -> Σ ;;; Γ |- t : subst0 s T -> subs Σ Γ (t :: s) (Δ ,, vass na T).

Lemma subs_length {cf:checker_flags} {Σ} {Γ s Δ} : subs Σ Γ s Δ -> #|s| = #|Δ|.
Proof.
  induction 1; simpl; auto. f_equal. auto.
Qed.

(** Well-typed substitution into a context with let-ins *)

Inductive subslet {cf:checker_flags} Σ (Γ : context) : list term -> context -> Type :=
| emptyslet : subslet Σ Γ [] []
| cons_let_ass Δ s na t T : subslet Σ Γ s Δ ->
              Σ ;;; Γ |- t : subst0 s T ->
             subslet Σ Γ (t :: s) (Δ ,, vass na T)
| cons_let_def Δ s na t T :
    subslet Σ Γ s Δ ->
    Σ ;;; Γ |- subst0 s t : subst0 s T ->
    subslet Σ Γ (subst0 s t :: s) (Δ ,, vdef na t T).

Lemma subslet_nth_error {cf:checker_flags} {Σ Γ s Δ decl n} :
  subslet Σ Γ s Δ ->
  nth_error Δ n = Some decl ->
  ∑ t, nth_error s n = Some t ×
  let ty := subst0 (skipn (S n) s) (decl_type decl) in
  Σ ;;; Γ |- t : ty ×
  match decl_body decl return Type with
  | Some t' =>
    let b := subst0 (skipn (S n) s) t' in
    (t = b)
  | None => unit
  end.
Proof.
  induction 1 in n |- *; simpl; auto; destruct n; simpl; try congruence.
  - intros [= <-]. exists t; split; auto.
    simpl. split; auto. exact tt.
  - intros. destruct decl as [na' [b|] ty]; cbn in *.
    + specialize (IHX _ H) as [t' [hnth [hty heq]]]. exists t'; intuition auto.
    + now apply IHX.
  - intros [= <-]. eexists; split; eauto.
    simpl. split; auto.
  - apply IHX.
Qed.

Lemma subslet_length {cf:checker_flags} {Σ Γ s Δ} : subslet Σ Γ s Δ -> #|s| = #|Δ|.
Proof.
  induction 1; simpl; f_equal; auto.
Qed.

Lemma subst_decl_closed n k d : closed_decl k d -> subst_decl n k d = d.
Proof.
  case: d => na [body|] ty; rewrite /subst_decl /map_decl /=.
  - move/andb_and => [cb cty]. rewrite !subst_closedn //.
  - move=> cty; now rewrite !subst_closedn //.
Qed.

Lemma closed_ctx_subst n k ctx : closed_ctx ctx = true -> subst_context n k ctx = ctx.
Proof.
  induction ctx in n, k |- *; auto.
  rewrite closedn_ctx_cons.
  move/andb_and => /= [Hctx Hd].
  rewrite subst_context_snoc /snoc /= IHctx // subst_decl_closed //.
  now apply: closed_decl_upwards.
Qed.

Lemma closed_tele_subst n k ctx :
  closed_ctx ctx ->
  mapi (fun (k' : nat) (decl : context_decl) => subst_decl n (k' + k) decl) (List.rev ctx) = List.rev ctx.
Proof.
  rewrite test_context_k_eq /mapi. simpl. generalize 0.
  induction ctx using rev_ind; try easy.
  move=> n0.
  rewrite /closedn_ctx !rev_app_distr /id /=.
  move/andb_and => [closedx Hctx].
  rewrite subst_decl_closed //.
  - rewrite (closed_decl_upwards n0) //; lia.
  - f_equal. now rewrite IHctx.
Qed.

Lemma map_vass_map_def_subst g l n k :
  (mapi (fun i (d : def term) => vass (dname d) (lift0 i (dtype d)))
        (map (map_def (subst n k) g) l)) =
  (mapi (fun i d => map_decl (subst n (i + k)) d) (mapi (fun i (d : def term) => vass (dname d) (lift0 i (dtype d))) l)).
Proof.
  rewrite mapi_mapi mapi_map. apply mapi_ext.
  intros. unfold map_decl, vass; simpl; f_equal.
  rewrite commut_lift_subst_rec. 1: lia. f_equal; lia.
Qed.

Lemma All_local_env_subst {cf:checker_flags} (P Q : context -> term -> option term -> Type) c n k :
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

Lemma subst_length {cf:checker_flags} Σ Γ s Γ' : subs Σ Γ s Γ' -> #|s| = #|Γ'|.
Proof.
  induction 1; simpl; lia.
Qed.

Lemma subs_nth_error_ge {cf:checker_flags} Σ Γ Γ' Γ'' v s :
  subs Σ Γ s Γ' ->
  #|Γ' ,,, Γ''| <= v ->
  nth_error (Γ ,,, Γ' ,,, Γ'') v =
  nth_error (Γ ,,, subst_context s 0 Γ'') (v - #|Γ'|).
Proof.
  simpl.
  intros. rewrite app_context_length in H.
  rewrite !nth_error_app_ge; autorewrite with wf; f_equal; try lia.
Qed.

Lemma nth_error_subst_context (Γ' : context) s (v : nat) k :
    nth_error (subst_context s k Γ') v =
    option_map (subst_decl s (#|Γ'| - S v + k)) (nth_error Γ' v).
Proof.
  induction Γ' in v |- *; intros.
  - simpl. unfold subst_context, fold_context_k; simpl; rewrite nth_error_nil. easy.
  - simpl. destruct v; rewrite subst_context_snoc.
    + simpl. repeat f_equal; try lia.
    + simpl. rewrite IHΓ'; simpl in *. lia_f_equal.
Qed.

Lemma subs_nth_error_lt {cf:checker_flags} Σ Γ Γ' Γ'' v s :
  subs Σ Γ s Γ' ->
  v < #|Γ''| ->
  nth_error (Γ ,,, subst_context s 0 Γ'') v =
  option_map (map_decl (subst s (#|Γ''| - S v))) (nth_error (Γ ,,, Γ' ,,, Γ'') v).
Proof.
  simpl. intros Hs Hv.
  rewrite !nth_error_app_lt; autorewrite with wf; f_equal; try lia.
  erewrite nth_error_subst_context. f_equal. unfold subst_decl. rewrite Nat.add_0_r. reflexivity.
Qed.

Lemma subslet_nth_error_lt {cf:checker_flags} Σ Γ Γ' Γ'' v s :
  subslet Σ Γ s Γ' ->
  v < #|Γ''| ->
  nth_error (Γ ,,, subst_context s 0 Γ'') v =
  option_map (map_decl (subst s (#|Γ''| - S v))) (nth_error (Γ ,,, Γ' ,,, Γ'') v).
Proof.
  simpl. intros Hs Hv.
  rewrite !nth_error_app_lt; autorewrite with wf; f_equal; try lia.
  erewrite nth_error_subst_context. f_equal. unfold subst_decl. rewrite Nat.add_0_r. reflexivity.
Qed.

Lemma expand_lets_subst_comm' Γ s k x : 
  closedn (k + #|Γ|) x ->
  expand_lets (subst_context s k Γ) x = subst s (k + context_assumptions Γ) (expand_lets Γ x).
Proof.
  unfold expand_lets, expand_lets_k; simpl; intros clx.
  len.
  rewrite !subst_extended_subst.
  rewrite distr_subst. f_equal.
  len. rewrite subst_closedn //.
  rewrite Nat.add_assoc; eapply closedn_lift.
  now rewrite Nat.add_comm.
Qed.

Lemma subst_iota_red s k pars args br :
  #|skipn pars args| = context_assumptions br.(bcontext) ->
  subst s k (iota_red pars args br) =
  iota_red pars (List.map (subst s k) args) (map_branch_k (subst s) k br).
Proof.
  intros hctx. rewrite !subst_inst. rewrite inst_iota_red //.
  f_equal; try setoid_rewrite <-subst_inst' => //.
  rewrite /map_branch_k /map_branch_shift; f_equal.
  * rewrite mapi_context_inst /shiftf. setoid_rewrite subst_inst'.
    rewrite mapi_context_fold.
    eapply fold_context_k_ext => i t. now sigma.
  * simpl. rewrite subst_inst'. now sigma. 
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
Hint Resolve subst_unfold_fix : core.

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
Hint Resolve subst_unfold_cofix : core.

Lemma decompose_app_rec_subst n k t l :
  let (f, a) := decompose_app_rec t l in
  subst n k f = f ->
  decompose_app_rec (subst n k t) (map (subst n k) l)  = (f, map (subst n k) a).
Proof.
  induction t in k, l |- *; simpl; auto; try congruence.

  - destruct Nat.leb; try reflexivity.
    destruct nth_error.
    + simpl. intros ->. simpl. reflexivity.
    + intros ->. simpl. reflexivity.
  - specialize (IHt1 k (t2 :: l)).
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
  unfold isConstruct_app in *.
  destruct (decompose_app t) eqn:Heq. eapply decompose_app_subst in Heq as ->.
  - destruct t0; try discriminate || reflexivity.
  - destruct t0; try discriminate || reflexivity.
Qed.
Hint Resolve subst_is_constructor : core.
Hint Constructors All_local_env : core.

Lemma typed_subst `{checker_flags} Σ Γ t T n k :
  wf Σ.1 -> k >= #|Γ| ->
  Σ ;;; Γ |- t : T -> subst n k T = T /\ subst n k t = t.
Proof.
  intros wfΣ Hk Hty.
  pose proof (typing_wf_local Hty).
  apply typecheck_closed in Hty; eauto.
  destruct Hty as [_ [Hcl [Ht HT]%andb_and]].
  pose proof (closed_upwards k Ht).
  simpl in *. forward H0 by lia.
  pose proof (closed_upwards k HT).
  simpl in *. forward H1 by lia.
  apply (subst_closedn n) in H0; apply (subst_closedn n) in H1; auto.
Qed.

Lemma subst_wf_local `{checker_flags} Σ Γ n k :
  wf Σ.1 ->
  wf_local Σ Γ ->
  subst_context n k Γ = Γ.
Proof.
  intros wfΣ.
  induction 1; auto; unfold subst_context, snoc; rewrite fold_context_k_snoc0;
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
  map_constant_body (subst n k) (map_constant_body (subst_instance u) decl) =
  map_constant_body (subst_instance u) decl.
Proof.
  intros.
  eapply declared_decl_closed in H0; eauto.
  unfold map_constant_body.
  do 2 red in H0. destruct decl as [ty [body|] univs]; simpl in *.
  - rewrite -> andb_and in H0. intuition.
    rewrite <- (closedn_subst_instance 0 body u) in H1.
    rewrite <- (closedn_subst_instance 0 ty u) in H2.
    f_equal.
    + apply subst_closedn; eauto using closed_upwards with arith wf.
    + f_equal. apply subst_closedn; eauto using closed_upwards with arith wf.
  - red in H0. f_equal.
    intuition. simpl in *.
    rewrite <- (closedn_subst_instance 0 ty u) in H0.
    rewrite andb_true_r in H0.
    eapply subst_closedn; eauto using closed_upwards with arith wf.
Qed.

Definition subst_mutual_inductive_body n k m :=
  map_mutual_inductive_body (fun k' => subst n (k' + k)) m.

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

(* Lemma subst_declared_minductive {cf:checker_flags} Σ cst decl n k :
  wf Σ ->
  declared_minductive Σ cst decl ->
  subst_mutual_inductive_body n k decl = decl.
Proof.
  intros wfΣ Hdecl.
  pose proof (on_declared_minductive wfΣ Hdecl). apply onNpars in X.
  apply (declared_inductive_closed (Σ:=(empty_ext Σ))) in Hdecl; auto.
  move: Hdecl.
  rewrite /closed_inductive_decl /lift_mutual_inductive_body.
  destruct decl; simpl.
  move/andb_and => [clpar clbodies]. f_equal.
  - now rewrite [fold_context_k _ _]closed_ctx_subst.
  - eapply forallb_All in clbodies.
    eapply Alli_mapi_id.
    * eapply (All_Alli clbodies). intros; eauto.
      intros. eapply H.
    * simpl; intros.
      move: H. rewrite /closed_inductive_body.
      destruct x; simpl. move=> /andb_and[/andb_and [ci ct] cp].
      f_equal.
      + rewrite subst_closedn; eauto.
        eapply closed_upwards; eauto; lia.
      + eapply All_map_id. eapply forallb_All in ct.
        eapply (All_impl ct). intros x.
        destruct x as [[id ty] arg]; unfold on_pi2; intros c; simpl; repeat f_equal.
        apply subst_closedn. unfold cstr_type in c; simpl in c.
        eapply closed_upwards; eauto; lia.
      + simpl in X. rewrite -X in cp.
        eapply forallb_All in cp. eapply All_map_id; eauto.
        eapply (All_impl cp); pcuicfo.
        destruct x; unfold on_snd; simpl; f_equal.
        apply subst_closedn. rewrite context_assumptions_fold.
        eapply closed_upwards; eauto; lia.
Qed.

Lemma subst_declared_inductive {cf:checker_flags} ind Σ mdecl idecl n k :
  wf Σ ->
  declared_inductive Σ ind mdecl idecl ->
  map_one_inductive_body (context_assumptions mdecl.(ind_params))
                         (length (arities_context mdecl.(ind_bodies)))
                         (fun k' => subst n (k' + k)) (inductive_ind ind) idecl = idecl.
Proof.
  unfold declared_inductive. intros wfΣ [Hmdecl Hidecl].
   eapply (subst_declared_minductive _ _ _ n k) in Hmdecl. 2: auto.
  unfold subst_mutual_inductive_body in Hmdecl.
  destruct mdecl. simpl in *.
  injection Hmdecl. intros Heq.
  clear Hmdecl.
  pose proof Hidecl as Hidecl'.
  rewrite <- Heq in Hidecl'.
  rewrite nth_error_mapi in Hidecl'.
  clear Heq.
  unfold option_map in Hidecl'. rewrite Hidecl in Hidecl'.
  congruence.
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

Lemma subst_declared_constructor {cf:checker_flags} Σ c u mdecl idecl cdecl n k :
  wf Σ -> declared_constructor Σ c mdecl idecl cdecl ->
  subst (map (subst_instance u) n) k (type_of_constructor mdecl cdecl c u) = (type_of_constructor mdecl cdecl c u).
Proof.
  unfold declared_constructor. destruct c as [i ci]. intros wfΣ [Hidecl Hcdecl].
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
  now rewrite <- subst_instance_subst.
Qed.

Lemma subst_declared_projection {cf:checker_flags} Σ c mdecl idecl pdecl n k :
  wf Σ ->
  declared_projection Σ c mdecl idecl pdecl ->
  on_snd (subst n (S (ind_npars mdecl + k))) pdecl = pdecl.
Proof.
  intros.
  eapply (declared_projection_closed (Σ:=empty_ext Σ)) in H; auto.
  unfold on_snd. simpl.
  rewrite subst_closedn.
  - eapply closed_upwards; eauto; try lia.
  - destruct pdecl; reflexivity.
Qed.
*)
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
(*
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
  case E: (instantiate_params_subst (List.rev params) args)=> /= [[l' t']|] /= //.
  specialize (Heq' _ _ E). rewrite Heq'. move=> [= <-]. f_equal.
  rewrite distr_subst //.
  move/instantiate_params_subst_length: E => -> /=. do 2 f_equal. lia.
Qed.
Hint Rewrite subst_instantiate_params : lift.
*)

Lemma to_extended_list_k_map_subst:
  forall n (k : nat) (c : context) k',
    #|c| + k' <= k ->
    to_extended_list_k c k' = map (subst n k) (to_extended_list_k c k').
Proof.
  intros n k c k'.
  pose proof (to_extended_list_k_spec c k').
  symmetry. solve_all.
  destruct H as [x' [-> Hx']]. intuition. simpl.
  destruct (leb_spec_Set k x').
  - lia.
  - reflexivity.
Qed.

Lemma wf_arities_context' {cf:checker_flags}:
  forall (Σ : global_env_ext) mind (mdecl : mutual_inductive_body),
    wf Σ ->
    on_inductive (lift_typing typing) Σ mind mdecl ->
    wf_local Σ (arities_context (ind_bodies mdecl)).
Proof.
  intros Σ mind mdecl wfΣ Hdecl.
  apply onInductives in Hdecl.
  unfold arities_context.
  revert Hdecl.
  induction (ind_bodies mdecl) using rev_ind. 1: constructor.
  intros Ha.
  rewrite rev_map_app.
  simpl. apply Alli_app in Ha as [Hl Hx].
  inv Hx. clear X0.
  apply onArity in X as [s Hs].
  specialize (IHl Hl).
  econstructor; eauto.
  fold (arities_context l) in *.
  unshelve epose proof (weakening Σ [] (arities_context l) _ _ wfΣ _ Hs).
  1: now rewrite app_context_nil_l.
  simpl in X.
  eapply (env_prop_typing _ _ typecheck_closed) in Hs; eauto.
  rewrite -> andb_and in Hs. destruct Hs as [Hs Ht].
  simpl in Hs. apply (lift_closed #|arities_context l|) in Hs.
  rewrite -> Hs, app_context_nil_l in X. simpl. exists s.
  apply X.
Qed.

Lemma wf_arities_context {cf:checker_flags} (Σ : global_env) mind mdecl : wf Σ ->
  declared_minductive Σ mind mdecl -> wf_local (Σ, ind_universes mdecl) (arities_context mdecl.(ind_bodies)).
Proof.
  intros wfΣ Hdecl.
  eapply declared_minductive_inv in Hdecl. 2:apply weaken_env_prop_typing. all:eauto.
  eapply wf_arities_context'; eauto.
Qed.

Lemma on_constructor_closed {cf:checker_flags} {Σ : global_env} {mind mdecl u idecl indices cdecl cs} :
  wf Σ ->
  on_constructor (lift_typing typing) (Σ, ind_universes mdecl) mdecl (inductive_ind mind) indices idecl cdecl cs ->
  let cty := subst0 (inds (inductive_mind mind) u (ind_bodies mdecl))
                    (subst_instance u cdecl.(cstr_type))
  in closed cty.
Proof.
  intros wfΣ [? ? ? [s Hs] _ _ _ _].
  pose proof (typing_wf_local Hs).
  destruct cdecl as [id cty car].
  apply subject_closed in Hs; eauto.
  rewrite arities_context_length in Hs.
  simpl in *.
  eapply (closedn_subst _ 0 0).
  - clear. unfold inds.
    induction #|ind_bodies mdecl|; simpl; try constructor; auto.
  - simpl. now rewrite -> inds_length, closedn_subst_instance.
Qed.

Lemma subst_cstr_concl_head ind u mdecl (arity : context) args :
  let head := tRel (#|ind_bodies mdecl| - S (inductive_ind ind) + #|ind_params mdecl| + #|arity|) in
  let s := (inds (inductive_mind ind) u (ind_bodies mdecl)) in
  inductive_ind ind < #|ind_bodies mdecl| ->
  subst s (#|arity| + #|ind_params mdecl|)
        (subst_instance u (mkApps head (to_extended_list_k (ind_params mdecl) #|arity| ++ args)))
  = mkApps (tInd ind u) (to_extended_list_k (ind_params mdecl) #|arity| ++
                        map (subst s (#|arity| + #|ind_params mdecl|)) (map (subst_instance u) args)).
Proof.
  intros.
  rewrite subst_instance_mkApps subst_mkApps.
  f_equal.
  - subst head. simpl subst_instance.
    rewrite (subst_rel_eq _ _ (#|ind_bodies mdecl| - S (inductive_ind ind)) (tInd ind u)) //; try lia.
    subst s. rewrite inds_spec rev_mapi nth_error_mapi /=.
    elim nth_error_spec.
    + intros. simpl.
      f_equal. destruct ind; simpl. f_equal. f_equal. simpl in H. lia.
    + rewrite List.rev_length. lia.
  - rewrite !map_app. f_equal.
    rewrite map_subst_instance_to_extended_list_k.
    erewrite to_extended_list_k_map_subst at 2.
    + now rewrite Nat.add_comm.
    + lia.
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
    + rewrite (lift_to_extended_list_k _ _ 1) map_map_compose.
      pose proof (to_extended_list_k_spec Γ k).
      solve_all. destruct H0 as [n [-> Hn]].
      rewrite /lift (subst_app_decomp [a] s k); auto with wf.
      rewrite subst_rel_gt.
      * simpl. lia.
      * unf_term. repeat (f_equal; simpl; try lia).
    + now rewrite /map (subst_rel_eq _ _ 0 a).
  - rewrite -IHcontext_subst // to_extended_list_k_cons /=.
    rewrite (lift_to_extended_list_k _ _ 1) map_map_compose.
    pose proof (to_extended_list_k_spec Γ k).
    solve_all. destruct H0 as [n [-> Hn]].
    rewrite /lift (subst_app_decomp [subst0 s b] s k); auto with wf.
    rewrite subst_rel_gt.
    + simpl; lia.
    + unf_term. repeat (f_equal; simpl; try lia).
Qed.


Lemma Alli_map_option_out_mapi_Some_spec' {A B} (f g : nat -> A -> option B) h l t P :
  All P l ->
  (forall i x t, P x -> f i x = Some t -> g i x = Some (h t)) ->
  map_option_out (mapi f l) = Some t ->
  map_option_out (mapi g l) = Some (map h t).
Proof.
  unfold mapi. generalize 0.
  move => n Ha Hfg. move: t.
  induction Ha in n |- *; try constructor; auto.
  - destruct t; cbnr; discriminate.
  - move=> t /=. case E: (f n x) => [b|]; try congruence.
    rewrite (Hfg n _ _ p E).
    case E' : map_option_out => [b'|]; try congruence.
    move=> [= <-]. now rewrite (IHHa _ _ E').
Qed.

(*
Lemma subst_build_case_predicate_type ind mdecl idecl u params ps pty n k :
  closed_ctx (subst_instance u (ind_params mdecl)) ->
  closed (ind_type idecl) ->
  build_case_predicate_type ind mdecl idecl params u ps = Some pty ->
  build_case_predicate_type ind mdecl
    (map_one_inductive_body (context_assumptions mdecl.(ind_params))
            (length (arities_context (ind_bodies mdecl))) (fun k' => subst n (k' + k))
            (inductive_ind ind) idecl)
    (map (subst n k) params) u ps
  = Some (subst n k pty).
Proof.
  intros closedparams closedtype.
  unfold build_case_predicate_type; simpl.
  case_eq (instantiate_params (subst_instance u (ind_params mdecl)) params
                              (subst_instance u (ind_type idecl)));
    [|discriminate ].
  intros ipars Hipars.
  apply (subst_instantiate_params n k) in Hipars; tas.
  rewrite ind_type_map. simpl.
  rewrite subst_closedn in Hipars.
  { rewrite closedn_subst_instance; eapply closed_upwards; tea; lia. }
  rewrite subst_closedn; [eapply closed_upwards; tea; lia|].
  rewrite Hipars.
  specialize (subst_destArity [] ipars n k);
    destruct (destArity [] ipars) as [[ctx s]|]; [|discriminate].
  simpl. cbn. move => -> /some_inj-HH. simpl. f_equal.
  etransitivity.
  2: exact (f_equal (subst n k) HH).
  rewrite subst_it_mkProd_or_LetIn. unf_term. simpl. f_equal. f_equal.
  { destruct idecl; reflexivity. }
  rewrite subst_mkApps; simpl. f_equal.
  rewrite map_app; f_equal.
  - rewrite !map_map; apply map_ext; clear; intro.
    rewrite subst_context_length.
    rewrite -> commut_lift_subst_rec by lia.
    f_equal. lia.
  - rewrite /to_extended_list to_extended_list_k_subst.
    rewrite <- to_extended_list_k_map_subst by lia. reflexivity.
Qed.

Lemma subst_build_branches_type {cf:checker_flags}
      n k Σ ind mdecl idecl indices args u p brs cs :
  wf Σ ->
  declared_inductive Σ ind mdecl idecl ->
  closed_ctx (subst_instance u (ind_params mdecl)) ->
  on_inductive (lift_typing typing) (Σ, ind_universes mdecl)
               (inductive_mind ind) mdecl ->
  on_constructors (lift_typing typing) (Σ, ind_universes mdecl)
                  mdecl (inductive_ind ind) idecl indices (ind_ctors idecl) cs ->
  map_option_out (build_branches_type ind mdecl idecl args u p) = Some brs ->
  map_option_out (build_branches_type ind mdecl
         idecl (map (subst n k) args) u (subst n k p)) =
         Some (map (on_snd (subst n k)) brs).
Proof.
  intros wfΣ wfidecl closedparams onmind Honcs.
  rewrite !build_branches_type_. cbn.
  eapply Alli_map_option_out_mapi_Some_spec'.
  { eapply All2_All_left; tea. intros x y u'; exact (y; u'). }
  clear Honcs brs.
  intros j [[id t] i] [t' k'] [cs' Honc].
  case_eq (instantiate_params (subst_instance u (ind_params mdecl)) args
                              (subst0 (inds (inductive_mind ind) u
                                            (ind_bodies mdecl))
                                      (subst_instance u t)));
    [|discriminate].
  intros ty Heq; cbn.
  pose proof (on_constructor_closed wfΣ (u:=u) Honc) as clt; cbn in clt.
  eapply (closed_upwards k) in clt; try lia.
  remember (subst0 (inds (inductive_mind ind) u (ind_bodies mdecl))
                   (subst_instance u t)) as ty'.
  apply (subst_instantiate_params n k) in Heq as Heq'; tas.
  erewrite subst_closedn in Heq'; tas.
  rewrite Heq'.
  eapply instantiate_params_make_context_subst in Heq.
  destruct Heq as [ctx' [ty'' [s' [Hty [Hsubst Ht0]]]]].
  subst ty; simpl.
  rewrite Heqty' in Hty.
  destruct Honc as [Hcstr_args ? cdecl_eq Hty' _ _]; unfold cstr_type in *; simpl in *.
  rewrite cdecl_eq in Hty.
  rewrite -> !subst_instance_it_mkProd_or_LetIn in Hty.
  rewrite !subst_it_mkProd_or_LetIn in Hty.
  assert (H0: #|subst_context (inds (inductive_mind ind) u (ind_bodies mdecl)) 0
                (subst_instance u (ind_params mdecl))|
          = #|subst_instance u (ind_params mdecl)|). {
    now rewrite subst_context_length. }
  rewrite <- H0 in Hty.
  rewrite decompose_prod_n_assum_it_mkProd in Hty.
  injection Hty. clear Hty.
  intros Heqty'' <-. revert Heqty''.
  rewrite !subst_instance_length Nat.add_0_r.
  rewrite subst_context_length subst_instance_length.
  rewrite (subst_cstr_concl_head ind u mdecl cs'.(cstr_args) cs'.(cstr_indices)).
  { destruct wfidecl as [Hmdecl Hnth].
    now apply nth_error_Some_length in Hnth.
  }
  intros <-. rewrite !subst_it_mkProd_or_LetIn !subst_mkApps /=.
  rewrite !decompose_prod_assum_it_mkProd /=;
          try by rewrite is_ind_app_head_mkApps.
  rewrite !decompose_app_mkApps; try by reflexivity.
  simpl. rewrite !map_app !subst_context_length
                 !subst_instance_length Nat.add_0_r.
  eapply subst_to_extended_list_k with (k:=#|cs'.(cstr_args)|) in Hsubst as XX.
  rewrite map_subst_instance_to_extended_list_k in XX.
  rewrite !XX; clear XX.
  apply make_context_subst_spec in Hsubst as Hsubst'.
  rewrite rev_involutive in Hsubst'.
  pose proof (context_subst_assumptions_length Hsubst') as H1.
  case E: chop => [l l'].
  have chopm := (chop_map _ _ _ _ _ E).
  move: E chopm.
  rewrite chop_n_app ?map_length. {
    rewrite <- H1. apply onNpars in onmind.
    now rewrite subst_instance_assumptions. }
  move=> [= <- <-] chopm.
  move: {chopm}(chopm _ (subst n (#|cs'.(cstr_args)| + k))).
  rewrite map_app.
  move=> chopm; rewrite {}chopm /=.
  inversion 1; subst. f_equal. unfold on_snd; cbn; f_equal.
  rewrite !app_nil_r /on_snd /=.
  rewrite subst_it_mkProd_or_LetIn !subst_context_length !subst_mkApps
          !subst_instance_length !map_app.
  f_equal. f_equal.
  -- rewrite -> commut_lift_subst_rec by lia. arith_congr.
  -- f_equal. simpl. f_equal.
     rewrite !subst_mkApps /= !map_app. f_equal.
     f_equal.
     rewrite /to_extended_list -to_extended_list_k_map_subst.
     ++ rewrite !subst_context_length subst_instance_length. lia.
     ++ now rewrite to_extended_list_k_subst.
Qed.
*)

Hint Unfold subst1 : subst.
Hint Rewrite subst_mkApps distr_subst: subst.

Inductive untyped_subslet (Γ : context) : list term -> context -> Type :=
| untyped_emptyslet : untyped_subslet Γ [] []
| untyped_cons_let_ass Δ s na t T :
    untyped_subslet Γ s Δ ->
    untyped_subslet Γ (t :: s) (Δ ,, vass na T)
| untyped_cons_let_def Δ s na t T :
    untyped_subslet Γ s Δ ->
    untyped_subslet Γ (subst0 s t :: s) (Δ ,, vdef na t T).

Lemma subslet_untyped_subslet {cf:checker_flags} Σ Γ s Γ' : subslet Σ Γ s Γ' -> untyped_subslet Γ s Γ'.
Proof.
  induction 1; constructor; auto.
Qed.
Coercion subslet_untyped_subslet : subslet >-> untyped_subslet.

Lemma decompose_prod_assum_it_mkProd_or_LetIn ctx t ctx' t' :
 decompose_prod_assum ctx t = (ctx', t') ->
 it_mkProd_or_LetIn ctx t = it_mkProd_or_LetIn ctx' t'.
Proof.
  induction t in ctx, ctx', t' |- *; simpl; try intros [= -> <-]; auto.
  - intros H. now apply IHt2 in H.
  - intros H. now apply IHt3 in H.
Qed.

Inductive decompose_prod_assum_graph : term -> (context * term) -> Type :=
| decompose_arity ctx t : decompose_prod_assum_graph (it_mkProd_or_LetIn ctx t) (ctx, t).

Lemma decompose_prod_assum_spec ctx t :
  decompose_prod_assum_graph (it_mkProd_or_LetIn ctx t) (decompose_prod_assum ctx t).
Proof.
 induction t in ctx |- *; simpl; try constructor 1.
 - specialize (IHt2 (vass na t1 :: ctx)).
   apply IHt2.
 - apply (IHt3 (vdef na t1 t2 :: ctx)).
Qed.

Lemma subst_decompose_prod_assum_rec ctx t s k :
  let (ctx', t') := decompose_prod_assum ctx t in
  ∑ ctx'' t'',
    (decompose_prod_assum [] (subst s (#|ctx'| + k) t') = (ctx'', t'')) *
  (decompose_prod_assum (subst_context s k ctx) (subst s (length ctx + k) t) =
  (subst_context s k ctx' ,,, ctx'', t'')).
Proof.
  induction t in ctx, k |- *; simpl; try solve [ eexists _, _; pcuicfo ].
  - elim: leb_spec_Set => comp.
    + destruct (nth_error s (n - (#|ctx| + k))) eqn:Heq.
      * destruct decompose_prod_assum eqn:Heq'.
        eexists _, _; intuition eauto.
        now rewrite decompose_prod_assum_ctx Heq'.
      * eexists _,_; pcuicfo.
    + eexists _,_; pcuicfo.
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
Qed.
(*

Lemma subst_decompose_prod_assum_rec ctx t s k :
  let (ctx', t') := decompose_prod_assum ctx t in
  let (ctx'', t'') := decompose_prod_assum (subst_context s k ctx) (subst s (length ctx + k) t) in
  subst s k (it_mkProd_or_LetIn ctx' t') = it_mkProd_or_LetIn ctx'' t''.
Proof.
  rewrite decompose_prod_assum_ctx.
  destruct decompose_prod_assum eqn:Heq.
  destruct (decompose_prod_assum (subst_context _ _ _) _) eqn:Heq'.
  apply decompose_prod_assum_it_mkProd_or_LetIn in Heq.
  apply decompose_prod_assum_it_mkProd_or_LetIn in Heq'.
  rewrite subst_it_mkProd_or_LetIn.
  rewrite subst_context_app.
  rewrite it_mkProd_or_LetIn_app.
  rewrite -Heq'. f_equal.
  simpl in Heq.
  rewrite Heq.
  rewrite subst_it_mkProd_or_LetIn.
  rewrite app_context_length.
  lia_f_equal.
Qed. *)

Lemma smash_context_subst Δ s n Γ : smash_context (subst_context s (n + #|Γ|) Δ) (subst_context s n Γ) =
  subst_context s n (smash_context Δ Γ).
Proof.
  revert Δ. induction Γ as [|[na [b|] ty]]; intros Δ; simpl; auto.
  - now rewrite Nat.add_0_r.
  - rewrite -IHΓ.
    rewrite subst_context_snoc /=. f_equal.
    rewrite !subst_context_alt !mapi_compose.
    apply mapi_ext=> n' x.
    destruct x as [na' [b'|] ty']; simpl.
    * rewrite !mapi_length /subst_decl /= /map_decl /=; f_equal.
      + rewrite Nat.add_0_r distr_subst_rec. simpl. lia_f_equal.
      + rewrite Nat.add_0_r distr_subst_rec; simpl. lia_f_equal.
    * rewrite !mapi_length /subst_decl /= /map_decl /=; f_equal.
      rewrite Nat.add_0_r distr_subst_rec /=. lia_f_equal.
  - rewrite -IHΓ.
    rewrite subst_context_snoc /= // /subst_decl /map_decl /=.
    f_equal.
    rewrite subst_context_app. simpl.
    rewrite /app_context. f_equal.
    + lia_f_equal.
    + rewrite /subst_context // /fold_context_k /= /map_decl /=.
      lia_f_equal.
Qed.

Arguments Nat.sub : simpl nomatch.

Lemma assumption_context_skipn Γ n :
  assumption_context Γ ->
  assumption_context (skipn n Γ).
Proof.
  induction 1 in n |- *; simpl.
  - destruct n; constructor.
  - destruct n.
    * rewrite skipn_0. constructor; auto.
    * now rewrite skipn_S.
Qed.

Hint Rewrite idsn_length : len.

Lemma subst_fn_eq s s' x : s = s' -> subst_fn s x = subst_fn s' x.
Proof.
  intros -> ; reflexivity.
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

Lemma substitution_check_one_fix s k mfix inds :
  map_option_out (map check_one_fix mfix) = Some inds ->
  map_option_out (map (fun x : def term =>
    check_one_fix (map_def (subst s k) (subst s (#|mfix| + k)) x)) mfix) = Some inds.
Proof.
  apply map_option_out_impl.
  move=> [na ty def rarg] /=.
  rewrite decompose_prod_assum_ctx.
  destruct (decompose_prod_assum _ ty) eqn:decomp.
  rewrite decompose_prod_assum_ctx in decomp.
  destruct (decompose_prod_assum [] ty) eqn:decty.
  noconf decomp. rewrite !app_context_nil_l.
  pose proof (subst_decompose_prod_assum_rec [] ty s k).
  rewrite decty in X.
  destruct X as [ctx'' [t'' [dect decty']]].
  rewrite subst_context_nil in decty'; simpl in decty'.
  rewrite decty'. intros ind.
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
Qed.

Lemma context_assumptions_smash_context Δ Γ :
  context_assumptions (smash_context Δ Γ) = 
  context_assumptions Δ + context_assumptions Γ.
Proof.
  induction Γ as [|[? [] ?] ?] in Δ |- *; simpl; auto;
  rewrite IHΓ.
  - now rewrite context_assumptions_fold.
  - rewrite context_assumptions_app /=. lia.
Qed. 

Lemma nth_error_ass_subst_context s k Γ : 
  (forall n d, nth_error Γ n = Some d -> decl_body d = None) ->
  forall n d, nth_error (subst_context s k Γ) n = Some d -> decl_body d = None.
Proof.
  induction Γ as [|[? [] ?] ?] in |- *; simpl; auto;
  intros; destruct n; simpl in *; rewrite ?subst_context_snoc in H0; simpl in H0.
  - noconf H0; simpl.
    specialize (H 0 _ eq_refl). simpl in H; discriminate.
  - specialize (H 0 _ eq_refl). simpl in H; discriminate.
  - noconf H0; simpl. auto.
  - eapply IHΓ; intros; eauto.
    now specialize (H (S n0) d0 H1).
Qed.

Lemma nth_error_smash_context Γ Δ : 
  (forall n d, nth_error Δ n = Some d -> decl_body d = None) ->
  forall n d, nth_error (smash_context Δ Γ) n = Some d -> decl_body d = None.
Proof.
  induction Γ as [|[? [] ?] ?] in Δ |- *; simpl; auto.
  - intros. eapply (IHΓ (subst_context [t] 0 Δ)); tea.
    now apply nth_error_ass_subst_context.
  - intros. eapply IHΓ. 2:eauto.
    intros.
    pose proof (nth_error_Some_length H1). autorewrite with len in H2. simpl in H2.
    destruct (eq_dec n0 #|Δ|).
    * subst.
      rewrite nth_error_app_ge in H1; try lia.
      rewrite Nat.sub_diag /= in H1. noconf H1.
      reflexivity.
    * rewrite nth_error_app_lt in H1; try lia. eauto.
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
  rewrite decty'.
  apply decompose_app_inv in eqapp.
  subst t.
  rewrite subst_mkApps /= in dect.
  rewrite decompose_prod_assum_mkApps in dect. noconf dect.
  rewrite decompose_app_mkApps //.
Qed.

Lemma subs_nth_error {cf:checker_flags} Σ Γ s Δ decl n t :
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
  - intros. destruct decl as [na' [b|] ty]; cbn in *.
    + eapply IHX. all: eauto.
    + now apply IHX.
Qed.

Lemma untyped_subslet_nth_error Γ s Δ decl n t :
  untyped_subslet Γ s Δ ->
  nth_error Δ n = Some decl ->
  nth_error s n = Some t ->
  match decl_body decl return Type with
  | Some t' => t = subst0 (skipn (S n) s) t'
  | None => True
  end.
Proof.
  induction 1 in n |- *; simpl; auto; destruct n; simpl; try congruence.
  - intros [= <-]. intros [= ->].
    simpl. auto.
  - intros. destruct decl as [na' [b|] ty]; cbn in *. 2: auto.
    specialize (IHX _ H H0). intuition auto.
  - intros [= <-]. intros [= <-].
    simpl. split; auto.
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
  induction M2 in M1, N1 |- *.
  - simpl; auto.
  - intros. specialize (IHM2 (tApp M1 a) (tApp N1 a)).
    forward IHM2.
    { constructor. auto. }
    simpl. auto.
Qed.

Lemma red1_mkApps_r Σ Γ M1 M2 N2 :
  OnOne2 (red1 Σ Γ) M2 N2 -> red1 Σ Γ (mkApps M1 M2) (mkApps M1 N2).
Proof.
  intros. induction X in M1 |- *.
  - simpl. eapply red1_mkApps_l. constructor; auto.
  - apply (IHX (tApp M1 hd)).
Qed.

Arguments iota_red : simpl never.

(** Standard substitution lemma for a context with no lets. *)

Inductive nth_error_app_spec {A} (l l' : list A) (n : nat) : option A -> Type :=
| nth_error_app_spec_left x : 
  nth_error l n = Some x -> 
  n < #|l| ->
  nth_error_app_spec l l' n (Some x)
| nth_error_app_spec_right x :
  nth_error l' (n - #|l|) = Some x ->
  #|l| <= n < #|l| + #|l'| ->
  nth_error_app_spec l l' n (Some x)
| nth_error_app_spec_out : #|l| + #|l'| <= n -> nth_error_app_spec l l' n None.

Lemma nth_error_appP {A} (l l' : list A) (n : nat) : nth_error_app_spec l l' n (nth_error (l ++ l') n).
Proof.
  destruct (Nat.ltb n #|l|) eqn:lt; [apply Nat.ltb_lt in lt|apply Nat.ltb_nlt in lt].
  * rewrite nth_error_app_lt //.
    destruct (snd (nth_error_Some' _ _) lt) as [x eq].
    rewrite eq.
    constructor; auto.
  * destruct (Nat.ltb n (#|l| + #|l'|)) eqn:ltb'; [apply Nat.ltb_lt in ltb'|apply Nat.ltb_nlt in ltb'].
    + rewrite nth_error_app2; try lia.
      destruct nth_error eqn:hnth.
      - constructor 2; auto; try lia.
      - constructor.
        eapply nth_error_None in hnth. lia.
    + case: nth_error_spec => //; try lia.
      { intros. len in l0. lia. }
      len. intros. constructor. lia.
Qed.

Lemma nth_error_app_context (Γ Δ : context) (n : nat) : 
  nth_error_app_spec Δ Γ n (nth_error (Γ ,,, Δ) n).
Proof.
  apply nth_error_appP.
Qed.

(** Substitution without lets in Γ' *)
Lemma subs_usubst {cf:checker_flags} Σ Γ Γ' Γ'' s :
  subs Σ Γ s Γ' ->
  usubst (Γ,,, Γ',,, Γ'') (⇑^#|Γ''| (s ⋅n ids)) (Γ,,, subst_context s 0 Γ'').
Proof.
  intros subs n decl.
  case: (nth_error_app_context (Γ ,,, Γ') Γ'' n) => // x hnth hlt [=] hx; subst x => b hb.
  - left; eexists n, _.
    split; auto.
    * rewrite Upn_eq /subst_consn idsn_lt //.
    * rewrite nth_error_app_lt; len => //.
      change (fun m => S (n + m)) with (lift_renaming (S n) 0).
      rewrite nth_error_subst_context /= hnth /=. split; eauto.
      rewrite /= hb /=. f_equal.
      rewrite subst_inst. rewrite Nat.add_0_r.
      rewrite rename_inst.
      sigma. rewrite ren_lift_renaming. 
      rewrite Upn_0.
      rewrite -shiftn_consn_idsn.
      rewrite -subst_compose_assoc -Upn_Upn.
      now replace (S n + (#|Γ''| - S n)) with #|Γ''| by lia.
  - move: hnth.
    case: (nth_error_app_context Γ Γ' _) => // x' hnth hn' [=] eq; subst x'.
    * elimtype False.
      revert subs hnth hb; generalize (n - #|Γ''|); clear.
      intros n subs; induction subs in n |- *; simpl => //.
      { now rewrite nth_error_nil //. }
      { destruct n; simpl.
        * intros [= <-] => //.
        * intros hnth. now specialize (IHsubs _ hnth). }
    * left; exists (n - #|Γ'|), decl.
      repeat split.
      + rewrite Upn_eq /subst_consn nth_error_idsn_None //; try lia.
        unfold subst_compose.
        apply subs_length in subs.
        rewrite (proj2 (nth_error_None _ _)); try (len; lia).
        simpl. len. unfold shiftk. lia_f_equal.
      + rewrite nth_error_app_ge; len; try lia.
        rewrite -hnth. lia_f_equal.
      + rewrite -lift_renaming_0_rshift hb /=.
        f_equal; sigma. rewrite ren_lift_renaming. sigma. 
        apply inst_ext. rewrite -shiftk_shift.
        rewrite - !subst_compose_assoc -shiftk_shift.
        replace (S n) with ((S n - #|Γ''|) + #|Γ''|) by lia.
        rewrite -shiftk_compose subst_compose_assoc shiftn_consn_idsn.
        replace (S n - #|Γ''|) with (S (n - #|Γ''| - #|Γ'|) + #|Γ'|) by lia.
        rewrite -shiftk_compose subst_compose_assoc -(subst_compose_assoc (↑^#|Γ'|)).
        apply subs_length in subs.
        rewrite subst_consn_shiftn //. sigma.
        rewrite -shiftk_shift. rewrite -shiftk_shift_l shiftk_compose.
        now replace (n - #|Γ''| - #|Γ'| + S #|Γ''|) with (S (n - #|Γ'|)) by lia.
Qed.

Lemma untyped_subslet_length {Γ s Δ} : untyped_subslet Γ s Δ -> #|s| = #|Δ|.
Proof.
  induction 1; simpl; lia.
Qed.

(* Let-expanding substitution *)
Lemma subslet_usubst {Γ Δ Γ' s} :
  untyped_subslet Γ s Δ ->
  usubst (Γ,,, Δ,,, Γ') (⇑^#|Γ'| (s ⋅n ids)) (Γ,,, subst_context s 0 Γ').
Proof.
  intros subs n decl.
  case: (nth_error_app_context (Γ ,,, Δ) Γ' n) => // x hnth hlt [=] hx; subst x => b hb.
  - left; eexists n, _.
    split; auto.
    * rewrite Upn_eq /subst_consn idsn_lt //.
    * rewrite nth_error_app_lt; len => //.
      change (fun m => S (n + m)) with (lift_renaming (S n) 0).
      rewrite nth_error_subst_context /= hnth /=. split; eauto.
      rewrite /= hb /=. f_equal.
      rewrite subst_inst. rewrite Nat.add_0_r.
      rewrite rename_inst.
      sigma. rewrite ren_lift_renaming. 
      rewrite Upn_0.
      rewrite -shiftn_consn_idsn.
      rewrite -subst_compose_assoc -Upn_Upn.
      now replace (S n + (#|Γ'| - S n)) with #|Γ'| by lia.
  - move: hnth.
    case: (nth_error_app_context Γ Δ _) => // x' hnth hn' [=] eq; subst x'.
    * right.
      pose proof (untyped_subslet_length subs).
      rewrite Upn_eq {1}/subst_consn nth_error_idsn_None; try lia.
      len. rewrite subst_consn_compose subst_consn_lt'; len; try lia.
      rewrite /subst_fn nth_error_map. 
      case: nth_error_spec; try lia. move=> x hs hns.
      epose proof (untyped_subslet_nth_error _ _ _ _ _ _ subs hnth hs).
      rewrite hb in X; rewrite X; cbn.
      rewrite subst_inst Upn_0 inst_assoc. apply inst_ext.
      rewrite skipn_subst. 2:lia.
      sigma.
      rewrite subst_consn_compose. sigma. 
      rewrite -subst_compose_assoc -shiftk_shift -subst_compose_assoc.
      rewrite -shiftk_shift.
      rewrite (shift_subst_consn_ge (S n)). 2:len; lia. now len.
    * left; exists (n - #|s|), decl.
      pose proof (untyped_subslet_length subs).
      repeat split.
      + rewrite Upn_eq /subst_consn nth_error_idsn_None //; try lia.
        unfold subst_compose.
        rewrite (proj2 (nth_error_None _ _)); try (len; lia).
        simpl. len. unfold shiftk. lia_f_equal.
      + rewrite nth_error_app_ge; len; try lia.
        rewrite -hnth. lia_f_equal.
      + rewrite -lift_renaming_0_rshift hb /=.
        f_equal; sigma. rewrite ren_lift_renaming. sigma. 
        apply inst_ext. rewrite -shiftk_shift.
        rewrite - !subst_compose_assoc -shiftk_shift.
        replace (S n) with ((S n - #|Γ'|) + #|Γ'|) by lia.
        rewrite -shiftk_compose subst_compose_assoc shiftn_consn_idsn.
        replace (S n - #|Γ'|) with (S (n - #|Γ'| - #|s|) + #|s|) by lia.
        rewrite -shiftk_compose subst_compose_assoc -(subst_compose_assoc (↑^#|s|)).
        rewrite subst_consn_shiftn //. sigma.
        rewrite -shiftk_shift. rewrite -shiftk_shift_l shiftk_compose.
        now replace (n - #|Γ'| - #|s| + S #|Γ'|) with (S (n - #|s|)) by lia.
Qed.

Lemma substitution_red1 {cf:checker_flags} (Σ : global_env_ext) {Γ Γ' Γ'' s M N} :
  wf Σ -> subs Σ Γ s Γ' -> wf_local Σ Γ ->
  red1 Σ (Γ ,,, Γ' ,,, Γ'') M N ->
  red Σ (Γ ,,, subst_context s 0 Γ'') (subst s #|Γ''| M) (subst s #|Γ''| N).
Proof.
  intros wfΣ Hs wfΓ H.
  rewrite !subst_inst.
  eapply red1_inst; eauto.
  now eapply subs_usubst.
Qed.

Lemma subst_skipn {n s k t} : n <= #|s| -> subst (skipn n s) k t = subst s k (lift n k t).
Proof.
  intros Hn.
  assert (#|firstn n s| = n) by (rewrite firstn_length_le; lia).
  rewrite <- (firstn_skipn n s) at 2.
  rewrite subst_app_simpl. rewrite H.
  rewrite <- commut_lift_subst_rec; auto with arith.
  rewrite -{3}H. now rewrite simpl_subst_k.
Qed.

Lemma substitution_let_red `{cf : checker_flags} (Σ : global_env_ext) {Γ Δ Γ' s M N} :
  wf Σ -> subslet Σ Γ s Δ -> wf_local Σ Γ ->
  red1 Σ (Γ ,,, Δ ,,, Γ') M N ->
  red Σ (Γ ,,, subst_context s 0 Γ') (subst s #|Γ'| M) (subst s #|Γ'| N).
Proof.
  intros wfΣ Hs wfΓ H.
  rewrite !subst_inst.
  eapply red1_inst; eauto.
  now eapply (subslet_usubst Hs).
Qed.

Lemma substitution_untyped_let_red {cf:checker_flags} (Σ : global_env_ext) Γ Δ Γ' s M N :
  wf Σ -> untyped_subslet Γ s Δ ->
  red1 Σ (Γ ,,, Δ ,,, Γ') M N ->
  red Σ (Γ ,,, subst_context s 0 Γ') (subst s #|Γ'| M) (subst s #|Γ'| N).
Proof.
  intros wfΣ Hs H.
  rewrite !subst_inst.
  eapply red1_inst; eauto.
  now eapply subslet_usubst.
Qed.

Lemma substitution_untyped_red {cf:checker_flags} Σ Γ Δ Γ' s M N :
  wf Σ -> untyped_subslet Γ s Δ ->
  red Σ (Γ ,,, Δ ,,, Γ') M N ->
  red Σ (Γ ,,, subst_context s 0 Γ') (subst s #|Γ'| M) (subst s #|Γ'| N).
Proof.
  intros wfΣ subsl.
  induction 1; trea.
  - eapply substitution_untyped_let_red; eassumption.
  - etransitivity; eauto.
Qed.

Lemma subst_compare_term {cf:checker_flags} le Σ (φ : ConstraintSet.t) (l : list term) (k : nat) (T U : term) :
  compare_term le Σ φ T U -> compare_term le Σ φ (subst l k T) (subst l k U).
Proof.
  destruct le; simpl.
  - apply subst_leq_term.
  - apply subst_eq_term. 
Qed.

Lemma subst_eq_decl `{checker_flags} {le Σ ϕ l k d d'} :
  eq_decl le Σ ϕ d d' -> eq_decl le Σ ϕ (subst_decl l k d) (subst_decl l k d').
Proof.
  intros []; constructor; auto; destruct le; 
    intuition eauto using subst_compare_term, subst_eq_term, subst_leq_term.
Qed.

Lemma subst_eq_context `{checker_flags} le Σ φ l l' n k :
  eq_context le Σ φ l l' ->
  eq_context le Σ φ (subst_context n k l) (subst_context n k l').
Proof.
  induction 1; rewrite ?subst_context_snoc /=; constructor; auto.
  erewrite (All2_fold_length X). simpl.
  apply (subst_eq_decl p).
Qed.

Lemma substitution_red `{cf : checker_flags} (Σ : global_env_ext) Γ Δ Γ' s M N :
  wf Σ -> subslet Σ Γ s Δ -> wf_local Σ Γ ->
  red Σ (Γ ,,, Δ ,,, Γ') M N ->
  red Σ (Γ ,,, subst_context s 0 Γ') (subst s #|Γ'| M) (subst s #|Γ'| N).
Proof.
  intros HG Hs Hl Hred. induction Hred; trea.
  - eapply substitution_let_red; eauto.
  - etransitivity; eauto.
Qed.
 
Lemma red_red_onctx {cf:checker_flags} Σ Γ Δ Γ' s s' ctx :
  untyped_subslet Γ s Δ ->
  onctx
    (fun b : term =>
    forall Δ Γ'0 : context,
    untyped_subslet Γ s Δ ->
    red Σ (Γ,,, Γ'0) (subst s #|Γ'0| b) (subst s' #|Γ'0| b)) ctx ->
  All2_fold
  (fun (Γ0 Δ0 : context) (d d' : context_decl) =>
    red_decls Σ (Γ,,, Γ',,, mapi_context (shiftf (subst s) #|Γ'|) Γ0)
      (Γ,,, Γ',,, mapi_context (shiftf (subst s') #|Γ'|) Δ0)
      (map_decl (shiftf (subst s) #|Γ'| #|Γ0|) d)
      (map_decl (shiftf (subst s') #|Γ'| #|Γ0|) d')) ctx ctx.
Proof.
  intros hsubs.
  induction 1; constructor; auto.
  destruct p. destruct x as [na [b|] ty]; constructor; auto; simpl in *;
  rewrite /shiftf.
  - specialize (o _ (Γ' ,,, mapi_context (fun k' => subst s (k' + #|Γ'|)) l) hsubs).
    len in o. now rewrite -app_context_assoc.
  - specialize (r _ (Γ' ,,, mapi_context (fun k' => subst s (k' + #|Γ'|)) l) hsubs).
    len in r. now rewrite -app_context_assoc.
  - specialize (r _ (Γ' ,,, mapi_context (fun k' => subst s (k' + #|Γ'|)) l) hsubs).
    len in r. now rewrite -app_context_assoc.
Qed.

Lemma red_red {cf:checker_flags} (Σ : global_env_ext) Γ Δ Γ' s s' b : wf Σ ->
  All2 (red Σ Γ) s s' ->
  untyped_subslet Γ s Δ ->
  red Σ (Γ ,,, Γ') (subst s #|Γ'| b) (subst s' #|Γ'| b).
Proof.
  intros wfΣ Hall Hsubs.
  revert Δ Γ' Hsubs.
  elim b using term_forall_list_ind;
        intros; match goal with
                  |- context [tRel _] => idtac
                | |- _ => cbn -[plus]
                end; try easy;
      autorewrite with map; 
      rewrite ?Nat.add_assoc;
      try solve [f_equal; auto; solve_all].

  - unfold subst.
    destruct (#|Γ'| <=? n) eqn:Heq.
    + destruct nth_error eqn:Heq'.
      * destruct (All2_nth_error_Some _ _ Hall Heq') as [t' [-> Ptt']].
        intros. apply (weakening_red Σ Γ [] Γ' t t'); auto.
      * rewrite (All2_nth_error_None _ Hall Heq').
        apply All2_length in Hall as ->. reflexivity.
    + reflexivity.

  - apply red_evar. apply All2_map. solve_all.
  - apply red_prod; eauto.
    now eapply (X0 Δ (Γ' ,, _)).

  - apply red_abs; eauto.
    now eapply (X0 Δ (Γ' ,, _)).

  - apply red_letin; eauto.
    now eapply (X1 Δ (Γ' ,, _)).
  - apply red_app; eauto.
  - eapply (red_case (p:=(map_predicate_k id (subst s) #|Γ'| p))); simpl; solve_all.
    * specialize (r _ (Γ' ,,, subst_context s #|Γ'| (pcontext p)) Hsubs). len in r.
      now rewrite mapi_context_fold -app_context_assoc.
    * eapply red_ctx_rel_red_context_rel => //.
      eapply All2_fold_mapi.
      eapply red_red_onctx; tea.
    * red. solve_all.
      eapply All_All2; tea => /=. solve_all; unfold on_Trel; simpl.
      + specialize (b0 _ (Γ' ,,, mapi_context (shiftf (subst s) #|Γ'|) (bcontext x)) Hsubs).
        len in b0. now rewrite -app_context_assoc.
      + eapply red_ctx_rel_red_context_rel => //.
        eapply All2_fold_mapi.
        eapply red_red_onctx; tea.
  - apply red_proj_c; eauto.
  - apply red_fix_congr; eauto.
    solve_all. eapply All_All2; tea; simpl; solve_all.
    rewrite subst_fix_context.
    specialize (b0 _ (Γ' ,,, subst_context s #|Γ'| (fix_context m)) Hsubs).
    now rewrite app_context_length subst_context_length app_context_assoc fix_context_length in b0.
  - apply red_cofix_congr; eauto.
    red in X. solve_all. eapply All_All2; tea; simpl; solve_all.
    rewrite subst_fix_context.
    specialize (b0 _ (Γ' ,,, subst_context s #|Γ'| (fix_context m)) Hsubs).
    now rewrite app_context_length subst_context_length app_context_assoc fix_context_length in b0.
Qed.

Lemma untyped_substitution_red {cf:checker_flags} Σ Γ Δ Γ' s M N :
  wf Σ -> untyped_subslet Γ s Δ ->
  red Σ (Γ ,,, Δ ,,, Γ') M N ->
  red Σ (Γ ,,, subst_context s 0 Γ') (subst s #|Γ'| M) (subst s #|Γ'| N).
Proof.
  intros HG Hs Hred. induction Hred; trea.
  - eapply substitution_untyped_let_red; eauto.
  - etransitivity; eauto.
Qed.

Notation subst_predicate s := (map_predicate_k id (subst s)).

(*
Fixpoint subst_stack s k π :=
  match π with
  | ε => ε
  | App u π =>
      let k' := #|stack_context π| + k in
      App (subst s k' u) (subst_stack s k π)
  | Fix mfix idx args π =>
      let k' := #|stack_context π| + k in
      let k'' := #|mfix| + k' in
      let mfix' := List.map (map_def (subst s k') (subst s k'')) mfix in
      Fix mfix' idx (map (subst s k') args) (subst_stack s k π)
  | Fix_mfix_ty na bo ra mfix1 mfix2 idx π =>
      let k' := #|stack_context π| + k in
      let k'' := #|mfix1| + S #|mfix2| + k' in
      let mfix1' := List.map (map_def (subst s k') (subst s k'')) mfix1 in
      let mfix2' := List.map (map_def (subst s k') (subst s k'')) mfix2 in
      Fix_mfix_ty na (subst s k'' bo) ra mfix1' mfix2' idx (subst_stack s k π)
  | Fix_mfix_bd na ty ra mfix1 mfix2 idx π =>
      let k' := #|stack_context π| + k in
      let k'' := #|mfix1| + S #|mfix2| + k' in
      let mfix1' := List.map (map_def (subst s k') (subst s k'')) mfix1 in
      let mfix2' := List.map (map_def (subst s k') (subst s k'')) mfix2 in
      Fix_mfix_bd na (subst s k' ty) ra mfix1' mfix2' idx (subst_stack s k π)
  | CoFix mfix idx args π =>
      let k' := #|stack_context π| + k in
      let k'' := #|mfix| + k' in
      let mfix' := List.map (map_def (subst s k') (subst s k'')) mfix in
      CoFix mfix' idx (map (subst s k') args) (subst_stack s k π)
  | CoFix_mfix_ty na bo ra mfix1 mfix2 idx π =>
      let k' := #|stack_context π| + k in
      let k'' := #|mfix1| + S #|mfix2| + k' in
      let mfix1' := List.map (map_def (subst s k') (subst s k'')) mfix1 in
      let mfix2' := List.map (map_def (subst s k') (subst s k'')) mfix2 in
      CoFix_mfix_ty na (subst s k'' bo) ra mfix1' mfix2' idx (subst_stack s k π)
  | CoFix_mfix_bd na ty ra mfix1 mfix2 idx π =>
      let k' := #|stack_context π| + k in
      let k'' := #|mfix1| + S #|mfix2| + k' in
      let mfix1' := List.map (map_def (subst s k') (subst s k'')) mfix1 in
      let mfix2' := List.map (map_def (subst s k') (subst s k'')) mfix2 in
      CoFix_mfix_bd na (subst s k' ty) ra mfix1' mfix2' idx (subst_stack s k π)
  | Case_pars ci pars1 pars2 pinst pctx pret c brs π =>
    let k' := #|stack_context π| + k in
    let brs' := map_branches_k (subst s) k' brs in
    Case_pars ci (map (subst s k') pars1) (map (subst s k') pars2)
      pinst 
      (subst_context s k' pctx)
      (subst s (#|pctx| + k') pret)
      (subst s k' c) brs' (subst_stack s k π)
  | Case_p ci pars pinst pctx c brs π =>
      let k' := #|stack_context π| + k in
      let brs' := map_branches_k (subst s) k' brs in
      Case_p ci (map (subst s k') pars) pinst 
        (subst_context s k' pctx)
        (subst s k' c) brs' (subst_stack s k π)
  | Case ci pred brs π =>
      let k' := #|stack_context π| + k in
      let brs' := map_branches_k (subst s) k' brs in
      Case ci (subst_predicate s k' pred) brs' (subst_stack s k π)
  | Case_brs ci pred c brctx brs1 brs2 π =>
      let k' := #|stack_context π| + k in
      let brs1' := map_branches_k (subst s) k' brs1 in
      let brs2' := map_branches_k (subst s) k' brs2 in
      Case_brs ci (subst_predicate s k' pred) (subst s k' c)
        (subst_context s k' brctx) brs1' brs2' (subst_stack s k π)
  | Proj p π =>
      Proj p (subst_stack s k π)
  | Prod_l na B π =>
      let k' := #|stack_context π| + k in
      Prod_l na (subst s (S k') B) (subst_stack s k π)
  | Prod_r na A π =>
      let k' := #|stack_context π| + k in
      Prod_r na (subst s k' A) (subst_stack s k π)
  | Lambda_ty na b π =>
      let k' := #|stack_context π| + k in
      Lambda_ty na (subst s (S k') b) (subst_stack s k π)
  | Lambda_tm na A π =>
      let k' := #|stack_context π| + k in
      Lambda_tm na (subst s k' A) (subst_stack s k π)
  | LetIn_bd na B u π =>
      let k' := #|stack_context π| + k in
      LetIn_bd na (subst s k' B) (subst s (S k') u) (subst_stack s k π)
  | LetIn_ty na b u π =>
      let k' := #|stack_context π| + k in
      LetIn_ty na (subst s k' b) (subst s (S k') u) (subst_stack s k π)
  | LetIn_in na b B π =>
      let k' := #|stack_context π| + k in
      LetIn_in na (subst s k' b) (subst s k' B) (subst_stack s k π)
  | coApp u π =>
      let k' := #|stack_context π| + k in
      coApp (subst s k' u) (subst_stack s k π)
  end.

Lemma subst_zipc :
  forall s k t π,
    let k' := #|stack_context π| + k in
    subst s k (zipc t π) =
    zipc (subst s k' t) (subst_stack s k π).
Proof.
  intros s k t π k'.
  induction π in s, k, t, k' |- *.
  all: try reflexivity.
  all: try solve [
    simpl ; rewrite IHπ ; cbn ; reflexivity
  ].
  - simpl. rewrite IHπ. cbn. f_equal.
    rewrite subst_mkApps. cbn. reflexivity.
  - simpl. rewrite IHπ. cbn. f_equal. f_equal.
    rewrite map_app. rewrite !app_length. cbn. reflexivity.
  - simpl. rewrite IHπ. cbn. f_equal. f_equal.
    rewrite map_app. rewrite !app_length. cbn. f_equal.
    unfold map_def at 1. cbn. f_equal.
    rewrite fix_context_alt_length.
    rewrite !app_length. cbn. rewrite !map_length.
    f_equal. f_equal. lia.
  - simpl. rewrite IHπ. cbn. f_equal. f_equal.
    rewrite subst_mkApps. cbn. reflexivity.
  - simpl. rewrite IHπ. cbn. f_equal. f_equal.
    rewrite map_app. rewrite !app_length. cbn. reflexivity.
  - simpl. rewrite IHπ. cbn. f_equal. f_equal.
    rewrite map_app. rewrite !app_length. cbn. f_equal.
    unfold map_def at 1. cbn. f_equal.
    rewrite fix_context_alt_length.
    rewrite !app_length. cbn. rewrite !map_length.
    f_equal. f_equal. lia.
  - simpl. rewrite IHπ. cbn. f_equal. f_equal.
    rewrite /map_predicate_k /= map_app.
    now rewrite mapi_context_fold.
  - simpl; rewrite IHπ; cbn. f_equal. f_equal.
    now rewrite /map_predicate_k /= mapi_context_fold; len.
  - simpl; rewrite IHπ; cbn; do 2 f_equal.
    rewrite map_app /=; len. do 2 f_equal.
    now rewrite /map_branch_k /= mapi_context_fold Nat.add_assoc.
Qed.
*)

(** The cumulativity relation is substitutive, yay! *)

Lemma substitution_untyped_cumul {cf:checker_flags} Σ Γ Γ' Γ'' s M N :
  wf Σ.1 -> untyped_subslet Γ s Γ' ->
  Σ ;;; Γ ,,, Γ' ,,, Γ'' |- M <= N ->
  Σ ;;; Γ ,,, subst_context s 0 Γ'' |- subst s #|Γ''| M <= subst s #|Γ''| N.
Proof.
  intros wfΣ Hs. induction 1.
  - constructor.
    now apply subst_leq_term.
  - eapply substitution_untyped_let_red in r. 3:eauto. all:eauto with wf.
    eapply red_cumul_cumul; eauto.
  - eapply substitution_untyped_let_red in r. 3:eauto. all:eauto with wf.
    eapply red_cumul_cumul_inv; eauto.
Qed.

Lemma substitution_cumul0 {cf:checker_flags} Σ Γ na t u u' a : wf Σ.1 ->
  Σ ;;; Γ ,, vass na t |- u <= u' ->
  Σ ;;; Γ |- subst10 a u <= subst10 a u'.
Proof.
  move=> wfΣ Hu.
  pose proof (substitution_untyped_cumul Σ Γ [vass na t] [] [a] u u' wfΣ).
  forward X.
  { constructor. constructor. }
  simpl in X. now apply X.
Qed.

Lemma substitution_cumul_let {cf:checker_flags} Σ Γ na t ty u u' : wf Σ.1 ->
  Σ ;;; Γ ,, vdef na t ty |- u <= u' ->
  Σ ;;; Γ |- subst10 t u <= subst10 t u'.
Proof.
  move=> wfΣ Hu.
  pose proof (substitution_untyped_cumul Σ Γ [vdef na t ty] [] [t] u u' wfΣ).
  forward X.
  { rewrite - {1}(subst_empty 0 t). constructor. constructor. }
  simpl in X. now apply X.
Qed.

(** The cumulativity relation is substitutive, yay! *)

Lemma substitution_cumul `{cf : checker_flags} (Σ : global_env_ext) Γ Γ' Γ'' s M N :
  wf Σ -> wf_local Σ (Γ ,,, Γ' ,,, Γ'') -> subslet Σ Γ s Γ' ->
  Σ ;;; Γ ,,, Γ' ,,, Γ'' |- M <= N ->
  Σ ;;; Γ ,,, subst_context s 0 Γ'' |- subst s #|Γ''| M <= subst s #|Γ''| N.
Proof.
  intros wfΣ wfΓ Hs. induction 1.
  - constructor.
    now apply subst_leq_term.
  - eapply substitution_let_red in r. 4:eauto. all:eauto with wf.
    eapply red_cumul_cumul; eauto.
  - eapply substitution_let_red in r. 4:eauto. all:eauto with wf.
    eapply red_cumul_cumul_inv; eauto.
Qed.

(** Old substitution lemma without lets *)
(*
Theorem substitution Σ Γ Γ' s Δ (t : term) T :
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
      rewrite -> nth_error_app_context_ge in H by lia.
      rewrite -> nth_error_app_context_lt in H by lia.
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
      rewrite H0 in Hs.
      assert (S n = #|s| + (S (n - #|s|))) by lia.
      rewrite H1. rewrite simpl_subst; auto; try lia.
      constructor; auto.
      rewrite -> nth_error_app_context_ge; try lia; rewrite subst_context_length.
      rewrite -> 2!nth_error_app_context_ge in H by lia.
      rewrite <- H. f_equal. lia.
      lia.

    + eapply subs_nth_error_lt in sub; eauto.
      rewrite H in sub. simpl in sub.
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
    rewrite !map_cst_type. eapply subst_declared_constant in H as ->; eauto.

  - eapply refine_type. econstructor; eauto.
    eapply on_declared_inductive in as isdecl [on_mind on_ind]; auto.
    apply onArity in on_ind as [[s' Hindty] _].
    apply typecheck_closed in Hindty as [_ Hindty]; eauto. symmetry.
    move/andb_and/proj1: Hindty. rewrite -(closedn_subst_instance _ _ u) => Hty.
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
    specialize (X4 Γ Γ' Δ s sub eq_refl wfsubs).
    simpl. econstructor.
    4:{ eapply subst_types_of_case in H0.
        simpl in H1. subst pars. rewrite firstn_map. eapply H0; eauto.
        all:eauto. }
    -- eauto.
    -- eauto.
    -- eauto.
    -- revert H1. subst pars.
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
    erewrite distr_subst_rec. simpl.
    rewrite map_rev. subst ty.
    f_equal.
    apply on_declared_projection in isdecl as [_ isdecl]; auto.
    eapply on_projection_closed in isdecl as clty; auto.
    symmetry. apply subst_closedn; eauto.
    rewrite List.rev_length H. eapply closed_upwards; eauto. lia.

  - assert (wf_local Σ (Γ ,,, subst_context s 0 Δ ,,, subst_context s #|Δ| (fix_context mfix))).
    subst types.
    apply All_local_env_app_inv in X as [X Hfixc].
    apply All_local_env_app. intuition.
    revert Hfixc. clear X0 X H.
    induction 1; simpl; auto.
    + destruct t0 as [u [Ht IHt]].
      specialize (IHt Γ Γ' (Δ ,,, Γ0) s sub). forward IHt. now rewrite app_context_assoc.
      rewrite app_context_length subst_context_app app_context_assoc Nat.add_0_r in IHt.
      unfold snoc; rewrite subst_context_snoc; econstructor; auto. exists u.
        apply IHt; apply All_local_env_app; intuition.
    + destruct t0 as [Ht IHt].
       specialize (IHt Γ Γ' (Δ ,,, Γ0) s sub). forward IHt. now rewrite app_context_assoc.
       rewrite app_context_length subst_context_app app_context_assoc Nat.add_0_r in IHt.
       unfold snoc; rewrite subst_context_snoc; econstructor; auto;
       apply IHt; apply All_local_env_app; intuition.
    + erewrite map_dtype. eapply type_Fix.
      * rewrite nth_error_map H. reflexivity.
      * now rewrite subst_fix_context.
      * rewrite subst_fix_context.
        apply All_map.
        clear X. eapply All_impl; eauto.
        clear X0. simpl; intros [na ty bod] [[Htyd Hlam] IH].
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
    apply All_local_env_app_inv in X as [X Hfixc].
    apply All_local_env_app. intuition.
    revert Hfixc. clear X0 X H.
    induction 1; simpl; auto.
    + destruct t0 as [u [Ht IHt]].
      specialize (IHt Γ Γ' (Δ ,,, Γ0) s sub). forward IHt. now rewrite app_context_assoc.
      rewrite app_context_length subst_context_app app_context_assoc Nat.add_0_r in IHt.
      unfold snoc; rewrite subst_context_snoc; econstructor; auto. exists u.
        apply IHt; apply All_local_env_app; intuition.
    + destruct t0 as [Ht IHt].
       specialize (IHt Γ Γ' (Δ ,,, Γ0) s sub). forward IHt. now rewrite app_context_assoc.
       rewrite app_context_length subst_context_app app_context_assoc Nat.add_0_r in IHt.
       unfold snoc; rewrite subst_context_snoc; econstructor; auto;
       apply IHt; apply All_local_env_app; intuition.
    + erewrite map_dtype. eapply type_CoFix.
      * rewrite nth_error_map H. reflexivity.
      * now rewrite subst_fix_context.
      * rewrite subst_fix_context.
        apply All_map.
        clear X. eapply All_impl; eauto.
        clear X0. simpl; intros [na ty bod] [Htyd IH].
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
    destruct X2 as [Bs|[u Hu]].
    + left. destruct Bs as [[ctx [u [Hd IH]]]]. simpl in *.
      exists (subst_context s #|Δ| ctx), u.
      pose proof (subst_destArity [] B s #|Δ|). rewrite Hd in H.
      rewrite H. clear H.
      split; auto.
      apply All_local_env_app; intuition auto.
      clear -sub wfsubs a.
      induction ctx; try constructor; depelim a.
      -- rewrite subst_context_snoc.
         unfold snoc. unfold vass, snoc in H. noconf H.
         econstructor; auto.
         eapply IHctx. eapply a.
         simpl. destruct tu as [u tu]. exists u.
         specialize (t0 _ _ (Δ ,,, ctx) _ sub). forward t0.
         now rewrite app_context_assoc. simpl in t0.
         forward t0. rewrite subst_context_app app_context_assoc Nat.add_0_r.
         apply All_local_env_app. split; auto.
         eapply IHctx. eapply a.
         now rewrite subst_context_app Nat.add_0_r app_context_assoc app_length in t0.
      -- rewrite subst_context_snoc.
         unfold vdef, snoc in H |- *. noconf H.
         constructor; auto.
         eapply IHctx. eapply a.
         simpl.
         specialize (t0 _ _ (Δ ,,, ctx) _ sub). forward t0.
         now rewrite app_context_assoc. simpl in t0.
         forward t0. rewrite subst_context_app app_context_assoc Nat.add_0_r.
         apply All_local_env_app. split; auto.
         eapply IHctx. eapply a.
         now rewrite subst_context_app Nat.add_0_r app_context_assoc app_length in t0.
    + right; exists u; intuition eauto.
    + eapply substitution_cumul; eauto.
Qed.
*)

Lemma usubst_well_subst {cf} Σ Γ σ Δ : 
  usubst Γ σ Δ ->
  (forall x decl, nth_error Γ x = Some decl -> 
    Σ ;;; Δ |- σ x : (decl.(decl_type)).[↑^(S x) ∘s σ]) ->
  well_subst Σ Γ σ Δ.
Proof.
  intros us hty.
  intros x decl hnth.
  split.
  * specialize (hty x decl hnth).
    now sigma.
  * apply (us x decl hnth).
Qed.

Lemma subslet_well_subst {cf} {Σ} {wfΣ : wf Σ} {Γ Γ' s Δ} : 
  subslet Σ Γ s Γ' ->
  wf_local Σ (Γ ,,, subst_context s 0 Δ) ->
  well_subst Σ (Γ ,,, Γ' ,,, Δ) (⇑^#|Δ| (s ⋅n ids)) (Γ ,,, subst_context s 0 Δ).
Proof.
  intros hs hsΔ.
  apply usubst_well_subst.
  * apply (subslet_usubst hs).
  * intros x decl.
    case: nth_error_app_context => //.
    { intros d hnth hn [= ->].
      rewrite {1}Upn_eq subst_consn_lt'; len => //. rewrite /subst_fn.
      rewrite idsn_lt //.
      eapply meta_conv.
      - econstructor; auto.
        rewrite nth_error_app_lt; len => //.
        now rewrite nth_error_subst_context hnth.
      - rewrite /subst_decl. simpl. 
        rewrite lift0_inst !subst_inst_aux Nat.add_0_r.
        sigma. rewrite -shiftk_shift -subst_compose_assoc -shiftk_shift.
        rewrite subst_shift_comm.
        rewrite -subst_fn_subst_consn. lia_f_equal. }
    { intros n hnth; len; intros hd [= ->].
      pose proof (subslet_length hs).
      move: hnth; case: nth_error_app_context => //.
      * intros n hnth hx [= ->].
        rewrite {1}Upn_eq subst_consn_ge; len => //; try lia.
        rewrite subst_consn_compose.
        rewrite subst_consn_lt'; len; try lia.
        unfold subst_fn. rewrite nth_error_map.
        destruct (subslet_nth_error hs hnth) as [t [hnths [hty hb]]].
        rewrite hnths /=. sigma in hty.
        eapply meta_conv in hty.
        2:now rewrite skipn_subst ?Upn_0; try lia.
        eapply (shift_typing (Δ := subst_context s 0 Δ)) in hty.
        2:tas.
        2:now len.
        rewrite inst_assoc in hty.
        rewrite Upn_eq.
        eapply meta_conv; eauto.
        eapply inst_ext.
        rewrite (shift_subst_consn_ge (S x)); len; try lia.
        rewrite subst_compose_assoc.
        now replace (S x - #|Δ|) with (S (x - #|Δ|)) by lia.
      * intros n hnth hn [= ->].
        eapply meta_conv_all.
        2:reflexivity.
        2:{ rewrite Upn_subst_consn_ge; try lia. rewrite compose_ids_l.
            instantiate (1 := tRel (x - #|s|)).
            rewrite /shiftk. lia_f_equal. }
        2:{ econstructor; eauto. }
        eapply meta_conv.
        { econstructor; tas.
          rewrite nth_error_app_context_ge; len; try lia.
          rewrite H. erewrite <- hnth. lia_f_equal. }
        rewrite lift0_inst.
        rewrite Upn_eq.
        rewrite shift_subst_consn_ge; len; try lia.
        rewrite subst_consn_compose shift_subst_consn_ge; len; try lia.
        rewrite H. rewrite shiftk_compose. lia_f_equal.
    }
Qed.

Lemma All_local_env_inst {cf} {Σ} {wfΣ : wf Σ} {Γ0 Γ' Δ s} :
  All_local_env
    (lift_typing
      (fun (Σ : global_env_ext) (Γ : context) (t T : term) =>
        forall (Δ : PCUICEnvironment.context) (σ : nat -> term),
        wf_local Σ Δ -> well_subst Σ Γ σ Δ -> Σ;;; Δ |- t.[σ] : T.[σ]) Σ)
    (Γ0,,, Γ',,, Δ) ->
  wf_local Σ Γ0 ->
  subslet Σ Γ0 s Γ' ->
  wf_local Σ (Γ0,,, subst_context s 0 Δ).
Proof.
  intros HΓ HΓ0 sub.
  rewrite subst_context_inst_context.
  eapply (wf_local_app_inst _ (Γ0 ,,, Γ')); eauto.
  * now eapply All_local_env_app_inv in HΓ as [].
  * eapply (subslet_well_subst (Δ:=[])) in sub;
    rewrite ?subst_context_nil in sub |- *.
    + apply sub.
    + pcuicfo. 
Qed.

Theorem substitution_prop `{cf : checker_flags} : env_prop
  (fun Σ Γ0 t T =>
  forall (Γ Γ' Δ : context) (s : list term)
    (sub : subslet Σ Γ s Γ') (eqΓ0 : Γ0 = Γ ,,, Γ' ,,, Δ),
    wf_local Σ (Γ ,,, subst_context s 0 Δ) ->
    Σ ;;; Γ ,,, subst_context s 0 Δ |- subst s #|Δ| t : subst s #|Δ| T)
  (fun Σ Γ0 =>
    forall (Γ Γ' Δ : context) (s : list term)
    (sub : subslet Σ Γ s Γ') (eqΓ0 : Γ0 = Γ ,,, Γ' ,,, Δ),
    wf_local Σ (Γ ,,, subst_context s 0 Δ)).
Proof.
  intros Σ wfΣ Γ t T HT.
  pose proof (type_inst Σ wfΣ Γ t T HT) as [HΣ [HΓ HTy]].
  intuition auto.
  3:{
    subst Γ.
    rewrite !subst_inst. eapply HTy => //.
    eapply subslet_well_subst; eauto. }
  2:{ subst Γ.
      eapply typing_wf_local in HT.
      eapply wf_local_app_inv in HT as [HΓ0 _].
      eapply wf_local_app_inv in HΓ0 as [HΓ0 _].
      eapply All_local_env_inst; eauto. }
  unshelve eapply on_wf_global_env_impl ; tea.
  clear. intros * HΣ HP HQ.
  apply lift_typing_impl. clear -HΣ HP.
  intros. subst Γ.
  rewrite !subst_inst. eapply X => //.
  now unshelve eapply subslet_well_subst.
Qed.

Corollary substitution `{cf : checker_flags} (Σ : global_env_ext) Γ Γ' s Δ (t : term) T :
  wf Σ -> subslet Σ Γ s Γ' ->
  Σ ;;; Γ ,,, Γ' ,,, Δ |- t : T ->
  Σ ;;; Γ ,,, subst_context s 0 Δ |- subst s #|Δ| t : subst s #|Δ| T.
Proof.
  intros HΣ Hs Ht.
  eapply (env_prop_typing _ _ substitution_prop); trea.
  eapply (env_prop_wf_local _ _ substitution_prop); trea.
  now eapply typing_wf_local in Ht.
Qed.

Corollary substitution_wf_local `{cf : checker_flags} (Σ : global_env_ext) Γ Γ' s Δ :
  wf Σ -> subslet Σ Γ s Γ' ->
  wf_local Σ (Γ ,,, Γ' ,,, Δ) ->
  wf_local Σ (Γ ,,, subst_context s 0 Δ).
Proof.
  intros HΣ Hs Ht.
  eapply (env_prop_wf_local _ _ substitution_prop); trea.
Qed.

Lemma substitution0 {cf:checker_flags} (Σ : global_env_ext) Γ n u U (t : term) T :
  wf Σ ->
  Σ ;;; Γ ,, vass n U |- t : T -> Σ ;;; Γ |- u : U ->
  Σ ;;; Γ |- t {0 := u} : T {0 := u}.
Proof.
  intros HΣ Ht Hu.
  assert (wfΓ : wf_local Σ Γ).
  { apply typing_wf_local in Hu; eauto. }
  pose proof (substitution Σ Γ [vass n U] [u] [] t T HΣ) as thm.
  forward thm.
  { constructor.
    - constructor.
    - rewrite subst_empty; auto.
  }
  now apply (thm Ht).
Qed.

Lemma substitution_let {cf:checker_flags} (Σ : global_env_ext) Γ n u U (t : term) T :
  wf Σ ->
  Σ ;;; Γ ,, vdef n u U |- t : T ->
  Σ ;;; Γ |- t {0 := u} : T {0 := u}.
Proof.
  intros HΣ Ht.
  assert ((wf_local Σ Γ) * (Σ ;;; Γ |- u : U)%type) as [wfΓ tyu].
  { apply typing_wf_local in Ht; eauto with wf.
    now depelim Ht; simpl in *.
  }
  epose proof (substitution Σ Γ [vdef n u U] _ [] t T HΣ) as thm.
  forward thm.
  { constructor.
    - constructor.
    - rewrite !subst_empty; auto.
  }
  simpl in thm.
  specialize (thm Ht). now rewrite !subst_empty in thm.
Qed.
