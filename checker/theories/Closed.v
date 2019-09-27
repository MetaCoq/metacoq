(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega Lia.
From MetaCoq.Template Require Import config utils Ast AstUtils Induction utils LiftSubst.
From MetaCoq.Checker Require Import Typing TypingWf WeakeningEnv.
Require Import ssreflect ssrbool.

Definition closed_decl n d :=
  option_default (closedn n) d.(decl_body) true && closedn n d.(decl_type).

Definition closed_ctx ctx :=
  forallb id (mapi (fun k d => closed_decl k d) (List.rev ctx)).

(** * Lemmas about the [closedn] predicate *)

Lemma closedn_lift n k k' t : closedn k t -> closedn (k + n) (lift n k' t).
Proof.
  revert k.
  induction t in n, k' |- * using term_forall_list_ind; intros;
    simpl in *; rewrite -> ?andb_and in *;
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length, ?Nat.add_assoc;
    simpl closed in *; solve_all;
    unfold compose, test_def, test_snd in *;
      try solve [simpl lift; simpl closed; f_equal; auto; repeat (toProp; solve_all)]; try easy.

  - elim (Nat.leb_spec k' n0); intros. simpl.
    elim (Nat.ltb_spec); auto. apply Nat.ltb_lt in H. lia.
    simpl. elim (Nat.ltb_spec); auto. intros.
    apply Nat.ltb_lt in H. lia.
Qed.

Lemma closedn_lift_inv n k k' t : k <= k' ->
                                   closedn (k' + n) (lift n k t) ->
                                   closedn k' t.
Proof.
  induction t in n, k, k' |- * using term_forall_list_ind; intros;
    simpl in *;
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length, ?Nat.add_assoc in *;
    simpl closed in *; repeat (toProp; solve_all); try change_Sk;
    unfold compose, test_def, on_snd, test_snd in *; simpl in *; eauto with all.

  - revert H0.
    elim (Nat.leb_spec k n0); intros. simpl in *.
    elim (Nat.ltb_spec); auto. apply Nat.ltb_lt in H1. intros. lia.
    revert H1. simpl. elim (Nat.ltb_spec); auto. intros. apply Nat.ltb_lt. lia.
  - specialize (IHt2 n (S k) (S k')). eauto with all.
  - specialize (IHt2 n (S k) (S k')). eauto with all.
  - specialize (IHt3 n (S k) (S k')). eauto with all.
  - toProp. solve_all. specialize (H1 n (#|m| + k) (#|m| + k')). eauto with all.
  - toProp. solve_all. specialize (H1 n (#|m| + k) (#|m| + k')). eauto with all.
Qed.

Lemma closedn_mkApps k f u:
  closedn k f -> forallb (closedn k) u ->
  closedn k (mkApps f u).
Proof.
  intros Hf Hu.
  induction u; simpl; auto.
  destruct f; simpl in *; try rewrite Hf Hu; auto.
  rewrite forallb_app. simpl. rewrite Hu.
  rewrite andb_assoc. now rewrite Hf.
Qed.

Lemma closedn_mkApps_inv k f u:
  closedn k (mkApps f u) ->
  closedn k f && forallb (closedn k) u.
Proof.
  induction u; simpl; auto.
  - now rewrite andb_true_r.
  - intros. destruct f; simpl in *; auto.
    rewrite forallb_app in H. simpl in H.
    now rewrite andb_assoc in H.
Qed.

Lemma closedn_subst s k k' t :
  forallb (closedn k) s -> closedn (k + k' + #|s|) t ->
  closedn (k + k') (subst s k' t).
Proof.
  intros Hs. solve_all. revert H.
  induction t in k' |- * using term_forall_list_ind; intros;
    simpl in *;
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length;
    simpl closed in *; try change_Sk; repeat (toProp; solve_all);
    unfold compose, test_def, on_snd, test_snd in *; simpl in *; eauto with all.

  - elim (Nat.leb_spec k' n); intros. simpl.
    apply Nat.ltb_lt in H.
    destruct nth_error eqn:Heq.
    -- eapply closedn_lift.
       now eapply nth_error_all in Heq; simpl; eauto; simpl in *.
    -- simpl. elim (Nat.ltb_spec); auto. intros.
       apply nth_error_None in Heq. lia.
    -- simpl. apply Nat.ltb_lt in H0.
       apply Nat.ltb_lt. apply Nat.ltb_lt in H0. lia.

  - specialize (IHt2 (S k')).
    rewrite <- Nat.add_succ_comm in IHt2. eauto.
  - specialize (IHt2 (S k')).
    rewrite <- Nat.add_succ_comm in IHt2. eauto.
  - specialize (IHt3 (S k')).
    rewrite <- Nat.add_succ_comm in IHt3. eauto.
  - rewrite closedn_mkApps; solve_all.
  - toProp; solve_all. rewrite -> !Nat.add_assoc in *.
    specialize (H0 (#|m| + k')). unfold is_true. rewrite <- H0. f_equal. lia.
    unfold is_true. rewrite <- H2. f_equal. lia.
  - toProp; solve_all. rewrite -> !Nat.add_assoc in *.
    specialize (H0 (#|m| + k')). unfold is_true. rewrite <- H0. f_equal. lia.
    unfold is_true. rewrite <- H2. f_equal. lia.
Qed.

Lemma closedn_subst0 s k t :
  forallb (closedn k) s -> closedn (k + #|s|) t ->
  closedn k (subst0 s t).
Proof.
  intros.
  generalize (closedn_subst s k 0 t H).
  rewrite Nat.add_0_r. eauto.
Qed.

Lemma subst_closedn s k t : Ast.wf t ->
  closedn k t -> subst s k t = t.
Proof.
  intros Hcl.
  pose proof (simpl_subst_rec _ Hcl s 0 k k).
  intros. pose proof (lift_closed (#|s| + 0) _ _ H0).
  do 2 (forward H; auto). rewrite H1 in H.
  rewrite H. now apply lift_closed.
Qed.

Lemma closedn_subst_instance_constr k t u :
  closedn k (UnivSubst.subst_instance_constr u t) = closedn k t.
Proof.
  revert k.
  induction t in |- * using term_forall_list_ind; intros;
    simpl in *; rewrite -> ?andb_and in *;
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def;
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

Require Import ssreflect.


Lemma destArity_spec ctx T :
  match destArity ctx T with
  | Some (ctx', s) => it_mkProd_or_LetIn ctx T = it_mkProd_or_LetIn ctx' (tSort s)
  | None => True
  end.
Proof.
  induction T in ctx |- *; simpl; simplify_dep_elim; try easy.
  specialize (IHT2 (ctx,, vass na T1)). now destruct destArity.
  specialize (IHT3 (ctx,, vdef na T1 T2)). now destruct destArity.
Qed.

Definition closedn_ctx n ctx :=
  forallb id (mapi (fun k d => closed_decl (n + k) d) (List.rev ctx)).

Lemma closedn_ctx_cons n d Γ : closedn_ctx n (d :: Γ) -> closedn_ctx n Γ && closed_decl (n + #|Γ|) d.
Proof.
  unfold closedn_ctx.
  simpl. rewrite mapi_app. rewrite forallb_app.
  move/andP => [] -> /=. now rewrite Nat.add_0_r List.rev_length andb_true_r.
Qed.

Lemma closedn_ctx_app n Γ Γ' :
  closedn_ctx n (Γ ,,, Γ') =
  closedn_ctx n Γ && closedn_ctx (n + #|Γ|) Γ'.
Proof.
  rewrite /closedn_ctx /app_context /= List.rev_app_distr mapi_app forallb_app /=.
  bool_congr.
  rewrite List.rev_length.
  f_equal. eapply mapi_ext. intros.
  f_equal. lia.
Qed.

Lemma closedn_All_local_closed:
  forall (cf : checker_flags) (Σ : global_env_ext) (ctx : list context_decl)
         (wfΓ' : wf_local Σ ctx),
    All_local_env_over typing
    (fun (Σ0 : global_env_ext) (Γ0 : context) (_ : wf_local Σ0 Γ0) (t T : term) (_ : Σ0;;; Γ0 |- t : T) =>
       closedn #|Γ0| t && closedn #|Γ0| T) Σ ctx wfΓ' ->
    closedn_ctx 0 ctx.
Proof.
  intros cf Σ Γ al.
  induction 1. constructor.
  rewrite /closedn_ctx /= mapi_app forallb_app /= [forallb _ _]IHX /id /closed_decl /=.
  now rewrite Nat.add_0_r List.rev_length p.
  rewrite /closedn_ctx /= mapi_app forallb_app /= [forallb _ _]IHX /id /closed_decl /=.
  now rewrite Nat.add_0_r List.rev_length p.
Qed.

Lemma closedn_mkProd_or_LetIn (Γ : context) d T :
    closed_decl #|Γ| d ->
    closedn (S #|Γ|) T -> closedn #|Γ| (mkProd_or_LetIn d T).
Proof.
  destruct d as [na [b|] ty]; simpl in *. unfold closed_decl.
  simpl. now move/andP => [] -> ->.
  simpl. now move/andP => [] /= _ -> ->.
Qed.

Lemma closedn_mkLambda_or_LetIn (Γ : context) d T :
    closed_decl #|Γ| d ->
    closedn (S #|Γ|) T -> closedn #|Γ| (mkLambda_or_LetIn d T).
Proof.
  destruct d as [na [b|] ty]; simpl in *. unfold closed_decl.
  simpl. now move/andP => [] -> ->.
  simpl. now move/andP => [] /= _ -> ->.
Qed.

Lemma closedn_it_mkProd_or_LetIn
      (Γ : context) (ctx : list context_decl) T :
    closedn_ctx #|Γ| ctx ->
    closedn (#|Γ| + #|ctx|) T -> closedn #|Γ| (it_mkProd_or_LetIn ctx T).
Proof.
  induction ctx in Γ, T |- *. simpl.
  - now rewrite Nat.add_0_r.
  - move/closedn_ctx_cons/andP => [] cctx ca cT.
    apply (IHctx Γ (mkProd_or_LetIn a T) cctx).
    simpl in cT. rewrite <- app_length.
    eapply closedn_mkProd_or_LetIn;
      now rewrite app_length // plus_n_Sm.
Qed.

Lemma closedn_it_mkLambda_or_LetIn
      (Γ : context) (ctx : list context_decl) T :
    closedn_ctx #|Γ| ctx ->
    closedn (#|Γ| + #|ctx|) T -> closedn #|Γ| (it_mkLambda_or_LetIn ctx T).
Proof.
  induction ctx in Γ, T |- *. simpl.
  - now rewrite Nat.add_0_r.
  - move/closedn_ctx_cons/andP => [] cctx ca cT.
    apply (IHctx Γ (mkLambda_or_LetIn a T) cctx).
    simpl in cT. rewrite <- app_length.
    eapply closedn_mkLambda_or_LetIn;
      now rewrite app_length // plus_n_Sm.
Qed.

Lemma typecheck_closed `{cf : checker_flags} :
  env_prop (fun Σ Γ t T =>
              closedn #|Γ| t && closedn #|Γ| T).
Proof.
  assert(weaken_env_prop (lift_typing (fun (_ : global_env_ext) (Γ : context) (t T : term) =>
                                         closedn #|Γ| t && closedn #|Γ| T))).
  { repeat red. intros. destruct t; red in X0; eauto. }

  apply typing_ind_env; intros; simpl; rewrite -> ?andb_and in *; try solve [intuition auto].
  - pose proof (nth_error_Some_length H).
    elim (Nat.ltb_spec n #|Γ|); intuition. clear H0.
    eapply (nth_error_All_local_env_over H) in X0 as [HΓ Hdecl].
    destruct lookup_wf_local_decl; cbn in *.
    destruct decl as [na [b|] ty]; cbn in *.
    -- move/andb_and: Hdecl => [] _.
       rewrite skipn_length; try lia.
       move/(closedn_lift (S n)).
       now have->: #|Γ| - S n + S n = #|Γ| by lia.
    -- rewrite andb_true_r in Hdecl.
       move/(closedn_lift (S n)): Hdecl.
       rewrite skipn_length; try lia.
       now have->: #|Γ| - S n + S n = #|Γ| by lia.

  - destruct H. rewrite and_assoc. split. auto.
    clear X0 H H0 H1.
    induction X1; simpl. intuition auto.
    rewrite -> andb_and in *. destruct p0. rewrite H.
    rewrite <- andb_and. simpl.
    apply IHX1. unfold subst.
    pose proof (closedn_subst [hd] #|Γ| 0). rewrite Nat.add_0_r in H1.
    apply H1. simpl. now rewrite H.
    simpl. simpl in p. rewrite -> andb_and in p. intuition auto.
    rewrite Nat.add_1_r. auto.

  - rewrite closedn_subst_instance_constr.
    eapply lookup_on_global_env in H; eauto.
    destruct H as [Σ' [HΣ' IH]].
    repeat red in IH. destruct decl, cst_body. simpl in *.
    rewrite -> andb_and in IH. intuition.
    eauto using closed_upwards with arith.
    simpl in *.
    repeat red in IH. destruct IH as [s Hs].
    rewrite -> andb_and in Hs. intuition.
    eauto using closed_upwards with arith.


  - rewrite closedn_subst_instance_constr.
    eapply declared_inductive_inv in X0; eauto.
    apply onArity in X0. repeat red in X0.
    destruct X0 as [s Hs]. rewrite -> andb_and in Hs.
    intuition eauto using closed_upwards with arith.

  - destruct isdecl as [Hidecl Hcdecl].
    eapply declared_inductive_inv in X0; eauto.
    apply onConstructors in X0. repeat red in X0.
    eapply nth_error_alli in Hcdecl; eauto.
    repeat red in Hcdecl.
    destruct Hcdecl as [[s Hs] _]. rewrite -> andb_and in Hs.
    destruct Hs as [Hdecl _].
    unfold type_of_constructor.
    apply closedn_subst0.
    unfold inds. clear. simpl. induction #|ind_bodies mdecl|. constructor.
    simpl. now rewrite IHn.
    rewrite inds_length. unfold arities_context in Hdecl.
    rewrite rev_map_length in Hdecl.
    rewrite closedn_subst_instance_constr.
    eauto using closed_upwards with arith.

  - intuition auto. solve_all. unfold test_snd. simpl in *.
    toProp; eauto.
    apply closedn_mkApps; auto.
    rewrite forallb_app. simpl. rewrite H3.
    rewrite forallb_skipn; auto.
    now apply closedn_mkApps_inv in H7.

  - intuition auto.
    apply closedn_subst0.
    simpl. apply closedn_mkApps_inv in H2.
    rewrite forallb_rev H1. apply H2.
    rewrite closedn_subst_instance_constr.
    eapply declared_projection_inv in isdecl as H'; eauto.
    apply on_declared_projection in isdecl as [[Hmdecl Hidecl] Hpdecl]; auto.
    red in Hpdecl.
    destruct Hpdecl as [s Hs]. simpl in *.
    apply onNpars in Hmdecl.
    cbn in H'; destruct H'.
    simpl in *.
    rewrite List.rev_length H0.
    rewrite andb_true_r in i. rewrite <- Hmdecl.
    rewrite smash_context_length in i. simpl in i.
    eapply closed_upwards; eauto. lia.

  - split. solve_all.
    destruct x; simpl in *.
    unfold test_def. simpl. toProp.
    split.
    rewrite -> app_context_length in *. rewrite -> Nat.add_comm in *.
    eapply closedn_lift_inv in H2; eauto. lia.
    subst types.
    now rewrite app_context_length fix_context_length in H1.
    eapply nth_error_all in H0; eauto. simpl in H0. intuition. toProp.
    subst types. rewrite app_context_length in H1.
    rewrite Nat.add_comm in H1.
    now eapply closedn_lift_inv in H1.

  - split. solve_all. destruct x; simpl in *.
    unfold test_def. simpl. toProp.
    split.
    rewrite -> app_context_length in *. rewrite -> Nat.add_comm in *.
    eapply closedn_lift_inv in H2; eauto. lia.
    subst types.
    now rewrite -> app_context_length, fix_context_length in H1.
    eapply (nth_error_all) in H; eauto. simpl in *.
    intuition. toProp.
    subst types. rewrite app_context_length in H1.
    rewrite Nat.add_comm in H1.
    now eapply closedn_lift_inv in H1.

  - destruct X2; intuition eauto.
    + destruct i as [[u [ctx [Heq Hi]]] Hwfi]. simpl in Hwfi.
      generalize (destArity_spec [] B). rewrite Heq.
      simpl; intros ->.
      apply closedn_All_local_closed in Hwfi.
      rewrite closedn_ctx_app in Hwfi.
      move/andP: Hwfi => [] clΓ clctx.
      apply closedn_it_mkProd_or_LetIn => //.
    + destruct s. rewrite andb_true_r in p. intuition auto.
Qed.


Lemma declared_decl_closed `{checker_flags} (Σ : global_env) cst decl :
  wf Σ ->
  lookup_env Σ cst = Some decl ->
  on_global_decl (fun Σ Γ b t =>
                    match t with Some t => Ast.wf t | None => True end /\ Ast.wf b /\
                    closedn #|Γ| b && option_default (closedn #|Γ|) t true)
                 (Σ, universes_decl_of_decl decl) decl.
Proof.
  intros.
  eapply weaken_lookup_on_global_env; try red; eauto.
  eapply on_global_env_impl; cycle 1.
  eapply on_global_env_mix.
  2:apply (env_prop_sigma _ typecheck_closed _ X).
  2:apply (env_prop_sigma _ typing_wf_gen _ X).
  red; intros. unfold lift_typing in *. destruct b; intuition auto with wf.
  destruct X0 as [s0 Hs0]. exists s0. intuition auto with wf.
  intros.
  simpl in X1. destruct X1 as [Hcl Hwf]. red in Hcl, Hwf.
  destruct T; simpl; intuition auto.
  destruct Hwf; simpl; intuition auto.
  destruct Hwf; simpl; intuition auto.
  destruct Hcl; simpl; intuition auto.
Qed.

Require Import ssreflect ssrbool.
Lemma closed_decl_upwards k d : closed_decl k d -> forall k', k <= k' -> closed_decl k' d.
Proof.
  case: d => na [body|] ty; rewrite /closed_decl /=.
  move/andP => [cb cty] k' lek'. do 2 rewrite (@closed_upwards k) //.
  move=> cty k' lek'; rewrite (@closed_upwards k) //.
Qed.
