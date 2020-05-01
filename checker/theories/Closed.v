(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool List Program ZArith Lia.
From MetaCoq.Template Require Import config utils Ast AstUtils Induction
  LiftSubst UnivSubst Typing TypingWf.
From MetaCoq.Checker Require Import Reflect WeakeningEnv.
Require Import ssreflect.

From Equations Require Import Equations.

(** * Lemmas about the [closedn] predicate *)

Definition closed_decl n d :=
  option_default (closedn n) d.(decl_body) true && closedn n d.(decl_type).

Definition closedn_ctx n ctx :=
  forallb id (mapi (fun k d => closed_decl (n + k) d) (List.rev ctx)).

Lemma closed_decl_upwards k d : closed_decl k d -> forall k', k <= k' -> closed_decl k' d.
Proof.
  case: d => na [body|] ty; rewrite /closed_decl /=.
  move/andP => [cb cty] k' lek'. do 2 rewrite (@closed_upwards k) //.
  move=> cty k' lek'; rewrite (@closed_upwards k) //.
Qed.
  
Notation closed_ctx ctx := (closedn_ctx 0 ctx).

Lemma closedn_lift n k k' t : closedn k t -> closedn (k + n) (lift n k' t).
Proof.
  revert k.
  induction t in n, k' |- * using term_forall_list_ind; intros;
    simpl in *; rewrite -> ?andb_and in *;
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length, ?Nat.add_assoc;
    simpl closed in *; solve_all;
    unfold compose, test_def, test_snd in *;
      try solve [simpl lift; simpl closed; f_equal; auto; repeat (rtoProp; solve_all)]; try easy.

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
    simpl closed in *; repeat (rtoProp; solve_all); try change_Sk;
    unfold compose, test_def, on_snd, test_snd in *; simpl in *; eauto with all.

  - revert H0.
    elim (Nat.leb_spec k n0); intros. simpl in *.
    elim (Nat.ltb_spec); auto. apply Nat.ltb_lt in H1. intros. lia.
    revert H1. simpl. intro. repeat toProp. lia.
  - specialize (IHt2 n (S k) (S k')). eauto with all.
  - specialize (IHt2 n (S k) (S k')). eauto with all.
  - specialize (IHt3 n (S k) (S k')). eauto with all.
  - rtoProp. solve_all. specialize (b0 n (#|m| + k) (#|m| + k')). eauto with all.
  - rtoProp. solve_all. specialize (b0 n (#|m| + k) (#|m| + k')). eauto with all.
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
    simpl closed in *; try change_Sk; repeat (rtoProp; solve_all);
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
  - rtoProp; solve_all. rewrite -> !Nat.add_assoc in *.
    specialize (b0 (#|m| + k')). unfold is_true. rewrite <- b0. f_equal. lia.
    unfold is_true. rewrite <- H0. f_equal. lia.
  - rtoProp; solve_all. rewrite -> !Nat.add_assoc in *.
    specialize (b0 (#|m| + k')). unfold is_true. rewrite <- b0. f_equal. lia.
    unfold is_true. rewrite <- H0. f_equal. lia.
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
  closedn k (subst_instance_constr u t) = closedn k t.
Proof.
  revert k.
  induction t in |- * using term_forall_list_ind; intros;
    simpl in *; rewrite -> ?andb_and in *;
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def;
    try solve [repeat (f_equal; eauto)];  simpl closed in *;
      try rewrite ?map_length; intuition auto.

  - rewrite forallb_map; eapply Forall_forallb_eq_forallb; eauto.
  - rewrite forallb_map. f_equal; eauto using Forall_forallb_eq_forallb.
  - red in X. rewrite forallb_map. f_equal.
    + f_equal; auto.
    + eapply Forall_forallb_eq_forallb.
      eapply All_Forall; tea.
      intros [] XX; apply XX.
  - red in X. rewrite forallb_map.
    eapply Forall_forallb_eq_forallb. eapply All_Forall; eauto.
    unfold test_def, compose, map_def. simpl.
    do 3 (f_equal; intuition eauto).
  - red in X. rewrite forallb_map.
    eapply Forall_forallb_eq_forallb. eapply All_Forall; eauto.
    unfold test_def, compose, map_def. simpl.
    do 3 (f_equal; intuition eauto).
Qed.



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
  f_equal.
  rewrite List.rev_length.
  f_equal. eapply mapi_ext. intros.
  f_equal. lia.
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
 
Lemma type_local_ctx_All_local_env {cf:checker_flags} P Σ Γ Δ s : 
  All_local_env (lift_typing P Σ) Γ ->
  type_local_ctx (lift_typing P) Σ Γ Δ s ->
  All_local_env (lift_typing P Σ) (Γ ,,, Δ).
Proof.
  induction Δ; simpl; auto.
  destruct a as [na [b|] ty];
  intros wfΓ wfctx; constructor; intuition auto.
   exists s; auto.
Qed.

Definition Pclosed :=
  (fun (_ : global_env_ext) (Γ : context) (t T : term) =>
           closedn #|Γ| t && closedn #|Γ| T).

Lemma type_local_ctx_Pclosed Σ Γ Δ s :
  type_local_ctx (lift_typing Pclosed) Σ Γ Δ s ->
  Alli (fun i d => closed_decl (#|Γ| + i) d) 0 (List.rev Δ).
Proof.
  induction Δ; simpl; auto; try constructor.  
  destruct a as [? [] ?]; intuition auto.
  - apply Alli_app_inv; auto. constructor. simpl.
    rewrite List.rev_length. 2:constructor.
    unfold closed_decl. unfold Pclosed in b0. simpl.
    rewrite app_context_length in b0. now rewrite Nat.add_comm.
  - apply Alli_app_inv; auto. constructor. simpl.
    rewrite List.rev_length. 2:constructor.
    unfold closed_decl. unfold Pclosed in b. simpl.
    rewrite app_context_length in b. rewrite Nat.add_comm.
    now rewrite andb_true_r in b.
Qed.

Lemma All_local_env_Pclosed Σ Γ :
  All_local_env ( lift_typing Pclosed Σ) Γ ->
  Alli (fun i d => closed_decl i d) 0 (List.rev Γ).
Proof.
  induction Γ; simpl; auto; try constructor.  
  intros all; depelim all; intuition auto.
  - apply Alli_app_inv; auto. constructor. simpl.
    rewrite List.rev_length. 2:constructor.
    unfold closed_decl. unfold Pclosed in l. simpl. red in l.
    destruct l as [s H].
    now rewrite andb_true_r in H.
  - apply Alli_app_inv; auto. constructor. simpl.
    rewrite List.rev_length. 2:constructor.
    unfold closed_decl. unfold Pclosed, lift_typing in *. now simpl.
Qed.

Lemma closed_subst_context (Γ Δ Δ' : context) t :
  closedn (#|Γ| + #|Δ|) t ->
  Alli (fun i d => closed_decl (#|Γ| + S #|Δ| + i) d) 0 (List.rev Δ') -> 
  Alli (fun i d => closed_decl (#|Γ| + #|Δ| + i) d) 0 (List.rev (subst_context [t] 0 Δ')).
Proof.
  induction Δ' in Δ |- *.
  intros. simpl. auto. constructor.
  destruct a as [? [] ?]; simpl.
  - intros. eapply Alli_app in X as [X X'].
    rewrite subst_context_snoc. simpl. eapply Alli_app_inv.
    eapply IHΔ'; eauto. constructor; [|constructor].
    simpl. 
    rewrite /closed_decl /map_decl /= Nat.add_0_r List.rev_length subst_context_length.
    inv X'. unfold closed_decl in H0. simpl in H0.
    rewrite List.rev_length Nat.add_0_r in H0.
    move/andP: H0 => [Hl Hr].
    rewrite !closedn_subst /= ?H //; eapply closed_upwards; eauto; try lia.
  - intros. eapply Alli_app in X as [X X'].
    rewrite subst_context_snoc. simpl. eapply Alli_app_inv.
    eapply IHΔ'; eauto. constructor; [|constructor].
    simpl. 
    rewrite /closed_decl /map_decl /= Nat.add_0_r List.rev_length subst_context_length.
    inv X'. unfold closed_decl in H0. simpl in H0.
    rewrite List.rev_length Nat.add_0_r in H0.
    rewrite !closedn_subst /= ?H //; eapply closed_upwards; eauto; try lia.
Qed.

Lemma closed_smash_context_gen (Γ Δ Δ' : context) :
  Alli (fun i d => closed_decl (#|Γ| + i) d) 0 (List.rev Δ) -> 
  Alli (fun i d => closed_decl (#|Γ| + #|Δ| + i) d) 0 (List.rev Δ') -> 
  Alli (fun i d => closed_decl (#|Γ| + i) d) 0 (List.rev (smash_context Δ' Δ)).
Proof.
  induction Δ in Δ' |- *.
  intros. simpl. auto.
  simpl. eapply (Alli_impl _ X0). simpl. now rewrite Nat.add_0_r.
  destruct a as [? [] ?]; simpl.
  - intros. eapply Alli_app in X as [X X'].
    eapply IHΔ; eauto.
    inv X'. unfold closed_decl in H. simpl in H.
    rewrite List.rev_length Nat.add_0_r in H.
    clear X1. eapply closed_subst_context; auto.
    now move/andP: H => [].
  - intros. eapply Alli_app in X as [X X'].
    eapply IHΔ; eauto.
    inv X'. unfold closed_decl in H. simpl in H.
    rewrite List.rev_length Nat.add_0_r in H.
    clear X1. rewrite List.rev_app_distr.
    eapply Alli_app_inv; repeat constructor.
    now rewrite /closed_decl Nat.add_0_r /=.
    rewrite List.rev_length /=. clear -X0.
    apply Alli_shift, (Alli_impl _ X0). intros.
    eapply closed_decl_upwards; eauto; lia.
Qed.

Lemma closed_smash_context (Γ Δ : context) :
  Alli (fun i d => closed_decl (#|Γ| + i) d) 0 (List.rev Δ) -> 
  Alli (fun i d => closed_decl (#|Γ| + i) d) 0 (List.rev (smash_context [] Δ)).
Proof.
  intros; apply (closed_smash_context_gen Γ _ []); auto. constructor.
Qed.

Lemma context_assumptions_app Γ Δ : context_assumptions (Γ ++ Δ) = 
  context_assumptions Γ + context_assumptions Δ.
Proof.
  induction Γ as [|[? [] ?] ?]; simpl; auto.
Qed.

Lemma weaken_env_prop_closed {cf:checker_flags} : 
  weaken_env_prop (lift_typing (fun (_ : global_env_ext) (Γ : context) (t T : term) =>
  closedn #|Γ| t && closedn #|Γ| T)).
Proof. repeat red. intros. destruct t; red in X0; eauto. Qed.

Lemma declared_projection_closed_ind {cf:checker_flags} {Σ : global_env_ext} {mdecl idecl p pdecl} : 
  wf Σ.1 ->
  declared_projection Σ.1 mdecl idecl p pdecl ->
  Forall_decls_typing
  (fun (_ : TemplateEnvironment.global_env_ext) (Γ : TemplateEnvironment.context) (t T : term) =>
  closedn #|Γ| t && closedn #|Γ| T) Σ.1 ->
  closedn (S (ind_npars mdecl)) pdecl.2.
Proof.
  intros wfΣ isdecl X0.
  pose proof (declared_projection_inv weaken_env_prop_closed wfΣ X0 isdecl) as onp.
  set (declared_inductive_inv _ wfΣ X0 isdecl.p1) as oib in *.
  clearbody oib.
  have onpars := onParams _ _ _ _ (declared_minductive_inv weaken_env_prop_closed wfΣ X0 isdecl.p1.p1).
  have parslen := onNpars _ _ _ _ (declared_minductive_inv weaken_env_prop_closed wfΣ X0 isdecl.p1.p1).
  simpl in onp. destruct (ind_cshapes oib) as [|? []] eqn:Heq; try contradiction.
  red in onp.
  destruct (nth_error (smash_context [] _) _) eqn:Heq'; try contradiction.
  rewrite {}onp. 
  pose proof (onConstructors oib) as onc. 
  red in onc. rewrite Heq in onc. inv onc. clear X1.
  eapply on_cargs in X.
  simpl.
  replace (S (ind_npars mdecl)) with (1 + ind_npars mdecl) by lia.
  eapply closedn_subst.
  { clear. unfold inds. generalize (TemplateEnvironment.ind_bodies mdecl).
    induction l; simpl; auto. }
  rewrite inds_length.
  eapply closedn_subst0.
  { clear. unfold projs. induction p.2; simpl; auto. }
  rewrite projs_length /=.
  eapply (@closed_upwards (ind_npars mdecl + #|ind_bodies mdecl| + p.2 + 1)).
  2:lia.
  eapply closedn_lift.
  clear -parslen isdecl Heq' onpars X.
  rename X into args.
  apply type_local_ctx_Pclosed in args.
  red in onpars.
  eapply All_local_env_Pclosed in onpars.
  eapply (Alli_impl (Q:=fun i d => closed_decl (#|ind_params mdecl| + i + #|arities_context (ind_bodies mdecl)|) d)) in args.
  2:{ intros n x. rewrite app_context_length. 
      intros H; eapply closed_decl_upwards; eauto. lia. }
  eapply (Alli_shiftn (P:=fun i d => closed_decl (i + #|arities_context (ind_bodies mdecl)|) d)) in args.
  rewrite Nat.add_0_r in args.
  eapply (Alli_impl (Q:=fun i d => closed_decl (i + #|arities_context (ind_bodies mdecl)|) d)) in onpars.
  2:{ intros n x d. eapply closed_decl_upwards; eauto; lia. }
  epose proof (Alli_app_inv onpars). rewrite List.rev_length /= in X.
  specialize (X args). rewrite -List.rev_app_distr in X.
  clear onpars args.
  eapply (Alli_impl (Q:=fun i d => closed_decl (#|arities_context (ind_bodies mdecl)| + i) d)) in X.
  2:intros; eapply closed_decl_upwards; eauto; lia.
  eapply closed_smash_context in X.
  eapply Alli_rev_nth_error in X; eauto.
  rewrite smash_context_length in X. simpl in X.
  eapply nth_error_Some_length in Heq'. rewrite smash_context_length in Heq'.
  simpl in Heq'. unfold closed_decl in X.
  move/andP: X => [] _ cl.
  eapply closed_upwards. eauto. rewrite arities_context_length.
  rewrite context_assumptions_app parslen.
  rewrite context_assumptions_app in Heq'. lia.
Qed.

Lemma typecheck_closed `{cf : checker_flags} :
  env_prop (fun Σ Γ t T =>
              closedn #|Γ| t && closedn #|Γ| T).
Proof.
  assert (X := weaken_env_prop_closed).
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
    apply closedn_subst0.
    + unfold inds. clear. simpl. induction #|ind_bodies mdecl|. constructor.
      simpl. now rewrite IHn.
    + rewrite inds_length.
      rewrite closedn_subst_instance_constr.
      eapply declared_inductive_inv in X0; eauto.
      pose proof X0.(onConstructors) as XX.
      eapply All2_nth_error_Some in Hcdecl; eauto.
      destruct Hcdecl as [? [? ?]]. cbn in *.
      destruct o.(on_ctype) as [s Hs]. rewrite -> andb_and in Hs.
      apply proj1 in Hs.
      unfold arities_context in Hs.
      rewrite rev_map_length in Hs.
      eauto using closed_upwards with arith.

  - intuition auto. solve_all. unfold test_snd. simpl in *.
    rtoProp; eauto.
    apply closedn_mkApps; auto.
    rewrite forallb_app. simpl. rewrite H1.
    rewrite forallb_skipn; auto.
    now apply closedn_mkApps_inv in H7.

  - intuition auto.
    apply closedn_subst0.
    simpl. apply closedn_mkApps_inv in H2.
    rewrite forallb_rev H1. apply H2.
    simpl. rewrite List.rev_length. rewrite H0.
    rewrite closedn_subst_instance_constr.
    eapply closed_upwards. eapply declared_projection_closed_ind; eauto.
    lia.

  - split. solve_all.
    destruct x; simpl in *.
    unfold test_def. simpl. rtoProp.
    split.
    rewrite -> app_context_length in *. rewrite -> Nat.add_comm in *.
    eapply closedn_lift_inv in H2; eauto. lia.
    subst types.
    now rewrite app_context_length fix_context_length in H1.
    eapply nth_error_all in H0; eauto. simpl in H0. intuition. rtoProp.
    subst types. rewrite app_context_length in H1.
    rewrite Nat.add_comm in H1.
    now eapply closedn_lift_inv in H1.

  - split. solve_all. destruct x; simpl in *.
    unfold test_def. simpl. rtoProp.
    split.
    rewrite -> app_context_length in *. rewrite -> Nat.add_comm in *.
    eapply closedn_lift_inv in H2; eauto. lia.
    subst types.
    now rewrite -> app_context_length, fix_context_length in H1.
    eapply (nth_error_all) in H; eauto. simpl in *.
    intuition. rtoProp.
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

Lemma declared_decl_closed `{checker_flags} {Σ : global_env} {cst decl} :
  wf Σ ->
  lookup_env Σ cst = Some decl ->
  on_global_decl (fun Σ Γ b t => closedn #|Γ| b && option_default (closedn #|Γ|) t true)
                 (Σ, universes_decl_of_decl decl) cst decl.
Proof.
  intros.
  eapply weaken_lookup_on_global_env; try red; eauto.
  eapply on_global_env_impl; cycle 1.
  apply (env_prop_sigma _ typecheck_closed _ X).
  red; intros. unfold lift_typing in *. destruct T; intuition auto with wf.
  destruct X1 as [s0 Hs0]. simpl. rtoProp; intuition.
Qed.

Definition closed_inductive_body mdecl idecl :=
  closedn 0 idecl.(ind_type) &&
  forallb (fun cdecl => 
    closedn (#|arities_context mdecl.(ind_bodies)|) (cdecl_type cdecl)) idecl.(ind_ctors) &&
  forallb (fun x => closedn (S (ind_npars mdecl)) x.2) idecl.(ind_projs).

Definition closed_inductive_decl mdecl :=
  closed_ctx (ind_params mdecl) &&
  forallb (closed_inductive_body mdecl) (ind_bodies mdecl). 
  

Lemma closedn_All_local_env (ctx : list context_decl) :
  All_local_env 
    (fun (Γ : context) (b : term) (t : option term) =>
      closedn #|Γ| b && option_default (closedn #|Γ|) t true) ctx ->
    closedn_ctx 0 ctx.
Proof.
  induction 1. constructor.
  rewrite /closedn_ctx /= mapi_app forallb_app /= [forallb _ _]IHX /id /closed_decl /=.
  now rewrite Nat.add_0_r List.rev_length t0.
  rewrite /closedn_ctx /= mapi_app forallb_app /= [forallb _ _]IHX /id /closed_decl /=.
  now rewrite Nat.add_0_r List.rev_length t1.
Qed.

Lemma skipn_0 {A} (l : list A) : skipn 0 l = l.
Proof. reflexivity. Qed.

Lemma declared_projection_closed {cf:checker_flags} {Σ : global_env_ext} {mdecl idecl p pdecl} : 
  wf Σ.1 ->
  declared_projection Σ.1 mdecl idecl p pdecl ->
  closedn (S (ind_npars mdecl)) pdecl.2.
Proof.
  intros; eapply declared_projection_closed_ind; eauto.
  eapply typecheck_closed; eauto.
  constructor. eapply type_Prop.
Qed.

Lemma declared_inductive_closed {cf:checker_flags} {Σ : global_env_ext} {mdecl mind} : 
  wf Σ.1 ->
  declared_minductive Σ.1 mind mdecl ->
  closed_inductive_decl mdecl.
Proof.
  intros wfΣ decl.
  pose proof (declared_decl_closed wfΣ decl) as decl'.
  red in decl'.
  unfold closed_inductive_decl.
  apply andb_and. split. apply onParams in decl'.
  now apply closedn_All_local_env in decl'; auto.
  apply onInductives in decl'.
  eapply All_forallb.
  
  assert (Alli (fun i =>  declared_inductive Σ.1 mdecl {| inductive_mind := mind; inductive_ind := i |}) 
    0 (ind_bodies mdecl)).
  { eapply forall_nth_error_Alli. intros.
    split; auto. }
  eapply Alli_mix in decl'; eauto. clear X.
  clear decl.
  eapply Alli_All; eauto.
  intros n x [decli oib].
  rewrite /closed_inductive_body.
  apply andb_and; split. apply andb_and. split.
  - apply onArity in oib. hnf in oib.
    now move/andP: oib => [].
  - pose proof (onConstructors oib).
    red in X. eapply All_forallb. eapply All2_All_left; eauto.
    firstorder auto.
    eapply on_ctype in X0.
    now move/andP: X0 => [].
  - eapply All_forallb.
    pose proof (onProjections oib).
    destruct (eq_dec (ind_projs x) []) as [->|eq]; try constructor.
    specialize (X eq). clear eq.
    destruct (ind_cshapes oib) as [|? []]; try contradiction.
    apply on_projs in X.
    assert (Alli (fun i pdecl => declared_projection Σ.1 mdecl x 
     (({| inductive_mind := mind; inductive_ind := n |}, mdecl.(ind_npars)), i) pdecl)
      0 (ind_projs x)).
    { eapply forall_nth_error_Alli.
      intros. split; auto. }
    eapply (Alli_All X0). intros.
    now eapply declared_projection_closed in H.
Qed.

Lemma rev_subst_instance_context u Γ :
  List.rev (subst_instance_context u Γ) = subst_instance_context u (List.rev Γ).
Proof.
  unfold subst_instance_context, map_context.
  now rewrite map_rev.
Qed.

Lemma closedn_subst_instance_context k Γ u :
  closedn_ctx k (subst_instance_context u Γ) = closedn_ctx k Γ.
Proof.
  unfold closedn_ctx; f_equal.
  rewrite rev_subst_instance_context.
  rewrite mapi_map. apply mapi_ext.
  intros n [? [] ?]; unfold closed_decl; cbn.
  all: now rewrite !closedn_subst_instance_constr.
Qed.
