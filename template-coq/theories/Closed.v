(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega Lia.
From Template Require Import config utils Ast AstUtils Induction utils LiftSubst Typing TypingWf.
From Template Require Import WeakeningEnv.
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

Lemma typecheck_closed `{cf : checker_flags} :
  env_prop (fun Σ Γ t T =>
              closedn #|Γ| t && closedn #|Γ| T).
Proof.
  assert(weaken_env_prop (lift_typing (fun (_ : global_context) (Γ : context) (t T : term) =>
                                         closedn #|Γ| t && closedn #|Γ| T))).
  { repeat red. intros. destruct t; red in X0; eauto. }

  apply typing_ind_env; intros; simpl; rewrite -> ?andb_and in *; try solve [intuition auto].
  - pose proof (nth_error_Some_length H).
    elim (Nat.ltb_spec n #|Γ|); intuition.
    eapply (All_local_env_lookup H0) in H. red in H.
    destruct decl_body.
    -- move/andb_and: H => [].
       rewrite skipn_length; try lia; move=> Ht.
       move/(closedn_lift (S n)).
       now have->: #|Γ| - S n + S n = #|Γ| by lia.
    -- move: H => [s].
       move/andb_and => [Hty _].
       move: Hty; rewrite skipn_length; try lia.
       move/(closedn_lift (S n)).
       have->: #|Γ| - S n + S n = #|Γ| by lia.
       eauto.

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
    destruct X0 as [[s Hs] _]. rewrite -> andb_and in Hs.
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
    rewrite forallb_app. simpl. rewrite H4.
    rewrite forallb_skipn; auto.
    now apply closedn_mkApps_inv in H9.

  - intuition. subst ty.
    apply closedn_subst0.
    simpl. apply closedn_mkApps_inv in H2.
    rewrite forallb_rev H1. apply H2.
    rewrite closedn_subst_instance_constr.
    destruct isdecl as [isdecl Hpdecl].
    eapply declared_inductive_inv in isdecl; eauto.
    apply onProjections in isdecl.
    eapply nth_error_alli in isdecl; eauto.
    red in isdecl.
    destruct decompose_prod_assum eqn:Heq.
    destruct isdecl as [[s Hs] Hc]. simpl in *.
    rewrite <- Hc in H0. rewrite <- H0 in Hs.
    rewrite andb_true_r in Hs. rewrite List.rev_length.
    eauto using closed_upwards with arith.

  - split. solve_all.
    destruct x; simpl in *.
    unfold test_def. simpl. toProp.
    split.
    rewrite -> app_context_length in *. rewrite -> Nat.add_comm in *.
    eapply closedn_lift_inv in H1; eauto. lia.
    subst types.
    now rewrite app_context_length fix_context_length in H0.
    eapply nth_error_all in H; eauto. simpl in H. intuition. toProp.
    subst types. rewrite app_context_length in H0.
    rewrite Nat.add_comm in H0.
    now eapply closedn_lift_inv in H0.

  - split. solve_all. destruct x; simpl in *.
    unfold test_def. simpl. toProp.
    split.
    rewrite -> app_context_length in *. rewrite -> Nat.add_comm in *.
    eapply closedn_lift_inv in H1; eauto. lia.
    subst types.
    now rewrite -> app_context_length, fix_context_length in H0.
    eapply (nth_error_all) in H; eauto. simpl in *.
    intuition. toProp.
    subst types. rewrite app_context_length in H0.
    rewrite Nat.add_comm in H0.
    now eapply closedn_lift_inv in H0.
Qed.

Lemma declared_decl_closed `{checker_flags} Σ cst decl :
  wf Σ ->
  lookup_env (fst Σ) cst = Some decl ->
  on_global_decl (fun Σ Γ b t =>
                    match b with Some b => Ast.wf b | None => True end /\ Ast.wf t /\
                    option_default (closedn #|Γ|) b true && closedn #|Γ| t) Σ decl.
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
  toProp; intuition.
Qed.

Require Import ssreflect ssrbool.
Lemma closed_decl_upwards k d : closed_decl k d -> forall k', k <= k' -> closed_decl k' d.
Proof.
  case: d => na [body|] ty; rewrite /closed_decl /=.
  move/andP => [cb cty] k' lek'. do 2 rewrite (@closed_upwards k) //.
  move=> cty k' lek'; rewrite (@closed_upwards k) //.
Qed.
