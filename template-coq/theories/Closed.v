(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega Lia.
From Template Require Import config utils Ast AstUtils Induction utils LiftSubst Typing.
From Template Require Import WeakeningEnv.

(** * Lemmas about the [closedn] predicate *)

Lemma closedn_lift n k k' t : closedn k t = true -> closedn (k + n) (lift n k' t) = true.
Proof.
  revert k.
  induction t in n, k' |- * using term_forall_list_ind; intros;
    simpl in *; rewrite ?andb_true_iff in *;
    rewrite ?map_map_compose, ?compose_on_snd, ?compose_map_def;
    try (f_equal; apply_spec);  simpl closed in *;
      try rewrite ?map_length; intuition auto.

  - elim (Nat.leb_spec k' n0); intros. simpl.
    elim (Nat.ltb_spec); auto. apply Nat.ltb_lt in H. lia.
    simpl. elim (Nat.ltb_spec); auto. intros.
    apply Nat.ltb_lt in H. lia.
  - merge_Forall. rewrite forallb_map. eapply Forall_forallb in H0; intuition eauto.
  - specialize (IHt2 n (S k') _ H1). eauto.
  - specialize (IHt2 n (S k') _ H1). eauto.
  - specialize (IHt3 n (S k') _ H1). eauto.
  - merge_Forall. rewrite forallb_map. eapply Forall_forallb in H2; intuition eauto.
  - merge_Forall. rewrite forallb_map. eapply Forall_forallb in H2; intuition eauto.
    destruct x; unfold test_snd, compose, on_snd; simpl. eapply H1. auto.
  - merge_Forall. rewrite forallb_map. eapply Forall_forallb in H0; intuition eauto.
    unfold test_def, compose, map_def in *. simpl.
    rewrite !andb_true_iff in *. intuition auto.
    rewrite Nat.add_assoc. eauto.
  - merge_Forall. rewrite forallb_map. eapply Forall_forallb in H0; intuition eauto.
    unfold test_def, compose, map_def in *. simpl.
    rewrite !andb_true_iff in *. intuition auto.
    rewrite Nat.add_assoc. eauto.
Qed.


Lemma closedn_lift_inv n k k' t : k <= k' ->
                                   closedn (k' + n) (lift n k t) = true ->
                                   closedn k' t = true.
Proof.
  induction t in n, k, k' |- * using term_forall_list_ind; intros;
    simpl in *; rewrite ?andb_true_iff in *;
    rewrite ?map_map_compose, ?compose_on_snd, ?compose_map_def;
    try (f_equal; apply_spec);  simpl closed in *;
      try rewrite ?map_length; intuition eauto 2.

  - revert H0.
    elim (Nat.leb_spec k n0); intros. simpl in *.
    elim (Nat.ltb_spec); auto. apply Nat.ltb_lt in H1. intros. lia.
    revert H1. simpl. elim (Nat.ltb_spec); auto. intros. apply Nat.ltb_lt. lia.
    intros; discriminate.
  - rewrite forallb_map in H1. merge_Forall. eapply Forall_forallb; eauto.
    simpl; intuition eauto.
  - specialize (IHt2 n (S k) (S k')). eauto with arith.
  - specialize (IHt2 n (S k) (S k')). eauto with arith.
  - specialize (IHt3 n (S k) (S k')). eauto with arith.
  - rewrite forallb_map in H3. merge_Forall. eapply Forall_forallb; eauto. simpl; intuition eauto.
  - rewrite forallb_map in H3. merge_Forall. eapply Forall_forallb; eauto. simpl; intuition eauto.
    destruct x; unfold test_snd, compose, on_snd in *; simpl in *; eauto.
  - rewrite forallb_map in H1. merge_Forall. eapply Forall_forallb; intuition eauto.
    unfold test_def, compose, map_def in *. simpl in *.
    rewrite !andb_true_iff in *. rewrite !map_length in *. intuition eauto 2.
    rewrite Nat.add_assoc in H5. specialize (H4 n (#|m| + k) (#|m| + k')). forward H4 by lia.
    apply H4. auto.
  - rewrite forallb_map in H1. merge_Forall. eapply Forall_forallb; intuition eauto.
    unfold test_def, compose, map_def in *. simpl in *.
    rewrite !andb_true_iff in *. rewrite !map_length in *. intuition eauto 2.
    rewrite Nat.add_assoc in H5. specialize (H4 n (#|m| + k) (#|m| + k')). forward H4 by lia.
    apply H4. auto.
Qed.

Lemma closedn_mkApps k f u:
  closedn k f = true -> forallb (closedn k) u = true ->
  closedn k (mkApps f u) = true.
Proof.
  intros Hf Hu.
  induction u; simpl; auto.
  destruct f; simpl in *; try rewrite Hf, Hu; auto.
  rewrite forallb_app. simpl. rewrite Hu.
  rewrite andb_assoc. now rewrite Hf.
Qed.

Lemma closedn_mkApps_inv k f u:
  closedn k (mkApps f u) = true ->
  closedn k f && forallb (closedn k) u = true.
Proof.
  induction u; simpl; auto.
  - now rewrite andb_true_r.
  - intros. destruct f; simpl in *; auto.
    rewrite forallb_app in H. simpl in H.
    now rewrite andb_assoc in H.
Qed.

Lemma closedn_subst s k k' t :
  forallb (closedn k) s = true -> closedn (k + k' + #|s|) t = true ->
  closedn (k + k') (subst s k' t) = true.
Proof.
  induction t in k' |- * using term_forall_list_ind; intros;
    simpl in *; rewrite ?andb_true_iff in *;
    rewrite ?map_map_compose, ?compose_on_snd, ?compose_map_def;
    try (f_equal; apply_spec);  simpl closed in *;
      try rewrite ?map_length; intuition auto.

  - elim (Nat.leb_spec k' n); intros. simpl.
    apply Nat.ltb_lt in H0.
    destruct nth_error eqn:Heq.
    -- eapply closedn_lift. eapply forallb_Forall in H; eauto. 2:{ intros. apply H2. }
       now eapply nth_error_forall in Heq; simpl; eauto; simpl in *.
    -- simpl. elim (Nat.ltb_spec); auto. intros.
       apply nth_error_None in Heq. lia.
    -- simpl. apply Nat.ltb_lt in H0.
       apply Nat.ltb_lt. lia.

  - merge_Forall. rewrite forallb_map.
    eapply Forall_forallb; eauto. unfold compose; intuition eauto.
  - specialize (IHt2 (S k') H).
    rewrite <- Nat.add_succ_comm in IHt2. eauto.
  - specialize (IHt2 (S k') H).
    rewrite <- Nat.add_succ_comm in IHt2. eauto.
  - specialize (IHt3 (S k') H).
    rewrite <- Nat.add_succ_comm in IHt3. eauto.
  - merge_Forall.
    rewrite closedn_mkApps. eauto.
    now specialize (IHt k' H0).
    rewrite forallb_map. eapply Forall_forallb; eauto. simpl; intuition eauto.
  - merge_Forall. rewrite forallb_map. eapply Forall_forallb; eauto.
    simpl. intros [n trm]. unfold test_snd, on_snd, compose. intuition eauto.
  - merge_Forall. rewrite forallb_map. eapply Forall_forallb; eauto. simpl; intuition eauto.
    unfold test_def, compose, map_def in *. simpl.
    rewrite !andb_true_iff in *. intuition auto.
    rewrite Nat.add_assoc.
    specialize (H4 (#|m| + k')).
    rewrite <- H4; eauto.
    f_equal; lia. rewrite <- H5. f_equal; lia.
  - merge_Forall. rewrite forallb_map. eapply Forall_forallb; eauto. simpl; intuition eauto.
    unfold test_def, compose, map_def in *. simpl.
    rewrite !andb_true_iff in *. intuition auto.
    rewrite Nat.add_assoc.
    specialize (H4 (#|m| + k')).
    rewrite <- H4; eauto.
    f_equal; lia. rewrite <- H5. f_equal; lia.
Qed.

Lemma closedn_substl s k t :
  forallb (closedn k) s = true -> closedn (k + #|s|) t = true ->
  closedn k (substl s t) = true.
Proof.
  unfold substl.
  intros.
  generalize (closedn_subst s k 0 t H).
  rewrite Nat.add_0_r. eauto.
Qed.

Lemma subst_closedn s k t : Ast.wf t ->
  closedn k t = true -> subst s k t = t.
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
    simpl in *; rewrite ?andb_true_iff in *;
    rewrite ?map_map_compose, ?compose_on_snd, ?compose_map_def;
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
              closedn #|Γ| t && closedn #|Γ| T = true).
Proof.
  assert(weaken_env_prop (lift_typing (fun (_ : global_context) (Γ : context) (t T : term) =>
                                         closedn #|Γ| t && closedn #|Γ| T = true))).
  { repeat red. intros. destruct t; red in X0; eauto. }

  apply typing_ind_env; intros; simpl; rewrite -> ?andb_true_iff in *; try solve [intuition auto].
  - pose proof (nth_error_Some_length H).
    elim (Nat.ltb_spec n #|Γ|); intuition.
    eapply (All_local_env_lookup H0) in H. red in H.
    destruct decl_body.
    -- move/andb_true_iff: H => [].
       rewrite skipn_length; try lia; move=> Ht.
       move/(closedn_lift (S n)).
       now have->: #|Γ| - S n + S n = #|Γ| by lia.
    -- move: H => [s].
       move/andb_true_iff => [Hty _].
       move: Hty; rewrite skipn_length; try lia.
       move/(closedn_lift (S n)).
       by have->: #|Γ| - S n + S n = #|Γ| by lia.

  - destruct H. rewrite and_assoc. split. auto.
    clear X0 H H0 H1.
    induction X1; simpl. intuition auto.
    rewrite -> andb_true_iff in *. destruct p0. rewrite H.
    rewrite <- andb_true_iff. simpl.
    apply IHX1. unfold subst.
    pose proof (closedn_subst [hd] #|Γ| 0). rewrite Nat.add_0_r in H1.
    apply H1. simpl. now rewrite H.
    simpl. simpl in p. rewrite -> andb_true_iff in p. intuition auto.
    rewrite Nat.add_1_r. auto.

  - rewrite closedn_subst_instance_constr.
    eapply lookup_on_global_env in H; eauto.
    destruct H as [Σ' [HΣ' IH]].
    repeat red in IH. destruct decl, cst_body. simpl in *.
    rewrite -> andb_true_iff in IH. intuition.
    eauto using closed_upwards with arith.
    simpl in *.
    repeat red in IH. destruct IH as [s Hs].
    rewrite -> andb_true_iff in Hs. intuition.
    eauto using closed_upwards with arith.

  - rewrite closedn_subst_instance_constr.
    eapply declared_inductive_inv in X0; eauto.
    apply onArity in X0. repeat red in X0.
    destruct X0 as [[s Hs] _]. rewrite -> andb_true_iff in Hs.
    intuition eauto using closed_upwards with arith.

  - destruct isdecl as [Hidecl Hcdecl].
    eapply declared_inductive_inv in X0; eauto.
    apply onConstructors in X0. repeat red in X0.
    eapply nth_error_alli in Hcdecl; eauto.
    repeat red in Hcdecl.
    destruct Hcdecl as [[s Hs] _]. rewrite -> andb_true_iff in Hs.
    destruct Hs as [Hdecl _].
    unfold type_of_constructor.
    apply closedn_substl.
    unfold inds. clear. simpl. induction #|ind_bodies mdecl|. constructor.
    simpl. now rewrite IHn.
    rewrite inds_length. unfold arities_context in Hdecl.
    rewrite rev_map_length in Hdecl.
    rewrite closedn_subst_instance_constr.
    eauto using closed_upwards with arith.

  - intuition auto.
    eapply Forall_forallb; eauto.
    eapply Forall2_Forall_left; eauto.
    simpl; intros. destruct X4. rewrite -> andb_true_iff in e. destruct e.
    apply H7. simpl; intros. eauto.
    apply closedn_mkApps; auto.
    rewrite forallb_app. simpl. rewrite H6.
    rewrite forallb_skipn; auto.
    now apply closedn_mkApps_inv in H11.

  - intuition. subst ty.
    apply closedn_substl.
    simpl. apply closedn_mkApps_inv in H2.
    rewrite forallb_rev H1. apply H2.
    rewrite closedn_subst_instance_constr.
    destruct isdecl as [isdecl Hpdecl].
    eapply declared_inductive_inv in isdecl; eauto.
    apply onProjections in isdecl.
    destruct decompose_prod_assum eqn:Heq.
    destruct isdecl as [Hc isdecl].
    eapply nth_error_alli in isdecl; eauto.
    destruct isdecl as [s Hs]. simpl in *.
    forward Hc. intro. rewrite H in Hpdecl; destruct (snd p); discriminate.
    rewrite <- Hc in H0. rewrite <- H0 in Hs.
    rewrite andb_true_r in Hs. rewrite List.rev_length.
    eauto using closed_upwards with arith.

  - split. eapply All_forallb; eauto.
    simpl; eauto. intros. intuition.
    destruct x; simpl in *.
    unfold test_def. simpl.
    rewrite -> andb_true_iff in *. destruct b.
    split.
    rewrite -> app_context_length in *. rewrite -> Nat.add_comm in *.
    eapply closedn_lift_inv in H1; eauto. lia.
    subst types.
    now rewrite app_context_length fix_context_length in H0.
    eapply nth_error_all in H; eauto. simpl in H. intuition.
    rewrite -> !andb_true_iff in b. intuition.
    subst types. rewrite app_context_length in H0.
    rewrite Nat.add_comm in H0.
    now eapply closedn_lift_inv in H0.

  - split. eapply All_forallb; eauto.
    simpl; eauto. intros. intuition.
    destruct x; simpl in *.
    unfold test_def. simpl.
    rewrite -> andb_true_iff in *. destruct b.
    split.
    rewrite -> app_context_length in *. rewrite -> Nat.add_comm in *.
    eapply closedn_lift_inv in H1; eauto. lia.
    subst types.
    now rewrite -> app_context_length, fix_context_length in H0.
    eapply (nth_error_all) in H; eauto. simpl in *.
    intuition.
    rewrite -> !andb_true_iff in b. intuition.
    subst types. rewrite app_context_length in H0.
    rewrite Nat.add_comm in H0.
    now eapply closedn_lift_inv in H0.
Qed.
