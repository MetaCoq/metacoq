(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction.

Instance subst_instance_list A `{UnivSubst A} : UnivSubst (list A) :=
  fun u => List.map (subst_instance u).


Lemma subst_instance_lift u c n k :
  subst_instance u (lift n k c) = lift n k (subst_instance u c).
Proof.
  unfold subst_instance; cbn.
  induction c in k |- * using term_forall_list_ind; simpl; auto;
    rewrite ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length;
      autorewrite with map;
    try solve [f_equal; eauto; solve_all; eauto].
Qed.

Lemma subst_instance_mkApps u f a :
  subst_instance u (mkApps f a) =
  mkApps (subst_instance u f) (map (subst_instance u) a).
Proof.
  induction a in f |- *; auto.
  simpl map. simpl. now rewrite IHa.
Qed.

Lemma subst_instance_it_mkProd_or_LetIn u ctx t :
  subst_instance u (it_mkProd_or_LetIn ctx t) =
  it_mkProd_or_LetIn (subst_instance u ctx) (subst_instance u t).
Proof.
  unfold subst_instance; cbn.
  induction ctx in u, t |- *; simpl; unfold mkProd_or_LetIn; try congruence.
  rewrite IHctx.  f_equal; unfold mkProd_or_LetIn.
  destruct a as [na [b|] ty]; simpl; eauto.
Qed.

Lemma subst_instance_it_mkLambda_or_LetIn u ctx t :
  subst_instance u (it_mkLambda_or_LetIn ctx t) =
  it_mkLambda_or_LetIn (subst_instance u ctx) (subst_instance u t).
Proof.
  unfold subst_instance; cbn.
  induction ctx in u, t |- *; simpl; unfold mkProd_or_LetIn; try congruence.
  rewrite IHctx.  f_equal; unfold mkProd_or_LetIn.
  destruct a as [na [b|] ty]; simpl; eauto.
Qed.

Lemma subst_instance_subst u c (s : list term) k :
  subst_instance u (subst s k c) = subst (subst_instance u s) k (subst_instance u c).
Proof.
  unfold subst_instance, subst_instance_list; cbn.
  induction c in k |- * using term_forall_list_ind; simpl; auto;
    rewrite ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length,
      ?map_branch_map_branch, ?map_predicate_map_predicate;
    try solve [f_equal; eauto; solve_all; eauto].

  elim (Nat.leb k n); auto.
  rewrite nth_error_map.
  destruct (nth_error s (n - k)). simpl.
  now rewrite subst_instance_lift. reflexivity.
Qed.

Lemma map_subst_instance_to_extended_list_k u ctx k :
  map (subst_instance u) (to_extended_list_k ctx k)
  = to_extended_list_k ctx k.
Proof.
  pose proof (to_extended_list_k_spec ctx k).
  solve_all. now destruct H as [n [-> _]].
Qed.

Hint Rewrite map_map_compose @compose_map_def map_length : map.

Lemma closedu_subst_instance u t
  : closedu 0 t -> subst_instance u t = t.
Proof.
  unfold subst_instance; cbn.
  induction t in |- * using term_forall_list_ind; simpl; auto; intros H';
    autorewrite with map;
    try f_equal; eauto with substu; unfold test_predicate, test_branch, test_def in *;
      try solve [f_equal; eauto; repeat (rtoProp; solve_all); eauto with substu].
Qed.

Hint Rewrite test_context_map : map.

Lemma subst_instance_closedu (u : Instance.t) (Hcl : closedu_instance 0 u) t :
  closedu #|u| t -> closedu 0 (subst_instance u t).
Proof.
  induction t in |- * using term_forall_list_ind; simpl; auto; intros H';
    autorewrite with map;
    try f_equal; auto with substu;
      unfold test_def, test_predicate, test_branch in *; simpl;
      f_equal; eauto; repeat (rtoProp; solve_all); intuition auto with substu.
Qed.

Lemma rev_subst_instance {u Γ} :
  List.rev (subst_instance u Γ) = subst_instance u (List.rev Γ).
Proof.
  unfold subst_instance, subst_instance_context, map_context.
  now rewrite map_rev.
Qed.

Lemma subst_instance_extended_subst u Γ n :
  map (subst_instance u) (extended_subst Γ n) =
  extended_subst (subst_instance u Γ) n.
Proof.
  induction Γ as [|[?[]?] ?] in n |- *; simpl; auto.
  - autorewrite with len.
    f_equal; auto.
    rewrite subst_instance_subst, <-IHΓ.
    rewrite <-subst_instance_lift; simpl.
    f_equal.
  - f_equal; auto.
Qed.
