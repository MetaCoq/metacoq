(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction.

Lemma lift_subst_instance_constr u c n k :
  lift n k (subst_instance_constr u c) = subst_instance_constr u (lift n k c).
Proof.
  induction c in k |- * using term_forall_list_ind; simpl; auto;
    rewrite ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length,
      ?map_predicate_map_predicate, ?map_branch_map_branch;
    try solve [f_equal; eauto; solve_all; eauto].
Qed.

Lemma subst_instance_constr_mkApps u f a :
  subst_instance_constr u (mkApps f a) =
  mkApps (subst_instance_constr u f) (map (subst_instance_constr u) a).
Proof.
  induction a in f |- *; auto.
  simpl map. simpl. now rewrite IHa.
Qed.

Lemma subst_instance_constr_it_mkProd_or_LetIn u ctx t :
  subst_instance_constr u (it_mkProd_or_LetIn ctx t) =
  it_mkProd_or_LetIn (subst_instance_context u ctx) (subst_instance_constr u t).
Proof.
  induction ctx in u, t |- *; simpl; unfold mkProd_or_LetIn; try congruence.
  rewrite IHctx.  f_equal; unfold mkProd_or_LetIn.
  destruct a as [na [b|] ty]; simpl; eauto.
Qed.

Lemma subst_instance_context_length u ctx
  : #|subst_instance_context u ctx| = #|ctx|.
Proof. unfold subst_instance_context, map_context. now rewrite map_length. Qed.
Hint Rewrite subst_instance_context_length : len.

Lemma subst_subst_instance_constr u c N k :
  subst (map (subst_instance_constr u) N) k (subst_instance_constr u c)
  = subst_instance_constr u (subst N k c).
Proof.
  induction c in k |- * using term_forall_list_ind; simpl; auto;
    rewrite ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length,
      ?map_branch_map_branch, ?map_predicate_map_predicate;
    try solve [f_equal; eauto; solve_all; eauto].

  elim (Nat.leb k n). rewrite nth_error_map.
  destruct (nth_error N (n - k)). simpl.
  apply lift_subst_instance_constr. reflexivity. reflexivity.
Qed.

Lemma map_subst_instance_constr_to_extended_list_k u ctx k :
  map (subst_instance_constr u) (to_extended_list_k ctx k)
  = to_extended_list_k ctx k.
Proof.
  pose proof (to_extended_list_k_spec ctx k).
  solve_all. now destruct H as [n [-> _]].
Qed.

Lemma closedu_subst_instance_constr u t
  : closedu 0 t -> subst_instance_constr u t = t.
Proof.
  induction t in |- * using term_forall_list_ind; simpl; auto; intros H';
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length,
      ?map_branch_map_branch, ?map_predicate_map_predicate;
    try f_equal; eauto with substu; unfold test_predicate, test_def in *;
      try solve [f_equal; eauto; repeat (rtoProp; solve_all); eauto with substu].
Qed.

Lemma subst_instance_constr_closedu (u : Instance.t) (Hcl : closedu_instance 0 u) t :
  closedu #|u| t -> closedu 0 (subst_instance_constr u t).
Proof.
  induction t in |- * using term_forall_list_ind; simpl; auto; intros H';
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length, ?forallb_map,
      ?map_predicate_map_predicate;
    try f_equal; auto with substu;
      unfold test_def, test_predicate in *; simpl;
      f_equal; eauto; repeat (rtoProp; solve_all); intuition auto with substu.
Qed.


Lemma rev_subst_instance_context {u Γ} :
  List.rev (subst_instance_context u Γ) = subst_instance_context u (List.rev Γ).
Proof.
  unfold subst_instance_context, map_context.
  now rewrite map_rev.
Qed.
