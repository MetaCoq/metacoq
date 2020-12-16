(* Distributed under the terms of the MIT license. *)
From MetaCoq Require Import utils Ast AstUtils Environment Induction LiftSubst.

(** * Universe substitution

  Substitution of universe levels for universe level variables, used to
  implement universe polymorphism. *)

Lemma lift_subst_instance_constr u c n k :
  lift n k (subst_instance_constr u c) = subst_instance_constr u (lift n k c).
Proof.
  induction c in k |- * using term_forall_list_ind; simpl; auto;
    rewrite ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length,
            ?map_predicate_map_predicate, ?map_predicate_subst_instance_predicate, 
            ?map_branch_map_branch;
    f_equal; eauto; solve_all; eauto.
Qed.

Lemma subst_instance_constr_mkApps u f a :
  subst_instance_constr u (mkApps f a) =
  mkApps (subst_instance_constr u f) (map (subst_instance_constr u) a).
Proof.
  induction a in f |- *; auto.
  simpl map. simpl. destruct f; try reflexivity.
  simpl. f_equal. rewrite map_app. reflexivity.
Qed.

Lemma subst_instance_constr_it_mkProd_or_LetIn u ctx t :
  subst_instance_constr u (it_mkProd_or_LetIn ctx t) =
  it_mkProd_or_LetIn (subst_instance_context u ctx) (subst_instance_constr u t).
Proof.
  induction ctx in u, t |- *; simpl; try congruence.
  rewrite IHctx. unfold mkProd_or_LetIn; cbn. f_equal.
  destruct (decl_body a); eauto.
Qed.

Lemma subst_instance_context_length u ctx
  : #|subst_instance_context u ctx| = #|ctx|.
Proof.
  unfold subst_instance_context, map_context.
  now rewrite map_length.
Qed.

Lemma subst_subst_instance_constr u c N k :
  subst (map (subst_instance_constr u) N) k (subst_instance_constr u c) =
  subst_instance_constr u (subst N k c).
Proof.
  induction c in k |- * using term_forall_list_ind; simpl; auto;
    rewrite ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length, 
            ?map_predicate_map_predicate,
            ?map_branch_map_branch; simpl;
    try solve [f_equal; eauto; solve_all; eauto].

  - elim (Nat.leb k n). rewrite nth_error_map.
    destruct (nth_error N (n - k)). simpl.
    apply lift_subst_instance_constr. reflexivity. reflexivity.
    
  - rewrite subst_instance_constr_mkApps. f_equal; auto.
    rewrite map_map_compose. solve_all.
Qed.

Lemma map_subst_instance_constr_to_extended_list_k u ctx k :
  map (subst_instance_constr u) (to_extended_list_k ctx k)
  = to_extended_list_k ctx k.
Proof.
  pose proof (to_extended_list_k_spec ctx k).
  solve_all. now destruct H as [n [-> _]].
Qed.

(** Tests that the term is closed over [k] universe variables *)
Fixpoint closedu (k : nat) (t : term) : bool :=
  match t with
  | tSort univ => closedu_universe k univ
  | tInd _ u => closedu_instance k u
  | tConstruct _ _ u => closedu_instance k u
  | tConst _ u => closedu_instance k u
  | tRel i => true
  | tEvar ev args => forallb (closedu k) args
  | tLambda _ T M | tProd _ T M => closedu k T && closedu k M
  | tApp u v => closedu k u && forallb (closedu k) v
  | tCast c kind t => closedu k c && closedu k t
  | tLetIn na b t b' => closedu k b && closedu k t && closedu k b'
  | tCase ind p c brs =>
    let p' := test_predicate (closedu_instance k) (closedu k) (closedu k) p in
    let brs' := forallb (test_branch (closedu k)) brs in
    p' && closedu k c && brs'
  | tProj p c => closedu k c
  | tFix mfix idx =>
    forallb (test_def (closedu k) (closedu k)) mfix
  | tCoFix mfix idx =>
    forallb (test_def (closedu k) (closedu k)) mfix
  | x => true
  end.

Lemma closedu_subst_instance_constr u t
  : closedu 0 t -> subst_instance_constr u t = t.
Proof.
  induction t in |- * using term_forall_list_ind; simpl; auto; intros H';
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length,
               ?map_predicate_map_predicate, ?map_branch_map_branch;
    try f_equal; eauto with substu; unfold test_def, test_predicate in *;
      try solve [f_equal; eauto; repeat (rtoProp; solve_all; eauto with substu)].
Qed.

Lemma subst_instance_constr_closedu (u : Instance.t) (Hcl : closedu_instance 0 u) t :
  closedu #|u| t -> closedu 0 (subst_instance_constr u t).
Proof.
  induction t in |- * using term_forall_list_ind; simpl; auto; intros H';
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length, ?forallb_map,
               ?map_predicate_map_predicate;
    try f_equal; auto with substu;
      unfold test_def, test_predicate in *; simpl;
      try solve [f_equal; eauto; repeat (rtoProp; solve_all); intuition auto with substu].
Qed.
