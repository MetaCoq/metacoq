(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import utils Ast AstUtils univ Induction LiftSubst.
Require Import String Lia.
Local Open Scope string_scope.
Set Asymmetric Patterns.

(** * Universe substitution

  *WIP*

  Substitution of universe levels for universe level variables, used to
  implement universe polymorphism. *)

Definition subst_instance_level u l :=
  match l with
  | univ.Level.lProp | univ.Level.lSet | univ.Level.Level _ => l
  | univ.Level.Var n => List.nth n u univ.Level.lProp
  end.

Definition subst_instance_cstrs u cstrs :=
  ConstraintSet.fold (fun '(l,d,r) =>
                     ConstraintSet.add (subst_instance_level u l, d, subst_instance_level u r))
                  cstrs ConstraintSet.empty.

Definition subst_instance_level_expr (u : universe_instance) (s : Universe.Expr.t) :=
  let '(l, b) := s in (subst_instance_level u l, b).

Definition subst_instance_univ (u : universe_instance) (s : universe) :=
  List.map (subst_instance_level_expr u) s.

Definition subst_instance_instance (u u' : universe_instance) :=
  List.map (subst_instance_level u) u'.

Fixpoint subst_instance_constr (u : universe_instance) (c : term) :=
  match c with
  | tRel _ | tVar _ | tMeta _ => c
  | tSort s => tSort (subst_instance_univ u s)
  | tConst c u' => tConst c (subst_instance_instance u u')
  | tInd i u' => tInd i (subst_instance_instance u u')
  | tConstruct ind k u' => tConstruct ind k (subst_instance_instance u u')
  | tEvar ev args => tEvar ev (List.map (subst_instance_constr u) args)
  | tLambda na T M => tLambda na (subst_instance_constr u T) (subst_instance_constr u M)
  | tApp f v => tApp (subst_instance_constr u f) (List.map (subst_instance_constr u) v)
  | tProd na A B => tProd na (subst_instance_constr u A) (subst_instance_constr u B)
  | tCast c kind ty => tCast (subst_instance_constr u c) kind (subst_instance_constr u ty)
  | tLetIn na b ty b' => tLetIn na (subst_instance_constr u b) (subst_instance_constr u ty)
                                (subst_instance_constr u b')
  | tCase ind p c brs =>
    let brs' := List.map (on_snd (subst_instance_constr u)) brs in
    tCase ind (subst_instance_constr u p) (subst_instance_constr u c) brs'
  | tProj p c => tProj p (subst_instance_constr u c)
  | tFix mfix idx =>
    let mfix' := List.map (map_def (subst_instance_constr u) (subst_instance_constr u)) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let mfix' := List.map (map_def (subst_instance_constr u) (subst_instance_constr u)) mfix in
    tCoFix mfix' idx
  end.

Definition subst_instance_context (u : universe_instance) (c : context) : context :=
  AstUtils.map_context (subst_instance_constr u) c.

Lemma lift_subst_instance_constr u c n k :
  lift n k (subst_instance_constr u c) = subst_instance_constr u (lift n k c).
Proof.
  induction c in k |- * using term_forall_list_ind; simpl; auto;
    rewrite ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length;
    try solve [f_equal; eauto; apply_spec; eauto].

  elim (Nat.leb k n0); reflexivity.
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
  rewrite IHctx. f_equal. destruct (decl_body a); eauto.
Qed.

Lemma subst_instance_context_length u ctx : #|subst_instance_context u ctx| = #|ctx|.
Proof. unfold subst_instance_context, map_context. now rewrite map_length. Qed.

Lemma subst_subst_instance_constr u c N k :
  subst (map (subst_instance_constr u) N) k (subst_instance_constr u c) =
  subst_instance_constr u (subst N k c).
Proof.
  induction c in k |- * using term_forall_list_ind; simpl; auto;
    rewrite ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length;
    try solve [f_equal; eauto; apply_spec; eauto].

  elim (Nat.leb k n). rewrite nth_error_map.
  destruct (nth_error N (n - k)). simpl.
  apply lift_subst_instance_constr. reflexivity. reflexivity.

  rewrite subst_instance_constr_mkApps. f_equal; auto.
  rewrite map_map_compose. apply_spec; eauto.
Qed.

Lemma map_subst_instance_constr_to_extended_list_k u ctx k :
  map (subst_instance_constr u) (to_extended_list_k ctx k) = to_extended_list_k ctx k.
Proof.
  pose proof (to_extended_list_k_spec ctx k).
  apply_spec. intros. now destruct H0 as [n [-> _]].
Qed.

Section Closedu.
  (** Tests that the term is closed over [k] universe variables *)
  Context (k : nat).

  Definition closedu_level (l : Level.t) :=
    match l with
    | Level.Var n => n <? k
    | _ => true
    end.

  Definition closedu_level_expr (s : Universe.Expr.t) :=
    closedu_level (fst s).

  Definition closedu_universe (u : universe) :=
    forallb closedu_level_expr u.

  Definition closedu_instance (u : universe_instance) :=
    forallb closedu_level u.

  Fixpoint closedu (t : term) : bool :=
  match t with
  | tSort univ => closedu_universe univ
  | tInd _ u => closedu_instance u
  | tConstruct _ _ u => closedu_instance u
  | tConst _ u => closedu_instance u
  | tRel i => true
  | tEvar ev args => forallb closedu args
  | tLambda _ T M | tProd _ T M => closedu T && closedu M
  | tApp u v => closedu u && forallb (closedu) v
  | tCast c kind t => closedu c && closedu t
  | tLetIn na b t b' => closedu b && closedu t && closedu b'
  | tCase ind p c brs =>
    let brs' := forallb (test_snd (closedu)) brs in
    closedu p && closedu c && brs'
  | tProj p c => closedu c
  | tFix mfix idx =>
    forallb (test_def closedu closedu ) mfix
  | tCoFix mfix idx =>
    forallb (test_def closedu closedu) mfix
  | x => true
  end.

End Closedu.

Require Import ssreflect ssrbool.

Ltac merge_Forall := unfold tFixProp, tCaseBrsProp in *;
  repeat match goal with
  | H : Forall _ ?x, H' : is_true (forallb _ ?x) |- _ =>
    eapply (Forall_forall_mix H) in H'; clear H
  end.

Ltac apply_spec :=
  match goal with
  | H : Forall _ _, H' : forallb _ _ |- map _ _ = map _ _ =>
    eapply (forall_forallb_map_spec H H')
  | H : Forall _ _, H' : forallb _ _ |- forallb _ _ = _ =>
    eapply (forall_forallb_forallb_spec H H')
  | H : tCaseBrsProp _ _, H' : forallb _ _ |- map _ _ = map _ _ =>
    eapply (case_brs_forallb_map_spec H H')
  | H : tCaseBrsProp _ _ |- map _ _ = map _ _ =>
    eapply (case_brs_map_spec H)
  | H : tFixProp _ _ _, H' : forallb _ _ |- map _ _ = map _ _ =>
    eapply (tfix_forallb_map_spec H H')
  | H : tFixProp _ _ _ |- map _ _ = map _ _ =>
    eapply (tfix_map_spec H)
  | H : Forall _ _ |- map _ _ = map _ _ =>
    eapply (forall_map_spec H)
  | H : Forall _ _ |- map _ _ = _ =>
    eapply (forall_map_id_spec H)
  | H : Forall _ _ |- is_true (forallb _ _) =>
    eapply (Forall_forallb _ _ _ H); clear H
  end.

Lemma andb_and b b' : b && b' <-> b /\ b'.
Proof. elim (@andP b b'); intuition. Qed.

Lemma closedu_subst_instance_level u t : closedu_level 0 t -> subst_instance_level u t = t.
Proof.
  destruct t => /=; auto.
  move/Nat.ltb_spec0. intro H. inversion H.
Qed.

Lemma closedu_subst_instance_level_expr u t : closedu_level_expr 0 t -> subst_instance_level_expr u t = t.
Proof.
  destruct t as [l n].
  rewrite /closedu_level_expr /subst_instance_level_expr /=.
  move/(closedu_subst_instance_level u) => //. congruence.
Qed.

Lemma closedu_subst_instance_univ u t : closedu_universe 0 t -> subst_instance_univ u t = t.
Proof.
  rewrite /closedu_universe /subst_instance_univ => H.
  eapply (forallb_Forall (closedu_level_expr 0)) in H; auto.
  apply_spec. now move=> x /(closedu_subst_instance_level_expr u).
Qed.
Hint Resolve closedu_subst_instance_level_expr closedu_subst_instance_level closedu_subst_instance_univ : terms.

Lemma closedu_subst_instance_instance u t : closedu_instance 0 t -> subst_instance_instance u t = t.
Proof.
  rewrite /closedu_instance /subst_instance_instance => H.
  eapply (forallb_Forall (closedu_level 0)) in H; auto.
  apply_spec. now move=> x /(closedu_subst_instance_level u).
Qed.
Hint Resolve closedu_subst_instance_instance : terms.

Lemma closedu_subst_instance_constr u t : closedu 0 t -> subst_instance_constr u t = t.
Proof.
  induction t in |- * using term_forall_list_ind; simpl; auto; intros H';
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length;
    try f_equal; eauto with terms;
    try rewrite -> !andb_and in *; try intuition eauto with terms;
    try solve [f_equal; eauto; merge_Forall; apply_spec; intuition eauto with terms].

  - red in H. merge_Forall. apply_spec.
    move => [ar t] /=; rewrite /on_snd /=; intuition eauto.
    now rewrite H.
  - red in H; merge_Forall; apply_spec.
    move => [na b ty] /=; rewrite /map_def /test_def /=; intuition try easy.
    rewrite -> !andb_true_iff in *.
    f_equal; intuition eauto.
  - red in H; merge_Forall; apply_spec.
    move => [na b ty] /=; rewrite /map_def /test_def /=; intuition try easy.
    rewrite -> !andb_true_iff in *.
    f_equal; intuition eauto.
Qed.

Section SubstInstanceClosed.
  Context (u : universe_instance) (Hcl : closedu_instance 0 u).

  Lemma forallb_nth {A} (l : list A) (n : nat) P d :
    forallb P l -> n < #|l| -> exists x, (nth n l d = x) /\ P x.
  Proof.
    induction l in n |- *; destruct n; simpl; auto; try easy.
    move/andP => [pa pl] pn. exists a; easy.
    move/andP => [pa pl] pn. specialize (IHl n pl).
    forward IHl. lia. auto.
  Qed.

  Lemma subst_instance_level_closedu t : closedu_level #|u| t -> closedu_level 0 (subst_instance_level u t).
  Proof.
    destruct t => /=; auto.
    move/Nat.ltb_spec0. intro H.
    red in Hcl. unfold closedu_instance in Hcl.
    eapply forallb_nth in Hcl; eauto. destruct Hcl as [x [Hn Hx]]. now rewrite -> Hn.
  Qed.

  Lemma subst_instance_level_expr_closedu t :
    closedu_level_expr #|u| t -> closedu_level_expr 0 (subst_instance_level_expr u t).
  Proof.
    destruct t as [l n].
    rewrite /closedu_level_expr /subst_instance_level_expr /=.
    move/(subst_instance_level_closedu) => //.
  Qed.

  Lemma subst_instance_univ_closedu t : closedu_universe #|u| t -> closedu_universe 0 (subst_instance_univ u t).
  Proof.
    rewrite /closedu_universe /subst_instance_univ => H.
    eapply (forallb_Forall (closedu_level_expr #|u|)) in H; auto.
    rewrite forallb_map. eapply Forall_forallb; eauto.
    now move=> x /(subst_instance_level_expr_closedu).
  Qed.
  Hint Resolve subst_instance_level_expr_closedu subst_instance_level_closedu subst_instance_univ_closedu : terms.

  Lemma subst_instance_instance_closedu t :
    closedu_instance #|u| t -> closedu_instance 0 (subst_instance_instance u t).
  Proof.
    rewrite /closedu_instance /subst_instance_instance => H.
    eapply (forallb_Forall (closedu_level #|u|)) in H; auto.
    rewrite forallb_map. eapply Forall_forallb; eauto.
    simpl. now move=> x /(subst_instance_level_closedu).
  Qed.
  Hint Resolve subst_instance_instance_closedu : terms.

  Lemma subst_instance_constr_closedu t :
    closedu #|u| t -> closedu 0 (subst_instance_constr u t).
  Proof.
    induction t in |- * using term_forall_list_ind; simpl; auto; intros H';
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length, ?forallb_map;
    try f_equal; auto with terms;
    try rewrite -> !andb_and in *; try intuition auto with terms;
    try solve [f_equal; eauto; merge_Forall; apply_spec; intuition auto with terms].

    - merge_Forall. apply_spec.
      intros [na b ty]; unfold test_def, compose; simpl; intuition;
        rewrite -> andb_true_iff in *; simpl; intuition auto.
    - merge_Forall. apply_spec.
      intros [na b ty]; unfold test_def, compose; simpl; intuition;
        rewrite -> andb_true_iff in *; simpl; intuition auto.
  Qed.
End SubstInstanceClosed.
