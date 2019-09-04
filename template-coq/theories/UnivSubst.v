(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From MetaCoq Require Import utils Ast AstUtils Induction LiftSubst.
Require Import String Lia.
Local Open Scope string_scope.
Set Asymmetric Patterns.
Require Import ssreflect ssrbool.

(** * Universe substitution

  *WIP*

  Substitution of universe levels for universe level variables, used to
  implement universe polymorphism. *)


(** Substitutable type *)

Class UnivSubst A := subst_instance : universe_instance -> A -> A.


Instance subst_instance_level : UnivSubst Level.t :=
  fun u l => match l with
          | Level.lProp | Level.lSet | Level.Level _ => l
          | Level.Var n => List.nth n u Level.lSet
          end.

Instance subst_instance_cstr : UnivSubst univ_constraint :=
  fun u c => (subst_instance_level u c.1.1, c.1.2, subst_instance_level u c.2).

Instance subst_instance_cstrs : UnivSubst constraints :=
  fun u ctrs => ConstraintSet.fold (fun c => ConstraintSet.add (subst_instance_cstr u c))
                                ctrs ConstraintSet.empty.

Instance subst_instance_level_expr : UnivSubst Universe.Expr.t :=
  fun u e => (subst_instance_level u e.1, e.2).

Instance subst_instance_univ : UnivSubst universe :=
  fun u s => NEL.map (subst_instance_level_expr u) s.

Instance subst_instance_instance : UnivSubst universe_instance :=
  fun u u' => List.map (subst_instance_level u) u'.

Instance subst_instance_constr : UnivSubst term :=
  fix subst_instance_constr u c {struct c} : term :=
  match c with
  | tRel _ | tVar _ => c
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

Instance subst_instance_context : UnivSubst context :=
  fun u c => AstUtils.map_context (subst_instance_constr u) c.

Lemma lift_subst_instance_constr u c n k :
  lift n k (subst_instance_constr u c) = subst_instance_constr u (lift n k c).
Proof.
  induction c in k |- * using term_forall_list_ind; simpl; auto;
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length;
    try solve [f_equal; eauto; solve_all; eauto].

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
  rewrite IHctx /= /mkProd_or_LetIn /=. f_equal. destruct (decl_body a); eauto.
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
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length;
    try solve [f_equal; eauto; solve_all; eauto].

  elim (Nat.leb k n). rewrite nth_error_map.
  destruct (nth_error N (n - k)). simpl.
  apply lift_subst_instance_constr. reflexivity. reflexivity.

  rewrite subst_instance_constr_mkApps. f_equal; auto.
  rewrite map_map_compose. solve_all.
Qed.

Lemma map_subst_instance_constr_to_extended_list_k u ctx k :
  map (subst_instance_constr u) (to_extended_list_k ctx k)
  = to_extended_list_k ctx k.
Proof.
  pose proof (to_extended_list_k_spec ctx k).
  solve_all. now destruct H as [n [-> _]].
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

(** Universe-closed terms are unaffected by universe substitution. *)

Section UniverseClosedSubst.
  Lemma closedu_subst_instance_level u t
  : closedu_level 0 t -> subst_instance_level u t = t.
  Proof.
    destruct t => /=; auto.
    move/Nat.ltb_spec0. intro H. inversion H.
  Qed.

  Lemma closedu_subst_instance_level_expr u t
    : closedu_level_expr 0 t -> subst_instance_level_expr u t = t.
  Proof.
    destruct t as [l n].
    rewrite /closedu_level_expr /subst_instance_level_expr /=.
    move/(closedu_subst_instance_level u) => //. congruence.
  Qed.

  Lemma closedu_subst_instance_univ u t
    : closedu_universe 0 t -> subst_instance_univ u t = t.
  Proof.
    rewrite /closedu_universe /subst_instance_univ => H.
    pose proof (proj1 (forallb_forall _ t) H) as HH; clear H.
    induction t; cbn; f_equal.
    1-2: now apply closedu_subst_instance_level_expr, HH; cbn.
    apply IHt. intros x Hx; apply HH. now right.
  Qed.
  Hint Resolve closedu_subst_instance_level_expr closedu_subst_instance_level closedu_subst_instance_univ : terms.

  Lemma closedu_subst_instance_instance u t
    : closedu_instance 0 t -> subst_instance_instance u t = t.
  Proof.
    rewrite /closedu_instance /subst_instance_instance => H. solve_all.
    now apply (closedu_subst_instance_level u).
  Qed.
  Hint Resolve closedu_subst_instance_instance : terms.

  Lemma closedu_subst_instance_constr u t
    : closedu 0 t -> subst_instance_constr u t = t.
  Proof.
    induction t in |- * using term_forall_list_ind; simpl; auto; intros H';
      rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length;
      try f_equal; eauto with terms; unfold test_def in *;
        try solve [f_equal; eauto; repeat (toProp; solve_all)].
  Qed.
End UniverseClosedSubst.

Section SubstInstanceClosed.
  (** Substitution of a universe-closed instance of the right size 
      produces a universe-closed term. *)

  Context (u : universe_instance) (Hcl : closedu_instance 0 u).

  Lemma subst_instance_level_closedu t
    : closedu_level #|u| t -> closedu_level 0 (subst_instance_level u t).
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

  Lemma subst_instance_univ_closedu t
    : closedu_universe #|u| t -> closedu_universe 0 (subst_instance_univ u t).
  Proof.
    rewrite /closedu_universe /subst_instance_univ => H.
    eapply (forallb_Forall (closedu_level_expr #|u|)) in H; auto.
    unfold universe_coercion; rewrite NEL.map_to_list forallb_map.
    eapply Forall_forallb; eauto.
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
    unfold test_def, map_def, compose in *;
    try solve [f_equal; eauto; repeat (toProp; solve_all); intuition auto with terms].
  Qed.
End SubstInstanceClosed.
