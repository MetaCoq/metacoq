(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import utils Ast AstUtils univ Induction LiftSubst.
Require Import String.
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