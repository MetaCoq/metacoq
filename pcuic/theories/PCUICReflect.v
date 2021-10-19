(* Distributed under the terms of the MIT license. *)
Require Import ssreflect.
From Equations Require Import Equations.

From MetaCoq.PCUIC Require Import PCUICAst PCUICInduction.
From MetaCoq.Template Require Import utils.
From MetaCoq.Template Require Export Reflect.

Open Scope pcuic.


Local Ltac finish :=
  let h := fresh "h" in
  right ;
  match goal with
  | e : ?t <> ?u |- _ =>
    intro h ; apply e ; now inversion h
  end.

Local Ltac fcase c :=
  let e := fresh "e" in
  case c ; intro e ; [ subst ; try (left ; reflexivity) | finish ].

Local Ltac term_dec_tac term_dec :=
  repeat match goal with
         | t : term, u : term |- _ => fcase (term_dec t u)
         | u : Universe.t, u' : Universe.t |- _ => fcase (eq_dec u u')
         | x : Instance.t, y : Instance.t |- _ =>
           fcase (eq_dec x y)
         | x : list Level.t, y : Instance.t |- _ =>
           fcase (eq_dec x y)
         | x : list aname, y : list aname |- _ => fcase (eq_dec x y)
         | n : nat, m : nat |- _ => fcase (Nat.eq_dec n m)
         | i : ident, i' : ident |- _ => fcase (string_dec i i')
         | i : kername, i' : kername |- _ => fcase (kername_eq_dec i i')
         | i : string, i' : kername |- _ => fcase (string_dec i i')
         | n : name, n' : name |- _ => fcase (eq_dec n n')
         | n : aname, n' : aname |- _ => fcase (eq_dec n n')
         | i : prim_val, j : prim_val |- _ => fcase (eq_dec i j)
         | i : inductive, i' : inductive |- _ => fcase (eq_dec i i')
         | x : inductive * nat, y : inductive * nat |- _ =>
           fcase (eq_dec x y)
         | x : case_info, y : case_info |- _ =>
           fcase (eq_dec x y)
         | x : projection, y : projection |- _ => fcase (eq_dec x y)
         end.

Derive NoConfusion NoConfusionHom for term.

Lemma eq_dec_ctx_IH ctx :
  onctx (fun x : term => forall y : term, {x = y} + {x <> y}) ctx ->
  forall ctx',
    {ctx = ctx'} + {ctx <> ctx'}.
Proof.
  induction 1.
  - intros []; [left; reflexivity|right; discriminate].
  - intros []; [right; discriminate|].
    destruct p as [pty pbod].
    destruct x as [xna [xbod|] xty]; cbn in *.
    destruct c as [cname [cbod|] cty]; cbn in *; nodec.
    fcase (eq_dec xna cname).
    destruct (pty cty) ; nodec.
    destruct (pbod cbod); nodec.
    destruct (IHX l0) ; nodec.
    subst; left; reflexivity.
    destruct c as [cname [cbod|] cty]; cbn in *; nodec.
    fcase (eq_dec xna cname).
    destruct (pty cty) ; nodec.
    destruct (IHX l0) ; nodec.
    subst; left; reflexivity.
Qed.

#[global]
Instance EqDec_term : EqDec term.
Proof.
  intro x; induction x using term_forall_list_ind ; intro t ;
    destruct t ; try (right ; discriminate).
  all: term_dec_tac term_dec.
  - revert l0. rename X into H; induction H ; intro l0.
    + destruct l0.
      * left. reflexivity.
      * right. discriminate.
    + destruct l0.
      * right. discriminate.
      * destruct (IHAll l0) ; nodec.
        destruct (p t) ; nodec.
        subst. left. inversion e. reflexivity.
  - destruct (IHx1 t1) ; nodec.
    destruct (IHx2 t2) ; nodec.
    subst. left. reflexivity.
  - destruct (IHx1 t1) ; nodec.
    destruct (IHx2 t2) ; nodec.
    subst. left. reflexivity.
  - destruct (IHx1 t1) ; nodec.
    destruct (IHx2 t2) ; nodec.
    destruct (IHx3 t3) ; nodec.
    subst. left. reflexivity.
  - destruct (IHx1 t1) ; nodec.
    destruct (IHx2 t2) ; nodec.
    subst. left. reflexivity.
  - destruct (IHx t) ; nodec. subst x. clear IHx.
    destruct p, p0; subst; cbn.
    term_dec_tac term_dec.
    destruct X as (?&?&?).
    destruct (s preturn0); cbn in * ; nodec.
    subst.
    assert ({pparams = pparams0} + {pparams <> pparams0}) as []; nodec.
    { revert pparams0.
      clear -a.
      induction a.
      - intros []; [left; reflexivity|right; discriminate].
      - intros []; [right; discriminate|].
        destruct (p t) ; nodec.
        destruct (IHa l0) ; nodec.
        subst; left; reflexivity. }
    subst.
    assert ({pcontext = pcontext0} + {pcontext <> pcontext0}) as []; nodec.
    { revert pcontext0. now apply eq_dec_ctx_IH. }
    subst pcontext.
    revert brs. clear -X0.
    induction X0 ; intro l0.
    + destruct l0.
      * left. reflexivity.
      * right. discriminate.
    + destruct l0.
      * right. discriminate.
      * destruct (IHX0 l0) ; nodec.
        destruct p as (hctx & hbod).
        destruct (hbod (bbody b)) ; nodec.
        assert ({bcontext x = bcontext b} + {bcontext x <> bcontext b}) as []; nodec.
        { now apply eq_dec_ctx_IH. }
        destruct x, b.
        left.
        cbn in *. subst. inversion e. reflexivity.
  - destruct (IHx t) ; nodec.
    left. subst. reflexivity.
  - revert mfix. induction X ; intro m0.
    + destruct m0.
      * left. reflexivity.
      * right. discriminate.
    + destruct p as [p1 p2].
      destruct m0.
      * right. discriminate.
      * destruct (p1 (dtype d)) ; nodec.
        destruct (p2 (dbody d)) ; nodec.
        destruct (IHX m0) ; nodec.
        destruct x, d ; subst. cbn in *.
        destruct (eq_dec dname dname0) ; nodec.
        subst. inversion e1. subst.
        destruct (eq_dec rarg rarg0) ; nodec.
        subst. left. reflexivity.
  - revert mfix. induction X ; intro m0.
    + destruct m0.
      * left. reflexivity.
      * right. discriminate.
    + destruct p as [p1 p2].
      destruct m0.
      * right. discriminate.
      * destruct (p1 (dtype d)) ; nodec.
        destruct (p2 (dbody d)) ; nodec.
        destruct (IHX m0) ; nodec.
        destruct x, d ; subst. cbn in *.
        destruct (eq_dec dname dname0) ; nodec.
        subst. inversion e1. subst.
        destruct (eq_dec rarg rarg0) ; nodec.
        subst. left. reflexivity.
Defined.

(** Avoid name clash with template's reflect term, namespace handlining bug in extraction. *)
#[global]
Instance reflect_pcuic_term : ReflectEq term :=
  let h := EqDec_ReflectEq term in _.

#[global]
Instance eqb_ctx : ReflectEq context := _.

#[global]
Instance eq_predicate : EqDec (predicate term).
Proof.
  intros [] [].
  fcase (eq_dec pparams pparams0).
  fcase (eq_dec puinst puinst0).
  fcase (eq_dec pcontext pcontext0).
  fcase (eq_dec preturn preturn0).
Defined.

Global Instance branch_eq_dec : EqDec (branch term).
Proof. ltac:(Equations.Prop.Tactics.eqdec_proof). Qed.

Definition eqb_context_decl (x y : context_decl) :=
  let (na, b, ty) := x in
  let (na', b', ty') := y in
  eqb na na' && eqb b b' && eqb ty ty'.

#[global]
Instance eq_ctx : ReflectEq context_decl.
Proof.
  refine {| eqb := eqb_context_decl |}.
  intros.
  destruct x as [na b ty], y as [na' b' ty']. cbn -[eqb].
  destruct (eqb_spec na na'); subst;
    destruct (eqb_spec b b'); subst;
      destruct (eqb_spec ty ty'); subst; constructor; congruence.
Qed.

#[global]
Instance reflect_eq_context : ReflectEq context := _.

Definition eqb_constant_body (x y : constant_body) :=
  let (tyx, bodyx, univx) := x in
  let (tyy, bodyy, univy) := y in
  eqb tyx tyy && eqb bodyx bodyy && eqb univx univy.

#[global]
Instance reflect_constant_body : ReflectEq constant_body.
Proof.
  refine {| eqb := eqb_constant_body |}.
  intros [] [].
  unfold eqb_constant_body; finish_reflect.
Defined.

Local Infix "==?" := eqb (at level 20).

Definition eqb_constructor_body (x y : constructor_body) :=
  x.(cstr_name) ==? y.(cstr_name) &&
  x.(cstr_args) ==? y.(cstr_args) &&
  x.(cstr_indices) ==? y.(cstr_indices) &&
  x.(cstr_type) ==? y.(cstr_type) &&
  x.(cstr_arity) ==? y.(cstr_arity).

#[global]
Instance reflect_constructor_body : ReflectEq constructor_body.
Proof.
  refine {| eqb := eqb_constructor_body |}.
  intros [] [].
  unfold eqb_constructor_body; cbn -[eqb]. finish_reflect.
Defined.
  
Definition eqb_one_inductive_body (x y : one_inductive_body) :=
  x.(ind_name) ==? y.(ind_name) &&
  x.(ind_indices) ==? y.(ind_indices) &&
  x.(ind_sort) ==? y.(ind_sort) &&
  x.(ind_type) ==? y.(ind_type) &&
  x.(ind_kelim) ==? y.(ind_kelim) &&
  x.(ind_ctors) ==? y.(ind_ctors) &&
  x.(ind_projs) ==? y.(ind_projs) &&
  x.(ind_relevance) ==? y.(ind_relevance).

#[global]
Instance reflect_one_inductive_body : ReflectEq one_inductive_body.
Proof.
  refine {| eqb := eqb_one_inductive_body |}.
  intros [] [].
  unfold eqb_one_inductive_body; cbn -[eqb]; finish_reflect.
Defined.

Definition eqb_mutual_inductive_body (x y : mutual_inductive_body) :=
  let (f, n, p, b, u, v) := x in
  let (f', n', p', b', u', v') := y in
  eqb f f' && eqb n n' && eqb b b' && eqb p p' && eqb u u' && eqb v v'.

#[global]
Instance reflect_mutual_inductive_body : ReflectEq mutual_inductive_body.
Proof.
  refine {| eqb := eqb_mutual_inductive_body |}.
  intros [] [].
  unfold eqb_mutual_inductive_body; finish_reflect.
Defined.

Definition eqb_global_decl x y :=
  match x, y with
  | ConstantDecl cst, ConstantDecl cst' => eqb cst cst'
  | InductiveDecl mib, InductiveDecl mib' => eqb mib mib'
  | _, _ => false
  end.

#[global]
Instance reflect_global_decl : ReflectEq global_decl.
Proof.
  refine {| eqb := eqb_global_decl |}.
  unfold eqb_global_decl.
  intros [] []; finish_reflect.
Defined.
