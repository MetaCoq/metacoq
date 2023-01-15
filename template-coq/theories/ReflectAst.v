(* Distributed under the terms of the MIT license. *)
(* For primitive integers and floats  *)
From Coq Require Numbers.Cyclic.Int63.Uint63 Floats.PrimFloat Floats.FloatAxioms.
From MetaCoq.Template Require Import utils AstUtils BasicAst Ast Reflect Environment Induction.
Require Import ssreflect.
From Equations Require Import Equations.

Local Infix "==?" := eqb (at level 20).

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
         | x : list aname, y : list aname |- _ =>
           fcase (eq_dec x y)
         | n : nat, m : nat |- _ => fcase (Nat.eq_dec n m)
         | i : ident, i' : ident |- _ => fcase (eq_dec i i')
         | i : kername, i' : kername |- _ => fcase (eq_dec i i')
         | i : string, i' : kername |- _ => fcase (eq_dec i i')
         | n : name, n' : name |- _ => fcase (eq_dec n n')
         | n : aname, n' : aname |- _ => fcase (eq_dec n n')
         | i : inductive, i' : inductive |- _ => fcase (eq_dec i i')
         | x : inductive * nat, y : inductive * nat |- _ =>
           fcase (eq_dec x y)
         | x : case_info, y : case_info |- _ =>
           fcase (eq_dec x y)
         | x : projection, y : projection |- _ => fcase (eq_dec x y)
         | x : cast_kind, y : cast_kind |- _ => fcase (eq_dec x y)
         end.

#[global] Instance eq_predicate {term} `{EqDec term} : EqDec (predicate term).
Proof.
  intros [] [].
  fcase (eq_dec pparams pparams0).
  fcase (eq_dec puinst puinst0).
  fcase (eq_dec pcontext pcontext0).
  fcase (eq_dec preturn preturn0).
Defined.

Derive NoConfusion NoConfusionHom for term.

#[global] Instance EqDec_term : EqDec term.
Proof.
  intro x; induction x using term_forall_list_rect ; intro t ;
    destruct t ; try (right ; discriminate).
  all: term_dec_tac term_dec.
  - induction X in args |- *.
    + destruct args.
      * left. reflexivity.
      * right. discriminate.
    + destruct args.
      * right. discriminate.
      * destruct (IHX args) ; nodec.
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
    subst. left. reflexivity.
  - destruct (IHx1 t1) ; nodec.
    destruct (IHx2 t2) ; nodec.
    destruct (IHx3 t3) ; nodec.
    subst. left. reflexivity.
  - destruct (IHx t) ; nodec.
    subst. induction X in args |- *.
    + destruct args. all: nodec.
      left. reflexivity.
    + destruct args. all: nodec.
      destruct (IHX args). all: nodec.
      destruct (p t0). all: nodec.
      subst. inversion e. subst.
      left. reflexivity.
  - destruct (IHx t) ; nodec.
    destruct p0, type_info; subst; cbn.
    term_dec_tac term_dec.
    destruct X as (?&?).
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
    revert branches. clear -X0.
    induction X0 ; intro l0.
    + destruct l0.
      * left. reflexivity.
      * right. discriminate.
    + destruct l0.
      * right. discriminate.
      * destruct (IHX0 l0) ; nodec.
        destruct (p (bbody b)) ; nodec.
        destruct (eq_dec (bcontext x) (bcontext b)) ; nodec.
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
  - destruct (eq_dec i i0) ; nodec.
    subst. left. reflexivity.
  - destruct (eq_dec f f0) ; nodec.
    subst. left. reflexivity.
Defined.

#[global] Instance reflect_term : ReflectEq term :=
  let h := EqDec_ReflectEq term in _.

#[global] Instance eqb_ctx : ReflectEq context := _.

Definition eqb_constant_body (x y : constant_body) :=
  let (tyx, bodyx, univx, relx) := x in
  let (tyy, bodyy, univy, rely) := y in
  eqb tyx tyy && eqb bodyx bodyy && eqb univx univy && eqb relx rely.

#[global] Instance reflect_constant_body : ReflectEq constant_body.
Proof.
  refine {| eqb := eqb_constant_body |}.
  intros [] [].
  unfold eqb_constant_body; finish_reflect.
Defined.

Definition eqb_constructor_body (x y : constructor_body) :=
  x.(cstr_name) ==? y.(cstr_name) &&
  x.(cstr_args) ==? y.(cstr_args) &&
  x.(cstr_indices) ==? y.(cstr_indices) &&
  x.(cstr_type) ==? y.(cstr_type) &&
  x.(cstr_arity) ==? y.(cstr_arity).

#[global] Instance reflect_constructor_body : ReflectEq constructor_body.
Proof.
  refine {| eqb := eqb_constructor_body |}.
  intros [] [].
  unfold eqb_constructor_body; cbn -[eqb]. finish_reflect.
Defined.

Definition eqb_projection_body (x y : projection_body) :=
  x.(proj_name) ==? y.(proj_name) &&
  x.(proj_type) ==? y.(proj_type) &&
  x.(proj_relevance) ==? y.(proj_relevance).

#[global] Instance reflect_projection_body : ReflectEq projection_body.
Proof.
  refine {| eqb := eqb_projection_body |}.
  intros [] [].
  unfold eqb_projection_body; cbn -[eqb]; finish_reflect.
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

#[global] Instance reflect_one_inductive_body : ReflectEq one_inductive_body.
Proof.
  refine {| eqb := eqb_one_inductive_body |}.
  intros [] [].
  unfold eqb_one_inductive_body; cbn -[eqb]; finish_reflect.
Defined.

Definition eqb_mutual_inductive_body (x y : mutual_inductive_body) :=
  let (f, n, p, b, u, v) := x in
  let (f', n', p', b', u', v') := y in
  eqb f f' && eqb n n' && eqb b b' && eqb p p' && eqb u u' && eqb v v'.

#[global] Instance reflect_mutual_inductive_body : ReflectEq mutual_inductive_body.
Proof.
  refine {| eqb := eqb_mutual_inductive_body |}.
  intros [] [].
  unfold eqb_mutual_inductive_body; finish_reflect.
Defined.

Fixpoint eqb_structure_field (sf sf': structure_field) {struct sf}:=
  match sf, sf' with
  | sfconst c, sfconst c' => c ==? c'
  | sfmind m, sfmind m' => m ==? m'
  | sfmod mi mt, sfmod mi' mt' => eqb_module_impl mi mi' && eqb_module_type_decl mt mt'
  | sfmodtype mt, sfmodtype mt' => eqb_module_type_decl mt mt'
  | _, _ => false
  end
with eqb_module_impl (mi mi': module_implementation) {struct mi}:=
  match mi, mi' with
  | mi_abstract, mi_abstract | mi_fullstruct, mi_fullstruct => true
  | mi_algebraic kn, mi_algebraic kn' => kn ==? kn'
  | mi_struct mt, mi_struct mt' => eqb_module_type_decl mt mt'
  | _, _ => false
  end
with eqb_module_type_decl (mt mt': module_type_decl) {struct mt} :=
  match mt, mt' with
  | sb_nil, sb_nil => true
  | sb_cons k sf sb, sb_cons k' sf' sb' =>
      k ==? k' && eqb_structure_field sf sf' && eqb_module_type_decl sb sb'
  | _, _ => false
  end.

Lemma reflect_sf_mi_sb:
(forall f f': structure_field, reflectProp (f = f') (eqb_structure_field f f')) ×
(forall m m': module_implementation, reflectProp (m = m') (eqb_module_impl m m')) ×
(forall s s': structure_body, reflectProp (s = s') (eqb_module_type_decl s s')).
Proof.
  apply sf_mi_sb_mutind; intros.
  - destruct f'; simpl; try now constructor. destruct (eqb_spec c c0); now constructor.
  - destruct f'; simpl; try now constructor. destruct (eqb_spec m m0); now constructor.
  - destruct f'; simpl; try now constructor.
    destruct (H m0), (H0 s0); simpl; now constructor.
  - destruct f'; simpl; try now constructor.
    destruct (H s0); simpl; now constructor.
  - destruct m'; simpl; now constructor.
  - destruct m'; simpl; try now constructor.
    destruct (eqb_spec k k0); now constructor.
  - destruct m'; simpl; try now constructor.
    destruct (H s0); simpl; now constructor.
  - destruct m'; simpl; now constructor.
  - destruct s'; simpl; now constructor.
  - destruct s'; simpl; try now constructor.
    destruct (eqb_spec i i0), (H s1), (H0 s'); simpl; now constructor.
Qed.

#[global] Instance reflect_structure_field : ReflectEq structure_field :=
{ eqb := eqb_structure_field ; eqb_spec := reflect_sf_mi_sb.1 }.

#[global] Instance reflect_module_impl : ReflectEq module_implementation :=
{ eqb := eqb_module_impl ; eqb_spec := reflect_sf_mi_sb.2.1 }.

#[global] Instance reflect_structure_body : ReflectEq structure_body :=
{ eqb := eqb_module_type_decl ; eqb_spec := reflect_sf_mi_sb.2.2 }.

#[global] Instance reflect_module_type : ReflectEq module_type_decl :=
{ eqb := eqb_module_type_decl ; eqb_spec := reflect_sf_mi_sb.2.2 }.

Definition eqb_module_decl (m m': module_decl) := (m.1 ==? m'.1) && (m.2 ==? m'.2).

#[global] Instance reflect_module_decl : ReflectEq module_decl.
Proof.
  refine {| eqb := eqb_module_decl |}.
  intros [] [].
  unfold eqb_module_decl; cbn -[eqb]; finish_reflect.
Qed.

Definition eqb_global_decl x y :=
  match x, y with
  | ConstantDecl cst, ConstantDecl cst' => eqb cst cst'
  | InductiveDecl mib, InductiveDecl mib' => eqb mib mib'
  | ModuleDecl m, ModuleDecl m' => eqb m m'
  | ModuleTypeDecl mt, ModuleTypeDecl mt' => eqb mt mt'
  | _, _ => false
  end.

#[global] Instance reflect_global_decl : ReflectEq global_decl.
Proof.
  refine {| eqb := eqb_global_decl |}.
  unfold eqb_global_decl.
  intros [] []; finish_reflect.
Defined.
