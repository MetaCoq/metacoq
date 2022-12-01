(* Distributed under the terms of the MIT license. *)
From Coq Require Import CMorphisms.
From MetaCoq.Template Require Import LibHypsNaming config utils Reflect.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICReflect.

Require Import ssreflect ssrbool.
From Equations.Prop Require Import DepElim.
From Equations Require Import Equations.
Set Equations With UIP.

Ltac pcuic :=
  try repeat red; cbn in *;
   try (solve [ intuition auto; eauto with pcuic || (try lia || congruence) ]).

#[global]
Instance All2_fold_len {A} P (Γ Δ : list A) : HasLen (All2_fold P Γ Δ) #|Γ| #|Δ| :=
  All2_fold_length.

Implicit Types (cf : checker_flags).

Definition R_universe_instance R :=
  fun u u' => Forall2 R (List.map Universe.make u) (List.map Universe.make u').

(** Cumulative inductive types:

  To simplify the development, we allow the variance list to not exactly
  match the instances, so as to keep syntactic ws_cumul_pb an equivalence relation
  even on ill-formed terms. It corresponds to the right notion on well-formed terms.
*)

Definition R_universe_variance (Re Rle : Universe.t -> Universe.t -> Prop) v u u' :=
  match v with
  | Variance.Irrelevant => True
  | Variance.Covariant => Rle (Universe.make u) (Universe.make u')
  | Variance.Invariant => Re (Universe.make u) (Universe.make u')
  end.

Fixpoint R_universe_instance_variance Re Rle v u u' :=
  match u, u' return Prop with
  | u :: us, u' :: us' =>
    match v with
    | [] => R_universe_instance_variance Re Rle v us us'
      (* Missing variance stands for irrelevance, we still check that the instances have
        the same length. *)
    | v :: vs => R_universe_variance Re Rle v u u' /\
        R_universe_instance_variance Re Rle vs us us'
    end
  | [], [] => True
  | _, _ => False
  end.

Definition global_variance_gen lookup gr napp :=
  match gr with
  | IndRef ind =>
    match lookup_inductive_gen lookup ind with
    | Some (mdecl, idecl) =>
      match destArity [] idecl.(ind_type) with
      | Some (ctx, _) => if (context_assumptions ctx) <=? napp then mdecl.(ind_variance)
        else None
      | None => None
      end
    | None => None
    end
  | ConstructRef ind k =>
    match lookup_constructor_gen lookup ind k with
    | Some (mdecl, idecl, cdecl) =>
      if (cdecl.(cstr_arity) + mdecl.(ind_npars))%nat <=? napp then
        (** Fully applied constructors are always compared at the same supertype,
          which implies that no universe ws_cumul_pb needs to be checked here. *)
        Some []
      else None
    | _ => None
    end
  | _ => None
  end.

Notation global_variance Σ := (global_variance_gen (lookup_env Σ)).

Definition R_opt_variance Re Rle v :=
  match v with
  | Some v => R_universe_instance_variance Re Rle v
  | None => R_universe_instance Re
  end.

Definition R_global_instance_gen Σ Re Rle gr napp :=
  R_opt_variance Re Rle (global_variance_gen Σ gr napp).

Notation R_global_instance Σ := (R_global_instance_gen (lookup_env Σ)).

Definition R_ind_universes {cf:checker_flags} (Σ : global_env_ext) ind n i i' :=
  R_global_instance Σ (eq_universe (global_ext_constraints Σ))
    (leq_universe (global_ext_constraints Σ)) (IndRef ind) n i i'.

Lemma R_universe_instance_impl R R' :
  RelationClasses.subrelation R R' ->
  RelationClasses.subrelation (R_universe_instance R) (R_universe_instance R').
Proof.
  intros H x y xy. eapply Forall2_impl ; tea.
Qed.

Lemma R_universe_instance_impl' R R' :
  RelationClasses.subrelation R R' ->
  forall u u', R_universe_instance R u u' -> R_universe_instance R' u u'.
Proof.
  intros H x y xy. eapply Forall2_impl ; tea.
Qed.

Section compare_decls.
  (* leq_term compares types, eq_term bodies:
    - For conversion they are both equality
    - For cumulativity only the type are compared using leq.
  *)
  Context {eq_term leq_term : term -> term -> Type}.
  Inductive compare_decls  : context_decl -> context_decl -> Type :=
  | compare_vass {na T na' T'} :
    eq_binder_annot na na' ->
    leq_term T T' ->
    compare_decls (vass na T) (vass na' T')
  | compare_vdef {na b T na' b' T'} :
    eq_binder_annot na na' ->
    eq_term b b' ->
    leq_term T T' ->
    compare_decls (vdef na b T) (vdef na' b' T').

  Derive Signature NoConfusion for compare_decls.
End compare_decls.
Arguments compare_decls : clear implicits.

Notation eq_context_upto_names := (All2 (compare_decls eq eq)).

Notation eq_context_gen eq_term leq_term :=
  (All2_fold (fun _ _ => compare_decls eq_term leq_term)).

Lemma eq_context_upto_names_gen Γ Γ' : eq_context_upto_names Γ Γ' <~> eq_context_gen eq eq Γ Γ'.
Proof.
  split; intros e; depind e; constructor; auto.
Qed.

Lemma compare_decls_impl eq_term leq_term eq_term' leq_term' :
  subrelation eq_term eq_term' ->
  subrelation leq_term leq_term' ->
  subrelation (compare_decls eq_term leq_term)
    (compare_decls eq_term' leq_term').
Proof.
  intros he hle x y []; constructor; auto.
Qed.

Lemma eq_context_gen_impl eq_term leq_term eq_term' leq_term' :
  subrelation eq_term eq_term' ->
  subrelation leq_term leq_term' ->
  subrelation (eq_context_gen eq_term leq_term) (eq_context_gen eq_term' leq_term').
Proof.
  intros he hle x y eq.
  eapply All2_fold_impl; tea => /=.
  intros; eapply compare_decls_impl; tea.
Qed.

Lemma compare_decl_impl_ondecl P eq_term leq_term eq_term' leq_term' d d' :
  ondecl P d ->
  (forall x y, P x -> eq_term x y -> eq_term' x y) ->
  (forall x y, P x -> leq_term x y -> leq_term' x y) ->
  compare_decls eq_term leq_term d d' ->
  compare_decls eq_term' leq_term' d d'.
Proof.
  intros ond he hle cd; depelim cd; depelim ond; constructor => //; eauto.
Qed.

Lemma compare_decl_map eq_term leq_term f g d d' :
  compare_decls (fun x y => eq_term (f x) (g y))
    (fun x y => leq_term (f x) (g y)) d d' ->
  compare_decls eq_term leq_term (map_decl f d) (map_decl g d').
Proof.
  intros h; depelim h; constructor; intuition auto.
Qed.

Definition bcompare_decls (eq_term leq_term : term -> term -> bool) (d d' : context_decl) : bool :=
  match d, d' with
  | {| decl_name := na; decl_body := None; decl_type := T |},
    {| decl_name := na'; decl_body := None; decl_type := T' |} =>
    eqb_binder_annot na na' && leq_term T T'
  | {| decl_name := na; decl_body := Some b; decl_type := T |},
    {| decl_name := na'; decl_body := Some b'; decl_type := T' |} =>
    eqb_binder_annot na na' && eq_term b b' && leq_term T T'
  | _, _ => false
  end.

#[global]
Polymorphic Instance compare_decl_refl eq_term leq_term :
  CRelationClasses.Reflexive eq_term ->
  CRelationClasses.Reflexive leq_term ->
  CRelationClasses.Reflexive (compare_decls eq_term leq_term).
Proof.
  intros heq hle d.
  destruct d as [na [b|] ty]; constructor; auto; reflexivity.
Qed.

#[global]
Polymorphic Instance compare_decl_sym eq_term leq_term :
  CRelationClasses.Symmetric eq_term ->
  CRelationClasses.Symmetric leq_term ->
  CRelationClasses.Symmetric (compare_decls eq_term leq_term).
Proof.
  intros heq hle d d' []; constructor; auto; now symmetry.
Qed.

#[global]
Polymorphic Instance compare_decl_trans eq_term leq_term :
  CRelationClasses.Transitive eq_term ->
  CRelationClasses.Transitive leq_term ->
  CRelationClasses.Transitive (compare_decls eq_term leq_term).
Proof.
  intros hle hre x y z h h'; depelim h; depelim h'; constructor; auto;
  etransitivity; eauto.
Qed.

#[global]
Instance alpha_eq_reflexive : CRelationClasses.Reflexive eq_context_upto_names.
Proof.
  intros x. eapply All2_refl. reflexivity.
Qed.

#[global]
Instance alpha_eq_symmmetric : CRelationClasses.Symmetric eq_context_upto_names.
Proof.
  intros x. eapply All2_symP. tc.
Qed.

#[global]
Instance alpha_eq_trans : CRelationClasses.Transitive eq_context_upto_names.
Proof.
  intros x y z. apply All2_trans. tc.
Qed.

#[global]
Polymorphic Instance eq_context_refl eq_term leq_term :
  CRelationClasses.Reflexive eq_term ->
  CRelationClasses.Reflexive leq_term ->
  CRelationClasses.Reflexive (eq_context_gen eq_term leq_term).
Proof.
  intros heq hle x.
  eapply All2_fold_refl.
  intros. reflexivity.
Qed.

#[global]
Polymorphic Instance eq_context_sym eq_term leq_term :
  CRelationClasses.Symmetric eq_term ->
  CRelationClasses.Symmetric leq_term ->
  CRelationClasses.Symmetric (eq_context_gen eq_term leq_term).
Proof.
  intros heq hle x.
  eapply All2_fold_sym.
  intros. now symmetry.
Qed.

#[global]
Polymorphic Instance eq_context_trans eq_term leq_term :
  CRelationClasses.Transitive eq_term ->
  CRelationClasses.Transitive leq_term ->
  CRelationClasses.Transitive (eq_context_gen eq_term leq_term).
Proof.
  intros hr x y z.
  eapply All2_fold_trans; intros.
  now transitivity y0.
Qed.

Definition eq_predicate (eq_term : term -> term -> Type) Re p p' :=
  All2 eq_term p.(pparams) p'.(pparams) *
  (R_universe_instance Re p.(puinst) p'.(puinst) *
  ((eq_context_gen eq eq p.(pcontext) p'.(pcontext)) *
    eq_term p.(preturn) p'.(preturn))).

(** ** Syntactic ws_cumul_pb up-to universes
  We don't look at printing annotations *)

(** ws_cumul_pb is indexed by a natural number that counts the number of applications
  that surround the current term, used to implement cumulativity of inductive types
  correctly (only fully applied constructors and inductives benefit from it). *)

Reserved Notation " Σ ⊢ t <==[ Rle , napp ] u" (at level 50, t, u at next level,
  format "Σ  ⊢  t  <==[ Rle , napp ]  u").


Inductive eq_term_upto_univ_napp Σ (Re Rle : Universe.t -> Universe.t -> Prop) (napp : nat) : term -> term -> Type :=
| eq_Rel : forall n,
    Σ ⊢ tRel n <==[ Rle , napp ] tRel n

| eq_Evar : forall e args args',
    All2 (eq_term_upto_univ_napp Σ Re Re 0) args args' ->
    Σ ⊢ tEvar e args <==[ Rle , napp ] tEvar e args'

| eq_Var : forall id,
    Σ ⊢ tVar id <==[ Rle , napp ] tVar id

| eq_Sort : forall s s',
    Rle s s' ->
    Σ ⊢ tSort s  <==[ Rle , napp ] tSort s'

| eq_App : forall t t' u u',
    Σ ⊢ t <==[ Rle , S napp ] t' ->
    Σ ⊢ u <==[ Re , 0 ] u' ->
    Σ ⊢ tApp t u <==[ Rle , napp ] tApp t' u'

| eq_Const : forall c u u',
    R_universe_instance Re u u' ->
    Σ ⊢ tConst c u <==[ Rle , napp ] tConst c u'

| eq_Ind : forall i u u',
    R_global_instance Σ Re Rle (IndRef i) napp u u' ->
    Σ ⊢ tInd i u <==[ Rle , napp ] tInd i u'

| eq_Construct : forall i k u u',
    R_global_instance Σ Re Rle (ConstructRef i k) napp u u' ->
    Σ ⊢ tConstruct i k u <==[ Rle , napp ] tConstruct i k u'

| eq_Lambda : forall na na' ty ty' t t',
    eq_binder_annot na na' ->
    Σ ⊢ ty <==[ Re , 0 ] ty' ->
    Σ ⊢ t <==[ Rle , 0 ] t' ->
    Σ ⊢ tLambda na ty t <==[ Rle , napp ] tLambda na' ty' t'

| eq_Prod : forall na na' a a' b b',
    eq_binder_annot na na' ->
    Σ ⊢ a <==[ Re , 0 ] a' ->
    Σ ⊢ b <==[ Rle , 0 ] b' ->
    Σ ⊢ tProd na a b <==[ Rle , napp ] tProd na' a' b'

| eq_LetIn : forall na na' t t' ty ty' u u',
    eq_binder_annot na na' ->
    Σ ⊢ t <==[ Re , 0 ] t' ->
    Σ ⊢ ty <==[ Re , 0 ] ty' ->
    Σ ⊢ u <==[ Rle , 0 ] u' ->
    Σ ⊢ tLetIn na t ty u <==[ Rle , napp ] tLetIn na' t' ty' u'

| eq_Case : forall indn p p' c c' brs brs',
    eq_predicate (eq_term_upto_univ_napp Σ Re Re 0) Re p p' ->
    Σ ⊢ c <==[ Re , 0 ] c' ->
    All2 (fun x y =>
      eq_context_gen eq eq (bcontext x) (bcontext y) *
      (Σ ⊢ x.(bbody) <==[ Re , 0 ] y.(bbody))
    ) brs brs' ->
    Σ ⊢ tCase indn p c brs <==[ Rle , napp ] tCase indn p' c' brs'

| eq_Proj : forall p c c',
    Σ ⊢ c <==[ Re , 0 ] c' ->
    Σ ⊢ tProj p c <==[ Rle , napp ] tProj p c'

| eq_Fix : forall mfix mfix' idx,
    All2 (fun x y =>
      (Σ ⊢ x.(dtype) <==[ Re , 0 ] y.(dtype)) *
      (Σ ⊢ x.(dbody) <==[ Re , 0 ] y.(dbody)) *
      (x.(rarg) = y.(rarg)) *
      eq_binder_annot x.(dname) y.(dname)
    )%type mfix mfix' ->
    Σ ⊢ tFix mfix idx <==[ Rle , napp ] tFix mfix' idx

| eq_CoFix : forall mfix mfix' idx,
    All2 (fun x y =>
      (Σ ⊢ x.(dtype) <==[ Re , 0 ] y.(dtype)) *
      (Σ ⊢ x.(dbody) <==[ Re , 0 ] y.(dbody)) *
      (x.(rarg) = y.(rarg)) *
      eq_binder_annot x.(dname) y.(dname)
    ) mfix mfix' ->
    Σ ⊢ tCoFix mfix idx <==[ Rle , napp ] tCoFix mfix' idx

| eq_Prim i : eq_term_upto_univ_napp Σ Re Rle napp (tPrim i) (tPrim i)
where " Σ ⊢ t <==[ Rle , napp ] u " := (eq_term_upto_univ_napp Σ _ Rle napp t u) : type_scope.

Notation eq_term_upto_univ Σ Re Rle := (eq_term_upto_univ_napp Σ Re Rle 0).

(* ** Syntactic conparison up-to universes *)

Definition compare_term_napp `{checker_flags} (pb : conv_pb) Σ φ napp (t u : term) :=
  eq_term_upto_univ_napp Σ (eq_universe φ) (compare_universe pb φ) napp t u.

Definition compare_term `{checker_flags} (pb : conv_pb) Σ φ (t u : term) :=
  eq_term_upto_univ Σ (eq_universe φ) (compare_universe pb φ) t u.

(* ** Syntactic conversion up-to universes *)

Notation eq_term := (compare_term Conv).

(* ** Syntactic cumulativity up-to universes *)

Notation leq_term := (compare_term Cumul).

Definition compare_opt_term `{checker_flags} (pb : conv_pb) Σ φ (t u : option term) :=
  match t, u with
  | Some t, Some u => compare_term pb Σ φ t u
  | None, None => True
  | _, _ => False
  end.

Definition compare_decl `{checker_flags} pb Σ φ (d d' : context_decl) :=
  compare_decls (compare_term Conv Σ φ) (compare_term pb Σ φ) d d'.

Notation eq_decl := (compare_decl Conv).
Notation leq_decl := (compare_decl Cumul).

Definition compare_context `{checker_flags} pb Σ φ (Γ Δ : context) :=
  eq_context_gen (compare_term Conv Σ φ) (compare_term pb Σ φ) Γ Δ.

Notation eq_context := (compare_context Conv).
Notation leq_context := (compare_context Cumul).

Notation eq_context_upto Σ Re Rle :=
  (eq_context_gen (eq_term_upto_univ Σ Re Re) (eq_term_upto_univ Σ Re Rle)).

Lemma R_global_instance_refl Σ Re Rle gr napp u :
  RelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Rle ->
  R_global_instance Σ Re Rle gr napp u u.
Proof.
  intros rRE rRle.
  unfold R_global_instance_gen.
  destruct global_variance_gen as [v|] eqn:lookup.
  - induction u in v |- *; simpl; auto;
    unfold R_opt_variance in IHu; destruct v; simpl; auto.
    split; auto.
    destruct t; simpl; auto.
  - apply Forall2_same; eauto.
Qed.

#[global]
Instance eq_binder_annot_equiv {A} : RelationClasses.Equivalence (@eq_binder_annot A A).
Proof.
  split.
  - red. reflexivity.
  - red; now symmetry.
  - intros x y z; unfold eq_binder_annot.
    apply transitivity.
Qed.

Definition eq_binder_annot_refl {A} x : @eq_binder_annot A A x x.
Proof. reflexivity. Qed.

#[global]
Hint Resolve eq_binder_annot_refl : core.

(* TODO MOVE *)
#[global]
Existing Instance All2_symP.

(* TODO MOVE *)
#[global]
Instance Forall2_symP :
  forall A (P : A -> A -> Prop),
    RelationClasses.Symmetric P ->
    Symmetric (Forall2 P).
Proof.
  intros A P h l l' hl.
  induction hl. all: auto.
Qed.

Lemma eq_binder_relevances_refl (x : list aname) : All2 (on_rel eq binder_relevance) x x.
Proof. now eapply All_All2_refl, All_refl. Qed.
#[global]
Hint Resolve eq_binder_relevances_refl : core.

#[global]
Instance R_universe_instance_refl Re : RelationClasses.Reflexive Re ->
  RelationClasses.Reflexive (R_universe_instance Re).
Proof. intros tRe x. eapply Forall2_map.
  induction x; constructor; auto.
Qed.

#[global]
Instance R_universe_instance_sym Re : RelationClasses.Symmetric Re ->
  RelationClasses.Symmetric (R_universe_instance Re).
Proof. intros tRe x y. now eapply Forall2_symP. Qed.

#[global]
Instance R_universe_instance_trans Re : RelationClasses.Transitive Re ->
  RelationClasses.Transitive (R_universe_instance Re).
Proof. intros tRe x y z. now eapply Forall2_trans. Qed.

Lemma onctx_eq_ctx P ctx eq_term :
  onctx P ctx ->
  (forall x, P x -> eq_term x x) ->
  All2_fold (fun _ _ => compare_decls eq_term eq_term) ctx ctx.
Proof.
  intros onc HP.
  induction onc.
  - constructor; auto.
  - constructor; auto; simpl.
    destruct x as [na [b|] ty]; destruct p; simpl in *;
    constructor; auto.
Qed.

#[global]
Polymorphic Instance creflexive_eq A : CRelationClasses.Reflexive (@eq A).
Proof. intro x. constructor. Qed.

#[global]
Polymorphic Instance eq_predicate_refl Re Ru :
  CRelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Ru ->
  CRelationClasses.Reflexive (eq_predicate Re Ru).
Proof.
  intros hre hru.
  intros p. unfold eq_predicate; intuition auto; try reflexivity.
  eapply All2_same; reflexivity.
Qed.

#[global]
Polymorphic Instance eq_term_upto_univ_refl Σ Re Rle napp :
  RelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Rle ->
  Reflexive (eq_term_upto_univ_napp Σ Re Rle napp).
Proof.
  intros hRe hRle t.
  induction t in napp, Rle, hRle |- * using term_forall_list_ind.
  all: simpl.
  all: try constructor. all: eauto.
  all: try solve [eapply All_All2 ; eauto].
  all: try solve [eapply Forall2_same ; eauto].
  all: try solve [unfold eq_predicate; solve_all; eapply All_All2; eauto].
  - apply R_global_instance_refl; auto.
  - apply R_global_instance_refl; auto.
  - destruct X as [? [? ?]].
    unfold eq_predicate; solve_all.
    eapply All_All2; eauto. reflexivity.
    eapply onctx_eq_ctx in a0; eauto.
  - eapply All_All2; eauto; simpl; intuition eauto.
    eapply onctx_eq_ctx in a; eauto.
  - eapply All_All2; eauto; simpl; intuition eauto.
  - eapply All_All2; eauto; simpl; intuition eauto.
Qed.

#[global]
Instance compare_term_refl {cf} pb {Σ : global_env} φ : Reflexive (compare_term pb Σ φ).
Proof. eapply eq_term_upto_univ_refl; tc. Qed.

Derive Signature for eq_term_upto_univ_napp.

Lemma R_global_instance_sym Σ Re Rle gr napp u u' :
  RelationClasses.Symmetric Re ->
  RelationClasses.Symmetric Rle ->
  R_global_instance Σ Re Rle gr napp u' u ->
  R_global_instance Σ Re Rle gr napp u u'.
Proof.
  intros rRE rRle.
  unfold R_global_instance_gen.
  destruct global_variance_gen as [v|] eqn:lookup.
  - induction u in u', v |- *; destruct u'; simpl; auto;
    destruct v as [|v vs]; unfold R_opt_variance in IHu; simpl; auto.
    intros [Ra Ru']. split.
    destruct v; simpl; auto.
    apply IHu; auto.
  - apply Forall2_symP; eauto.
Qed.

Lemma onctx_eq_ctx_sym P ctx ctx' eq_term :
  onctx P ctx ->
  (forall x, P x -> forall y, eq_term x y -> eq_term y x) ->
  All2_fold (fun _ _ => compare_decls eq_term eq_term) ctx ctx' ->
  All2_fold (fun _ _ => compare_decls eq_term eq_term) ctx' ctx.
Proof.
  intros onc HP H1.
  induction H1; depelim onc; constructor; intuition auto; simpl in *.
  depelim p; depelim o; constructor; auto; try now symmetry.
Qed.

#[global]
Polymorphic Instance eq_term_upto_univ_sym Σ Re Rle napp :
  RelationClasses.Symmetric Re ->
  RelationClasses.Symmetric Rle ->
  Symmetric (eq_term_upto_univ_napp Σ Re Rle napp).
Proof.
  intros he hle u v e.
  pose proof (@RelationClasses.symmetry _ (@eq_binder_annot name name) _).
  induction u in Rle, hle, v, napp, e |- * using term_forall_list_ind.
  all: dependent destruction e.
  all: try solve [
    econstructor ; eauto using R_global_instance_sym ;
    try eapply Forall2_symP ; eauto
  ].
  - econstructor.
    eapply All2_All_mix_left in X as h; eauto.
    clear a X.
    induction h.
    + constructor.
    + destruct r as [h1 h2]. eapply h1 in h2 ; auto.
  - solve_all. destruct e as (r & ? & eq & ?).
    econstructor; rewrite ?e; unfold eq_predicate in *; solve_all; eauto.
    eapply All2_sym; solve_all.
    unfold R_universe_instance in r |- *.
    eapply Forall2_symP; eauto.
    eapply onctx_eq_ctx_sym in a1; eauto.
    eapply All2_sym; solve_all.
    eapply onctx_eq_ctx_sym in a0; eauto.
  - econstructor.
    eapply All2_All_mix_left in X as h; eauto.
    clear a X.
    induction h.
    + constructor.
    + destruct r as [[h1 h2] [[[h3 h4] h5] h6]].
      eapply h1 in h3; auto. constructor; auto.
  - econstructor.
    eapply All2_All_mix_left in X as h; eauto.
    clear a X.
    induction h.
    + constructor.
    + destruct r as [[h1 h2] [[[h3 h4] h5] h6]]. eapply h1 in h3 ; auto.
    constructor; auto.
Qed.

#[global]
Polymorphic Instance eq_predicate_sym Re Ru :
  CRelationClasses.Symmetric Re ->
  RelationClasses.Symmetric Ru ->
  CRelationClasses.Symmetric (eq_predicate Re Ru).
Proof.
  intros hre hru.
  intros p. unfold eq_predicate; intuition auto; try now symmetry.
Qed.

#[global]
Instance compare_term_sym {cf} Σ φ : Symmetric (compare_term Conv Σ φ).
Proof.
  now intros t u; unfold compare_term; cbn; symmetry.
Qed.

#[global]
Instance R_global_instance_trans Σ Re Rle gr napp :
  RelationClasses.Transitive Re ->
  RelationClasses.Transitive Rle ->
  RelationClasses.Transitive (R_global_instance Σ Re Rle gr napp).
Proof.
  intros he hle x y z.
  unfold R_global_instance_gen, R_opt_variance.
  destruct global_variance_gen as [v|].
  clear -he hle.
  induction x in y, z, v |- *; destruct y, z, v; simpl; auto => //. eauto.
  intros [Ra Rxy] [Rt Ryz].
  split; eauto.
  destruct t1; simpl in *; auto.
  now etransitivity; eauto.
  now etransitivity; eauto.
  eapply Forall2_trans; auto.
Qed.

Lemma onctx_eq_ctx_trans P ctx ctx' ctx'' eq_term :
  onctx P ctx ->
  (forall x, P x -> forall y z, eq_term x y -> eq_term y z -> eq_term x z) ->
  All2_fold (fun _ _ => compare_decls eq_term eq_term) ctx ctx' ->
  All2_fold (fun _ _ => compare_decls eq_term eq_term) ctx' ctx'' ->
  All2_fold (fun _ _ => compare_decls eq_term eq_term) ctx ctx''.
Proof.
  intros onc HP H1; revert ctx''.
  induction H1; depelim onc; intros ctx'' H; depelim H; constructor; intuition auto; simpl in *.
  depelim o. depelim p0.
  - depelim c; constructor; [now etransitivity|eauto].
  - depelim c; constructor; [now etransitivity|eauto ..].
Qed.

#[global]
Polymorphic Instance eq_predicate_trans Re Ru :
  CRelationClasses.Transitive Re ->
  RelationClasses.Transitive Ru ->
  CRelationClasses.Transitive (eq_predicate Re Ru).
Proof.
  intros hre hru.
  intros p. unfold eq_predicate; intuition auto; try now etransitivity.
  eapply All2_trans; tea.
  etransitivity; tea.
Qed.

#[global]
Polymorphic Instance eq_term_upto_univ_trans Σ Re Rle napp :
  RelationClasses.Transitive Re ->
  RelationClasses.Transitive Rle ->
  Transitive (eq_term_upto_univ_napp Σ Re Rle napp).
Proof.
  intros he hle u v w e1 e2.
  pose proof (@RelationClasses.transitivity _ (@eq_binder_annot name name) _).
  induction u in Rle, hle, v, w, napp, e1, e2 |- * using term_forall_list_ind.
  all: dependent destruction e1.
  all: try solve [ eauto ].
  all: try solve [
    dependent destruction e2 ; econstructor ; eauto;
    try eapply Forall2_trans ; eauto
  ].
  - dependent destruction e2.
    econstructor.
    eapply All2_All_mix_left in X as h; eauto.
    clear a X.
    induction h in a0, args'0 |- *.
    + assumption.
    + dependent destruction a0. constructor ; eauto.
      destruct r as [h1 h2]. eauto.
  - dependent destruction e2.
    constructor.
    eapply R_global_instance_trans; eauto.
  - dependent destruction e2.
    constructor.
    eapply R_global_instance_trans; eauto.
  - dependent destruction e2.
    unfold eq_predicate in *.
    !!solve_all.
    econstructor; unfold eq_predicate in *; solve_all; eauto.
    * clear -he hh1 hh2.
      revert hh1 hh2. generalize (pparams p), p'.(pparams), p'0.(pparams).
      intros l l' l''.
      induction 1 in l'' |- *; auto. intros H; depelim H. constructor; auto.
      eapply r; eauto. apply r.
    * etransitivity; eauto.
    * eapply onctx_eq_ctx_trans in hh; eauto.
      intros ???? -> ->; eauto.
    * clear -H he a a0.
      induction a in a0, brs'0 |- *.
      + assumption.
      + depelim a0. destruct p. constructor; auto.
        destruct r as [[h1 h1'] [h2 h3]].
        split.
        eapply onctx_eq_ctx_trans in h1; eauto.
        intros ???? -> ->;reflexivity.
        eapply h1'; eauto.
  - dependent destruction e2.
    econstructor.
    eapply All2_All_mix_left in X as h; eauto.
    clear a X.
    induction h in a0, mfix'0 |- *.
    + assumption.
    + dependent destruction a0. constructor ; eauto.
      intuition eauto.
      transitivity (rarg y); auto.
  - dependent destruction e2.
    econstructor.
    eapply All2_All_mix_left in X as h; eauto.
    clear a X.
    induction h in a0, mfix'0 |- *.
    + assumption.
    + dependent destruction a0. constructor ; eauto.
      intuition eauto.
      transitivity (rarg y); auto.
Qed.

#[global]
Instance compare_term_trans {cf} pb Σ φ : Transitive (compare_term pb Σ φ).
Proof. apply eq_term_upto_univ_trans; tc. Qed.

#[global]
Polymorphic Instance eq_term_upto_univ_equiv Σ Re (hRe : RelationClasses.Equivalence Re)
  : Equivalence (eq_term_upto_univ Σ Re Re).
Proof.
  constructor. all: exact _.
Defined.

#[global]
Polymorphic Instance eq_context_equiv {cf} Σ φ : Equivalence (eq_context_gen (eq_term Σ φ) (eq_term Σ φ)).
Proof.
  constructor; try exact _.
Qed.

#[global]
Polymorphic Instance leq_context_preord {cf} Σ φ : PreOrder (eq_context_gen (eq_term Σ φ) (leq_term Σ φ)).
Proof.
  constructor; try exact _.
Qed.

#[global]
Polymorphic Instance eq_term_equiv {cf:checker_flags} Σ φ : Equivalence (eq_term Σ φ).
Proof. split; tc. Qed.

#[global]
Polymorphic Instance leq_term_preorder {cf:checker_flags} Σ φ : PreOrder (leq_term Σ φ).
Proof. split; tc. Qed.

#[global]
Instance R_universe_instance_equiv R (hR : RelationClasses.Equivalence R)
  : RelationClasses.Equivalence (R_universe_instance R).
Proof.
  split.
  - intro. apply Forall2_same. reflexivity.
  - intros x y xy. eapply Forall2_sym, Forall2_impl; tea. now symmetry.
  - intros x y z xy yz. eapply Forall2_trans; tea. apply hR.
Qed.

Lemma R_universe_instance_antisym Re Rle (hRe : RelationClasses.Equivalence Re) :
  RelationClasses.Antisymmetric _ Re Rle ->
  RelationClasses.Antisymmetric _ (R_universe_instance Re) (R_universe_instance Rle).
Proof.
  intros H x y H1 H2.
  eapply Forall2_sym in H2.
  eapply Forall2_impl; [eapply Forall2_and|]; [exact H1|exact H2|].
  cbn; intros ? ? [? ?]. eapply H; assumption.
Qed.

#[global]
Instance R_global_instance_equiv Σ R (hR : RelationClasses.Equivalence R) gr napp
  : RelationClasses.Equivalence (R_global_instance Σ R R gr napp).
Proof.
  split.
  - intro. apply R_global_instance_refl; typeclasses eauto.
  - intros x y xy. eapply R_global_instance_sym; auto; typeclasses eauto.
  - intros x y z xy yz. eapply R_global_instance_trans; eauto; typeclasses eauto.
Qed.

#[global]
Instance R_global_instance_antisym Σ Re Rle (hRe : RelationClasses.Equivalence Re) gr napp :
  RelationClasses.Antisymmetric _ Re Rle ->
  RelationClasses.Antisymmetric _ (R_global_instance Σ Re Re gr napp) (R_global_instance Σ Re Rle gr napp).
Proof.
  intros hR u v.
  unfold R_global_instance_gen, R_opt_variance.
  destruct global_variance_gen; auto.
  induction u in l, v |- *; destruct v, l; simpl; auto.
  intros [at' uv] [ta vu]. split; auto.
  destruct t0; simpl in *; auto.
Qed.

Lemma eq_term_upto_univ_antisym Σ Re Rle (hRe : RelationClasses.Equivalence Re) :
  RelationClasses.Antisymmetric _ Re Rle ->
  Antisymmetric (eq_term_upto_univ Σ Re Re) (eq_term_upto_univ Σ Re Rle).
Proof.
  intros hR u v. generalize 0; intros n h h'.
  induction u in v, n, h, h' |- * using term_forall_list_ind.
  all: simpl ; inversion h ; subst; inversion h' ;
       subst ; try constructor ; auto.
  all: eapply RelationClasses.antisymmetry; eauto.
Qed.

#[global]
Instance leq_term_antisym {cf:checker_flags} Σ φ
  : Antisymmetric (eq_term Σ φ) (leq_term Σ φ).
Proof.
  eapply eq_term_upto_univ_antisym; exact _.
Qed.

Lemma global_variance_napp_mon {Σ gr napp napp' v} :
  napp <= napp' ->
  global_variance Σ gr napp = Some v ->
  global_variance Σ gr napp' = Some v.
Proof.
  intros hnapp.
  rewrite /global_variance_gen.
  destruct gr; try congruence.
  - destruct lookup_inductive_gen as [[mdecl idec]|] => //.
    destruct destArity as [[ctx s]|] => //.
    elim: Nat.leb_spec => // cass indv.
    elim: Nat.leb_spec => //. lia.
  - destruct lookup_constructor_gen as [[[mdecl idecl] cdecl]|] => //.
    elim: Nat.leb_spec => // cass indv.
    elim: Nat.leb_spec => //. lia.
Qed.

#[global]
Instance R_global_instance_impl_same_napp Σ Re Re' Rle Rle' gr napp :
  RelationClasses.subrelation Re Re' ->
  RelationClasses.subrelation Rle Rle' ->
  subrelation (R_global_instance Σ Re Rle gr napp) (R_global_instance Σ Re' Rle' gr napp).
Proof.
  intros he hle t t'.
  unfold R_global_instance_gen, R_opt_variance.
  destruct global_variance_gen as [v|] eqn:glob.
  induction t in v, t' |- *; destruct v, t'; simpl; auto.
  intros []; split; auto.
  destruct t0; simpl; auto.
  now eapply R_universe_instance_impl'.
Qed.

#[global]
Instance R_global_instance_impl Σ Re Re' Rle Rle' gr napp napp' :
  RelationClasses.subrelation Re Re' ->
  RelationClasses.subrelation Re Rle' ->
  RelationClasses.subrelation Rle Rle' ->
  napp <= napp' ->
  subrelation (R_global_instance Σ Re Rle gr napp) (R_global_instance Σ Re' Rle' gr napp').
Proof.
  intros he hle hele hnapp t t'.
  unfold R_global_instance_gen, R_opt_variance.
  destruct global_variance_gen as [v|] eqn:glob.
  rewrite (global_variance_napp_mon hnapp glob).
  induction t in v, t' |- *; destruct v, t'; simpl; auto.
  intros []; split; auto.
  destruct t0; simpl; auto.
  destruct (global_variance _ _ napp') as [v|] eqn:glob'; eauto using R_universe_instance_impl'.
  induction t in v, t' |- *; destruct v, t'; simpl; auto; intros H; inv H.
  eauto.
  split; auto.
  destruct t0; simpl; auto.
Qed.

Lemma global_variance_empty gr napp env : env.(declarations) = [] -> global_variance env gr napp = None.
Proof.
  destruct env; cbn => ->. destruct gr; auto.
Qed.

(** Pure syntactic equality, without cumulative inductive types subtyping *)

#[global]
Instance R_global_instance_empty_impl Σ Re Re' Rle Rle' gr napp napp' :
  RelationClasses.subrelation Re Re' ->
  RelationClasses.subrelation Rle Rle' ->
  RelationClasses.subrelation Re Rle' ->
  subrelation (R_global_instance empty_global_env Re Rle gr napp) (R_global_instance Σ Re' Rle' gr napp').
Proof.
  intros he hle hele t t'.
  unfold R_global_instance_gen, R_opt_variance.
  rewrite global_variance_empty //.
  destruct global_variance_gen as [v|]; eauto using R_universe_instance_impl'.
  induction t in v, t' |- *; destruct v, t'; simpl; intros H; inv H; auto.
  simpl.
  split; auto.
  destruct t0; simpl; auto.
Qed.

Lemma onctx_eq_ctx_impl P ctx ctx' eq_term eq_term' :
  onctx P ctx ->
  (forall x, P x -> forall y, eq_term x y -> eq_term' x y) ->
  eq_context_gen eq_term eq_term ctx ctx' ->
  eq_context_gen eq_term' eq_term' ctx ctx'.
Proof.
  intros onc HP H1.
  induction H1; depelim onc; constructor; eauto; intuition auto; simpl in *.
  destruct o; depelim p; constructor; auto.
Qed.

#[global]
Instance eq_term_upto_univ_impl Σ Re Re' Rle Rle' napp napp' :
  RelationClasses.subrelation Re Re' ->
  RelationClasses.subrelation Rle Rle' ->
  RelationClasses.subrelation Re Rle' ->
  napp <= napp' ->
  subrelation (eq_term_upto_univ_napp Σ Re Rle napp) (eq_term_upto_univ_napp Σ Re' Rle' napp').
Proof.
  intros he hle hele hnapp t t'.
  induction t in napp, napp', hnapp, t', Rle, Rle', hle, hele |- * using term_forall_list_ind;
    try (inversion 1; subst; constructor;
         eauto using R_universe_instance_impl'; fail).
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
  - inversion 1; subst; constructor.
    eapply IHt1. 4:eauto. all:auto with arith. eauto.
  - inversion 1; subst; constructor.
    eapply R_global_instance_impl. 5:eauto. all:auto.
  - inversion 1; subst; constructor.
    eapply R_global_instance_impl. 5:eauto. all:eauto.
  - inversion 1; subst; constructor; unfold eq_predicate in *; eauto; solve_all.
    * eapply R_universe_instance_impl'; eauto.
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x [? ?] y [[[? ?] ?] ?]. repeat split; eauto.
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x [? ?] y [[[? ?] ?] ?]. repeat split; eauto.
Qed.

#[global]
Instance eq_term_upto_univ_empty_impl Σ Re Re' Rle Rle' napp napp' :
  RelationClasses.subrelation Re Re' ->
  RelationClasses.subrelation Rle Rle' ->
  RelationClasses.subrelation Re Rle' ->
  subrelation (eq_term_upto_univ_napp empty_global_env Re Rle napp) (eq_term_upto_univ_napp Σ Re' Rle' napp').
Proof.
  intros he hle hele t t'.
  induction t in napp, napp', t', Rle, Rle', hle, hele |- * using term_forall_list_ind;
    try (inversion 1; subst; constructor;
         eauto using R_universe_instance_impl'; fail).
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
  - inversion 1; subst; constructor.
    (* eapply shelf bug... fixed in unifall *)
    eapply R_global_instance_empty_impl. 4:eauto. all:eauto.
  - inversion 1; subst; constructor.
    eapply R_global_instance_empty_impl. 4:eauto. all:eauto.
  - inversion 1; subst; constructor; unfold eq_predicate in *; solve_all.
    * eapply R_universe_instance_impl'; eauto.
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x [? ?] y [[[? ?] ?] ?]. repeat split; eauto.
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x [? ?] y [[[? ?] ?] ?]. repeat split; eauto.
Qed.

#[global]
Instance eq_term_upto_univ_leq Σ Re Rle napp napp' :
  RelationClasses.subrelation Re Rle ->
  napp <= napp' ->
  subrelation (eq_term_upto_univ_napp Σ Re Re napp) (eq_term_upto_univ_napp Σ Re Rle napp').
Proof.
  intros H. eapply eq_term_upto_univ_impl; exact _.
Qed.

#[global]
Instance eq_term_leq_term {cf:checker_flags} Σ φ
  : subrelation (eq_term Σ φ) (leq_term Σ φ).
Proof.
  eapply eq_term_upto_univ_leq; auto; exact _.
Qed.

#[global]
Instance leq_term_partial_order {cf:checker_flags} Σ φ
  : PartialOrder (eq_term Σ φ) (leq_term Σ φ).
Proof.
  split. intros eqxy; split; now eapply eq_term_leq_term.
  intros [xy yx].
  now eapply leq_term_antisym.
Qed.

#[global]
Hint Constructors compare_decls : pcuic.

Local Ltac lih :=
  lazymatch goal with
  | ih : forall Rle v n k, eq_term_upto_univ_napp _ _ _ ?u _ -> _
    |- eq_term_upto_univ _ _ (lift _ _ ?u) _ =>
    eapply ih
  end.

Lemma eq_term_upto_univ_lift Σ Re Rle n n' k :
  Proper (eq_term_upto_univ_napp Σ Re Rle n' ==> eq_term_upto_univ_napp Σ Re Rle n') (lift n k).
Proof.
  intros u v e.
  induction u in n', v, n, k, e, Rle |- * using term_forall_list_ind.
  all: dependent destruction e.
  all: try solve [cbn ; constructor ; try lih ; try assumption; solve_all].
  - cbn. destruct e as (? & ? & e & ?).
    constructor; unfold eq_predicate in *; simpl; !!solve_all.
    * rewrite -?(All2_fold_length e).
      eapply hh0; eauto.
    * rewrite (All2_fold_length a). now eapply hh4.
  - cbn. constructor.
    pose proof (All2_length a).
    solve_all. rewrite H. eauto.
  - cbn. constructor.
    pose proof (All2_length a).
    solve_all. rewrite H. eauto.
Qed.

Lemma lift_compare_term `{checker_flags} pb Σ ϕ n k t t' :
  compare_term pb Σ ϕ t t' -> compare_term pb Σ ϕ (lift n k t) (lift n k t').
Proof.
  now apply eq_term_upto_univ_lift.
Qed.

Lemma lift_compare_decls `{checker_flags} pb Σ ϕ n k d d' :
  compare_decl pb Σ ϕ d d' -> compare_decl pb Σ ϕ (lift_decl n k d) (lift_decl n k d').
Proof.
  intros []; constructor; cbn; intuition auto using lift_compare_term.
Qed.

Lemma lift_compare_context `{checker_flags} pb Σ φ l l' n k :
  compare_context pb Σ φ l l' ->
  compare_context pb Σ φ (lift_context n k l) (lift_context n k l').
Proof.
  unfold compare_context.
  induction 1; rewrite -> ?lift_context_snoc0. constructor.
  constructor; auto.
  eapply lift_compare_decls in p.
  now rewrite (All2_fold_length X).
Qed.

Lemma lift_eq_term {cf:checker_flags} Σ φ n k T U :
  eq_term Σ φ T U -> eq_term Σ φ (lift n k T) (lift n k U).
Proof.
  apply eq_term_upto_univ_lift.
Qed.

Lemma lift_leq_term {cf:checker_flags} Σ φ n k T U :
  leq_term Σ φ T U -> leq_term Σ φ (lift n k T) (lift n k U).
Proof.
  apply eq_term_upto_univ_lift.
Qed.

Local Ltac sih :=
  lazymatch goal with
  | ih : forall Rle v n x y, _ -> eq_term_upto_univ _ _ ?u _ -> _ -> _
    |- eq_term_upto_univ _ _ (subst _ _ ?u) _ => eapply ih
  end.

Lemma eq_term_upto_univ_substs Σ Re Rle napp :
  RelationClasses.subrelation Re Rle ->
  forall u v n l l',
    eq_term_upto_univ_napp Σ Re Rle napp u v ->
    All2 (eq_term_upto_univ Σ Re Re) l l' ->
    eq_term_upto_univ_napp Σ Re Rle napp (subst l n u) (subst l' n v).
Proof.
  unfold RelationClasses.subrelation; intros hR u v n l l' hu hl.
  induction u in napp, v, n, l, l', hu, hl, Rle, hR |- * using term_forall_list_ind.
  all: dependent destruction hu.
  all: try solve [ cbn ; constructor ; try sih ; eauto ].
  - cbn. destruct (Nat.leb_spec0 n n0).
    + case_eq (nth_error l (n0 - n)).
      * intros t e. eapply All2_nth_error_Some in e as h ; eauto.
        destruct h as [t' [e' h]].
        rewrite e'.
        eapply eq_term_upto_univ_lift.
        eapply eq_term_upto_univ_leq. 3:eauto. all:auto with arith.
      * intros h. eapply All2_nth_error_None in h as hh ; eauto.
        rewrite hh.
        apply All2_length in hl as e. rewrite <- e.
        constructor.
    + constructor.
  - cbn. constructor. solve_all.
  - cbn.
    destruct e as (? & ? & e & ?).
    constructor ; unfold eq_predicate; simpl; try sih ; solve_all.
    * rewrite -(All2_fold_length e). eapply e1; eauto.
    * rewrite (All2_fold_length a). now eapply b0.
  - cbn. constructor ; try sih ; eauto.
    pose proof (All2_length a).
    solve_all. now rewrite H.
  - cbn. constructor ; try sih ; eauto.
    pose proof (All2_length a).
    solve_all. now rewrite H.
Qed.

Lemma eq_term_upto_univ_subst Σ Re Rle :
  RelationClasses.subrelation Re Rle ->
  forall u v n x y,
    eq_term_upto_univ Σ Re Rle u v ->
    eq_term_upto_univ Σ Re Re x y ->
    eq_term_upto_univ Σ Re Rle (u{n := x}) (v{n := y}).
Proof.
  intros hR u v n x y e1 e2.
  eapply eq_term_upto_univ_substs; eauto.
Qed.

Lemma subst_eq_term {cf:checker_flags} Σ φ l k T U :
  eq_term Σ φ T U ->
  eq_term Σ φ (subst l k T) (subst l k U).
Proof.
  intros Hleq.
  eapply eq_term_upto_univ_substs; try easy.
  now eapply All2_same.
Qed.

Lemma subst_leq_term {cf:checker_flags} Σ φ l k T U :
  leq_term Σ φ T U ->
  leq_term Σ φ (subst l k T) (subst l k U).
Proof.
  intros Hleq.
  eapply eq_term_upto_univ_substs; try easy.
  intro; apply eq_universe_leq_universe.
  now eapply All2_same.
Qed.

(** ** Behavior on mkApps and it_mkLambda_or_LetIn **  *)

Lemma eq_term_eq_term_napp Σ Re Rle napp t t' :
  RelationClasses.subrelation Re Rle ->
  eq_term_upto_univ Σ Re Rle t t' ->
  eq_term_upto_univ_napp Σ Re Rle napp t t'.
Proof.
  intros. eapply eq_term_upto_univ_impl. 5:eauto.
  4:auto with arith. all:typeclasses eauto.
Qed.

Lemma leq_term_leq_term_napp Σ Re Rle napp t t' :
  RelationClasses.subrelation Re Rle ->
  eq_term_upto_univ Σ Re Rle t t' ->
  eq_term_upto_univ_napp Σ Re Rle napp t t'.
Proof.
  intros. eapply eq_term_upto_univ_impl. 5:eauto.
  4:auto with arith. all:try typeclasses eauto.
Qed.

Lemma eq_term_upto_univ_napp_mkApps Σ Re Rle u1 l1 u2 l2 napp :
    eq_term_upto_univ_napp Σ Re Rle (#|l1| + napp) u1 u2 ->
    All2 (eq_term_upto_univ Σ Re Re) l1 l2 ->
    eq_term_upto_univ_napp Σ Re Rle napp (mkApps u1 l1) (mkApps u2 l2).
Proof.
  intros hu hl. induction l1 in napp, u1, u2, l2, hu, hl |- *.
  - inversion hl. subst. assumption.
  - inversion hl. subst. simpl.
    eapply IHl1.
    + constructor. all: assumption.
    + assumption.
Qed.

Lemma eq_term_upto_univ_napp_mkApps_l_inv Σ Re Rle napp u l t :
    eq_term_upto_univ_napp Σ Re Rle napp (mkApps u l) t ->
    ∑ u' l',
      eq_term_upto_univ_napp Σ Re Rle (#|l| + napp) u u' *
      All2 (eq_term_upto_univ Σ Re Re) l l' *
      (t = mkApps u' l').
Proof.
  intros h. induction l in napp, u, t, h, Rle |- *.
  - cbn in h. exists t, []. split ; auto.
  - cbn in h. apply IHl in h as [u' [l' [[h1 h2] h3]]].
    dependent destruction h1. subst.
    eexists. eexists. split; [ split | ].
    + eassumption.
    + constructor.
      * eassumption.
      * eassumption.
    + cbn. reflexivity.
Qed.

Lemma eq_term_upto_univ_napp_mkApps_r_inv Σ Re Rle napp u l t :
    eq_term_upto_univ_napp Σ Re Rle napp t (mkApps u l) ->
    ∑ u' l',
      eq_term_upto_univ_napp Σ Re Rle (#|l| + napp) u' u *
      All2 (eq_term_upto_univ Σ Re Re) l' l *
      (t = mkApps u' l').
Proof.
  intros h. induction l in napp, u, t, h, Rle |- *.
  - cbn in h. exists t, []. split ; auto.
  - cbn in h. apply IHl in h as [u' [l' [[h1 h2] h3]]].
    dependent destruction h1. subst.
    eexists. eexists. split; [ split | ].
    + eassumption.
    + constructor.
      * eassumption.
      * eassumption.
    + cbn. reflexivity.
Qed.

Lemma eq_term_upto_univ_mkApps Σ Re Rle u1 l1 u2 l2 :
    eq_term_upto_univ_napp Σ Re Rle #|l1| u1 u2 ->
    All2 (eq_term_upto_univ Σ Re Re) l1 l2 ->
    eq_term_upto_univ Σ Re Rle (mkApps u1 l1) (mkApps u2 l2).
Proof.
  intros; apply eq_term_upto_univ_napp_mkApps; rewrite ?Nat.add_0_r; auto.
Qed.

Lemma eq_term_upto_univ_mkApps_l_inv Σ Re Rle u l t :
    eq_term_upto_univ Σ Re Rle (mkApps u l) t ->
    ∑ u' l',
      eq_term_upto_univ_napp Σ Re Rle #|l| u u' *
      All2 (eq_term_upto_univ Σ Re Re) l l' *
      (t = mkApps u' l').
Proof.
  intros H; apply eq_term_upto_univ_napp_mkApps_l_inv in H; rewrite ?Nat.add_0_r in H; auto.
Qed.

Lemma eq_term_upto_univ_mkApps_r_inv Σ Re Rle u l t :
    eq_term_upto_univ Σ Re Rle t (mkApps u l) ->
    ∑ u' l',
      eq_term_upto_univ_napp Σ Re Rle #|l| u' u *
      All2 (eq_term_upto_univ Σ Re Re) l' l *
      (t = mkApps u' l').
Proof.
  intros H; apply eq_term_upto_univ_napp_mkApps_r_inv in H;
    rewrite Nat.add_0_r in H; auto.
Qed.

Lemma R_universe_instance_eq {u u'} : R_universe_instance eq u u' -> u = u'.
Proof.
  intros H.
  apply Forall2_eq in H. apply map_inj in H ; revgoals.
  { apply Universe.make_inj. }
  subst. constructor ; auto.
Qed.

Lemma valid_constraints_empty {cf} i :
  valid_constraints (empty_ext empty_global_env) (subst_instance_cstrs i (empty_ext empty_global_env)).
Proof.
  red. destruct check_univs => //.
Qed.

Lemma upto_eq_impl Σ Re Rle :
  RelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Rle ->
  subrelation (eq_term_upto_univ Σ eq eq) (eq_term_upto_univ Σ Re Rle).
Proof.
  intros he hle. eapply eq_term_upto_univ_impl. 4:auto.
  all: intros ? ? []; eauto.
Qed.

(** ** Syntactic ws_cumul_pb up to printing anotations ** *)

Definition upto_names := eq_term_upto_univ empty_global_env eq eq.

Infix "≡" := upto_names (at level 70).

Infix "≡'" := (eq_term_upto_univ empty_global_env eq eq) (at level 70).
Notation upto_names' := (eq_term_upto_univ empty_global_env eq eq).

#[global]
Instance upto_names_ref : Reflexive upto_names.
Proof.
  eapply eq_term_upto_univ_refl; exact _.
Qed.

#[global]
Instance upto_names_sym : Symmetric upto_names.
Proof.
  eapply eq_term_upto_univ_sym; exact _.
Qed.

#[global]
Instance upto_names_trans : Transitive upto_names.
Proof.
  eapply eq_term_upto_univ_trans; exact _.
Qed.

(* TODO: rename *)
(* Definition nleq_term t t' := *)
(*   eqb_term_upto_univ eqb eqb t t'. *)

(* Corollary reflect_upto_names : *)
(*   forall t t', reflectT (upto_names t t') (nleq_term t t'). *)
(* Proof. *)
(*   intros t t'. eapply reflect_eq_term_upto_univ. *)
(*   all: intros u u'; eapply reflect_reflectT, eqb_spec. *)
(* Qed. *)

Lemma upto_names_impl Σ Re Rle :
  RelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Rle ->
  subrelation upto_names (eq_term_upto_univ Σ Re Rle).
Proof.
  intros he hle. eapply eq_term_upto_univ_empty_impl; auto.
  all: intros ? ? []; eauto.
Qed.

Lemma upto_names_impl_eq_term {cf:checker_flags} Σ φ u v :
    u ≡ v -> eq_term Σ φ u v.
Proof.
  eapply upto_names_impl ; exact _.
Qed.

Lemma upto_names_impl_leq_term {cf:checker_flags} Σ φ u v :
    u ≡ v -> leq_term Σ φ u v.
Proof.
  eapply upto_names_impl ; exact _.
Qed.

Lemma eq_term_upto_univ_isApp Σ Re Rle napp u v :
  eq_term_upto_univ_napp Σ Re Rle napp u v ->
  isApp u = isApp v.
Proof.
  induction 1.
  all: reflexivity.
Qed.

(** ** ws_cumul_pb on contexts ** *)

Inductive rel_option {A B} (R : A -> B -> Type) : option A -> option B -> Type :=
| rel_some : forall a b, R a b -> rel_option R (Some a) (Some b)
| rel_none : rel_option R None None.

Derive Signature NoConfusion for rel_option.

Definition eq_decl_upto_gen Σ Re Rle d d' : Type :=
  eq_binder_annot d.(decl_name) d'.(decl_name) *
  rel_option (eq_term_upto_univ Σ Re Re) d.(decl_body) d'.(decl_body) *
  eq_term_upto_univ Σ Re Rle d.(decl_type) d'.(decl_type).

(* TODO perhaps should be def *)
Lemma All2_eq_context_upto Σ Re Rle :
  subrelation (All2 (eq_decl_upto_gen Σ Re Rle)) (eq_context_upto Σ Re Rle).
Proof.
  intros Γ Δ h.
  induction h.
  - constructor.
  - destruct r as [[h1 h2] h3].
    destruct x as [na bo ty], y as [na' bo' ty'].
    simpl in h1, h2.
    destruct h2.
    + constructor ; eauto. constructor; auto.
    + constructor ; eauto. constructor; auto.
Qed.

Lemma eq_context_upto_refl Σ Re Rle :
  RelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Rle ->
  Reflexive (eq_context_upto Σ Re Rle).
Proof. exact _. Qed.

Lemma eq_context_upto_sym Σ Re Rle :
  RelationClasses.Symmetric Re ->
  RelationClasses.Symmetric Rle ->
  Symmetric (eq_context_upto Σ Re Rle).
Proof. exact _. Qed.

Lemma eq_context_upto_cat Σ Re Rle Γ Δ Γ' Δ' :
  eq_context_upto Σ Re Rle Γ Γ' ->
  eq_context_upto Σ Re Rle Δ Δ' ->
  eq_context_upto Σ Re Rle (Γ ,,, Δ) (Γ' ,,, Δ').
Proof. intros. eapply All2_fold_app; eauto. Qed.

Lemma eq_context_upto_rev Σ Re Rle Γ Δ :
  eq_context_upto Σ Re Rle Γ Δ ->
  eq_context_upto Σ Re Rle (rev Γ) (rev Δ).
Proof.
  induction 1.
  - constructor.
  - rewrite 2!rev_cons. eapply eq_context_upto_cat ; eauto.
    constructor ; eauto. constructor.
Qed.

Lemma eq_context_upto_rev' :
  forall Σ Γ Δ Re Rle,
    eq_context_upto Σ Re Rle Γ Δ ->
    eq_context_upto Σ Re Rle (List.rev Γ) (List.rev Δ).
Proof.
  intros Σ Γ Δ Re Rle h.
  induction h.
  - constructor.
  - simpl. eapply eq_context_upto_cat.
    + repeat constructor; assumption.
    + assumption.
Qed.

Lemma eq_context_upto_length :
  forall {Σ Re Rle Γ Δ},
    eq_context_upto Σ Re Rle Γ Δ ->
    #|Γ| = #|Δ|.
Proof.
  intros Σ Re Rle Γ Δ h.
  induction h. all: simpl ; auto.
Qed.

Lemma eq_context_upto_subst_context Σ Re Rle :
  RelationClasses.subrelation Re Rle ->
  forall u v n l l',
    eq_context_upto Σ Re Rle u v ->
    All2 (eq_term_upto_univ Σ Re Re) l l' ->
    eq_context_upto Σ Re Rle (subst_context l n u) (subst_context l' n v).
Proof.
  intros re u v n l l'.
  induction 1; intros Hl.
  - rewrite !subst_context_nil. constructor.
  - rewrite !subst_context_snoc; constructor; eauto.
    depelim p; constructor; simpl; intuition auto;
    rewrite -(length_of X);
    apply eq_term_upto_univ_substs; auto. reflexivity.
Qed.

#[global]
Hint Resolve All2_fold_nil : pcuic.

Lemma eq_context_upto_smash_context Σ ctx ctx' x y :
  eq_context_upto Σ eq eq ctx ctx' -> eq_context_upto Σ eq eq x y ->
  eq_context_upto Σ eq eq (smash_context ctx x) (smash_context ctx' y).
Proof.
  induction x in ctx, ctx', y |- *; intros eqctx eqt; inv eqt; simpl;
    try split; auto; try constructor; auto. depelim X0 => /=.
  - apply IHx; auto. apply eq_context_upto_cat; auto.
    constructor; pcuic.
  - apply IHx; auto. eapply eq_context_upto_subst_context; eauto.
    typeclasses eauto.
Qed.

Lemma eq_context_upto_nth_error Σ Re Rle ctx ctx' n :
  eq_context_upto Σ Re Rle ctx ctx' ->
  rel_option (eq_decl_upto_gen Σ Re Rle) (nth_error ctx n) (nth_error ctx' n).
Proof.
  induction 1 in n |- *.
  - rewrite nth_error_nil. constructor.
  - destruct n; simpl; auto.
    constructor. depelim p; constructor; intuition auto;
    now constructor.
Qed.

Lemma eq_context_impl :
  forall Σ Re Re' Rle Rle',
    RelationClasses.subrelation Re Re' ->
    RelationClasses.subrelation Rle Rle' ->
    RelationClasses.subrelation Re' Rle' ->
    subrelation (eq_context_upto Σ Re Rle) (eq_context_upto Σ Re' Rle').
Proof.
  intros Σ Re Re' Rle Rle' hR hR' hReRle' Γ Δ h.
  induction h.
  - constructor.
  - constructor; auto.
    depelim p; constructor; auto.
    all:eapply eq_term_upto_univ_impl. 5,10,15:tea. all:eauto.
    all:now transitivity Re'.
Qed.

Lemma eq_term_upto_univ_it_mkLambda_or_LetIn Σ Re Rle :
    RelationClasses.Reflexive Re ->
    Proper (eq_context_upto Σ Re Re ==> eq_term_upto_univ Σ Re Rle ==> eq_term_upto_univ Σ Re Rle) it_mkLambda_or_LetIn.
Proof.
  intros he Γ Δ eq u v h.
  induction eq in u, v, h, he |- *.
  - assumption.
  - simpl. cbn. apply IHeq => //.
    destruct p; cbn; constructor ; tas; try reflexivity.
Qed.

Lemma eq_term_upto_univ_it_mkLambda_or_LetIn_r Σ Re Rle Γ :
  RelationClasses.Reflexive Re ->
  respectful (eq_term_upto_univ Σ Re Rle) (eq_term_upto_univ Σ Re Rle)
             (it_mkLambda_or_LetIn Γ) (it_mkLambda_or_LetIn Γ).
Proof.
  intros he u v h.
  induction Γ as [| [na [b|] A] Γ ih ] in u, v, h |- *.
  - assumption.
  - simpl. cbn. apply ih. constructor ; try apply eq_term_upto_univ_refl.
    all: auto.
  - simpl. cbn. apply ih. constructor ; try apply eq_term_upto_univ_refl.
    all: auto.
Qed.

Lemma eq_term_it_mkLambda_or_LetIn {cf:checker_flags} Σ φ Γ :
  respectful (eq_term Σ φ) (eq_term Σ φ)
             (it_mkLambda_or_LetIn Γ) (it_mkLambda_or_LetIn Γ).
Proof.
  apply eq_term_upto_univ_it_mkLambda_or_LetIn_r; exact _.
Qed.

Lemma eq_term_upto_univ_it_mkProd_or_LetIn Σ Re Rle Γ :
  RelationClasses.Reflexive Re ->
  respectful (eq_term_upto_univ Σ Re Rle) (eq_term_upto_univ Σ Re Rle)
             (it_mkProd_or_LetIn Γ) (it_mkProd_or_LetIn Γ).
Proof.
  intros he u v h.
  induction Γ as [| [na [b|] A] Γ ih ] in u, v, h |- *.
  - assumption.
  - simpl. cbn. apply ih. constructor ; try apply eq_term_upto_univ_refl.
    all: auto.
  - simpl. cbn. apply ih. constructor ; try apply eq_term_upto_univ_refl.
    all: auto.
Qed.

Lemma eq_term_it_mkProd_or_LetIn {cf:checker_flags} Σ φ Γ:
  respectful (eq_term Σ φ) (eq_term Σ φ)
             (it_mkProd_or_LetIn Γ) (it_mkProd_or_LetIn Γ).
Proof.
  eapply eq_term_upto_univ_it_mkProd_or_LetIn ; exact _.
Qed.

Lemma eq_term_it_mkLambda_or_LetIn_inv {cf:checker_flags} Σ φ Γ u v :
    eq_term Σ φ (it_mkLambda_or_LetIn Γ u) (it_mkLambda_or_LetIn Γ v) ->
    eq_term Σ  φ u v.
Proof.
  revert u v. induction Γ as [| [na [b|] A] Γ ih ] ; intros u v h.
  - assumption.
  - simpl in h. cbn in h. apply ih in h. inversion h. subst.
    assumption.
  - simpl in h. cbn in h. apply ih in h. inversion h. subst.
    assumption.
Qed.

Lemma eq_term_upto_univ_mkApps_inv Σ Re Rle u l u' l' :
  isApp u = false ->
  isApp u' = false ->
  eq_term_upto_univ Σ Re Rle (mkApps u l) (mkApps u' l') ->
  eq_term_upto_univ_napp Σ Re Rle #|l| u u' * All2 (eq_term_upto_univ Σ Re Re) l l'.
Proof.
  intros hu hu' h.
  apply eq_term_upto_univ_mkApps_l_inv in h as hh.
  destruct hh as [v [args [[h1 h2] h3]]].
  apply eq_term_upto_univ_isApp in h1 as hh1. rewrite hu in hh1.
  apply mkApps_notApp_inj in h3 ; auto.
  destruct h3 as [? ?]. subst. split ; auto.
Qed.

Lemma isLambda_eq_term_l Σ Re u v :
    isLambda u ->
    eq_term_upto_univ Σ Re Re u v ->
    isLambda v.
Proof.
  intros h e.
  destruct u; try discriminate.
  depelim e. auto.
Qed.

Lemma isLambda_eq_term_r Σ Re u v :
    isLambda v ->
    eq_term_upto_univ Σ Re Re u v ->
    isLambda u.
Proof.
  intros h e.
  destruct v ; try discriminate.
  depelim e. auto.
Qed.

Lemma isConstruct_app_eq_term_l Σ Re u v :
    isConstruct_app u ->
    eq_term_upto_univ Σ Re Re u v ->
    isConstruct_app v.
Proof.
  intros h e.
  case_eq (decompose_app u). intros t1 l1 e1.
  case_eq (decompose_app v). intros t2 l2 e2.
  unfold isConstruct_app in *.
  rewrite e1 in h. cbn in h.
  rewrite e2. cbn.
  destruct t1 ; try discriminate.
  apply decompose_app_inv in e1 as ?. subst.
  apply decompose_app_inv in e2 as ?. subst.
  apply eq_term_upto_univ_mkApps_inv in e as hh.
  - destruct hh as [h1 h2].
    dependent destruction h1. reflexivity.
  - reflexivity.
  - eapply decompose_app_notApp. eassumption.
Qed.

Lemma isConstruct_app_eq_term_r :
  forall Σ Re u v,
    isConstruct_app v ->
    eq_term_upto_univ Σ Re Re u v ->
    isConstruct_app u.
Proof.
  intros Σ Re u v h e.
  case_eq (decompose_app u). intros t1 l1 e1.
  case_eq (decompose_app v). intros t2 l2 e2.
  unfold isConstruct_app in *.
  rewrite e2 in h. cbn in h.
  rewrite e1. cbn.
  destruct t2 ; try discriminate.
  apply decompose_app_inv in e1 as ?. subst.
  apply decompose_app_inv in e2 as ?. subst.
  apply eq_term_upto_univ_mkApps_inv in e as hh.
  - destruct hh as [h1 h2].
    dependent destruction h1. reflexivity.
  - eapply decompose_app_notApp. eassumption.
  - reflexivity.
Qed.

Lemma R_global_instance_flip Σ gr napp
  (Re Rle Rle' : Universe.t -> Universe.t -> Prop) u v:
  RelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Rle ->
  RelationClasses.Symmetric Re ->
  RelationClasses.Transitive Re ->
  RelationClasses.Transitive Rle ->
  RelationClasses.subrelation Re Rle ->
  (forall x y, Rle x y -> Rle' y x) ->
  R_global_instance Σ Re Rle gr napp u v ->
  R_global_instance Σ Re Rle' gr napp v u.
Proof.
  intros Rerefl Rlerefl Resym Retrans Rletrans incl incl'.
  unfold R_global_instance_gen, R_opt_variance.
  destruct global_variance_gen as [vs|] eqn:var.
  - induction u in vs, v |- *; destruct v; simpl; auto;
    destruct vs as [|v' vs]; simpl; auto.
    intros [Ra Ru']. split.
    destruct v'; simpl; auto.
    apply IHu; auto.
  - apply Forall2_symP; eauto.
Qed.

Lemma eq_term_upto_univ_napp_flip Σ (Re Rle Rle' : Universe.t -> Universe.t -> Prop) napp u v :
  RelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Rle ->
  RelationClasses.Symmetric Re ->
  RelationClasses.Transitive Re ->
  RelationClasses.Transitive Rle ->
  RelationClasses.subrelation Re Rle ->
  (forall x y, Rle x y -> Rle' y x) ->
  eq_term_upto_univ_napp Σ Re Rle napp u v ->
  eq_term_upto_univ_napp Σ Re Rle' napp v u.
Proof.
  intros Rerefl Rlerefl Resym Retrans Rletrans incl incl' H.
  assert (Resub : RelationClasses.subrelation Re Re).
  { typeclasses eauto. }
  revert Rerefl Rlerefl Resym Retrans Rletrans incl incl' Resub.
  revert Re Rle u v H Rle'.
  induction 1; intros; constructor; intuition auto.
  all:try solve [now symmetry].
  all:eauto using R_global_instance_flip.
  - eapply All2_sym. solve_all.
    * eapply eq_context_sym; try tc. tas.
    * now eapply eq_term_upto_univ_sym.
  - eapply All2_sym. solve_all.
    now eapply eq_term_upto_univ_sym.
    now eapply eq_term_upto_univ_sym.
    now symmetry.
  - eapply All2_sym. solve_all.
    now eapply eq_term_upto_univ_sym.
    now eapply eq_term_upto_univ_sym.
    now symmetry.
Qed.

Lemma eq_univ_make :
  forall u u',
    Forall2 eq (map Universe.make u) (map Universe.make u') ->
    u = u'.
Proof.
  intros u u' H. eapply Forall2_map' in H.
  eapply Forall2_eq. eapply Forall2_impl; tea.
  clear. intros [] [] H; now inversion H.
Qed.

(** ws_cumul_pb of binder annotations *)
Notation eq_annots Γ Δ :=
  (Forall2 (fun na decl => eq_binder_annot na (decl_name decl)) Γ Δ).

Lemma eq_context_gen_binder_annot Γ Δ :
  eq_context_gen eq eq Γ Δ -> eq_annots (forget_types Γ) Δ.
Proof.
  induction 1; constructor; auto.
  destruct p; auto.
Qed.

Lemma eq_annots_fold (Γ : list aname) (f : nat -> term -> term) (Δ : context) :
  eq_annots Γ (fold_context_k f Δ) <-> eq_annots Γ Δ.
Proof.
  induction Δ in Γ |- *.
  - cbn; auto. reflexivity.
  - rewrite fold_context_k_snoc0 /=.
    destruct Γ; split; intros H; depelim H; constructor; auto;
    now apply IHΔ.
Qed.

Lemma eq_annots_subst_context (Γ : list aname) s k (Δ : context) :
  eq_annots Γ (subst_context s k Δ) <-> eq_annots Γ Δ.
Proof.
  apply eq_annots_fold.
Qed.

Lemma eq_annots_lift_context (Γ : list aname) n k (Δ : context) :
  eq_annots Γ (lift_context n k Δ) <-> eq_annots Γ Δ.
Proof.
  apply eq_annots_fold.
Qed.

#[global]
Instance Forall2_ext {A B} :
  Proper (pointwise_relation A (pointwise_relation B iff) ==> eq ==> eq ==> iff) (@Forall2 A B).
Proof.
  intros f g Hfg ?? -> ?? ->.
  split; intro; eapply Forall2_impl; tea; apply Hfg.
Qed.

Lemma eq_annots_subst_instance_ctx (Γ : list aname) u (Δ : context) :
  eq_annots Γ Δ@[u] <-> eq_annots Γ Δ.
Proof.
  etransitivity. eapply Forall2_map_right.
  eapply Forall2_ext; auto.
  intros x y; reflexivity.
Qed.

Lemma eq_annots_inst_case_context (Γ : list aname) pars puinst (ctx : context) :
  eq_annots Γ ctx <->
  eq_annots Γ (PCUICCases.inst_case_context pars puinst ctx).
Proof.
  etransitivity. symmetry; eapply (eq_annots_subst_instance_ctx _ puinst).
  etransitivity.
  symmetry; eapply (eq_annots_subst_context _ (List.rev pars) 0).
  reflexivity.
Qed.
