(* Distributed under the terms of the MIT license. *)
From Coq Require Import CMorphisms.
From MetaCoq.Template Require Import LibHypsNaming config utils Reflect.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICReflect PCUICContextRelation.

Require Import ssreflect.
From Equations.Prop Require Import DepElim.
From Equations Require Import Equations.
Set Equations With UIP.

Instance All2_fold_len P Γ Δ : HasLen (All2_fold P Γ Δ) #|Γ| #|Δ| :=
  All2_fold_length.

Implicit Types (cf : checker_flags).

Definition R_universe_instance R :=
  fun u u' => Forall2 R (List.map Universe.make u) (List.map Universe.make u').

(** Cumulative inductive types:

  To simplify the development, we allow the variance list to not exactly 
  match the instances, so as to keep syntactic equality an equivalence relation
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

Definition global_variance Σ gr napp :=
  match gr with
  | IndRef ind =>
    match lookup_inductive Σ ind with
    | Some (mdecl, idecl) => 
      match destArity [] idecl.(ind_type) with
      | Some (ctx, _) => if (context_assumptions ctx) <=? napp then mdecl.(ind_variance)
        else None
      | None => None
      end
    | None => None
    end
  | ConstructRef ind k =>
    match lookup_constructor Σ ind k with
    | Some (mdecl, idecl, cdecl) =>
      if (cdecl.(cstr_arity) + mdecl.(ind_npars))%nat <=? napp then
        (** Fully applied constructors are always compared at the same supertype, 
          which implies that no universe equality needs to be checked here. *)
        Some []
      else None
    | _ => None
    end
  | _ => None
  end.

Definition R_opt_variance Re Rle v :=
  match v with 
  | Some v => R_universe_instance_variance Re Rle v
  | None => R_universe_instance Re
  end.

Definition R_global_instance Σ Re Rle gr napp :=
  R_opt_variance Re Rle (global_variance Σ gr napp).

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

Notation eq_context_gen eq_term leq_term :=
  (All2_fold (fun _ _ => compare_decls eq_term leq_term)).

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

Instance compare_decl_refl eq_term leq_term : 
  CRelationClasses.Reflexive eq_term -> 
  CRelationClasses.Reflexive leq_term -> 
  CRelationClasses.Reflexive (compare_decls eq_term leq_term).    
Proof.
  intros heq hle d.
  destruct d as [na [b|] ty]; constructor; auto; reflexivity.
Qed.

Instance compare_decl_sym eq_term leq_term :
  CRelationClasses.Symmetric eq_term -> 
  CRelationClasses.Symmetric leq_term -> 
  CRelationClasses.Symmetric (compare_decls eq_term leq_term).    
Proof.
  intros heq hle d d' []; constructor; auto; now symmetry.
Qed.

Instance compare_decl_trans eq_term leq_term :
  CRelationClasses.Transitive eq_term -> 
  CRelationClasses.Transitive leq_term -> 
  CRelationClasses.Transitive (compare_decls eq_term leq_term).    
Proof.
  intros hle hre x y z h h'; depelim h; depelim h'; constructor; auto;
  etransitivity; eauto.
Qed.

Instance eq_context_refl eq_term leq_term : 
  CRelationClasses.Reflexive eq_term -> 
  CRelationClasses.Reflexive leq_term -> 
  CRelationClasses.Reflexive (eq_context_gen eq_term leq_term).    
Proof.
  intros heq hle x.
  eapply All2_fold_refl.
  intros. reflexivity. 
Qed.

Instance eq_context_sym eq_term leq_term : 
  CRelationClasses.Symmetric eq_term -> 
  CRelationClasses.Symmetric leq_term -> 
  CRelationClasses.Symmetric (eq_context_gen eq_term leq_term).    
Proof.
  intros heq hle x.
  eapply All2_fold_sym.
  intros. now symmetry. 
Qed.

Instance eq_context_trans eq_term leq_term : 
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
  ((eq_context_gen eq_term eq_term p.(pcontext) p'.(pcontext)) *
    eq_term p.(preturn) p'.(preturn))).

(** ** Syntactic equality up-to universes
  We don't look at printing annotations *)

(** Equality is indexed by a natural number that counts the number of applications
  that surround the current term, used to implement cumulativity of inductive types
  correctly (only fully applied constructors and inductives benefit from it). *)  

Inductive eq_term_upto_univ_napp Σ (Re Rle : Universe.t -> Universe.t -> Prop) (napp : nat) : term -> term -> Type :=
| eq_Rel n  :
    eq_term_upto_univ_napp Σ Re Rle napp (tRel n) (tRel n)

| eq_Evar e args args' :
    All2 (eq_term_upto_univ_napp Σ Re Re 0) args args' ->
    eq_term_upto_univ_napp Σ Re Rle napp (tEvar e args) (tEvar e args')

| eq_Var id :
    eq_term_upto_univ_napp Σ Re Rle napp (tVar id) (tVar id)

| eq_Sort s s' :
    Rle s s' ->
    eq_term_upto_univ_napp Σ Re Rle napp (tSort s) (tSort s')

| eq_App t t' u u' :
    eq_term_upto_univ_napp Σ Re Rle (S napp) t t' ->
    eq_term_upto_univ_napp Σ Re Re 0 u u' ->
    eq_term_upto_univ_napp Σ Re Rle napp (tApp t u) (tApp t' u')

| eq_Const c u u' :
    R_universe_instance Re u u' ->
    eq_term_upto_univ_napp Σ Re Rle napp (tConst c u) (tConst c u')

| eq_Ind i u u' :
    R_global_instance Σ Re Rle (IndRef i) napp u u' ->
    eq_term_upto_univ_napp Σ Re Rle napp (tInd i u) (tInd i u')

| eq_Construct i k u u' :
    R_global_instance Σ Re Rle (ConstructRef i k) napp u u' ->
    eq_term_upto_univ_napp Σ Re Rle napp (tConstruct i k u) (tConstruct i k u')

| eq_Lambda na na' ty ty' t t' :
    eq_binder_annot na na' ->
    eq_term_upto_univ_napp Σ Re Re 0 ty ty' ->
    eq_term_upto_univ_napp Σ Re Rle 0 t t' ->
    eq_term_upto_univ_napp Σ Re Rle napp (tLambda na ty t) (tLambda na' ty' t')

| eq_Prod na na' a a' b b' :
    eq_binder_annot na na' ->
    eq_term_upto_univ_napp Σ Re Re 0 a a' ->
    eq_term_upto_univ_napp Σ Re Rle 0 b b' ->
    eq_term_upto_univ_napp Σ Re Rle napp (tProd na a b) (tProd na' a' b')

| eq_LetIn na na' t t' ty ty' u u' :
    eq_binder_annot na na' ->
    eq_term_upto_univ_napp Σ Re Re 0 t t' ->
    eq_term_upto_univ_napp Σ Re Re 0 ty ty' ->
    eq_term_upto_univ_napp Σ Re Rle 0 u u' ->
    eq_term_upto_univ_napp Σ Re Rle napp (tLetIn na t ty u) (tLetIn na' t' ty' u')

| eq_Case indn p p' c c' brs brs' :
    eq_predicate (eq_term_upto_univ_napp Σ Re Re 0) Re p p' ->
    eq_term_upto_univ_napp Σ Re Re 0 c c' ->
    All2 (fun x y =>
      eq_context_gen (eq_term_upto_univ_napp Σ Re Re 0) 
        (eq_term_upto_univ_napp Σ Re Re 0)
        (bcontext x) (bcontext y) *
      eq_term_upto_univ_napp Σ Re Re 0 (bbody x) (bbody y)
    ) brs brs' ->
    eq_term_upto_univ_napp Σ Re Rle napp (tCase indn p c brs) (tCase indn p' c' brs')

| eq_Proj p c c' :
    eq_term_upto_univ_napp Σ Re Re 0 c c' ->
    eq_term_upto_univ_napp Σ Re Rle napp (tProj p c) (tProj p c')

| eq_Fix mfix mfix' idx :
    All2 (fun x y =>
      eq_term_upto_univ_napp Σ Re Re 0 x.(dtype) y.(dtype) *
      eq_term_upto_univ_napp Σ Re Re 0 x.(dbody) y.(dbody) *
      (x.(rarg) = y.(rarg)) *
      eq_binder_annot x.(dname) y.(dname)
    )%type mfix mfix' ->
    eq_term_upto_univ_napp Σ Re Rle napp (tFix mfix idx) (tFix mfix' idx)

| eq_CoFix mfix mfix' idx :
    All2 (fun x y =>
      eq_term_upto_univ_napp Σ Re Re 0 x.(dtype) y.(dtype) *
      eq_term_upto_univ_napp Σ Re Re 0 x.(dbody) y.(dbody) *
      (x.(rarg) = y.(rarg)) *
      eq_binder_annot x.(dname) y.(dname)
    ) mfix mfix' ->
    eq_term_upto_univ_napp Σ Re Rle napp (tCoFix mfix idx) (tCoFix mfix' idx)
    
| eq_Prim i : eq_term_upto_univ_napp Σ Re Rle napp (tPrim i) (tPrim i).

Notation eq_term_upto_univ Σ Re Rle := (eq_term_upto_univ_napp Σ Re Rle 0).

(* ** Syntactic conversion up-to universes *)

Definition eq_term `{checker_flags} Σ φ :=
  eq_term_upto_univ Σ (eq_universe φ) (eq_universe φ).

(* ** Syntactic cumulativity up-to universes *)

Definition leq_term `{checker_flags} Σ φ :=
  eq_term_upto_univ Σ (eq_universe φ) (leq_universe φ).

Lemma R_global_instance_refl Σ Re Rle gr napp u : 
  RelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Rle ->
  R_global_instance Σ Re Rle gr napp u u.
Proof.
  intros rRE rRle.
  rewrite /R_global_instance.
  destruct global_variance as [v|] eqn:lookup.
  - induction u in v |- *; simpl; auto;
    unfold R_opt_variance in IHu; destruct v; simpl; auto.
    split; auto.
    destruct t; simpl; auto.
  - apply Forall2_same; eauto.
Qed.

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

Hint Resolve @eq_binder_annot_refl : core.

(* TODO MOVE *)
Existing Instance All2_symP.

(* TODO MOVE *)
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
Hint Resolve eq_binder_relevances_refl : core.

Instance R_universe_instance_refl Re : RelationClasses.Reflexive Re -> 
  RelationClasses.Reflexive (R_universe_instance Re).
Proof. intros tRe x. eapply Forall2_map. 
  induction x; constructor; auto.
Qed.

Instance R_universe_instance_sym Re : RelationClasses.Symmetric Re -> 
  RelationClasses.Symmetric (R_universe_instance Re).
Proof. intros tRe x y. now eapply Forall2_symP. Qed.
 
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

Instance eq_predicate_refl Re Ru :
  CRelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Ru ->
  CRelationClasses.Reflexive (eq_predicate Re Ru).
Proof.
  intros hre hru.
  intros p. unfold eq_predicate; intuition auto; try reflexivity.
  eapply All2_same; reflexivity.
Qed.

Instance eq_term_upto_univ_refl Σ Re Rle napp :
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

Instance eq_term_refl `{checker_flags} Σ φ : Reflexive (eq_term Σ φ).
Proof.
  apply eq_term_upto_univ_refl. all: exact _.
Qed.

Instance leq_term_refl `{checker_flags} Σ φ : Reflexive (leq_term Σ φ).
Proof.
  apply eq_term_upto_univ_refl; exact _.
Qed.

Derive Signature for eq_term_upto_univ_napp.

Lemma R_global_instance_sym Σ Re Rle gr napp u u' : 
  RelationClasses.Symmetric Re ->
  RelationClasses.Symmetric Rle ->
  R_global_instance Σ Re Rle gr napp u' u ->
  R_global_instance Σ Re Rle gr napp u u'.
Proof.
  intros rRE rRle.
  rewrite /R_global_instance.
  destruct global_variance as [v|] eqn:lookup.
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

Instance eq_term_upto_univ_sym Σ Re Rle napp :
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

Instance eq_predicate_sym Re Ru :
  CRelationClasses.Symmetric Re ->
  RelationClasses.Symmetric Ru ->
  CRelationClasses.Symmetric (eq_predicate Re Ru).
Proof.
  intros hre hru.
  intros p. unfold eq_predicate; intuition auto; try now symmetry.
Qed.

Instance eq_term_sym `{checker_flags} Σ φ : Symmetric (eq_term Σ φ).
Proof.
  eapply eq_term_upto_univ_sym. all: exact _.
Qed.

Instance R_global_instance_trans Σ Re Rle gr napp :
  RelationClasses.Transitive Re ->
  RelationClasses.Transitive Rle ->
  RelationClasses.Transitive (R_global_instance Σ Re Rle gr napp).
Proof.
  intros he hle x y z.
  unfold R_global_instance, R_opt_variance.
  destruct global_variance as [v|].
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

Instance eq_predicate_trans Re Ru :
  CRelationClasses.Transitive Re ->
  RelationClasses.Transitive Ru ->
  CRelationClasses.Transitive (eq_predicate Re Ru).
Proof.
  intros hre hru.
  intros p. unfold eq_predicate; intuition auto; try now etransitivity.
  eapply All2_trans; tea.
Qed.

Instance eq_term_upto_univ_trans Σ Re Rle napp :
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
    * clear -H he a a0.
      induction a in a0, brs'0 |- *.
      + assumption.
      + depelim a0. destruct p. constructor; auto.
        destruct r as [[h1 h1'] [h2 h3]].
        split.
        eapply onctx_eq_ctx_trans in h1; eauto.
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

Instance eq_term_trans {cf:checker_flags} Σ φ : Transitive (eq_term Σ φ).
Proof.
  eapply eq_term_upto_univ_trans. all: exact _.
Qed.

Instance leq_term_trans {cf:checker_flags} Σ φ : Transitive (leq_term Σ φ).
Proof.
  eapply eq_term_upto_univ_trans ; exact _.
Qed.

Instance eq_term_upto_univ_equiv Σ Re (hRe : RelationClasses.Equivalence Re)
  : Equivalence (eq_term_upto_univ Σ Re Re).
Proof.
  constructor. all: exact _.
Defined.

Instance eq_context_equiv {cf} Σ φ : Equivalence (eq_context_gen (eq_term Σ φ) (eq_term Σ φ)).
Proof.
  constructor; try exact _.
Qed.

Instance leq_context_preord {cf} Σ φ : PreOrder (eq_context_gen (eq_term Σ φ) (leq_term Σ φ)).
Proof.
  constructor; try exact _.
Qed.

Instance eq_term_equiv {cf:checker_flags} Σ φ : Equivalence (eq_term Σ φ) :=
  {| Equivalence_Reflexive := eq_term_refl _ _;
     Equivalence_Symmetric := eq_term_sym _ _;
     Equivalence_Transitive := eq_term_trans _ _ |}.

Instance leq_term_preorder {cf:checker_flags} Σ φ : PreOrder (leq_term Σ φ) :=
  {| PreOrder_Reflexive := leq_term_refl _ _;
     PreOrder_Transitive := leq_term_trans _ _ |}.

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

Instance R_global_instance_equiv Σ R (hR : RelationClasses.Equivalence R) gr napp
  : RelationClasses.Equivalence (R_global_instance Σ R R gr napp).
Proof.
  split.
  - intro. apply R_global_instance_refl; typeclasses eauto.
  - intros x y xy. eapply R_global_instance_sym; auto; typeclasses eauto.
  - intros x y z xy yz. eapply R_global_instance_trans; eauto; typeclasses eauto.
Qed.

Instance R_global_instance_antisym Σ Re Rle (hRe : RelationClasses.Equivalence Re) gr napp :
  RelationClasses.Antisymmetric _ Re Rle ->
  RelationClasses.Antisymmetric _ (R_global_instance Σ Re Re gr napp) (R_global_instance Σ Re Rle gr napp).
Proof.
  intros hR u v.
  unfold R_global_instance, R_opt_variance.
  destruct global_variance; auto.
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
  rewrite /global_variance.
  destruct gr; try congruence.
  - destruct lookup_inductive as [[mdecl idec]|] => //.
    destruct destArity as [[ctx s]|] => //.
    elim: Nat.leb_spec => // cass indv.
    elim: Nat.leb_spec => //. lia.
  - destruct lookup_constructor as [[[mdecl idecl] cdecl]|] => //.
    elim: Nat.leb_spec => // cass indv.
    elim: Nat.leb_spec => //. lia.
Qed.

Instance R_global_instance_impl_same_napp Σ Re Re' Rle Rle' gr napp :
  RelationClasses.subrelation Re Re' ->
  RelationClasses.subrelation Rle Rle' ->
  subrelation (R_global_instance Σ Re Rle gr napp) (R_global_instance Σ Re' Rle' gr napp).
Proof.
  intros he hle t t'.
  rewrite /R_global_instance /R_opt_variance.
  destruct global_variance as [v|] eqn:glob.
  induction t in v, t' |- *; destruct v, t'; simpl; auto.
  intros []; split; auto.
  destruct t0; simpl; auto.
  now eapply R_universe_instance_impl'.
Qed.

Instance R_global_instance_impl Σ Re Re' Rle Rle' gr napp napp' :
  RelationClasses.subrelation Re Re' ->
  RelationClasses.subrelation Re Rle' ->
  RelationClasses.subrelation Rle Rle' ->
  napp <= napp' ->
  subrelation (R_global_instance Σ Re Rle gr napp) (R_global_instance Σ Re' Rle' gr napp').
Proof.
  intros he hle hele hnapp t t'.
  rewrite /R_global_instance /R_opt_variance.
  destruct global_variance as [v|] eqn:glob.
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

Lemma global_variance_empty gr napp : global_variance [] gr napp = None.
Proof.
  destruct gr; auto.
Qed.

(** Pure syntactic equality, without cumulative inductive types subtyping *)

Instance R_global_instance_empty_impl Σ Re Re' Rle Rle' gr napp napp' :
  RelationClasses.subrelation Re Re' ->
  RelationClasses.subrelation Rle Rle' ->
  RelationClasses.subrelation Re Rle' ->
  subrelation (R_global_instance [] Re Rle gr napp) (R_global_instance Σ Re' Rle' gr napp').
Proof.
  intros he hle hele t t'.
  rewrite /R_global_instance /R_opt_variance. simpl.
  rewrite global_variance_empty.
  destruct global_variance as [v|]; eauto using R_universe_instance_impl'.
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
    * eapply onctx_eq_ctx_impl in a0; tea. eauto.
    * eapply onctx_eq_ctx_impl in a4; tea. eauto.
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x [? ?] y [[[? ?] ?] ?]. repeat split; eauto.
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x [? ?] y [[[? ?] ?] ?]. repeat split; eauto.
Qed.

Instance eq_term_upto_univ_empty_impl Σ Re Re' Rle Rle' napp napp' :
  RelationClasses.subrelation Re Re' ->
  RelationClasses.subrelation Rle Rle' ->
  RelationClasses.subrelation Re Rle' ->
  subrelation (eq_term_upto_univ_napp [] Re Rle napp) (eq_term_upto_univ_napp Σ Re' Rle' napp').
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
    * eapply onctx_eq_ctx_impl in a0; tea. eauto.
    * eapply onctx_eq_ctx_impl in a4; tea. eauto.
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x [? ?] y [[[? ?] ?] ?]. repeat split; eauto.
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x [? ?] y [[[? ?] ?] ?]. repeat split; eauto.    
Qed.

Instance eq_term_upto_univ_leq Σ Re Rle napp napp' :
  RelationClasses.subrelation Re Rle ->
  napp <= napp' ->
  subrelation (eq_term_upto_univ_napp Σ Re Re napp) (eq_term_upto_univ_napp Σ Re Rle napp').
Proof.
  intros H. eapply eq_term_upto_univ_impl; exact _.
Qed.

Instance eq_term_leq_term {cf:checker_flags} Σ φ
  : subrelation (eq_term Σ φ) (leq_term Σ φ).
Proof.
  eapply eq_term_upto_univ_leq; auto; exact _.
Qed.

Instance leq_term_partial_order {cf:checker_flags} Σ φ
  : PartialOrder (eq_term Σ φ) (leq_term Σ φ).
Proof.
  split. intros eqxy; split; now eapply eq_term_leq_term.
  intros [xy yx].
  now eapply leq_term_antisym.
Qed.

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
    * apply All2_fold_mapi.
      eapply All2_fold_impl_onctx; tea; simpl; eauto.
      unfold ondecl;
      intros Γ Γ' d d' IH []; constructor; intuition eauto.
    * rewrite -?(All2_fold_length e).
      eapply hh0; eauto.
    * eapply All2_fold_mapi.
      eapply All2_fold_impl_onctx; tea; simpl; eauto.
      unfold ondecl;
      intros Γ Γ' d d' IH []; constructor; intuition pcuic.
    * rewrite (All2_fold_length a). now eapply hh4.
  - cbn. constructor.
    pose proof (All2_length a).
    solve_all. rewrite H. eauto.
  - cbn. constructor.
    pose proof (All2_length a).
    solve_all. rewrite H. eauto.
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
    * eapply All2_fold_mapi.
      eapply All2_fold_impl_onctx; tea; simpl; eauto.
      unfold ondecl; intros Γ Γ' d d' IH []; constructor; simpl; intuition eauto.
    * rewrite -(All2_fold_length e). eapply e1; eauto.
    * eapply All2_fold_mapi.
      eapply All2_fold_impl_onctx; tea; simpl; eauto.
      unfold ondecl; intros Γ Γ' d d' IH []; simpl; constructor; intuition eauto.
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

(** ** Boolean version **  *)

Definition compare_universe_variance (equ lequ : Universe.t -> Universe.t -> bool) v u u' :=
  match v with
  | Variance.Irrelevant => true
  | Variance.Covariant => lequ (Universe.make u) (Universe.make u')
  | Variance.Invariant => equ (Universe.make u) (Universe.make u')
  end.

Definition compare_universe_instance equ u u' :=
  forallb2 equ (map Universe.make u) (map Universe.make u').
  
Fixpoint compare_universe_instance_variance equ lequ v u u' :=
  match u, u' with
  | u :: us, u' :: us' =>
    match v with
    | [] => compare_universe_instance_variance equ lequ v us us' 
      (* Missing variance stands for irrelevance *)
    | v :: vs => compare_universe_variance equ lequ v u u' &&
        compare_universe_instance_variance equ lequ vs us us'
    end
  | [], [] => true
  | _, _ => false
  end.

Definition compare_global_instance Σ equ lequ gr napp :=
  match global_variance Σ gr napp with
  | Some v => compare_universe_instance_variance equ lequ v
  | None => compare_universe_instance equ
  end.

Definition eqb_binder_annots (x y : list aname) : bool :=
  forallb2 eqb_binder_annot x y.

Fixpoint eqb_term_upto_univ_napp Σ (equ lequ : Universe.t -> Universe.t -> bool) napp (u v : term) : bool :=
  match u, v with
  | tRel n, tRel m =>
    eqb n m

  | tEvar e args, tEvar e' args' =>
    eqb e e' &&
    forallb2 (eqb_term_upto_univ_napp Σ equ equ 0) args args'

  | tVar id, tVar id' =>
    eqb id id'

  | tSort u, tSort u' =>
    lequ u u'

  | tApp u v, tApp u' v' =>
    eqb_term_upto_univ_napp Σ equ lequ (S napp) u u' &&
    eqb_term_upto_univ_napp Σ equ equ 0 v v'

  | tConst c u, tConst c' u' =>
    eqb c c' &&
    forallb2 equ (map Universe.make u) (map Universe.make u')

  | tInd i u, tInd i' u' =>
    eqb i i' &&
    compare_global_instance Σ equ lequ (IndRef i) napp u u'

  | tConstruct i k u, tConstruct i' k' u' =>
    eqb i i' &&
    eqb k k' &&
    compare_global_instance Σ equ lequ (ConstructRef i k) napp u u'

  | tLambda na A t, tLambda na' A' t' =>
    eqb_binder_annot na na' &&
    eqb_term_upto_univ_napp Σ equ equ 0 A A' &&
    eqb_term_upto_univ_napp Σ equ lequ 0 t t'

  | tProd na A B, tProd na' A' B' =>
    eqb_binder_annot na na' &&
    eqb_term_upto_univ_napp Σ equ equ 0 A A' &&
    eqb_term_upto_univ_napp Σ equ lequ 0 B B'

  | tLetIn na B b u, tLetIn na' B' b' u' =>
    eqb_binder_annot na na' &&
    eqb_term_upto_univ_napp Σ equ equ 0 B B' &&
    eqb_term_upto_univ_napp Σ equ equ 0 b b' &&
    eqb_term_upto_univ_napp Σ equ lequ 0 u u'

  | tCase indp p c brs, tCase indp' p' c' brs' =>
    eqb indp indp' &&
    eqb_predicate_gen
      (fun u u' => forallb2 equ (map Universe.make u) (map Universe.make u'))
      (bcompare_decls (eqb_term_upto_univ_napp Σ equ equ 0) 
        (eqb_term_upto_univ_napp Σ equ equ 0))
      (eqb_term_upto_univ_napp Σ equ equ 0) p p' &&
    eqb_term_upto_univ_napp Σ equ equ 0 c c' &&
    forallb2 (fun x y =>
      forallb2 
        (bcompare_decls (eqb_term_upto_univ_napp Σ equ equ 0) 
          (eqb_term_upto_univ_napp Σ equ equ 0))
        x.(bcontext) y.(bcontext) &&
      eqb_term_upto_univ_napp Σ equ equ 0 (bbody x) (bbody y)
    ) brs brs'

  | tProj p c, tProj p' c' =>
    eqb p p' &&
    eqb_term_upto_univ_napp Σ equ equ 0 c c'

  | tFix mfix idx, tFix mfix' idx' =>
    eqb idx idx' &&
    forallb2 (fun x y =>
      eqb_term_upto_univ_napp Σ equ equ 0 x.(dtype) y.(dtype) &&
      eqb_term_upto_univ_napp Σ equ equ 0 x.(dbody) y.(dbody) &&
      eqb x.(rarg) y.(rarg) &&
      eqb_binder_annot x.(dname) y.(dname)
    ) mfix mfix'

  | tCoFix mfix idx, tCoFix mfix' idx' =>
    eqb idx idx' &&
    forallb2 (fun x y =>
      eqb_term_upto_univ_napp Σ equ equ 0 x.(dtype) y.(dtype) &&
      eqb_term_upto_univ_napp Σ equ equ 0 x.(dbody) y.(dbody) &&
      eqb x.(rarg) y.(rarg) &&
      eqb_binder_annot x.(dname) y.(dname)
    ) mfix mfix'

  | tPrim p, tPrim p' => eqb p p'

  | _, _ => false
  end.

Notation eqb_term_upto_univ Σ eq leq := (eqb_term_upto_univ_napp Σ eq leq 0).

Ltac eqspec :=
  lazymatch goal with
  | |- context [ eqb ?u ?v ] =>
    destruct (eqb_spec u v) ; nodec ; subst
  end.

Ltac eqspecs :=
  repeat eqspec.

Local Ltac equspec equ h :=
  repeat lazymatch goal with
  | |- context [ equ ?x ?y ] =>
    destruct (h x y) ; nodec ; subst
  end.

Local Ltac ih :=
  repeat lazymatch goal with
  | ih : forall lequ Rle napp hle t', reflectT (eq_term_upto_univ_napp _ _ _ napp ?t _) _,
    hle : forall u u', reflectT (?Rle u u') (?lequ u u')
    |- context [ eqb_term_upto_univ _ _ ?lequ ?t ?t' ] =>
    destruct (ih lequ Rle 0 hle t') ; nodec ; subst
  end.

Lemma compare_global_instance_impl (equ lequ : _ -> _ -> bool) Σ Re Rle gr napp :
  RelationClasses.subrelation equ Re ->
  RelationClasses.subrelation lequ Rle ->
  subrelation (compare_global_instance Σ equ lequ gr napp) (R_global_instance Σ Re Rle gr napp).
Proof.
  intros hre hrle x y.
  unfold compare_global_instance, R_global_instance, R_opt_variance.
  destruct global_variance as [v|].
  induction x in v, y |- *; destruct v, y; simpl; auto.
  rtoProp. intros [Hat Hxy]. split; auto.
  destruct t; simpl in *; auto.
  intro. eapply forallb2_Forall2 in H.
  eapply Forall2_impl; tea; eauto.
Qed.

Lemma Forall2_forallb2:
  forall (A : Type) (p : A -> A -> bool) (l l' : list A),
  Forall2 (fun x y : A => p x y) l l' -> forallb2 p l l'.
Proof.
  induction 1; simpl; auto.
  now rewrite H IHForall2.
Qed.

Lemma compare_global_instance_impl_inv (equ lequ : _ -> _ -> bool) Σ Re Rle gr napp :
  RelationClasses.subrelation Re equ ->
  RelationClasses.subrelation Rle lequ ->
  subrelation (R_global_instance Σ Re Rle gr napp) (compare_global_instance Σ equ lequ gr napp).
Proof.
  intros hre hrle x y.
  unfold compare_global_instance, R_global_instance.
  destruct global_variance as [v|]; auto.
  induction x in v, y |- *; destruct v, y; simpl; auto.    
  rtoProp. intros [Hat Hxy]. split; auto.
  destruct t; simpl in *; auto.
  intro. red. eapply Forall2_forallb2.
  eapply Forall2_impl; tea; eauto.
Qed.

Lemma eqb_annot_spec {A} na na' : eqb_binder_annot na na' <-> @eq_binder_annot A A na na'.
Proof.
  unfold eqb_binder_annot, eq_binder_annot.
  now destruct Classes.eq_dec.
Qed.

Lemma eqb_annot_reflect {A} na na' : reflect (@eq_binder_annot A A na na') (eqb_binder_annot na na').
Proof.
  unfold eqb_binder_annot, eq_binder_annot.
  destruct Classes.eq_dec; constructor; auto.
Qed.

Lemma eqb_annot_refl {A} n : @eqb_binder_annot A n n.
Proof.
  apply eqb_annot_spec. reflexivity.
Qed.

Lemma eqb_annots_spec nas nas' : eqb_binder_annots nas nas' <-> Forall2 (on_rel eq binder_relevance) nas nas'.
Proof.
  unfold eqb_binder_annots, eq_binder_annot.
  split; intros.
  eapply forallb2_Forall2 in H.
  eapply (Forall2_impl H). unfold on_rel. apply eqb_annot_spec.
  eapply Forall2_forallb2, (Forall2_impl H); apply eqb_annot_spec.
Qed.

Lemma eqb_annots_reflect nas nas' : reflectT (All2 (on_rel eq binder_relevance) nas nas') (eqb_binder_annots nas nas').
Proof.
  unfold eqb_binder_annots, eq_binder_annot.
  destruct forallb2 eqn:H; constructor.
  eapply Forall2_All2. now apply eqb_annots_spec.
  intros H'; apply All2_Forall2, eqb_annots_spec in H'.
  red in H'. unfold eqb_binder_annots in H'. congruence.
Qed.

(*Lemma eqb_context_reflect ctx ctx' : reflectT (eq_context_gen false (eq_term_up)) *)

Lemma forallb2_bcompare_decl_All2_fold
  (P : term -> term -> bool) Γ Δ : 
  forallb2 (bcompare_decls P P) Γ Δ ->
  All2_fold (fun _ _ => bcompare_decls P P) Γ Δ.
Proof.
  induction Γ as [|[na [b|] ty] Γ] in Δ |- *; destruct Δ as [|[na' [b'|] ty'] Δ]; simpl => //; constructor; auto;
  now move/andb_and: H => [].
Qed.

Lemma reflect_eq_context_IH {Σ equ lequ} {Re Rle : Universe.t -> Universe.t -> Prop} :
  (forall u u', reflectT (Re u u') (equ u u')) ->
  (forall u u', reflectT (Rle u u') (lequ u u')) ->
  forall ctx ctx',
  onctx
      (fun t : term =>
       forall (lequ : Universe.t -> Universe.t -> bool)
         (Rle : Universe.t -> Universe.t -> Prop) 
         (napp : nat),
       (forall u u' : Universe.t, reflectT (Rle u u') (lequ u u')) ->
       forall t' : term,
       reflectT (eq_term_upto_univ_napp Σ Re Rle napp t t')
         (eqb_term_upto_univ_napp Σ equ lequ napp t t')) 
      ctx ->
  reflectT 
    (eq_context_gen (eq_term_upto_univ Σ Re Re) (eq_term_upto_univ Σ Re Re) ctx ctx')
    (forallb2 (bcompare_decls (eqb_term_upto_univ Σ equ equ)
      (eqb_term_upto_univ Σ equ equ)) ctx ctx').
Proof.
  intros hRe hRle ctx ctx' onc.
  eapply equiv_reflectT.
  - intros hcc'.
    eapply All2_fold_forallb2, All2_fold_impl_onctx; tea.
    unfold ondecl; intuition auto.
    depelim X0; cbn in * => //;
    intuition auto.
    + destruct (eqb_annot_reflect na na') => //.
      destruct (a equ Re 0 hRe T') => //.
    + destruct (eqb_annot_reflect na na') => //.
      destruct (b0 equ Re 0 hRe b') => //.
      destruct (a equ Re 0 hRe T') => //.
  - intros hcc'.
    eapply forallb2_bcompare_decl_All2_fold in hcc'; tea.
    eapply All2_fold_impl_onctx in onc; tea; simpl; intuition eauto.
    destruct X0.
    move: H.
    destruct d as [na [bod|] ty], d' as [na' [bod'|] ty']; cbn in * => //.
    + destruct (eqb_annot_reflect na na') => //.
      destruct (r equ Re 0 hRe ty') => //.
      destruct (o equ Re 0 hRe bod') => //.
      now constructor.
      now rewrite andb_false_r.
    + destruct (eqb_annot_reflect na na') => //.
      destruct (r equ Re 0 hRe ty') => //.
      now constructor.
Qed.

Definition reflect_eq_predicate {Σ equ lequ} {Re Rle : Universe.t -> Universe.t -> Prop} :
  (forall u u', reflectT (Re u u') (equ u u')) ->
  (forall u u', reflectT (Rle u u') (lequ u u')) ->
  forall p p',
  tCasePredProp
  (fun t : term =>
   forall (lequ : Universe.t -> Universe.t -> bool)
     (Rle : Universe.t -> Universe.t -> Prop) 
     (napp : nat),
   (forall u u' : Universe.t, reflectT (Rle u u') (lequ u u')) ->
   forall t' : term,
   reflectT (eq_term_upto_univ_napp Σ Re Rle napp t t')
     (eqb_term_upto_univ_napp Σ equ lequ napp t t'))
  (fun t : term =>
   forall (lequ : Universe.t -> Universe.t -> bool)
     (Rle : Universe.t -> Universe.t -> Prop) 
     (napp : nat),
   (forall u u' : Universe.t, reflectT (Rle u u') (lequ u u')) ->
   forall t' : term,
   reflectT (eq_term_upto_univ_napp Σ Re Rle napp t t')
     (eqb_term_upto_univ_napp Σ equ lequ napp t t')) p ->
  reflectT (eq_predicate (eq_term_upto_univ_napp Σ Re Re 0) Re p p') 
    (eqb_predicate_gen (fun u u' => forallb2 equ (map Universe.make u) (map Universe.make u'))
      (bcompare_decls (eqb_term_upto_univ_napp Σ equ equ 0) (eqb_term_upto_univ_napp Σ equ equ 0))
      (eqb_term_upto_univ_napp Σ equ equ 0) p p').
Proof.
  intros.
  solve_all. unfold eq_predicate, eqb_predicate, eqb_predicate_gen.
  simpl; apply equiv_reflectT.
  - intros H; rtoProp.
    destruct H as [onpars [onuinst [pctx pret]]].
    intuition auto; rtoProp; intuition auto.
    * solve_all. destruct (a _ Re 0 X y); auto; try contradiction.
    * red in onuinst. 
      eapply Forall2_forallb2, Forall2_impl; eauto.
      now move=> x y /X.
    * destruct (reflect_eq_context_IH X X0 (pcontext p) (pcontext p') a0) => //.
    * ih. contradiction.
  - move/andb_and => [/andb_and [/andb_and [ppars pinst] pctx] pret].
    intuition auto.
    * solve_all.
      now destruct (a _ _ 0 X y).
    * solve_all. red. apply All2_Forall2.
      eapply (All2_impl pinst); eauto.
      now move=> x y /X.
    * now destruct (reflect_eq_context_IH X X0 (pcontext p) (pcontext p') a0).
    * now destruct (r _ _ 0 X (preturn p')).
Qed.

Lemma reflect_eq_term_upto_univ Σ equ lequ (Re Rle : Universe.t -> Universe.t -> Prop) napp :
  (forall u u', reflectT (Re u u') (equ u u')) ->
  (forall u u', reflectT (Rle u u') (lequ u u')) ->
  forall t t', reflectT (eq_term_upto_univ_napp Σ Re Rle napp t t')
                   (eqb_term_upto_univ_napp Σ equ lequ napp t t').
Proof.
  intros he hle t t'.
  induction t in t', napp, lequ, Rle, hle |- * using term_forall_list_ind.
  all: destruct t' ; nodec.
  (* all: try solve [ *)
  (*   cbn - [eqb] ; eqspecs ; equspec equ h ; ih ; *)
  (*   constructor ; constructor ; assumption *)
  (* ]. *)
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    constructor. constructor ; assumption.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    constructor. constructor ; assumption.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    cbn.
    induction X in l0 |- *.
    + destruct l0.
      * constructor. constructor. constructor.
      * constructor. intro bot. inversion bot. inversion X.
    + destruct l0.
      * constructor. intro bot. inversion bot. subst. inversion X0.
      * cbn. destruct (p _ _ 0 he t).
        -- destruct (IHX l0).
           ++ constructor. constructor. constructor ; try assumption.
              inversion e0. subst. assumption.
           ++ constructor. intro bot. inversion bot. subst.
              inversion X0. subst.
              apply f. constructor. assumption.
        -- constructor. intro bot. apply f.
           inversion bot. subst. inversion X0. subst. assumption.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    constructor. constructor. assumption.
  - cbn - [eqb]. eqspecs. equspec equ he.
    destruct (eqb_annot_reflect n na); ih.
    constructor. constructor; assumption.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle.
    destruct (eqb_annot_reflect n na); ih.
    constructor. constructor ; assumption.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle.
    destruct (eqb_annot_reflect n na); ih.
    constructor. constructor ; assumption.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    destruct (IHt1 lequ Rle (S napp) hle t'1);
    constructor; try (constructor ; assumption).
    intros H; inv H. auto.
    destruct (IHt1 lequ Rle (S napp) hle t'1); constructor; auto.
    intros H; inv H; auto.
    intros H; inv H; auto.
  - cbn - [eqb].
    pose proof (eqb_spec s k) as H.
    match goal with
    | |- context G[ eqb ?x ?y ] =>
      set (toto := eqb x y) in * ;
      let G' := context G[toto] in
      change G'
    end.
    destruct H ; nodec. subst.
    equspec equ he. equspec lequ hle. ih.
    cbn. induction u in ui |- *.
    + destruct ui.
      * constructor. constructor. constructor.
      * constructor. intro bot. inversion bot. subst. inversion H0.
    + destruct ui.
      * constructor. intro bot. inversion bot. subst. inversion H0.
      * cbn. equspec equ he. equspec lequ hle.
        -- cbn. destruct (IHu ui).
           ++ constructor. constructor.
              inversion e. subst.
              constructor ; assumption.
           ++ constructor. intro bot. apply f.
              inversion bot. subst. constructor. inversion H0.
              subst. assumption.
        -- constructor. intro bot. apply f.
           inversion bot. subst. inversion H0. subst.
           assumption.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    simpl; apply equiv_reflectT.
    inversion 1; subst.
    eapply compare_global_instance_impl_inv; eauto.
    apply (reflectT_subrelation he).
    apply (reflectT_subrelation hle).
    intro; constructor; eapply compare_global_instance_impl; eauto.
    apply (reflectT_subrelation' he).
    apply (reflectT_subrelation' hle).
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    simpl; apply equiv_reflectT.
    inversion 1; subst.
    eapply compare_global_instance_impl_inv; eauto.
    apply (reflectT_subrelation he).
    apply (reflectT_subrelation hle).
    intro; constructor; eapply compare_global_instance_impl; eauto.
    apply (reflectT_subrelation' he).
    apply (reflectT_subrelation' hle).

  - cbn - [eqb]. eqspecs => /=.
    destruct (reflect_eq_predicate he hle p p0 X).
    ih. clear X. rename X0 into X.
    induction l in brs, X |- *.
    + destruct brs.
      * constructor. constructor ; try assumption.
        constructor.
      * constructor. intro bot. inversion bot. subst. inversion X2.
    + destruct brs.
      * constructor. intro bot. inversion bot. subst. inversion X2.
      * cbn - [eqb]. inversion X. subst.
        destruct a, b. cbn - [eqb eqb_binder_annots].
        destruct X0 as [onc onbod].
        destruct (reflect_eq_context_IH he hle bcontext bcontext0 onc) => // /=.
        -- cbn - [eqb].
           pose proof (onbod equ Re 0 he bbody0) as hh. cbn in hh.
           destruct hh => /=.
           ++ cbn -[eqb eqb_binder_annots] in *. destruct (IHl X1 brs).
              ** constructor ; try easy. inversion e2. subst.
                 constructor; auto.
              ** constructor. intro bot. apply f. inversion bot. subst.
                 inversion X3. subst. constructor; auto.
           ++ constructor. intro bot. apply f. inversion bot. subst.
              inversion X3. subst. destruct X4. assumption.
        -- constructor. intro bot. inversion bot. subst.
           inversion X3. subst. destruct X4. cbn in e1. subst.
           contradiction.
    + simpl. constructor. intros bot; inv bot; contradiction.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    constructor. constructor ; assumption.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    cbn - [eqb]. induction m in X, mfix |- *.
    + destruct mfix.
      * constructor. constructor. constructor.
      * constructor. intro bot. inversion bot. subst. inversion X0.
    + destruct mfix.
      * constructor. intro bot. inversion bot. subst. inversion X0.
      * cbn - [eqb].
      inversion X. subst.
        destruct X0 as [h1 h2].
        destruct (h1 equ Re 0 he (dtype d)).
        -- destruct (h2 equ Re 0 he (dbody d)).
           ++ cbn - [eqb]. eqspecs.
              ** cbn - [eqb]. destruct (IHm X1 mfix).
                 --- destruct (eqb_annot_reflect (dname a) (dname d)).
                      constructor. constructor. constructor ; try easy.
                     inversion e2. assumption.
                     constructor. intro bot; inversion bot. subst.
                     apply n. inversion X0. subst. destruct X2 as [[? ?] ?].
                     assumption.
                  --- rewrite andb_false_r.
                      constructor. intro bot. apply f.
                     inversion bot. subst. constructor.
                     inversion X0. subst. assumption.                     
              ** constructor. intro bot. inversion bot. subst.
                 apply n. inversion X0. subst. destruct X2 as [[? ?] ?].
                 assumption.
           ++ constructor. intro bot. apply f.
              inversion bot. subst. inversion X0. subst.
              apply X2.
        -- constructor. intro bot. apply f.
           inversion bot. subst. inversion X0. subst. apply X2.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    cbn - [eqb]. induction m in X, mfix |- *.
    + destruct mfix.
      * constructor. constructor. constructor.
      * constructor. intro bot. inversion bot. subst. inversion X0.
    + destruct mfix.
      * constructor. intro bot. inversion bot. subst. inversion X0.
      * cbn - [eqb]. inversion X. subst.
        destruct X0 as [h1 h2].
        destruct (h1 equ Re 0 he (dtype d)).
        -- destruct (h2 equ Re 0 he (dbody d)).
           ++ cbn - [eqb]. eqspecs.
              ** cbn - [eqb]. destruct (IHm X1 mfix).
                 --- destruct (eqb_annot_reflect (dname a) (dname d)).
                    constructor. constructor. constructor ; try easy.
                    inversion e2. assumption.
                    constructor. intro bot; inversion bot. subst.
                    apply n. inversion X0. subst. destruct X2 as [[? ?] ?].
                    assumption.
                 --- rewrite andb_false_r.
                     constructor. intro bot. apply f.
                     inversion bot. subst. constructor.
                     inversion X0. subst. assumption.
              ** constructor. intro bot. inversion bot. subst.
                 apply n. inversion X0. subst. destruct X2 as [[? ?] ?].
                 assumption.
           ++ constructor. intro bot. apply f.
              inversion bot. subst. inversion X0. subst.
              apply X2.
        -- constructor. intro bot. apply f.
           inversion bot. subst. inversion X0. subst. apply X2.
  - cbn - [eqb]. eqspecs. do 2 constructor.
Qed.

Lemma eqb_term_upto_univ_impl (equ lequ : _ -> _ -> bool) Σ Re Rle napp :
  RelationClasses.subrelation equ Re ->
  RelationClasses.subrelation lequ Rle ->
  RelationClasses.subrelation equ Rle ->
  subrelation (eqb_term_upto_univ_napp Σ equ lequ napp) (eq_term_upto_univ_napp Σ Re Rle napp).
Proof.
  intros he hle heqle t t'.
  case: (reflect_eq_term_upto_univ Σ equ lequ equ lequ) => //; eauto.
  1-2:eapply reflectT_pred2.
  intros. eapply eq_term_upto_univ_impl. 5:tea. all:eauto.
Qed.

Lemma compare_global_instance_refl :
  forall Σ (eqb leqb : Universe.t -> Universe.t -> bool) gr napp u,
    (forall u, eqb u u) ->
    (forall u, leqb u u) ->
    compare_global_instance Σ eqb leqb gr napp u u.
Proof.
  intros Σ eqb leqb gr napp u eqb_refl leqb_refl.
  rewrite /compare_global_instance.
  destruct global_variance as [v|].
  induction u in v |- *; destruct v; simpl; auto.
  rtoProp. split; auto.
  destruct t; simpl; auto.
  rewrite /compare_universe_instance.
  rewrite forallb2_map; eapply forallb2_refl; intro; apply eqb_refl.
Qed.

Lemma eq_dec_to_bool_refl {A} {ea : Classes.EqDec A} (x : A) : 
  eq_dec_to_bool x x.
Proof.
  unfold eq_dec_to_bool.
  destruct (Classes.eq_dec x x).
  constructor.
  congruence.
Qed.

Lemma eqb_term_upto_univ_refl :
  forall Σ (eqb leqb : Universe.t -> Universe.t -> bool) napp t,
    (forall u, eqb u u) ->
    (forall u, leqb u u) ->
    eqb_term_upto_univ_napp Σ eqb leqb napp t t.
Proof.
  intros Σ eqb leqb napp t eqb_refl leqb_refl.
  case: (reflect_eq_term_upto_univ Σ eqb leqb eqb leqb napp _ _ t t) => //.
  * intros. eapply equiv_reflectT; auto.
  * intros. eapply equiv_reflectT; auto.
  * intros.
    unshelve epose proof (eq_term_upto_univ_refl Σ eqb leqb napp _ _); eauto.
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

Lemma eq_term_upto_univ_it_mkLambda_or_LetIn Σ Re Rle Γ :
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
  apply eq_term_upto_univ_it_mkLambda_or_LetIn; exact _.
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

Lemma upto_eq_impl Σ Re Rle :
  RelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Rle ->
  subrelation (eq_term_upto_univ Σ eq eq) (eq_term_upto_univ Σ Re Rle).
Proof.
  intros he hle. eapply eq_term_upto_univ_impl. 4:auto.
  all: intros ? ? []; eauto.
Qed.

(** ** Syntactic equality up to printing anotations ** *)

Definition upto_names := eq_term_upto_univ [] eq eq.

Infix "≡" := upto_names (at level 60).

Infix "≡'" := (eq_term_upto_univ [] eq eq) (at level 60).
Notation upto_names' := (eq_term_upto_univ [] eq eq).

Instance upto_names_ref : Reflexive upto_names.
Proof.
  eapply eq_term_upto_univ_refl; exact _.
Qed.

Instance upto_names_sym : Symmetric upto_names.
Proof.
  eapply eq_term_upto_univ_sym; exact _.
Qed.

Instance upto_names_trans : Transitive upto_names.
Proof.
  eapply eq_term_upto_univ_trans; exact _.
Qed.

(* todo: rename *)
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

(** ** Equality on contexts ** *)

Notation eq_context_upto Σ Re Rle := 
  (eq_context_gen (eq_term_upto_univ Σ Re Re) (eq_term_upto_univ Σ Re Rle)).

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
Proof.
  intros.
  eapply All2_fold_app; eauto.
  apply (length_of X0).
Qed.

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

Definition compare_term `{checker_flags} (le : bool) Σ φ (t u : term) :=
  if le then leq_term Σ φ t u else eq_term Σ φ t u.

Lemma lift_compare_term `{checker_flags} le Σ ϕ n k t t' :
  compare_term le Σ ϕ t t' -> compare_term le Σ ϕ (lift n k t) (lift n k t').
Proof.
  destruct le; intros. now apply lift_leq_term. now apply lift_eq_term.
Qed.

(* todo: unify *)
Definition eq_opt_term `{checker_flags} (le : bool) Σ φ (t u : option term) :=
  match t, u with
  | Some t, Some u => compare_term le Σ φ t u
  | None, None => True
  | _, _ => False
  end.

Definition eq_decl `{checker_flags} le Σ φ (d d' : context_decl) :=
  compare_decls (eq_term Σ φ) (if le then leq_term Σ φ else eq_term Σ φ) d d'.

Definition eq_context `{checker_flags} le Σ φ (Γ Δ : context) :=
  eq_context_gen (eq_term Σ φ) (if le then leq_term Σ φ else eq_term Σ φ) Γ Δ.

Lemma lift_compare_decls `{checker_flags} le Σ ϕ n k d d' :
  eq_decl le Σ ϕ d d' -> eq_decl le Σ ϕ (lift_decl n k d) (lift_decl n k d').
Proof.
  intros []; destruct le; constructor; cbn; intuition auto using lift_compare_term, lift_eq_term, lift_leq_term.
Qed.

Lemma lift_eq_context `{checker_flags} le Σ φ l l' n k :
  eq_context le Σ φ l l' ->
  eq_context le Σ φ (lift_context n k l) (lift_context n k l').
Proof.
  unfold eq_context.
  induction 1; rewrite -> ?lift_context_snoc0. constructor.
  constructor; auto. 
  eapply lift_compare_decls in p.
  now rewrite (All2_fold_length X).
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
  rewrite /R_global_instance /R_opt_variance.
  destruct global_variance as [vs|] eqn:var.  
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
