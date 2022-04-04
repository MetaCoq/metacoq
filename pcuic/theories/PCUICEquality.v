(* Distributed under the terms of the MIT license. *)
From Coq Require Import CMorphisms.
From MetaCoq.Template Require Import LibHypsNaming config utils Reflect.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICReflect.

Require Import ssreflect ssrbool.
From Equations.Prop Require Import DepElim.
From Equations Require Import Equations.
Set Equations With UIP.

(** TODO MOVE *)

Inductive lt_pb : conv_pb -> conv_pb -> Type :=
  | lt_refl pb : lt_pb pb pb
  | lt_conv_cum : lt_pb Conv Cumul.

Lemma conv_min pb : lt_pb Conv pb.
Proof.
  destruct pb ; now constructor.
Qed.

Lemma lt_conv pb : lt_pb pb Conv -> pb = Conv.
Proof.
  now inversion 1.
Qed.

Lemma gt_cumul pb : lt_pb Cumul pb -> pb = Cumul.
Proof.
  now inversion 1.
Qed.

#[global] Hint Resolve conv_min lt_conv gt_cumul : core.

#[global] Instance lt_pb_refl : CRelationClasses.Reflexive lt_pb.
Proof.
  intros p.
  now constructor.
Qed.

#[global] Instance lt_pb_trans : CRelationClasses.Transitive lt_pb.
Proof.
  intros p p' p''.
  now inversion 1.
Qed.

#[global] Instance lt_pb_preord : CRelationClasses.PreOrder lt_pb.
Proof.
  now constructor ; tc.
Qed.

#[global] Instance lt_pb_antisym : CRelationClasses.Antisymmetric eq lt_pb.
Proof.
  now inversion 1.
Qed.

#[global] Instance lt_pb_partialord : CRelationClasses.PartialOrder eq lt_pb.
Proof.
  intros p p' ; cbn.
  split ; intros H.
  - now subst.
  - destruct H as [H H'].
    inversion H ; subst.
    1: reflexivity.
    inversion H'.
Qed.

Ltac pcuic :=
  try repeat red; cbn in *;
   try (solve [ intuition auto; eauto with pcuic || (try lia || congruence) ]).

#[global]
Instance All2_fold_len {A} P (Γ Δ : list A) : HasLen (All2_fold P Γ Δ) #|Γ| #|Δ| :=
  All2_fold_length.

#[global] Instance All2_len {A} P (Γ Δ : list A) : HasLen (All2 P Γ Δ) #|Γ| #|Δ| := All2_length.

Implicit Types (cf : checker_flags).

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

Definition R_universe_instance R :=
  fun u u' => Forall2 R (List.map Universe.make u) (List.map Universe.make u').

#[global]
Instance R_universe_instance_refl R : RelationClasses.Reflexive R -> 
  RelationClasses.Reflexive (R_universe_instance R).
Proof. intros tRe x. eapply Forall2_map. 
  induction x; constructor; auto.
Qed.

#[global]
Instance R_universe_instance_sym R : RelationClasses.Symmetric R -> 
  RelationClasses.Symmetric (R_universe_instance R).
Proof. intros tRe x y. now eapply Forall2_symP. Qed.

#[global]
Instance R_universe_instance_trans R : RelationClasses.Transitive R -> 
  RelationClasses.Transitive (R_universe_instance R).
Proof. intros tRe x y z. now eapply Forall2_trans. Qed.

(** Cumulative inductive types:

  To simplify the development, we allow the variance list to not exactly 
  match the instances, so as to keep syntactic ws_cumul_pb an equivalence relation
  even on ill-formed terms. It corresponds to the right notion on well-formed terms.
*)

Definition R_universe_variance (R : conv_pb -> Universe.t -> Universe.t -> Prop) pb v u u' :=
  match v with
  | Variance.Irrelevant => True
  | Variance.Covariant => R pb (Universe.make u) (Universe.make u')
  | Variance.Invariant => R Conv (Universe.make u) (Universe.make u')
  end.

Fixpoint R_universe_instance_variance R pb v u u' :=
  match u, u' return Prop with
  | u :: us, u' :: us' =>
    match v with
    | [] => R_universe_instance_variance R pb v us us' 
      (* Missing variance stands for irrelevance, we still check that the instances have
        the same length. *)
    | v :: vs => R_universe_variance R pb v u u' /\
        R_universe_instance_variance R pb vs us us'
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
          which implies that no universe ws_cumul_pb needs to be checked here. *)
        Some []
      else None
    | _ => None
    end
  | _ => None
  end.

Definition R_opt_variance R pb v :=
  match v with 
  | Some v => R_universe_instance_variance R pb v
  | None => R_universe_instance (R Conv)
  end.

Definition R_global_instance Σ R pb gr napp :=
  R_opt_variance R pb (global_variance Σ gr napp).

Definition R_ind_universes {cf:checker_flags} (Σ : global_env_ext) pb ind n i i' :=
  R_global_instance Σ (fun pb' => compare_universe pb' (global_ext_constraints Σ)) pb
  (IndRef ind) n i i'.  

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
  (* Only the type are compared using cumulativity,
  the bodies are always compared for conversion.
   *)

  Context {compare_term : conv_pb -> term -> term -> Type} {pb : conv_pb}.
  Inductive compare_decls  : context_decl -> context_decl -> Type :=
  | compare_vass {na T na' T'} :
    eq_binder_annot na na' ->
    compare_term pb T T' ->
    compare_decls (vass na T) (vass na' T')
  | compare_vdef {na b T na' b' T'} :
    eq_binder_annot na na' ->
    compare_term Conv b b' ->
    compare_term pb T T' -> 
    compare_decls (vdef na b T) (vdef na' b' T').

  Derive Signature NoConfusion for compare_decls.
End compare_decls.
Arguments compare_decls : clear implicits.

Notation eq_context_pb compare_term pb :=
  (All2 (compare_decls compare_term pb)).

Notation eq_context_upto_names := (eq_context_pb (fun _ => eq) Cumul).

Lemma eq_context_upto_names_pb pb Γ Γ' :
  eq_context_upto_names Γ Γ' <~> eq_context_pb (fun _ => eq) pb Γ Γ'.
Proof.
  split; intros e; depind e; constructor; auto.
  all: match goal with | H : compare_decls _ _ _ _ |- _ => destruct H ; now constructor end.
Qed.

Lemma compare_decls_impl compare_term compare_term' pb pb' :
  subrelation (compare_term Conv) (compare_term' Conv) ->
  subrelation (compare_term pb) (compare_term' pb') ->
  subrelation (compare_decls compare_term pb)
    (compare_decls compare_term' pb').
Proof.
  intros he hle x y []; constructor; auto.
Qed.

#[global] Instance eq_context_pb_impl compare_term compare_term' pb pb' :
subrelation (compare_term Conv) (compare_term' Conv) ->
  subrelation (compare_term pb) (compare_term' pb') ->
  subrelation (eq_context_pb compare_term pb) (eq_context_pb compare_term' pb').
Proof.
  red.
  solve_all.
  intros; eapply compare_decls_impl ; eauto.
Qed.

Lemma compare_decl_map compare_term pb f g d d' :
  compare_decls (fun pb' x y => compare_term pb' (f x) (g y)) pb d d' ->
  compare_decls compare_term pb (map_decl f d) (map_decl g d').
Proof.
  intros h; depelim h; constructor; intuition auto.
Qed.

Definition bcompare_decls (compare_term : conv_pb -> term -> term -> bool)
  pb (d d' : context_decl) : bool :=
  match d, d' with
  | {| decl_name := na; decl_body := None; decl_type := T |},
    {| decl_name := na'; decl_body := None; decl_type := T' |} =>
    eqb_binder_annot na na' && compare_term pb T T'
  | {| decl_name := na; decl_body := Some b; decl_type := T |},
    {| decl_name := na'; decl_body := Some b'; decl_type := T' |} =>
    eqb_binder_annot na na' && compare_term Conv b b' && compare_term pb T T'
  | _, _ => false
  end.

#[global] Polymorphic Instance compare_decl_refl compare_term pb :
  CRelationClasses.Reflexive (compare_term Conv) ->
  CRelationClasses.Reflexive (compare_term pb) ->
  CRelationClasses.Reflexive (compare_decls compare_term pb).
Proof.
  intros he hle [? []] ; constructor; auto ; reflexivity.
Qed.

#[global]
Polymorphic Instance compare_decl_refl_conv compare_term :
  CRelationClasses.Reflexive (compare_term Conv) ->
  CRelationClasses.Reflexive (compare_decls compare_term Conv).
Proof.
  tc.
Qed.

#[global] Polymorphic Instance compare_decl_sym compare_term pb :
  CRelationClasses.Symmetric (compare_term Conv) ->
  CRelationClasses.Symmetric (compare_term pb) ->
  CRelationClasses.Symmetric (compare_decls compare_term pb).
Proof.
  intros he hle d d' []; constructor ; symmetry ; auto.
Qed.

#[global]
Polymorphic Instance compare_decl_sym_conv compare_term :
CRelationClasses.Symmetric (compare_term Conv) ->
CRelationClasses.Symmetric (compare_decls compare_term Conv). 
Proof.
  tc.
Qed.

#[global]
Polymorphic Instance compare_decl_trans compare_term pb :
  CRelationClasses.Transitive (compare_term Conv) ->
  CRelationClasses.Transitive (compare_term pb) ->
  CRelationClasses.Transitive (compare_decls compare_term pb).
Proof.
  intros he hle x y z h h'; depelim h; depelim h'; constructor; auto;
  etransitivity; eauto.
Qed.

#[global]
Polymorphic Instance compare_decl_trans_conv compare_term :
  CRelationClasses.Transitive (compare_term Conv) ->
  CRelationClasses.Transitive (compare_decls compare_term Conv).
Proof.
  tc.
Qed.

#[global]
Instance alpha_eq_reflexive : CRelationClasses.Reflexive eq_context_upto_names.
Proof.
  red. intros. eapply All2_refl. reflexivity.
Qed.

#[global]
Instance alpha_eq_symmmetric : CRelationClasses.Symmetric eq_context_upto_names.
Proof.
  red. eapply All2_symP. tc.
Qed.

#[global]
Instance alpha_eq_trans : CRelationClasses.Transitive eq_context_upto_names.
Proof.
  red. apply All2_trans. tc.
Qed.

#[global]
Polymorphic Instance eq_context_refl compare_term pb : 
  CRelationClasses.Reflexive (compare_term Conv) ->
  CRelationClasses.Reflexive (compare_term pb) ->
  CRelationClasses.Reflexive (eq_context_pb compare_term pb).    
Proof.
  intros he hle x.
  now eapply All2_refl.
Qed.

#[global]
Polymorphic Instance eq_context_refl_conv compare_term : 
  CRelationClasses.Reflexive (compare_term Conv) ->
  CRelationClasses.Reflexive (eq_context_pb compare_term Conv).
Proof.
  tc.
Qed.

#[global]
Polymorphic Instance eq_context_sym compare_term pb : 
  CRelationClasses.Symmetric (compare_term Conv) ->
  CRelationClasses.Symmetric (compare_term pb) ->
  CRelationClasses.Symmetric (eq_context_pb compare_term pb).
Proof.
  intros ? ? ? ?.
  eapply All2_symP ; tea.
  red. now symmetry.
Qed.

#[global]
Polymorphic Instance eq_context_sym_conv compare_term : 
  CRelationClasses.Symmetric (compare_term Conv) ->
  CRelationClasses.Symmetric (eq_context_pb compare_term Conv).
Proof.
  tc.
Qed.

#[global]
Polymorphic Instance eq_context_trans compare_term pb : 
  CRelationClasses.Transitive (compare_term Conv) ->
  CRelationClasses.Transitive (compare_term pb) ->  
  CRelationClasses.Transitive (eq_context_pb compare_term pb).
Proof.
  intros hr x y z.
  eapply All2_trans; intros.
  red.
  now etransitivity.
Qed.


#[global]
Polymorphic Instance eq_context_trans_conv compare_term : 
  CRelationClasses.Transitive (compare_term Conv) ->  
  CRelationClasses.Transitive (eq_context_pb compare_term Conv).
Proof.
  tc.
Qed.

Definition eq_predicate (eq_term : term -> term -> Type) Re p p' :=
  All2 eq_term p.(pparams) p'.(pparams) *
  (R_universe_instance Re p.(puinst) p'.(puinst) *
  ((eq_context_upto_names p.(pcontext) p'.(pcontext)) *
    eq_term p.(preturn) p'.(preturn))).

(** ** Syntactic ws_cumul_pb up-to universes
  We don't look at printing annotations *)

(** ws_cumul_pb is indexed by a natural number that counts the number of applications
  that surround the current term, used to implement cumulativity of inductive types
  correctly (only fully applied constructors and inductives benefit from it). *)  

Reserved Notation " Σ ⊢ t <==[ pb , napp ] u" (at level 50, t, u at next level,
  format "Σ  ⊢  t  <==[ pb , napp ]  u").


Inductive compare_term_upto_univ_napp Σ (R : conv_pb -> Universe.t -> Universe.t -> Prop)
  (pb : conv_pb) (napp : nat) : term -> term -> Type :=
| eq_Rel : forall n,
    Σ ⊢ tRel n <==[ pb , napp ] tRel n

| eq_Evar : forall e args args',
    All2 (compare_term_upto_univ_napp Σ R Conv 0) args args' ->
    Σ ⊢ tEvar e args <==[ pb , napp ] tEvar e args'

| eq_Var : forall id,
    Σ ⊢ tVar id <==[ pb , napp ] tVar id

| eq_Sort : forall s s',
    R pb s s' ->
    Σ ⊢ tSort s  <==[ pb , napp ] tSort s'

| eq_App : forall t t' u u',
    Σ ⊢ t <==[ pb , S napp ] t' ->
    Σ ⊢ u <==[ Conv , 0 ] u' ->
    Σ ⊢ tApp t u <==[ pb , napp ] tApp t' u'

| eq_Const : forall c u u',
    R_universe_instance (R Conv) u u' ->
    Σ ⊢ tConst c u <==[ pb , napp ] tConst c u'

| eq_Ind : forall i u u',
    R_global_instance Σ R pb (IndRef i) napp u u' ->
    Σ ⊢ tInd i u <==[ pb , napp ] tInd i u'

| eq_Construct : forall i k u u',
    R_global_instance Σ R pb (ConstructRef i k) napp u u' ->
    Σ ⊢ tConstruct i k u <==[ pb , napp ] tConstruct i k u'

| eq_Lambda : forall na na' ty ty' t t',
    eq_binder_annot na na' ->
    Σ ⊢ ty <==[ Conv , 0 ] ty' ->
    Σ ⊢ t <==[ pb , 0 ] t' ->
    Σ ⊢ tLambda na ty t <==[ pb , napp ] tLambda na' ty' t'

| eq_Prod : forall na na' a a' b b',
    eq_binder_annot na na' ->
    Σ ⊢ a <==[ Conv , 0 ] a' ->
    Σ ⊢ b <==[ pb , 0 ] b' ->
    Σ ⊢ tProd na a b <==[ pb , napp ] tProd na' a' b'

| eq_LetIn : forall na na' t t' ty ty' u u',
    eq_binder_annot na na' ->
    Σ ⊢ t <==[ Conv , 0 ] t' ->
    Σ ⊢ ty <==[ Conv , 0 ] ty' ->
    Σ ⊢ u <==[ pb , 0 ] u' ->
    Σ ⊢ tLetIn na t ty u <==[ pb , napp ] tLetIn na' t' ty' u'

| eq_Case : forall indn p p' c c' brs brs',
    eq_predicate (compare_term_upto_univ_napp Σ R Conv 0) (R Conv) p p' ->
    Σ ⊢ c <==[ Conv , 0 ] c' ->
    All2 (fun x y =>
      eq_context_upto_names (bcontext x) (bcontext y) *
      (Σ ⊢ x.(bbody) <==[ Conv , 0 ] y.(bbody))
    ) brs brs' ->
    Σ ⊢ tCase indn p c brs <==[ pb , napp ] tCase indn p' c' brs'

| eq_Proj : forall p c c',
    Σ ⊢ c <==[ Conv , 0 ] c' ->
    Σ ⊢ tProj p c <==[ pb , napp ] tProj p c'

| eq_Fix : forall mfix mfix' idx,
    All2 (fun x y =>
      (Σ ⊢ x.(dtype) <==[ Conv , 0 ] y.(dtype)) *
      (Σ ⊢ x.(dbody) <==[ Conv , 0 ] y.(dbody)) *
      (x.(rarg) = y.(rarg)) *
      eq_binder_annot x.(dname) y.(dname)
    )%type mfix mfix' ->
    Σ ⊢ tFix mfix idx <==[ pb , napp ] tFix mfix' idx

| eq_CoFix : forall mfix mfix' idx,
    All2 (fun x y =>
      (Σ ⊢ x.(dtype) <==[ Conv , 0 ] y.(dtype)) *
      (Σ ⊢ x.(dbody) <==[ Conv , 0 ] y.(dbody)) *
      (x.(rarg) = y.(rarg)) *
      eq_binder_annot x.(dname) y.(dname)
    ) mfix mfix' ->
    Σ ⊢ tCoFix mfix idx <==[ pb , napp ] tCoFix mfix' idx
    
(* | eq_Prim i : Σ ⊢ tPrim i <==[ pb , napp ] tPrim i *)
where " Σ ⊢ t <==[ pb , napp ] u " := (compare_term_upto_univ_napp Σ _ pb napp t u) : type_scope.

Notation compare_term_upto_univ Σ R pb := (compare_term_upto_univ_napp Σ R pb 0).

Derive Signature for compare_term_upto_univ_napp.

(* ** Syntactic conparison up-to universes *)

Definition compare_term_napp `{checker_flags} (pb : conv_pb) Σ φ napp (t u : term) :=
  compare_term_upto_univ_napp Σ (fun pb' => compare_universe pb' φ) pb napp t u.
  
Definition compare_term `{checker_flags} (pb : conv_pb) Σ φ (t u : term) :=
  compare_term_napp pb Σ φ 0 t u.

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
  compare_decls (fun pb' => compare_term pb' Σ φ) pb d d'.

Notation eq_decl := (compare_decl Conv).
Notation leq_decl := (compare_decl Cumul).

Definition compare_context `{checker_flags} pb Σ φ (Γ Δ : context) :=
  eq_context_pb (fun pb' => compare_term pb' Σ φ) pb Γ Δ.
  
Notation eq_context := (compare_context Conv).
Notation leq_context := (compare_context Cumul).

Notation eq_context_upto Σ R pb := 
  (eq_context_pb (fun pb' => compare_term_upto_univ Σ R pb') pb).

Section Impl.

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

  #[global]
  Instance R_global_instance_impl_same_napp Σ R R' pb gr napp :
    RelationClasses.subrelation (R Conv) (R' Conv) ->
    RelationClasses.subrelation (R pb) (R' pb) ->
    subrelation (R_global_instance Σ R pb gr napp) (R_global_instance Σ R' pb gr napp).
  Proof.
    intros he hle t t'.
    rewrite /R_global_instance /R_opt_variance.
    destruct global_variance as [v|] eqn:glob.
    induction t in v, t' |- *; destruct v, t'; simpl; auto.
    intros []; split; auto.
    - destruct t0; simpl; auto.
    - now eapply R_universe_instance_impl'.
  Qed.

  #[global]
  Instance R_global_instance_impl Σ R R' pb pb' gr napp napp' :
    RelationClasses.subrelation (R Conv) (R' Conv) ->
    RelationClasses.subrelation (R Conv) (R' pb') ->
    RelationClasses.subrelation (R pb) (R' pb') ->
    napp <= napp' ->
    subrelation (R_global_instance Σ R pb gr napp) (R_global_instance Σ R' pb' gr napp').
  Proof.
    intros he he' hle hnapp t t'.
    rewrite /R_global_instance /R_opt_variance.
    destruct global_variance as [v|] eqn:glob.
    - rewrite (global_variance_napp_mon hnapp glob).
      induction t in v, t' |- *; destruct v, t'; simpl; auto.
      intros []; split; auto.
      destruct t0; simpl; auto.
      all: eapply h ; tea ; eauto.
      all: reflexivity.
    - destruct (global_variance _ _ napp') as [v|] eqn:glob'; eauto using R_universe_instance_impl'.
      induction t in v, t' |- *; destruct v, t'; simpl; auto; intros H; inv H.
      eauto.
      split; auto.
      destruct t0; simpl; auto.
  Qed.

  #[global]
  Instance R_global_instance_impl_same Σ R R' pb pb' gr napp :
    RelationClasses.subrelation (R Conv) (R' Conv) ->
    RelationClasses.subrelation (R pb) (R' pb') ->
    subrelation (R_global_instance Σ R pb gr napp) (R_global_instance Σ R' pb' gr napp).
  Proof.
    intros he hle t t'.
    rewrite /R_global_instance /R_opt_variance.
    destruct global_variance as [v|] eqn:glob.
    - induction t in v, t' |- *; destruct v, t'; simpl; auto.
      intros []; split; auto.
      destruct t0; simpl; auto.
    - eauto using R_universe_instance_impl'.
  Qed.

  Lemma global_variance_empty gr napp env : env.(declarations) = [] -> global_variance env gr napp = None.
  Proof.
    destruct env; cbn => ->. destruct gr; auto.
  Qed.

  (** Pure syntactic equality, without cumulative inductive types subtyping *)

  #[global]
  Instance R_global_instance_empty_impl Σ R R' pb pb' gr napp napp' :
    RelationClasses.subrelation (R Conv) (R' Conv) ->
    RelationClasses.subrelation (R Conv) (R' pb') ->
    RelationClasses.subrelation (R pb) (R' pb') ->
    subrelation (R_global_instance empty_global_env R pb gr napp) (R_global_instance Σ R' pb' gr napp').
  Proof.
    intros he he' hle t t'.
    rewrite /R_global_instance /R_opt_variance. simpl.
    rewrite global_variance_empty //.
    destruct global_variance as [v|]; eauto using R_universe_instance_impl'.
    induction t in v, t' |- *; destruct v, t'; simpl; intros H; inv H; auto.
    simpl.
    split; auto.
    destruct t0; simpl; auto.
  Qed.

  #[global]
  Instance compare_term_upto_univ_impl Σ R R' pb pb' napp napp' :
    RelationClasses.subrelation (R Conv) (R' Conv) ->
    RelationClasses.subrelation (R Conv) (R' pb') ->
    RelationClasses.subrelation (R pb) (R' pb') ->
    napp <= napp' ->
    subrelation (compare_term_upto_univ_napp Σ R pb napp) (compare_term_upto_univ_napp Σ R' pb' napp').
  Proof.
    intros he he' hle hnapp t t'.
    induction t in pb, pb', he', hle, napp, napp', hnapp, t' |- * using term_forall_list_ind.
    all: inversion 1; subst; constructor.
    all: try solve [
            eauto using R_universe_instance_impl'].
    all: try solve [solve_all].
    - eapply IHt1 ; tea.
      auto with arith.
    - eapply R_global_instance_impl. all:eauto.
    - eapply R_global_instance_impl. all:eauto.
    - unfold eq_predicate in *; eauto; solve_all.
      eapply R_universe_instance_impl'; eauto.
  Qed.

  #[global]
  Instance compare_term_upto_univ_impl_same Σ R R' pb pb' napp :
    RelationClasses.subrelation (R Conv) (R' Conv) ->
    RelationClasses.subrelation (R pb) (R' pb') ->
    subrelation (compare_term_upto_univ_napp Σ R pb napp) (compare_term_upto_univ_napp Σ R' pb' napp).
  Proof.
    intros he hle t t'.
    induction t in pb, pb', hle, napp, t' |- * using term_forall_list_ind.
    all: inversion 1; subst; constructor.
    all: try solve [
            eauto using R_universe_instance_impl'].
    all: try solve [solve_all].
    - eapply R_global_instance_impl_same. all:eauto.
    - eapply R_global_instance_impl_same. all:eauto.
    - unfold eq_predicate in *; eauto; solve_all.
      eapply R_universe_instance_impl'; eauto.
  Qed.

  #[global]
  Instance compare_term_upto_univ_empty_impl Σ R R' pb pb' napp napp' :
    RelationClasses.subrelation (R Conv) (R' Conv) ->
    RelationClasses.subrelation (R Conv) (R' pb') ->
    RelationClasses.subrelation (R pb) (R' pb') ->
    subrelation (compare_term_upto_univ_napp empty_global_env R pb napp) (compare_term_upto_univ_napp Σ R' pb' napp').
  Proof.
    intros he he' hle t t'.
    induction t in pb, pb', he', hle, napp, napp', t' |- * using term_forall_list_ind.
    all: inversion 1; subst; constructor.
    all: try solve [
            eauto using R_universe_instance_impl'].
    all: try solve [solve_all].
    - eapply R_global_instance_empty_impl. all:eauto.
    - eapply R_global_instance_empty_impl. all:eauto.
    - unfold eq_predicate in *; eauto; solve_all.
      eapply R_universe_instance_impl'; eauto.
  Qed.

  #[global]
  Instance eq_term_upto_univ_leq Σ R pb napp napp' :
    RelationClasses.subrelation (R Conv) (R pb) ->
    napp <= napp' ->
    subrelation (compare_term_upto_univ_napp Σ R Conv napp) (compare_term_upto_univ_napp Σ R pb napp').
  Proof.
    intros.
    eapply compare_term_upto_univ_impl => //.
  Qed.

  #[global]
  Instance eq_term_leq_term {cf:checker_flags} Σ φ
    : subrelation (eq_term Σ φ) (leq_term Σ φ).
  Proof.
    eapply eq_term_upto_univ_leq ; auto; exact _.
  Qed.

  Lemma upto_eq_impl Σ R pb :
    RelationClasses.Reflexive (R Conv) ->
    RelationClasses.Reflexive (R pb) ->
    subrelation (compare_term_upto_univ Σ (fun _ => eq) pb) (compare_term_upto_univ Σ R pb).
  Proof.
    intros he hle. eapply compare_term_upto_univ_impl ; auto.
    all: move => ? ? -> //.
  Qed.

  Lemma compare_term_upto_univ_cst_ Σ R napp pb t t' :
    (compare_term_upto_univ_napp Σ (fun _ => R Conv) pb napp t t') <~>
    (compare_term_upto_univ_napp Σ R Conv napp t t').
  Proof.
    split ; intros.
    all: eapply compare_term_upto_univ_impl ; [..|eassumption] ; eauto.
    all: now red.
  Qed.

End Impl.

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

Lemma eq_binder_relevances_refl (x : list aname) : All2 (on_rel eq binder_relevance) x x.
Proof. now eapply All_All2_refl, All_refl. Qed.
#[global]
Hint Resolve eq_binder_relevances_refl : core.

Section Refl.

  #[global] Instance R_global_instance_refl Σ R pb gr napp :
    RelationClasses.Reflexive (R Conv) ->
    RelationClasses.Reflexive (R pb) ->
    RelationClasses.Reflexive (R_global_instance Σ R pb gr napp).
  Proof.
    intros he hle u.
    rewrite /R_global_instance.
    destruct global_variance as [v|] eqn:lookup.
    - induction u in v |- *; simpl; auto;
      unfold R_opt_variance in IHu; destruct v; simpl; auto.
      split; auto.
      destruct t; simpl; auto.
    - apply Forall2_same; eauto.
  Qed.

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
  Polymorphic Instance compare_term_upto_univ_refl Σ R pb napp :
    RelationClasses.Reflexive (R Conv) ->
    RelationClasses.Reflexive (R pb) ->
    Reflexive (compare_term_upto_univ_napp Σ R pb napp).
  Proof.
    intros he hle t.
    induction t in hle, napp, pb |- * using term_forall_list_ind.
    all: constructor.
    all: try solve [eauto].
    all: try solve [reflexivity].
    all: try solve [eapply All_All2 ; intuition].
    destruct X as [? [? ?]].
    unfold eq_predicate; solve_all.
    3: reflexivity.
    2: now eapply R_universe_instance_refl.
    eapply All_All2; eauto.
  Qed.

  #[global]
  Polymorphic Instance compare_term_upto_univ_refl_conv Σ R napp :
    RelationClasses.Reflexive (R Conv) ->
    Reflexive (compare_term_upto_univ_napp Σ R Conv napp).
  Proof.
    tc.
  Qed.

  #[global]
  Instance compare_term_refl {cf} pb {Σ : global_env} φ : Reflexive (compare_term pb Σ φ).
  Proof. eapply compare_term_upto_univ_refl ; tc. Qed.

End Refl.

Section Sym.

  #[global]
  Polymorphic Instance R_global_instance_sym Σ R pb gr napp : 
    RelationClasses.Symmetric (R Conv) ->
    RelationClasses.Symmetric (R pb) ->
    RelationClasses.Symmetric (R_global_instance Σ R pb gr napp).
  Proof.
    intros re rle u u'.
    rewrite /R_global_instance.
    destruct global_variance as [v|] eqn:lookup.
    - induction u in u', v |- *; destruct u'; simpl; auto;
      destruct v as [|v vs]; unfold R_opt_variance in IHu; simpl; auto.
      intros [Ra Ru']. split ; auto.
      destruct v; simpl; auto.
    - apply Forall2_symP; eauto.
  Qed.

  #[global]
  Polymorphic Instance compare_term_upto_univ_sym Σ pb R napp :
    RelationClasses.Symmetric (R Conv) ->
    RelationClasses.Symmetric (R pb) ->
    Symmetric (compare_term_upto_univ_napp Σ R pb napp).
  Proof.
    intros he hle u v e.
    pose proof (@RelationClasses.symmetry _ (@eq_binder_annot name name) _).
    induction u in v, pb, hle, napp, e |- * using term_forall_list_ind.
    all: dependent destruction e.
    all: econstructor.
    all: try solve [eauto].
    all: try solve [now symmetry].
    - eapply All2_All_mix_left in X as h; eauto.
      clear a X.
      induction h.
      + constructor.
      + destruct r as [h1 h2]. eapply h1 in h2 ; auto.
    - solve_all. destruct e as (r & ? & eq & ?).
      econstructor; rewrite ?e; unfold eq_predicate in *; solve_all; eauto.
      + eapply All2_sym; solve_all.
      + unfold R_universe_instance in r |- *.
        eapply Forall2_symP; eauto.
      + eapply All2_sym ; solve_all.
        now symmetry.
    - eapply All2_sym ; solve_all.
      eapply All2_sym ; solve_all.
      now symmetry.
    - eapply All2_sym.
      solve_all.
    - eapply All2_sym.
      solve_all.
  Qed.

  #[global]
  Instance compare_term_upto_univ_sym_conv Σ R napp :
    RelationClasses.Symmetric (R Conv) ->
    Symmetric (compare_term_upto_univ_napp Σ R Conv napp).
  Proof.
    tc.
  Qed.

  #[global]
  Instance eq_term_sym {cf} Σ φ : Symmetric (eq_term Σ φ).
  Proof.
    intros t u e.
    eapply compare_term_upto_univ_sym_conv; tea.
    tc.
  Qed.

End Sym.

Section Trans.

  #[global]
  Instance R_global_instance_trans Σ R pb gr napp :
    RelationClasses.Transitive (R Conv) ->
    RelationClasses.Transitive (R pb) ->
    RelationClasses.Transitive (R_global_instance Σ R pb gr napp).
  Proof.
    intros he hle x y z.
    unfold R_global_instance, R_opt_variance.
    destruct global_variance as [v|].
    - induction x in y, z, v |- *; destruct y, z, v; simpl; auto => //. 1: eauto.
      intros [Ra Rxy] [Rt Ryz].
      split; eauto.
      destruct t1; simpl in *; eauto.
    - eapply Forall2_trans; auto.
  Qed.

  #[global]
  Polymorphic Instance compare_term_upto_univ_trans Σ R pb napp :
    RelationClasses.Transitive (R Conv) ->
    RelationClasses.Transitive (R pb) -> 
    Transitive (compare_term_upto_univ_napp Σ R pb napp).
  Proof.
    intros he hle u v w e1 e2.
    pose proof (@RelationClasses.transitivity _ (@eq_binder_annot name name) _).
    induction u in hle, v, w, pb, napp, e1, e2 |- * using term_forall_list_ind.
    all: dependent destruction e1.
    all: try solve [ eauto ].
    all: dependent destruction e2 ; econstructor.
    all: try solve [ eauto ].
    - solve_all.
      induction a in a0, args'0 |- *.
      + assumption.
      + dependent destruction a0. intuition.
    - eapply R_universe_instance_trans ; eauto. 
    - eapply R_global_instance_trans; eauto.
    - eapply R_global_instance_trans; eauto.
    - unfold eq_predicate in *.
      !!solve_all.
      * clear -he hle hh0 hh1.
        revert hh0 hh1. generalize (pparams p), p'.(pparams), p'0.(pparams).
        intros l l' l''.
        induction 1 in l'' |- *; auto. intros H; depelim H. constructor; auto.
        eapply r; eauto. apply r.
      * eapply R_universe_instance_trans ; eauto.
      * etransitivity ; tea.
        solve_all.
    - !!solve_all.
      clear -H he hle a a0.
      induction a in a0, brs'0 |- *.
      + assumption.
      + depelim a0. destruct p. constructor; auto.
        split ; solve_all.
        etransitivity ; tea.
        solve_all.
    - solve_all.
      induction a in a0, mfix'0 |- *.
      + assumption.
      + dependent destruction a0. constructor ; eauto.
        intuition eauto.
        now etransitivity.
    - solve_all.
      induction a in a0, mfix'0 |- *.
      + assumption.
      + dependent destruction a0. constructor ; eauto.
        intuition eauto.
        now etransitivity.
  Qed.

  #[global]
  Polymorphic Instance compare_term_upto_univ_trans_conv Σ R napp :
    RelationClasses.Transitive (R Conv) ->
    Transitive (compare_term_upto_univ_napp Σ R Conv napp).
  Proof.
    tc.
  Qed.


  #[global]
  Instance leq_term_trans {cf} Σ φ : Transitive (leq_term Σ φ).
  Proof. apply compare_term_upto_univ_trans; tc. Qed.

  #[global]
  Instance eq_term_trans {cf} Σ φ : Transitive (eq_term Σ φ).
  Proof. apply compare_term_upto_univ_trans; tc. Qed.

End Trans.

#[global]
Polymorphic Instance compare_term_upto_univ_equiv Σ R (hR : RelationClasses.Equivalence (R Conv))
  : Equivalence (compare_term_upto_univ Σ R Conv).
Proof.
  constructor; tc.
Defined.

#[global]
Polymorphic Instance eq_context_equiv {cf} Σ φ :
  Equivalence (eq_context_pb (fun pb => compare_term pb Σ φ) Conv).
Proof.
  constructor; tc. 
Qed.

#[global]
Polymorphic Instance compare_term_preord {cf} pb Σ φ :
  PreOrder (compare_term pb Σ φ).
Proof.
  constructor;tc.
  red.
  eapply compare_term_upto_univ_trans; tc.
Qed.  

#[global]
Polymorphic Instance leq_context_preord {cf} Σ φ pb :
  PreOrder (eq_context_pb (fun pb => compare_term pb Σ φ) pb).
Proof.
  constructor; tc.
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
  split; tc.
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
Instance R_global_instance_equiv Σ R (hR : RelationClasses.Equivalence (R Conv)) gr napp
  : RelationClasses.Equivalence (R_global_instance Σ R Conv gr napp).
Proof.
  split; tc.
Qed.

#[global]
Instance R_global_instance_antisym Σ R pb (hRe : RelationClasses.Equivalence (R Conv)) gr napp :
  RelationClasses.Antisymmetric _ (R Conv) (R pb) ->
  RelationClasses.Antisymmetric _ (R_global_instance Σ R Conv gr napp) (R_global_instance Σ R pb gr napp).
Proof.
  intros hR u v.
  unfold R_global_instance, R_opt_variance.
  destruct global_variance; auto.
  induction u in l, v |- *; destruct v, l; simpl; auto.
  intros [at' uv] [ta vu]. split; auto.
  destruct t0; simpl in *; auto.
Qed.  

Lemma eq_term_upto_univ_antisym Σ R pb (hRe : RelationClasses.Equivalence (R Conv)) :
  RelationClasses.Antisymmetric _ (R Conv) (R pb) ->
  Antisymmetric (compare_term_upto_univ Σ R Conv) (compare_term_upto_univ Σ R pb).
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

Section Lift.

  Local Ltac lih :=
    lazymatch goal with
    | ih : forall pb v n k, compare_term_upto_univ_napp _ _ _ ?u _ -> _
      |- compare_term_upto_univ _ _ (lift _ _ ?u) _ =>
      eapply ih
    end.

  Lemma compare_term_upto_univ_lift Σ R pb n n' k :
    Proper (compare_term_upto_univ_napp Σ R pb n' ==> compare_term_upto_univ_napp Σ R pb n') (lift n k).
  Proof.
    intros u v e.
    induction u in n', v, n, k, e, pb |- * using term_forall_list_ind.
    all: dependent destruction e.
    all: try solve [cbn ; constructor ; try lih ; try assumption; solve_all].
    - cbn. destruct e as (? & ? & e & ?).
      constructor; unfold eq_predicate in *; simpl; !!solve_all.
      * now rewrite -?(All2_length e).
      * now rewrite (All2_length a).
    - cbn. constructor.
      pose proof (All2_length a).
      solve_all. rewrite H. eauto.
    - cbn. constructor.
      pose proof (All2_length a).
      solve_all. rewrite H. eauto.
  Qed.

  Lemma lift_compare_decls `{checker_flags} pb Σ ϕ n k d d' :
    compare_decl pb Σ ϕ d d' -> compare_decl pb Σ ϕ (lift_decl n k d) (lift_decl n k d').
  Proof.
    intros []; constructor; cbn ; auto.
    all: now apply compare_term_upto_univ_lift.
  Qed.

  Lemma lift_compare_context `{checker_flags} pb Σ φ l l' n k :
    compare_context pb Σ φ l l' ->
    compare_context pb Σ φ (lift_context n k l) (lift_context n k l').
  Proof.
    unfold compare_context.
    induction 1; rewrite -> ?lift_context_snoc0. constructor.
    constructor; auto. 
    eapply lift_compare_decls in r.
    now rewrite (All2_length X).
  Qed.

  Lemma lift_eq_term {cf:checker_flags} Σ φ n k T U :
    eq_term Σ φ T U -> eq_term Σ φ (lift n k T) (lift n k U).
  Proof.
    apply compare_term_upto_univ_lift.
  Qed.

  Lemma lift_leq_term {cf:checker_flags} Σ φ n k T U :
    leq_term Σ φ T U -> leq_term Σ φ (lift n k T) (lift n k U).
  Proof.
    apply compare_term_upto_univ_lift.
  Qed.

End Lift.

Section Subst.

  Local Ltac sih :=
    lazymatch goal with
    | ih : forall Rle v n x y, _ -> compare_term_upto_univ _ _ ?u _ -> _ -> _
      |- compare_term_upto_univ _ _ (subst _ _ ?u) _ => eapply ih
    end.

  Lemma compare_term_upto_univ_substs Σ R pb napp :
    RelationClasses.subrelation (R Conv) (R pb) ->
    forall u v n l l',
      compare_term_upto_univ_napp Σ R pb napp u v ->
      All2 (compare_term_upto_univ Σ R Conv) l l' ->
      compare_term_upto_univ_napp Σ R pb napp (subst l n u) (subst l' n v).
  Proof.
    unfold RelationClasses.subrelation; intros hR u v n l l' hu hl.
    induction u in napp, v, n, l, l', hu, hl, pb, hR |- * using term_forall_list_ind.
    all: dependent destruction hu.
    all: try solve [ cbn ; constructor ; try sih ; eauto ].
    - cbn. destruct (Nat.leb_spec0 n n0).
      2: now constructor.
      case_eq (nth_error l (n0 - n)).
      * intros t e. eapply All2_nth_error_Some in e as h ; eauto.
        destruct h as [t' [e' h]].
        rewrite e'.
        eapply compare_term_upto_univ_lift.
        eapply compare_term_upto_univ_impl ; [..|eassumption].
        all: auto with arith.
        reflexivity.
      * intros h. eapply All2_nth_error_None in h as hh ; eauto.
        rewrite hh.
        apply All2_length in hl as e. rewrite <- e.
        constructor.
    - cbn. constructor. solve_all.
    - cbn.
      destruct e as (? & ? & e & ?).
      constructor ; unfold eq_predicate; simpl; try sih ; solve_all.
      * now rewrite -(All2_length e).
      * now rewrite (All2_length a).
    - cbn. constructor ; try sih ; eauto.
      pose proof (All2_length a).
      solve_all. now rewrite H.
    - cbn. constructor ; try sih ; eauto.
      pose proof (All2_length a).
      solve_all. now rewrite H.
  Qed.

  Lemma compare_term_upto_univ_subst Σ R pb :
    RelationClasses.subrelation (R Conv) (R pb) ->
    forall u v n x y,
      compare_term_upto_univ Σ R pb u v ->
      compare_term_upto_univ Σ R Conv x y ->
      compare_term_upto_univ Σ R pb (u{n := x}) (v{n := y}).
  Proof.
    intros hR u v n x y e1 e2.
    eapply compare_term_upto_univ_substs; eauto.
  Qed.

  Lemma subst_compare_term {cf:checker_flags} pb Σ φ l k T U :
    compare_term pb Σ φ T U ->
    compare_term pb Σ φ (subst l k T) (subst l k U).
  Proof.
    intros Hleq.
    eapply compare_term_upto_univ_substs; try easy.
    1: cbn ; tc.
    now eapply All2_same.
  Qed.

End Subst.

(** ** Behavior on mkApps and it_mkLambda_or_LetIn **  *)

Section Mk.

  Lemma compare_term_compare_term_napp Σ R pb napp t t' :
    RelationClasses.subrelation (R Conv) (R pb) ->
    compare_term_upto_univ Σ R pb t t' -> 
    compare_term_upto_univ_napp Σ R pb napp t t'.
  Proof.
    intros. eapply compare_term_upto_univ_impl ; [..|eassumption].
    all: auto with arith.
    all: reflexivity.
  Qed.

  Lemma compare_term_upto_univ_napp_mkApps Σ R pb u1 l1 u2 l2 napp :
      compare_term_upto_univ_napp Σ R pb (#|l1| + napp) u1 u2 ->
      All2 (compare_term_upto_univ Σ R Conv) l1 l2 ->
      compare_term_upto_univ_napp Σ R pb napp (mkApps u1 l1) (mkApps u2 l2).
  Proof.
    intros hu hl. induction l1 in napp, u1, u2, l2, hu, hl |- *.
    - inversion hl. subst. assumption.
    - inversion hl. subst. simpl.
      eapply IHl1.
      + constructor. all: assumption.
      + assumption.
  Qed.

  Lemma compare_term_upto_univ_napp_mkApps_l_inv Σ R pb napp u l t :
      compare_term_upto_univ_napp Σ R pb napp (mkApps u l) t ->
      ∑ u' l',
        compare_term_upto_univ_napp Σ R pb (#|l| + napp) u u' *
        All2 (compare_term_upto_univ Σ R Conv) l l' *
        (t = mkApps u' l').
  Proof.
    intros h. induction l in napp, u, t, h, pb |- *.
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

  Lemma compare_term_upto_univ_napp_mkApps_r_inv Σ R pb napp u l t :
      compare_term_upto_univ_napp Σ R pb napp t (mkApps u l) ->
      ∑ u' l',
        compare_term_upto_univ_napp Σ R pb (#|l| + napp) u' u *
        All2 (compare_term_upto_univ Σ R Conv) l' l *
        (t = mkApps u' l').
  Proof.
    intros h. induction l in napp, u, t, h, R, pb |- *.
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

  Lemma compare_term_upto_univ_mkApps Σ R pb u1 l1 u2 l2 :
      compare_term_upto_univ_napp Σ R pb #|l1| u1 u2 ->
      All2 (compare_term_upto_univ Σ R Conv) l1 l2 ->
      compare_term_upto_univ Σ R pb (mkApps u1 l1) (mkApps u2 l2).
  Proof.
    intros; apply compare_term_upto_univ_napp_mkApps; rewrite ?Nat.add_0_r; auto.
  Qed.

  Lemma compare_term_upto_univ_mkApps_l_inv Σ R pb u l t :
      compare_term_upto_univ Σ R pb (mkApps u l) t ->
      ∑ u' l',
        compare_term_upto_univ_napp Σ R pb #|l| u u' *
        All2 (compare_term_upto_univ Σ R Conv) l l' *
        (t = mkApps u' l').
  Proof.
    intros H; apply compare_term_upto_univ_napp_mkApps_l_inv in H; rewrite ?Nat.add_0_r in H; auto.
  Qed.

  Lemma compare_term_upto_univ_mkApps_r_inv Σ R pb u l t :
      compare_term_upto_univ Σ R pb t (mkApps u l) ->
      ∑ u' l',
        compare_term_upto_univ_napp Σ R pb #|l| u' u *
        All2 (compare_term_upto_univ Σ R Conv) l' l *
        (t = mkApps u' l').
  Proof.
    intros H; apply compare_term_upto_univ_napp_mkApps_r_inv in H;
      rewrite Nat.add_0_r in H; auto.
  Qed.

  Lemma compare_term_upto_univ_isApp Σ R pb napp u v :
    compare_term_upto_univ_napp Σ R pb napp u v ->
    isApp u = isApp v.
  Proof.
    induction 1.
    all: reflexivity.
  Qed.

  Lemma compare_term_upto_univ_mkApps_inv Σ R pb u l u' l' :
    isApp u = false ->
    isApp u' = false ->
    compare_term_upto_univ Σ R pb (mkApps u l) (mkApps u' l') ->
    compare_term_upto_univ_napp Σ R pb #|l| u u' * All2 (compare_term_upto_univ Σ R Conv) l l'.
  Proof.
    intros hu hu' h.
    apply compare_term_upto_univ_mkApps_l_inv in h as hh.
    destruct hh as [v [args [[h1 h2] h3]]].
    apply compare_term_upto_univ_isApp in h1 as hh1. rewrite hu in hh1.
    apply mkApps_notApp_inj in h3 ; auto.
    destruct h3 as [? ?]. subst. split ; auto.
  Qed.

  Lemma compare_term_upto_univ_it_mkLambda_or_LetIn Σ R pb :
    RelationClasses.Reflexive (R Conv) ->
    Proper (eq_context_upto Σ R Conv ==> compare_term_upto_univ Σ R pb ==> compare_term_upto_univ Σ R pb) it_mkLambda_or_LetIn.
  Proof.
    intros he Γ Δ eq u v h.
    induction eq in u, v, h, he |- *.
    - assumption.
    - simpl. cbn. apply IHeq => //.
      destruct r; cbn; constructor ; tas; try reflexivity.
  Qed.

  Lemma compare_term_upto_univ_it_mkLambda_or_LetIn_r Σ R pb Γ :
    RelationClasses.Reflexive (R Conv) ->
    respectful (compare_term_upto_univ Σ R pb) (compare_term_upto_univ Σ R pb)
              (it_mkLambda_or_LetIn Γ) (it_mkLambda_or_LetIn Γ).
  Proof.
    intros he u v h.
    induction Γ as [| [na [b|] A] Γ ih ] in u, v, h |- *.
    - assumption.
    - simpl. cbn. apply ih. constructor ; try reflexivity.
      all: auto.
    - simpl. cbn. apply ih. constructor ; try reflexivity.
      all: auto.
  Qed.

  Lemma compare_term_it_mkLambda_or_LetIn {cf:checker_flags} Σ pb φ Γ :
    respectful (compare_term pb Σ φ) (compare_term pb Σ φ)
              (it_mkLambda_or_LetIn Γ) (it_mkLambda_or_LetIn Γ).
  Proof.
    apply compare_term_upto_univ_it_mkLambda_or_LetIn_r; exact _.
  Qed.

  Lemma compare_term_upto_univ_it_mkProd_or_LetIn Σ R pb Γ :
    RelationClasses.Reflexive (R Conv) ->
    respectful (compare_term_upto_univ Σ R pb) (compare_term_upto_univ Σ R pb)
              (it_mkProd_or_LetIn Γ) (it_mkProd_or_LetIn Γ).
  Proof.
    intros he u v h.
    induction Γ as [| [na [b|] A] Γ ih ] in u, v, h |- *.
    - assumption.
    - simpl. cbn. apply ih. constructor ; try reflexivity.
      all: auto.
    - simpl. cbn. apply ih. constructor ; try reflexivity.
      all: auto.
  Qed.

  Lemma compare_term_it_mkProd_or_LetIn {cf:checker_flags} Σ pb φ Γ:
    respectful (compare_term pb Σ φ) (compare_term pb Σ φ)
              (it_mkProd_or_LetIn Γ) (it_mkProd_or_LetIn Γ).
  Proof.
    eapply compare_term_upto_univ_it_mkProd_or_LetIn ; exact _.
  Qed.

  Lemma compare_term_it_mkLambda_or_LetIn_inv {cf:checker_flags} Σ pb φ Γ u v :
      compare_term Σ pb φ (it_mkLambda_or_LetIn Γ u) (it_mkLambda_or_LetIn Γ v) ->
      compare_term Σ pb φ u v.
  Proof.
    revert u v. induction Γ as [| [na [b|] A] Γ ih ] ; intros u v h.
    - assumption.
    - simpl in h. cbn in h. apply ih in h. inversion h. subst.
      assumption.
    - simpl in h. cbn in h. apply ih in h. inversion h. subst.
      assumption.
  Qed.

End Mk.

(** ** Syntactic ws_cumul_pb up to printing anotations ** *)


Definition upto_names := compare_term_upto_univ empty_global_env (fun _ => eq) Conv.

Notation "`≡α`" := upto_names.
Infix "≡α" := upto_names (at level 60).
Notation "`≡Γ`" := (eq_context_upto empty_global_env (fun _ => eq) Conv).
Infix "≡Γ" := (eq_context_upto empty_global_env (fun _ => eq) Conv) (at level 20, no associativity).

Section UptoNames.

  Lemma R_universe_instance_eq {u u'} : R_universe_instance eq u u' -> u = u'.
  Proof.
    intros H.
    apply Forall2_eq in H. apply map_inj in H ; revgoals.
    { apply Universe.make_inj. }
    subst. constructor ; auto.
  Qed.

  Lemma valid_constraints_empty {cf} i : valid_constraints (empty_ext empty_global_env) (subst_instance_cstrs i (empty_ext empty_global_env)).
  Proof.
    red. destruct check_univs => //.
  Qed.

  #[global]
  Instance upto_names_terms_refl : CRelationClasses.Reflexive (All2 `≡α`).
  Proof. intro; apply All2_refl; reflexivity. Qed.

  Lemma eq_context_upto_empty_impl {cf} {Σ : global_env_ext} pb ctx ctx' :
    ctx ≡Γ ctx' ->
    eq_context_upto Σ (fun _ => eq_universe Σ) pb ctx ctx'.
  Proof.
    intros. solve_all.
    destruct X ; constructor ; auto.
    all: eapply compare_term_upto_univ_empty_impl; eauto. 
    all: move => ? ? -> ; reflexivity.
  Qed.

  (* Infix "≡'" := (eq_term_upto_univ [] eq eq) (at level 70).
  Notation upto_names' := (eq_term_upto_univ [] eq eq). *)

  #[global]
  Instance upto_names_ref : Reflexive upto_names.
  Proof.
    tc.
  Qed.

  #[global]
  Instance upto_names_sym : Symmetric upto_names.
  Proof.
    tc.
  Qed.

  #[global]
  Instance upto_names_trans : Transitive upto_names.
  Proof.
    tc.
  Qed.

  Lemma upto_names_impl Σ R pb :
    RelationClasses.Reflexive (R Conv) ->
    RelationClasses.Reflexive (R pb) ->
    subrelation upto_names (compare_term_upto_univ Σ R pb).
  Proof.
    intros h h'.
    eapply compare_term_upto_univ_empty_impl; auto.
    all: red in h, h' |- * => ? ? -> //.
  Qed.

  Lemma upto_names_impl_eq_term {cf:checker_flags} Σ φ u v :
      u ≡α v -> eq_term Σ φ u v.
  Proof.
    eapply upto_names_impl ; exact _.
  Qed.

  Lemma upto_names_impl_leq_term {cf:checker_flags} Σ φ u v :
      u ≡α v -> leq_term Σ φ u v.
  Proof.
    eapply upto_names_impl ; exact _.
  Qed.

End UptoNames.

  (** ** ws_cumul_pb on contexts ** *)

  (* TODO move *)
  Inductive rel_option {A B} (R : A -> B -> Type) : option A -> option B -> Type :=
  | rel_some : forall a b, R a b -> rel_option R (Some a) (Some b)
  | rel_none : rel_option R None None.

  Derive Signature NoConfusion for rel_option.

  Definition compare_decl_upto Σ R pb d d' : Type :=
    eq_binder_annot d.(decl_name) d'.(decl_name) *
    rel_option (compare_term_upto_univ Σ R Conv) d.(decl_body) d'.(decl_body) *
    compare_term_upto_univ Σ R pb d.(decl_type) d'.(decl_type).

  (* TODO perhaps should be def *)
  (* Lemma All2_eq_context_upto Σ Re Rle :
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
  Qed. *)

  Lemma eq_context_upto_refl Σ R pb :
    RelationClasses.Reflexive (R Conv) ->
    RelationClasses.Reflexive (R pb) ->
    Reflexive (eq_context_upto Σ R pb).
  Proof.
    tc.
  Qed.

  Lemma eq_context_upto_sym Σ R pb :
    RelationClasses.Symmetric (R Conv) ->
    RelationClasses.Symmetric (R pb) ->
    Symmetric (eq_context_upto Σ R pb).
  Proof. tc. Qed.

  Lemma eq_context_upto_cat Σ R pb Γ Δ Γ' Δ' :
    eq_context_upto Σ R pb Γ Γ' ->
    eq_context_upto Σ R pb Δ Δ' ->
    eq_context_upto Σ R pb (Γ ,,, Δ) (Γ' ,,, Δ').
  Proof. intros. eapply All2_app; eauto. Qed.

  Lemma eq_context_upto_rev Σ R pb Γ Δ :
    eq_context_upto Σ R pb Γ Δ ->
    eq_context_upto Σ R pb (rev Γ) (rev Δ).
  Proof.
    induction 1.
    - constructor.
    - rewrite 2!rev_cons. eapply eq_context_upto_cat ; eauto.
  Qed.

  Lemma eq_context_upto_rev'  Σ Γ Δ R pb :
      eq_context_upto Σ R pb Γ Δ ->
      eq_context_upto Σ R pb (List.rev Γ) (List.rev Δ).
  Proof.
    induction 1.
    - constructor.
    - simpl. eapply eq_context_upto_cat.
      + repeat constructor; assumption.
      + assumption.
  Qed.

  Lemma eq_context_upto_length {Σ Re Rle Γ Δ} :
      eq_context_upto Σ Re Rle Γ Δ ->
      #|Γ| = #|Δ|.
  Proof.
    eapply All2_length.
  Qed.

  Lemma eq_context_upto_subst_context Σ R pb u v n l l' :
    RelationClasses.subrelation (R Conv) (R pb) ->
      eq_context_upto Σ R pb u v ->
      All2 (compare_term_upto_univ Σ R Conv) l l' ->
      eq_context_upto Σ R pb (subst_context l n u) (subst_context l' n v).
  Proof.
    intros re.
    induction 1; intros Hl.
    - rewrite !subst_context_nil. constructor.
    - rewrite !subst_context_snoc; constructor; eauto.
      depelim r; constructor; simpl; intuition auto.
      all: rewrite -(All2_length X) ;
      apply compare_term_upto_univ_substs; auto.
      reflexivity.
  Qed.

  #[global]
  Hint Resolve All2_fold_nil : pcuic.

  Lemma eq_context_upto_smash_context ctx ctx' x y :
    ctx ≡Γ ctx' -> x ≡Γ y -> 
    smash_context ctx x ≡Γ smash_context ctx' y.
  Proof.
    induction x in ctx, ctx', y |- *; intros eqctx eqt; inv eqt; simpl; 
      try split; auto; try constructor; auto. depelim X => /=.
    - apply IHx; auto. apply eq_context_upto_cat; auto.
      constructor; pcuic.
    - apply IHx; auto. eapply eq_context_upto_subst_context; eauto.
      typeclasses eauto.
  Qed.

  Lemma eq_context_upto_nth_error Σ R pb ctx ctx' n :
    eq_context_upto Σ R pb ctx ctx' -> 
    rel_option (compare_decl_upto Σ R pb) (nth_error ctx n) (nth_error ctx' n).
  Proof.
    induction 1 in n |- *.
    - rewrite nth_error_nil. constructor.
    - destruct n; simpl; auto. 
      constructor. depelim r; constructor; intuition auto;
      now constructor.
  Qed.

  Lemma eq_context_impl Σ R R' pb:
      RelationClasses.subrelation (R Conv) (R' Conv) ->
      RelationClasses.subrelation (R Conv) (R' pb) ->
      RelationClasses.subrelation (R pb) (R' pb) ->
      subrelation (eq_context_upto Σ R pb) (eq_context_upto Σ R' pb).
  Proof.
    intros hR hR' hR'' Γ Δ h.
    induction h.
    - constructor.
    - constructor; auto. 
      depelim r; constructor; auto.
      all:eapply compare_term_upto_univ_impl ; eauto with arith.
  Qed.

Lemma isLambda_compare_term_l Σ R pb u v :
    isLambda u ->
    compare_term_upto_univ Σ R pb u v ->
    isLambda v.
Proof.
  intros h e.
  destruct u; try discriminate.
  depelim e. auto.
Qed.

Lemma isLambda_compare_term_r Σ R pb u v :
    isLambda v ->
    compare_term_upto_univ Σ R pb u v ->
    isLambda u.
Proof.
  intros h e.
  destruct v ; try discriminate.
  depelim e. auto.
Qed.

Lemma isConstruct_app_compare_term_l Σ R pb u v :
    isConstruct_app u ->
    compare_term_upto_univ Σ R pb u v ->
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
  apply compare_term_upto_univ_mkApps_inv in e as hh.
  - destruct hh as [h1 h2].
    dependent destruction h1. reflexivity.
  - reflexivity.
  - eapply decompose_app_notApp. eassumption.
Qed.

Lemma isConstruct_app_compare_term_r Σ R pb u v :
  isConstruct_app v ->
  compare_term_upto_univ Σ R pb u v ->
  isConstruct_app u.
Proof.
  intros h e.
  case_eq (decompose_app u). intros t1 l1 e1.
  case_eq (decompose_app v). intros t2 l2 e2.
  unfold isConstruct_app in *.
  rewrite e2 in h. cbn in h.
  rewrite e1. cbn.
  destruct t2 ; try discriminate.
  apply decompose_app_inv in e1 as ?. subst.
  apply decompose_app_inv in e2 as ?. subst.
  apply compare_term_upto_univ_mkApps_inv in e as hh.
  - destruct hh as [h1 h2].
    dependent destruction h1. reflexivity.
  - eapply decompose_app_notApp. eassumption.
  - reflexivity.
Qed.

Lemma R_global_instance_flip Σ gr napp (R R' : conv_pb -> Universe.t -> Universe.t -> Prop) pb pb' u v:
  RelationClasses.Reflexive (R Conv) ->
  RelationClasses.Reflexive (R pb) ->
  RelationClasses.Symmetric (R' Conv) ->
  RelationClasses.Transitive (R Conv) ->
  RelationClasses.Transitive (R pb) ->
  RelationClasses.subrelation (R Conv) (R' Conv) ->
  RelationClasses.subrelation (R Conv) (R pb') ->
  (forall x y, (R pb x y) -> (R' pb' y x)) ->
  R_global_instance Σ R pb gr napp u v ->
  R_global_instance Σ R' pb' gr napp v u.
Proof.
  intros Rerefl Rlerefl Resym Retrans Rletrans inclc inclp incl'.
  rewrite /R_global_instance /R_opt_variance.
  destruct global_variance as [vs|] eqn:var.  
  - induction u in vs, v |- *; destruct v; simpl; auto;
    destruct vs as [|v' vs]; simpl; auto.
    intros [Ra Ru']. split.
    destruct v'; simpl; auto.
    apply IHu; auto.
  - intros.
    apply Forall2_symP; eauto.
    eapply Forall2_impl ; eauto.
Qed.

Lemma compare_term_upto_univ_napp_flip Σ (R R' : conv_pb -> Universe.t -> Universe.t -> Prop) pb pb' napp u v :
  RelationClasses.Reflexive (R Conv) ->
  RelationClasses.Reflexive (R pb) ->
  RelationClasses.Symmetric (R' Conv) ->
  RelationClasses.Transitive (R Conv) ->
  RelationClasses.Transitive (R pb) ->
  RelationClasses.subrelation (R Conv) (R' Conv) ->
  RelationClasses.subrelation (R Conv) (R pb') ->
  (forall x y, (R pb x y) -> (R' pb' y x)) ->
  compare_term_upto_univ_napp Σ R pb napp u v ->
  compare_term_upto_univ_napp Σ R' pb' napp v u.
Proof.
  intros Rerefl Rlerefl Resym Retrans Rletrans incl incl' H e.
  induction e in Rlerefl, Rletrans, incl', H |- *.
  all: intros; constructor.
  all: intuition auto.
  all:try solve [symmetry ; eapply compare_term_upto_univ_impl ; [..|eassumption] ; auto ].
  all:try solve [symmetry ; eapply R_universe_instance_impl ; [..|eassumption] ; auto].
  all: try solve [now symmetry].
  all:eauto using R_global_instance_flip.
  - eapply All2_sym. solve_all.
    symmetry.
    eapply compare_term_upto_univ_impl ; [..|eassumption] ; auto with arith.
  - unfold eq_predicate in * ; intuition auto.
    all: symmetry ; auto.
    + solve_all.
      now eapply compare_term_upto_univ_impl ; [..|eassumption].
    + now eapply R_universe_instance_impl ; [..|eassumption].
    + now eapply compare_term_upto_univ_impl ; [..|eassumption].
  - eapply All2_sym. solve_all.
    + now symmetry.
    + symmetry. now eapply compare_term_upto_univ_impl ; [..|eassumption].
  - eapply All2_sym. solve_all.
    all: symmetry ; auto.
    all: now eapply compare_term_upto_univ_impl ; [..|eassumption].
  - eapply All2_sym. solve_all.
      all: symmetry ; auto.
      all: now eapply compare_term_upto_univ_impl ; [..|eassumption].
Qed.

Lemma eq_univ_make u u' : 
    Forall2 eq (map Universe.make u) (map Universe.make u') ->
    u = u'.
Proof.
  intros H.
  eapply Forall2_map' in H.
  eapply Forall2_eq. eapply Forall2_impl; tea.
  clear. intros [] [] H; now inversion H.
Qed.

(** ws_cumul_pb of binder annotations *)
Notation eq_annots Γ Δ :=
  (Forall2 (fun na decl => eq_binder_annot na (decl_name decl)) Γ Δ).

Lemma eq_context_gen_binder_annot (pb : conv_pb) Γ Δ : 
  eq_context_pb (fun _ => eq) pb Γ Δ -> eq_annots (forget_types Γ) Δ.
Proof.
  induction 1; constructor; auto.
  destruct r; auto.
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