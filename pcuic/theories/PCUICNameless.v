(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia
     Classes.RelationClasses.
From Template
Require Import config monad_utils utils AstUtils UnivSubst.
From PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICTyping
     PCUICCumulativity.
From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.

Definition anon (na : name) : bool :=
  match na with
  | nAnon => true
  | nNamed s => false
  end.

Fixpoint nameless (t : term) : bool :=
  match t with
  | tRel n => true
  | tVar n => true
  | tEvar n l => forallb nameless l
  | tSort s => true
  | tProd na A B => anon na && nameless A && nameless B
  | tLambda na A b => anon na && nameless A && nameless b
  | tLetIn na b B t => anon na && nameless b && nameless B && nameless t
  | tApp u v => nameless u && nameless v
  | tConst c u => true
  | tInd i u => true
  | tConstruct i n u => true
  | tCase indn p c brs =>
    nameless p && nameless c && forallb (test_snd nameless) brs
  | tProj p c => nameless c
  | tFix mfix idx =>
    forallb (fun d => anon d.(dname)) mfix &&
    forallb (test_def nameless nameless) mfix
  | tCoFix mfix idx =>
    forallb (fun d => anon d.(dname)) mfix &&
    forallb (test_def nameless nameless) mfix
  end.

Definition map_def_anon {A B : Set} (tyf bodyf : A -> B) (d : def A) :=
  {| dname := nAnon ;
     dtype := tyf d.(dtype) ;
     dbody := bodyf d.(dbody) ;
     rarg := d.(rarg) |}.

Fixpoint nl (t : term) : term :=
  match t with
  | tRel n => tRel n
  | tVar n => tVar n
  | tEvar n l => tEvar n (map nl l)
  | tSort s => tSort s
  | tProd na A B => tProd nAnon (nl A) (nl B)
  | tLambda na A b => tLambda nAnon (nl A) (nl b)
  | tLetIn na b B t => tLetIn nAnon (nl b) (nl B) (nl t)
  | tApp u v => tApp (nl u) (nl v)
  | tConst c u => tConst c u
  | tInd i u => tInd i u
  | tConstruct i n u => tConstruct i n u
  | tCase indn p c brs => tCase indn (nl p) (nl c) (map (on_snd nl) brs)
  | tProj p c => tProj p (nl c)
  | tFix mfix idx => tFix (map (map_def_anon nl nl) mfix) idx
  | tCoFix mfix idx => tCoFix (map (map_def_anon nl nl) mfix) idx
  end.

Derive Signature for eq_term_upto_univ.
Derive NoConfusion NoConfusionHom for term.

Ltac destruct_one_andb :=
  lazymatch goal with
  | h : is_true (_ && _) |- _ =>
    apply andP in h ; destruct h as [? ?]
  end.

Ltac destruct_andb :=
  repeat destruct_one_andb.

Local Ltac anonify :=
  repeat lazymatch goal with
  | h : is_true (anon ?na) |- _ =>
    destruct na ; [clear h | discriminate h]
  end.

Local Ltac ih :=
  lazymatch goal with
  | ih : forall v : term, _ -> _ -> eq_term_upto_univ _ _ _ -> ?u = _
    |- ?u = ?v =>
    eapply ih ; assumption
  end.

Lemma eq_univ_make :
  forall u u',
    Forall2 eq (map Universe.make u) (map Universe.make u') ->
    u = u'.
Proof.
  intros u u' h.
  revert u' h.
  induction u ; intros u' h.
  - destruct u' ; inversion h. reflexivity.
  - destruct u' ; inversion h. subst.
    f_equal.
    + inversion H2. reflexivity.
    + eapply IHu. assumption.
Qed.

Lemma nameless_eq_term_spec :
  forall `{checker_flags} u v,
    nameless u ->
    nameless v ->
    eq_term_upto_univ eq u v ->
    u = v.
Proof.
  intros flags u v hu hv e.
  revert v hu hv e.
  induction u using term_forall_list_ind ; intros v hu hv e.
  all: dependent destruction e.
  all: cbn in hu, hv ; destruct_andb ; anonify.
  all: try reflexivity.
  all: try solve [ f_equal ; try ih ; try assumption ].
  - f_equal. cbn in hu, hv.
    revert args' hu hv H0. induction l ; intros args' hu hv h.
    + destruct args' ; try solve [ inversion h ].
      reflexivity.
    + destruct args' ; try solve [ inversion h ].
      inversion h. subst.
      inversion H. subst.
      cbn in hu, hv. destruct_andb.
      f_equal.
      * eapply H2 ; assumption.
      * eapply IHl ; assumption.
  - f_equal ; try solve [ ih ].
    eapply eq_univ_make. assumption.
  - f_equal ; try solve [ ih ].
    eapply eq_univ_make. assumption.
  - f_equal ; try solve [ ih ].
    eapply eq_univ_make. assumption.
  - f_equal ; try solve [ ih ].
    revert brs' H4 H1 H.
    induction l ; intros brs' h1 h2 h.
    + destruct brs' ; inversion h. reflexivity.
    + destruct brs' ; inversion h. subst.
      cbn in h1, h2. destruct_andb.
      inversion X. subst.
      f_equal.
      * destruct a, p. cbn in *. destruct H6. subst.
        f_equal. eapply H11 ; assumption.
      * eapply IHl ; assumption.
  - f_equal ; try solve [ ih ].
    revert mfix' H2 H3 H0 H1 H.
    induction m ; intros m' h1 h2 h3 h4 h.
    + destruct m' ; inversion h. reflexivity.
    + destruct m' ; inversion h. subst.
      inversion X. subst.
      cbn in h1, h2, h3, h4. destruct_andb.
      f_equal.
      * destruct a, d. cbn in *. destruct H2 as [? [? ?]].
        unfold test_def in H7, H. cbn in H7, H.
        destruct_andb. anonify.
        f_equal.
        -- eapply H1 ; assumption.
        -- eapply H1 ; assumption.
        -- assumption.
      * eapply IHm ; assumption.
  - f_equal ; try solve [ ih ].
    revert mfix' H2 H3 H0 H1 H.
    induction m ; intros m' h1 h2 h3 h4 h.
    + destruct m' ; inversion h. reflexivity.
    + destruct m' ; inversion h. subst.
      inversion X. subst.
      cbn in h1, h2, h3, h4. destruct_andb.
      f_equal.
      * destruct a, d. cbn in *. destruct H2 as [? [? ?]].
        unfold test_def in H7, H. cbn in H7, H.
        destruct_andb. anonify.
        f_equal.
        -- eapply H1 ; assumption.
        -- eapply H1 ; assumption.
        -- assumption.
      * eapply IHm ; assumption.
Qed.

Lemma nl_spec :
  forall u, nameless (nl u).
Proof.
  intros u. induction u using term_forall_list_ind.
  all: try reflexivity.
  all: try (simpl ; repeat (eapply andb_true_intro ; split) ; assumption).
  - cbn. eapply All_forallb. eapply All_map. assumption.
  - simpl ; repeat (eapply andb_true_intro ; split) ; try assumption.
    induction l.
    + reflexivity.
    + cbn. inversion X. subst.
      repeat (eapply andb_true_intro ; split) ; try assumption.
      eapply IHl. assumption.
  - simpl ; repeat (eapply andb_true_intro ; split) ; try assumption.
    + induction m.
      * reflexivity.
      * cbn. eapply IHm. inversion X. subst. assumption.
    + induction m.
      * reflexivity.
      * cbn. inversion X. subst. destruct H1.
        repeat (eapply andb_true_intro ; split).
        all: try assumption.
        eapply IHm. assumption.
  - simpl ; repeat (eapply andb_true_intro ; split) ; try assumption.
    + induction m.
      * reflexivity.
      * cbn. eapply IHm. inversion X. subst. assumption.
    + induction m.
      * reflexivity.
      * cbn. inversion X. subst. destruct H1.
        repeat (eapply andb_true_intro ; split).
        all: try assumption.
        eapply IHm. assumption.
Qed.

Local Ltac ih2 :=
  lazymatch goal with
  | ih : forall v : term, eq_term_upto_univ _ ?u _ -> _
    |- eq_term_upto_univ _ (nl ?u) _ =>
    eapply ih ; assumption
  end.

(* TODO Instead prove eq_term t (nl t) + symmetry and transitivity *)
Lemma eq_term_upto_univ_nl :
  forall `{checker_flags} u v,
    eq_term_upto_univ eq u v ->
    eq_term_upto_univ eq (nl u) (nl v).
Proof.
  intros flags u v h.
  revert v h.
  induction u using term_forall_list_ind ; intros v h.
  all: dependent destruction h.
  all: try (simpl ; constructor ; try ih2 ; assumption).
  + cbn. constructor.
    eapply Forall2_map.
    eapply Forall2_impl' ; try eassumption.
    eapply All_Forall. assumption.
  + cbn. constructor ; try ih2.
    eapply Forall2_map.
    eapply Forall2_impl' ; try eassumption.
    clear - X. induction X.
    * constructor.
    * constructor ; try assumption.
      intros [n t] [hn ht].
      split ; try assumption.
      eapply p. assumption.
  + cbn. constructor ; try ih2.
    eapply Forall2_map.
    eapply Forall2_impl' ; try eassumption.
    clear - X. induction X.
    * constructor.
    * constructor ; try assumption.
      intros y [? [? ?]]. repeat split.
      -- eapply p. assumption.
      -- eapply p. assumption.
      -- assumption.
  + cbn. constructor ; try ih2.
    eapply Forall2_map.
    eapply Forall2_impl' ; try eassumption.
    clear - X. induction X.
    * constructor.
    * constructor ; try assumption.
      intros y [? [? ?]]. repeat split.
      -- eapply p. assumption.
      -- eapply p. assumption.
      -- assumption.
Qed.

Corollary eq_term_nl_eq :
  forall `{checker_flags} u v,
    eq_term_upto_univ eq u v ->
    nl u = nl v.
Proof.
  intros flags u v h.
  eapply nameless_eq_term_spec.
  - eapply nl_spec.
  - eapply nl_spec.
  - eapply eq_term_upto_univ_nl. assumption.
Qed.

Local Ltac ih3 :=
  lazymatch goal with
  | ih : forall v : term, eq_term_upto_univ _ (nl ?u) _ -> _
    |- eq_term_upto_univ _ ?u _ =>
    eapply ih ; assumption
  end.

(* TODO Move *)
Lemma Forall2_map_inv :
  forall {A B A' B'} (R : A' -> B' -> Prop) (f : A -> A')
    (g : B -> B') (l : list A) (l' : list B),
    Forall2 R (map f l) (map g l') ->
    Forall2 (fun x => R (f x) ∘ g) l l'.
Proof.
  intros A B A' B' R f g l l' h.
  induction l in l', h |- * ; destruct l' ; try solve [ inversion h ].
  - constructor.
  - constructor.
    + inversion h. subst. assumption.
    + eapply IHl. inversion h. assumption.
Qed.

Lemma eq_term_upto_univ_nl_inv :
  forall `{checker_flags} R u v,
    Reflexive R ->
    eq_term_upto_univ R (nl u) (nl v) ->
    eq_term_upto_univ R u v.
Proof.
  intros flags R u v hR h.
  revert v h.
  induction u using term_forall_list_ind ; intros v h.
  all: dependent destruction h.
  all: destruct v ; try discriminate.
  all: try solve [
    try lazymatch goal with
    | h : nl _ = _ |- _ =>
      simpl in h ; inversion h ; subst
    end ;
    constructor ;
    try ih3 ;
    assumption
  ].
  - cbn in H1. inversion H1. subst. constructor.
    apply Forall2_map_inv in H0.
    eapply Forall2_impl' ; try eassumption.
    eapply All_Forall. assumption.
  - cbn in H0. inversion H0. subst. constructor ; try ih3.
    apply Forall2_map_inv in H.
    eapply Forall2_impl' ; try eassumption.
    eapply All_Forall. eapply All_impl ; [ exact X |].
    intros x H1 y [? ?]. split ; auto.
  - cbn in H0. inversion H0. subst. constructor.
    apply Forall2_map_inv in H.
    eapply Forall2_impl' ; try eassumption.
    eapply All_Forall. eapply All_impl ; [ exact X |].
    intros x [? ?] y [? [? ?]]. repeat split ; auto.
  - cbn in H0. inversion H0. subst. constructor.
    apply Forall2_map_inv in H.
    eapply Forall2_impl' ; try eassumption.
    eapply All_Forall. eapply All_impl ; [ exact X |].
    intros x [? ?] y [? [? ?]]. repeat split ; auto.
Qed.

Definition map_decl_anon f (d : context_decl) :=
  {| decl_name := nAnon ;
     decl_body := option_map f d.(decl_body) ;
     decl_type := f d.(decl_type)
  |}.

Definition nlctx (Γ : context) : context :=
  map (map_decl_anon nl) Γ.

Definition test_option {A} f (o : option A) : bool :=
  match o with
  | None => true
  | Some x => f x
  end.

Definition nameless_ctx (Γ : context) : bool :=
  forallb (fun d =>
    anon d.(decl_name) &&
    test_option nameless d.(decl_body) &&
    nameless d.(decl_type)
  ) Γ.

Lemma nlctx_spec :
  forall Γ, nameless_ctx (nlctx Γ).
Proof.
  intros Γ. induction Γ as [| [na [b|] B] Γ ih].
  - reflexivity.
  - simpl. rewrite 2!nl_spec, ih. reflexivity.
  - simpl. rewrite nl_spec, ih. reflexivity.
Qed.

Lemma eq_term_upto_univ_tm_nl :
  forall `{checker_flags} R u,
    Reflexive R ->
    eq_term_upto_univ R u (nl u).
Proof.
  intros flags R u hR.
  induction u using term_forall_list_ind.
  all: try solve [
    simpl ; try apply eq_term_upto_univ_refl ; auto ; constructor ; assumption
  ].
  - simpl. constructor.
    induction l.
    + constructor.
    + simpl. inversion H. subst. constructor ; try assumption.
      eapply IHl. assumption.
  - simpl. destruct p. constructor ; try assumption.
    induction l.
    + constructor.
    + simpl. inversion X. subst. constructor.
      * split ; auto.
      * eapply IHl. assumption.
  - simpl. constructor. induction m.
    + constructor.
    + simpl. inversion X. subst. constructor ; auto.
      repeat split ; auto.
      all: apply H1.
  - simpl. constructor. induction m.
    + constructor.
    + simpl. inversion X. subst. constructor ; auto.
      repeat split ; auto.
      all: apply H1.
Qed.

(* Corollary eq_term_tm_nl : *)
(*   forall `{checker_flags} G u, *)
(*     eq_term G u (nl u). *)
(* Proof. *)
(*   intros flags G u. *)
(*   unfold eq_term. *)
