(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia
     Classes.RelationClasses.
From Template Require Import config utils Universes BasicAst AstUtils UnivSubst.
From PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICReflect
                          PCUICLiftSubst PCUICUnivSubst PCUICTyping
                          PCUICNameless PCUICCumulativity.

Fixpoint eqb_term_upto_univ (equ : universe -> universe -> bool) (u v : term) : bool :=
  match u, v with
  | tRel n, tRel m =>
    eqb n m

  | tEvar e args, tEvar e' args' =>
    eqb e e' &&
    forallb2 (eqb_term_upto_univ equ) args args'

  | tVar id, tVar id' =>
    eqb id id'

  | tSort u, tSort u' =>
    equ u u'

  | tApp u v, tApp u' v' =>
    eqb_term_upto_univ equ u u' &&
    eqb_term_upto_univ equ v v'

  | tConst c u, tConst c' u' =>
    eqb c c' &&
    forallb2 equ (map Universe.make u) (map Universe.make u')

  | tInd i u, tInd i' u' =>
    eqb i i' &&
    forallb2 equ (map Universe.make u) (map Universe.make u')

  | tConstruct i k u, tConstruct i' k' u' =>
    eqb i i' &&
    eqb k k' &&
    forallb2 equ (map Universe.make u) (map Universe.make u')

  | tLambda na A t, tLambda na' A' t' =>
    eqb_term_upto_univ equ A A' &&
    eqb_term_upto_univ equ t t'

  | tProd na A B, tProd na' A' B' =>
    eqb_term_upto_univ equ A A' &&
    eqb_term_upto_univ equ B B'

  | tLetIn na B b u, tLetIn na' B' b' u' =>
    eqb_term_upto_univ equ B B' &&
    eqb_term_upto_univ equ b b' &&
    eqb_term_upto_univ equ u u'

  | tCase indp p c brs, tCase indp' p' c' brs' =>
    eqb indp indp' &&
    eqb_term_upto_univ equ p p' &&
    eqb_term_upto_univ equ c c' &&
    forallb2 (fun x y =>
      eqb (fst x) (fst y) &&
      eqb_term_upto_univ equ (snd x) (snd y)
    ) brs brs'

  | tProj p c, tProj p' c' =>
    eqb p p' &&
    eqb_term_upto_univ equ c c'

  | tFix mfix idx, tFix mfix' idx' =>
    eqb idx idx' &&
    forallb2 (fun x y =>
      eqb_term_upto_univ equ x.(dtype) y.(dtype) &&
      eqb_term_upto_univ equ x.(dbody) y.(dbody) &&
      eqb x.(rarg) y.(rarg)
    ) mfix mfix'

  | tCoFix mfix idx, tCoFix mfix' idx' =>
    eqb idx idx' &&
    forallb2 (fun x y =>
      eqb_term_upto_univ equ x.(dtype) y.(dtype) &&
      eqb_term_upto_univ equ x.(dbody) y.(dbody) &&
      eqb x.(rarg) y.(rarg)
    ) mfix mfix'

  | _, _ => false
  end.

(* Definition eqb_term `{checker_flags} (u v : term) : bool := *)
(*   eqb_term_upto_univ () *)

(* Definition leqb_term `{checker_flags} (u v : term) : bool := *)
(*   eqb_term_upto_univ () *)

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
  | ih : forall t', reflect (eq_term_upto_univ _ ?t _) _
    |- context [ eqb_term_upto_univ _ ?t ?t' ] =>
    destruct (ih t') ; nodec ; subst
  end.

Lemma reflect_eq_term_upto_univ :
  forall equ R,
    (forall u u', reflect (R u u') (equ u u')) ->
    forall t t', reflect (eq_term_upto_univ R t t') (eqb_term_upto_univ equ t t').
Proof.
  intros equ R h t t'.
  revert t'.
  induction t using term_forall_list_ind ; intro t'.
  all: destruct t' ; nodec.
  (* all: try solve [ *)
  (*   cbn - [eqb] ; eqspecs ; equspec equ h ; ih ; *)
  (*   constructor ; constructor ; assumption *)
  (* ]. *)
  - cbn - [eqb]. eqspecs. equspec equ h. ih.
    constructor. constructor ; assumption.
  - cbn - [eqb]. eqspecs. equspec equ h. ih.
    constructor. constructor ; assumption.
  - cbn - [eqb]. eqspecs. equspec equ h. ih.
    cbn.
    induction H in l0 |- *.
    + destruct l0.
      * constructor. constructor. constructor.
      * constructor. intro bot. inversion bot. subst.
        inversion H0.
    + destruct l0.
      * constructor. intro bot. inversion bot. subst.
        inversion H1.
      * cbn. destruct (p t).
        -- destruct (IHAll l0).
           ++ constructor. constructor. constructor ; try assumption.
              inversion e0. subst. assumption.
           ++ constructor. intro bot. inversion bot. subst.
              inversion H1. subst.
              apply n. constructor. assumption.
        -- constructor. intro bot. apply n.
           inversion bot. subst. inversion H1. subst. assumption.
  - cbn - [eqb]. eqspecs. equspec equ h.
    constructor. constructor. assumption.
  - cbn - [eqb]. eqspecs. ih.
    constructor. constructor ; assumption.
  - cbn - [eqb]. eqspecs. equspec equ h. ih.
    constructor. constructor ; assumption.
  - cbn - [eqb]. eqspecs. equspec equ h. ih.
    constructor. constructor ; assumption.
  - cbn - [eqb]. eqspecs. equspec equ h. ih.
    constructor. constructor ; assumption.
  - cbn - [eqb].
    pose proof (eqb_spec s k) as H.
    match goal with
    | |- context G[ eqb ?x ?y ] =>
      set (toto := eqb x y) in * ;
      let G' := context G[toto] in
      change G'
    end.
    destruct H ; nodec. subst.
    equspec equ h. ih.
    cbn. induction u in u0 |- *.
    + destruct u0.
      * constructor. constructor. constructor.
      * constructor. intro bot. inversion bot. subst. inversion H0.
    + destruct u0.
      * constructor. intro bot. inversion bot. subst. inversion H0.
      * cbn. equspec equ h.
        -- cbn. destruct (IHu u0).
           ++ constructor. constructor.
              inversion e. subst.
              constructor ; assumption.
           ++ constructor. intro bot. apply n.
              inversion bot. subst. constructor. inversion H0.
              subst. assumption.
        -- constructor. intro bot. apply n.
           inversion bot. subst. inversion H0. subst.
           assumption.
  - cbn - [eqb]. eqspecs. equspec equ h. ih.
    simpl. induction u in u0 |- *.
    + destruct u0.
      * constructor. constructor. constructor.
      * constructor. intro bot. inversion bot. subst. inversion H0.
    + destruct u0.
      * constructor. intro bot. inversion bot. subst. inversion H0.
      * cbn. equspec equ h.
        -- cbn. destruct (IHu u0).
           ++ constructor. constructor.
              inversion e. subst.
              constructor ; assumption.
           ++ constructor. intro bot. apply n.
              inversion bot. subst. constructor. inversion H0.
              subst. assumption.
        -- constructor. intro bot. apply n.
           inversion bot. subst. inversion H0. subst.
           assumption.
  - cbn - [eqb]. eqspecs. equspec equ h. ih.
    simpl. induction u in u0 |- *.
    + destruct u0.
      * constructor. constructor. constructor.
      * constructor. intro bot. inversion bot. subst. inversion H0.
    + destruct u0.
      * constructor. intro bot. inversion bot. subst. inversion H0.
      * cbn. equspec equ h.
        -- cbn. destruct (IHu u0).
           ++ constructor. constructor.
              inversion e. subst.
              constructor ; assumption.
           ++ constructor. intro bot. apply n.
              inversion bot. subst. constructor. inversion H0.
              subst. assumption.
        -- constructor. intro bot. apply n.
           inversion bot. subst. inversion H0. subst.
           assumption.
  - cbn - [eqb]. eqspecs. equspec equ h. ih.
    cbn - [eqb].
    destruct p0 as [i n].
    induction l in l0, X |- *.
    + destruct l0.
      * constructor. constructor ; try assumption.
        constructor.
      * constructor. intro bot. inversion bot. subst. inversion H9.
    + destruct l0.
      * constructor. intro bot. inversion bot. subst. inversion H9.
      * cbn - [eqb]. inversion X. subst.
        destruct a, p. cbn - [eqb]. eqspecs.
        -- cbn - [eqb]. pose proof (H1 t0) as hh. cbn in hh.
           destruct hh.
           ++ cbn - [eqb].
              destruct (IHl H2 l0).
              ** constructor. constructor ; try assumption.
                 constructor ; try easy.
                 inversion e2. subst. assumption.
              ** constructor. intro bot. apply n0. inversion bot. subst.
                 constructor ; try assumption.
                 inversion H11. subst. assumption.
           ++ constructor. intro bot. apply n0. inversion bot. subst.
              inversion H11. subst. destruct H5. assumption.
        -- constructor. intro bot. inversion bot. subst.
           inversion H11. subst. destruct H5. cbn in H. subst.
           apply n2. reflexivity.
  - cbn - [eqb]. eqspecs. equspec equ h. ih.
    constructor. constructor ; assumption.
  - cbn - [eqb]. eqspecs. equspec equ h. ih.
    cbn - [eqb]. induction m in X, m0 |- *.
    + destruct m0.
      * constructor. constructor. constructor.
      * constructor. intro bot. inversion bot. subst. inversion H0.
    + destruct m0.
      * constructor. intro bot. inversion bot. subst. inversion H0.
      * cbn - [eqb]. inversion X. subst.
        destruct H1 as [h1 h2].
        destruct (h1 (dtype d)).
        -- destruct (h2 (dbody d)).
           ++ cbn - [eqb]. eqspecs.
              ** cbn - [eqb]. destruct (IHm H2 m0).
                 --- constructor. constructor. constructor ; try easy.
                     inversion e2. assumption.
                 --- constructor. intro bot. apply n.
                     inversion bot. subst. constructor.
                     inversion H0. subst. assumption.
              ** constructor. intro bot. inversion bot. subst.
                 apply n. inversion H0. subst. destruct H4 as [? [? ?]].
                 assumption.
           ++ constructor. intro bot. apply n.
              inversion bot. subst. inversion H0. subst.
              apply H4.
        -- constructor. intro bot. apply n.
           inversion bot. subst. inversion H0. subst. apply H4.
  - cbn - [eqb]. eqspecs. equspec equ h. ih.
    cbn - [eqb]. induction m in X, m0 |- *.
    + destruct m0.
      * constructor. constructor. constructor.
      * constructor. intro bot. inversion bot. subst. inversion H0.
    + destruct m0.
      * constructor. intro bot. inversion bot. subst. inversion H0.
      * cbn - [eqb]. inversion X. subst.
        destruct H1 as [h1 h2].
        destruct (h1 (dtype d)).
        -- destruct (h2 (dbody d)).
           ++ cbn - [eqb]. eqspecs.
              ** cbn - [eqb]. destruct (IHm H2 m0).
                 --- constructor. constructor. constructor ; try easy.
                     inversion e2. assumption.
                 --- constructor. intro bot. apply n.
                     inversion bot. subst. constructor.
                     inversion H0. subst. assumption.
              ** constructor. intro bot. inversion bot. subst.
                 apply n. inversion H0. subst. destruct H4 as [? [? ?]].
                 assumption.
           ++ constructor. intro bot. apply n.
              inversion bot. subst. inversion H0. subst.
              apply H4.
        -- constructor. intro bot. apply n.
           inversion bot. subst. inversion H0. subst. apply H4.
Qed.

(* Syntactical equality *)
Definition nleq_term t t' :=
  eqb_term_upto_univ eqb t t'.

Corollary reflect_eq_term_upto_univ_eqb :
  forall t t',
    reflect (eq_term_upto_univ eq t t') (nleq_term t t').
Proof.
  intros t t'. eapply reflect_eq_term_upto_univ.
  eapply eqb_spec.
Qed.

Corollary reflect_nleq_term :
  forall `{checker_flags} t t',
    reflect (nl t = nl t') (nleq_term t t').
Proof.
  intros flags t t'.
  destruct (reflect_eq_term_upto_univ_eqb t t').
  - constructor. eapply eq_term_nl_eq. assumption.
  - constructor. intro bot. apply n.
    apply eq_term_upto_univ_nl_inv ; auto.
    rewrite bot.
    apply eq_term_upto_univ_refl ; auto.
Qed.

Local Ltac ih2 :=
  lazymatch goal with
  | ih : forall v, _ -> eq_term_upto_univ _ ?u _ |- eq_term_upto_univ _ ?u _ =>
    eapply ih
  end.

Lemma eq_term_upto_univ_eq_eq_term_upto_univ :
  forall R u v,
    Reflexive R ->
    eq_term_upto_univ eq u v ->
    eq_term_upto_univ R u v.
Proof.
  intros R u v hR h.
  induction u using term_forall_list_ind in v, h |- *.
  all: dependent destruction h.
  all: try solve [ constructor ; try ih2 ; try assumption ; try reflexivity ].
  - constructor. eapply Forall2_impl' ; try eassumption.
    eapply All_Forall. assumption.
  - constructor. eapply Forall2_impl ; try eassumption.
    intros x y []. reflexivity.
  - constructor. eapply Forall2_impl ; try eassumption.
    intros x y []. reflexivity.
  - constructor. eapply Forall2_impl ; try eassumption.
    intros x y []. reflexivity.
  - constructor ; try ih2 ; try assumption.
    eapply Forall2_impl' ; try eassumption.
    apply All_Forall. eapply All_impl ; try eassumption.
    intros [? ?] ? [? ?] [? ?]. split ; auto.
  - constructor. eapply Forall2_impl' ; try eassumption.
    eapply All_Forall. eapply All_impl ; try eassumption.
    intros x [? ?] y [? [? ?]]. repeat split ; auto.
  - constructor. eapply Forall2_impl' ; try eassumption.
    eapply All_Forall. eapply All_impl ; try eassumption.
    intros x [? ?] y [? [? ?]]. repeat split ; auto.
Qed.

Lemma eq_term_upto_univ_eq_eq_term :
  forall φ u v,
    eq_term_upto_univ eq u v ->
    eq_term φ u v.
Proof.
  intros φ u v h.
  eapply eq_term_upto_univ_eq_eq_term_upto_univ ; auto.
  intro x. eapply eq_universe'_refl.
Qed.