(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia
     Classes.RelationClasses.
From Template
Require Import config monad_utils utils AstUtils UnivSubst.
From PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICTyping.
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
  | tFix mfix idx => true
  | tCoFix mfix idx => true
  end.

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
  | tCase indn p c brs => tCase indn (nl p) (nl c) (map (on_snd nl )brs)
  | tProj p c => tProj p (nl c)
  | tFix mfix idx => tFix mfix idx
  | tCoFix mfix idx => tCoFix mfix idx
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
  | ih : forall v : term, _ -> _ -> eq_term _ _ _ -> ?u = _
    |- ?u = ?v =>
    eapply ih ; assumption
  end.

Lemma nameless_eq_term_spec :
  forall `{checker_flags} φ u v,
    nameless u ->
    nameless v ->
    eq_term φ u v ->
    u = v.
Proof.
  intros flags φ u v hu hv eq.
  revert v hu hv eq.
  induction u using term_forall_list_ind ; intros v hu hv eq.
  all: dependent destruction eq.
  all: try reflexivity.
  all: try solve [ cbn in hu, hv ; destruct_andb ; anonify ; f_equal ; ih ].
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
  - (* Problem indeed, must not be general on checker_flags
       IDEA: Erase universes depending on the flag??
     *)
    give_up.
  - cbn in hu, hv. destruct_andb.
    anonify.
    f_equal ; try solve [ ih ].
    (* Universe problem again... *)
    give_up.
  - cbn in hu, hv. destruct_andb.
    anonify.
    f_equal ; try solve [ ih ].
    (* Universe problem again... *)
    give_up.
  - cbn in hu, hv. destruct_andb.
    anonify.
    f_equal ; try solve [ ih ].
    (* Universe problem again... *)
    give_up.
  - cbn in hu, hv. destruct_andb.
    anonify.
    f_equal ; try solve [ ih ].
    revert brs' H4 H1 H.
    induction l ; intros brs' h1 h2 h.
    + destruct brs' ; try solve [ inversion h ]. reflexivity.
    + destruct brs' ; try solve [ inversion h ].
      inversion h. subst.
      cbn in h1, h2. destruct_andb.
      f_equal.
      * destruct a, p. cbn in *.
        (* Problem: the natural numbers aren't checked *)
        admit.
      * inversion X. subst.
        eapply IHl ; assumption.
  - cbn in hu, hv. destruct_andb.
    anonify.
    f_equal ; try solve [ ih ].
    revert mfix' H.
    induction m ; intros m' h.
    + destruct m' ; inversion h. reflexivity.
    + destruct m' ; inversion h. subst.
      inversion X. subst.
      f_equal.
      * destruct a, d. cbn in *. destruct H2.
        f_equal.
        -- (* maybe should be erased *) give_up.
        -- eapply H1 ; try assumption.
           (* NEED Strengthen nameless to check inside mfixpoints *)
           all: give_up.
        -- eapply H1 ; try assumption.
           (* NEED Strengthen nameless to check inside mfixpoints *)
           all: give_up.
        -- (* PROBLEM here as well *)
           give_up.
      * eapply IHm ; assumption.
  - (* SAME *)
    admit.
Abort.

Conjecture nl_spec :
  forall u, nameless (nl u).