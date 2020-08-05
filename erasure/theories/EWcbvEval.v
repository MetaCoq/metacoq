(* Distributed under the terms of the MIT license.   *)
Set Warnings "-notation-overridden".

From Coq Require Import Arith Bool List Program.
From Equations Require Import Equations.
From MetaCoq.Template Require Import config utils.
From MetaCoq.Erasure Require Import EAst EAstUtils ELiftSubst ECSubst ETyping.

Set Asymmetric Patterns.
Require Import ssreflect ssrbool.

Local Ltac inv H := inversion H; subst.

(** * Weak-head call-by-value evaluation strategy.

  The [wcbveval] inductive relation specifies weak cbv evaluation.  It
  is shown to be a subrelation of the 1-step reduction relation from
  which conversion is defined. Hence two terms that reduce to the same
  wcbv head normal form are convertible.

  This reduction strategy is supposed to mimick at the Coq level the
  reduction strategy of ML programming languages. It is used to state
  the extraction conjecture that can be applied to Coq terms to produce
  (untyped) terms where all proofs are erased to a dummy value. *)

(** ** Big step version of weak cbv beta-zeta-iota-fix-delta reduction. *)

Definition atom t :=
  match t with
  | tBox
  | tConstruct _ _
  | tCoFix _ _
  | tLambda _ _
  | tFix _ _ => true
  | _ => false
  end.

Definition isFixApp t :=
  match fst (decompose_app t) with
  | tFix _ _ => true
  | _ => false
  end.

Definition substl defs body : term :=
  fold_left (fun bod term => csubst term 0 bod)
    defs body.

Definition cunfold_fix (mfix : mfixpoint term) (idx : nat) :=
  match List.nth_error mfix idx with
  | Some d =>
    Some (d.(rarg), substl (fix_subst mfix) d.(dbody))
  | None => None
  end.

Definition isStuckFix t args :=
  match t with
  | tFix mfix idx =>
    match cunfold_fix mfix idx with
    | Some (narg, fn) =>
      ~~ is_nth_constructor_app_or_box narg args
    | None => false
    end
  | _ => false
  end.

Lemma atom_mkApps f l : atom (mkApps f l) -> (l = []) /\ atom f.
Proof.
  revert f; induction l using rev_ind. simpl. intuition auto.
  simpl. intros. now rewrite mkApps_app in H.
Qed.

Definition cunfold_cofix (mfix : mfixpoint term) (idx : nat) :=
  match List.nth_error mfix idx with
  | Some d =>
    Some (d.(rarg), substl (cofix_subst mfix) d.(dbody))
  | None => None
  end.

Section Wcbv.
  Context (Σ : global_declarations).
  (* The local context is fixed: we are only doing weak reductions *)

  Inductive eval : term -> term -> Prop :=
  (** Reductions *)
  | eval_box a t t' :
      eval a tBox ->
      eval t t' ->
      eval (tApp a t) tBox

  (** Beta *)
  | eval_beta f na b a a' res :
      eval f (tLambda na b) ->
      eval a a' ->
      eval (csubst a' 0 b) res ->
      eval (tApp f a) res

  (** Let *)
  | eval_zeta na b0 b0' b1 res :
      eval b0 b0' ->
      eval (csubst b0' 0 b1) res ->
      eval (tLetIn na b0 b1) res

  (** Case *)
  | eval_iota ind pars discr c args brs res :
      eval discr (mkApps (tConstruct ind c) args) ->
      eval (iota_red pars c args brs) res ->
      eval (tCase (ind, pars) discr brs) res

  (** Singleton case on a proof *)
  | eval_iota_sing ind pars discr brs n f res :
      eval discr tBox ->
      brs = [ (n,f) ] ->
      eval (mkApps f (repeat tBox n)) res ->
      eval (tCase (ind, pars) discr brs) res

  (** Fix unfolding, with guard *)
  | eval_fix f mfix idx argsv a av narg fn res :
      eval f (mkApps (tFix mfix idx) argsv) ->
      eval a av ->
      cunfold_fix mfix idx = Some (narg, fn) ->
      #|argsv| = narg ->
      is_constructor_app_or_box av ->
      eval (tApp (mkApps fn argsv) av) res ->
      eval (tApp f a) res

  (** Fix stuck, with guard *)
  | eval_fix_value f mfix idx argsv a av narg fn :
      eval f (mkApps (tFix mfix idx) argsv) ->
      eval a av ->
      cunfold_fix mfix idx = Some (narg, fn) ->
      (#|argsv| <> narg \/ (#|argsv| = narg /\ ~~is_constructor_app_or_box av)) ->
      eval (tApp f a) (tApp (mkApps (tFix mfix idx) argsv) av)

  (** CoFix-case unfolding *)
  | red_cofix_case ip mfix idx args narg fn brs res :
      cunfold_cofix mfix idx = Some (narg, fn) ->
      eval (tCase ip (mkApps fn args) brs) res ->
      eval (tCase ip (mkApps (tCoFix mfix idx) args) brs) res

  (** CoFix-proj unfolding *)
  | red_cofix_proj p mfix idx args narg fn res :
      cunfold_cofix mfix idx = Some (narg, fn) ->
      eval (tProj p (mkApps fn args)) res ->
      eval (tProj p (mkApps (tCoFix mfix idx) args)) res

  (** Constant unfolding *)
  | eval_delta c decl body (isdecl : declared_constant Σ c decl) res :
      decl.(cst_body) = Some body ->
      eval body res ->
      eval (tConst c) res

  (** Proj *)
  | eval_proj i pars arg discr args k res :
      eval discr (mkApps (tConstruct i k) args) ->
      eval (List.nth (pars + arg) args tDummy) res ->
      eval (tProj (i, pars, arg) discr) res

  (** Proj *)
  | eval_proj_box i pars arg discr :
      eval discr tBox ->
      eval (tProj (i, pars, arg) discr) tBox

  (** Atoms (non redex-producing heads) applied to values are values *)
  | eval_app_cong f f' a a' :
      eval f f' ->
      ~~ (isLambda f' || isFixApp f' || isBox f') ->
      eval a a' ->
      eval (tApp f a) (tApp f' a')

  (** Evars complicate reasoning due to the embedded substitution, we skip
      them for now *)
  (* | eval_evar n l l' : *)
  (*     Forall2 eval l l' -> *)
  (*     eval (tEvar n l) (tEvar n l') *)


  (** Atoms are values (includes abstractions, cofixpoints and constructors) *)
  | eval_atom t : atom t -> eval t t.

  Hint Constructors eval : core.
  Derive Signature for eval.
  Derive NoConfusionHom for term.

  (** Characterization of values for this reduction relation.
      Only constructors and cofixpoints can accumulate arguments.
      All other values are atoms and cannot have arguments:
      - box
      - abstractions
      - constant constructors
      - unapplied fixpoints and cofixpoints
   *)

  Definition value_head x :=
    isConstruct x || isCoFix x.

  Inductive value : term -> Prop :=
  | value_atom t : atom t -> value t
  (* | value_evar n l l' : Forall value l -> Forall value l' -> value (mkApps (tEvar n l) l') *)
  | value_app t l : value_head t -> Forall value l -> value (mkApps t l)
  | value_stuck_fix f args :
      Forall value args ->
      isStuckFix f args ->
      value (mkApps f args)
  .

  Lemma value_values_ind : forall P : term -> Prop,
      (forall t, atom t -> P t) ->
      (forall t l, value_head t -> Forall value l -> Forall P l -> P (mkApps t l)) ->
      (forall f args,
          Forall value args ->
          Forall P args ->
          isStuckFix f args ->
          P (mkApps f args)) ->
      forall t : term, value t -> P t.
  Proof.
    intros P ? ? ?.
    fix value_values_ind 2. destruct 1.
    - apply H; auto.
    - eapply H0; auto.
      revert l H3. fix aux 2. destruct 1. constructor; auto.
      constructor. eauto. eauto.
    - eapply H1; eauto.
      clear H3. revert args H2. fix aux 2. destruct 1. constructor; auto.
      constructor. now eapply value_values_ind. now apply aux.
  Defined.

  Lemma value_head_nApp {t} : value_head t -> ~~ isApp t.
  Proof. destruct t; auto. Qed.
  Hint Resolve value_head_nApp : core.

  Lemma isStuckfix_nApp {t args} : isStuckFix t args -> ~~ isApp t.
  Proof. destruct t; auto. Qed.
  Hint Resolve isStuckfix_nApp : core.

  Lemma atom_nApp {t} : atom t -> ~~ isApp t.
  Proof. destruct t; auto. Qed.
  Hint Resolve atom_nApp : core.

  Lemma value_mkApps_inv t l :
    ~~ isApp t ->
    value (mkApps t l) ->
    ((l = []) /\ atom t) \/ (value_head t /\ Forall value l) \/ (isStuckFix t l /\ Forall value l).
  Proof.
    intros H H'. generalize_eqs H'. revert t H. induction H' using value_values_ind.
    intros.
    subst.
    - now eapply atom_mkApps in H.
    - intros * isapp appeq. move: (value_head_nApp H) => Ht.
      apply mkApps_eq_inj in appeq; intuition subst; auto.
    - intros * isapp appeq. move: (isStuckfix_nApp H1) => Hf.
      apply mkApps_eq_inj in appeq; intuition subst; auto.
  Qed.

  (** The codomain of evaluation is only values: *)
  (*     It means no redex can remain at the head of an evaluated term. *)

  Lemma value_head_spec t :
    value_head t = (~~ (isLambda t || isFix t || isBox t)) && atom t.
  Proof.
    destruct t; intuition auto.
  Qed.

  Lemma isFixApp_mkApps f args : ~~ isApp f -> isFixApp (mkApps f args) = isFixApp f.
  Proof.
    move=> Hf.
    rewrite /isFixApp !decompose_app_mkApps // /=. now eapply negbTE in Hf.
    change f with (mkApps f []) at 2.
    rewrite !decompose_app_mkApps // /=. now eapply negbTE in Hf.
  Qed.

  Lemma Forall_app_inv {A} (P : A -> Prop) l l' : Forall P l -> Forall P l' -> Forall P (l ++ l').
  Proof.
    intros Hl Hl'. induction Hl. apply Hl'.
    constructor; intuition auto.
  Qed.

  Lemma eval_to_value e e' : eval e e' -> value e'.
  Proof.
    induction 1; simpl; auto using value.
    - change (tApp ?h ?a) with (mkApps h [a]).
      rewrite mkApps_nested.
      apply value_mkApps_inv in IHeval1; [|easy].
      destruct IHeval1 as [(-> & _)|[|(stuck & vals)]].
      + cbn in *.
        apply (value_stuck_fix _ [av]); [easy|].
        cbn.
        destruct (cunfold_fix mfix idx) as [(? & ?)|]; [|easy].
        noconf H1.
        destruct H2 as [|(<- & ?)]; [|easy].
        unfold is_nth_constructor_app_or_box.
        now rewrite (proj2 (nth_error_None _ _));
          cbn in *.
      + easy.
      + eapply value_stuck_fix; [now apply Forall_app_inv|].
        unfold isStuckFix in *.
        destruct (cunfold_fix mfix idx) as [(? & ?)|]; [|easy].
        noconf H1.
        unfold is_nth_constructor_app_or_box in *.
        destruct H2 as [|(<- & ?)]; [|now rewrite nth_error_snoc].
        destruct (Nat.ltb_spec #|argsv| narg).
        * rewrite (proj2 (nth_error_None _ _)); [|easy].
          rewrite app_length.
          cbn.
          easy.
        * now rewrite nth_error_app1.

    - destruct (mkApps_elim f' [a']).
      eapply value_mkApps_inv in IHeval1 => //.
      destruct IHeval1; intuition subst.
      * rewrite H3.
        simpl. rewrite H3 in H. simpl in *.
        apply (value_app f0 [a']). rewrite H3 in H0. destruct f0; simpl in * |- *; try congruence.
        constructor; auto. constructor. constructor; auto.
      * rewrite [tApp _ _](mkApps_nested _ (firstn n l) [a']).
        constructor 2; auto. eapply Forall_app_inv; auto.
      * rewrite [tApp _ _](mkApps_nested _ (firstn n l) [a']).
        erewrite isFixApp_mkApps in H0 => //.
        destruct f0; simpl in *; try congruence.
        rewrite /isFixApp in H0. simpl in H0.
        rewrite orb_true_r orb_true_l in H0. easy.
  Qed.

  Lemma closed_unfold_fix_cunfold_eq mfix idx : 
    closed (tFix mfix idx) ->
    unfold_fix mfix idx = cunfold_fix mfix idx.
  Proof.  
    unfold unfold_fix, cunfold_fix.
    destruct (nth_error mfix idx) eqn:Heq => //.
    move=> /= Hf; f_equal; f_equal.
    have clfix : All (closedn 0) (fix_subst mfix).
    { clear Heq d idx.
      solve_all.
      unfold fix_subst.
      move: #|mfix| => n.
      induction n. constructor.
      constructor; auto.
      simpl. solve_all. }
    move: (fix_subst mfix) (dbody d) clfix.
    clear; induction fix_subst => Hfix /= //.
    now rewrite subst_empty.
    move=> Ha; depelim Ha.
    simpl in *.
    rewrite -IHfix_subst => //.
    rewrite (subst_app_decomp [_]). simpl.
    f_equal. rewrite lift_closed // closed_subst //.
  Qed.

  Lemma closed_unfold_cofix_cunfold_eq mfix idx : 
    closed (tCoFix mfix idx) ->
    unfold_cofix mfix idx = cunfold_cofix mfix idx.
  Proof.  
    unfold unfold_cofix, cunfold_cofix.
    destruct (nth_error mfix idx) eqn:Heq => //.
    move=> /= Hf; f_equal; f_equal.
    have clfix : All (closedn 0) (cofix_subst mfix).
    { clear Heq d idx.
      solve_all.
      unfold cofix_subst.
      move: #|mfix| => n.
      induction n. constructor.
      constructor; auto.
      simpl. solve_all. }
    move: (cofix_subst mfix) (dbody d) clfix.
    clear; induction cofix_subst => Hfix /= //.
    now rewrite subst_empty.
    move=> Ha; depelim Ha.
    simpl in *.
    rewrite -IHcofix_subst => //.
    rewrite (subst_app_decomp [_]). simpl.
    f_equal. rewrite lift_closed // closed_subst //.
  Qed.

Lemma eval_mkApps_tCoFix mfix idx args v :
  eval (mkApps (tCoFix mfix idx) args) v ->
  exists args', v = mkApps (tCoFix mfix idx) args'.
Proof.
  revert v.
  induction args using List.rev_ind; intros v ev.
  + exists [].
    now depelim ev.
  + rewrite mkApps_app in ev.
    cbn in *.
    depelim ev;
      try (apply IHargs in ev1 as (? & ?); solve_discr).
    * apply IHargs in ev1 as (argsv & ->).
      exists (argsv ++ [a']).
      now rewrite mkApps_app.
    * easy.
Qed.

Derive NoConfusionHom for EAst.global_decl.

Unset SsrRewrite.
Lemma eval_deterministic {t v v'} :
  eval t v ->
  eval t v' ->
  v = v'.
Proof.
  intros ev.
  revert v'.
  depind ev; intros v' ev'.
  - depelim ev'.
    + easy.
    + now apply IHev1 in ev'1.
    + apply IHev1 in ev'1; solve_discr.
    + apply IHev1 in ev'1; solve_discr.
    + apply IHev1 in ev'1; subst; easy.
    + easy.
  - depelim ev'.
    + now apply IHev1 in ev'1.
    + apply IHev1 in ev'1; subst.
      apply IHev2 in ev'2; subst.
      noconf ev'1.
      now apply IHev3 in ev'3.
    + apply IHev1 in ev'1; solve_discr.
    + apply IHev1 in ev'1; solve_discr.
    + apply IHev1 in ev'1; subst; easy.
    + easy.
  - depelim ev'.
    + apply IHev1 in ev'1; subst.
      now apply IHev2 in ev'2.
    + easy.
  - depelim ev'.
    + apply IHev1 in ev'1; solve_discr.
      noconf H.
      now apply IHev2 in ev'2.
    + apply IHev1 in ev'1; solve_discr.
    + apply eval_mkApps_tCoFix in ev1 as (? & ?); solve_discr.
    + easy.
  - depelim ev'.
    + apply IHev1 in ev'1; solve_discr.
    + subst.
      noconf H0.
      now apply IHev2 in ev'2.
    + apply eval_mkApps_tCoFix in ev1 as (? & ?); solve_discr.
    + easy.
  - depelim ev'.
    + apply IHev1 in ev'1; solve_discr.
    + apply IHev1 in ev'1; solve_discr.
    + apply IHev1 in ev'1.
      apply mkApps_eq_inj in ev'1; try easy.
      depelim ev'1.
      noconf H2.
      subst.
      apply IHev2 in ev'2; subst.
      rewrite H4 in H.
      now noconf H.
    + apply IHev1 in ev'1.
      apply mkApps_eq_inj in ev'1; try easy.
      depelim ev'1.
      noconf H2.
      noconf H3.
      apply IHev2 in ev'2.
      subst.
      rewrite H4 in H.
      noconf H.
      destruct H5 as [|(_ & ?)]; [easy|].
      now apply negb_true_iff in H.
    + apply IHev1 in ev'1.
      subst.
      rewrite isFixApp_mkApps in H2 by easy.
      cbn in *.
      now rewrite orb_true_r in H2.
    + easy.
  - depelim ev'.
    + apply IHev1 in ev'1; solve_discr.
    + apply IHev1 in ev'1; solve_discr.
    + apply IHev1 in ev'1.
      apply IHev2 in ev'2.
      apply mkApps_eq_inj in ev'1 as (ev'1 & <-); try easy.
      noconf ev'1.
      subst.
      rewrite H1 in H.
      noconf H.
      destruct H0 as [|(? & ?)]; [easy|].
      now apply negb_true_iff in H0.
    + apply IHev1 in ev'1.
      apply IHev2 in ev'2.
      now apply mkApps_eq_inj in ev'1 as (ev'1 & <-).
    + apply IHev1 in ev'1.
      subst.
      rewrite isFixApp_mkApps in H1 by easy.
      cbn in H1.
      now rewrite orb_true_r in H1.
    + easy.
  - depelim ev'.
    + apply eval_mkApps_tCoFix in ev'1 as (? & ?); solve_discr.
    + apply eval_mkApps_tCoFix in ev'1 as (? & ?); solve_discr.
    + apply mkApps_eq_inj in H1 as (H1 & <-); try easy.
      noconf H1.
      rewrite H0 in H.
      noconf H.
      now apply IHev in ev'.
    + easy.
  - depelim ev'.
    + apply mkApps_eq_inj in H1 as (H1 & <-); try easy.
      noconf H1.
      rewrite H0 in H.
      noconf H.
      now apply IHev in ev'.
    + apply eval_mkApps_tCoFix in ev'1 as (? & ?); solve_discr.
    + apply eval_mkApps_tCoFix in ev' as (? & ?); solve_discr.
    + easy.
  - depelim ev'.
    + unfold ETyping.declared_constant in *.
      rewrite isdecl0 in isdecl.
      noconf isdecl.
      rewrite H0 in H.
      noconf H.
      now apply IHev in ev'.
    + easy.
  - depelim ev'.
    + apply eval_mkApps_tCoFix in ev1 as (? & ?); solve_discr.
    + apply IHev1 in ev'1.
      now apply mkApps_eq_inj in ev'1 as (ev'1 & <-).
    + apply IHev1 in ev'; solve_discr.
    + easy.
  - depelim ev'.
    + apply eval_mkApps_tCoFix in ev as (? & ?); solve_discr.
    + apply IHev in ev'1; solve_discr.
    + easy.
    + easy.
  - depelim ev'.
    + apply IHev1 in ev'1.
      apply IHev2 in ev'2.
      now subst.
    + apply IHev1 in ev'1.
      apply IHev2 in ev'2.
      now subst.
    + apply IHev1 in ev'1.
      apply IHev2 in ev'2.
      subst.
      rewrite isFixApp_mkApps in H by easy.
      cbn in H.
      now rewrite orb_true_r in H.
    + apply IHev1 in ev'1.
      apply IHev2 in ev'2.
      now subst.
    + apply IHev1 in ev'1.
      apply IHev2 in ev'2.
      congruence.
    + easy.
  - now depelim ev'.
Qed.
Set SsrRewrite.

End Wcbv.

Arguments eval_deterministic {_ _ _ _}.
