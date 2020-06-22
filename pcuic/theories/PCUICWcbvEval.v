(* Distributed under the terms of the MIT license.   *)
Set Warnings "-notation-overridden".

From Coq Require Import Bool List Lia CRelationClasses.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst
     PCUICUnivSubst PCUICTyping PCUICReduction PCUICClosed PCUICCSubst.
Require Import String.
Local Open Scope string_scope.
Set Asymmetric Patterns.

Require Import ssreflect ssrbool.

From Equations Require Import Equations.

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
  | tInd _ _
  | tConstruct _ _ _
  | tFix _ _
  | tCoFix _ _
  | tLambda _ _ _
  | tSort _
  | tProd _ _ _ => true
  | _ => false
  end.

Definition isArityHead t :=
  match t with
  | tSort _
  | tProd _ _ _ => true
  | _ => false
  end.

Definition isEvar t :=
  match t with
  | tEvar _ _ => true
  | _ => false
  end.

Definition isFix t :=
  match t with
  | tFix _ _ => true
  | _ => false
  end.

Definition isFixApp t :=
  match fst (decompose_app t) with
  | tFix _ _ => true
  | _ => false
  end.

Definition isCoFix t :=
  match t with
  | tCoFix _ _ => true
  | _ => false
  end.

Definition isInd t :=
  match t with
  | tInd _ _ => true
  | _ => false
  end.

Definition isConstruct t :=
  match t with
  | tConstruct _ _ _ => true
  | _ => false
  end.

Definition isAssRel Γ x :=
  match x with
  | tRel i =>
    match option_map decl_body (nth_error Γ i) with
    | Some None => true
    | _ => false
    end
  | _ => false
  end.

Definition isAxiom Σ x :=
  match x with
  | tConst c u =>
    match lookup_env Σ c with
    | Some (ConstantDecl {| cst_body := None |}) => true
    | _ => false
    end
  | _ => false
  end.

Definition substl defs body : term :=
  fold_left (fun bod term => csubst term 0 bod)
    defs body.

Definition cunfold_fix (mfix : mfixpoint term) (idx : nat) :=
  match List.nth_error mfix idx with
  | Some d => Some (d.(rarg), substl (fix_subst mfix) d.(dbody))
  | None => None
  end.

Definition cunfold_cofix (mfix : mfixpoint term) (idx : nat) :=
  match List.nth_error mfix idx with
  | Some d =>
    Some (d.(rarg), substl (cofix_subst mfix) d.(dbody))
  | None => None
  end.

Definition isStuckFix t args :=
  match t with
  | tFix mfix idx =>
    match unfold_fix mfix idx with
    | Some (narg, fn) =>
      ~~ is_constructor narg args
    | None => false
    end
  | _ => false
  end.

Lemma atom_mkApps f l : atom (mkApps f l) -> (l = []) /\ atom f.
Proof.
  revert f; induction l using rev_ind. simpl. intuition auto.
  simpl. intros. now rewrite -mkApps_nested in H.
Qed.

Section Wcbv.
  Context (Σ : global_env).
  (* The local context is empty: we are only doing weak reductions *)

  Inductive eval : term -> term -> Type :=
  (** Reductions *)
  (** Beta *)
  | eval_beta f na t b a a' res :
      eval f (tLambda na t b) ->
      eval a a' ->
      eval (csubst a' 0 b) res ->
      eval (tApp f a) res

  (** Let *)
  | eval_zeta na b0 b0' t b1 res :
      eval b0 b0' ->
      eval (csubst b0' 0 b1) res ->
      eval (tLetIn na b0 t b1) res

  (**
  (** Local variables: defined or undefined *)
  | eval_rel_def i body res :
      option_map decl_body (nth_error Γ i) = Some (Some body) ->
      eval (lift0 (S i) body) res ->
      eval (tRel i) res

  | eval_rel_undef i :
      option_map decl_body (nth_error Γ i) = Some None ->
      eval (tRel i) (tRel i)
  *)

  (** Constant unfolding *)
  | eval_delta c decl body (isdecl : declared_constant Σ c decl) u res :
      decl.(cst_body) = Some body ->
      eval (subst_instance_constr u body) res ->
      eval (tConst c u) res

  (** Axiom *)
  | eval_axiom c decl (isdecl : declared_constant Σ c decl) u :
      decl.(cst_body) = None ->
      eval (tConst c u) (tConst c u)

  (** Case *)
  | eval_iota ind pars discr c u args p brs res :
      eval discr (mkApps (tConstruct ind c u) args) ->
      eval (iota_red pars c args brs) res ->
      eval (tCase (ind, pars) p discr brs) res

  (** Proj *)
  | eval_proj i pars arg discr args k u a res :
      eval discr (mkApps (tConstruct i k u) args) ->
      nth_error args (pars + arg) = Some a ->
      eval a res ->
      eval (tProj (i, pars, arg) discr) res

  (** Fix unfolding, with guard *)
  | eval_fix f mfix idx args args' narg fn res :
      eval f (tFix mfix idx) ->
      cunfold_fix mfix idx = Some (narg, fn) ->
      (* There must be at least one argument for this to succeed *)
      is_constructor narg args' ->
      (** We unfold only a fix applied exactly to narg arguments,
          avoiding overlap with [eval_beta] when there are more arguments. *)
      S narg = #|args| ->
      (* We reduce all arguments before unfolding *)
      All2 eval args args' ->
      eval (mkApps fn args') res ->
      eval (mkApps f args) res

  (** Fix stuck, with guard *)
  | eval_fix_value f mfix idx args args' :
      eval f (tFix mfix idx) ->
      (* We reduce all arguments to produce a suspended fix application value
         Note that the stuck fixpoint can be applied to any number of arguments
         here. *)
      All2 eval args args' ->
      isStuckFix (tFix mfix idx) args' ->
      eval (mkApps f args) (mkApps (tFix mfix idx) args')

  (** CoFix-case unfolding *)
  | red_cofix_case ip mfix idx p args narg fn brs res :
      cunfold_cofix mfix idx = Some (narg, fn) ->
      eval (tCase ip p (mkApps fn args) brs) res ->
      eval (tCase ip p (mkApps (tCoFix mfix idx) args) brs) res

  (** CoFix-proj unfolding *)
  | red_cofix_proj p mfix idx args narg fn res :
      cunfold_cofix mfix idx = Some (narg, fn) ->
      eval (tProj p (mkApps fn args)) res ->
      eval (tProj p (mkApps (tCoFix mfix idx) args)) res

  (** Non redex-producing heads applied to values are values *)
  | eval_app_cong f f' a a' :
      eval f f' ->
      ~~ (isLambda f' || isFixApp f' || isArityHead f') ->
      eval a a' ->
      eval (tApp f a) (tApp f' a')

  (** Evars complicate reasoning due to the embedded substitution, we skip
      them for now *)
  (* | eval_evar n l l' : *)
  (*     Forall2 eval l l' -> *)
  (*     eval (tEvar n l) (tEvar n l') *)


  (** Atoms are values (includes abstractions, cofixpoints and constructors
      along with type constructors) *)
  | eval_atom t : atom t -> eval t t.

  (* Scheme Minimality for eval Sort Type. *)
  Definition eval_evals_ind :
    forall P : term -> term -> Type,
      (forall (f : term) (na : name) (t b a a' res : term),
          eval f (tLambda na t b) ->
          P f (tLambda na t b) -> eval a a' -> P a a' -> eval (csubst a' 0 b) res -> P (csubst a' 0 b) res -> P (tApp f a) res) ->
      (forall (na : name) (b0 b0' t b1 res : term),
          eval b0 b0' -> P b0 b0' -> eval (csubst b0' 0 b1) res -> 
          P (csubst b0' 0 b1) res -> P (tLetIn na b0 t b1) res) ->
      (* (forall (i : nat) (body res : term),
          option_map decl_body (nth_error Γ i) = Some (Some body) ->
          eval ((lift0 (S i)) body) res -> P ((lift0 (S i)) body) res -> P (tRel i) res) -> *)
      (* (forall i : nat, option_map decl_body (nth_error Γ i) = Some None -> P (tRel i) (tRel i)) -> *)
      (forall c (decl : constant_body) (body : term),
          declared_constant Σ c decl ->
          forall (u : Instance.t) (res : term),
            cst_body decl = Some body ->
            eval (subst_instance_constr u body) res -> P (subst_instance_constr u body) res -> P (tConst c u) res) ->
      (forall c (decl : constant_body),
          declared_constant Σ c decl -> forall u : Instance.t, cst_body decl = None -> P (tConst c u) (tConst c u)) ->
      (forall (ind : inductive) (pars : nat) (discr : term) (c : nat) (u : Instance.t)
              (args : list term) (p : term) (brs : list (nat × term)) (res : term),
          eval discr (mkApps (tConstruct ind c u) args) ->
          P discr (mkApps (tConstruct ind c u) args) ->
          eval (iota_red pars c args brs) res -> P (iota_red pars c args brs) res -> P (tCase (ind, pars) p discr brs) res) ->
      (forall (i : inductive) (pars arg : nat) (discr : term) (args : list term) (k : nat) (u : Instance.t)
              (a res : term),
          eval discr (mkApps (tConstruct i k u) args) ->
          P discr (mkApps (tConstruct i k u) args) ->
          nth_error args (pars + arg) = Some a -> eval a res -> P a res -> P (tProj (i, pars, arg) discr) res) ->
      (forall f (mfix : mfixpoint term) (idx : nat) (args args' : list term) (narg : nat) (fn res : term),
          eval f (tFix mfix idx) ->
          P f (tFix mfix idx) ->
          cunfold_fix mfix idx = Some (narg, fn) ->
          is_constructor narg args' ->
          S narg = #|args| ->
          All2 eval args args' ->
          All2 P args args' ->
          eval (mkApps fn args') res -> P (mkApps fn args') res -> P (mkApps f args) res) ->
      (forall f (mfix : mfixpoint term) (idx : nat) (args args' : list term),
          eval f (tFix mfix idx) ->
          P f (tFix mfix idx) ->
          All2 eval args args' ->
          All2 P args args' ->
          isStuckFix (tFix mfix idx) args' -> P (mkApps f args) (mkApps (tFix mfix idx) args')) ->
      (forall (ip : inductive × nat) (mfix : mfixpoint term) (idx : nat) (p : term) (args : list term)
              (narg : nat) (fn : term) (brs : list (nat × term)) (res : term),
          cunfold_cofix mfix idx = Some (narg, fn) ->
          eval (tCase ip p (mkApps fn args) brs) res ->
          P (tCase ip p (mkApps fn args) brs) res -> P (tCase ip p (mkApps (tCoFix mfix idx) args) brs) res) ->
      (forall (p : projection) (mfix : mfixpoint term) (idx : nat) (args : list term) (narg : nat) (fn res : term),
          cunfold_cofix mfix idx = Some (narg, fn) ->
          eval (tProj p (mkApps fn args)) res ->
          P (tProj p (mkApps fn args)) res -> P (tProj p (mkApps (tCoFix mfix idx) args)) res) ->
      (forall f11 f' a a' : term,
          eval f11 f' -> P f11 f' -> ~~ (isLambda f' || isFixApp f' || isArityHead f') -> eval a a' -> P a a' -> P (tApp f11 a) (tApp f' a')) ->
      (forall t : term, atom t -> P t t) -> forall t t0 : term, eval t t0 -> P t t0.
  Proof.
    intros P Hbeta Hlet (*Hreldef Hrelvar*) Hcst Hax Hcase Hproj Hfix Hstuckfix Hcofixcase Hcofixproj Happcong Hatom.
    fix eval_evals_ind 3. destruct 1;
             try solve [match goal with [ H : _ |- _ ] =>
                             match type of H with
                               forall t t0, eval t t0 -> _ => fail 1
                             | _ => eapply H
                             end end; eauto].
    (* - eapply Hrelvar, e. *)
    - eapply Hax; [eapply isdecl|eapply e].
    - eapply Hfix; eauto.
      clear -a eval_evals_ind.
      revert args args' a. fix aux 3. destruct 1. constructor; auto.
      constructor. now apply eval_evals_ind. now apply aux.
    - eapply Hstuckfix => //. eapply eval_evals_ind. auto.
      clear -eval_evals_ind a.
      revert args args' a. fix aux 3. destruct 1. constructor; auto.
      constructor. now apply eval_evals_ind. now apply aux.
  Defined.

  (** Characterization of values for this reduction relation.
      Only constructors and cofixpoints can accumulate arguments.
      All other values are atoms and cannot have arguments:
      - box
      - abstractions
      - constant constructors
      - unapplied fixpoints and cofixpoints
   *)

  Definition value_head x :=
    isInd x || isConstruct x || isCoFix x || isAxiom Σ x.

  (* Lemma value_head_atom x : value_head x -> atom x. *)
  (* Proof. destruct x; auto. Qed. *)

  Inductive value : term -> Type :=
  | value_atom t : atom t -> value t
  (* | value_evar n l l' : Forall value l -> Forall value l' -> value (mkApps (tEvar n l) l') *)
  | value_app t l : value_head t -> All value l -> value (mkApps t l)
  | value_stuck_fix f args :
      All value args ->
      isStuckFix f args ->
      value (mkApps f args)
  .

  Lemma value_values_ind : forall P : term -> Type,
      (forall t, atom t -> P t) ->
      (* (forall n l l', Forall value l -> Forall P l -> Forall value l' -> Forall P l' -> *)
      (*                 P (mkApps (tEvar n l) l')) -> *)
      (forall t l, value_head t -> All value l -> All P l -> P (mkApps t l)) ->
      (forall f args,
          All value args ->
          All P args ->
          isStuckFix f args ->
          P (mkApps f args)) ->
      forall t : term, value t -> P t.
  Proof.
    intros P ???.
    fix value_values_ind 2. destruct 1.
    - apply X; auto.
    - eapply X0; auto.
      revert l a. fix aux 2. destruct 1. constructor; auto.
      constructor. now eapply value_values_ind. now apply aux.
    - eapply X1; eauto.
      clear i. revert args a. fix aux 2. destruct 1. constructor; auto.
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
    ((l = []) * atom t) + (value_head t * All value l) + (isStuckFix t l * All value l).
  Proof.
    intros H H'. set (x := mkApps t l) in *. cut (x = mkApps t l); [|reflexivity].
    clearbody x. induction H' using value_values_ind; intro H1.
    - subst. now eapply atom_mkApps in H0.
    - move: (value_head_nApp H0) => Ht.
      apply mkApps_eq_inj in H1; intuition subst; auto.
    - move: (isStuckfix_nApp H0) => Hf.
      apply mkApps_eq_inj in H1; intuition subst; auto.
  Qed.

  (** The codomain of evaluation is only values: *)
  (*     It means no redex can remain at the head of an evaluated term. *)

  Lemma isFixApp_mkApps f args : ~~ isApp f -> isFixApp (mkApps f args) = isFixApp f.
  Proof.
    move=> Hf.
    rewrite /isFixApp !decompose_app_mkApps // /=.
    change f with (mkApps f []) at 2.
    rewrite !decompose_app_mkApps // /=.
  Qed.

  Lemma eval_to_value e e' : eval e e' -> value e'.
  Proof.
    induction 1 using eval_evals_ind; simpl; auto using value.
    (* eapply (value_app (tEvar n l') []). constructor. constructor. *)

    (* - eapply (value_app (tRel i) []). now rewrite /value_head /= H. constructor. *)
    - eapply (value_app (tConst c u) []).
      red in H.
      rewrite /value_head /= H.
      destruct decl as [? [b|] ?]; try discriminate.
      constructor. constructor.
    - eapply value_stuck_fix => //.
      now eapply All2_right in X1.
    - destruct (mkApps_elim f' [a']).
      eapply value_mkApps_inv in IHX1 => //.
      destruct IHX1; intuition subst.
      * rewrite a1.
        simpl. rewrite a1 in H. simpl in *.
        apply (value_app f [a']). destruct f; simpl in * |- *; try congruence;
        constructor; auto. constructor. auto. constructor; auto.
      * rewrite [tApp _ _](mkApps_nested _ (firstn n l) [a']).
        constructor 2; auto. eapply All_app_inv; auto.
      * rewrite [tApp _ _](mkApps_nested _ (firstn n l) [a']).
        rewrite isFixApp_mkApps in H => //.
        destruct f; simpl in *; try congruence.
        rewrite /isFixApp in H. simpl in H.
        rewrite orb_true_r orb_true_l in H. easy.
  Qed.

  Lemma value_head_spec t :
    implb (value_head t) (~~ (isLambda t || isFixApp t || isArityHead t)).
  Proof.
    destruct t; simpl; intuition auto; eapply implybT.
  Qed.

  Derive Signature for eval.

  Lemma value_final e : value e -> eval e e.
  Proof.
    induction 1 using value_values_ind; simpl; auto using value.
    - now constructor.
    - apply All_All2_refl in X0 as X1.
      move/implyP: (value_head_spec t).
      move/(_ H) => Ht.
      induction l using rev_ind. simpl.
      destruct t; try discriminate.
      (* * constructor.
        unfold value_head in H. simpl in H. destruct option_map as [[o|]|] => //. *)
      * unfold value_head in H. simpl in H.
        destruct lookup_env eqn:Heq => //.
        destruct g eqn:Heq' => //.
        destruct c as [? [b|] ?] eqn:Heq'' => //. subst.
        eapply eval_axiom. red.
        rewrite Heq. reflexivity.
        easy.
      * now eapply eval_atom.
      * now eapply eval_atom.
      * now eapply eval_atom.
      * rewrite -mkApps_nested.
        eapply All_app in X as [Hl Hx]. depelim Hx.
        eapply All_app in X0 as [Hl' Hx']. depelim Hx'.
        eapply All2_app_inv_r in X1 as [Hl'' [Hx'' [? [? ?]]]]. depelim a0. depelim a0.
        eapply eval_app_cong; auto.
        eapply IHl; auto.
        now eapply All_All2.
        (* move/andP: H => [Ht Ht']. *)
        destruct l using rev_ind; auto.
        eapply value_head_nApp in H.
        rewrite isFixApp_mkApps => //.
        rewrite -mkApps_nested; simpl.
        rewrite orb_false_r.
        destruct t; auto.
    - destruct f; try discriminate.
      apply All_All2_refl in X0.
      eapply eval_fix_value => //.
      constructor; auto.
  Qed.

  Lemma closed_beta na t b u : closed (tLambda na t b) -> closed u -> closed (csubst u 0 b).
  Proof. simpl; move/andP => [ct cb] cu. now eapply closed_csubst. Qed.

  Lemma closed_def `{checker_flags} c decl u b : wf Σ -> declared_constant Σ c decl -> 
    cst_body decl = Some b ->
    closed (subst_instance_constr u b).
  Proof.
    move=> wfΣ Hc Hb.
    rewrite PCUICClosed.closedn_subst_instance_constr.
    apply declared_decl_closed in Hc => //. simpl in Hc. red in Hc.
    rewrite Hb in Hc. simpl in Hc. now move/andP: Hc.
  Qed.
  Lemma closed_iota ind pars c u args brs : forallb (test_snd (closedn 0)) brs ->
    closed (mkApps (tConstruct ind c u) args) ->
    closed (iota_red pars c args brs).
  Proof.
    unfold iota_red => cbrs cargs.
    eapply closedn_mkApps. solve_all.
    rewrite nth_nth_error.
    destruct (nth_error_spec brs c) as [br e|e].
    eapply All_nth_error in e; eauto. simpl in e. apply e.
    auto.
    eapply closedn_mkApps_inv in cargs.
    move/andP: cargs => [Hcons Hargs]. now rewrite forallb_skipn.
  Qed.

  Lemma closed_arg f args n a :  
    closed (mkApps f args) ->
    nth_error args n = Some a -> closed a.
  Proof.
    move/closedn_mkApps_inv/andP => [cf cargs].
    solve_all. eapply All_nth_error in cargs; eauto.
  Qed.


  Lemma closed_unfold_fix mfix idx narg fn : 
    closed (tFix mfix idx) ->
    unfold_fix mfix idx = Some (narg, fn) -> closed fn.
  Proof.
    unfold unfold_fix. destruct (nth_error mfix idx) eqn:Heq.
    move=> /= Hf Heq'; noconf Heq'.
    eapply closedn_subst0. unfold fix_subst. clear -Hf. generalize #|mfix|.
    induction n; simpl; auto. apply/andP; split; auto.
    simpl. rewrite fix_subst_length. solve_all.
    eapply All_nth_error in Hf; eauto. unfold test_def in Hf.
    rewrite PeanoNat.Nat.add_0_r in Hf. now move/andP: Hf.
    discriminate.
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
    move=> Ha; dependent elimination Ha as [All_cons ca cf].
    simpl in *.
    rewrite -IHfix_subst => //.
    rewrite (subst_app_decomp [wildcard]). simpl.
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
    move=> Ha; dependent elimination Ha as [All_cons ca cf].
    simpl in *.
    rewrite -IHcofix_subst => //.
    rewrite (subst_app_decomp [wildcard]). simpl.
    f_equal. rewrite lift_closed // closed_subst //.
  Qed.

  Lemma closed_unfold_cofix mfix idx narg fn : 
    closed (tCoFix mfix idx) ->
    unfold_cofix mfix idx = Some (narg, fn) -> closed fn.
  Proof.
    unfold unfold_cofix. destruct (nth_error mfix idx) eqn:Heq.
    move=> /= Hf Heq'; noconf Heq'.
    eapply closedn_subst0. unfold cofix_subst. clear -Hf. generalize #|mfix|.
    induction n; simpl; auto. apply/andP; split; auto.
    simpl. rewrite cofix_subst_length. solve_all.
    eapply All_nth_error in Hf; eauto. unfold test_def in Hf.
    rewrite PeanoNat.Nat.add_0_r in Hf. now move/andP: Hf.
    discriminate.
  Qed.

  (** Evaluation preserves closedness: *)
  Lemma eval_closed `{checker_flags} {wfΣ : wf Σ} : forall t u, closed t -> eval t u -> closed u.
  Proof.
    move=> t u Hc ev. move: Hc.
    induction ev using eval_evals_ind; simpl in *; auto;
      (move/andP=> [/andP[Hc Hc'] Hc''] || move/andP=> [Hc Hc'] || move=>Hc); auto.
    - eapply IHev3. unshelve eapply closed_beta. 3:eauto. exact na. simpl. eauto.
    - eapply IHev2. now rewrite closed_csubst.
    - apply IHev. eapply closed_def; eauto.
    - eapply IHev2. eapply closed_iota in Hc''. eauto. eauto.
    - eapply IHev2; auto. specialize (IHev1 Hc).
      eapply closedn_mkApps_inv in IHev1.
      move/andP: IHev1 => [Hcons Hargs]. solve_all.
      eapply All_nth_error in Hargs; eauto.
    - eapply IHev2.
      eapply closedn_mkApps_inv in Hc. move/andP: Hc=> [cf cargs].
      specialize (IHev1 cf).
      rewrite -closed_unfold_fix_cunfold_eq in H0 => //.
      eapply closed_unfold_fix in H0; eauto.
      eapply closedn_mkApps; eauto.
      solve_all.
    - move/closedn_mkApps_inv/andP: Hc => [Hf Hargs]. eapply closedn_mkApps; eauto.
      solve_all.
    - eapply IHev. move/closedn_mkApps_inv/andP: Hc' => [Hfix Hargs].
      repeat (apply/andP; split; auto). eapply closedn_mkApps.
      rewrite -closed_unfold_cofix_cunfold_eq in H0 => //.
      eapply closed_unfold_cofix in H0; eauto.
      auto.
    - eapply IHev. move/closedn_mkApps_inv/andP: Hc => [Hfix Hargs].
      eapply closedn_mkApps; eauto.
      rewrite -closed_unfold_cofix_cunfold_eq in H0 => //.
      eapply closed_unfold_cofix in H0; eauto.
    - apply/andP; split; auto.
    Qed.

  (* Lemma eval_tApp_tFix_inv mfix idx a v : *)
  (*   eval (tApp (tFix mfix idx) a) v -> *)
  (*   (exists fn arg, *)
  (*       (unfold_fix mfix idx = Some (arg, fn)) * *)
  (*       (eval (tApp fn a) v)). *)
  (* Proof. *)
  (*   intros H; depind H; try solve_discr. *)
  (*   - depelim H. *)
  (*   - depelim H. *)
  (*   - eexists _, _; firstorder eauto. *)
  (*   - now depelim H. *)
  (*   - discriminate. *)
  (* Qed. *)

  (* TODO MOVE *)
  Lemma nApp_isApp_false :
    forall u,
      nApp u = 0 ->
      isApp u = false.
  Proof.
    intros u e.
    destruct u. all: simpl. all: try reflexivity.
    discriminate.
  Qed.

  Lemma eval_tRel n t :
    eval (tRel n) t -> False.
    Proof. intros H; depind H; solve_discr.
    - destruct (mkApps_elim f args).
      change (tRel n) with (mkApps (tRel n) []) in H1.
      eapply mkApps_eq_inj in H1 => //. intuition subst.
      rewrite firstn_nil in H, IHeval1.
      specialize (IHeval1 _ _ eq_refl). rewrite skipn_nil in e0. discriminate.
    - change (tRel n) with (mkApps (tRel n) []) in H0.
    eapply mkApps_eq_inj in H0 => //.
    + intuition subst.
      now specialize (IHeval _ _ eq_refl).
    + apply (f_equal nApp) in H0 as e. simpl in e.
      rewrite nApp_mkApps in e. symmetry in e.
      assert (nApp f = 0) as h by lia.
      apply nApp_isApp_false in h. rewrite h. reflexivity.
    - now simpl in i.
  Qed.
(*    (match option_map decl_body (nth_error Γ n) with
     | Some (Some b) => eval (lift0 (S n) b) t
     | _ => t = (tRel n)
     end).
  Proof.
    intros H; depind H; try rewrite e; try solve_discr; try now easy.
    - destruct (mkApps_elim f args).
      change (tRel n) with (mkApps (tRel n) []) in H1.
      eapply mkApps_eq_inj in H1 => //. intuition subst.
      rewrite firstn_nil in H, IHeval1.
      specialize (IHeval1 _ _ eq_refl). rewrite skipn_nil in e0. discriminate.
    - change (tRel n) with (mkApps (tRel n) []) in H0.
      eapply mkApps_eq_inj in H0 => //.
      + intuition subst.
        specialize (IHeval _ _ eq_refl).
        destruct option_map as [[o|]|] => //. depelim a. simpl in i.
        simpl. auto.
      + apply (f_equal nApp) in H0 as e. simpl in e.
        rewrite nApp_mkApps in e. symmetry in e.
        assert (nApp f = 0) as h by lia.
        apply nApp_isApp_false in h. rewrite h. reflexivity.
  Qed. *)

  Lemma eval_tVar i t : eval (tVar i) t -> False.
  Proof.
    intros H; depind H; try solve_discr; try now easy.
    - apply (f_equal nApp) in H1 as h. simpl in h.
      rewrite nApp_mkApps in h. lia.
    - apply (f_equal nApp) in H0 as h. simpl in h.
      rewrite nApp_mkApps in h. depelim a.
      + simpl in *. subst.
        eapply IHeval. reflexivity.
      + simpl in h. lia.
  Qed.

  Lemma eval_tEvar n l t : eval (tEvar n l) t -> False.
                          (* exists l', All2 eval l l' /\ (t = tEvar n l'). *)
  Proof.
    intros H; depind H; try solve_discr; try now easy.
    - apply (f_equal nApp) in H1 as h. simpl in h.
      rewrite nApp_mkApps in h. lia.
    - apply (f_equal nApp) in H0 as h. simpl in h.
      rewrite nApp_mkApps in h. depelim a.
      + simpl in *. subst.
        eapply IHeval. reflexivity.
      + simpl in h. lia.
  Qed.

  Lemma eval_atom_inj t t' : atom t -> eval t t' -> t = t'.
  Proof.
    intros Ha H; depind H; try solve_discr; try now easy.
    eapply atom_mkApps in Ha; intuition subst. discriminate.
    eapply atom_mkApps in Ha; intuition subst. now depelim a.
  Qed.

  Lemma eval_LetIn {n b ty t v} :
    eval (tLetIn n b ty t) v ->
    ∑ b',
      eval b b' * eval (csubst b' 0 t) v.
  Proof.
    intros H; depind H; try solve_discr; try now easy.
    - apply (f_equal nApp) in H1 as h. simpl in h.
      rewrite nApp_mkApps in h. exfalso. lia.
    - apply (f_equal nApp) in H0 as h. simpl in h.
      rewrite nApp_mkApps in h. depelim a.
      + simpl in *. subst.
        eapply IHeval. reflexivity.
      + simpl in h. exfalso. lia.
  Qed.

  Lemma eval_Const {c u v} :
    eval (tConst c u) v ->
    ∑ decl, declared_constant Σ c decl *
                 match cst_body decl with
                 | Some body => eval (subst_instance_constr u body) v
                 | None => v = tConst c u
                 end.
  Proof.
    intros H; depind H; try solve_discr; try now easy.
    - exists decl. intuition auto. now rewrite e.
    - exists decl. intuition auto. now rewrite e.
    - apply (f_equal nApp) in H1 as h.
      simpl in h. rewrite nApp_mkApps in h.
      exfalso. lia.
    - apply (f_equal nApp) in H0 as h.
      simpl in h. rewrite nApp_mkApps in h.
      destruct a.
      + simpl in *. subst.
        eapply IHeval. reflexivity.
      + exfalso. simpl in h. lia.
  Qed.

  Lemma eval_mkApps_tCoFix mfix idx l v :
    eval (mkApps (tCoFix mfix idx) l) v ->
    ∑ l', All2 eval l l' * (v = mkApps (tCoFix mfix idx) l').
  Proof.
    intros H.
    depind H; try solve_discr'.
    - destruct (mkApps_elim f [a]).
      rewrite [tApp _ _](mkApps_nested f (firstn n l0) [a]) in H2.
      solve_discr'.
      specialize (IHeval1 _ _ _ _ eq_refl).
      firstorder eauto.
      solve_discr'.
    - destruct (mkApps_elim f args). solve_discr'.
      specialize (IHeval1 _ _ _ _ eq_refl).
      firstorder eauto. solve_discr.
    - destruct (mkApps_elim f args). solve_discr'.
      specialize (IHeval _ _ _ _ eq_refl).
      firstorder eauto. solve_discr.
    - destruct (mkApps_elim f [a]).
      replace (tApp (mkApps f (firstn n l0)) a)
        with (mkApps f (firstn n l0 ++ [a])) in H1.
      2:now rewrite -mkApps_nested.
      solve_discr'.
      specialize (IHeval1 _ _ _ _ eq_refl).
      firstorder eauto. subst.
      exists (x ++ [a'])%list.
      split. eapply All2_app; auto.
      now rewrite -mkApps_nested.
    - eapply atom_mkApps in i; intuition try easy.
      subst.
      exists []. intuition auto.
  Qed.

  Lemma eval_mkApps_cong f f' l l' :
    eval f f' ->
    value_head f' ->
    All2 eval l l' ->
    eval (mkApps f l) (mkApps f' l').
  Proof.
    revert l'. induction l using rev_ind; intros l' evf vf' evl.
    depelim evl. eapply evf.
    eapply All2_app_inv in evl as [[? ?] [? ?]].
    intuition auto. subst. depelim a. depelim a.
    rewrite - !mkApps_nested /=. eapply eval_app_cong; auto.
    rewrite isFixApp_mkApps. auto.
    destruct l0 using rev_ind; simpl; [|rewrite - !mkApps_nested]; simpl in *; destruct f';
      try discriminate; try constructor.
  Qed.
  Arguments removelast : simpl nomatch.
  Lemma removelast_length {A} (l : list A) : 0 < #|l| -> #|removelast l| < #|l|.
  Proof.
    induction l; cbn -[removelast]; auto. intros.
    destruct l. auto.
    forward IHl. simpl; lia. cbn -[removelast] in *. simpl removelast. simpl. lia.
  Qed.

  Lemma eval_deterministic {t v v'} : eval t v -> eval t v' -> v = v'.
  Proof.
    intros tv. revert v'.
    revert t v tv.
    induction 1 using eval_evals_ind; intros v' tv'.
    - depelim tv'; auto.
      * specialize (IHtv1 _ tv'1); try congruence. inv IHtv1.
        specialize (IHtv2 _ tv'2). subst.
        specialize (IHtv3 _ tv'3). now subst.
      * rewrite [args](app_removelast_last a) in H.
        destruct args; discriminate.
        rewrite -mkApps_nested in H. simpl in H. injection H. intros. clear H.
        subst.
        assert (eval (mkApps f0 (removelast args)) (mkApps (tFix mfix idx) (removelast args'))).
        eapply eval_fix_value. auto. admit.
        simpl. admit.
(*        rewrite e /is_constructor. rewrite /is_constructor in i.
        destruct (nth_error (removelast args') narg) eqn:Heq.
        eapply nth_error_Some_length in Heq.
        have H':= (removelast_length args').
        forward H'. rewrite -(All2_length _ _ a0). lia.
        elimtype False. rewrite -(All2_length _ _ a0) in H'. lia. 
        constructor.*)
        specialize (IHtv1 _ X).
        solve_discr'.
      * destruct (mkApps_elim f [a]).
        destruct (mkApps_elim f0 args).
(*
    - depelim tv'; auto; try specialize (IHtv1 _ tv'1) || solve [depelim tv1]; try congruence.
      inv IHtv1. specialize (IHtv2 _ tv'2). subst.
      now specialize (IHtv3 _ tv'3).
      now subst f'. easy.
    - eapply eval_LetIn in tv' as [b' [evb evt]].
      rewrite -(IHtv1 _ evb) in evt.
      eapply (IHtv2 _ evt).
    - depelim tv'; try solve_discr.
      * specialize (IHtv1 _ tv'1).
        solve_discr. inv H.
        now specialize (IHtv2 _ tv'2).
      * specialize (IHtv1 _ tv'1); solve_discr.
      * eapply eval_mkApps_tCoFix in tv1 as [l' [ev' eq]]. solve_discr.
      * easy.
    - subst.
      depelim tv'.
      * specialize (IHtv1 _ tv'1).
        solve_discr.
      * specialize (IHtv1 _ tv'1).
        now specialize (IHtv2 _ tv'2).
      * pose proof tv1. eapply eval_mkApps_tCoFix in H0.
        destruct H0 as [l' [evargs eq]]. solve_discr.
      * easy.
    - depelim tv' => //.
      * depelim tv'1.
      * depelim tv'1.
      * rewrite H in H0. inv H0.
        now specialize (IHtv _ tv').
      * now depelim tv'1.
*)
  (*   - depelim tv'; try easy. *)
  (*     * eapply eval_mkApps_tCoFix in tv'1 as [l' [evargs eq]]. *)
  (*       solve_discr. *)
  (*     * eapply eval_mkApps_tCoFix in tv'1 as [l' [evargs eq]]. *)
  (*       solve_discr. *)
  (*     * solve_discr. inv H1. rewrite H in H0. inv H0. *)
  (*       now specialize (IHtv _ tv'). *)

  (*   - depelim tv'; try easy. *)
  (*     * solve_discr. inv H1. rewrite H in H0. inv H0. *)
  (*       now specialize (IHtv _ tv'). *)
  (*     * eapply eval_mkApps_tCoFix in tv'1 as [l' [evargs eq]]. *)
  (*       solve_discr. *)
  (*     * eapply eval_mkApps_tCoFix in tv' as [l' [evargs eq]]. *)
  (*       solve_discr. *)

  (*   - eapply eval_Const in tv' as [decl' [body' [? ?]]]. *)
  (*     intuition eauto. eapply IHtv. *)
  (*     red in isdecl, H0. rewrite H0 in isdecl. inv isdecl. *)
  (*     now rewrite H in H2; inv H2. *)

  (*   - depelim tv'. *)
  (*     * eapply eval_mkApps_tCoFix in tv1 as [l' [evargs eq]]. *)
  (*       solve_discr. *)
  (*     * specialize (IHtv1 _ tv'1). *)
  (*       solve_discr. inv H. *)
  (*       now specialize (IHtv2 _ tv'2). *)
  (*     * specialize (IHtv1 _ tv'). solve_discr. *)
  (*     * easy. *)

  (*   - depelim tv'; try easy. *)
  (*     * eapply eval_mkApps_tCoFix in tv as [l' [evargs eq]]. *)
  (*       solve_discr. *)
  (*     * specialize (IHtv _ tv'1). solve_discr. *)

  (*   - depelim tv'; try specialize (IHtv1 _ tv'1); subst; try easy. *)
  (*     depelim tv1. easy. *)
  (*     specialize (IHtv2 _ tv'2). congruence. *)

  (*   - depelim tv'; try easy. *)
  (* Qed. *)
  Admitted.

End Wcbv.


(** Well-typed closed programs can't go wrong: they always evaluate to a value. *)

Conjecture closed_typed_wcbeval : forall {cf : checker_flags} (Σ : global_env_ext) t T,
    Σ ;;; [] |- t : T -> ∑ u, eval (fst Σ) t u.

(** Evaluation is a subrelation of reduction: *)

Tactic Notation "redt" uconstr(y) := eapply (transitivity (R:=red _ _) (y:=y)).

Lemma wcbeval_red `{checker_flags} : forall (Σ : global_env_ext) t u, wf Σ -> closed t ->
    eval Σ t u -> red Σ [] t u.
Proof.
  intros Σ t u wfΣ Hc He. revert Hc.
  induction He using eval_evals_ind; simpl; 
  (move/andP => [/andP[Hc Hc'] Hc''] || move/andP => [Hc Hc'] || move => Hc);
    try solve[econstructor; eauto].

  - redt (tApp (tLambda na t b) a); eauto.
    eapply red_app; eauto.
    redt (tApp (tLambda na t b) a'). eapply red_app; eauto.
    redt (csubst a' 0 b).
    rewrite (closed_subst a' 0 b).
    eapply eval_closed; eauto. eapply red1_red. constructor.
    eapply IHHe3. eapply closed_csubst. eauto using eval_closed.
    eapply eval_closed in He1; eauto. 
    simpl in He1. now move/andP: He1.

  - redt (tLetIn na b0' t b1); eauto.
    eapply red_letin; auto.
    redt (b1 {0 := b0'}); auto.
    do 2 econstructor.
    forward IHHe2.
    eapply closed_csubst; eauto using eval_closed. unfold subst1.
    rewrite -(closed_subst b0' 0 b1); eauto using eval_closed.

  - redt (subst_instance_constr u body); auto.
    eapply red1_red. econstructor; eauto.
    apply IHHe. now eapply closed_def.

  - redt (tCase (ind, pars) p _ brs).
    eapply red_case. eauto. eapply IHHe1; eauto.
    eapply All2_same. intros. split; auto.
    redt (iota_red _ _ _ _); eauto. 2:eapply IHHe2.
    eapply red1_red. econstructor.
    eapply closed_iota; eauto. now eapply eval_closed in He1.

  - redt _. 2:eapply IHHe2; eauto using eval_closed.
    redt (tProj _ (mkApps _ _)). eapply red_proj_c. eauto.
    apply red1_red. econstructor; eauto.
    eapply eval_closed in He1; eauto. eapply closed_arg in He1; eauto.

  - move/closedn_mkApps_inv/andP: Hc => [Hf Hargs]. 
    redt (mkApps (tFix mfix idx) args'); eauto.
    eapply red_mkApps; eauto. solve_all.
    rewrite -closed_unfold_fix_cunfold_eq in H0; auto.
    eapply eval_closed in He1; eauto.
    redt (mkApps fn args'); eauto.
    eapply red1_red. eapply red_fix; eauto.
    eapply IHHe2. eapply eval_closed in He1; eauto.
    eapply closedn_mkApps; eauto using closed_unfold_fix.
    clear -wfΣ X Hargs. solve_all. now eapply eval_closed.

  - move/closedn_mkApps_inv/andP: Hc => [Hf Hargs].
    eapply red_mkApps; eauto.
    eauto using eval_closed.
    solve_all.

  - move/closedn_mkApps_inv/andP: Hc' => [Hf Hargs].
    rewrite -closed_unfold_cofix_cunfold_eq in H0; auto.
    redt _. eapply red1_red.
    eapply PCUICTyping.red_cofix_case; eauto.
    eapply IHHe.
    eapply closed_unfold_cofix in H0; eauto.
    simpl. rewrite Hc closedn_mkApps; eauto.

  - move/closedn_mkApps_inv/andP: Hc => [Hf Hargs].
    rewrite -closed_unfold_cofix_cunfold_eq in H0; auto.
    redt _. 2:eapply IHHe.
    redt (tProj _ (mkApps _ _)). eapply red_proj_c. eauto.
    apply red1_red. econstructor; eauto.
    simpl. eapply closed_unfold_cofix in H0; eauto.
    rewrite closedn_mkApps; eauto.

  - eapply (red_mkApps _ _ [a] [a']); auto.
Qed.
