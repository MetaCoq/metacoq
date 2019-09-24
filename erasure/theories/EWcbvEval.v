(* Distributed under the terms of the MIT license.   *)
Set Warnings "-notation-overridden".

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From MetaCoq.Template Require Import config utils Ast.
From MetaCoq.PCUIC Require Import PCUICAstUtils.
From MetaCoq.Erasure Require Import EAst EAstUtils EInduction ELiftSubst ETyping.
From MetaCoq.Template Require AstUtils.

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
  simpl. intros. now rewrite mkApps_app in H.
Qed.

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
      eval (subst10 a' b) res ->
      eval (tApp f a) res

  (** Let *)
  | eval_zeta na b0 b0' b1 res :
      eval b0 b0' ->
      eval (subst10 b0' b1) res ->
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

  (** Fix unfolding *)
  | eval_fix f mfix idx args args' narg fn res :
      eval f (tFix mfix idx) ->
      unfold_fix mfix idx = Some (narg, fn) ->
      (* There must be at least one argument for this to succeed *)
      is_constructor_or_box narg args' ->
      (** We unfold only a fix applied exactly to narg arguments,
          avoiding overlap with [eval_beta] when there are more arguments. *)
      S narg = #|args| ->
      (* We reduce all arguments before unfolding *)
      Forall2 eval args args' ->
      eval (mkApps fn args') res ->
      eval (mkApps f args) res

  (** Fix stuck *)
  | eval_fix_value f mfix idx args args' :
      eval f (tFix mfix idx) ->
      (* We reduce all arguments to produce a suspended fix application value
         Note that the stuck fixpoint can be applied to any number of arguments
         here. *)
      Forall2 eval args args' ->
      isStuckFix (tFix mfix idx) args' ->
      eval (mkApps f args) (mkApps (tFix mfix idx) args')

  (** CoFix-case unfolding *)
  | red_cofix_case ip mfix idx args narg fn brs res :
      unfold_cofix mfix idx = Some (narg, fn) ->
      eval (tCase ip (mkApps fn args) brs) res ->
      eval (tCase ip (mkApps (tCoFix mfix idx) args) brs) res

  (** CoFix-proj unfolding *)
  | red_cofix_proj p mfix idx args narg fn res :
      unfold_cofix mfix idx = Some (narg, fn) ->
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

  Hint Constructors eval.
  
  (* Scheme Minimality for eval Sort Type. *)
  Definition eval_evals_ind :
    forall P : term -> term -> Prop,
      (forall a t t', eval a tBox -> P a tBox -> eval t t' -> P t t' -> eval (tApp a t) tBox -> P (tApp a t) tBox ) -> 
      (forall (f : term) (na : name) (b a a' res : term),
          eval f (tLambda na b) ->
          P f (tLambda na b) -> eval a a' -> P a a' -> eval (b {0 := a'}) res -> P (b {0 := a'}) res -> P (tApp f a) res) ->
      (forall (na : name) (b0 b0' b1 res : term),
          eval b0 b0' -> P b0 b0' -> eval (b1 {0 := b0'}) res -> P (b1 {0 := b0'}) res -> P (tLetIn na b0 b1) res) ->
      (forall (c : ident) (decl : constant_body) (body : term),
          declared_constant Σ c decl ->
          forall (res : term),
            cst_body decl = Some body ->
            eval body res -> P body res -> P (tConst c) res) ->
      (forall (ind : inductive) (pars : nat) (discr : term) (c : nat) 
              (args : list term) (brs : list (nat × term)) (res : term),
          eval discr (mkApps (tConstruct ind c) args) ->
          P discr (mkApps (tConstruct ind c) args) ->
          eval (iota_red pars c args brs) res -> P (iota_red pars c args brs) res -> P (tCase (ind, pars) discr brs) res) ->
      (forall ind pars discr brs n f res,
          eval discr tBox -> P discr tBox ->
          brs = [(n, f)] ->
          eval (mkApps f (repeat tBox n)) res -> P (mkApps f (repeat tBox n)) res ->
          eval (tCase (ind, pars) discr brs) res -> P (tCase (ind, pars) discr brs) res
      ) ->
      (forall (i : inductive) (pars arg : nat) (discr : term) (args : list term) (k : nat)
              (a res : term),
          eval discr (mkApps (tConstruct i k) args) ->
          P discr (mkApps (tConstruct i k) args) ->
          eval (nth (pars + arg) args tDummy) res -> P (nth (pars + arg) args tDummy) res -> P (tProj (i, pars, arg) discr) res) ->
      (forall i pars arg discr,
          eval discr tBox -> P discr tBox ->
          eval (tProj (i, pars, arg) discr) tBox -> P (tProj (i, pars, arg) discr) tBox
      ) ->
      (forall f (mfix : mfixpoint term) (idx : nat) (args args' : list term) (narg : nat) (fn res : term),
          eval f (tFix mfix idx) ->
          P f (tFix mfix idx) ->
          unfold_fix mfix idx = Some (narg, fn) ->
          is_constructor_or_box narg args' ->
          S narg = #|args| ->
          Forall2 eval args args' ->
          Forall2 P args args' ->
          eval (mkApps fn args') res -> P (mkApps fn args') res -> P (mkApps f args) res) ->
      (forall f (mfix : mfixpoint term) (idx : nat) (args args' : list term),
          eval f (tFix mfix idx) ->
          P f (tFix mfix idx) ->
          Forall2 eval args args' ->
          Forall2 P args args' ->
          isStuckFix (tFix mfix idx) args' -> P (mkApps f args) (mkApps (tFix mfix idx) args')) ->
      (forall (ip : inductive × nat) (mfix : mfixpoint term) (idx : nat) (args : list term)
              (narg : nat) (fn : term) (brs : list (nat × term)) (res : term),
          unfold_cofix mfix idx = Some (narg, fn) ->
          eval (tCase ip (mkApps fn args) brs) res ->
          P (tCase ip (mkApps fn args) brs) res -> P (tCase ip (mkApps (tCoFix mfix idx) args) brs) res) ->
      (forall (p : projection) (mfix : mfixpoint term) (idx : nat) (args : list term) (narg : nat) (fn res : term),
          unfold_cofix mfix idx = Some (narg, fn) ->
          eval (tProj p (mkApps fn args)) res ->
          P (tProj p (mkApps fn args)) res -> P (tProj p (mkApps (tCoFix mfix idx) args)) res) ->
      (forall f11 f' a a' : term,
          eval f11 f' -> P f11 f' -> ~~ (isLambda f' || isFixApp f' || isBox f') -> eval a a' -> P a a' -> P (tApp f11 a) (tApp f' a')) ->
      (forall t : term, atom t -> P t t) -> forall t t0 : term, eval t t0 -> P t t0.
  Proof.
    intros P Hbox Hbeta Hlet Hcst Hcase Hsing Hproj Hprojbox Hfix Hstuckfix Hcofixcase Hcofixproj Happcong Hatom.
    fix eval_evals_ind 3. destruct 1;
             try solve [match goal with [ H : _ |- _ ] =>
                             match type of H with
                               forall t t0, eval t t0 -> _ => fail 1
                             | _ => eapply H
                             end end; eauto].
    - eapply Hbox; eauto. 
    - eapply Hcase; eauto.
    - eapply Hfix; eauto.
      clear -H3 eval_evals_ind.
      revert args args' H3. fix aux 3. destruct 1. constructor; auto.
      constructor. now apply eval_evals_ind. now apply aux.
    - eapply Hstuckfix => //. eapply eval_evals_ind. auto.
      clear -eval_evals_ind H0.
      revert args args' H0. fix aux 3. destruct 1. constructor; auto.
      constructor. now apply eval_evals_ind. now apply aux.
  Qed.

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
    induction 1 using eval_evals_ind; simpl; auto using value.
    (* eapply (value_app (tEvar n l') []). constructor. constructor. *)
    - eapply value_stuck_fix => //.
      now eapply Forall2_right in H1. 
    - destruct (mkApps_elim f' [a']).
      eapply value_mkApps_inv in IHeval1 => //.
      destruct IHeval1; intuition subst.
      * rewrite H3.
        simpl. rewrite H3 in H. simpl in *.
        apply (value_app f [a']). rewrite H3 in H0. destruct f; simpl in * |- *; try congruence.
        constructor; auto. constructor. constructor; auto.
      * rewrite [tApp _ _](mkApps_nested _ (firstn n l) [a']).
        constructor 2; auto. eapply Forall_app_inv; auto.
      * rewrite [tApp _ _](mkApps_nested _ (firstn n l) [a']).
        erewrite isFixApp_mkApps in H0 => //.
        destruct f; simpl in *; try congruence.
        rewrite /isFixApp in H0. simpl in H0.
        rewrite orb_true_r orb_true_l in H0. easy.
  Qed.
  
  (* Lemma eval_to_value e e' : eval e e' -> value e'. *)
  (* Proof. *)
  (*   induction 1 using eval_ind; simpl; auto using value. *)
  (*   - eapply value_stuck_fix => //. *)
      
  (*     eapply Forall2_right. *)
  (*     eauto. *)
  (*     admit. *)
  (*   - destruct (mkApps_elim f' [a']). *)
  (*     eapply value_mkApps_inv in IHeval1 => //. *)
  (*     destruct IHeval1; intuition subst. *)
  (*     * rewrite H3. *)
  (*       simpl. rewrite H3 in H. simpl in *. *)
  (*       apply (value_app f0 [a']). destruct f0; simpl in * |- *; try congruence. *)
        
  (*       constructor; auto. constructor. constructor; auto. *)
  (*     * rewrite [tApp _ _](mkApps_nested _ (firstn n l) [a']). *)
  (*       constructor 2; auto. eapply All_app_inv; auto. *)
  (*     * rewrite [tApp _ _](mkApps_nested _ (firstn n l) [a']). *)
  (*       rewrite isFixApp_mkApps in H => //. *)
  (*       destruct f; simpl in *; try congruence. *)
  (*       rewrite /isFixApp in H. simpl in H. *)
  (*       rewrite orb_true_r orb_true_l in H. easy. *)
  (* Qed. *)
  (* Admitted. *)
  
  (* Lemma value_final e : value e -> eval e e. *)
  (* Proof. *)
  (*   induction 1 using value_values_ind; simpl; auto using value. *)
  (*   now constructor. *)
  (*   assert (Forall2 eval l l). *)
  (*   induction H1; constructor; auto. eapply IHForall. now depelim H0. *)
  (*   rewrite value_head_spec in H. *)
  (*   induction l using rev_ind. simpl. *)
  (*   move/andP: H => [H H']. *)
  (*   constructor; try easy. *)
  (*   rewrite mkApps_app. *)
  (*   eapply Forall_app in H0 as [Hl Hx]. depelim Hx. *)
  (*   eapply Forall2_app_r in H2 as [Hl' Hx']. *)
  (*   eapply eval_app_cong; auto. *)
  (*   eapply IHl. auto. *)
  (*   now eapply Forall2_Forall. auto. *)
  (*   move/andP: H => [Ht Ht']. *)
  (*   destruct l using rev_ind; auto. now rewrite mkApps_app; simpl. *)
  (* Qed. *)

  (* (** Evaluation preserves closedness: *) *)
  (* Lemma eval_closed : forall n t u, closedn n t = true -> eval t u -> closedn n u = true. *)
  (* Proof. *)
  (*   induction 2 using eval_ind; simpl in *; auto. eapply IHeval3. *)
  (*   admit. *)
  (* Admitted. (* closedness of evaluates for Eterms, not needed for verification *) *)

  (* Lemma eval_tApp_tFix_inv mfix idx a v : *)
  (*   eval (tApp (tFix mfix idx) a) v -> *)
  (*   (exists fn arg, *)
  (*       (unfold_fix mfix idx = Some (arg, fn)) /\ *)
  (*       (eval (tApp fn a) v)). *)
  (* Proof. *)
  (*   intros H; depind H; try solve_discr. *)
  (*   - depelim H. *)
  (*   - depelim H. *)
  (*   - eexists _, _; firstorder eauto.  *)
  (*   - now depelim H. *)
  (*   - discriminate. *)
  (* Qed. *)

  (* Lemma eval_tBox t : eval tBox t -> t = tBox. *)
  (* Proof. *)
  (*   intros H; depind H; try solve_discr. auto. *)
  (* Qed. *)

  (* Lemma eval_tRel n t : eval (tRel n) t -> False. *)
  (* Proof. *)
  (*   intros H; depind H; try solve_discr; try now easy. *)
  (* Qed. *)

  (* Lemma eval_tVar i t : eval (tVar i) t -> False. *)
  (* Proof. *)
  (*   intros H; depind H; try solve_discr; try now easy. *)
  (* Qed. *)

  (* Lemma eval_tEvar n l t : eval (tEvar n l) t -> False. *)
  (*                         (* exists l', Forall2 eval l l' /\ (t = tEvar n l'). *) *)
  (* Proof. *)
  (*   intros H; depind H; try solve_discr; try now easy. *)
  (* Qed. *)

  (* (* Lemma eval_atom_inj t t' : atom t -> eval t t' -> t = t'. *) *)
  (* (* Proof. *) *)
  (* (*   intros Ha H; depind H; try solve_discr; try now easy. *) *)
  (* (* Qed. *) *)

  (* Lemma eval_LetIn {n b t v} : *)
  (*   eval (tLetIn n b t) v -> *)
  (*   exists b', *)
  (*     eval b b' /\ eval (t {0 := b'}) v. *)
  (* Proof. *)
  (*   intros H; depind H; try solve_discr; try now easy. *)
  (* Qed. *)

  (* Lemma eval_Const {c v} : *)
  (*   eval (tConst c) v -> *)
  (*   exists decl body, declared_constant Σ c decl /\ *)
  (*                     cst_body decl = Some body /\ *)
  (*                     eval body v. *)
  (* Proof. *)
  (*   intros H; depind H; try solve_discr; try now easy. *)
  (*   exists decl, body. intuition auto. *)
  (* Qed. *)

  (* Lemma eval_mkApps_tCoFix mfix idx l v : *)
  (*   eval (mkApps (tCoFix mfix idx) l) v -> *)
  (*   (exists l', Forall2 eval l l' /\ (v = mkApps (tCoFix mfix idx) l')). *)
  (* Proof. *)
  (*   intros H. *)
  (*   depind H; try solve_discr. *)
  (*   destruct (mkApps_elim a [t]). *)
  (*   rewrite -[tApp _ _](mkApps_app f (firstn n l0) [t]) in x. *)
  (*   solve_discr. *)
  (*   specialize (IHeval1 _ _ _ eq_refl). *)
  (*   firstorder eauto. *)
  (*   solve_discr. *)
  (*   destruct (mkApps_elim f [a]). *)
  (*   rewrite -[tApp _ _](mkApps_app f (firstn n l0) [a]) in x. solve_discr. *)
  (*   specialize (IHeval1 _ _ _ eq_refl). *)
  (*   firstorder eauto. solve_discr. *)
  (*   destruct (mkApps_elim f [arg]). *)
  (*   rewrite -[tApp _ _](mkApps_app f (firstn n l0) [arg]) in x. solve_discr. *)
  (*   specialize (IHeval1 _ _ _ eq_refl). destruct IHeval1. *)
  (*   destruct H2. solve_discr. *)
  (*   change (tApp f a) with (mkApps f [a]) in x. *)
  (*   assert (l <> []). *)
  (*   destruct l; simpl in *; discriminate. *)
  (*   rewrite (app_removelast_last a H2) in x |- *. *)
  (*   rewrite mkApps_app in x. simpl in x. inv x. *)
  (*   specialize (IHeval1 _ _ _ eq_refl). *)
  (*   destruct IHeval1 as [l' [evl' eqf']]. *)
  (*   exists (l' ++ [a']). *)
  (*   split. eapply Forall2_app; auto. constructor. now rewrite - !H5. constructor. *)
  (*   subst f'. *)
  (*   now rewrite mkApps_app. *)
  (*   eapply atom_mkApps in H; intuition try easy. *)
  (*   subst. *)
  (*   exists []. intuition auto. *)
  (* Qed. *)

  (* Lemma eval_deterministic {t v v'} : eval t v -> eval t v' -> v = v'. *)
  (* Proof. *)
  (*   intros tv. revert v'. *)
  (*   revert t v tv. *)
  (*   induction 1 using eval_ind; intros v' tv'. *)
  (*   - depelim tv'; auto. specialize (IHtv1 _ tv'1); congruence. *)
  (*     specialize (IHtv1 _ tv'1). now subst. *)
  (*     specialize (IHtv1 _ tv'1). now subst. easy. *)
  (*   - depelim tv'; auto; try specialize (IHtv1 _ tv'1) || solve [depelim tv1]; try congruence. *)
  (*     inv IHtv1. specialize (IHtv2 _ tv'2). subst. *)
  (*     now specialize (IHtv3 _ tv'3). *)
  (*     now subst f'. easy. *)
  (*   - eapply eval_LetIn in tv' as [b' [evb evt]]. *)
  (*     rewrite -(IHtv1 _ evb) in evt. *)
  (*     eapply (IHtv2 _ evt). *)
  (*   - depelim tv'; try solve_discr. *)
  (*     * specialize (IHtv1 _ tv'1). *)
  (*       solve_discr. inv H. *)
  (*       now specialize (IHtv2 _ tv'2). *)
  (*     * specialize (IHtv1 _ tv'1); solve_discr. *)
  (*     * eapply eval_mkApps_tCoFix in tv1 as [l' [ev' eq]]. solve_discr. *)
  (*     * easy. *)
  (*   - subst. *)
  (*     depelim tv'. *)
  (*     * specialize (IHtv1 _ tv'1). *)
  (*       solve_discr. *)
  (*     * specialize (IHtv1 _ tv'1). *)
  (*       now specialize (IHtv2 _ tv'2). *)
  (*     * pose proof tv1. eapply eval_mkApps_tCoFix in H0. *)
  (*       destruct H0 as [l' [evargs eq]]. solve_discr. *)
  (*     * easy. *)
  (*   - depelim tv' => //. *)
  (*     * specialize (IHtv1 _ tv'1). discriminate. *)
  (*     * specialize (IHtv1 _ tv'1). discriminate. *)
  (*     * specialize (IHtv1 _ tv'1). inv IHtv1. *)
  (*       rewrite H in H0. inv H0. *)
  (*       now specialize (IHtv2 _ tv'2). *)
  (*     * specialize (IHtv1 _ tv'1); subst. easy. *)

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
  (*     * specialize (IHtv1 _ tv'1).  *)
  (*       solve_discr. inv H. *)
  (*       now specialize (IHtv2 _ tv'2). *)
  (*     * specialize (IHtv1 _ tv'). solve_discr. *)
  (*     * easy. *)

  (*   - depelim tv'; try easy. *)
  (*     * eapply eval_mkApps_tCoFix in tv as [l' [evargs eq]]. *)
  (*       solve_discr. *)
  (*     * specialize (IHtv _ tv'1). solve_discr. *)

  (*   - depelim tv'; try specialize (IHtv1 _ tv'1); subst; try easy. *)
  (*     specialize (IHtv2 _ tv'2). subst. reflexivity. *)

  (*   - depelim tv'; try easy. *)
  (* Qed. *)

  (* Lemma eval_mkApps_cong f f' l l' : *)
  (*   eval f f' -> *)
  (*   value_head f' -> *)
  (*   Forall2 eval l l' -> *)
  (*   eval (mkApps f l) (mkApps f' l'). *)
  (* Proof. *)
  (*   revert l'. induction l using rev_ind; intros l' evf vf' evl. *)
  (*   depelim evl. eapply evf. *)
  (*   eapply Forall2_app_inv_l in evl as [? [? [? ?]]]. *)
  (*   intuition auto. subst. depelim H1. depelim H1. *)
  (*   rewrite !mkApps_app /=. eapply eval_app_cong; auto. *)
  (*   destruct x0 using rev_ind; simpl; [|rewrite !mkApps_app]; simpl in *; destruct f'; *)
  (*     try discriminate; constructor. *)
  (* Qed. *)

End Wcbv.
