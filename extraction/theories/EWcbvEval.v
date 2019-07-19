(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From MetaCoq.Template Require Import config utils Ast.
From MetaCoq.Extraction Require Import EAst EInduction ELiftSubst ETyping.
From MetaCoq.Template Require AstUtils.
Require Import String.
Local Open Scope string_scope.
Set Asymmetric Patterns.

Existing Instance config.default_checker_flags.


(** * Weak (head) call-by-value evaluation strategy.

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
  | tFix _ _
  | tCoFix _ _ => true
  | _ => false
  end.

Section Wcbv.
  Context (Σ : global_declarations).
  (* The local context is fixed: we are only doing weak reductions *)

  Inductive eval : term -> term -> Prop :=
  (** Reductions *)
  | eval_box a l :
      eval a tBox ->
      eval (tApp a l) tBox

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
           
  (** Fix unfolding, with guard *)
  | eval_fix mfix idx args args' narg fn res :
      unfold_fix mfix idx = Some (narg, fn) ->
      (* We do not need to check the guard in the extracted language
         as we assume reduction of closed terms, whose canonical
         form will be a constructor or a box.  *)
      (* is_constructor_or_box narg args' -> *)
      Forall2 eval args args' ->
      eval (mkApps fn args') res ->
      eval (mkApps (tFix mfix idx) args) res

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
           
  (** Abstractions are values *)
  | eval_abs na N : eval (tLambda na N) (tLambda na N)

  (** Constructors applied to values are values *)
  | eval_constr f i k l l' :
      eval f (tConstruct i k) ->
      Forall2 eval l l' ->
      eval (mkApps f l) (mkApps (tConstruct i k) l')

  (** Atoms are values *)
  | eval_atom t : atom t -> eval t t

  | eval_evar ev l : eval (tEvar ev l) (tEvar ev l) (* Lets say it is a value for now *).

  (* (** The right induction principle for the nested [Forall] cases: *) *)

  Lemma eval_evals_ind :
    forall P : term -> term -> Prop,
      (forall a l, eval a tBox ->
                   P (tApp a l) tBox) ->
      (forall (f : term) (na : name) (b a a' : term) (res : term),
          eval f (tLambda na b) ->
          P f (tLambda na b) ->
          eval a a' -> P a a' ->
          eval (b {0 := a'}) res -> P (b {0 := a'}) res -> P (tApp f a) res) ->

      (forall (na : name) (b0 b0' b1 res : term),
          eval b0 b0' -> P b0 b0' -> eval (b1 {0 := b0'}) res -> P (b1 {0 := b0'}) res ->
          P (tLetIn na b0 b1) res) ->

      (forall (ind : inductive) (pars : nat) (discr : term) (c : nat)
              (args : list term) (brs : list (nat * term)) (res : term),
          eval discr (mkApps (tConstruct ind c) args) ->
          P discr (mkApps (tConstruct ind c) args) ->
          eval (iota_red pars c args brs) res ->
          P (iota_red pars c args brs) res -> P (tCase (ind, pars) discr brs) res) ->

      (forall (ind : inductive) (pars : nat) (discr : term) (brs : list (nat * term)) (n : nat) (f3 res : term),
        eval discr tBox ->
        P discr tBox ->
        brs = [(n, f3)] ->
        eval (mkApps f3 (repeat tBox n)) res ->
        P (mkApps f3 (repeat tBox n)) res -> P (tCase (ind, pars) discr brs) res) ->
      
      (forall (mfix : mfixpoint term) (idx : nat) (args args' : list term) (narg : nat) (fn res : term),
          unfold_fix mfix idx = Some (narg, fn) ->
          Forall2 eval args args' ->
          Forall2 P args args' ->
          (* is_constructor_or_box narg args' = true -> *)
          eval (mkApps fn args') res -> P (mkApps fn args') res -> P (mkApps (tFix mfix idx) args) res) ->

      (forall (ip : inductive * nat)  (mfix : mfixpoint term) (idx : nat) (args : list term)
              (narg : nat) (fn : term) (brs : list (nat * term)) (res : term),
          unfold_cofix mfix idx = Some (narg, fn) ->
          eval (tCase ip (mkApps fn args) brs) res ->
          P (tCase ip (mkApps fn args) brs) res -> P (tCase ip (mkApps (tCoFix mfix idx) args) brs) res) ->

      (forall (p : projection) (mfix : mfixpoint term) (idx : nat) (args : list term) (narg : nat) (fn res : term),
          unfold_cofix mfix idx = Some (narg, fn) ->
          eval (tProj p (mkApps fn args)) res ->
          P (tProj p (mkApps fn args)) res -> P (tProj p (mkApps (tCoFix mfix idx) args)) res) ->

      (forall (c : ident) (decl : constant_body) (body : term),
          declared_constant Σ c decl ->
          forall (res : term),
            cst_body decl = Some body ->
            eval body res -> P body res -> P (tConst c) res) ->

      (forall (i : inductive) (pars arg : nat) (discr : term) (args : list term) (k : nat)
              (res : term),
          eval discr (mkApps (tConstruct i k) args) ->
          P discr (mkApps (tConstruct i k) args) ->
          eval (nth (pars + arg) args tDummy) res ->
          P (nth (pars + arg) args tDummy) res -> P (tProj (i, pars, arg) discr) res) ->

      (forall (i : inductive) (pars arg : nat) (discr : term),
          eval discr tBox ->
          P discr tBox ->
          P (tProj (i, pars, arg) discr) tBox) ->
      
      (forall (na : name) (M N : term), P (tLambda na N) (tLambda na N)) ->

      (forall (f8 : term) (i : inductive) (k : nat) (l l' : list term),
          eval f8 (tConstruct i k) ->
          P f8 (tConstruct i k) -> Forall2 eval l l' -> Forall2 P l l' -> P (mkApps f8 l) (mkApps (tConstruct i k) l')) ->
      (forall t, atom t -> P t t) ->

      (forall (ev : nat) (l : list term), P (tEvar ev l) (tEvar ev l)) ->

      forall t t0 : term, eval t t0 -> P t t0.
  Proof.
    intros P Hbox Hbeta Hlet Hcase Hscase Hfix Hcoficase Hcofixproj
           Hconst Hproj Hproj2 Hlam Hcstr Hatom Hevar.
    fix eval_evals_ind 3. destruct 1;
             try match goal with [ H : _ |- _ ] =>
                             match type of H with
                               forall t t0, eval t t0 -> _ => fail 1
                             | context [ atom _ ] => fail
                             | _ => try solve [eapply H; eauto]
                             end end; eauto.
    eapply Hfix. eauto. eauto.
    clear H1.
    revert args args' H0. fix aux 3. destruct 1. constructor; auto.
    constructor. now apply eval_evals_ind. now apply aux. all:eauto.
    eapply Hcstr; eauto.
    revert l l' H0. fix aux 3. destruct 1; constructor.
    now apply eval_evals_ind. apply aux. auto.
  Defined.

  (** Characterization of values for this reduction relation: *)
  (*     Basically atoms (constructors, inductives, products (FIXME sorts missing)) *)
  (*     and de Bruijn variables and lambda abstractions. Closed values disallow *)
  (*     de Bruijn variables. *)

  Inductive value : term -> Prop :=
  | value_atom t : atom t -> value t
  | value_tEvar ev l : value (tEvar ev l)
  | value_tLam na b : value (tLambda na b)
  | value_tConstructApp i k l : Forall value l -> value (mkApps (tConstruct i k) l).

  Lemma value_values_ind : forall P : term -> Prop,
      (forall t, atom t -> P t) ->
      (forall (ev : nat) (l : list term), P (tEvar ev l)) ->
      (forall (na : name) (b : term), P (tLambda na b)) ->
      (forall (i : inductive) (k : nat) (l : list term),
          Forall value l -> Forall P l -> P (mkApps (tConstruct i k) l)) ->
      forall t : term, value t -> P t.
  Proof.
    intros P ????.
    fix value_values_ind 2. destruct 1. 1-3:clear value_values_ind; auto.
    apply H2; auto.
    revert l H3. fix aux 2. destruct 1. constructor; auto.
    constructor. now apply value_values_ind. now apply aux.
  Defined.

  (** The codomain of evaluation is only values: *)
  (*     It means no redex can remain at the head of an evaluated term. *)

  Lemma eval_to_value e e' : eval e e' -> value e'.
  Proof.
    induction 1 using eval_evals_ind; simpl; auto using value.
    eapply (value_tConstructApp i k).
    apply (Forall2_right _ _ _ H1).
  Qed.

  (** Evaluation preserves closedness: *)
  Lemma eval_closed : forall n t u, closedn n t = true -> eval t u -> closedn n u = true.
  Proof.
    induction 2 using eval_evals_ind; simpl in *; auto. eapply IHeval3.
    admit.
  Admitted. (* closedness of evaluates for Eterms, not needed for verification *)

End Wcbv.
