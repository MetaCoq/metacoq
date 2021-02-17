(* Distributed under the terms of the MIT license. *)
From Coq Require Import CRelationClasses.
From MetaCoq.Template Require Import config utils Environment Ast AstUtils Reflect LiftSubst MCList
     UnivSubst WfInv Typing.

Require Import ssreflect ssrbool.
Require Import Equations.Prop.DepElim.

(** * Weak-head call-by-value evaluation strategy.

  The [wcbveval] inductive relation specifies weak cbv evaluation.  It
  is shown to be a subrelation of the 1-step reduction relation from
  which conversion is defined. Hence two terms that reduce to the same
  wcbv head normal form are convertible.

  This reduction strategy is supposed to mimick at the Coq level the
  reduction strategy of ML programming languages. It is used to state
  the extraction conjecture that can be applied to Coq terms to produce
  (untyped) terms where all proofs are erased to a dummy value. *)


Local Ltac inv H := inversion H; subst.

(** ** Big step version of weak cbv beta-zeta-iota-fix-delta reduction. *)

Definition atom t :=
  match t with
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

Definition isConstruct t :=
  match t with
  | tConstruct _ _ _ => true
  | _ => false
  end.

Definition isAssRel (Γ : context) x :=
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
  simpl. intros. rewrite -mkApp_mkApps in H.
  unfold mkApp in H. destruct (mkApps f l); discriminate.
Qed.

Section Wcbv.
  Context (Σ : global_env) (Γ : context).
  (* The local context is fixed: we are only doing weak reductions *)

  Inductive eval : term -> term -> Type :=
  (** Reductions *)
  (** Beta *)
  | eval_beta f na t b a a' l res :
      eval f (tLambda na t b) ->
      eval a a' ->
      eval (mkApps (subst10 a' b) l) res ->
      eval (tApp f (a :: l)) res

  (** Let *)
  | eval_zeta na b0 b0' t b1 res :
      eval b0 b0' ->
      eval (subst10 b0' b1) res ->
      eval (tLetIn na b0 t b1) res

  (** Local variable with bodies *)
  | eval_rel_def i body res :
      option_map decl_body (nth_error Γ i) = Some (Some body) ->
      eval (lift0 (S i) body) res ->
      eval (tRel i) res

  (** Constant unfolding *)
  | eval_delta c decl body (isdecl : declared_constant Σ c decl) u res :
      decl.(cst_body) = Some body ->
      eval (subst_instance u body) res ->
      eval (tConst c u) res

  (** Case *)
  | eval_iota ci mdecl idecl cdecl discr c u args p brs br res :
      eval discr (mkApps (tConstruct ci.(ci_ind) c u) args) ->
      nth_error brs c = Some br ->
      declared_constructor Σ (ci.(ci_ind), c) mdecl idecl cdecl ->
      let bctx := case_branch_context p cdecl in
      #|skipn (ci_npar ci) args| = context_assumptions bctx ->
      eval (iota_red ci.(ci_npar) args bctx br) res ->
      eval (tCase ci p discr brs) res

  (** Proj *)
  | eval_proj indnpararg discr args u a res :
      eval discr (mkApps (tConstruct indnpararg.1.1 0 u) args) ->
      nth_error args (indnpararg.1.2 + indnpararg.2) = Some a ->
      eval a res ->
      eval (tProj indnpararg discr) res
           
  (** Fix unfolding, with guard *)
  | eval_fix f mfix idx fixargsv args argsv narg fn res :
      eval f (mkApps (tFix mfix idx) fixargsv) ->
      All2 eval args argsv ->
      unfold_fix mfix idx = Some (narg, fn) ->
      is_constructor narg (fixargsv ++ argsv) ->
      eval (mkApps fn (fixargsv ++ argsv)) res ->
      eval (mkApps f args) res

  (** Fix stuck, with guard *)
  | eval_fix_value f mfix idx fixargsv args argsv narg fn :
      eval f (mkApps (tFix mfix idx) fixargsv) ->
      All2 eval args argsv ->
      unfold_fix mfix idx = Some (narg, fn) ->
      ~~is_constructor narg (fixargsv ++ argsv) ->
      eval (mkApps f args) (mkApps (tFix mfix idx) (fixargsv ++ argsv))

  (** CoFix-case unfolding *)
  | red_cofix_case ip mfix idx p args narg fn brs res :
      unfold_cofix mfix idx = Some (narg, fn) ->
      eval (tCase ip p (mkApps fn args) brs) res ->
      eval (tCase ip p (mkApps (tCoFix mfix idx) args) brs) res

  (** CoFix-proj unfolding *)
  | red_cofix_proj p mfix idx args narg fn res :
      unfold_cofix mfix idx = Some (narg, fn) ->
      eval (tProj p (mkApps fn args)) res ->
      eval (tProj p (mkApps (tCoFix mfix idx) args)) res

  (** Non redex-producing heads applied to values are values *)
  | eval_app_cong f f' a a' :
      ~~ isApp f -> ~~ is_empty a -> (* This ensures eval only applies to well-formed terms *)
      eval f f' ->
      ~~ (isLambda f' || isFixApp f' || isArityHead f') ->
      All2 eval a a' ->
      eval (tApp f a) (mkApps f' a')

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
      (forall (f : term) (na : aname) t b a a' l res,
          eval f (tLambda na t b) ->
          P f (tLambda na t b) -> eval a a' -> P a a' ->
          eval (mkApps (b {0 := a'}) l) res -> P (mkApps (b {0 := a'}) l) res ->
          P (tApp f (a :: l)) res) ->
      (forall (na : aname) (b0 b0' t b1 res : term),
          eval b0 b0' -> P b0 b0' -> eval (b1 {0 := b0'}) res -> P (b1 {0 := b0'}) res -> P (tLetIn na b0 t b1) res) ->
      (forall (i : nat) (body res : term),
          option_map decl_body (nth_error Γ i) = Some (Some body) ->
          eval ((lift0 (S i)) body) res -> P ((lift0 (S i)) body) res -> P (tRel i) res) ->
      (forall c (decl : constant_body) (body : term),
          declared_constant Σ c decl ->
          forall (u : Instance.t) (res : term),
            cst_body decl = Some body ->
            eval (subst_instance u body) res -> P (subst_instance u body) res -> P (tConst c u) res) ->
      (forall ci mdecl idecl cdecl (discr : term) (c : nat) (u : Instance.t)
              (args : list term) (p : predicate term) (brs : list (branch term)) br (res : term),
          let ind := ci.(ci_ind) in
          let npar := ci.(ci_npar) in
          eval discr (mkApps (tConstruct ind c u) args) ->
          P discr (mkApps (tConstruct ind c u) args) ->
          nth_error brs c = Some br ->
          declared_constructor Σ (ci.(ci_ind), c) mdecl idecl cdecl ->
          let bctx := case_branch_context p cdecl in
          #|skipn (ci_npar ci) args| = context_assumptions bctx ->
          eval (iota_red npar args bctx br) res -> P (iota_red npar args bctx br) res -> 
          P (tCase ci p discr brs) res) ->
      (forall (indnpararg : ((inductive × nat) × nat)) (discr : term) (args : list term) (u : Instance.t)
              (a res : term),
          eval discr (mkApps (tConstruct indnpararg.1.1 0 u) args) ->
          P discr (mkApps (tConstruct indnpararg.1.1 0 u) args) ->
          nth_error args (indnpararg.1.2 + indnpararg.2) = Some a -> 
          eval a res -> P a res ->
          P (tProj indnpararg discr) res) ->
      (forall (f : term) (mfix : mfixpoint term) (idx : nat) (fixargsv args argsv : list term)
             (narg : nat) (fn res : term),
        eval f (mkApps (tFix mfix idx) fixargsv) ->
        P f (mkApps (tFix mfix idx) fixargsv) ->
        All2 eval args argsv ->
        All2 P args argsv ->
        unfold_fix mfix idx = Some (narg, fn) ->
        is_constructor narg (fixargsv ++ argsv) ->
        eval (mkApps fn (fixargsv ++ argsv)) res ->
        P (mkApps fn (fixargsv ++ argsv)) res ->
        P (mkApps f args) res) ->
      (forall (f : term) (mfix : mfixpoint term) (idx : nat) (fixargsv args argsv : list term)
              (narg : nat) (fn : term),
          eval f (mkApps (tFix mfix idx) fixargsv) ->
          P f (mkApps (tFix mfix idx) fixargsv) ->
          All2 eval args argsv ->
          All2 P args argsv ->
          unfold_fix mfix idx = Some (narg, fn) ->
          ~~ is_constructor narg (fixargsv ++ argsv) ->
          P (mkApps f args) (mkApps (tFix mfix idx) (fixargsv ++ argsv))) ->
      (forall (ip : case_info) (mfix : mfixpoint term) (idx : nat) 
        (p : predicate term) (args : list term)
        (narg : nat) (fn : term) (brs : list (branch term)) (res : term),
          unfold_cofix mfix idx = Some (narg, fn) ->
          eval (tCase ip p (mkApps fn args) brs) res ->
          P (tCase ip p (mkApps fn args) brs) res -> P (tCase ip p (mkApps (tCoFix mfix idx) args) brs) res) ->
      (forall (p : projection) (mfix : mfixpoint term) (idx : nat) (args : list term) (narg : nat) (fn res : term),
          unfold_cofix mfix idx = Some (narg, fn) ->
          eval (tProj p (mkApps fn args)) res ->
          P (tProj p (mkApps fn args)) res -> P (tProj p (mkApps (tCoFix mfix idx) args)) res) ->
      (forall f f' a a',
          ~~ isApp f -> ~~ is_empty a ->
          eval f f' -> P f f' ->
          ~~ (isLambda f' || isFixApp f' || isArityHead f') ->
          All2 eval a a' -> All2 P a a' -> P (tApp f a) (mkApps f' a')) ->
      (forall t : term, atom t -> P t t) -> forall t t0 : term, eval t t0 -> P t t0.
  Proof.
    intros P Hbeta Hlet Hreldef Hcst Hcase Hproj Hfix Hstuckfix Hcofixcase Hcofixproj Happcong Hatom.
    fix eval_evals_ind 3. destruct 1;
             try solve [match goal with [ H : _ |- _ ] =>
                             match type of H with
                               forall t t0, eval t t0 -> _ => fail 1
                             | _ => eapply H
                             end end; eauto].
    - eapply Hfix; eauto.
      clear -a eval_evals_ind.
      revert args argsv a.
      fix aux 3; destruct 1; constructor; auto.
    - eapply Hstuckfix; eauto.
      clear -a eval_evals_ind.
      revert args argsv a.
      fix aux 3; destruct 1; constructor; auto.
    - eapply Happcong; auto. clear i0.
      revert a a' a0. fix aux 3; destruct 1; constructor; auto.
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
    isConstruct x || isCoFix x.

  (* Lemma value_head_atom x : value_head x -> atom x. *)
  (* Proof. destruct x; auto. Qed. *)

  Inductive value : term -> Type :=
  | value_atom t : atom t -> value t
  | value_app t l : value_head t -> All value l -> value (mkApps t l)
  | value_stuck_fix f args : All value args -> isStuckFix f args -> value (mkApps f args).

  Lemma value_values_ind : forall P : term -> Type,
      (forall t, atom t -> P t) ->
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
    intros H H'. generalize_eq x (mkApps t l).
    revert t H. induction H' using value_values_ind.
    intros. subst.
    - now eapply atom_mkApps in H.
    - intros * isapp appeq. move: (value_head_nApp H) => Ht.
      apply mkApps_eq_inj in appeq; intuition subst; auto.
    - intros * isapp appeq. move: (isStuckfix_nApp H) => Hf.
      apply mkApps_eq_inj in appeq; intuition subst; auto.
  Qed.
  
  Lemma value_mkApps_values t l :
    value (mkApps t l) ->
    ~~ isApp t ->
    All value l.
  Proof.
    intros val not_app.
    now apply value_mkApps_inv in val as [[(-> & ?)|]|].
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
    intros eve. induction eve using eval_evals_ind; simpl; intros; auto using value.

    - eapply value_stuck_fix.
      + apply All_app_inv.
        * now eapply value_mkApps_values.
        * now eapply All2_All_right.
      + unfold isStuckFix.
        now rewrite H.

    - apply All2_right in X0.
      depelim IHeve.
      destruct t; simpl in * |- *; try congruence.
      eapply value_app; auto.
      eapply value_app; auto.
      rewrite mkApps_nested.
      eapply value_app. auto.
      eapply All_app_inv; auto.
      rewrite mkApps_nested.
      eapply value_stuck_fix.
      eapply All_app_inv; auto.
      rewrite isFixApp_mkApps in H1.
      destruct f0; auto.
      destruct f0; auto.
      simpl in i. rewrite /isFixApp in H1. simpl in H1.
      rewrite orb_true_r orb_true_l in H1. easy.
  Qed.

  Lemma value_head_spec t :
    implb (value_head t) (~~ (isLambda t || isFixApp t || isArityHead t)).
  Proof.
    destruct t; simpl; intuition auto; eapply implybT.
  Qed.

  Lemma value_head_final t :
    value_head t ->
    ~~ (isLambda t || isFixApp t || isArityHead t) ->
    eval t t.
  Proof.
    destruct t; intros vt nt; try discriminate.
    - now eapply eval_atom.
    - now eapply eval_atom.
  Qed.

  Lemma value_final e : value e -> eval e e.
  Proof.
    induction 1 using value_values_ind; simpl; auto using value.
    - now constructor.
    - assert (All2 eval l l).
      { induction X0; constructor; auto. eapply IHX0. now inversion X. }
      move/implyP: (value_head_spec t).
      move/(_ H) => Ht.
      induction l using rev_ind. simpl.
      now eapply value_head_final.
      eapply All_app in X as [Hl Hx]. inv Hx.
      eapply All_app in X0 as [Hl' Hx']. inv Hx'.
      eapply All2_app_r in X1 as [Hl'' Hx''].
      pose proof (value_head_nApp H).
      rewrite -{1}mkApps_tApp => //. rewrite is_empty_app /= // andb_false_r //.
      eapply eval_app_cong; auto. rewrite is_empty_app /= andb_false_r //.
      now eapply value_head_final.
      eapply All2_app; auto.
    - destruct f; try discriminate.
      unfold isStuckFix in *.
      destruct (unfold_fix _ _) as [(? & ?)|] eqn:uf; [|easy].
      eapply (eval_fix_value _ _ _ []).
      + now eapply eval_atom.
      + now eapply All_All2.
      + easy.
      + easy.
  Qed.

  (* (** Evaluation preserves closedness: *) *)
  (* Lemma eval_closed : forall n t u, closedn n t = true -> eval t u -> closedn n u = true. *)
  (* Proof. *)
  (*   induction 2 using eval_ind; simpl in *; auto. eapply IHeval3. *)
  (*   admit. *)
  (* Admitted. (* closedness of evaluates for Eterms, not needed for verification *) *)

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

  (* Lemma eval_tRel n t : *)
  (*   eval (tRel n) t -> *)
  (*   (match option_map decl_body (nth_error Γ n) with *)
  (*    | Some (Some b) => eval (lift0 (S n) b) t *)
  (*    | _ => t = (tRel n) *)
  (*    end). *)
  (* Proof. *)
  (*   intros H; depind H; try rewrite e; try solve_discr'; try now easy. *)
  (*   destruct (mkApps_elim f args). *)
  (*   change (tRel n) with (mkApps (tRel n) []) in x. *)
  (*   eapply mkApps_eq_inj in x => //. intuition subst. constructor. simpl in x. rewrite firstn_nil in H, IHeval1. *)
  (*   specialize (IHeval1 _ eq_refl). rewrite skipn_nil in e0. discriminate. *)
  (*   change (tRel n) with (mkApps (tRel n) []) in x. *)
  (*   eapply mkApps_eq_inj in x => //. intuition subst. specialize (IHeval _ eq_refl). *)
  (*   destruct option_map as [[o|]|] => //. depelim a. simpl in i. simpl. auto. *)
  (*   eapply mkApps_nisApp in x => //. intuition subst => //. *)
  (* Qed. *)

  (* Lemma eval_tVar i t : eval (tVar i) t -> False. *)
  (* Proof. *)
  (*   intros H; depind H; try solve_discr; try now easy. *)
  (*   eapply mkApps_nisApp in x => //; intuition subst; auto. discriminate. *)
  (*   eapply mkApps_nisApp in x => //; intuition subst; auto. depelim a. eauto. *)
  (* Qed. *)

  (* Lemma eval_tEvar n l t : eval (tEvar n l) t -> False. *)
  (*                         (* exists l', All2 eval l l' /\ (t = tEvar n l'). *) *)
  (* Proof. *)
  (*   intros H; depind H; try solve_discr; try now easy. *)
  (*   eapply mkApps_nisApp in x => //; intuition subst; auto. discriminate. *)
  (*   eapply mkApps_nisApp in x => //; intuition subst; auto. eauto. *)
  (* Qed. *)

  Derive Signature for All2.

  Lemma eval_atom_inj t t' : atom t -> eval t t' -> t = t'.
  Proof.
    intros Ha H; depind H; try solve_discr'; try now easy.
    - eapply atom_mkApps in Ha; intuition subst.
      depelim a.
      apply atom_mkApps in H2 as (-> & ?).
      unfold is_constructor in *.
      now rewrite nth_error_nil in i.

    - eapply atom_mkApps in Ha; intuition subst.
      depelim a.
      apply atom_mkApps in H1 as (-> & ?).
      unfold is_constructor in *.
      now rewrite nth_error_nil in i.
  Qed.

  Derive Signature for eval.
  
  Lemma eval_to_stuck_fix_inv mfix idx narg fn t args :
    unfold_fix mfix idx = Some (narg, fn) ->
    eval t (mkApps (tFix mfix idx) args) ->
    ~~is_constructor narg args.
  Proof.
    intros uf ev.
    apply eval_to_value in ev.
    apply value_mkApps_inv in ev as [[(-> & ?)|]|]; try easy.
    - unfold is_constructor in *.
      now rewrite nth_error_nil.
    - unfold isStuckFix in *.
      now rewrite uf in p.
  Qed.

  Lemma eval_LetIn {n b ty t v} :
    eval (tLetIn n b ty t) v ->
    ∑ b',
      eval b b' * eval (t {0 := b'}) v.
  Proof.
    intros H; depind H; try solve_discr'; try now easy.
    - symmetry in H1. apply mkApps_nisApp in H1 => //; intuition subst; auto.
      depelim a.
      eapply eval_to_stuck_fix_inv in H; [|easy].
      apply negb_true_iff in H.
      now rewrite app_nil_r in i.

    - symmetry in H0. eapply mkApps_nisApp in H0 => //; intuition subst; auto.
      depelim a.
      now rewrite app_nil_r.
  Qed.

  Lemma eval_Const {c u v} :
    eval (tConst c u) v ->
    ∑ decl, declared_constant Σ c decl *
                 match cst_body decl with
                 | Some body => eval (subst_instance u body) v
                 | None => False
                 end.
  Proof.
    intros H; depind H; try solve_discr'; try now easy.
    - exists decl. intuition auto. now rewrite e.
    - symmetry in H1. eapply mkApps_nisApp in H1 => //; intuition subst; auto.
      depelim a.
      eapply eval_to_stuck_fix_inv in H; [|easy].
      apply negb_true_iff in H.
      now rewrite app_nil_r in i.
    - symmetry in H0. eapply mkApps_nisApp in H0 => //; intuition subst; auto.
      depelim a.
      apply IHeval.
      now rewrite app_nil_r.
  Qed.

  (* Lemma eval_mkApps_tCoFix mfix idx l v : *)
  (*   eval (mkApps (tCoFix mfix idx) l) v -> *)
  (*   ∑ l', All2 eval l l' * (v = mkApps (tCoFix mfix idx) l'). *)
  (* Proof. *)
  (*   intros H. *)
  (*   depind H; try solve_discr'. *)
  (*   - destruct (mkApps_elim f (a :: l0)). admit. *)
  (*     rewrite [tApp _ _](mkApps_nested f (firstn n l1) (skipn n l1)) in x. *)
  (*     solve_discr'. *)
  (*     specialize (IHeval1 _ _ _ eq_refl). *)
  (*     firstorder eauto. *)
  (*     solve_discr'. *)
  (*   - destruct (mkApps_elim f args). solve_discr'. *)
  (*     specialize (IHeval1 _ _ _ eq_refl). *)
  (*     firstorder eauto. solve_discr. *)
  (*   - destruct (mkApps_elim f args). solve_discr'. *)
  (*     specialize (IHeval _ _ _ eq_refl). *)
  (*     firstorder eauto. solve_discr. *)
  (*   - destruct (mkApps_elim f [a]). *)
  (*     replace (tApp (mkApps f (firstn n l0)) a) with (mkApps f (firstn n l0 ++ [a])) in x. *)
  (*     2:now rewrite -mkApps_nested. *)
  (*     solve_discr'. *)
  (*     specialize (IHeval1 _ _ _ eq_refl). *)
  (*     firstorder eauto. subst. *)
  (*     exists (x ++ [a']). *)
  (*     split. eapply All2_app; auto. *)
  (*     now rewrite -mkApps_nested. *)
  (*   - eapply atom_mkApps in i; intuition try easy. *)
  (*     subst. *)
  (*     exists []. intuition auto. *)
  (* Qed. *)

  (* Should follow from PCUIC's eval deterministic? *)
  (* Lemma eval_deterministic {t v v'} : eval t v -> eval t v' -> v = v'. *)
  (* Proof. *)
  (*   intros tv. revert v'. *)
  (*   revert t v tv. *)
  (*   induction 1 using eval_evals_ind; intros v' tv'. *)
  (*   - depelim tv'; auto. *)
  (*     * specialize (IHtv1 _ tv'1); try congruence. inv IHtv1. *)
  (*       specialize (IHtv2 _ tv'2). subst. *)
  (*       specialize (IHtv3 _ tv'3). now subst. *)
  (*     * rewrite [args](app_removelast_last a) in x. *)
  (*       destruct args; discriminate. *)
  (*       rewrite -mkApps_nested in x. simpl in x. injection x. intros. clear x. *)
  (*       subst. *)
  (*       admit. *)
  (* Admitted. *)
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
  (*     * depelim tv'1. *)
  (*     * depelim tv'1. *)
  (*     * rewrite H in H0. inv H0. *)
  (*       now specialize (IHtv _ tv'). *)
  (*     * now depelim tv'1. *)

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
Lemma All2_app_inv_l :
  forall A B R l1 l2 r,
    @All2 A B R (l1 ++ l2) r ->
    ∑ r1 r2,
      (r = r1 ++ r2) ×
      All2 R l1 r1 ×
      All2 R l2 r2.
Proof.
  intros A B R l1 l2 r h.
  exists (firstn #|l1| r), (skipn #|l1| r).
  split ; [| split].
  - rewrite firstn_skipn. reflexivity.
  - apply All2_firstn with (n := #|l1|) in h.
    rewrite firstn_app in h. rewrite firstn_all in h.
    replace (#|l1| - #|l1|) with 0 in h by lia. cbn in h.
    rewrite app_nil_r in h. assumption.
  - apply All2_skipn with (n := #|l1|) in h.
    rewrite skipn_all_app in h. assumption.
Qed.

  Lemma eval_mkApps_cong f f' l l' :
    ~~ isApp f ->
    eval f f' ->
    value_head f' ->
    All2 eval l l' ->
    eval (mkApps f l) (mkApps f' l').
  Proof.
    revert l'. induction l using rev_ind; intros l' appf evf vf' evl.
    depelim evl. intros. eapply evf.
    eapply All2_app_inv_l in evl as [? [? [? ?]]].
    intuition auto. subst. depelim b. depelim b.
    rewrite -mkApps_tApp => //. rewrite is_empty_app /= andb_false_r //.
    eapply eval_app_cong; auto.  rewrite is_empty_app /= andb_false_r //.
    destruct f'; auto.
    eapply All2_app; auto.
  Qed.

End Wcbv.


(** Well-typed closed programs can't go wrong: they always evaluate to a value. *)

Conjecture closed_typed_wcbeval : forall {cf : checker_flags} (Σ : global_env_ext) t T,
    Σ ;;; [] |- t : T -> ∑ u, eval (fst Σ) [] t u.

(** Evaluation is a subrelation of reduction: *)

Tactic Notation "redt" uconstr(y) := eapply (transitivity (R:=red _ _) (y:=y)).

(* Lemma wcbeval_red : forall (Σ : global_env_ext) Γ t u, *)
(*     eval Σ Γ t u -> red Σ Γ t u. *)
(* Proof. *)
(*   intros Σ. *)
(*   induction 1 using eval_evals_ind; try solve[ constructor; eauto]. *)

(*   - redt (tApp (tLambda na t b) (a :: l)); eauto. *)
(*     eapply red_app; eauto. *)
(*     redt (tApp (tLambda na t b) a'). eapply red_app; eauto. *)
(*     redt (b {0 := a'}). do 2 econstructor. apply IHX3. *)

(*   - redt (tLetIn na b0' t b1); eauto. *)
(*     eapply red_letin; auto. *)
(*     redt (b1 {0 := b0'}); auto. *)
(*     do 2 econstructor. *)

(*   - redt (lift0 (S i) body); auto. *)
(*     eapply red1_red. econstructor. *)
(*     auto. *)

(*   - redt (subst_instance u body); auto. *)
(*     eapply red1_red. econstructor; eauto. *)

(*   - redt (tCase (ind, pars) p _ brs). *)
(*     eapply red_case; eauto. *)
(*     eapply All2_same. intros. split; auto. *)
(*     redt (iota_red _ _ _ _); eauto. *)
(*     eapply red1_red. econstructor. *)

(*   - redt _. 2:eauto. *)
(*     redt (tProj _ (mkApps _ _)). eapply red_proj_c. eauto. *)
(*     apply red1_red. econstructor; eauto. *)

(*   - redt (mkApps (tFix mfix idx) args'); eauto. *)
(*     eapply red_mkApps; eauto. *)
(*     redt (mkApps fn args'); eauto. *)
(*     eapply red1_red. eapply red_fix; eauto. *)

(*   - eapply red_mkApps; auto. *)

(*   - redt _. eapply red1_red. eapply PCUICTyping.red_cofix_case; eauto. eauto. *)

(*   - redt _. 2:eauto. *)
(*     redt (tProj _ (mkApps _ _)). eapply red_proj_c. eauto. *)
(*     apply red1_red. econstructor; eauto. *)

(*   - eapply (red_mkApps _ _ [a] [a']); auto. *)
(* Qed. *)
