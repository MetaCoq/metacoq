(* Distributed under the terms of the MIT license. *)
From Coq Require Import CRelationClasses.
From MetaCoq.Template Require Import config utils Environment Ast AstUtils Reflect LiftSubst MCList
     UnivSubst WfAst TypingWf Typing.

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

(** We use a different substitution function that requires no lifting as it assumes 
  we are substituting closed terms. *)

Fixpoint csubst t k u :=
  match u with
  | tRel n =>
     match Nat.compare k n with
    | Datatypes.Eq => t
    | Gt => tRel n
    | Lt => tRel (Nat.pred n)
    end
  | tEvar ev args => tEvar ev (List.map (csubst t k) args)
  | tLambda na T M => tLambda na (csubst t k T) (csubst t (S k) M)
  | tApp u v => mkApps (csubst t k u) (map (csubst t k) v)
  | tProd na A B => tProd na (csubst t k A) (csubst t (S k) B)
  | tLetIn na b ty b' => tLetIn na (csubst t k b) (csubst t k ty) (csubst t (S k) b')
  | tCase ind p c brs =>
    let k' := #|pcontext p| + k in
    let brs' := map_branches_k (csubst t) k brs in
    tCase ind (map_predicate id (csubst t k) (csubst t k') p) (csubst t k c) brs'
  | tProj p c => tProj p (csubst t k c)
  | tFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (csubst t k) (csubst t k')) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (csubst t k) (csubst t k')) mfix in
    tCoFix mfix' idx
  | tCast c kd c' => tCast (csubst t k c) kd (csubst t k c')
  | x => x
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

Definition isStuckFix t (args : list term) :=
  match t with
  | tFix mfix idx =>
    match cunfold_fix mfix idx with
    | Some (narg, fn) =>
      #|args| <? narg
    | None => false
    end
  | _ => false
  end.

Lemma atom_mkApps f l : atom (mkApps f l) -> (l = []) /\ atom f.
Proof.
  revert f; induction l using rev_ind. simpl. intuition auto.
  simpl. intros. rewrite -AstUtils.mkApp_mkApps in H.
  unfold mkApp in H. destruct (mkApps f l); discriminate.
Qed.

Section Wcbv.
  
  Context (Σ : global_env).
  (* The local context is fixed: we are only doing weak reductions *)

  Inductive eval : term -> term -> Type :=
  (** Reductions *)
  (** Beta *)
  | eval_beta f na t b a a' l res :
      eval f (tLambda na t b) ->
      eval a a' ->
      eval (mkApps (csubst a' 0 b) l) res ->
      eval (tApp f (a :: l)) res

  (** Let *)
  | eval_zeta na b0 b0' t b1 res :
      eval b0 b0' ->
      eval (csubst b0' 0 b1) res ->
      eval (tLetIn na b0 t b1) res

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
      let bctx := case_branch_context ci.(ci_ind) mdecl cdecl p br in
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
      ~~ isApp f ->
      eval f (mkApps (tFix mfix idx) fixargsv) ->
      All2 eval args argsv ->
      cunfold_fix mfix idx = Some (narg, fn) ->
      #|fixargsv| < narg < #|fixargsv| + #|args| ->
      eval (mkApps fn (fixargsv ++ argsv)) res ->
      eval (mkApps f args) res

  (** Fix stuck, with guard *)
  | eval_fix_value f mfix idx fixargsv args argsv narg fn :
      ~~ isApp f ->
      eval f (mkApps (tFix mfix idx) fixargsv) ->
      All2 eval args argsv ->
      cunfold_fix mfix idx = Some (narg, fn) ->
      #|fixargsv ++ argsv| < narg ->
      eval (mkApps f args) (mkApps (tFix mfix idx) (fixargsv ++ argsv))

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
          eval (mkApps (csubst a' 0 b) l) res -> P (mkApps (csubst a' 0 b) l) res ->
          P (tApp f (a :: l)) res) ->
      (forall (na : aname) (b0 b0' t b1 res : term),
          eval b0 b0' -> P b0 b0' -> 
          eval (csubst b0' 0 b1) res -> 
          P (csubst b0' 0 b1) res -> P (tLetIn na b0 t b1) res) ->
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
          let bctx := case_branch_context ci.(ci_ind) mdecl cdecl p br in
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
        ~~ isApp f ->
        eval f (mkApps (tFix mfix idx) fixargsv) ->
        P f (mkApps (tFix mfix idx) fixargsv) ->
        All2 eval args argsv ->
        All2 P args argsv ->
        cunfold_fix mfix idx = Some (narg, fn) ->
        #|fixargsv| < narg < #|fixargsv| + #|args| ->
        eval (mkApps fn (fixargsv ++ argsv)) res ->
        P (mkApps fn (fixargsv ++ argsv)) res ->
        P (mkApps f args) res) ->
      (forall (f : term) (mfix : mfixpoint term) (idx : nat) (fixargsv args argsv : list term)
              (narg : nat) (fn : term),
          ~~ isApp f ->
          eval f (mkApps (tFix mfix idx) fixargsv) ->
          P f (mkApps (tFix mfix idx) fixargsv) ->
          All2 eval args argsv ->
          All2 P args argsv ->
          cunfold_fix mfix idx = Some (narg, fn) ->
          #|fixargsv ++ argsv| < narg ->
          P (mkApps f args) (mkApps (tFix mfix idx) (fixargsv ++ argsv))) ->
      (forall (ip : case_info) (mfix : mfixpoint term) (idx : nat) 
        (p : predicate term) (args : list term)
        (narg : nat) (fn : term) (brs : list (branch term)) (res : term),
          cunfold_cofix mfix idx = Some (narg, fn) ->
          eval (tCase ip p (mkApps fn args) brs) res ->
          P (tCase ip p (mkApps fn args) brs) res -> P (tCase ip p (mkApps (tCoFix mfix idx) args) brs) res) ->
      (forall (p : projection) (mfix : mfixpoint term) (idx : nat) (args : list term) (narg : nat) (fn res : term),
          cunfold_cofix mfix idx = Some (narg, fn) ->
          eval (tProj p (mkApps fn args)) res ->
          P (tProj p (mkApps fn args)) res -> P (tProj p (mkApps (tCoFix mfix idx) args)) res) ->
      (forall f f' a a',
          ~~ isApp f -> ~~ is_empty a ->
          eval f f' -> P f f' ->
          ~~ (isLambda f' || isFixApp f' || isArityHead f') ->
          All2 eval a a' -> All2 P a a' -> P (tApp f a) (mkApps f' a')) ->
      (forall t : term, atom t -> P t t) -> forall t t0 : term, eval t t0 -> P t t0.
  Proof.
    intros P Hbeta Hlet Hcst Hcase Hproj Hfix Hstuckfix Hcofixcase Hcofixproj Happcong Hatom.
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
        rewrite H0. now eapply Nat.ltb_lt.

    - apply All2_right in X0.
      depelim IHeve.
      destruct t; simpl in * |- *; try congruence.
      eapply value_app; auto.
      eapply value_app; auto.
      rewrite -mkApps_app.
      eapply value_app. auto.
      eapply All_app_inv; auto.
      rewrite -mkApps_app.
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
      destruct (cunfold_fix _ _) as [(? & ?)|] eqn:uf; [|easy].
      eapply Nat.ltb_lt in H.
      eapply (eval_fix_value _ _ _ []); tea => //.
      + now eapply eval_atom.
      + now eapply All_All2.
  Qed.

  Lemma eval_atom_inj t t' : atom t -> eval t t' -> t = t'.
  Proof.
    intros Ha H; depind H; try solve_discr'; try now easy.
    - eapply atom_mkApps in Ha; intuition subst.
      depelim a.
      apply atom_mkApps in H2 as (-> & ?).
      cbn in *. lia.

    - eapply atom_mkApps in Ha; intuition subst.
      depelim a.
      apply atom_mkApps in H1 as (-> & ?).
      cbn in *. reflexivity.
  Qed.

  Derive Signature for eval.
  
  Lemma eval_to_stuck_fix_inv mfix idx narg fn t args :
    cunfold_fix mfix idx = Some (narg, fn) ->
    eval t (mkApps (tFix mfix idx) args) ->
    args = [] \/ #|args| < narg.
  Proof.
    intros uf ev.
    apply eval_to_value in ev.
    apply value_mkApps_inv in ev as [[(-> & ?)|]|]; try easy.
    - unfold isStuckFix in *.
      rewrite uf in p.
      destruct p. eapply Nat.ltb_lt in i. lia.
  Qed.

  Lemma eval_LetIn {n b ty t v} :
    eval (tLetIn n b ty t) v ->
    ∑ b',
      eval b b' * eval (csubst b' 0 t) v.
  Proof.
    intros H; depind H; try solve_discr'; try now easy.
    - depelim a.
      eapply eval_to_stuck_fix_inv in H; [|easy].
      elimtype False. destruct H; subst; cbn in *; lia.

    - depelim a.
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
    - depelim a.
      eapply eval_to_stuck_fix_inv in H; [|easy].
      elimtype False. destruct H; subst; cbn in *; lia.
    - depelim a.
      apply IHeval.
      now rewrite app_nil_r.
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
