(* Distributed under the terms of the MIT license. *)
From Coq Require Import CRelationClasses.
From MetaCoq.Common Require Import config.
From MetaCoq.Utils Require Import utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst
     PCUICUnivSubst PCUICTyping PCUICGlobalEnv PCUICReduction PCUICClosed PCUICCSubst
     PCUICClosedTyp PCUICEtaExpand. (* Due to reliance on wf Σ instead of closed_env Σ *)

Require Import ssreflect ssrbool.
From Equations Require Import Equations.

(** * Weak-head call-by-value evaluation strategy.

  The [wcbveval] inductive relation specifies weak cbv evaluation.  It
  is shown to be a subrelation of the 1-step reduction relation from
  which conversion is defined. Hence two terms that reduce to the same
  wcbv head normal form are convertible.

  This reduction strategy is supposed to mimick at the Coq level the
  reduction strategy of ML programming languages. It is used to state
  the extraction theorem that can be applied to Coq terms to produce
  (untyped) terms where all proofs are erased to a dummy value. *)


Local Ltac inv H := inversion H; subst.

Lemma nApp_mkApps t f args :
  t = mkApps f args -> ~~ isApp t -> t = f /\ args = [].
Proof.
  intros -> napp.
  destruct args using rev_case; cbn in *; solve_discr; try discriminate => //. split => //.
  now rewrite mkApps_app /= in napp.
Qed.

Ltac solve_discr :=
  try progress (prepare_discr; finish_discr; cbn[mkApps] in * );
  try match goal with
    H : mkApps _ _ = mkApps ?f ?l |- _ =>
    eapply mkApps_eq_inj in H as [? ?]; [|easy|easy]; subst; try intuition congruence; try noconf H
  | H : ?t = mkApps ?f ?l |- _ =>
    (change t with (mkApps t []) in H ;
    eapply mkApps_eq_inj in H as [? ?]; [|easy|easy]; subst; try intuition congruence; try noconf H) ||
    (eapply nApp_mkApps in H as [? ?]; [|easy]; subst)
  | H : mkApps ?f ?l = ?t |- _ =>
    change t with (mkApps t []) in H ;
    eapply mkApps_eq_inj in H as [? ?]; [|easy|easy]; subst; try intuition congruence; try noconf H
  end.

(** ** Big step version of weak cbv beta-zeta-iota-fix-delta reduction. *)

Definition atom t :=
  match t with
  | tInd _ _
  | tConstruct _ _ _
  | tFix _ _
  | tCoFix _ _
  | tLambda _ _ _
  | tSort _
  | tProd _ _ _
  | tPrim _ => true
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

Definition isFixApp t := isFix (head t).

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

Definition isConstructApp t := isConstruct (head t).

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

Definition isPrim t :=
  match t with
  | tPrim _ => true
  | _ => false
  end.

Definition isPrimApp t := isPrim (head t).

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

Definition isStuckFix t (args : list term) :=
  match t with
  | tFix mfix idx =>
    match cunfold_fix mfix idx with
    | Some (narg, fn) => #|args| <=? narg
    | None => false
    end
  | _ => false
  end.

Lemma atom_mkApps f l : atom (mkApps f l) -> (l = []) /\ atom f.
Proof.
  revert f; induction l using rev_ind. simpl. intuition auto.
  simpl. intros. now rewrite mkApps_app in H.
Qed.

Global Hint Resolve app_tip_nil : core.

Definition cstr_arity mdecl cdecl :=
  (mdecl.(ind_npars) + context_assumptions cdecl.(cstr_args))%nat.

Lemma nisLambda_mkApps f args : ~~ isLambda f -> ~~ isLambda (mkApps f args).
Proof. destruct args using rev_case => //. rewrite mkApps_app /= //. Qed.

Lemma nisArityHead_mkApps f args : ~~ isArityHead f -> ~~ isArityHead (mkApps f args).
Proof. destruct args using rev_case => //. rewrite mkApps_app /= //. Qed.

Lemma nisPrim_mkApps f args : ~~ isPrim f -> ~~ isPrim (mkApps f args).
Proof. destruct args using rev_case => //. rewrite mkApps_app /= //. Qed.

(* Lemma isLambda_mkApps f args : ~~ isApp f ->
  isLambda f = isLambda (mkApps f args).
Proof. destruct args using rev_case => //. rewrite mkApps_app /= //. Qed. *)

Lemma head_mkApps f args : head (mkApps f args) = head f.
Proof.
  induction args in f |- *; cbn => //.
  now rewrite IHargs head_tapp.
Qed.

Lemma isFixApp_mkApps f args : isFixApp (mkApps f args) = isFixApp f.
Proof.
  now rewrite /isFixApp head_mkApps.
Qed.

Lemma isConstructApp_mkApps f args : isConstructApp (mkApps f args) = isConstructApp f.
Proof.
  now rewrite /isConstructApp head_mkApps.
Qed.

Lemma isPrimApp_mkApps f args : isPrimApp (mkApps f args) = isPrimApp f.
Proof. now rewrite /isPrimApp head_mkApps. Qed.

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

  (** Constant unfolding *)
  | eval_delta c decl body (isdecl : declared_constant_gen (lookup_env Σ) c decl) u res :
      decl.(cst_body) = Some body ->
      eval (subst_instance u body) res ->
      eval (tConst c u) res

  (** Case *)
  | eval_iota ci discr c mdecl idecl cdecl u args p brs br res :
    eval discr (mkApps (tConstruct ci.(ci_ind) c u) args) ->
    nth_error brs c = Some br ->
    declared_constructor_gen (lookup_env Σ) (ci.(ci_ind), c) mdecl idecl cdecl ->
    #|args| = cstr_arity mdecl cdecl ->
    ci.(ci_npar) = mdecl.(ind_npars) ->
    context_assumptions cdecl.(cstr_args) = context_assumptions br.(bcontext) ->
    eval (iota_red ci.(ci_npar) p args br) res ->
    eval (tCase ci p discr brs) res

  (** Proj *)
  | eval_proj p discr args u a res mdecl idecl cdecl pdecl :
      declared_projection_gen (lookup_env Σ) p mdecl idecl cdecl pdecl ->
      eval discr (mkApps (tConstruct p.(proj_ind) 0 u) args) ->
      #|args| = cstr_arity mdecl cdecl ->
      nth_error args (p.(proj_npars) + p.(proj_arg)) = Some a ->
      eval a res ->
      eval (tProj p discr) res

  (** Fix unfolding, with guard *)
  | eval_fix f mfix idx argsv a av fn res :
      eval f (mkApps (tFix mfix idx) argsv) ->
      eval a av ->
      cunfold_fix mfix idx = Some (#|argsv|, fn) ->
      eval (tApp (mkApps fn argsv) av) res ->
      eval (tApp f a) res

  (** Fix stuck, with guard *)
  | eval_fix_value f mfix idx argsv a av narg fn :
      eval f (mkApps (tFix mfix idx) argsv) ->
      eval a av ->
      cunfold_fix mfix idx = Some (narg, fn) ->
      (#|argsv| < narg) ->
      eval (tApp f a) (tApp (mkApps (tFix mfix idx) argsv) av)

  (** CoFix-case unfolding *)
  | eval_cofix_case ip mfix idx p discr args narg fn brs res :
      cunfold_cofix mfix idx = Some (narg, fn) ->
      eval discr (mkApps (tCoFix mfix idx) args) ->
      eval (tCase ip p (mkApps fn args) brs) res ->
      eval (tCase ip p discr brs) res

  (** CoFix-proj unfolding *)
  | eval_cofix_proj p mfix idx discr args narg fn res :
      cunfold_cofix mfix idx = Some (narg, fn) ->
      eval discr (mkApps (tCoFix mfix idx) args) ->
      eval (tProj p (mkApps fn args)) res ->
      eval (tProj p discr) res

  (** Constructor congruence: we do not allow over-applications *)
  | eval_construct ind c u mdecl idecl cdecl f args a a' :
    declared_constructor_gen (lookup_env Σ) (ind, c) mdecl idecl cdecl ->
    eval f (mkApps (tConstruct ind c u) args) ->
    #|args| < cstr_arity mdecl cdecl ->
    eval a a' ->
    eval (tApp f a) (mkApps (tConstruct ind c u) (args ++ [a']))

  (** Non redex-producing heads applied to values are values *)
  | eval_app_cong f f' a a' :
      eval f f' ->
      ~~ (isLambda f' || isFixApp f' || isArityHead f' || isConstructApp f' || isPrimApp f') ->
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
  Derive Signature for eval.

  (** Characterization of values for this reduction relation.
      Only constructors and cofixpoints can accumulate arguments.
      All other values are atoms and cannot have arguments:
      - box
      - abstractions
      - constant constructors
      - unapplied fixpoints and cofixpoints
   *)

   Variant value_head (nargs : nat) : term -> Type :=
   | value_head_cstr ind c u mdecl idecl cdecl :
     declared_constructor_gen (lookup_env Σ) (ind, c) mdecl idecl cdecl ->
     nargs <= cstr_arity mdecl cdecl ->
     value_head nargs (tConstruct ind c u)
   | value_head_ind ind u : value_head nargs (tInd ind u)
   | value_head_cofix mfix idx : value_head nargs (tCoFix mfix idx)
   | value_head_fix mfix idx rarg fn :
     cunfold_fix mfix idx = Some (rarg, fn) ->
     nargs <= rarg ->
     value_head nargs (tFix mfix idx).
   Derive Signature NoConfusion for value_head.

   Inductive value : term -> Type :=
   | value_atom t : atom t -> value t
   | value_app_nonnil f args : value_head #|args| f -> args <> [] -> All value args -> value (mkApps f args).
   Derive Signature for value.

   Lemma value_app f args : value_head #|args| f -> All value args -> value (mkApps f args).
   Proof using Type.
     destruct (args).
     - intros [] hv; now constructor.
     - intros vh av. eapply value_app_nonnil => //.
   Qed.

   Lemma value_values_ind : forall P : term -> Type,
       (forall t, atom t -> P t) ->
       (forall f args, value_head #|args| f -> args <> [] -> All value args -> All P args -> P (mkApps f args)) ->
       forall t : term, value t -> P t.
   Proof.
     intros P ??.
     fix value_values_ind 2. destruct 1.
     - apply X; auto.
     - eapply X0; auto; tea.
       clear v n. revert args a. fix aux 2. destruct 1. constructor; auto.
       constructor. now eapply value_values_ind. now apply aux.
   Defined.

   Lemma value_head_nApp {nargs t} : value_head nargs t -> ~~ isApp t.
   Proof using Type. destruct 1; auto. Qed.
   Hint Resolve value_head_nApp : core.

   Lemma isStuckfix_nApp {t args} : isStuckFix t args -> ~~ isApp t.
   Proof using Type. destruct t; auto. Qed.
   Hint Resolve isStuckfix_nApp : core.

   Lemma atom_nApp {t} : atom t -> ~~ isApp t.
   Proof using Type. destruct t; auto. Qed.
   Hint Resolve atom_nApp : core.

   Lemma value_mkApps_inv t l :
     ~~ isApp t ->
     value (mkApps t l) ->
     ((l = []) × atom t) + ([× l <> [], value_head #|l| t & All value l]).
   Proof using Type.
     intros H H'. generalize_eq x (mkApps t l).
     revert t H. induction H' using value_values_ind.
     intros. subst.
     - now eapply atom_mkApps in H.
     - intros * isapp appeq. move: (value_head_nApp X) => Ht.
       right.
       apply mkApps_eq_inj in appeq => //. intuition subst; auto => //.
   Qed.

   Lemma value_mkApps_values t l :
     value (mkApps t l) ->
     ~~ isApp t ->
     All value l.
   Proof using Type.
     intros val not_app.
     now apply value_mkApps_inv in val as [(-> & ?)|[]].
   Qed.

   (** The codomain of evaluation is only values: *)
   (*     It means no redex can remain at the head of an evaluated term. *)

  (** The codomain of evaluation is only values: *)
  (*     It means no redex can remain at the head of an evaluated term. *)

  Lemma eval_to_value e e' : eval e e' -> value e'.
  Proof using Type.
    intros ev. induction ev; simpl; intros; auto using value.

    - change (tApp ?h ?a) with (mkApps h [a]).
      rewrite -mkApps_app.
      apply value_mkApps_inv in IHev1; [|easy].
      destruct IHev1 as [(-> & _)|[]].
      + apply value_app; auto. len.
        cbn in *. econstructor; tea. cbn; auto.
      + depelim v. rewrite e0 in e. noconf e.
        eapply value_app; auto. econstructor; tea.
          len; lia. apply All_app_inv; auto.

    - apply value_mkApps_inv in IHev1; [|easy].
      destruct IHev1 as [(-> & _)|[]].
      + eapply value_app; cbn; auto. econstructor; tea.
      + eapply value_app; cbn; auto. econstructor; tea. cbn; len.
        eapply All_app_inv; auto.

    - destruct (mkApps_elim f' [a']).
      eapply value_mkApps_inv in IHev1 => //.
      destruct IHev1 as [?|[]]; intuition subst.
      * rewrite a0 /=.
        rewrite a0 in i. simpl in *.
        apply (value_app f0 [a']).
        destruct f0; simpl in * |- *; try congruence.
        all:try solve [repeat constructor; auto].
        auto.
      * rewrite -[tApp _ _](mkApps_app _ (firstn n l) [a']).
        eapply value_app; auto. len.
        rewrite isFixApp_mkApps // isConstructApp_mkApps // in i.
        rewrite !negb_or in i. rtoProp; intuition auto.
        destruct v; cbn in * => //.
        + constructor.
        + constructor.
        + apply All_app_inv; auto.
  Qed.

  Lemma value_head_spec n t :
    value_head n t -> (~~ (isLambda t || isArityHead t)).
  Proof using Type.
    now destruct 1; simpl.
  Qed.

  Lemma value_head_final n t :
    value_head n t -> eval t t.
  Proof using Type.
    destruct 1.
    - now constructor.
    - now eapply eval_atom.
    - now eapply eval_atom.
    - now eapply eval_atom.
  Qed.

  Lemma eval_mkApps_Construct ind c u mdecl idecl cdecl f args args' :
    declared_constructor_gen (lookup_env Σ) (ind, c) mdecl idecl cdecl ->
    eval f (tConstruct ind c u) ->
    #|args| <= cstr_arity mdecl cdecl ->
    All2 eval args args' ->
    eval (mkApps f args) (mkApps (tConstruct ind c u) args').
  Proof using Type.
    intros hdecl evf hargs. revert args'.
    induction args using rev_ind; intros args' evargs.
    - depelim evargs. now cbn.
    - eapply All2_app_inv_l in evargs as [r1 [r2 [-> [evl evr]]]].
      depelim evr. depelim evr.
      rewrite mkApps_app /=. len in hargs. cbn in hargs.
      eapply eval_construct; tea.
      eapply IHargs => //. lia.
      rewrite -(All2_length evl). lia.
  Qed.

  Lemma eval_mkApps_CoFix f mfix idx args args' :
    eval f (tCoFix mfix idx) ->
    All2 eval args args' ->
    eval (mkApps f args) (mkApps (tCoFix mfix idx) args').
  Proof using Type.
    intros evf hargs. revert args' hargs.
    induction args using rev_ind; intros args' evargs.
    - depelim evargs. cbn; auto.
    - eapply All2_app_inv_l in evargs as [r1 [r2 [-> [evl evr]]]].
      depelim evr. depelim evr.
      rewrite !mkApps_app /=.
      eapply eval_app_cong; tea.
      eapply IHargs => //.
      rewrite isFixApp_mkApps // /= isConstructApp_mkApps // !negb_or isPrimApp_mkApps.
      rtoProp; intuition auto.
      apply nisLambda_mkApps => //. apply nisArityHead_mkApps => //.
  Qed.

  Lemma eval_mkApps_tInd f ind u args args' :
    eval f (tInd ind u) ->
    All2 eval args args' ->
    eval (mkApps f args) (mkApps (tInd ind u) args').
  Proof using Type.
    intros evf hargs. revert args' hargs.
    induction args using rev_ind; intros args' evargs.
    - depelim evargs. cbn; auto.
    - eapply All2_app_inv_l in evargs as [r1 [r2 [-> [evl evr]]]].
      depelim evr. depelim evr.
      rewrite !mkApps_app /=.
      eapply eval_app_cong; tea.
      eapply IHargs => //.
      rewrite isFixApp_mkApps // /= isConstructApp_mkApps // !negb_or isPrimApp_mkApps.
      rtoProp; intuition auto.
      apply nisLambda_mkApps => //. apply nisArityHead_mkApps => //.
  Qed.

  Lemma eval_stuck_Fix {f mfix idx args args'} :
    eval f (tFix mfix idx) ->
    All2 eval args args' ->
    isStuckFix (tFix mfix idx) args ->
    eval (mkApps f args) (mkApps (tFix mfix idx) args').
  Proof using Type.
    intros evf hargs. revert args' hargs.
    induction args using rev_ind; intros args' evargs.
    - depelim evargs. cbn; auto.
    - eapply All2_app_inv_l in evargs as [r1 [r2 [-> [evl evr]]]].
      depelim evr. depelim evr.
      rewrite !mkApps_app /=.
      destruct cunfold_fix as [[rarg fn]|] eqn:eqc => //.
      len; cbn. move/Nat.leb_le => hrarg.
      eapply eval_fix_value.
      eapply IHargs => //. unfold isStuckFix. rewrite eqc. apply Nat.leb_le; lia. auto. tea.
      rewrite -(All2_length evl). lia.
  Qed.

  Lemma value_head_antimon {n n' f} : n' <= n -> value_head n f -> value_head n' f.
  Proof using Type.
    intros hn []; econstructor; tea. lia. lia.
  Qed.

  Lemma eval_mkApps_cong f f' l l' :
    eval f f' ->
    value_head #|l| f' ->
    All2 eval l l' ->
    eval (mkApps f l) (mkApps f' l').
  Proof using Type.
    revert l'. induction l using rev_ind; intros l' evf vf' evl.
    depelim evl. eapply evf.
    eapply All2_app_inv_l in evl as (?&?&?&?&?).
    intuition auto. subst. depelim a0. depelim a0.
    - destruct vf'.
      * eapply eval_mkApps_Construct; tea. eapply All2_app; auto.
      * eapply eval_mkApps_tInd; auto. eapply All2_app; auto.
      * eapply eval_mkApps_CoFix; auto. eapply All2_app; auto.
      * eapply eval_stuck_Fix; tea. eapply All2_app; auto.
        unfold isStuckFix; rewrite e0. now apply Nat.leb_le.
  Qed.

  Lemma value_final e : value e -> eval e e.
  Proof using Type.
    induction 1 using value_values_ind; simpl; auto using value.
    - now constructor.
    - assert (All2 eval args args).
      { clear -X1; induction X1; constructor; auto. }
      eapply eval_mkApps_cong => //. now eapply value_head_final.
  Qed.

  Lemma eval_stuck_fix args argsv mfix idx :
    All2 eval args argsv ->
    isStuckFix (tFix mfix idx) argsv ->
    eval (mkApps (tFix mfix idx) args) (mkApps (tFix mfix idx) argsv).
  Proof using Type.
    intros. eapply eval_stuck_Fix; eauto. now constructor.
    move: H. unfold isStuckFix. destruct cunfold_fix as [[rarg fn]|] => //.
    now rewrite (All2_length X).
  Qed.

  Lemma stuck_fix_value_inv argsv mfix idx narg fn :
    value (mkApps (tFix mfix idx) argsv) ->
    cunfold_fix mfix idx = Some (narg, fn) ->
    (All value argsv * isStuckFix (tFix mfix idx) argsv).
  Proof using Type.
    remember (mkApps (tFix mfix idx) argsv) as tfix.
    intros hv; revert Heqtfix.
    induction hv using value_values_ind; intros eq; subst.
    unfold atom in H. destruct argsv using rev_case => //.
    split; auto. simpl. simpl in H. rewrite H0 //.
    rewrite mkApps_app /= // in H.
    solve_discr => //.
    depelim X. rewrite e. intros [= -> ->]. split => //.
    unfold isStuckFix. rewrite e. now apply Nat.leb_le.
  Qed.

  Lemma stuck_fix_value_args argsv mfix idx narg fn :
    value (mkApps (tFix mfix idx) argsv) ->
    cunfold_fix mfix idx = Some (narg, fn) ->
    #|argsv| <= narg.
  Proof using Type.
    intros val unf.
    eapply stuck_fix_value_inv in val; eauto.
    destruct val.
    simpl in i. rewrite unf in i.
    now eapply Nat.leb_le in i.
  Qed.

  Lemma closed_beta na t b u : closed (tLambda na t b) -> closed u -> closed (csubst u 0 b).
  Proof using Type. simpl; move/andP => [ct cb] cu. now eapply closed_csubst. Qed.

  Lemma closed_def `{checker_flags} c decl u b : wf Σ -> declared_constant Σ c decl ->
    cst_body decl = Some b ->
    closed (subst_instance u b).
  Proof using Type.
    move=> wfΣ Hc Hb. unshelve eapply declared_constant_to_gen in Hc; eauto.
    rewrite PCUICClosed.closedn_subst_instance.
    apply declared_decl_closed in Hc => //. simpl in Hc. red in Hc.
    rewrite Hb in Hc. simpl in Hc. now move/andP: Hc.
  Qed.

  Lemma closed_iota ci ind p c u args brs br :
    forallb (test_branch_k p closedn 0) brs ->
    forallb (closedn 0) p.(pparams) ->
    closed (mkApps (tConstruct ind c u) args) ->
    #|args| = (ci.(ci_npar) + context_assumptions br.(bcontext))%nat ->    nth_error brs c = Some br ->
    closed (iota_red (ci_npar ci) p args br).
  Proof using Type.
    unfold iota_red => cbrs cpars cargs hass e.
    solve_all.
    eapply All_nth_error in e; eauto. simpl in e.
    rewrite closedn_mkApps in cargs.
    move/andP: cargs => [Hcons Hargs].
    eapply (closedn_subst _ 0 0).
    now rewrite forallb_rev forallb_skipn //.
    simpl. rewrite List.rev_length /expand_lets /expand_lets_k.
    rewrite -(Nat.add_0_r #|skipn (ci_npar ci) args|).
    rewrite skipn_length hass.
    replace (ci_npar ci + context_assumptions (bcontext br) - ci_npar ci)
    with (context_assumptions (bcontext br)) by lia.
    move/andP: e => [cltx clb].
    have hl : context_assumptions (inst_case_branch_context p br) = context_assumptions (bcontext br).
    { rewrite /inst_case_branch_context. now len. }
    eapply (closedn_subst _ _ 0).
    rewrite -hl.
    eapply closedn_extended_subst => //.
    { rewrite /inst_case_branch_context /inst_case_context.
      eapply (closedn_ctx_subst 0 0); cbn.
      rewrite closedn_subst_instance_context. now len.
      rewrite forallb_rev. solve_all. }
    rewrite extended_subst_length Nat.add_0_r /= Nat.add_comm -hl.
    eapply closedn_lift.
    rewrite inst_case_branch_context_length.
    now rewrite Nat.add_0_r in clb.
  Qed.

  Lemma closed_arg f args n a :
    closed (mkApps f args) ->
    nth_error args n = Some a -> closed a.
  Proof using Type.
    rewrite closedn_mkApps.
    move/andP => [cf cargs].
    solve_all. eapply All_nth_error in cargs; eauto.
  Qed.

  Lemma closed_unfold_fix mfix idx narg fn :
    closed (tFix mfix idx) ->
    unfold_fix mfix idx = Some (narg, fn) -> closed fn.
  Proof using Type.
    unfold unfold_fix. destruct (nth_error mfix idx) eqn:Heq.
    move=> /= Hf Heq'; noconf Heq'.
    eapply closedn_subst0. unfold fix_subst. clear -Hf. generalize #|mfix|.
    induction n; simpl; auto.
    simpl. rewrite fix_subst_length. solve_all.
    eapply All_nth_error in Hf; eauto. unfold test_def in Hf.
    rewrite PeanoNat.Nat.add_0_r in Hf. now move/andP: Hf.
    discriminate.
  Qed.

  Lemma closed_fix_substl_subst_eq {mfix idx d} :
    closed (tFix mfix idx) ->
    nth_error mfix idx = Some d ->
    subst0 (fix_subst mfix) (dbody d) = substl (fix_subst mfix) (dbody d).
  Proof using Type.
    move=> /= Hf; f_equal; f_equal.
    have clfix : All (closedn 0) (fix_subst mfix).
    { clear idx.
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
    intros hnth.
    rewrite -IHfix_subst => //.
    rewrite (subst_app_decomp [_]). simpl.
    f_equal. rewrite lift_closed // closed_subst //.
  Qed.

  Lemma closed_cofix_substl_subst_eq {mfix idx d} :
    closed (tCoFix mfix idx) ->
    nth_error mfix idx = Some d ->
    subst0 (cofix_subst mfix) (dbody d) = substl (cofix_subst mfix) (dbody d).
  Proof using Type.
    move=> /= Hf; f_equal; f_equal.
    have clfix : All (closedn 0) (cofix_subst mfix).
    { clear idx.
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
    intros hnth.
    rewrite -IHcofix_subst => //.
    rewrite (subst_app_decomp [_]). simpl.
    f_equal. rewrite lift_closed // closed_subst //.
  Qed.

  Lemma closed_unfold_fix_cunfold_eq mfix idx :
    closed (tFix mfix idx) ->
    unfold_fix mfix idx = cunfold_fix mfix idx.
  Proof using Type.
    unfold unfold_fix, cunfold_fix.
    destruct (nth_error mfix idx) eqn:Heq => //.
    intros cl; f_equal; f_equal.
    now rewrite (closed_fix_substl_subst_eq cl).
  Qed.

  Lemma closed_unfold_cofix_cunfold_eq mfix idx :
    closed (tCoFix mfix idx) ->
    unfold_cofix mfix idx = cunfold_cofix mfix idx.
  Proof using Type.
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
    rewrite (subst_app_decomp [_]). simpl.
    f_equal. rewrite lift_closed // closed_subst //.
  Qed.

  Lemma closed_unfold_cofix mfix idx narg fn :
    closed (tCoFix mfix idx) ->
    unfold_cofix mfix idx = Some (narg, fn) -> closed fn.
  Proof using Type.
    unfold unfold_cofix. destruct (nth_error mfix idx) eqn:Heq.
    move=> /= Hf Heq'; noconf Heq'.
    eapply closedn_subst0. unfold cofix_subst. clear -Hf. generalize #|mfix|.
    induction n; simpl; auto.
    simpl. rewrite cofix_subst_length. solve_all.
    eapply All_nth_error in Hf; eauto. unfold test_def in Hf.
    rewrite PeanoNat.Nat.add_0_r in Hf. now move/andP: Hf.
    discriminate.
  Qed.

  (** Evaluation preserves closedness: *)
  Lemma eval_closed `{checker_flags} {wfΣ : wf Σ} : forall t u, closed t -> eval t u -> closed u.
  Proof using Type.
    move=> t u Hc ev. move: Hc.
    induction ev; simpl in *; auto;
      (move/andP=> [/andP[Hc Hc'] Hc''] || move/andP=> [Hc Hc'] || move=>Hc); auto.
    - eapply IHev3. unshelve eapply closed_beta. 3:eauto. exact na. simpl. eauto.
    - eapply IHev2. now rewrite closed_csubst.
    - apply IHev. eapply closed_def; eauto.
      apply declared_constant_from_gen; eauto.
    - apply IHev2.
      eapply closed_iota; tea.
      move/andP: Hc => [] /andP [] //.
      now eapply IHev1. rewrite e1.
      now rewrite -e2.
    - eapply IHev2.
      specialize (IHev1 Hc).
      rewrite closedn_mkApps in IHev1.
      move/andP: IHev1 => [Hcons Hargs]. solve_all.
      eapply All_nth_error in Hargs; eauto.
    - eapply IHev3.
      apply/andP.
      split; [|easy].
      specialize (IHev1 Hc).
      rewrite closedn_mkApps in IHev1.
      move/andP: IHev1 => [clfix clargs].
      rewrite closedn_mkApps clargs andb_true_r.
      eapply closed_unfold_fix; [easy|].
      now rewrite closed_unfold_fix_cunfold_eq.
    - apply andb_true_iff.
      split; [|easy].
      solve_all.
    - eapply IHev2. solve_all. rewrite !closedn_mkApps in H0 |- *. solve_all.
      rewrite -closed_unfold_cofix_cunfold_eq in e => //.
      eapply closed_unfold_cofix in e; eauto.
    - eapply IHev2. solve_all. rewrite !closedn_mkApps in H0 |- *. solve_all.
      rewrite -closed_unfold_cofix_cunfold_eq in e => //.
      eapply closed_unfold_cofix in e; eauto.
    - rewrite closedn_mkApps /=. specialize (IHev1 Hc). specialize (IHev2 Hc').
      move: IHev1. rewrite closedn_mkApps /= forallb_app => -> /=. now rewrite IHev2.
    - apply/andP; split; auto.
  Qed.

  (* TODO MOVE *)
  Lemma nApp_isApp_false :
    forall u,
      nApp u = 0 ->
      isApp u = false.
  Proof using Type.
    intros u e.
    destruct u. all: simpl. all: try reflexivity.
    discriminate.
  Qed.

  Lemma eval_tRel n t :
    eval (tRel n) t -> False.
  Proof using Type. now intros e; depelim e. Qed.

  Lemma eval_tVar i t : eval (tVar i) t -> False.
  Proof using Type. now intros e; depelim e. Qed.

  Lemma eval_tEvar n l t : eval (tEvar n l) t -> False.
  Proof using Type. now intros e; depelim e. Qed.

  Lemma eval_mkApps_tCoFix mfix idx args v :
    eval (mkApps (tCoFix mfix idx) args)  v ->
    exists args', v = mkApps (tCoFix mfix idx) args'.
  Proof using Type.
    revert v.
    induction args using List.rev_ind; intros v ev.
    + exists [].
      now depelim ev.
    + rewrite mkApps_app in ev.
      cbn in *.
      depelim ev;
        try solve [apply IHargs in ev1 as (? & ?); solve_discr].
      * apply IHargs in ev1 as (argsv & ->).
        exists (argsv ++ [a']).
        now rewrite mkApps_app.
      * easy.
  Qed.

  Set Equations With UIP.

  Scheme Induction for le Sort Prop.

  Lemma le_irrel n m (p q : n <= m) : p = q.
  Proof using Type.
    revert q.
    now induction p using le_ind_dep; intros q; depelim q.
  Qed.

  Instance branch_UIP : UIP (branch term).
  Proof using Type.
    eapply EqDec.eqdec_uip; tc.
  Qed.

  Instance option_UIP {A} (u : EqDec A) : UIP (option A).
  Proof using Type.
    eapply EqDec.eqdec_uip; tc.
    eqdec_proof.
  Qed.

  Lemma declared_constructor_unique {ind mdecl idecl cdecl} (d d' : declared_constructor_gen (lookup_env Σ) ind mdecl idecl cdecl) : d = d'.
  Proof using Type.
    destruct d, d'.
    destruct d, d0.
    assert (d0 = d) as -> by apply uip.
    assert (e1 = e2) as -> by now apply uip.
    assert (e = e0) as -> by now apply uip.
    reflexivity.
  Qed.

  Lemma declared_projection_unique {ind mdecl idecl cdecl pdecl}
     (d d' : declared_projection_gen (lookup_env Σ) ind mdecl idecl cdecl pdecl) : d = d'.
  Proof using Type.
    destruct d, d'.
    rewrite (declared_constructor_unique d d0).
    destruct a, a0.
    assert (e = e1) as -> by now apply uip.
    assert (e0 = e2) as -> by now apply uip.
    reflexivity.
  Qed.

  Unset SsrRewrite.
  Lemma eval_unique_sig {t v v'} :
    forall (ev1 : eval t v) (ev2 : eval t v'),
      {| pr1 := v; pr2 := ev1 |} = {| pr1 := v'; pr2 := ev2 |}.
  Proof using Type.
    Local Ltac go :=
      solve [
          repeat
            match goal with
            | [H: _, H' : _ |- _] =>
              specialize (H _ H');
              try solve [apply (f_equal pr1) in H; cbn in *; solve_discr];
              noconf H
            end; easy].
    intros ev.
    revert v'.
    depind ev; intros v' ev'.
    - depelim ev'; go.
    - depelim ev'; go.
    - depelim ev'; try go.
      pose proof (declared_constant_inj _ _ isdecl isdecl0) as <-.
      assert (body0 = body) as -> by congruence.
      assert (e0 = e) as -> by now apply uip.
      assert (isdecl0 = isdecl) as -> by now apply uip.
      now specialize (IHev _ ev'); noconf IHev.
    - depelim ev'; try go.
      + specialize (IHev1 _ ev'1).
        apply (f_equal pr1) in IHev1 as apps_eq; cbn in *.
        apply mkApps_eq_inj in apps_eq as (eq1 & eq2); try easy.
        noconf eq1. noconf eq2. noconf IHev1.
        epose proof (declared_constructor_inj d d0) as [-> [-> <-]].
        pose proof e3. rewrite e in H. noconf H.
        specialize (IHev2 _ ev'2). noconf IHev2.
        assert (e = e3) as -> by now apply uip.
        assert (d = d0) as -> by apply declared_constructor_unique.
        assert (e0 = e4) as -> by now apply uip.
        assert (e1 = e5) as -> by now apply uip.
        assert (e2 = e6) as -> by now apply uip.
        reflexivity.
    - depelim ev'; try go.
      + specialize (IHev1 _ ev'1); noconf IHev1.
        apply (f_equal pr1) in IHev1 as apps_eq; cbn in *.
        apply mkApps_eq_inj in apps_eq as (eq1 & eq2); try easy.
        noconf eq1. noconf eq2. noconf IHev1.
        pose proof (declared_projection_inj d d0) as [? [? []]].
        subst mdecl0 idecl0 cdecl0 pdecl0.
        assert (d = d0) as -> by apply declared_projection_unique.
        pose proof e2. rewrite e0 in H. noconf H.
        specialize (IHev2 _ ev'2); noconf IHev2.
        assert (e = e1) as -> by now apply uip.
        assert (e0 = e2) as -> by now apply uip.
        reflexivity.
    - depelim ev'; try go.
      + specialize (IHev1 _ ev'1).
        pose proof (mkApps_eq_inj (f_equal pr1 IHev1) eq_refl eq_refl) as (? & <-).
        noconf H.
        noconf IHev1.
        specialize (IHev2 _ ev'2); noconf IHev2.
        pose proof e.
        rewrite e0 in H. noconf H.
        assert (e0 = e) as -> by now apply uip.
        specialize (IHev3 _ ev'3).
        now noconf IHev3.
      + specialize (IHev1 _ ev'1).
        pose proof (mkApps_eq_inj (f_equal pr1 IHev1) eq_refl eq_refl) as (? & <-).
        noconf H. noconf IHev1.
        elimtype False. rewrite e in e0. noconf e0. lia.
      + specialize (IHev1 _ ev'1). noconf IHev1.
        exfalso.
        rewrite isFixApp_mkApps in i; try easy.
        cbn in *.
        now rewrite Bool.orb_true_r in i.
    - depelim ev'; try go.
      + specialize (IHev1 _ ev'1).
        pose proof (mkApps_eq_inj (f_equal pr1 IHev1) eq_refl eq_refl) as (? & <-).
        noconf H.
        exfalso; rewrite e0 in e.
        noconf e.
        lia.
      + specialize (IHev1 _ ev'1).
        pose proof (mkApps_eq_inj (f_equal pr1 IHev1) eq_refl eq_refl) as (? & <-).
        noconf H.
        noconf IHev1.
        specialize (IHev2 _ ev'2); noconf IHev2.
        assert (narg0 = narg) as -> by congruence.
        assert (fn0 = fn) as -> by congruence.
        assert (e0 = e) as -> by now apply uip.
        now assert (l0 = l) as -> by now apply le_irrel.
      + specialize (IHev1 _ ev'1).
        noconf IHev1.
        exfalso.
        rewrite isFixApp_mkApps in i; try easy.
        cbn in *.
        now rewrite Bool.orb_true_r in i.
    - depelim ev'; try go.
      specialize (IHev1 _ ev'1).
      pose proof (mkApps_eq_inj (f_equal pr1 IHev1) eq_refl eq_refl) as (? & <-).
      noconf H. noconf IHev1.
      assert (narg0 = narg) as -> by congruence.
      assert (fn0 = fn) as -> by congruence.
      specialize (IHev2 _ ev'2); noconf IHev2.
      now assert (e0 = e) as -> by now apply uip.
    - depelim ev'; try go.
      specialize (IHev1 _ ev'1).
      pose proof (mkApps_eq_inj (f_equal pr1 IHev1) eq_refl eq_refl) as (? & <-).
      noconf H. noconf IHev1.
      assert (narg0 = narg) as -> by congruence.
      assert (fn0 = fn) as -> by congruence.
      specialize (IHev2 _ ev'2); noconf IHev2.
      now assert (e0 = e) as -> by now apply uip.
    - depelim ev'; try go.
      * specialize (IHev1 _ ev'1); noconf IHev1.
        specialize (IHev2 _ ev'2). noconf IHev2.
        pose proof (mkApps_eq_inj (f_equal pr1 IHev1) eq_refl eq_refl) as (? & <-). noconf H.
        noconf IHev1.
        epose proof (declared_constructor_inj d d0) as [-> [-> <-]].
        assert (d = d0) as -> by apply declared_constructor_unique.
        assert (l = l0) as -> by now apply le_irrel. reflexivity.
      * specialize (IHev1 _ ev'1); noconf IHev1.
        specialize (IHev2 _ ev'2). noconf IHev2.
        elimtype False. rewrite isConstructApp_mkApps in i; auto.
        cbn in i. rewrite !negb_or in i; rtoProp; intuition auto.
    - depelim ev'; try go.
      + specialize (IHev1 _ ev'1); noconf IHev1.
        exfalso.
        rewrite isFixApp_mkApps in i; try easy.
        cbn in *.
        now rewrite Bool.orb_true_r in i.
      + specialize (IHev1 _ ev'1); noconf IHev1.
        exfalso.
        rewrite isFixApp_mkApps in i; try easy.
        cbn in *.
        now rewrite Bool.orb_true_r in i.
      + specialize (IHev1 _ ev'1); noconf IHev1.
        specialize (IHev2 _ ev'2); noconf IHev2.
        elimtype False.
        rewrite isConstructApp_mkApps in i; auto.
        cbn in i. rewrite !negb_or in i; rtoProp; intuition auto.
      + specialize (IHev1 _ ev'1); noconf IHev1.
        specialize (IHev2 _ ev'2); noconf IHev2.
        now assert (i0 = i) as -> by now apply uip.
    - depelim ev'; try go.
      now assert (i0 = i) as -> by now apply uip.
  Qed.

  Lemma eval_deterministic {t v v'} :
    eval t v ->
    eval t v' ->
    v = v'.
  Proof using Type.
    intros ev ev'.
    pose proof (eval_unique_sig ev ev').
    now noconf H.
  Qed.

  Lemma eval_unique {t v} :
    forall (ev1 : eval t v) (ev2 : eval t v),
      ev1 = ev2.
  Proof using Type.
    intros ev ev'.
    pose proof (eval_unique_sig ev ev').
    now noconf H.
  Qed.

  Set SsrRewrite.

  Lemma eval_LetIn {n b ty t v} :
    eval (tLetIn n b ty t) v ->
    ∑ b',
      eval b b' * eval (csubst b' 0 t) v.
  Proof using Type. now intros H; depelim H. Qed.

  Lemma eval_Const {c u v} :
    eval (tConst c u) v ->
    ∑ decl, declared_constant Σ c decl *
                 match cst_body decl with
                 | Some body => eval (subst_instance u body) v
                 | None => False
                 end.
  Proof using Type.
    intros H; depelim H.
    - exists decl. apply declared_constant_from_gen in isdecl.
      split; [easy|].
      now rewrite e.
    - easy.
  Qed.

End Wcbv.

Arguments eval_unique_sig {_ _ _ _}.
Arguments eval_deterministic {_ _ _ _}.
Arguments eval_unique {_ _ _}.

Reserved Notation " Σ ⊢ t ⇝ᵥ u " (at level 50, t, u at next level).

Local Open Scope type_scope.

Inductive wcbv_red1 (Σ: global_env) : term -> term -> Type :=
| wcbv_red_app_left a a' b :
  Σ ⊢ a ⇝ᵥ a' -> Σ ⊢ tApp a b ⇝ᵥ tApp a' b
| wcbv_red_app_right a b b' :
  value Σ a -> Σ ⊢ b ⇝ᵥ b' -> Σ ⊢ tApp a b ⇝ᵥ tApp a b'
| wcbv_red_beta na t b a :
  value Σ a -> Σ ⊢ tApp (tLambda na t b) a ⇝ᵥ csubst a 0 b
| wcbv_red_let_in b0 b0' na t b1 :
  Σ ⊢ b0 ⇝ᵥ b0' -> Σ ⊢ tLetIn na b0 t b1 ⇝ᵥ tLetIn na b0' t b1
| wcbv_red_zeta b0 na t b1 :
  value Σ b0 -> Σ ⊢ tLetIn na b0 t b1 ⇝ᵥ csubst b0 0 b1
| wcbv_red_delta decl body c u (isdecl : declared_constant Σ c decl) :
   decl.(cst_body) = Some body ->
  Σ ⊢ tConst c u ⇝ᵥ subst_instance u body
| wcbv_red_case_in ci p discr discr' brs :
  Σ ⊢ discr ⇝ᵥ discr' -> Σ ⊢ tCase ci p discr brs ⇝ᵥ tCase ci p discr' brs
| wcbv_red_iota ci c mdecl idecl cdecl u args p brs br :
  nth_error brs c = Some br ->
  declared_constructor Σ (ci.(ci_ind), c) mdecl idecl cdecl ->
  #|args| = cstr_arity mdecl cdecl ->
  ci.(ci_npar) = mdecl.(ind_npars) ->
  context_assumptions (cdecl.(cstr_args)) = context_assumptions br.(bcontext) ->
  All (value Σ) args ->
  Σ ⊢ tCase ci p (mkApps (tConstruct ci.(ci_ind) c u) args) brs ⇝ᵥ iota_red ci.(ci_npar) p args br
| wcbv_red_proj_in discr discr' p :
  Σ ⊢ discr ⇝ᵥ discr' -> Σ ⊢ tProj p discr ⇝ᵥ tProj p discr'
| wcbv_red_proj p args u a mdecl idecl cdecl pdecl :
  declared_projection_gen (lookup_env Σ) p mdecl idecl cdecl pdecl ->
  #|args| = cstr_arity mdecl cdecl ->
  nth_error args (p.(proj_npars) + p.(proj_arg)) = Some a ->
  All (value Σ) args ->
  Σ ⊢ tProj p (mkApps (tConstruct p.(proj_ind) 0 u) args) ⇝ᵥ a
| wcbv_red_fix mfix idx argsv a fn :
  All (value Σ) argsv ->
  value Σ a ->
  unfold_fix mfix idx = Some (#|argsv|, fn) ->
  isConstruct_app a = true ->
  Σ ⊢ tApp ((mkApps (tFix mfix idx) argsv)) a ⇝ᵥ tApp (mkApps fn argsv) a
| wcbv_red_cofix_proj : forall (p : projection) (mfix : mfixpoint term)
                     (idx : nat) (args : list term)
                     (narg : nat) (fn : term),
                   cunfold_cofix mfix idx = Some (narg, fn) ->
                   All (value Σ) args ->
                   Σ ⊢ tProj p (mkApps (tCoFix mfix idx) args) ⇝ᵥ tProj p (mkApps fn args)
| wcbv_red_cofix_case : forall (ip : case_info) (mfix : mfixpoint term)
                     (idx : nat) (p : predicate term)
                     (args : list term) (narg : nat)
                     (fn : term) (brs : list (branch term)),
                   cunfold_cofix mfix idx = Some (narg, fn) ->
                   All (value Σ) args ->
                   Σ ⊢ tCase ip p (mkApps (tCoFix mfix idx) args) brs ⇝ᵥ tCase ip p (mkApps fn args) brs
where " Σ ⊢ t ⇝ᵥ u " := (wcbv_red1 Σ t u).


Lemma wcbv_red1_closed {cf : checker_flags} {Σ t t'} :
  wf Σ ->
  closed t -> Σ ⊢ t ⇝ᵥ t' -> closed t'.
Proof.
  intros Hwf Hcl Hred. induction Hred; cbn in *; solve_all.
  all: eauto using closed_csubst, closed_def.
  - eapply closed_iota; eauto. solve_all. unfold test_predicate_k in H. solve_all.
    now rewrite e0 /cstr_arity -e1 -e2.
  - eauto using closed_arg.
  - rewrite !closedn_mkApps in H |- *. solve_all.
    eapply closed_unfold_fix; tea.
  - rewrite !closedn_mkApps in Hcl |- *. solve_all.
    unfold cunfold_cofix in e. destruct nth_error as [d | ] eqn:E; inversion e.
    eapply closed_unfold_cofix with (narg := narg); eauto.
    unfold unfold_cofix. rewrite E. subst. repeat f_equal.
    eapply closed_cofix_substl_subst_eq; eauto.
  - rewrite !closedn_mkApps in H1 |- *. solve_all.
    unfold cunfold_cofix in e. destruct nth_error as [d | ] eqn:E; inversion e.
    eapply closed_unfold_cofix with (narg := narg); eauto.
    unfold unfold_cofix. rewrite E. subst. repeat f_equal.
    eapply closed_cofix_substl_subst_eq; eauto.
Qed.

Lemma wcbv_red1_red1 {cf : checker_flags} {Σ t t' } :
  closed t ->
  Σ ⊢ t ⇝ᵥ t' -> Σ ;;; [] |- t ⇝ t'.
Proof.
  intros Hcl Hred.
  induction Hred. all: cbn in *; solve_all.
  1-10: try econstructor; eauto using wcbv_red1_closed.
  1,2: now rewrite closed_subst; eauto; econstructor; eauto.
  - now rewrite e0 /cstr_arity -e1 -e2.
  - rewrite !tApp_mkApps -!mkApps_app. econstructor. eauto.
    unfold is_constructor. now rewrite nth_error_app2 // Nat.sub_diag.
  - unfold cunfold_cofix in e. destruct nth_error as [d | ] eqn:E; try congruence.
    inversion e; subst.
    econstructor. unfold unfold_cofix. rewrite E. repeat f_equal.
    eapply closed_cofix_substl_subst_eq; eauto. rewrite closedn_mkApps in Hcl. solve_all.
  - unfold cunfold_cofix in e. destruct nth_error as [d | ] eqn:E; try congruence.
    inversion e; subst.
    econstructor. unfold unfold_cofix. rewrite E. repeat f_equal.
    eapply closed_cofix_substl_subst_eq; eauto. rewrite closedn_mkApps in H1. solve_all.
Qed.


Global Hint Constructors value eval : wcbv.
Global Hint Resolve value_final : wcbv.

Lemma wcbv_red1_eval {cf : checker_flags} {Σ : global_env_ext } t t' v : wf Σ ->
  closed t ->
  Σ ⊢ t ⇝ᵥ t' -> eval Σ t' v -> eval Σ t v.
Proof.
  intros Hwf Hty Hred Heval.
  induction Hred in Heval, v, Hty |- *; eauto with wcbv.
  - inversion Heval; subst; clear Heval. all:cbn in Hty; solve_all. 1-3,6:now econstructor; eauto with wcbv.
    eapply eval_construct; tea. eauto. eapply eval_app_cong; eauto with wcbv.
  - inversion Heval; subst; clear Heval. all:cbn in Hty; solve_all. 1-3,6: now econstructor; eauto with wcbv.
    eapply eval_construct; tea. eauto. eapply eval_app_cong; eauto with wcbv.
  - inversion Heval; subst; clear Heval. all:cbn in Hty; solve_all. all: now econstructor; eauto with wcbv.
  - unshelve eapply declared_constant_to_gen in isdecl; eauto.
    inversion Heval; subst. all:cbn in Hty; solve_all. all: try now econstructor; eauto with wcbv.
  - inversion Heval; subst. all:cbn in Hty; solve_all. all: try now econstructor; eauto with wcbv.
  - eapply eval_iota. eapply eval_mkApps_Construct; tea.
    unshelve eapply declared_constructor_to_gen; eauto.
    now econstructor. unfold cstr_arity. rewrite e0.
    rewrite (PCUICGlobalEnv.declared_minductive_ind_npars d).
    now rewrite -(declared_minductive_ind_npars d) /cstr_arity.
    all:tea. eapply All_All2_refl. solve_all. now eapply value_final.
    unshelve eapply declared_constructor_to_gen; eauto.
  - inversion Heval; subst; clear Heval. all:cbn in Hty; solve_all. all: now econstructor; eauto with wcbv.
  - all:cbn in Hty; solve_all. eapply eval_proj; tea.
    eapply value_final. eapply value_app; auto. econstructor; tea. eapply d.
    rewrite e; lia.
  - eapply eval_fix; eauto.
    + eapply value_final. eapply value_app; auto. econstructor.
      rewrite <- closed_unfold_fix_cunfold_eq, e. reflexivity. 2:eauto.
      cbn in Hty. rewrite closedn_mkApps in Hty. solve_all.
    + eapply value_final; eauto.
    + rewrite <- closed_unfold_fix_cunfold_eq, e. reflexivity.
      cbn in Hty. rewrite closedn_mkApps in Hty. solve_all.
      Unshelve. all: now econstructor.
  - destruct p as [[] ?]. eapply eval_cofix_proj; tea.
    eapply value_final, value_app. now constructor. auto.
  - eapply eval_cofix_case; tea.
    eapply value_final, value_app. now constructor. auto.
Qed.

Lemma expanded_tApp (Σ : global_env) (Γ : list nat) (f : term) a :
  expanded Σ Γ f -> expanded Σ Γ a ->
  expanded Σ Γ (tApp f a).
Proof.
  induction 1 using expanded_ind; intros expa.
  all:rewrite -?[tApp _ a](mkApps_app _ _ [a]).
  all:try (eapply (expanded_mkApps _ _ _ [a]) => //; econstructor; eauto).

  - econstructor; tea. rewrite app_length. lia. eapply app_Forall;eauto.
  - econstructor; tea. eapply app_Forall; eauto.
  - eapply expanded_tFix; tea. eapply app_Forall; eauto. eauto. rewrite app_length; cbn; eauto. lia.
  - eapply expanded_tConstruct_app; tea. rewrite app_length ; lia. eapply app_Forall; eauto.
Qed.

Lemma expanded_mkApps (Σ : global_env) (Γ : list nat) (f : term) (args : list term) :
  expanded Σ Γ f -> Forall (expanded Σ Γ) args -> expanded Σ Γ (mkApps f args).
Proof.
  intros expf expa; induction expa in f, expf |- *; eauto.
  cbn. eapply IHexpa. now eapply expanded_tApp.
Qed.

Lemma expanded_tApp_inv Σ Γ f a :
  ~ isConstructApp f || isFixApp f || isRel (head f) ->
  expanded Σ Γ (tApp f a) ->
  expanded Σ Γ f /\ expanded Σ Γ a.
Proof.
  rewrite /isConstructApp /isFixApp.
  intros hf exp; depind exp.
  - destruct args using rev_case; solve_discr; try discriminate.
    rewrite mkApps_app in H3; noconf H3.
    eapply Forall_app in H1 as [? ha]. depelim ha.
    destruct args using rev_case; cbn in hf => //.
    now rewrite !head_mkApps /= in hf.
  - destruct args using rev_case; solve_discr. subst f6.
    eapply IHexp => //.
    rewrite mkApps_app in H2; noconf H2.
    eapply Forall_app in H0 as [? H0]. depelim H0. split => //.
    rewrite !head_mkApps in hf.
    eapply expanded_mkApps => //.
  - destruct args using rev_case; solve_discr. discriminate.
    rewrite mkApps_app in H6; noconf H6.
    eapply Forall_app in H1 as [? h]. depelim h. split => //.
    now rewrite !head_mkApps /= in hf.
  - destruct args using rev_case; solve_discr. discriminate.
    rewrite mkApps_app in H3; noconf H3.
    now rewrite !head_mkApps /= in hf.
Qed.

Lemma expanded_tLambda_inv Σ Γ na t b :
  expanded Σ Γ (tLambda na t b) ->
  expanded Σ (0 :: Γ) b.
Proof.
  intros exp; depind exp; solve_discr => //; eauto.
Qed.

Lemma expanded_tLetIn_inv Σ Γ na t t' b :
  expanded Σ Γ (tLetIn na t t' b) ->
  expanded Σ Γ t /\ expanded Σ (0 :: Γ) b.
Proof.
  intros exp; depind exp; solve_discr => //; eauto.
Qed.

Lemma expanded_tEvar_inv Σ Γ ev l:
  expanded Σ Γ (tEvar ev l) ->
  Forall (expanded Σ Γ) l.
Proof.
  intros exp; depind exp; solve_discr => //; eauto.
Qed.

Lemma expanded_tCase_inv Σ Γ ci p c brs :
  expanded Σ Γ (tCase ci p c brs) ->
  Forall (expanded Σ Γ) (pparams p) /\
  Forall
    (fun br : branch term =>
     ∥ All_fold
         (fun (Δ : list context_decl) (d : context_decl)
          =>
          ForOption
            (fun b : term =>
             expanded Σ
               (repeat 0 #|Δ| ++
                repeat 0 #|pparams p|) b)
            (decl_body d)) (bcontext br) ∥ /\
     expanded Σ (repeat 0 #|bcontext br| ++ Γ) (bbody br))
    brs /\
  expanded Σ Γ c.
Proof.
  intros exp; depind exp; solve_discr => //; eauto.
Qed.

Lemma expanded_tProj_inv Σ Γ p c :
  expanded Σ Γ (tProj p c) ->
  expanded Σ Γ c.
Proof.
  intros exp; depind exp; solve_discr => //; eauto.
Qed.

Lemma expanded_tCoFix_inv Σ Γ mfix idx :
 expanded Σ Γ (tCoFix mfix idx) ->
 Forall (fun d : def term => expanded Σ (repeat 0 #|mfix| ++ Γ) (dbody d)) mfix.
Proof.
  intros exp; depind exp; solve_discr => //; eauto.
Qed.

Import PCUICOnOne.

Module Red1Apps.


  Inductive red1 (Σ : global_env) (Γ : context) : term -> term -> Type :=
  (** Reductions *)
  (** Beta *)
  | red_beta na t b a ts :
    Σ ;;; Γ |- mkApps (tLambda na t b) (a :: ts) ⇝ mkApps (b {0 := a}) ts

  (** Let *)
  | red_zeta na b t b' :
    Σ ;;; Γ |- tLetIn na b t b' ⇝ b' {0 := b}

  | red_rel i body :
      option_map decl_body (nth_error Γ i) = Some (Some body) ->
      Σ ;;; Γ |- tRel i ⇝ lift0 (S i) body

  (** Case *)
  | red_iota ci c u args p brs br :
      nth_error brs c = Some br ->
      #|args| = (ci.(ci_npar) + context_assumptions br.(bcontext))%nat ->
      Σ ;;; Γ |- tCase ci p (mkApps (tConstruct ci.(ci_ind) c u) args) brs
          ⇝ iota_red ci.(ci_npar) p args br

  (** Fix unfolding, with guard *)
  | red_fix mfix idx args narg fn :
      unfold_fix mfix idx = Some (narg, fn) ->
      is_constructor narg args = true ->
      Σ ;;; Γ |- mkApps (tFix mfix idx) args ⇝ mkApps fn args

  (** CoFix-case unfolding *)
  | red_cofix_case ip p mfix idx args narg fn brs :
      unfold_cofix mfix idx = Some (narg, fn) ->
      Σ ;;; Γ |- tCase ip p (mkApps (tCoFix mfix idx) args) brs ⇝
          tCase ip p (mkApps fn args) brs

  (** CoFix-proj unfolding *)
  | red_cofix_proj p mfix idx args narg fn :
      unfold_cofix mfix idx = Some (narg, fn) ->
      Σ ;;; Γ |- tProj p (mkApps (tCoFix mfix idx) args) ⇝ tProj p (mkApps fn args)

  (** Constant unfolding *)
  | red_delta c decl body (isdecl : declared_constant Σ c decl) u :
      decl.(cst_body) = Some body ->
      Σ ;;; Γ |- tConst c u ⇝ subst_instance u body

  (** Proj *)
  | red_proj p args u arg:
      nth_error args (p.(proj_npars) + p.(proj_arg)) = Some arg ->
      Σ ;;; Γ |- tProj p (mkApps (tConstruct p.(proj_ind) 0 u) args) ⇝ arg


  | abs_red_l na M M' N : Σ ;;; Γ |- M ⇝ M' -> Σ ;;; Γ |- tLambda na M N ⇝ tLambda na M' N
  | abs_red_r na M M' N : Σ ;;; Γ ,, vass na N |- M ⇝ M' -> Σ ;;; Γ |- tLambda na N M ⇝ tLambda na N M'

  | letin_red_def na b t b' r : Σ ;;; Γ |- b ⇝ r -> Σ ;;; Γ |- tLetIn na b t b' ⇝ tLetIn na r t b'
  | letin_red_ty na b t b' r : Σ ;;; Γ |- t ⇝ r -> Σ ;;; Γ |- tLetIn na b t b' ⇝ tLetIn na b r b'
  | letin_red_body na b t b' r : Σ ;;; Γ ,, vdef na b t |- b' ⇝ r -> Σ ;;; Γ |- tLetIn na b t b' ⇝ tLetIn na b t r

  | case_red_param ci p params' c brs :
      OnOne2 (fun t u => Σ ;;; Γ |- t ⇝ u) p.(pparams) params' ->
      Σ ;;; Γ |- tCase ci p c brs ⇝ tCase ci (set_pparams p params') c brs

  | case_red_return ci p preturn' c brs :
    Σ ;;; Γ ,,, inst_case_predicate_context p |- p.(preturn) ⇝ preturn' ->
    Σ ;;; Γ |- tCase ci p c brs ⇝ tCase ci (set_preturn p preturn') c brs

  | case_red_discr ci p c c' brs :
    Σ ;;; Γ |- c ⇝ c' -> Σ ;;; Γ |- tCase ci p c brs ⇝ tCase ci p c' brs

  | case_red_brs ci p c brs brs' :
      OnOne2 (fun br br' =>
        on_Trel_eq (fun t u => Σ ;;; Γ ,,, inst_case_branch_context p br |- t ⇝ u) bbody bcontext br br')
        brs brs' ->
      Σ ;;; Γ |- tCase ci p c brs ⇝ tCase ci p c brs'

  | proj_red p c c' : Σ ;;; Γ |- c ⇝ c' -> Σ ;;; Γ |- tProj p c ⇝ tProj p c'

  | app_red_l M1 N1 M2 : Σ ;;; Γ |- M1 ⇝ N1 -> ~~ isApp M1 -> ~~ isFix M1 -> M2 <> nil ->
    Σ ;;; Γ |- mkApps M1 M2 ⇝ mkApps N1 M2

  | app_red_r M2 N2 M1 : ~~ isApp M1 -> OnOne2 (fun M2 N2 => Σ ;;; Γ |- M2 ⇝ N2) M2 N2 -> Σ ;;; Γ |- mkApps M1 M2 ⇝ mkApps M1 N2

  | app_fix_red_ty mfix0 mfix1 idx M2 :
    OnOne2 (on_Trel_eq (fun t u => Σ ;;; Γ |- t ⇝ u) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
    Σ ;;; Γ |- mkApps (tFix mfix0 idx) M2 ⇝ mkApps (tFix mfix1 idx) M2

  | app_fix_red_body mfix0 mfix1 idx M2 :
    OnOne2 (on_Trel_eq (fun t u => Σ ;;; Γ ,,, fix_context mfix0 |- t ⇝ u) dbody (fun x => (dname x, dtype x, rarg x))) mfix0 mfix1 ->
    Σ ;;; Γ |- mkApps (tFix mfix0 idx) M2 ⇝ mkApps (tFix mfix1 idx) M2

  | prod_red_l na M1 M2 N1 : Σ ;;; Γ |- M1 ⇝ N1 -> Σ ;;; Γ |- tProd na M1 M2 ⇝ tProd na N1 M2
  | prod_red_r na M2 N2 M1 : Σ ;;; Γ ,, vass na M1 |- M2 ⇝ N2 ->
                            Σ ;;; Γ |- tProd na M1 M2 ⇝ tProd na M1 N2

  | evar_red ev l l' : OnOne2 (fun t u => Σ ;;; Γ |- t ⇝ u) l l' -> Σ ;;; Γ |- tEvar ev l ⇝ tEvar ev l'

  | fix_red_ty mfix0 mfix1 idx :
      OnOne2 (on_Trel_eq (fun t u => Σ ;;; Γ |- t ⇝ u) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
      Σ ;;; Γ |- tFix mfix0 idx ⇝ tFix mfix1 idx

  | fix_red_body mfix0 mfix1 idx :
      OnOne2 (on_Trel_eq (fun t u => Σ ;;; Γ ,,, fix_context mfix0 |- t ⇝ u) dbody (fun x => (dname x, dtype x, rarg x)))
            mfix0 mfix1 ->
      Σ ;;; Γ |- tFix mfix0 idx ⇝ tFix mfix1 idx

  | cofix_red_ty mfix0 mfix1 idx :
      OnOne2 (on_Trel_eq (fun t u => Σ ;;; Γ |- t ⇝ u) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
      Σ ;;; Γ |- tCoFix mfix0 idx ⇝ tCoFix mfix1 idx

  | cofix_red_body mfix0 mfix1 idx :
      OnOne2 (on_Trel_eq (fun t u => Σ ;;; Γ ,,, fix_context mfix0 |- t ⇝ u) dbody (fun x => (dname x, dtype x, rarg x))) mfix0 mfix1 ->
      Σ ;;; Γ |- tCoFix mfix0 idx ⇝ tCoFix mfix1 idx
  where " Σ ;;; Γ |- t ⇝ u " := (red1 Σ Γ t u).

Lemma red1_ind_all :
  forall (Σ : global_env) (P : context -> term -> term -> Type),

       (forall (Γ : context) (na : aname) (t b a : term) ts,
        P Γ (mkApps (tLambda na t b) (a :: ts)) (mkApps (b {0 := a}) ts)) ->

       (forall (Γ : context) (na : aname) (b t b' : term), P Γ (tLetIn na b t b') (b' {0 := b})) ->

       (forall (Γ : context) (i : nat) (body : term),
        option_map decl_body (nth_error Γ i) = Some (Some body) -> P Γ (tRel i) ((lift0 (S i)) body)) ->

       (forall (Γ : context) (ci : case_info) (c : nat) (u : Instance.t) (args : list term)
          (p : predicate term) (brs : list (branch term)) br,
          nth_error brs c = Some br ->
          #|args| = (ci.(ci_npar) + context_assumptions br.(bcontext))%nat ->
          P Γ (tCase ci p (mkApps (tConstruct ci.(ci_ind) c u) args) brs)
              (iota_red ci.(ci_npar) p args br)) ->

       (forall (Γ : context) (mfix : mfixpoint term) (idx : nat) (args : list term) (narg : nat) (fn : term),
        unfold_fix mfix idx = Some (narg, fn) ->
        is_constructor narg args = true -> P Γ (mkApps (tFix mfix idx) args) (mkApps fn args)) ->

       (forall (Γ : context) ci (p : predicate term) (mfix : mfixpoint term) (idx : nat)
          (args : list term) (narg : nat) (fn : term) (brs : list (branch term)),
        unfold_cofix mfix idx = Some (narg, fn) ->
        P Γ (tCase ci p (mkApps (tCoFix mfix idx) args) brs) (tCase ci p (mkApps fn args) brs)) ->

       (forall (Γ : context) (p : projection) (mfix : mfixpoint term) (idx : nat) (args : list term)
          (narg : nat) (fn : term),
        unfold_cofix mfix idx = Some (narg, fn) -> P Γ (tProj p (mkApps (tCoFix mfix idx) args)) (tProj p (mkApps fn args))) ->

       (forall (Γ : context) c (decl : constant_body) (body : term),
        declared_constant Σ c decl ->
        forall u : Instance.t, cst_body decl = Some body -> P Γ (tConst c u) (subst_instance u body)) ->

       (forall (Γ : context) p (args : list term) (u : Instance.t)
         (arg : term),
           nth_error args (p.(proj_npars) + p.(proj_arg)) = Some arg ->
           P Γ (tProj p (mkApps (tConstruct p.(proj_ind) 0 u) args)) arg) ->

       (forall (Γ : context) (na : aname) (M M' N : term),
        red1 Σ Γ M M' -> P Γ M M' -> P Γ (tLambda na M N) (tLambda na M' N)) ->

       (forall (Γ : context) (na : aname) (M M' N : term),
        red1 Σ (Γ,, vass na N) M M' -> P (Γ,, vass na N) M M' -> P Γ (tLambda na N M) (tLambda na N M')) ->

       (forall (Γ : context) (na : aname) (b t b' r : term),
        red1 Σ Γ b r -> P Γ b r -> P Γ (tLetIn na b t b') (tLetIn na r t b')) ->

       (forall (Γ : context) (na : aname) (b t b' r : term),
        red1 Σ Γ t r -> P Γ t r -> P Γ (tLetIn na b t b') (tLetIn na b r b')) ->

       (forall (Γ : context) (na : aname) (b t b' r : term),
        red1 Σ (Γ,, vdef na b t) b' r -> P (Γ,, vdef na b t) b' r -> P Γ (tLetIn na b t b') (tLetIn na b t r)) ->

       (forall (Γ : context) (ci : case_info) p params' c brs,
          OnOne2 (Trel_conj (red1 Σ Γ) (P Γ)) p.(pparams) params' ->
           P Γ (tCase ci p c brs)
               (tCase ci (set_pparams p params') c brs)) ->

       (forall (Γ : context) (ci : case_info) p preturn' c brs,
          red1 Σ (Γ ,,, inst_case_predicate_context p) p.(preturn) preturn' ->
          P (Γ ,,, inst_case_predicate_context p) p.(preturn) preturn' ->
          P Γ (tCase ci p c brs)
              (tCase ci (set_preturn p preturn') c brs)) ->

       (forall (Γ : context) (ind : case_info) (p : predicate term) (c c' : term) (brs : list (branch term)),
        red1 Σ Γ c c' -> P Γ c c' -> P Γ (tCase ind p c brs) (tCase ind p c' brs)) ->

       (forall (Γ : context) ci p c brs brs',
          OnOne2 (fun br br' =>
          (on_Trel_eq (Trel_conj (red1 Σ (Γ ,,, inst_case_branch_context p br))
            (P (Γ ,,, inst_case_branch_context p br)))
            bbody bcontext br br')) brs brs' ->
          P Γ (tCase ci p c brs) (tCase ci p c brs')) ->

       (forall (Γ : context) (p : projection) (c c' : term), red1 Σ Γ c c' -> P Γ c c' ->
                                                             P Γ (tProj p c) (tProj p c')) ->

       (forall (Γ : context) M1 N1 M2, red1 Σ Γ M1 N1 -> P Γ M1 N1 -> ~~ isApp M1 -> ~~ isFix M1 -> M2 <> [] ->
                                                         P Γ (mkApps M1 M2) (mkApps N1 M2)) ->

       (forall (Γ : context) M1 N2 M2, ~~ isApp M1 ->
        OnOne2 (Trel_conj (red1 Σ Γ) (P Γ)) M2 N2 ->
        P Γ (mkApps M1 M2) (mkApps M1 N2)) ->

      (forall (Γ : context) mfix0 mfix1 idx M2,
        OnOne2 (on_Trel_eq (Trel_conj (fun t u => Σ ;;; Γ |- t ⇝ u) (P Γ)) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
        P Γ (mkApps (tFix mfix0 idx) M2) (mkApps (tFix mfix1 idx) M2)) ->

      (forall (Γ : context) mfix0 mfix1 idx M2,
        OnOne2 (on_Trel_eq (Trel_conj (fun t u => Σ ;;; Γ ,,, fix_context mfix0 |- t ⇝ u) (P (Γ ,,, fix_context mfix0))) dbody (fun x => (dname x, dtype x, rarg x))) mfix0 mfix1 ->
        P Γ (mkApps (tFix mfix0 idx) M2) (mkApps (tFix mfix1 idx) M2)) ->

       (forall (Γ : context) (na : aname) (M1 M2 N1 : term),
        red1 Σ Γ M1 N1 -> P Γ M1 N1 -> P Γ (tProd na M1 M2) (tProd na N1 M2)) ->

       (forall (Γ : context) (na : aname) (M2 N2 M1 : term),
        red1 Σ (Γ,, vass na M1) M2 N2 -> P (Γ,, vass na M1) M2 N2 -> P Γ (tProd na M1 M2) (tProd na M1 N2)) ->

       (forall (Γ : context) (ev : nat) (l l' : list term),
           OnOne2 (Trel_conj (red1 Σ Γ) (P Γ)) l l' -> P Γ (tEvar ev l) (tEvar ev l')) ->

       (forall (Γ : context) (mfix0 mfix1 : list (def term)) (idx : nat),
        OnOne2 (on_Trel_eq (Trel_conj (red1 Σ Γ) (P Γ)) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
        P Γ (tFix mfix0 idx) (tFix mfix1 idx)) ->

       (forall (Γ : context) (mfix0 mfix1 : list (def term)) (idx : nat),
        OnOne2 (on_Trel_eq (Trel_conj (red1 Σ (Γ ,,, fix_context mfix0))
                                      (P (Γ ,,, fix_context mfix0))) dbody
                           (fun x => (dname x, dtype x, rarg x))) mfix0 mfix1 ->
        P Γ (tFix mfix0 idx) (tFix mfix1 idx)) ->

       (forall (Γ : context) (mfix0 mfix1 : list (def term)) (idx : nat),
        OnOne2 (on_Trel_eq (Trel_conj (red1 Σ Γ) (P Γ)) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
        P Γ (tCoFix mfix0 idx) (tCoFix mfix1 idx)) ->

       (forall (Γ : context) (mfix0 mfix1 : list (def term)) (idx : nat),
        OnOne2 (on_Trel_eq (Trel_conj (red1 Σ (Γ ,,, fix_context mfix0))
                                      (P (Γ ,,, fix_context mfix0))) dbody
                           (fun x => (dname x, dtype x, rarg x))) mfix0 mfix1 ->
        P Γ (tCoFix mfix0 idx) (tCoFix mfix1 idx)) ->

       forall (Γ : context) (t t0 : term), red1 Σ Γ t t0 -> P Γ t t0.
Proof.
  intros. rename X29 into Xlast. revert Γ t t0 Xlast.
  fix aux 4. intros Γ t T.
  move aux at top.
  destruct 1; match goal with
              | |- P _ (tFix _ _) (tFix _ _) => idtac
              | |- P _ (tCoFix _ _) (tCoFix _ _) => idtac
              | |- P _ (mkApps (tFix _ _) _) _ => idtac
              | |- P _ (tCase _ _ (mkApps (tCoFix _ _) _) _) _ => idtac
              | |- P _ (tProj _ (mkApps (tCoFix _ _) _)) _ => idtac
              | H : _ |- _ => eapply H; eauto
              end.
  - eapply X3; eauto.
  - eapply X4; eauto.
  - eapply X5; eauto.

  - revert params' o.
    generalize (pparams p).
    fix auxl 3.
    intros params params' [].
    + constructor. split; auto.
    + constructor. auto.

  - revert brs' o.
    revert brs.
    fix auxl 3.
    intros l l' Hl. destruct Hl.
    + simpl in *. constructor; intros; intuition auto.
    + constructor. eapply auxl. apply Hl.

  - revert M2 N2 o.
    fix auxl 3.
    intros l l' Hl. destruct Hl.
    + constructor. split; auto.
    + constructor. auto.

  - eapply X20.
    revert mfix0 mfix1 o.
    fix auxl 3.
    intros l l' Hl. destruct Hl.
    + constructor; split; auto; intuition.
    + constructor; try split; auto; intuition.

  - eapply X21. revert o.
    generalize (fix_context mfix0).
    intros c o. revert mfix0 mfix1 o.
    fix auxl 3.
    intros l l' Hl. destruct Hl.
    + constructor. split; auto; intuition.
    + constructor; try split; auto; intuition.

  - revert l l' o.
    fix auxl 3.
    intros l l' Hl. destruct Hl.
    + constructor. split; auto.
    + constructor. auto.

  - eapply X25.
    revert mfix0 mfix1 o; fix auxl 3.
    intros l l' Hl; destruct Hl;
    constructor; try split; auto; intuition.

  - eapply X26.
    revert o. generalize (fix_context mfix0). intros c Xnew.
    revert mfix0 mfix1 Xnew; fix auxl 3; intros l l' Hl;
    destruct Hl; constructor; try split; auto; intuition.

  - eapply X27.
    revert mfix0 mfix1 o.
    fix auxl 3; intros l l' Hl; destruct Hl;
      constructor; try split; auto; intuition.

  - eapply X28.
    revert o. generalize (fix_context mfix0). intros c new.
    revert mfix0 mfix1 new; fix auxl 3; intros l l' Hl; destruct Hl;
      constructor; try split; auto; intuition.
Defined.

Lemma red_tApp Σ Γ t v u :
  red1 Σ Γ t v ->
  red1 Σ Γ (tApp t u) (tApp v u).
Proof.
  induction 1.
  all:try solve [eapply (app_red_l _ _ _ _ [u]) => //; econstructor; eauto].
  - rewrite -![tApp _ u](mkApps_app _ _ [u]).
    eapply red_beta.
  - rewrite -![tApp _ u](mkApps_app _ _ [u]). econstructor; eauto.
    now apply is_constructor_app_ge.
  - rewrite -![tApp _ u](mkApps_app _ _ [u]). econstructor; eauto.
  - rewrite -![tApp _ u](mkApps_app _ _ [u]). econstructor; eauto.
    now eapply OnOne2_app_r.
  - rewrite -![tApp _ u](mkApps_app _ _ [u]). now eapply app_fix_red_ty.
  - rewrite -![tApp _ u](mkApps_app _ _ [u]). now eapply app_fix_red_body.
  - now eapply (app_fix_red_ty _ _ _ _ _ [_]).
  - now eapply (app_fix_red_body _ _ _ _ _ [_]).
Qed.

Lemma isLambda_red1 Σ Γ b b' : isLambda b -> red1 Σ Γ b b' -> isLambda b'.
Proof.
  destruct b; simpl; try discriminate.
  intros _ red.
  depelim red; solve_discr; eauto. depelim o.
Qed.

End Red1Apps.

Lemma red1_red1apps Σ Γ t v :
  red1 Σ Γ t v -> Red1Apps.red1 Σ Γ t v.
Proof.
  intros red; induction red using red1_ind_all in |- *.
  all:try solve [econstructor; eauto; solve_all; eauto].
  - eapply (Red1Apps.red_beta _ _ _ _ _ _ []).
  - now eapply Red1Apps.red_tApp.
  - remember (decompose_app (tApp M1 M2)).
    destruct p as [hd args].
    edestruct (decompose_app_rec_inv' M1 [M2]). rewrite /decompose_app in Heqp.
    cbn in Heqp. rewrite -Heqp. reflexivity.
    destruct a as [napp [hm2 hm1]].
    symmetry in Heqp; eapply decompose_app_inv in Heqp. rewrite Heqp.
    assert (tApp M1 N2 = mkApps hd (firstn x args ++ [N2])) as ->.
    { now rewrite mkApps_app -hm1. }
    rewrite -{1}(firstn_skipn x args) -hm2. eapply Red1Apps.app_red_r => //.
    eapply OnOne2_app. now constructor.
Qed.

Lemma head_nApp f :
  ~~ isApp f -> head f = f.
Proof.
  induction f => //.
Qed.

Lemma expanded_mkApps_inv Σ Γ f v :
  ~~ isApp f ->
  ~~ (isConstruct f || isFix f || isRel f) ->
  expanded Σ Γ (mkApps f v) ->
  expanded Σ Γ f /\ Forall (expanded Σ Γ) v.
Proof.
  intros happ hc.
  induction v using rev_ind; cbn.
  - intros exp; split => //.
  - rewrite mkApps_app /=.
    move/expanded_tApp_inv => e.
    forward e. rewrite /isConstructApp /isFixApp head_mkApps.
    rewrite head_nApp //. now move/negbTE: hc ->.
    intuition auto. eapply app_Forall; eauto.
Qed.


Lemma arguments_mkApps f args :
  ~~ isApp f ->
  arguments (mkApps f args) = args.
Proof.
  rewrite /arguments => isa.
  rewrite decompose_app_mkApps //.
Qed.

Lemma arguments_mkApps' f args :
  arguments (mkApps f args) = arguments f ++ args.
Proof.
  rewrite /arguments.
  rewrite /decompose_app decompose_app_rec_mkApps //.
  rewrite app_nil_r.
  induction f in args |- * => //=.
  rewrite IHf1. now rewrite (IHf1 [f2]) -app_assoc.
Qed.

Lemma expanded_mkApps_inv' Σ Γ f :
  expanded Σ Γ f ->
  let args := arguments f in
  Forall (expanded Σ Γ) args /\
    match head f with
    | tRel n => exists m, nth_error Γ n = Some m /\ m <= #|args|
    | tConstruct ind c u => exists mind idecl cdecl,
      declared_constructor Σ (ind, c) mind idecl cdecl /\ #|args| >= ind_npars mind + context_assumptions (cstr_args cdecl)
    | tFix mfix idx => exists d,
      Forall
        (fun d0 : def term =>
        isLambda (dbody d0) /\
        (let ctx :=
            rev_map (fun d1 : def term => (1 + rarg d1)%nat)
              mfix in
          expanded Σ (ctx ++ Γ) (dbody d0))) mfix /\
      args <> [] /\
      nth_error mfix idx = Some d /\ #|args| > rarg d
    | _ => expanded Σ Γ (head f)
    end.
Proof.
  induction 1 using expanded_ind; cbn.
  all: try solve [split; econstructor; eauto].
  all:rewrite head_mkApps /=.
  - rewrite arguments_mkApps //. split => //. now exists m.
  - destruct IHexpanded. rewrite arguments_mkApps'. split.
    eapply app_Forall => //.
    rewrite app_length.
    destruct (head f6) => //; firstorder (eauto; try lia).
    exists x. split => //. firstorder (eauto; try lia).
    intros heq; apply H5. now eapply app_eq_nil in heq.
  - rewrite arguments_mkApps //. split => //. now exists d.
  - rewrite arguments_mkApps //. split => //.
    firstorder.
Qed.

Lemma All_fold_map_context (P : context -> context_decl -> Type) (f : term -> term) ctx :
  All_fold P (map_context f ctx) <~> All_fold (fun Γ d => P (map_context f Γ) (map_decl f d)) ctx.
Proof.
  induction ctx.
  - split; constructor.
  - cbn. split; intros H; depelim H; constructor; auto; now apply IHctx.
Qed.

Lemma expanded_fix_subst Σ a k b Γ Γs Δ :
  #|Γ| = k ->
  Forall2 (fun n arg => forall args Γ' k',
    Forall (expanded Σ (Γ' ++ Δ)) args ->
    n <= #|args| ->
    #|Γ'| = k' ->
    expanded Σ (Γ' ++ Δ) (mkApps (lift0 k' arg) args)) Γs a ->
  expanded Σ (Γ ++ Γs ++ Δ) b ->
  expanded Σ (Γ ++ Δ) (subst a k b).
Proof.
  intros Hk Hs.
  remember (Γ ++ _ ++ Δ)%list as Γ_.
  intros exp; revert Γ k Hk HeqΓ_.
  induction exp using expanded_ind; intros Γ' k Hk ->.
  all:try solve[ cbn; econstructor => // ].
  2,7:solve[ cbn; econstructor => //; solve_all ].
  - rewrite subst_mkApps /=.
    destruct (Nat.leb_spec k n).
    destruct (nth_error a _) eqn:hnth.
    * pose proof (Forall2_length Hs).
      pose proof (Forall2_nth_error_Some_r _ _ _ _ _ _ _ hnth Hs) as [t' [hnth' hargs]].
      eapply hargs => //.
      eapply Forall_map.
      2:{ len. rewrite nth_error_app_ge in H. lia. subst k.
        rewrite nth_error_app_lt in H.
        eapply nth_error_Some_length in hnth'. lia. rewrite hnth' in H. noconf H. exact H0. }
      solve_all.
    * rewrite nth_error_app_ge in H. lia.
      eapply nth_error_None in hnth.
      pose proof (Forall2_length Hs).
      rewrite nth_error_app_ge in H. lia.
      eapply expanded_tRel. rewrite nth_error_app_ge. lia. erewrite <- H.
      lia_f_equal. len. solve_all.
    * rewrite nth_error_app_lt in H. lia.
      eapply expanded_tRel. rewrite nth_error_app_lt. lia. tea. now len.
      solve_all.
  - cbn. econstructor.
    eapply (IHexp (0 :: Γ') (S k)); cbn; auto; try lia.
  - cbn. econstructor. apply IHexp1; auto.
    eapply (IHexp2 (0 :: Γ') (S k)); cbn; auto; lia.
  - rewrite subst_mkApps.
    destruct (isConstruct (subst a k f6) || isFix (subst a k f6) || isRel (subst a k f6)) eqn:eqc.
    specialize (IHexp  _ _ Hk eq_refl).
    eapply expanded_mkApps_expanded => //. solve_all.
    eapply expanded_mkApps => //. now eapply IHexp. solve_all.
  - cbn. econstructor. eauto. cbn. solve_all. solve_all.
    specialize (H1 (repeat 0 #|bcontext x| ++ Γ') (#|bcontext x| + k)%nat).
    forward H1 by len.
    forward H1. now rewrite app_assoc.
    rewrite /id. rewrite app_assoc. apply H1.
  - rewrite subst_mkApps. cbn.
    eapply expanded_tFix.
    + solve_all. now eapply isLambda_subst.
      specialize (a0
      (rev_map (fun d0 : def term => S (rarg d0))
      (map (map_def (subst a k) (subst a (#|mfix| + k))) mfix) ++ Γ') (#|mfix| + k)%nat).
      forward a0 by len.
      forward a0. { rewrite app_assoc. f_equal. f_equal.
        rewrite !rev_map_spec. f_equal. now rewrite map_map_compose /=. }
      rewrite app_assoc. eapply a0.
    + solve_all.
    + now destruct args.
    + rewrite nth_error_map /= H4 //.
    + len.
  - cbn. constructor.
    solve_all.
    specialize (a0 (repeat 0 #|mfix| ++ Γ') (#|mfix| + k)%nat).
    forward a0 by len.
    forward a0. { rewrite app_assoc //. }
    rewrite app_assoc. eapply a0.
  - rewrite subst_mkApps. cbn.
    eapply expanded_tConstruct_app; tea. now len.
    solve_all.
Qed.

Lemma expanded_unfold_fix Σ Γ' mfix idx narg fn :
  unfold_fix mfix idx = Some (narg, fn) ->
  All (fun d0 : def term => isLambda (dbody d0) /\ expanded Σ (rev_map (fun d1 : def term => S (rarg d1)) mfix ++ Γ') (dbody d0)) mfix ->
  expanded Σ Γ' fn.
Proof.
  unfold unfold_fix.
  destruct nth_error eqn:e => //.
  intros [= <- <-] hf.
  pose proof (nth_error_all e hf) as [hl hf'].
  eapply (expanded_fix_subst _ _ _ _ []) => //; tea.
  rewrite rev_map_spec.
  eapply Forall2_from_nth_error. len.
  intros n rarg f. len. intros hn hrarg hnthf args Γ'' k' hargs hrarg' <-.
  eapply PCUICParallelReductionConfluence.nth_error_fix_subst in hnthf. subst f.
  move: hrarg.
  rewrite nth_error_rev; len. rewrite List.rev_involutive nth_error_map.
  intros hrarg.
  destruct (nth_error mfix (_ - _)) eqn:e'. cbn in hrarg. noconf hrarg.
  eapply expanded_tFix => //. solve_all.
  eapply expanded_lift; len. rewrite !rev_map_spec in H1 *.
  rewrite map_map => //. destruct args => //. cbn in hrarg'. lia.
  rewrite nth_error_map /= e' /= //. cbn. lia.
  eapply nth_error_None in e'. lia.
Qed.

Lemma expanded_unfold_cofix Σ Γ' mfix idx narg fn :
  unfold_cofix mfix idx = Some (narg, fn) ->
  All (fun d0 : def term => expanded Σ (repeat 0 #|mfix| ++ Γ') (dbody d0)) mfix ->
  expanded Σ Γ' fn.
Proof.
  unfold unfold_cofix.
  destruct nth_error eqn:e => //.
  intros [= <- <-] hf.
  pose proof (nth_error_all e hf) as hf'.
  eapply (expanded_subst _ _ _ _ []) => //; tea.
  rewrite /cofix_subst.
  generalize #|mfix|.
  induction n; repeat constructor; eauto. solve_all.
  len.
Qed.

Lemma expanded_weakening_env {cf : checker_flags} Σ Σ' Γ t :
  wf Σ' ->
  extends Σ Σ' ->
  expanded Σ Γ t -> expanded Σ' Γ t.
Proof.
  intros w s.
  eapply expanded_ind; intros.
  all:try solve [econstructor; eauto].
  - econstructor; eauto. solve_all. sq. eapply All_fold_impl; tea. cbn.
    intros. now rewrite repeat_app in H6.
  - eapply expanded_tFix; eauto. solve_all.
  - eapply expanded_tConstruct_app; eauto.
    eapply PCUICWeakeningEnv.weakening_env_declared_constructor; tea.
Qed.

Lemma expanded_global_env_constant {cf : checker_flags} Σ c decl :
  wf Σ ->
  expanded_global_env Σ ->
  declared_constant Σ c decl ->
  ForOption (expanded Σ []) (cst_body decl).
Proof.
  intros wf; destruct Σ as [Σ univs] => /=. cbn.
  unfold expanded_global_env. cbn.
  induction 1; cbn => //.
  intros [->|H'].
  - depelim H0.
    destruct decl as [? [] ?]; cbn in *.
    constructor. cbn.
    eapply expanded_weakening_env; tea.
    eapply extends_strictly_on_decls_extends.
    split => //=. eapply incl_cs_refl. 2:eapply Retroknowledge.extends_refl.
    set (cb := ConstantDecl _). now exists [(c, cb)].
    constructor.
  - forward IHexpanded_global_declarations.
    destruct wf. cbn in *. split => //.
    cbn. now depelim o0.
    eapply IHexpanded_global_declarations in H'.
    destruct decl as [? [] ?]; cbn in * => //. 2:constructor.
    depelim H'. constructor.
    eapply expanded_weakening_env; tea.
    eapply extends_strictly_on_decls_extends.
    split => //=. eapply incl_cs_refl. 2:eapply Retroknowledge.extends_refl.
    now exists [decl0].
Qed.

Lemma All_fold_nth_error P (ctx : context) n b :
  All_fold P ctx -> nth_error ctx n = Some b ->
  P (skipn (S n) ctx) b.
Proof.
  induction 1 in n, b |- *.
  - rewrite nth_error_nil //.
  - destruct n => //=.
    * intros [= <-]. now rewrite skipn_S skipn_0.
    * intros hnth. now rewrite skipn_S.
Qed.

Lemma skipn_repeat {A} k n (a : A) :
  skipn n (repeat a k) = repeat a (k - n).
Proof.
  induction n in k |- *.
  - rewrite skipn_0. lia_f_equal.
  - destruct k => //=.
    rewrite skipn_S IHn. lia_f_equal.
Qed.

Lemma expanded_red {cf : checker_flags} {Σ : global_env_ext} Γ Γ' t v : wf Σ ->
  expanded_global_env Σ ->
  (forall n body, option_map decl_body (nth_error Γ n) = Some (Some body) -> expanded Σ (skipn (S n) Γ') body) ->
  red1 Σ Γ t v ->
  expanded Σ Γ' t ->
  expanded Σ Γ' v.
Proof.
  move=> wf expΣ wfΓ /red1_red1apps red.
  induction red using Red1Apps.red1_ind_all in wfΓ, Γ' |- *;  intros exp.
  - eapply expanded_mkApps_inv in exp as [] => //.
    eapply expanded_tLambda_inv in H.
    depelim H0.
    eapply expanded_mkApps => //.
    eapply (expanded_subst _ _ _ _ [] Γ') => //. now constructor.
  - eapply expanded_tLetIn_inv in exp as [].
    eapply (expanded_subst _ _ _ _ [] Γ') => //. now constructor.
  - rewrite -(firstn_skipn (S i) Γ').
    eapply expanded_mkApps_inv' in exp; cbn in exp.
    destruct exp as [_ [m []]]. eapply nth_error_Some_length in H0.
    eapply (expanded_lift _ _ _ _ []) => //.
    rewrite firstn_length_le; try lia.
    now eapply wfΓ.
  - eapply expanded_tCase_inv in exp as [? []].
    unfold iota_red.
    move/expanded_mkApps_inv': H3 => /=.
    rewrite arguments_mkApps // head_mkApps //=.
    intros [hargs [mind [idecl [cdecl [declc hargs']]]]].
    eapply nth_error_forall in H2; tea.
    destruct H2 as [[hbctx] hbod].
    eapply (expanded_subst _ _ _ _ [] _) => //.
    + eapply Forall_rev, Forall_skipn => //.
    + len. replace #|skipn (ci_npar ci) args| with (context_assumptions (inst_case_branch_context p br)).
      eapply expanded_let_expansion; len. red.
      sq. rewrite /inst_case_branch_context /inst_case_context /subst_context.
      eapply PCUICParallelReduction.All_fold_fold_context_k.
      eapply All_fold_map_context, All_fold_impl; tea; cbn.
      intros ? ? fo. len. destruct x as [? [] ?] => //; constructor.
      cbn in fo. depelim fo. eapply (expanded_subst _ _ _ _ (repeat 0 #|Γ0|) _); len.
      eapply Forall_rev; eauto.
      eapply expanded_subst_instance. rewrite app_assoc. now eapply expanded_weakening.
      rewrite skipn_length. len.
  - move/expanded_mkApps_inv': exp. cbn.
    rewrite arguments_mkApps // head_mkApps //=.
    move=> [hargs [d [hf [hargs' []]]]] hnth hrarg.
    eapply expanded_mkApps_expanded => //; solve_all.
    eapply expanded_unfold_fix in H; tea.
  - eapply expanded_tCase_inv in exp as [? []].
    constructor => //.
    eapply expanded_mkApps_inv' in H2. move: H2; rewrite arguments_mkApps // head_mkApps //=.
    intros [hargs' hcof]. cbn in hcof. eapply expanded_tCoFix_inv in hcof.
    eapply expanded_unfold_cofix in H; tea. eapply expanded_mkApps; tea => //. solve_all.
  - eapply expanded_tProj_inv in exp. econstructor.
    eapply expanded_mkApps_inv' in exp. move: exp; rewrite arguments_mkApps // head_mkApps //=.
    intros [hargs' hcof]. cbn in hcof. eapply expanded_tCoFix_inv in hcof.
    eapply expanded_mkApps => //.
    eapply expanded_unfold_cofix in H; tea. solve_all.
  - eapply expanded_subst_instance.
    eapply expanded_global_env_constant in expΣ; tea.
    eapply (expanded_weakening _ []). rewrite H0 in expΣ. now depelim expΣ.
  - eapply expanded_tProj_inv in exp.
    move/expanded_mkApps_inv': exp. rewrite arguments_mkApps // head_mkApps //=.
    intros [].
    eapply nth_error_forall in H0; tea.
  - constructor. now eapply expanded_tLambda_inv in exp.
  - constructor. eapply expanded_tLambda_inv in exp.
    eapply IHred => //.
    { intros [] body; cbn => //. rewrite skipn_S. eapply wfΓ. }
  - eapply expanded_tLetIn_inv in exp; now constructor.
  - eapply expanded_tLetIn_inv in exp. now constructor.
  - eapply expanded_tLetIn_inv in exp. constructor; intuition eauto.
    eapply IHred => //.
    { intros [] ? => //=. intros [=]. subst b. now rewrite skipn_S skipn_0.
      rewrite skipn_S. eapply wfΓ. }
  - eapply expanded_tCase_inv in exp as [? []].
    constructor; eauto. cbn.
    solve_all. eapply OnOne2_impl_All_r; tea. intuition eauto. now apply X0.
    now rewrite /PCUICOnOne.set_pparams /= -(OnOne2_length X).
  - eapply expanded_tCase_inv in exp as [? []].
    constructor; eauto.
  - eapply expanded_tCase_inv in exp as [? []].
    econstructor; eauto.
  - eapply expanded_tCase_inv in exp as [? []].
    econstructor; eauto. solve_all.
    eapply OnOne2_impl_All_r; tea.
    intros x y [? ?]. intros [[] ?]. rewrite -e0.
    solve_all. eapply e => //.
    intros n b.
    clear -H H2 wfΓ.
    destruct nth_error eqn:e' => //.
    cbn. intros [=]. destruct c as [? [] ?]. cbn in *. noconf H1.
    eapply nth_error_app_inv in e' as [[]|[]].
    { rewrite inst_case_branch_context_length in H0. destruct H2.
      rewrite /inst_case_branch_context /inst_case_context in H1.
      destruct (nth_error (bcontext x) n) eqn:e.
      2:{ eapply nth_error_None in e. rewrite skipn_app skipn_all2. len. cbn. len. }
      rewrite /subst_context in H1.
      erewrite nth_error_fold_context_k in H1. 4:{ rewrite nth_error_map e //. } 3:len. 2:exact [].
      len in H1. noconf H1. destruct c as [? [] ?]; noconf H1.
      rewrite skipn_app. len. eapply All_fold_nth_error in X; tea. cbn in X. depelim X.
      rewrite skipn_length in H1.
      eapply expanded_subst. rewrite skipn_length. len.
      replace (S n - #|bcontext x|) with 0. 2:{ lia. } rewrite skipn_0. eapply Forall_rev. solve_all.
      len. rewrite app_assoc. eapply expanded_weakening. eapply expanded_subst_instance.
      now rewrite skipn_repeat. }
    { rewrite inst_case_branch_context_length in H0, H1.
      rewrite skipn_app skipn_all2 /=; len.
      replace (S n - #|bcontext x|) with (S (n - #|bcontext x|)). 2:lia.
      eapply wfΓ. rewrite H1 //. }
    noconf H1.
  - eapply expanded_tProj_inv in exp. now econstructor.
  - eapply expanded_mkApps_inv' in exp.
    rewrite head_mkApps head_nApp in exp => //.
    rewrite arguments_mkApps // in exp. destruct exp as [].
    specialize (IHred Γ' wfΓ).
    destruct M1; try solve [eapply expanded_mkApps => //; eauto].
    * depelim red; solve_discr. eapply wfΓ in e.
      eapply expanded_mkApps => //.
      rewrite -(firstn_skipn (S n) Γ'). eapply (expanded_lift _ _ _ _ []) => //.
      destruct H3 as [m [hn ha]].
      rewrite firstn_length_le //. now eapply nth_error_Some_length in hn.
      depelim o.
    * depelim red; solve_discr. depelim o.

  - eapply expanded_mkApps_inv' in exp.
    move: exp.
    rewrite head_mkApps head_nApp // arguments_mkApps //.
    intros [].
    assert(Forall (expanded Σ Γ') N2).
    { clear H1. solve_all. eapply OnOne2_impl_All_r; tea. cbn. intuition auto. }
    destruct M1; try solve [eapply expanded_mkApps => //; eauto].
    + rewrite (OnOne2_length X) in H1. destruct H1 as [m []]; eapply expanded_tRel; tea.
    + rewrite (OnOne2_length X) in H1. destruct H1 as [m [? [? []]]]; eapply expanded_tConstruct_app; tea.
    + rewrite (OnOne2_length X) in H1.
      destruct H1 as [d [? [? []]]]; eapply expanded_tFix; tea.
      destruct N2; cbn in *; eauto. lia. intros eq; discriminate.

  - move/expanded_mkApps_inv': exp.
    rewrite head_mkApps head_nApp // arguments_mkApps // => [] [] hargs [d [hf [hm2 [hnth harg]]]].
    eapply OnOne2_nth_error in hnth as [t' [hnth hor]]; tea.
    eapply expanded_tFix; tea.
    { clear hor. solve_all. eapply OnOne2_impl_All_r; tea.
      intros ? ? [] []. noconf e. rewrite -H2. split => //. solve_all.
      clear -X H1.
      enough (rev_map (fun d1 : def term => S (rarg d1)) mfix0 = (rev_map (fun d1 : def term => S (rarg d1)) mfix1)) as <- => //.
      clear -X. rewrite !rev_map_spec. f_equal. induction X. destruct p as []. cbn in *. congruence. cbn. congruence. }
    { destruct hor; subst => //. destruct p as [? e]; noconf e. now congruence. }

  - move/expanded_mkApps_inv': exp.
    rewrite head_mkApps head_nApp // arguments_mkApps // => [] [] hargs [d [hf [hm2 [hnth harg]]]].
    eapply OnOne2_nth_error in hnth as [t' [hnth hor]]; tea.
    eapply expanded_tFix; tea.
    { clear hor. solve_all.
      assert (rev_map (fun d1 : def term => S (rarg d1)) mfix0 = (rev_map (fun d1 : def term => S (rarg d1)) mfix1)).
      { clear -X. rewrite !rev_map_spec. f_equal. induction X. destruct p as []. cbn in *. congruence. cbn. congruence. }
      rewrite -H.
      eapply OnOne2_impl_All_r; tea.
      intros ? ? [] []. noconf e. destruct p.
      eapply Red1Apps.isLambda_red1 in r; tea. split => //.
      set(Γ'' := rev_map (fun d1 : def term => S (rarg d1)) mfix0).
      eapply e => //.
      { intros n b hnth'.
        destruct (nth_error (fix_context mfix0) n) eqn:e'.
        rewrite nth_error_app_lt in hnth'. now eapply nth_error_Some_length in e'.
        rewrite e' in hnth'. noconf hnth'.
        pose proof (PCUICParallelReductionConfluence.fix_context_assumption_context mfix0).
        eapply PCUICParallelReductionConfluence.nth_error_assumption_context in H6; tea. congruence.
        rewrite /Γ''.
        eapply nth_error_None in e'. len in e'.
        rewrite nth_error_app_ge in hnth' => //. now len.
        rewrite skipn_app skipn_all2. len.
        cbn. len. replace (S n - #|mfix0|) with (S (n - #|mfix0|)). 2:{ lia. }
        eapply wfΓ. now len in hnth'. } }
    { destruct hor; subst => //. destruct p as [? e]; noconf e. now congruence. }
  - eapply expanded_tProd.
  - constructor.
  - constructor.
    eapply expanded_tEvar_inv in exp.
    solve_all; eapply OnOne2_impl_All_r; tea. intuition eauto.
    now eapply X0.
  - depelim exp; solve_discr. now cbn in H.
  - depelim exp; solve_discr. now cbn in H.
  - eapply expanded_tCoFix_inv in exp. econstructor.
    rewrite -(OnOne2_length X). solve_all; eapply OnOne2_impl_All_r; tea; intuition eauto.
    destruct X0. noconf e. now rewrite -H1.
  - eapply expanded_tCoFix_inv in exp. econstructor.
    rewrite -(OnOne2_length X). solve_all; eapply OnOne2_impl_All_r; tea; intuition eauto.
    destruct X0. destruct p. noconf e. eapply e0 => //.
    intros n b.
    destruct nth_error eqn:e' => //.
    cbn. intros [=]. destruct c as [? [] ?]. cbn in *. noconf H4.
    eapply nth_error_app_inv in e' as [[]|[]].
    { pose proof (PCUICParallelReductionConfluence.fix_context_assumption_context mfix0).
      eapply PCUICParallelReductionConfluence.nth_error_assumption_context in H5; tea. cbn in H5. congruence. }
    len in H3. len in H4.
    rewrite skipn_app skipn_all2; len.
    replace (S n - #|mfix0|) with (S (n - #|mfix0|)) by lia. eapply wfΓ. rewrite H4 /= //.
    noconf H4.
Qed.