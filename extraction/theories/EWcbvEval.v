(* Distributed under the terms of the MIT license.   *)
Set Warnings "-notation-overridden".

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From MetaCoq.Template Require Import config utils Ast.
From MetaCoq.PCUIC Require Import PCUICAstUtils.
From MetaCoq.Extraction Require Import EAst EAstUtils EInduction ELiftSubst ETyping.
From MetaCoq.Template Require AstUtils.
Require Import String.
Local Open Scope string_scope.
Set Asymmetric Patterns.
Require Import ssreflect ssrbool.

Existing Instance config.default_checker_flags.

Local Ltac inv H := inversion H; subst.

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
  | tCoFix _ _
  | tLambda _ _
  | tFix _ _ => true
  | _ => false
  end.

Lemma mkApps_app t l l' : mkApps t (l ++ l') = mkApps (mkApps t l) l'.
Proof.
  induction l in t, l' |- *; simpl; auto.
Qed.

Lemma decompose_app_rec_inv {t l' f l} :
  decompose_app_rec t l' = (f, l) ->
  mkApps t l' = mkApps f l.
Proof.
  induction t in f, l', l |- *; try intros [= <- <-]; try reflexivity.
  simpl. apply/IHt1.
Qed.

Lemma decompose_app_inv {t f l} :
  decompose_app t = (f, l) -> t = mkApps f l.
Proof. by apply/decompose_app_rec_inv. Qed.
Lemma atom_decompose_app t l : ~~ isApp t -> decompose_app_rec t l = pair t l.
Proof. destruct t; simpl; congruence. Qed.

Lemma mkApps_eq_decompose_app_rec {f args t l} :
  mkApps f args = t ->
  ~~ isApp f ->
  match decompose_app_rec t l with
  | (f', args') => f' = f /\ mkApps t l = mkApps f' args'
  end.
Proof.
  revert f t l.
  induction args using rev_ind; simpl.
  - intros * -> **. rewrite atom_decompose_app; auto.
  - intros. rewrite mkApps_app in H.
    specialize (IHargs f).
    destruct (isApp t) eqn:Heq.
    destruct t; try discriminate.
    simpl in Heq. inv H. simpl.
    specialize (IHargs (mkApps f args) (t2 :: l) eq_refl H0).
    destruct decompose_app_rec. intuition.
    subst t.
    simpl in Heq. discriminate.
Qed.

Lemma decompose_app_eq_right t l l' : decompose_app_rec t l = decompose_app_rec t l' -> l = l'.
Proof.
  induction t in l, l' |- *; simpl; intros [=]; auto.
  specialize (IHt1 _ _ H0). now inv IHt1.
Qed.

Lemma mkApps_eq_right t l l' : mkApps t l = mkApps t l' -> l = l'.
Proof.
  intros. eapply (f_equal decompose_app) in H. unfold decompose_app in H.
  rewrite !decompose_app_rec_mkApps in H. apply decompose_app_eq_right in H.
  now rewrite !app_nil_r in H.
Qed.

Lemma mkApps_eq_decompose' {f args t} :
  mkApps f args = t ->
  ~~ isApp f ->
  match decompose_app t with
  | (f', args') => f' = f /\ args' = args /\ t = mkApps f' args'
  end.
Proof.
  intros.
  have H' := (@mkApps_eq_decompose_app_rec f args t [] H H0).
  rewrite /decompose_app. destruct (decompose_app_rec t []).
  intuition subst; auto. simpl in H2. now eapply mkApps_eq_right in H2.
Qed.


Lemma decompose_app_rec_notApp :
  forall t l u l',
    decompose_app_rec t l = (u, l') ->
    ~~ isApp u.
Proof.
  intros t l u l' e.
  induction t in l, u, l', e |- *.
  all: try (cbn in e ; inversion e ; reflexivity).
  cbn in e. eapply IHt1. eassumption.
Qed.

Lemma decompose_app_notApp :
  forall t u l,
    decompose_app t = (u, l) ->
    ~~ isApp u.
Proof.
  intros t u l e.
  eapply decompose_app_rec_notApp. eassumption.
Qed.

Inductive mkApps_spec : term -> list term -> term -> list term -> term -> Type :=
| mkApps_intro f l n :
    ~~ isApp f ->
    mkApps_spec f l (mkApps f (firstn n l)) (skipn n l) (mkApps f l).

Lemma decompose_app_rec_eq f l :
  ~~ isApp f ->
  decompose_app_rec f l = (f, l).
Proof.
  destruct f; simpl; try discriminate; congruence.
Qed.
Close Scope string_scope.

Lemma firstn_add {A} x y (args : list A) : firstn (x + y) args = firstn x args ++ firstn y (skipn x args).
Proof.
  induction x in y, args |- *. simpl. reflexivity.
  simpl. destruct args. simpl.
  now rewrite firstn_nil.
  rewrite IHx. now rewrite app_comm_cons.
Qed.

Lemma decompose_app_rec_inv' f l hd args :
  decompose_app_rec f l = (hd, args) ->
  ∑ n, ~~ isApp hd /\ l = skipn n args /\ f = mkApps hd (firstn n args).
Proof.
  destruct (isApp f) eqn:Heq.
  revert l args hd.
  induction f; try discriminate. intros.
  simpl in H.
  destruct (isApp f1) eqn:Hf1.
  2:{ rewrite decompose_app_rec_eq in H => //. now apply negbT.
      revert Hf1.
      inv H. exists 1. simpl. intuition auto. now eapply negbT. }
  destruct (IHf1 eq_refl _ _ _ H).
  clear IHf1.
  exists (S x); intuition auto. eapply (f_equal (skipn 1)) in H2.
  rewrite [l]H2. now rewrite skipn_skipn Nat.add_1_r.
  rewrite -Nat.add_1_r firstn_add H3 -H2.
  now rewrite -[tApp _ _](mkApps_app hd _ [f2]).
  rewrite decompose_app_rec_eq; auto. now apply negbT.
  move=> [] H ->. subst f. exists 0. intuition auto.
  now apply negbT.
Qed.

Lemma mkApps_elim_rec t l l' :
  let app' := decompose_app_rec (mkApps t l) l' in
  mkApps_spec app'.1 app'.2 t (l ++ l') (mkApps t (l ++ l')).
Proof.
  destruct app' as [hd args] eqn:Heq.
  subst app'.
  rewrite decompose_app_rec_mkApps in Heq.
  have H := decompose_app_rec_inv' _ _ _ _ Heq.
  destruct H. simpl. destruct a as [isapp [Hl' Hl]].
  subst t.
  have H' := mkApps_intro hd args x. rewrite Hl'.
  rewrite -mkApps_app. now rewrite firstn_skipn.
Qed.

Lemma mkApps_elim t l  :
  let app' := decompose_app (mkApps t l) in
  mkApps_spec app'.1 app'.2 t l (mkApps t l).
Proof.
  have H := @mkApps_elim_rec t l [].
  now rewrite app_nil_r in H.
Qed.

Lemma mkApps_eq_inj {t t' l l'} :
  mkApps t l = mkApps t' l' ->
  ~~ isApp t -> ~~ isApp t' -> t = t' /\ l = l'.
Proof.
  intros Happ Ht Ht'. eapply (f_equal decompose_app) in Happ. unfold decompose_app in Happ.
  rewrite !decompose_app_rec_mkApps in Happ. rewrite !atom_decompose_app in Happ; auto.
  now rewrite !app_nil_r in Happ.
Qed.

Ltac solve_discr :=
  match goal with
    H : mkApps _ _ = mkApps ?f ?l |- _ =>
    eapply mkApps_eq_inj in H as [? ?]; [|easy|easy]; subst; try intuition congruence
  | H : ?t = mkApps ?f ?l |- _ =>
    change t with (mkApps t []) in H ;
    eapply mkApps_eq_inj in H as [? ?]; [|easy|easy]; subst; try intuition congruence
  | H : mkApps ?f ?l = ?t |- _ =>
    change t with (mkApps t []) in H ;
    eapply mkApps_eq_inj in H as [? ?]; [|easy|easy]; subst; try intuition congruence
  end.

Lemma atom_mkApps f l : atom (mkApps f l) -> (l = []) /\ atom f.
Proof.
  revert f; induction l using rev_ind. simpl. intuition auto.
  simpl. intros. now rewrite mkApps_app in H.
Qed.

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

Definition isCoFix t :=
  match t with
  | tCoFix _ _ => true
  | _ => false
  end.

Definition isConstruct t :=
  match t with
  | tConstruct _ _ => true
  | _ => false
  end.

Definition isBox t :=
  match t with
  | tBox => true
  | _ => false
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
           
  (** Fix unfolding, without guard *)
  | eval_fix mfix idx arg narg fn res :
      unfold_fix mfix idx = Some (narg, fn) ->
      (* We do not need to check the guard in the extracted language
         as we assume reduction of closed terms, whose canonical
         form will be a constructor or a box. A fixpoint must
         still be applied to at least one argument to unfold. *)
      eval (tApp fn arg) res ->
      eval (tApp (tFix mfix idx) arg) res

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
      ~~ (isLambda f' || isFix f' || isBox f') ->
      eval a a' ->
      eval (tApp f a) (tApp f' a')

  (** Evars complicate reasoning due to the embedded substitution, we skip
      them for now *)
  (* | eval_evar n l l' : *)
  (*     Forall2 eval l l' -> *)
  (*     eval (tEvar n l) (tEvar n l') *)


  (** Atoms are values (includes abstractions, cofixpoints and constructors) *)
  | eval_atom t : atom t -> eval t t.

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
  | value_app t l : value_head t -> Forall value l -> value (mkApps t l).

  Lemma value_values_ind : forall P : term -> Prop,
      (forall t, atom t -> P t) ->
      (* (forall n l l', Forall value l -> Forall P l -> Forall value l' -> Forall P l' -> *)
      (*                 P (mkApps (tEvar n l) l')) -> *)
      (forall t l, value_head t -> Forall value l -> Forall P l -> P (mkApps t l)) ->
      forall t : term, value t -> P t.
  Proof.
    intros P ??.
    fix value_values_ind 2. destruct 1. apply H; auto.
    eapply H0; auto.
    revert l H2. fix aux 2. destruct 1. constructor; auto.
    constructor. now eapply value_values_ind. now apply aux.
  Defined.

  Lemma value_head_nApp t : value_head t -> ~~ isApp t.
  Proof. destruct t; auto. Qed.
  Hint Resolve value_head_nApp : core.

  Lemma value_mkApps_inv t l :
    ~~ isApp t ->
    value (mkApps t l) ->
    (l = [] /\ atom t) \/ (value_head t /\ Forall value l).
  Proof.
    intros H H'. generalize_eqs H'. revert t H. induction H' using value_values_ind.
    intros.
    subst.
    - now eapply atom_mkApps in H.
    - intros * isapp appeq. solve_discr.
  Qed.

  (** The codomain of evaluation is only values: *)
  (*     It means no redex can remain at the head of an evaluated term. *)

  Lemma Forall_skipn {A} (P : A -> Prop) n l : Forall P l -> Forall P (skipn n l).
  Proof.
    intros H. revert n; induction H; intros n. rewrite skipn_nil; auto.
    destruct n; simpl.
    - rewrite /skipn. constructor; auto.
    - now auto.
  Qed.

  Lemma Forall_firstn {A} (P : A -> Prop) n l : Forall P l -> Forall P (firstn n l).
  Proof.
    intros H. revert n; induction H; intros n. rewrite firstn_nil; auto.
    destruct n; simpl.
    - constructor; auto.
    - constructor; auto.
  Qed.

  Lemma value_head_spec t :
    value_head t = (~~ (isLambda t || isFix t || isBox t)) && atom t.
  Proof.
    destruct t; intuition auto.
  Qed.

  Lemma eval_to_value e e' : eval e e' -> value e'.
  Proof.
    induction 1 using eval_ind; simpl; auto using value.
    (* eapply (value_app (tEvar n l') []). constructor. constructor. *)
    destruct (mkApps_elim f' []).
    eapply value_mkApps_inv in IHeval1.
    destruct IHeval1; intuition subst.
    rewrite H3.
    simpl. rewrite H3 in H0. simpl in *.
    apply (value_app f0 [a']).
    rewrite value_head_spec. now rewrite H0 H4.
    constructor; auto.
    rewrite -[tApp _ _](mkApps_app _ (firstn n l) [a']).
    constructor 2; auto. eapply app_Forall; auto. auto.
  Qed.

  Lemma Forall2_app_r {A} (P : A -> A -> Prop) l l' r r' : Forall2 P (l ++ [r]) (l' ++ [r']) ->
                                                           (Forall2 P l l') * (P r r').
  Proof.
    induction l in l', r |- *. simpl. intros. destruct l'. simpl in *.
    depelim H; intuition auto.
    depelim H. destruct l'; depelim H0.
    intros.
    depelim l'; depelim H. destruct l; depelim H0.
    specialize (IHl _ _ H0). intuition auto.
  Qed.

  Lemma value_final e : value e -> eval e e.
  Proof.
    induction 1 using value_values_ind; simpl; auto using value.
    now constructor.
    assert (Forall2 eval l l).
    induction H1; constructor; auto. eapply IHForall. now depelim H0.
    rewrite value_head_spec in H.
    induction l using rev_ind. simpl.
    move/andP: H => [H H'].
    constructor; try easy.
    rewrite mkApps_app.
    eapply Forall_app in H0 as [Hl Hx]. depelim Hx.
    eapply Forall2_app_r in H2 as [Hl' Hx'].
    eapply eval_app_cong; auto.
    eapply IHl. auto.
    now eapply Forall2_Forall. auto.
    move/andP: H => [Ht Ht'].
    destruct l using rev_ind; auto. now rewrite mkApps_app; simpl.
  Qed.

  (* (** Evaluation preserves closedness: *) *)
  (* Lemma eval_closed : forall n t u, closedn n t = true -> eval t u -> closedn n u = true. *)
  (* Proof. *)
  (*   induction 2 using eval_ind; simpl in *; auto. eapply IHeval3. *)
  (*   admit. *)
  (* Admitted. (* closedness of evaluates for Eterms, not needed for verification *) *)

  Lemma eval_tApp_tFix_inv mfix idx a v :
    eval (tApp (tFix mfix idx) a) v ->
    (exists fn arg,
        (unfold_fix mfix idx = Some (arg, fn)) /\
        (eval (tApp fn a) v)).
  Proof.
    intros H; depind H; try solve_discr.
    - depelim H.
    - depelim H.
    - eexists _, _; firstorder eauto.
    - now depelim H.
    - discriminate.
  Qed.

  Lemma eval_tBox t : eval tBox t -> t = tBox.
  Proof.
    intros H; depind H; try solve_discr. auto.
  Qed.

  Lemma eval_tRel n t : eval (tRel n) t -> False.
  Proof.
    intros H; depind H; try solve_discr; try now easy.
  Qed.

  Lemma eval_tVar i t : eval (tVar i) t -> False.
  Proof.
    intros H; depind H; try solve_discr; try now easy.
  Qed.

  Lemma eval_tEvar n l t : eval (tEvar n l) t -> False.
                          (* exists l', Forall2 eval l l' /\ (t = tEvar n l'). *)
  Proof.
    intros H; depind H; try solve_discr; try now easy.
  Qed.

  Lemma eval_atom_inj t t' : atom t -> eval t t' -> t = t'.
  Proof.
    intros Ha H; depind H; try solve_discr; try now easy.
  Qed.

  Lemma eval_LetIn {n b t v} :
    eval (tLetIn n b t) v ->
    exists b',
      eval b b' /\ eval (t {0 := b'}) v.
  Proof.
    intros H; depind H; try solve_discr; try now easy.
  Qed.

  Lemma eval_Const {c v} :
    eval (tConst c) v ->
    exists decl body, declared_constant Σ c decl /\
                      cst_body decl = Some body /\
                      eval body v.
  Proof.
    intros H; depind H; try solve_discr; try now easy.
    exists decl, body. intuition auto.
  Qed.

  Lemma eval_mkApps_tCoFix mfix idx l v :
    eval (mkApps (tCoFix mfix idx) l) v ->
    (exists l', Forall2 eval l l' /\ (v = mkApps (tCoFix mfix idx) l')).
  Proof.
    intros H.
    depind H; try solve_discr.
    destruct (mkApps_elim a [t]).
    rewrite -[tApp _ _](mkApps_app f (firstn n l0) [t]) in x.
    solve_discr.
    specialize (IHeval1 _ _ _ eq_refl).
    firstorder eauto.
    solve_discr.
    destruct (mkApps_elim f [a]).
    rewrite -[tApp _ _](mkApps_app f (firstn n l0) [a]) in x. solve_discr.
    specialize (IHeval1 _ _ _ eq_refl).
    firstorder eauto. solve_discr.
    change (tApp (tFix mfix0 idx0) arg) with (mkApps (tFix mfix0 idx0) [arg]) in x.
    solve_discr.
    change (tApp f a) with (mkApps f [a]) in x.
    assert (l <> []).
    destruct l; simpl in *; discriminate.
    rewrite (app_removelast_last a H2) in x |- *.
    rewrite mkApps_app in x. simpl in x. inv x.
    specialize (IHeval1 _ _ _ eq_refl).
    destruct IHeval1 as [l' [evl' eqf']].
    exists (l' ++ [a']).
    split. eapply Forall2_app; auto. constructor. now rewrite - !H5. constructor.
    subst f'.
    now rewrite mkApps_app.
    eapply atom_mkApps in H; intuition try easy.
    subst.
    exists []. intuition auto.
  Qed.

  Lemma eval_deterministic {t v v'} : eval t v -> eval t v' -> v = v'.
  Proof.
    intros tv. revert v'.
    revert t v tv.
    induction 1 using eval_ind; intros v' tv'.
    - depelim tv'; auto. specialize (IHtv1 _ tv'1); congruence.
      depelim tv1. specialize (IHtv1 _ tv'1). now subst. easy.
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

    - depelim tv'; try easy.
      * eapply eval_mkApps_tCoFix in tv'1 as [l' [evargs eq]].
        solve_discr.
      * eapply eval_mkApps_tCoFix in tv'1 as [l' [evargs eq]].
        solve_discr.
      * solve_discr. inv H1. rewrite H in H0. inv H0.
        now specialize (IHtv _ tv').

    - depelim tv'; try easy.
      * solve_discr. inv H1. rewrite H in H0. inv H0.
        now specialize (IHtv _ tv').
      * eapply eval_mkApps_tCoFix in tv'1 as [l' [evargs eq]].
        solve_discr.
      * eapply eval_mkApps_tCoFix in tv' as [l' [evargs eq]].
        solve_discr.

    - eapply eval_Const in tv' as [decl' [body' [? ?]]].
      intuition eauto. eapply IHtv.
      red in isdecl, H0. rewrite H0 in isdecl. inv isdecl.
      now rewrite H in H2; inv H2.

    - depelim tv'.
      * eapply eval_mkApps_tCoFix in tv1 as [l' [evargs eq]].
        solve_discr.
      * specialize (IHtv1 _ tv'1). 
        solve_discr. inv H.
        now specialize (IHtv2 _ tv'2).
      * specialize (IHtv1 _ tv'). solve_discr.
      * easy.

    - depelim tv'; try easy.
      * eapply eval_mkApps_tCoFix in tv as [l' [evargs eq]].
        solve_discr.
      * specialize (IHtv _ tv'1). solve_discr.

    - depelim tv'; try specialize (IHtv1 _ tv'1); subst; try easy.
      depelim tv1. easy.
      specialize (IHtv2 _ tv'2). congruence.

    - depelim tv'; try easy.
  Qed.

  Lemma eval_mkApps_cong f f' l l' :
    eval f f' ->
    value_head f' ->
    Forall2 eval l l' ->
    eval (mkApps f l) (mkApps f' l').
  Proof.
    revert l'. induction l using rev_ind; intros l' evf vf' evl.
    depelim evl. eapply evf.
    eapply Forall2_app_inv_l in evl as [? [? [? ?]]].
    intuition auto. subst. depelim H1. depelim H1.
    rewrite !mkApps_app /=. eapply eval_app_cong; auto.
    destruct x0 using rev_ind; simpl; [|rewrite !mkApps_app]; simpl in *; destruct f';
      try discriminate; constructor.
  Qed.

End Wcbv.
