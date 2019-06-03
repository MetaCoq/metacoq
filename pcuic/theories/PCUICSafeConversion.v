(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia
     Classes.RelationClasses Omega.
From MetaCoq.Template Require Import config Universes monad_utils utils BasicAst
     AstUtils UnivSubst.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICReflect PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICSafeReduce
     PCUICCumulativity PCUICSR PCUICPosition PCUICEquality PCUICNameless
     PCUICSafeLemmata PCUICNormal.
From Equations Require Import Equations.

Require Import Equations.Prop.DepElim.

Import MonadNotation.

Module PSR := PCUICSafeReduce.

(** * Conversion for PCUIC without fuel

  Following PCUICSafereduce, we derive a fuel-free implementation of
  conversion (and cumulativity) checking for PCUIC.

 *)

Section Conversion.

  Context (flags : RedFlags.t).
  Context (Σ : global_context).
  Context (hΣ : wf Σ).

  Set Equations With UIP.

  Inductive state :=
  | Reduction (t : term)
  | Term (t : term)
  | Args
  | Fallback (t : term).

  Inductive stateR : state -> state -> Prop :=
  | stateR_Term_Reduction : forall u v, stateR (Term u) (Reduction v)
  | stateR_Arg_Term : forall u, stateR Args (Term u)
  | stateR_Fallback_Term : forall u v, stateR (Fallback u) (Term v).

  Derive Signature for stateR.

  Lemma stateR_Acc :
    forall s, Acc stateR s.
  Proof.
    assert (Acc stateR Args) as hArgs.
    { constructor. intros s h.
      dependent induction h.
      all: discriminate.
    }
    assert (forall t, Acc stateR (Fallback t)) as hFall.
    { intros t. constructor. intros s h.
      dependent induction h.
      all: discriminate.
    }
    assert (forall t, Acc stateR (Term t)) as hTerm.
    { intros t. constructor. intros s h.
      dependent induction h.
      all: try discriminate.
      - apply hArgs.
      - apply hFall.
    }
    assert (forall t, Acc stateR (Reduction t)) as hRed.
    { intros t. constructor. intros s h.
      dependent induction h.
      all: try discriminate.
      apply hTerm.
    }
    intro s. destruct s ; eauto.
  Qed.

  Notation wtp Γ t π :=
    (welltyped Σ [] (zipx Γ t π)) (only parsing).

  Definition wts Γ s t π :=
    match s with
    | Reduction t'
    | Fallback t'
    | Term t' => wtp Γ t' π
    | Args => wtp Γ t π
    end.

  Set Primitive Projections.

  Record pack := mkpack {
    st : state ;
    ctx : context ;
    tm : term ;
    stk1 : stack ;
    stk2 : stack ;
    tm' := match st with
           | Reduction t | Fallback t | Term t => t
           | Args => tm
           end ;
    wth : welltyped Σ [] (zipx ctx tm' stk2)
  }.

  Record nlpack := mknlpack {
    nl_st : state ;
    nl_ctx : context ;
    nl_tm : term ;
    nl_stk1 : stack ;
    nl_stk2 : stack ;
    nl_tm' := match nl_st with
           | Reduction t | Fallback t | Term t => t
           | Args => nl_tm
           end ;
    nl_wth : welltyped (nlg Σ) [] (zipx nl_ctx nl_tm' nl_stk2)
  }.

  Definition nlstate (s : state) :=
    match s with
    | Reduction t => Reduction (nl t)
    | Term t => Term (nl t)
    | Args => Args
    | Fallback t => Fallback (nl t)
    end.

  Definition nl_pack (p : pack) : nlpack.
  Proof.
    destruct p as [s Γ t π1 π2 t' h].
    unshelve eexists.
    - exact (nlstate s).
    - exact (nlctx Γ).
    - exact (nl t).
    - exact (nlstack π2).
    - exact (nlstack π1).
    - eapply welltyped_nlg ; auto.
      eapply welltyped_rename ; auto.
      + exact h.
      + destruct s.
        * cbn. rewrite <- nl_zipx.
          eapply eq_term_tm_nl.
        * cbn. rewrite <- nl_zipx.
          eapply eq_term_tm_nl.
        * cbn. rewrite <- nl_zipx.
          eapply eq_term_tm_nl.
        * cbn. rewrite <- nl_zipx.
          eapply eq_term_tm_nl.
  Defined.

  Definition wterm Γ := { t : term | welltyped (nlg Σ) Γ t }.

  Definition wcored Γ (u v : wterm Γ) :=
    cored (nlg Σ) Γ (` u) (` v).

  Lemma wcored_wf :
    forall Γ, well_founded (wcored Γ).
  Proof.
    intros Γ [u hu].
    pose proof (normalisation _ _ _ hu) as h.
    dependent induction h.
    constructor. intros [y hy] r.
    unfold wcored in r. cbn in r.
    eapply H0. assumption.
  Qed.

  Definition R_aux :=
    t ⊩ cored (nlg Σ) [] ⨶ @posR t ⊗ w ⊩ wcored [] ⨶ @posR (` w) ⊗ stateR.

  Notation nl_pzt u := (zipx (nl_ctx u) (nl_tm u) (nl_stk1 u)) (only parsing).
  Notation nl_pps1 u := (xpos (nl_ctx u) (nl_tm u) (nl_stk1 u)) (only parsing).
  Notation nl_pwt u := (exist _ (nl_wth u)) (only parsing).
  Notation nl_pps2 u := (xpos (nl_ctx u) (nl_tm' u) (nl_stk2 u)) (only parsing).

  Notation obpack u :=
    (nl_pzt u ; (nl_pps1 u, (nl_pwt u ; (nl_pps2 u, nl_st u)))) (only parsing).

  Definition R_nl (u v : nlpack) :=
    R_aux (obpack u) (obpack v).

  Definition R (u v : pack) :=
    R_nl (nl_pack u) (nl_pack v).

  Notation pzt u := (zipx (ctx u) (tm u) (stk1 u)) (only parsing).
  Notation pps1 u := (xpos (ctx u) (tm u) (stk1 u)) (only parsing).
  Notation pwt u := (exist _ (wth u)) (only parsing).
  Notation pps2 u := (xpos (ctx u) (tm' u) (stk2 u)) (only parsing).

  Lemma R_aux_Acc :
    forall t p w q s,
      welltyped (nlg Σ) [] t ->
      Acc R_aux (t ; (p, (w ; (q, s)))).
  Proof.
    intros t p w q s ht.
    eapply dlexprod_Acc.
    - intro u. eapply Subterm.wf_lexprod.
      + intro. eapply posR_Acc.
      + intros [w' q']. eapply dlexprod_Acc.
        * intros [t' h']. eapply Subterm.wf_lexprod.
          -- intro. eapply posR_Acc.
          -- intro. eapply stateR_Acc.
        * eapply wcored_wf.
    - eapply normalisation. eassumption.
  Qed.

  Lemma R_Acc :
    forall u,
      welltyped (nlg Σ) [] (zipx (ctx u) (tm u) (stk1 u)) ->
      Acc R u.
  Proof.
    intros u h.
    eapply Acc_fun with (f := fun x => obpack (nl_pack x)).
    apply R_aux_Acc.
    rewrite <- nl_zipx.
    eapply welltyped_rename ; auto.
    - eapply wf_nlg ; auto.
    - eassumption.
    - eapply eq_term_tm_nl.
  Qed.

  Lemma R_cored :
    forall p1 p2,
      cored Σ [] (pzt p1) (pzt p2) ->
      R p1 p2.
  Proof.
    intros p1 p2 h.
    left. rewrite <- 2!nl_zipx.
    change [] with (nlctx []).
    eapply cored_nl ; auto.
  Qed.

  Lemma R_aux_positionR :
    forall t1 t2 (p1 : pos t1) (p2 : pos t2) s1 s2,
      t1 = t2 ->
      positionR (` p1) (` p2) ->
      R_aux (t1 ; (p1, s1)) (t2 ; (p2, s2)).
  Proof.
    intros t1 t2 p1 p2 s1 s2 e h.
    subst. right. left. assumption.
  Qed.

  Lemma R_positionR :
    forall p1 p2,
      nl (pzt p1) = nl (pzt p2) ->
      positionR (` (pps1 p1)) (` (pps1 p2)) ->
      R p1 p2.
  Proof.
    intros [s1 Γ1 t1 π1 ρ1 t1' h1] [s2 Γ2 t2 π2 ρ2 t2' h2] e h. simpl in *.
    eapply R_aux_positionR ; simpl.
    - rewrite <- 2!nl_zipx. assumption.
    - rewrite 2!xposition_nlctx, 2!xposition_nlstack.
      assumption.
  Qed.

  Lemma R_aux_cored2 :
    forall t1 t2 (p1 : pos t1) (p2 : pos t2) w1 w2 q1 q2 s1 s2,
      t1 = t2 ->
      ` p1 = ` p2 ->
      cored (nlg Σ) [] (` w1) (` w2) ->
      R_aux (t1 ; (p1, (w1 ; (q1, s1)))) (t2 ; (p2, (w2 ; (q2, s2)))).
  Proof.
    intros t1 t2 [p1 hp1] [p2 hp2] [t1' h1'] [t2' h2'] q1 q2 s1 s2 e1 e2 h.
    cbn in e2. cbn in h. subst.
    pose proof (uip hp1 hp2). subst.
    right. right. left. assumption.
  Qed.

  Lemma R_cored2 :
    forall p1 p2,
      nl (pzt p1) = nl (pzt p2) ->
      ` (pps1 p1) = ` (pps1 p2) ->
      cored Σ [] (` (pwt p1)) (` (pwt p2)) ->
      R p1 p2.
  Proof.
    intros [s1 Γ1 t1 π1 ρ1 t1' h1] [s2 Γ2 t2 π2 ρ2 t2' h2] e1 e2 h. simpl in *.
    eapply R_aux_cored2 ; simpl.
    - rewrite <- 2!nl_zipx. assumption.
    - rewrite 2!xposition_nlctx, 2!xposition_nlstack. assumption.
    - destruct s1, s2 ; simpl.
      all: rewrite <- 2!nl_zipx.
      all: change [] with (nlctx []).
      all: eapply cored_nl ; auto.
  Qed.

  (* TODO Here we assume that welltyped is really squashed, which should be ok
     if we defined it in SProp probably.
     NOTE We will have to put the squash in SProp as well, but that's not too big a deal.
   *)
  Axiom welltyped_irr :
    forall {Σ Γ t} (h1 h2 : welltyped Σ Γ t), h1 = h2.

  Lemma R_aux_positionR2 :
    forall t1 t2 (p1 : pos t1) (p2 : pos t2) w1 w2 q1 q2 s1 s2,
      t1 = t2 ->
      ` p1 = ` p2 ->
      ` w1 = ` w2 ->
      positionR (` q1) (` q2) ->
      R_aux (t1 ; (p1, (w1 ; (q1, s1)))) (t2 ; (p2, (w2 ; (q2, s2)))).
  Proof.
    intros t1 t2 [p1 hp1] [p2 hp2] [t1' h1'] [t2' h2'] q1 q2 s1 s2 e1 e2 e3 h.
    cbn in e2. cbn in e3. subst.
    pose proof (uip hp1 hp2). subst.
    pose proof (welltyped_irr h1' h2'). subst.
    right. right. right. left. assumption.
  Qed.

  Lemma R_positionR2 :
    forall p1 p2,
      nl (pzt p1) = nl (pzt p2) ->
      ` (pps1 p1) = ` (pps1 p2) ->
      nl (` (pwt p1)) = nl (` (pwt p2)) ->
      positionR (` (pps2 p1)) (` (pps2 p2)) ->
      R p1 p2.
  Proof.
    intros [s1 Γ1 t1 π1 ρ1 t1' h1] [s2 Γ2 t2 π2 ρ2 t2' h2] e1 e2 e3 h.
    simpl in *.
    eapply R_aux_positionR2 ; simpl.
    - rewrite <- 2!nl_zipx. assumption.
    - rewrite 2!xposition_nlctx, 2!xposition_nlstack. assumption.
    - destruct s1, s2 ; simpl.
      all: rewrite <- 2!nl_zipx. all: assumption.
    - rewrite 2!xposition_nlctx, 2!xposition_nlstack. assumption.
  Qed.

  Lemma R_aux_stateR :
    forall t1 t2 (p1 : pos t1) (p2 : pos t2) w1 w2 q1 q2 s1 s2 ,
      t1 = t2 ->
      ` p1 = ` p2 ->
      ` w1 = ` w2 ->
      ` q1 = ` q2 ->
      stateR s1 s2 ->
      R_aux (t1 ; (p1, (w1 ; (q1, s1)))) (t2 ; (p2, (w2 ; (q2, s2)))).
  Proof.
    intros t1 t2 [p1 hp1] [p2 hp2] [t1' h1'] [t2' h2'] [q1 hq1] [q2 hq2] s1 s2
           e1 e2 e3 e4 h.
    cbn in e2. cbn in e3. cbn in e4. subst.
    pose proof (uip hp1 hp2). subst.
    pose proof (welltyped_irr h1' h2'). subst.
    pose proof (uip hq1 hq2). subst.
    right. right. right. right. assumption.
  Qed.

  Lemma R_stateR :
    forall p1 p2,
      nl (pzt p1) = nl (pzt p2) ->
      ` (pps1 p1) = ` (pps1 p2) ->
      nl (` (pwt p1)) = nl (` (pwt p2)) ->
      ` (pps2 p1) = ` (pps2 p2) ->
      stateR (st p1) (st p2) ->
      R p1 p2.
  Proof.
    intros [s1 Γ1 t1 π1 ρ1 t1' h1] [s2 Γ2 t2 π2 ρ2 t2' h2] e1 e2 e3 e4 h.
    simpl in *.
    eapply R_aux_stateR ; simpl.
    - rewrite <- 2!nl_zipx. assumption.
    - rewrite 2!xposition_nlctx, 2!xposition_nlstack. assumption.
    - destruct s1, s2 ; simpl.
      all: rewrite <- 2!nl_zipx. all: assumption.
    - rewrite 2!xposition_nlctx, 2!xposition_nlstack. assumption.
    - induction h ; constructor.
  Qed.

  Lemma zwts :
    forall {Γ s t π},
      wts Γ s t π ->
      welltyped Σ [] (zipx Γ match s with Reduction u | Fallback u | Term u => u | Args => t end π).
  Proof.
    intros Γ s t π h.
    destruct s ; assumption.
  Defined.

  Definition Ret s Γ t π π' :=
    match s with
    | Reduction t' =>
      forall leq, { b : bool | if b then conv leq Σ Γ (zippx t π) (zippx t' π') else True }
    | Fallback t'
    | Term t' =>
      forall leq,
        isred (t, π) ->
        isred (t', π') ->
        { b : bool | if b then conv leq Σ Γ (zippx t π) (zippx t' π') else True }
    | Args =>
      { b : bool | if b then ∥ Σ ;;; Γ |- zippx t π = zippx t π' ∥ else True }
    end.

  Definition Aux s Γ t π1 π2 h2 :=
     forall s' Γ' t' π1' π2'
       (h1' : wtp Γ' t' π1')
       (h2' : wts Γ' s' t' π2'),
       R (mkpack s' Γ' t' π1' π2' (zwts h2'))
         (mkpack s Γ t π1 π2 (zwts h2)) ->
       Ret s' Γ' t' π1' π2'.

  Notation no := (exist false I) (only parsing).
  Notation yes := (exist true _) (only parsing).

  Notation repack e := (let '(exist b h) := e in exist b _) (only parsing).

  Notation isconv_red_raw Γ leq t1 π1 t2 π2 aux :=
    (aux (Reduction t2) Γ t1 π1 π2 _ _ _ leq) (only parsing).
  Notation isconv_prog_raw Γ leq t1 π1 t2 π2 aux :=
    (aux (Term t2) Γ t1 π1 π2 _ _ _ leq _ _) (only parsing).
  Notation isconv_args_raw Γ t π1 π2 aux :=
    (aux Args Γ t π1 π2 _ _ _) (only parsing).
  Notation isconv_fallback_raw Γ leq t1 π1 t2 π2 aux :=
    (aux (Fallback t2) Γ t1 π1 π2 _ _ _ leq _ _) (only parsing).

  Notation isconv_red Γ leq t1 π1 t2 π2 aux :=
    (repack (isconv_red_raw Γ leq t1 π1 t2 π2 aux)) (only parsing).
  Notation isconv_prog Γ leq t1 π1 t2 π2 aux :=
    (repack (isconv_prog_raw Γ leq t1 π1 t2 π2 aux)) (only parsing).
  Notation isconv_args Γ t π1 π2 aux :=
    (repack (isconv_args_raw Γ t π1 π2 aux)) (only parsing).
  Notation isconv_fallback Γ leq t1 π1 t2 π2 aux :=
    (repack (isconv_fallback_raw Γ leq t1 π1 t2 π2 aux)) (only parsing).

  Equations(noeqns) _isconv_red (Γ : context) (leq : conv_pb)
            (t1 : term) (π1 : stack) (h1 : wtp Γ t1 π1)
            (t2 : term) (π2 : stack) (h2 : wtp Γ t2 π2)
            (aux : Aux (Reduction t2) Γ t1 π1 π2 h2)
    : { b : bool | if b then conv leq Σ Γ (zippx t1 π1) (zippx t2 π2) else True } :=

    _isconv_red Γ leq t1 π1 h1 t2 π2 h2 aux
    with inspect (decompose_stack π1) := {
    | @exist (args1, ρ1) e1 with inspect (decompose_stack π2) := {
      | @exist (args2, ρ2) e2
        with inspect (reduce_stack nodelta_flags Σ (Γ ,,, stack_context π1) t1 (appstack args1 ε) _) := {
        | @exist (t1',π1') eq1
          with inspect (reduce_stack nodelta_flags Σ (Γ ,,, stack_context π2) t2 (appstack args2 ε) _) := {
          | @exist (t2',π2') eq2 => isconv_prog Γ leq t1' (π1' +++ ρ1) t2' (π2' +++ ρ2) aux
          }
        }
      }
    }.
  Next Obligation.
    apply welltyped_zipx in h1.
    apply welltyped_zipc_zippx in h1 ; try assumption.
    cbn. rewrite zipc_appstack. cbn.
    unfold zippx in h1. rewrite <- e1 in h1.
    apply welltyped_it_mkLambda_or_LetIn in h1.
    pose proof (decompose_stack_eq _ _ _ (eq_sym e1)). subst.
    rewrite stack_context_appstack. assumption.
  Qed.
  Next Obligation.
    clear aux eq1.
    apply welltyped_zipx in h2.
    apply welltyped_zipc_zippx in h2 ; try assumption.
    cbn. rewrite zipc_appstack. cbn.
    unfold zippx in h2. rewrite <- e2 in h2.
    apply welltyped_it_mkLambda_or_LetIn in h2.
    pose proof (decompose_stack_eq _ _ _ (eq_sym e2)). subst.
    rewrite stack_context_appstack. assumption.
  Qed.
  Next Obligation.
    match type of eq1 with
    | _ = reduce_stack ?f ?Σ ?Γ ?t ?π ?h =>
      destruct (reduce_stack_sound f Σ Γ t π h) as [r1] ;
      pose proof (reduce_stack_decompose nodelta_flags _ _ _ _ h) as d1 ;
      pose proof (reduce_stack_context f Σ Γ t π h) as c1
    end.
    rewrite <- eq1 in r1.
    rewrite <- eq1 in d1. cbn in d1.
    rewrite <- eq1 in c1. cbn in c1.
    rewrite stack_context_appstack in c1. cbn in c1.

    pose proof (decompose_stack_eq _ _ _ (eq_sym e1)). subst.
    clear eq1 eq2.
    apply welltyped_zipx in h1.
    rewrite zipc_appstack in h1.
    case_eq (decompose_stack π1'). intros args1' ρ1' e1'.
    rewrite e1' in d1. cbn in d1.
    rewrite decompose_stack_appstack in d1. cbn in d1. subst.
    pose proof (decompose_stack_eq _ _ _ e1'). subst.
    rewrite stack_cat_appstack.
    eapply zipx_welltyped ; try assumption.
    rewrite zipc_appstack.

    rewrite stack_context_appstack in r1. cbn in r1.
    rewrite 2!zipc_appstack in r1. cbn in r1.

    eapply red_welltyped ; try assumption ; revgoals.
    - constructor. zip fold. eapply red_context. eassumption.
    - cbn. assumption.
  Qed.
  Next Obligation.
    match type of eq2 with
    | _ = reduce_stack ?f ?Σ ?Γ ?t ?π ?h =>
      destruct (reduce_stack_sound f Σ Γ t π h) as [r2] ;
      pose proof (reduce_stack_decompose nodelta_flags _ _ _ _ h) as d2 ;
      pose proof (reduce_stack_context f Σ Γ t π h) as c2
    end.
    rewrite <- eq2 in r2.
    rewrite <- eq2 in d2. cbn in d2.
    rewrite <- eq2 in c2. cbn in c2.
    rewrite stack_context_appstack in c2. cbn in c2.

    pose proof (decompose_stack_eq _ _ _ (eq_sym e2)). subst.
    clear eq1 eq2 aux.
    apply welltyped_zipx in h2.
    rewrite zipc_appstack in h2.
    case_eq (decompose_stack π2'). intros args2' ρ2' e2'.
    rewrite e2' in d2. cbn in d2.
    rewrite decompose_stack_appstack in d2. cbn in d2. subst.
    pose proof (decompose_stack_eq _ _ _ e2'). subst.
    rewrite stack_cat_appstack.
    eapply zipx_welltyped ; try assumption.
    rewrite zipc_appstack.

    rewrite stack_context_appstack in r2. cbn in r2.
    rewrite 2!zipc_appstack in r2. cbn in r2.

    eapply red_welltyped ; try assumption ; revgoals.
    - constructor. zip fold. eapply red_context. eassumption.
    - cbn. assumption.
  Qed.
  Next Obligation.
    match type of eq1 with
    | _ = reduce_stack ?f ?Σ ?Γ ?t ?π ?h =>
      pose proof (reduce_stack_decompose nodelta_flags _ _ _ _ h) as d1 ;
      pose proof (reduce_stack_context f Σ Γ t π h) as c1
    end.
    rewrite <- eq1 in d1. cbn in d1.
    rewrite <- eq1 in c1. cbn in c1.
    rewrite stack_context_appstack in c1. cbn in c1.
    pose proof (decompose_stack_eq _ _ _ (eq_sym e1)). subst.
    match type of eq1 with
    | _ = reduce_stack ?f ?Σ ?Γ ?t ?π ?hh =>
      pose proof (reduce_stack_Req f _ _ _ _ hh) as [ e | h ]
    end.
    - assert (ee1 := eq1). rewrite e in ee1. inversion ee1. subst.
      match type of eq2 with
      | _ = reduce_stack ?f ?Σ ?Γ ?t ?π ?h =>
        pose proof (reduce_stack_decompose nodelta_flags _ _ _ _ h) as d2 ;
        pose proof (reduce_stack_context f Σ Γ t π h) as c2
      end.
      rewrite <- eq2 in d2. cbn in d2.
      rewrite <- eq2 in c2. cbn in c2.
      rewrite stack_context_appstack in c2. cbn in c2.
      pose proof (decompose_stack_eq _ _ _ (eq_sym e2)). subst.
      match type of eq2 with
      | _ = reduce_stack ?f ?Σ ?Γ ?t ?π ?hh =>
        pose proof (reduce_stack_Req f _ _ _ _ hh) as [ ee | h ]
      end.
      + assert (ee2 := eq2). rewrite ee in ee2. inversion ee2. subst.
        unshelve eapply R_stateR.
        * simpl. rewrite stack_cat_appstack. reflexivity.
        * simpl. rewrite stack_cat_appstack. reflexivity.
        * simpl. rewrite stack_cat_appstack. reflexivity.
        * simpl. rewrite stack_cat_appstack. reflexivity.
        * simpl. constructor.
      + rewrite <- eq2 in h.
        rewrite stack_context_appstack in h.
        dependent destruction h.
        * cbn in H. rewrite zipc_appstack in H. cbn in H.
          unshelve eapply R_cored2.
          -- simpl. rewrite stack_cat_appstack. reflexivity.
          -- simpl. rewrite stack_cat_appstack. reflexivity.
          -- simpl.
             eapply cored_it_mkLambda_or_LetIn.
             rewrite app_context_nil_l.
             rewrite zipc_appstack. rewrite zipc_stack_cat.
             repeat zip fold. eapply cored_context.
             assumption.
        * destruct y' as [q hq].
          cbn in H0. inversion H0. subst.
          unshelve eapply R_positionR2.
          -- simpl. rewrite stack_cat_appstack. reflexivity.
          -- simpl. rewrite stack_cat_appstack. reflexivity.
          -- simpl. unfold zipx. f_equal. f_equal.
             rewrite zipc_stack_cat.
             rewrite <- H2.
             rewrite 2!zipc_appstack. cbn. reflexivity.
          -- simpl. unfold xposition. eapply positionR_poscat.
             unfold posR in H. cbn in H.
             rewrite stack_position_appstack in H. cbn in H.
             rewrite stack_position_stack_cat.
             rewrite stack_position_appstack.
             eapply positionR_poscat.
             assumption.
    - rewrite <- eq1 in h.
      rewrite stack_context_appstack in h.
      dependent destruction h.
      + cbn in H. rewrite zipc_appstack in H. cbn in H.
        eapply R_cored. simpl. eapply cored_it_mkLambda_or_LetIn.
        rewrite app_context_nil_l.
        rewrite zipc_appstack. rewrite zipc_stack_cat.
        repeat zip fold. eapply cored_context.
        assumption.
      + destruct y' as [q hq].
        cbn in H0. inversion H0. (* Why is noconf failing at this point? *)
        subst.
        unshelve eapply R_positionR ; simpl.
        * unfold zipx. f_equal. f_equal.
          rewrite zipc_stack_cat.
          rewrite <- H2.
          rewrite 2!zipc_appstack. cbn. reflexivity.
        * unfold xposition. eapply positionR_poscat.
          unfold posR in H. cbn in H.
          rewrite stack_position_appstack in H. cbn in H.
          rewrite stack_position_stack_cat.
          rewrite stack_position_appstack.
          eapply positionR_poscat.
          assumption.
  Qed.
  Next Obligation.
    match type of eq1 with
    | _ = reduce_stack ?f ?Σ ?Γ ?t ?π ?h =>
      pose proof (reduce_stack_isred f Σ Γ t π h eq_refl) as r1
    end.
    rewrite <- eq1 in r1. destruct r1 as [ha hl].
    split.
    - assumption.
    - cbn in hl. cbn. intro h.
      specialize (hl h).
      destruct π1'.
      all: try reflexivity.
      + cbn. destruct ρ1.
        all: try reflexivity.
        exfalso.
        apply (decompose_stack_not_app _ _ _ _ (eq_sym e1)).
      + discriminate hl.
  Qed.
  Next Obligation.
    match type of eq2 with
    | _ = reduce_stack ?f ?Σ ?Γ ?t ?π ?h =>
      pose proof (reduce_stack_isred f Σ Γ t π h eq_refl) as r2
    end.
    rewrite <- eq2 in r2. destruct r2 as [ha hl].
    split.
    - assumption.
    - cbn in hl. cbn. intro h.
      specialize (hl h).
      destruct π2'.
      all: try reflexivity.
      + cbn. destruct ρ2.
        all: try reflexivity.
        exfalso.
        apply (decompose_stack_not_app _ _ _ _ (eq_sym e2)).
      + discriminate hl.
  Qed.
  Next Obligation.
    destruct b ; auto.
    unfold zippx. rewrite <- e1. rewrite <- e2.

    match type of eq1 with
    | _ = reduce_stack ?f ?Σ ?Γ ?t ?π ?h =>
      destruct (reduce_stack_sound f Σ Γ t π h) as [r1] ;
      pose proof (reduce_stack_decompose nodelta_flags _ _ _ _ h) as d1 ;
      pose proof (reduce_stack_context f Σ Γ t π h) as c1
    end.
    rewrite <- eq1 in r1.
    rewrite <- eq1 in d1. cbn in d1.
    rewrite <- eq1 in c1. cbn in c1.
    rewrite stack_context_appstack in c1. cbn in c1.

    match type of eq2 with
    | _ = reduce_stack ?f ?Σ ?Γ ?t ?π ?h =>
      destruct (reduce_stack_sound f Σ Γ t π h) as [r2] ;
      pose proof (reduce_stack_decompose nodelta_flags _ _ _ _ h) as d2 ;
      pose proof (reduce_stack_context f Σ Γ t π h) as c2
    end.
    rewrite <- eq2 in r2.
    rewrite <- eq2 in d2. cbn in d2.
    rewrite <- eq2 in c2. cbn in c2.
    rewrite stack_context_appstack in c2. cbn in c2.

    clear eq1 eq2.

    pose proof (decompose_stack_eq _ _ _ (eq_sym e1)). subst.
    case_eq (decompose_stack π1'). intros args1' ρ1' e1'.
    rewrite e1' in d1. cbn in d1.
    rewrite decompose_stack_appstack in d1. cbn in d1. subst.
    pose proof (decompose_stack_eq _ _ _ e1'). subst.

    pose proof (decompose_stack_eq _ _ _ (eq_sym e2)). subst.
    case_eq (decompose_stack π2'). intros args2' ρ2' e2'.
    rewrite e2' in d2. cbn in d2.
    rewrite decompose_stack_appstack in d2. cbn in d2. subst.
    pose proof (decompose_stack_eq _ _ _ e2'). subst.

    rewrite stack_context_appstack in r1. cbn in r1.
    rewrite 2!zipc_appstack in r1. cbn in r1.

    rewrite stack_context_appstack in r2. cbn in r2.
    rewrite 2!zipc_appstack in r2. cbn in r2.

    rewrite 2!stack_cat_appstack in h.
    unfold zippx in h.
    rewrite 2!decompose_stack_appstack in h.
    rewrite decompose_stack_twice with (1 := eq_sym e1) in h.
    rewrite decompose_stack_twice with (1 := eq_sym e2) in h.
    simpl in h.
    rewrite 2!app_nil_r in h.

    eapply conv_trans'.
    - eapply red_conv_l.
      eapply red_it_mkLambda_or_LetIn.
      eassumption.
    - eapply conv_trans'.
      + eassumption.
      + eapply red_conv_r.
        eapply red_it_mkLambda_or_LetIn.
        assumption.
  Qed.

  Equations unfold_one_fix (Γ : context) (mfix : mfixpoint term)
            (idx : nat) (π : stack) (h : wtp Γ (tFix mfix idx) π)
    : option (term * stack) :=

    unfold_one_fix Γ mfix idx π h with inspect (unfold_fix mfix idx) := {
    | @exist (Some (arg, fn)) eq1 with inspect (decompose_stack_at π arg) := {
      | @exist (Some (l, c, θ)) eq2 with inspect (reduce_stack RedFlags.default Σ (Γ ,,, stack_context θ) c ε _) := {
        | @exist (cred, ρ) eq3 with construct_viewc cred := {
          | view_construct ind n ui := Some (fn, appstack l (App (zipc (tConstruct ind n ui) ρ) θ)) ;
          | view_other t h := None
          }
        } ;
      | _ := None
      } ;
    | _ := None
    }.
  Next Obligation.
    cbn. symmetry in eq2.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq2). subst.
    apply welltyped_zipx in h. rewrite zipc_appstack in h. cbn in h.
    zip fold in h. apply welltyped_context in h ; auto. simpl in h.
    destruct h as [T h].
    destruct (inversion_App h) as [na [A' [B' [[?] [[?] [?]]]]]].
    eexists. eassumption.
  Qed.

  Derive NoConfusion NoConfusionHom for option.

  Lemma unfold_one_fix_red_zippx :
    forall Γ mfix idx π h fn ξ,
      Some (fn, ξ) = unfold_one_fix Γ mfix idx π h ->
      ∥ red (fst Σ) Γ (zippx (tFix mfix idx) π) (zippx fn ξ) ∥.
  Proof.
    intros Γ mfix idx π h fn ξ eq.
    revert eq.
    funelim (unfold_one_fix Γ mfix idx π h).
    all: intro eq ; noconf eq.
    unfold zippx.
    pose proof (eq_sym e0) as eq.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq). subst.
    rewrite 2!decompose_stack_appstack. simpl.
    case_eq (decompose_stack s). intros l' s' e'.
    simpl.
    match type of e1 with
    | _ = reduce_stack ?flags ?Σ ?Γ ?t ?π ?h =>
      pose proof (reduce_stack_sound flags Σ Γ t π h) as [r1] ;
      pose proof (reduce_stack_decompose flags Σ Γ t π h) as hd
    end.
    rewrite <- e1 in r1. cbn in r1.
    rewrite <- e1 in hd. cbn in hd.
    constructor. eapply red_it_mkLambda_or_LetIn.
    rewrite <- 2!mkApps_nested. cbn. eapply red_mkApps.
    pose proof (decompose_stack_eq _ _ _ e'). subst.
    rewrite stack_context_appstack in r1.
    econstructor.
    - eapply app_reds_r. exact r1.
    - repeat lazymatch goal with
      | |- context [ tApp (mkApps ?t ?l) ?u ] =>
        replace (tApp (mkApps t l) u) with (mkApps t (l ++ [u]))
          by (rewrite <- mkApps_nested ; reflexivity)
      end.
      eapply red_fix.
      + symmetry. eassumption.
      + unfold is_constructor.
        pose proof (eq_sym e0) as eql.
        apply decompose_stack_at_length in eql. subst.
        rewrite nth_error_app_ge by auto.
        replace (#|l| - #|l|) with 0 by omega. cbn.
        case_eq (decompose_stack s0). intros l0 s1 ee.
        rewrite ee in hd.
        pose proof (decompose_stack_eq _ _ _ ee). subst.
        cbn in hd. subst.
        rewrite zipc_appstack. cbn.
        unfold isConstruct_app. rewrite decompose_app_mkApps by auto.
        reflexivity.
  Qed.

  Lemma unfold_one_fix_red :
    forall Γ mfix idx π h fn ξ,
      Some (fn, ξ) = unfold_one_fix Γ mfix idx π h ->
      ∥ red (fst Σ) Γ (zipc (tFix mfix idx) π) (zipc fn ξ) ∥.
  Proof.
    intros Γ mfix idx π h fn ξ eq.
    revert eq.
    funelim (unfold_one_fix Γ mfix idx π h).
    all: intro eq ; noconf eq.
    pose proof (eq_sym e0) as eq.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq). subst.
    rewrite !zipc_appstack. cbn.
    match type of e1 with
    | _ = reduce_stack ?flags ?Σ ?Γ ?t ?π ?h =>
      pose proof (reduce_stack_sound flags Σ Γ t π h) as [r1] ;
      pose proof (reduce_stack_decompose flags Σ Γ t π h) as hd
    end.
    rewrite <- e1 in r1. cbn in r1.
    rewrite <- e1 in hd. cbn in hd.
    do 2 zip fold. constructor. eapply red_context.
    econstructor.
    - eapply app_reds_r. exact r1.
    - repeat lazymatch goal with
      | |- context [ tApp (mkApps ?t ?l) ?u ] =>
        replace (tApp (mkApps t l) u) with (mkApps t (l ++ [u]))
          by (rewrite <- mkApps_nested ; reflexivity)
      end.
      eapply red_fix.
      + symmetry. eassumption.
      + unfold is_constructor.
        pose proof (eq_sym e0) as eql.
        apply decompose_stack_at_length in eql. subst.
        rewrite nth_error_app_ge by auto.
        replace (#|l| - #|l|) with 0 by omega. cbn.
        case_eq (decompose_stack s0). intros l0 s1 ee.
        rewrite ee in hd.
        pose proof (decompose_stack_eq _ _ _ ee). subst.
        cbn in hd. subst.
        rewrite zipc_appstack. cbn.
        unfold isConstruct_app. rewrite decompose_app_mkApps by auto.
        reflexivity.
  Qed.

  Lemma unfold_one_fix_cored :
    forall Γ mfix idx π h fn ξ,
      Some (fn, ξ) = unfold_one_fix Γ mfix idx π h ->
      cored (fst Σ) Γ (zipc fn ξ) (zipc (tFix mfix idx) π).
  Proof.
    intros Γ mfix idx π h fn ξ eq.
    revert eq.
    funelim (unfold_one_fix Γ mfix idx π h).
    all: intro eq ; noconf eq.
    pose proof (eq_sym e0) as eq.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq). subst.
    rewrite !zipc_appstack. cbn.
    match type of e1 with
    | _ = reduce_stack ?flags ?Σ ?Γ ?t ?π ?h =>
      pose proof (reduce_stack_sound flags Σ Γ t π h) as [r1] ;
      pose proof (reduce_stack_decompose flags Σ Γ t π h) as hd
    end.
    rewrite <- e1 in r1. cbn in r1.
    rewrite <- e1 in hd. cbn in hd.
    do 2 zip fold. eapply cored_context.
    eapply cored_red_trans.
    - eapply app_reds_r. exact r1.
    - repeat lazymatch goal with
      | |- context [ tApp (mkApps ?t ?l) ?u ] =>
        replace (tApp (mkApps t l) u) with (mkApps t (l ++ [u]))
          by (rewrite <- mkApps_nested ; reflexivity)
      end.
      eapply red_fix.
      + symmetry. eassumption.
      + unfold is_constructor.
        pose proof (eq_sym e0) as eql.
        apply decompose_stack_at_length in eql. subst.
        rewrite nth_error_app_ge by auto.
        replace (#|l| - #|l|) with 0 by omega. cbn.
        case_eq (decompose_stack s0). intros l0 s1 ee.
        rewrite ee in hd.
        pose proof (decompose_stack_eq _ _ _ ee). subst.
        cbn in hd. subst.
        rewrite zipc_appstack. cbn.
        unfold isConstruct_app. rewrite decompose_app_mkApps by auto.
        reflexivity.
  Qed.

  Lemma unfold_one_fix_decompose :
    forall Γ mfix idx π h fn ξ,
      Some (fn, ξ) = unfold_one_fix Γ mfix idx π h ->
      snd (decompose_stack π) = snd (decompose_stack ξ).
  Proof.
    intros Γ mfix idx π h fn ξ eq.
    revert eq.
    funelim (unfold_one_fix Γ mfix idx π h).
    all: intro eq ; noconf eq.
    pose proof (eq_sym e0) as eq.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq). subst.
    rewrite 2!decompose_stack_appstack. cbn.
    case_eq (decompose_stack s). intros l0 s1 H2.
    reflexivity.
  Qed.

  (* Tailored view for isconv_prog *)
  Equations prog_discr (t1 t2 : term) : Prop :=
    prog_discr (tApp _ _) (tApp _ _) := False ;
    prog_discr (tConst _ _) (tConst _ _) := False ;
    prog_discr (tLambda _ _ _) (tLambda _ _ _) := False ;
    prog_discr (tProd _ _ _) (tProd _ _ _) := False ;
    prog_discr (tCase _ _ _ _) (tCase _ _ _ _) := False ;
    prog_discr (tProj _ _) (tProj _ _) := False ;
    prog_discr (tFix _ _) (tFix _ _) := False ;
    prog_discr (tCoFix _ _) (tCoFix _ _) := False ;
    prog_discr _ _ := True.

  Inductive prog_view : term -> term -> Set :=
  | prog_view_App u1 v1 u2 v2 :
      prog_view (tApp u1 v1) (tApp u2 v2)

  | prog_view_Const c1 u1 c2 u2 :
      prog_view (tConst c1 u1) (tConst c2 u2)

  | prog_view_Lambda na1 A1 b1 na2 A2 b2 :
      prog_view (tLambda na1 A1 b1) (tLambda na2 A2 b2)

  | prog_view_Prod na1 A1 B1 na2 A2 B2 :
      prog_view (tProd na1 A1 B1) (tProd na2 A2 B2)

  | prog_view_Case ind par p c brs ind' par' p' c' brs' :
      prog_view (tCase (ind, par) p c brs) (tCase (ind', par') p' c' brs')

  | prog_view_Proj p c p' c' :
      prog_view (tProj p c) (tProj p' c')

  | prog_view_Fix mfix idx mfix' idx' :
      prog_view (tFix mfix idx) (tFix mfix' idx')

  | prog_view_CoFix mfix idx mfix' idx' :
      prog_view (tCoFix mfix idx) (tCoFix mfix' idx')

  | prog_view_other :
      forall u v, prog_discr u v -> prog_view u v.

  Equations prog_viewc u v : prog_view u v :=
    prog_viewc (tApp u1 v1) (tApp u2 v2) :=
      prog_view_App u1 v1 u2 v2 ;

    prog_viewc (tConst c1 u1) (tConst c2 u2) :=
      prog_view_Const c1 u1 c2 u2 ;

    prog_viewc (tLambda na1 A1 b1) (tLambda na2 A2 b2) :=
      prog_view_Lambda na1 A1 b1 na2 A2 b2 ;

    prog_viewc (tProd na1 A1 B1) (tProd na2 A2 B2) :=
      prog_view_Prod na1 A1 B1 na2 A2 B2 ;

    prog_viewc (tCase (ind, par) p c brs) (tCase (ind', par') p' c' brs') :=
      prog_view_Case ind par p c brs ind' par' p' c' brs' ;

    prog_viewc (tProj p c) (tProj p' c') :=
      prog_view_Proj p c p' c' ;

    prog_viewc (tFix mfix idx) (tFix mfix' idx') :=
      prog_view_Fix mfix idx mfix' idx' ;

    prog_viewc (tCoFix mfix idx) (tCoFix mfix' idx') :=
      prog_view_CoFix mfix idx mfix' idx' ;

    prog_viewc u v := prog_view_other u v I.

  Equations(noeqns) _isconv_prog (Γ : context) (leq : conv_pb)
            (t1 : term) (π1 : stack) (h1 : wtp Γ t1 π1)
            (t2 : term) (π2 : stack) (h2 : wtp Γ t2 π2)
            (ir1 : isred (t1, π1)) (ir2 : isred (t2, π2))
            (aux : Aux (Term t2) Γ t1 π1 π2 h2)
    : { b : bool | if b then conv leq Σ Γ (zippx t1 π1) (zippx t2 π2) else True } :=

    _isconv_prog Γ leq t1 π1 h1 t2 π2 h2 ir1 ir2 aux with prog_viewc t1 t2 := {
    | prog_view_App _ _ _ _ :=
      False_rect _ _ ;

    | prog_view_Const c u c' u' with eq_dec c c' := {
      | left eq1 with eq_dec u u' := {
        | left eq2 with isconv_args_raw Γ (tConst c u) π1 π2 aux := {
          | @exist true h := yes ;
          (* Unfold both constants at once *)
          | @exist false _ with inspect (lookup_env Σ c) := {
            | @exist (Some (ConstantDecl n {| cst_body := Some body |})) eq3 :=
              (* In PCUICChecker, there is no subst but I guess it's just wrong. *)
              isconv_red Γ leq (subst_instance_constr u body) π1
                               (subst_instance_constr u body) π2 aux ;
            (* Inductive or not found *)
            | @exist _ _ := no
            }
          } ;
        (* If the two constants are different, we unfold one of them *)
        | right _ with inspect (lookup_env Σ c') := {
          | @exist (Some (ConstantDecl n {| cst_body := Some b |})) eq1 :=
            isconv_red Γ leq (tConst c u) π1 (subst_instance_constr u' b) π2 aux ;
          (* Inductive or not found *)
          | _ with inspect (lookup_env Σ c) := {
            | @exist (Some (ConstantDecl n {| cst_body := Some b |})) eq1 :=
              isconv_red Γ leq (subst_instance_constr u b) π1
                               (tConst c' u') π2 aux ;
            (* Both Inductive or not found *)
            | _ := no
            }
          }
        } ;
      | right _ := no
      } ;

    | prog_view_Lambda na A1 t1 na' A2 t2
      with isconv_red_raw Γ Conv A1 (Lambda_ty na t1 π1)
                                 A2 (Lambda_ty na' t2 π2) aux := {
      | @exist true h :=
        isconv_red Γ leq
                   t1 (Lambda_tm na A1 π1)
                   t2 (Lambda_tm na' A2 π2) aux ;
      | @exist false _ := no
      } ;

    | prog_view_Prod na A1 B1 na' A2 B2
      with isconv_red_raw Γ Conv A1 (Prod_l na B1 π1) A2 (Prod_l na' B2 π2) aux := {
      | @exist true h :=
        isconv_red Γ leq
                   B1 (Prod_r na A1 π1)
                   B2 (Prod_r na' A2 π2) aux ;
      | @exist false _ := no
      } ;

    | prog_view_Case ind par p c brs ind' par' p' c' brs'
      with inspect (nleq_term (tCase (ind, par) p c brs) (tCase (ind', par') p' c' brs')) := {
      | @exist true eq1 := isconv_args Γ (tCase (ind, par) p c brs) π1 π2 aux ;
      | @exist false _ with inspect (reduce_term RedFlags.default Σ (Γ ,,, stack_context π1) c _) := {
        | @exist cred eq1 with inspect (reduce_term RedFlags.default Σ (Γ ,,, stack_context π2) c' _) := {
           | @exist cred' eq2 with inspect (nleq_term cred c && nleq_term cred' c') := {
              | @exist true eq3 := no ;
              | @exist false eq3 :=
                isconv_red Γ leq (tCase (ind, par) p cred brs) π1
                                 (tCase (ind', par') p' cred' brs') π2 aux
              }
           }
        }
      } ;

    | prog_view_Proj p c p' c' with inspect (nleq_term (tProj p c) (tProj p' c')) := {
      | @exist true eq1 := isconv_args Γ (tProj p c) π1 π2 aux ;
      | @exist false _ := no
      } ;

    | prog_view_Fix mfix idx mfix' idx'
      with inspect (nleq_term (tFix mfix idx) (tFix mfix' idx')) := {
      | @exist true eq1 := isconv_args Γ (tFix mfix idx) π1 π2 aux ;
      | @exist false _ with inspect (unfold_one_fix Γ mfix idx π1 _) := {
        | @exist (Some (fn, θ)) eq1
          with inspect (decompose_stack θ) := {
          | @exist (l', θ') eq2
            with inspect (reduce_stack nodelta_flags Σ (Γ ,,, stack_context θ') fn (appstack l' ε) _) := {
            | @exist (fn', ρ) eq3 :=
              isconv_prog Γ leq fn' (ρ +++ θ') (tFix mfix' idx') π2 aux
            }
          } ;
        | _ with inspect (unfold_one_fix Γ mfix' idx' π2 _) := {
          | @exist (Some (fn, θ)) eq1
            with inspect (decompose_stack θ) := {
            | @exist (l', θ') eq2
              with inspect (reduce_stack nodelta_flags Σ (Γ ,,, stack_context θ') fn (appstack l' ε) _) := {
              | @exist (fn', ρ) eq3 :=
                isconv_prog Γ leq (tFix mfix idx) π1 fn' (ρ +++ θ') aux
              }
            } ;
          | _ := no
          }
        }
      } ;

    | prog_view_CoFix mfix idx mfix' idx'
      with inspect (nleq_term (tCoFix mfix idx) (tCoFix mfix' idx')) := {
      | @exist true eq1 := isconv_args Γ (tCoFix mfix idx) π1 π2 aux ;
      | @exist false _ := no
      } ;

    | prog_view_other t1 t2 h :=
      isconv_fallback Γ leq t1 π1 t2 π2 aux
    }.

  (* tApp *)
  Next Obligation.
    destruct ir1 as [ha1 _]. discriminate ha1.
  Qed.

  (* tConst *)
  Next Obligation.
    unshelve eapply R_stateR.
    all: try reflexivity.
    constructor.
  Qed.
  Next Obligation.
    destruct h. eapply conv_conv_l. assumption.
  Qed.
  Next Obligation.
    eapply red_welltyped ; auto.
    - exact h1.
    - constructor. eapply red_zipx. eapply red_const. eassumption.
  Qed.
  Next Obligation.
    eapply red_welltyped ; auto.
    - exact h2.
    - constructor. eapply red_zipx. eapply red_const. eassumption.
  Qed.
  Next Obligation.
    eapply R_cored. simpl.
    eapply cored_zipx.
    eapply cored_const.
    eassumption.
  Qed.
  Next Obligation.
    destruct b ; auto.
    eapply conv_trans'.
    - eapply red_conv_l.
      eapply red_zippx.
      eapply red_const. eassumption.
    - eapply conv_trans' ; try eassumption.
      eapply red_conv_r.
      eapply red_zippx.
      eapply red_const. eassumption.
  Qed.
  Next Obligation.
    eapply red_welltyped ; auto ; [ exact h2 | ].
    constructor. eapply red_zipx. eapply red_const. eassumption.
  Qed.
  Next Obligation.
    unshelve eapply R_cored2.
    all: try reflexivity.
    simpl. eapply cored_zipx.
    eapply cored_const. eassumption.
  Qed.
  Next Obligation.
    destruct b0 ; auto.
    eapply conv_trans' ; try eassumption.
    eapply red_conv_r.
    eapply red_zippx. eapply red_const. eassumption.
  Qed.
  Next Obligation.
    eapply red_welltyped ; auto ; [ exact h1 | ].
    constructor. eapply red_zipx. eapply red_const. eassumption.
  Qed.
  Next Obligation.
    eapply R_cored. simpl. eapply cored_zipx.
    eapply cored_const. eassumption.
  Qed.
  Next Obligation.
    destruct b0 ; auto.
    eapply conv_trans' ; try eassumption.
    eapply red_conv_l.
    eapply red_zippx. eapply red_const. eassumption.
  Qed.
  Next Obligation.
    eapply red_welltyped ; auto ; [ exact h1 | ].
    constructor. eapply red_zipx. eapply red_const. eassumption.
  Qed.
  Next Obligation.
    eapply R_cored. simpl. eapply cored_zipx.
    eapply cored_const. eassumption.
  Qed.
  Next Obligation.
    destruct b0 ; auto.
    eapply conv_trans' ; try eassumption.
    eapply red_conv_l.
    eapply red_zippx. eapply red_const. eassumption.
  Qed.
  Next Obligation.
    eapply red_welltyped ; auto ; [ exact h1 | ].
    constructor. eapply red_zipx. eapply red_const. eassumption.
  Qed.
  Next Obligation.
    eapply R_cored. simpl. eapply cored_zipx.
    eapply cored_const. eassumption.
  Qed.
  Next Obligation.
    destruct b0 ; auto.
    eapply conv_trans' ; try eassumption.
    eapply red_conv_l.
    eapply red_zippx. eapply red_const. eassumption.
  Qed.

  (* tLambda *)
  Next Obligation.
    unshelve eapply R_positionR.
    - reflexivity.
    - simpl. unfold xposition. eapply positionR_poscat.
      simpl. rewrite <- app_nil_r. eapply positionR_poscat. constructor.
  Qed.
  Next Obligation.
    unshelve eapply R_positionR.
    - reflexivity.
    - simpl. unfold xposition. eapply positionR_poscat.
      simpl. rewrite <- app_nil_r. eapply positionR_poscat. constructor.
  Qed.
  Next Obligation.
    destruct b ; auto.
    destruct h0 as [h0].

    unfold zippx in h0. simpl in h0.
    unfold zippx in h. simpl in h. cbn in h.
    unfold zippx.
    case_eq (decompose_stack π1). intros l1 ρ1 e1.
    case_eq (decompose_stack π2). intros l2 ρ2 e2.
    pose proof (decompose_stack_eq _ _ _ e1). subst.
    pose proof (decompose_stack_eq _ _ _ e2). subst.
    rewrite 2!stack_context_appstack in h0.
    rewrite 2!stack_context_appstack in h.

    destruct ir1 as [_ hl1]. cbn in hl1.
    specialize (hl1 eq_refl).
    destruct l1 ; try discriminate hl1. clear hl1.

    destruct ir2 as [_ hl2]. cbn in hl2.
    specialize (hl2 eq_refl).
    destruct l2 ; try discriminate hl2. clear hl2.

    (* The fact that we can conclude directly is distrubing!
       Are we checking too much?
       TODO CHECK
     *)
    cbn. assumption.
  Qed.

  (* tProd *)
  Next Obligation.
    unshelve eapply R_positionR.
    - reflexivity.
    - simpl. unfold xposition. eapply positionR_poscat.
      simpl. rewrite <- app_nil_r. eapply positionR_poscat. constructor.
  Qed.
  Next Obligation.
    unshelve eapply R_positionR.
    - simpl. reflexivity.
    - simpl. unfold xposition. eapply positionR_poscat.
      simpl. rewrite <- app_nil_r. eapply positionR_poscat. constructor.
  Qed.
  Next Obligation.
    destruct b ; auto.
    destruct h0 as [h0].
    unfold zippx in h0. simpl in h0.
    unfold zippx in h. simpl in h. cbn in h.
    unfold zippx.
    case_eq (decompose_stack π1). intros l1 ρ1 e1.
    case_eq (decompose_stack π2). intros l2 ρ2 e2.
    pose proof (decompose_stack_eq _ _ _ e1). subst.
    pose proof (decompose_stack_eq _ _ _ e2). subst.
    rewrite 2!stack_context_appstack in h0.
    rewrite 2!stack_context_appstack in h.

    apply welltyped_zipx in h1.
    apply welltyped_zipc_zippx in h1 ; auto.
    unfold zippx in h1. rewrite decompose_stack_appstack in h1.
    rewrite decompose_stack_twice with (1 := e1) in h1.
    simpl in h1. rewrite app_nil_r in h1.
    apply welltyped_it_mkLambda_or_LetIn in h1.
    apply mkApps_Prod_nil in h1 ; auto. subst.

    clear aux.
    apply welltyped_zipx in h2.
    apply welltyped_zipc_zippx in h2 ; auto.
    unfold zippx in h2. rewrite decompose_stack_appstack in h2.
    rewrite decompose_stack_twice with (1 := e2) in h2.
    simpl in h2. rewrite app_nil_r in h2.
    apply welltyped_it_mkLambda_or_LetIn in h2.
    apply mkApps_Prod_nil in h2 ; auto. subst.

    cbn.
    apply it_mkLambda_or_LetIn_stack_context_conv_inv in h0 as [? ?] ; auto.
    eapply it_mkLambda_or_LetIn_conv' ; auto.
    apply it_mkLambda_or_LetIn_stack_context_conv'_inv in h as [[?] hl] ; auto.
    apply Lambda_conv_inv in hl as [[?] ?] ; auto.
    eapply Prod_conv ; auto.
  Qed.

  (* tCase *)
  Next Obligation.
    symmetry in eq1.
    eapply welltyped_rename ; auto ; [ exact h2 |].
    eapply eq_term_sym.
    eapply eq_term_zipx.
    eapply eq_term_upto_univ_eq_eq_term.
    eapply ssrbool.elimT.
    - eapply reflect_eq_term_upto_univ_eqb.
    - assumption.
  Qed.
  Next Obligation.
    unshelve eapply R_stateR.
    all: try reflexivity.
    - simpl.
      symmetry in eq1.
      eapply ssrbool.elimT.
      + eapply reflect_nleq_term.
      + eapply nleq_term_zipx. assumption.
    - simpl. constructor.
  Qed.
  Next Obligation.
    destruct b ; auto.
    eapply conv_conv.
    destruct h. constructor.
    eapply conv_trans ; try eassumption.
    eapply conv_zippx ; auto.
    eapply eq_term_conv.
    symmetry in eq1.
    eapply eq_term_upto_univ_eq_eq_term.
    eapply ssrbool.elimT.
    - eapply reflect_eq_term_upto_univ_eqb.
    - assumption.
  Qed.
  Next Obligation.
    apply welltyped_zipx in h1.
    zip fold in h1. apply welltyped_context in h1 ; auto. simpl in h1.
    destruct h1 as [T h1].
    destruct (weak_inversion_Case h1) as [args [u [?]]].
    eexists. eassumption.
  Qed.
  Next Obligation.
    clear aux.
    apply welltyped_zipx in h2.
    zip fold in h2. apply welltyped_context in h2 ; auto. simpl in h2.
    destruct h2 as [T h2].
    destruct (weak_inversion_Case h2) as [args [u [?]]].
    eexists. eassumption.
  Qed.
  Next Obligation.
    eapply red_welltyped ; auto.
    - exact h1.
    - match goal with
      | |- context [ reduce_term ?f ?Σ ?Γ ?t ?h ] =>
        pose proof (reduce_term_sound f Σ Γ t h) as [hr]
      end.
      constructor.
      eapply red_zipx.
      eapply PCUICReduction.red_case.
      + constructor.
      + assumption.
      + clear.
        induction brs ; eauto.
        constructor.
        * constructor.
        * eapply IHbrs.
  Qed.
  Next Obligation.
    eapply red_welltyped ; auto.
    - exact h2.
    - match goal with
      | |- context [ reduce_term ?f ?Σ ?Γ ?t ?h ] =>
        pose proof (reduce_term_sound f Σ Γ t h) as [hr]
      end.
      constructor.
      eapply red_zipx.
      eapply PCUICReduction.red_case.
      + constructor.
      + assumption.
      + clear.
        induction brs' ; eauto.
        constructor.
        * constructor.
        * eapply IHbrs'.
  Qed.
  Next Obligation.
    match goal with
    | |- context [ reduce_term ?f ?Σ ?Γ c ?h ] =>
      destruct (reduce_stack_Req f Σ Γ c ε h) as [e | hr]
    end.
    - match goal with
      | |- context [ reduce_term ?f ?Σ ?Γ c' ?h ] =>
        destruct (reduce_stack_Req f Σ Γ c' ε h) as [e' | hr]
      end.
      + exfalso.
        unfold reduce_term in eq3.
        rewrite e in eq3.
        rewrite e' in eq3.
        cbn in eq3. symmetry in eq3.
        assert (bot : eqb_term_upto_univ eqb c c && eqb_term_upto_univ eqb c' c').
        { apply andb_and. split.
          - eapply ssrbool.introT.
            + eapply reflect_eq_term_upto_univ_eqb.
            + eapply eq_term_upto_univ_refl. intro. reflexivity.
          - eapply ssrbool.introT.
            + eapply reflect_eq_term_upto_univ_eqb.
            + eapply eq_term_upto_univ_refl. intro. reflexivity.
        }
        rewrite bot in eq3. discriminate.
      + dependent destruction hr.
        * unshelve eapply R_cored2.
          all: try reflexivity.
          -- simpl. unfold reduce_term. rewrite e. reflexivity.
          -- simpl. eapply cored_zipx. eapply cored_case. assumption.
        * exfalso.
          destruct y'. simpl in H0. inversion H0. subst.
          unfold reduce_term in eq3.
          rewrite e in eq3.
          rewrite <- H2 in eq3.
          cbn in eq3. symmetry in eq3.
          assert (bot : eqb_term_upto_univ eqb c c && eqb_term_upto_univ eqb c' c').
          { apply andb_and. split.
            - eapply ssrbool.introT.
              + eapply reflect_eq_term_upto_univ_eqb.
              + eapply eq_term_upto_univ_refl. intro. reflexivity.
            - eapply ssrbool.introT.
              + eapply reflect_eq_term_upto_univ_eqb.
              + eapply eq_term_upto_univ_refl. intro. reflexivity.
          }
          rewrite bot in eq3. discriminate.
    - dependent destruction hr.
      + eapply R_cored. simpl.
        eapply cored_zipx. eapply cored_case. assumption.
      + match goal with
        | |- context [ reduce_term ?f ?Σ ?Γ c' ?h ] =>
          destruct (reduce_stack_Req f Σ Γ c' ε h) as [e' | hr]
        end.
        * exfalso.
          destruct y'. simpl in H0. inversion H0. subst.
          unfold reduce_term in eq3.
          rewrite e' in eq3.
          rewrite <- H2 in eq3.
          cbn in eq3. symmetry in eq3.
          assert (bot : eqb_term_upto_univ eqb c c && eqb_term_upto_univ eqb c' c').
          { apply andb_and. split.
            - eapply ssrbool.introT.
              + eapply reflect_eq_term_upto_univ_eqb.
              + eapply eq_term_upto_univ_refl. intro. reflexivity.
            - eapply ssrbool.introT.
              + eapply reflect_eq_term_upto_univ_eqb.
              + eapply eq_term_upto_univ_refl. intro. reflexivity.
          }
          rewrite bot in eq3. discriminate.
        * dependent destruction hr.
          -- unshelve eapply R_cored2.
             all: try reflexivity.
             ++ simpl. unfold reduce_term.
                destruct y'. simpl in H0. inversion H0. subst.
                rewrite <- H3. reflexivity.
             ++ simpl. eapply cored_zipx. eapply cored_case. assumption.
          -- exfalso.
             destruct y'. simpl in H0. inversion H0. subst.
             destruct y'0. simpl in H2. inversion H2. subst.
             unfold reduce_term in eq3.
             rewrite <- H4 in eq3.
             rewrite <- H5 in eq3.
             cbn in eq3. symmetry in eq3.
             assert (bot : eqb_term_upto_univ eqb c c && eqb_term_upto_univ eqb c' c').
             { apply andb_and. split.
               - eapply ssrbool.introT.
                 + eapply reflect_eq_term_upto_univ_eqb.
                 + eapply eq_term_upto_univ_refl. intro. reflexivity.
               - eapply ssrbool.introT.
                 + eapply reflect_eq_term_upto_univ_eqb.
                 + eapply eq_term_upto_univ_refl. intro. reflexivity.
             }
             rewrite bot in eq3. discriminate.
  Qed.
  Next Obligation.
    destruct b ; auto.
    match type of h with
    | context [ reduce_term ?f ?Σ ?Γ c ?h ] =>
      pose proof (reduce_term_sound f Σ Γ c h) as hr
    end.
    match type of h with
    | context [ reduce_term ?f ?Σ ?Γ c' ?h ] =>
      pose proof (reduce_term_sound f Σ Γ c' h) as hr'
    end.
    destruct hr as [hr], hr' as [hr'].
    eapply conv_trans'.
    - eapply red_conv_l.
      eapply red_zippx.
      eapply PCUICReduction.red_case.
      + constructor.
      + eassumption.
      + instantiate (1 := brs).
        clear.
        induction brs ; eauto.
        constructor.
        * constructor.
        * eapply IHbrs.
    - eapply conv_trans' ; try eassumption.
      eapply red_conv_r.
      eapply red_zippx.
      eapply PCUICReduction.red_case.
      + constructor.
      + eassumption.
      + clear.
        induction brs' ; eauto.
        constructor.
        * constructor.
        * eapply IHbrs'.
  Qed.

  (* tProj *)
  Next Obligation.
    eapply welltyped_rename ; auto.
    - exact h2.
    - apply eq_term_sym.
      cbn. eapply eq_term_zipx.
      eapply eq_term_upto_univ_eq_eq_term.
      eapply ssrbool.elimT.
      + eapply reflect_eq_term_upto_univ_eqb.
      + symmetry. assumption.
  Qed.
  Next Obligation.
    unshelve eapply R_stateR.
    all: try reflexivity.
    - simpl.
      eapply ssrbool.elimT.
      + eapply reflect_nleq_term.
      + eapply nleq_term_zipx.
        symmetry. assumption.
    - simpl. constructor.
  Qed.
  Next Obligation.
    destruct b ; auto.
    eapply conv_conv.
    destruct h. constructor.
    eapply conv_trans ; try eassumption.
    eapply conv_zippx ; auto.
    eapply eq_term_conv.
    eapply eq_term_upto_univ_eq_eq_term.
    eapply ssrbool.elimT.
    - eapply reflect_eq_term_upto_univ_eqb.
    - symmetry. assumption.
  Qed.

  (* tFix *)
  Next Obligation.
    eapply welltyped_rename ; auto.
    - exact h2.
    - apply eq_term_sym. eapply eq_term_zipx.
      eapply eq_term_upto_univ_eq_eq_term.
      eapply ssrbool.elimT.
      + eapply reflect_eq_term_upto_univ_eqb.
      + symmetry. assumption.
  Qed.
  Next Obligation.
    unshelve eapply R_stateR.
    all: try reflexivity.
    - simpl.
      eapply ssrbool.elimT.
      + eapply reflect_nleq_term.
      + eapply nleq_term_zipx.
        symmetry. assumption.
    - simpl. constructor.
  Qed.
  Next Obligation.
    destruct b ; auto.
    destruct h as [h].
    eapply conv_conv.
    constructor.
    eapply conv_trans ; try eassumption.
    eapply conv_zippx ; auto.
    eapply eq_term_conv.
    symmetry in eq1.
    eapply eq_term_upto_univ_eq_eq_term.
    eapply ssrbool.elimT.
    - eapply reflect_eq_term_upto_univ_eqb.
    - assumption.
  Qed.
  Next Obligation.
    cbn. rewrite zipc_appstack. cbn.
    apply unfold_one_fix_red_zippx in eq1 as r.
    unfold zippx in r.
    rewrite <- eq2 in r.
    case_eq (decompose_stack π1). intros l1 ρ1 e1.
    rewrite e1 in r.
    apply welltyped_zipx in h1 as hh1 ; auto.
    apply welltyped_zipc_zippx in hh1 ; auto.
    pose proof (decompose_stack_eq _ _ _ e1). subst.
    unfold zippx in hh1. rewrite e1 in hh1.
    pose proof (red_welltyped flags _ hh1 r) as hh.
    apply welltyped_it_mkLambda_or_LetIn in hh.
    assumption.
  Qed.
  Next Obligation.
    apply unfold_one_fix_red in eq1 as r1.
    apply unfold_one_fix_decompose in eq1 as d1.
    match type of eq3 with
    | _ = reduce_stack ?f ?Σ ?Γ ?t ?π ?h =>
      destruct (reduce_stack_sound f Σ Γ t π h) as [r2] ;
      pose proof (reduce_stack_decompose nodelta_flags _ _ _ _ h) as d2 ;
      pose proof (reduce_stack_context f Σ Γ t π h) as c2
    end.
    rewrite <- eq3 in r2. cbn in r2. rewrite zipc_appstack in r2. cbn in r2.
    rewrite <- eq3 in d2. cbn in d2. rewrite decompose_stack_appstack in d2.
    cbn in d2.
    rewrite <- eq3 in c2. cbn in c2. rewrite stack_context_appstack in c2.
    cbn in c2.
    case_eq (decompose_stack ρ). intros l ξ e.
    rewrite e in d2. cbn in d2. subst.
    apply welltyped_zipx in h1 as hh1.
    pose proof (red_welltyped flags _ hh1 r1) as hh.
    apply red_context in r2.
    pose proof (decompose_stack_eq _ _ _ (eq_sym eq2)). subst.
    rewrite zipc_appstack in hh. cbn in r2.
    pose proof (red_welltyped flags _ hh (sq _ r2)) as hh2.
    eapply zipx_welltyped ; auto.
    rewrite zipc_stack_cat.
    assumption.
  Qed.
  Next Obligation.
    apply unfold_one_fix_cored in eq1 as r1.
    apply unfold_one_fix_decompose in eq1 as d1.
    match type of eq3 with
    | _ = reduce_stack ?f ?Σ ?Γ ?t ?π ?h =>
      destruct (reduce_stack_sound f Σ Γ t π h) as [r2]
    end.
    rewrite <- eq3 in r2.
    eapply R_cored. simpl. eapply cored_it_mkLambda_or_LetIn.
    rewrite app_context_nil_l.
    eapply red_cored_cored ; try eassumption.
    apply red_context in r2. cbn in r2.
    rewrite zipc_stack_cat.
    pose proof (decompose_stack_eq _ _ _ (eq_sym eq2)). subst.
    rewrite zipc_appstack in r2. cbn in r2.
    rewrite zipc_appstack.
    assumption.
  Qed.
  Next Obligation.
    match type of eq3 with
    | _ = reduce_stack ?f ?Σ ?Γ ?t ?π ?h =>
      pose proof (reduce_stack_decompose nodelta_flags _ _ _ _ h) as d2 ;
      pose proof (reduce_stack_isred f Σ Γ t π h eq_refl) as ir
    end.
    rewrite <- eq3 in d2. cbn in d2. rewrite decompose_stack_appstack in d2.
    cbn in d2.
    rewrite <- eq3 in ir. destruct ir as [? hl].
    split.
    - assumption.
    - simpl. intro h. specialize (hl h). cbn in hl.
      case_eq (decompose_stack ρ). intros l π e.
      rewrite e in d2. cbn in d2. subst.
      pose proof (decompose_stack_eq _ _ _ e). subst.
      rewrite stack_cat_appstack.
      apply isStackApp_false_appstack in hl. subst. cbn.
      eapply decompose_stack_noStackApp. symmetry. eassumption.
  Qed.
  Next Obligation.
    destruct b ; auto.
    apply unfold_one_fix_red_zippx in eq1 as r1.
    destruct r1 as [r1].
    match type of eq3 with
    | _ = reduce_stack ?f ?Σ ?Γ ?t ?π ?h =>
      destruct (reduce_stack_sound f Σ Γ t π h) as [r2] ;
      pose proof (reduce_stack_decompose nodelta_flags _ _ _ _ h) as d2
    end.
    rewrite <- eq3 in r2.
    rewrite <- eq3 in d2. cbn in d2. rewrite decompose_stack_appstack in d2.
    cbn in d2.
    apply unfold_one_fix_decompose in eq1 as d1.
    assert (r2' : red (fst Σ) Γ (zippx fn θ) (zippx fn' (ρ +++ θ'))).
    { unfold zippx.
      case_eq (decompose_stack ρ). intros l ξ e.
      rewrite e in d2. cbn in d2. subst.
      pose proof (decompose_stack_eq _ _ _ e). subst.
      rewrite stack_cat_appstack. rewrite decompose_stack_appstack.
      rewrite <- eq2.
      cbn in r2. rewrite 2!zipc_appstack in r2. cbn in r2.
      rewrite stack_context_decompose.
      eapply red_it_mkLambda_or_LetIn.
      rewrite <- eq2 in d1. cbn in d1. subst.
      case_eq (decompose_stack π1). intros l1 ρ1 e1.
      simpl. rewrite e1 in r2. simpl in r2.
      pose proof (decompose_stack_eq _ _ _ e1). subst.
      rewrite decompose_stack_twice with (1 := e1). cbn.
      rewrite app_nil_r.
      assumption.
    }
    pose proof (red_trans _ _ _ _ _ r1 r2') as r.
    eapply conv_trans'.
    - eapply red_conv_l. eassumption.
    - assumption.
  Qed.
  Next Obligation.
    cbn. rewrite zipc_appstack. cbn.
    apply unfold_one_fix_red_zippx in eq1 as r.
    unfold zippx in r.
    rewrite <- eq2 in r.
    case_eq (decompose_stack π2). intros l2 ρ2 e2.
    rewrite e2 in r.
    apply welltyped_zipx in h2 as hh2.
    apply welltyped_zipc_zippx in hh2 ; auto.
    pose proof (decompose_stack_eq _ _ _ e2). subst.
    unfold zippx in hh2. rewrite e2 in hh2.
    pose proof (red_welltyped flags _ hh2 r) as hh.
    apply welltyped_it_mkLambda_or_LetIn in hh.
    assumption.
  Qed.
  Next Obligation.
    apply unfold_one_fix_red in eq1 as r1.
    apply unfold_one_fix_decompose in eq1 as d1.
    match type of eq3 with
    | _ = reduce_stack ?f ?Σ ?Γ ?t ?π ?h =>
      destruct (reduce_stack_sound f Σ Γ t π h) as [r2] ;
      pose proof (reduce_stack_decompose nodelta_flags _ _ _ _ h) as d2 ;
      pose proof (reduce_stack_context f Σ Γ t π h) as c2
    end.
    rewrite <- eq3 in r2. cbn in r2. rewrite zipc_appstack in r2. cbn in r2.
    rewrite <- eq3 in d2. cbn in d2. rewrite decompose_stack_appstack in d2.
    cbn in d2.
    rewrite <- eq3 in c2. cbn in c2. rewrite stack_context_appstack in c2.
    cbn in c2.
    case_eq (decompose_stack ρ). intros l ξ e.
    rewrite e in d2. cbn in d2. subst.
    apply welltyped_zipx in h2 as hh2.
    pose proof (red_welltyped flags _ hh2 r1) as hh.
    apply red_context in r2.
    pose proof (decompose_stack_eq _ _ _ (eq_sym eq2)). subst.
    rewrite zipc_appstack in hh. cbn in r2.
    pose proof (red_welltyped flags _ hh (sq _ r2)) as hh'.
    eapply zipx_welltyped ; auto.
    rewrite zipc_stack_cat.
    assumption.
  Qed.
  Next Obligation.
    apply unfold_one_fix_cored in eq1 as r1.
    apply unfold_one_fix_decompose in eq1 as d1.
    match type of eq3 with
    | _ = reduce_stack ?f ?Σ ?Γ ?t ?π ?h =>
      destruct (reduce_stack_sound f Σ Γ t π h) as [r2]
    end.
    rewrite <- eq3 in r2.
    eapply R_cored2. all: try reflexivity. simpl.
    eapply cored_it_mkLambda_or_LetIn.
    rewrite app_context_nil_l.
    eapply red_cored_cored ; try eassumption.
    cbn in r2.
    rewrite zipc_stack_cat.
    pose proof (decompose_stack_eq _ _ _ (eq_sym eq2)). subst.
    rewrite zipc_appstack in r2. cbn in r2.
    rewrite zipc_appstack.
    zip fold. eapply red_context.
    assumption.
  Qed.
  Next Obligation.
    match type of eq3 with
    | _ = reduce_stack ?f ?Σ ?Γ ?t ?π ?h =>
      pose proof (reduce_stack_decompose nodelta_flags _ _ _ _ h) as d2 ;
      pose proof (reduce_stack_isred f Σ Γ t π h eq_refl) as ir
    end.
    rewrite <- eq3 in d2. cbn in d2. rewrite decompose_stack_appstack in d2.
    cbn in d2.
    rewrite <- eq3 in ir. destruct ir as [? hl].
    split.
    - assumption.
    - simpl. intro h. specialize (hl h). cbn in hl.
      case_eq (decompose_stack ρ). intros l π e.
      rewrite e in d2. cbn in d2. subst.
      pose proof (decompose_stack_eq _ _ _ e). subst.
      rewrite stack_cat_appstack.
      apply isStackApp_false_appstack in hl. subst. cbn.
      eapply decompose_stack_noStackApp. symmetry. eassumption.
  Qed.
  Next Obligation.
    destruct b ; auto.
    apply unfold_one_fix_red_zippx in eq1 as r1.
    destruct r1 as [r1].
    match type of eq3 with
    | _ = reduce_stack ?f ?Σ ?Γ ?t ?π ?h =>
      destruct (reduce_stack_sound f Σ Γ t π h) as [r2] ;
      pose proof (reduce_stack_decompose nodelta_flags _ _ _ _ h) as d2
    end.
    rewrite <- eq3 in r2.
    rewrite <- eq3 in d2. cbn in d2. rewrite decompose_stack_appstack in d2.
    cbn in d2.
    apply unfold_one_fix_decompose in eq1 as d1.
    assert (r2' : red (fst Σ) Γ (zippx fn θ) (zippx fn' (ρ +++ θ'))).
    { unfold zippx.
      case_eq (decompose_stack ρ). intros l ξ e.
      rewrite e in d2. cbn in d2. subst.
      pose proof (decompose_stack_eq _ _ _ e). subst.
      rewrite stack_cat_appstack. rewrite decompose_stack_appstack.
      rewrite <- eq2.
      cbn in r2. rewrite 2!zipc_appstack in r2. cbn in r2.
      rewrite stack_context_decompose.
      eapply red_it_mkLambda_or_LetIn.
      rewrite <- eq2 in d1. cbn in d1. subst.
      case_eq (decompose_stack π2). intros l2 ρ2 e2.
      simpl. rewrite e2 in r2. simpl in r2.
      pose proof (decompose_stack_eq _ _ _ e2). subst.
      rewrite decompose_stack_twice with (1 := e2). cbn.
      rewrite app_nil_r.
      assumption.
    }
    pose proof (red_trans _ _ _ _ _ r1 r2') as r.
    eapply conv_trans' ; revgoals.
    - eapply red_conv_r. eassumption.
    - assumption.
  Qed.

  (* tCoFix *)
  Next Obligation.
    eapply welltyped_rename ; auto.
    - exact h2.
    - apply eq_term_sym. eapply eq_term_zipx.
      eapply eq_term_upto_univ_eq_eq_term.
      eapply ssrbool.elimT.
      + eapply reflect_eq_term_upto_univ_eqb.
      + symmetry. assumption.
  Qed.
  Next Obligation.
    unshelve eapply R_stateR.
    all: try reflexivity.
    - simpl.
      eapply ssrbool.elimT.
      + eapply reflect_nleq_term.
      + eapply nleq_term_zipx.
        symmetry. assumption.
    - simpl. constructor.
  Qed.
  Next Obligation.
    destruct b ; auto.
    eapply conv_conv.
    destruct h. constructor.
    eapply conv_trans ; try eassumption.
    eapply conv_zippx ; auto.
    eapply eq_term_conv.
    symmetry in eq1.
    eapply eq_term_upto_univ_eq_eq_term.
    eapply ssrbool.elimT.
    - eapply reflect_eq_term_upto_univ_eqb.
    - assumption.
  Qed.

  (* Fallback *)
  Next Obligation.
    unshelve eapply R_stateR.
    all: try reflexivity.
    simpl. constructor.
  Qed.

  Definition Aux' Γ t args l1 π1 π2 h2 :=
     forall u1 u2 ca1 a1 ρ2
       (h1' : wtp Γ u1 (coApp (mkApps t ca1) (appstack a1 π1)))
       (h2' : wtp Γ u2 ρ2),
       let x := mkpack (Reduction u2) Γ u1 (coApp (mkApps t ca1) (appstack a1 π1)) ρ2 h2' in
       let y := mkpack Args Γ (mkApps t args) (appstack l1 π1) π2 h2 in
       S #|ca1| + #|a1| = #|args| + #|l1| ->
       pzt x = pzt y /\
       positionR (` (pps1 x)) (` (pps1 y)) ->
       Ret (Reduction u2) Γ u1 (coApp (mkApps t ca1) (appstack a1 π1)) ρ2.

  Axiom cheat : forall {A}, A.
  Tactic Notation "cheat" := exact cheat.

  Equations(noeqns) _isconv_args' (Γ : context) (t : term) (args : list term)
            (l1 : list term) (π1 : stack) (h1 : wtp Γ (mkApps t args) (appstack l1 π1))
            (l2 : list term) (π2 : stack) (h2 : wtp Γ (mkApps t args) (appstack l2 π2))
            (aux : Aux' Γ t args l1 π1 (appstack l2 π2) h2)
    : { b : bool | if b then ∥ Σ ;;; Γ |- zippx (mkApps t args) (appstack l1 π1) = zippx (mkApps t args) (appstack l2 π2) ∥ else True } by struct l1 :=
    _isconv_args' Γ t args (u1 :: l1) π1 h1 (u2 :: l2) π2 h2 aux
    with aux u1 u2 args l1 (coApp (mkApps t args) (appstack l2 π2)) _ _ _ _ Conv := {
    | @exist true H1 with _isconv_args' Γ t (args ++ [u1]) l1 π1 _ l2 π2 _ _ := {
      | @exist true H2 := yes ;
      | @exist false _ := no
      } ;
    | @exist false _ := no
    } ;

    _isconv_args' Γ t args [] ε h1 [] ε h2 aux := yes ;

    _isconv_args' Γ t args l1 π1 h1 l2 π2 h2 aux := no.
  Next Obligation.
    constructor. apply conv_refl.
  Qed.
  Next Obligation.
    split ; [ reflexivity |].
    unfold xposition. eapply positionR_poscat.
    cbn. eapply positionR_poscat. constructor.
  Qed.
  Next Obligation.
    rewrite <- mkApps_nested. assumption.
  Qed.
  Next Obligation.
    rewrite <- mkApps_nested.
    destruct H1 as [H1]. unfold zippx in H1.
    simpl in H1. rewrite 2!stack_context_appstack in H1.
    apply zipx_welltyped ; auto.
    clear aux.
    (* We get that u2 is well-typed *)
    apply welltyped_zipx in h2. cbn in h2. cbn.
    zip fold in h2.
    apply welltyped_context in h2 as hh2 ; auto. simpl in hh2.
    rewrite stack_context_appstack in hh2.
    destruct hh2 as [A2 hh2].
    destruct (inversion_App hh2) as [na2 [A2' [B2' [[?] [[hu2] [?]]]]]].
    (* We get that u1 is well-typed *)
    apply welltyped_zipx in h1. cbn in h1. cbn.
    zip fold in h1.
    apply welltyped_context in h1 as hh1 ; auto. simpl in hh1.
    rewrite stack_context_appstack in hh1.
    destruct hh1 as [A1 hh1].
    destruct (inversion_App hh1) as [na1 [A1' [B1' [[?] [[hu1] [?]]]]]].
    apply type_it_mkLambda_or_LetIn in hu1 ; auto.
    apply type_it_mkLambda_or_LetIn in hu2 ; auto.
    (* pose proof (subj_conv flags _ hΣ H1 hu1 hu2) as heq. *)
    (* Now we would like to invert heq to get equality of contexts and
       codomains.
       We would have two convertible terms against the same stack,
       so we should get the result.

       The problem is that let bindings are not injective!
       Perhaps our invariant should be to only close lambdas
       and avoid let bindings.
       Is it possible?
     *)
    cheat.
  Qed.
  Next Obligation.
    simpl in H0. destruct H0 as [eq hp].
    rewrite app_length in H. cbn in H.
    eapply aux.
    - assumption.
    - cbn. omega.
    - instantiate (1 := h2'). simpl. split.
      + rewrite <- mkApps_nested in eq. assumption.
      + subst x y.
        unfold xposition. cbn. apply positionR_poscat.
        rewrite 2!stack_position_appstack.
        rewrite <- !app_assoc. apply positionR_poscat.
        assert (h : forall n m, positionR (list_make n app_l ++ [app_r]) (list_make m app_l)).
        { clear. intro n. induction n ; intro m.
          - destruct m ; constructor.
          - destruct m.
            + constructor.
            + cbn. constructor. apply IHn.
        }
        rewrite <- list_make_app_r.
        apply (h #|a1| (S #|l1|)).
  Defined.
  Next Obligation.
    destruct H1 as [H1]. destruct H2 as [H2].
    constructor.
    unfold zippx. simpl.
    rewrite 2!decompose_stack_appstack. simpl.
    unfold zippx in H1. simpl in H1.
    unfold zippx in H2. rewrite 2!decompose_stack_appstack in H2.
    rewrite <- !mkApps_nested in H2. cbn in H2.
    rewrite 2!stack_context_decompose in H2.
    rewrite 2!stack_context_decompose.
    rewrite <- !mkApps_nested. cbn in H2.
    rewrite 2!stack_context_appstack in H1.
    case_eq (decompose_stack π1). intros args1 ρ1 e1.
    rewrite e1 in H2. cbn in H2. cbn.
    case_eq (decompose_stack π2). intros args2 ρ2 e2.
    rewrite e2 in H2. cbn in H2. cbn.
    pose proof (decompose_stack_eq _ _ _ e1).
    pose proof (decompose_stack_eq _ _ _ e2).
    subst.
    rewrite !stack_context_appstack in H1.
    rewrite !stack_context_appstack in H2.
    rewrite !stack_context_appstack.

    apply it_mkLambda_or_LetIn_stack_context_conv_inv in H1 as [? ?] ; auto.
    apply it_mkLambda_or_LetIn_stack_context_conv_inv in H2 as [? ?] ; auto.
    eapply it_mkLambda_or_LetIn_conv ; auto.
    eapply conv_trans ; eauto.
    eapply mkApps_conv_weak ; auto.
    eapply mkApps_conv_weak ; auto.
    eapply App_conv ; auto.
    eapply conv_refl.
  Qed.

  Equations(noeqns) _isconv_args (Γ : context) (t : term)
           (π1 : stack) (h1 : wtp Γ t π1)
           (π2 : stack) (h2 : wtp Γ t π2)
           (aux : Aux Args Γ t π1 π2 h2)
    : { b : bool | if b then ∥ Σ ;;; Γ |- zippx t π1 = zippx t π2 ∥ else True } :=
    _isconv_args Γ t π1 h1 π2 h2 aux with inspect (decompose_stack π1) := {
    | @exist (l1, θ1) eq1 with inspect (decompose_stack π2) := {
      | @exist (l2, θ2) eq2 with _isconv_args' Γ t [] l1 θ1 _ l2 θ2 _ _ := {
        | @exist true h := yes ;
        | @exist false _ := no
        }
      }
    }.
  Next Obligation.
    pose proof (decompose_stack_eq _ _ _ (eq_sym eq1)). subst.
    assumption.
  Qed.
  Next Obligation.
    pose proof (decompose_stack_eq _ _ _ (eq_sym eq2)). subst.
    assumption.
  Qed.
  Next Obligation.
    specialize (aux (Reduction u2)) as h. cbn in h.
    eapply h.
    - assumption.
    - pose proof (decompose_stack_eq _ _ _ (eq_sym eq1)). subst.
      instantiate (1 := h2').
      simpl in H0. destruct H0 as [eq hp].
      unshelve eapply R_positionR ; try assumption.
      simpl. f_equal. assumption.
  Qed.
  Next Obligation.
    pose proof (decompose_stack_eq _ _ _ (eq_sym eq1)). subst.
    pose proof (decompose_stack_eq _ _ _ (eq_sym eq2)). subst.
    assumption.
  Qed.

  Equations discr_construct_cofix (t : term) : Prop :=
    discr_construct_cofix (tConstruct ind n ui) := False ;
    discr_construct_cofix (tCoFix mfix idx) := False ;
    discr_construct_cofix _ := True.

  Inductive construct_cofix_view : term -> Set :=
  | ccview_construct : forall ind n ui, construct_cofix_view (tConstruct ind n ui)
  | ccview_cofix : forall mfix idx, construct_cofix_view (tCoFix mfix idx)
  | ccview_other : forall t, discr_construct_cofix t -> construct_cofix_view t.

  Equations cc_viewc t : construct_cofix_view t :=
    cc_viewc (tConstruct ind n ui) := ccview_construct ind n ui ;
    cc_viewc (tCoFix mfix idx) := ccview_cofix mfix idx ;
    cc_viewc t := ccview_other t I.

  Equations unfold_one_case (Γ : context) (c : term) (h : welltyped Σ Γ c) : option (term * stack) :=
    unfold_one_case Γ c h with inspect (reduce_stack RedFlags.default Σ Γ c ε _) := {
    | @exist (cred, ρ) eq with cc_viewc cred := {
      | ccview_construct ind n ui := Some (tConstruct ind n ui, ρ) ;
      | ccview_cofix mfix idx := Some (tCoFix mfix idx, ρ) ;
      | ccview_other t _ := None
      }
    }.

  Lemma unfold_one_case_construct_cofix :
    forall Γ t h fn ξ,
      Some (fn, ξ) = unfold_one_case Γ t h ->
      ~ (discr_construct_cofix fn).
  Proof.
    intros Γ t h fn ξ e.
    revert e.
    funelim (unfold_one_case Γ t h).
    all: intro ee. all: noconf ee.
    all: simp discr_construct_cofix.
    all: auto.
  Qed.

  Lemma unfold_one_case_stack :
    forall Γ t h fn ξ,
      Some (fn, ξ) = unfold_one_case Γ t h ->
      snd (decompose_stack ξ) = ε.
  Proof.
    intros Γ t h fn ξ e.
    revert e.
    funelim (unfold_one_case Γ t h).
    all: intro ee. all: noconf ee.
    - match type of e with
      | _ = reduce_stack ?flags ?Σ ?Γ ?t ?π ?h =>
        pose proof (reduce_stack_decompose flags Σ Γ t π h) as d
      end.
      rewrite <- e in d. cbn in d.
      assumption.
    - match type of e with
      | _ = reduce_stack ?flags ?Σ ?Γ ?t ?π ?h =>
        pose proof (reduce_stack_decompose flags Σ Γ t π h) as d
      end.
      rewrite <- e in d. cbn in d.
      assumption.
  Qed.

  Lemma unfold_one_case_red_zippx :
    forall Γ t h fn ξ,
      Some (fn, ξ) = unfold_one_case Γ t h ->
      ∥ red (fst Σ) Γ t (zippx fn ξ) ∥.
  Proof.
    intros Γ t h fn ξ e.
    revert e.
    funelim (unfold_one_case Γ t h).
    all: intro ee. all: noconf ee.
    - match type of e with
      | _ = reduce_stack ?flags ?Σ ?Γ ?t ?π ?h =>
        pose proof (reduce_stack_sound flags Σ Γ t π h) as [r1] ;
        pose proof (reduce_stack_decompose flags Σ Γ t π h) as d
      end.
      rewrite <- e in r1. cbn in r1.
      rewrite <- e in d. cbn in d.
      case_eq (decompose_stack s). intros l ρ e'.
      rewrite e' in d. cbn in d. subst.
      unfold zippx. rewrite e'. cbn.
      apply decompose_stack_eq in e' as ?. subst.
      rewrite zipc_appstack in r1. cbn in r1.
      constructor. assumption.
    - match type of e with
      | _ = reduce_stack ?flags ?Σ ?Γ ?t ?π ?h =>
        pose proof (reduce_stack_sound flags Σ Γ t π h) as [r1] ;
        pose proof (reduce_stack_decompose flags Σ Γ t π h) as d
      end.
      rewrite <- e in r1. cbn in r1.
      rewrite <- e in d. cbn in d.
      case_eq (decompose_stack s). intros l ρ e'.
      rewrite e' in d. cbn in d. subst.
      unfold zippx. rewrite e'. cbn.
      apply decompose_stack_eq in e' as ?. subst.
      rewrite zipc_appstack in r1. cbn in r1.
      constructor. assumption.
  Qed.

  Lemma unfold_one_case_red :
    forall Γ t h fn ξ,
      Some (fn, ξ) = unfold_one_case Γ t h ->
      ∥ red (fst Σ) Γ t (zipc fn ξ) ∥.
  Proof.
    intros Γ t h fn ξ e.
    revert e.
    funelim (unfold_one_case Γ t h).
    all: intro ee. all: noconf ee.
    - match type of e with
      | _ = reduce_stack ?flags ?Σ ?Γ ?t ?π ?h =>
        pose proof (reduce_stack_sound flags Σ Γ t π h) as [r1] ;
        pose proof (reduce_stack_decompose flags Σ Γ t π h) as d
      end.
      rewrite <- e in r1. cbn in r1.
      rewrite <- e in d. cbn in d.
      case_eq (decompose_stack s). intros l ρ e'.
      rewrite e' in d. cbn in d. subst.
      apply decompose_stack_eq in e' as ?. subst.
      rewrite zipc_appstack in r1. cbn in r1.
      rewrite zipc_appstack. cbn.
      constructor. assumption.
    - match type of e with
      | _ = reduce_stack ?flags ?Σ ?Γ ?t ?π ?h =>
        pose proof (reduce_stack_sound flags Σ Γ t π h) as [r1] ;
        pose proof (reduce_stack_decompose flags Σ Γ t π h) as d
      end.
      rewrite <- e in r1. cbn in r1.
      rewrite <- e in d. cbn in d.
      case_eq (decompose_stack s). intros l ρ e'.
      rewrite e' in d. cbn in d. subst.
      apply decompose_stack_eq in e' as ?. subst.
      rewrite zipc_appstack in r1. cbn in r1.
      rewrite zipc_appstack. cbn.
      constructor. assumption.
  Qed.

  (* Lemma unfold_one_case_cored : *)
  (*   forall Γ c h cred ρ, *)
  (*     Some (cred, ρ) = unfold_one_case Γ c h -> *)
  (*     cored Σ Γ (zipc cred ρ) c. *)
  (* Proof. *)
  (*   intros Γ c h cred ρ e. *)
  (*   revert e. *)
  (*   funelim (unfold_one_case Γ c h). *)
  (*   all: intro ee ; noconf ee. *)
  (*   - match type of e with *)
  (*     | _ = reduce_stack ?flags ?Σ ?Γ ?t ?π ?h => *)
  (*       pose proof (reduce_stack_sound flags Σ Γ t π h) as [r1] *)
  (*     end. *)
  (*     rewrite <- e in r1. cbn in r1. *)

  Equations reducible_head (Γ : context) (t : term) (π : stack)
            (h : wtp Γ t π)
    : option (term * stack) :=

    reducible_head Γ (tFix mfix idx) π h := unfold_one_fix Γ mfix idx π h ;

    reducible_head Γ (tCase ind p c brs) π h
    with inspect (unfold_one_case (Γ ,,, stack_context π) c _) := {
    | @exist (Some (cred, ρ)) eq := Some (tCase ind p (zipc cred ρ) brs, π) ;
    | @exist None _ := None
    } ;

    reducible_head Γ (tProj p c) π h
    with inspect (unfold_one_case (Γ ,,, stack_context π) c _) := {
    | @exist (Some (cred, ρ)) eq := Some (tProj p (zipc cred ρ), π) ;
    | @exist None _ := None
    } ;

    (* TODO tConst *)

    reducible_head Γ _ π h := None.
  Next Obligation.
    apply welltyped_zipx in h. zip fold in h.
    apply welltyped_context in h ; auto. simpl in h.
    destruct h as [T h].
    apply inversion_Case in h as X ; auto.
    destruct X as [u [npar [args [mdecl [idecl [pty [indctx [pctx [ps [btys [? [? [? [? [? [? [? [? ?]]]]]]]]]]]]]]]]]].
    eexists. eassumption.
  Qed.
  Next Obligation.
    apply welltyped_zipx in h. zip fold in h.
    apply welltyped_context in h ; auto. simpl in h.
    destruct h as [T h].
    apply inversion_Proj in h as X ; auto.
    destruct X as [u [mdecl [idecl [pdecl [args [? [? [? ?]]]]]]]].
    eexists. eassumption.
  Qed.

  Lemma reducible_head_red_zippx :
    forall Γ t π h fn ξ,
      Some (fn, ξ) = reducible_head Γ t π h ->
      ∥ red (fst Σ) Γ (zippx t π) (zippx fn ξ) ∥.
  Proof.
    intros Γ t π h fn ξ e.
    revert e.
    funelim (reducible_head Γ t π h).
    all: intro ee ; noconf ee.
    - eapply unfold_one_fix_red_zippx. eassumption.
    - apply unfold_one_case_red_zippx in e as r. destruct r as [r].
      apply unfold_one_case_stack in e as d.
      case_eq (decompose_stack s). intros l s0 ee.
      unfold zippx in r. rewrite ee in r.
      rewrite ee in d. cbn in d. subst.
      apply decompose_stack_eq in ee. subst.
      cbn in r.
      constructor.
      unfold zippx.
      case_eq (decompose_stack π). intros l1 ρ ee.
      rewrite zipc_appstack. cbn.
      eapply red_it_mkLambda_or_LetIn.
      eapply red_mkApps.
      apply decompose_stack_eq in ee. subst.
      rewrite stack_context_appstack in r.
      induction r.
      + constructor.
      + econstructor ; eauto.
        constructor. assumption.
    - apply unfold_one_case_red_zippx in e as r. destruct r as [r].
      apply unfold_one_case_stack in e as d.
      case_eq (decompose_stack s). intros l s0 ee.
      unfold zippx in r. rewrite ee in r.
      rewrite ee in d. cbn in d. subst.
      apply decompose_stack_eq in ee. subst.
      cbn in r.
      constructor.
      unfold zippx.
      case_eq (decompose_stack π). intros l1 ρ ee.
      rewrite zipc_appstack. cbn.
      eapply red_it_mkLambda_or_LetIn.
      eapply red_mkApps.
      apply decompose_stack_eq in ee. subst.
      rewrite stack_context_appstack in r.
      induction r.
      + constructor.
      + econstructor ; eauto.
        constructor. assumption.
  Qed.

  Lemma reducible_head_red :
    forall Γ t π h fn ξ,
      Some (fn, ξ) = reducible_head Γ t π h ->
      ∥ red (fst Σ) Γ (zipc t π) (zipc fn ξ) ∥.
  Proof.
    intros Γ t π h fn ξ e.
    revert e.
    funelim (reducible_head Γ t π h).
    all: intro ee ; noconf ee.
    - eapply unfold_one_fix_red. eassumption.
    - apply unfold_one_case_red in e as r. destruct r as [r].
      apply unfold_one_case_stack in e as d.
      case_eq (decompose_stack s). intros l s0 ee.
      rewrite ee in d. cbn in d. subst.
      constructor.
      eapply red_context.
      induction r.
      + constructor.
      + econstructor ; eauto.
        constructor. assumption.
    - apply unfold_one_case_red in e as r. destruct r as [r].
      apply unfold_one_case_stack in e as d.
      case_eq (decompose_stack s). intros l s0 ee.
      rewrite ee in d. cbn in d. subst.
      constructor.
      eapply red_context.
      induction r.
      + constructor.
      + econstructor ; eauto.
        constructor. assumption.
  Qed.

  Derive Signature for whnf.
  Derive Signature for whne.

  Lemma reducible_head_reduce_cored :
    forall Γ t π fn ξ l θ t' ρ h h',
      Some (fn, ξ) = reducible_head Γ t π h ->
      (l, θ) = decompose_stack ξ ->
      (t', ρ) = reduce_stack nodelta_flags Σ (Γ ,,, stack_context ξ)
                            fn (appstack l ε) h' ->
      cored Σ Γ (zipc t' (ρ +++ θ)) (zipc t π).
  Proof.
    intros Γ t π fn ξ l θ t' ρ h h' e1 e2 e3.
    revert e1.
    funelim (reducible_head Γ t π h).
    all: intro e1 ; noconf e1.
    - apply unfold_one_fix_cored in e1 as r1.
      apply unfold_one_fix_decompose in e1 as d1.
      match type of e3 with
      | _ = reduce_stack ?f ?Σ ?Γ ?t ?π ?h =>
        destruct (reduce_stack_sound f Σ Γ t π h) as [r2]
      end.
      rewrite <- e3 in r2.
      eapply red_cored_cored ; try eassumption.
      cbn in r2.
      rewrite zipc_stack_cat.
      pose proof (decompose_stack_eq _ _ _ (eq_sym e2)). subst.
      rewrite !zipc_appstack in r2. cbn in r2.
      rewrite zipc_appstack.
      repeat zip fold.
      eapply red_context.
      rewrite stack_context_appstack in r2. cbn.
      assumption.
    - apply unfold_one_case_red in e as r1. destruct r1 as [r1].
      apply unfold_one_case_stack in e as d1.
      apply unfold_one_case_construct_cofix in e as hh1.
      case_eq (decompose_stack s). intros l' s0 ee.
      rewrite ee in d1. cbn in d1. subst.
      match type of e3 with
      | _ = reduce_stack ?f ?Σ ?Γ ?t ?π ?h =>
        destruct (reduce_stack_sound f Σ Γ t π h) as [r2] ;
        pose proof (reduce_stack_decompose f Σ Γ t π h) as d2 ;
        pose proof (reduce_stack_whnf f Σ Γ t π h) as w2 ;
        pose proof (reduce_stack_isred f Σ Γ t π h) as ir2
      end.
      rewrite <- e3 in r2. cbn in r2.
      rewrite <- e3 in d2. cbn in d2.
      rewrite <- e3 in w2. simpl in w2.
      rewrite <- e3 in ir2. simpl in ir2. specialize (ir2 eq_refl).
      rewrite zipc_appstack in r2. cbn in r2.
      rewrite decompose_stack_appstack in d2. cbn in d2.
      case_eq (decompose_stack ρ). intros l1 s0 e'.
      rewrite e' in d2. cbn in d2. subst.
      apply decompose_stack_eq in e' as ?. subst.
      rewrite stack_cat_appstack.
      pose proof (decompose_stack_eq _ _ _ (eq_sym e2)). subst.
      rewrite 2!zipc_appstack.
      apply decompose_stack_eq in ee as ?. subst.
      rewrite zipc_appstack in r1. cbn in r1.
      rewrite stack_context_appstack in r1.
      rewrite stack_context_appstack in r2.
      rewrite 2!zipc_appstack in r2. cbn in r2.
      repeat zip fold. eapply cored_context.
      eapply cored_red_cored.
      + eapply red_neq_cored ; try eassumption.
        intro bot.
        rewrite 2!stack_context_appstack in w2. simpl in w2.
        destruct ir2 as [nap2 _].
        simpl in nap2.
        apply mkApps_notApp_inj in bot as eq ; auto.
        destruct eq as [? ?]. subst. clear bot nap2.
        revert hh1.
        funelim (discr_construct_cofix t).
        all: auto.
        all: intros _.
        * dependent destruction w2.
          -- dependent destruction H0.
             ++
Lemma whne_mkApps_inv :
  forall flags Γ t l,
    whne flags Σ Γ (mkApps t l) ->
    whne flags Σ Γ t.
Proof.
  intros flags0 Γ t l h.
  induction l in t, h |- *.
  - assumption.
  - simpl in h. apply IHl in h. inversion h. assumption.
Qed.
apply whne_mkApps_inv in H0. dependent destruction H0.
             ++ cbn in H0. discriminate.
          -- (* Pretty clear *)
             admit.
          -- (* Pretty clear *)
             admit.
        (* Maybe we should show Req instead of cored!
           Or go for the whnf thing!
           We also should exploit the fact that unfold_one_case unsures we have
           a constructor!
         *)
        * (* Here it is less clear, we probably need to conclude form h'
             that we cannot match on CoFix? Might not even be true...
             Or maybe we should exploit unfold_one_stack in a better way.
             We should know that we are in a case where we matched on a
             constructor.
           *)
          admit.
      + eapply red_mkApps.
        eapply red_Case_c. assumption.


      (* eapply red_cored_cored ; try eassumption. *)

      (* Actually we need to use reduce_stack_Req
         to exploit the fact that we indeed reduce.
         One could also say that some extra property on whnf
         would allow us to conclude that case on a constructor
         necessarilly reduces.
         Maybe we will have to do so.

         OTHER SOLUTION: Simply say that red means cored or =
         and show that = is not possible when the lhs is case of cosntr.
       *)

  (*   - apply unfold_one_case_red in e as r. destruct r as [r]. *)
  (*     apply unfold_one_case_stack in e as d. *)
  (*     case_eq (decompose_stack s). intros l s0 ee. *)
  (*     rewrite ee in d. cbn in d. subst. *)
  (*     constructor. *)
  (*     eapply red_context. *)
  (*     induction r. *)
  (*     + constructor. *)
  (*     + econstructor ; eauto. *)
  (*       constructor. assumption. *)
  (* Qed. *)
  Admitted.

  Equations(noeqns) _isconv_fallback (Γ : context) (leq : conv_pb)
            (t1 : term) (π1 : stack) (h1 : wtp Γ t1 π1)
            (t2 : term) (π2 : stack) (h2 : wtp Γ t2 π2)
            (ir1 : isred (t1, π1)) (ir2 : isred (t2, π2))
            (aux : Aux (Fallback t2) Γ t1 π1 π2 h2)
    : { b : bool | if b then conv leq Σ Γ (zippx t1 π1) (zippx t2 π2) else True } :=
    _isconv_fallback Γ leq t1 π1 h1 t2 π2 h2 ir1 ir2 aux
    with inspect (reducible_head Γ t1 π1 h1) := {
    | @exist (Some (rt1, ρ1)) eq1 with inspect (decompose_stack ρ1) := {
      | @exist (l1, θ1) eq2
        with inspect (reduce_stack nodelta_flags Σ (Γ ,,, stack_context ρ1) rt1 (appstack l1 ε) _) := {
        | @exist (rt1', θ1') eq3 :=
          isconv_prog Γ leq rt1' (θ1' +++ θ1) t2 π2 aux
        }
      } ;
    | @exist None _ := no (* TODO *)
    }.
  Next Obligation.
    cbn. rewrite zipc_appstack. cbn.
    apply welltyped_zipx in h1 as hh1.
    apply reducible_head_red_zippx in eq1 as r.
    unfold zippx in r.
    rewrite <- eq2 in r.
    case_eq (decompose_stack π1). intros l1' ρ1' e1.
    rewrite e1 in r.
    apply welltyped_zipc_zippx in hh1 ; auto.
    apply decompose_stack_eq in e1 as ?. subst.
    unfold zippx in hh1. rewrite e1 in hh1.
    pose proof (red_welltyped flags _ hh1 r) as hh.
    apply welltyped_it_mkLambda_or_LetIn in hh.
    symmetry in eq2.
    apply decompose_stack_eq in eq2. subst.
    rewrite stack_context_appstack.
    assumption.
  Qed.
  Next Obligation.
    apply reducible_head_red in eq1 as r1. destruct r1 as [r1].
    match type of eq3 with
    | _ = reduce_stack ?f ?Σ ?Γ ?t ?π ?h =>
      destruct (reduce_stack_sound f Σ Γ t π h) as [r2] ;
      pose proof (reduce_stack_decompose nodelta_flags _ _ _ _ h) as d2
    end.
    rewrite <- eq3 in r2. cbn in r2.
    rewrite <- eq3 in d2. cbn in d2.
    rewrite decompose_stack_appstack in d2. cbn in d2.
    rewrite zipc_appstack in r2. cbn in r2.
    case_eq (decompose_stack θ1'). intros l s e.
    rewrite e in d2. cbn in d2. subst.
    apply decompose_stack_eq in e as ?. subst.
    rewrite stack_cat_appstack.
    eapply zipx_welltyped ; auto.
    rewrite zipc_appstack in r2. cbn in r2.
    rewrite zipc_appstack.
    pose proof (eq_sym eq2) as eq2'.
    apply decompose_stack_eq in eq2'. subst.
    rewrite stack_context_appstack in r2.
    eapply red_welltyped ; auto ; revgoals.
    - constructor. zip fold. eapply red_context. eassumption.
    - rewrite zipc_appstack in r1. cbn.
      eapply red_welltyped ; auto ; revgoals.
      + constructor. eassumption.
      + eapply welltyped_zipx. assumption.
  Qed.
  Next Obligation.
    eapply R_cored. simpl.
    eapply cored_it_mkLambda_or_LetIn.
    rewrite app_context_nil_l.
    eapply reducible_head_reduce_cored ; eassumption.
  Qed.
  Next Obligation.
  Admitted.
  Next Obligation.
    destruct b ; auto.
  Admitted.

  Equations _isconv (s : state) (Γ : context)
            (t : term) (π1 : stack) (h1 : wtp Γ t π1)
            (π2 : stack) (h2 : wts Γ s t π2)
            (aux : Aux s Γ t π1 π2 h2)
  : Ret s Γ t π1 π2 :=
    _isconv (Reduction t2) Γ t1 π1 h1 π2 h2 aux :=
      λ { | leq := _isconv_red Γ leq t1 π1 h1 t2 π2 h2 aux } ;

    _isconv (Term t2) Γ t1 π1 h1 π2 h2 aux :=
      λ { | leq | r1 | r2 := _isconv_prog Γ leq t1 π1 h1 t2 π2 h2 r1 r2 aux } ;

    _isconv Args Γ t π1 h1 π2 h2 aux :=
        _isconv_args Γ t π1 h1 π2 h2 aux ;

    _isconv (Fallback t2) Γ t1 π1 h1 π2 h2 aux :=
      λ { | leq | r1 | r2 := _isconv_fallback Γ leq t1 π1 h1 t2 π2 h2 r1 r2 aux }.

  Equations(noeqns) isconv_full (s : state) (Γ : context)
            (t : term) (π1 : stack) (h1 : wtp Γ t π1)
            (π2 : stack) (h2 : wts Γ s t π2)
    : Ret s Γ t π1 π2 :=

    isconv_full s Γ t π1 h1 π2 h2 :=
      Fix_F (R := R)
            (fun '(mkpack s' Γ' t' π1' π2' h2') => wtp Γ' t' π1' -> wts Γ' s' t' π2' -> Ret s' Γ' t' π1' π2')
            (fun pp f => _)
            (x := mkpack s Γ t π1 π2 _)
            _ _ _.
  Next Obligation.
    unshelve eapply _isconv ; try assumption.
    intros s' Γ' t' π1' π2' h1' h2' hR. destruct pp.
    assert (wth0 = zwts H0) by apply welltyped_irr. subst.
    specialize (f (mkpack s' Γ' t' π1' π2' (zwts h2')) hR). cbn in f.
    eapply f ; assumption.
  Qed.
  Next Obligation.
    destruct s ; assumption.
  Qed.
  Next Obligation.
    apply R_Acc. simpl. eapply welltyped_nlg ; assumption.
  Qed.

  Definition isconv Γ leq t1 π1 h1 t2 π2 h2 :=
    let '(exist b _) := isconv_full (Reduction t2) Γ t1 π1 h1 π2 h2 leq in b.

  Theorem isconv_sound :
    forall Γ leq t1 π1 h1 t2 π2 h2,
      isconv Γ leq t1 π1 h1 t2 π2 h2 ->
      conv leq Σ Γ (zippx t1 π1) (zippx t2 π2).
  Proof.
    unfold isconv.
    intros Γ leq t1 π1 h1 t2 π2 h2.
    destruct isconv_full as [[]] ; auto.
    discriminate.
  Qed.

  Definition isconv_term Γ leq t1 (h1 : welltyped Σ Γ t1) t2 (h2 : welltyped Σ Γ t2) :=
    isconv Γ leq t1 ε (zipx_welltyped flags _ hΣ (π := ε) h1) t2 ε (zipx_welltyped flags _ hΣ (π := ε) h2).

  Theorem isconv_term_sound :
    forall Γ leq t1 h1 t2 h2,
      isconv_term Γ leq t1 h1 t2 h2 ->
      conv leq Σ Γ t1 t2.
  Proof.
    intros Γ leq t1 h1 t2 h2.
    unfold isconv_term. intro h.
    apply isconv_sound in h. assumption.
  Qed.

End Conversion.