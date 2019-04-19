(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia
     Classes.RelationClasses.
From Template Require Import config univ monad_utils utils BasicAst AstUtils
     UnivSubst.
From PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICReflect
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICSafeReduce PCUICCumulativity
     PCUICSR PCUICPosition.
From Equations Require Import Equations.

Require Import Equations.Prop.DepElim.

Import MonadNotation.

Module PSR := PCUICSafeReduce.

(** * Conversion for PCUIC without fuel

  Following PCUICSafereduce, we derive a fuel-free implementation of
  conversion (and cumulativity) checking for PCUIC.

 *)

Inductive conv_pb :=
| Conv
| Cumul.

Section Conversion.

  Context (flags : RedFlags.t).
  (* Context `{checker_flags}. *)
  Context (Σ : global_context).
  Context (hΣ : wf Σ).

  Tactic Notation "zip" "fold" "in" hyp(h) :=
    lazymatch type of h with
    | context C[ zipc ?t ?π ] =>
      let C' := context C[ zip (t,π) ] in
      change C' in h
    end.

  Tactic Notation "zip" "fold" :=
    lazymatch goal with
    | |- context C[ zipc ?t ?π ] =>
      let C' := context C[ zip (t,π) ] in
      change C'
    end.

  Definition conv leq Σ Γ u v :=
    match leq with
    | Conv => ∥ Σ ;;; Γ |- u = v ∥
    | Cumul => ∥ Σ ;;; Γ |- u <= v ∥
    end.

  Definition nodelta_flags := RedFlags.mk true true true false true true.

  Lemma red_welltyped :
    forall {Γ u v},
      welltyped Σ Γ u ->
      ∥ red (fst Σ) Γ u v ∥ ->
      welltyped Σ Γ v.
  Proof.
    intros Γ u v h [r].
    revert h. induction r ; intros h.
    - assumption.
    - specialize IHr with (1 := ltac:(eassumption)).
      destruct IHr as [A ?]. exists A.
      eapply PSR.subject_reduction ; eassumption.
  Qed.

  Set Equations With UIP.

  Lemma cored_it_mkLambda_or_LetIn :
    forall Γ Δ u v,
      cored Σ (Γ ,,, Δ) u v ->
      cored Σ Γ (it_mkLambda_or_LetIn Δ u)
               (it_mkLambda_or_LetIn Δ v).
  Proof.
    intros Γ Δ u v h.
    induction h.
    - constructor. apply red1_it_mkLambda_or_LetIn. assumption.
    - eapply cored_trans.
      + eapply IHh.
      + apply red1_it_mkLambda_or_LetIn. assumption.
  Qed.

  Lemma red_it_mkLambda_or_LetIn :
    forall Γ Δ u v,
      red Σ (Γ ,,, Δ) u v ->
      red Σ Γ (it_mkLambda_or_LetIn Δ u)
              (it_mkLambda_or_LetIn Δ v).
  Proof.
    intros Γ Δ u v h.
    induction h.
    - constructor.
    - econstructor.
      + eassumption.
      + eapply red1_it_mkLambda_or_LetIn. assumption.
  Qed.

  Lemma cored_zipx :
    forall Γ u v π,
      cored Σ (Γ ,,, stack_context π) u v ->
      cored Σ [] (zipx Γ u π) (zipx Γ v π).
  Proof.
    intros Γ u v π h.
    eapply cored_it_mkLambda_or_LetIn.
    eapply cored_context.
    rewrite app_context_nil_l.
    assumption.
  Qed.

  Lemma red_trans :
    forall Γ u v w,
      red (fst Σ) Γ u v ->
      red (fst Σ) Γ v w ->
      red (fst Σ) Γ u w.
  Proof.
    intros Γ u v w h1 h2.
    revert u h1. induction h2 ; intros u h1.
    - assumption.
    - specialize IHh2 with (1 := h1).
      eapply trans_red.
      + eapply IHh2.
      + assumption.
  Qed.

  Lemma conv_refl' :
    forall leq Γ t,
      conv leq Σ Γ t t.
  Proof.
    intros leq Γ t.
    destruct leq.
    - cbn. constructor. apply conv_refl.
    - cbn. constructor. apply cumul_refl'.
  Qed.

  Lemma conv_sym :
    forall Γ u v,
      Σ ;;; Γ |- u = v ->
      Σ ;;; Γ |- v = u.
  Proof.
    intros Γ u v [h1 h2].
    econstructor ; assumption.
  Qed.

  Lemma conv_conv :
    forall {Γ leq u v},
      ∥ Σ ;;; Γ |- u = v ∥ ->
      conv leq Σ Γ u v.
  Proof.
    intros Γ leq u v h.
    destruct leq.
    - assumption.
    - destruct h as [[h1 h2]]. cbn.
      constructor. assumption.
  Qed.

  Lemma eq_term_conv :
    forall {Γ u v},
      eq_term (snd Σ) u v ->
      Σ ;;; Γ |- u = v.
  Proof.
    intros Γ u v e.
    constructor.
    - eapply cumul_refl.
      eapply eq_term_leq_term. assumption.
    - eapply cumul_refl.
      eapply eq_term_leq_term.
      eapply eq_term_sym.
      assumption.
  Qed.

  Lemma conv_trans :
    forall Γ u v w,
      Σ ;;; Γ |- u = v ->
      Σ ;;; Γ |- v = w ->
      Σ ;;; Γ |- u = w.
  Proof.
    intros Γ u v w h1 h2.
    destruct h1, h2. constructor ; eapply cumul_trans ; eassumption.
  Qed.

  Lemma conv_trans' :
    forall leq Γ u v w,
      conv leq Σ Γ u v ->
      conv leq Σ Γ v w ->
      conv leq Σ Γ u w.
  Proof.
    intros leq Γ u v w h1 h2.
    destruct leq.
    - cbn in *. destruct h1, h2. constructor.
      eapply conv_trans ; eassumption.
    - cbn in *. destruct h1, h2. constructor. eapply cumul_trans ; eassumption.
  Qed.

  Lemma red_conv_l :
    forall leq Γ u v,
      red (fst Σ) Γ u v ->
      conv leq Σ Γ u v.
  Proof.
    intros leq Γ u v h.
    induction h.
    - apply conv_refl'.
    - eapply conv_trans' ; try eassumption.
      destruct leq.
      + simpl. constructor. constructor.
        * eapply cumul_red_l.
          -- eassumption.
          -- eapply cumul_refl'.
        * eapply cumul_red_r.
          -- eapply cumul_refl'.
          -- assumption.
      + simpl. constructor.
        eapply cumul_red_l.
        * eassumption.
        * eapply cumul_refl'.
  Qed.

  Lemma red_conv_r :
    forall leq Γ u v,
      red (fst Σ) Γ u v ->
      conv leq Σ Γ v u.
  Proof.
    intros leq Γ u v h.
    induction h.
    - apply conv_refl'.
    - eapply conv_trans' ; try eassumption.
      destruct leq.
      + simpl. constructor. constructor.
        * eapply cumul_red_r.
          -- eapply cumul_refl'.
          -- assumption.
        * eapply cumul_red_l.
          -- eassumption.
          -- eapply cumul_refl'.
      + simpl. constructor.
        eapply cumul_red_r.
        * eapply cumul_refl'.
        * assumption.
  Qed.

  Lemma conv_conv_l :
    forall leq Γ u v,
        Σ ;;; Γ |- u = v ->
        conv leq Σ Γ u v.
  Proof.
    intros [] Γ u v [h1 h2].
    - cbn. constructor. constructor ; assumption.
    - cbn. constructor. assumption.
  Qed.

  Lemma conv_conv_r :
    forall leq Γ u v,
        Σ ;;; Γ |- u = v ->
        conv leq Σ Γ v u.
  Proof.
    intros [] Γ u v [h1 h2].
    - cbn. constructor. constructor ; assumption.
    - cbn. constructor. assumption.
  Qed.

  Lemma cumul_App_l :
    forall {Γ f g x},
      Σ ;;; Γ |- f <= g ->
      Σ ;;; Γ |- tApp f x <= tApp g x.
  Proof.
    intros Γ f g x h.
    induction h.
    - eapply cumul_refl. cbn.
      rewrite e. rewrite eq_term_refl.
      reflexivity.
    - eapply cumul_red_l ; try eassumption.
      econstructor. assumption.
    - eapply cumul_red_r ; try eassumption.
      econstructor. assumption.
  Qed.

  Lemma conv_App_r :
    forall {Γ f x y},
      Σ ;;; Γ |- x = y ->
      Σ ;;; Γ |- tApp f x = tApp f y.
  Proof.
    intros Γ f x y [h1 h2].
  Admitted.

  Lemma conv_Prod_l :
    forall {Γ na A1 A2 B},
      Σ ;;; Γ |- A1 = A2 ->
      Σ ;;; Γ |- tProd na A1 B = tProd na A2 B.
  Proof.
  Admitted.

  Lemma cumul_Prod_r :
    forall {Γ na A B1 B2},
      Σ ;;; Γ ,, vass na A |- B1 <= B2 ->
      Σ ;;; Γ |- tProd na A B1 <= tProd na A B2.
  Proof.
    intros Γ na A B1 B2 h.
    induction h.
    - eapply cumul_refl. cbn. rewrite e.
      rewrite eq_term_refl. reflexivity.
    - eapply cumul_red_l ; try eassumption.
      econstructor. assumption.
    - eapply cumul_red_r ; try eassumption.
      econstructor. assumption.
  Qed.

  Lemma conv_Prod :
    forall leq Γ na na' A1 A2 B1 B2,
      Σ ;;; Γ |- A1 = A2 ->
      conv leq Σ (Γ,, vass na A1) B1 B2 ->
      conv leq Σ Γ (tProd na A1 B1) (tProd na' A2 B2).
  Admitted.

  Lemma cumul_context :
    forall Γ u v ρ,
      Σ ;;; Γ |- u <= v ->
      Σ ;;; Γ |- zipc u ρ <= zipc v ρ.
  Proof.
    intros Γ u v ρ h.
    revert u v h. induction ρ ; intros u v h.
    - cbn. assumption.
    - cbn. apply IHρ.
      eapply cumul_App_l. assumption.
    - cbn. eapply IHρ.
      (* eapply conv_App_r. *)
      (* Congruence for application on the right *)
      admit.
    - cbn.
      (* Congruence for case *)
      admit.
  Admitted.

  Lemma conv_context :
    forall Γ u v ρ,
      Σ ;;; Γ |- u = v ->
      Σ ;;; Γ |- zipc u ρ = zipc v ρ.
  Proof.
    intros Γ u v ρ [].
    constructor ; eapply cumul_context ; assumption.
  Qed.

  Lemma conv_context' :
    forall Γ leq u v ρ,
      conv leq Σ Γ u v ->
      conv leq Σ Γ (zipc u ρ) (zipc v ρ).
  Proof.
    intros Γ leq u v ρ h.
    destruct leq.
    - cbn in *. destruct h as [[h1 h2]]. constructor.
      constructor ; eapply cumul_context ; assumption.
    - cbn in *. destruct h. constructor.
      eapply cumul_context. assumption.
  Qed.

  Inductive state :=
  | Reduction (t : term)
  | Term (t : term)
  | Args.
  (* | Fallback *) (* TODO *)

  Inductive stateR : state -> state -> Prop :=
  | stateR_Term_Reduction : forall u v, stateR (Term u) (Reduction v)
  | stateR_Arg_Term : forall u, stateR Args (Term u).

  Derive Signature for stateR.

  Lemma stateR_Acc :
    forall s, Acc stateR s.
  Proof.
    assert (Acc stateR Args) as hArgs.
    { constructor. intros s h.
      dependent induction h.
      all: try discriminate.
    }
    assert (forall t, Acc stateR (Term t)) as hTerm.
    { intros t. constructor. intros s h.
      dependent induction h.
      all: try discriminate.
      apply hArgs.
    }
    assert (forall t, Acc stateR (Reduction t)) as hRed.
    { intros t. constructor. intros s h.
      dependent induction h.
      all: try discriminate.
      apply hTerm.
    }
    intro s. destruct s ; eauto.
  Qed.

  Notation pack := (state * context * term * stack * stack)%type.

  Definition dumbR (u v : pack) := False.

  Notation "( x ; y )" := (existT _ x y).

  Definition lexprod := Subterm.lexprod.
  Arguments lexprod {_ _} _ _ _ _.

  Definition ctx (x : pack) :=
    let '(s, Γ, u, π1, π2) := x in Γ.

  Definition tm (x : pack) :=
    let '(s, Γ, u, π1, π2) := x in u.

  Definition stk1 (x : pack) :=
    let '(s, Γ, u, π1, π2) := x in π1.

  Definition stk2 (x : pack) :=
    let '(s, Γ, u, π1, π2) := x in π2.

  Definition st (x : pack) :=
    let '(s, Γ, u, π1, π2) := x in s.

  Definition R_aux :=
    dlexprod (cored Σ []) (fun t => lexprod (@posR t) stateR).

  Notation obpack u :=
    (zipx (ctx u) (tm u) (stk1 u) ; (xpos (ctx u) (tm u) (stk1 u), st u))
    (only parsing).

  Definition R (u v : pack) :=
    R_aux (obpack u) (obpack v).

  Lemma R_aux_Acc :
    forall t p s,
      welltyped Σ [] t ->
      Acc R_aux (t ; (p, s)).
  Proof.
    intros t p s h.
    eapply dlexprod_Acc.
    - intro u. eapply Subterm.wf_lexprod.
      + intro. eapply posR_Acc.
      + intro. eapply stateR_Acc.
    - eapply normalisation. eassumption.
  Qed.

  Lemma R_Acc :
    forall u,
      welltyped Σ [] (zipx (ctx u) (tm u) (stk1 u)) ->
      Acc R u.
  Proof.
    intros [[[[s Γ] t] π1] π2] h.
    cbn in h.
    pose proof (R_aux_Acc (zipx Γ t π1) (xpos Γ t π1) s h) as hacc.
    clear h. dependent induction hacc.
    constructor. intros [[[[r Δ] u] θ1] θ2] h'.
    eapply H0 ; try reflexivity.
    assumption.
  Qed.

  Notation coe P h t := (eq_rect_r P t h).

  Lemma R_posR :
    forall t1 t2 (p1 : pos t1) (p2 : pos t2) s1 s2 (e : t1 = t2),
      posR p1 (coe _ e p2) ->
      R_aux (t1 ; (p1, s1)) (t2 ; (p2, s2)).
  Proof.
    intros t1 t2 p1 p2 s1 s2 e h.
    subst. cbn in h. right. left. assumption.
  Qed.

  Lemma R_positionR :
    forall t1 t2 (p1 : pos t1) (p2 : pos t2) s1 s2,
      t1 = t2 ->
      positionR (` p1) (` p2) ->
      R_aux (t1 ; (p1, s1)) (t2 ; (p2, s2)).
  Proof.
    intros t1 t2 p1 p2 s1 s2 e h.
    subst. right. left. assumption.
  Qed.

  Lemma R_stateR :
    forall t1 t2 (p1 : pos t1) (p2 : pos t2) s1 s2,
      t1 = t2 ->
      ` p1 = ` p2 ->
      stateR s1 s2 ->
      R_aux (t1 ; (p1, s1)) (t2 ; (p2, s2)).
  Proof.
    intros t1 t2 [p1 hp1] [p2 hp2] s1 s2 e1 e2 h.
    cbn in e2. subst.
    pose proof (uip hp1 hp2). subst.
    right. right. assumption.
  Qed.

  Lemma inversion_LetIn :
    forall {Γ na b B t T},
      Σ ;;; Γ |- tLetIn na b B t : T ->
      exists s1 A,
        ∥ Σ ;;; Γ |- B : tSort s1 ∥ /\
        ∥ Σ ;;; Γ |- b : B ∥ /\
        ∥ Σ ;;; Γ ,, vdef na b B |- t : A ∥ /\
        ∥ Σ ;;; Γ |- tLetIn na b B A <= T ∥.
  Proof.
    intros Γ na b B t T h. dependent induction h.
    - exists s1, b'_ty. split ; [| split ; [| split]].
      + constructor. assumption.
      + constructor. assumption.
      + constructor. assumption.
      + constructor. apply cumul_refl'.
    - destruct IHh as [s1 [A' [? [? [? hc]]]]].
      exists s1, A'. split ; [| split ; [| split]].
      all: try assumption.
      destruct hc.
      constructor. eapply cumul_trans ; eassumption.
  Qed.

  Lemma welltyped_it_mkLambda_or_LetIn :
    forall Γ Δ t,
      welltyped Σ Γ (it_mkLambda_or_LetIn Δ t) ->
      welltyped Σ (Γ ,,, Δ) t.
  Proof.
    intros Γ Δ t h.
    revert Γ t h.
    induction Δ as [| [na [b|] A] Δ ih ] ; intros Γ t h.
    - assumption.
    - simpl. apply ih in h. cbn in h.
      destruct h as [T h].
      pose proof (inversion_LetIn h) as [s1 [A' [[?] [[?] [[?] [?]]]]]].
      exists A'. assumption.
    - simpl. apply ih in h. cbn in h.
      destruct h as [T h].
      pose proof (inversion_Lambda h) as [s1 [B [[?] [[?] [?]]]]].
      exists B. assumption.
  Qed.

  Definition Ret s Γ t π π' :=
    match s with
    | Reduction t'
    | Term t' =>
      forall leq, { b : bool | if b then conv leq Σ Γ (zippx t π) (zippx t' π') else True }
    | Args =>
      { b : bool | if b then ∥ Σ ;;; Γ |- zippx t π = zippx t π' ∥ else True }
    end.

  Notation wtp Γ t π :=
    (welltyped Σ Γ (zippx t π)) (only parsing).

  Definition wts Γ s t π :=
    match s with
    | Reduction t'
    | Term t' => wtp Γ t' π
    | Args => wtp Γ t π
    end.

  Definition Aux s Γ t π1 π2 :=
     forall s' Γ' t' π1' π2',
       wtp Γ' t' π1' ->
       wts Γ' s' t' π2' ->
       R (s', Γ', t', π1', π2') (s, Γ, t, π1, π2) ->
       Ret s' Γ' t' π1' π2'.

  Notation no := (exist false I) (only parsing).
  Notation yes := (exist true _) (only parsing).

  Notation repack e := (let '(exist b h) := e in exist b _) (only parsing).

  Notation isconv_red_raw Γ leq t1 π1 t2 π2 aux :=
    (aux (Reduction t2) Γ t1 π1 π2 _ _ _ leq) (only parsing).
  Notation isconv_prog_raw Γ leq t1 π1 t2 π2 aux :=
    (aux (Term t2) Γ t1 π1 π2 _ _ _ leq) (only parsing).
  Notation isconv_args_raw Γ t π1 π2 aux :=
    (aux Args Γ t π1 π2 _ _ _) (only parsing).

  Notation isconv_red Γ leq t1 π1 t2 π2 aux :=
    (repack (isconv_red_raw Γ leq t1 π1 t2 π2 aux)) (only parsing).
  Notation isconv_prog Γ leq t1 π1 t2 π2 aux :=
    (repack (isconv_prog_raw Γ leq t1 π1 t2 π2 aux)) (only parsing).
  Notation isconv_args Γ t π1 π2 aux :=
    (repack (isconv_args_raw Γ t π1 π2 aux)) (only parsing).

  Equations(noeqns) _isconv_red (Γ : context) (leq : conv_pb)
            (t1 : term) (π1 : stack) (h1 : wtp Γ t1 π1)
            (t2 : term) (π2 : stack) (h2 : wtp Γ t2 π2)
            (aux : Aux (Reduction t2) Γ t1 π1 π2)
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
    unfold zippx in h1. rewrite <- e1 in h1.
    apply welltyped_it_mkLambda_or_LetIn in h1.
    cbn. rewrite zipc_appstack. cbn.
    pose proof (decompose_stack_eq _ _ _ (eq_sym e1)). subst.
    rewrite stack_context_appstack. assumption.
  Qed.
  Next Obligation.
    unfold zippx in h2. rewrite <- e2 in h2.
    apply welltyped_it_mkLambda_or_LetIn in h2.
    cbn. rewrite zipc_appstack. cbn.
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
    unfold zippx in h1.
    rewrite decompose_stack_appstack in h1.
    rewrite decompose_stack_twice with (1 := eq_sym e1) in h1. simpl in h1.
    rewrite app_nil_r in h1.
    (* apply welltyped_it_mkLambda_or_LetIn in h1. *)
    case_eq (decompose_stack π1'). intros args1' ρ1' e1'.
    rewrite e1' in d1. cbn in d1.
    rewrite decompose_stack_appstack in d1. cbn in d1. subst.
    pose proof (decompose_stack_eq _ _ _ e1'). subst.
    rewrite stack_cat_appstack.
    unfold zippx.
    rewrite decompose_stack_appstack.
    rewrite decompose_stack_twice with (1 := eq_sym e1). simpl.
    rewrite app_nil_r.

    rewrite stack_context_appstack in r1. cbn in r1.
    rewrite 2!zipc_appstack in r1. cbn in r1.

    eapply red_welltyped.
    - exact h1.
    - constructor. eapply red_it_mkLambda_or_LetIn. assumption.
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
    clear eq1 eq2.
    unfold zippx in h2.
    rewrite decompose_stack_appstack in h2.
    rewrite decompose_stack_twice with (1 := eq_sym e2) in h2. simpl in h2.
    rewrite app_nil_r in h2.
    (* apply welltyped_it_mkLambda_or_LetIn in h2. *)
    case_eq (decompose_stack π2'). intros args2' ρ2' e2'.
    rewrite e2' in d2. cbn in d2.
    rewrite decompose_stack_appstack in d2. cbn in d2. subst.
    pose proof (decompose_stack_eq _ _ _ e2'). subst.
    rewrite stack_cat_appstack.
    unfold zippx.
    rewrite decompose_stack_appstack.
    rewrite decompose_stack_twice with (1 := eq_sym e2). simpl.
    rewrite app_nil_r.

    rewrite stack_context_appstack in r2. cbn in r2.
    rewrite 2!zipc_appstack in r2. cbn in r2.

    eapply red_welltyped.
    - exact h2.
    - constructor. eapply red_it_mkLambda_or_LetIn. assumption.
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
    - clear eq2. rewrite e in eq1. inversion eq1. subst.
      unshelve eapply R_stateR.
      + simpl. rewrite stack_cat_appstack. reflexivity.
      + simpl. rewrite stack_cat_appstack. reflexivity.
      + simpl. constructor.
    - rewrite <- eq1 in h.
      rewrite stack_context_appstack in h.
      dependent destruction h.
      + cbn in H. rewrite zipc_appstack in H. cbn in H.
        left. simpl. eapply cored_it_mkLambda_or_LetIn.
        rewrite app_context_nil_l.
        rewrite zipc_appstack. rewrite zipc_stack_cat.
        repeat zip fold. eapply cored_context.
        assumption.
      + destruct y' as [q hq].
        cbn in H0. inversion H0. (* Why is noconf failing at this point? *)
        subst.
        unshelve eapply R_positionR.
        * simpl. unfold zipx. f_equal.
          rewrite zipc_stack_cat. rewrite <- H2.
          rewrite 2!zipc_appstack. cbn. reflexivity.
        * simpl. unfold xposition. eapply positionR_poscat.
          unfold posR in H. cbn in H.
          rewrite stack_position_appstack in H. cbn in H.
          rewrite stack_position_stack_cat.
          rewrite stack_position_appstack.
          eapply positionR_poscat. assumption.
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
    unfold zippx in h1.
    rewrite decompose_stack_appstack in h1.
    rewrite decompose_stack_twice with (1 := eq_sym e1) in h1. simpl in h1.
    rewrite app_nil_r in h1.
    case_eq (decompose_stack π1'). intros args1' ρ1' e1'.
    rewrite e1' in d1. cbn in d1.
    rewrite decompose_stack_appstack in d1. cbn in d1. subst.
    pose proof (decompose_stack_eq _ _ _ e1'). subst.

    pose proof (decompose_stack_eq _ _ _ (eq_sym e2)). subst.
    unfold zippx in h2.
    rewrite decompose_stack_appstack in h2.
    rewrite decompose_stack_twice with (1 := eq_sym e2) in h2. simpl in h2.
    rewrite app_nil_r in h2.
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

  Lemma lookup_env_const_name :
    forall {c c' d},
      lookup_env Σ c' = Some (ConstantDecl c d) ->
      c' = c.
  Proof.
    intros c c' d e. clear hΣ.
    destruct Σ as [Σ' ?]. cbn in e.
    induction Σ'.
    - cbn in e. discriminate.
    - destruct a.
      + cbn in e. destruct (ident_eq_spec c' k).
        * subst. inversion e. reflexivity.
        * apply IHΣ'. assumption.
      + cbn in e. destruct (ident_eq_spec c' k).
        * inversion e.
        * apply IHΣ'. assumption.
  Qed.

  Lemma red_const :
    forall {Γ n c u cty cb cu},
      Some (ConstantDecl n {| cst_type := cty ; cst_body := Some cb ; cst_universes := cu |})
      = lookup_env Σ c ->
      red (fst Σ) Γ (tConst c u) (subst_instance_constr u cb).
  Proof.
    intros Γ n c u cty cb cu e.
    symmetry in e.
    pose proof (lookup_env_const_name e). subst.
    econstructor.
    - econstructor.
    - econstructor.
      + exact e.
      + reflexivity.
  Qed.

  Derive Signature for cumul.
  Derive Signature for red1.

  Lemma context_conversion :
    forall {Γ t T Γ'},
      Σ ;;; Γ |- t : T ->
      PCUICSR.conv_context Σ Γ Γ' ->
      Σ ;;; Γ' |- t : T.
  Admitted.

  (* Not clear what we want here.
     Let's figure out the rest first.
   *)
  Equations unfold_one_fix (Γ : context) (mfix : mfixpoint term)
            (idx : nat) (π : stack) (h : welltyped Σ Γ (zippx (tFix mfix idx) π))
    : option term :=

    unfold_one_fix Γ mfix idx π h with inspect (unfold_fix mfix idx) := {
    | @exist (Some (arg, fn)) eq1 with inspect (decompose_stack_at π arg) := {
      | @exist (Some (l, c, θ)) eq2 with inspect (reduce_stack RedFlags.default Σ Γ c ε _) := {
        | @exist (cred, ρ) eq3 with construct_viewc cred := {
          | view_construct ind n ui := Some fn ;
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
    unfold zippx in h. rewrite decompose_stack_appstack in h.
    simpl in h.
    apply welltyped_it_mkLambda_or_LetIn in h.
  (*   rewrite zipc_appstack in h. cbn in h. *)
  (*   zip fold in h. apply welltyped_context in h. cbn in h. *)
  (*   destruct h as [T h]. *)
  (*   destruct (inversion_App h) as [na [A' [B' [[?] [[?] [?]]]]]]. *)
  (*   eexists. eassumption. *)
  (* Qed. *)
  Admitted.

  Derive NoConfusion NoConfusionHom for option.

  Lemma unfold_one_fix_red :
    forall Γ mfix idx π h fn,
      Some fn = unfold_one_fix Γ mfix idx π h ->
      red (fst Σ) Γ (zipc (tFix mfix idx) π) (zipc fn π).
  Proof.
    intros Γ mfix idx π h fn eq.
    revert eq.
    funelim (unfold_one_fix Γ mfix idx π h).
    all: intro eq ; noconf eq.
    pose proof (eq_sym e0) as eq.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq). subst.
    rewrite !zipc_appstack. cbn.
    do 2 zip fold. eapply red_context.
    (* TODO Maybe we can only conclude conversion? *)
  Abort.

  Lemma welltyped_zipp :
    forall Γ t ρ,
      welltyped Σ Γ (zipp t ρ) ->
      welltyped Σ Γ t.
  Proof.
    intros Γ t ρ [A h].
    unfold zipp in h.
    case_eq (decompose_stack ρ). intros l π e.
    rewrite e in h. clear - h.
    revert t A h.
    induction l ; intros t A h.
    - eexists. cbn in h. eassumption.
    - cbn in h. apply IHl in h.
      destruct h as [T h].
      destruct (inversion_App h) as [na [A' [B' [[?] [[?] [?]]]]]].
      eexists. eassumption.
  Qed.

  Lemma welltyped_zippx :
    forall Γ t ρ,
      welltyped Σ Γ (zippx t ρ) ->
      welltyped Σ (Γ ,,, stack_context ρ) t.
  Proof.
    intros Γ t ρ h.
    unfold zippx in h.
    case_eq (decompose_stack ρ). intros l π e.
    rewrite e in h.
    apply welltyped_it_mkLambda_or_LetIn in h.
    pose proof (decompose_stack_eq _ _ _ e). subst.
    rewrite stack_context_appstack.
    clear - h. destruct h as [A h].
    revert t A h.
    induction l ; intros t A h.
    - eexists. eassumption.
    - cbn in h. apply IHl in h.
      destruct h as [B h].
      destruct (inversion_App h) as [na [A' [B' [[?] [[?] [?]]]]]].
      eexists. eassumption.
  Qed.

  Derive NoConfusion NoConfusionHom for list.

  Lemma it_mkLambda_or_LetIn_welltyped :
    forall Γ Δ t,
      welltyped Σ (Γ ,,, Δ) t ->
      welltyped Σ Γ (it_mkLambda_or_LetIn Δ t).
  Proof.
    intros Γ Δ t h.
    revert Γ t h.
    induction Δ as [| [na [b|] B] Δ ih ] ; intros Γ t h.
    - assumption.
    - simpl. eapply ih. cbn.
      destruct h as [A h].
      pose proof (typing_wf_local h) as hc.
      cbn in hc. dependent destruction hc.
      + cbn in H. inversion H.
      + cbn in H. symmetry in H. inversion H. subst. clear H.
        cbn in l.
        eexists. econstructor ; try eassumption.
        (* FIXME We need to sort B, but we only know it's a type.
           It might be a problem with the way context are wellformed.
           Let typing asks for the type to be sorted so it should
           also hold in the context.
           At least they should be synchronised.
         *)
        admit.
    - simpl. eapply ih. cbn.
      destruct h as [A h].
      pose proof (typing_wf_local h) as hc.
      cbn in hc. dependent destruction hc.
      + cbn in H. symmetry in H. inversion H. subst. clear H.
        destruct l as [s hs].
        eexists. econstructor ; eassumption.
      + cbn in H. inversion H.
  Admitted.

  Equations(noeqns) _isconv_prog (Γ : context) (leq : conv_pb)
            (t1 : term) (π1 : stack) (h1 : welltyped Σ Γ (zippx t1 π1))
            (t2 : term) (π2 : stack) (h2 : welltyped Σ Γ (zippx t2 π2))
            (aux : Aux (Term t2) Γ t1 π1 π2)
    : { b : bool | if b then conv leq Σ Γ (zippx t1 π1) (zippx t2 π2) else True } :=

    (* This case is impossible, but we would need some extra argument to make it
       truly impossible (namely, only allow results of reduce_stack with the
       right flags). *)
    (* _isconv_prog Γ leq (tApp _ _) π1 h1 (tApp _ _) π2 h2 aux := no ; *)

    _isconv_prog Γ leq (tConst c u) π1 h1 (tConst c' u') π2 h2 aux
    with eq_dec c c' := {
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

    (* It should be probable that the stacks are empty, but we are missing
       assumptions.
       Another option is to leave that for later and only match on empty
       stacks.
     *)
    _isconv_prog Γ leq (tLambda na A1 t1) π1 h1 (tLambda _ A2 t2) π2 h2 aux
    with isconv_red_raw Γ Conv A1 ε A2 ε aux := {
    | @exist true h := isconv_red (Γ,, vass na A1) leq t1 ε t2 ε aux ;
    | @exist false _ := no
    } ;

    _isconv_prog Γ leq (tProd na A1 B1) π1 h1 (tProd na' A2 B2) π2 h2 aux
    with isconv_red_raw Γ Conv A1 (Prod_l na B1 π1) A2 (Prod_l na' B2 π2) aux := {
    | @exist true h := isconv_red (Γ,, vass na A1) leq B1 ε B2 ε aux ;
    | @exist false _ := no
    } ;

    (* Hnf did not reduce, maybe delta needed in c *)
    _isconv_prog Γ leq (tCase (ind, par) p c brs) π1 h1
                       (tCase (ind',par') p' c' brs') π2 h2 aux
    with inspect (eq_term (snd Σ) p p' && eq_term (snd Σ) c c'
        && forallb2 (fun '(a, b) '(a', b') => eq_term (snd Σ) b b') brs brs') := {
    | @exist true eq1 := isconv_args Γ (tCase (ind, par) p c brs) π1 π2 aux ;
    | @exist false _ with inspect (reduce_term RedFlags.default Σ Γ c _) := {
      | @exist cred eq1 with inspect (reduce_term RedFlags.default Σ Γ c' _) := {
         | @exist cred' eq2 with inspect (eq_term (snd Σ) cred c && eq_term (snd Σ) cred' c') := {
            | @exist true eq3 := no ; (* In Checker it says yes, but wrong right? *)
            | @exist false eq3 :=
              (* In Checker, only ind, par and p are used, not clear why *)
              isconv_red Γ leq (tCase (ind, par) p cred brs) π1
                               (tCase (ind', par') p' cred' brs') π2 aux
            }
         }
      }
    } ;

    _isconv_prog Γ leq (tProj p c) π1 h1 (tProj p' c') π2 h2 aux
    with inspect (eq_projection p p' && eq_term (snd Σ) c c') := {
    | @exist true eq1 := isconv_args Γ (tProj p c) π1 π2 aux ;
    | @exist false _ := no
    } ;

    (* Subtle difference here with Checker, if the terms are syntactically equal
       but the stacks are not convertible, then we say no. *)
    _isconv_prog Γ leq (tFix mfix idx) π1 h1 (tFix mfix' idx') π2 h2 aux
    with inspect (eq_term (snd Σ) (tFix mfix idx) (tFix mfix' idx')) := {
    | @exist true eq1 := isconv_args Γ (tFix mfix idx) π1 π2 aux ;
    | @exist false _ with inspect (unfold_one_fix Γ mfix idx π1 _) := {
      | @exist (Some fn) eq1
        with inspect (reduce_stack nodelta_flags Σ Γ fn π1 _) := {
        | @exist (fn', ρ) eq2 :=
          isconv_prog Γ leq fn' ρ (tFix mfix' idx') π2 aux
        } ;
      | _ with inspect (unfold_one_fix Γ mfix' idx' π2 _) := {
        | @exist (Some fn) eq1
          with inspect (reduce_stack nodelta_flags Σ Γ fn π2 _) := {
          | @exist (fn', ρ) eq2 :=
            isconv_prog Γ leq (tFix mfix' idx') π2 fn' ρ aux
          } ;
        | _ := no
        }
      }
    } ;

    _isconv_prog Γ leq (tCoFix mfix idx) π1 h1 (tCoFix mfix' idx') π2 h2 aux
    with inspect (eq_term (snd Σ) (tCoFix mfix idx) (tCoFix mfix' idx')) := {
    | @exist true eq1 := isconv_args Γ (tCoFix mfix idx) π1 π2 aux ;
    | @exist false _ := no
    } ;

    (* TODO Fallback *)
    _isconv_prog Γ leq t1 π1 h1 t2 π2 h2 aux := no.

  (* tProd *)
  Next Obligation.
    unfold zippx. simpl.
    apply welltyped_zippx in h1.
    apply it_mkLambda_or_LetIn_welltyped.
    destruct h1 as [T h1].
    destruct (inversion_Prod h1) as [s1 [s2 [[?] [[?] [?]]]]].
    eexists. eassumption.
  Qed.
  Next Obligation.
    unfold zippx. simpl.
    apply welltyped_zippx in h2.
    apply it_mkLambda_or_LetIn_welltyped.
    destruct h2 as [T h2].
    destruct (inversion_Prod h2) as [s1 [s2 [[?] [[?] [?]]]]].
    eexists. eassumption.
  Qed.
  Next Obligation.
    unshelve eapply R_positionR.
    - reflexivity.
    - simpl. unfold xposition. eapply positionR_poscat.
      simpl. rewrite <- app_nil_r. eapply positionR_poscat. constructor.
  Qed.
  Next Obligation.
    (* Will admit in order to figure out what the stack should be. *)
  (*   zip fold in h1. apply welltyped_context in h1. cbn in h1. *)
  (*   destruct h1 as [T h1]. *)
  (*   destruct (inversion_Prod h1) as [s1 [s2 [[?] [[?] [?]]]]]. *)
  (*   eexists. eassumption. *)
  (* Qed. *)
  Admitted.
  Next Obligation.
    (* destruct h as [h]. *)
  (*   zip fold in h2. apply welltyped_context in h2. cbn in h2. *)
  (*   destruct h2 as [T h2]. *)
  (*   destruct (inversion_Prod h2) as [s1 [s2 [[?] [[?] [?]]]]]. *)
  (*   zip fold in h1. apply welltyped_context in h1. cbn in h1. *)
  (*   destruct h1 as [T' h1]. *)
  (*   destruct (inversion_Prod h1) as [s1' [s2' [[?] [[?] [?]]]]]. *)
  (*   eexists. eapply context_conversion ; try eassumption. *)
  (*   econstructor. *)
  (*   - eapply conv_context_refl ; try assumption. *)
  (*     eapply typing_wf_local. eassumption. *)
  (*   - constructor. *)
  (*     + right. eexists. eassumption. *)
  (*     + apply conv_sym. assumption. *)
  (* Qed. *)
  Admitted.
  Next Obligation.
    unshelve eapply R_positionR.
    - simpl. fail "oh no".
      (* It's not even a problem of stacks.
         On one side we'll have a λ and on the other a Π.
         This means this approach doesn't work.
         Maybe we could instead push something on the stack
         (like an alternate Prod focusing on the other side).
       *)
    (* pose proof (zip_Prod_Empty h1). subst. *)
    (* pose proof (zip_Prod_Empty h2). subst. *)
    (* R (Reduction B2, Γ,, vass na A1, B1, ε, ε) *)
    (*   (Term (tProd t2 A2 B2), Γ, tProd na A1 B1, ε, ε) *)
  Admitted.
  Next Obligation.
    destruct b ; auto.
    destruct h0 as [h0].
    pose proof (zip_Prod_Empty h1). subst.
    pose proof (zip_Prod_Empty h2). subst.
    cbn. eapply conv_Prod ; eassumption.
  Qed.

  (* tLambda *)
  Next Obligation.
    zip fold in h1. apply welltyped_context in h1. cbn in h1.
    destruct h1 as [T h1].
    destruct (inversion_Lambda h1) as [s1 [B [[?] [[?] [?]]]]].
    eexists. eassumption.
  Qed.
  Next Obligation.
    zip fold in h2. apply welltyped_context in h2. cbn in h2.
    destruct h2 as [T h2].
    destruct (inversion_Lambda h2) as [s1 [B [[?] [[?] [?]]]]].
    eexists. eassumption.
  Qed.
  Next Obligation.
    (* Maybe we'll force π1 and π2 to be ε *)
    (* R (Reduction A2, Γ, A1, ε, ε) *)
    (*   (Term (tLambda t0 A2 t2), Γ, tLambda na A1 t1, π1, π2) *)
  Admitted.
  Next Obligation.
    zip fold in h1. apply welltyped_context in h1. cbn in h1.
    destruct h1 as [T h1].
    destruct (inversion_Lambda h1) as [s1 [B [[?] [[?] [?]]]]].
    eexists. eassumption.
  Qed.
  Next Obligation.
    destruct h.
    zip fold in h1. apply welltyped_context in h1. cbn in h1.
    destruct h1 as [T h1].
    destruct (inversion_Lambda h1) as [s1 [B [[?] [[?] [?]]]]].
    zip fold in h2. apply welltyped_context in h2. cbn in h2.
    destruct h2 as [T' h2].
    destruct (inversion_Lambda h2) as [s1' [B' [[?] [[?] [?]]]]].
    eexists. eapply context_conversion ; try eassumption.
    econstructor.
    - eapply conv_context_refl ; try assumption.
      eapply typing_wf_local. eassumption.
    - constructor.
      + right. eexists. eassumption.
      + apply conv_sym. assumption.
  Qed.
  Next Obligation.
    (* Maybe we'll force π1 and π2 to be ε *)
    (* R (Reduction t2, Γ,, vass na A1, t1, ε, ε) *)
    (*   (Term (tLambda t0 A2 t2), Γ, tLambda na A1 t1, π1, π2) *)
  Admitted.
  Next Obligation.
    destruct b ; auto.
    destruct h0 as [h0].
    (* Again we need to know π1 = π2, so we might be better off
       enforcing it.
     *)
  Admitted.

  (* tConst *)
  Next Obligation.
    (* R (Args, Γ, tConst c' u', π1, π2) *)
    (*   (Term (tConst c' u'), Γ, tConst c' u', π1, π2) *)
  Admitted.
  Next Obligation.
    destruct h. eapply conv_conv_l. assumption.
  Qed.
  Next Obligation.
    eapply red_welltyped.
    - exact h1.
    - constructor. eapply red_context. eapply red_const. eassumption.
  Qed.
  Next Obligation.
    eapply red_welltyped.
    - exact h2.
    - constructor. eapply red_context. eapply red_const. eassumption.
  Qed.
  Next Obligation.
    (* tConst c' u' reduces to subst_instance_constr u' body *)
    (* R (Reduction (subst_instance_constr u' body), Γ, subst_instance_constr u' body, π1, π2) *)
    (*   (Term (tConst c' u'), Γ, tConst c' u', π1, π2) *)
  Admitted.
  Next Obligation.
    destruct b ; auto.
    eapply conv_trans'.
    - eapply red_conv_l.
      eapply red_context.
      eapply red_const. eassumption.
    - eapply conv_trans' ; try eassumption.
      eapply red_conv_r.
      eapply red_context.
      eapply red_const. eassumption.
  Qed.
  Next Obligation.
    eapply red_welltyped ; [ exact h2 | ].
    constructor. eapply red_context. eapply red_const. eassumption.
  Qed.
  Next Obligation.
    (* R (Reduction (subst_instance_constr u' b), Γ, tConst c' u, π1, π2) *)
    (*   (Term (tConst c' u'), Γ, tConst c' u, π1, π2) *)
  Admitted.
  Next Obligation.
    destruct b0 ; auto.
    eapply conv_trans' ; try eassumption.
    eapply red_conv_r.
    eapply red_context. eapply red_const. eassumption.
  Qed.
  Next Obligation.
    eapply red_welltyped ; [ exact h1 | ].
    constructor. eapply red_context. eapply red_const. eassumption.
  Qed.
  Next Obligation.
    (* Fine by reduction *)
    (* R (Reduction (tConst c' u'), Γ, subst_instance_constr u b, π1, π2) *)
    (*   (Term (tConst c' u'), Γ, tConst c' u, π1, π2) *)
  Admitted.
  Next Obligation.
    destruct b0 ; auto.
    eapply conv_trans' ; try eassumption.
    eapply red_conv_l.
    eapply red_context. eapply red_const. eassumption.
  Qed.
  Next Obligation.
    eapply red_welltyped ; [ exact h1 | ].
    constructor. eapply red_context. eapply red_const. eassumption.
  Qed.
  Next Obligation.
    (* Fine by reduction *)
    (* R (Reduction (tConst c' u'), Γ, subst_instance_constr u b, π1, π2) *)
    (*   (Term (tConst c' u'), Γ, tConst c' u, π1, π2) *)
  Admitted.
  Next Obligation.
    destruct b0 ; auto.
    eapply conv_trans' ; try eassumption.
    eapply red_conv_l.
    eapply red_context. eapply red_const. eassumption.
  Qed.
  Next Obligation.
    eapply red_welltyped ; [ exact h1 | ].
    constructor. eapply red_context. eapply red_const. eassumption.
  Qed.
  Next Obligation.
    (* Fine by reduction *)
    (* R (Reduction (tConst c' u'), Γ, subst_instance_constr u b, π1, π2) *)
    (*   (Term (tConst c' u'), Γ, tConst c' u, π1, π2) *)
  Admitted.
  Next Obligation.
    destruct b0 ; auto.
    eapply conv_trans' ; try eassumption.
    eapply red_conv_l.
    eapply red_context. eapply red_const. eassumption.
  Qed.

  (* tCase *)
  Next Obligation.
    (* How do we know ind = ind' and par = par'? *)
    (* One solution: just ask! *)
  Admitted.
  Next Obligation.
    (* R (Args, Γ, tCase (ind, par) p c brs, π1, π2) *)
    (*   (Term (tCase (ind', par') p' c' brs'), Γ, tCase (ind, par) p c brs, π1, π2) *)
  Admitted.
  Next Obligation.
    destruct b ; auto.
    eapply conv_conv.
    destruct h. constructor.
    eapply conv_trans ; try eassumption.
    eapply conv_context.
    eapply eq_term_conv.
    (* Missing ind = ind' again. *)
  Admitted.
  Next Obligation.
    zip fold in h1. apply welltyped_context in h1. cbn in h1.
    destruct h1 as [T h1].
    destruct (weak_inversion_Case h1) as [args [u [?]]].
    eexists. eassumption.
  Qed.
  Next Obligation.
    zip fold in h2. apply welltyped_context in h2. cbn in h2.
    destruct h2 as [T h2].
    destruct (weak_inversion_Case h2) as [args [u [?]]].
    eexists. eassumption.
  Qed.
  Next Obligation.
    eapply red_welltyped.
    - exact h1.
    - match goal with
      | |- context [ reduce_term ?f ?Σ ?Γ ?t ?h ] =>
        pose proof (reduce_term_sound f Σ Γ t h) as hr
      end.
      destruct hr as [hr]. constructor.
      eapply red_context.
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
    eapply red_welltyped.
    - exact h2.
    - match goal with
      | |- context [ reduce_term ?f ?Σ ?Γ ?t ?h ] =>
        pose proof (reduce_term_sound f Σ Γ t h) as hr
      end.
      destruct hr as [hr]. constructor.
      eapply red_context.
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
    (* R *)
    (* (Reduction *)
    (*    (tCase (ind', par') p' *)
    (*       (reduce_term RedFlags.default Σ Γ c' *)
    (*          (_isconv_prog_obligations_obligation_44 p' c' brs' Γ ind' par' π2 h2)) *)
    (*       brs'), Γ, *)
    (* tCase (ind, par) p *)
    (*   (reduce_term RedFlags.default Σ Γ c *)
    (*      (_isconv_prog_obligations_obligation_43 p c brs Γ ind par π1 h1)) brs, π1, *)
    (* π2) *)
    (* (Term (tCase (ind', par') p' c' brs'), Γ, tCase (ind, par) p c brs, π1, π2) *)
  Admitted.
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
      eapply red_context.
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
      eapply red_context.
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
    (* Some kind of subject conversion *)
  Admitted.
  Next Obligation.
    (* R (Args, Γ, tProj p c, π1, π2) *)
    (*   (Term (tProj p' c'), Γ, tProj p c, π1, π2) *)
  Admitted.
  Next Obligation.
    destruct b ; auto.
    eapply conv_conv.
    destruct h. constructor.
    eapply conv_trans ; try eassumption.
    eapply conv_context.
    eapply eq_term_conv.
    symmetry. assumption.
  Qed.

  (* tFix *)
  Next Obligation.
    (* Subject conversion *)
  Admitted.
  Next Obligation.
    (* R (Args, Γ, tFix mfix idx, π1, π2) *)
    (*   (Term (tFix mfix' idx'), Γ, tFix mfix idx, π1, π2) *)
  Admitted.
  Next Obligation.
    destruct b ; auto.
    destruct h as [h].
    eapply conv_conv.
    constructor.
    eapply conv_trans ; try eassumption.
    eapply conv_context.
    eapply eq_term_conv.
    symmetry. assumption.
  Qed.
  Next Obligation.
    eapply red_welltyped.
    - eapply h1.
    - constructor. eapply red_context.
      (* Need appropriate lemme on unfold_one_fix. *)
  Admitted.
  Next Obligation.
    match type of eq2 with
    | context [ reduce_stack ?f ?Σ ?Γ ?c ?π ?h ] =>
      pose proof (reduce_stack_sound f Σ Γ c π h) as hr
    end.
    destruct hr as [hr].
    rewrite <- eq2 in hr.
    eapply red_welltyped.
    - eapply h1.
    - constructor. eapply red_trans.
      + admit. (* Need appropriate lemme on unfold_one_fix. *)
      + eapply hr.
  Admitted.
  Next Obligation.
    (* R (Term (tFix mfix' idx'), Γ, fn', ρ, π2) *)
    (*   (Term (tFix mfix' idx'), Γ, tFix mfix idx, π1, π2) *)
  Admitted.
  Next Obligation.
    destruct b ; auto.
    (* Need appropriate lemme on unfold_one_fix. *)
  Admitted.
  Next Obligation.
    eapply red_welltyped.
    - eapply h2.
    - constructor. eapply red_context.
      (* Need appropriate lemme on unfold_one_fix. *)
  Admitted.
  Next Obligation.
    match type of eq2 with
    | context [ reduce_stack ?f ?Σ ?Γ ?c ?π ?h ] =>
      pose proof (reduce_stack_sound f Σ Γ c π h) as hr
    end.
    destruct hr as [hr].
    rewrite <- eq2 in hr.
    eapply red_welltyped.
    - eapply h2.
    - constructor. eapply red_trans.
      + admit. (* Need appropriate lemme on unfold_one_fix. *)
      + eapply hr.
  Admitted.
  Next Obligation.
    (* R (Term fn', Γ, tFix mfix' idx', π2, ρ) *)
    (*   (Term (tFix mfix' idx'), Γ, tFix mfix idx, π1, π2) *)
  Admitted.
  Next Obligation.
    destruct b ; auto.
    (* Need appropriate lemme on unfold_one_fix. *)
  Admitted.

  (* tCoFix *)
  Next Obligation.
    (* Subject conversion? *)
  Admitted.
  Next Obligation.
    (* R (Args, Γ, tCoFix mfix idx, π1, π2) *)
    (*   (Term (tCoFix mfix' idx'), Γ, tCoFix mfix idx, π1, π2) *)
  Admitted.
  Next Obligation.
    destruct b ; auto.
    eapply conv_conv.
    destruct h. constructor.
    eapply conv_trans ; try eassumption.
    eapply conv_context.
    eapply eq_term_conv.
    symmetry. assumption.
  Qed.

  Equations(noeqns) _isconv_args (Γ : context) (t : term)
            (π1 : stack) (h1 : welltyped Σ Γ (zipc t π1))
            (π2 : stack) (h2 : welltyped Σ Γ (zipc t π2))
            (aux : Aux Args Γ t π1 π2)
    : { b : bool | if b then ∥ Σ ;;; Γ |- zipc t π1 = zipc t π2 ∥ else True } :=

    _isconv_args Γ t (App u1 ρ1) h1 (App u2 ρ2) h2 aux
    with isconv_red_raw Γ Conv u1 ε u2 ε aux := {
    | @exist true h1 := isconv_args Γ (tApp t u1) ρ1 ρ2 aux ;
    | @exist false _ := no
    } ;

    _isconv_args Γ t ε h1 ε h2 aux := yes ;

    _isconv_args Γ t π1 h1 π2 h2 aux := no.
  Next Obligation.
    constructor.
    apply conv_refl.
  Qed.
  Next Obligation.
    zip fold in h1.
    apply welltyped_context in h1. cbn in h1.
    destruct h1 as [T h1].
    destruct (inversion_App h1) as [na [A [B [[?] [[?] [?]]]]]].
    exists A. assumption.
  Qed.
  Next Obligation.
    zip fold in h2.
    apply welltyped_context in h2. cbn in h2.
    destruct h2 as [T h2].
    destruct (inversion_App h2) as [na [A [B [[?] [[?] [?]]]]]].
    exists A. assumption.
  Qed.
  Next Obligation.
    (* R (Reduction u2, Γ, u1, ε, ε) (Args, Γ, t, App u1 ρ1, App u2 ρ2) *)
  Admitted.
  Next Obligation.
    (* Here it is a bit unclear. Maybe things would be better if a common
       type was assumed.
     *)
  Admitted.
  Next Obligation.
    (* R (Args, Γ, tApp t u1, ρ1, ρ2) (Args, Γ, t, App u1 ρ1, App u2 ρ2) *)
  Admitted.
  Next Obligation.
    destruct b ; auto.
    destruct h1 as [h1]. destruct h as [h].
    constructor.
    eapply conv_trans ; try eassumption.
    eapply conv_context. eapply conv_App_r. assumption.
  Qed.

  Lemma welltyped_it_mkLambda_or_LetIn' :
    forall Γ t,
      ∥ wf_local Σ Γ ∥ ->
      welltyped Σ Γ t ->
      welltyped Σ [] (it_mkLambda_or_LetIn Γ t).
  Proof.
    intros Γ t [hΓ] [A h].
    revert t A h.
    induction hΓ as [| Γ na B hΓ ih hl | Γ na b B hΓ ih hl] ; intros t A h.
    - eexists. eassumption.
    - destruct hl as [s hs].
      simpl. eapply ih. cbn. eapply type_Lambda ; eassumption.
    - simpl. eapply ih. cbn. eapply type_LetIn ; try eassumption.
      (* Again a universe problem! *)
      (* We don't have enough to conclude as B may only be a sort itself. *)
  Admitted.

  Lemma welltyped_it_mkLambda_or_LetIn :
    forall Γ t,
      welltyped Σ Γ t ->
      welltyped Σ [] (it_mkLambda_or_LetIn Γ t).
  Proof.
    intros Γ t h.
    eapply welltyped_it_mkLambda_or_LetIn' ; try assumption.
    destruct h as [A h]. constructor.
    eapply typing_wf_local. eassumption.
  Qed.

  Lemma welltyped_zipx :
    forall Γ t π,
      welltyped Σ Γ (zipc t π) ->
      welltyped Σ [] (zipx Γ t π).
  Proof.
    intros Γ t π h.
    eapply welltyped_it_mkLambda_or_LetIn. assumption.
  Qed.

  Equations _isconv (s : state) (Γ : context)
            (t : term) (π1 : stack) (h1 : welltyped Σ Γ (zipc t π1))
            (π2 : stack) (h2 : wts Γ s t π2)
            (aux : Aux s Γ t π1 π2)
  : Ret s Γ t π1 π2 :=
    _isconv (Reduction t2) Γ t1 π1 h1 π2 h2 aux :=
      λ { | leq := _isconv_red Γ leq t1 π1 h1 t2 π2 h2 aux } ;

    _isconv (Term t2) Γ t1 π1 h1 π2 h2 aux :=
      λ { | leq := _isconv_prog Γ leq t1 π1 h1 t2 π2 h2 aux } ;

    _isconv Args Γ t π1 h1 π2 h2 aux :=
        _isconv_args Γ t π1 h1 π2 h2 aux.

  Equations(noeqns) isconv_full (s : state) (Γ : context)
            (t : term) (π1 : stack) (h1 : welltyped Σ Γ (zipc t π1))
            (π2 : stack) (h2 : wts Γ s t π2)
    : Ret s Γ t π1 π2 :=

    isconv_full s Γ t π1 h1 π2 h2 :=
      Fix_F (R := R)
            (fun '(s', Γ', t', π1', π2') => welltyped Σ Γ' (zipc t' π1') -> wts Γ' s' t' π2' -> Ret s' Γ' t' π1' π2')
            (fun t' f => _)
            (x := (s, Γ, t, π1, π2))
            _ _ _.
  Next Obligation.
    eapply _isconv ; try assumption.
    intros s' Γ' t' π1' π2' h1' h2' hR.
    specialize (f (s', Γ', t', π1', π2') hR). cbn in f.
    eapply f ; assumption.
  Qed.
  Next Obligation.
    apply R_Acc. simpl.
    eapply welltyped_zipx ; assumption.
  Qed.

  Definition isconv Γ leq t1 π1 h1 t2 π2 h2 :=
    let '(exist b _) := isconv_full (Reduction t2) Γ t1 π1 h1 π2 h2 leq in b.

  Theorem isconv_sound :
    forall Γ leq t1 π1 h1 t2 π2 h2,
      isconv Γ leq t1 π1 h1 t2 π2 h2 ->
      conv leq Σ Γ (zipc t1 π1) (zipc t2 π2).
  Proof.
    unfold isconv.
    intros Γ leq t1 π1 h1 t2 π2 h2.
    destruct isconv_full as [[]] ; auto.
    discriminate.
  Qed.

End Conversion.