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

  (* Before we were zipping terms and stacks.
     Now, we even add the context into the mix.
   *)
  Definition zipx (Γ : context) (t : term) (π : stack) : term :=
    it_mkLambda_or_LetIn Γ (zipc t π).

  Fixpoint context_position Γ : position :=
    match Γ with
    | [] => []
    | {| decl_name := na ; decl_body := None ; decl_type := A |} :: Γ =>
      context_position Γ ++ [ lam_tm ]
    | {| decl_name := na ; decl_body := Some b ; decl_type := A |} :: Γ =>
      context_position Γ ++ [ let_in ]
    end.

  Lemma context_position_atpos :
    forall Γ t, atpos (it_mkLambda_or_LetIn Γ t) (context_position Γ) = t.
  Proof.
    intros Γ t. revert t. induction Γ as [| d Γ ih ] ; intro t.
    - reflexivity.
    - destruct d as [na [b|] A].
      + simpl. rewrite poscat_atpos. rewrite ih. reflexivity.
      + simpl. rewrite poscat_atpos. rewrite ih. reflexivity.
  Qed.

  Lemma context_position_valid :
    forall Γ t, validpos (it_mkLambda_or_LetIn Γ t) (context_position Γ).
  Proof.
    intros Γ t. revert t. induction Γ as [| [na [b|] A] Γ ih ] ; intro t.
    - reflexivity.
    - simpl. eapply poscat_valid.
      + eapply ih.
      + rewrite context_position_atpos. reflexivity.
    - simpl. eapply poscat_valid.
      + eapply ih.
      + rewrite context_position_atpos. reflexivity.
  Qed.

  Definition xposition Γ π : position :=
    context_position Γ ++ stack_position π.

  Lemma xposition_atpos :
    forall Γ t π, atpos (zipx Γ t π) (xposition Γ π) = t.
  Proof.
    intros Γ t π. unfold xposition.
    rewrite poscat_atpos.
    rewrite context_position_atpos.
    apply stack_position_atpos.
  Qed.

  Lemma xposition_valid :
    forall Γ t π, validpos (zipx Γ t π) (xposition Γ π).
  Proof.
    intros Γ t π. unfold xposition.
    eapply poscat_valid.
    - apply context_position_valid.
    - rewrite context_position_atpos.
      apply stack_position_valid.
  Qed.

  Definition xpos Γ t π : pos (zipx Γ t π) :=
    exist (xposition Γ π) (xposition_valid Γ t π).

  Lemma positionR_stack_pos_xpos :
    forall Γ π1 π2,
      positionR (stack_position π1) (stack_position π2) ->
      positionR (xposition Γ π1) (xposition Γ π2).
  Proof.
    intros Γ π1 π2 h.
    unfold xposition.
    eapply positionR_poscat. assumption.
  Qed.

  Lemma red1_it_mkLambda_or_LetIn :
    forall Γ u v,
      red1 Σ Γ u v ->
      red1 Σ [] (it_mkLambda_or_LetIn Γ u)
              (it_mkLambda_or_LetIn Γ v).
  Proof.
    intros Γ u v h.
    revert u v h.
    induction Γ as [| [na [b|] A] Γ ih ] ; intros u v h.
    - cbn. assumption.
    - simpl. eapply ih. cbn. constructor. assumption.
    - simpl. eapply ih. cbn. constructor. assumption.
  Qed.

  Lemma cored_it_mkLambda_or_LetIn :
    forall Γ u v,
      cored Σ Γ u v ->
      cored Σ [] (it_mkLambda_or_LetIn Γ u)
              (it_mkLambda_or_LetIn Γ v).
  Proof.
    intros Γ u v h.
    induction h.
    - constructor. apply red1_it_mkLambda_or_LetIn. assumption.
    - eapply cored_trans.
      + eapply IHh.
      + apply red1_it_mkLambda_or_LetIn. assumption.
  Qed.

  Lemma cored_zipx :
    forall Γ u v π,
      cored Σ Γ u v ->
      cored Σ [] (zipx Γ u π) (zipx Γ v π).
  Proof.
    intros Γ u v π h.
    eapply cored_it_mkLambda_or_LetIn.
    eapply cored_context.
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

  (* Unusable without primitive projections *)
  (* Definition R (x y : state * context * term * stack * stack) := *)
  (*   let '(s, Γ, u, π1, π2) := x in *)
  (*   let '(r, Δ, v, θ1, θ2) := y in *)
  (*   dlexprod (cored Σ Γ) (fun _ => dumbR) *)
  (*            (zipc u π1 ; x) *)
  (*            (zipc v θ1 ; y). *)

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

  (* Definition ecored u v := *)
  (*   exists Γ, cored Σ Γ u v. *)

  (* Lemma ecored_Acc : *)
  (*   forall u, *)
  (*     (exists Γ, welltyped Σ Γ u) -> *)
  (*     Acc ecored u. *)
  (* Proof. *)
  (*   intros u [Γ h]. *)
  (*   pose proof (normalisation _ _ _ h) as acc. *)
  (*   clear - acc. *)
  (*   induction acc. *)
  (*   constructor. intros y h. *)
  (*   eapply H0. *)

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

  (* Lemma right_dlex_eq : *)
  (*   forall {A B} leA (leB : forall x : A, B x -> B x -> Prop) a1 a2 b1 b2 (e : a1 = a2), *)
  (*     leB a1 b1 (coe B e b2) -> *)
  (*     dlexprod leA leB (a1 ; b1) (a2 ; b2). *)
  (* Proof. *)
  (*   intros A B leA leB a1 a2 b1 b2 e h. *)
  (*   subst. cbn in h. *)
  (*   right. assumption. *)
  (* Qed. *)

  (* Lemma right_lex_eq : *)
  (*   forall {A B} leA (leB : B -> B -> Prop) a1 a2 b1 b2, *)
  (*     a1 = a2 -> *)
  (*     leB b1 b2 -> *)
  (*     @lexprod A B leA leB (a1, b1) (a2, b2). *)
  (* Proof. *)
  (*   intros A B leA leB a1 a2 b1 b2 e h. *)
  (*   subst. right. assumption. *)
  (* Qed. *)

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
    forall t1 t2 (p1 : pos t1) (p2 : pos t2) s1 s2 (e : t1 = t2),
      p1 = coe _ e p2 ->
      stateR s1 s2 ->
      R_aux (t1 ; (p1, s1)) (t2 ; (p2, s2)).
  Proof.
    intros t1 t2 p1 p2 s1 s2 e1 e2 h.
    subst. cbn. right. right. assumption.
  Qed.

  Definition zipp t π :=
    let '(args, ρ) := decompose_stack π in
    mkApps t args.

  Definition Ret s Γ t π π' :=
    match s with
    | Reduction t'
    | Term t' =>
      forall leq, { b : bool | if b then conv leq Σ Γ (zipp t π) (zipp t' π') else True }
    | Args =>
      { b : bool | if b then ∥ Σ ;;; Γ |- zipp t π = zipp t π' ∥ else True }
    end.

  Definition wts Γ s t π :=
    match s with
    | Reduction t' => welltyped Σ Γ (zipc t' π)
    | Term t' => welltyped Σ Γ (zipc t' π)
    | Args => welltyped Σ Γ (zipc t π)
    end.

  Definition Aux s Γ t π1 π2 :=
     forall s' Γ' t' π1' π2',
       welltyped Σ Γ' (zipc t' π1') ->
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
            (t1 : term) (π1 : stack) (h1 : welltyped Σ Γ (zipc t1 π1))
            (t2 : term) (π2 : stack) (h2 : welltyped Σ Γ (zipc t2 π2))
            (aux : Aux (Reduction t2) Γ t1 π1 π2)
    : { b : bool | if b then conv leq Σ Γ (zipp t1 π1) (zipp t2 π2) else True } :=

    _isconv_red Γ leq t1 π1 h1 t2 π2 h2 aux
    with inspect (reduce_stack nodelta_flags Σ Γ t1 π1 h1) := {
    | @exist (t1',π1') eq1
      with inspect (reduce_stack nodelta_flags Σ Γ t2 π2 h2) := {
      | @exist (t2',π2') eq2 => isconv_prog Γ leq t1' π1' t2' π2' aux
      }
    }.
  Next Obligation.
    eapply red_welltyped.
    - eapply h1.
    - do 2 zip fold. rewrite eq1.
      eapply reduce_stack_sound.
  Qed.
  Next Obligation.
    eapply red_welltyped.
    - eapply h2.
    - repeat zip fold. rewrite eq2.
      eapply reduce_stack_sound.
  Qed.
  Next Obligation.
    destruct (reduce_stack_Req nodelta_flags _ Γ t1 π1 h1) as [ e | h ].
    - rewrite e in eq1. inversion eq1. subst.
      right. right. simpl.
      constructor.
    - rewrite <- eq1 in h.
      dependent destruction h.
      + left. simpl. eapply cored_it_mkLambda_or_LetIn. assumption.
      + destruct y' as [q hq].
        cbn in H0. inversion H0. (* Why is noconf failing at this point? *)
        subst.
        unshelve eapply R_positionR.
        * simpl. unfold zipx. f_equal. symmetry. assumption.
        * simpl. unfold xposition. eapply positionR_poscat. assumption.
  Qed.
  Next Obligation.
    destruct b ; auto.
    destruct (reduce_stack_sound nodelta_flags _ _ _ _ h1).
    destruct (reduce_stack_sound nodelta_flags _ _ _ _ h2).
    (* Maybe we need to use Pr here.
       We could update it by discrimiating on App,
       saying everything not App stays the same
       (it might even not be necessary to discrimiate
       since we use decompose_stack).
     *)
    eapply conv_trans'.
    - eapply red_conv_l. eassumption.
    - eapply conv_trans'.
      + rewrite <- eq1. eassumption.
      + zip fold. rewrite eq2.
        eapply red_conv_r. assumption.
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

  (* If I do not manage to prove it, it's okay to enfore the stacks to be empty
     by matching.
   *)
  Lemma zip_Prod_Empty :
    forall {Γ na A B π},
      welltyped Σ Γ (zipc (tProd na A B) π) ->
      π = ε.
  Proof.
    intros Γ na A B π h.
    induction π.
    - reflexivity.
    - exfalso.
      cbn in h.
      zip fold in h.
      apply welltyped_context in h.
      destruct h as [T h]. cbn in h.
      destruct (inversion_App h) as [na' [A' [B' [[h1] [[?] [?]]]]]].
      destruct (inversion_Prod h1) as [s1 [s2 [[?] [[?] [bot]]]]].
      dependent destruction bot.
      + cbn in e. discriminate.
      + dependent destruction r.
        revert H.
        set (u := tFix mfix idx).
        assert (forall s, u <> tSort s) as neq by easy.
        clearbody u. revert u neq. clear.
        induction args ; intros u neq e.
        * destruct u ; try discriminate e.
          eapply neq. reflexivity.
        * simpl in e. eapply IHargs ; [ | eassumption ].
          intro. discriminate.
      +
  Admitted.

  Lemma context_conversion :
    forall {Γ t T Γ'},
      Σ ;;; Γ |- t : T ->
      PCUICSR.conv_context Σ Γ Γ' ->
      Σ ;;; Γ' |- t : T.
  Admitted.

  Equations unfold_one_fix (Γ : context) (mfix : mfixpoint term)
            (idx : nat) (π : stack) (h : welltyped Σ Γ (zipc (tFix mfix idx) π))
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
    rewrite zipc_appstack in h. cbn in h.
    zip fold in h. apply welltyped_context in h. cbn in h.
    destruct h as [T h].
    destruct (inversion_App h) as [na [A' [B' [[?] [[?] [?]]]]]].
    eexists. eassumption.
  Qed.

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

  Equations(noeqns) _isconv_prog (Γ : context) (leq : conv_pb)
            (t1 : term) (π1 : stack) (h1 : welltyped Σ Γ (zipc t1 π1))
            (t2 : term) (π2 : stack) (h2 : welltyped Σ Γ (zipc t2 π2))
            (aux : Aux (Term t2) Γ t1 π1 π2)
    : { b : bool | if b then conv leq Σ Γ (zipc t1 π1) (zipc t2 π2) else True } :=

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
    with isconv_red_raw Γ Conv A1 (Prod na B1 ε) A2 (Prod na' B2 ε) aux := {
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
    zip fold in h1. apply welltyped_context in h1. cbn in h1.
    destruct h1 as [T h1].
    destruct (inversion_Prod h1) as [s1 [s2 [[?] [[?] [?]]]]].
    eexists. eassumption.
  Qed.
  Next Obligation.
    zip fold in h2. apply welltyped_context in h2. cbn in h2.
    destruct h2 as [T h2].
    destruct (inversion_Prod h2) as [s1 [s2 [[?] [[?] [?]]]]].
    eexists. eassumption.
  Qed.
  Next Obligation.
    pose proof (zip_Prod_Empty h1). subst.
    pose proof (zip_Prod_Empty h2). subst.
    unshelve eapply R_positionR.
    - reflexivity.
    - simpl. unfold xposition. eapply positionR_poscat.
      simpl. constructor.
  Qed.
  Next Obligation.
    zip fold in h1. apply welltyped_context in h1. cbn in h1.
    destruct h1 as [T h1].
    destruct (inversion_Prod h1) as [s1 [s2 [[?] [[?] [?]]]]].
    eexists. eassumption.
  Qed.
  Next Obligation.
    (* PROBLEM AGAIN

       We conclude that the products are equal, meaning, we actually would
       compare the codomains on the stacks. This is problematic.

       This means that perhaps, having an extra Prod constructor to stacks
       wasn't the right fix to the previous problem.
     *)
    destruct h as [h].
    zip fold in h2. apply welltyped_context in h2. cbn in h2.
    destruct h2 as [T h2].
    destruct (inversion_Prod h2) as [s1 [s2 [[?] [[?] [?]]]]].
    zip fold in h1. apply welltyped_context in h1. cbn in h1.
    destruct h1 as [T' h1].
    destruct (inversion_Prod h1) as [s1' [s2' [[?] [[?] [?]]]]].
    eexists. eapply context_conversion ; try eassumption.
    econstructor.
    - eapply conv_context_refl ; try assumption.
      eapply typing_wf_local. eassumption.
    - constructor.
      + right. eexists. eassumption.
      + apply conv_sym. assumption.
  Qed.
  Next Obligation.
    pose proof (zip_Prod_Empty h1). subst.
    pose proof (zip_Prod_Empty h2). subst.
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