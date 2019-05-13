(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia
     Classes.RelationClasses Omega.
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

  Lemma red_zipx :
    forall Γ u v π,
      red Σ (Γ ,,, stack_context π) u v ->
      red Σ [] (zipx Γ u π) (zipx Γ v π).
  Proof.
    intros Γ u v π h.
    eapply red_it_mkLambda_or_LetIn.
    eapply red_context.
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

  Lemma cumul_it_mkLambda_or_LetIn :
    forall Δ Γ u v,
      Σ ;;; (Δ ,,, Γ) |- u <= v ->
      Σ ;;; Δ |- it_mkLambda_or_LetIn Γ u <= it_mkLambda_or_LetIn Γ v.
  Proof.
    intros Δ Γ u v h. revert Δ u v h.
    induction Γ as [| [na [b|] A] Γ ih ] ; intros Δ u v h.
    - assumption.
    - simpl. cbn. eapply ih.
      (* Need cumul for LetIn *)
      admit.
    - simpl. cbn. eapply ih.
      (* Need cumul for Lambda *)
      admit.
  Admitted.

  Lemma cumul_zippx :
    forall Γ u v ρ,
      Σ ;;; (Γ ,,, stack_context ρ) |- u <= v ->
      Σ ;;; Γ |- zippx u ρ <= zippx v ρ.
  Proof.
    intros Γ u v ρ h.
    revert u v h. induction ρ ; intros u v h.
    - cbn. assumption.
    - unfold zippx. simpl.
      case_eq (decompose_stack ρ). intros l π e.
      unfold zippx in IHρ. rewrite e in IHρ.
      apply IHρ.
      eapply cumul_App_l. assumption.
    - unfold zippx. simpl.
      eapply cumul_it_mkLambda_or_LetIn.
      assumption.
    - unfold zippx. simpl.
      eapply cumul_it_mkLambda_or_LetIn.
      assumption.
    - unfold zippx. simpl.
      eapply cumul_it_mkLambda_or_LetIn.
      assumption.
    - unfold zippx. simpl.
      eapply cumul_it_mkLambda_or_LetIn. cbn.
      (* Need cumul for Lambda again *)
      admit.
    - unfold zippx. simpl.
      eapply cumul_it_mkLambda_or_LetIn.
      assumption.
    - unfold zippx. simpl.
      eapply cumul_it_mkLambda_or_LetIn. cbn.
      (* cumul lambda *)
      admit.
  Admitted.

  Lemma conv_zippx :
    forall Γ u v ρ,
      Σ ;;; Γ ,,, stack_context ρ |- u = v ->
      Σ ;;; Γ |- zippx u ρ = zippx v ρ.
  Proof.
    intros Γ u v ρ [].
    constructor ; eapply cumul_zippx ; assumption.
  Qed.

  Lemma conv_zippx' :
    forall Γ leq u v ρ,
      conv leq Σ (Γ ,,, stack_context ρ) u v ->
      conv leq Σ Γ (zippx u ρ) (zippx v ρ).
  Proof.
    intros Γ leq u v ρ h.
    destruct leq.
    - cbn in *. destruct h as [[h1 h2]]. constructor.
      constructor ; eapply cumul_zippx ; assumption.
    - cbn in *. destruct h. constructor.
      eapply cumul_zippx. assumption.
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

  (* Notation wtp Γ t π := *)
  (*   (welltyped Σ Γ (zippx t π)) (only parsing). *)

  Notation wtp Γ t π :=
    (welltyped Σ [] (zipx Γ t π)) (only parsing).

  Definition wts Γ s t π :=
    match s with
    | Reduction t'
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
           | Reduction t | Term t => t
           | Args => tm
           end ;
    wth : welltyped Σ [] (zipx ctx tm' stk2)
  }.

  Definition dumbR (u v : pack) := False.

  (* Inductive lexprod_l {A B C} (leS : @sig A B -> sig B -> Prop) (leC : C -> C -> Prop) : sig B * C -> sig B * C -> Prop := *)
  (* | left_lex_l : *)
  (*     forall x x' y y', *)
  (*       leS x x' -> *)
  (*       lexprod_l leS leC (x,y) (x',y') *)
  (* | right_lex_l : *)
  (*     forall a b1 b2 c1 c2, *)
  (*       leC c1 c2 -> *)
  (*       lexprod_l leS leC (exist a b1, c1) (exist a b2, c2). *)

  (* Derive Signature for lexprod_l. *)

  (* Lemma acc_lexprod_l : *)
  (*   forall A B C leS leC, *)
  (*     well_founded leC -> *)
  (*     forall x, *)
  (*       Acc leS x -> *)
  (*       forall y, *)
  (*         Acc leC y -> *)
  (*         Acc (@lexprod_l A B C leS leC) (x,y). *)
  (* Proof. *)
  (*   intros A B C leS leC hw. *)
  (*   induction 1 as [[a b] h1 ih1]. *)
  (*   intro c. *)
  (*   induction 1 as [c h2 ih2]. *)
  (*   constructor. *)
  (*   intros [[a' b'] c'] h. simple inversion h. *)
  (*   - intro hx. inversion H0. inversion H1. subst. *)
  (*     eapply ih1. *)
  (*     + assumption. *)
  (*     + apply hw. *)
  (*   - intro hc. inversion H0. inversion H1. subst. *)
  (*     specialize (ih2 _ hc). *)
  (*     (* Mismatch, need b = b' *) *)
  (* Abort. *)

  Definition wterm Γ := { t : term | welltyped Σ Γ t }.

  Definition wcored Γ (u v : wterm Γ) :=
    cored Σ Γ (` u) (` v).

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
    t ⊩ cored Σ [] ⨱ @posR t × w ⊩ wcored [] ⨱ @posR (` w) × stateR.

  Notation pzt u := (zipx (ctx u) (tm u) (stk1 u)) (only parsing).
  Notation pps1 u := (xpos (ctx u) (tm u) (stk1 u)) (only parsing).
  Notation pwt u := (exist _ (wth u)) (only parsing).
  Notation pps2 u := (xpos (ctx u) (tm' u) (stk2 u)) (only parsing).

  Notation obpack u :=
    (pzt u ; (pps1 u, (pwt u ; (pps2 u, st u)))) (only parsing).

  Definition R (u v : pack) :=
    R_aux (obpack u) (obpack v).

  Lemma R_aux_Acc :
    forall t p w q s,
      welltyped Σ [] t ->
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

  Lemma wf_fun :
    forall A (R : A -> A -> Prop) B (f : B -> A),
      well_founded R ->
      well_founded (fun x y => R (f x) (f y)).
  Proof.
    intros A R B f h x.
    specialize (h (f x)).
    dependent induction h.
    constructor. intros y h.
    eapply H0 ; try reflexivity. assumption.
  Qed.

  Lemma Acc_fun :
    forall A (R : A -> A -> Prop) B (f : B -> A) x,
      Acc R (f x) ->
      Acc (fun x y => R (f x) (f y)) x.
  Proof.
    intros A R B f x h.
    dependent induction h.
    constructor. intros y h.
    eapply H0 ; try reflexivity. assumption.
  Qed.

  Lemma R_Acc :
    forall u,
      welltyped Σ [] (zipx (ctx u) (tm u) (stk1 u)) ->
      Acc R u.
  Proof.
    intros u h.
    eapply Acc_fun with (f := fun x => obpack x).
    apply R_aux_Acc. assumption.
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

  Lemma R_cored2 :
    forall t1 t2 (p1 : pos t1) (p2 : pos t2) w1 w2 q1 q2 s1 s2,
      t1 = t2 ->
      ` p1 = ` p2 ->
      cored Σ [] (` w1) (` w2) ->
      R_aux (t1 ; (p1, (w1 ; (q1, s1)))) (t2 ; (p2, (w2 ; (q2, s2)))).
  Proof.
    intros t1 t2 [p1 hp1] [p2 hp2] [t1' h1'] [t2' h2'] q1 q2 s1 s2 e1 e2 h.
    cbn in e2. cbn in h. subst.
    pose proof (uip hp1 hp2). subst.
    right. right. left. assumption.
  Qed.

  (* TODO Here we assume that welltyped is really squashed, which should be ok
     if we defined it in SProp probably.
   *)
  Axiom welltyped_irr :
    forall {Γ t} (h1 h2 : welltyped Σ Γ t), h1 = h2.

  Lemma R_positionR2 :
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

  Lemma R_stateR :
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

  Lemma zipx_welltyped :
    forall {Γ t π},
      welltyped Σ Γ (zipc t π) ->
      welltyped Σ [] (zipx Γ t π).
  Proof.
    intros Γ t π h.
    eapply it_mkLambda_or_LetIn_welltyped.
    rewrite app_context_nil_l.
    assumption.
  Qed.

  Lemma welltyped_zipx :
    forall {Γ t π},
      welltyped Σ [] (zipx Γ t π) ->
      welltyped Σ Γ (zipc t π).
  Proof.
    intros Γ t π h.
    apply welltyped_it_mkLambda_or_LetIn in h.
    rewrite app_context_nil_l in h.
    assumption.
  Qed.

  Lemma welltyped_zipc_zippx :
    forall Γ t π,
      welltyped Σ Γ (zipc t π) ->
      welltyped Σ Γ (zippx t π).
  Proof.
    intros Γ t π h.
    unfold zippx.
    case_eq (decompose_stack π). intros l ρ e.
    pose proof (decompose_stack_eq _ _ _ e). subst.
    eapply it_mkLambda_or_LetIn_welltyped.
    rewrite zipc_appstack in h. zip fold in h.
    apply welltyped_context in h. assumption.
  Qed.

  Lemma zwts :
    forall {Γ s t π},
      wts Γ s t π ->
      welltyped Σ [] (zipx Γ match s with Reduction u | Term u => u | Args => t end π).
  Proof.
    intros Γ s t π h.
    destruct s ; assumption.
  Defined.

  Definition Ret s Γ t π π' :=
    match s with
    | Reduction t' =>
      forall leq, { b : bool | if b then conv leq Σ Γ (zippx t π) (zippx t' π') else True }
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

  Notation isconv_red Γ leq t1 π1 t2 π2 aux :=
    (repack (isconv_red_raw Γ leq t1 π1 t2 π2 aux)) (only parsing).
  Notation isconv_prog Γ leq t1 π1 t2 π2 aux :=
    (repack (isconv_prog_raw Γ leq t1 π1 t2 π2 aux)) (only parsing).
  Notation isconv_args Γ t π1 π2 aux :=
    (repack (isconv_args_raw Γ t π1 π2 aux)) (only parsing).

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
    apply welltyped_zipc_zippx in h1.
    cbn. rewrite zipc_appstack. cbn.
    unfold zippx in h1. rewrite <- e1 in h1.
    apply welltyped_it_mkLambda_or_LetIn in h1.
    pose proof (decompose_stack_eq _ _ _ (eq_sym e1)). subst.
    rewrite stack_context_appstack. assumption.
  Qed.
  Next Obligation.
    clear aux eq1.
    apply welltyped_zipx in h2.
    apply welltyped_zipc_zippx in h2.
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
    eapply zipx_welltyped.
    rewrite zipc_appstack.

    rewrite stack_context_appstack in r1. cbn in r1.
    rewrite 2!zipc_appstack in r1. cbn in r1.

    eapply red_welltyped ; revgoals.
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
    eapply zipx_welltyped.
    rewrite zipc_appstack.

    rewrite stack_context_appstack in r2. cbn in r2.
    rewrite 2!zipc_appstack in r2. cbn in r2.

    eapply red_welltyped ; revgoals.
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
          -- simpl. eapply cored_it_mkLambda_or_LetIn.
             rewrite app_context_nil_l.
             rewrite zipc_appstack. rewrite zipc_stack_cat.
             repeat zip fold. eapply cored_context.
             assumption.
        * destruct y' as [q hq].
          cbn in H0. inversion H0. subst.
          unshelve eapply R_positionR2.
          -- simpl. rewrite stack_cat_appstack. reflexivity.
          -- simpl. rewrite stack_cat_appstack. reflexivity.
          -- simpl. unfold zipx. f_equal.
             rewrite zipc_stack_cat. rewrite <- H2.
             rewrite 2!zipc_appstack. cbn. reflexivity.
          -- simpl. unfold xposition. eapply positionR_poscat.
             unfold posR in H. cbn in H.
             rewrite stack_position_appstack in H. cbn in H.
             rewrite stack_position_stack_cat.
             rewrite stack_position_appstack.
             eapply positionR_poscat. assumption.
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

  Lemma cored_const :
    forall {Γ n c u cty cb cu},
      Some (ConstantDecl n {| cst_type := cty ; cst_body := Some cb ; cst_universes := cu |})
      = lookup_env Σ c ->
      cored (fst Σ) Γ (subst_instance_constr u cb) (tConst c u).
  Proof.
    intros Γ n c u cty cb cu e.
    symmetry in e.
    pose proof (lookup_env_const_name e). subst.
    econstructor.
    econstructor.
    - exact e.
    - reflexivity.
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

  Fixpoint isAppProd (t : term) : bool :=
    match t with
    | tApp t l => isAppProd t
    | tProd na A B => true
    | _ => false
    end.

  Fixpoint isProd t :=
    match t with
    | tProd na A B => true
    | _ => false
    end.

  Lemma isAppProd_isProd :
    forall Γ t,
      isAppProd t ->
      welltyped Σ Γ t ->
      isProd t.
  Proof.
    intros Γ t hp hw.
    revert Γ hp hw.
    induction t ; intros Γ hp hw.
    all: try discriminate hp.
    - reflexivity.
    - simpl in hp.
      specialize IHt1 with (1 := hp).
      assert (welltyped Σ Γ t1) as h.
      { destruct hw as [T h].
        destruct (inversion_App h) as [na [A' [B' [[?] [[?] [?]]]]]].
        eexists. eassumption.
      }
      specialize IHt1 with (1 := h).
      destruct t1.
      all: try discriminate IHt1.
      destruct hw as [T hw'].
      destruct (inversion_App hw') as [na [A' [B' [[hP] [[?] [?]]]]]].
      destruct (inversion_Prod hP) as [s1 [s2 [[?] [[?] [bot]]]]].
      (* dependent destruction bot. *)
      (* + discriminate e. *)
      (* + dependent destruction r. *)
      admit.
  Admitted.

  Lemma isAppProd_mkApps :
    forall t l, isAppProd (mkApps t l) = isAppProd t.
  Proof.
    intros t l. revert t.
    induction l ; intros t.
    - reflexivity.
    - cbn. rewrite IHl. reflexivity.
  Qed.

  Lemma isProdmkApps :
    forall t l,
      isProd (mkApps t l) ->
      l = [].
  Proof.
    intros t l h.
    revert t h.
    induction l ; intros t h.
    - reflexivity.
    - cbn in h. specialize IHl with (1 := h). subst.
      cbn in h. discriminate h.
  Qed.

  Lemma mkApps_Prod_nil :
    forall Γ na A B l,
      welltyped Σ Γ (mkApps (tProd na A B) l) ->
      l = [].
  Proof.
    intros Γ na A B l h.
    pose proof (isAppProd_isProd) as hh.
    specialize hh with (2 := h).
    rewrite isAppProd_mkApps in hh.
    specialize hh with (1 := eq_refl).
    apply isProdmkApps in hh. assumption.
  Qed.

  Lemma welltyped_rename :
    forall Γ u v,
      welltyped Σ Γ u ->
      eq_term (snd Σ) u v ->
      welltyped Σ Γ v.
  Admitted.

  Lemma eq_term_it_mkLambda_or_LetIn :
    forall Γ u v,
      eq_term (snd Σ) (it_mkLambda_or_LetIn Γ u) (it_mkLambda_or_LetIn Γ v) =
      eq_term (snd Σ) u v.
  Proof.
    intros Γ.
    induction Γ as [| [na [b|] A] Γ ih ] ; intros u v.
    - reflexivity.
    - simpl. cbn. rewrite ih. cbn.
      rewrite !eq_term_refl. reflexivity.
    - simpl. cbn. rewrite ih. cbn.
      rewrite !eq_term_refl. reflexivity.
  Qed.

  Lemma eq_term_zipc :
    forall u v π,
      eq_term (snd Σ) (zipc u π) (zipc v π) = eq_term (snd Σ) u v.
  Proof.
    intros u v π.
    revert u v. induction π ; intros u v.
    all: try solve [
      simpl ; rewrite ?IHπ ; cbn ;
      rewrite ?eq_term_refl, ?andb_true_r ;
      reflexivity
    ].
    simpl. rewrite IHπ. cbn.
    destruct indn.
    assert (forallb2 (fun '(_, b) '(_, b') => eq_term (snd Σ) b b') brs brs) as e.
    { clear. induction brs.
      - reflexivity.
      - cbn. rewrite IHbrs. destruct a.
        rewrite eq_term_refl. reflexivity.
    } rewrite e.
    rewrite ?eq_term_refl, ?andb_true_r, ?eq_ind_refl, ?eq_nat_refl.
    reflexivity.
  Qed.

  Lemma eq_term_zipx :
    forall Γ u v π,
      eq_term (snd Σ) (zipx Γ u π) (zipx Γ v π) =
      eq_term (snd Σ) u v.
  Proof.
    intros Γ u v π.
    unfold zipx. rewrite eq_term_it_mkLambda_or_LetIn.
    apply eq_term_zipc.
  Qed.

  Equations(noeqns) _isconv_prog (Γ : context) (leq : conv_pb)
            (t1 : term) (π1 : stack) (h1 : wtp Γ t1 π1)
            (t2 : term) (π2 : stack) (h2 : wtp Γ t2 π2)
            (ir1 : isred (t1, π1)) (ir2 : isred (t2, π2))
            (aux : Aux (Term t2) Γ t1 π1 π2 h2)
    : { b : bool | if b then conv leq Σ Γ (zippx t1 π1) (zippx t2 π2) else True } :=

    _isconv_prog Γ leq (tApp _ _) π1 h1 (tApp _ _) π2 h2 ir1 ir2 aux :=
      False_rect _ _ ;

    _isconv_prog Γ leq (tConst c u) π1 h1 (tConst c' u') π2 h2 ir1 ir2 aux
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
    _isconv_prog Γ leq (tLambda na A1 t1) π1 h1 (tLambda na' A2 t2) π2 h2 ir1 ir2 aux
    with isconv_red_raw Γ Conv A1 (Lambda_ty na t1 π1) A2 (Lambda_ty na' t2 π2) aux := {
    | @exist true h :=
      isconv_red Γ leq
                 t1 (Lambda_tm na A1 π1)
                 t2 (Lambda_tm na' A2 π2) aux ;
    | @exist false _ := no
    } ;

    _isconv_prog Γ leq (tProd na A1 B1) π1 h1 (tProd na' A2 B2) π2 h2 ir1 ir2 aux
    with isconv_red_raw Γ Conv A1 (Prod_l na B1 π1) A2 (Prod_l na' B2 π2) aux := {
    | @exist true h :=
      isconv_red Γ leq
                 B1 (Prod_r na A1 π1)
                 B2 (Prod_r na' A2 π2) aux ;
    | @exist false _ := no
    } ;

    (* Hnf did not reduce, maybe delta needed in c *)
    _isconv_prog Γ leq (tCase (ind, par) p c brs) π1 h1
                       (tCase (ind',par') p' c' brs') π2 h2
                       ir1 ir2 aux
    with inspect (eq_term (snd Σ) p p' && eq_term (snd Σ) c c'
        && forallb2 (fun '(a, b) '(a', b') => eq_term (snd Σ) b b') brs brs') := {
    | @exist true eq1 := isconv_args Γ (tCase (ind, par) p c brs) π1 π2 aux ;
    | @exist false _ with inspect (reduce_term RedFlags.default Σ (Γ ,,, stack_context π1) c _) := {
      | @exist cred eq1 with inspect (reduce_term RedFlags.default Σ (Γ ,,, stack_context π2) c' _) := {
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

    _isconv_prog Γ leq (tProj p c) π1 h1 (tProj p' c') π2 h2 ir1 ir2 aux
    with inspect (eq_projection p p' && eq_term (snd Σ) c c') := {
    | @exist true eq1 := isconv_args Γ (tProj p c) π1 π2 aux ;
    | @exist false _ := no
    } ;

    (* Subtle difference here with Checker, if the terms are syntactically equal
       but the stacks are not convertible, then we say no. *)
    _isconv_prog Γ leq (tFix mfix idx) π1 h1 (tFix mfix' idx') π2 h2 ir1 ir2 aux
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

    _isconv_prog Γ leq (tCoFix mfix idx) π1 h1 (tCoFix mfix' idx') π2 h2 ir1 ir2 aux
    with inspect (eq_term (snd Σ) (tCoFix mfix idx) (tCoFix mfix' idx')) := {
    | @exist true eq1 := isconv_args Γ (tCoFix mfix idx) π1 π2 aux ;
    | @exist false _ := no
    } ;

    (* TODO Fallback *)
    _isconv_prog Γ leq t1 π1 h1 t2 π2 h2 ir1 ir2 aux := no.

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
    apply welltyped_zipc_zippx in h1.
    unfold zippx in h1. rewrite decompose_stack_appstack in h1.
    rewrite decompose_stack_twice with (1 := e1) in h1.
    simpl in h1. rewrite app_nil_r in h1.
    apply welltyped_it_mkLambda_or_LetIn in h1.
    apply mkApps_Prod_nil in h1. subst.

    clear aux.
    apply welltyped_zipx in h2.
    apply welltyped_zipc_zippx in h2.
    unfold zippx in h2. rewrite decompose_stack_appstack in h2.
    rewrite decompose_stack_twice with (1 := e2) in h2.
    simpl in h2. rewrite app_nil_r in h2.
    apply welltyped_it_mkLambda_or_LetIn in h2.
    apply mkApps_Prod_nil in h2. subst.

    cbn.

    (* Not very clear how to conclude yet...
       It seems true enough though.
       We must go on to this if the conclusion assumption is too strong.
     *)
    (* eapply conv_Prod ; eassumption. *)
  (* Qed. *)
  Admitted.

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
    eapply red_welltyped.
    - exact h1.
    - constructor. eapply red_zipx. eapply red_const. eassumption.
  Qed.
  Next Obligation.
    eapply red_welltyped.
    - exact h2.
    - constructor. eapply red_zipx. eapply red_const. eassumption.
  Qed.
  Next Obligation.
    left. simpl.
    eapply cored_zipx. eapply cored_const. eassumption.
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
    eapply red_welltyped ; [ exact h2 | ].
    constructor. eapply red_zipx. eapply red_const. eassumption.
  Qed.
  Next Obligation.
    unshelve eapply R_cored2.
    all: try reflexivity.
    simpl. eapply cored_zipx. eapply cored_const. eassumption.
  Qed.
  Next Obligation.
    destruct b0 ; auto.
    eapply conv_trans' ; try eassumption.
    eapply red_conv_r.
    eapply red_zippx. eapply red_const. eassumption.
  Qed.
  Next Obligation.
    eapply red_welltyped ; [ exact h1 | ].
    constructor. eapply red_zipx. eapply red_const. eassumption.
  Qed.
  Next Obligation.
    left. simpl. eapply cored_zipx. eapply cored_const. eassumption.
  Qed.
  Next Obligation.
    destruct b0 ; auto.
    eapply conv_trans' ; try eassumption.
    eapply red_conv_l.
    eapply red_zippx. eapply red_const. eassumption.
  Qed.
  Next Obligation.
    eapply red_welltyped ; [ exact h1 | ].
    constructor. eapply red_zipx. eapply red_const. eassumption.
  Qed.
  Next Obligation.
    left. simpl. eapply cored_zipx. eapply cored_const. eassumption.
  Qed.
  Next Obligation.
    destruct b0 ; auto.
    eapply conv_trans' ; try eassumption.
    eapply red_conv_l.
    eapply red_zippx. eapply red_const. eassumption.
  Qed.
  Next Obligation.
    eapply red_welltyped ; [ exact h1 | ].
    constructor. eapply red_zipx. eapply red_const. eassumption.
  Qed.
  Next Obligation.
    left. simpl. eapply cored_zipx. eapply cored_const. eassumption.
  Qed.
  Next Obligation.
    destruct b0 ; auto.
    eapply conv_trans' ; try eassumption.
    eapply red_conv_l.
    eapply red_zippx. eapply red_const. eassumption.
  Qed.

  (* tCase *)
  Next Obligation.
    symmetry in eq1.
    apply andP in eq1 as [eq1 ebrs].
    apply andP in eq1 as [ep ec].
    (* How do we know ind = ind' and par = par'? *)
    (* One solution: just ask! *)
    (* Anyway we would need to show welltypedness survises renaming *)
  Admitted.
  Next Obligation.
    unshelve eapply R_stateR.
    all: try reflexivity.
    - simpl. (* We need the same as above *)
      admit.
    - simpl. constructor.
  Admitted.
  Next Obligation.
    destruct b ; auto.
    eapply conv_conv.
    destruct h. constructor.
    eapply conv_trans ; try eassumption.
    eapply conv_zippx.
    eapply eq_term_conv.
    (* Missing ind = ind' again. *)
  Admitted.
  Next Obligation.
    apply welltyped_zipx in h1.
    zip fold in h1. apply welltyped_context in h1. simpl in h1.
    destruct h1 as [T h1].
    destruct (weak_inversion_Case h1) as [args [u [?]]].
    eexists. eassumption.
  Qed.
  Next Obligation.
    clear aux.
    apply welltyped_zipx in h2.
    zip fold in h2. apply welltyped_context in h2. simpl in h2.
    destruct h2 as [T h2].
    destruct (weak_inversion_Case h2) as [args [u [?]]].
    eexists. eassumption.
  Qed.
  Next Obligation.
    eapply red_welltyped.
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
    eapply red_welltyped.
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
        cbn in eq3.
        rewrite 2!eq_term_refl in eq3. discriminate eq3.
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
          cbn in eq3.
          rewrite 2!eq_term_refl in eq3. discriminate eq3.
    - dependent destruction hr.
      + left. simpl.
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
          cbn in eq3.
          rewrite 2!eq_term_refl in eq3. discriminate eq3.
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
             cbn in eq3.
             rewrite 2!eq_term_refl in eq3. discriminate eq3.
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
    eapply welltyped_rename.
    - exact h2.
    - apply eq_term_sym.
      cbn. rewrite eq_term_zipx. cbn.
      rewrite <- eq1. reflexivity.
  Qed.
  Next Obligation.
    unshelve eapply R_stateR.
    all: try reflexivity.
    - simpl.
      (* NEW PROBLEM.
         We have only eq_term, no equality.
         Damn names!
       *)
      admit.
    - simpl. constructor.
  Admitted.
  Next Obligation.
    destruct b ; auto.
    eapply conv_conv.
    destruct h. constructor.
    eapply conv_trans ; try eassumption.
    eapply conv_zippx.
    eapply eq_term_conv.
    symmetry. assumption.
  Qed.

  (* tFix *)
  Next Obligation.
    eapply welltyped_rename.
    - exact h2.
    - apply eq_term_sym. rewrite eq_term_zipx. cbn. rewrite <- eq1. reflexivity.
  Qed.
  Next Obligation.
    unshelve eapply R_stateR.
    all: try reflexivity.
    - simpl.
      (* NEW PROBLEM.
         We have only eq_term, no equality.
         Damn names!
       *)
      admit.
    - simpl. constructor.
  Admitted.
  Next Obligation.
    destruct b ; auto.
    destruct h as [h].
    eapply conv_conv.
    constructor.
    eapply conv_trans ; try eassumption.
    eapply conv_zippx.
    eapply eq_term_conv.
    symmetry. assumption.
  Qed.
  Next Obligation.
    apply welltyped_zipx in h1.
    apply welltyped_zipc_zippx in h1.
    assumption.
  Qed.
  Next Obligation.
    (* Need appropriate lemma on unfold_one_fix. *)
  Admitted.
  Next Obligation.
    (* Need appropriate lemma on unfold_one_fix. *)
  Admitted.
  Next Obligation.
    (* Need appropriate lemma on unfold_one_fix. *)
  Admitted.
  Next Obligation.
    rewrite eq2.
    eapply reduce_stack_isred.
    auto.
  Qed.
  Next Obligation.
    destruct b ; auto.
    (* Need appropriate lemma on unfold_one_fix. *)
  Admitted.
  Next Obligation.
    clear aux.
    apply welltyped_zipx in h2.
    apply welltyped_zipc_zippx in h2.
    assumption.
  Qed.
  Next Obligation.
    (* Need lemma on unfold_one_fix *)
  Admitted.
  Next Obligation.
    (* Need lemma on unfold_one_fix *)
  Admitted.
  Next Obligation.
    (* Need lemma on unfold_one_fix *)
  Admitted.
  Next Obligation.
    rewrite eq2.
    eapply reduce_stack_isred.
    auto.
  Qed.
  Next Obligation.
    destruct b ; auto.
    (* Need appropriate lemma on unfold_one_fix. *)
  Admitted.

  (* tCoFix *)
  Next Obligation.
    eapply welltyped_rename.
    - exact h2.
    - apply eq_term_sym. rewrite eq_term_zipx. cbn. rewrite <- eq1. reflexivity.
  Qed.
  Next Obligation.
    unshelve eapply R_stateR.
    all: try reflexivity.
    - simpl.
      (* BIG PROBLEM again where we only have eq_term *)
      give_up.
    - simpl. constructor.
  Admitted.
  Next Obligation.
    destruct b ; auto.
    eapply conv_conv.
    destruct h. constructor.
    eapply conv_trans ; try eassumption.
    eapply conv_zippx.
    eapply eq_term_conv.
    symmetry. assumption.
  Qed.

  (* View on stack App *)
  (* Equations discr_App (π : stack) : Prop := *)
  (*   discr_App (App u ρ) := False ; *)
  (*   discr_App _ := True. *)

  (* Inductive stack_App_view_t : stack -> Set := *)
  (* | stack_App u ρ : stack_App_view_t (App u ρ) *)
  (* | stack_other π : discr_App π -> stack_App_view_t π. *)

  (* Equations stack_App_view π : stack_App_view_t π := *)
  (*   stack_App_view (App u ρ) := stack_App u ρ ; *)
  (*   stack_App_view π := stack_other π I. *)

  (* ERROR Cannot guess decreasing argument of fix *)
  (* Equations stack_args Γ (t : term) (π1 π2 : stack) (h2 : wtp Γ t π2) *)
  (*   : list (term * stack * { x : term * stack | wtp Γ (fst x) (snd x) }) := *)
  (*   stack_args Γ t π1 π2 h2 with stack_App_view π1 := { *)
  (*   | stack_App u1 ρ1 with stack_App_view π2 := { *)
  (*     | stack_App u2 ρ2 := *)
  (*       (u1, coApp t ρ1, exist (u2, coApp t ρ2) h2) *)
  (*       :: stack_args Γ (tApp t u2) ρ1 ρ2 h2 ; *)
  (*     | _ := [] *)
  (*     } ; *)
  (*   | _ := [] *)
  (*   }. *)

(*
  Equations stack_args Γ (t : term) (π1 π2 : stack) (h2 : wtp Γ t π2)
    : list (term * stack * { x : term * stack | wtp Γ (fst x) (snd x) }) :=
    stack_args Γ t (App u1 ρ1) (App u2 ρ2) h2 :=
      (u1, coApp t ρ1, exist (u2, coApp t ρ2) h2)
      :: stack_args Γ (tApp t u2) ρ1 ρ2 h2 ;
    stack_args Γ t π1 π2 h2 := [].

  Lemma stack_args_noApp :
    forall Γ t θ1 θ2 h,
      isStackApp θ1 = false ->
      stack_args Γ t θ1 θ2 h = [].
  Proof.
    intros Γ t θ1 θ2 h n1.
    funelim (stack_args Γ t θ1 θ2 h).
    all: try reflexivity.
    cbn in n1. discriminate.
  Qed.

  (* Lemma stack_args_R_aux : *)
  (*   forall Γ t l1 θ1 l2 θ2 n h2 h2', *)
  (*     isStackApp θ1 = false -> *)
  (*     isStackApp θ2 = false -> *)
  (*     #|l1| = #|l2| -> *)
  (*     Forall (fun '(u1, ρ1, exist (u2, ρ2) h) => *)
  (*       R (mkpack (Reduction u2) Γ u1 ρ1 ρ2 h) *)
  (*         (mkpack Args Γ t (appstack l1 θ1) (appstack l2 θ2) h2) *)
  (*     ) (stack_args Γ (mkApps t (firstn n l2)) *)
  (*                   (appstack (skipn n l1) θ1) (appstack (skipn n l2) θ2) h2'). *)
  (* Proof. *)
  (*   simpl. intros Γ t l1 θ1 l2 θ2 n h2 h2' n1 n2 e. *)
  (*   revert Γ t l1 θ1 l2 θ2 h2 h2' n1 n2 e. *)
  (*   induction n ; intros Γ t l1 θ1 l2 θ2 h2 h2' n1 n2 e. *)
  (*   - admit. *)
  (*   - destruct (Nat.leb_spec0 #|l1| (S n)). *)
  (*     + revert h2'. *)
  (*       erewrite !firstn_all2 by omega. *)
  (*       erewrite !skipn_all2 by omega. *)
  (*       intros h2'. *)
  (*       cbn. rewrite stack_args_noApp by assumption. *)
  (*       constructor. *)
  (*     + destruct l1 as [|u1 l1], l2 as [|u2 l2] ; try discriminate. *)
  (*       * cbn in *. exfalso. omega. *)
  (*       * cbn in n0. simpl. *)
  (*         specialize (IHn Γ t (u1 :: l1) θ1 (u2 :: l2) θ2 h2). *)
  (*         specialize IHn with (1 := n1) (2 := n2) (3 := e). *)
  (*         simpl in IHn. *)
  (*         eapply IHn. *)

  (* Lemma strong_nat_rev_ind (max : nat) : *)
  (*   forall (P : nat -> Prop), *)
  (*     (forall n, n >= max -> P n) -> *)
  (*     (forall n, (forall m, n < m -> m < max -> P m) -> P n) -> *)
  (*     forall n, P n. *)
  (* Proof. *)
  (*   intros P hmax hS. *)
  (*   assert (h : forall n, P (max - n)). *)
  (*   { intros n. induction n using strong_nat_ind. *)
  (*     destruct (Nat.ltb_spec0 max n). *)
  (*     - replace (max - n) with 0 by omega. *)
  (*       specialize (H max l). *)
  (*       replace (max - max) with 0 in H by omega. *)
  (*       assumption. *)
  (*     - destruct (Nat.eqb_spec n max). *)
  (*       + subst. admit. *)
  (*       + assert (n < max) by omega. *)

  (*     - apply hmax. omega. *)
  (*     - destruct (Nat.leb_spec0 max n). *)
  (*       + replace (max - S n) with 0 by omega. *)
  (*         replace (max - n) with 0 in IHn by omega. *)
  (*         assumption. *)
  (*       + eapply hS. *)
  (*         * omega. *)
  (*         * intros m h. *)
  (*           assert (max < S n + m) by omega. *)


 (* ; try eassumption ; omega. *)
 (*    } *)
 (*    intro n. *)
 (*    destruct (Nat.leb_spec0 max n). *)
 (*    - apply hmax. omega. *)
 (*    - replace n with (max - (max - n)) by omega. apply h. *)
 (*  Qed. *)

  Lemma stack_args_R_aux :
    forall Γ t l1 θ1 l2 θ2 n h2 h2',
      isStackApp θ1 = false ->
      isStackApp θ2 = false ->
      #|l1| = #|l2| ->
      Forall (fun '(u1, ρ1, exist (u2, ρ2) h) =>
        R (mkpack (Reduction u2) Γ u1 ρ1 ρ2 h)
          (mkpack Args Γ t (appstack l1 θ1) (appstack l2 θ2) h2)
      ) (stack_args Γ (mkApps t (firstn n l2))
                    (appstack (skipn n l1) θ1) (appstack (skipn n l2) θ2) h2').
  Proof.
    simpl. intros Γ t l1 θ1 l2 θ2 n h2 h2' n1 n2 e.
    pose (m := #|l1|).
    assert (eq : m = #|l1|) by reflexivity.
    clearbody m.
    revert Γ t l1 θ1 l2 θ2 h2 h2' n1 n2 e eq.
    induction n using (nat_rev_ind m) ;
    intros Γ t l1 θ1 l2 θ2 h2 h2' hn1 hn2 e eq.
    - subst. revert h2'.
      erewrite !firstn_all2 by omega.
      erewrite !skipn_all2 by omega.
      cbn. intros h2'.
      rewrite stack_args_noApp by assumption. constructor.
    - subst. specialize (IHn Γ t l1 θ1 l2 θ2 h2).
      specialize IHn with (1 := hn1) (2 := hn2) (3 := e) (4 := eq_refl).
      destruct l1 as [|u1 l1], l2 as [|u2 l2] ; try discriminate.
      + cbn in H. exfalso. omega.
      + cbn in IHn. destruct n.
        * cbn. cbn in IHn. simp stack_args.
          econstructor.
          -- unshelve eapply R_positionR ; try reflexivity.
             simpl. unfold xposition. eapply positionR_poscat.
             cbn. eapply positionR_poscat. constructor.
          -- eapply IHn.
        * simpl.
  Admitted.

  Lemma stack_args_R :
    forall Γ t π1 π2 h2,
      Forall (fun '(u1, ρ1, exist (u2, ρ2) h) =>
        R (mkpack (Reduction u2) Γ u1 ρ1 ρ2 h)
          (mkpack Args Γ t π1 π2 h2)
      ) (stack_args Γ t π1 π2 h2).
  Proof.
    simpl. intros Γ t π1 π2 h2.
    case_eq (decompose_stack π1). intros l1 θ1 e1.
    case_eq (decompose_stack π2). intros l2 θ2 e2.
    pose proof (decompose_stack_eq _ _ _ e1).
    pose proof (decompose_stack_eq _ _ _ e2).
    subst.
    destruct (eqb_spec #|l1| #|l2|).
    - eapply stack_args_R_aux with (n := 0).
      + destruct θ1 ; try reflexivity. exfalso.
        eapply decompose_stack_not_app. eassumption.
      + destruct θ2 ; try reflexivity. exfalso.
        eapply decompose_stack_not_app. eassumption.
      + assumption.
    - (* Unfortunately, having different lengths is not enough to return
         the empty list, maybe we should synchronise things more...
       *)
  Abort.

  Lemma stack_args_R :
    forall Γ t π1 π2 h2,
      Forall (fun '(u1, ρ1, exist (u2, ρ2) h) =>
        R (mkpack (Reduction u2) Γ u1 ρ1 ρ2 h)
          (mkpack Args Γ t π1 π2 h2)
      ) (stack_args Γ t π1 π2 h2).
  Proof.
    simpl. intros Γ t π1 π2 h2.
    assert (h :
      Forall (fun '(u1, ρ1, exist (u2, ρ2) h) =>
        let x := mkpack (Reduction u2) Γ u1 ρ1 ρ2 h in
        let y := mkpack Args Γ t π1 π2 h2 in
        pzt x = pzt y /\
        positionR (` (pps1 x)) (` (pps1 y))
      ) (stack_args Γ t π1 π2 h2)
    ).
    { funelim (stack_args Γ t π1 π2 h2).
      all: try solve [ constructor ].
      econstructor.
      - split ; [ reflexivity |].
        simpl. unfold xposition. eapply positionR_poscat.
        cbn. eapply positionR_poscat. constructor.
      - eapply Forall_impl.
        + eapply H.
        + clear H. intros [[u1 ρ1] [[u2 ρ2] h2']] h.
          simpl. simpl in h.
fofo

    funelim (stack_args Γ t π1 π2 h2).
    all: try solve [ constructor ].
    econstructor.
    - unshelve eapply R_positionR ; try reflexivity.
      simpl. unfold xposition. eapply positionR_poscat.
      cbn. eapply positionR_poscat. constructor.
    - eapply Forall_impl.
      + eapply H.
      + clear. intros [[u1 ρ1] [[u2 ρ2] h2']] h.


  Lemma stack_args_R_aux :
    forall Γ t l1 θ1 l2 θ2 m h2 h2',
      isStackApp θ1 = false ->
      isStackApp θ2 = false ->
      #|l1| = #|l2| ->
      let n := #|l1| - m in
      Forall (fun '(u1, ρ1, exist (u2, ρ2) h) =>
        R (mkpack (Reduction u2) Γ u1 ρ1 ρ2 h)
          (mkpack Args Γ t (appstack l1 θ1) (appstack l2 θ2) h2)
      ) (stack_args Γ (mkApps t (firstn n l2))
                    (appstack (skipn n l1) θ1) (appstack (skipn n l2) θ2) h2').
  Proof.
    simpl. intros Γ t l1 θ1 l2 θ2 m h2 h2' n1 n2 e.
    revert Γ t l1 θ1 l2 θ2 h2 h2' n1 n2 e.
    induction m ; intros Γ t l1 θ1 l2 θ2 h2 h2' n1 n2 e.
    - revert h2'.
      erewrite !firstn_all2 by omega.
      erewrite !skipn_all2 by omega.
      cbn. intros h2'.
      rewrite stack_args_noApp by assumption.
      constructor.
    - destruct (Nat.ltb_spec0 #|l1| (S m)).
      + revert h2'.
        replace (#|l1| - S m) with 0 by omega.
        cbn. unfold skipn.
        intros h2'.
        destruct l1, l2 ; try discriminate e.
        * cbn. rewrite stack_args_noApp by assumption. constructor.
        * cbn.
          specialize (IHm Γ t (t0 :: l1) θ1 (t1 :: l2) θ2 h2).
          specialize IHm with (1 := n1) (2 := n2).
          cbn in l.
          assert (h : S #|l1| - m = 0) by omega.
          assert (h' : #|t0 :: l1| - m = 0) by auto with arith.
          rewrite h' in IHm.
          cbn in IHm. unfold skipn in IHm. cbn in IHm.
          eapply IHm. easy.
      + destruct l1, l2 ; try discriminate e.
        * exfalso. cbn in n. omega.
        * simpl.
          destruct (Nat.eqb_spec #|l1| m).
          -- subst. revert h2'. simpl.
             replace (#|l1| - #|l1|) with 0 by omega.
             simpl.
             intros h2'.
             specialize (IHm Γ t (t0 :: l1) θ1 (t1 :: l2) θ2 h2).
             specialize IHm with (1 := n1) (2 := n2) (3 := e).
             replace (#|t0 :: l1| - #|l1|) with 1 in IHm
             by (change (1 = S #|l1| - #|l1|) ; omega).
             cbn in IHm. unfold skipn in IHm.
             simp stack_args. econstructor.
             ++ unshelve eapply R_positionR ; try reflexivity.
                simpl. unfold xposition. eapply positionR_poscat.
                cbn. eapply positionR_poscat. constructor.
             ++ eapply IHm.
          -- cbn in n.
             revert h2'. simpl.
             replace (#|l1| - m) with (S (#|l1| - S m)) by omega.
             simpl.
             change (skipn (S (#|l1| - S m)) (t0 :: l1))
               with (skipn (#|l1| - S m) l1).
             change (skipn (S (#|l1| - S m)) (t1 :: l2))
               with (skipn (#|l1| - S m) l2).
             intros h2'.
             change (#|t0 :: l1| - m) with (S #|l1| - m) in IHm.
             replace (S #|l1| - m) with (S (#|l1| - m)) in IHm by omega.
             simpl in IHm.
             change (skipn (S (#|l1| - m)) (t1 :: l2))
               with (skipn (#|l1| - m) l2) in IHm.
             change (skipn (S (#|l1| - m)) (t0 :: l1))
               with (skipn (#|l1| - m) l1) in IHm.



             change (firstn (S #|l1| - m) (t1 :: l2))
               with (firstn (#|l1| - m) l2) in IHm.

assert (#|l1| - m = S (#|l1| - S m)).
             { cbn in n. omega. }


 by (cbn ; omega).


             simp stack_args in IHm.


simp stack_args. econstructor.
          -- unshelve eapply R_positionR.
             ++ simpl. reflexivity.
             ++ simpl. unfold xposition. eapply positionR_poscat.
                cbn. eapply positionR_poscat. constructor.
          -- specialize (IHm Γ t (t0 :: l1) θ1 (t1 :: l2) θ2 h2).
             specialize IHm with (1 := n1) (2 := n2).
             cbn in l.
             assert (h : S #|l1| - m = 0) by omega.
             assert (h' : #|t0 :: l1| - m = 0) by auto with arith.
             rewrite h' in IHm.
             cbn in IHm. unfold skipn in IHm. cbn in IHm.
             simp stack_args in IHm.

             eapply IHm.

             replace (#|t0 :: l1| - m) with 0 in IHm by (cbn ; omega).
             eapply IHm.

  Lemma stack_args_R_aux :
    forall Γ t l1 θ1 l2 θ2 n h2 h2',
      Forall (fun '(u1, ρ1, exist (u2, ρ2) h) =>
        R (mkpack (Reduction u2) Γ u1 ρ1 ρ2 h)
          (mkpack Args Γ t (appstack l1 θ1) (appstack l2 θ2) h2)
      ) (stack_args Γ (mkApps t (firstn n l1))
                    (appstack (skipn n l1) θ1) (appstack (skipn n l2) θ2) h2').
  Proof.
    simpl. intros Γ t l1 θ1 l2 θ2 n h2 h2'.
    revert Γ t l1 θ1 l2 θ2 h2 h2'.
    induction n ; intros Γ t l1 θ1 l2 θ2 h2 h2'.
    - cbn. unfold skipn. cbn in h2'. unfold skipn in h2'.


  Lemma stack_args_R :
    forall Γ t π1 π2 h2,
      Forall (fun '(u1, ρ1, exist (u2, ρ2) h) =>
        R (mkpack (Reduction u2) Γ u1 ρ1 ρ2 h)
          (mkpack Args Γ t π1 π2 h2)
      ) (stack_args Γ t π1 π2 h2).
  Proof.
    simpl. intros Γ t π1 π2 h2.
    case_eq (decompose_stack π1). intros l1 θ1 e1.
    case_eq (decompose_stack π2). intros l2 θ2 e2.
    pose proof (decompose_stack_eq _ _ _ e1).
    pose proof (decompose_stack_eq _ _ _ e2).
    subst.
    (* Maybe generalise this with firstn/skipn and do it by induction on n?
       This way we can have the whole term in R and the n/firstn/skipn in the
       argument to stack_args.
     *)


(*     funelim (stack_args Γ t π1 π2 h2). *)
(*     all: try solve [ constructor ]. *)
(*     econstructor. *)
(*     - unshelve eapply R_positionR. *)
(*       + simpl. reflexivity. *)
(*       + simpl. unfold xposition. eapply positionR_poscat. *)
(*         cbn. eapply positionR_poscat. constructor. *)
(*     - *)

(* specialize (H Γ t2 (args ++ [t1]) π π0). *)
(*       assert (h2' : welltyped Σ [] (zipx Γ (mkApps t2 (args ++ [t1])) π0)). *)
(*       { rewrite <- mkApps_nested. assumption. } *)
(*       specialize (H h2'). *)
(*       revert h2' H. rewrite <- mkApps_nested. intros h2' H. *)
(*       assert (h2' = h2) by (apply welltyped_irr). subst. *)
(*       specialize (H eq_refl). cbn in H. *)



      (* apply H. *)


  (*     match goal with *)
(*       | |- context [ Forall ?Q _ ] => set (P := Q) in * *)
(*       end. *)


(*       eapply H. *)
(*       specialize H with (t := t2) (args0 := args ++ [t1]). *)


(* revert h2 H. *)
(*       replace (tApp (mkApps t2 args) t1) with (mkApps t2 (args ++ [t1])) *)
(*       by (rewrite <- mkApps_nested ; reflexivity). *)
(*       specialize (H Γ _) *)
  Abort.



  Lemma foo :
    forall Γ t π1 π2 h2,
      Forall (fun '(u1, ρ1, exist (u2, ρ2) h) =>
        R (mkpack (Reduction u2) Γ u1 ρ1 ρ2 h)
          (mkpack Args Γ t π1 π2 h2)
      ) (stack_args Γ t π1 π2 h2).
  Proof.
    simpl. intros Γ t π1 π2 h2.
    funelim (stack_args Γ t π1 π2 h2).
    all: try solve [ constructor ].
    match goal with
    | |- context [ Forall ?Q _ ] => set (P := Q) in *
    end.

    econstructor.
    - unshelve eapply R_positionR.
      + simpl. reflexivity.
      + simpl. unfold xposition. eapply positionR_poscat.
        cbn. eapply positionR_poscat. constructor.
    -


  Abort.
*)

  Definition Aux' Γ t π1 π2 h2 :=
     forall u1 u2 ρ1 ρ2
       (h1' : wtp Γ u1 ρ1)
       (h2' : wtp Γ u2 ρ2),
       let x := mkpack (Reduction u2) Γ u1 ρ1 ρ2 h2' in
       let y := mkpack Args Γ t π1 π2 h2 in
       pzt x = pzt y /\
       positionR (` (pps1 x)) (` (pps1 y)) ->
       Ret (Reduction u2) Γ u1 ρ1 ρ2.

  Lemma positionR_context_position_inv :
    forall Γ p q,
      positionR (context_position Γ ++ p) (context_position Γ ++ q) ->
      positionR p q.
  Proof.
    intros Γ p q h.
    revert p q h.
    induction Γ as [| [na [b|] A] Γ ih ] ; intros p q h.
    - assumption.
    - cbn in h. rewrite <- 2!app_assoc in h. apply ih in h.
      cbn in h. dependent destruction h.
      assumption.
    - cbn in h. rewrite <- 2!app_assoc in h. apply ih in h.
      cbn in h. dependent destruction h.
      assumption.
  Qed.

  Lemma positionR_xposition_inv :
    forall Γ ρ1 ρ2,
      positionR (xposition Γ ρ1) (xposition Γ ρ2) ->
      positionR (stack_position ρ1) (stack_position ρ2).
  Proof.
    intros Γ ρ1 ρ2 h.
    eapply positionR_context_position_inv.
    eassumption.
  Qed.

  Lemma it_mkLambda_or_LetIn_inj :
    forall Γ u v,
      it_mkLambda_or_LetIn Γ u =
      it_mkLambda_or_LetIn Γ v ->
      u = v.
  Proof.
    intros Γ u v e.
    revert u v e.
    induction Γ as [| [na [b|] A] Γ ih ] ; intros u v e.
    - assumption.
    - simpl in e. cbn in e.
      apply ih in e.
      inversion e. reflexivity.
    - simpl in e. cbn in e.
      apply ih in e.
      inversion e. reflexivity.
  Qed.

  Equations(noeqns) _isconv_args' (Γ : context) (t : term)
            (π1 : stack) (h1 : wtp Γ t π1)
            (π2 : stack) (h2 : wtp Γ t π2)
            (aux : Aux' Γ t π1 π2 h2)
    : { b : bool | if b then ∥ Σ ;;; Γ |- zippx t π1 = zippx t π2 ∥ else True } :=

    _isconv_args' Γ t (App u1 ρ1) h1 (App u2 ρ2) h2 aux
    with aux u1 u2 (coApp t ρ1) (coApp t ρ2) _ _ _ Conv := {
    | @exist true H1 with _isconv_args' Γ (tApp t u1) ρ1 _ ρ2 _ _ := {
      | @exist true H2 := yes ;
      | @exist false _ := no
      } ;
    | @exist false _ := no
    } ;

    _isconv_args' Γ t ε h1 ε h2 aux := yes ;

    _isconv_args' Γ t π1 h1 π2 h2 aux := no.
  Next Obligation.
    constructor. apply conv_refl.
  Qed.
  Next Obligation.
    split ; try reflexivity.
    unfold xposition. eapply positionR_poscat.
    cbn. eapply positionR_poscat. constructor.
  Qed.
  Next Obligation.
    destruct H1 as [H1]. unfold zippx in H1.
    simpl in H1.
    apply zipx_welltyped.
    clear aux.
    apply welltyped_zipx in h2. cbn in h2.
    (* We need subject conversion here it woud seem *)
    admit.
  Admitted.
  Next Obligation.
    simpl in H. destruct H as [eq hp].
    eapply aux.
    - assumption.
    - instantiate (1 := h2'). split.
      + simpl. assumption.
      + simpl.
        unfold zipx in eq.
        apply it_mkLambda_or_LetIn_inj in eq.
        apply positionR_xposition_inv in hp.
        unfold xposition. cbn. apply positionR_poscat.


        (* dependent induction hp. *)
        (* * rewrite H, H0. constructor. *)
        (* * rewrite H, H0. cbn. constructor. *)
        (*   destruct ρ0. all: try discriminate. *)
        (*   -- cbn in eq. destruct ρ1. all: try discriminate. *)
        (*      ++ cbn in H, H0. *)

        Lemma positionR_stack_app_r :
          forall ρ1 ρ2,
            positionR (stack_position ρ1) (stack_position ρ2) ->
            positionR (stack_position ρ1) (stack_position ρ2 ++ [app_l]).
        Proof.
          intros ρ1 ρ2 h.
          dependent induction h.
          - rewrite H, H0. constructor.
          - rewrite H, H0. cbn. constructor.
            destruct ρ1. all: try discriminate H.
            + cbn in H.
            (* eapply IHh. *)
        Abort.



(* zipx Γ u0 ρ0 = zipx Γ (tApp t u1) ρ1 *)
(*   hp : positionR (stack_position ρ0) (stack_position ρ1) *)
(*   leq : conv_pb *)
(*   ============================ *)
(*   positionR (stack_position ρ0) (stack_position ρ1 ++ [app_l]) *)
  Admitted.
  Next Obligation.
    destruct H2 as [H2], H1 as [H1].
    constructor.
    unfold zippx. simpl.
    unfold zippx in H1.
    unfold zippx in H2.
    case_eq (decompose_stack ρ1). intros l1 θ1 e1.
    case_eq (decompose_stack ρ2). intros l2 θ2 e2.
    simpl in H1.
    rewrite e1 in H2. rewrite e2 in H2.
    cbn.
    pose proof (decompose_stack_eq _ _ _ e1) as eq1.
    pose proof (decompose_stack_eq _ _ _ e2) as eq2.
    rewrite eq1 in H1. rewrite eq2 in H1.
    rewrite !stack_context_appstack in H1.
    (* Not clear how to conclude, but it seems fine. *)
    (* eapply conv_trans ; try eassumption. *)
    admit.
  Admitted.


    eapply aux.
    - eassumption.
    - assert (R_trans : forall x y z, R x y -> R y z -> R x z) by admit.
      eapply R_trans ; try eassumption.
      unshelve eapply R_positionR ; try reflexivity.
      simpl. unfold xposition. eapply positionR_poscat.
      cbn.
      (* This doesn't work by transitivity. *)
      give_up.
  Abort.

(* Equations(noeqns) _isconv_args (Γ : context) (t : term) *)
(*             (π1 : stack) (h1 : wtp Γ t π1) *)
(*             (π2 : stack) (h2 : wtp Γ t π2) *)
(*             (aux : Aux Args Γ t π1 π2 h2) *)
(*     : { b : bool | if b then ∥ Σ ;;; Γ |- zippx t π1 = zippx t π2 ∥ else True } := *)

  Equations(noeqns) _isconv_args (Γ : context) (t : term)
            (π1 : stack) (h1 : wtp Γ t π1)
            (π2 : stack) (h2 : wtp Γ t π2)
            (aux : Aux Args Γ t π1 π2 h2)
    : { b : bool | if b then ∥ Σ ;;; Γ |- zippx t π1 = zippx t π2 ∥ else True } :=

    _isconv_args Γ t (App u1 ρ1) h1 (App u2 ρ2) h2 aux
    with isconv_red_raw Γ Conv u1 (coApp t ρ1) u2 (coApp t ρ2) aux := {
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
    unshelve eapply R_positionR.
    - simpl. reflexivity.
    - simpl. unfold xposition. eapply positionR_poscat.
      cbn. eapply positionR_poscat. constructor.
  Qed.
  Next Obligation.
    destruct h1 as [h1]. unfold zippx in h1.
    simpl in h1.
    apply zipx_welltyped.
    clear aux.
    apply welltyped_zipx in h2. cbn in h2.
    (* We need subject conversion here it woud seem *)
    admit.
  Admitted.
  Next Obligation.
    unshelve eapply R_positionR.
    - simpl. reflexivity.
    - simpl. unfold xposition. eapply positionR_poscat.
      cbn. rewrite <- app_nil_r at 1. eapply positionR_poscat.
      (* SERIOUS ISSUE *)
      (* It is not clear how to get rid of this one!
         Indeed, the position is not smaller, worse, it is the other way around.
         Also, it is not entierely clear what gets smaller here!
       *)
      fail "Is all hope lost?!".
  Admitted.
  Next Obligation.
    destruct b ; auto.
    destruct h1 as [h1]. destruct h as [h].
    constructor.
    eapply conv_trans ; try eassumption.
    eapply conv_context. eapply conv_App_r. assumption.
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