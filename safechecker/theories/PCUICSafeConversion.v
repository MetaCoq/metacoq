(* Distributed under the terms of the MIT license. *)
From Coq Require Import ProofIrrelevance.
From MetaCoq.Template Require Import config utils uGraph.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICReflect PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICGlobalEnv
     PCUICCumulativity PCUICEquality PCUICConversion
     PCUICSafeLemmata PCUICNormal PCUICInversion PCUICReduction PCUICPosition
     PCUICPrincipality PCUICContextConversion PCUICSN PCUICUtils PCUICWeakening
     PCUICConvCumInversion.
From MetaCoq.SafeChecker Require Import PCUICEqualityDec PCUICErrors PCUICSafeReduce.

Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

Local Set Keyed Unification.

Set Default Goal Selector "!".

Module PSR := PCUICSafeReduce.

Instance red_brs_refl Σ Γ: CRelationClasses.Reflexive (@red_brs Σ Γ).
Proof.
  intros brs.
  eapply All2_same; unfold on_Trel; split; reflexivity.
Qed.

(** * Conversion for PCUIC without fuel

  Following PCUICSafeReduce, we derive a fuel-free implementation of
  conversion (and cumulativity) checking for PCUIC.

 *)

Section Conversion.

  Context {cf : checker_flags}.
  Context (Σ : global_env_ext).
  Context (hΣ : ∥ wf Σ ∥) (Hφ : ∥ on_udecl Σ.1 Σ.2 ∥).
  Context (G : universes_graph) (HG : is_graph_of_uctx G (global_ext_uctx Σ)).

  Local Definition hΣ' : ∥ wf_ext Σ ∥.
  Proof.
    destruct hΣ, Hφ; now constructor.
  Defined.


  Set Equations With UIP.

  Inductive state :=
  | Reduction
  | Term
  | Args
  | Fallback.

  Inductive stateR : state -> state -> Prop :=
  | stateR_Term_Reduction : stateR Term Reduction
  | stateR_Args_Term : stateR Args Term
  | stateR_Fallback_Term : stateR Fallback Term
  | stateR_Args_Fallback : stateR Args Fallback.

  Derive Signature for stateR.

  Lemma stateR_Acc :
    forall s, Acc stateR s.
  Proof.
    assert (Acc stateR Args) as hArgs.
    { constructor. intros s h.
      dependent induction h.
      all: discriminate.
    }
    assert (Acc stateR Fallback) as hFall.
    { constructor. intros s h.
      dependent induction h.
      all: try discriminate.
      apply hArgs.
    }
    assert (Acc stateR Term) as hTerm.
    { constructor. intros s h.
      dependent induction h.
      all: try discriminate.
      - apply hArgs.
      - apply hFall.
    }
    assert (Acc stateR Reduction) as hRed.
    { constructor. intros s h.
      dependent induction h.
      all: try discriminate.
      apply hTerm.
    }
    intro s. destruct s ; eauto.
  Qed.

  Notation wtp Γ t π :=
    (welltyped Σ Γ (zipc t π)) (only parsing).

  Set Primitive Projections.

  Record pack (Γ : context) := mkpack {
    st   : state ;
    tm1  : term ;
    stk1 : stack ;
    tm2  : term ;
    stk2 : stack ;
    wth  : wtp Γ tm2 stk2
  }.

  Arguments st {_} _.
  Arguments tm1 {_} _.
  Arguments stk1 {_} _.
  Arguments tm2 {_} _.
  Arguments stk2 {_} _.
  Arguments wth {_} _.

  Definition wterm Γ := { t : term | welltyped Σ Γ t }.

  Definition wcored Γ (u v : wterm Γ) :=
    cored' Σ Γ (` u) (` v).

  Lemma wcored_wf :
    forall Γ, well_founded (wcored Γ).
  Proof.
    intros Γ [u hu].
    destruct hΣ as [hΣ'].
    apply normalisation_upto in hu as h. 2: assumption.
    dependent induction h.
    constructor. intros [y hy] r.
    unfold wcored in r. cbn in r.
    eapply H0. all: assumption.
  Qed.

  Definition eqt u v :=
    ∥ eq_term Σ Σ u v ∥.

  Lemma eq_term_valid_pos :
    forall {u v p},
      validpos u p ->
      eqt u v ->
      validpos v p.
  Proof.
    intros u v p vp [e].
    eapply eq_term_valid_pos. all: eauto.
  Qed.

  Definition weqt {Γ} (u v : wterm Γ) :=
    eqt (` u) (` v).

  Equations R_aux (Γ : context) :
    (∑ t : term, pos t × (∑ w : wterm Γ, pos (` w) × state)) ->
    (∑ t : term, pos t × (∑ w : wterm Γ, pos (` w) × state)) -> Prop :=
    R_aux Γ :=
      t ⊨ eqt \ cored' Σ Γ by _ ⨷
      @posR t ⊗
      w ⊨ weqt \ wcored Γ by _ ⨷
      @posR (` w) ⊗
      stateR.
  Next Obligation.
    split. 2: intuition eauto.
    exists (` p).
    destruct p as [p hp].
    eapply eq_term_valid_pos. all: eauto.
  Defined.
  Next Obligation.
    split. 2: assumption.
    exists (` p).
    destruct x as [u hu], x' as [v hv].
    destruct p as [p hp].
    simpl in *.
    eapply eq_term_valid_pos. all: eauto.
  Defined.

  Derive Signature for Subterm.lexprod.

  Lemma R_aux_Acc :
    forall Γ t p w q s,
      welltyped Σ Γ t ->
      Acc (R_aux Γ) (t ; (p, (w ; (q, s)))).
  Proof.
    intros Γ t p w q s ht.
    rewrite R_aux_equation_1.
    unshelve eapply dlexmod_Acc.
    - intros x y [e]. constructor. eapply eq_term_sym. assumption.
    - intros x y z [e1] [e2]. constructor. eapply eq_term_trans. all: eauto.
    - intro u. eapply Subterm.wf_lexprod.
      + intro. eapply posR_Acc.
      + intros [w' q'].
        unshelve eapply dlexmod_Acc.
        * intros x y [e]. constructor. eapply eq_term_sym. assumption.
        * intros x y z [e1] [e2]. constructor. eapply eq_term_trans. all: eauto.
        * intros [t' h']. eapply Subterm.wf_lexprod.
          -- intro. eapply posR_Acc.
          -- intro. eapply stateR_Acc.
        * intros x x' y [e] [y' [x'' [r [[e1] [e2]]]]].
          eexists _,_. intuition eauto using sq.
          constructor. eapply eq_term_trans. all: eauto.
        * intros x. exists (sq (eq_term_refl _ _ _)). intros [[q'' h] ?].
          unfold R_aux_obligations_obligation_2.
          simpl. f_equal. f_equal.
          eapply uip.
        * intros x x' [[q'' h] ?] [e].
          unfold R_aux_obligations_obligation_2.
          simpl. f_equal. f_equal.
          eapply uip.
        * intros x y z e1 e2 [[q'' h] ?].
          unfold R_aux_obligations_obligation_2.
          simpl. f_equal. f_equal.
          eapply uip.
        * intros [t1 ht1] [t2 ht2] [e] [[q1 hq1] s1] [[q2 hq2] s2] h.
          simpl in *.
          dependent destruction h.
          -- left. unfold posR in *. simpl in *. assumption.
          -- match goal with
             | |- context [ exist q1 ?hq1 ] =>
               assert (ee : hq1 = hq2) by eapply uip
             end.
            rewrite ee. right. clear ee. assumption.
        * eapply wcored_wf.
    - intros x x' y [e] [y' [x'' [r [[e1] [e2]]]]].
      eexists _,_. intuition eauto using sq.
      constructor. eapply eq_term_trans. all: eauto.
    - intros x. exists (sq (eq_term_refl _ _ _)). intros [[q' h] [? [? ?]]].
      unfold R_aux_obligations_obligation_1.
      simpl. f_equal. f_equal.
      eapply uip.
    - intros x x' [[q' h] [? [? ?]]] [e].
      unfold R_aux_obligations_obligation_1.
      simpl. f_equal. f_equal.
      eapply uip.
    - intros x y z e1 e2 [[q' h] [? [? ?]]].
      unfold R_aux_obligations_obligation_1.
      simpl. f_equal. f_equal.
      eapply uip.
    - intros x x' [e]
             [[p1 hp1] [[u hu] [[q1 hq1] s1]]]
             [[p2 hp2] [[v hv] [[q2 hq2] s2]]] hl.
      simpl in *.
      dependent destruction hl.
      + left. unfold posR in *.
        simpl in *.
        assumption.
      + match goal with
        | |- context [ exist p1 ?hp1 ] =>
          assert (ee : hp1 = hp2) by eapply uip
        end.
        rewrite ee. right. clear ee.
        dependent destruction H.
        * left. assumption.
        * unshelve econstructor 2. 1: assumption.
          dependent destruction H.
          -- left. unfold posR in *.
             simpl in *. assumption.
          -- right. assumption.
    - eapply normalisation_upto. all: assumption.
  Qed.

  Notation pzt u := (zipc (tm1 u) (stk1 u)) (only parsing).
  Notation pps1 u := (stack_pos (tm1 u) (stk1 u)) (only parsing).
  Notation pwt u := (exist _ (wth u)) (only parsing).
  Notation pps2 u := (stack_pos (tm2 u) (stk2 u)) (only parsing).

  Notation obpack u :=
    (pzt u ; (pps1 u, (pwt u ; (pps2 u, st u)))) (only parsing).

  Definition R Γ (u v : pack Γ) :=
    R_aux Γ (obpack u) (obpack v).

  Lemma R_Acc :
    forall Γ u,
      welltyped Σ Γ (zipc (tm1 u) (stk1 u)) ->
      Acc (R Γ) u.
  Proof.
    intros Γ u h.
    eapply Acc_fun with (f := fun x => obpack x).
    apply R_aux_Acc. assumption.
  Qed.

  Notation eq_term Σ t u := (eq_term Σ Σ t u).

  Lemma R_cored :
    forall Γ p1 p2,
      cored Σ Γ (pzt p1) (pzt p2) ->
      R Γ p1 p2.
  Proof.
    intros Γ p1 p2 h.
    left. eapply cored_cored'. assumption.
  Qed.

  Lemma R_aux_positionR :
    forall Γ t1 t2 (p1 : pos t1) (p2 : pos t2) s1 s2,
      eq_term Σ t1 t2 ->
      positionR (` p1) (` p2) ->
      R_aux Γ (t1 ; (p1, s1)) (t2 ; (p2, s2)).
  Proof.
    intros Γ t1 t2 p1 p2 [? [? ?]] s2 e h.
    unshelve eright.
    - constructor. assumption.
    - left. unfold posR. simpl. assumption.
  Qed.

  Lemma R_positionR :
    forall Γ p1 p2,
      eq_term Σ (pzt p1) (pzt p2) ->
      positionR (` (pps1 p1)) (` (pps1 p2)) ->
      R Γ p1 p2.
  Proof.
    intros Γ [s1 t1 π1 ρ1 t1' h1] [s2 t2 π2 ρ2 t2' h2] e h. simpl in *.
    eapply R_aux_positionR ; simpl.
    - assumption.
    - assumption.
  Qed.

  Lemma R_aux_cored2 :
    forall Γ t1 t2 (p1 : pos t1) (p2 : pos t2) w1 w2 q1 q2 s1 s2,
      eq_term Σ t1 t2 ->
      ` p1 = ` p2 ->
      cored' Σ Γ (` w1) (` w2) ->
      R_aux Γ (t1 ; (p1, (w1 ; (q1, s1)))) (t2 ; (p2, (w2 ; (q2, s2)))).
  Proof.
    intros Γ t1 t2 [p1 hp1] [p2 hp2] [t1' h1'] [t2' h2'] q1 q2 s1 s2 e1 e2 h.
    cbn in e2. cbn in h. subst.
    unshelve eright.
    - constructor. assumption.
    - unfold R_aux_obligations_obligation_1. simpl.
      match goal with
      | |- context [ exist p2 ?hp1 ] =>
        assert (e : hp1 = hp2) by eapply uip
      end.
      rewrite e.
      right.
      left. assumption.
  Qed.

  Lemma R_cored2 :
    forall Γ p1 p2,
      eq_term Σ (pzt p1) (pzt p2) ->
      ` (pps1 p1) = ` (pps1 p2) ->
      cored Σ Γ (` (pwt p1)) (` (pwt p2)) ->
      R Γ p1 p2.
  Proof.
    intros Γ [s1 t1 π1 ρ1 t1' h1] [s2 t2 π2 ρ2 t2' h2] e1 e2 h. simpl in *.
    eapply R_aux_cored2. all: simpl. all: auto.
    destruct s1, s2.
    all: eapply cored_cored'.
    all: assumption.
  Qed.

  Lemma R_aux_positionR2 :
    forall Γ t1 t2 (p1 : pos t1) (p2 : pos t2) w1 w2 q1 q2 s1 s2,
      eq_term Σ t1 t2 ->
      ` p1 = ` p2 ->
      eq_term Σ (` w1) (` w2) ->
      positionR (` q1) (` q2) ->
      R_aux Γ (t1 ; (p1, (w1 ; (q1, s1)))) (t2 ; (p2, (w2 ; (q2, s2)))).
  Proof.
    intros Γ t1 t2 [p1 hp1] [p2 hp2] [t1' h1'] [t2' h2'] q1 q2 s1 s2 e1 e2 e3 h.
    cbn in e2. cbn in e3. subst.
    unshelve eright.
    - constructor. assumption.
    - unfold R_aux_obligations_obligation_1. simpl.
      match goal with
      | |- context [ exist p2 ?hp1 ] =>
        assert (e : hp1 = hp2) by eapply uip
      end.
      rewrite e.
      right.
      unshelve eright.
      + constructor. assumption.
      + left. unfold posR. simpl. assumption.
  Qed.

  Lemma R_positionR2 :
    forall Γ p1 p2,
      eq_term Σ (pzt p1) (pzt p2) ->
      ` (pps1 p1) = ` (pps1 p2) ->
      eq_term Σ (` (pwt p1)) (` (pwt p2)) ->
      positionR (` (pps2 p1)) (` (pps2 p2)) ->
      R Γ p1 p2.
  Proof.
    intros Γ [s1 t1 π1 ρ1 t1' h1] [s2 t2 π2 ρ2 t2' h2] e1 e2 e3 h.
    simpl in *.
    eapply R_aux_positionR2. all: simpl. all: auto.
  Qed.

  Lemma R_aux_stateR :
    forall Γ t1 t2 (p1 : pos t1) (p2 : pos t2) w1 w2 q1 q2 s1 s2 ,
      eq_term Σ t1 t2 ->
      ` p1 = ` p2 ->
      eq_term Σ (` w1) (` w2) ->
      ` q1 = ` q2 ->
      stateR s1 s2 ->
      R_aux Γ (t1 ; (p1, (w1 ; (q1, s1)))) (t2 ; (p2, (w2 ; (q2, s2)))).
  Proof.
    intros Γ t1 t2 [p1 hp1] [p2 hp2] [t1' h1'] [t2' h2'] [q1 hq1] [q2 hq2] s1 s2
           e1 e2 e3 e4 h.
    cbn in e2. cbn in e3. cbn in e4. subst.
    unshelve eright.
    - constructor. assumption.
    - unfold R_aux_obligations_obligation_1. simpl.
      match goal with
      | |- context [ exist p2 ?hp1 ] =>
        assert (e : hp1 = hp2) by eapply uip
      end.
      rewrite e.
      right.
      unshelve eright.
      + constructor. assumption.
      + unfold R_aux_obligations_obligation_2. simpl.
        match goal with
        | |- context [ exist q2 ?hq1 ] =>
          assert (e' : hq1 = hq2) by eapply uip
        end.
        rewrite e'.
        right. assumption.
  Qed.

  Lemma R_stateR :
    forall Γ p1 p2,
      eq_term Σ (pzt p1) (pzt p2) ->
      ` (pps1 p1) = ` (pps1 p2) ->
      eq_term Σ (` (pwt p1)) (` (pwt p2)) ->
      ` (pps2 p1) = ` (pps2 p2) ->
      stateR (st p1) (st p2) ->
      R Γ p1 p2.
  Proof.
    intros Γ [s1 t1 π1 ρ1 t1' h1] [s2 t2 π2 ρ2 t2' h2] e1 e2 e3 e4 h.
    simpl in *.
    eapply R_aux_stateR. all: simpl. all: auto.
  Qed.

  Notation eqb_ctx := (eqb_ctx Σ G).
  Notation eqb_term := (eqb_term Σ G).
  Notation leqb_term := (leqb_term Σ G).

  Definition eqb_term_stack t1 π1 t2 π2 :=
    eqb_ctx (stack_context π1) (stack_context π2) &&
    eqb_term (zipp t1 π1) (zipp t2 π2).

  Lemma eqb_term_stack_spec :
    forall Γ t1 π1 t2 π2,
      eqb_term_stack t1 π1 t2 π2 ->
      eq_context_upto Σ (eq_universe Σ) (eq_universe Σ)
                      (Γ ,,, stack_context π1)
                      (Γ ,,, stack_context π2) ×
      eq_term Σ (zipp t1 π1) (zipp t2 π2).
  Proof.
    intros Γ t1 π1 t2 π2 h.
    apply andb_and in h as [h1 h2].
    split.
    - eapply eq_context_upto_cat.
      + eapply eq_context_upto_refl; tc.
      + eapply eqb_ctx_spec; eassumption.
    - eapply eqb_term_spec; eassumption.
  Qed.

  Definition leqb_term_stack t1 π1 t2 π2 :=
    eqb_ctx (stack_context π1) (stack_context π2) &&
    leqb_term (zipp t1 π1) (zipp t2 π2).
  
  Lemma leqb_term_stack_spec :
    forall Γ t1 π1 t2 π2,
      leqb_term_stack t1 π1 t2 π2 ->
      eq_context_upto Σ (eq_universe Σ) (eq_universe Σ)
                      (Γ ,,, stack_context π1)
                      (Γ ,,, stack_context π2) ×
      leq_term Σ Σ (zipp t1 π1) (zipp t2 π2).
  Proof.
    intros Γ t1 π1 t2 π2 h.
    apply andb_and in h as [h1 h2].
    split.
    - eapply eq_context_upto_cat.
      + eapply eq_context_upto_refl; tc.
      + eapply eqb_ctx_spec; eassumption.
    - eapply leqb_term_spec; eassumption.
  Qed.

  Notation conv_stack_ctx Γ π1 π2 :=
    (∥ conv_context Σ (Γ ,,, stack_context π1) (Γ ,,, stack_context π2) ∥).

  Notation conv_term leq Γ t π t' π' :=
    (conv_cum leq Σ (Γ ,,, stack_context π) (zipp t π) (zipp t' π'))
      (only parsing).

  Notation alt_conv_term Γ t π t' π' :=
    (∥ Σ ;;; Γ ,,, stack_context π |- zipp t π = zipp t' π' ∥)
      (only parsing).

  Inductive ConversionResult (P : Prop) :=
  | Success (h : P)
  | Error (e : ConversionError) (h : ~P).

  Arguments Success {_} _.
  Arguments Error {_} _.

  Definition isred_full Γ t π :=
    isApp t = false /\
    ∥whnf RedFlags.nodelta Σ (Γ,,, stack_context π) (zipp t π)∥.
  
  Lemma isred_full_nobeta Γ t π :
    isred_full Γ t π ->
    isLambda t ->
    isStackApp π = false.
  Proof.
    intros (?&isr) islam.
    destruct t; cbn in *; try easy.
    unfold zipp in isr.
    destruct π; cbn in *; try easy.
    destruct (decompose_stack π) in isr.
    destruct isr as [isr].
    depelim isr; rewrite mkApps_tApp in *; try solve [solve_discr].
    apply whne_mkApps_inv in w; [|easy].
    destruct w as [|(?&?&?&?&?&?&?&?)]; [|discriminate].
    depelim w; solve_discr; discriminate.
   Qed.

  Lemma eta_pair {A B} (p q : A * B) :
    p = q ->
    (p.1, p.2) = (q.1, q.2).
  Proof. now destruct p, q. Qed.

  Ltac is_var t :=
    match goal with
    | v : _ |- _ =>
      match t with
      | v => idtac
      end
    end.

  Lemma zipp_stack_cat_decompose_stack t π π' :
    zipp t (π +++ (decompose_stack π').2) = zipp t π.
  Proof.
    rewrite zipp_stack_cat; auto.
    destruct decompose_stack eqn:decomp.
    now apply decompose_stack_noStackApp in decomp.
  Qed.

  Lemma zipc_decompose_stack_empty t π :
    (decompose_stack π).2 = ε ->
    zipc t π = zipp t π.
  Proof.
    destruct decompose_stack eqn:decomp.
    apply decompose_stack_eq in decomp as ->.
    cbn; intros ->.
    rewrite zipc_appstack, zipp_as_mkApps, decompose_stack_appstack.
    cbn.
    now rewrite app_nil_r.
  Qed.

  Ltac reduce_stack_facts :=
    repeat
      match goal with
      | [H: (?a, ?b) = reduce_stack ?f ?Σ ?wf ?Γ ?t ?π ?h |- _] =>
        let rid := fresh "r" in
        let decompid := fresh "d" in
        let whid := fresh "w" in
        let isr := fresh "isr" in
        pose proof (reduce_stack_sound f Σ wf Γ t π h) as [rid];
        pose proof (reduce_stack_decompose f Σ wf Γ t π h) as decompid;
        pose proof (reduce_stack_whnf f Σ wf Γ t π h) as whid;
        pose proof (reduce_stack_isred f Σ wf Γ t π h) as isr;
        rewrite <- H in rid, decompid, whid, isr; cbn in rid, decompid, whid, isr;
        clear H
      end.
  
  Lemma zipc_unfold_decompose_stack t π :
    zipc t π = zipc (mkApps t (decompose_stack π).1) (decompose_stack π).2.
  Proof.
    rewrite <- zipc_appstack.
    destruct (decompose_stack π) eqn:decomp.
    now apply decompose_stack_eq in decomp as ->.
  Qed.

  Ltac simpl_stacks :=
    (repeat
       match goal with
       | [H: (?a, ?b) = decompose_stack ?π |- _] =>
         is_var a;
         is_var b;
         apply eta_pair in H; cbn in H; noconf H
       end);
    (repeat
       match goal with
       | [H: context[decompose_stack (appstack ?l ?ρ)] |- _] =>
         (rewrite (decompose_stack_appstack l ρ) in H; cbn in H) || fail 2
       | [H: context[stack_context (?π +++ ?π')] |- _] =>
         (rewrite (stack_context_stack_cat π' π) in H; cbn in H) || fail 2
       | [H: (decompose_stack ?π).2 = ε, H': context[stack_context ?π] |- _] =>
         (rewrite <- (stack_context_decompose π), H in H'; cbn in H') || fail 2
       | [H: (decompose_stack ?π).2 = ε, H': context[zipc ?t ?π] |- _] =>
         (rewrite (zipc_decompose_stack_empty t π H) in H'; cbn in H') || fail 2
       | [H: context[stack_context (decompose_stack ?π).2] |- _] =>
         (rewrite (stack_context_decompose π) in H; cbn in H) || fail 2
       | [H: context[zipp ?t (?π +++ (decompose_stack ?π').2)] |- _] =>
         (rewrite (zipp_stack_cat_decompose_stack t π π') in H; cbn in H) || fail 2
       | [H: context[zipc ?t (appstack ?args ?π)] |- _] =>
         (rewrite (@zipc_appstack t args π) in H; cbn in H) || fail 2
       | [H: context[zipc ?t (?π +++ ?π')] |- _] =>
         (rewrite (zipc_stack_cat t π π') in H; cbn in H) || fail 2
       | [H: context[zip (mkApps ?t (decompose_stack ?π).1, decompose_stack ?π).2] |- _] =>
         unfold zip in H
       | [H: context[zipc (mkApps ?t (decompose_stack ?π).1) (decompose_stack ?π).2] |- _] =>
         (rewrite <- (zipc_unfold_decompose_stack t π) in H; cbn in H) || fail 2
       | [H: isStackApp ?π = false, H': context[zipp ?t ?π] |- _] =>
         (rewrite (zipp_noStackApp t π H) in H'; cbn in H') || fail 2
       | [H: (decompose_stack ?π).2 = (decompose_stack ?π').2, H': context[stack_context ?π] |- _] =>
         (rewrite <- (stack_context_decompose π), H, (stack_context_decompose π') in H'; cbn in H')
         || fail 2

       | [|- context[decompose_stack (appstack ?l ?ρ)]] =>
         (rewrite (decompose_stack_appstack l ρ); cbn) || fail 2
       | [|- context[stack_context (?π +++ ?π')]] =>
         (rewrite (stack_context_stack_cat π' π); cbn) || fail 2
       | [H: (decompose_stack ?π).2 = ε |- context[stack_context ?π]] =>
         (rewrite <- (stack_context_decompose π), H; cbn) || fail 2
       | [H: (decompose_stack ?π).2 = ε |- context[zipc ?t ?π]] =>
         (rewrite (zipc_decompose_stack_empty t π H); cbn) || fail 2
       | [|- context[stack_context (decompose_stack ?π).2]] =>
         (rewrite (stack_context_decompose π); cbn) || fail 2
       | [|- context[zipp ?t (?π +++ (decompose_stack ?π').2)]] =>
         (rewrite (zipp_stack_cat_decompose_stack t π π'); cbn) || fail 2
       | [|- context[zipc ?t (appstack ?args ?π)]] =>
         (rewrite (@zipc_appstack t args π); cbn) || fail 2
       | [|- context[zipc ?t (?π +++ ?π')]] =>
         (rewrite (zipc_stack_cat t π π'); cbn) || fail 2
       | [|- context[zip (mkApps ?t (decompose_stack ?π).1, decompose_stack ?π).2]] =>
         unfold zip
       | [|- context[zipc (mkApps ?t (decompose_stack ?π).1) (decompose_stack ?π).2]] =>
         (rewrite <- (zipc_unfold_decompose_stack t π); cbn) || fail 2
       | [H: isStackApp ?π = false |- context[zipp ?t ?π]] =>
         (rewrite (zipp_noStackApp t π H); cbn) || fail 2
       | [H: (decompose_stack ?π).2 = (decompose_stack ?π').2 |- context[stack_context ?π]] =>
         (rewrite <- (stack_context_decompose π), H, (stack_context_decompose π'); cbn) || fail 2
       end);
    repeat
      match goal with
      | [H: context[zipp ?t ?π] |- _] => rewrite (zipp_as_mkApps t π) in H
      | [|- context[zipp ?t ?π]] => rewrite (zipp_as_mkApps t π)
      end.
  
  Ltac simpl_reduce_stack := reduce_stack_facts; simpl_stacks.
  
  (* Tailored view for isconv_prog and precondition for fallback case *)
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
  
  (* Note that the arity of this should be the same for all s as otherwise
     the extracted code is not correct *)
  Definition Ret s Γ t π t' π' :=
    forall (leq : conv_pb),
      conv_stack_ctx Γ π π' ->
      (match s with Fallback | Term => isred_full Γ t π | _ => True end) ->
      (match s with Fallback | Term => isred_full Γ t' π' | _ => True end) ->
      (match s with | Fallback => prog_discr t t' | _ => True end) ->
      match s with
      | Reduction
      | Term
      | Fallback => ConversionResult (conv_term leq Γ t π t' π')
      | Args => ConversionResult (∥conv_terms Σ (Γ,,, stack_context π)
                                   (decompose_stack π).1
                                   (decompose_stack π').1∥)
      end.

  Definition Aux s Γ t1 π1 t2 π2 h2 :=
     forall s' t1' π1' t2' π2'
       (h1' : wtp Γ t1' π1')
       (h2' : wtp Γ t2' π2'),
       conv_stack_ctx Γ π1 π2 ->
       R Γ
         (mkpack Γ s' t1' π1' t2' π2' h2')
         (mkpack Γ s t1 π1 t2 π2 h2) ->
       Ret s' Γ t1' π1' t2' π2'.

  Notation yes := (Success _) (only parsing).
  Notation no := (fun e => Error e _) (only parsing).

  (* TODO NOTE
     repack could also take another argument of type
     ConversionError -> ConversionError
     to keep a full error trace (we currently only do it partially).
  *)
  Notation repack e :=
    (match e with Success h => Success _ | Error er h => Error er _ end)
    (only parsing).

  Notation isconv_red_raw leq t1 π1 t2 π2 aux :=
    (aux Reduction t1 π1 t2 π2 _ _ _ _ leq _ I I I) (only parsing).
  Notation isconv_prog_raw leq t1 π1 t2 π2 aux :=
    (aux Term t1 π1 t2 π2 _ _ _ _ leq _ _ _ I) (only parsing).
  Notation isconv_args_raw leq t1 π1 t2 π2 aux :=
    (aux Args t1 π1 t2 π2 _ _ _ _ leq _ I I I) (only parsing).
  Notation isconv_fallback_raw leq t1 π1 t2 π2 aux :=
    (aux Fallback t1 π1 t2 π2 _ _ _ _ leq _ _ _ _) (only parsing).

  Notation isconv_red leq t1 π1 t2 π2 aux :=
    (repack (isconv_red_raw leq t1 π1 t2 π2 aux)) (only parsing).
  Notation isconv_prog leq t1 π1 t2 π2 aux :=
    (repack (isconv_prog_raw leq t1 π1 t2 π2 aux)) (only parsing).
  Notation isconv_args leq t1 π1 t2 π2 aux :=
    (repack (isconv_args_raw leq t1 π1 t2 π2 aux)) (only parsing).
  Notation isconv_fallback leq t1 π1 t2 π2 aux :=
    (repack (isconv_fallback_raw leq t1 π1 t2 π2 aux)) (only parsing).

  Equations(noeqns) _isconv_red (Γ : context) (leq : conv_pb)
            (t1 : term) (π1 : stack) (h1 : wtp Γ t1 π1)
            (t2 : term) (π2 : stack) (h2 : wtp Γ t2 π2)
            (hx : conv_stack_ctx Γ π1 π2)
            (aux : Aux Reduction Γ t1 π1 t2 π2 h2)
    : ConversionResult (conv_term leq Γ t1 π1 t2 π2) :=

    _isconv_red Γ leq t1 π1 h1 t2 π2 h2 hx aux
    with inspect (decompose_stack π1) := {
    | @exist (args1, ρ1) e1 with inspect (decompose_stack π2) := {
      | @exist (args2, ρ2) e2
        with inspect (reduce_stack RedFlags.nodelta Σ hΣ (Γ ,,, stack_context π1) t1 (appstack args1 ε) _) := {
        | @exist (t1',π1') eq1
          with inspect (reduce_stack RedFlags.nodelta Σ hΣ (Γ ,,, stack_context π2) t2 (appstack args2 ε) _) := {
          | @exist (t2',π2') eq2 => isconv_prog leq t1' (π1' +++ ρ1) t2' (π2' +++ ρ2) aux
          }
        }
      }
    }.
  Next Obligation.
    symmetry in e1.
    eapply welltyped_zipc_stack_context. all: eassumption.
  Qed.
  Next Obligation.
    clear aux eq1.
    symmetry in e2.
    eapply welltyped_zipc_stack_context. all: eassumption.
  Qed.
  Next Obligation.
    simpl_reduce_stack.
    eapply red_welltyped ; try assumption ; revgoals.
    - constructor. zip fold. eapply red_context_zip. simpl_stacks. eassumption.
    - cbn. simpl_stacks. assumption.
  Qed.
  Next Obligation.
    simpl_reduce_stack.
    eapply red_welltyped ; try assumption ; revgoals.
    - constructor. zip fold. eapply red_context_zip. simpl_stacks. eassumption.
    - cbn. simpl_stacks. assumption.
  Qed.
  Next Obligation.
    match type of eq1 with
    | _ = reduce_stack ?f ?Σ ?hΣ ?Γ ?t ?π ?h =>
      pose proof (reduce_stack_decompose RedFlags.nodelta _ hΣ _ _ _ h) as d1 ;
      pose proof (reduce_stack_context f Σ hΣ Γ t π h) as c1
    end.
    rewrite <- eq1 in d1. cbn in d1.
    rewrite <- eq1 in c1. cbn in c1.
    rewrite stack_context_appstack in c1. cbn in c1.
    pose proof (decompose_stack_eq _ _ _ (eq_sym e1)). subst.
    match type of eq1 with
    | _ = reduce_stack ?f ?Σ ?hΣ ?Γ ?t ?π ?hh =>
      pose proof (reduce_stack_Req f _ hΣ _ _ _ hh) as [ e | h ]
    end.
    - assert (ee1 := eq1). rewrite e in ee1. inversion ee1. subst.
      match type of eq2 with
      | _ = reduce_stack ?f ?Σ ?hΣ ?Γ ?t ?π ?h =>
        pose proof (reduce_stack_decompose RedFlags.nodelta _ hΣ _ _ _ h) as d2 ;
        pose proof (reduce_stack_context f Σ hΣ Γ t π h) as c2
      end.
      rewrite <- eq2 in d2. cbn in d2.
      rewrite <- eq2 in c2. cbn in c2.
      rewrite stack_context_appstack in c2. cbn in c2.
      pose proof (decompose_stack_eq _ _ _ (eq_sym e2)). subst.
      match type of eq2 with
      | _ = reduce_stack ?f ?Σ ?hΣ ?Γ ?t ?π ?hh =>
        pose proof (reduce_stack_Req f _ hΣ _ _ _ hh) as [ ee | h ]
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
             rewrite zipc_appstack. rewrite zipc_stack_cat.
             repeat zip fold. eapply cored_context.
             assumption.
        * destruct y' as [q hq].
          cbn in H0. inversion H0. subst.
          unshelve eapply R_positionR2.
          -- simpl. rewrite stack_cat_appstack. reflexivity.
          -- simpl. rewrite stack_cat_appstack. reflexivity.
          -- simpl. f_equal.
             rewrite zipc_stack_cat.
             rewrite <- H2.
             rewrite 2!zipc_appstack. cbn. reflexivity.
          -- simpl.
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
        eapply R_cored. simpl.
        rewrite zipc_appstack. rewrite zipc_stack_cat.
        repeat zip fold. eapply cored_context.
        assumption.
      + destruct y' as [q hq].
        cbn in H0. inversion H0. (* Why is noconf failing at this point? *)
        subst.
        unshelve eapply R_positionR ; simpl.
        * f_equal.
          rewrite zipc_stack_cat.
          rewrite <- H2.
          rewrite 2!zipc_appstack. cbn. reflexivity.
        * unfold posR in H. cbn in H.
          rewrite stack_position_appstack in H. cbn in H.
          rewrite stack_position_stack_cat.
          rewrite stack_position_appstack.
          eapply positionR_poscat.
          assumption.
  Qed.
  Next Obligation.
    simpl_reduce_stack.
    assumption.
  Qed.
  Next Obligation.
    simpl_reduce_stack.
    specialize (isr0 eq_refl) as (?&?).
    split; [easy|].
    simpl_stacks.
    easy.
  Qed.
  Next Obligation.
    simpl_reduce_stack.
    specialize (isr eq_refl) as (?&?).
    split; [easy|].
    simpl_stacks.
    easy.
  Qed.
  Next Obligation.
    simpl_reduce_stack.
    destruct hΣ, hx.
    apply -> conv_cum_red_conv_iff; eauto.
  Qed.
  Next Obligation.
    apply h; clear h.
    simpl_reduce_stack.
    destruct hΣ, hx.
    apply <- conv_cum_red_conv_iff; eauto.
  Qed.

  Opaque reduce_stack.
  Equations unfold_one_fix (Γ : context) (mfix : mfixpoint term)
            (idx : nat) (π : stack) (h : wtp Γ (tFix mfix idx) π)
    : option (term * stack) :=

    unfold_one_fix Γ mfix idx π h with inspect (unfold_fix mfix idx) := {
    | @exist (Some (arg, fn)) eq1 with inspect (decompose_stack_at π arg) := {
      | @exist (Some (l, c, θ)) eq2 with inspect (reduce_stack RedFlags.default Σ hΣ (Γ ,,, stack_context θ) c ε _) := {
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
    destruct hΣ.
    cbn. symmetry in eq2.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq2). subst.
    rewrite zipc_appstack in h. cbn in h.
    zip fold in h. apply welltyped_context in h ; auto. simpl in h.
    destruct h as [T h].
    apply inversion_App in h as hh ; auto.
    destruct hh as [na [A' [B' [? [? ?]]]]].
    eexists. eassumption.
  Qed.
  Transparent reduce_stack.

  Derive NoConfusion NoConfusionHom for option.

  Lemma unfold_one_fix_red_zipp :
    forall Γ mfix idx π h fn ξ,
      Some (fn, ξ) = unfold_one_fix Γ mfix idx π h ->
      ∥ red (fst Σ) (Γ ,,, stack_context π) (zipp (tFix mfix idx) π) (zipp fn ξ) ∥.
  Proof.
    intros Γ mfix idx π h fn ξ eq.
    revert eq.
    funelim (unfold_one_fix Γ mfix idx π h).
    all: intro eq ; noconf eq.
    unfold zipp.
    pose proof (eq_sym e0) as eq.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq). subst.
    rewrite 2!decompose_stack_appstack. simpl.
    case_eq (decompose_stack s). intros l' s' e'.
    simpl.
    match type of e1 with
    | _ = reduce_stack ?flags ?Σ ?hΣ ?Γ ?t ?π ?h =>
      pose proof (reduce_stack_sound flags Σ hΣ Γ t π h) as [r1] ;
      pose proof (reduce_stack_decompose flags Σ hΣ Γ t π h) as hd
    end.
    rewrite <- e1 in r1. cbn in r1.
    rewrite <- e1 in hd. cbn in hd.
    constructor.
    rewrite stack_context_appstack. simpl.
    rewrite <- 2!mkApps_nested. cbn. eapply red_mkApps_f.
    pose proof (decompose_stack_eq _ _ _ e'). subst.
    rewrite stack_context_appstack in r1.
    rewrite stack_context_appstack.
    eapply trans_red.
    - eapply red_app_r. exact r1.
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
        replace (#|l| - #|l|) with 0 by lia. cbn.
        case_eq (decompose_stack s0). intros l0 s1 ee.
        rewrite ee in hd.
        pose proof (decompose_stack_eq _ _ _ ee). subst.
        cbn in hd. subst.
        rewrite zipc_appstack. cbn.
        unfold isConstruct_app. rewrite decompose_app_mkApps by auto.
        reflexivity.
  Qed.

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
    | _ = reduce_stack ?flags ?Σ ?hΣ ?Γ ?t ?π ?h =>
      pose proof (reduce_stack_sound flags Σ hΣ Γ t π h) as [r1] ;
      pose proof (reduce_stack_decompose flags Σ hΣ Γ t π h) as hd
    end.
    rewrite <- e1 in r1. cbn in r1.
    rewrite <- e1 in hd. cbn in hd.
    constructor. eapply red_it_mkLambda_or_LetIn.
    rewrite <- 2!mkApps_nested. cbn. eapply red_mkApps_f.
    pose proof (decompose_stack_eq _ _ _ e'). subst.
    rewrite stack_context_appstack in r1.
    eapply trans_red.
    - eapply red_app_r. exact r1.
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
        replace (#|l| - #|l|) with 0 by lia. cbn.
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
    | _ = reduce_stack ?flags ?Σ ?hΣ ?Γ ?t ?π ?h =>
      pose proof (reduce_stack_sound flags Σ hΣ Γ t π h) as [r1] ;
      pose proof (reduce_stack_decompose flags Σ hΣ Γ t π h) as hd
    end.
    rewrite <- e1 in r1. cbn in r1.
    rewrite <- e1 in hd. cbn in hd.
    do 2 zip fold. constructor. eapply red_context_zip.
    eapply trans_red.
    - eapply red_app_r. exact r1.
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
        replace (#|l| - #|l|) with 0 by lia. cbn.
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
    | _ = reduce_stack ?flags ?Σ ?hΣ ?Γ ?t ?π ?h =>
      pose proof (reduce_stack_sound flags Σ hΣ Γ t π h) as [r1] ;
      pose proof (reduce_stack_decompose flags Σ hΣ Γ t π h) as hd
    end.
    rewrite <- e1 in r1. cbn in r1.
    rewrite <- e1 in hd. cbn in hd.
    do 2 zip fold. eapply cored_context.
    eapply cored_red_trans.
    - eapply red_app_r. exact r1.
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
        replace (#|l| - #|l|) with 0 by lia. cbn.
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

  Lemma unfold_one_fix_None Γ mfix idx π wf : 
    None = unfold_one_fix Γ mfix idx π wf ->
    ∥∑args,
      All2 (red Σ (Γ,,, stack_context π)) (decompose_stack π).1 args ×
      whnf RedFlags.default Σ (Γ,,, stack_context π) (mkApps (tFix mfix idx) args)∥.
  Proof.
    funelim (unfold_one_fix Γ mfix idx π wf).
    all: intros [=].
    - constructor; eexists _; split; [apply All2_same; reflexivity|].
      eapply whnf_fixapp.
      now rewrite <- e.
    - constructor; eexists _; split; [apply All2_same; reflexivity|].
      eapply whnf_fixapp.
      rewrite <- e.
      destruct (decompose_stack π) eqn:decomp.
      apply decompose_stack_noStackApp in decomp as ?.
      apply decompose_stack_eq in decomp as ->.
      clear H.
      symmetry in e0.
      now apply decompose_stack_at_appstack_None in e0.
    - match type of e1 with
      | _ = reduce_stack ?a ?b ?c ?d ?e ?f ?g =>
        pose proof (reduce_stack_sound a b c d e f g) as [r];
        pose proof (reduce_stack_whnf a b c d e f g) as wh;
        pose proof (reduce_stack_decompose a b c d e f g) as decomp;
        pose proof (reduce_stack_isred a b c d e f g) as isr
      end.
      rewrite <- e1 in r, wh, decomp, isr.
      specialize (isr eq_refl) as (noapp&_).
      cbn in *.
      clear H e1 H0.
      symmetry in e0.
      apply decompose_stack_at_length in e0 as ?.
      apply decompose_stack_at_eq in e0 as ->.
      rewrite stack_context_appstack.
      cbn.
      apply welltyped_zipc_zipp in h; auto.
      rewrite <- (stack_context_decompose s0), decomp in wh.
      change (App t0 s) with (appstack [t0] s) in *.
      rewrite !decompose_stack_appstack.
      rewrite zipp_as_mkApps, !decompose_stack_appstack in h.
      destruct h as (ty&typ).
      cbn in *.
      rewrite stack_context_appstack in typ.
      cbn in *.
      destruct (decompose_stack s0) eqn:decomp'.
      apply decompose_stack_eq in decomp' as ->.
      rewrite zipc_appstack in r.
      rewrite zipp_appstack in wh.
      cbn in *; subst; cbn in *.
      destruct hΣ, wh.
      constructor; exists (l ++ (mkApps t2 l0) :: (decompose_stack s).1).
      eapply PCUICSR.subject_reduction in typ.
      2: eauto.
      2: apply red_mkApps; [reflexivity|].
      1: split.
      1,3: apply All2_app; [apply All2_same; reflexivity|].
      1,2: constructor; [|apply All2_same; reflexivity].
      1-2: eassumption.
      apply whnf_ne.
      econstructor.
      + eauto.
      + rewrite nth_error_snoc by easy.
        eauto.
      + eapply whnf_fix_arg_whne; eauto.
        now destruct t2.
  Qed.

  Inductive prog_view : term -> term -> Type :=
  | prog_view_App u1 v1 u2 v2 :
      prog_view (tApp u1 v1) (tApp u2 v2)

  | prog_view_Const c1 u1 c2 u2 :
      prog_view (tConst c1 u1) (tConst c2 u2)

  | prog_view_Lambda na1 A1 b1 na2 A2 b2 :
      prog_view (tLambda na1 A1 b1) (tLambda na2 A2 b2)

  | prog_view_Prod na1 A1 B1 na2 A2 B2 :
      prog_view (tProd na1 A1 B1) (tProd na2 A2 B2)

  | prog_view_Case ci p c brs ci' p' c' brs' :
      prog_view (tCase ci p c brs) (tCase ci' p' c' brs')

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

    prog_viewc (tCase ci p c brs) (tCase ci' p' c' brs') :=
      prog_view_Case ci p c brs ci' p' c' brs' ;

    prog_viewc (tProj p c) (tProj p' c') :=
      prog_view_Proj p c p' c' ;

    prog_viewc (tFix mfix idx) (tFix mfix' idx') :=
      prog_view_Fix mfix idx mfix' idx' ;

    prog_viewc (tCoFix mfix idx) (tCoFix mfix' idx') :=
      prog_view_CoFix mfix idx mfix' idx' ;

    prog_viewc u v := prog_view_other u v I.

  Lemma welltyped_wf_local Γ t :
    welltyped Σ Γ t ->
    ∥ wf_local Σ Γ ∥.
  Proof.
    intros [].
    destruct hΣ. 
    now constructor ; eapply typing_wf_local in X.
  Qed.

  Definition eqb_universe_instance u v :=
    forallb2 (check_eqb_universe G) (map Universe.make u) (map Universe.make v).

  Lemma eqb_universe_instance_spec :
    forall u v,
      eqb_universe_instance u v ->
      R_universe_instance (eq_universe (global_ext_constraints Σ)) u v.
  Proof.
    intros u v e.
    unfold eqb_universe_instance in e.
    eapply forallb2_Forall2 in e.
    eapply Forall2_impl. 1: eassumption.
    intros. eapply (check_eqb_universe_spec' G (global_ext_uctx Σ)).
    all: auto.
    + destruct hΣ'. sq. eapply wf_ext_global_uctx_invariants.
      eapply X.
    + destruct hΣ'. sq; eapply global_ext_uctx_consistent; assumption.
  Qed.
  
  Arguments LevelSet.mem : simpl never.

  Notation conv_pb_relb := (conv_pb_relb G).

  Lemma conv_pb_relb_complete leq u u' :
    wf_universe Σ u ->
    wf_universe Σ u' ->
    conv_pb_rel leq (global_ext_constraints Σ) u u' ->
    conv_pb_relb leq u u'.
  Proof.
    intros all1 all2 conv.
    destruct leq; cbn.
    - eapply check_eqb_universe_complete; eauto.
      + destruct hΣ' as [hΣ']; apply wf_ext_global_uctx_invariants, hΣ'.
      + destruct hΣ' as [hΣ']; apply global_ext_uctx_consistent, hΣ'.
    - eapply check_leqb_universe_complete; eauto.
      + destruct hΣ' as [hΣ']; apply wf_ext_global_uctx_invariants, hΣ'.
      + destruct hΣ' as [hΣ']; apply global_ext_uctx_consistent, hΣ'.
  Qed.
  
  Lemma get_level_make l :
    UnivExpr.get_level (UnivExpr.make l) = l.
  Proof. now destruct l. Qed.
  
  Lemma conv_pb_relb_make_complete leq x y :
    LevelSet.mem x (global_ext_levels Σ) ->
    LevelSet.mem y (global_ext_levels Σ) ->
    conv_pb_rel leq (global_ext_constraints Σ) (Universe.make x) (Universe.make y) ->
    conv_pb_relb leq (Universe.make x) (Universe.make y).
  Proof.
    intros memx memy r.
    apply conv_pb_relb_complete; auto.
    - intros ? ->%UnivExprSet.singleton_spec.
      simpl. now apply LevelSet.mem_spec.
    - intros ? ->%UnivExprSet.singleton_spec; simpl.
      now apply LevelSet.mem_spec.
  Qed.
  
  Lemma eqb_universe_instance_complete u u' :
    Forall (fun u => LevelSet.mem u (global_ext_levels Σ)) u ->
    Forall (fun u => LevelSet.mem u (global_ext_levels Σ)) u' ->
    R_universe_instance (eq_universe (global_ext_constraints Σ)) u u' ->
    eqb_universe_instance u u'.
  Proof.
    intros memu memu' r.
    induction u in u', memu, memu', r |- *.
    - now destruct u'.
    - destruct u'; [easy|].
      depelim memu.
      depelim memu'.
      depelim r.
      cbn in *.
      apply Bool.andb_true_iff.
      split.
      + apply (conv_pb_relb_make_complete Conv); auto.
      + now apply IHu.
  Qed.

  Lemma compare_universe_variance_complete leq v u u' :
    LevelSet.mem u (global_ext_levels Σ) ->
    LevelSet.mem u' (global_ext_levels Σ) ->
    R_universe_variance (eq_universe Σ) (conv_pb_rel leq Σ) v u u' ->
    compare_universe_variance (check_eqb_universe G) (conv_pb_relb leq) v u u'.
  Proof.
    intros memu memu' r.
    destruct v; cbn in *; auto.
    - apply conv_pb_relb_make_complete; auto.
    - apply (conv_pb_relb_make_complete Conv); auto.
  Qed.

  Lemma compare_universe_instance_variance_complete leq v u u' :
    Forall (fun u => LevelSet.mem u (global_ext_levels Σ)) u ->
    Forall (fun u => LevelSet.mem u (global_ext_levels Σ)) u' ->
    R_universe_instance_variance (eq_universe Σ) (conv_pb_rel leq Σ) v u u' ->
    compare_universe_instance_variance (check_eqb_universe G) (conv_pb_relb leq) v u u'.
  Proof.
    intros memu memu' r.
    induction u in v, u', memu, memu', r |- *.
    - now destruct u'.
    - destruct u'; [easy|].
      depelim memu.
      depelim memu'.
      cbn in *.
      destruct v; auto.
      apply Bool.andb_true_iff.
      destruct r.
      split.
      + apply compare_universe_variance_complete; auto.
      + now apply IHu.
  Qed.

  Lemma compare_global_instance_complete u v leq gr napp :
    Forall (fun u => LevelSet.mem u (global_ext_levels Σ)) u ->
    Forall (fun u => LevelSet.mem u (global_ext_levels Σ)) v->
    R_global_instance Σ (eq_universe Σ) (conv_pb_rel leq Σ) gr napp u v ->
    compare_global_instance Σ (check_eqb_universe G) (conv_pb_relb leq) gr napp u v.
  Proof.
    intros consu consv r.
    unfold compare_global_instance, R_global_instance, R_opt_variance in *.
    destruct global_variance.
    - apply compare_universe_instance_variance_complete; auto.
    - apply eqb_universe_instance_complete; auto.
  Qed.
  
  Lemma consistent_instance_ext_all_mem udecl u :
    consistent_instance_ext Σ udecl u ->
    Forall (fun u => LevelSet.mem u (global_ext_levels Σ)) u.
  Proof.
    intros cons.
    unfold consistent_instance_ext, consistent_instance in *.
    destruct udecl; [now destruct u|].
    destruct cons as (mems&_&_).
    now apply forallb_Forall.
  Qed.
  
  Lemma welltyped_zipc_tConst_inv Γ c u π :
    welltyped Σ Γ (zipc (tConst c u) π) ->
    exists cst,
      declared_constant Σ c cst
      × consistent_instance_ext Σ (cst_universes cst) u.
  Proof.
    intros h.
    destruct hΣ.
    zip fold in h.
    apply welltyped_context in h; auto.
    destruct h as (?&typ).
    apply inversion_Const in typ as (?&?&?&wfu&_); auto.
    now unfold declared_constant in d.
  Qed.
  
  Equations(noeqns) unfold_constants (Γ : context) (leq : conv_pb)
            (c : kername) (u : Instance.t) (π1 : stack)
            (h1 : wtp Γ (tConst c u) π1)
            (c' : kername) (u' : Instance.t) (π2 : stack)
            (h2 : wtp Γ (tConst c' u') π2)
            (ne : c <> c' \/ (c = c' /\ ~eqb_universe_instance u u'))
            (hx : conv_stack_ctx Γ π1 π2)
            (aux : Aux Term Γ (tConst c u) π1 (tConst c' u') π2 h2)
    : ConversionResult (conv_term leq Γ (tConst c u) π1 (tConst c' u') π2) :=

    unfold_constants Γ leq c u π1 h1 c' u' π2 h2 ne hx aux
    with inspect (lookup_env Σ c') := {
    | @exist (Some (ConstantDecl {| cst_body := Some b |})) eq1 :=
      isconv_red leq (tConst c u) π1 (subst_instance u' b) π2 aux ;
    (* Inductive or not found *)
    | @exist _ eq1 with inspect (lookup_env Σ c) := {
      | @exist (Some (ConstantDecl {| cst_body := Some b |})) eq2 :=
        isconv_red leq (subst_instance u b) π1
                        (tConst c' u') π2 aux ;
      (* Both Inductive or not found *)
      | @exist _ eq2 := no (NotFoundConstants c c')
      }
    }.
  Solve All Obligations with
      Tactics.program_simplify;
      CoreTactics.equations_simpl;
      try solve
          [match goal with
           | [H: welltyped ?Σ ?Γ ?t |- _] =>
             let id := fresh in
             apply welltyped_zipc_tConst_inv in H as id;
               destruct id as (?&?&?);
               unfold declared_constant in *;
               congruence
           end].
  Next Obligation.
    eapply red_welltyped ; auto.
    - exact h2.
    - constructor. eapply red_zipc.
      eapply red_const. eassumption.
  Qed.
  Next Obligation.
    unshelve eapply R_cored2.
    all: try reflexivity.
    simpl. eapply cored_zipc.
    eapply cored_const. eassumption.
  Qed.
  Next Obligation.
    destruct hΣ.
    etransitivity ; try eassumption.
    eapply red_conv_cum_r ; try assumption.
    eapply red_zipp. eapply red_const. eassumption.
  Qed.
  Next Obligation.
    (* Contraposition of previous goal *)
    apply h; clear h.
    destruct hΣ.
    etransitivity ; try eassumption.
    eapply red_conv_cum_l ; try assumption.
    eapply red_zipp. eapply red_const. eassumption.
  Qed.
  Next Obligation.
    eapply red_welltyped ; auto ; [ exact h1 | ].
    constructor. eapply red_zipc.
    eapply red_const. eassumption.
  Qed.
  Next Obligation.
    eapply R_cored. simpl. eapply cored_zipc.
    eapply cored_const. eassumption.
  Qed.
  Next Obligation.
    destruct hΣ as [wΣ].
    etransitivity ; try eassumption.
    eapply red_conv_cum_l ; try assumption.
    eapply red_zipp. eapply red_const. eassumption.
  Qed.
  Next Obligation.
    (* Contraposition of previous goal *)
    apply h; clear h.
    destruct hΣ as [wΣ].
    etransitivity ; try eassumption.
    eapply red_conv_cum_r ; try assumption.
    eapply red_zipp. eapply red_const. eassumption.
  Qed.
  Next Obligation.
    (* Both c and c' are axioms. Either they are different constants or they are not
       convertible because the universes are different. *)
    apply conv_cum_alt in H as [(?&?&(r1&r2)&eq)].
    rewrite zipp_as_mkApps in r1, r2.
    destruct hΣ.
    symmetry in eq1, eq2.
    eapply PCUICConfluence.red_mkApps_tConst_axiom in r1 as (?&->&?); eauto.
    eapply PCUICConfluence.red_mkApps_tConst_axiom in r2 as (?&->&?); eauto.
    apply eq_termp_mkApps_inv in eq as (eq&?); [|easy|easy].
    depelim eq.
    destruct ne as [|(_&ne)]; [congruence|].
    
    clear aux.
    apply welltyped_zipc_tConst_inv in h1 as (cst1&decl1&cons1).
    apply welltyped_zipc_tConst_inv in h2 as (cst2&decl2&cons2).
    eapply PCUICWeakeningEnv.declared_constant_inj in decl1; eauto; subst.
    apply consistent_instance_ext_all_mem in cons1.
    apply consistent_instance_ext_all_mem in cons2.
    eapply eqb_universe_instance_complete in r; auto.
  Qed.

  Lemma All2i_length {A B} (P : nat -> A -> B -> Type) n l l' :
    All2i P n l l' -> #|l| = #|l'|.
  Proof.
    induction 1; simpl; auto; lia.
  Qed.

  Lemma welltyped_zipc_tCase_brs_length Γ ci motive discr brs π :
    welltyped Σ Γ (zipc (tCase ci motive discr brs) π) ->
    exists mib oib, declared_inductive Σ ci mib oib /\ #|brs| = #|ind_ctors oib|.
  Proof.
    intros wf.
    zip fold in wf.
    apply welltyped_context in wf; [|assumption].
    destruct hΣ.
    destruct wf as [ctyp typ].
    apply inversion_Case in typ as (mdecl&idecl&?&[]&?); auto.
    exists mdecl, idecl.
    split; [easy|].
    now apply All2i_length in a1.
  Qed.

  Equations isconv_branches (Γ : context)
    (ci : case_info)
    (p : predicate term) (c : term) (brs1 brs2 : list (branch term))
    (π : stack) (h : wtp Γ (tCase ci p c (brs1 ++ brs2)) π)
    (p' : predicate term) (c' : term) (brs1' brs2' : list (branch term))
    (π' : stack) (h' : wtp Γ (tCase ci p' c' (brs1' ++ brs2')) π')
    (hx : conv_stack_ctx Γ π π')
    (h1 : ∥ conv_brs Σ (Γ ,,, stack_context π) brs1 brs1' ∥)
    (aux : Aux Term Γ (tCase ci p c (brs1 ++ brs2)) π (tCase ci p' c' (brs1' ++ brs2')) π' h')
    : ConversionResult (∥ conv_brs Σ (Γ ,,, stack_context π) brs2 brs2' ∥)
    by struct brs2 :=

    isconv_branches Γ ci
      p c brs1 ({| bcontext := m; bbody := br |} :: brs2) π h
      p' c' brs1' ({| bcontext := m'; bbody := br' |} :: brs2') π' h' hx h1 aux
    (* todo case: here we should check convertibility of the contexts instead
      of propositional equality *)
    with inspect (eqb m m') := {
    | @exist true eq1
      with isconv_red_raw Conv
              br (Case_brs ci p c m brs1 brs2 π)
              br' (Case_brs ci p' c' m' brs1' brs2' π')
      aux := {
      | Success h2
        with isconv_branches Γ ci
              p c (brs1 ++ [{|bcontext := m; bbody := br|}]) brs2 π _
              p' c' (brs1' ++ [{| bcontext := m'; bbody := br'|}]) brs2' π' _ hx _ _ := {
        | Success h3 := yes ;
        | Error e h := no e
        } ;
      | Error e h := no e
      } ;
    | @exist false eq1 := Error (
        CaseBranchNumMismatch ci
          (Γ ,,, stack_context π) p c brs1 m br brs2
          (Γ ,,, stack_context π') p' c' brs1' m' br' brs2'
      ) _
    } ;

    isconv_branches Γ ci
      p c brs1 [] π h
      p' c' brs1' [] π' h' hx h1 aux := yes ;

    isconv_branches Γ ci
      p c brs1 brs2 π h
      p' c' brs1' brs2' π' h' hx h1 aux := False_rect _ _.
  Next Obligation.
    constructor. constructor.
  Qed.
  Next Obligation.
    destruct h1 as [h1].
    apply All2_length in h1 as e1.
    clear aux.
    apply welltyped_zipc_tCase_brs_length in h as (?&?&?&?).
    apply welltyped_zipc_tCase_brs_length in h' as (?&?&?&?).
    pose proof (PCUICInductiveInversion.declared_inductive_unique_sig H H1) as u; noconf u.
    rewrite app_length in *.
    cbn in *.
    lia.
  Qed.
  Next Obligation.
    destruct h1 as [h1].
    apply All2_length in h1 as e1.
    clear aux.
    apply welltyped_zipc_tCase_brs_length in h as (?&?&?&?).
    apply welltyped_zipc_tCase_brs_length in h' as (?&?&?&?).
    pose proof (PCUICInductiveInversion.declared_inductive_unique_sig H H1) as u; noconf u.
    rewrite app_length in *.
    cbn in *.
    lia.
  Qed.
  Next Obligation.
    eapply R_positionR. all: simpl.
    1: reflexivity.
    rewrite <- app_nil_r. eapply positionR_poscat.
    constructor.
  Qed.
  Next Obligation.
    todo "case".
    (*  rewrite <- app_assoc. simpl. assumption. *)
  Qed.
  Next Obligation.
    rewrite <- app_assoc. simpl. assumption.
  Qed.
  Next Obligation.
    todo "case".
    (*destruct h1 as [h1], h2 as [h2]. simpl.
    econstructor. apply All2_app.
    - assumption.
    - constructor. 2: constructor.
      simpl.
      change (m =? m') with (eqb m m') in eq1.
      destruct (eqb_spec m m'). 2: discriminate.
      intuition eauto.*)
  Qed.
  Next Obligation.
    todo "case".
  Qed.
  Next Obligation.
    unshelve eapply aux. all: try eassumption.
    clear aux.
    lazymatch goal with
    | h : R _ _ ?r1 |- R _ _ ?r2 =>
      assert (e : r1 = r2)
    end.
    { clear H0.
      match goal with
      | |- {| wth := ?x |} = _ =>
        generalize x
      end.
      rewrite <- !app_assoc. simpl.
      intro w.
      f_equal.
      eapply proof_irrelevance.
    }
    rewrite <- e. assumption.
  Qed. 
  Next Obligation.
    destruct h1 as [h1], h2 as [h2], h3 as [h3].
    todo "case". (* equality of nats should now be convertibility of contexts *)
    (*change (m =? m') with (eqb m m') in eq1.
    destruct (eqb_spec m m'). 2: discriminate.
    constructor. constructor. all: intuition eauto.*)
  Qed.
  Next Obligation.
    (* Contrapositive of previous obligation *)
    apply h; clear h.
    destruct H as [H]; inversion H; now constructor.
  Qed.
  Next Obligation.
    (* Contrapositive of 3rd obligation above *)
    apply h; clear h.
    destruct h1 as [h1], H as [h2].
    constructor. inversion h2; clear h2.
    destruct X as [_ h2]. simpl in h2. cbn.
    now rewrite app_context_assoc.
  Qed.
  Next Obligation.
    destruct H as [H]; inversion H.
    destruct X as [eq_mm' _].
    todo "case".
    (* change (m =? m') with (eqb m m') in eq1.
    destruct (eqb_spec m m') as [|F]. 1: discriminate.
    apply F, eq_mm'. *)
  Qed.

  Equations isconv_branches' (Γ : context)
    (ci : case_info)
    (p : predicate term) (c : term) (brs : list (branch term))
    (π : stack) (h : wtp Γ (tCase ci p c brs) π)
    (ci' : case_info)
    (p' : predicate term) (c' : term) (brs' : list (branch term))
    (π' : stack) (h' : wtp Γ (tCase ci' p' c' brs') π')
    (hx : conv_stack_ctx Γ π π')
    (ei : ci = ci')
    (aux : Aux Term Γ (tCase ci p c brs) π (tCase ci' p' c' brs') π' h')
    : ConversionResult (∥ conv_brs Σ (Γ ,,, stack_context π) brs brs' ∥) :=

    isconv_branches' Γ ci p c brs π h ci' p' c' brs' π' h' hx eci aux :=
      isconv_branches Γ ci p c [] brs π _ p' c' [] brs' π' _ _ _ _.
  Next Obligation.
    constructor. constructor.
  Qed.
  Next Obligation.
    unshelve eapply aux. all: eassumption.
  Qed.

  (* Factorise notions of fixpoints *)
  Inductive fix_kind :=
  | IndFix
  | CoIndFix.

  Definition mFix k :=
    match k with
    | IndFix => tFix
    | CoIndFix => tCoFix
    end.

  Definition mFix_mfix_ty fk :=
    match fk with
    | IndFix => Fix_mfix_ty
    | CoIndFix => CoFix_mfix_ty
    end.

  Definition mFix_mfix_bd fk :=
    match fk with
    | IndFix => Fix_mfix_bd
    | CoIndFix => CoFix_mfix_bd
    end.

  Definition mFixRargMismatch fk :=
    match fk with
    | IndFix => FixRargMismatch
    | CoIndFix => CoFixRargMismatch
    end.

  Definition mFixMfixMismatch fk :=
    match fk with
    | IndFix => FixMfixMismatch
    | CoIndFix => CoFixMfixMismatch
    end.

  Lemma stack_context_mFix_mfix_bd :
    forall fk na ty ra mfix1 mfix2 idx π,
      stack_context (mFix_mfix_bd fk na ty ra mfix1 mfix2 idx π) =
      stack_context π ,,,
        fix_context_alt (map def_sig mfix1 ++ (na,ty) :: map def_sig mfix2).
  Proof.
    intros fk na ty ra mfix1 mfix2 idx π.
    destruct fk. all: reflexivity.
  Qed.

  Equations isconv_fix_types (fk : fix_kind) (Γ : context)
    (idx : nat)
    (mfix1 mfix2 : mfixpoint term) (π : stack)
    (h : wtp Γ (mFix fk (mfix1 ++ mfix2) idx) π)
    (mfix1' mfix2' : mfixpoint term) (π' : stack)
    (h' : wtp Γ (mFix fk (mfix1' ++ mfix2') idx) π')
    (hx : conv_stack_ctx Γ π π')
    (h1 : ∥ All2 (fun u v =>
                   Σ ;;; Γ ,,, stack_context π |- u.(dtype) = v.(dtype) ×
                   (u.(rarg) = v.(rarg)) * eq_binder_annot u.(dname) v.(dname)
            ) mfix1 mfix1' ∥)
    (aux : Aux Term Γ (mFix fk (mfix1 ++ mfix2) idx) π (mFix fk (mfix1' ++ mfix2') idx) π' h')
    : ConversionResult (∥ All2 (fun u v =>
          Σ ;;; Γ ,,, stack_context π |- u.(dtype) = v.(dtype) ×
          (u.(rarg) = v.(rarg)) * eq_binder_annot u.(dname) v.(dname)
      ) mfix2 mfix2' ∥)
    by struct mfix2 :=

    isconv_fix_types
      fk Γ idx mfix1 (u :: mfix2) π h mfix1' (v :: mfix2') π' h' hx h1 aux
    with inspect (eqb u.(rarg) v.(rarg)) := {
    | @exist true eq1
      with inspect (eqb_binder_annot u.(dname) v.(dname)) := {
      | @exist true eqann
        with isconv_red_raw Conv
             u.(dtype)
             (mFix_mfix_ty fk u.(dname) u.(dbody) u.(rarg) mfix1 mfix2 idx π)
             v.(dtype)
             (mFix_mfix_ty fk v.(dname) v.(dbody) v.(rarg) mfix1' mfix2' idx π')
             aux
      := {
      | Success h2 with
          isconv_fix_types fk Γ idx
            (mfix1 ++ [u]) mfix2 π _
            (mfix1' ++ [v]) mfix2' π' _
            hx _ _
        := {
        | Success h3 := yes ;
        | Error e h := no e
        } ;
      | Error e h := no e
      } ;
      | @exist false neqann := no (
        FixRargMismatch idx
          (Γ ,,, stack_context π) u mfix1 mfix2
          (Γ ,,, stack_context π') v mfix1' mfix2'
      ) };
    | @exist false eq1 := no (
        mFixRargMismatch fk idx
          (Γ ,,, stack_context π) u mfix1 mfix2
          (Γ ,,, stack_context π') v mfix1' mfix2'
      )
    } ;

    isconv_fix_types fk Γ idx mfix1 [] π h mfix1' [] π' h' hx h1 aux := yes ;

    (* TODO It might be more efficient to check the lengths first
       and then conclude this case is not possible.
    *)
    isconv_fix_types fk Γ idx mfix1 mfix2 π h mfix1' mfix2' π' h' hx h1 aux :=
      no (
        mFixMfixMismatch fk idx
          (Γ ,,, stack_context π) (mfix1 ++ mfix2)
          (Γ ,,, stack_context π') (mfix1' ++ mfix2')
      ).

  Next Obligation.
    constructor. constructor.
  Qed.
  Next Obligation.
    (* Left list is empty *)
    destruct H as [H]; inversion H.
  Qed.
  Next Obligation.
    (* Right list is empty *)
    destruct H as [H]; inversion H.
  Qed.  
  Next Obligation.
    destruct u. destruct fk. all: assumption.
  Qed.
  Next Obligation.
    destruct v. destruct fk. all: assumption.
  Qed.
  Next Obligation.
    eapply R_positionR. all: simpl.
    - destruct u. destruct fk. all: reflexivity.
    - rewrite <- app_nil_r. destruct fk.
      + eapply positionR_poscat. constructor.
      + eapply positionR_poscat. constructor.
  Qed.
  Next Obligation.
    destruct fk.
    - simpl. assumption.
    - simpl. assumption.
  Qed.
  Next Obligation.
    rewrite <- app_assoc. simpl. assumption.
  Qed.
  Next Obligation.
    rewrite <- app_assoc. simpl. assumption.
  Qed.
  Next Obligation.
    destruct hx as [hx], h1 as [h1], h2 as [h2].
    destruct hΣ as [wΣ].
    unfold zipp in h2.
    constructor.
    apply All2_app. 1: assumption.
    constructor. 2: constructor.
    change (true = eqb u.(rarg) v.(rarg)) in eq1.
    destruct (eqb_spec u.(rarg) v.(rarg)). 2: discriminate.
    symmetry in eqann.
    apply eqb_binder_annot_spec in eqann.
    split; auto.
    destruct fk; simpl in *.
    all: intuition eauto.
  Qed.
  Next Obligation.
    unshelve eapply aux. all: try eassumption.
    clear aux.
    lazymatch goal with
    | h : R _ _ ?r1 |- R _ _ ?r2 =>
      rename h into hr ;
      assert (e : r1 = r2)
    end.
    { clear hr.
      match goal with
      | |- {| wth := ?x |} = _ =>
        generalize x
      end.
      rewrite <- !app_assoc. simpl.
      intro w.
      f_equal.
      eapply proof_irrelevance.
    }
    rewrite <- e. assumption.
  Qed.
  Next Obligation.
    destruct hx as [hx], h1 as [h1], h2 as [h2], h3 as [h3].
    destruct hΣ as [wΣ].
    unfold zipp in h2.
    constructor.
    constructor. 2: assumption.
    change (true = eqb u.(rarg) v.(rarg)) in eq1.
    destruct (eqb_spec u.(rarg) v.(rarg)). 2: discriminate.
    symmetry in eqann.
    apply eqb_binder_annot_spec in eqann.
    clear eq1.
    destruct fk.
    all: intuition eauto.
  Qed.
  Next Obligation.
    (* Contrapositive of previous obligation *)
    apply h; clear h.
    destruct H as [H]; inversion H.
    constructor; assumption.
  Qed.  
  Next Obligation.
    destruct H as [H]; inversion H; destruct X as [eq_uv _].
    apply h; clear h; constructor.
    destruct fk; apply eq_uv.
  Qed.
  Next Obligation.
    destruct H as [H]; inversion H; destruct X as [_ [eq_uv eqann]].
    change (?ru =? ?rv) with (eqb ru rv) in eq1.
    symmetry in neqann.
    (* would be simpler using ssr's move/ tactic *)
    pose proof (eqb_annot_reflect (dname u) (dname v)) as r.
    now apply (ssrbool.elimF r neqann).
  Qed.
  Next Obligation.
    destruct H as [H]; inversion H; destruct X as [_ [eq_uv eqann]].
    change (?ru =? ?rv) with (eqb ru rv) in eq1.
    destruct (eqb_spec (rarg u) (rarg v)) as [|neq_uv]; [discriminate|].
    exact (neq_uv eq_uv).
  Qed.

  (* TODO MOVE *)
  Lemma conv_context_decl :
    forall Γ Δ d d',
      conv_context Σ Γ Δ ->
      conv_decls Σ Γ Δ d d' ->
      conv_context Σ (Γ ,, d) (Δ ,, d').
  Proof.
    intros Γ Δ d d' hx h.
    destruct h.
    all: constructor. all: try assumption.
    all: constructor. all: assumption.
  Qed.

  Equations isconv_fix_bodies (fk : fix_kind) (Γ : context) (idx : nat)
    (mfix1 mfix2 : mfixpoint term) (π : stack)
    (h : wtp Γ (mFix fk (mfix1 ++ mfix2) idx) π)
    (mfix1' mfix2' : mfixpoint term) (π' : stack)
    (h' : wtp Γ (mFix fk (mfix1' ++ mfix2') idx) π')
    (hx : conv_stack_ctx Γ π π')
    (h1 : ∥ All2 (fun u v => Σ ;;; Γ ,,, stack_context π ,,, fix_context_alt (map def_sig mfix1 ++ map def_sig mfix2) |- u.(dbody) = v.(dbody)) mfix1 mfix1' ∥)
    (ha : ∥ All2 (fun u v =>
                    Σ ;;; Γ ,,, stack_context π |- u.(dtype) = v.(dtype) ×
                    (u.(rarg) = v.(rarg)) * eq_binder_annot u.(dname) v.(dname)
           ) (mfix1 ++ mfix2) (mfix1' ++ mfix2') ∥)
    (aux : Aux Term Γ (mFix fk (mfix1 ++ mfix2) idx) π (mFix fk (mfix1' ++ mfix2') idx) π' h')
    : ConversionResult (∥ All2 (fun u v => Σ ;;; Γ ,,, stack_context π ,,, fix_context_alt (map def_sig mfix1 ++ map def_sig mfix2) |- u.(dbody) = v.(dbody)) mfix2 mfix2' ∥)
    by struct mfix2 :=

  isconv_fix_bodies fk Γ idx mfix1 (u :: mfix2) π h mfix1' (v :: mfix2') π' h' hx h1 ha aux
  with isconv_red_raw Conv
        u.(dbody)
        (mFix_mfix_bd fk u.(dname) u.(dtype) u.(rarg) mfix1 mfix2 idx π)
        v.(dbody)
        (mFix_mfix_bd fk v.(dname) v.(dtype) v.(rarg) mfix1' mfix2' idx π')
        aux
  := {
  | Success h2
    with isconv_fix_bodies fk Γ idx
           (mfix1 ++ [u]) mfix2 π _
           (mfix1' ++ [v]) mfix2' π' _
           hx _ _ _
    := {
    | Success h3 := yes ;
    | Error e h := no e
    } ;
  | Error e h := no e
  } ;

  isconv_fix_bodies fk Γ idx mfix1 [] π h mfix1' [] π' h' hx h1 ha aux := yes ;

  isconv_fix_bodies fk Γ idx mfix1 mfix2 π h mfix1' mfix2' π' h' hx h1 ha aux :=
    False_rect _ _.

  Next Obligation.
    constructor. constructor.
  Qed.
  Next Obligation.
    destruct h1 as [h1], ha as [ha].
    apply All2_length in h1 as e1.
    apply All2_length in ha as ea.
    rewrite !app_length in ea. simpl in ea. lia.
  Qed.
  Next Obligation.
    destruct h1 as [h1], ha as [ha].
    apply All2_length in h1 as e1.
    apply All2_length in ha as ea.
    rewrite !app_length in ea. simpl in ea. lia.
  Qed.
  Next Obligation.
    destruct u. destruct fk. all: assumption.
  Qed.
  Next Obligation.
    destruct v. destruct fk. all: assumption.
  Qed.
  Next Obligation.
    eapply R_positionR. all: simpl.
    - destruct u. destruct fk. all: reflexivity.
    - rewrite <- app_nil_r.
      destruct fk.
      + eapply positionR_poscat. constructor.
      + eapply positionR_poscat. constructor.
  Qed.
  Next Obligation.
    destruct hΣ as [wΣ], ha as [ha], hx as [hx].
    clear - wΣ ha hx. constructor.
    rewrite 2!stack_context_mFix_mfix_bd.
    change (dname u, dtype u) with (def_sig u).
    change (dname v, dtype v) with (def_sig v).
    repeat match goal with
    | |- context [ ?f ?x :: map ?f ?l ] =>
      change (f x :: map f l) with (map f (x :: l))
    end.
    rewrite <- 2!map_app.
    revert ha.
    generalize (mfix1 ++ u :: mfix2). intro Δ.
    generalize (mfix1' ++ v :: mfix2'). intro Δ'.
    intro ha.
    rewrite !app_context_assoc.
    revert hx ha.
    generalize (Γ ,,, stack_context π').
    generalize (Γ ,,, stack_context π).
    clear Γ. intros Γ Γ' hx ha.
    assert (h :
      All2
        (fun d d' => (conv Σ Γ d.2 d'.2) * eq_binder_annot d.1 d'.1)
        (map def_sig Δ) (map def_sig Δ')
    ).
    { apply All2_map. eapply All2_impl. 1: eassumption.
      intros [na ty bo ra] [na' ty' bo' ra'] [? [? ?]].
      simpl in *. split; tas.
    }
    clear ha.
    revert h.
    generalize (map def_sig Δ). clear Δ. intro Δ.
    generalize (map def_sig Δ'). clear Δ'. intro Δ'.
    intro h.
    unfold fix_context_alt.
    match goal with
    | |- conv_context _ (_ ,,, List.rev ?l) (_ ,,, List.rev ?l') =>
      assert (hi :
        All2i (fun i d d' =>
          forall Ξ Θ,
            #|Ξ| = i ->
            conv_decls Σ (Γ ,,, Ξ) Θ d d'
        ) 0 l l'
      )
    end.
    { eapply All2i_mapi.
      generalize 0 at 3. intro n.
      induction h in n |- *. 1: constructor.
      constructor. 2: eapply IHh.
      destruct r.
      intros Ξ Θ eΞ. constructor; tas.
      rewrite <- eΞ.
      eapply @weakening_conv with (Γ' := []). all: assumption.
    }
    clear h.
    revert hi.
    match goal with
    | |- context [ conv_context _ (_ ,,, List.rev ?l) (_ ,,, List.rev ?l') ] =>
      generalize l' ;
      generalize l
    end.
    clear Δ Δ'. intros Δ Δ' h.
    apply All2i_rev in h. simpl in h.
    revert h.
    rewrite <- (List.rev_length Δ).
    generalize (List.rev Δ). clear Δ. intro Δ.
    generalize (List.rev Δ'). clear Δ'. intro Δ'.
    intro h.
    set (ln := #|Δ|) in *.
    set (m := 0) in *.
    assert (e : ln - m = #|Δ|) by lia.
    clearbody ln m.
    induction h.
    - assumption.
    - simpl in *.
      eapply conv_context_decl.
      + eapply IHh. lia.
      + eapply r0. lia.
  Qed.
  Next Obligation.
    rewrite <- app_assoc. simpl. assumption.
  Qed.
  Next Obligation.
    rewrite <- app_assoc. simpl. assumption.
  Qed.
  Next Obligation.
    destruct hx as [hx], h1 as [h1], h2 as [h2], ha as [ha].
    destruct hΣ as [wΣ].
    unfold zipp in h2. (* simpl in h2. *)
    constructor.
    apply All2_app.
    - eapply All2_impl. 1: exact h1.
      simpl. intros [? ? ? ?] [? ? ? ?] hh.
      simpl in *.
      rewrite map_app. simpl.
      rewrite <- !app_assoc. simpl.
      assumption.
    - constructor. 2: constructor.
      rewrite map_app. simpl.
      rewrite <- !app_assoc. simpl.
      destruct u as [na ty bo ra], v as [na' ty' bo' ra']. simpl in *.
      unfold def_sig at 2. simpl.
      destruct fk.
      + rewrite app_context_assoc in h2. assumption.
      + rewrite app_context_assoc in h2. assumption.
  Qed.
  Next Obligation.
    destruct ha as [ha].
    constructor.
    rewrite <- !app_assoc. simpl. assumption.
  Qed.
  Next Obligation.
    unshelve eapply aux. all: try eassumption.
    clear aux.
    lazymatch goal with
    | h : R _ _ ?r1 |- R _ _ ?r2 =>
      rename h into hr ;
      assert (e : r1 = r2)
    end.
    { clear hr.
      match goal with
      | |- {| wth := ?x |} = _ =>
        generalize x
      end.
      rewrite <- !app_assoc. simpl.
      intro w.
      f_equal.
      eapply proof_irrelevance.
    }
    rewrite <- e. assumption.
  Qed.
  Next Obligation.
    destruct hx as [hx], h1 as [h1], h2 as [h2], h3 as [h3].
    destruct hΣ as [wΣ].
    unfold zipp in h2. simpl in h2.
    constructor.
    constructor.
    - destruct u as [na ty bo ra], v as [na' ty' bo' ra']. simpl in *.
      unfold def_sig at 2. simpl.
      destruct fk.
      + rewrite app_context_assoc in h2. assumption.
      + rewrite app_context_assoc in h2. assumption.
    - eapply All2_impl. 1: exact h3.
      simpl. intros [? ? ? ?] [? ? ? ?] hh.
      simpl in *.
      rewrite map_app in hh. simpl in hh.
      rewrite <- !app_assoc in hh. simpl in hh.
      assumption.
  Qed.
  Next Obligation.
    apply h; clear h.
    destruct H as [H]; inversion H; constructor.
    rewrite map_app, <- app_assoc; simpl; assumption.
  Qed.  
  Next Obligation.
    apply h; clear h.
    destruct H as [H]; inversion H; constructor.
    destruct fk; cbn -[app_context].
    all: rewrite app_context_assoc; apply X.
  Qed.  

  Equations isconv_fix (fk : fix_kind) (Γ : context)
    (mfix : mfixpoint term) (idx : nat) (π : stack)
    (h : wtp Γ (mFix fk mfix idx) π)
    (mfix' : mfixpoint term) (idx' : nat) (π' : stack)
    (h' : wtp Γ (mFix fk mfix' idx') π')
    (hx : conv_stack_ctx Γ π π')
    (ei : idx = idx')
    (aux : Aux Term Γ (mFix fk mfix idx) π (mFix fk mfix' idx') π' h')
    : ConversionResult (∥ All2 (fun u v =>
          Σ ;;; Γ ,,, stack_context π |- u.(dtype) = v.(dtype) ×
          Σ ;;; Γ ,,, stack_context π ,,, fix_context mfix |- u.(dbody) = v.(dbody) ×
          (u.(rarg) = v.(rarg)) * eq_binder_annot u.(dname) v.(dname)
      ) mfix mfix' ∥) :=

    isconv_fix fk Γ mfix idx π h mfix' idx' π' h' hx ei aux
    with
      isconv_fix_types fk Γ idx
        [] mfix π _
        [] mfix' π' _
        hx _ _
    := {
    | Success h1
      with
        isconv_fix_bodies fk Γ idx
          [] mfix π _
          [] mfix' π' _
          hx _ _ _
      := {
      | Success h2 := yes ;
      | Error e h := no e
      } ;
    | Error e h := no e
    }.

  Next Obligation.
    constructor. constructor.
  Qed.
  Next Obligation.
    unshelve eapply aux. all: eassumption.
  Qed.
  Next Obligation.
    constructor. constructor.
  Qed.
  Next Obligation.
    unshelve eapply aux. all: eassumption.
  Qed.
  Next Obligation.
    destruct h1 as [h1], h2 as [h2].
    constructor.
    rewrite fix_context_fix_context_alt.
    pose proof (All2_mix h1 h2) as h3.
    eapply All2_impl. 1: exact h3.
    intros [? ? ? ?] [? ? ? ?] ?. simpl in *.
    intuition eauto.
  Qed.
  Next Obligation.
    (* Contrapositive of previous obligation *)
    apply h; clear h.
    destruct H as [H]; constructor.
    apply (All2_impl H).
    rewrite <- fix_context_fix_context_alt. intuition.
  Qed.  
  Next Obligation.
    (* Contrapositive of pre-previous obligation *)
    apply h; clear h.
    destruct H as [H]; constructor; apply (All2_impl H).
    intuition.
  Qed.
  
  Lemma invert_type_mkApps_tProd Γ na A b args T :
    Σ;;; Γ |- mkApps (tProd na A b) args : T -> args = [].
  Proof.
    intros typ.
    destruct hΣ.
    apply PCUICValidity.inversion_mkApps in typ as (?&typ_prod&typ_args); [|easy].
    apply inversion_Prod in typ_prod as (?&?&?&?&?); [|easy].
    eapply PCUICSpine.typing_spine_strengthen in typ_args; eauto.
    clear -typ_args.
    depelim typ_args.
    - easy.
    - now apply cumul_Sort_Prod_inv in c.
  Qed.

  Lemma welltyped_zipc_tProd_appstack_nil {Γ na A B l ρ} :
    welltyped Σ Γ (zipc (tProd na A B) (appstack l ρ)) -> l = [].
  Proof. 
    intros wh.
    rewrite zipc_appstack in wh.
    zip fold in wh.
    apply welltyped_context in wh; [|easy].
    cbn in wh.
    destruct l as [|? ? _] using List.rev_ind; [easy|].
    rewrite <- mkApps_nested in wh.
    cbn in wh. destruct wh as (?&typ); auto.
    change (tApp ?h ?a) with (mkApps h [a]) in typ.
    rewrite mkApps_nested in typ.
    now apply invert_type_mkApps_tProd in typ.
  Qed.

  Lemma reduced_case_discriminee_whne Γ π ci p c brs h :
    eqb_term (reduce_term
                RedFlags.default
                Σ hΣ (Γ,,, stack_context π) c h) c = true ->
    isred_full Γ (tCase ci p c brs) π ->
    ∥whne RedFlags.default Σ (Γ,,, stack_context π) c∥.
  Proof.
    intros eq ir.
    destruct ir as (_&[wh]).
    apply eqb_term_spec in eq; tea.
    epose proof (reduce_term_complete _ _ _ _ _ _) as [wh'].
    eapply whnf_eq_term in eq; [|exact wh'].
    rewrite zipp_as_mkApps in wh.
    depelim wh; solve_discr.
    apply whne_mkApps_inv in w as [|(?&?&?&?&?&?&?&?&?)]; [|easy|easy].
    depelim w; cbn in *; try easy; solve_discr.
    apply whnf_whne_nodelta_upgrade in eq; auto using sq.
  Qed.
  
  Lemma inv_reduced_discriminees_case leq Γ π π' ci ci' p p' c c' brs brs' h h' :
    conv_stack_ctx Γ π π' ->
    true = eqb_term (reduce_term
                       RedFlags.default
                       Σ hΣ (Γ,,, stack_context π) c h) c ->
    true = eqb_term (reduce_term
                       RedFlags.default
                       Σ hΣ (Γ,,, stack_context π') c' h') c' ->
    isred_full Γ (tCase ci p c brs) π ->
    isred_full Γ (tCase ci' p' c' brs') π' ->
    conv_cum
      leq Σ (Γ,,, stack_context π)
      (zipp (tCase ci p c brs) π)
      (zipp (tCase ci' p' c' brs') π') ->
    ∥ci = ci' ×
     conv_predicate Σ (Γ,,, stack_context π) p p' ×
     Σ;;; Γ,,, stack_context π |- c = c' ×
     conv_brs Σ (Γ,,, stack_context π) brs brs' ×
     conv_terms Σ (Γ,,, stack_context π) (decompose_stack π).1 (decompose_stack π').1∥.
  Proof.
    intros [] c_is_red%eq_sym c'_is_red%eq_sym isr1 isr2 cc.
    eapply reduced_case_discriminee_whne in c_is_red as wh1; eauto.
    eapply reduced_case_discriminee_whne in c'_is_red as wh2; eauto.
    destruct hΣ, wh1 as [wh1], wh2 as [wh2].
    rewrite !zipp_as_mkApps in cc.
    eapply whne_conv_context in wh2.
    2: eapply conv_context_sym; eauto.
    apply conv_cum_mkApps_inv in cc as [(conv_case&conv_args)]; eauto using whnf_mkApps.
    eapply conv_cum_tCase_inv in conv_case; eauto.
    destruct conv_case as [(<-&?&?&?)].
    constructor; intuition auto.
  Qed.

  Lemma reduced_proj_body_whne Γ π p c h :
    true = eqb_term (reduce_term
                RedFlags.default
                Σ hΣ (Γ,,, stack_context π) c h) c ->
    isred_full Γ (tProj p c) π ->
    ∥whne RedFlags.default Σ (Γ,,, stack_context π) c∥.
  Proof.
    intros eq%eq_sym ir.
    destruct ir as (_&[wh]).
    apply eqb_term_spec in eq; tea.
    epose proof (reduce_term_complete _ _ _ _ _ _) as [wh'].
    eapply whnf_eq_term in eq; [|exact wh'].
    rewrite zipp_as_mkApps in wh.
    depelim wh; solve_discr.
    apply whne_mkApps_inv in w as [|(?&?&?&?&?&?&?&?&?)]; [|easy|easy].
    depelim w; cbn in *; try easy; solve_discr.
    apply whnf_whne_nodelta_upgrade in eq; auto using sq.
  Qed.
  
  Lemma inv_reduced_body_proj leq Γ π π' p p' c c' h h' :
    conv_stack_ctx Γ π π' ->
    true = eqb_term (reduce_term
                       RedFlags.default
                       Σ hΣ (Γ,,, stack_context π) c h) c ->
    true = eqb_term (reduce_term
                       RedFlags.default
                       Σ hΣ (Γ,,, stack_context π') c' h') c' ->
    isred_full Γ (tProj p c) π ->
    isred_full Γ (tProj p' c') π' ->
    conv_cum leq Σ (Γ,,, stack_context π) (zipp (tProj p c) π) (zipp (tProj p' c') π') ->
    ∥p = p' ×
     Σ;;; Γ,,, stack_context π |- c = c' ×
     conv_terms Σ (Γ,,, stack_context π) (decompose_stack π).1 (decompose_stack π').1∥.
  Proof.
    intros [] c_is_red c'_is_red isr1 isr2 cc.
    eapply reduced_proj_body_whne in c_is_red as wh1; eauto.
    eapply reduced_proj_body_whne in c'_is_red as wh2; eauto.
    destruct hΣ, wh1 as [wh1], wh2 as [wh2].
    rewrite !zipp_as_mkApps in cc.
    eapply whne_conv_context in wh2.
    2: eapply conv_context_sym; eauto.
    apply conv_cum_mkApps_inv in cc as [(conv_proj&conv_args)]; eauto using whnf_mkApps.
    eapply conv_cum_tProj_inv in conv_proj; eauto.
    destruct conv_proj as [(<-&?)].
    constructor; auto.
  Qed.

  Lemma inv_stuck_fixes leq Γ mfix idx π mfix' idx' π' h h' :
    conv_stack_ctx Γ π π' ->
    None = unfold_one_fix Γ mfix idx π h ->
    None = unfold_one_fix Γ mfix' idx' π' h' ->
    conv_cum leq Σ (Γ,,, stack_context π) (zipp (tFix mfix idx) π) (zipp (tFix mfix' idx') π') ->
    ∥idx = idx' ×
     All2 (fun d d' =>
             rarg d = rarg d' × eq_binder_annot d.(dname) d'.(dname) ×
             Σ;;; Γ,,, stack_context π |- dtype d = dtype d' ×
             Σ;;; Γ,,, stack_context π,,, fix_context mfix |- dbody d = dbody d')
          mfix mfix' ×
     conv_terms Σ (Γ,,, stack_context π) (decompose_stack π).1 (decompose_stack π').1∥.
  Proof.
    intros [?] uf1 uf2 cc.
    rewrite !zipp_as_mkApps in cc.
    apply unfold_one_fix_None in uf1 as [(?&?&?)].
    apply unfold_one_fix_None in uf2 as [(?&?&?)].
    destruct hΣ.
    eapply conv_cum_red_conv_inv in cc.
    2: assumption.
    2: eassumption.
    2: apply red_mkApps; [reflexivity|exact a].
    2: apply red_mkApps; [reflexivity|exact a0].
    apply conv_cum_mkApps_inv in cc as [(conv_fix&conv_args)]; auto.
    2: eapply whnf_conv_context; eauto.
    2: eapply conv_context_sym; eauto.
    apply conv_cum_tFix_inv in conv_fix as [(<-&?)]; auto.
    constructor; split; [|split]; auto.
    eapply conv_terms_red_conv; eauto.
  Qed.

  Lemma inv_stuck_cofixes leq Γ mfix idx π mfix' idx' π' :
    conv_stack_ctx Γ π π' ->
    conv_cum leq Σ (Γ,,, stack_context π) (zipp (tCoFix mfix idx) π) (zipp (tCoFix mfix' idx') π') ->
    ∥idx = idx' ×
     All2 (fun d d' =>
             rarg d = rarg d' × eq_binder_annot d.(dname) d'.(dname) ×
             Σ;;; Γ,,, stack_context π |- dtype d = dtype d' ×
             Σ;;; Γ,,, stack_context π,,, fix_context mfix |- dbody d = dbody d')
          mfix mfix' ×
     conv_terms Σ (Γ,,, stack_context π) (decompose_stack π).1 (decompose_stack π').1∥.
  Proof.
    intros [?] cc.
    rewrite !zipp_as_mkApps in cc.
    destruct hΣ.
    apply conv_cum_mkApps_inv in cc as [(conv_cofix&conv_args)]; auto.
    apply conv_cum_tCoFix_inv in conv_cofix as [(<-&?)]; auto.
    constructor; split; [|split]; auto.
  Qed.

  (* See https://github.com/coq/coq/blob/master/kernel/reduction.ml#L367 *)
  Opaque reduce_stack.
  Equations(noeqns) _isconv_prog (Γ : context) (leq : conv_pb)
            (t1 : term) (π1 : stack) (h1 : wtp Γ t1 π1)
            (t2 : term) (π2 : stack) (h2 : wtp Γ t2 π2)
            (hx : conv_stack_ctx Γ π1 π2)
            (ir1 : isred_full Γ t1 π1) (ir2 : isred_full Γ t2 π2)
            (aux : Aux Term Γ t1 π1 t2 π2 h2)
    : ConversionResult (conv_term leq Γ t1 π1 t2 π2) :=

    _isconv_prog Γ leq t1 π1 h1 t2 π2 h2 hx ir1 ir2 aux with prog_viewc t1 t2 := {
    | prog_view_App _ _ _ _ := False_rect _ _;

    | prog_view_Const c u c' u' with eq_dec c c' := {
      | left eq1 with inspect (eqb_universe_instance u u') := {
        | @exist true eq2 with isconv_args_raw leq (tConst c u) π1 (tConst c' u') π2 aux := {
          | Success h := yes ;
          (* Unfold both constants at once *)
          | Error e h with inspect (lookup_env Σ c) := {
            | @exist (Some (ConstantDecl {| cst_body := Some body |})) eq3 :=
              isconv_red leq (subst_instance u body) π1
                             (subst_instance u' body) π2 aux ;
            (* Inductive or not found *)
            | @exist _ _ := no (NotFoundConstant c)
            }
          } ;
        (* If universes are different, we unfold one of the constants *)
        | @exist false uneq_u := unfold_constants Γ leq c u π1 h1 c' u' π2 h2 _ hx aux
        } ;
      (* If the two constants are different, we unfold one of them *)
      | right uneq_c := unfold_constants Γ leq c u π1 h1 c' u' π2 h2 _ hx aux
      } ;

    | prog_view_Lambda na A1 t1 na' A2 t2
      with isconv_red_raw Conv A1 (Lambda_ty na t1 π1)
                               A2 (Lambda_ty na' t2 π2) aux := {
      | Success h with inspect (eqb_binder_annot na na') := {
        | exist true _ :=
          isconv_red leq
                     t1 (Lambda_tm na A1 π1)
                     t2 (Lambda_tm na' A2 π2) aux ;
        | exist false e := 
          no (
            LambdaNotConvertibleAnn
              (Γ ,,, stack_context π1) na A1 t1
              (Γ ,,, stack_context π2) na' A2 t2
          ) };
      | Error e h :=
        no (
          LambdaNotConvertibleTypes
            (Γ ,,, stack_context π1) na A1 t1
            (Γ ,,, stack_context π2) na' A2 t2 e
        )
      } ;

    | prog_view_Prod na A1 B1 na' A2 B2
      with isconv_red_raw Conv A1 (Prod_l na B1 π1) A2 (Prod_l na' B2 π2) aux := {
      | Success h  with inspect (eqb_binder_annot na na') := {
        | exist true _ :=
          isconv_red leq
                   B1 (Prod_r na A1 π1)
                   B2 (Prod_r na' A2 π2) aux ;
        | exist false e := 
          no (
            ProdNotConvertibleAnn
              (Γ ,,, stack_context π1) na A1 B1
              (Γ ,,, stack_context π2) na' A2 B2
          ) };
      | Error e h :=
        no (
          ProdNotConvertibleDomains
            (Γ ,,, stack_context π1) na A1 B1
            (Γ ,,, stack_context π2) na' A2 B2 e
        )
      } ;

    (* todo "case" we are missing comparisons here of the contexts of predicates *)
    | prog_view_Case ci p c brs ci' p' c' brs'
      with inspect (reduce_term RedFlags.default Σ hΣ (Γ ,,, stack_context π1) c _) := {
      | @exist cred eq1 with inspect (eqb_term cred c) := {
        | @exist true eq2 with inspect (reduce_term RedFlags.default Σ hΣ (Γ ,,, stack_context π2) c' _) := {
          | @exist cred' eq3 with inspect (eqb_term cred' c') := {
            | @exist true eq4 with inspect (eqb ci ci') := {
              | @exist true eq5 with
                  isconv_red_raw Conv
                    p.(preturn) (Case_p ci p.(pparams) p.(puinst) p.(pcontext) c brs π1)
                    p'.(preturn) (Case_p ci' p'.(pparams) p'.(puinst) p'.(pcontext) c' brs' π2)
                    aux
                := {
                | Success h1 with
                    isconv_red_raw Conv
                      c (Case ci p brs π1)
                      c' (Case ci' p' brs' π2)
                      aux
                  := {
                  | Success h2 with isconv_branches' Γ ci p c brs π1 _ ci' p' c' brs' π2 _ _ _ aux := {
                    | Success h3 with isconv_args_raw leq (tCase ci p c brs) π1 (tCase ci' p' c' brs') π2 aux := {
                      | Success h4 := yes ;
                      | Error e h := no e
                      } ;
                    | Error e h := no e
                    } ;
                  | Error e h := no e
                  } ;
                | Error e h := no e
                } ;
              | @exist false eq5 :=
                no (
                  CaseOnDifferentInd
                    (Γ ,,, stack_context π1) ci p c brs
                    (Γ ,,, stack_context π2) ci' p' c' brs'
                )
              } ;
            | @exist false eq4 :=
              isconv_red leq
                (tCase ci p c brs) π1
                (tCase ci' p' cred' brs') π2
                aux
            }
          } ;
        | @exist false eq3 :=
          isconv_red leq
            (tCase ci p cred brs) π1
            (tCase ci' p' c' brs') π2
            aux
        }
      } ;

    | prog_view_Proj p c p' c' with inspect (reduce_term RedFlags.default Σ hΣ (Γ ,,, stack_context π1) c _) := {
      | @exist cred eq1 with inspect (eqb_term cred c) := {
        | @exist true eq3 with inspect (reduce_term RedFlags.default Σ hΣ (Γ ,,, stack_context π2) c' _) := {
          | @exist cred' eq2 with inspect (eqb_term cred' c') := {
            | @exist true eq4 with inspect (eqb p p') := {
              | @exist true eq5 with isconv_red_raw Conv c (Proj p π1) c' (Proj p' π2) aux := {
                | Success h1 := isconv_args leq (tProj p c) π1 (tProj p' c') π2 aux ;
                | Error e h := no e
                } ;
              | @exist false eq5 :=
                no (
                  DistinctStuckProj
                    (Γ ,,, stack_context π1) p c
                    (Γ ,,, stack_context π2) p' c'
                )
              } ;
            | @exist false eq4 :=
              isconv_red leq
                (tProj p c) π1
                (tProj p' cred') π2
                aux
          }
        } ;
        | @exist false eq3 :=
          isconv_red leq
            (tProj p cred) π1
            (tProj p' c') π2
            aux
      }
    } ;

    | prog_view_Fix mfix idx mfix' idx'
      with inspect (unfold_one_fix Γ mfix idx π1 _) := {
      | @exist (Some (fn, θ)) eq1 with inspect (decompose_stack θ) := {
        | @exist (l', θ') eq2
          with inspect (reduce_stack RedFlags.nodelta Σ hΣ (Γ ,,, stack_context θ') fn (appstack l' ε) _) := {
          | @exist (fn', ρ) eq3 :=
            isconv_prog leq fn' (ρ +++ θ') (tFix mfix' idx') π2 aux
          }
        } ;
      | _ with inspect (unfold_one_fix Γ mfix' idx' π2 _) := {
        | @exist (Some (fn, θ)) eq1
          with inspect (decompose_stack θ) := {
          | @exist (l', θ') eq2
            with inspect (reduce_stack RedFlags.nodelta Σ hΣ (Γ ,,, stack_context θ') fn (appstack l' ε) _) := {
            | @exist (fn', ρ) eq3 :=
              isconv_prog leq (tFix mfix idx) π1 fn' (ρ +++ θ') aux
            }
          } ;
        | _ with inspect (eqb idx idx') := {
          | @exist true eq4 with isconv_fix IndFix Γ mfix idx π1 _ mfix' idx' π2 _ _ _ aux := {
            | Success h1 with isconv_args_raw leq (tFix mfix idx) π1 (tFix mfix' idx') π2 aux := {
              | Success h2 := yes ;
              | Error e h := no e
              } ;
            | Error e h := no e
            } ;
          | @exist false idx_uneq :=
            no (
              CannotUnfoldFix
                (Γ ,,, stack_context π1) mfix idx
                (Γ ,,, stack_context π2) mfix' idx'
            )
          }
        }
      } ;

    | prog_view_CoFix mfix idx mfix' idx'
      with inspect (eqb idx idx') := {
      | @exist true eq4 with isconv_fix CoIndFix Γ mfix idx π1 _ mfix' idx' π2 _ _ _ aux := {
        | Success h1 with isconv_args_raw leq (tCoFix mfix idx) π1 (tCoFix mfix' idx') π2 aux := {
          | Success h2 := yes ;
          | Error e h := no e
          } ;
        | Error e h := no e
        } ;
      | @exist false idx_uneq :=
        no (
          DistinctCoFix
            (Γ ,,, stack_context π1) mfix idx
            (Γ ,,, stack_context π2) mfix' idx'
        )
      } ;

    | prog_view_other t1 t2 h :=
      isconv_fallback leq t1 π1 t2 π2 aux
    }.

  (* tApp *)
  Next Obligation.
    destruct ir1 as [ha1 _]. discriminate ha1.
  Qed.

  (* tConst *)
  Next Obligation.
    eapply R_stateR. all: try reflexivity.
    simpl. constructor.
  Qed.
  Next Obligation.
    apply conv_cum_zipp; auto.
    destruct hΣ.
    eapply conv_conv_cum.
    constructor. constructor.
    constructor. eapply eqb_universe_instance_spec. auto.
  Qed.
  Next Obligation.
    eapply red_welltyped ; auto.
    - exact h1.
    - constructor. eapply red_zipc.
      eapply red_const. eassumption.
  Qed.
  Next Obligation.
    eapply red_welltyped ; auto.
    - exact h2.
    - constructor. eapply red_zipc.
      eapply red_const. eassumption.
  Qed.
  Next Obligation.
    eapply R_cored. simpl.
    eapply cored_zipc.
    eapply cored_const.
    eassumption.
  Qed.
  Next Obligation.
    destruct hΣ.
    etransitivity.
    - eapply red_conv_cum_l ; try assumption.
      eapply red_zipp.
      eapply red_const. eassumption.
    - etransitivity ; try eassumption.
      eapply red_conv_cum_r ; try assumption.
      eapply red_zipp.
      eapply red_const. eassumption.
  Qed.
  Next Obligation.
    apply h; cbn; clear h.
    destruct hΣ.
    eapply conv_cum_red_inv.
    - assumption.
    - apply red_zipp.
      eapply red_const; eauto.
    - apply red_zipp.
      eapply red_const; eauto.
    - exact H.
  Qed.
  Next Obligation.
    apply h; clear h.
    rewrite !zipp_as_mkApps in H.
    destruct hΣ.
    apply conv_cum_mkApps_inv in H as [(?&?)]; eauto.
    - now constructor.
    - apply whnf_mkApps.
      eapply whne_const; eauto.
    - apply whnf_mkApps.
      eapply whne_const; eauto.
  Qed.
  Next Obligation.
    apply welltyped_zipc_tConst_inv in h1 as (?&?&?).
    unfold declared_constant in *.
    congruence.
  Qed.
  Next Obligation.
    apply welltyped_zipc_tConst_inv in h1 as (?&?&?).
    unfold declared_constant in *.
    congruence.
  Qed.
  Next Obligation.
    right; split; [easy|].
    now rewrite <- uneq_u.
  Qed.

  (* tLambda *)
  Next Obligation.
    unshelve eapply R_positionR.
    - reflexivity.
    - simpl. rewrite <- app_nil_r. eapply positionR_poscat. constructor.
  Qed.
  Next Obligation.
    unshelve eapply R_positionR.
    - reflexivity.
    - simpl. rewrite <- app_nil_r. eapply positionR_poscat. constructor.
  Qed.
  Next Obligation.
    destruct hx as [hx].
    destruct h as [h].
    constructor. constructor. 1: assumption.
    constructor.
    - symmetry in wildcard7. now apply eqb_binder_annot_spec.
    - assumption.
  Qed.
  Next Obligation.
    destruct h0 as [h0].
    destruct hx as [hx].
    apply isred_full_nobeta in ir1; [|easy].
    apply isred_full_nobeta in ir2; [|easy].
    cbn in *.
    simpl_stacks.
    destruct hΣ.
    symmetry in wildcard7; apply eqb_binder_annot_spec in wildcard7.
    now eapply conv_cum_Lambda.
  Qed.
  Next Obligation.
    (* Contrapositive of previous obligation *)
    apply h; clear h.
    destruct h0 as [h0].
    destruct hx as [hx].
    apply isred_full_nobeta in ir1; [|easy].
    apply isred_full_nobeta in ir2; [|easy].
    cbn in *.
    simpl_stacks.
    destruct hΣ.
    symmetry in wildcard7; apply eqb_binder_annot_spec in wildcard7.
    apply Lambda_conv_cum_inv in H as (?&?&?); auto.
  Qed.
  Next Obligation.
    symmetry in e0.
    destruct hx as [hx].
    apply isred_full_nobeta in ir1; [|easy].
    apply isred_full_nobeta in ir2; [|easy].
    cbn in *.
    simpl_stacks.
    destruct hΣ.
    apply Lambda_conv_cum_inv in H as (?&?&?); auto.
    eapply (ssrbool.elimF (eqb_annot_reflect _ _)) in e0; auto.
  Qed.
  Next Obligation.
    (* Contrapositive of previous obligation *)
    apply h; clear h.
    destruct hx as [hx].
    apply isred_full_nobeta in ir1; [|easy].
    apply isred_full_nobeta in ir2; [|easy].
    cbn in *.
    simpl_stacks.
    destruct hΣ.
    apply Lambda_conv_cum_inv in H as (?&?&?); auto.
  Qed.

  (* tProd *)
  Next Obligation.
    unshelve eapply R_positionR.
    - reflexivity.
    - simpl. rewrite <- app_nil_r. eapply positionR_poscat. constructor.
  Qed.
  Next Obligation.
    unshelve eapply R_positionR.
    - simpl. reflexivity.
    - simpl. rewrite <- app_nil_r. eapply positionR_poscat. constructor.
  Qed.
  Next Obligation.
    destruct hx as [hx].
    destruct h as [h].
    constructor. constructor. 1: assumption.
    constructor.
    - symmetry in wildcard8.
      now apply eqb_binder_annot_spec.
    - assumption.
  Qed.
  Next Obligation.
    destruct hΣ as [wΣ].
    destruct h0 as [h0].
    destruct hx as [hx].
    cbn in *.
    apply welltyped_zipc_zipp in h1; auto.
    clear aux.
    apply welltyped_zipc_zipp in h2; auto.
    rewrite !zipp_as_mkApps in *.
    apply mkApps_Prod_nil in h1 as ->; auto.
    apply mkApps_Prod_nil in h2 as ->; auto.
    eapply conv_cum_Prod; auto.
    symmetry in wildcard8. now apply eqb_binder_annot_spec.
  Qed.
  Next Obligation.
    (* Codomains are not convertible *)
    apply h; clear h.
    symmetry in wildcard8. apply eqb_binder_annot_spec in wildcard8.
    destruct hΣ as [wΣ], h0 as [h0], hx as [hx].
    cbn in *.
    apply welltyped_zipc_zipp in h1; auto.
    clear aux.
    apply welltyped_zipc_zipp in h2; auto.
    rewrite !zipp_as_mkApps in *.
    apply mkApps_Prod_nil in h1; auto.
    apply mkApps_Prod_nil in h2; auto.
    rewrite h1, h2 in H.
    apply Prod_conv_cum_inv in H as (?&_&?); auto.
  Qed.
  Next Obligation.
    (* Annotations are not convertible *)
    destruct hΣ as [wΣ].
    destruct hx as [hx].
    cbn in *.
    apply welltyped_zipc_zipp in h1; auto.
    clear aux.
    apply welltyped_zipc_zipp in h2; auto.
    rewrite !zipp_as_mkApps in *.
    apply mkApps_Prod_nil in h1; auto.
    apply mkApps_Prod_nil in h2; auto.
    rewrite h1, h2 in H.
    apply Prod_conv_cum_inv in H as (?&?&?); auto.
    eapply (ssrbool.elimF (eqb_annot_reflect _ _)); tea.
    now unfold eqb_binder_annot.
  Qed.
  Next Obligation.
    (* Domains are not convertible *)
    apply h; clear h.
    destruct hΣ as [wΣ], hx as [hx].
    cbn in *.
    apply welltyped_zipc_zipp in h1; auto.
    clear aux.
    apply welltyped_zipc_zipp in h2; auto.
    rewrite !zipp_as_mkApps in *.
    apply mkApps_Prod_nil in h1; auto.
    apply mkApps_Prod_nil in h2; auto.
    rewrite h1, h2 in H.
    apply Prod_conv_cum_inv in H as (?&?&_); auto.
  Qed.
  (* tCase *)
  Next Obligation.
    destruct hΣ as [wΣ].
    zip fold in h1. apply welltyped_context in h1 ; auto. simpl in h1.
    destruct h1 as [T h1].
    apply inversion_Case in h1 as hh ; auto.
    destruct hh as [mdecl [idecl [indices [data cum]]]].
    epose proof (case_inversion_data_cty data).
    eexists. eassumption.
  Qed.
  Next Obligation.
    destruct hΣ as [wΣ].
    clear aux.
    zip fold in h2. apply welltyped_context in h2 ; auto. simpl in h2.
    destruct h2 as [T h2].
    apply inversion_Case in h2 as hh ; auto.
    destruct hh as [mdecl [idecl [indices [data cum]]]].
    epose proof (case_inversion_data_cty data).
    eexists. eassumption.
  Qed.
  Next Obligation.
    destruct p; exact h1.
  Qed.
  Next Obligation.
    destruct p'; exact h2.
  Qed.
  Next Obligation.
    eapply R_positionR. all: simpl.
    all:destruct p; simpl in *; try reflexivity.
    rewrite <- app_nil_r.
    eapply positionR_poscat. constructor.
  Qed.
  Next Obligation.
    todo "case".
  Qed.
  Next Obligation.
    eapply R_positionR. all: simpl.
    1: reflexivity.
    rewrite <- app_nil_r.
    eapply positionR_poscat. constructor.
  Qed.
  Next Obligation.
    change (eq_dec_to_bool ci ci') with (eqb ci ci') in eq5.
    destruct (eqb_spec ci ci'). 2: discriminate.
    assumption.
  Qed.
  Next Obligation.
    unshelve eapply R_stateR.
    all: try reflexivity.
    simpl. constructor.
  Qed.
  Next Obligation.
    apply conv_cum_zipp; auto.
    destruct h1 as [h1], h2 as [h2], h3 as [h3].
    unfold zipp in h1, h2. simpl in h1, h2.
    pose proof hΣ as wΣ. destruct wΣ.
    eapply conv_conv_cum.
    constructor.
    change (eq_dec_to_bool ci ci') with (eqb ci ci') in eq5.
    destruct (eqb_spec ci ci'). 2: discriminate.
    subst. eapply conv_Case. all: tas.
    todo "case".
  Qed.
  Next Obligation.
    apply h; clear h.
    eapply inv_reduced_discriminees_case in H as [(<-&?&?&?&?)]; eauto.
    constructor; auto.
  Qed.
  Next Obligation.
    apply h; cbn; clear h.
    eapply inv_reduced_discriminees_case in H as [(<-&?&?&?&?)]; eauto.
    constructor; auto.
  Qed.
  Next Obligation.
    apply h; cbn; clear h.
    eapply inv_reduced_discriminees_case in H as [(<-&?&?&?&?)]; eauto.
    constructor; auto.
  Qed.
  Next Obligation.
    apply h; cbn; clear h.
    eapply inv_reduced_discriminees_case in H as [(<-&?&?&?&?)]; eauto.
    constructor; auto. rewrite app_context_assoc. apply c0.
  Qed.
  Next Obligation.
    eapply inv_reduced_discriminees_case in H as [(<-&?&?&?&?)]; eauto.
    rewrite eq_dec_to_bool_refl in eq5.
    congruence.
  Qed.
  Next Obligation.
    eapply red_welltyped ; auto.
    - exact h2.
    - match goal with
      | |- context [ reduce_term ?f ?Σ ?hΣ ?Γ ?t ?h ] =>
        pose proof (reduce_term_sound f Σ hΣ Γ t h) as [hr]
      end.
      constructor.
      eapply red_zipc.
      destruct p' as [pars inst ctx ret]; cbn in *.
      set (p' := {| pparams := _ |}) in *.
      unfold p' at 2.
      change inst with (puinst p').
      eapply red_case.
      + reflexivity.
      + todo "case".
      + todo "case".
      + assumption.
      + clear.
        induction brs' ; constructor; eauto.
        split; red; reflexivity.
  Qed.
  Next Obligation.
    match goal with
    | |- context [ reduce_term ?f ?Σ ?hΣ ?Γ c' ?h ] =>
      destruct (reduce_stack_Req f Σ hΣ Γ c' ε h) as [e' | hr]
    end.
    1:{
      exfalso.
      unfold reduce_term in eq4.
      rewrite e' in eq4. cbn in eq4.
      rewrite eqb_term_refl in eq4.
      discriminate.
    }
    dependent destruction hr.
    2:{
      exfalso.
      destruct y'. simpl in H0. inversion H0. subst.
      unfold reduce_term in eq4.
      rewrite <- H2 in eq4.
      cbn in eq4.
      rewrite eqb_term_refl in eq4.
      discriminate.
    }
    unshelve eapply R_cored2.
    all: try reflexivity.
    simpl. eapply cored_zipc. eapply cored_case. assumption.
  Qed.
  Next Obligation.
    pose proof hΣ as w. destruct w.
    destruct hx as [hx].
    match type of h with
    | context [ reduce_term ?f ?Σ ?hΣ ?Γ c' ?h ] =>
      pose proof (reduce_term_sound f Σ hΣ Γ c' h) as hr
    end.
    destruct hr as [hr].
    etransitivity.
    - eassumption.
    - eapply conv_cum_conv_ctx.
      + assumption.
      + eapply red_conv_cum_r ; try assumption.
        eapply red_zipp.
        eapply red_case_c.
        eassumption.
      + eapply conv_context_sym. all: auto.
  Qed.
  Next Obligation.
    apply h; clear h.
    pose proof hΣ as [].
    destruct hx.
    epose proof (reduce_term_sound _ _ _ _ _ _) as [r].
    eapply conv_cum_red_conv_inv.
    1,2,5: eassumption.
    1: reflexivity.
    apply red_zipp.
    apply red_case_c.
    exact r.
  Qed.

  Next Obligation.
    eapply red_welltyped ; auto.
    - exact h1.
    - match goal with
      | |- context [ reduce_term ?f ?Σ ?hΣ ?Γ ?t ?h ] =>
        pose proof (reduce_term_sound f Σ hΣ Γ t h) as [hr]
      end.
      constructor.
      eapply red_zipc.
      destruct p as [pars inst ctx ret]; cbn in *.
      set (p := {| pparams := _ |}) in *.
      unfold p at 2.
      change inst with (puinst p).
      eapply red_case.
      + reflexivity.
      + todo "case".
      + todo "case".
      + assumption.
      + reflexivity.
  Qed.
  Next Obligation.
    match goal with
    | |- context [ reduce_term ?f ?Σ ?hΣ ?Γ c ?h ] =>
      destruct (reduce_stack_Req f Σ hΣ Γ c ε h) as [e' | hr]
    end.
    1:{
      exfalso.
      unfold reduce_term in eq3.
      rewrite e' in eq3. cbn in eq3.
      rewrite eqb_term_refl in eq3.
      discriminate.
    }
    dependent destruction hr.
    2:{
      exfalso.
      destruct y'. simpl in H0. inversion H0. subst.
      unfold reduce_term in eq3.
      rewrite <- H2 in eq3.
      cbn in eq3.
      rewrite eqb_term_refl in eq3.
      discriminate.
    }
    unshelve eapply R_cored.
    simpl. eapply cored_zipc. eapply cored_case. assumption.
  Qed.
  Next Obligation.
    destruct hΣ as [wΣ].
    destruct hx as [hx].
    match type of h with
    | context [ reduce_term ?f ?Σ ?hΣ ?Γ c ?h ] =>
      pose proof (reduce_term_sound f Σ hΣ Γ c h) as hr
    end.
    destruct hr as [hr].
    etransitivity.
    - eapply red_conv_cum_l ; try assumption.
      eapply red_zipp.
      eapply red_case_c.
      eassumption.
    - assumption.
  Qed.
  Next Obligation.
    apply h; clear h.
    pose proof hΣ as [].
    destruct hx.
    epose proof (reduce_term_sound _ _ _ _ _ _) as [r].
    eapply conv_cum_red_inv.
    1,4: eassumption.
    2: reflexivity.
    apply red_zipp, red_case_c, r.
  Qed.

  (* tProj *)
  Next Obligation.
    destruct hΣ as [wΣ].
    zip fold in h1. apply welltyped_context in h1 ; auto. simpl in h1.
    destruct h1 as [T h1].
    apply inversion_Proj in h1 as hh. 2: auto.
    destruct hh as [? [? [? [? [? [? [? [? ?]]]]]]]].
    eexists. eassumption.
  Qed.
  Next Obligation.
    destruct hΣ as [wΣ].
    zip fold in h2. apply welltyped_context in h2 as h2' ; auto. simpl in h2'.
    destruct h2' as [T h2'].
    apply inversion_Proj in h2' as hh. 2: auto.
    destruct hh as [? [? [? [? [? [? [? [? ?]]]]]]]].
    eexists. eassumption.
  Qed.
  Next Obligation.
    eapply R_aux_positionR. all: simpl.
    - reflexivity.
    - rewrite <- app_nil_r. apply positionR_poscat. constructor.
  Qed.
  Next Obligation.
    unshelve eapply R_stateR.
    all: try reflexivity.
    simpl. constructor.
  Qed.
  Next Obligation.
    destruct h1 as [h1].
    change (true = eqb p p') in eq5.
    destruct (eqb_spec p p'). 2: discriminate. subst.
    apply conv_cum_zipp; auto.
    eapply conv_conv_cum.
    constructor.
    eapply conv_Proj_c. assumption.
  Qed.
  Next Obligation.
    apply h; cbn; clear h.
    eapply inv_reduced_body_proj in H; eauto.
    destruct H as [(<-&?&?)].
    constructor; auto.
  Qed.
  Next Obligation.
    apply h; cbn; clear h.
    eapply inv_reduced_body_proj in H; eauto.
    destruct H as [(<-&?&?)].
    constructor; auto.
  Qed.
  Next Obligation.
    eapply inv_reduced_body_proj in H; eauto.
    destruct H as [(<-&?&?)].
    rewrite eq_prod_refl in eq5;
      eauto using eq_prod_refl, Nat.eqb_refl, eq_string_refl, eq_inductive_refl.
  Qed.
  Next Obligation.
    eapply red_welltyped ; auto.
    - exact h2.
    - match goal with
      | |- context [ reduce_term ?f ?Σ ?hΣ ?Γ ?t ?h ] =>
        pose proof (reduce_term_sound f Σ hΣ Γ t h) as [hr]
      end.
      constructor.
      eapply red_zipc.
      eapply red_proj_c.
      assumption.
  Qed.
  Next Obligation.
    match goal with
    | |- context [ reduce_term ?f ?Σ ?hΣ ?Γ c' ?h ] =>
      destruct (reduce_stack_Req f Σ hΣ Γ c' ε h) as [e' | hr]
    end.
    1:{
      exfalso.
      unfold reduce_term in eq4.
      rewrite e' in eq4. cbn in eq4.
      rewrite eqb_term_refl in eq4.
      discriminate.
    }
    dependent destruction hr.
    2:{
      exfalso.
      destruct y'. simpl in H0. inversion H0. subst.
      unfold reduce_term in eq4.
      rewrite <- H2 in eq4.
      cbn in eq4.
      rewrite eqb_term_refl in eq4.
      discriminate.
    }
    unshelve eapply R_cored2.
    all: try reflexivity.
    simpl. eapply cored_zipc. eapply cored_proj. assumption.
  Qed.
  Next Obligation.
    pose proof hΣ as w. destruct w.
    destruct hx as [hx].
    match type of h with
    | context [ reduce_term ?f ?Σ ?hΣ ?Γ c' ?h ] =>
      pose proof (reduce_term_sound f Σ hΣ Γ c' h) as hr
    end.
    destruct hr as [hr].
    etransitivity.
    - eassumption.
    - eapply conv_cum_conv_ctx.
      + assumption.
      + eapply red_conv_cum_r ; try assumption.
        eapply red_zipp.
        eapply red_proj_c.
        eassumption.
      + eapply conv_context_sym. all: auto.
  Qed.
  Next Obligation.
    apply h; cbn; clear h.
    pose proof hΣ as w. destruct w.
    destruct hx as [hx].
    match type of eq4 with
    | context [ reduce_term ?f ?Σ ?hΣ ?Γ c' ?h ] =>
      pose proof (reduce_term_sound f Σ hΣ Γ c' h) as hr
    end.
    destruct hr as [hr].
    etransitivity; [eassumption|].
    eapply conv_cum_conv_ctx; eauto.
    2: eapply conv_context_sym; eauto.
    eapply red_conv_cum_l ; try assumption.
    eapply red_zipp.
    eapply red_proj_c.
    eassumption.
  Qed.
  Next Obligation.
    eapply red_welltyped ; auto.
    - exact h1.
    - match goal with
      | |- context [ reduce_term ?f ?Σ ?hΣ ?Γ ?t ?h ] =>
        pose proof (reduce_term_sound f Σ hΣ Γ t h) as [hr]
      end.
      constructor.
      eapply red_zipc.
      eapply red_proj_c.
      assumption.
  Qed.
  Next Obligation.
    match goal with
    | |- context [ reduce_term ?f ?Σ ?hΣ ?Γ c ?h ] =>
      destruct (reduce_stack_Req f Σ hΣ Γ c ε h) as [e' | hr]
    end.
    1:{
      exfalso.
      unfold reduce_term in eq3.
      rewrite e' in eq3. cbn in eq3.
      rewrite eqb_term_refl in eq3.
      discriminate.
    }
    dependent destruction hr.
    2:{
      exfalso.
      destruct y'. simpl in H0. inversion H0. subst.
      unfold reduce_term in eq3.
      rewrite <- H2 in eq3.
      cbn in eq3.
      rewrite eqb_term_refl in eq3.
      discriminate.
    }
    unshelve eapply R_cored.
    simpl. eapply cored_zipc. eapply cored_proj. assumption.
  Qed.
  Next Obligation.
    destruct hΣ as [wΣ].
    destruct hx as [hx].
    match type of h with
    | context [ reduce_term ?f ?Σ ?hΣ ?Γ c ?h ] =>
      pose proof (reduce_term_sound f Σ hΣ Γ c h) as hr
    end.
    destruct hr as [hr].
    etransitivity.
    - eapply red_conv_cum_l ; try assumption.
      eapply red_zipp.
      eapply red_proj_c.
      eassumption.
    - assumption.
  Qed.
  Next Obligation.
    apply h; cbn; clear h.
    destruct hΣ as [wΣ].
    destruct hx as [hx].
    match type of eq3 with
    | context [ reduce_term ?f ?Σ ?hΣ ?Γ c ?h ] =>
      pose proof (reduce_term_sound f Σ hΣ Γ c h) as hr
    end.
    destruct hr as [hr].
    etransitivity.
    - eapply red_conv_cum_r ; try assumption.
      eapply red_zipp.
      eapply red_proj_c.
      eassumption.
    - assumption.
  Qed.
  
  (* tFix *)
  Next Obligation.
    cbn. rewrite zipc_appstack. cbn.
    apply unfold_one_fix_red_zipp in eq1 as r.
    apply unfold_one_fix_decompose in eq1 as d.
    rewrite <- eq2 in d. simpl in d.
    unfold zipp in r.
    rewrite <- eq2 in r.
    case_eq (decompose_stack π1). intros l1 ρ1 e1.
    rewrite e1 in r.
    rewrite e1 in d. simpl in d. subst.
    apply welltyped_zipc_zipp in h1 as hh1. 2: auto.
    pose proof (decompose_stack_eq _ _ _ e1). subst.
    unfold zipp in hh1. rewrite e1 in hh1.
    pose proof (red_welltyped _ hΣ hh1 r) as hh.
    rewrite stack_context_appstack in hh.
    assumption.
  Qed.
  Next Obligation.
    apply unfold_one_fix_red in eq1 as r1.
    apply unfold_one_fix_decompose in eq1 as d1.
    reduce_stack_facts.
    simpl_stacks.
    destruct r1 as [r1].
    eapply red_welltyped.
    1: eauto.
    1: exact h1.
    constructor.
    etransitivity.
    2: { apply red_zipc.
         rewrite stack_context_decompose.
         exact r. }
    simpl_stacks.
    eassumption.
  Qed.
  Next Obligation.
    apply unfold_one_fix_cored in eq1 as r1.
    apply unfold_one_fix_decompose in eq1 as d1.
    match type of eq3 with
    | _ = reduce_stack ?f ?Σ ?hΣ ?Γ ?t ?π ?h =>
      destruct (reduce_stack_sound f Σ hΣ Γ t π h) as [r2]
    end.
    rewrite <- eq3 in r2.
    eapply R_cored. simpl.
    eapply red_cored_cored ; try eassumption.
    apply red_context_zip in r2. cbn in r2.
    rewrite zipc_stack_cat.
    pose proof (decompose_stack_eq _ _ _ (eq_sym eq2)). subst.
    rewrite zipc_appstack in r2. cbn in r2.
    rewrite zipc_appstack.
    assumption.
  Qed.
  Next Obligation.
    apply unfold_one_fix_decompose in eq1 as d1.
    reduce_stack_facts.
    now simpl_stacks.
  Qed.
  Next Obligation.
    simpl_reduce_stack.
    specialize (isr eq_refl) as (?&_).
    split; [easy|].
    cbn in *.
    now simpl_stacks.
  Qed.
  Next Obligation.
    apply unfold_one_fix_red_zipp in eq1 as r1.
    apply unfold_one_fix_decompose in eq1 as d1.
    reduce_stack_facts.
    simpl_reduce_stack.
    destruct hΣ, r1 as [r1].
    eapply conv_cum_trans; auto.
    2: exact h.
    eapply red_conv_cum_l.
    etransitivity; eauto.
  Qed.
  Next Obligation.
    apply h; clear h.
    apply unfold_one_fix_red_zipp in eq1 as r1.
    apply unfold_one_fix_decompose in eq1 as d1.
    reduce_stack_facts.
    simpl_reduce_stack.
    destruct hΣ, r1 as [r1].
    eapply conv_cum_red_inv.
    1: auto.
    2: reflexivity.
    2: exact H.
    etransitivity; eauto.
  Qed.
  Next Obligation.
    apply unfold_one_fix_red_zipp in eq1 as r.
    apply unfold_one_fix_decompose in eq1 as d.
    clear aux eq1.
    apply welltyped_zipc_zipp in h2; auto.
    cbn in *.
    simpl_stacks.
    eapply red_welltyped; eauto.
  Qed.
  Next Obligation.
    apply unfold_one_fix_red in eq1 as r1.
    apply unfold_one_fix_decompose in eq1 as d1.
    match type of eq3 with
    | _ = reduce_stack ?f ?Σ ?hΣ ?Γ ?t ?π ?h =>
      destruct (reduce_stack_sound f Σ hΣ Γ t π h) as [r2] ;
      pose proof (reduce_stack_decompose RedFlags.nodelta _ hΣ _ _ _ h) as d2 ;
      pose proof (reduce_stack_context f Σ hΣ Γ t π h) as c2
    end.
    rewrite <- eq3 in r2. cbn in r2. rewrite zipc_appstack in r2. cbn in r2.
    rewrite <- eq3 in d2. cbn in d2. rewrite decompose_stack_appstack in d2.
    cbn in d2.
    rewrite <- eq3 in c2. cbn in c2. rewrite stack_context_appstack in c2.
    cbn in c2.
    case_eq (decompose_stack ρ). intros l ξ e.
    rewrite e in d2. cbn in d2. subst.
    pose proof (red_welltyped _ hΣ h2 r1) as hh.
    apply red_context_zip in r2.
    pose proof (decompose_stack_eq _ _ _ (eq_sym eq2)). subst.
    rewrite zipc_appstack in hh. cbn in r2.
    pose proof (red_welltyped _ hΣ hh (sq r2)) as hh'.
    rewrite zipc_stack_cat. assumption.
  Qed.
  Next Obligation.
    apply unfold_one_fix_cored in eq1 as r1.
    apply unfold_one_fix_decompose in eq1 as d1.
    match type of eq3 with
    | _ = reduce_stack ?f ?Σ ?hΣ ?Γ ?t ?π ?h =>
      destruct (reduce_stack_sound f Σ hΣ Γ t π h) as [r2]
    end.
    rewrite <- eq3 in r2.
    eapply R_cored2. all: try reflexivity. simpl.
    eapply red_cored_cored ; try eassumption.
    cbn in r2.
    rewrite zipc_stack_cat.
    pose proof (decompose_stack_eq _ _ _ (eq_sym eq2)). subst.
    rewrite zipc_appstack in r2. cbn in r2.
    rewrite zipc_appstack.
    do 2 zip fold. eapply red_context_zip.
    assumption.
  Qed.
  Next Obligation.
    apply unfold_one_fix_decompose in eq1 as d1.
    match type of eq3 with
    | _ = reduce_stack ?f ?Σ ?hΣ ?Γ ?t ?π ?h =>
      pose proof (reduce_stack_decompose RedFlags.nodelta _ hΣ _ _ _ h) as d2
    end.
    rewrite <- eq3 in d2. cbn in d2.
     rewrite decompose_stack_appstack in d2.
    cbn in d2.
    rewrite <- eq2 in d1. simpl in d1.
    case_eq (decompose_stack π2). intros args2 ρ2 e2.
    rewrite e2 in d1. simpl in d1. subst.
    case_eq (decompose_stack ρ). intros l ξ e'.
    rewrite e' in d2. simpl in d2. subst.
    apply decompose_stack_eq in e' as ?. subst.
    rewrite stack_cat_appstack.
    rewrite stack_context_appstack.
    apply decompose_stack_eq in e2 as ?. subst.
    clear eq3.
    rewrite stack_context_appstack in hx.
    assumption.
  Qed.
  Next Obligation.
    simpl_reduce_stack.
    specialize (isr eq_refl) as (?&_).
    split; [easy|].
    simpl_stacks.
    eauto.
  Qed.
  Next Obligation.
    apply unfold_one_fix_red_zipp in eq1 as r1.
    apply unfold_one_fix_decompose in eq1 as d1.
    reduce_stack_facts.
    simpl_reduce_stack.
    destruct r1 as [r1].
    destruct hΣ, hx.
    eapply conv_cum_red_conv.
    1,2,5: eauto.
    1: reflexivity.
    etransitivity; eauto.
  Qed.
  Next Obligation.
    apply h; clear h.
    apply unfold_one_fix_red_zipp in eq1 as r1.
    apply unfold_one_fix_decompose in eq1 as d1.
    reduce_stack_facts.
    simpl_reduce_stack.
    destruct r1 as [r1].
    destruct hΣ, hx.
    eapply conv_cum_red_conv_inv.
    1,2,5: eauto.
    1: reflexivity.
    etransitivity; eauto.
  Qed.
  Next Obligation.
    change (true = eqb idx idx') in eq4.
    destruct (eqb_spec idx idx'). 2: discriminate.
    assumption.
  Qed.
  Next Obligation.
    eapply R_stateR.
    all: simpl.
    all: try reflexivity.
    constructor.
  Qed.
  Next Obligation.
    apply conv_cum_zipp; auto.
    destruct h1 as [h1].
    destruct hΣ.
    eapply conv_conv_cum_l.
    change (true = eqb idx idx') in eq4.
    destruct (eqb_spec idx idx'). 2: discriminate.
    subst.
    eapply conv_Fix. all: assumption.
  Qed.
  Next Obligation.
    apply h; clear h.
    eapply inv_stuck_fixes in H as [(<-&?&?)]; eauto.
    constructor; auto.
  Qed.
  Next Obligation.
    apply h; clear h.
    eapply inv_stuck_fixes in H as [(<-&?&?)]; eauto.
    constructor; auto.
    eapply All2_impl; eauto.
    cbn; intros; easy.
  Qed.
  Next Obligation.
    eapply inv_stuck_fixes in H as [(<-&?&?)]; eauto.
    rewrite Nat.eqb_refl in idx_uneq.
    congruence.
  Qed.

  (* tCoFix *)
  Next Obligation.
    change (true = eqb idx idx') in eq4.
    destruct (eqb_spec idx idx'). 2: discriminate.
    assumption.
  Qed.
  Next Obligation.
    eapply R_stateR.
    all: simpl.
    all: try reflexivity.
    constructor.
  Qed.
  Next Obligation.
    apply conv_cum_zipp; auto.
    destruct h1 as [h1].
    destruct hΣ.
    eapply conv_conv_cum_l.
    change (true = eqb idx idx') in eq4.
    destruct (eqb_spec idx idx'). 2: discriminate.
    subst.
    eapply conv_CoFix. all: assumption.
  Qed.
  Next Obligation.
    apply h; clear h.
    eapply inv_stuck_cofixes in H as [(<-&?&?)]; eauto.
    constructor; auto.
  Qed.
  Next Obligation.
    apply h; clear h.
    eapply inv_stuck_cofixes in H as [(<-&?&?)]; eauto.
    constructor; auto.
    eapply All2_impl; eauto.
    cbn; intros; easy.
  Qed.
  Next Obligation.
    eapply inv_stuck_cofixes in H as [(<-&?&?)]; eauto.
    rewrite Nat.eqb_refl in idx_uneq.
    congruence.
  Qed.

  (* Fallback *)
  Next Obligation.
    unshelve eapply R_stateR.
    all: try reflexivity.
    simpl. constructor.
  Qed.

  Definition Aux' Γ t1 args1 l1 π1 t2 π2 h2 :=
    forall u1 u2 ca1 a1 ρ2
      (h1' : wtp Γ u1 (coApp (mkApps t1 ca1) (appstack a1 π1)))
      (h2' : wtp Γ u2 ρ2),
      let x :=
        mkpack Γ Reduction u1 (coApp (mkApps t1 ca1) (appstack a1 π1)) u2 ρ2 h2'
      in
      let y := mkpack Γ Args (mkApps t1 args1) (appstack l1 π1) t2 π2 h2 in
      (S #|ca1| + #|a1| = #|args1| + #|l1|)%nat ->
      pzt x = pzt y /\
      positionR (` (pps1 x)) (` (pps1 y)) ->
      Ret Reduction Γ u1 (coApp (mkApps t1 ca1) (appstack a1 π1)) u2 ρ2.

  Equations(noeqns) _isconv_args' (leq : conv_pb) (Γ : context)
            (t1 : term) (args1 : list term)
            (l1 : list term) (π1 : stack)
            (h1 : wtp Γ (mkApps t1 args1) (appstack l1 π1))
            (hπ1 : isStackApp π1 = false)
            (t2 : term)
            (l2 : list term) (π2 : stack)
            (h2 : wtp Γ t2 (appstack l2 π2))
            (hπ2 : isStackApp π2 = false)
            (hx : conv_stack_ctx Γ π1 π2)
            (aux : Aux' Γ t1 args1 l1 π1 t2 (appstack l2 π2) h2)
    : ConversionResult (∥conv_terms Σ (Γ,,, stack_context π1) l1 l2∥) by struct l1 :=
    _isconv_args' leq Γ t1 args1 (u1 :: l1) π1 h1 hπ1 t2 (u2 :: l2) π2 h2 hπ2 hx aux
    with aux u1 u2 args1 l1 (coApp t2 (appstack l2 π2)) _ _ _ _ Conv _ I I I := {
    | Success H1 with _isconv_args' leq Γ t1 (args1 ++ [u1]) l1 π1 _ _ (tApp t2 u2) l2 π2 _ _ _ _ := {
      | Success H2 := yes ;
      | Error e herr :=
        no (
          StackTailError
            leq
            (Γ ,,, stack_context π1) t1 args1 u1 l1
            (Γ ,,, stack_context π2) t2 u2 l2 e
        )
      } ;
    | Error e herr :=
      no (
        StackHeadError
          leq
          (Γ ,,, stack_context π1) t1 args1 u1 l1
          (Γ ,,, stack_context π2) t2 u2 l2 e
      )
    } ;

    _isconv_args' leq Γ t1 args1 [] π1 h1 hπ1 t2 [] π2 h2 hπ2 hx aux := yes ;

    _isconv_args' leq Γ t1 args1 l1 π1 h1 hπ1 t2 l2 π2 h2 hπ2 hx aux :=
      no (
        StackMismatch
          (Γ ,,, stack_context π1) t1 args1 l1
          (Γ ,,, stack_context π2) t2 l2
      ).
  Next Obligation.
    constructor; constructor.
  Defined.
  Next Obligation.
    destruct H as [H]; depelim H.
  Qed.
  Next Obligation.
    destruct H as [H]; depelim H.
  Qed.
  Next Obligation.
    split. 1: reflexivity.
    eapply positionR_poscat. constructor.
  Defined.
  Next Obligation.
    rewrite 2!stack_context_appstack.
    assumption.
  Qed.
  Next Obligation.
    rewrite <- mkApps_nested. assumption.
  Defined.
  Next Obligation.
    simpl in H0. destruct H0 as [eq hp].
    rewrite app_length in H. cbn in H.
    eapply aux. all: auto.
    - cbn. lia.
    - instantiate (1 := h2'). simpl. split.
      + rewrite <- mkApps_nested in eq. assumption.
      + subst x y.
        rewrite 2!stack_position_appstack.
        rewrite <- !app_assoc. apply positionR_poscat.
        assert (h' : forall n m, positionR (list_make n app_l ++ [app_r]) (list_make m app_l)).
        { clear. intro n. induction n ; intro m.
          - destruct m ; constructor.
          - destruct m.
            + constructor.
            + cbn. constructor. apply IHn.
        }
        rewrite <- list_make_app_r.
        apply (h' #|a1| (S #|l1|)).
  Defined.
  Next Obligation.
    destruct hΣ as [wΣ].
    destruct H1 as [H1].
    unfold zipp. simpl.
    unfold zipp in H1. simpl in H1.
    rewrite stack_context_appstack in H1.
    destruct H2 as [H2].
    constructor; constructor; auto.
  Defined.
  Next Obligation.
    apply herr; clear herr.
    destruct H as [H]; depelim H.
    constructor; auto.
  Qed.
  Next Obligation.
    apply herr; cbn; clear herr.
    destruct H as [H]; depelim H.
    rewrite stack_context_appstack.
    constructor; auto.
  Qed.

  Equations(noeqns) _isconv_args (leq : conv_pb) (Γ : context)
           (t1 : term) (π1 : stack) (h1 : wtp Γ t1 π1)
           (t2 : term) (π2 : stack) (h2 : wtp Γ t2 π2)
           (hx : conv_stack_ctx Γ π1 π2)
           (aux : Aux Args Γ t1 π1 t2 π2 h2)
    : ConversionResult (∥conv_terms Σ (Γ,,, stack_context π1)
                         (decompose_stack π1).1
                         (decompose_stack π2).1∥) :=
    _isconv_args leq Γ t1 π1 h1 t2 π2 h2 hx aux with inspect (decompose_stack π1) := {
    | @exist (l1, θ1) eq1 with inspect (decompose_stack π2) := {
      | @exist (l2, θ2) eq2 with _isconv_args' leq Γ t1 [] l1 θ1 _ _ t2 l2 θ2 _ _ _ _ := {
        | Success h := yes ;
        | Error e h := no e
        }
      }
    }.
  Next Obligation.
    pose proof (decompose_stack_eq _ _ _ (eq_sym eq1)). subst.
    assumption.
  Qed.
  Next Obligation.
    eapply decompose_stack_noStackApp. eauto.
  Qed.
  Next Obligation.
    pose proof (decompose_stack_eq _ _ _ (eq_sym eq2)). subst.
    assumption.
  Qed.
  Next Obligation.
    eapply decompose_stack_noStackApp. eauto.
  Qed.
  Next Obligation.
    pose proof (decompose_stack_eq _ _ _ (eq_sym eq1)). subst.
    pose proof (decompose_stack_eq _ _ _ (eq_sym eq2)). subst.
    rewrite 2!stack_context_appstack in hx.
    assumption.
  Qed.
  Next Obligation.
    specialize (aux Reduction) as h. cbn in h.
    eapply h. all: auto.
    pose proof (decompose_stack_eq _ _ _ (eq_sym eq1)). subst.
    instantiate (1 := h2').
    simpl in H0. destruct H0 as [eq hp].
    unshelve eapply R_positionR. 2: assumption.
    simpl. rewrite eq. reflexivity.
  Qed.
  (* The obligation tactic wipes out a useful hypothesis here? *)
  Obligation Tactic := idtac.
  Next Obligation.
    intros; cbn in *.
    rewrite <- (stack_context_decompose π1).
    rewrite <- eq1, <- eq2.
    auto.
  Qed.
  Next Obligation.
    intros; cbn in *.
    rewrite <- (stack_context_decompose π1).
    rewrite <- eq1, <- eq2.
    auto.
  Qed.
  Obligation Tactic :=
    Tactics.program_simplify; CoreTactics.equations_simpl; try Tactics.program_solve_wf.
  
  Equations unfold_one_case (Γ : context) (ci : case_info)
            (p : predicate term) (c : term) (brs : list (branch term))
            (h : welltyped Σ Γ (tCase ci p c brs)) : option term :=
    unfold_one_case Γ ci p c brs h
    with inspect (reduce_stack RedFlags.default Σ hΣ Γ c ε _) := {
    | @exist (cred, ρ) eq with cc_viewc cred := {
      | ccview_construct ind' n ui with inspect (decompose_stack ρ) := {
        | @exist (args, ξ) eq' with inspect (nth_error brs n) := {
          | exist (Some br) eqbr := Some (iota_red ci.(ci_npar) args br) ;
          | exist None eqbr := False_rect _ _ }
        } ;
      | ccview_cofix mfix idx with inspect (unfold_cofix mfix idx) := {
        | @exist (Some (narg, fn)) eq2 with inspect (decompose_stack ρ) := {
          | @exist (args, ξ) eq' := Some (tCase ci p (mkApps fn args) brs)
          } ;
        | @exist None eq2 := False_rect _ _
        } ;
      | ccview_other t _ := None
      }
    }.
  Next Obligation.
    destruct hΣ as [wΣ].
    cbn. destruct h as [T h].
    apply inversion_Case in h ; auto.
    destruct h as [mdecl [idecl [indices [data cum]]]].
    epose proof (case_inversion_data_cty data).
    eexists. eassumption.
  Qed.
  Next Obligation.
    simpl_reduce_stack.
    destruct hΣ.
    assert (r' : ∥ red Σ Γ (tCase ci p c brs)
      (tCase ci p (mkApps (tConstruct ind' n ui) (decompose_stack ρ).1) brs) ∥).
    { constructor. eapply red_case_c. eassumption. }
    pose proof (red_welltyped _ hΣ h r') as h'.
    destruct h'.
    apply inversion_Case in X0 as [mdecl [idecl [indices [data cum]]]]; auto.
    destruct data.
    todo "case". (* show in SafeLemmata that if the case is well-typed the the branch must exist *)
  Qed.
  
  Next Obligation.
    exfalso.
    simpl_reduce_stack.
    destruct h as (?&typ); auto.
    destruct hΣ.
    apply inversion_Case in typ as [mdecl [idecl [indices [data cum]]]]; auto.
    pose proof (case_inversion_data_cty data) as t0.
    eapply PCUICSR.subject_reduction in t0; eauto.
    apply PCUICValidity.inversion_mkApps in t0 as (?&?&?); auto.
    apply inversion_CoFix in t as (?&?&?&?&?&?&?); auto.
    unfold unfold_cofix in eq2.
    rewrite e in eq2.
    congruence.
  Qed.

  Lemma unfold_one_case_cored :
    forall Γ ci p c brs h t,
      Some t = unfold_one_case Γ ci p c brs h ->
      cored Σ Γ t (tCase ci p c brs).
  Proof.
    intros Γ ci p c brs h t e.
    revert e.
    funelim (unfold_one_case Γ ci p c brs h).
    all: intros eq ; noconf eq.
    - clear H H0 H1.
      simpl_reduce_stack.
      assert (r' : ∥ red Σ Γ (tCase ci p c brs)
          (tCase ci p (mkApps (tConstruct ind n ui) (decompose_stack s).1) brs) ∥).
      { constructor. eapply red_case_c. eassumption. }
      pose proof (red_welltyped _ hΣ h r') as h'.
      eapply Case_Construct_ind_eq in h' ; eauto. subst.
      eapply cored_red_cored.
      + constructor. eapply red_iota. 1: now symmetry.
        todo "cases". (* from welltyped case*)
      + eapply red_case_c. eassumption.
    - match type of eq with
      | _ = False_rect _ ?f => destruct f
      end.
    - clear H H0. revert eq.
      destruct unfold_one_case_obligations_obligation_3.
    - clear H H0 H1.
      simpl_reduce_stack.
      assert (r' : ∥ red Σ Γ (tCase ci p c brs)
                     (tCase ci p (mkApps (tCoFix mfix idx) (decompose_stack s).1) brs) ∥).
      { constructor. eapply red_case_c. eassumption. }
      pose proof (red_welltyped _ hΣ h r') as h'.
      eapply cored_red_cored.
      + constructor. eapply red_cofix_case. eauto.
      + eapply red_case_c. eassumption.
  Qed.
  
  Lemma unfold_one_case_None Γ ci p c brs h :
    None = unfold_one_case Γ ci p c brs h ->
    ∥∑ c', red Σ Γ c c' × whne RedFlags.default Σ Γ c'∥.
  Proof.
    funelim (unfold_one_case Γ ci p c brs h); intros [=].
    - clear H.
      simpl_reduce_stack.
      destruct h as (?&typ); auto.
      destruct hΣ, w.
      constructor; exists (mkApps t0 (decompose_stack s).1).
      split; [easy|].
      specialize (isr eq_refl) as (noapp&_).
      eapply PCUICSR.subject_reduction in typ.
      2: eauto.
      2: eapply red_case_c; eauto.
      eapply whnf_case_arg_whne; eauto.
      now destruct t0.
    - match type of H3 with
      | _ = False_rect _ ?f => destruct f
      end.
    - match type of H2 with
      | _ = False_rect _ ?f => destruct f
      end.
  Qed.

  Equations unfold_one_proj (Γ : context) (p : projection) (c : term)
            (h : welltyped Σ Γ (tProj p c)) : option term :=

    unfold_one_proj Γ p c h with p := {
    | (i, pars, narg) with inspect (reduce_stack RedFlags.default Σ hΣ Γ c ε _) := {
      | @exist (cred, ρ) eq with cc0_viewc cred := {
        | cc0view_construct ind' ui with inspect (decompose_stack ρ) := {
          | @exist (args, ξ) eq' with inspect (nth_error args (pars + narg)) := {
            | @exist (Some arg) eq2 := Some arg ;
            | @exist None eq2 := False_rect _ _
            }
          } ;
        | cc0view_cofix mfix idx with inspect (decompose_stack ρ) := {
          | @exist (args, ξ) eq' with inspect (unfold_cofix mfix idx) := {
            | @exist (Some (narg, fn)) eq2 :=
              Some (tProj (i, pars, narg) (mkApps fn args)) ;
            | @exist None eq2 := False_rect _ _
            }
          } ;
        | cc0view_other t _ := None
        }
      }
    }.
  Next Obligation.
    destruct hΣ as [wΣ].
    cbn. destruct h as [T h].
    apply inversion_Proj in h ; auto.
    destruct h as [uni [mdecl [idecl [pdecl [args' [? [? [? ?]]]]]]]].
    eexists. eassumption.
  Qed.
  Next Obligation.
    simpl_reduce_stack.
    destruct h as (?&typ); auto.
    destruct hΣ.
    eapply PCUICSR.subject_reduction in typ.
    2: auto.
    2: apply red_proj_c; eassumption.
    apply PCUICInductiveInversion.invert_Proj_Construct in typ as (<-&_&?); auto.
    apply eq_sym, nth_error_None in eq2.
    lia.
  Qed.
  Next Obligation.
    simpl_reduce_stack.
    destruct h as (?&typ); auto.
    destruct hΣ.
    apply inversion_Proj in typ as (?&?&?&?&?&?&?&?&?); auto.
    eapply PCUICSR.subject_reduction in t; eauto.
    apply PCUICValidity.inversion_mkApps in t as (?&?&?); auto.
    apply inversion_CoFix in t as (?&?&?&?&?&?&?); auto.
    unfold unfold_cofix in eq2.
    rewrite e0 in eq2.
    congruence.
  Qed.

  Lemma unfold_one_proj_cored :
    forall Γ p c h t,
      Some t = unfold_one_proj Γ p c h ->
      cored Σ Γ t (tProj p c).
  Proof.
    intros Γ p c h t e.
    revert e.
    funelim (unfold_one_proj Γ p c h).
    all: intros eq ; noconf eq.
    - clear H H0 H1.
      simpl_reduce_stack.
      pose proof (red_proj_c (i, n0, n) _ _ r) as r'.
      pose proof (red_welltyped _ hΣ h (sq r')) as h'.
      apply Proj_Construct_ind_eq in h' ; auto. subst.
      eapply cored_red_cored.
      + constructor. eapply red_proj. eauto.
      + eapply red_proj_c. eassumption.
    - match type of eq with
      | _ = False_rect _ ?f => destruct f
      end.
    - clear H H0 H1.
      simpl_reduce_stack.
      pose proof (red_proj_c (i, n0, n) _ _ r) as r'.
      pose proof (red_welltyped _ hΣ h (sq r')) as h'.
      eapply cored_red_cored.
      + constructor. eapply red_cofix_proj. eauto.
      + eapply red_proj_c. eassumption.
    - match type of eq with
      | _ = False_rect _ ?f => destruct f
      end.
  Qed.

  Lemma unfold_one_proj_None Γ p c h :
    None = unfold_one_proj Γ p c h ->
    ∥∑ c', red Σ Γ c c' × whne RedFlags.default Σ Γ c'∥.
  Proof.
    funelim (unfold_one_proj Γ p c h); intros [=].
    - clear H.
      simpl_reduce_stack.
      destruct hΣ, w.
      destruct h as (?&typ); auto.
      constructor; exists (mkApps t0 (decompose_stack s).1).
      split; [easy|].
      specialize (isr eq_refl) as (noapp&_).
      eapply PCUICSR.subject_reduction in typ.
      2: eauto.
      2: eapply red_proj_c; eauto.
      eapply whnf_proj_arg_whne; eauto.
      now destruct t0.
    - match type of H3 with
      | _ = False_rect _ ?f => destruct f
      end.
    - match type of H3 with
      | _ = False_rect _ ?f => destruct f
      end.
  Qed.

  Equations reducible_head (Γ : context) (t : term) (π : stack)
            (h : wtp Γ t π)
    : option (term × stack) :=

    reducible_head Γ (tFix mfix idx) π h := unfold_one_fix Γ mfix idx π h ;

    reducible_head Γ (tCase ci p c brs) π h
    with inspect (unfold_one_case (Γ ,,, stack_context π) ci p c brs _) := {
    | @exist (Some t) eq :=Some (t, π) ;
    | @exist None _ := None
    } ;

    reducible_head Γ (tProj p c) π h
    with inspect (unfold_one_proj (Γ ,,, stack_context π) p c _) := {
    | @exist (Some t) eq := Some (t, π) ;
    | @exist None _ := None
    } ;

    reducible_head Γ (tConst c u) π h
    with inspect (lookup_env Σ c) := {
    | @exist (Some (ConstantDecl {| cst_body := Some body |})) eq :=
      Some (subst_instance u body, π) ;
    | @exist _ _ := None
    } ;

    reducible_head Γ _ π h := None.
  Next Obligation.
    zip fold in h.
    apply welltyped_context in h ; auto.
  Qed.
  Next Obligation.
    zip fold in h.
    apply welltyped_context in h ; auto.
  Qed.

  Lemma reducible_head_red_zipp :
    forall Γ t π h fn ξ,
      Some (fn, ξ) = reducible_head Γ t π h ->
      ∥ red (fst Σ) (Γ ,,, stack_context π) (zipp t π) (zipp fn ξ) ∥.
  Proof.
    intros Γ t π h fn ξ e.
    revert e.
    funelim (reducible_head Γ t π h).
    all: intro ee ; noconf ee.
    - eapply unfold_one_fix_red_zipp. eassumption.
    - constructor. simpl_stacks. 
      eapply red_mkApps_f.
      eapply trans_red.
      + reflexivity.
      + eapply red_delta.
        * unfold declared_constant. eauto.
        * reflexivity.
    - apply unfold_one_case_cored in e as r. apply cored_red in r.
      destruct r as [r].
      constructor. simpl_stacks.
      eapply red_mkApps_f.
      assumption.
    - apply unfold_one_proj_cored in e as r. apply cored_red in r.
      destruct r as [r].
      constructor. simpl_stacks.
      eapply red_mkApps_f.
      assumption.
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
    - constructor. unfold zippx.
      case_eq (decompose_stack π). intros l s eq.
      eapply red_it_mkLambda_or_LetIn. eapply red_mkApps_f.
      eapply trans_red.
      + reflexivity.
      + eapply red_delta.
        * unfold declared_constant. eauto.
        * reflexivity.
    - apply unfold_one_case_cored in e as r. apply cored_red in r.
      destruct r as [r].
      constructor. unfold zippx.
      case_eq (decompose_stack π). intros l s e'.
      eapply red_it_mkLambda_or_LetIn. eapply red_mkApps_f.
      apply decompose_stack_eq in e'. subst.
      rewrite stack_context_appstack in r. assumption.
    - apply unfold_one_proj_cored in e as r. apply cored_red in r.
      destruct r as [r].
      constructor. unfold zippx.
      case_eq (decompose_stack π). intros l s e'.
      eapply red_it_mkLambda_or_LetIn. eapply red_mkApps_f.
      apply decompose_stack_eq in e'. subst.
      rewrite stack_context_appstack in r. assumption.
  Qed.

  Lemma reducible_head_cored :
    forall Γ t π h fn ξ,
      Some (fn, ξ) = reducible_head Γ t π h ->
      cored Σ Γ (zipc fn ξ) (zipc t π).
  Proof.
    intros Γ t π h fn ξ e.
    revert e.
    funelim (reducible_head Γ t π h).
    all: intro ee ; noconf ee.
    - eapply unfold_one_fix_cored. eassumption.
    - repeat zip fold. eapply cored_context.
      constructor. eapply red_delta.
      + unfold declared_constant. eauto.
      + reflexivity.
    - repeat zip fold. eapply cored_context.
      eapply unfold_one_case_cored. eassumption.
    - repeat zip fold. eapply cored_context.
      eapply unfold_one_proj_cored. eassumption.
  Qed.

  Lemma reducible_head_decompose :
    forall Γ t π h fn ξ,
      Some (fn, ξ) = reducible_head Γ t π h ->
      snd (decompose_stack π) = snd (decompose_stack ξ).
  Proof.
    intros Γ t π h fn ξ e.
    revert e.
    funelim (reducible_head Γ t π h).
    all: intro ee ; noconf ee.
    - eapply unfold_one_fix_decompose. eassumption.
    - reflexivity.
    - reflexivity.
    - reflexivity.
  Qed.

  (* TODO move to PCUICNormal *)
  Lemma whnf_mkApps_tPrim_inv : 
    forall (f : RedFlags.t) (Σ : global_env) (Γ : context) p (args : list term),
      whnf f Σ Γ (mkApps (tPrim p) args) -> args = [].
  Proof.
    intros * wh.
    inversion wh; solve_discr.
    clear -X.
    remember (mkApps (tPrim p) args) eqn:teq.
    exfalso.
    revert teq.
    induction X in args |- *; intros; solve_discr.
    destruct args as [|? ? _] using MCList.rev_ind; [easy|].
    rewrite <- mkApps_nested in teq.
    cbn in teq. noconf teq.
    eauto.
  Qed.

  Lemma reducible_head_None Γ t π h :
    isApp t = false ->
    whnf RedFlags.nodelta Σ (Γ,,, stack_context π) (mkApps t (decompose_stack π).1) ->
    None = reducible_head Γ t π h ->
    ∥∑ t' args',
      whnf_red Σ (Γ,,, stack_context π) t t' ×
      All2 (red Σ (Γ,,, stack_context π)) (decompose_stack π).1 args' ×
      whnf RedFlags.default Σ (Γ,,, stack_context π) (mkApps t' args')∥.
  Proof.
    funelim (reducible_head Γ t π h); intros notapp wh [=].
    - apply whnf_mkApps_inv in wh.
      depelim wh; solve_discr.
      depelim w; solve_discr; try discriminate.
      constructor; eexists _, (decompose_stack π).1.
      split; [now constructor|].
      split; eauto with pcuic.
      apply whnf_mkApps.
      eauto with pcuic.
    - apply whnf_mkApps_inv in wh; auto.
      depelim wh; solve_discr.
      constructor; eexists _, (decompose_stack π).1.
      split; [constructor|].
      split; eauto with pcuic.
      apply whnf_mkApps.
      constructor.
    - apply whnf_mkApps_inv in wh; auto.
      depelim wh; solve_discr.
      constructor; eexists _, (decompose_stack π).1.
      split; [constructor; eauto with pcuic|].
      split; eauto with pcuic.
      apply whnf_mkApps.
      depelim w; solve_discr; eauto with pcuic.
    - apply whnf_mkApps_tSort_inv in wh as ->.
      constructor; eexists _, [].
      eauto using whnf_red with pcuic.
    - apply whnf_mkApps_tProd_inv in wh as ->.
      constructor; eexists _, [].
      eauto using whnf_red with pcuic.
    - depelim wh; solve_discr.
      + apply whne_mkApps_inv in w as [|(?&?&?&?&?&?&?&?&?)]; auto; try discriminate.
        depelim w; solve_discr.
        discriminate.
      + rewrite H1.
        constructor; eexists _, []; eauto using whnf_red with pcuic.
    - apply whnf_mkApps_inv in wh; auto.
      depelim wh; solve_discr.
      depelim w; solve_discr.
      discriminate.
    - discriminate.
    - constructor; eexists _, (decompose_stack π).1; eauto using whnf_red with pcuic.
    - constructor; eexists _, (decompose_stack π).1; eauto using whnf_red with pcuic.
    - eapply unfold_one_fix_None in H0 as [(?&?&?)].
      constructor; eexists _, x.
      split; [constructor; eauto with pcuic|].
      eauto with pcuic.
    - constructor; eexists _, (decompose_stack π).1.
      split; [constructor; eauto with pcuic|].
      eauto with pcuic.
    - apply whnf_mkApps_tPrim_inv in wh as ->.
      constructor; eexists _, [].
      eauto using whnf_red with pcuic.
    - constructor; eexists _, (decompose_stack π).1.
      split; [econstructor|]; eauto.
      split; [eauto with pcuic|].
      apply whnf_mkApps.
      eapply whne_const; eauto.
    - zip fold in h.
      apply welltyped_context in h; auto.
      destruct hΣ.
      destruct h as (?&typ); auto.
      apply inversion_Const in typ as (?&?&?&?); auto.
      unfold declared_constant in d; congruence.
    - zip fold in h.
      apply welltyped_context in h; auto.
      destruct hΣ.
      destruct h as (?&typ); auto.
      apply inversion_Const in typ as (?&?&?&?); auto.
      unfold declared_constant in d; congruence.
    - clear H.
      apply unfold_one_case_None in e as [(c'&r&whcase)].
      constructor; exists (tCase indn p c' brs), (decompose_stack π).1.
      split.
      + destruct p. constructor; eauto with pcuic.
      + split; [eauto with pcuic|].
        apply whnf_mkApps.
        auto.
    - clear H.
      apply unfold_one_proj_None in e as [(c'&r&whproj)].
      constructor; exists (tProj p0 c'), (decompose_stack π).1.
      split.
      + constructor; eauto with pcuic.
      + split; [eauto with pcuic|].
        apply whnf_mkApps.
        auto.
  Qed.
  
  (* TODO Factorise *)
  Equations(noeqns) _isconv_fallback (Γ : context) (leq : conv_pb)
            (t1 : term) (π1 : stack) (h1 : wtp Γ t1 π1)
            (t2 : term) (π2 : stack) (h2 : wtp Γ t2 π2)
            (ir1 : isred_full Γ t1 π1) (ir2 : isred_full Γ t2 π2)
            (hdiscr : prog_discr t1 t2)
            (hx : conv_stack_ctx Γ π1 π2)
            (aux : Aux Fallback Γ t1 π1 t2 π2 h2)
    : ConversionResult (conv_term leq Γ t1 π1 t2 π2) :=
    _isconv_fallback Γ leq t1 π1 h1 t2 π2 h2 ir1 ir2 hdiscr hx aux
    with inspect (reducible_head Γ t1 π1 h1) := {
    | @exist (Some (rt1, ρ1)) eq1 with inspect (decompose_stack ρ1) := {
      | @exist (l1, θ1) eq2
        with inspect (reduce_stack RedFlags.nodelta Σ hΣ (Γ ,,, stack_context ρ1) rt1 (appstack l1 ε) _) := {
        | @exist (rt1', θ1') eq3 :=
          isconv_prog leq rt1' (θ1' +++ θ1) t2 π2 aux
        }
      } ;
    | @exist None nored1 with inspect (reducible_head Γ t2 π2 h2) := {
      | @exist (Some (rt2, ρ2)) eq1 with inspect (decompose_stack ρ2) := {
        | @exist (l2, θ2) eq2
          with inspect (reduce_stack RedFlags.nodelta Σ hΣ (Γ ,,, stack_context ρ2) rt2 (appstack l2 ε) _) := {
          | @exist (rt2', θ2') eq3 :=
            isconv_prog leq t1 π1 rt2' (θ2' +++ θ2) aux
          }
        } ;
      | @exist None nored2 with inspect (eqb_termp_napp Σ G leq #|(decompose_stack π1).1| t1 t2) := {
        | @exist true eq1 := isconv_args leq t1 π1 t2 π2 aux;
        | @exist false noteq :=
          no (
              HeadMismatch
                leq
                (Γ ,,, stack_context π1) t1
                (Γ ,,, stack_context π2) t2
            )
        }
      }
    }.
  Next Obligation.
    apply reducible_head_red_zipp in eq1 as r.
    apply reducible_head_decompose in eq1 as d.
    apply welltyped_zipc_zipp in h1 as hh1. 2: auto.
    cbn in *.
    simpl_stacks.
    pose proof (red_welltyped _ hΣ hh1 r) as hh.
    assumption.
  Qed.
  Next Obligation.
    apply reducible_head_cored in eq1 as r1. apply cored_red in r1.
    destruct r1 as [r1].
    simpl_reduce_stack.
    eapply red_welltyped ; auto ; revgoals.
    - constructor. zip fold. eapply red_context_zip. simpl_stacks. eassumption.
    - cbn. simpl_stacks.
      eapply red_welltyped ; auto ; revgoals.
      + constructor. eassumption.
      + assumption.
  Qed.
  Next Obligation.
    eapply R_cored. simpl.
    apply reducible_head_cored in eq1 as r1.
    apply reducible_head_decompose in eq1 as d1.
    rewrite <- eq2 in d1. cbn in d1.
    case_eq (decompose_stack π1). intros l' s' e'.
    rewrite e' in d1. cbn in d1. subst.
    match type of eq3 with
    | _ = reduce_stack ?f ?Σ ?hΣ ?Γ ?t ?π ?h =>
      destruct (reduce_stack_sound f Σ hΣ Γ t π h) as [r2] ;
      pose proof (reduce_stack_decompose RedFlags.nodelta _ hΣ _ _ _ h) as d2
    end.
    rewrite <- eq3 in r2. cbn in r2.
    rewrite <- eq3 in d2. cbn in d2.
    rewrite decompose_stack_appstack in d2. cbn in d2.
    rewrite zipc_appstack in r2. cbn in r2.
    case_eq (decompose_stack θ1'). intros l s e.
    rewrite e in d2. cbn in d2. subst.
    apply decompose_stack_eq in e as ?. subst.
    apply decompose_stack_eq in e' as ?. subst.
    rewrite stack_cat_appstack. rewrite 2!zipc_appstack.
    rewrite zipc_appstack in r2. simpl in r2.
    clear eq3. symmetry in eq2. apply decompose_stack_eq in eq2. subst.
    rewrite 2!zipc_appstack in r1.
    rewrite stack_context_appstack in r2.
    eapply red_cored_cored ; try eassumption.
    repeat zip fold. eapply red_context_zip. assumption.
  Qed.
  Next Obligation.
    apply reducible_head_decompose in eq1 as d1.
    simpl_reduce_stack.
    assumption.
  Qed.
  Next Obligation.
    simpl_reduce_stack.
    specialize (isr eq_refl) as (?&_).
    split; auto.
    now simpl_stacks.
  Qed.
  Next Obligation.
    apply reducible_head_red_zipp in eq1 as r1. destruct r1 as [r1].
    apply reducible_head_decompose in eq1 as d1.
    simpl_reduce_stack.
    destruct hΣ as [wΣ].
    etransitivity ; try eassumption.
    eapply red_conv_cum_l ; try assumption.
    eapply red_trans ; try eassumption.
  Qed.
  Next Obligation.
    apply h; clear h.
    apply reducible_head_red_zipp in eq1 as r1. destruct r1 as [r1].
    apply reducible_head_decompose in eq1 as d1.
    simpl_reduce_stack.
    destruct hΣ as [wΣ].
    etransitivity ; try eassumption.
    eapply red_conv_cum_r ; try assumption.
    eapply red_trans ; eassumption.
  Qed.
  Next Obligation.
    apply reducible_head_red_zipp in eq1 as r.
    apply reducible_head_decompose in eq1 as d.
    cbn.
    simpl_stacks.
    apply welltyped_zipc_zipp in h2 as hh2. 2: auto.
    simpl_stacks.
    pose proof (red_welltyped _ hΣ hh2 r) as hh.
    assumption.
  Qed.
  Next Obligation.
    apply reducible_head_cored in eq1 as r1. apply cored_red in r1.
    destruct r1 as [r1].
    match type of eq3 with
    | _ = reduce_stack ?f ?Σ ?hΣ ?Γ ?t ?π ?h =>
      destruct (reduce_stack_sound f Σ hΣ Γ t π h) as [r2] ;
      pose proof (reduce_stack_decompose RedFlags.nodelta _ hΣ _ _ _ h) as d2
    end.
    rewrite <- eq3 in r2. cbn in r2.
    rewrite <- eq3 in d2. cbn in d2.
    rewrite decompose_stack_appstack in d2. cbn in d2.
    rewrite zipc_appstack in r2. cbn in r2.
    case_eq (decompose_stack θ2'). intros l s e.
    rewrite e in d2. cbn in d2. subst.
    apply decompose_stack_eq in e as ?. subst.
    rewrite stack_cat_appstack.
    rewrite zipc_appstack in r2. cbn in r2.
    rewrite zipc_appstack.
    pose proof (eq_sym eq2) as eq2'.
    apply decompose_stack_eq in eq2'. subst.
    rewrite stack_context_appstack in r2.
    eapply red_welltyped ; auto ; revgoals.
    - constructor. zip fold. eapply red_context_zip. eassumption.
    - rewrite zipc_appstack in r1. cbn.
      eapply red_welltyped ; auto ; revgoals.
      + constructor. eassumption.
      + assumption.
  Qed.
  Next Obligation.
    eapply R_cored2. all: simpl. all: try reflexivity.
    apply reducible_head_cored in eq1 as r1.
    apply reducible_head_decompose in eq1 as d1.
    rewrite <- eq2 in d1. cbn in d1.
    case_eq (decompose_stack π2). intros l' s' e'.
    rewrite e' in d1. cbn in d1. subst.
    match type of eq3 with
    | _ = reduce_stack ?f ?Σ ?hΣ ?Γ ?t ?π ?h =>
      destruct (reduce_stack_sound f Σ hΣ Γ t π h) as [r2] ;
      pose proof (reduce_stack_decompose RedFlags.nodelta _ hΣ _ _ _ h) as d2
    end.
    rewrite <- eq3 in r2. cbn in r2.
    rewrite <- eq3 in d2. cbn in d2.
    rewrite decompose_stack_appstack in d2. cbn in d2.
    rewrite zipc_appstack in r2. cbn in r2.
    case_eq (decompose_stack θ2'). intros l s e.
    rewrite e in d2. cbn in d2. subst.
    apply decompose_stack_eq in e as ?. subst.
    apply decompose_stack_eq in e' as ?. subst.
    rewrite stack_cat_appstack. rewrite 2!zipc_appstack.
    rewrite zipc_appstack in r2. simpl in r2.
    clear eq3. symmetry in eq2. apply decompose_stack_eq in eq2. subst.
    rewrite 2!zipc_appstack in r1.
    rewrite stack_context_appstack in r2.
    eapply red_cored_cored ; try eassumption.
    repeat zip fold. eapply red_context_zip. assumption.
  Qed.
  Next Obligation.
    apply reducible_head_decompose in eq1 as d1.
    now simpl_reduce_stack.
  Qed.
  Next Obligation.
    simpl_reduce_stack.
    specialize (isr eq_refl) as (?&_).
    split; auto.
    now simpl_stacks.
  Qed.
  Next Obligation.
    destruct hΣ as [wΣ].
    apply reducible_head_red_zipp in eq1 as r1. destruct r1 as [r1].
    apply reducible_head_decompose in eq1 as d1.
    simpl_reduce_stack.
    destruct hx as [hx].
    etransitivity ; try eassumption.
    eapply conv_cum_conv_ctx.
    - assumption.
    - eapply red_conv_cum_r. 1: assumption.
      eapply red_trans ; eassumption.
    - eapply conv_context_sym. all: auto.
  Qed.
  Next Obligation.
    apply h; clear h.
    (* Contrapositive of previous case *)
    destruct hΣ as [wΣ].
    apply reducible_head_red_zipp in eq1 as r1. destruct r1 as [r1].
    apply reducible_head_decompose in eq1 as d1.
    simpl_reduce_stack.
    destruct hx as [hx].
    etransitivity ; try eassumption.
    eapply conv_cum_conv_ctx.
    - assumption.
    - eapply red_conv_cum_l.
      eapply red_trans ; eassumption.
    - eapply conv_context_sym. all: auto.
  Qed.
  Next Obligation.
    eapply R_stateR. all: simpl. all: try reflexivity.
    constructor.
  Qed.
  Next Obligation.
    destruct h, hΣ.
    apply conv_terms_alt in X as (argsr&argsr'&?&?&?).
    rewrite !zipp_as_mkApps.
    apply conv_cum_alt.
    constructor; eexists _, _.
    split; [split|].
    - apply red_mkApps; [reflexivity|eassumption].
    - apply red_mkApps; [reflexivity|eassumption].
    - apply eq_term_upto_univ_napp_mkApps; auto.
      rewrite Nat.add_0_r.
      apply All2_length in a.
      rewrite a in eq1.
      eapply eqb_termp_napp_spec; eauto.
  Qed.
  Next Obligation.
    apply h; clear h.
    destruct ir1 as (notapp1&[whδ1]), ir2 as (notapp2&[whδ2]).
    rewrite !zipp_as_mkApps in *.
    apply reducible_head_None in nored1 as [(?&?&s1&r1&wh1)]; auto.
    apply reducible_head_None in nored2 as [(?&?&s2&r2&wh2)]; auto.
    destruct hΣ, hx.
    apply whnf_red_red in s1 as ?.
    apply whnf_red_red in s2 as ?.
    eapply conv_cum_red_conv_inv in H.
    2: assumption.
    2: eassumption.
    2: apply red_mkApps; eassumption.
    2: apply red_mkApps; eassumption.
    apply conv_cum_mkApps_inv in H as [(?&?)]; auto.
    2: now depelim s1.
    2: now depelim s2.
    2: eapply whnf_conv_context; eauto.
    2: eapply conv_context_sym; eauto.
    constructor.
    eapply conv_terms_red_conv; eauto.
  Qed.
  Next Obligation.
    unfold eqb_termp_napp in noteq.
    destruct ir1 as (notapp1&[whδ1]), ir2 as (notapp2&[whδ2]).
    rewrite !zipp_as_mkApps in *.
    apply reducible_head_None in nored1 as [(?&?&s1&rargs1&wh1)]; auto.
    apply reducible_head_None in nored2 as [(?&?&s2&rargs2&wh2)]; auto.
    destruct hΣ, hx.
    apply whnf_red_red in s1 as ?.
    apply whnf_red_red in s2 as ?.
    eapply conv_cum_red_conv_inv in H.
    2: assumption.
    2: eassumption.
    2: apply red_mkApps; eassumption.
    2: apply red_mkApps; eassumption.
    apply conv_cum_mkApps_inv in H as [(conv_hds&_)]; auto.
    2: now inversion s1; subst.
    2: now inversion s2; subst.
    2: eapply whnf_conv_context; eauto.
    2: eapply conv_context_sym; eauto.
    apply whnf_mkApps_inv in wh1.
    destruct t1; cbn in *.
    all: inversion s1; subst; clear s1.
    9: { destruct conv_hds as [H].
         inversion H; subst; clear H.
         inversion s2; subst; clear s2.
         zip fold in h1.
         zip fold in h2.
         apply welltyped_context in h1; auto.
         clear aux.
         apply welltyped_context in h2; auto.
         destruct h1 as (?&typ1); auto.
         destruct h2 as (?&typ2); auto.
         apply inversion_Ind in typ1 as (?&?&?&?&?&?); auto.
         apply inversion_Ind in typ2 as (?&?&?&?&?&?); auto.
         apply consistent_instance_ext_all_mem in c1.
         apply consistent_instance_ext_all_mem in c.
         apply compare_global_instance_complete in H3; auto.
         rewrite eq_inductive_refl in noteq.
         apply All2_length in rargs1.
         rewrite <- rargs1 in H3.
         cbn in *.
         easy. }
    9: { destruct conv_hds as [H].
         inversion H; subst; clear H.
         inversion s2; subst; clear s2.
         zip fold in h1.
         zip fold in h2.
         apply welltyped_context in h1; auto.
         clear aux.
         apply welltyped_context in h2; auto.
         destruct h1 as (?&typ1); auto.
         destruct h2 as (?&typ2); auto.
         apply inversion_Construct in typ1 as (?&?&?&?&?&?&?); auto.
         apply inversion_Construct in typ2 as (?&?&?&?&?&?&?); auto.
         apply consistent_instance_ext_all_mem in c1.
         apply consistent_instance_ext_all_mem in c.
         apply compare_global_instance_complete in H4; auto.
         rewrite eq_inductive_refl, Nat.eqb_refl in noteq.
         apply All2_length in rargs1.
         rewrite <- rargs1 in H4.
         cbn in *.
         easy. }
    all: apply conv_cum_alt in conv_hds as [(?&?&(r1&r2)&?)].
    all: eapply whnf_red_inv in r1; auto.
    all: inversion r1; subst; clear r1.
    all: inversion e0; subst; clear e0.
    all: apply whnf_mkApps_inv in wh2.
    all: eapply whnf_conv_context in wh2; [|apply conv_context_sym; eauto].
    all: eapply whnf_red_inv in r2; auto.
    all: inversion r2; subst; clear r2.
    all: inversion s2; subst; clear s2.
    all: destruct hdiscr.
    - now rewrite Nat.eqb_refl in noteq.
    - now rewrite eq_string_refl in noteq.
    - zip fold in h1.
      apply welltyped_context in h1; auto.
      destruct h1 as (?&typ).
      now apply inversion_Evar in typ.
    - zip fold in h1.
      zip fold in h2.
      apply welltyped_context in h1 as [s1 h1]; auto.
      clear aux.
      apply welltyped_context in h2 as [s2 h2]; auto.
      simpl in h2.
      apply inversion_Sort in h2 as (_&h2&_); auto.
      apply inversion_Sort in h1 as (_&h1&_); auto.      
      eapply conv_pb_relb_complete in H0; eauto.
      congruence.
    - now rewrite eq_dec_to_bool_refl in noteq.
  Qed.
  
  Equations _isconv (s : state) (Γ : context)
            (t1 : term) (π1 : stack) (h1 : wtp Γ t1 π1)
            (t2 : term) (π2 : stack) (h2 : wtp Γ t2 π2)
            (aux : Aux s Γ t1 π1 t2 π2 h2)
  : Ret s Γ t1 π1 t2 π2 :=
    _isconv Reduction Γ t1 π1 h1 t2 π2 h2 aux :=
      λ { | leq | hx | _ | _ | _ := _isconv_red Γ leq t1 π1 h1 t2 π2 h2 hx aux } ;

    _isconv Term Γ t1 π1 h1 t2 π2 h2 aux :=
      λ { | leq | hx | r1 | r2 | _ := _isconv_prog Γ leq t1 π1 h1 t2 π2 h2 hx r1 r2 aux } ;

    _isconv Args Γ t1 π1 h1 t2 π2 h2 aux :=
      λ { | leq | hx | _ | _ | _ := _isconv_args leq Γ t1 π1 h1 t2 π2 h2 hx aux } ;

    _isconv Fallback Γ t1 π1 h1 t2 π2 h2 aux :=
      λ { | leq | hx | r1 | r2 | hd := _isconv_fallback Γ leq t1 π1 h1 t2 π2 h2 r1 r2 hd hx aux }.

  Equations(noeqns) isconv_full (s : state) (Γ : context)
            (t1 : term) (π1 : stack) (h1 : wtp Γ t1 π1)
            (t2 : term) (π2 : stack) (h2 : wtp Γ t2 π2)
    : Ret s Γ t1 π1 t2 π2 :=

    isconv_full s Γ t1 π1 h1 t2 π2 h2 hx :=
      Fix_F (R := R Γ)
            (fun '(mkpack s' t1' π1' t2' π2' h2') =>
              wtp Γ t1' π1' ->
              wtp Γ t2' π2' ->
              Ret s' Γ t1' π1' t2' π2'
            )
            (fun pp f => _)
            (x := mkpack Γ s t1 π1 t2 π2 _)
            _ _ _ _.
  Next Obligation.
    unshelve eapply _isconv. all: try assumption.
    intros s' t1' π1' t2' π2' h1' h2' hx' hR.
    apply welltyped_zipc_zipp in h1. 2: auto.
    destruct pp.
    assert (wth0 = H0) by apply proof_irrelevance. simpl in hR. subst.
    specialize (f (mkpack Γ s' t1' π1' t2' π2' h2') hR). cbn in f.
    eapply f ; assumption.
  Qed.
  Next Obligation.
    apply R_Acc. assumption.
  Qed.
  
  Inductive ConversionResultSummary :=
  | ConvSuccess : ConversionResultSummary
  | ConvError : ConversionError -> ConversionResultSummary.

  Definition isconv Γ leq t1 π1 h1 t2 π2 h2 hx :=
    match isconv_full Reduction Γ t1 π1 h1 t2 π2 h2 leq hx I I I with
    | Success _ => ConvSuccess
    | Error e _ => ConvError e
    end.
  
  Theorem isconv_sound :
    forall Γ leq t1 π1 h1 t2 π2 h2 hx,
      isconv Γ leq t1 π1 h1 t2 π2 h2 hx = ConvSuccess ->
      conv_cum leq Σ (Γ ,,, stack_context π1) (zipp t1 π1) (zipp t2 π2).
  Proof.
    unfold isconv.
    intros Γ leq t1 π1 h1 t2 π2 h2 hx.
    destruct isconv_full as [].
    - auto.
    - discriminate.
  Qed.
  
  Theorem isconv_complete :
    forall Γ leq t1 π1 h1 t2 π2 h2 hx e,
      isconv Γ leq t1 π1 h1 t2 π2 h2 hx = ConvError e ->
      ~conv_cum leq Σ (Γ ,,, stack_context π1) (zipp t1 π1) (zipp t2 π2).
  Proof.
    unfold isconv.
    intros Γ leq t1 π1 h1 t2 π2 h2 hx.
    destruct isconv_full as []; auto.
    intros ? [=].
  Qed.

  Definition isconv_term Γ leq t1 (h1 : welltyped Σ Γ t1) t2 (h2 : welltyped Σ Γ t2) :=
    isconv Γ leq t1 ε h1 t2 ε h2 (sq (conv_ctx_refl _ Γ)).

  Theorem isconv_term_sound :
    forall Γ leq t1 h1 t2 h2,
      isconv_term Γ leq t1 h1 t2 h2 = ConvSuccess ->
      conv_cum leq Σ Γ t1 t2.
  Proof.
    intros Γ leq t1 h1 t2 h2.
    unfold isconv_term. intro h.
    apply isconv_sound in h. apply h.
  Qed.

  Theorem isconv_term_complete :
    forall Γ leq t1 h1 t2 h2 e,
      isconv_term Γ leq t1 h1 t2 h2 = ConvError e ->
      ~conv_cum leq Σ Γ t1 t2.
  Proof.
    intros Γ leq t1 h1 t2 h2 e.
    unfold isconv_term. intro h.
    apply isconv_complete in h. apply h.
  Qed.
  Transparent reduce_stack.
  
End Conversion.
