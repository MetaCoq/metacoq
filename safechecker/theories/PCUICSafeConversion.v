(* Distributed under the terms of the MIT license. *)
From Coq Require Import ProofIrrelevance.
From MetaCoq.Template Require Import config utils uGraph.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICReflect PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICGlobalEnv
     PCUICCumulativity PCUICConversion PCUICEquality PCUICConversion
     PCUICSafeLemmata PCUICNormal PCUICInversion PCUICReduction PCUICPosition
     PCUICPrincipality PCUICContextConversion PCUICContextConversionTyp PCUICSN PCUICUtils PCUICWfUniverses
     PCUICOnFreeVars PCUICWellScopedCumulativity
     PCUICWeakeningEnvConv PCUICWeakeningEnvTyp
     PCUICWeakeningConv PCUICWeakeningTyp 
     PCUICClosed PCUICClosedTyp PCUICConvCumInversion PCUICEqualityDec.
From MetaCoq.SafeChecker Require Import PCUICErrors PCUICSafeReduce.

Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

Local Set Keyed Unification.

Set Default Goal Selector "!".

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

#[global]
Instance red_brs_refl Σ p Γ: CRelationClasses.Reflexive (@red_brs Σ p Γ).
Proof.
  intros brs.
  eapply All2_same; unfold on_Trel; split; reflexivity.
Qed.

#[global]
Instance conv_cum_trans {cf leq} {Σ : global_env_ext} {Γ} : wf Σ -> RelationClasses.Transitive (@conv_cum cf leq Σ Γ).
Proof.
  intros x y z; unfold conv_cum. intros; sq.
  now etransitivity.
Qed.

Lemma closed_red_mkApps_tConst_axiom {cf} {Σ} {wfΣ : wf Σ} {Γ} {cst u} {args : list term} {cb c} :
  declared_constant Σ cst cb -> cst_body cb = None ->
  Σ ;;; Γ ⊢ mkApps (tConst cst u) args ⇝ c ->
  ∑ args' : list term,
  (c = mkApps (tConst cst u) args') * (red_terms Σ Γ args args').
Proof.
  intros decl hcb [clΓ clt r].
  eapply (PCUICConfluence.red_mkApps_tConst_axiom (Γ := exist Γ clΓ)) in decl as [args' [eq r']]; tea.
  * exists args'; split; auto.
    eapply into_red_terms; auto.
    inv_on_free_vars. solve_all.
  * cbn. inv_on_free_vars; solve_all.
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

  Local Definition heΣ : ∥ wf_ext Σ ∥.
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
    apply normalisation_upto in hu as h. 2: exact heΣ.
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
    - eapply normalisation_upto.
      2: assumption.
      1: exact heΣ.
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
    (∥ (Σ ⊢ Γ ,,, stack_context π1 = Γ ,,, stack_context π2) ∥).

  Notation conv_term leq Γ t π t' π' :=
    (conv_cum leq Σ (Γ ,,, stack_context π) (zipp t π) (zipp t' π'))
      (only parsing).

  Notation alt_conv_term Γ t π t' π' :=
    (∥ Σ ;;; Γ ,,, stack_context π ⊢ zipp t π = zipp t' π' ∥)
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
    destruct π as [|[]]; cbn in *; try easy.
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
    zipp t (π ++ (decompose_stack π').2) = zipp t π.
  Proof.
    rewrite zipp_stack_cat; auto.
    destruct decompose_stack eqn:decomp.
    now apply decompose_stack_noStackApp in decomp.
  Qed.

  Lemma zipc_decompose_stack_empty t π :
    (decompose_stack π).2 = [] ->
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
       | [H: context[stack_context (?π ++ ?π')] |- _] =>
         (rewrite (stack_context_stack_cat π' π) in H; cbn in H) || fail 2
       | [H: (decompose_stack ?π).2 = [], H': context[stack_context ?π] |- _] =>
         (rewrite <- (stack_context_decompose π), H in H'; cbn in H') || fail 2
       | [H: (decompose_stack ?π).2 = [], H': context[zipc ?t ?π] |- _] =>
         (rewrite (zipc_decompose_stack_empty t π H) in H'; cbn in H') || fail 2
       | [H: context[stack_context (decompose_stack ?π).2] |- _] =>
         (rewrite (stack_context_decompose π) in H; cbn in H) || fail 2
       | [H: context[zipp ?t (?π ++ (decompose_stack ?π').2)] |- _] =>
         (rewrite (zipp_stack_cat_decompose_stack t π π') in H; cbn in H) || fail 2
       | [H: context[zipc ?t (appstack ?args ?π)] |- _] =>
         (rewrite (@zipc_appstack t args π) in H; cbn in H) || fail 2
       | [H: context[zipc ?t (?π ++ ?π')] |- _] =>
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
       | [|- context[stack_context (?π ++ ?π')]] =>
         (rewrite (stack_context_stack_cat π' π); cbn) || fail 2
       | [H: (decompose_stack ?π).2 = [] |- context[stack_context ?π]] =>
         (rewrite <- (stack_context_decompose π), H; cbn) || fail 2
       | [H: (decompose_stack ?π).2 = [] |- context[zipc ?t ?π]] =>
         (rewrite (zipc_decompose_stack_empty t π H); cbn) || fail 2
       | [|- context[stack_context (decompose_stack ?π).2]] =>
         (rewrite (stack_context_decompose π); cbn) || fail 2
       | [|- context[zipp ?t (?π ++ (decompose_stack ?π').2)]] =>
         (rewrite (zipp_stack_cat_decompose_stack t π π'); cbn) || fail 2
       | [|- context[zipc ?t (appstack ?args ?π)]] =>
         (rewrite (@zipc_appstack t args π); cbn) || fail 2
       | [|- context[zipc ?t (?π ++ ?π')]] =>
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
      | Args => ConversionResult (∥equality_terms Σ (Γ,,, stack_context π)
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
        with inspect (reduce_stack RedFlags.nodelta Σ heΣ
                                   (Γ ,,, stack_context π1)
                                   t1 (appstack args1 []) _) := {
        | @exist (t1',π1') eq1
          with inspect (reduce_stack RedFlags.nodelta Σ heΣ
                                     (Γ ,,, stack_context π2)
                                     t2 (appstack args2 []) _) := {
          | @exist (t2',π2') eq2 => isconv_prog leq t1' (π1' ++ ρ1) t2' (π2' ++ ρ2) aux
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
    - constructor. zip fold. eapply red_context_zip. simpl_stacks. eapply r0.
    - cbn. simpl_stacks. assumption.
  Qed.
  Next Obligation.
    simpl_reduce_stack.
    eapply red_welltyped ; try assumption ; revgoals.
    - constructor. zip fold. eapply red_context_zip. simpl_stacks. eapply r.
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
      | @exist (Some (l, c, θ)) eq2 with inspect (reduce_stack RedFlags.default Σ heΣ
                                                               (Γ ,,, stack_context θ) c [] _) := {
        | @exist (cred, ρ) eq3 with construct_viewc cred := {
          | view_construct ind n ui := Some (fn, appstack l (App_l (zipc (tConstruct ind n ui) ρ) :: θ)) ;
          | view_other cred h' := None
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
    apply_funelim (unfold_one_fix Γ mfix idx π h); intros; try discriminate.
    all: noconf eq.
    unfold zipp.
    pose proof (eq_sym eq2) as eq.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq). subst.
    rewrite 2!decompose_stack_appstack. simpl.
    case_eq (decompose_stack θ). intros l' s' e'.
    simpl.
    match type of eq3 with
    | _ = reduce_stack ?flags ?Σ ?hΣ ?Γ ?t ?π ?h =>
      pose proof (reduce_stack_sound flags Σ hΣ Γ t π h) as [r1] ;
      pose proof (reduce_stack_decompose flags Σ hΣ Γ t π h) as hd
    end.
    rewrite <- eq3 in r1. cbn in r1.
    rewrite <- eq3 in hd. cbn in hd.
    constructor.
    rewrite stack_context_appstack. simpl.
    rewrite 2!mkApps_app. cbn. eapply red_mkApps_f.
    pose proof (decompose_stack_eq _ _ _ e'). subst.
    rewrite stack_context_appstack in r1.
    rewrite stack_context_appstack.
    eapply trans_red.
    - eapply red_app_r. exact r1.
    - repeat lazymatch goal with
      | |- context [ tApp (mkApps ?t ?l) ?u ] =>
        replace (tApp (mkApps t l) u) with (mkApps t (l ++ [u]))
          by (rewrite mkApps_app ; reflexivity)
      end.
      eapply red_fix.
      + symmetry. eassumption.
      + unfold is_constructor.
        pose proof (eq_sym eq2) as eql.
        apply decompose_stack_at_length in eql. subst.
        rewrite nth_error_app_ge by auto.
        replace (#|l| - #|l|) with 0 by lia. cbn.
        case_eq (decompose_stack ρ). intros l0 s1 ee.
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
    apply_funelim (unfold_one_fix Γ mfix idx π h); intros; noconf eq.
    unfold zippx.
    pose proof (eq_sym eq2) as eq.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq). subst.
    rewrite 2!decompose_stack_appstack. simpl.
    case_eq (decompose_stack θ). intros l' s' e'.
    simpl.
    match type of eq3 with
    | _ = reduce_stack ?flags ?Σ ?hΣ ?Γ ?t ?π ?h =>
      pose proof (reduce_stack_sound flags Σ hΣ Γ t π h) as [r1] ;
      pose proof (reduce_stack_decompose flags Σ hΣ Γ t π h) as hd
    end.
    rewrite <- eq3 in r1. cbn in r1.
    rewrite <- eq3 in hd. cbn in hd.
    constructor. eapply red_it_mkLambda_or_LetIn.
    rewrite 2!mkApps_app. cbn. eapply red_mkApps_f.
    pose proof (decompose_stack_eq _ _ _ e'). subst.
    rewrite stack_context_appstack in r1.
    eapply trans_red.
    - eapply red_app_r. exact r1.
    - repeat lazymatch goal with
      | |- context [ tApp (mkApps ?t ?l) ?u ] =>
        replace (tApp (mkApps t l) u) with (mkApps t (l ++ [u]))
          by (rewrite mkApps_app ; reflexivity)
      end.
      eapply red_fix.
      + symmetry. eassumption.
      + unfold is_constructor.
        pose proof (eq_sym eq2) as eql.
        apply decompose_stack_at_length in eql. subst.
        rewrite nth_error_app_ge by auto.
        replace (#|l| - #|l|) with 0 by lia. cbn.
        case_eq (decompose_stack ρ). intros l0 s1 ee.
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
    apply_funelim (unfold_one_fix Γ mfix idx π h); intros; noconf eq.
    pose proof (eq_sym eq2) as eq.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq). subst.
    rewrite !zipc_appstack. cbn.
    match type of eq3 with
    | _ = reduce_stack ?flags ?Σ ?hΣ ?Γ ?t ?π ?h =>
      pose proof (reduce_stack_sound flags Σ hΣ Γ t π h) as [r1] ;
      pose proof (reduce_stack_decompose flags Σ hΣ Γ t π h) as hd
    end.
    clear Heq1 Heq2. cbn in r1.
    rewrite <- eq3 in r1. cbn in r1.
    rewrite <- eq3 in hd. cbn in hd.
    do 2 zip fold. constructor. eapply red_context_zip.
    eapply trans_red.
    - eapply red_app_r. exact r1.
    - repeat lazymatch goal with
      | |- context [ tApp (mkApps ?t ?l) ?u ] =>
        replace (tApp (mkApps t l) u) with (mkApps t (l ++ [u]))
          by (rewrite mkApps_app ; reflexivity)
      end.
      eapply red_fix.
      + symmetry. eassumption.
      + unfold is_constructor.
        pose proof (eq_sym eq2) as eql.
        apply decompose_stack_at_length in eql. subst.
        rewrite nth_error_app_ge by auto.
        replace (#|l| - #|l|) with 0 by lia. cbn.
        case_eq (decompose_stack ρ). intros l0 s1 ee.
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
    apply_funelim (unfold_one_fix Γ mfix idx π h); intros ; noconf eq.
    pose proof (eq_sym eq2) as eq.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq). subst.
    rewrite !zipc_appstack. cbn.
    match type of eq3 with
    | _ = reduce_stack ?flags ?Σ ?hΣ ?Γ ?t ?π ?h =>
      pose proof (reduce_stack_sound flags Σ hΣ Γ t π h) as [r1] ;
      pose proof (reduce_stack_decompose flags Σ hΣ Γ t π h) as hd
    end.
    rewrite <- eq3 in r1. cbn in r1.
    rewrite <- eq3 in hd. cbn in hd.
    do 2 zip fold. eapply cored_context.
    eapply cored_red_trans.
    - eapply red_app_r. exact r1.
    - repeat lazymatch goal with
      | |- context [ tApp (mkApps ?t ?l) ?u ] =>
        replace (tApp (mkApps t l) u) with (mkApps t (l ++ [u]))
          by (rewrite mkApps_app ; reflexivity)
      end.
      eapply red_fix.
      + symmetry. eassumption.
      + unfold is_constructor.
        pose proof (eq_sym eq2) as eql.
        apply decompose_stack_at_length in eql. subst.
        rewrite nth_error_app_ge by auto.
        replace (#|l| - #|l|) with 0 by lia. cbn.
        case_eq (decompose_stack ρ). intros l0 s1 ee.
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
    apply_funelim (unfold_one_fix Γ mfix idx π h); intros; noconf eq.
    pose proof (eq_sym eq2) as eq.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq). subst.
    rewrite 2!decompose_stack_appstack. cbn.
    case_eq (decompose_stack θ). intros l0 s1 H2.
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
      rewrite <- eq1.
      destruct (decompose_stack π) eqn:decomp.
      apply decompose_stack_noStackApp in decomp as ?.
      apply decompose_stack_eq in decomp as ->.
      clear H.
      symmetry in e.
      now apply decompose_stack_at_appstack_None in e.
    - match type of eq3 with
      | _ = reduce_stack ?a ?b ?c ?d ?e ?f ?g =>
        pose proof (reduce_stack_sound a b c d e f g) as [r];
        pose proof (reduce_stack_whnf a b c d e f g) as wh;
        pose proof (reduce_stack_decompose a b c d e f g) as decomp;
        pose proof (reduce_stack_isred a b c d e f g) as isr
      end.
      rewrite <- eq3 in r, wh, decomp, isr.
      specialize (isr eq_refl) as (noapp&_).
      cbn in *.
      clear H eq3 H0.
      symmetry in eq2.
      apply decompose_stack_at_length in eq2 as ?.
      apply decompose_stack_at_eq in eq2 as ->.
      rewrite stack_context_appstack.
      cbn.
      apply welltyped_zipc_zipp in h; auto.
      rewrite <- (stack_context_decompose ρ), decomp in wh.
      change (App_l c :: θ) with (appstack [c] θ) in *.
      rewrite !decompose_stack_appstack.
      rewrite zipp_as_mkApps, !decompose_stack_appstack in h.
      destruct h as (ty&typ).
      cbn in *.
      rewrite stack_context_appstack in typ.
      cbn in *.
      destruct (decompose_stack ρ) eqn:decomp'.
      apply decompose_stack_eq in decomp' as ->.
      rewrite zipc_appstack in r.
      rewrite zipp_appstack in wh.
      cbn in *; subst; cbn in *.
      destruct hΣ, wh.
      constructor; exists (l ++ (mkApps cred l0) :: (decompose_stack θ).1).
      eapply PCUICSR.subject_reduction in typ.
      2: eauto.
      2: apply red_mkApps; [reflexivity|].
      1: split.
      1,3: apply All2_app; [apply All2_same; reflexivity|].
      1,2: constructor; [|apply All2_same; reflexivity].
      1-2: eapply r.
      apply whnf_ne.
      econstructor.
      + eauto.
      + rewrite nth_error_snoc by easy.
        eauto.
      + eapply whnf_fix_arg_whne; eauto.
        now destruct cred.
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
    + pose proof heΣ. sq. eapply wf_ext_global_uctx_invariants.
      assumption.
    + pose proof heΣ. sq. eapply global_ext_uctx_consistent; assumption.
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
    destruct heΣ.
    destruct leq; cbn.
    - eapply check_eqb_universe_complete; eauto.
      + now apply wf_ext_global_uctx_invariants.
      + now apply global_ext_uctx_consistent.
    - eapply check_leqb_universe_complete; eauto.
      + now apply wf_ext_global_uctx_invariants.
      + now apply global_ext_uctx_consistent.
  Qed.
  
  Lemma get_level_make l :
    UnivExpr.get_level (UnivExpr.make l) = l.
  Proof. now destruct l. Qed.
  
  Lemma conv_pb_relb_make_complete leq x y :
    wf_universe_level Σ x ->
    wf_universe_level Σ y ->
    conv_pb_rel leq (global_ext_constraints Σ) (Universe.make x) (Universe.make y) ->
    conv_pb_relb leq (Universe.make x) (Universe.make y).
  Proof.
    intros wfx wfy r.
    apply conv_pb_relb_complete; auto.
    - intros ? ->%UnivExprSet.singleton_spec; auto.
    - intros ? ->%UnivExprSet.singleton_spec; auto.
  Qed.
  
  Lemma eqb_universe_instance_complete u u' :
    wf_universe_instance Σ u ->
    wf_universe_instance Σ u' ->
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
    wf_universe_level Σ u ->
    wf_universe_level Σ u' ->
    R_universe_variance (eq_universe Σ) (conv_pb_rel leq Σ) v u u' ->
    compare_universe_variance (check_eqb_universe G) (conv_pb_relb leq) v u u'.
  Proof.
    intros memu memu' r.
    destruct v; cbn in *; auto.
    - apply conv_pb_relb_make_complete; auto.
    - apply (conv_pb_relb_make_complete Conv); auto.
  Qed.

  Lemma compare_universe_instance_variance_complete leq v u u' :
    wf_universe_instance Σ u ->
    wf_universe_instance Σ u' ->
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
    wf_universe_instance Σ u ->
    wf_universe_instance Σ v ->
    R_global_instance Σ (eq_universe Σ) (conv_pb_rel leq Σ) gr napp u v ->
    compare_global_instance Σ (check_eqb_universe G) (conv_pb_relb leq) gr napp u v.
  Proof.
    intros consu consv r.
    unfold compare_global_instance, R_global_instance, R_opt_variance in *.
    destruct global_variance.
    - apply compare_universe_instance_variance_complete; auto.
    - apply eqb_universe_instance_complete; auto.
  Qed.
  
  Lemma consistent_instance_ext_wf udecl u :
    consistent_instance_ext Σ udecl u ->
    wf_universe_instance Σ u.
  Proof.
    intros cons.
    unfold consistent_instance_ext, consistent_instance in *.
    destruct udecl.
    - destruct u; cbn in *; [|congruence].
      constructor.
    - destruct cons as (mems&_&_).
      apply forallb_Forall in mems.
      eapply Forall_impl; eauto.
      cbn.
      intros ? ?%LevelSet.mem_spec; auto.
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

  Lemma red_conv_cum_l {leq Γ u v} :
    Σ ;;; Γ ⊢ u ⇝ v -> conv_cum leq Σ Γ u v.
  Proof.
    intros r. sq. now apply red_equality.
  Qed.

  Lemma red_conv_cum_r {leq Γ u v} :
    Σ ;;; Γ ⊢ u ⇝ v -> conv_cum leq Σ Γ v u.
  Proof.
    intros r. sq. now apply red_equality_inv.
  Qed.

  Lemma closed_red_zipp {Γ t u π} :
    is_open_term Γ (zipp t π) ->
    Σ ;;; Γ ⊢ t ⇝ u ->
    Σ ;;; Γ ⊢ zipp t π ⇝ zipp u π.
  Proof.
    intros cltπ [clΓ clt r].
    eapply into_closed_red; tea.
    now eapply red_zipp.
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
    eapply red_welltyped; tea.
    constructor. eapply red_zipc.
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
    etransitivity; try eassumption.
    eapply red_conv_cum_r ; try assumption.
    eapply closed_red_zipp. 
    * clear aux. eapply welltyped_zipc_zipp in h2; auto.
      eapply welltyped_is_open_term in h2.
      sq. now rewrite (All2_fold_length hx).
    * eapply into_closed_red; fvs.
      + eapply red_const. eassumption.
      + red in h. sq. fvs.
  Qed.
  Next Obligation.
    (* Contraposition of previous goal *)
    apply h; clear h.
    destruct hΣ.
    etransitivity ; try eassumption.
    eapply red_conv_cum_l ; try assumption.
    eapply closed_red_zipp.
    * clear aux; eapply welltyped_zipc_zipp in h2; auto.
      eapply welltyped_is_open_term in h2. sq. now rewrite (All2_fold_length hx).
    * eapply into_closed_red; fvs.
      + eapply red_const. eassumption.
      + sq. fvs.
  Qed.
  Next Obligation.
    eapply red_welltyped ; [auto| exact h1|].
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
    eapply closed_red_zipp.
    { eapply welltyped_zipc_zipp in h1; auto; fvs. }
    eapply into_closed_red; fvs.
    + eapply red_const. eassumption.
    + sq; fvs.
  Qed.
  Next Obligation.
    (* Contraposition of previous goal *)
    apply h; clear h.
    destruct hΣ as [wΣ].
    etransitivity ; try eassumption.
    eapply red_conv_cum_r ; try assumption.
    eapply closed_red_zipp.
    { eapply welltyped_zipc_zipp in h1; auto; fvs. }
    eapply into_closed_red; fvs.
    + eapply red_const. eassumption.
    + sq; fvs.
  Qed.
  Next Obligation.
    (* Both c and c' are axioms. Either they are different constants or they are not
       convertible because the universes are different. *)
    apply conv_cum_alt in H as [(?&?&[r1 r2 eq])]; auto.
    rewrite zipp_as_mkApps in r1, r2.
    symmetry in eq1, eq2.
    generalize hΣ. intros [].
    unshelve eapply closed_red_mkApps_tConst_axiom in r1 as (?&->&?); eauto.
    eapply closed_red_mkApps_tConst_axiom in r2 as (?&->&?); eauto.
    apply eq_termp_mkApps_inv in eq as (eq&?); [|easy|easy].
    depelim eq.
    destruct ne as [|(_&ne)]; [congruence|].
    
    clear aux.
    apply welltyped_zipc_tConst_inv in h1 as (cst1&decl1&cons1).
    apply welltyped_zipc_tConst_inv in h2 as (cst2&decl2&cons2).
    eapply declared_constant_inj in decl1; eauto; subst.
    apply consistent_instance_ext_wf in cons1.
    apply consistent_instance_ext_wf in cons2.
    eapply eqb_universe_instance_complete in r; auto.
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
    apply inversion_Case in typ as (mdecl&idecl&?&?&[]&?); auto.
    exists mdecl, idecl.
    split; [easy|].
    now apply All2i_length in brs_ty.
  Qed.
  
  Equations (noeqns) isconv_context_aux
            (Γ Γ' Δ Δ' : context)
            (cc : ∥Σ ⊢ Γ = Γ'∥)
            (check :
               forall (leq : conv_pb) (Δh : context_hole) (t : term) (Δh' : context_hole) (t' : term),
                 Δ = fill_context_hole Δh t ->
                 Δ' = fill_context_hole Δh' t' ->
                 ∥ context_equality_rel false Σ Γ (context_hole_context Δh) (context_hole_context Δh')∥ ->
                 ConversionResult (conv_cum leq Σ (Γ,,, context_hole_context Δh) t t'))
            (Δpre Δ'pre Δpost Δ'post : context)
            (eq : Δ = Δpre ,,, Δpost)
            (eq' : Δ' = Δ'pre ,,, Δ'post) :
    ConversionResult (∥context_equality_rel false Σ Γ Δpre Δ'pre∥) by struct Δpre := {

    isconv_context_aux Γ Γ' Δ Δ' cc check [] [] Δpost Δ'post eq eq' => yes;

    isconv_context_aux Γ Γ' Δ Δ' cc check
                           (mkdecl na bd ty :: Δpre)
                           (mkdecl na' bd' ty' :: Δ'pre)
                           Δpost Δ'post eq eq'
      with isconv_context_aux
             Γ Γ' Δ Δ' cc check Δpre Δ'pre
             (Δpost ++ [mkdecl na bd ty])
             (Δ'post ++ [mkdecl na' bd' ty']) _ _ := {

      | Error ce not_conv_rest => no ce;

      | Success conv_rest
        with inspect (eqb_binder_annot na na') := {
        
        | exist false neq_binders => no (ContextNotConvertibleAnn
                                           (Γ,,, Δpre) (mkdecl na bd ty)
                                           (Γ',,, Δ'pre) (mkdecl na' bd' ty'));

        | exist true eq_binders
          with check Conv
               (Δpre, decl_hole_type na bd, Δpost) ty
               (Δ'pre, decl_hole_type na' bd', Δ'post) ty'
               _ _ conv_rest := {

          | Error ce not_conv_type => no (ContextNotConvertibleType
                                            (Γ,,, Δpre) (mkdecl na bd ty)
                                            (Γ',,, Δ'pre) (mkdecl na' bd' ty'));

          | Success conv_type with bd, bd' := {
            
            | Some body | Some body'
                with check Conv
                     (Δpre, decl_hole_body na ty, Δpost) body
                     (Δ'pre, decl_hole_body na' ty', Δ'post) body'
                     _ _ conv_rest := {
              | Error ce not_conv_body => no (ContextNotConvertibleBody
                                                (Γ,,, Δpre) (mkdecl na bd ty)
                                                (Γ',,, Δ'pre) (mkdecl na' bd' ty'));
              
              | Success conv_body => yes
              };

            | None | None => yes;

            | _ | _ => no (ContextNotConvertibleBody
                             (Γ,,, Δpre) (mkdecl na bd ty)
                             (Γ',,, Δ'pre) (mkdecl na' bd' ty'))
            }
          }
        }
      };

    isconv_context_aux Γ Γ' Δ Δ' cc check
                       Δpre Δ'pre Δpost Δ'post eq eq' => no ContextNotConvertibleLength
    }.
  Next Obligation. 
    sq. constructor; fvs. constructor.
  Qed.
  Next Obligation.
    sq. depelim H. depelim a.
  Qed.
  Next Obligation.
    destruct H as [H]; depelim H. depelim a.
  Qed.
  Next Obligation.
    unfold app_context.
    rewrite <- app_assoc; auto.
  Qed.
  Next Obligation.
    unfold app_context.
    rewrite <- app_assoc; auto.
  Qed.
  Next Obligation.
    unfold conv_cum in conv_type, conv_body. sq.
    constructor; fvs.
    constructor; auto. 
    * now destruct conv_rest.
    * constructor; auto.
      apply eqb_annot_spec; auto.
  Qed.
  Next Obligation.
    destruct H as [H].
    contradiction not_conv_body.
    depelim H.
    depelim a. depelim a0.
    constructor; auto.
  Qed.
  Next Obligation.
    destruct H as [H].
    depelim H.
    depelim a. depelim a0.
  Qed.
  Next Obligation.
    destruct H as [H].
    depelim H. 
    depelim a. depelim a0.
  Qed.
  Next Obligation.
    red in conv_type. sq.
    constructor; fvs.
    constructor; auto. 
    * now destruct conv_rest.
    * constructor; auto.
      apply eqb_annot_spec; auto.
  Qed.
  Next Obligation.
    destruct H as [H].
    contradiction not_conv_type.
    depelim H.
    constructor.
    depelim a; auto. depelim a0; auto.
  Qed.
  Next Obligation.
    destruct H as [H].
    depelim H.
    depelim a. depelim a0.
    - apply eqb_annot_spec in eqna; congruence.
    - apply eqb_annot_spec in eqna; congruence.
  Qed.
  Next Obligation.
    destruct H as [H].
    contradiction not_conv_rest.
    depelim H.
    depelim a.
    constructor; auto. 
    split; auto.
  Qed.

  Definition isconv_context
            (Γ Γ' Δ Δ' : context)
            (cc : ∥ Σ ⊢ Γ = Γ' ∥)
            (check :
               forall (leq : conv_pb) (Δh : context_hole) (t : term) (Δh' : context_hole) (t' : term),
                 Δ = fill_context_hole Δh t ->
                 Δ' = fill_context_hole Δh' t' ->
                 ∥context_equality_rel false Σ Γ (context_hole_context Δh) (context_hole_context Δh')∥ ->
                 ConversionResult (conv_cum leq Σ (Γ,,, context_hole_context Δh) t t'))
    : ConversionResult (∥context_equality_rel false Σ Γ Δ Δ'∥) :=
    isconv_context_aux Γ Γ' Δ Δ' cc check Δ Δ' [] [] eq_refl eq_refl.

  Lemma case_conv_brs_inv {Γ ci br br' p c brs1 brs2 π}
  (h : wtp Γ (tCase ci p c (brs1 ++ br :: brs2)) π)
  (p' : predicate term) (c' : term) (brs1' brs2' : list (branch term))
  (π' : stack) (h' : wtp Γ (tCase ci p' c' (brs1' ++ br' :: brs2')) π')
  (hx : conv_stack_ctx Γ π π')
  (hp : ∥ equality_predicate Σ (Γ ,,, stack_context π) p p' ∥)
  (h1 : ∥ equality_brs Σ (Γ ,,, stack_context π) p brs1 brs1' ∥) :
  ∥ ∑ mdecl idecl,
    [× declared_inductive Σ ci mdecl idecl,
       #|pparams p| = ind_npars mdecl,
       #|pparams p'| = ind_npars mdecl,
       eq_context_gen eq eq br.(bcontext) br'.(bcontext),
       test_context_k (fun k : nat => on_free_vars (closedP k (fun _ : nat => true)))
         #|pparams p| br.(bcontext) &
       test_context_k (fun k : nat => on_free_vars (closedP k (fun _ : nat => true)))
         #|pparams p'| br'.(bcontext)] ∥.
  Proof.
    destruct hΣ.
    destruct hx as [hx].
    destruct hp as [hp].
    destruct h1 as [h1].
    eapply welltyped_zipc_zipp in h; auto.
    eapply welltyped_zipc_zipp in h'; auto.
    rewrite zipp_as_mkApps in h, h'.
    destruct h as [s h]. destruct h' as [s' h'].
    eapply PCUICValidity.inversion_mkApps in h as [A [hcase _]].
    eapply PCUICValidity.inversion_mkApps in h' as [A' [hcase' _]].
    destruct hp as []. 
    eapply inversion_Case in hcase as [mdecl [idecl [decli [indices [hcase _]]]]]; auto.
    eapply inversion_Case in hcase' as [mdecl' [idecl' [decli' [indices' [hcase' _]]]]]; auto.
    destruct (declared_inductive_inj decli decli'). subst mdecl' idecl'.
    constructor.
    assert (clm' : test_context_k (fun k : nat => on_free_vars (closedP k (fun _ : nat => true)))
      #|pparams p'| br'.(bcontext)).
    { rewrite test_context_k_closed_on_free_vars_ctx.
      destruct hcase'.
      eapply All2i_app_inv_r in brs_ty as (? & ? & ? & ? & ?).
      depelim a2. clear a1 a2.
      destruct p0 as [p0 _].
      cbn in p0.
      eapply alpha_eq_context_gen in p0.
      eapply PCUICConfluence.eq_context_upto_names_on_free_vars.
      2:symmetry; exact p0.
      rewrite <-closedn_ctx_on_free_vars.
      destruct ci. cbn.
      eapply PCUICClosed.closedn_ctx_upwards.
      { eapply (PCUICInstConv.closedn_ctx_cstr_branch_context (c:=(ci_ind, #|x|)) (idecl:=idecl)).
        split; auto. rewrite e0; cbn. rewrite nth_error_app_ge; auto.
        now rewrite Nat.sub_diag; cbn. }
      rewrite (wf_predicate_length_pars wf_pred).
      now rewrite (PCUICGlobalEnv.declared_minductive_ind_npars decli).
    }
    rewrite test_context_k_closed_on_free_vars_ctx.
    destruct hcase.
    eapply All2i_app_inv_r in brs_ty as (? & ? & ? & ? & ?).
    depelim a2. eapply All2i_length in a1; clear a2.
    destruct p0 as [p0 _].
    destruct hcase'.
    eapply All2i_app_inv_r in brs_ty as (? & ? & ? & ? & ?).
    depelim a3. eapply All2i_length in a2. clear a3.
    destruct p1 as [p1 _].
    rewrite e0 in e1. cbn in *. 
    pose proof (All2_length h1). rewrite <- a1 in H.
    rewrite <- a2 in H. eapply app_inj_length_l in e1 as [-> eq]; auto.
    noconf eq. exists mdecl, idecl.
    split; tea.
    - eapply (wf_predicate_length_pars wf_pred).
    - eapply (wf_predicate_length_pars wf_pred0).
    - eapply alpha_eq_context_gen. etransitivity; tea.
      now symmetry.
    - eapply alpha_eq_context_gen in p0.
      eapply PCUICConfluence.eq_context_upto_names_on_free_vars.
      2:symmetry; exact p0.
      rewrite <- closedn_ctx_on_free_vars.
      destruct ci. cbn.
      eapply PCUICClosed.closedn_ctx_upwards.
      { eapply (PCUICInstConv.closedn_ctx_cstr_branch_context (c:=(ci_ind, #|x0|)) (idecl:=idecl)).
        split; auto. rewrite e0; cbn. rewrite nth_error_app_ge; auto.
        now rewrite Nat.sub_diag; cbn. }
      rewrite (wf_predicate_length_pars wf_pred).
      now rewrite (PCUICGlobalEnv.declared_minductive_ind_npars decli).
  Qed.

  Equations isconv_branches (Γ : context)
    (ci : case_info)
    (p : predicate term) (c : term) (brs1 brs2 : list (branch term))
    (π : stack) (h : wtp Γ (tCase ci p c (brs1 ++ brs2)) π)
    (p' : predicate term) (c' : term) (brs1' brs2' : list (branch term))
    (π' : stack) (h' : wtp Γ (tCase ci p' c' (brs1' ++ brs2')) π')
    (hx : conv_stack_ctx Γ π π')
    (hp : ∥ equality_predicate Σ (Γ ,,, stack_context π) p p' ∥)
    (h1 : ∥ equality_brs Σ (Γ ,,, stack_context π) p brs1 brs1' ∥)
    (aux : Aux Term Γ (tCase ci p c (brs1 ++ brs2)) π (tCase ci p' c' (brs1' ++ brs2')) π' h')
    : ConversionResult (∥ equality_brs Σ (Γ ,,, stack_context π) p brs2 brs2' ∥)
    by struct brs2 :=

    isconv_branches Γ ci
      p c brs1 ({| bcontext := m; bbody := br |} :: brs2) π h
      p' c' brs1' ({| bcontext := m'; bbody := br' |} :: brs2') π' h' hx hp h1 aux
     with isconv_red_raw Conv
              br (Case_branch ci p c (brs1, branch_hole_body m, brs2) :: π)
              br' (Case_branch ci p' c' (brs1', branch_hole_body m', brs2') :: π') aux := {
      | Success h2
        with isconv_branches Γ ci
              p c (brs1 ++ [{|bcontext := m; bbody := br|}]) brs2 π _
              p' c' (brs1' ++ [{| bcontext := m'; bbody := br'|}]) brs2' π' _ hx hp _ _ := {
        | Success h3 := yes ;
        | Error e h'' := no e
        } ;
      | Error e nconv := no e
    } ;

    isconv_branches Γ ci
      p c brs1 [] π h
      p' c' brs1' [] π' h' hx hp h1 aux := yes ;

    isconv_branches Γ ci
      p c brs1 brs2 π h
      p' c' brs1' brs2' π' h' hx hp h1 aux := False_rect _ _.
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
    rewrite <- app_nil_r.
    rewrite stack_position_cons.
    eapply positionR_poscat.
    constructor.
  Qed.
  Next Obligation.
    eapply case_conv_brs_inv in h1; tea.
    sq. destruct h1 as [mdecl [idecl [decli eqp eqp' eqm clm clm']]].
    transitivity (Γ ,,, stack_context π ,,, inst_case_context (pparams p') (puinst p') m').
    - unfold app_context; rewrite <-app_assoc.
      inv_on_free_vars. 
      eapply inst_case_context_equality; tea. 
      * fvs.
      * eapply hp.
      * eapply hp.
    - unfold app_context. rewrite <- app_assoc. eapply context_equality_app_same; auto.
      rewrite on_free_vars_ctx_app.
      apply andb_true_iff. split; auto. 1:now apply context_equality_closed_left in hx.
      eapply on_free_vars_ctx_inst_case_context; trea.
      destruct hp.
      now eapply (equality_terms_open_terms_right a).
  Qed.
  Next Obligation.
    now rewrite <- app_assoc.
  Qed.
  Next Obligation.
    now rewrite <- app_assoc.
  Qed.
  Next Obligation.
    destruct (case_conv_brs_inv h p' c' brs1' brs2' _ h') as [[mdecl [idecl [decli eqp eqp' eqm clm clm']]]]; tea.
    destruct h1 as [h1], h2 as [h2].
    constructor. apply All2_app.
    - assumption.
    - constructor.
      2: now constructor.
      simpl.
      unfold zipp in h2.
      split; auto. 
      cbn in h2.
      unfold inst_case_branch_context. cbn.
      now unfold app_context; rewrite app_assoc.
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
    destruct (case_conv_brs_inv h p' c' brs1' brs2' _ h') as [[mdecl [idecl [decli eqp eqp' eqm clm clm']]]]; tea.
    destruct h2 as [h2], h3 as [h3].
    constructor.
    constructor; auto.
    unfold zipp in *; simpl in *.
    split; auto.
    rewrite app_context_assoc in h2; auto.
  Qed.
  Next Obligation.
    (* Contrapositive of previous obligation *)
    apply h''; clear h''.
    destruct H as [H]; inversion H; now constructor.
  Qed.
  Next Obligation.
    (* Contrapositive of 3rd obligation above *)
    apply nconv; clear nconv.
    destruct h1 as [h1], H as [h2].
    constructor. inversion h2; clear h2.
    destruct X as [_ h2]. simpl in h2. cbn.
    now rewrite app_context_assoc.
  Qed.
  
  Equations isconv_branches' (Γ : context)
    (ci : case_info)
    (p : predicate term) (c : term) (brs : list (branch term))
    (π : stack) (h : wtp Γ (tCase ci p c brs) π)
    (ci' : case_info)
    (p' : predicate term) (c' : term) (brs' : list (branch term))
    (π' : stack) (h' : wtp Γ (tCase ci' p' c' brs') π')
    (hx : conv_stack_ctx Γ π π')
    (hp : ∥ equality_predicate Σ (Γ ,,, stack_context π) p p' ∥)
    (ei : ci = ci')
    (aux : Aux Term Γ (tCase ci p c brs) π (tCase ci' p' c' brs') π' h')
    : ConversionResult (∥ equality_brs Σ (Γ ,,, stack_context π) p brs brs' ∥) :=

    isconv_branches' Γ ci p c brs π h ci' p' c' brs' π' h' hx hp eci aux :=
      isconv_branches Γ ci p c [] brs π _ p' c' [] brs' π' _ _ _ _ _.
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
  
  Definition mFix_mfix fk :=
    match fk with
    | IndFix => Fix
    | CoIndFix => CoFix
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

  Equations isequality_fix_types (fk : fix_kind) (Γ : context)
    (idx : nat)
    (mfix1 mfix2 : mfixpoint term) (π : stack)
    (h : wtp Γ (mFix fk (mfix1 ++ mfix2) idx) π)
    (mfix1' mfix2' : mfixpoint term) (π' : stack)
    (h' : wtp Γ (mFix fk (mfix1' ++ mfix2') idx) π')
    (hx : conv_stack_ctx Γ π π')
    (h1 : ∥ All2 (fun u v =>
                   Σ ;;; Γ ,,, stack_context π ⊢ u.(dtype) = v.(dtype) ×
                   (u.(rarg) = v.(rarg)) * eq_binder_annot u.(dname) v.(dname)
            ) mfix1 mfix1' ∥)
    (aux : Aux Term Γ (mFix fk (mfix1 ++ mfix2) idx) π (mFix fk (mfix1' ++ mfix2') idx) π' h')
    : ConversionResult (∥ All2 (fun u v =>
          Σ ;;; Γ ,,, stack_context π ⊢ u.(dtype) = v.(dtype) ×
          (u.(rarg) = v.(rarg)) * eq_binder_annot u.(dname) v.(dname)
      ) mfix2 mfix2' ∥)
    by struct mfix2 :=

    isequality_fix_types
      fk Γ idx mfix1 (u :: mfix2) π h mfix1' (v :: mfix2') π' h' hx h1 aux
    with inspect (eqb u.(rarg) v.(rarg)) := {
    | @exist true eq1
      with inspect (eqb_binder_annot u.(dname) v.(dname)) := {
      | @exist true eqann
        with isconv_red_raw Conv
             u.(dtype)
             (mFix_mfix fk (mfix1, def_hole_type u.(dname) u.(dbody) u.(rarg), mfix2) idx :: π)
             v.(dtype)
             (mFix_mfix fk (mfix1', def_hole_type v.(dname) v.(dbody) v.(rarg), mfix2') idx :: π')
             aux
      := {
      | Success h2 with
          isequality_fix_types fk Γ idx
            (mfix1 ++ [u]) mfix2 π _
            (mfix1' ++ [v]) mfix2' π' _
            hx _ _
        := {
        | Success h3 := yes ;
        | Error e h'' := no e
        } ;
      | Error e h'' := no e
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

    isequality_fix_types fk Γ idx mfix1 [] π h mfix1' [] π' h' hx h1 aux := yes ;

    (* TODO It might be more efficient to check the lengths first
       and then conclude this case is not possible.
    *)
    isequality_fix_types fk Γ idx mfix1 mfix2 π h mfix1' mfix2' π' h' hx h1 aux :=
      no (
        mFixMfixMismatch fk idx
          (Γ ,,, stack_context π) (mfix1 ++ mfix2)
          (Γ ,,, stack_context π') (mfix1' ++ mfix2')
      ).

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
    - rewrite <- app_nil_r, stack_position_cons. destruct fk.
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
    destruct fk; simpl in *; auto.
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
    apply h''; clear h''.
    destruct H as [H]; inversion H.
    constructor; assumption.
  Qed.  
  Next Obligation.
    destruct H as [H]; inversion H; destruct X as [eq_uv _].
    apply h''; clear h''; constructor.
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

  Lemma stack_entry_context_mFix_mfix_bd :
    forall fk na ty ra mfix1 mfix2 idx,
      stack_entry_context (mFix_mfix fk (mfix1, def_hole_body na ty ra, mfix2) idx) =
      fix_context_alt (map def_sig mfix1 ++ (na,ty) :: map def_sig mfix2).
  Proof.
    intros fk na ty ra mfix1 mfix2 idx.
    destruct fk. all: reflexivity.
  Qed.

  Equations isequality_fix_bodies (fk : fix_kind) (Γ : context) (idx : nat)
    (mfix1 mfix2 : mfixpoint term) (π : stack)
    (h : wtp Γ (mFix fk (mfix1 ++ mfix2) idx) π)
    (mfix1' mfix2' : mfixpoint term) (π' : stack)
    (h' : wtp Γ (mFix fk (mfix1' ++ mfix2') idx) π')
    (hx : conv_stack_ctx Γ π π')
    (h1 : ∥ All2 (fun u v => Σ ;;; Γ ,,, stack_context π ,,, fix_context_alt (map def_sig mfix1 ++ map def_sig mfix2) ⊢ u.(dbody) = v.(dbody)) mfix1 mfix1' ∥)
    (ha : ∥ All2 (fun u v =>
                    Σ ;;; Γ ,,, stack_context π ⊢ u.(dtype) = v.(dtype) ×
                    (u.(rarg) = v.(rarg)) * eq_binder_annot u.(dname) v.(dname)
           ) (mfix1 ++ mfix2) (mfix1' ++ mfix2') ∥)
    (aux : Aux Term Γ (mFix fk (mfix1 ++ mfix2) idx) π (mFix fk (mfix1' ++ mfix2') idx) π' h')
    : ConversionResult (∥ All2 (fun u v => Σ ;;; Γ ,,, stack_context π ,,, fix_context_alt (map def_sig mfix1 ++ map def_sig mfix2) ⊢ u.(dbody) = v.(dbody)) mfix2 mfix2' ∥)
    by struct mfix2 :=

  isequality_fix_bodies fk Γ idx mfix1 (u :: mfix2) π h mfix1' (v :: mfix2') π' h' hx h1 ha aux
  with isconv_red_raw Conv
        u.(dbody)
        (mFix_mfix fk (mfix1, def_hole_body u.(dname) u.(dtype) u.(rarg), mfix2) idx :: π)
        v.(dbody)
        (mFix_mfix fk (mfix1', def_hole_body v.(dname) v.(dtype) v.(rarg), mfix2') idx :: π')
        aux
  := {
  | Success h2
    with isequality_fix_bodies fk Γ idx
           (mfix1 ++ [u]) mfix2 π _
           (mfix1' ++ [v]) mfix2' π' _
           hx _ _ _
    := {
    | Success h3 := yes ;
    | Error e h'' := no e
    } ;
  | Error e h'' := no e
  } ;

  isequality_fix_bodies fk Γ idx mfix1 [] π h mfix1' [] π' h' hx h1 ha aux := yes ;

  isequality_fix_bodies fk Γ idx mfix1 mfix2 π h mfix1' mfix2' π' h' hx h1 ha aux :=
    False_rect _ _.

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
    - rewrite <- app_nil_r, stack_position_cons.
      destruct fk.
      + eapply positionR_poscat. constructor.
      + eapply positionR_poscat. constructor.
  Qed.
  Next Obligation.
    destruct hΣ as [wΣ], ha as [ha], hx as [hx].
    clear - wΣ ha hx. constructor.
    rewrite 2!stack_entry_context_mFix_mfix_bd.
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
        (fun d d' => (Σ ;;; Γ ⊢ d.2 = d'.2) * eq_binder_annot d.1 d'.1)
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
    | |- context_equality _ _ (_ ,,, List.rev ?l) (_ ,,, List.rev ?l') =>
      assert (hi :
        All2i (fun i d d' =>
          forall Ξ,
            is_closed_context (Γ ,,, Ξ) ->
            #|Ξ| = i ->
            equality_open_decls false Σ (Γ ,,, Ξ) d d'
        ) 0 l l'
      )
    end.
    { eapply All2i_mapi.
      generalize 0 at 3. intro n.
      induction h in n |- *. 1: constructor.
      constructor. 2: eapply IHh.
      destruct r.
      intros Ξ cl eΞ. constructor; tas.
      rewrite <- eΞ.
      eapply @weakening_equality with (Γ' := []). all: try assumption.

    }
    clear h.
    revert hi.
    match goal with
    | |- context [ context_equality _ _ (_ ,,, List.rev ?l) (_ ,,, List.rev ?l') ] =>
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
      forward IHh by lia.
      constructor.
      + eapply IHh.
      + eapply r0. 2:lia.
        fvs.
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
    apply h''; clear h''.
    destruct H as [H]; inversion H; constructor.
    rewrite map_app, <- app_assoc; simpl; assumption.
  Qed.  
  Next Obligation.
    apply h''; clear h''.
    destruct H as [H]; inversion H; constructor.
    destruct fk; cbn -[app_context].
    all: rewrite app_context_assoc; apply X.
  Qed.  

  Equations isequality_Fix (fk : fix_kind) (Γ : context)
    (mfix : mfixpoint term) (idx : nat) (π : stack)
    (h : wtp Γ (mFix fk mfix idx) π)
    (mfix' : mfixpoint term) (idx' : nat) (π' : stack)
    (h' : wtp Γ (mFix fk mfix' idx') π')
    (hx : conv_stack_ctx Γ π π')
    (ei : idx = idx')
    (aux : Aux Term Γ (mFix fk mfix idx) π (mFix fk mfix' idx') π' h')
    : ConversionResult (∥ All2 (fun u v =>
          Σ ;;; Γ ,,, stack_context π ⊢ u.(dtype) = v.(dtype) ×
          Σ ;;; Γ ,,, stack_context π ,,, fix_context mfix ⊢ u.(dbody) = v.(dbody) ×
          (u.(rarg) = v.(rarg)) * eq_binder_annot u.(dname) v.(dname)
      ) mfix mfix' ∥) :=

    isequality_Fix fk Γ mfix idx π h mfix' idx' π' h' hx ei aux
    with
      isequality_fix_types fk Γ idx
        [] mfix π _
        [] mfix' π' _
        hx _ _
    := {
    | Success h1
      with
        isequality_fix_bodies fk Γ idx
          [] mfix π _
          [] mfix' π' _
          hx _ _ _
      := {
      | Success h2 := yes ;
      | Error e h'' := no e
      } ;
    | Error e h'' := no e
    }.

  Next Obligation.
    unshelve eapply aux. all: eassumption.
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
    apply h''; clear h''.
    destruct H as [H]; constructor.
    apply (All2_impl H).
    rewrite <- fix_context_fix_context_alt. intuition.
  Qed.  
  Next Obligation.
    (* Contrapositive of pre-previous obligation *)
    apply h''; clear h''.
    destruct H as [H]; constructor; apply (All2_impl H).
    intuition.
  Qed.
  
  Lemma invert_type_mkApps_tProd Γ na A b args T :
    Σ;;; Γ |- mkApps (tProd na A b) args : T -> args = [].
  Proof.
    intros typ.
    destruct hΣ.
    apply PCUICValidity.inversion_mkApps in typ as (?&[typ_prod typ_args]).
    apply inversion_Prod in typ_prod as (?&?&?&?&?); [|easy].
    eapply PCUICSpine.typing_spine_strengthen in typ_args; eauto.
    2:{ eapply PCUICArities.isType_Sort. 2:pcuic.
        eapply wf_universe_product; now eapply typing_wf_universe. }
    clear -typ_args.
    depelim typ_args.
    - easy.
    - now apply equality_Sort_Prod_inv in e.
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
    rewrite mkApps_app in wh.
    cbn in wh. destruct wh as (?&typ); auto.
    change (tApp ?h ?a) with (mkApps h [a]) in typ.
    rewrite <-mkApps_app in typ.
    now apply invert_type_mkApps_tProd in typ.
  Qed.

  Lemma reduced_case_discriminee_whne Γ π ci p c brs h :
    eqb_term (reduce_term
                RedFlags.default
                Σ heΣ (Γ,,, stack_context π) c h) c = true ->
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
  
  Lemma welltyped_zipp_inv Γ t π : welltyped Σ Γ (zipp t π) -> welltyped Σ Γ t.
  Proof.
    sq.
    induction π; cbn; auto.
    unfold zipp.
    destruct decompose_stack.
    intros [s' Hs].
    eapply PCUICValidity.inversion_mkApps in Hs as [? []].
    now exists x.
  Qed.

  Lemma inv_reduced_discriminees_case leq Γ π π' ci ci' p p' c c' brs brs' h h' :
    conv_stack_ctx Γ π π' ->
    true = eqb_term (reduce_term
                       RedFlags.default
                       Σ heΣ (Γ,,, stack_context π) c h) c ->
    true = eqb_term (reduce_term
                       RedFlags.default
                       Σ heΣ (Γ,,, stack_context π') c' h') c' ->
    welltyped Σ Γ (zipc (tCase ci p c brs) π) ->
    welltyped Σ Γ (zipc (tCase ci' p' c' brs') π') ->
    isred_full Γ (tCase ci p c brs) π ->
    isred_full Γ (tCase ci' p' c' brs') π' ->
    conv_cum
      leq Σ (Γ,,, stack_context π)
      (zipp (tCase ci p c brs) π)
      (zipp (tCase ci' p' c' brs') π') ->
    ∥[× ci = ci',
     equality_predicate Σ (Γ,,, stack_context π) p p',
     Σ;;; Γ,,, stack_context π ⊢ c = c',
     equality_brs Σ (Γ,,, stack_context π) p brs brs' &
     equality_terms Σ (Γ,,, stack_context π) (decompose_stack π).1 (decompose_stack π').1]∥.
  Proof.
    intros [] c_is_red%eq_sym c'_is_red%eq_sym wtc wtc' isr1 isr2 cc.
    eapply reduced_case_discriminee_whne in c_is_red as wh1; eauto.
    eapply reduced_case_discriminee_whne in c'_is_red as wh2; eauto.
    destruct hΣ, wh1 as [wh1], wh2 as [wh2].
    rewrite !zipp_as_mkApps in cc.
    eapply whne_conv_context in wh2.
    2:{ symmetry in X. eapply context_equality_forget in X. exact X. }
    apply conv_cum_mkApps_inv in cc as [(equality_Case&conv_args)]; eauto using whnf_mkApps.
    red in isr1.
    eapply welltyped_zipc_zipp, welltyped_zipp_inv in wtc. 2:sq; auto.
    eapply welltyped_zipc_zipp, welltyped_zipp_inv in wtc'. 2:sq; auto.
    destruct wtc. eapply inversion_Case in X1 as [mdecl [idecl [isdecl [indices [[] ?]]]]]; tea.
    destruct wtc'. eapply inversion_Case in X1 as [mdecl' [idecl' [isdecl' [indices' [[] ?]]]]] ; tea.
    eapply conv_cum_tCase_inv in equality_Case; eauto.
    destruct equality_Case as [[<- ? ? ?]].
    split; split; auto.
  Qed.

  Lemma reduced_proj_body_whne Γ π p c h :
    true = eqb_term (reduce_term
                RedFlags.default
                Σ heΣ (Γ,,, stack_context π) c h) c ->
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
                       Σ heΣ (Γ,,, stack_context π) c h) c ->
    true = eqb_term (reduce_term
                       RedFlags.default
                       Σ heΣ (Γ,,, stack_context π') c' h') c' ->
    isred_full Γ (tProj p c) π ->
    isred_full Γ (tProj p' c') π' ->
    conv_cum leq Σ (Γ,,, stack_context π) (zipp (tProj p c) π) (zipp (tProj p' c') π') ->
    ∥p = p' ×
     Σ;;; Γ,,, stack_context π ⊢ c = c' ×
     equality_terms Σ (Γ,,, stack_context π) (decompose_stack π).1 (decompose_stack π').1∥.
  Proof.
    intros [] c_is_red c'_is_red isr1 isr2 cc.
    eapply reduced_proj_body_whne in c_is_red as wh1; eauto.
    eapply reduced_proj_body_whne in c'_is_red as wh2; eauto.
    destruct hΣ, wh1 as [wh1], wh2 as [wh2].
    rewrite !zipp_as_mkApps in cc.
    eapply whne_conv_context in wh2.
    2:{ symmetry in X. eapply context_equality_forget in X. exact X. }
    apply conv_cum_mkApps_inv in cc as [(conv_proj&conv_args)]; eauto using whnf_mkApps.
    eapply conv_cum_tProj_inv in conv_proj; eauto.
    destruct conv_proj as [(<-&?)].
    constructor; auto.
  Qed.
  
  Lemma conv_cum_red_conv_inv leq Γ Γ' t1 t2 t1' t2' :
    context_equality false Σ Γ Γ' ->
    red Σ Γ t1 t1' ->
    red Σ Γ' t2 t2' ->
    sq_equality leq Σ Γ t1 t2 ->
    sq_equality leq Σ Γ t1' t2'.
  Proof.
    sq.
    intros. eapply conv_cum_red_conv_inv; eauto.
    all:eapply into_closed_red; tea. 
    * fvs.
    * destruct H; fvs.
    * fvs.
    * destruct H. rewrite <-(All2_fold_length X). now eapply equality_is_open_term_right.
  Qed.

  Lemma inv_stuck_fixes leq Γ mfix idx π mfix' idx' π' h h' :
    conv_stack_ctx Γ π π' ->
    None = unfold_one_fix Γ mfix idx π h ->
    None = unfold_one_fix Γ mfix' idx' π' h' ->
    conv_cum leq Σ (Γ,,, stack_context π) (zipp (tFix mfix idx) π) (zipp (tFix mfix' idx') π') ->
    ∥[× idx = idx',
     All2 (fun d d' =>
             rarg d = rarg d' × eq_binder_annot d.(dname) d'.(dname) ×
             Σ;;; Γ,,, stack_context π ⊢ dtype d = dtype d' ×
             Σ;;; Γ,,, stack_context π,,, fix_context mfix ⊢ dbody d = dbody d')
          mfix mfix' &
     equality_terms Σ (Γ,,, stack_context π) (decompose_stack π).1 (decompose_stack π').1]∥.
  Proof.
    intros [?] uf1 uf2 cc.
    rewrite !zipp_as_mkApps in cc.
    apply unfold_one_fix_None in uf1 as [(?&?&?)].
    apply unfold_one_fix_None in uf2 as [(?&?&?)].
    destruct hΣ.
    eapply conv_cum_red_conv_inv in cc.
    2: eassumption.
    2: eapply red_mkApps; [reflexivity|exact a].
    2: apply red_mkApps; [reflexivity|exact a0].
    apply conv_cum_mkApps_inv in cc as [(equality_Fix&conv_args)]; auto.
    2:{ eapply whnf_conv_context; eauto.
        symmetry in X. now eapply context_equality_forget in X. }
    apply conv_cum_tFix_inv in equality_Fix as [(<-&?)]; auto.
    sq; split; auto. 
    * eapply All2_impl; tea; cbn. intros ? ? []. repeat split; auto.
    * eapply equality_terms_red_conv; eauto.
      all:eapply into_red_terms; tea.
      1,3:fvs.
      + eapply welltyped_zipc_zipp in h; auto.
        destruct h as [s h].
        rewrite zipp_as_mkApps in h.
        eapply subject_is_open_term in h.
        rewrite on_free_vars_mkApps in h. now apply andb_true_iff in h.
      + eapply welltyped_zipc_zipp in h'; auto.
        destruct h' as [s h'].
        rewrite zipp_as_mkApps in h'.
        eapply subject_is_open_term in h'.
        rewrite on_free_vars_mkApps in h'. now apply andb_true_iff in h'.
  Qed.

  Lemma inv_stuck_cofixes leq Γ mfix idx π mfix' idx' π' :
    conv_stack_ctx Γ π π' ->
    conv_cum leq Σ (Γ,,, stack_context π) (zipp (tCoFix mfix idx) π) (zipp (tCoFix mfix' idx') π') ->
    ∥idx = idx' ×
     All2 (fun d d' =>
             rarg d = rarg d' × eq_binder_annot d.(dname) d'.(dname) ×
             Σ;;; Γ,,, stack_context π ⊢ dtype d = dtype d' ×
             Σ;;; Γ,,, stack_context π,,, fix_context mfix ⊢ dbody d = dbody d')
          mfix mfix' ×
     equality_terms Σ (Γ,,, stack_context π) (decompose_stack π).1 (decompose_stack π').1∥.
  Proof.
    intros [?] cc.
    rewrite !zipp_as_mkApps in cc.
    destruct hΣ.
    apply conv_cum_mkApps_inv in cc as [(equality_CoFix&conv_args)]; auto.
    apply conv_cum_tCoFix_inv in equality_CoFix as [(<-&?)]; auto.
    constructor; split; [|split]; auto.
    eapply All2_impl; tea. intros ? ? []. repeat split; auto.
  Qed.
  
  Equations (noeqns) isconv_predicate_params_aux
            (Γ : context)
            (ci1 : case_info)
            (p1 : predicate term) (c1 : term) (brs1 : list (branch term))
            (π1 : stack)
            (h1 : wtp Γ (tCase ci1 p1 c1 brs1) π1)
            (ci2 : case_info)
            (p2 : predicate term) (c2 : term) (brs2 : list (branch term))
            (π2 : stack) (h2 : wtp Γ (tCase ci2 p2 c2 brs2) π2)
            (hx : conv_stack_ctx Γ π1 π2)
            (aux : Aux Term Γ (tCase ci1 p1 c1 brs1) π1 (tCase ci2 p2 c2 brs2) π2 h2)
            (pre1 pre2 post1 post2 : list term)
            (eq1 : p1.(pparams) = pre1 ++ post1)
            (eq2 : p2.(pparams) = pre2 ++ post2) :
    ConversionResult (∥equality_terms Σ (Γ,,, stack_context π1) post1 post2∥) :=
    isconv_predicate_params_aux
      Γ ci1 p1 c1 brs1 π1 h1 ci2 p2 c2 brs2 π2 h2
      hx aux pre1 pre2 [] [] eq1 eq2 => yes;
    
    isconv_predicate_params_aux
      Γ ci1 p1 c1 brs1 π1 h1 ci2 p2 c2 brs2 π2 h2
      hx aux pre1 pre2 (t1 :: post1) (t2 :: post2) eq1 eq2
      with isconv_red_raw
           Conv
           t1 (Case_pred
                 ci1
                 (pred_hole_params pre1 post1 p1.(puinst) p1.(pcontext) p1.(preturn))
                 c1 brs1 :: π1)
           t2 (Case_pred
                 ci2
                 (pred_hole_params pre2 post2 p2.(puinst) p2.(pcontext) p2.(preturn))
                 c2 brs2 :: π2) aux := {
      
      | Error ce not_conv_term => no ce;

      | Success conv_tm
          with isconv_predicate_params_aux
               Γ ci1 p1 c1 brs1 π1 h1 ci2 p2 c2 brs2 π2 h2 hx aux
               (pre1 ++ [t1]) (pre2 ++ [t2]) post1 post2 _ _ := {
        
        | Error ce not_conv_rest => no ce;
        
        | Success conv_rest => yes
        }
      };

    isconv_predicate_params_aux
      Γ ci1 p1 c1 brs1 π1 h1 ci2 p2 c2 brs2 π2 h2 hx aux
      pre1 pre2 post1 post2 eq eq2 => no (CasePredParamsUnequalLength
                                            (Γ,,, stack_context π1) ci1 p1 c1 brs1
                                            (Γ,,, stack_context π2) ci2 p2 c2 brs2).
  Next Obligation.
    destruct H as [H].
    depelim H.
  Qed.
  Next Obligation.
    destruct H as [H].
    depelim H.
  Qed.
  Next Obligation.
    destruct p1; auto.
  Qed.
  Next Obligation.
    destruct p2; auto.
  Qed.
  Next Obligation.
    apply R_positionR. all: simpl.
    1: destruct p1; cbn in *; subst; reflexivity.
    rewrite stack_position_cons.
    rewrite <- app_nil_r.
    eapply positionR_poscat.
    constructor.
  Qed.
  Next Obligation.
    rewrite <- app_assoc; auto.
  Qed.
  Next Obligation.
    rewrite <- app_assoc; auto.
  Qed.
  Next Obligation.
    destruct conv_tm, conv_rest.
    unfold zipp in X; simpl in *.
    constructor; constructor; auto.
  Qed.
  Next Obligation.
    contradiction not_conv_rest.
    destruct H as [H]; depelim H.
    constructor; auto.
  Qed.
  Next Obligation.
    contradiction not_conv_term.
    destruct H as [H]; depelim H.
    constructor; auto.
  Qed.

  Lemma case_conv_preds_inv {Γ ci p c brs brs' π}
  (h : wtp Γ (tCase ci p c brs) π)
  (p' : predicate term) (c' : term) 
  (π' : stack) (h' : wtp Γ (tCase ci p' c' brs') π')
  (hx : conv_stack_ctx Γ π π')
  (huinst : R_universe_instance (eq_universe Σ) (puinst p) (puinst p'))
  (hp : ∥ equality_terms Σ (Γ,,, stack_context π) (pparams p) (pparams p') ∥) :
  ∥ ∑ mdecl idecl,
    [× declared_inductive Σ ci mdecl idecl,
       #|pparams p| = ind_npars mdecl,
       #|pparams p'| = ind_npars mdecl,
       eq_context_gen eq eq p.(pcontext) p'.(pcontext),
       test_context_k (fun k : nat => on_free_vars (closedP k (fun _ : nat => true)))
         #|pparams p| p.(pcontext) &
       test_context_k (fun k : nat => on_free_vars (closedP k (fun _ : nat => true)))
         #|pparams p'| p'.(pcontext)] ∥.
  Proof.
    destruct hΣ.
    destruct hx as [hx].
    destruct hp as [hp].
    eapply welltyped_zipc_zipp in h; auto.
    eapply welltyped_zipc_zipp in h'; auto.
    rewrite zipp_as_mkApps in h, h'.
    destruct h as [s h]. destruct h' as [s' h'].
    eapply PCUICValidity.inversion_mkApps in h as [A [hcase _]].
    eapply PCUICValidity.inversion_mkApps in h' as [A' [hcase' _]].
    eapply inversion_Case in hcase as [mdecl [idecl [decli [indices [hcase _]]]]]; auto.
    eapply inversion_Case in hcase' as [mdecl' [idecl' [decli' [indices' [hcase' _]]]]]; auto.
    destruct (declared_inductive_inj decli decli'). subst mdecl' idecl'.
    constructor.
    assert (clp : test_context_k (fun k : nat => on_free_vars (closedP k (fun _ : nat => true)))
      #|pparams p| p.(pcontext)).
    { rewrite test_context_k_closed_on_free_vars_ctx.
      destruct hcase.
      eapply alpha_eq_context_gen in conv_pctx.
      eapply PCUICConfluence.eq_context_upto_names_on_free_vars.
      2:symmetry; exact conv_pctx.
      rewrite <- closedn_ctx_on_free_vars.
      eapply PCUICClosed.closedn_ctx_upwards.
      { eapply (closed_ind_predicate_context); tea.
        eapply declared_minductive_closed; tea. exact decli'. }
      rewrite (wf_predicate_length_pars wf_pred).
      now rewrite (PCUICGlobalEnv.declared_minductive_ind_npars decli).
    }
    rewrite test_context_k_closed_on_free_vars_ctx.
    exists mdecl, idecl.
    destruct hcase. destruct hcase'.
    split; tea.
    - eapply (wf_predicate_length_pars wf_pred).
    - eapply (wf_predicate_length_pars wf_pred0).
    - eapply alpha_eq_context_gen. etransitivity; tea.
      now symmetry. 
    - now rewrite <- test_context_k_closed_on_free_vars_ctx.
    - rewrite test_context_k_closed_on_free_vars_ctx. 
      eapply alpha_eq_context_gen in conv_pctx0.
      eapply PCUICConfluence.eq_context_upto_names_on_free_vars.
      2:symmetry; exact conv_pctx0.
      rewrite <- closedn_ctx_on_free_vars.
      relativize #|pparams p'|.
      { eapply (closed_ind_predicate_context); tea.
        eapply declared_minductive_closed; tea. exact decli'. }
      rewrite (wf_predicate_length_pars wf_pred0).
      now rewrite (PCUICGlobalEnv.declared_minductive_ind_npars decli).
  Qed.

  Definition isconv_predicate_params
            (Γ : context)
            (ci1 : case_info)
            (p1 : predicate term) (c1 : term) (brs1 : list (branch term))
            (π1 : stack)
            (h1 : wtp Γ (tCase ci1 p1 c1 brs1) π1)
            (ci2 : case_info)
            (p2 : predicate term) (c2 : term) (brs2 : list (branch term))
            (π2 : stack) (h2 : wtp Γ (tCase ci2 p2 c2 brs2) π2)
            (hx : conv_stack_ctx Γ π1 π2)
            (aux : Aux Term Γ (tCase ci1 p1 c1 brs1) π1 (tCase ci2 p2 c2 brs2) π2 h2) :=
    isconv_predicate_params_aux Γ ci1 p1 c1 brs1 π1 h1 ci2 p2 c2 brs2 π2 h2 hx aux [] []
                                p1.(pparams) p2.(pparams) eq_refl eq_refl.
  
  Equations (noeqns) isconv_predicate
            (Γ : context)
            (ci1 : case_info)
            (p1 : predicate term) (c1 : term) (brs1 : list (branch term))
            (π1 : stack)
            (h1 : wtp Γ (tCase ci1 p1 c1 brs1) π1)
            (ci2 : case_info)
            (p2 : predicate term) (c2 : term) (brs2 : list (branch term))
            (π2 : stack) (h2 : wtp Γ (tCase ci2 p2 c2 brs2) π2)
            (hx : conv_stack_ctx Γ π1 π2)
            (eqci : ci1 = ci2)
            (aux : Aux Term Γ (tCase ci1 p1 c1 brs1) π1 (tCase ci2 p2 c2 brs2) π2 h2)
    : ConversionResult (∥equality_predicate Σ (Γ,,, stack_context π1) p1 p2∥) :=

    isconv_predicate Γ ci1 p1 c1 brs1 π1 h1 ci2 p2 c2 brs2 π2 h2 hx eqci aux
      with isconv_predicate_params
           Γ ci1 p1 c1 brs1 π1 h1 ci2 p2 c2 brs2 π2 h2 hx aux := {

      | Error ce not_conv_params => no ce;

      | Success conv_params
        with inspect (eqb_universe_instance p1.(puinst) p2.(puinst)) := {

        | exist false not_eq_insts => no (CasePredUnequalUniverseInstances
                                            (Γ,,, stack_context π1) ci1 p1 c1 brs1
                                            (Γ,,, stack_context π2) ci2 p2 c2 brs2);

        | exist true eq_insts
            with isconv_red_raw
                 Conv p1.(preturn)
                      (Case_pred ci1 (pred_hole_return p1.(pparams) p1.(puinst) p1.(pcontext))
                                 c1 brs1 :: π1)
                      p2.(preturn)
                      (Case_pred ci2 (pred_hole_return p2.(pparams) p2.(puinst) p2.(pcontext))
                                 c2 brs2 :: π2)
                      aux := {

            | Error ce not_conv_ret => no ce;

            | Success conv_ret => yes
          }
        }
      }.
  Next Obligation.
    destruct p1; cbn in *; subst; auto.
  Qed.
  Next Obligation.
    destruct p2; cbn in *; subst; auto.
  Qed.
  Next Obligation.
    apply R_positionR. all: simpl.
    1: destruct p1; cbn in *; subst; reflexivity.
    rewrite stack_position_cons.
    rewrite <- app_nil_r.
    eapply positionR_poscat.
    constructor.
  Qed.
  Next Obligation.
    destruct hΣ.
    apply eq_sym, eqb_universe_instance_spec in eq_insts.
    destruct (case_conv_preds_inv h1 _ _ _ h2 hx eq_insts conv_params) as []; tea.
    destruct hx as [hx].
    destruct conv_params as [conv_params].
    constructor.
    unfold app_context; rewrite <- !app_assoc.
    destruct X0 as [mdecl [idecl []]].
    etransitivity.
    * inv_on_free_vars. eapply (inst_case_context_equality d e e0 i i0); tea. fvs.
    * eapply context_equality_app_same. 2:eapply hx.
      rewrite on_free_vars_ctx_app.
      apply andb_true_iff. split; auto. 
      1:now eapply context_equality_closed_left in hx.
      eapply on_free_vars_ctx_inst_case_context; trea.
      fvs.
  Qed.
  Next Obligation.
    unfold zipp in conv_ret; simpl in conv_ret.
    apply eq_sym, eqb_universe_instance_spec in eq_insts.
    destruct (case_conv_preds_inv h1 _ _ _ h2 hx eq_insts conv_params) as []; tea.
    destruct hx as [hx]. destruct conv_params as [conv_params].
    destruct conv_ret as [h].
    split. split; auto.
    2:rewrite app_context_assoc in h; auto.
    now destruct X as [mdecl [idecl []]].
  Qed.
  Next Obligation.
    unfold zipp in not_conv_ret; simpl in not_conv_ret.
    contradiction not_conv_ret.
    rewrite app_context_assoc.
    destruct H as [[]]; constructor; auto.
  Qed.
  Next Obligation.
    destruct hΣ.
    zip fold in h1.
    apply welltyped_context in h1 as (?&typ1); auto.
    apply inversion_Case in typ1 as (?&?&?&?&[]&?); auto.
    zip fold in h2.
    clear aux.
    apply welltyped_context in h2 as (?&typ2); auto.
    apply inversion_Case in typ2 as (?&?&?&?&[]&?); auto.
    apply consistent_instance_ext_wf in cons.
    apply consistent_instance_ext_wf in cons0.
    destruct H as [[]].
    apply eqb_universe_instance_complete in r; auto.
    congruence.
  Qed.
  Next Obligation.
    contradiction not_conv_params.
    destruct H as [[]]; constructor; auto.
  Qed.

  Lemma conv_cum_red_inv leq Γ t1 t2 t1' t2' :
    red Σ Γ t1 t1' ->
    red Σ Γ t2 t2' ->
    sq_equality leq Σ Γ t1 t2 ->
    sq_equality leq Σ Γ t1' t2'.
  Proof.
    intros. destruct hΣ.
    destruct H. eapply conv_cum_red_inv; tea. 3:split; eauto.
    all:eapply into_closed_red; tea; fvs.
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
      with isconv_red_raw Conv A1 (Lambda_ty na t1 :: π1)
                               A2 (Lambda_ty na' t2 :: π2) aux := {
      | Success h with inspect (eqb_binder_annot na na') := {
        | exist true _ :=
          isconv_red leq
                     t1 (Lambda_bd na A1 :: π1)
                     t2 (Lambda_bd na' A2 :: π2) aux ;
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
      with isconv_red_raw Conv A1 (Prod_l na B1 :: π1) A2 (Prod_l na' B2 :: π2) aux := {
      | Success h  with inspect (eqb_binder_annot na na') := {
        | exist true _ :=
          isconv_red leq
                   B1 (Prod_r na A1 :: π1)
                   B2 (Prod_r na' A2 :: π2) aux ;
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

    | prog_view_Case ci p c brs ci' p' c' brs'
      with inspect (reduce_term RedFlags.default Σ heΣ (Γ ,,, stack_context π1) c _) := {
      | @exist cred eq1 with inspect (eqb_term cred c) := {
        | @exist true eq2 with inspect (reduce_term RedFlags.default Σ heΣ (Γ ,,, stack_context π2) c' _) := {
          | @exist cred' eq3 with inspect (eqb_term cred' c') := {
            | @exist true eq4 with inspect (eqb ci ci') := {
              | @exist true eq5
                  with isconv_predicate Γ ci p c brs π1 _ ci' p' c' brs' π2 _ _ _ aux := { 
                | Success convp with isconv_red_raw Conv
                                  c (Case_discr ci p brs :: π1)
                                  c' (Case_discr ci' p' brs' :: π2) aux := {
                  | Success convdiscr with isconv_branches' Γ ci p c brs π1 _ ci' p' c' brs' π2 _ _ _ _ aux := {
                    | Success convbrs with isconv_args_raw leq (tCase ci p c brs) π1 (tCase ci' p' c' brs') π2 aux := {
                      | Success convargs := yes ;
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

    | prog_view_Proj p c p' c' with inspect (reduce_term RedFlags.default Σ heΣ (Γ ,,, stack_context π1) c _) := {
      | @exist cred eq1 with inspect (eqb_term cred c) := {
        | @exist true eq3 with inspect (reduce_term RedFlags.default Σ heΣ (Γ ,,, stack_context π2) c' _) := {
          | @exist cred' eq2 with inspect (eqb_term cred' c') := {
            | @exist true eq4 with inspect (eqb p p') := {
              | @exist true eq5 with isconv_red_raw Conv c (Proj p :: π1) c' (Proj p' :: π2) aux := {
                | Success convdiscr := isconv_args leq (tProj p c) π1 (tProj p' c') π2 aux ;
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
          with inspect (reduce_stack RedFlags.nodelta Σ heΣ (Γ ,,, stack_context θ') fn (appstack l' []) _) := {
          | @exist (fn', ρ) eq3 :=
            isconv_prog leq fn' (ρ ++ θ') (tFix mfix' idx') π2 aux
          }
        } ;
      | @exist None eee with inspect (unfold_one_fix Γ mfix' idx' π2 _) := {
        | @exist (Some (fn, θ)) eq1
          with inspect (decompose_stack θ) := {
          | @exist (l', θ') eq2
            with inspect (reduce_stack RedFlags.nodelta Σ heΣ (Γ ,,, stack_context θ') fn (appstack l' []) _) := {
            | @exist (fn', ρ) eq3 :=
              isconv_prog leq (tFix mfix idx) π1 fn' (ρ ++ θ') aux
            }
          } ;
        | @exist None eq1 with inspect (eqb idx idx') := {
          | @exist true eq4 with isequality_Fix IndFix Γ mfix idx π1 _ mfix' idx' π2 _ _ _ aux := {
            | Success convfix with isconv_args_raw leq (tFix mfix idx) π1 (tFix mfix' idx') π2 aux := {
              | Success convargs := yes ;
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
      | @exist true eq4 with isequality_Fix CoIndFix Γ mfix idx π1 _ mfix' idx' π2 _ _ _ aux := {
        | Success convfix with isconv_args_raw leq (tCoFix mfix idx) π1 (tCoFix mfix' idx') π2 aux := {
          | Success convargs := yes ;
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
    destruct hΣ.
    apply conv_cum_zipp; auto.
    constructor. eapply equality_eq_le_gen.
    constructor. all:fvs. 
    - destruct h. eapply welltyped_zipc_zipp in h1; auto. fvs.
    - constructor. eapply eqb_universe_instance_spec. auto.
  Qed.
  Next Obligation.
    eapply red_welltyped ; [auto|..].
    - exact h1.
    - constructor. eapply red_zipc.
      eapply red_const. eassumption.
  Qed.
  Next Obligation.
    eapply red_welltyped ; [auto|..].
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
      eapply closed_red_zipp. 1:eapply welltyped_zipc_zipp in h1; fvs.
      eapply into_closed_red.
      * eapply red_const. eassumption.
      * eapply welltyped_zipc_zipp in h1; fvs.
      * eapply welltyped_zipc_zipp in h1; fvs.
    - etransitivity ; try eassumption.
      eapply red_conv_cum_r ; try assumption.
      eapply closed_red_zipp; auto.
      2:{ eapply into_closed_red; auto.
        * eapply red_const. eassumption.
        * eapply welltyped_zipc_zipp in h1; fvs. }
      clear aux. eapply welltyped_zipc_zipp in h2; auto.
      destruct hx as [hx]. rewrite (All2_fold_length hx); fvs.
  Qed.
  Next Obligation.
    apply h; cbn; clear h.
    destruct hΣ.
    eapply conv_cum_red_inv.
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
    - simpl. rewrite <- app_nil_r, stack_position_cons. eapply positionR_poscat. constructor.
  Qed.
  Next Obligation.
    unshelve eapply R_positionR.
    - reflexivity.
    - simpl. rewrite <- app_nil_r, stack_position_cons. eapply positionR_poscat. constructor.
  Qed.
  Next Obligation.
    destruct hx as [hx].
    destruct h as [h].
    constructor. constructor. 1: assumption.
    constructor.
    - symmetry in e. now apply eqb_binder_annot_spec.
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
    symmetry in e; apply eqb_binder_annot_spec in e.
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
    symmetry in e; apply eqb_binder_annot_spec in e.
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
    - simpl. rewrite <- app_nil_r, stack_position_cons. eapply positionR_poscat. constructor.
  Qed.
  Next Obligation.
    unshelve eapply R_positionR.
    - simpl. reflexivity.
    - simpl. rewrite <- app_nil_r, stack_position_cons. eapply positionR_poscat. constructor.
  Qed.
  Next Obligation.
    destruct hx as [hx].
    destruct h as [h].
    constructor. constructor. 1: assumption.
    constructor.
    - symmetry in e.
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
    destruct h.
    symmetry in e.
    apply eqb_binder_annot_spec in e.
    split; eapply equality_Prod; auto.
  Qed.
  Next Obligation.
    (* Codomains are not convertible *)
    apply h; clear h.
    symmetry in e. apply eqb_binder_annot_spec in e.
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
    destruct hh as [mdecl [idecl [isdecl [indices [[] cum]]]]].
    eexists. eassumption.
  Qed.
  Next Obligation.
    destruct hΣ as [wΣ].
    clear aux.
    zip fold in h2. apply welltyped_context in h2 ; auto. simpl in h2.
    destruct h2 as [T h2].
    apply inversion_Case in h2 as hh ; auto.
    destruct hh as [mdecl [idecl [isdecl [indices [[] cum]]]]].
    eexists. eassumption.
  Qed.
  Next Obligation.
    change (eq_dec_to_bool ci ci') with (eqb ci ci') in eq5.
    destruct (eqb_spec ci ci'). 2: discriminate.
    assumption.
  Qed.
  Next Obligation.
    eapply R_positionR. all: simpl.
    1: reflexivity.
    rewrite <- app_nil_r, stack_position_cons.
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
    destruct convp as [h1'], convbrs as [h2'], convargs as [h3].
    destruct convdiscr as [cdiscr]. cbn in cdiscr.
    unfold zipp in h1, h2. simpl in h1, h2.
    pose proof hΣ as wΣ. destruct wΣ.
    constructor.
    apply equality_eq_le_gen.
    change (eq_dec_to_bool ci ci') with (eqb ci ci') in eq5.
    destruct (eqb_spec ci ci'). 2: discriminate.
    subst. eapply equality_Case. all: tas.
    * clear aux eq2 eq4. eapply welltyped_zipc_zipp in h1; auto.
      eapply welltyped_is_open_term in h1.
      rewrite zipp_as_mkApps in h1.
      rewrite on_free_vars_mkApps in h1.
      now apply andb_true_iff in h1 as [].
    * clear aux eq2 eq4. eapply welltyped_zipc_zipp in h2; auto.
      eapply welltyped_is_open_term in h2.
      rewrite zipp_as_mkApps in h2.
      rewrite on_free_vars_mkApps in h2.
      destruct hx as [hx]. 
      unfold is_open_case. rewrite (All2_fold_length hx).
      now apply andb_true_iff in h2 as [].
  Qed.
  Next Obligation.
    apply h; clear h.
    eapply inv_reduced_discriminees_case in H as [[<-]]; eauto.
  Qed.
  Next Obligation.
    apply h; cbn; clear h.
    eapply inv_reduced_discriminees_case in H as [[<-]]; eauto.
  Qed.
  Next Obligation.
    apply h; cbn; clear h.
    eapply inv_reduced_discriminees_case in H as [[<-]]; eauto.
    constructor; auto.
  Qed.
  Next Obligation.
    apply h; cbn; clear h.
    eapply inv_reduced_discriminees_case in H as [[<-]]; eauto.
  Qed.
  Next Obligation.
    eapply inv_reduced_discriminees_case in H as [[<-]]; eauto.
    change (eqb ci ci) with (eq_dec_to_bool ci ci) in eq5.
    rewrite eq_dec_to_bool_refl in eq5.
    congruence.
  Qed.
  Next Obligation.
    eapply red_welltyped ; [auto|..].
    - exact h2.
    - match goal with
      | |- context [ reduce_term ?f ?Σ ?hΣ ?Γ ?t ?h ] =>
        pose proof (reduce_term_sound f Σ hΣ Γ t h) as [hr]
      end.
      constructor.
      eapply red_zipc.
      eapply red_case_c; auto. eapply hr.
  Qed.
  Next Obligation.
    match goal with
    | |- context [ reduce_term ?f ?Σ ?hΣ ?Γ c' ?h ] =>
      destruct (reduce_stack_Req f Σ hΣ Γ c' [] h) as [e' | hr]
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
    - eapply conv_cum_conv_ctx; tea.
      eapply red_conv_cum_r ; try assumption.
      eapply into_closed_red.
      * eapply red_zipp.
        eapply red_case_c. eapply hr.
      * fvs.
      * clear aux eq4 h hr.
        eapply welltyped_zipc_zipp in h2; fvs.
  Qed.
  Next Obligation.
    apply h; clear h.
    pose proof hΣ as [].
    destruct hx.
    epose proof (reduce_term_sound _ _ _ _ _ _) as [r].
    eapply conv_cum_red_conv_inv.
    1,2,4: tea.
    1: reflexivity.
    apply red_zipp.
    apply red_case_c.
    exact r.
  Qed.

  Next Obligation.
    eapply red_welltyped ; [auto|..].
    - exact h1.
    - match goal with
      | |- context [ reduce_term ?f ?Σ ?hΣ ?Γ ?t ?h ] =>
        pose proof (reduce_term_sound f Σ hΣ Γ t h) as [hr]
      end.
      constructor.
      eapply red_zipc.
      apply red_case_c, hr.
  Qed.
  Next Obligation.
    match goal with
    | |- context [ reduce_term ?f ?Σ ?hΣ ?Γ c ?h ] =>
      destruct (reduce_stack_Req f Σ hΣ Γ c [] h) as [e' | hr]
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
      eapply into_closed_red.
      * eapply red_zipp.
        eapply red_case_c, hr.
      * fvs.
      * clear eq3 h hr; eapply welltyped_zipc_zipp in h1; fvs.
    - assumption.
  Qed.
  Next Obligation.
    apply h; clear h.
    pose proof hΣ as [].
    destruct hx.
    epose proof (reduce_term_sound _ _ _ _ _ _) as [r].
    eapply conv_cum_red_inv.
    3: eassumption.
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
    - rewrite <- app_nil_r, stack_position_cons. apply positionR_poscat. constructor.
  Qed.
  Next Obligation.
    unshelve eapply R_stateR.
    all: try reflexivity.
    simpl. constructor.
  Qed.
  Next Obligation.
    destruct convdiscr as [h1'].
    change (true = eqb p p') in eq5.
    destruct (eqb_spec p p'). 2: discriminate. subst.
    apply conv_cum_zipp; auto.
    clear eq3 eq4 aux. destruct hΣ. eapply conv_conv_cum_l.
    now eapply equality_Proj_c.
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
    rewrite PCUICParallelReductionConfluence.eqb_refl in eq5. discriminate.
    (* rewrite eq_prod_refl in eq5.
      eauto using eq_prod_refl, Nat.eqb_refl, eq_string_refl, eq_inductive_refl. *)
  Qed.
  Next Obligation.
    eapply red_welltyped ; [auto|..].
    - exact h2.
    - match goal with
      | |- context [ reduce_term ?f ?Σ ?hΣ ?Γ ?t ?h ] =>
        pose proof (reduce_term_sound f Σ hΣ Γ t h) as [hr]
      end.
      constructor.
      eapply red_zipc.
      eapply red_proj_c, hr.
  Qed.
  Next Obligation.
    match goal with
    | |- context [ reduce_term ?f ?Σ ?hΣ ?Γ c' ?h ] =>
      destruct (reduce_stack_Req f Σ hΣ Γ c' [] h) as [e' | hr]
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
    - eapply conv_cum_conv_ctx; tea.
      eapply red_conv_cum_r ; try assumption.
      eapply into_closed_red.
      * eapply red_zipp.
        eapply red_proj_c, hr.
      * fvs.
      * clear hr h eq4 aux. eapply welltyped_zipc_zipp in h2; fvs.
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
    eapply red_conv_cum_l ; try assumption.
    eapply into_closed_red.
    * eapply red_zipp.
      eapply red_proj_c, hr.
    * fvs.
    * clear eq4 aux hr. eapply welltyped_zipc_zipp in h2; fvs.
  Qed.
  Next Obligation.
    eapply red_welltyped ; [auto|..].
    - exact h1.
    - match goal with
      | |- context [ reduce_term ?f ?Σ ?hΣ ?Γ ?t ?h ] =>
        pose proof (reduce_term_sound f Σ hΣ Γ t h) as [hr]
      end.
      constructor.
      eapply red_zipc.
      eapply red_proj_c, hr.
  Qed.
  Next Obligation.
    match goal with
    | |- context [ reduce_term ?f ?Σ ?hΣ ?Γ c ?h ] =>
      destruct (reduce_stack_Req f Σ hΣ Γ c [] h) as [e' | hr]
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
      eapply into_closed_red.
      * eapply red_zipp.
        eapply red_proj_c, hr.
      * fvs.
      * clear eq3 aux hr h. eapply welltyped_zipc_zipp in h1; fvs.
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
      eapply into_closed_red.
      * eapply red_zipp.
        eapply red_proj_c, hr.
      * fvs.
      * clear hr H eq3. eapply welltyped_zipc_zipp in h1; fvs.
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
    eapply clrel_rel in r2.
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
  Lemma wt_zip_mkapps Γ f π : welltyped Σ Γ (zipc f π) -> is_open_term (Γ ,,, stack_context π) (mkApps f (decompose_stack π).1).
  Proof.
    intros. apply welltyped_zipc_zipp in H; auto.
    rewrite zipp_as_mkApps in H. destruct hΣ; fvs.
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
    etransitivity. 2:eauto.
    eapply into_closed_red; tea; [fvs|].
    eapply (f_equal stack_context) in d1.
    rewrite !stack_context_decompose in d1. rewrite <- d1.
    now eapply wt_zip_mkapps.
  Qed.
  Next Obligation.
    apply h; clear h.
    apply unfold_one_fix_red_zipp in eq1 as r1.
    apply unfold_one_fix_decompose in eq1 as d1.
    reduce_stack_facts.
    simpl_reduce_stack.
    destruct hΣ, r1 as [r1].
    eapply conv_cum_red_inv.
    * exact r.
    * auto.
    * etransitivity; eauto.
      split. eapply equality_eq_le_gen. symmetry.
      eapply red_equality.
      eapply into_closed_red.
      + eapply r1.
      + fvs.
      + eapply (f_equal stack_context) in d1.
        rewrite !stack_context_decompose in d1. rewrite <- d1.
        now eapply wt_zip_mkapps.
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
    apply clrel_rel, red_context_zip in r2.
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
    do 2 zip fold. eapply red_context_zip, r2.
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
    1,4: eauto.
    * eapply closed_red_refl; [fvs|].
      now eapply wt_zip_mkapps.
    * etransitivity; eauto. 
      eapply into_closed_red.
      + eapply r1.
      + fvs.
      + eapply (f_equal stack_context) in d1.
        rewrite !stack_context_decompose in d1. rewrite <- d1.
        now eapply wt_zip_mkapps.
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
    1,4: eauto.
    * eapply closed_red_refl. 1:fvs.
      now eapply wt_zip_mkapps.
    * etransitivity; eauto. eapply r.
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
    destruct convfix as [h1'].
    destruct hΣ.
    eapply conv_conv_cum_l.
    change (true = eqb idx idx') in eq4.
    destruct (eqb_spec idx idx'). 2: discriminate.
    subst.
    eapply equality_Fix; auto.
    clear aux eee. eapply welltyped_zipc_zipp in h1; fvs.
  Qed.
  Next Obligation.
    apply h; clear h.
    eapply inv_stuck_fixes in H as [[<-]]; eauto.
  Qed.
  Next Obligation.
    apply h; clear h.
    eapply inv_stuck_fixes in H as [[<-]]; eauto.
    constructor; auto.
    eapply All2_impl; eauto.
    cbn; intros; easy.
  Qed.
  Next Obligation.
    eapply inv_stuck_fixes in H as [[<-]]; eauto.
    rewrite PCUICParallelReductionConfluence.eqb_refl in idx_uneq.
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
    destruct convfix as [h1'].
    destruct hΣ.
    eapply conv_conv_cum_l.
    change (true = eqb idx idx') in eq4.
    destruct (eqb_spec idx idx'). 2: discriminate.
    subst.
    eapply equality_CoFix; auto.
    clear aux h1'. eapply welltyped_zipc_zipp in h1; fvs.
  Qed.
  Next Obligation.
    apply h; clear h.
    eapply inv_stuck_cofixes in H as [(<-&?&?)]; eauto.
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
    rewrite PCUICParallelReductionConfluence.eqb_refl in idx_uneq.
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
      (h1' : wtp Γ u1 (App_r (mkApps t1 ca1) :: appstack a1 π1))
      (h2' : wtp Γ u2 ρ2),
      let x :=
        mkpack Γ Reduction u1 (App_r (mkApps t1 ca1) :: (appstack a1 π1)) u2 ρ2 h2'
      in
      let y := mkpack Γ Args (mkApps t1 args1) (appstack l1 π1) t2 π2 h2 in
      (S #|ca1| + #|a1| = #|args1| + #|l1|)%nat ->
      pzt x = pzt y /\
      positionR (` (pps1 x)) (` (pps1 y)) ->
      Ret Reduction Γ u1 (App_r (mkApps t1 ca1) :: (appstack a1 π1)) u2 ρ2.

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
    : ConversionResult (∥equality_terms Σ (Γ,,, stack_context π1) l1 l2∥) by struct l1 :=
    _isconv_args' leq Γ t1 args1 (u1 :: l1) π1 h1 hπ1 t2 (u2 :: l2) π2 h2 hπ2 hx aux
    with aux u1 u2 args1 l1 (App_r t2 :: (appstack l2 π2)) _ _ _ _ Conv _ I I I := {
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
    destruct H as [H]; depelim H.
  Qed.
  Next Obligation.
    destruct H as [H]; depelim H.
  Qed.
  Next Obligation.
    split. 1: reflexivity.
    rewrite !stack_position_cons.
    eapply positionR_poscat. constructor.
  Defined.
  Next Obligation.
    rewrite 2!stack_context_appstack.
    assumption.
  Qed.
  Next Obligation.
    rewrite mkApps_app. assumption.
  Defined.
  Next Obligation.
    simpl in H0. destruct H0 as [eq hp].
    rewrite app_length in H. cbn in H.
    eapply aux. all: auto.
    - cbn. lia.
    - instantiate (1 := h2'). simpl. split.
      + rewrite mkApps_app in eq. assumption.
      + subst x y.
        rewrite !stack_position_cons, !stack_position_appstack.
        rewrite <- !app_assoc. apply positionR_poscat.
        assert (h' : forall n m, positionR (repeat app_l n ++ [app_r]) (repeat app_l m)).
        { clear. intro n. induction n ; intro m.
          - destruct m ; constructor.
          - destruct m.
            + constructor.
            + cbn. constructor. apply IHn.
        }
        simpl.
        rewrite <- repeat_snoc.
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
    : ConversionResult (∥equality_terms Σ (Γ,,, stack_context π1)
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
    with inspect (reduce_stack RedFlags.default Σ heΣ Γ c [] _) := {
    | @exist (cred, ρ) eq with cc_viewc cred := {
      | ccview_construct ind' n ui with inspect (decompose_stack ρ) := {
        | @exist (args, ξ) eq' with inspect (nth_error brs n) := {
          | exist (Some br) eqbr := Some (iota_red ci.(ci_npar) p args br) ;
          | exist None eqbr := False_rect _ _ }
        } ;
      | ccview_cofix mfix idx with inspect (unfold_cofix mfix idx) := {
        | @exist (Some (narg, fn)) eq2 with inspect (decompose_stack ρ) := {
          | @exist (args, ξ) eq' := Some (tCase ci p (mkApps fn args) brs)
          } ;
        | @exist None eq2 := False_rect _ _
        } ;
      | ccview_other cred _ := None
      }
    }.
  Next Obligation.
    destruct hΣ as [wΣ].
    cbn. destruct h as [T h].
    apply inversion_Case in h ; auto.
    destruct h as [mdecl [idecl [isdecl [indices [[] cum]]]]].
    eexists. eassumption.
  Qed.
  Next Obligation.
    simpl_reduce_stack.
    destruct hΣ.
    assert (r' : ∥ red Σ Γ (tCase ci p c brs)
      (tCase ci p (mkApps (tConstruct ind' n ui) (decompose_stack ρ).1) brs) ∥).
    { constructor. eapply red_case_c, r. }
    pose proof (red_welltyped _ hΣ h r') as h'.
    destruct h'.
    apply PCUICInductiveInversion.invert_Case_Construct in X0 as (?&?&?&?); auto.
    congruence.
  Qed.
  
  Next Obligation.
    exfalso.
    simpl_reduce_stack.
    destruct h as (?&typ); auto.
    destruct hΣ.
    apply inversion_Case in typ as [mdecl [idecl [isdecl [indices [[] cum]]]]]; auto.
    eapply PCUICSR.subject_reduction in scrut_ty. 2:auto. 2:exact r.
    eapply PCUICValidity.inversion_mkApps in scrut_ty as (?&typ&?); auto.
    apply inversion_CoFix in typ as (?&?&?&?&?&?&?); auto.
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
    all:try Program.Tactics.bang.
    all: intros eq'' ; noconf eq''.
    - clear H H0 H1.
      simpl_reduce_stack.
      assert (r' : ∥ red Σ Γ (tCase ci p c brs)
          (tCase ci p (mkApps (tConstruct ind' n ui) (decompose_stack ρ).1) brs) ∥).
      { constructor. eapply red_case_c, r. }
      pose proof (red_welltyped _ hΣ h r') as h'.
      eapply Case_Construct_ind_eq in h' ; eauto. subst.
      eapply cored_red_cored.
      + constructor. eapply red_iota. 1: now symmetry.
        destruct h as (?&typ).
        destruct r' as [r'].
        destruct hΣ.
        eapply PCUICSR.subject_reduction in typ; eauto.
        apply PCUICInductiveInversion.invert_Case_Construct in typ as (?&?&?&?); auto.
        rewrite H0 in eqbr; noconf eqbr.
        rewrite skipn_length; lia.
      + eapply red_case_c, r.
    - clear H H0 H1.
      simpl_reduce_stack.
      assert (r' : ∥ red Σ Γ (tCase ci p c brs)
                     (tCase ci p (mkApps (tCoFix mfix idx) (decompose_stack ρ).1) brs) ∥).
      { constructor. eapply red_case_c, r. }
      pose proof (red_welltyped _ hΣ h r') as h'.
      eapply cored_red_cored.
      + constructor. eapply red_cofix_case. eauto.
      + eapply red_case_c, r.
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
      constructor; exists (mkApps cred (decompose_stack ρ).1).
      split; [exact r|].
      specialize (isr eq_refl) as (noapp&_).
      eapply PCUICSR.subject_reduction in typ.
      2: eauto.
      2: eapply red_case_c, r.
      eapply whnf_case_arg_whne; eauto.
      now destruct cred.
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
    | (i, pars, narg) with inspect (reduce_stack RedFlags.default Σ heΣ Γ c [] _) := {
      | @exist (cred, ρ) eq with cc0_viewc cred := {
        | cc0view_construct ind' ui with inspect (decompose_stack ρ) := {
          | @exist (args, ξ) eq' with inspect (nth_error args (pars + narg)) := {
            | @exist (Some arg) eq2 := Some arg ;
            | @exist None eq2 := False_rect _ _
            }
          } ;
        | cc0view_cofix mfix idx with inspect (decompose_stack ρ) := {
          | @exist (args, ξ) eq' with inspect (unfold_cofix mfix idx) := {
            | @exist (Some (rarg, fn)) eq2 :=
              Some (tProj (i, pars, narg) (mkApps fn args)) ;
            | @exist None eq2 := False_rect _ _
            }
          } ;
        | cc0view_other cred _ := None
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
    2: apply red_proj_c, r.
    apply PCUICInductiveInversion.invert_Proj_Construct in typ as (<-&_&?); auto.
    apply eq_sym, nth_error_None in eq2.
    lia.
  Qed.
  Next Obligation.
    simpl_reduce_stack.
    destruct h as (?&typ); auto.
    destruct hΣ.
    apply inversion_Proj in typ as (?&?&?&?&?&?&?&?&?&?); auto.
    eapply PCUICSR.subject_reduction in t. 2:eauto. 2:exact r.
    apply PCUICValidity.inversion_mkApps in t as (?&?&?); auto.
    apply inversion_CoFix in t as (?&?&?&?&?&?&?); auto.
    unfold unfold_cofix in eq2.
    rewrite e1 in eq2.
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
    all: intros eq'' ; noconf eq''.
    - clear H H0 H1.
      simpl_reduce_stack.
      pose proof (red_proj_c (i, pars, narg) _ _ r) as r'.
      pose proof (red_welltyped _ hΣ h (sq r')) as h'.
      apply Proj_Construct_ind_eq in h' ; auto. subst.
      eapply cored_red_cored.
      + constructor. eapply red_proj. eauto.
      + eapply red_proj_c, r.
    - match type of eq'' with
      | _ = False_rect _ ?f => destruct f
      end.
    - clear H H0 H1.
      simpl_reduce_stack.
      pose proof (red_proj_c (i, pars, narg) _ _ r) as r'.
      pose proof (red_welltyped _ hΣ h (sq r')) as h'.
      eapply cored_red_cored.
      + constructor. eapply red_cofix_proj. eauto.
      + eapply red_proj_c, r.
    - match type of eq'' with
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
      constructor; exists (mkApps cred (decompose_stack ρ).1).
      split; [exact r|].
      specialize (isr eq_refl) as (noapp&_).
      eapply PCUICSR.subject_reduction in typ.
      2: eauto.
      2: eapply red_proj_c, r.
      eapply whnf_proj_arg_whne ; eauto.
      1: exact heΣ.
      now destruct cred.
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
    - apply unfold_one_case_cored in eq as r. apply cored_red in r.
      destruct r as [r].
      constructor. simpl_stacks.
      eapply red_mkApps_f.
      assumption.
    - apply unfold_one_proj_cored in eq as r. apply cored_red in r.
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
      case_eq (decompose_stack π). intros l s eq'.
      eapply red_it_mkLambda_or_LetIn. eapply red_mkApps_f.
      eapply trans_red.
      + reflexivity.
      + eapply red_delta.
        * unfold declared_constant. eauto.
        * reflexivity.
    - apply unfold_one_case_cored in eq as r. apply cored_red in r.
      destruct r as [r].
      constructor. unfold zippx.
      case_eq (decompose_stack π). intros l s e'.
      eapply red_it_mkLambda_or_LetIn. eapply red_mkApps_f.
      apply decompose_stack_eq in e'. subst.
      rewrite stack_context_appstack in r. assumption.
    - apply unfold_one_proj_cored in eq as r. apply cored_red in r.
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
    rewrite mkApps_app in teq.
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
      constructor; exists (tCase ci p c' brs), (decompose_stack π).1.
      split.
      + destruct p. constructor; eauto with pcuic.
      + split; [eauto with pcuic|].
        apply whnf_mkApps.
        auto.
    - clear H.
      apply unfold_one_proj_None in e as [(c'&r&whproj)].
      constructor; exists (tProj p c'), (decompose_stack π).1.
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
        with inspect (reduce_stack RedFlags.nodelta Σ heΣ (Γ ,,, stack_context ρ1) rt1 (appstack l1 []) _) := {
        | @exist (rt1', θ1') eq3 :=
          isconv_prog leq rt1' (θ1' ++ θ1) t2 π2 aux
        }
      } ;
    | @exist None nored1 with inspect (reducible_head Γ t2 π2 h2) := {
      | @exist (Some (rt2, ρ2)) eq1 with inspect (decompose_stack ρ2) := {
        | @exist (l2, θ2) eq2
          with inspect (reduce_stack RedFlags.nodelta Σ heΣ (Γ ,,, stack_context ρ2) rt2 (appstack l2 []) _) := {
          | @exist (rt2', θ2') eq3 :=
            isconv_prog leq t1 π1 rt2' (θ2' ++ θ2) aux
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
    eapply red_welltyped; revgoals. 3:auto.
    - constructor. zip fold. eapply red_context_zip. simpl_stacks. exact r.
    - cbn. simpl_stacks.
      eapply red_welltyped. 1:auto.
      2:{ constructor. exact r1. }
      eassumption.
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
    repeat zip fold. eapply red_context_zip, r2.
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
    eapply red_conv_cum_l; try assumption.
    etransitivity ; try eassumption.
    eapply into_closed_red; tea.
    * fvs.
    * eapply (f_equal stack_context) in d1.
      rewrite !stack_context_decompose in d1. rewrite <- d1.
      now eapply wt_zip_mkapps.
  Qed.
  Next Obligation.
    apply h; clear h.
    apply reducible_head_red_zipp in eq1 as r1. destruct r1 as [r1].
    apply reducible_head_decompose in eq1 as d1.
    simpl_reduce_stack.
    destruct hΣ as [wΣ].
    etransitivity ; try eassumption.
    eapply red_conv_cum_r ; try assumption.
    etransitivity; tea.
    eapply (f_equal stack_context) in d1.
    rewrite !stack_context_decompose in d1.
    eapply into_closed_red; [exact r1|..]. 1:fvs.
    rewrite <- d1. now eapply wt_zip_mkapps.
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
    eapply red_welltyped; [auto|..] ; revgoals.
    - constructor. zip fold. eapply red_context_zip, r2.
    - rewrite zipc_appstack in r1. cbn.
      eapply red_welltyped ; [auto|..] ; revgoals.
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
    repeat zip fold. eapply red_context_zip, r2.
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
    - eapply red_conv_cum_r.
      etransitivity; tea.
      eapply into_closed_red; [exact r1|..]. 1:fvs.
      eapply (f_equal stack_context) in d1.
      rewrite !stack_context_decompose in d1.
      eapply into_closed_red; [exact r1|..]. 1:fvs.
      rewrite <- d1. now eapply wt_zip_mkapps.
    - exact hx.
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
    - eapply red_conv_cum_l.
      etransitivity; tea.
      eapply (f_equal stack_context) in d1.
      rewrite !stack_context_decompose in d1.
      eapply into_closed_red; [exact r1|..]. 1:fvs.
      rewrite <- d1; now eapply wt_zip_mkapps.
    - exact hx.
  Qed.
  Next Obligation.
    eapply R_stateR. all: simpl. all: try reflexivity.
    constructor.
  Qed.
  Next Obligation.
    destruct h, hΣ.
    apply equality_terms_alt in X as (argsr&argsr'&[]).
    rewrite !zipp_as_mkApps.
    apply conv_cum_alt; auto.
    constructor; eexists _, _.
    split.
    - apply PCUICInductiveInversion.closed_red_mkApps; tea.
      * clear aux nored1. eapply welltyped_zipc_zipp in h1; fvs.
      * clear aux nored1. eapply wt_zip_mkapps in h1.
        rewrite on_free_vars_mkApps in h1. now apply andb_true_iff in h1.
    - apply PCUICInductiveInversion.closed_red_mkApps; tea.
      * clear aux nored1. eapply welltyped_zipc_zipp in h1; fvs.
      * clear aux nored1 nored2. eapply wt_zip_mkapps in h1.
        eapply wt_zip_mkapps in h2. destruct hx.
        rewrite (All2_fold_length X). 
        rewrite on_free_vars_mkApps in h2. now apply andb_true_iff in h2.
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
    2: eassumption.
    2: apply red_mkApps; eassumption.
    2: apply red_mkApps; eassumption.
    apply conv_cum_mkApps_inv in H as [(?&?)]; auto.
    2: now depelim s1.
    2: now depelim s2.
    2: eapply whnf_conv_context; eauto.
    2: symmetry in X0; eapply context_equality_forget in X0; eauto.
    constructor.
    eapply equality_terms_red_conv; eauto.
    all:eapply into_red_terms; tea.
    1:fvs. 2:fvs.
    all:clear aux. 
    * eapply wt_zip_mkapps in h1.
      rewrite on_free_vars_mkApps in h1. now apply andb_true_iff in h1 as [].
    * eapply wt_zip_mkapps in h2.
      rewrite on_free_vars_mkApps in h2. now apply andb_true_iff in h2 as [].
  Qed.

  Lemma leq_rel_conv_pb_dir leq : leq_rel (conv_pb_dir leq) = conv_pb_rel leq.
  Proof. destruct leq; reflexivity. Qed.

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
    2: eassumption.
    2: apply red_mkApps; eassumption.
    2: apply red_mkApps; eassumption.
    apply conv_cum_mkApps_inv in H as [(conv_hds&_)]; auto.
    2: now inversion s1; subst.
    2: now inversion s2; subst.
    2: eapply whnf_conv_context; eauto.
    2: { symmetry in X0. eapply context_equality_forget in X0; tea. }
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
         apply consistent_instance_ext_wf in c0.
         apply consistent_instance_ext_wf in c.
         rewrite leq_rel_conv_pb_dir in H3.
         apply compare_global_instance_complete in H3; auto.
         rewrite PCUICParallelReductionConfluence.eqb_refl in noteq.
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
         apply consistent_instance_ext_wf in c0.
         apply consistent_instance_ext_wf in c.
         rewrite leq_rel_conv_pb_dir in H4.
         apply compare_global_instance_complete in H4; auto.
         rewrite !PCUICParallelReductionConfluence.eqb_refl in noteq.
         apply All2_length in rargs1.
         rewrite <- rargs1 in H4.
         cbn in *.
         easy. }
    all: apply conv_cum_alt in conv_hds as [(?&?&[r1 r2 ?])]; auto.
    all: eapply whnf_red_inv in r1; auto.
    all: inversion r1; subst; clear r1.
    all: inversion c; subst; clear c.
    all: apply whnf_mkApps_inv in wh2.
    all: eapply whnf_conv_context in wh2; [|symmetry in X0; eapply context_equality_forget in X0; exact X0].
    all: eapply whnf_red_inv in r2; auto.
    all: inversion r2; subst; clear r2.
    all: inversion s2; subst; clear s2.
    all: destruct hdiscr.
    all: try now rewrite PCUICParallelReductionConfluence.eqb_refl in noteq.
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
      rewrite leq_rel_conv_pb_dir in H0.      
      eapply conv_pb_relb_complete in H0; eauto.
      congruence.
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

  Program Definition isconv_term Γ leq t1 (h1 : welltyped Σ Γ t1) t2 (h2 : welltyped Σ Γ t2) :=
    isconv Γ leq t1 [] h1 t2 [] h2 _.
    
  Next Obligation.
    destruct h1.
    sq. eapply context_equality_refl. fvs.
  Qed.
  
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
