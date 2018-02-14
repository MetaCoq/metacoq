From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast LiftSubst Typing.
From Translation
     Require Import SAst SLiftSubst SCommon XTyping ITyping PackLifts.

Section Translation.

Open Scope type_scope.
Open Scope x_scope.
Open Scope i_scope.

Axiom cheating : forall {A}, A.
Tactic Notation "cheat" := (apply cheating).

(*! Relation for translated expressions *)

Reserved Notation " t1 ∼ t2 " (at level 20).

Inductive trel : sterm -> sterm -> Type :=
| trel_Rel x :
    sRel x ∼ sRel x

| trel_Transport_l t1 t2 T1 T2 p :
    t1 ∼ t2 ->
    sTransport T1 T2 p t1 ∼ t2

| trel_Transport_r t1 t2 T1 T2 p :
    t1 ∼ t2 ->
    t1 ∼ sTransport T1 T2 p t2

| trel_Prod n1 n2 A1 A2 B1 B2 :
    A1 ∼ A2 ->
    B1 ∼ B2 ->
    sProd n1 A1 B1 ∼ sProd n2 A2 B2

| trel_Eq A1 A2 u1 u2 v1 v2 :
    A1 ∼ A2 ->
    u1 ∼ u2 ->
    v1 ∼ v2 ->
    sEq A1 u1 v1 ∼ sEq A2 u2 v2

| trel_Sort s :
    sSort s ∼ sSort s

| trel_Lambda n1 n2 A1 A2 B1 B2 u1 u2 :
    A1 ∼ A2 ->
    B1 ∼ B2 ->
    u1 ∼ u2 ->
    sLambda n1 A1 B1 u1 ∼ sLambda n2 A2 B2 u2

| trel_App u1 u2 n1 n2 A1 A2 B1 B2 v1 v2 :
    u1 ∼ u2 ->
    A1 ∼ A2 ->
    B1 ∼ B2 ->
    v1 ∼ v2 ->
    sApp u1 n1 A1 B1 v1 ∼ sApp u2 n2 A2 B2 v2

| trel_Refl A1 A2 u1 u2 :
    A1 ∼ A2 ->
    u1 ∼ u2 ->
    sRefl A1 u1 ∼ sRefl A2 u2

where " t1 ∼ t2 " := (trel t1 t2).

Derive Signature for trel.

(* We also define a biased relation that only allows transports on one side,
   the idea being that the term on the other side belongs to the source.
   This might be unnecessary as transport isn't typable in the source but
   hopefully this is more straightforward.
 *)
Reserved Notation " t ⊏ t' " (at level 20).

(* The first is in the source, the second in the target. *)
Inductive inrel : sterm -> sterm -> Type :=
| inrel_Rel x :
    sRel x ⊏ sRel x

| inrel_Transport t t' T1 T2 p :
    t ⊏ t' ->
    t ⊏ sTransport T1 T2 p t'

| inrel_Prod n n' A A' B B' :
    A ⊏ A' ->
    B ⊏ B' ->
    sProd n A B ⊏ sProd n' A' B'

| inrel_Eq A A' u u' v v' :
    A ⊏ A' ->
    u ⊏ u' ->
    v ⊏ v' ->
    sEq A u v ⊏ sEq A' u' v'

| inrel_Sort s :
    sSort s ⊏ sSort s

| inrel_Lambda n n' A A' B B' u u' :
    A ⊏ A' ->
    B ⊏ B' ->
    u ⊏ u' ->
    sLambda n A B u ⊏ sLambda n' A' B' u'

| inrel_App u u' n n' A A' B B' v v' :
    u ⊏ u' ->
    A ⊏ A' ->
    B ⊏ B' ->
    v ⊏ v' ->
    sApp u n A B v ⊏ sApp u' n' A' B' v'

| inrel_Refl A A' u u' :
    A ⊏ A' ->
    u ⊏ u' ->
    sRefl A u ⊏ sRefl A' u'

where " t ⊏ t' " := (inrel t t').

Lemma inrel_trel :
  forall {t t'}, t ⊏ t' -> t ∼ t'.
Proof.
  intros t t' h.
  induction h ; now constructor.
Defined.

Lemma trel_to_heq' :
  forall {Σ t1 t2},
    t1 ∼ t2 ->
    forall {Γ Γ1 Γ2 T1 T2},
      #|Γ1| = #|Γ2| ->
      Σ ;;; Γ ,,, Γ1 |-i t1 : T1 ->
      Σ ;;; Γ ,,, Γ2 |-i  t2 : T2 ->
      ∑ p,
        Σ ;;; mix Γ Γ1 Γ2 |-i p : sHeq (llift0 #|Γ1| T1)
                                      (llift0 #|Γ1| t1)
                                      (rlift0 #|Γ1| T2)
                                      (rlift0 #|Γ1| t2).
Proof.
  intros Σ t1 t2 sim.
  induction sim ; intros Γ Γ1 Γ2 U1 U2 eq h1 h2.

  (* Variable case *)
  - cbn. case_eq #|Γ1|.
    + intro e0. cbn. rewrite e0 in eq.
      destruct Γ1 ; try (now inversion e0).
      destruct Γ2 ; try (now inversion eq).
      cbn in *. rewrite !llift00, !rlift00.
      destruct (uniqueness h1 h2) as [s e].
      destruct (eq_typing e) as [hU1 hU2].
      exists (sHeqRefl U1 (sRel x)).
      eapply type_conv.
      * eapply type_HeqRefl ; eassumption.
      * apply type_Heq ; eassumption.
      * apply cong_Heq.
        all: try (apply eq_reflexivity).
        all: easy.
    + intros n eqγ. case_eq (x <=? n).
      * intro xln. exists (sProjTe (sRel x)).
        apply type_ProjTe'.
        (* generalize dependent Γ2. *)
        (* dependent induction Γ1 ; [ cbn in eqγ ; discriminate | .. ]. *)
        (* intros Γ2 eq h2. *)
        (* dependent destruction Γ2. *)
        (* eapply type_conv'. *)
        (* -- eapply type_Rel. cheat. *)
        (* -- generalize dependent Γ2. *)
        (*    dependent induction Γ1 ; [ cbn in eqγ ; discriminate | .. ]. *)
        (*    intros Γ2 eq h2. *)
        (*    dependent destruction Γ2. *)

        cheat.
      * intro nlx.
        assert (h1' : Σ ;;; mix Γ Γ1 Γ2 |-i sRel x : llift0 (S n) U1).
        { replace (sRel x) with (llift0 (S n) (sRel x))
            by (cbn ; now rewrite nlx).
          replace (S n) with #|Γ1| by (apply eqγ).
          eapply type_llift0 ; assumption.
        }
        assert (h2' : Σ ;;; mix Γ Γ1 Γ2 |-i sRel x : rlift0 (S n) U2).
        { replace (sRel x) with (rlift0 (S n) (sRel x))
            by (cbn ; now rewrite nlx).
          replace (S n) with #|Γ1| by (apply eqγ).
          eapply @type_rlift with (Δ := nil) ; assumption.
        }
        destruct (uniqueness h1' h2') as [s e].
        destruct (eq_typing e) as [hlU1 hrU2].
        exists (sHeqRefl (llift0 (S n) U1) (sRel x)).
        eapply type_conv.
        -- eapply type_HeqRefl ; eassumption.
        -- apply type_Heq ; eassumption.
        -- apply cong_Heq.
           all: try (apply eq_reflexivity).
           all: easy.

  (* Left transport *)
  - destruct (inversionTransport h1) as [s [[[[? ht1] hT1] ?] ?]].
    destruct (IHsim _ _ _ _ _ eq ht1 h2) as [q hq].
    cbn.
    exists (sHeqTrans (sHeqSym (sHeqTransport (llift0 #|Γ1| p) (llift0 #|Γ1| t1))) q).
    eapply type_HeqTrans'.
    + eapply type_HeqSym'.
      eapply type_conv.
      * eapply type_HeqTransport'.
        -- eapply type_llift0 ; eassumption.
        -- instantiate (2 := s). instantiate (1 := llift0 #|Γ1| T2).
           change (sEq (sSort s) (llift0 #|Γ1| T1) (llift0 #|Γ1| T2))
             with (llift0 #|Γ1| (sEq (sSort s) T1 T2)).
           eapply type_llift0 ; assumption.
      * instantiate (1 := succ_sort s).
        change (sSort (succ_sort s)) with (llift0 #|Γ1| (sSort (succ_sort s))).
        instantiate (1 := llift0 #|Γ1| t1).
        instantiate (1 := llift0 #|Γ1| T1).
        match goal with
        | |- ?Σ ;;; ?Γ |-i ?T : ?s =>
          change T with (llift0 #|Γ1| (sHeq T1 t1 U1 (sTransport T1 T2 p t1)))
        end.
        eapply type_llift0 ; try assumption.
        cbn. apply type_Heq ; try assumption.
        apply (eq_typing pi2_0).
      * apply cong_Heq.
        all: try (apply eq_reflexivity).
        1-3: change (sSort s) with (llift0 #|Γ1| (sSort s)).
        1,3: eapply type_llift0 ; try assumption.
        -- eapply cong_llift0 ; assumption.
        -- cbn.
           match goal with
           | |- ?Σ ;;; ?Γ |-i ?T : ?s =>
             change T with (llift0 #|Γ1| (sTransport T1 T2 p t1))
           end.
           eapply type_llift0 ; try assumption.
           eapply type_Transport ; eassumption.
    + assumption.

  (* Right transport *)
  - destruct (inversionTransport h2) as [s [[[[? ht2] hT1] ?] ?]].
    destruct (IHsim _ _ _ _ _ eq h1 ht2) as [q hq].
    cbn.
    exists (sHeqTrans q (sHeqTransport (rlift0 #|Γ1| p) (rlift0 #|Γ1| t2))).
    eapply type_HeqTrans'.
    + eassumption.
    + eapply type_conv.
      * eapply type_HeqTransport'.
        -- eapply type_rlift0 ; eassumption.
        -- instantiate (2 := s). instantiate (1 := rlift0 #|Γ1| T2).
           change (sEq (sSort s) (rlift0 #|Γ1| T1) (rlift0 #|Γ1| T2))
             with (rlift0 #|Γ1| (sEq (sSort s) T1 T2)).
           eapply type_rlift0 ; assumption.
      * instantiate (1 := succ_sort s).
        change (sSort (succ_sort s)) with (rlift0 #|Γ1| (sSort (succ_sort s))).
        match goal with
        | |- ?Σ ;;; ?Γ |-i ?T : ?s =>
          change T with (rlift0 #|Γ1| (sHeq T1 t2 U2 (sTransport T1 T2 p t2)))
        end.
        eapply type_rlift0 ; try assumption.
        cbn. apply type_Heq ; try assumption.
        apply (eq_typing pi2_0).
      * apply cong_Heq.
        all: try (apply eq_reflexivity).
        1-3: change (sSort s) with (rlift0 #|Γ1| (sSort s)).
        4: match goal with
           | |- ?Σ ;;; ?Γ |-i ?T : ?s =>
             change T with (rlift0 #|Γ1| (sTransport T1 T2 p t2))
           end.
        1,3,4: eapply type_rlift0 ; try assumption.
        -- cbn. eapply type_Transport ; eassumption.
        -- eapply cong_rlift0 ; assumption.

  (* Prod *)
  - destruct (inversionProd h1) as [s1 [z1 [[hA1 hB1] ?]]].
    destruct (inversionProd h2) as [s2 [z2 [[hA2 hB2] ?]]].
    destruct (IHsim1 _ _ _ _ _ eq hA1 hA2) as [pA hpA].
    destruct (IHsim2 _ (Γ1 ,, svass n1 A1) (Γ2 ,, svass n2 A2)
                     _ _ ltac:(cbn ; omega) hB1 hB2) as [pB hpB].
    exists (sCongProd (llift #|Γ1| 1 B1) (rlift #|Γ1| 1 B2) pA pB).
    destruct (istype_type hpA) as [? iA].
    destruct (inversionHeq iA) as [? [[[[? ?] ?] ?] ?]].
    destruct (istype_type hpB) as [? iB].
    destruct (inversionHeq iB) as [? [[[[? ?] ?] ?] ?]].
    eapply type_conv'.
    + eapply type_CongProd'.
      * eassumption.
      * rewrite llift_substProj, rlift_substProj.
        apply hpB.
      * change (sSort z1) with (llift #|Γ1| 1 (sSort z1)).
        eapply type_llift1 ; eassumption.
      * change (sSort z2) with (rlift #|Γ1| 1 (sSort z2)).
        eapply type_rlift1 ; eassumption.
    + cbn. apply cong_Heq.
      all: try (apply eq_reflexivity).
      * instantiate (1 := succ_sort (max_sort s1 z1)).
        change (sSort (max_sort s1 z1))
          with (llift0 #|Γ1| (sSort (max_sort s1 z1))).
        change (sSort (succ_sort (max_sort s1 z1)))
          with (llift0 #|Γ1| (sSort (succ_sort (max_sort s1 z1)))).
        eapply cong_llift0 ; assumption.
      * change (sSort (max_sort s2 z2))
          with (rlift0 #|Γ1| (sSort (max_sort s2 z2))).
        change (sSort (succ_sort (max_sort s1 z1)))
          with (rlift0 #|Γ1| (sSort (succ_sort (max_sort s1 z1)))).
        eapply cong_rlift0 ; try assumption.
        cbn in hpB. rewrite <- llift_substProj, <- rlift_substProj in hpB.
        assert (hB1' : Σ;;; mix Γ Γ1 Γ2,, svass n1 (llift0 #|Γ1| A1) |-i llift #|Γ1| 1 B1 : sSort z1).
        { change (sSort z1) with (llift #|Γ1| 1 (sSort z1)).
           eapply type_llift1 ; eassumption.
        }
        assert (hB2' : Σ;;; mix Γ Γ1 Γ2,, svass n2 (rlift0 #|Γ1| A2) |-i rlift #|Γ1| 1 B2 : sSort z2).
        { change (sSort z2) with (rlift #|Γ1| 1 (sSort z2)).
           eapply type_rlift1 ; eassumption.
        }
        destruct (prod_sorts hpA hpB hB1' hB2') as [ss [zz [mm [[? ?] eqm]]]].
        eapply eq_conv.
        -- eassumption.
        -- eapply strengthen_sort_eq.
           ++ eapply eq_symmetry.
              eapply cong_succ_sort.
              eassumption.
           ++ eapply typing_wf. eassumption.
      * apply type_Prod.
        -- assumption.
        -- change (sSort z1) with (llift #|Γ1| 1 (sSort z1)).
           eapply type_llift1 ; eassumption.
      * apply type_Prod.
        -- assumption.
        -- change (sSort z2) with (rlift #|Γ1| 1 (sSort z2)).
           eapply type_rlift1 ; eassumption.

  (* Eq *)
  - destruct (inversionEq h1) as [s1 [[[hA1 hu1] hv1] eqA]].
    destruct (inversionEq h2) as [s2 [[[hA2 hu2] hv2] eqB]].
    destruct (IHsim1 _ _ _ _ _ eq hA1 hA2) as [pA hpA].
    destruct (IHsim2 _ _ _ _ _ eq hu1 hu2) as [pu hpu].
    destruct (IHsim3 _ _ _ _ _ eq hv1 hv2) as [pv hpv].
    exists (sCongEq pA pu pv).
    eapply type_conv'.
    + eapply type_CongEq' ; eassumption.
    + apply cong_Heq.
      * change (sSort s1) with (llift0 #|Γ1| (sSort s1)).
        instantiate (1 := (succ_sort s1)).
        change (sSort (succ_sort s1))
          with (llift0 #|Γ1| (sSort (succ_sort s1))).
        eapply cong_llift0 ; eassumption.
      * change (sSort s2) with (rlift0 #|Γ1| (sSort s2)).
        change (sSort (succ_sort s1))
          with (rlift0 #|Γ1| (sSort (succ_sort s1))).
        eapply cong_rlift0 ; try eassumption.
        destruct (istype_type hpA) as [? iA].
        destruct (inversionHeq iA) as [? [[[[es1 es2] ?] ?] ?]].
        cbn in es1, es2.
        pose proof (sorts_in_sort es2 es1) as ess.
        eapply eq_conv.
        -- eassumption.
        -- eapply cong_succ_sort. eapply strengthen_sort_eq.
           ++ eassumption.
           ++ eapply typing_wf. eassumption.
      * apply eq_reflexivity.
        change (sSort s1) with (llift0 #|Γ1| (sSort s1)).
        eapply type_llift0.
        -- apply type_Eq ; eassumption.
        -- assumption.
      * apply eq_reflexivity.
        change (sSort s2) with (rlift0 #|Γ1| (sSort s2)).
        eapply type_rlift0.
        -- apply type_Eq ; eassumption.
        -- assumption.

  (* Sort *)
  - pose proof (inversionSort h1) as e1.
    pose proof (inversionSort h2) as e2.
    exists (sHeqRefl (sSort (succ_sort s)) (sSort s)).
    (* A wf_mix lemma would be more suitable. *)
    assert (hwf : wf Σ (mix Γ Γ1 Γ2)).
    { assert (hi : Σ;;; mix Γ Γ1 Γ2 |-i llift0 #|Γ1| (sSort s) : llift0 #|Γ1| U1).
      { eapply type_llift0 ; eassumption. }
      eapply typing_wf. eassumption.
    }
    eapply type_conv'.
    + eapply type_HeqRefl'.
      apply type_Sort. eassumption.
    + cbn. apply cong_Heq.
      * instantiate (1 := succ_sort (succ_sort s)).
        change (sSort (succ_sort s))
          with (llift0 #|Γ1| (sSort (succ_sort s))).
        change (sSort (succ_sort (succ_sort s)))
          with (llift0 #|Γ1| (sSort (succ_sort (succ_sort s)))).
        eapply cong_llift0 ; assumption.
      * change (sSort (succ_sort s))
          with (rlift0 #|Γ1| (sSort (succ_sort s))).
        change (sSort (succ_sort (succ_sort s)))
          with (rlift0 #|Γ1| (sSort (succ_sort (succ_sort s)))).
        eapply cong_rlift0 ; assumption.
      * apply eq_reflexivity. apply type_Sort. eassumption.
      * apply eq_reflexivity. apply type_Sort. eassumption.

  (* Lambda *)
  - destruct (inversionLambda h1) as [s1 [z1 [[[hA1 hB1] hu1] eq1]]].
    destruct (inversionLambda h2) as [s2 [z2 [[[hA2 hB2] hu2] eq2]]].
    destruct (IHsim1 _ _ _ _ _ eq hA1 hA2) as [pA hpA].
    destruct (IHsim2 _ (Γ1 ,, svass n1 A1) (Γ2 ,, svass n2 A2) _ _ ltac:(cbn ; omega) hB1 hB2) as [pB hpB].
    destruct (IHsim3 _ (Γ1 ,, svass n1 A1) (Γ2 ,, svass n2 A2) _ _ ltac:(cbn ; omega) hu1 hu2) as [pu hpu].
    exists (sCongLambda (llift #|Γ1| 1 B1) (rlift #|Γ1| 1 B2)
                   (llift #|Γ1| 1 u1) (rlift #|Γ1| 1 u2) pA pB pu).
    eapply type_conv'.
    + eapply type_CongLambda'.
      * eassumption.
      * rewrite llift_substProj, rlift_substProj. apply hpB.
      * rewrite !llift_substProj, !rlift_substProj. apply hpu.
      * change (sSort z1) with (llift #|Γ1| 1 (sSort z1)).
        eapply type_llift1 ; eassumption.
      * change (sSort z2) with (rlift #|Γ1| 1 (sSort z2)).
        eapply type_rlift1 ; eassumption.
      * eapply type_llift1 ; eassumption.
      * eapply type_rlift1 ; eassumption.
    + cbn. apply cong_Heq.
      all: try (apply eq_reflexivity).
      * match goal with
        | |- _ ;;; _ |-i ?T = _ : ?S =>
          change T with (llift0 #|Γ1| (sProd n1 A1 B1)) ;
          change S with (llift0 #|Γ1| S)
        end.
        eapply cong_llift0 ; eassumption.
      * match goal with
        | |- _ ;;; _ |-i ?T = _ : ?S =>
          change T with (rlift0 #|Γ1| (sProd n2 A2 B2)) ;
          change S with (rlift0 #|Γ1| S)
        end.
        eapply cong_rlift0 ; try eassumption.
        assert (hB1' : Σ;;; mix Γ Γ1 Γ2,, svass n1 (llift0 #|Γ1| A1) |-i llift #|Γ1| 1 B1 : sSort z1).
        { change (sSort z1) with (llift #|Γ1| 1 (sSort z1)).
          eapply type_llift1 ; eassumption.
        }
        assert (hB2' : Σ;;; mix Γ Γ1 Γ2,, svass n2 (rlift0 #|Γ1| A2) |-i rlift #|Γ1| 1 B2 : sSort z2).
        { change (sSort z2) with (rlift #|Γ1| 1 (sSort z2)).
          eapply type_rlift1 ; eassumption.
        }
        cbn in hpB. rewrite <- llift_substProj, <- rlift_substProj in hpB.
        destruct (prod_sorts hpA hpB hB1' hB2') as [ss [zz [mm [[? ?] eqm]]]].
        eapply eq_conv ; try eassumption.
        eapply eq_symmetry. eapply strengthen_sort_eq.
        -- eassumption.
        -- eapply typing_wf. eassumption.
      * match goal with
        | |- _ ;;; _ |-i ?t : ?T =>
          change T with (llift0 #|Γ1| (sProd n1 A1 B1)) ;
          change t with (llift0 #|Γ1| (sLambda n1 A1 B1 u1))
        end.
        apply type_llift0 ; [| assumption].
        eapply type_Lambda ; eassumption.
      * match goal with
        | |- _ ;;; _ |-i ?t : ?T =>
          change T with (rlift0 #|Γ1| (sProd n2 A2 B2)) ;
          change t with (rlift0 #|Γ1| (sLambda n2 A2 B2 u2))
        end.
        apply type_rlift0 ; [| assumption].
        eapply type_Lambda ; eassumption.

  (* App *)
  - destruct (inversionApp h1) as [s1 [z1 [[[[hA1 hB1] hu1] hv1] e1]]].
    destruct (inversionApp h2) as [s2 [z2 [[[[hA2 hB2] hu2] hv2] e2]]].
    destruct (IHsim1 _ _ _ _ _ eq hu1 hu2) as [pu hpu].
    destruct (IHsim2 _ _ _ _ _ eq hA1 hA2) as [pA hpA].
    destruct (IHsim3 _ (Γ1 ,, svass n1 A1) (Γ2 ,, svass n2 A2) _ _
                     ltac:(cbn ; omega) hB1 hB2) as [pB hpB].
    destruct (IHsim4 _ _ _ _ _ eq hv1 hv2) as [pv hpv].
    exists (sCongApp (llift #|Γ1| 1 B1) (rlift #|Γ1| 1 B2) pu pA pB pv).
    eapply type_conv'.
    + eapply type_CongApp'.
      * apply hpA.
      * rewrite llift_substProj, rlift_substProj.
        apply hpB.
      * apply hpu.
      * apply hpv.
      * change (sSort z1) with (llift #|Γ1| 1 (sSort z1)).
        eapply type_llift1 ; eassumption.
      * change (sSort z2) with (rlift #|Γ1| 1 (sSort z2)).
        eapply type_rlift1 ; eassumption.
    + cbn. apply cong_Heq.
      all: try (apply eq_reflexivity).
      * rewrite <- llift_subst. cbn.
        match goal with
        | |- _ ;;; _ |-i _ = _ : ?S =>
          change S with (llift0 #|Γ1| S)
        end.
        eapply cong_llift0 ; eassumption.
      * rewrite <- rlift_subst. cbn.
        match goal with
        | |- _ ;;; _ |-i _ = _ : ?S =>
          change S with (rlift0 #|Γ1| S)
        end.
        eapply cong_rlift0 ; try eassumption.
        cbn in hpB. rewrite <- llift_substProj, <- rlift_substProj in hpB.
        assert (hB1' : Σ;;; mix Γ Γ1 Γ2,, svass n1 (llift0 #|Γ1| A1) |-i llift #|Γ1| 1 B1 : sSort z1).
        { change (sSort z1) with (llift #|Γ1| 1 (sSort z1)).
           eapply type_llift1 ; eassumption.
        }
        assert (hB2' : Σ;;; mix Γ Γ1 Γ2,, svass n2 (rlift0 #|Γ1| A2) |-i rlift #|Γ1| 1 B2 : sSort z2).
        { change (sSort z2) with (rlift #|Γ1| 1 (sSort z2)).
           eapply type_rlift1 ; eassumption.
        }
        destruct (prod_sorts hpA hpB hB1' hB2') as [ss [zz [mm [[? ?] eqm]]]].
        eapply eq_conv.
        -- eassumption.
        -- eapply strengthen_sort_eq.
           ++ eassumption.
           ++ eapply typing_wf. eassumption.
      * rewrite <- llift_subst. cbn.
        match goal with
        | |- _ ;;; _ |-i ?t : _ =>
          change t with (llift0 #|Γ1| (sApp u1 n1 A1 B1 v1))
        end.
        eapply type_llift0 ; [| eassumption].
        eapply type_App ; eassumption.
      * rewrite <- rlift_subst. cbn.
        match goal with
        | |- _ ;;; _ |-i ?t : _ =>
          change t with (rlift0 #|Γ1| (sApp u2 n2 A2 B2 v2))
        end.
        eapply type_rlift0 ; [| eassumption].
        eapply type_App ; eassumption.

  (* Refl *)
  - destruct (inversionRefl h1) as [s1 [[hA1 hu1] e1]].
    destruct (inversionRefl h2) as [s2 [[hA2 hu2] e2]].
    destruct (IHsim1 _ _ _ _ _ eq hA1 hA2) as [pA hpA].
    destruct (IHsim2 _ _ _ _ _ eq hu1 hu2) as [pu hpu].
    exists (sCongRefl pA pu).
    eapply type_conv'.
    + eapply type_CongRefl' ; eassumption.
    + apply cong_Heq.
      all: try apply eq_reflexivity.
      * match goal with
        | |- ?Σ ;;; ?Γ |-i ?u = ?v : ?A =>
          change u with (llift0 #|Γ1| (sEq A1 u1 u1)) ;
          change A with (llift0 #|Γ1| A)
        end.
        eapply cong_llift0 ; eassumption.
      * match goal with
        | |- ?Σ ;;; ?Γ |-i ?u = ?v : ?A =>
          change u with (rlift0 #|Γ1| (sEq A2 u2 u2)) ;
          change A with (rlift0 #|Γ1| A)
        end.
        eapply cong_rlift0.
        -- destruct (istype_type hpA) as [? iA].
           destruct (inversionHeq iA) as [? [[[[es1 es2] ?] ?] ?]].
           cbn in es1, es2.
           eapply eq_conv.
           ++ eassumption.
           ++ eapply strengthen_sort_eq.
              ** eapply sorts_in_sort ; eassumption.
              ** eapply typing_wf. eassumption.
        -- assumption.
      * match goal with
        | |- ?Σ ;;; ?Γ |-i ?u : ?A =>
          change A with (llift0 #|Γ1| (sEq A1 u1 u1))
        end.
        eapply type_llift0.
        -- eapply type_Refl ; eassumption.
        -- assumption.
      * match goal with
        | |- ?Σ ;;; ?Γ |-i ?u : ?A =>
          change A with (rlift0 #|Γ1| (sEq A2 u2 u2))
        end.
        eapply type_rlift0.
        -- eapply type_Refl ; eassumption.
        -- assumption.
Defined.

Corollary trel_to_heq :
  forall {Σ Γ T1 T2} {t1 t2 : sterm},
    t1 ∼ t2 ->
    Σ ;;; Γ |-i t1 : T1 ->
    Σ ;;; Γ |-i t2 : T2 ->
    ∑ p, Σ ;;; Γ |-i p : sHeq T1 t1 T2 t2.
Proof.
  intros Σ Γ T1 T2 t1 t2 h h1 h2.
  destruct (@trel_to_heq' _ _ _ h _ nil nil _ _ eq_refl h1 h2) as [p hp].
  cbn in hp. rewrite !llift00, !rlift00 in hp.
  exists p. apply hp.
Defined.

Lemma inrel_lift :
  forall {t t'},
    t ⊏ t' ->
    forall n k, lift n k t ⊏ lift n k t'.
Proof.
  intros  t t'. induction 1 ; intros m k.
  all: try (cbn ; now constructor).
  cbn. destruct (k <=? x) ; now constructor.
Defined.

Lemma inrel_subst :
  forall {t t'},
    t ⊏ t' ->
    forall {u u'},
      u ⊏ u' ->
      forall n, t{ n := u } ⊏ t'{ n := u' }.
Proof.
  intros t t'. induction 1 ; intros v1 v2 hu m.
  all: try (cbn ; constructor ; easy).
  cbn. destruct (m ?= x).
  - now apply inrel_lift.
  - constructor.
  - constructor.
Defined.

Lemma trel_lift :
  forall {t1 t2},
    t1 ∼ t2 ->
    forall n k, lift n k t1 ∼ lift n k t2.
Proof.
  intros t1 t2. induction 1 ; intros n k.
  all: try (cbn ; now constructor).
  cbn. destruct (k <=? x) ; now constructor.
Defined.

Lemma trel_subst :
  forall {t1 t2},
    t1 ∼ t2 ->
    forall {u1 u2},
      u1 ∼ u2 ->
      forall n, t1{ n := u1 } ∼ t2{ n := u2 }.
Proof.
  intros t1 t2. induction 1 ; intros m1 m2 hu n.
  all: try (cbn ; constructor ; easy).
  unfold subst. destruct (nat_compare n x).
  - now apply trel_lift.
  - apply trel_Rel.
  - apply trel_Rel.
Defined.

(* We decided not to have it for the sake of simplicity of the relation.
   This property isn't needed in any case.
   We only require ∼ to be a PER.
 *)
(* Lemma trel_refl : forall {t}, t ∼ t. *)
(* Proof. *)
(*   induction t ; try (now constructor). *)
(*   constructor. constructor. assumption. *)
(* Defined. *)

Lemma trel_sym : forall {t1 t2}, t1 ∼ t2 -> t2 ∼ t1.
Proof.
  intros t1 t2. induction 1 ; (now constructor).
Defined.

Lemma inversion_trel_transport :
  forall {A B p t1 t2},
    sTransport A B p t1 ∼ t2 ->
    t1 ∼ t2.
Proof.
  intros A B p t1 t2 h.
  dependent induction h.
  - assumption.
  - constructor. eapply IHh.
Defined.

Lemma trel_trans :
  forall {t1 t2},
    t1 ∼ t2 ->
    forall {t3},
      t2 ∼ t3 ->
      t1 ∼ t3.
Proof.
  intros t1 t2. induction 1 ; intros t3 h.
  all: try (
    dependent induction h ; [
      constructor ; eapply IHh ; assumption
    | now constructor
    ]
  ).
  - constructor. now apply IHtrel.
  - apply IHtrel. eapply inversion_trel_transport. eassumption.
Defined.

Reserved Notation " Γ ≈ Δ " (at level 19).

Inductive crel : scontext -> scontext -> Type :=
| crel_empty : nil ≈ nil
| crel_snoc Γ Δ n t m u : Γ ≈ Δ -> t ∼ u -> (Γ ,, svass n t) ≈ (Δ ,, svass m u)

where " Γ ≈ Δ " := (crel Γ Δ).

Reserved Notation " Γ ⊂ Γ' " (at level 19).

Inductive increl : scontext -> scontext -> Type :=
| increl_empty : nil ⊂ nil
| increl_snoc Γ Γ' n n' T T' :
    Γ ⊂ Γ' -> T ⊏ T' -> (Γ ,, svass n T) ⊂ (Γ' ,, svass n' T')

where " Γ ⊂ Γ' " := (increl Γ Γ').

(*! Notion of translation *)
Definition trans Σ Γ A t Γ' A' t' :=
  Γ ⊂ Γ' *
  A ⊏ A' *
  t ⊏ t' *
  (Σ ;;; Γ' |-i t' : A').

Notation " Σ ;;;; Γ' |--- [ t' ] : A' # ⟦ Γ |--- [ t ] : A ⟧ " :=
  (trans Σ Γ A t Γ' A' t')
    (at level 7) : i_scope.

Definition ctxtrans Σ Γ Γ' :=
  Γ ⊂ Γ' * (wf Σ Γ').

Notation " Σ |--i Γ' # ⟦ Γ ⟧ " := (ctxtrans Σ Γ Γ') (at level 7) : i_scope.

(* Notion of head *)
Inductive head_kind :=
| headRel
| headSort (s : sort)
| headProd
| headLambda
| headApp
| headEq
| headRefl
| headJ
| headTransport
| headHeq
| headOther
.

Definition head (t : sterm) : head_kind :=
  match t with
  | sRel x => headRel
  | sSort s => headSort s
  | sProd n A B => headProd
  | sLambda n A B t => headLambda
  | sApp u n A B v => headApp
  | sEq A u v => headEq
  | sRefl A u => headRefl
  | sJ A u P w v p => headJ
  | sTransport A B p t => headTransport
  | sHeq A a B b => headHeq
  (* We actually only care about type heads in the source *)
  | _ => headOther
  end.

Inductive transport_data :=
| trd (T1 T2 p : sterm).

Definition transport_data_app (td : transport_data) (t : sterm) : sterm :=
  match td with
  | trd T1 T2 p => sTransport T1 T2 p t
  end.

Definition transport_seq := list transport_data.

Definition transport_seq_app (tr : transport_seq) (t : sterm) : sterm :=
  List.fold_right transport_data_app t tr.

Lemma trel_transport_seq :
  forall {A A'},
    A ⊏ A' ->
    ∑ A'' (tseq : transport_seq),
      (head A'' = head A) *
      (A' = transport_seq_app tseq A'') *
      (A ⊏ A'').
Proof.
  intros A A' h.
  induction h.
 all : try (eexists ; exists nil ; split;  [split ; [idtac | reflexivity]| idtac]; [reflexivity | now constructor ]). 

  destruct IHh as [A'' [tseq [[hh he] hsub]]].
  exists A'', (trd T1 T2 p :: tseq). split ; [split | idtac].
  assumption.
  cbn. now f_equal.
  assumption.
Defined.

(* We only need it for heads in the source *)
Inductive type_head : head_kind -> Type :=
| type_headSort s : type_head (headSort s)
| type_headProd : type_head headProd
| type_headEq : type_head headEq
.

Lemma inversion_transportType :
  forall {Σ tseq Γ' A' T},
    type_head (head A') ->
    Σ ;;; Γ' |-i transport_seq_app tseq A' : T ->
    ∑ s,
      (Σ ;;; Γ' |-i A' : sSort s) *
      (Σ ;;; Γ' |-i T : sSort (succ_sort s)).
Proof.
  intros Σ tseq. induction tseq ; intros Γ' A' T hh ht.

  - cbn in *. destruct A' ; try (now inversion hh).
    + exists (succ_sort s). repeat split.
      * apply type_Sort. apply (typing_wf ht).
      * eapply (eq_typing (inversionSort ht)). 
    + destruct (inversionProd ht) as [s1 [s2 [[? ?] ?]]].
      exists (max_sort s1 s2). repeat split.
      * now apply type_Prod.
      * eapply (eq_typing pi2_0).
    + destruct (inversionEq ht) as [s [[[? ?] ?] ?]].
      exists s. repeat split.
      * now apply type_Eq.
      * eapply (eq_typing pi2_1).

  - destruct a. cbn in ht.
    change (fold_right transport_data_app A' tseq)
      with (transport_seq_app tseq A') in ht.
    destruct (inversionTransport ht) as [s [[[[? hA'] hT1] ?] ?]].
    destruct (IHtseq Γ' A' T1 hh hA') as [s' [hAs hT1s]].
    exists s'. repeat split.
    + assumption.
    + destruct (eq_typing pi2_0) as [_ hT].
      destruct (uniqueness hT1 hT1s) as [s3 hs3].
      eapply type_conv.
      * eassumption.
      * apply (eq_typing hs3).
      * assumption.
Defined.

Lemma choose_type' :
  forall {Σ A A'},
    type_head (head A) ->
    A ⊏ A' ->
    forall {Γ Γ' t t'},
      Γ ⊂ Γ' ->
      t ⊏ t' ->
      (Σ ;;; Γ' |-i t' : A') ->
      ∑ A'',
        (∑ t'', Σ ;;;; Γ' |--- [ t'' ] : A'' # ⟦ Γ |--- [t] : A ⟧) *
        (head A'' = head A).
Proof.
  intros Σ A A' hth hA Γ Γ' t t' hΓ ht h.
  destruct (trel_transport_seq hA) as [A'' [tseq [[hh heq] hrel]]].
  rewrite heq in h.
  destruct (istype_type h) as [s hs].
  assert (hth' : type_head (head A'')) by (now rewrite hh).
  destruct (inversion_transportType hth' hs) as [s' [h' hss']].
  exists A''. split.
  - assert (simA : A' ∼ A'').
    { apply trel_sym.
      eapply trel_trans.
      - apply trel_sym. apply inrel_trel. eassumption.
      - apply inrel_trel. assumption.
    }
    pose (thm := @trel_to_heq Σ Γ' (sSort s) (sSort s) A' A'' simA).
    rewrite <- heq in hs.
    destruct thm as [p hp].
    + assumption.
    + eapply type_conv.
      * eassumption.
      * eassumption.
      * eapply sorts_in_sort.
        -- apply type_Sort. apply (typing_wf h').
        -- assumption.
    + destruct (sort_heq_ex hp) as [q hq].
      exists (sTransport A' A'' q t').
      repeat split.
      * assumption.
      * assumption.
      * constructor. assumption.
      * destruct (istype_type hq) as [? hEq].
        destruct (inversionEq hEq) as [? [[[? ?] ?] ?]].
        eapply type_Transport.
        -- eassumption.
        -- eassumption.
        -- assumption.
        -- subst. assumption.
  - assumption.
Defined.

Lemma choose_type :
  forall {Σ Γ A t Γ' A' t'},
    type_head (head A) ->
    Σ ;;;; Γ' |--- [ t' ] : A' # ⟦ Γ |--- [t] : A ⟧ ->
    ∑ A'',
      (∑ t'', Σ ;;;; Γ' |--- [ t'' ] : A'' # ⟦ Γ |--- [t] : A ⟧) *
      (head A'' = head A).
Proof.
  intros Σ Γ A t Γ' A' t' htt [[[hΓ hA] ht] h].
  now eapply choose_type'.
Defined.

Lemma change_type :
  forall {Σ Γ A t Γ' A' t' s A''},
    Σ ;;;; Γ' |--- [ t' ] : A' # ⟦ Γ |--- [t] : A ⟧ ->
    Σ ;;;; Γ' |--- [ A'' ] : sSort s # ⟦ Γ |--- [A] : sSort s ⟧ ->
    ∑ t'', Σ ;;;; Γ' |--- [ t'' ] : A'' # ⟦ Γ |--- [t] : A ⟧.
Proof.
  intros Σ Γ A t Γ' A' t' s A'' [[[rΓ' rA'] rt'] ht'] [[[rΓ'' _] rA''] hA''].
  assert (simA : A' ∼ A'').
  { eapply trel_trans.
    - eapply trel_sym. eapply inrel_trel. eassumption.
    - eapply inrel_trel. eassumption.
  }
  destruct (istype_type ht') as [s2 hA'].
  destruct (@trel_to_heq Σ Γ' (sSort s2) (sSort s) A' A'' simA) as [p hp].
  - assumption.
  - assumption.
  - destruct (istype_type hp) as [s1 hheq].
    assert (Σ ;;; Γ' |-i sSort s : sSort (succ_sort s)).
    { apply type_Sort. apply (typing_wf hp). }
    destruct (inversionHeq hheq) as [? [[[[? hs] ?] ?] ?]].
    assert (hp' : Σ ;;; Γ' |-i p : sHeq (sSort s) A' (sSort s) A'').
    { eapply type_conv.
      - eassumption.
      - apply type_Heq ; try eassumption.
        eapply type_conv.
        + eassumption.
        + apply type_Sort. apply (typing_wf hA').
        + apply sorts_in_sort.
          * eapply type_conv.
            -- eassumption.
            -- apply type_Sort. apply (typing_wf hA').
            -- apply eq_symmetry. apply (inversionSort hs).
          * assumption.
      - apply cong_Heq ; try (apply eq_reflexivity) ; try assumption.
        apply sorts_in_sort ; assumption.
    }
    destruct (sort_heq_ex hp') as [q hq].
    exists (sTransport A' A'' q t').
    repeat split.
    + assumption.
    + assumption.
    + constructor. assumption.
    + apply type_Transport with (s := s) ; try assumption.
      eapply type_conv.
      * eassumption.
      * apply type_Sort. apply (typing_wf hs).
      * apply sorts_in_sort.
        -- eapply type_conv.
           ++ eassumption.
           ++ apply type_Sort. apply (typing_wf hs).
           ++ apply eq_symmetry. apply (inversionSort hs).
        -- apply type_Sort. apply (typing_wf hs).
Defined.


(*! Translation *)

Fact length_increl : forall {Γ Γ'}, Γ ⊂ Γ' -> #|Γ| = #|Γ'|.
Proof.
  intros Γ Γ' h.
  dependent induction h.
  - reflexivity.
  - cbn. now f_equal.
Defined.

Fact nth_increl :
  forall {Γ Γ'},
    Γ ⊂ Γ' ->
    forall {n} { isdecl : n < #|Γ| } { isdecl' : n < #|Γ'| },
      sdecl_type (safe_nth Γ (exist (fun n0 : nat => n0 < #|Γ|) n isdecl))
    ⊏ sdecl_type (safe_nth Γ' (exist (fun n0 : nat => n0 < #|Γ'|) n isdecl')).
Proof.
  intros Γ Γ' e. induction e ; intros m isdecl isdecl'.
  - exfalso. easy.
  - destruct m.
    + cbn. assumption.
    + cbn. apply IHe.
Defined.

Definition trans_snoc {Σ Γ x A s Γ' A' s'} :
  Σ |--i Γ' # ⟦ Γ ⟧ ->
  Σ ;;;; Γ' |--- [A'] : sSort s' # ⟦ Γ |--- [A] : sSort s ⟧ ->
  Σ |--i Γ' ,, svass x A' # ⟦ Γ ,, svass x A ⟧.
Proof.
  intros hΓ hA.
  split.
  - constructor ; now destruct hA as [[[? ?] ?] ?].
  - econstructor.
    + now destruct hΓ.
    + now destruct hA as [[[? ?] ?] ?].
Defined.

Definition trans_Prod {Σ Γ n A B s1 s2 Γ' A' B'} :
  Σ |--i Γ' # ⟦ Γ ⟧ ->
  Σ ;;;; Γ' |--- [A'] : sSort s1 # ⟦ Γ |--- [A] : sSort s1 ⟧ ->
  Σ ;;;; Γ' ,, svass n A' |--- [B'] : sSort s2
  # ⟦ Γ ,, svass n A |--- [B]: sSort s2 ⟧ ->
  Σ ;;;; Γ' |--- [sProd n A' B']: sSort (max_sort s1 s2)
  # ⟦ Γ |--- [ sProd n A B]: sSort (max_sort s1 s2) ⟧.
Proof.
  intros hΓ hA hB.
  destruct hΓ. destruct hA as [[? ?] ?]. destruct hB as [[? ?] ?].
  repeat split.
  - assumption.
  - constructor.
  - now constructor.
  - now eapply type_Prod.
Defined.

Definition trans_Eq {Σ Γ A u v s Γ' A' u' v'} :
  Σ |--i Γ' # ⟦ Γ ⟧ ->
  Σ ;;;; Γ' |--- [A'] : sSort s # ⟦ Γ |--- [A] : sSort s ⟧ ->
  Σ ;;;; Γ' |--- [u'] : A' # ⟦ Γ |--- [u] : A ⟧ ->
  Σ ;;;; Γ' |--- [v'] : A' # ⟦ Γ |--- [v] : A ⟧ ->
  Σ ;;;; Γ' |--- [sEq A' u' v'] : sSort s # ⟦ Γ |--- [sEq A u v] : sSort s ⟧.
Proof.
  intros hΓ hA hu hv.
  destruct hA as [[[? ?] ?] ?].
  destruct hu as [[[? ?] ?] ?].
  destruct hv as [[[? ?] ?] ?].
  repeat split.
  - assumption.
  - constructor.
  - constructor ; assumption.
  - apply type_Eq ; assumption.
Defined.

(* Maybe put this together with the other translation definitions *)
Definition eqtrans Σ Γ A u v Γ' A' A'' u' v' p' :=
  Γ ⊂ Γ' *
  A ⊏ A' *
  A ⊏ A'' *
  u ⊏ u' *
  v ⊏ v' *
  (Σ ;;; Γ' |-i p' : sHeq A' u' A'' v').

Lemma eqtrans_trans :
  forall {Σ Γ A u v Γ' A' A'' u' v' p'},
    eqtrans Σ Γ A u v Γ' A' A'' u' v' p' ->
    (Σ ;;;; Γ' |--- [u'] : A' # ⟦ Γ |--- [u] : A ⟧) *
    (Σ ;;;; Γ' |--- [v'] : A'' # ⟦ Γ |--- [v] : A ⟧).
Proof.
  intros Σ Γ A u v Γ' A' A'' u' v' p' h.
  destruct h as [[[[[eΓ eS'] eS''] eA] eB] hp'].
  destruct (istype_type hp') as [? hheq].
  destruct (inversionHeq hheq) as [? [[[[? ?] ?] ?] ?]].
  repeat split ; assumption.
Defined.

Scheme typing_ind := Induction for XTyping.typing Sort Type
  with wf_ind := Induction for XTyping.wf Sort Type
  with eq_term_ind := Induction for XTyping.eq_term Sort Type.

(* Combined Scheme typing_all from typing_ind , wf_ind , eq_term_ind. *)

Definition typing_all : forall (Σ : global_context)
         (P0 : forall s : scontext, XTyping.wf Σ s -> Type)
         (P : forall (s : scontext) (s0 s1 : sterm),
              Σ;;; s |-x s0 : s1 -> Type)
         (P1 : forall (s : scontext) (s0 s1 s2 : sterm),
               Σ;;; s |-x s0 = s1 : s2 -> Type),
       P0 [] (XTyping.wf_nil Σ) ->
       (forall (Γ : scontext) (x : name) (A : sterm) 
          (s : sort) (w : XTyping.wf Σ Γ),
        P0 Γ w ->
        forall t : Σ;;; Γ |-x A : sSort s,
        P Γ A (sSort s) t ->
        P0 (Γ,, svass x A) (XTyping.wf_snoc Σ Γ x A s w t))->
       (forall (Γ : scontext) (n : nat) (w : XTyping.wf Σ Γ),
        P0 Γ w ->
        forall isdecl : n < #|Γ|,
        P Γ (sRel n)
          (lift0 (S n)
             (sdecl_type
                (safe_nth Γ (exist (fun n0 : nat => n0 < #|Γ|) n isdecl))))
          (XTyping.type_Rel Σ Γ n w isdecl)) ->
       (forall (Γ : scontext) (s : sort) (w : XTyping.wf Σ Γ),
        P0 Γ w ->
        P Γ (sSort s) (sSort (succ_sort s)) (XTyping.type_Sort Σ Γ s w)) ->
       (forall (Γ : scontext) (n : name) (t b : sterm) 
          (s1 s2 : sort) (t0 : Σ;;; Γ |-x t : sSort s1),
        P Γ t (sSort s1) t0 ->
        forall t1 : Σ;;; Γ,, svass n t |-x b : sSort s2,
        P (Γ,, svass n t) b (sSort s2) t1 ->
        P Γ (sProd n t b) (sSort (max_sort s1 s2))
          (XTyping.type_Prod Σ Γ n t b s1 s2 t0 t1)) ->
       (forall (Γ : scontext) (n n' : name) (t b : sterm) 
          (s1 s2 : sort) (bty : sterm) (t0 : Σ;;; Γ |-x t : sSort s1),
        P Γ t (sSort s1) t0 ->
        forall t1 : Σ;;; Γ,, svass n t |-x bty : sSort s2,
        P (Γ,, svass n t) bty (sSort s2) t1 ->
        forall t2 : Σ;;; Γ,, svass n t |-x b : bty,
        P (Γ,, svass n t) b bty t2 ->
        P Γ (sLambda n t bty b) (sProd n' t bty)
          (XTyping.type_Lambda Σ Γ n n' t b s1 s2 bty t0 t1 t2)) ->
       (forall (Γ : scontext) (n : name) (s1 s2 : sort) 
          (t A B u : sterm) (t0 : Σ;;; Γ |-x A : sSort s1),
        P Γ A (sSort s1) t0 ->
        forall t1 : Σ;;; Γ,, svass n A |-x B : sSort s2,
        P (Γ,, svass n A) B (sSort s2) t1 ->
        forall t2 : Σ;;; Γ |-x t : sProd n A B,
        P Γ t (sProd n A B) t2 ->
        forall t3 : Σ;;; Γ |-x u : A,
        P Γ u A t3 ->
        P Γ (sApp t n A B u) (B {0 := u})
          (XTyping.type_App Σ Γ n s1 s2 t A B u t0 t1 t2 t3)) ->
       (forall (Γ : scontext) (s : sort) (A u v : sterm)
          (t : Σ;;; Γ |-x A : sSort s),
        P Γ A (sSort s) t ->
        forall t0 : Σ;;; Γ |-x u : A,
        P Γ u A t0 ->
        forall t1 : Σ;;; Γ |-x v : A,
        P Γ v A t1 ->
        P Γ (sEq A u v) (sSort s) (XTyping.type_Eq Σ Γ s A u v t t0 t1)) ->
       (forall (Γ : scontext) (s : sort) (A u : sterm)
          (t : Σ;;; Γ |-x A : sSort s),
        P Γ A (sSort s) t ->
        forall t0 : Σ;;; Γ |-x u : A,
        P Γ u A t0 ->
        P Γ (sRefl A u) (sEq A u u) (XTyping.type_Refl Σ Γ s A u t t0)) ->
       (forall (Γ : scontext) (t A B : sterm) (s : sort)
          (t0 : Σ;;; Γ |-x t : A),
        P Γ t A t0 ->
        forall t1 : Σ;;; Γ |-x B : sSort s,
        P Γ B (sSort s) t1 ->
        forall e : Σ;;; Γ |-x A = B : sSort s,
        P1 Γ A B (sSort s) e ->
        P Γ t B (XTyping.type_conv Σ Γ t A B s t0 t1 e)) ->
       (forall (Γ : scontext) (u A : sterm) (t : Σ;;; Γ |-x u : A),
        P Γ u A t -> P1 Γ u u A (XTyping.eq_reflexivity Σ Γ u A t)) ->
       (forall (Γ : scontext) (u v A : sterm) (e : Σ;;; Γ |-x u = v : A),
        P1 Γ u v A e -> P1 Γ v u A (XTyping.eq_symmetry Σ Γ u v A e)) ->
       (forall (Γ : scontext) (u v w A : sterm) (e : Σ;;; Γ |-x u = v : A),
        P1 Γ u v A e ->
        forall e0 : Σ;;; Γ |-x v = w : A,
        P1 Γ v w A e0 -> P1 Γ u w A (XTyping.eq_transitivity Σ Γ u v w A e e0)) ->
       (forall (Γ : scontext) (s1 s2 : sort) (n : name) 
          (A B t u : sterm) (t0 : Σ;;; Γ |-x A : sSort s1),
        P Γ A (sSort s1) t0 ->
        forall t1 : Σ;;; Γ,, svass n A |-x B : sSort s2,
        P (Γ,, svass n A) B (sSort s2) t1 ->
        forall t2 : Σ;;; Γ,, svass n A |-x t : B,
        P (Γ,, svass n A) t B t2 ->
        forall t3 : Σ;;; Γ |-x u : A,
        P Γ u A t3 ->
        P1 Γ (sApp (sLambda n A B t) n A B u) (t {0 := u}) 
          (B {0 := u}) (XTyping.eq_beta Σ Γ s1 s2 n A B t u t0 t1 t2 t3)) ->
       (forall (Γ : scontext) (s : sort) (T1 T2 t1 t2 : sterm)
          (e : Σ;;; Γ |-x t1 = t2 : T1),
        P1 Γ t1 t2 T1 e ->
        forall e0 : Σ;;; Γ |-x T1 = T2 : sSort s,
        P1 Γ T1 T2 (sSort s) e0 ->
        P1 Γ t1 t2 T2 (XTyping.eq_conv Σ Γ s T1 T2 t1 t2 e e0)) ->
       (forall (Γ : scontext) (n1 n2 : name) (A1 A2 B1 B2 : sterm)
          (s1 s2 : sort) (e : Σ;;; Γ |-x A1 = A2 : sSort s1),
        P1 Γ A1 A2 (sSort s1) e ->
        forall e0 : Σ;;; Γ,, svass n1 A1 |-x B1 = B2 : sSort s2,
        P1 (Γ,, svass n1 A1) B1 B2 (sSort s2) e0 ->
        forall t : Σ;;; Γ,, svass n1 A1 |-x B1 : sSort s2,
        P (Γ,, svass n1 A1) B1 (sSort s2) t ->
        forall t0 : Σ;;; Γ,, svass n2 A2 |-x B2 : sSort s2,
        P (Γ,, svass n2 A2) B2 (sSort s2) t0 ->
        P1 Γ (sProd n1 A1 B1) (sProd n2 A2 B2) (sSort (max_sort s1 s2))
          (XTyping.cong_Prod Σ Γ n1 n2 A1 A2 B1 B2 s1 s2 e e0 t t0)) ->
       (forall (Γ : scontext) (n1 n2 n' : name) (A1 A2 B1 B2 t1 t2 : sterm)
          (s1 s2 : sort) (e : Σ;;; Γ |-x A1 = A2 : sSort s1),
        P1 Γ A1 A2 (sSort s1) e ->
        forall e0 : Σ;;; Γ,, svass n1 A1 |-x B1 = B2 : sSort s2,
        P1 (Γ,, svass n1 A1) B1 B2 (sSort s2) e0 ->
        forall e1 : Σ;;; Γ,, svass n1 A1 |-x t1 = t2 : B1,
        P1 (Γ,, svass n1 A1) t1 t2 B1 e1 ->
        forall t : Σ;;; Γ,, svass n1 A1 |-x B1 : sSort s2,
        P (Γ,, svass n1 A1) B1 (sSort s2) t ->
        forall t0 : Σ;;; Γ,, svass n2 A2 |-x B2 : sSort s2,
        P (Γ,, svass n2 A2) B2 (sSort s2) t0 ->
        forall t3 : Σ;;; Γ,, svass n1 A1 |-x t1 : B1,
        P (Γ,, svass n1 A1) t1 B1 t3 ->
        forall t4 : Σ;;; Γ,, svass n2 A2 |-x t2 : B2,
        P (Γ,, svass n2 A2) t2 B2 t4 ->
        P1 Γ (sLambda n1 A1 B1 t1) (sLambda n2 A2 B2 t2) 
          (sProd n' A1 B1)
          (XTyping.cong_Lambda Σ Γ n1 n2 n' A1 A2 B1 B2 t1 t2 s1 s2 e e0 e1 t
             t0 t3 t4)) ->
       (forall (Γ : scontext) (n1 n2 : name) (s1 s2 : sort)
          (t1 t2 A1 A2 B1 B2 u1 u2 : sterm)
          (e : Σ;;; Γ |-x A1 = A2 : sSort s1),
        P1 Γ A1 A2 (sSort s1) e ->
        forall e0 : Σ;;; Γ,, svass n1 A1 |-x B1 = B2 : sSort s2,
        P1 (Γ,, svass n1 A1) B1 B2 (sSort s2) e0 ->
        forall e1 : Σ;;; Γ |-x t1 = t2 : sProd n1 A1 B1,
        P1 Γ t1 t2 (sProd n1 A1 B1) e1 ->
        forall e2 : Σ;;; Γ |-x u1 = u2 : A1,
        P1 Γ u1 u2 A1 e2 ->
        forall t : Σ;;; Γ,, svass n1 A1 |-x B1 : sSort s2,
        P (Γ,, svass n1 A1) B1 (sSort s2) t ->
        forall t0 : Σ;;; Γ,, svass n2 A2 |-x B2 : sSort s2,
        P (Γ,, svass n2 A2) B2 (sSort s2) t0 ->
        forall t3 : Σ;;; Γ |-x t1 : sProd n1 A1 B1,
        P Γ t1 (sProd n1 A1 B1) t3 ->
        forall t4 : Σ;;; Γ |-x t2 : sProd n2 A2 B2,
        P Γ t2 (sProd n2 A2 B2) t4 ->
        forall t5 : Σ;;; Γ |-x u1 : A1,
        P Γ u1 A1 t5 ->
        forall t6 : Σ;;; Γ |-x u2 : A2,
        P Γ u2 A2 t6 ->
        P1 Γ (sApp t1 n1 A1 B1 u1) (sApp t2 n2 A2 B2 u2) 
          (B1 {0 := u1})
          (XTyping.cong_App Σ Γ n1 n2 s1 s2 t1 t2 A1 A2 B1 B2 u1 u2 e e0 e1 e2
             t t0 t3 t4 t5 t6)) ->
       (forall (Γ : scontext) (s : sort) (A1 A2 u1 u2 v1 v2 : sterm)
          (e : Σ;;; Γ |-x A1 = A2 : sSort s),
        P1 Γ A1 A2 (sSort s) e ->
        forall e0 : Σ;;; Γ |-x u1 = u2 : A1,
        P1 Γ u1 u2 A1 e0 ->
        forall e1 : Σ;;; Γ |-x v1 = v2 : A1,
        P1 Γ v1 v2 A1 e1 ->
        P1 Γ (sEq A1 u1 v1) (sEq A2 u2 v2) (sSort s)
          (XTyping.cong_Eq Σ Γ s A1 A2 u1 u2 v1 v2 e e0 e1)) ->
       (forall (Γ : scontext) (s : sort) (A1 A2 u1 u2 : sterm)
          (e : Σ;;; Γ |-x A1 = A2 : sSort s),
        P1 Γ A1 A2 (sSort s) e ->
        forall e0 : Σ;;; Γ |-x u1 = u2 : A1,
        P1 Γ u1 u2 A1 e0 ->
        P1 Γ (sRefl A1 u1) (sRefl A2 u2) (sEq A1 u1 u1)
          (XTyping.cong_Refl Σ Γ s A1 A2 u1 u2 e e0)) ->
       (forall (Γ : scontext) (A u v e : sterm) (t : Σ;;; Γ |-x e : sEq A u v),
        P Γ e (sEq A u v) t -> P1 Γ u v A (reflection Σ Γ A u v e t)) ->
       (forall (s : scontext) (w : XTyping.wf Σ s), P0 s w) *
       (forall (s : scontext) (s0 s1 : sterm) (t : Σ;;; s |-x s0 : s1),
           P s s0 s1 t) *
       (forall (s : scontext) (s0 s1 s2 : sterm) (e : Σ;;; s |-x s0 = s1 : s2),
           P1 s s0 s1 s2 e).
Proof. 
  intros; repeat split ; [
  eapply wf_ind | eapply typing_ind | eapply eq_term_ind]; eauto.
Defined. 

Definition complete_translation {Σ} :
           (forall Γ (h : XTyping.wf Σ Γ),
               ∑ Γ', Σ |--i Γ' # ⟦ Γ ⟧ )
           * (forall { Γ t A} (h : Σ ;;; Γ |-x t : A)
     {Γ'} (hΓ : Σ |--i Γ' # ⟦ Γ ⟧),                        
       ∑ A' t', Σ ;;;; Γ' |--- [t'] : A' # ⟦ Γ |--- [t] : A ⟧)
 * (forall { Γ u v A} (h : Σ ;;; Γ |-x u = v : A)
                    {Γ'} (hΓ : Σ |--i Γ' # ⟦ Γ ⟧),
  ∑ A' A'' u' v' p',
    eqtrans Σ Γ A u v Γ' A' A'' u' v' p').
Proof.
  unshelve refine (typing_all Σ
                     (fun Γ (h : XTyping.wf Σ Γ) =>
                        ∑ Γ', Σ |--i Γ' # ⟦ Γ ⟧ )
                     (fun { Γ t A} (h : Σ ;;; Γ |-x t : A) => forall
                          {Γ'} (hΓ : Σ |--i Γ' # ⟦ Γ ⟧),                        
                          ∑ A' t', Σ ;;;; Γ' |--- [t'] : A' # ⟦ Γ |--- [t] : A ⟧)
                     (fun { Γ u v A} (h : Σ ;;; Γ |-x u = v : A) => forall
                    {Γ'} (hΓ : Σ |--i Γ' # ⟦ Γ ⟧),
  ∑ A' A'' u' v' p',
    eqtrans Σ Γ A u v Γ' A' A'' u' v' p')
                     _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); intros.
  (** context_translation **)
  
    (* wf_nil *)
    + exists nil. split ; constructor.

    (* wf_snoc *)
    + destruct H as [Γ' hΓ'].
      rename t into hA.
      destruct (H0 _ hΓ') as [T [A' hA']].
      assert (th : type_head (head (sSort s))) by constructor.
      destruct (choose_type th hA') as [T' [[A'' hA''] hh]].
      destruct T' ; try (now inversion hh).
      exists (Γ' ,, svass x A''). now eapply trans_snoc.

  (** type_translation **)
  
    (* type_Rel *)
    + assert (isdecl' : n < #|Γ'|).
      { destruct hΓ as [iΓ _]. now rewrite <- (length_increl iΓ). }
      exists (lift0 (S n) (sdecl_type (safe_nth Γ' (exist _ n isdecl')))), (sRel n).
      repeat split.
      * now destruct hΓ.
      * apply inrel_lift. apply nth_increl. now destruct hΓ.
      * constructor.
      * apply type_Rel. now destruct hΓ.

    (* type_Sort *)
    + exists (sSort (succ_sort s)), (sSort s).
      repeat split.
      * now destruct hΓ.
      * constructor.
      * constructor.
      * apply type_Sort. now destruct hΓ.

    (* type_Prod *)
    + (* Translation of the domain *)
      destruct (H _ hΓ) as [S' [t' ht']].
      assert (th : type_head (head (sSort s1))) by constructor.
      destruct (choose_type th ht') as [T' [[t'' ht''] hh]].
      clear ht' t' S'.
      destruct T' ; inversion hh.
      subst. clear hh th.
      (* Translation of the codomain *)
      destruct (H0 _ (trans_snoc hΓ ht''))
        as [S' [b' hb']].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type th hb') as [T' [[b'' hb''] hh]].
      clear hb' b' S'.
      destruct T' ; inversion hh. subst. clear hh th.
      (* Now we conclude *)
      exists (sSort (max_sort s1 s2)), (sProd n t'' b'').
      now apply trans_Prod.

    (* type_Lambda *)
    + (* Translation of the domain *)
      destruct (H _ hΓ) as [S' [t' ht']].
      assert (th : type_head (head (sSort s1))) by constructor.
      destruct (choose_type th ht') as [T' [[t'' ht''] hh]].
      clear ht' t' S'.
      destruct T' ; inversion hh.
      subst. clear hh th.
      (* Translation of the codomain *)
      destruct (H0 _ (trans_snoc hΓ ht''))
        as [S' [bty' hbty']].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type th hbty') as [T' [[bty'' hbty''] hh]].
      clear hbty' bty' S'.
      destruct T' ; inversion hh. subst. clear hh th.
      (* Translation of the term *)
      destruct (H1 _ (trans_snoc hΓ ht''))
        as [S' [b' hb']].
      destruct (change_type hb' hbty'') as [b'' hb''].
      clear hb' S' b'.
      exists (sProd n' t'' bty''), (sLambda n t'' bty'' b'').
      repeat split.
      * now destruct hΓ.
      * constructor.
        -- now destruct ht'' as [[[? ?] ?] ?].
        -- now destruct hbty'' as [[[? ?] ?] ?].
      * constructor.
        -- now destruct ht'' as [[[? ?] ?] ?].
        -- now destruct hbty'' as [[[? ?] ?] ?].
        -- now destruct hb'' as [[[? ?] ?] ?].
      * eapply type_Lambda.
        -- now destruct ht'' as [[[? ?] ?] ?].
        -- now destruct hbty'' as [[[? ?] ?] ?].
        -- now destruct hb'' as [[[? ?] ?] ?].
    (* type_App *)
    + (* Translation of the domain *)
      destruct (H _ hΓ) as [S' [A'' hA'']].
      assert (th : type_head (head (sSort s1))) by constructor.
      destruct (choose_type th hA'') as [T' [[A' hA'] hh]].
      clear hA'' A'' S'.
      destruct T' ; inversion hh.
      subst. clear hh th.
      (* Translation of the codomain *)
      destruct (H0 _ (trans_snoc hΓ hA'))
        as [S' [B'' hB'']].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type th hB'') as [T' [[B' hB'] hh]].
      clear hB'' B'' S'.
      destruct T' ; inversion hh. subst. clear hh th.
      (* Translation of the function *)
      destruct (H1 _ hΓ) as [T'' [t'' ht'']].
      assert (th : type_head (head (sProd n A B))) by constructor.
      destruct (choose_type th ht'') as [T' [[t' ht'] hh]].
      clear ht'' t'' T''.
      destruct T' ; inversion hh. subst. clear hh th.
      rename T'1 into A'', T'2 into B''.
      destruct (change_type ht' (trans_Prod hΓ hA' hB')) as [t'' ht''].
      clear ht' A'' B'' t'.
      (* Translation of the argument *)
      destruct (H2 _ hΓ) as [A'' [u'' hu'']].
      destruct (change_type hu'' hA') as [u' hu'].
      clear hu'' A'' u''.
      (* We now conclude *)
      exists (B'{ 0 := u' }), (sApp t'' n A' B' u').
      destruct hΓ.
      destruct hA' as [[[? ?] ?] ?].
      destruct hB' as [[[? ?] ?] ?].
      destruct ht'' as [[[? ?] ?] ?].
      destruct hu' as [[[? ?] ?] ?].
      repeat split.
      * assumption.
      * now apply inrel_subst.
      * now constructor.
      * eapply type_App ; eassumption.

    (* type_Eq *)
    + (* The type *)
      destruct (H _ hΓ) as [S [A'' hA'']].
      assert (th : type_head (head (sSort s))) by constructor.
      destruct (choose_type th hA'') as [T [[A' hA'] hh]].
      clear hA'' A'' S.
      destruct T ; inversion hh. subst. clear hh th.
      (* The first term *)
      destruct (H0 _ hΓ) as [A'' [u'' hu'']].
      destruct (change_type hu'' hA') as [u' hu'].
      clear hu'' u'' A''.
      (* The other term *)
      destruct (H1 _ hΓ) as [A'' [v'' hv'']].
      destruct (change_type hv'' hA') as [v' hv'].
      (* Now we conclude *)
      exists (sSort s), (sEq A' u' v').
      apply trans_Eq ; assumption.

    (* type_Refl *)
    + destruct (H0 _ hΓ) as [A' [u' hu']].
      exists (sEq A' u' u'), (sRefl A' u').
      destruct hu' as [[[? ?] ?] hu'].
      destruct hΓ.
      destruct (istype_type hu').
      repeat split.
      * assumption.
      * constructor ; assumption.
      * constructor ; assumption.
      * eapply type_Refl ; eassumption.

    (* type_conv *)
    + (* Translating the conversion *)
      destruct (H1 _ hΓ)
        as [S' [S'' [A'' [B'' [p' h']]]]].
      destruct (eqtrans_trans h') as [hA'' hB''].
      destruct h' as [[[[[eΓ eS'] eS''] eA] eB] hp'].
      assert (th : type_head (head (sSort s))) by constructor.
      destruct (choose_type th hA'') as [T [[A' hA'] hh]].
      (* clear hA'' eS' eA A'' S'. *)
      destruct T ; inversion hh. subst. clear hh.
      destruct (choose_type th hB'') as [T [[B' hB'] hh]].
      (* clear hB'' eS'' eB B'' S''. *)
      destruct T ; inversion hh. subst. clear hh th.
      (* Translating the term *)
      destruct (H _ hΓ) as [A''' [t'' ht'']].
      destruct (change_type ht'' hA') as [t' ht'].
      assert (hpA : ∑ pA, Σ ;;; Γ' |-i pA : sHeq (sSort s) A' S' A'').
      { destruct hA' as [[_ eA'] hA'].
        destruct hA'' as [_ hA''].
        assert (hr : A' ∼ A'').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        apply (trel_to_heq hr) ; assumption.
      }
      destruct hpA as [pA hpA].
      assert (hpB : ∑ pB, Σ ;;; Γ' |-i pB : sHeq S'' B'' (sSort s) B').
      { destruct hB' as [[_ eB'] hB'].
        destruct hB'' as [_ hB''].
        assert (hr : B'' ∼ B').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        apply (trel_to_heq hr) ; assumption.
      }
      destruct hpB as [pB hpB].
      assert (hq : ∑ q, Σ ;;; Γ' |-i q : sHeq (sSort s) A' (sSort s) B').
      { exists (sHeqTrans pA (sHeqTrans p' pB)).
        eapply type_HeqTrans'.
        - eassumption.
        - eapply type_HeqTrans'.
          + eassumption.
          + assumption.
      }
      destruct hq as [q hq].
      destruct (sort_heq_ex hq) as [e' he'].
      (* Now we conclude *)
      exists B', (sTransport A' B' e' t').
      destruct hA' as [[[? ?] ?] ?].
      destruct hB' as [[[? ?] ?] ?].
      destruct ht' as [[[? ?] ?] ?].
      repeat split ; try assumption.
      * constructor. assumption.
      * eapply type_Transport ; eassumption.

  (** eq_translation **)
  
    (* eq_reflexivity *)
    + destruct (H _ hΓ) as [A' [u' hu']].
      destruct hu' as [[[? ?] ?] hu'].
      destruct (istype_type hu') as [s' hA'].
      exists A', A', u', u', (sHeqRefl A' u').
      repeat split ; try assumption.
      eapply type_HeqRefl ; eassumption.

    (* eq_symmetry *)
    + destruct (H _ hΓ)
        as [A' [A'' [u' [v' [p' h']]]]].
      destruct h' as [[[[[? ?] ?] ?] ?] hp'].
      exists A'', A', v', u', (sHeqSym p').
      repeat split ; try assumption.
      eapply type_HeqSym'. eassumption.
      
    (* eq_transitivity *)
    + destruct (H _ hΓ)
        as [A1 [A2 [u1 [v1 [p1 h1']]]]].
      destruct (H0 _ hΓ)
        as [A3 [A4 [v2 [w1 [p2 h2']]]]].
      destruct (eqtrans_trans h1') as [hu1 hv1].
      destruct (eqtrans_trans h2') as [hv2 hw1].
      destruct h1' as [[[[[? ?] ?] ?] ?] hp1].
      destruct h2' as [[[[[? ?] ?] ?] ?] hp2].
      (* We have a missing link between (v1 : A2) and (v2 : A3) *)
      assert (sim : v1 ∼ v2).
      { eapply trel_trans.
        - eapply trel_sym. eapply inrel_trel. eassumption.
        - apply inrel_trel. assumption.
      }
      destruct hv1 as [_ hv1].
      destruct hv2 as [_ hv2].
      destruct (trel_to_heq sim hv1 hv2) as [p3 hp3].
      (* We can conclude *)
      exists A1, A4, u1, w1.
      exists (sHeqTrans p1 (sHeqTrans p3 p2)).
      repeat split ; try assumption.
      eapply type_HeqTrans'.
      * eassumption.
      * eapply type_HeqTrans' ; eassumption.

        
    (* eq_beta *)
    + (* Translation of the domain *)
      destruct (H _ hΓ) as [S [A'' hA'']].
      assert (th : type_head (head (sSort s1))) by constructor.
      destruct (choose_type th hA'') as [T' [[A' hA'] hh]].
      clear hA'' A'' S.
      destruct T' ; inversion hh. subst. clear hh th.
      (* Translation of the codomain *)
      destruct (H0 _ (trans_snoc hΓ hA'))
        as [S' [B'' hB'']].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type th hB'') as [T' [[B' hB'] hh]].
      clear hB'' B'' S'.
      destruct T' ; inversion hh. subst. clear hh th.
      (* Translation of the in-term *)
      destruct (H1 _ (trans_snoc hΓ hA'))
        as [T' [t'' ht'']].
      destruct (change_type ht'' hB') as [t' ht'].
      clear ht'' T' t''.
      (* Translation of the argument *)
      destruct (H2 _ hΓ) as [A'' [u'' hu'']].
      destruct (change_type hu'' hA') as [u' hu'].
      clear hu'' A'' u''.
      (* Now we conclude using reflexivity *)
      exists (B'{0 := u'}), (B'{0 := u'}).
      exists (sApp (sLambda n A' B' t') n A' B' u'), (t'{0 := u'}).
      exists (sHeqRefl (B'{0 := u'}) (t'{0 := u'})).
      destruct hA' as [[[? ?] ?] ?].
      destruct hB' as [[[? ?] ?] ?].
      destruct ht' as [[[? ?] ?] ?].
      destruct hu' as [[[? ?] ?] ?].
      repeat split.
      * assumption.
      * eapply inrel_subst ; assumption.
      * eapply inrel_subst ; assumption.
      * constructor ; try assumption.
        constructor ; assumption.
      * eapply inrel_subst ; assumption.
      * eapply type_conv.
        -- apply @type_HeqRefl with (s := s2).
           ++ change (sSort s2) with ((sSort s2){0 := u'}).
              eapply typing_subst ; eassumption.
           ++ eapply typing_subst ; eassumption.
        -- apply @type_Heq with (s := s2).
           ++ change (sSort s2) with ((sSort s2){0 := u'}).
              eapply typing_subst ; eassumption.
           ++ change (sSort s2) with ((sSort s2){0 := u'}).
              eapply typing_subst ; eassumption.
           ++ eapply type_App. all: try eassumption.
              eapply type_Lambda. all: eassumption.
           ++ eapply typing_subst ; eassumption.
        -- apply cong_Heq.
           all: try (apply eq_reflexivity).
           ++ change (sSort s2) with ((sSort s2){0 := u'}).
              eapply typing_subst ; eassumption.
           ++ change (sSort s2) with ((sSort s2){0 := u'}).
              eapply typing_subst ; eassumption.
           ++ apply eq_symmetry. eapply eq_beta ; eassumption.
           ++ eapply typing_subst ; eassumption.
    (* eq_conv *)
    + (* Translating the conversion *)
      destruct (H0 _ hΓ)
        as [S' [S'' [T1'' [T2'' [p' h']]]]].
      destruct (eqtrans_trans h') as [hT1'' hT2''].
      destruct h' as [[[[[eΓ eS'] eS''] eT1] eT2] hp'].
      assert (th : type_head (head (sSort s))) by constructor.
      destruct (choose_type th hT1'') as [T [[T1' hT1'] hh]].
      destruct T ; inversion hh. subst. clear hh.
      destruct (choose_type th hT2'') as [T [[T2' hT2'] hh]].
      destruct T ; inversion hh. subst. clear hh th.
      (* Translation the term conversion *)
      destruct (H _ hΓ)
        as [T1''' [T2''' [t1'' [t2'' [q' hq']]]]].
      destruct (eqtrans_trans hq') as [ht1'' ht2''].
      destruct (change_type ht1'' hT1') as [t1' ht1'].
      destruct (change_type ht2'' hT1') as [t2' ht2'].
      (* clear ht1'' ht2'' hq' T1''' T2''' t1'' t2'' q'. *)
      destruct hq' as [[[[[_ eT1'''] eT2'''] et1''] et2''] hq'].
      (* Building the intermediary paths *)
      assert (hpT1 : ∑ p1, Σ ;;; Γ' |-i p1 : sHeq (sSort s) T1' S' T1'').
      { destruct hT1' as [[_ eT1'] hT1'].
        destruct hT1'' as [_ hT1''].
        assert (hr : T1' ∼ T1'').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        apply (trel_to_heq hr) ; assumption.
      }
      destruct hpT1 as [p1 hp1].
      assert (hp2 : ∑ p2, Σ ;;; Γ' |-i p2 : sHeq S'' T2'' (sSort s) T2').
      { destruct hT2' as [[_ eT2'] hT2'].
        destruct hT2'' as [_ hT2''].
        assert (hr : T2'' ∼ T2').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        apply (trel_to_heq hr) ; assumption.
      }
      destruct hp2 as [p2 hp2].
      assert (he : ∑ e, Σ ;;; Γ' |-i e : sHeq (sSort s) T1' (sSort s) T2').
      { exists (sHeqTrans p1 (sHeqTrans p' p2)).
        eapply type_HeqTrans'.
        - eassumption.
        - eapply type_HeqTrans'.
          + eassumption.
          + assumption.
      }
      destruct he as [e' he'].
      rename e into eqt.
      destruct (sort_heq_ex he') as [e he].
      (* Likewise, we build paths for the terms *)
      assert (hq1 : ∑ q1, Σ ;;; Γ' |-i q1 : sHeq T1' t1' T1''' t1'').
      { destruct ht1' as [[_ et1'] ht1'].
        destruct ht1'' as [_ ht1''].
        assert (hr : t1' ∼ t1'').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        apply (trel_to_heq hr) ; assumption.
      }
      destruct hq1 as [q1 hq1].
      assert (hq2 : ∑ q2, Σ ;;; Γ' |-i q2 : sHeq T2''' t2'' T1' t2').
      { destruct ht2' as [[_ et2'] ht2'].
        destruct ht2'' as [_ ht2''].
        assert (hr : t2'' ∼ t2').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        apply (trel_to_heq hr) ; assumption.
      }
      destruct hq2 as [q2 hq2].
      assert (hqq : ∑ qq, Σ ;;; Γ' |-i qq : sHeq T1' t1' T1' t2').
      { exists (sHeqTrans q1 (sHeqTrans q' q2)).
        eapply type_HeqTrans'.
        - eassumption.
        - eapply type_HeqTrans'.
          + eassumption.
          + assumption.
      }
      destruct hqq as [qq hqq].
      assert (hql : ∑ ql, Σ ;;; Γ' |-i ql : sHeq T2' (sTransport T1' T2' e t1') T1' t1').
      { exists (sHeqSym (sHeqTransport e t1')).
        destruct ht1' as [_ ht1'].
        eapply type_HeqSym'. eapply type_HeqTransport' ; eassumption.
      }
      destruct hql as [ql hql].
      assert (hqr : ∑ qr, Σ ;;; Γ' |-i qr : sHeq T1' t2' T2' (sTransport T1' T2' e t2')).
      { exists (sHeqTransport e t2').
        destruct ht2' as [_ ht2'].
        eapply type_HeqTransport' ; eassumption.
      }
      destruct hqr as [qr hqr].
      assert (hqf : ∑ qf, Σ ;;; Γ' |-i qf
                                    : sHeq T2' (sTransport T1' T2' e t1')
                                           T2' (sTransport T1' T2' e t2')).
      { exists (sHeqTrans (sHeqTrans ql qq) qr).
        eapply type_HeqTrans'.
        - eapply type_HeqTrans' ; eassumption.
        - assumption.
      }
      destruct hqf as [qf hqf].
      (* Now we conclude *)
      exists T2', T2', (sTransport T1' T2' e t1'), (sTransport T1' T2' e t2').
      exists qf.
      destruct hT1' as [[[? ?] ?] ?].
      destruct hT2' as [[[? ?] ?] ?].
      destruct ht1' as [[[? ?] ?] ?].
      destruct ht2' as [[[? ?] ?] ?].
      repeat split ; try eassumption.
      * econstructor. assumption.
      * econstructor. assumption.


(* cong_Prod *)
    + (* The domains *)
      destruct (H _ hΓ)
        as [T1 [T2 [A1'' [A2'' [pA h1']]]]].
      destruct (eqtrans_trans h1') as [hA1'' hA2''].
      destruct h1' as [[[[[? ?] ?] ?] ?] hpA''].
      assert (th : type_head (head (sSort s1))) by constructor.
      destruct (choose_type th hA1'') as [T' [[A1' hA1'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh.
      destruct (choose_type th hA2'') as [T' [[A2' hA2'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh th.
      (* Now the codomains *)
      destruct (H0 _ (trans_snoc hΓ hA1'))
        as [S1 [S2 [B1'' [B2'' [pB h2']]]]].
      destruct (eqtrans_trans h2') as [hB1'' hB2''].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type th hB1'') as [T' [[B1' hB1'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh.
      destruct (choose_type th hB2'') as [T' [[B2' hB2'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh th.
      destruct h2' as [[[[[? ?] ?] ?] ?] hpB''].
      (* Now we connect the paths for the domains *)
      assert (hp1 : ∑ p1, Σ ;;; Γ' |-i p1 : sHeq (sSort s1) A1' (sSort s1) A2').
      { destruct hA1' as [[_ eA1'] hA1'].
        destruct hA1'' as [_ hA1''].
        destruct hA2' as [[_ eA2'] hA2'].
        destruct hA2'' as [_ hA2''].
        assert (hr : A1' ∼ A1'').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq hr ltac:(eassumption) ltac:(eassumption))
        as [pl hpl].
        assert (hr' : A2'' ∼ A2').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq hr' ltac:(eassumption) ltac:(eassumption))
          as [pr hpr].
        exists (sHeqTrans (sHeqTrans pl pA) pr).
        eapply type_HeqTrans'.
        - eapply type_HeqTrans' ; eassumption.
        - eassumption.
      }
      destruct hp1 as [p1 hp1].
      (* And then the paths for the codomains *)
      pose (Γ1 := nil ,, svass n1 A1').
      pose (Γ2 := nil ,, svass n2 A2').
      pose (Δ := mix Γ' Γ1 Γ2).
      assert (hp2 : ∑ p2, Σ ;;; Γ' ,,, Γ1 |-i p2 : sHeq (sSort s2) B1'
                                                       (sSort s2) B2').
      { destruct hB1' as [[_ eB1'] hB1'].
        destruct hB1'' as [_ hB1''].
        destruct hB2' as [[_ eB2'] hB2'].
        destruct hB2'' as [_ hB2''].
        assert (hr : B1' ∼ B1'').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq hr ltac:(eassumption) ltac:(eassumption))
        as [pl hpl].
        assert (hr' : B2'' ∼ B2').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq hr' ltac:(eassumption) ltac:(eassumption))
          as [pr hpr].
        exists (sHeqTrans (sHeqTrans pl pB) pr).
        eapply type_HeqTrans'.
        - eapply type_HeqTrans' ; eassumption.
        - eassumption.
      }
      destruct hp2 as [p2 hp2].
      assert (hp3 : ∑ p3, Σ ;;; Δ |-i p3 : sHeq (sSort s2)
                                               (llift0 #|Γ1| B1')
                                               (sSort s2)
                                               (llift0 #|Γ1| B2')
             ).
      { exists (llift0 #|Γ1| p2).
        match goal with
        | |- _ ;;; _ |-i _ : ?T =>
          change T with (llift0 #|Γ1| (sHeq (sSort s2) B1' (sSort s2) B2'))
        end.
        eapply type_llift0 ; easy.
      }
      destruct hp3 as [p3 hp3].
      (* Also translating the typing hypothesis for B2 *)
      destruct (H2 _ (trans_snoc hΓ hA2'))
        as [S' [B2''' hB2''']].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type th hB2''') as [T' [[tB2 htB2] hh]].
      clear hB2''' B2''' S'.
      destruct T' ; inversion hh. subst. clear hh th.
      (* Now we can use the strong version of the lemma to build a path between
         B2' and tB2 !
       *)
      assert (hp4 : ∑ p4, Σ ;;; Δ |-i p4 : sHeq (sSort s2) (llift0 #|Γ1| B2')
                                               (sSort s2) (rlift0 #|Γ1| tB2)
             ).
      { change (sSort s2) with (llift0 #|Γ1| (sSort s2)) at 1.
        change (sSort s2) with (rlift0 #|Γ1| (sSort s2)) at 2.
        eapply trel_to_heq'.
        - destruct htB2 as [[? ?] ?].
          destruct hB2' as [[? ?] ?].
          eapply trel_trans.
          + eapply trel_sym. eapply inrel_trel. eassumption.
          + apply inrel_trel. assumption.
        - reflexivity.
        - destruct hB2' as [[? ?] ?]. assumption.
        - destruct htB2 as [[? ?] ?]. assumption.
      }
      destruct hp4 as [p4 hp4].
      (* This gives us a better path *)
      assert (hp5 : ∑ p5, Σ ;;; Δ |-i p5 : sHeq (sSort s2) (llift0 #|Γ1| B1')
                                               (sSort s2) (rlift0 #|Γ1| tB2)
             ).
      { exists (sHeqTrans p3 p4).
        eapply type_HeqTrans' ; eassumption.
      }
      destruct hp5 as [p5 hp5].
      (* We can finally conclude! *)
      exists (sSort (max_sort s1 s2)), (sSort (max_sort s1 s2)).
      exists (sProd n1 A1' B1'), (sProd n2 A2' tB2).
      exists (sCongProd B1' tB2 p1 p5).
      destruct hA1' as [[[? ?] ?] ?].
      destruct hB1' as [[[? ?] ?] ?].
      destruct hA2' as [[[? ?] ?] ?].
      destruct htB2 as [[[? ?] ?] ?].
      repeat split.
      all: try constructor. all: try assumption.
      eapply type_CongProd'.
      * assumption.
      * cbn in hp5. rewrite <- llift_substProj, <- rlift_substProj in hp5.
        rewrite !llift00, !rlift00 in hp5.
        apply hp5.
      * assumption.
      * assumption.


        
    (* cong_Lambda *)
    + (* The domains *)
      destruct (H _ hΓ)
        as [T1 [T2 [A1'' [A2'' [pA h1']]]]].
      destruct (eqtrans_trans h1') as [hA1'' hA2''].
      destruct h1' as [[[[[? ?] ?] ?] ?] hpA''].
      assert (th : type_head (head (sSort s1))) by constructor.
      destruct (choose_type th hA1'') as [T' [[A1' hA1'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh.
      destruct (choose_type th hA2'') as [T' [[A2' hA2'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh th.
      (* Now the codomains *)
      destruct (H0 _ (trans_snoc hΓ hA1'))
        as [S1 [S2 [B1'' [B2'' [pB h2']]]]].
      destruct (eqtrans_trans h2') as [hB1'' hB2''].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type th hB1'') as [T' [[B1' hB1'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh.
      destruct (choose_type th hB2'') as [T' [[B2' hB2'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh th.
      destruct h2' as [[[[[? ?] ?] ?] ?] hpB''].
      (* Now we connect the paths for the domains *)
      assert (hp1 : ∑ p1, Σ ;;; Γ' |-i p1 : sHeq (sSort s1) A1' (sSort s1) A2').
      { destruct hA1' as [[_ eA1'] hA1'].
        destruct hA1'' as [_ hA1''].
        destruct hA2' as [[_ eA2'] hA2'].
        destruct hA2'' as [_ hA2''].
        assert (hr : A1' ∼ A1'').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq hr ltac:(eassumption) ltac:(eassumption))
        as [pl hpl].
        assert (hr' : A2'' ∼ A2').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq hr' ltac:(eassumption) ltac:(eassumption))
          as [pr hpr].
        exists (sHeqTrans (sHeqTrans pl pA) pr).
        eapply type_HeqTrans'.
        - eapply type_HeqTrans' ; eassumption.
        - eassumption.
      }
      destruct hp1 as [p1 hp1].
      (* And then the paths for the codomains *)
      pose (Γ1 := nil ,, svass n1 A1').
      pose (Γ2 := nil ,, svass n2 A2').
      pose (Δ := mix Γ' Γ1 Γ2).
      assert (hp2 : ∑ p2, Σ ;;; Γ' ,,, Γ1 |-i p2 : sHeq (sSort s2) B1'
                                                       (sSort s2) B2').
      { destruct hB1' as [[_ eB1'] hB1'].
        destruct hB1'' as [_ hB1''].
        destruct hB2' as [[_ eB2'] hB2'].
        destruct hB2'' as [_ hB2''].
        assert (hr : B1' ∼ B1'').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq hr ltac:(eassumption) ltac:(eassumption))
        as [pl hpl].
        assert (hr' : B2'' ∼ B2').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq hr' ltac:(eassumption) ltac:(eassumption))
          as [pr hpr].
        exists (sHeqTrans (sHeqTrans pl pB) pr).
        eapply type_HeqTrans'.
        - eapply type_HeqTrans' ; eassumption.
        - eassumption.
      }
      destruct hp2 as [p2 hp2].
      assert (hp3 : ∑ p3, Σ ;;; Δ |-i p3 : sHeq (sSort s2)
                                               (llift0 #|Γ1| B1')
                                               (sSort s2)
                                               (llift0 #|Γ1| B2')
             ).
      { exists (llift0 #|Γ1| p2).
        match goal with
        | |- _ ;;; _ |-i _ : ?T =>
          change T with (llift0 #|Γ1| (sHeq (sSort s2) B1' (sSort s2) B2'))
        end.
        eapply type_llift0 ; easy.
      }
      destruct hp3 as [p3 hp3].
      (* Also translating the typing hypothesis for B2 *)
      destruct (H3 _ (trans_snoc hΓ hA2'))
        as [S' [B2''' hB2''']].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type th hB2''') as [T' [[tB2 htB2] hh]].
      clear hB2''' B2''' S'.
      destruct T' ; inversion hh. subst. clear hh th.
      (* Now we can use the strong version of the lemma to build a path between
         B2' and tB2 !
       *)
      assert (hp4 : ∑ p4, Σ ;;; Δ |-i p4 : sHeq (sSort s2) (llift0 #|Γ1| B2')
                                               (sSort s2) (rlift0 #|Γ1| tB2)
             ).
      { change (sSort s2) with (llift0 #|Γ1| (sSort s2)) at 1.
        change (sSort s2) with (rlift0 #|Γ1| (sSort s2)) at 2.
        eapply trel_to_heq'.
        - destruct htB2 as [[? ?] ?].
          destruct hB2' as [[? ?] ?].
          eapply trel_trans.
          + eapply trel_sym. eapply inrel_trel. eassumption.
          + apply inrel_trel. assumption.
        - reflexivity.
        - destruct hB2' as [[? ?] ?]. assumption.
        - destruct htB2 as [[? ?] ?]. assumption.
      }
      destruct hp4 as [p4 hp4].
      (* This gives us a better path *)
      assert (hp5 : ∑ p5, Σ ;;; Δ |-i p5 : sHeq (sSort s2) (llift0 #|Γ1| B1')
                                               (sSort s2) (rlift0 #|Γ1| tB2)
             ).
      { exists (sHeqTrans p3 p4).
        eapply type_HeqTrans' ; eassumption.
      }
      destruct hp5 as [p5 hp5].
      (* Cleaning *)
      clear hp4 p4 hp3 p3 hp2 p2.
      clear hB2' B2' hB2'' hpB'' hB1'' hpA'' hA1'' hA2''.
      (* clear i8 i7 i6 i5 i4 S1 S2 B1'' B2'' pB. *)
      (* clear i3 i2 i1 i0 i T1 T2 A1'' A2'' pA. *)
      clear pA pB pi2_5 B1'' pi2_6 B2''.
      rename p1 into pA, p5 into pB, hp1 into hpA, hp5 into hpB.
      rename tB2 into B2', htB2 into hB2'.
      (* We can now focus on the function terms *)
      destruct (H1 _ (trans_snoc hΓ hA1'))
        as [B1'' [B1''' [t1'' [t2'' [pt h3']]]]].
      destruct (eqtrans_trans h3') as [ht1'' ht2''].
      destruct (change_type ht1'' hB1') as [t1' ht1'].
      destruct (change_type ht2'' hB1') as [t2' ht2'].
      destruct (H5 _ (trans_snoc hΓ hA2'))
        as [B2'' [t2''' ht2''']].
      destruct (change_type ht2''' hB2') as [tt2 htt2].
      assert (hq1 : ∑ q1, Σ ;;; Γ' ,, svass n1 A1' |-i q1 : sHeq B1' t1' B1' t2').
      { destruct h3' as [[[[[? ?] ?] ?] ?] hpt''].
        destruct ht1' as [[_ et1'] ht1'].
        destruct ht1'' as [_ ht1''].
        destruct ht2' as [[_ et2'] ht2'].
        destruct ht2'' as [_ ht2''].
        assert (hr : t1' ∼ t1'').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - apply inrel_trel. assumption.
        }
        destruct (trel_to_heq hr ltac:(eassumption) ltac:(eassumption))
        as [pl hpl].
        assert (hr' : t2'' ∼ t2').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq hr' ltac:(eassumption) ltac:(eassumption))
          as [pr hpr].
        exists (sHeqTrans (sHeqTrans pl pt) pr).
        eapply type_HeqTrans'.
        - eapply type_HeqTrans' ; eassumption.
        - assumption.
      }
      destruct hq1 as [q1 hq1].
      assert (hq2 : ∑ q2,
        Σ ;;; Δ |-i q2 : sHeq (llift0 #|Γ1| B1') (llift0 #|Γ1| t1')
                             (llift0 #|Γ1| B1') (llift0 #|Γ1| t2')
      ).
      { exists (llift0 #|Γ1| q1).
        match goal with
        | |- _ ;;; _ |-i _ : ?T =>
          change T with (llift0 #|Γ1| (sHeq B1' t1' B1' t2'))
        end.
        eapply type_llift0 ; easy.
      }
      destruct hq2 as [q2 hq2].
      assert (hq3 : ∑ q3,
        Σ ;;; Δ |-i q3 : sHeq (llift0 #|Γ1| B1') (llift0 #|Γ1| t2')
                             (rlift0 #|Γ1| B2') (rlift0 #|Γ1| tt2)
      ).
      { eapply trel_to_heq'.
        - destruct htt2 as [[? ?] ?].
          destruct ht2' as [[? ?] ?].
          eapply trel_trans.
          + eapply trel_sym. eapply inrel_trel. eassumption.
          + apply inrel_trel. assumption.
        - reflexivity.
        - destruct ht2' as [[? ?] ?]. assumption.
        - destruct htt2 as [[? ?] ?]. assumption.
      }
      destruct hq3 as [q3 hq3].
      assert (hq4 : ∑ q4,
        Σ ;;; Δ |-i q4 : sHeq (llift0 #|Γ1| B1') (llift0 #|Γ1| t1')
                             (rlift0 #|Γ1| B2') (rlift0 #|Γ1| tt2)
      ).
      { exists (sHeqTrans q2 q3).
        eapply type_HeqTrans' ; eassumption.
      }
      destruct hq4 as [qt hqt].
      (* We're almost done.
         However, our translation of (sLambda n2 A2 B2 t2) has to live in
         our translation of (sProd n' A1 B1).
         This is where the path between the two types comes into action.
       *)
      assert (hty : ∑ pty,
        Σ ;;; Γ' |-i pty : sHeq (sSort (max_sort s1 s2)) (sProd n2 A2' B2')
                               (sSort (max_sort s1 s2)) (sProd n1 A1' B1')

      ).
      { exists (sHeqSym (sCongProd B1' B2' pA pB)).
        destruct hB1' as [[[? ?] ?] ?].
        destruct hB2' as [[[? ?] ?] ?].
        eapply type_HeqSym'. eapply type_CongProd'.
        - assumption.
        - cbn in hpB. rewrite <- llift_substProj, <- rlift_substProj in hpB.
          rewrite !llift00, !rlift00 in hpB.
          apply hpB.
        - assumption.
        - assumption.
      }
      destruct hty as [pty hty].
      destruct (sort_heq_ex hty) as [eT heT].
      (* We move the lambda now. *)
      pose (tλ :=
              sTransport (sProd n2 A2' B2') (sProd n1 A1' B1')
                         eT (sLambda n2 A2' B2' tt2)
      ).
      (* Now we conclude *)
      exists (sProd n1 A1' B1'), (sProd n1 A1' B1').
      exists (sLambda n1 A1' B1' t1'), tλ.
      exists (sHeqTrans (sCongLambda B1' B2' t1' tt2 pA pB qt)
                   (sHeqTransport eT (sLambda n2 A2' B2' tt2))).
      destruct ht1' as [[[? ?] ?] ?].
      destruct htt2 as [[[? ?] ?] ?].
      destruct hA1' as [[[? ?] ?] ?].
      destruct hA2' as [[[? ?] ?] ?].
      destruct hB1' as [[[? ?] ?] ?].
      destruct hB2' as [[[? ?] ?] ?].
      repeat split.
      * assumption.
      * constructor ; assumption.
      * constructor ; assumption.
      * constructor ; assumption.
      * constructor. constructor ; assumption.
      * eapply type_HeqTrans'.
        -- eapply type_CongLambda'.
           ++ eassumption.
           ++ cbn in hpB. rewrite <- llift_substProj, <- rlift_substProj in hpB.
              rewrite !llift00, !rlift00 in hpB.
              apply hpB.
           ++ cbn in hqt. rewrite <- !llift_substProj, <- !rlift_substProj in hqt.
              rewrite !llift00, !rlift00 in hqt.
              apply hqt.
           ++ assumption.
           ++ eassumption.
           ++ assumption.
           ++ assumption.
        -- eapply type_HeqTransport'.
           ++ eapply type_Lambda ; eassumption.
           ++ eassumption.

    (* cong_App *)
    + (* The domains *)
      destruct (H _ hΓ)
        as [T1 [T2 [A1'' [A2'' [pA h1']]]]].
      destruct (eqtrans_trans h1') as [hA1'' hA2''].
      destruct h1' as [[[[[? ?] ?] ?] ?] hpA''].
      assert (th : type_head (head (sSort s1))) by constructor.
      destruct (choose_type th hA1'') as [T' [[A1' hA1'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh.
      destruct (choose_type th hA2'') as [T' [[A2' hA2'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh th.
      (* Now the codomains *)
      destruct (H0 _ (trans_snoc hΓ hA1'))
        as [S1 [S2 [B1'' [B2'' [pB h2']]]]].
      destruct (eqtrans_trans h2') as [hB1'' hB2''].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type th hB1'') as [T' [[B1' hB1'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh.
      destruct (choose_type th hB2'') as [T' [[B2' hB2'] hh]].
      destruct T' ; inversion hh. subst.
      clear hh th.
      destruct h2' as [[[[[? ?] ?] ?] ?] hpB''].
      (* Now we connect the paths for the domains *)
      assert (hp1 : ∑ p1, Σ ;;; Γ' |-i p1 : sHeq (sSort s1) A1' (sSort s1) A2').
      { destruct hA1' as [[_ eA1'] hA1'].
        destruct hA1'' as [_ hA1''].
        destruct hA2' as [[_ eA2'] hA2'].
        destruct hA2'' as [_ hA2''].
        assert (hr : A1' ∼ A1'').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq hr ltac:(eassumption) ltac:(eassumption))
        as [pl hpl].
        assert (hr' : A2'' ∼ A2').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq hr' ltac:(eassumption) ltac:(eassumption))
          as [pr hpr].
        exists (sHeqTrans (sHeqTrans pl pA) pr).
        eapply type_HeqTrans'.
        - eapply type_HeqTrans' ; eassumption.
        - eassumption.
      }
      destruct hp1 as [p1 hp1].
      (* And then the paths for the codomains *)
      pose (Γ1 := nil ,, svass n1 A1').
      pose (Γ2 := nil ,, svass n2 A2').
      pose (Δ := mix Γ' Γ1 Γ2).
      assert (hp2 : ∑ p2, Σ ;;; Γ' ,,, Γ1 |-i p2 : sHeq (sSort s2) B1'
                                                       (sSort s2) B2').
      { destruct hB1' as [[_ eB1'] hB1'].
        destruct hB1'' as [_ hB1''].
        destruct hB2' as [[_ eB2'] hB2'].
        destruct hB2'' as [_ hB2''].
        assert (hr : B1' ∼ B1'').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq hr ltac:(eassumption) ltac:(eassumption))
        as [pl hpl].
        assert (hr' : B2'' ∼ B2').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq hr' ltac:(eassumption) ltac:(eassumption))
          as [pr hpr].
        exists (sHeqTrans (sHeqTrans pl pB) pr).
        eapply type_HeqTrans'.
        - eapply type_HeqTrans' ; eassumption.
        - eassumption.
      }
      destruct hp2 as [p2 hp2].
      assert (hp3 : ∑ p3, Σ ;;; Δ |-i p3 : sHeq (sSort s2)
                                               (llift0 #|Γ1| B1')
                                               (sSort s2)
                                               (llift0 #|Γ1| B2')
             ).
      { exists (llift0 #|Γ1| p2).
        match goal with
        | |- _ ;;; _ |-i _ : ?T =>
          change T with (llift0 #|Γ1| (sHeq (sSort s2) B1' (sSort s2) B2'))
        end.
        eapply type_llift0 ; easy.
      }
      destruct hp3 as [p3 hp3].
      (* Also translating the typing hypothesis for B2 *)
      destruct (H4 _ (trans_snoc hΓ hA2'))
        as [S' [B2''' hB2''']].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type th hB2''') as [T' [[tB2 htB2] hh]].
      clear hB2''' B2''' S'.
      destruct T' ; inversion hh. subst. clear hh th.
      (* Now we can use the strong version of the lemma to build a path between
         B2' and tB2 !
       *)
      assert (hp4 : ∑ p4, Σ ;;; Δ |-i p4 : sHeq (sSort s2) (llift0 #|Γ1| B2')
                                               (sSort s2) (rlift0 #|Γ1| tB2)
             ).
      { change (sSort s2) with (llift0 #|Γ1| (sSort s2)) at 1.
        change (sSort s2) with (rlift0 #|Γ1| (sSort s2)) at 2.
        eapply trel_to_heq'.
        - destruct htB2 as [[? ?] ?].
          destruct hB2' as [[? ?] ?].
          eapply trel_trans.
          + eapply trel_sym. eapply inrel_trel. eassumption.
          + apply inrel_trel. assumption.
        - reflexivity.
        - destruct hB2' as [[? ?] ?]. assumption.
        - destruct htB2 as [[? ?] ?]. assumption.
      }
      destruct hp4 as [p4 hp4].
      (* This gives us a better path *)
      assert (hp5 : ∑ p5, Σ ;;; Δ |-i p5 : sHeq (sSort s2) (llift0 #|Γ1| B1')
                                               (sSort s2) (rlift0 #|Γ1| tB2)
             ).
      { exists (sHeqTrans p3 p4).
        eapply type_HeqTrans' ; eassumption.
      }
      destruct hp5 as [p5 hp5].
      (* Cleaning *)
      clear hp4 p4 hp3 p3 hp2 p2.
      clear hB2' B2' hB2'' hpB'' hB1'' hpA'' hA1'' hA2''.
      (* clear i8 i7 i6 i5 i4 S1 S2 B1'' B2'' pB. *)
      (* clear i3 i2 i1 i0 i T1 T2 A1'' A2'' pA. *)
      clear pA pB pi2_1 pi2_2 A1'' A2''.
      rename p1 into pA, p5 into pB, hp1 into hpA, hp5 into hpB.
      rename tB2 into B2', htB2 into hB2'.
      (* We can now translate the functions. *)
      destruct (H1 _ hΓ)
        as [P1 [P1' [t1'' [t2'' [pt h3']]]]].
      destruct (eqtrans_trans h3') as [ht1'' ht2''].
      destruct (change_type ht1'' (trans_Prod hΓ hA1' hB1')) as [t1' ht1'].
      destruct (change_type ht2'' (trans_Prod hΓ hA1' hB1')) as [t2' ht2'].
      destruct h3' as [[[[[? ?] ?] ?] ?] hpt].
      destruct (H6 _ hΓ)
        as [P2 [t2''' ht2''']].
      destruct (change_type ht2''' (trans_Prod hΓ hA2' hB2')) as [tt2 htt2].
      clear ht2''' t2''' P2.
      assert (hqt : ∑ qt,
        Σ ;;; Γ' |-i qt : sHeq (sProd n1 A1' B1') t1' (sProd n2 A2' B2') tt2
      ).
      { destruct ht1'' as [[[? ?] ?] ?].
        destruct ht2'' as [[[? ?] ?] ?].
        destruct ht1' as [[[? ?] ?] ?].
        destruct ht2' as [[[? ?] ?] ?].
        destruct htt2 as [[[? ?] ?] ?].
        assert (r1 : t1' ∼ t1'').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - apply inrel_trel. assumption.
        }
        destruct (trel_to_heq r1 ltac:(eassumption) ltac:(eassumption))
          as [pl hpl].
        assert (r2 : t2'' ∼ tt2).
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - apply inrel_trel. assumption.
        }
        destruct (trel_to_heq r2 ltac:(eassumption) ltac:(eassumption))
          as [pr hpr].
        exists (sHeqTrans pl (sHeqTrans pt pr)).
        eapply type_HeqTrans'.
        - eassumption.
        - eapply type_HeqTrans' ; eassumption.
      }
      destruct hqt as [qt hqt].
      (* We then translate the arguments. *)
      destruct (H2 _ hΓ)
        as [A1'' [A1''' [u1'' [u2'' [pu h4']]]]].
      destruct (eqtrans_trans h4') as [hu1'' hu2''].
      destruct (change_type hu1'' hA1') as [u1' hu1'].
      destruct h4' as [[[[[? ?] ?] ?] ?] hpu].
      destruct (H8 _ hΓ) as [A2'' [u2''' hu2''']].
      destruct (change_type hu2''' hA2') as [tu2 htu2].
      clear hu2''' u2''' A2''.
      assert (hqu : ∑ qu, Σ ;;; Γ' |-i qu : sHeq A1' u1' A2' tu2).
      { destruct hu1'' as [[[? ?] ?] ?].
        destruct hu2'' as [[[? ?] ?] ?].
        destruct hu1' as [[[? ?] ?] ?].
        destruct htu2 as [[[? ?] ?] ?].
        assert (r1 : u1' ∼ u1'').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - apply inrel_trel. assumption.
        }
        destruct (trel_to_heq r1 ltac:(eassumption) ltac:(eassumption))
          as [pl hpl].
        assert (r2 : u2'' ∼ tu2).
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - apply inrel_trel. assumption.
        }
        destruct (trel_to_heq r2 ltac:(eassumption) ltac:(eassumption))
          as [pr hpr].
        exists (sHeqTrans pl (sHeqTrans pu pr)).
        eapply type_HeqTrans'.
        - eassumption.
        - eapply type_HeqTrans' ; eassumption.
      }
      destruct hqu as [qu hqu].
      (* We have an equality between Apps now *)
      assert (happ : ∑ qapp,
        Σ ;;; Γ' |-i qapp : sHeq (B1'{0 := u1'}) (sApp t1' n1 A1' B1' u1')
                                (B2'{0 := tu2}) (sApp tt2 n2 A2' B2' tu2)
      ).
      { exists (sCongApp B1' B2' qt pA pB qu).
        destruct hB1' as [[[? ?] ?] ?].
        destruct hB2' as [[[? ?] ?] ?].
        eapply type_CongApp'.
        - eassumption.
        - cbn in hpB. rewrite <- llift_substProj, <- rlift_substProj in hpB.
          rewrite !llift00, !rlift00 in hpB.
          apply hpB.
        - assumption.
        - assumption.
        - assumption.
        - assumption.
      }
      destruct happ as [qapp happ].
      (* Finally we translate the right App to put it in the left Prod *)
      rename e into eA.
      pose (e := sHeqTypeEq (sHeqSym qapp)).
      pose (tapp := sTransport (B2' {0 := tu2}) (B1'{0 := u1'}) e (sApp tt2 n2 A2' B2' tu2)).
      (* We conclude *)
      exists (B1'{0 := u1'}), (B1'{0 := u1'}).
      exists (sApp t1' n1 A1' B1' u1'), tapp.
      exists (sHeqTrans qapp (sHeqTransport e (sApp tt2 n2 A2' B2' tu2))).
      destruct ht1' as [[[? ?] ?] ?].
      destruct htt2 as [[[? ?] ?] ?].
      destruct hu1' as [[[? ?] ?] ?].
      destruct htu2 as [[[? ?] ?] ?].
      destruct hA1' as [[[? ?] ?] ?].
      destruct hA2' as [[[? ?] ?] ?].
      destruct hB1' as [[[? ?] ?] ?].
      destruct hB2' as [[[? ?] ?] ?].
      repeat split.
      * assumption.
      * eapply inrel_subst ; assumption.
      * eapply inrel_subst ; assumption.
      * constructor ; assumption.
      * constructor. constructor ; assumption.
      * eapply type_HeqTrans'.
        -- eassumption.
        -- eapply type_HeqTransport'.
           ++ eapply type_App ; eassumption.
           ++ eapply type_HeqTypeEq'.
              ** eapply type_HeqSym'. eassumption.
              ** match goal with
                 | |- _ ;;; _ |-i _ : ?S =>
                   change S with (S {0 := tu2})
                 end.
                 eapply typing_subst ; eassumption.

    (* cong_Eq *)
    + destruct (H _ hΓ)
        as [T1 [T2 [A1' [A2' [pA h1']]]]].
      destruct (H0 _ hΓ)
        as [A1'' [A1''' [u1' [u2' [pu h2']]]]].
      destruct (H1 _ hΓ)
        as [A1'''' [A1''''' [v1' [v2' [pv h3']]]]].
      destruct (eqtrans_trans h1') as [hA1' hA2'].
      destruct (eqtrans_trans h2') as [hu1' hu2'].
      destruct (eqtrans_trans h3') as [hv1' hv2'].
      destruct h1' as [[[[[? ?] ?] ?] ?] hpA].
      destruct h2' as [[[[[? ?] ?] ?] ?] hpu].
      destruct h3' as [[[[[? ?] ?] ?] ?] hpv].
      (* We need to chain translations a lot to use sCongEq *)
      assert (th : type_head (head (sSort s))) by constructor.
      destruct (choose_type th hA1') as [T' [[tA1 htA1] hh]].
      destruct T' ; inversion hh. subst.
      clear th hh.
      assert (th : type_head (head (sSort s))) by constructor.
      destruct (choose_type th hA2') as [T' [[tA2 htA2] hh]].
      destruct T' ; inversion hh. subst.
      clear th hh.
      (* For the types we build the missing hequalities *)
      assert (hp : ∑ p, Σ ;;; Γ' |-i p : sHeq (sSort s) tA1 (sSort s) tA2).
      { destruct hA1' as [_ hA1'].
        destruct htA1 as [[[? ?] ?] htA1].
        assert (sim1 : tA1 ∼ A1').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq sim1 htA1 hA1') as [p1 hp1].
        destruct hA2' as [_ hA2'].
        destruct htA2 as [[[? ?] ?] htA2].
        assert (sim2 : A2' ∼ tA2).
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq sim2 hA2' htA2) as [p2 hp2].
        exists (sHeqTrans p1 (sHeqTrans pA p2)).
        eapply type_HeqTrans'.
        - eassumption.
        - eapply type_HeqTrans' ; eassumption.
      }
      destruct hp as [qA hqA].
      (* Now we need to do the same for the terms *)
      destruct (change_type hu1' htA1) as [tu1 htu1].
      destruct (change_type hu2' htA1) as [tu2 htu2].
      destruct (change_type hv1' htA1) as [tv1 htv1].
      destruct (change_type hv2' htA1) as [tv2 htv2].
      assert (hqu : ∑ qu, Σ ;;; Γ' |-i qu : sHeq tA1 tu1 tA1 tu2).
      { destruct hu1' as [_ hu1'].
        destruct htu1 as [[[? ?] ?] htu1].
        assert (sim1 : tu1 ∼ u1').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq sim1 htu1 hu1') as [pl hpl].
        destruct hu2' as [_ hu2'].
        destruct htu2 as [[[? ?] ?] htu2].
        assert (sim2 : u2' ∼ tu2).
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq sim2 hu2' htu2) as [pr hpr].
        exists (sHeqTrans (sHeqTrans pl pu) pr).
        eapply type_HeqTrans'.
        - eapply type_HeqTrans' ; eassumption.
        - eassumption.
      }
      destruct hqu as [qu hqu].
      assert (hqv : ∑ qv, Σ ;;; Γ' |-i qv : sHeq tA1 tv1 tA1 tv2).
      { destruct hv1' as [_ hv1'].
        destruct htv1 as [[[? ?] ?] htv1].
        assert (sim1 : tv1 ∼ v1').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq sim1 htv1 hv1') as [pl hpl].
        destruct hv2' as [_ hv2'].
        destruct htv2 as [[[? ?] ?] htv2].
        assert (sim2 : v2' ∼ tv2).
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq sim2 hv2' htv2) as [pr hpr].
        exists (sHeqTrans (sHeqTrans pl pv) pr).
        eapply type_HeqTrans'.
        - eapply type_HeqTrans' ; eassumption.
        - eassumption.
      }
      destruct hqv as [qv hqv].
      (* We move terms back into tA2 *)
      destruct (sort_heq_ex hqA) as [eA heA].
      pose (ttu2 := sTransport tA1 tA2 eA tu2).
      assert (hq : ∑ q, Σ ;;; Γ' |-i q : sHeq tA1 tu1 tA2 ttu2).
      { exists (sHeqTrans qu (sHeqTransport eA tu2)).
        destruct htu2 as [[[? ?] ?] ?].
        destruct htA1 as [[[? ?] ?] ?].
        destruct htA2 as [[[? ?] ?] ?].
        eapply type_HeqTrans'.
        - eassumption.
        - eapply type_HeqTransport ; eassumption.
      }
      destruct hq as [qu' hqu'].
      pose (ttv2 := sTransport tA1 tA2 eA tv2).
      assert (hq : ∑ q, Σ ;;; Γ' |-i q : sHeq tA1 tv1 tA2 ttv2).
      { exists (sHeqTrans qv (sHeqTransport eA tv2)).
        destruct htv2 as [[[? ?] ?] ?].
        destruct htA1 as [[[? ?] ?] ?].
        destruct htA2 as [[[? ?] ?] ?].
        eapply type_HeqTrans'.
        - eassumption.
        - eapply type_HeqTransport ; eassumption.
      }
      destruct hq as [qv' hqv'].
      exists (sSort s), (sSort s), (sEq tA1 tu1 tv1), (sEq tA2 ttu2 ttv2).
      exists (sCongEq qA qu' qv').
      destruct htu1 as [[[? ?] ?] ?].
      destruct htu2 as [[[? ?] ?] ?].
      destruct htA1 as [[[? ?] ?] ?].
      destruct htA2 as [[[? ?] ?] ?].
      destruct htv1 as [[[? ?] ?] ?].
      destruct htv2 as [[[? ?] ?] ?].
      repeat split ; try eassumption.
      * econstructor ; assumption.
      * econstructor ; try assumption.
        -- econstructor ; eassumption.
        -- econstructor ; eassumption.
      * eapply type_CongEq' ; assumption.

    (* cong_Refl *)
    + destruct (H _ hΓ)
        as [T1 [T2 [A1' [A2' [pA h1']]]]].
      destruct (H0 _ hΓ)
        as [A1'' [A1''' [u1' [u2' [pu h2']]]]].
      destruct (eqtrans_trans h1') as [hA1' hA2'].
      destruct (eqtrans_trans h2') as [hu1' hu2'].
      destruct h1' as [[[[[? ?] ?] ?] ?] hpA].
      destruct h2' as [[[[[? ?] ?] ?] ?] hpu].
      (* The types *)
      assert (th : type_head (head (sSort s))) by constructor.
      destruct (choose_type th hA1') as [T' [[tA1 htA1] hh]].
      destruct T' ; inversion hh. subst.
      clear th hh.
      assert (th : type_head (head (sSort s))) by constructor.
      destruct (choose_type th hA2') as [T' [[tA2 htA2] hh]].
      destruct T' ; inversion hh. subst.
      clear th hh.
      assert (hp : ∑ p, Σ ;;; Γ' |-i p : sHeq (sSort s) tA1 (sSort s) tA2).
      { destruct hA1' as [_ hA1'].
        destruct htA1 as [[[? ?] ?] htA1].
        assert (sim1 : tA1 ∼ A1').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq sim1 htA1 hA1') as [p1 hp1].
        destruct hA2' as [_ hA2'].
        destruct htA2 as [[[? ?] ?] htA2].
        assert (sim2 : A2' ∼ tA2).
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq sim2 hA2' htA2) as [p2 hp2].
        exists (sHeqTrans p1 (sHeqTrans pA p2)).
        eapply type_HeqTrans'.
        - eassumption.
        - eapply type_HeqTrans' ; eassumption.
      }
      destruct hp as [qA hqA].
      (* The terms *)
      destruct (change_type hu1' htA1) as [tu1 htu1].
      destruct (change_type hu2' htA1) as [tu2 htu2].
      assert (hqu : ∑ qu, Σ ;;; Γ' |-i qu : sHeq tA1 tu1 tA1 tu2).
      { destruct hu1' as [_ hu1'].
        destruct htu1 as [[[? ?] ?] htu1].
        assert (sim1 : tu1 ∼ u1').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq sim1 htu1 hu1') as [pl hpl].
        destruct hu2' as [_ hu2'].
        destruct htu2 as [[[? ?] ?] htu2].
        assert (sim2 : u2' ∼ tu2).
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq sim2 hu2' htu2) as [pr hpr].
        exists (sHeqTrans (sHeqTrans pl pu) pr).
        eapply type_HeqTrans'.
        - eapply type_HeqTrans' ; eassumption.
        - eassumption.
      }
      destruct hqu as [qu hqu].
      (* tu2 isn't in the right place, so we need to chain one last equality. *)
      destruct (sort_heq_ex hqA) as [eA heA].
      pose (ttu2 := sTransport tA1 tA2 eA tu2).
      assert (hq : ∑ q, Σ ;;; Γ' |-i q : sHeq tA1 tu1 tA2 ttu2).
      { exists (sHeqTrans qu (sHeqTransport eA tu2)).
        destruct htu2 as [[[? ?] ?] ?].
        destruct htA1 as [[[? ?] ?] ?].
        destruct htA2 as [[[? ?] ?] ?].
        eapply type_HeqTrans'.
        - eassumption.
        - eapply type_HeqTransport ; eassumption.
      }
      destruct hq as [q hq].
      (* We're still not there yet as we need to have two translations of the
         same type. *)
      assert (pE : ∑ pE, Σ ;;; Γ' |-i pE : sHeq (sSort s) (sEq tA2 ttu2 ttu2)
                                               (sSort s) (sEq tA1 tu1 tu1)).
      { exists (sHeqSym (sCongEq qA q q)).
        eapply type_HeqSym'. eapply type_CongEq' ; eassumption.
      }
      destruct pE as [pE hpE].
      assert (eE : ∑ eE, Σ ;;; Γ' |-i eE : sEq (sSort s) (sEq tA2 ttu2 ttu2)
                                              (sEq tA1 tu1 tu1)).
      { eapply (sort_heq_ex hpE). }
      destruct eE as [eE hE].
      pose (trefl2 := sTransport (sEq tA2 ttu2 ttu2)
                                 (sEq tA1 tu1 tu1)
                                 eE (sRefl tA2 ttu2)
           ).
      exists (sEq tA1 tu1 tu1), (sEq tA1 tu1 tu1).
      exists (sRefl tA1 tu1), trefl2.
      exists (sHeqTrans (sCongRefl qA q) (sHeqTransport eE (sRefl tA2 ttu2))).
      destruct htu1 as [[[? ?] ?] ?].
      destruct htu2 as [[[? ?] ?] ?].
      destruct htA1 as [[[? ?] ?] ?].
      destruct htA2 as [[[? ?] ?] ?].
      repeat split.
      all: try assumption.
      all: try (econstructor ; eassumption).
      * econstructor. econstructor.
        -- assumption.
        -- econstructor. assumption.
      * eapply type_HeqTrans'.
        -- eapply type_CongRefl' ; eassumption.
        -- eapply type_HeqTransport'.
           ++ eapply type_Refl'.
              eapply type_Transport' ; eassumption.
           ++ eassumption.

    (* reflection *)
    + destruct (H _ hΓ) as [T' [e'' he'']].
      assert (th : type_head (head (sEq A u v))) by constructor.
      destruct (choose_type th he'') as [T'' [[e' he'] hh]].
      destruct T'' ; try (now inversion hh).
      rename T''1 into A', T''2 into u', T''3 into v'.
      clear hh he'' e'' he'' T' th.
      destruct he' as [[[? ieq] ?] he'].
      destruct (istype_type he') as [? heq].
      destruct (inversionEq heq) as [s [[[? ?] ?] ?]].
      exists A', A', u', v'.
      exists (sEqToHeq e').
      inversion ieq. subst.
      repeat split ; try eassumption.
      eapply type_EqToHeq'. assumption.

Defined.

End Translation.