From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import Ast SAst LiftSubst SLiftSubst SCommon Typing
                             XTyping ITyping.

Section Translation.

Open Scope type_scope.
Open Scope x_scope.
Open Scope i_scope.

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

Definition transport_heq (A B p t : sterm) : sterm.
Admitted.

Lemma type_transport_heq :
  forall {Σ Γ s A B p t},
    Σ ;;; Γ |-i t : A ->
    Σ ;;; Γ |-i p : sEq (sSort s) A B ->
    Σ ;;; Γ |-i transport_heq A B p t : sHeq A t B (sTransport A B p t).
Admitted.

Definition heq_Prod (s1 s2 z1 z2 : sort) (n1 n2 : name) (A1 A2 B1 B2 p q : sterm) : sterm.
Admitted.

Lemma type_heq_Prod :
  forall {Σ Γ s1 s2 z1 z2 n1 n2 nx ny ne A1 A2 B1 B2 p q},
    Σ ;;; Γ |-i p : sHeq (sSort s1) A1 (sSort z1) A2 ->
    Σ ;;; Γ ,, svass nx A1 ,, svass ny (lift0 1 A2) ,, svass ne (sHeq (lift0 2 A1) (sRel 1) (lift0 2 A2) (sRel 0)) |-i
    q : sHeq (sSort s2) (lift0 2 B1) (sSort z2) (lift0 1 (lift 1 1 B1)) ->
    Σ ;;; Γ |-i heq_Prod s1 s2 z1 z2 n1 n2 A1 A2 B1 B2 p q :
    sHeq (sSort (max_sort s1 s2)) (sProd n1 A1 B1)
         (sSort (max_sort z1 z2)) (sProd n2 A2 B2).
Admitted.

Definition heq_Eq (s1 s2 : sort) (A1 A2 u1 u2 v1 v2 pA pu pv : sterm) : sterm.
Admitted.

Lemma type_heq_Eq :
  forall {Σ Γ s1 s2 A1 A2 u1 u2 v1 v2 pA pu pv},
    Σ ;;; Γ |-i pA : sHeq (sSort s1) A1 (sSort s2) A2 ->
    Σ ;;; Γ |-i pu : sHeq A1 u1 A2 u2 ->
    Σ ;;; Γ |-i pv : sHeq A1 v1 A2 v2 ->
    Σ ;;; Γ |-i heq_Eq s1 s2 A1 A2 u1 u2 v1 v2 pA pu pv
             : sHeq (sSort s1) (sEq A1 u1 v1)
                    (sSort s2) (sEq A2 u2 v2).
Admitted.

Definition sCongRefl (s1 s2 : sort) (A1 A2 u1 u2 pA pu : sterm) : sterm.
Admitted.

Lemma type_CongRefl :
  forall {Σ Γ s1 s2 A1 A2 u1 u2 pA pu},
    Σ ;;; Γ |-i pA : sHeq (sSort s1) A1 (sSort s2) A2 ->
    Σ ;;; Γ |-i pu : sHeq A1 u1 A2 u2 ->
    Σ ;;; Γ |-i sCongRefl s1 s2 A1 A2 u1 u2 pA pu :
               sHeq (sEq A1 u1 u1) (sRefl A1 u1) (sEq A2 u2 u2) (sRefl A2 u2).
Admitted.

(* In order to do things properly we need to extend the context heterogenously,
   this is done by extending the context with triples
   (x : A, y : B, e : heq A x B y).
   We also need to define correspond lifts.

   If Γ, Γ1, Δ |- t : T then
   mix Γ Γ1 Γ2, Δ |- llift #|Γ1| #|Δ| t : llift #|Γ1| #|Δ| T
   If Γ, Γ2, Δ |- t : T then
   mix Γ Γ1 Γ2, Δ |- rlift #|Γ1| #|Δ| t : rlift #|Γ1| #|Δ| T
 *)

Fixpoint llift γ δ t : sterm :=
  match t with
  | sRel i =>
    if i <? δ
    then sRel i
    else if i <? δ + γ
         then sRel (3 * (i - δ) + δ + 2)
         else sRel (i + 3*γ + δ)
  | sLambda na A B b =>
    sLambda na (llift γ δ A) (llift γ (S δ) B) (llift γ (S δ) b)
  | sApp u na A B v =>
    sApp (llift γ δ u) na (llift γ δ A) (llift γ (S δ) B) (llift γ δ v)
  | sProd na A B => sProd na (llift γ δ A) (llift γ (S δ) B)
  | sEq A u v => sEq (llift γ δ A) (llift γ δ u) (llift γ δ v)
  | sRefl A u => sRefl (llift γ δ A) (llift γ δ u)
  | sJ A u P w v p =>
    sJ (llift γ δ A)
       (llift γ δ u)
       (lift γ (S (S δ)) P)
       (llift γ δ w)
       (llift γ δ v)
       (llift γ δ p)
  | sTransport A B p t =>
    sTransport (llift γ δ A) (llift γ δ B) (llift γ δ p) (llift γ δ t)
  | sUip A u v p q =>
    sUip (llift γ δ A) (llift γ δ u) (llift γ δ v) (llift γ δ p) (llift γ δ q)
  | sFunext A B f g e =>
    sFunext (llift γ δ A) (llift γ (S δ) B)
            (llift γ δ f) (llift γ δ g) (llift γ δ e)
  | sHeq A a B b =>
    sHeq (llift γ δ A) (llift γ δ a) (llift γ δ B) (llift γ δ b)
  | sHeqToEq A u v p =>
    sHeqToEq (llift γ δ A) (llift γ δ u) (llift γ δ v) (llift γ δ p)
  | sHeqRefl A a => sHeqRefl (llift γ δ A) (llift γ δ a)
  | sHeqSym A a B b p =>
    sHeqSym (llift γ δ A) (llift γ δ a)
            (llift γ δ B) (llift γ δ b) (llift γ δ p)
  | sHeqTrans A a B b C c p q =>
    sHeqTrans (llift γ δ A) (llift γ δ a)
              (llift γ δ B) (llift γ δ b)
              (llift γ δ C) (llift γ δ c)
              (llift γ δ p) (llift γ δ q)
  | x => x
  end.

Notation llift0 γ t := (llift γ 0 t).

Fixpoint rlift γ δ t : sterm :=
  match t with
  | sRel i =>
    if i <? δ
    then sRel i
    else if i <? δ + γ
         then sRel (3 * (i - δ) + δ + 1)
         else sRel (i + 3*γ + δ)
  | sLambda na A B b =>
    sLambda na (rlift γ δ A) (rlift γ (S δ) B) (rlift γ (S δ) b)
  | sApp u na A B v =>
    sApp (rlift γ δ u) na (rlift γ δ A) (rlift γ (S δ) B) (rlift γ δ v)
  | sProd na A B => sProd na (rlift γ δ A) (rlift γ (S δ) B)
  | sEq A u v => sEq (rlift γ δ A) (rlift γ δ u) (rlift γ δ v)
  | sRefl A u => sRefl (rlift γ δ A) (rlift γ δ u)
  | sJ A u P w v p =>
    sJ (rlift γ δ A)
       (rlift γ δ u)
       (lift γ (S (S δ)) P)
       (rlift γ δ w)
       (rlift γ δ v)
       (rlift γ δ p)
  | sTransport A B p t =>
    sTransport (rlift γ δ A) (rlift γ δ B) (rlift γ δ p) (rlift γ δ t)
  | sUip A u v p q =>
    sUip (rlift γ δ A) (rlift γ δ u) (rlift γ δ v) (rlift γ δ p) (rlift γ δ q)
  | sFunext A B f g e =>
    sFunext (rlift γ δ A) (rlift γ (S δ) B)
            (rlift γ δ f) (rlift γ δ g) (rlift γ δ e)
  | sHeq A a B b =>
    sHeq (rlift γ δ A) (rlift γ δ a) (rlift γ δ B) (rlift γ δ b)
  | sHeqToEq A u v p =>
    sHeqToEq (rlift γ δ A) (rlift γ δ u) (rlift γ δ v) (rlift γ δ p)
  | sHeqRefl A a => sHeqRefl (rlift γ δ A) (rlift γ δ a)
  | sHeqSym A a B b p =>
    sHeqSym (rlift γ δ A) (rlift γ δ a)
            (rlift γ δ B) (rlift γ δ b) (rlift γ δ p)
  | sHeqTrans A a B b C c p q =>
    sHeqTrans (rlift γ δ A) (rlift γ δ a)
              (rlift γ δ B) (rlift γ δ b)
              (rlift γ δ C) (rlift γ δ c)
              (rlift γ δ p) (rlift γ δ q)
  | x => x
  end.

Notation rlift0 γ t := (rlift γ 0 t).

(* Fixpoint mix (Γ Γ1 Γ2 : scontext) : scontext := *)
(*   match Γ1, Γ2, Γs with *)
(*   | (Γ1 ,, svass nx A), (Γ2 ,, svass ny B), s :: Γs => (mix Γ Γ1 Γ2) ,, svass *)

Lemma trelE_to_heq :
  forall {Σ t1 t2},
    t1 ∼ t2 ->
    forall {Γ T1 T2},
      Σ ;;; Γ |-i t1 : T1 ->
      Σ ;;; Γ |-i t2 : T2 ->
      ∑ p, Σ ;;; Γ |-i p : sHeq T1 t1 T2 t2.
Proof.
  intros Σ t1 t2. induction 1 ; intros Γ A B h1 h2.
  - destruct (uniqueness h1 h2) as [s eq].
    destruct (eq_typing eq) as [hA hB].
    assert (hs : Σ ;;; Γ |-i sSort s : sSort (succ_sort s)).
    { apply type_Sort. apply (typing_wf h1). }
    exists (sHeqRefl A (sRel x)).
    eapply type_conv.
    + eapply type_HeqRefl ; eassumption.
    + apply type_Heq ; eassumption.
    + apply cong_Heq ; try (apply eq_reflexivity ; assumption).
      assumption.
  - destruct (inversionTransport h1) as [s [[[[? ht1] hT1] ?] ?]].
(*    destruct (IHtrel _ _ _ ht1 h2) as [s1 [q hq]].
    destruct (istype_type hq) as [s2 hheq].
    destruct (inversionHeq hheq) as [[[[hT1' ?] ?] ?] ?].
    destruct (uniqueness hT1 hT1') as [s3 hss1].
    assert (hss : Σ ;;; Γ |-i sSort s : sSort (succ_sort s)).
    { apply type_Sort. apply (typing_wf h1). }
    destruct (eq_typing hss1) as [hss3 hs1s3].
    destruct (uniqueness hss3 hss).
    assert (hB : Σ ;;; Γ |-i B : sSort s).
    { eapply type_conv.
      - eassumption.
      - exact hss.
      - apply eq_symmetry. eapply eq_conv ; eassumption.
    }
    assert (hA : Σ ;;; Γ |-i A : sSort s).
    { apply (eq_typing e). }
    exists s.
    exists (sHeqTrans s T2 (sTransport T1 T2 p t1) T1 t1 B t2
                 (sHeqSym s T1 t1 T2 (sTransport T1 T2 p t1) (transport_heq s T1 T2 p t1))
                 q).
    eapply type_conv.
    + eapply type_HeqTrans'.
      * apply type_HeqSym'. apply type_transport_heq ; assumption.
      * eapply type_conv.
        -- eassumption.
        -- apply type_heq ; assumption.
        -- apply cong_heq ; try (apply eq_reflexivity ; assumption).
           apply eq_symmetry. eapply eq_conv ; eassumption.
    + apply type_heq ; try assumption.
    + apply cong_heq ; try (apply eq_reflexivity) ; try assumption.
      apply type_Transport with (s := s) ; assumption.
  - destruct (inversionTransport h2) as [s [[[[? ht2] hT1] ?] ?]].
    destruct (IHtrel _ _ _ h1 ht2) as [s1 [q hq]].
    destruct (istype_type hq) as [s2 hheq].
    destruct (inversionHeq hheq) as [[[[? hT1'] ?] ?] ?].
    destruct (uniqueness hT1 hT1') as [s3 hss1].
    assert (hss : Σ ;;; Γ |-i sSort s : sSort (succ_sort s)).
    { apply type_Sort. apply (typing_wf h1). }
    destruct (eq_typing hss1) as [hss3 hs1s3].
    destruct (uniqueness hss3 hss).
    assert (hB : Σ ;;; Γ |-i B : sSort s).
    { apply (eq_typing e). }
    assert (hA : Σ ;;; Γ |-i A : sSort s).
    { eapply type_conv.
      - eassumption.
      - exact hss.
      - apply eq_symmetry. eapply eq_conv ; eassumption.
    }
    exists s.
    exists (sHeqTrans s A t1 T1 t2 T2 (sTransport T1 T2 p t2)
                 q
                 (transport_heq s T1 T2 p t2)
      ).
    eapply type_conv.
    + eapply type_HeqTrans'.
      * eapply type_conv.
        -- eassumption.
        -- apply type_heq ; assumption.
        -- apply cong_heq ; try (apply eq_reflexivity ; assumption).
           apply eq_symmetry. eapply eq_conv ; eassumption.
      * apply type_transport_heq ; assumption.
    + apply type_heq ; try assumption.
    + apply cong_heq ; try (apply eq_reflexivity) ; try assumption.
      apply type_Transport with (s := s) ; assumption.
  - destruct (inversionProd h1) as [s1 [z1 [[hA1 hB1] ?]]].
    destruct (inversionProd h2) as [s2 [z2 [[hA2 hB2] ?]]].
    destruct (IHtrel1 _ _ _ hA1 hA2) as [s [p hp]].
    (* Here comes the trick to have a common context. *)
    pose (Δ := Γ ,, svass n1 A1 ,, svass n2 (lift0 1 A2) ,, svass nAnon (heq s1 (lift0 2 A1) (sRel 1) (lift0 2 A2) (sRel 0))).
    assert (hB1' : Σ ;;; Δ |-i lift0 2 B1 : lift0 2 (sSort z1)).
    { eapply typing_lift02.
      - assumption.
      - instantiate (1 := s2). change (sSort s2) with (lift0 1 (sSort s2)).
        eapply typing_lift01 ; eassumption.
      - apply type_heq.
        + change (sSort s1) with (lift0 2 (sSort s1)).
          eapply typing_lift02.
          * assumption.
          * eassumption.
          * instantiate (1 := s2). change (sSort s2) with (lift0 1 (sSort s2)).
            eapply typing_lift01 ; eassumption.
        + eapply type_conv.
          * instantiate (1 := sSort s2). change (sSort s2) with (lift0 2 (sSort s2)).
            eapply typing_lift02.
            -- assumption.
            -- eassumption.
            -- instantiate (1 := s2). change (sSort s2) with (lift0 1 (sSort s2)).
               eapply typing_lift01 ; eassumption.
          * apply type_Sort. econstructor.
            -- econstructor.
               ++ apply (typing_wf hA1).
               ++ eexists ; eassumption.
            -- exists s2. change (sSort s2) with (lift0 1 (sSort s2)).
               eapply typing_lift01 ; eassumption.
          * apply sorts_in_sort.
            -- destruct (istype_type hp) as [? hheq].
               destruct (inversionHeq hheq) as [[[[hs1 ?] ?] ?] ?].
               pose proof (inversionSort hs1).
               eapply type_conv.
               ++ change (sSort s2) with (lift0 2 (sSort s2)).
                  eapply typing_lift02.
                  ** eassumption.
                  ** eassumption.
                  ** instantiate (1 := s2).
                     change (sSort s2) with (lift0 1 (sSort s2)).
                     eapply typing_lift01 ; eassumption.
               ++ apply type_Sort. econstructor.
                  ** apply (typing_wf hB1).
                  ** exists s2. change (sSort s2) with (lift0 1 (sSort s2)).
                     eapply typing_lift01 ; eassumption.
               ++ cbn. apply eq_symmetry. apply inversionSort.
                  change (sSort s1) with (lift0 2 (sSort s1)).
                  change (sSort s) with (lift0 2 (sSort s)).
                  eapply typing_lift02.
                  ** assumption.
                  ** eassumption.
                  ** instantiate (1 := s2).
                     change (sSort s2) with (lift0 1 (sSort s2)).
                     eapply typing_lift01 ; eassumption.
            -- apply type_Sort. econstructor.
               ++ apply (typing_wf hB1).
               ++ exists s2. change (sSort s2) with (lift0 1 (sSort s2)).
                  eapply typing_lift01 ; eassumption.
        + simple refine (type_Rel _ _ _ _ _).
          * econstructor.
            -- apply (typing_wf hB1).
            -- exists s2. change (sSort s2) with (lift0 1 (sSort s2)).
               eapply typing_lift01 ; eassumption.
          * cbn. omega.
        + assert (eq : forall t, lift0 2 t = lift0 1 (lift0 1 t)).
          { intro u. rewrite lift_lift. reflexivity. }
          rewrite eq.
          simple refine (type_Rel _ _ _ _ _).
          * econstructor.
            -- apply (typing_wf hB1).
            -- exists s2. change (sSort s2) with (lift0 1 (sSort s2)).
               eapply typing_lift01 ; eassumption.
          * cbn. omega.
    }
    (* After this tedious proof, we remark that we cannot use the induction
       hypothesis on B1 as we have lift0 2 B1 instead.
       This could be solved by changing the corresponding trel case.
     *)
    admit.
  - destruct (inversionEq h1) as [s1 [[[hA1 hu1] hv1] eqA]].
    destruct (inversionEq h2) as [s2 [[[hA2 hu2] hv2] eqB]].
    destruct (IHtrel1 _ _ _ hA1 hA2) as [sA [pA hpA]].
    destruct (IHtrel2 _ _ _ hu1 hu2) as [su [pu hpu]].
    destruct (IHtrel3 _ _ _ hv1 hv2) as [sv [pv hpv]].
    exists (succ_sort s1).
    exists (heq_Eq s1 s2 A1 A2 u1 u2 v1 v2 pA pu pv).
    assert (s1s1 : Σ;;; Γ |-i sSort s1 : sSort (succ_sort s1)).
    { apply type_Sort. apply (typing_wf hA1). }
    destruct (istype_type hpA) as [? heqA].
    destruct (istype_type hpu) as [? hequ].
    destruct (istype_type hpv) as [? heqv].
    destruct (inversionHeq heqA) as [[[[? ?] ?] ?] ?].
    destruct (inversionHeq hequ) as [[[[A1su A2su] ?] ?] ?].
    destruct (inversionHeq heqv) as [[[[A1sv A2sv] ?] ?] ?].
    destruct (uniqueness hA1 A1su) as [? eq].
    destruct (uniqueness hA2 A2su) as [? eq'].
    destruct (eq_typing eq') as [? su1].
    destruct (eq_typing eq) as [? su2].
    destruct (uniqueness su1 su2) as [? hh].
    assert (s1s2 : Σ;;; Γ |-i sSort s1 = sSort s2 : sSort (succ_sort s1)).
    { eapply eq_conv.
      - eapply eq_transitivity.
        + eassumption.
        + eapply eq_symmetry. eapply eq_conv.
          * eassumption.
          * eassumption.
      - apply eq_symmetry. apply inversionSort. assumption.
    }
    assert (s2s1 : Σ;;; Γ |-i sSort s2 : sSort (succ_sort s1)).
    { apply (eq_typing s1s2). }
    assert (Σ;;; Γ |-i sSort sA = sSort (succ_sort s1) : sSort (succ_sort (succ_sort s1))).
    { apply eq_symmetry. apply inversionSort. assumption. }
    assert (Σ;;; Γ |-i A2 : sSort s1).
    { eapply type_conv ; [ exact hA2 | idtac | eapply eq_symmetry ; eassumption ].
      eassumption.
    }
    assert (Σ;;; Γ |-i sSort su = sSort s1 : sSort (succ_sort s1)).
    { apply eq_symmetry. eapply eq_conv.
      - eassumption.
      - apply eq_symmetry. apply inversionSort. assumption.
    }
    destruct (uniqueness hA1 A1sv) as [? eq2].
    destruct (uniqueness hA2 A2sv) as [? eq3].
    destruct (eq_typing eq3) as [? sv1].
    destruct (eq_typing eq2) as [? sv2].
    destruct (uniqueness sv1 sv2) as [? hhh].
    assert (Σ;;; Γ |-i sSort sv = sSort s1 : sSort (succ_sort s1)).
    { apply eq_symmetry. eapply eq_conv.
      - eassumption.
      - apply eq_symmetry. apply inversionSort. assumption.
    }
    assert (Σ;;; Γ |-i A : sSort (succ_sort s1)).
    { apply (eq_typing eqA). }
    assert (Σ;;; Γ |-i B : sSort (succ_sort s2)).
    { apply (eq_typing eqB). }
    assert (s2s2 : Σ;;; Γ |-i sSort s2 : sSort (succ_sort s2)).
    { apply type_Sort. apply (typing_wf hA1). }
    destruct (uniqueness s2s2 s2s1) as [? eq4].
    assert (Σ;;; Γ |-i B : sSort (succ_sort s1)).
    { eapply type_conv.
      - eassumption.
      - apply (eq_typing eq4).
      - assumption.
    }
    eapply type_conv.
    + apply type_heq_Eq.
      * eapply type_conv.
        -- exact hpA.
        -- apply type_heq ; assumption.
        -- apply cong_heq.
           all: try (apply eq_reflexivity).
           all: easy.
      * eapply type_conv.
        -- exact hpu.
        -- apply type_heq ; assumption.
        -- apply cong_heq.
           all: try (apply eq_reflexivity).
           all: easy.
      * eapply type_conv.
        -- exact hpv.
        -- apply type_heq ; assumption.
        -- apply cong_heq.
           all: try (apply eq_reflexivity).
           all: easy.
    + apply type_heq ; assumption.
    + apply cong_heq.
      all: try (apply eq_reflexivity).
      all: try assumption.
      * apply type_Sort. apply (typing_wf hA1).
      * eapply eq_conv.
        -- eassumption.
        -- eassumption.
      * eapply type_conv ; [ eassumption | idtac | eapply eq_symmetry ; eassumption ].
        assumption.
      * eapply type_conv ; [ eassumption | idtac | eapply eq_symmetry ; eassumption ].
        assumption.
  - destruct (uniqueness h1 h2) as [s' eq].
    exists (succ_sort (succ_sort s)), (sHeqRefl (succ_sort (succ_sort s)) A (sSort s)).
    pose proof (inversionSort h1) as eqA.
    destruct (eq_typing eqA) as [hss hAs].
    pose proof (inversionSort h2) as eqB.
    destruct (eq_typing eqB) as [_ hBs].
    destruct (eq_typing eq) as [_ Bs'].
    destruct (uniqueness Bs' hBs).
    eapply type_conv.
    + apply type_HeqRefl ; assumption.
    + apply type_heq ; assumption.
    + apply cong_heq.
      all: try (apply eq_reflexivity).
      all: try assumption.
      * apply type_Sort. apply (typing_wf hAs).
      * eapply eq_conv ; eassumption.
  - admit.
  - admit.
  - destruct (inversionRefl h1) as [s1 [[hA1 hu1] eqA]].
    destruct (inversionRefl h2) as [s2 [[hA2 hu2] eqB]].
    destruct (IHtrel1 _ _ _ hA1 hA2) as [sA [pA hpA]].
    destruct (IHtrel2 _ _ _ hu1 hu2) as [su [pu hpu]].
    exists s1, (sHeqRefl s1 s2 A1 A2 u1 u2 pA pu).
    assert (Σ;;; Γ |-i sSort s1 : sSort (succ_sort s1)).
    { apply type_Sort. apply (typing_wf hA1). }
    destruct (istype_type hpA) as [? heqA].
    destruct (inversionHeq heqA) as [? ?].
    assert (Σ;;; Γ |-i sSort s2 : sSort (succ_sort s1)).
    { admit. }
    eapply type_conv.
    + apply type_HeqRefl.
      * eapply type_conv.
        -- eassumption.
        -- apply type_heq. all: try assumption.
        -- admit.
      * admit.
    + admit.
    + admit.
      Unshelve. admit.*)
Admitted.

Corollary trel_to_heq :
  forall {Σ Γ T1 T2} {t1 t2 : sterm},
    t1 ∼ t2 ->
    Σ ;;; Γ |-i t1 : T1 ->
    Σ ;;; Γ |-i t2 : T2 ->
    ∑ p, Σ ;;; Γ |-i p : sHeq T1 t1 T2 t2.
Proof.
  intros Σ Γ T1 T2 t1 t2 h h1 h2.
  now apply trelE_to_heq.
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
  - constructor. eapply IHh. reflexivity.
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
      constructor ; eapply IHh ; [ .. | reflexivity ] ; assumption
    | now constructor
    ]
  ).
  - assumption.
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
| headUip
| headFunext
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
  | sUip A u v p q => headUip
  | sFunext A B f g e => headFunext
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
  induction h ; try (eexists ; exists nil ; split ; [ split ; [ idtac | reflexivity ] | idtac ] ; [ reflexivity | now constructor ]).
  destruct IHh as [A'' [tseq [[hh he] hsub]]].
  exists A'', (trd T1 T2 p :: tseq). split ; [ split | ].
  - assumption.
  - cbn. now f_equal.
  - assumption.
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
      * eapply eq_typing, (inversionSort ht).
    + destruct (inversionProd ht) as [s1 [s2 [[? ?] ?]]].
      exists (max_sort s1 s2). repeat split.
      * now apply type_Prod.
      * now eapply eq_typing.
    + destruct (inversionEq ht) as [s [[[? ?] ?] ?]].
      exists s. repeat split.
      * now apply type_Eq.
      * now eapply eq_typing.

  - destruct a. cbn in ht.
    change (fold_right transport_data_app A' tseq)
      with (transport_seq_app tseq A') in ht.
    destruct (inversionTransport ht) as [s [[[[? hA'] hT1] ?] ?]].
    destruct (IHtseq Γ' A' T1 hh hA') as [s' [hAs hT1s]].
    exists s'. repeat split.
    + assumption.
    + destruct (eq_typing e) as [_ hT].
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

Axiom cheating : forall {A}, A.
Tactic Notation "cheat" := (apply cheating).

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
  - constructor.
    + now destruct hΓ.
    + exists s'. now destruct hA as [[[? ?] ?] ?].
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

Fixpoint context_translation {Σ Γ} (h : XTyping.wf Σ Γ) :
  ∑ Γ', Σ |--i Γ' # ⟦ Γ ⟧

with type_translation {Σ Γ A t} (h : Σ ;;; Γ |-x t : A)
                          {Γ'} (hΓ : Σ |--i Γ' # ⟦ Γ ⟧) {struct h} :
  ∑ A' t', Σ ;;;; Γ' |--- [t'] : A' # ⟦ Γ |--- [t] : A ⟧

with eq_translation {Σ Γ A u v} (h : Σ ;;; Γ |-x u = v : A)
                    {Γ'} (hΓ : Σ |--i Γ' # ⟦ Γ ⟧) {struct h} :
  ∑ A' A'' u' v' p',
    eqtrans Σ Γ A u v Γ' A' A'' u' v' p'
.
Proof.
  (** context_translation **)
  - dependent destruction h.

    (* wf_nil *)
    + exists nil. split ; constructor.

    (* wf_snoc *)
    + destruct (context_translation _ _ h) as [Γ' hΓ'].
      destruct s as [s hA].
      destruct (type_translation _ _ _ _ hA _ hΓ') as [T [A' hA']].
      assert (th : type_head (head (sSort s))) by constructor.
      destruct (choose_type th hA') as [T' [[A'' hA''] hh]].
      destruct T' ; try (now inversion hh).
      exists (Γ' ,, svass x A''). now eapply trans_snoc.

  (** type_translation **)
  - dependent destruction h.

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
      destruct (type_translation _ _ _ _ h1 _ hΓ) as [S' [t' ht']].
      assert (th : type_head (head (sSort s1))) by constructor.
      destruct (choose_type th ht') as [T' [[t'' ht''] hh]].
      clear ht' t' S'.
      destruct T' ; inversion hh.
      subst. clear hh th.
      (* Translation of the codomain *)
      destruct (type_translation _ _ _ _ h2 _ (trans_snoc hΓ ht''))
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
      destruct (type_translation _ _ _ _ h1 _ hΓ) as [S' [t' ht']].
      assert (th : type_head (head (sSort s1))) by constructor.
      destruct (choose_type th ht') as [T' [[t'' ht''] hh]].
      clear ht' t' S'.
      destruct T' ; inversion hh.
      subst. clear hh th.
      (* Translation of the codomain *)
      destruct (type_translation _ _ _ _ h2 _ (trans_snoc hΓ ht''))
        as [S' [bty' hbty']].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type th hbty') as [T' [[bty'' hbty''] hh]].
      clear hbty' bty' S'.
      destruct T' ; inversion hh. subst. clear hh th.
      (* Translation of the term *)
      destruct (type_translation _ _ _ _ h3 _ (trans_snoc hΓ ht''))
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
      destruct (type_translation _ _ _ _ h1 _ hΓ) as [S' [A'' hA'']].
      assert (th : type_head (head (sSort s1))) by constructor.
      destruct (choose_type th hA'') as [T' [[A' hA'] hh]].
      clear hA'' A'' S'.
      destruct T' ; inversion hh.
      subst. clear hh th.
      (* Translation of the codomain *)
      destruct (type_translation _ _ _ _ h2 _ (trans_snoc hΓ hA'))
        as [S' [B'' hB'']].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type th hB'') as [T' [[B' hB'] hh]].
      clear hB'' B'' S'.
      destruct T' ; inversion hh. subst. clear hh th.
      (* Translation of the function *)
      destruct (type_translation _ _ _ _ h3 _ hΓ) as [T'' [t'' ht'']].
      assert (th : type_head (head (sProd n A B))) by constructor.
      destruct (choose_type th ht'') as [T' [[t' ht'] hh]].
      clear ht'' t'' T''.
      destruct T' ; inversion hh. subst. clear hh th.
      rename T'1 into A'', T'2 into B''.
      destruct (change_type ht' (trans_Prod hΓ hA' hB')) as [t'' ht''].
      clear ht' A'' B'' t'.
      (* Translation of the argument *)
      destruct (type_translation _ _ _ _ h4 _ hΓ) as [A'' [u'' hu'']].
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
      destruct (type_translation _ _ _ _ h1 _ hΓ) as [S [A'' hA'']].
      assert (th : type_head (head (sSort s))) by constructor.
      destruct (choose_type th hA'') as [T [[A' hA'] hh]].
      clear hA'' A'' S.
      destruct T ; inversion hh. subst. clear hh th.
      (* The first term *)
      destruct (type_translation _ _ _ _ h2 _ hΓ) as [A'' [u'' hu'']].
      destruct (change_type hu'' hA') as [u' hu'].
      clear hu'' u'' A''.
      (* The other term *)
      destruct (type_translation _ _ _ _ h3 _ hΓ) as [A'' [v'' hv'']].
      destruct (change_type hv'' hA') as [v' hv'].
      (* Now we conclude *)
      exists (sSort s), (sEq A' u' v').
      apply trans_Eq ; assumption.

    (* type_Refl *)
    + destruct (type_translation _ _ _ _ h2 _ hΓ) as [A' [u' hu']].
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
      destruct (eq_translation _ _ _ _ _ e _ hΓ)
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
      destruct (type_translation _ _ _ _ h1 _ hΓ) as [A''' [t'' ht'']].
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
      { exists (sHeqTrans (sSort s) A' S' A'' (sSort s) B'
                     pA (sHeqTrans S' A'' S'' B'' (sSort s) B' p' pB)).
        apply type_HeqTrans'.
        - assumption.
        - apply type_HeqTrans'.
          + assumption.
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
  - dependent destruction h.

    (* eq_reflexivity *)
    + destruct (type_translation _ _ _ _ t _ hΓ) as [A' [u' hu']].
      destruct hu' as [[[? ?] ?] hu'].
      destruct (istype_type hu') as [s' hA'].
      exists A', A', u', u', (sHeqRefl A' u').
      repeat split ; try assumption.
      eapply type_HeqRefl ; eassumption.

    (* eq_symmetry *)
    + destruct (eq_translation _ _ _ _ _ h _ hΓ)
        as [A' [A'' [u' [v' [p' h']]]]].
      destruct h' as [[[[[? ?] ?] ?] ?] hp'].
      exists A'', A', v', u', (sHeqSym A' u' A'' v' p').
      repeat split ; try assumption.
      eapply type_HeqSym'. eassumption.

    (* eq_transitivity *)
    + destruct (eq_translation _ _ _ _ _ h1 _ hΓ)
        as [A1 [A2 [u1 [v1 [p1 h1']]]]].
      destruct (eq_translation _ _ _ _ _ h2 _ hΓ)
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
      exists (sHeqTrans A1 u1 A2 v1 A4 w1
                   p1
                   (sHeqTrans A2 v1  A3 v2 A4 w1
                              p3
                              p2)
        ).
      repeat split ; try assumption.
      apply type_HeqTrans'.
      * assumption.
      * apply type_HeqTrans' ; assumption.

    (* eq_beta *)
    + (* Translation of the domain *)
      destruct (type_translation _ _ _ _ t0 _ hΓ) as [S [A'' hA'']].
      assert (th : type_head (head (sSort s1))) by constructor.
      destruct (choose_type th hA'') as [T' [[A' hA'] hh]].
      clear hA'' A'' S.
      destruct T' ; inversion hh. subst. clear hh th.
      (* Translation of the codomain *)
      destruct (type_translation _ _ _ _ t1 _ (trans_snoc hΓ hA'))
        as [S' [B'' hB'']].
      assert (th : type_head (head (sSort s2))) by constructor.
      destruct (choose_type th hB'') as [T' [[B' hB'] hh]].
      clear hB'' B'' S'.
      destruct T' ; inversion hh. subst. clear hh th.
      (* Translation of the in-term *)
      destruct (type_translation _ _ _ _ t2 _ (trans_snoc hΓ hA'))
        as [T' [t'' ht'']].
      destruct (change_type ht'' hB') as [t' ht'].
      clear ht'' T' t''.
      (* Translation of the argument *)
      destruct (type_translation _ _ _ _ t3 _ hΓ) as [A'' [u'' hu'']].
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
    + cheat.

    (* cong_Prod *)
    + cheat.

    (* cong_Lambda *)
    + cheat.

    (* cong_App *)
    + cheat.

    (* cong_Eq *)
    + destruct (eq_translation _ _ _ _ _ h1 _ hΓ)
        as [T1 [T2 [A1' [A2' [pA h1']]]]].
      destruct (eq_translation _ _ _ _ _ h2 _ hΓ)
        as [A1'' [A1''' [u1' [u2' [pu h2']]]]].
      destruct (eq_translation _ _ _ _ _ h3 _ hΓ)
        as [A1'''' [A1''''' [v1' [v2' [pv h3']]]]].
      destruct (eqtrans_trans h1') as [hA1' hA2'].
      destruct (eqtrans_trans h2') as [hu1' hu2'].
      destruct (eqtrans_trans h3') as [hv1' hv2'].
      destruct h1' as [[[[[? ?] ?] ?] ?] hpA].
      destruct h2' as [[[[[? ?] ?] ?] ?] hpu].
      destruct h3' as [[[[[? ?] ?] ?] ?] hpv].
      (* We need to chain translations a lot to use heq_Eq *)
      assert (th : type_head (head (sSort s))) by constructor.
      destruct (choose_type th hA1') as [T' [[tA1 htA1] hh]].
      destruct T' ; inversion hh. subst.
      clear th hh.
      assert (th : type_head (head (sSort s))) by constructor.
      destruct (choose_type th hA2') as [T' [[tA2 htA2] hh]].
      destruct T' ; inversion hh. subst.
      clear th hh.
      (* For the types we build the missing hequalities *)
      (*assert (hp : ∑ p, Σ ;;; Γ' |-i p : heq (succ_sort s) (sSort s) tA1 (sSort s) tA2).
      { destruct hA1' as [_ hA1'].
        destruct htA1 as [[[? ?] ?] htA1].
        assert (sim1 : tA1 ∼ A1').
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq sim1 htA1 hA1') as [sA [p1 hp1]].
        destruct hA2' as [_ hA2'].
        destruct htA2 as [[[? ?] ?] htA2].
        assert (sim2 : A2' ∼ tA2).
        { eapply trel_trans.
          - eapply trel_sym. eapply inrel_trel. eassumption.
          - eapply inrel_trel. eassumption.
        }
        destruct (trel_to_heq sim2 hA2' htA2) as [sA' [p2 hp2]].
        exists (sHeqTrans (succ_sort s) (sSort s) tA1 T1 A1' (sSort s) tA2
                     p1
                     (sHeqTrans (succ_sort s) T1 A1' T2 A2' (sSort s) tA2
                                pA
                                p2
                     )
          ).
        assert (wf Σ Γ') by (apply (typing_wf hp1)).
        assert (Σ;;; Γ' |-i sSort s : sSort (succ_sort s)).
        { apply type_Sort. assumption. }
        destruct (istype_type hp1) as [? hheq1].
        destruct (inversionHeq hheq1) as [[[[ssA T1sA] ?] ?] ?].
        destruct (istype_type hp2) as [? hheq2].
        destruct (inversionHeq hheq2) as [[[[T2sA' ?] ?] ?] ?].
        destruct (istype_type hpA) as [? hheqA].
        destruct (inversionHeq hheqA) as [[[[T1s1 ?] ?] ?] ?].
        assert (T1ss : Σ;;; Γ' |-i T1 : sSort (succ_sort s)).
        { eapply type_conv.
          1: exact T1sA.
          2: apply eq_symmetry ; eapply inversionSort ; eassumption.
          apply type_Sort. assumption.
        }
        assert (Σ;;; Γ' |-i sSort sA = sSort (succ_sort s) : sSort (succ_sort (succ_sort s))).
        { apply eq_symmetry ; eapply inversionSort ; eassumption. }
        assert (Σ;;; Γ' |-i T2 : sSort (succ_sort s)).
        { eapply type_conv.
          1: exact T2sA'.
          2: apply eq_symmetry ; eapply inversionSort ; eassumption.
          apply type_Sort. assumption.
        }
        destruct (uniqueness T1s1 T1ss) as [? eq].
        assert (Σ;;; Γ' |-i sSort s1 = sSort (succ_sort s) : sSort (succ_sort (succ_sort s))).
        { eapply eq_conv.
          - eassumption.
          - apply eq_symmetry. eapply inversionSort. apply (eq_typing eq).
        }
        assert (Σ;;; Γ' |-i sSort sA' = sSort (succ_sort s) : sSort (succ_sort (succ_sort s))).
        { apply eq_symmetry. eapply inversionSort. assumption. }
        apply type_HeqTrans'.
        - eapply type_conv.
          + eassumption.
          + apply type_heq ; eassumption.
          + apply cong_heq.
            all: try (apply eq_reflexivity).
            all: easy.
        - apply type_HeqTrans'.
          + eapply type_conv.
            * eassumption.
            * apply type_heq ; eassumption.
            * apply cong_heq.
              all: try (apply eq_reflexivity).
              all: easy.
          + eapply type_conv.
            * eassumption.
            * apply type_heq ; eassumption.
            * apply cong_heq.
              all: try (apply eq_reflexivity).
              all: easy.
      }
      destruct hp as [qA hqA].
      (* Now we need to do the same for the terms *)
      destruct (change_type hu1' htA1) as [tu1 htu1].
      destruct (change_type hu2' htA1) as [tu2 htu2].
      (* destruct (change_type hv1' htA2) as [tv1 htv1]. *)
      (* destruct (change_type hv2' htA2) as [tv2 htv2]. *)*)
      cheat.

    (* cong_Refl *)
    + cheat.

    (* reflection *)
    + destruct (type_translation _ _ _ _ t _ hΓ) as [T' [e'' he'']].
      assert (th : type_head (head (sEq A u v))) by constructor.
      destruct (choose_type th he'') as [T'' [[e' he'] hh]].
      destruct T'' ; try (now inversion hh).
      rename T''1 into A', T''2 into u', T''3 into v'.
      clear hh he'' e'' he'' T' th.
      destruct he' as [[[? ieq] ?] he'].
      destruct (istype_type he') as [? heq].
      destruct (inversionEq heq) as [s [[[? ?] ?] ?]].
      exists A', A', u', v'.
      (*exists (sPair (sEq (sSort s) A' A')
               (sEq (lift0 1 A')
                    (sTransport (lift0 1 A') (lift0 1 A') (sRel 0) (lift0 1 u'))
                    (lift0 1 v'))
               (sRefl (sSort s) A')
               e'
        ).
      inversion ieq. subst.
      assert (hs : Σ;;; Γ' |-i sSort s : sSort (succ_sort s)).
      { apply type_Sort. apply (typing_wf he'). }
      repeat split ; try eassumption.
      eapply type_Pair.
      * apply type_Eq ; eassumption.
      * apply type_Eq.
        -- instantiate (1 := s).
           change (sSort s) with (lift0 1 (sSort s)).
           eapply typing_lift01.
           ++ assumption.
           ++ apply type_Eq ; eassumption.
        -- eapply type_Transport.
           ++ instantiate (1 := s).
              change (sSort s) with (lift0 1 (sSort s)).
              eapply typing_lift01.
              ** assumption.
              ** apply type_Eq ; eassumption.
           ++ change (sSort s) with (lift0 1 (sSort s)).
              eapply typing_lift01.
              ** assumption.
              ** apply type_Eq ; eassumption.
           ++ simple refine (type_Rel _ _ _ _ _).
              ** econstructor.
                 --- apply (typing_wf he').
                 --- eexists. apply type_Eq ; eassumption.
              ** cbn. omega.
           ++ eapply typing_lift01.
              ** assumption.
              ** apply type_Eq ; eassumption.
        -- eapply typing_lift01.
           ++ assumption.
           ++ apply type_Eq ; eassumption.
      * eapply type_Refl ; eassumption.
      * cbn. rewrite !lift_subst, lift00.
        eapply type_conv.
        -- eassumption.
        -- apply type_Eq ; try eassumption.
           eapply type_Transport ; try eassumption.
           eapply type_Refl ; eassumption.
        -- apply cong_Eq.
           all: try (apply eq_reflexivity).
           all: try assumption.
           apply eq_symmetry.
           apply eq_TransportRefl ; assumption.*)
      (* TODO We need to have eq => heq in the syntax now! *)
      cheat.
Defined.

End Translation.