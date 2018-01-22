From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import Ast SAst LiftSubst SLiftSubst SCommon Typing
                             XTyping ITyping.

Section Translation.

Open Scope type_scope.
Open Scope x_scope.
Open Scope i_scope.

(*! Relation for translated expressions *)
Inductive trel (E : list (nat * nat)) : sterm -> sterm -> Type :=
| trel_assumption x y :
    In (x,y) E ->
    trel E (sRel x) (sRel y)

| trel_Rel x :
    trel E (sRel x) (sRel x)

| trel_Transport_l t1 t2 T1 T2 p :
    trel E t1 t2 ->
    trel E (sTransport T1 T2 p t1) t2

| trel_Transport_r t1 t2 T1 T2 p :
    trel E t1 t2 ->
    trel E t1 (sTransport T1 T2 p t2)

| trel_Prod n1 n2 A1 A2 B1 B2 :
    trel E A1 A2 ->
    trel E B1 B2 ->
    trel E (sProd n1 A1 B1) (sProd n2 A2 B2)

| trel_Eq A1 A2 u1 u2 v1 v2 :
    trel E A1 A2 ->
    trel E u1 u2 ->
    trel E v1 v2 ->
    trel E (sEq A1 u1 v1) (sEq A2 u2 v2)

| trel_Sig n1 n2 A1 A2 B1 B2 :
    trel E A1 A2 ->
    trel E B1 B2 ->
    trel E (sSig n1 A1 B1) (sSig n2 A2 B2)

| trel_Sort s :
    trel E (sSort s) (sSort s)

| trel_Lambda n1 n2 A1 A2 B1 B2 u1 u2 :
    trel E A1 A2 ->
    trel E B1 B2 ->
    trel E u1 u2 ->
    trel E (sLambda n1 A1 B1 u1) (sLambda n2 A2 B2 u2)

| trel_App u1 u2 n1 n2 A1 A2 B1 B2 v1 v2 :
    trel E u1 u2 ->
    trel E A1 A2 ->
    trel E B1 B2 ->
    trel E v1 v2 ->
    trel E (sApp u1 n1 A1 B1 v1) (sApp u2 n2 A2 B2 v2)

| trel_Refl A1 A2 u1 u2 :
    trel E A1 A2 ->
    trel E u1 u2 ->
    trel E (sRefl A1 u1) (sRefl A2 u2)

| trel_Funext A1 A2 B1 B2 f1 f2 g1 g2 e1 e2 :
    trel E A1 A2 ->
    trel E B1 B2 ->
    trel E f1 f2 ->
    trel E g1 g2 ->
    trel E e1 e2 ->
    trel E (sFunext A1 B1 f1 g1 e1) (sFunext A2 B2 f2 g2 e2)

| trel_Uip A1 A2 u1 u2 v1 v2 p1 p2 q1 q2 :
    trel E A1 A2 ->
    trel E u1 u2 ->
    trel E v1 v2 ->
    trel E p1 p2 ->
    trel E q1 q2 ->
    trel E (sUip A1 u1 v1 p1 q1) (sUip A2 u2 v2 p2 q2)

| trel_J A1 A2 P1 P2 u1 u2 v1 v2 w1 w2 p1 p2 :
    trel E A1 A2 ->
    trel E P1 P2 ->
    trel E u1 u2 ->
    trel E v1 v2 ->
    trel E w1 w2 ->
    trel E p1 p2 ->
    trel E (sJ A1 u1 P1 w1 v1 p1) (sJ A2 u2 P2 w2 v2 p2)

| trel_Pair A1 A2 B1 B2 u1 u2 v1 v2 :
    trel E A1 A2 ->
    trel E B1 B2 ->
    trel E u1 u2 ->
    trel E v1 v2 ->
    trel E (sPair A1 B1 u1 v1) (sPair A2 B2 u2 v2)

| trel_SigLet A1 A2 B1 B2 P1 P2 p1 p2 t1 t2 :
    trel E A1 A2 ->
    trel E B1 B2 ->
    trel E P1 P2 ->
    trel E p1 p2 ->
    trel E t1 t2 ->
    trel E (sSigLet A1 B1 P1 p1 t1) (sSigLet A2 B2 P2 p2 t2)
.

Notation " t1 ∼ t2 " := (trel nil t1 t2) (at level 20).

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

(*! Heterogenous equality *)
Definition heq s A a B b :=
  sSig nAnon (sEq (sSort s) A B)
       (sEq (lift0 1 B)
            (sTransport (lift0 1 A) (lift0 1 B) (sRel 0) (lift0 1 a))
            (lift0 1 b)).

Lemma type_heq :
  forall {Σ Γ s A a B b},
      Σ ;;; Γ |-i A : sSort s ->
      Σ ;;; Γ |-i B : sSort s ->
      Σ ;;; Γ |-i a : A ->
      Σ ;;; Γ |-i b : B ->
      Σ ;;; Γ |-i heq s A a B b : sSort (succ_sort s).
Proof.
  intros Σ Γ s A a B b hA hB ha hb.
  assert (hs : Σ ;;; Γ |-i sSort s : sSort (succ_sort s)).
  { apply type_Sort. apply (typing_wf hA). }
  replace (sSort (succ_sort s)) with (sSort (max_sort (succ_sort s) s)) by (now rewrite max_succ_id).
  eapply type_Sig.
  - apply type_Eq ; eassumption.
  - apply type_Eq.
    + change (sSort s) with (lift0 1 (sSort s)).
      eapply typing_lift01.
      * assumption.
      * apply type_Eq ; eassumption.
    + apply type_Transport with (s := s).
      * change (sSort s) with (lift0 1 (sSort s)).
        eapply typing_lift01.
        -- assumption.
        -- apply type_Eq ; eassumption.
      * change (sSort s) with (lift0 1 (sSort s)).
        eapply typing_lift01.
        -- assumption.
        -- apply type_Eq ; eassumption.
      * simple refine (type_Rel Σ _ 0 _ _).
        -- econstructor.
           ++ apply (typing_wf hA).
           ++ exists (succ_sort s). apply type_Eq ; assumption.
        -- simpl. omega.
      * eapply typing_lift01.
        -- assumption.
        -- apply type_Eq ; eassumption.
    + eapply typing_lift01.
      * assumption.
      * apply type_Eq ; eassumption.
Defined.

Lemma heq_to_eq :
  forall {Σ Γ s A u v e},
    Σ ;;; Γ |-i e : heq s A u A v ->
    ∑ p, Σ ;;; Γ |-i p : sEq A u v.
Proof.
  intros Σ Γ s A u v e h.
  unfold heq in h.
  set (U := sEq (sSort s) A A) in h.
  set (V := sEq (lift0 1 A) (sTransport (lift0 1 A) (lift0 1 A) (sRel 0) (lift0 1 u)) (lift0 1 v)) in h.
  exists (sSigLet U V
             (sEq (lift0 1 A) (lift0 1 u) (lift0 1 v))
             e
             (sJ U
                 (sRel 1)
                 (sEq (lift0 3 A) (sTransport (lift0 3 A) (lift0 3 A) (sRel 1) (lift0 3 u)) (lift0 3 v))
                 (sRel 0)
                 (sRefl U A)
                 (sUip (sSort s) A A (sRel 1) (sRefl U A))
             )
  ).
Admitted.

Corollary sort_heq :
  forall {Σ Γ s A B e},
    Σ ;;; Γ |-i e : heq (succ_sort s) (sSort s) A (sSort s) B ->
    ∑ p, Σ ;;; Γ |-i p : sEq (sSort s) A B.
Proof.
  intros Σ Γ s A B e h.
  now eapply heq_to_eq.
Defined.

Lemma trelE_to_heq :
  forall {E Σ Γ},
    (forall x y s T1 T2,
        In (x,y) E ->
        Σ ;;; Γ |-i T1 : sSort s ->
        Σ ;;; Γ |-i T2 : sSort s ->
        Σ ;;; Γ |-i sRel x : T1 ->
        Σ ;;; Γ |-i sRel y : T2 ->
        ∑ p, Σ ;;; Γ |-i p : heq s T1 (sRel x) T2 (sRel y)) ->
    forall {t1 t2},
      trel E t1 t2 ->
      forall {s T1 T2},
        Σ ;;; Γ |-i T1 : sSort s ->
        Σ ;;; Γ |-i T2 : sSort s ->
        Σ ;;; Γ |-i t1 : T1 ->
        Σ ;;; Γ |-i t2 : T2 ->
        ∑ p, Σ ;;; Γ |-i p : heq s T1 t1 T2 t2.
Proof.
  intros E Σ Γ H t1 t2. induction 1 ; intros s' A B H1 H2 H3 H4.
  - now apply H.
  - destruct (uniqueness H3 H4) as [s eq].
    unfold heq. cbn.
    set (U := sEq (sSort s') A B).
    set (V := sEq (lift0 1 B) (sTransport (lift0 1 A) (lift0 1 B) (sRel 0) (sRel (S x))) (sRel (S x))).
    exists (sPair U V (sRefl (sSort s') A) (sRefl (lift0 1 B) (sRel (S x)))).
    eapply type_Pair.
    + eapply type_Eq.
      * apply type_Sort. apply (typing_wf H1).
      * assumption.
      * assumption.
    + eapply type_Eq.
      * instantiate (1 := s').
        change (sSort s') with (lift0 1 (sSort s')).
        eapply typing_lift01.
        -- assumption.
        -- (* TODO LATER *)
           admit.
      * eapply type_Transport.
        -- admit.
        -- admit.
        -- eapply type_Conv.
           ++ eapply type_Rel. constructor.
              ** apply (typing_wf H1).
              ** exists (succ_sort s'). eapply type_Eq.
                 --- apply type_Sort. apply (typing_wf H1).
                 --- assumption.
                 --- assumption.
           ++ eapply type_Eq.
              ** apply type_Sort. constructor.
                 --- apply (typing_wf H1).
                 --- exists (succ_sort s'). eapply type_Eq.
                     +++ apply type_Sort. apply (typing_wf H1).
                     +++ assumption.
                     +++ assumption.
              ** instantiate (1 := s') .
                 change (sSort s') with (lift0 1 (sSort s')).
                 eapply typing_lift01.
                 --- assumption.
                 --- eapply type_Eq.
                     +++ apply type_Sort. apply (typing_wf H1).
                     +++ assumption.
                     +++ assumption.
              ** change (sSort s') with (lift0 1 (sSort s')).
                 eapply typing_lift01.
                 --- assumption.
                 --- eapply type_Eq.
                     +++ apply type_Sort. apply (typing_wf H1).
                     +++ assumption.
                     +++ assumption.
           ++ cbn. apply eq_reflexivity.
              eapply type_Eq.
              ** apply type_Sort. constructor.
                 --- apply (typing_wf H1).
                 --- exists (succ_sort s'). eapply type_Eq.
                     +++ apply type_Sort. apply (typing_wf H1).
                     +++ assumption.
                     +++ assumption.
              ** change (sSort s') with (lift0 1 (sSort s')).
                 eapply typing_lift01.
                 --- assumption.
                 --- eapply type_Eq.
                     +++ apply type_Sort. apply (typing_wf H1).
                     +++ assumption.
                     +++ assumption.
              ** change (sSort s') with (lift0 1 (sSort s')).
                 eapply typing_lift01.
                 --- assumption.
                 --- eapply type_Eq.
                     +++ apply type_Sort. apply (typing_wf H1).
                     +++ assumption.
                     +++ assumption.
        -- change (sRel (S x)) with (lift0 1 (sRel x)).
           eapply typing_lift01.
           ++ assumption.
           ++ eapply type_Eq.
              ** apply type_Sort. apply (typing_wf H1).
              ** assumption.
              ** assumption.
      * change (sRel (S x)) with (lift0 1 (sRel x)).
        eapply typing_lift01.
        -- assumption.
        -- eapply type_Eq.
           ++ apply type_Sort. apply (typing_wf H1).
           ++ assumption.
           ++ assumption.
    + eapply type_Conv.
      * eapply type_Refl.
        -- apply type_Sort. apply (typing_wf H1).
        -- assumption.
      * eapply type_Eq.
        -- apply type_Sort. apply (typing_wf H1).
        -- assumption.
        -- assumption.
      * apply cong_Eq.
        -- apply eq_reflexivity. apply type_Sort. apply (typing_wf H1).
        -- apply eq_reflexivity. assumption.
        -- destruct (eq_typing eq) as [hs _].
           destruct (uniqueness hs H1).
           eapply eq_conv ; eassumption.
    + (* This is me being lazy? *)
      admit.
  - admit. (* Need inversion on typing of transport *)
  - admit. (* Need inversion on typing of transport *)
  - admit. (* Need inversion on typing *)
Admitted.

Corollary trel_to_heq :
  forall {Σ Γ s T1 T2} {t1 t2 : sterm},
    t1 ∼ t2 ->
    Σ ;;; Γ |-i T1 : sSort s ->
    Σ ;;; Γ |-i T2 : sSort s ->
    Σ ;;; Γ |-i t1 : T1 ->
    Σ ;;; Γ |-i t2 : T2 ->
    ∑ p, Σ ;;; Γ |-i p : heq s T1 t1 T2 t2.
Proof.
  intros Σ Γ s T1 T2 t1 t2 H H0 H1 H2 H3.
  now apply @trelE_to_heq with (E := nil).
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
  - easy.
  - cbn. destruct (k <=? x) ; now constructor.
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
  - exfalso. easy.
  - unfold subst. destruct (nat_compare n x).
    + now apply trel_lift.
    + apply trel_Rel.
    + apply trel_Rel.
Defined.

Lemma trel_refl : forall {t}, t ∼ t.
Proof.
  induction t ; try (now constructor).
  constructor. constructor. assumption.
Defined.

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
  - easy.
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
| headSig
| headPair
| headSigLet
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
  | sSig n A B => headSig
  | sPair A B u v => headPair
  | sSigLet A B P p t => headSigLet
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

Inductive type_head : head_kind -> Type :=
| type_headSort s : type_head (headSort s)
| type_headProd : type_head headProd
| type_headEq : type_head headEq
| type_headSig : type_head headSig
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
    + destruct (inversionSig ht) as [s1 [s2 [[? ?] ?]]].
      exists (max_sort s1 s2). repeat split.
      * now apply type_Sig.
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
      eapply type_Conv.
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
    pose (thm := @trel_to_heq Σ Γ' (succ_sort s) (sSort s) (sSort s) A' A'' simA).
    rewrite <- heq in hs.
    destruct thm as [p hp].
    + apply type_Sort. apply (typing_wf h').
    + apply type_Sort. apply (typing_wf h').
    + assumption.
    + eapply type_Conv.
      * eassumption.
      * eassumption.
      * eapply sorts_in_sort.
        -- apply type_Sort. apply (typing_wf h').
        -- assumption.
    + destruct (sort_heq hp) as [q hq].
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

(* This has an extra assumption when compared to the paper version.
   Hopefully it will be enough to deal with translation.
 *)
Lemma change_type :
  forall {Σ Γ A t Γ' A' t' s A''},
    Σ ;;; Γ' |-i A' : sSort s ->
    Σ ;;;; Γ' |--- [ t' ] : A' # ⟦ Γ |--- [t] : A ⟧ ->
    Σ ;;;; Γ' |--- [ A'' ] : sSort s # ⟦ Γ |--- [A] : sSort s ⟧ ->
    ∑ t'', Σ ;;;; Γ' |--- [ t'' ] : A'' # ⟦ Γ |--- [t] : A ⟧.
Proof.
  intros Σ Γ A t Γ' A' t' s A'' hAs [[[rΓ' rA'] rt'] ht'] [[[rΓ'' _] rA''] hA''].
  assert (simA : A' ∼ A'').
  { eapply trel_trans.
    - eapply trel_sym. eapply inrel_trel. eassumption.
    - eapply inrel_trel. eassumption.
  }
  destruct (@trel_to_heq Σ Γ' (succ_sort s) (sSort s) (sSort s) A' A'' simA) as [p hp].
  - apply type_Sort. apply (typing_wf ht').
  - apply type_Sort. apply (typing_wf ht').
  - assumption.
  - assumption.
  - destruct (sort_heq hp) as [q hq].
    exists (sTransport A' A'' q t').
    repeat split.
    + assumption.
    + assumption.
    + constructor. assumption.
    + eapply type_Transport ; eassumption.
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
Definition eqtrans Σ Γ s A u v Γ' A' A'' u' v' p' :=
  Γ ⊂ Γ' *
  A ⊏ A' *
  A ⊏ A'' *
  u ⊏ u' *
  v ⊏ v' *
  (Σ ;;; Γ' |-i p' : heq s A' u' A'' v').

Fixpoint context_translation {Σ Γ} (h : XTyping.wf Σ Γ) :
  ∑ Γ', Σ |--i Γ' # ⟦ Γ ⟧

with type_translation {Σ Γ A t} (h : Σ ;;; Γ |-x t : A)
                          {Γ'} (hΓ : Σ |--i Γ' # ⟦ Γ ⟧) {struct h} :
  ∑ A' t', Σ ;;;; Γ' |--- [t'] : A' # ⟦ Γ |--- [t] : A ⟧

with eq_translation {Σ Γ s A u v} (h : Σ ;;; Γ |-x u = v : A)
                    (hA : Σ ;;; Γ |-x A : sSort s)
                    {Γ'} (hΓ : Σ |--i Γ' # ⟦ Γ ⟧) {struct h} :
  ∑ A' A'' u' v' p',
    eqtrans Σ Γ s A u v Γ' A' A'' u' v' p'
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
      * apply inrel_lift.
        (* Need lemma for Γ ⊂ Γ' -> ... *)
        cheat.
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
      assert (hS' : Σ ;;; Γ' ,, svass n t'' |-i S' : sSort s2).
      { (* Maybe we need to relax change_type, otherwise it won't be usable.
           Maybe this could be done by removing sort annotation to Eq (which we
           don't feature in the article anyway).
         *)
        cheat.
      }
      destruct (change_type hS' hb' hbty'') as [b'' hb''].
      clear hS' hb' S' b'.
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
      rename n0 into x, T'1 into A'', T'2 into B''.
      assert (hS' : Σ ;;; Γ' |-i sProd x A'' B'' : sSort (max_sort s1 s2)).
      { (* I see no way of proving this... *)
        cheat.
      }
      destruct (change_type hS' ht' (trans_Prod hΓ hA' hB')) as [t'' ht''].
      clear hS' ht' A'' B'' t'.
      (* Translation of the argument *)
      destruct (type_translation _ _ _ _ h4 _ hΓ) as [A'' [u'' hu'']].
      assert (hS : Σ ;;; Γ' |-i A'' : sSort s1).
      { (* Maybe we could add something to the theorem to state that the
           translation of the type lives in the right sort.
         *)
        cheat.
      }
      destruct (change_type hS hu'' hA') as [u' hu'].
      clear hS hu'' A'' u''.
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
      assert (hS : Σ ;;; Γ' |-i A'' : sSort s).
      { cheat. }
      destruct (change_type hS hu'' hA') as [u' hu'].
      clear hS hu'' u'' A''.
      (* The other term *)
      destruct (type_translation _ _ _ _ h3 _ hΓ) as [A'' [v'' hv'']].
      assert (hS : Σ ;;; Γ' |-i A'' : sSort s).
      { cheat. }
      destruct (change_type hS hv'' hA') as [v' hv'].
      (* Now we conclude *)
      exists (sSort s), (sEq A' u' v').
      apply trans_Eq ; assumption.

    (* type_Refl *)
    + (* Here we have two choices, either to translate h1 or not.
         If we do translate it we get hypotheses on the sort of A,
         but we also need to say that the translation we get from h2
         is also living in this sort...
         So it would be worth it only in the event that we return information
         about the sort in type_translation.
       *)
      destruct (type_translation _ _ _ _ h2 _ hΓ) as [A' [u' hu']].
      exists (sEq A' u' u'), (sRefl A' u').
      destruct hu' as [[[? ?] ?] hu'].
      destruct hΓ.
      (* This step might no longer be necesary later *)
      destruct (istype_type hu').
      repeat split.
      * assumption.
      * constructor ; assumption.
      * constructor ; assumption.
      * eapply type_Refl ; eassumption.

    (* type_Conv *)
    + (* Translating the conversion *)
      assert (hs : Σ ;;; Γ |-x sSort s : sSort (succ_sort s)).
      { constructor. apply (XTyping.typing_wf h1). }
      destruct (eq_translation _ _ _ _ _ _ e hs _ hΓ)
        as [S' [S'' [A' [B' [p' h']]]]].
      destruct h' as [[[[[eΓ eS'] eS''] eA] eB] hp'].
      (* With this new version I no longer know of the shape of the types. *)
      (* assert (Ss : S' = sSort s) by (inversion eS'). subst. *)
      (* assert (Ss : S'' = sSort s) by (inversion eS''). subst. *)
      (* Can similar things be done to solve more sorts? *)
      (* destruct (sort_heq hp') as [q hq]. *)
      (* Translating the term *)
      destruct (type_translation _ _ _ _ h1 _ hΓ) as [A'' [t' ht']].
      (* Translating the other type *)
      destruct (type_translation _ _ _ _ h2 _ hΓ) as [S [B''' hB''']].
      assert (th : type_head (head (sSort s))) by constructor.
      destruct (choose_type th hB''') as [T [[B'' hB''] hh]].
      clear hB''' B''' S.
      destruct T ; inversion hh. subst. clear hh th.
      (* Problem! Nothing ever states that A' or A'' are translations.
         This is going to prove hard if we ever want to apply change_type.
         Maybe we should add an hypothesis to the conversion rule
         and/or to the conclusion of eq_translation.
       *)
      cheat.

  (** eq_translation **)
  - dependent destruction h.

    (* eq_reflexivity *)
    + destruct (type_translation _ _ _ _ t _ hΓ) as [A' [u' hu]].
      (* First we should dea with the different properties of heq.
         This should come with the quoting of terms (the likes of
         convinceme.v).
         By the way, the very same terms should come in handy when dealing
         with trel_to_heq.
         By the way, maybe we can add transitivity as a constructor to
         trel. It would be translated as well wouldn't it?
         But maybe if would mess with inversions, so it might be a better
         idea to leave it as it is.
       *)
      cheat.

    (* eq_symmetry *)
    + cheat.

    (* eq_transitivity *)
    + cheat.

    (* eq_beta *)
    + cheat.

    (* eq_conv *)
    + cheat.

    (* cong_Prod *)
    + cheat.

    (* cong_Lambda *)
    + cheat.

    (* cong_App *)
    + cheat.

    (* cong_Eq *)
    + cheat.

    (* cong_Refl *)
    + cheat.

    (* reflection *)
    + cheat.
Defined.


End Translation.