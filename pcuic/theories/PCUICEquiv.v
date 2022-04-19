From Coq Require Import Utf8 ssreflect.
From MetaCoq.Template Require Import utils config.
From MetaCoq.PCUIC Require Import PCUICAst PCUICReduction PCUICTyping PCUICValidity PCUICSN PCUICSR.

Local Existing Instance default_checker_flags.

Record car {Σ} := mkCar {
  context : context;
  subject : term;
  type : term;
  typing : Σ ;;; context |- subject : type
}.
Arguments car : clear implicits.
Derive NoConfusion for car.
Import PCUICSafeLemmata.

Definition rel Σ (x y : car Σ) :=
  (* typing_size (typing x) < typing_size (typing y) \/ *)
  (cored Σ (context x) (subject x) (subject y) /\ context x = context y /\ type x = type y) \/
  (cored Σ (context x) (type x) (type y)  /\ context x = context y /\ subject x = subject y).

Import Relation_Definitions Relation_Operators.

Definition compose {A} (R R' : relation A) := fun x z => exists y, R x y /\ R' y z.

Section Acc_equiv.
  Context {A} (R R' : relation A).

  Lemma Acc_equiv : (forall x y, R x y <-> R' x y) -> forall x, Acc R x -> Acc R' x.
  Proof.
    intros heq x.
    induction 1. constructor; intros y hr.
    eapply heq in hr. now apply H0.
  Qed.
End Acc_equiv.

Section Acc_union.
  Context {A} (R R' : relation A).
  Context (wfr : well_founded R) (wfr' : well_founded R').

  Context (comp : forall x y, compose R R' x y <-> compose R' R x y).

  (* Lemma comp_union x y : union _ R R' x y <-> compose R R' x y. *)
  
  Inductive AccR (x : A) : Prop :=
	  | Acc_introR : (∀ y : A, R y x → AccR y) → AccR x
    | Acc2 : Acc R' x -> AccR x.

  (* Context (trans : forall x y z, union _ R R' x y -> union _ R R' y z -> union _ R R' x z). *)

  Lemma accu_accr x : Acc (union _ R R') x -> AccR x.
  Proof.
    induction 1.
    constructor.
    intros y hr. now specialize (H0 _ (or_introl hr)).
  Qed.

  Lemma accr_accu x : AccR x -> Acc (union _ R R') x.
  Proof.
    induction 1. clear H.
    induction (wfr' x). clear H.
    - constructor.
      intros y hr. destruct hr. eauto.
      eapply H1; tea. intros.
      destruct (comp y0 x). forward H3. red. exists y; split => //.
      destruct H3 as [z [Hz Hz']].
      specialize (H0 _ Hz'). 
      apply (Acc_inv H0 (or_intror Hz)).
    - induction H. clear H.
      induction (wfr x). clear H.
      constructor.
      intros y hr. destruct hr; eauto.
      eapply H1; tea. intros.
      destruct (comp y0 x). forward H4. red. exists y; split => //.
      destruct H4 as [z [Hz Hz']].
      specialize (H0 _ Hz'). 
      apply (Acc_inv H0 (or_introl Hz)).
  Qed.

  Lemma acc_union x : Acc (union _ R R') x.
  Proof.
    eapply accr_accu.
    induction (wfr x). clear H.
    constructor. apply H0.
  Qed.

End Acc_union.

Require Import Wf.
From Equations Require Import Equations.

Lemma Acc_image {A B} (R : relation A) (f : B -> A) : forall x : B, Acc R (f x) -> Acc (fun x y => R (f x) (f y)) x.
Proof.
  intros x.
  intros H; depind H.
  constructor. 
  intros y hr.
  eapply H0. exact hr. reflexivity.
Qed.

Lemma wf_subject_red Σ {wfΣ : wf_ext Σ} : forall x : car Σ,
  Acc (fun x y => cored Σ (context x) (subject x) (subject y) /\ 
    (context x) = (context y) /\ (type x) = (type y)) x.
Proof.
  intros x.
  pose proof (normalisation _ wfΣ).
  specialize (H _ _ (iswelltyped (typing x))).
  destruct x as [Γ t T Ht].
  cbn in *.
  revert T Ht. induction H.
  intros.
  constructor. cbn.
  intros [Γ' t' T' Ht']; cbn; intros [hred []].
  subst Γ' T'.
  eapply H0. exact hred.
Qed.

Lemma wf_type_red Σ {wfΣ : wf_ext Σ} : forall x : car Σ,
  Acc (fun x y => cored Σ (context x) (type x) (type y) /\ (context x) = (context y) /\ (subject x) = (subject y)) x.
Proof.
  intros x.
  pose proof (normalisation _ wfΣ).
  pose proof (validity (typing x)).
  destruct X as [s Hs].
  specialize (H _ _ (iswelltyped Hs)). clear s Hs.
  destruct x as [Γ t T Ht]. cbn in *.
  cbn in *.
  revert t Ht. induction H.
  intros.
  constructor. cbn.
  intros [Γ' t' T' Ht']; cbn; intros [hred []].
  subst Γ' t'.
  eapply H0. exact hred.
Qed.

Import PCUICOnFreeVars PCUICCumulativity PCUICConversion.

Lemma wf_rel Σ : wf_ext Σ -> forall x : car Σ, Acc (rel Σ) x.
Proof.
  intros wfΣ car.
  apply acc_union; auto.
  red. eapply (wf_subject_red Σ).
  red; now eapply wf_type_red. 
  unfold compose. 
  intros [Γ t T Ht] [Γ' t' T' Ht']; cbn in *.
  split.
  - intros [[Γ'' t'' T'' Ht''] [hred' []]]. cbn in *.
    destruct H0; subst.
    destruct hred'. destruct H1; subst.
    destruct (cored_alt _ _ _ _ H) as [hr].
    unshelve eexists (mkCar Σ Γ' t T' _).
    { eapply validity in Ht' as [s HT']. eapply type_Cumul; tea.
      eapply PCUICConversion.cumulAlgo_cumulSpec.
      eapply PCUICWellScopedCumulativity.into_ws_cumul_pb; fvs.
      eapply red_cumul_inv. red.
      now eapply clos_t_rt. }
    cbn. intuition auto.
  - intros [[Γ'' t'' T'' Ht''] [hred' []]]. cbn in *.
    destruct H0; subst.
    destruct hred'. destruct H1; subst.
    destruct (cored_alt _ _ _ _ H0) as [hr].
    destruct (cored_alt _ _ _ _ H) as [hr'].
    unshelve eexists (mkCar Σ Γ' t' T _).
    { eapply validity in Ht as [s HT']. eapply type_Cumul; tea.
      eapply PCUICConversion.cumulAlgo_cumulSpec.
      eapply PCUICWellScopedCumulativity.into_ws_cumul_pb; fvs.
      eapply red_cumul. red.
      now eapply clos_t_rt. }
    cbn. intuition auto.
Qed.

Definition inj_car {Σ Γ t T} (d : Σ ;;; Γ |- t : T) := mkCar _ _ _ _ d.

Definition subderiv Σ (d d' : car Σ) : Prop := 
  match d'.(typing) with
  | type_Cumul t A B s ta bs cum => (d = inj_car ta \/ d = inj_car bs)
  | _ => False
  end.

Definition is_subderiv {Σ} (d d' : car Σ) : Prop := 
  match d'.(typing) with
  | type_Cumul t A B s ta bs cum => d = inj_car bs
  | _ => False
  end.

Definition on_subderiv Σ (P : car Σ -> car Σ -> Prop) (d d' : car Σ) : Prop := 
  match d'.(typing) with
  | type_Cumul t A B s ta bs cum => P d (inj_car ta)
    (* d = inj_car bs \/  *)
    (* P d (inj_car bs) *)
  | _ => False
  end.

Set Equations With UIP.
Import PCUICReflect PCUICWellScopedCumulativity.

Definition rel' Σ P (x y : car Σ) :=
  on_subderiv _ P x y.


Definition on_subderivty Σ (P : car Σ -> car Σ -> Prop) (d d' : car Σ) : Prop := 
  match d'.(typing) with
  | type_Cumul t A B s ta bs cum => P d (inj_car bs)
    (* d = inj_car bs \/  *)
    (* P d (inj_car bs) *)
  | _ => False
  end.

Definition rel'' Σ P (x y : car Σ) :=
  on_subderivty _ P x y.

Definition on_subderivs Σ (P : car Σ -> Prop) (d : car Σ) : Prop := 
  match d.(typing) with
  | type_Cumul t A B s ta bs cum => P (inj_car ta)
  | _ => True
  end.
(* 
Lemma ons Σ (P : car Σ -> Prop) (R : car Σ -> car Σ -> Prop) 
  (HRP : forall x y, R x y -> P x) d : Acc R d -> on_subderivs Σ P d.
Proof.
  induction 1.
  destruct x.
  destruct typing0; cbn => //.
  specialize (H0 (inj_car typing0_2)).
  forward H0. cbn. *)

Definition red_subject Σ (x y : car Σ) := 
  cored Σ (context x) (subject x) (subject y) /\ 
  (context x) = (context y) /\ (type x) = (type y).

Definition red_type Σ (x y : car Σ) := 
  cored Σ (context x) (type x) (type y) /\ 
  (context x) = (context y) /\ (subject x) = (subject y).

Lemma wf_rel' Σ : wf_ext Σ -> 
  forall x : car Σ, Acc (rel' Σ (red_subject Σ)) x.
Proof.
  intros wfΣ car.
  pose proof (normalisation _ wfΣ _ _ (iswelltyped (typing car))).
  destruct car as [Γ t T Ht]; cbn in *.
  revert T Ht.
  induction H.
  intros T Ht.
  destruct Ht.
  1-13:constructor;
  intros [Γ' t' T' Ht']; unfold rel'; cbn => //.
  set (tc := {| typing := type_Cumul _ _ _ _ _ _ _ _ _ |}).
  constructor. intros.
  unfold rel' in H1.
  cbn in H1. destruct y as [].
  unfold red_subject in H1. cbn in H1. destruct H1 as [cor [eqctx eqty]].
  subst context0 type0.
  now eapply (H0).
Qed.

Lemma subject_reduction_cored {Σ} {wfΣ : wf_ext Σ} {Γ t t' T} : 
  Σ ;;; Γ |- t : T ->
  cored Σ Γ t' t ->
  ∥ Σ ;;; Γ |- t' : T ∥.
Proof.
  intros ht.
  move/cored_alt => [] hr.
  sq. eapply subject_reduction; tea. apply wfΣ.
  now eapply clos_t_rt.
Qed.

Lemma type_reduction_cored {Σ} {wfΣ : wf_ext Σ} {Γ t T T'} : 
  Σ ;;; Γ |- t : T ->
  cored Σ Γ T' T ->
  ∥ Σ ;;; Γ |- t : T' ∥.
Proof.
  intros ht.
  move/cored_alt => [] hr.
  sq. eapply type_reduction; tea.
  now eapply clos_t_rt.
Qed.

Lemma wf_rel'' Σ : wf_ext Σ -> 
  forall x : car Σ, Acc (rel'' Σ (rel Σ)) x.
Proof.
  intros wfΣ car.
  pose proof (wf_rel _ wfΣ car).
  induction H.
  destruct x as [Γ t T Ht]; cbn in *.
  destruct Ht. 1-13:admit.
  constructor; intros [].
  unfold rel''. cbn. intros hrel.
  unfold inj_car in hrel. red in hrel. cbn in hrel.
  destruct hrel.
  - destruct H1 as [? []]. subst Γ type0.
    assert (∥ ∑ H2 : Σ ;;; context0 |- t : subject0 , on_subderivty Σ (rel Σ) {|
      context := context0;
      subject := subject0;
      type := tSort s;
      typing := typing0
    |} (inj_car H2) ∥).
    { move/cored_alt: H1 => [hr]. sq.
      exists (type_reduction (type_Cumul Σ context0 t A B s Ht1 Ht2 c) (clos_t_rt _ _ hr)).
      admit. }
    destruct H2 as [[H2 H2P]].
    specialize (H0 {| context := context0; subject := _; type := _; typing := H2 |}). apply H0.
    unfold rel. cbn. right; auto.
    red. apply H2P.
  -
    red. cbn.

  intros 


  destruct (validity (typing car)).
  pose proof (normalisation _ wfΣ _ _ (iswelltyped t)). clear x t.
  destruct car as [Γ t T Ht]; cbn in *.
  revert t Ht.
  induction H.
  intros t Ht.
  destruct Ht.
  1-13:constructor;
  intros [Γ' t' T' Ht']; unfold rel''; cbn => //.
  set (tc := {| typing := type_Cumul _ _ _ _ _ _ _ _ _ |}).
  constructor. intros.
  unfold rel'' in H1.
  cbn in H1. destruct y as [].
  unfold red_type in H1. cbn in H1. destruct H1 as [cor [eqctx eqty]].
  subst context0 subject0. specialize (H0 _ cor).
  eapply H0.
Qed.

(*Lemma wf_rel' Σ P : wf_ext Σ -> 
  (forall x : car Σ, Acc P x) ->
  forall x : car Σ, Acc (rel' Σ P) x.
Proof.
  intros wfΣ HP car.
  induction car. induction typing0.
  1-13:constructor;
  intros [Γ' t' T' Ht']; unfold rel'; cbn => //.
  set (tc := {| typing := type_Cumul _ _ _ _ _ _ _ _ _ |}).
  pose proof (HP (inj_car typing0_2)). unfold tc in *.
  clear -H.
  unfold inj_car in *.
  constructor. intros.
  unfold rel' in H0.

  depind H.
  constructor.
  intros y. set (yr := y).
  destruct y as [Γ0 t0 T0 Ht0].
  intros hrel.
  cbn in hrel.
  (* - unfold inj_car in eq. cbn in eq. noconf eq. cbn in *.
    eapply IHtyping0_2. *)
  - specialize ()
  
    epose proof (Acc_inv IHtyping0_2).
    apply H1. red.
    unfold rel'.
    constructor. 
    intros y'.
    set (yr' := y').
    destruct y' as [Γ0' t0' T0' H0'].
    destruct H0; cbn. 1-13:move=> //.
    intros []. subst yr'. unfold inj_car in H0; cbn in H0. noconf H0.
    cbn in *.
    { eapply H1.
    [].
Qed.

Definition rel' Σ (x y : car Σ) :=
  on_subderiv _ (rel Σ) x y.

Lemma wf_rel' Σ : wf_ext Σ -> forall x : car Σ, Acc (rel' Σ) x.
Proof.
  intros wfΣ car.
  induction car. induction typing0.
  1-13:constructor;
  intros [Γ' t' T' Ht']; unfold rel'; cbn => //.
  set (tc := {| typing := type_Cumul _ _ _ _ _ _ _ _ _ |}).
  pose proof (wf_rel _ wfΣ tc). unfold tc in *.
  depind H.
  constructor.
  intros y. set (yr := y).
  destruct y as [Γ0 t0 T0 Ht0].
  intros [eq|hrel].
  - unfold inj_car in eq. cbn in eq. noconf eq. cbn in *.
    eapply IHtyping0_2.
  - epose proof (Acc_inv IHtyping0_2).
    apply H1. red.
    unfold rel'.
    constructor. 
    intros y'.
    set (yr' := y').
    destruct y' as [Γ0' t0' T0' H0'].
    destruct H0; cbn. 1-13:move=> //.
    intros []. subst yr'. unfold inj_car in H0; cbn in H0. noconf H0.
    cbn in *.
    { eapply H1.
    [].
Qed.*)
(* destruct H as [? []]. subst Γ.
  
  unfold on_subderiv. cbn.
  simpl.
  unfold on_subderiv.
  intros 

  apply acc_union; auto.
  { red. intros [Γ t T Ht].
    induction Ht.
    all:constructor; intros []; cbn; intros H.
    all:destruct H as [H].
    all:try solve [destruct H].
    unfold inj_car in H. destruct H.
    * noconf H. now cbn in IHHt1.
    * noconf H. now cbn in IHHt2. }
  { red. now eapply wf_rel. }
  red. 
  unfold compose. 
  intros [Γ t T Ht] [Γ' t' T' Ht']; cbn -[typing_size] in *.
  split.
  - intros [[Γ'' t'' T'' Ht''] [hred' []]]. cbn -[typing_size] in *.
    destruct H; subst. destruct H0; subst.
    destruct (cored_alt _ _ _ _ H) as [hr].
    unfold rel. cbn -[typing_size].
    destruct hred'.
    destruct Ht''; cbn in H0 => //.
    destruct H0; unfold inj_car in *.
    * noconf H0.
      eexists (inj_car Ht'). cbn.
    { cbn -[typing_size]. 
      inv X.
      depelim X.
    eapply validity in Ht' as [s HT']. eapply type_Cumul; tea.
      eapply PCUICConversion.cumulAlgo_cumulSpec.
      eapply PCUICWellScopedCumulativity.into_ws_cumul_pb; fvs.
      eapply red_cumul_inv. red.
      now eapply clos_t_rt. }
    cbn. intuition auto.
  - intros [[Γ'' t'' T'' Ht''] [hred' []]]. cbn in *.
    destruct H0; subst.
    destruct hred'. destruct H1; subst.
    destruct (cored_alt _ _ _ _ H0) as [hr].
    destruct (cored_alt _ _ _ _ H) as [hr'].
    unshelve eexists (mkCar Σ Γ' t' T _).
    { eapply validity in Ht as [s HT']. eapply type_Cumul; tea.
      eapply PCUICConversion.cumulAlgo_cumulSpec.
      eapply PCUICWellScopedCumulativity.into_ws_cumul_pb; fvs.
      eapply red_cumul. red.
      now eapply clos_t_rt. }
    cbn. intuition auto.
Qed. *)

Local Instance wf Σ {wfΣ : wf_ext Σ} : WellFounded (rel' Σ (red_subject Σ)).
Proof. red. red. now apply wf_rel'. Qed.
 (* now apply wf_rel. Qed. *)

Lemma test {Σ : global_env_ext} {wfΣ : wf_ext Σ} {Γ t T} : 
  Σ ;;; Γ |- t : T -> Σ ;;; Γ |- t : T.
Proof.
  intros d.
  epose proof (FixWf (WF:=wf Σ)).
  set (c := mkCar _ Γ t T d).
  change Γ with (context c).
  change t with (subject c).
  change T with (type c).
  clearbody c. revert c. clear -wfΣ X.
  refine (X _ _).
  intros [Γ t T d]; cbn. unfold rel. cbn.
  intros IH.
  set (IH' := fun Γ' t' T' (d' : Σ ;;; Γ' |- t' : T') => IH (mkCar _ Γ' t' T' d')).
  clearbody IH'. cbn in IH'. clear IH. rename IH' into IH.
  destruct d.
  14:{
    clear X. unfold rel' in IH.
    eapply type_Cumul.
    eapply IH. cbn. unfold inj_car, rel. cbn.
    split. cbn. reflexivity.
    assert (Σ ;;; Γ ⊢ B ⇝1 A). admit.
    clear IH. eapply subject_reduction1 in d2; tea. 2:exact X.
    exists (inj_car d2). cbn. left. intuition auto.
    eapply cored_alt. sq. eapply clrel_rel in X. now constructor.



    specialize (y ) 

   }
  
  rec_wf_rel IH d (rel Σ).