(* Distributed under the terms of the MIT license.   *)
Set Warnings "-notation-overridden".

From Coq Require Import Bool String List Program BinPos Compare_dec ZArith.


From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICEquality
     PCUICUnivSubst PCUICTyping PCUICGeneration.

From MetaCoq.Template Require Import config utils Ast TypingWf WfInv UnivSubst LiftSubst.

Require PCUICToTemplateCorrectness TemplateToPCUICCorrectness.

Module PT := PCUICToTemplate.
Module TP := TemplateToPCUIC.


Lemma retr t : TP.trans (PT.trans t) = t.
Proof.
  induction t using term_forall_list_ind; cbnr; f_equal; auto.
  2: { rewrite TemplateToPCUICCorrectness.trans_mkApp. now f_equal. }
  all: rewrite map_map; apply All_map_id; tas; eapply All_impl; tea; cbn.
  intros []; cbn. unfold on_snd; simpl. congruence.
  intros []; cbn. unfold map_def; simpl. intros []; congruence.
  intros []; cbn. unfold map_def; simpl. intros []; congruence.
Qed.

Fixpoint without_cast t : bool :=
 match t with
 | tRel n => true
 | tVar id => true
 | tEvar ev args => forallb without_cast args
 | tSort s => true
 | tCast t kind v => false
 | tProd na ty body => without_cast ty && without_cast body
 | tLambda na ty body => without_cast ty && without_cast body
 | tLetIn na def def_ty body
   => without_cast def && without_cast def_ty && without_cast body
 | tApp f args => without_cast f && forallb without_cast args
 | tConst c u => true
 | tInd ind u => true
 | tConstruct ind idx u => true
 | tCase ind_and_nbparams type_info discr branches
   => without_cast type_info && without_cast discr &&
     forallb (without_cast ∘ snd) branches
 | tProj proj t => without_cast t
 | tFix mfix idx
 | tCoFix mfix idx =>
   forallb (without_cast ∘ dtype) mfix && forallb (without_cast ∘ dbody) mfix
 end.

Lemma without_cast_mkApp t u :
  without_cast (mkApp t u) = without_cast t && without_cast u.
Proof.
  induction t; cbnr; rewrite ?andb_true_r; trea.
  rewrite forallb_app, andb_assoc; cbn. now rewrite andb_true_r.
Qed.

Lemma PT_trans_without_cast t : without_cast (PT.trans t).
Proof.
  induction t using term_forall_list_ind; cbnr; repeat toProp; tas.
  2: { rewrite without_cast_mkApp. now toProp. }
  all: apply All_forallb; solve_all.
Qed.

Lemma PT_trans_wf t : wf (PT.trans t).
Proof.
  induction t using term_forall_list_ind; cbnr; try constructor; tas.
  2: now apply wf_mkApp.
  all: solve_all.
  admit. (* isLambda fix *)
Admitted.


Lemma sect t : wf t -> without_cast t -> PT.trans (TP.trans t) = t.
Proof.
  induction t using Induction.term_forall_list_ind; cbnr; try discriminate;
    intros H1 H2; invs H1; cbn in *; rtoProp; f_equal; auto.
  2: assert (map PT.trans (map TP.trans l) = l) as HH.
  3:{ rewrite PCUICToTemplateCorrectness.trans_mkApps; cbn.
      rewrite IHt, HH; tas. now apply mkApps_tApp. }
  all: rewrite ?map_map; try apply All_map_id; solve_all.
  destruct x; unfold on_snd; cbn in *; congruence.
  destruct x; unfold map_def; cbn in *; congruence.
  destruct x; unfold map_def; cbn in *; congruence.
Qed.

Lemma TP_trans_isApp t :
  wf t -> without_cast t -> PCUICAst.isApp (TP.trans t) = isApp t.
Proof.
  destruct 1; cbnr.
  discriminate.
  intros _. clear -H0.
  destruct u. contradiction.
  cbn. apply isApp_mkApps. reflexivity.
Qed.


Require Import PCUICAst ssrbool.

Lemma term_app_forall_list_ind :
  forall P : term -> Type,
    (forall n : nat, P (tRel n)) ->
    (forall i : ident, P (tVar i)) ->
    (forall (n : nat) (l : list term), All P l -> P (tEvar n l)) ->
    (forall s, P (tSort s)) ->
    (forall (n : name) (t : term), P t -> forall t0 : term, P t0 -> P (tProd n t t0)) ->
    (forall (n : name) (t : term), P t -> forall t0 : term, P t0 -> P (tLambda n t t0)) ->
    (forall (n : name) (t : term),
        P t -> forall t0 : term, P t0 -> forall t1 : term, P t1 -> P (tLetIn n t t0 t1)) ->
    (forall t l, ~~ (isApp t) -> P t -> All P l -> P (mkApps t l)) ->
    (forall (s : String.string) (u : list Level.t), P (tConst s u)) ->
    (forall (i : inductive) (u : list Level.t), P (tInd i u)) ->
    (forall (i : inductive) (n : nat) (u : list Level.t), P (tConstruct i n u)) ->
    (forall (p : inductive * nat) (t : term),
        P t -> forall t0 : term, P t0 -> forall l : list (nat * term),
            tCaseBrsProp P l -> P (tCase p t t0 l)) ->
    (forall (s : projection) (t : term), P t -> P (tProj s t)) ->
    (forall (m : mfixpoint term) (n : nat), tFixProp P P m -> P (tFix m n)) ->
    (forall (m : mfixpoint term) (n : nat), tFixProp P P m -> P (tCoFix m n)) ->
    forall t : term, P t.
Proof.
  intros P X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14.
  enough (forall t, wf t -> without_cast t -> P (TP.trans t)) as XX. {
    intro t. specialize (XX (PT.trans t)).
    rewrite retr in XX; apply XX.
    apply PT_trans_wf. apply PT_trans_without_cast. }
  induction t using Induction.term_forall_list_rect; cbn; auto;
    try discriminate; intros XX YY; rtoProp.
  - apply X2.
    assert (Forall wf l) as HH by now invs XX.
    solve_all.
  - apply X4.
    + apply IHt1; now invs XX.
    + apply IHt2; now invs XX.
  - apply X5.
    + apply IHt1; now invs XX.
    + apply IHt2; now invs XX.
  - apply X6.
    + apply IHt1; now invs XX.
    + apply IHt2; now invs XX.
    + apply IHt3; now invs XX.
  - apply X7.
    + invs XX. now rewrite TP_trans_isApp, H3.
    + apply IHt; tas. invs XX; tas.
    + assert (Forall wf l) as HH by now invs XX.
      solve_all.
Admitted.
