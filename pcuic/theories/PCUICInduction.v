(* Distributed under the terms of the MIT license.   *)

From MetaCoq.Template Require Import utils.
From MetaCoq.PCUIC Require Import PCUICAst.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICSize.
Require Import List Program Lia.
Require Import BinPos.
Require Import Coq.Arith.Compare_dec Bool.
Set Asymmetric Patterns.

(** * Deriving a compact induction principle for terms

  *WIP*

  Allows to get the right induction principle on lists of terms appearing
  in the term syntax (in evar, applications, branches of cases and (co-)fixpoints. *)

(** Custom induction principle on syntax, dealing with the various lists appearing in terms. *)

Lemma term_forall_list_ind :
  forall P : term -> Type,
    (forall n : nat, P (tRel n)) ->
    (forall i : ident, P (tVar i)) ->
    (forall (n : nat) (l : list term), All P l -> P (tEvar n l)) ->
    (forall s, P (tSort s)) ->
    (forall (n : name) (t : term), P t -> forall t0 : term, P t0 -> P (tProd n t t0)) ->
    (forall (n : name) (t : term), P t -> forall t0 : term, P t0 -> P (tLambda n t t0)) ->
    (forall (n : name) (t : term),
        P t -> forall t0 : term, P t0 -> forall t1 : term, P t1 -> P (tLetIn n t t0 t1)) ->
    (forall t u : term, P t -> P u -> P (tApp t u)) ->
    (forall s (u : list Level.t), P (tConst s u)) ->
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
  intros until t. revert t.
  fix auxt 1.
  move auxt at top.
  destruct t; match goal with
                 H : _ |- _ => apply H
              end; auto.
  revert l.
  fix auxl' 1.
  destruct l; constructor; [|apply auxl'].
  apply auxt.
  revert brs.
  fix auxl' 1.
  destruct brs; constructor; [|apply auxl'].
  apply auxt.

  revert mfix.
  fix auxm 1.
  destruct mfix; constructor; [|apply auxm].
  split; apply auxt.
  revert mfix.
  fix auxm 1.
  destruct mfix; constructor; [|apply auxm].
  split; apply auxt.
Defined.


Inductive ForallT {A} (P : A -> Type) : list A -> Type :=
| ForallT_nil : ForallT P []
| ForallT_cons : forall (x : A) (l : list A), P x -> ForallT P l -> ForallT P (x :: l).

Definition tCaseBrsType {A} (P : A -> Type) (l : list (nat * A)) :=
  ForallT (fun x => P (snd x)) l.

Definition tFixType {A : Set} (P P' : A -> Type) (m : mfixpoint A) :=
  ForallT (fun x : def A => P x.(dtype) * P' x.(dbody))%type m.

Lemma size_decompose_app_rec t L :
  list_size size L + size t = size (decompose_app_rec t L).1 + list_size size (decompose_app_rec t L).2.
Proof.
  induction t in L |- *; cbn; try lia.
  rewrite <- IHt1. cbn. lia.
Qed.    

Lemma size_decompose_app t :
  size t = size (decompose_app t).1 + list_size size (decompose_app t).2.
Proof.
  unfold decompose_app.
  eapply (size_decompose_app_rec t []).
Qed.

Lemma decompose_app_rec_length_mono t L1 L2 :
  length L1 <= length L2 ->
  length (decompose_app_rec t L1).2 <= length (decompose_app_rec t L2).2.
Proof.
  intros. induction t in L1, L2, H |- *; cbn; try lia.
  eapply IHt1. cbn. lia.
Qed.

Lemma decompose_app_rec_length t L :
  length (decompose_app_rec t L).2 >= length L.
Proof.
  induction t in L |- * ; cbn; try lia.
  unfold ge. etransitivity. eapply IHt1.
  eapply decompose_app_rec_length_mono. cbn. lia.
Qed.

Lemma decompose_app_size_tApp1 t1 t2 :
  size (decompose_app (tApp t1 t2)).1 < size (tApp t1 t2).
Proof.
  rewrite size_decompose_app with (t := tApp t1 t2). cbn.
  pose proof (decompose_app_rec_length t1 [t2]). cbn in H.
  pose proof (list_size_length size (decompose_app_rec t1 [t2]).2).
  lia.
Qed.

Lemma decompose_app_size_tApp2 t1 t2 :
  Forall (fun t => size t < size (tApp t1 t2)) (decompose_app (tApp t1 t2)).2.
Proof.
  todo String.EmptyString.
Qed.

Definition mkApps_decompose_app_rec t l :
  mkApps t l = mkApps  (fst (decompose_app_rec t l)) (snd (decompose_app_rec t l)).
Proof.
  revert l; induction t; try reflexivity.
  intro l; cbn in *.
  transitivity (mkApps t1 ((t2 ::l))). reflexivity.
  now rewrite IHt1.
Qed.

Definition mkApps_decompose_app t :
  t = mkApps  (fst (decompose_app t)) (snd (decompose_app t))
  := mkApps_decompose_app_rec t [].

Lemma term_forall_mkApps_ind :
  forall P : term -> Type,
    (forall n : nat, P (tRel n)) ->
    (forall i : ident, P (tVar i)) ->
    (forall (n : nat) (l : list term), All P l -> P (tEvar n l)) ->
    (forall s, P (tSort s)) ->
    (forall (n : name) (t : term), P t -> forall t0 : term, P t0 -> P (tProd n t t0)) ->
    (forall (n : name) (t : term), P t -> forall t0 : term, P t0 -> P (tLambda n t t0)) ->
    (forall (n : name) (t : term),
        P t -> forall t0 : term, P t0 -> forall t1 : term, P t1 -> P (tLetIn n t t0 t1)) ->
    (forall t : term, forall v, ~ isApp t -> P t -> All P v -> P (mkApps t v)) ->
    (forall (s : kername) (u : list Level.t), P (tConst s u)) ->
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
  intros until t.
  assert (Acc (MR lt size) t) by eapply measure_wf, Wf_nat.lt_wf.
  induction H. rename X14 into auxt. clear H. rename x into t.
  move auxt at top.

  destruct t; try now repeat (match goal with
                 H : _ |- _ => apply H; try (hnf; cbn; lia)
              end).

  - eapply X1. revert l auxt. unfold MR; cbn. fix auxt' 1.
    destruct l; constructor. apply auxt. hnf; cbn; lia. apply auxt'. intros. apply auxt.
    hnf in *; cbn in *. lia. 

  - rewrite mkApps_decompose_app.
    destruct decompose_app eqn:E. cbn.
    eapply X6.
    + eapply decompose_app_notApp in E. eauto.
    + eapply auxt. cbn. hnf. pose proof (decompose_app_size_tApp1 t1 t2). rewrite E in *. hnf in *; cbn in *. lia.
    + pose proof (decompose_app_size_tApp2 t1 t2). rewrite E in *. cbn in H. clear E.
      induction l.
      * econstructor.
      * econstructor. eapply auxt. hnf; cbn. inv H. eassumption.
        eapply IHl. inv H. eassumption.
        
  - eapply X10; [apply auxt; hnf; cbn; lia.. | ]. rename brs into l.
    revert l auxt. unfold MR; cbn. fix auxt' 1.
    destruct l; constructor. apply auxt. hnf; cbn; lia. apply auxt'. intros. apply auxt.
    hnf in *; cbn in *. lia. 
  
  - eapply X12; [apply auxt; hnf; cbn; lia.. | ]. rename mfix into l.
    revert l auxt. unfold MR; cbn. fix auxt' 1.
    destruct l; constructor. split.
    apply auxt. hnf; cbn. unfold def_size. lia.
    apply auxt. hnf; cbn. unfold def_size. lia.   
    apply auxt'. intros. apply auxt.
    hnf in *; cbn in *. unfold mfixpoint_size, def_size in *. lia. 

  - eapply X13; [apply auxt; hnf; cbn; lia.. | ]. rename mfix into l.
    revert l auxt. unfold MR; cbn. fix auxt' 1.
    destruct l; constructor. split.
    apply auxt. hnf; cbn. unfold def_size. lia.
    apply auxt. hnf; cbn. unfold def_size. lia.   
    apply auxt'. intros. apply auxt.
    hnf in *; cbn in *. unfold mfixpoint_size, def_size in *. lia. 
Defined.
