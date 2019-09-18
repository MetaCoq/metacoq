(* Distributed under the terms of the MIT license.   *)

From MetaCoq.Template Require Import utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils.
Require Import List Program.
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

Lemma term_forall_list_rec :
  forall P : term -> Type,
    (forall n : nat, P (tRel n)) ->
    (forall i : ident, P (tVar i)) ->
    (forall (n : nat) (l : list term), ForallT P l -> P (tEvar n l)) ->
    (forall s, P (tSort s)) ->
    (forall (n : name) (t : term), P t -> forall t0 : term, P t0 -> P (tProd n t t0)) ->
    (forall (n : name) (t : term), P t -> forall t0 : term, P t0 -> P (tLambda n t t0)) ->
    (forall (n : name) (t : term),
        P t -> forall t0 : term, P t0 -> forall t1 : term, P t1 -> P (tLetIn n t t0 t1)) ->
    (forall t u : term, P t -> P u -> P (tApp t u)) ->
    (forall (s : String.string) (u : list Level.t), P (tConst s u)) ->
    (forall (i : inductive) (u : list Level.t), P (tInd i u)) ->
    (forall (i : inductive) (n : nat) (u : list Level.t), P (tConstruct i n u)) ->
    (forall (p : inductive * nat) (t : term),
        P t -> forall t0 : term, P t0 -> forall l : list (nat * term),
            tCaseBrsType P l -> P (tCase p t t0 l)) ->
    (forall (s : projection) (t : term), P t -> P (tProj s t)) ->
    (forall (m : mfixpoint term) (n : nat), tFixType P P m -> P (tFix m n)) ->
    (forall (m : mfixpoint term) (n : nat), tFixType P P m -> P (tCoFix m n)) ->
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
