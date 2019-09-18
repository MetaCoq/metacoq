(* Distributed under the terms of the MIT license.   *)

From MetaCoq Require Import BasicAst Ast AstUtils.
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
  forall P : term -> Prop,
    (forall n : nat, P (tRel n)) ->
    (forall i : ident, P (tVar i)) ->
    (forall (n : nat) (l : list term), Forall P l -> P (tEvar n l)) ->
    (forall s, P (tSort s)) ->
    (forall t : term, P t -> forall (c : cast_kind) (t0 : term), P t0 -> P (tCast t c t0)) ->
    (forall (n : name) (t : term), P t -> forall t0 : term, P t0 -> P (tProd n t t0)) ->
    (forall (n : name) (t : term), P t -> forall t0 : term, P t0 -> P (tLambda n t t0)) ->
    (forall (n : name) (t : term),
        P t -> forall t0 : term, P t0 -> forall t1 : term, P t1 -> P (tLetIn n t t0 t1)) ->
    (forall t : term, P t -> forall l : list term, Forall P l -> P (tApp t l)) ->
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
  destruct t;
    match goal with
      H : _ |- _ => apply H; auto
    end;
    match goal with
      |- _ P ?arg =>
      revert arg; fix aux_arg 1; intro arg;
        destruct arg; constructor; [|apply aux_arg];
          try split; apply auxt
    end.
Defined.


Lemma lift_to_list (P : term -> Prop) : (forall t, wf t -> P t) -> forall l, Forall wf l -> Forall P l.
Proof.
  intros IH.
  fix lift_to_list 1.
  destruct l; constructor.
  apply IH. now inversion_clear H.
  apply lift_to_list. now inversion_clear H.
Defined.

Lemma lift_to_wf_list (P : term -> Prop) : forall l, Forall (fun t => wf t -> P t) l -> Forall wf l -> Forall P l.
Proof.
  induction 1. constructor.
  inversion_clear 1. specialize (IHForall H3).
  constructor; auto.
Qed.

Ltac inv H := inversion_clear H.
Lemma term_wf_forall_list_ind :
  forall P : term -> Prop,
    (forall n : nat, P (tRel n)) ->
    (forall i : ident, P (tVar i)) ->
    (forall (n : nat) (l : list term), Forall P l -> P (tEvar n l)) ->
    (forall s, P (tSort s)) ->
    (forall t : term, P t -> forall (c : cast_kind) (t0 : term), P t0 -> P (tCast t c t0)) ->
    (forall (n : name) (t : term), P t -> forall t0 : term, P t0 -> P (tProd n t t0)) ->
    (forall (n : name) (t : term), P t -> forall t0 : term, P t0 -> P (tLambda n t t0)) ->
    (forall (n : name) (t : term),
        P t -> forall t0 : term, P t0 -> forall t1 : term, P t1 -> P (tLetIn n t t0 t1)) ->
    (forall t : term, isApp t = false -> wf t -> P t ->
                      forall l : list term, l <> nil -> Forall wf l -> Forall P l -> P (tApp t l)) ->
    (forall (s : String.string) (u : list Level.t), P (tConst s u)) ->
    (forall (i : inductive) (u : list Level.t), P (tInd i u)) ->
    (forall (i : inductive) (n : nat) (u : list Level.t), P (tConstruct i n u)) ->
    (forall (p : inductive * nat) (t : term),
        P t -> forall t0 : term, P t0 -> forall l : list (nat * term),
            tCaseBrsProp P l -> P (tCase p t t0 l)) ->
    (forall (s : projection) (t : term), P t -> P (tProj s t)) ->
    (forall (m : mfixpoint term) (n : nat), tFixProp P P m -> Forall (fun def => isLambda (dbody def) = true) m -> P (tFix m n)) ->
    (forall (m : mfixpoint term) (n : nat), tFixProp P P m -> P (tCoFix m n)) ->
    forall t : term, wf t -> P t.
Proof.
  pose proof I as H1.  (* can go away, to avoid renaming everything... *)
  intros until t. revert t.
  apply (term_forall_list_ind (fun t => wf t -> P t));
    intros; try solve [match goal with
                 H : _ |- _ => apply H
              end; auto].
  apply H2. inv H17.
  auto using lift_to_wf_list.

  inv H18; auto.
  inv H18; auto.
  inv H18; auto.
  inv H19; auto.
  inv H18; auto.

  apply H8; auto.
  auto using lift_to_wf_list.

  inv H19; apply H12; auto.
  red.
  red in H18.
  induction H18.
  constructor.
  inv H22; auto.

  inv H17; auto.

  inv H17; auto.
  apply H14. red.
  red in H16.
  induction H16. constructor.
  inv H18; constructor; intuition auto.
  clear H16; induction H18; constructor; intuition auto.

  inv H17; auto.
  apply H15. red.
  red in H16.
  induction H16. constructor.
  inv H18; constructor; intuition auto.
Qed.
