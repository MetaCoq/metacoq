(* Distributed under the terms of the MIT license. *)
Require Import List.
From MetaCoq.Template Require Import utils BasicAst.
From MetaCoq.Erasure Require Import EAst.

(** * Deriving a compact induction principle for terms

  Allows to get the right induction principle on lists of terms appearing
  in the term syntax (in evar, applications, branches of cases and (co-)fixpoints. *)


(** Custom induction principle on syntax, dealing with the various lists appearing in terms. *)

Lemma term_forall_list_ind :
  forall P : term -> Type,
    (P tBox) ->
    (forall n : nat, P (tRel n)) ->
    (forall i : ident, P (tVar i)) ->
    (forall (n : nat) (l : list term), All P l -> P (tEvar n l)) ->
    (forall (n : name) (t : term), P t -> P (tLambda n t)) ->
    (forall (n : name) (t : term),
        P t -> forall t0 : term, P t0 -> P (tLetIn n t t0)) ->
    (forall t u : term, P t -> P u -> P (tApp t u)) ->
    (forall s, P (tConst s)) ->
    (forall (i : inductive) (n : nat), P (tConstruct i n)) ->
    (forall (p : inductive * nat) (t : term),
        P t -> forall l : list (list name * term),
        All (fun x => P x.2) l -> P (tCase p t l)) ->
    (forall (s : projection) (t : term), P t -> P (tProj s t)) ->
    (forall (m : mfixpoint term) (n : nat), All (fun x => P (dbody x)) m -> P (tFix m n)) ->
    (forall (m : mfixpoint term) (n : nat), All (fun x => P (dbody x)) m -> P (tCoFix m n)) ->
    (* (forall p, P (tPrim p)) -> *)
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
  revert l.
  fix auxl' 1.
  destruct l; constructor; [|apply auxl'].
  apply auxt.

  revert m.
  fix auxm 1.
  destruct m; constructor; [|apply auxm].
  apply auxt.

  revert m.
  fix auxm 1.
  destruct m; constructor; [|apply auxm].
  apply auxt.
Defined.

Ltac applyhyp :=
  match goal with
    H : _ |- _ => apply H
  end.

Class Hyp (T : Type) := hyp : T.
#[global]
Hint Extern 10 (Hyp _) => exactly_once multimatch goal with H : _ |- _
=> exact H end : typeclass_instances.
Class AHyp (T : Type) := ahyp : T.
#[global]
Hint Extern 10 (AHyp _) => multimatch goal with H : _ |- _
=> eapply H; shelve end : typeclass_instances.

Ltac inv H :=
  inversion_clear H ||
  match H with
  | @hyp _ ?X => inversion_clear X
  | @ahyp _ ?X => inversion_clear X
  end.
