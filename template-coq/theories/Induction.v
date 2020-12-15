(* Distributed under the terms of the MIT license. *)
From MetaCoq Require Import utils Ast AstUtils Environment.

(** * Deriving a compact induction principle for terms

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
    (forall (n : aname) (t : term), P t -> forall t0 : term, P t0 -> P (tProd n t t0)) ->
    (forall (n : aname) (t : term), P t -> forall t0 : term, P t0 -> P (tLambda n t t0)) ->
    (forall (n : aname) (t : term),
        P t -> forall t0 : term, P t0 -> forall t1 : term, P t1 -> P (tLetIn n t t0 t1)) ->
    (forall t : term, P t -> forall l : list term, Forall P l -> P (tApp t l)) ->
    (forall s (u : list Level.t), P (tConst s u)) ->
    (forall (i : inductive) (u : list Level.t), P (tInd i u)) ->
    (forall (i : inductive) (n : nat) (u : list Level.t), P (tConstruct i n u)) ->
    (forall (ci : case_info) (t : predicate term),
        tCasePredProp P P t -> forall t0 : term, P t0 -> forall l : list (branch term),
        tCaseBrsProp P l -> P (tCase ci t t0 l)) ->
    (forall (s : projection) (t : term), P t -> P (tProj s t)) ->
    (forall (m : mfixpoint term) (n : nat), tFixProp P P m -> P (tFix m n)) ->
    (forall (m : mfixpoint term) (n : nat), tFixProp P P m -> P (tCoFix m n)) ->
    (forall i, P (tInt i)) ->
    (forall f, P (tFloat f)) ->    
    forall t : term, P t.
Proof.
  intros until t. revert t.
  fix auxt 1.
  move auxt at top.
  destruct t;
    match goal with
      H : _ |- _ => apply H; auto
    end;
    try solve [match goal with
      |- _ P ?arg =>
      revert arg; fix aux_arg 1; intro arg;
        destruct arg; constructor; [|apply aux_arg];
          try split; apply auxt
    end].
  destruct type_info; split; cbn; [|now auto].
  revert pparams; fix aux_pparams 1.
  intros []; constructor; [apply auxt|apply aux_pparams].
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
    (forall (n : aname) (t : term), P t -> forall t0 : term, P t0 -> P (tProd n t t0)) ->
    (forall (n : aname) (t : term), P t -> forall t0 : term, P t0 -> P (tLambda n t t0)) ->
    (forall (n : aname) (t : term),
        P t -> forall t0 : term, P t0 -> forall t1 : term, P t1 -> P (tLetIn n t t0 t1)) ->
    (forall t : term, isApp t = false -> wf t -> P t ->
                      forall l : list term, l <> nil -> Forall wf l -> Forall P l -> P (tApp t l)) ->
    (forall s (u : list Level.t), P (tConst s u)) ->
    (forall (i : inductive) (u : list Level.t), P (tInd i u)) ->
    (forall (i : inductive) (n : nat) (u : list Level.t), P (tConstruct i n u)) ->
    (forall (ci : case_info) (p0 : predicate term),
        tCasePredProp P P p0 -> forall t : term, P t -> forall l : list (branch term),
        tCaseBrsProp P l -> P (tCase ci p0 t l)) ->
    (forall (s : projection) (t : term), P t -> P (tProj s t)) ->
    (forall (m : mfixpoint term) (n : nat), tFixProp P P m -> P (tFix m n)) ->
    (forall (m : mfixpoint term) (n : nat), tFixProp P P m -> P (tCoFix m n)) ->
    (forall i, P (tInt i)) ->
    (forall f, P (tFloat f)) ->
    forall t : term, wf t -> P t.
Proof.
  pose proof I as H1.   (* can go away, to avoid renaming everything... *)
  intros until t. revert t. rename H16 into H16'.
  apply (term_forall_list_ind (fun t => wf t -> P t));
    intros; try solve [match goal with
                 H : _ |- _ => apply H
              end; auto].
  apply H2. inv H18.
  auto using lift_to_wf_list.

  - inv H19; auto.
  - inv H19; auto.
  - inv H19; auto.
  - inv H20; auto.
  - inv H19; auto.
    apply H8; auto.
    auto using lift_to_wf_list.
    
  - destruct X.
    inv H18; apply H12; auto.
    + split; auto.
      apply Forall_All in H19.
      eapply All_mix in a; [|exact H19].
      eapply All_impl; eauto; cbn; intros; tauto.
    + apply Forall_All in H22.
      eapply All_mix in X0; [|exact H22].
      eapply All_impl; eauto; cbn; intros; tauto.

  - inv H18; auto.

  - inv H16; auto.
    apply H14. red. red in X.
    induction X; constructor.
    + split; inv H18; intuition.
    + apply IHX. now inv H18.

  - inv H16; auto.
    apply H15. red. red in X.
    induction X; constructor.
    + split; inv H18; intuition.
    + apply IHX. now inv H18.
Qed.

Definition tCaseBrsType {A} (P : A -> Type) (l : list (branch A)) :=
  All (fun x => P (bbody x)) l.

Definition tFixType {A} (P P' : A -> Type) (m : mfixpoint A) :=
  All (fun x : def A => P x.(dtype) * P' x.(dbody))%type m.

Lemma term_forall_list_rect :
  forall P : term -> Type,
    (forall n : nat, P (tRel n)) ->
    (forall i : ident, P (tVar i)) ->
    (forall (n : nat) (l : list term), All P l -> P (tEvar n l)) ->
    (forall s, P (tSort s)) ->
    (forall t : term, P t -> forall (c : cast_kind) (t0 : term), P t0 -> P (tCast t c t0)) ->
    (forall (n : aname) (t : term), P t -> forall t0 : term, P t0 -> P (tProd n t t0)) ->
    (forall (n : aname) (t : term), P t -> forall t0 : term, P t0 -> P (tLambda n t t0)) ->
    (forall (n : aname) (t : term),
        P t -> forall t0 : term, P t0 -> forall t1 : term, P t1 -> P (tLetIn n t t0 t1)) ->
    (forall t : term, P t -> forall l : list term, All P l -> P (tApp t l)) ->
    (forall s (u : list Level.t), P (tConst s u)) ->
    (forall (i : inductive) (u : list Level.t), P (tInd i u)) ->
    (forall (i : inductive) (n : nat) (u : list Level.t), P (tConstruct i n u)) ->
    (forall (ci : case_info) (p0 : predicate term),
        tCasePredProp P P p0 -> forall t : term, P t -> forall l : list (branch term),
        tCaseBrsType P l -> P (tCase ci p0 t l)) ->
    (forall (s : projection) (t : term), P t -> P (tProj s t)) ->
    (forall (m : mfixpoint term) (n : nat), tFixType P P m -> P (tFix m n)) ->
    (forall (m : mfixpoint term) (n : nat), tFixType P P m -> P (tCoFix m n)) ->
    (forall i, P (tInt i)) ->
    (forall f, P (tFloat f)) ->    
    forall t : term, P t.
Proof.
  intros until t. revert t.
  fix auxt 1.
  move auxt at top.
  destruct t;
    match goal with
      H : _ |- _ => apply H; auto
    end;
    try solve [match goal with
      |- _ P ?arg =>
      revert arg; fix aux_arg 1; intro arg;
        destruct arg; constructor; [|apply aux_arg];
          try split; apply auxt
    end].
  destruct type_info; split; cbn; [|now auto].
  revert pparams; fix aux_pparams 1.
  intros []; constructor; [apply auxt|apply aux_pparams].
Defined.
