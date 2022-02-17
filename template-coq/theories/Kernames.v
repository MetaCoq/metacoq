
(* Distributed under the terms of the MIT license. *)
From Coq Require Import Lia MSetList OrderedTypeAlt OrderedTypeEx Ascii String.
From MetaCoq.Template Require Import MCUtils BasicAst AstUtils.
From Coq Require Import ssreflect.

Definition compare_ident := string_compare.

Module IdentOT := StringOT.

Module DirPathOT := ListOrderedType IdentOT.
  
(* Eval compute in DirPathOT.compare ["foo"; "bar"] ["baz"].
 *)

Module ModPathComp.
  Definition t := modpath.

  Definition eq := @eq modpath.
  Definition eq_univ : RelationClasses.Equivalence eq := _.

  Definition mpbound_compare dp id k dp' id' k' :=
    compare_cont (DirPathOT.compare dp dp')
      (compare_cont (IdentOT.compare id id') (Nat.compare k k')).

  Fixpoint compare mp mp' :=
    match mp, mp' with
    | MPfile dp, MPfile dp' => DirPathOT.compare dp dp'
    | MPbound dp id k, MPbound dp' id' k' => 
      mpbound_compare dp id k dp' id' k'
    | MPdot mp id, MPdot mp' id' => 
      compare_cont (compare mp mp') (IdentOT.compare id id')
    | MPfile _, _ => Gt
    | _, MPfile _ => Lt
    | MPbound _ _ _, _ => Gt
    | _, MPbound _ _ _ => Lt
    end.

  Infix "?=" := compare (at level 70, no associativity).

  Lemma nat_compare_sym : forall x y, Nat.compare x y = CompOpp (Nat.compare y x).
  Proof.
    intros; apply PeanoNat.Nat.compare_antisym.
  Qed.

  Lemma compare_eq x y : x ?= y = Eq -> x = y.
  Proof.
    induction x in y |- *; destruct y; simpl; auto; try congruence.
    intros c. eapply DirPathOT.compare_eq in c; now subst.
    unfold mpbound_compare.
    destruct (DirPathOT.compare dp dp0) eqn:eq => //.
    destruct (IdentOT.compare id id0) eqn:eq' => //.
    destruct (Nat.compare i i0) eqn:eq'' => //.
    apply DirPathOT.compare_eq in eq.
    apply string_compare_eq in eq'.
    apply PeanoNat.Nat.compare_eq in eq''. congruence.
    destruct (x ?= y) eqn:eq; try congruence.
    specialize (IHx _ eq). subst.
    now intros c; apply string_compare_eq in c; subst.
    all:simpl; discriminate.
  Qed.

  Lemma compare_sym : forall x y, (y ?= x) = CompOpp (x ?= y).
  Proof.
    induction x; destruct y; simpl; auto.
    apply DirPathOT.compare_sym.
    unfold mpbound_compare.
    rewrite DirPathOT.compare_sym.
    rewrite IdentOT.compare_sym.
    destruct (DirPathOT.compare dp dp0); auto.
    simpl. destruct (IdentOT.compare id id0); simpl; auto.
    apply nat_compare_sym.
    rewrite IHx.
    destruct (x ?= y); simpl; auto.
    apply IdentOT.compare_sym.
  Qed.
 
  Lemma nat_compare_trans :
    forall c x y z, Nat.compare x y = c -> Nat.compare y z = c -> Nat.compare x z = c.
  Proof.
    intros c x y z.
    destruct (PeanoNat.Nat.compare_spec x y); subst; intros <-;
    destruct (PeanoNat.Nat.compare_spec y z); subst; try congruence;
    destruct (PeanoNat.Nat.compare_spec x z); subst; try congruence; lia.
  Qed.
 
  Lemma compare_trans :
    forall c x y z, (x?=y) = c -> (y?=z) = c -> (x?=z) = c.
  Proof.
    intros c x y z. revert c.
    induction x in y, z |- *; destruct y, z; intros c; simpl; auto; try congruence.
    apply DirPathOT.compare_trans.
    unfold mpbound_compare.
    eapply compare_cont_trans; eauto using DirPathOT.compare_trans, DirPathOT.compare_eq.
    intros c'.
    eapply compare_cont_trans; eauto using StringOT.compare_trans, StringOT.compare_eq, nat_compare_trans.
    intros x y. apply StringOT.compare_eq.
    destruct (x ?= y) eqn:eq.
    apply compare_eq in eq. subst.
    destruct (IdentOT.compare id id0) eqn:eq.
    apply string_compare_eq in eq; red in eq; subst. all:intros <-; auto.
    destruct (y ?= z) eqn:eq'; auto.
    apply compare_eq in eq'; subst.
    intros eq'.
    eapply IdentOT.compare_trans; eauto. cbn in *.
    destruct (y ?= z) eqn:eq'; auto. cbn.
    now apply IdentOT.compare_trans.
    destruct (y ?= z) eqn:eq'; auto; cbn; try congruence.
    apply compare_eq in eq'; subst.
    intros eq'. now rewrite eq.
    rewrite (IHx _ _ _ eq eq') //.
    destruct (y ?= z) eqn:eq'; cbn; auto; try congruence.
    apply compare_eq in eq'; subst.
    intros eq'. now rewrite eq. 
    now rewrite (IHx _ _ _ eq eq').
  Qed.

End ModPathComp.

Module ModPathOT := OrderedType_from_Alt ModPathComp.

Module KernameComp.
  Definition t := kername.

  Definition eq := @eq kername.
  Lemma eq_equiv : RelationClasses.Equivalence eq.
  Proof. apply _. Qed.

  Definition compare kn kn' := 
    match kn, kn' with
    | (mp, id), (mp', id') => 
      compare_cont (ModPathComp.compare mp mp') (IdentOT.compare id id')
    end.

  Infix "?=" := compare (at level 70, no associativity).

  Lemma compare_sym : forall x y, (y ?= x) = CompOpp (x ?= y).
  Proof.
    induction x; destruct y; simpl; auto.
    unfold compare_ident.
    rewrite ModPathComp.compare_sym IdentOT.compare_sym.
    destruct ModPathComp.compare, IdentOT.compare; auto.
  Qed.
   
  Lemma compare_trans :
    forall c x y z, (x?=y) = c -> (y?=z) = c -> (x?=z) = c.
  Proof.
    intros c [] [] [] => /=.
    eapply compare_cont_trans; eauto using ModPathComp.compare_trans, ModPathComp.compare_eq, 
      StringOT.compare_trans.
  Qed.
    
End KernameComp.

Module KernameOT.
 Include KernameComp.
 Module OT := OrderedType_from_Alt KernameComp.

 Definition lt := OT.lt.
 Global Instance lt_strorder : StrictOrder OT.lt.
  Proof.
    constructor.
    - intros x X. apply OT.lt_not_eq in X. apply X. apply OT.eq_refl.
    - intros x y z X1 X2. eapply OT.lt_trans; eauto.
  Qed.

  Lemma lt_compat : Proper (eq ==> eq ==> iff) OT.lt.
  Proof.
    intros x x' H1 y y' H2.
    red in H1, H2. subst. reflexivity.
  Qed.

  Definition compare_spec : forall x y, CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
  Proof.
    induction x; destruct y.
    simpl. 
    destruct (ModPathComp.compare a m) eqn:eq.
    destruct (IdentOT.compare b i) eqn:eq'.
    all:constructor. red. eapply ModPathComp.compare_eq in eq. eapply string_compare_eq in eq'. congruence.
    all:hnf; simpl; rewrite ?eq ?eq' //.
    rewrite ModPathComp.compare_sym eq /= IdentOT.compare_sym eq' //.
    now rewrite ModPathComp.compare_sym eq /=.
  Defined.

  Lemma compare_eq x y : compare x y = Eq <-> x = y.
  Proof.
    split.
    - destruct (compare_spec x y); try congruence.
    - intros <-. destruct (compare_spec x x); auto.
      now apply irreflexivity in H.
      now apply irreflexivity in H.
  Qed.

  Definition eq_dec : forall x y, {eq x y} + {~ eq x y}.
  Proof.
    intros k k'. apply kername_eq_dec.
  Defined.

End KernameOT.

(* Local Open Scope string_scope.*)
(* Eval compute in KernameOT.compare (MPfile ["fdejrkjl"], "A") (MPfile ["lfrk;k"], "B"). *)
  
Module KernameSet := MSetAVL.Make KernameOT.
Module KernameSetFact := MSetFacts.WFactsOn KernameOT KernameSet.
Module KernameSetProp := MSetProperties.WPropertiesOn KernameOT KernameSet.

Lemma knset_in_fold_left {A} kn f (l : list A) acc : 
  KernameSet.In kn (fold_left (fun acc x => KernameSet.union (f x) acc) l acc) <->
  (KernameSet.In kn acc \/ exists a, In a l /\ KernameSet.In kn (f a)).
Proof.
  induction l in acc |- *; simpl.
  - split; auto. intros [H0|H0]; auto. now destruct H0.
  - rewrite IHl. rewrite KernameSet.union_spec.
    intuition auto.
    * right. now exists a; intuition auto.
    * destruct H0 as [a' [ina inkn]].
      right. now exists a'; intuition auto.
    * destruct H0 as [a' [ina inkn]].
      destruct ina as [<-|ina'];
      intuition auto. right. now exists a'.
Qed.
