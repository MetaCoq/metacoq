
(* Distributed under the terms of the MIT license. *)
From Coq Require Import Lia MSetList OrderedTypeAlt OrderedTypeEx Ascii String.
From MetaCoq.Template Require Import MCUtils BasicAst AstUtils.
From Coq Require Import ssreflect.

Definition compare_ident := string_compare.

Module IdentComp <: OrderedTypeAlt.
  Definition t := string.

  Definition eq := @eq string.
  Definition eq_univ : RelationClasses.Equivalence eq := _.

  Definition compare := string_compare.

  Infix "?=" := compare (at level 70, no associativity).

  Lemma compare_sym : forall x y, (y ?= x) = CompOpp (x ?= y).
  Proof.
    induction x; destruct y; simpl; auto;
    destruct (ascii_compare a0 a) eqn:eq.
    apply ascii_Compare_eq in eq; subst a0.
    destruct (ascii_compare a a) eqn:eq'.
    apply ascii_Compare_eq in eq'. apply IHx.
    pose proof (proj2 (ascii_Compare_eq a a) eq_refl). congruence.
    pose proof (proj2 (ascii_Compare_eq a a) eq_refl). congruence.
    apply ascii_compare_Lt in eq. now rewrite eq.
    apply ascii_compare_Lt in eq. now rewrite eq.
  Qed.

  Lemma compare_trans :
    forall c x y z, (x?=y) = c -> (y?=z) = c -> (x?=z) = c.
  Proof.
    intros c x y z. unfold compare.
    destruct (string_compare x y) eqn:eq => <-; auto.
    apply string_compare_eq in eq; subst; auto.
    now apply transitive_string_lt.
    rewrite <-string_compare_lt.
    apply string_compare_lt in eq. intros.
    apply string_compare_lt. eapply transitive_string_lt. eapply H. apply eq.
  Qed.

End IdentComp.

Module IdentOT := OrderedType_from_Alt IdentComp.

Module DirPathComp <: OrderedTypeAlt.
  Definition t := dirpath.

  Definition eq := @eq dirpath.
  Definition eq_univ : RelationClasses.Equivalence eq := _.

  Fixpoint compare dp dp' :=
    match dp, dp' with
    | hd :: tl, hd' :: tl' => 
      match IdentComp.compare hd hd' with
      | Eq => compare tl tl'
      | x => x
      end
    | [], [] => Eq
    | [], _ => Lt
    | _, [] => Gt
    end.

  Infix "?=" := compare (at level 70, no associativity).

  Lemma compare_eq : forall x y, (x ?= y) = Eq -> x = y.
  Proof.
    induction x; destruct y; simpl; auto; try congruence.
    destruct (IdentComp.compare a s) eqn:eq; try congruence.
    eapply string_compare_eq in eq; subst.
    intros; f_equal; eauto.
  Qed.

  Lemma compare_sym : forall x y, (y ?= x) = CompOpp (x ?= y).
  Proof.
    induction x; destruct y; simpl; auto.
    unfold compare_ident.
    rewrite IdentComp.compare_sym.
    destruct (IdentComp.compare a s); simpl; auto.
  Qed.
 
  Lemma compare_trans :
    forall c x y z, (x?=y) = c -> (y?=z) = c -> (x?=z) = c.
  Proof.
    intros c x y z. revert c.
    induction x in y, z |- *; destruct y, z; intros c; simpl; auto; try congruence.
    pose proof (IdentComp.compare_trans c a s s0).
    destruct (IdentComp.compare a s) eqn:eqc;
    destruct (IdentComp.compare s s0) eqn:eqc'; simpl; try congruence;
    try rewrite (IdentComp.compare_trans _ _ _ _ eqc eqc'); auto.
    now eapply IHx.
    intros Hc <-. apply string_compare_eq in eqc. subst.
    now rewrite eqc'.
    intros Hc <-. apply string_compare_eq in eqc. subst.
    now rewrite eqc'.
    intros Hc <-. apply string_compare_eq in eqc'. subst.
    now rewrite eqc.
    intros Hc <-. apply string_compare_eq in eqc'. subst.
    now rewrite eqc.
  Qed.

End DirPathComp.

Module DirPathOT := OrderedType_from_Alt DirPathComp.

(* Eval compute in DirPathComp.compare ["foo"; "bar"] ["baz"].
 *)

Module ModPathComp.
  Definition t := modpath.

  Definition eq := @eq modpath.
  Definition eq_univ : RelationClasses.Equivalence eq := _.

  Definition mpbound_compare dp id k dp' id' k' :=
    if DirPathComp.compare dp dp' is Eq then
      if IdentComp.compare id id' is Eq then
        Nat.compare k k'
      else IdentComp.compare id id'
    else DirPathComp.compare dp dp'.

  Fixpoint compare mp mp' :=
    match mp, mp' with
    | MPfile dp, MPfile dp' => DirPathComp.compare dp dp'
    | MPbound dp id k, MPbound dp' id' k' => 
      mpbound_compare dp id k dp' id' k'
    | MPdot mp id, MPdot mp' id' => 
      if compare mp mp' is Eq then
        IdentComp.compare id id'
      else compare mp mp'
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
    intros c. eapply DirPathComp.compare_eq in c; now subst.
    unfold mpbound_compare.
    destruct (DirPathComp.compare dp dp0) eqn:eq => //.
    destruct (IdentComp.compare id id0) eqn:eq' => //.
    destruct (Nat.compare i i0) eqn:eq'' => //.
    apply DirPathComp.compare_eq in eq.
    apply string_compare_eq in eq'.
    apply PeanoNat.Nat.compare_eq in eq''. congruence.
    destruct (x ?= y) eqn:eq; try congruence.
    specialize (IHx _ eq). subst.
    now intros c; apply string_compare_eq in c; subst.
  Qed.


  Lemma compare_sym : forall x y, (y ?= x) = CompOpp (x ?= y).
  Proof.
    induction x; destruct y; simpl; auto.
    apply DirPathComp.compare_sym.
    unfold mpbound_compare.
    rewrite DirPathComp.compare_sym.
    rewrite IdentComp.compare_sym.
    destruct (DirPathComp.compare dp dp0); auto.
    simpl. destruct (IdentComp.compare id id0); simpl; auto.
    apply nat_compare_sym.
    rewrite IHx.
    destruct (x ?= y); simpl; auto.
    apply IdentComp.compare_sym.
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
    apply DirPathComp.compare_trans.
    unfold mpbound_compare.
    pose proof (fun c => DirPathComp.compare_trans c dp dp0 dp1).
    destruct (DirPathComp.compare dp dp0) eqn:eq.
    eapply DirPathComp.compare_eq in eq. subst.
    destruct (DirPathComp.compare dp0 dp1) eqn:eq; try congruence.
    eapply DirPathComp.compare_eq in eq. subst.
    destruct (IdentComp.compare id id0) eqn:eq'.
    apply string_compare_eq in eq'. subst.
    destruct (IdentComp.compare id0 id1) eqn:eq'; auto.
    apply string_compare_eq in eq'. subst.
    apply nat_compare_trans. auto.
    intros <-.
    destruct (IdentComp.compare id0 id1) eqn:eq''; try congruence.
    apply string_compare_eq in eq''. subst.
    now rewrite eq'.
    now rewrite (IdentComp.compare_trans _ _ _ _ eq' eq'').
    intros <-.
    destruct (IdentComp.compare id0 id1) eqn:eq''; try congruence.
    apply string_compare_eq in eq''; subst.
    now rewrite eq'.
    now rewrite (IdentComp.compare_trans _ _ _ _ eq' eq'').
    intros <-.
    destruct (DirPathComp.compare dp0 dp1) eqn:eq'; [apply DirPathComp.compare_eq in eq'|..]; subst.
    now rewrite eq.
    intros _.
    now rewrite (DirPathComp.compare_trans _ _ _ _ eq eq').
    congruence.
    intros <-.
    destruct (DirPathComp.compare dp0 dp1) eqn:eq'; [apply DirPathComp.compare_eq in eq'|..]; subst.
    now rewrite eq. congruence.
    now rewrite (DirPathComp.compare_trans _ _ _ _ eq eq').
    destruct (x ?= y) eqn:eq.
    apply compare_eq in eq. subst.
    destruct (IdentComp.compare id id0) eqn:eq.
    apply string_compare_eq in eq; subst. all:intros <-; auto.
    destruct (y ?= z) eqn:eq'; auto.
    apply compare_eq in eq'; subst.
    intros eq'.
    eapply IdentComp.compare_trans; eauto.
    destruct (y ?= z) eqn:eq'; auto.
    apply compare_eq in eq'; subst.
    intros eq'.
    eapply IdentComp.compare_trans; eauto.
    destruct (y ?= z) eqn:eq'; auto.
    apply compare_eq in eq'; subst.
    intros eq'. now rewrite eq.
    now rewrite (IHx _ _ _ eq eq'). congruence.
    destruct (y ?= z) eqn:eq'; auto.
    apply compare_eq in eq'; subst.
    intros eq'. now rewrite eq. congruence.
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
      if ModPathComp.compare mp mp' is Eq then
        IdentComp.compare id id'
      else ModPathComp.compare mp mp'
    end.

  Infix "?=" := compare (at level 70, no associativity).

  Lemma compare_sym : forall x y, (y ?= x) = CompOpp (x ?= y).
  Proof.
    induction x; destruct y; simpl; auto.
    unfold compare_ident.
    rewrite ModPathComp.compare_sym IdentComp.compare_sym.
    destruct ModPathComp.compare, IdentComp.compare; auto.
  Qed.
   
  Lemma compare_trans :
    forall c x y z, (x?=y) = c -> (y?=z) = c -> (x?=z) = c.
  Proof.
    intros c [] [] [] => /=.
    destruct ModPathComp.compare eqn:eq.
    apply ModPathComp.compare_eq in eq. subst; auto.
    destruct IdentComp.compare eqn:eq'; auto.
    apply string_compare_eq in eq'; subst.
    all:intros <-; auto.
    destruct ModPathComp.compare; auto.
    eapply IdentComp.compare_trans; eauto.
    destruct ModPathComp.compare; auto.
    eapply IdentComp.compare_trans; eauto.
    destruct (ModPathComp.compare m0 m1) eqn:eq'; auto; try congruence.
    apply ModPathComp.compare_eq in eq'; subst. now rewrite eq.
    now rewrite (ModPathComp.compare_trans _ _ _ _ eq eq').
    destruct (ModPathComp.compare m0 m1) eqn:eq'; auto; try congruence.
    apply ModPathComp.compare_eq in eq'; subst. now rewrite eq.
    now rewrite (ModPathComp.compare_trans _ _ _ _ eq eq').
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
    destruct (IdentComp.compare b i) eqn:eq'.
    all:constructor. red. eapply ModPathComp.compare_eq in eq. eapply string_compare_eq in eq'. congruence.
    all:hnf; simpl; rewrite ?eq ?eq' //.
    rewrite ModPathComp.compare_sym eq /= IdentComp.compare_sym eq' //.
    now rewrite ModPathComp.compare_sym eq /=.
  Defined.

  Definition eq_dec : forall x y, {eq x y} + {~ eq x y}.
  Proof.
    intros k k'. apply kername_eq_dec.
  Defined.

End KernameOT.

(* Local Open Scope string_scope. *)
(* Eval compute in KernameOT.compare (MPfile ["fdejrkjl"], "A") (MPfile ["lfrk;k"], "B"). *)
  
Module KernameSet := MSetList.Make KernameOT.
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
