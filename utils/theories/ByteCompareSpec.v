From Coq Require Import Strings.Byte NArith.
From MetaCoq.Template Require Import ReflectEq ByteCompare.
From Equations Require Import Equations.

Derive NoConfusion for comparison.

Section ByteNoConf.
  Local Ltac solve_noconf ::= idtac.
  Derive NoConfusion for byte.
  Next Obligation.
    destruct a; abstract (destruct b; try exact (False_ind _ H); exact eq_refl).
  Defined.
  Next Obligation.
    destruct b; cbn; exact I.
  Defined.
  Next Obligation.
    destruct a; abstract (destruct b; try (exact (False_ind _ e)); destruct e; exact eq_refl).
  Defined.
  Next Obligation.
    destruct b; cbn; exact eq_refl.
  Defined.
End ByteNoConf.

Lemma reflect_equiv P Q b : P <-> Q -> Bool.reflect P b -> Bool.reflect Q b.
Proof.
  intros eq r. destruct r.
  - now constructor; apply eq.
  - constructor. now rewrite <- eq.
Qed.

Require Import MCCompare.

Definition lt x y := compare x y = Lt.

Lemma compare_equiv x y : compare x y = N.compare (Byte.to_N x) (Byte.to_N y).
Proof.
  reflexivity.
Qed.
(*
Proof.
  destruct x; abstract (destruct y; exact eq_refl).
Qed. *)

Lemma compare_opp x y : compare x y = CompOpp (compare y x).
Proof.
  rewrite !compare_equiv.
  apply N.compare_antisym.
Qed.

Lemma compare_eq x y : compare x y = Eq -> x = y.
Proof.
  rewrite compare_equiv.
  intros Hcomp.
  eapply N.compare_eq in Hcomp.
  eapply (f_equal of_N) in Hcomp.
  rewrite !of_to_N in Hcomp. now noconf Hcomp.
Qed.

Lemma compare_spec x y : CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
Proof.
  destruct (compare x y) eqn:comp.
  - constructor. now apply compare_eq in comp.
  - constructor. exact comp.
  - constructor. red. now rewrite compare_opp, comp.
Qed.

From Coq Require Import Lia.

Lemma lt_trans x y z : lt x y -> lt y z -> lt x z.
Proof.
  unfold lt.
  rewrite !compare_equiv.
  rewrite !N.compare_lt_iff. lia.
Qed.

Lemma lt_not_eq x y : lt x y -> x <> y.
Proof.
  unfold lt.
  rewrite !compare_equiv.
  rewrite !N.compare_lt_iff. intros Hlt Heq. subst. lia.
Qed.

Lemma compare_eq_refl x : compare x x = Eq.
Proof.
  rewrite compare_equiv.
  eapply N.compare_refl.
Qed.

Definition eqb_compare x y : eqb x y = match compare x y with Eq => true | _ => false end.
Proof.
  unfold eqb.
  apply N.eqb_compare.
  (* destruct x; cbn; abstract (destruct y; cbn; exact eq_refl). *)
Qed.

Global Program Instance byte_reflect_eq : ReflectEq byte :=
  {| ReflectEq.eqb := eqb |}.
Next Obligation.
  rewrite eqb_compare.
  destruct (compare_spec x y); constructor; auto.
  all:apply lt_not_eq in H.
  - assumption.
  - now apply not_eq_sym.
Qed.
