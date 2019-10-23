(************************************************************************)
(* This file introduces the canonical equality type class and its default instance *)
(************************************************************************)

Require Import HoTT.

Set Universe Polymorphism.
Set Primitive Projections.
Set Polymorphic Inductive Cumulativity. 
Unset Universe Minimization ToSet.

Class Canonical_eq@{i} (A:Type@{i}) :=
  { can_eq : forall (x y : A), x = y -> x = y ;
    can_eq_refl : forall x, can_eq x x eq_refl = eq_refl }.

Definition Canonical_eq_gen A : Canonical_eq A :=
  {| can_eq := fun x y e => e ;
     can_eq_refl := fun x => eq_refl |}.

Arguments can_eq {_} _.
Arguments can_eq_refl {_}.

Instance Canonical_eq_Forall A (B: A -> Type) : Canonical_eq (forall x:A, B x) := Canonical_eq_gen _.



(* Lemmas about canonical equality *)

Definition can_eq_eq {A} (e :Canonical_eq A) : e.(can_eq) = fun x y e => e.
Proof.
  apply funext; intros x. apply funext; intros y. apply funext; intro E.
  destruct E. apply can_eq_refl. 
Defined. 


Definition Canonical_eq_eq A (e e':Canonical_eq A)
           (H : e.(can_eq) = e'.(can_eq)) :
  (transport_eq (fun X => X = _) H  (can_eq_eq e) = (can_eq_eq e')) ->
  e = e'.
Proof.
  destruct e, e'. cbn in *. destruct H. cbn.
  unfold can_eq_eq.
  intros H. apply ap_inv_equiv' in H. cbn in H. 
  assert (can_eq_refl0 = can_eq_refl1).
  apply funext. intro x. 
  pose (H' := apD10 H x). apply ap_inv_equiv' in H'.
  pose (H'' := apD10 H' x). apply ap_inv_equiv' in H''.
  exact (apD10 H'' eq_refl). 
  destruct X. reflexivity.
Defined. 

Definition Canonical_contr A (e :Canonical_eq A) : e = Canonical_eq_gen A.
Proof.
  unshelve eapply Canonical_eq_eq.
  apply can_eq_eq.
  cbn. rewrite transport_paths_l. rewrite inv_inv.
  unfold can_eq_eq. cbn. apply inverse. 
  pose (@e_sect _ _ _ (funext _ _  (fun (x y : A) (e0 : eq A x y) => e0) (fun (x y : A) (e0 : eq A x y) => e0)) eq_refl).
  etransitivity; try exact e0. clear e0. apply ap. apply funext. intros. cbn.
  pose (@e_sect _ _ _ (funext _ _  (fun (y : A) (e0 : eq A x y) => e0) (fun (y : A) (e0 : eq A x y) => e0)) eq_refl).
  etransitivity ; try apply e0. clear e0. apply ap. apply funext. intros y. cbn.
  pose (@e_sect _ _ _ (funext _ _  (fun (e0 : eq A x y) => e0) (fun (e0 : eq A x y) => e0)) eq_refl). 
  etransitivity; try apply e0. clear e0. apply ap. apply funext. intros e0. cbn.
  destruct e0. reflexivity.                  
Defined.

