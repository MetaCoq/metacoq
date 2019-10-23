(************************************************************************)
(* This file defines a number of hints for typeclass resolution, as well
   as few Ltac tactics.
 *)
(************************************************************************)

Require Import HoTT.

Set Universe Polymorphism.
Set Primitive Projections.

Existing Class eq. 

Ltac tc := typeclasses eauto with typeclass_instances.

Ltac resolve_eq := intros; 
                   progress (repeat (try reflexivity;
                   try eassumption;
                   cbn; try rewrite concat_refl;
                   try rewrite inv_inv;
                   try repeat eapply ap; 
                   try repeat eapply ap2)).

Hint Extern 100 (_ = _) => resolve_eq : typeclass_instances.

Hint Extern 10 (?e ?x = _ ) => eapply (ap e) : typeclass_instances.

Hint Extern 10 (?e ?x ?y = _ ) => eapply (ap2 e) : typeclass_instances.

Ltac clear_eq := cbn in *; repeat match goal with | [e: ?A = ?B |- _] => destruct e end.

Create HintDb equiv.
Hint Extern 0 (prod ?A ?B ) => split : typeclass_instances.

Hint Extern 0 unit => exact tt  : typeclass_instances.

Ltac etransitivity := refine (concat _ _).


Hint Extern 0 (e_inv' ?e (e_fun ?e ?x) = _ ) =>
etransitivity ; [exact (e_sect (e_fun e) x) | idtac ] : equiv.

Hint Extern 0 (e_fun ?e (e_inv' ?e ?x) = _ ) =>
etransitivity ; [exact (e_retr (e_fun e) x) | idtac ] : equiv.

Hint Extern 0 ((e_inv' ?e) ∘ (e_fun ?e) ?x = _ ) =>
etransitivity ; [exact (e_sect (e_fun e) x) | idtac ] : equiv.

Hint Extern 0 ((e_fun ?e) ∘ (e_inv' ?e) ?x = _ ) =>
etransitivity ; [exact (e_retr (e_fun e) x) | idtac ] : equiv.

Hint Extern 0 (e_inv (e_fun ?e) (e_fun ?e ?x) = _ ) =>
etransitivity ; [exact (e_sect (e_fun e) x) | idtac ] : equiv.

Hint Extern 0 (e_fun ?e (e_inv (e_fun ?e) ?x) = _ ) =>
etransitivity ; [exact (e_retr (e_fun e) x) | idtac ] : equiv.

Hint Extern 0 ((e_inv (e_fun ?e)) ∘ (e_fun ?e) ?x = _ ) =>
etransitivity ; [exact (e_sect (e_fun e) x) | idtac ] : equiv.

Hint Extern 0 ((e_fun ?e) ∘ (e_inv (e_fun ?e)) ?x = _ ) =>
etransitivity ; [exact (e_retr (e_fun e) x) | idtac ] : equiv.


Hint Extern 0 (?g (?f ?n) = _ ) =>
etransitivity ; [exact (e_sect f n) | idtac ] : equiv.

Hint Extern 0 (?f (?g ?n) = _ ) =>
etransitivity ; [exact (e_retr f n) | idtac ] : equiv.

Hint Extern 0 (_ = ?g (?f ?n)) => exact (e_sect f n)^ : equiv.

Hint Extern 0 (_ = ?f (?g ?n)) => exact (e_retr f n)^ : equiv.

Typeclasses Transparent e_inv'  univalent_transport. 
Hint Transparent e_inv'  univalent_transport. 
Hint Unfold e_inv'  univalent_transport. 

Ltac equiv_elim :=
  clear_eq;
  match goal with | [x: ?A |- _] => induction x; simpl; try typeclasses eauto with typeclass_instances end.

Hint Extern 0 => progress (cbn in *): typeclass_instances. 

Hint Extern 0 => eassumption : typeclass_instances. 

Tactic Notation "erefine" uconstr(c) := unshelve notypeclasses refine c.

Ltac change_eq_to_Logic_eq :=
  let e := fresh "e" in
  match goal with | |- ?X = ?Y =>
                    assert (e : Logic.eq X Y) ; [idtac | now destruct e]
  end.

Ltac solve_cons_eq pr :=
  first [ reflexivity |
          apply (ap pr); auto;  typeclasses eauto with equiv typeclass_instances |
          apply (ap2 pr); auto;  typeclasses eauto with equiv typeclass_instances |
          apply (ap3 pr); auto;  typeclasses eauto with equiv typeclass_instances  |
          apply (ap4 pr); auto;  typeclasses eauto with equiv typeclass_instances |
          apply (ap (pr _)); auto;  typeclasses eauto with equiv typeclass_instances |
          apply (ap2 (pr _)); auto;  typeclasses eauto with equiv typeclass_instances |
          apply (ap3 (pr _)); auto;  typeclasses eauto with equiv typeclass_instances  |
          apply (ap4 (pr _)); auto;  typeclasses eauto with equiv typeclass_instances |
          apply (ap (pr _ _)); auto;  typeclasses eauto with equiv typeclass_instances |
          apply (ap2 (pr _ _)); auto;  typeclasses eauto with equiv typeclass_instances |
          apply (ap3 (pr _ _)); auto;  typeclasses eauto with equiv typeclass_instances  |
          apply (ap4 (pr _ _)); auto;  typeclasses eauto with equiv typeclass_instances |
          apply (ap (pr _ _ _)); auto;  typeclasses eauto with equiv typeclass_instances |
          apply (ap2 (pr _ _ _)); auto;  typeclasses eauto with equiv typeclass_instances |
          apply (ap3 (pr _ _ _)); auto;  typeclasses eauto with equiv typeclass_instances  |
          apply (ap4 (pr _ _ _)); auto;  typeclasses eauto with equiv typeclass_instances |
          apply (ap (pr _ _ _ _)); auto;  typeclasses eauto with equiv typeclass_instances |
          apply (ap2 (pr _ _ _ _)); auto;  typeclasses eauto with equiv typeclass_instances |
          apply (ap3 (pr _ _ _ _)); auto;  typeclasses eauto with equiv typeclass_instances  |
          apply (ap4 (pr _ _ _ _)); auto;  typeclasses eauto with equiv typeclass_instances |
          apply (ap (fun a => pr a _)); auto;  typeclasses eauto with equiv typeclass_instances |
          apply (ap2 (fun a => pr a _)); auto;  typeclasses eauto with equiv typeclass_instances |
          apply (ap3 (fun a => pr a _)); auto;  typeclasses eauto with equiv typeclass_instances  |
          apply (ap4 (fun a => pr a _)); auto;  typeclasses eauto with equiv typeclass_instances  ].

Tactic Notation "apply_cons" uconstr(cons) :=
  match goal with
  | [ H : _, H' : _, H'' : _, H''' : _, H'''' : _, H''''' : _ |- _ ] =>
    exact (cons H H' H'' H''' H'''' H''''')
  | [ H : _, H' : _, H'' : _, H''' : _, H'''' : _ |- _ ] =>
    exact (cons H H' H'' H''' H'''')
  | [ H : _, H' : _, H'' : _, H''' : _ |- _ ] => exact (cons H H' H'' H''')
  | [ H : _, H' : _, H'' : _ |- _ ] => exact (cons H H' H'')
  | [ H : _, H' : _ |- _ ] => exact (cons H H')
  | [ H : _ |- _ ] => exact (cons H)
  | [ |- _ ] => exact cons
  end.

Tactic Notation "solve_section2" uconstr(pr1) uconstr(pr2) :=
  let l := fresh "l" in intro l; induction l ; cbn in *;  [ solve_cons_eq pr1 | solve_cons_eq pr2].

Tactic Notation "define_map2" constr(ty) uconstr(rec) uconstr(cons1) uconstr(cons2) :=
  first [ refine (rec (fun _ => _) _ _) | refine (rec (fun _ _ => _) _ _ _) | refine (rec (fun _ _ _ => _) _ _ _ _)];
  repeat (let l := fresh in
          intros l;
          first [apply univalent_transport in l |
                 idtac]); try clear dependent ty;
  [apply_cons cons1 | apply_cons cons2].

Tactic Notation "equiv_pind2" uconstr(rec) uconstr(pr1) uconstr(pr2) :=
  clear_eq; first [
  match goal with
    e : ?ty ≃ ?ty'  |- _ =>
  let e' := fresh in set (e' := Equiv_inverse e);
  unshelve refine (BuildEquiv _ _ _ (isequiv_adjointify _ _ _ _));
  [ define_map2 ty rec pr1 pr2 |
    define_map2 ty' rec pr1 pr2 |
    simpl; solve_section2 pr1 pr2 |
    simpl; solve_section2 pr1 pr2]
  end |
  match goal with
    e : forall _ _ , _ ≃ _  |- _ =>
  let e' := fresh in set (e' := fun a b => Equiv_inverse (e a b));
  unshelve refine (BuildEquiv _ _ _ (isequiv_adjointify _ _ _ _));
  [ define_map2 unit rec pr1 pr2 |
    define_map2 unit rec pr1 pr2 |
    simpl; solve_section2 pr1 pr2 |
    simpl; solve_section2 pr1 pr2]
  end].

Tactic Notation "solve_section3" uconstr(pr1) uconstr(pr2) uconstr(pr3) :=
  let l := fresh "l" in intro l; induction l; [ solve_cons_eq pr1 | solve_cons_eq pr2 | solve_cons_eq pr3].


Tactic Notation "define_map3" constr(ty) uconstr(rec) uconstr(cons1) uconstr(cons2) uconstr(cons3) :=
  first [ refine (rec (fun _ => _) _ _ _) | refine (rec (fun _ _ => _) _ _ _ _) | refine (rec (fun _ _ _ => _) _ _ _ _ _)];
  repeat (let l := fresh in
          intros l;
          first [apply univalent_transport in l |
                 idtac]); clear dependent ty ;
  [apply_cons cons1 | apply_cons cons2 | apply_cons cons3].


Tactic Notation "equiv_pind3" uconstr(rec) uconstr(pr1) uconstr(pr2) uconstr(pr3) :=
  clear_eq;
  match goal with e : ?ty ≃ ?ty'  |- _ =>
  let e' := fresh in set (e' := Equiv_inverse e);
  unshelve refine (BuildEquiv _ _ _ (isequiv_adjointify _ _ _ _));
  [ define_map3 ty rec pr1 pr2 pr3 |
    define_map3 ty' rec pr1 pr2 pr3|
    simpl; solve_section3 pr1 pr2 pr3 |
    simpl; solve_section3 pr1 pr2 pr3]
end.

Tactic Notation "solve_section" uconstr(pr1) :=
  let l := fresh "l" in intro l; induction l; solve_cons_eq pr1.

Tactic Notation "define_map" constr(ty) uconstr(rec) uconstr(cons1) :=
  first [ refine (rec (fun _ => _) _) | refine (rec (fun _ _ => _) _ _) | refine (rec (fun _ _ _ => _) _ _ _)];
  repeat (let l := fresh in
          intros l;
          first [apply univalent_transport in l |
                 idtac]); clear dependent ty;
  apply_cons cons1.

Tactic Notation "equiv_pind" uconstr(rec) uconstr(pr1) :=
  clear_eq;
  match goal with
    e : ?ty ≃ ?ty'  , e1 : ?ty1 ≃ ?ty1' |- _ =>
  let e' := fresh in set (e' := Equiv_inverse e);
  let e'' := fresh in set (e'' := Equiv_inverse e1);
  unshelve refine (BuildEquiv _ _ _ (isequiv_adjointify _ _ _ _));
  [ define_map ty rec pr1  |
    define_map ty' rec pr1 |
    simpl; solve_section pr1 |
    simpl; solve_section pr1 ]
  |  e : ?ty ≃ ?ty'  |- _ =>
  let e' := fresh in set (e' := Equiv_inverse e);
  unshelve refine (BuildEquiv _ _ _ (isequiv_adjointify _ _ _ _));
  [ define_map ty rec pr1  |
    define_map ty' rec pr1 |
    simpl; solve_section pr1 |
    simpl; solve_section pr1 ]
end.
