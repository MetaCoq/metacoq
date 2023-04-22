(* Distributed under the terms of the MIT license. *)
From Coq Require CRelationClasses.
From Coq Require Import Bool RelationClasses Btauto.
From Coq.ssr Require Import ssreflect ssrbool.

Class checker_flags := {
  (* check_guard : bool ; *)

  (* Checking universe constraints iff [true] *)
  check_univs : bool ;

  (* Prop <= Type iff [true] *)
  prop_sub_type : bool ;

  (* If sort of indices are taken in account for the sort of inductive types *)
  indices_matter : bool ;

  (* Lets in constructor types are allowed iff [true] *)
  lets_in_constructor_types : bool
}.

(** Should correspond to Coq *)
Local Instance default_checker_flags : checker_flags := {|
  check_univs := true ;
  prop_sub_type := true;
  indices_matter := false;
  lets_in_constructor_types := true
|}.

Local Instance type_in_type : checker_flags := {|
  check_univs := false ;
  prop_sub_type := true;
  indices_matter := false;
  lets_in_constructor_types := true
|}.

Local Instance extraction_checker_flags : checker_flags := {|
  check_univs := true ;
  prop_sub_type := false;
  indices_matter := false;
  lets_in_constructor_types := false
|}.

(** [cf1 -> cf2] means that typing under [cf1] implies typing under [cf2] *)
#[local] Definition impl (cf1 cf2 : checker_flags) : bool
  := implb cf2.(@check_univs) cf1.(@check_univs)
     && implb cf1.(@prop_sub_type) cf2.(@prop_sub_type)
     && implb cf2.(@indices_matter) cf1.(@indices_matter)
     && implb cf1.(@lets_in_constructor_types) cf2.(@lets_in_constructor_types).

#[local] Definition impl_reflb cf : impl cf cf = true.
Proof. rewrite /impl !implb_same ?orb_true_r //. Qed.
#[local] Definition impl_refl : Reflexive impl := impl_reflb.
#[local] Definition impl_crefl : CRelationClasses.Reflexive impl := impl_reflb.
#[local] Definition impl_trans : Transitive impl.
Proof.
  rewrite /impl => x y z; destruct x, y, z; cbn.
  rewrite !implb_orb.
  repeat match goal with
         | [ |- is_true (andb _ _) -> _ ] => move => /andP[]
         | [ |- is_true (orb _ _) -> _ ] => move => /orP[]
         | [ |- is_true (negb _) -> _ ] => let H := fresh in intro H; apply negbTE in H; subst => //=
         | [ |- is_true true -> _ ] => move => _
         | [ |- is_true false -> _ ] => move => //=
         | [ |- is_true ?x -> _ ] => is_var x; let H := fresh in intro H; cbv [is_true] in H; subst
         end.
  all: rewrite ?orb_true_l ?orb_true_r ?andb_false_l ?andb_false_r //.
Qed.
#[local] Definition impl_ctrans : CRelationClasses.Transitive impl := impl_trans.
#[global] Existing Instances
  impl_refl impl_crefl
  impl_trans impl_ctrans
| 100.
