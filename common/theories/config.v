(* Distributed under the terms of the MIT license. *)


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
