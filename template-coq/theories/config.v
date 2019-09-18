Class checker_flags := {
  (* check_guard : bool ; *)

  (* Checking universe constraints iff [true] *)
  check_univs : bool ;

  (* Allow use of cofix iff [true] *)
  allow_cofix : bool ;

  (* Prop <= Type iff [true] *)
  prop_sub_type : bool
}.

(* Should correspond to Coq *)
Local Instance default_checker_flags : checker_flags := {|
  check_univs := true ;
  allow_cofix := true ;
  prop_sub_type := true
|}.

Local Instance type_in_type : checker_flags := {|
  check_univs := false ;
  allow_cofix := true ;
  prop_sub_type := true
|}.

Local Instance extraction_checker_flags : checker_flags := {|
  check_univs := true ;
  allow_cofix := false ;
  prop_sub_type := false
|}.
