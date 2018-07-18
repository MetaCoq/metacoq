Class checker_flags := {
  (* check_guard : bool ; *)
  (* Checking universe constraints iff [true] *)
  check_univs : bool
}.

Local Instance default_checker_flags : checker_flags := {|
  check_univs := true
|}.

Local Instance type_in_type : checker_flags := {|
  check_univs := false
|}.