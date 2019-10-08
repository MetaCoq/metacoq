(** Check reduction *)
MetaCoq Quote Recursively Definition ast := term.
MetaCoq Unquote Definition normal_form := ltac:(interp_red ast).

Definition normal_form' := Eval vm_compute in normal_form.
Print normal_form'.
Check convertible term normal_form.

(** Check typing *)
MetaCoq Unquote Definition inferred_type := ltac:(interp_infer ast).
Definition inferred_type' := Eval cbv delta in inferred_type.
Print inferred_type'.
Check convertible ltac:(term_type term) inferred_type.
