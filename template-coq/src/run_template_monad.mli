val declare_inductive : Environ.env -> Evd.evar_map -> Constr.t -> unit

val run_template_program_rec :
    poly:bool ->
    ?intactic:bool ->
    (Environ.env * Evd.evar_map * Constr.t -> unit) ->
    Environ.env -> Evd.evar_map * Constr.t -> unit
