val declare_inductive : Environ.env -> Evd.evar_map -> Constr.t -> unit

val run_template_program_rec :
           ?intactic:bool ->
           (Environ.env * Evd.evar_map * Constr.t -> unit) ->
           Environ.env -> Evd.evar_map * Constr.t -> unit
