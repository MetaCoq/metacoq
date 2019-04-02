val unquote_pair : Constr.t -> Constr.t * Constr.t

val unquote_list : Constr.t -> Constr.t list

val unquote_bool : Constr.t -> bool

val unquote_ident : Constr.t -> Names.Id.t

val unquote_string : Constr.t -> string

(* ^^ above this is completely generic *)

val unquote_level : Evd.evar_map -> Constr.constr -> Evd.evar_map * Univ.Level.t

val unquote_universe_instance : Evd.evar_map -> Constr.constr -> Evd.evar_map * Univ.Instance.t

val map_evm : ('a -> 'b -> 'a * 'c) -> 'a -> 'b list -> 'a * 'c list

val denote_term : Evd.evar_map -> Constr.t -> Evd.evar_map * Constr.t
