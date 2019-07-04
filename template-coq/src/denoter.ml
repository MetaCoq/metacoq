open Names
open Quoted

module type Denoter =
sig
  include Quoted

  val unquote_ident : quoted_ident -> Id.t
  val unquote_name : quoted_name -> Name.t
  val unquote_int :  quoted_int -> int
  val unquote_bool : quoted_bool -> bool
  (* val unquote_sort : quoted_sort -> Sorts.t *)
  (* val unquote_sort_family : quoted_sort_family -> Sorts.family *)
  val unquote_cast_kind : quoted_cast_kind -> Constr.cast_kind
  val unquote_kn :  quoted_kernel_name -> Libnames.qualid
  val unquote_inductive :  quoted_inductive -> Names.inductive
  (*val unquote_univ_instance :  quoted_univ_instance -> Univ.Instance.t *)
  val unquote_proj : quoted_proj -> (quoted_inductive * quoted_int * quoted_int)
  val unquote_universe : Evd.evar_map -> quoted_sort -> Evd.evar_map * Univ.Universe.t
  val unquote_universe_instance: Evd.evar_map -> quoted_univ_instance -> Evd.evar_map * Univ.Instance.t
  (* val representsIndConstuctor : quoted_inductive -> Term.constr -> bool *)
  val inspect_term : t -> (t, quoted_int, quoted_ident, quoted_name, quoted_sort, quoted_cast_kind, quoted_kernel_name, quoted_inductive, quoted_univ_instance, quoted_proj) structure_of_term

end
