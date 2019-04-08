open Univ
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
  val print_term : t -> Pp.std_ppcmds

  (* val representsIndConstuctor : quoted_inductive -> Term.constr -> bool *)
  val inspect_term : t -> (t, quoted_int, quoted_ident, quoted_name, quoted_sort, quoted_cast_kind, quoted_kernel_name, quoted_inductive, quoted_univ_instance, quoted_proj) structure_of_term

(*
  val quote_ident : quoted_ident -> Id.t
  val quote_name : quoted_name -> Name.t
  val quote_int : quoted_int -> int
  val quote_bool : quoted_bool -> bool
  val quote_sort : quoted_sort -> Sorts.t
  val quote_sort_family : quoted_sort_family -> Sorts.family
  val quote_cast_kind : quoted_cast_kind -> Constr.cast_kind
  val quote_kn : quoted_kernel_name -> KerName.t
  val quote_inductive : quoted_inductive -> quoted_kernel_name * quoted_int
  val quote_proj : quoted_proj -> (quoted_inductive * quoted_int * quoted_int)

  val quote_constraint_type : quoted_constraint_type -> Univ.constraint_type
  val quote_univ_constraint : quoted_univ_constraint -> Univ.univ_constraint
  val quote_univ_instance : quoted_univ_instance -> Univ.Instance.t
  val quote_univ_constraints : quoted_univ_constraints -> Univ.Constraint.t
  val quote_univ_context : quoted_univ_context -> Univ.UContext.t
  val quote_cumulative_univ_context : quoted_univ_context -> Univ.CumulativityInfo.t
  val quote_abstract_univ_context : quoted_univ_context -> Univ.AUContext.t
  val quote_inductive_universes : quoted_inductive_universes -> Entries.inductive_universes

  val quote_mind_params : quoted_mind_params -> (quoted_ident * (t,t) sum) list
  val quote_mind_finiteness : quoted_mind_finiteness -> Declarations.recursivity_kind
  val quote_mutual_inductive_entry :
    quoted_mind_entry ->
    (quoted_mind_finiteness * quoted_mind_params * quoted_ind_entry list *
     quoted_inductive_universes)

  val quote_entry : quoted_entry -> (quoted_definition_entry, quoted_mind_entry) sum option

  val quote_context_decl : quoted_context_decl -> (quoted_name * t option * t)
  val quote_context : quoted_context -> quoted_context_decl list

  val mk_one_inductive_body
    : quoted_one_inductive_body ->
      (quoted_ident * t (* ind type *) * quoted_sort_family list
       * (quoted_ident * t (* constr type *) * quoted_int) list
       * (quoted_ident * t (* projection type *)) list)

  val mk_mutual_inductive_body :
    quoted_mutual_inductive_body ->
    (  quoted_int (* number of params (no lets) *)
     * quoted_context (* parameters context with lets *)
     * quoted_one_inductive_body list
     * quoted_univ_context )

  val mk_constant_body : quoted_constant_body -> (quoted_univ_context * t (* type *) * t option (* body *))

  val mk_inductive_decl : quoted_global_decl -> (quoted_kernel_name * quoted_mutual_inductive_body)

  val mk_constant_decl : quoted_global_decl -> (quoted_kernel_name * quoted_constant_body)

  val empty_global_declartions : quoted_global_declarations
  val add_global_decl : quoted_global_declarations -> (quoted_global_decl * quoted_global_declarations)

  val mk_program : quoted_program -> (quoted_global_declarations * t)
*)

end
