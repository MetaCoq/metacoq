type ('a,'b) sum =
  Left of 'a | Right of 'b

type ('term, 'name, 'nat) adef = { adname : 'name; adtype : 'term; adbody : 'term; rarg : 'nat }

type ('term, 'name, 'nat) amfixpoint = ('term, 'name, 'nat) adef list

type ('term, 'nat, 'ident, 'name, 'quoted_sort, 'cast_kind, 'kername, 'inductive, 'universe_instance, 'projection) structure_of_term =
  | ACoq_tRel of 'nat
  | ACoq_tVar of 'ident
  | ACoq_tMeta of 'nat
  | ACoq_tEvar of 'nat * 'term list
  | ACoq_tSort of 'quoted_sort
  | ACoq_tCast of 'term * 'cast_kind * 'term
  | ACoq_tProd of 'name * 'term * 'term
  | ACoq_tLambda of 'name * 'term * 'term
  | ACoq_tLetIn of 'name * 'term * 'term * 'term
  | ACoq_tApp of 'term * 'term list
  | ACoq_tConst of 'kername * 'universe_instance
  | ACoq_tInd of 'inductive * 'universe_instance
  | ACoq_tConstruct of 'inductive * 'nat * 'universe_instance
  | ACoq_tCase of ('inductive * 'nat) * 'term * 'term * ('nat * 'term) list
  | ACoq_tProj of 'projection * 'term
  | ACoq_tFix of ('term, 'name, 'nat) amfixpoint * 'nat
  | ACoq_tCoFix of ('term, 'name, 'nat) amfixpoint * 'nat

module type Quoter = sig
  type t

  type quoted_ident
  type quoted_int
  type quoted_bool
  type quoted_name
  type quoted_sort
  type quoted_cast_kind
  type quoted_kernel_name
  type quoted_inductive
  type quoted_decl
  type quoted_program
  type quoted_constraint_type
  type quoted_univ_constraint
  type quoted_univ_instance
  type quoted_univ_constraints
  type quoted_univ_context
  type quoted_mind_params
  type quoted_ind_entry =
    quoted_ident * t * quoted_bool * quoted_ident list * t list
  type quoted_definition_entry = t * t option
  type quoted_mind_entry
  type quoted_mind_finiteness
  type quoted_entry
  type quoted_proj
  type quoted_sort_family

  open Names

  val quote_ident : Id.t -> quoted_ident
  val quote_name : Name.t -> quoted_name
  val quote_int : int -> quoted_int
  val quote_bool : bool -> quoted_bool
  val quote_sort : Sorts.t -> quoted_sort
  val quote_sort_family : Sorts.family -> quoted_sort_family
  val quote_cast_kind : Constr.cast_kind -> quoted_cast_kind
  val quote_kn : kernel_name -> quoted_kernel_name
  val quote_inductive : quoted_kernel_name * quoted_int -> quoted_inductive
  val quote_constraint_type : Univ.constraint_type -> quoted_constraint_type
  val quote_univ_constraint : Univ.univ_constraint -> quoted_univ_constraint
  val quote_univ_instance : Univ.Instance.t -> quoted_univ_instance
  val quote_univ_constraints : Univ.Constraint.t -> quoted_univ_constraints
  val quote_univ_context : Univ.UContext.t -> quoted_univ_context
  val quote_abstract_univ_context : Univ.AUContext.t -> quoted_univ_context

  (* val quote_mind_params : (quoted_ident * (t,t) sum) list -> quoted_mind_params *)
  (* val quote_mind_finiteness : Decl_kinds.recursivity_kind -> quoted_mind_finiteness *)
  (* val quote_mutual_inductive_entry : *)
  (*   quoted_mind_finiteness * quoted_mind_params * quoted_ind_entry list * quoted_bool -> *)
  (*   quoted_mind_entry *)

  (* val quote_entry : (quoted_definition_entry, quoted_mind_entry) sum option -> quoted_entry *)
  val quote_proj : quoted_inductive -> quoted_int -> quoted_int -> quoted_proj

  val mkName : quoted_ident -> quoted_name
  val mkAnon : quoted_name

  val mkRel : quoted_int -> t
  val mkVar : quoted_ident -> t
  val mkMeta : quoted_int -> t
  val mkEvar : quoted_int -> t array -> t
  val mkSort : quoted_sort -> t
  val mkCast : t -> quoted_cast_kind -> t -> t
  val mkProd : quoted_name -> t -> t -> t
  val mkLambda : quoted_name -> t -> t -> t
  val mkLetIn : quoted_name -> t -> t -> t -> t
  val mkApp : t -> t array -> t
  val mkConst : quoted_kernel_name -> quoted_univ_instance -> t
  val mkInd : quoted_inductive -> quoted_univ_instance -> t
  val mkConstruct : quoted_inductive * quoted_int -> quoted_univ_instance -> t
  val mkCase : (quoted_inductive * quoted_int) -> quoted_int list -> t -> t ->
               t list -> t
  val mkProj : quoted_proj -> t -> t
  val mkFix : (quoted_int array * quoted_int) * (quoted_name array * t array * t array) -> t
  val mkCoFix : quoted_int * (quoted_name array * t array * t array) -> t

  val mkMutualInductive :
    quoted_kernel_name -> quoted_univ_context -> quoted_int (* params *) ->
    (quoted_ident * t (* ind type *) * quoted_sort_family list *
       (quoted_ident * t (* constr type *) * quoted_int) list *
         (quoted_ident * t (* projection type *)) list) list ->
     quoted_decl

  val mkConstant : quoted_kernel_name -> quoted_univ_context ->
                   t (* type *) -> t (* body *) -> quoted_decl
  val mkAxiom : quoted_kernel_name -> quoted_univ_context -> t -> quoted_decl

  val mkExt : quoted_decl -> quoted_program -> quoted_program
  val mkIn : t -> quoted_program
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
  
  (* val representsIndConstuctor : quoted_inductive -> Term.constr -> bool *)
  val inspectTerm : t -> (t, quoted_int, quoted_ident, quoted_name, quoted_sort, quoted_cast_kind, quoted_kernel_name, quoted_inductive, quoted_univ_instance, quoted_proj) structure_of_term
end

module Reify(Q : Quoter) : sig
  val quote_mind_decl : Environ.env -> Names.mutual_inductive -> Q.quoted_decl
  val quote_term : Environ.env -> Constr.t -> Q.t
  val quote_term_rec : Environ.env -> Constr.t -> Q.quoted_program
end
  
