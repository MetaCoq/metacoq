open Names
open Constr
open BasicAst
open Ast0
open Quoted
open Quoter
open Ast_quoter

module ExtractionDenoter =
struct
  type t = Ast0.term
  type quoted_ident = char list
  type quoted_int = Datatypes.nat
  type quoted_bool = bool
  type quoted_name = name
  type quoted_sort = Universes0.universe
  type quoted_cast_kind = cast_kind
  type quoted_kernel_name = char list
  type quoted_inductive = inductive
  type quoted_proj = projection
  type quoted_global_reference = global_reference

  type quoted_sort_family = Universes0.sort_family
  type quoted_constraint_type = Universes0.constraint_type
  type quoted_univ_constraint = Universes0.univ_constraint
  type quoted_univ_constraints = Universes0.constraints
  type quoted_univ_instance = Universes0.Instance.t
  type quoted_univ_context = Universes0.UContext.t
  type quoted_univ_contextset = Universes0.ContextSet.t
  type quoted_abstract_univ_context = Universes0.AUContext.t
  type quoted_variance = Universes0.Variance.t
  type quoted_universes_decl = Universes0.universes_decl

  type quoted_mind_params = (ident * local_entry) list
  type quoted_ind_entry = quoted_ident * t * quoted_bool * quoted_ident list * t list
  type quoted_definition_entry = t * t option * quoted_universes_decl
  type quoted_mind_entry = mutual_inductive_entry
  type quoted_mind_finiteness = recursivity_kind
  type quoted_entry = (constant_entry, quoted_mind_entry) sum option

  type quoted_context_decl = context_decl
  type quoted_context = context
  type quoted_one_inductive_body = one_inductive_body
  type quoted_mutual_inductive_body = mutual_inductive_body
  type quoted_constant_body = constant_body
  type quoted_global_decl = global_decl
  type quoted_global_env = global_env
  type quoted_program = program

  let mkAnon = mkAnon
  let mkName = mkName
  let quote_kn = quote_kn
  let mkRel = mkRel
  let mkVar = mkVar
  let mkEvar = mkEvar
  let mkSort = mkSort
  let mkCast = mkCast
  let mkConst = mkConst
  let mkProd = mkProd

  let mkLambda = mkLambda
  let mkApp = mkApp
  let mkLetIn = mkLetIn
  let mkFix = mkFix
  let mkConstruct = mkConstruct
  let mkCoFix = mkCoFix
  let mkInd = mkInd
  let mkCase = mkCase
  let quote_proj = quote_proj
  let mkProj = mkProj

  let unquote_def (x: 't BasicAst.def) : ('t, name, quoted_int) Quoted.adef =
    {
      adname=dname x;
      adtype=dtype x;
      adbody=dbody x;
      rarg=rarg x
    }

  let inspect_term (tt: t):(t, quoted_int, quoted_ident, quoted_name, quoted_sort, quoted_cast_kind, quoted_kernel_name, quoted_inductive, quoted_univ_instance, quoted_proj) structure_of_term=
    match tt with
    | Coq_tRel n -> ACoq_tRel n
    | Coq_tVar v -> ACoq_tVar v
    | Coq_tEvar (x,l) -> ACoq_tEvar (x,l)
    | Coq_tSort u -> ACoq_tSort u
    | Coq_tCast (t,k,tt) -> ACoq_tCast (t,k,tt)
    | Coq_tProd (a,b,c) -> ACoq_tProd (a,b,c)
    | Coq_tLambda (a,b,c) -> ACoq_tLambda (a,b,c)
    | Coq_tLetIn (a,b,c,d) -> ACoq_tLetIn (a,b,c,d)
    | Coq_tApp (a,b) -> ACoq_tApp (a,b)
    | Coq_tConst (a,b) -> ACoq_tConst (a,b)
    | Coq_tInd (a,b) -> ACoq_tInd (a,b)
    | Coq_tConstruct (a,b,c) -> ACoq_tConstruct (a,b,c)
    | Coq_tCase (a,b,c,d) -> ACoq_tCase (a,b,c,d)
    | Coq_tProj (a,b) -> ACoq_tProj (a,b)
    | Coq_tFix (a,b) -> ACoq_tFix (List.map unquote_def a,b)
    | Coq_tCoFix (a,b) -> ACoq_tCoFix (List.map unquote_def a,b)
    (*
    | Coq_tApp of term * term list
    | Coq_tConst of kername * universe_instance
    | Coq_tInd of inductive * universe_instance
    | Coq_tConstruct of inductive * nat * universe_instance
    | Coq_tCase of (inductive * nat) * term * term * (nat * term) list
    | Coq_tProj of projection * term
    | Coq_tFix of term mfixpoint * nat
    | Coq_tCoFix of term mfixpoint * nat
    *)

  let unquote_ident (qi: quoted_ident) : Id.t
  = Ast_quoter.unquote_ident qi

  let unquote_name (qn: quoted_name) : Name.t
  = Ast_quoter.unquote_name qn

  let unquote_int (q:  quoted_int) : int
  = Ast_quoter.unquote_int q

  let unquote_bool (q: quoted_bool) : bool
  = Ast_quoter.unquote_bool q

  let unquote_cast_kind (q: quoted_cast_kind ) : Constr.cast_kind
  = Ast_quoter.unquote_cast_kind q

  let unquote_kn (q:  quoted_kernel_name ) : Libnames.qualid
  = Ast_quoter.unquote_kn q

  let unquote_inductive (q:  quoted_inductive ) : Names.inductive
  = Ast_quoter.unquote_inductive q

  let unquote_proj (q: quoted_proj ) : (quoted_inductive * quoted_int * quoted_int)
  = Ast_quoter.unquote_proj q

  let unquote_universe (q: Evd.evar_map) (qs: quoted_sort): Evd.evar_map * Univ.Universe.t
  = Ast_quoter.unquote_universe q qs

  let unquote_universe_instance(evm: Evd.evar_map) (l: quoted_univ_instance): Evd.evar_map * Univ.Instance.t
  = (evm,  Univ.Instance.of_array (Array.of_list (List0.map unquote_level l)))


end

module  ExtractionDenote = Denote.Denote(ExtractionDenoter)
