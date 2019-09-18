(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmp" i*)

open Constr
open Quoted
open Quoter

module TemplateASTIdQuoter =
struct
  type t = Constr.t (* ? *)
  type quoted_ident = Id.t
  type quoted_int = int
  type quoted_bool = bool
  type quoted_name = Name.t
  type quoted_sort = Sorts.t
  type quoted_cast_kind = Constr.cast_kind
  type quoted_kernel_name = KerName.t
  type quoted_inductive = KerName.t * int
  type quoted_proj = quoted_inductive * int * int
  type quoted_global_reference = global_reference (* ? *)

  type quoted_sort_family = Sorts.family
  type quoted_constraint_type = Univ.constraint_type
  type quoted_univ_constraint = Univ.univ_constraint
  type quoted_univ_constraints = Univ.Constraint.t
  type quoted_univ_instance = Univ.Instance.t
  type quoted_univ_context = Univ.UContext.t
  type quoted_univ_contextset = Univ.ContextSet.t
  type quoted_abstract_univ_context = Univ.AUContext.t
  type quoted_variance = Univ.Variance.t
  type quoted_universes_decl = Universes0.universes_decl (* ? *)

  type quoted_mind_params = (Id.t * (t,t) sum) list (* ? *)
  type quoted_ind_entry = quoted_ident * t * quoted_bool * quoted_ident list * t list (* ? *)
  type quoted_definition_entry = t * t option * quoted_universes_decl (* ? *)
  type quoted_mind_entry = quoted_mind_finiteness * quoted_mind_params * quoted_ind_entry list * quoted_universes_decl
  type quoted_mind_finiteness = Declarations.recursivity_kind
  type quoted_entry = (quoted_definition_entry, quoted_mind_entry) sum option

  type quoted_context_decl = quoted_name * t option * t (* ? *)
  type quoted_context = quoted_context_decl list
  type quoted_one_inductive_body = one_inductive_body (* ? *)
  type quoted_mutual_inductive_body = mutual_inductive_body (* ? *)
  type quoted_constant_body = constant_body (* ? *)
  type quoted_global_decl = global_decl (* ? *)
  type quoted_global_env = global_env (* ? *)
  type quoted_program = program (* ? *)

  open Names

  let quote_ident id = id

  let quote_name name = name

  let quote_int i = i

  let quote_bool b = b

  let quote_level l = l

  let quote_universe s = s

  let quote_sort s = s

  let quote_sort_family s = s

  let quote_cast_kind k = k

  let quote_kn kn = kn
  let quote_inductive (kn, i) = (kn, i)
  let quote_proj ind p a = ((ind,p),a)

  let quote_constraint_type c = c

  let quote_univ_constraint ((l, ct, l')) = ((l, ct, l'))

  let quote_univ_instance (i : Univ.Instance.t) : quoted_univ_instance = i

  let quote_univ_constraints (c : Univ.Constraint.t) : quoted_univ_constraints = c

  let quote_variance (v : Univ.Variance.t) = v

  let quote_univ_context (uctx : Univ.UContext.t) : quoted_univ_context = uctx

  let quote_univ_contextset (uctx : Univ.ContextSet.t) : quoted_univ_contextset = uctx

  let quote_abstract_univ_context uctx = uctx

  let quote_context_decl na b t = (na, b, t)

  let quote_context l = l

  let mkAnon () = Name.Anonymous
  let mkName i = Name.Name i

  let mkRel n = Constr.Rel n
  let mkVar id = Constr.Var id
  let mkEvar n args = Constr.Evar (n,Array.to_list args)
  let mkSort s = Constr.Sort s
  let mkCast c k t = Constr.Cast (c,k,t)

  let mkConst c u = Constr.Const (c, u)
  let mkProd na t b = Constr.Prod (na, t, b)
  let mkLambda na t b = Constr.Lambda (na, t, b)
  let mkApp f xs = Constr.App (f, Array.to_list xs)
  let mkInd i u = Constr.Ind (i, u)
  let mkConstruct (ind, i) u = Constr.Construct (ind, i, u)
  let mkLetIn na b t t' = Constr.LetIn (na,b,t,t')

  let rec seq f t =
    if f < t then
      f :: seq (f + 1) t
    else []

  let mkFix ((a,b),(ns,ts,ds)) =
    let mk_fun xs i =
      { dname = Array.get ns i ;
        dtype = Array.get ts i ;
        dbody = Array.get ds i ;
        rarg = Array.get a i } :: xs
    in
    let defs = List.fold_left mk_fun [] (seq 0 (Array.length a)) in
    let block = List.rev defs in
    Coq_tFix (block, b)

  let mkCoFix (a,(ns,ts,ds)) =
    let mk_fun xs i =
      { dname = Array.get ns i ;
        dtype = Array.get ts i ;
        dbody = Array.get ds i ;
        rarg = Datatypes.O } :: xs
    in
    let defs = List.fold_left mk_fun [] (seq 0 (Array.length ns)) in
    let block = List.rev defs in
    Coq_tFix (block, a)

  let mkCase (ind, npar) nargs p c brs =
    let info = (ind, npar) in
    let branches = List.map2 (fun br nargs ->  (nargs, br)) brs nargs in
    Coq_tCase (info,p,c,branches)
  let mkProj p c = Coq_tProj (p,c)


  let mkMonomorphic_ctx tm = Universes0.Monomorphic_ctx tm 
  let mkPolymorphic_ctx tm = Universes0.Polymorphic_ctx tm 
  let mkCumulative_ctx tm var = Universes0.Cumulative_ctx (tm, var)


  let mk_one_inductive_body (id, ty, kel, ctr, proj) =
    let ctr = List.map (fun (a, b, c) -> ((a, b), c)) ctr in
    { ind_name = id; ind_type = ty;
      ind_kelim = kel; ind_ctors = ctr; ind_projs = proj }

  let mk_mutual_inductive_body finite npars params inds uctx =
    {ind_finite = finite;
     ind_npars = npars; ind_params = params; ind_bodies = inds; ind_universes = uctx}

  let mk_constant_body ty tm uctx =
    {cst_type = ty; cst_body = tm; cst_universes = uctx}

  let mk_inductive_decl kn bdy = InductiveDecl (kn, bdy)

  let mk_constant_decl kn bdy = ConstantDecl (kn, bdy)

  let empty_global_declartions () = []

  let add_global_decl a b = a :: b

  let mk_program decls tm = (decls, tm)

  let quote_mind_finiteness = function
    | Declarations.Finite -> Finite
    | Declarations.CoFinite -> CoFinite
    | Declarations.BiFinite -> BiFinite

  let quote_mind_params l =
    let map (id, body) =
      match body with
      | Left ty -> (id, LocalAssum ty)
      | Right trm -> (id, LocalDef trm)
    in List.map map l

  let quote_one_inductive_entry (id, ar, b, consnames, constypes) =
    { mind_entry_typename = id;
      mind_entry_arity = ar;
      mind_entry_template = b;
      mind_entry_consnames = consnames;
      mind_entry_lc = constypes }

  let quote_mutual_inductive_entry (mf, mp, is, univs) =
    { mind_entry_record = None;
      mind_entry_finite = mf;
      mind_entry_params = mp;
      mind_entry_inds = List.map quote_one_inductive_entry is;
      mind_entry_universes = univs;
      mind_entry_private = None }

  let quote_constant_entry (ty, body, ctx) : constant_entry =
    match body with
    | None -> ParameterEntry { parameter_entry_type = ty;
                               parameter_entry_universes = ctx }
    | Some b -> DefinitionEntry { definition_entry_type = ty;
                                  definition_entry_body = b;
                                  definition_entry_universes = ctx;
                                  definition_entry_opaque = false }

  let quote_entry e =
    match e with
    | Some (Left (ty, body, ctx)) ->
      Some (Left (quote_constant_entry (ty, body, ctx)))
    | Some (Right mind_entry) ->
       Some (Right mind_entry)
    | None -> None

  (* let inspectTerm (t : term) :  (term, quoted_int, quoted_ident, quoted_name, quoted_sort, quoted_cast_kind, quoted_kernel_name, quoted_inductive, quoted_univ_instance, quoted_proj) structure_of_term =
   match t with
  | Coq_tRel n -> ACoq_tRel n
    (* so on *)
  | _ ->  failwith "not yet implemented" *)




  (* let unquote_ident (qi: quoted_ident) : Id.t =
    let s = list_to_string qi in
    Id.of_string s

  let unquote_name (q: quoted_name) : Name.t =
    match q with
    | Coq_nAnon -> Anonymous
    | Coq_nNamed n -> Name (unquote_ident n)

  let rec unquote_int (q: quoted_int) : int =
    match q with
    | Datatypes.O -> 0
    | Datatypes.S x -> succ (unquote_int x)

  let unquote_bool (q : quoted_bool) : bool = q

  (* val unquote_sort : quoted_sort -> Sorts.t *)
  (* val unquote_sort_family : quoted_sort_family -> Sorts.family *)
  let unquote_cast_kind (q : quoted_cast_kind) : Constr.cast_kind =
    match q with
    | VmCast -> VMcast
    | NativeCast -> NATIVEcast
    | Cast -> DEFAULTcast
    | RevertCast -> REVERTcast

  let unquote_kn (q: quoted_kernel_name) : Libnames.qualid =
    let s = list_to_string q in
    Libnames.qualid_of_string s

  let unquote_inductive (q: quoted_inductive) : Names.inductive =
    let { inductive_mind = na; inductive_ind = i } = q in
    let comps = CString.split '.' (list_to_string na) in
    let comps = List.map Id.of_string comps in
    let id, dp = CList.sep_last comps in
    let dp = DirPath.make (List.rev dp) in
    let mind = Globnames.encode_mind dp id in
    (mind, unquote_int i)

  (*val unquote_univ_instance :  quoted_univ_instance -> Univ.Instance.t *)
  let unquote_proj (q : quoted_proj) : (quoted_inductive * quoted_int * quoted_int) =
    let (ind, ps), idx = q in
    (ind, ps, idx)

  let unquote_level (trm : Universes0.Level.t) : Univ.Level.t =
    match trm with
    | Universes0.Level.Coq_lProp -> Univ.Level.prop
    | Universes0.Level.Coq_lSet -> Univ.Level.set
    | Universes0.Level.Level s ->
      let s = list_to_string s in
      let comps = CString.split '.' s in
      let last, dp = CList.sep_last comps in
      let dp = DirPath.make (List.map Id.of_string comps) in
      let idx = int_of_string last in
      Univ.Level.make dp idx
    | Universes0.Level.Var n -> Univ.Level.var (unquote_int n)

  let unquote_level_expr (trm : Universes0.Level.t) (b : quoted_bool) : Univ.Universe.t =
    let l = unquote_level trm in
    let u = Univ.Universe.make l in
    if b && not (Univ.Level.is_prop l) then Univ.Universe.super u
    else u

  let unquote_universe evd (trm : Universes0.Universe.t) =
    (* | [] -> Evd.new_univ_variable (Evd.UnivFlexible false) evd *)
    let rec aux = function
      | Utils.NEL.Coq_sing (l,b) -> unquote_level_expr l b
      | Utils.NEL.Coq_cons ((l,b), q) -> Univ.Universe.sup (aux q) (unquote_level_expr l b)
    in evd, aux trm

  let quote_global_reference : Globnames.global_reference -> quoted_global_reference = function
    | Globnames.VarRef _ -> CErrors.user_err (Pp.str "VarRef unsupported")
    | Globnames.ConstRef c ->
      let kn = quote_kn (Names.Constant.canonical c) in
      BasicAst.ConstRef kn
    | Globnames.IndRef (i, n) ->
      let kn = quote_kn (Names.MutInd.canonical i) in
      let n = quote_int n in
      BasicAst.IndRef (quote_inductive (kn,n))
    | Globnames.ConstructRef ((i, n), k) ->
       let kn = quote_kn (Names.MutInd.canonical i) in
       let n = quote_int n in
       let k = (quote_int (k - 1)) in
       BasicAst.ConstructRef (quote_inductive (kn,n), k) *)
end

module TemplateASTIdReifier = Reify(TemplateASTIdQuoter)

include TemplateASTIdQuoter
include TemplateASTIdReifier
