open Names
open Datatypes
open Kernames
open BasicAst
open Ast0
open Ast0.Env
open Tm_util
open Caml_bytestring

module ExtractedASTBaseQuoter =
struct
  type t = Ast0.term
  type quoted_ident = Bytestring.String.t
  type quoted_int = Datatypes.nat
  type quoted_int63 = Uint63.t
  type quoted_float64 = Float64.t
  type quoted_bool = bool
  type quoted_name = BasicAst.name
  type quoted_aname = BasicAst.aname
  type quoted_relevance = BasicAst.relevance
  type quoted_sort = Universes0.Universe.t
  type quoted_cast_kind = cast_kind
  type quoted_kernel_name = Kernames.kername
  type quoted_inductive = inductive
  type quoted_proj = projection
  type quoted_global_reference = global_reference

  type quoted_sort_family = Universes0.allowed_eliminations
  type quoted_constraint_type = Universes0.ConstraintType.t
  type quoted_univ_constraint = Universes0.UnivConstraint.t
  type quoted_univ_constraints = Universes0.ConstraintSet.t
  type quoted_univ_instance = Universes0.Instance.t
  type quoted_univ_context = Universes0.UContext.t
  type quoted_univ_contextset = Universes0.ContextSet.t
  type quoted_abstract_univ_context = Universes0.AUContext.t
  type quoted_variance = Universes0.Variance.t
  type quoted_universes_decl = Universes0.universes_decl
  type quoted_universes_entry = Universes0.universes_entry

  type quoted_ind_entry = quoted_ident * t * quoted_ident list * t list
  type quoted_definition_entry = Ast0.definition_entry
  type quoted_parameter_entry = Ast0.parameter_entry
  type quoted_constant_entry = Ast0.constant_entry
  type quoted_mind_entry = mutual_inductive_entry
  type quoted_mind_finiteness = recursivity_kind
  type quoted_entry = (constant_entry, quoted_mind_entry) sum option

  type quoted_context_decl = Ast0.term context_decl
  type quoted_context = context
  type quoted_one_inductive_body = one_inductive_body
  type quoted_mutual_inductive_body = mutual_inductive_body
  type quoted_constant_body = constant_body
  type quoted_global_decl = global_decl
  type quoted_global_declarations = global_declarations
  type quoted_retroknowledge = Environment.Retroknowledge.t
  type quoted_global_env = global_env
  type quoted_program = program

  let quote_string = bytestring_of_caml_string
  let quote_ident id = quote_string (Id.to_string id)

  let quote_relevance = function
    | Sorts.Relevant -> BasicAst.Relevant
    | Sorts.Irrelevant -> BasicAst.Irrelevant

  let quote_name : Names.Name.t -> BasicAst.name = function
    | Anonymous -> Coq_nAnon
    | Name i -> Coq_nNamed (quote_ident i)

  let quote_aname ann_n =
    let {Context.binder_name = n; Context.binder_relevance = relevance} = ann_n in
    { BasicAst.binder_name = quote_name n; BasicAst.binder_relevance = quote_relevance relevance }

  let quote_int = Caml_nat.nat_of_caml_int
  let quote_bool x = x

  let quote_int63 x = x

  let quote_float64 x = x

  (* NOTE: fails if it hits Prop or SProp *)
  let quote_nonprop_level (l : Univ.Level.t) : Universes0.Level.t =
    if Univ.Level.is_set l then Universes0.Level.Coq_lzero
    else match Univ.Level.var_index l with
         | Some x -> Universes0.Level.Var (quote_int x)
         | None -> Universes0.Level.Level (quote_string (Univ.Level.to_string l))

  let quote_level (l : Univ.Level.t) : (Universes0.PropLevel.t, Universes0.Level.t) Datatypes.sum =
    try Coq_inr (quote_nonprop_level l)
    with e -> assert false

  let quote_universe s : Universes0.Universe.t =
    match Univ.Universe.level s with
      Some l -> Universes0.Universe.of_levels (quote_level l)
    | _ -> 
      let univs = List.map (fun (l,i) -> 
          match quote_level l with
          | Coq_inl lprop -> assert false
          | Coq_inr ql -> (ql, i > 0)) (Univ.Universe.repr s) in
      Universes0.Universe.from_kernel_repr (List.hd univs) (List.tl univs)

  let quote_sort s = match s with
  | Sorts.Set -> quote_universe Univ.Universe.type0
  | Sorts.SProp -> Universes0.Universe.of_levels (Coq_inl Universes0.PropLevel.Coq_lSProp)
  | Sorts.Prop -> Universes0.Universe.of_levels (Coq_inl Universes0.PropLevel.Coq_lProp)
  | Sorts.Type u -> quote_universe u

  let quote_sort_family s =
    match s with
    | Sorts.InSProp -> Universes0.IntoSProp
    | Sorts.InProp -> Universes0.IntoPropSProp
    | Sorts.InSet -> Universes0.IntoSetPropSProp
    | Sorts.InType -> Universes0.IntoAny

  let quote_cast_kind = function
    | Constr.DEFAULTcast -> Cast
    | Constr.NATIVEcast -> NativeCast
    | Constr.VMcast -> VmCast

  let quote_dirpath (dp : DirPath.t) : Kernames.dirpath =
    let l = DirPath.repr dp in
    List.map quote_ident l

  let rec quote_modpath (mp : ModPath.t) : Kernames.modpath =
    match mp with
    | MPfile dp -> MPfile (quote_dirpath dp)
    | MPbound mbid -> let (i, id, dp) = MBId.repr mbid in
      MPbound (quote_dirpath dp, quote_ident id, quote_int i)
    | MPdot (mp, id) -> MPdot (quote_modpath mp, quote_ident (Label.to_id id))

  let quote_kn (kn : KerName.t) : Kernames.kername =
    (quote_modpath (KerName.modpath kn),
     quote_ident (Label.to_id (KerName.label kn)))

  let quote_inductive (kn, i) = { inductive_mind = kn ; inductive_ind = i }
  let quote_proj ind p a = { proj_ind = ind; proj_npars = p; proj_arg = a }

  let quote_constraint_type = function
    | Univ.Lt -> Universes0.ConstraintType.Le BinNums.(Zpos Coq_xH)
    | Univ.Le -> Universes0.ConstraintType.Le BinNums.Z0
    | Univ.Eq -> Universes0.ConstraintType.Eq

  let is_Lt = function
    | Univ.Lt -> true
    | _ -> false

  let is_Le = function
    | Univ.Le -> true
    | _ -> false

  let is_Eq = function
    | Univ.Eq -> true
    | _ -> false

  let quote_univ_constraint ((l, ct, l') : Univ.univ_constraint) : quoted_univ_constraint =
    try ((quote_nonprop_level l, quote_constraint_type ct), quote_nonprop_level l')
    with e -> assert false

  let quote_univ_instance (i : Univ.Instance.t) : quoted_univ_instance =
    let arr = Univ.Instance.to_array i in
    (* we assume that valid instances do not contain [Prop] or [SProp] *)
    try CArray.map_to_list quote_nonprop_level arr
    with e -> assert false

   (* (Prop, Le | Lt, l),  (Prop, Eq, Prop) -- trivial, (l, c, Prop)  -- unsatisfiable  *)
  let rec constraints_ (cs : Univ.univ_constraint list) : quoted_univ_constraint list =
    match cs with
    | [] -> []
    | (l, ct, l') :: cs' ->
      quote_univ_constraint (l,ct,l') :: constraints_ cs'

  let quote_univ_constraints (c : Univ.Constraints.t) : quoted_univ_constraints =
    let l = constraints_ (Univ.Constraints.elements c) in
    Universes0.ConstraintSet.(List.fold_right add l empty)

  let quote_variance (v : Univ.Variance.t) =
    match v with
    | Univ.Variance.Irrelevant -> Universes0.Variance.Irrelevant
    | Univ.Variance.Covariant -> Universes0.Variance.Covariant
    | Univ.Variance.Invariant -> Universes0.Variance.Invariant

  let quote_univ_context (uctx : Univ.UContext.t) : quoted_univ_context =
    let names = CArray.map_to_list quote_name (Univ.UContext.names uctx)  in
    let levels = Univ.UContext.instance uctx  in
    let constraints = Univ.UContext.constraints uctx in
    (names, (quote_univ_instance levels, quote_univ_constraints constraints))

  let quote_univ_contextset (uctx : Univ.ContextSet.t) : quoted_univ_contextset =
    (* CHECKME: is is safe to assume that there will be no Prop or SProp? *)
    let levels = filter_map 
      (fun l -> match quote_level l with
        | Coq_inl _ -> None
        | Coq_inr l -> Some l)
      (Univ.Level.Set.elements (Univ.ContextSet.levels uctx)) in
    let constraints = Univ.ContextSet.constraints uctx in
    (Universes0.LevelSetProp.of_list levels, quote_univ_constraints constraints)

  let quote_abstract_univ_context uctx : quoted_abstract_univ_context =
    let names = Univ.AbstractContext.names uctx in
    let levels = CArray.map_to_list quote_name names in
    let constraints = Univ.UContext.constraints (Univ.AbstractContext.repr uctx) in
    (levels, quote_univ_constraints constraints)

  let quote_context_decl na b t =
    { decl_name = na;
      decl_body = b;
      decl_type = t }

  let quote_context l = l

  let mkAnon () = Coq_nAnon
  let mkName i = Coq_nNamed i

  let mkBindAnn nm r = { BasicAst.binder_name = nm; BasicAst.binder_relevance = r}

  let mkAAnon r = mkBindAnn mkAnon r
  let mkAName i r = mkBindAnn (mkName i) r

  (* let mkAAnon r = {BasicAst.binder_name = mkAnon; BasicAst.binder_relevance = r}
   * let mkAName i r = {BasicAst.binder_name = mkName i; BasicAst.binder_relevance = r} *)


  let mkRel n = Coq_tRel n
  let mkVar id = Coq_tVar id
  let mkEvar n args = Coq_tEvar (n,Array.to_list args)
  let mkSort s = Coq_tSort s
  let mkCast c k t = Coq_tCast (c,k,t)

  let mkConst c u = Coq_tConst (c, u)
  let mkProd na t b = Coq_tProd (na, t, b)
  let mkLambda na t b = Coq_tLambda (na, t, b)
  let mkApp f xs = Coq_tApp (f, Array.to_list xs)
  let mkInd i u = Coq_tInd (i, u)
  let mkConstruct (ind, i) u = Coq_tConstruct (ind, i, u)
  let mkLetIn na b t t' = Coq_tLetIn (na,b,t,t')
  let mkInt i = Coq_tInt i
  let mkFloat f = Coq_tFloat f

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
    Coq_tCoFix (block, a)

  let mkCase (ind, npar, r) (univs, pars, pctx, pret) c brs =
    let info = { ci_ind = ind; ci_npar = npar; ci_relevance = r } in
    let pred = { pparams = Array.to_list pars; 
                 puinst = univs; 
                 pcontext = List.rev (Array.to_list pctx);
                 preturn = pret } in
    let branches = List.map (fun (bctx, br) -> { bcontext = List.rev (Array.to_list bctx); bbody = br }) brs in
    Coq_tCase (info,pred,c,branches)

  let mkProj p c = Coq_tProj (p,c)


  let mkMonomorphic_ctx () = Universes0.Monomorphic_ctx
  let mkPolymorphic_ctx tm = Universes0.Polymorphic_ctx tm

  let mk_one_inductive_body (id, indices, sort, ty, kel, ctrs, projs, relevance) =
    let ctrs = List.map (fun (name, args, indices, ty, arity) -> 
      { cstr_name = name; 
        cstr_args = args;
        cstr_indices = indices;
        cstr_type = ty;
        cstr_arity = arity }) ctrs in
    let projs = List.map (fun (proj_name, proj_relevance, proj_type) -> 
        { proj_name; proj_relevance; proj_type }) projs in
    { ind_name = id; ind_type = ty;
      ind_indices = indices;
      ind_sort = sort;
      ind_kelim = kel; 
      ind_ctors = ctrs;
      ind_projs = projs; 
      ind_relevance = relevance }

  let mk_mutual_inductive_body finite npars params inds uctx variance =
    {ind_finite = finite;
     ind_npars = npars; ind_params = params; ind_bodies = inds;
     ind_universes = uctx; ind_variance = variance}

  let mk_constant_body ty tm uctx rel =
    {cst_type = ty; cst_body = tm; cst_universes = uctx; cst_relevance = rel}

  let mk_inductive_decl bdy = InductiveDecl bdy

  let mk_constant_decl bdy = ConstantDecl bdy

  let empty_global_declarations () = []

  let add_global_decl kn a b = (kn, a) :: b

  type pre_quoted_retroknowledge = 
    { retro_int63 : quoted_kernel_name option;
      retro_float64 : quoted_kernel_name option }

  let quote_retroknowledge r = 
    { Environment.Retroknowledge.retro_int63 = r.retro_int63; 
      Environment.Retroknowledge.retro_float64 = r.retro_float64 }

  let mk_global_env universes declarations retroknowledge = { universes; declarations; retroknowledge }
  let mk_program decls tm = (decls, tm)

  let quote_mind_finiteness = function
    | Declarations.Finite -> Finite
    | Declarations.CoFinite -> CoFinite
    | Declarations.BiFinite -> BiFinite

  let quote_one_inductive_entry (id, ar, consnames, constypes) =
    { mind_entry_typename = id;
      mind_entry_arity = ar;
      mind_entry_consnames = consnames;
      mind_entry_lc = constypes }

  let quote_mutual_inductive_entry (mf, mp, is, univs, variance) =
    { mind_entry_record = None;
      mind_entry_finite = mf;
      mind_entry_params = mp;
      mind_entry_inds = List.map quote_one_inductive_entry is;
      mind_entry_template = false;
      mind_entry_universes = univs;
      mind_entry_variance = variance;
      mind_entry_private = None }

  let quote_definition_entry ty body ctx =
    { definition_entry_type = ty;
      definition_entry_body = body;
      definition_entry_universes = ctx;
      definition_entry_opaque = false }

  let quote_parameter_entry ty ctx =
    { parameter_entry_type = ty;
      parameter_entry_universes = ctx }

  let quote_constant_entry = function
    | Left ce -> DefinitionEntry ce
    | Right pe -> ParameterEntry pe
(*
  let quote_entry e =
    match e with
    | Some (Left (ty, body, ctx)) ->
      Some (Left (quote_constant_entry (ty, body, ctx)))
    | Some (Right mind_entry) ->
       Some (Right mind_entry)
    | None -> None *)

  let inspectTerm (t : term) :  (term, quoted_int, quoted_ident, quoted_name, quoted_sort, quoted_cast_kind,
    quoted_kernel_name, quoted_inductive, quoted_relevance, quoted_univ_instance, quoted_proj, 
    quoted_int63, quoted_float64) structure_of_term =
   match t with
  | Coq_tRel n -> ACoq_tRel n
  (* todo ! *)
    (* so on *)
  | _ ->  failwith "not yet implemented"





  let quote_global_reference : GlobRef.t -> quoted_global_reference = function
    | GlobRef.VarRef id -> VarRef (quote_ident id)
    | GlobRef.ConstRef c ->
      let kn = quote_kn (Constant.canonical c) in
      ConstRef kn
    | GlobRef.IndRef (i, n) ->
      let kn = quote_kn (MutInd.canonical i) in
      let n = quote_int n in
      IndRef (quote_inductive (kn,n))
    | GlobRef.ConstructRef ((i, n), k) ->
       let kn = quote_kn (MutInd.canonical i) in
       let n = quote_int n in
       let k = (quote_int (k - 1)) in
       ConstructRef (quote_inductive (kn,n), k)

  let mkPolymorphic_entry c = Universes0.Polymorphic_entry c
  let mkMonomorphic_entry c = Universes0.Monomorphic_entry c

end

module ExtractedASTQuoter = Quoter.Quoter(ExtractedASTBaseQuoter)

include ExtractedASTBaseQuoter
include ExtractedASTQuoter
