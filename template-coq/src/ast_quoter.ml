open Names
open Datatypes
open BasicAst
open Ast0
open Tm_util

module ExtractedASTBaseQuoter =
struct
  type t = Ast0.term
  type quoted_ident = char list
  type quoted_int = Datatypes.nat
  type quoted_bool = bool
  type quoted_name = BasicAst.name
  type quoted_aname = BasicAst.aname
  type quoted_relevance = BasicAst.relevance
  type quoted_sort = Universes0.Universe.t
  type quoted_cast_kind = cast_kind
  type quoted_kernel_name = BasicAst.kername
  type quoted_inductive = inductive
  type quoted_proj = projection
  type quoted_global_reference = global_reference

  type quoted_sort_family = Universes0.sort_family
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

  type quoted_ind_entry = quoted_ident * t * quoted_bool * quoted_ident list * t list
  type quoted_definition_entry = Ast0.definition_entry
  type quoted_parameter_entry = Ast0.parameter_entry
  type quoted_constant_entry = Ast0.constant_entry
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

  let quote_ident id =
    string_to_list (Id.to_string id)

  let quote_relevance = function
    | Sorts.Relevant -> BasicAst.Relevant
    | Sorts.Irrelevant -> BasicAst.Irrelevant
 
  let quote_name = function
    | Anonymous -> Coq_nAnon
    | Name i -> Coq_nNamed (quote_ident i)

  let quote_aname ann_n =
    let {Context.binder_name = n; Context.binder_relevance = relevance} = ann_n in
    { BasicAst.binder_name = quote_name n; BasicAst.binder_relevance = quote_relevance relevance }

 let quote_int i =
    let rec aux acc i =
      if i < 0 then acc
      else aux (Datatypes.S acc) (i - 1)
    in aux Datatypes.O (i - 1)

  let quote_bool x = x

  (* NOTE: fails if it hits Prop or SProp *)
  let quote_nonprop_level (l : Univ.Level.t) : Universes0.Level.t =
    if Univ.Level.is_prop l || Univ.Level.is_sprop l then
      failwith "Prop or SProp found in levels"
    else if Univ.Level.is_set l then Universes0.Level.Coq_lSet
    else match Univ.Level.var_index l with
         | Some x -> Universes0.Level.Var (quote_int x)
         | None -> Universes0.Level.Level (string_to_list (Univ.Level.to_string l))

  let quote_level (l : Univ.Level.t) : (Universes0.PropLevel.t, Universes0.Level.t) Datatypes.sum =
    if Univ.Level.is_prop l then Coq_inl Universes0.PropLevel.Coq_lProp
    else if Univ.Level.is_sprop l then Coq_inl Universes0.PropLevel.Coq_lSProp
    else (* NOTE: in this branch we know that [l] is neither [SProp] nor [Prop]*)
      Coq_inr (quote_nonprop_level l)
    (* else if Univ.Level.is_set l then Coq_inr Universes0.Level.Coq_lSet
     * else let l' = match Univ.Level.var_index l with
     *         | Some x -> Universes0.Level.Var (quote_int x)
     *         | None -> Universes0.Level.Level (string_to_list (Univ.Level.to_string l))
     *      in Coq_inr l' *)

  let quote_universe s : Universes0.Universe.t =
    match Univ.Universe.level s with
      Some l -> Universes0.Universe.of_levels (quote_level l)
    | _ -> let univs =
          Univ.Universe.map (fun (l,i) -> (quote_nonprop_level l, i > 0)) s in
    Universes0.Universe.from_kernel_repr (List.hd univs) (List.tl univs)

  let quote_sort s =
    quote_universe (Sorts.univ_of_sort s)

  let quote_sort_family s =
    match s with
    | Sorts.InProp -> Universes0.InProp
    | Sorts.InSet -> Universes0.InSet
    | Sorts.InType -> Universes0.InType
    | Sorts.InSProp -> Universes0.InProp (* FIXME "SProp sort not supported" *)

  let quote_cast_kind = function
    | Constr.DEFAULTcast -> Cast
    | Constr.REVERTcast -> RevertCast
    | Constr.NATIVEcast -> NativeCast
    | Constr.VMcast -> VmCast


  let quote_dirpath (dp : DirPath.t) : BasicAst.dirpath =
    let l = DirPath.repr dp in
    List.map quote_ident l

  let rec quote_modpath (mp : ModPath.t) : BasicAst.modpath =
    match mp with
    | MPfile dp -> MPfile (quote_dirpath dp)
    | MPbound mbid -> let (i, id, dp) = MBId.repr mbid in
      MPbound (quote_dirpath dp, quote_ident id, quote_int i)
    | MPdot (mp, id) -> MPdot (quote_modpath mp, quote_ident (Label.to_id id))

  let quote_kn (kn : KerName.t) : BasicAst.kername =
    (quote_modpath (KerName.modpath kn),
     quote_ident (Label.to_id (KerName.label kn)))

  let quote_inductive (kn, i) = { inductive_mind = kn ; inductive_ind = i }
  let quote_proj ind p a = ((ind,p),a)

  let quote_constraint_type = function
    | Univ.Lt -> Universes0.ConstraintType.Le 1
    | Univ.Le -> Universes0.ConstraintType.Le 0
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
    ((quote_nonprop_level l, quote_constraint_type ct), quote_nonprop_level l')

  let quote_univ_instance (i : Univ.Instance.t) : quoted_univ_instance =
    let arr = Univ.Instance.to_array i in
    (* we assume that valid instances do not contain [Prop] or [SProp] *)
    CArray.map_to_list quote_nonprop_level arr

   (* (Prop, Le | Lt, l),  (Prop, Eq, Prop) -- trivial, (l, c, Prop)  -- unsatisfiable  *)
  let rec constraints_ (cs : Univ.univ_constraint list) : quoted_univ_constraint list =
    match cs with
    | [] -> []
    | (l, ct, l') :: cs' ->
       if (* ignore trivial constraints *)
         (Univ.Level.is_prop l && (is_Le ct || is_Lt ct)) ||
          (Univ.Level.is_prop l && is_Eq ct && Univ.Level.is_prop l')
       then constraints_ cs'
       else if (* fail on unisatisfiable ones -- well-typed term is expected *)
         Univ.Level.is_prop l' then failwith "Unsatisfiable constraint (l <= Prop)"
       else (* NOTE:SPROP: we don't expect SProp to be in the constraint set *)
         quote_univ_constraint (l,ct,l') :: constraints_ cs'

  let quote_univ_constraints (c : Univ.Constraint.t) : quoted_univ_constraints =
    let l = constraints_ (Univ.Constraint.elements c) in
    Universes0.ConstraintSet.(List.fold_right add l empty)

  let quote_variance (v : Univ.Variance.t) =
    match v with
    | Univ.Variance.Irrelevant -> Universes0.Variance.Irrelevant
    | Univ.Variance.Covariant -> Universes0.Variance.Covariant
    | Univ.Variance.Invariant -> Universes0.Variance.Invariant

  let quote_univ_context (uctx : Univ.UContext.t) : quoted_univ_context =
    let levels = Univ.UContext.instance uctx  in
    let constraints = Univ.UContext.constraints uctx in
    (quote_univ_instance levels, quote_univ_constraints constraints)

  let quote_univ_contextset (uctx : Univ.ContextSet.t) : quoted_univ_contextset =
    (* CHECKME: is is safe to assume that there will be no Prop or SProp? *)
    let levels = List.map quote_nonprop_level (Univ.LSet.elements (Univ.ContextSet.levels uctx)) in
    let constraints = Univ.ContextSet.constraints uctx in
    (Universes0.LevelSetProp.of_list levels, quote_univ_constraints constraints)

  let quote_abstract_univ_context uctx =
    let names = Univ.AUContext.names uctx in
    let levels = CArray.map_to_list quote_name names in
    let constraints = Univ.UContext.constraints (Univ.AUContext.repr uctx) in
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

  let mkCase (ind, npar, r) nargs p c brs =
    let info = ((ind, npar), r) in
    let branches = List.map2 (fun br nargs ->  (nargs, br)) brs nargs in
    Coq_tCase (info,p,c,branches)
  let mkProj p c = Coq_tProj (p,c)


  let mkMonomorphic_ctx tm = Universes0.Monomorphic_ctx tm
  let mkPolymorphic_ctx tm = Universes0.Polymorphic_ctx tm

  let mk_one_inductive_body (id, ty, kel, ctr, proj, relevance) =
    let ctr = List.map (fun (a, b, c) -> ((a, b), c)) ctr in
    { ind_name = id; ind_type = ty;
      ind_kelim = kel; ind_ctors = ctr;
      ind_projs = proj; ind_relevance = relevance }

  let mk_mutual_inductive_body finite npars params inds uctx variance =
    {ind_finite = finite;
     ind_npars = npars; ind_params = params; ind_bodies = inds; 
     ind_universes = uctx; ind_variance = variance}

  let mk_constant_body ty tm uctx =
    {cst_type = ty; cst_body = tm; cst_universes = uctx}

  let mk_inductive_decl bdy = InductiveDecl bdy

  let mk_constant_decl bdy = ConstantDecl bdy

  let empty_global_declarations () = []

  let add_global_decl kn a b = (kn, a) :: b

  let mk_program decls tm = (decls, tm)

  let quote_mind_finiteness = function
    | Declarations.Finite -> Finite
    | Declarations.CoFinite -> CoFinite
    | Declarations.BiFinite -> BiFinite

  let quote_one_inductive_entry (id, ar, b, consnames, constypes) =
    { mind_entry_typename = id;
      mind_entry_arity = ar;
      mind_entry_template = b;
      mind_entry_consnames = consnames;
      mind_entry_lc = constypes }

  let quote_mutual_inductive_entry (mf, mp, is, univs, variance) =
    { mind_entry_record = None;
      mind_entry_finite = mf;
      mind_entry_params = mp;
      mind_entry_inds = List.map quote_one_inductive_entry is;
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

  let inspectTerm (t : term) :  (term, quoted_int, quoted_ident, quoted_name, quoted_sort, quoted_cast_kind, quoted_kernel_name, quoted_inductive, quoted_relevance, quoted_univ_instance, quoted_proj) structure_of_term =
   match t with
  | Coq_tRel n -> ACoq_tRel n
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

  let mkPolymorphic_entry names c = Universes0.Polymorphic_entry (names, c)
  let mkMonomorphic_entry c = Universes0.Monomorphic_entry c
  
end

module ExtractedASTQuoter = Quoter.Quoter(ExtractedASTBaseQuoter)

include ExtractedASTBaseQuoter
include ExtractedASTQuoter
