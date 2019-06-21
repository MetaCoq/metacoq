open Univ
open Entries
open Names
open Pp
open Tm_util
open Quoted
open Quoter
open Constr_quoted

(** The reifier to Coq values *)
module TemplateCoqQuoter =
struct
  include ConstrQuoted


  let to_coq_list typ =
    let the_nil = Constr.mkApp (c_nil, [| typ |]) in
    let rec to_list (ls : Constr.t list) : Constr.t =
      match ls with
	[] -> the_nil
      | l :: ls ->
	Constr.mkApp (c_cons, [| typ ; l ; to_list ls |])
    in to_list

  let quote_option ty = function
    | Some tm -> Constr.mkApp (cSome, [|ty; tm|])
    | None -> Constr.mkApp (cNone, [|ty|])

  (* Quote OCaml int to Coq nat *)
  let quote_int =
    (* the cache is global but only accessible through quote_int *)
    let cache = Hashtbl.create 10 in
    let rec recurse i =
      try Hashtbl.find cache i
      with
	Not_found ->
	  if i = 0 then
	    let result = tO in
	    let _ = Hashtbl.add cache i result in
	    result
	  else
	    let result = Constr.mkApp (tS, [| recurse (i - 1) |]) in
	    let _ = Hashtbl.add cache i result in
	    result
    in
    fun i ->
    if i >= 0 then recurse i else
      CErrors.anomaly (str "Negative int can't be unquoted to nat.")

  let quote_bool b =
    if b then ttrue else tfalse

  let quote_char i =
    Constr.mkApp (tAscii, Array.of_list (List.map (fun m -> quote_bool ((i land m) = m))
					 (List.rev [128;64;32;16;8;4;2;1])))

  let chars = Array.init 255 quote_char

  let quote_char c = chars.(int_of_char c)

  let string_hash = Hashtbl.create 420

  let to_string s =
    let len = String.length s in
    let rec go from acc =
      if from < 0 then acc
      else
        let term = Constr.mkApp (tString, [| quote_char (String.get s from) ; acc |]) in
        go (from - 1) term
    in
    go (len - 1) tEmptyString

  let quote_string s =
    try Hashtbl.find string_hash s
    with Not_found ->
      let term = to_string s in
      Hashtbl.add string_hash s term; term

  let quote_ident i =
    let s = Id.to_string i in
    quote_string s

  let quote_name n =
    match n with
      Names.Name id -> Constr.mkApp (nNamed, [| quote_ident id |])
    | Names.Anonymous -> nAnon

  let quote_cast_kind k =
    match k with
      Constr.VMcast -> kVmCast
    | Constr.DEFAULTcast -> kCast
    | Constr.REVERTcast -> kRevertCast
    | Constr.NATIVEcast -> kNative

  let string_of_level s =
    to_string (Univ.Level.to_string s)

  let quote_level l =
    debug (fun () -> str"quote_level " ++ Level.pr l);
    if Level.is_prop l then lProp
    else if Level.is_set l then lSet
    else match Level.var_index l with
         | Some x -> Constr.mkApp (tLevelVar, [| quote_int x |])
         | None -> Constr.mkApp (tLevel, [| string_of_level l|])

  let quote_universe s =
    let levels = Universe.map (fun (l,i) -> pair tlevel bool_type (quote_level l) (if i > 0 then ttrue else tfalse)) s in
    let hd = List.hd levels in
    let tl = to_coq_list (prod tlevel bool_type) (List.tl levels) in
    Constr.mkApp (tmake_universe, [| hd ; tl |])

  (* todo : can be deduced from quote_level, hence shoud be in the Reify module *)
  let quote_univ_instance u =
    let arr = Univ.Instance.to_array u in
    to_coq_list tlevel (CArray.map_to_list quote_level arr)

  let quote_constraint_type (c : Univ.constraint_type) =
    match c with
    | Lt -> tunivLt
    | Le -> tunivLe
    | Eq -> tunivEq

  let quote_univ_constraint ((l1, ct, l2) : Univ.univ_constraint) =
    let l1 = quote_level l1 in
    let l2 = quote_level l2 in
    let ct = quote_constraint_type ct in
    Constr.mkApp (tmake_univ_constraint, [| l1; ct; l2 |])

  let quote_univ_constraints const =
    let const = Univ.Constraint.elements const in
    List.fold_left (fun tm c ->
        let c = quote_univ_constraint c in
        Constr.mkApp (tConstraintSetadd, [| c; tm|])
      ) tConstraintSetempty const

  let quote_variance v =
    match v with
    | Univ.Variance.Irrelevant -> cIrrelevant
    | Univ.Variance.Covariant -> cCovariant
    | Univ.Variance.Invariant -> cInvariant

  let quote_cuminfo_variance var =
    let var_list = CArray.map_to_list quote_variance var in
    to_coq_list tVariance var_list

  let quote_ucontext inst const =
    let inst' = quote_univ_instance inst in
    let const' = quote_univ_constraints const in
    Constr.mkApp (tUContextmake, [|inst'; const'|])

  let quote_univ_context uctx =
    let inst = Univ.UContext.instance uctx in
    let const = Univ.UContext.constraints uctx in
    Constr.mkApp (cMonomorphic_ctx, [| quote_ucontext inst const |])

  let quote_cumulative_univ_context cumi =
    let uctx = Univ.CumulativityInfo.univ_context cumi in
    let inst = Univ.UContext.instance uctx in
    let const = Univ.UContext.constraints uctx in
    let var = Univ.CumulativityInfo.variance cumi in
    let uctx' = quote_ucontext inst const in
    let var' = quote_cuminfo_variance var in
    let listvar = Constr.mkApp (tlist, [| tVariance |]) in
    let cumi' = pair tUContext listvar uctx' var' in
    Constr.mkApp (cCumulative_ctx, [| cumi' |])

  let quote_abstract_univ_context_aux uctx =
    let inst = Univ.UContext.instance uctx in
    let const = Univ.UContext.constraints uctx in
    Constr.mkApp (cPolymorphic_ctx, [| quote_ucontext inst const |])

  let quote_abstract_univ_context uctx =
    let uctx = Univ.AUContext.repr uctx in
    quote_abstract_univ_context_aux uctx

  let quote_inductive_universes uctx =
    match uctx with
    | Monomorphic_ind_entry uctx -> quote_univ_context (Univ.ContextSet.to_context uctx)
    | Polymorphic_ind_entry uctx -> quote_abstract_univ_context_aux uctx
    | Cumulative_ind_entry info ->
      quote_abstract_univ_context_aux (CumulativityInfo.univ_context info) (* FIXME lossy *)

  let quote_ugraph (g : UGraph.t) =
    let inst' = quote_univ_instance Univ.Instance.empty in
    let const' = quote_univ_constraints (UGraph.constraints_of_universes g) in
    let uctx = Constr.mkApp (tUContextmake, [|inst' ; const'|]) in
    Constr.mkApp (tadd_global_constraints, [|Constr.mkApp (cMonomorphic_ctx, [| uctx |]); tinit_graph|])

  let quote_sort s =
    quote_universe (Sorts.univ_of_sort s)

  let quote_sort_family = function
    | Sorts.InProp -> sfProp
    | Sorts.InSet -> sfSet
    | Sorts.InType -> sfType

  let quote_context_decl na b t =
    Constr.mkApp (tmkdecl, [| na; quote_option tTerm b; t |])

  let quote_context ctx =
    to_coq_list tcontext_decl ctx

  let mk_ctor_list =
    let ctor_list =
      let ctor_info_typ = prod (prod tident tTerm) tnat in
      to_coq_list ctor_info_typ
    in
    fun ls ->
    let ctors = List.map (fun (a,b,c) -> pair (prod tident tTerm) tnat
				              (pair tident tTerm a b) c) ls in
    ctor_list ctors

  let mk_proj_list d =
    to_coq_list (prod tident tTerm)
                (List.map (fun (a, b) -> pair tident tTerm a b) d)

  let quote_inductive (kn, i) =
    Constr.mkApp (tmkInd, [| kn; i |])

  let mkAnon = nAnon
  let mkName id = Constr.mkApp (nNamed, [| id |])
  let quote_kn kn = quote_string (KerName.to_string kn)
  let mkRel i = Constr.mkApp (tRel, [| i |])
  let mkVar id = Constr.mkApp (tVar, [| id |])
  let mkEvar n args = Constr.mkApp (tEvar, [| n; to_coq_list tTerm (Array.to_list args) |])
  let mkSort s = Constr.mkApp (tSort, [| s |])
  let mkCast c k t = Constr.mkApp (tCast, [| c ; k ; t |])
  let mkConst kn u = Constr.mkApp (tConst, [| kn ; u |])
  let mkProd na t b =
    Constr.mkApp (tProd, [| na ; t ; b |])
  let mkLambda na t b =
    Constr.mkApp (tLambda, [| na ; t ; b |])
  let mkApp f xs =
    Constr.mkApp (tApp, [| f ; to_coq_list tTerm (Array.to_list xs) |])

  let mkLetIn na t t' b =
    Constr.mkApp (tLetIn, [| na ; t ; t' ; b |])

  let rec seq f t =
    if f < t then f :: seq (f + 1) t
    else []

  let mkFix ((a,b),(ns,ts,ds)) =
    let mk_fun xs i =
      Constr.mkApp (tmkdef, [| tTerm ; Array.get ns i ;
                             Array.get ts i ; Array.get ds i ; Array.get a i |]) :: xs
    in
    let defs = List.fold_left mk_fun [] (seq 0 (Array.length a)) in
    let block = to_coq_list (Constr.mkApp (tdef, [| tTerm |])) (List.rev defs) in
    Constr.mkApp (tFix, [| block ; b |])

  let mkConstruct (ind, i) u =
    Constr.mkApp (tConstructor, [| ind ; i ; u |])

  let mkCoFix (a,(ns,ts,ds)) =
    let mk_fun xs i =
      Constr.mkApp (tmkdef, [| tTerm ; Array.get ns i ;
                             Array.get ts i ; Array.get ds i ; tO |]) :: xs
    in
    let defs = List.fold_left mk_fun [] (seq 0 (Array.length ns)) in
    let block = to_coq_list (Constr.mkApp (tdef, [| tTerm |])) (List.rev defs) in
    Constr.mkApp (tCoFix, [| block ; a |])

  let mkInd i u = Constr.mkApp (tInd, [| i ; u |])

  let mkCase (ind, npar) nargs p c brs =
    let info = pair tIndTy tnat ind npar in
    let branches = List.map2 (fun br nargs ->  pair tnat tTerm nargs br) brs nargs in
    let tl = prod tnat tTerm in
    Constr.mkApp (tCase, [| info ; p ; c ; to_coq_list tl branches |])

  let quote_proj ind pars args =
    pair (prod tIndTy tnat) tnat (pair tIndTy tnat ind pars) args

  let mkProj kn t =
    Constr.mkApp (tProj, [| kn; t |])

  let mk_one_inductive_body (a, b, c, d, e) =
    let c = to_coq_list tsort_family c in
    let d = mk_ctor_list d in
    let e = mk_proj_list e in
    Constr.mkApp (tBuild_one_inductive_body, [| a; b; c; d; e |])

  let mk_mutual_inductive_body finite npars params inds uctx =
    let inds = to_coq_list tone_inductive_body inds in
    Constr.mkApp (tBuild_mutual_inductive_body, [|finite; npars; params; inds; uctx|])

  let mk_constant_body ty tm uctx =
    let tm = quote_option tTerm tm in
    Constr.mkApp (tBuild_constant_body, [|ty; tm; uctx|])

  let mk_inductive_decl kn mind =
    Constr.mkApp (tInductiveDecl, [|kn; mind|])

  let mk_constant_decl kn bdy =
    Constr.mkApp (tConstantDecl, [|kn; bdy|])

  let empty_global_declartions =
    Constr.mkApp (c_nil, [| tglobal_decl |])

  let add_global_decl d l =
    Constr.mkApp (c_cons, [|tglobal_decl; d; l|])

  let mk_program = pair tglobal_declarations tTerm

  let quote_mind_finiteness (f: Declarations.recursivity_kind) =
    match f with
    | Declarations.Finite -> cFinite
    | Declarations.CoFinite -> cCoFinite
    | Declarations.BiFinite -> cBiFinite

  let make_one_inductive_entry (iname, arity, templatePoly, consnames, constypes) =
    let consnames = to_coq_list tident consnames in
    let constypes = to_coq_list tTerm constypes in
    Constr.mkApp (tBuild_one_inductive_entry, [| iname; arity; templatePoly; consnames; constypes |])

  let quote_mind_params l =
    let pair i l = pair tident tlocal_entry i l in
    let map (id, ob) =
      match ob with
      | Left b -> pair id (Constr.mkApp (tLocalDef,[|b|]))
      | Right t -> pair id (Constr.mkApp (tLocalAssum,[|t|]))
    in
    let the_prod = Constr.mkApp (prod_type,[|tident; tlocal_entry|]) in
    to_coq_list the_prod (List.map map l)

  let quote_mutual_inductive_entry (mf, mp, is, mpol) =
    let is = to_coq_list tOne_inductive_entry (List.map make_one_inductive_entry is) in
    let mpr = Constr.mkApp (cNone, [|bool_type|]) in
    let mr = Constr.mkApp (cNone, [|Constr.mkApp (option_type, [|tident|])|])  in
    Constr.mkApp (tBuild_mutual_inductive_entry, [| mr; mf; mp; is; mpol; mpr |])


  let quote_constant_entry (ty, body, ctx) =
    match body with
    | None ->
      Constr.mkApp (cParameterEntry, [| Constr.mkApp (cParameter_entry, [|ty; ctx|]) |])
    | Some body ->
      Constr.mkApp (cDefinitionEntry,
                  [| Constr.mkApp (cDefinition_entry, [|ty;body;ctx;tfalse (*FIXME*)|]) |])

  let quote_entry decl =
    let opType = Constr.mkApp(sum_type, [|tConstant_entry;tMutual_inductive_entry|]) in
    let mkSome c t = Constr.mkApp (cSome, [|opType; Constr.mkApp (c, [|tConstant_entry;tMutual_inductive_entry; t|] )|]) in
    let mkSomeDef = mkSome cInl in
    let mkSomeInd  = mkSome cInr in
    match decl with
    | Some (Left centry) -> mkSomeDef (quote_constant_entry centry)
    | Some (Right mind) -> mkSomeInd mind
    | None -> Constr.mkApp (cNone, [| opType |])


  let quote_global_reference : Globnames.global_reference -> quoted_global_reference = function
    | Globnames.VarRef _ -> CErrors.user_err (str "VarRef unsupported")
    | Globnames.ConstRef c ->
       let kn = quote_kn (Names.Constant.canonical c) in
       Constr.mkApp (tConstRef, [|kn|])
    | Globnames.IndRef (i, n) ->
       let kn = quote_kn (Names.MutInd.canonical i) in
       let n = quote_int n in
       Constr.mkApp (tIndRef, [|quote_inductive (kn ,n)|])
    | Globnames.ConstructRef ((i, n), k) ->
       let kn = quote_kn (Names.MutInd.canonical i) in
       let n = quote_int n in
       let k = (quote_int (k - 1)) in
       Constr.mkApp (tConstructRef, [|quote_inductive (kn ,n); k|])
end


module TermReify = Reify(TemplateCoqQuoter)
