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
    let the_nil = constr_mkApp (c_nil, [| typ |]) in
    let rec to_list (ls : Constr.t list) : Constr.t =
      match ls with
	[] -> the_nil
      | l :: ls ->
	constr_mkApp (c_cons, [| typ ; l ; to_list ls |])
    in to_list

  let quote_option ty = function
    | Some tm -> constr_mkApp (cSome, [|ty; tm|])
    | None -> constr_mkApp (cNone, [|ty|])

  (* Quote OCaml int to Coq nat *)
  let quote_int =
    (* the cache is global but only accessible through quote_int *)
    let cache = Hashtbl.create 10 in
    let rec recurse i =
      try Hashtbl.find cache i
      with
	Not_found ->
	  if i = 0 then
	    let result = Lazy.force tO in
	    let _ = Hashtbl.add cache i result in
	    result
	  else
	    let result = constr_mkApp (tS, [| recurse (i - 1) |]) in
	    let _ = Hashtbl.add cache i result in
	    result
    in
    fun i ->
    if i >= 0 then recurse i else
      CErrors.anomaly (str "Negative int can't be unquoted to nat.")

  let quote_bool b =
    if b then Lazy.force ttrue else Lazy.force tfalse

  let quote_char i =
    constr_mkApp (tAscii, Array.of_list (List.map (fun m -> quote_bool ((i land m) = m))
					 (List.rev [128;64;32;16;8;4;2;1])))

  let chars = lazy (Array.init 255 quote_char)

  let quote_char c = (Lazy.force chars).(int_of_char c)

  let string_hash = Hashtbl.create 420

  let to_string s =
    let len = String.length s in
    let rec go from acc =
      if from < 0 then acc
      else
        let term = constr_mkApp (tString, [| quote_char (String.get s from) ; acc |]) in
        go (from - 1) term
    in
    go (len - 1) (Lazy.force tEmptyString)

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
      Names.Name id -> constr_mkApp (nNamed, [| quote_ident id |])
    | Names.Anonymous -> Lazy.force nAnon

  let quote_cast_kind k =
    match k with
      Constr.VMcast -> Lazy.force kVmCast
    | Constr.DEFAULTcast -> Lazy.force kCast
    | Constr.REVERTcast -> Lazy.force kRevertCast
    | Constr.NATIVEcast -> Lazy.force kNative

  let string_of_level s =
    to_string (Univ.Level.to_string s)

  let quote_level l =
    debug (fun () -> str"quote_level " ++ Level.pr l);
    if Level.is_prop l then Lazy.force lProp
    else if Level.is_set l then Lazy.force lSet
    else match Level.var_index l with
         | Some x -> constr_mkApp (tLevelVar, [| quote_int x |])
         | None -> constr_mkApp (tLevel, [| string_of_level l|])

  let quote_universe s =
    let levels = Universe.map (fun (l,i) -> pairl tlevel bool_type (quote_level l) (quote_bool (i > 0))) s in
    let hd = List.hd levels in
    let tl = to_coq_list (prodl tlevel bool_type) (List.tl levels) in
    constr_mkApp (tmake_universe, [| hd ; tl |])

  (* todo : can be deduced from quote_level, hence shoud be in the Reify module *)
  let quote_univ_instance u =
    let arr = Univ.Instance.to_array u in
    to_coq_listl tlevel (CArray.map_to_list quote_level arr)

  let quote_constraint_type (c : Univ.constraint_type) =
    match c with
    | Lt -> Lazy.force tunivLt
    | Le -> Lazy.force tunivLe
    | Eq -> Lazy.force tunivEq

  let quote_univ_constraint ((l1, ct, l2) : Univ.univ_constraint) =
    let l1 = quote_level l1 in
    let l2 = quote_level l2 in
    let ct = quote_constraint_type ct in
    constr_mkApp (tmake_univ_constraint, [| l1; ct; l2 |])

  let quote_univ_constraints const =
    let const = Univ.Constraint.elements const in
    List.fold_left (fun tm c ->
        let c = quote_univ_constraint c in
        constr_mkApp (tConstraintSetadd, [| c; tm|])
      ) (Lazy.force tConstraintSetempty) const

  let quote_variance v =
    match v with
    | Univ.Variance.Irrelevant -> Lazy.force cIrrelevant
    | Univ.Variance.Covariant -> Lazy.force cCovariant
    | Univ.Variance.Invariant -> Lazy.force cInvariant

  let quote_cuminfo_variance var =
    let var_list = CArray.map_to_list quote_variance var in
    to_coq_listl tVariance var_list

  let quote_ucontext inst const =
    let inst' = quote_univ_instance inst in
    let const' = quote_univ_constraints const in
    constr_mkApp (tUContextmake, [|inst'; const'|])

  let quote_univ_context uctx =
    let inst = Univ.UContext.instance uctx in
    let const = Univ.UContext.constraints uctx in
    constr_mkApp (cMonomorphic_ctx, [| quote_ucontext inst const |])

  let quote_cumulative_univ_context cumi =
    let uctx = Univ.CumulativityInfo.univ_context cumi in
    let inst = Univ.UContext.instance uctx in
    let const = Univ.UContext.constraints uctx in
    let var = Univ.CumulativityInfo.variance cumi in
    let uctx' = quote_ucontext inst const in
    let var' = quote_cuminfo_variance var in
    let listvar = constr_mkAppl (tlist, [| tVariance |]) in
    let cumi' = pair (Lazy.force tUContext) listvar uctx' var' in
    constr_mkApp (cCumulative_ctx, [| cumi' |])

  let quote_abstract_univ_context_aux uctx =
    let inst = Univ.UContext.instance uctx in
    let const = Univ.UContext.constraints uctx in
    constr_mkApp (cPolymorphic_ctx, [| quote_ucontext inst const |])

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
    let uctx = constr_mkApp (tUContextmake, [|inst' ; const'|]) in
    constr_mkApp (tadd_global_constraints, [|constr_mkApp (cMonomorphic_ctx, [| uctx |]); Lazy.force tinit_graph|])

  let quote_sort s =
    quote_universe (Sorts.univ_of_sort s)

  let quote_sort_family = function
    | Sorts.InProp -> Lazy.force sfProp
    | Sorts.InSet -> Lazy.force sfSet
    | Sorts.InType -> Lazy.force sfType

  let quote_context_decl na b t =
    constr_mkApp (tmkdecl, [| na; quote_optionl tTerm b; t |])

  let quote_context ctx =
    to_coq_listl tcontext_decl ctx

  let mk_ctor_list =
    let ctor_list =
      lazy (let ctor_info_typ = prod (prodl tident tTerm) (Lazy.force tnat) in
      to_coq_list ctor_info_typ)
    in
    fun ls ->
    let ctors = List.map (fun (a,b,c) -> pair (prodl tident tTerm) (Lazy.force tnat)
				              (pairl tident tTerm a b) c) ls in
    (Lazy.force ctor_list) ctors

  let mk_proj_list d =
    to_coq_list (prodl tident tTerm)
                (List.map (fun (a, b) -> pairl tident tTerm a b) d)

  let quote_inductive (kn, i) =
    constr_mkApp (tmkInd, [| kn; i |])

  let mkAnon () = Lazy.force nAnon
  let mkName id = constr_mkApp (nNamed, [| id |])
  let quote_kn kn = quote_string (KerName.to_string kn)
  let mkRel i = constr_mkApp (tRel, [| i |])
  let mkVar id = constr_mkApp (tVar, [| id |])
  let mkEvar n args = constr_mkApp (tEvar, [| n; to_coq_listl tTerm (Array.to_list args) |])
  let mkSort s = constr_mkApp (tSort, [| s |])
  let mkCast c k t = constr_mkApp (tCast, [| c ; k ; t |])
  let mkConst kn u = constr_mkApp (tConst, [| kn ; u |])
  let mkProd na t b =
    constr_mkApp (tProd, [| na ; t ; b |])
  let mkLambda na t b =
    constr_mkApp (tLambda, [| na ; t ; b |])
  let mkApp f xs =
    constr_mkApp (tApp, [| f ; to_coq_listl tTerm (Array.to_list xs) |])

  let mkLetIn na t t' b =
    constr_mkApp (tLetIn, [| na ; t ; t' ; b |])

  let rec seq f t =
    if f < t then f :: seq (f + 1) t
    else []

  let mkFix ((a,b),(ns,ts,ds)) =
    let mk_fun xs i =
      constr_mkApp (tmkdef, [| Lazy.force tTerm ; Array.get ns i ;
                             Array.get ts i ; Array.get ds i ; Array.get a i |]) :: xs
    in
    let defs = List.fold_left mk_fun [] (seq 0 (Array.length a)) in
    let block = to_coq_list (constr_mkAppl (tdef, [| tTerm |])) (List.rev defs) in
    constr_mkApp (tFix, [| block ; b |])

  let mkConstruct (ind, i) u =
    constr_mkApp (tConstructor, [| ind ; i ; u |])

  let mkCoFix (a,(ns,ts,ds)) =
    let mk_fun xs i =
      constr_mkApp (tmkdef, [| Lazy.force tTerm ; Array.get ns i ;
                             Array.get ts i ; Array.get ds i ; Lazy.force tO |]) :: xs
    in
    let defs = List.fold_left mk_fun [] (seq 0 (Array.length ns)) in
    let block = to_coq_list (constr_mkAppl (tdef, [| tTerm |])) (List.rev defs) in
    constr_mkApp (tCoFix, [| block ; a |])

  let mkInd i u = constr_mkApp (tInd, [| i ; u |])

  let mkCase (ind, npar) nargs p c brs =
    let info = pairl tIndTy tnat ind npar in
    let branches = List.map2 (fun br nargs ->  pairl tnat tTerm nargs br) brs nargs in
    let tl = prodl tnat tTerm in
    constr_mkApp (tCase, [| info ; p ; c ; to_coq_list tl branches |])

  let quote_proj ind pars args =
    pair (prodl tIndTy tnat) (Lazy.force tnat) (pairl tIndTy tnat ind pars) args

  let mkProj kn t =
    constr_mkApp (tProj, [| kn; t |])

  let mk_one_inductive_body (a, b, c, d, e) =
    let c = to_coq_listl tsort_family c in
    let d = mk_ctor_list d in
    let e = mk_proj_list e in
    constr_mkApp (tBuild_one_inductive_body, [| a; b; c; d; e |])

  let mk_mutual_inductive_body finite npars params inds uctx =
    let inds = to_coq_listl tone_inductive_body inds in
    constr_mkApp (tBuild_mutual_inductive_body, [|finite; npars; params; inds; uctx|])

  let mk_constant_body ty tm uctx =
    let tm = quote_optionl tTerm tm in
    constr_mkApp (tBuild_constant_body, [|ty; tm; uctx|])

  let mk_inductive_decl kn mind =
    constr_mkApp (tInductiveDecl, [|kn; mind|])

  let mk_constant_decl kn bdy =
    constr_mkApp (tConstantDecl, [|kn; bdy|])

  let empty_global_declartions () =
    constr_mkAppl (c_nil, [| tglobal_decl |])

  let add_global_decl d l =
    constr_mkApp (c_cons, [|Lazy.force tglobal_decl; d; l|])

  let mk_program f s = pairl tglobal_declarations tTerm f s

  let quote_mind_finiteness (f: Declarations.recursivity_kind) =
    match f with
    | Declarations.Finite -> Lazy.force cFinite
    | Declarations.CoFinite -> Lazy.force cCoFinite
    | Declarations.BiFinite -> Lazy.force cBiFinite

  let make_one_inductive_entry (iname, arity, templatePoly, consnames, constypes) =
    let consnames = to_coq_listl tident consnames in
    let constypes = to_coq_listl tTerm constypes in
    constr_mkApp (tBuild_one_inductive_entry, [| iname; arity; templatePoly; consnames; constypes |])

  let quote_mind_params l =
    let pair i l = pairl tident tlocal_entry i l in
    let map (id, ob) =
      match ob with
      | Left b -> pair id (constr_mkApp (tLocalDef,[|b|]))
      | Right t -> pair id (constr_mkApp (tLocalAssum,[|t|]))
    in
    let the_prod = constr_mkAppl (prod_type,[|tident; tlocal_entry|]) in
    to_coq_list the_prod (List.map map l)

  let quote_mutual_inductive_entry (mf, mp, is, mpol) =
    let is = to_coq_listl tOne_inductive_entry (List.map make_one_inductive_entry is) in
    let mpr = constr_mkAppl (cNone, [|bool_type|]) in
    let mr = constr_mkApp (cNone, [|constr_mkAppl (option_type, [|tident|])|])  in
    constr_mkApp (tBuild_mutual_inductive_entry, [| mr; mf; mp; is; mpol; mpr |])


  let quote_constant_entry (ty, body, ctx) =
    match body with
    | None ->
      constr_mkApp (cParameterEntry, [| constr_mkApp (cParameter_entry, [|ty; ctx|]) |])
    | Some body ->
      constr_mkApp (cDefinitionEntry,
                  [| constr_mkApp (cDefinition_entry, [|ty;body;ctx;Lazy.force tfalse (*FIXME*)|]) |])

  let quote_entry decl =
    let opType = constr_mkAppl(sum_type, [|tConstant_entry;tMutual_inductive_entry|]) in
    let mkSome c t = constr_mkApp (cSome, [|opType; constr_mkAppl (c, [|tConstant_entry;tMutual_inductive_entry; lazy t|] )|]) in
    let mkSomeDef = mkSome cInl in
    let mkSomeInd  = mkSome cInr in
    match decl with
    | Some (Left centry) -> mkSomeDef (quote_constant_entry centry)
    | Some (Right mind) -> mkSomeInd mind
    | None -> constr_mkApp (cNone, [| opType |])


  let quote_global_reference : Globnames.global_reference -> quoted_global_reference = function
    | Globnames.VarRef _ -> CErrors.user_err (str "VarRef unsupported")
    | Globnames.ConstRef c ->
       let kn = quote_kn (Names.Constant.canonical c) in
       constr_mkApp (tConstRef, [|kn|])
    | Globnames.IndRef (i, n) ->
       let kn = quote_kn (Names.MutInd.canonical i) in
       let n = quote_int n in
       constr_mkApp (tIndRef, [|quote_inductive (kn ,n)|])
    | Globnames.ConstructRef ((i, n), k) ->
       let kn = quote_kn (Names.MutInd.canonical i) in
       let n = quote_int n in
       let k = (quote_int (k - 1)) in
       constr_mkApp (tConstructRef, [|quote_inductive (kn ,n); k|])
end


module TermReify = Reify(TemplateCoqQuoter)
