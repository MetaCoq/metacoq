open Univ
open Entries
open Pp
open Tm_util

(** The reifier to Coq values *)
module ConstrQuoted =
struct
  type t = Constr.t

  type quoted_ident = Constr.t (* of type Ast.ident *)
  type quoted_int = Constr.t (* of type nat *)
  type quoted_bool = Constr.t (* of type bool *)
  type quoted_name = Constr.t (* of type Ast.name *)
  type quoted_sort = Constr.t (* of type Ast.universe *)
  type quoted_cast_kind = Constr.t  (* of type Ast.cast_kind *)
  type quoted_kernel_name = Constr.t (* of type Ast.kername *)
  type quoted_inductive = Constr.t (* of type Ast.inductive *)
  type quoted_proj = Constr.t (* of type Ast.projection *)
  type quoted_global_reference = Constr.t (* of type Ast.global_reference *)

  type quoted_sort_family = Constr.t (* of type Ast.sort_family *)
  type quoted_constraint_type = Constr.t (* of type Universes.constraint_type *)
  type quoted_univ_constraint = Constr.t (* of type Universes.univ_constraint *)
  type quoted_univ_constraints = Constr.t (* of type Universes.constraints *)
  type quoted_univ_instance = Constr.t (* of type Universes.universe_instance *)
  type quoted_univ_context = Constr.t (* of type Universes.UContext.t *)
  type quoted_univ_contextset = Constr.t (* of type Universes.ContextSet.t *)
  type quoted_abstract_univ_context = Constr.t (* of type Universes.AUContext.t *)
  type quoted_variance = Constr.t (* of type Universes.Variance.t *)
  type quoted_universes_decl = Constr.t (* of type Universes.universes_decl *)

  type quoted_universes_entry = Constr.t (* of type Ast.universes_entry *)
  type quoted_ind_entry = quoted_ident * t * quoted_bool * quoted_ident list * t list
  type quoted_definition_entry = Constr.t (* of type Ast.definition_entry *)
  type quoted_parameter_entry = Constr.t (* of type Ast.parameter_entry *)
  type quoted_constant_entry = Constr.t (* of type Ast.constant_entry *)
  type quoted_mind_entry = Constr.t (* of type Ast.mutual_inductive_entry *)
  type quoted_mind_finiteness = Constr.t (* of type Ast.mutual_inductive_entry ?? *)
  type quoted_entry = Constr.t (* of type option (constant_entry + mutual_inductive_entry) *)

  type quoted_context_decl = Constr.t (* in Ast *)
  type quoted_context = Constr.t (* in Ast *)

  type quoted_one_inductive_body = Constr.t (* of type Ast.one_inductive_body *)
  type quoted_mutual_inductive_body = Constr.t (* of type Ast.mutual_inductive_body *)
  type quoted_constant_body = Constr.t (* of type Ast.constant_body *)
  type quoted_global_decl = Constr.t (* of type Ast.global_decl *)
  type quoted_global_env = Constr.t (* of type Ast.global_env *)
  type quoted_program = Constr.t (* of type Ast.program *)

  let resolve (tm : string) : Constr.t Lazy.t =
    lazy (
      let tm_ref = Coqlib.lib_ref tm in
      UnivGen.constr_of_monomorphic_global tm_ref
    )
    (* gen_constant_in_modules contrib_name [path] tm *)

  let resolve_ref (tm : string) : Names.GlobRef.t Lazy.t =
    lazy (Coqlib.lib_ref tm)

  let ast s = resolve ("metacoq.ast." ^ s)
  let template s = resolve ("metacoq.template." ^ s)
  let template_ref s = resolve_ref ("metacoq.template." ^ s)

  let tString = resolve "metacoq.string.cons"
  let tEmptyString = resolve "metacoq.string.nil"
  let tO = resolve "metacoq.nat.zero"
  let tS = resolve "metacoq.nat.succ"
  let tnat = resolve "metacoq.nat.type"
  let bool_type = resolve "metacoq.bool.type"
  let ttrue = resolve "metacoq.bool.true"
  let tfalse = resolve "metacoq.bool.false"
  let option_type = resolve "metacoq.option.type"
  let cSome = resolve "metacoq.option.some"
  let cNone = resolve "metacoq.option.none"

  let unit_tt = resolve "metacoq.unit.intro"
  
  let tAscii = resolve "metacoq.ascii.intro"
  let tlist = resolve "metacoq.list.type"
  let c_nil = resolve "metacoq.list.nil"
  let c_cons = resolve "metacoq.list.cons"

  let prod_type = resolve "metacoq.prod.type"
  let c_pair = resolve "metacoq.prod.intro"

  let sum_type = resolve "metacoq.sum.type"
  let cInl = resolve "metacoq.sum.inl"
  let cInr = resolve "metacoq.sum.inr"

  let texistT = resolve "metacoq.sigma.intro"
  let texistT_typed_term = resolve_ref "metacoq.sigma.typed_term"

  let constr_mkApp (h, a) = Constr.mkApp (Lazy.force h, a)
  let constr_mkAppl (h, a) = Constr.mkApp (Lazy.force h, Array.map Lazy.force a)
  let prod a b = constr_mkApp (prod_type, [| a ; b |])
  let prodl a b = prod (Lazy.force a) (Lazy.force b)
  let pair a b f s = constr_mkApp (c_pair, [| a ; b ; f ; s |])
  let pairl a b f s = pair (Lazy.force a) (Lazy.force b) f s

    (* reify the constructors in Template.Ast.v, which are the building blocks of reified terms *)
  let nAnon = ast "nAnon"
  let nNamed = ast "nNamed"
  let kVmCast = ast "VmCast"
  let kNative = ast "NativeCast"
  let kCast = ast "Cast"
  let kRevertCast = ast "RevertCast"
  let lProp = ast "level.lProp"
  let lSet = ast "level.lSet"
  let tsort_family = ast "sort_family"
  let lfresh_universe = ast "fresh_universe"
  let lfresh_level = ast "fresh_level"
  let sfProp = ast "InProp"
  let sfSet = ast "InSet"
  let sfType = ast "InType"
  let tident = ast "ident"
  let tname = ast "name"
  let tIndTy = ast "inductive"
  let tmkInd = ast "mkInd"
  let tmkdecl = ast "mkdecl"
  let (tTerm,tRel,tVar,tEvar,tSort,tCast,tProd,
       tLambda,tLetIn,tApp,tCase,tFix,tConstructor,tConst,tInd,tCoFix,tProj) =
    (ast "term", ast "tRel", ast "tVar", ast "tEvar",
     ast "tSort", ast "tCast", ast "tProd", ast "tLambda",
     ast "tLetIn", ast "tApp", ast "tCase", ast "tFix",
     ast "tConstruct", ast "tConst", ast "tInd", ast "tCoFix", ast "tProj")

  let tlevel = ast "level.t"
  let tLevel = ast "level.Level"
  let tLevelVar = ast "level.Var"
  let tunivLe = ast "constraints.Le"
  let tunivLt = ast "constraints.Lt"
  let tunivEq = ast "constraints.Eq"
  let tMktUnivExprSet = ast "univexprset.mkt"
  let tBuild_Universe = ast "universe.build"
  let tfrom_kernel_repr = ast "universe.from_kernel_repr"
  let tto_kernel_repr = ast "universe.to_kernel_repr"
  let tLevelSet_of_list = ast "universe.of_list"

  let noprop_tSet = ast "noproplevel.lSet"
  let noprop_tLevel = ast "noproplevel.Level"
  let noprop_tLevelVar = ast "noproplevel.Var"
  let univexpr_lProp = ast "univexpr.prop"
  let univexpr_npe = ast "univexpr.npe"

  (* let tunivcontext = resolve_symbol pkg_univ "universe_context" *)
  let tVariance = ast "variance.t"
  let cIrrelevant = ast "variance.Irrelevant"
  let cCovariant = ast "variance.Covariant"
  let cInvariant = ast "variance.Invariant"
  let cMonomorphic_ctx = ast "Monomorphic_ctx"
  let cPolymorphic_ctx = ast "Polymorphic_ctx"
  let tUContext = ast "UContext.t"
  let tAUContext = ast "AUContext.t"
  let tUContextmake = ast "UContext.make"
  let tAUContextmake = ast "AUContext.make"
  let tConstraintSet = ast "ConstraintSet.t_"
  let tConstraintSetempty = ast "ConstraintSet.empty"
  let tConstraintSetadd = ast "ConstraintSet.add"
  let tLevelSet = ast "LevelSet.t"
  let tmake_univ_constraint = ast "make_univ_constraint"
  let tinit_graph = ast "graph.init"
  (* FIXME this doesn't exist! *)
  let tadd_global_constraints = ast "graph.add_global_constraints"

  let (tdef,tmkdef) = (ast "def", ast "mkdef")

  let (cFinite,cCoFinite,cBiFinite) = (ast "Finite", ast "CoFinite", ast "BiFinite")
  let tone_inductive_body = ast "one_inductive_body"
  let tBuild_one_inductive_body = ast "Build_one_inductive_body"
  let tBuild_mutual_inductive_body = ast "Build_mutual_inductive_body"
  let tBuild_constant_body = ast "Build_constant_body"
  let tglobal_decl = ast "global_decl"
  let tConstantDecl = ast "ConstantDecl"
  let tInductiveDecl = ast "InductiveDecl"
  let tglobal_env = ast "global_env"

  let (tglobal_reference, tConstRef, tIndRef, tConstructRef) =
    (ast "global_reference", ast "ConstRef", ast "IndRef", ast "ConstructRef")

  let tcontext_decl = ast "context_decl"
  let tcontext = ast "context"

  let tMutual_inductive_entry = ast "mutual_inductive_entry"
  let tOne_inductive_entry = ast "one_inductive_entry"
  let tBuild_mutual_inductive_entry = ast "Build_mutual_inductive_entry"
  let tBuild_one_inductive_entry = ast "Build_one_inductive_entry"
  let tConstant_entry = ast "constant_entry"
  let cParameterEntry = ast "ParameterEntry"
  let cDefinitionEntry = ast "DefinitionEntry"
  let cBuild_parameter_entry = ast "Build_parameter_entry"
  let cBuild_definition_entry = ast "Build_definition_entry"
  let cMonomorphic_entry = ast "Monomorphic_entry"
  let cPolymorphic_entry = ast "Polymorphic_entry"

  let (tcbv, tcbn, thnf, tall, tlazy, tunfold) = 
    (template "cbv", template "cbn", template "hnf", template "all", template "lazy", template "unfold")

  let constr_equall h t = Constr.equal h (Lazy.force t)

  let to_coq_list typ =
    let the_nil = constr_mkApp (c_nil, [| typ |]) in
    let rec to_list (ls : Constr.t list) : Constr.t =
      match ls with
	[] -> the_nil
      | l :: ls ->
	constr_mkApp (c_cons, [| typ ; l ; to_list ls |])
    in to_list

  let to_coq_listl typ = to_coq_list (Lazy.force typ)

  let quote_option ty = function
    | Some tm -> constr_mkApp (cSome, [|ty; tm|])
    | None -> constr_mkApp (cNone, [|ty|])

  (* Quote OCaml int to Coq nat *)
  let quote_int =
    (* the cache is global but only accessible through quote_int *)
    let cache : (int,Constr.constr) Hashtbl.t = Hashtbl.create 10 in
    let rec recurse (i : int) : Constr.constr =
      try Hashtbl.find cache i
      with
	Not_found ->
	  if i = 0 then
	    let result = tO in
	    let _ =
              Hashtbl.add cache i (Lazy.force result) in
	    Lazy.force result
	  else
	    let result =
              constr_mkApp (tS, [| recurse (i - 1) |]) in
	    let _ =
              Hashtbl.add cache i result in
	    result
    in
    fun i ->
    if i >= 0 then recurse i else
      CErrors.anomaly Pp.(str "Negative int can't be unquoted to nat.")

  let quote_bool b =
    if b then ttrue else tfalse

  let quote_char i =
    constr_mkAppl (tAscii, Array.of_list (List.map (fun m -> quote_bool ((i land m) = m))
					 (List.rev [128;64;32;16;8;4;2;1])))

  let chars = Array.init 255 quote_char

  let quote_char c = chars.(int_of_char c)

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
    let s = Names.Id.to_string i in
    quote_string s

  let quote_name n =
    match n with
      Names.Name id -> constr_mkApp (nNamed, [| quote_ident id |])
    | Names.Anonymous -> Lazy.force nAnon

  let quote_cast_kind k =
    match k with
      Constr.VMcast -> kVmCast
    | Constr.DEFAULTcast -> kCast
    | Constr.REVERTcast -> kRevertCast
    | Constr.NATIVEcast -> kNative

  let string_of_level s =
    to_string (Univ.Level.to_string s)

  let quote_level l =
    let open Univ in
    debug (fun () -> str"quote_level " ++ Level.pr l);
    if Level.is_prop l then Lazy.force lProp
    else if Level.is_set l then Lazy.force lSet
    else match Level.var_index l with
         | Some x -> constr_mkApp (tLevelVar, [| quote_int x |])
         | None -> constr_mkApp (tLevel, [| string_of_level l|])

  let quote_universe s =
    let levels = Universe.map (fun (l,i) ->
                     pair (Lazy.force tlevel) (Lazy.force bool_type) (quote_level l)
                       (if i > 0 then (Lazy.force ttrue) else (Lazy.force tfalse))) s in
    to_coq_list (prod (Lazy.force tlevel) (Lazy.force bool_type)) levels

  (* todo : can be deduced from quote_level, hence shoud be in the Reify module *)
  let quote_univ_instance u =
    let arr = Univ.Instance.to_array u in
    to_coq_list (Lazy.force tlevel) (CArray.map_to_list quote_level arr)

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
    to_coq_list (Lazy.force tVariance) var_list

  let quote_ucontext inst const =
    let inst' = quote_univ_instance inst in
    let const' = quote_univ_constraints const in
    constr_mkApp (tUContextmake, [|inst'; const'|])

  let quote_univ_context uctx =
    let inst = Univ.UContext.instance uctx in
    let const = Univ.UContext.constraints uctx in
    constr_mkApp (cMonomorphic_ctx, [| quote_ucontext inst const |])

  let quote_variance var =
    let listvar = constr_mkAppl (tlist, [| tVariance |]) in
    match var with
    | None -> constr_mkApp (cNone, [| listvar |])
    | Some var ->
     let var' = quote_cuminfo_variance var in
      constr_mkApp (cSome, [| listvar; var' |])

  let quote_abstract_univ_context_aux uctx =
    let inst = Univ.UContext.instance uctx in
    let const = Univ.UContext.constraints uctx in
    constr_mkApp (cPolymorphic_ctx, [| quote_ucontext inst const |])

  let quote_abstract_univ_context uctx =
    let uctx = Univ.AUContext.repr uctx in
    quote_abstract_univ_context_aux uctx

  let mkMonomorphic_entry ctx = 
     constr_mkApp (cMonomorphic_entry, [| ctx |])
  
  let mkPolymorphic_entry names ctx = 
     let names = to_coq_list (Lazy.force tname) names in
     constr_mkApp (cPolymorphic_entry, [| names; ctx |])
    
  let quote_inductive_universes uctx =
    match uctx with
    | Monomorphic_entry uctx -> 
      let ctx = quote_univ_context (Univ.ContextSet.to_context uctx) in
      constr_mkApp (cMonomorphic_entry, [| ctx |])
    | Polymorphic_entry (names, uctx) ->
      let names = CArray.map_to_list quote_name names in
      let names = to_coq_list (Lazy.force tname) names in
      let ctx = quote_univ_context uctx in
      constr_mkApp (cPolymorphic_entry, [| names; ctx |])

  let quote_ugraph (g : UGraph.t) =
    let inst' = quote_univ_instance Univ.Instance.empty in
    let const' = quote_univ_constraints (fst (UGraph.constraints_of_universes g)) in
    let uctx = constr_mkApp (tUContextmake, [|inst' ; const'|]) in
    constr_mkApp (tadd_global_constraints, [|constr_mkApp (cMonomorphic_ctx, [| uctx |]); Lazy.force tinit_graph|])

  let quote_sort s =
    quote_universe (Sorts.univ_of_sort s)

  let quote_sort_family = function
    | Sorts.InProp -> sfProp
    | Sorts.InSet -> sfSet
    | Sorts.InType -> sfType
    | Sorts.InSProp -> sfProp  (* FIXME SProp support *)

  let quote_context_decl na b t =
    constr_mkApp (tmkdecl, [| na; quote_option (Lazy.force tTerm) b; t |])

  let quote_context ctx =
    to_coq_list (Lazy.force tcontext_decl) ctx

  let mk_ctor_list =
    let ctor_list =
      let ctor_info_typ = prod (prod (Lazy.force tident) (Lazy.force tTerm)) (Lazy.force tnat) in
      to_coq_list ctor_info_typ
    in
    fun ls ->
    let ctors = List.map (fun (a,b,c) -> pair (prod (Lazy.force tident) (Lazy.force tTerm)) (Lazy.force tnat)
				              (pair (Lazy.force tident) (Lazy.force tTerm) a b) c) ls in
    ctor_list ctors

  let mk_proj_list d =
    to_coq_list (prod (Lazy.force tident) (Lazy.force tTerm))
                (List.map (fun (a, b) -> pair (Lazy.force tident) (Lazy.force tTerm) a b) d)

  let quote_inductive (kn, i) =
    constr_mkApp (tmkInd, [| kn; i |])

  let rec seq f t =
    if f < t then f :: seq (f + 1) t
    else []


  let mkAnon () = Lazy.force nAnon
  let mkName id = constr_mkApp (nNamed, [| id |])

  let mkRel i = constr_mkApp (tRel, [| i |])
  let mkVar id = constr_mkApp (tVar, [| id |])
  let mkEvar n args = constr_mkApp (tEvar, [| n; to_coq_list (Lazy.force tTerm) (Array.to_list args) |])
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

  let mkProj kn t =
    constr_mkApp (tProj, [| kn; t |])
end
