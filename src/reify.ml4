(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmp" i*)

open Declarations
open Ltac_plugin
open Univ
open Entries
open Names
open Redops
open Genredexpr

let contrib_name = "template-coq"

let toDecl (old: Names.name * ((Constr.constr) option) * Constr.constr) : Context.Rel.Declaration.t =
  let (name,value,typ) = old in
  match value with
  | Some value -> Context.Rel.Declaration.LocalDef (name,value,typ)
  | None -> Context.Rel.Declaration.LocalAssum (name,typ)

let cast_prop = ref (false)
let _ = Goptions.declare_bool_option {
  Goptions.optdepr = false;
  Goptions.optname = "Casting of propositions in template-coq";
  Goptions.optkey = ["Template";"Cast";"Propositions"];
  Goptions.optread = (fun () -> !cast_prop);
  Goptions.optwrite = (fun a -> cast_prop:=a);
}

let cast_types = ref (false)
let _ = Goptions.declare_bool_option {
  Goptions.optdepr = false;
  Goptions.optname = "Casting of all types in template-coq";
  Goptions.optkey = ["Template";"Cast";"Types"];
  Goptions.optread = (fun () -> !cast_types);
  Goptions.optwrite = (fun a -> cast_types:=a);
}

(* whether Set Template Cast Propositions is on, as needed for erasure in Certicoq *)
let is_cast_prop () = !cast_prop

open Pp (* this adds the ++ to the current scope *)

let opt_debug = ref false

let debug (m : unit -> Pp.std_ppcmds) =
  if !opt_debug then
    Feedback.(msg_debug (m ()))
  else
    ()

exception NotSupported of Term.constr * string

let not_supported trm =
  CErrors.user_err (str "Not Supported:" ++ spc () ++ Printer.pr_constr trm)

let not_supported_verb trm rs =
  CErrors.user_err (str "Not Supported raised at " ++ str rs ++ str ":" ++ spc () ++ Printer.pr_constr trm)

let bad_term trm =
  CErrors.user_err (str "Bad term:" ++ spc () ++ Printer.pr_constr trm)

let bad_term_verb trm rs =
  CErrors.user_err (str "Bad term:" ++ spc () ++ Printer.pr_constr trm
                    ++ spc () ++ str " Error: " ++ str rs)

let gen_constant_in_modules locstr dirs s =
  Universes.constr_of_global (Coqlib.gen_reference_in_modules locstr dirs s)

let opt_hnf_ctor_types = ref false

let hnf_type env ty =
  let rec hnf_type continue ty =
    match Term.kind_of_term ty with
      Term.Prod (n,t,b) -> Term.mkProd (n,t,hnf_type true b)
    | Term.LetIn _
      | Term.Cast _
      | Term.App _ when continue ->
       hnf_type false (Reduction.whd_all env ty)
    | _ -> ty
  in
  hnf_type true ty

let split_name s : (Names.DirPath.t * Names.Id.t) =
  let ss = List.rev (Str.split (Str.regexp (Str.quote ".")) s) in
  match ss with
    nm :: rst ->
     let dp = (Names.make_dirpath (List.map Names.id_of_string rst)) in (dp, Names.Id.of_string nm)
  | [] -> raise (Failure "Empty name cannot be quoted")

module Mindset = Names.Mindset

type ('a,'b) sum =
  Left of 'a | Right of 'b

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
end

(** The reifier to Coq values *)
module TemplateCoqQuoter =
struct
  type t = Term.constr

  type quoted_ident = Term.constr (* of type Ast.ident *)
  type quoted_int = Term.constr (* of type nat *)
  type quoted_bool = Term.constr (* of type bool *)
  type quoted_name = Term.constr (* of type Ast.name *)
  type quoted_sort = Term.constr (* of type Ast.universe *)
  type quoted_cast_kind = Term.constr  (* of type Ast.cast_kind *)
  type quoted_kernel_name = Term.constr (* of type Ast.kername *)
  type quoted_inductive = Term.constr (* of type Ast.inductive *)
  type quoted_constraint_type = Term.constr (* of type univ.constraint_type *)
  type quoted_univ_constraint = Term.constr (* of type univ.univ_constraint *)
  type quoted_univ_constraints = Term.constr (* of type univ.constraints *)
  type quoted_univ_instance = Term.constr (* of type univ.universe_instance *)
  type quoted_univ_context = Term.constr (* of type univ.universe_context *)
  type quoted_proj = Term.constr (* of type Ast.projection *)
  type quoted_sort_family = Term.constr (* of type Ast.sort_family *)

  type quoted_decl = Term.constr (* of type Ast.program ??? *)
  type quoted_mind_params = Term.constr (* of type list (Ast.ident * list (ident * local_entry)local_entry) *)
  type quoted_program = Term.constr (* of type Ast.program *)
  type quoted_ind_entry =
    quoted_ident * t * quoted_bool * quoted_ident list * t list

  type quoted_mind_entry = Term.constr (* of type Ast.mutual_inductive_entry *)
  type quoted_mind_finiteness = Term.constr (* of type Ast.mutual_inductive_entry *)
  type quoted_definition_entry = t * t option
  type quoted_entry = Term.constr (* of type option (constant_entry + mutual_inductive_entry) *)
  type quoted_global_reference = Term.constr (* of type Ast.global_reference *)
  type quoted_reduction_strategy = Term.constr (* of type Ast.reductionStrategy *)

  let resolve_symbol (path : string list) (tm : string) : Term.constr =
    gen_constant_in_modules contrib_name [path] tm

  let pkg_datatypes = ["Coq";"Init";"Datatypes"]
  let pkg_string = ["Coq";"Strings";"String"]
  let pkg_reify = ["Template";"Ast"]
  let pkg_univ = ["Template";"kernel";"univ"]
  let pkg_level = ["Template";"kernel";"univ";"Level"]
  let pkg_ugraph = ["Template";"kernel";"uGraph"]
  let ext_pkg_univ s = List.append pkg_univ [s]

  let r_reify = resolve_symbol pkg_reify

  let tString = resolve_symbol pkg_string "String"
  let tEmptyString = resolve_symbol pkg_string "EmptyString"
  let tO = resolve_symbol pkg_datatypes "O"
  let tS = resolve_symbol pkg_datatypes "S"
  let tnat = resolve_symbol pkg_datatypes "nat"
  let ttrue = resolve_symbol pkg_datatypes "true"
  let cSome = resolve_symbol pkg_datatypes "Some"
  let cNone = resolve_symbol pkg_datatypes "None"
  let tfalse = resolve_symbol pkg_datatypes "false"
  let unit_tt = resolve_symbol pkg_datatypes "tt"
  let tAscii = resolve_symbol ["Coq";"Strings";"Ascii"] "Ascii"
  let c_nil = resolve_symbol pkg_datatypes "nil"
  let c_cons = resolve_symbol pkg_datatypes "cons"
  let prod_type = resolve_symbol pkg_datatypes "prod"
  let sum_type = resolve_symbol pkg_datatypes "sum"
  let option_type = resolve_symbol pkg_datatypes "option"
  let bool_type = resolve_symbol pkg_datatypes "bool"
  let cInl = resolve_symbol pkg_datatypes "inl"
  let cInr = resolve_symbol pkg_datatypes "inr"
  let prod a b =
    Term.mkApp (prod_type, [| a ; b |])
  let c_pair = resolve_symbol pkg_datatypes "pair"
  let pair a b f s =
    Term.mkApp (c_pair, [| a ; b ; f ; s |])

    (* reify the constructors in Template.Ast.v, which are the building blocks of reified terms *)
  let nAnon = r_reify "nAnon"
  let nNamed = r_reify "nNamed"
  let kVmCast = r_reify "VmCast"
  let kNative = r_reify "NativeCast"
  let kCast = r_reify "Cast"
  let kRevertCast = r_reify "RevertCast"
  let lProp = resolve_symbol pkg_level "lProp"
  let lSet = resolve_symbol pkg_level "lSet"
  let sfProp = r_reify "InProp"
  let sfSet = r_reify "InSet"
  let sfType = r_reify "InType"
  let tident = r_reify "ident"
  let tIndTy = r_reify "inductive"
  let tmkInd = r_reify "mkInd"
  let tsort_family = r_reify "sort_family"
  let (tTerm,tRel,tVar,tMeta,tEvar,tSort,tCast,tProd,
       tLambda,tLetIn,tApp,tCase,tFix,tConstructor,tConst,tInd,tCoFix,tProj) =
    (r_reify "term", r_reify "tRel", r_reify "tVar", r_reify "tMeta", r_reify "tEvar",
     r_reify "tSort", r_reify "tCast", r_reify "tProd", r_reify "tLambda",
     r_reify "tLetIn", r_reify "tApp", r_reify "tCase", r_reify "tFix",
     r_reify "tConstruct", r_reify "tConst", r_reify "tInd", r_reify "tCoFix", r_reify "tProj")

  let tlevel = resolve_symbol pkg_level "t"
  let tLevel = resolve_symbol pkg_level "Level"
  let tLevelVar = resolve_symbol pkg_level "Var"
  let tunivLe = resolve_symbol pkg_univ "Le"
  let tunivLt = resolve_symbol pkg_univ "Lt"
  let tunivEq = resolve_symbol pkg_univ "Eq"
  let tUContextmake = resolve_symbol (ext_pkg_univ "UContext") "make"
  (* let tConstraintempty = resolve_symbol (ext_pkg_univ "Constraint") "empty" *)
  let tConstraintempty = Universes.constr_of_global (Coqlib.find_reference "template coq bug" (ext_pkg_univ "Constraint") "empty")
  let tConstraintadd = Universes.constr_of_global (Coqlib.find_reference "template coq bug" (ext_pkg_univ "Constraint") "add")
  let tmake_univ_constraint = resolve_symbol pkg_univ "make_univ_constraint"
  let tinit_graph = resolve_symbol pkg_ugraph "init_graph"
  let tadd_constraints = resolve_symbol pkg_ugraph  "add_constraints"

  let (tdef,tmkdef) = (r_reify "def", r_reify "mkdef")
  let (tLocalDef,tLocalAssum,tlocal_entry) = (r_reify "LocalDef", r_reify "LocalAssum", r_reify "local_entry")

  let (cFinite,cCoFinite,cBiFinite) = (r_reify "Finite", r_reify "CoFinite", r_reify "BiFinite")
  let (pConstr,pType,pAxiom,pIn) =
    (r_reify "PConstr", r_reify "PType", r_reify "PAxiom", r_reify "PIn")
  let tinductive_body = r_reify "inductive_body"
  let tmkinductive_body = r_reify "mkinductive_body"
  let tBuild_minductive_decl = r_reify "Build_minductive_decl"

  let tMutual_inductive_entry = r_reify "mutual_inductive_entry"
  let tOne_inductive_entry = r_reify "one_inductive_entry"
  let tBuild_mutual_inductive_entry = r_reify "Build_mutual_inductive_entry"
  let tBuild_one_inductive_entry = r_reify "Build_one_inductive_entry"
  let tConstant_entry = r_reify "constant_entry"
  let cParameterEntry = r_reify "ParameterEntry"
  let cDefinitionEntry = r_reify "DefinitionEntry"
  let cParameter_entry = r_reify "Build_parameter_entry"
  let cDefinition_entry = r_reify "Build_definition_entry"

  let (tcbv, tcbn, thnf, tall, tlazy) = (r_reify "cbv", r_reify "cbn", r_reify "hnf", r_reify "all", r_reify "lazy")

  let (tglobal_reference, tConstRef, tIndRef, tConstructRef) = (r_reify "global_reference", r_reify "ConstRef", r_reify "IndRef", r_reify "ConstructRef")

  let (tmReturn, tmBind, tmQuote, tmQuoteRec, tmEval, tmDefinition, tmAxiom, tmLemma, tmFreshName, tmAbout, tmCurrentModPath,
       tmMkDefinition, tmMkInductive, tmPrint, tmFail, tmQuoteInductive, tmQuoteConstant, tmQuoteUniverses, tmUnquote, tmUnquoteTyped) =
    (r_reify "tmReturn", r_reify "tmBind", r_reify "tmQuote", r_reify "tmQuoteRec", r_reify "tmEval", r_reify "tmDefinition",
     r_reify "tmAxiom", r_reify "tmLemma", r_reify "tmFreshName", r_reify "tmAbout", r_reify "tmCurrentModPath",
     r_reify "tmMkDefinition", r_reify "tmMkInductive", r_reify "tmPrint", r_reify "tmFail", r_reify "tmQuoteInductive", r_reify "tmQuoteConstant",
     r_reify "tmQuoteUniverses", r_reify "tmUnquote", r_reify "tmUnquoteTyped")

  (* let pkg_specif = ["Coq";"Init";"Specif"] *)
  (* let texistT = resolve_symbol pkg_specif "existT" *)
  let texistT_typed_term = r_reify "existT_typed_term"

  let to_coq_list typ =
    let the_nil = Term.mkApp (c_nil, [| typ |]) in
    let rec to_list (ls : Term.constr list) : Term.constr =
      match ls with
	[] -> the_nil
      | l :: ls ->
	Term.mkApp (c_cons, [| typ ; l ; to_list ls |])
    in to_list

  let int_to_nat =
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
	    let result = Term.mkApp (tS, [| recurse (i - 1) |]) in
	    let _ = Hashtbl.add cache i result in
	    result
    in
    fun i ->
      assert (i >= 0) ;
      recurse i

  let quote_bool b =
    if b then ttrue else tfalse

  let quote_char i =
    Term.mkApp (tAscii, Array.of_list (List.map (fun m -> quote_bool ((i land m) = m))
					 (List.rev [128;64;32;16;8;4;2;1])))

  let chars = Array.init 255 quote_char

  let quote_char c = chars.(int_of_char c)

  let string_hash = Hashtbl.create 420

  let to_string s =
    let len = String.length s in
    let rec go from acc =
      if from < 0 then acc
      else
        let term = Term.mkApp (tString, [| quote_char (String.get s from) ; acc |]) in
        go (from - 1) term
    in
    go (len - 1) tEmptyString

  let quote_string s =
    try Hashtbl.find string_hash s
    with Not_found ->
      let term = to_string s in
      Hashtbl.add string_hash s term; term

  let quote_ident i =
    let s = Names.string_of_id i in
    quote_string s

  let quote_name n =
    match n with
      Names.Name id -> Term.mkApp (nNamed, [| quote_ident id |])
    | Names.Anonymous -> nAnon

  let quote_cast_kind k =
    match k with
      Term.VMcast -> kVmCast
    | Term.DEFAULTcast -> kCast
    | Term.REVERTcast -> kRevertCast
    | Term.NATIVEcast -> kNative

  let string_of_level s =
    to_string (Univ.Level.to_string s)

  let quote_level l =
    if Level.is_prop l then lProp
    else if Level.is_set l then lSet
    else match Level.var_index l with
         | Some x -> Term.mkApp (tLevelVar, [| int_to_nat x |])
         | None -> Term.mkApp (tLevel, [| string_of_level l|])

  let quote_universe s =
    (* hack because we can't recover the list of level*int *)
    (* todo : map on LSet is now exposed in Coq trunk, we should use it to remove this hack *)
    let levels = LSet.elements (Universe.levels s) in
    let levels = List.map (fun l -> let l' = quote_level l in
                                    (* is indeed i always 0 or 1 ? *)
                                    let b' = quote_bool (Universe.exists (fun (l2,i) -> Level.equal l l2 && i = 1) s) in
                                    pair tlevel bool_type l' b')
                          levels in
    to_coq_list (prod tlevel bool_type) levels

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
    Term.mkApp (tmake_univ_constraint, [| l1; ct; l2 |])

  let quote_univ_constraints const =
    let const = Univ.Constraint.elements const in
    List.fold_left (fun tm c ->
        let c = quote_univ_constraint c in
        Term.mkApp (tConstraintadd, [| c; tm|])
      ) tConstraintempty const

  let quote_univ_context uctx =
    let inst = Univ.UContext.instance uctx in
    let const = Univ.UContext.constraints uctx in
    let inst' = quote_univ_instance inst in
    let const' = quote_univ_constraints const in
    Term.mkApp (tUContextmake, [|inst'; const'|])


  let quote_ugraph (g : UGraph.t) =
    let inst' = quote_univ_instance Univ.Instance.empty in
    let const' = quote_univ_constraints (UGraph.constraints_of_universes g) in
    let uctx = Term.mkApp (tUContextmake, [|inst' ; const'|]) in
    Term.mkApp (tadd_constraints, [|uctx; tinit_graph|])

  let quote_sort s =
    quote_universe (Sorts.univ_of_sort s)

  let quote_sort_family = function
    | Sorts.InProp -> sfProp
    | Sorts.InSet -> sfSet
    | Sorts.InType -> sfType

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
    Term.mkApp (tmkInd, [| kn; i |])

  let mkAnon = nAnon
  let mkName id = Term.mkApp (nNamed, [| id |])
  let quote_int = int_to_nat
  let quote_kn kn = quote_string (Names.string_of_kn kn)
  let mkRel i = Term.mkApp (tRel, [| i |])
  let mkVar id = Term.mkApp (tVar, [| id |])
  let mkMeta i = Term.mkApp (tMeta, [| i |])
  let mkEvar n args = Term.mkApp (tEvar, [| n; to_coq_list tTerm (Array.to_list args) |])
  let mkSort s = Term.mkApp (tSort, [| s |])
  let mkCast c k t = Term.mkApp (tCast, [| c ; k ; t |])
  let mkConst kn u = Term.mkApp (tConst, [| kn ; u |])
  let mkProd na t b =
    Term.mkApp (tProd, [| na ; t ; b |])
  let mkLambda na t b =
    Term.mkApp (tLambda, [| na ; t ; b |])
  let mkApp f xs =
    Term.mkApp (tApp, [| f ; to_coq_list tTerm (Array.to_list xs) |])

  let mkLetIn na t t' b =
    Term.mkApp (tLetIn, [| na ; t ; t' ; b |])

  let rec seq f t =
    if f < t then f :: seq (f + 1) t
    else []

  let mkFix ((a,b),(ns,ts,ds)) =
    let mk_fun xs i =
      Term.mkApp (tmkdef, [| tTerm ; Array.get ns i ;
                             Array.get ts i ; Array.get ds i ; Array.get a i |]) :: xs
    in
    let defs = List.fold_left mk_fun [] (seq 0 (Array.length a)) in
    let block = to_coq_list (Term.mkApp (tdef, [| tTerm |])) (List.rev defs) in
    Term.mkApp (tFix, [| block ; b |])

  let mkConstruct (ind, i) u =
    Term.mkApp (tConstructor, [| ind ; i ; u |])

  let mkCoFix (a,(ns,ts,ds)) =
    let mk_fun xs i =
      Term.mkApp (tmkdef, [| tTerm ; Array.get ns i ;
                             Array.get ts i ; Array.get ds i ; tO |]) :: xs
    in
    let defs = List.fold_left mk_fun [] (seq 0 (Array.length ns)) in
    let block = to_coq_list (Term.mkApp (tdef, [| tTerm |])) (List.rev defs) in
    Term.mkApp (tCoFix, [| block ; a |])

  let mkInd i u = Term.mkApp (tInd, [| i ; u |])

  let mkCase (ind, npar) nargs p c brs =
    let info = pair tIndTy tnat ind npar in
    let branches = List.map2 (fun br nargs ->  pair tnat tTerm nargs br) brs nargs in
    let tl = prod tnat tTerm in
    Term.mkApp (tCase, [| info ; p ; c ; to_coq_list tl branches |])

  let quote_proj ind pars args =
    pair (prod tIndTy tnat) tnat (pair tIndTy tnat ind pars) args

  let mkProj kn t =
    Term.mkApp (tProj, [| kn; t |])

  let mkMutualInductive kn uctx p ls =
    let result = to_coq_list tinductive_body
         (List.map (fun (a,b,c,d,e) ->
              let c = to_coq_list tsort_family c in
              let d = mk_ctor_list d in
              let e = mk_proj_list e in
              Term.mkApp (tmkinductive_body, [| a; b; c; d; e |])) ls) in
    Term.mkApp (pType, [| kn; uctx; p; result |])

  let mkConstant kn uctx ty c =
    Term.mkApp (pConstr, [| kn; uctx ; ty; c |])

  let mkAxiom kn uctx t =
    Term.mkApp (pAxiom, [| kn; uctx; t |])

  let mkExt x acc = Term.mkApp (x, [| acc |])
  let mkIn t = Term.mkApp (pIn, [| t |])

  (* let quote_mind_finiteness (f: Decl_kinds.recursivity_kind) = *)
  (*   match f with *)
  (*   | Decl_kinds.Finite -> cFinite *)
  (*   | Decl_kinds.CoFinite -> cCoFinite *)
  (*   | Decl_kinds.BiFinite -> cBiFinite *)

  (* let make_one_inductive_entry (iname, arity, templatePoly, consnames, constypes) = *)
  (*   let consnames = to_coq_list tident consnames in *)
  (*   let constypes = to_coq_list tTerm constypes in *)
  (*   Term.mkApp (tBuild_one_inductive_entry, [| iname; arity; templatePoly; consnames; constypes |]) *)

  (* let quote_mind_params l = *)
  (*   let pair i l = pair tident tlocal_entry i l in *)
  (*   let map (id, ob) = *)
  (*     match ob with *)
  (*     | Left b -> pair id (Term.mkApp (tLocalDef,[|b|])) *)
  (*     | Right t -> pair id (Term.mkApp (tLocalAssum,[|t|])) *)
  (*   in *)
  (*   let the_prod = Term.mkApp (prod_type,[|tident; tlocal_entry|]) in *)
  (*   to_coq_list the_prod (List.map map l) *)

  (* let quote_mutual_inductive_entry (mf, mp, is, mpol) = *)
  (*   let is = to_coq_list tOne_inductive_entry (List.map make_one_inductive_entry is) in *)
  (*   let mpr = Term.mkApp (cNone, [|bool_type|]) in *)
  (*   let mr = Term.mkApp (cNone, [|Term.mkApp (option_type, [|tident|])|])  in *)
  (*   Term.mkApp (tBuild_mutual_inductive_entry, [| mr; mf; mp; is; mpol; mpr |]) *)


  (* let quote_entry decl = *)
  (*   let opType = Term.mkApp(sum_type, [|tConstant_entry;tMutual_inductive_entry|]) in *)
  (*   let mkSome c t = Term.mkApp (cSome, [|opType; Term.mkApp (c, [|tConstant_entry;tMutual_inductive_entry; t|] )|]) in *)
  (*   let mkSomeDef = mkSome cInl in *)
  (*   let mkSomeInd  = mkSome cInr in *)
  (*   let mkParameterEntry ty = *)
  (*     mkSomeDef (Term.mkApp (cParameterEntry, [| Term.mkApp (cParameter_entry, [|ty|]) |])) *)
  (*   in *)
  (*   let mkDefinitionEntry ty body = *)
  (*     let b = Term.mkApp (cDefinitionEntry, [| Term.mkApp (cDefinition_entry, [|ty;body|]) |]) in *)
  (*     mkSomeDef b *)
  (*   in *)
  (*   match decl with *)
  (*   | Some (Left (ty, body)) -> *)
  (*      (match body with *)
  (*       | None -> mkParameterEntry ty *)
  (*       | Some b -> mkDefinitionEntry ty b) *)
  (*   | Some (Right mind) -> *)
  (*      mkSomeInd mind *)
  (*   | None -> Constr.mkApp (cNone, [| opType |]) *)


  let quote_global_reference : Globnames.global_reference -> quoted_global_reference = function
    | Globnames.VarRef _ -> CErrors.user_err (str "VarRef unsupported")
    | Globnames.ConstRef c ->
       let kn = quote_kn (Names.Constant.canonical c) in
       Term.mkApp (tConstRef, [|kn|])
    | Globnames.IndRef (i, n) ->
       let kn = quote_kn (Names.MutInd.canonical i) in
       let n = quote_int n in
       Term.mkApp (tIndRef, [|quote_inductive (kn ,n)|])
    | Globnames.ConstructRef ((i, n), k) ->
       let kn = quote_kn (Names.MutInd.canonical i) in
       let n = quote_int n in
       let k = (quote_int (k - 1)) in
       Term.mkApp (tConstructRef, [|quote_inductive (kn ,n); k|])

end



module Reify(Q : Quoter) =
struct

  let push_rel decl (in_prop, env) = (in_prop, Environ.push_rel decl env)
  let push_rel_context ctx (in_prop, env) = (in_prop, Environ.push_rel_context ctx env)

  let castSetProp (sf:Term.sorts) t =
    if !cast_types then
      let sf = Term.family_of_sort sf in
      let k = Q.quote_cast_kind Constr.DEFAULTcast in
      if sf == Term.InProp
      then Q.mkCast t k (Q.mkSort (Q.quote_sort Sorts.prop))
      else if sf == Term.InSet
      then Q.mkCast t k (Q.mkSort (Q.quote_sort Sorts.set))
      else t
    else t

  let noteTypeAsCast t typ =
    if !cast_types then
      Q.mkCast t (Q.quote_cast_kind Constr.DEFAULTcast) typ
    else t

  let getSort env (t:Term.constr) =
    if !cast_types then
      Retyping.get_sort_of env Evd.empty (EConstr.of_constr t)
    else Sorts.prop

  let getType env (t:Term.constr) : Term.constr =
    EConstr.to_constr Evd.empty (Retyping.get_type_of env Evd.empty (EConstr.of_constr t))

  (* given a term of shape \x1 x2 ..., T, it puts a cast around T if T is a Set or a Prop,
     lambdas like this arise in the case-return type in matches, i.e. the part between return and with in
     match _  as   _ in  _ return __ with *)
  let rec putReturnTypeInfo (env : Environ.env) (t: Term.constr) : Term.constr =
    if !cast_types then
      match Term.kind_of_term t with
      | Term.Lambda (n,t,b) ->
         Term.mkLambda (n,t,putReturnTypeInfo (Environ.push_rel (toDecl (n, None, t)) env) b)
      | _ ->
         let ty = getType env t in
         Term.mkCast (t,Term.DEFAULTcast,ty)
    else t

  open Declarations
  let get_abstract_inductive_universes iu =
    match iu with
    | Monomorphic_ind ctx -> ctx (* FIXME is it ok ??? *)
    | Polymorphic_ind ctx -> Univ.AUContext.repr ctx
    | Cumulative_ind cumi ->
       let cumi = Univ.instantiate_cumulativity_info cumi in
       Univ.CumulativityInfo.univ_context cumi  (* FIXME check also *)

  let get_constant_uctx = function
    | Monomorphic_const ctx -> ctx
    | Polymorphic_const ctx -> Univ.AUContext.repr ctx

  let quote_term_remember
      (add_constant : Names.kernel_name -> 'a -> 'a)
      (add_inductive : Names.inductive -> 'a -> 'a) =
    let rec quote_term (acc : 'a) env trm =
      let aux acc env trm =
      match Term.kind_of_term trm with
	Term.Rel i -> (Q.mkRel (Q.quote_int (i - 1)), acc)
      | Term.Var v -> (Q.mkVar (Q.quote_ident v), acc)
      | Term.Meta n -> (Q.mkMeta (Q.quote_int n), acc)
      | Term.Evar (n,args) ->
	let (acc,args') =
	  CArray.fold_map (fun acc x ->
	    let (x,acc) = quote_term acc env x in acc,x)
	                  acc args in
         (Q.mkEvar (Q.quote_int (Evar.repr n)) args', acc)
      | Term.Sort s -> (Q.mkSort (Q.quote_sort s), acc)
      | Term.Cast (c,k,t) ->
	let (c',acc) = quote_term acc env c in
	let (t',acc) = quote_term acc env t in
        let k' = Q.quote_cast_kind k in
        (Q.mkCast c' k' t', acc)

      | Term.Prod (n,t,b) ->
	let (t',acc) = quote_term acc env t in
        let sf = getSort (snd env) t in
        let env = push_rel (toDecl (n, None, t)) env in
        let sfb = getSort (snd env) b in
	let (b',acc) = quote_term acc env b in
        (Q.mkProd (Q.quote_name n) (castSetProp sf t') (castSetProp sfb b'), acc)

      | Term.Lambda (n,t,b) ->
	let (t',acc) = quote_term acc env t in
        let sf = getSort (snd env) t  in
	let (b',acc) = quote_term acc (push_rel (toDecl (n, None, t)) env) b in
	(Q.mkLambda (Q.quote_name n) (castSetProp sf t') b', acc)

      | Term.LetIn (n,e,t,b) ->
	let (e',acc) = quote_term acc env e in
	let (t',acc) = quote_term acc env t in
	let (b',acc) = quote_term acc (push_rel (toDecl (n, Some e, t)) env) b in
	(Q.mkLetIn (Q.quote_name n) e' t' b', acc)

      | Term.App (f,xs) ->
	let (f',acc) = quote_term acc env f in
	let (acc,xs') =
	  CArray.fold_map (fun acc x ->
	    let (x,acc) = quote_term acc env x in acc,x)
	    acc xs in
	(Q.mkApp f' xs', acc)

      | Term.Const (c,pu) ->
         let kn = Names.Constant.canonical c in
         let pu' = Q.quote_univ_instance pu in
	 (Q.mkConst (Q.quote_kn kn) pu', add_constant kn acc)

      | Term.Construct (((ind,i),c),pu) ->
         (Q.mkConstruct (Q.quote_inductive (Q.quote_kn (Names.MutInd.canonical ind), Q.quote_int i),
                         Q.quote_int (c - 1))
            (Q.quote_univ_instance pu), add_inductive (ind,i) acc)

      | Term.Ind ((ind,i),pu) ->
         (Q.mkInd (Q.quote_inductive (Q.quote_kn (Names.MutInd.canonical ind), Q.quote_int i))
            (Q.quote_univ_instance pu), add_inductive (ind,i) acc)

      | Term.Case (ci,typeInfo,discriminant,e) ->
         let ind = Q.quote_inductive (Q.quote_kn (Names.MutInd.canonical (fst ci.Term.ci_ind)),
                                      Q.quote_int (snd ci.Term.ci_ind)) in
         let npar = Q.quote_int ci.Term.ci_npar in
         let typeInfo = putReturnTypeInfo (snd env) typeInfo in
	 let (qtypeInfo,acc) = quote_term acc env typeInfo in
	 let (qdiscriminant,acc) = quote_term acc env discriminant in
         let qdiscriminant,acc =
           if !cast_types then
             let discriminantType = getType (snd env) discriminant in
             let (discriminantType,acc) = (quote_term acc env discriminantType) in
             noteTypeAsCast qdiscriminant discriminantType, acc
           else qdiscriminant, acc
         in
	 let (branches,nargs,acc) =
           CArray.fold_left2 (fun (xs,nargs,acc) x narg ->
               let (x,acc) = quote_term acc env x in
               let narg = Q.quote_int narg in
               (x :: xs, narg :: nargs, acc))
             ([],[],acc) e ci.Term.ci_cstr_nargs in
         (Q.mkCase (ind, npar) (List.rev nargs) qtypeInfo qdiscriminant (List.rev branches), acc)

      | Term.Fix fp -> quote_fixpoint acc env fp
      | Term.CoFix fp -> quote_cofixpoint acc env fp
      | Term.Proj (p,c) ->
         let proj = Environ.lookup_projection p (snd env) in
         let ind = proj.Declarations.proj_ind in
         let ind = Q.quote_inductive (Q.quote_kn (Names.MutInd.canonical ind),
                                      Q.quote_int 0) in
         let pars = Q.quote_int proj.Declarations.proj_npars in
         let arg = Q.quote_int proj.Declarations.proj_arg in
         let p' = Q.quote_proj ind pars arg in
         let kn = Names.Constant.canonical (Names.Projection.constant p) in
         let t', acc = quote_term acc env c in
         (Q.mkProj p' t', add_constant kn acc)
      in
      let in_prop, env' = env in
      if is_cast_prop () && not in_prop then
        let ty =
          let trm = EConstr.of_constr trm in
          try Retyping.get_type_of env' Evd.empty trm
          with e ->
            Feedback.msg_debug (str"Anomaly trying to get the type of: " ++
                                  Termops.print_constr_env (snd env) Evd.empty trm);
            raise e
        in
        let sf =
          try Retyping.get_sort_family_of env' Evd.empty ty
          with e ->
            Feedback.msg_debug (str"Anomaly trying to get the sort of: " ++
                                  Termops.print_constr_env (snd env) Evd.empty ty);
            raise e
        in
        if sf == Term.InProp then
          aux acc (true, env')
              (Term.mkCast (trm, Term.DEFAULTcast,
                            Term.mkCast (EConstr.to_constr Evd.empty ty, Term.DEFAULTcast, Term.mkProp)))
        else aux acc env trm
      else aux acc env trm
    and quote_recdecl (acc : 'a) env b (ns,ts,ds) =
      let ctxt =
        CArray.map2_i (fun i na t -> (Context.Rel.Declaration.LocalAssum (na, Vars.lift i t))) ns ts in
      let envfix = push_rel_context (CArray.rev_to_list ctxt) env in
      let ns' = Array.map Q.quote_name ns in
      let b' = Q.quote_int b in
      let acc, ts' =
        CArray.fold_map (fun acc t -> let x,acc = quote_term acc env t in acc, x) acc ts in
      let acc, ds' =
        CArray.fold_map (fun acc t -> let x,y = quote_term acc envfix t in y, x) acc ds in
      ((b',(ns',ts',ds')), acc)
    and quote_fixpoint acc env t =
      let ((a,b),decl) = t in
      let a' = Array.map Q.quote_int a in
      let (b',decl'),acc = quote_recdecl acc env b decl in
      (Q.mkFix ((a',b'),decl'), acc)
    and quote_cofixpoint acc env t =
      let (a,decl) = t in
      let (a',decl'),acc = quote_recdecl acc env a decl in
      (Q.mkCoFix (a',decl'), acc)
    and quote_minductive_type (acc : 'a) env (t : Names.mutual_inductive) =
      let mib = Environ.lookup_mind t (snd env) in
      let uctx = get_abstract_inductive_universes mib.Declarations.mind_universes in
      let inst = Univ.UContext.instance uctx in
      let indtys =
        Declarations.(CArray.map_to_list (fun oib ->
           let ty = Inductive.type_of_inductive (snd env) ((mib,oib),inst) in
           (Context.Rel.Declaration.LocalAssum (Names.Name oib.mind_typename, ty))) mib.mind_packets)
      in
      let envind = push_rel_context (List.rev indtys) env in
      let ref_name = Q.quote_kn (Names.canonical_mind t) in
      let (ls,acc) =
	List.fold_left (fun (ls,acc) oib ->
	  let named_ctors =
	    CList.combine3
	      Declarations.(Array.to_list oib.mind_consnames)
	      Declarations.(Array.to_list oib.mind_user_lc)
	      Declarations.(Array.to_list oib.mind_consnrealargs)
	  in
          let indty = Inductive.type_of_inductive (snd env) ((mib,oib),inst) in
          let indty, acc = quote_term acc env indty in
	  let (reified_ctors,acc) =
	    List.fold_left (fun (ls,acc) (nm,ty,ar) ->
	      debug (fun () -> Pp.(str "XXXX" ++ spc () ++
                            bool !opt_hnf_ctor_types)) ;
	      let ty = if !opt_hnf_ctor_types then hnf_type (snd envind) ty else ty in
	      let (ty,acc) = quote_term acc envind ty in
	      ((Q.quote_ident nm, ty, Q.quote_int ar) :: ls, acc))
	      ([],acc) named_ctors
	  in
          let projs, acc =
            match mib.Declarations.mind_record with
            | Some (Some (id, csts, ps)) ->
               let ctxwolet = Termops.smash_rel_context mib.Declarations.mind_params_ctxt in
               let indty = Term.mkApp (Term.mkIndU ((t,0),inst),
                                       Context.Rel.to_extended_vect Constr.mkRel 0 ctxwolet) in
               let indbinder = Context.Rel.Declaration.LocalAssum (Names.Name id,indty) in
               let envpars = push_rel_context (indbinder :: ctxwolet) env in
               let ps, acc = CArray.fold_right2 (fun cst pb (ls,acc) ->
                 let (ty, acc) = quote_term acc envpars pb.Declarations.proj_type in
                 let kn = Names.KerName.label (Names.Constant.canonical cst) in
                 let na = Q.quote_ident (Names.Label.to_id kn) in
                 ((na, ty) :: ls, acc)) csts ps ([],acc)
               in ps, acc
            | _ -> [], acc
          in
          let sf = List.map Q.quote_sort_family oib.Declarations.mind_kelim in
	  Declarations.((Q.quote_ident oib.mind_typename, indty, sf, (List.rev reified_ctors), projs) :: ls, acc))
	  ([],acc) Declarations.((Array.to_list mib.mind_packets))
      in
      let params = Q.quote_int mib.Declarations.mind_nparams in
      let uctx = Q.quote_univ_context (get_abstract_inductive_universes mib.Declarations.mind_universes) in
      Q.mkMutualInductive ref_name uctx params (List.rev ls), acc
    in ((fun acc env -> quote_term acc (false, env)),
        (fun acc env -> quote_minductive_type acc (false, env)))

  let quote_term env trm =
    (try
      let u = Sorts.univ_of_sort (Term.destSort trm) in
      Feedback.msg_debug (Printer.pr_constr trm);
      Feedback.msg_debug (Univ.Universe.pr u);
    with
    | _ -> ());
    let (fn,_) = quote_term_remember (fun _ () -> ()) (fun _ () -> ()) in
    fst (fn () env trm)

  let quote_mind_decl env trm =
    let (_,fn) = quote_term_remember (fun _ () -> ()) (fun _ () -> ()) in
    fst (fn () env trm)

  type defType =
    Ind of Names.inductive
  | Const of Names.kernel_name

  let quote_term_rec env trm =
    let visited_terms = ref Names.KNset.empty in
    let visited_types = ref Mindset.empty in
    let constants = ref [] in
    let add quote_term quote_type trm acc =
      match trm with
      | Ind (mi,idx) ->
	let t = mi in
	if Mindset.mem t !visited_types then ()
	else
	  begin
	    let (result,acc) =
              try quote_type acc env mi
              with e ->
                Feedback.msg_debug (str"Exception raised while checking " ++ Names.pr_mind mi);
                raise e
            in
	    visited_types := Mindset.add t !visited_types ;
	    constants := result :: !constants
	  end
      | Const kn ->
	if Names.KNset.mem kn !visited_terms then ()
	else
	  begin
	    visited_terms := Names.KNset.add kn !visited_terms ;
            let c = Names.Constant.make kn kn in
	    let cd = Environ.lookup_constant c env in
	    let do_body pu ty body =
	      let (result,acc) =
		try quote_term acc (Global.env ()) body
                with e ->
                  Feedback.msg_debug (str"Exception raised while checking body of " ++ Names.pr_kn kn);
                  raise e
	      in
	      constants := Q.mkConstant (Q.quote_kn kn) pu ty result :: !constants
	    in
            let uctx = Q.quote_univ_context (get_constant_uctx cd.const_universes) in
            let ty, acc =
              let ty =
                match cd.const_type with
	        | RegularArity ty -> ty
	        | TemplateArity (ctx,ar) ->
                   Term.it_mkProd_or_LetIn (Constr.mkSort (Sorts.Type ar.template_level)) ctx
              in
              (try quote_term acc (Global.env ()) ty
               with e ->
                 Feedback.msg_debug (str"Exception raised while checking type of " ++ Names.pr_kn kn);
                 raise e)
            in
	      match cd.const_body with
		Undef _ -> constants := Q.mkAxiom (Q.quote_kn kn) uctx ty :: !constants
	      | Def cs ->
		 do_body uctx ty (Mod_subst.force_constr cs)
	      | OpaqueDef lc ->
		 do_body uctx ty (Opaqueproof.force_proof (Global.opaque_tables ()) lc)
	  end
    in
    let (quote_rem,quote_typ) =
      let a = ref (fun _ _ _ -> assert false) in
      let b = ref (fun _ _ _ -> assert false) in
      let (x,y) =
	quote_term_remember (fun x () -> add !a !b (Const x) ())
	                    (fun y () -> add !a !b (Ind y) ())
      in
      a := x ;
      b := y ;
      (x,y)
    in
    let (x,acc) = quote_rem () env trm
    in List.fold_left (fun acc x -> Q.mkExt x acc)
                      (Q.mkIn x) !constants

  (* let quote_one_ind envA envC (mi:Entries.one_inductive_entry) = *)
  (*   let iname = Q.quote_ident mi.mind_entry_typename  in *)
  (*   let arity = quote_term envA mi.mind_entry_arity in *)
  (*   let templatePoly = Q.quote_bool mi.mind_entry_template in *)
  (*   let consnames = List.map Q.quote_ident (mi.mind_entry_consnames) in *)
  (*   let constypes = List.map (quote_term envC) (mi.mind_entry_lc) in *)
  (*   (iname, arity, templatePoly, consnames, constypes) *)

  (* let process_local_entry *)
  (*       (f: 'a -> Term.constr option (\* body *\) -> Term.constr (\* type *\) -> Names.Id.t -> Environ.env -> 'a) *)
  (*       ((env,a):(Environ.env*'a)) *)
  (*       ((n,le):(Names.Id.t * Entries.local_entry)) *)
  (*     :  (Environ.env * 'a) = *)
  (*   match le with *)
  (*   | Entries.LocalAssumEntry t -> (Environ.push_rel (toDecl (Names.Name n,None,t)) env, f a None t n env) *)
  (*   | Entries.LocalDefEntry b -> *)
  (*      let typ = getType env b in *)
  (*      (Environ.push_rel (toDecl (Names.Name n, Some b, typ)) env, f a (Some b) typ n env) *)


  (* let quote_mind_params env (params:(Names.Id.t * Entries.local_entry) list) = *)
  (*   let f lr ob t n env = *)
  (*     match ob with *)
  (*     | Some b -> (Q.quote_ident n, Left (quote_term env b))::lr *)
  (*     | None -> *)
  (*        let sf = getSort env t in *)
  (*        let t' = castSetProp sf (quote_term env t) in *)
  (*        (Q.quote_ident n, Right t')::lr in *)
  (*   let (env, params) = List.fold_left (process_local_entry f) (env,[]) (List.rev params) in *)
  (*   (env, Q.quote_mind_params (List.rev params)) *)

  (* let mind_params_as_types ((env,t):Environ.env*Term.constr) (params:(Names.Id.t * Entries.local_entry) list) : *)
  (*       Environ.env*Term.constr = *)
  (*   List.fold_left (process_local_entry (fun tr ob typ n env -> Term.mkProd_or_LetIn (toDecl (Names.Name n,ob,typ)) tr)) (env,t) *)
  (*     (List.rev params) *)

  (* let quote_mut_ind env (mi:Declarations.mutual_inductive_body) = *)
  (*  let t= Discharge.process_inductive ([],Univ.AUContext.empty) (Names.Cmap.empty,Names.Mindmap.empty) mi in *)
  (*   let mf = Q.quote_mind_finiteness t.mind_entry_finite in *)
  (*   let mp = (snd (quote_mind_params env (t.mind_entry_params))) in *)
  (*   (\* before quoting the types of constructors, we need to enrich the environment with the inductives *\) *)
  (*   let one_arities = *)
  (*     List.map *)
  (*       (fun x -> (x.mind_entry_typename, *)
  (*                  snd (mind_params_as_types (env,x.mind_entry_arity) (t.mind_entry_params)))) *)
  (*       t.mind_entry_inds in *)
  (*   (\* env for quoting constructors of inductives. First push inductices, then params *\) *)
  (*   let envC = List.fold_left (fun env p -> Environ.push_rel (toDecl (Names.Name (fst p), None, snd p)) env) env (one_arities) in *)
  (*   let (envC,_) = List.fold_left (process_local_entry (fun _ _ _ _ _ -> ())) (envC,()) (List.rev (t.mind_entry_params)) in *)
  (*   (\* env for quoting arities of inductives -- just push the params *\) *)
  (*   let (envA,_) = List.fold_left (process_local_entry (fun _ _ _ _ _ -> ())) (env,()) (List.rev (t.mind_entry_params)) in *)
  (*   let is = List.map (quote_one_ind envA envC) t.mind_entry_inds in *)
  (*   let mpol = Q.quote_bool false in *)
  (*   Q.quote_mutual_inductive_entry (mf, mp, is, mpol) *)

  (* let quote_entry bypass env evm (name:string) = *)
  (*   let (dp, nm) = split_name name in *)
  (*   let entry = *)
  (*     match Nametab.locate (Libnames.make_qualid dp nm) with *)
  (*     | Globnames.ConstRef c -> *)
  (*        let cd = Environ.lookup_constant c env in *)
  (*        let ty = *)
  (*          match cd.const_type with *)
  (*          | RegularArity ty -> quote_term env ty *)
  (*          | TemplateArity _ -> *)
  (*             CErrors.user_err (Pp.str "Cannot reify deprecated template-polymorphic constant types") *)
  (*        in *)
  (*        let body = match cd.const_body with *)
  (*          | Undef _ -> None *)
  (*          | Def cs -> Some (quote_term env (Mod_subst.force_constr cs)) *)
  (*          | OpaqueDef cs -> *)
  (*             if bypass *)
  (*             then Some (quote_term env (Opaqueproof.force_proof (Global.opaque_tables ()) cs)) *)
  (*             else None *)
  (*        in Some (Left (ty, body)) *)

  (*     | Globnames.IndRef ni -> *)
  (*        let c = Environ.lookup_mind (fst ni) env in (\* FIX: For efficienctly, we should also export (snd ni)*\) *)
  (*        let miq = quote_mut_ind env c in *)
  (*        Some (Right miq) *)
  (*     | Globnames.ConstructRef _ -> None (\* FIX?: return the enclusing mutual inductive *\) *)
  (*     | Globnames.VarRef _ -> None *)
  (*   in Q.quote_entry entry *)
end

module TermReify = Reify(TemplateCoqQuoter)



let reduce_hnf env evm (trm : Term.constr) =
  let trm = Tacred.hnf_constr env evm (EConstr.of_constr trm) in
  (evm, EConstr.to_constr evm trm)

let reduce_all env evm ?(red=Genredexpr.Cbv Redops.all_flags) trm =
  let red, _ = Redexpr.reduction_of_red_expr env red in
  let evm, red = red env evm (EConstr.of_constr trm) in
  (evm, EConstr.to_constr evm red)

let rec app_full trm acc =
  match Term.kind_of_term trm with
    Term.App (f, xs) -> app_full f (Array.to_list xs @ acc)
  | _ -> (trm, acc)


module Denote =
struct

  open TemplateCoqQuoter

  let rec nat_to_int trm =
    let (h,args) = app_full trm [] in
    if Term.eq_constr h tO then
      0
    else if Term.eq_constr h tS then
      match args with
	n :: _ -> 1 + nat_to_int n
      | _ -> not_supported_verb trm "nat_to_int nil"
    else
      not_supported_verb trm "nat_to_int"

  let from_bool trm =
    if Term.eq_constr trm ttrue then
      true
    else if Term.eq_constr trm tfalse then
      false
    else not_supported_verb trm "from_bool"

  let unquote_char trm =
    let (h,args) = app_full trm [] in
    if Term.eq_constr h tAscii then
      match args with
	a :: b :: c :: d :: e :: f :: g :: h :: _ ->
	  let bits = List.rev [a;b;c;d;e;f;g;h] in
	  let v = List.fold_left (fun a n -> (a lsl 1) lor if from_bool n then 1 else 0) 0 bits in
	  char_of_int v
      | _ -> assert false
    else
      not_supported trm

  let unquote_string trm =
    let rec go n trm =
      let (h,args) = app_full trm [] in
      if Term.eq_constr h tEmptyString then
        Bytes.create n
      else if Term.eq_constr h tString then
	match args with
	  c :: s :: _ ->
	    let res = go (n + 1) s in
	    let _ = Bytes.set res n (unquote_char c) in
	    res
	| _ -> bad_term_verb trm "unquote_string"
      else
	not_supported_verb trm "unquote_string"
    in
    Bytes.to_string (go 0 trm)

  let unquote_ident trm =
    Names.id_of_string (unquote_string trm)

  let unquote_cast_kind trm =
    if Term.eq_constr trm kVmCast then
      Term.VMcast
    else if Term.eq_constr trm kCast then
      Term.DEFAULTcast
    else if Term.eq_constr trm kRevertCast then
      Term.REVERTcast
    else if Term.eq_constr trm kNative then
      Term.VMcast
    else
      bad_term trm


  let unquote_name trm =
    let (h,args) = app_full trm [] in
    if Term.eq_constr h nAnon then
      Names.Anonymous
    else if Term.eq_constr h nNamed then
      match args with
	n :: _ -> Names.Name (unquote_ident n)
      | _ -> raise (Failure "ill-typed, expected name")
    else
      raise (Failure "non-value")



  let from_coq_pair trm =
    let (h,args) = app_full trm [] in
    if Term.eq_constr h c_pair then
      match args with
	_ :: _ :: x :: y :: [] -> (x, y)
      | _ -> bad_term trm
    else
      not_supported_verb trm "from_coq_pair"


  let rec from_coq_list trm =
    let (h,args) = app_full trm [] in
    if Term.eq_constr h c_nil then []
    else if Term.eq_constr h c_cons then
      match args with
	_ :: x :: xs :: _ -> x :: from_coq_list xs
      | _ -> bad_term trm
    else
      not_supported_verb trm "from_coq_list"


  (* This code is taken from Pretyping, because it is not exposed globally *)
  (* the case for strict universe declarations was removed *)
  let get_level evd s =
    let names, _ = Global.global_universe_names () in
    if CString.string_contains ~where:s ~what:"." then
      match List.rev (CString.split '.' s) with
      | [] -> CErrors.anomaly (str"Invalid universe name " ++ str s ++ str".")
      | n :: dp ->
	 let num = int_of_string n in
	 let dp = DirPath.make (List.map Id.of_string dp) in
	 let level = Univ.Level.make dp num in
	 let evd =
	   try Evd.add_global_univ evd level
	   with UGraph.AlreadyDeclared -> evd
	 in evd, level
    else
      try
	let level = Evd.universe_of_name evd s in
	evd, level
      with Not_found ->
	try
	  let id = try Id.of_string s with _ -> raise Not_found in    (* Names.Id.of_string can fail if the name is not valid (utf8 ...) *)
          evd, snd (Idmap.find id names)
	with Not_found ->
  	  Evd.new_univ_level_variable ~name:s Evd.UnivRigid evd
  (* end of code from Pretyping *)



  let unquote_level evd trm (* of type level *) : Evd.evar_map * Univ.Level.t =
    let (h,args) = app_full trm [] in
    if Term.eq_constr h lProp then
      match args with
      | [] -> evd, Univ.Level.prop
      | _ -> bad_term_verb trm "unquote_level"
    else if Term.eq_constr h lSet then
      match args with
      | [] -> evd, Univ.Level.set
      | _ -> bad_term_verb trm "unquote_level"
    else if Term.eq_constr h tLevel then
      match args with
      | s :: [] -> get_level evd (unquote_string s)
      | _ -> bad_term_verb trm "unquote_level"
    else if Term.eq_constr h tLevelVar then
      match args with
      | l :: [] -> evd, Univ.Level.var (nat_to_int l)
      | _ -> bad_term_verb trm "unquote_level"
    else
      not_supported_verb trm "unquote_level"

  let unquote_level_expr evd trm (* of type level *) b (* of type bool *) : Evd.evar_map * Univ.Universe.t=
    let evd, l = unquote_level evd trm in
    let u = Univ.Universe.make l in
    if from_bool b then evd, Univ.Universe.super u
    else evd, u

  let unquote_universe evd trm (* of type universe *) =
    let levels = List.map from_coq_pair (from_coq_list trm) in
    let evd, u = match levels with
      | [] -> CErrors.anomaly (str "Empty level in unquote_sort. Please fill a bug in Template Coq.")
      | (l,b)::q -> List.fold_left (fun (evd,u) (l,b) -> let evd, u' = unquote_level_expr evd l b
                                                         in evd, Univ.Universe.sup u u')
                                   (unquote_level_expr evd l b) q
    in evd, u



  let denote_inductive trm =
    let (h,args) = app_full trm [] in
    if Term.eq_constr h tmkInd then
      match args with
	nm :: num :: _ ->
        let s = (unquote_string nm) in
        let (dp, nm) = split_name s in
        (try
          match Nametab.locate (Libnames.make_qualid dp nm) with
          | Globnames.ConstRef c ->  CErrors.user_err (str "this not an inductive constant. use tConst instead of tInd : " ++ str s)
          | Globnames.IndRef i -> (fst i, nat_to_int  num)
          | Globnames.VarRef _ -> CErrors.user_err (str "the constant is a variable. use tVar : " ++ str s)
          | Globnames.ConstructRef _ -> CErrors.user_err (str "the constant is a consructor. use tConstructor : " ++ str s)
        with
        Not_found ->   CErrors.user_err (str "Constant not found : " ++ str s))
      | _ -> assert false
    else
      bad_term_verb trm "non-constructor"


  (** NOTE: Because the representation is lossy, I should probably
   ** come back through elaboration.
   ** - This would also allow writing terms with holes
   **)
  let denote_term evdref trm =
    let rec aux trm =
    debug (fun () -> Pp.(str "denote_term" ++ spc () ++ Printer.pr_constr trm)) ;
    let (h,args) = app_full trm [] in
    if Term.eq_constr h tRel then
      match args with
	x :: _ ->
	  Term.mkRel (nat_to_int x + 1)
      | _ -> raise (Failure "ill-typed")
    else if Term.eq_constr h tVar then
      match args with
	x :: _ -> Term.mkVar (unquote_ident x)
      | _ -> raise (Failure "ill-typed")
    else if Term.eq_constr h tSort then
      match args with
	x :: _ -> let evd, u = unquote_universe !evdref x in evdref := evd; Term.mkType u
      | _ -> raise (Failure "ill-typed")
    else if Term.eq_constr h tCast then
      match args with
	t :: c :: ty :: _ ->
	  Term.mkCast (aux t, unquote_cast_kind c, aux ty)
      | _ -> raise (Failure "ill-typed")
    else if Term.eq_constr h tProd then
      match args with
	n :: t :: b :: _ ->
	  Term.mkProd (unquote_name n, aux t, aux b)
      | _ -> raise (Failure "ill-typed (product)")
    else if Term.eq_constr h tLambda then
      match args with
	n :: t :: b :: _ ->
	Term.mkLambda (unquote_name n, aux t, aux b)
      | _ -> raise (Failure "ill-typed (lambda)")
    else if Term.eq_constr h tLetIn then
      match args with
	n :: e :: t :: b :: _ ->
	  Term.mkLetIn (unquote_name n, aux e, aux t, aux b)
      | _ -> raise (Failure "ill-typed (let-in)")
    else if Term.eq_constr h tApp then
      match args with
	f :: xs :: _ ->
	  Term.mkApp (aux f,
		      Array.of_list (List.map aux (from_coq_list xs)))
      | _ -> raise (Failure "ill-typed (app)")
    else if Term.eq_constr h tConst then
      match args with
    	s :: u :: [] ->
         (* TODO: unquote universes *)
        let s = (unquote_string s) in
        let (dp, nm) = split_name s in
        (try
          match Nametab.locate (Libnames.make_qualid dp nm) with
          | Globnames.ConstRef c ->
             EConstr.Unsafe.to_constr (Evarutil.e_new_global evdref (Globnames.ConstRef c))
          | Globnames.IndRef _ -> CErrors.user_err (str "the constant is an inductive. use tInd : " ++ str s)
          | Globnames.VarRef _ -> CErrors.user_err (str "the constant is a variable. use tVar : " ++ str s)
          | Globnames.ConstructRef _ -> CErrors.user_err (str "the constant is a consructor. use tConstructor : " ++ str s)
        with
        Not_found -> CErrors.user_err (str "Constant not found : " ++ str s))
      | _ -> raise (Failure "ill-typed (tConst)")
    else if Term.eq_constr h tConstructor then
      match args with
	i :: idx :: _ ->
	  let i = denote_inductive i in
	  Term.mkConstruct (i, nat_to_int idx + 1)
      | _ -> raise (Failure "ill-typed (constructor)")
    else if Term.eq_constr h tInd then
      match args with
	i :: _ ->
	  let i = denote_inductive i in
	  Term.mkInd i
      | _ -> raise (Failure "ill-typed (inductive)")
    else if Term.eq_constr h tCase then
      match args with
	info :: ty :: d :: brs :: _ ->
          let i, _ = from_coq_pair info in
          let ind = denote_inductive i in
          let ci = Inductiveops.make_case_info (Global.env ()) ind Term.RegularStyle in
          let denote_branch br =
            let _, br = from_coq_pair br in
            aux br
          in
	  Term.mkCase (ci, aux ty, aux d,
			Array.of_list (List.map denote_branch (from_coq_list brs)))
      | _ -> raise (Failure "ill-typed (case)")
    else if Term.eq_constr h tFix then
      match args with
      | bds :: i :: _ ->
        let unquoteFbd  b : ((Term.constr * Term.constr) * (Term.constr * Term.constr)) =
          let (_,args) = app_full b [] in
          match args with
          | _(*type*)::a::b::c::d::[] -> ((a,b),(c,d))
          |_ -> raise (Failure " (mkdef must take exactly 5 arguments)")
          in
        let lbd = List.map unquoteFbd (from_coq_list bds) in
        let (p1,p2) = (List.map fst lbd, List.map snd lbd) in
        let (names,types,bodies,rargs) = (List.map fst p1, List.map snd p1, List.map fst p2, List.map snd p2) in
        let (types,bodies) = (List.map aux types, List.map aux bodies) in
        let (names,rargs) = (List.map unquote_name names, List.map nat_to_int rargs) in
        let la = Array.of_list in
        Term.mkFix ((la rargs,nat_to_int i), (la names, la types, la bodies))
      | _ -> raise (Failure "tFix takes exactly 2 arguments")
    else if Term.eq_constr h tCoFix then
      match args with
      | bds :: i :: _ ->
        let unquoteFbd  b : (Term.constr * Term.constr * Term.constr) =
          let (_,args) = app_full b [] in
          match args with
          | _(*type*)::a::b::c::d::[] -> ((a,b,c))
          |_ -> raise (Failure " (mkdef must take exactly 5 arguments)")
          in
        let lbd = List.map unquoteFbd (from_coq_list bds) in
        let (names,types,bodies) = CList.split3 lbd in
        let (types,bodies) = (List.map aux types, List.map aux bodies) in
        let names = List.map unquote_name names in
        let la = Array.of_list in
        Term.mkCoFix (nat_to_int i, (la names, la types, la bodies))
      | _ -> raise (Failure "tFix takes exactly 2 arguments")
    else if Term.eq_constr h tProj then
      match args with
      | [ proj ; t ] ->
         let (p, narg) = from_coq_pair proj in
         let (ind, _) = from_coq_pair p in
	 let ind' = denote_inductive ind in
         let projs = Recordops.lookup_projections ind' in
         (match List.nth projs (nat_to_int narg) with
          | Some p -> Term.mkProj (Names.Projection.make p false, aux t)
          | None -> bad_term trm)
      | _ -> raise (Failure "ill-typed (proj)")
    else
      not_supported_verb trm "big_case"
    in aux trm



  let denote_reduction_strategy (trm : quoted_reduction_strategy) : Redexpr.red_expr =
    (* from g_tactic.ml4 *)
    let default_flags = Redops.make_red_flag [FBeta;FMatch;FFix;FCofix;FZeta;FDeltaBut []] in
    if Term.eq_constr trm tcbv then Cbv default_flags
    else if Term.eq_constr trm tcbn then Cbn default_flags
    else if Term.eq_constr trm thnf then Hnf
    else if Term.eq_constr trm tall then Cbv all_flags
    else if Term.eq_constr trm tlazy then Lazy all_flags
    else not_supported_verb trm "denote_reduction_strategy"



  let denote_local_entry evdref trm =
    let (h,args) = app_full trm [] in
      match args with
	    x :: [] ->
      if Term.eq_constr h tLocalDef then Entries.LocalDefEntry (denote_term evdref x)
      else (if  Term.eq_constr h tLocalAssum then Entries.LocalAssumEntry (denote_term evdref x) else bad_term trm)
      | _ -> bad_term trm

  let denote_mind_entry_finite trm =
    let (h,args) = app_full trm [] in
      match args with
	    [] ->
      if Term.eq_constr h cFinite then Decl_kinds.Finite
      else if  Term.eq_constr h cCoFinite then Decl_kinds.CoFinite
      else if  Term.eq_constr h cBiFinite then Decl_kinds.BiFinite
      else bad_term trm
      | _ -> bad_term trm

  let unquote_map_option f trm =
    let (h,args) = app_full trm [] in
    if Term.eq_constr h cSome then
    match args with
	  _ :: x :: _ -> Some (f x)
      | _ -> bad_term trm
    else if Term.eq_constr h cNone then
    match args with
	  _ :: [] -> None
      | _ -> bad_term trm
    else
      not_supported_verb trm "unqote_map_option"


  let denote_universe_context (trm : Term.constr) : Univ.universe_context =
    Univ.UContext.empty (* FIXME !!! *)


  let declare_inductive (env: Environ.env) (evm: Evd.evar_map) (body: Term.constr) : unit =
  let (evm,body) = reduce_all env evm body in
  let (_,args) = app_full body [] in (* check that the first component is Build_mut_ind .. *)
  let evdref = ref evm in
  let one_ind b1 : Entries.one_inductive_entry =
    let (_,args) = app_full b1 [] in (* check that the first component is Build_one_ind .. *)
    match args with
    | mt::ma::mtemp::mcn::mct::[] ->
    {
    mind_entry_typename = unquote_ident mt;
    mind_entry_arity = denote_term evdref ma;
    mind_entry_template = from_bool mtemp;
    mind_entry_consnames = List.map unquote_ident (from_coq_list mcn);
    mind_entry_lc = List.map (denote_term evdref) (from_coq_list mct)
    }
    | _ -> raise (Failure "ill-typed one_inductive_entry")
     in
  let mut_ind mr mf mp mi mpol uctx mpr : Entries.mutual_inductive_entry =
    {
    mind_entry_record = unquote_map_option (unquote_map_option unquote_ident) mr;
    mind_entry_finite = denote_mind_entry_finite mf; (* inductive *)
    mind_entry_params = List.map (fun p -> let (l,r) = (from_coq_pair p) in (unquote_ident l, (denote_local_entry evdref r)))
      (List.rev (from_coq_list mp));
    mind_entry_inds = List.map one_ind (from_coq_list mi);
    (* mind_entry_polymorphic = from_bool mpol; *)
    mind_entry_universes =
      (let uctx = denote_universe_context uctx in
      if from_bool mpol then Polymorphic_ind_entry uctx
      else Monomorphic_ind_entry uctx);
    mind_entry_private = unquote_map_option from_bool mpr (*mpr*)
    } in
    match args with
    mr::mf::mp::mi::mpol::univs::mpr::[] ->
      ignore(Command.declare_mutual_inductive_with_eliminations (mut_ind mr mf mp mi mpol univs mpr) [] [])
    | _ -> raise (Failure "ill-typed mutual_inductive_entry")


  let monad_failure s k =
    CErrors.user_err  (str (s ^ " must take " ^ (string_of_int k) ^ " argument" ^ (if k > 0 then "s" else "") ^ ".")
                       ++ str "Please file a bug with Template-Coq.")

  let rec run_template_program_rec (k : Evd.evar_map * Term.constr -> unit)  ((evm, pgm) : Evd.evar_map * Term.constr) : unit =
    let env = Global.env () in
    let (evm, pgm) = reduce_hnf env evm pgm in
    let (coConstr, args) = app_full pgm [] in
    if Term.eq_constr coConstr tmReturn then
      match args with
      | _::h::[] -> k (evm, h)
      | _ -> monad_failure "tmReturn" 2
    else if Term.eq_constr coConstr tmBind then
      match args with
      | _::_::a::f::[] ->
         run_template_program_rec (fun (evm, ar) -> run_template_program_rec k (evm, Term.mkApp (f, [|ar|]))) (evm, a)
      | _ -> monad_failure "tmBind" 4
    else if Term.eq_constr coConstr tmDefinition then
      match args with
      | name::typ::body::[] ->
         let (evm, name) = reduce_all env evm name in
         (* todo: let the user choose the reduction used for the type *)
         let (evm, typ) = reduce_hnf env evm typ in
         let n = Declare.declare_definition ~kind:Decl_kinds.Definition (unquote_ident name) ~types:typ (body, Evd.universe_context_set evm) in
         k (evm, Term.mkConst n)
      | _ -> monad_failure "tmDefinition" 3
    else if Term.eq_constr coConstr tmAxiom then
      match args with
      | name::typ::[] ->
         let (evm, name) = reduce_all env evm name in
         let (evm, typ) = reduce_hnf env evm typ in
         let param = Entries.ParameterEntry (None, false, (typ, UState.context (Evd.evar_universe_context evm)), None) in
         let n = Declare.declare_constant (unquote_ident name) (param, Decl_kinds.IsDefinition Decl_kinds.Definition) in
         k (evm, Term.mkConst n)
      | _ -> monad_failure "tmAxiom" 2
    else if Term.eq_constr coConstr tmLemma then
      match args with
      | name::typ::[] ->
         let (evm, name) = reduce_all env evm name in
         let (evm, typ) = reduce_hnf env evm typ in
         let kind = (Decl_kinds.Global, Flags.use_polymorphic_flag (), Decl_kinds.Definition) in
         let hole = CAst.make (Constrexpr.CHole (None, Misctypes.IntroAnonymous, None)) in
         let typ = Constrextern.extern_type true env evm (EConstr.of_constr typ) in
         let original_program_flag = !Flags.program_mode in
         Flags.program_mode := true;
         Command.do_definition (unquote_ident name) kind None [] None hole (Some typ)
                               (Lemmas.mk_hook (fun _ gr -> let env = Global.env () in
                                                            let evm, t = Evd.fresh_global env evm gr in k (evm, t)));
         Flags.program_mode := original_program_flag
         (* let kind = Decl_kinds.(Global, Flags.use_polymorphic_flag (), DefinitionBody Definition) in *)
         (* Lemmas.start_proof (unquote_ident name) kind evm (EConstr.of_constr typ) *)
                            (* (Lemmas.mk_hook (fun _ gr -> *)
                                 (* let evm, t = Evd.fresh_global env evm gr in k (env, evm, t) *)
                                 (* k (env, evm, unit_tt) *)
                            (* )); *)
      | _ -> monad_failure "tmLemma" 2
    else if Term.eq_constr coConstr tmMkDefinition then
      match args with
      | name::body::[] ->
         let (evm, name) = reduce_all env evm name in
         let (evm, def) = reduce_all env evm body in
         let evdref = ref evm in
         let trm = denote_term evdref def in
         let evm = !evdref in
         let _ = Declare.declare_definition ~kind:Decl_kinds.Definition (unquote_ident name) (trm, Evd.universe_context_set evm) in
         k (evm, unit_tt)
      | _ -> monad_failure "tmMkDefinition" 2
    else if Term.eq_constr coConstr tmQuote then
      match args with
      | _::trm::[] -> let qt = TermReify.quote_term env trm (* user should do the reduction (using tmEval) if they want *)
                      in k (evm, qt)
      | _ -> monad_failure "tmQuote" 2
    else if Term.eq_constr coConstr tmQuoteRec then
      match args with
      | _::trm::[] -> let qt = TermReify.quote_term_rec env trm in
                      k (evm, qt)
      | _ -> monad_failure "tmQuoteRec" 2
    else if Term.eq_constr coConstr tmQuoteInductive then
      match args with
      | name::[] ->
         let (evm, name) = reduce_all env evm name in
         let name = unquote_string name in
         let (dp, nm) = split_name name in
         (match Nametab.locate (Libnames.make_qualid dp nm) with
          | Globnames.IndRef ni ->
             let t = TermReify.quote_mind_decl env (fst ni) in
             let _, args = Term.destApp t in
             (match args with
              | [|name; uctx ; n; inds|] ->
                 let decl = Term.mkApp (tBuild_minductive_decl, [|n ; inds ; uctx|]) in
                 k (evm, decl)
              | _ -> bad_term_verb t "anomaly in quoting of inductive types")
               (* quote_mut_ind produce an entry rather than a decl *)
          (* let c = Environ.lookup_mind (fst ni) env in (\* FIX: For efficienctly, we should also export (snd ni)*\) *)
          (* TermReify.quote_mut_ind env c *)
          | _ -> CErrors.user_err (str name ++ str " does not seem to be an inductive."))
      (* k (evm, entry) *)
      | _ -> monad_failure "tmQuoteInductive" 1
    else if Term.eq_constr coConstr tmQuoteConstant then
      match args with
      | name::b::[] ->
         let (evm, name) = reduce_all env evm name in
         let name = unquote_string name in
         let (evm, b) = reduce_all env evm b in
         let bypass = from_bool b in
         let (dp, nm) = split_name name in
         let entry = (* todo: this should be defined in the quoter module *)
           match Nametab.locate (Libnames.make_qualid dp nm) with
           | Globnames.ConstRef c ->
              let cd = Environ.lookup_constant c env in
              let ty = match cd.const_type with
                | RegularArity ty -> TermReify.quote_term env ty
                | TemplateArity _ -> CErrors.user_err (Pp.str "Cannot reify deprecated template-polymorphic constant types")
              in
              let body = match cd.const_body with
                | Def cs -> Some (TermReify.quote_term env (Mod_subst.force_constr cs))
                | OpaqueDef cs when bypass -> Some (TermReify.quote_term env (Opaqueproof.force_proof (Global.opaque_tables ()) cs))
                | _ -> None
              in
              (match body with
               | Some body -> Term.mkApp (cDefinitionEntry, [| Term.mkApp (cDefinition_entry, [|ty;body|]) |])
               | None -> Term.mkApp (cParameterEntry, [| Term.mkApp (cParameter_entry, [|ty|]) |]))
           | _ -> CErrors.user_err (str name ++ str " does not seem to be a constant.") in
         k (evm, entry)
      | _ -> monad_failure "tmQuoteConstant" 2
    else if Term.eq_constr coConstr tmQuoteUniverses then
      match args with
      | _::[] -> let univs = Environ.universes env in
                 k (evm, quote_ugraph univs)
      | _ -> monad_failure "tmQuoteUniverses" 1
    else if Term.eq_constr coConstr tmPrint then
      match args with
      | _::trm::[] -> Feedback.msg_info (Printer.pr_constr trm);
                      k (evm, unit_tt)
      | _ -> monad_failure "tmPrint" 2
    else if Term.eq_constr coConstr tmFail then
      match args with
      | _::trm::[] -> CErrors.user_err (str (unquote_string trm))
      | _ -> monad_failure "tmFail" 2
    else if Term.eq_constr coConstr tmAbout then
      match args with
      | id::[] -> let id = unquote_string id in
                  (try
                     let gr = Smartlocate.locate_global_with_alias (None, Libnames.qualid_of_string id) in
                     let opt = Term.mkApp (cSome , [|tglobal_reference ; quote_global_reference gr|]) in
                    k (evm, opt)
                  with
                  | Not_found -> k (evm, Term.mkApp (cNone, [|tglobal_reference|])))
      | _ -> monad_failure "tmAbout" 1
    else if Term.eq_constr coConstr tmCurrentModPath then
      match args with
      | _::[] -> let mp = Lib.current_mp () in
                 (* let dp' = Lib.cwd () in (* different on sections ? *) *)
                 let s = quote_string (Names.ModPath.to_string mp) in
                 k (evm, s)
      | _ -> monad_failure "tmCurrentModPath" 1
    else if Term.eq_constr coConstr tmEval then
      match args with
      | s(*reduction strategy*)::_(*type*)::trm::[] ->
         let red = denote_reduction_strategy s in
         let (evm, trm) = reduce_all ~red env evm trm
         in k (evm, trm)
      | _ -> monad_failure "tmEval" 3
    else if Term.eq_constr coConstr tmMkInductive then
      match args with
      | mind::[] -> declare_inductive env evm mind;
                    k (evm, unit_tt)
      | _ -> monad_failure "tmMkInductive" 1
    else if Term.eq_constr coConstr tmUnquote then
      match args with
      | t::[] ->
        let (evm, t) = reduce_all env evm t in
        let evdref = ref evm in
        let t' = denote_term evdref t in
        let evm = !evdref in
        let typ = EConstr.to_constr evm (Retyping.get_type_of env evm (EConstr.of_constr t')) in
        (* todo: we could declare a new universe <= Coq.Init.Specif.7 or 8 instead of using [texistT_typed_term] *)
        (* let (evm, u) = Evd.fresh_sort_in_family env evm Sorts.InType in *)
        (* (env, evm, Term.mkApp (texistT, [|Term.mkSort u; *)
        (*                                   Term.mkLambda (Names.Name (Names.Id.of_string "T"), Term.mkSort u, Term.mkRel 1); *)
        (*                                   typ; t'|])) *)
        k (evm, Term.mkApp (texistT_typed_term, [|typ; t'|]))
      | _ -> monad_failure "tmUnquote" 1
    else if Term.eq_constr coConstr tmUnquoteTyped then
      match args with
      | typ::t::[] ->
        let (evm, t) = reduce_all env evm t in
        let evdref = ref evm in
        let t' = denote_term evdref t in
        (* todo: investigate why the following bugs *)
        Feedback.msg_debug (str "lllllllllll");
        let t' = Typing.e_solve_evars env evdref (EConstr.of_constr t') in
        Feedback.msg_debug (str "lllllllllll1");
        Typing.e_check env evdref t' (EConstr.of_constr typ) ;
        Feedback.msg_debug (str "lllllllllll2");
        let t' = EConstr.to_constr !evdref t' in
        k (!evdref, t')
      | _ -> monad_failure "tmUnquoteTyped" 2
    else if Term.eq_constr coConstr tmFreshName then
      match args with
      | name::[] -> let name' = Namegen.next_ident_away_from (unquote_ident name) (fun id -> Nametab.exists_cci (Lib.make_path id)) in
                    k (evm, quote_ident name')
      | _ -> monad_failure "tmFreshName" 1
    else CErrors.user_err (str "Invalid argument or not yet implemented. The argument must be a TemplateProgram")
end

DECLARE PLUGIN "template_plugin"

(** Calling Ltac **)

let ltac_lcall tac args =
  Tacexpr.TacArg(Loc.tag @@ Tacexpr.TacCall (Loc.tag (Misctypes.ArgVar(Loc.tag @@ Names.Id.of_string tac),args)))

open Names
open Tacexpr
open Tacinterp
open Misctypes


let ltac_apply (f : Value.t) (args: Tacinterp.Value.t list) =
  let fold arg (i, vars, lfun) =
    let id = Names.Id.of_string ("x" ^ string_of_int i) in
    let x = Reference (ArgVar (Loc.tag id)) in
    (succ i, x :: vars, Id.Map.add id arg lfun)
  in
  let (_, args, lfun) = List.fold_right fold args (0, [], Id.Map.empty) in
  let lfun = Id.Map.add (Id.of_string "F") f lfun in
  let ist = { (Tacinterp.default_ist ()) with Tacinterp.lfun = lfun; } in
  Tacinterp.eval_tactic_ist ist (ltac_lcall "F" args)

let to_ltac_val c = Tacinterp.Value.of_constr c

let check_inside_section () =
  if Lib.sections_are_opened () then
    CErrors.user_err ~hdr:"Quote" (Pp.str "You can not quote within a section.")


open Stdarg
open Tacarg

TACTIC EXTEND get_goal
    | [ "quote_term" constr(c) tactic(tac) ] ->
      [ (** quote the given term, pass the result to t **)
  Proofview.Goal.nf_enter begin fun gl ->
          let env = Proofview.Goal.env gl in
	  let c = TermReify.quote_term env (EConstr.to_constr (Proofview.Goal.sigma gl) c) in
	  ltac_apply tac (List.map to_ltac_val [EConstr.of_constr c])
  end ]
(*
    | [ "quote_goal" ] ->
      [ (** get the representation of the goal **)
	fun gl -> assert false ]
    | [ "get_inductive" constr(i) ] ->
      [ fun gl -> assert false ]
*)
END;;

TACTIC EXTEND denote_term
    | [ "denote_term" constr(c) tactic(tac) ] ->
      [ Proofview.Goal.enter (begin fun gl ->
         let env = Proofview.Goal.env gl in
         let evm = Proofview.Goal.sigma gl in
         let evdref = ref evm in
         let c = Denote.denote_term evdref (EConstr.to_constr evm c) in
         (* TODO : not the right way of retype things *)
         let def' = Constrextern.extern_constr true env !evdref (EConstr.of_constr c) in
         let def = Constrintern.interp_constr env !evdref def' in
         Proofview.tclTHEN (Proofview.Unsafe.tclEVARS !evdref)
	                   (ltac_apply tac (List.map to_ltac_val [EConstr.of_constr (fst def)]))
      end) ]
END;;


VERNAC COMMAND EXTEND Make_vernac CLASSIFIED AS SIDEFF
    | [ "Quote" "Definition" ident(name) ":=" constr(def) ] ->
      [ check_inside_section () ;
	let (evm,env) = Lemmas.get_current_context () in
	let def,uctx = Constrintern.interp_constr env evm def in
	let trm = TermReify.quote_term env def in
	ignore(Declare.declare_definition ~kind:Decl_kinds.Definition name
                                          (trm, Evd.evar_universe_context_set uctx)) ]
END;;

VERNAC COMMAND EXTEND Make_vernac_reduce CLASSIFIED AS SIDEFF
    | [ "Quote" "Definition" ident(name) ":=" "Eval" red_expr(rd) "in" constr(def) ] ->
      [ check_inside_section () ;
	let (evm,env) = Lemmas.get_current_context () in
	let def, uctx = Constrintern.interp_constr env evm def in
        let evm = Evd.from_ctx uctx in
        let (evm,rd) = Tacinterp.interp_redexp env evm rd in
	let (evm,def) = reduce_all env evm ~red:rd def in
	let trm = TermReify.quote_term env def in
	ignore(Declare.declare_definition ~kind:Decl_kinds.Definition
                                          name (trm, Evd.universe_context_set evm)) ]
END;;

VERNAC COMMAND EXTEND Make_recursive CLASSIFIED AS SIDEFF
    | [ "Quote" "Recursively" "Definition" ident(name) ":=" constr(def) ] ->
      [ check_inside_section () ;
	let (evm,env) = Lemmas.get_current_context () in
	let def, uctx = Constrintern.interp_constr env evm def in
	let trm = TermReify.quote_term_rec env def in
	ignore(Declare.declare_definition
	  ~kind:Decl_kinds.Definition name
	  (trm, Evd.evar_universe_context_set uctx)) ]
END;;

VERNAC COMMAND EXTEND Unquote_vernac CLASSIFIED AS SIDEFF
    | [ "Make" "Definition" ident(name) ":=" constr(def) ] ->
      [ check_inside_section () ;
	let (evm, env) = Lemmas.get_current_context () in
	let (trm, uctx) = Constrintern.interp_constr env evm def in
        let evdref = ref (Evd.from_ctx uctx) in
	let trm = Denote.denote_term evdref trm in
	let _ = Declare.declare_definition ~kind:Decl_kinds.Definition name (trm, Evd.universe_context_set !evdref) in
        () ]
END;;

VERNAC COMMAND EXTEND Unquote_vernac_red CLASSIFIED AS SIDEFF
    | [ "Make" "Definition" ident(name) ":=" "Eval" red_expr(rd) "in" constr(def) ] ->
      [ check_inside_section () ;
	let (evm, env) = Lemmas.get_current_context () in
	let (trm, uctx) = Constrintern.interp_constr env evm def in
        let evm = Evd.from_ctx uctx in
        let (evm,rd) = Tacinterp.interp_redexp env evm rd in
	let (evm,trm) = reduce_all env evm ~red:rd trm in
        let evdref = ref evm in
	let trm = Denote.denote_term evdref trm in
	let _ = Declare.declare_definition ~kind:Decl_kinds.Definition name (trm, Evd.universe_context_set !evdref) in
        () ]
END;;

VERNAC COMMAND EXTEND Unquote_inductive CLASSIFIED AS SIDEFF
    | [ "Make" "Inductive" constr(def) ] ->
      [ check_inside_section () ;
	let (evm,env) = Lemmas.get_current_context () in
	let (body,uctx) = Constrintern.interp_constr env evm def in
        Denote.declare_inductive env evm body ]
END;;

VERNAC COMMAND EXTEND Run_program CLASSIFIED AS SIDEFF
    | [ "Run" "TemplateProgram" constr(def) ] ->
      [ check_inside_section () ;
	let (evm, env) = Lemmas.get_current_context () in
        let (def, _) = Constrintern.interp_constr env evm def in
        (* todo : uctx ? *)
        Denote.run_template_program_rec (fun _ -> ()) (evm, def) ]
END;;

VERNAC COMMAND EXTEND Make_tests CLASSIFIED AS QUERY
    | [ "Test" "Quote" constr(c) ] ->
      [ check_inside_section () ;
	let (evm,env) = Lemmas.get_current_context () in
	let c = Constrintern.interp_constr env evm c in
	let result = TermReify.quote_term env (fst c) in
        Feedback.msg_notice (Printer.pr_constr result) ;
	() ]
END;;
