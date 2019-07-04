open Univ
open Entries
open Names
open Pp
open Tm_util
open Quoted

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

  type quoted_mind_params = Constr.t (* of type list (Ast.ident * list (ident * local_entry)local_entry) *)
  type quoted_ind_entry = quoted_ident * t * quoted_bool * quoted_ident list * t list
  type quoted_definition_entry = t * t option * quoted_universes_decl
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

  let resolve_symbol (path : string list) (tm : string) : Constr.t Lazy.t =
    gen_constant_in_modules contrib_name [path] tm

  let resolve_symbol_p (path : string list) (tm : string) : Globnames.global_reference Lazy.t =
    lazy (Coqlib.gen_reference_in_modules contrib_name [path] tm)

  let pkg_datatypes = ["Coq";"Init";"Datatypes"]
  let pkg_string = ["Coq";"Strings";"String"]
  let pkg_base_reify = ["MetaCoq";"Template";"BasicAst"]
  let pkg_reify = ["MetaCoq";"Template";"Ast"]
  let pkg_template_monad = ["MetaCoq";"Template";"TemplateMonad"]
  let pkg_univ = ["MetaCoq";"Template";"Universes"]
  let pkg_level = ["MetaCoq";"Template";"Universes";"Level"]
  let pkg_variance = ["MetaCoq";"Template";"Universes";"Variance"]
  let pkg_ugraph = ["MetaCoq";"Template";"uGraph"]
  let ext_pkg_univ s = List.append pkg_univ [s]

  let r_base_reify = resolve_symbol pkg_base_reify
  let r_reify = resolve_symbol pkg_reify
  let r_template_monad = resolve_symbol pkg_template_monad
  let r_template_monad_p = resolve_symbol_p pkg_template_monad

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
  let tlist = resolve_symbol pkg_datatypes "list"
  let c_nil = resolve_symbol pkg_datatypes "nil"
  let c_cons = resolve_symbol pkg_datatypes "cons"
  let nel_sing = resolve_symbol ["MetaCoq";"Template";"utils";"NEL"] "sing"
  let nel_cons = resolve_symbol ["MetaCoq";"Template";"utils";"NEL"] "cons"
  let prod_type = resolve_symbol pkg_datatypes "prod"
  let sum_type = resolve_symbol pkg_datatypes "sum"
  let option_type = resolve_symbol pkg_datatypes "option"
  let bool_type = resolve_symbol pkg_datatypes "bool"
  let cInl = resolve_symbol pkg_datatypes "inl"
  let cInr = resolve_symbol pkg_datatypes "inr"
  let constr_mkApp (h, a) = Constr.mkApp (Lazy.force h, a)
  let constr_mkAppl (h, a) = Constr.mkApp (Lazy.force h, Array.map Lazy.force a)
  let prod a b = constr_mkApp (prod_type, [| a ; b |])
  let prodl a b = prod (Lazy.force a) (Lazy.force b)
  let c_pair = resolve_symbol pkg_datatypes "pair"
  let pair a b f s = constr_mkApp (c_pair, [| a ; b ; f ; s |])
  let pairl a b f s = pair (Lazy.force a) (Lazy.force b) f s

    (* reify the constructors in Template.Ast.v, which are the building blocks of reified terms *)
  let nAnon = r_base_reify "nAnon"
  let nNamed = r_base_reify "nNamed"
  let kVmCast = r_base_reify "VmCast"
  let kNative = r_base_reify "NativeCast"
  let kCast = r_base_reify "Cast"
  let kRevertCast = r_base_reify "RevertCast"
  let lProp = resolve_symbol pkg_level "lProp"
  let lSet = resolve_symbol pkg_level "lSet"
  let tsort_family = resolve_symbol pkg_univ "sort_family"
  let lfresh_universe = resolve_symbol pkg_univ "fresh_universe"
  let sfProp = resolve_symbol pkg_univ "InProp"
  let sfSet = resolve_symbol pkg_univ "InSet"
  let sfType = resolve_symbol pkg_univ "InType"
  let tident = r_base_reify "ident"
  let tname = r_base_reify "name"
  let tIndTy = r_base_reify "inductive"
  let tmkInd = r_base_reify "mkInd"
  let tmkdecl = r_reify "mkdecl"
  let (tTerm,tRel,tVar,tEvar,tSort,tCast,tProd,
       tLambda,tLetIn,tApp,tCase,tFix,tConstructor,tConst,tInd,tCoFix,tProj) =
    (r_reify "term", r_reify "tRel", r_reify "tVar", r_reify "tEvar",
     r_reify "tSort", r_reify "tCast", r_reify "tProd", r_reify "tLambda",
     r_reify "tLetIn", r_reify "tApp", r_reify "tCase", r_reify "tFix",
     r_reify "tConstruct", r_reify "tConst", r_reify "tInd", r_reify "tCoFix", r_reify "tProj")

  let tlevel = resolve_symbol pkg_level "t"
  let tLevel = resolve_symbol pkg_level "Level"
  let tLevelVar = resolve_symbol pkg_level "Var"
  let tunivLe = resolve_symbol (ext_pkg_univ "ConstraintType") "Le"
  let tunivLt = resolve_symbol (ext_pkg_univ "ConstraintType") "Lt"
  let tunivEq = resolve_symbol (ext_pkg_univ "ConstraintType") "Eq"
  let tmake_universe = resolve_symbol (ext_pkg_univ "Universe") "make''"
  let tLevelSet_of_list = resolve_symbol (ext_pkg_univ "LevelSetProp") "of_list"

  (* let tunivcontext = resolve_symbol pkg_univ "universe_context" *)
  let tVariance = resolve_symbol pkg_variance "t"
  let cIrrelevant = resolve_symbol pkg_variance "Irrelevant"
  let cCovariant = resolve_symbol pkg_variance "Covariant"
  let cInvariant = resolve_symbol pkg_variance "Invariant"
  let cMonomorphic_ctx = resolve_symbol pkg_univ "Monomorphic_ctx"
  let cPolymorphic_ctx = resolve_symbol pkg_univ "Polymorphic_ctx"
  let cCumulative_ctx = resolve_symbol pkg_univ "Cumulative_ctx"
  let tUContext = resolve_symbol (ext_pkg_univ "UContext") "t"
  let tAUContext = resolve_symbol (ext_pkg_univ "AUContext") "t"
  let tUContextmake = resolve_symbol (ext_pkg_univ "UContext") "make"
  let tAUContextmake = resolve_symbol (ext_pkg_univ "AUContext") "make"
  let tACumulativityInfomake = resolve_symbol (ext_pkg_univ "ACumulativityInfo") "make"
  let tConstraintSet = resolve_symbol (ext_pkg_univ "ConstraintSet") "t_"
  let tLevelSet = resolve_symbol (ext_pkg_univ "LevelSet") "t_"
  let tConstraintSetempty = lazy (Universes.constr_of_global (Coqlib.find_reference "template coq bug" (ext_pkg_univ "ConstraintSet") "empty"))
  let tConstraintSetadd = lazy (Universes.constr_of_global (Coqlib.find_reference "template coq bug" (ext_pkg_univ "ConstraintSet") "add"))
  let tmake_univ_constraint = resolve_symbol pkg_univ "make_univ_constraint"

  let (tdef,tmkdef) = (r_base_reify "def", r_base_reify "mkdef")
  let (tLocalDef,tLocalAssum,tlocal_entry) = (r_reify "LocalDef", r_reify "LocalAssum", r_reify "local_entry")

  let (cFinite,cCoFinite,cBiFinite) = (r_reify "Finite", r_reify "CoFinite", r_reify "BiFinite")
  let tone_inductive_body = r_reify "one_inductive_body"
  let tBuild_one_inductive_body = r_reify "Build_one_inductive_body"
  let tBuild_mutual_inductive_body = r_reify "Build_mutual_inductive_body"
  let tBuild_constant_body = r_reify "Build_constant_body"
  let tglobal_decl = r_reify "global_decl"
  let tConstantDecl = r_reify "ConstantDecl"
  let tInductiveDecl = r_reify "InductiveDecl"
  let tglobal_env = r_reify "global_env"

  let tcontext_decl = r_reify "context_decl"
  let tcontext = r_reify "context"

  let tMutual_inductive_entry = r_reify "mutual_inductive_entry"
  let tOne_inductive_entry = r_reify "one_inductive_entry"
  let tBuild_mutual_inductive_entry = r_reify "Build_mutual_inductive_entry"
  let tBuild_one_inductive_entry = r_reify "Build_one_inductive_entry"
  let tConstant_entry = r_reify "constant_entry"
  let cParameterEntry = r_reify "ParameterEntry"
  let cDefinitionEntry = r_reify "DefinitionEntry"
  let cParameter_entry = r_reify "Build_parameter_entry"
  let cDefinition_entry = r_reify "Build_definition_entry"

  let (tcbv, tcbn, thnf, tall, tlazy, tunfold) = (r_template_monad "cbv", r_template_monad "cbn", r_template_monad "hnf", r_template_monad "all", r_template_monad "lazy", r_template_monad "unfold")

  let (tglobal_reference, tConstRef, tIndRef, tConstructRef) =
    (r_base_reify "global_reference", r_base_reify "ConstRef", r_base_reify "IndRef", r_base_reify "ConstructRef")

  let pkg_specif = ["Coq";"Init";"Specif"]
  let texistT = resolve_symbol pkg_specif "existT"
  let texistT_typed_term = r_template_monad_p "existT_typed_term"

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

  let rec seq f t =
    if f < t then f :: seq (f + 1) t
    else []


  let mkAnon () = Lazy.force nAnon
  let mkName id = constr_mkApp (nNamed, [| id |])

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
