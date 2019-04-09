open Univ
open Names
open Pp (* this adds the ++ to the current scope *)

open Tm_util
open Quoted
open Quoter
open Denoter
open Constr_quoter
open TemplateCoqQuoter


(* todo: the recursive call is uneeded provided we call it on well formed terms *)

let print_term (u: t) : Pp.t = pr_constr u

let strict_unquote_universe_mode = ref true

let unquote_pair trm =
  let (h,args) = app_full trm [] in
  if Constr.equal h c_pair then
    match args with
      _ :: _ :: x :: y :: [] -> (x, y)
    | _ -> bad_term_verb trm "unquote_pair"
  else
    not_supported_verb trm "unquote_pair"

let rec unquote_list trm =
  let (h,args) = app_full trm [] in
  if Constr.equal h c_nil then
    []
  else if Constr.equal h c_cons then
    match args with
      _ :: x :: xs :: [] -> x :: unquote_list xs
    | _ -> bad_term_verb trm "unquote_list"
  else
    not_supported_verb trm "unquote_list"


(* Unquote Coq nat to OCaml int *)
let rec unquote_nat trm =
  let (h,args) = app_full trm [] in
  if Constr.equal h tO then
    0
  else if Constr.equal h tS then
    match args with
      n :: [] -> 1 + unquote_nat n
    | _ -> bad_term_verb trm "unquote_nat"
  else
    not_supported_verb trm "unquote_nat"

let unquote_bool trm =
  if Constr.equal trm ttrue then
    true
  else if Constr.equal trm tfalse then
    false
  else not_supported_verb trm "from_bool"

let unquote_char trm =
  let (h,args) = app_full trm [] in
  if Constr.equal h tAscii then
    match args with
      a :: b :: c :: d :: e :: f :: g :: h :: [] ->
      let bits = List.rev [a;b;c;d;e;f;g;h] in
      let v = List.fold_left (fun a n -> (a lsl 1) lor if unquote_bool n then 1 else 0) 0 bits in
      char_of_int v
    | _ -> bad_term_verb trm "unquote_char"
  else
    not_supported trm

let unquote_string trm =
  let rec go n trm =
    let (h,args) = app_full trm [] in
    if Constr.equal h tEmptyString then
      Bytes.create n
    else if Constr.equal h tString then
      match args with
        c :: s :: [] ->
        let res = go (n + 1) s in
        let _ = Bytes.set res n (unquote_char c) in
        res
      | _ -> bad_term_verb trm "unquote_string"
    else
      not_supported_verb trm "unquote_string"
  in
  Bytes.to_string (go 0 trm)

let unquote_ident trm =
  Id.of_string (unquote_string trm)

let unquote_cast_kind trm =
  if Constr.equal trm kVmCast then
    Constr.VMcast
  else if Constr.equal trm kCast then
    Constr.DEFAULTcast
  else if Constr.equal trm kRevertCast then
    Constr.REVERTcast
  else if Constr.equal trm kNative then
    Constr.VMcast
  else
    not_supported_verb trm "unquote_cast_kind"

let unquote_name trm =
  let (h,args) = app_full trm [] in
  if Constr.equal h nAnon then
    Names.Anonymous
  else if Constr.equal h nNamed then
    match args with
      n :: [] -> Names.Name (unquote_ident n)
    | _ -> bad_term_verb trm "unquote_name"
  else
    not_supported_verb trm "unquote_name"

let get_level evm s =
  if CString.string_contains ~where:s ~what:"." then
    match List.rev (CString.split '.' s) with
    | [] -> CErrors.anomaly (str"Invalid universe name " ++ str s ++ str".")
    | n :: dp ->
      let num = int_of_string n in
      let dp = DirPath.make (List.map Id.of_string dp) in
      let l = Univ.Level.make dp num in
      try
        let evm = Evd.add_global_univ evm l in
        if !strict_unquote_universe_mode then
          CErrors.user_err ~hdr:"unquote_level" (str ("Level "^s^" is not a declared level and you are in Strict Unquote Universe Mode."))
        else (Feedback.msg_info (str"Fresh universe " ++ Level.pr l ++ str" was added to the context.");
              evm, l)
      with
      | UGraph.AlreadyDeclared -> evm, l
  else
    try
      evm, Evd.universe_of_name evm (Id.of_string s)
    with Not_found ->
    try
      let univ, k = Nametab.locate_universe (Libnames.qualid_of_string s) in
      evm, Univ.Level.make univ k
    with Not_found ->
      CErrors.user_err ~hdr:"unquote_level" (str ("Level "^s^" is not a declared level."))





let unquote_level evm trm (* of type level *) : Evd.evar_map * Univ.Level.t =
  let (h,args) = app_full trm [] in
  if Constr.equal h lProp then
    match args with
    | [] -> evm, Univ.Level.prop
    | _ -> bad_term_verb trm "unquote_level"
  else if Constr.equal h lSet then
    match args with
    | [] -> evm, Univ.Level.set
    | _ -> bad_term_verb trm "unquote_level"
  else if Constr.equal h tLevel then
    match args with
    | s :: [] -> debug (fun () -> str "Unquoting level " ++ pr_constr trm);
      get_level evm (unquote_string s)
    | _ -> bad_term_verb trm "unquote_level"
  else if Constr.equal h tLevelVar then
    match args with
    | l :: [] -> evm, Univ.Level.var (unquote_nat l)
    | _ -> bad_term_verb trm "unquote_level"
  else
    not_supported_verb trm "unquote_level"

let unquote_level_expr evm trm (* of type level *) b (* of type bool *) : Evd.evar_map * Univ.Universe.t =
  let evm, l = unquote_level evm trm in
  let u = Univ.Universe.make l in
  evm, if unquote_bool b then Univ.Universe.super u else u


let unquote_universe evm trm (* of type universe *) =
  let levels = List.map unquote_pair (unquote_list trm) in
  match levels with
  | [] -> if !strict_unquote_universe_mode then
      CErrors.user_err ~hdr:"unquote_universe" (str "It is not possible to unquote an empty universe in Strict Unquote Universe Mode.")
    else
      let evm, u = Evd.new_univ_variable (Evd.UnivFlexible false) evm in
      Feedback.msg_info (str"Fresh universe " ++ Universe.pr u ++ str" was added to the context.");
      evm, u
  | (l,b)::q -> List.fold_left (fun (evm,u) (l,b) -> let evm, u' = unquote_level_expr evm l b
                                 in evm, Univ.Universe.sup u u')
                  (unquote_level_expr evm l b) q

let map_evm (f : 'a -> 'b -> 'a * 'c) (evm : 'a) (l : 'b list) : 'a * ('c list) =
  let evm, res = List.fold_left (fun (evm, l) b -> let evm, c = f evm b in evm, c :: l) (evm, []) l in
  evm, List.rev res

let unquote_universe_instance evm trm (* of type universe_instance *) =
  let l = unquote_list trm in
  let evm, l = map_evm unquote_level evm l in
  evm, Univ.Instance.of_array (Array.of_list l)



let unquote_kn (k : quoted_kernel_name) : Libnames.qualid =
  Libnames.qualid_of_string (clean_name (unquote_string k))

let unquote_proj (qp : quoted_proj) : (quoted_inductive * quoted_int * quoted_int) =
  let (h,args) = app_full qp [] in
  match args with
  | tyin::tynat::indpars::idx::[] ->
    let (h',args') = app_full indpars [] in
    (match args' with
     | tyind :: tynat :: ind :: n :: [] -> (ind, n, idx)
     | _ -> bad_term_verb qp "unquote_proj")
  | _ -> bad_term_verb qp "unquote_proj"

let unquote_inductive trm =
  let (h,args) = app_full trm [] in
  if Constr.equal h tmkInd then
    match args with
      nm :: num :: _ ->
      let s = (unquote_string nm) in
      let (dp, nm) = split_name s in
      (try
         match Nametab.locate (Libnames.make_qualid dp nm) with
         | Globnames.ConstRef c ->  CErrors.user_err (str "this not an inductive constant. use tConst instead of tInd : " ++ str s)
         | Globnames.IndRef i -> (fst i, unquote_nat  num)
         | Globnames.VarRef _ -> CErrors.user_err (str "the constant is a variable. use tVar : " ++ str s)
         | Globnames.ConstructRef _ -> CErrors.user_err (str "the constant is a consructor. use tConstructor : " ++ str s)
       with
         Not_found ->   CErrors.user_err (str "Constant not found : " ++ str s))
    | _ -> assert false
  else
    bad_term_verb trm "non-constructor"

let inspect_term (t:Constr.t) :  (Constr.t, quoted_int, quoted_ident, quoted_name, quoted_sort, quoted_cast_kind, quoted_kernel_name, quoted_inductive, quoted_univ_instance, quoted_proj) structure_of_term =
  let (h,args) = app_full t [] in
  if Constr.equal h tRel then
    match args with
      x :: _ -> ACoq_tRel x
    | _ -> CErrors.user_err (print_term t ++ Pp.str ("has bad structure"))
  else if Constr.equal h tVar then
    match args with
      x :: _ -> ACoq_tVar x
    | _ -> CErrors.user_err (print_term t ++ Pp.str ("has bad structure"))
  else if Constr.equal h tMeta then
    match args with
      x :: _ -> ACoq_tMeta x
    | _ -> CErrors.user_err (print_term t ++ Pp.str ("has bad structure"))
  else if Constr.equal h tSort then
    match args with
      x :: _ -> ACoq_tSort x
    | _ -> CErrors.user_err (print_term t ++ Pp.str ("has bad structure"))
  else if Constr.equal h tCast then
    match args with
      x :: y :: z :: _ -> ACoq_tCast (x, y, z)
    | _ -> CErrors.user_err (print_term t ++ Pp.str ("has bad structure"))
  else if Constr.equal h tProd then
    match args with
      n :: t :: b :: _ -> ACoq_tProd (n,t,b)
    | _ -> CErrors.user_err (print_term t ++ Pp.str ("has bad structure"))
  else if Constr.equal h tLambda then
    match args with
      n  :: t :: b :: _ -> ACoq_tLambda (n,t,b)
    | _ -> CErrors.user_err (print_term t ++ Pp.str ("has bad structure"))
  else if Constr.equal h tLetIn then
    match args with
      n :: e :: t :: b :: _ -> ACoq_tLetIn (n,e,t,b)
    | _ -> CErrors.user_err (print_term t ++ Pp.str ("has bad structure"))
  else if Constr.equal h tApp then
    match args with
      f::xs::_ -> ACoq_tApp (f, unquote_list xs)
    | _ -> CErrors.user_err (print_term t ++ Pp.str ("has bad structure"))
  else if Constr.equal h tConst then
    match args with
      s::u::_ -> ACoq_tConst (s, u)
    | _ -> CErrors.user_err (print_term t ++ Pp.str ("has bad structure"))
  else if Constr.equal h tInd then
    match args with
      i::u::_ -> ACoq_tInd (i,u)
    | _ -> CErrors.user_err (print_term t ++ Pp.str ("has bad structure"))
  else if Constr.equal h tConstructor then
    match args with
      i::idx::u::_ -> ACoq_tConstruct (i,idx,u)
    | _ -> CErrors.user_err (print_term t ++ Pp.str ("has bad structure: constructor case"))
  else if Constr.equal h tCase then
    match args with
      info::ty::d::brs::_ -> ACoq_tCase (unquote_pair info, ty, d, List.map unquote_pair (unquote_list brs))
    | _ -> CErrors.user_err (print_term t ++ Pp.str ("has bad structure"))
  else if Constr.equal h tFix then
    match args with
      bds::i::_ ->
      let unquoteFbd  b  =
        let (_,args) = app_full b [] in
        match args with
        | _(*type*) :: na :: ty :: body :: rarg :: [] ->
            { adtype = ty;
              adname = na;
              adbody = body;
              rarg
            }
        |_ -> raise (Failure " (mkdef must take exactly 5 arguments)")
      in
      let lbd = List.map unquoteFbd (unquote_list bds) in
      ACoq_tFix (lbd, i)
    | _ -> CErrors.user_err (print_term t ++ Pp.str ("has bad structure"))
  else if Constr.equal h tCoFix then
    match args with
      bds::i::_ ->
      let unquoteFbd  b  =
        let (_,args) = app_full b [] in
        match args with
        | _(*type*) :: na :: ty :: body :: rarg :: [] ->
            { adtype = ty;
              adname = na;
              adbody = body;
              rarg
            }
        |_ -> raise (Failure " (mkdef must take exactly 5 arguments)")
      in
      let lbd = List.map unquoteFbd (unquote_list bds) in
      ACoq_tCoFix (lbd, i)
    | _ -> CErrors.user_err (print_term t ++ Pp.str ("has bad structure"))
  else if Constr.equal h tProj then
    match args with
      proj::t::_ -> ACoq_tProj (proj, t)
    | _ -> CErrors.user_err (print_term t ++ Pp.str ("has bad structure"))

  else
    CErrors.user_err (str"inspect_term: cannot recognize " ++ print_term t ++ str" (maybe you forgot to reduce it?)")
        
module Denote (D : Denoter) =
struct



(* If strict unquote universe mode is on then fail when unquoting a non *)
(* declared universe / an empty list of level expressions. *)
(* Otherwise, add it / a fresh level the global environnment. *)


let _ =
  let open Goptions in
  declare_bool_option
    { optdepr  = false;
      optname  = "strict unquote universe mode";
      optkey   = ["Strict"; "Unquote"; "Universe"; "Mode"];
      optread  = (fun () -> !strict_unquote_universe_mode);
      optwrite = (fun b -> strict_unquote_universe_mode := b) }




(* TODO: replace app_full by this abstract version?*)
let rec app_full_abs (trm: D.t) (acc: D.t list) =
  match D.inspect_term trm with
    ACoq_tApp (f, xs) -> app_full_abs f (xs @ acc)
  | _ -> (trm, acc)

let denote_term (evm : Evd.evar_map) (trm: D.t) : Evd.evar_map * Constr.t =
  let rec aux evm (trm: D.t) : _ * Constr.t =
(*    debug (fun () -> Pp.(str "denote_term" ++ spc () ++ pr_constr trm)) ; *)
    match D.inspect_term trm with
    | ACoq_tRel x -> evm, Constr.mkRel (D.unquote_int x + 1)
    | ACoq_tVar x -> evm, Constr.mkVar (D.unquote_ident x)
    | ACoq_tSort x -> let evm, u = D.unquote_universe evm x in evm, Constr.mkType u
    | ACoq_tCast (t,c,ty) -> let evm, t = aux evm t in
                             let evm, ty = aux evm ty in
                             evm, Constr.mkCast (t, D.unquote_cast_kind c, ty)
    | ACoq_tProd (n,t,b) -> let evm, t = aux evm t in
                            let evm, b = aux evm b in
                            evm, Constr.mkProd (D.unquote_name n, t, b)
    | ACoq_tLambda (n,t,b) -> let evm, t = aux evm t in
                              let evm, b = aux evm b in
                              evm, Constr.mkLambda (D.unquote_name n, t, b)
    | ACoq_tLetIn (n,e,t,b) -> let evm, e = aux evm e in
                               let evm, t = aux evm t in
                               let evm, b = aux evm b in
                               evm, Constr.mkLetIn (D.unquote_name n, e, t, b)
    | ACoq_tApp (f,xs) -> let evm, f = aux evm f in
                          let evm, xs = map_evm aux evm xs in
                          evm, Constr.mkApp (f, Array.of_list xs)
    | ACoq_tConst (s,u) ->
       let s = D.unquote_kn s in
       let evm, u = D.unquote_universe_instance evm u in
       (try
          match Nametab.locate s with
          | Globnames.ConstRef c -> evm, Constr.mkConstU (c, u)
          | Globnames.IndRef _ -> CErrors.user_err (str"The constant " ++ Libnames.pr_qualid s ++ str" is an inductive, use tInd.")
          | Globnames.VarRef _ -> CErrors.user_err (str"The constant " ++ Libnames.pr_qualid s ++ str" is a variable, use tVar.")
          | Globnames.ConstructRef _ -> CErrors.user_err (str"The constant " ++ Libnames.pr_qualid s ++ str" is a constructor, use tConstructor.")
        with
          Not_found -> CErrors.user_err (str"Constant not found: " ++ Libnames.pr_qualid s))
    | ACoq_tConstruct (i,idx,u) ->
       let ind = D.unquote_inductive i in
       let evm, u = D.unquote_universe_instance evm u in
       evm, Constr.mkConstructU ((ind, D.unquote_int idx + 1), u)
    | ACoq_tInd (i, u) ->
       let i = D.unquote_inductive i in
       let evm, u = D.unquote_universe_instance evm u in
       evm, Constr.mkIndU (i, u)
    | ACoq_tCase ((i, _), ty, d, brs) ->
       let ind = D.unquote_inductive i in
       let evm, ty = aux evm ty in
       let evm, d = aux evm d in
       let evm, brs = map_evm aux evm (List.map snd brs) in
       (* todo: reify better case_info *)
       let ci = Inductiveops.make_case_info (Global.env ()) ind Constr.RegularStyle in
       evm, Constr.mkCase (ci, ty, d, Array.of_list brs)
    | ACoq_tFix (lbd, i) ->
       let (names,types,bodies,rargs) = (List.map (fun p->p.adname) lbd,  List.map (fun p->p.adtype) lbd, List.map (fun p->p.adbody) lbd,
                                         List.map (fun p->p.rarg) lbd) in
       let evm, types = map_evm aux evm types in
       let evm, bodies = map_evm aux evm bodies in
       let (names,rargs) = (List.map D.unquote_name names, List.map D.unquote_int rargs) in
       let la = Array.of_list in
       evm, Constr.mkFix ((la rargs, D.unquote_int i), (la names, la types, la bodies))
    | ACoq_tCoFix (lbd, i) ->
       let (names,types,bodies,rargs) = (List.map (fun p->p.adname) lbd,  List.map (fun p->p.adtype) lbd, List.map (fun p->p.adbody) lbd,
                                         List.map (fun p->p.rarg) lbd) in
       let evm, types = map_evm aux evm types in
       let evm, bodies = map_evm aux evm bodies in
       let (names,rargs) = (List.map D.unquote_name names, List.map D.unquote_int rargs) in
       let la = Array.of_list in
       evm, Constr.mkCoFix (D.unquote_int i, (la names, la types, la bodies))
    | ACoq_tProj (proj,t) ->
       let (ind, _, narg) = D.unquote_proj proj in (* todo: is narg the correct projection? *)
       let ind' = D.unquote_inductive ind in
       let projs = Recordops.lookup_projections ind' in
       let evm, t = aux evm t in
       (match List.nth projs (D.unquote_int narg) with
        | Some p -> evm, Constr.mkProj (Names.Projection.make p false, t)
        | None -> (*bad_term trm *) failwith "tproj case of denote_term")
    | _ -> failwith "big case of denote_term"
  in aux evm trm

end

open Denoter
open Constr_quoter
module CoqLiveDenoter =
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
  type quoted_constraint_type = Constr.t (* of type univ.constraint_type *)
  type quoted_univ_constraint = Constr.t (* of type univ.univ_constraint *)
  type quoted_univ_constraints = Constr.t (* of type univ.constraints *)
  type quoted_univ_instance = Constr.t (* of type univ.universe_instance *)
  type quoted_univ_context = Constr.t (* of type univ.universe_context *)
  type quoted_inductive_universes = Constr.t (* of type univ.universe_context *)

  type quoted_mind_params = Constr.t (* of type list (Ast.ident * list (ident * local_entry)local_entry) *)
  type quoted_ind_entry = quoted_ident * t * quoted_bool * quoted_ident list * t list
  type quoted_definition_entry = t * t option * quoted_univ_context
  type quoted_mind_entry = Constr.t (* of type Ast.mutual_inductive_entry *)
  type quoted_mind_finiteness = Constr.t (* of type Ast.mutual_inductive_entry ?? *)
  type quoted_entry = Constr.t (* of type option (constant_entry + mutual_inductive_entry) *)

  type quoted_context_decl = Constr.t (* in Ast *)
  type quoted_context = Constr.t (* in Ast *)

  type quoted_one_inductive_body = Constr.t (* of type Ast.one_inductive_body *)
  type quoted_mutual_inductive_body = Constr.t (* of type Ast.mutual_inductive_body *)
  type quoted_constant_body = Constr.t (* of type Ast.constant_body *)
  type quoted_global_decl = Constr.t (* of type Ast.global_decl *)
  type quoted_global_declarations = Constr.t (* of type Ast.global_declarations *)
  type quoted_program = Constr.t (* of type Ast.program *)

  type quoted_reduction_strategy = Constr.t (* of type Ast.reductionStrategy *)

  let unquote_ident=unquote_ident
  let unquote_name=unquote_name
  let unquote_int=unquote_nat
  let print_term=print_term
  let inspect_term=inspect_term 
  let unquote_universe_instance=unquote_universe_instance

  let unquote_universe=unquote_universe
  let unquote_proj=unquote_proj
  let unquote_inductive=unquote_inductive
  let unquote_kn=unquote_kn
  let unquote_cast_kind=unquote_cast_kind
  let unquote_bool=unquote_bool



  let mkAnon = mkAnon
  let mkName = mkName
  let quote_kn = quote_kn
  let mkRel = mkRel
  let mkVar = mkVar
  let mkMeta = mkMeta
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
end



module CoqLiveDenote = Denote(CoqLiveDenoter)

let denote_term=CoqLiveDenote.denote_term

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
  type quoted_sort = Univ0.universe
  type quoted_cast_kind = cast_kind
  type quoted_kernel_name = char list
  type quoted_inductive = inductive
  type quoted_proj = projection
  type quoted_global_reference = global_reference

  type quoted_sort_family = sort_family
  type quoted_constraint_type = Univ0.constraint_type
  type quoted_univ_constraint = Univ0.univ_constraint
  type quoted_univ_instance = Univ0.Instance.t
  type quoted_univ_constraints = Univ0.constraints
  type quoted_univ_context = Univ0.universe_context
  type quoted_inductive_universes = quoted_univ_context

  type quoted_mind_params = (ident * local_entry) list
  type quoted_ind_entry = quoted_ident * t * quoted_bool * quoted_ident list * t list
  type quoted_definition_entry = t * t option * quoted_univ_context
  type quoted_mind_entry = mutual_inductive_entry
  type quoted_mind_finiteness = recursivity_kind
  type quoted_entry = (constant_entry, quoted_mind_entry) sum option

  type quoted_context_decl = context_decl
  type quoted_context = context
  type quoted_one_inductive_body = one_inductive_body
  type quoted_mutual_inductive_body = mutual_inductive_body
  type quoted_constant_body = constant_body
  type quoted_global_decl = global_decl
  type quoted_global_declarations = global_declarations
  type quoted_program = program

  let mkAnon = mkAnon
  let mkName = mkName
  let quote_kn = quote_kn
  let mkRel = mkRel
  let mkVar = mkVar
  let mkMeta = mkMeta
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
  let print_term (u: t) : Pp.t = Pp.str "printing not implemented"

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
    | Coq_tMeta n -> ACoq_tMeta n
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
  = failwith "nyi"
  let unquote_name (qn: quoted_name) : Name.t
  = failwith "nyi"
  let unquote_int (q:  quoted_int ) : int
  = failwith "nyi"
  let unquote_bool (q: quoted_bool ) : bool
  = failwith "nyi"
  let unquote_cast_kind (q: quoted_cast_kind ) : Constr.cast_kind
  = failwith "nyi"
  let unquote_kn (q:  quoted_kernel_name ) : Libnames.qualid
  = failwith "nyi"
  let unquote_inductive (q:  quoted_inductive ) : Names.inductive
  = failwith "nyi"
  let unquote_proj (q: quoted_proj ) : (quoted_inductive * quoted_int * quoted_int)
  = failwith "nyi"
  let unquote_universe (q: Evd.evar_map) (qs: quoted_sort): Evd.evar_map * Univ.Universe.t
  = failwith "nyi"
  let unquote_universe_instance(q: Evd.evar_map) (qu: quoted_univ_instance): Evd.evar_map * Univ.Instance.t
  = failwith "nyi"
  
end

module  ExtractionDenote = Denote(ExtractionDenoter)
