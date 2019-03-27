open CErrors
open Univ
open Entries
open Names
open Redops
open Genredexpr
open Pp (* this adds the ++ to the current scope *)

open Quoter
open Constr_quoter
open TemplateCoqQuoter
open Template_monad

(* todo: the recursive call is uneeded provided we call it on well formed terms *)
let rec app_full trm acc =
  match Constr.kind trm with
    Constr.App (f, xs) -> app_full f (Array.to_list xs @ acc)
  | _ -> (trm, acc)

let print_term (u: t) : Pp.t = pr_constr u

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


let inspectTerm (t:Constr.t) :  (Constr.t, quoted_int, quoted_ident, quoted_name, quoted_sort, quoted_cast_kind, quoted_kernel_name, quoted_inductive, quoted_univ_instance, quoted_proj) structure_of_term =
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


(* If strict unquote universe mode is on then fail when unquoting a non *)
(* declared universe / an empty list of level expressions. *)
(* Otherwise, add it / a fresh level the global environnment. *)

let strict_unquote_universe_mode = ref true

let _ =
  let open Goptions in
  declare_bool_option
    { optdepr  = false;
      optname  = "strict unquote universe mode";
      optkey   = ["Strict"; "Unquote"; "Universe"; "Mode"];
      optread  = (fun () -> !strict_unquote_universe_mode);
      optwrite = (fun b -> strict_unquote_universe_mode := b) }

let map_evm (f : 'a -> 'b -> 'a * 'c) (evm : 'a) (l : 'b list) : 'a * ('c list) =
  let evm, res = List.fold_left (fun (evm, l) b -> let evm, c = f evm b in evm, c :: l) (evm, []) l in
  evm, List.rev res



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



(* TODO: replace app_full by this abstract version?*)
let rec app_full_abs (trm: Constr.t) (acc: Constr.t list) =
  match inspectTerm trm with
    ACoq_tApp (f, xs) -> app_full_abs f (xs @ acc)
  | _ -> (trm, acc)


let denote_term evm (trm: Constr.t) : Evd.evar_map * Constr.t =
  let rec aux evm (trm: Constr.t) : _ * Constr.t =
    debug (fun () -> Pp.(str "denote_term" ++ spc () ++ pr_constr trm)) ;
    match (inspectTerm trm) with
    | ACoq_tRel x -> evm, Constr.mkRel (unquote_nat x + 1)
    | ACoq_tVar x -> evm, Constr.mkVar (unquote_ident x)
    | ACoq_tSort x -> let evm, u = unquote_universe evm x in evm, Constr.mkType u
    | ACoq_tCast (t,c,ty) -> let evm, t = aux evm t in
                             let evm, ty = aux evm ty in
                             evm, Constr.mkCast (t, unquote_cast_kind c, ty)
    | ACoq_tProd (n,t,b) -> let evm, t = aux evm t in
                            let evm, b = aux evm b in
                            evm, Constr.mkProd (unquote_name n, t, b)
    | ACoq_tLambda (n,t,b) -> let evm, t = aux evm t in
                              let evm, b = aux evm b in
                              evm, Constr.mkLambda (unquote_name n, t, b)
    | ACoq_tLetIn (n,e,t,b) -> let evm, e = aux evm e in
                               let evm, t = aux evm t in
                               let evm, b = aux evm b in
                               evm, Constr.mkLetIn (unquote_name n, e, t, b)
    | ACoq_tApp (f,xs) -> let evm, f = aux evm f in
                          let evm, xs = map_evm aux evm xs in
                          evm, Constr.mkApp (f, Array.of_list xs)
    | ACoq_tConst (s,u) ->
       let s = unquote_kn s in
       let evm, u = unquote_universe_instance evm u in
       (try
          match Nametab.locate s with
          | Globnames.ConstRef c -> evm, Constr.mkConstU (c, u)
          | Globnames.IndRef _ -> CErrors.user_err (str"The constant " ++ Libnames.pr_qualid s ++ str" is an inductive, use tInd.")
          | Globnames.VarRef _ -> CErrors.user_err (str"The constant " ++ Libnames.pr_qualid s ++ str" is a variable, use tVar.")
          | Globnames.ConstructRef _ -> CErrors.user_err (str"The constant " ++ Libnames.pr_qualid s ++ str" is a constructor, use tConstructor.")
        with
          Not_found -> CErrors.user_err (str"Constant not found: " ++ Libnames.pr_qualid s))
    | ACoq_tConstruct (i,idx,u) ->
       let ind = unquote_inductive i in
       let evm, u = unquote_universe_instance evm u in
       evm, Constr.mkConstructU ((ind, unquote_nat idx + 1), u)
    | ACoq_tInd (i, u) ->
       let i = unquote_inductive i in
       let evm, u = unquote_universe_instance evm u in
       evm, Constr.mkIndU (i, u)
    | ACoq_tCase ((i, _), ty, d, brs) ->
       let ind = unquote_inductive i in
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
       let (names,rargs) = (List.map unquote_name names, List.map unquote_nat rargs) in
       let la = Array.of_list in
       evm, Constr.mkFix ((la rargs,unquote_nat i), (la names, la types, la bodies))
    | ACoq_tCoFix (lbd, i) ->
       let (names,types,bodies,rargs) = (List.map (fun p->p.adname) lbd,  List.map (fun p->p.adtype) lbd, List.map (fun p->p.adbody) lbd,
                                         List.map (fun p->p.rarg) lbd) in
       let evm, types = map_evm aux evm types in
       let evm, bodies = map_evm aux evm bodies in
       let (names,rargs) = (List.map unquote_name names, List.map unquote_nat rargs) in
       let la = Array.of_list in
       evm, Constr.mkCoFix (unquote_nat i, (la names, la types, la bodies))
    | ACoq_tProj (proj,t) ->
       let (ind, _, narg) = unquote_proj proj in (* todo: is narg the correct projection? *)
       let ind' = unquote_inductive ind in
       let projs = Recordops.lookup_projections ind' in
       let evm, t = aux evm t in
       (match List.nth projs (unquote_nat narg) with
        | Some p -> evm, Constr.mkProj (Names.Projection.make p false, t)
        | None -> bad_term trm)
    | _ ->  not_supported_verb trm "big_case"
  in aux evm trm



let unquote_reduction_strategy env evm trm (* of type reductionStrategy *) : Redexpr.red_expr =
  let (trm, args) = app_full trm [] in
  (* from g_tactic.ml4 *)
  let default_flags = Redops.make_red_flag [FBeta;FMatch;FFix;FCofix;FZeta;FDeltaBut []] in
  if Constr.equal trm tcbv then Cbv default_flags
  else if Constr.equal trm tcbn then Cbn default_flags
  else if Constr.equal trm thnf then Hnf
  else if Constr.equal trm tall then Cbv all_flags
  else if Constr.equal trm tlazy then Lazy all_flags
  else if Constr.equal trm tunfold then
    match args with
    | name (* to unfold *) :: _ ->
       let name = reduce_all env evm name in
       let name = unquote_ident name in
       (try Unfold [Locus.AllOccurrences, Tacred.evaluable_of_global_reference env (Nametab.global (CAst.make (Libnames.Qualid (Libnames.qualid_of_ident name))))]
        with
        | _ -> CErrors.user_err (str "Constant not found or not a constant: " ++ Pp.str (Names.Id.to_string name)))
    | _ -> bad_term_verb trm "unquote_reduction_strategy"
  else not_supported_verb trm "unquote_reduction_strategy"



let denote_local_entry evm trm =
  let (h,args) = app_full trm [] in
  match args with
    x :: [] ->
    if Constr.equal h tLocalDef then
      let evm, x = denote_term evm x in
      evm, Entries.LocalDefEntry x
    else if  Constr.equal h tLocalAssum then
      let evm, x = denote_term evm x in
      evm, Entries.LocalAssumEntry x
    else
      not_supported_verb trm "denote_local_entry"
  | _ -> bad_term_verb trm "denote_local_entry"

let denote_mind_entry_finite trm =
  let (h,args) = app_full trm [] in
  match args with
    [] ->
    if Constr.equal h cFinite then Declarations.Finite
    else if  Constr.equal h cCoFinite then Declarations.CoFinite
    else if  Constr.equal h cBiFinite then Declarations.BiFinite
    else not_supported_verb trm "denote_mind_entry_finite"
  | _ -> bad_term_verb trm "denote_mind_entry_finite"



let unquote_map_option f trm =
  let (h,args) = app_full trm [] in
  if Constr.equal h cSome then
    match args with
      _ :: x :: [] -> Some (f x)
    | _ -> bad_term trm
  else if Constr.equal h cNone then
    match args with
      _ :: [] -> None
    | _ -> bad_term trm
  else
    not_supported_verb trm "unquote_map_option"

let denote_option = unquote_map_option (fun x -> x)



let unquote_constraint_type trm (* of type constraint_type *) : constraint_type =
  let (h,args) = app_full trm [] in
  match args with
    [] ->
    if Constr.equal h tunivLt then Univ.Lt
    else if Constr.equal h tunivLe then Univ.Le
    else if Constr.equal h tunivEq then Univ.Eq
    else not_supported_verb trm "unquote_constraint_type"
  | _ -> bad_term_verb trm "unquote_constraint_type"

let unquote_univ_constraint evm c (* of type univ_constraint *) : _ * univ_constraint =
  let c, l2 = unquote_pair c in
  let l1, c = unquote_pair c in
  let evm, l1 = unquote_level evm l1 in
  let evm, l2 = unquote_level evm l2 in
  let c = unquote_constraint_type c in
  evm, (l1, c, l2)

(* set given by MSets.MSetWeakList.Make *)
let unquote_set trm =
  let (h, args) = app_full trm [] in
  (* h supposed to be Mkt, the constructor of the record *)
  match args with
  | list :: ok :: [] -> unquote_list list
  | _ -> not_supported_verb trm "unquote_set"

let unquote_constraints evm c (* of type constraints *) : _ * Constraint.t =
  let c = unquote_set c in
  List.fold_left (fun (evm, set) c -> let evm, c = unquote_univ_constraint evm c in evm, Constraint.add c set)
                 (evm, Constraint.empty) c 


let denote_variance trm (* of type Variance *) : Variance.t =
  if Constr.equal trm cIrrelevant then Variance.Irrelevant
  else if Constr.equal trm cCovariant then Variance.Covariant
  else if Constr.equal trm cInvariant then Variance.Invariant
  else not_supported_verb trm "denote_variance"

let denote_ucontext evm trm (* of type UContext.t *) : _ * UContext.t =
  let i, c = unquote_pair trm in
  let evm, i = unquote_universe_instance evm i in
  let evm, c = unquote_constraints evm c in
  evm, Univ.UContext.make (i, c)

let denote_cumulativity_info evm trm (* of type CumulativityInfo *) : _ * CumulativityInfo.t =
  let uctx, variances = unquote_pair trm in
  let evm, uctx = denote_ucontext evm uctx in
  let variances = List.map denote_variance (unquote_list variances) in
  evm, CumulativityInfo.make (uctx, Array.of_list variances)


(* todo : stick to Coq implem *)
type universe_context_type =
  | Monomorphic_uctx of Univ.UContext.t
  | Polymorphic_uctx of Univ.UContext.t
  | Cumulative_uctx of Univ.CumulativityInfo.t

let to_entry_inductive_universes = function
  | Monomorphic_uctx ctx -> Monomorphic_ind_entry (ContextSet.of_context ctx)
  | Polymorphic_uctx ctx -> Polymorphic_ind_entry ctx
  | Cumulative_uctx ctx -> Cumulative_ind_entry ctx

let denote_universe_context evm trm (* of type universe_context *) : _ * universe_context_type =
  let (h, args) = app_full trm [] in
  match args with
  | ctx :: [] -> if Constr.equal h cMonomorphic_ctx then
                   let evm, ctx = denote_ucontext evm ctx in
                   evm, Monomorphic_uctx ctx
                 else if Constr.equal h cPolymorphic_ctx then
                   let evm, ctx = denote_ucontext evm ctx in
                   evm, Polymorphic_uctx ctx
                 else if Constr.equal h cCumulative_ctx then
                   let evm, ctx = denote_cumulativity_info evm ctx in
                   evm, Cumulative_uctx ctx
                 else
                   not_supported_verb trm "denote_universe_context"
  | _ -> bad_term_verb trm "denote_universe_context"



let unquote_one_inductive_entry evm trm (* of type one_inductive_entry *) : _ * Entries.one_inductive_entry =
  let (h,args) = app_full trm [] in
  if Constr.equal h tBuild_one_inductive_entry then
    match args with
    | id::ar::template::cnames::ctms::[] ->
       let id = unquote_ident id in
       let evm, ar = denote_term evm ar in
       let template = unquote_bool template in
       let cnames = List.map unquote_ident (unquote_list cnames) in
       let evm, ctms = map_evm denote_term evm (unquote_list ctms) in
       evm, { mind_entry_typename = id ;
              mind_entry_arity = ar;
              mind_entry_template = template;
              mind_entry_consnames = cnames;
              mind_entry_lc = ctms }
    | _ -> bad_term_verb trm "unquote_one_inductive_entry"
  else
    not_supported_verb trm "unquote_one_inductive_entry"

let unquote_mutual_inductive_entry evm trm (* of type mutual_inductive_entry *) : _ * Entries.mutual_inductive_entry =
  let (h,args) = app_full trm [] in
  if Constr.equal h tBuild_mutual_inductive_entry then
    match args with
    | record::finite::params::inds::univs::priv::[] ->
       let record = unquote_map_option (unquote_map_option unquote_ident) record in
       let finite = denote_mind_entry_finite finite in
       let evm, params = map_evm (fun evm p -> let (l,r) = unquote_pair p in
                                               let evm, e = denote_local_entry evm r in
                                               evm, (unquote_ident l, e))
                                 evm (unquote_list params) in
       let evm, inds = map_evm unquote_one_inductive_entry evm (unquote_list inds) in
       let evm, univs = denote_universe_context evm univs in
       let priv = unquote_map_option unquote_bool priv in
       evm, { mind_entry_record = record;
              mind_entry_finite = finite;
              mind_entry_params = params;
              mind_entry_inds = inds;
              mind_entry_universes = to_entry_inductive_universes univs;
              mind_entry_private = priv }
    | _ -> bad_term_verb trm "unquote_mutual_inductive_entry"
  else
    not_supported_verb trm "unquote_mutual_inductive_entry"


let declare_inductive (env: Environ.env) (evm: Evd.evar_map) (mind: Constr.t) : unit =
  let mind = reduce_all env evm mind in
  debug (fun () -> str"declare_inductive: " ++ pr_constr mind);
  let evm, mind = unquote_mutual_inductive_entry evm mind in
  ignore (ComInductive.declare_mutual_inductive_with_eliminations mind Names.Id.Map.empty [])

let not_in_tactic s =
  CErrors.user_err  (str ("You can not use " ^ s ^ " in a tactic."))

let monad_failure_full s k prg =
  CErrors.user_err
    (str (s ^ " must take " ^ (string_of_int k) ^ " argument" ^ (if k > 0 then "s" else "") ^ ".") ++
       str "While trying to run: " ++ fnl () ++ print_term prg ++ fnl () ++
       str "Please file a bug with Template-Coq.")

(* note(gmm): polymorphism should probably be part an argument to `do_definition`
 *)
let do_definition evm k (name : Names.Id.t) (typ : Constr.t option) (body : Constr.t) =
  let univs =
    if Flags.is_universe_polymorphism ()
    then Polymorphic_const_entry (Evd.to_universe_context evm)
    else Monomorphic_const_entry (Evd.universe_context_set evm) in
  let n =
      Declare.declare_definition ~kind:k name ?types:typ
        (body, univs)
  in
  Constr.mkConst n

let do_lemma env evm k (ident : Names.Id.t) (typ : Constr.t) (body : Constr.t) =
  let poly = Flags.is_universe_polymorphism () in
  let kind = (Decl_kinds.Global, poly, Decl_kinds.Definition) in
  let hole = CAst.make (Constrexpr.CHole (None, Misctypes.IntroAnonymous, None)) in
  let evm, (c, _) =
    Constrintern.interp_casted_constr_evars_impls env evm hole
      (EConstr.of_constr typ)
  in
  Obligations.check_evars env evm;
  let obls, _, c, cty =
    Obligations.eterm_obligations env ident evm 0 (EConstr.to_constr evm c) typ
  in
  let ctx = Evd.evar_universe_context evm in
  let hook =
    Lemmas.mk_hook (fun _ gr _ -> let env = Global.env () in
                     let evm = Evd.from_env env in
                     let evm, t = Evd.fresh_global env evm gr in
                     k (evm, t)) in
  ignore (Obligations.add_definition ident ~term:c cty ctx ~kind ~hook obls)
  (* question(gmm): why is this so different from `do_definition`? *)

let do_axiom evm (ident : Names.Id.t) (typ : Constr.t) =
    let param =
      Entries.ParameterEntry
        (None, (typ, Monomorphic_const_entry (Evd.universe_context_set evm)), None)
    in
    let n =
      Declare.declare_constant ident
        (param, Decl_kinds.IsDefinition Decl_kinds.Definition)
    in
    Constr.mkConst n


let under_option (f : Constr.t -> 'b) (t : Constr.t)
  : 'b option =
  match denote_option t with
    Some t -> Some (f t)
  | None -> None


let rec run_template_program_rec ?(intactic=false) (k : Environ.env * Evd.evar_map * Constr.t -> unit) env ((evm, pgm) : Evd.evar_map * Constr.t) : unit =
  let open TemplateMonad in
  let (kind, universes) = next_action env pgm in
  match kind with
    TmReturn h ->
     let (evm, _) = Typing.type_of env evm (EConstr.of_constr h) in
     k (env, evm, h)
  | TmBind (a,f) ->
    run_template_program_rec ~intactic:intactic (fun (env, evm, ar) -> run_template_program_rec ~intactic:intactic k env (evm, Constr.mkApp (f, [|ar|]))) env (evm, a)
  | TmDefinition (name,s,typ,body) ->
    let name = reduce_all env evm name in
    let evm, typ = (match denote_option s with Some s -> let red = unquote_reduction_strategy env evm s in reduce env evm red typ | None -> evm, typ) in
    let univs =
      if Flags.is_universe_polymorphism () then Polymorphic_const_entry (Evd.to_universe_context evm)
      else Monomorphic_const_entry (Evd.universe_context_set evm) in
    let n = Declare.declare_definition ~kind:Decl_kinds.Definition (unquote_ident name) ~types:typ (body, univs) in
    let env = Global.env () in
    k (env, evm, Constr.mkConst n)

  | TmMkDefinition (name, body) ->
    let name = reduce_all env evm name in
    let body = reduce_all env evm body in
    let evm, trm = denote_term evm body in
    let (evm, _) = Typing.type_of env evm (EConstr.of_constr trm) in
    let _ = Declare.declare_definition ~kind:Decl_kinds.Definition (unquote_ident name) (trm, Monomorphic_const_entry (Evd.universe_context_set evm)) in
    let env = Global.env () in
    k (env, evm, unit_tt)
  | TmDefinitionTerm (Definition, name, typ, body) ->
    let name = unquote_ident (reduce_all env evm name) in
    let evm,body = denote_term evm body in
    let evm,typ =
      match
        under_option (fun t -> denote_term evm (reduce_all env evm t))
          typ
      with
      | None -> (evm, None)
      | Some (evm,t) -> (evm, Some t)
    in
    let res = do_definition evm Decl_kinds.Definition name typ body in
    k (env, evm, res)
  | TmDefinitionTerm (Lemma, name, typ, body) ->
    let name = reduce_all env evm name in
    let poly = Flags.is_universe_polymorphism () in
    let kind = (Decl_kinds.Global, poly, Decl_kinds.Definition) in
    let hole = CAst.make (Constrexpr.CHole (None, Misctypes.IntroAnonymous, None)) in
    let evm, (c, _) = Constrintern.interp_casted_constr_evars_impls env evm hole (EConstr.of_constr typ) in
    let ident = unquote_ident name in
    Obligations.check_evars env evm;
    let obls, _, c, cty = Obligations.eterm_obligations env ident evm 0 (EConstr.to_constr evm c) typ in
    (* let evm = Evd.minimize_universes evm in *)
    let ctx = Evd.evar_universe_context evm in
    let hook = Lemmas.mk_hook (fun _ gr _ -> let env = Global.env () in
                                let evm = Evd.from_env env in
                                let evm, t = Evd.fresh_global env evm gr in k (env, evm, t)) in
    ignore (Obligations.add_definition ident ~term:c cty ctx ~kind ~hook obls)
  (* let kind = Decl_kinds.(Global, Flags.use_polymorphic_flag (), DefinitionBody Definition) in *)
  (* Lemmas.start_proof (unquote_ident name) kind evm (EConstr.of_constr typ) *)
  (* (Lemmas.mk_hook (fun _ gr -> *)
  (* let evm, t = Evd.fresh_global env evm gr in k (env, evm, t) *)
  (* k (env, evm, unit_tt) *)
  (* )); *)

  | TmAxiom (name,s,typ) ->
    let name = reduce_all env evm name in
    let evm, typ = (match denote_option s with Some s -> let red = unquote_reduction_strategy env evm s in reduce env evm red typ | None -> evm, typ) in
    let param = Entries.ParameterEntry (None, (typ, Monomorphic_const_entry (Evd.universe_context_set evm)), None) in
    let n = Declare.declare_constant (unquote_ident name) (param, Decl_kinds.IsDefinition Decl_kinds.Definition) in
    let env = Global.env () in
    k (env, evm, Constr.mkConst n)
  | TmAxiomTerm (name,typ) ->
    let name = unquote_ident (reduce_all env evm name) in
    let evm,typ = denote_term evm (reduce_all env evm typ) in
    let res = do_axiom evm name typ in
    let env = Global.env () in
    k (env, evm, res)
  | TmLemma (name,s,typ) ->
    let name = reduce_all env evm name in
    let evm, typ = (match denote_option s with Some s -> let red = unquote_reduction_strategy env evm s in reduce env evm red typ | None -> evm, typ) in
    let poly = Flags.is_universe_polymorphism () in
    let kind = (Decl_kinds.Global, poly, Decl_kinds.Definition) in
    let hole = CAst.make (Constrexpr.CHole (None, Misctypes.IntroAnonymous, None)) in
    let evm, (c, _) = Constrintern.interp_casted_constr_evars_impls env evm hole (EConstr.of_constr typ) in
    let ident = unquote_ident name in
    Obligations.check_evars env evm;
       let obls, _, c, cty = Obligations.eterm_obligations env ident evm 0 (EConstr.to_constr evm c) typ in
       (* let evm = Evd.minimize_universes evm in *)
       let ctx = Evd.evar_universe_context evm in
       let hook = Lemmas.mk_hook (fun _ gr _ -> let env = Global.env () in
                                                let evm = Evd.from_env env in
                                                let evm, t = Evd.fresh_global env evm gr in k (env, evm, t)) in  (* todo better *)
       ignore (Obligations.add_definition ident ~term:c cty ctx ~kind ~hook obls)
    (* let kind = Decl_kinds.(Global, Flags.use_polymorphic_flag (), DefinitionBody Definition) in *)
    (* Lemmas.start_proof (unquote_ident name) kind evm (EConstr.of_constr typ) *)
    (* (Lemmas.mk_hook (fun _ gr -> *)
    (* let evm, t = Evd.fresh_global env evm gr in k (env, evm, t) *)
    (* k (env, evm, unit_tt) *)
    (* )); *)
  | TmQuote (false, trm) ->
    let qt = TermReify.quote_term env trm (* user should do the reduction (using tmEval) if they want *)
    in k (env, evm, qt)
  | TmQuote (true, trm) ->
    let qt = TermReify.quote_term_rec env trm in
    k (env, evm, qt)
  | TmQuoteInd name ->
       let name = reduce_all env evm name in
       let name = unquote_string name in
       let (dp, nm) = split_name name in
       (match Nametab.locate (Libnames.make_qualid dp nm) with
        | Globnames.IndRef ni ->
           let t = TermReify.quote_mind_decl env (fst ni) in
           let _, args = Constr.destApp t in
           (match args with
            | [|kn; decl|] ->
               k (env, evm, decl)
            | _ -> bad_term_verb t "anomaly in quoting of inductive types")
        (* quote_mut_ind produce an entry rather than a decl *)
        (* let c = Environ.lookup_mind (fst ni) env in (\* FIX: For efficienctly, we should also export (snd ni)*\) *)
        (* TermReify.quote_mut_ind env c *)
        | _ -> CErrors.user_err (str name ++ str " does not seem to be an inductive."))
  | TmQuoteConst (name,bypass) ->
       let name = reduce_all env evm name in
       let name = unquote_string name in
       let bypass = reduce_all env evm bypass in
       let bypass = unquote_bool bypass in
       let entry = TermReify.quote_entry_aux bypass env evm name in
       let entry =
         match entry with
         | Some (Left cstentry) -> TemplateCoqQuoter.quote_constant_entry cstentry
         | Some (Right _) -> CErrors.user_err (str name ++ str " refers to an inductive")
         | None -> bad_term_verb pgm "anomaly in QuoteConstant"
       in
       k (env, evm, entry)
  | TmQuoteUnivs ->
    let univs = Environ.universes env in
    k (env, evm, quote_ugraph univs)
  | TmPrint trm -> Feedback.msg_info (pr_constr trm);
    k (env, evm, unit_tt)
  | TmMsg msg ->
     let msg = reduce_all env evm msg in
     let msg = unquote_string msg in
     Feedback.msg_info (str msg);
     k (env, evm, unit_tt)
  | TmFail trm ->
    CErrors.user_err (str (unquote_string trm))
  | TmAbout id ->
    begin
      let id = unquote_string id in
      try
        let gr = Smartlocate.locate_global_with_alias (CAst.make (Libnames.qualid_of_string id)) in
        let opt = Constr.mkApp (cSome , [|tglobal_reference ; quote_global_reference gr|]) in
        k (env, evm, opt)
      with
      | Not_found -> k (env, evm, Constr.mkApp (cNone, [|tglobal_reference|]))
    end
  | TmCurrentModPath ->
    let mp = Lib.current_mp () in
    (* let dp' = Lib.cwd () in (* different on sections ? *) *)
    let s = quote_string (Names.ModPath.to_string mp) in
    k (env, evm, s)
  | TmEval (s, trm) ->
    let red = unquote_reduction_strategy env evm s in
    let (evm, trm) = reduce env evm red trm
    in k (env, evm, trm)
  | TmEvalTerm (s,trm) ->
    let red = unquote_reduction_strategy env evm s in
    let evdref = ref evm in
    let (evm, trm) =
      let evm,t = denote_term evm trm in
      reduce env evm red t
    in
    k (env,evm, trm)
  | TmMkInductive mind ->
    declare_inductive env evm mind;
    let env = Global.env () in
    k (env, evm, unit_tt)
  | TmUnquote t ->
       (try
         let t = reduce_all env evm t in
         let evm, t' = denote_term evm t in
         let typ = Retyping.get_type_of env evm (EConstr.of_constr t') in
         let evm, typ = Evarsolve.refresh_universes (Some false) env evm typ in
         let make_typed_term typ term evm =
           match texistT_typed_term with
           | ConstructRef ctor ->
              let (evm,c) = Evarutil.new_global evm texistT_typed_term in
              let term = Constr.mkApp
               (EConstr.to_constr evm c, [|typ; t'|]) in
             let evm, _ = Typing.type_of env evm (EConstr.of_constr term) in
               (env, evm, term)
           | _ -> anomaly (str "texistT_typed_term does not refer to a constructor")
         in
           k (make_typed_term (EConstr.to_constr evm typ) t' evm)
        with Reduction.NotArity -> CErrors.user_err (str "unquoting ill-typed term"))
  | TmUnquoteTyped (typ, t) ->
       let t = reduce_all env evm t in
       let evm, t' = denote_term evm t in
       let evdref = ref evm in
       (* let t' = Typing.e_solve_evars env evdref (EConstr.of_constr t') in *)
       Typing.e_check env evdref (EConstr.of_constr t') (EConstr.of_constr typ);
       let evm = !evdref in
       k (env, evm, t')
  | TmFreshName name ->
    let name' = Namegen.next_ident_away_from (unquote_ident name) (fun id -> Nametab.exists_cci (Lib.make_path id)) in
    k (env, evm, quote_ident name')
  | TmExistingInstance name ->
     Classes.existing_instance true (CAst.make (Libnames.Qualid (Libnames.qualid_of_ident (unquote_ident name)))) None;
     k (env, evm, unit_tt)
  | TmInferInstance (s, typ) ->
    begin
      let evm, typ = (match denote_option s with Some s -> let red = unquote_reduction_strategy env evm s in reduce env evm red typ | None -> evm, typ) in
      try
        let (evm,t) = Typeclasses.resolve_one_typeclass env evm (EConstr.of_constr typ) in
        k (env, evm, Constr.mkApp (cSome, [| typ; EConstr.to_constr evm t|]))
      with
        Not_found -> k (env, evm, Constr.mkApp (cNone, [|typ|]))
    end
  | TmInferInstanceTerm typ ->
    begin
      let evm,typ = denote_term evm (reduce_all env evm typ) in
      try
        let (evm,t) = Typeclasses.resolve_one_typeclass env evm (EConstr.of_constr typ) in
        let quoted = TermReify.quote_term env (EConstr.to_constr evm t) in
        k (env, evm, Constr.mkApp (cSome, [| tTerm; quoted |]))
      with
        Not_found -> k (env, evm, Constr.mkApp (cNone, [| tTerm|]))
     end
  | TmPrintTerm trm ->
    begin
      try
       let t = reduce_all env evm trm in
       let evdref = ref evm in
       let evm',t' = denote_term evm t in
       Feedback.msg_info (pr_constr t');
       k (env, evm, unit_tt)
      with
      Reduction.NotArity -> CErrors.user_err (str "printing ill-typed term")
    end
