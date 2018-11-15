open CErrors
open Univ
open Entries
open Names
open Namegen
open Redops
open Genredexpr
open Obligations
open Pp (* this adds the ++ to the current scope *)

open Quoter
open Constr_quoter
open TemplateCoqQuoter

let rec app_full trm acc =
  match Constr.kind trm with
    Constr.App (f, xs) -> app_full f (Array.to_list xs @ acc)
  | _ -> (trm, acc)

let print_term (u: t) : Pp.t = pr_constr u

let from_coq_pair trm =
  let (h,args) = app_full trm [] in
  if Constr.equal h c_pair then
    match args with
      _ :: _ :: x :: y :: [] -> (x, y)
    | _ -> bad_term trm
  else
    not_supported_verb trm "from_coq_pair"


let rec from_coq_list trm =
  let (h,args) = app_full trm [] in
  if Constr.equal h c_nil then []
  else if Constr.equal h c_cons then
    match args with
      _ :: x :: xs :: _ -> x :: from_coq_list xs
    | _ -> bad_term trm
  else
    not_supported_verb trm "from_coq_list"

let unquote_map_option f trm =
  let (h,args) = app_full trm [] in
  if Constr.equal h cSome then
    match args with
      _ :: x :: _ -> Some (f x)
    | _ -> bad_term trm
  else if Constr.equal h cNone then
    match args with
      _ :: [] -> None
    | _ -> bad_term trm
  else
    not_supported_verb trm "unqote_map_option"

let unquote_option = unquote_map_option (fun x -> x) 

let inspectTerm (t:Constr.t) :  (Constr.t, quoted_int, quoted_ident, quoted_aname, quoted_sort, quoted_cast_kind, quoted_kernel_name, quoted_inductive, quoted_univ_instance, quoted_proj) structure_of_term =
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
      f::xs::_ -> ACoq_tApp (f, from_coq_list xs)
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
      info::ty::is::d::brs::_ -> ACoq_tCase (from_coq_pair info, ty, unquote_option is, d, List.map from_coq_pair (from_coq_list brs))
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
      let lbd = List.map unquoteFbd (from_coq_list bds) in
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
      let lbd = List.map unquoteFbd (from_coq_list bds) in
      ACoq_tCoFix (lbd, i)
    | _ -> CErrors.user_err (print_term t ++ Pp.str ("has bad structure"))
  else if Constr.equal h tProj then
    match args with
      proj::t::_ -> ACoq_tProj (proj, t)
    | _ -> CErrors.user_err (print_term t ++ Pp.str ("has bad structure"))

  else
    CErrors.user_err (str"inspect_term: cannot recognize " ++ print_term t)

let rec unquote_int trm =
  let (h,args) = app_full trm [] in
  if Constr.equal h tO then
    0
  else if Constr.equal h tS then
    match args with
      n :: _ -> 1 + unquote_int n
    | _ -> not_supported_verb trm "unquote_int nil"
  else
    not_supported_verb trm "unquote_int"

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
      a :: b :: c :: d :: e :: f :: g :: h :: _ ->
      let bits = List.rev [a;b;c;d;e;f;g;h] in
      let v = List.fold_left (fun a n -> (a lsl 1) lor if unquote_bool n then 1 else 0) 0 bits in
      char_of_int v
    | _ -> assert false
  else
    not_supported trm

let unquote_string trm =
  let rec go n trm =
    let (h,args) = app_full trm [] in
    if Constr.equal h tEmptyString then
      Bytes.create n
    else if Constr.equal h tString then
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
    bad_term trm

let unquote_relevance trm =
      if Constr.equal trm tRelevant then
        Sorts.Relevant
      else if Constr.equal trm tIrrelevant then
        Sorts.Irrelevant
      else raise (Failure "Invalid relevance")

let unquote_name trm =
  let (h,args) = app_full trm [] in
  if Constr.equal h nAnon then Names.Anonymous
  else if Constr.equal h nNamed then
    match args with
      n :: _ -> Names.Name (unquote_ident n)
    | _ -> raise (Failure "ill-typed, expected name")
  else
    raise (Failure "non-value")


let unquote_aname trm =
  let (h,args) = app_full trm [] in
  if Constr.equal h tmkBindAnn then
    match args with
      _ :: nm :: relevance :: _ -> { Context.binder_name = unquote_name nm; Context.binder_relevance = unquote_relevance relevance }
    | _ -> raise (Failure "ill-typed, expected annotated name")
  else
    raise (Failure "non-value")


  (* FIXME CHANGES: This code was taken from (old version of) Pretyping, because it is not exposed globally *)
  (* the case for strict universe declarations was removed *)

 (* It seems that the way to work with global universe declarations has changed.
    See: https://github.com/coq/coq/commit/20c98eab851210702b39e1c66e005acfc351d8dd
    Also, instead of strings, new level manupulation functions
    use [qualid]. Maybe it's worth considering to make corresponding changes to template-coq representations as well.
  *)

let get_level evd s =
  if CString.string_contains ~where:s ~what:"." then
    match List.rev (CString.split_on_char '.' s) with
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
      let level = Evd.universe_of_name evd (Id.of_string s) in
      evd, level
    with Not_found ->
      user_err  ~hdr:"interp_universe_level_name"
                (Pp.(str "Undeclared universe: " ++ Id.print (Id.of_string s)))
(* end of code from Pretyping *)



let unquote_level evd trm (* of type level *) : Evd.evar_map * Univ.Level.t =
  let (h,args) = app_full trm [] in
  if Constr.equal h lProp then
    match args with
    | [] -> evd, Univ.Level.prop
    | _ -> bad_term_verb trm "unquote_level"
  else if Constr.equal h lSet then
    match args with
    | [] -> evd, Univ.Level.set
    | _ -> bad_term_verb trm "unquote_level"
  else if Constr.equal h tLevel then
    match args with
    | s :: [] -> get_level evd (unquote_string s)
    | _ -> bad_term_verb trm "unquote_level"
  else if Constr.equal h tLevelVar then
    match args with
    | l :: [] -> evd, Univ.Level.var (unquote_int l)
    | _ -> bad_term_verb trm "unquote_level"
  else
    not_supported_verb trm "unquote_level"

let unquote_level_expr evd trm (* of type level *) b (* of type bool *) : Evd.evar_map * Univ.Universe.t=
  let evd, l = unquote_level evd trm in
  let u = Univ.Universe.make l in
  if unquote_bool b then evd, Univ.Universe.super u
  else evd, u

let unquote_universe evd trm (* of type universe *) =
  let levels = List.map from_coq_pair (from_coq_list trm) in
  let evd, u = match levels with
    | [] -> Evd.new_univ_variable (Evd.UnivFlexible false) evd
    | (l,b)::q -> List.fold_left (fun (evd,u) (l,b) -> let evd, u' = unquote_level_expr evd l b
                                                       in evd, Univ.Universe.sup u u')
                                 (unquote_level_expr evd l b) q
  in evd, u

let unquote_kn (k : quoted_kernel_name) : Libnames.qualid =
  Libnames.qualid_of_string (clean_name (unquote_string k))

let unquote_proj (qp : quoted_proj) : (quoted_inductive * quoted_int * quoted_int) =
  let (h,args) = app_full qp [] in
  match args with
  | tyin::tynat::indpars::idx::[] ->
     let (h',args') = app_full indpars [] in
     (match args' with
      | tyind :: tynat :: ind :: n :: [] -> (ind, n, idx)
      | _ -> bad_term_verb qp "not a projection")
  | _ -> bad_term_verb qp "not a projection"

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
         | Globnames.IndRef i -> (fst i, unquote_int  num)
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


let denote_term evdref (trm: Constr.t) : Constr.t =
  let rec aux (trm: Constr.t) : Constr.t =
    (*debug (fun () -> Pp.(str "denote_term" ++ spc () ++ pr_constr trm)) ; *)
    match (inspectTerm trm) with
    | ACoq_tRel x -> Constr.mkRel (unquote_int x + 1)
    | ACoq_tVar x -> Constr.mkVar (unquote_ident x)
    | ACoq_tSort x ->
       let evd, u = unquote_universe !evdref x in evdref := evd; Constr.mkType u
    | ACoq_tCast (t,c,ty) -> Constr.mkCast (aux t, unquote_cast_kind c, aux ty)
    | ACoq_tProd (n,t,b) -> Constr.mkProd (unquote_aname n, aux t, aux b)
    | ACoq_tLambda (n,t,b) -> Constr.mkLambda (unquote_aname n, aux t, aux b)
    | ACoq_tLetIn (n,e,t,b) -> Constr.mkLetIn (unquote_aname n, aux e, aux t, aux b)
    | ACoq_tApp (f,xs) ->
       Constr.mkApp (aux f, Array.of_list (List.map aux  xs))
    | ACoq_tConst (s,_) ->
       (* TODO: unquote universes *)
       let s = (unquote_kn s) in
       (try
          match Nametab.locate s with
          | Globnames.ConstRef c -> UnivGen.constr_of_global (Globnames.ConstRef c)
          | Globnames.IndRef _ -> CErrors.user_err (str "the constant is an inductive. use tInd : "
                                                    ++  Pp.str (Libnames.string_of_qualid s))
          | Globnames.VarRef _ -> CErrors.user_err (str "the constant is a variable. use tVar : " ++ Pp.str (Libnames.string_of_qualid s))
          | Globnames.ConstructRef _ -> CErrors.user_err (str "the constant is a consructor. use tConstructor : "++ Pp.str (Libnames.string_of_qualid s))
        with
          Not_found -> CErrors.user_err (str "Constant not found : " ++ Pp.str (Libnames.string_of_qualid s)))
    | ACoq_tConstruct (i,idx,_) ->
       let ind = unquote_inductive i in
       Constr.mkConstruct (ind, unquote_int idx + 1)
    | ACoq_tInd (i, _) ->
       let i = unquote_inductive i in
       Constr.mkInd i
    | ACoq_tCase (info, ty, is, d, brs) ->
       let i, _ = info in
       let ind = unquote_inductive i in
       let relevance = Inductive.relevance_of_inductive (Global.env ()) ind in
       let ci = Inductiveops.make_case_info (Global.env ()) ind relevance Constr.RegularStyle in
       let denote_branch br =
         let _, br = br in
         aux br
       in
       Constr.mkCase (ci, aux ty, Option.map aux is, aux d, Array.of_list (List.map denote_branch (brs)))
    | ACoq_tFix (lbd, i) ->
       let (names,types,bodies,rargs) = (List.map (fun p->p.adname) lbd,  List.map (fun p->p.adtype) lbd, List.map (fun p->p.adbody) lbd,
                                         List.map (fun p->p.rarg) lbd) in
       let (types,bodies) = (List.map aux types, List.map aux bodies) in
       let (names,rargs) = (List.map unquote_aname names, List.map unquote_int rargs) in
       let la = Array.of_list in
       Constr.mkFix ((la rargs,unquote_int i), (la names, la types, la bodies))
    | ACoq_tCoFix (lbd, i) ->
       let (names,types,bodies,rargs) = (List.map (fun p->p.adname) lbd,  List.map (fun p->p.adtype) lbd, List.map (fun p->p.adbody) lbd,
                                         List.map (fun p->p.rarg) lbd) in
       let (types,bodies) = (List.map aux types, List.map aux bodies) in
       let (names,rargs) = (List.map unquote_aname names, List.map unquote_int rargs) in
       let la = Array.of_list in
       Constr.mkCoFix (unquote_int i, (la names, la types, la bodies))
    | ACoq_tProj (proj,t) ->
       let (ind, n, narg) = unquote_proj proj in (* is narg the correct projection? *)
       let ind' = unquote_inductive ind in
       let narg = unquote_int narg in
       let projs = Environ.get_projections (Global.env ()) ind' in
       (match projs with
        | Some projs -> Constr.mkProj (Names.Projection.make projs.(narg) false, aux t)
        | None -> bad_term trm)
    | _ ->  not_supported_verb trm "big_case"
  in aux trm

let denote_reduction_strategy env evm (trm : quoted_reduction_strategy) : Redexpr.red_expr =
  let trm = Reduction.whd_all env trm in
  let (trm, args) = app_full trm [] in
  (* from g_tactic.ml4 *)
  let default_flags = Redops.make_red_flag [FBeta;FMatch;FFix;FCofix;FZeta;FDeltaBut []] in
  if Constr.equal trm tcbv then Cbv default_flags
  else if Constr.equal trm tcbn then Cbn default_flags
  else if Constr.equal trm thnf then Hnf
  else if Constr.equal trm tall then Cbv all_flags
  else if Constr.equal trm tlazy then Lazy all_flags
  else if Constr.equal trm tunfold then
    (match args with name (* to unfold *) :: _ ->
    let name = reduce_all env evm name in
    let name = unquote_ident name in
      (try Unfold [Locus.AllOccurrences, Tacred.evaluable_of_global_reference env
        (Nametab.global (Libnames.qualid_of_ident name))]
       with
         _ -> CErrors.user_err (str "Constant not found or not a constant: " ++ Pp.str (Names.Id.to_string name)))
  | _ -> raise  (Failure "ill-typed reduction strategy"))
  else not_supported_verb trm "denote_reduction_strategy"



let denote_local_entry evdref trm =
  let (h,args) = app_full trm [] in
  match args with
    x :: [] ->
    if Constr.equal h tLocalDef then Entries.LocalDefEntry (denote_term evdref x)
    else (if  Constr.equal h tLocalAssum then Entries.LocalAssumEntry (denote_term evdref x) else bad_term trm)
  | _ -> bad_term trm

let denote_mind_entry_finite trm =
  let (h,args) = app_full trm [] in
  match args with
    [] ->
    if Constr.equal h cFinite then Declarations.Finite
    else if  Constr.equal h cCoFinite then Declarations.CoFinite
    else if  Constr.equal h cBiFinite then Declarations.BiFinite
    else bad_term trm
  | _ -> bad_term trm

let unquote_map_option f trm =
  let (h,args) = app_full trm [] in
  if Constr.equal h cSome then
    match args with
      _ :: x :: _ -> Some (f x)
    | _ -> bad_term trm
  else if Constr.equal h cNone then
    match args with
      _ :: [] -> None
    | _ -> bad_term trm
  else
    not_supported_verb trm "unqote_map_option"

let denote_ucontext (trm : Constr.t) : UContext.t =
  Univ.UContext.empty (* FIXME *)

let denote_universe_context (trm : Constr.t) : bool * UContext.t =
  let (h, args) = app_full trm [] in
  let b =
    if Constr.equal h cMonomorphic_ctx then Some false
    else if Constr.equal h cPolymorphic_ctx then Some true
    else None
  in
  match b, args with
  | Some poly, ctx :: [] ->
     poly, denote_ucontext ctx
  | _, _ -> bad_term trm

let denote_mind_entry_universes trm =
  match denote_universe_context trm with
  | false, ctx -> Monomorphic_ind_entry (Univ.ContextSet.of_context ctx)
  | true, ctx -> Polymorphic_ind_entry ctx

(* let denote_inductive_first trm =
 *   let (h,args) = app_full trm [] in
 *   if Constr.equal h tmkInd then
 *     match args with
 *       nm :: num :: _ ->
 *       let s = (unquote_string nm) in
 *       let (dp, nm) = split_name s in
 *       (try
 *         match Nametab.locate (Libnames.make_qualid dp nm) with
 *         | Globnames.ConstRef c ->  CErrors.user_err (str "this not an inductive constant. use tConst instead of tInd : " ++ str s)
 *         | Globnames.IndRef i -> (fst i, unquote_int  num)
 *         | Globnames.VarRef _ -> CErrors.user_err (str "the constant is a variable. use tVar : " ++ str s)
 *         | Globnames.ConstructRef _ -> CErrors.user_err (str "the constant is a consructor. use tConstructor : " ++ str s)
 *       with
 *       Not_found ->   CErrors.user_err (str "Constant not found : " ++ str s))
 *     | _ -> assert false
 *   else
 *     bad_term_verb trm "non-constructor" *)

let declare_inductive (env: Environ.env) (evm: Evd.evar_map) (body: Constr.t) : unit =
  let body = reduce_all env evm body in
  let (_,args) = app_full body [] in (* check that the first component is Build_mut_ind .. *)
  let evdref = ref evm in
  let one_ind b1 : Entries.one_inductive_entry =
    let (_,args) = app_full b1 [] in (* check that the first component is Build_one_ind .. *)
    match args with
    | mt::ma::mtemp::mcn::mct::[] ->
       {
         mind_entry_typename = unquote_ident mt;
         mind_entry_arity = denote_term evdref ma;
         mind_entry_template = unquote_bool mtemp;
         mind_entry_consnames = List.map unquote_ident (from_coq_list mcn);
         mind_entry_lc = List.map (denote_term evdref) (from_coq_list mct)
       }
    | _ -> raise (Failure "ill-typed one_inductive_entry")
  in
  let mut_ind mr mf mp mi uctx mpr : Entries.mutual_inductive_entry =
    {
      mind_entry_record = unquote_map_option (unquote_map_option (fun x -> Array.of_list (List.map unquote_ident (from_coq_list x)))) mr;
      mind_entry_finite = denote_mind_entry_finite mf; (* inductive *)
      mind_entry_params = List.map (fun p -> let (l,r) = (from_coq_pair p) in (unquote_ident l, (denote_local_entry evdref r)))
                                   (List.rev (from_coq_list mp));
      mind_entry_inds = List.map one_ind (from_coq_list mi);
      mind_entry_universes = denote_mind_entry_universes uctx;
      mind_entry_private = unquote_map_option unquote_bool mpr (*mpr*)
    } in
  match args with
    mr::mf::mp::mi::univs::mpr::[] ->
    ignore(ComInductive.declare_mutual_inductive_with_eliminations (mut_ind mr mf mp mi univs mpr) Names.Id.Map.empty [])
  | _ -> raise (Failure "ill-typed mutual_inductive_entry")


let monad_failure s k =
  CErrors.user_err  (str (s ^ " must take " ^ (string_of_int k) ^ " argument" ^ (if k > 0 then "s" else "") ^ ".")
                     ++ str "Please file a bug with Template-Coq.")
let not_in_tactic s =
  CErrors.user_err  (str ("You can not use " ^ s ^ " in a tactic."))

let monad_failure_full s k prg =
  CErrors.user_err
    (str (s ^ " must take " ^ (string_of_int k) ^ " argument" ^ (if k > 0 then "s" else "") ^ ".") ++
       str "While trying to run: " ++ fnl () ++ print_term prg ++ fnl () ++
       str "Please file a bug with Template-Coq.")

let rec run_template_program_rec ?(intactic=false) (k : Evd.evar_map * Constr.t -> unit)  ((evm, pgm) : Evd.evar_map * Constr.t) : unit =
  let env = Global.env () in
  let pgm = Reduction.whd_all env pgm in
  let (coConstr, args) = app_full pgm [] in
  let (glob_ref, universes) =
    try
      let open Constr in
      let open GlobRef in
      match kind coConstr with
      | Const (c, u) -> GlobRef.ConstRef c, u
      | Ind (i, u) -> GlobRef.IndRef i, u
      | Construct (c, u) -> GlobRef.ConstructRef c, u
      | Var id -> GlobRef.VarRef id, Instance.empty
      | _ -> raise Not_found
    with _ ->
      CErrors.user_err (str "Invalid argument or not yet implemented. The argument must be a TemplateProgram: " ++ pr_constr coConstr)
  in
  if GlobRef.equal glob_ref tmReturn then
    match args with
    | _::h::[] -> k (evm, h)
    | _ -> monad_failure "tmReturn" 2
  else if GlobRef.equal glob_ref tmBind then
    match args with
    | _::_::a::f::[] ->
       run_template_program_rec ~intactic:intactic (fun (evm, ar) -> run_template_program_rec k (evm, Constr.mkApp (f, [|ar|]))) (evm, a)
    | _ -> monad_failure_full "tmBind" 4 pgm
  else if GlobRef.equal glob_ref tmDefinition then
    if intactic then not_in_tactic "tmDefinition" else
    match args with
    | name::typ::body::[] ->
       let name = reduce_all env evm name in
       let univs =
         if Flags.is_universe_polymorphism () then Polymorphic_const_entry (Evd.to_universe_context evm)
         else Monomorphic_const_entry (Evd.universe_context_set evm) in
       let n = Declare.declare_definition ~kind:Decl_kinds.Definition (unquote_ident name) ~types:typ (body, univs) in
       k (evm, Constr.mkConst n)
    | _ -> monad_failure "tmDefinition" 3
  else if GlobRef.equal glob_ref tmAxiom then
    if intactic then not_in_tactic "tmAxiom" else
    match args with
    | name::typ::[] ->
       let name = reduce_all env evm name in
       let param = Entries.ParameterEntry (None, (typ, Monomorphic_const_entry (Evd.universe_context_set evm)), None) in
       let n = Declare.declare_constant (unquote_ident name) (param, Decl_kinds.IsDefinition Decl_kinds.Definition) in
       k (evm, Constr.mkConst n)
    | _ -> monad_failure "tmAxiom" 2
  else if GlobRef.equal glob_ref tmLemma then
    if intactic then not_in_tactic "tmLemma" else
    match args with
    | name::typ::[] ->
       let name = reduce_all env evm name in
       let poly = Flags.is_universe_polymorphism () in
       let kind = (Decl_kinds.Global, poly, Decl_kinds.Definition) in
       let hole = CAst.make (Constrexpr.CHole (None, Namegen.IntroAnonymous, None)) in
       let evm, (c, _) = Constrintern.interp_casted_constr_evars_impls env evm hole (EConstr.of_constr typ) in
       let ident = unquote_ident name in
       Obligations.check_evars env evm;
       (* SPROP: [Evd.fresh_global] now returns [evar_map * EContsr.t] and we have to convert [t] (see [g_template_coq.ml4 for more comments]) *)
       let obls, _, c, cty = Obligations.eterm_obligations env ident evm 0
                               (EConstr.to_constr ~abort_on_undefined_evars:false evm c) typ in
       let ctx = Evd.evar_universe_context evm in
       let hook = Obligations.mk_univ_hook (fun _ _ gr ->
                      let env = Global.env () in
                      let evm = Evd.from_env env in
                      let evm, t = Evd.fresh_global env evm gr in
       (* SPROP: [Evd.fresh_global] now returns [evar_map * EContsr.t] and we have to convert [t] (see [g_template_coq.ml4 for more comments]) *)
                      k (evm, (EConstr.to_constr ~abort_on_undefined_evars:false evm t))) in
       ignore (Obligations.add_definition ident ~term:c cty ctx ~kind ~hook obls)
    | _ -> monad_failure "tmLemma" 2
  else if GlobRef.equal glob_ref tmMkDefinition then
    if intactic then not_in_tactic "tmExistingInstance" else
    match args with
    | name::body::[] ->
       let name = reduce_all env evm name in
       let evdref = ref evm in
       let trm = denote_term evdref body in
       let (evm, _) = Typing.type_of env !evdref (EConstr.of_constr trm) in
       let _ = Declare.declare_definition ~kind:Decl_kinds.Definition (unquote_ident name) (trm, Monomorphic_const_entry (Evd.universe_context_set evm)) in
       k (evm, unit_tt)
    | _ -> monad_failure "tmMkDefinition" 2
  else if GlobRef.equal glob_ref tmQuote then
    match args with
    | _::trm::[] -> let qt = TermReify.quote_term env trm (* user should do the reduction (using tmEval) if they want *)
                    in k (evm, qt)
    | _ -> monad_failure "tmQuote" 2
  else if GlobRef.equal glob_ref tmQuoteRec then
    match args with
    | _::trm::[] -> let qt = TermReify.quote_term_rec env trm in
                    k (evm, qt)
    | _ -> monad_failure "tmQuoteRec" 2
  else if GlobRef.equal glob_ref tmQuoteInductive then
    match args with
    | name::[] ->
       let name = reduce_all env evm name in
       let name = unquote_string name in
       let (dp, nm) = split_name name in
       (match Nametab.locate (Libnames.make_qualid dp nm) with
        | Globnames.IndRef ni ->
           let t = TermReify.quote_mind_decl env (fst ni) in
           let _, args = Constr.destApp t in
           (match args with
            | [|kn; decl|] ->
               k (evm, decl)
            | _ -> bad_term_verb t "anomaly in quoting of inductive types")
        (* quote_mut_ind produce an entry rather than a decl *)
        (* let c = Environ.lookup_mind (fst ni) env in (\* FIX: For efficienctly, we should also export (snd ni)*\) *)
        (* TermReify.quote_mut_ind env c *)
        | _ -> CErrors.user_err (str name ++ str " does not seem to be an inductive."))
    (* k (evm, entry) *)
    | _ -> monad_failure "tmQuoteInductive" 1
  else if GlobRef.equal glob_ref tmQuoteConstant then
    match args with
    | name::bypass::[] ->
       let name = reduce_all env evm name in
       let name = unquote_string name in
       let bypass = reduce_all env evm bypass in
       let bypass = unquote_bool bypass in
       let entry = TermReify.quote_entry_aux bypass env evm name in
       let entry =
         match entry with
         | Some (Left cstentry) -> TemplateCoqQuoter.quote_constant_entry cstentry
         | Some (Right _) -> CErrors.user_err (str name ++ str " refers to an inductive")
         | None -> bad_term_verb coConstr "anomaly in QuoteConstant"
       in
       k (evm, entry)
    | _ -> monad_failure "tmQuoteConstant" 2
  else if GlobRef.equal glob_ref tmQuoteUniverses then
    match args with
    | _::[] -> let univs = Environ.universes env in
               k (evm, quote_ugraph univs)
    | _ -> monad_failure "tmQuoteUniverses" 1
  else if GlobRef.equal glob_ref tmPrint then
    match args with
    | _::trm::[] -> Feedback.msg_info (pr_constr trm);
                    k (evm, unit_tt)
    | _ -> monad_failure "tmPrint" 2
  else if GlobRef.equal glob_ref tmFail then
    match args with
    | _::trm::[] -> CErrors.user_err (str (unquote_string trm))
    | _ -> monad_failure "tmFail" 2
  else if GlobRef.equal glob_ref tmAbout then
    match args with
    | id::[] -> let id = unquote_string id in
                (try
                   let gr = Smartlocate.locate_global_with_alias (Libnames.qualid_of_string id) in
                   let opt = Constr.mkApp (cSome , [|tglobal_reference ; quote_global_reference gr|]) in
                   k (evm, opt)
                 with
                 | Not_found -> k (evm, Constr.mkApp (cNone, [|tglobal_reference|])))
    | _ -> monad_failure "tmAbout" 1
  else if GlobRef.equal glob_ref tmCurrentModPath then
    match args with
    | _::[] -> let mp = Lib.current_mp () in
               (* let dp' = Lib.cwd () in (* different on sections ? *) *)
               let s = quote_string (Names.ModPath.to_string mp) in
               k (evm, s)
    | _ -> monad_failure "tmCurrentModPath" 1
  else if GlobRef.equal glob_ref tmEval then
    match args with
    | s(*reduction strategy*)::_(*type*)::trm::[] ->
       let red = denote_reduction_strategy env evm s in
       let (evm, trm) = reduce env evm red trm
       in k (evm, trm)
    | _ -> monad_failure "tmEval" 3
  else if GlobRef.equal glob_ref tmMkInductive then
    match args with
    | mind::[] -> declare_inductive env evm mind;
                  k (evm, unit_tt)
    | _ -> monad_failure "tmMkInductive" 1
  else if GlobRef.equal glob_ref tmUnquote then
    match args with
    | t::[] ->
       (try
         let t = reduce_all env evm t in
         let evdref = ref evm in
         let t' = denote_term evdref t in
         let evm = !evdref in
         let typ = Retyping.get_type_of env evm (EConstr.of_constr t') in
         let evm, typ = Evarsolve.refresh_universes (Some false) env evm typ in
         let make_typed_term typ term evm =
           match texistT_typed_term with
           | GlobRef.ConstructRef ctor ->
             let u = (Univ.Instance.to_array universes).(1) in
             let term = Constr.mkApp
               (Constr.mkConstructU (ctor, Univ.Instance.of_array [|u|]), [|typ; t'|]) in
             let evm, _ = Typing.type_of env evm (EConstr.of_constr term) in
               (evm, term)
           | _ -> anomaly (str "texistT_typed_term does not refer to a constructor")
         in
           k (make_typed_term (EConstr.to_constr evm typ) t' evm)
        with Reduction.NotArity -> CErrors.user_err (str "unquoting ill-typed term"))
    | _ -> monad_failure "tmUnquote" 1
  else if GlobRef.equal glob_ref tmUnquoteTyped then
    match args with
    | typ::t::[] ->
       let t = reduce_all env evm t in
       let evdref = ref evm in
       let t' = denote_term evdref t in
       let (evm, t') = Typing.solve_evars env !evdref (EConstr.of_constr t') in
       let evm = Typing.check env evm t' (EConstr.of_constr typ) in
       let t' = EConstr.to_constr evm t' in
       k (evm, t')
    | _ -> monad_failure "tmUnquoteTyped" 2
  else if GlobRef.equal glob_ref tmFreshName then
    match args with
    | name::[] -> let name' = Namegen.next_ident_away_from (unquote_ident name) (fun id -> Nametab.exists_cci (Lib.make_path id)) in
                  k (evm, quote_ident name')
    | _ -> monad_failure "tmFreshName" 1
  else if GlobRef.equal glob_ref tmExistingInstance then
    match args with
    | name :: [] ->
      Classes.existing_instance true (Libnames.qualid_of_ident (unquote_ident name)) None
    | _ -> monad_failure "tmExistingInstance" 1
  else if GlobRef.equal glob_ref tmInferInstance then
    match args with
    | typ :: [] ->
       (try
          let (evm,t) = Typeclasses.resolve_one_typeclass env evm (EConstr.of_constr typ) in
          k (evm, Constr.mkApp (cSome, [| typ; EConstr.to_constr evm t|]))
        with
          Not_found -> k (evm, Constr.mkApp (cNone, [|typ|]))
       )
    | _ -> monad_failure "tmInferInstance" 1
  else CErrors.user_err (str "Invalid argument or not yet implemented. The argument must be a TemplateProgram: " ++ pr_constr coConstr)
