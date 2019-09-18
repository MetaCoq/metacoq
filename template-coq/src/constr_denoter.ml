open Pp
open Names
open Univ
open Tm_util
open Quoted
open Denote
open Constr_quoted



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


module CoqLiveDenoter =
struct
  include ConstrQuoted

  let unquote_sigt trm =
    let (h,args) = app_full trm [] in
    if constr_equall h texistT then
      match args with
        _ :: _ :: x :: y :: [] -> (x, y)
      | _ -> bad_term_verb trm "unquote_sigt"
    else
      not_supported_verb trm "unquote_sigt"

  let unquote_pair trm =
    let (h,args) = app_full trm [] in
    if constr_equall h c_pair then
      match args with
        _ :: _ :: x :: y :: [] -> (x, y)
      | _ -> bad_term_verb trm "unquote_pair"
    else
      not_supported_verb trm "unquote_pair"

  let rec unquote_list trm =
    let (h,args) = app_full trm [] in
    if constr_equall h c_nil then
      []
    else if constr_equall h c_cons then
      match args with
        _ :: x :: xs :: [] -> x :: unquote_list xs
      | _ -> bad_term_verb trm "unquote_list"
    else
      not_supported_verb trm "unquote_list"

  let rec unquote_non_empty_list trm =
    let (h,args) = app_full trm [] in
    if constr_equall h nel_sing then
      match args with
        _ :: x :: [] -> [x]
      | _ -> bad_term_verb trm "unquote_non_empty_list"
    else if constr_equall h nel_cons then
      match args with
        _ :: x :: xs :: [] -> x :: unquote_non_empty_list xs
      | _ -> bad_term_verb trm "unquote_non_empty_list"
    else
      not_supported_verb trm "unquote_non_empty_list"

  (* Unquote Coq nat to OCaml int *)
  let rec unquote_nat trm =
    let (h,args) = app_full trm [] in
    if constr_equall h tO then
      0
    else if constr_equall h tS then
      match args with
        n :: [] -> 1 + unquote_nat n
      | _ -> bad_term_verb trm "unquote_nat"
    else
      not_supported_verb trm "unquote_nat"

  let unquote_bool trm =
    if constr_equall trm ttrue then
      true
    else if constr_equall trm tfalse then
      false
    else not_supported_verb trm "from_bool"

  let unquote_char trm =
    let (h,args) = app_full trm [] in
    if constr_equall h tAscii then
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
      if constr_equall h tEmptyString then
        Bytes.create n
      else if constr_equall h tString then
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
    Names.Id.of_string (unquote_string trm)

  let unquote_cast_kind trm =
    if constr_equall trm kVmCast then
      Constr.VMcast
    else if constr_equall trm kCast then
      Constr.DEFAULTcast
    else if constr_equall trm kRevertCast then
      Constr.REVERTcast
    else if constr_equall trm kNative then
      Constr.VMcast
    else
      not_supported_verb trm "unquote_cast_kind"

  let unquote_name trm =
    let (h,args) = app_full trm [] in
    if constr_equall h nAnon then
      Names.Anonymous
    else if constr_equall h nNamed then
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
    if constr_equall h lProp then
      match args with
      | [] -> evm, Univ.Level.prop
      | _ -> bad_term_verb trm "unquote_level"
    else if constr_equall h lSet then
      match args with
      | [] -> evm, Univ.Level.set
      | _ -> bad_term_verb trm "unquote_level"
    else if constr_equall h tLevel then
      match args with
      | s :: [] -> debug (fun () -> str "Unquoting level " ++ pr_constr trm);
        get_level evm (unquote_string s)
      | _ -> bad_term_verb trm "unquote_level"
    else if constr_equall h tLevelVar then
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
    if constr_equall trm lfresh_universe then
      if !strict_unquote_universe_mode then
        CErrors.user_err ~hdr:"unquote_universe" (str "It is not possible to unquote a fresh universe in Strict Unquote Universe Mode.")
      else
        let evm, u = Evd.new_univ_variable (Evd.UnivFlexible false) evm in
        Feedback.msg_info (str"Fresh universe " ++ Universe.pr u ++ str" was added to the context.");
        evm, u
    else
      let levels = List.map unquote_pair (unquote_non_empty_list trm) in
      match levels with
      | [] -> assert false
      | (l,b)::q -> List.fold_left (fun (evm,u) (l,b) -> let evm, u' = unquote_level_expr evm l b
                                     in evm, Univ.Universe.sup u u')
                      (unquote_level_expr evm l b) q

  let unquote_universe_instance evm trm (* of type universe_instance *) =
    let l = unquote_list trm in
    let evm, l = map_evm unquote_level evm l in
    evm, Univ.Instance.of_array (Array.of_list l)


  let unquote_kn (k : quoted_kernel_name) : Libnames.qualid =
    Libnames.qualid_of_string (Quoted.clean_name (unquote_string k))

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
    if constr_equall h tmkInd then
      match args with
        nm :: num :: _ ->
        let s = unquote_string nm in
        let (dp, nm) = Quoted.split_name s in
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


  let unquote_int=unquote_nat
  let print_term=Printer.pr_constr_env (Global.env ()) Evd.empty

  let inspect_term (t:Constr.t)
  : (Constr.t, quoted_int, quoted_ident, quoted_name, quoted_sort, quoted_cast_kind, quoted_kernel_name, quoted_inductive, quoted_univ_instance, quoted_proj) structure_of_term =
    let (h,args) = app_full t [] in
    if constr_equall h tRel then
      match args with
        x :: _ -> ACoq_tRel x
      | _ -> CErrors.user_err (print_term t ++ Pp.str ("has bad structure"))
    else if constr_equall h tVar then
      match args with
        x :: _ -> ACoq_tVar x
      | _ -> CErrors.user_err (print_term t ++ Pp.str ("has bad structure"))
    else if constr_equall h tSort then
      match args with
        x :: _ -> ACoq_tSort x
      | _ -> CErrors.user_err (print_term t ++ Pp.str ("has bad structure"))
    else if constr_equall h tCast then
      match args with
        x :: y :: z :: _ -> ACoq_tCast (x, y, z)
      | _ -> CErrors.user_err (print_term t ++ Pp.str ("has bad structure"))
    else if constr_equall h tProd then
      match args with
        n :: t :: b :: _ -> ACoq_tProd (n,t,b)
      | _ -> CErrors.user_err (print_term t ++ Pp.str ("has bad structure"))
    else if constr_equall h tLambda then
      match args with
        n  :: t :: b :: _ -> ACoq_tLambda (n,t,b)
      | _ -> CErrors.user_err (print_term t ++ Pp.str ("has bad structure"))
    else if constr_equall h tLetIn then
      match args with
        n :: e :: t :: b :: _ -> ACoq_tLetIn (n,e,t,b)
      | _ -> CErrors.user_err (print_term t ++ Pp.str ("has bad structure"))
    else if constr_equall h tApp then
      match args with
        f::xs::_ -> ACoq_tApp (f, unquote_list xs)
      | _ -> CErrors.user_err (print_term t ++ Pp.str ("has bad structure"))
    else if constr_equall h tConst then
      match args with
        s::u::_ -> ACoq_tConst (s, u)
      | _ -> CErrors.user_err (print_term t ++ Pp.str ("has bad structure"))
    else if constr_equall h tInd then
      match args with
        i::u::_ -> ACoq_tInd (i,u)
      | _ -> CErrors.user_err (print_term t ++ Pp.str ("has bad structure"))
    else if constr_equall h tConstructor then
      match args with
        i::idx::u::_ -> ACoq_tConstruct (i,idx,u)
      | _ -> CErrors.user_err (print_term t ++ Pp.str ("has bad structure: constructor case"))
    else if constr_equall h tCase then
      match args with
        info::ty::d::brs::_ -> ACoq_tCase (unquote_pair info, ty, d, List.map unquote_pair (unquote_list brs))
      | _ -> CErrors.user_err (print_term t ++ Pp.str ("has bad structure"))
    else if constr_equall h tFix then
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
    else if constr_equall h tCoFix then
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
    else if constr_equall h tProj then
      match args with
        proj::t::_ -> ACoq_tProj (proj, t)
      | _ -> CErrors.user_err (print_term t ++ Pp.str ("has bad structure"))

    else
      CErrors.user_err (str"inspect_term: cannot recognize " ++ print_term t ++ str" (maybe you forgot to reduce it?)")

end



module CoqLiveDenote = Denote(CoqLiveDenoter)

let denote_term=CoqLiveDenote.denote_term
