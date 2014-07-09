(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmp" i*)

let contrib_name = "template-coq"

module TermReify = struct
  exception NotSupported of Term.constr

  let not_supported trm =
    raise (NotSupported trm)
  let bad_term trm =
    raise (NotSupported trm)

  let resolve_symbol (path : string list) (tm : string) : Term.constr =
    let re = Coqlib.find_reference contrib_name path tm in
    Libnames.constr_of_global re

  let pkg_bignums = ["Coq";"Numbers";"BinNums"]
  let pkg_datatypes = ["Coq";"Init";"Datatypes"]
  let pkg_reify = ["TemplateCoq";"Ast"]
  let pkg_string = ["Coq";"Strings";"String"]

  let r_reify = resolve_symbol pkg_reify

  let tString = resolve_symbol pkg_string "String"
  let tEmptyString = resolve_symbol pkg_string "EmptyString"
  let tO = resolve_symbol pkg_datatypes "O"
  let tS = resolve_symbol pkg_datatypes "S"
  let ttrue = resolve_symbol pkg_datatypes "true"
  let tfalse = resolve_symbol pkg_datatypes "false"
  let tAscii = resolve_symbol ["Coq";"Strings";"Ascii"] "Ascii"
  let c_nil = resolve_symbol pkg_datatypes "nil"
  let c_cons = resolve_symbol pkg_datatypes "cons"
  let nAnon = r_reify "nAnon"
  let nNamed = r_reify "nNamed"
  let kVmCast = r_reify "VmCast"
  let kNative = r_reify "NativeCast"
  let kCast = r_reify "Cast"
  let kRevertCast = r_reify "RevertCast"
  let sProp = r_reify "sProp"
  let sSet = r_reify "sSet"
  let sType = r_reify "sType"
  let [tTerm;tRel;tVar;tMeta;tEvar;tSort;tCast;tProd;tLambda;tLetIn;tApp;tCase;tFix]
      = List.map r_reify ["term";"tRel";"tVar";"tMeta";"tEvar";"tSort";"tCast";"tProd";"tLambda";"tLetIn";"tApp";"tCase";"tFix"]

  let to_positive =
    let xH = resolve_symbol pkg_bignums "xH" in
    let xO = resolve_symbol pkg_bignums "xO" in
    let xI = resolve_symbol pkg_bignums "xI" in
    let rec to_positive n =
      if n = 1 then
	xH
      else
	if n mod 2 = 0 then
	  Term.mkApp (xO, [| to_positive (n / 2) |])
	else
  	  Term.mkApp (xI, [| to_positive (n / 2) |])
    in
    fun n ->
      if n <= 0
      then raise (Invalid_argument ("to_positive: " ^ string_of_int n))
      else to_positive n

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

  let quote_ident i =
    let s = Names.string_of_id i in
    assert false

  let quote_name n =
    match n with
      Names.Name id -> Term.mkApp (nNamed, [| quote_ident id |])
    | Names.Anonymous -> nAnon

  let quote_cast_kind k =
    match k with
      Term.VMcast -> kVmCast
    | Term.DEFAULTcast -> kCast
    | Term.REVERTcast -> kRevertCast

  let quote_universe s =
    (** Don't seem to be able to do this **)
    assert false

  let quote_sort s =
    match s with
      Term.Prop Term.Pos -> sProp
    | Term.Prop Term.Null -> sSet
    | Term.Type u -> Term.mkApp (sType, [| quote_universe u |])

  let rec quote_term trm =
    match Term.kind_of_term trm with
      Term.Rel i -> Term.mkApp (tRel, [| int_to_nat i |])
    | Term.Var v -> Term.mkApp (tVar, [| quote_ident v |])
    | Term.Sort s -> Term.mkApp (tSort, [| quote_sort s |])
    | Term.Cast (c,k,t) ->
      Term.mkApp (tCast, [| quote_term c ; quote_cast_kind k ; quote_term t |])
    | Term.Prod (n,t,b) ->
      Term.mkApp (tProd, [| quote_name n ; quote_term t ; quote_term b |])
    | Term.Lambda (n,t,b) ->
      Term.mkApp (tLambda, [| quote_name n ; quote_term t ; quote_term b |])
    | Term.LetIn (n,t,e,b) ->
      Term.mkApp (tLetIn, [| quote_name n ; quote_term t ; quote_term e ; quote_term b |])
    | Term.App (f,xs) ->
      Term.mkApp (tApp, [| quote_term f ; to_coq_list tTerm (List.map quote_term (Array.to_list xs)) |])
    | Term.Case (ci, e, t, args) ->
      assert false
    | _ -> raise (NotSupported trm)

  let rec app_full trm acc =
    match Term.kind_of_term trm with
      Term.App (f, xs) -> app_full f (Array.to_list xs @ acc)
    | _ -> (trm, acc)

  let rec nat_to_int trm =
    let (h,args) = app_full trm [] in
    if Term.eq_constr h tO then
      0
    else if Term.eq_constr h tS then
      match args with
	n :: _ -> 1 + nat_to_int n
      | _ -> not_supported trm
    else
      not_supported trm

  let from_bool trm =
    if Term.eq_constr trm ttrue then
      true
    else if Term.eq_constr trm tfalse then
      false
    else not_supported trm

  let unquote_char trm =
    let (h,args) = app_full trm [] in
    if Term.eq_constr h tAscii then
      match args with
	a :: b :: c :: d :: e :: f :: g :: h :: i :: _ ->
	  let bits = [a;b;c;d;e;f;g;h;i] in
	  let v = List.fold_left (fun a n -> (a lsr 1) lor if from_bool n then 1 else 0) 0 bits in
	  char_of_int v
      | _ -> assert false
    else
      not_supported trm

  let unquote_ident trm =
    let rec go n trm =
      let (h,args) = app_full trm [] in
      if Term.eq_constr h tEmptyString then
	String.create n
      else if Term.eq_constr h tString then
	match args with
	  c :: s :: _ ->
	    let res = go (n + 1) s in
	    let _ = String.set res n (unquote_char c) in
	    res
	| _ -> bad_term trm
      else
	not_supported trm
    in Names.id_of_string (go 0 trm)

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

  let unquote_sort trm =
    let (h,args) = app_full trm [] in
    if Term.eq_constr h sType then
      raise (NotSupported h)
    else if Term.eq_constr h sProp then
      Term.Prop Term.Pos
    else if Term.eq_constr h sSet then
      Term.Prop Term.Null
    else
      raise (Failure "ill-typed, expected sort")

  let rec from_coq_list trm =
    let (h,args) = app_full trm [] in
    if Term.eq_constr h c_nil then []
    else if Term.eq_constr h c_cons then
      match args with
	_ :: x :: xs :: _ -> x :: from_coq_list xs
      | _ -> bad_term trm
    else
      not_supported trm


  let rec denote trm =
    let (h,args) = app_full trm [] in
    if Term.eq_constr h tRel then
      match args with
	x :: _ ->
	  Term.mkRel (nat_to_int x)
      | _ -> raise (Failure "ill-typed")
    else if Term.eq_constr h tVar then
      match args with
	x :: _ -> Term.mkVar (unquote_ident x)
      | _ -> raise (Failure "ill-typed")
    else if Term.eq_constr h tSort then
      match args with
	x :: _ -> Term.mkSort (unquote_sort x)
      | _ -> raise (Failure "ill-typed")
    else if Term.eq_constr h tCast then
      match args with
	t :: c :: ty :: _ ->
	  Term.mkCast (denote t, unquote_cast_kind c, denote ty)
      | _ -> raise (Failure "ill-typed")
    else if Term.eq_constr h tProd then
      match args with
	n :: t :: b :: _ ->
	  Term.mkProd (unquote_name n, denote t, denote b)
      | _ -> raise (Failure "ill-typed (product)")
    else if Term.eq_constr h tLambda then
      match args with
	n :: t :: b :: _ ->
	  Term.mkLambda (unquote_name n, denote t, denote b)
      | _ -> raise (Failure "ill-typed (lambda)")
    else if Term.eq_constr h tLetIn then
      match args with
	n :: t :: e :: b :: _ ->
	  Term.mkLetIn (unquote_name n, denote t, denote e, denote b)
      | _ -> raise (Failure "ill-typed (let-in)")
    else if Term.eq_constr h tApp then
      match args with
	f :: xs :: _ ->
	  Term.mkApp (denote f,
		      Array.of_list (List.map denote (from_coq_list xs)))
      | _ -> raise (Failure "ill-typed (app)")
    else
      raise (NotSupported trm)

end

let _= Mltop.add_known_module "templateCoq"

TACTIC EXTEND get_goal
    | [ "quote_goal" ] ->
      [ (** get the representation of the goal **)
	fun gl -> assert false ]
    | [ "quote_term" constr(c) ] ->
      [ (** quote the given term **)
	fun gl -> assert false ]
    | [ "get_inductive" constr(i) ] ->
      [ fun gl -> assert false ]
END;;

VERNAC COMMAND EXTEND Make
    | [ "Make" "Definition" ident(d) tactic(t) ] ->
      [ (** [t] returns a [term] **)
	assert false ]
    | [ "Make" "Definitions" tactic(t) ] ->
      [ (** [t] returns a [list (string * term)] **)
	assert false]
END;;
