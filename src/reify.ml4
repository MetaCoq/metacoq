(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmp" i*)

let contrib_name = "template-coq"

let pp_constr fmt x = Pp.pp_with fmt (Printer.pr_constr x)

module TermReify = struct
  exception NotSupported of Term.constr

  let not_supported trm =
    Format.eprintf "\nNot Supported: %a\n" pp_constr trm ;
    flush stdout ;
    raise (NotSupported trm)
  let bad_term trm =
    raise (NotSupported trm)

  let resolve_symbol (path : string list) (tm : string) : Term.constr =
    let re = Coqlib.find_reference contrib_name path tm in
    Libnames.constr_of_global re

  let pkg_bignums = ["Coq";"Numbers";"BinNums"]
  let pkg_datatypes = ["Coq";"Init";"Datatypes"]
  let pkg_reify = ["Template";"Ast"]
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
  let tmkInd = r_reify "mkInd"
  let [tTerm;tRel;tVar;tMeta;tEvar;tSort;tCast;tProd;tLambda;tLetIn;tApp;tCase;tFix;tConstructor;tConst;tInd;tUnknown]
      = List.map r_reify ["term";"tRel";"tVar";"tMeta";"tEvar";"tSort";"tCast";"tProd";"tLambda";"tLetIn";"tApp";"tCase";"tFix";"tConstruct";"tConst";"tInd";"tUnknown"]
  let [tdef;tmkdef] = List.map r_reify ["def";"mkdef"]

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

  let quote_bool b =
    if b then ttrue else tfalse

  let quote_char c =
    let i = int_of_char c in
    Term.mkApp (tAscii, Array.of_list (List.map (fun m -> quote_bool ((i land m) = m))
					 (List.rev [128;64;32;16;8;4;2;1])))

  let quote_string s =
    let rec go from acc =
      if from < 0 then acc
      else
	go (from - 1) (Term.mkApp (tString, [| quote_char (String.get s from) ; acc |]))
    in
    go (String.length s - 1) tEmptyString

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

  let quote_universe s =
    (** Don't seem to be able to do this **)
    assert false

  let quote_sort s =
    match s with
      Term.Prop Term.Pos -> sProp
    | Term.Prop Term.Null -> sSet
    | Term.Type u -> Term.mkApp (sType, [| quote_universe u |])

  let quote_inductive (t : Names.inductive) =
    let (_,i) = t in
    Term.mkApp (tmkInd, [| quote_string (Format.asprintf "%a" pp_constr (Term.mkInd t))
			 ; int_to_nat i |])

  let rec quote_term trm =
    match Term.kind_of_term trm with
      Term.Rel i -> Term.mkApp (tRel, [| int_to_nat (i - 1) |])
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
    | Term.Const c -> Term.mkApp (tConst, [| quote_string (Names.string_of_con c) |])
    | Term.Construct (ind,c) -> Term.mkApp (tConstructor, [| quote_inductive ind ; int_to_nat (c - 1) |])
    | Term.Ind i -> Term.mkApp (tInd, [| quote_inductive i |])
    | Term.Case (ci,a,b,e) ->
      Term.mkApp (tCase, [| quote_term a ; quote_term b
			  ; to_coq_list tTerm (List.map (fun x -> quote_term x) (Array.to_list e)) |])
    | Term.Fix fp ->
      let (t,n) = quote_fixpoint fp in
      Term.mkApp (tFix, [| t ; int_to_nat n |])
    | _ -> Term.mkApp (tUnknown, [| quote_string (Format.asprintf "%a" pp_constr trm) |])
  and quote_fixpoint t =
    let ((a,b),(ns,ts,ds)) = t in
    let rec seq f t =
      if f < t then
	f :: seq (f + 1) t
      else
	[]
    in
    let mk_fun i =
      let n = int_to_nat (Array.get a i) in
      let nm = quote_name (Array.get ns i) in
      let ty = quote_term (Array.get ts i) in
      let ds = quote_term (Array.get ds i) in
      Term.mkApp (tmkdef, [| tTerm ; nm ; ty ; ds ; n |])
    in
    let defs = to_coq_list (Term.mkApp (tdef, [| tTerm |]))
      (List.map mk_fun (seq 0 (Array.length a)))
    in
    (defs, b)

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

(** Stolen from CoqPluginUtils **)
(** Calling Ltac **)
let ltac_call tac (args:Tacexpr.glob_tactic_arg list) =
  Tacexpr.TacArg(Util.dummy_loc,Tacexpr.TacCall(Util.dummy_loc, Glob_term.ArgArg(Util.dummy_loc, Lazy.force tac),args))

(* Calling a locally bound tactic *)
let ltac_lcall tac args =
  Tacexpr.TacArg(Util.dummy_loc,Tacexpr.TacCall(Util.dummy_loc, Glob_term.ArgVar(Util.dummy_loc, Names.id_of_string tac),args))

let ltac_letin (x, e1) e2 =
  Tacexpr.TacLetIn(false,[(Util.dummy_loc,Names.id_of_string x),e1],e2)

let ltac_apply (f:Tacexpr.glob_tactic_expr) (args:Tacexpr.glob_tactic_arg list) =
  Tacinterp.eval_tactic
    (ltac_letin ("F", Tacexpr.Tacexp f) (ltac_lcall "F" args))

let to_ltac_val c = Tacexpr.TacDynamic(Util.dummy_loc,Pretyping.constr_in c)

(** From Containers **)
let declare_definition
    id (loc, boxed_flag, def_obj_kind)
    binder_list red_expr_opt constr_expr
    constr_expr_opt decl_hook =
  let (def_entry, man_impl) =
    Command.interp_definition binder_list red_expr_opt constr_expr
      constr_expr_opt
  in
    Command.declare_definition
      id (loc, def_obj_kind) def_entry man_impl decl_hook


TACTIC EXTEND get_goal
    | [ "quote_term" constr(c) tactic(tac) ] ->
      [ (** quote the given term, pass the result to t **)
	fun gl ->
	  let c = TermReify.quote_term c in
	  ltac_apply tac (List.map to_ltac_val [c]) gl ]
(*
    | [ "quote_goal" ] ->
      [ (** get the representation of the goal **)
	fun gl -> assert false ]
    | [ "get_inductive" constr(i) ] ->
      [ fun gl -> assert false ]
*)
END;;

VERNAC COMMAND EXTEND Make_vernac
    | [ "Quote" "Definition" ident(name) ":=" constr(def) ] ->
      [ let (evm,env) = Lemmas.get_current_context () in
	let def = Constrintern.interp_constr evm env def in
	let trm = TermReify.quote_term def in
	let result = Constrextern.extern_constr true env trm in
	declare_definition name
	  (Decl_kinds.Global, false, Decl_kinds.Definition)
	  [] None result None (fun _ _ -> ()) ]
    | [ "Quote" "Definition" ident(name) ":=" "Eval" red_expr(rd) "in" constr(def) ] ->
      [ let (evm,env) = Lemmas.get_current_context () in
	let def = Constrintern.interp_constr evm env def in
	let (evm2,red) = Tacinterp.interp_redexp env evm rd in
	let red = fst (Redexpr.reduction_of_red_expr red) in
	let def = red env evm2 def in
	let trm = TermReify.quote_term def in
	let _ = Format.printf "%a\n" pp_constr trm in
	let result = Constrextern.extern_constr true env trm in
	declare_definition name
	  (Decl_kinds.Global, false, Decl_kinds.Definition)
	  [] None result None (fun _ _ -> ())

 ]
END;;
(**
    | [ "Quote" "Definition" ident(d) ; d = def_body ]
      [ 
**)


VERNAC COMMAND EXTEND Make

(*
    | [ "Make" "Definition" ident(d) tactic(t) ] ->
      [ (** [t] returns a [term] **)
	assert false ]
    | [ "Make" "Definitions" tactic(t) ] ->
      [ (** [t] returns a [list (string * term)] **)
	assert false ]
*)
    | [ "Test" "Quote" constr(c) ] ->
      [ let (evm,env) = Lemmas.get_current_context () in
	let c = Constrintern.interp_constr evm env c in
	let result = TermReify.quote_term c in
	Pp.msgnl (Printer.pr_constr result) ;
	() ]
END;;
