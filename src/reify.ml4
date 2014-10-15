(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmp" i*)

let contrib_name = "template-coq"

let pp_constr fmt x = Pp.pp_with fmt (Printer.pr_constr x)

module TermReify = struct
  exception NotSupported of Term.constr

  module Cmap = Names.Cmap
  module Cset = Names.Cset
  module Mindset = Names.Mindset


  let not_supported trm =
    Format.eprintf "\nNot Supported: %a\n" pp_constr trm ;
    flush stderr ;
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
  let prod_type = resolve_symbol pkg_datatypes "prod"
  let prod a b =
    Term.mkApp (prod_type, [| a ; b |])
  let c_pair = resolve_symbol pkg_datatypes "pair"
  let pair a b f s =
    Term.mkApp (c_pair, [| a ; b ; f ; s |])

  let nAnon = r_reify "nAnon"
  let nNamed = r_reify "nNamed"
  let kVmCast = r_reify "VmCast"
  let kNative = r_reify "NativeCast"
  let kCast = r_reify "Cast"
  let kRevertCast = r_reify "RevertCast"
  let sProp = r_reify "sProp"
  let sSet = r_reify "sSet"
  let sType = r_reify "sType"
  let tident = r_reify "ident"
  let tmkInd = r_reify "mkInd"
  let [tTerm;tRel;tVar;tMeta;tEvar;tSort;tCast;tProd;tLambda;tLetIn;tApp;tCase;tFix;tConstructor;tConst;tInd;tUnknown]
      = List.map r_reify ["term";"tRel";"tVar";"tMeta";"tEvar";"tSort";"tCast";"tProd";"tLambda";"tLetIn";"tApp";"tCase";"tFix";"tConstruct";"tConst";"tInd";"tUnknown"]
  let [tdef;tmkdef] = List.map r_reify ["def";"mkdef"]
  let [pConstr;pType;pAxiom;pIn]
      = List.map r_reify ["PConstr";"PType";"PAxiom";"PIn"]
  let tinductive_body = r_reify "inductive_body"
  let tmkinductive_body = r_reify "mkinductive_body"

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
    (** TODO: This doesn't work yet **)
    to_positive 1

  let quote_sort s =
    match s with
      Term.Prop _ ->
	if s = Term.prop_sort then sProp
	else
	  let _ = assert (s = Term.set_sort) in
	  sSet
    | Term.Type u -> Term.mkApp (sType, [| quote_universe u |])

  let quote_inductive env (t : Names.inductive) =
    let (m,i) = t in
    Term.mkApp (tmkInd, [| quote_string (Names.string_of_kn (Names.canonical_mind m))
			 ; int_to_nat i |])

  let mk_ctor_list =
    let ctor_list =
      let ctor_info_typ = prod tident tTerm in
      to_coq_list ctor_info_typ
    in
    fun ls ->
      let ctors = List.map (fun (a,b) -> pair tident tTerm a b) ls in
      Term.mkApp (tmkinductive_body, [| ctor_list ctors |])

  let rec pair_with_number st ls =
    match ls with
      [] -> []
    | l :: ls -> (st,l) :: pair_with_number (st + 1) ls


  let quote_term_remember
      (add_constant : Names.constant -> 'a -> 'a)
      (add_inductive : Names.inductive -> 'a -> 'a) =
    let rec quote_term (acc : 'a) env trm =
      match Term.kind_of_term trm with
	Term.Rel i -> (Term.mkApp (tRel, [| int_to_nat (i - 1) |]), acc)
      | Term.Var v -> (Term.mkApp (tVar, [| quote_ident v |]), acc)
      | Term.Sort s -> (Term.mkApp (tSort, [| quote_sort s |]), acc)
      | Term.Cast (c,k,t) ->
	let (c',acc) = quote_term acc env c in
	let (t',acc) = quote_term acc env t in
	(Term.mkApp (tCast, [| c' ; quote_cast_kind k ; t' |]), acc)
      | Term.Prod (n,t,b) ->
	let (t',acc) = quote_term acc env t in
	let (b',acc) = quote_term acc env b in
	(Term.mkApp (tProd, [| quote_name n ; t' ; b' |]), acc)
      | Term.Lambda (n,t,b) ->
	let (t',acc) = quote_term acc env t in
	let (b',acc) = quote_term acc env b in
	(Term.mkApp (tLambda, [| quote_name n ; t' ; b' |]), acc)
      | Term.LetIn (n,t,e,b) ->
	let (t',acc) = quote_term acc env t in
	let (e',acc) = quote_term acc env e in
	let (b',acc) = quote_term acc env b in
	(Term.mkApp (tLetIn, [| quote_name n ; t' ; e' ; b' |]), acc)
      | Term.App (f,xs) ->
	let (f',acc) = quote_term acc env f in
	let (xs',acc) =
	  List.fold_left (fun (xs,acc) x ->
	    let (x,acc) = quote_term acc env x in (x :: xs, acc))
	    ([],acc) (Array.to_list xs) in
	(Term.mkApp (tApp, [| f' ; to_coq_list tTerm (List.rev xs') |]), acc)
      | Term.Const c ->
	(Term.mkApp (tConst, [| quote_string (Names.string_of_con c) |]), add_constant c acc)
      | Term.Construct (ind,c) ->
	(Term.mkApp (tConstructor, [| quote_inductive env ind ; int_to_nat (c - 1) |]), add_inductive ind acc)
      | Term.Ind i -> (Term.mkApp (tInd, [| quote_inductive env i |]), add_inductive i acc)
      | Term.Case (ci,a,b,e) ->
        let npar = int_to_nat ci.ci_npar in
	let (a',acc) = quote_term acc env a in
	let (b',acc) = quote_term acc env b in
	let (branches,acc) =
	  List.fold_left (fun (xs,acc) x ->
	    let (x,acc) = quote_term acc env x in (x :: xs, acc))
	    ([],acc) (Array.to_list e) in
	(Term.mkApp (tCase, [| npar ; a' ; b' ; to_coq_list tTerm (List.rev branches) |]), acc)
      | Term.Fix fp ->
	let (t,n,acc) = quote_fixpoint acc env fp in
	(Term.mkApp (tFix, [| t ; int_to_nat n |]), acc)
      | _ -> (Term.mkApp (tUnknown, [| quote_string (Format.asprintf "%a" pp_constr trm) |]), acc)
    and quote_fixpoint acc env t =
      let ((a,b),(ns,ts,ds)) = t in
      let rec seq f t =
	if f < t then
	  f :: seq (f + 1) t
	else
	  []
      in
      let mk_fun (xs,acc) i =
	let n = int_to_nat (Array.get a i) in
	let nm = quote_name (Array.get ns i) in
	let (ty,acc) = quote_term acc env (Array.get ts i) in
	let (ds,acc) = quote_term acc env (Array.get ds i) in
	(Term.mkApp (tmkdef, [| tTerm ; nm ; ty ; ds ; n |]) :: xs, acc)
      in
      let (defs,acc) = List.fold_left mk_fun ([],acc) (seq 0 (Array.length a)) in
      (to_coq_list (Term.mkApp (tdef, [| tTerm |])) (List.rev defs), b, acc)
    and quote_minductive_type (acc : 'a) env (t : Names.mutual_inductive) =
      let mib = Environ.lookup_mind t env in
      let (ls,acc) =
	List.fold_left (fun (ls,acc) (n,oib) ->
	  let named_ctors =
	    List.combine
	      Declarations.(Array.to_list oib.mind_consnames)
	      Declarations.(Array.to_list oib.mind_user_lc)
	  in
	  let (reified_ctors,acc) =
	    List.fold_left (fun (ls,acc) (nm,ty) ->
	      let (ty,acc) = quote_term acc env ty in
	      ((quote_ident nm, ty) :: ls, acc))
	      ([],acc) named_ctors
	  in
	  Declarations.((quote_ident oib.mind_typename,
	    mk_ctor_list (List.rev reified_ctors)) :: ls, acc))
	  ([],acc) Declarations.(pair_with_number 0
		      (Array.to_list mib.mind_packets))
      in
      (to_coq_list (prod tident tinductive_body)
	 (List.map (fun (a,b) ->
	   pair tident tinductive_body a b) (List.rev ls)),
       acc)
    in (quote_term, quote_minductive_type)

  let quote_term env trm =
    let (fn,_) = quote_term_remember (fun _ () -> ()) (fun _ () -> ()) in
    fst (fn () env trm)

  type defType =
    Ind of Names.inductive
  | Const of Names.constant

  let quote_term_rec env trm =
    let visited_terms = ref Cset.empty in
    let visited_types = ref Mindset.empty in
    let constants = ref [] in
    let add quote_term quote_type trm acc =
      match trm with
      | Ind (mi,idx) ->
	let t = mi in
	if Mindset.mem t !visited_types then ()
	else
	  begin
	    let (result,acc) = quote_type acc env mi in
	    let ref_name =
	      quote_string (Names.string_of_kn (Names.canonical_mind mi)) in
	    visited_types := Mindset.add t !visited_types ;
	    constants := Term.mkApp (pType, [| ref_name
					     ; result |]) :: !constants
	  end
      | Const c ->
	if Cset.mem c !visited_terms then ()
	else
	  begin
	    visited_terms := Cset.add c !visited_terms ;
	    let cd = Environ.lookup_constant c env in
	    let do_body body =
	      let (result,acc) =
		quote_term acc Environ.empty_env body
	      in
	      constants := Term.mkApp (pConstr,
				       [| quote_string (Names.string_of_con c)
				       ; result |]) :: !constants
	    in
	    Declarations.(
	      match cd.const_body with
		Undef i ->
		  constants := Term.mkApp (pAxiom,
					   [| quote_string (Names.string_of_con c) |]) :: !constants
	      | Def cs ->
		do_body (force cs)
	      | OpaqueDef lc ->
		do_body (force_opaque lc))
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
    in List.fold_left (fun acc x -> Term.mkApp (x, [| acc |]))
                      (Term.mkApp (pIn, [| x |])) !constants

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
    in
    go 0 trm

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

  let kn_of_canonical_string s =
    let ss = List.rev (Str.split (Str.regexp (Str.quote ".")) s) in
    match ss with
      nm :: rst ->
	let rec to_mp ls = Names.MPfile (Names.make_dirpath (List.map Names.id_of_string ls)) in
	let mp = to_mp rst in
	Names.make_kn mp Names.empty_dirpath (Names.mk_label nm)
    | _ -> assert false

  let denote_inductive trm =
    let (h,args) = app_full trm [] in
    if Term.eq_constr h tmkInd then
      match args with
	nm :: num :: _ ->
	  let n = unquote_string nm in
	  let kn = kn_of_canonical_string n in
	  let mi = Names.mind_of_kn kn in
	  let i = nat_to_int num in
	  (mi, i)
      | _ -> assert false
    else
      raise (Failure "non-constructor")

  let rec from_coq_list trm =
    let (h,args) = app_full trm [] in
    if Term.eq_constr h c_nil then []
    else if Term.eq_constr h c_cons then
      match args with
	_ :: x :: xs :: _ -> x :: from_coq_list xs
      | _ -> bad_term trm
    else
      not_supported trm


  (** NOTE: Because the representation is lossy, I should probably
   ** come back through elaboration.
   ** - This would also allow me to write terms with holes
   **)
  let rec denote_term trm =
    Format.eprintf "%a\n" pp_constr trm ;
    let (h,args) = app_full trm [] in
    if Term.eq_constr h tRel then
      match args with
	x :: _ ->
	  Format.eprintf "Rel\n" ;
	  Term.mkRel (nat_to_int x + 1)
      | _ -> raise (Failure "ill-typed")
    else if Term.eq_constr h tVar then
      match args with
	x :: _ -> Format.eprintf "var\n"; Term.mkVar (unquote_ident x)
      | _ -> raise (Failure "ill-typed")
    else if Term.eq_constr h tSort then
      match args with
	x :: _ -> Term.mkSort (unquote_sort x)
      | _ -> raise (Failure "ill-typed")
    else if Term.eq_constr h tCast then
      match args with
	t :: c :: ty :: _ ->
	  Term.mkCast (denote_term t, unquote_cast_kind c, denote_term ty)
      | _ -> raise (Failure "ill-typed")
    else if Term.eq_constr h tProd then
      match args with
	n :: t :: b :: _ ->
	  Term.mkProd (unquote_name n, denote_term t, denote_term b)
      | _ -> raise (Failure "ill-typed (product)")
    else if Term.eq_constr h tLambda then
      match args with
	n :: t :: b :: _ ->
      Format.eprintf "lambda\n";
	  Term.mkLambda (unquote_name n, denote_term t, denote_term b)
      | _ -> raise (Failure "ill-typed (lambda)")
    else if Term.eq_constr h tLetIn then
      match args with
	n :: t :: e :: b :: _ ->
	  Term.mkLetIn (unquote_name n, denote_term t, denote_term e, denote_term b)
      | _ -> raise (Failure "ill-typed (let-in)")
    else if Term.eq_constr h tApp then
      match args with
	f :: xs :: _ ->
	  Term.mkApp (denote_term f,
		      Array.of_list (List.map denote_term (from_coq_list xs)))
      | _ -> raise (Failure "ill-typed (app)")
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
	ty :: d :: brs :: _ ->
	  Term.mkCase (assert false (** I don't have any information to put here **)
		      , denote_term ty, denote_term d ,
			Array.of_list (List.map denote_term (from_coq_list brs)))
      | _ -> raise (Failure "ill-typed (case)")
    else
      not_supported trm

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

let check_inside_section () =
  if Lib.sections_are_opened () then
    (** In trunk this seems to be moved to Errors **)
    Util.errorlabstrm "Quote" (Pp.str "You can not quote within a section.")
  else ()



TACTIC EXTEND get_goal
    | [ "quote_term" constr(c) tactic(tac) ] ->
      [ (** quote the given term, pass the result to t **)
	fun gl ->
	  let env = Tacmach.pf_env gl in
	  let c = TermReify.quote_term env c in
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
      [ check_inside_section () ;
	let (evm,env) = Lemmas.get_current_context () in
	let def = Constrintern.interp_constr evm env def in
	let trm = TermReify.quote_term env def in
	let result = Constrextern.extern_constr true env trm in
	declare_definition name
	  (Decl_kinds.Global, false, Decl_kinds.Definition)
	  [] None result None (fun _ _ -> ()) ]
    | [ "Quote" "Definition" ident(name) ":=" "Eval" red_expr(rd) "in" constr(def) ] ->
      [ check_inside_section () ;
	let (evm,env) = Lemmas.get_current_context () in
	let def = Constrintern.interp_constr evm env def in
	let (evm2,red) = Tacinterp.interp_redexp env evm rd in
	let red = fst (Redexpr.reduction_of_red_expr red) in
	let def = red env evm2 def in
	let trm = TermReify.quote_term env def in
	let result = Constrextern.extern_constr true env trm in
	declare_definition name
	  (Decl_kinds.Global, false, Decl_kinds.Definition)
	  [] None result None (fun _ _ -> ()) ]
END;;

VERNAC COMMAND EXTEND Make_recursive
    | [ "Quote" "Recursively" "Definition" ident(name) ":=" constr(def) ] ->
      [ check_inside_section () ;
	let (evm,env) = Lemmas.get_current_context () in
	let def = Constrintern.interp_constr evm env def in
	let trm = TermReify.quote_term_rec env def in
	let result = Constrextern.extern_constr true env trm in
	declare_definition name
	  (Decl_kinds.Global, false, Decl_kinds.Definition)
	  [] None result None (fun _ _ -> ()) ]
END;;

VERNAC COMMAND EXTEND Unquote_vernac
    | [ "Make" "Definition" ident(name) ":=" constr(def) ] ->
      [ check_inside_section () ;
	let (evm,env) = Lemmas.get_current_context () in
	let def = Constrintern.interp_constr evm env def in
	let trm = TermReify.denote_term def in
	let result = Constrextern.extern_constr true env trm in
	declare_definition name
	  (Decl_kinds.Global, false, Decl_kinds.Definition)
	  [] None result None (fun _ _ -> ()) ]
END;;

VERNAC COMMAND EXTEND Make_tests
(*
    | [ "Make" "Definitions" tactic(t) ] ->
      [ (** [t] returns a [list (string * term)] **)
	assert false ]
*)
    | [ "Test" "Quote" constr(c) ] ->
      [ check_inside_section () ;
	let (evm,env) = Lemmas.get_current_context () in
	let c = Constrintern.interp_constr evm env c in
	let result = TermReify.quote_term env c in
(* DEBUGGING
	let back = TermReify.denote_term result in
	Format.eprintf "%a\n" pp_constr result ;
	Format.eprintf "%a\n" pp_constr back ;
	assert (Term.eq_constr c back) ;
*)
	Pp.msgnl (Printer.pr_constr result) ;
	() ]
END;;
