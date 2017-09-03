(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmp" i*)

let contrib_name = "template-coq"

let cast_prop = ref (false)
let _ = Goptions.declare_bool_option {
  Goptions.optsync = true; Goptions.optdepr = false;
  Goptions.optname = "Casting of propositions in template-coq";
  Goptions.optkey = ["Template";"Cast";"Propositions"];
  Goptions.optread = (fun () -> !cast_prop);
  Goptions.optwrite = (fun a -> cast_prop:=a);
}

(* whether Set Template Cast Propositions is on, as needed for erasure in Certicoq *)
let is_cast_prop () = !cast_prop

let pp_constr fmt x = Pp.pp_with fmt (Printer.pr_constr x)

open Pp (* this adds the ++ to the current scope *)

exception NotSupported of Term.constr
   
let not_supported trm =
  Feedback.msg_error (str "Not Supported:" ++ spc () ++ Printer.pr_constr trm) ;
  raise (NotSupported trm)
let bad_term trm =
  raise (NotSupported trm)
(* flags *)
  
let opt_hnf_ctor_types = ref false
let opt_debug = ref false
              
let with_debug f =
  opt_debug := true ;
  try
    let result = f () in
    opt_debug := false ;
    result
  with
    e -> let _ = opt_debug := false in raise e

let debug (m : unit -> Pp.std_ppcmds) =
  if !opt_debug then
    Feedback.(msg_debug (m ()))
  else
    ()

let with_hnf_ctor_types f =
  opt_hnf_ctor_types := true ;
  try
    let result = f () in
    opt_hnf_ctor_types := false ;
    result
  with
    e -> let _ = opt_hnf_ctor_types := false in raise e

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

module Cmap = Names.KNmap
module Cset = Names.KNset
module Mindset = Names.Mindset
   
module type Quoter = sig
  type t

  type quoted_ident
  type quoted_int
  type quoted_name
  type quoted_sort
  type quoted_cast_kind
  type quoted_kernel_name
  type quoted_inductive
  type quoted_decl
  type quoted_program
     
  open Names

  val quote_ident : Id.t -> quoted_ident
  val quote_name : Name.t -> quoted_name
  val quote_int : int -> quoted_int
  val quote_sort : Sorts.t -> quoted_sort
  val quote_cast_kind : Constr.cast_kind -> quoted_cast_kind
  val quote_kn : kernel_name -> quoted_kernel_name
  val quote_inductive : quoted_kernel_name * quoted_int -> quoted_inductive
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
  val mkConst : quoted_kernel_name -> t
  val mkInd : quoted_inductive -> t
  val mkConstruct : quoted_inductive * quoted_int -> t
  val mkCase : (quoted_inductive * quoted_int) -> quoted_int list -> t -> t ->
               t list -> t
  val mkProj : quoted_kernel_name -> t -> t
  val mkFix : (quoted_int array * quoted_int) * (quoted_name array * t array * t array) -> t
  val mkCoFix : quoted_int * (quoted_name array * t array * t array) -> t

  val mkMutualInductive : quoted_kernel_name -> quoted_int (* params *) ->
                          (quoted_ident * t (* ind type *) *
                             (quoted_ident * t (* constr type *) * quoted_int) list) list ->
                          quoted_decl

  val mkConstant : quoted_kernel_name -> t (* type *) -> t (* body *) -> quoted_decl
  val mkAxiom : quoted_kernel_name -> t -> quoted_decl

  val mkExt : quoted_decl -> quoted_program -> quoted_program
  val mkIn : t -> quoted_program 
end

(** The reifier to Coq values *)                   
module TemplateCoqQuoter =
struct 
  type t = Term.constr

  type quoted_ident = Term.constr
  type quoted_int = Term.constr
  type quoted_name = Term.constr
  type quoted_sort = Term.constr
  type quoted_cast_kind = Term.constr
  type quoted_kernel_name = Term.constr
  type quoted_recdecl = Term.constr
  type quoted_inductive = Term.constr

  type quoted_decl = Term.constr

  type quoted_program = Term.constr

  let resolve_symbol (path : string list) (tm : string) : Term.constr =
    Coqlib.gen_constant_in_modules contrib_name [path] tm

  let pkg_bignums = ["Coq";"Numbers";"BinNums"]
  let pkg_datatypes = ["Coq";"Init";"Datatypes"]
  let pkg_reify = ["Template";"Ast"]
  let pkg_string = ["Coq";"Strings";"String"]

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
  let tAscii = resolve_symbol ["Coq";"Strings";"Ascii"] "Ascii"
  let c_nil = resolve_symbol pkg_datatypes "nil"
  let c_cons = resolve_symbol pkg_datatypes "cons"
  let prod_type = resolve_symbol pkg_datatypes "prod"
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
  let sProp = r_reify "sProp"
  let sSet = r_reify "sSet"
  let sType = r_reify "sType"
  let tident = r_reify "ident"
  let tIndTy = r_reify "inductive"
  let tmkInd = r_reify "mkInd"
  let (tTerm,tRel,tVar,tMeta,tEvar,tSort,tCast,tProd,
       tLambda,tLetIn,tApp,tCase,tFix,tConstructor,tConst,tInd,tCoFix,tProj) =
    (r_reify "term", r_reify "tRel", r_reify "tVar", r_reify "tMeta", r_reify "tEvar",
     r_reify "tSort", r_reify "tCast", r_reify "tProd", r_reify "tLambda",
     r_reify "tLetIn", r_reify "tApp", r_reify "tCase", r_reify "tFix",
     r_reify "tConstruct", r_reify "tConst", r_reify "tInd", r_reify "tCoFix", r_reify "tProj")

  let (tdef,tmkdef) = (r_reify "def", r_reify "mkdef")
  let (tLocalDef,tLocalAssum) = (r_reify "LocalDef", r_reify "LocalAssum")
  let (cFinite,cCoFinite,cBiFinite) = (r_reify "Finite", r_reify "CoFinite", r_reify "BiFinite")
  let (pConstr,pType,pAxiom,pIn) =
    (r_reify "PConstr", r_reify "PType", r_reify "PAxiom", r_reify "PIn")
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

  let quote_char i =
    Term.mkApp (tAscii, Array.of_list (List.map (fun m -> quote_bool ((i land m) = m))
					 (List.rev [128;64;32;16;8;4;2;1])))

  let chars = Array.init 255 quote_char

  let quote_char c = chars.(int_of_char c)

  let string_hash = Hashtbl.create 420

  let quote_string s =
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
      let term = quote_string s in
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
      let ctor_info_typ = prod (prod tident tTerm) tnat in
      to_coq_list ctor_info_typ
    in
    fun ls ->
    let ctors = List.map (fun (a,b,c) -> pair (prod tident tTerm) tnat
					 (pair tident tTerm a b) c) ls in
      Term.mkApp (tmkinductive_body, [| ctor_list ctors |])

  let rec pair_with_number st ls =
    match ls with
      [] -> []
    | l :: ls -> (st,l) :: pair_with_number (st + 1) ls

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
  let mkConst kn = Term.mkApp (tConst, [| kn |])
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

  let mkCoFix (a,(ns,ts,ds)) =
    let mk_fun xs i =
      Term.mkApp (tmkdef, [| tTerm ; Array.get ns i ;
                             Array.get ts i ; Array.get ds i ; tO |]) :: xs
    in
    let defs = List.fold_left mk_fun [] (seq 0 (Array.length ns)) in
    let block = to_coq_list (Term.mkApp (tdef, [| tTerm |])) (List.rev defs) in
    Term.mkApp (tCoFix, [| block ; a |])

  let mkConstruct (ind, i) = 
    Term.mkApp (tConstructor, [| ind ; i |])

  let mkInd i = Term.mkApp (tInd, [| i |])

  let mkCase (ind, npar) nargs p c brs =
    let info = pair tIndTy tnat ind npar in
    let branches = List.map2 (fun br nargs ->  pair tnat tTerm nargs br) brs nargs in
    let tl = prod tnat tTerm in
    Term.mkApp (tCase, [| info ; p ; c ; to_coq_list tl branches |])

  let mkProj kn t =
    Term.mkApp (tProj, [| kn; t |])

  let mkMutualInductive kn p ls =
    let result = to_coq_list (prod (prod tident tTerm) tinductive_body)
         (List.map (fun (a,b,c) ->
                                let c = mk_ctor_list c in
	                        pair (prod tident tTerm) tinductive_body (pair tident tTerm a b) c)
                   (List.rev ls)) in
    Term.mkApp (pType, [| kn; p; result |])

    
  let mkConstant kn ty c =
    Term.mkApp (pConstr, [| kn; ty; c |])

  let mkAxiom kn t =
    Term.mkApp (pAxiom, [| kn; t |])

  let mkExt x acc = Term.mkApp (x, [| acc |])
  let mkIn t = Term.mkApp (pIn, [| t |])
end
                   
module Reify(Q : Quoter) =
struct

  let push_rel decl (in_prop, env) = (in_prop, Environ.push_rel decl env)
  let push_rel_context ctx (in_prop, env) = (in_prop, Environ.push_rel_context ctx env)

  let quote_term_remember
      (add_constant : Names.kernel_name -> 'a -> 'a)
      (add_inductive : Names.inductive -> 'a -> 'a) =
    let rec quote_term (acc : 'a) env trm =
      let rec aux acc env trm =
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
	let (b',acc) = quote_term acc (push_rel (Context.Rel.Declaration.LocalAssum (n, t)) env) b in
        (Q.mkProd (Q.quote_name n) t' b', acc)
      | Term.Lambda (n,t,b) ->
	let (t',acc) = quote_term acc env t in
	let (b',acc) = quote_term acc (push_rel (Context.Rel.Declaration.LocalAssum (n, t)) env) b in
	(Q.mkLambda (Q.quote_name n) t' b', acc)
      | Term.LetIn (n,e,t,b) ->
	let (e',acc) = quote_term acc env e in
	let (t',acc) = quote_term acc env t in
	let (b',acc) = quote_term acc (push_rel (Context.Rel.Declaration.LocalDef (n, e, t)) env) b in
	(Q.mkLetIn (Q.quote_name n) e' t' b', acc)
      | Term.App (f,xs) ->
	let (f',acc) = quote_term acc env f in
	let (acc,xs') =
	  CArray.fold_map (fun acc x ->
	    let (x,acc) = quote_term acc env x in acc,x)
	    acc xs in
	(Q.mkApp f' xs', acc)
      | Term.Const (c,pu) -> (* FIXME: take universe constraints into account *)
         let kn = Names.Constant.canonical c in
	 (Q.mkConst (Q.quote_kn kn), add_constant kn acc)
      | Term.Construct (((ind,i),c),pu) ->
         (* FIXME: take universe constraints into account *)
         (Q.mkConstruct (Q.quote_inductive (Q.quote_kn (Names.MutInd.canonical ind), Q.quote_int i),
                         Q.quote_int (c - 1)), add_inductive (ind,i) acc)
      | Term.Ind ((ind,i),pu) -> (* FIXME: take universe constraints into account *)
         (Q.mkInd (Q.quote_inductive (Q.quote_kn (Names.MutInd.canonical ind), Q.quote_int i)), add_inductive (ind,i) acc)
      | Term.Case (ci,a,b,e) ->
         let ind = Q.quote_inductive (Q.quote_kn (Names.MutInd.canonical (fst ci.Term.ci_ind)),
                                      Q.quote_int (snd ci.Term.ci_ind)) in
        let npar = Q.quote_int ci.Term.ci_npar in
	let (a',acc) = quote_term acc env a in
	let (b',acc) = quote_term acc env b in
	let (branches,nargs,acc) =
          CArray.fold_left2 (fun (xs,nargs,acc) x narg ->
              let (x,acc) = quote_term acc env x in
              let narg = Q.quote_int narg in
            (x :: xs, narg :: nargs, acc))
          ([],[],acc) e ci.Term.ci_cstr_nargs in
        (Q.mkCase (ind, npar) (List.rev nargs) a' b' (List.rev branches), acc)
      | Term.Fix fp -> quote_fixpoint acc env fp
      | Term.CoFix fp -> quote_cofixpoint acc env fp
      | Term.Proj (p,c) ->
         let kn = Names.Constant.canonical (Names.Projection.constant p) in
         let p' = Q.quote_kn kn in
         let t', acc = quote_term acc env c in
         (Q.mkProj p' t', add_constant kn acc)
      in
      let in_prop, env' = env in
      if is_cast_prop () && not in_prop then
        let ty =
          try Retyping.get_type_of env' Evd.empty trm
          with e ->
            Feedback.msg_debug (str"Anomaly trying to get the type of: " ++
                                  Printer.pr_constr_env (snd env) Evd.empty trm);
            raise e
        in
        let sf =
          try Retyping.get_sort_family_of env' Evd.empty ty
          with e ->
            Feedback.msg_debug (str"Anomaly trying to get the sort of: " ++
                                  Printer.pr_constr_env (snd env) Evd.empty ty);
            raise e
        in
        if sf == Term.InProp then
          aux acc (true, env')
              (Term.mkCast (trm, Term.DEFAULTcast,
                            Term.mkCast (ty, Term.DEFAULTcast, Term.mkProp)))
        else aux acc env trm
      else aux acc env trm
    and quote_recdecl (acc : 'a) env b (ns,ts,ds) =
      let ctxt = CArray.map2_i (fun i na t -> (Context.Rel.Declaration.LocalAssum (na, Vars.lift i t))) ns ts in
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
      let inst = Univ.UContext.instance mib.Declarations.mind_universes in
      let indtys =
        Array.to_list Declarations.(Array.map (fun oib ->
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
	  Declarations.((Q.quote_ident oib.mind_typename, indty, (List.rev reified_ctors)) :: ls, acc))
	  ([],acc) Declarations.((Array.to_list mib.mind_packets))
      in
      let params = Q.quote_int mib.Declarations.mind_nparams in
      Q.mkMutualInductive ref_name params (List.rev ls), acc
    in ((fun acc env -> quote_term acc (false, env)),
        (fun acc env -> quote_minductive_type acc (false, env)))

  let quote_term env trm =
    let (fn,_) = quote_term_remember (fun _ () -> ()) (fun _ () -> ()) in
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
            let open Declarations in
	    visited_terms := Names.KNset.add kn !visited_terms ;
            let c = Names.Constant.make kn kn in
	    let cd = Environ.lookup_constant c env in
	    let do_body ty body =
	      let (result,acc) =
		try quote_term acc (Global.env ()) body
                with e ->
                  Feedback.msg_debug (str"Exception raised while checking body of " ++ Names.pr_kn kn);
                  raise e
	      in
	      constants := Q.mkConstant (Q.quote_kn kn) ty result :: !constants
	    in
            let ty, acc =
              let ty =
                match cd.const_type with
	        | RegularArity ty -> ty
	        | TemplateArity (ctx,ar) ->
                   Termops.it_mkProd_or_LetIn (Constr.mkSort (Sorts.Type ar.template_level)) ctx
              in
              (try quote_term acc (Global.env ()) ty
               with e ->
                 Feedback.msg_debug (str"Exception raised while checking type of " ++ Names.pr_kn kn);
                 raise e)
            in
	    Declarations.(
	      match cd.const_body with
		Undef _ -> constants := Q.mkAxiom (Q.quote_kn kn) ty :: !constants
	      | Def cs ->
		 do_body ty (Mod_subst.force_constr cs)
	      | OpaqueDef lc ->
		 do_body ty (Opaqueproof.force_proof (Global.opaque_tables ()) lc))
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

end

module Denote =
struct

  open TemplateCoqQuoter
  
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
        Bytes.create n
      else if Term.eq_constr h tString then
	match args with
	  c :: s :: _ ->
	    let res = go (n + 1) s in
	    let _ = Bytes.set res n (unquote_char c) in
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
      Term.prop_sort
    else if Term.eq_constr h sSet then
      Term.set_sort
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

  let reduce_all env (evm,def) rd =
    let (evm2,red) = Tacinterp.interp_redexp env evm rd in
    let red = fst (Redexpr.reduction_of_red_expr env red) in
    let Sigma.Sigma (c, evm, _) = red.Reductionops.e_redfun env (Sigma.Unsafe.of_evar_map evm2) def in
    Sigma.to_evar_map evm, c

  let from_coq_pair trm =
    let (h,args) = app_full trm [] in
    if Term.eq_constr h c_pair then
      match args with
	_ :: _ :: x :: y :: [] -> (x, y)
      | _ -> bad_term trm
    else
      not_supported trm


  (** NOTE: Because the representation is lossy, I should probably
   ** come back through elaboration.
   ** - This would also allow writing terms with holes
   **)
  let rec denote_term trm =
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
	Term.mkLambda (unquote_name n, denote_term t, denote_term b)
      | _ -> raise (Failure "ill-typed (lambda)")
    else if Term.eq_constr h tLetIn then
      match args with
	n :: e :: t :: b :: _ ->
	  Term.mkLetIn (unquote_name n, denote_term e, denote_term t, denote_term b)
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
	info :: ty :: d :: brs :: _ ->
          let i, _ = from_coq_pair info in
          let ind = denote_inductive i in
          let ci = Inductiveops.make_case_info (Global.env ()) ind Term.RegularStyle in
          let denote_branch br =
            let _, br = from_coq_pair br in
            denote_term br
          in
	  Term.mkCase (ci, denote_term ty, denote_term d,
			Array.of_list (List.map denote_branch (from_coq_list brs)))
      | _ -> raise (Failure "ill-typed (case)")
    else
      not_supported trm

  let denote_local_entry trm =
    let (h,args) = app_full trm [] in
      match args with
	    x :: [] -> 
      if Term.eq_constr h tLocalDef then Entries.LocalDefEntry (denote_term x)
      else (if  Term.eq_constr h tLocalAssum then Entries.LocalAssumEntry (denote_term x) else bad_term trm)
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
      not_supported trm


  let declare_inductive (env: Environ.env) (evm: Evd.evar_map) (body: Constrexpr.constr_expr) : unit =
  let open Entries in
    let (body,_) = Constrintern.interp_constr env evm body in
  let (evm,body) = reduce_all env (evm,body)  (Genredexpr.Cbv Redops.all_flags) in
  let (_,args) = app_full body [] in (* check that the first component is Build_mut_ind .. *)
  let one_ind b1 : Entries.one_inductive_entry = 
    let (_,args) = app_full b1 [] in (* check that the first component is Build_one_ind .. *)
    match args with
    | mt::ma::mtemp::mcn::mct::[] ->
    {
    mind_entry_typename = unquote_ident mt;
    mind_entry_arity = denote_term ma;
    mind_entry_template = from_bool mtemp;
    mind_entry_consnames = List.map unquote_ident (from_coq_list mcn);
    mind_entry_lc = List.map denote_term (from_coq_list mct)
    } 
    | _ -> raise (Failure "ill-typed one_inductive_entry")
     in 
  let mut_ind mr mf mp mi mpol mpr : Entries.mutual_inductive_entry =
    {
    mind_entry_record = unquote_map_option (unquote_map_option unquote_ident) mr;
    mind_entry_finite = denote_mind_entry_finite mf; (* inductive *)
    mind_entry_params = List.map (fun p -> let (l,r) = (from_coq_pair p) in (unquote_ident l, (denote_local_entry r))) (from_coq_list mp);
    mind_entry_inds = List.map one_ind (from_coq_list mi);
    mind_entry_polymorphic = from_bool mpol;
    mind_entry_universes = Univ.UContext.empty;
    mind_entry_private = unquote_map_option from_bool mpr (*mpr*)
    } in 
    match args with
    mr::mf::mp::mi::mpol::mpr::[] -> 
      ignore(Command.declare_mutual_inductive_with_eliminations (mut_ind mr mf mp mi mpol mpr) [] [])
    | _ -> raise (Failure "ill-typed mutual_inductive_entry")

end

DECLARE PLUGIN "template_plugin"

(** Stolen from CoqPluginUtils **)
(** Calling Ltac **)
let ltac_call tac (args:Tacexpr.glob_tactic_arg list) =
  Tacexpr.TacArg(Loc.ghost,Tacexpr.TacCall(Loc.ghost, Misctypes.ArgArg(Loc.ghost, Lazy.force tac),args))

(* Calling a locally bound tactic *)
let ltac_lcall tac args =
  Tacexpr.TacArg(Loc.ghost,Tacexpr.TacCall(Loc.ghost, Misctypes.ArgVar(Loc.ghost, Names.id_of_string tac),args))

let ltac_letin (x, e1) e2 =
  Tacexpr.TacLetIn(false,[(Loc.ghost,Names.id_of_string x),e1],e2)

open Names
open Tacexpr
open Tacinterp
open Misctypes

let ltac_apply (f : Value.t) (args: Tacinterp.Value.t list) =
  let fold arg (i, vars, lfun) =
    let id = Id.of_string ("x" ^ string_of_int i) in
    let x = Reference (ArgVar (Loc.ghost, id)) in
    (succ i, x :: vars, Id.Map.add id arg lfun)
  in
  let (_, args, lfun) = List.fold_right fold args (0, [], Id.Map.empty) in
  let lfun = Id.Map.add (Id.of_string "F") f lfun in
  let ist = { (Tacinterp.default_ist ()) with Tacinterp.lfun = lfun; } in
  Tacinterp.eval_tactic_ist ist (ltac_lcall "F" args)

(* let ltac_apply (f:Tacexpr.glob_tactic_expr) (args:Tacexpr.glob_tactic_arg list) = *)
(*   Tacinterp.eval_tactic *)
(*     (ltac_letin ("F", Tacexpr.Tacexp f) (ltac_lcall "F" args)) *)

let to_ltac_val c = Tacinterp.Value.of_constr c

(** From Containers **)
let declare_definition
    (id : Names.Id.t) (loc, boxed_flag, def_obj_kind)
    (binder_list : Constrexpr.local_binder list) red_expr_opt constr_expr
    constr_expr_opt decl_hook =
  Command.do_definition
  id (loc, false, def_obj_kind) None binder_list red_expr_opt constr_expr
  constr_expr_opt decl_hook

let check_inside_section () =
  if Lib.sections_are_opened () then
    (** In trunk this seems to be moved to Errors **)
    (* For Coq 8.7: CErrors.user_err ~hdr:"Quote" (Pp.str "You can not quote within a section.") *)
    CErrors.errorlabstrm "Quote" (Pp.str "You can not quote within a section.")
  else ()

open Constrarg
open Proofview.Notations
open Pp

module TermReify = Reify(TemplateCoqQuoter)   

TACTIC EXTEND get_goal
    | [ "quote_term" constr(c) tactic(tac) ] ->
      [ (** quote the given term, pass the result to t **)
  Proofview.Goal.nf_enter { enter = begin fun gl ->
          let env = Proofview.Goal.env gl in
	  let c = TermReify.quote_term env c in
	  ltac_apply tac (List.map to_ltac_val [c])
  end } ]
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
      [ Proofview.Goal.nf_enter { enter = begin fun gl ->
         let (evm,env) = Lemmas.get_current_context() in
         let c = Denote.denote_term c in
         let def' = Constrextern.extern_constr true env evm c in
         let def = Constrintern.interp_constr env evm def' in
	 ltac_apply tac (List.map to_ltac_val [fst def])
      end } ]
END;;

VERNAC COMMAND EXTEND Make_vernac CLASSIFIED AS SIDEFF
    | [ "Quote" "Definition" ident(name) ":=" constr(def) ] ->
      [ check_inside_section () ;
	let (evm,env) = Lemmas.get_current_context () in
	let def = Constrintern.interp_constr env evm def in
	let trm = TermReify.quote_term env (fst def) in
	ignore(Declare.declare_definition ~kind:Decl_kinds.Definition name
                                          (trm, Univ.ContextSet.empty)) ]
END;;

VERNAC COMMAND EXTEND Make_vernac_reduce CLASSIFIED AS SIDEFF
    | [ "Quote" "Definition" ident(name) ":=" "Eval" red_expr(rd) "in" constr(def) ] ->
      [ check_inside_section () ;
	let (evm,env) = Lemmas.get_current_context () in
	let def, uctx = Constrintern.interp_constr env evm def in
        let evm = Evd.from_ctx uctx in
	let (evm2,def) = Denote.reduce_all env (evm, def) rd in
	let trm = TermReify.quote_term env def in
	ignore(Declare.declare_definition ~kind:Decl_kinds.Definition
                                          name (trm, Univ.ContextSet.empty)) ]
END;;


VERNAC COMMAND EXTEND Make_recursive CLASSIFIED AS SIDEFF
    | [ "Quote" "Recursively" "Definition" ident(name) ":=" constr(def) ] ->
      [ check_inside_section () ;
	let (evm,env) = Lemmas.get_current_context () in
	let def = Constrintern.interp_constr env evm def in
	let trm = TermReify.quote_term_rec env (fst def) in
	ignore(Declare.declare_definition 
	  ~kind:Decl_kinds.Definition name
	  (trm, (* No new universe constraints can be generated by typing the AST *)
           Univ.ContextSet.empty)) ]
END;;
        
VERNAC COMMAND EXTEND Unquote_vernac CLASSIFIED AS SIDEFF
    | [ "Make" "Definition" ident(name) ":=" constr(def) ] ->
      [ check_inside_section () ;
	let (evm,env) = Lemmas.get_current_context () in
	let def = Constrintern.interp_constr env evm def in
	let trm = Denote.denote_term (fst def) in
	let result = Constrextern.extern_constr true env evm trm in
	declare_definition name
	  (Decl_kinds.Global, false, Decl_kinds.Definition)
	  [] None result None (Lemmas.mk_hook (fun _ _ -> ())) ]
END;;

VERNAC COMMAND EXTEND Unquote_inductive CLASSIFIED AS SIDEFF
    | [ "Make" "Inductive" constr(def) ] ->
      [ check_inside_section () ;
	let (evm,env) = Lemmas.get_current_context () in
  Denote.declare_inductive env evm def ]
END;;

VERNAC COMMAND EXTEND Make_tests CLASSIFIED AS QUERY
(*
    | [ "Make" "Definitions" tactic(t) ] ->
      [ (** [t] returns a [list (string * term)] **)
	assert false ]
*)
    | [ "Test" "Quote" constr(c) ] ->
      [ check_inside_section () ;
	let (evm,env) = Lemmas.get_current_context () in
	let c = Constrintern.interp_constr env evm c in
	let result = TermReify.quote_term env (fst c) in
(* DEBUGGING
	let back = TermReify.denote_term result in
	Format.eprintf "%a\n" pp_constr result ;
	Format.eprintf "%a\n" pp_constr back ;
	assert (Term.eq_constr c back) ;
*)
        Feedback.msg_notice (Printer.pr_constr result) ;
	() ]
END;;
