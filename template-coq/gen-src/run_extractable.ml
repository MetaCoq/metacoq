open Extractable
open Plugin_core
open Ast0
open BasicAst


let of_constr (t : Constr.t) : Ast0.term =
  failwith "of_constr"

let to_string (cl : char list) : string =
  failwith "to_string"

let of_string (s : string) : char list =
  failwith "of_string"

let to_reduction_strategy (s : Common.reductionStrategy) =
  failwith "to_reduction_strategy"

let to_ident : char list -> Names.Id.t =
  failwith "to_ident"

let of_ident : Names.Id.t -> char list =
  failwith "of_ident"

let of_global_reference (t : Plugin_core.global_reference) : BasicAst.global_reference =
  failwith "of_global_reference"

let to_qualid (c : char list) : Libnames.qualid =
  Libnames.qualid_of_string (to_string c)

let of_qualid (q : Libnames.qualid) : char list =
  of_string (Libnames.string_of_qualid q)

let of_kername : Names.KerName.t -> char list =
  failwith "of_kername"

let to_kername : char list -> Names.KerName.t =
  failwith "of_kername"

let of_mib : Plugin_core.mutual_inductive_body -> _ =
  failwith "of_mib"

let to_mie : _ -> Plugin_core.mutual_inductive_entry =
  failwith "to_mie"

let of_constant_entry : _ -> Ast0.constant_entry =
  failwith "of_constant_entry"

(* what about the overflow?
  efficiency? extract to bigint using Coq directives and convert to int here? *)
let of_nat (t : Datatypes.nat) : int =
  failwith "of_constr"

let of_cast_kind (ck: BasicAst.cast_kind) : Constr.cast_kind =
  match ck with
  | VmCast -> Constr.VMcast
  | NativeCast -> Constr.VMcast
  | Cast -> Constr.DEFAULTcast
  | RevertCast -> Constr.REVERTcast


  (* todo(gmm): determine what of these already exist. *)
let rec to_constr_ev (evm : Evd.evar_map) (t : Ast0.term) : Evd.evar_map * Constr.t =
  match t with
  | Coq_tRel x -> evm, Constr.mkRel (of_nat x + 1)
  | Coq_tVar x -> evm, Constr.mkVar (to_ident x)
  | Coq_tCast (t,c,ty) -> let evm, t = to_constr_ev evm t in
    let evm, ty = to_constr_ev evm ty in
    evm, Constr.mkCast (t, of_cast_kind c, ty)
  (* the next case is quite complex: look at Denote.unquote_universe *)
  | Coq_tSort u -> evm, Constr.mkType u
  | Coq_tProd (n,t,b) -> let evm, t = aux evm t in
    let evm, b = aux evm b in
    evm, Constr.mkProd (unquote_name n, t, b)
  | Coq_tLambda (n,t,b) -> let evm, t = aux evm t in
    let evm, b = aux evm b in
    evm, Constr.mkLambda (unquote_name n, t, b)
  | Coq_tLetIn (n,e,t,b) -> let evm, e = aux evm e in
    let evm, t = aux evm t in
    let evm, b = aux evm b in
    evm, Constr.mkLetIn (unquote_name n, e, t, b)
  | Coq_tApp (f,xs) -> let evm, f = aux evm f in
    let evm, xs = map_evm aux evm xs in
    evm, Constr.mkApp (f, Array.of_list xs)
  | Coq_tConst (s,u) ->
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
  | Coq_tConstruct (i,idx,u) ->
    let ind = unquote_inductive i in
    let evm, u = unquote_universe_instance evm u in
    evm, Constr.mkConstructU ((ind, unquote_nat idx + 1), u)
  | Coq_tInd (i, u) ->
    let i = unquote_inductive i in
    let evm, u = unquote_universe_instance evm u in
    evm, Constr.mkIndU (i, u)
  | Coq_tCase ((i, _), ty, d, brs) ->
    let ind = unquote_inductive i in
    let evm, ty = aux evm ty in
    let evm, d = aux evm d in
    let evm, brs = map_evm aux evm (List.map snd brs) in
    (* todo: reify better case_info *)
    let ci = Inductiveops.make_case_info (Global.env ()) ind Constr.RegularStyle in
    evm, Constr.mkCase (ci, ty, d, Array.of_list brs)
  | Coq_tFix (lbd, i) ->
    let (names,types,bodies,rargs) = (List.map (fun p->p.adname) lbd,  List.map (fun p->p.adtype) lbd, List.map (fun p->p.adbody) lbd,
                                      List.map (fun p->p.rarg) lbd) in
    let evm, types = map_evm aux evm types in
    let evm, bodies = map_evm aux evm bodies in
    let (names,rargs) = (List.map unquote_name names, List.map unquote_nat rargs) in
    let la = Array.of_list in
    evm, Constr.mkFix ((la rargs,unquote_nat i), (la names, la types, la bodies))
  | Coq_tCoFix (lbd, i) ->
    let (names,types,bodies,rargs) = (List.map (fun p->p.adname) lbd,  List.map (fun p->p.adtype) lbd, List.map (fun p->p.adbody) lbd,
                                      List.map (fun p->p.rarg) lbd) in
    let evm, types = map_evm aux evm types in
    let evm, bodies = map_evm aux evm bodies in
    let (names,rargs) = (List.map unquote_name names, List.map unquote_nat rargs) in
    let la = Array.of_list in
    evm, Constr.mkCoFix (unquote_nat i, (la names, la types, la bodies))
  | Coq_tProj (proj,t) ->
    let (ind, _, narg) = unquote_proj proj in (* todo: is narg the correct projection? *)
    let ind' = unquote_inductive ind in
    let projs = Recordops.lookup_projections ind' in
    let evm, t = aux evm t in
    (match List.nth projs (unquote_nat narg) with
     | Some p -> evm, Constr.mkProj (Names.Projection.make p false, t)
     | None -> bad_term trm)
  | _ ->  not_supported_verb trm "big_case"

let to_constr (t : Ast0.term) : Constr.t =
  snd (to_constr_ev Evd.empty t)


let rec interp_tm (t : 'a coq_TM) : 'a tm =
  match t with
  | Coq_tmReturn x -> tmReturn x
  | Coq_tmBind (c, k) -> tmBind (interp_tm c) (fun x -> interp_tm (k x))
  | Coq_tmPrint t -> Obj.magic (tmPrint (to_constr t))
  | Coq_tmMsg msg -> Obj.magic (tmMsg (to_string msg))
  | Coq_tmFail err -> tmFail (to_string err)
  | Coq_tmEval (r,t) ->
    tmMap (fun x -> Obj.magic (of_constr x))
          (tmEval (to_reduction_strategy r) (to_constr t))
  | Coq_tmDefinition (nm, typ, trm) ->
    let typ =
      match typ with
        None -> None
      | Some typ -> Some (to_constr typ)
    in
    tmMap (fun x -> Obj.magic (of_kername x))
          (tmDefinition (to_ident nm) typ (to_constr trm))
  | Coq_tmAxiom (nm, typ) ->
    tmMap (fun x -> Obj.magic (of_kername x))
          (tmAxiom (to_ident nm) (to_constr typ))
  | Coq_tmLemma (nm, typ) ->
    tmMap (fun x -> Obj.magic (of_kername x))
          (tmLemma (to_ident nm) (to_constr typ))
  | Coq_tmFreshName nm ->
    tmMap (fun x -> Obj.magic (of_ident x))
          (tmFreshName (to_ident nm))
  | Coq_tmAbout id ->
    tmMap (function
             None -> Obj.magic None
           | Some gr -> Obj.magic (Some (of_global_reference gr)))
          (tmAbout (to_qualid id))
  | Coq_tmCurrentModPath ->
    tmMap (fun mp -> Obj.magic (of_string (Names.ModPath.to_string mp)))
          tmCurrentModPath
  | Coq_tmQuoteInductive kn ->
    tmMap (function
             None -> Obj.magic None
           | Some mib -> Obj.magic (Some (of_mib mib)))
          (tmQuoteInductive (to_kername kn))
  | Coq_tmQuoteUniverses ->
    tmMap (fun x -> failwith "tmQuoteUniverses") tmQuoteUniverses
  | Coq_tmQuoteConstant (kn, b) ->
    tmMap (fun x -> Obj.magic (of_constant_entry x))
          (tmQuoteConstant (to_kername kn) b)
  | Coq_tmInductive i ->
    tmMap (fun _ -> Obj.magic ()) (tmInductive (to_mie i))
  | Coq_tmExistingInstance k ->
    Obj.magic (tmExistingInstance (to_kername k))
  | Coq_tmInferInstance t ->
    tmMap (function
             None -> Obj.magic None
           | Some inst -> Obj.magic (Some (of_constr inst)))
          (tmInferInstance (to_constr t))
