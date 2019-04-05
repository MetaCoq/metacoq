open Extractable
open Plugin_core

(* todo(gmm): determine what of these already exist. *)
let to_constr (t : Ast0.term) : Constr.t =
  failwith "to_constr"

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

let of_global_reference (t : global_reference) : BasicAst.global_reference =
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
