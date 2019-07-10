(* open Univ
 * open Names *)
open Pp (* this adds the ++ to the current scope *)

open Quoted
open Denoter

(* todo: the recursive call is uneeded provided we call it on well formed terms *)

let strict_unquote_universe_mode = ref true

let map_evm (f : 'a -> 'b -> 'a * 'c) (evm : 'a) (l : 'b list) : 'a * ('c list) =
  let evm, res = List.fold_left (fun (evm, l) b -> let evm, c = f evm b in evm, c :: l) (evm, []) l in
  evm, List.rev res


module Denote (D : Denoter) =
struct

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
