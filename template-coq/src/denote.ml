(* open Univ
 * open Names *)
open Pp (* this adds the ++ to the current scope *)
open Names
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
         let (ind, npars, arg) = D.unquote_proj proj in
         let ind' = D.unquote_inductive ind in
         let proj_npars = D.unquote_int npars in
         let proj_arg = D.unquote_int arg in
         let l = (match List.nth (Recordops.lookup_projections ind') proj_arg with
                  | Some p -> Names.Constant.label p
                  | None -> failwith "tproj case of denote_term") in
         let p' = Names.Projection.make (Projection.Repr.make ind' ~proj_npars ~proj_arg l) false in
         let evm, t' = aux evm t in
         evm, Constr.mkProj (p', t')
      (* | _ ->  not_supported_verb trm "big_case"
       * 
       * | ACoq_tProj (proj,t) ->
       *   let (ind, _, narg) = D.unquote_proj proj in (\* todo: is narg the correct projection? *\)
       *   let ind' = D.unquote_inductive ind in
       *   let projs = Recordops.lookup_projections ind' in
       *   let evm, t = aux evm t in
       *   (match List.nth projs (D.unquote_int narg) with
       *    | Some p -> evm, Constr.mkProj (Names.Projection.make p false, t)
       *    | None -> (\*bad_term trm *\) ) *)
      | _ -> failwith "big case of denote_term"
    in aux evm trm

end

(* let get_level evm s =
 *   if CString.string_contains ~where:s ~what:"." then
 *     match List.rev (CString.split '.' s) with
 *     | [] -> CErrors.anomaly (str"Invalid universe name " ++ str s ++ str".")
 *     | n :: dp ->
 *        let num = int_of_string n in
 *        let dp = DirPath.make (List.map Id.of_string dp) in
 *        let l = Univ.Level.make dp num in
 *        try
 *          let evm = Evd.add_global_univ evm l in
 *          if !strict_unquote_universe_mode then
 *            CErrors.user_err ~hdr:"unquote_level" (str ("Level "^s^" is not a declared level and you are in Strict Unquote Universe Mode."))
 *          else (Feedback.msg_info (str"Fresh universe " ++ Level.pr l ++ str" was added to the context.");
 *                evm, l)
 *        with
 *        | UGraph.AlreadyDeclared -> evm, l
 *   else
 *     try
 *       evm, Evd.universe_of_name evm (Id.of_string s)
 *     with Not_found ->
 *          try
 *            let univ, k = Nametab.locate_universe (Libnames.qualid_of_string s) in
 *            evm, Univ.Level.make univ k
 *          with Not_found ->
 *            CErrors.user_err ~hdr:"unquote_level" (str ("Level "^s^" is not a declared level."))
 * 
 * 
 * 
 * 
 * 
 * let unquote_level evm trm (\* of type level *\) : Evd.evar_map * Univ.Level.t =
 *   let (h,args) = app_full trm [] in
 *   if Constr.equal h lProp then
 *     match args with
 *     | [] -> evm, Univ.Level.prop
 *     | _ -> bad_term_verb trm "unquote_level"
 *   else if Constr.equal h lSet then
 *     match args with
 *     | [] -> evm, Univ.Level.set
 *     | _ -> bad_term_verb trm "unquote_level"
 *   else if Constr.equal h tLevel then
 *     match args with
 *     | s :: [] -> debug (fun () -> str "Unquoting level " ++ pr_constr trm);
 *                  get_level evm (unquote_string s)
 *     | _ -> bad_term_verb trm "unquote_level"
 *   else if Constr.equal h tLevelVar then
 *     match args with
 *     | l :: [] -> evm, Univ.Level.var (unquote_nat l)
 *     | _ -> bad_term_verb trm "unquote_level"
 *   else
 *     not_supported_verb trm "unquote_level"
 * 
 * let unquote_level_expr evm trm (\* of type level *\) b (\* of type bool *\) : Evd.evar_map * Univ.Universe.t =
 *   let evm, l = unquote_level evm trm in
 *   let u = Univ.Universe.make l in
 *   evm, if unquote_bool b then Univ.Universe.super u else u
 * 
 * 
 * let unquote_universe evm trm (\* of type universe *\) =
 *   let levels = List.map unquote_pair (unquote_list trm) in
 *   match levels with
 *   | [] -> if !strict_unquote_universe_mode then
 *             CErrors.user_err ~hdr:"unquote_universe" (str "It is not possible to unquote an empty universe in Strict Unquote Universe Mode.")
 *           else
 *             let evm, u = Evd.new_univ_variable (Evd.UnivFlexible false) evm in
 *             Feedback.msg_info (str"Fresh universe " ++ Universe.pr u ++ str" was added to the context.");
 *             evm, u
 *   | (l,b)::q -> List.fold_left (fun (evm,u) (l,b) -> let evm, u' = unquote_level_expr evm l b
 *                                                      in evm, Univ.Universe.sup u u')
 *                                (unquote_level_expr evm l b) q
 * 
 * let unquote_universe_instance evm trm (\* of type universe_instance *\) =
 *   let l = unquote_list trm in
 *   let evm, l = map_evm unquote_level evm l in
 *   evm, Univ.Instance.of_array (Array.of_list l)
 * 
 * 
 * 
 * let unquote_kn (k : quoted_kernel_name) : Libnames.qualid =
 *   Libnames.qualid_of_string (clean_name (unquote_string k))
 * 
 * let unquote_proj (qp : quoted_proj) : (quoted_inductive * quoted_int * quoted_int) =
 *   let (h,args) = app_full qp [] in
 *   match args with
 *   | tyin::tynat::indpars::idx::[] ->
 *      let (h',args') = app_full indpars [] in
 *      (match args' with
 *       | tyind :: tynat :: ind :: n :: [] -> (ind, n, idx)
 *       | _ -> bad_term_verb qp "unquote_proj")
 *   | _ -> bad_term_verb qp "unquote_proj"
 * 
 * let unquote_inductive trm =
 *   let (h,args) = app_full trm [] in
 *   if Constr.equal h tmkInd then
 *     match args with
 *       nm :: num :: _ ->
 *       let s = (unquote_string nm) in
 *       let (dp, nm) = split_name s in
 *       (try
 *          match Nametab.locate (Libnames.make_qualid dp nm) with
 *          | Globnames.ConstRef c ->  CErrors.user_err (str "this not an inductive constant. use tConst instead of tInd : " ++ str s)
 *          | Globnames.IndRef i -> (fst i, unquote_nat  num)
 *          | Globnames.VarRef _ -> CErrors.user_err (str "the constant is a variable. use tVar : " ++ str s)
 *          | Globnames.ConstructRef _ -> CErrors.user_err (str "the constant is a consructor. use tConstructor : " ++ str s)
 *        with
 *          Not_found ->   CErrors.user_err (str "Constant not found : " ++ str s))
 *     | _ -> assert false
 *   else
 *     bad_term_verb trm "non-constructor"
 * 
 * 
 * 
 * (\* TODO: replace app_full by this abstract version?*\)
 * let rec app_full_abs (trm: Constr.t) (acc: Constr.t list) =
 *   match inspectTerm trm with
 *     ACoq_tApp (f, xs) -> app_full_abs f (xs @ acc)
 *   | _ -> (trm, acc)
 * 
 * 
 * let denote_term evm (trm: Constr.t) : Evd.evar_map * Constr.t =
 *   let rec aux evm (trm: Constr.t) : _ * Constr.t =
 *     debug (fun () -> Pp.(str "denote_term" ++ spc () ++ pr_constr trm)) ;
 *     match (inspectTerm trm) with
 *     | ACoq_tRel x -> evm, Constr.mkRel (unquote_nat x + 1)
 *     | ACoq_tVar x -> evm, Constr.mkVar (unquote_ident x)
 *     | ACoq_tSort x -> let evm, u = unquote_universe evm x in evm, Constr.mkType u
 *     | ACoq_tCast (t,c,ty) -> let evm, t = aux evm t in
 *                              let evm, ty = aux evm ty in
 *                              evm, Constr.mkCast (t, unquote_cast_kind c, ty)
 *     | ACoq_tProd (n,t,b) -> let evm, t = aux evm t in
 *                             let evm, b = aux evm b in
 *                             evm, Constr.mkProd (unquote_name n, t, b)
 *     | ACoq_tLambda (n,t,b) -> let evm, t = aux evm t in
 *                               let evm, b = aux evm b in
 *                               evm, Constr.mkLambda (unquote_name n, t, b)
 *     | ACoq_tLetIn (n,e,t,b) -> let evm, e = aux evm e in
 *                                let evm, t = aux evm t in
 *                                let evm, b = aux evm b in
 *                                evm, Constr.mkLetIn (unquote_name n, e, t, b)
 *     | ACoq_tApp (f,xs) -> let evm, f = aux evm f in
 *                           let evm, xs = map_evm aux evm xs in
 *                           evm, Constr.mkApp (f, Array.of_list xs)
 *     | ACoq_tConst (s,u) ->
 *        let s = unquote_kn s in
 *        let evm, u = unquote_universe_instance evm u in
 *        (try
 *           match Nametab.locate s with
 *           | Globnames.ConstRef c -> evm, Constr.mkConstU (c, u)
 *           | Globnames.IndRef _ -> CErrors.user_err (str"The constant " ++ Libnames.pr_qualid s ++ str" is an inductive, use tInd.")
 *           | Globnames.VarRef _ -> CErrors.user_err (str"The constant " ++ Libnames.pr_qualid s ++ str" is a variable, use tVar.")
 *           | Globnames.ConstructRef _ -> CErrors.user_err (str"The constant " ++ Libnames.pr_qualid s ++ str" is a constructor, use tConstructor.")
 *         with
 *           Not_found -> CErrors.user_err (str"Constant not found: " ++ Libnames.pr_qualid s))
 *     | ACoq_tConstruct (i,idx,u) ->
 *        let ind = unquote_inductive i in
 *        let evm, u = unquote_universe_instance evm u in
 *        evm, Constr.mkConstructU ((ind, unquote_nat idx + 1), u)
 *     | ACoq_tInd (i, u) ->
 *        let i = unquote_inductive i in
 *        let evm, u = unquote_universe_instance evm u in
 *        evm, Constr.mkIndU (i, u)
 *     | ACoq_tCase ((i, _), ty, d, brs) ->
 *        let ind = unquote_inductive i in
 *        let evm, ty = aux evm ty in
 *        let evm, d = aux evm d in
 *        let evm, brs = map_evm aux evm (List.map snd brs) in
 *        (\* todo: reify better case_info *\)
 *        let ci = Inductiveops.make_case_info (Global.env ()) ind Constr.RegularStyle in
 *        evm, Constr.mkCase (ci, ty, d, Array.of_list brs)
 *     | ACoq_tFix (lbd, i) ->
 *        let (names,types,bodies,rargs) = (List.map (fun p->p.adname) lbd,  List.map (fun p->p.adtype) lbd, List.map (fun p->p.adbody) lbd,
 *                                          List.map (fun p->p.rarg) lbd) in
 *        let evm, types = map_evm aux evm types in
 *        let evm, bodies = map_evm aux evm bodies in
 *        let (names,rargs) = (List.map unquote_name names, List.map unquote_nat rargs) in
 *        let la = Array.of_list in
 *        evm, Constr.mkFix ((la rargs,unquote_nat i), (la names, la types, la bodies))
 *     | ACoq_tCoFix (lbd, i) ->
 *        let (names,types,bodies,rargs) = (List.map (fun p->p.adname) lbd,  List.map (fun p->p.adtype) lbd, List.map (fun p->p.adbody) lbd,
 *                                          List.map (fun p->p.rarg) lbd) in
 *        let evm, types = map_evm aux evm types in
 *        let evm, bodies = map_evm aux evm bodies in
 *        let (names,rargs) = (List.map unquote_name names, List.map unquote_nat rargs) in
 *        let la = Array.of_list in
 *        evm, Constr.mkCoFix (unquote_nat i, (la names, la types, la bodies))
 *     | ACoq_tProj (proj,t) ->
 *        let (ind, npars, arg) = unquote_proj proj in
 *        let ind' = unquote_inductive ind in
 *        let proj_npars = unquote_nat npars in
 *        let proj_arg = unquote_nat arg in
 *        let l = (match List.nth (Recordops.lookup_projections ind') proj_arg with
 *         | Some p -> Names.Constant.label p
 *         | None -> bad_term trm) in
 *        let p' = Names.Projection.make (Projection.Repr.make ind' ~proj_npars ~proj_arg l) false in
 *        let evm, t' = aux evm t in
 *        evm, Constr.mkProj (p', t')
 *     | _ ->  not_supported_verb trm "big_case"
 *   in aux evm trm
 * 
 * 
 * 
 * let unquote_reduction_strategy env evm trm (\* of type reductionStrategy *\) : Redexpr.red_expr =
 *   let (trm, args) = app_full trm [] in
 *   (\* from g_tactic.ml4 *\)
 *   let default_flags = Redops.make_red_flag [FBeta;FMatch;FFix;FCofix;FZeta;FDeltaBut []] in
 *   if Constr.equal trm tcbv then Cbv default_flags
 *   else if Constr.equal trm tcbn then Cbn default_flags
 *   else if Constr.equal trm thnf then Hnf
 *   else if Constr.equal trm tall then Cbv all_flags
 *   else if Constr.equal trm tlazy then Lazy all_flags
 *   else if Constr.equal trm tunfold then
 *     match args with
 *     | name (\* to unfold *\) :: _ ->
 *        let name = reduce_all env evm name in
 *        let name = unquote_ident name in
 *        (try Unfold [Locus.AllOccurrences, Tacred.evaluable_of_global_reference env (Nametab.global (Libnames.qualid_of_ident name))]
 *         with
 *         | _ -> CErrors.user_err (str "Constant not found or not a constant: " ++ Pp.str (Names.Id.to_string name)))
 *     | _ -> bad_term_verb trm "unquote_reduction_strategy"
 *   else not_supported_verb trm "unquote_reduction_strategy"
 * 
 * 
 * 
 * let denote_local_entry evm trm =
 *   let (h,args) = app_full trm [] in
 *   match args with
 *     x :: [] ->
 *     if Constr.equal h tLocalDef then
 *       let evm, x = denote_term evm x in
 *       evm, Entries.LocalDefEntry x
 *     else if  Constr.equal h tLocalAssum then
 *       let evm, x = denote_term evm x in
 *       evm, Entries.LocalAssumEntry x
 *     else
 *       not_supported_verb trm "denote_local_entry"
 *   | _ -> bad_term_verb trm "denote_local_entry"
 * 
 * let denote_mind_entry_finite trm =
 *   let (h,args) = app_full trm [] in
 *   match args with
 *     [] ->
 *     if Constr.equal h cFinite then Declarations.Finite
 *     else if  Constr.equal h cCoFinite then Declarations.CoFinite
 *     else if  Constr.equal h cBiFinite then Declarations.BiFinite
 *     else not_supported_verb trm "denote_mind_entry_finite"
 *   | _ -> bad_term_verb trm "denote_mind_entry_finite"
 * 
 * 
 * 
 * let unquote_map_option f trm =
 *   let (h,args) = app_full trm [] in
 *   if Constr.equal h cSome then
 *     match args with
 *       _ :: x :: [] -> Some (f x)
 *     | _ -> bad_term trm
 *   else if Constr.equal h cNone then
 *     match args with
 *       _ :: [] -> None
 *     | _ -> bad_term trm
 *   else
 *     not_supported_verb trm "unquote_map_option"
 * 
 * let denote_option = unquote_map_option (fun x -> x)
 * 
 * 
 * 
 * let unquote_constraint_type trm (\* of type constraint_type *\) : constraint_type =
 *   let (h,args) = app_full trm [] in
 *   match args with
 *     [] ->
 *     if Constr.equal h tunivLt then Univ.Lt
 *     else if Constr.equal h tunivLe then Univ.Le
 *     else if Constr.equal h tunivEq then Univ.Eq
 *     else not_supported_verb trm "unquote_constraint_type"
 *   | _ -> bad_term_verb trm "unquote_constraint_type"
 * 
 * let unquote_univ_constraint evm c (\* of type univ_constraint *\) : _ * univ_constraint =
 *   let c, l2 = unquote_pair c in
 *   let l1, c = unquote_pair c in
 *   let evm, l1 = unquote_level evm l1 in
 *   let evm, l2 = unquote_level evm l2 in
 *   let c = unquote_constraint_type c in
 *   evm, (l1, c, l2)
 * 
 * (\* set given by MSets.MSetWeakList.Make *\)
 * let unquote_set trm =
 *   let (h, args) = app_full trm [] in
 *   (\* h supposed to be Mkt, the constructor of the record *\)
 *   match args with
 *   | list :: ok :: [] -> unquote_list list
 *   | _ -> not_supported_verb trm "unquote_set"
 * 
 * let unquote_constraints evm c (\* of type constraints *\) : _ * Constraint.t =
 *   let c = unquote_set c in
 *   List.fold_left (fun (evm, set) c -> let evm, c = unquote_univ_constraint evm c in evm, Constraint.add c set)
 *                  (evm, Constraint.empty) c 
 * 
 * 
 * let denote_variance trm (\* of type Variance *\) : Variance.t =
 *   if Constr.equal trm cIrrelevant then Variance.Irrelevant
 *   else if Constr.equal trm cCovariant then Variance.Covariant
 *   else if Constr.equal trm cInvariant then Variance.Invariant
 *   else not_supported_verb trm "denote_variance"
 * 
 * let denote_ucontext evm trm (\* of type UContext.t *\) : _ * UContext.t =
 *   let i, c = unquote_pair trm in
 *   let evm, i = unquote_universe_instance evm i in
 *   let evm, c = unquote_constraints evm c in
 *   evm, Univ.UContext.make (i, c)
 * 
 * let denote_cumulativity_info evm trm (\* of type CumulativityInfo *\) : _ * CumulativityInfo.t =
 *   let uctx, variances = unquote_pair trm in
 *   let evm, uctx = denote_ucontext evm uctx in
 *   let variances = List.map denote_variance (unquote_list variances) in
 *   evm, CumulativityInfo.make (uctx, Array.of_list variances)
 * 
 * 
 * (\* todo : stick to Coq implem *\)
 * type universe_context_type =
 *   | Monomorphic_uctx of Univ.UContext.t
 *   | Polymorphic_uctx of Univ.UContext.t
 *   | Cumulative_uctx of Univ.CumulativityInfo.t
 * 
 * let to_entry_inductive_universes = function
 *   | Monomorphic_uctx ctx -> Monomorphic_ind_entry (ContextSet.of_context ctx)
 *   | Polymorphic_uctx ctx -> Polymorphic_ind_entry ctx
 *   | Cumulative_uctx ctx -> Cumulative_ind_entry ctx
 * 
 * let denote_universe_context evm trm (\* of type universe_context *\) : _ * universe_context_type =
 *   let (h, args) = app_full trm [] in
 *   match args with
 *   | ctx :: [] -> if Constr.equal h cMonomorphic_ctx then
 *                    let evm, ctx = denote_ucontext evm ctx in
 *                    evm, Monomorphic_uctx ctx
 *                  else if Constr.equal h cPolymorphic_ctx then
 *                    let evm, ctx = denote_ucontext evm ctx in
 *                    evm, Polymorphic_uctx ctx
 *                  else if Constr.equal h cCumulative_ctx then
 *                    let evm, ctx = denote_cumulativity_info evm ctx in
 *                    evm, Cumulative_uctx ctx
 *                  else
 *                    not_supported_verb trm "denote_universe_context"
 *   | _ -> bad_term_verb trm "denote_universe_context"
 * 
 * 
 * 
 * let unquote_one_inductive_entry evm trm (\* of type one_inductive_entry *\) : _ * Entries.one_inductive_entry =
 *   let (h,args) = app_full trm [] in
 *   if Constr.equal h tBuild_one_inductive_entry then
 *     match args with
 *     | id::ar::template::cnames::ctms::[] ->
 *        let id = unquote_ident id in
 *        let evm, ar = denote_term evm ar in
 *        let template = unquote_bool template in
 *        let cnames = List.map unquote_ident (unquote_list cnames) in
 *        let evm, ctms = map_evm denote_term evm (unquote_list ctms) in
 *        evm, { mind_entry_typename = id ;
 *               mind_entry_arity = ar;
 *               mind_entry_template = template;
 *               mind_entry_consnames = cnames;
 *               mind_entry_lc = ctms }
 *     | _ -> bad_term_verb trm "unquote_one_inductive_entry"
 *   else
 *     not_supported_verb trm "unquote_one_inductive_entry"
 * 
 * let unquote_mutual_inductive_entry evm trm (\* of type mutual_inductive_entry *\) : _ * Entries.mutual_inductive_entry =
 *   let (h,args) = app_full trm [] in
 *   if Constr.equal h tBuild_mutual_inductive_entry then
 *     match args with
 *     | record::finite::params::inds::univs::priv::[] ->
 *        let record = unquote_map_option (unquote_map_option unquote_ident) record in
 *        let finite = denote_mind_entry_finite finite in
 *        let evm, params = map_evm (fun evm p -> let (l,r) = unquote_pair p in
 *                                                let evm, e = denote_local_entry evm r in
 *                                                evm, (unquote_ident l, e))
 *                                  evm (unquote_list params) in
 *        let evm, inds = map_evm unquote_one_inductive_entry evm (unquote_list inds) in
 *        let evm, univs = denote_universe_context evm univs in
 *        let priv = unquote_map_option unquote_bool priv in
 *        evm, { mind_entry_record = None; (\* record TODO TODO *\)
 *               mind_entry_finite = finite;
 *               mind_entry_params = params;
 *               mind_entry_inds = inds;
 *               mind_entry_universes = to_entry_inductive_universes univs;
 *               mind_entry_private = priv }
 *     | _ -> bad_term_verb trm "unquote_mutual_inductive_entry"
 *   else
 *     not_supported_verb trm "unquote_mutual_inductive_entry"
 * 
 * 
 * let declare_inductive (env: Environ.env) (evm: Evd.evar_map) (mind: Constr.t) : unit =
 *   let mind = reduce_all env evm mind in
 *   debug (fun () -> str"declare_inductive: " ++ pr_constr mind);
 *   let evm, mind = unquote_mutual_inductive_entry evm mind in
 *   ignore (ComInductive.declare_mutual_inductive_with_eliminations mind Names.Id.Map.empty [])
 * 
 * let not_in_tactic s =
 *   CErrors.user_err  (str ("You can not use " ^ s ^ " in a tactic."))
 * 
 * let monad_failure_full s k prg =
 *   CErrors.user_err
 *     (str (s ^ " must take " ^ (string_of_int k) ^ " argument" ^ (if k > 0 then "s" else "") ^ ".") ++
 *        str "While trying to run: " ++ fnl () ++ print_term prg ++ fnl () ++
 *        str "Please file a bug with Template-Coq.")
 * 
 * let rec run_template_program_rec ?(intactic=false) (k : Environ.env * Evd.evar_map * Constr.t -> unit) env ((evm, pgm) : Evd.evar_map * Constr.t) : unit =
 *   let open TemplateMonad in
 *   let (kind, universes) = next_action env pgm in
 *   match kind with
 *     TmReturn h -> k (env, evm, h)
 *   | TmBind (a,f) ->
 *     run_template_program_rec ~intactic:intactic (fun (env, evm, ar) -> run_template_program_rec ~intactic:intactic k env (evm, Constr.mkApp (f, [|ar|]))) env (evm, a)
 *   | TmDefinition (name,s,typ,body) ->
 *     let name = reduce_all env evm name in
 *     let evm, typ = (match denote_option s with Some s -> let red = unquote_reduction_strategy env evm s in reduce env evm red typ | None -> evm, typ) in
 *     let univs =
 *       if Flags.is_universe_polymorphism () then Polymorphic_const_entry (Evd.to_universe_context evm)
 *       else Monomorphic_const_entry (Evd.universe_context_set evm) in
 *     let n = Declare.declare_definition ~kind:Decl_kinds.Definition (unquote_ident name) ~types:typ (body, univs) in
 *     let env = Global.env () in
 *     k (env, evm, Constr.mkConst n)
 *   | TmAxiom (name,s,typ) ->
 *     let name = reduce_all env evm name in
 *     let evm, typ = (match denote_option s with Some s -> let red = unquote_reduction_strategy env evm s in reduce env evm red typ | None -> evm, typ) in
 *     let param = Entries.ParameterEntry (None, (typ, Monomorphic_const_entry (Evd.universe_context_set evm)), None) in
 *     let n = Declare.declare_constant (unquote_ident name) (param, Decl_kinds.IsDefinition Decl_kinds.Definition) in
 *     let env = Global.env () in
 *     k (env, evm, Constr.mkConst n)
 *   | TmLemma (name,s,typ) ->
 *     let name = reduce_all env evm name in
 *     let evm, typ = (match denote_option s with Some s -> let red = unquote_reduction_strategy env evm s in reduce env evm red typ | None -> evm, typ) in
 *     let poly = Flags.is_universe_polymorphism () in
 *     let kind = (Decl_kinds.Global, poly, Decl_kinds.Definition) in
 *     let hole = CAst.make (Constrexpr.CHole (None, Misctypes.IntroAnonymous, None)) in
 *     let evm, (c, _) = Constrintern.interp_casted_constr_evars_impls env evm hole (EConstr.of_constr typ) in
 *     let ident = unquote_ident name in
 *     Obligations.check_evars env evm;
 *        let obls, _, c, cty = Obligations.eterm_obligations env ident evm 0 (EConstr.to_constr evm c) typ in
 *        (\* let evm = Evd.minimize_universes evm in *\)
 *        let ctx = Evd.evar_universe_context evm in
 *        let hook = Lemmas.mk_hook (fun _ gr _ -> let env = Global.env () in
 *                                                 let evm = Evd.from_env env in
 *                                                 let evm, t = Evd.fresh_global env evm gr in k (env, evm, EConstr.to_constr evm t)) in
 *        ignore (Obligations.add_definition ident ~term:c cty ctx ~kind ~hook obls)
 *     (\* let kind = Decl_kinds.(Global, Flags.use_polymorphic_flag (), DefinitionBody Definition) in *\)
 *     (\* Lemmas.start_proof (unquote_ident name) kind evm (EConstr.of_constr typ) *\)
 *     (\* (Lemmas.mk_hook (fun _ gr -> *\)
 *     (\* let evm, t = Evd.fresh_global env evm gr in k (env, evm, t) *\)
 *     (\* k (env, evm, unit_tt) *\)
 *     (\* )); *\)
 *   | TmMkDefinition (name, body) ->
 *     let name = reduce_all env evm name in
 *     let body = reduce_all env evm body in
 *     let evm, trm = denote_term evm body in
 *     let (evm, _) = Typing.type_of env evm (EConstr.of_constr trm) in
 *     let _ = Declare.declare_definition ~kind:Decl_kinds.Definition (unquote_ident name) (trm, Monomorphic_const_entry (Evd.universe_context_set evm)) in
 *     let env = Global.env () in
 *     k (env, evm, unit_tt)
 *   | TmQuote trm ->
 *     let qt = TermReify.quote_term env trm (\* user should do the reduction (using tmEval) if they want *\)
 *     in k (env, evm, qt)
 *   | TmQuoteRec trm ->
 *     let qt = TermReify.quote_term_rec env trm in
 *     k (env, evm, qt)
 *   | TmQuoteInd name ->
 *        let name = reduce_all env evm name in
 *        let name = unquote_string name in
 *        let (dp, nm) = split_name name in
 *        (match Nametab.locate (Libnames.make_qualid dp nm) with
 *         | Globnames.IndRef ni ->
 *            let t = TermReify.quote_mind_decl env (fst ni) in
 *            let _, args = Constr.destApp t in
 *            (match args with
 *             | [|kn; decl|] ->
 *                k (env, evm, decl)
 *             | _ -> bad_term_verb t "anomaly in quoting of inductive types")
 *         (\* quote_mut_ind produce an entry rather than a decl *\)
 *         (\* let c = Environ.lookup_mind (fst ni) env in (\\* FIX: For efficienctly, we should also export (snd ni)*\\) *\)
 *         (\* TermReify.quote_mut_ind env c *\)
 *         | _ -> CErrors.user_err (str name ++ str " does not seem to be an inductive."))
 *   | TmQuoteConst (name,bypass) ->
 *        let name = reduce_all env evm name in
 *        let name = unquote_string name in
 *        let bypass = reduce_all env evm bypass in
 *        let bypass = unquote_bool bypass in
 *        let entry = TermReify.quote_entry_aux bypass env evm name in
 *        let entry =
 *          match entry with
 *          | Some (Left cstentry) -> TemplateCoqQuoter.quote_constant_entry cstentry
 *          | Some (Right _) -> CErrors.user_err (str name ++ str " refers to an inductive")
 *          | None -> bad_term_verb pgm "anomaly in QuoteConstant"
 *        in
 *        k (env, evm, entry)
 *   | TmQuoteUnivs ->
 *     let univs = Environ.universes env in
 *     k (env, evm, quote_ugraph univs)
 *   | TmPrint trm -> Feedback.msg_info (pr_constr trm);
 *     k (env, evm, unit_tt)
 *   | TmFail trm ->
 *     CErrors.user_err (str (unquote_string trm))
 *   | TmAbout id ->
 *     begin
 *       let id = unquote_string id in
 *       try
 *         let gr = Smartlocate.locate_global_with_alias (Libnames.qualid_of_string id) in
 *         let opt = Constr.mkApp (cSome , [|tglobal_reference ; quote_global_reference gr|]) in
 *         k (env, evm, opt)
 *       with
 *       | Not_found -> k (env, evm, Constr.mkApp (cNone, [|tglobal_reference|]))
 *     end
 *   | TmCurrentModPath ->
 *     let mp = Lib.current_mp () in
 *     (\* let dp' = Lib.cwd () in (\* different on sections ? *\) *\)
 *     let s = quote_string (Names.ModPath.to_string mp) in
 *     k (env, evm, s)
 *   | TmEval (s, trm) ->
 *     let red = unquote_reduction_strategy env evm s in
 *     let (evm, trm) = reduce env evm red trm
 *     in k (env, evm, trm)
 *   | TmMkInductive mind ->
 *     declare_inductive env evm mind;
 *     let env = Global.env () in
 *     k (env, evm, unit_tt)
 *   | TmUnquote t ->
 *        (try
 *          let t = reduce_all env evm t in
 *          let evm, t' = denote_term evm t in
 *          let typ = Retyping.get_type_of env evm (EConstr.of_constr t') in
 *          let evm, typ = Evarsolve.refresh_universes (Some false) env evm typ in
 *          let make_typed_term typ term evm =
 *            match texistT_typed_term with
 *            | ConstructRef ctor ->
 *              let u = (Univ.Instance.to_array universes).(1) in
 *              let term = Constr.mkApp
 *                (Constr.mkConstructU (ctor, Univ.Instance.of_array [|u|]), [|typ; t'|]) in
 *              let evm, _ = Typing.type_of env evm (EConstr.of_constr term) in
 *                (env, evm, term)
 *            | _ -> anomaly (str "texistT_typed_term does not refer to a constructor")
 *          in
 *            k (make_typed_term (EConstr.to_constr evm typ) t' evm)
 *         with Reduction.NotArity -> CErrors.user_err (str "unquoting ill-typed term"))
 *   | TmUnquoteTyped (typ, t) ->
 *        let t = reduce_all env evm t in
 *        let evm, t' = denote_term evm t in
 *        let evdref = ref evm in
 *        (\* let t' = Typing.e_solve_evars env evdref (EConstr.of_constr t') in *\)
 *        Feedback.msg_debug (Printer.pr_constr typ);
 *        Typing.e_check env evdref (EConstr.of_constr t') (EConstr.of_constr typ);
 *        let evm = !evdref in
 *        k (env, evm, t')
 *   | TmFreshName name ->
 *     let name' = Namegen.next_ident_away_from (unquote_ident name) (fun id -> Nametab.exists_cci (Lib.make_path id)) in
 *     k (env, evm, quote_ident name')
 *   | TmExistingInstance name ->
 *      Classes.existing_instance true (Libnames.qualid_of_ident (unquote_ident name)) None
 *   | TmInferInstance (s, typ) ->
 *        let evm, typ = (match denote_option s with Some s -> let red = unquote_reduction_strategy env evm s in reduce env evm red typ | None -> evm, typ) in
 *        (try
 *           let (evm,t) = Typeclasses.resolve_one_typeclass env evm (EConstr.of_constr typ) in
 *           k (env, evm, Constr.mkApp (cSome, [| typ; EConstr.to_constr evm t|]))
 *         with
 *           Not_found -> k (env, evm, Constr.mkApp (cNone, [|typ|]))
 *        ) *)
