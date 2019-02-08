     | ACoq_tProj (proj,t) ->
         let (ind, npars, arg) = unquote_proj proj in
         let ind' = unquote_inductive ind in
         let proj_npars = unquote_nat npars in
         let proj_arg = unquote_nat arg in
         let l = (match List.nth (Recordops.lookup_projections ind') proj_arg with
          | Some p -> Names.Constant.label p
          | None -> bad_term trm) in
         let p' = Names.Projection.make (Projection.Repr.make ind' ~proj_npars ~proj_arg l) false in
         let evm, t' = aux evm t in
         evm, Constr.mkProj (p', t')
      | _ ->  not_supported_verb trm "big_case"
 
