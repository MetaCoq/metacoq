open BasicAst
open Datatypes
open EAst
open ETyping
open Extract
open List0
open MCProd

(** val optimize : E.global_context -> E.term -> E.term **)

let rec optimize _UU03a3_ t = match t with
| E.Coq_tRel i -> E.Coq_tRel i
| E.Coq_tEvar (ev, args) -> E.Coq_tEvar (ev, (map (optimize _UU03a3_) args))
| E.Coq_tLambda (na, m) -> E.Coq_tLambda (na, (optimize _UU03a3_ m))
| E.Coq_tLetIn (na, b, b') ->
  E.Coq_tLetIn (na, (optimize _UU03a3_ b), (optimize _UU03a3_ b'))
| E.Coq_tApp (u, v) ->
  E.Coq_tApp ((optimize _UU03a3_ u), (optimize _UU03a3_ v))
| E.Coq_tCase (ind, c, brs) ->
  let brs' = map (on_snd (optimize _UU03a3_)) brs in
  (match is_propositional _UU03a3_ (fst ind) with
   | Some b ->
     if b
     then (match brs' with
           | [] -> E.Coq_tCase (ind, (optimize _UU03a3_ c), brs')
           | p :: l ->
             let (a, b0) = p in
             (match l with
              | [] -> E.mkApps b0 (repeat E.Coq_tBox a)
              | _ :: _ -> E.Coq_tCase (ind, (optimize _UU03a3_ c), brs')))
     else E.Coq_tCase (ind, (optimize _UU03a3_ c), brs')
   | None -> E.Coq_tCase (ind, (optimize _UU03a3_ c), brs'))
| E.Coq_tProj (p, c) ->
  (match is_propositional _UU03a3_ (fst (fst p)) with
   | Some b ->
     if b then E.Coq_tBox else E.Coq_tProj (p, (optimize _UU03a3_ c))
   | None -> E.Coq_tProj (p, (optimize _UU03a3_ c)))
| E.Coq_tFix (mfix, idx) ->
  let mfix' = map (E.map_def (optimize _UU03a3_)) mfix in
  E.Coq_tFix (mfix', idx)
| E.Coq_tCoFix (mfix, idx) ->
  let mfix' = map (E.map_def (optimize _UU03a3_)) mfix in
  E.Coq_tCoFix (mfix', idx)
| _ -> t

(** val optimize_constant_decl :
    E.global_context -> E.constant_body -> E.constant_body **)

let optimize_constant_decl _UU03a3_ cb =
  option_map (optimize _UU03a3_) (E.cst_body cb)

(** val optimize_decl : E.global_context -> E.global_decl -> E.global_decl **)

let optimize_decl _UU03a3_ d = match d with
| E.ConstantDecl cb -> E.ConstantDecl (optimize_constant_decl _UU03a3_ cb)
| E.InductiveDecl _ -> d

(** val optimize_env :
    global_declarations -> (kername * E.global_decl) list **)

let optimize_env _UU03a3_ =
  map (on_snd (optimize_decl _UU03a3_)) _UU03a3_
