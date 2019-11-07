open AstUtils
open BasicAst
open Datatypes
open List0
open Nat0
open PCUICAst
open PCUICAstUtils
open PCUICChecker
open PCUICLiftSubst
open Pretty
open String0
open Utils

(** val print_defs :
    (context -> bool -> bool -> term -> char list) -> context -> term
    mfixpoint -> char list **)

let print_defs print_term0 _UU0393_ defs =
  let ctx' = PCUICLiftSubst.fix_context defs in
  print_list
    (print_def (print_term0 _UU0393_ true false)
      (print_term0 (app ctx' _UU0393_) true false))
    (append nl (' '::('w'::('i'::('t'::('h'::(' '::[]))))))) defs

(** val is_fresh : context -> ident -> bool **)

let is_fresh _UU0393_ id =
  forallb (fun decl ->
    match decl.decl_name with
    | Coq_nAnon -> true
    | Coq_nNamed id' -> negb (ident_eq id id')) _UU0393_

(** val name_from_term : global_env_ext -> term -> char list **)

let rec name_from_term _UU03a3_ = function
| Coq_tRel _ -> 'H'::[]
| Coq_tVar _ -> 'H'::[]
| Coq_tEvar (_, _) -> 'H'::[]
| Coq_tSort _ -> 'X'::[]
| Coq_tProd (_, _, _) -> 'f'::[]
| Coq_tLambda (_, _, _) -> 'f'::[]
| Coq_tLetIn (_, _, _, t') -> name_from_term _UU03a3_ t'
| Coq_tApp (f, _) -> name_from_term _UU03a3_ f
| Coq_tConst (_, _) -> 'x'::[]
| Coq_tInd (ind, _) ->
  let { inductive_mind = i; inductive_ind = k } = ind in
  (match PCUICChecker.lookup_ind_decl (fst_ctx _UU03a3_) i k with
   | Checked a -> let (_, body) = a in substring O (S O) body.ind_name
   | TypeError _ -> 'X'::[])
| _ -> 'U'::[]

(** val fresh_id_from : context -> nat -> char list -> char list **)

let fresh_id_from _UU0393_ n id =
  let rec aux i = match i with
  | O -> id
  | S i' ->
    let id' = append id (string_of_nat (sub n i)) in
    if is_fresh _UU0393_ id' then id' else aux i'
  in aux n

(** val fresh_name : global_env_ext -> context -> name -> term -> name **)

let fresh_name _UU03a3_ _UU0393_ na t =
  let id =
    match na with
    | Coq_nAnon -> name_from_term _UU03a3_ t
    | Coq_nNamed id -> id
  in
  if is_fresh _UU0393_ id
  then Coq_nNamed id
  else Coq_nNamed
         (fresh_id_from _UU0393_ (S (S (S (S (S (S (S (S (S (S O)))))))))) id)

(** val print_term :
    global_env_ext -> context -> bool -> bool -> term -> char list **)

let rec print_term _UU03a3_ _UU0393_ top inapp = function
| Coq_tRel n ->
  (match nth_error _UU0393_ n with
   | Some c ->
     let { decl_name = na; decl_body = _; decl_type = _ } = c in
     (match na with
      | Coq_nAnon ->
        append
          ('A'::('n'::('o'::('n'::('y'::('m'::('o'::('u'::('s'::(' '::('('::[])))))))))))
          (append (string_of_nat n) (')'::[]))
      | Coq_nNamed id -> id)
   | None ->
     append
       ('U'::('n'::('b'::('o'::('u'::('n'::('d'::('R'::('e'::('l'::('('::[])))))))))))
       (append (string_of_nat n) (')'::[])))
| Coq_tVar n -> append ('V'::('a'::('r'::('('::[])))) (append n (')'::[]))
| Coq_tEvar (ev, _) ->
  append ('E'::('v'::('a'::('r'::('('::[])))))
    (append (string_of_nat ev) (append ('['::(']'::[])) (')'::[])))
| Coq_tSort s -> string_of_sort s
| Coq_tProd (na, dom, codom) ->
  let na' = fresh_name _UU03a3_ _UU0393_ na dom in
  parens top
    (append ('\226'::('\136'::('\128'::(' '::[]))))
      (append (string_of_name na')
        (append (' '::(':'::(' '::[])))
          (append (print_term _UU03a3_ _UU0393_ true false dom)
            (append (','::(' '::[]))
              (print_term _UU03a3_ ((vass na' dom) :: _UU0393_) true false
                codom))))))
| Coq_tLambda (na, dom, body) ->
  let na' = fresh_name _UU03a3_ _UU0393_ na dom in
  parens top
    (append ('f'::('u'::('n'::(' '::[]))))
      (append (string_of_name na')
        (append (' '::(':'::(' '::[])))
          (append (print_term _UU03a3_ _UU0393_ true false dom)
            (append (' '::('='::('>'::(' '::[]))))
              (print_term _UU03a3_ ((vass na' dom) :: _UU0393_) true false
                body))))))
| Coq_tLetIn (na, def, dom, body) ->
  let na' = fresh_name _UU03a3_ _UU0393_ na dom in
  parens top
    (append ('l'::('e'::('t'::[])))
      (append (string_of_name na')
        (append (' '::(':'::(' '::[])))
          (append (print_term _UU03a3_ _UU0393_ true false dom)
            (append (' '::(':'::('='::(' '::[]))))
              (append (print_term _UU03a3_ _UU0393_ true false def)
                (append (' '::('i'::('n'::(' '::[]))))
                  (append nl
                    (print_term _UU03a3_ ((vdef na' def dom) :: _UU0393_)
                      true false body)))))))))
| Coq_tApp (f, l) ->
  parens ((||) top inapp)
    (append (print_term _UU03a3_ _UU0393_ false true f)
      (append (' '::[]) (print_term _UU03a3_ _UU0393_ false false l)))
| Coq_tConst (c, u) -> append c (print_universe_instance u)
| Coq_tInd (ind, u) ->
  let { inductive_mind = i; inductive_ind = k } = ind in
  (match PCUICChecker.lookup_ind_decl (fst_ctx _UU03a3_) i k with
   | Checked a ->
     let (_, oib) = a in append oib.ind_name (print_universe_instance u)
   | TypeError _ ->
     append
       ('U'::('n'::('b'::('o'::('u'::('n'::('d'::('I'::('n'::('d'::('('::[])))))))))))
       (append
         (string_of_inductive { inductive_mind = i; inductive_ind = k })
         (append (','::[]) (append (string_of_universe_instance u) (')'::[])))))
| Coq_tConstruct (ind, l, u) ->
  let { inductive_mind = i; inductive_ind = k } = ind in
  (match PCUICChecker.lookup_ind_decl (fst_ctx _UU03a3_) i k with
   | Checked a ->
     let (_, oib) = a in
     (match nth_error oib.ind_ctors l with
      | Some p ->
        let (p0, _) = p in
        let (na, _) = p0 in append na (print_universe_instance u)
      | None ->
        append
          ('U'::('n'::('b'::('o'::('u'::('n'::('d'::('C'::('o'::('n'::('s'::('t'::('r'::('u'::('c'::('t'::('('::[])))))))))))))))))
          (append (string_of_inductive ind)
            (append (','::[])
              (append (string_of_nat l)
                (append (','::[])
                  (append (string_of_universe_instance u) (')'::[])))))))
   | TypeError _ ->
     append
       ('U'::('n'::('b'::('o'::('u'::('n'::('d'::('C'::('o'::('n'::('s'::('t'::('r'::('u'::('c'::('t'::('('::[])))))))))))))))))
       (append (string_of_inductive ind)
         (append (','::[])
           (append (string_of_nat l)
             (append (','::[])
               (append (string_of_universe_instance u) (')'::[])))))))
| Coq_tCase (indn, p, t0, brs) ->
  let (ind, _) = indn in
  let { inductive_mind = mind; inductive_ind = i } = ind in
  (match PCUICChecker.lookup_ind_decl (fst_ctx _UU03a3_) mind i with
   | Checked a ->
     let (_, oib) = a in
     (match p with
      | Coq_tLambda (na, _, b) ->
        let print_branch =
          let rec print_branch _UU0393_0 arity br =
            match arity with
            | O ->
              append ('='::('>'::(' '::[])))
                (print_term _UU03a3_ _UU0393_0 true false br)
            | S n ->
              (match br with
               | Coq_tLambda (na0, a0, b0) ->
                 let na' = fresh_name _UU03a3_ _UU0393_0 na0 a0 in
                 append (string_of_name na')
                   (append (' '::(' '::[]))
                     (print_branch ((vass na' a0) :: _UU0393_0) n b0))
               | _ ->
                 append ('='::('>'::(' '::[])))
                   (print_term _UU03a3_ _UU0393_0 true false br))
          in print_branch
        in
        let brs0 =
          map (fun pat ->
            let (arity, br) = pat in print_branch _UU0393_ arity br) brs
        in
        let brs1 = combine brs0 oib.ind_ctors in
        parens top
          (append ('m'::('a'::('t'::('c'::('h'::(' '::[]))))))
            (append (print_term _UU03a3_ _UU0393_ true false t0)
              (append (' '::('a'::('s'::(' '::[]))))
                (append (string_of_name na)
                  (append (' '::('i'::('n'::(' '::[]))))
                    (append oib.ind_name
                      (append
                        (' '::('r'::('e'::('t'::('u'::('r'::('n'::(' '::[]))))))))
                        (append (print_term _UU03a3_ _UU0393_ true false b)
                          (append
                            (' '::('w'::('i'::('t'::('h'::(' '::[]))))))
                            (append nl
                              (append
                                (print_list (fun pat ->
                                  let (b0, y) = pat in
                                  let (y0, _) = y in
                                  let (na0, _) = y0 in
                                  append na0 (append (' '::[]) b0))
                                  (append nl (' '::('|'::(' '::[])))) brs1)
                                (append nl
                                  (append ('e'::('n'::('d'::[]))) nl)))))))))))))
      | _ ->
        append ('C'::('a'::('s'::('e'::('('::[])))))
          (append (string_of_inductive ind)
            (append (','::[])
              (append (string_of_nat i)
                (append (','::[])
                  (append (string_of_term t0)
                    (append (','::[])
                      (append (string_of_term p)
                        (append (','::[])
                          (append
                            (string_of_list (fun b -> string_of_term (snd b))
                              brs) (')'::[])))))))))))
   | TypeError _ ->
     append ('C'::('a'::('s'::('e'::('('::[])))))
       (append (string_of_inductive ind)
         (append (','::[])
           (append (string_of_nat i)
             (append (','::[])
               (append (string_of_term t0)
                 (append (','::[])
                   (append (string_of_term p)
                     (append (','::[])
                       (append
                         (string_of_list (fun b -> string_of_term (snd b))
                           brs) (')'::[])))))))))))
| Coq_tProj (p, c) ->
  let (p0, k) = p in
  let (ind, _) = p0 in
  let { inductive_mind = mind; inductive_ind = i } = ind in
  (match PCUICChecker.lookup_ind_decl (fst_ctx _UU03a3_) mind i with
   | Checked a ->
     let (_, oib) = a in
     (match nth_error oib.ind_projs k with
      | Some p1 ->
        let (na, _) = p1 in
        append (print_term _UU03a3_ _UU0393_ false false c)
          (append ('.'::('('::[])) (append na (')'::[])))
      | None ->
        append
          ('U'::('n'::('b'::('o'::('u'::('n'::('d'::('P'::('r'::('o'::('j'::('('::[]))))))))))))
          (append (string_of_inductive ind)
            (append (','::[])
              (append (string_of_nat i)
                (append (','::[])
                  (append (string_of_nat k)
                    (append (','::[])
                      (append (print_term _UU03a3_ _UU0393_ true false c)
                        (')'::[])))))))))
   | TypeError _ ->
     append
       ('U'::('n'::('b'::('o'::('u'::('n'::('d'::('P'::('r'::('o'::('j'::('('::[]))))))))))))
       (append (string_of_inductive ind)
         (append (','::[])
           (append (string_of_nat i)
             (append (','::[])
               (append (string_of_nat k)
                 (append (','::[])
                   (append (print_term _UU03a3_ _UU0393_ true false c)
                     (')'::[])))))))))
| Coq_tFix (l, n) ->
  parens top
    (append ('l'::('e'::('t'::(' '::('f'::('i'::('x'::(' '::[]))))))))
      (append (print_defs (print_term _UU03a3_) _UU0393_ l)
        (append nl
          (append (' '::('i'::('n'::(' '::[]))))
            (nth_default (string_of_nat n)
              (map (fun x -> string_of_name x.dname) l) n)))))
| Coq_tCoFix (l, n) ->
  parens top
    (append
      ('l'::('e'::('t'::(' '::('c'::('o'::('f'::('i'::('x'::(' '::[]))))))))))
      (append (print_defs (print_term _UU03a3_) _UU0393_ l)
        (append nl
          (append (' '::('i'::('n'::(' '::[]))))
            (nth_default (string_of_nat n)
              (map (fun x -> string_of_name x.dname) l) n)))))
