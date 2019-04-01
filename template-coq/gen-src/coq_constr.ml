open Plugin_core
open Constr

type nat

let tRel (n : nat) =
  failwith "tRel"
let tVar (i : Names.Id.t) : Constr.t =
  Constr.mkVar i

let tMeta (n : nat) : Constr.t =
  failwith "tMeta"

let tEvar (n : nat) (ls : Constr.t list) : Constr.t =
(*   Constr.mkEvar n (Array.of_list ls) *)
  failwith "tEvar"

let tSort (u : Univ.universe) : Constr.t =
  Constr.mkSort u

let tCast (a : Constr.t) (b : Constr.cast_kind) (c : Constr.t) : Constr.t =
  Constr.mkCast (a, b, c)


let constr_match
    (rel : nat -> 'a)
    (var : ident -> 'a)
    (meta : nat -> 'a)
    (evar : nat -> term list -> 'a)
    (sort : universe -> 'a)
    (cast : term -> Constr.cast_kind -> term -> 'a)
    (prod : name -> term -> term -> 'a)
    (lambda : name -> term -> term -> 'a)
    (letin : name -> term -> term -> term -> 'a)
    (app : term -> term list -> 'a)
    (const : kername -> universe_instance -> 'a)
    (construct : inductive -> nat -> universe_instance -> 'a)
    (case : inductive * nat * term -> term -> (nat * term) list -> 'a)
    (proj : projection -> term -> 'a)
    (fix : term mfixpoint -> nat -> 'a)
    (cofix : term mfixpoint -> nat -> 'a)
    (t : term) : 'a =
  match Constr.kind t with
  | Constr.Rel n -> rel n
  | Constr.Var id -> var id
  | Constr.Meta m -> meta m
  | Constr.Evar (a,b) -> evar a b
  | Constr.Sort s -> sort s
  | Constr.Cast (a,b,c) -> cast a b c
  | Constr.Prod (a,b,c) -> prod a b c
  | Constr.Lambda (a,b,c) -> lambda a b c
  | Constr.LetIn (a,b,c,d) -> letin a b c d
  | Constr.App (f, xs) -> app f (Array.to_list xs)
  | Constr.Const _
  | Constr.Ind _
  | Constr.Construct _
  | Constr.Case _
  | Constr.Fix _
  | Constr.CoFix _
  | Constr.Proj _ -> failwith "not implemented"
