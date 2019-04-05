open Plugin_core
open Constr

type name = Names.Name.t
type id = Names.Id.t
type universe = Univ.Universe.t
type universe_instance = unit
type projection = Names.Projection.t
type 'a mfixpoint = 'a BasicAst.mfixpoint
type nat = int

let tRel (n : nat) =
  failwith "tRel"
let tVar (i : id) : Constr.t =
  Constr.mkVar i

let tMeta (n : nat) : Constr.t =
  failwith "tMeta"

let tEvar (n : nat) (ls : Constr.t list) : Constr.t =
  failwith "tEvar is not supported"

let tSort (u : Univ.Universe.t) : Constr.t =
  failwith "tSort"

let tCast (a : Constr.t) (b : Constr.cast_kind) (c : Constr.t) : Constr.t =
  Constr.mkCast (a, b, c)

let tProd (n : name) (a : Constr.t) (b : Constr.t) : Constr.t =
  Constr.mkProd (n, a, b)

let tLambda (n : name) (a : Constr.t) (b : Constr.t) : Constr.t =
  Constr.mkLambda (n, a, b)

let tLetIn (n : name) (t : Constr.t) (b : Constr.t) (c : Constr.t) : Constr.t =
  Constr.mkLetIn (n, t, b, c)

let tApp (f : Constr.t) (ls : Constr.t list) : Constr.t =
  Constr.mkApp (f, Array.of_list ls)

let tConst (kn : 'a) : 'a =
  failwith "tConst"

let tConstruct (kn : 'a) : 'a =
  failwith "tConstruct"

let tCase (_ : 'a) : 'a =
  failwith "tCase"

let tProj (_ : BasicAst.projection) (_ : Constr.t) : Constr.t =
  failwith "tProj"

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
    (construct : Names.inductive -> nat -> universe_instance -> 'a)
    (case : Names.inductive * nat * term -> term -> (nat * term) list -> 'a)
    (proj : projection -> term -> 'a)
    (fix : term mfixpoint -> nat -> 'a)
    (cofix : term mfixpoint -> nat -> 'a)
    (t : term) : 'a =
  match Constr.kind t with
  | Constr.Rel n -> rel n
  | Constr.Var id -> var id
  | Constr.Meta m -> meta m
  | Constr.Evar (a,b) -> evar (Evar.repr a) (Array.to_list b)
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
