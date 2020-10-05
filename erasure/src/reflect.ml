open BasicAst
open Bool
open Classes0
open Datatypes
open MCCompare
open MCString
open PeanoNat
open String0

type 'a coq_ReflectEq = { eqb : ('a -> 'a -> bool);
                          eqb_spec : ('a -> 'a -> reflect) }

(** val coq_ReflectEq_EqDec : 'a1 coq_ReflectEq -> 'a1 coq_EqDec **)

let coq_ReflectEq_EqDec x x0 y =
  let { eqb = _; eqb_spec = h } = x in
  let r = h x0 y in (match r with
                     | ReflectT -> true
                     | ReflectF -> false)

(** val reflect_string_obligation_1 : char list -> char list -> reflect **)

let reflect_string_obligation_1 x y =
  let s0 = string_dec x y in
  if s0
  then ReflectT
  else let c = string_compare x y in
       (match c with
        | Eq -> assert false (* absurd case *)
        | _ -> ReflectF)

(** val reflect_string : char list coq_ReflectEq **)

let reflect_string =
  { eqb = eq_string; eqb_spec = reflect_string_obligation_1 }

(** val reflect_nat : nat coq_ReflectEq **)

let reflect_nat =
  { eqb = Nat.eqb; eqb_spec = Nat.eqb_spec }

(** val eq_prod :
    ('a1 -> 'a1 -> bool) -> ('a2 -> 'a2 -> bool) -> ('a1 * 'a2) ->
    ('a1 * 'a2) -> bool **)

let eq_prod eqA eqB x y =
  let (a1, b1) = x in
  let (a2, b2) = y in if eqA a1 a2 then eqB b1 b2 else false

(** val reflect_prod_obligation_1 :
    'a1 coq_ReflectEq -> 'a2 coq_ReflectEq -> ('a1 * 'a2) -> ('a1 * 'a2) ->
    reflect **)

let reflect_prod_obligation_1 rA rB x0 y0 =
  let (x, y) = x0 in
  let (u, v) = y0 in
  let r = rA.eqb_spec x u in
  (match r with
   | ReflectT -> rB.eqb_spec y v
   | ReflectF -> ReflectF)

(** val reflect_prod :
    'a1 coq_ReflectEq -> 'a2 coq_ReflectEq -> ('a1 * 'a2) coq_ReflectEq **)

let reflect_prod x x0 =
  { eqb = (eq_prod x.eqb x0.eqb); eqb_spec = (fun x1 ->
    reflect_prod_obligation_1 x x0 x1) }

(** val reflect_kername_obligation_1 : kername -> kername -> reflect **)

let reflect_kername_obligation_1 x y =
  let s = kername_eq_dec x y in if s then ReflectT else ReflectF

(** val reflect_kername : kername coq_ReflectEq **)

let reflect_kername =
  { eqb = eq_kername; eqb_spec = reflect_kername_obligation_1 }

(** val reflect_inductive_obligation_1 : inductive -> inductive -> reflect **)

let reflect_inductive_obligation_1 i i' =
  let { inductive_mind = m; inductive_ind = n } = i in
  let { inductive_mind = m'; inductive_ind = n' } = i' in
  let r = reflect_kername.eqb_spec m m' in
  (match r with
   | ReflectT -> reflect_nat.eqb_spec n n'
   | ReflectF -> ReflectF)

(** val reflect_inductive : inductive coq_ReflectEq **)

let reflect_inductive =
  { eqb = eq_inductive; eqb_spec = reflect_inductive_obligation_1 }

(** val eqb_recursivity_kind :
    recursivity_kind -> recursivity_kind -> bool **)

let eqb_recursivity_kind r r' =
  match r with
  | Finite -> (match r' with
               | Finite -> true
               | _ -> false)
  | CoFinite -> (match r' with
                 | CoFinite -> true
                 | _ -> false)
  | BiFinite -> (match r' with
                 | BiFinite -> true
                 | _ -> false)

(** val reflect_recursivity_kind : recursivity_kind coq_ReflectEq **)

let reflect_recursivity_kind =
  { eqb = eqb_recursivity_kind; eqb_spec = (fun x y ->
    match x with
    | Finite -> (match y with
                 | Finite -> ReflectT
                 | _ -> ReflectF)
    | CoFinite -> (match y with
                   | CoFinite -> ReflectT
                   | _ -> ReflectF)
    | BiFinite -> (match y with
                   | BiFinite -> ReflectT
                   | _ -> ReflectF)) }
