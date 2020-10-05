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

val coq_ReflectEq_EqDec : 'a1 coq_ReflectEq -> 'a1 coq_EqDec

val reflect_string_obligation_1 : char list -> char list -> reflect

val reflect_string : char list coq_ReflectEq

val reflect_nat : nat coq_ReflectEq

val eq_prod :
  ('a1 -> 'a1 -> bool) -> ('a2 -> 'a2 -> bool) -> ('a1 * 'a2) -> ('a1 * 'a2)
  -> bool

val reflect_prod_obligation_1 :
  'a1 coq_ReflectEq -> 'a2 coq_ReflectEq -> ('a1 * 'a2) -> ('a1 * 'a2) ->
  reflect

val reflect_prod :
  'a1 coq_ReflectEq -> 'a2 coq_ReflectEq -> ('a1 * 'a2) coq_ReflectEq

val reflect_kername_obligation_1 : kername -> kername -> reflect

val reflect_kername : kername coq_ReflectEq

val reflect_inductive_obligation_1 : inductive -> inductive -> reflect

val reflect_inductive : inductive coq_ReflectEq

val eqb_recursivity_kind : recursivity_kind -> recursivity_kind -> bool

val reflect_recursivity_kind : recursivity_kind coq_ReflectEq
