open BasicAst
open Datatypes
open List0
open PCUICAst
open PCUICTyping
open Universes0
open Monad_utils

type __ = Obj.t

type type_error =
| UnboundRel of nat
| UnboundVar of char list
| UnboundMeta of nat
| UnboundEvar of nat
| UndeclaredConstant of char list
| UndeclaredInductive of inductive
| UndeclaredConstructor of inductive * nat
| NotConvertible of context * term * term * term * term
| NotASort of term
| NotAProduct of term * term
| NotAnInductive of term
| IllFormedFix of term mfixpoint * nat
| UnsatisfiedConstraints of ConstraintSet.t
| CannotTakeSuccessor of universe
| NotEnoughFuel of nat

type 'a typing_result =
| Checked of 'a
| TypeError of type_error

val typing_monad : __ typing_result coq_Monad

val monad_exc : (type_error, __ typing_result) coq_MonadExc

val lookup_ind_decl :
  global_env -> ident -> nat -> ((PCUICEnvironment.one_inductive_body
  list * universes_decl) * PCUICEnvironment.one_inductive_body) typing_result
