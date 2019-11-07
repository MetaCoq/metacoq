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

(** val typing_monad : __ typing_result coq_Monad **)

let typing_monad =
  { ret = (fun _ a -> Checked a); bind = (fun _ _ m f ->
    match m with
    | Checked a -> f a
    | TypeError t0 -> TypeError t0) }

(** val monad_exc : (type_error, __ typing_result) coq_MonadExc **)

let monad_exc =
  { raise = (fun _ e -> TypeError e); catch = (fun _ m f ->
    match m with
    | Checked _ -> m
    | TypeError t0 -> f t0) }

(** val lookup_ind_decl :
    global_env -> ident -> nat -> ((PCUICEnvironment.one_inductive_body
    list * universes_decl) * PCUICEnvironment.one_inductive_body)
    typing_result **)

let lookup_ind_decl _UU03a3_ ind i =
  match lookup_env _UU03a3_ ind with
  | Some g ->
    (match g with
     | PCUICEnvironment.ConstantDecl (_, _) ->
       raise (Obj.magic monad_exc) (UndeclaredInductive { inductive_mind =
         ind; inductive_ind = i })
     | PCUICEnvironment.InductiveDecl (_, m) ->
       let { PCUICEnvironment.ind_finite = _; PCUICEnvironment.ind_npars = _;
         PCUICEnvironment.ind_params = _; PCUICEnvironment.ind_bodies = l;
         PCUICEnvironment.ind_universes = uctx } = m
       in
       (match nth_error l i with
        | Some body -> ret (Obj.magic typing_monad) ((l, uctx), body)
        | None ->
          raise (Obj.magic monad_exc) (UndeclaredInductive { inductive_mind =
            ind; inductive_ind = i })))
  | None ->
    raise (Obj.magic monad_exc) (UndeclaredInductive { inductive_mind = ind;
      inductive_ind = i })
