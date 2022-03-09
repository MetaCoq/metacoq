open All_Forall
open BasicAst
open Datatypes
open List0
open PCUICAst
open PCUICEquality
open Universes0

(** val compare_universe_variance :
    (Universe.t -> Universe.t -> bool) -> (Universe.t -> Universe.t -> bool)
    -> Variance.t -> Level.t -> Level.t -> bool **)

let compare_universe_variance equ lequ v u u' =
  match v with
  | Variance.Irrelevant -> true
  | Variance.Covariant -> lequ (Universe.make u) (Universe.make u')
  | Variance.Invariant -> equ (Universe.make u) (Universe.make u')

(** val compare_universe_instance :
    (Universe.t -> Universe.t -> bool) -> Level.t list -> Level.t list -> bool **)

let compare_universe_instance equ u u' =
  forallb2 equ (map Universe.make u) (map Universe.make u')

(** val compare_universe_instance_variance :
    (Universe.t -> Universe.t -> bool) -> (Universe.t -> Universe.t -> bool)
    -> Variance.t list -> Level.t list -> Level.t list -> bool **)

let rec compare_universe_instance_variance equ lequ v u u' =
  match u with
  | [] -> (match u' with
           | [] -> true
           | _ :: _ -> false)
  | u0 :: us ->
    (match u' with
     | [] -> false
     | u'0 :: us' ->
       (match v with
        | [] -> compare_universe_instance_variance equ lequ v us us'
        | v0 :: vs ->
          (&&) (compare_universe_variance equ lequ v0 u0 u'0)
            (compare_universe_instance_variance equ lequ vs us us')))

(** val compare_global_instance :
    PCUICEnvironment.global_env -> (Universe.t -> Universe.t -> bool) ->
    (Universe.t -> Universe.t -> bool) -> global_reference -> nat -> Level.t
    list -> Level.t list -> bool **)

let compare_global_instance _UU03a3_ equ lequ gr napp =
  match global_variance _UU03a3_ gr napp with
  | Some v -> compare_universe_instance_variance equ lequ v
  | None -> compare_universe_instance equ
