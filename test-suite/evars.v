From Coq Require Import String List.
From MetaCoq.Template Require Import Ast Loader.
Import ListNotations.
Definition bAnon := {| binder_name := nAnon; binder_relevance := Relevant |}.
Definition bNamed s := {| binder_name := nNamed s; binder_relevance := Relevant |}.

Goal True.
  evar (n : nat).
  match goal with
    H := ?t |- _ => quote_term t (fun x => pose (qn:=x))
  end.
  match goal with
    qn := Ast.tEvar _ nil |- _ => idtac
  end.
  exact I.
  Unshelve. exact 0.
Qed.

(** Evars *)
MetaCoq Quote Definition lnil := @nil.
MetaCoq Quote Definition listnat := (list nat).
MetaCoq Unquote Definition foo := (tCast (tApp lnil [hole]) Cast listnat).

Local Open Scope string_scope.

Goal list nat.
  (* Back and forth *)
  let x := open_constr:(nil) in quote_term x (fun qt =>
    ltac:(denote_term qt (fun unqt => set (e := eq_refl : unqt = x :> list bool)))).
    (* Creation of evars by denotation of 'hole' *)
  let x := eval cbv in (tApp lnil [hole]) in
  denote_term x (fun k => exact k).
Defined.

Goal True.
  let x := eval cbv in (tLambda bAnon listnat hole) in
  (* We check that created evars are in the right context *)
  denote_term x (fun k => set (ev := k); revert ev).
  instantiate (1 := list nat).
  instantiate (1 := l).
  exact I.
Qed.


