
Set Universe Polymorphism.

Cumulative Inductive list@{i} (A : Type@{i}) : Type@{i} := nil : list A | cons : A -> list A -> list A.
Set Printing Universes.
Set Printing All.
Print list.

Cumulative Inductive onlist@{j} (Y : Type@{j}) : Type@{j} :=
 | nest : list@{j} Y -> onlist Y.


Definition onlist_out@{j} {Y : Type@{j}} (o : onlist Y) : list@{j} Y := 
  match o with 
  | nest _ l => l
  end.

 (* We don't require that list@{j'} Y is well-typed when Y : Type@{j} in the cumulativity checking
    but we check cumulativity assuming it. *)

(* When comparing fully applied `onlist@{u} X <= onlist@{v} Y` we check that the parameters are convertible,
    so: X ~= Y : max(u, v). Morally list@{v} X is not necessarily welltyped, but list@{max(u,v)} X is.  *)


Monomorphic Universes u v.
(* Monomorphic Constraint u < v. *)

Definition id@{u} {A : Type@{u}} (x : A) := x.

(* Forces u <= v *)
Definition trans_onlist := (fun (X : Type@{u}) (x : onlist@{u} X) => @id (@onlist@{v} X) x).

Set Printing Universes.
Definition t := (fun X : Type@{u} => trans_onlist X (nest X (@nil@{u} X))).

Definition t' := Eval compute in t.



Goal True.
    set (foo := t').
    unfold t' in foo.


Cumulative Inductive onlist@{j k +} (Y : Type@{j} -> Type@{j}) : Type@{k} :=
 | nest : forall x : Type@{j}, Y x -> onlist Y.

(** Parameters are convertible, one live in {j} the other in {j'}. 
    By confluence and sr, they both reduce to the same well-typed terms in some universe k <= j, j'.


*)

(* Y : Type@{j} -> Type@{j} 

   x : Type@{j'} 

   Y x -> Type@{j'} <= Type@{j}
*)
