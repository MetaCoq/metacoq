(* Distributed under the terms of the MIT license.   *)
Require Import Coq.Strings.String.

Definition ident   := string. (* e.g. nat *)
Definition qualid  := string. (* e.g. Datatypes.nat *)
Definition kername := string. (* e.g. Coq.Init.Datatypes.nat *)

Inductive name : Set :=
| nAnon
| nNamed (_ : ident).

Record inductive : Set := mkInd { inductive_mind : kername ;
                                  inductive_ind : nat }.
Arguments mkInd _%string _%nat.

Definition projection : Set := inductive * nat (* params *) * nat (* argument *).

(** Parametrized by term because term is not yet defined *)

Record def (term : Set) : Set := mkdef {
  dname : name; (* the name **)
  dtype : term;
  dbody : term; (* the body (a lambda term). Note, this may mention other (mutually-defined) names **)
  rarg  : nat  (* the index of the recursive argument, 0 for cofixpoints **) }.

Arguments dname {term} _.
Arguments dtype {term} _.
Arguments dbody {term} _.
Arguments rarg {term} _.

Definition mfixpoint (term : Set) : Set :=
  list (def term).

(** The kind of a cast *)

Inductive cast_kind : Set :=
| VmCast
| NativeCast
| Cast
| RevertCast.

Inductive recursivity_kind :=
  | Finite (* = inductive *)
  | CoFinite (* = coinductive *)
  | BiFinite (* = non-recursive, like in "Record" definitions *).

(** Kernel declaration references [global_reference] *)

Inductive global_reference :=
| VarRef : ident -> global_reference
| ConstRef : kername -> global_reference
| IndRef : inductive -> global_reference
| ConstructRef : inductive -> nat -> global_reference.
