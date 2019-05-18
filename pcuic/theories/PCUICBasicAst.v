(* Distributed under the terms of the MIT license.   *)
Require Import Coq.Strings.String.
From Template Require Import BasicAst.
From PCUIC Require Import Name.

Section BasicAST.

Context `{Name}.

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

End BasicAST.