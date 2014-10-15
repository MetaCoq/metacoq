Require Import Coq.Strings.String.
Require Import Coq.PArith.BinPos.

Definition universe := positive.
Definition ident := string.

Inductive sort : Type :=
| sProp
| sSet
| sType (_ : universe).

Record ind : Type := {} .

Inductive name : Type :=
| nAnon
| nNamed (_ : ident).

Inductive cast_kind : Type :=
| VmCast
| NativeCast
| Cast
| RevertCast.

Inductive inductive : Type :=
| mkInd : string -> nat -> inductive.

Record def (term : Type) : Type := mkdef
{ dname : name (** the name (note, this may mention other definitions **)
; dtype : term
; dbody : term (** the body (a lambda term) **)
; rarg  : nat  (** the index of the recursive argument **)
}.

Definition mfixpoint (term : Type) : Type :=
  list (def term).

Inductive term : Type :=
| tRel       : nat -> term
| tVar       : ident -> term (** this can go away **)
| tMeta      : nat -> term   (** NOTE: this can go away *)
| tEvar      : nat -> term
| tSort      : sort -> term
| tCast      : term -> cast_kind -> term -> term
| tProd      : name -> term (** the type **) -> term -> term
| tLambda    : name -> term (** the type **) -> term -> term
| tLetIn     : name -> term (** the type **) -> term -> term -> term
| tApp       : term -> list term -> term
| tConst     : string -> term
| tInd       : inductive -> term
| tConstruct : inductive -> nat -> term
| tCase      : nat (* # of parameters *) -> term (** type info **) -> term -> list term -> term
| tFix       : mfixpoint term -> nat -> term
(*
| CoFix     of ('constr, 'types) pcofixpoint
*)
| tUnknown : string -> term.

Record inductive_body := mkinductive_body
{ ctors : list (ident * term) }.

Inductive program : Type :=
| PConstr : string -> term -> program -> program
| PType   : ident -> list (ident * inductive_body) -> program -> program
| PAxiom  : ident -> program -> program
| PIn     : term -> program.