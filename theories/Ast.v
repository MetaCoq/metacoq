Require Import Coq.Strings.String.
Require Import Coq.PArith.BinPos.

Definition universe := positive.
Definition ident := string.

Inductive sort : Set :=
| sProp
| sSet
| sType (_ : universe).

Inductive name : Set :=
| nAnon
| nNamed (_ : ident).

Inductive cast_kind : Set :=
| VmCast
| NativeCast
| Cast
| RevertCast.

Inductive inductive : Set :=
| mkInd : string -> nat -> inductive.

Record def (term : Set) : Set := mkdef
{ dname : name (** the name (note, this may mention other definitions **)
; dtype : term
; dbody : term (** the body (a lambda term) **)
; rarg  : nat  (** the index of the recursive argument **)
}.

Definition mfixpoint (term : Set) : Set :=
  list (def term).

Inductive term : Set :=
| tRel       : nat -> term
| tVar       : ident -> term (** this can go away **)
| tMeta      : nat -> term   (** NOTE: this can go away *)
| tEvar      : nat -> term
| tSort      : sort -> term
| tCast      : term -> cast_kind -> term -> term
| tProd      : name -> term (** the type **) -> term -> term
| tLambda    : name -> term (** the type **) -> term -> term
| tLetIn     : name -> term (** the term **) -> term (** the type **) -> term -> term
| tApp       : term -> list term -> term
| tConst     : string -> term
| tInd       : inductive -> term
| tConstruct : inductive -> nat -> term
| tCase      : (inductive * nat) (* # of parameters *) -> term (** type info **) -> term ->
               list (nat * term) -> term
| tFix       : mfixpoint term -> nat -> term
(*
| CoFix     of ('constr, 'types) pcofixpoint
*)
| tUnknown : string -> term.

Record inductive_body := mkinductive_body
{ ctors : list (ident * term * nat (* arity, w/o lets, w/o parameters *)) }.

Inductive program : Set :=
| PConstr : string -> term (*-> bool denoting opacity?*) -> program -> program
| PType   : ident -> nat (* # of parameters, w/o let-ins *) ->
            list (ident * inductive_body) -> program -> program
| PAxiom  : ident -> term (* the type *) -> program -> program
| PIn     : term -> program.


(* representation of mutual inductives. copied, more or less, from Coq/kernel/entries.mli
*)

Record one_inductive_entry : Set := {
  mind_entry_typename : ident;
  mind_entry_arity : term;
  mind_entry_template : bool; (* template polymorphism ? *)
  mind_entry_consnames : list ident;
  mind_entry_lc : list term}.


Definition local_entry : Set := term.
(*
Original definition in OCaml:

type local_entry =
  | LocalDef of constr
  | LocalAssum of constr
*)

Record mutual_inductive_entry : Set := {
  mind_entry_record : option (option ident); 
(*  mind_entry_finite : Decl_kinds.recursivity_kind;  (* inductive/coinductive/record*)*)
  mind_entry_params : list (ident * local_entry);
  mind_entry_inds : list one_inductive_entry;
  mind_entry_polymorphic : bool; 
(*  mind_entry_universes : Univ.universe_context; (*what is this?*) *)
  mind_entry_private : option bool
}.


(** A monad for programming with template-coq operations.
Using this monad, it should be possible to write many plugins (e.g. paramcoq)
in Gallina *)
Inductive TemplateMonad : Type -> Type :=
| tmReturn : forall T:Type, T -> TemplateMonad T
| tmBind : forall (A B : Type), 
    (A -> TemplateMonad B) 
    -> (TemplateMonad A) 
    -> (TemplateMonad B)
| tmPrint : forall A, A -> TemplateMonad unit
| tmQuote : ident -> TemplateMonad term
| tmQuoteRec : ident -> TemplateMonad program
| tmReduce : term (* -> strategy? *)-> TemplateMonad term
| tmMkDefinition : ident -> term -> TemplateMonad unit (* bool indicating success? *)
| tmMkInductive : mutual_inductive_entry -> TemplateMonad unit (* bool indicating success? *)
| tmFreshName : ident -> TemplateMonad ident 
    (* Guarenteed to not cause "... already declared" error *)
.




