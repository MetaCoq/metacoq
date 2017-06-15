Require Import Coq.Strings.String.
Require Import Coq.PArith.BinPos.

Definition universe := string.
Definition ident := string.

Inductive level : Set :=
  Level (_ : string)
| LevelVar (_ : nat) (* are these debruijn indices ? *).

Inductive sort : Set :=
| sProp
| sSet
| sType (_ : universe).

Record ind : Set := {} .

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
| tConst     : string -> list level -> term
| tInd       : inductive -> list level -> term
| tConstruct : inductive -> nat -> list level -> term
| tCase      : (inductive * nat) (* # of parameters *) -> term (** type info **)
               -> term (* discriminee *)->
               list (nat * term) (* branches *)
               -> term
| tFix       : mfixpoint term -> nat -> term
(*
| CoFix     of ('constr, 'types) pcofixpoint
*)
| tUnknown : string -> term.

Record inductive_body := mkinductive_body
{ ctors : list (ident * term * nat (* arity, w/o lets, w/o parameters *)) }.

Inductive program : Set :=
| PConstr : string -> list level -> term (*-> bool denoting opacity?*) -> program -> program
| PType   : ident -> nat (* # of parameters, w/o let-ins *) ->
            list (ident * inductive_body) -> program -> program
| PAxiom  : ident -> term (* the type *) -> program -> program
| PIn     : term -> program.


(** representation of mutual inductives. nearly copied from Coq/kernel/entries.mli
*)

Record one_inductive_entry : Set := {
  mind_entry_typename : ident;
  mind_entry_arity : term;
  mind_entry_template : bool; (* template polymorphism ? *)
  mind_entry_consnames : list ident;
  mind_entry_lc : list term}.


Inductive local_entry : Set := 
| LocalDef : term -> local_entry (* local let binding *)
| LocalAssum : term -> local_entry.


Inductive recursivity_kind :=
  | Finite (** = inductive *)
  | CoFinite (** = coinductive *)
  | BiFinite (** = non-recursive, like in "Record" definitions *).


(* kernel/entries.mli*)
Record mutual_inductive_entry : Set := {
  mind_entry_record : option (option ident); 
  mind_entry_finite : recursivity_kind;
  mind_entry_params : list (ident * local_entry);
  mind_entry_inds : list one_inductive_entry;
  mind_entry_polymorphic : bool; 
(*  mind_entry_universes : Univ.universe_context; *)
  (* Should the above be used? At least we need one number indicating
     the number of polymorphically bound definitions*)
  mind_entry_private : option bool
}.

Inductive reductionStrategy : Set :=
  cbv | cbn | hnf | all.

(** A monad for programming with template-coq operations.
Using this monad, it should be possible to write many plugins (e.g. paramcoq)
in Gallina *)
Inductive TemplateMonad : Type -> Prop :=
| tmReturn : forall {A:Type}, A -> TemplateMonad A
| tmBind : forall {A B : Type}, 
    (TemplateMonad A) 
    -> (A -> TemplateMonad B) 
    -> (TemplateMonad B)
| tmPrint : forall {A:Type}, A -> TemplateMonad unit
(** Quote the body of a definition or inductive. Its name need not be fully qualified --
  the implementation uses Locate *)
| tmQuote : ident -> bool (** bypass opacity?*)-> TemplateMonad (option (term+mutual_inductive_entry))
(** similar to Quote Definition ... := ...
  To actually make the definition, use (tmMkDefinition false) *)
| tmQuoteTerm : forall {A:Type}, A  -> TemplateMonad term
(** similar to Quote Recursively Definition ... := ...*)
| tmQuoteTermRec : forall {A:Type}, A  -> TemplateMonad program
(** FIXME: strategy is currently ignored in the implementation -- it does all reductions.*)
| tmReduce : reductionStrategy -> forall {A:Type}, A -> TemplateMonad A
| tmMkDefinition : bool (* unquote? *) -> ident -> forall {A:Type}, A -> TemplateMonad unit (* bool indicating success? *)
    (* should it take the number of polymorphically bound universes? in case
       unquoting has to be done? *)
| tmMkInductive : mutual_inductive_entry -> TemplateMonad unit (* bool indicating success? *)

(* Not yet implemented:*)

(** unquote then reduce then quote *)
| tmUnQReduceQ : reductionStrategy -> term (* -> strategy? *)-> TemplateMonad term
| tmUnquote : term  -> TemplateMonad {T:Type & T}
| tmFreshName : ident -> TemplateMonad bool 
    (* yes => Guarenteed to not cause "... already declared" error *).
