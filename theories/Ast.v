Require Import Coq.Strings.String.
Require Import Coq.PArith.BinPos.

Definition universe := string.
Definition ident := string. (* e.g. nat *)
Definition kername := string. (* e.g. Coq.Init.Datatypes.nat *)

Inductive level : Set :=
  Level (_ : string)
| LevelVar (_ : nat) (* are these debruijn indices ? *).

Inductive sort : Set :=
| sProp
| sSet
| sType (_ : universe).

Record ind : Set := {} .

Inductive sort_family : Set :=
| InProp | InSet | InType.

Inductive name : Set :=
| nAnon
| nNamed (_ : ident).

Inductive cast_kind : Set :=
| VmCast
| NativeCast
| Cast
| RevertCast.

Inductive inductive : Set :=
| mkInd : kername -> nat -> inductive.

Record def (term : Set) : Set := mkdef
{ dname : name (** the name (note, this may mention other definitions **)
; dtype : term
; dbody : term (** the body (a lambda term) **)
; rarg  : nat  (** the index of the recursive argument, 0 for cofixpoints **)
}.

Definition mfixpoint (term : Set) : Set :=
  list (def term).

Definition projection : Set := inductive * nat (* params *) * nat (* argument *).

Definition universe_instance : Set := list level.

Inductive term : Set :=
| tRel       : nat -> term
| tVar       : ident -> term (** For free variables (e.g. in a goal) *)
| tMeta      : nat -> term   (** NOTE: this can go away *)
| tEvar      : nat -> list term -> term
| tSort      : sort -> term
| tCast      : term -> cast_kind -> term -> term
| tProd      : name -> term (** the type **) -> term -> term
| tLambda    : name -> term (** the type **) -> term -> term
| tLetIn     : name -> term (** the term **) -> term (** the type **) -> term -> term
| tApp       : term -> list term -> term
| tConst     : kername -> universe_instance -> term
| tInd       : inductive -> universe_instance -> term
| tConstruct : inductive -> nat -> universe_instance -> term
| tCase      : (inductive * nat) (* # of parameters *) -> term (** type info **)
               -> term (* discriminee *)->
               list (nat * term) (* branches *)
               -> term
| tProj      : projection -> term -> term
| tFix       : mfixpoint term -> nat -> term
| tCoFix     : mfixpoint term -> nat -> term.

Record inductive_body :=
  mkinductive_body
    { ind_name : ident;
      ind_type : term; (* Closed arity *)
      ind_kelim : list sort_family; (* Allowed elimination sorts *)
      ind_ctors : list (ident * term (* Under context of arities of the mutual inductive *)
                    * nat (* arity, w/o lets, w/o parameters *));
      ind_projs : list (ident * term) (* names and types of projections, if any.
                                     Type under context of params and inductive object *) }.

Inductive program : Set :=
| PConstr : string -> universe_instance -> term (* type *) -> term (* body *) -> program -> program
| PType   : ident -> nat (* # of parameters, w/o let-ins *) ->
            list inductive_body (* Non-empty *) -> program -> program
| PAxiom  : ident -> universe_instance -> term (* the type *) -> program -> program
| PIn     : term -> program.


Record constant_decl :=
  { cst_name : ident; (* TODO Universes *)
    cst_universes : universe_instance;
    cst_type : term;
    cst_body : option term }.

Record minductive_decl :=
  { ind_npars : nat;
    ind_bodies : list inductive_body }.

Inductive global_decl :=
| ConstantDecl : ident -> constant_decl -> global_decl
| InductiveDecl : ident -> minductive_decl -> global_decl.

Definition extend_program (p : program) (d : global_decl) : program :=
  match d with
  | ConstantDecl i {| cst_name:=_; cst_universes := u; cst_type:=ty;  cst_body:=Some body |}
    => PConstr i u (* TODO universes *) ty body p
  | ConstantDecl i {| cst_name:=_; cst_universes := u; cst_type:=ty;  cst_body:=None |}
    => PAxiom i u ty p
  | InductiveDecl i {| ind_npars:=n; ind_bodies := l |}
    => PType i n l p
  end.

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
Record definition_entry : Set := {
  definition_entry_type : term;
  definition_entry_body : term }.
  (* Missing universes, opaque, inline *)

Record parameter_entry : Set := {
  parameter_entry_type : term }.

Inductive constant_entry : Set :=
| ParameterEntry (p : parameter_entry)
| DefinitionEntry (def : definition_entry).


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

Definition typed_term := {T : Type & T}.
Definition existT_typed_term a t : typed_term := @existT Type (fun T => T) a t.

Definition my_projT1 (t : typed_term) : Type := @projT1 Type (fun T => T) t.
Definition my_projT2 (t : typed_term) : my_projT1 t := @projT2 Type (fun T => T) t.


Inductive global_reference :=
(* VarRef of Names.variable *)
| ConstRef : kername -> global_reference
| IndRef : inductive -> global_reference
| ConstructRef : inductive -> nat -> global_reference.

(** A monad for programming with template-coq operations.
Using this monad, it should be possible to write many plugins (e.g. paramcoq)
in Gallina *)
Inductive TemplateMonad : Type -> Prop :=
(* monadic operations *)
| tmReturn : forall {A:Type}, A -> TemplateMonad A
| tmBind : forall {A B : Type}, 
    (TemplateMonad A) 
    -> (A -> TemplateMonad B) 
    -> (TemplateMonad B)

(* general operations *)
| tmPrint : forall {A:Type}, A -> TemplateMonad unit
(** FIXME: strategy is currently ignored in the implementation -- it does all reductions.*)
| tmReduce : reductionStrategy -> forall {A:Type}, A -> TemplateMonad A
| tmDefinition : ident -> forall {A:Type}, A -> TemplateMonad unit
| tmAxiom : ident -> Type -> TemplateMonad unit
    (* todo: give a reduction strategy for the type (hnf for the moment) *)
| tmLemma : ident -> Type -> TemplateMonad unit
| tmFreshName : ident -> TemplateMonad ident
    (* Guarenteed to not cause "... already declared" error *)

(* quoting and unquoting operations *)
(** Similar to Quote Definition ... := ... *)
| tmQuote : forall {A:Type}, A  -> TemplateMonad term
(** Similar to Quote Recursively Definition ... := ...*)
| tmQuoteRec : forall {A:Type}, A  -> TemplateMonad program
(** Quote the body of a definition or inductive. Its name need not be fully qualified *)
| tmQuoteInductive : kername -> TemplateMonad mutual_inductive_entry
| tmQuoteConstant : kername -> bool (** bypass opacity?*) -> TemplateMonad constant_entry
| tmMkDefinition : ident -> term -> TemplateMonad unit
    (* unquote before making the definition *)
    (* should it take the number of polymorphically bound universes? in case
       unquoting has to be done? *)
| tmMkInductive : mutual_inductive_entry -> TemplateMonad unit (* bool indicating success? *)
| tmUnquote : term  -> TemplateMonad typed_term

(* Not yet implemented:*)
| tmAbout : ident -> TemplateMonad global_reference
.

(** unquote then reduce then quote *)
(* Definition tmUnQReduceQ : reductionStrategy -> term -> TemplateMonad term *)
(*   := fun s t => tmBind (tmBind (tmUnquote t) *)
(*                             (fun t => tmReduce s (projT2 t))) *)
(*                     tmQuoteTerm. *)

