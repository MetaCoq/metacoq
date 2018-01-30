Require Import Coq.Strings.String.
Require Import Coq.PArith.BinPos.
Require Import List. Import ListNotations.
From Template Require Import monad_utils.
From Template Require Export univ uGraph.

Definition ident := string. (* e.g. nat *)
Definition kername := string. (* e.g. Coq.Init.Datatypes.nat *)

Inductive sort_family : Set := InProp | InSet | InType.

Inductive name : Set :=
| nAnon
| nNamed (_ : ident).

Inductive cast_kind : Set :=
| VmCast
| NativeCast
| Cast
| RevertCast.

Record inductive : Set := mkInd { inductive_mind : kername ;
                                  inductive_ind : nat }.
Arguments mkInd _%string _%nat.

Definition projection : Set := inductive * nat (* params *) * nat (* argument *).

Inductive global_reference :=
(* VarRef of Names.variable *)
| ConstRef : kername -> global_reference
| IndRef : inductive -> global_reference
| ConstructRef : inductive -> nat -> global_reference.

(* Parametrized by term because term is not yet defined *)
Record def (term : Set) : Set := mkdef
{ dname : name (** the name (note, this may mention other definitions **)
; dtype : term
; dbody : term (** the body (a lambda term) **)
; rarg  : nat  (** the index of the recursive argument, 0 for cofixpoints **)
}.

Definition mfixpoint (term : Set) : Set :=
  list (def term).

Inductive term : Set :=
| tRel       : nat -> term
| tVar       : ident -> term (** For free variables (e.g. in a goal) *)
| tMeta      : nat -> term   (** NOTE: this can go away *)
| tEvar      : nat -> list term -> term
| tSort      : universe -> term
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


Definition mkApps t us :=
  match us with
  | nil => t
  | _ => match t with
        | tApp f args => tApp f (args ++ us)
        | _ => tApp t us
        end
  end.

Definition mkApp t u := Eval cbn in mkApps t [u].


(** * Entries *)

(** representation of mutual inductives. nearly copied from Coq/kernel/entries.mli
*)

(** Assume the following definition in concrete syntax:
{v Inductive I1 (x1:X1) ... (xn:Xn) : A1 := c11 : T11 | ... | c1n1 : T1n1
...
with      Ip (x1:X1) ... (xn:Xn) : Ap := cp1 : Tp1 | ... | cpnp : Tpnp. v}

then, in i{^ th} block, [mind_entry_params] is [xn:Xn;...;x1:X1];
[mind_entry_arity] is [Ai], defined in context [x1:X1;...;xn:Xn];
[mind_entry_lc] is [Ti1;...;Tini], defined in context [[A'1;...;A'p;x1:X1;...;xn:Xn]] where [A'i] is [Ai] generalized over [[x1:X1;...;xn:Xn]].
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
Record definition_entry := {
  definition_entry_type : term;
  definition_entry_body : term;
  definition_entry_polymorphic : bool;
  definition_entry_universes   : universe_context;
  definition_entry_opaque      : bool;
 }.


Record parameter_entry : Set := {
  parameter_entry_type : term }.

Inductive constant_entry :=
| ParameterEntry (p : parameter_entry)
| DefinitionEntry (def : definition_entry).

Record mutual_inductive_entry := {
  mind_entry_record : option (option ident); 
  mind_entry_finite : recursivity_kind;
  mind_entry_params : list (ident * local_entry);
  mind_entry_inds : list one_inductive_entry;
  mind_entry_polymorphic : bool; 
  mind_entry_universes : univ.universe_context;
  mind_entry_private : option bool
}.


(** * Declarations *)

(** ** The context of De Bruijn indices *)

Record context_decl := { decl_name : name ;
                         decl_body : option term ;
                         decl_type : term }.

Definition vass x A := {| decl_name := x; decl_body := None; decl_type := A |}.
Definition vdef x t A := {| decl_name := x; decl_body := Some t; decl_type := A |}.

(* local ctx *)
Definition context := list context_decl.

Definition snoc {A} (Γ : list A) (d : A) := d :: Γ.

Notation " Γ ,, d " := (snoc Γ d) (at level 20, d at next level).

(** ** The context of global constants *)

(* one_inductive_body from declarations.ml *)
Record inductive_body :=
  mkinductive_body
    { ind_name : ident;
      ind_type : term; (* Closed arity *)
      ind_kelim : list sort_family; (* Allowed elimination sorts *)
      ind_ctors : list (ident * term (* Under context of arities of the mutual inductive *)
                    * nat (* arity, w/o lets, w/o parameters *));
      ind_projs : list (ident * term) (* names and types of projections, if any.
                                     Type under context of params and inductive object *) }.

(* mutual_inductive_body from declarations.ml *)
Record minductive_decl :=
  { ind_npars : nat;
    ind_bodies : list inductive_body ;
    ind_universes : universe_context
  }.

(* constant_body from declarations.ml *)
Record constant_decl :=
  { cst_universes : universe_context;
    cst_type : term;
    cst_body : option term }.

Inductive global_decl :=
| ConstantDecl : kername -> constant_decl -> global_decl
| InductiveDecl : kername -> minductive_decl -> global_decl.


Definition global_declarations := list global_decl.

Definition global_context : Type := global_declarations * uGraph.t.



Inductive program :=
| PConstr : string -> universe_context -> term (* type *) -> term (* body *) -> program -> program
| PType   : ident -> universe_context -> nat (* # of parameters, w/o let-ins *) ->
            list inductive_body (* Non-empty *) -> program -> program
| PAxiom  : ident -> universe_context -> term (* the type *) -> program -> program
| PIn     : term -> program.

Definition extend_program (p : program) (d : global_decl) : program :=
  match d with
  | ConstantDecl i {| cst_universes := u; cst_type:=ty;  cst_body:=Some body |}
    => PConstr i u ty body p
  | ConstantDecl i {| cst_universes := u; cst_type:=ty;  cst_body:=None |}
    => PAxiom i u ty p
  | InductiveDecl i {| ind_npars:=n; ind_bodies := l ; ind_universes := u |}
    => PType i u n l p
  end.




Inductive reductionStrategy : Set :=
  cbv | cbn | hnf | all | lazy.

Definition typed_term := {T : Type & T}.
Definition existT_typed_term a t : typed_term := @existT Type (fun T => T) a t.

Definition my_projT1 (t : typed_term) : Type := @projT1 Type (fun T => T) t.
Definition my_projT2 (t : typed_term) : my_projT1 t := @projT2 Type (fun T => T) t.


(** A monad for programming with template-coq operations.
Using this monad, it should be possible to write many plugins (e.g. paramcoq)
in Gallina *)
Inductive TemplateMonad : Type -> Prop :=
(** ** Monadic operations *)
| tmReturn : forall {A:Type}, A -> TemplateMonad A
| tmBind : forall {A B : Type}, TemplateMonad A -> (A -> TemplateMonad B)
                           -> TemplateMonad B

(** ** General commands *)
| tmPrint : forall {A:Type}, A -> TemplateMonad unit
| tmFail : forall {A:Type}, string -> TemplateMonad A
| tmEval : reductionStrategy -> forall {A:Type}, A -> TemplateMonad A

(** Return the defined constant *)
| tmDefinition : ident -> forall {A:Type}, A -> TemplateMonad A
| tmAxiom : ident -> forall A, TemplateMonad A
| tmLemma : ident -> forall A, TemplateMonad A

(** Guarenteed to not cause "... already declared" error *)
| tmFreshName : ident -> TemplateMonad ident

| tmAbout : ident -> TemplateMonad (option global_reference)
| tmCurrentModPath : unit -> TemplateMonad string

(** ** Quoting and unquoting commands *)
(** Similar to Quote Definition ... := ... *)
| tmQuote : forall {A:Type}, A  -> TemplateMonad term
(** Similar to Quote Recursively Definition ... := ...*)
| tmQuoteRec : forall {A:Type}, A  -> TemplateMonad program
(** Quote the body of a definition or inductive. Its name need not be fully qualified *)
| tmQuoteInductive : kername -> TemplateMonad minductive_decl
| tmQuoteUniverses : unit -> TemplateMonad uGraph.t
| tmQuoteConstant : kername -> bool (** bypass opacity?*) -> TemplateMonad constant_entry
| tmMkDefinition : ident -> term -> TemplateMonad unit
    (* unquote before making the definition *)
    (* should it take the number of polymorphically bound universes? in case
       unquoting has to be done? *)
| tmMkInductive : mutual_inductive_entry -> TemplateMonad unit
| tmUnquote : term  -> TemplateMonad typed_term
| tmUnquoteTyped : forall A, term -> TemplateMonad A

(** ** Not yet implemented *)
| tmExistingInstance : ident -> TemplateMonad unit
.

(* This allow to use notations of MonadNotation *)
Instance TemplateMonad_Monad : Monad TemplateMonad
  := {| ret := @tmReturn ; bind := @tmBind |}.
