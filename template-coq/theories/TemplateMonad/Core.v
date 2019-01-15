From Coq Require Import Strings.String.
From Template Require Import Ast AstUtils.

Set Universe Polymorphism.
Set Primitive Projections.
Set Printing Universes.

(** ** The Template Monad

  A monad for programming with Template Coq structures. *)

(** Reduction strategy to apply, beware [cbv], [cbn] and [lazy] are _strong_. *)

Inductive reductionStrategy : Set :=
  cbv | cbn | hnf | all | lazy | unfold (i : ident).

Record typed_term : Type := existT_typed_term
{ my_projT1 : Type
; my_projT2 : my_projT1
}.
(*
Polymorphic Definition typed_term@{t} := {T : Type@{t} & T}.
Polymorphic Definition existT_typed_term a t : typed_term :=
  @existT Type (fun T => T) a t. (* todo: need to fix this *)

Definition my_projT1 (t : typed_term) : Type := @projT1 Type (fun T => T) t.
Definition my_projT2 (t : typed_term) : my_projT1 t := @projT2 Type (fun T => T) t.
*)

(** *** The TemplateMonad type *)

Module InProp.
  Cumulative Inductive TemplateMonad@{t u} : Type@{t} -> Prop :=
  (* Monadic operations *)
  | tmReturn : forall {A:Type@{t}}, A -> TemplateMonad A
  | tmBind : forall {A B : Type@{t}}, TemplateMonad A -> (A -> TemplateMonad B)
                                 -> TemplateMonad B

  (* General commands *)
  | tmPrint : forall {A:Type@{t}}, A -> TemplateMonad unit
  | tmFail : forall {A:Type@{t}}, string -> TemplateMonad A
  | tmEval : reductionStrategy -> forall {A:Type@{t}}, A -> TemplateMonad A


  (* Return the defined constant *)
  | tmDefinitionRed : ident -> option reductionStrategy -> forall {A:Type@{t}}, A -> TemplateMonad A
  | tmAxiomRed : ident -> option reductionStrategy -> forall A : Type@{t}, TemplateMonad A
  | tmLemmaRed : ident -> option reductionStrategy -> forall A : Type@{t}, TemplateMonad A

  (* Guaranteed to not cause "... already declared" error *)
  | tmFreshName : ident -> TemplateMonad ident

  | tmAbout : ident -> TemplateMonad (option global_reference)
  | tmCurrentModPath : unit -> TemplateMonad string

  (* Quoting and unquoting commands *)
  (* Similar to Quote Definition ... := ... *)
  | tmQuote : forall {A:Type@{t}}, A  -> TemplateMonad Ast.term
  (* Similar to Quote Recursively Definition ... := ...*)
  | tmQuoteRec : forall {A:Type@{t}}, A  -> TemplateMonad program
  (* Quote the body of a definition or inductive. Its name need not be fully qualified *)
  | tmQuoteInductive : kername -> TemplateMonad mutual_inductive_body
  | tmQuoteUniverses : unit -> TemplateMonad uGraph.t
  | tmQuoteConstant : kername -> bool (* bypass opacity? *) -> TemplateMonad constant_entry
  | tmMkDefinition : ident -> Ast.term -> TemplateMonad unit
  (* unquote before making the definition *)
  (* FIXME take an optional universe context as well *)
  | tmMkInductive : mutual_inductive_entry -> TemplateMonad unit
  | tmUnquote : Ast.term  -> TemplateMonad typed_term@{u}
  | tmUnquoteTyped : forall A : Type@{t}, Ast.term -> TemplateMonad A

  (* Typeclass registration and querying for an instance *)
  | tmExistingInstance : ident -> TemplateMonad unit
  | tmInferInstance : option reductionStrategy -> forall A : Type@{t}, TemplateMonad (option A)
  .
End InProp.

Module InType.
  Cumulative Inductive TemplateMonad@{t u} : Type@{t} -> Type :=
  (* Monadic operations *)
  | tmReturn : forall {A:Type@{t}}, A -> TemplateMonad A
  | tmBind : forall {A B : Type@{t}}, TemplateMonad A -> (A -> TemplateMonad B)
                                 -> TemplateMonad B

  (* General commands *)
  | tmFail : forall {A:Type@{t}}, string -> TemplateMonad A
  | tmEval : reductionStrategy -> forall {A:Type@{t}}, A -> TemplateMonad A

  (* Return the defined constant *)
  | tmDefinitionRed : ident -> option reductionStrategy -> forall {A:Type@{t}}, A -> TemplateMonad A
  | tmAxiomRed : ident -> option reductionStrategy -> forall A : Type@{t}, TemplateMonad A
  | tmLemmaRed : ident -> option reductionStrategy -> forall A : Type@{t}, TemplateMonad A

  (* Guaranteed to not cause "... already declared" error *)
  | tmFreshName : ident -> TemplateMonad ident

  | tmAbout : ident -> TemplateMonad (option global_reference)
  | tmCurrentModPath : unit -> TemplateMonad string

  (* Quote the body of a definition or inductive. Its name need not be fully qualified *)
  | tmQuoteInductive : kername -> TemplateMonad mutual_inductive_body
  | tmQuoteUniverses : unit -> TemplateMonad uGraph.t
  | tmQuoteConstant : kername -> bool (* bypass opacity? *) -> TemplateMonad constant_entry
  | tmMkDefinition : ident -> Ast.term -> TemplateMonad unit
  (* unquote before making the definition *)
  (* FIXME take an optional universe context as well *)
  | tmMkInductive : mutual_inductive_entry -> TemplateMonad unit
  | tmUnquote : Ast.term  -> TemplateMonad typed_term@{u}
  | tmUnquoteTyped : forall A : Type@{t}, Ast.term -> TemplateMonad A

  (* Typeclass registration and querying for an instance *)
  | tmExistingInstance : ident -> TemplateMonad unit
  | tmInferInstance : option reductionStrategy -> forall A : Type@{t}, TemplateMonad (option A)
  .
End InType.

Module TMAbs.
  Record TMInstance@{t u r} :=
  { TemplateMonad : Type@{t} -> Type@{r}
  ; tmReturn : forall {A:Type@{t}}, A -> TemplateMonad A
  ; tmBind : forall {A B : Type@{t}}, TemplateMonad A -> (A -> TemplateMonad B)
                                 -> TemplateMonad B

  (* General commands *)
  ; tmFail : forall {A:Type@{t}}, string -> TemplateMonad A
  ; tmEval : reductionStrategy -> forall {A:Type@{t}}, A -> TemplateMonad A

  (* Return the defined constant *)
  ; tmDefinitionRed : ident -> option reductionStrategy -> forall {A:Type@{t}}, A -> TemplateMonad A
  ; tmAxiomRed : ident -> option reductionStrategy -> forall A : Type@{t}, TemplateMonad A
  ; tmLemmaRed : ident -> option reductionStrategy -> forall A : Type@{t}, TemplateMonad A

  (* Guaranteed to not cause "... already declared" error *)
  ; tmFreshName : ident -> TemplateMonad ident

  ; tmAbout : ident -> TemplateMonad (option global_reference)
  ; tmCurrentModPath : unit -> TemplateMonad string

  (* Quote the body of a definition or inductive. Its name need not be fully qualified *)
  ; tmQuoteInductive : kername -> TemplateMonad mutual_inductive_body
  ; tmQuoteUniverses : unit -> TemplateMonad uGraph.t
  ; tmQuoteConstant : kername -> bool (* bypass opacity? *) -> TemplateMonad constant_entry
  ; tmMkDefinition : ident -> Ast.term -> TemplateMonad unit
  (* unquote before making the definition *)
  (* FIXME take an optional universe context as well *)
  ; tmMkInductive : mutual_inductive_entry -> TemplateMonad unit
  ; tmUnquote : Ast.term  -> TemplateMonad typed_term@{u}
  ; tmUnquoteTyped : forall A : Type@{t}, Ast.term -> TemplateMonad A

  (* Typeclass registration and querying for an instance *)
  ; tmExistingInstance : ident -> TemplateMonad unit
  ; tmInferInstance : option reductionStrategy -> forall A : Type@{t}, TemplateMonad (option A)
  }.

End TMAbs.

  Definition PropInstance@{t u r}: TMAbs.TMInstance@{t u r} :=
    {| TMAbs.TemplateMonad := InProp.TemplateMonad@{t u}
     ; TMAbs.tmReturn:=@InProp.tmReturn
     ; TMAbs.tmBind:=@InProp.tmBind
     ; TMAbs.tmFail:=@InProp.tmFail
     ; TMAbs.tmEval:=@InProp.tmEval
     ; TMAbs.tmDefinitionRed:=@InProp.tmDefinitionRed
     ; TMAbs.tmAxiomRed:=@InProp.tmAxiomRed
     ; TMAbs.tmLemmaRed:=@InProp.tmLemmaRed
     ; TMAbs.tmFreshName:=@InProp.tmFreshName
     ; TMAbs.tmAbout:=@InProp.tmAbout
     ; TMAbs.tmCurrentModPath:=@InProp.tmCurrentModPath
     ; TMAbs.tmQuoteInductive:=@InProp.tmQuoteInductive
     ; TMAbs.tmQuoteUniverses:=@InProp.tmQuoteUniverses
     ; TMAbs.tmQuoteConstant:=@InProp.tmQuoteConstant
     ; TMAbs.tmMkDefinition:=@InProp.tmMkDefinition
     ; TMAbs.tmMkInductive:=@InProp.tmMkInductive
     ; TMAbs.tmUnquote:=@InProp.tmUnquote
     ; TMAbs.tmUnquoteTyped:=@InProp.tmUnquoteTyped
     ; TMAbs.tmExistingInstance:=@InProp.tmExistingInstance
     ; TMAbs.tmInferInstance:=@InProp.tmInferInstance
    |}.

  Definition TypeInstance@{t u r}: TMAbs.TMInstance@{t u r} :=
    {| TMAbs.TemplateMonad := InType.TemplateMonad@{t u}
     ; TMAbs.tmReturn:=@InType.tmReturn
     ; TMAbs.tmBind:=@InType.tmBind
     ; TMAbs.tmFail:=@InType.tmFail
     ; TMAbs.tmEval:=@InType.tmEval
     ; TMAbs.tmDefinitionRed:=@InType.tmDefinitionRed
     ; TMAbs.tmAxiomRed:=@InType.tmAxiomRed
     ; TMAbs.tmLemmaRed:=@InType.tmLemmaRed
     ; TMAbs.tmFreshName:=@InType.tmFreshName
     ; TMAbs.tmAbout:=@InType.tmAbout
     ; TMAbs.tmCurrentModPath:=@InType.tmCurrentModPath
     ; TMAbs.tmQuoteInductive:=@InType.tmQuoteInductive
     ; TMAbs.tmQuoteUniverses:=@InType.tmQuoteUniverses
     ; TMAbs.tmQuoteConstant:=@InType.tmQuoteConstant
     ; TMAbs.tmMkDefinition:=@InType.tmMkDefinition
     ; TMAbs.tmMkInductive:=@InType.tmMkInductive
     ; TMAbs.tmUnquote:=@InType.tmUnquote
     ; TMAbs.tmUnquoteTyped:=@InType.tmUnquoteTyped
     ; TMAbs.tmExistingInstance:=@InType.tmExistingInstance
     ; TMAbs.tmInferInstance:=@InType.tmInferInstance
    |}.
  (* Monadic operations *)

Export InProp.

Definition print_nf {A} (msg : A) : TemplateMonad unit
  := tmBind (tmEval all msg) tmPrint.

Definition fail_nf {A} (msg : string) : TemplateMonad A
  := tmBind (tmEval all msg) tmFail.

Definition tmMkInductive' (mind : mutual_inductive_body) : TemplateMonad unit
  := tmMkInductive (mind_body_to_entry mind).

Definition tmLemma (i : ident) := tmLemmaRed i (Some hnf).
Definition tmAxiom (i : ident) := tmAxiomRed i (Some hnf).
Definition tmDefinition (i : ident) {A : Type} := @tmDefinitionRed i (Some hnf) A.
