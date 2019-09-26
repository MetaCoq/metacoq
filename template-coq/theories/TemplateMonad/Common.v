From Coq Require Import Strings.String.
From MetaCoq.Template Require Import Ast.

Set Universe Polymorphism.
Set Universe Minimization ToSet.
Set Primitive Projections.
Set Printing Universes.

(** Reduction strategy to apply, beware [cbv], [cbn] and [lazy] are _strong_. *)

Variant reductionStrategy : Set :=
  cbv | cbn | hnf | all | lazy | unfold (i : ident).

Record typed_term : Type := existT_typed_term
{ my_projT1 : Type
; my_projT2 : my_projT1
}.


Record TMInstance@{t u r} :=
{ TemplateMonad : Type@{t} -> Type@{r}
; tmReturn : forall {A:Type@{t}}, A -> TemplateMonad A
; tmBind : forall {A B : Type@{t}}, TemplateMonad A -> (A -> TemplateMonad B)
                                   -> TemplateMonad B

(* General commands *)
; tmFail : forall {A:Type@{t}}, string -> TemplateMonad A

(* Guaranteed to not cause "... already declared" error *)
; tmFreshName : ident -> TemplateMonad ident

; tmAbout : ident -> TemplateMonad (option global_reference)
; tmCurrentModPath : unit -> TemplateMonad string

(* Quote the body of a definition or inductive. Its name need not be fully quaified *)
; tmQuoteInductive : kername -> TemplateMonad mutual_inductive_body
; tmQuoteUniverses : TemplateMonad constraints
; tmQuoteConstant : kername -> bool (* bypass opacity? *) -> TemplateMonad constant_entry
(* unquote before making the definition *)
(* FIXME take an optional universe context as well *)
; tmMkInductive : mutual_inductive_entry -> TemplateMonad unit
(* Typeclass registration and querying for an instance *)
; tmExistingInstance : ident -> TemplateMonad unit
}.

Variant import_status : Set :=
| ImportDefaultBehavior
| ImportNeedQualified.

Variant locality :=
| Discharge
| Global (_ : import_status).
