(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import utils Ast.

Local Set Universe Polymorphism.


(** Reduction strategy to apply, beware [cbv], [cbn] and [lazy] are _strong_. *)

Monomorphic Variant reductionStrategy : Set :=
  cbv | cbn | hnf | all | lazy | unfold (i : kername).

Record typed_term : Type := existT_typed_term
{ my_projT1 : Type
; my_projT2 : my_projT1
}.

Monomorphic Inductive option_instance (A : Type) : Type := my_Some : A -> option_instance A | my_None : option_instance A.

Arguments Some {A} a.
Arguments None {A}.

Record TMInstance@{t u r} :=
{ TemplateMonad : Type@{t} -> Type@{r}
; tmReturn : forall {A:Type@{t}}, A -> TemplateMonad A
; tmBind : forall {A B : Type@{t}}, TemplateMonad A -> (A -> TemplateMonad B)
                                   -> TemplateMonad B

(* General commands *)
; tmFail : forall {A:Type@{t}}, string -> TemplateMonad A

(* Guaranteed to not cause "... already declared" error *)
; tmFreshName : ident -> TemplateMonad ident

; tmLocate : qualid -> TemplateMonad (list global_reference)
; tmCurrentModPath : unit -> TemplateMonad modpath

(* Quote the body of a definition or inductive. Its name need not be fully quaified *)
; tmQuoteInductive : kername -> TemplateMonad mutual_inductive_body
; tmQuoteUniverses : TemplateMonad ConstraintSet.t
; tmQuoteConstant : kername -> bool (* bypass opacity? *) -> TemplateMonad constant_body
(* unquote before making the definition *)
(* FIXME take an optional universe context as well *)
; tmMkInductive : bool (* infer universes? *) -> mutual_inductive_entry -> TemplateMonad unit
(* Typeclass registration and querying for an instance *)
; tmExistingInstance : global_reference -> TemplateMonad unit
}.

Monomorphic Variant import_status : Set :=
| ImportDefaultBehavior
| ImportNeedQualified.

Monomorphic Variant locality :=
| Discharge
| Global (_ : import_status).
