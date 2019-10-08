From Coq Require Import Strings.String.
Open Scope string_scope.
From MetaCoq.Template Require Import Ast AstUtils Common.

Set Universe Polymorphism.
Set Universe Minimization ToSet.
Set Primitive Projections.
Set Printing Universes.

(** ** The Template Monad

  A monad for programming with Template Coq structures. Use [Run
  TemplateProgram] on a monad action to produce its side-effects.

  Uses a reduction strategy specifier [reductionStrategy]. *)

(** *** The TemplateMonad type *)
Cumulative Inductive TemplateMonad@{t u} : Type@{t} -> Prop :=
(* Monadic operations *)
| tmReturn : forall {A:Type@{t}}, A -> TemplateMonad A
| tmBind : forall {A B : Type@{t}}, TemplateMonad A -> (A -> TemplateMonad B)
                               -> TemplateMonad B

(* General commands *)
| tmPrint : forall {A:Type@{t}}, A -> TemplateMonad unit
| tmMsg   : string -> TemplateMonad unit
| tmFail : forall {A:Type@{t}}, string -> TemplateMonad A
| tmEval : reductionStrategy -> forall {A:Type@{t}}, A -> TemplateMonad A

(* Return the defined constant *)
| tmLemma : ident -> forall A : Type@{t}, TemplateMonad A
| tmDefinitionRed_ : forall (opaque : bool), ident -> option reductionStrategy -> forall {A:Type@{t}}, A -> TemplateMonad A
| tmAxiomRed : ident -> option reductionStrategy -> forall A : Type@{t}, TemplateMonad A
| tmVariable : ident -> Type@{t} -> TemplateMonad unit
                                                                                
(* Guaranteed to not cause "... already declared" error *)
| tmFreshName : ident -> TemplateMonad ident

| tmAbout : qualid -> TemplateMonad (option global_reference)
| tmCurrentModPath : unit -> TemplateMonad string

(* Quoting and unquoting commands *)
(* Similar to Quote Definition ... := ... *)
| tmQuote : forall {A:Type@{t}}, A  -> TemplateMonad Ast.term
(* Similar to Quote Recursively Definition ... := ...*)
| tmQuoteRec : forall {A:Type@{t}}, A  -> TemplateMonad program
(* Quote the body of a definition or inductive. Its name need not be fully qualified *)
| tmQuoteInductive : qualid -> TemplateMonad mutual_inductive_body
| tmQuoteUniverses : TemplateMonad constraints
| tmQuoteConstant : qualid -> bool (* bypass opacity? *) -> TemplateMonad constant_entry
(* unquote before making the definition *)
(* FIXME take an optional universe context as well *)
| tmMkInductive : mutual_inductive_entry -> TemplateMonad unit
| tmUnquote : Ast.term  -> TemplateMonad typed_term@{u}
| tmUnquoteTyped : forall A : Type@{t}, Ast.term -> TemplateMonad A

(* Typeclass registration and querying for an instance *)
| tmExistingInstance : qualid -> TemplateMonad unit
| tmInferInstance : option reductionStrategy -> forall A : Type@{t}, TemplateMonad (option A)
.

Polymorphic Definition tmDefinitionRed
: ident -> option reductionStrategy -> forall {A:Type}, A -> TemplateMonad A :=
  @tmDefinitionRed_ false.
Polymorphic Definition tmOpaqueDefinitionRed
: ident -> option reductionStrategy -> forall {A:Type}, A -> TemplateMonad A :=
  @tmDefinitionRed_ true.

Definition print_nf {A} (msg : A) : TemplateMonad unit
  := tmBind (tmEval all msg) tmPrint.

Definition fail_nf {A} (msg : string) : TemplateMonad A
  := tmBind (tmEval all msg) tmFail.

Definition tmMkInductive' (mind : mutual_inductive_body) : TemplateMonad unit
  := tmMkInductive (mind_body_to_entry mind).

Definition tmAxiom id := tmAxiomRed id None.
Definition tmDefinition id {A} t := @tmDefinitionRed_ false id None A t.

(* Don't remove. Constants used in the implem of the plugin *)
Definition tmTestQuote {A} (t : A) := tmBind (tmQuote t) tmPrint.
Definition tmQuoteDefinition id {A} (t : A) := tmBind (tmQuote t) (tmDefinition id).
Definition tmQuoteDefinitionRed id rd {A} (t : A)
  := tmBind (tmEval rd t) (tmQuoteDefinition id).
Definition tmQuoteRecDefinition id {A} (t : A)
  := tmBind (tmQuoteRec t) (tmDefinition id).
Definition tmMkDefinition id (tm : term) : TemplateMonad unit
  := tmBind (tmUnquote tm)
            (fun t' => tmBind (tmEval (unfold "Template.TemplateMonad.Common.my_projT2") (my_projT2 t'))
            (fun t'' => tmBind (tmDefinitionRed id (Some (unfold "Template.TemplateMonad.Common.my_projT1")) t'')
            (fun _ => tmReturn tt))).
