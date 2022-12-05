(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import utils Ast AstUtils Common.

Local Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
Import MCMonadNotation.

(** * The Template Monad

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

(* Returns the list of globrefs corresponding to a qualid,
   the head is the default one if any. *)
| tmLocate : qualid -> TemplateMonad (list global_reference)
| tmCurrentModPath : unit -> TemplateMonad modpath

(* Quoting and unquoting commands *)
(* Similar to MetaCoq Quote Definition ... := ... *)
| tmQuote : forall {A:Type@{t}}, A  -> TemplateMonad Ast.term
(* Similar to MetaCoq Quote Recursively Definition but takes a boolean "bypass opacity" flag.
  ([true] - quote bodies of all dependencies (transparent and opaque);
   [false] -quote bodies of transparent definitions only) *)
| tmQuoteRecTransp : forall {A:Type@{t}}, A -> bool(* bypass opacity? *) -> TemplateMonad program
(* Quote the body of a definition or inductive. Its name need not be fully qualified *)
| tmQuoteInductive : kername -> TemplateMonad mutual_inductive_body
| tmQuoteUniverses : TemplateMonad ConstraintSet.t
| tmQuoteConstant : kername -> bool (* bypass opacity? *) -> TemplateMonad constant_body
| tmQuoteModule : qualid -> TemplateMonad (list global_reference)
(* unquote before making the definition *)
(* FIXME take an optional universe context as well *)
| tmMkInductive : bool -> mutual_inductive_entry -> TemplateMonad unit
| tmUnquote : Ast.term  -> TemplateMonad typed_term@{u}
| tmUnquoteTyped : forall A : Type@{t}, Ast.term -> TemplateMonad A

(* Typeclass registration and querying for an instance *)
(* Rk: This is *Global* Existing Instance, not Local *)
| tmExistingInstance : global_reference -> TemplateMonad unit
| tmInferInstance : option reductionStrategy -> forall A : Type@{t}, TemplateMonad (option_instance A)
.

(** This allow to use notations of MonadNotation *)
Global Instance TemplateMonad_Monad@{t u} : Monad@{t u} TemplateMonad@{t u} :=
  {| ret := @tmReturn ; bind := @tmBind |}.

Polymorphic Definition tmDefinitionRed
: ident -> option reductionStrategy -> forall {A:Type}, A -> TemplateMonad A :=
  @tmDefinitionRed_ false.
Polymorphic Definition tmOpaqueDefinitionRed
: ident -> option reductionStrategy -> forall {A:Type}, A -> TemplateMonad A :=
  @tmDefinitionRed_ true.

Definition print_nf {A} (msg : A) : TemplateMonad unit
  := tmEval all msg >>= tmPrint.

Definition fail_nf {A} (msg : string) : TemplateMonad A
  := tmEval all msg >>= tmFail.

Definition tmMkInductive' (mind : mutual_inductive_body) : TemplateMonad unit
  := tmMkInductive false (mind_body_to_entry mind).

Definition tmAxiom id := tmAxiomRed id None.
Definition tmDefinition id {A} t := @tmDefinitionRed_ false id None A t.

(** We keep the original behaviour of [tmQuoteRec]: it quotes all the dependencies regardless of the opaqueness settings *)
Definition tmQuoteRec {A} (a : A) := tmQuoteRecTransp a true.

Definition tmLocate1 (q : qualid) : TemplateMonad global_reference :=
  l <- tmLocate q ;;
  match l with
  | [] => tmFail ("Constant [" ^ q ^ "] not found")
  | x :: _ => tmReturn x
  end.

(** Don't remove. Constants used in the implem of the plugin *)
Definition tmTestQuote {A} (t : A) := tmQuote t >>= tmPrint.

Definition Common_kn (s : ident) :=
  (MPfile ["Common"; "TemplateMonad"; "Template"; "MetaCoq"], s).
Definition tmTestUnquote (t : term) :=
     t' <- tmUnquote t ;;
     t'' <- tmEval (unfold (Common_kn "my_projT2")) (my_projT2 t') ;;
     tmPrint t''.

Definition tmQuoteDefinition id {A} (t : A) := tmQuote t >>= tmDefinition id.
Definition tmQuoteDefinitionRed id rd {A} (t : A)
  := tmEval rd t >>= tmQuoteDefinition id.
Definition tmQuoteRecDefinition id {A} (t : A)
  := tmQuoteRec t >>= tmDefinition id.

Definition tmMkDefinition (id : ident) (tm : term) : TemplateMonad unit
  := t' <- tmUnquote tm ;;
     t'' <- tmEval (unfold (Common_kn "my_projT2")) (my_projT2 t') ;;
     tmDefinitionRed id (Some (unfold (Common_kn "my_projT1"))) t'' ;;
     tmReturn tt.

Definition TypeInstance : Common.TMInstance :=
  {| Common.TemplateMonad := TemplateMonad
   ; Common.tmReturn:=@tmReturn
   ; Common.tmBind:=@tmBind
   ; Common.tmFail:=@tmFail
   ; Common.tmFreshName:=@tmFreshName
   ; Common.tmLocate:=@tmLocate
   ; Common.tmCurrentModPath:=@tmCurrentModPath
   ; Common.tmQuoteInductive:=@tmQuoteInductive
   ; Common.tmQuoteUniverses:=@tmQuoteUniverses
   ; Common.tmQuoteConstant:=@tmQuoteConstant
   ; Common.tmMkInductive:=@tmMkInductive
   ; Common.tmExistingInstance:=@tmExistingInstance
   |}.

Definition tmQuoteUniverse@{U t u} : TemplateMonad@{t u} Universe.t
  := u <- @tmQuote Prop (Type@{U} -> True);;
     match u with
     | tProd _ (tSort u) _ => ret u
     | _ => tmFail "Anomaly: tmQuote (Type -> True) should be (tProd _ (tSort _) _)!"%bs
     end.
Definition tmQuoteLevel@{U t u} : TemplateMonad@{t u} Level.t
  := u <- tmQuoteUniverse@{U t u};;
     match Universe.get_is_level u with
     | Some l => ret l
     | None => tmFail "Universe is not a level"%bs
     end.

Definition tmFix'@{a b t u} {A : Type@{a}} {B : Type@{b}} (qtmFix' : Ast.term) (f : (A -> TemplateMonad@{t u} B) -> (A -> TemplateMonad@{t u} B)) : A -> TemplateMonad@{t u} B
  := f (fun a
        => tmFix <- tmUnquoteTyped (Ast.term -> ((A -> TemplateMonad@{t u} B) -> (A -> TemplateMonad@{t u} B)) -> A -> TemplateMonad@{t u} B) qtmFix';;
           tmFix qtmFix' f a).
Definition tmFix@{a b t u} {A : Type@{a}} {B : Type@{b}} (f : (A -> TemplateMonad@{t u} B) -> (A -> TemplateMonad@{t u} B)) : A -> TemplateMonad@{t u} B
  := f (fun a
        => (qA <- tmQuote A;;
            qB <- tmQuote B;;
            qa <- tmQuoteLevel@{a _ _};;
            qb <- tmQuoteLevel@{b _ _};;
            qt <- tmQuoteLevel@{t _ _};;
            qu <- tmQuoteLevel@{u _ _};;
            let self := tConst (MPfile ["Core"; "TemplateMonad"; "Template"; "MetaCoq"], "tmFix'")%bs [qa;qb;qt;qu] in
            @tmFix'@{a b t u} A B (mkApps self [qA; qB]) f a)).
