From Coq Require Import String List ZArith.
From MetaCoq.Template Require config utils All.
From MetaCoq.Template Require Import BasicAst TemplateMonad monad_utils.
From MetaCoq.PCUIC Require Import TemplateToPCUIC.
Import MCMonadNotation.
Local Open Scope string_scope.
Import ListNotations.

(* From MetaCoq.PCUIC Require Import PCUICAst PCUICReduction PCUICCumulativity PCUICTyping PCUICSafeLemmata. *)

From MetaCoq.Template Require Import Universes.
Declare Custom Entry term.
Module LevelsToIndices.
Import Ast.

(* Conversion from de Bruijn levels to indices *)
Fixpoint toDB k (t : term) : term :=
  match t with 
  | tRel n => Ast.tRel (k - n)
  | tVar id => Ast.tVar id
  | tEvar ev args => Ast.tEvar ev (List.map (toDB k) args)
  | tSort s => Ast.tSort s
  | tCast t ck u => Ast.tCast (toDB k t) ck (toDB k u)
  | tProd na ty body => Ast.tProd na (toDB k ty) (toDB (S k) body)
  | tLambda na ty body => Ast.tLambda na (toDB k ty) (toDB (S k) body)
  | tApp f args => Ast.tApp (toDB k f) (List.map (toDB k) args)
  | tConst c u => Ast.tConst c u
  | tInd c u => Ast.tInd c u
  | tConstruct c k u => Ast.tConstruct c k u
  | _ => Ast.tInt (Int63.of_Z 0%Z)
  end.
End LevelsToIndices.

Module PHOAS.
Inductive term {var : Type} | : Type :=
| tRel (n : var)
| tVar (id : ident) (* For free variables (e.g. in a goal) *)
| tEvar (ev : nat) (args : list term)
| tSort (s : Universe.t)
| tCast (t : term) (kind : cast_kind) (v : term)
| tProd (na : aname) (ty : term) (body : var -> term)
| tLambda (na : aname) (ty : term) (body : var -> term)
| tLetIn (na : aname) (def : term) (def_ty : term) (body : var -> term)
| tApp (f : term) (args : list term)
| tConst (c : kername) (u : Instance.t)
| tInd (ind : inductive) (u : Instance.t)
| tConstruct (ind : inductive) (idx : nat) (u : Instance.t)
| tCase (ind_nbparams_relevance: inductive*nat*relevance) (type_info:term)
        (discr:term) (branches : list (nat * term))
| tProj (proj : projection) (t : term)
| tFix (mfix : mfixpoint term) (idx : nat)
| tCoFix (mfix : mfixpoint term) (idx : nat)
| tInt (i : Int63.int)
| tFloat (f : PrimFloat.float).
Arguments term : clear implicits.

(* To de Bruijn indices *)
Fixpoint toDB k (t : term nat) : Ast.term :=
  match t with 
  | tRel n => Ast.tRel (k - S n)
  | tVar id => Ast.tVar id
  | tEvar ev args => Ast.tEvar ev (List.map (toDB k) args)
  | tSort s => Ast.tSort s
  | tCast t ck u => Ast.tCast (toDB k t) ck (toDB k u)
  | tProd na ty body => Ast.tProd na (toDB k ty) (toDB (S k) (body k))
  | tLambda na ty body => Ast.tLambda na (toDB k ty) (toDB (S k) (body k))
  | tLetIn na ty b body => Ast.tLetIn na (toDB k ty) (toDB k b) (toDB (S k) (body k))
  | tApp f args => Ast.tApp (toDB k f) (List.map (toDB k) args)
  | tConst c u => Ast.tConst c u
  | tInd c u => Ast.tInd c u
  | tConstruct c k u => Ast.tConstruct c k u
  | tCase i t d brs => 
    Ast.tCase i (toDB k t) (toDB k d) (List.map (fun '(x, y) => (x, toDB k y)) brs)
  | tProj p t => Ast.tProj p (toDB k t)
  | tFix mfix idx => 
    let mfix' := List.map (map_def (toDB k) (toDB (k + length mfix))) mfix in
    Ast.tFix mfix' idx
  | tCoFix mfix idx => 
    let mfix' := List.map (map_def (toDB k) (toDB (k + length mfix))) mfix in
    Ast.tCoFix mfix' idx
  | tInt i => Ast.tInt i
  | tFloat f => Ast.tFloat f
  end.

  Definition tImpl {var} (A B : term var) := tProd bAnon A (fun _ => B).
End PHOAS.
Definition term := forall var, PHOAS.term var.

(* Definition of_phoas {A} (t : term A) : term :=  *)

Definition myterm := PHOAS.term nat.
Definition nat_rel : nat -> myterm := PHOAS.tRel.

Notation "[!  e ]" := (e : myterm) (e custom term at level 200).
Notation "( e )" := e (e custom term, in custom term).
Notation "t1 t2" := (PHOAS.tApp t1 [t2]) (in custom term at level 4, left associativity).

Notation "'Type' u" := (PHOAS.tSort u) (u constr, in custom term at level 0).
Notation "'Type0'" := (PHOAS.tSort Universe.type0) (in custom term at level 0).
Notation "'Type1'" := (PHOAS.tSort Universe.type1) (in custom term at level 0).
Notation "'Π' x @ ( na , A ) , B" := (PHOAS.tProd (bNamed na) A (fun x => B))
                         (in custom term at level 4, right associativity,
                             x binder,
                             na constr,
                             A custom term at level 4,
                             B custom term at level 4).
Notation "A → B" := (PHOAS.tImpl A B)
  (in custom term at level 4, right associativity,
    A custom term,
    B custom term at level 4).
    
Notation "'λ' x @ ( na , A ) , B" := (PHOAS.tLambda (bNamed na) A (fun x : _ => B)) 
  (in custom term at level 4, right associativity,
  x binder,
  na constr,
  A custom term at level 4,
  B custom term at level 4).

Notation "' x" := (PHOAS.tRel x) (in custom term at level 0, x constr at level 2, format "' x").
Notation "{ x }" := x (x constr, in custom term).

Definition of_phoas (t : myterm) : PCUICAst.term := 
  TemplateToPCUIC.trans (PHOAS.toDB 0 t).

Coercion of_phoas : myterm >-> PCUICAst.term.

Coercion nat_rel : nat >-> myterm.

(* Definition tnat {var} : PHOAS.term var  := PHOAS.tInd
  {|
  	inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
    inductive_ind := 0
  |} []. *)

(* Type [! λ x @ ("x", { tnat }), λ x' @ ("x", { tnat }), λ y @ ("y", Type0), 'y 'x]. *)
