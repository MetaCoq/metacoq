(* Distributed under the terms of the MIT license.   *)

Require Import Coq.Strings.String.
Require Import Coq.PArith.BinPos.
Require Import List. Import ListNotations.
From MetaCoq.Template Require Export Universes BasicAst.

(* Declare Scope pcuic.*)
Delimit Scope pcuic with pcuic.
Open Scope pcuic.

(** * AST of the Polymorphic Cumulative Calculus of Inductive Constructions

   This AST is a cleaned-up version of Coq's internal AST better suited for reasoning.
   In particular, it has binary applications and all terms are well-formed.
   Casts are absent as well. *)

Inductive term : Set :=
| tRel (n : nat)
| tVar (i : ident) (* For free variables (e.g. in a goal) *)
| tEvar (n : nat) (l : list term)
| tSort (u : universe)
| tProd (na : name) (A B : term)
| tLambda (na : name) (A t : term)
| tLetIn (na : name) (b B t : term) (* let na := b : B in t *)
| tApp (u v : term)
| tConst (k : kername) (ui : universe_instance)
| tInd (ind : inductive) (ui : universe_instance)
| tConstruct (ind : inductive) (n : nat) (ui : universe_instance)
| tCase (indn : inductive * nat) (p c : term) (brs : list (nat * term)) (* # of parameters/type info/discriminee/branches *)
| tProj (p : projection) (c : term)
| tFix (mfix : mfixpoint term) (idx : nat)
| tCoFix (mfix : mfixpoint term) (idx : nat).

Fixpoint mkApps t us :=
  match us with
  | nil => t
  | u :: us => mkApps (tApp t u) us
  end.

Definition isApp t :=
  match t with
  | tApp _ _ => true
  | _ => false
  end.

Definition isLambda t :=
  match t with
  | tLambda _ _ _ => true
  | _ => false
  end.

(** ** Entries

  The kernel accepts these inputs and typechecks them to produce
  declarations. Reflects [kernel/entries.mli].
*)

(** *** Constant and axiom entries *)

Record parameter_entry := {
  parameter_entry_type      : term;
  parameter_entry_universes : universes_decl }.

Record definition_entry := {
  definition_entry_type      : term;
  definition_entry_body      : term;
  definition_entry_universes : universes_decl;
  definition_entry_opaque    : bool }.


Inductive constant_entry :=
| ParameterEntry  (p : parameter_entry)
| DefinitionEntry (def : definition_entry).

(** *** Inductive entries *)

(** This is the representation of mutual inductives.
    nearly copied from [kernel/entries.mli]

  Assume the following definition in concrete syntax:

[[
  Inductive I1 (x1:X1) ... (xn:Xn) : A1 := c11 : T11 | ... | c1n1 : T1n1
  ...
  with      Ip (x1:X1) ... (xn:Xn) : Ap := cp1 : Tp1  ... | cpnp : Tpnp.
]]

  then, in [i]th block, [mind_entry_params] is [xn:Xn;...;x1:X1];
  [mind_entry_arity] is [Ai], defined in context [x1:X1;...;xn:Xn];
  [mind_entry_lc] is [Ti1;...;Tini], defined in context
  [A'1;...;A'p;x1:X1;...;xn:Xn] where [A'i] is [Ai] generalized over
  [x1:X1;...;xn:Xn].
*)

Inductive local_entry : Set :=
| LocalDef : term -> local_entry (* local let binding *)
| LocalAssum : term -> local_entry.

Record one_inductive_entry : Set := {
  mind_entry_typename : ident;
  mind_entry_arity : term;
  mind_entry_template : bool; (* template polymorphism *)
  mind_entry_consnames : list ident;
  mind_entry_lc : list term (* constructor list *) }.

Record mutual_inductive_entry := {
  mind_entry_record    : option (option ident);
  (* Is this mutual inductive defined as a record?
     If so, is it primitive, using binder name [ident]
     for the record in primitive projections ? *)
  mind_entry_finite    : recursivity_kind;
  mind_entry_params    : list (ident * local_entry);
  mind_entry_inds      : list one_inductive_entry;
  mind_entry_universes : universes_decl;
  mind_entry_private   : option bool
  (* Private flag for sealing an inductive definition in an enclosing
     module. Not handled by Template Coq yet. *) }.



(** ** Declarations *)

(** *** The context of De Bruijn indices *)

Record context_decl := {
  decl_name : name ;
  decl_body : option term ;
  decl_type : term }.

(** Local (de Bruijn) variable binding *)

Definition vass x A := {| decl_name := x; decl_body := None; decl_type := A |}.

(** Local (de Bruijn) let-binding *)

Definition vdef x t A := {| decl_name := x; decl_body := Some t; decl_type := A |}.

(** Local (de Bruijn) context *)

Definition context := list context_decl.

(** Last declaration first *)

Definition snoc {A} (Γ : list A) (d : A) := d :: Γ.

Notation " Γ ,, d " := (snoc Γ d) (at level 20, d at next level) : pcuic.

(** *** Environments *)

(** See [one_inductive_body] from [declarations.ml]. *)
Record one_inductive_body := {
  ind_name : ident;
  ind_type : term; (* Closed arity *)
  ind_kelim : list sort_family; (* Allowed elimination sorts *)
  ind_ctors : list (ident * term (* Under context of arities of the mutual inductive *)
                    * nat (* arity, w/o lets, w/o parameters *));
  ind_projs : list (ident * term) (* names and types of projections, if any.
                                     Type under context of params and inductive object *) }.

(** See [mutual_inductive_body] from [declarations.ml]. *)
Record mutual_inductive_body := {
  ind_finite : recursivity_kind;
  ind_npars : nat;
  ind_params : context;
  ind_bodies : list one_inductive_body ;
  ind_universes : universes_decl }.

(** See [constant_body] from [declarations.ml] *)
Record constant_body := {
    cst_type : term;
    cst_body : option term;
    cst_universes : universes_decl }.

Inductive global_decl :=
| ConstantDecl : kername -> constant_body -> global_decl
| InductiveDecl : kername -> mutual_inductive_body -> global_decl.

Definition global_env := list global_decl.

(** A context of global declarations + global universe constraints,
    i.e. a global environment *)

Definition global_env_ext : Type := global_env * universes_decl.

(** *** Programs

  A set of declarations and a term, as produced by [Quote Recursively]. *)

Definition program : Type := global_env * term.
