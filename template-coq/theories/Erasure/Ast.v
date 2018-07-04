(* Distributed under the terms of the MIT license.   *)

Require Import Coq.Strings.String.
Require Import Coq.PArith.BinPos.
Require Import List. Import ListNotations.
From Template Require Import monad_utils.
From Template Require Export univ uGraph Ast.

(** Erased terms

  These are the terms produced by erasure:
  compared to kernel terms, all proofs are translated to [tBox] and
  casts are removed.
*)

Inductive term : Set :=
| tBox       : term (* Represents all proofs *)
| tRel       : nat -> term
| tVar       : ident -> term (* For free variables (e.g. in a goal) *)
| tMeta      : nat -> term   (* NOTE: this will go away *)
| tEvar      : nat -> list term -> term
| tSort      : universe -> term
| tProd      : name -> term (* the type *) -> term -> term
| tLambda    : name -> term -> term -> term
| tLetIn     : name -> term (* the term *) -> term -> term -> term
| tApp       : term -> list term -> term
| tConst     : kername -> universe_instance -> term
| tInd       : inductive -> universe_instance -> term
| tConstruct : inductive -> nat -> universe_instance -> term
| tCase      : (inductive * nat) (* # of parameters *) -> term (* type info *)
               -> term (* discriminee *) -> list (nat * term) (* branches *) -> term
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

Definition isApp t :=
  match t with
  | tApp _ _ => true
  | _ => false
  end.

(** Well-formed terms: invariants which are not ensured by the OCaml type system *)

Inductive wf : term -> Prop :=
| wf_tBox : wf tBox
| wf_tRel n : wf (tRel n)
| wf_tVar id : wf (tVar id)
| wf_tMeta n : wf (tMeta n)
| wf_tEvar n l : Forall wf l -> wf (tEvar n l)
| wf_tSort u : wf (tSort u)
| wf_tProd na t b : wf t -> wf b -> wf (tProd na t b)
| wf_tLambda na t b : wf t -> wf b -> wf (tLambda na t b)
| wf_tLetIn na t b b' : wf t -> wf b -> wf b' -> wf (tLetIn na t b b')
| wf_tApp t u : ~ isApp t = true -> u <> nil -> wf t -> Forall wf u -> wf (tApp t u)
| wf_tConst k u : wf (tConst k u)
| wf_tInd i u : wf (tInd i u)
| wf_tConstruct i k u : wf (tConstruct i k u)
| wf_tCase ci p c brs : wf p -> wf c -> Forall (Program.Basics.compose wf snd) brs -> wf (tCase ci p c brs)
| wf_tProj p t : wf t -> wf (tProj p t)
| wf_tFix mfix k : Forall (fun def => wf def.(dtype _) /\ wf def.(dbody _)) mfix -> wf (tFix mfix k)
| wf_tCoFix mfix k : Forall (fun def => wf def.(dtype _) /\ wf def.(dbody _)) mfix -> wf (tCoFix mfix k).

(** ** Entries

  The kernel accepts these inputs and typechecks them to produce
  declarations. Reflects [kernel/entries.mli].
*)

(** *** Constant and axiom entries *)

Record parameter_entry := {
  parameter_entry_type      : term;
  parameter_entry_universes : universe_context }.

Record definition_entry := {
  definition_entry_type      : term;
  definition_entry_body      : term;
  definition_entry_universes : universe_context;
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

Inductive recursivity_kind :=
  | Finite (* = inductive *)
  | CoFinite (* = coinductive *)
  | BiFinite (* = non-recursive, like in "Record" definitions *).

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
  mind_entry_universes : universe_context;
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

Notation " Γ ,, d " := (snoc Γ d) (at level 20, d at next level).

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
  ind_npars : nat;
  ind_bodies : list one_inductive_body ;
  ind_universes : universe_context }.

(** See [constant_body] from [declarations.ml] *)
Record constant_body := {
    cst_type : term;
    cst_body : option term;
    cst_universes : universe_context }.

Inductive global_decl :=
| ConstantDecl : kername -> constant_body -> global_decl
| InductiveDecl : kername -> mutual_inductive_body -> global_decl.

Definition global_declarations := list global_decl.

(** A context of global declarations + global universe constraints,
    i.e. a global environment *)

Definition global_context : Type := global_declarations * uGraph.t.

(** *** Programs

  A set of declarations and a term, as produced by [Quote Recursively]. *)

Definition program : Type := global_declarations * term.
