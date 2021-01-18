(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Export utils Universes BasicAst
     Environment EnvironmentTyping.
From MetaCoq.PCUIC Require Export PCUICPrimitive.
From Equations Require Import Equations.
(** * AST of the Polymorphic Cumulative Calculus of Inductive Constructions

   This AST is a cleaned-up version of Coq's internal AST better suited for
   reasoning.
   In particular, it has binary applications and all terms are well-formed.
   Casts are absent as well. *)

Declare Scope pcuic.
Delimit Scope pcuic with pcuic.
Open Scope pcuic.

(** DO NOT USE firstorder, since the introduction of Ints and Floats, it became unusuable. *)
Ltac pcuicfo_gen tac :=
  simpl in *; intuition (simpl; intuition tac).

Tactic Notation "pcuicfo" := pcuicfo_gen auto.
Tactic Notation "pcuicfo" tactic(tac) := pcuicfo_gen tac.

Inductive term :=
| tRel (n : nat)
| tVar (i : ident) (* For free variables (e.g. in a goal) *)
| tEvar (n : nat) (l : list term)
| tSort (u : Universe.t)
| tProd (na : aname) (A B : term)
| tLambda (na : aname) (A t : term)
| tLetIn (na : aname) (b B t : term) (* let na := b : B in t *)
| tApp (u v : term)
| tConst (k : kername) (ui : Instance.t)
| tInd (ind : inductive) (ui : Instance.t)
| tConstruct (ind : inductive) (n : nat) (ui : Instance.t)
| tCase (indn : inductive * nat) (p c : term) (brs : list (nat * term)) (* # of parameters/type info/discriminee/branches *)
| tProj (p : projection) (c : term)
| tFix (mfix : mfixpoint term) (idx : nat)
| tCoFix (mfix : mfixpoint term) (idx : nat)
(** We use faithful models of primitive type values in PCUIC *)
| tPrim (prim : prim_val term).

Derive NoConfusion for term.

Notation prim_val := (prim_val term).

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

Derive NoConfusion for parameter_entry definition_entry constant_entry.

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

Inductive local_entry :=
| LocalDef : term -> local_entry (* local let binding *)
| LocalAssum : term -> local_entry.

Record one_inductive_entry := {
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

Derive NoConfusion for local_entry one_inductive_entry mutual_inductive_entry.

Module PCUICTerm <: Term.

  Definition term := term.

  Definition tRel := tRel.
  Definition tSort := tSort.
  Definition tProd := tProd.
  Definition tLambda := tLambda.
  Definition tLetIn := tLetIn.
  Definition tInd := tInd.
  Definition tProj := tProj.
  Definition mkApps := mkApps.

End PCUICTerm.

Ltac unf_term := unfold PCUICTerm.term in *; unfold PCUICTerm.tRel in *;
                  unfold PCUICTerm.tSort in *; unfold PCUICTerm.tProd in *;
                  unfold PCUICTerm.tLambda in *; unfold PCUICTerm.tLetIn in *;
                  unfold PCUICTerm.tInd in *; unfold PCUICTerm.tProj in *.

Module PCUICEnvironment := Environment PCUICTerm.
Include PCUICEnvironment.

Module PCUICLookup := Lookup PCUICTerm PCUICEnvironment.
Include PCUICLookup.

Derive NoConfusion for global_decl context_decl.
