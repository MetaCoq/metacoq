(* Distributed under the terms of the MIT license. *)
From Coq Require Import Morphisms.
From MetaCoq.Template Require Export utils Universes BasicAst Environment Reflect.
From MetaCoq.PCUIC Require EnvironmentTyping.
From MetaCoq.PCUIC Require Export PCUICPrimitive.
From Equations Require Import Equations.
Require Vector Fin.
(*
Section Branch.
  Context {term : nat -> Type}.
  (* Parameterized by term types as they are not yet defined. *)
  Record branch := mk_branch {
    bcontext : list (context_decl term);
    (* Context of binders of the branch, including lets. *)
    bbody : term; (* The branch body *) }.
  Derive NoConfusion for branch.
End Branch.
Arguments branch : clear implicits.

(* Defined here since BasicAst does not have access to universe instances.
  Parameterized by term types as they are not yet defined. *)
Record predicate {term} := mk_predicate {
  pparams : list term; (* The parameters *)
  puinst : Instance.t; (* The universe instance *)
  pcontext : list (context_decl term); (* The predicate context,
    initially built from params and puinst *)
  preturn : term; (* The return type *) }.
  Derive NoConfusion for predicate.
Arguments predicate : clear implicits.
Arguments mk_predicate {_}.
  *)

Inductive context (P : nat -> Type) : nat -> Type :=
| tnil : context P 0
| tcons {n} : P n -> context P n -> context P (S n).

Inductive context_decl (term : nat -> Type) : nat -> Type :=
| vass {n} (na : aname) (ty : term n) : context_decl term n
| vdef {n} (na : aname) (ty : term n) (body : term n) : context_decl term n.

Definition context_gen (term : nat -> Type) :=
  context (context_decl term).

Definition shift n (f : nat -> Type) :=
  fun i => f (n + i).

Variant FixCoFix :=
  | Fix | CoFix.

(* Terms are well-scoped in a global environment *)

Variant global_reference :=
  | ConstRef (kn : kername)
  | IndRef (ind : inductive)
  | ConstructRef (ind : inductive) (k : nat).

Definition global_env (term : nat -> Type) := list (kername * term 0).

Fixpoint lookup_env {term} (Σ : global_env term) (kn : kername) : option (term 0) :=
  match Σ with
  | nil => None
  | d :: tl =>
    if eq_kername kn d.1 then Some d.2
    else lookup_env tl kn
  end.

Definition declared_constant {term} (Σ : global_env term) (id : kername) : Type :=
  ∑ decl, lookup_env Σ id = Some decl.
(*
Definition declared_minductive Σ mind decl :=
  lookup_env Σ mind = Some (InductiveDecl decl).

Definition declared_inductive Σ ind mdecl decl :=
  declared_minductive Σ (inductive_mind ind) mdecl /\
  List.nth_error mdecl.(ind_bodies) (inductive_ind ind) = Some decl.

Definition declared_constructor Σ cstr mdecl idecl cdecl : Prop :=
  declared_inductive Σ (fst cstr) mdecl idecl /\
  List.nth_error idecl.(ind_ctors) (snd cstr) = Some cdecl. *)

Inductive term {k : nat} : Type :=
| tRel (f : Fin.t k)
| tVar (i : ident) (* For free variables (e.g. in a goal) *)
| tEvar (n : nat) (l : list term)
| tSort (u : Universe.t)
| tProd (na : aname) (A : term) (B : @term Σ (S k))
| tLambda (na : aname) (A : term) (B : @term Σ (S k))
| tLetIn (na : aname) (b B : term) (t : @term Σ (S k))
| tApp (u v : term)
| tConst (kn : kername) (ui : Instance.t)
  (declared_constant Σ kn)
(* | tInd ind : inductive) (ui : Instance.t) *)
| tConstruct (ind : inductive) (n : nat) (ui : Instance.t)
| tCase {plen} (indn : case_info) (pparams : list term) (puinst : Instance.t)
  (pcontext : context_gen (shift k (@term Σ)) plen)
  (c : term)
  (brs : list (∑ brlen (ctx : context_gen (@term Σ) brlen), @term Σ (brlen + k)))
| tProj (p : projection) (c : term)
| tFix (e : FixCoFix) {n} (mfix : Vector.t (def term) n) (idx : Fin.t n)
(** We use faithful models of primitive type values in PCUIC *)
| tPrim (prim : prim_val term).

with branch {n : nat} := Type :=
| vass (na : aname) (t : term k)

with global_env : Type :=
.
