(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils.

Require Import ssreflect.

Definition relevance_of_constant Σ kn :=
  match lookup_constant Σ kn with
  | Some decl => decl.(cst_relevance)
  | None => Relevant
  end.

Definition relevance_of_constructor Σ ind (k : nat) :=
  match lookup_inductive Σ ind with
  | Some (_, idecl) => idecl.(ind_relevance)
  | None => Relevant
  end.

Definition relevance_of_projection Σ (p: projection) :=
  match lookup_projection Σ p with
  | Some (_, _, _, pdecl) => pdecl.(proj_relevance)
  | None => Relevant
  end.

Definition mark_context := list relevance.
Definition marks_of_context (Γ: context) := List.map (binder_relevance ∘ decl_name) Γ.

Fixpoint relevance_of_term (Σ : global_env) (Γ : mark_context) (t: term) : relevance :=
  match t with
  | tRel n =>
      option_default id (nth_error Γ n) Relevant
  | tLambda na A t => relevance_of_term Σ (Γ ,, na.(binder_relevance)) t
  | tLetIn na b B t => relevance_of_term Σ (Γ ,, na.(binder_relevance)) t
  | tApp u _ => relevance_of_term Σ Γ u
  | tConst k _ => relevance_of_constant Σ k
  | tConstruct ind i _ => relevance_of_constructor Σ ind i
  | tCase ci _ _ _ => ci.(ci_relevance)
  | tProj p _ => relevance_of_projection Σ p
  | tFix mfix n | tCoFix mfix n => option_default (binder_relevance ∘ dname) (nth_error mfix n) Relevant
  | tVar _ | tEvar _ _ | tSort _ | tProd _ _ _ | tInd _ _ => Relevant
  end.

Notation isTermRel Σ Γ t rel := (relevance_of_term Σ Γ t = rel).

Lemma mark_of_context_app Γ Γ' Δ Δ' :
  marks_of_context Γ = marks_of_context Γ' -> marks_of_context Δ = marks_of_context Δ' -> marks_of_context (Γ,,, Δ) = marks_of_context (Γ',,, Δ').
Proof.
  rewrite /marks_of_context !map_app; congruence.
Qed.
