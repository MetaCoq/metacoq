(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils.

Require Import ssreflect.

Definition mark_context := list relevance.
Definition marks_of_context (Γ: context) := List.map (binder_relevance ∘ decl_name) Γ.

Inductive isTermRel (Σ : global_env) (Γ : mark_context) : term -> relevance -> Type :=
  | rel_Rel n rel :
      nth_error Γ n = Some rel -> isTermRel Σ Γ (tRel n) rel

  | rel_Lambda na A t rel :
      isTermRel Σ (Γ ,, na.(binder_relevance)) t rel -> isTermRel Σ Γ (tLambda na A t) rel
  
  | rel_LetIn na b B t rel :
      isTermRel Σ (Γ ,, na.(binder_relevance)) t rel -> isTermRel Σ Γ (tLetIn na b B t) rel
  
  | rel_App t u rel :
      isTermRel Σ Γ t rel -> isTermRel Σ Γ (tApp t u) rel
  
  | rel_Const kn u decl :
      declared_constant Σ kn decl -> isTermRel Σ Γ (tConst kn u) decl.(cst_relevance)
  
  | rel_Construct ind i u mdecl idecl cdecl :
      declared_constructor Σ (ind, i) mdecl idecl cdecl -> isTermRel Σ Γ (tConstruct ind i u) idecl.(ind_relevance)
  
  | rel_Case ci p c brs :
      isTermRel Σ Γ (tCase ci p c brs) ci.(ci_relevance)
  
  | rel_Proj p u mdecl idecl cdecl pdecl :
      declared_projection Σ p mdecl idecl cdecl pdecl -> isTermRel Σ Γ (tProj p u) pdecl.(proj_relevance)
  
  | rel_Fix mfix n def :
      nth_error mfix n = Some def -> isTermRel Σ Γ (tFix mfix n) def.(dname).(binder_relevance)
  
  | rel_CoFix mfix n def :
      nth_error mfix n = Some def -> isTermRel Σ Γ (tCoFix mfix n) def.(dname).(binder_relevance)
  
  | rel_Sort s :
      isTermRel Σ Γ (tSort s) Relevant
  
  | rel_Prod na A B :
      isTermRel Σ Γ (tProd na A B) Relevant
  
  | rel_Ind ind u :
      isTermRel Σ Γ (tInd ind u) Relevant. 

Derive Signature for isTermRel.

Lemma mark_of_context_app Γ Γ' Δ Δ' :
  marks_of_context Γ = marks_of_context Γ' -> marks_of_context Δ = marks_of_context Δ' -> marks_of_context (Γ,,, Δ) = marks_of_context (Γ',,, Δ').
Proof.
  rewrite /marks_of_context !map_app; congruence.
Qed.
