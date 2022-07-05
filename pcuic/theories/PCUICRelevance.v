(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils.

Require Import ssreflect.

Lemma mark_of_context_app Γ Γ' Δ Δ' :
  marks_of_context Γ = marks_of_context Γ' -> marks_of_context Δ = marks_of_context Δ' -> marks_of_context (Γ,,, Δ) = marks_of_context (Γ',,, Δ').
Proof.
  rewrite /marks_of_context !map_app; congruence.
Qed.
