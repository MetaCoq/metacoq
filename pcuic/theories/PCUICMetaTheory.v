(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICLiftSubst PCUICUnivSubst PCUICTyping.
Require Import String.
Local Open Scope string_scope.
Set Asymmetric Patterns.

Local Existing Instance config.default_checker_flags.

(** The subject reduction property of the system: *)

(* Commented otherwise extraction would produce an axiom making the whole
   extracted code unusable *)
(* Conjecture subject_reduction : forall (Σ : global_env_ext) Γ t u T, *)
(*     Σ ;;; Γ |- t : T -> red Σ Γ t u -> Σ ;;; Γ |- u : T. *)

(** Weak Normalization: every term has a normal form *)

Definition normal (Σ : global_env_ext) Γ t := { u : _ & red1 Σ Γ t u } -> False.

Conjecture weak_normalization : forall (Σ : global_env_ext) Γ t T,
    Σ ;;; Γ |- t : T -> { u & (red Σ Γ t u * normal Σ Γ u)%type }.
