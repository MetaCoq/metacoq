(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From MetaCoq.Template Require Import config utils Ast Induction LiftSubst UnivSubst.
From MetaCoq.Template Require AstUtils.
From MetaCoq.Checker Require Import Typing.
Require Import String.
Local Open Scope string_scope.
Set Asymmetric Patterns.

Existing Instance config.default_checker_flags.

(** The subject reduction property of the system.
    We comment this as otherwise extraction can produce "axioms to be realized"
    values that make extracted code useless, as type are in Type.
 *)
(*
Conjecture subject_reduction : forall (Σ : global_env_ext) Γ t u T,
    Σ ;;; Γ |- t : T -> red Σ Γ t u -> Σ ;;; Γ |- u : T.
*)
(** Weak Normalization: every term has a normal form *)

Definition normal (Σ : global_env) Γ t := { u & red1 Σ Γ t u } -> False.
(*
Conjecture weak_normalization : forall (Σ : global_env_ext) Γ t T,
    Σ ;;; Γ |- t : T -> { u & (red Σ Γ t u * normal Σ Γ u)%type }.
*)
