(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config Universes Loader.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping PCUICSN PCUICLiftSubst.
From MetaCoq.SafeChecker Require Import PCUICErrors PCUICWfEnv PCUICTypeChecker PCUICSafeChecker.
From Equations Require Import Equations.

Import MCMonadNotation.
Global Existing Instance default_checker_flags.
Global Existing Instance default_normalizing.

(* ********************************************************* *)
(* In this file we define a small plugin which proves        *)
(* the identity theorem for any sort using the safe checker. *)
(* ********************************************************* *)

Definition bAnon := {| binder_name := nAnon; binder_relevance := Relevant |}.
Definition bNamed s := {| binder_name := nNamed s; binder_relevance := Relevant |}.

Definition tImpl X Y := tProd bAnon X (lift0 1 Y).

Definition univ := Level.Level "s".

(* TODO move to SafeChecker *)

Definition gctx : global_env_ext := 
  ({| universes := (LevelSet.singleton univ, ConstraintSet.empty); declarations := [] |}, Monomorphic_ctx).

(** We use the environment checker to produce the proof that gctx, which is a singleton with only 
    universe "s" declared  is well-formed. *)

Definition kername_of_string (s : string) : kername :=
  (MPfile [], s).

Definition make_wf_env_ext (Σ : global_env_ext) : EnvCheck wf_env_ext :=
  '(exist Σ' pf) <- check_wf_ext Σ ;;
  ret Σ'.

Definition gctx_wf_env : wf_env_ext.
Proof.
  let wf_proof := eval hnf in (make_wf_env_ext gctx) in 
  match wf_proof with
  | CorrectDecl ?x => exact x
  | _ => fail "Couldn't prove the global environment is well-formed"
  end.
Defined.



(** There is always a proof of `forall x : Sort s, x -> x` *)

Definition inh (Σ : wf_env_ext) Γ T := (∑ t, ∥ typing Σ Γ t T ∥).

Definition check_inh (Σ : wf_env_ext) Γ (wfΓ : ∥ wf_local Σ Γ ∥) t {T} : typing_result (inh Σ Γ T) := 
  prf <- check_type_wf_env_fast Σ Γ wfΓ t (T := T) ;;
  ret (t; prf).

Ltac fill_inh t := 
  lazymatch goal with
  [ wfΓ : ∥ wf_local _ ?Γ ∥ |- inh ?Σ ?Γ ?T ] => 
    let t := uconstr:(check_inh Σ Γ wfΓ t (T:=T)) in
    let proof := eval lazy in t in
    match proof with
    | Checked ?d => exact_no_check d
    | TypeError ?e => 
        let str := eval cbn in (string_of_type_error Σ e) in
        fail "Failed to inhabit " T " : " str
    | _ => fail "Anomaly: unexpected return value: " proof
    end
  | [ |- inh _ ?Γ _ ] => fail "Missing local wellformedness assumption for" Γ
  end.
