(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config Universes All.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping PCUICLiftSubst.
From MetaCoq.SafeChecker Require Import PCUICSafeChecker.
From Equations Require Import Equations.

Existing Instance default_checker_flags.

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
  ([], Monomorphic_ctx (LevelSet.singleton univ, ConstraintSet.empty)).

Obligation Tactic := idtac.
Program Definition check_wf_ext (Σ : global_env_ext) : EnvCheck (∑ G, is_graph_of_uctx G (global_ext_uctx Σ) * ∥ wf_ext Σ ∥) :=
  G <- check_wf_env Σ.1 ;;
  let '(G; p) := (G : ∑ G, is_graph_of_uctx G (global_uctx Σ) /\ ∥ wf Σ ∥) in
  uctx <- check_udecl "toplevel term" Σ.1 (proj2 p) G (proj1 p) Σ.2 ;;
  let '(uctx'; conj eq onudecl) := (uctx : ∑ uctx, _ /\ _) in
  let G' := add_uctx uctx' G in
  ret (G'; _).
Next Obligation. simpl. 
  simpl; intros. subst. destruct p. split.
  unfold is_graph_of_uctx, gc_of_uctx in *; simpl.
  destruct Σ as [Σ univs]. simpl in *.
  simpl in H. simpl. 
  case_eq (gc_of_constraints (constraints_of_udecl univs));
    [|intro HH; rewrite HH in eq; discriminate eq].
  intros ctrs' Hctrs'. rewrite Hctrs' in eq.
  noconf eq.
  unfold global_ext_constraints; simpl.
  rewrite gc_of_constraints_union. rewrite Hctrs'.
  red in H. unfold gc_of_uctx in H; simpl in H.
  destruct (gc_of_constraints (global_constraints Σ)) eqn:HΣcstrs; auto.
  simpl. unfold global_ext_levels; simpl. rewrite no_prop_levels_union.
  subst G. symmetry. apply add_uctx_make_graph.
  sq; split; auto.
Defined.

Record wf_env {cf:checker_flags} := { 
    wf_env_env :> global_env_ext;
    wf_env_wf :> ∥ wf_ext wf_env_env ∥;
    wf_env_graph :> universes_graph;
    wf_env_graph_wf : is_graph_of_uctx wf_env_graph (global_ext_uctx wf_env_env)
}.

Definition wf_env_sq_wf (Σ : wf_env) : ∥ wf Σ ∥.
Proof.
  destruct (wf_env_wf Σ).
  sq. apply X.
Defined.

Definition make_wf_env Σ : EnvCheck wf_env :=
  Gwf <- check_wf_ext Σ ;;
  let '(G; p) := (Gwf : ∑ G, _ * _) in
  ret {| wf_env_env := Σ; wf_env_wf := p.2; 
        wf_env_graph := G; wf_env_graph_wf := p.1 |}.

(** We use the environment checker to produce the proof that gctx, which is a singleton with only 
    universe "s" declared  is well-formed. *)
Definition gctx_wf_env : wf_env.
Proof.
  let wf_proof := eval hnf in (make_wf_env gctx) in 
  match wf_proof with
  | CorrectDecl ?x => exact x
  | _ => fail "Couldn't prove the global environment is well-formed"
  end.
Defined.

Definition check_wf_env_ext {cf:checker_flags} (Σ : global_env_ext) (wfΣ : ∥ wf_ext Σ ∥) 
    (G : universes_graph) (HG : is_graph_of_uctx G (global_ext_uctx Σ)) Γ (wfΓ : ∥ wf_local Σ Γ ∥) t T : typing_result (∥ Σ ;;; Γ |- t : T ∥) := 
  @check cf Σ (let 'sq wfΣ := wfΣ in sq wfΣ.1) (let 'sq wfΣ := wfΣ in sq wfΣ.2) G HG Γ wfΓ t T.

Definition check_wf_env {cf:checker_flags} (Σ : wf_env) Γ (wfΓ : ∥ wf_local Σ Γ ∥) t T : typing_result (∥ Σ ;;; Γ |- t : T ∥) := 
  check_wf_env_ext Σ (wf_env_wf Σ) Σ (wf_env_graph_wf Σ) Γ wfΓ t T.

(** There is always a proof of `forall x : Sort s, x -> x` *)

Definition inh {cf:checker_flags} (Σ : wf_env) Γ T := ∑ t, ∥ Σ ;;; Γ |- t : T ∥.

Definition check_inh {cf:checker_flags} (Σ : wf_env) Γ (wfΓ : ∥ wf_local Σ Γ ∥) t {T} : typing_result (inh Σ Γ T) := 
  d <- check_wf_env Σ Γ wfΓ t T ;;
  ret (t; d).

Ltac fill_inh t := 
  lazymatch goal with
  [ wfΓ : ∥ wf_local _ ?Γ ∥ |- inh ?Σ ?Γ ?T ] => 
    let t := constr:(check_inh Σ Γ wfΓ t (T:=T)) in
    let proof := eval hnf in t in
    match proof with
    | Checked ?d => exact d
    | TypeError ?e => 
        let str := eval cbn in (string_of_type_error Σ e) in
        fail "Failed to inhabit " T " : " str
    | _ => fail "Anomaly: unexpected return value: " proof
    end
  | [ |- inh _ ?Γ _ ] => fail "Missing local wellformedness assumption for" Γ
  end.

Lemma identity_typing (u := Universe.make univ): inh gctx_wf_env [] (tProd (bNamed "s") (tSort u) (tImpl (tRel 0) (tRel 0))).
Proof.
  set (impl := tLambda (bNamed "s") (tSort u) (tLambda bAnon (tRel 0) (tRel 0))).
  assert (wfΓ : ∥ wf_local gctx_wf_env [] ∥) by do 2 constructor.
  Time fill_inh impl.
Time Qed. 

(* Qed time with lazy: 1min *)
(* hnf: fill_inh 3 sec, Qed time: 36s *)
(* vm_compute: fill_inh 10 sec, Qed time: 40s *)
(* If we had certicoq trusted it would be fast...*)