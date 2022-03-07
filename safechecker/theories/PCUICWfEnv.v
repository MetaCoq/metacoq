(* Distributed under the terms of the MIT license. *)
From Coq Require Import ssreflect.
From MetaCoq.Template Require Import config utils uGraph EnvMap.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICReflect PCUICTyping PCUICGlobalEnv.
  
(* We pack up all the information required on the global environment and graph in a 
single record. *)

Record wf_env {cf:checker_flags} := { 
  wf_env_env :> global_env;
  wf_env_map :> EnvMap.t global_decl;
  wf_env_map_repr :> EnvMap.repr wf_env_env.(declarations) wf_env_map;
  wf_env_wf :> ∥ wf wf_env_env ∥;
  wf_env_graph :> universes_graph;
  wf_env_graph_wf : is_graph_of_uctx wf_env_graph (global_uctx wf_env_env)
}.

Record wf_env_ext {cf:checker_flags} := { 
  wf_env_ext_env :> global_env_ext;
  wf_env_ext_map :> EnvMap.t global_decl;
  wf_env_ext_map_repr :> EnvMap.repr wf_env_ext_env.(declarations) wf_env_ext_map;
  wf_env_ext_wf :> ∥ wf_ext wf_env_ext_env ∥;
  wf_env_ext_graph :> universes_graph;
  wf_env_ext_graph_wf : is_graph_of_uctx wf_env_ext_graph (global_ext_uctx wf_env_ext_env)
}.

Lemma wf_fresh_globals {cf : checker_flags} Σ : wf Σ -> EnvMap.fresh_globals Σ.(declarations).
Proof. destruct Σ as [univs Σ]; cbn.
  move=> [] onu; cbn. induction 1; constructor; auto.
Qed.

Lemma of_global_env_cons {cf:checker_flags} d g : EnvMap.fresh_globals (add_global_decl g d).(declarations) ->
  EnvMap.of_global_env (add_global_decl g d).(declarations) = EnvMap.add d.1 d.2 (EnvMap.of_global_env g.(declarations)).
Proof.
  unfold EnvMap.of_global_env. simpl. unfold KernameMapFact.uncurry.
  reflexivity.
Qed.

Section WfEnv.
  Context {cf : checker_flags}.

  Definition wf_env_sq_wf (Σ : wf_env) : ∥ wf Σ ∥.
  Proof.
    destruct (wf_env_wf Σ).
    sq. apply X.
  Qed.

  Definition wf_env_ext_sq_wf (Σ : wf_env_ext) : ∥ wf Σ ∥.
  Proof.
    destruct (wf_env_ext_wf Σ).
    sq. apply X.
  Qed.

  Definition lookup (Σ : wf_env_ext) (kn : kername) : option global_decl :=
    EnvMap.lookup kn Σ.(wf_env_ext_map).

  Lemma lookup_lookup_env Σ kn : lookup Σ kn = lookup_env Σ kn.
  Proof.
    rewrite /lookup. destruct Σ as [Σ map repr [wfext] G HG].
    apply EnvMap.lookup_spec; auto. now eapply wf_fresh_globals.
  Qed.

End WfEnv.


Create HintDb wf_env discriminated.
Global Hint Constants Opaque : wf_env.
Global Hint Variables Opaque : wf_env.

Global Hint Resolve wf_env_ext_wf : wf_env.

Ltac unsquash_wf_env := 
  match goal with
  | Σ : wf_env_ext |- _ => try destruct Σ.(wf_env_ext_wf) as [wfΣ]
  end.

Global Hint Resolve wf_env_ext_sq_wf : wf_env.
Global Hint Resolve wf_env_ext_graph_wf : wf_env.

Definition Σudecl {cf : checker_flags} (Σ : wf_env_ext) : ∥ on_udecl Σ.(wf_env_ext_env).1 Σ.(wf_env_ext_env).2 ∥ := 
  map_squash (fun x => x.2) Σ.
Global Hint Resolve Σudecl : wf_env.

Ltac wf_env := auto with wf_env.

Lemma wf_ext_gc_of_uctx {cf:checker_flags} {Σ : global_env_ext} (HΣ : ∥ wf_ext Σ ∥)
  : { uctx' | gc_of_uctx (global_ext_uctx Σ) = Some uctx' }.
Proof.
  assert (consistent (global_ext_uctx Σ).2) as HC.
  { sq; apply (global_ext_uctx_consistent _ HΣ). }
  destruct Σ as [Σ φ].
  simpl in HC.
  unfold gc_of_uctx; simpl in *.
  apply gc_consistent_iff in HC.
  destruct (gc_of_constraints (global_ext_constraints (Σ, φ))).
  eexists; reflexivity.
  contradiction HC.
Defined.

(** Any well-formed global environment gives rise to a well-formed universe graph corresponding to it. *)

Lemma graph_of_wf_ext {cf:checker_flags} {Σ : global_env_ext} (HΣ : ∥ wf_ext Σ ∥)
  : { G | is_graph_of_uctx G (global_ext_uctx Σ) }.
Proof.
  destruct (wf_ext_gc_of_uctx HΣ) as [uctx Huctx].
  exists (make_graph uctx). unfold is_graph_of_uctx. now rewrite Huctx.
Defined.

(** Build an optimized environment representation for lookups along with the graph associated to a well-formed 
  global environment. The graph building is separated, so that [(build_wf_env_ext Σ wfΣ).(wf_env_ext_env)] is
  convertible to [Σ]. *)

Definition build_wf_env_ext {cf : checker_flags} (Σ : global_env_ext) (wfΣ : ∥ wf_ext Σ ∥) : wf_env_ext := 
  {| wf_env_ext_env := Σ; 
     wf_env_ext_map := EnvMap.of_global_env Σ.(declarations); 
     wf_env_ext_map_repr := EnvMap.repr_global_env Σ.(declarations);
     wf_env_ext_wf := wfΣ;
     wf_env_ext_graph := proj1_sig (graph_of_wf_ext wfΣ);
     wf_env_ext_graph_wf := proj2_sig (graph_of_wf_ext wfΣ) |}.

Section GraphSpec.
  Context {cf:checker_flags} {Σ : global_env_ext} (HΣ : ∥ wf Σ ∥)
      (Hφ : ∥ on_udecl Σ.1 Σ.2 ∥)
      (G : universes_graph) (HG : is_graph_of_uctx G (global_ext_uctx Σ)).

  Local Definition HΣ' : ∥ wf_ext Σ ∥.
  Proof.
    destruct HΣ, Hφ; now constructor.
  Defined.
    
  Lemma check_constraints_spec ctrs
    : check_constraints G ctrs -> valid_constraints (global_ext_constraints Σ) ctrs.
  Proof.
    pose proof HΣ'.
    intros HH.
    refine (check_constraints_spec G (global_ext_uctx Σ) _ _ HG _ HH).
    sq; now eapply wf_ext_global_uctx_invariants.
    sq; now eapply global_ext_uctx_consistent.
  Qed.

  Lemma is_graph_of_uctx_levels (l : Level.t) :
    LevelSet.mem l (uGraph.wGraph.V G) <->
    LevelSet.mem l (global_ext_levels Σ).
  Proof.
    unfold is_graph_of_uctx in HG.
    case_eq (gc_of_uctx (global_ext_uctx Σ)); [intros [lvs cts] XX|intro XX];
      rewrite -> XX in *; simpl in *; [|contradiction].
    unfold gc_of_uctx in XX; simpl in XX.
    destruct (gc_of_constraints Σ); [|discriminate].
    inversion XX; subst.
    unfold is_true. rewrite !LevelSet.mem_spec. 
    symmetry. apply HG. 
  Qed.

End GraphSpec.