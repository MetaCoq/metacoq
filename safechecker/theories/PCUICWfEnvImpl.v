(* Distributed under the terms of the MIT license. *)
From Coq Require Import ssreflect ssrbool.
From MetaCoq.Template Require Import config utils uGraph EnvMap.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICEquality PCUICReduction
     PCUICReflect PCUICSafeLemmata PCUICTyping PCUICGlobalEnv PCUICWfUniverses.
From MetaCoq.SafeChecker Require Import PCUICEqualityDec PCUICWfEnv. 

Lemma wf_gc_of_uctx {cf:checker_flags} {Σ : global_env} (HΣ : ∥ wf Σ ∥)
: ∑ uctx', gc_of_uctx (global_uctx Σ) = Some uctx'.
Proof.
assert (consistent (global_uctx Σ).2) as HC.
{ sq; apply (wf_consistent _ HΣ). }
unfold gc_of_uctx; simpl in *.
apply gc_consistent_iff in HC.
destruct (gc_of_constraints (global_constraints Σ)).
eexists; reflexivity.
contradiction HC.
Defined.

Lemma graph_of_wf {cf:checker_flags} {Σ : global_env} (HΣ : ∥ wf Σ ∥)
: ∑ G, is_graph_of_uctx G (global_uctx Σ).
Proof.
destruct (wf_gc_of_uctx HΣ) as [uctx Huctx].
exists (make_graph uctx). unfold is_graph_of_uctx. now rewrite Huctx.
Defined.

Lemma wf_ext_gc_of_uctx {cf:checker_flags} {Σ : global_env_ext} (HΣ : ∥ wf_ext Σ ∥)
: ∑ uctx', gc_of_uctx (global_ext_uctx Σ) = Some uctx'.
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

Lemma graph_of_wf_ext {cf:checker_flags} {Σ : global_env_ext} (HΣ : ∥ wf_ext Σ ∥)
: ∑ G, is_graph_of_uctx G (global_ext_uctx Σ).
Proof.
destruct (wf_ext_gc_of_uctx HΣ) as [uctx Huctx].
exists (make_graph uctx). unfold is_graph_of_uctx. now rewrite Huctx.
Defined.

Definition abstract_env_graph {abstract_env_ext_impl : Type} 
  `{abstract_env_ext_prop abstract_env_impl} X `{abstract_env_ext_correct abstract_env_impl X} 
  {Σ} (wfΣ : abstract_env_ext_rel X Σ)
  := projT1 (graph_of_wf_ext (abstract_env_ext_wf wfΣ)).

Definition abstract_env_graph_wf {cf:checker_flags} {abstract_env_ext_impl : Type} 
`{abstract_env_ext_prop abstract_env_impl} X `{abstract_env_ext_correct abstract_env_impl X} 
 {Σ} (wfΣ : abstract_env_ext_rel X Σ) := projT2 (graph_of_wf_ext (abstract_env_ext_wf wfΣ)).

Record referenced_impl {cf:checker_flags} := {
      referenced_impl_env :> global_env_ext;
      referenced_impl_wf :> ∥ wf_ext referenced_impl_env ∥;
      referenced_impl_graph_ := projT1 (graph_of_wf_ext referenced_impl_wf);
      referenced_impl_graph_wf_ := projT2 (graph_of_wf_ext referenced_impl_wf)
  }.

Axiom guard_impl : FixCoFix -> global_env_ext -> context -> mfixpoint term -> bool.
Axiom guard_correct : forall fix_cofix Σ Γ mfix,
  guard fix_cofix Σ Γ mfix <-> guard_impl fix_cofix Σ Γ mfix.

Definition check_conv_pb_relb_correct {cf:checker_flags} (Σ : global_env_ext) (HΣ : ∥ wf_ext Σ ∥) G
  (HG : is_graph_of_uctx G (global_ext_uctx Σ)) conv_pb u u' :
  wf_universe Σ u' -> wf_universe Σ u -> 
  compare_universe conv_pb Σ u u' <-> conv_pb_relb G conv_pb u u'.
Proof. 
  intros.  sq.  destruct conv_pb; split; cbn; intro. 
  - apply (check_eqb_universe_complete _ (global_ext_levels Σ, global_ext_constraints Σ)); eauto.
      + eapply wf_ext_global_uctx_invariants; eauto.
      + eapply wf_ext_consistent; eauto.  
  - apply (check_eqb_universe_spec' G (global_ext_levels Σ, global_ext_constraints Σ)); eauto. 
      + eapply wf_ext_global_uctx_invariants; eauto.
      + eapply wf_ext_consistent; eauto.  
  - apply (check_leqb_universe_complete _ (global_ext_levels Σ, global_ext_constraints Σ)); eauto.
      + eapply wf_ext_global_uctx_invariants; eauto.
      + eapply wf_ext_consistent; eauto.  
  - apply (check_leqb_universe_spec' G (global_ext_levels Σ, global_ext_constraints Σ)); eauto. 
      + eapply wf_ext_global_uctx_invariants; eauto.
      + eapply wf_ext_consistent; eauto. 
Defined. 

Definition canonincal_abstract_env_ext_struct {cf:checker_flags} :
  abstract_env_ext_struct referenced_impl :=
  {| abstract_env_lookup := fun Σ => lookup_env (referenced_impl_env Σ) ;
     abstract_env_conv_pb_relb := fun Σ conv_pb => conv_pb_relb (referenced_impl_graph_ Σ) conv_pb ;
     abstract_env_compare_global_instance := fun Σ =>
      compare_global_instance (referenced_impl_env Σ)
                              (check_eqb_universe (referenced_impl_graph_ Σ));
     abstract_env_level_mem := fun Σ => level_mem (referenced_impl_env Σ);
     abstract_env_ext_wf_universeb := fun Σ u => wf_universeb Σ u;
     abstract_env_check_constraints := fun Σ => check_constraints (referenced_impl_graph_ Σ);

     abstract_env_guard := fun Σ fix_cofix => guard_impl fix_cofix (referenced_impl_env Σ);
     abstract_env_ext_rel := fun X Σ => Σ = referenced_impl_env X
  |}.

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

Definition fake_guard_impl : FixCoFix -> global_env_ext -> context -> mfixpoint term -> bool
  := fun fix_cofix Σ Γ mfix => true.

Axiom fake_guard_correct : forall fix_cofix Σ Γ mfix,
  guard fix_cofix Σ Γ mfix <-> fake_guard_impl fix_cofix Σ Γ mfix.

Definition optimized_abstract_env_ext_struct {cf:checker_flags} :
  abstract_env_ext_struct wf_env_ext :=
  {| abstract_env_lookup := fun Σ k => EnvMap.lookup k (wf_env_ext_map Σ);
     abstract_env_conv_pb_relb := fun Σ conv_pb => conv_pb_relb (wf_env_ext_graph Σ) conv_pb ;
     abstract_env_compare_global_instance := fun Σ =>
      compare_global_instance (wf_env_ext_env Σ)
                              (check_eqb_universe (wf_env_ext_graph Σ));
     abstract_env_level_mem := fun Σ l => LevelSet.mem l (uGraph.wGraph.V (wf_env_ext_graph Σ));
     abstract_env_ext_wf_universeb := fun Σ u => wf_universeb Σ u;
     abstract_env_check_constraints := fun Σ => check_constraints (wf_env_ext_graph Σ);

     abstract_env_guard := fun Σ fix_cofix => fake_guard_impl fix_cofix (wf_env_ext_env Σ);
     abstract_env_ext_rel := fun X Σ => Σ = wf_env_ext_env X
  |}.

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

  Definition referenced_impl_sq_wf (Σ : referenced_impl) : ∥ wf Σ ∥.
  Proof.
    destruct (referenced_impl_wf Σ).
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

Definition Σudecl_ref {cf : checker_flags} (Σ : referenced_impl) : ∥ on_udecl Σ.(referenced_impl_env).1 Σ.(referenced_impl_env).2 ∥ :=
    map_squash (fun x => x.2) Σ.
  
  Global Hint Resolve Σudecl : wf_env.

Ltac wf_env := auto with wf_env.


(** Build an optimized environment representation for lookups along with the graph associated to a well-formed
  global environment. The graph building is separated, so that [(build_wf_env_ext Σ wfΣ).(wf_env_ext_env)] is
  convertible to [Σ]. *)

Definition build_wf_env_ext {cf : checker_flags} (Σ : global_env_ext) (wfΣ : ∥ wf_ext Σ ∥) : wf_env_ext :=
  {| wf_env_ext_env := Σ;
     wf_env_ext_map := EnvMap.of_global_env Σ.(declarations);
     wf_env_ext_map_repr := EnvMap.repr_global_env Σ.(declarations);
     wf_env_ext_wf := wfΣ;
     wf_env_ext_graph := projT1 (graph_of_wf_ext wfΣ);
     wf_env_ext_graph_wf := projT2 (graph_of_wf_ext wfΣ) |}.

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

  Lemma check_constraints_complete ctrs (H : check_univs)
  : valid_constraints (global_ext_constraints Σ) ctrs -> check_constraints G ctrs.
  Proof.
    pose proof HΣ'.
    intros HH.
    refine (check_constraints_complete G (global_ext_uctx Σ) _ _ HG _ _ _ HH); eauto; sq.
    now eapply wf_ext_global_uctx_invariants.
    now eapply global_ext_uctx_consistent.
    pose proof (wf_ext_global_uctx_invariants Σ H0) as [H1 H2].
    split; eauto. clear H1. 
    unfold uctx_invariants in *; cbn in *.   
    unfold valid_constraints in HH. rewrite H in HH.
    unfold valid_constraints0 in HH. unfold ConstraintSet.For_all.
    intro x; specialize (H2 x). intro; apply H2.
    
  Admitted.

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


Program Definition canonincal_abstract_env_prop {cf:checker_flags} :
  @abstract_env_ext_prop _ _ canonincal_abstract_env_ext_struct :=
     {| abstract_env_ext_exists := fun Σ => sq (referenced_impl_env Σ ; eq_refl); |}.
Next Obligation. apply check_conv_pb_relb_correct; eauto. apply referenced_impl_wf. apply referenced_impl_graph_wf_.  Defined.
Next Obligation. eapply reflect_iff. eapply reflect_R_global_instance; eauto.
  move => ? ? /wf_universe_reflect ? - /wf_universe_reflect ?.
  apply iff_reflect;  apply check_conv_pb_relb_correct with (conv_pb := Conv); eauto.
  apply referenced_impl_wf. apply referenced_impl_graph_wf_.
  move => ? ? /wf_universe_reflect ? - /wf_universe_reflect ?.
  apply X0; eauto. 
  all: rewrite wf_universeb_instance_forall.
  revert H; move => / wf_universe_instanceP ?; eauto. 
  revert H0; move => / wf_universe_instanceP ?; eauto. 
Defined. 
Next Obligation. split; intros. 
  - eapply check_constraints_complete; eauto.
    apply referenced_impl_sq_wf. apply Σudecl_ref.
    apply referenced_impl_graph_wf_.
  - eapply check_constraints_spec; eauto.    
  apply referenced_impl_sq_wf. apply Σudecl_ref.
  apply referenced_impl_graph_wf_.
  Defined. 
Next Obligation. apply guard_correct. Defined.

Program Definition canonincal_abstract_env_correct {cf:checker_flags}
  (X : referenced_impl) :
  @abstract_env_ext_correct _ cf canonincal_abstract_env_ext_struct X.
Proof. econstructor. intros. cbn in H; subst. apply referenced_impl_wf. Defined.


Program Definition optimized_abstract_env_prop {cf:checker_flags} :
@abstract_env_ext_prop _ _ optimized_abstract_env_ext_struct :=
   {| abstract_env_ext_exists := fun Σ => sq (wf_env_ext_env Σ ; eq_refl); |}.
Next Obligation. pose (wf_env_ext_wf X). sq. 
  erewrite EnvMap.lookup_spec; try reflexivity. 
  1: apply wf_fresh_globals; eauto.
  1: apply wf_env_ext_map_repr. Qed.
Next Obligation. apply check_conv_pb_relb_correct; eauto.
  apply wf_env_ext_wf. apply wf_env_ext_graph_wf.
Defined.
Next Obligation. eapply reflect_iff. eapply reflect_R_global_instance; eauto.
  move => ? ? /wf_universe_reflect ? - /wf_universe_reflect ?.
  apply iff_reflect;  apply check_conv_pb_relb_correct with (conv_pb := Conv); eauto.
  apply wf_env_ext_wf. apply wf_env_ext_graph_wf.
  move => ? ? /wf_universe_reflect ? - /wf_universe_reflect ?.
  apply X0; eauto. 
  all: rewrite wf_universeb_instance_forall.
  revert H; move => / wf_universe_instanceP ?; eauto. 
  revert H0; move => / wf_universe_instanceP ?; eauto. 
Defined. 
Next Obligation. eapply eq_true_iff_eq.
                 split; intros; eapply is_graph_of_uctx_levels; eauto;
                 eapply wf_env_ext_graph_wf. Qed.
Next Obligation. split; intros. 
  - eapply check_constraints_complete; eauto.
    apply wf_env_ext_sq_wf. apply Σudecl.
    apply wf_env_ext_graph_wf.
  - eapply check_constraints_spec; eauto.    
    apply wf_env_ext_sq_wf. apply Σudecl.
    apply wf_env_ext_graph_wf.
Defined. 
Next Obligation. apply fake_guard_correct. Defined.

Program Definition optimized_abstract_env_correct {cf:checker_flags} 
  (X : wf_env_ext):
  @abstract_env_ext_correct _ cf optimized_abstract_env_ext_struct X.
Proof. econstructor. intros. cbn in H; subst. apply wf_env_ext_wf. Defined.

