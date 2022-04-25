(* Distributed under the terms of the MIT license. *)
From Coq Require Import ssreflect ssrbool.
From MetaCoq.Template Require Import config utils uGraph EnvMap.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICEquality PCUICReduction
     PCUICReflect PCUICSafeLemmata PCUICTyping PCUICGlobalEnv PCUICWfUniverses.
From MetaCoq.SafeChecker Require Import PCUICEqualityDec PCUICWfEnv. 
From Equations Require Import Equations.

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

Require Import Morphisms.

Global Instance consistent_proper : Proper (CS.Equal ==> iff) consistent.
Proof.
  intros c c' eq. rewrite /consistent.
  now setoid_rewrite eq.
Qed.

Lemma on_udecl_mono {cf:checker_flags} {Σ : global_env} {wfΣ : wf Σ} : on_udecl Σ Monomorphic_ctx.
Proof.
  repeat split; cbn.
  - intros i; rewrite LevelSetFact.empty_iff //.
  - intros i; rewrite ConstraintSetFact.empty_iff //.
  - red. rewrite /univs_ext_constraints /=.
    rewrite CS_union_empty.
    apply wfΣ.
  - apply consistent_extension_on_empty.
Qed.

Record referenced_impl_ext {cf:checker_flags} := {
      referenced_impl_env_ext :> global_env_ext;
      referenced_impl_ext_wf :> ∥ wf_ext referenced_impl_env_ext ∥;
      referenced_impl_ext_graph := projT1 (graph_of_wf_ext referenced_impl_ext_wf);
      referenced_impl_ext_graph_wf := projT2 (graph_of_wf_ext referenced_impl_ext_wf)
  }.

Record referenced_impl {cf:checker_flags} := {
      referenced_impl_env :> global_env;
      referenced_impl_wf :> ∥ wf referenced_impl_env ∥;
      referenced_impl_graph := projT1 (graph_of_wf referenced_impl_wf);
      referenced_impl_graph_wf := projT2 (graph_of_wf referenced_impl_wf)
  }.

Axiom guard_impl : FixCoFix -> global_env_ext -> context -> mfixpoint term -> bool.
Axiom guard_correct : forall fix_cofix Σ Γ mfix,
  guard fix_cofix Σ Γ mfix <-> guard_impl fix_cofix Σ Γ mfix.


Definition fake_guard_impl : FixCoFix -> global_env_ext -> context -> mfixpoint term -> bool
  := fun fix_cofix Σ Γ mfix => true.

Axiom fake_guard_correct : forall fix_cofix Σ Γ mfix,
  guard fix_cofix Σ Γ mfix <-> fake_guard_impl fix_cofix Σ Γ mfix.

  
Definition init_env : global_env := {| universes := (LS.singleton Level.lzero , CS.empty); declarations := [] |}.

Definition on_global_univ_init_env : on_global_univs init_env.
  repeat split. 
  - intros x Hx; cbn in *. inversion Hx.
  - intros x Hx; cbn in *. destruct x; eauto. now inversion Hx.
  - red. unshelve eexists. 
    + econstructor; eauto. intros; exact 1%positive.
    + red. intros ? ?. cbn in *. inversion H.
Defined.          

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

Global Instance canonical_abstract_env_ext_struct {cf:checker_flags} :
  abstract_env_ext_struct referenced_impl_ext :=
  {| abstract_env_lookup := fun Σ => lookup_env (referenced_impl_env_ext Σ) ;
     abstract_env_conv_pb_relb := fun Σ conv_pb => conv_pb_relb (referenced_impl_ext_graph Σ) conv_pb ;
     abstract_env_compare_global_instance := fun Σ =>
      compare_global_instance (referenced_impl_env_ext Σ)
                              (check_eqb_universe (referenced_impl_ext_graph Σ));
     abstract_env_level_mem := fun Σ => level_mem (referenced_impl_env_ext Σ);
     abstract_env_ext_wf_universeb := fun Σ u => wf_universeb Σ u;
     abstract_env_check_constraints := fun Σ => check_constraints (referenced_impl_ext_graph Σ);

     abstract_env_guard := fun Σ fix_cofix => guard_impl fix_cofix (referenced_impl_env_ext Σ);
     abstract_env_ext_rel := fun X Σ => Σ = referenced_impl_env_ext X
  |}.

Program Global Instance canonical_abstract_env_struct {cf:checker_flags} :
  abstract_env_struct referenced_impl referenced_impl_ext :=
 {|
 abstract_env_empty := {|
 referenced_impl_env := {| universes := init_env ; declarations := [] |};
 |} ;
 abstract_env_init := fun cs H =>  {|
 referenced_impl_env := {| universes := cs ; declarations := [] |};
 |} ;
 abstract_env_add_decl := fun X kn d H => 
  {| referenced_impl_env := add_global_decl X.(referenced_impl_env) (kn,d);
   |};
 abstract_env_empty_ext X := {| referenced_impl_env_ext := (X , Monomorphic_ctx);
 |} ;
 abstract_env_univ X := X ;
 abstract_env_global_declarations X := declarations X;
 abstract_env_is_consistent uctx := wGraph.is_acyclic (make_graph uctx);
 abstract_env_is_consistent_uctx X uctx :=
   let G := referenced_impl_graph X in
   let G' := add_uctx uctx G in
   wGraph.is_acyclic G' && wGraph.is_full_subgraph G G' ;
 abstract_env_add_uctx X uctx udecl Hdecl Hglobal := {| referenced_impl_env_ext := (X.(referenced_impl_env) , udecl);
 |} ;
 abstract_env_rel := fun X Σ => Σ = referenced_impl_env X
 |}.
Next Obligation. sq. constructor; cbn; eauto. apply on_global_univ_init_env. econstructor. Qed.
Next Obligation. sq; constructor; cbn; eauto. econstructor. Qed.
Next Obligation. pose proof (referenced_impl_wf X) as [[? ?]]; sq; destruct H.
  econstructor; eauto. econstructor; eauto.  Qed.
Next Obligation. pose proof (referenced_impl_wf X) as [?]. sq. split; eauto.
  apply on_udecl_mono.
Qed.
Next Obligation.
  pose proof (referenced_impl_wf X). now sq.
Qed.

(* We pack up all the information required on the global environment and graph in a
single record. *)

Record wf_env {cf:checker_flags} := {
  wf_env_referenced :> referenced_impl;
  wf_env_map :> EnvMap.t global_decl;
  wf_env_map_repr :> EnvMap.repr (referenced_impl_env wf_env_referenced).(declarations) wf_env_map;
}.

Record wf_env_ext {cf:checker_flags} := {
  wf_env_ext_referenced :> referenced_impl_ext;
  wf_env_ext_map :> EnvMap.t global_decl;
  wf_env_ext_map_repr :> EnvMap.repr (referenced_impl_env_ext wf_env_ext_referenced).(declarations) wf_env_ext_map;
}.


Global Instance optimized_abstract_env_ext_struct {cf:checker_flags} :
  abstract_env_ext_struct wf_env_ext :=
  {| abstract_env_lookup := fun Σ k => EnvMap.lookup k (wf_env_ext_map Σ);
     abstract_env_conv_pb_relb X := abstract_env_conv_pb_relb X.(wf_env_ext_referenced);
     abstract_env_compare_global_instance X := abstract_env_compare_global_instance X.(wf_env_ext_referenced);
     abstract_env_level_mem X := abstract_env_level_mem X.(wf_env_ext_referenced);
     abstract_env_ext_wf_universeb X := abstract_env_ext_wf_universeb X.(wf_env_ext_referenced);
     abstract_env_check_constraints X := abstract_env_check_constraints X.(wf_env_ext_referenced);
     abstract_env_guard := fun Σ fix_cofix => fake_guard_impl fix_cofix (wf_env_ext_referenced Σ);
     abstract_env_ext_rel X := abstract_env_ext_rel X.(wf_env_ext_referenced);
  |}.

Lemma wf_env_eta {cf : checker_flags} (Σ : wf_env) : {| universes := Σ.(universes); declarations := Σ.(declarations) |} = Σ.
Proof.
  destruct Σ => /= //. destruct referenced_impl_env => //.
Qed.

Lemma wf_fresh_globals {cf : checker_flags} Σ : wf Σ -> EnvMap.fresh_globals Σ.(declarations).
Proof. destruct Σ as [univs Σ]; cbn.
  move=> [] onu; cbn. induction 1; constructor; auto.
Qed.


Lemma wf_env_fresh {cf : checker_flags} (Σ : wf_env) : EnvMap.EnvMap.fresh_globals Σ.(declarations).
Proof.
  destruct Σ.(referenced_impl_wf).
  now eapply wf_fresh_globals. 
Qed.

Lemma of_global_env_cons {cf:checker_flags} d g : EnvMap.fresh_globals (add_global_decl g d).(declarations) ->
  EnvMap.of_global_env (add_global_decl g d).(declarations) = EnvMap.add d.1 d.2 (EnvMap.of_global_env g.(declarations)).
Proof.
  unfold EnvMap.of_global_env. simpl. unfold KernameMapFact.uncurry.
  reflexivity.
Qed.

Program Definition wf_env_empty {cf:checker_flags} :=
 {|   
  wf_env_referenced := abstract_env_empty ;
  wf_env_map := EnvMap.empty;
  |}.

Program Definition wf_env_init {cf:checker_flags} cs : 
  on_global_univs cs -> wf_env := fun H =>
  {|   
  wf_env_referenced := abstract_env_init cs H;
  wf_env_map := EnvMap.empty;
  |}.

Program Global Instance optimized_abstract_env_struct {cf:checker_flags} :
  abstract_env_struct wf_env wf_env_ext :=
 {|
 abstract_env_empty := wf_env_empty;
 abstract_env_init := wf_env_init;
 abstract_env_add_decl X kn d H :=
  {| wf_env_referenced := @abstract_env_add_decl _ _ referenced_impl_ext _ X.(wf_env_referenced) kn d H ;
     wf_env_map := EnvMap.add kn d X.(wf_env_map) |};
 abstract_env_empty_ext X := 
  {| wf_env_ext_referenced := @abstract_env_empty_ext _ _ referenced_impl_ext _ X.(wf_env_referenced) ;
     wf_env_ext_map := X.(wf_env_map) |};
 abstract_env_global_declarations X := abstract_env_global_declarations X.(wf_env_referenced);
 abstract_env_is_consistent univ := abstract_env_is_consistent univ;
 abstract_env_is_consistent_uctx X uctx := abstract_env_is_consistent_uctx X.(wf_env_referenced) uctx;
 abstract_env_add_uctx X uctx udecl Huctx Hdecl := 
 {| wf_env_ext_referenced := @abstract_env_add_uctx _ _ referenced_impl_ext _ X.(wf_env_referenced) uctx udecl Huctx Hdecl ;
    wf_env_ext_map := X.(wf_env_map) |};
 abstract_env_rel X := abstract_env_rel X.(wf_env_referenced)
 |}.
Next Obligation.
  pose proof (X.(wf_env_referenced).(referenced_impl_wf)) as [?].
  sq. destruct H.  
  apply EnvMap.repr_add; eauto; try eapply wf_fresh_globals; eauto. 
  apply wf_env_map_repr.
Defined. 
Next Obligation. apply wf_env_map_repr. Defined.
Next Obligation. apply wf_env_map_repr. Defined.

Section WfEnv.
  Context {cf : checker_flags}.

  Definition referenced_impl_sq_wf (Σ : referenced_impl_ext) : ∥ wf Σ ∥.
  Proof.
    destruct (referenced_impl_ext_wf Σ).
    sq. apply X.
  Qed.

  Definition lookup (Σ : wf_env_ext) (kn : kername) : option global_decl :=
    EnvMap.lookup kn Σ.(wf_env_ext_map).

  Lemma lookup_lookup_env Σ kn : lookup Σ kn = lookup_env Σ kn.
  Proof.
    rewrite /lookup. destruct Σ as [Σ map repr]. pose (referenced_impl_sq_wf Σ).
    sq. apply EnvMap.lookup_spec; auto. now eapply wf_fresh_globals.
  Qed.

End WfEnv.


Create HintDb wf_env discriminated.
Global Hint Constants Opaque : wf_env.
Global Hint Variables Opaque : wf_env.

Global Hint Resolve referenced_impl_ext_wf : wf_env.
Global Hint Resolve referenced_impl_wf : wf_env.

Definition Σudecl_ref {cf : checker_flags} (Σ : referenced_impl_ext) : 
  ∥ on_udecl Σ.(referenced_impl_env_ext).1 Σ.(referenced_impl_env_ext).2 ∥ :=
    map_squash (fun x => x.2) Σ.

Definition Σudecl {cf : checker_flags} (Σ : wf_env_ext) : 
  ∥ on_udecl Σ.(referenced_impl_env_ext).1 Σ.(referenced_impl_env_ext).2 ∥ :=
  map_squash (fun x => x.2) Σ.
  
  Global Hint Resolve Σudecl : wf_env.

Ltac wf_env := auto with wf_env.


(** Build an optimized environment representation for lookups along with the graph associated to a well-formed
  global environment. The graph building is separated, so that [(build_wf_env_ext Σ wfΣ).(wf_env_ext_env)] is
  convertible to [Σ]. *)

Definition build_wf_env_ext {cf : checker_flags} (Σ : global_env_ext) (wfΣ : ∥ wf_ext Σ ∥) : wf_env_ext :=
  {| wf_env_ext_referenced := 
      {| referenced_impl_env_ext := Σ; referenced_impl_ext_wf := wfΣ |} ;
     wf_env_ext_map := EnvMap.of_global_env Σ.(declarations);
     wf_env_ext_map_repr := EnvMap.repr_global_env Σ.(declarations);
|}.

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

  Lemma check_constraints_complete ctrs (H : check_univs) :
  uctx_invariants ((global_ext_uctx Σ).1, ctrs) -> valid_constraints (global_ext_constraints Σ) ctrs -> check_constraints G ctrs.
  Proof.
    pose proof HΣ'.
    intros Huctx HH.  
    refine (check_constraints_complete G (global_ext_uctx Σ) _ _ HG _ _ _ HH); eauto; sq.
    now eapply wf_ext_global_uctx_invariants.
    now eapply global_ext_uctx_consistent.
    pose proof (wf_ext_global_uctx_invariants Σ H0) as [H1 H2].
    split; eauto.
  Defined.

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


Program Global Instance canonical_abstract_env_ext_prop {cf:checker_flags} :
  @abstract_env_ext_prop _ _ canonical_abstract_env_ext_struct :=
     {| abstract_env_ext_exists := fun Σ => sq (referenced_impl_env_ext Σ ; eq_refl); |}.
Next Obligation. wf_env. Defined.
Next Obligation. apply check_conv_pb_relb_correct; eauto; wf_env.   
   apply (graph_of_wf_ext X).π2. Defined.
Next Obligation. eapply reflect_iff. eapply reflect_R_global_instance; eauto.
  move => ? ? /wf_universe_reflect ? - /wf_universe_reflect ?.
  apply iff_reflect;  apply check_conv_pb_relb_correct with (conv_pb := Conv); eauto; wf_env. 
  apply (graph_of_wf_ext X).π2.
  move => ? ? /wf_universe_reflect ? - /wf_universe_reflect ?.
  apply X0; eauto. 
  all: rewrite wf_universeb_instance_forall.
  revert H; move => / wf_universe_instanceP ?; eauto. 
  revert H0; move => / wf_universe_instanceP ?; eauto. 
Defined. 
Next Obligation. split; intros. 
  - eapply check_constraints_complete; eauto.
    apply referenced_impl_sq_wf. apply Σudecl_ref.
    apply (graph_of_wf_ext X).π2.
    now destruct X. 
  - eapply check_constraints_spec; eauto.    
  apply referenced_impl_sq_wf. apply Σudecl_ref.
  apply (graph_of_wf_ext X).π2.
  Defined. 
Next Obligation. apply guard_correct. Defined.

Program Global Instance optimized_abstract_env_ext_prop {cf:checker_flags} :
@abstract_env_ext_prop _ _ optimized_abstract_env_ext_struct :=
   {| abstract_env_ext_exists := fun Σ => sq (referenced_impl_env_ext Σ ; eq_refl); |}.
Next Obligation. wf_env. Defined.
Next Obligation. pose (referenced_impl_ext_wf X). sq. 
  erewrite EnvMap.lookup_spec; try reflexivity. 
  1: apply wf_fresh_globals; eauto.
  1: apply wf_env_ext_map_repr. Qed.
Next Obligation. now rewrite (abstract_env_compare_universe_correct X.(wf_env_ext_referenced)). Defined.
Next Obligation. now rewrite (abstract_env_compare_global_instance_correct X.(wf_env_ext_referenced)); eauto. Defined.
Next Obligation. now rewrite (abstract_env_check_constraints_correct X.(wf_env_ext_referenced)); eauto. Defined.
Next Obligation. apply fake_guard_correct. Defined.


Program Global Instance canonical_abstract_env_prop {cf:checker_flags} :
  @abstract_env_prop _ _ _ canonical_abstract_env_ext_struct canonical_abstract_env_struct.
Next Obligation. now sq. Qed.
Next Obligation. wf_env. Qed.
Next Obligation. now split. Qed.
Next Obligation. now split. Qed.
Next Obligation. unshelve epose proof (is_consistent_spec udecl _) as Hconsistent; eauto.
  unfold is_consistent in Hconsistent; now rewrite H0 in Hconsistent.
  Qed.
Next Obligation.
  rename H2 into Hudecl. unfold referenced_impl_graph; rewrite andb_and.
  pose proof (referenced_impl_graph_wf X) as HG.
  set (gph := (graph_of_wf X).π1) in *. clearbody gph. simpl in HG.
  move: HG=> /on_SomeP [[uctx1 uctx2] [Huctx HG]].
  pose proof (gcinv := gc_of_uctx_invariants _ _ Huctx H0).
  pose proof (invG := make_graph_invariants _ gcinv).
  destruct (gc_of_uctx_union _ _ _ _ Hudecl Huctx) as [gcsExt [uctxExtEq hgcs]].
  pose proof (HG' := add_uctx_make_graph t uctx1 t0 uctx2).
  set (uctxExt := (LS.union t uctx1, GCS.union t0 uctx2)) in HG'.
  have gcExtinv : global_gc_uctx_invariants uctxExt.
  { rewrite /uctxExt /global_gc_uctx_invariants /=; rewrite <- hgcs.
    apply: (gc_of_uctx_invariants _ _ uctxExtEq). }
  pose proof (invG' := make_graph_invariants _ gcExtinv).
  move: (Huctx); rewrite /gc_of_uctx.
  case_eq (gc_of_constraints (global_uctx X).2) => //=.
  intros Σctrs HΣctrs [=]; subst.
  unfold gc_of_uctx in Hudecl; move: Hudecl.
  case_eq (gc_of_constraints (constraints_of_udecl udecl)); last by move=> ->.
  move=> ctrs /= /[dup] Hctrs -> [=]??; subst. simpl in *.
  rewrite - (is_consistent_spec (global_ext_uctx (X, udecl))).
  pose proof (gc_of_constraints_union (constraints_of_udecl udecl) (global_constraints X)).
  rewrite HΣctrs Hctrs in H. simpl in H.
  unfold is_consistent, global_ext_uctx, gc_of_uctx, global_ext_constraints. simpl.
  destruct (gc_of_constraints (ConstraintSet.union (constraints_of_udecl udecl)
                                                   (global_constraints X))).
  2: inversion H.
  simpl in H.
  assert (H45 : make_graph (global_ext_levels (X, udecl) , t) =_g make_graph uctxExt).
  { apply make_graph_proper. now split; eauto. }
  erewrite is_acyclic_proper; last eassumption.
  clear H1 H0 H45; split.
  + move=> [] h consistent_ext ; split; first by rewrite -{1}HG HG'.
    apply/wGraph.is_full_subgraph_spec.
    symmetry in HG.
    refine (@consistent_on_full_subgraph _ (global_uctx X) (uctx_of_udecl udecl)
                                        (global_levels X, uctx2)
                                        (levels_of_udecl udecl, t0)
                                        gph
                                        _
                                        _
                                        gcinv
                                        Huctx
                                        (gc_of_constraints_of_uctx (uctx_of_udecl udecl) _ Hctrs)
                                        HG
           ).
    * move: h=> /wGraph.is_acyclic_spec.
      rewrite -HG' -HG.
      apply: acyclic_no_loop_add_uctx.
    * apply: consistent_extension_on_union.
      pose proof (referenced_impl_wf X); sq.
      apply: PCUICUnivSubstitutionConv.levels_global_constraint.
      unfold uctx_of_udecl=> /=.
      exact consistent_ext.
  + move=> [acG'] /wGraph.is_full_subgraph_spec H1; split; first by rewrite -HG' HG.
    rewrite  -HG' HG in invG'.
    move: acG' => /wGraph.is_acyclic_correct acG'.
    intros v [gΣ [gcΣeq Σsat]]%gc_of_constraints_spec%on_SomeP.
    symmetry in HG. rewrite -HG in HG'.
    move: gcΣeq; rewrite HΣctrs => [=]?; subst.
    destruct (graph_extend gph _ H1 acG' _ _ gcinv gcExtinv HG HG' v Σsat) as [vext [vextsat extendsv]].
    simpl in vextsat.
    exists vext; split.
    * apply gc_of_constraints_spec.
      rewrite Hctrs /=.
      apply GoodConstraintSet.for_all_spec; first by move=> ?? ->.
      move=> ??; apply GoodConstraintSet.for_all_spec in vextsat; last by move=> ??->.
      apply: vextsat; apply/GoodConstraintSet.union_spec; by left.
    * move=> l Hl; apply extendsv.
      case: HG=> eq1 _ ; rewrite eq1 //=.
  Qed.

Program Global Instance optimized_abstract_env_prop {cf:checker_flags} :
  @abstract_env_prop _ _ _ optimized_abstract_env_ext_struct optimized_abstract_env_struct.
Next Obligation. now sq. Qed.
Next Obligation. wf_env. Qed.
Next Obligation. now split. Qed.
Next Obligation. now split. Qed.
Next Obligation. now erewrite (@abstract_env_is_consistent_correct _ _ _ _ _ canonical_abstract_env_prop); eauto. Qed.
Next Obligation. now erewrite (abstract_env_is_consistent_uctx_correct X.(wf_env_referenced)); eauto. Qed.
  
  
Definition canonical_abstract_env_ext_impl {cf:checker_flags} : abstract_env_ext_impl :=
  (referenced_impl_ext ; canonical_abstract_env_ext_struct ; canonical_abstract_env_ext_prop).
  
Definition optimized_abstract_env_ext_impl {cf:checker_flags} : abstract_env_ext_impl :=
  (wf_env_ext ; optimized_abstract_env_ext_struct ; optimized_abstract_env_ext_prop).

Definition optimized_abstract_env_impl {cf:checker_flags} : abstract_env_impl :=
  (wf_env ; optimized_abstract_env_ext_impl ; optimized_abstract_env_struct ; optimized_abstract_env_prop).


