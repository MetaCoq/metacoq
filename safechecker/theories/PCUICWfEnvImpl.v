(* Distributed under the terms of the MIT license. *)
From Coq Require Import ssreflect ssrbool.
From MetaCoq.Template Require Import config utils uGraph EnvMap.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICEquality PCUICReduction
     PCUICReflect PCUICSafeLemmata PCUICTyping PCUICGlobalEnv PCUICWfUniverses.
From MetaCoq.SafeChecker Require Import PCUICEqualityDec PCUICWfEnv.
From Equations Require Import Equations.

Class abstract_guard_impl :=
  { guard_impl : FixCoFix -> global_env_ext -> context -> mfixpoint term -> bool ;
    guard_correct : forall fix_cofix Σ Γ mfix, guard fix_cofix Σ Γ mfix <-> guard_impl fix_cofix Σ Γ mfix
  }.

Definition fake_guard_impl : FixCoFix -> global_env_ext -> context -> mfixpoint term -> bool
  := fun fix_cofix Σ Γ mfix => true.

Record referenced_impl_ext {cf:checker_flags} {guard : abstract_guard_impl} := {
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

Program Definition referenced_pop {cf:checker_flags} (Σ : referenced_impl) : referenced_impl :=
match Σ.(declarations) with
 [] => Σ
 | (d::decls) =>
   {| referenced_impl_env := {| universes := Σ.(universes); declarations := decls; retroknowledge := Σ.(retroknowledge) |} |}
end.
Next Obligation.
destruct Σ.(referenced_impl_wf). sq.
destruct X as [onu ond]; split => //. rewrite <- Heq_anonymous in ond.
now depelim ond.
Qed.

Program Definition make_wf_env_ext {cf:checker_flags} {guard : abstract_guard_impl}
(Σ : referenced_impl) (univs : universes_decl)
(prf : forall Σ0 : global_env, Σ0 = Σ -> ∥ wf_ext (Σ0, univs) ∥) : referenced_impl_ext :=
{| referenced_impl_env_ext := (Σ, univs);|}.

Program Global Instance canonical_abstract_env_struct {cf:checker_flags} {guard : abstract_guard_impl} :
  abstract_env_struct referenced_impl referenced_impl_ext :=
  {|
  abstract_env_lookup := fun Σ => lookup_env (referenced_impl_env_ext Σ) ;
  abstract_env_leqb_level_n := fun Σ => leqb_level_n (referenced_impl_ext_graph Σ) ;
  abstract_env_level_mem := fun Σ levels l => LevelSet.mem l (LevelSet.union levels (global_ext_levels (referenced_impl_env_ext Σ)));
  abstract_env_ext_wf_universeb := fun Σ u => wf_universeb Σ u;
  abstract_env_guard := fun Σ fix_cofix => guard_impl fix_cofix (referenced_impl_env_ext Σ);
  abstract_env_ext_rel := fun X Σ => Σ = referenced_impl_env_ext X;
  abstract_env_init := fun cs retro H =>  {|
     referenced_impl_env := {| universes := cs ;
                               declarations := [];
                               retroknowledge := retro |}; |} ;
  abstract_env_add_decl := fun X kn d H =>
    {| referenced_impl_env := add_global_decl X.(referenced_impl_env) (kn,d); |};
  abstract_env_is_consistent X uctx :=
   let G := referenced_impl_graph X in
   let G' := add_uctx uctx G in
   wGraph.is_acyclic G' && wGraph.IsFullSubgraph.is_full_extension G G' ;
  abstract_env_add_udecl X udecl Hglobal :=
    {| referenced_impl_env_ext := (X.(referenced_impl_env) , udecl); |} ;
  abstract_primitive_constant := fun X tag => primitive_constant X tag;
  abstract_env_rel := fun X Σ => Σ = referenced_impl_env X ;
  abstract_pop_decls := referenced_pop ;
 |}.
Next Obligation. sq; constructor; cbn; eauto. econstructor. Qed.
Next Obligation.
 pose proof (referenced_impl_wf X). destruct (H _ eq_refl).
 sq. destruct H0.  econstructor; eauto. econstructor; eauto.
  Qed.
Next Obligation.
  pose proof (referenced_impl_wf X). destruct (Hglobal _ eq_refl); sq.
  now econstructor.
Qed.

(* We pack up all the information required on the global environment and graph in a
single record. *)

Record wf_env {cf:checker_flags} := {
  wf_env_referenced :> referenced_impl;
  wf_env_map :> EnvMap.t global_decl;
  wf_env_map_repr :> EnvMap.repr (referenced_impl_env wf_env_referenced).(declarations) wf_env_map;
}.

Record wf_env_ext {cf:checker_flags} {guard : abstract_guard_impl} := {
  wf_env_ext_referenced :> referenced_impl_ext;
  wf_env_ext_map :> EnvMap.t global_decl;
  wf_env_ext_map_repr :> EnvMap.repr (referenced_impl_env_ext wf_env_ext_referenced).(declarations) wf_env_ext_map;
}.

Lemma wf_env_eta {cf : checker_flags} (Σ : wf_env) :
 {| universes := Σ.(universes); declarations := Σ.(declarations); retroknowledge := Σ.(retroknowledge) |} = Σ.
Proof.
  destruct Σ => /= //. destruct referenced_impl_env => //.
Qed.

Lemma wf_fresh_globals {cf : checker_flags} Σ : wf Σ -> EnvMap.fresh_globals Σ.(declarations).
Proof. destruct Σ as [univs Σ]; cbn.
  move=> [] onu; cbn. induction 1; constructor; auto. now destruct o.
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

Program Definition wf_env_init {cf:checker_flags} {guard : abstract_guard_impl} cs retro :
  on_global_univs cs -> wf_env := fun H =>
  {|
  wf_env_referenced := abstract_env_init cs retro H;
  wf_env_map := EnvMap.empty;
  |}.

Lemma reference_pop_decls_correct {cf:checker_flags} (X:referenced_impl) decls
  (prf : forall Σ : global_env, Σ = X ->
  exists d, Σ.(declarations) = d :: decls) :
  let X' := referenced_pop X in
  forall Σ Σ', Σ = X -> Σ' = X' ->
          Σ'.(declarations) = decls /\ Σ.(universes) = Σ'.(universes) /\
          Σ.(retroknowledge) = Σ'.(retroknowledge).
Proof.
  cbn; intros; subst. specialize (prf _ eq_refl).
  unfold referenced_pop. cbn. set (referenced_pop_obligation_1 cf X).
  clearbody s. destruct (X.(declarations)); cbn; inversion prf; now inversion H.
Qed.

Program Definition optim_pop {cf:checker_flags} (Σ : wf_env) : wf_env :=
  match Σ.(referenced_impl_env).(declarations) with
    [] => Σ
    | ((kn , d) :: decls) =>
    {| wf_env_referenced := referenced_pop Σ ;
        wf_env_map := EnvMap.EnvMap.remove kn Σ.(wf_env_map);
    |}
  end.

Next Obligation.
  pose proof Σ.(wf_env_map_repr). red in H.
  rewrite <- Heq_anonymous in H.
  set (Σ0 := EnvMap.of_global_env decls).
  pose proof (EnvMap.remove_add_eq decls kn d Σ0).
  PCUICSR.forward_keep H0.
  { pose proof (Σf := wf_env_fresh Σ). rewrite <- Heq_anonymous in Σf. now depelim Σf. }
  PCUICSR.forward_keep H0.
  { pose proof (Σf := wf_env_fresh Σ). rewrite <- Heq_anonymous in Σf. now depelim Σf. }
  PCUICSR.forward_keep H0.
  { red. unfold EnvMap.equal. reflexivity. }
  unfold EnvMap.repr.
  rewrite H /=. unfold KernameMapFact.uncurry; cbn.
  unfold EnvMap.add in H0.
  unfold referenced_pop. cbn. set (referenced_pop_obligation_1 cf _).
  clearbody s.
  destruct (declarations Σ); cbn in *; inversion Heq_anonymous; clear Heq_anonymous s.
  subst. unfold KernameMapFact.uncurry in *; cbn in *.
  unfold Σ0 in * ; clear Σ0. unfold EnvMap.equal, KernameMap.Equal in H0.
  specialize (H0 y). cbn in H0. rewrite H0. reflexivity.
Qed.

Program Global Instance optimized_abstract_env_struct {cf:checker_flags} {guard : abstract_guard_impl} :
  abstract_env_struct wf_env wf_env_ext :=
 {|
 abstract_env_lookup := fun Σ k => EnvMap.lookup k (wf_env_ext_map Σ);
 abstract_env_leqb_level_n X := abstract_env_leqb_level_n X.(wf_env_ext_referenced);
 abstract_env_level_mem X := abstract_env_level_mem X.(wf_env_ext_referenced);
 abstract_env_ext_wf_universeb X := abstract_env_ext_wf_universeb X.(wf_env_ext_referenced);
 abstract_env_guard := fun Σ fix_cofix => guard_impl fix_cofix (wf_env_ext_referenced Σ);
 abstract_env_ext_rel X := abstract_env_ext_rel X.(wf_env_ext_referenced);

 abstract_env_init := wf_env_init;
 abstract_env_add_decl X kn d H :=
  {| wf_env_referenced := @abstract_env_add_decl _ _ referenced_impl_ext _ X.(wf_env_referenced) kn d H ;
     wf_env_map := EnvMap.add kn d X.(wf_env_map) |};
 abstract_env_is_consistent X uctx := abstract_env_is_consistent X.(wf_env_referenced) uctx;
 abstract_env_add_udecl X udecl Hdecl :=
 {| wf_env_ext_referenced := @abstract_env_add_udecl _ _ referenced_impl_ext _ X.(wf_env_referenced) udecl Hdecl ;
    wf_env_ext_map := X.(wf_env_map) |};
 abstract_primitive_constant X := abstract_primitive_constant X.(wf_env_ext_referenced);
 abstract_env_rel X := abstract_env_rel X.(wf_env_referenced) ;
 abstract_pop_decls := optim_pop ;
 |}.
Next Obligation.
  pose proof (X.(wf_env_referenced).(referenced_impl_wf)) as [?].
  sq. destruct (H _ eq_refl).
  apply EnvMap.repr_add; eauto; try eapply wf_fresh_globals; eauto.
  destruct X1; eauto.
  apply wf_env_map_repr.
Qed.
Next Obligation. apply wf_env_map_repr. Qed.

Section WfEnv.
  Context {cf : checker_flags} {guard : abstract_guard_impl}.

  Definition referenced_impl_sq_wf (Σ : referenced_impl_ext) : ∥ wf Σ ∥.
  Proof using Type.
    destruct (referenced_impl_ext_wf Σ).
    sq. apply X.
  Qed.

  Definition lookup (Σ : wf_env_ext) (kn : kername) : option global_decl :=
    EnvMap.lookup kn Σ.(wf_env_ext_map).

  Lemma lookup_lookup_env Σ kn : lookup Σ kn = lookup_env Σ kn.
  Proof using Type.
    rewrite /lookup. destruct Σ as [Σ map repr]. pose (referenced_impl_sq_wf Σ).
    sq. apply EnvMap.lookup_spec; auto. now eapply wf_fresh_globals.
  Qed.

End WfEnv.


Create HintDb wf_env discriminated.
Global Hint Constants Opaque : wf_env.
Global Hint Variables Opaque : wf_env.

Global Hint Resolve referenced_impl_ext_wf : wf_env.
Global Hint Resolve referenced_impl_wf : wf_env.

Definition Σudecl_ref {cf : checker_flags} {guard : abstract_guard_impl} (Σ : referenced_impl_ext) :
  ∥ on_udecl Σ.(referenced_impl_env_ext).1 Σ.(referenced_impl_env_ext).2 ∥ :=
    map_squash (fun x => x.2) Σ.

Definition Σudecl {cf : checker_flags} {guard : abstract_guard_impl} (Σ : wf_env_ext) :
  ∥ on_udecl Σ.(referenced_impl_env_ext).1 Σ.(referenced_impl_env_ext).2 ∥ :=
  map_squash (fun x => x.2) Σ.

  Global Hint Resolve Σudecl : wf_env.

Ltac wf_env := auto with wf_env.


(** Build an optimized environment representation for lookups along with the graph associated to a well-formed
  global environment. The graph building is separated, so that [(build_wf_env_ext Σ wfΣ).(wf_env_ext_env)] is
  convertible to [Σ]. *)

Definition build_wf_env_ext {cf : checker_flags} {guard : abstract_guard_impl} (Σ : global_env_ext) (wfΣ : ∥ wf_ext Σ ∥) : wf_env_ext :=
  {| wf_env_ext_referenced :=
      {| referenced_impl_env_ext := Σ; referenced_impl_ext_wf := wfΣ |} ;
     wf_env_ext_map := EnvMap.of_global_env Σ.(declarations);
     wf_env_ext_map_repr := EnvMap.repr_global_env Σ.(declarations);
|}.

Section GraphSpec.
  Context {cf:checker_flags} {guard : abstract_guard_impl} {Σ : global_env_ext} (HΣ : ∥ wf Σ ∥)
      (Hφ : ∥ on_udecl Σ.1 Σ.2 ∥)
      (G : universes_graph) (HG : is_graph_of_uctx G (global_ext_uctx Σ)).

  Local Definition HΣ' : ∥ wf_ext Σ ∥.
  Proof.
    destruct HΣ, Hφ; now constructor.
  Qed.

  Lemma is_graph_of_uctx_levels (l : Level.t) :
    LevelSet.mem l (uGraph.wGraph.V G) <->
    LevelSet.mem l (global_ext_levels Σ).
  Proof using HG.
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

Program Global Instance canonical_abstract_env_prop {cf:checker_flags} {guard : abstract_guard_impl} :
  @abstract_env_prop _ _ _ canonical_abstract_env_struct :=
     {| abstract_env_ext_exists := fun Σ => sq (referenced_impl_env_ext Σ ; eq_refl); |}.
Next Obligation. wf_env. Qed.
Next Obligation.
  pose proof (referenced_impl_ext_wf X); sq.
  set (uctx := wf_ext_gc_of_uctx _); destruct uctx as [[l ctrs] Huctx].
  assert (consistent (global_ext_uctx X).2) as HC.
      { sq; apply (global_ext_uctx_consistent _ H). }
  simpl in HC. apply gc_consistent_iff in HC.
  split.
  - eapply leqb_level_n_spec0.
    + eapply gc_of_uctx_invariants; try eapply wf_ext_global_uctx_invariants; eauto.
    + Opaque gc_of_constraints. cbn in *. Transparent gc_of_constraints.
      destruct (gc_of_constraints X); inversion Huctx. now destruct H2.
    + unfold referenced_impl_ext_graph; cbn.
      set (G := graph_of_wf_ext _); destruct G as [G HG].
      cbn. unfold is_graph_of_uctx in HG. now rewrite Huctx in HG.
  - eapply leqb_level_n_spec.
    + eapply gc_of_uctx_invariants; try eapply wf_ext_global_uctx_invariants; eauto.
    + Opaque gc_of_constraints. cbn in *. Transparent gc_of_constraints.
      destruct (gc_of_constraints X); inversion Huctx. now destruct H2.
    + unfold referenced_impl_ext_graph; cbn.
      set (G := graph_of_wf_ext _); destruct G as [G HG].
      cbn. unfold is_graph_of_uctx in HG. now rewrite Huctx in HG.
Qed.
Next Obligation. apply guard_correct. Qed.
Next Obligation. now sq. Qed.
Next Obligation. wf_env. Qed.
Next Obligation. now split. Qed.
Next Obligation.
  rename H2 into Hudecl. unfold referenced_impl_graph; rewrite andb_and.
  pose proof (referenced_impl_graph_wf X) as HG.
  set (gph := (graph_of_wf X).π1) in *. clearbody gph. simpl in HG.
  pose proof (HG' := is_graph_of_uctx_add Hudecl HG).
  pose (global_ext_uctx := ContextSet.union udecl (global_uctx X)).
  rewrite - (is_consistent_spec global_ext_uctx) (is_consistent_spec2 HG').
  assert (reorder : forall a b c : Prop, (a -> b <-> c) -> a /\ b <-> a /\ c) by intuition; apply reorder.
  move=> ?; rewrite consistent_extension_on_union.
  1:{ pose proof (referenced_impl_wf X); sq.
      apply: PCUICUnivSubstitutionConv.levels_global_constraint. }
  cbn.
  change (CS.union _ _) with global_ext_uctx.2.
  apply: consistent_ext_on_full_ext=> //.
  apply: add_uctx_subgraph.
Qed.
Next Obligation.
  apply (reference_pop_decls_correct X decls prf X (referenced_pop X) eq_refl eq_refl).
Qed.


Program Global Instance optimized_abstract_env_prop {cf:checker_flags} {guard : abstract_guard_impl} :
  @abstract_env_prop _ _ _ optimized_abstract_env_struct :=
     {| abstract_env_ext_exists := fun Σ => sq (referenced_impl_env_ext Σ ; eq_refl); |}.
Next Obligation. wf_env. Qed.
Next Obligation. pose (referenced_impl_ext_wf X). sq.
    erewrite EnvMap.lookup_spec; try reflexivity.
    1: apply wf_fresh_globals; eauto.
    1: apply wf_env_ext_map_repr. Qed.
Next Obligation.
    epose (prf := abstract_env_leqb_level_n_correct X.(wf_env_ext_referenced) eq_refl).
    erewrite wf_ext_gc_of_uctx_irr.  exact prf. Qed.
Next Obligation. eapply guard_correct. Qed.
Next Obligation. now sq. Qed.
Next Obligation. wf_env. Qed.
Next Obligation. now split. Qed.
Next Obligation.
  now erewrite (abstract_env_is_consistent_correct X.(wf_env_referenced)); eauto. Qed.
Next Obligation. unfold optim_pop. set (optim_pop_obligation_1 cf X). clearbody r.
  pose proof (reference_pop_decls_correct X decls prf X (referenced_pop X) eq_refl eq_refl).
  specialize (prf _ eq_refl).
  destruct (declarations X); cbn; inversion prf; inversion H0. subst.
  now destruct x.
Qed.

Definition canonical_abstract_env_impl {cf:checker_flags} {guard : abstract_guard_impl} : abstract_env_impl :=
  (referenced_impl ; referenced_impl_ext ; canonical_abstract_env_struct ; canonical_abstract_env_prop).

Definition optimized_abstract_env_impl {cf:checker_flags} {guard : abstract_guard_impl} : abstract_env_impl :=
  (wf_env; wf_env_ext ; optimized_abstract_env_struct ; optimized_abstract_env_prop).

Definition build_wf_env_from_env {cf : checker_flags} (Σ : global_env) (wfΣ : ∥ PCUICTyping.wf Σ ∥) : wf_env
  :=
  let Σm := EnvMap.of_global_env Σ.(declarations) in
  {| wf_env_referenced := {| referenced_impl_env := Σ; referenced_impl_wf := wfΣ |} ;
     wf_env_map := Σm;
     wf_env_map_repr := EnvMap.repr_global_env Σ.(declarations);
 |}.
