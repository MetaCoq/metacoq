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

Definition init_env : global_env :=
   {| universes := (LS.singleton Level.lzero , CS.empty); declarations := []; retroknowledge := Retroknowledge.empty |}.

Definition on_global_univ_init_env : on_global_univs init_env.
  repeat split. 
  - intros x Hx; cbn in *. inversion Hx.
  - intros x Hx; cbn in *. destruct x; eauto. now inversion Hx.
  - red. unshelve eexists. 
    + econstructor; eauto. intros; exact 1%positive.
    + red. intros ? ?. cbn in *. inversion H.
Qed.          

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
Qed. 


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
  {| abstract_env_lookup := fun Σ => lookup_env (referenced_impl_env_ext Σ) ;
     abstract_env_ext_retroknowledge := fun Σ => (referenced_impl_env_ext Σ).(retroknowledge) ;
     abstract_env_conv_pb_relb := fun Σ conv_pb => conv_pb_relb (referenced_impl_ext_graph Σ) conv_pb ;
     abstract_env_compare_global_instance := fun Σ =>
      compare_global_instance (referenced_impl_env_ext Σ)
                              (check_eqb_universe (referenced_impl_ext_graph Σ));
     abstract_env_level_mem := fun Σ => level_mem (referenced_impl_env_ext Σ);
     abstract_env_ext_wf_universeb := fun Σ u => wf_universeb Σ u;
     abstract_env_check_constraints := fun Σ => check_constraints (referenced_impl_ext_graph Σ);

     abstract_env_guard := fun Σ fix_cofix => guard_impl fix_cofix (referenced_impl_env_ext Σ);
     abstract_env_ext_rel := fun X Σ => Σ = referenced_impl_env_ext X;
     abstract_env_empty := {|
       referenced_impl_env := {| universes := init_env ; declarations := []; retroknowledge := Retroknowledge.empty |};
 |} ;
 abstract_env_init := fun cs retro H =>  {|
 referenced_impl_env := {| universes := cs ; declarations := []; retroknowledge := retro |};
 |} ;
 abstract_env_add_decl := fun X kn d H => 
  {| referenced_impl_env := add_global_decl X.(referenced_impl_env) (kn,d);
   |};
 abstract_env_empty_ext X := {| referenced_impl_env_ext := (X , Monomorphic_ctx);
 |} ;
 abstract_env_univ X := X ;
 abstract_env_global_declarations X := declarations X;
 abstract_env_retroknowledge X := X.(retroknowledge) ;
 abstract_env_is_consistent uctx := wGraph.is_acyclic (make_graph uctx);
 abstract_env_is_consistent_uctx X uctx :=
   let G := referenced_impl_graph X in
   let G' := add_uctx uctx G in
   wGraph.is_acyclic G' && wGraph.IsFullSubgraph.is_full_extension G G' ;
 abstract_env_add_uctx X uctx udecl Hdecl Hglobal := {| referenced_impl_env_ext := (X.(referenced_impl_env) , udecl);
 |} ;
 abstract_env_rel := fun X Σ => Σ = referenced_impl_env X ;
 abstract_pop_decls := referenced_pop ;
 abstract_make_wf_env_ext := make_wf_env_ext ;
 |}.
Next Obligation. sq. constructor; cbn; eauto. apply on_global_univ_init_env. econstructor. Qed.
Next Obligation. sq; constructor; cbn; eauto. econstructor. Qed.
Next Obligation. pose proof (referenced_impl_wf X) as [[? ?]]; sq; destruct H.
  econstructor; eauto. econstructor; eauto. econstructor; eauto. Qed.
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

Program Definition wf_env_empty {cf:checker_flags} {guard : abstract_guard_impl} :=
 {|   
  wf_env_referenced := abstract_env_empty ;
  wf_env_map := EnvMap.empty;
  |}.
  
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

Program Definition optim_make_wf_env_ext {cf:checker_flags} {guard : abstract_guard_impl} (Σ : wf_env) (univs : universes_decl) 
  (prf : forall Σ0 : global_env, abstract_env_rel Σ.(wf_env_referenced) Σ0 -> ∥ wf_ext (Σ0, univs) ∥) : wf_env_ext :=
  {| wf_env_ext_referenced := {| referenced_impl_env_ext := (Σ, univs);|} ;
     wf_env_ext_map := Σ.(wf_env_map);
     wf_env_ext_map_repr := Σ.(wf_env_map_repr) |}.
     
Program Global Instance optimized_abstract_env_struct {cf:checker_flags} {guard : abstract_guard_impl} :
  abstract_env_struct wf_env wf_env_ext :=
 {|
 abstract_env_lookup := fun Σ k => EnvMap.lookup k (wf_env_ext_map Σ);
 abstract_env_ext_retroknowledge := fun X => X.(wf_env_ext_referenced).(retroknowledge);
 abstract_env_conv_pb_relb X := abstract_env_conv_pb_relb X.(wf_env_ext_referenced);
 abstract_env_compare_global_instance X := abstract_env_compare_global_instance X.(wf_env_ext_referenced);
 abstract_env_level_mem X := abstract_env_level_mem X.(wf_env_ext_referenced);
 abstract_env_ext_wf_universeb X := abstract_env_ext_wf_universeb X.(wf_env_ext_referenced);
 abstract_env_check_constraints X := abstract_env_check_constraints X.(wf_env_ext_referenced);
 abstract_env_guard := fun Σ fix_cofix => guard_impl fix_cofix (wf_env_ext_referenced Σ);
 abstract_env_ext_rel X := abstract_env_ext_rel X.(wf_env_ext_referenced);
 
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
 abstract_env_rel X := abstract_env_rel X.(wf_env_referenced) ;
 abstract_pop_decls := optim_pop ;
 abstract_make_wf_env_ext := optim_make_wf_env_ext ;
 |}.
Next Obligation.
  pose proof (X.(wf_env_referenced).(referenced_impl_wf)) as [?].
  sq. destruct H.  
  apply EnvMap.repr_add; eauto; try eapply wf_fresh_globals; eauto. 
  apply wf_env_map_repr.
Qed. 
Next Obligation. apply wf_env_map_repr. Qed.
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

  Lemma check_constraints_spec ctrs
    : check_constraints G ctrs -> valid_constraints (global_ext_constraints Σ) ctrs.
  Proof using HG HΣ Hφ.
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
Next Obligation. apply check_conv_pb_relb_correct; eauto; wf_env.   
   apply (graph_of_wf_ext X).π2. Qed.
Next Obligation. eapply reflect_iff. eapply reflect_R_global_instance; eauto.
  move => ? ? /wf_universe_reflect ? - /wf_universe_reflect ?.
  apply iff_reflect;  apply check_conv_pb_relb_correct with (conv_pb := Conv); eauto; wf_env. 
  apply (graph_of_wf_ext X).π2.
  move => ? ? /wf_universe_reflect ? - /wf_universe_reflect ?.
  apply X0; eauto. 
  all: rewrite wf_universeb_instance_forall.
  revert H; move => / wf_universe_instanceP ?; eauto. 
  revert H0; move => / wf_universe_instanceP ?; eauto. 
Qed. 
Next Obligation. split; intros. 
  - eapply check_constraints_complete; eauto.
    apply referenced_impl_sq_wf. apply Σudecl_ref.
    apply (graph_of_wf_ext X).π2.
    now destruct X. 
  - eapply check_constraints_spec; eauto.    
  apply referenced_impl_sq_wf. apply Σudecl_ref.
  apply (graph_of_wf_ext X).π2.
  Qed. 
Next Obligation. apply guard_correct. Qed.
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
  pose proof (HG' := is_graph_of_uctx_add Hudecl HG).
  rewrite - (is_consistent_spec (global_ext_uctx (X, udecl))) (is_consistent_spec2 HG').
  assert (reorder : forall a b c : Prop, (a -> b <-> c) -> a /\ b <-> a /\ c) by intuition; apply reorder.
  move=> ?; rewrite consistent_extension_on_union.
  2:{ pose proof (referenced_impl_wf X); sq.
      apply: PCUICUnivSubstitutionConv.levels_global_constraint. }
  change (CS.union _ _) with (global_ext_uctx (X, udecl)).2.
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
  Next Obligation. now rewrite (abstract_env_compare_universe_correct X.(wf_env_ext_referenced)). Qed.
  Next Obligation. now rewrite (abstract_env_compare_global_instance_correct X.(wf_env_ext_referenced)); eauto. Qed.
  Next Obligation. now rewrite (abstract_env_check_constraints_correct X.(wf_env_ext_referenced)); eauto. Qed.
  Next Obligation. eapply guard_correct. Qed.
  Next Obligation. now sq. Qed.
Next Obligation. wf_env. Qed.
Next Obligation. now split. Qed.
Next Obligation. now split. Qed.
Next Obligation. now erewrite (@abstract_env_is_consistent_correct _ _ _ _ canonical_abstract_env_prop); eauto. Qed.
Next Obligation. now erewrite (abstract_env_is_consistent_uctx_correct X.(wf_env_referenced)); eauto. Qed.
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
