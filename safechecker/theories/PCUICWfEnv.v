(* Distributed under the terms of the MIT license. *)
From Coq Require Import ssreflect.
From MetaCoq.Template Require Import config utils uGraph EnvMap.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICReduction
     PCUICReflect PCUICSafeLemmata PCUICTyping PCUICGlobalEnv PCUICWfUniverses.
From MetaCoq.SafeChecker Require Import PCUICEqualityDec.

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

Definition level_mem : global_env_ext -> Level.t -> bool
  := fun X l => LevelSet.mem l (global_ext_levels X).

Class abstract_env_struct {cf:checker_flags} (abstract_env_impl : Type) := {
  abstract_env_lookup : abstract_env_impl -> kername -> option global_decl;
  abstract_env_eq : abstract_env_impl -> Universe.t -> Universe.t -> bool;
  abstract_env_leq : abstract_env_impl -> Universe.t -> Universe.t -> bool;
  abstract_env_compare_global_instance : abstract_env_impl -> (Universe.t -> Universe.t -> bool) -> global_reference -> nat -> list Level.t -> list Level.t -> bool;
  abstract_env_level_mem : abstract_env_impl -> Level.t -> bool;
  abstract_env_check_constraints : abstract_env_impl -> ConstraintSet.t -> bool;
  abstract_env_guard : abstract_env_impl -> FixCoFix -> context -> mfixpoint term -> bool;
  abstract_env_fixguard X := abstract_env_guard X Fix;
  abstract_env_cofixguard X := abstract_env_guard X CoFix;
  (* This part of the structure is here to state the correctness properties *)
  abstract_env_rel : abstract_env_impl -> global_env_ext -> Prop;
}.

Definition abstract_env_wf_universeb {cf:checker_flags} (abstract_env_impl : Type) (X_ : abstract_env_struct abstract_env_impl)
  : abstract_env_impl -> Universe.t -> bool
  := fun X s => match s with
  | Universe.lType l =>
    UnivExprSet.for_all
        (fun l0 : UnivExprSet.elt =>
        abstract_env_level_mem X (UnivExpr.get_level l0)) l
  | _ => true
  end.

Class abstract_env_prop {cf:checker_flags} (abstract_env_impl : Type) (X : abstract_env_struct abstract_env_impl) : Prop := {

  abstract_env_exists X : ∥ ∑ Σ , abstract_env_rel X Σ ∥;
  abstract_env_irr {X Σ Σ'} :
    abstract_env_rel X Σ -> abstract_env_rel X Σ' ->  Σ = Σ';
  abstract_env_wf {X Σ} : abstract_env_rel X Σ -> ∥ wf_ext Σ ∥;
  abstract_env_graph X {Σ} wfΣ: universes_graph := projT1 (graph_of_wf_ext (abstract_env_wf wfΣ)) ;
  abstract_env_graph_wf X {Σ} wfΣ : is_graph_of_uctx (abstract_env_graph X wfΣ) (global_ext_uctx Σ)
    := projT2 (graph_of_wf_ext (abstract_env_wf wfΣ));
  abstract_env_lookup_correct X {Σ} c : abstract_env_rel X Σ ->
    lookup_env Σ c = abstract_env_lookup X c ;
  abstract_env_eq_correct X {Σ} (wfΣ : abstract_env_rel X Σ) u u' : check_eqb_universe (abstract_env_graph X wfΣ) u u' = abstract_env_eq X u u';
  abstract_env_leq_correct X {Σ} (wfΣ : abstract_env_rel X Σ) u u' : check_leqb_universe (abstract_env_graph X wfΣ) u u' = abstract_env_leq X u u';
  abstract_env_compare_global_instance_correct X {Σ} (wfΣ : abstract_env_rel X Σ) leq ref n l l' : 
    compare_global_instance Σ (check_eqb_universe (abstract_env_graph X wfΣ)) leq ref n l l' = 
    abstract_env_compare_global_instance X leq ref n l l';
  abstract_env_level_mem_correct X {Σ} (wfΣ : abstract_env_rel X Σ) u : level_mem Σ u = abstract_env_level_mem X u;
  abstract_env_check_constraints_correct X {Σ} (wfΣ : abstract_env_rel X Σ) u : check_constraints (abstract_env_graph X wfΣ) u = abstract_env_check_constraints X u;
  abstract_env_guard_correct X {Σ} (wfΣ : abstract_env_rel X Σ) fix_cofix Γ mfix :
    guard fix_cofix Σ Γ mfix <-> abstract_env_guard X fix_cofix Γ mfix;
   }.

Definition abstract_env_wf_universeb_correct {cf:checker_flags} (abstract_env_impl : Type) (X_ : abstract_env_struct abstract_env_impl)
  (X__ : abstract_env_prop abstract_env_impl X_)
   X {Σ} (wfΣ : abstract_env_rel X Σ) u : wf_universeb Σ u = abstract_env_wf_universeb _ _ X u.
Proof.
  destruct u; auto.
  destruct n. cbn. repeat rewrite for_all_elements.
  induction (UnivExprSet.elements t_set); cbn; auto.
  rewrite <- IHl. erewrite <- abstract_env_level_mem_correct; eauto.
  reflexivity.
Defined.

Definition abstract_env_impl {cf:checker_flags} := ∑ X Y, abstract_env_prop X Y.

Global Instance abstract_env_impl_abstract_env_struct {cf:checker_flags} (Σ : abstract_env_impl) : abstract_env_struct Σ.π1.
  exact (Σ.π2.π1).
Defined.

Global Instance abstract_env_impl_abstract_env_prop {cf:checker_flags} (Σ : abstract_env_impl) : abstract_env_prop Σ.π1 _.
  exact (Σ.π2.π2).
Defined.

Definition abstract_env_cored {cf:checker_flags} (_X : abstract_env_impl) (X : _X.π1) {Σ Σ' Γ u v} : abstract_env_rel X Σ -> abstract_env_rel X Σ'
-> cored Σ Γ u v -> cored Σ' Γ u v.
Proof.
  intros HΣ HΣ' Hred. erewrite abstract_env_irr; eauto.
Defined.

Definition abstract_env_ext_sq_wf {cf:checker_flags} (X : abstract_env_impl) (x : X.π1)
  Σ (wfΣ : abstract_env_rel x Σ) : ∥ wf Σ∥.
  destruct (abstract_env_wf wfΣ).
  sq. auto.
Qed.

Record abstract_env_ext {cf:checker_flags} := {
      abstract_env_ext_env :> global_env_ext;
      abstract_env_ext_wf :> ∥ wf_ext abstract_env_ext_env ∥;
      abstract_env_ext_graph_ := projT1 (graph_of_wf_ext abstract_env_ext_wf);
      abstract_env_ext_graph_wf_ := projT2 (graph_of_wf_ext abstract_env_ext_wf)
  }.

Axiom guard_impl : FixCoFix -> global_env_ext -> context -> mfixpoint term -> bool.
Axiom guard_correct : forall fix_cofix Σ Γ mfix,
  guard fix_cofix Σ Γ mfix <-> guard_impl fix_cofix Σ Γ mfix.

Program Definition canonincal_abstract_env_struct {cf:checker_flags} :
  abstract_env_struct abstract_env_ext :=
  {| abstract_env_lookup := fun Σ => lookup_env (abstract_env_ext_env Σ) ;
     abstract_env_eq := fun Σ => check_eqb_universe (abstract_env_ext_graph_ Σ);
     abstract_env_leq := fun Σ => check_leqb_universe (abstract_env_ext_graph_ Σ) ;
     abstract_env_compare_global_instance := fun Σ =>
      compare_global_instance (abstract_env_ext_env Σ)
                              (check_eqb_universe (abstract_env_ext_graph_ Σ));
     abstract_env_level_mem := fun Σ => level_mem (abstract_env_ext_env Σ);
     abstract_env_check_constraints := fun Σ => check_constraints (abstract_env_ext_graph_ Σ);

     abstract_env_guard := fun Σ fix_cofix => guard_impl fix_cofix (abstract_env_ext_env Σ);
     abstract_env_rel := fun X Σ => Σ = abstract_env_ext_env X;
  |}.

Program Definition canonincal_abstract_env_prop {cf:checker_flags} :
  abstract_env_prop _ canonincal_abstract_env_struct :=
     {| abstract_env_exists := fun Σ => sq (abstract_env_ext_env Σ ; eq_refl); |}.
Next Obligation. apply abstract_env_ext_wf. Defined.
Next Obligation. apply guard_correct. Defined.
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

Program Definition optimized_abstract_env_struct {cf:checker_flags} :
  abstract_env_struct wf_env_ext :=
  {| abstract_env_lookup := fun Σ k => EnvMap.lookup k (wf_env_ext_map Σ);
     abstract_env_eq := fun Σ => check_eqb_universe (wf_env_ext_graph Σ);
     abstract_env_leq := fun Σ => check_leqb_universe (wf_env_ext_graph Σ) ;
     abstract_env_compare_global_instance := fun Σ =>
      compare_global_instance (wf_env_ext_env Σ)
                              (check_eqb_universe (wf_env_ext_graph Σ));
     abstract_env_level_mem := fun Σ l => LevelSet.mem l (uGraph.wGraph.V (wf_env_ext_graph Σ));
     abstract_env_check_constraints := fun Σ => check_constraints (wf_env_ext_graph Σ);

     abstract_env_guard := fun Σ fix_cofix => fake_guard_impl fix_cofix (wf_env_ext_env Σ);

     abstract_env_rel := fun X Σ => Σ = wf_env_ext_env X;
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

Program Definition optimized_abstract_env_prop {cf:checker_flags} :
abstract_env_prop _ optimized_abstract_env_struct :=
   {| abstract_env_exists := fun Σ => sq (wf_env_ext_env Σ ; eq_refl); |}.
Next Obligation. apply wf_env_ext_wf. Defined.
Next Obligation. pose (wf_env_ext_wf X). sq. 
  erewrite EnvMap.lookup_spec; try reflexivity. 
  1: apply wf_fresh_globals; eauto.
  1: apply wf_env_ext_map_repr. Qed.
Next Obligation. cbn. 
  pose proof (wf_env_ext_graph_wf X).
Admitted.
Next Obligation. Admitted.
Next Obligation. cbn.
  erewrite compare_global_instance_proper; eauto.  intros.
  exact (optimized_abstract_env_prop_obligation_4 cf X _ eq_refl u u').
Defined. 
Next Obligation. eapply eq_true_iff_eq.
                 split; intros; eapply is_graph_of_uctx_levels; eauto;
                 eapply wf_env_ext_graph_wf. Qed.
Next Obligation. unfold check_constraints.
  destruct gc_of_constraints; eauto.
  unfold check_gc_constraints.  
Admitted.
Next Obligation. apply fake_guard_correct. Defined.
