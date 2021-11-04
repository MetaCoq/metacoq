(* Distributed under the terms of the MIT license. *)
From Coq Require Import ProofIrrelevance.
From MetaCoq.Template Require Import config utils uGraph.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICReflect PCUICTyping.

(** Injectivity of declared_*, inversion lemmas on declared global references and 
    universe consistency of the global environment.
*)

Lemma declared_constant_inj {Σ c} decl1 decl2 :
  declared_constant Σ c decl1 -> declared_constant Σ c decl2 -> decl1 = decl2.
Proof.
  intros. unfold declared_constant in *. rewrite H in H0.
  now inv H0.
Qed.

Lemma declared_inductive_inj {Σ mdecl mdecl' ind idecl idecl'} :
  declared_inductive Σ ind mdecl' idecl' ->
  declared_inductive Σ ind mdecl idecl ->
  mdecl = mdecl' /\ idecl = idecl'.
Proof.
  intros [] []. unfold declared_minductive in *.
  rewrite H in H1. inversion H1. subst. rewrite H2 in H0. inversion H0. eauto.
Qed.

Lemma declared_constructor_inj {Σ mdecl mdecl' idecl idecl' cdecl cdecl' c} :
  declared_constructor Σ c mdecl' idecl' cdecl ->
  declared_constructor Σ c mdecl idecl cdecl' ->
  mdecl = mdecl' /\ idecl = idecl'  /\ cdecl = cdecl'.
Proof.
  intros [] []. 
  destruct (declared_inductive_inj H H1); subst.
  rewrite H0 in H2. intuition congruence.
Qed.

Lemma declared_projection_inj {Σ mdecl mdecl' idecl idecl' cdecl cdecl' pdecl pdecl' p} :
  declared_projection Σ p mdecl idecl cdecl pdecl ->
  declared_projection Σ p mdecl' idecl' cdecl' pdecl' ->
  mdecl = mdecl' /\ idecl = idecl'  /\ cdecl = cdecl' /\ pdecl = pdecl'.
Proof.
  intros [] []. 
  destruct (declared_constructor_inj H H1) as [? []]; subst.
  destruct H0, H2.
  rewrite H0 in H2. intuition congruence.
Qed.

Lemma declared_inductive_minductive {Σ ind mdecl idecl} :
  declared_inductive Σ ind mdecl idecl -> declared_minductive Σ (inductive_mind ind) mdecl.
Proof. now intros []. Qed.
#[global]
Hint Resolve declared_inductive_minductive : pcuic core.

Coercion declared_inductive_minductive : declared_inductive >-> declared_minductive.

Lemma declared_constructor_inductive {Σ ind mdecl idecl cdecl} :
  declared_constructor Σ ind mdecl idecl cdecl ->
  declared_inductive Σ ind.1 mdecl idecl.
Proof. now intros []. Qed.
Coercion declared_constructor_inductive : declared_constructor >-> declared_inductive.

Lemma declared_projection_constructor {Σ ind mdecl idecl cdecl pdecl} :
  declared_projection Σ ind mdecl idecl cdecl pdecl ->
  declared_constructor Σ (ind.1.1, 0) mdecl idecl cdecl.
Proof. now intros []. Qed.
Coercion declared_projection_constructor : declared_projection >-> declared_constructor.

Section DeclaredInv.
  Context {cf:checker_flags} {Σ} {wfΣ : wf Σ}.

  Lemma declared_minductive_ind_npars  {mdecl ind} :
    declared_minductive Σ ind mdecl ->
    ind_npars mdecl = context_assumptions mdecl.(ind_params).
  Proof.
    intros h.
    unfold declared_minductive in h.
    eapply lookup_on_global_env in h. 2: eauto.
    destruct h as [Σ' [wfΣ' decl']].
    red in decl'. destruct decl' as [h ? ? ?].
    now rewrite onNpars.
  Qed.

End DeclaredInv.

Definition wf_global_uctx_invariants {cf:checker_flags} Σ :
  wf Σ ->
  global_uctx_invariants (global_uctx Σ).
Proof.
 intros HΣ. split.
 - cbn. eapply LevelSet.mem_spec, global_levels_Set.
 - unfold global_uctx.
   simpl. intros [[l ct] l'] Hctr. simpl in *.
   induction Σ in HΣ, l, ct, l', Hctr |- *.
   + apply ConstraintSetFact.empty_iff in Hctr; contradiction.
   + simpl in *. apply ConstraintSet.union_spec in Hctr.
     destruct Hctr as [Hctr|Hctr].
     * split.
       -- inversion HΣ; subst.
          destruct H2 as [HH1 [HH HH3]].
          subst udecl. destruct d as [decl|decl]; simpl in *.
          ++ destruct decl; simpl in *.
             destruct cst_universes0 ; [
               eapply (HH (l, ct, l') Hctr)
             | apply ConstraintSetFact.empty_iff in Hctr ; contradiction
             ].
          ++ destruct decl. simpl in *.
             destruct ind_universes0 ; [
               eapply (HH (l, ct, l') Hctr)
             | apply ConstraintSetFact.empty_iff in Hctr; contradiction
             ].
       -- inversion HΣ. subst.
          destruct H2 as [HH1 [HH HH3]].
          subst udecl. destruct d as [decl|decl].
          all: simpl in *.
          ++ destruct decl. simpl in *.
             destruct cst_universes0 ; [
               eapply (HH (l, ct, l') Hctr)
             | apply ConstraintSetFact.empty_iff in Hctr; contradiction
             ].
          ++ destruct decl. simpl in *.
             destruct ind_universes0; [
               eapply (HH (l, ct, l') Hctr)
             | apply ConstraintSetFact.empty_iff in Hctr; contradiction
             ].
     * inversion HΣ. subst.
       split.
       all: apply LevelSet.union_spec.
       all: right.
       all: unshelve eapply (IHΣ _ _ _ _ Hctr).
       all: try eassumption.
Qed.

Definition wf_ext_global_uctx_invariants {cf:checker_flags} Σ :
  wf_ext Σ ->
  global_uctx_invariants (global_ext_uctx Σ).
Proof.
 intros HΣ. split.
 - apply LevelSet.union_spec. right. apply LevelSet.mem_spec, global_levels_Set.
 - destruct Σ as [Σ φ]. destruct HΣ as [HΣ Hφ].
   destruct (wf_global_uctx_invariants _ HΣ) as [_ XX].
   unfold global_ext_uctx, global_ext_levels, global_ext_constraints.
   simpl. intros [[l ct] l'] Hctr. simpl in *. apply ConstraintSet.union_spec in Hctr.
   destruct Hctr as [Hctr|Hctr].
   + destruct Hφ as [_ [HH _]]. apply (HH _ Hctr).
   + specialize (XX _ Hctr).
     split; apply LevelSet.union_spec; right; apply XX.
Qed.

Lemma wf_consistent {cf:checker_flags} Σ : wf Σ -> consistent (global_constraints Σ).
Proof.
  destruct Σ.
  - exists {| valuation_mono := fun _ => 1%positive;  valuation_poly := fun _ => 0 |}.
    intros x Hx; now apply ConstraintSetFact.empty_iff in Hx.
  - inversion 1; subst. subst udecl. clear -H2.
    destruct H2 as [_ [_ [_ [v Hv]]]].
    exists v. intros ct Hc. apply Hv. simpl in *.
    apply ConstraintSet.union_spec in Hc. destruct Hc.
    apply ConstraintSet.union_spec; simpl.
    + left. destruct d.
      destruct c, cst_universes0. assumption.
      apply ConstraintSetFact.empty_iff in H; contradiction.
      destruct m, ind_universes0. assumption.
      apply ConstraintSetFact.empty_iff in H; contradiction.
    + apply ConstraintSet.union_spec; simpl.
      now right.
Qed.

Definition global_ext_uctx_consistent {cf:checker_flags} Σ
 : wf_ext Σ -> consistent (global_ext_uctx Σ).2.
Proof. 
  intros HΣ. cbn. unfold global_ext_constraints.
  unfold wf_ext, on_global_env_ext in HΣ.
  destruct HΣ as [_ [_ [_ HH]]]. apply HH.
Qed.


