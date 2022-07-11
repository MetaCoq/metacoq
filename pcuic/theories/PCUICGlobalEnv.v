(* Distributed under the terms of the MIT license. *)
From Coq Require Import ProofIrrelevance.
From MetaCoq.Template Require Import config utils uGraph.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils.

Require Import ssreflect.


Lemma lookup_on_global_env {cf : checker_flags} Pcmp P (Σ : global_env) c decl :
  on_global_env Pcmp P Σ ->
  lookup_env Σ c = Some decl ->
  { Σ' : global_env & [× extends Σ' Σ, on_global_env Pcmp P Σ' &
      on_global_decl Pcmp P (Σ', universes_decl_of_decl decl) c decl] }.
Proof using Type.
  destruct Σ as [univs Σ]; unfold on_global_env, lookup_env; cbn.
  intros [cu Σp].
  induction Σp; simpl. congruence.
  destruct (eqb_specT c kn); subst.
  - intros [= ->].
    exists ({| universes := univs; declarations := Σ |}).
    split.
    * red; cbn. split; [split;[lsets|csets]|].
      exists [(kn, decl)] => //.
    * split => //.
    * apply o0.
  - intros hl. destruct (IHΣp hl) as [Σ' []].
    exists Σ'.
    split=> //.
    destruct e as [eu ed]. red; cbn in *.
    split; [auto|].
    destruct ed as [Σ'' ->].
    exists (Σ'' ,, (kn, d)) => //.
Qed.

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
  declared_constructor Σ (ind.(proj_ind), 0) mdecl idecl cdecl.
Proof. now intros []. Qed.
Coercion declared_projection_constructor : declared_projection >-> declared_constructor.

Section DeclaredInv.
  Context {cf:checker_flags} {Σ} {Pcmp P} {wfΣ : on_global_env Pcmp P Σ}.

  Lemma declared_minductive_ind_npars_gen  {mdecl ind} :
    declared_minductive Σ ind mdecl ->
    ind_npars mdecl = context_assumptions mdecl.(ind_params).
  Proof using wfΣ.
    intros h.
    unfold declared_minductive in h.
    eapply lookup_on_global_env in h; tea.
    destruct h as [Σ' [ext wfΣ' decl']].
    red in decl'. destruct decl' as [h ? ? ?].
    now rewrite onNpars.
  Qed.

End DeclaredInv.

Definition wf_global_uctx_invariants {cf:checker_flags} {Pcmp P} Σ :
  on_global_env Pcmp P Σ ->
  global_uctx_invariants (global_uctx Σ).
Proof.
 intros HΣ. split.
 - cbn. apply global_levels_InSet.
 - unfold global_uctx.
   simpl. intros [[l ct] l'] Hctr. simpl in *.
   induction Σ in HΣ, l, ct, l', Hctr |- *.
   destruct HΣ. cbn in *.
   destruct o as [decls cu].
   now specialize (decls _ Hctr).
Qed.

Lemma LevelSet_in_union_global Σ l ls : 
  LevelSet.In l (LevelSet.union ls (universes Σ).1) ->
  LevelSet.In l (LevelSet.union ls (global_levels (universes Σ))).
Proof.
  intros H % LevelSet.union_spec.
  apply LevelSet.union_spec. intuition auto.
  right. now apply LevelSet.union_spec.
Qed.

Definition wf_ext_global_uctx_invariants {cf:checker_flags} {Pcmp P} Σ :
  on_global_env_ext Pcmp P Σ ->
  global_uctx_invariants (global_ext_uctx Σ).
Proof.
 intros HΣ. split.
 - apply global_ext_levels_InSet.
 - destruct Σ as [Σ φ]. destruct HΣ as [HΣ Hφ].
   destruct (wf_global_uctx_invariants _ HΣ) as [_ XX].
   unfold global_ext_uctx, global_ext_levels, global_ext_constraints.
   simpl. intros [[l ct] l'] Hctr. simpl in *. apply ConstraintSet.union_spec in Hctr.
   destruct Hctr as [Hctr|Hctr].
   + destruct Hφ as [_ [HH _]]. specialize (HH _ Hctr). cbn in HH.
     intuition auto using LevelSet_in_union_global.
   + specialize (XX _ Hctr).
     split; apply LevelSet.union_spec; right; apply XX.
Qed.

Lemma wf_consistent {cf:checker_flags} Σ {Pcmp P} :
  on_global_env Pcmp P Σ -> consistent (global_constraints Σ).
Proof.
  destruct Σ.
  intros [cu ong]. apply cu.
Qed.

Definition global_ext_uctx_consistent {cf:checker_flags} {Pcmp P} Σ
 : on_global_env_ext Pcmp P Σ -> consistent (global_ext_uctx Σ).2.
Proof. 
  intros HΣ. cbn. unfold global_ext_constraints.
  unfold on_global_env_ext in HΣ.
  destruct HΣ as (_ & _ & _ & HH & _). apply HH.
Qed.


