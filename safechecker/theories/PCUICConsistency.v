(* The safe checker gives us a sound and complete wh-normalizer for
   PCUIC, assuming strong normalization. Combined with canonicity,
   this allows us to prove that PCUIC is consistent, i.e. there
   is no axiom-free proof of [forall (P : Prop), P] in the empty
   context. To do so we use weakening to add an empty inductive, the
   provided term to build an inhabitant and then canonicity to show
   that this is a contradiction. *)

From Coq Require Import Ascii String.
From Equations Require Import Equations.
From MetaCoq.PCUIC Require Import PCUICAst.
From MetaCoq.PCUIC Require Import PCUICAstUtils.
From MetaCoq.PCUIC Require Import PCUICCanonicity.
From MetaCoq.PCUIC Require Import PCUICInductiveInversion.
From MetaCoq.PCUIC Require Import PCUICInversion.
From MetaCoq.PCUIC Require Import PCUICLiftSubst.
From MetaCoq.PCUIC Require Import PCUICSR.
From MetaCoq.PCUIC Require Import PCUICSafeLemmata.
From MetaCoq.PCUIC Require Import PCUICTyping.
From MetaCoq.PCUIC Require Import PCUICUnivSubst.
From MetaCoq.PCUIC Require Import PCUICValidity.
From MetaCoq.PCUIC Require Import PCUICWeakeningEnv.
From MetaCoq.PCUIC Require Import PCUICWellScopedCumulativity.
From MetaCoq.Template Require Import config utils.
From MetaCoq.SafeChecker Require Import PCUICSafeReduce.

Local Opaque hnf.

Fixpoint string_repeat c (n : nat) : string :=
  match n with
  | 0 => ""
  | S n => String c (string_repeat c n)
  end.

Lemma string_repeat_length c n :
  String.length (string_repeat c n) = n.
Proof.
  induction n; cbn; auto with arith.
Qed.

Definition max_name_length (Σ : global_env) : nat :=
  fold_right max 0 (map (fun '(kn, _) => String.length (string_of_kername kn)) Σ).

Lemma max_name_length_ge Σ :
  Forall (fun '(kn, _) => String.length (string_of_kername kn) <= max_name_length Σ) Σ.
Proof.
  induction Σ as [|(kn&decl) Σ IH]; cbn; constructor.
  - lia.
  - eapply Forall_impl; eauto.
    intros (?&?); cbn; intros.
    fold (max_name_length Σ).
    lia.
Qed.

Definition make_fresh_name (Σ : global_env) : kername :=
  (MPfile [], string_repeat "a"%char (S (max_name_length Σ))).

Lemma make_fresh_name_fresh Σ :
  fresh_global (make_fresh_name Σ) Σ.
Proof.
  pose proof (max_name_length_ge Σ) as all.
  eapply Forall_impl; eauto.
  cbn.
  intros (kn&decl) le.
  cbn.
  intros ->.
  unfold make_fresh_name in le.
  cbn in le.
  rewrite string_repeat_length in le.
  lia.
Qed.

Definition Prop_univ := Universe.of_levels (inl PropLevel.lProp).

Definition False_oib : one_inductive_body :=
  {| ind_name := "False";
     ind_indices := [];
     ind_sort := Prop_univ;
     ind_type := tSort Prop_univ;
     ind_kelim := IntoAny;
     ind_ctors := [];
     ind_projs := [];
     ind_relevance := Relevant |}.

Definition False_mib : mutual_inductive_body :=
  {| ind_finite := BiFinite;
     ind_npars := 0;
     ind_params := [];
     ind_bodies := [False_oib];
     ind_universes := Monomorphic_ctx ContextSet.empty;
     ind_variance := None |}.

Definition axiom_free Σ :=
  forall c decl, declared_constant Σ c decl -> cst_body decl <> None.

Lemma axiom_free_axiom_free_value Σ t :
  axiom_free Σ ->
  axiom_free_value Σ [] t.
Proof.
  intros axfree.
  cut (Forall is_true []); [|constructor].
  generalize ([] : list bool).
  induction t; intros axfree_args all_true; cbn; auto.
  - destruct lookup_env eqn:find; auto.
    destruct g; auto.
    destruct c; auto.
    apply axfree in find; cbn in *.
    now destruct cst_body0.
  - destruct nth_error; auto.
    rewrite nth_nth_error.
    destruct nth_error eqn:nth; auto.
    eapply nth_error_forall in nth; eauto.
Qed.

Definition binder := {| binder_name := nNamed "P"; binder_relevance := Relevant |}.

Theorem pcuic_consistent {cf:checker_flags} Σ t :
  wf_ext Σ ->
  axiom_free Σ ->
  (* t : forall (P : Prop), P *)
  Σ ;;; [] |- t : tProd binder (tSort Prop_univ) (tRel 0) ->
  False.
Proof.
  intros wfΣ axfree cons.
  set (Σext := ((make_fresh_name Σ, InductiveDecl False_mib) :: Σ.1, Σ.2)).
  assert (wf': wf_ext Σext).
  { constructor; [constructor|].
    - destruct wfΣ; auto.
    - apply make_fresh_name_fresh.
    - red.
      cbn.
      split.
      { now intros ? ?%LevelSet.empty_spec. }
      split.
      { now intros ? ?%ConstraintSet.empty_spec. }
      split; auto.
      destruct wfΣ as (?&(?&?&?&[val sat])).
      exists val.
      intros l isin.
      apply sat; auto.
      apply ConstraintSet.union_spec.
      apply ConstraintSet.union_spec in isin as [?%ConstraintSet.empty_spec|]; auto.
    - hnf.
      constructor.
      + constructor.
        * econstructor; cbn; auto.
          -- exists (Universe.super Prop_univ).
             constructor; auto.
             constructor.
          -- instantiate (1 := []).
             constructor.
          -- now cbn.
          -- intros; congruence.
        * constructor.
      + constructor.
      + reflexivity.
      + reflexivity.
    - destruct wfΣ; auto. }
  eapply (env_prop_typing PCUICWeakeningEnv.weakening_env) in cons; auto.
  3: exists [(make_fresh_name Σ, InductiveDecl False_mib)]; reflexivity.
  2: now destruct wf'.
  
  set (Σ' := _ ++ _) in cons.
  set (False_ty := tInd (mkInd (make_fresh_name Σ) 0) []).
  assert (typ_false: (Σ', Σ.2);;; [] |- tApp t False_ty : False_ty).
  { apply validity in cons as typ_prod; auto.
    destruct typ_prod. red in t0.
    eapply type_App with (B := tRel 0) (u := False_ty); eauto.
    eapply type_Ind with (u := []) (mdecl := False_mib) (idecl := False_oib); eauto.
    - hnf.
      cbn.
      unfold declared_minductive.
      cbn.
      rewrite eq_kername_refl.
      auto.
    - cbn.
      auto. }
  assert (sqwf: ∥ wf (Σ', Σ.2).1 ∥) by now destruct wf'.
  pose proof (iswelltyped _ _ _ _ typ_false) as wt.
  pose proof (@hnf_sound _ _ sqwf _ _ wt) as [r].
  pose proof (@hnf_complete _ _ sqwf _ _ wt) as [w].
  eapply subject_reduction_closed in typ_false; eauto.
  eapply whnf_ind_finite with (indargs := []) in typ_false as ctor; auto.
  - unfold isConstruct_app in ctor.
    destruct decompose_app eqn:decomp.
    apply decompose_app_inv in decomp.
    rewrite decomp in typ_false.
    destruct t0; try discriminate ctor.
    apply inversion_mkApps in typ_false as H; auto.
    destruct H as (?&typ_ctor&_).
    apply inversion_Construct in typ_ctor as (?&?&?&?&?&?&?); auto.
    eapply Construct_Ind_ind_eq with (args' := []) in typ_false; tea.
    2: eauto.
    destruct (on_declared_constructor d).
    destruct p.
    destruct s.
    destruct p.
    destruct typ_false as (((((->&_)&_)&_)&_)&_).
    clear -d.
    destruct d as ((?&?)&?).
    cbn in *.
    red in H.
    cbn in *.
    rewrite eq_kername_refl in H.
    noconf H.
    noconf H0.
    cbn in H1.
    rewrite nth_error_nil in H1.
    discriminate.
  - eapply axiom_free_axiom_free_value.
    intros kn decl isdecl.
    hnf in isdecl.
    cbn in isdecl.
    destruct eq_kername; [noconf isdecl|].
    eapply axfree; eauto.
  - unfold check_recursivity_kind.
    cbn.
    rewrite eq_kername_refl; auto.
Qed.
