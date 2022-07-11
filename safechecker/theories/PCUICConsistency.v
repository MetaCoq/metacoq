(* The safe checker gives us a sound and complete wh-normalizer for
   PCUIC, assuming strong normalization. Combined with canonicity,
   this allows us to prove that PCUIC is consistent, i.e. there
   is no axiom-free proof of [forall (P : Prop), P] in the empty
   context. To do so we use weakening to add an empty inductive, the
   provided term to build an inhabitant and then canonicity to show
   that this is a contradiction. *)

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
From MetaCoq.PCUIC Require Import PCUICWeakeningEnvConv.
From MetaCoq.PCUIC Require Import PCUICWeakeningEnvTyp.
From MetaCoq.PCUIC Require Import PCUICWellScopedCumulativity.
From MetaCoq.PCUIC Require Import PCUICSN.
From MetaCoq.Template Require Import config utils EnvMap.
From MetaCoq.SafeChecker Require Import PCUICWfEnv PCUICSafeReduce PCUICWfEnvImpl.

Local Opaque hnf.

Fixpoint string_repeat c (n : nat) : string :=
  match n with
  | 0 => ""
  | S n => String.String c (string_repeat c n)
  end.

Lemma string_repeat_length c n :
  String.length (string_repeat c n) = n.
Proof.
  induction n; cbn; auto with arith.
Qed.

Definition max_name_length (Σ : global_declarations) : nat :=
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
  (MPfile [], string_repeat "a"%byte (S (max_name_length Σ.(declarations)))).

Lemma make_fresh_name_fresh Σ :
  fresh_global (make_fresh_name Σ) Σ.(declarations).
Proof.
  pose proof (max_name_length_ge Σ.(declarations)) as all.
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
     ind_universes := Monomorphic_ctx;
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

Definition global_env_add (Σ : global_env) d :=
  {| universes := Σ.(universes); declarations := d :: Σ.(declarations) |}.

Theorem pcuic_consistent {cf:checker_flags} {nor : normalizing_flags} {guard : abstract_guard_impl}
  (_Σ :referenced_impl_ext) t :
  axiom_free _Σ ->
  (* t : forall (P : Prop), P *)
  _Σ ;;; [] |- t : tProd binder (tSort Prop_univ) (tRel 0) ->
  False.
Proof.
  intros axfree cons.
  set (Σ := referenced_impl_env_ext _Σ); set (wfΣ := referenced_impl_ext_wf _Σ).
  set (Σext := (global_env_add Σ.1 (make_fresh_name Σ, InductiveDecl False_mib), Σ.2)).
  destruct wfΣ as [wfΣ].
  assert (wf': wf_ext Σext).
  { constructor; [constructor|]; auto; try apply wfΣ.
    constructor; auto.
    - apply wfΣ.
    - apply make_fresh_name_fresh.
    - split; first now intros ? ?%LevelSet.empty_spec.
      split; first now intros ? ?%ConstraintSet.empty_spec.
      destruct wfΣ as (?&(?&?&[val sat]&monoval)); split.
      1: { 
        exists val.
        intros l isin.
        apply sat; auto.
        apply ConstraintSet.union_spec.
        apply ConstraintSet.union_spec in isin as [?%ConstraintSet.empty_spec|]; auto.
      }
      intros v hv; exists v; split; [intros ? []%CS.empty_spec| now intros ??].
    - hnf.
      constructor.
      + constructor.
        * econstructor; cbnr; auto.
          -- exists (Universe.super Prop_univ).
             split; [cbnr|].
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
  }
  eapply (env_prop_typing weakening_env) in cons; auto.
  2:instantiate (1:=Σext.1).
  3:{ split; auto; cbn. split; [lsets|csets].
      exists [(make_fresh_name Σ.1, InductiveDecl False_mib)]; reflexivity. }
  2: now destruct wf'.

  set (Σ' := Σext.1) in cons.
  set (False_ty := tInd (mkInd (make_fresh_name Σ) 0) []).
  assert (typ_false: (Σ', Σ.2);;; [] |- tApp t False_ty : False_ty).
  { apply validity in cons as typ_prod; auto.
    destruct typ_prod as (s & e & Hs).
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
  pose proof (iswelltyped typ_false) as wt.
  set (_Σ' := Build_referenced_impl_ext cf _ Σext (sq wf')). cbn in *.
  unshelve epose proof (hnf_sound (X_type := canonical_abstract_env_ext_impl) (X := _Σ') (Γ := []) (t := tApp t False_ty) Σext eq_refl) as [r].
  1: cbn; intros; subst; exact wt.
  unshelve epose proof (hnf_complete (X_type := canonical_abstract_env_ext_impl) (X := _Σ') (Γ := []) (t := tApp t False_ty) Σext eq_refl) as [w].
  1 : cbn; intros; subst; exact wt.
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
