(* Distributed under the terms of the MIT license.   *)

(** * Universe Substitution lemmas for typing derivations. *)

From Coq Require Import Bool String List BinPos Compare_dec Arith Lia ZArith
     CRelationClasses.
Require Import Coq.Program.Syntax Coq.Program.Basics.
From MetaCoq.Template Require Import utils config AstUtils UnivSubst.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICEquality
     PCUICUnivSubst PCUICTyping PCUICWeakeningEnv PCUICClosed
     PCUICReduction PCUICCumulativity PCUICWeakening.

Local Set Keyed Unification.

Module CS := ConstraintSet.
Module LS := LevelSet.

Create HintDb univ_subst.

Local Ltac aa := rdestruct; eauto with univ_subst.


Section CheckerFlags.
Context {cf : checker_flags}.


Global Instance subst_instance_list {A} `(UnivSubst A) : UnivSubst (list A)
  := fun u => map (subst_instance u).

Global Instance subst_instance_def {A : Set} `(UnivSubst A) : UnivSubst (def A)
  := fun u => map_def (subst_instance u) (subst_instance u).

Global Instance subst_instance_prod {A B} `(UnivSubst A) `(UnivSubst B)
  : UnivSubst (A × B)
  := fun u => on_pair (subst_instance u) (subst_instance u).

Global Instance subst_instance_nat : UnivSubst nat
  := fun _ n => n.



Lemma subst_instance_instance_length u1 u2 :
  #|subst_instance_instance u2 u1| = #|u1|.
Proof.
  unfold subst_instance_instance.
  now rewrite map_length.
Qed.

Lemma subst_instance_level_two u1 u2 l :
  subst_instance_level u1 (subst_instance_level u2 l)
  = subst_instance_level (subst_instance_instance u1 u2) l.
Proof.
  destruct l; cbn; try reflexivity.
  unfold subst_instance_instance.
  rewrite <- (map_nth (subst_instance_level u1)); reflexivity.
Qed.

Lemma subst_instance_univ_two u1 u2 s :
  subst_instance_univ u1 (subst_instance_univ u2 s)
  = subst_instance_univ (subst_instance_instance u1 u2) s.
Proof.
  unfold subst_instance_univ. rewrite NEL.map_map.
  apply NEL.map_ext. clear s.
  intros [l []]; unfold subst_instance_level_expr;
    now rewrite subst_instance_level_two.
Qed.

Lemma subst_instance_instance_two u1 u2 u :
  subst_instance_instance u1 (subst_instance_instance u2 u)
  = subst_instance_instance (subst_instance_instance u1 u2) u.
Proof.
  unfold subst_instance_instance. rewrite map_map.
  apply map_ext, subst_instance_level_two.
Qed.

Lemma subst_instance_constr_two u1 u2 t :
  subst_instance_constr u1 (subst_instance_constr u2 t)
  = subst_instance_constr (subst_instance_instance u1 u2) t.
Proof.
  induction t using term_forall_list_ind; cbn; f_equal;
    auto using subst_instance_instance_two.
  - rewrite map_map. now apply All_map_eq.
  - apply subst_instance_univ_two.
  - rewrite map_map. apply All_map_eq.
    eapply All_impl; tea.
    cbn. intros [? ?]; unfold on_snd; cbn; congruence.
  - rewrite map_map. apply All_map_eq.
    eapply All_impl; tea.
    cbn. intros [? ? ?] [? ?]; cbn in *. unfold map_def; cbn; congruence.
  - rewrite map_map. apply All_map_eq.
    eapply All_impl; tea.
    cbn. intros [? ? ?] [? ?]; cbn in *. unfold map_def; cbn; congruence.
Qed.

Lemma subst_instance_context_two u1 u2 Γ :
  subst_instance_context u1 (subst_instance_context u2 Γ)
  = subst_instance_context (subst_instance_instance u1 u2) Γ.
Proof.
  induction Γ; try reflexivity.
  simpl. rewrite IHΓ; f_equal.
  destruct a as [? [] ?]; unfold map_decl; cbn;
    now rewrite !subst_instance_constr_two.
Qed.

Lemma subst_instance_cstr_two u1 u2 c :
  subst_instance_cstr u1 (subst_instance_cstr u2 c)
  = subst_instance_cstr (subst_instance_instance u1 u2) c.
Proof.
  destruct c as [[? ?] ?]; unfold subst_instance_cstr; cbn.
  now rewrite !subst_instance_level_two.
Qed.

Lemma In_subst_instance_cstrs u c ctrs :
  CS.In c (subst_instance_cstrs u ctrs)
  <-> exists c', c = subst_instance_cstr u c' /\ CS.In c' ctrs.
Proof.
  unfold subst_instance_cstrs.
  rewrite CS.fold_spec.
  transitivity (CS.In c CS.empty \/
                exists c', c = subst_instance_cstr u c'
                      /\ In c' (CS.elements ctrs)).
  - generalize (CS.elements ctrs), CS.empty.
    induction l; cbn.
    + firstorder.
    + intros t. etransitivity. eapply IHl. split; intros [HH|HH].
      * destruct a as [[l1 a] l2]. apply CS.add_spec in HH.
        destruct HH as [HH|HH].
        right; eexists. split; [|left; reflexivity]. assumption.
        now left.
      * destruct HH as [c' ?]. right; exists c'; intuition.
      * left. destruct a as [[l1 a] l2]. apply CS.add_spec.
        now right.
      * destruct HH as [c' [HH1 [?|?]]]; subst.
        left; destruct c' as [[l1 c'] l2];
          apply CS.add_spec; now left.
        right; exists c'; intuition.
  - rewrite ConstraintSetFact.empty_iff.
    transitivity (exists c', c = subst_instance_cstr u c'
                        /\ In c' (CS.elements ctrs)).
    intuition.
    apply iff_ex; intro. apply and_iff_compat_l. symmetry.
    etransitivity. eapply CS.elements_spec1.
    etransitivity. eapply SetoidList.InA_alt.
    split; intro; eauto.
    now destruct H as [? [[] ?]].
Qed.

Lemma In_subst_instance_cstrs' u c ctrs :
  CS.In c ctrs ->
  CS.In (subst_instance_cstr u c) (subst_instance_cstrs u ctrs).
Proof.
  intro H. apply In_subst_instance_cstrs. now eexists.
Qed.

Lemma subst_instance_cstrs_two u1 u2 ctrs :
  CS.Equal
    (subst_instance_cstrs u1 (subst_instance_cstrs u2 ctrs))
    (subst_instance_cstrs (subst_instance_instance u1 u2) ctrs).
Proof.
  intro c; split; intro Hc; apply In_subst_instance_cstrs.
  - apply In_subst_instance_cstrs in Hc; destruct Hc as [c' [eq Hc']].
    apply In_subst_instance_cstrs in Hc'; destruct Hc' as [c'' [eq' Hc'']].
    exists c''. subst; now rewrite subst_instance_cstr_two.
  - apply In_subst_instance_cstrs in Hc; destruct Hc as [c' [eq Hc']].
    exists (subst_instance_cstr u2 c'). split.
    now rewrite subst_instance_cstr_two.
    now apply In_subst_instance_cstrs'.
Qed.


Lemma consistent_instance_no_prop lvs φ uctx u :
  consistent_instance lvs φ uctx u
  -> forallb (fun x => negb (Level.is_prop x)) u.
Proof.
  unfold consistent_instance. destruct uctx as [ctx|ctx|ctx].
  destruct u; [reflexivity|discriminate].
  2: destruct ctx as [ctx ?].
  all: destruct (AUContext.repr ctx); intro H; apply H.
Qed.

Hint Resolve consistent_instance_no_prop : univ_subst.

Lemma consistent_instance_declared lvs φ uctx u :
  consistent_instance lvs φ uctx u
  -> forallb (fun l => LS.mem l lvs) u.
Proof.
  unfold consistent_instance. destruct uctx as [ctx|ctx|ctx].
  destruct u; [reflexivity|discriminate].
  2: destruct ctx as [ctx ?].
  all: destruct (AUContext.repr ctx); intro H; apply H.
Qed.

Lemma monomorphic_level_notin_AUContext s φ :
  ~ LS.In (Level.Level s) (AUContext.levels φ).
Proof.
  destruct φ as [φ1 φ2].
  intro H. apply (proj1 (LevelSetProp.of_list_1 _ _)) in H. cbn in H.
  apply SetoidList.InA_alt in H.
  destruct H as [? [? H]]; subst. revert H.
  unfold mapi; generalize 0.
  induction φ1; cbn. trivial.
  intros n [H|H]. discriminate. eauto.
Qed.

Global Instance satisfies_equal_sets v :
  Morphisms.Proper (Morphisms.respectful CS.Equal iff) (satisfies v).
Proof.
  intros φ1 φ2 H; split; intros HH c Hc; now apply HH, H.
Qed.

Global Instance satisfies_subsets v :
  Morphisms.Proper (Morphisms.respectful CS.Subset (flip impl))
                   (satisfies v).
Proof.
  intros φ1 φ2 H H2 c Hc; now apply H2, H.
Qed.

Hint Resolve subst_instance_cstrs_two
     satisfies_equal_sets satisfies_subsets : univ_subst.


Lemma val0_subst_instance_level u l v
      (Hu : forallb (negb ∘ Level.is_prop) u)
  : val0 v (subst_instance_level u l) = val0 (subst_instance_valuation u v) l.
Proof.
  destruct l; aa; cbn.
  rewrite Znat.Z2Nat.id; auto.
  apply (forallb_nth' n Level.lSet) in Hu.
    destruct Hu as [[?l [HH1 HH2]]|HH1]; rewrite HH1; cbn.
    destruct l; try discriminate; cbn.
    apply Zorder.Zle_0_nat.
    reflexivity.
Qed.

Lemma satisfies0_subst_instance_ctr u v c
      (Hu : forallb (negb ∘ Level.is_prop) u)
  : satisfies0 v (subst_instance_cstr u c)
    <-> satisfies0 (subst_instance_valuation u v) c.
Proof.
  destruct c as [[l1 []] l2]; unfold subst_instance_cstr; cbn;
    split; intro H; constructor; inv H.
  all: rewrite <- ?val0_subst_instance_level; tea.
  all: rewrite ?val0_subst_instance_level; tea.
Qed.

Lemma satisfies_subst_instance_ctr u v ctrs
      (Hu : forallb (negb ∘ Level.is_prop) u)
  : satisfies v (subst_instance_cstrs u ctrs)
    <-> satisfies (subst_instance_valuation u v) ctrs.
Proof.
  split; intros Hv c Hc.
  - apply satisfies0_subst_instance_ctr; tas. apply Hv.
    apply In_subst_instance_cstrs. exists c; now split.
  - apply In_subst_instance_cstrs in Hc.
    destruct Hc as [c' [? Hc']]; subst.
    apply satisfies0_subst_instance_ctr; auto.
Qed.

(** global constraints are monomorphic *)

Lemma not_var_global_levels Σ (hΣ : wf Σ) :
  LS.For_all (negb ∘ Level.is_var) (global_levels Σ).
Proof.
  induction hΣ as [|Σ d hΣ IH HH univs Hu Hd].
  - intros l Hl. apply LevelSet_pair_In in Hl.
    destruct Hl as [Hl|Hl]; subst; reflexivity.
  - subst univs. intros l Hl. simpl in Hl; apply LS.union_spec in Hl.
    destruct Hl as [Hl|Hl]; auto. clear -Hu Hl.
    destruct d as [? [? ? [φ|?|?]]|? [? ? ? ? [φ|?|?]]]; cbn in *;
      unfold monomorphic_levels_decl in *; cbn in *;
      try now apply LS.empty_spec in Hl.
    all: destruct Hu as [_ [_ [Hu _]]];
      apply LevelSetFact.for_all_2 in Hu; auto.
    all: now intros x y [].
Qed.

Definition wf_ext_wk (Σ : global_env_ext)
  := wf Σ.1 × on_udecl_prop Σ.1 Σ.2.


Lemma not_var_global_ext_levels Σ φ (hΣ : wf_ext_wk (Σ, Monomorphic_ctx φ)) :
  LS.For_all (negb ∘ Level.is_var)
                   (global_ext_levels (Σ, Monomorphic_ctx φ)).
Proof.
  destruct hΣ as [hΣ Hφ].
  intros l Hl; apply LS.union_spec in Hl; destruct Hl as [Hl|Hl].
  - destruct Hφ as [_ [Hφ _]]. apply LevelSetFact.for_all_2 in Hφ; auto.
    now intros x y [].
  - eapply not_var_global_levels; eassumption.
Qed.

Lemma levels_global_constraint Σ (hΣ : wf Σ) c :
  CS.In c (global_constraints Σ)
  -> LS.In c.1.1 (global_levels Σ)
    /\ LS.In c.2 (global_levels Σ).
Proof.
  induction hΣ as [|Σ d hΣ IH HH univs Hu Hd].
  - intro H; now apply CS.empty_spec in H.
  - subst univs. intro Hc. simpl in *; apply CS.union_spec in Hc.
    destruct Hc as [Hc|Hc]; auto. clear -Hu Hc.
    + destruct d as [? [? ? [φ|?|?]]|? [? ? ? ? [φ|?|?]]]; cbn in *;
        unfold monomorphic_levels_decl, monomorphic_constraints_decl in *; cbn in *;
          try now apply CS.empty_spec in Hc.
      all: destruct Hu as [_ [Hu [_ _]]].
      all: destruct c as [[l1 c] l2]; exact (Hu _ Hc).
    + split; apply LS.union_spec; now right.

Qed.

Lemma levels_global_ext_constraint Σ φ (hΣ : wf_ext_wk (Σ, φ)) c :
  CS.In c (global_ext_constraints (Σ, φ))
  -> LS.In c.1.1 (global_ext_levels (Σ, φ))
    /\ LS.In c.2 (global_ext_levels (Σ, φ)).
Proof.
  intro H. apply CS.union_spec in H; simpl in H.
  destruct hΣ as [hΣ Hφ], H as [Hc|H]; simpl in *.
  - destruct Hφ as [Hφ _]. unfold global_ext_levels. simpl.
    destruct c as [[l1 c] l2]; exact  (Hφ _ Hc).
  - apply levels_global_constraint in H; tas.
    split; apply LS.union_spec; right; apply H.
Qed.

Definition is_monomorphic_cstr (c : univ_constraint)
  := negb (Level.is_var c.1.1) && negb (Level.is_var c.2).

Lemma monomorphic_global_constraint Σ (hΣ : wf Σ) c :
  CS.In c (global_constraints Σ)
  -> is_monomorphic_cstr c.
Proof.
  intros H. apply levels_global_constraint in H; tas.
  apply andb_and. split; destruct H as [H1 H2].
  now apply not_var_global_levels in H1.
  now apply not_var_global_levels in H2.
Qed.

Lemma monomorphic_global_constraint_ext Σ φ
      (hΣ : wf_ext_wk (Σ, Monomorphic_ctx φ)) c :
  CS.In c (global_ext_constraints (Σ, Monomorphic_ctx φ))
  -> is_monomorphic_cstr c.
Proof.
  intros H. apply levels_global_ext_constraint in H; tas.
  apply andb_and. split; destruct H as [H1 H2].
  now apply not_var_global_ext_levels in H1.
  now apply not_var_global_ext_levels in H2.
Qed.

Hint Resolve monomorphic_global_constraint monomorphic_global_constraint_ext
  : univ_subst.

Lemma subst_instance_monom_cstr inst c :
  is_monomorphic_cstr c
  -> subst_instance_cstr inst c = c.
Proof.
  intro H; apply andb_and in H. destruct H.
  destruct c as [[[] ?] []]; cbnr; discriminate.
Qed.

Lemma satisfies_union v φ1 φ2 :
  satisfies v (CS.union φ1 φ2)
  <-> (satisfies v φ1 /\ satisfies v φ2).
Proof.
  unfold satisfies. split.
  - intros H; split; intros c Hc; apply H; now apply CS.union_spec.
  - intros [H1 H2] c Hc; apply CS.union_spec in Hc; destruct Hc; auto.
Qed.

Lemma equal_subst_instance_cstrs_mono u cstrs :
  CS.For_all is_monomorphic_cstr cstrs ->
  CS.Equal (subst_instance_cstrs u cstrs) cstrs.
Proof.
  intros HH c. etransitivity.
  eapply In_subst_instance_cstrs. split; intro H.
  destruct H as [c' [eq Hc']]. subst; rewrite subst_instance_monom_cstr; aa.
  exists c. rewrite subst_instance_monom_cstr; aa.
Qed.

Lemma subst_instance_cstrs_union u φ φ' :
  CS.Equal (subst_instance_cstrs u (CS.union φ φ'))
           (CS.union (subst_instance_cstrs u φ) (subst_instance_cstrs u φ')).
Proof.
  intro c; split; intro Hc.
  - apply In_subst_instance_cstrs in Hc.
    destruct Hc as [c' [eq Hc]]; subst.
    apply* CS.union_spec in Hc.
    destruct Hc; [left|right]; now apply In_subst_instance_cstrs'.
  - apply In_subst_instance_cstrs.
    apply CS.union_spec in Hc.
    destruct Hc as [Hc|Hc]; apply In_subst_instance_cstrs in Hc;
      destruct Hc as [c'[eq Hc]]; exists c'; aa; apply CS.union_spec;
        [left|right]; aa.
Qed.

Hint Unfold CS.For_all : univ_subst.

Definition sub_context_set (φ φ' : ContextSet.t)
  := LS.Subset φ.1 φ'.1 /\ CS.Subset φ.2 φ'.2.

Definition global_ext_context_set Σ : ContextSet.t
  := (global_ext_levels Σ, global_ext_constraints Σ).

Global Instance sub_context_set_trans : RelationClasses.Transitive sub_context_set.
Proof.
  split; (etransitivity; [eapply H | eapply H0]).
Qed.


Lemma consistent_ext_trans_polymorphic_case_aux {Σ φ1 φ2 φ' udecl inst inst'} :
  wf_ext_wk (Σ, Polymorphic_ctx (φ1, φ2)) ->
  valid_constraints0 (global_ext_constraints (Σ, Polymorphic_ctx (φ1, φ2)))
                     (subst_instance_cstrs inst udecl) ->
  valid_constraints0 (global_ext_constraints (Σ, φ'))
                     (subst_instance_cstrs inst' φ2) ->
  forallb (fun x : Level.t => negb (Level.is_prop x)) inst' ->
  valid_constraints0 (global_ext_constraints (Σ, φ'))
                     (subst_instance_cstrs
                        (subst_instance_instance inst' inst) udecl).
Proof.
  intros [HΣ Hφ] H3 H2 H2'.
  intros v Hv. rewrite <- subst_instance_cstrs_two.
  apply satisfies_subst_instance_ctr; tas. apply H3.
  apply satisfies_union; simpl. split.
  - apply satisfies_subst_instance_ctr; auto.
  - apply satisfies_subst_instance_ctr; tas.
    rewrite equal_subst_instance_cstrs_mono; aa.
    apply satisfies_union in Hv; apply Hv.
Qed.

Lemma consistent_ext_trans_polymorphic_cases Σ φ φ' udecl inst inst' :
  wf_ext_wk (Σ, φ) ->
  sub_context_set (monomorphic_udecl φ) (global_ext_context_set (Σ, φ')) ->
  consistent_instance_ext (Σ, φ) (Polymorphic_ctx udecl) inst ->
  consistent_instance_ext (Σ, φ') φ inst' ->
  consistent_instance_ext (Σ, φ') (Polymorphic_ctx udecl)
                          (subst_instance_instance inst' inst).
Proof.
  intros HΣφ Hφ [H [H0 [H1 H3]]] H2.
  apply consistent_instance_no_prop in H2 as H2'.
  repeat split.
  3: now rewrite subst_instance_instance_length.
  + clear -H H2'.
    assert (HH: forall l, negb (Level.is_prop l) ->
                     negb (Level.is_prop (subst_instance_level inst' l))). {
      destruct l; cbnr; aa.
      eapply (forallb_nth' n Level.lSet) in H2'.
      destruct H2' as [[? [H2 ?]]|H2]; rewrite H2; auto. }
    induction inst; cbnr. rewrite HH; cbn. apply IHinst.
    all: apply andP in H; try apply H.
  + rewrite forallb_map. apply forallb_forall.
    intros l Hl. unfold global_ext_levels, compose in *; simpl in *.
    eapply forallb_forall in H0; tea. clear -Hφ H0 H2 Hl.
    apply LevelSet_mem_union in H0. destruct H0 as [H|H].
    2: { destruct l; simpl; try (apply LevelSet_mem_union; right; assumption).
         apply consistent_instance_declared in H2.
         apply (forallb_nth' n Level.lSet) in H2.
         destruct H2 as [[? [H2 ?]]|H2]; rewrite H2; tas.
         apply LevelSet_mem_union; right.
         apply global_levels_Set. }
    *  destruct l; simpl.
       -- apply LevelSet_mem_union; right; apply global_levels_Prop.
       -- apply LevelSet_mem_union; right; apply global_levels_Set.
       -- apply LS.mem_spec in H.
          destruct φ as [φ|[φ1 φ2]|[[φ1 φ2] φ3]]; simpl in *.
          apply Hφ in H. now apply LS.mem_spec.
          all: now apply monomorphic_level_notin_AUContext in H.
       -- apply consistent_instance_declared in H2.
          apply (forallb_nth' n Level.lSet) in H2.
          destruct H2 as [[? [H2 ?]]|H2]; rewrite H2; tas.
          apply LevelSet_mem_union; right; apply global_levels_Set.
  + unfold consistent_instance_ext, consistent_instance in H2.
    unfold valid_constraints in *; destruct check_univs; [|trivial].
    destruct φ as [φ|[φ1 φ2]|[[φ1 φ2] φ3]]; simpl in *.
    * intros v Hv. rewrite <- subst_instance_cstrs_two.
      apply satisfies_subst_instance_ctr; tas.
      apply H3. apply satisfies_subst_instance_ctr; tas.
      rewrite equal_subst_instance_cstrs_mono; aa.
      apply satisfies_union; simpl; split.
      -- intros c Hc. now apply Hv, Hφ.
      -- apply satisfies_union in Hv; apply Hv.
    * destruct H2 as [_ [_ [_ H2]]].
      eapply consistent_ext_trans_polymorphic_case_aux; try eassumption.
    * destruct H2 as [_ [_ [_ H2]]].
      eapply (consistent_ext_trans_polymorphic_case_aux HΣφ); eassumption.
Qed.

Lemma consistent_ext_trans Σ φ φ' udecl inst inst' :
  wf_ext_wk (Σ, φ) ->
  sub_context_set (monomorphic_udecl φ) (global_ext_context_set (Σ, φ')) ->
  consistent_instance_ext (Σ, φ) udecl inst ->
  consistent_instance_ext (Σ, φ') φ inst' ->
  consistent_instance_ext (Σ, φ') udecl (subst_instance_instance inst' inst).
Proof.
  intros HΣφ Hφ H1 H2. destruct udecl as [?|udecl|[udecl ?]].
  - (* udecl monomorphic *)
    cbn; now rewrite subst_instance_instance_length.
  - (* udecl polymorphic *)
    eapply consistent_ext_trans_polymorphic_cases; eassumption.
  - (* udecl cumulative *)
    eapply consistent_ext_trans_polymorphic_cases; eassumption.
Qed.

Hint Resolve consistent_ext_trans : univ_subst.


Lemma consistent_instance_valid_constraints Σ φ u univs :
  wf_ext_wk (Σ, φ) ->
  CS.Subset (monomorphic_constraints φ)
                       (global_ext_constraints (Σ, univs)) ->
  consistent_instance_ext (Σ, univs) φ u ->
  valid_constraints (global_ext_constraints (Σ, univs))
                    (subst_instance_cstrs u (global_ext_constraints (Σ, φ))).
Proof.
  intros HΣ Hsub HH.
  apply consistent_instance_no_prop in HH as Hu.
  unfold valid_constraints; case_eq check_univs; [intro Hcf|trivial].
  intros v Hv. apply satisfies_subst_instance_ctr; tas.
  apply satisfies_union; simpl; split.
  - destruct φ as [φ|[φ1 φ2]|[[φ1 φ2] ?]].
    + cbn. apply satisfies_subst_instance_ctr; tas.
      rewrite equal_subst_instance_cstrs_mono; aa.
      rewrite <- Hsub in Hv; assumption.
      intros c Hc; eapply monomorphic_global_constraint_ext; tea.
      apply CS.union_spec; now left.
    + destruct HH as [_ [_ [_ H1]]].
      unfold valid_constraints in H1; rewrite Hcf in H1.
      apply satisfies_subst_instance_ctr; aa.
    + destruct HH as [_ [_ [_ H1]]].
      unfold valid_constraints in H1; rewrite Hcf in H1.
      apply satisfies_subst_instance_ctr; aa.
  - apply satisfies_subst_instance_ctr; tas.
    apply satisfies_union in Hv. destruct HΣ.
    rewrite equal_subst_instance_cstrs_mono; aa.
Qed.

Hint Resolve consistent_instance_valid_constraints : univ_subst.

Class SubstUnivPreserved {A} `{UnivSubst A} (R : constraints -> crelation A)
  := Build_SubstUnivPreserved :
       forall φ φ' (u : universe_instance),
         forallb (fun x => negb (Level.is_prop x)) u ->
         valid_constraints φ' (subst_instance_cstrs u φ) ->
         subrelation (R φ)
                     (precompose (R φ') (subst_instance u)).

Lemma satisfies_subst_instance φ φ' u :
  check_univs = true ->
  forallb (fun x => negb (Level.is_prop x)) u ->
  valid_constraints φ' (subst_instance_cstrs u φ) ->
  forall v, satisfies v φ' ->
       satisfies (subst_instance_valuation u v) φ.
Proof.
  intros Hcf Hu HH v Hv.
  unfold valid_constraints in HH; rewrite Hcf in HH.
  apply satisfies_subst_instance_ctr; aa.
Qed.

Global Instance leq_universe_subst_instance : SubstUnivPreserved leq_universe.
Proof.
  intros φ φ' u Hu HH t t' Htt'.
  unfold leq_universe in *; case_eq check_univs;
    [intro Hcf; rewrite Hcf in *|trivial].
  intros v Hv; cbn.
  rewrite !subst_instance_univ_val'; tas.
  apply Htt'. clear t t' Htt'.
  eapply satisfies_subst_instance; tea.
Qed.

Global Instance eq_universe_subst_instance : SubstUnivPreserved eq_universe.
Proof.
  intros φ φ' u Hu HH t t' Htt'.
  unfold eq_universe in *; case_eq check_univs;
    [intro Hcf; rewrite Hcf in *|trivial].
  intros v Hv; cbn.
  rewrite !subst_instance_univ_val'; tas.
  apply Htt'. clear t t' Htt'.
  eapply satisfies_subst_instance; tea.
Qed.

Lemma precompose_subst_instance_instance Rle u i i' :
  precompose (R_universe_instance Rle) (subst_instance_instance u) i i'
  <~> R_universe_instance (precompose Rle (subst_instance_univ u)) i i'.
Proof.
  unfold R_universe_instance, subst_instance_instance.
  replace (map Universe.make (map (subst_instance_level u) i))
    with (map (subst_instance_univ u) (map Universe.make i)).
  replace (map Universe.make (map (subst_instance_level u) i'))
    with (map (subst_instance_univ u) (map Universe.make i')).
  split. apply Forall2_map_inv. apply Forall2_map.
  all: rewrite !map_map; apply map_ext; reflexivity.
Qed.

Definition precompose_subst_instance_instance__1 Rle u i i'
  := equiv _ _ (precompose_subst_instance_instance Rle u i i').

Definition precompose_subst_instance_instance__2 Rle u i i'
  := equiv_inv _ _ (precompose_subst_instance_instance Rle u i i').


Global Instance eq_term_upto_univ_subst_instance
         (Re Rle : constraints -> universe -> universe -> Prop)
      {he: SubstUnivPreserved Re} {hle: SubstUnivPreserved Rle}
  : SubstUnivPreserved (fun φ => eq_term_upto_univ (Re φ) (Rle φ)).
Proof.
  intros φ φ' u Hu HH t t'.
  specialize (he _ _ _ Hu HH).
  specialize (hle _ _ _ Hu HH).
  clear Hu HH.
  induction t in t', Rle, hle |- * using term_forall_list_ind;
    inversion 1; subst; cbn; constructor;
      eauto using precompose_subst_instance_instance__2, R_universe_instance_impl'.
  all: apply All2_map; eapply All2_impl'; tea;
    eapply All_impl; eauto; cbn; intros; aa.
Qed.

Lemma leq_term_subst_instance : SubstUnivPreserved leq_term.
Proof. exact _. Qed.

Lemma eq_term_subst_instance : SubstUnivPreserved eq_term.
Proof. exact _. Qed.





(** Now routine lemmas ... *)

Lemma subst_instance_univ_super l u
      (Hu : forallb (negb ∘ Level.is_prop) u)
  : subst_instance_univ u (Universe.super l)
    = Universe.super (subst_instance_level u l).
Proof.
  destruct l; cbnr. unfold subst_instance_level_expr; cbn.
  destruct (le_lt_dec #|u| n) as [HH|HH].
  + now rewrite nth_overflow.
  + eapply (forallb_nth _ _ _ Level.lSet Hu) in HH.
    destruct HH as [l [HH1 HH2]]. rewrite HH1.
    destruct l; cbn; try reflexivity; discriminate.
Qed.

Lemma subst_instance_univ_make l u :
  subst_instance_univ u (Universe.make l)
  = Universe.make (subst_instance_level u l).
Proof.
  reflexivity.
Qed.


Lemma LevelIn_subst_instance Σ l u univs :
  LS.In l (global_ext_levels Σ) ->
  LS.Subset (monomorphic_levels Σ.2) (global_ext_levels (Σ.1, univs)) ->
  consistent_instance_ext (Σ.1, univs) Σ.2 u ->
  LS.In (subst_instance_level u l) (global_ext_levels (Σ.1, univs)).
Proof.
  intros H H0 H'. destruct l; simpl.
  - apply LS.union_spec; right; simpl.
    apply LS.mem_spec, global_levels_Prop.
  - apply LS.union_spec; right; simpl.
    apply LS.mem_spec, global_levels_Set.
  - apply LS.union_spec in H; destruct H as [H|H]; simpl in *.
    + apply H0. destruct Σ as [? φ]; cbn in *; clear -H.
      destruct φ as [?|?|[? ?]]; tas;
        now apply monomorphic_level_notin_AUContext in H.
    + apply LS.union_spec; now right.
  - apply consistent_instance_declared in H'.
    apply (forallb_nth' n Level.lSet) in H'.
    destruct H' as [[? [eq ?]]|eq]; rewrite eq.
    + now apply LS.mem_spec.
    + apply LS.union_spec; right; simpl.
      apply LS.mem_spec, global_levels_Set.
Qed.


Lemma is_prop_subst_instance_univ u l
      (Hu : forallb (negb ∘ Level.is_prop) u)
  : Universe.is_prop (subst_instance_univ u l) = Universe.is_prop l.
Proof.
  assert (He : forall a, Universe.Expr.is_prop (subst_instance_level_expr u a)
                    = Universe.Expr.is_prop a). {
    intros [[] b]; cbn; try reflexivity.
    destruct (le_lt_dec #|u| n) as [HH|HH].
    + now rewrite nth_overflow.
    + eapply (forallb_nth _ _ _ Level.lSet Hu) in HH.
      destruct HH as [?l [HH1 HH2]]. rewrite HH1. now apply ssrbool.negbTE. }
  induction l. apply He. cbn. f_equal. apply He. apply IHl.
Qed.

Lemma is_small_subst_instance_univ u l
  : Universe.is_small l -> Universe.is_small (subst_instance_univ u l).
Proof.
  assert (He : forall a, Universe.Expr.is_small a ->
             Universe.Expr.is_small (subst_instance_level_expr u a)). {
    intros [[] []]; cbn; auto. }
  induction l. apply He.
  intro HH; cbn in HH; apply andP in HH; destruct HH as [H1 H2].
  cbn. apply andb_and; split. now apply He.
  now apply IHl.
Qed.


Lemma sup_subst_instance_univ u s1 s2 :
  subst_instance_univ u (Universe.sup s1 s2)
  = Universe.sup (subst_instance_univ u s1) (subst_instance_univ u s2).
Proof.
  unfold subst_instance_univ, Universe.sup.
  apply NEL.map_app.
Qed.

Lemma product_subst_instance u s1 s2
      (Hu : forallb (negb ∘ Level.is_prop) u)
 : subst_instance_univ u (Universe.sort_of_product s1 s2)
   = Universe.sort_of_product (subst_instance_univ u s1) (subst_instance_univ u s2).
Proof.
  unfold Universe.sort_of_product.
  rewrite is_prop_subst_instance_univ; tas.
  destruct (Universe.is_prop s2); cbn; try reflexivity.
  apply sup_subst_instance_univ.
Qed.


Lemma iota_red_subst_instance pars c args brs u :
  subst_instance_constr u (iota_red pars c args brs)
  = iota_red pars c (subst_instance u args) (subst_instance u brs).
Proof.
  unfold iota_red. rewrite !subst_instance_constr_mkApps.
  f_equal; simpl; eauto using map_skipn.
  rewrite nth_map; simpl; auto.
Qed.

Lemma fix_subst_subst_instance u mfix :
  map (subst_instance_constr u) (fix_subst mfix)
  = fix_subst (subst_instance u mfix).
Proof.
  unfold fix_subst. rewrite map_length.
  generalize #|mfix|. induction n. reflexivity.
  simpl. rewrite IHn; reflexivity.
Qed.


Lemma cofix_subst_subst_instance u mfix :
  map (subst_instance_constr u) (cofix_subst mfix)
  = cofix_subst (subst_instance u mfix).
Proof.
  unfold cofix_subst. rewrite map_length.
  generalize #|mfix|. induction n. reflexivity.
  simpl. rewrite IHn; reflexivity.
Qed.


Lemma isConstruct_app_subst_instance u t :
  isConstruct_app (subst_instance_constr u t) = isConstruct_app t.
Proof.
  unfold isConstruct_app.
  assert (HH: (decompose_app (subst_instance_constr u t)).1
              = subst_instance_constr u (decompose_app t).1). {
    unfold decompose_app. generalize (@nil term) at 1. generalize (@nil term).
    induction t; cbn; try reflexivity.
    intros l l'. erewrite IHt1; reflexivity. }
  rewrite HH. destruct (decompose_app t).1; reflexivity.
Qed.

Lemma fix_context_subst_instance u mfix :
  subst_instance_context u (fix_context mfix)
  = fix_context (subst_instance u mfix).
Proof.
  unfold subst_instance_context, map_context, fix_context.
  rewrite map_rev. f_equal.
  rewrite map_mapi, mapi_map. eapply mapi_ext.
  intros n x. unfold map_decl, vass; cbn. f_equal.
  symmetry; apply lift_subst_instance_constr.
Qed.

Lemma subst_instance_context_app u L1 L2 :
  subst_instance_context u (L1,,,L2)
  = subst_instance_context u L1 ,,, subst_instance_context u L2.
Proof.
  unfold subst_instance_context, map_context; now rewrite map_app.
Qed.

Lemma red1_subst_instance Σ Γ u s t :
  red1 Σ Γ s t ->
  red1 Σ (subst_instance_context u Γ)
       (subst_instance_constr u s) (subst_instance_constr u t).
Proof.
  intros X0. pose proof I as X.
  intros. induction X0 using red1_ind_all.
  all: try (cbn; econstructor; eauto; fail).
  - cbn. rewrite <- subst_subst_instance_constr. econstructor.
  - cbn. rewrite <- subst_subst_instance_constr. econstructor.
  - cbn. rewrite <- lift_subst_instance_constr. econstructor.
    unfold subst_instance_context.
    unfold option_map in *. destruct (nth_error Γ) eqn:E; inversion H.
    unfold map_context. rewrite nth_error_map, E. cbn.
    rewrite map_decl_body. destruct c. cbn in H1. subst.
    reflexivity.
  - cbn. rewrite subst_instance_constr_mkApps. cbn.
    rewrite iota_red_subst_instance. econstructor.
  - cbn. rewrite !subst_instance_constr_mkApps. cbn.
    econstructor.
    + unfold unfold_fix in *. destruct (nth_error mfix idx) eqn:E.
      * destruct (isLambda (dbody d)) eqn:E2; inversion H.
        rewrite nth_error_map, E. cbn.
        destruct d. cbn in *. destruct dbody; cbn in *; try congruence.
        repeat f_equal.
        all: rewrite <- subst_subst_instance_constr;
          rewrite fix_subst_subst_instance; reflexivity.
      * inversion H.
    + unfold is_constructor in *.
      destruct (nth_error args narg) eqn:E; inversion H0; clear H0.
      rewrite nth_error_map, E. cbn.
      eapply isConstruct_app_subst_instance.
  - cbn. rewrite !subst_instance_constr_mkApps.
    unfold unfold_cofix in *. destruct (nth_error mfix idx) eqn:E.
    inversion H.
    econstructor. fold subst_instance_constr.
    unfold unfold_cofix.
    rewrite nth_error_map, E. cbn.
    rewrite <- subst_subst_instance_constr.
    now rewrite cofix_subst_subst_instance.
    econstructor. fold subst_instance_constr.
    inversion H.
  - cbn. unfold unfold_cofix in *.
    destruct nth_error eqn:E; inversion H.
    rewrite !subst_instance_constr_mkApps.
    econstructor. fold subst_instance_constr.
    unfold unfold_cofix.
    rewrite nth_error_map. destruct nth_error; cbn.
    rewrite <- subst_subst_instance_constr, cofix_subst_subst_instance.
    all: now inversion E.
  - cbn. rewrite subst_instance_constr_two. econstructor; eauto.
  - cbn. rewrite !subst_instance_constr_mkApps.
    econstructor. now rewrite nth_error_map, H.
  - cbn. econstructor; eauto.
    eapply OnOne2_map. eapply OnOne2_impl. eassumption.
    firstorder.
  - cbn; econstructor;
    eapply OnOne2_map; eapply OnOne2_impl; [ eassumption | firstorder].
  - cbn; econstructor;
      eapply OnOne2_map; eapply OnOne2_impl; [ eassumption | ].
    intros. destruct X1. destruct p. inversion e. destruct x, y; cbn in *; subst.
    red. split; cbn; eauto.
  - cbn. eapply fix_red_body.
      eapply OnOne2_map; eapply OnOne2_impl; [ eassumption | ].
    intros. destruct X1. destruct p. inversion e. destruct x, y; cbn in *; subst.
    red. split; cbn; eauto.
    rewrite <- (fix_context_subst_instance u mfix0).
    unfold subst_instance_context, map_context in *. rewrite map_app in *.
    eassumption.
  - cbn; econstructor;
      eapply OnOne2_map; eapply OnOne2_impl; [ eassumption | ].
    intros. destruct X1. destruct p. inversion e. destruct x, y; cbn in *; subst.
    red. split; cbn; eauto.
  - cbn. eapply cofix_red_body.
      eapply OnOne2_map; eapply OnOne2_impl; [ eassumption | ].
    intros. destruct X1. destruct p. inversion e. destruct x, y; cbn in *; subst.
    red. split; cbn; eauto.
    rewrite <- (fix_context_subst_instance u mfix0).
    unfold subst_instance_context, map_context in *. rewrite map_app in *.
    eassumption.
    Grab Existential Variables. all:repeat econstructor.
Qed.



Lemma cumul_subst_instance (Σ : global_env_ext) Γ u A B univs :
  forallb (fun x => negb (Level.is_prop x)) u ->
  valid_constraints (global_ext_constraints (Σ.1, univs))
                    (subst_instance_cstrs u Σ) ->
  Σ ;;; Γ |- A <= B ->
  (Σ.1,univs) ;;; subst_instance_context u Γ
                   |- subst_instance_constr u A <= subst_instance_constr u B.
Proof.
  intros Hu HH X0. induction X0.
  - econstructor.
    eapply leq_term_subst_instance; tea.
  - econstructor 2. eapply red1_subst_instance; cbn; eauto. eauto.
  - econstructor 3. eauto. eapply red1_subst_instance; cbn; eauto.
Qed.

Global Instance eq_decl_subst_instance : SubstUnivPreserved eq_decl.
Proof.
  intros φ1 φ2 u Hu HH [? [?|] ?] [? [?|] ?] [H1 H2]; split; cbn in *; auto.
  all: eapply eq_term_subst_instance; tea.
Qed.

Global Instance eq_context_subst_instance : SubstUnivPreserved eq_context.
Proof.
  intros φ φ' u Hu HH Γ Γ' X. eapply All2_map, All2_impl; tea.
  eapply eq_decl_subst_instance; eassumption.
Qed.

Lemma subst_instance_destArity Γ A u :
  destArity (subst_instance_context u Γ) (subst_instance_constr u A)
  = match destArity Γ A with
    | Some (ctx, s) => Some (subst_instance_context u ctx, subst_instance_univ u s)
    | None => None
    end.
Proof.
  induction A in Γ |- *; simpl; try reflexivity.
  - change (subst_instance_context u Γ,, vass na (subst_instance_constr u A1))
      with (subst_instance_context u (Γ ,, vass na A1)).
    now rewrite IHA2.
  - change (subst_instance_context u Γ ,,
               vdef na (subst_instance_constr u A1) (subst_instance_constr u A2))
      with (subst_instance_context u (Γ ,, vdef na A1 A2)).
    now rewrite IHA3.
Qed.


(* todo move *)
Lemma option_map_two {A B C} (f : A -> B) (g : B -> C) x
  : option_map g (option_map f x) = option_map (g ∘ f) x.
Proof.
  destruct x; reflexivity.
Qed.

Lemma option_map_ext {A B} (f g : A -> B) (H : forall x, f x = g x)
  : forall z, option_map f z = option_map g z.
Proof.
  intros []; cbn; congruence.
Qed.


Lemma subst_instance_instantiate_params_subst u0 params pars s ty :
  option_map (on_pair (map (subst_instance_constr u0)) (subst_instance_constr u0))
             (instantiate_params_subst params pars s ty)
  = instantiate_params_subst (subst_instance_context u0 params)
                             (map (subst_instance_constr u0) pars)
                             (map (subst_instance_constr u0) s)
                             (subst_instance_constr u0 ty).
Proof.
  induction params in pars, s, ty |- *; cbn.
  - destruct pars; cbnr.
  - destruct ?; cbnr; destruct ?; cbnr.
    + rewrite IHparams; cbn. repeat f_equal.
      symmetry; apply subst_subst_instance_constr.
    + destruct ?; cbnr. now rewrite IHparams.
Qed.

Lemma subst_instance_instantiate_params u0 params pars ty :
  option_map (subst_instance_constr u0)
             (instantiate_params params pars ty)
  = instantiate_params (subst_instance_context u0 params)
                       (map (subst_instance_constr u0) pars)
                       (subst_instance_constr u0 ty).
Proof.
  unfold instantiate_params.
  change (@nil term) with (map (subst_instance_constr u0) []) at 2.
  rewrite rev_subst_instance_context.
  rewrite <- subst_instance_instantiate_params_subst.
  destruct ?; cbnr. destruct p; cbn.
  now rewrite subst_subst_instance_constr.
Qed.

Lemma subst_instance_inds u0 ind u bodies :
  subst_instance u0 (inds ind u bodies)
  = inds ind (subst_instance u0 u) bodies.
Proof.
  unfold inds.
  induction #|bodies|; cbnr.
  f_equal. apply IHn.
Qed.


Lemma subst_instance_decompose_prod_assum u Γ t :
  subst_instance u (decompose_prod_assum Γ t)
  = decompose_prod_assum (subst_instance_context u Γ) (subst_instance_constr u t).
Proof.
  induction t in Γ |- *; cbnr.
  apply IHt2. apply IHt3.
Qed.

Lemma subst_instance_decompose_app_rec u Γ t
  : subst_instance u (decompose_app_rec t Γ)
    = decompose_app_rec (subst_instance u t) (subst_instance u Γ).
Proof.
  induction t in Γ |- *; cbnr.
  now rewrite IHt1.
Qed.

Lemma subst_instance_to_extended_list u l
  : map (subst_instance_constr u) (to_extended_list l)
    = to_extended_list (subst_instance_context u l).
Proof.
  - unfold to_extended_list, to_extended_list_k.
    change [] with (map (subst_instance_constr u) []) at 2.
    generalize (@nil term), 0. induction l as [|[aa [ab|] ac] bb].
    + reflexivity.
    + intros l n; cbn. now rewrite IHbb.
    + intros l n; cbn. now rewrite IHbb.
Qed.

Lemma subst_instance_build_branches_type u0 ind mdecl idecl pars u p :
  map (option_map (on_snd (subst_instance_constr u0)))
      (build_branches_type ind mdecl idecl pars u p)
  = build_branches_type ind mdecl idecl (map (subst_instance_constr u0) pars)
                        (subst_instance_instance u0 u) (subst_instance_constr u0 p).
Proof.
  rewrite !build_branches_type_. rewrite map_mapi.
  eapply mapi_ext.
  intros n [[id t] k]; cbn.
  rewrite <- subst_instance_context_two.
  rewrite <- subst_instance_constr_two.
  rewrite <- subst_instance_inds.
  rewrite subst_subst_instance_constr.
  rewrite <- subst_instance_instantiate_params.
  rewrite !option_map_two. apply option_map_ext.
  intros x. rewrite <- (subst_instance_decompose_prod_assum u0 [] x).
  destruct (decompose_prod_assum [] x). simpl.
  unfold decompose_app; rewrite <- (subst_instance_decompose_app_rec u0 [] t0).
  destruct (decompose_app_rec t0 []); cbn.
  unfold subst_instance, subst_instance_list.
  case_eq (chop (ind_npars mdecl) l); intros l0 l1 H.
  eapply chop_map in H; rewrite H; clear H.
  unfold on_snd; cbn. f_equal.
  rewrite subst_instance_constr_it_mkProd_or_LetIn. f_equal.
  rewrite subst_instance_constr_mkApps; f_equal.
  - rewrite subst_instance_context_length.
    symmetry; apply lift_subst_instance_constr.
  - rewrite map_app; f_equal; cbn.
    rewrite subst_instance_constr_mkApps, map_app; cbn; repeat f_equal.
    apply subst_instance_to_extended_list.
Qed.


Axiom fix_guard_subst_instance :
  forall mfix u,
    fix_guard mfix ->
    fix_guard (map (map_def (subst_instance_constr u) (subst_instance_constr u))
                   mfix).


Lemma All_local_env_over_subst_instance Σ Γ (wfΓ : wf_local Σ Γ) :
  All_local_env_over typing
                     (fun Σ0 Γ0 (_ : wf_local Σ0 Γ0) t T (_ : Σ0;;; Γ0 |- t : T) =>
       forall u univs, wf_ext_wk Σ0 ->
                  sub_context_set (monomorphic_udecl Σ0.2)
                                  (global_ext_context_set (Σ0.1, univs)) ->
                  consistent_instance_ext (Σ0.1, univs) Σ0.2 u ->
                  (Σ0.1, univs) ;;; subst_instance_context u Γ0
                  |- subst_instance_constr u t : subst_instance_constr u T)
                     Σ Γ wfΓ ->
  forall u univs,
    wf_ext_wk Σ ->
    sub_context_set (monomorphic_udecl Σ.2)
                    (global_ext_context_set (Σ.1, univs)) ->
    consistent_instance_ext (Σ.1, univs) Σ.2 u ->
    wf_local (Σ.1, univs) (subst_instance_context u Γ).
Proof.
  induction 1; simpl; constructor; cbn in *; auto.
  all: destruct tu; eexists; cbn in *; eauto.
Qed.

Hint Resolve All_local_env_over_subst_instance : univ_subst.

Lemma typing_subst_instance :
  env_prop (fun Σ Γ t T => forall u univs,
                wf_ext_wk Σ ->
                sub_context_set (monomorphic_udecl Σ.2)
                                (global_ext_context_set (Σ.1, univs)) ->
                consistent_instance_ext (Σ.1, univs) Σ.2 u ->
                (Σ.1,univs) ;;; subst_instance_context u Γ
                |- subst_instance_constr u t : subst_instance_constr u T).
Proof.
  apply typing_ind_env; intros Σ wfΣ Γ wfΓ; cbn  -[Universe.make] in *.
  - intros n decl eq X u univs wfΣ' H Hsub. rewrite <- lift_subst_instance_constr.
    rewrite map_decl_type. econstructor; aa.
    unfold subst_instance_context, map_context.
    now rewrite nth_error_map, eq.
  - intros l X Hl u univs wfΣ' HSub H.
    rewrite subst_instance_univ_super, subst_instance_univ_make.
    econstructor. aa. destruct HSub. eapply LevelIn_subst_instance; eauto.
    eapply consistent_instance_no_prop; eassumption.
  - intros n t0 b s1 s2 X X0 X1 X2 X3 u univs wfΣ' HSub H.
    rewrite product_subst_instance; aa. econstructor.
    eapply X1; eauto.
    eapply X3; eauto.
  - intros n t0 b s1 bty X X0 X1 X2 X3 u univs wfΣ' HSub H.
    econstructor. eapply X1; aa. eapply X3; aa.
  - intros n b b_ty b' s1 b'_ty X X0 X1 X2 X3 X4 X5 u univs wfΣ' HSub H.
    econstructor; eauto. eapply X5; aa.
  - intros t0 na A B u X X0 X1 X2 X3 u0 univs wfΣ' HSub H.
    rewrite <- subst_subst_instance_constr. cbn. econstructor.
    + eapply X1; eauto.
    + eapply X3; eauto.
  - intros. rewrite subst_instance_constr_two. econstructor; [aa|aa|].
    clear X X0; cbn in *.
    eapply consistent_ext_trans; eauto.
  - intros. rewrite subst_instance_constr_two. econstructor; [aa|aa|].
    clear X X0; cbn in *.
    eapply consistent_ext_trans; eauto.
  - intros. eapply meta_conv. econstructor; aa. clear.
    unfold type_of_constructor; cbn.
    rewrite <- subst_subst_instance_constr. f_equal.
    + unfold inds. induction #|ind_bodies mdecl|. reflexivity.
      cbn. now rewrite IHn.
    + symmetry; apply subst_instance_constr_two.

  - intros ind u npar p c brs args mdecl idecl isdecl X X0 H pty X1 indctx pctx ps
           btys H0 X2 H1 X3 X4 X5 X6 u0 univs wfΣ' HSub H2.
    rewrite subst_instance_constr_mkApps in *.
    rewrite map_app. cbn. rewrite map_skipn.
    eapply type_Case with (u1:=subst_instance_instance u0 u)
                          (indctx0:=subst_instance_context u0 indctx)
                          (ps0 :=subst_instance_univ u0 ps)
                          (pctx0:=subst_instance_context u0 pctx)
                          (btys0:=map (on_snd (subst_instance_constr u0)) btys);
      eauto.
    + clear -H0 H2. rewrite firstn_map.
      apply* types_of_case_spec in H0. destruct H0 as [s' [E1 [E2 E3]]].
      eexists. repeat split.
      2: now rewrite (subst_instance_destArity []), E2.
      * rewrite <- subst_instance_constr_two, <- subst_instance_context_two.
        set (param' := subst_instance_context u (ind_params mdecl)) in *.
        set (type' := subst_instance_constr u (ind_type idecl)) in *.
        rewrite <- subst_instance_instantiate_params.
        destruct (instantiate_params param' (firstn npar args) type');
          [|discriminate].
        cbn in *. apply some_inj in E1.
        rewrite (subst_instance_destArity []), E1; reflexivity.
      * rewrite <- subst_instance_build_branches_type.
        now rewrite map_option_out_map_option_map, E3.
    + clear -X2 X HSub wfΣ' H2. destruct HSub as [_ HSub]; cbn in *.
      eapply consistent_instance_valid_constraints in H2 as H2'; aa; simpl in *.
      eapply eq_context_subst_instance in X2; aa.
      refine (transport (fun c => eq_context _ c _) _ X2). clear.
      cbn. f_equal. unfold map_decl; cbn. f_equal.
      rewrite subst_instance_constr_mkApps. f_equal.
      rewrite !map_app. f_equal.
      * rewrite firstn_map, !map_map. eapply map_ext.
        rewrite subst_instance_context_length.
        intro; symmetry; apply lift_subst_instance_constr.
      * apply subst_instance_to_extended_list.
    + clear -H1 H2.
      induction (ind_kelim idecl) as [|a l]; try discriminate; cbn in *.
      apply* orb_true_iff in H1.
      destruct H1 as [H1|H1]; [left|right; now eapply IHl].
      clear IHl. unfold universe_family in *.
      rewrite is_prop_subst_instance_univ; [|aa].
      destruct (Universe.is_prop ps); cbnr.
      case_eq (Universe.is_small ps); intro HH; rewrite HH in H1.
      ++ apply (is_small_subst_instance_univ u0) in HH.
         now rewrite HH.
      ++ destruct a; inv H1.
         destruct ?; constructor.
    + apply X5 in H2; tea.
      rewrite subst_instance_constr_mkApps in H2; eassumption.
    + eapply All2_map with (f := (on_snd (subst_instance_constr u0)))
                           (g:= (on_snd (subst_instance_constr u0))).
      eapply All2_impl. eassumption. intros.
      simpl in X7. destruct X7 as [[[? ?] ?] ?]. intuition eauto.
      cbn. eauto. cbn.
      destruct x, y; cbn in *; subst.
      eapply t1; assumption.

  - intros p c u mdecl idecl pdecl isdecl args X X0 X1 X2 H u0 univs wfΣ' HSub H0.
    rewrite <- subst_subst_instance_constr. cbn.
    rewrite !subst_instance_constr_two.
    rewrite map_rev. econstructor; eauto. 2:now rewrite map_length.
    eapply X2 in H0; tas. rewrite subst_instance_constr_mkApps in H0.
    eassumption.

  - intros mfix n decl H H0 X X0 u univs wfΣ' HSub H1.
    erewrite map_dtype. econstructor.
    + now apply fix_guard_subst_instance.
    + rewrite nth_error_map, H. reflexivity.
    + rewrite <- (fix_context_subst_instance u mfix).
      refine (subst_instance_context_app u Γ (fix_context mfix) # _).
      destruct mfix; [cbn in; rewrite nth_error_nil in H; discriminate|].
      inv X0. eapply typing_wf_local. eapply X1; eassumption.
    + eapply All_map, All_impl; tea.
      intros x [[X1 X2] X3]. split.
      * specialize (X3 u univs wfΣ' HSub H1). erewrite map_dbody in X3.
        rewrite <- lift_subst_instance_constr in X3.
        rewrite fix_context_length, map_length in *.
        erewrite map_dtype with (d := x) in X3.
        unfold subst_instance_context, map_context in *.
        rewrite map_app in *.
        rewrite <- (fix_context_subst_instance u mfix).
        eapply X3.
      * destruct x as [? ? []]; cbn in *; tea.

  - intros mfix n decl H X X0 H0 u univs wfΣ' HSub H1.
    erewrite map_dtype. econstructor; tas.
    + rewrite nth_error_map, H. reflexivity.
    + rewrite <- (fix_context_subst_instance u mfix).
      refine (subst_instance_context_app u Γ (fix_context mfix) # _).
      destruct mfix; [cbn in; rewrite nth_error_nil in H; discriminate|].
      inv X0. eapply typing_wf_local. eapply X1; eassumption.
    + eapply All_map, All_impl; tea.
      intros x [X1 X3].
      * specialize (X3 u univs wfΣ' HSub H1). erewrite map_dbody in X3.
        rewrite <- lift_subst_instance_constr in X3.
        rewrite fix_context_length, map_length in *.
        unfold subst_instance_context, map_context in *.
        rewrite map_app in *.
        unfold compose.
        rewrite <- (fix_context_subst_instance u mfix).
        rewrite <- map_dtype. eapply X3.

  - intros t0 A B X X0 X1 X2 X3 u univs wfΣ' HSub H.
    econstructor. eapply X1; aa.
    + destruct X2; [left|right].
      * clear -i H wfΣ' HSub. destruct i as [[ctx [s [H1 H2]]] HH]; cbn in HH.
        exists (subst_instance_context u ctx), (subst_instance_univ u s). split.
        now rewrite (subst_instance_destArity []), H1.
        rewrite <- subst_instance_context_app. unfold app_context in *.
        revert H2 HH. generalize (ctx ++ Γ).
        induction 1; simpl; constructor; auto; cbn in *.
        eexists. eapply p; tas.
        eexists. eapply p0; tas.
        eapply p; tas.
      * aa.
    + destruct HSub. eapply cumul_subst_instance; aa.
Qed.


Lemma typing_subst_instance' Σ φ Γ t T u univs :
  wf_ext_wk (Σ, univs) ->
  (Σ, univs) ;;; Γ |- t : T ->
  sub_context_set (monomorphic_udecl univs) (global_ext_context_set (Σ, φ)) ->
  consistent_instance_ext (Σ, φ) univs u ->
  (Σ, φ) ;;; subst_instance_context u Γ
            |- subst_instance_constr u t : subst_instance_constr u T.
Proof.
  intros X X0 X1.
  eapply (typing_subst_instance (Σ, univs)); tas. apply X.
  eapply typing_wf_local; eassumption.
Qed.


Definition global_context_set Σ : ContextSet.t
  := (global_levels Σ, global_constraints Σ).

Lemma global_context_set_sub_ext Σ φ :
  sub_context_set (global_context_set Σ) (global_ext_context_set (Σ, φ)).
Proof.
  split. cbn. apply LevelSetProp.union_subset_2.
  apply ConstraintSetProp.union_subset_2.
Qed.


Lemma weaken_lookup_on_global_env'' Σ c decl :
  wf Σ ->
  lookup_env Σ c = Some decl ->
  sub_context_set (monomorphic_udecl (universes_decl_of_decl decl))
                  (global_context_set Σ).
Proof.
  intros X1 X2; pose proof (weaken_lookup_on_global_env' _ _ _ X1 X2) as XX.
  set (φ := universes_decl_of_decl decl) in *; clearbody φ. clear -XX.
  destruct φ as [φ|φ|φ].
  split; apply XX.
  all: split;
    [apply LevelSetProp.subset_empty|apply ConstraintSetProp.subset_empty].
Qed.


Lemma typing_subst_instance'' Σ φ Γ t T u univs :
  wf_ext_wk (Σ, univs) ->
  (Σ, univs) ;;; Γ |- t : T ->
  sub_context_set (monomorphic_udecl univs) (global_context_set Σ) ->
  consistent_instance_ext (Σ, φ) univs u ->
  (Σ, φ) ;;; subst_instance_context u Γ
            |- subst_instance_constr u t : subst_instance_constr u T.
Proof.
  intros X X0 X1.
  eapply (typing_subst_instance (Σ, univs)); tas. apply X.
  eapply typing_wf_local; eassumption.
  etransitivity; tea. apply global_context_set_sub_ext.
Qed.


Lemma typing_subst_instance_decl Σ Γ t T c decl u :
  wf Σ.1 ->
  lookup_env Σ.1 c = Some decl ->
  (Σ.1, universes_decl_of_decl decl) ;;; Γ |- t : T ->
  consistent_instance_ext Σ (universes_decl_of_decl decl) u ->
  Σ ;;; subst_instance_context u Γ
            |- subst_instance_constr u t : subst_instance_constr u T.
Proof.
  destruct Σ as [Σ φ]. intros X X0 X1 X2.
  eapply typing_subst_instance''; tea. split; tas.
  eapply weaken_lookup_on_global_env'; tea.
  eapply weaken_lookup_on_global_env''; tea.
Qed.

End CheckerFlags.
