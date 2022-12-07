(* Distributed under the terms of the MIT license. *)
From Coq Require Import ssreflect CRelationClasses.
From MetaCoq.Template Require Import utils config Universes uGraph.
From MetaCoq.PCUIC Require Import PCUICAst PCUICOnOne PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICEquality PCUICUnivSubst
     PCUICCases PCUICCumulativity PCUICTyping
     PCUICReduction PCUICWeakeningEnv
     PCUICClosed PCUICPosition PCUICGuardCondition.

Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

Implicit Types (cf : checker_flags).

(** * Universe Substitution lemmas for typing derivations. *)

Local Set Keyed Unification.

Set Default Goal Selector "!".

Create HintDb univ_subst.

Local Ltac aa := rdest; eauto with univ_subst.

Import NonEmptySetFacts.

Lemma subst_instance_level_val u l v v'
      (H1 : forall s, valuation_mono v s = valuation_mono v' s)
      (H2 : forall n, val v (nth n u Level.lzero) = valuation_poly v' n)
  : val v (subst_instance_level u l) = val v' l.
Proof.
  destruct l; cbn; try congruence. apply H2.
Qed.

Lemma eq_valuation v v'
      (H1 : forall s, valuation_mono v s = valuation_mono v' s)
      (H2 : forall n, valuation_poly v n = valuation_poly v' n)
  : forall u : Universe.t, Universe.to_cuniv v u = Universe.to_cuniv v' u.
Proof.
  intros [| | u]; cbnr. f_equal.
  assert (He : forall e : LevelExpr.t, val v e = val v' e). {
    intros [[] b]; cbnr; rewrite ?H1 ?H2; reflexivity. }
  rewrite !val_fold_right.
  induction ((List.rev (LevelAlgExpr.exprs u).2)); cbn; congruence.
Qed.
(*
Lemma is_prop_subst_instance_level u l
    : Level.is_prop (subst_instance_level u l) = Level.is_prop l.
Proof.
  destruct l; cbn; try reflexivity.
  destruct (le_lt_dec #|u| n) as [HH|HH].
  + now rewrite nth_overflow.
  + eapply (forallb_nth _ _ _ Level.lzero Hu) in HH.
    destruct HH as [l [HH1 HH2]]. rewrite HH1. now apply ssrbool.negbTE.
Qed. *)

Lemma subst_instance_level_expr_val u expr v v'
      (H1 : forall s, valuation_mono v s = valuation_mono v' s)
      (H2 : forall n, val v (nth n u Level.lzero) = valuation_poly v' n)
  : val v (subst_instance_level_expr u expr) = val v' expr.
Proof.
  destruct expr as [[] b]; cbnr.
  { now rewrite <- H1. }
  rewrite <- H2, nth_nth_error.
  destruct nth_error; cbnr.
Qed.

Lemma subst_instance_univ0_val u exprs v v'
      (H1 : forall s, valuation_mono v s = valuation_mono v' s)
      (H2 : forall n, val v (nth n u Level.lzero) = valuation_poly v' n)
  : val v (subst_instance_univ0 u exprs) = val v' exprs.
Proof.
  symmetry.
  apply val_caract. split.
  - intros e Xe.
    apply val_le_caract. eexists; split.
    + apply map_spec. eexists; split; tea. reflexivity.
    + erewrite subst_instance_level_expr_val with (v':=v'); tea. reflexivity.
  - destruct ((val_caract (map (subst_instance_level_expr u) exprs) v _).p1 eq_refl)
      as [_ [e [He1 <-]]].
    apply map_spec in He1 as [e0 [He0 ->]].
    eexists; split; tea.
    symmetry; now apply subst_instance_level_expr_val.
Qed.

Lemma subst_instance_univ_val u s v v'
      (H1 : forall s, valuation_mono v s = valuation_mono v' s)
      (H2 : forall n, val v (nth n u Level.lzero) = valuation_poly v' n)
  : Universe.to_cuniv v (subst_instance_univ u s) = Universe.to_cuniv v' s.
Proof.
  destruct s as [ | | exprs]; cbnr.
  f_equal; now apply subst_instance_univ0_val.
Qed.

Definition subst_instance_valuation (u : Instance.t) (v : valuation) :=
  {| valuation_mono := valuation_mono v ;
     valuation_poly := fun i => val v (nth i u Level.lzero) |}.


Lemma subst_instance_level_val' u l v
  : val v (subst_instance_level u l) = val (subst_instance_valuation u v) l.
Proof.
  now apply subst_instance_level_val.
Qed.


Lemma subst_instance_univ0_val' u exprs v
  : val v (subst_instance_univ0 u exprs) = val (subst_instance_valuation u v) exprs.
Proof.
  now apply subst_instance_univ0_val.
Qed.

Lemma subst_instance_univ_val' u l v
  : Universe.to_cuniv v (subst_instance_univ u l) = Universe.to_cuniv (subst_instance_valuation u v) l.
Proof.
  now apply subst_instance_univ_val.
Qed.

Lemma subst_instance_univ_make' (l : LevelExpr.t) u :
  subst_instance u (LevelAlgExpr.make l) = LevelAlgExpr.make (subst_instance_level_expr u l).
Proof. reflexivity. Qed.

Lemma subst_instance_univ_make l u :
  subst_instance_univ u (Universe.make l)
  = Universe.make (subst_instance_level u l).
Proof.
  destruct l; cbnr. rewrite nth_nth_error.
  destruct nth_error; cbnr.
Qed.


Class SubstUnivPreserving Re := Build_SubstUnivPreserving :
  forall s u1 u2, R_universe_instance Re u1 u2 ->
             Re (subst_instance_univ u1 s) (subst_instance_univ u2 s).

Lemma subst_equal_inst_inst Re :
  SubstUnivPreserving Re ->
  forall u u1 u2, R_universe_instance Re u1 u2 ->
             R_universe_instance Re (subst_instance u1 u)
                                    (subst_instance u2 u).
Proof.
  intros hRe u. induction u; cbnr; try now constructor.
  intros u1 u2; unfold R_universe_instance; cbn; constructor.
  - pose proof (hRe (Universe.make a) u1 u2 H) as HH.
    now rewrite !subst_instance_univ_make in HH.
  - exact (IHu u1 u2 H).
Qed.

Lemma subst_equal_inst_global_inst Σ Re Rle gr napp :
  RelationClasses.Reflexive Re ->
  SubstUnivPreserving Re ->
  RelationClasses.subrelation Re Rle ->
  forall u u1 u2, R_universe_instance Re u1 u2 ->
             R_global_instance Σ Re Rle gr napp (subst_instance u1 u)
                                    (subst_instance u2 u).
Proof.
  intros reflRe hRe subr u u1 u2 Ru1u2.
  unfold R_global_instance, R_global_instance_gen, R_opt_variance.
  destruct global_variance_gen as [v|]; auto using subst_equal_inst_inst.
  induction u in v |- *; cbnr; try now constructor.
  - destruct v; simpl; auto.
    split; auto.
    destruct t; simpl; auto.
    * pose proof (hRe (Universe.make a) u1 u2 Ru1u2) as HH.
      now rewrite !subst_instance_univ_make in HH.
    * pose proof (hRe (Universe.make a) u1 u2 Ru1u2) as HH.
      now rewrite !subst_instance_univ_make in HH.
Qed.

Lemma eq_term_upto_univ_subst_instance Σ Re Rle napp :
  RelationClasses.Reflexive Re ->
  SubstUnivPreserving Re ->
  RelationClasses.subrelation Re Rle ->
  forall t u1 u2,
    R_universe_instance Re u1 u2 ->
    eq_term_upto_univ_napp Σ Re Rle napp (subst_instance u1 t)
                            (subst_instance u2 t).
Proof.
  intros ref hRe subr t.
  induction t in napp, Re, Rle, ref, hRe, subr |- * using term_forall_list_ind; intros u1 u2 hu.
  all: cbn; try constructor; eauto using subst_equal_inst_inst.
  all: try eapply All2_map, All_All2; tea; cbn; intros; rdest; eauto.
  all: try (eapply X0 || eapply IHt || eapply IHt1 || eapply IHt2 || eapply e || eapply e0); try typeclasses eauto; auto.
  all: eauto using subst_equal_inst_global_inst.
  - rewrite /eq_predicate /=. intuition auto.
    * solve_all. eapply All_All2; tea; cbn; intros; rdest; eauto.
      eapply X; eauto. tc.
    * eapply subst_equal_inst_inst => //.
    * solve_all. reflexivity.
    * eapply X => //.
  - solve_all. reflexivity.
Qed.

#[global]
Instance eq_universe_SubstUnivPreserving {cf:checker_flags} φ :
  SubstUnivPreserving (eq_universe φ).
Proof.
  intros [| | exprs]; cbnr.
  intros u1 u2 hu.
  unfold_univ_rel.
  assert (He : forall e, val v (subst_instance_level_expr u1 e)
                    = val v (subst_instance_level_expr u2 e)). {
    destruct e as [[] b]; cbnr.
    case_eq (nth_error u1 n).
    - intros l1 X. eapply Forall2_nth_error_Some_l in hu.
      2: now rewrite -> nth_error_map, X.
      destruct hu as [l2 [H1 H2]].
      rewrite nth_error_map in H1.
      destruct (nth_error u2 n) as [l2'|]; [|discriminate].
      apply some_inj in H1; subst. clear u1 u2 X.
      specialize (H2 v Hv).
      destruct l1, l2'; cbn in *; noconf H2; try lia.
    - intros X. eapply Forall2_nth_error_None_l in hu.
      2: now rewrite -> nth_error_map, X.
      rewrite nth_error_map in hu.
      destruct (nth_error u2 n); [discriminate|reflexivity]. }
  simpl.
  apply val_caract; split.
  - intros e Xe. apply map_spec in Xe as [e' [H1 H2]]; subst.
    apply val_le_caract. eexists; split.
    + apply map_spec; eexists; split; tea; reflexivity.
    + now rewrite He.
  - destruct ((val_caract (map (subst_instance_level_expr u2) exprs) v _).p1 eq_refl)
      as [_ [e [He1 He2]]]. rewrite <- He2.
    apply map_spec in He1. destruct He1 as [e0 [He0 He1]]; subst.
    eexists; split; [|eapply He]. eapply map_spec.
    now eexists; split; tea.
Qed.

#[global]
Instance leq_universe_SubstUnivPreserving {cf:checker_flags} φ :
  SubstUnivPreserving (leq_universe φ).
Proof.
  intros [| | exprs] u1 u2 hu; cbnr.
  unfold_univ_rel.
  assert (He : forall e, val v (subst_instance_level_expr u1 e)
                    <= val v (subst_instance_level_expr u2 e)). {
    destruct e as [[] b]; cbnr.
    case_eq (nth_error u1 n).
    - intros l1 X. eapply Forall2_nth_error_Some_l in hu.
      2: now rewrite -> nth_error_map, X.
      destruct hu as [l2 [H1 H2]].
      rewrite nth_error_map in H1.
      destruct (nth_error u2 n) as [l2'|]; [|discriminate].
      apply some_inj in H1; subst. clear u1 u2 X.
      specialize (H2 v Hv).
      destruct l1, l2'; cbn in *; noconf H2; try lia.
    - intros X. eapply Forall2_nth_error_None_l in hu.
      2: now rewrite -> nth_error_map, X.
      rewrite nth_error_map in hu.
      destruct (nth_error u2 n); [discriminate|reflexivity]. }
  simpl.
  rewrite Z.sub_0_r.
  eapply Nat2Z.inj_le.
  remember (val v (subst_instance u2 exprs)) as val2 eqn:eq. symmetry in eq.
  apply val_caract in eq.
  destruct eq.
  destruct H0 as [e [inet vale]].
  apply map_spec in inet as [e' [H1 H2]]; subst.
  remember (val v (subst_instance u1 exprs)) as val1 eqn:eq. symmetry in eq.
  apply val_caract in eq as [eq' [e'' [ine'' vale'']]].
  subst val1.
  apply map_spec in ine'' as [e0 [ine0 eq]].
  specialize (He e0). subst e''.
  etransitivity.
  - eassumption.
  - eapply H.
    eapply map_spec.
    exists e0; split; auto.
Qed.

#[global]
Instance compare_universe_substu {cf} le Σ : SubstUnivPreserving (compare_universe le Σ).
Proof.
  destruct le; tc.
Qed.

Global Instance subst_instance_def {A} `(UnivSubst A) : UnivSubst (def A)
  := fun u => map_def (subst_instance u) (subst_instance u).

Global Instance subst_instance_prod {A B} `(UnivSubst A) `(UnivSubst B)
  : UnivSubst (A × B)
  := fun u => map_pair (subst_instance u) (subst_instance u).

Global Instance subst_instance_nat : UnivSubst nat
  := fun _ n => n.

Lemma subst_instance_level_two u1 u2 l :
  subst_instance_level u1 (subst_instance_level u2 l)
  = subst_instance_level (subst_instance u1 u2) l.
Proof.
  destruct l; cbn; try reflexivity.
  unfold subst_instance.
  rewrite <- (map_nth (subst_instance_level u1)); reflexivity.
Qed.

Lemma subst_instance_level_expr_two u1 u2 e :
  subst_instance_level_expr u1 (subst_instance_level_expr u2 e)
  = subst_instance_level_expr (subst_instance u1 u2) e.
Proof.
  destruct e as [[] b]; cbnr.
  unfold subst_instance. erewrite nth_error_map.
  destruct nth_error; cbnr.
  destruct t; cbnr.
  rewrite nth_nth_error. destruct nth_error; cbnr.
Qed.

Lemma subst_instance_univ0_two u1 u2 exprs :
  subst_instance_univ0 u1 (subst_instance_univ0 u2 exprs)
  = subst_instance_univ0 (subst_instance u1 u2) exprs.
Proof.
  unfold subst_instance_univ0.
  eapply eq_univ'.
  intro l; split; intro Hl; apply map_spec in Hl as [l' [H1 H2]];
    apply map_spec; subst.
  - apply map_spec in H1 as [l'' [H1 H2]]; subst.
    eexists; split; tea. apply subst_instance_level_expr_two.
  - eexists; split. 2: symmetry; eapply subst_instance_level_expr_two.
    apply map_spec. eexists; split; tea; reflexivity.
Qed.


Lemma subst_instance_univ_two u1 u2 s :
  subst_instance_univ u1 (subst_instance_univ u2 s)
  = subst_instance_univ (subst_instance u1 u2) s.
Proof.
  destruct s; cbnr. f_equal.
  apply subst_instance_univ0_two.
Qed.

Lemma subst_instance_two_instance u1 u2 (u : Instance.t) :
  subst_instance u1 (subst_instance u2 u)
  = subst_instance (subst_instance u1 u2) u.
Proof.
  rewrite /subst_instance /= /subst_instance_instance.
  rewrite map_map.
  apply map_ext, subst_instance_level_two.
Qed.

Lemma subst_instance_two u1 u2 (t : term) :
  subst_instance u1 (subst_instance u2 t)
  = subst_instance (subst_instance u1 u2) t.
Proof.
  rewrite /subst_instance /=.
  induction t using term_forall_list_ind; cbn; f_equal;
    auto using subst_instance_two_instance.
  - rewrite map_map. now apply All_map_eq.
  - apply subst_instance_univ_two.
  - destruct X; red in X0. rewrite map_predicate_map_predicate.
    apply map_predicate_eq_spec; solve_all.
    now rewrite [subst_instance_instance _ _]subst_instance_two_instance.
  - rewrite map_map. apply All_map_eq. red in X0. solve_all.
  - rewrite map_map. apply All_map_eq. solve_all.
    rewrite map_def_map_def; solve_all.
  - rewrite map_map. apply All_map_eq. solve_all.
    rewrite map_def_map_def; solve_all.
Qed.

Lemma subst_instance_two_context u1 u2 (Γ : context) :
  subst_instance u1 (subst_instance u2 Γ)
  = subst_instance (subst_instance u1 u2) Γ.
Proof.
  rewrite /subst_instance /=.
  induction Γ; try reflexivity.
  simpl. rewrite IHΓ; f_equal.
  destruct a as [? [] ?]; unfold map_decl; cbn;
    now rewrite !subst_instance_two.
Qed.

Lemma subst_instance_cstr_two u1 u2 c :
  subst_instance_cstr u1 (subst_instance_cstr u2 c)
  = subst_instance_cstr (subst_instance u1 u2) c.
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
    + pcuicfo. now destruct H0 as [? ?].
    + intros t. etransitivity. 1: eapply IHl.
      split; intros [HH|HH].
      * destruct a as [[l1 a] l2]. apply CS.add_spec in HH.
        destruct HH as [HH|HH]. 2: now left.
        right; eexists. split; [|left; reflexivity]. assumption.
      * destruct HH as [c' ?]. right; exists c'; intuition.
      * left. destruct a as [[l1 a] l2]. apply CS.add_spec.
        now right.
      * destruct HH as [c' [HH1 [?|?]]]; subst.
        -- left. destruct c' as [[l1 c'] l2];
           apply CS.add_spec; now left.
        -- right. exists c'. intuition.
  - rewrite ConstraintSetFact.empty_iff.
    transitivity (exists c', c = subst_instance_cstr u c'
                        /\ In c' (CS.elements ctrs)).
    1: intuition.
    apply iff_ex; intro. apply and_iff_compat_l. symmetry.
    etransitivity. 1: symmetry; apply CS.elements_spec1.
    etransitivity. 1: eapply SetoidList.InA_alt.
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
    (subst_instance_cstrs (subst_instance u1 u2) ctrs).
Proof.
  intro c; split; intro Hc; apply In_subst_instance_cstrs.
  - apply In_subst_instance_cstrs in Hc; destruct Hc as [c' [eq Hc']].
    apply In_subst_instance_cstrs in Hc'; destruct Hc' as [c'' [eq' Hc'']].
    exists c''. subst; now rewrite subst_instance_cstr_two.
  - apply In_subst_instance_cstrs in Hc; destruct Hc as [c' [eq Hc']].
    exists (subst_instance_cstr u2 c'). split.
    + now rewrite subst_instance_cstr_two.
    + now apply In_subst_instance_cstrs'.
Qed.

Lemma is_prop_subst_instance_univ u l
  : Universe.is_prop (subst_instance_univ u l) = Universe.is_prop l.
Proof.
  destruct l; cbnr.
Qed.

Lemma is_sprop_subst_instance_univ u l
  : Universe.is_sprop (subst_instance_univ u l) = Universe.is_sprop l.
Proof.
  destruct l; cbnr.
Qed.

Lemma is_prop_subst_instance u x0 :
  Universe.is_prop x0 -> Universe.is_prop (subst_instance_univ u x0).
Proof.
  now rewrite is_prop_subst_instance_univ.
Qed.

Lemma sup_subst_instance_univ0 u s1 s2 :
  subst_instance u (LevelAlgExpr.sup s1 s2)
  = LevelAlgExpr.sup (subst_instance u s1) (subst_instance u s2).
Proof.
  apply eq_univ'. cbn.
  intro x; split; intro Hx.
  + apply map_spec in Hx as [y [H H']]; subst.
    apply LevelExprSet.union_spec.
    apply LevelExprSet.union_spec in H as [H|H]; [left|right].
    all: apply map_spec; eexists; split; tea; reflexivity.
  + apply map_spec.
    apply LevelExprSet.union_spec in Hx as [H|H];
      apply map_spec in H as [y [H H']]; subst.
    all: eexists; split; [eapply LevelExprSet.union_spec|reflexivity]; auto.
Qed.

Lemma sup_subst_instance_univ u s1 s2 :
  subst_instance_univ u (Universe.sup s1 s2)
  = Universe.sup (subst_instance_univ u s1) (subst_instance_univ u s2).
Proof.
  destruct s1, s2; cbnr. f_equal.
  apply sup_subst_instance_univ0.
Qed.

Lemma consistent_instance_declared {cf: checker_flags} lvs φ uctx u :
  consistent_instance lvs φ uctx u ->
  forallb (fun l => LS.mem l lvs) u.
Proof.
  unfold consistent_instance. destruct uctx as [|ctx].
  1: destruct u; [reflexivity|discriminate].
  intuition auto.
Qed.

Lemma monomorphic_level_notin_AUContext s φ :
  ~ LS.In (Level.Level s) (AUContext.levels φ).
Proof.
  destruct φ as [φ1 φ2].
  intro H. apply (proj1 (LevelSetProp.of_list_1 _ _)) in H. cbn in H.
  apply SetoidList.InA_alt in H.
  destruct H as [? [? H]]; subst. revert H.
  unfold mapi; generalize 0.
  induction φ1; cbn. 1: trivial.
  intros n [H|H].
  - discriminate.
  - eauto.
Qed.

Global Instance satisfies_equal_sets v :
  Morphisms.Proper (Morphisms.respectful CS.Equal iff) (satisfies v).
Proof.
  intros φ1 φ2 H; split; intros HH c Hc; now apply HH, H.
Qed.

Global Instance satisfies_subsets v :
  Morphisms.Proper (Morphisms.respectful CS.Subset (fun A B : Prop => B -> A))
                   (satisfies v).
Proof.
  intros φ1 φ2 H H2 c Hc; now apply H2, H.
Qed.

#[global] Hint Resolve subst_instance_cstrs_two
     satisfies_equal_sets satisfies_subsets : univ_subst.

Lemma satisfies0_subst_instance_ctr u v c
  : satisfies0 v (subst_instance_cstr u c)
    <-> satisfies0 (subst_instance_valuation u v) c.
Proof.
  destruct c as [[l1 []] l2]; unfold subst_instance_cstr; cbn;
    split; intro H; constructor; inv H.
  all: rewrite <- ?subst_instance_level_val'; tea.
  all: rewrite ?subst_instance_level_val'; tea.
Qed.

Lemma satisfies_subst_instance_ctr u v ctrs
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

Lemma not_var_global_levels {cf : checker_flags} {Σ} (hΣ : wf Σ) :
  LS.For_all (negb ∘ Level.is_var) (global_levels Σ).
Proof.
  destruct hΣ as [onu ond]. apply onu.
Qed.

Definition wf_ext_wk {cf : checker_flags} (Σ : global_env_ext)
  := wf Σ.1 × on_udecl_prop Σ.1 Σ.2.

Lemma wf_ext_wk_wf {cf:checker_flags} Σ : wf_ext_wk Σ -> wf Σ.
Proof. intro H; apply H. Qed.

#[global]
Hint Resolve wf_ext_wk_wf : core.

Lemma not_var_global_ext_levels {cf : checker_flags} Σ (hΣ : wf_ext_wk (Σ, Monomorphic_ctx)) :
  LS.For_all (negb ∘ Level.is_var) (global_ext_levels (Σ, Monomorphic_ctx)).
Proof. apply hΣ. Qed.

Lemma levels_global_constraint {cf : checker_flags} Σ (hΣ : wf Σ) c :
  CS.In c (global_constraints Σ)
  -> LS.In c.1.1 (global_levels Σ)
    /\ LS.In c.2 (global_levels Σ).
Proof.
  intros inc.
  destruct hΣ. destruct o. specialize (H c inc).
  destruct c as [[l eq] r]; apply H.
Qed.

Lemma levels_global_ext_constraint {cf : checker_flags} Σ φ (hΣ : wf_ext_wk (Σ, φ)) c :
  CS.In c (global_ext_constraints (Σ, φ))
  -> LS.In c.1.1 (global_ext_levels (Σ, φ))
    /\ LS.In c.2 (global_ext_levels (Σ, φ)).
Proof.
  intro H. apply CS.union_spec in H; simpl in H.
  destruct hΣ as [hΣ Hφ], H as [Hc|H]; simpl in *.
  - red in Hφ. unfold global_ext_levels. simpl.
    destruct c as [[l1 c] l2]; exact (Hφ _ Hc).
  - apply levels_global_constraint in H; tas.
    split; apply LS.union_spec; right; apply H.
Qed.

Definition is_monomorphic_cstr (c : UnivConstraint.t)
  := negb (Level.is_var c.1.1) && negb (Level.is_var c.2).

Lemma monomorphic_global_constraint {cf : checker_flags} Σ (hΣ : wf Σ) c :
  CS.In c (global_constraints Σ)
  -> is_monomorphic_cstr c.
Proof.
  intros H. apply levels_global_constraint in H; tas.
  apply andb_and. split; destruct H as [H1 H2].
  - now apply not_var_global_levels in H1.
  - now apply not_var_global_levels in H2.
Qed.

Lemma monomorphic_global_constraint_ext {cf : checker_flags} Σ
      (hΣ : wf_ext_wk (Σ, Monomorphic_ctx)) c :
  CS.In c (global_ext_constraints (Σ, Monomorphic_ctx))
  -> is_monomorphic_cstr c.
Proof.
  intros H. apply levels_global_ext_constraint in H; tas.
  apply andb_and. split; destruct H as [H1 H2].
  - now apply not_var_global_ext_levels in H1.
  - now apply not_var_global_ext_levels in H2.
Qed.

#[global] Hint Resolve monomorphic_global_constraint monomorphic_global_constraint_ext
  : univ_subst.

Lemma subst_instance_monom_cstr inst c :
  is_monomorphic_cstr c
  -> subst_instance_cstr inst c = c.
Proof.
  intro H; apply andb_and in H. destruct H.
  destruct c as [[[] ?] []]; cbnr; discriminate.
Qed.

Lemma equal_subst_instance_cstrs_mono u cstrs :
  CS.For_all is_monomorphic_cstr cstrs ->
  CS.Equal (subst_instance_cstrs u cstrs) cstrs.
Proof.
  intros HH c. etransitivity.
  - eapply In_subst_instance_cstrs.
  - split; intro H.
    + destruct H as [c' [eq Hc']]. subst; rewrite subst_instance_monom_cstr; aa.
    + exists c. rewrite subst_instance_monom_cstr; aa.
Qed.

Lemma subst_instance_cstrs_union u φ φ' :
  CS.Equal (subst_instance_cstrs u (CS.union φ φ'))
           (CS.union (subst_instance_cstrs u φ) (subst_instance_cstrs u φ')).
Proof.
  intro c; split; intro Hc.
  - apply In_subst_instance_cstrs in Hc.
    destruct Hc as [c' [eq Hc]]; subst.
    apply CS.union_spec in Hc. apply CS.union_spec.
    destruct Hc; [left|right]; now apply In_subst_instance_cstrs'.
  - apply In_subst_instance_cstrs.
    apply CS.union_spec in Hc.
    destruct Hc as [Hc|Hc]; apply In_subst_instance_cstrs in Hc;
      destruct Hc as [c'[eq Hc]]; exists c'; aa; apply CS.union_spec;
        [left|right]; aa.
Qed.

#[global] Hint Unfold CS.For_all : univ_subst.

Definition sub_context_set (φ φ' : ContextSet.t)
  := LS.Subset φ.1 φ'.1 /\ CS.Subset φ.2 φ'.2.

Definition global_ext_context_set Σ : ContextSet.t
  := (global_ext_levels Σ, global_ext_constraints Σ).

Global Instance sub_context_set_trans : RelationClasses.Transitive sub_context_set.
Proof.
  split; (etransitivity; [eapply H | eapply H0]).
Qed.

Lemma consistent_ext_trans_polymorphic_case_aux {cf : checker_flags} {Σ φ1 φ2 φ' udecl inst inst'} :
  wf_ext_wk (Σ, Polymorphic_ctx (φ1, φ2)) ->
  valid_constraints0 (global_ext_constraints (Σ, Polymorphic_ctx (φ1, φ2)))
                     (subst_instance_cstrs inst udecl) ->
  valid_constraints0 (global_ext_constraints (Σ, φ'))
                     (subst_instance_cstrs inst' φ2) ->
  valid_constraints0 (global_ext_constraints (Σ, φ'))
                     (subst_instance_cstrs
                        (subst_instance inst' inst) udecl).
Proof.
  intros [HΣ Hφ] H3 H2.
  intros v Hv. rewrite <- subst_instance_cstrs_two.
  apply satisfies_subst_instance_ctr; tas. apply H3.
  apply satisfies_union; simpl. split.
  - apply satisfies_subst_instance_ctr; auto.
  - apply satisfies_subst_instance_ctr; tas.
    rewrite equal_subst_instance_cstrs_mono; aa.
    apply satisfies_union in Hv. apply Hv.
Qed.

Lemma consistent_ext_trans_polymorphic_cases {cf : checker_flags} Σ φ φ' udecl inst inst' :
  wf_ext_wk (Σ, φ) ->
  consistent_instance_ext (Σ, φ) (Polymorphic_ctx udecl) inst ->
  consistent_instance_ext (Σ, φ') φ inst' ->
  consistent_instance_ext (Σ, φ') (Polymorphic_ctx udecl)
                          (subst_instance inst' inst).
Proof.
  intros HΣφ [H [H0 H1]] H2.
  repeat split.
  2: now rewrite subst_instance_instance_length.
  + rewrite forallb_map. apply forallb_forall.
    intros l Hl. (* unfold global_ext_levels in *; simpl in *. *)
    eapply forallb_forall in H; tea. clear -H H2 Hl.
    apply LevelSet_mem_union in H. destruct H as [H|H].
    2: { destruct l; simpl; try (apply LevelSet_mem_union; right; assumption).
         apply consistent_instance_declared in H2.
         apply (forallb_nth' n Level.lzero) in H2.
         destruct H2 as [[? [H2 ?]]|H2]; rewrite H2; tas.
         apply LS.mem_spec, global_ext_levels_InSet. }
    *  destruct l; simpl.
       -- apply LS.mem_spec, global_ext_levels_InSet.
       -- apply LS.mem_spec in H.
          destruct φ as [|[φ1 φ2]]; simpl in *.
          { now apply LevelSetFact.empty_iff in H. }
          now apply monomorphic_level_notin_AUContext in H.
       -- apply consistent_instance_declared in H2.
          apply (forallb_nth' n Level.lzero) in H2.
          destruct H2 as [[? [H2 ?]]|H2]; rewrite H2; tas.
          apply LS.mem_spec, global_ext_levels_InSet.
  + unfold consistent_instance_ext, consistent_instance in H2.
    unfold valid_constraints in *; destruct check_univs; [|trivial].
    destruct φ as [|[φ1 φ2]]; simpl in *.
    * intros v Hv. rewrite <- subst_instance_cstrs_two.
      apply satisfies_subst_instance_ctr; tas.
      apply H1. apply satisfies_subst_instance_ctr; tas.
      rewrite equal_subst_instance_cstrs_mono; aa.
      apply satisfies_union; simpl; split.
      -- intros c Hc. now apply Hv.
      -- apply satisfies_union in Hv; apply Hv.
    * destruct H2 as [_ [_ H2]].
      eapply consistent_ext_trans_polymorphic_case_aux; try eassumption.
Qed.

Lemma consistent_ext_trans {cf : checker_flags} Σ φ φ' udecl inst inst' :
  wf_ext_wk (Σ, φ) ->
  consistent_instance_ext (Σ, φ) udecl inst ->
  consistent_instance_ext (Σ, φ') φ inst' ->
  consistent_instance_ext (Σ, φ') udecl (subst_instance inst' inst).
Proof.
  intros HΣφ H1 H2. destruct udecl as [|udecl].
  - (* udecl monomorphic *)
    cbn; now len.
  - (* udecl polymorphic *)
    eapply consistent_ext_trans_polymorphic_cases; eassumption.
Qed.

#[global] Hint Resolve consistent_ext_trans : univ_subst.

Lemma consistent_instance_valid_constraints {cf : checker_flags} Σ φ u univs :
  wf_ext_wk (Σ, φ) ->
  consistent_instance_ext (Σ, univs) φ u ->
  valid_constraints (global_ext_constraints (Σ, univs))
                    (subst_instance_cstrs u (global_ext_constraints (Σ, φ))).
Proof.
  intros HΣ HH.
  unfold valid_constraints; case_eq check_univs; [intro Hcf|trivial].
  intros v Hv. apply satisfies_subst_instance_ctr; tas.
  apply satisfies_union; simpl; split.
  - destruct φ as [|[φ1 φ2]].
    + cbn. apply satisfies_subst_instance_ctr; tas.
      rewrite equal_subst_instance_cstrs_mono; aa.
      * intros x hin. csets.
      * intros x hin. csets.
    + destruct HH as [_ [_ H1]].
      unfold valid_constraints in H1; rewrite Hcf in H1.
      apply satisfies_subst_instance_ctr; aa.
  - apply satisfies_subst_instance_ctr; tas.
    apply satisfies_union in Hv. destruct HΣ.
    rewrite equal_subst_instance_cstrs_mono; aa.
Qed.

#[global] Hint Resolve consistent_instance_valid_constraints : univ_subst.

Class SubstUnivPreserved {cf : checker_flags} {A} `{UnivSubst A} (R : ConstraintSet.t -> crelation A)
  := Build_SubstUnivPreserved :
       forall φ φ' (u : Instance.t),
         valid_constraints φ' (subst_instance_cstrs u φ) ->
         subrelation (R φ)
                     (precompose (R φ') (subst_instance u)).

Lemma satisfies_subst_instance {cf : checker_flags} φ φ' u :
  check_univs ->
  valid_constraints φ' (subst_instance_cstrs u φ) ->
  forall v, satisfies v φ' ->
       satisfies (subst_instance_valuation u v) φ.
Proof.
  intros Hcf HH v Hv.
  unfold valid_constraints in HH; rewrite Hcf in HH.
  apply satisfies_subst_instance_ctr; aa.
Qed.

Global Instance leq_universe_subst_instance {cf : checker_flags} : SubstUnivPreserved leq_universe.
Proof.
  intros φ φ' u HH [| | exprs] [| | exprs'] Hle; cbnr; trivial.
  unfold_univ_rel eqn:H.
  rewrite !subst_instance_univ0_val'; tas.
  apply Hle.
  eapply satisfies_subst_instance; tea.
Qed.

Global Instance eq_universe_subst_instance {cf : checker_flags} : SubstUnivPreserved eq_universe.
Proof.
  intros φ φ' u HH [| | exprs] [| | exprs'] Hle; cbnr; trivial.
  unfold_univ_rel eqn:H.
  rewrite !subst_instance_univ0_val'; tas.
  apply Hle.
  eapply satisfies_subst_instance; tea.
Qed.

Lemma precompose_subst_instance Rle u i i' :
  precompose (R_universe_instance Rle) (subst_instance u) i i'
  <~> R_universe_instance (precompose Rle (subst_instance_univ u)) i i'.
Proof.
  unfold R_universe_instance, subst_instance.
  replace (List.map Universe.make (List.map (subst_instance_level u) i))
    with (List.map (subst_instance_univ u) (List.map Universe.make i)).
  1: replace (List.map Universe.make (List.map (subst_instance_level u) i'))
      with (List.map (subst_instance_univ u) (List.map Universe.make i')).
  1: split.
  1: apply Forall2_map_inv.
  1: apply Forall2_map.
  all: rewrite !map_map; apply map_ext.
  all: intro; apply subst_instance_univ_make.
Qed.

Definition precompose_subst_instance__1 Rle u i i'
  := fst (precompose_subst_instance Rle u i i').

Definition precompose_subst_instance__2 Rle u i i'
  := snd (precompose_subst_instance Rle u i i').

Lemma subst_instance_level_expr_make u l :
  subst_instance_level_expr u (LevelExpr.make l) = LevelExpr.make (subst_instance_level u l).
Proof.
  destruct l; simpl; auto.
  rewrite nth_nth_error. now destruct nth_error.
Qed.

Lemma subst_instance_make'_make u l :
  subst_instance u (LevelAlgExpr.make (LevelExpr.make l)) =
  LevelAlgExpr.make (LevelExpr.make (subst_instance_level u l)).
Proof.
  now rewrite subst_instance_univ_make' subst_instance_level_expr_make.
Qed.

Lemma precompose_subst_instance_global Σ Re Rle gr napp u i i' :
  precompose (R_global_instance Σ Re Rle gr napp) (subst_instance u) i i'
  <~> R_global_instance Σ (precompose Re (subst_instance_univ u))
    (precompose Rle (subst_instance_univ u)) gr napp i i'.
Proof.
  unfold R_global_instance, R_global_instance_gen, R_opt_variance, subst_instance.
  destruct global_variance_gen as [v|]; eauto using precompose_subst_instance.
  induction i in i', v |- *; destruct i', v; simpl; try split; auto.
  - destruct (IHi i' []). intros; auto.
  - destruct (IHi i' []). intros; auto.
  - destruct (IHi i' v). intros []; split; auto.
    destruct t0; simpl in *; auto.
    * now rewrite !subst_instance_make'_make.
    * now rewrite !subst_instance_make'_make.
  - destruct (IHi i' v). intros []; split; auto.
    destruct t0; simpl in *; auto.
    * now rewrite !subst_instance_make'_make in H.
    * now rewrite !subst_instance_make'_make in H.
Qed.

Definition precompose_subst_instance_global__1 Σ Re Rle gr napp u i i'
  := fst (precompose_subst_instance_global Σ Re Rle gr napp u i i').

Definition precompose_subst_instance_global__2 Σ Re Rle gr napp u i i'
  := snd (precompose_subst_instance_global Σ Re Rle gr napp u i i').

Global Instance eq_term_upto_univ_subst_preserved {cf : checker_flags} Σ
  (Re Rle : ConstraintSet.t -> Universe.t -> Universe.t -> Prop) napp
  {he: SubstUnivPreserved Re} {hle: SubstUnivPreserved Rle}
  : SubstUnivPreserved (fun φ => eq_term_upto_univ_napp Σ (Re φ) (Rle φ) napp).
Proof.
  intros φ φ' u HH t t'.
  specialize (he _ _ _ HH).
  specialize (hle _ _ _ HH).
  clear HH. cbn in he.
  induction t in napp, t', Rle, hle |- * using term_forall_list_ind;
    inversion 1; subst; cbn; constructor;
      eauto using precompose_subst_instance__2, R_universe_instance_impl'.
  all: try (apply All2_map; eapply All2_impl'; tea;
    eapply All_impl; eauto; cbn; intros; aa).
  - inv X.
    eapply precompose_subst_instance_global__2.
    eapply R_global_instance_impl_same_napp; eauto.
  - inv X.
    eapply precompose_subst_instance_global__2.
    eapply R_global_instance_impl_same_napp; eauto.
  - destruct X2 as [? [? [? ?]]].
    repeat split; simpl; eauto; solve_all.
    * eapply precompose_subst_instance.
      eapply R_universe_instance_impl; eauto.
Qed.

Lemma leq_term_subst_instance {cf : checker_flags} Σ : SubstUnivPreserved (leq_term Σ).
Proof. apply eq_term_upto_univ_subst_preserved; cbn; apply _. Qed.

Lemma eq_term_subst_instance {cf : checker_flags} Σ : SubstUnivPreserved (eq_term Σ).
Proof. apply eq_term_upto_univ_subst_preserved; cbn; exact _. Qed.

Lemma compare_term_subst_instance {cf : checker_flags} pb Σ : SubstUnivPreserved (compare_term pb Σ).
Proof. apply eq_term_upto_univ_subst_preserved; cbn; try destruct pb; exact _. Qed.

(** Now routine lemmas ... *)

Lemma In_subst_instance x u (l : LevelAlgExpr.t) :
  LevelExprSet.In x (subst_instance u l) <->
  (exists x', LevelExprSet.In x' l /\ x = subst_instance u x').
Proof.
  unfold subst_instance; cbn.
  unfold subst_instance_univ0.
  now rewrite map_spec.
Qed.

Lemma subst_instance_univ_super l u
  : subst_instance_univ u (Universe.super l) = Universe.super (subst_instance u l).
Proof.
  destruct l; cbnr. f_equal.
  apply eq_univ'.
  intros x.
  rewrite In_subst_instance.
  rewrite spec_map_succ. split.
  * intros [x' [hin eq]].
    subst.
    apply spec_map_succ in hin as [y [int eq]].
    subst x'. exists (subst_instance u y).
    split; auto.
    - rewrite In_subst_instance. exists y; split; auto.
    - destruct y as [[] ?]; simpl; cbn; auto.
      now destruct nth_error.
  * intros [x' [hin eq]]. subst x.
    apply In_subst_instance in hin as [y [hin eq]].
    subst x'.
    exists (LevelExpr.succ y); cbn.
    rewrite spec_map_succ. split.
    - exists y; auto.
    - destruct y as [[] ?]; cbn; auto.
      now destruct nth_error.
Qed.

Lemma monomorphic_level_notin_levels_of_udecl s udecl :
  LevelSet.In (Level.Level s) (levels_of_udecl udecl) -> False.
Proof.
  destruct udecl; cbn.
  - lsets.
  - apply monomorphic_level_notin_AUContext.
Qed.

Lemma LevelIn_subst_instance {cf : checker_flags} Σ l u univs :
  LS.In l (global_ext_levels Σ) ->
  consistent_instance_ext (Σ.1, univs) Σ.2 u ->
  LS.In (subst_instance_level u l) (global_ext_levels (Σ.1, univs)).
Proof.
  intros H H'. destruct l; simpl.
  - apply global_ext_levels_InSet.
  - apply LS.union_spec in H; destruct H as [H|H]; simpl in *.
    + now apply monomorphic_level_notin_levels_of_udecl in H.
    + apply LS.union_spec; now right.
  - apply consistent_instance_declared in H'.
    apply (forallb_nth' n Level.lzero) in H'.
    destruct H' as [[? [eq ?]]|eq]; rewrite eq.
    + now apply LS.mem_spec.
    + apply global_ext_levels_InSet.
Qed.


Lemma product_subst_instance u s1 s2
 : subst_instance_univ u (Universe.sort_of_product s1 s2)
   = Universe.sort_of_product (subst_instance_univ u s1) (subst_instance_univ u s2).
Proof.
  unfold Universe.sort_of_product.
  rewrite is_prop_subst_instance_univ; tas.
  destruct s2; cbn; try reflexivity.
  destruct s1; cbn; try reflexivity.
  f_equal.
  apply sup_subst_instance_univ0.
Qed.

Lemma subst_instance_extended_subst u Γ :
  subst_instance u (extended_subst Γ 0) =
  extended_subst (subst_instance u Γ) 0.
Proof.
  rewrite /subst_instance /= /subst_instance_list /subst_instance /=.
  induction Γ as [|[na [b|] ty] Γ]; auto; rewrite /=; len; f_equal; auto.
  - rewrite [subst_instance_constr _ _]subst_instance_subst -IHΓ. f_equal.
    now rewrite subst_instance_lift.
  - rewrite !(lift_extended_subst _ 1).
    rewrite map_map_compose.
    setoid_rewrite subst_instance_lift.
    now rewrite -map_map_compose IHΓ.
Qed.
#[global] Hint Rewrite subst_instance_extended_subst : substu.

Lemma expand_lets_subst_instance u Γ t :
  subst_instance u (expand_lets Γ t) =
  expand_lets (subst_instance u Γ) (subst_instance u t).
Proof.
  rewrite /expand_lets /expand_lets_k.
  rewrite subst_instance_subst subst_instance_lift.
  now rewrite subst_instance_extended_subst /=; len.
Qed.
#[global] Hint Rewrite expand_lets_subst_instance : substu.

Global Instance subst_instance_predicate : UnivSubst (predicate term)
  := fun u => map_predicate (subst_instance u) (subst_instance u) (subst_instance u) id.

Lemma fix_subst_instance_subst u mfix :
  subst_instance u (fix_subst mfix) = fix_subst (subst_instance u mfix).
Proof.
  rewrite /subst_instance /subst_instance_list.
  unfold fix_subst. rewrite map_length.
  generalize #|mfix|. induction n. 1: reflexivity.
  simpl. rewrite IHn; reflexivity.
Qed.

Lemma cofix_subst_instance_subst u mfix :
  subst_instance u (cofix_subst mfix) = cofix_subst (subst_instance u mfix).
Proof.
  rewrite /subst_instance /subst_instance_list.
  unfold cofix_subst. rewrite map_length.
  generalize #|mfix|. induction n. 1: reflexivity.
  simpl. rewrite IHn; reflexivity.
Qed.

Lemma isConstruct_app_subst_instance u t :
  isConstruct_app (subst_instance u t) = isConstruct_app t.
Proof.
  unfold isConstruct_app.
  assert (HH: (decompose_app (subst_instance u t)).1
              = subst_instance u (decompose_app t).1). {
    unfold decompose_app. generalize (@nil term) at 1. generalize (@nil term).
    induction t; cbn; try reflexivity.
    intros l l'. erewrite IHt1; reflexivity. }
  rewrite HH. destruct (decompose_app t).1; reflexivity.
Qed.

Lemma fix_context_subst_instance u mfix :
  subst_instance u (fix_context mfix)
  = fix_context (subst_instance u mfix).
Proof.
  rewrite /subst_instance /= /subst_instance /subst_instance_context /map_context /fix_context.
  rewrite map_rev. f_equal.
  rewrite map_mapi mapi_map. eapply mapi_ext.
  intros n x. unfold map_decl, vass; cbn. f_equal.
  apply subst_instance_lift.
Qed.

Lemma subst_instance_app {A} {au : UnivSubst A} u (L1 L2 : list A) :
  subst_instance u (L1 ++ L2)
  = subst_instance u L1 ++ subst_instance u L2.
Proof.
  rewrite /subst_instance /= /subst_instance_list /=.
  now rewrite map_app.
Qed.

Lemma subst_instance_app_ctx u (L1 L2 : context) :
  subst_instance u (L1 ,,, L2)
  = subst_instance u L1 ,,, subst_instance u L2.
Proof.
  rewrite /app_context. now apply subst_instance_app.
Qed.

Definition map_constructor_body' f c :=
  {| cstr_name := cstr_name c;
     cstr_args := map_context f (cstr_args c);
     cstr_indices := List.map f (cstr_indices c);
     cstr_type := f (cstr_type c);
     cstr_arity := cstr_arity c |}.

Global Instance subst_instance_constructor_body : UnivSubst constructor_body
  := fun u => map_constructor_body' (subst_instance u).

Definition map_one_inductive_body' fu f oib :=
	{|
    ind_name := oib.(ind_name);
    ind_indices := map_context f oib.(ind_indices);
    ind_sort := fu oib.(ind_sort);
    ind_type := f oib.(ind_type);
    ind_kelim := oib.(ind_kelim);
    ind_ctors := List.map (map_constructor_body' f) oib.(ind_ctors);
    ind_projs := List.map (map_projection_body 0 (fun _ => f)) oib.(ind_projs);
    ind_relevance := oib.(ind_relevance) |}.

Global Instance subst_instance_inductive_body : UnivSubst one_inductive_body
  := fun u => map_one_inductive_body' (subst_instance u) (subst_instance u).

Definition map_mutual_inductive_body' fu f mib :=
  {| ind_finite := mib.(ind_finite);
     ind_npars := mib.(ind_npars);
     ind_params := map_context f mib.(ind_params);
     ind_bodies := List.map (map_one_inductive_body' fu f) mib.(ind_bodies);
     ind_universes := mib.(ind_universes);
     ind_variance := mib.(ind_variance) |}.

Global Instance subst_instance_mutual_inductive_body : UnivSubst mutual_inductive_body
  := fun u => map_mutual_inductive_body' (subst_instance u) (subst_instance u).

Lemma subst_instance_cstr_args u cdecl :
  cstr_args (subst_instance u cdecl) =
  subst_instance u (cstr_args cdecl).
Proof. reflexivity. Qed.

Lemma map_fold_context_k {term term' term''} (f : term' -> term) (g : nat -> term'' -> term') (Γ : list (BasicAst.context_decl term'')) :
  map_context f (fold_context_k g Γ) = fold_context_k (fun i => f ∘ (g i)) Γ.
Proof.
  now rewrite /map_context map_fold_context_k.
Qed.

Lemma subst_instance_subst_context u s k ctx :
  subst_instance u (subst_context s k ctx) =
  subst_context (subst_instance u s) k (subst_instance u ctx).
Proof.
  rewrite /subst_instance /= /subst_instance /subst_instance_context map_fold_context_k.
  rewrite /subst_context fold_context_k_map.
  apply fold_context_k_ext => i t.
  now rewrite -subst_instance_subst.
Qed.

Lemma subst_instance_subst_telescope u s k ctx :
  subst_instance u (subst_telescope s k ctx) =
  subst_telescope (subst_instance u s) k (subst_instance u ctx).
Proof.
  rewrite /subst_instance /= /subst_instance /subst_instance_context /= /subst_telescope /=
    /map_context map_mapi mapi_map.
  apply mapi_ext => i t.
  rewrite !compose_map_decl; apply map_decl_ext => t'.
  now rewrite -subst_instance_subst.
Qed.

Lemma subst_instance_lift_context u n k ctx :
  subst_instance u (lift_context n k ctx) =
  lift_context n k (subst_instance u ctx).
Proof.
  rewrite /subst_instance /= /subst_instance_context map_fold_context_k.
  rewrite /lift_context fold_context_k_map.
  apply fold_context_k_ext => i t.
  now rewrite subst_instance_lift.
Qed.

Lemma subst_instance_inds u0 ind u bodies :
  subst_instance u0 (inds ind u bodies)
  = inds ind (subst_instance u0 u) bodies.
Proof.
  unfold inds.
  induction #|bodies|; cbnr.
  f_equal. apply IHn.
Qed.

#[global] Hint Rewrite subst_instance_subst_context subst_instance_lift_context
  subst_instance_lift subst_instance_mkApps
  subst_instance_subst
  subst_instance_it_mkProd_or_LetIn
  subst_instance_it_mkLambda_or_LetIn
  subst_instance_inds
  : substu.
Ltac substu := autorewrite with substu.

Lemma inst_case_context_subst_instance pars puinst ctx u :
  subst_instance u (inst_case_context pars puinst ctx) =
  inst_case_context (subst_instance u pars) (subst_instance u puinst) ctx.
Proof.
  rewrite /inst_case_context; substu.
  rewrite [subst_instance _ _]map_rev.
  now rewrite subst_instance_two_context.
Qed.

Lemma inst_case_predicate_context_subst_instance p u :
  subst_instance u (inst_case_predicate_context p) =
  inst_case_predicate_context (subst_instance u p).
Proof.
  now rewrite /inst_case_predicate_context inst_case_context_subst_instance; cbn.
Qed.

Lemma inst_case_branch_context_subst_instance p br u :
  subst_instance u (inst_case_branch_context p br) =
  inst_case_branch_context (subst_instance u p) (map_branch (subst_instance u) id br).
Proof.
  now rewrite /inst_case_branch_context inst_case_context_subst_instance.
Qed.

Lemma iota_red_subst_instance pars p args br u :
  subst_instance u (iota_red pars p args br)
  = iota_red pars (subst_instance u p) (List.map (subst_instance u) args) (map_branch (subst_instance u) id br).
Proof.
  unfold iota_red.
  rewrite subst_instance_subst -map_skipn -map_rev.
  f_equal. rewrite expand_lets_subst_instance. f_equal.
  now rewrite inst_case_branch_context_subst_instance.
Qed.

Lemma map_map2 {A B C D} (f : A -> B) (g : C -> D -> A) (l : list C) (l' : list D) :
  List.map f (map2 g l l') =
  map2 (fun (x : C) (y : D) => f (g x y)) l l'.
Proof.
  induction l in l' |- *; destruct l'; simpl; auto.
  * cbn. now f_equal.
Qed.

Lemma map2_map_r {A B C D} (f : B -> C) (g : A -> C -> D) (l : list A) (l' : list B) :
  map2 g l (List.map f l') =
  map2 (fun x y => g x (f y)) l l'.
Proof.
  induction l in l' |- *; destruct l'; simpl; auto.
  * cbn. now f_equal.
Qed.

Lemma map2_set_binder_name_map bctx f Γ :
  map2 set_binder_name bctx (map_context f Γ) =
  map_context f (map2 set_binder_name bctx Γ).
Proof.
  now rewrite /map_context map_map2 map2_map_r.
Qed.

Lemma subst_instance_case_branch_context ind mdecl u p bctx cdecl :
  subst_instance u (case_branch_context ind mdecl p bctx cdecl) =
  case_branch_context ind mdecl (subst_instance u p) bctx cdecl.
Proof.
  unfold case_branch_context, case_branch_context_gen.
  cbn -[fold_context_k].
  substu => /=; len.
  rewrite /pre_case_branch_context_gen -inst_case_context_subst_instance.
  now rewrite -[subst_instance _ _]map2_set_binder_name_map.
Qed.

Lemma subst_instance_case_predicate_context ind mdecl idecl p u :
  subst_instance u (case_predicate_context ind mdecl idecl p) =
  case_predicate_context ind mdecl idecl (subst_instance u p).
Proof.
  unfold case_predicate_context, case_predicate_context_gen.
  cbn -[fold_context_k].
  substu => /=; len.
  rewrite /pre_case_predicate_context_gen -inst_case_context_subst_instance.
  now rewrite -[subst_instance _ _]map2_set_binder_name_map.
Qed.

Lemma subst_instance_to_extended_list u l
  : List.map (subst_instance u) (to_extended_list l)
    = to_extended_list (subst_instance u l).
Proof.
  - unfold to_extended_list, to_extended_list_k.
    change [] with (List.map (subst_instance u) (@nil term)) at 2.
    unf_term. generalize (@nil term), 0. induction l as [|[aa [ab|] ac] bb].
    + reflexivity.
    + intros l n; cbn. now rewrite IHbb.
    + intros l n; cbn. now rewrite IHbb.
Qed.

Lemma to_extended_list_subst_instance u l
  : to_extended_list (subst_instance u l) = to_extended_list l.
Proof.
  - unfold to_extended_list, to_extended_list_k.
    unf_term. generalize (@nil term), 0. induction l as [|[aa [ab|] ac] bb].
    + reflexivity.
    + intros l n; cbn. now rewrite IHbb.
    + intros l n; cbn. now rewrite IHbb.
Qed.

Lemma subst_instance_expand_lets u Γ t :
  subst_instance u (expand_lets Γ t) =
  expand_lets (subst_instance u Γ) (subst_instance u t).
Proof.
  rewrite /expand_lets /expand_lets_k.
  rewrite subst_instance_subst.
  rewrite subst_instance_extended_subst.
  f_equal.
  rewrite subst_instance_lift. len; f_equal.
Qed.

#[global] Hint Rewrite subst_instance_expand_lets closedn_subst_instance : substu.

Lemma subst_instance_expand_lets_ctx u Γ Δ :
  subst_instance u (expand_lets_ctx Γ Δ) =
  (expand_lets_ctx (subst_instance u Γ) (subst_instance u Δ)).
Proof.
  now rewrite /expand_lets_ctx /expand_lets_k_ctx; substu; len.
Qed.
#[global] Hint Rewrite subst_instance_expand_lets_ctx : substu.

Lemma forget_types_subst_instance l ctx :
  forget_types (subst_instance l ctx) = forget_types ctx.
Proof.
  now rewrite /forget_types map_map_compose /=.
Qed.

Lemma subst_instance_case_branch_type {cf : checker_flags} {Σ} {wfΣ : wf Σ} u (ci : case_info) mdecl idecl p predctx br i cdecl :
  let ptm :=
    it_mkLambda_or_LetIn predctx (preturn p)
  in
  let p' := subst_instance u p in
  let ptm' :=
    it_mkLambda_or_LetIn
      (subst_instance u predctx)
      (preturn p') in
  case_branch_type ci mdecl idecl
     (subst_instance u p)
     (map_branch (subst_instance u) id br)
     ptm' i cdecl =
  map_pair (subst_instance u) (subst_instance u)
  (case_branch_type ci mdecl idecl p br ptm i cdecl).
Proof.
  intros ptm p' ptm'.
  rewrite /case_branch_type /case_branch_type_gen /map_pair /=.
  rewrite subst_instance_case_branch_context //.
  f_equal; substu.
  f_equal.
  rewrite map_app. f_equal.
  + rewrite !map_map_compose. apply map_ext => x.
    substu.
    rewrite [subst_instance u (List.rev _)]map_rev. f_equal.
    rewrite /expand_lets_k. len.
    rewrite ?subst_instance_two ?subst_instance_two_context //.
  + simpl. f_equal.
    substu. rewrite map_app /= //.
    rewrite subst_instance_to_extended_list to_extended_list_subst_instance.
    do 2 f_equal.
    rewrite !map_map_compose. now setoid_rewrite <-subst_instance_lift.
Qed.

Lemma subst_instance_wf_predicate u mdecl idecl p :
  wf_predicate mdecl idecl p ->
  wf_predicate mdecl idecl (subst_instance u p).
Proof.
  intros []. split.
  - now len.
  - simpl. assumption.
Qed.

Lemma subst_instance_wf_branch u cdecl br :
  wf_branch cdecl br ->
  wf_branch cdecl (map_branch (subst_instance u) id br).
Proof.
  now unfold wf_branch, wf_branch_gen.
Qed.

Lemma subst_instance_wf_branches cdecl u brs :
  wf_branches cdecl brs ->
  wf_branches cdecl (List.map (map_branch (subst_instance u) id) brs).
Proof.
  unfold wf_branches, wf_branches_gen.
  intros h. solve_all.
Qed.
#[global] Hint Resolve subst_instance_wf_predicate
  subst_instance_wf_branch subst_instance_wf_branches : pcuic.

Lemma subst_instance_predicate_set_pparams u p params :
  subst_instance u (set_pparams p params) =
  set_pparams (subst_instance u p) (List.map (subst_instance u) params).
Proof. reflexivity. Qed.

(* Lemma subst_instance_predicate_set_pcontext u p pcontext :
  subst_instance u (set_pcontext p pcontext) =
  set_pcontext (subst_instance u p) (subst_instance u pcontext).
Proof. reflexivity. Qed. *)

Lemma subst_instance_predicate_set_preturn u p pret :
  subst_instance u (set_preturn p pret) =
  set_preturn (subst_instance u p) (subst_instance u pret).
Proof. reflexivity. Qed.

Lemma red1_subst_instance Σ Γ u s t :
  red1 Σ Γ s t ->
  red1 Σ (subst_instance u Γ)
       (subst_instance u s) (subst_instance u t).
Proof.
  intros X0. pose proof I as X.
  intros. induction X0 using red1_ind_all.
  all: try (cbn; econstructor; eauto; fail).
  - cbn. rewrite subst_instance_subst. econstructor.
  - cbn. rewrite subst_instance_subst. econstructor.
  - cbn. rewrite subst_instance_lift. econstructor.
    unfold subst_instance.
    unfold option_map in *. destruct (nth_error Γ) eqn:E; inversion H.
    unfold map_context. rewrite nth_error_map E. cbn.
    rewrite map_decl_body. destruct c. cbn in H1. subst.
    reflexivity.
  - cbn. rewrite subst_instance_mkApps. cbn.
    rewrite iota_red_subst_instance.
    change (bcontext br) with (bcotext (map_branch (subst_instance u) br)).
    eapply red_iota; eauto with pcuic.
    * rewrite nth_error_map H //.
    * simpl. now len.
  - cbn. rewrite !subst_instance_mkApps. cbn.
    econstructor.
    + unfold unfold_fix in *. destruct (nth_error mfix idx) eqn:E.
      * inversion H.
        rewrite nth_error_map E. cbn.
        destruct d. cbn in *. cbn in *; try congruence.
        f_equal. f_equal.
        now rewrite subst_instance_subst fix_subst_instance_subst.
      * inversion H.
    + unfold is_constructor in *.
      destruct (nth_error args narg) eqn:E; inversion H0; clear H0.
      rewrite nth_error_map E. cbn.
      eapply isConstruct_app_subst_instance.
  - cbn. rewrite !subst_instance_mkApps.
    unfold unfold_cofix in *. destruct (nth_error mfix idx) eqn:E.
    + inversion H.
      econstructor. fold subst_instance_constr.
      unfold unfold_cofix.
      rewrite nth_error_map E. cbn.
      rewrite subst_instance_subst.
      now rewrite cofix_subst_instance_subst.
    + cbn.
      inversion H.
  - cbn. unfold unfold_cofix in *.
    destruct nth_error eqn:E; inversion H.
    rewrite !subst_instance_mkApps.
    econstructor. fold subst_instance.
    unfold unfold_cofix.
    rewrite nth_error_map. destruct nth_error; cbn.
    1: rewrite subst_instance_subst cofix_subst_instance_subst.
    all: now inversion E.
  - cbn. rewrite subst_instance_two. econstructor; eauto.
  - cbn. rewrite !subst_instance_mkApps.
    econstructor. now rewrite nth_error_map H.
  - cbn.
    rewrite [map_predicate _ _ _ _ (set_pparams _ _)]subst_instance_predicate_set_pparams.
    econstructor; eauto.
    eapply OnOne2_map. eapply OnOne2_impl. 1: eassumption.
    (* Used to be pcuicfo *)
    simpl in *; intuition; simpl in *.
  - cbn.
    rewrite [map_predicate _ _ _ _ (set_preturn _ _)]subst_instance_predicate_set_preturn.
    eapply case_red_return; eauto with pcuic.
    rewrite subst_instance_app in IHX0.
    now rewrite -inst_case_predicate_context_subst_instance.
  - cbn. econstructor; eauto with pcuic.
    * eapply OnOne2_map. eapply OnOne2_impl; [eassumption | pcuicfo];
      unfold on_Trel; simpl; intuition eauto.
      rewrite /map_branch /id.
      now rewrite subst_instance_app inst_case_branch_context_subst_instance in b0.
  - cbn; econstructor;
      eapply OnOne2_map; eapply OnOne2_impl; [ eassumption | ].
    intros. destruct X1. now red.
  - cbn. eapply fix_red_ty.
      eapply OnOne2_map; eapply OnOne2_impl; [ eassumption | ].
    intros. destruct X1. destruct p. inversion e. destruct x, y; cbn in *; subst.
    red. split; cbn; eauto.
  - cbn. eapply fix_red_body.
    eapply OnOne2_map; eapply OnOne2_impl; [ eassumption | ].
    intros. destruct X1. destruct p. inversion e. destruct x, y; cbn in *; subst.
    red; split; cbn; eauto.
    rewrite subst_instance_app in r0.
    now rewrite -(fix_context_subst_instance u mfix0).
  - cbn; econstructor;
      eapply OnOne2_map; eapply OnOne2_impl; [ eassumption | ].
    intros. destruct X1. destruct p. inversion e. destruct x, y; cbn in *; subst.
    red. split; cbn; eauto.
  - cbn. eapply cofix_red_body.
      eapply OnOne2_map; eapply OnOne2_impl; [ eassumption | ].
    intros. destruct X1. destruct p. inversion e. destruct x, y; cbn in *; subst.
    red. split; cbn; eauto.
    rewrite subst_instance_app in r0.
    now rewrite <- (fix_context_subst_instance u mfix0).
Qed.

Lemma subst_instance_ws_cumul_pb {cf : checker_flags} (Σ : global_env_ext) Γ u A B univs :
valid_constraints (global_ext_constraints (Σ.1, univs))
                  (subst_instance_cstrs u Σ) ->
  Σ ;;; Γ |- A = B ->
  (Σ.1,univs) ;;; subst_instance u Γ |- subst_instance u A = subst_instance u B.
Proof.
  intros HH X0. induction X0.
  - econstructor.
    eapply eq_term_subst_instance; tea.
  - econstructor 2. 1: eapply red1_subst_instance; cbn; eauto. eauto.
  - econstructor 3. 1: eauto. eapply red1_subst_instance; cbn; eauto.
Qed.

Lemma cumul_subst_instance {cf : checker_flags} (Σ : global_env_ext) Γ u A B univs :
  valid_constraints (global_ext_constraints (Σ.1, univs))
                    (subst_instance_cstrs u Σ) ->
  Σ ;;; Γ |- A <= B ->
  (Σ.1,univs) ;;; subst_instance u Γ
                   |- subst_instance u A <= subst_instance u B.
Proof.
  intros HH X0. induction X0.
  - econstructor.
    eapply leq_term_subst_instance; tea.
  - econstructor 2. 1: eapply red1_subst_instance; cbn; eauto. eauto.
  - econstructor 3. 1: eauto. eapply red1_subst_instance; cbn; eauto.
Qed.

Lemma is_allowed_elimination_subst_instance {cf : checker_flags} (Σ : global_env_ext) univs inst u al :
  valid_constraints (global_ext_constraints (Σ.1, univs))
                    (subst_instance_cstrs inst Σ) ->
  is_allowed_elimination Σ al u ->
  is_allowed_elimination (global_ext_constraints (Σ.1, univs)) al (subst_instance_univ inst u).
Proof.
  destruct al, u as [| | u]; trivial.
  intros val [H|isal]; [cbn in H; discriminate | right].
  unfold_univ_rel eqn:H.
  eapply satisfies_subst_instance in Hv; eauto.
  specialize (isal _ Hv).
  rewrite subst_instance_univ0_val'; auto.
Qed.

Global Instance compare_decl_subst_instance {cf : checker_flags} pb Σ : SubstUnivPreserved (compare_decl pb Σ).
Proof.
  intros φ1 φ2 u HH ? ? [] => /=; constructor; auto;
   eapply compare_term_subst_instance; tea.
Qed.

Global Instance compare_context_subst_instance {cf : checker_flags} pb Σ : SubstUnivPreserved (compare_context pb Σ).
Proof.
  intros φ φ' u HH Γ Γ' X. eapply All2_fold_map, All2_fold_impl; tea.
  intros. eapply compare_decl_subst_instance; eassumption.
Qed.

Lemma subst_instance_destArity Γ A u :
  destArity (subst_instance u Γ) (subst_instance u A)
  = match destArity Γ A with
    | Some (ctx, s) => Some (subst_instance u ctx, subst_instance_univ u s)
    | None => None
    end.
Proof.
  induction A in Γ |- *; simpl; try reflexivity.
  - change (subst_instance u Γ,, vass na (subst_instance_constr u A1))
      with (subst_instance u (Γ ,, vass na A1)).
    now rewrite IHA2.
  - change (subst_instance u Γ ,,
               vdef na (subst_instance_constr u A1) (subst_instance_constr u A2))
      with (subst_instance u (Γ ,, vdef na A1 A2)).
    now rewrite IHA3.
Qed.

Lemma subst_instance_decompose_prod_assum u Γ t :
  subst_instance u (decompose_prod_assum Γ t)
  = decompose_prod_assum (subst_instance u Γ) (subst_instance u t).
Proof.
  induction t in Γ |- *; cbnr.
  - apply IHt2.
  - apply IHt3.
Qed.

Lemma subst_instance_decompose_app_rec u Γ t
  : subst_instance u (decompose_app_rec t Γ)
    = decompose_app_rec (subst_instance u t) (subst_instance u Γ).
Proof.
  induction t in Γ |- *; cbnr.
  now rewrite IHt1.
Qed.

Lemma subst_instance_decompose_app u t
  : subst_instance u (decompose_app t) = decompose_app (subst_instance u t).
Proof.
  unfold decompose_app. now rewrite (subst_instance_decompose_app_rec u []).
Qed.

Lemma subst_instance_smash u Γ Δ :
  subst_instance u (smash_context Δ Γ) =
  smash_context (subst_instance u Δ) (subst_instance u Γ).
Proof.
  induction Γ as [|[? [] ?] ?] in Δ |- *; simpl; auto.
  - rewrite IHΓ. f_equal.
    now rewrite subst_instance_subst_context.
  - rewrite IHΓ subst_instance_app; trivial.
Qed.

Lemma destInd_subst_instance u t :
  destInd (subst_instance u t) = option_map (fun '(i, u') => (i, subst_instance u u')) (destInd t).
Proof.
  destruct t; simpl; try congruence.
  f_equal.
Qed.

Lemma subst_instance_check_one_fix u mfix :
  List.map
        (fun x : def term =>
        check_one_fix (map_def (subst_instance u) (subst_instance u) x)) mfix =
  List.map check_one_fix mfix.
Proof.
  apply map_ext. intros [na ty def rarg]; simpl.
  rewrite decompose_prod_assum_ctx.
  destruct (decompose_prod_assum _ ty) eqn:decomp.
  rewrite decompose_prod_assum_ctx in decomp.
  erewrite <-(subst_instance_decompose_prod_assum u []).
  destruct (decompose_prod_assum [] ty) eqn:decty.
  rewrite app_context_nil_l in decomp.
  injection decomp. intros -> ->. clear decomp.
  simpl. rewrite !app_context_nil_l -(subst_instance_smash u _ []).
  unfold subst_instance, map_context.
  rewrite <- map_rev. rewrite nth_error_map.
  destruct nth_error as [d|] eqn:Hnth; simpl; auto.
  rewrite <- subst_instance_decompose_app.
  destruct (decompose_app (decl_type d)) eqn:Happ.
  simpl.
  rewrite destInd_subst_instance.
  destruct destInd as [[i u']|]; simpl; auto.
Qed.

Lemma subst_instance_check_one_cofix u mfix :
  List.map
        (fun x : def term =>
        check_one_cofix (map_def (subst_instance u) (subst_instance u) x)) mfix =
  List.map check_one_cofix mfix.
Proof.
  apply map_ext. intros [na ty def rarg]; simpl.
  rewrite decompose_prod_assum_ctx.
  destruct (decompose_prod_assum _ ty) eqn:decomp.
  rewrite decompose_prod_assum_ctx in decomp.
  rewrite <- (subst_instance_decompose_prod_assum _ []).
  destruct (decompose_prod_assum [] ty) eqn:decty.
  rewrite app_context_nil_l in decomp.
  injection decomp; intros -> ->; clear decomp.
  simpl.
  destruct (decompose_app t) eqn:Happ.
  rewrite <- subst_instance_decompose_app, Happ. simpl.
  rewrite destInd_subst_instance.
  destruct destInd as [[i u']|]; simpl; auto.
Qed.

Lemma All_local_env_over_subst_instance {cf : checker_flags} Σ Γ (wfΓ : wf_local Σ Γ) :
  All_local_env_over typing
                     (fun Σ0 Γ0 (_ : wf_local Σ0 Γ0) t T (_ : Σ0;;; Γ0 |- t : T) =>
       forall u univs, wf_ext_wk Σ0 ->
                  consistent_instance_ext (Σ0.1, univs) Σ0.2 u ->
                  (Σ0.1, univs) ;;; subst_instance u Γ0
                  |- subst_instance u t : subst_instance u T)
                     Σ Γ wfΓ ->
  forall u univs,
    wf_ext_wk Σ ->
    consistent_instance_ext (Σ.1, univs) Σ.2 u ->
    wf_local (Σ.1, univs) (subst_instance u Γ).
Proof.
  induction 1; simpl; rewrite /subst_instance /=; constructor; cbn in *; auto.
  all: eapply infer_typing_sort_impl with _ tu; cbn in *; eauto.
Qed.

#[global] Hint Resolve All_local_env_over_subst_instance : univ_subst.

Lemma in_var_global_ext {cf : checker_flags} n Σ :
  wf Σ.1 ->
  LevelSet.In (Level.Var n) (global_ext_levels Σ) ->
  LevelSet.In (Level.Var n) (levels_of_udecl Σ.2).
Proof.
  intros wfΣ Hin.
  eapply LevelSet.union_spec in Hin.
  destruct Hin; auto.
  eapply not_var_global_levels in wfΣ.
  specialize (wfΣ (Level.Var n) H).
  now simpl in wfΣ.
Qed.

Lemma monomorphic_level_in_global_ext l Σ :
  LevelSet.In (Level.Level l) (global_ext_levels Σ) ->
  LevelSet.In (Level.Level l) (global_levels Σ).
Proof.
  unfold global_ext_levels.
  intros [hin|hin] % LevelSet.union_spec.
  - now eapply monomorphic_level_notin_levels_of_udecl in hin.
  - apply hin.
Qed.

Lemma wf_universe_subst_instance {cf : checker_flags} (Σ : global_env_ext) univs u s :
   wf Σ ->
   wf_universe Σ s ->
   consistent_instance_ext (Σ.1, univs) Σ.2 u ->
   wf_universe (Σ.1, univs) (subst_instance u s).
Proof.
  destruct s as [| | t]; cbnr.
  intros wfΣ Hl Hu e [[l n] [inl ->]]%In_subst_instance.
  destruct l as [|s|n']; simpl; auto.
  - apply global_ext_levels_InSet.
  - specialize (Hl (Level.Level s, n) inl).
    simpl in Hl. apply monomorphic_level_in_global_ext in Hl.
    eapply LS.union_spec. now right.
  - specialize (Hl (Level.Var n', n) inl).
    eapply LS.union_spec in Hl as [Hl|Hl].
    + red in Hu.
      unfold levels_of_udecl in Hl.
      destruct Σ.2.
      * simpl in Hu.
        destruct u; try discriminate. lsets.
      * destruct Hu as [declu [us vc]].
        unfold subst_instance. simpl.
        destruct (nth_error u n') eqn:hnth.
        2: simpl; apply global_ext_levels_InSet.
        eapply forallb_Forall in declu.
        eapply nth_error_forall in declu; eauto.
        simpl in declu. now eapply LS.mem_spec in declu.
    + now apply not_var_global_levels in Hl.
Qed.

Definition global_context_set Σ : ContextSet.t := universes Σ.

Lemma global_context_set_sub_ext Σ φ :
  sub_context_set (global_context_set Σ) (global_ext_context_set (Σ, φ)).
Proof.
  split.
  - cbn. unfold global_ext_levels. cbn.
    unfold global_levels.
    intros x hin. apply LevelSet.union_spec; right.
    now apply LevelSet.union_spec; left.
  - apply ConstraintSetProp.union_subset_2.
Qed.

Definition wf_global_ext {cf : checker_flags} Σ ext := wf_ext_wk (Σ, ext).

Require Import Morphisms.
Require Import ssreflect.
Set SimplIsCbn.

Section SubstIdentity.
  Context `{cf:checker_flags}.

  Lemma subst_instance_id_mdecl Σ u mdecl :
    consistent_instance_ext Σ (ind_universes mdecl) u ->
    subst_instance u (abstract_instance (ind_universes mdecl)) = u.
  Proof using Type.
    intros cu.
    red in cu. red in cu.
    destruct (ind_universes mdecl) eqn:eqi.
    - destruct u; simpl in cu; try discriminate.
      reflexivity.
    - simpl. destruct cst as [univs csts]. simpl.
      rewrite map_mapi. simpl. simpl in cu.
      destruct cu as [Hu [sizeu vu]].
      now rewrite mapi_nth.
  Qed.

  Lemma declared_inductive_wf_ext_wk Σ mdecl mind :
    wf Σ ->
    declared_minductive Σ mind mdecl ->
    wf_ext_wk (Σ, ind_universes mdecl).
  Proof using Type.
    intros wfΣ decli.
    epose proof (weaken_lookup_on_global_env' _ _ (InductiveDecl mdecl) wfΣ decli); eauto.
    red. simpl. split; auto.
  Qed.

  Lemma declared_inductive_wf_global_ext Σ mdecl mind :
    wf Σ ->
    declared_minductive Σ mind mdecl ->
    wf_global_ext Σ (ind_universes mdecl).
  Proof using Type.
    intros wfΣ decli.
    split; auto.
    epose proof (weaken_lookup_on_global_env' _ _ (InductiveDecl mdecl) wfΣ decli); eauto.
  Qed.

  Hint Resolve declared_inductive_wf_ext_wk declared_inductive_wf_global_ext : pcuic.

  Lemma subst_instance_level_abs l n Σ :
    wf Σ ->
    LevelSet.In l (LevelSet.union
     (fold_right LevelSet.add LevelSet.empty
        (unfold n Level.Var)) (global_levels Σ)) ->
    subst_instance_level (unfold n Level.Var) l = l.
  Proof using Type.
    intros wfΣ lin.
    eapply LevelSet.union_spec in lin.
    destruct lin.
    - apply LevelSet_In_fold_right_add in H.
      destruct l; simpl; auto.
      eapply In_unfold_inj in H; [|congruence].
      pose proof (proj1 (nth_error_unfold Level.Var n n0) H).
      now rewrite (nth_error_nth _ _ _ H0).
    - eapply not_var_global_levels in wfΣ.
      specialize (wfΣ l H). simpl in wfΣ.
      destruct l => //.
  Qed.

  Lemma consistent_instance_ext_abstract_instance Σ udecl :
    wf Σ ->
    wf_global_ext Σ udecl ->
    consistent_instance_ext (Σ, udecl) udecl (abstract_instance udecl).
  Proof using Type.
    intros wfΣ wf_glob_ext.
    red. red.
    destruct udecl as [|[univs cst]] eqn:indu.
    { simpl. reflexivity. }
    split; [|split].
    - simpl abstract_instance.
      eapply forallb_mapi => //.
      intros i Hi. unfold global_ext_levels.
      apply LevelSet.mem_spec, LevelSet.union_spec. left.
      unfold levels_of_udecl. simpl.
      rewrite (mapi_unfold Level.Var).
      eapply LevelSet_In_fold_right_add.
      induction #|univs| in i, Hi |- *; try lia.
      simpl. eapply in_or_app. destruct (eq_dec i n).
      * subst. right; simpl; auto.
      * left; apply IHn; lia.
    - now rewrite mapi_length.
    - simpl. rewrite (mapi_unfold Level.Var).
      assert(CS.Equal (subst_instance_cstrs (unfold #|univs| Level.Var) cst) cst).
      { unfold CS.Equal; intros a.
        unfold subst_instance_cstrs.
        red in wf_glob_ext.
        destruct wf_glob_ext as [_ wfext].
        unfold on_udecl_prop in wfext.
        simpl constraints_of_udecl in wfext.
        simpl levels_of_udecl in wfext.
        rewrite (mapi_unfold Level.Var) in wfext.
        clear indu.
        simpl fst in wfext.
        revert wfext.
        eapply ConstraintSetProp.fold_rec_weak; auto.
        2:reflexivity.
        * intros s s' a' eqs H.
          intros Hf.
          rewrite <- eqs in Hf. rewrite -eqs; auto.
        * intros x a0 s nin equiv.
          intros cadd.
          eapply CS_For_all_add in cadd as [cadd Ps].
          specialize (equiv Ps). clear Ps.
          destruct x as [[l c] r]. destruct cadd as [inl inr].
          unfold subst_instance_cstr. simpl.
          eapply subst_instance_level_abs in inl; auto.
          eapply subst_instance_level_abs in inr; auto.
          rewrite inl inr.
          rewrite !CS.add_spec.
          intuition auto. }
      unfold valid_constraints. destruct check_univs; auto.
      unfold valid_constraints0. simpl.
      unfold satisfies.
      intros v. rewrite H.
      eapply CS_For_all_union.
  Qed.

  Lemma udecl_prop_in_var_poly {Σ n} : on_udecl_prop Σ.1 Σ.2 -> LevelSet.In (Level.Var n) (levels_of_udecl Σ.2) ->
    ∑ ctx, Σ.2 = Polymorphic_ctx ctx.
  Proof using cf.
    intros onu lin.
    destruct (Σ.2); intuition eauto.
    simpl in lin, onu. lsets.
  Qed.

  Lemma consistent_instance_ext_subst_abs Σ decl u :
    wf_ext_wk Σ ->
    consistent_instance_ext Σ decl u ->
    subst_instance (abstract_instance Σ.2) u = u.
  Proof using Type.
    intros [wfΣ onu] cu.
    destruct decl.
    - simpl in cu. destruct u; simpl in *; try discriminate; auto.
    - destruct cu as [decl' [sizeu vc]].
      clear sizeu vc.
      induction u; simpl; auto.
      move/andb_and: decl' => [ina au]. specialize (IHu au).
      rewrite [List.map _ u]IHu. f_equal. clear au.
      destruct a; simpl; auto.
      eapply LevelSet.mem_spec in ina.
      eapply in_var_global_ext in ina; auto.
      destruct (udecl_prop_in_var_poly onu ina) as [[univs csts] eq].
      rewrite eq in IHu, ina |- *. simpl in *.
      rewrite mapi_unfold in IHu, ina |- *.
      eapply LevelSet_In_fold_right_add in ina.
      eapply In_unfold_inj in ina; try congruence.
      eapply (nth_error_unfold Level.Var) in ina.
      now rewrite (nth_error_nth _ _ _ ina).
  Qed.

  Lemma in_global_ext_subst_abs_level Σ l :
    wf_ext_wk Σ ->
    LevelSet.In (LevelExpr.get_level l) (global_ext_levels Σ) ->
    subst_instance (abstract_instance Σ.2) l = l.
  Proof using Type.
    intros [wfΣ onu] cu.
    destruct l; auto.
    destruct t; auto.
    eapply in_var_global_ext in cu; eauto.
    eapply udecl_prop_in_var_poly in onu as [[ctx cstrs] eq]; eauto.
    rewrite eq. simpl.
    rewrite eq in cu. simpl in cu.
    apply LevelSet_In_fold_right_add in cu.
    unfold AUContext.repr in *. rewrite (mapi_unfold Level.Var) in cu |- *.
    destruct nth_error eqn:hnth.
    * apply nth_error_unfold_inv in hnth. subst; auto.
    * apply nth_error_None in hnth. rewrite unfold_length in hnth.
      apply In_unfold_inj in cu; try lia. congruence.
  Qed.

  Lemma consistent_instance_ext_subst_abs_univ Σ u :
    wf_ext_wk Σ ->
    wf_universe Σ u ->
    subst_instance_univ (abstract_instance Σ.2) u = u.
  Proof using Type.
    intros wf cu.
    destruct u; simpl; auto. f_equal.
    apply eq_univ'.
    simpl in cu.
    intros l.
    rewrite In_subst_instance.
    split.
    - intros [x [inx ->]].
      specialize (cu _ inx).
      unfold subst_instance.
      apply in_global_ext_subst_abs_level in cu; eauto.
      unfold subst_instance in cu. now rewrite cu.
    - intros inl.
      specialize (cu _ inl). exists l; split; auto.
      now rewrite in_global_ext_subst_abs_level.
  Qed.

  Lemma consistent_instance_ext_subst_abs_inds Σ decl ind u bodies :
    wf_ext_wk Σ ->
    consistent_instance_ext Σ decl u ->
    subst_instance (abstract_instance Σ.2) (inds ind u bodies) =
      (inds ind u bodies).
  Proof using Type.
    intros wf cu.
    unfold inds. generalize #|bodies|.
    induction n; simpl; auto. rewrite IHn; f_equal.
    now rewrite [subst_instance_instance _ _](consistent_instance_ext_subst_abs _ _ _ wf cu).
  Qed.

  Lemma wf_universe_type1 Σ : wf_universe Σ Universe.type1.
  Proof using Type.
    simpl.
    intros l hin%LevelExprSet.singleton_spec.
    subst l. simpl.
    apply global_ext_levels_InSet.
  Qed.

  Lemma wf_universe_super {Σ u} : wf_universe Σ u -> wf_universe Σ (Universe.super u).
  Proof using Type.
    destruct u; cbn.
    1-2:intros _ l hin%LevelExprSet.singleton_spec; subst l; apply wf_universe_type1;
     now apply LevelExprSet.singleton_spec.
    intros Hl.
    intros l hin.
    eapply Universes.spec_map_succ in hin as [x' [int ->]].
    simpl. now specialize (Hl _ int).
  Qed.

  Lemma app_inj {A} (l l' l0 l0' : list A) :
    #|l| = #|l0| ->
    l ++ l' = l0 ++ l0' ->
    l = l0 /\ l' = l0'.
  Proof using Type.
    induction l in l', l0, l0' |- *; destruct l0; simpl in * => //; auto.
    intros [= eq] [= -> eql].
    now destruct (IHl _ _ _ eq eql).
  Qed.

  Lemma subst_abstract_instance_id :
    env_prop (fun Σ Γ t T =>
        wf_ext_wk Σ ->
        let u := abstract_instance (snd Σ) in
        subst_instance u t = t × subst_instance u T = T)
        (fun Σ Γ =>
        wf_ext_wk Σ ->
        let u := abstract_instance (snd Σ) in
        subst_instance u Γ = Γ).
  Proof using Type.
    eapply typing_ind_env; intros; simpl in *; auto; try ((subst u || subst u0); split; [f_equal|]; intuition eauto).
    1:{ induction X; simpl; auto; unfold snoc.
      * f_equal; auto.
        unfold map_decl. simpl. unfold vass. f_equal. intuition auto.
      * unfold map_decl. simpl. unfold vdef. repeat f_equal; intuition auto. }

    1:{ rewrite subst_instance_lift. f_equal.
      generalize H. rewrite -H1 /subst_instance /= nth_error_map H /= => [=].
      intros Hdecl. now rewrite -{2}Hdecl. }

    all:try (solve [f_equal; eauto; try congruence]).
    all:try (rewrite ?subst_instance_two; f_equal; eapply consistent_instance_ext_subst_abs; eauto).

    - now rewrite consistent_instance_ext_subst_abs_univ.

    - rewrite consistent_instance_ext_subst_abs_univ //.
      now apply wf_universe_super.

    - rewrite product_subst_instance. f_equal;
      intuition eauto; now noconf b0; noconf b1.

    - intuition auto. noconf a; noconf b; noconf b0.
      rewrite subst_instance_subst /= /subst1.
      repeat (f_equal; simpl; auto).

    - rewrite /type_of_constructor subst_instance_subst subst_instance_two.
      erewrite consistent_instance_ext_subst_abs; eauto. f_equal.
      eapply consistent_instance_ext_subst_abs_inds; eauto.

    - solve_all; simpl in *.
      * rewrite subst_instance_mkApps /= /subst_instance /= in b0.
        eapply mkApps_nApp_inj in b0 as [Hi Hpars] => //.
        now noconf Hi.
      * rewrite subst_instance_mkApps /= /subst_instance /= in b0.
        eapply mkApps_nApp_inj in b0 as [Hi Hpars] => //.
        rewrite map_app in Hpars.
        eapply app_inj in Hpars as [Hpars hinds]. 2:now len.
        rewrite -{2}(map_id (pparams p)) in Hpars.
        now apply map_eq_inj in Hpars.

    - solve_all.

    - rewrite subst_instance_mkApps. f_equal.
      * rewrite /ptm.
        rewrite subst_instance_it_mkLambda_or_LetIn.
        rewrite subst_instance_app in H.
        eapply app_inj in H as []; [|now len].
        rewrite H. now f_equal.
      * rewrite map_app.
        rewrite subst_instance_mkApps /= /subst_instance /= in b0.
        eapply mkApps_nApp_inj in b0 as [Hi Hpars] => //.
        rewrite map_app in Hpars.
        eapply app_inj in Hpars as [Hpars hinds]. 2:now len.
        now rewrite hinds /= a0.
    - rewrite subst_instance_subst /=.
      rewrite /subst_instance /=.
      rewrite subst_instance_mkApps in b.
      eapply mkApps_nApp_inj in b as [Hi Hpars] => //.
      f_equal.
      * rewrite a; f_equal.
        rewrite /subst_instance_list. now rewrite map_rev Hpars.
      * rewrite [subst_instance_constr _ _]subst_instance_two.
        noconf Hi. now rewrite [subst_instance _ u]H.
    - solve_all. destruct a as [s [? ?]]; solve_all.
    - clear X0. eapply nth_error_all in X as [s [Hs [IHs _]]]; eauto.
    - solve_all. destruct a as [s [? ?]]. solve_all.
    - clear X0. eapply nth_error_all in X as [s [Hs [IHs _]]]; eauto.
  Qed.

  Lemma typed_subst_abstract_instance Σ Γ t T :
    wf_ext_wk Σ ->
    Σ ;;; Γ |- t : T ->
    let u := abstract_instance Σ.2 in
    subst_instance u t = t.
  Proof using Type.
    intros [wfΣ onu] H. eapply (env_prop_typing subst_abstract_instance_id) in H as [H H']; eauto.
    split; auto.
  Qed.

  Lemma subst_instance_id Σ Γ :
    wf_ext_wk Σ ->
    wf_local Σ Γ ->
    let u := abstract_instance Σ.2 in
    subst_instance u Γ = Γ.
  Proof using Type.
    intros. eapply (env_prop_wf_local subst_abstract_instance_id) in X0; eauto.
  Qed.

End SubstIdentity.
