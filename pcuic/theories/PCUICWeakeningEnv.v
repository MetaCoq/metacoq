(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils.
From Equations Require Import Equations.
From MetaCoq Require Import LibHypsNaming.

Require Import ssreflect.

Set Default Goal Selector "!".
Implicit Types (cf : checker_flags).

Lemma global_ext_constraints_app Σ Σ' φ
  : ConstraintSet.Subset (universes Σ).2 (universes Σ').2 ->
    ConstraintSet.Subset (global_ext_constraints (Σ, φ))
                         (global_ext_constraints (Σ', φ)).
Proof.
  unfold global_ext_constraints; simpl.
  intros sub ctr Hc. apply ConstraintSet.union_spec in Hc.
  apply ConstraintSet.union_spec.
  destruct Hc as [Hc|Hc]; [now left|right]. clear φ.
  unfold global_constraints in Hc.
  apply (sub _ Hc).
Qed.


Ltac my_rename_hyp h th :=
  match th with
  | (extends ?t _) => fresh "ext" t
  | (extends ?t.1 _) => fresh "ext" t
  | (extends _ _) => fresh "ext"
  end.

Ltac rename_hyp h ht ::= my_rename_hyp h ht.

(** * Weakening lemmas w.r.t. the global environment *)

(** ** Constraints *)

Lemma weakening_env_global_ext_levels Σ Σ' φ (H : extends Σ Σ') l
  : LevelSet.In l (global_ext_levels (Σ, φ))
    -> LevelSet.In l (global_ext_levels (Σ', φ)).
Proof.
  unfold global_ext_levels; simpl.
  intros Hl. apply LevelSet.union_spec in Hl.
  apply LevelSet.union_spec.
  destruct Hl as [Hl|Hl]; [now left|right]. clear φ.
  destruct H as [[lsub csub] [Σ'' eq]]; subst.
  apply LevelSet.union_spec in Hl.
  apply LevelSet.union_spec; intuition auto.
Qed.
#[global] Hint Resolve weakening_env_global_ext_levels : extends.

Lemma weakening_env_global_ext_levels' Σ Σ' φ (H : extends Σ Σ') l
  : LevelSet.mem l (global_ext_levels (Σ, φ))
    -> LevelSet.mem l (global_ext_levels (Σ', φ)).
Proof.
  intro HH. apply LevelSet.mem_spec in HH.
  now eapply LevelSet.mem_spec, weakening_env_global_ext_levels.
Qed.

Lemma weakening_env_global_ext_constraints Σ Σ' φ (H : extends Σ Σ')
  : ConstraintSet.Subset (global_ext_constraints (Σ, φ))
                         (global_ext_constraints (Σ', φ)).
Proof.
  destruct H as [sub [Σ'' eq]]. subst.
  apply global_ext_constraints_app, sub.
Qed.

#[global] Instance subrel_extends_cmp {cf} pb (Σ Σ' : global_env) (ϕ : universes_decl) :
  extends Σ Σ' ->
  RelationClasses.subrelation (compare_universe pb (global_ext_constraints (Σ, ϕ)))
    (compare_universe pb (global_ext_constraints (Σ', ϕ))).
Proof.
  intros ext u u'.
  apply cmp_universe_subset.
  apply weakening_env_global_ext_constraints, ext.
Qed.

#[global] Instance subrel_extends_eq_pb {cf} pb (Σ Σ' : global_env) (ϕ : universes_decl) :
  extends Σ Σ' ->
  RelationClasses.subrelation (eq_universe (global_ext_constraints (Σ, ϕ)))
    (compare_universe pb (global_ext_constraints (Σ', ϕ))).
Proof.
  change eq_universe with (compare_universe Conv).
  intros ext.
  destruct pb.
  - tc.
  - transitivity (compare_universe Conv (global_ext_constraints (Σ', ϕ))); tc.
Qed.

#[global] Instance subrel_extends_eq {cf} (Σ Σ' : global_env) (ϕ : universes_decl) :
  extends Σ Σ' ->
  RelationClasses.subrelation (eq_universe (global_ext_constraints (Σ, ϕ)))
    (eq_universe (global_ext_constraints (Σ', ϕ))).
Proof. change eq_universe with (compare_universe Conv). tc. Qed.

#[global] Instance subrel_extends_le {cf} (Σ Σ' : global_env) (ϕ : universes_decl) :
  extends Σ Σ' ->
  RelationClasses.subrelation (leq_universe (global_ext_constraints (Σ, ϕ)))
    (leq_universe (global_ext_constraints (Σ', ϕ))).
Proof. change leq_universe with (compare_universe Cumul). tc. Qed.

#[global] Instance subrel_extends_eq_le {cf} (Σ Σ' : global_env) (ϕ : universes_decl) :
  extends Σ Σ' ->
  RelationClasses.subrelation (eq_universe (global_ext_constraints (Σ, ϕ)))
    (leq_universe (global_ext_constraints (Σ', ϕ))).
Proof. change leq_universe with (compare_universe Cumul). tc. Qed.

Lemma subrelations_extends {cf} Σ Σ' φ :
  extends Σ Σ' ->
  RelationClasses.subrelation (eq_universe (global_ext_constraints (Σ,φ))) (eq_universe (global_ext_constraints (Σ',φ))).
Proof. typeclasses eauto. Qed.

Lemma subrelations_leq_extends {cf} Σ Σ' φ :
  extends Σ Σ' ->
  RelationClasses.subrelation (leq_universe (global_ext_constraints (Σ,φ))) (leq_universe (global_ext_constraints (Σ',φ))).
Proof. typeclasses eauto. Qed.

Lemma subrelations_compare_extends {cf} Σ Σ' pb φ :
  extends Σ Σ' ->
  RelationClasses.subrelation (compare_universe pb (global_ext_constraints (Σ,φ)))
    (compare_universe pb (global_ext_constraints (Σ',φ))).
Proof. destruct pb; typeclasses eauto. Qed.

Lemma subrelations_eq_compare_extends {cf} Σ Σ' pb φ :
  extends Σ Σ' ->
  RelationClasses.subrelation (eq_universe (global_ext_constraints (Σ,φ)))
    (compare_universe pb (global_ext_constraints (Σ',φ))).
Proof. destruct pb; typeclasses eauto. Qed.


Lemma weakening_env_is_allowed_elimination {cf} Σ Σ' φ u allowed :
  extends Σ Σ' ->
  is_allowed_elimination (global_ext_constraints (Σ, φ)) allowed u ->
  is_allowed_elimination (global_ext_constraints (Σ', φ)) allowed u.
Proof.
  destruct allowed; cbnr; trivial.
  intros ext [ | al]; auto.
  destruct u; cbn in *; try elim al.
  right.
  unfold_univ_rel.
  apply al.
  eapply satisfies_subset; eauto.
  apply weakening_env_global_ext_constraints, ext.
Qed.
#[global] Hint Resolve weakening_env_is_allowed_elimination : extends.

Lemma weakening_env_consistent_instance {cf} Σ Σ' φ ctrs u (H : extends Σ Σ')
  : consistent_instance_ext (Σ, φ) ctrs u
    -> consistent_instance_ext (Σ', φ) ctrs u.
Proof.
    unfold consistent_instance_ext, consistent_instance.
    intros X.
    destruct ctrs; tas.
    destruct X as (H0 & H1 & H2); repeat split; tas.
    - eapply forallb_Forall in H0; eapply forallb_Forall, Forall_impl; tea.
      intros x ?; now eapply weakening_env_global_ext_levels'.
    - eapply valid_subset; tea;
      now eapply weakening_env_global_ext_constraints.
Qed.
#[global] Hint Resolve weakening_env_consistent_instance : extends.

Lemma global_levels_union_set Σ :
  LevelSet.Equal (LevelSet.union (LevelSet.singleton Level.lzero) (global_levels Σ))
  (global_levels Σ).
Proof.
  apply LevelSetProp.union_subset_equal.
  intros x hin. eapply LevelSet.singleton_spec in hin; subst x.
  apply global_levels_InSet.
Qed.

Lemma global_levels_sub {univs univs'} : univs ⊂_cs univs' ->
  LevelSet.Subset (global_levels univs) (global_levels univs').
Proof.
  unfold global_levels => sub.
  intros x hin % LevelSet.union_spec.
  apply LevelSet.union_spec.
  intuition auto. left. now apply sub.
Qed.

Lemma extends_wf_universe {Σ : global_env_ext} Σ' u : extends Σ Σ' ->
  wf_universe Σ u -> wf_universe (Σ', Σ.2) u.
Proof.
  destruct Σ as [Σ univ]; cbn.
  intros [sub [Σ'' eq]].
  destruct u; simpl; auto.
  intros Hl.
  intros l inl; specialize (Hl l inl).
  cbn.
  unfold global_ext_levels.
  eapply LevelSet.union_spec; simpl.
  apply LevelSet.union_spec in Hl as [Hl|Hl]; cbn in Hl.
  - simpl. simpl in Hl. now left.
  - right. eapply global_levels_sub; tea.
Qed.




Definition on_udecl_prop (Σ : global_env) (udecl : universes_decl)
  := let levels := levels_of_udecl udecl in
     let global_levels := global_levels Σ.(universes) in
     let all_levels := LevelSet.union levels global_levels in
     ConstraintSet.For_all (declared_cstr_levels all_levels) (constraints_of_udecl udecl).
     (* /\ match udecl with
       | Monomorphic_ctx ctx => LevelSet.for_all (negb ∘ Level.is_var) ctx.1
                               /\ LevelSet.Subset ctx.1 global_levels
                               /\ ConstraintSet.Subset ctx.2 (global_constraints Σ)
                               /\ satisfiable_udecl Σ.(universes) udecl
       | _ => True
       end. *)

Lemma in_global_levels l u :
  LevelSet.In l (ContextSet.levels u) ->
  LevelSet.In l (global_levels u).
Proof.
  intros hin; now apply LevelSet.union_spec.
Qed.

Lemma declared_cstr_levels_sub l l' c :
  LevelSet.Subset l l' ->
  declared_cstr_levels l c -> declared_cstr_levels l' c.
Proof.
  intros sub; unfold declared_cstr_levels.
  destruct c as [[l1 eq] l2]. intuition auto.
Qed.

Lemma on_udecl_on_udecl_prop (Σ : global_env) ctx :
  on_udecl Σ.(universes) (Polymorphic_ctx ctx) -> on_udecl_prop Σ (Polymorphic_ctx ctx).
Proof.
  intros [? [? ?]]. red.
  intros x hin. specialize (H0 x hin).
  eapply declared_cstr_levels_sub; tea.
  intros x' hin'.
  eapply LevelSet.union_spec. apply LevelSet.union_spec in hin'.
  intuition auto.
Qed.



(** ** Lookup *)

Lemma lookup_global_Some_fresh Σ c decl :
  lookup_global Σ c = Some decl -> ~ (fresh_global c Σ).
Proof.
  induction Σ; cbn. 1: congruence.
  destruct (eqb_spec c a.1); subst.
  - intros [= <-] H2. inv H2.
    contradiction.
  - intros H1 H2. apply IHΣ; tas.
    now inv H2.
Qed.

Lemma lookup_env_Some_fresh Σ c decl :
  lookup_env Σ c = Some decl -> ~ (fresh_global c Σ.(declarations)).
Proof.
  apply lookup_global_Some_fresh.
Qed.

Section ExtendsWf.
  Context {cf : checker_flags}.
  Context {Pcmp: global_env_ext -> context -> conv_pb -> term -> term -> Type}.
  Context {P: global_env_ext -> context -> term -> typ_or_sort -> Type}.

  Let wf := on_global_env Pcmp P.

Lemma extends_lookup Σ Σ' c decl :
  wf Σ' ->
  extends Σ Σ' ->
  lookup_env Σ c = Some decl ->
  lookup_env Σ' c = Some decl.
Proof using P Pcmp cf.
  destruct Σ as [univs Σ], Σ' as [univs' Σ']; cbn.
  intros [hu hΣ].
  rewrite /lookup_env; intros [sub [Σ'' eq]]; cbn in *. subst Σ'.
  induction Σ'' in hΣ, c, decl |- *.
  - simpl. auto.
  - intros hl. depelim hΣ. specialize (IHΣ'' c decl hΣ hl).
    simpl in *.
    destruct (eqb_spec c kn); subst; auto. destruct o.
    apply lookup_global_Some_fresh in IHΣ''; contradiction.
Qed.
Hint Resolve extends_lookup : extends.

Lemma weakening_env_declared_constant :
  forall (Σ : global_env) cst (decl : constant_body),
    declared_constant Σ cst decl ->
    forall Σ' : global_env, wf Σ' -> extends Σ Σ' -> declared_constant Σ' cst decl.
Proof using P Pcmp cf.
  intros Σ cst decl H0 Σ' X2 H2.
  eapply extends_lookup; eauto.
Qed.
Hint Resolve weakening_env_declared_constant : extends.

Lemma weakening_env_declared_minductive `{CF:checker_flags}:
  forall (Σ : global_env) ind decl,
    declared_minductive Σ ind decl ->
    forall Σ' : global_env, wf Σ' -> extends Σ Σ' -> declared_minductive Σ' ind decl.
Proof using P Pcmp cf.
  intros Σ cst decl H0 Σ' X2 H2.
  eapply extends_lookup; eauto.
Qed.

Hint Extern 0 => eapply weakening_env_declared_minductive : extends.

Lemma weakening_env_declared_inductive:
  forall (H : checker_flags) (Σ : global_env) ind mdecl decl,
    declared_inductive Σ mdecl ind decl ->
    forall Σ' : global_env, wf Σ' -> extends Σ Σ' -> declared_inductive Σ' mdecl ind decl.
Proof using P Pcmp cf.
  intros H Σ cst decl H0 [Hmdecl Hidecl] Σ' X2 H2. split; eauto with extends.
Qed.

Hint Extern 0 => eapply weakening_env_declared_inductive : extends.

Lemma weakening_env_declared_constructor :
  forall (H : checker_flags) (Σ : global_env) ind mdecl idecl decl,
    declared_constructor Σ idecl ind mdecl decl ->
    forall Σ' : global_env, wf Σ' -> extends Σ Σ' ->
    declared_constructor Σ' idecl ind mdecl decl.
Proof using P Pcmp cf.
  intros H Σ cst mdecl idecl cdecl [Hidecl Hcdecl] Σ' X2 H2.
  split; eauto with extends.
Qed.
Hint Extern 0 => eapply weakening_env_declared_constructor : extends.

Lemma weakening_env_declared_projection :
  forall (H : checker_flags) (Σ : global_env) ind mdecl idecl cdecl pdecl,
    declared_projection Σ idecl ind mdecl cdecl pdecl ->
    forall Σ' : global_env, wf Σ' -> extends Σ Σ' ->
    declared_projection Σ' idecl ind mdecl cdecl pdecl.
Proof using P Pcmp cf.
  intros H Σ cst mdecl idecl cdecl pdecl [Hidecl Hcdecl] Σ' X2 H2.
  split; eauto with extends.
Qed.
Hint Extern 0 => eapply weakening_env_declared_projection : extends.

(* Lemma wf_extends {Σ Σ'} : wf Σ' -> extends Σ Σ' -> wf Σ.
Proof.
  intros HΣ' [univs [Σ'' eq]]. simpl in *.
  split => //.
  - red.
  induction Σ''; auto.
  inv HΣ'. auto.
Qed. *)

(** ** Back to universes *)


Lemma weaken_lookup_on_global_env' Σ c decl :
  wf Σ ->
  lookup_env Σ c = Some decl ->
  on_udecl_prop Σ (universes_decl_of_decl decl).
Proof using P Pcmp cf.
  intros [onu wfΣ] HH.
  destruct Σ as [univs Σ]; cbn in *.
  induction wfΣ; simpl. 1: discriminate.
  destruct o as [? udecl o ?].
  cbn in HH. subst udecl.
  destruct (eqb_spec c kn); subst.
  - apply some_inj in HH; destruct HH. subst.
    clear -o. unfold on_udecl, on_udecl_prop in *.
    destruct o as [H1 [H2 [H3 H4]]]. repeat split.
    clear -H2. intros [[? ?] ?] Hc. specialize (H2 _ Hc).
    destruct H2 as [H H']. simpl. split.
    * apply LevelSet.union_spec in H. apply LevelSet.union_spec.
      destruct H; [now left|right]; auto.
    * apply LevelSet.union_spec in H'. apply LevelSet.union_spec.
      destruct H'; [now left|right]; auto.
    (*+ revert H3. case_eq (universes_decl_of_decl d); trivial.
      intros ctx eq Hctx. repeat split.
      * auto.
      * intros l Hl. simpl. replace (monomorphic_levels_decl d) with ctx.1.
        -- apply in_global_levels. apply LevelSet.union_spec; now left.
        -- clear -eq. destruct d as [c|c]; cbn in *.
           all: destruct c; cbn in *; now rewrite eq.
      * simpl. replace (monomorphic_constraints_decl d) with ctx.2.
        -- intros c Hc; apply ConstraintSet.union_spec; now left.
        -- clear -eq. destruct d as [c|c]; cbn in *.
           all: destruct c; cbn in *; now rewrite eq.
      * clear -eq H4. destruct H4 as [v Hv]. exists v.
      intros c Hc; apply (Hv c).
      apply ConstraintSet.union_spec in Hc; destruct Hc as [Hc|Hc].
      2: apply ConstraintSet.union_spec in Hc; destruct Hc as [Hc|Hc].
      -- apply ConstraintSet.union_spec. simpl in *. left; now rewrite eq.
      -- apply ConstraintSet.union_spec; left. simpl.
         destruct d as [[? ? []]|[? ? ? ? []]]; simpl in *; tas;
           now apply ConstraintSet.empty_spec in Hc.
      -- apply ConstraintSet.union_spec; now right.*)
  - specialize (IHwfΣ HH). revert IHwfΣ o; clear.
    generalize (universes_decl_of_decl decl); intros d' HH Hd.
    unfold on_udecl_prop in *.
    intros [[? ?] ?] Hc. specialize (HH _ Hc).
    destruct HH as [H' H'']. simpl. split.
    * apply LevelSet.union_spec in H'. apply LevelSet.union_spec.
      destruct H'; [now left|right]; auto.
    * apply LevelSet.union_spec in H''. apply LevelSet.union_spec.
      destruct H''; [now left|right]; auto.

    (*+ destruct d'; trivial. repeat split.
      * destruct H2; auto.
      * intros l Hl. apply H2 in Hl.
        apply LevelSet.union_spec; now right.
      * intros c Hc. apply H2 in Hc.
        apply ConstraintSet.union_spec; now right.
      * destruct Hd as [_ [_ [_ Hd]]]; cbn in Hd.
        destruct Hd as [v Hv]. exists v. intros c Hc; apply Hv; clear v Hv.
          apply ConstraintSet.union_spec in Hc; destruct Hc as [Hc|Hc]; simpl in *.
          2: apply ConstraintSet.union_spec in Hc; destruct Hc as [Hc|Hc];
            simpl in *.
          -- apply H2 in Hc. apply ConstraintSet.union_spec; now right.
          -- clear -Hc. destruct d as [[? ? []]|[? ? ? ? []]]; cbn in *.
             all: try (apply ConstraintSet.empty_spec in Hc; contradiction).
             all: apply ConstraintSet.union_spec; now left.
          -- apply ConstraintSet.union_spec; now right.*)
Qed.



Definition weaken_env_prop_full
  (P : global_env_ext -> context -> term -> term -> Type) :=
  forall (Σ : global_env_ext) (Σ' : global_env),
    wf Σ -> wf Σ' -> extends Σ.1 Σ' ->
    forall Γ t T, P Σ Γ t T -> P (Σ', Σ.2) Γ t T.

Definition weaken_env_prop
           (P : global_env_ext -> context -> term -> typ_or_sort -> Type) :=
  forall Σ Σ' φ, wf Σ -> wf Σ' -> extends Σ Σ' -> forall Γ t T, P (Σ, φ) Γ t T -> P (Σ', φ) Γ t T.

Definition weaken_env_decls_prop
  (P : global_env_ext -> context -> term -> typ_or_sort -> Type) :=
  forall Σ Σ' φ, wf Σ' -> extends_decls Σ Σ' -> forall Γ t T, P (Σ, φ) Γ t T -> P (Σ', φ) Γ t T.

Lemma extends_decls_wf Σ Σ' :
  wf Σ' -> extends_decls Σ Σ' -> wf Σ.
Proof using P Pcmp cf.
  intros [onu ond] [eq [Σ'' eq']].
  split => //.
  - red. rewrite eq. apply onu.
  - rewrite eq. rewrite eq' in ond.
    rewrite -e in ond.
    revert ond; clear.
    induction Σ''; cbn; auto.
    intros H; depelim H.
    apply IHΣ''. apply H.
Qed.

End ExtendsWf.

Arguments weaken_env_prop_full {cf} (Pcmp P)%function_scope _%function_scope.
Arguments weaken_env_decls_prop {cf} (Pcmp P)%function_scope _%function_scope.
Arguments weaken_env_prop {cf} (Pcmp P)%function_scope _%function_scope.

#[global] Hint Resolve extends_lookup : extends.
#[global] Hint Resolve weakening_env_declared_constant : extends.
#[global] Hint Resolve weakening_env_declared_minductive : extends.
#[global] Hint Resolve weakening_env_declared_inductive : extends.
#[global] Hint Resolve weakening_env_declared_constructor : extends.
#[global] Hint Resolve weakening_env_declared_projection : extends.
