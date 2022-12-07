(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
  PCUICWeakeningEnv PCUICEquality PCUICReduction PCUICCumulativity PCUICCumulativitySpec
  (* PCUICContextSubst *) (* PCUICUnivSubst *) (* PCUICCases *) (* PCUICTyping *)
  (* PCUICGuardCondition *) (* PCUICGlobalEnv *).
From Equations Require Import Equations.

Require Import ssreflect.

Set Default Goal Selector "!".
Implicit Types (cf : checker_flags).

Lemma compare_term_subset {cf} pb Σ φ φ' t t'
  : ConstraintSet.Subset φ φ'
    -> compare_term pb Σ φ t t' -> compare_term pb Σ φ' t t'.
Proof.
  intro H. apply eq_term_upto_univ_impl; auto.
  all: change eq_universe with (compare_universe Conv).
  all: change leq_universe with (compare_universe Cumul).
  3: destruct pb.
  4: transitivity (compare_universe Cumul φ).
  4: tc.
  all: intros ??; now eapply cmp_universe_subset.
Qed.

Lemma eq_term_subset {cf} Σ φ φ' t t'
  : ConstraintSet.Subset φ φ' -> eq_term Σ φ t t' -> eq_term Σ φ' t t'.
Proof. apply compare_term_subset with (pb := Conv). Qed.

Lemma leq_term_subset {cf:checker_flags} Σ ctrs ctrs' t u
  : ConstraintSet.Subset ctrs ctrs' -> leq_term Σ ctrs t u -> leq_term Σ ctrs' t u.
Proof. apply compare_term_subset with (pb := Cumul). Qed.

Lemma compare_decl_subset {cf} pb Σ φ φ' d d'
  : ConstraintSet.Subset φ φ'
    -> compare_decl pb Σ φ d d' -> compare_decl pb Σ φ' d d'.
Proof.
  intros Hφ []; constructor; eauto using compare_term_subset.
Qed.

Lemma compare_context_subset {cf} pb Σ φ φ' Γ Γ'
  : ConstraintSet.Subset φ φ'
    -> compare_context pb Σ φ Γ Γ' ->  compare_context pb Σ φ' Γ Γ'.
Proof.
  intros Hφ. induction 1; constructor; auto; eapply compare_decl_subset; eassumption.
Qed.

Section ExtendsWf.
  Context {cf : checker_flags}.
  Context {Pcmp: global_env_ext -> context -> conv_pb -> term -> term -> Type}.
  Context {P: global_env_ext -> context -> term -> typ_or_sort -> Type}.

  Let wf := on_global_env Pcmp P.

Lemma global_variance_sigma_mon {Σ Σ' gr napp v} :
  wf Σ' -> extends Σ Σ' ->
  global_variance Σ gr napp = Some v ->
  global_variance Σ' gr napp = Some v.
Proof using P Pcmp cf.
  intros wfΣ' ext.
  rewrite /global_variance_gen /lookup_constructor /lookup_constructor_gen 
    /lookup_inductive /lookup_inductive_gen /lookup_minductive /lookup_minductive_gen.
  destruct gr as [|ind|[ind i]|] => /= //.
  - destruct (lookup_env Σ ind) eqn:look => //.
    eapply extends_lookup in look; eauto. rewrite look //.
  - destruct (lookup_env Σ (inductive_mind i)) eqn:look => //.
    eapply extends_lookup in look; eauto. rewrite look //.
Qed.

(** The definition of [R_global_instance] is defined so that it is weakenable. *)
Lemma R_global_instance_weaken_env Σ Σ' Re Re' Rle Rle' gr napp :
  wf Σ' -> extends Σ Σ' ->
  RelationClasses.subrelation Re Re' ->
  RelationClasses.subrelation Rle Rle' ->
  RelationClasses.subrelation Re Rle' ->
  subrelation (R_global_instance Σ Re Rle gr napp) (R_global_instance Σ' Re' Rle' gr napp).
Proof using P Pcmp cf.
  intros wfΣ ext he hle hele t t'.
  rewrite /R_global_instance_gen /R_opt_variance.
  destruct global_variance_gen as [v|] eqn:look.
  - rewrite (global_variance_sigma_mon wfΣ ext look).
    induction t in v, t' |- *; destruct v, t'; simpl; auto.
    intros []; split; auto.
    destruct t0; simpl; auto.
  - destruct (global_variance Σ' gr napp) => //.
    * induction t in l, t' |- *; destruct l,  t'; simpl; intros H; inv H; auto.
      split; auto. destruct t0; simpl; auto.
    * eauto using R_universe_instance_impl'.
Qed.

#[global]
Instance eq_term_upto_univ_weaken_env Σ Σ' Re Re' Rle Rle' napp :
  wf Σ' -> extends Σ Σ' ->
  RelationClasses.subrelation Re Re' ->
  RelationClasses.subrelation Rle Rle' ->
  RelationClasses.subrelation Re Rle' ->
  CRelationClasses.subrelation (eq_term_upto_univ_napp Σ Re Rle napp)
    (eq_term_upto_univ_napp Σ' Re' Rle' napp).
Proof using P Pcmp cf.
  intros wfΣ ext he hele hle t t'.
  induction t in napp, t', Rle, Rle', hle, hele |- * using PCUICInduction.term_forall_list_ind;
    try (inversion 1; subst; constructor;
         eauto using R_universe_instance_impl'; fail).
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
  - inversion 1; subst; constructor.
    eapply R_global_instance_weaken_env. 6:eauto. all:eauto.
  - inversion 1; subst; constructor.
    eapply R_global_instance_weaken_env. 6:eauto. all:eauto.
  - inversion 1; subst; destruct X as [? [? ?]]; constructor; eauto.
    * destruct X2 as [? [? ?]].
      constructor; intuition auto; solve_all.
      + eauto using R_universe_instance_impl'.
    * eapply All2_impl'; tea.
      eapply All_impl; eauto.
      cbn. intros x [? ?] y [? ?]. split; eauto.
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x [? ?] y [[[? ?] ?] ?]. repeat split; eauto.
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x [? ?] y [[[? ?] ?] ?]. repeat split; eauto.
Qed.

Lemma weakening_env_red1 Σ Σ' Γ M N :
  wf Σ' ->
  extends Σ Σ' ->
  red1 Σ Γ M N ->
  red1 Σ' Γ M N.
Proof using P Pcmp cf.
  induction 3 using red1_ind_all;
    try solve [econstructor; eauto with extends; solve_all].
Qed.

Lemma weakening_env_cumul_gen pb Σ Σ' φ Γ M N :
  wf Σ' ->
  extends Σ Σ' ->
  cumulAlgo_gen (Σ, φ)  Γ pb M N ->
  cumulAlgo_gen (Σ', φ) Γ pb M N.
Proof using P Pcmp.
  intros wfΣ ext.
  induction 1; simpl.
  - econstructor. eapply compare_term_subset.
    + now eapply global_ext_constraints_app.
    + simpl in *. eapply eq_term_upto_univ_weaken_env in c; simpl; eauto.
      all:typeclasses eauto.
  - econstructor 2; eauto. eapply weakening_env_red1; eauto.
  - econstructor 3; eauto. eapply weakening_env_red1; eauto.
Qed.

Lemma weakening_env_conv Σ Σ' φ Γ M N :
  wf Σ' ->
  extends Σ Σ' ->
  convAlgo (Σ, φ) Γ M N ->
  convAlgo (Σ', φ) Γ M N.
Proof using P Pcmp. apply weakening_env_cumul_gen with (pb := Conv). Qed.

Lemma weakening_env_cumul Σ Σ' φ Γ M N :
  wf Σ' ->
  extends Σ Σ' ->
  cumulAlgo (Σ, φ) Γ M N ->
  cumulAlgo (Σ', φ) Γ M N.
Proof using P Pcmp. apply weakening_env_cumul_gen with (pb := Cumul). Qed.


Lemma weakening_env_cumulSpec0 Σ Σ' φ Γ pb M N :
  wf Σ' ->
  extends Σ Σ' ->
  cumulSpec0 (Σ, φ) Γ pb M N ->
  cumulSpec0 (Σ', φ) Γ pb M N.
Proof.
  intros HΣ' Hextends Ind.
  pose proof (subrelations_leq_extends _ _  φ Hextends). revert H.
  assert (RelationClasses.subrelation
          (eq_universe (global_ext_constraints (Σ,φ)))
          (leq_universe (global_ext_constraints (Σ',φ)))).
  { typeclasses eauto. } revert H.
  generalize (leq_universe (global_ext_constraints (Σ',φ))); intros Rle Hlee Hle .
  revert pb Γ M N Ind Σ' Rle Hle Hlee HΣ' Hextends.
  apply: (cumulSpec0_ind_all (Σ,φ)).
  all:intros; try solve [econstructor; eauto with extends; intuition auto].
  - eapply cumul_Evar. solve_all.
  - eapply cumul_Case.
    * destruct X as (Hparams & Hinst & Hctx & Hret & IHret). repeat split; tas.
      + solve_all.
      + eapply R_universe_instance_impl'; eauto; apply subrelations_extends; eauto.
      + eapply IHret; eauto.
    * solve_all.
    * solve_all.
  - eapply cumul_Fix; solve_all.
  - eapply cumul_CoFix; solve_all.
  - eapply cumul_Ind; eauto. 2:solve_all.
    eapply @R_global_instance_weaken_env. 1,2,6:eauto. all: tc.
  - eapply cumul_Construct; eauto. 2:solve_all.
    eapply @R_global_instance_weaken_env. 1,2,6:eauto. all: tc.
  - eapply cumul_Sort. eapply subrelations_compare_extends; tea.
  - eapply cumul_Const. eapply R_universe_instance_impl'; eauto; tc.
Defined.


Lemma weakening_env_convSpec Σ Σ' φ Γ M N :
  wf Σ' ->
  extends Σ Σ' ->
  convSpec (Σ, φ) Γ M N ->
  convSpec (Σ', φ) Γ M N.
Proof using P Pcmp. apply weakening_env_cumulSpec0 with (pb := Conv). Qed.

Lemma weakening_env_cumulSpec Σ Σ' φ Γ M N :
  wf Σ' ->
  extends Σ Σ' ->
  cumulSpec (Σ, φ) Γ M N ->
  cumulSpec (Σ', φ) Γ M N.
Proof using P Pcmp. apply weakening_env_cumulSpec0 with (pb := Cumul). Qed.

Lemma weakening_env_conv_decls {Σ φ Σ' Γ Γ'} :
  wf Σ' -> extends Σ Σ' ->
  CRelationClasses.subrelation (conv_decls cumulSpec0 (Σ, φ) Γ Γ') (conv_decls cumulSpec0 (Σ', φ) Γ Γ').
Proof using P Pcmp.
  intros wfΣ' ext d d' Hd; depelim Hd; constructor; tas;
    eapply weakening_env_convSpec; tea.
Qed.

Lemma weakening_env_cumul_decls {Σ φ Σ' Γ Γ'} :
  wf Σ' -> extends Σ Σ' ->
  CRelationClasses.subrelation (cumul_decls cumulSpec0 (Σ, φ) Γ Γ') (cumul_decls cumulSpec0 (Σ', φ) Γ Γ').
Proof using P Pcmp.
  intros wfΣ' ext d d' Hd; depelim Hd; constructor; tas;
    (eapply weakening_env_convSpec || eapply weakening_env_cumulSpec); tea.
Qed.

Lemma weakening_env_conv_ctx {Σ Σ' φ Γ Δ} :
  wf Σ' ->
  extends Σ Σ' ->
  conv_context cumulSpec0 (Σ, φ) Γ Δ ->
  conv_context cumulSpec0 (Σ', φ) Γ Δ.
Proof using P Pcmp.
  intros wfΣ' ext.
  intros; eapply All2_fold_impl; tea => Γ0 Γ' d d'.
  now eapply weakening_env_conv_decls.
Qed.


Lemma weakening_env_cumul_ctx {Σ Σ' φ Γ Δ} :
  wf Σ' ->
  extends Σ Σ' ->
  cumul_context cumulSpec0 (Σ, φ) Γ Δ ->
  cumul_context cumulSpec0 (Σ', φ) Γ Δ.
Proof using P Pcmp.
  intros wfΣ' ext.
  intros; eapply All2_fold_impl; tea => Γ0 Γ' d d'.
  now eapply weakening_env_cumul_decls.
Qed.

End ExtendsWf.

#[global] Hint Resolve weakening_env_conv_ctx : extends.
#[global] Hint Resolve weakening_env_cumul_ctx : extends.
