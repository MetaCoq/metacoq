(* Distributed under the terms of the MIT license.   *)
From Equations Require Import Equations.
From Coq Require Import Bool String List Program BinPos Compare_dec Omega Lia.
From MetaCoq.Template Require Import config utils AstUtils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICWeakeningEnv PCUICWeakening
     PCUICSubstitution
     PCUICReduction PCUICCumulativity PCUICConfluence PCUICParallelReductionConfluence
     PCUICEquality PCUICContextConversion.
Require Import ssreflect ssrbool.
Require Import String.
From MetaCoq Require Import LibHypsNaming.
Local Open Scope string_scope.
Set Asymmetric Patterns.
Require Import CRelationClasses.
Require Import Equations.Type.Relation Equations.Type.Relation_Properties.
Require Import Equations.Prop.DepElim.

Ltac tc := try typeclasses eauto 10.
Hint Resolve eq_universe_leq_universe' : pcuic.

Derive Signature for cumul assumption_context.

Instance cumul_trans {cf:checker_flags} (Σ : global_env_ext) Γ :
  wf Σ -> Transitive (cumul Σ Γ).
Proof.
  intros wfΣ t u v X X0.
  eapply cumul_alt in X as [v' [v'' [[redl redr] eq]]].
  eapply cumul_alt in X0 as [w [w' [[redl' redr'] eq']]].
  destruct (red_confluence wfΣ redr redl') as [nf [nfl nfr]].
  eapply cumul_alt.
  eapply red_eq_term_upto_univ_r in eq; tc;eauto with pcuic.
  destruct eq as [v'0 [red'0 eq2]].
  eapply red_eq_term_upto_univ_l in eq'; tc;eauto with pcuic.
  destruct eq' as [v'1 [red'1 eq1]].
  exists v'0, v'1.
  split. split; auto.
  transitivity v'; auto.
  transitivity w'; auto.
  eapply leq_term_trans with nf; eauto.
Qed.

Instance conv_trans {cf:checker_flags} (Σ : global_env_ext) Γ :
  wf Σ -> Transitive (PCUICTyping.conv Σ Γ).
Proof.
  intros wfΣ t u v tu uv.
  split. eapply cumul_trans with u. auto. apply tu. apply uv.
  eapply cumul_trans with u. auto. apply uv. apply tu.
Qed.

Instance conv_sym {cf:checker_flags} (Σ : global_env_ext) Γ :
  wf Σ -> Symmetric (PCUICTyping.conv Σ Γ).
Proof.
  intros wfΣ t u tu. split; apply tu.
Qed.

Instance conv_alt_reflexive {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} Γ : Reflexive (conv_alt Σ Γ).
Proof. intros x. eapply conv_alt_refl, eq_term_refl. Qed.

Instance conv_alt_symmetric {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} Γ : Symmetric (conv_alt Σ Γ).
Proof. intros x y. eapply conv_alt_sym. auto. Qed.

Instance conv_alt_transitive {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} Γ : Transitive (conv_alt Σ Γ).
Proof. intros x y z. eapply conv_alt_trans. auto. Qed.

Instance cumul_reflexive {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} Γ : Reflexive (cumul Σ Γ).
Proof. intros x. eapply cumul_refl'. Qed.

Instance cumul_transitive {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} Γ : Transitive (cumul Σ Γ).
Proof. intros x y z. eapply cumul_trans. auto. Qed.

Existing Class wf.

Lemma congr_cumul_prod : forall `{checker_flags} Σ Γ na na' M1 M2 N1 N2,
    Σ ;;; Γ |- M1 == N1 ->
    Σ ;;; (Γ ,, vass na M1) |- M2 <= N2 ->
    Σ ;;; Γ |- (tProd na M1 M2) <= (tProd na' N1 N2).
Proof.
  intros.
Admitted.

(* Should follow from context conversion + invariants on T and U *)
(* Lemma conv_conv_alt `{cf : checker_flags} {Σ : global_env_ext} (wfΣ : wf Σ) Γ T U : *)
(*   Σ ;;; Γ |- T = U -> Σ ;;; Γ |- T == U. *)
(* Proof. *)
(* Admitted. *)

Lemma cumul_Sort_inv {cf:checker_flags} Σ Γ s s' :
  Σ ;;; Γ |- tSort s <= tSort s' -> leq_universe (global_ext_constraints Σ) s s'.
Proof.
  intros H; depind H; auto.
  - now inversion l.
  - depelim r. solve_discr.
  - depelim r. solve_discr.
Qed.

Lemma cumul_Sort_Prod_inv {cf:checker_flags} Σ Γ s na dom codom :
  Σ ;;; Γ |- tSort s <= tProd na dom codom -> False.
Proof.
  intros H; depind H; auto.
  - now inversion l.
  - depelim r. solve_discr.
  - depelim r. solve_discr. eapply IHcumul. reflexivity.
    eapply IHcumul. reflexivity.
Qed.

Lemma cumul_Sort_l_inv {cf:checker_flags} Σ Γ s T :
  Σ ;;; Γ |- tSort s <= T ->
  ∑ s', red Σ Γ T (tSort s') * leq_universe Σ s s'.
Proof.
  intros H; depind H; auto.
  - now inversion l.
  - depelim r. solve_discr.
  - destruct IHcumul as [s' [redv leq]].
    exists s'. split; auto. now eapply red_step with v.
Qed.

Lemma cumul_Sort_r_inv {cf:checker_flags} Σ Γ s T :
  Σ ;;; Γ |- T <= tSort s ->
  ∑ s', red Σ Γ T (tSort s') * leq_universe Σ s' s.
Proof.
  intros H; depind H; auto.
  - now inversion l.
  - destruct IHcumul as [s' [redv leq]].
    exists s'. split; auto. now eapply red_step with v.
  - depelim r. solve_discr.
Qed.

Lemma cumul_LetIn_l_inv {cf:checker_flags} (Σ : global_env_ext) Γ na b B codom T :
  wf Σ ->
  Σ ;;; Γ |- tLetIn na b B codom <= T ->
  ∑ codom', red Σ Γ T codom' *
                     (Σ ;;; Γ |- codom {0 := b} <= codom').
Proof.
  intros wfΣ H; depind H; auto.
  - inv l. eexists (u' {0 := t'}); intuition eauto. eapply red1_red. constructor.
    transitivity (codom {0 := t'}).
    { constructor. eapply eq_term_upto_univ_subst; trivial. auto with pcuic. reflexivity. }
    constructor. now eapply subst_leq_term.
  - depelim r.
    * exists u; intuition auto.
    * solve_discr.
    * specialize (IHcumul _ _ _ _ _ wfΣ eq_refl).
      destruct IHcumul as [codom' [reddom' leq]].
      exists codom'; intuition auto.
      transitivity (codom {0 := r}); eauto.
      eapply red_cumul. eapply (red_red Σ _ [vdef na b B] []) => //. constructor. now eapply red1_red.
      constructor. rewrite -{1}(subst_empty 0 b). repeat constructor.
    * specialize (IHcumul _ _ _ _ _ wfΣ eq_refl).
      destruct IHcumul as [codom' [reddom' leq]].
      exists codom'; intuition auto.
    * specialize (IHcumul _ _ _ _ _ wfΣ eq_refl).
      destruct IHcumul as [codom' [reddom' leq]].
      exists codom'; intuition auto.
      eapply transitivity; [|eassumption].
      eapply red_cumul.
      rewrite -{1 2}(subst_empty 0 b).
      eapply (untyped_substitution_red _ _ [vdef na b B] []); auto. repeat constructor.
  - specialize (IHcumul wfΣ).
    destruct IHcumul as [codom' [reddom' leq]] => //.
    exists codom'; intuition auto.
    now eapply red_step with v.
Qed.

Lemma cumul_LetIn_r_inv {cf:checker_flags} (Σ : global_env_ext) Γ na b B codom T :
  wf Σ ->
  Σ ;;; Γ |- T <= tLetIn na b B codom ->
  ∑ codom', red Σ Γ T codom' *
                     (Σ ;;; Γ |- codom' <= codom {0 := b}).
Proof.
  intros wfΣ H; depind H; auto.
  - inv l. eexists (u {0 := t0}); intuition eauto. eapply red1_red. constructor.
    transitivity (codom {0 := t0}).
    { constructor. eapply eq_term_upto_univ_subst; trivial. auto with pcuic. reflexivity. }
    constructor. eapply eq_term_upto_univ_subst; auto with pcuic. reflexivity.
  - specialize (IHcumul wfΣ).
    destruct IHcumul as [codom' [reddom' leq]] => //.
    exists codom'; intuition auto.
    now eapply red_step with v.
  - depelim r.
    * eexists ; intuition eauto.
    * solve_discr.
    * specialize (IHcumul _ _ _ _ _ wfΣ eq_refl).
      destruct IHcumul as [codom' [reddom' leq]].
      exists codom'; intuition auto.
      transitivity (codom {0 := r}); eauto.
      eapply red_cumul_inv. eapply (red_red Σ _ [vdef na b B] []) => //. constructor. now eapply red1_red.
      constructor. rewrite -{1}(subst_empty 0 b). repeat constructor.
    * specialize (IHcumul _ _ _ _ _ wfΣ eq_refl).
      destruct IHcumul as [codom' [reddom' leq]].
      exists codom'; intuition auto.
    * specialize (IHcumul _ _ _ _ _ wfΣ eq_refl).
      destruct IHcumul as [codom' [reddom' leq]].
      exists codom'; intuition auto.
      eapply transitivity; [eassumption|].
      eapply red_cumul_inv.
      rewrite -{1 2}(subst_empty 0 b).
      eapply (untyped_substitution_red _ _ [vdef na b B] []); auto. repeat constructor.
Qed.

Lemma cumul_Prod_l_inv {cf:checker_flags} (Σ : global_env_ext) Γ na dom codom T :
  wf Σ ->
  Σ ;;; Γ |- tProd na dom codom <= T ->
  ∑ na' dom' codom', red Σ Γ T (tProd na' dom' codom') *
                     (Σ ;;; Γ |- dom == dom') * (Σ ;;; Γ ,, vass na dom |- codom <= codom').
Proof.
  intros wfΣ H; depind H; auto.
  - inv l. exists na', a', b'; intuition eauto; constructor; auto.
  - depelim r. solve_discr.
    * specialize (IHcumul _ _ _ _ wfΣ eq_refl).
      destruct IHcumul as [na' [dom' [codom' [[reddom' eqdom'] leq]]]].
      exists na', dom', codom'; intuition auto.
      transitivity N1; eauto.
      eapply cumul_conv_ctx; eauto. constructor; auto with pcuic.
      constructor. symmetry; eapply red_conv_alt; auto.

    * specialize (IHcumul _ _ _ _ wfΣ eq_refl).
      destruct IHcumul as [na' [dom' [codom' [[reddom' eqdom'] leq]]]].
      exists na', dom', codom'; intuition auto.
      transitivity N2; eauto. eapply red_cumul; auto.
  - destruct IHcumul as [na' [dom' [codom' [[reddom' eqdom'] leq]]]] => //.
    exists na', dom', codom'; intuition auto.
    now eapply red_step with v.
Qed.

Lemma cumul_Prod_r_inv {cf:checker_flags} (Σ : global_env_ext) Γ na' dom' codom' T :
  wf Σ ->
  Σ ;;; Γ |- T <= tProd na' dom' codom' ->
  ∑ na dom codom, red Σ Γ T (tProd na dom codom) *
                     (Σ ;;; Γ |- dom == dom') * (Σ ;;; Γ ,, vass na' dom' |- codom <= codom').
Proof.
  intros wfΣ H; depind H; auto.
  - inv l. exists na, a, b; intuition eauto; constructor; auto.
  - destruct IHcumul as [na [dom [codom [[reddom' eqdom'] leq]]]] => //.
    exists na, dom, codom; intuition auto.
    now eapply red_step with v.
  - depelim r. solve_discr.
    * specialize (IHcumul _ _ _ _ wfΣ eq_refl).
      destruct IHcumul as [na [dom [codom [[reddom' eqdom'] leq]]]].
      eexists _, _, _; intuition eauto.
      transitivity N1; eauto. symmetry; apply red_conv_alt; auto.
      eapply cumul_conv_ctx; eauto. constructor; auto with pcuic.
      constructor. symmetry. eapply red_conv_alt; auto.

    * specialize (IHcumul _ _ _ _ wfΣ eq_refl).
      destruct IHcumul as [na [dom [codom [[reddom' eqdom'] leq]]]].
      eexists _, _, _; intuition eauto.
      transitivity N2; eauto. eapply red_cumul_inv; auto.
Qed.

Lemma cumul_Prod_Sort_inv {cf:checker_flags} Σ Γ s na dom codom :
  Σ ;;; Γ |- tProd na dom codom <= tSort s -> False.
Proof.
  intros H; depind H; auto.
  - now inversion l.
  - depelim r. solve_discr. eapply IHcumul; reflexivity.
    eapply IHcumul; reflexivity.
  - depelim r. solve_discr.
Qed.

Lemma cumul_Prod_Prod_inv {cf:checker_flags} (Σ : global_env_ext) Γ na na' dom dom' codom codom' : wf Σ ->
  Σ ;;; Γ |- tProd na dom codom <= tProd na' dom' codom' ->
   ((Σ ;;; Γ |- dom == dom') * (Σ ;;; Γ ,, vass na' dom' |- codom <= codom'))%type.
Proof.
  intros wfΣ H; depind H; auto.
  - inv l. split; auto; constructor; auto.
  - depelim r. solve_discr.
    destruct (IHcumul na na' N1 _ _ _ wfΣ eq_refl).
    split; auto. transitivity N1=> //. now eapply red_conv_alt, red1_red.
    destruct (IHcumul na na' _ _ N2 _ wfΣ eq_refl).
    split; auto. eapply cumul_trans. auto. 2:eauto.
    eapply cumul_conv_ctx; eauto. eapply red_cumul; eauto.
    constructor; auto with pcuic.
  - depelim r. solve_discr.
    destruct (IHcumul na na' _ _ _ _ wfΣ eq_refl).
    split; auto. transitivity N1 => //. symmetry => //.
    now eapply red_conv_alt, red1_red.
    eapply cumul_red_ctx_inv. auto. eauto. constructor. eapply All2_local_env_red_refl. red.
    now eapply red1_red.
    destruct (IHcumul na na' _ _ _ _ wfΣ eq_refl).
    split; auto.
    eapply cumul_trans with N2; auto.
    eapply red1_red, red_conv in r. apply r.
Qed.

Lemma assumption_context_app Γ Γ' :
  assumption_context (Γ' ,,, Γ) ->
  assumption_context Γ * assumption_context Γ'.
Proof.
  induction Γ; simpl; split; try constructor; auto. depelim H. constructor; auto. now eapply IHΓ.
  depelim H. now eapply IHΓ.
Qed.

Lemma it_mkProd_or_LetIn_ass_inv {cf : checker_flags} (Σ : global_env_ext) Γ ctx ctx' s s' :
  wf Σ ->
  assumption_context ctx ->
  assumption_context ctx' ->
  Σ ;;; Γ |- it_mkProd_or_LetIn ctx (tSort s) <= it_mkProd_or_LetIn ctx' (tSort s') ->
  conv_context Σ ctx ctx' * leq_term Σ (tSort s) (tSort s').
Proof.
  intros wfΣ.
  revert Γ ctx' s s'.
  induction ctx using rev_ind.
  intros. destruct ctx' using rev_ind. simpl in X.
  - eapply cumul_Sort_inv in X. split; constructor; auto.
  - destruct x as [na [b|] ty]. elimtype False.
    apply assumption_context_app in H0.
    destruct H0. inv a0.
    rewrite it_mkProd_or_LetIn_app in X.
    apply assumption_context_app in H0 as [H0 _].
    specialize (IHctx' H0).
    simpl in IHctx'. simpl in X. unfold mkProd_or_LetIn in X. simpl in X.
    eapply cumul_Sort_Prod_inv in X. depelim X.
  - intros.
    rewrite it_mkProd_or_LetIn_app in X.
    simpl in X.
    eapply assumption_context_app in H as [H H'].
    destruct x as [na [b|] ty]. elimtype False. inv H'.
    rewrite /mkProd_or_LetIn /= in X.
    destruct ctx' using rev_ind.
    simpl in X.
    now eapply cumul_Prod_Sort_inv in X.
    eapply assumption_context_app in H0 as [H0 Hx].
    destruct x as [na' [b'|] ty']; [elimtype False; inv Hx|].
    rewrite it_mkProd_or_LetIn_app in X.
    rewrite /= /mkProd_or_LetIn /= in X.
    eapply cumul_Prod_Prod_inv in X as [Hdom Hcodom]; auto.
    specialize (IHctx (Γ ,, vass na' ty') l0 s s' H H0 Hcodom). clear IHctx'.
    intuition auto.
Admitted.

(** Injectivity of products, the essential property of cumulativity needed for subject reduction. *)
Lemma cumul_Prod_inv {cf:checker_flags} Σ Γ na na' A B A' B' :
  wf Σ.1 -> wf_local Σ Γ ->
  Σ ;;; Γ |- tProd na A B <= tProd na' A' B' ->
   ((Σ ;;; Γ |- A == A') * (Σ ;;; Γ ,, vass na' A' |- B <= B'))%type.
Proof.
  intros wfΣ wfΓ H; depind H.
  - depelim l.
    split; auto.
    now constructor.
    now constructor.

  - depelim r. solve_discr.
    specialize (IHcumul _ _ _ _ _ _ wfΣ wfΓ eq_refl).
    intuition auto.
    econstructor 2; eauto.

    specialize (IHcumul _ _ _ _ _ _ wfΣ wfΓ eq_refl).
    intuition auto. apply cumul_trans with N2. auto.
    eapply cumul_conv_ctx; eauto.

    econstructor 2. eauto. constructor. reflexivity.
    constructor. now apply conv_ctx_refl.
    constructor; auto.
    auto.

  - depelim r. solve_discr.
    specialize (IHcumul _ _ _ _ _ _ wfΣ wfΓ eq_refl).
    intuition auto. econstructor 3. 2:eauto. auto.
    eapply cumul_conv_ctx in b. eauto. auto. constructor. eapply conv_ctx_refl. auto.
    constructor. eapply conv_alt_sym; auto.

    specialize (IHcumul _ _ _ _ _ _ wfΣ wfΓ eq_refl).
    intuition auto. apply cumul_trans with N2. auto. auto.
    eapply cumul_red_r; eauto.
Qed.

Lemma tProd_it_mkProd_or_LetIn na A B ctx s :
  tProd na A B = it_mkProd_or_LetIn ctx (tSort s) ->
  { ctx' & ctx = (ctx' ++ [vass na A])%list /\
           destArity [] B = Some (ctx', s) }.
Proof.
  intros. exists (removelast ctx).
  revert na A B s H.
  induction ctx using rev_ind; intros; noconf H.
  rewrite it_mkProd_or_LetIn_app in H. simpl in H.
  destruct x as [na' [b'|] ty']; noconf H; simpl in *.
  rewrite removelast_app. congruence. simpl. rewrite app_nil_r. intuition auto.
  rewrite destArity_it_mkProd_or_LetIn. simpl. now rewrite app_context_nil_l.
Qed.

Section Inversions.
  Context {cf : checker_flags}.
  Context (Σ : global_env_ext) (wfΣ : wf Σ).

  Lemma conv_trans_reg : forall Γ u v w,
      Σ ;;; Γ |- u = v ->
                 Σ ;;; Γ |- v = w ->
                            Σ ;;; Γ |- u = w.
  Proof.
    intros Γ u v w h1 h2.
    destruct h1, h2. constructor ; eapply cumul_trans ; eassumption.
  Qed.

  Lemma cumul_App_r {Γ f u v} :
    Σ ;;; Γ |- u == v ->
    Σ ;;; Γ |- tApp f u <= tApp f v.
  Proof.
    intros h.
    induction h.
    - eapply cumul_refl. constructor.
      + apply leq_term_refl.
      + assumption.
    -  eapply cumul_red_l ; try eassumption.
       econstructor. assumption.
    - eapply cumul_red_r ; try eassumption.
      econstructor. assumption.
  Qed.

  Lemma conv_App_r {Γ f x y} :
    Σ ;;; Γ |- x == y ->
    Σ ;;; Γ |- tApp f x == tApp f y.
  Proof.
    intros h.
    induction h.
    - constructor. constructor.
      + apply eq_term_refl.
      + assumption.
    - eapply conv_alt_red_l ; eauto.
      econstructor. assumption.
    - eapply conv_alt_red_r ; eauto.
      econstructor. assumption.
  Qed.

  Lemma conv_Prod_l:
    forall {Γ na na' A1 A2 B},
      Σ ;;; Γ |- A1 == A2 ->
      Σ ;;; Γ |- tProd na A1 B == tProd na' A2 B.
  Proof.
    intros Γ na na' A1 A2 B h.
    induction h.
    - constructor. constructor.
      + assumption.
      + apply eq_term_refl.
    - eapply conv_alt_red_l ; eauto.
      econstructor. assumption.
    - eapply conv_alt_red_r ; eauto.
      econstructor. assumption.
  Qed.

  Lemma conv_Prod_r  :
    forall {Γ na A B1 B2},
      Σ ;;; Γ ,, vass na A |- B1 == B2 ->
      Σ ;;; Γ |- tProd na A B1 == tProd na A B2.
  Proof.
    intros Γ na A B1 B2 h.
    induction h.
    - constructor. constructor.
      + apply eq_term_refl.
      + assumption.
    - eapply conv_alt_red_l ; eauto.
      econstructor. assumption.
    - eapply conv_alt_red_r ; eauto.
      econstructor. assumption.
  Qed.

  Lemma cumul_Prod_r :
    forall {Γ na A B1 B2},
      Σ ;;; Γ ,, vass na A |- B1 <= B2 ->
      Σ ;;; Γ |- tProd na A B1 <= tProd na A B2.
  Proof.
    intros Γ na A B1 B2 h.
    induction h.
    - eapply cumul_refl. constructor.
      + apply eq_term_refl.
      + assumption.
    - eapply cumul_red_l ; try eassumption.
      econstructor. assumption.
    - eapply cumul_red_r ; try eassumption.
      econstructor. assumption.
  Qed.

  Lemma conv_cumul_l :
    forall Γ u v,
      Σ ;;; Γ |- u == v ->
      Σ ;;; Γ |- u <= v.
  Proof.
    intros Γ u v h. now eapply conv_alt_cumul.
  Qed.

  Lemma conv_refl' :
    forall leq Γ t,
      conv leq Σ Γ t t.
  Proof.
    intros leq Γ t.
    destruct leq.
    - cbn. constructor. apply conv_alt_refl. reflexivity.
    - cbn. constructor. apply cumul_refl'.
  Qed.

  Lemma conv_conv :
    forall {Γ leq u v},
      ∥ Σ ;;; Γ |- u == v ∥ ->
      conv leq Σ Γ u v.
  Proof.
    intros Γ leq u v h.
    destruct leq.
    - assumption.
    - destruct h. cbn.
      constructor. now eapply conv_alt_cumul.
  Qed.

  Lemma eq_term_conv :
    forall {Γ u v},
      eq_term (global_ext_constraints Σ) u v ->
      Σ ;;; Γ |- u = v.
  Proof.
    intros Γ u v e.
    constructor.
    - eapply cumul_refl.
      eapply eq_term_leq_term. assumption.
    - eapply cumul_refl.
      eapply eq_term_leq_term.
      eapply eq_term_sym.
      assumption.
  Qed.

  Global Instance conv_trans' :
    forall leq Γ, Transitive (conv leq Σ Γ).
  Proof.
    intros leq Γ u v w h1 h2.
    destruct leq.
    - cbn in *. destruct h1, h2. constructor.
      eapply conv_alt_trans ; eassumption.
    - cbn in *. destruct h1, h2. constructor. eapply cumul_trans ; eassumption.
  Qed.

  Lemma red_conv_l :
    forall leq Γ u v,
      red (fst Σ) Γ u v ->
      conv leq Σ Γ u v.
  Proof.
    intros leq Γ u v h.
    induction h.
    - apply conv_refl'.
    - eapply conv_trans' ; try eassumption.
      destruct leq.
      + simpl. destruct IHh. constructor.
        eapply conv_alt_red_l; eauto.
      + simpl. constructor.
        eapply cumul_red_l.
        * eassumption.
        * eapply cumul_refl'.
  Qed.

  Lemma red_conv_r :
    forall leq Γ u v,
      red (fst Σ) Γ u v ->
      conv leq Σ Γ v u.
  Proof.
    intros leq Γ u v h.
    induction h.
    - apply conv_refl'.
    - eapply conv_trans' ; try eassumption.
      destruct leq.
      + simpl. destruct IHh. constructor.
        eapply conv_alt_red_r; eauto.
      + simpl. constructor.
        eapply cumul_red_r.
        * eapply cumul_refl'.
        * assumption.
  Qed.

  Lemma conv_Prod leq Γ na1 na2 A1 A2 B1 B2 :
      Σ ;;; Γ |- A1 == A2 ->
      conv leq Σ (Γ,, vass na1 A1) B1 B2 ->
      conv leq Σ Γ (tProd na1 A1 B1) (tProd na2 A2 B2).
  Proof.
    intros h1 h2; destruct leq.
    - simpl in *. destruct h2 as [h2]. constructor.
      eapply conv_alt_trans => //.
      + eapply conv_Prod_r. eassumption.
      + eapply conv_Prod_l. eassumption.
    - simpl in *. destruct h2 as [h2]. constructor.
      eapply cumul_trans. auto.
      + eapply cumul_Prod_r. eassumption.
      + eapply conv_cumul_l. eapply conv_Prod_l. assumption.
  Qed.

  Lemma cumul_Case_c :
    forall Γ indn p brs u v,
      Σ ;;; Γ |- u == v ->
      Σ ;;; Γ |- tCase indn p u brs <= tCase indn p v brs.
  Proof.
    intros Γ [ind n] p brs u v h.
    induction h.
    - constructor. constructor.
      + eapply eq_term_refl.
      + assumption.
      + eapply All2_same.
        intros. split ; eauto.
        reflexivity.
    - eapply cumul_red_l ; eauto.
      constructor. assumption.
    - eapply cumul_red_r ; eauto.
      constructor. assumption.
  Qed.

  Lemma cumul_Proj_c :
    forall Γ p u v,
      Σ ;;; Γ |- u == v ->
      Σ ;;; Γ |- tProj p u <= tProj p v.
  Proof.
    intros Γ p u v h.
    induction h.
    - eapply cumul_refl. constructor. assumption.
    - eapply cumul_red_l ; try eassumption.
      econstructor. assumption.
    - eapply cumul_red_r ; try eassumption.
      econstructor. assumption.
  Qed.

  Lemma conv_App_l :
    forall {Γ f g x},
      Σ ;;; Γ |- f == g ->
      Σ ;;; Γ |- tApp f x == tApp g x.
  Proof.
    intros Γ f g x h.
    induction h.
    - constructor. constructor.
      + assumption.
      + apply eq_term_refl.
    - eapply conv_alt_red_l ; eauto.
      econstructor. assumption.
    - eapply conv_alt_red_r ; eauto.
      econstructor. assumption.
  Qed.

  Lemma App_conv :
    forall Γ t1 t2 u1 u2,
      Σ ;;; Γ |- t1 == t2 ->
      Σ ;;; Γ |- u1 == u2 ->
      Σ ;;; Γ |- tApp t1 u1 == tApp t2 u2.
  Proof.
    intros. etransitivity.
    eapply conv_App_l; tea.
    eapply conv_App_r; tea.
  Qed.

  Lemma conv_Case_c :
    forall Γ indn p brs u v,
      Σ ;;; Γ |- u == v ->
      Σ ;;; Γ |- tCase indn p u brs == tCase indn p v brs.
  Proof.
    intros Γ [ind n] p brs u v h.
    induction h.
    - constructor. constructor.
      + eapply eq_term_refl.
      + assumption.
      + eapply All2_same.
        intros. split ; eauto. reflexivity.
    - eapply conv_alt_red_l ; eauto.
      constructor. assumption.
    - eapply conv_alt_red_r ; eauto.
      constructor. assumption.
  Qed.

  Lemma conv_Proj_c :
    forall Γ p u v,
      Σ ;;; Γ |- u == v ->
      Σ ;;; Γ |- tProj p u == tProj p v.
  Proof.
    intros Γ p u v h.
    induction h.
    - eapply conv_alt_refl. constructor. assumption.
    - eapply conv_alt_red_l ; try eassumption.
      econstructor. assumption.
    - eapply conv_alt_red_r ; try eassumption.
      econstructor. assumption.
  Qed.

  Lemma conv_Lambda_l :
    forall Γ na A b na' A',
      Σ ;;; Γ |- A == A' ->
      Σ ;;; Γ |- tLambda na A b == tLambda na' A' b.
  Proof.
    intros Γ na A b na' A' h.
    induction h.
    - eapply conv_alt_refl. constructor.
      + assumption.
      + eapply eq_term_refl.
    - eapply conv_alt_red_l ; try eassumption.
      econstructor. assumption.
    - eapply conv_alt_red_r ; try eassumption.
      econstructor. assumption.
  Qed.

  Lemma conv_Lambda_r :
    forall Γ na A b b',
      Σ ;;; Γ,, vass na A |- b == b' ->
      Σ ;;; Γ |- tLambda na A b == tLambda na A b'.
  Proof.
    intros Γ na A b b' h.
    induction h.
    - eapply conv_alt_refl. constructor.
      + eapply eq_term_refl.
      + assumption.
    - eapply conv_alt_red_l ; try eassumption.
      econstructor. assumption.
    - eapply conv_alt_red_r ; try eassumption.
      econstructor. assumption.
  Qed.

  Lemma cumul_LetIn_bo :
    forall Γ na ty t u u',
      Σ ;;; Γ ,, vdef na ty t |- u <= u' ->
      Σ ;;; Γ |- tLetIn na ty t u <= tLetIn na ty t u'.
  Proof.
    intros Γ na ty t u u' h.
    induction h.
    - eapply cumul_refl. constructor.
      all: try eapply eq_term_refl.
      assumption.
    - eapply cumul_red_l ; try eassumption.
      econstructor. assumption.
    - eapply cumul_red_r ; try eassumption.
      econstructor. assumption.
  Qed.

  Lemma cumul_Lambda_r :
    forall Γ na A b b',
      Σ ;;; Γ,, vass na A |- b <= b' ->
      Σ ;;; Γ |- tLambda na A b <= tLambda na A b'.
  Proof.
    intros Γ na A b b' h.
    induction h.
    - eapply cumul_refl. constructor.
      + eapply eq_term_refl.
      + assumption.
    - eapply cumul_red_l ; try eassumption.
      econstructor. assumption.
    - eapply cumul_red_r ; try eassumption.
      econstructor. assumption.
  Qed.

  Lemma cumul_it_mkLambda_or_LetIn :
    forall Δ Γ u v,
      Σ ;;; (Δ ,,, Γ) |- u <= v ->
      Σ ;;; Δ |- it_mkLambda_or_LetIn Γ u <= it_mkLambda_or_LetIn Γ v.
  Proof.
    intros Δ Γ u v h. revert Δ u v h.
    induction Γ as [| [na [b|] A] Γ ih ] ; intros Δ u v h.
    - assumption.
    - simpl. cbn. eapply ih.
      eapply cumul_LetIn_bo. assumption.
    - simpl. cbn. eapply ih.
      eapply cumul_Lambda_r. assumption.
  Qed.

  Lemma cumul_it_mkProd_or_LetIn :
    forall Δ Γ B B',
      Σ ;;; (Δ ,,, Γ) |- B <= B' ->
      Σ ;;; Δ |- it_mkProd_or_LetIn Γ B <= it_mkProd_or_LetIn Γ B'.
  Proof.
    intros Δ Γ B B' h.
    induction Γ as [| [na [b|] A] Γ ih ] in Δ, B, B', h |- *.
    - assumption.
    - simpl. cbn. eapply ih.
      eapply cumul_LetIn_bo. assumption.
    - simpl. cbn. eapply ih.
      eapply cumul_Prod_r. assumption.
  Qed.

  Lemma mkApps_conv_weak :
    forall Γ u1 u2 l,
      Σ ;;; Γ |- u1 == u2 ->
      Σ ;;; Γ |- mkApps u1 l == mkApps u2 l.
  Proof.
    intros Γ u1 u2 l. induction l in u1, u2 |- *; cbn. trivial.
    intros X. apply IHl. now apply conv_App_l.
  Qed.


  Lemma context_relation_length P Γ Γ' :
    context_relation P Γ Γ' -> #|Γ| = #|Γ'|.
  Proof.
    induction 1; cbn; congruence.
  Qed.


  Lemma conv_Lambda leq Γ na1 na2 A1 A2 t1 t2 :
      Σ ;;; Γ |- A1 == A2 ->
      conv leq Σ (Γ ,, vass na1 A1) t1 t2 ->
      conv leq Σ Γ (tLambda na1 A1 t1) (tLambda na2 A2 t2).
  Proof.
    intros X H. destruct leq; cbn in *; sq.
    - etransitivity. eapply conv_Lambda_r; tea.
      now eapply conv_Lambda_l.
    - etransitivity. eapply cumul_Lambda_r; tea.
      eapply conv_cumul_l, conv_Lambda_l; tea.
  Qed.

  Lemma conva_LetIn_tm Γ na na' ty t t' u :
      Σ ;;; Γ |- t == t' ->
      Σ ;;; Γ |- tLetIn na t ty u == tLetIn na' t' ty u.
  Proof.
    induction 1.
    - constructor 1. constructor; try reflexivity.
      assumption.
    - econstructor 2; tea. now constructor.
    - econstructor 3; tea. now constructor.
  Qed.

  Lemma conva_LetIn_ty Γ na na' ty ty' t u :
      Σ ;;; Γ |- ty == ty' ->
      Σ ;;; Γ |- tLetIn na t ty u == tLetIn na' t ty' u.
  Proof.
    induction 1.
    - constructor 1. constructor; try reflexivity.
      assumption.
    - econstructor 2; tea. now constructor.
    - econstructor 3; tea. now constructor.
  Qed.

  Lemma conva_LetIn_bo Γ na ty t u u' :
      Σ ;;; Γ ,, vdef na ty t |- u == u' ->
      Σ ;;; Γ |- tLetIn na ty t u == tLetIn na ty t u'.
  Proof.
    induction 1.
    - constructor 1. now constructor. 
    - econstructor 2; tea. now constructor.
    - econstructor 3; tea. now constructor.
  Qed.

  Lemma conv_LetIn leq Γ na1 na2 t1 t2 A1 A2 u1 u2 :
      Σ;;; Γ |- t1 == t2 ->
      Σ;;; Γ |- A1 == A2 ->
      conv leq Σ (Γ ,, vdef na1 t1 A1) u1 u2 ->
      conv leq Σ Γ (tLetIn na1 t1 A1 u1) (tLetIn na2 t2 A2 u2).
  Proof.
    intros X H H'. destruct leq; cbn in *; sq.
    - etransitivity. eapply conva_LetIn_bo; tea.
      etransitivity. eapply conva_LetIn_tm; tea.
      eapply conva_LetIn_ty with (na := na1); tea.
    - etransitivity. eapply cumul_LetIn_bo; tea.
      etransitivity. eapply conv_cumul_l, conva_LetIn_tm; tea.
      eapply conv_cumul_l, conva_LetIn_ty with (na := na1); tea.
  Qed.

  Lemma conv_conv_ctx leq Γ Γ' T U :
    conv leq Σ Γ T U ->
    conv_context Σ Γ Γ' ->
    conv leq Σ Γ' T U.
  Proof.
    destruct leq; cbn; intros; sq.
    eapply conv_alt_conv_ctx; eassumption.
    eapply cumul_conv_ctx; eassumption.
  Qed.


  Lemma it_mkLambda_or_LetIn_conv' leq Γ Δ1 Δ2 t1 t2 :
      conv_context Σ (Γ ,,, Δ1) (Γ ,,, Δ2) ->
      conv leq Σ (Γ ,,, Δ1) t1 t2 ->
      conv leq Σ Γ (it_mkLambda_or_LetIn Δ1 t1) (it_mkLambda_or_LetIn Δ2 t2).
  Proof.
    induction Δ1 in Δ2, t1, t2 |- *; intros X Y.
    - apply context_relation_length in X.
      destruct Δ2; cbn in *; [trivial|].
      rewrite app_length in X; lia.
    - apply context_relation_length in X as X'.
      destruct Δ2 as [|c Δ2]; simpl in *; [rewrite app_length in X'; lia|].
      dependent destruction X.
      + eapply IHΔ1; tas; cbn.
        inv c0. eapply conv_Lambda; tea.
      + eapply IHΔ1; tas; cbn.
        inversion c0; subst; eapply conv_LetIn; auto.
  Qed.

  Lemma it_mkLambda_or_LetIn_conv Γ Δ1 Δ2 t1 t2 :
      conv_context Σ (Γ ,,, Δ1) (Γ ,,, Δ2) ->
      Σ ;;; Γ ,,, Δ1 |- t1 == t2 ->
      Σ ;;; Γ |- it_mkLambda_or_LetIn Δ1 t1 == it_mkLambda_or_LetIn Δ2 t2.
  Proof.
    induction Δ1 in Δ2, t1, t2 |- *; intros X Y.
    - apply context_relation_length in X.
      destruct Δ2; cbn in *; [trivial|].
      exfalso. rewrite app_length in X; lia.
    - apply context_relation_length in X as X'.
      destruct Δ2 as [|c Δ2]; simpl in *; [exfalso; rewrite app_length in X'; lia|].
      dependent destruction X.
      + eapply IHΔ1; tas; cbn.
        inv c0. etransitivity. eapply conv_Lambda_r; tea.
        now eapply conv_Lambda_l.
      + eapply IHΔ1; tas; cbn.
        etransitivity. eapply conva_LetIn_bo; tea. inv c0.
        eapply conva_LetIn_ty; tea.
        etransitivity. eapply conva_LetIn_tm; tea.
        eapply conva_LetIn_ty with (na := na); tea.
  Qed.

  Lemma red_lambda_inv Γ na A1 b1 T :
    red Σ Γ (tLambda na A1 b1) T ->
    ∑ A2 b2, (T = tLambda na A2 b2) *
             red Σ Γ A1 A2 * red Σ (Γ ,, vass na A1) b1 b2.
  Proof.
    intros.
    eapply red_alt in X. eapply clos_rt_rt1n_iff in X.
    depind X.
    - eexists _, _; intuition eauto.
    - depelim r; solve_discr; specialize (IHX _ _ _ _ eq_refl);
      destruct IHX as [A2 [B2 [[-> ?] ?]]].
      * eexists _, _; intuition eauto.
        now eapply red_step with M'.
        eapply PCUICConfluence.red_red_ctx; eauto.
        constructor; auto. eapply All2_local_env_red_refl.
        red. auto.
      * eexists _, _; intuition eauto.
        now eapply red_step with M'.
  Qed.

  Lemma Lambda_conv_inv :
    forall leq Γ na1 na2 A1 A2 b1 b2,
      wf_local Σ Γ ->
      conv leq Σ Γ (tLambda na1 A1 b1) (tLambda na2 A2 b2) ->
      ∥ Σ ;;; Γ |- A1 == A2 ∥ /\ conv leq Σ (Γ ,, vass na1 A1) b1 b2.
  Proof.
    intros * wfΓ.
    destruct leq; simpl in *.
    - destruct 1.
      eapply conv_alt_red in X as [l [r [[redl redr] eq]]].
      eapply red_lambda_inv in redl as [A1' [b1' [[-> ?] ?]]].
      eapply red_lambda_inv in redr as [A2' [b2' [[-> ?] ?]]].
      depelim eq. assert (Σ ;;; Γ |- A1 == A2).
      { eapply conv_alt_trans with A1'; auto.
        eapply conv_alt_trans with A2'; auto.
        constructor. assumption.
        apply conv_alt_sym; auto. }
      split; constructor; auto.
      eapply conv_alt_trans with b1'; auto.
      eapply conv_alt_trans with b2'; auto.
      constructor; auto.
      apply conv_alt_sym; auto.
      eapply conv_alt_conv_ctx; eauto.
      constructor; auto. reflexivity. constructor. now apply conv_alt_sym.
    - destruct 1.
      eapply cumul_alt in X as [l [r [[redl redr] eq]]].
      eapply red_lambda_inv in redl as [A1' [b1' [[-> ?] ?]]].
      eapply red_lambda_inv in redr as [A2' [b2' [[-> ?] ?]]].
      depelim eq. assert (Σ ;;; Γ |- A1 == A2).
      { eapply conv_alt_trans with A1'; auto.
        eapply conv_alt_trans with A2'; auto.
        constructor. assumption.
        apply conv_alt_sym; auto. }
      split; constructor; auto.
      eapply red_cumul_cumul; tea.
      eapply cumul_trans with b2'; auto.
      constructor; auto.
      eapply cumul_conv_ctx; tas. eapply red_cumul_cumul_inv; tea.
      reflexivity. symmetry in X.
      constructor. reflexivity. now constructor.
  Qed.

End Inversions.
