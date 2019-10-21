(* Distributed under the terms of the MIT license.   *)
Set Warnings "-notation-overridden".

From Equations Require Import Equations.
From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICWeakeningEnv PCUICWeakening
     PCUICSubstitution PCUICClosed PCUICInversion PCUICEquality
     PCUICReduction PCUICCumulativity PCUICGeneration
     PCUICParallelReductionConfluence PCUICConfluence
     PCUICContextConversion PCUICConversion PCUICUnivSubst.

Require Import ssreflect ssrbool.
Require Import String.
From MetaCoq Require Import LibHypsNaming.
Local Open Scope string_scope.
Set Asymmetric Patterns.
From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.
Require Import CMorphisms CRelationClasses.

Set Equations With UIP.
Set Printing Universes.

Section Principality.
  Context {cf : checker_flags}.
  Context (Σ : global_env_ext).
  Context (wfΣ : wf Σ).

  Definition Is_conv_to_Arity Σ Γ T :=
    exists T', ∥ red Σ Γ T T' ∥ /\ isArity T'.

  Lemma Is_conv_to_Arity_inv :
    forall Γ T,
      Is_conv_to_Arity Σ Γ T ->
      (exists na A B, ∥ red Σ Γ T (tProd na A B) ∥) \/
      (exists na b B t, ∥ red Σ Γ T (tLetIn na b B t) ∥) \/
      (exists u, ∥ red Σ Γ T (tSort u) ∥).
  Proof.
    intros Γ T [T' [r a]].
    destruct T'.
    all: try contradiction.
    - right. right. eexists. eassumption.
    - left. eexists _, _, _. eassumption.
    - right. left. eexists _, _, _, _. eassumption.
  Qed.

  Lemma invert_red_sort Γ u v :
    red Σ Γ (tSort u) v -> v = tSort u.
  Proof.
    intros H; apply red_alt in H.
    generalize_eqs H.
    induction H; simplify *. depind r.
    solve_discr.
    reflexivity.
    eapply IHclos_refl_trans2. f_equal. auto.
  Qed.

  Lemma invert_cumul_sort_r Γ C u :
    Σ ;;; Γ |- C <= tSort u ->
               ∑ u', red Σ Γ C (tSort u') * leq_universe (global_ext_constraints Σ) u' u.
  Proof.
    intros Hcum.
    eapply cumul_alt in Hcum as [v [v' [[redv redv'] leqvv']]].
    eapply invert_red_sort in redv' as ->.
    depelim leqvv'. exists s. intuition eauto.
  Qed.

  Lemma invert_cumul_sort_l Γ C u :
    Σ ;;; Γ |- tSort u <= C ->
               ∑ u', red Σ Γ C (tSort u') * leq_universe (global_ext_constraints Σ) u u'.
  Proof.
    intros Hcum.
    eapply cumul_alt in Hcum as [v [v' [[redv redv'] leqvv']]].
    eapply invert_red_sort in redv as ->.
    depelim leqvv'. exists s'. intuition eauto.
  Qed.

  Lemma invert_red_prod Γ na A B v :
    red Σ Γ (tProd na A B) v ->
    ∑ A' B', (v = tProd na A' B') *
             (red Σ Γ A A') *
             (red Σ (vass na A :: Γ) B B').
  Proof.
    intros H. apply red_alt in H.
    generalize_eqs H. revert na A B.
    induction H; simplify_dep_elim.
    depelim r. solve_discr.
    do 2 eexists. repeat split; eauto with pcuic.
    do 2 eexists. repeat split; eauto with pcuic.
    do 2 eexists. repeat split; eauto with pcuic.
    specialize (IHclos_refl_trans1 _ _ _ eq_refl).
    destruct IHclos_refl_trans1 as (? & ? & (-> & ?) & ?). auto.
    specialize (IHclos_refl_trans2 _ _ _ eq_refl).
    destruct IHclos_refl_trans2 as (? & ? & (-> & ?) & ?).
    do 2 eexists. repeat split; eauto with pcuic.
    now transitivity x.
    transitivity x0; auto.
    eapply PCUICConfluence.red_red_ctx. eauto. eauto.
    constructor. eapply All2_local_env_red_refl. red. auto.
  Qed.

  Lemma invert_cumul_prod_r Γ C na A B :
    Σ ;;; Γ |- C <= tProd na A B ->
    ∑ na' A' B', red Σ.1 Γ C (tProd na' A' B') *
                 (Σ ;;; Γ |- A == A') *
                 (Σ ;;; (Γ ,, vass na A) |- B' <= B).
  Proof.
    intros Hprod.
    eapply cumul_alt in Hprod as [v [v' [[redv redv'] leqvv']]].
    eapply invert_red_prod in redv' as (A' & B' & ((-> & Ha') & ?)) => //.
    depelim leqvv'.
    do 3 eexists; intuition eauto.
    eapply conv_alt_trans with A'; auto.
    eapply conv_alt_sym; auto.
    constructor; auto.
    eapply cumul_trans with B'; auto.
    constructor. eapply leqvv'2.
    now eapply red_cumul_inv.
  Qed.

  Lemma eq_term_upto_univ_conv_arity_l :
    forall Re Rle Γ u v,
      isArity u ->
      eq_term_upto_univ Re Rle u v ->
      Is_conv_to_Arity Σ Γ v.
  Proof.
    intros Re Rle Γ u v a e.
    induction u in Γ, a, v, Rle, e |- *. all: try contradiction.
    all: dependent destruction e.
    - eexists. split.
      + constructor. constructor.
      + reflexivity.
    - simpl in a.
      eapply IHu2 in e2. 2: assumption.
      destruct e2 as [b'' [[r] ab]].
      exists (tProd na' a' b''). split.
      + constructor. eapply red_prod_r. eassumption.
      + simpl. assumption.
    - simpl in a.
      eapply IHu3 in e3. 2: assumption.
      destruct e3 as [u'' [[r] au]].
      exists (tLetIn na' t' ty' u''). split.
      + constructor. eapply red_letin.
        all: try solve [ constructor ].
        eassumption.
      + simpl. assumption.
  Qed.

  Lemma eq_term_upto_univ_conv_arity_r :
    forall Re Rle Γ u v,
      isArity u ->
      eq_term_upto_univ Re Rle v u ->
      Is_conv_to_Arity Σ Γ v.
  Proof.
    intros Re Rle Γ u v a e.
    induction u in Γ, a, v, Rle, e |- *. all: try contradiction.
    all: dependent destruction e.
    - eexists. split.
      + constructor. constructor.
      + reflexivity.
    - simpl in a.
      eapply IHu2 in e2. 2: assumption.
      destruct e2 as [b'' [[r] ab]].
      exists (tProd na0 a0 b''). split.
      + constructor. eapply red_prod_r. eassumption.
      + simpl. assumption.
    - simpl in a.
      eapply IHu3 in e3. 2: assumption.
      destruct e3 as [u'' [[r] au]].
      exists (tLetIn na0 t ty u''). split.
      + constructor. eapply red_letin.
        all: try solve [ constructor ].
        eassumption.
      + simpl. assumption.
  Qed.

  Lemma isArity_subst :
    forall u v k,
      isArity u ->
      isArity (u { k := v }).
  Proof.
    intros u v k h.
    induction u in v, k, h |- *. all: try contradiction.
    - simpl. constructor.
    - simpl in *. eapply IHu2. assumption.
    - simpl in *. eapply IHu3. assumption.
  Qed.

  Lemma isArity_red1 :
    forall Γ u v,
      red1 Σ Γ u v ->
      isArity u ->
      isArity v.
  Proof.
    intros Γ u v h a.
    induction u in Γ, v, h, a |- *. all: try contradiction.
    - dependent destruction h.
      apply (f_equal nApp) in H as eq. simpl in eq.
      rewrite nApp_mkApps in eq. simpl in eq.
      destruct args. 2: discriminate.
      simpl in H. discriminate.
    - dependent destruction h.
      + apply (f_equal nApp) in H as eq. simpl in eq.
        rewrite nApp_mkApps in eq. simpl in eq.
        destruct args. 2: discriminate.
        simpl in H. discriminate.
      + assumption.
      + simpl in *. eapply IHu2. all: eassumption.
    - dependent destruction h.
      + simpl in *. apply isArity_subst. assumption.
      + apply (f_equal nApp) in H as eq. simpl in eq.
        rewrite nApp_mkApps in eq. simpl in eq.
        destruct args. 2: discriminate.
        simpl in H. discriminate.
      + assumption.
      + assumption.
      + simpl in *. eapply IHu3. all: eassumption.
  Qed.

  Lemma invert_cumul_arity_r :
    forall (Γ : context) (C : term) T,
      isArity T ->
      Σ;;; Γ |- C <= T ->
      Is_conv_to_Arity Σ Γ C.
  Proof.
    intros Γ C T a h.
    induction h.
    - eapply eq_term_upto_univ_conv_arity_r. all: eassumption.
    - forward IHh by assumption. destruct IHh as [v' [[r'] a']].
      exists v'. split.
      + constructor. eapply red_trans.
        * eapply trans_red.
          -- constructor.
          -- eassumption.
        * assumption.
      + assumption.
    - eapply IHh. eapply isArity_red1. all: eassumption.
  Qed.

  Lemma invert_cumul_arity_l :
    forall (Γ : context) (C : term) T,
      isArity C ->
      Σ;;; Γ |- C <= T ->
      Is_conv_to_Arity Σ Γ T.
  Proof.
    intros Γ C T a h.
    induction h.
    - eapply eq_term_upto_univ_conv_arity_l. all: eassumption.
    - eapply IHh. eapply isArity_red1. all: eassumption.
    - forward IHh by assumption. destruct IHh as [v' [[r'] a']].
      exists v'. split.
      + constructor. eapply red_trans.
        * eapply trans_red.
          -- constructor.
          -- eassumption.
        * assumption.
      + assumption.
  Qed.

  Lemma invert_cumul_prod_l Γ C na A B :
    Σ ;;; Γ |- tProd na A B <= C ->
               ∑ na' A' B', red Σ.1 Γ C (tProd na' A' B') *
                            (Σ ;;; Γ |- A == A') *
                            (Σ ;;; (Γ ,, vass na A) |- B <= B').
  Proof.
    intros Hprod.
    eapply cumul_alt in Hprod as [v [v' [[redv redv'] leqvv']]].
    eapply invert_red_prod in redv as (A' & B' & ((-> & Ha') & ?)) => //.
    depelim leqvv'.
    do 3 eexists; intuition eauto.
    - eapply conv_alt_trans with A'; auto.
      now constructor.
    - eapply cumul_trans with B'; eauto.
      now eapply red_cumul.
      now constructor; apply leqvv'2.
  Qed.

  Lemma app_mkApps :
    forall u v t l,
      isApp t = false ->
      tApp u v = mkApps t l ->
      ∑ l',
        (l = l' ++ [v])%list ×
        u = mkApps t l'.
  Proof.
    intros u v t l h e.
    induction l in u, v, t, e, h |- * using list_rect_rev.
    - cbn in e. subst. cbn in h. discriminate.
    - rewrite <- mkApps_nested in e. cbn in e.
      exists l. inversion e. subst. auto.
  Qed.

  (* TODO Duplicate of red_mkApps_tInd?? *)
  Lemma invert_red_ind :
    forall Γ ind ui l T,
      red Σ.1 Γ (mkApps (tInd ind ui) l) T ->
      ∑ l',
        T = mkApps (tInd ind ui) l' ×
        All2 (red Σ Γ) l l'.
  Proof.
    intros Γ ind ui l T h.
    dependent induction h.
    - exists l. split ; auto. apply All2_same. intro. constructor.
    - clear h.
      destruct IHh as [l'' [? ha]]. subst.
      dependent induction r.
      all: try solve [
        apply (f_equal decompose_app) in H ;
        rewrite !decompose_app_mkApps in H ; auto ;
        cbn in H ; inversion H
      ].
      + symmetry in H. apply app_mkApps in H ; auto.
        destruct H as [l' [? ?]]. subst.
        specialize IHr with (1 := eq_refl).
        apply All2_app_inv_r in ha as [l1 [l2 [? [h1 h2]]]]. subst.
        specialize IHr with (1 := h1).
        destruct IHr as [l [? ha]]. subst.
        exists (l ++ [M2])%list. rewrite <- mkApps_nested. split ; auto.
        apply All2_app ; auto.
      + symmetry in H. apply app_mkApps in H ; auto.
        destruct H as [l' [? ?]]. subst.
        exists (l' ++ [N2])%list. rewrite <- mkApps_nested. split ; auto.
        apply All2_app_inv_r in ha as [l1 [l2 [? [h1 h2]]]]. subst.
        apply All2_app ; auto.
        dependent destruction h2. dependent destruction h2.
        repeat constructor. eapply red_trans ; eauto.
  Qed.

  Lemma invert_cumul_ind_l :
    forall Γ ind ui l T,
      Σ ;;; Γ |- mkApps (tInd ind ui) l <= T ->
      ∑ ui' l',
        red Σ.1 Γ T (mkApps (tInd ind ui') l') ×
        R_universe_instance (eq_universe Σ) ui ui' ×
        All2 (fun a a' => Σ ;;; Γ |- a = a') l l'.
  Proof.
    intros Γ ind ui l T h.
    eapply cumul_alt in h as [v [v' [[redv redv'] leqvv']]].
    eapply invert_red_ind in redv as [l' [? ha]]. subst.
    eapply eq_term_upto_univ_mkApps_l_inv in leqvv'
      as [u [l'' [[e ?] ?]]].
    subst.
    dependent destruction e.
    eexists _,_. split ; eauto. split ; auto.
    eapply All2_trans.
    - intros x y z h1 h2. eapply conv_trans ; eauto.
    - eapply All2_impl ; eauto.
      intros x y h. eapply red_conv. assumption.
    - eapply All2_impl ; eauto.
      intros x y h. eapply eq_term_conv. assumption.
  Qed.

  Lemma invert_cumul_ind_r :
    forall Γ ind ui l T,
      Σ ;;; Γ |- T <= mkApps (tInd ind ui) l ->
      ∑ ui' l',
        red Σ.1 Γ T (mkApps (tInd ind ui') l') ×
        R_universe_instance (eq_universe Σ) ui' ui ×
        All2 (fun a a' => Σ ;;; Γ |- a == a') l l'.
  Proof.
    intros Γ ind ui l T h.
    eapply cumul_alt in h as [v [v' [[redv redv'] leqvv']]].
    eapply invert_red_ind in redv' as [l' [? ?]]. subst.
    eapply eq_term_upto_univ_mkApps_r_inv in leqvv'
      as [u [l'' [[e ?] ?]]].
    subst.
    dependent destruction e.
    eexists _,_. split ; eauto. split ; auto.
    eapply All2_trans.
    - intros x y z h1 h2. eapply conv_alt_trans ; eauto.
    - eapply All2_impl ; eauto.
    - eapply All2_swap.
      eapply All2_impl ; eauto.
      intros x y h. eapply conv_alt_sym; auto. now constructor.
  Qed.

  Ltac pih :=
    lazymatch goal with
    | ih : forall _ _ _, _ -> _ ;;; _ |- ?u : _ -> _,
    h1 : _ ;;; _ |- ?u : _,
    h2 : _ ;;; _ |- ?u : _
    |- _ =>
  specialize (ih _ _ _ h1 h2)
  end.


  Ltac insum :=
    match goal with
    | |- ∑ x : _, _ =>
      eexists
    end.

  Ltac intimes :=
    match goal with
    | |- _ × _ =>
      split
    end.

  Ltac outsum :=
    match goal with
    | ih : ∑ x : _, _ |- _ =>
      destruct ih as [? ?]
    end.

  Ltac outtimes :=
    match goal with
    | ih : _ × _ |- _ =>
      destruct ih as [? ?]
    end.

  Arguments equiv {A B}.
  Arguments equiv_inv {A B}.

  Lemma cumul_sort_confluence {Γ A u v} :
    Σ ;;; Γ |- A <= tSort u ->
    Σ ;;; Γ |- A <= tSort v ->
    ∑ v', (Σ ;;; Γ |- A == tSort v') *
          (leq_universe (global_ext_constraints Σ) v' u /\
           leq_universe (global_ext_constraints Σ) v' v).
  Proof.
    move=> H H'.
    eapply invert_cumul_sort_r in H as [u'u ?].
    eapply invert_cumul_sort_r in H' as [vu ?].
    destruct p, p0.
    destruct (red_confluence wfΣ r r0).
    destruct p.
    eapply invert_red_sort in r1.
    eapply invert_red_sort in r2. subst. noconf r2.
    exists u'u. split; auto.
  Qed.

  Lemma isWfArity_sort Γ u :
    wf_local Σ Γ ->
    isWfArity typing Σ Γ (tSort u).
  Proof.
    move=> wfΓ. red. exists [], u. intuition auto.
  Qed.

  Instance conv_alt_transitive Γ : Transitive (fun x y => Σ ;;; Γ |- x == y).
  Proof. intros x y z; eapply conv_alt_trans. auto. Qed.

  Theorem principal_typing {Γ u A B} : Σ ;;; Γ |- u : A -> Σ ;;; Γ |- u : B ->
    ∑ C, Σ ;;; Γ |- C <= A  ×  Σ ;;; Γ |- C <= B × Σ ;;; Γ |- u : C.
  Admitted.

End Principality.
