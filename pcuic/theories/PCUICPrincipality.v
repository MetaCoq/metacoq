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

  Definition Is_conv_to_Arity Σ Γ T := exists T', ∥red Σ Γ T T'∥ /\ isArity T'.
 
  Lemma Is_conv_to_Arity_inv Γ T :
    Is_conv_to_Arity Σ Γ T ->
    (exists na A B, ∥red Σ Γ T (tProd na A B)∥) \/ (exists u, ∥red Σ Γ T (tSort u)∥).
  Admitted.

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

  Lemma invert_cumul_arity_r (Γ : context) (C : term) T :
    wf_local Σ Γ ->
    isArity T ->
    Σ;;; Γ |- C <= T -> Is_conv_to_Arity Σ Γ C.
  Proof.
    revert Γ C; induction T; cbn in *; intros Γ C wfΓ ? ?; try tauto.
    - eapply invert_cumul_sort_r in X as (? & ? & ?).
      exists (tSort x). split; sq; eauto.
    - eapply invert_cumul_prod_r in X as (? & ? & ? & [] & ?); eauto.
      (* eapply IHT2 in c0 as (? & ? & ?); eauto. sq. *)

      (* exists (tProd x x0 x2). split; sq; cbn; eauto. *)
      (* etransitivity. eauto. *)
      (* eapply PCUICReduction.red_prod_r. *)

    (*   eapply context_conversion_red. eauto. 2:eauto. *)
    (*   + econstructor. clear; induction Γ. econstructor. destruct a, decl_body. econstructor. eauto. econstructor. econstructor. eauto. econstructor. eauto. econstructor. *)

    (*   econstructor. 2:eauto. 2:econstructor; eauto. 2:cbn. admit. admit. *)
    (* -   admit. *)
  Admitted.                       (* invert_cumul_arity_r *)

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

  Lemma invert_cumul_arity_l (Γ : context) (C : term) T :
    wf_local Σ Γ ->
    isArity C ->
    Σ;;; Γ |- C <= T -> Is_conv_to_Arity Σ Γ T.
  Proof.
    revert Γ T; induction C; cbn in *; intros Γ T wfΓ ? ?; try tauto.
    - eapply invert_cumul_sort_l in X as (? & ? & ?).
      exists (tSort x). split; sq; eauto.
    - eapply invert_cumul_prod_l in X as (? & ? & ? & [] & ?); eauto.
      eapply IHC2 in c0 as (? & ? & ?); eauto. sq.

      exists (tProd x x0 x2). split; sq; cbn; eauto.
      etransitivity. eauto.
      eapply PCUICReduction.red_prod_r.

      (*   eapply context_conversion_red. eauto. 2:eauto. *)
      (*   econstructor. eapply conv_context_refl; eauto.  *)

      (*   econstructor. 2:eauto. 2:econstructor; eauto. 2:cbn. admit. admit. *)
      (* - eapply invert_cumul_letin_l in X; eauto. *)
  Admitted.                       (* invert_cumul_arity_l *)

  Lemma invert_red_letin Γ C na d ty b :
    red Σ.1 Γ (tLetIn na d ty b) C ->
    (∑ na' d' ty' b',
     (red Σ.1 Γ C (tLetIn na' d' ty' b') *
      (Σ ;;; Γ |- d = d') *
      (Σ ;;; Γ |- ty = ty') *
      (Σ ;;; (Γ ,, vdef na d ty) |- b <= b'))) +
    (red Σ.1 Γ (subst10 d b) C)%type.
  Proof.
    intros wfHlet.
    (* eapply cumul_alt in Hlet. *)
    (* destruct Hlet as [v [v' [[redv redv'] leqvv']]]. *)
    (* eapply cumul_alt. *)
    (* exists v, v'. repeat split; auto. *)
  Admitted.

  Lemma invert_cumul_letin_l Γ C na d ty b :
    Σ ;;; Γ |- tLetIn na d ty b <= C ->
               (* (∑ na' d' ty' b', *)
               (*  (red Σ Γ C (tLetIn na' d' ty' b') * *)
               (*   (Σ ;;; Γ |- d = d') * *)
               (*   (Σ ;;; Γ |- ty = ty') * *)
                                                          (*   (Σ ;;; (Γ ,, vdef na d ty) |- b <= b'))) + *)
               (Σ ;;; Γ |- subst10 d b <= C).
  Proof.
    intros Hlet.
    eapply cumul_alt in Hlet.
    destruct Hlet as [v [v' [[redv redv'] leqvv']]].
    eapply cumul_alt.
    exists v, v'. repeat split; auto.
  Admitted.
  (* depelim redv. *)
  (* - depelim leqvv'. *)
  (*   exists na', ty', t', u'. *)
  (*   split. split. *)
  (*   split. auto. eapply conv_conv_alt. *)
  (*   now eapply conv_alt_refl. *)
  (*   now eapply conv_conv_alt, conv_alt_refl. *)
  (*   constructor. auto. *)
  (* - *)
  (*   eapply conv_conv_alt, conv_alt_refl. *)
  (*   eapply *)

  (*   eapply red_conv. *)
  (*   repeat split; auto. *)
  (*   eapply *)

  (* eapply red_ *)

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

  Lemma leq_universe_product_mon u u' v v' :
    leq_universe (global_ext_constraints Σ) u u' ->
    leq_universe (global_ext_constraints Σ) v v' ->
    leq_universe (global_ext_constraints Σ) (Universe.sort_of_product u v) (Universe.sort_of_product u' v').
  Proof.
  Admitted.

  Lemma isWfArity_sort Γ u :
    wf_local Σ Γ ->
    isWfArity typing Σ Γ (tSort u).
  Proof.
    move=> wfΓ. red. exists [], u. intuition auto.
  Qed.

  (* Duplicate *)
  (* Lemma eq_term_upto_univ_mkApps_r_inv : *)
  (*   forall Re Rle u l t, *)
  (*     eq_term_upto_univ Re Rle t (mkApps u l) -> *)
  (*     ∑ u' l', *)
  (*   eq_term_upto_univ Re Rle u' u * *)
  (*   All2 (eq_term_upto_univ Re Re) l' l * *)
  (*   (t = mkApps u' l'). *)
  (* Proof. *)
  (*   intros Re Rle u l t h. *)
  (*   induction l in u, t, h, Rle |- *. *)
  (*   - cbn in h. exists t, []. split ; auto. *)
  (*   - cbn in h. apply IHl in h as [u' [l' [[h1 h2] h3]]]. *)
  (*     dependent destruction h1. subst. *)
  (*     eexists. eexists. split; [ split | ]. *)
  (*     + eassumption. *)
  (*     + constructor. *)
  (*       * eassumption. *)
  (*       * eassumption. *)
  (*     + cbn. reflexivity. *)
  (* Qed. *)

  (* Duplicate *)
  (* Lemma invert_cumul_ind_r Γ t ind u args : *)
  (*   Σ ;;; Γ |- t <= mkApps (tInd ind u) args -> *)
  (*              ∑ u' args', red Σ Γ t (mkApps (tInd ind u') args') * *)
  (*                          All2 (leq_universe (global_ext_constraints Σ)) (map Universe.make u') (map Universe.make u) * *)
  (*                          All2 (fun a a' => Σ ;;; Γ |- a = a') args args'. *)
  (* Proof. *)
  (*   intros H. eapply cumul_alt in H. *)
  (*   destruct H as [v [v' [[redv redv'] leq]]]. *)
  (*   eapply red_mkApps_tInd in redv' as [args' [-> ?]]; eauto. *)
  (*   apply eq_term_upto_univ_mkApps_r_inv in leq as [u' [l' [[eqhd eqargs] Heq]]]. *)
  (*   subst v. depelim eqhd. *)
  (*   exists u0, l'. split; auto. *)
  (*   clear -eqargs a0. *)
  (*   induction eqargs in a0, args |- *; depelim a0. constructor. *)
  (*   constructor. apply conv_trans with y. now eapply red_conv. *)
  (*   apply conv_conv_alt. constructor. now apply eq_term_sym. *)
  (*   now apply IHeqargs. *)
  (* Qed. *)


  Instance conv_alt_transitive Γ : Transitive (fun x y => Σ ;;; Γ |- x == y).
  Proof. intros x y z; eapply conv_alt_trans. auto. Qed.

  Theorem principal_typing {Γ u A B} : Σ ;;; Γ |- u : A -> Σ ;;; Γ |- u : B ->
    ∑ C, Σ ;;; Γ |- C <= A  ×  Σ ;;; Γ |- C <= B × Σ ;;; Γ |- u : C.
  Proof.
    intros hA hB.
    induction u in Γ, A, B, hA, hB |- * using term_forall_list_rec.
    - apply inversion_Rel in hA as iA.
      destruct iA as [decl [? [e ?]]].
      apply inversion_Rel in hB as iB.
      destruct iB as [decl' [? [e' ?]]].
      rewrite e' in e. inversion e. subst. clear e.
      repeat insum. repeat intimes.
      all: try eassumption.
      constructor ; assumption.
    - apply inversion_Var in hA. destruct hA.
    - apply inversion_Evar in hA. destruct hA.
    - apply inversion_Sort in hA as iA.
      apply inversion_Sort in hB as iB.
      repeat outsum. repeat outtimes. subst.
      inversion e. subst.
      repeat insum. repeat intimes.
      all: try eassumption.
      (* * left; eexists _, _; intuition auto. *)
      * constructor ; assumption.
    - apply inversion_Prod in hA as [dom1 [codom1 iA]]; auto.
      apply inversion_Prod in hB as [dom2 [codom2 iB]]=> //.
      repeat outsum. repeat outtimes.
      repeat pih.
      destruct IHu1 as [dom Hdom].
      destruct IHu2 as [codom Hcodom].
      repeat outsum. repeat outtimes.
      destruct (cumul_sort_confluence c3 c4) as [dom' [dom'dom [leq0 leq1]]].
      destruct (cumul_sort_confluence c1 c2) as [codom' [codom'dom [leq0' leq1']]].
      exists (tSort (Universe.sort_of_product dom' codom')).
      repeat split.
      * eapply cumul_trans. auto. 2:eapply c0.
        constructor. constructor.
        apply leq_universe_product_mon; auto.
      * eapply cumul_trans. auto. 2:eapply c.
        constructor. constructor.
        apply leq_universe_product_mon; auto.
      (* * left; eexists _, _; intuition eauto. now eapply typing_wf_local in t4. *)
      * eapply type_Prod.
        eapply type_Cumul; eauto.
        left; eapply isWfArity_sort. now eapply typing_wf_local in t1.
        eapply conv_alt_cumul; auto.
        eapply type_Cumul; eauto.
        left; eapply isWfArity_sort. now eapply typing_wf_local in t3.
        eapply conv_alt_cumul; auto.

    - apply inversion_Lambda in hA => //.
      apply inversion_Lambda in hB => //.
      repeat outsum. repeat outtimes.
      repeat pih.
      repeat outsum. repeat outtimes.
      apply invert_cumul_prod_l in c0 as [na' [A' [B' [[redA u1eq] ?]]]] => //.
      apply invert_cumul_prod_l in c as [na'' [A'' [B'' [[redA' u1eq'] ?]]]] => //.
      exists (tProd n u1 x3).
      repeat split; auto.
      * eapply cumul_trans with (tProd na' A' B'); auto.
        eapply congr_cumul_prod => //.
        eapply cumul_trans with x2 => //.
        now eapply red_cumul_inv.
      * eapply cumul_trans with (tProd na'' A'' B''); auto.
        eapply congr_cumul_prod => //.
        eapply cumul_trans with x0 => //.
        now eapply red_cumul_inv.
      (* * destruct i as [[ctx [s [? ?]]]|?]. *)
      (*   ** left; eexists _, s. simpl. intuition eauto. *)
      (*      generalize (destArity_spec [] x3). rewrite e. *)
      (*      simpl. move => ->. rewrite destArity_it_mkProd_or_LetIn. simpl. *)
      (*      intuition eauto. *)
      (*      unfold snoc. simpl. now rewrite app_context_assoc. *)
      (*   ** right. red. destruct i as [s us]. *)
      (*      exists (Universe.sort_of_product x s). *)
      (*      eapply type_Prod; auto. *)
      * eapply type_Lambda; eauto.

    - eapply inversion_LetIn in hA; auto.
      eapply inversion_LetIn in hB; auto.
      destruct hA as [tty [bty ?]].
      destruct hB as [tty' [bty' ?]].
      repeat outtimes.
      specialize (IHu3 _ _ _ t4 t1) as [C' ?].
      repeat outtimes.
      exists (tLetIn n u1 u2 C'). repeat split.
      * clear IHu1 IHu2.
        eapply invert_cumul_letin_l in c0 => //.
        eapply invert_cumul_letin_l in c => //.
        eapply cumul_trans with (C' {0 := u1}). auto.
        eapply red_cumul. eapply red_step.
        econstructor. auto.
        eapply cumul_trans with (bty {0 := u1}) => //.
        eapply (substitution_cumul Σ Γ [vdef n u1 u2] []) => //.
        constructor; auto.
        now eapply typing_wf_local in t3.
        red. exists tty' => //.
        pose proof (cons_let_def Σ Γ [] [] n u1 u2).
        rewrite !subst_empty in X. apply X. constructor.
        auto.
      * clear IHu1 IHu2.
        eapply invert_cumul_letin_l in c0 => //.
        eapply invert_cumul_letin_l in c => //.
        eapply cumul_trans with (C' {0 := u1}). auto.
        eapply red_cumul. eapply red_step.
        econstructor. auto.
        eapply cumul_trans with (bty' {0 := u1}) => //.
        eapply (substitution_cumul Σ Γ [vdef n u1 u2] []) => //.
        constructor; auto.
        now eapply typing_wf_local in t3.
        red. exists tty' => //.
        pose proof (cons_let_def Σ Γ [] [] n u1 u2).
        rewrite !subst_empty in X. apply X. constructor.
        auto.
      (* * destruct i as [[ctx' [s' [? ?]]]|[s Hs]]. *)
      (*   ** left. red. simpl. *)
      (*      generalize (destArity_spec [] C'); rewrite e. *)
      (*      simpl. move => ->. *)
      (*      rewrite destArity_it_mkProd_or_LetIn. simpl. *)
      (*      eexists _, _; intuition eauto. *)
      (*      now rewrite app_context_assoc. *)
      (*   ** right. exists s. eapply type_Cumul. econstructor; eauto. *)
      (*      left. red. exists [], s. intuition auto. now eapply typing_wf_local in t2. *)
      (*      eapply red_cumul. eapply red1_red. constructor. *)
      * eapply type_LetIn; eauto.

    - eapply inversion_App in hA as [na [dom [codom [tydom [tyarg tycodom]]]]] => //.
      eapply inversion_App in hB as [na' [dom' [codom' [tydom' [tyarg' tycodom']]]]] => //.
      specialize (IHu2 _ _ _ tyarg tyarg').
      specialize (IHu1 _ _ _ tydom tydom').
      destruct IHu1, IHu2.
      repeat outtimes.
      apply invert_cumul_prod_r in c1 as [? [A' [B' [[redA u1eq] ?]]]] => //.
      apply invert_cumul_prod_r in c2 as [? [A'' [B'' [[redA' u1eq'] ?]]]] => //.
      destruct (red_confluence wfΣ redA redA') as [nfprod [redl redr]].
      eapply invert_red_prod in redl as [? [? [[? ?] ?]]] => //. subst.
      eapply invert_red_prod in redr as [? [? [[? ?] ?]]] => //. noconf e.
      assert(Σ ;;; Γ |- A' == A'').
      { apply conv_alt_trans with x3 => //.
        now eapply red_conv_alt. apply conv_alt_sym; auto. }
      assert(Σ ;;; Γ ,, vass x1 A' |- B' == B'').
      { apply conv_alt_trans with x4 => //.
        now eapply red_conv_alt. apply conv_alt_sym; auto.
        eapply conv_alt_conv_ctx; eauto. constructor; auto. eapply conv_ctx_refl.
        constructor. now eapply conv_alt_sym. }
      exists (B' {0 := u2}).
      repeat split.
      * eapply cumul_trans with (codom {0 := u2}) => //.
        eapply substitution_cumul0 => //. eapply c1.
      * eapply cumul_trans with (B'' {0 := u2}); eauto.
        eapply substitution_cumul0 => //. eapply conv_alt_cumul in X0; eauto.
        eapply cumul_trans with (codom' {0 := u2}) => //.
        eapply substitution_cumul0 => //. eauto.
      * eapply type_App.
        2:eapply tyarg.
        eapply type_Cumul. eapply t0.
        instantiate (1 := x1).
        (* Needs to show wf arity preservation? needing validity? or just inversion on tydom ? *)
        admit.
        eapply cumul_trans with (tProd x1 A' B')=> //.
        eapply red_cumul; eauto.
        eapply congr_cumul_prod.
        eapply conv_alt_sym; eauto.
        eapply cumul_refl'.

    - eapply inversion_Const in hA as [decl ?] => //.
      eapply inversion_Const in hB as [decl' ?] => //.
      repeat outtimes.
      exists (subst_instance_constr u (cst_type decl)).
      red in d0, d. rewrite d0 in d. noconf d.
      repeat intimes; eauto.
      eapply type_Const; eauto.

    - eapply inversion_Ind in hA as [mdecl [idecl [? [Hdecl ?]]]] => //.
      eapply inversion_Ind in hB as [mdecl' [idecl' [? [Hdecl' ?]]]] => //.
      repeat outtimes.
      exists (subst_instance_constr u (ind_type idecl)).
      red in Hdecl, Hdecl'. destruct Hdecl as [? ?].
      destruct Hdecl' as [? ?]. red in H, H1.
      rewrite H1 in H; noconf H.
      rewrite H2 in H0; noconf H0.
      repeat intimes; eauto.
      eapply type_Ind; eauto.
      split; eauto.

    - eapply inversion_Construct in hA as [mdecl [idecl [? [? [Hdecl ?]]]]] => //.
      eapply inversion_Construct in hB as [mdecl' [idecl' [? [? [Hdecl' ?]]]]] => //.
      repeat outtimes.
      red in Hdecl, Hdecl'.
      destruct Hdecl as [[? ?] ?].
      destruct Hdecl' as [[? ?] ?].
      red in H, H2. rewrite H2 in H. noconf H.
      rewrite H3 in H0. noconf H0.
      rewrite H4 in H1. noconf H1.
      exists (type_of_constructor mdecl (i1, t0, n1) (i, n) u).
      repeat split; eauto.
      eapply type_Construct; eauto. repeat split; eauto.

    - destruct p as [ind n].
      eapply inversion_Case in hA=>//.
      eapply inversion_Case in hB=>//.
      repeat outsum. repeat outtimes. simpl in *.
      repeat outtimes.
      subst.
      destruct d, d0. red in H, H1.
      rewrite H in H1. noconf H1. rewrite H0 in H2. noconf H2.
      specialize (IHu1 _ _ _ t t1). clear t t1.
      specialize (IHu2 _ _ _ t0 t2). clear t0 t2.
      repeat outsum. repeat outtimes.
      eapply invert_cumul_ind_r in c3 as [u' [x0' [redr [redu ?]]]].
      eapply invert_cumul_ind_r in c4 as [u'' [x9' [redr' [redu' ?]]]].
      assert (All2 (fun a a' => Σ ;;; Γ |- a == a') x0 x9).
      { destruct (red_confluence wfΣ redr redr').
        destruct p.
        eapply red_mkApps_tInd in r as [args' [? ?]]; auto.
        eapply red_mkApps_tInd in r0 as [args'' [? ?]]; auto.
        subst. solve_discr.
        clear -wfΣ a1 a2 a3 a4.
        eapply (All2_impl (Q:=fun x y => Σ ;;; Γ |- x == y)) in a3; auto using red_conv.
        eapply (All2_impl (Q:=fun x y => Σ ;;; Γ |- y == x)) in a4; auto using conv_alt_sym, red_conv.
        pose proof (All2_trans _ (conv_alt_transitive _) _ _ _ a1 a3).
        apply All2_sym in a4.
        pose proof (All2_trans _ (conv_alt_transitive _) _ _ _ X a4).
        eapply (All2_impl (Q:=fun x y => Σ ;;; Γ |- y == x)) in a2; auto using conv_sym, red_conv.
        apply All2_sym in a2.
        apply (All2_trans _ (conv_alt_transitive _) _ _ _ X0 a2).
        intros ? ? ?. eapply conv_alt_sym. assumption. auto.
      }
      clear redr redr' a1 a2.
      exists (mkApps u1 (skipn (ind_npars x10) x9 ++ [u2])); repeat split; auto.

      2:{ revert e2.
          rewrite /types_of_case.
          destruct instantiate_params eqn:Heq => //.
          destruct (destArity [] t1) as [[args s']|] eqn:eqar => //.
          destruct (destArity [] x12) as [[args' s'']|] eqn:eqx12 => //.
          destruct (destArity [] x2) as [[ctxx2 sx2]|] eqn:eqx2 => //.
          destruct map_option_out eqn:eqbrs => //.
          intros [=]. subst.
          eapply (type_Case _ _ _ x8). eauto. repeat split; eauto. auto.
          eapply t0. rewrite /types_of_case.
          rewrite Heq eqar eqx2 eqbrs. reflexivity.
          admit. admit. eapply type_Cumul. eauto.
          all:admit. }

      admit.

    - destruct s as [[ind k] pars]; simpl in *.
      eapply inversion_Proj in hA=>//.
      eapply inversion_Proj in hB=>//.
      repeat outsum. repeat outtimes.
      simpl in *.
      destruct d0, d. destruct H, H1. red in H, H1.
      rewrite H1 in H; noconf H.
      rewrite H4 in H3; noconf H3.
      destruct H0, H2.
      rewrite H2 in H; noconf H.
      rewrite -e in e0.
      specialize (IHu _ _ _ t t1) as [C' [? [? ?]]].
      eapply invert_cumul_ind_r in c1 as [u' [x0' [redr [redu ?]]]].
      eapply invert_cumul_ind_r in c2 as [u'' [x9' [redr' [redu' ?]]]].
      exists (subst0 (u :: List.rev x3) (subst_instance_constr x t2)).
      repeat split; auto.
      admit.

      eapply refine_type. eapply type_Proj. repeat split; eauto.
      simpl. eapply type_Cumul. eapply t0.
      right. 2:eapply red_cumul; eauto.
      admit. rewrite H3. simpl. simpl in H0.
      rewrite -H0. admit.
      simpl.
      admit.

    - eapply inversion_Fix in hA as [decl [hguard [nthe [wfΓ [? ?]]]]]=>//.
      eapply inversion_Fix in hB as [decl' [hguard' [nthe' [wfΓ' [? ?]]]]]=>//.
      rewrite nthe' in nthe; noconf nthe.
      exists (dtype decl); repeat split; eauto.
      eapply type_Fix; eauto.

    - eapply inversion_CoFix in hA as [decl [allow [nthe [wfΓ [? ?]]]]]=>//.
      eapply inversion_CoFix in hB as [decl' [allpw [nthe' [wfΓ' [? ?]]]]]=>//.
      rewrite nthe' in nthe; noconf nthe.
      exists (dtype decl); repeat split; eauto.
      eapply type_CoFix; eauto.
  Admitted.

End Principality.
