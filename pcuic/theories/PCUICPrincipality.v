(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICTyping PCUICGlobalEnv
     PCUICWeakeningEnvTyp PCUICSubstitution PCUICEquality
     PCUICReduction PCUICCumulativity PCUICConfluence PCUICClosed PCUICClosedTyp
     PCUICContextConversion PCUICContextConversionTyp PCUICConversion PCUICInversion PCUICUnivSubst
     PCUICArities PCUICValidity PCUICInductives PCUICInductiveInversion
     PCUICSR PCUICCumulProp PCUICWfUniverses
     PCUICOnFreeVars PCUICWellScopedCumulativity.

Require Import ssreflect ssrbool.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.
Set Equations With UIP.

(** We show that principal types are derivable, without relying on normalization.
  The principal type is burried in the proof here, but [PCUICSafeRetyping.type_of]
  gives an explicit computation, but its definition and correctness proof requires
  completeness of weak-head-reduction. *)

Section Principality.
  Context {cf : checker_flags}.
  Context (Σ : global_env_ext).
  Context (wfΣ : wf_ext Σ).

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

  Lemma isWfArity_sort Γ u :
    wf_local Σ Γ ->
    wf_universe Σ u ->
    isWfArity Σ Γ (tSort u).
  Proof using Type.
    move=> wfΓ wfu.
    split. eapply isType_Sort; eauto. exists [], u. intuition auto.
  Qed.
  Hint Extern 10 (isWfArity _ _ (tSort _)) => apply isWfArity_sort : pcuic.

  Ltac int inv := intros B hB; eapply inv in hB; auto; split; [|econstructor; eauto].
  Hint Resolve wf_ext_wf : core.

  Theorem principal_type {Γ u A} : Σ ;;; Γ |- u : A ->
    ∑ C, (forall B, Σ ;;; Γ |- u : B -> Σ ;;; Γ ⊢ C ≤ B × Σ ;;; Γ |- u : C).
  Proof using wfΣ.
    intros hA.
    induction u in Γ, A, hA |- * using term_forall_list_ind.
    - apply inversion_Rel in hA as iA. 2: auto.
      destruct iA as [decl [? [e ?]]].
      eexists; int inversion_Rel.
      destruct hB as [decl' [? [e' ?]]].
      rewrite e' in e. noconf e.
      all: try eassumption.
    - apply inversion_Var in hA. destruct hA.
    - apply inversion_Evar in hA. destruct hA.
    - apply inversion_Sort in hA as iA. 2: auto.
      repeat outsum. repeat outtimes. subst.
      exists (tSort (Universe.super s)).
      int inversion_Sort.
      repeat outsum. repeat outtimes. now subst.
    - apply inversion_Prod in hA as [dom1 [codom1 iA]]; auto.
      repeat outtimes.
      specialize (IHu1 _ _ t) as [dom Hdom].
      specialize (IHu2 _ _ t0) as [codom Hcodom].
      destruct (Hdom _ t) as [e e'].
      eapply ws_cumul_pb_Sort_r_inv in e as [domu [red leq]].
      destruct (Hcodom _ t0) as [e e''].
      eapply ws_cumul_pb_Sort_r_inv in e as [codomu [cored coleq]].
      exists (tSort (Universe.sort_of_product domu codomu)).
      int inversion_Prod.
      repeat outsum; repeat outtimes.
      + etransitivity. 1: auto. 2:eapply w0.
        destruct (Hdom _ t1) as [le' u1'].
        eapply ws_cumul_pb_Sort_r_inv in le' as [u' [redu' leu']].
        destruct (Hcodom _ t2) as [le'' u2'].
        eapply ws_cumul_pb_Sort_r_inv in le'' as [u'' [redu'' leu'']].
        constructor => //. fvs. constructor.
        apply leq_universe_product_mon; auto.
        pose proof (closed_red_confluence red redu') as [v' [redl redr]].
        eapply invert_red_sort in redl.
        eapply invert_red_sort in redr. subst. now noconf redr.
        pose proof (closed_red_confluence cored redu'') as [v' [redl redr]].
        eapply invert_red_sort in redl.
        eapply invert_red_sort in redr. subst. now noconf redr.
      + eapply type_reduction; eauto. eapply red.
      + eapply type_reduction; eauto. eapply cored.

    - apply inversion_Lambda in hA => //; eauto.
      repeat outsum. repeat outtimes.
      destruct (IHu1 _ _ t) as [? ?].
      destruct (IHu2 _ _ t0) as [? ?].
      destruct (p _ t).
      destruct (p0 _ t0).
      exists (tProd n u1 x2).
      int inversion_Lambda.
      repeat outsum. repeat outtimes.
      etransitivity; eauto.
      apply ws_cumul_pb_Prod_l_inv in w2 as [na' [A' [B' [redA u1eq ?]]]] => //; auto.
      destruct (p0 _ t4).
      eapply ws_cumul_pb_Prod => //; auto.
      transitivity A' => //. now symmetry.

    - eapply inversion_LetIn in hA as (s1 & bty & Hu2 & Hu1 & Hu3 & Hcum); auto.
      destruct (IHu1 _ _ Hu1) as [? p].
      destruct (p _ Hu1).
      destruct (IHu2 _ _ Hu2) as [? p'].
      destruct (p' _ Hu2).
      destruct (IHu3 _ _ Hu3) as [? p''].
      destruct (p'' _ Hu3).
      exists (tLetIn n u1 u2 x1).
      int inversion_LetIn.
      destruct hB as (s1' & bty' & Hu2' & Hu1' & Hu3' & Hcum'); eauto.
      etransitivity; eauto.
      eapply ws_cumul_pb_LetIn; eauto using wt_cumul_pb_refl.
      now specialize (p'' _ Hu3') as [? ?].

    - eapply inversion_App in hA as [na [dom [codom [tydom [tyarg tycodom]]]]] => //; auto.
      destruct (IHu2 _ _ tyarg).
      destruct (IHu1 _ _ tydom).
      destruct (p _ tyarg). destruct (p0 _ tydom).
      apply ws_cumul_pb_Prod_r_inv in w0 as [? [A' [B' [redA eqann u1eq ?]]]] => //; auto.
      exists (subst [u2] 0 B').
      intros ? hB.
      eapply inversion_App in hB as [na' [dom' [codom' [tydom' [tyarg' tycodom']]]]] => //; auto.
      destruct (p0 _ tydom').
      destruct (p _ tyarg').
      apply ws_cumul_pb_Prod_r_inv in w1 as [? [A'' [B'' [redA' eqann' u1eq' ?]]]] => //; auto.
      destruct (closed_red_confluence redA redA') as [nfprod [redl redr]].
      eapply invert_red_prod in redl as [? [? [? ? ?]]] => //. subst.
      eapply invert_red_prod in redr as [? [? [? ? ?]]] => //. noconf e.
      all:auto.
      assert(Σ ;;; Γ ⊢ A' = A'').
      { transitivity x3 => //; eauto using red_ws_cumul_pb.
        symmetry. now apply red_ws_cumul_pb. }
      assert(Σ ;;; Γ ,, vass x1 A' ⊢ B' = B'').
      { transitivity x4 => //.
        - now eapply red_ws_cumul_pb.
        - symmetry. eapply (ws_cumul_pb_ws_cumul_ctx (pb:=Conv)); tea.
          2:eapply red_ws_cumul_pb; tea.
          constructor; auto. eapply ws_cumul_ctx_pb_refl. fvs.
          constructor. reflexivity. now symmetry. }
      split.
      etransitivity; eauto.
      eapply (substitution0_ws_cumul_pb (na:=na') (T:=dom')) => //.
      have convctx : Σ ⊢ Γ ,, vass na' dom' = Γ ,, vass x1 A'.
      { constructor. apply ws_cumul_ctx_pb_refl. fvs. constructor => //. transitivity A'' => //.
        now symmetry. now symmetry. }
      transitivity B'' => //. eapply (ws_cumul_pb_ws_cumul_ctx (pb':=Conv)); tea.
      now apply ws_cumul_pb_eq_le.
      eapply type_App'. tea.
      eapply type_reduction; eauto. eapply redA.
      eapply (type_ws_cumul_pb (pb:=Cumul)); eauto.
      { eapply validity in t0; auto.
        eapply isType_red in t0; [|exact redA].
        eapply isType_tProd in t0 as [? ?]; eauto. }
      transitivity dom' => //. transitivity A''.
      all:apply ws_cumul_pb_eq_le; symmetry => //.

    - eapply inversion_Const in hA as [decl ?] => //; auto.
      repeat outtimes.
      eexists; int inversion_Const.
      destruct hB as [decl' [wf [declc' [cu cum]]]].
      now rewrite -(declared_constant_inj _ _ d declc') in cum.

    - eapply inversion_Ind in hA as [mdecl [idecl [? [Hdecl ?]]]] => //; auto.
      repeat outtimes.
      exists (subst_instance u (ind_type idecl)).
      int inversion_Ind. destruct hB as [mdecl' [idecl' [? [Hdecl' ?]]]] => //.
      red in Hdecl, Hdecl'. destruct Hdecl as [? ?].
      destruct Hdecl' as [? ?]. red in H, H1.
      rewrite H1 in H; noconf H.
      rewrite H2 in H0; noconf H0.
      repeat intimes; eauto. now destruct p.

    - eapply inversion_Construct in hA as [mdecl [idecl [? [? [Hdecl ?]]]]] => //; auto.
      repeat outtimes.
      exists (type_of_constructor mdecl x (i, n) u).
      int inversion_Construct. destruct hB as [mdecl' [idecl' [? [? [Hdecl' [? ?]]]]]] => //.
      red in Hdecl, Hdecl'.
      destruct Hdecl as [[? ?] ?].
      destruct Hdecl' as [[? ?] ?].
      red in H, H2. rewrite H2 in H. noconf H.
      rewrite H3 in H0. noconf H0.
      rewrite H4 in H1. now noconf H1.

    - assert (wf Σ) by auto.
      eapply inversion_Case in hA as (mdecl&idecl&isdecl&indices&[]&?); auto.
      destruct (IHu _ _ scrut_ty) as [? p0].
      destruct (p0 _ scrut_ty).
      eapply ws_cumul_pb_Ind_r_inv in w0 as [u' [x0' [redr redu ?]]]; auto.
      exists (mkApps ptm (indices ++ [u])); intros b hB; repeat split; auto.
      2:econstructor; eauto.
      eapply inversion_Case in hB as (mdecl'&idecl'&isdecl'&indices'&[]&?); tea. clear brs_ty0.
      destruct (declared_inductive_inj isdecl isdecl') as [-> ->].
      destruct (p0 _ scrut_ty0).
      eapply ws_cumul_pb_Ind_r_inv in w1 as [u'' [x9' [redr' redu' ?]]]; auto.
      assert (ws_cumul_pb_terms Σ Γ x0' x9').
      { destruct (closed_red_confluence redr redr') as [nf [r r0]].
        eapply invert_red_mkApps_tInd in r as [args' [? ?]]; auto.
        eapply invert_red_mkApps_tInd in r0 as [args'' [? ?]]; auto.
        subst. solve_discr.
        clear -wfΣ i a a0 a1 a2.
        transitivity args'; auto using red_terms_ws_cumul_pb_terms.
        now symmetry; apply red_terms_ws_cumul_pb_terms. }
      clear redr redr'.
      etransitivity; [|tea].
      eapply ws_cumul_pb_mkApps; auto. rewrite /ptm /predctx.
      * eapply PCUICGeneration.type_it_mkLambda_or_LetIn in pret_ty.
        eapply ws_cumul_pb_eq_le, wt_cumul_pb_refl. eapply pret_ty.
      * eapply All2_app. 2:constructor; auto.
        assert (ws_cumul_pb_terms Σ Γ (pparams p ++ indices) (pparams p ++ indices')).
        { transitivity x9'; tea. transitivity x0' => //. now symmetry. }
        eapply All2_app_inv in X3 as [] => //.
        eapply wt_cumul_pb_refl; tea.
      * split; eauto.
      * split; eauto.

    - destruct s as [ind k pars]; simpl in *.
      eapply inversion_Proj in hA=>//; auto.
      repeat outsum. repeat outtimes.
      simpl in *.
      specialize (IHu _ _ t) as [C HP].
      destruct (HP _ t).
      eapply ws_cumul_pb_Ind_r_inv in w0 as [u' [x0' [redr redu ?]]]; auto.
      exists (subst0 (u :: List.rev x0') (subst_instance u' (proj_type x3))).
      intros B hB.
      eapply inversion_Proj in hB=>//; auto.
      repeat outsum. repeat outtimes.
      simpl in *.
      destruct (declared_projection_inj d d0) as [-> [-> [-> ?]]]. subst x9.
      destruct (HP _ t1).
      eapply ws_cumul_pb_Ind_r_inv in w1 as [u'' [x0'' [redr' redu' ?]]]; auto.
      split; cycle 1.
      eapply type_reduction in t0. 2:exact redr.
      eapply (type_Proj _ _ _ _ _ _ _ _ _ _ d0); simpl; auto.
      now rewrite (All2_length a).
      destruct (closed_red_confluence redr redr') as [nf [redl redr'']].
      eapply invert_red_mkApps_tInd in redl as [? [-> conv]]; auto.
      eapply invert_red_mkApps_tInd in redr'' as [? [[=] conv']]; auto.
      solve_discr.
      etransitivity; eauto.
      assert (consistent_instance_ext Σ (ind_universes x6) u').
      { eapply type_reduction in t2. 2:eapply redr.
        eapply validity in t2; eauto.
        destruct t2 as [s Hs].
        eapply invert_type_mkApps_ind in Hs. intuition eauto. all:auto. eapply d. }
      assert (consistent_instance_ext Σ (ind_universes x6) x5).
        { eapply validity in t1; eauto.
          destruct t1 as [s Hs].
          eapply invert_type_mkApps_ind in Hs. intuition eauto. all:auto. eapply d. }
      set (p := {| proj_ind := ind; proj_npars := k; proj_arg := pars |}).
      transitivity (subst0 (u :: List.rev x0') (subst_instance x5 (proj_type x3))); cycle 1.
      eapply ws_cumul_pb_eq_le.
      assert (ws_cumul_pb_terms Σ Γ x0' x10).
      { transitivity x0'' => //.
        transitivity x0. auto using red_terms_ws_cumul_pb_terms.
        symmetry. auto using red_terms_ws_cumul_pb_terms. }
      eapply (substitution_ws_cumul_pb_subst_conv (Γ0 := projection_context ind x6 x7 u')
      (Γ1 := projection_context ind x6 x7 x5) (Δ := [])); auto.
      * eapply (projection_subslet _ _ _ _ _ _ p); eauto.
        simpl. eapply type_reduction; eauto. eapply redr. simpl.
        eapply type_reduction in t0. 2:eapply redr. eapply validity; eauto.
      * split.
        { eapply PCUICWeakeningTyp.weaken_wf_local; tea. pcuic. pcuic.
          eapply (wf_projection_context _ (p:=p)); tea. pcuic. }
        eapply (projection_subslet _ _ _ _ _ _ p); eauto.
        simpl. eapply validity; eauto.
      * constructor; auto. now eapply wt_cumul_pb_refl. now apply All2_rev.
      * eapply ws_cumul_pb_refl.
        { eapply wf_local_closed_context. cbn -[projection_context].
          eapply PCUICWeakeningTyp.weaken_wf_local; pcuic.
          eapply (wf_projection_context _ (p:=p)); pcuic. }
        eapply declared_projection_closed in d0; eauto.
        cbn in d0. len. rewrite (declared_minductive_ind_npars d) in d0.
        len. rewrite on_free_vars_subst_instance.
        rewrite closedn_on_free_vars //.
        eapply closed_upwards; tea. lia.
      * eapply (substitution_ws_cumul_pb (Γ:=Γ) (Γ' := projection_context ind x6 x7 u') (Γ'' := [])); auto.
        eapply (projection_subslet _ _ _ _ _ _ p); eauto.
        simpl. eapply type_reduction; eauto. eapply redr. simpl.
        eapply type_reduction in t0. 2:eapply redr.
        eapply validity; eauto. simpl in redu'.
        rewrite e0 in redu'.
        unshelve epose proof (projection_cumulative_indices d _ H H0 redu').
        { eapply (PCUICWeakeningEnv.weaken_lookup_on_global_env' _ _ _ (wfΣ : wf _) (proj1 (proj1 (proj1 d)))). }
        eapply on_declared_projection in d0; eauto.
        eapply weaken_ws_cumul_pb in X; eauto.

    - pose proof (typing_wf_local hA).
      apply inversion_Fix in hA as [decl [hguard [nthe [wfΓ [? [? ?]]]]]]=>//; auto.
      exists (dtype decl).
      intros B hB.
      eapply inversion_Fix in hB as [decl' [hguard' [nthe' [wfΓ' [? [? ?]]]]]]=>//; auto.
      rewrite nthe' in nthe; noconf nthe.
      repeat split; eauto.
      eapply type_Fix; eauto.

    - pose proof (typing_wf_local hA).
      apply inversion_CoFix in hA as [decl [hguard [nthe [wfΓ [? [? ?]]]]]]=>//; auto.
      exists (dtype decl).
      intros B hB.
      eapply inversion_CoFix in hB as [decl' [hguard' [nthe' [wfΓ' [? [? ?]]]]]]=>//; auto.
      rewrite nthe' in nthe; noconf nthe.
      repeat split; eauto.
      eapply type_CoFix; eauto.
    - apply inversion_Prim in hA as [prim_ty [cdecl []]] => //; pcuic.
      exists (tConst prim_ty []).
      intros B hB.
      apply inversion_Prim in hB as [prim_ty' [cdecl' []]] => //; pcuic.
      econstructor; tea.
  Qed.

  (** A weaker version that is often convenient to use. *)
  Lemma common_typing {Γ u A B} : Σ ;;; Γ |- u : A -> Σ ;;; Γ |- u : B ->
    ∑ C, Σ ;;; Γ ⊢ C ≤ A × Σ ;;; Γ ⊢ C ≤ B × Σ ;;; Γ |- u : C.
  Proof using wfΣ.
    intros hA hB.
    destruct (principal_type hA) as [P HP]; eauto.
    exists P; split; eauto.
    eapply HP; eauto.
  Qed.

End Principality.

Lemma principal_type_ind {cf:checker_flags} {Σ Γ c ind u u' args args'} {wfΣ: wf_ext Σ} :
  Σ ;;; Γ |- c : mkApps (tInd ind u) args ->
  Σ ;;; Γ |- c : mkApps (tInd ind u') args' ->
  (∑ ui',
    PCUICEquality.R_global_instance Σ.1 (eq_universe (global_ext_constraints Σ))
     (leq_universe (global_ext_constraints Σ)) (IndRef ind) #|args| ui' u *
    PCUICEquality.R_global_instance Σ.1 (eq_universe (global_ext_constraints Σ))
     (leq_universe (global_ext_constraints Σ)) (IndRef ind) #|args'| ui' u') *
  ws_cumul_pb_terms Σ Γ args args'.
Proof.
  intros h h'.
  destruct (common_typing _ wfΣ h h') as [C [l [r ty]]].
  eapply ws_cumul_pb_Ind_r_inv in l as [ui' [l' [red Ru eqargs]]]; auto.
  eapply ws_cumul_pb_Ind_r_inv in r as [ui'' [l'' [red' Ru' eqargs']]]; auto.
  destruct (closed_red_confluence red red') as [nf [redl redr]].
  eapply invert_red_mkApps_tInd in redl as [args'' [-> eq0]]; auto.
  eapply invert_red_mkApps_tInd in redr as [args''' [eqnf eq1]]; auto.
  solve_discr.
  split.
  assert (#|args| = #|args'|).
  now rewrite -(All2_length eqargs) -(All2_length eqargs') (All2_length a) (All2_length a0).
  exists ui'. split; auto.

  transitivity l'. now symmetry.
  transitivity args'' => //. now apply red_terms_ws_cumul_pb_terms.
  transitivity l''. symmetry. auto using red_terms_ws_cumul_pb_terms.
  now symmetry.
Qed.

Lemma eq_term_leq_term {cf:checker_flags} {Σ : global_env_ext} {x y} :
  eq_term Σ Σ x y ->
  leq_term Σ Σ x y.
Proof.
  eapply eq_term_upto_univ_impl; auto; typeclasses eauto.
Qed.

Lemma eq_term_empty_leq_term {cf:checker_flags} {Σ : global_env_ext} {x y} :
  eq_term empty_global_env Σ x y ->
  leq_term empty_global_env Σ x y.
Proof.
  eapply eq_term_upto_univ_impl; auto; typeclasses eauto.
Qed.

Lemma eq_term_empty_eq_term {cf:checker_flags} {Σ : global_env_ext} {x y} :
  eq_term empty_global_env Σ x y ->
  eq_term Σ Σ x y.
Proof.
  eapply eq_term_upto_univ_empty_impl; auto; typeclasses eauto.
Qed.

Lemma leq_term_empty_leq_term {cf:checker_flags} {Σ : global_env_ext} {x y} :
  leq_term empty_global_env Σ x y ->
  leq_term Σ Σ x y.
Proof.
  eapply eq_term_upto_univ_empty_impl; auto; typeclasses eauto.
Qed.

Lemma eq_context_empty_eq_context {cf:checker_flags} {Σ : global_env_ext} {x y} :
  eq_context_upto empty_global_env (eq_universe Σ) (eq_universe Σ) x y ->
  eq_context_upto Σ (eq_universe Σ) (eq_universe Σ) x y.
Proof.
  intros.
  eapply All2_fold_impl; tea.
  intros ???? []; constructor; eauto using eq_term_empty_eq_term.
  all:now apply eq_term_empty_eq_term.
Qed.

Notation eq_term_napp Σ n x y :=
  (eq_term_upto_univ_napp Σ (eq_universe Σ) (eq_universe Σ) n x y).

Notation leq_term_napp Σ n x y :=
    (eq_term_upto_univ_napp Σ (eq_universe Σ) (leq_universe Σ) n x y).

Lemma eq_term_upto_univ_napp_leq {cf:checker_flags} {Σ : global_env_ext} {n x y} :
  eq_term_napp Σ n x y ->
  leq_term_napp Σ n x y.
Proof.
  eapply eq_term_upto_univ_impl; auto; typeclasses eauto.
Qed.

Lemma R_global_instance_empty_universe_instance Re Rle ref napp u u' :
  R_global_instance empty_global_env Re Rle ref napp u u' ->
  R_universe_instance Re u u'.
Proof.
  rewrite /R_global_instance_gen.
  now rewrite global_variance_empty.
Qed.

Lemma eq_context_upto_inst_case_context {cf : checker_flags} {Σ : global_env_ext} pars pars' puinst puinst' ctx :
  All2 (eq_term_upto_univ empty_global_env (eq_universe Σ) (eq_universe Σ)) pars pars' ->
  R_universe_instance (eq_universe Σ) puinst puinst' ->
  eq_context_upto Σ.1 (eq_universe Σ) (eq_universe Σ) (inst_case_context pars puinst ctx)
    (inst_case_context pars' puinst' ctx).
Proof.
  intros onps oninst.
  rewrite /inst_case_context.
  eapply eq_context_upto_subst_context. tc.
  eapply eq_context_upto_univ_subst_instance; tc; auto.
  eapply All2_rev. eapply All2_impl; tea.
  intros. now eapply eq_term_empty_eq_term.
Qed.

Lemma typing_leq_term {cf:checker_flags} (Σ : global_env_ext) Γ t t' T T' :
  wf Σ.1 ->
  on_udecl Σ.1 Σ.2 ->
  Σ ;;; Γ |- t : T ->
  Σ ;;; Γ |- t' : T' ->
  leq_term empty_global_env Σ t' t ->
  (* No cumulativity of inductive types, as they can relate
    inductives in different sorts. *)
  Σ ;;; Γ |- t' : T.
Proof.
  intros wfΣ onu Ht.
  revert Σ wfΣ Γ t T Ht onu t' T'.
  eapply (typing_ind_env
  (fun Σ Γ t T =>
    forall (onu : on_udecl Σ.1 Σ.2),
    forall t' T' : term, Σ ;;; Γ |- t' : T' -> leq_term empty_global_env Σ t' t -> Σ;;; Γ |- t' : T)
  (fun Σ Γ => wf_local Σ Γ)); auto;intros Σ wfΣ Γ wfΓ; intros.
    1-13:match goal with
    [ H : leq_term _ _ _ _ |- _ ] => depelim H
    end.
  all:try solve [econstructor; eauto].

  - eapply inversion_Sort in X0 as [wf [wfs cum]]; auto.
    eapply type_Cumul' with (tSort (Universe.super s)).
    constructor; auto. eapply PCUICArities.isType_Sort; pcuic.
    apply cumul_Sort. now apply leq_universe_super.

  - eapply inversion_Prod in X4 as [s1' [s2' [Ha [Hb Hs]]]]; auto.
    specialize (X1 onu _ _ Ha).
    specialize (X1 (eq_term_empty_leq_term X5_1)).
    apply eq_term_empty_eq_term in X5_1.
    eapply context_conversion in Hb. 3:{ constructor. apply conv_ctx_refl. constructor.
      eassumption. constructor. eauto. }
    all:eauto.
    2:{ constructor; eauto. now exists s1. }
    specialize (X3 onu _ _ Hb X5_2).
    econstructor; eauto.
    apply leq_term_empty_leq_term in X5_2.
    eapply context_conversion; eauto.
    constructor; pcuic. constructor; try now symmetry; now constructor.
    pcuic.
    constructor; pcuic.
    constructor. now symmetry.

  - eapply inversion_Lambda in X4 as (s & B & dom & codom & cum); auto.
    specialize (X1 onu _ _ dom (eq_term_empty_leq_term X5_1)).
    apply eq_term_empty_eq_term in X5_1.
    assert(conv_context cumulAlgo_gen Σ (Γ ,, vass na ty) (Γ ,, vass n t)).
    { repeat constructor; pcuic. }
    specialize (X3 onu t0 B).
    forward X3 by eapply context_conversion; eauto; pcuic.
    eapply (type_ws_cumul_pb (pb:=Conv)).
    * econstructor. eauto. instantiate (1 := bty).
      eapply context_conversion; eauto; pcuic.
      constructor; pcuic. constructor; pcuic. symmetry; constructor; auto.
    * have tyl := type_Lambda _ _ _ _ _ _ _ X0 X2.
      now eapply PCUICValidity.validity in tyl.
    * eapply ws_cumul_pb_Prod; eauto.
      constructor; auto; fvs.
      eapply ws_cumul_pb_refl. now eapply typing_closed_ctx in codom.
      eapply type_closed, closedn_on_free_vars in X2.
      now len in X2; len.

  - eapply inversion_LetIn in X6 as (s1' & A & dom & bod & codom & cum); auto.
    specialize (X1 onu _ _ dom (eq_term_empty_leq_term X7_2)).
    specialize (X3 onu _ _ bod (eq_term_empty_leq_term X7_1)).
    apply eq_term_empty_eq_term in X7_1.
    apply eq_term_empty_eq_term in X7_2.
    assert(Σ ⊢ Γ ,, vdef na t ty = Γ ,, vdef n b b_ty).
    { constructor. eapply ws_cumul_ctx_pb_refl. fvs. constructor => //.
      constructor; fvs. constructor; fvs. }
    specialize (X5 onu u A).
    forward X5 by eapply closed_context_conversion; eauto; pcuic.
    specialize (X5 X7_3).
    eapply leq_term_empty_leq_term in X7_3.
    have uty : Σ ;;; Γ ,, vdef na t ty |- u : b'_ty.
    { eapply closed_context_conversion; eauto.
      pcuic. now symmetry. }
    eapply type_ws_cumul_pb.
    * econstructor. eauto. eauto.
      now instantiate (1 := b'_ty).
    * eapply PCUICValidity.validity; eauto.
      econstructor; eauto.
    * eapply (ws_cumul_pb_LetIn (pb:=Conv)); pcuic.
      constructor; auto; fvs.
      constructor; fvs.
      apply ws_cumul_pb_refl; fvs.

  - eapply inversion_App in X6 as (na' & A' & B' & hf & ha & cum); auto.
    unfold leq_term in X1.
    eapply eq_term_upto_univ_empty_impl in X7_1.
    specialize (X3 onu _ _ hf X7_1). all:try typeclasses eauto.
    specialize (X5 onu _ _ ha (eq_term_empty_leq_term X7_2)).
    eapply leq_term_empty_leq_term in X7_1.
    eapply eq_term_empty_eq_term in X7_2.
    eapply type_ws_cumul_pb.
    * eapply type_App'; [eapply X3|eapply X5].
    * eapply validity; pcuic.
      eapply type_App; eauto.
    * eapply ws_cumul_pb_eq_le.
      eapply validity in X2; auto.
      apply PCUICArities.isType_tProd in X2 as [tyA tyB].
      eapply (substitution_ws_cumul_pb_subst_conv (Γ0 := [vass na A]) (Γ1 := [vass na A]) (Δ := [])); pcuic.
      constructor. 2:constructor.
      constructor; fvs.

  - eapply inversion_Const in X1 as [decl' [wf [declc [cu cum]]]]; auto.
    eapply type_Cumul'; eauto.
    econstructor; eauto.
    eapply validity; eauto.
    econstructor; eauto.
    eapply eq_term_upto_univ_cumulSpec.
    pose proof (declared_constant_inj _ _ H declc); subst decl'.
    eapply PCUICUnivSubstitutionConv.eq_term_upto_univ_subst_instance; eauto; typeclasses eauto.

  - eapply inversion_Ind in X1 as [decl' [idecl' [wf [declc [cu cum]]]]]; auto.
    eapply type_Cumul'; eauto.
    econstructor; eauto.
    eapply validity; eauto.
    econstructor; eauto.
    eapply eq_term_upto_univ_cumulSpec.
    pose proof (declared_inductive_inj isdecl declc) as [-> ->].
    eapply PCUICUnivSubstitutionConv.eq_term_upto_univ_subst_instance; eauto; typeclasses eauto.

  - eapply inversion_Construct in X1 as [decl' [idecl' [cdecl' [wf [declc [cu cum]]]]]]; auto.
    eapply (type_ws_cumul_pb (pb:=Conv)); eauto.
    econstructor; eauto.
    eapply validity; eauto.
    econstructor; eauto.
    pose proof (declared_constructor_inj isdecl declc) as [-> [-> ->]].
    unfold type_of_constructor.
    transitivity (subst0 (inds (inductive_mind ind) u (ind_bodies mdecl))
    (subst_instance u0 cdecl'.(cstr_type))).
    * have clctx : is_closed_context (Γ ,,, (arities_context (ind_bodies mdecl))@[u0]).
      { rewrite on_free_vars_ctx_app. apply /andP ; split => //. fvs.
        erewrite PCUICOnFreeVars.on_free_vars_ctx_subst_instance.
        pose proof (declared_minductive_closed_arities declc).
        now eapply closed_ctx_on_free_vars in H0. }
      eapply (substitution_ws_cumul_pb_subst_conv (Δ := [])); eauto.
      eapply weaken_subslet; tea; eapply subslet_inds; tea; eapply isdecl.
      split; revgoals.
      eapply weaken_subslet; tea; eapply subslet_inds; tea; eapply isdecl.
      eapply PCUICWeakeningTyp.weaken_wf_local; tea.
      eapply (wf_arities_context_inst isdecl); tea.
      cbn. eapply conv_inds => //. fvs.
      simpl. eapply ws_cumul_pb_refl => //. tea.
      pose proof (declared_constructor_closed_gen_type declc) as cl.
      eapply closedn_on_free_vars in cl. len.
      rewrite -shiftnP_add. len in cl.
      now rewrite on_free_vars_subst_instance.
    * have cld : is_open_term (Γ ,,, arities_context (ind_bodies mdecl)) (cstr_type cdecl').
      { pose proof (declared_constructor_closed_gen_type declc) as cl.
        eapply closedn_on_free_vars in cl. len.
        rewrite -shiftnP_add. len in cl. exact cl. }
      constructor; auto. fvs.
      { eapply on_free_vars_subst. eapply inds_is_open_terms.
        len. len in cld. rewrite shiftnP_add.
        now rewrite on_free_vars_subst_instance. }
      { eapply on_free_vars_subst. eapply inds_is_open_terms.
        len. len in cld. rewrite shiftnP_add.
        now rewrite on_free_vars_subst_instance. }
      eapply PCUICEquality.subst_eq_term.
      eapply PCUICUnivSubstitutionConv.eq_term_upto_univ_subst_instance; eauto; typeclasses eauto.

  - eassert (ctx_inst _ _ _ _ _) as Hctxi by now eapply ctx_inst_impl with (1 := X5).
    assert (isType Σ Γ (mkApps ptm (indices ++ [c]))).
    { eapply validity. econstructor; eauto. all:split; eauto.
      solve_all. }
    eapply inversion_Case in X9 as (mdecl' & idecl' & decli' & indices' & data & cum); auto.
    destruct (declared_inductive_inj isdecl decli'). subst mdecl' idecl'.
    destruct data.
    unshelve epose proof (X7 _ _ _ scrut_ty (eq_term_empty_leq_term X10)); tea.
    pose proof (eq_term_empty_eq_term X10).
    destruct e as [eqpars [eqinst [eqpctx eqpret]]].
    eapply eq_term_empty_eq_term in eqpret.
    eapply type_ws_cumul_pb.
    * econstructor; eauto. all:split; eauto.
    * tas.
    * clear brs_ty.
      eapply ws_cumul_pb_eq_le.
      eapply ws_cumul_pb_mkApps; pcuic.
      rewrite /ptm. constructor. fvs.
      eapply PCUICGeneration.type_it_mkLambda_or_LetIn in pret_ty. subst predctx0; fvs.
      eapply PCUICGeneration.type_it_mkLambda_or_LetIn in pret. subst predctx; fvs.
      eapply PCUICEquality.eq_term_upto_univ_it_mkLambda_or_LetIn; tea. tc.
      rewrite /predctx.
      rewrite /case_predicate_context /case_predicate_context_gen.
      eapply eq_context_upto_map2_set_binder_name. tea.
      rewrite /pre_case_predicate_context_gen.
      eapply eq_context_upto_inst_case_context => //.
      eapply All2_app. 2:constructor; pcuic.
      specialize (X3 _ _ scrut_ty (eq_term_empty_leq_term X10)).
      unshelve epose proof (principal_type_ind scrut_ty X3) as [_ indconv]; tea.
      split; auto.
      eapply All2_app_inv in indconv as [convpars convinds] => //.
      exact (All2_length eqpars).
      constructor => //; fvs.

  - eapply inversion_Proj in X3 as (u' & mdecl' & idecl' & cdecl' & pdecl' & args' & inv); auto.
    intuition auto.
    specialize (X3 _ _ a0 (eq_term_empty_leq_term X4)).
    eapply eq_term_empty_eq_term in X4.
    assert (wf_ext Σ) by (split; assumption).
    pose proof (principal_type_ind X3 a0) as [Ruu' X3'].
    eapply (type_ws_cumul_pb (pb:=Conv)).
    * clear a0.
      econstructor; eauto.
      now rewrite (All2_length X3').
    * eapply PCUICValidity.validity; eauto.
      eapply type_Proj; eauto.
    * destruct (declared_projection_inj a isdecl) as [-> [-> [-> ->]]].
      set (ctx := PCUICInductives.projection_context p.(proj_ind) mdecl idecl u).
      have clctx : is_closed_context (Γ,,, ctx).
      { rewrite /ctx.
        eapply validity in X1.
        eapply isType_mkApps_Ind_inv in X1 as [parsubst [argsubst []]]; tea. 2:exact a.
        epose proof (wf_projection_context _ _ a c1).
        rewrite on_free_vars_ctx_app. apply /andP; split; fvs.
        eapply wf_local_closed_context in X1.
        eapply on_free_vars_ctx_impl; tea => //.
        move=> i //. }
      eapply (substitution_ws_cumul_pb_subst_conv (Γ0 := ctx) (Γ1 := ctx) (Δ := [])); eauto.
      + eapply PCUICInductives.projection_subslet; eauto.
        eapply validity in X3; auto.
      + split.
        eapply PCUICWeakeningTyp.weaken_wf_local; tea.
        eapply wf_projection_context; tea.
        eapply validity in X3.
        now eapply (isType_mkApps_Ind_inv _ a) in X3 as [? [? []]].
        eapply PCUICInductives.projection_subslet; eauto.
        eapply validity in X3; auto.
      + constructor. constructor; fvs.
        eapply All2_rev. eapply ws_cumul_pb_terms_refl => //; fvs.
      + rewrite /ctx; eapply ws_cumul_pb_refl => //.
        epose proof (declared_projection_closed a).
        rewrite on_free_vars_subst_instance; len. len.
        rewrite -(declared_minductive_ind_npars a).
        eapply closedn_on_free_vars in H0.
        now rewrite -plus_Sn_m -shiftnP_add.

  - eapply inversion_Fix in X2 as (decl' & fixguard' & Hnth & types' & bodies & wffix & cum); auto.
    eapply type_Cumul_alt.
    econstructor; eauto.
    eapply PCUICValidity.validity; eauto.
    econstructor. 3:eapply H0. all:eauto.
    eapply (All_impl X0); pcuicfo.
    apply infer_typing_sort_impl with id X2; now intros [].
    eapply (All_impl X1); pcuicfo; now destruct X2.
    eapply All2_nth_error in a; eauto.
    destruct a as [[[eqty _] _] _].
    constructor. eapply eq_term_empty_leq_term in eqty.
    now eapply leq_term_empty_leq_term.

  - eapply inversion_CoFix in X2 as (decl' & fixguard' & Hnth & types' & bodies & wfcofix & cum); auto.
    eapply type_Cumul_alt.
    econstructor; eauto.
    eapply PCUICValidity.validity; eauto.
    eapply type_CoFix. 3:eapply H0. all:eauto.
    eapply (All_impl X0); pcuicfo.
    apply infer_typing_sort_impl with id X2; now intros [].
    eapply (All_impl X1); pcuicfo; now destruct X2.
    eapply All2_nth_error in a; eauto.
    destruct a as [[[eqty _] _] _].
    constructor. apply eq_term_empty_leq_term in eqty.
    now eapply leq_term_empty_leq_term.

  - depelim X2.
    econstructor; tea.

  - eapply type_Cumul'.
    eapply X1; eauto. now exists s.
    auto.
Qed.

Lemma typing_eq_term {cf:checker_flags} (Σ : global_env_ext) Γ t t' T T' :
  wf_ext Σ ->
  Σ ;;; Γ |- t : T ->
  Σ ;;; Γ |- t' : T' ->
  eq_term empty_global_env Σ t t' ->
  Σ ;;; Γ |- t' : T.
Proof.
  intros wfΣ ht ht' eq.
  eapply typing_leq_term; eauto. apply wfΣ.
  now eapply eq_term_empty_leq_term.
Qed.

(* Print Assumptions principal_type. *)
