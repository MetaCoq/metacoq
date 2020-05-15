(* Distributed under the terms of the MIT license.   *)
Set Warnings "-notation-overridden".

From Coq Require Import String Bool List.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICTyping PCUICSubstitution PCUICEquality
     PCUICReduction PCUICCumulativity PCUICConfluence
     PCUICContextConversion PCUICConversion PCUICInversion PCUICUnivSubst
     PCUICArities PCUICValidity PCUICSR.

Require Import ssreflect.

Set Asymmetric Patterns.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

Set Equations With UIP.
Set Printing Universes.

Section Principality.
  Context {cf : checker_flags}.
  Context (Σ : global_env_ext).
  Context (wfΣ : wf Σ).

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
    ∑ v', (Σ ;;; Γ |- A = tSort v') *
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


  Lemma cumul_ind_confluence {Γ A ind u v l l'} :
    Σ ;;; Γ |- A <= mkApps (tInd ind u) l  ->
    Σ ;;; Γ |- A <= mkApps (tInd ind v) l' ->
    ∑ v' l'', (red Σ Γ A (mkApps (tInd ind v') l'')) *
          All2 (conv Σ Γ) l l'' *
          All2 (conv Σ Γ) l' l'' *          
          (R_universe_instance (eq_universe (global_ext_constraints Σ)) v' u /\
           R_universe_instance (eq_universe (global_ext_constraints Σ)) v' v).
  Proof.
    move=> H H'.
    eapply invert_cumul_ind_r in H as [u'u [l'u [redl [ru ?]]]].
    eapply invert_cumul_ind_r in H' as [vu [l''u [redr [ru' ?]]]].
    destruct (red_confluence wfΣ redl redr) as [nf [redl' redr']].
    eapply red_mkApps_tInd in redl'  as [args' [eqnf conv]].
    eapply red_mkApps_tInd in redr'  as [args'' [eqnf' conv']].
    rewrite eqnf in eqnf'. solve_discr. subst nf.
    all:auto. exists u'u, args'; intuition auto.
    transitivity (mkApps (tInd ind u'u) l'u).
    auto. eapply red_mkApps. reflexivity. auto.
    - apply All2_trans with l'u => //. typeclasses eauto.
      eapply (All2_impl conv). intros. now apply red_conv.
    - apply All2_trans with l''u => //. typeclasses eauto.
      eapply (All2_impl conv'). intros. now apply red_conv.
  Qed.

  Lemma isWfArity_sort Γ u :
    wf_local Σ Γ ->
    isWfArity typing Σ Γ (tSort u).
  Proof.
    move=> wfΓ. red. exists [], u. intuition auto.
  Qed.
  Hint Extern 10 (isWfArity _ _ _ (tSort _)) => apply isWfArity_sort : pcuic.

  Theorem principal_typing {Γ u A B} : Σ ;;; Γ |- u : A -> Σ ;;; Γ |- u : B ->
    ∑ C, Σ ;;; Γ |- C <= A  ×  Σ ;;; Γ |- C <= B × Σ ;;; Γ |- u : C.
  Proof.
    intros hA hB.
    induction u in Γ, A, B, hA, hB |- * using term_forall_list_ind.
    - apply inversion_Rel in hA as iA. 2: auto.
      destruct iA as [decl [? [e ?]]].
      apply inversion_Rel in hB as iB. 2: auto.
      destruct iB as [decl' [? [e' ?]]].
      rewrite e' in e. inversion e. subst. clear e.
      repeat insum. repeat intimes.
      all: try eassumption.
      constructor ; assumption.
    - apply inversion_Var in hA. destruct hA.
    - apply inversion_Evar in hA. destruct hA.
    - apply inversion_Sort in hA as iA. 2: auto.
      apply inversion_Sort in hB as iB. 2: auto.
      repeat outsum. repeat outtimes. subst.
      assert (x0 = x) as ee. {
        clear -e. destruct x, x0; cbnr; invs e; reflexivity. }
      subst. repeat insum. repeat intimes; tea.
      constructor ; assumption.
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
      + eapply cumul_trans. 1: auto. 2:eapply c0.
        constructor. constructor.
        apply leq_universe_product_mon; auto.
      + eapply cumul_trans. 1: auto. 2:eapply c.
        constructor. constructor.
        apply leq_universe_product_mon; auto.
      + eapply type_Prod.
        * eapply type_Cumul; eauto.
          -- left; eapply isWfArity_sort. now eapply typing_wf_local in t1.
          -- eapply conv_cumul; auto.
        * eapply type_Cumul; eauto.
          -- left; eapply isWfArity_sort. now eapply typing_wf_local in t3.
          -- eapply conv_cumul; auto.

    - apply inversion_Lambda in hA => //.
      apply inversion_Lambda in hB => //.
      repeat outsum. repeat outtimes.
      repeat pih.
      repeat outsum. repeat outtimes.
      apply invert_cumul_prod_l in c0 as [na' [A' [B' [[redA u1eq] ?]]]] => //.
      apply invert_cumul_prod_l in c as [na'' [A'' [B'' [[redA' u1eq'] ?]]]] => //.
      exists (tProd n u1 x3).
      repeat split; auto.
      + eapply cumul_trans with (tProd na' A' B'); auto.
        * eapply congr_cumul_prod => //.
          eapply cumul_trans with x2 => //.
        * now eapply red_cumul_inv.
      + eapply cumul_trans with (tProd na'' A'' B''); auto.
        * eapply congr_cumul_prod => //.
          eapply cumul_trans with x0 => //.
        * now eapply red_cumul_inv.
      + eapply type_Lambda; eauto.

    - eapply inversion_LetIn in hA; auto.
      eapply inversion_LetIn in hB; auto.
      destruct hA as [tty [bty ?]].
      destruct hB as [tty' [bty' ?]].
      repeat outtimes.
      specialize (IHu3 _ _ _ t4 t1) as [C' ?].
      repeat outtimes.
      exists (tLetIn n u1 u2 C'). repeat split.
      + clear IHu1 IHu2.
        eapply invert_cumul_letin_l in c0 => //.
        eapply invert_cumul_letin_l in c => //.
        eapply cumul_trans with (C' {0 := u1}). 1: auto.
        * eapply red_cumul. eapply red_step.
          -- econstructor.
          -- auto.
        * eapply cumul_trans with (bty {0 := u1}) => //.
          eapply (substitution_cumul Σ Γ [vdef n u1 u2] []) => //.
          -- constructor; auto.
             ++ now eapply typing_wf_local in t3.
             ++ red. exists tty' => //.
          -- pose proof (cons_let_def Σ Γ [] [] n u1 u2).
             rewrite !subst_empty in X. apply X. 1: constructor.
             auto.
      + clear IHu1 IHu2.
        eapply invert_cumul_letin_l in c0 => //.
        eapply invert_cumul_letin_l in c => //.
        eapply cumul_trans with (C' {0 := u1}). 1: auto.
        * eapply red_cumul. eapply red_step.
          -- econstructor.
          -- auto.
        * eapply cumul_trans with (bty' {0 := u1}) => //.
          eapply (substitution_cumul Σ Γ [vdef n u1 u2] []) => //.
          -- constructor; auto.
             ++ now eapply typing_wf_local in t3.
             ++ red. exists tty' => //.
          -- pose proof (cons_let_def Σ Γ [] [] n u1 u2).
             rewrite !subst_empty in X. apply X. 1: constructor.
             auto.
      + eapply type_LetIn; eauto.

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
      assert(Σ ;;; Γ |- A' = A'').
      { apply conv_trans with x3 => //.
        - now eapply red_conv.
        - apply conv_sym; auto.
      }
      assert(Σ ;;; Γ ,, vass x1 A' |- B' = B'').
      { apply conv_trans with x4 => //.
        - now eapply red_conv.
        - apply conv_sym; auto.
          eapply conv_conv_ctx; eauto.
          constructor; auto. 1: eapply conv_ctx_refl.
          constructor. now eapply conv_sym.
      }
      exists (B' {0 := u2}).
      repeat split.
      + eapply cumul_trans with (codom {0 := u2}) => //.
        eapply substitution_cumul0 => //. eapply c1.
      + eapply cumul_trans with (B'' {0 := u2}); eauto.
        * eapply substitution_cumul0 => //. eapply conv_cumul in X0; eauto.
        * eapply cumul_trans with (codom' {0 := u2}) => //.
          eapply substitution_cumul0 => //. eauto.
      + eapply (type_App _ _ _ x1 A').
        eapply type_Cumul.
        * eapply t0.
        * have v := validity_term wfΣ t0; auto.
          eapply isWfArity_or_Type_red in v.
          3:eapply redA. now apply v. auto.
        * apply red_cumul; eauto.
        * eapply type_Cumul. eauto.
          have v := validity_term wfΣ t0; auto.
          eapply isWfArity_or_Type_red in v.
          3:eapply redA.
          eapply isWAT_tProd in v as [HA' _].
          right; apply HA'. all:auto. now apply typing_wf_local in tydom'.
          transitivity A''; eauto. now apply conv_cumul.
          apply conv_cumul. now symmetry.

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
      specialize (IHu1 _ _ _ t t1). clear t. eapply PCUICValidity.validity in t1.
      specialize (IHu2 _ _ _ t0 t2).
      repeat outsum. repeat outtimes.
      eapply invert_cumul_ind_r in c1 as [u' [x0' [redr [redu ?]]]]; auto.
      eapply invert_cumul_ind_r in c2 as [u'' [x9' [redr' [redu' ?]]]]; auto.
      assert (All2 (fun a a' => Σ ;;; Γ |- a = a') x0 x7).
      { destruct (red_confluence wfΣ redr redr').
        destruct p.
        eapply red_mkApps_tInd in r as [args' [? ?]]; auto.
        eapply red_mkApps_tInd in r0 as [args'' [? ?]]; auto.
        subst. solve_discr.
        clear -wfΣ a1 a2 a3 a4.
        eapply (All2_impl (Q:=fun x y => Σ ;;; Γ |- x = y)) in a3; auto using red_conv.
        eapply (All2_impl (Q:=fun x y => Σ ;;; Γ |- y = x)) in a4;
          [|intros; symmetry; now apply red_conv].
        pose proof (All2_trans _ (conv_trans _ _) _ _ _ a1 a3).
        apply All2_sym in a4.
        pose proof (All2_trans _ (conv_trans _ _) _ _ _ X a4).
        eapply (All2_impl (Q:=fun x y => Σ ;;; Γ |- y = x)) in a2;
          [|intros; now symmetry].
        - apply All2_sym in a2.
          apply (All2_trans _ (conv_trans _ _) _ _ _ X0 a2).
      }
      clear redr redr' a1 a2.
      exists (mkApps u1 (skipn (ind_npars x8) x7 ++ [u2])); repeat split; auto.
      transitivity (mkApps u1 (skipn (ind_npars x8) x0 ++ [u2])); auto.
      eapply conv_cumul, mkApps_conv_args; auto.
      eapply All2_app. 2:constructor; auto.
      eapply All2_skipn. eapply All2_sym, (All2_impl X0); firstorder.
      econstructor;  eauto. simpl. split; auto.
      eapply type_Cumul; eauto. auto.

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
      destruct (cumul_ind_confluence c1 c2) as [nfu [nfargs [[[conv convargs] convargs'] [ru ru']]]].
      exists (subst0 (u :: List.rev nfargs) (subst_instance_constr nfu t2)).
      repeat split; auto.
      + etransitivity; [|eapply c0].
        admit.
      + etransitivity; [|eapply c].
        admit.
      + eapply refine_type.
        * eapply type_Proj.
          -- repeat split; eauto.
          -- simpl. eapply type_Cumul.
             1: eapply t0.
             1: right.
             2:eapply conv_cumul; eauto.
             eapply type_reduction in t0; [|auto|apply conv].
             eapply validity_term in t0; eauto. 
             now apply PCUICInductiveInversion.isWAT_mkApps_Ind_isType in t0.
          -- rewrite H3. simpl. simpl in H0.
             rewrite -H0. rewrite -(All2_length _ _ convargs). congruence.
        * simpl. reflexivity.

    - pose proof (typing_wf_local hA).
      apply inversion_Fix in hA as [decl [hguard [nthe [wfΓ [? ?]]]]]=>//.
      eapply inversion_Fix in hB as [decl' [hguard' [nthe' [wfΓ' [? ?]]]]]=>//.
      rewrite nthe' in nthe; noconf nthe.
      exists (dtype decl); repeat split; eauto.
      eapply type_Fix; eauto.

    - pose proof (typing_wf_local hA).
      eapply inversion_CoFix in hA as [decl [allow [nthe [wfΓ [? ?]]]]]=>//.
      eapply inversion_CoFix in hB as [decl' [allpw [nthe' [wfΓ' [? ?]]]]]=>//.
      rewrite nthe' in nthe; noconf nthe.
      exists (dtype decl); repeat split; eauto.
      eapply type_CoFix; eauto.
  Qed.

End Principality.

Lemma principal_type_ind {cf:checker_flags} {Σ Γ c ind u u' args args'} {wfΣ: wf Σ.1} :
  Σ ;;; Γ |- c : mkApps (tInd ind u) args ->
  Σ ;;; Γ |- c : mkApps (tInd ind u') args' ->
  PCUICEquality.R_universe_instance (eq_universe (global_ext_constraints Σ)) u u' * 
  All2 (conv Σ Γ) args args'.
Proof.
  intros h h'.
  destruct (principal_typing _ wfΣ h h') as [C [l [r ty]]].
  eapply invert_cumul_ind_r in l as [ui' [l' [red [Ru eqargs]]]]; auto.
  eapply invert_cumul_ind_r in r as [ui'' [l'' [red' [Ru' eqargs']]]]; auto.
  destruct (red_confluence wfΣ red red') as [nf [redl redr]].
  eapply red_mkApps_tInd in redl as [args'' [-> eq0]]; auto.
  eapply red_mkApps_tInd in redr as [args''' [eqnf eq1]]; auto.
  solve_discr.
  split. transitivity ui'; eauto. now symmetry.
  eapply All2_trans; [|eapply eqargs|]. intro; intros. eapply conv_trans; eauto.
  eapply All2_trans. intro; intros. eapply conv_trans; eauto.
  2:{ eapply All2_sym. eapply (All2_impl eqargs'). intros. now apply conv_sym. }
  eapply All2_trans. intro; intros. eapply conv_trans; eauto.
  eapply (All2_impl eq0). intros. now apply red_conv.
  eapply All2_sym; eapply (All2_impl eq1). intros. symmetry. now apply red_conv.
Qed.

Lemma typing_leq_term {cf:checker_flags} (Σ : global_env_ext) Γ t t' T T' : 
  wf Σ.1 ->
  Σ ;;; Γ |- t : T ->
  Σ ;;; Γ |- t' : T' ->
  PCUICEquality.leq_term Σ t' t ->
  Σ ;;; Γ |- t' : T.
Proof.
  intros wfΣ Ht.
  revert Σ wfΣ Γ t T Ht t' T'.
  eapply (typing_ind_env 
  (fun Σ Γ t T =>
    forall t' T' : term, Σ ;;; Γ |- t' : T' -> PCUICEquality.leq_term Σ t' t -> Σ;;; Γ |- t' : T)
  (fun Σ Γ wfΓ => wf_local Σ Γ)); auto;intros Σ wfΣ Γ wfΓ; intros.
    1-13:match goal with
    [ H : PCUICEquality.leq_term _ _ _ |- _ ] => depelim H
    end.
  all:try solve [econstructor; eauto].
  13:{ eapply type_Cumul.
       eapply X1. eauto. eauto. 
       destruct X2; [left|right].
       red in i. apply i.
       exists s.π1. apply s.π2. auto.
    }
  - eapply inversion_Sort in X0 as [l' [_ [Inl' [-> ?]]]].
    eapply type_Cumul with (tSort (Universe.super l')).
    constructor; auto. left; eexists _, _; simpl; intuition eauto.
    constructor. constructor. apply leq_universe_super.
    apply x. auto.

  - eapply inversion_Prod in X4 as [s1' [s2' [Ha [Hb Hs]]]]; auto.
    specialize (X1 _ _ Ha). 
    specialize (X1 (PCUICEquality.eq_term_leq_term _ _ _ X5_1)).
    eapply context_conversion in Hb. 3:{ constructor. apply conv_ctx_refl. constructor.
      constructor; eauto. }
    all:eauto.
    2:{ constructor; eauto. now exists s1. }
    specialize (X3 _ _ Hb X5_2).
    econstructor; eauto.
    eapply context_conversion; eauto.
    constructor; pcuic. constructor. symmetry;  now constructor.
    constructor; pcuic.

  - eapply inversion_Lambda in X4 as (s & B & dom & codom & cum); auto.
    specialize (X1 _ _ dom (PCUICEquality.eq_term_leq_term _ _ _ X5_1)).
    assert(conv_context Σ (Γ ,, vass na ty) (Γ ,, vass n t)).
    { repeat constructor; pcuic. }
    specialize (X3 t0 B).
    forward X3 by eapply context_conversion; eauto; pcuic.
    econstructor.
    econstructor. eauto. instantiate (1 := bty).
    eapply context_conversion; eauto; pcuic.
    constructor; pcuic. constructor; pcuic. symmetry; constructor; auto.
    have tyl := type_Lambda _ _ _ _ _ _ _ X0 X2.
    now eapply PCUICValidity.validity in tyl.
    eapply congr_cumul_prod; eauto.
    constructor; auto. reflexivity.
    
  - eapply inversion_LetIn in X6 as (s1' & A & dom & bod & codom & cum); auto.
    specialize (X1 _ _ dom (PCUICEquality.eq_term_leq_term _ _ _ X7_2)).
    specialize (X3 _ _ bod (PCUICEquality.eq_term_leq_term _ _ _ X7_1)).
    assert(conv_context Σ (Γ ,, vdef na t ty) (Γ ,, vdef n b b_ty)).
    { repeat constructor; pcuic. }
    specialize (X5 u A).
    forward X5 by eapply context_conversion; eauto; pcuic.
    specialize (X5 X7_3).
    econstructor.
    econstructor. eauto. eauto.
    instantiate (1 := b'_ty).
    eapply context_conversion; eauto.
    apply conv_context_sym; auto.
    pcuic. eapply PCUICValidity.validity; eauto.
    econstructor; eauto.
    eapply cum_LetIn; pcuic.
    
  - eapply inversion_App in X4 as (na' & A' & B' & hf & ha & cum); auto.
    specialize (X1 _ _ hf X5_1).
    specialize (X3 _ _ ha (PCUICEquality.eq_term_leq_term _ _ _ X5_2)).
    econstructor.
    econstructor; [eapply X1|eapply X3].
    eapply PCUICValidity.validity; pcuic.
    eapply type_App; eauto.
    eapply conv_cumul. eapply (subst_conv Γ [vass na A] [vass na A] []); pcuic.
    repeat constructor. now rewrite subst_empty.
    repeat constructor. now rewrite subst_empty.
    eapply PCUICValidity.validity in X0; auto.
    apply PCUICArities.isWAT_tProd in X0 as [tyA]; auto.
    constructor; auto.

  - eapply inversion_Const in X1 as [decl' [wf [declc [cu cum]]]]; auto.
    econstructor; eauto.
    econstructor; eauto.
    eapply PCUICValidity.validity; eauto.
    econstructor; eauto.
    eapply conv_cumul. constructor.
    pose proof (PCUICWeakeningEnv.declared_constant_inj _ _ H declc); subst decl'.
    eapply PCUICUnivSubstitution.eq_term_upto_univ_subst_instance_constr; eauto; typeclasses eauto.
  
  - eapply inversion_Ind in X1 as [decl' [idecl' [wf [declc [cu cum]]]]]; auto.
    econstructor; eauto.
    econstructor; eauto.
    eapply PCUICValidity.validity; eauto.
    econstructor; eauto.
    eapply conv_cumul. constructor.
    pose proof (PCUICWeakeningEnv.declared_inductive_inj isdecl declc) as [-> ->].
    eapply PCUICUnivSubstitution.eq_term_upto_univ_subst_instance_constr; eauto; typeclasses eauto.
  
  - eapply inversion_Construct in X1 as [decl' [idecl' [cdecl' [wf [declc [cu cum]]]]]]; auto.
    econstructor; eauto.
    econstructor; eauto.
    eapply PCUICValidity.validity; eauto.
    econstructor; eauto.
    pose proof (PCUICWeakeningEnv.declared_constructor_inj isdecl declc) as [-> [-> ->]].
    unfold type_of_constructor.
    transitivity (subst0 (inds (inductive_mind (ind, i).1) u (ind_bodies mdecl))
    (subst_instance_constr u0 cdecl'.1.2)).
    * eapply conv_cumul.
      eapply (conv_subst_conv _ Γ _ _ []); eauto.
      { unfold inds.
        generalize #|ind_bodies mdecl|.
        induction n; simpl; constructor; auto.
        constructor. constructor. auto. }
      eapply subslet_untyped_subslet.
      eapply (PCUICSpine.weaken_subslet _ _ _ Γ []); eauto.
      eapply PCUICArities.subslet_inds; eauto.
      destruct declc; eauto.
      eapply subslet_untyped_subslet.
      eapply (PCUICSpine.weaken_subslet _ _ _ Γ []); eauto.
      eapply PCUICArities.subslet_inds; eauto.
      destruct declc; eauto.
    * constructor. eapply PCUICEquality.subst_leq_term.
      eapply PCUICEquality.eq_term_leq_term.
      eapply PCUICUnivSubstitution.eq_term_upto_univ_subst_instance_constr; eauto; typeclasses eauto.

  - eapply inversion_Case in X6 as (u' & args' & mdecl' & idecl' & ps' & pty' & btys' & inv); auto.
    intuition auto.
    intuition auto.
    eapply type_Cumul.
    econstructor; eauto.
    eapply PCUICValidity.validity; eauto.
    eapply (type_Case _ _ (ind, npar)). eapply isdecl.
    all:eauto.
    eapply (All2_impl X5); firstorder.
    eapply conv_cumul.
    eapply mkApps_conv_args; pcuic.
    eapply All2_app. simpl in *.
    2:constructor; pcuic.
    eapply All2_skipn.
    clear -wfΣ a5 X4 X7_2.
    specialize (X4 _ _ a5 (PCUICEquality.eq_term_leq_term _ _ _ X7_2)).
    eapply (principal_type_ind a5 X4).
    
  - eapply inversion_Proj in X3 as (u' & mdecl' & idecl' & pdecl' & args' & inv); auto.
    intuition auto.
    eapply type_Cumul.
    econstructor; eauto.
    eapply PCUICValidity.validity; eauto.
    eapply type_Proj; eauto.
    specialize (X2 _ _ a0 (PCUICEquality.eq_term_leq_term _ _ _ X4)).
    pose proof (principal_type_ind X2 a0) as [Ruu' X3].
    transitivity (subst0 (c :: List.rev args) (subst_instance_constr u' pdecl'.2)).
    eapply conv_cumul.
    set (ctx := PCUICInductives.projection_context mdecl' idecl' p.1.1 u').
    set (ctx' := PCUICInductives.projection_context mdecl' idecl' p.1.1 u).
    eapply (conv_subst_conv _ Γ ctx ctx' []); eauto.
    constructor. now constructor.
    eapply All2_rev. apply All2_sym. apply (All2_impl X3). intros; now symmetry.
    eapply subslet_untyped_subslet; eauto.
    eapply PCUICInductives.projection_subslet; eauto.
    eapply subslet_untyped_subslet; eauto.
    eapply PCUICInductives.projection_subslet; eauto.
    constructor. eapply PCUICEquality.subst_leq_term.
    destruct (PCUICWeakeningEnv.declared_projection_inj a isdecl) as [<- [<- <-]].
    subst ty.
    eapply PCUICEquality.eq_term_leq_term.
    eapply PCUICUnivSubstitution.eq_term_upto_univ_subst_instance_constr; eauto; try typeclasses eauto.
    now symmetry.

  - eapply inversion_Fix in X2 as (decl' & fixguard' & Hnth & types' & bodies & cum); auto.
    eapply type_Cumul.
    econstructor; eauto.
    eapply PCUICValidity.validity; eauto.
    econstructor. 2:eapply H0. all:eauto.
    eapply (All_impl X0); firstorder.
    eapply (All_impl X1); firstorder.
    eapply All2_nth_error in a; eauto.
    destruct a as [[eqty _] _].
    constructor. now apply PCUICEquality.eq_term_leq_term.
  
  - eapply inversion_CoFix in X2 as (decl' & fixguard' & Hnth & types' & bodies & cum); auto.
    eapply type_Cumul.
    econstructor; eauto.
    eapply PCUICValidity.validity; eauto.
    eapply type_CoFix. 2:eapply H. all:eauto.
    eapply (All_impl X0); firstorder.
    eapply (All_impl X1); firstorder.
    eapply All2_nth_error in a; eauto.
    destruct a as [[eqty _] _].
    constructor. now apply PCUICEquality.eq_term_leq_term.
Qed.

Lemma typing_eq_term {cf:checker_flags} (Σ : global_env_ext) Γ t t' T T' : 
  wf Σ.1 ->
  Σ ;;; Γ |- t : T ->
  Σ ;;; Γ |- t' : T' ->
  eq_term Σ t t' ->
  Σ ;;; Γ |- t' : T.
Proof.
  intros wfΣ ht ht' eq.
  eapply typing_leq_term; eauto.
  now eapply eq_term_leq_term.
Qed.
