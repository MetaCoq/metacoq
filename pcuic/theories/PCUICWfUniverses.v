(* Distributed under the terms of the MIT license. *)
From Coq Require Import Morphisms.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICInduction
     PCUICLiftSubst PCUICTyping PCUICWeakeningEnv PCUICWeakening PCUICInversion
     PCUICSubstitution PCUICReduction PCUICCumulativity PCUICGeneration
     PCUICUnivSubst PCUICParallelReductionConfluence PCUICWeakeningEnv
     PCUICUnivSubstitution PCUICConversion.

From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.
Require Import ssreflect ssrbool.

From MetaCoq.PCUIC Require Import PCUICInduction.

Section CheckerFlags.
  Context {cf:checker_flags}.

  Lemma wf_universe_type1 Σ : wf_universe Σ Universe.type1.
  Proof.
    simpl.
    intros l hin%UnivExprSet.singleton_spec.
    subst l. simpl.
    apply LS.union_spec. right; apply global_levels_Set.
  Qed.

  Lemma wf_universe_super {Σ u} : wf_universe Σ u -> wf_universe Σ (Universe.super u).
  Proof.
    destruct u; cbn.
    1-2:intros _ l hin%UnivExprSet.singleton_spec; subst l; apply wf_universe_type1;
     now apply UnivExprSet.singleton_spec.
    intros Hl.
    intros l hin. 
    eapply Universes.spec_map_succ in hin as [x' [int ->]].
    simpl. now specialize (Hl _ int).
  Qed.

  Lemma wf_universe_sup {Σ u u'} : wf_universe Σ u -> wf_universe Σ u' ->
    wf_universe Σ (Universe.sup u u').
  Proof.
    destruct u, u'; cbn; auto.
    intros Hu Hu' l [Hl|Hl]%UnivExprSet.union_spec.
    now apply (Hu _ Hl).
    now apply (Hu' _ Hl).
  Qed.
  
  Lemma wf_universe_product {Σ u u'} : wf_universe Σ u -> wf_universe Σ u' ->
    wf_universe Σ (Universe.sort_of_product u u').
  Proof.
    intros Hu Hu'. unfold Universe.sort_of_product.
    destruct (Universe.is_prop u' || Universe.is_sprop u'); auto.
    now apply wf_universe_sup.
  Qed.

  Hint Resolve @wf_universe_type1 @wf_universe_super @wf_universe_sup @wf_universe_product : pcuic.

  Lemma wf_universe_instantiate Σ univs s u φ :
    wf Σ ->
    wf_universe (Σ, univs) s ->
    consistent_instance_ext (Σ, φ) univs u ->
    sub_context_set (monomorphic_udecl univs) (global_ext_context_set (Σ, φ)) ->
    wf_universe (Σ, φ) (subst_instance_univ u s).
  Proof.
    intros wfΣ Hs cu.
    apply (wf_universe_subst_instance (Σ, univs) φ); auto.
  Qed.

    Section WfUniverses.
    Context (Σ : global_env_ext).

    Definition wf_universeb (s : Universe.t) : bool :=
      match s with
      | Universe.lType l => UnivExprSet.for_all (fun l => LevelSet.mem (UnivExpr.get_level l) (global_ext_levels Σ)) l
      | _ => true
      end.

    Lemma wf_universe_reflect (u : Universe.t) : 
      reflect (wf_universe Σ u) (wf_universeb u).
    Proof.
      destruct u; simpl; try now constructor.
      eapply iff_reflect.
      rewrite UnivExprSet.for_all_spec.
      split; intros.
      - intros l Hl; specialize (H l Hl).
        now eapply LS.mem_spec.
      - specialize (H l H0). simpl in H.
        now eapply LS.mem_spec in H.
    Qed.

    Lemma reflect_bP {P b} (r : reflect P b) : b -> P.
    Proof. destruct r; auto. discriminate. Qed.

    Lemma reflect_Pb {P b} (r : reflect P b) : P -> b.
    Proof. destruct r; auto. Qed.

    Fixpoint wf_universes t := 
      match t with
      | tSort s => wf_universeb s
      | tApp t u
      | tProd _ t u
      | tLambda _ t u => wf_universes t && wf_universes u
      | tCase _ t p brs => wf_universes t && wf_universes p && 
        forallb (test_snd wf_universes) brs
      | tLetIn _ t t' u =>
        wf_universes t && wf_universes t' && wf_universes u
      | tProj _ t => wf_universes t
      | tFix mfix _ | tCoFix mfix _ =>
        forallb (fun d => wf_universes d.(dtype) && wf_universes d.(dbody)) mfix
      | _ => true
      end.

    Lemma All_forallb {A} (P : A -> Type) l (H : All P l) p p' : (forall x, P x -> p x = p' x) -> forallb p l = forallb p' l.
    Proof.
      intros; induction H; simpl; auto.
      now rewrite IHAll H0.
    Qed.

    Lemma wf_universes_lift n k t : wf_universes (lift n k t) = wf_universes t.
    Proof.
      induction t in n, k |- * using term_forall_list_ind; simpl; auto; try
        rewrite ?IHt1 ?IHt2 ?IHt3; auto.
        ssrbool.bool_congr. red in X.
        rewrite forallb_map.
        eapply All_forallb; eauto. simpl; intros [].
        simpl. intros. cbn. now rewrite H.
        rewrite forallb_map.
        eapply All_forallb; eauto. simpl; intros [].
        simpl. intros. cbn. now rewrite H.
        rewrite forallb_map.
        eapply All_forallb; eauto. simpl; intros [].
        simpl. intros. cbn. now rewrite H.
    Qed.

    Lemma wf_universes_subst s k t :
      All wf_universes s ->
      wf_universes (subst s k t) = wf_universes t.
    Proof.
      intros Hs.
      induction t in k |- * using term_forall_list_ind; simpl; auto; try
        rewrite ?IHt1 ?IHt2 ?IHt3; auto.
      - destruct (Nat.leb_spec k n); auto.
        destruct nth_error eqn:nth; simpl; auto.
        eapply nth_error_all in nth; eauto.
        simpl in nth. intros. now rewrite wf_universes_lift.
      - ssrbool.bool_congr. red in X.
        rewrite forallb_map.
        eapply All_forallb; eauto. simpl; intros [].
        simpl. intros. cbn. now apply H.
      - rewrite forallb_map.
        eapply All_forallb; eauto. simpl; intros [].
        simpl. intros. cbn. now rewrite H.
      - rewrite forallb_map.
        eapply All_forallb; eauto. simpl; intros [].
        simpl. intros. cbn. now rewrite H.
    Qed.

  End WfUniverses.

  Ltac to_prop := 
    repeat match goal with 
    | [ H: is_true (?x && ?y) |- _ ] =>
     let x := fresh in let y := fresh in move/andP: H; move=> [x y]; rewrite ?x ?y; simpl
    end. 

  Ltac to_wfu := 
    repeat match goal with 
    | [ H: is_true (wf_universeb _ ?x) |- _ ] => apply (reflect_bP (wf_universe_reflect _ x)) in H
    | [ |- is_true (wf_universeb _ ?x) ] => apply (reflect_Pb (wf_universe_reflect _ x))
    end. 
 
  Lemma wf_universes_inst {Σ : global_env_ext} univs t u : 
    wf Σ ->
    sub_context_set (monomorphic_udecl univs) (global_ext_context_set Σ) ->
    consistent_instance_ext Σ univs u ->
    wf_universes (Σ.1, univs) t ->
    wf_universes Σ (subst_instance u t).
  Proof.
    intros wfΣ sub cu wft.
    induction t using term_forall_list_ind; simpl in *; auto; try to_prop; 
      try apply /andP; to_wfu; intuition eauto 4.

    - to_wfu. destruct Σ as [Σ univs']. simpl in *.
      eapply (wf_universe_subst_instance (Σ, univs)); auto.

    - apply /andP; to_wfu; intuition eauto 4.
    - apply /andP; to_wfu; intuition eauto 4.
    - rewrite forallb_map.
      red in X. solve_all.
    - rewrite forallb_map. red in X.
      solve_all. to_prop.
      apply /andP; split; to_wfu; auto 4.
    - rewrite forallb_map. red in X.
      solve_all. to_prop.
      apply /andP; split; to_wfu; auto 4.
  Qed.
  
  Lemma weaken_wf_universe Σ Σ' t : wf Σ' -> extends Σ.1 Σ' ->
    wf_universe Σ t ->
    wf_universe (Σ', Σ.2) t.
  Proof.
    intros wfΣ ext.
    destruct t; simpl; auto.
    intros Hl l inl; specialize (Hl l inl).
    apply LS.union_spec. apply LS.union_spec in Hl as [Hl|Hl]; simpl.
    left; auto.
    right. destruct ext as [? ->]. simpl.
    rewrite global_levels_ext.
    eapply LS.union_spec. right; auto.
  Qed.

  Lemma weaken_wf_universes Σ Σ' t : wf Σ' -> extends Σ.1 Σ' ->
    wf_universes Σ t ->
    wf_universes (Σ', Σ.2) t.
  Proof.
    intros wfΣ ext.
    induction t using term_forall_list_ind; simpl in *; auto; intros; to_prop;
    try apply /andP; to_wfu; intuition eauto 4.

  - now eapply weaken_wf_universe.
  - apply /andP; to_wfu; intuition eauto 4.
  - apply /andP; to_wfu; intuition eauto 4.
  - red in X; solve_all.
  - red in X. solve_all. to_prop.
    apply /andP; split; to_wfu; auto 4.
  - red in X. solve_all. to_prop.
    apply /andP; split; to_wfu; auto 4.
  Qed.

  Lemma wf_universes_weaken_full : weaken_env_prop_full (fun Σ Γ t T => 
      wf_universes Σ t && wf_universes Σ T).
  Proof.
    red. intros.
    to_prop; apply /andP; split; now apply weaken_wf_universes.
  Qed.

  Lemma wf_universes_weaken :
    weaken_env_prop
      (lift_typing (fun Σ Γ (t T : term) => wf_universes Σ t && wf_universes Σ T)).
  Proof.
    red. intros.
    unfold lift_typing in *. destruct T. now eapply (wf_universes_weaken_full (_, _)).
    destruct X1 as [s Hs]; exists s. now eapply (wf_universes_weaken_full (_, _)).
  Qed.

  Lemma wf_universes_inds Σ mind u bodies : 
    All (fun t : term => wf_universes Σ t) (inds mind u bodies).
  Proof.
    unfold inds.
    generalize #|bodies|.
    induction n; simpl; auto.
  Qed.

  Lemma wf_universes_mkApps Σ f args : 
    wf_universes Σ (mkApps f args) = wf_universes Σ f && forallb (wf_universes Σ) args.
  Proof.
    induction args using rev_ind; simpl; auto. now rewrite andb_true_r.
    rewrite -PCUICAstUtils.mkApps_nested /= IHargs forallb_app /=.
    now rewrite andb_true_r andb_assoc.
  Qed.
    
  Lemma type_local_ctx_wf Σ Γ Δ s : type_local_ctx
    (lift_typing
     (fun (Σ : PCUICEnvironment.global_env_ext)
        (_ : PCUICEnvironment.context) (t T : term) =>
      wf_universes Σ t && wf_universes Σ T)) Σ Γ Δ s ->
      All (fun d => option_default (wf_universes Σ) (decl_body d) true && wf_universes Σ (decl_type d)) Δ.
  Proof.
    induction Δ as [|[na [b|] ty] ?]; simpl; constructor; auto.
    simpl.
    destruct X as [? [? ?]]. now to_prop.
    apply IHΔ. apply X.
    simpl.
    destruct X as [? ?]. now to_prop.
    apply IHΔ. apply X.
  Qed.



  Theorem wf_types :
    env_prop (fun Σ Γ t T => wf_universes Σ t && wf_universes Σ T)
      (fun Σ Γ wfΓ =>
      All_local_env_over typing
      (fun (Σ : global_env_ext) (Γ : context) (_ : wf_local Σ Γ) 
         (t T : term) (_ : Σ;;; Γ |- t : T) => wf_universes Σ t && wf_universes Σ T) Σ Γ
      wfΓ).
  Proof.
    apply typing_ind_env; intros; rename_all_hyps; simpl; to_prop; simpl; auto.

    - rewrite wf_universes_lift.
      destruct (nth_error_All_local_env_over heq_nth_error X) as [HΓ' Hd].
      destruct decl as [na [b|] ty]; cbn -[skipn] in *.
      + now destruct Hd as [Hd _]; to_prop.
      + destruct lookup_wf_local_decl; cbn -[skipn] in *.
        destruct o. now simpl in Hd; to_prop.

    - apply/andP; split; to_wfu; eauto with pcuic.
       
    - simpl in *; to_wfu. eauto with pcuic.
    - rewrite wf_universes_subst. constructor. to_wfu; auto. constructor.
      now move/andP: H3 => [].

    - pose proof (declared_constant_inv _ _ _ _ wf_universes_weaken wf X H).
      red in X1; cbn in X1.
      destruct (cst_body decl).
      * to_prop.
        eapply wf_universes_inst; eauto.
        epose proof (weaken_lookup_on_global_env'' Σ.1 _ _ wf H).
        simpl in H3.
        eapply sub_context_set_trans; eauto.
        eapply global_context_set_sub_ext.
      * move: X1 => [s /andP[Hc _]].
        to_prop.
        eapply wf_universes_inst; eauto.
        epose proof (weaken_lookup_on_global_env'' Σ.1 _ _ wf H).
        simpl in H1.
        eapply sub_context_set_trans; eauto.
        eapply global_context_set_sub_ext.

    - pose proof (declared_inductive_inv wf_universes_weaken wf X isdecl).
      cbn in X1. eapply onArity in X1. cbn in X1.
      move: X1 => [s /andP[Hind _]].
      eapply wf_universes_inst; eauto.
      generalize (weaken_lookup_on_global_env'' Σ.1 _ _ wf (proj1 isdecl)).
      simpl. intros H'.
      eapply sub_context_set_trans; eauto.
      eapply global_context_set_sub_ext.

    - pose proof (declared_constructor_inv wf_universes_weaken wf X isdecl) as [sc [nthe onc]].
      unfold type_of_constructor.
      rewrite wf_universes_subst.
      apply wf_universes_inds.
      eapply on_ctype in onc. cbn in onc.
      move: onc=> [_ /andP[onc _]].
      eapply wf_universes_inst; eauto.
      generalize (weaken_lookup_on_global_env'' Σ.1 _ _ wf (proj1 (proj1 isdecl))).
      simpl. intros H'.
      eapply sub_context_set_trans; eauto.
      eapply global_context_set_sub_ext.
    
    - apply /andP. split.
      solve_all. cbn in *. now to_prop.
      rewrite wf_universes_mkApps; apply/andP; split; auto.
      rewrite forallb_app /= H /= andb_true_r.
      rewrite forallb_skipn //.
      rewrite wf_universes_mkApps in H0.
      now to_prop.

    - rewrite /subst1. rewrite wf_universes_subst.
      constructor => //. eapply All_rev.
      rewrite wf_universes_mkApps in H1.
      move/andP: H1 => [].
      now intros _ hargs%forallb_All.
      pose proof (declared_projection_inv wf_universes_weaken wf X isdecl).
      destruct (declared_inductive_inv); simpl in *.
      destruct ind_cshapes as [|cs []] => //.
      destruct X1. red in o. subst ty.
      destruct nth_error eqn:heq.
      destruct o as [_ ->].
      assert (wf_universes (Σ.1, ind_universes mdecl) (decl_type c0)).
      destruct p0 as [[tyctx _] _].
      all:admit.
    
    - apply/andP; split; auto.
      solve_all. move:a => [s [Hty /andP[wfty wfs]]].
      to_prop. now rewrite wfty.
      eapply nth_error_all in X0; eauto.
      simpl in X0. now move: X0 => [s [Hty /andP[wfty _]]].

    - apply/andP; split; auto.
      solve_all. move:a => [s [Hty /andP[wfty wfs]]].
      to_prop. now rewrite wfty.
      eapply nth_error_all in X0; eauto.
      simpl in X0. now move: X0 => [s [Hty /andP[wfty _]]].
  Admitted.

  Lemma typing_wf_universes {Σ : global_env_ext} {Γ t T} : 
    wf Σ ->
    Σ ;;; Γ |- t : T -> wf_universes Σ t && wf_universes Σ T.
  Proof.
    intros wfΣ Hty.
    exact (env_prop_typing _ _ wf_types _ wfΣ _ _ _ Hty).
  Qed.

  Lemma typing_wf_universe {Σ : global_env_ext} {Γ t s} : 
    wf Σ ->
    Σ ;;; Γ |- t : tSort s -> wf_universe Σ s.
  Proof.
    intros wfΣ Hty.
    apply typing_wf_universes in Hty as [_ wfs]%MCProd.andP; auto.
    simpl in wfs. now to_wfu.
  Qed.

  Lemma isType_wf_universes {Σ Γ T} : wf Σ.1 -> isType Σ Γ T -> wf_universes Σ T.
  Proof.
    intros wfΣ [s Hs]. now eapply typing_wf_universes in Hs as [HT _]%MCProd.andP.
  Qed.
  
  Definition wf_decl_universes Σ d :=
    option_default (wf_universes Σ) d.(decl_body) true &&
    wf_universes Σ d.(decl_type).
  
  Definition wf_ctx_universes Σ Γ :=
    forallb (wf_decl_universes Σ) Γ.
  
  Lemma wf_universes_it_mkProd_or_LetIn {Σ Γ T} : 
    wf_universes Σ (it_mkProd_or_LetIn Γ T) = wf_ctx_universes Σ Γ && wf_universes Σ T.
  Proof.
    induction Γ as [ |[na [b|] ty] Γ] using rev_ind; simpl; auto;
      now rewrite it_mkProd_or_LetIn_app /= IHΓ /wf_ctx_universes forallb_app /=
      {3}/wf_decl_universes; cbn; bool_congr.
  Qed.
  
End CheckerFlags.

Hint Resolve @wf_universe_type1 @wf_universe_super @wf_universe_sup @wf_universe_product : pcuic.

Hint Extern 4 (wf_universe _ ?u) => 
  match goal with
  [ H : typing _ _ _ (tSort u) |- _ ] => apply (typing_wf_universe _ H)
  end : pcuic.
