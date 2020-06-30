(* Distributed under the terms of the MIT license.   *)
Set Warnings "-notation-overridden".

Require Import Equations.Prop.DepElim.
From Coq Require Import Bool String List Lia Arith.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICUtils
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICWeakeningEnv PCUICWeakening
     PCUICSubstitution PCUICClosed PCUICCumulativity PCUICGeneration PCUICReduction
     PCUICAlpha PCUICEquality PCUICValidity PCUICParallelReductionConfluence
     PCUICConfluence PCUICContextConversion PCUICUnivSubstitution
     PCUICConversion PCUICInversion PCUICContexts PCUICArities
     PCUICParallelReduction PCUICSpine PCUICInductives PCUICInductiveInversion
     PCUICCtxShape.
     
Close Scope string_scope.

Require Import ssreflect. 

Set Asymmetric Patterns.
Set SimplIsCbn.

From Equations Require Import Equations.

Derive Signature for OnOne2_local_env.

Ltac rename_hyp h ht ::= my_rename_hyp h ht.
Ltac pcuic := intuition eauto 3 with pcuic ||
  (try solve [repeat red; cbn in *; intuition auto; eauto 3 with pcuic || (try lia || congruence)]).

Arguments Nat.sub : simpl nomatch.
Arguments Universe.sort_of_product : simpl nomatch.
Hint Rewrite subst_instance_context_assumptions : len.
Hint Rewrite projs_length : len.

Lemma nth_nth_error {A} {i} {l : list A} {d v} :
  nth i l d = v ->
  (nth_error l i = Some v) +
  (nth_error l i = None /\ v = d).
Proof.
  move: i v. elim: l => [|hd tl IH] //.
  - case => /= //; now right.
  - case => /= // _ <-. now left.
Qed.

(** The subject reduction property of the system: *)

Definition SR_red1 {cf:checker_flags} (Σ : global_env_ext) Γ t T :=
  forall u (Hu : red1 Σ Γ t u), Σ ;;; Γ |- u : T.

Lemma wf_fixpoint_red1_type {cf:checker_flags} (Σ : global_env_ext) Γ mfix mfix1 : 
  wf Σ.1 ->
  wf_fixpoint Σ.1 mfix ->
  OnOne2
  (fun x y : def term =>
   red1 Σ Γ (dtype x) (dtype y)
   × (dname x, dbody x, rarg x) = (dname y, dbody y, rarg y)) mfix mfix1 ->
  wf_fixpoint Σ.1 mfix1.
Proof.
  intros wfΣ wffix o.
  move: wffix; unfold wf_fixpoint.
  enough (forall inds, map_option_out (map check_one_fix mfix) = Some inds ->
     map_option_out (map check_one_fix mfix1) = Some inds) => //.
  destruct map_option_out. now specialize (H _ eq_refl) as ->.
  discriminate.
  induction o; intros inds.
  - simpl.
    destruct p as [redty eqs].
    destruct hd as [dname dtype dbody rarg], hd' as [dname' dtype' dbody' rarg'].
    simpl in *.
    noconf eqs.
    destruct (decompose_prod_assum [] dtype) eqn:decomp.
    destruct nth_error eqn:Hnth.
    apply decompose_prod_assum_it_mkProd_or_LetIn in decomp.
    simpl in decomp.
    subst dtype.
    destruct (red1_it_mkProd_or_LetIn_smash _ _ _ _ _ _ _ wfΣ redty Hnth) as 
      (ctx & t' & decomp & d & [hnth di]).
    rewrite decomp hnth.
    unfold head in di. destruct decompose_app; simpl in *.
    destruct destInd as [[ind u]|]; try discriminate.
    destruct decompose_app. simpl in di. rewrite di. auto.
    discriminate.
  - simpl map.
    simpl map_option_out.
    destruct check_one_fix => //.
    destruct map_option_out. specialize (IHo _ eq_refl).
    move=> [= <-]. now rewrite IHo.
    discriminate.
Qed.

Lemma wf_fixpoint_red1_body {cf:checker_flags} (Σ : global_env_ext) Γ mfix mfix1 : 
  wf Σ.1 ->
  wf_fixpoint Σ.1 mfix ->
  OnOne2
  (fun x y : def term =>
   red1 Σ Γ (dbody x) (dbody y)
   × (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)) mfix mfix1 ->
  wf_fixpoint Σ.1 mfix1.
Proof.
  intros wfΣ wffix o.
  move: wffix; unfold wf_fixpoint.
  enough (map check_one_fix mfix = map check_one_fix mfix1) as -> => //.
  induction o.
  - simpl. f_equal.
    destruct p as [redty eqs].
    destruct hd as [dname dtype dbody rarg], hd' as [dname' dtype' dbody' rarg'].
    simpl in *.
    noconf eqs. reflexivity.
  - simpl. now rewrite IHo.
Qed.

Lemma wf_cofixpoint_red1_type {cf:checker_flags} (Σ : global_env_ext) Γ mfix mfix1 : 
  wf Σ.1 ->
  wf_cofixpoint Σ.1 mfix ->
  OnOne2
  (fun x y : def term =>
   red1 Σ Γ (dtype x) (dtype y)
   × (dname x, dbody x, rarg x) = (dname y, dbody y, rarg y)) mfix mfix1 ->
  wf_cofixpoint Σ.1 mfix1.
Proof.
  intros wfΣ wffix o.
  move: wffix; unfold wf_cofixpoint.
  enough (forall inds, map_option_out (map check_one_cofix mfix) = Some inds ->
     map_option_out (map check_one_cofix mfix1) = Some inds) => //.
  destruct map_option_out. now specialize (H _ eq_refl) as ->.
  discriminate.
  induction o; intros inds.
  - simpl.
    destruct p as [redty eqs].
    destruct hd as [dname dtype dbody rarg], hd' as [dname' dtype' dbody' rarg'].
    simpl in *.
    noconf eqs.
    destruct (decompose_prod_assum [] dtype) eqn:decomp.
    apply decompose_prod_assum_it_mkProd_or_LetIn in decomp.
    simpl in decomp.
    subst dtype.
    eapply red1_red in redty.
    destruct (decompose_app t) as [f l] eqn:decomp.
    destruct f; try discriminate. simpl.
    apply decompose_app_inv in decomp. subst t.
    eapply red_it_mkProd_or_LetIn_mkApps_Ind in redty as [ctx' [args' ->]]; auto.
    erewrite decompose_prod_assum_it_mkProd => //.
    2:{ now rewrite is_ind_app_head_mkApps. }
    rewrite decompose_app_mkApps => //.
  - simpl map.
    simpl map_option_out.
    destruct check_one_cofix => //.
    destruct map_option_out. specialize (IHo _ eq_refl).
    move=> [= <-]. now rewrite IHo.
    discriminate.
Qed.

Lemma wf_cofixpoint_red1_body {cf:checker_flags} (Σ : global_env_ext) Γ mfix mfix1 : 
  wf Σ.1 ->
  wf_cofixpoint Σ.1 mfix ->
  OnOne2
  (fun x y : def term =>
   red1 Σ Γ (dbody x) (dbody y)
   × (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)) mfix mfix1 ->
  wf_cofixpoint Σ.1 mfix1.
Proof.
  intros wfΣ wffix o.
  move: wffix; unfold wf_cofixpoint.
  enough (map check_one_cofix mfix = map check_one_cofix mfix1) as -> => //.
  induction o.
  - simpl. f_equal.
    destruct p as [redty eqs].
    destruct hd as [dname dtype dbody rarg], hd' as [dname' dtype' dbody' rarg'].
    simpl in *.
    noconf eqs. reflexivity.
  - simpl. now rewrite IHo.
Qed.

Lemma sr_red1 {cf:checker_flags} :
  env_prop SR_red1
      (fun Σ Γ wfΓ =>
        All_local_env_over typing (fun  Σ Γ _ t T _ => SR_red1 Σ Γ t T) Σ Γ wfΓ).
Proof.
  apply typing_ind_env; intros Σ wfΣ Γ wfΓ; unfold SR_red1; intros **; rename_all_hyps; auto;
    match goal with
    | [H : (_ ;;; _ |- _ <= _) |- _ ] => idtac
    | _ =>
      depelim Hu; try solve [apply mkApps_Fix_spec in x; noconf x];
      try solve [econstructor; eauto] ;
      try solve [
        match goal with
        | h : _ = mkApps _ ?args |- _ =>
          let e := fresh "e" in
          apply (f_equal nApp) in h as e ; simpl in e ;
          rewrite nApp_mkApps in e ; simpl in e ;
          destruct args ; discriminate
        end
      ]
    end.

  - (* Rel *)
    rewrite heq_nth_error in e. destruct decl as [na b ty]; noconf e.
    simpl.
    pose proof (nth_error_All_local_env_over heq_nth_error X); eauto.
    destruct lookup_wf_local_decl; cbn in *.
    rewrite <- (firstn_skipn (S n) Γ).
    eapply weakening_length; auto.
    { rewrite firstn_length_le; auto. apply nth_error_Some_length in heq_nth_error. auto with arith. }
    now unfold app_context; rewrite firstn_skipn.
    apply o.

  - (* Prod *)
    constructor; eauto.
    eapply (context_conversion _ wf _ _ _ typeb).
    constructor; auto with pcuic.
    constructor; auto. exists s1; auto.

  - (* Lambda *)
    eapply type_Cumul. eapply type_Lambda; eauto.
    eapply (context_conversion _ wf _ _ _ typeb).
    constructor; auto with pcuic.
    constructor; auto. exists s1; auto.
    assert (Σ ;;; Γ |- tLambda n t b : tProd n t bty). econstructor; eauto.
    edestruct (validity _ wf _ _ _ X0). apply i.
    eapply cumul_red_r.
    apply cumul_refl'. constructor. apply Hu.

  - (* LetIn body *)
    eapply type_Cumul.
    apply (substitution_let _ Γ n b b_ty b' b'_ty wf typeb').
    specialize (typing_wf_local typeb') as wfd.
    assert (Σ ;;; Γ |- tLetIn n b b_ty b' : tLetIn n b b_ty b'_ty). econstructor; eauto.
    edestruct (validity _ wf _ _ _ X0). apply i.
    eapply cumul_red_r.
    apply cumul_refl'. constructor.

  - (* LetIn value *)
    eapply type_Cumul.
    econstructor; eauto.
    eapply (context_conversion _ wf _ _ _ typeb').
    constructor. auto with pcuic. constructor; eauto. constructor; auto.
    now exists s1. red. auto.
    assert (Σ ;;; Γ |- tLetIn n b b_ty b' : tLetIn n b b_ty b'_ty). econstructor; eauto.
    edestruct (validity _ wf _ _ _ X0). apply i.
    eapply cumul_red_r.
    apply cumul_refl'. now constructor.

  - (* LetIn type annotation *)
    specialize (forall_u _ Hu).
    eapply type_Cumul.
    econstructor; eauto.
    eapply type_Cumul. eauto. right; exists s1; auto.
    apply red_cumul; eauto.
    eapply (context_conversion _ wf _ _ _ typeb').
    constructor. auto with pcuic. constructor; eauto. constructor; auto.
    exists s1; auto. red; eauto.
    eapply type_Cumul. eauto. right. exists s1; auto. eapply red_cumul. now eapply red1_red.
    assert (Σ ;;; Γ |- tLetIn n b b_ty b' : tLetIn n b b_ty b'_ty). econstructor; eauto.
    edestruct (validity _ wf _ _ _ X0). apply i.
    eapply cumul_red_r.
    apply cumul_refl'. now constructor.

  - (* Application *)
    eapply substitution0; eauto.
    pose proof typet as typet'.
    eapply inversion_Lambda in typet' as [s1 [B' [Ht [Hb HU]]]]=>//.
    apply cumul_Prod_inv in HU as [eqA leqB] => //.
    destruct (validity _ wf _ _ _ typet).

    eapply type_Cumul; eauto.
    unshelve eapply (context_conversion _ wf _ _ _ Hb); eauto with wf.
    constructor. auto with pcuic. constructor ; eauto.
    constructor; auto with pcuic. red; eauto.
    eapply isWAT_tProd in i as [Hs _]; auto.
    eapply isWAT_tProd in i as [_ Hs]; intuition auto.

  - (* Fixpoint unfolding *)
    assert (args <> []) by (destruct args; simpl in *; congruence).
    apply tApp_mkApps_inj in H as [-> Hu]; auto.
    rewrite mkApps_nonempty; auto.
    epose (last_nonempty_eq H0). rewrite <- Hu in e1. rewrite <- e1.
    clear e1.
    specialize (inversion_mkApps wf typet) as [T' [appty spty]].
    specialize (validity _ wf _ _ _ appty) as [_ vT'].
    eapply type_tFix_inv in appty as [T [arg [fn' [[[Hnth wffix] Hty]]]]]; auto.
    rewrite e in Hnth. noconf Hnth.
    eapply type_App.
    eapply type_mkApps. eapply type_Cumul; eauto. eapply spty.
    eauto.

  - (* Congruence *)
    eapply type_Cumul; [eapply type_App| |]; eauto with wf.
    eapply validity. eauto. eauto.
    eapply type_App; eauto. eapply red_cumul_inv.
    eapply (red_red Σ Γ [vass na A] [] [u] [N2]); auto.
    constructor. constructor.

  - (* Constant unfolding *)
    unshelve epose proof (declared_constant_inj decl decl0 _ _); tea; subst decl.
    destruct decl0 as [ty body' univs]; simpl in *; subst body'.
    eapply on_declared_constant in H; tas; cbn in H.
    rewrite <- (app_context_nil_l Γ).
    apply typecheck_closed in H as H'; tas.
    destruct H' as [_ H']. apply andb_and in H'.
    replace (subst_instance_constr u body)
      with (lift0 #|Γ| (subst_instance_constr u body)).
    replace (subst_instance_constr u ty)
      with (lift0 #|Γ| (subst_instance_constr u ty)).
    2-3: rewrite lift_subst_instance_constr lift_closed; cbnr; apply H'.
    eapply weakening; tea.
    now rewrite app_context_nil_l.
    eapply typing_subst_instance_decl with (Γ0:=[]); tea.

  - (* iota reduction *)    
    subst npar.
    clear forall_u forall_u0 X X0.
    pose proof typec as typec''.
    unfold iota_red. rename args into iargs. rename args0 into cargs.
    pose proof typec as typec'.
    eapply inversion_mkApps in typec as [A [tyc tyargs]]; auto.
    eapply (inversion_Construct Σ wf) in tyc as [mdecl' [idecl' [cdecl' [wfl [declc [Hu tyc]]]]]].
    unshelve eapply Construct_Ind_ind_eq in typec'; eauto.
    unfold on_declared_constructor in typec'.
    destruct declc as [decli declc].
    unfold on_declared_inductive in typec'.
    destruct declared_constructor_inv as [cs [Hnth onc]].
    simpl in typec'.
    destruct (declared_inductive_inj isdecl decli) as []; subst mdecl' idecl'.
    set(oib := declared_inductive_inv _ _ _ _) in *. clearbody oib.
    eapply (build_branches_type_lookup _  Γ ind mdecl idecl cdecl' _ _ _ brs) in heq_map_option_out; eauto.
    2:{ eapply All2_impl; eauto. simpl; intuition eauto. }
    unshelve eapply build_case_predicate_type_spec in heq_build_case_predicate_type as 
      [parsubst [csubst ptyeq]]. 2:exact oib. subst pty.
    destruct heq_map_option_out as [nargs [br [brty [[[Hbr Hbrty] brbrty] brtys]]]].
    unshelve eapply (branch_type_spec Σ.1) in brtys; auto.
    destruct (nth_nth_error (@eq_refl _ (nth c0 brs (0, tDummy)))) => //.
    assert (H : ∑ t', nth_error btys c0 = Some t').
    pose proof (All2_length _ _ X5). eapply nth_error_Some_length in e. rewrite H in e.
    destruct (nth_error_spec btys c0). eexists; eauto. elimtype False; lia.
    destruct H as [t' Ht'].
    rewrite Hbr in e. noconf e. simpl in H. rewrite <- H. simpl.  
    clear H.
    destruct brtys as [-> brtys].
    specialize (brtys  _ csubst).
    simpl in brtys. subst brty.
    eapply type_mkApps. eauto.
    set argctx := cshape_args cs.
    clear Hbr brbrty Hbrty X5 Ht'.
    destruct typec' as [[[[_ equ] cu] eqargs] [cparsubst [cargsubst [iparsubst [iidxsubst ci]]]]].
    destruct ci as ((([cparsubst0 iparsubst0] & idxsubst0) & subsidx) & [s [typectx [Hpars Hargs]]]).
    pose proof (context_subst_fun csubst (iparsubst0.(inst_ctx_subst))). subst iparsubst.
    assert(leq:Σ ;;; Γ |- (it_mkProd_or_LetIn
    (subst_context parsubst 0
       (subst_context (inds (inductive_mind ind) u (ind_bodies mdecl))
          #|ind_params mdecl| (map_context (subst_instance_constr u) argctx)))
    (mkApps ((lift0 #|argctx|) p)
       (map
          (fun x : term =>
           subst parsubst #|argctx|
             (subst (inds (inductive_mind ind) u (ind_bodies mdecl))
                (#|argctx| + #|ind_params mdecl|) (subst_instance_constr u x)))
          (cshape_indices cs) ++
        [mkApps (tConstruct ind c0 u)
           (map (lift0 #|argctx|) (firstn (PCUICAst.ind_npars mdecl) iargs) ++
            to_extended_list 
              (subst_context parsubst 0
              (subst_context (inds (inductive_mind ind) u (ind_bodies mdecl))
                 #|ind_params mdecl| (map_context (subst_instance_constr u) argctx))))])))
           <=
    (it_mkProd_or_LetIn
     (subst_context cparsubst 0
        (subst_context (inds (inductive_mind ind) u1 (ind_bodies mdecl))
           #|ind_params mdecl| (map_context (subst_instance_constr u1) argctx)))
     (mkApps ((lift0 #|argctx|) p)
        (map
           (fun x : term =>
            subst cparsubst #|argctx|
              (subst (inds (inductive_mind ind) u1 (ind_bodies mdecl))
                 (#|argctx| + #|ind_params mdecl|) (subst_instance_constr u1 x)))
           (cshape_indices cs) ++
         [mkApps (tConstruct ind c0 u1)
            (map (lift0 #|argctx|) (firstn (PCUICAst.ind_npars mdecl) cargs) ++
             to_extended_list 
             (subst_context cparsubst 0
             (subst_context (inds (inductive_mind ind) u1 (ind_bodies mdecl))
                #|ind_params mdecl| (map_context (subst_instance_constr u1) argctx))))])))).
    { pose proof (subslet_inds _ _ u _ _ wf isdecl cu).
      pose proof (subslet_inds _ _ u1 _ _ wf ⋆ ⋆).
      assert(wfpararms : wf_local Σ (subst_instance_context u (ind_params mdecl))).
      { eapply (on_minductive_wf_params _ mdecl); intuition eauto. eapply isdecl. }
      assert(closed_ctx (subst_instance_context u (ind_params mdecl)) = true).
      { eapply closed_wf_local; eauto. }
      assert (closed_ctx (subst_instance_context u1 (ind_params mdecl)) = true).
      { eapply closed_wf_local; eauto.
        eapply (on_minductive_wf_params _ mdecl); intuition eauto.
        eapply isdecl. }
     assert(subslet Σ Γ (parsubst ++ inds (inductive_mind ind) u (ind_bodies mdecl))
        (subst_instance_context u
          (arities_context (ind_bodies mdecl) ,,, ind_params mdecl))).
      { rewrite subst_instance_context_app. eapply subslet_app.
        rewrite closed_ctx_subst; pcuic.
        eapply (weaken_subslet _  _ _ _ []) => //; eauto. }
      assert(subslet Σ Γ (cparsubst ++ inds (inductive_mind ind) u1 (ind_bodies mdecl))
        (subst_instance_context u1
          (arities_context (ind_bodies mdecl) ,,, ind_params mdecl))).
      { rewrite subst_instance_context_app. eapply subslet_app.
        rewrite closed_ctx_subst; pcuic.
        eapply (weaken_subslet _ _ _ _ []) => //; eauto. }
      assert (lenipar := context_subst_length _ _ _ iparsubst0).
      rewrite subst_instance_context_length in lenipar. 
      assert (lencpar := context_subst_length _ _ _ cparsubst0).
      rewrite subst_instance_context_length in lencpar. 
      assert (All2 (conv Σ Γ) (parsubst ++ inds (inductive_mind ind) u (ind_bodies mdecl))
        (cparsubst ++ inds (inductive_mind ind) u1 (ind_bodies mdecl))).
      { eapply All2_app.
        * eapply spine_subst_conv; eauto.
          eapply context_relation_subst_instance; eauto.
          now rewrite closedn_subst_instance_context in H.
          now symmetry.
        * now apply conv_inds. }
      pose proof (on_declared_inductive wf isdecl) as [onind _].
      eapply cumul_it_mkProd_or_LetIn => //.
      clear csubst. subst argctx.
      rewrite {1}lenipar. rewrite {1}lencpar.
      clear lenipar lencpar.
      rewrite - !subst_app_context.

      eapply (context_relation_subst _ 
        (subst_instance_context u (arities_context (ind_bodies mdecl) ,,, ind_params mdecl))
        (subst_instance_context u1 (arities_context (ind_bodies mdecl) ,,, ind_params mdecl))); eauto with pcuic.
      rewrite -app_context_assoc - [subst_instance_context _ _ ,,, _]subst_instance_context_app.
      apply weaken_wf_local => //.
      eapply on_constructor_inst; pcuic.
      - do 2 rewrite - [subst_instance_context _ _ ,,, _]subst_instance_context_app.
        eapply context_relation_subst_instance => //.
        eapply on_constructor_inst; pcuic.
        now symmetry.
      - apply conv_cumul.
        apply mkApps_conv_args => //. apply conv_refl'.
        eapply All2_app.
        eapply All2_map. eapply All2_refl. intros x.
        rewrite {1 2}lenipar.
        rewrite -subst_app_simpl. rewrite lencpar.
        rewrite -subst_app_simpl. rewrite -subst_app_context.
        rewrite -(subst_instance_context_length u argctx).
        eapply subst_conv => //; eauto.
        rewrite -app_context_assoc - [subst_instance_context _ _ ,,, _]subst_instance_context_app.
        apply weaken_wf_local => //.
        eapply on_constructor_inst; pcuic.
        rewrite -app_context_assoc - [subst_instance_context _ _ ,,, _]subst_instance_context_app.
        constructor.
        apply eq_term_upto_univ_subst_instance_constr; try typeclasses eauto.
        now symmetry.
        constructor. 2:constructor.
        apply mkApps_conv_args => //.
        do 2 constructor. now symmetry.
        apply All2_app.
        * eapply All2_map.
          eapply All2_impl. 
          apply All2_sym. eapply Hpars.
          simpl. intros x y conv.
          eapply (weakening_conv_gen _ Γ []); auto.
          now autorewrite with len. now symmetry.
        * set (r := (subst_context cparsubst _ _)).
          rewrite (to_extended_list_eq _ r). subst r.
          do 2 apply same_ctx_shape_subst.
          apply same_ctx_shape_map. apply same_ctx_shape_refl.
          apply All2_refl.
          intros. reflexivity. }
    unshelve eapply typing_spine_strengthen. 4:eapply leq. all:auto.
    clear leq. 
    set(cindices := map
    (fun x : term =>
     subst cparsubst #|argctx|
       (subst (inds (inductive_mind ind) u1 (ind_bodies mdecl))
          (#|argctx| + #|ind_params mdecl|)
          (subst_instance_constr u1 x)))
    (cshape_indices cs)) in *.

    eapply (typing_spine_weaken_concl (S:=
      (mkApps p (map (subst0 cargsubst) cindices ++ [mkApps (tConstruct ind c0 u1) cargs])))) => //.
    2:{ eapply conv_cumul; auto.
        eapply mkApps_conv_args; auto with pcuic.
        eapply All2_app; auto with pcuic.
        unfold cindices. rewrite !map_map_compose.
        eapply All2_trans. eapply conv_trans. auto.
        2:eauto. eapply All2_map. eapply All2_refl. intros x.
        rewrite subst_app_simpl. simpl.
        pose proof (context_subst_length _ _ _ idxsubst0).
        autorewrite with len in H. rewrite H. reflexivity. }
    eapply typing_spine_it_mkProd_or_LetIn_close_eq; eauto.
    * eapply make_context_subst_spec_inv. rewrite List.rev_involutive.
      apply idxsubst0.
    * pose proof (on_declared_minductive _ (declared_inductive_minductive _ _ _ _ decli)) as onmind.
      pose proof (onNpars _ _ _ _ onmind).
      pose proof (context_assumptions_length_bound (ind_params mdecl)).
      rewrite skipn_length; try lia.
      rewrite !context_assumptions_subst subst_instance_context_assumptions.
      rewrite eqargs. auto with arith.
    * apply idxsubst0.
    * right.
      pose proof (on_declared_inductive wf isdecl) as [onmind _].
      destruct (on_constructor_subst' _ _ _ _ _ _ wf isdecl onmind oib onc) as [[wfext wfc] insts].
      eexists.
      assert(wfparinds : wf_local Σ
        (subst_instance_context u (ind_params mdecl) ,,,
          subst_instance_context u (ind_indices oib))). 
      { unshelve epose proof (on_minductive_wf_params_indices_inst _ _ u _ _ wf _ oib cu); pcuic.
        now rewrite -subst_instance_context_app. }
      assert(wfΓparinds : wf_local Σ
        (Γ ,,, subst_instance_context u (ind_params mdecl) ,,,
          subst_instance_context u (ind_indices oib))). 
      { rewrite -app_context_assoc.
        eapply weaken_wf_local; auto. }
      assert(wfparinds' : wf_local Σ (subst_instance_context u1 (ind_params mdecl) ,,,
          subst_instance_context u1 (ind_indices oib))).
      { unshelve epose proof (on_minductive_wf_params_indices_inst _ _ u1 _ _ wf _ oib Hu); pcuic.
        now rewrite -subst_instance_context_app. }
      assert(wfΓparinds' : wf_local Σ
        (Γ ,,, subst_instance_context u1 (ind_params mdecl) ,,,
          subst_instance_context u1 (ind_indices oib))).
      { rewrite -app_context_assoc. eapply weaken_wf_local; auto. }
      assert(wfparu : wf_local Σ (subst_instance_context u (ind_params mdecl))). 
      { eapply on_minductive_wf_params; eauto. destruct decli; eauto. }
      assert(wfparu1 : wf_local Σ (subst_instance_context u1 (ind_params mdecl))). 
      { eapply on_minductive_wf_params; eauto. destruct decli; eauto. }
      eapply type_it_mkProd_or_LetIn; eauto. 
      eapply type_mkApps.
      assert (Σ ;;; Γ |- p : 
      PCUICAst.it_mkProd_or_LetIn
      (subst_context cparsubst 0
         (subst_instance_context u1 (ind_indices oib)))
      (tProd (nNamed (PCUICAst.ind_name idecl))
         (mkApps (tInd ind u1)
            (map (lift0 #|ind_indices oib|)
               (firstn (PCUICAst.ind_npars mdecl) cargs) ++
             PCUICAst.to_extended_list (ind_indices oib))) 
         (tSort ps))).
      { eapply type_Cumul. eauto. left.
        eexists _, ps. rewrite destArity_it_mkProd_or_LetIn.
        simpl. split. reflexivity. rewrite app_context_nil_l. simpl.
        constructor.
        eapply substitution_wf_local; eauto. eapply cparsubst0 => //.
        red.
        { exists (subst_instance_univ u1 (ind_sort oib)).
          eapply type_mkApps. econstructor; eauto.
          eapply substitution_wf_local; eauto. eapply cparsubst0.
          eapply wf_arity_spine_typing_spine; auto.
          split.
          + pose proof oib.(onArity). right. red in X.
            destruct X.
            eapply (instantiate_minductive _ _ _ u1) in t; eauto.
            eexists. eapply weaken_ctx in t. simpl in t. eapply t; eauto.
            all:pcuic. eapply substitution_wf_local; eauto. eapply cparsubst0.
          + rewrite oib.(ind_arity_eq).
            rewrite subst_instance_constr_it_mkProd_or_LetIn.
            eapply arity_spine_it_mkProd_or_LetIn => //.
            eapply (spine_subst_weakening _ _ _ _ _ 
             (subst_context cparsubst 0 (subst_instance_context u1 (ind_indices oib)))) in cparsubst0 => //.
            autorewrite with len in cparsubst0.
            rewrite closed_ctx_lift in cparsubst0.
            now eapply closed_wf_local. apply cparsubst0.
            eapply substitution_wf_local; eauto. apply cparsubst0.
            rewrite subst_instance_constr_it_mkProd_or_LetIn subst_it_mkProd_or_LetIn /=.
            rewrite -(app_nil_r (to_extended_list _)).
            eapply arity_spine_it_mkProd_or_LetIn => //.
            epose proof (spine_subst_to_extended_list_k Σ (subst_context cparsubst 0 (subst_instance_context u1 (ind_indices oib)))
                Γ wf). forward X.
            eapply substitution_wf_local; eauto. apply cparsubst0.
            autorewrite with len in X. 
            fold (to_extended_list_k (subst_context cparsubst 0
               (subst_instance_context u1 (ind_indices oib))) 0) in X.
            rewrite to_extended_list_k_fold_context in X.
            rewrite distr_lift_subst_context in X.
            rewrite closed_ctx_lift in X. rewrite Nat.add_0_r.
            rewrite (subslet_length cparsubst0) subst_instance_context_length.
            apply closed_wf_local in wfparinds' => //.
            rewrite closedn_ctx_app in wfparinds'.
            autorewrite with len in wfparinds'. now move/andP: wfparinds' => [_ ?].
            now rewrite PCUICSubstitution.map_subst_instance_constr_to_extended_list_k in X.
            simpl. constructor. left; eexists _, _; intuition eauto. simpl.
            eapply substitution_wf_local; eauto; apply cparsubst0.
            reflexivity. }
        eapply cumul_it_mkProd_or_LetIn => //.
        eapply context_relation_subst => //. 2:eapply iparsubst0. 2:eapply cparsubst0. auto.
        eapply spine_subst_conv; eauto. eapply context_relation_subst_instance; eauto.
        now symmetry. now symmetry.
        rewrite - !subst_instance_context_app.
        eapply context_relation_subst_instance; eauto.
        eapply on_minductive_wf_params_indices_inst => //. destruct decli; eauto.
        now symmetry.
        eapply congr_cumul_prod; eauto.
        eapply mkApps_conv_args => //.
        constructor. constructor. now symmetry.
        apply All2_app. eapply All2_map.
        apply All2_sym. eapply All2_impl. eauto. simpl.
        intros x y Hx. eapply (weakening_conv_gen _ _ []) => //.
        now autorewrite with len. now apply conv_sym.
        eapply All2_refl. intros x. reflexivity. apply cumul_refl'. }
      clear typep.
      eapply weakening_gen in X. eauto.
      now autorewrite with len. auto. 
      eapply type_local_ctx_wf_local in typectx; auto.
      unfold to_extended_list.
      rewrite !to_extended_list_k_subst.
      rewrite PCUICSubstitution.map_subst_instance_constr_to_extended_list_k.
      rewrite lift_it_mkProd_or_LetIn.
      subst cindices.
      simpl.
      assert (closed_ctx (subst_instance_context u1 (ind_params mdecl)) = true).
      { eapply closed_wf_local; eauto. }
      assert (lencpar := context_subst_length _ _ _ cparsubst0).
      rewrite subst_instance_context_length in lencpar. rewrite lencpar.
      
      eapply (ctx_inst_inst _ _ u1) in insts; eauto.
      rewrite !subst_instance_context_app in insts.
      assert(closedindices : All (fun x => closedn (#|cshape_args cs| + #|ind_params mdecl|) x)
        (map
      (subst
         (inds (inductive_mind (ind, c0).1) u1
            (PCUICAst.ind_bodies mdecl))
         (#|cshape_args cs| + #|ind_params mdecl|))
      (map (subst_instance_constr u1) (cshape_indices cs)))).
      { rewrite -[_ ,,, _ ,,, _](app_context_nil_l _) in insts.
        rewrite -[subst_instance_context _ _ ,,, _ ,,, _]app_context_assoc in insts.
        rewrite app_context_assoc in insts.
        eapply (ctx_inst_subst _ []) in insts => //.
        2:{ eapply subslet_inds => //. pcuic. }
        rewrite app_context_nil_l in insts.
        autorewrite with len in insts.
        apply ctx_inst_closed in insts => //.
        now autorewrite with len in insts. }

      eapply (ctx_inst_weaken _ _ _ _ Γ) in insts => //.
      rewrite app_context_assoc in insts.
      eapply ctx_inst_subst in insts => //.
      2:{ eapply subslet_app. 2:{ eapply (weaken_subslet _ _ _ _ []) => //. eapply subslet_inds => //. pcuic. }
          rewrite closed_ctx_subst => //. eapply cparsubst0. }          
      rewrite subst_app_context in insts.
      rewrite subst_instance_context_rev in insts.
      rewrite subst_telescope_subst_context in insts.
      autorewrite with len in insts. simpl in insts.
      unshelve epose proof (ctx_inst_spine_subst _ _  _ _ wf _  _ insts) as instsp; eauto.
      { rewrite -lencpar. apply (spine_codom_wf _ _ _ _ _ idxsubst0). }
      { rewrite -lencpar.
        have w := spine_codom_wf _ _ _ _ _ idxsubst0.
        assert(wf_local Σ (subst_instance_context u1 (arities_context (ind_bodies mdecl)))).
        { eapply (wf_local_instantiate _ (InductiveDecl mdecl));pcuic. destruct isdecl; eauto.
          simpl. rewrite -app_context_assoc in wfc; now apply All_local_env_app in wfc. }
        eapply (weaken_wf_local (subst_instance_context u1 (arities_context (ind_bodies mdecl)))) in wfparinds'; eauto.
        rewrite app_context_assoc in wfparinds'.
        eapply (weaken_wf_local Γ) in wfparinds'; eauto.
        rewrite app_context_assoc in wfparinds'.
        unshelve epose proof (substitution_wf_local _ _ _ _ _ wf _ wfparinds') as w'. shelve.
        eapply subslet_app; first last. eapply (weaken_subslet _ _ _ _ []); eauto. eapply subslet_inds; eauto.
        rewrite closed_ctx_subst. auto. eapply cparsubst0.
        move: (weakening_wf_local _ _ _ _ wf w' w).
        autorewrite with len.
        clear -w lencpar. rewrite lencpar.
        rewrite -subst_app_context. rewrite lift_context_subst_context.
        now rewrite -subst_instance_lift_context. }
      rewrite {2}subst_instance_lift_context in instsp.
      rewrite -lift_context_subst_context in instsp.
      rewrite subst_app_context in instsp.
      assert(closedind : closedn_ctx #|ind_params mdecl| (subst_instance_context u1 (ind_indices oib))).
      unshelve epose proof (on_minductive_wf_params_indices _ _ _ _ _ _ oib); simpl; auto.
      destruct decli; auto.
      eapply closed_wf_local in X. rewrite closedn_ctx_app in X.
      move/andP: X => [_ X]. now rewrite closedn_subst_instance_context.
      simpl;  auto.
      rewrite (closed_ctx_subst _ _ (subst_instance_context u1 (ind_indices oib))) in instsp.    
      now rewrite -lencpar.

      assert((map (subst (cparsubst ++ inds (inductive_mind ind) u1 (PCUICAst.ind_bodies mdecl)) #|cshape_args cs|)
      (map (subst_instance_constr u1) (cshape_indices cs))) = 
      (map
      (fun x : term =>
      subst cparsubst #|argctx|
        (subst (inds (inductive_mind ind) u1 (ind_bodies mdecl)) (#|argctx| + #|cparsubst|) (subst_instance_constr u1 x)))
     (cshape_indices cs))).
      rewrite map_map_compose. apply map_ext=> x.
      now rewrite subst_app_simpl.
      rewrite H0 in insts, instsp. clear H0.

      apply wf_arity_spine_typing_spine => //.
      split.
      ** left.
         eexists _, _.
         rewrite destArity_it_mkProd_or_LetIn /=. split; [reflexivity|].
         rewrite app_context_nil_l. simpl.         
         constructor; auto. apply (spine_codom_wf _ _ _ _ _ instsp).
         red.
         autorewrite with len.
         rewrite lift_mkApps /=.
         rewrite !map_app !map_map_compose.
         exists (subst_instance_univ u1 (ind_sort oib)).
         eapply type_mkApps. econstructor; eauto.
         apply (spine_codom_wf _ _ _ _ _ instsp).
         apply wf_arity_spine_typing_spine => //.
         split.
         destruct (oib.(onArity)) as [s' Hs].
         eapply (instantiate_minductive _ _ _ u1) in Hs; eauto.
         2:pcuic. right; exists (subst_instance_univ u1 s'). red.
         eapply weaken_ctx in Hs. simpl in Hs. eauto. auto.
         now eapply spine_codom_wf.
         
         rewrite oib.(ind_arity_eq).
         rewrite subst_instance_constr_it_mkProd_or_LetIn.
         eapply arity_spine_it_mkProd_or_LetIn; eauto.
         { set (foo:=map (lift #|argctx| #|ind_indices oib| ∘ lift0 #|ind_indices oib|)
            cparsubst).
          clear -instsp wf cparsubst0 H.
          eapply (spine_subst_weakening _ _ _ _ _ (subst_context cparsubst 0
            (subst_context (inds (inductive_mind ind) u1 (ind_bodies mdecl))
              #|cparsubst| (map_context (subst_instance_constr u1) argctx)))) in cparsubst0; auto.
          rewrite closed_ctx_lift in cparsubst0 => //.
          autorewrite with len in cparsubst0.
          eapply (spine_subst_weakening _ _ _ _ _
            (lift_context #|argctx| 0
              (subst_context cparsubst 0 (subst_instance_context u1 (ind_indices oib)))))
              in cparsubst0 => //.
          autorewrite with len in cparsubst0.
          rewrite (closed_ctx_lift #|ind_indices oib|) in cparsubst0 => //.
          rewrite !map_map_compose in cparsubst0.
          rewrite - !simpl_map_lift. apply cparsubst0.
          apply (spine_codom_wf _ _ _ _ _ instsp).
          apply (spine_dom_wf _ _ _ _ _ instsp). }
        rewrite subst_instance_constr_it_mkProd_or_LetIn subst_it_mkProd_or_LetIn.
        simpl.
        rewrite lift_to_extended_list_k.
        rewrite -(app_nil_r (to_extended_list_k _ _)).
        eapply arity_spine_it_mkProd_or_LetIn; [auto|auto|constructor].
        assert ((subst_context
        (map
           (fun x : term =>
            lift #|argctx| #|ind_indices oib| (lift0 #|ind_indices oib| x))
           cparsubst) 0 (subst_instance_context u1 (ind_indices oib))) = 
          (lift_context #|ind_indices oib| 0
           (lift_context #|argctx| 0
            (subst_context cparsubst 0 (subst_instance_context u1 (ind_indices oib)))))).
        { rewrite -simpl_map_lift.
          rewrite lift_context_lift_context distr_lift_subst_context.
          rewrite map_lift_lift. f_equal.
          rewrite closed_ctx_lift -?lencpar ?Nat.add_0_r; auto. }
        rewrite simpl_map_lift.
        rewrite H0.
        have sps := spine_subst_to_extended_list_k Σ (lift_context #|argctx| 0
        (subst_context cparsubst 0 (subst_instance_context u1 (ind_indices oib)))).
        autorewrite with len in sps.
        rewrite [reln _ _ _]to_extended_list_k_fold_context in sps.
        rewrite to_extended_list_k_fold_context in sps.
        rewrite PCUICSubstitution.map_subst_instance_constr_to_extended_list_k in sps.
        apply sps; auto.
        apply (spine_codom_wf _ _ _ _ _ instsp).
        left; eexists _, _; split;  simpl; eauto.
        apply (spine_codom_wf _ _ _ _ _ instsp).
        reflexivity.

      ** eapply arity_spine_it_mkProd_or_LetIn; eauto.
         simpl. rewrite -(app_nil_r [mkApps _ _]).
         constructor; [|constructor].
         2:{ left; eexists _, _; simpl; split; eauto. apply (spine_dom_wf _ _ _ _ _ instsp). }
         2:{ simpl; reflexivity. }
         rewrite lift_mkApps subst_mkApps /=.
         autorewrite with len.
         eapply type_mkApps. econstructor; eauto; pcuic.
         apply (spine_dom_wf _ _ _ _ _ instsp).
         simpl.
         apply wf_arity_spine_typing_spine => //.
         split.
         unshelve epose proof (declared_constructor_valid_ty _ _ _ _ _ _ _ u1 wf (spine_dom_wf _ _ _ _ _ instsp) _ Hu); eauto.
         split; eauto.
         right; eauto.
         
         unfold type_of_constructor.
         rewrite {1}[cdecl'.1.2]onc.(cstr_eq).
         rewrite subst_instance_constr_it_mkProd_or_LetIn subst_it_mkProd_or_LetIn.
         eapply arity_spine_it_mkProd_or_LetIn; eauto.
         rewrite (closed_ctx_subst (inds _ _ _) 0) => //.
         rewrite -(closed_ctx_lift #|argctx| 0 (subst_instance_context u1 (ind_params mdecl))) => //.
         eapply (spine_subst_weakening _ _ _ _ _ (subst_context cparsubst 0
         (subst_context (inds (inductive_mind ind) u1 (ind_bodies mdecl))
            #|cparsubst| (map_context (subst_instance_constr u1) argctx)))) in cparsubst0; auto.
         autorewrite with len in cparsubst0. apply cparsubst0.
         eapply (spine_dom_wf _ _ _ _ _ instsp).
         rewrite subst_instance_constr_it_mkProd_or_LetIn !subst_it_mkProd_or_LetIn.
         autorewrite with len.
         rewrite subst_instance_constr_mkApps !subst_mkApps.
         rewrite -(app_nil_r (to_extended_list_k argctx 0)).
         eapply arity_spine_it_mkProd_or_LetIn; auto.
         
         *** have sps := spine_subst_to_extended_list_k Σ 
           ( subst_context cparsubst 0
           (subst_context (inds (inductive_mind ind) u1 (ind_bodies mdecl))
              #|cparsubst| (map_context (subst_instance_constr u1) argctx))) Γ wf
              (spine_dom_wf _ _ _ _ _ instsp)
              .
              autorewrite with len in sps.
              rewrite [reln _ _ _]to_extended_list_k_fold_context in sps.
              rewrite to_extended_list_k_fold_context in sps.
              rewrite PCUICSubstitution.map_subst_instance_constr_to_extended_list_k in sps.
              eapply (spine_subst_eq sps).
              rewrite distr_lift_subst_context.
              rewrite !Nat.add_0_r -lencpar. rewrite closed_ctx_lift => //.
              eapply (wf_local_instantiate _ (InductiveDecl mdecl) _ u1) in wfc; eauto.
              2:{ destruct decli; eauto.  }
              clear -wf wfc isdecl Hu. rewrite !subst_instance_context_app in wfc.
              pose proof (substitution_wf_local Σ [] (subst_instance_context u1 (arities_context (ind_bodies mdecl)))).
              specialize (X (inds (inductive_mind ind) u1 (ind_bodies mdecl))
                (subst_instance_context u1 (ind_params mdecl) ,,, (map_context (subst_instance_constr u1) argctx)) wf).
              rewrite app_context_nil_l in X.
              forward X by eapply subslet_inds; eauto.
              rewrite app_context_assoc in X.
              specialize(X wfc). rewrite app_context_nil_l in X.
              eapply closed_wf_local in X; eauto.
              rewrite subst_context_app in X.
              rewrite closedn_ctx_app in X.
              autorewrite with len in X. simpl in X.
              now move/andP: X => [_ X].
          *** rewrite !map_map_compose !map_app.
              assert ((map (subst0 (ctx_inst_sub insts) ∘ lift #|argctx| #|ind_indices oib| ∘ lift0 #|ind_indices oib|)
                (firstn (PCUICAst.ind_npars mdecl) cargs)) = 
              map (lift #|argctx| 0) (firstn (PCUICAst.ind_npars mdecl) cargs)).
              { apply map_ext => x. 
                rewrite simpl_lift => //. lia.
                rewrite subst_lift_above => //.
                rewrite (ctx_inst_subst_length insts); auto.
                now rewrite List.rev_length; autorewrite with len. }
              rewrite !map_map_compose {}H0.
              assert ((map (subst0 (ctx_inst_sub insts) ∘ lift #|argctx| #|ind_indices oib|)
                (to_extended_list_k (ind_indices oib) 0)) = 
              (map
              (fun x : term =>
                subst cparsubst #|argctx|
                  (subst (inds (inductive_mind ind) u1 (ind_bodies mdecl))
                    (#|argctx| + #|cparsubst|) (subst_instance_constr u1 x)))
              (cshape_indices cs))).
              { rewrite -map_map_compose.
                rewrite lift_to_extended_list_k.
                pose proof (ctx_inst_sub_to_extended_list_k _ _ _ _ insts).
                rewrite List.rev_involutive in H0.
                rewrite to_extended_list_k_subst in H0.
                rewrite PCUICSubstitution.map_subst_instance_constr_to_extended_list_k in H0.
                rewrite /lift_context to_extended_list_k_fold_context in H0.
                rewrite H0. reflexivity. }
              rewrite {}H0.
              constructor.
              { right. exists (subst_instance_univ u1 (ind_sort oib)).
                eapply type_mkApps. econstructor; eauto.
                apply (spine_dom_wf _ _ _ _ _ instsp).
                destruct (oib.(onArity)) as [s' Hs].
                eapply wf_arity_spine_typing_spine => //.
                split.
                eapply (instantiate_minductive _ _ _ u1) in Hs; eauto.
                2:pcuic.
                eapply weaken_ctx in Hs. simpl in Hs. right; exists (subst_instance_univ u1 s'). red. eauto. auto.
                now eapply spine_dom_wf.
                rewrite oib.(ind_arity_eq).
                rewrite subst_instance_constr_it_mkProd_or_LetIn.
                eapply arity_spine_it_mkProd_or_LetIn; eauto.
                { set (foo:=map (lift #|argctx| #|ind_indices oib| ∘ lift0 #|ind_indices oib|)
                    cparsubst).
                  clear -instsp wf cparsubst0 H.
                  eapply (spine_subst_weakening _ _ _ _ _ (subst_context cparsubst 0
                    (subst_context (inds (inductive_mind ind) u1 (ind_bodies mdecl))
                      #|cparsubst| (map_context (subst_instance_constr u1) argctx)))) in cparsubst0; auto.
                  rewrite closed_ctx_lift in cparsubst0 => //.
                  autorewrite with len in cparsubst0.
                  eapply cparsubst0.                  
                  apply (spine_dom_wf _ _ _ _ _ instsp). }
                rewrite subst_instance_constr_it_mkProd_or_LetIn subst_it_mkProd_or_LetIn.
                rewrite -(app_nil_r (map _ (cshape_indices _))).
                eapply arity_spine_it_mkProd_or_LetIn; [auto|auto|constructor].
                2:{ left; eexists _, _; split; simpl; eauto. now eapply spine_dom_wf. }
                eapply (spine_subst_eq instsp).
                rewrite distr_lift_subst_context.
                rewrite closed_ctx_lift ?Nat.add_0_r -?lencpar //.
                simpl. reflexivity. }

              rewrite subst_mkApps.
              apply conv_cumul.
              rewrite /cstr_concl_head.
              rewrite subst_inds_concl_head.
              { simpl. destruct decli. now eapply nth_error_Some_length in H2. }
              simpl. apply mkApps_conv_args; auto.
               
              rewrite map_app. eapply All2_app.
              ****
                eapply (All2_impl (P:=fun x y => x = y)).
                2:{ intros ? ? ->. reflexivity. }
                eapply All2_eq_eq.
                rewrite -(map_map_compose _ _ _ (subst_instance_constr _)
                                          (fun x => subst _ _ (subst _ _ x))).
                rewrite subst_instance_to_extended_list_k.
                rewrite -(map_map_compose _ _ _ (subst _ _)).
                rewrite -(subst_instance_context_length u1 (ind_params mdecl)).
                rewrite -to_extended_list_k_map_subst; [lia|].
                erewrite subst_to_extended_list_k.
                2:{ eapply make_context_subst_spec_inv. rewrite List.rev_involutive.
                    rewrite -[subst_instance_context _ _](closed_ctx_lift #|argctx| 0) => //.
                      apply context_subst_lift.
                    apply (cparsubst0.(inst_ctx_subst)). }
                rewrite map_map_compose.
                rewrite map_subst_lift_id_eq. now autorewrite with len.
                reflexivity.
              ****
                set (instargctx := subst_context cparsubst 0 (subst_context _ #|cparsubst| _)) in *.
                rewrite -{1}lencpar in instsp.
                assert(#|instargctx| = #|argctx|).
                { subst instargctx  ; now  autorewrite with len. }
                unfold argctx in H0.
                rewrite -{3}H0 -(all_rels_length instargctx 0 #|argctx|).
                rewrite -(map_map_compose _ _ _ _ (subst cparsubst #|argctx|)).
                rewrite -(map_map_compose _ _ _ (subst_instance_constr u1)).
                rewrite -(map_map_compose _ _ _
                                          (subst _ _ ∘ (subst_instance_constr u1))).
                rewrite map_map_compose.
                eapply All2_map. rewrite -lencpar.
                rewrite !map_map_compose.
                assert (All (fun x => closedn (#|cparsubst| + #|instargctx|) x) (map
                (subst (inds (inductive_mind ind) u1 (PCUICAst.ind_bodies mdecl))
                   (#|cshape_args cs| + #|ind_params mdecl|)
                 ∘ subst_instance_constr u1) (cshape_indices cs))).
                { rewrite map_map_compose in closedindices.
                  eapply (All_impl closedindices).
                  intros. now rewrite -lencpar H0 Nat.add_comm. }  
                apply (All_All2 X).
                intros. rewrite all_rels_length.
                pose proof (all_rels_subst Σ instargctx Γ (subst cparsubst #|argctx| x) wf (spine_dom_wf _ _ _ _ _ instsp)).
                eapply red_conv in X0.
                assert(subst (map (lift0 #|argctx|) cparsubst) #|instargctx| x =
                  (lift #|argctx| #|argctx| (subst cparsubst #|argctx| x))).
                { epose proof (distr_lift_subst_rec _ _ #|argctx| #|argctx| 0) as l.
                  rewrite Nat.add_0_r in l. rewrite -> l. f_equal. now rewrite H0.
                  rewrite H0 in H2. subst argctx.
                  rewrite lift_closed. eapply closed_upwards; eauto. lia. reflexivity. }
                rewrite H3.
                rewrite H0 in X0.
                symmetry in X0.
                apply X0.

    * rewrite subst_mkApps.
      pose proof (context_subst_length _ _ _ idxsubst0).
      rewrite !subst_context_length subst_instance_context_length in H.
      rewrite -{1}(Nat.add_0_r #|argctx|) (simpl_subst' _ _ 0 _ #|argctx|) /argctx; try lia; auto.
      rewrite lift0_id. f_equal.
      rewrite map_app /= subst_mkApps. f_equal.
      f_equal. simpl. f_equal.
      rewrite map_app -{1}(firstn_skipn (ind_npars mdecl) cargs).
      f_equal. rewrite map_map_compose.
      now rewrite H map_subst_lift_id.
      unfold to_extended_list.
      erewrite subst_to_extended_list_k. rewrite map_id_f. intros x; apply lift0_id.
      reflexivity.
      apply make_context_subst_spec_inv. rewrite List.rev_involutive.
      apply idxsubst0.
    * right.
      exists ps.
      eapply type_mkApps. eauto.
      eapply wf_arity_spine_typing_spine => //.
      split.
      ** now eapply validity in typep.
      ** eapply arity_spine_it_mkProd_or_LetIn => //.
         eauto.
         simpl. constructor.
         2:constructor; auto; eauto 4 with pcuic.
         2:left; eexists _, _; intuition auto.
        rewrite subst_mkApps. 
        rewrite map_app.
        pose proof (subslet_length subsidx).
        autorewrite with len in H. rewrite -H.
        rewrite map_map_compose map_subst_lift_id.
        pose proof (spine_subst_subst_to_extended_list_k subsidx).
        rewrite to_extended_list_k_fold_context in H0.
        rewrite PCUICSubstitution.map_subst_instance_constr_to_extended_list_k  in H0.
        rewrite {}H0. now rewrite firstn_skipn /=.
    * simpl in Hbr. rewrite Hbr in a. intuition discriminate.
    * eapply on_declared_minductive => //.
      destruct isdecl; auto.

  - (* Case congruence: on a cofix, impossible *)
    eapply inversion_mkApps in typec as [? [tcof ?]] =>  //.
    eapply type_tCoFix_inv in tcof as [d [[[Hnth wfcofix] ?] ?]] => //.
    unfold unfold_cofix in e.
    rewrite Hnth in e. noconf e.
    clear heq_map_option_out X5 heq_build_case_predicate_type forall_u.
    eapply typing_spine_strengthen in t; eauto. clear c.
    eapply wf_cofixpoint_typing_spine in t; eauto.
    2:eapply validity_term; eauto.
    unfold check_recursivity_kind in t.
    rewrite isdecl.p1 in t.
    apply PCUICReflect.eqb_eq in t. rewrite t /= in heq_isCoFinite.
    discriminate.

  - (* Case congruence on the predicate *) 
    eapply (type_Cumul _ _ _ (mkApps p' (skipn npar args ++ [c]))).
    eapply build_branches_type_red in heq_map_option_out as [brtys' [eqbrtys alleq]]; eauto.
    eapply type_Case; eauto.
    * eapply All2_trans'; eauto. simpl.
      intros.
      intuition auto. now transitivity y.1.
      eapply type_Cumul; eauto.
      now eapply conv_cumul, red_conv, red1_red.
    * right.
      pose proof typec as typec'.
      eapply (env_prop_typing _ _ validity) in typec' as wat; auto.
      unshelve eapply isWAT_mkApps_Ind in wat as [parsubst [argsubst wat]]; eauto.
      set (oib := on_declared_inductive wf isdecl) in *. clearbody oib.
      destruct oib as [onind oib].
      destruct wat  as [[spars sargs] cu].
      unshelve eapply (build_case_predicate_type_spec (Σ.1, _)) in heq_build_case_predicate_type as [parsubst' [cparsubst Hpty]]; eauto.
      rewrite {}Hpty in typep.
      exists ps.
      subst npar.
      pose proof (context_subst_fun cparsubst spars). subst parsubst'. clear cparsubst.
      eapply type_mkApps. eauto.
      eapply wf_arity_spine_typing_spine; eauto.
      split. apply (env_prop_typing _ _ validity) in typep as ?; eauto.
      eapply arity_spine_it_mkProd_or_LetIn; eauto.
      simpl. constructor; [ |constructor].
      2:{ left; eexists _, _; split. simpl; eauto. auto. }
      2:reflexivity.
      rewrite subst_mkApps. simpl.
      rewrite map_app. rewrite map_map_compose.
      rewrite map_subst_lift_id_eq. now rewrite (subslet_length sargs); autorewrite with len.
      move: (spine_subst_subst_to_extended_list_k sargs).
      rewrite to_extended_list_k_subst PCUICSubstitution.map_subst_instance_constr_to_extended_list_k.
      move->. now rewrite firstn_skipn.
    * now eapply conv_cumul, conv_sym, red_conv, red_mkApps_f, red1_red.

  - (* Case congruence on discriminee *) 
    eapply type_Cumul. eapply type_Case; eauto.
    * solve_all.
    * right.
      pose proof typec as typec'.
      eapply (env_prop_typing _ _ validity) in typec' as wat; auto.
      unshelve eapply isWAT_mkApps_Ind in wat as [parsubst [argsubst wat]]; eauto.
      set (oib := on_declared_inductive wf isdecl) in *. clearbody oib.
      destruct oib as [onind oib].
      destruct wat  as [[spars sargs] cu].
      unshelve eapply (build_case_predicate_type_spec (Σ.1, _)) in heq_build_case_predicate_type as [parsubst' [cparsubst Hpty]]; eauto.
      rewrite {}Hpty in typep.
      exists ps.
      subst npar.
      pose proof (context_subst_fun cparsubst spars). subst parsubst'. clear cparsubst.
      eapply type_mkApps. eauto.
      eapply wf_arity_spine_typing_spine; eauto.
      split. apply (env_prop_typing _ _ validity) in typep; eauto.
      eapply arity_spine_it_mkProd_or_LetIn; eauto.
      simpl. constructor; [ |constructor].
      2:{ left; eexists _, _; split. simpl; eauto. auto. }
      2:reflexivity.
      rewrite subst_mkApps. simpl.
      rewrite map_app. rewrite map_map_compose.
      rewrite map_subst_lift_id_eq. now rewrite (subslet_length sargs); autorewrite with len.
      move: (spine_subst_subst_to_extended_list_k sargs).
      rewrite to_extended_list_k_subst PCUICSubstitution.map_subst_instance_constr_to_extended_list_k.
      move->. now rewrite firstn_skipn.
    * eapply conv_cumul, conv_sym, red_conv, red_mkApps; auto.
      eapply All2_app; [eapply All2_refl; reflexivity|now constructor].

  - (* Case congruence on branches *)
    eapply type_Case; eauto.
    eapply (OnOne2_All2_All2 o X5).
    intros [] []; simpl. intros.
    intuition auto. subst.
    intros [] [] []; simpl. intros.
    intuition auto. subst.    
    reflexivity.

  - (* Proj CoFix congruence *)
    assert(typecofix : Σ ;;; Γ |- tProj p (mkApps (tCoFix mfix idx) args0) : subst0 (mkApps (tCoFix mfix idx) args0 :: List.rev args)
      (subst_instance_constr u pdecl.2)).
    { econstructor; eauto. }

    pose proof (env_prop_typing _ _  validity _ _ _ _ _ typec).
    eapply inversion_mkApps in typec as [? [tcof tsp]]; auto.
    eapply type_tCoFix_inv in tcof as [d [[[Hnth wfcofix] Hbody] Hcum]]; auto.
    unfold unfold_cofix in e.
    rewrite Hnth in e. noconf e.
    simpl in X1.
    eapply type_Cumul; [econstructor|..]; eauto.
    eapply typing_spine_strengthen in tsp; eauto.
    eapply type_mkApps. eauto. eauto.
    now eapply validity in typecofix.
    eapply conv_cumul.
    rewrite (subst_app_decomp [mkApps (subst0 (cofix_subst mfix) (dbody d)) args0]) (subst_app_decomp [mkApps (tCoFix mfix idx) args0]).
    eapply conv_sym, red_conv.
    destruct (on_declared_projection wf isdecl) as [oi onp].
    epose proof (subslet_projs _ _ _ _ wf (let (x, _) := isdecl in x)).
    set (oib := declared_inductive_inv _ _ _ _) in *. simpl in onp, X2.
    destruct (ind_cshapes oib) as [|? []]; try contradiction.
    destruct onp as [[[tyargctx onps] Hp2] onp].
    specialize (X2 onps).
    red in onp.
    destruct (nth_error (smash_context [] _) _) eqn:Heq; try contradiction.
    destruct onp as [na eq].
    pose proof (on_projs_noidx _ _ _ _ _ _ onps).
    set (indsubst := inds _ _ _) in *.
    set (projsubst := projs _ _ _) in *.
    rewrite eq.
    eapply (substitution_untyped_red _ Γ
      (smash_context [] (subst_instance_context u (ind_params mdecl))) []). auto.
    { unshelve eapply isWAT_mkApps_Ind in X1 as [parsubst [argsubst Hind]]; eauto.
      eapply (let (x, _) := isdecl in x).
      unfold on_declared_inductive in Hind. fold oib in Hind. simpl in Hind.
      destruct Hind as [[sppars spargs] cu].
      rewrite firstn_all2 in sppars. lia.
      eapply spine_subst_smash in sppars.
      eapply subslet_untyped_subslet. eapply sppars. auto. }
    rewrite - !subst_subst_instance_constr.
    rewrite distr_subst.
    rewrite distr_subst.
    rewrite distr_subst.
    autorewrite with len.
    rewrite -lift_subst_instance_constr.
    rewrite -(Nat.add_1_r (ind_npars mdecl)) Nat.add_assoc.
    rewrite {2 5}/projsubst. autorewrite with len.
    rewrite -(commut_lift_subst_rec _ _ 1 (#|projsubst| + ind_npars mdecl)).
    rewrite /projsubst. autorewrite with len. lia.
    rewrite !simpl_subst_k //.
    rewrite projs_subst_instance_constr. 
    rewrite projs_subst_above //. lia. simpl.
    rewrite !subst_projs_inst !projs_inst_lift.
    eapply (red_red _ (Γ ,,, smash_context [] (subst_instance_context u (ind_params mdecl)))
       (skipn (context_assumptions (cshape_args c) - p.2) 
       (smash_context [] (subst_context (inds (inductive_mind p.1.1) u (ind_bodies mdecl)) #|ind_params mdecl| (subst_instance_context u (cshape_args c))))) []); auto.
    ** eapply All2_map.
      eapply (All2_impl (P:=fun x y => red Σ.1 Γ x y)).
      2:{ intros x' y' hred. rewrite heq_length.
          eapply weakening_red_0; auto. autorewrite with len.
          pose proof (onNpars _ _ _ _ oi). simpl; lia. }
      elim: p.2. simpl. constructor.
      intros n Hn. constructor; auto.
      eapply red1_red. eapply red_cofix_proj. eauto.
      unfold unfold_cofix. rewrite Hnth. reflexivity.
    ** rewrite -projs_inst_lift.
      rewrite -subst_projs_inst.
      assert (p.2 = context_assumptions (cshape_args c) - (context_assumptions (cshape_args c) - p.2)) by lia.
      rewrite {1}H0. rewrite -skipn_projs map_skipn subst_projs_inst.
      eapply untyped_subslet_skipn. destruct p as [[[? ?] ?] ?]. simpl in *.
      rewrite /indsubst.
      eapply X2.

  - (* Proj Constructor reduction *) 
    pose proof (env_prop_typing _ _ validity _ _ _ _ _ typec).
    simpl in typec.
    pose proof typec as typec'.
    eapply inversion_mkApps in typec as [A [tyc tyargs]]; auto.
    eapply (inversion_Construct Σ wf) in tyc as [mdecl' [idecl' [cdecl' [wfl [declc [Hu tyc]]]]]].
    pose proof typec' as typec''.
    unshelve eapply Construct_Ind_ind_eq in typec'; eauto.
    unfold on_declared_constructor in typec'.
    destruct declc as [decli declc].
    unfold on_declared_inductive in typec'.
    destruct declared_constructor_inv as [cs [Hnth onc]].
    simpl in typec'.
    pose proof isdecl as isdecl'.
    destruct isdecl' as [decli' [H0 Hi]].
    destruct (declared_inductive_inj decli' decli) as []; subst mdecl' idecl'.
    simpl in decli'.
    set (pdecl' := conj decli isdecl.p2 : declared_projection Σ.1 mdecl idecl (i, pars, narg) pdecl).
    epose proof (declared_projection_type_and_eq wf pdecl').
    simpl in X2.
    pose proof (subslet_projs Σ _ _ _ _ decli) as projsubsl.
    destruct declared_inductive_inv. simpl in *.
    forward onProjections. clear pdecl'.
    eapply nth_error_Some_length in H0. simpl in H0.
    intros Hp. apply (f_equal (@length _)) in Hp. rewrite  Hp /=   in H0. lia.
    simpl in H0.
    simpl in *.
    destruct typec' as [[[[_ equ] cu] eqargs] [cparsubst [cargsubst [iparsubst [iidxsubst ci]]]]].
    destruct ci as ((([cparsubst0 iparsubst0] & idxsubst0) & subsidx) & [s [typectx [Hpars Hargs]]]).
    destruct ind_cshapes as [|? []]; try contradiction.
    destruct X2 as [projty projeq].
    destruct k; simpl in *; try discriminate. noconf Hnth.
    2:{ rewrite nth_error_nil in Hnth. discriminate. }
    specialize (projsubsl onProjections).
    destruct onProjections.
    pose proof (on_declared_minductive wf isdecl.p1.p1) as onmind.
    eapply nth_error_alli in on_projs; eauto.
    eapply typing_spine_strengthen in tyargs; eauto.
    rewrite -(firstn_skipn (ind_npars mdecl) args0) in tyargs, e |- *.
    subst pars.
    assert(#|firstn (ind_npars mdecl) args0| = ind_npars mdecl).
    rewrite firstn_length_le. lia. lia.
    rewrite nth_error_app_ge in e. lia.
    rewrite H in e. replace (ind_npars mdecl + narg - ind_npars mdecl) with narg in e by lia.
    epose proof (declared_constructor_valid_ty _ _ _ _ _ 0 cdecl' _ wf wfΓ) as Hty.
    forward Hty by (split; eauto).
    forward Hty. eapply Hu.
    unfold type_of_constructor in tyargs, Hty.
    rewrite [cdecl'.1.2]onc.(cstr_eq) in tyargs, Hty.
    rewrite !subst_instance_constr_it_mkProd_or_LetIn !subst_it_mkProd_or_LetIn in tyargs, Hty.
    eapply typing_spine_inv in tyargs as [arg_sub [[spargs iswat] sp]]; eauto.
    3:{ right; simpl; auto. }
    2:{ rewrite !context_assumptions_fold.
        rewrite subst_instance_context_assumptions. rewrite H.
        apply onNpars in onmind. lia. }
    clear Hty.
    rewrite subst_it_mkProd_or_LetIn in sp, iswat.
    rewrite !subst_instance_constr_mkApps !subst_mkApps in sp, iswat.
    eapply typing_spine_nth_error in sp; eauto.
    clear iswat.
    2:{ rewrite !context_assumptions_fold. rewrite subst_instance_context_assumptions.
        clear iswat sp. eapply nth_error_Some_length in H0. lia. }
    destruct sp as [decl [Hnth Hu0]].
    simpl in on_projs. red in on_projs.
    eapply type_Cumul; eauto.
    * rewrite firstn_skipn.
      eapply (isType_subst_instance_decl (u:=u) wf isdecl.p1.p1) in projty; eauto.
      right. destruct projty as [s' Hs].
      exists s'. red in Hs.
      rewrite /= /map_decl /= in Hs.
      eapply (weaken_ctx Γ) in Hs; auto.
      rewrite (subst_app_simpl [_]).
      eapply (substitution0 _ _ _ _ _ _ (tSort s')). auto.
      simpl.
      eapply (substitution _ Γ (subst_instance_context u (smash_context [] (ind_params mdecl)))
        _ [vass _ _] _ (tSort s')); eauto.
      rewrite firstn_all2 in iparsubst0. lia.
      eapply spine_subst_smash in iparsubst0; auto.
      rewrite subst_instance_context_smash.
      eapply iparsubst0. simpl.
      rewrite subst_instance_constr_mkApps subst_mkApps /=.
      rewrite (subst_instance_instance_id Σ) // subst_instance_to_extended_list.
      rewrite firstn_all2 in iparsubst0. lia.
      eapply spine_subst_smash in iparsubst0; auto.
      rewrite subst_instance_context_smash /=.
      rewrite /to_extended_list (spine_subst_subst_to_extended_list_k iparsubst0).
      assumption.
    * eapply conv_cumul.
      rewrite !context_assumptions_fold subst_instance_context_assumptions in Hnth.
      rewrite firstn_skipn.
      rewrite smash_context_app smash_context_acc in on_projs.
      rewrite nth_error_app_lt in on_projs.
      { autorewrite with len. simpl. 
        eapply nth_error_Some_length in Hnth. autorewrite with len in Hnth.
        now simpl in Hnth. }
      rewrite nth_error_subst_context in on_projs.
      epose proof (nth_error_lift_context_eq _ (smash_context [] (ind_params mdecl))).
      autorewrite with len in H1. simpl in H1.
      erewrite -> H1 in on_projs. clear H1.
      rewrite (smash_context_subst []) in Hnth.
      rewrite (smash_context_subst []) in Hnth.
      rewrite -(subst_instance_context_smash u1 _ []) in Hnth.
      rewrite !nth_error_subst_context in Hnth.
      rewrite nth_error_map in Hnth.
      destruct projeq as [decl' [[[Hdecl wfdecl] Hty1] Hty2]].
      rewrite Hdecl in on_projs, Hnth.
      simpl in on_projs, Hnth.
      destruct on_projs as [declna decltyeq].
      noconf Hnth. simpl in *.
      autorewrite with len in Hu0, decltyeq |- *.
      simpl in Hu0, decltyeq |- *.
      move: Hu0 decltyeq.
      assert (narg < context_assumptions (cshape_args cs)).
      eapply nth_error_Some_length in H0. lia.
      replace (context_assumptions (cshape_args cs) -
        S (context_assumptions (cshape_args cs) - S narg))
        with narg by lia.
      move=> Hu0 decltyeq.
      rewrite -Hty1. clear decltyeq.
      rewrite Hty2.
      unfold projection_type'.
      set (indsubst1 := inds _ _ _).
      set (indsubst := inds _ _ _).
      set (projsubst := projs _ _ _).
      rewrite - !subst_subst_instance_constr.
      rewrite -lift_subst_instance_constr.
      rewrite - !subst_subst_instance_constr.
      epose proof (commut_lift_subst_rec _ _ 1 narg narg).
      rewrite Nat.add_1_r in H2. rewrite <- H2 => //. clear H2.
      rewrite (subst_app_decomp [_]).
      autorewrite with len. rewrite heq_length.
      simpl. rewrite lift_mkApps. simpl.
      rewrite (distr_subst [_]). simpl.
      autorewrite with len. rewrite {2}/projsubst projs_length.
      rewrite simpl_subst_k // subst_instance_constr_projs.
      epose proof (subst_app_simpl (List.rev (firstn narg (skipn (ind_npars mdecl) args0))) _ 0).
      autorewrite with len in H2.  simpl in H2.
      assert(#|firstn narg (skipn (ind_npars mdecl) args0)| = narg).
      { rewrite firstn_length_le. rewrite skipn_length. lia. lia. lia. }
      rewrite H3 in H2. rewrite <- H2. clear H2.
      rewrite subst_app_decomp.
      epose proof (subst_app_simpl 
      (map
      (subst0
         [mkApps (tConstruct i 0 u1) (map (lift0 (ind_npars mdecl)) args0)])
      (projs i (ind_npars mdecl) narg))).
      autorewrite with len in H2.
      rewrite -H2. clear H2.
      rewrite subst_app_decomp.
      autorewrite with len.
      rewrite (distr_subst (List.rev args)).
      autorewrite with len.
      assert (map (subst0 (List.rev args))
      (map (subst_instance_constr u) (extended_subst (ind_params mdecl) 0))  = 
        iparsubst) as ->. 
      { rewrite firstn_all2 in iparsubst0. lia.
        rewrite extended_subst_subst_instance_constr.
        pose proof (inst_ctx_subst iparsubst0).
        eapply context_subst_extended_subst in X2.
        rewrite X2. eapply map_ext.
        intros. now rewrite subst_inst Upn_0. }
      eapply (subst_conv _ _ _ []).
      { auto. }
      { eapply spargs. } 
      { eapply iparsubst0. }
      { eapply spine_subst_conv. auto. 
        eapply spargs. eapply iparsubst0.
        rewrite closed_ctx_subst.
        eapply closed_wf_local; eauto.
        eapply on_minductive_wf_params; eauto. eapply decli.
        eapply context_relation_subst_instance; eauto.
        eapply on_minductive_wf_params; eauto. eapply decli.
        eapply Hpars. }
      { simpl.
        eapply weaken_wf_local; auto.
        rewrite closed_ctx_subst.
        eapply closed_wf_local; eauto.
        eapply on_minductive_wf_params; eauto. eapply decli.
        eapply on_minductive_wf_params; eauto. eapply decli. }
      simpl.
      rewrite distr_subst. autorewrite with len.
      simpl.
      do 2 rewrite map_map_compose.
      pose proof (subslet_length spargs).
      set (real_args0 := skipn (ind_npars mdecl) args0) in *.
      eapply firstn_length_le_inv in H3.
      assert (narg = #|real_args0| - (#|real_args0| - narg)) by lia.
      assert ((map
        (fun x : term =>
        subst (List.rev args) #|ind_params mdecl|
          (lift0 #|ind_params mdecl|
              (subst0
                [mkApps (tConstruct i 0 u1)
                    (map (lift0 (ind_npars mdecl)) args0)] x)))
        (projs i (ind_npars mdecl) narg))  = 
        (map
        (fun x : term =>
          (subst0
              [mkApps (tConstruct i 0 u1) (map (lift0 #|ind_params mdecl|) args0)] x))
            (projs i (ind_npars mdecl) narg))) as ->.
      { clear -eqargs heq_length.
        induction narg. simpl. reflexivity.
        simpl. f_equal. 2:auto.
        f_equal. rewrite !lift0_id.
        rewrite lift_mkApps subst_mkApps /=. f_equal.
        rewrite [map (lift0 _) _]map_map_compose.
        rewrite map_lift_lift. rewrite Nat.add_comm.
        rewrite map_map_compose.
        rewrite map_subst_lift_ext //.
        now autorewrite with len. }
      assert(wfctx : wf_local Σ
      (Γ ,,,
       subst_context (inds (inductive_mind i) u1 (ind_bodies mdecl)) 0
         (subst_instance_context u1 (PCUICEnvironment.ind_params mdecl)) ,,,
       lift_context
         #|subst_context (inds (inductive_mind i) u1 (ind_bodies mdecl)) 0
             (subst_instance_context u1 (PCUICEnvironment.ind_params mdecl))| 0
         (skipn (#|real_args0| - narg)
            (smash_context []
               (subst_context cparsubst 0
                  (subst_context (inds (inductive_mind i) u1 (ind_bodies mdecl))
                     #|ind_params mdecl|
                     (subst_instance_context u1 (cshape_args cs)))))))).
      { autorewrite with len.
        simpl. 
        fold indsubst1 in |- *.
        epose proof (weakening_wf_local Σ Γ _ (subst_context indsubst1 0 (subst_instance_context u1 (ind_params mdecl)))).
        autorewrite with len in X2.
        eapply X2; clear X2; auto.
        2:eapply spine_codom_wf; eauto.
        eapply All_local_env_app_inv. split; auto.
        eapply All_local_env_skipn.
        eapply wf_local_rel_smash_context; auto.
        eapply spine_codom_wf; eauto. }
      eapply (untyped_subst_conv (Γ ,,, _) _ _ []); auto.
      + move idxsubst0 at bottom.
        rewrite H2.
        eapply subslet_untyped_subslet.
        eapply subslet_lift; auto. apply wf. auto. eapply (spine_codom_wf _ _ _ _ _ spargs).
        eapply spine_subst_smash in idxsubst0.
        2:auto.
        eapply inst_subslet in idxsubst0.
        rewrite {1}H4. rewrite -skipn_rev.
        eapply subslet_skipn in idxsubst0. eapply idxsubst0.
      + specialize (projsubsl (Γ ,,,
      subst_context (inds (inductive_mind i) u1 (ind_bodies mdecl)) 0
        (subst_instance_context u1 (PCUICEnvironment.ind_params mdecl))) 
        (mkApps (tConstruct i 0 u1) (map (lift0 #|ind_params mdecl|) args0))
        u).
         eapply (untyped_subslet_skipn _ _ _ (#|real_args0| - narg)) in projsubsl.
        eapply untyped_subslet_eq_subst.
        eapply projsubsl.
        rewrite -subst_projs_inst.
        rewrite -map_skipn skipn_projs.
        rewrite /real_args0 skipn_length. lia.
        f_equal. f_equal. lia.
      + rewrite /real_args0.
        rewrite H2; autorewrite with len.
        rewrite H4 -skipn_projs map_skipn -skipn_rev map_skipn.
        eapply All2_skipn.
        rewrite /real_args0.
        rewrite skipn_length. lia.

        rewrite subst_projs_inst.
        change (tConstruct i 0 u1) with (lift0 #|ind_params mdecl| (tConstruct i 0 u1)).
        rewrite -lift_mkApps projs_inst_lift. eapply All2_map.
        eapply (All2_impl (P:=fun x y => Σ ;;; Γ |- x = y)).
        2:{ intros. epose proof (weakening_conv _ Γ [] (subst_context (inds (inductive_mind i) u1 (ind_bodies mdecl)) 0
            (subst_instance_context u1 (ind_params mdecl)))).
            autorewrite with len in X3. eapply X3. auto. assumption. }
        eapply All2_from_nth_error.
        autorewrite with len. rewrite skipn_length //; lia.
        move=> n x1 x2. autorewrite with len. rewrite skipn_length //; try lia.
        move=> Hn Hx1. rewrite nth_error_projs_inst //.
        move=> [=] h. subst x2. rewrite eqargs minus_plus.
        eapply conv_sym. eapply red_conv.
        eapply red1_red, red_proj.
        rewrite -{}Hx1.
        rewrite (nth_error_rev (List.rev _)). autorewrite with len.
        rewrite skipn_length //; lia.
        rewrite List.rev_involutive nth_error_skipn.
        autorewrite with len. f_equal.
        f_equal. rewrite skipn_length //; lia. 
      + simpl; auto.
      + assert (closedn (narg + #|ind_bodies mdecl| + #|ind_params mdecl|) (decl_type decl')).
        { clear projsubsl.
          eapply closed_wf_local in wfdecl.
          rewrite closedn_ctx_app in wfdecl.
          move/andP: wfdecl => [_ wfdecl].
          autorewrite with len in wfdecl.
          simpl in wfdecl.
          eapply closedn_ctx_decl in wfdecl; eauto.
          autorewrite with len in wfdecl.
          simpl in wfdecl.
          move/andP: wfdecl => [_ clty].
          eapply closed_upwards. eauto.
          lia. auto. }
      rewrite (subst_closedn (List.rev args)).
      eapply (closedn_subst _ 0).
      epose proof (PCUICClosed.declared_inductive_closed_inds _ _ _ _ _ wf decli).
      rewrite closed_map_subst_instance. eapply H6.
      rewrite /indsubst; autorewrite with len.
      rewrite closedn_subst_instance_constr.
      eapply closed_upwards; eauto; lia.
      autorewrite with len.
      pose proof(context_subst_length _ _ _ cparsubst0).
      autorewrite with len in H6. rewrite {2}H6.
      autorewrite with len in wfctx. move: wfctx.
      rewrite {2}H6.
      rewrite - !subst_app_context.
      rewrite !(smash_context_subst []).
      rewrite skipn_subst_context.
      rewrite subst_context_decompo.
      rewrite lift_context_subst_context.
      set(argctx := lift_context _ _ _) in *. move=> wfargctx.
      simpl.
      epose proof (untyped_subst_conv Γ _ _ (subst_instance_context u1 (ind_params mdecl) ,,, argctx) _ _ _ _); auto.
      rewrite subst_context_app in X2. autorewrite with len in X2.
      assert (#|argctx| = narg).
      rewrite /argctx; autorewrite with len.
      rewrite List.skipn_length. autorewrite with len. simpl.
      rewrite /real_args0 List.skipn_length eqargs. lia.
      rewrite H7 in X2.
      rewrite !app_context_assoc in X2.
      change (map (subst_instance_constr u)) with (subst_instance (A:=list term) u).
      rewrite /indsubst. 
      rewrite instantiate_inds; auto. eapply decli.
      eapply X2; clear X2; auto.
      ** eapply subslet_untyped_subslet.
        eapply PCUICArities.weaken_subslet; eauto.
        eapply subslet_inds; eauto.
      ** eapply subslet_untyped_subslet.
        eapply PCUICArities.weaken_subslet; eauto.
        eapply subslet_inds; eauto.
      ** eapply conv_inds => //.
      ** fold indsubst1 in |- *.
        eapply (wf_local_instantiate _ _ _ _ _ wf decli'.p1) in wfdecl.
        2:eapply Hu.
        eapply (weaken_wf_local Γ) in wfdecl; eauto.
        rewrite !subst_instance_context_app !app_context_assoc in wfdecl.
        apply All_local_env_app in wfdecl as [wfarpars wfsmash].
        epose proof (weakening_wf_local Σ (Γ ,,, subst_instance_context u1 (arities_context (ind_bodies mdecl))) _ 
          (subst_instance_context u1 (ind_params mdecl))).
        autorewrite with len in X2.
        rewrite /argctx. eapply X2; clear X2. all:auto.
        eapply substitution_wf_local; eauto.
        eapply spine_subst_weakening in cparsubst0; eauto.
        2:{ eapply All_local_env_app in wfarpars as [wfars _]. eapply wfars. }
        autorewrite with len in cparsubst0.
        rewrite inds_length. apply cparsubst0.
        rewrite closed_ctx_lift. eapply closed_wf_local. eauto.
        eapply on_minductive_wf_params; eauto. eapply decli. auto.
        eapply All_local_env_app_inv. split; auto.
        eapply All_local_env_skipn.
        now rewrite -(subst_instance_context_smash _ _ []).
      ** constructor.
        apply eq_term_upto_univ_subst_instance_constr; try typeclasses eauto.
        apply equ.

  - (* Proj congruence: discriminee reduction *) 
    eapply type_Cumul; [econstructor|..]; eauto.
    eapply validity; eauto.
    instantiate (1:= tProj p c).
    econstructor; eauto.
    eapply conv_cumul.
    rewrite (subst_app_simpl [c']) (subst_app_simpl [c]).
    eapply (untyped_subst_conv Γ [vass nAnon (mkApps (tInd p.1.1 u) args)] 
      [vass nAnon (mkApps (tInd p.1.1 u) args)] []); auto.
    repeat constructor. repeat constructor. constructor.
    now apply conv_sym, red_conv, red1_red. constructor.
    simpl. constructor. auto.
    eapply validity in typec; auto.
    destruct typec; auto.
    destruct i as [ctx [s [dA _]]].
    rewrite destArity_tInd in dA. discriminate.

  - (* Fix congruence *)
    symmetry in H0; apply mkApps_Fix_spec in H0. simpl in H0. subst args.
    simpl. destruct narg; discriminate.
  
  - (* Fix congruence: type reduction *)
    assert(fixl :#|fix_context mfix| = #|fix_context mfix1|) by now (rewrite !fix_context_length; apply (OnOne2_length o)).
    assert(convctx : conv_context Σ (Γ ,,, fix_context mfix) (Γ ,,, fix_context mfix1)).
    { clear -wf X o fixl.
      eapply context_relation_app_inv => //.
      apply conv_ctx_refl. clear X.
      apply conv_decls_fix_context => //.
      induction o; constructor.
      destruct p. now apply red_conv, red1_red.
      apply All2_refl. reflexivity.
      reflexivity. apply IHo. rewrite !fix_context_length in fixl |- *; simpl in *. lia. }
    assert(All (fun d => isType Σ Γ (dtype d)) mfix).
    { apply (All_impl X0).
      now intros x [s' [Hs' _]]; exists s'. }
    assert(All (fun d => isType Σ Γ (dtype d)) mfix1).
    { apply (OnOne2_All_All o X0).
      * intros x [s [Hs IH]].
        now exists s.
      * intros x y [red eq] [s [Hs IH]].
        now exists s; apply IH. }
    assert (wf_local Σ (Γ ,,, fix_context mfix1)).
    { apply All_mfix_wf; auto. }
    destruct (OnOne2_nth_error _ _ _ decl _ o heq_nth_error) as [decl' [eqnth disj]].
    eapply type_Cumul.
    econstructor; eauto.
    * eapply (fix_guard_red1 _ _ _ _ 0); eauto.
      constructor; eauto.
    * eapply (OnOne2_All_mix_left X0) in o.
      apply (OnOne2_All_All o X1).
      + intros x [[Hb Hlam] IH].
        split; auto.
        eapply context_conversion'; eauto.
        now rewrite -fixl.
      + move=> [na ty b rarg] [na' ty' b' rarg'] /= [[red eq] [s [Hs IH]]] [[Hb Hlam] IH'].
        noconf eq. split; auto.
        eapply context_conversion'; eauto.
        rewrite -fixl.
        eapply type_Cumul. eapply Hb.
        right. exists s. specialize (IH _ red).
        eapply (weakening _ _ _ _ (tSort _)); auto.
        apply All_mfix_wf; auto. 
        apply (weakening_cumul _ _ []); auto.
        now apply red_cumul, red1_red.

    * eapply wf_fixpoint_red1_type; eauto.
    * eapply All_nth_error in X2; eauto.
    * apply conv_cumul, conv_sym, red_conv. destruct disj as [<-|red].
      constructor. apply red1_red. apply red.

  - (* Fix congruence in body *)
    assert(fixl :#|fix_context mfix| = #|fix_context mfix1|) by now (rewrite !fix_context_length; apply (OnOne2_length o)).
    assert(convctx : fix_context mfix = fix_context mfix1).
    { clear -wf o.
      change fix_context with (fix_context_gen 0).
      generalize 0. induction o.
      destruct p as [_ eq]. noconf eq. simpl in H; noconf H.
      simpl. intros. now rewrite H H0.
      simpl. intros n; f_equal. apply IHo. }
    assert(All (fun d => isType Σ Γ (dtype d)) mfix).
    { apply (All_impl X0).
      now intros x [s' [Hs' _]]; exists s'. }
    assert(All (fun d => isType Σ Γ (dtype d)) mfix1).
    { apply (OnOne2_All_All o X0).
      * intros x [s [Hs IH]].
        now exists s.
      * intros x y [red eq] [s [Hs IH]].
        noconf eq. simpl in H0; noconf H0. rewrite -H2.
        now exists s; apply Hs. }
    assert (wf_local Σ (Γ ,,, fix_context mfix1)).
    { apply All_mfix_wf; auto. }
    destruct (OnOne2_nth_error _ _ _ decl _ o heq_nth_error) as [decl' [eqnth disj]].
    eapply type_Cumul.
    econstructor; eauto.
    * eapply (fix_guard_red1 _ _ _ _ 0); eauto.
      apply fix_red_body; eauto.
    * eapply (OnOne2_All_mix_left X0) in o.
       apply (OnOne2_All_All o X1).
      + intros x [[Hb Hlam] IH].
        split; auto.
        eapply context_conversion'; eauto.
        now rewrite -fixl.
        rewrite convctx. apply conv_ctx_refl.
      + move=> [na ty b rarg] [na' ty' b' rarg'] /= [[red eq] [s [Hs IH]]] [[Hb Hlam] IH'].
        noconf eq.
        rewrite -convctx. split; auto.
        now eapply isLambda_red1.
    * eapply wf_fixpoint_red1_body; eauto.
    * eapply All_nth_error in X2; eauto.
    * apply conv_cumul, conv_sym, red_conv. destruct disj as [<-|[_ eq]].
      constructor. noconf eq. simpl in H0; noconf H0. rewrite H2; constructor.

  - (* CoFix congruence type *)
    assert(fixl :#|fix_context mfix| = #|fix_context mfix1|) by now (rewrite !fix_context_length; apply (OnOne2_length o)).
    assert(convctx : conv_context Σ (Γ ,,, fix_context mfix) (Γ ,,, fix_context mfix1)).
    { clear -wf X o fixl.
      eapply context_relation_app_inv => //.
      apply conv_ctx_refl. clear X.
      apply conv_decls_fix_context => //.
      induction o; constructor.
      destruct p. now apply red_conv, red1_red.
      apply All2_refl. reflexivity.
      reflexivity. apply IHo. rewrite !fix_context_length /= in fixl |- *; lia. }
    assert(All (fun d => isType Σ Γ (dtype d)) mfix).
    { apply (All_impl X0).
      now intros x [s' [Hs' _]]; exists s'. }
    assert(All (fun d => isType Σ Γ (dtype d)) mfix1).
    { apply (OnOne2_All_All o X0).
      * intros x [s [Hs IH]].
        now exists s.
      * intros x y [red eq] [s [Hs IH]].
        now exists s; apply IH. }
    assert (wf_local Σ (Γ ,,, fix_context mfix1)).
    { apply All_mfix_wf; auto. }
    destruct (OnOne2_nth_error _ _ _ decl _ o heq_nth_error) as [decl' [eqnth disj]].
    eapply type_Cumul.
    econstructor; eauto.
    * eapply (cofix_guard_red1 _ _ _ _ 0); eauto.
      constructor; eauto.
    * eapply (OnOne2_All_mix_left X0) in o.
      apply (OnOne2_All_All o X1).
      + intros x [Hb IH].
        eapply context_conversion'; eauto.
        now rewrite -fixl.
      + move=> [na ty b rarg] [na' ty' b' rarg'] /= [[red eq] [s [Hs IH]]] [Hb IH'].
        noconf eq. 
        eapply context_conversion'; eauto.
        rewrite -fixl.
        eapply type_Cumul. eapply Hb.
        right. exists s. specialize (IH _ red).
        eapply (weakening _ _ _ _ (tSort _)); auto.
        apply All_mfix_wf; auto. 
        apply (weakening_cumul _ _ []); auto.
        now apply red_cumul, red1_red.
    * eapply wf_cofixpoint_red1_type; eauto.
    * eapply All_nth_error in X2; eauto.
    * apply conv_cumul, conv_sym, red_conv. destruct disj as [<-|red].
      constructor. apply red1_red. apply red.

  - (* CoFix congruence in body *)
    assert(fixl :#|fix_context mfix| = #|fix_context mfix1|) by now (rewrite !fix_context_length; apply (OnOne2_length o)).
    assert(convctx : fix_context mfix = fix_context mfix1).
    { clear -wf o.
      change fix_context with (fix_context_gen 0).
      generalize 0. induction o.
      destruct p as [_ eq]. noconf eq. simpl in H; noconf H.
      simpl. intros. now rewrite H H0.
      simpl. intros n; f_equal. apply IHo. }
    assert(All (fun d => isType Σ Γ (dtype d)) mfix).
    { apply (All_impl X0).
      now intros x [s' [Hs' _]]; exists s'. }
    assert(All (fun d => isType Σ Γ (dtype d)) mfix1).
    { apply (OnOne2_All_All o X0).
      * intros x [s [Hs IH]].
        now exists s.
      * intros x y [red eq] [s [Hs IH]].
        noconf eq. simpl in H0; noconf H0. rewrite -H2.
        now exists s; apply Hs. }
    assert (wf_local Σ (Γ ,,, fix_context mfix1)).
    { apply All_mfix_wf; auto. }
    destruct (OnOne2_nth_error _ _ _ decl _ o heq_nth_error) as [decl' [eqnth disj]].
    eapply type_Cumul.
    econstructor; eauto.
    * eapply (cofix_guard_red1 _ _ _ _ 0); eauto.
      apply cofix_red_body; eauto.
    * eapply (OnOne2_All_mix_left X0) in o.
      apply (OnOne2_All_All o X1).
      + intros x [Hb IH].
        now rewrite -convctx.
      + move=> [na ty b rarg] [na' ty' b' rarg'] /= [[red eq] [s [Hs IH]]] [Hb IH'].
        noconf eq.
        now rewrite -convctx. 
    * now eapply wf_cofixpoint_red1_body.
    * eapply All_nth_error in X2; eauto.
    * apply conv_cumul, conv_sym, red_conv. destruct disj as [<-|[_ eq]].
      constructor. noconf eq. simpl in H0; noconf H0. rewrite H2; constructor.
 
  - (* Conversion *)
    specialize (forall_u _ Hu).
    eapply type_Cumul; eauto.
    destruct X2 as [[wf' _]|[s Hs]].
    now left.
    now right.
Qed.

Print Assumptions sr_red1.

Definition sr_stmt {cf:checker_flags} (Σ : global_env_ext) Γ t T :=
  forall u, red Σ Γ t u -> Σ ;;; Γ |- u : T.

Theorem subject_reduction {cf:checker_flags} : 
  forall (Σ : global_env_ext) Γ t u T, wf Σ -> Σ ;;; Γ |- t : T -> red Σ Γ t u -> Σ ;;; Γ |- u : T.
Proof.
  intros * wfΣ Hty Hred.
  induction Hred. auto.
  eapply sr_red1 in IHHred; eauto with wf.
Qed.

Lemma subject_reduction1 {cf:checker_flags} {Σ Γ t u T}
  : wf Σ.1 -> Σ ;;; Γ |- t : T -> red1 Σ.1 Γ t u -> Σ ;;; Γ |- u : T.
Proof.
  intros. eapply subject_reduction; try eassumption.
  now apply red1_red.
Defined.

Section SRContext.
  Context {cf:checker_flags}.

  (* todo: rename wf_local_app *)
  Definition wf_local_app' {Σ Γ1 Γ2} :
    wf_local Σ Γ1 -> wf_local_rel Σ Γ1 Γ2
    -> wf_local Σ (Γ1 ,,, Γ2).
  Proof.
    intros H1 H2. apply wf_local_local_rel.
    apply wf_local_rel_local in H1.
    apply wf_local_rel_app_inv; tas.
    now rewrite app_context_nil_l.
  Qed.

  Definition cumul_red_l' `{checker_flags} :
    forall Σ Γ t u,
      wf Σ.1 ->
      red (fst Σ) Γ t u ->
      Σ ;;; Γ |- t <= u.
  Proof.
    intros Σ Γ t u hΣ h.
    induction h.
    - eapply cumul_refl'.
    - eapply PCUICConversion.cumul_trans ; try eassumption.
      eapply cumul_red_l.
      + eassumption.
      + eapply cumul_refl'.
  Defined.

  Hint Constructors OnOne2_local_env : aa.
  Hint Unfold red1_ctx : aa.


  Lemma red1_ctx_app Σ Γ Γ' Δ :
    red1_ctx Σ Γ Γ' ->
    red1_ctx Σ (Γ ,,, Δ) (Γ' ,,, Δ).
  Proof.
    induction Δ. trivial.
    intro H. simpl. constructor. now apply IHΔ.
  Qed.

  Lemma red1_red_ctx Σ Γ Γ' :
    red1_ctx Σ Γ Γ' ->
    red_ctx Σ Γ Γ'.
  Proof.
    induction 1; cbn in *.
    - constructor. reflexivity. cbn; eauto using red1_red.
    - constructor. reflexivity.
      destruct p as [[? []]|[? []]]; cbn; eauto using red1_red.
    - destruct d as [na [bo|] ty]; constructor; eauto.
      split; eapply refl_red.
      apply refl_red.
  Qed.

  Lemma nth_error_red1_ctx Σ Γ Γ' n decl :
    wf Σ ->
    nth_error Γ n = Some decl ->
    red1_ctx Σ Γ Γ' ->
    ∑ decl', nth_error Γ' n = Some decl'
              × red Σ Γ' (lift0 (S n) (decl_type decl))
              (lift0 (S n) (decl_type decl')).
  Proof.
    intros wfΣ h1 h2; induction h2 in n, h1 |- *.
    - destruct n.
      + inversion h1; subst. exists (vass na t').
        split; cbnr.
        eapply (weakening_red_0 wfΣ _ [_]); tas; cbnr.
        apply red1_red; tas.
      + exists decl. split; tas. apply refl_red.
    - destruct n.
      + inversion h1; subst.
        destruct p as [[? []]|[? []]].
        -- exists (vdef na b' t).
           split; cbnr.
        -- exists (vdef na b t').
           split; cbnr.
           eapply (weakening_red_0 wfΣ _ [_]); tas; cbnr.
           apply red1_red; tas.
      + exists decl. split; tas. apply refl_red.
    - destruct n.
      + exists d. split; cbnr. inv h1; apply refl_red.
      + cbn in h1. specialize (IHh2 _ h1).
        destruct IHh2 as [decl' [X1 X2]].
        exists decl'. split; tas.
        rewrite !(simpl_lift0 _ (S n)).
        eapply (weakening_red_0 wfΣ _ [_]); tas; cbnr.
  Qed.


  Lemma wf_local_isType_nth Σ Γ n decl :
    wf Σ.1 ->
    wf_local Σ Γ ->
    nth_error Γ n = Some decl ->
    ∑ s, Σ ;;; Γ |- lift0 (S n) (decl_type decl) : tSort s.
  Proof.
    induction n in Γ, decl |- *; intros hΣ hΓ e; destruct Γ;
      cbn; inversion e; inversion hΓ; subst.
    all: try (destruct X0 as [s Ht]; exists s;
              eapply (weakening _ _ [_] _ (tSort s)); tas).
    - eapply IHn in H0; tas. destruct H0 as [s Ht]. exists s.
      rewrite simpl_lift0.
      eapply (weakening _ _ [_] _ (tSort s)); tas; cbnr.
    - eapply IHn in H0; tas. destruct H0 as [s Ht]. exists s.
      rewrite simpl_lift0.
      eapply (weakening _ _ [_] _ (tSort s)); tas; cbnr.
  Qed.

  Ltac invs H := inversion H; subst.
  Ltac invc H := inversion H; subst; clear H.

  Lemma subject_reduction_ctx Σ Γ Γ' t T :
    wf Σ.1 ->
    red1_ctx Σ.1 Γ Γ' ->
    Σ ;;; Γ |- t : T -> Σ ;;; Γ' |- t : T.
  Proof.
    assert(OnOne2_local_env
      (on_one_decl
         (fun (Δ : PCUICAst.context) (t t' : term) => red1 Σ.1 Δ t t')) Γ Γ' ->
         conv_context Σ Γ Γ').
    { clear. induction 1.
      - red in p. constructor; auto.
        apply conv_ctx_refl. constructor. now apply red_conv, red1_red.
      - destruct p. constructor.
        apply conv_ctx_refl. destruct p as [red ->].
        constructor; auto; now apply red_conv, red1_red.
        constructor.
        apply conv_ctx_refl. destruct p as [red ->].
        constructor; auto; now apply red_conv, red1_red.
      - destruct d as [na [b|] ?]; constructor; auto; constructor; auto. }
    intros wfΣ r H.
    specialize (X r).
    assert(wf_local Σ Γ').
    apply typing_wf_local in H.
    induction H in Γ', r, X |-  *; depelim r; simpl in H; noconf H.
    - constructor; auto. red in o.
      destruct t2 as [s Hs]. exists s.
      eapply subject_reduction1 in Hs; eauto.
    - depelim X; simpl in H; noconf H; simpl in H0; noconf H0.
      constructor; auto. 
      destruct t1 as [s Hs]. exists s.
      eapply context_conversion; eauto.
    - depelim X; simpl in H; noconf H; simpl in H0; noconf H0.
      red in o. destruct t2 as [s Hs].
      simpl in t3.
      destruct o as [[r ->]|[r <-]].

      constructor; auto. exists s; auto.
      eapply subject_reduction1; eauto.
      constructor; auto. exists s; eapply subject_reduction1; eauto.
      eapply type_Cumul; eauto. right. exists s.
      eapply subject_reduction1; eauto.
      now apply red_cumul, red1_red.
    - depelim X; simpl in H; noconf H; simpl in H0; noconf H0.
      destruct t2 as [s Hs].
      simpl in t3.

      constructor; auto. exists s; auto.
      eapply context_conversion; eauto.
      red; eapply context_conversion; eauto.

    - eapply context_conversion; eauto.
  Qed.
  
  Lemma wf_local_red1 {Σ Γ Γ'} :
    wf Σ.1 ->
    red1_ctx Σ.1 Γ Γ' -> wf_local Σ Γ -> wf_local Σ Γ'.
  Proof.
    intro hΣ. induction 1; cbn in *.
    - intro e. inversion e; subst; cbn in *.
      constructor; tas. destruct X0 as [s Ht]. exists s.
      eapply subject_reduction1; tea.
    - intro e. inversion e; subst; cbn in *.
      destruct p as [[? []]|[? []]]; constructor; cbn; tas.
      + eapply subject_reduction1; tea.
      + destruct X0; eexists; eapply subject_reduction1; tea.
      + econstructor; tea.
        right; destruct X0; eexists; eapply subject_reduction1; tea.
        econstructor 2. eassumption. reflexivity.
    - intro H; inversion H; subst; constructor; cbn in *; auto.
      + destruct X1 as [s Ht]. exists s.
        eapply subject_reduction_ctx; tea.
      + destruct X1 as [s Ht]. exists s.
        eapply subject_reduction_ctx; tea.
      + eapply subject_reduction_ctx; tea.
  Qed.

  Lemma eq_context_upto_names_upto_names Γ Δ :
    eq_context_upto_names Γ Δ -> Γ ≡Γ Δ.
  Proof.
    induction 1; cbnr; try constructor; eauto.
    destruct x as [? [] ?], y as [? [] ?]; cbn in *; subst; inversion e.
    all: constructor; cbnr; eauto.
  Qed.


  Lemma wf_local_red {Σ Γ Γ'} :
    wf Σ.1 ->
    red_ctx Σ.1 Γ Γ' -> wf_local Σ Γ -> wf_local Σ Γ'.
  Proof.
    intros hΣ h. apply red_ctx_clos_rt_red1_ctx in h.
    induction h; eauto using wf_local_red1.
    apply eq_context_upto_names_upto_names in e.
    eauto using wf_local_alpha.
  Qed.


  Lemma wf_local_subst1 Σ (wfΣ : wf Σ.1) Γ na b t Γ' :
      wf_local Σ (Γ ,,, [],, vdef na b t ,,, Γ') ->
      wf_local Σ (Γ ,,, subst_context [b] 0 Γ').
  Proof.
    induction Γ' as [|d Γ']; [now inversion 1|].
    change (d :: Γ') with (Γ' ,, d).
    destruct d as [na' [bd|] ty]; rewrite !app_context_cons; intro HH.
    - rewrite subst_context_snoc0. simpl.
      inversion HH; subst; cbn in *. destruct X0 as [s X0].
      change (Γ,, vdef na b t ,,, Γ') with (Γ ,,, [vdef na b t] ,,, Γ') in *.
      assert (subslet Σ Γ [b] [vdef na b t]). {
        pose proof (cons_let_def Σ Γ [] [] na b t) as XX.
        rewrite !subst_empty in XX. apply XX. constructor.
        apply wf_local_app in X. inversion X; subst; cbn in *; assumption.
      }
      constructor; cbn; auto.
      1: exists s. 1: unfold PCUICTerm.tSort.
      1: change (tSort s) with (subst [b] #|Γ'| (tSort s)).
      all: eapply substitution; tea.
    - rewrite subst_context_snoc0. simpl.
      inversion HH; subst; cbn in *. destruct X0 as [s X0].
      change (Γ,, vdef na b t ,,, Γ') with (Γ ,,, [vdef na b t] ,,, Γ') in *.
      assert (subslet Σ Γ [b] [vdef na b t]). {
        pose proof (cons_let_def Σ Γ [] [] na b t) as XX.
        rewrite !subst_empty in XX. apply XX. constructor.
        apply wf_local_app in X. inversion X; subst; cbn in *; assumption. }
      constructor; cbn; auto. exists s.
      unfold PCUICTerm.tSort.
      change (tSort s) with (subst [b] #|Γ'| (tSort s)).
      all: eapply substitution; tea.
  Qed.


  Lemma red_ctx_app_context_l {Σ Γ Γ' Δ}
    : red_ctx Σ Γ Γ' -> red_ctx Σ (Γ ,,, Δ) (Γ' ,,, Δ).
  Proof.
    induction Δ as [|[na [bd|] ty] Δ]; [trivial| |];
      intro H; simpl; constructor; cbn; eauto; now apply IHΔ.
  Qed.


   Lemma isWfArity_red1 {Σ Γ A B} :
     wf Σ.1 ->
       red1 (fst Σ) Γ A B ->
       isWfArity typing Σ Γ A ->
       isWfArity typing Σ Γ B.
   Proof.
     intro wfΣ. induction 1 using red1_ind_all.
     all: intros [ctx [s [H1 H2]]]; cbn in *; try discriminate.
     - rewrite destArity_app in H1.
       case_eq (destArity [] b'); [intros [ctx' s']|]; intro ee;
         [|rewrite ee in H1; discriminate].
       pose proof (subst_destArity [] b' [b] 0) as H; cbn in H.
       rewrite ee in H. eexists _, s'. split. eassumption.
       rewrite ee in H1. cbn in *. inversion H1; subst.
       rewrite app_context_assoc in H2.
       now eapply wf_local_subst1.
     - rewrite destArity_tFix in H1; discriminate.
     - rewrite destArity_app in H1.
       case_eq (destArity [] b'); [intros [ctx' s']|]; intro ee;
         rewrite ee in H1; [|discriminate].
       eexists _, s'; split. cbn. rewrite destArity_app ee. reflexivity.
       cbn in H1. inversion H1; subst.
       eapply wf_local_red; try exact H2; tas.
       rewrite !app_context_assoc. apply red_ctx_app_context_l.
       constructor; cbn. reflexivity. split; auto.
     - rewrite destArity_app in H1.
       case_eq (destArity [] b'); [intros [ctx' s']|]; intro ee;
         rewrite ee in H1; [|discriminate].
       eexists _, s'; split. cbn. rewrite destArity_app ee. reflexivity.
       cbn in H1. inversion H1; subst.
       eapply wf_local_red; try exact H2; tas.
       rewrite !app_context_assoc. apply red_ctx_app_context_l.
       constructor; cbn. reflexivity. split; auto.
     - rewrite destArity_app in H1.
       case_eq (destArity [] b'); [intros [ctx' s']|]; intro ee;
         rewrite ee in H1; [|discriminate].
       forward IHX. {
         eexists _, s'; split; tea. cbn in H1.
         inversion H1; subst. now rewrite app_context_assoc in H2. }
       destruct IHX as [ctx'' [s'' [ee' ?]]].
       eexists _, s''; split. cbn. rewrite destArity_app ee'. reflexivity.
       now rewrite app_context_assoc.
     - rewrite destArity_app in H1.
       case_eq (destArity [] M2); [intros [ctx' s']|]; intro ee;
         rewrite ee in H1; [|discriminate].
       eexists _, s'; split. cbn. rewrite destArity_app ee. reflexivity.
       cbn in H1. inversion H1; subst.
       eapply wf_local_red; try exact H2; tas.
       rewrite !app_context_assoc. apply red_ctx_app_context_l.
       constructor; cbn. reflexivity. auto.
     - rewrite destArity_app in H1.
       case_eq (destArity [] M2); [intros [ctx' s']|]; intro ee;
         rewrite ee in H1; [|discriminate].
       forward IHX. {
         eexists _, s'; split; tea. cbn in H1.
         inversion H1; subst. now rewrite app_context_assoc in H2. }
       destruct IHX as [ctx'' [s'' [ee' ?]]].
       eexists _, s''; split. cbn. rewrite destArity_app ee'. reflexivity.
       now rewrite app_context_assoc.
   Qed.

   Lemma isWfArity_red {Σ Γ A B} :
     wf Σ.1 ->
     red (fst Σ) Γ A B ->
     isWfArity typing Σ Γ A ->
     isWfArity typing Σ Γ B.
   Proof.
     induction 2.
     - easy.
     - intro. now eapply isWfArity_red1.
   Qed.

   Lemma isWfArity_or_Type_red {Σ Γ A B} :
     wf Σ.1 ->
     red (fst Σ) Γ A B ->
     isWfArity_or_Type Σ Γ A ->
     isWfArity_or_Type Σ Γ B.
   Proof.
     intros ? ? [?|[? ?]]; [left|right].
     eapply isWfArity_red; eassumption.
     eexists. eapply subject_reduction; tea.
   Qed.

  Lemma type_reduction {Σ Γ t A B}
    : wf Σ.1 ->  Σ ;;; Γ |- t : A -> red (fst Σ) Γ A B -> Σ ;;; Γ |- t : B.
  Proof.
    intros HΣ' Ht Hr.
    econstructor. eassumption.
    2: now eapply cumul_red_l'.
    destruct (validity_term HΣ' Ht).
    - left. eapply isWfArity_red; try eassumption.
    - destruct i as [s HA]. right.
      exists s. eapply subject_reduction; eassumption.
  Defined.

End SRContext.

Lemma isWAT_tLetIn {cf:checker_flags} {Σ : global_env_ext} (HΣ' : wf Σ)
      {Γ} (HΓ : wf_local Σ Γ) {na t A B}
  : isWfArity_or_Type Σ Γ (tLetIn na t A B)
    <~> (isType Σ Γ A × (Σ ;;; Γ |- t : A)
                      × isWfArity_or_Type Σ (Γ,, vdef na t A) B).
Proof.
  split; intro HH.
  - destruct HH as [[ctx [s [H1 H2]]]|[s H]].
    + cbn in H1. apply destArity_app_Some in H1.
      destruct H1 as [ctx' [H1 HH]]; subst ctx.
      rewrite app_context_assoc in H2. repeat split.
      * apply wf_local_app in H2. inversion H2; subst. assumption.
      * apply wf_local_app in H2. inversion H2; subst. assumption.
      * left. exists ctx', s. split; tas.
    + apply inversion_LetIn in H; tas. destruct H as [s1 [A' [HA [Ht [HB H]]]]].
      repeat split; tas. 1: eexists; eassumption.
      apply cumul_Sort_r_inv in H.
      destruct H as [s' [H H']].
      right. exists s'. eapply type_reduction; tea.
      apply invert_red_letin in H; tas.
      destruct H as [[? [? [? [? [[[H ?] ?] ?]]]]]|H].
      * discriminate.
      * etransitivity.
        2: apply weakening_red_0 with (Γ' := [_]) (N := tSort _);
          tea; reflexivity.
        exact (red_rel_all _ (Γ ,, vdef na t A) 0 t A' eq_refl).
  - destruct HH as [HA [Ht [[ctx [s [H1 H2]]]|HB]]].
    + left. exists ([vdef na t A] ,,, ctx), s. split.
      cbn. now rewrite destArity_app H1.
      now rewrite app_context_assoc.
    + right. destruct HB as [sB HB].
      eexists. eapply type_reduction; tas.
      * econstructor; tea.
        apply HA.π2.
      * apply red1_red.
        apply red_zeta with (b':=tSort sB).
Defined.
