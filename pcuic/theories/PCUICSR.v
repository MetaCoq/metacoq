(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICUtils
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICWeakeningEnv PCUICWeakening
     PCUICSubstitution PCUICClosed PCUICCumulativity PCUICGeneration PCUICReduction
     PCUICAlpha PCUICEquality PCUICValidity PCUICParallelReductionConfluence
     PCUICConfluence PCUICContextConversion PCUICUnivSubstitution
     PCUICConversion PCUICInversion PCUICContexts PCUICArities
     PCUICParallelReduction PCUICSpine PCUICInductives PCUICInductiveInversion
     PCUICCtxShape.

Require Import ssreflect.
From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.
Local Set SimplIsCbn.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

Derive Signature for OnOne2_local_env.

Ltac rename_hyp h ht ::= my_rename_hyp h ht.
Ltac pcuic := intuition eauto 3 with pcuic ||
  (try solve [repeat red; cbn in *; intuition auto; eauto 3 with pcuic || (try lia || congruence)]).

Arguments Nat.sub : simpl nomatch.
Arguments Universe.sort_of_product : simpl nomatch.
Hint Rewrite subst_instance_context_assumptions : len.
Hint Rewrite projs_length : len.

(** The subject reduction property of the system: *)

Definition SR_red1 {cf} Σ Γ t T :=
  forall u (Hu : red1 Σ Γ t u), Σ ;;; Γ |- u : T.

(* Preservation of wf_*fixpoint *)  

Lemma wf_fixpoint_red1_type {cf Σ} {wfΣ : wf Σ} Γ mfix mfix1 : 
  wf_fixpoint Σ mfix ->
  OnOne2
  (fun x y : def term =>
   red1 Σ Γ (dtype x) (dtype y)
   × (dname x, dbody x, rarg x) = (dname y, dbody y, rarg y)) mfix mfix1 ->
  wf_fixpoint Σ mfix1.
Proof.
  intros wffix o.
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

Lemma wf_fixpoint_red1_body {cf Σ} {wfΣ : wf Σ} Γ mfix mfix1 : 
  wf_fixpoint Σ mfix ->
  OnOne2
  (fun x y : def term =>
   red1 Σ Γ (dbody x) (dbody y)
   × (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)) mfix mfix1 ->
  wf_fixpoint Σ mfix1.
Proof.
  intros wffix o.
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

Hint Extern 0 (conv_decls _ _ _ _ _) => constructor : pcuic.
Hint Extern 0 (cumul_decls _ _ _ _ _) => constructor : pcuic.
Hint Extern 0 (conv_context _ _ _) => constructor : pcuic.
Hint Extern 0 (cumul_context _ _ _) => constructor : pcuic.

Hint Extern 4 (∑ s : Universe.t, typing _ _ ?T (tSort s)) => 
  match goal with 
  | [ H : isType _ _ T |- _ ] => exact H
  end : pcuic.

Ltac unfold_pcuic := 
  progress (unfold lift_typing, PCUICTypingDef.conv, PCUICTypingDef.cumul, PCUICTypingDef.typing,
  PCUICTypingDef.wf_universe, PCUICTypingDef.closedn in * ).
Hint Extern 10 => unfold_pcuic : pcuic.

Hint Resolve red_conv red1_red red_cumul : pcuic.
Hint Transparent global_env_ext : pcuic.
Hint Constructors All_local_env context_relation : pcuic.
Ltac pcuics := try typeclasses eauto with pcuic.

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
      try solve [econstructor; eauto];
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
    unshelve eapply (context_conversion _ typeb); pcuics.

  - (* Lambda *)
    eapply type_Cumul'. eapply type_Lambda; eauto.
    unshelve eapply (context_conversion _ typeb); pcuics.
    assert (Σ ;;; Γ |- tLambda n t b : tProd n t bty). econstructor; pcuics.
    now eapply validity_term in X0.
    eapply cumul_red_r.
    apply cumul_refl'. constructor. apply Hu.

  - (* LetIn body *)
    eapply type_Cumul'.
    apply (substitution_let _ Γ n b b_ty b' b'_ty wf typeb').
    specialize (typing_wf_local typeb') as wfd.
    assert (Σ ;;; Γ |- tLetIn n b b_ty b' : tLetIn n b b_ty b'_ty). econstructor; eauto.
    edestruct (validity _ wf _ _ _ X0). apply i.
    eapply cumul_red_r.
    apply cumul_refl'. constructor.

  - (* LetIn value *)
    eapply type_Cumul'.
    econstructor; eauto.
    unshelve eapply (context_conversion _ typeb'); pcuics.
    assert (Σ ;;; Γ |- tLetIn n b b_ty b' : tLetIn n b b_ty b'_ty). econstructor; eauto.
    edestruct (validity _ wf _ _ _ X0). apply i.
    eapply cumul_red_r.
    apply cumul_refl'. now constructor.

  - (* LetIn type annotation *)
    specialize (forall_u _ Hu).
    eapply type_Cumul'.
    econstructor; eauto.
    eapply type_Cumul'. eauto. exists s1; auto.
    apply red_cumul; eauto.
    unshelve eapply (context_conversion _ typeb'); pcuics.
    constructor; pcuic.
    eapply type_Cumul'. eauto. all:pcuic.
    assert (Σ ;;; Γ |- tLetIn n b b_ty b' : tLetIn n b b_ty b'_ty). econstructor; eauto.
    edestruct (validity _ wf _ _ _ X0). apply i.
    eapply cumul_red_r.
    apply cumul_refl'. now constructor.

  - (* Application *)
    eapply substitution0; eauto.
    pose proof typet as typet'.
    eapply inversion_Lambda in typet' as [s1 [B' [Ht [Hb HU]]]]=>//.
    apply cumul_Prod_inv in HU as [[eqann eqA] leqB] => //.
    destruct (validity _ wf _ _ _ typet).
    eapply isType_tProd in i as [Hdom Hcodom]; auto.
    eapply type_Cumul'; eauto.
    unshelve eapply (context_conversion _ Hb); pcuics.

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
    eapply type_App; eauto.
    eapply type_mkApps. eapply type_Cumul'; eauto. eapply spty.
    
  - (* Congruence *)
    eapply type_Cumul'; [eapply type_App| |]; eauto with wf.
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
    eapply @typing_subst_instance_decl with (Γ:=[]); tea.

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
    unshelve eapply (branch_type_spec Σ.1) in brtys; eauto. 2:eapply on_declared_inductive; eauto.
    destruct (nth_nth_error' (@eq_refl _ (nth c0 brs (0, tDummy)))) => //.
    2:{ simpl in Hbr. rewrite Hbr in a. intuition discriminate. }
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
    unshelve epose proof (constructor_cumulative_indices wf isdecl oib onc _ Hu cu equ _ _ _ _ _ cparsubst0 iparsubst0 Hpars).
    { eapply (weaken_lookup_on_global_env' _ _ _ wf (proj1 decli)). }
    set (argctxu1 := subst_context _ _ _) in X |- *.
    set (argctxu := subst_context _ _ _) in X |- *.
    simpl in X.
    set (pargctxu1 := subst_context cparsubst 0 argctxu1) in X |- *.
    set (pargctxu := subst_context parsubst 0 argctxu) in X |- *.
    destruct X as [cumargs convidx]; eauto.
    assert(wfparu : wf_local Σ (subst_instance_context u (ind_params mdecl))). 
    { eapply on_minductive_wf_params; eauto. }
    assert (wfps : wf_universe Σ ps).
    { eapply validity in typep; auto. eapply PCUICWfUniverses.isType_wf_universes in typep.
      rewrite PCUICWfUniverses.wf_universes_it_mkProd_or_LetIn in typep.
      move/andb_and: typep => /= [_ /andb_and[_ typep]]. 
      now apply (ssrbool.elimT PCUICWfUniverses.wf_universe_reflect) in typep. auto. }
    eapply wf_arity_spine_typing_spine => //.
    split.
    { (* Predicate instantiation is well typed *) 
      exists (sort_of_products s ps).
      eapply type_it_mkProd_or_LetIn_sorts; eauto.
      assert (wf_local Σ (Γ ,,, pargctxu)).
      { eapply sorts_local_ctx_wf_local in typectx; eauto. }
      assert (#|argctx| = #|pargctxu|).
      { now rewrite /argctx /pargctxu /argctxu /argctx; autorewrite with len. }
      eapply type_mkApps.
      eapply weakening_gen; eauto.
      eapply wf_arity_spine_typing_spine => //.
      split.
      ** eapply validity in typep. eapply isType_lift. len. lia.
         all:auto.  rewrite skipn_all_app_eq //.
      ** rewrite lift_it_mkProd_or_LetIn.
         pose proof onc as onc'.
         eapply on_constructor_inst_pars_indices in onc'; eauto.
         2:{ simpl. eapply on_declared_inductive; eauto. }
         destruct onc' as [wfparsargs [inst sp]].
         eapply arity_spine_it_mkProd_or_LetIn => //.
         simpl in sp. rewrite !map_map_compose in sp. eapply sp.
         autorewrite with len.
         simpl. constructor.
         2:{ simpl; constructor; auto. }
         rewrite lift_mkApps subst_mkApps.
         simpl. eapply type_mkApps. econstructor; eauto.
         split; eauto.
         eapply wf_arity_spine_typing_spine; eauto.
         split; eauto. eapply declared_constructor_valid_ty; eauto.
         split; eauto.
         unfold type_of_constructor.
         rewrite [cdecl'.1.2](onc.(cstr_eq)).
         rewrite subst_instance_constr_it_mkProd_or_LetIn subst_it_mkProd_or_LetIn.
         eapply arity_spine_it_mkProd_or_LetIn; eauto.
         simpl. eapply spine_subst_weakening in iparsubst0. 3:eapply X. all:eauto.
         rewrite closed_ctx_lift in iparsubst0.
         now eapply closed_wf_local.
         rewrite -H in iparsubst0.
         rewrite closed_ctx_subst. now eapply closed_wf_local. eapply iparsubst0. 
         rewrite subst_instance_constr_it_mkProd_or_LetIn !subst_it_mkProd_or_LetIn.
         autorewrite with len.
         rewrite -(app_nil_r (to_extended_list pargctxu)).
         pose proof (spine_subst_to_extended_list_k _ _ _ wf X).
         rewrite {6}/pargctxu in X0.
         rewrite distr_lift_subst_context in X0.
         rewrite closed_ctx_lift in X0.
         { rewrite /argctxu. rewrite -(context_subst_length csubst).
           rewrite subst_instance_context_length. rewrite Nat.add_comm. eapply closedn_ctx_subst.
          2:eapply declared_minductive_closed_inds; eauto.
          rewrite /argctx. autorewrite with len. simpl.
          pose proof (on_declared_inductive wf isdecl) as [onind _].
          pose proof (on_constructor_inst u wf isdecl onind oib onc cu) as [wfcl _]; auto.
          eapply closed_wf_local in wfcl; auto.
          rewrite !subst_instance_context_app in wfcl.
          rewrite closedn_ctx_app in wfcl.
          move/andb_and: wfcl => []. autorewrite with len. now auto. }
         eapply arity_spine_it_mkProd_or_LetIn; eauto.
         { unfold to_extended_list, to_extended_list_k. rewrite /argctxu in X0. simpl. rewrite -H in X0. 
           eapply X0. }
         epose proof (to_extended_list_map_lift _ 0 _) as Hl; rewrite Nat.add_0_r in Hl.
         rewrite map_app.
         rewrite <- Hl. clear Hl.
         rewrite !map_app.
         rewrite (map_map_compose _ _ _ _ (lift #|argctx| _)).
         epose proof (simpl_lift_ext #|ind_indices oib| 0 #|argctx| #|ind_indices oib|).
         do 2 forward H0 by lia.
         rewrite (map_ext _ _ _ H0). clear H0.
         rewrite (Nat.add_comm (#|argctx|)).
         rewrite -(map_ext _ _ _ (simpl_lift_ext _ 0 _ 0 _ _)); try lia.
         rewrite -(map_map_compose _ _ _ _ (lift0 #|ind_indices oib|)).
         rewrite map_map_compose. rewrite map_subst_lift_id_eq.
         rewrite (subslet_length sp). now autorewrite with len.
         rewrite /to_extended_list -(PCUICSubstitution.map_subst_instance_constr_to_extended_list_k u (ind_indices oib)).
         rewrite -(to_extended_list_k_subst parsubst 0 (subst_instance_context _ _)_).
         rewrite -(to_extended_list_k_lift_context (subst_context _ _ _) 0 #|cshape_args cs|).
         erewrite subst_to_extended_list_k.
         2:{ eapply make_context_subst_spec_inv. rewrite List.rev_involutive. eapply sp. }
         rewrite map_lift0.
         rewrite subst_instance_constr_mkApps !subst_mkApps.
         rewrite /cstr_concl_head.
         rewrite subst_inds_concl_head. simpl.
         { simpl. destruct decli. now eapply nth_error_Some_length in H2. }
         simpl.
         constructor. exists (subst_instance_univ u (ind_sort oib)).
         { red. eapply type_mkApps. econstructor; eauto.
           eapply wf_arity_spine_typing_spine; eauto.
           constructor. epose proof (oib.(onArity)).
           rewrite (oib.(ind_arity_eq)) !subst_instance_constr_it_mkProd_or_LetIn.
           pose proof (on_declared_inductive wf decli) as [ondi oni].
           generalize (on_inductive_inst _ _ _ u _ _ wf X (proj1 decli) ondi oib cu).
           now rewrite subst_instance_context_app it_mkProd_or_LetIn_app.
           rewrite (oib.(ind_arity_eq)) !subst_instance_constr_it_mkProd_or_LetIn.
           eapply arity_spine_it_mkProd_or_LetIn; eauto.
           { eapply spine_subst_weakening in iparsubst0.
             rewrite closed_ctx_lift in iparsubst0.
             eapply closed_wf_local; eauto.
             rewrite H; eapply iparsubst0. all:eauto. }
           rewrite subst_it_mkProd_or_LetIn.
           eapply arity_spine_it_mkProd_or_LetIn_Sort => //.
           simpl in sp.
           pose proof (on_declared_inductive wf decli) as [ondi oni].
           eapply (on_inductive_sort_inst); eauto.
           instantiate (1:=inst).
           eapply spine_subst_eq; [eapply sp|].
           rewrite distr_lift_subst_context -H. f_equal.
           rewrite -(context_subst_length iparsubst0).
           autorewrite with len. rewrite closed_ctx_lift //.
           epose proof (on_minductive_wf_params_indices_inst _ _ u _ _ _ (proj1 decli) oib cu).
           rewrite subst_instance_context_app in X1. eapply closed_wf_local in X1; eauto.
           rewrite closedn_ctx_app in X1. autorewrite with len in X1.
           now move/andb_and: X1 => [].
         }
         simpl. 
         eapply conv_cumul; apply mkApps_conv_args; auto.
         rewrite !map_app. eapply All2_app.
         ****
           eapply (All2_impl (P:=fun x y => x = y)).
           2:{ intros ? ? ->. reflexivity. }
           eapply All2_eq_eq.
           rewrite subst_instance_to_extended_list_k.
           rewrite -to_extended_list_k_map_subst; [autorewrite with len; lia|].
           rewrite -[subst_instance_context _ _](closed_ctx_lift #|argctx| 0) => //.
           eapply closed_wf_local; eauto.
           erewrite subst_to_extended_list_k.
           2:{ eapply make_context_subst_spec_inv. rewrite List.rev_involutive.
               eapply spine_subst_weakening in iparsubst0; eauto.
               rewrite H; eapply iparsubst0; eauto. }
           rewrite map_map_compose.
           rewrite map_subst_lift_id_eq. now autorewrite with len.
           now rewrite H.
         ****
           rewrite -H in X0.
           rewrite map_map_compose.
           eapply All2_map.
           assert (All (fun x => closedn (#|parsubst| + #|argctx|) x) (map
           (subst (inds (inductive_mind ind) u (PCUICAst.ind_bodies mdecl))
              (#|cshape_args cs| + #|ind_params mdecl|)
            ∘ subst_instance_constr u) (cshape_indices cs))).
           { pose proof (positive_cstr_closed_indices wf onc).
             eapply All_map.
             eapply All_map_inv in X1.
             eapply (All_impl X1) => x cl.
             eapply (closedn_expand_lets 0) in cl.
             rewrite subst_closedn closedn_subst_instance_constr.
             now len in cl.
             rewrite -(context_subst_length iparsubst0).
             autorewrite with len. now rewrite Nat.add_comm; len in cl. }  
           rewrite !map_map_compose. apply (All_All2 X1).
           intros x cl.
           pose proof (all_rels_subst Σ pargctxu Γ (subst parsubst #|argctx| x) wf X) as X2.
           eapply red_conv in X2.
           assert(subst (map (lift0 #|argctx|) parsubst) #|cshape_args cs| x =
             (lift #|argctx| #|argctx| (subst parsubst #|argctx| x))) as ->.
           { epose proof (distr_lift_subst_rec _ _ #|argctx| #|argctx| 0) as l.
             rewrite Nat.add_0_r in l. rewrite -> l. f_equal.
             rewrite lift_closed. eapply closed_upwards; eauto. lia. reflexivity. }
           symmetry. now rewrite -H in X2. }

    rewrite -(app_nil_r (skipn _ _)).
    have argsubst := spine_subst_smash wf idxsubst0.
    eapply (spine_subst_cumul _ _ _ _ (smash_context [] pargctxu)) in argsubst; first last.
    4-5:apply smash_context_assumption_context; constructor. all:auto.
    { eapply on_constructor_inst in onc; eauto.
      2:{ simpl. eapply on_declared_inductive; eauto. }
      destruct onc as [wfc [inst spc]].
      rewrite !subst_instance_context_app in wfc.
      rewrite -(app_context_nil_l (_ ,,, _)) in wfc.
      rewrite -app_context_assoc in wfc.
      rewrite app_context_assoc in wfc.
      eapply (substitution_wf_local _ []) in wfc; eauto.
      2:eapply subslet_inds; eauto.
      simpl in wfc. rewrite subst_context_app in wfc.
      autorewrite with len in wfc.
      rewrite closed_ctx_subst in wfc.
      eapply closed_wf_local; eauto.
      eapply (weaken_wf_local Γ) in wfc; eauto.
      rewrite app_context_nil_l !app_context_assoc in wfc.
      eapply substitution_wf_local in wfc; eauto.
      2:eapply iparsubst0.
      eapply wf_local_smash_end; eauto. }
    apply argsubst.
    eapply arity_spine_it_mkProd_or_LetIn_smash => //.
    apply argsubst.
    rewrite lift_mkApps !subst_mkApps.
    constructor.
    { exists ps. red.
      eapply type_mkApps; eauto.
      eapply wf_arity_spine_typing_spine; eauto.
      split. eapply validity; eauto.
      eapply arity_spine_it_mkProd_or_LetIn; eauto.
      simpl. constructor. 
      2:{ constructor; pcuic. }
      rewrite subst_mkApps /= map_app. unfold to_extended_list.
      generalize (spine_subst_subst_to_extended_list_k subsidx).
      rewrite to_extended_list_k_subst 
        PCUICSubstitution.map_subst_instance_constr_to_extended_list_k => ->.
      move: (subslet_length subsidx). autorewrite with len => <-.
      now rewrite map_map_compose map_subst_lift_id firstn_skipn. }
    eapply conv_cumul. eapply mkApps_conv_args; auto.
    { rewrite /pargctxu /argctxu. autorewrite with len.
      rewrite simpl_lift; try lia. rewrite subst_subst_lift //; try reflexivity.
      autorewrite with len. rewrite skipn_length. lia.
      unfold argctx. lia. } 
    { rewrite !map_app. eapply All2_app.
      * eapply All2_transitivity. intros x y z; eapply conv_trans; eauto.
        2:eauto.
        (* 1: cshape indices are closed w.r.t. inds.
           2: parsubst and cparsubst are convertible
        *) 
        pose proof (positive_cstr_closed_indices wf onc).
        rewrite -(map_map_compose _ _ _ (subst (inds _ _ _) _ ∘ (subst_instance_constr u)) (subst parsubst #|argctx|)).
        rewrite -(map_map_compose _ _ _ (subst_instance_constr u)).
        rewrite (map_subst_closedn (inds _ _ _)).
        { apply All_forallb. apply All_map.
          eapply All_map_inv in X; eapply (All_impl X). 
          intros x Px.
          eapply (closedn_expand_lets 0) in Px.
          len in Px.
          rewrite closedn_subst_instance_constr.
          now rewrite /argctx; autorewrite with len. }
        rewrite -(map_map_compose _ _ _ (subst (inds _ _ _) _ ∘ (subst_instance_constr u1)) (subst _ _)).
        rewrite -(map_map_compose _ _ _ (subst_instance_constr u1)).
        rewrite (map_subst_closedn (inds _ _ _)).
        { apply All_forallb. apply All_map.
          eapply All_map_inv in X; eapply (All_impl X). 
          intros x Px.
          eapply (closedn_expand_lets 0) in Px.
          len in Px.
          rewrite closedn_subst_instance_constr.
          now rewrite /argctx; autorewrite with len. }
        rewrite (map_map_compose _ _ _ _ (subst0 (extended_subst pargctxu 0))).
        change (fun x =>  subst0 (extended_subst pargctxu 0) _ ) with (expand_lets pargctxu).
        rewrite -map_subst_app_simpl -(map_map_compose _ _ _ _ (subst0 cargsubst)) /=.
        rewrite (subslet_length idxsubst0); autorewrite with len.
        eapply All2_symmetry. intros x y. now symmetry.
        pose proof (spine_subst_extended_subst idxsubst0).
        unfold ind_subst in argctxu1; fold argctxu1 pargctxu1 in H. rewrite H.
        eapply spine_subst_smash in idxsubst0; eauto.
        epose proof (conv_terms_subst _ Γ (smash_context [] pargctxu1) (smash_context [] pargctxu) [] _ _ _ _ wf) as cv.
        simpl in cv. forward cv.
        eapply idxsubst0; eauto.
        specialize (cv idxsubst0 argsubst).
        forward cv. eapply All2_rev; auto. eapply All2_refl. reflexivity.
        specialize (cv convidx). clear convidx. rewrite subst_context_nil /= in cv.
        rewrite /pargctxu /argctx. assert (#|cshape_args cs| = #|argctxu|) as lenargctxu.
        { rewrite /argctxu; autorewrite with len. reflexivity. }
        rewrite lenargctxu.
        assert(context_assumptions (cshape_args cs) = context_assumptions argctxu1).
        { rewrite /argctxu1; autorewrite with len. reflexivity. }
        rewrite {1}H0 in cv.
        rewrite -(map_expand_lets_subst_comm _ _ _) in cv.
        rewrite (map_expand_lets_subst_comm _ _ _).
        assert(#|argctxu| = #|argctxu1|).
        { rewrite /argctxu /argctxu1; autorewrite with len. reflexivity. }
        assert(context_assumptions argctxu = context_assumptions (cshape_args cs)) as ->.
        { rewrite /argctxu /argctxu1; autorewrite with len. reflexivity. }
        rewrite -H2 in cv.
        rewrite /pargctxu1.
        epose proof (map_subst_expand_lets (List.rev (skipn (ind_npars mdecl) cargs)) 
          (subst_context cparsubst 0 argctxu1)).
        change (All2 (fun x y : term => Σ;;; Γ |- x = y) ?t ?u) with (conv_terms Σ Γ t u).
        eapply conv_terms_Proper.
        rewrite H3.
        2:{ autorewrite with len. rewrite -H0 (context_subst_length2 idxsubst0).
          autorewrite with len. rewrite context_assumptions_smash_context.
          autorewrite with len. now simpl. }
        rewrite -map_map_compose {1}/argctxu. reflexivity. reflexivity.
        autorewrite with len. clear H3.
        now rewrite {1}/argctx lenargctxu.

      * simpl. rewrite lift_mkApps !subst_mkApps /=.
        constructor. 2:constructor.
        assert (R_global_instance Σ.1 (eq_universe (global_ext_constraints Σ)) (eq_universe (global_ext_constraints Σ)) 
          (ConstructRef ind c0) (ind_npars mdecl + (context_assumptions (cshape_args cs))) u1 u).
        { unfold R_ind_universes in equ. clear -equ onc eqargs isdecl declc.
          rewrite /R_ind_universes /R_global_instance.
          assert (global_variance Σ.1 (ConstructRef ind c0)
            (ind_npars mdecl + context_assumptions (cshape_args cs)) = Some []).
          { unfold global_variance, lookup_constructor, lookup_inductive, lookup_minductive.
            change (fst_ctx Σ) with Σ.1.
            destruct isdecl as [lookmind looki].
            red in lookmind. rewrite lookmind looki declc.
            rewrite (cstr_args_length onc).
            elim: leb_spec_Set; auto. unfold cdecl_args. lia. }
          rewrite H. apply R_universe_instance_variance_irrelevant.
          now apply R_global_instance_length in equ. }
        transitivity (mkApps (tConstruct ind c0 u) cargs); first last.
        symmetry. constructor. eapply eq_term_upto_univ_mkApps.
        constructor. rewrite eqargs. apply H.
        eapply All2_refl. intros; reflexivity.
        eapply mkApps_conv_args; eauto.
        rewrite 3!map_app. rewrite 3!map_map_compose.
        rewrite /pargctxu /argctxu; autorewrite with len.
        rewrite map_subst_subst_lift_lift. autorewrite with len.
        rewrite skipn_length eqargs; try lia. subst argctx. lia.
        set (ctx := subst_context parsubst 0 _).
        pose proof (map_subst_extended_subst_lift_to_extended_list_k ctx).
        unfold ctx in H0. autorewrite with len in H0.
        rewrite {}H0 /to_extended_list.
        erewrite spine_subst_subst_to_extended_list_k.
        2:eapply argsubst. 
        rewrite -{2}(firstn_skipn (ind_npars mdecl) cargs).
        eapply All2_app; auto. apply All2_symmetry => //.
        intros x y conv; now symmetry.
        eapply All2_refl. intros; reflexivity. }

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
    apply Reflect.eqb_eq in t. rewrite t /= in heq_isCoFinite.
    discriminate.

  - (* Case congruence on the predicate *) 
    eapply (type_Cumul _ _ _ (mkApps p' (skipn npar args ++ [c]))).
    eapply build_branches_type_red in heq_map_option_out as [brtys' [eqbrtys alleq]]; eauto.
    eapply type_Case; eauto.
    * eapply All2_trans'; eauto. simpl.
      intros. destruct X1 as ((((? & ?) & ?) & [s [Hs IH]]) & ? & ?).
      specialize (IH _ r).
      intuition auto. now transitivity y.1.
      eapply type_Cumul'; eauto. now exists s.
      now eapply conv_cumul, red_conv, red1_red.
      now exists s.
    * pose proof typec as typec'.
      eapply (env_prop_typing _ _ validity) in typec' as wat; auto.
      unshelve eapply isType_mkApps_Ind in wat as [parsubst [argsubst wat]]; eauto.
      set (oib := on_declared_inductive wf isdecl) in *. clearbody oib.
      destruct oib as [onind oib].
      destruct wat  as [[spars sargs] cu].
      unshelve eapply (build_case_predicate_type_spec (Σ.1, _)) in heq_build_case_predicate_type as [parsubst' [cparsubst Hpty]]; eauto.
      rewrite {}Hpty in typep.
      subst npar.
      assert (wfps : wf_universe Σ ps).
      { eapply validity in typep; auto. eapply PCUICWfUniverses.isType_wf_universes in typep.
        rewrite PCUICWfUniverses.wf_universes_it_mkProd_or_LetIn in typep.
        move/andb_and: typep => /= [_ /andb_and[_ typep]]. 
        now apply (ssrbool.elimT PCUICWfUniverses.wf_universe_reflect) in typep. auto. }
      pose proof (context_subst_fun cparsubst spars). subst parsubst'. clear cparsubst.
      eapply type_mkApps. eauto.
      eapply wf_arity_spine_typing_spine; eauto.
      split. apply (env_prop_typing _ _ validity) in typep as ?; eauto.
      eapply arity_spine_it_mkProd_or_LetIn; eauto.
      simpl. constructor; [ |constructor].
      rewrite subst_mkApps. simpl.
      rewrite map_app. rewrite map_map_compose.
      rewrite map_subst_lift_id_eq. now rewrite (subslet_length sargs); autorewrite with len.
      move: (spine_subst_subst_to_extended_list_k sargs).
      rewrite to_extended_list_k_subst PCUICSubstitution.map_subst_instance_constr_to_extended_list_k.
      move->. now rewrite firstn_skipn.
    * now eapply conv_cumul, conv_sym, red_conv, red_mkApps_f, red1_red.

  - (* Case congruence on discriminee *) 
    eapply type_Cumul. eapply type_Case; eauto.
    * solve_all. destruct b0 as [s Hs]; exists s; pcuic.
    * pose proof typec as typec'.
      eapply (env_prop_typing _ _ validity) in typec' as wat; auto.
      unshelve eapply isType_mkApps_Ind in wat as [parsubst [argsubst wat]]; eauto.
      set (oib := on_declared_inductive wf isdecl) in *. clearbody oib.
      destruct oib as [onind oib].
      destruct wat as [[spars sargs] cu].
      unshelve eapply (build_case_predicate_type_spec (Σ.1, _)) in heq_build_case_predicate_type as [parsubst' [cparsubst Hpty]]; eauto.
      rewrite {}Hpty in typep.
      assert (wfps : wf_universe Σ ps).
      { eapply validity in typep; auto. eapply PCUICWfUniverses.isType_wf_universes in typep.
        rewrite PCUICWfUniverses.wf_universes_it_mkProd_or_LetIn in typep.
        move/andb_and: typep => /= [_ /andb_and[_ typep]]. 
        now apply (ssrbool.elimT PCUICWfUniverses.wf_universe_reflect) in typep. auto. }
      subst npar.
      pose proof (context_subst_fun cparsubst spars). subst parsubst'. clear cparsubst.
      eapply type_mkApps. eauto.
      eapply wf_arity_spine_typing_spine; eauto.
      split. apply (env_prop_typing _ _ validity) in typep; eauto.
      eapply arity_spine_it_mkProd_or_LetIn; eauto.
      simpl. constructor; [ |constructor].
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
    intuition auto. destruct b as [s [Hs IH]]; eauto. subst.
    intros [] [] []; simpl. intros.
    intuition auto. subst.    
    reflexivity.
    destruct b0 as [s [Hs IH]]; eauto.

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
    eapply type_Cumul'; [econstructor|..]; eauto.
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
    { unshelve eapply isType_mkApps_Ind in X1 as [parsubst [argsubst Hind]]; eauto.
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
          pose proof (onNpars oi). simpl; lia. }
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
    set(oib := declared_inductive_inv _ wf wf decli) in *.
    change (declared_inductive_inv weaken_env_prop_typing wf wf decli) with oib in X2.
    pose proof (onProjections oib) as onProjs. clearbody oib.
    forward onProjs. clear pdecl'.
    eapply nth_error_Some_length in H0. simpl in H0.
    intros Hp. apply (f_equal (@length _)) in Hp. rewrite  Hp /=   in H0. lia.
    simpl in H0.
    simpl in *.
    destruct typec' as [[[[_ equ] cu] eqargs] [cparsubst [cargsubst [iparsubst [iidxsubst ci]]]]].
    destruct ci as ((([cparsubst0 iparsubst0] & idxsubst0) & subsidx) & [s [typectx [Hpars Hargs]]]).
    destruct ind_cshapes as [|? []]; try contradiction.
    destruct X2 as [projty projeq].
    noconf Hnth.
    specialize (projsubsl onProjs).
    destruct onProjs.
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
    2:{ rewrite !context_assumptions_fold.
        rewrite subst_instance_context_assumptions. rewrite H.
        apply onNpars in onmind. lia. }
    rewrite closed_ctx_subst in spargs.
    { eapply closed_wf_local; eauto. eapply on_minductive_wf_params; eauto. }
    pose proof (spine_subst_inj_subst spargs cparsubst0). subst arg_sub.
    clear Hty.
    rewrite subst_it_mkProd_or_LetIn in sp, iswat.
    rewrite !subst_instance_constr_mkApps !subst_mkApps in sp, iswat.
    eapply typing_spine_nth_error in sp; eauto.
    clear iswat.
    2:{ rewrite !context_assumptions_fold. rewrite subst_instance_context_assumptions.
        clear iswat sp. eapply nth_error_Some_length in H0. lia. }
    destruct sp as [decl [Hnth Hu0]].
    simpl in on_projs. red in on_projs.
    eapply type_Cumul'; eauto.
    { rewrite firstn_skipn.
      eapply (isType_subst_instance_decl _ _ _ _ _ u wf isdecl.p1.p1) in projty; eauto.
      destruct projty as [s' Hs].
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
      assumption. }
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
    unshelve epose proof (constructor_cumulative_indices wf decli' oib onc _ Hu cu equ _ _ _ _ _ spargs iparsubst0 Hpars).
    { eapply (weaken_lookup_on_global_env' _ _ _ wf (proj1 decli)). }
    move: X2.
    set (argsu1 := subst_instance_context u1 (cshape_args cs)) in *.
    set (argsu := subst_instance_context u (cshape_args cs)) in *.
    set (argctxu1 := subst_context _ _ argsu1) in *.
    set (argctxu := subst_context _ _ argsu) in *.
    simpl.
    set (pargctxu1 := subst_context cparsubst 0 argctxu1) in *.
    set (pargctxu := subst_context iparsubst 0 argctxu) in *.
    move=> [cumargs _]; eauto.
    eapply context_relation_nth_ass in cumargs.
    3:eapply smash_context_assumption_context; constructor.
    2:{ unfold pargctxu1, argctxu1, argsu1.
        autorewrite with len in Hnth. eapply Hnth. }
    destruct cumargs as [decl' [Hdecl' cum]].
    rewrite (smash_context_subst []) in Hnth.
    rewrite (smash_context_subst []) in Hnth.
    rewrite -(subst_instance_context_smash u1 _ []) in Hnth.    
    rewrite !nth_error_subst_context in Hnth.
    rewrite nth_error_map in Hnth.
    destruct projeq as [decl'' [[[Hdecl wfdecl] Hty1] Hty2]].
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
    autorewrite with len in cum. simpl in cum.
    move: Hdecl'.
    rewrite /pargctxu /argctxu /argsu.
    rewrite !smash_context_subst_empty.
    rewrite -(subst_instance_context_smash _ _ []).
    rewrite !nth_error_subst_context.
    rewrite nth_error_map Hdecl. simpl => [= Hdecl'].
    subst decl'. simpl in cum.
    autorewrite with len in cum; simpl in cum. 
    assert(context_assumptions (cshape_args cs) -
      S (context_assumptions (cshape_args cs) - S narg) = narg) by lia.
    rewrite H2 in cum. 
    set (idx := S (context_assumptions (cshape_args cs) - S narg)) in *.
    assert (wfpargctxu1 : wf_local Σ (Γ ,,, skipn idx (smash_context [] pargctxu1))).
    { simpl. apply wf_local_app_skipn. apply wf_local_smash_end; auto.
      apply idxsubst0. }
    destruct cum as [[cr mapd] cdecl].
    destruct decl'' as [na [b|] ty]; simpl in mapd; try discriminate.
    depelim cdecl. rename c into cum.
    eapply (substitution_cumul _ Γ (skipn idx (smash_context [] pargctxu1)) [] 
      (skipn idx (List.rev (skipn (ind_npars mdecl) args0)))) in cum.
    all:auto.
    2:{ eapply subslet_skipn.
        eapply spine_subst_smash in idxsubst0; eauto. eapply idxsubst0. }
    assert (skipn idx (List.rev (skipn (ind_npars mdecl) args0)) = (List.rev (firstn narg (skipn (ind_npars mdecl) args0)))) as eq.
    { rewrite /idx skipn_rev. lia_f_equal. rewrite skipn_length; lia. }
    assert (narg = #|List.rev (firstn narg (skipn (ind_npars mdecl) args0))|).
    { autorewrite with len. rewrite firstn_length_le ?skipn_length; lia. }
    rewrite eq in cum. 
    rewrite subst_context_nil in cum. simpl in cum.
    rewrite -(subst_app_simpl' _ _ 0) in cum => //.
    rewrite subst_app_decomp in cum.
    etransitivity; [eapply cum|clear cum].
    rewrite -(subst_app_simpl' _ _ 0) //.
    rewrite subst_app_decomp.
    rewrite (subslet_length iparsubst0); autorewrite with len.
    assert (wf_local Σ (Γ ,,, subst_instance_context u (ind_params mdecl))).
    { eapply weaken_wf_local; eauto. eapply on_minductive_wf_params => //. pcuic. }
    eapply (substitution_cumul _ _ _ []); eauto. eapply iparsubst0.
    simpl.
    rewrite (distr_subst_rec _ _ _ #|ind_params mdecl| 0).
    autorewrite with len. simpl.
    eapply (untyped_subst_cumul (_ ,,, _) _ _ []); auto.
    { eapply subslet_untyped_subslet. rewrite -(subst_instance_context_length u).
      eapply subslet_lift; eauto. rewrite -eq.
      eapply spine_subst_smash in idxsubst0; eauto. 
      eapply subslet_skipn. eapply idxsubst0. }
    { rewrite subst_projs_inst.
      specialize (projsubsl (Γ ,,, subst_instance_context u (ind_params mdecl))).
      rewrite -projs_inst_lift projs_inst_subst.
      rewrite -{1}H2 -projs_inst_skipn.
      eapply untyped_subslet_skipn. eapply (projsubsl _ u). }
    { rewrite subst_projs_inst.
      rewrite !map_map_compose. eapply All2_map.
      eapply All2_from_nth_error.
      { autorewrite with len. lia. }
      intros n x x' Hn nth nth'.
      rewrite nth_error_projs_inst in nth'.
      lia. noconf nth'.
      simpl. rewrite lift_mkApps subst_mkApps /=.
      rewrite (map_map_compose _ _ _ (lift0 (ind_npars mdecl))).
      rewrite map_lift_lift map_map_compose.
      symmetry. eapply red_conv.
      etransitivity. eapply red1_red; constructor.
      eapply (f_equal (option_map (lift0 #|ind_params mdecl|))) in nth.
      simpl in nth. rewrite <-nth, nth_error_rev_inv; autorewrite with len; try lia.
      rewrite H3 Nat.add_comm.
      setoid_rewrite map_subst_lift_ext; try lia.
      2:autorewrite with len; lia.
      rewrite nth_error_map. f_equal.
      rewrite firstn_skipn_comm nth_error_skipn.
      rewrite -{1}[args0](firstn_skipn (ind_npars mdecl + narg)).
      rewrite nth_error_app1 // firstn_length_le; autorewrite with len; try lia.
      reflexivity. }
    { simpl. autorewrite with len.
      rewrite -(subst_instance_context_length u (ind_params mdecl)).
      eapply weakening_wf_local; auto. }
    simpl.
    unfold indsubst. 
    set (inds' := inds _ _ _).
    change (map (subst_instance_constr u) inds') with (subst_instance u inds').
    rewrite instantiate_inds => //. pcuic.
    rewrite (subst_closedn (List.rev args)); [|reflexivity].
    eapply (closedn_subst _ 0).  
    eapply declared_inductive_closed_inds; eauto.
    simpl. autorewrite with len.
    rewrite closedn_subst_instance_constr.
    clear projsubsl.
    eapply closed_wf_local in wfdecl.
    rewrite closedn_ctx_app in wfdecl.
    move/andb_and: wfdecl => [_ wfdecl].
    autorewrite with len in wfdecl.
    simpl in wfdecl.
    eapply closedn_ctx_decl in wfdecl; eauto.
    autorewrite with len in wfdecl.
    simpl in wfdecl.
    eapply closed_upwards. eauto.
    lia. auto.

  - (* Proj congruence: discriminee reduction *) 
    eapply type_Cumul'; [econstructor|..]; eauto.
    eapply validity; eauto.
    instantiate (1:= tProj p c).
    econstructor; eauto.
    eapply conv_cumul.
    rewrite (subst_app_simpl [c']) (subst_app_simpl [c]).
    set(bann := {| binder_name := nAnon; binder_relevance := idecl.(ind_relevance) |}).
    eapply (untyped_subst_conv Γ [vass bann (mkApps (tInd p.1.1 u) args)] 
      [vass bann (mkApps (tInd p.1.1 u) args)] []); auto.
    repeat constructor. repeat constructor. constructor.
    now apply conv_sym, red_conv, red1_red. constructor.
    simpl. constructor. auto.
    eapply validity in typec; auto.

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
      destruct p. split. now noconf e.
      now noconf e.
      apply All2_refl. intros; split; reflexivity.
      split; reflexivity.
      apply IHo. rewrite !fix_context_length in fixl |- *; simpl in *. lia. }
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
    eapply type_Cumul'.
    econstructor; eauto.
    * eapply (fix_guard_red1 _ _ _ _ 0); eauto.
      constructor; eauto.
    * eapply (OnOne2_All_mix_left X0) in o.
      apply (OnOne2_All_All o X1).
      + intros x [Hb IH].
        eapply context_conversion; eauto.
        now rewrite -fixl.
      + move=> [na ty b rarg] [na' ty' b' rarg'] /= [[red eq] [s [Hs IH]]] [Hb IH'].
        noconf eq.
        eapply context_conversion; eauto.
        rewrite -fixl.
        eapply type_Cumul'. eapply Hb.
        exists s. specialize (IH _ red).
        eapply (weakening _ _ _ _ (tSort _)); auto.
        apply All_mfix_wf; auto. 
        apply (weakening_cumul _ _ []); auto.
        now apply red_cumul, red1_red.

    * eapply wf_fixpoint_red1_type; eauto.
    * eapply All_nth_error in X2; eauto.
    * apply conv_cumul, conv_sym, red_conv. destruct disj as [<-|red].
      reflexivity. apply red1_red. apply red.

  - (* Fix congruence in body *)
    assert(fixl :#|fix_context mfix| = #|fix_context mfix1|) by now (rewrite !fix_context_length; apply (OnOne2_length o)).
    assert(convctx : fix_context mfix = fix_context mfix1).
    { clear -wf o.
      change fix_context with (fix_context_gen 0).
      generalize 0. induction o.
      destruct p as [_ eq]. noconf eq. do 2 (simpl in H; noconf H).
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
        noconf eq. rewrite -H2.
        now exists s; apply Hs. }
    assert (wf_local Σ (Γ ,,, fix_context mfix1)).
    { apply All_mfix_wf; auto. }
    destruct (OnOne2_nth_error _ _ _ decl _ o heq_nth_error) as [decl' [eqnth disj]].
    eapply type_Cumul'.
    econstructor; eauto.
    * eapply (fix_guard_red1 _ _ _ _ 0); eauto.
      apply fix_red_body; eauto.
    * eapply (OnOne2_All_mix_left X0) in o.
       apply (OnOne2_All_All o X1).
      + intros x [Hb IH].
        eapply context_conversion; eauto.
        now rewrite -fixl.
        rewrite convctx. apply conv_ctx_refl.
      + move=> [na ty b rarg] [na' ty' b' rarg'] /= [[red eq] [s [Hs IH]]] [Hb IH'].
        noconf eq.
        now rewrite -convctx.        
    * eapply wf_fixpoint_red1_body; eauto.
    * eapply All_nth_error in X2; eauto.
    * apply conv_cumul, conv_sym, red_conv. destruct disj as [<-|[_ eq]].
      reflexivity. noconf eq. simpl in H0; noconf H0. rewrite H2; reflexivity.

  - (* CoFix congruence type *)
    assert(fixl :#|fix_context mfix| = #|fix_context mfix1|) by now (rewrite !fix_context_length; apply (OnOne2_length o)).
    assert(convctx : conv_context Σ (Γ ,,, fix_context mfix) (Γ ,,, fix_context mfix1)).
    { clear -wf X o fixl.
      eapply context_relation_app_inv => //.
      apply conv_ctx_refl. clear X.
      apply conv_decls_fix_context => //.
      induction o; constructor; try split; auto;
      try (destruct p; now noconf e).
      apply All2_refl; split; reflexivity.
      apply IHo. rewrite !fix_context_length /= in fixl |- *; lia. }
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
    eapply type_Cumul'.
    econstructor; eauto.
    * eapply (cofix_guard_red1 _ _ _ _ 0); eauto.
      constructor; eauto.
    * eapply (OnOne2_All_mix_left X0) in o.
      apply (OnOne2_All_All o X1).
      + intros x [Hb IH].
        eapply context_conversion; eauto.
        now rewrite -fixl.
      + move=> [na ty b rarg] [na' ty' b' rarg'] /= [[red eq] [s [Hs IH]]] [Hb IH'].
        noconf eq. 
        eapply context_conversion; eauto.
        rewrite -fixl.
        eapply type_Cumul'. eapply Hb.
        exists s. specialize (IH _ red).
        eapply (weakening _ _ _ _ (tSort _)); auto.
        apply All_mfix_wf; auto. 
        apply (weakening_cumul _ _ []); auto.
        now apply red_cumul, red1_red.
    * eapply wf_cofixpoint_red1_type; eauto.
    * eapply All_nth_error in X2; eauto.
    * apply conv_cumul, conv_sym, red_conv. destruct disj as [<-|red].
      reflexivity. apply red1_red. apply red.

  - (* CoFix congruence in body *)
    assert(fixl :#|fix_context mfix| = #|fix_context mfix1|) by now (rewrite !fix_context_length; apply (OnOne2_length o)).
    assert(convctx : fix_context mfix = fix_context mfix1).
    { clear -wf o.
      change fix_context with (fix_context_gen 0).
      generalize 0. induction o.
      destruct p as [_ eq]. injection eq.
      simpl. intros. now rewrite H0 H1.
      simpl. intros n; f_equal. apply IHo. }
    assert(All (fun d => isType Σ Γ (dtype d)) mfix).
    { apply (All_impl X0).
      now intros x [s' [Hs' _]]; exists s'. }
    assert(All (fun d => isType Σ Γ (dtype d)) mfix1).
    { apply (OnOne2_All_All o X0).
      * intros x [s [Hs IH]].
        now exists s.
      * intros x y [red eq] [s [Hs IH]].
        noconf eq. rewrite -H2.
        now exists s; apply Hs. }
    assert (wf_local Σ (Γ ,,, fix_context mfix1)).
    { apply All_mfix_wf; auto. }
    destruct (OnOne2_nth_error _ _ _ decl _ o heq_nth_error) as [decl' [eqnth disj]].
    eapply type_Cumul'.
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
      (* constructor. noconf eq. rewrite H2; constructor. *)
      reflexivity. noconf eq. simpl in H0; noconf H0. rewrite H2; reflexivity.

  - (* Conversion *)
    specialize (forall_u _ Hu).
    eapply type_Cumul; eauto.
Qed.

Definition sr_stmt {cf:checker_flags} (Σ : global_env_ext) Γ t T :=
  forall u, red Σ Γ t u -> Σ ;;; Γ |- u : T.

Theorem subject_reduction {cf:checker_flags} : 
  forall (Σ : global_env_ext) Γ t u T, wf Σ -> Σ ;;; Γ |- t : T -> red Σ Γ t u -> Σ ;;; Γ |- u : T.
Proof.
  intros * wfΣ Hty Hred.
  induction Hred; eauto.
  eapply sr_red1 in Hty; eauto with wf.
Qed.

Lemma subject_reduction1 {cf Σ} {wfΣ : wf Σ} {Γ t u T}
  : Σ ;;; Γ |- t : T -> red1 Σ Γ t u -> Σ ;;; Γ |- u : T.
Proof.
  intros. eapply subject_reduction; try eassumption.
  now apply red1_red.
Defined.

Section SRContext.
  Context {cf:checker_flags}.

  Definition cumul_red_l' {Σ} {wfΣ : wf Σ} Γ t u :
      red Σ Γ t u ->
      Σ ;;; Γ |- t <= u.
  Proof.
    intros h.
    induction h using red_rect'.
    - eapply cumul_refl'.
    - eapply PCUICConversion.cumul_trans ; try eassumption.
      eapply cumul_red_l.
      + eassumption.
      + eapply cumul_refl'.
  Defined.

  Hint Constructors OnOne2_local_env : aa.
  Hint Unfold red1_ctx : aa.

  Lemma red1_ctx_app (Σ : global_env) Γ Γ' Δ :
    red1_ctx Σ Γ Γ' ->
    red1_ctx Σ (Γ ,,, Δ) (Γ' ,,, Δ).
  Proof.
    induction Δ. trivial.
    intro H. simpl. constructor. now apply IHΔ.
  Qed.

  Lemma red1_red_ctx (Σ : global_env) Γ Γ' :
    red1_ctx Σ Γ Γ' ->
    red_ctx Σ Γ Γ'.
  Proof.
    induction 1; cbn in *.
    - constructor; try reflexivity. cbn; eauto using red1_red.
    - constructor; try reflexivity.
      destruct p as [[? []]|[? []]]; cbn; eauto using red1_red.
    - destruct d as [na [bo|] ty]; constructor; eauto.
      split; eapply refl_red.
      apply refl_red.
  Qed.

  Lemma nth_error_red1_ctx (Σ : global_env) Γ Γ' n decl :
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

  Lemma wf_local_isType_nth {Σ} {wfΣ : wf Σ} Γ n decl :
    wf_local Σ Γ ->
    nth_error Γ n = Some decl ->
    ∑ s, Σ ;;; Γ |- lift0 (S n) (decl_type decl) : tSort s.
  Proof.
    induction n in Γ, decl |- *; intros hΓ e; destruct Γ;
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

  Lemma subject_reduction_ctx {Σ} {wfΣ : wf Σ} Γ Γ' t T :
    red1_ctx Σ Γ Γ' ->
    Σ ;;; Γ |- t : T -> Σ ;;; Γ' |- t : T.
  Proof.
    assert(OnOne2_local_env
      (on_one_decl
         (fun (Δ : PCUICAst.context) (t t' : term) => red1 Σ.1 Δ t t')) Γ Γ' ->
         conv_context Σ Γ Γ').
    { clear. induction 1.
      - red in p. constructor; auto.
        apply conv_ctx_refl. constructor. reflexivity.
        now apply red_conv, red1_red.
      - destruct p. constructor.
        apply conv_ctx_refl. destruct p as [red ->].
        constructor; pcuics. now apply red_conv, red1_red.
        destruct p as [red ->].
        constructor. pcuic.
        constructor; pcuics. now apply red_conv, red1_red.
      - destruct d as [na [b|] ?]; constructor; auto; constructor; auto. all:pcuic. }
    intros r H.
    specialize (X r).
    assert(wf_local Σ Γ').
    apply typing_wf_local in H.
    induction H in Γ', r, X |-  *; depelim r.
    - constructor; auto. red in o.
      destruct t1 as [s Hs]. exists s.
      eapply subject_reduction1 in Hs; eauto.
    - depelim X.
      constructor; auto. 
      destruct t1 as [s Hs]. exists s.
      eapply context_conversion; eauto.
    - depelim X.
      red in o. destruct t1 as [s Hs].
      simpl in t2.
      destruct o as [[r ->]|[r <-]].

      constructor; auto. exists s; auto.
      eapply subject_reduction1; eauto.
      constructor; auto. exists s; eapply subject_reduction1; eauto.
      eapply type_Cumul'; eauto. exists s.
      eapply subject_reduction1; eauto.
      now apply red_cumul, red1_red.
    - depelim X. destruct t1 as [s Hs].
      simpl in t2.
      constructor; auto. exists s; auto.
      eapply context_conversion; eauto.
      red; eapply context_conversion; eauto.

    - eapply context_conversion; eauto.
  Qed.
  
  Lemma wf_local_red1 {Σ} {wfΣ : wf Σ} {Γ Γ'} :
    red1_ctx Σ Γ Γ' -> wf_local Σ Γ -> wf_local Σ Γ'.
  Proof.
    induction 1; cbn in *.
    - intro e. inversion e; subst; cbn in *.
      constructor; tas. destruct X0 as [s Ht]. exists s.
      eapply subject_reduction1; tea.
    - intro e. inversion e; subst; cbn in *.
      destruct p as [[? []]|[? []]]; constructor; cbn; tas.
      + eapply subject_reduction1; tea.
      + destruct X0; eexists; eapply subject_reduction1; tea.
      + eapply type_Cumul'; tea.
        destruct X0. exists x. eapply subject_reduction1; tea.
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
    destruct x as [? [] ?], y as [? [] ?]; cbn in *; subst; inversion e0; cbn.
    all:constructor; cbnr; eauto.
  Qed.

  Lemma wf_local_red {Σ} {wfΣ : wf Σ} {Γ Γ'} :
    red_ctx Σ Γ Γ' -> wf_local Σ Γ -> wf_local Σ Γ'.
  Proof.
    intros h. apply red_ctx_clos_rt_red1_ctx in h.
    induction h; eauto using wf_local_red1.
    apply eq_context_upto_names_upto_names in e.
    eauto using wf_local_alpha.
  Qed.

  Lemma wf_local_subst1 {Σ} {wfΣ : wf Σ} Γ na b t Γ' :
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
        apply wf_local_app_l in X. inversion X; subst; cbn in *; assumption.
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
        apply wf_local_app_l in X. inversion X; subst; cbn in *; assumption. }
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

  Lemma isType_red1 {Σ : global_env_ext} {wfΣ : wf Σ} {Γ A B} :
     isType Σ Γ A ->
     red1 Σ Γ A B ->
     isType Σ Γ B.
   Proof.
     intros [s Hs] red.
     exists s. eapply subject_reduction1; eauto.
   Qed.

   Lemma isWfArity_red1 {Σ} {wfΣ : wf Σ} {Γ A B} :
     isWfArity Σ Γ A ->
     red1 Σ Γ A B ->
     isWfArity Σ Γ B.
   Proof.
     intros [isty H] re.
     split. eapply isType_red1; eauto.
     clear isty; revert H.
     induction re using red1_ind_all.
     all: intros [ctx [s H1]]; cbn in *; try discriminate.
     - rewrite destArity_app in H1.
       case_eq (destArity [] b'); [intros [ctx' s']|]; intro ee;
         [|rewrite ee in H1; discriminate].
       pose proof (subst_destArity [] b' [b] 0) as H; cbn in H.
       rewrite ee in H. eexists _, s'. eassumption.
     - rewrite destArity_tFix in H1; discriminate.
     - rewrite destArity_app in H1.
       case_eq (destArity [] b'); [intros [ctx' s']|]; intro ee;
         rewrite ee in H1; [|discriminate].
       eexists _, s'. cbn. rewrite destArity_app ee. reflexivity.
     - rewrite destArity_app in H1.
       case_eq (destArity [] b'); [intros [ctx' s']|]; intro ee;
         rewrite ee in H1; [|discriminate].
       eexists _, s'. cbn. rewrite destArity_app ee. reflexivity.
     - rewrite destArity_app in H1.
       case_eq (destArity [] b'); [intros [ctx' s']|]; intro ee;
         rewrite ee in H1; [|discriminate].
       forward IHre. { eexists _, s'; tea. }
       destruct IHre as [ctx'' [s'' ee']].
       eexists _, s''. cbn. rewrite destArity_app ee'. reflexivity.
     - rewrite destArity_app in H1.
       case_eq (destArity [] M2); [intros [ctx' s']|]; intro ee;
         rewrite ee in H1; [|discriminate].
       eexists _, s'. cbn. rewrite destArity_app ee. reflexivity.
     - rewrite destArity_app in H1.
       case_eq (destArity [] M2); [intros [ctx' s']|]; intro ee;
         rewrite ee in H1; [|discriminate].
       forward IHre. { eexists _, s'; tea. }
       destruct IHre as [ctx'' [s'' ee']].
       eexists _, s''. cbn. rewrite destArity_app ee'. reflexivity.
   Qed.

   Lemma isWfArity_red {Σ} {wfΣ : wf Σ} {Γ A B} :
     isWfArity Σ Γ A ->
     red Σ Γ A B ->
     isWfArity Σ Γ B.
   Proof.
     induction 2 using red_rect'.
     - easy.
     - now eapply isWfArity_red1.
   Qed.

   Lemma isType_red {Σ} {wfΣ : wf Σ} {Γ T U} :
    isType Σ Γ T -> red Σ Γ T U -> isType Σ Γ U.
   Proof.
     intros [s Hs] red; exists s.
     eapply subject_reduction; eauto.
   Qed.

  Lemma type_reduction {Σ} {wfΣ : wf Σ} {Γ t A B} : 
    Σ ;;; Γ |- t : A -> red Σ Γ A B -> Σ ;;; Γ |- t : B.
  Proof.
    intros Ht Hr.
    eapply type_Cumul'. eassumption.
    2: now eapply cumul_red_l'.
    destruct (validity_term wfΣ Ht) as [s HA]. 
    exists s; eapply subject_reduction; eassumption.
  Defined.

End SRContext.

Lemma isType_tLetIn {cf} {Σ} {HΣ' : wf Σ} {Γ} {na t A B}
  : isType Σ Γ (tLetIn na t A B)
    <~> (isType Σ Γ A × (Σ ;;; Γ |- t : A) × isType Σ (Γ,, vdef na t A) B).
Proof.
  split; intro HH.
  - destruct HH as [s H].
    apply inversion_LetIn in H; tas. destruct H as [s1 [A' [HA [Ht [HB H]]]]].
    repeat split; tas. 1: eexists; eassumption.
    apply cumul_Sort_r_inv in H.
    destruct H as [s' [H H']].
    exists s'. eapply type_reduction; tea.
    apply invert_red_letin in H; tas.
    destruct H as [[? [? [? [[[H ?] ?] ?]]]]|H].
    * discriminate.
    * etransitivity.
      2: apply weakening_red_0 with (Γ' := [_]) (N := tSort _);
        tea; reflexivity.
      exact (red_rel_all _ (Γ ,, vdef na t A) 0 t A' eq_refl).
  - destruct HH as [HA [Ht HB]].
    destruct HB as [sB HB].
    eexists. eapply type_reduction; tas.
    * econstructor; tea.
      apply HA.π2.
    * apply red1_red.
      apply red_zeta with (b':=tSort sB).
Defined.

(** Keep at the end to not disturb asynchronous proof processing *)
Print Assumptions sr_red1.
