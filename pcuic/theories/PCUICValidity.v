From Coq Require Import String Bool List PeanoNat.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst
     PCUICLiftSubst PCUICTyping PCUICWeakeningEnv PCUICWeakening PCUICInversion
     PCUICSubstitution PCUICReduction PCUICCumulativity PCUICGeneration PCUICUnivSubst
     PCUICParallelReductionConfluence
     PCUICUnivSubstitution PCUICConversion PCUICContexts PCUICArities
     PCUICSpine PCUICInductives.

From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.
Require Import ssreflect.

Derive Signature for typing cumul.

Section Validity.
  Context `{cf : config.checker_flags}.

  Lemma isType_subst_instance_decl Σ Γ T c decl u :
    wf Σ.1 ->
    lookup_env Σ.1 c = Some decl ->
    isType (Σ.1, universes_decl_of_decl decl) Γ T ->
    consistent_instance_ext Σ (universes_decl_of_decl decl) u ->
    isType Σ (subst_instance_context u Γ) (subst_instance_constr u T).
  Proof.
    destruct Σ as [Σ φ]. intros X X0 [s Hs] X1.
    exists (subst_instance_univ u s).
    eapply (typing_subst_instance_decl _ _ _ (tSort _)); eauto.
  Qed.
  
  Lemma isWfArity_subst_instance_decl Σ Γ T c decl u :
    wf Σ.1 ->
    lookup_env Σ.1 c = Some decl ->
    isWfArity typing (Σ.1, universes_decl_of_decl decl) Γ T ->
    consistent_instance_ext Σ (universes_decl_of_decl decl) u ->
    isWfArity typing Σ (subst_instance_context u Γ) (subst_instance_constr u T).
  Proof.
    destruct Σ as [Σ φ]. intros X X0 [ctx [s [eq wf]]] X1.
    exists (subst_instance_context u ctx), (subst_instance_univ u s).
    rewrite (subst_instance_destArity []) eq. intuition auto.
    rewrite -subst_instance_context_app.  
    eapply wf_local_subst_instance_decl; eauto.  
  Qed.
  
  Lemma isWAT_subst_instance_decl Σ Γ T c decl u :
    wf Σ.1 ->
    lookup_env Σ.1 c = Some decl ->
    isWfArity_or_Type (Σ.1, universes_decl_of_decl decl) Γ T ->
    consistent_instance_ext Σ (universes_decl_of_decl decl) u ->
    isWfArity_or_Type Σ (subst_instance_context u Γ) (subst_instance_constr u T).
  Proof.
    destruct Σ as [Σ φ]. intros X X0 X1 X2.
    destruct X1.
    - left. now eapply isWfArity_subst_instance_decl.
    - right. now eapply isType_subst_instance_decl.
  Qed.

  Lemma isWfArity_or_Type_lift (Σ : global_env_ext) n Γ ty (isdecl : n <= #|Γ|):
    wf Σ -> wf_local Σ Γ ->
    isWfArity_or_Type Σ (skipn n Γ) ty ->
    isWfArity_or_Type Σ Γ (lift0 n ty).
  Proof.
    intros wfΣ wfΓ wfty. rewrite <- (firstn_skipn n Γ) in wfΓ |- *.
    assert (n = #|firstn n Γ|).
    { rewrite firstn_length_le; auto with arith. }
    destruct wfty.
    - red. left. destruct i as [ctx [u [da Hd]]].
      exists (lift_context n 0 ctx), u. split.
      1: now rewrite (lift_destArity [] ty n 0) da.
      eapply All_local_env_app_inv.
      eapply All_local_env_app in Hd. intuition eauto.
      rewrite {3}H.
      clear -wfΣ wfΓ isdecl a b.
      induction b; rewrite ?lift_context_snoc; econstructor; simpl; auto.
      + destruct t0 as [u Hu]. exists u. rewrite Nat.add_0_r.
        unshelve eapply (weakening_typing Σ (skipn n Γ) Γ0 (firstn n Γ) t _ _ (tSort u)); eauto with wf.
      + destruct t0 as [u Hu]. exists u. rewrite Nat.add_0_r.
        unshelve eapply (weakening_typing Σ (skipn n Γ) Γ0 (firstn n Γ) t _ _ (tSort u)); eauto with wf.
      + rewrite Nat.add_0_r.
        unshelve eapply (weakening_typing Σ (skipn n Γ) Γ0 (firstn n Γ) b _ _ t); eauto with wf.
    - right. destruct i as [u Hu]. exists u.
      rewrite {3}H.
      unshelve eapply (weakening_typing Σ (skipn n Γ) [] (firstn n Γ) ty _ _ (tSort u)); eauto with wf.
  Qed.

  Lemma destArity_it_mkProd_or_LetIn ctx ctx' t :
    destArity ctx (it_mkProd_or_LetIn ctx' t) =
    destArity (ctx ,,, ctx') t.
  Proof.
    induction ctx' in ctx, t |- *; simpl; auto.
    rewrite IHctx'. destruct a as [na [b|] ty]; reflexivity.
  Qed.
  
  Hint Extern 30 (wf_local ?Σ ?Γ) =>
  match goal with
  | [ H : typing Σ Γ _ _ |- _ ] => apply (typing_wf_local H)
  end : pcuic.

  Ltac pcuic := try solve [ intuition typeclasses eauto with pcuic ].

  Definition weaken_env_prop_full
             (P : global_env_ext -> context -> term -> term -> Type) :=
    forall (Σ : global_env_ext) (Σ' : global_env), wf Σ' -> extends Σ.1 Σ' ->
                                                   forall Γ t T, P Σ Γ t T -> P (Σ', Σ.2) Γ t T.

  Lemma isWfArity_or_Type_weaken_full : weaken_env_prop_full (fun Σ Γ t T => isWfArity_or_Type Σ Γ T).
  Proof.
    red. intros.
    destruct X1. left. destruct i as [ctx [s [Heq Hs]]].
    exists ctx, s. split; auto with pcuic.
    right. destruct i as [u Hu]; exists u; pcuic.
    unshelve eapply (weaken_env_prop_typing _ _ _ _ X0 _ _ (Some (tSort u))); eauto with pcuic.
    red. simpl. destruct Σ. eapply Hu.
  Qed.
  Hint Resolve isWfArity_or_Type_weaken_full : pcuic.

  Lemma isWfArity_or_Type_weaken :
    weaken_env_prop
      (lift_typing (fun Σ Γ (_ T : term) => isWfArity_or_Type Σ Γ T)).
  Proof.
    red. intros.
    unfold lift_typing in *. destruct T. now eapply (isWfArity_or_Type_weaken_full (_, _)).
    destruct X1 as [s Hs]; exists s. now eapply (isWfArity_or_Type_weaken_full (_, _)).
  Qed.
  Hint Resolve isWfArity_or_Type_weaken : pcuic.

  Lemma typing_spine_app Σ Γ ty args na A B arg :
    wf Σ.1 ->
    typing_spine Σ Γ ty args (tProd na A  B) ->
    Σ ;;; Γ |- arg : A ->
    typing_spine Σ Γ ty (args ++ [arg]) (B {0 := arg}).
  Proof.
    intros wfΣ H; revert arg.
    dependent induction H.
    - intros arg  Harg. simpl. econstructor; eauto.
      constructor. 2:reflexivity.
      eapply isWAT_tProd in i as [watd wat].
      eapply (isWAT_subst wfΣ (Δ:=[vass na A])); eauto.
      constructor; auto. now apply typing_wf_local in Harg.
      constructor. constructor. now rewrite subst_empty. auto.
      now apply typing_wf_local in Harg.
    - intros arg Harg.
      econstructor; eauto.
  Qed.

  Lemma invert_type_mkApps_ind Σ Γ ind u args T mdecl idecl :
    wf Σ.1 ->
    declared_inductive Σ.1 mdecl ind idecl ->
    Σ ;;; Γ |- mkApps (tInd ind u) args : T ->
    (typing_spine Σ Γ (subst_instance_constr u (ind_type idecl)) args T)
    * consistent_instance_ext Σ (ind_universes mdecl) u.
  Proof.
    intros wfΣ decli.
    intros H; dependent induction H; solve_discr.
    - destruct args using rev_case; solve_discr. noconf H1.
      rewrite -PCUICAstUtils.mkApps_nested in H1. simpl in H1.
      noconf H1.  clear IHtyping2.
      specialize (IHtyping1 _ _ _ _ _ _ _ wfΣ decli eq_refl) as [IH cu];
        split; auto.
      destruct (on_declared_inductive wfΣ decli) as [onmind oib].
      eapply typing_spine_app; eauto.
    - noconf H0. subst.
      destruct (PCUICInductives.declared_inductive_unique isdecl decli) as [-> ->].
      clear decli. split; auto.
      constructor; [|reflexivity].
      destruct (on_declared_inductive wfΣ isdecl) as [onmind oib].
      pose proof (oib.(onArity)) as ar.
      eapply isWAT_weaken; eauto.
      eapply (isWAT_subst_instance_decl _ []); eauto.
      destruct isdecl; eauto.
      now right. simpl; auto.  
    - specialize (IHtyping _ _ wfΣ decli) as [IH cu]; split; auto.
      eapply typing_spine_weaken_concl; eauto.
  Qed.

  Lemma isWAT_mkApps_Ind {Σ Γ ind u args} (wfΣ : wf Σ.1)
    {mdecl idecl} (declm : declared_inductive Σ.1 mdecl ind idecl) :
    wf_local Σ Γ ->
    isWfArity_or_Type Σ Γ (mkApps (tInd ind u) args) ->
    ∑ parsubst argsubst,
      let oib := (on_declared_inductive wfΣ declm).2 in
      let parctx := (subst_instance_context u (ind_params mdecl)) in
      let argctx := (subst_context parsubst 0 (subst_instance_context u (oib.(ind_indices)))) in
      spine_subst Σ Γ (firstn (ind_npars mdecl) args) parsubst parctx *
      spine_subst Σ Γ (skipn (ind_npars mdecl) args) argsubst argctx *
      consistent_instance_ext Σ (ind_universes mdecl) u.
  Proof.
    move=> wfΓ isWAT.
    destruct isWAT.
    destruct i as [ctx [s Hs]].
    destruct Hs. rewrite destArity_tInd in e => //.
    destruct i as [s Hs].
    eapply invert_type_mkApps_ind in Hs as [tyargs cu]; eauto.
    set (decli' := on_declared_inductive _ _). clearbody decli'.
    rename declm into decli.
    destruct decli' as [declm decli'].
    pose proof (decli'.(onArity)) as ar. 
    rewrite decli'.(ind_arity_eq) in tyargs, ar.
    hnf in ar. destruct ar as [s' ar].
    rewrite !subst_instance_constr_it_mkProd_or_LetIn in tyargs.
    simpl in tyargs. rewrite -it_mkProd_or_LetIn_app in tyargs.
    eapply arity_typing_spine in tyargs as [[argslen leqs] [instsubst [wfdom wfcodom cs subs]]] => //.
    apply context_subst_app in cs as [parsubst argsubst].
    eexists _, _. move=> lk parctx argctx. subst lk.
    rewrite subst_instance_context_assumptions in argsubst, parsubst.
    rewrite declm.(onNpars _ _ _ _) in argsubst, parsubst.
    eapply subslet_app_inv in subs as [subp suba].
    rewrite subst_instance_context_length in subp, suba.
    subst parctx argctx.
    repeat split; eauto; rewrite ?subst_instance_context_length => //.
    rewrite app_context_assoc in wfcodom. now apply All_local_env_app in wfcodom as [? ?].
    simpl.
    eapply substitution_wf_local; eauto. now rewrite app_context_assoc in wfcodom.
    unshelve eapply on_inductive_inst in declm; pcuic.
    rewrite subst_instance_context_app in declm.
    now eapply isWAT_it_mkProd_or_LetIn_wf_local in declm.
  Qed.

  Lemma isWfArity_or_Type_extends : forall (cf : checker_flags) (Σ : global_env)
      (Σ' : PCUICEnvironment.global_env) (φ : universes_decl),
    wf Σ' ->
    extends Σ Σ' ->
    forall Γ : context,
    forall t0 : term,
    isWfArity_or_Type (Σ, φ) Γ t0 -> isWfArity_or_Type (Σ', φ) Γ t0.
  Proof.
    intros.
    destruct X1 as [[ctx [s [eq wf]]]|[s Hs]].
    - left; exists ctx, s; intuition auto.
      apply (PCUICWeakeningEnv.weaken_wf_local (Σ, φ)); auto.
    - right. exists s.
      eapply (env_prop_typing _ _ PCUICWeakeningEnv.weakening_env (Σ, φ)); auto.
      simpl. now eapply wf_extends.
  Qed.

  Lemma weaken_env_prop_isWAT :
    weaken_env_prop
    (lift_typing
         (fun (Σ0 : PCUICEnvironment.global_env_ext)
          (Γ0 : PCUICEnvironment.context) (_ T : term) =>
        isWfArity_or_Type Σ0 Γ0 T)).
  Proof.
    red. intros.
    red in X1 |- *.
    destruct T. now eapply isWfArity_or_Type_extends.
    destruct X1 as [s Hs]; exists s; now eapply isWfArity_or_Type_extends.
  Qed.

  Theorem validity :
    env_prop (fun Σ Γ t T => isWfArity_or_Type Σ Γ T)
      (fun Σ Γ wfΓ =>
      All_local_env_over typing
      (fun (Σ : global_env_ext) (Γ : context) (_ : wf_local Σ Γ) 
         (t T : term) (_ : Σ;;; Γ |- t : T) => isWfArity_or_Type Σ Γ T) Σ Γ
      wfΓ).
  Proof.
    apply typing_ind_env; intros; rename_all_hyps.

    - auto. 

    - destruct (nth_error_All_local_env_over heq_nth_error X) as [HΓ' Hd].
      destruct decl as [na [b|] ty]; cbn -[skipn] in *.
      + destruct Hd as [Hd _].
        eapply isWfArity_or_Type_lift; eauto. clear HΓ'. 
        now apply nth_error_Some_length in heq_nth_error.
      + destruct lookup_wf_local_decl; cbn -[skipn] in *.
        destruct o. right. exists x0. simpl in Hd.
        rewrite <- (firstn_skipn (S n) Γ).
        assert (S n = #|firstn (S n) Γ|).
        { apply nth_error_Some_length in heq_nth_error. rewrite firstn_length_le; auto with arith. }
        rewrite {3}H.
        apply (weakening Σ (skipn (S n) Γ) (firstn (S n) Γ) ty (tSort x0)); eauto with wf.
        unfold app_context. now rewrite (firstn_skipn (S n) Γ).

    - (* Universe *) left. exists [], (Universe.super l). split; auto.
    - (* Product *) left. eexists [], _. split; eauto. simpl. reflexivity.
    - (* Lambda *)
      destruct X3.
      + left. destruct i as [ctx [s [Heq Hs]]].
        red. simpl. pose proof (PCUICClosed.destArity_spec [] bty).
        rewrite Heq in H. simpl in H. subst bty. clear Heq.
        eexists _, s. split; auto.
        * rewrite destArity_it_mkProd_or_LetIn. simpl. reflexivity.
        * apply All_local_env_app_inv; split; auto.
          apply All_local_env_app_inv; split; auto.
          -- repeat constructor.
             simpl.
             exists s1; easy.
          -- apply All_local_env_app in Hs. unfold snoc.
             intuition auto. clear -b0.
             induction b0; constructor; eauto.
             ++ destruct t1 as [u Hu]. exists u.
                rewrite app_context_assoc. apply Hu.
             ++ simpl in t1 |- *.
                rewrite app_context_assoc. apply t1.
             ++ simpl in t2.
                rewrite app_context_assoc. apply t2.
      + destruct i as [u Hu].
        right. exists (Universe.sort_of_product s1 u); constructor; auto.

    - (* Let *)
      destruct X5.
      + left. destruct i as [ctx [s [Heq Hs]]].
        eexists _, s.
        simpl. split; auto.
        pose proof (PCUICClosed.destArity_spec [] b'_ty).
        rewrite Heq in H. simpl in H. subst b'_ty.
        rewrite destArity_it_mkProd_or_LetIn. simpl.
        reflexivity. rewrite app_context_assoc. simpl.
        apply All_local_env_app_inv; split; eauto with wf.
        apply All_local_env_app in Hs as [Hp Hs].
        apply Hs.
      + right.
        destruct i as [u Hu]. exists u.
        econstructor.
        eapply type_LetIn; eauto. left. exists [], u; intuition eauto with wf.
        eapply cumul_alt. exists (tSort u), (tSort u); intuition auto.
        apply red1_red; repeat constructor.
        reflexivity.

    - (* Application *)
      destruct X1 as [[ctx [s [Heq Hs]]]|].
      simpl in Heq. pose proof (PCUICClosed.destArity_spec ([],, vass na A) B).
      rewrite Heq in H.
      simpl in H. unfold mkProd_or_LetIn in H. simpl in H.
      destruct ctx using rev_ind; noconf H.
      simpl in H. rewrite it_mkProd_or_LetIn_app in H. simpl in H.
      destruct x as [na' [b|] ty]; noconf H.
      left. eexists _, s. split.
      unfold subst1. rewrite subst_it_mkProd_or_LetIn.
      rewrite destArity_it_mkProd_or_LetIn. simpl. reflexivity.
      rewrite app_context_nil_l. apply All_local_env_app_inv; intuition auto.
      apply All_local_env_app in Hs as [wf'Γ wfctx].
      apply All_local_env_app in wfctx as [wfd wfctx].
      eapply All_local_env_subst; eauto. simpl; intros.
      destruct T; simpl in *.
      + rewrite Nat.add_0_r. eapply substitution; eauto. constructor. constructor.
        2: simpl; eauto; now rewrite app_context_assoc in X0.
        now rewrite subst_empty.
      + rewrite Nat.add_0_r. destruct X0 as [u' Hu']. exists u'.
        eapply (substitution _ _ _ _ _ _ (tSort u')); eauto. constructor. constructor.
        2: simpl; eauto; now rewrite app_context_assoc in Hu'.
        now rewrite subst_empty.
      + right.
        destruct i as [u' Hu']. exists u'.
        eapply (substitution0 _ _ na _ _ _ (tSort u')); eauto.
        apply inversion_Prod in Hu' as [na' [s1 [s2 Hs]]]; tas. intuition.
        eapply type_Cumul; pcuic.
        eapply (weakening_cumul Σ Γ [] [vass na A]) in b; pcuic.
        simpl in b. eapply cumul_trans. auto. 2:eauto.
        constructor. constructor. simpl. apply leq_universe_product.

    - destruct decl as [ty [b|] univs]; simpl in *.
      * eapply declared_constant_inv in X; eauto.
        red in X. simpl in X.
        eapply isWAT_weaken; eauto.
        eapply (isWAT_subst_instance_decl _ []); eauto.
        apply weaken_env_prop_isWAT.
      * eapply isWAT_weaken; eauto.
        have ond := on_declared_constant _ _ _ wf H.
        do 2 red in ond. simpl in ond.
        eapply (isWAT_subst_instance_decl _ []); eauto.
        right. simpl. apply ond.

    - (* Inductive type *)
      destruct (on_declared_inductive wf isdecl); pcuic.
      destruct isdecl.
      apply onArity in o0.
      eapply isWAT_weaken; eauto.
      eapply (isWAT_subst_instance_decl _ []); eauto.
      right; simpl; apply o0.

    - (* Constant type *)
      destruct (on_declared_constructor wf isdecl) as [[oni oib] [s [decli [cs onc]]]].
      unfold type_of_constructor.
      right. red in onc. red in onc.
      destruct onc as [s' Hs].
      exists (subst_instance_univ u s').
      eapply instantiate_minductive in Hs; eauto.
      2:(destruct isdecl as [[] _]; eauto).
      simpl in Hs.
      eapply (weaken_ctx (Γ:=[]) Γ); eauto.
      eapply (substitution _ [] _ (inds _ _ _) [] _ (tSort _)); eauto.
      eapply subslet_inds; eauto. destruct isdecl; eauto.
      now rewrite app_context_nil_l.

    - (* Case predicate application *)
      right. red.
      eapply (isWAT_mkApps_Ind wf isdecl) in X4 as [parsubst [argsubst Hind]]; auto.
      destruct (on_declared_inductive wf isdecl) as [onmind oib]. simpl in Hind.
      destruct Hind as [[sparsubst sargsubst] cu].
      subst npar.
      eapply (build_case_predicate_type_spec _ _ _ _ _ _ _ _ oib) in heq_build_case_predicate_type as
        [pars [cs eqty]].
      exists ps.
      eapply type_mkApps; eauto.
      eapply wf_arity_spine_typing_spine; auto.
      split; auto.
      rewrite eqty. clear typep eqty X2.
      eapply arity_spine_it_mkProd_or_LetIn; auto.
      pose proof (context_subst_fun cs sparsubst). subst pars.
      eapply sargsubst.
      simpl. constructor; first last.
      constructor; auto. left; eexists _, _; intuition eauto.
      reflexivity.
      rewrite subst_mkApps.
      simpl.
      rewrite map_app. subst params.
      rewrite map_map_compose. rewrite map_subst_lift_id_eq.
      rewrite (subslet_length sargsubst). now autorewrite with len.
      unfold to_extended_list.
      eapply spine_subst_subst_to_extended_list_k in sargsubst.
      rewrite to_extended_list_k_subst
         PCUICSubstitution.map_subst_instance_constr_to_extended_list_k in sargsubst.
      rewrite sargsubst firstn_skipn. eauto.

    - (* Proj *)
      right.
      apply on_declared_projection in isdecl as [[onm oni] onp]=> //.
      destruct onp as [s Hty].
      exists s.
      subst ty.
      (* eapply typing_subst_instance in Hty. *)
      todo "projection"%string.

    - (* Fix *)
      eapply nth_error_all in X0; eauto.
      firstorder auto.
    
    - (* CoFix *)
      eapply nth_error_all in X0; eauto.
      firstorder auto.

    - (* Conv *)
      destruct X2. red in i. left. exact (projT1 i).
      right. destruct s as [u [Hu _]]. now exists u.
  Qed.

End Validity.

Lemma validity_term {cf:checker_flags} {Σ Γ t T} :
  wf Σ.1 -> Σ ;;; Γ |- t : T -> isWfArity_or_Type Σ Γ T.
Proof.
  intros. eapply validity; try eassumption.
Defined.

(* Should be a corollary of the lemma above.
   invert_type_mkApps should only be used as a stepping stone.
 *)
Lemma inversion_mkApps :
  forall `{checker_flags} {Σ Γ t l T},
    wf Σ.1 ->
    Σ ;;; Γ |- mkApps t l : T ->
    ∑ A U,
      Σ ;;; Γ |- t : A ×
      typing_spine Σ Γ A l U ×
      Σ ;;; Γ |- U <= T.
Proof.
  intros cf Σ Γ f u T wfΣ; induction u in f, T |- *. simpl. intros.
  { exists T, T. intuition pcuic. constructor. eapply validity; auto with pcuic.
    eauto. eapply cumul_refl'. }
  intros Hf. simpl in Hf.
  destruct u. simpl in Hf.
  - eapply inversion_App in Hf as [na' [A' [B' [Hf' [Ha HA''']]]]].
    eexists _, _; intuition eauto.
    econstructor; eauto with pcuic. eapply validity; eauto with wf pcuic.
    constructor. all:eauto with pcuic.
    eapply validity; eauto with wf.
    eapply type_App; eauto. 
  - specialize (IHu (tApp f a) T).
    specialize (IHu Hf) as [T' [U' [H' [H'' H''']]]].
    eapply inversion_App in H' as [na' [A' [B' [Hf' [Ha HA''']]]]]. 2:{ eassumption. }
    exists (tProd na' A' B'), U'. intuition; eauto.
    econstructor. eapply validity; eauto with wf.
    eapply cumul_refl'. auto.
    clear -H'' HA''' wfΣ. depind H''.
    econstructor; eauto. eapply cumul_trans; eauto.  
Qed.
