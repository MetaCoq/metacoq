From Coq Require Import String Bool List PeanoNat Lia.
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
      destruct (declared_inductive_inj isdecl decli) as [-> ->].
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

  (* Lemma type_local_ctx_smash Γ s Σ :
    type_local_ctx
      (lift_typing
      (fun (Σ : PCUICEnvironment.global_env_ext) 
          (Γ : context) (_ T : term) => isWfArity_or_Type Σ Γ T))
    Σ Γ Δ 
  (PCUICEnvironment.arities_context
     (PCUICEnvironment.ind_bodies mdecl) ,,,
   PCUICEnvironment.ind_params mdecl) (cshape_args c) 
  (cshape_sort c) *)

  Local Notation isWAT :=
    (lift_typing
      (fun (Σ0 : PCUICEnvironment.global_env_ext) (Γ : context) (_ T : term)
    => isWfArity_or_Type Σ0 Γ T)).
(* 
  Lemma All_local_env_isWAT_wf_local Σ Γ :
    wf_local Σ Γ ->
    All_local_env (isWAT Σ) Γ.
  Proof.
    intros; eapply All_local_env_impl; eauto.
    intros. red in X0.
    destruct T; hnf. 2:{} *)

  Lemma subst_context_smash_context s k Γ Δ :
    subst_context s k (smash_context Γ Δ) = 
    smash_context (subst_context s (#|Δ| + k) Γ) (subst_context s k Δ).
  Proof.
    induction Δ as [|[? [] ?] ?] in Γ |- *; simpl; auto;
     rewrite subst_context_snoc; simpl.
    - rewrite IHΔ. f_equal.
      rewrite !subst_context_alt !mapi_mapi. apply mapi_ext. clear.
      intros n x. rewrite /subst_decl !PCUICAstUtils.compose_map_decl.
      eapply PCUICAstUtils.map_decl_ext. intros.
      autorewrite with len. rewrite Nat.add_0_r.
      generalize (Nat.pred #|Γ| - n). generalize (#|Δ| + k). clear.
      intros. rewrite distr_subst_rec. simpl. now rewrite -Nat.add_assoc.
    - rewrite IHΔ. f_equal.
      rewrite subst_context_app. simpl.  unfold app_context. f_equal.
  Qed.

  Lemma wf_local_smash_context_gen Σ Γ Δ :
    wf Σ.1 ->
    wf_local Σ Γ -> All_local_env (fun Δ => lift_typing typing Σ (Γ ,,, Δ)) Δ -> 
    wf_local Σ (smash_context Δ Γ).
  Proof.
    intros wfΣ.
    induction 1 in Δ |- *; simpl; auto.
    - intros wfΔ. eapply (All_local_env_impl _ _ _ wfΔ).
      intros. now rewrite app_context_nil_l in X.
    - intros a.
      apply IHX. eapply All_local_env_app_inv. split; auto.
      repeat constructor; auto.
      eapply All_local_env_impl; eauto. simpl; intros.
      now rewrite app_context_assoc.
    - intros a.
      apply IHX. eapply All_local_env_subst; eauto. simpl; intros.
      destruct T; unfold lift_typing in *; simpl in *; firstorder auto.
      rewrite Nat.add_0_r.
      eapply (substitution _ Γ [vdef na b t] [b] Γ0) in X0; eauto.
      rewrite -{1}(subst_empty 0 b). repeat constructor. now rewrite !subst_empty.
      exists x.
      rewrite Nat.add_0_r.
      eapply (substitution _ Γ [vdef na b t] [b] Γ0) in p; eauto.
      rewrite -{1}(subst_empty 0 b). repeat constructor. now rewrite !subst_empty.
  Qed.
  
  Lemma wf_local_smash_context Σ Γ :
    wf Σ.1 -> wf_local Σ Γ -> wf_local Σ (smash_context [] Γ).
  Proof.
    intros; eapply wf_local_smash_context_gen; eauto.
  Qed.


  Lemma nth_error_ass_subst_context s k Γ : 
    (forall n d, nth_error Γ n = Some d -> decl_body d = None) ->
    forall n d, nth_error (subst_context s k Γ) n = Some d -> decl_body d = None.
  Proof.
    induction Γ as [|[? [] ?] ?] in |- *; simpl; auto;
    intros; destruct n; simpl in *; rewrite ?subst_context_snoc in H0; simpl in H0.
    - noconf H0; simpl.
      specialize (H 0 _ eq_refl). simpl in H; discriminate.
    - specialize (H 0 _ eq_refl). simpl in H; discriminate.
    - noconf H0; simpl. auto.
    - eapply IHΓ. intros. now specialize (H (S n0) d0 H1).
      eauto.
  Qed.

  Lemma nth_error_smash_context Γ Δ : 
    (forall n d, nth_error Δ n = Some d -> decl_body d = None) ->
    forall n d, nth_error (smash_context Δ Γ) n = Some d -> decl_body d = None.
  Proof.
    induction Γ as [|[? [] ?] ?] in Δ |- *; simpl; auto.
    - intros. eapply (IHΓ (subst_context [t] 0 Δ)).
      apply nth_error_ass_subst_context. auto. eauto.
    - intros. eapply IHΓ. 2:eauto.
      intros.
      pose proof (nth_error_Some_length H1). autorewrite with len in H2. simpl in H2.
      destruct (eq_dec n0 #|Δ|). subst.
      rewrite nth_error_app_ge in H1. lia. rewrite Nat.sub_diag /= in H1. noconf H1.
      reflexivity.
      rewrite nth_error_app_lt in H1; try lia. eauto.
  Qed.

  Lemma fold_context_compose f g Γ : 
    fold_context f (fold_context g Γ) = fold_context (fun n x => f n (g n x)) Γ.
  Proof.
    induction Γ; simpl; auto; rewrite !fold_context_snoc0.
    simpl. rewrite IHΓ. f_equal.
    rewrite PCUICAstUtils.compose_map_decl.
    now rewrite fold_context_length.
  Qed.

  Lemma fold_context_ext f g Γ : 
    f =2 g ->
    fold_context f Γ = fold_context g Γ.
  Proof.
    intros hfg.
    induction Γ; simpl; auto; rewrite !fold_context_snoc0.
    simpl. rewrite IHΓ. f_equal. apply PCUICAstUtils.map_decl_ext.
    intros. now apply hfg.
  Qed.

  (* Replace index k with n in i, k + S n |- x -> i, n, n, k
  Lemma subst_under_lift s n k x i : 

    subst s k (lift n (k + #|s|) x) = lift n k (subst s 0 x).
 *)
  Arguments Nat.sub : simpl never.
  (* Smashing a context Γ with Δ depending on it is the same as smashing Γ
     and substituting all references to Γ in Δ by the expansions of let bindings.
  *)

  Local Open Scope sigma.
  Require Import PCUICSigmaCalculus PCUICClosed.
  Lemma Upn_compose n σ σ' : ⇑^n σ ∘s ⇑^n σ' =1 ⇑^n (σ ∘s σ').
  Proof.
    induction n. unfold Upn. simpl.
    now rewrite !subst_consn_nil !shiftk_0 !compose_ids_r.
    rewrite !Upn_S. autorewrite with sigma. now rewrite IHn.
  Qed.

  Fixpoint extended_subst (Γ : context) (n : nat) :=
    match Γ with
    | nil => nil
    | cons d vs =>
      match decl_body d with
      | Some b =>
        (* Δ , vs |- b *)
        let s := extended_subst vs n in
        (* Δ , smash_context vs |- s : vs *)
        let b' := subst0 s (lift (context_assumptions vs) #|s| b) in
        (* Δ, smash_context vs |- b' *)
        b' :: s
      | None => tRel n :: extended_subst vs (S n)
      end
    end.

  Lemma extended_subst_length Γ n : #|extended_subst Γ n| = #|Γ|.
  Proof.
    induction Γ in n |- *; simpl; auto.
    now destruct a as [? [?|] ?] => /=; simpl; rewrite IHΓ. 
  Qed.
  Hint Rewrite extended_subst_length : len.
  (* Lemma Up_compose σ s : ⇑ σ ∘s (s ⋅n ids) *)

  Lemma extended_subst_lift (Δ : context) n : 
    extended_subst Δ n = map (lift0 n) (extended_subst Δ 0).
  Proof.
    rewrite -{1}(Nat.add_0_r n).
    generalize 0 at 1 3. revert n.
    induction Δ.
    simpl. auto.
    intros n n'.
    destruct a as [na [?|] ?]. simpl.
    f_equal. 2:auto.
    specialize (IHΔ n n').
    rewrite IHΔ.
    rewrite (distr_lift_subst _ _ n 0).
    rewrite extended_subst_length Nat.add_0_r.
    admit.
    simpl. f_equal; auto. specialize (IHΔ n (S n')).
    now rewrite -Nat.add_succ_r.
  Admitted.

  Hint Rewrite Nat.add_0_r : len.

  Lemma subst_consn_lt i (s : list term) σ : 
    i < #|s| -> 
    ∑ x, List.nth_error s i = Some x /\ (s ⋅n σ) i = x.
  Proof.
    clear.
    induction i in s |- *.
    simpl. destruct s; simpl.
    - lia.
    - intros lt. exists t; simpl; auto.
    - intros lt. destruct s; [elimtype False;inv lt|].
      simpl in *. specialize (IHi s). forward IHi by lia.
      destruct IHi as [? ?]; firstorder.
  Qed.
  
  Lemma up_ext_closed k' k s s' :
    (forall i, i < k' -> s i = s' i) -> 
    forall i, i < k + k' ->
    up k s i = up k s' i.
  Proof.
    unfold up. intros Hs t. elim (Nat.leb_spec k t) => H; auto.
    intros. f_equal. apply Hs. lia.
  Qed.

  Lemma inst_ext_closed s s' k t : 
    closedn k t -> 
    (forall x, x < k -> s x = s' x) -> 
    inst s t = inst s' t.
  Proof.
    clear.
    intros clt Hs. revert k clt s s' Hs.
    elim t using PCUICInduction.term_forall_list_ind; simpl in |- *; intros; try easy ;
      try (try rewrite H; try rewrite H0 ; try rewrite H1 ; easy);
      try solve [f_equal; solve_all].
    - apply Hs. now eapply Nat.ltb_lt. 
    - move/andP: clt => []. intros. f_equal; eauto.
      eapply H0; eauto. intros. eapply up_ext_closed; eauto.
    - move/andP: clt => []. intros. f_equal; eauto. now eapply H0, up_ext_closed.
    - move/andP: clt => [] /andP[] ?. intros. f_equal; eauto.
      now eapply H1, up_ext_closed.
    - move/andP: clt => [] ? ?. f_equal; eauto.
    - move/andP: clt => [] /andP[] ? ? b1.
      red in X. solve_all. f_equal; eauto.
      eapply All_map_eq. eapply (All_impl b1). firstorder.
    - f_equal; eauto. red in X. solve_all.
      move/andP: b => []. eauto. intros.
      apply map_def_eq_spec; eauto.
      eapply b0; eauto. now apply up_ext_closed.
    - f_equal; eauto. red in X. solve_all.
      move/andP: b => []. eauto. intros.
      apply map_def_eq_spec; eauto.
      eapply b0; eauto. now apply up_ext_closed.
  Qed.

  Lemma subst_consn_eq s0 s1 s2 s3 x : 
    x < #|s0| -> #|s0| = #|s2| ->
    subst_fn s0 x = subst_fn s2 x ->
    (s0 ⋅n s1) x = (s2 ⋅n s3) x.
  Proof.
    unfold subst_fn; intros Hx Heq Heqx.
    unfold subst_consn. 
    destruct (nth_error s0 x) eqn:Heq';
    destruct (nth_error s2 x) eqn:Heq''; auto.
    apply nth_error_None in Heq''. lia.
    apply nth_error_None in Heq'. lia.
    apply nth_error_None in Heq'. lia.
  Qed.

  Lemma inst_extended_subst_shift_ind (Γ : context) k : 
    closed_ctx Γ ->
    (forall x, x < #|Γ| -> 
      option_map (fun x0 : term => x0.[↑^k]) (nth_error (extended_subst Γ 0) x) =
      nth_error (extended_subst Γ k) x) ->
    map (inst ((extended_subst Γ 0 ⋅n ids) ∘s ↑^k)) (idsn #|Γ|) =
    map (inst (extended_subst Γ k ⋅n ids)) (idsn #|Γ|).
  Proof.
    intros.
    rewrite !map_idsn_spec.
    apply nat_recursion_ext => x l' Hx.
    f_equal. f_equal.
    edestruct (subst_consn_lt x (extended_subst Γ k) ids) as [d [Hd Hσ]].
    now (autorewrite with len; lia).
    simpl. rewrite Hσ.
    edestruct (subst_consn_lt x (extended_subst Γ 0) ids) as [d' [Hd' Hσ']].
    now autorewrite with len.
    unfold subst_compose. rewrite Hσ'.
    apply some_inj.
    rewrite -Hd. change (Some d'.[↑^k]) with (option_map (fun x => inst (↑^k) x) (Some d')).
    rewrite -Hd'. now apply H0.
  Qed.

  Hint Rewrite idsn_length : len.

  Lemma subst_fn_eq s s' x : s = s' -> subst_fn s x = subst_fn s' x.
  Proof.
    intros -> ; reflexivity.
  Qed.

  Lemma extended_subst_shift (Γ : context) k : 
    closed_ctx Γ ->
    forall x, x < #|Γ| -> 
    option_map (fun x0 : term => x0.[↑^k]) (nth_error (extended_subst Γ 0) x) =
    nth_error (extended_subst Γ k) x.
  Proof.
    intros clΓ.
    induction Γ in k, clΓ |- *. simpl. lia.
    simpl; intros x Hx.
    intros. 
    destruct a as [? [] ?]; auto.
    simpl.
    autorewrite with sigma.
    rewrite !ren_lift_renaming. autorewrite with len.
    rewrite Upn_eq. rewrite !subst_consn_compose.
    autorewrite with sigma.
    move/closedn_ctx_cons/andP: clΓ => [clΓ /andP [clt _]].
    simpl in clt.
    destruct x. simpl. f_equal.
    autorewrite with sigma.
    rewrite subst_consn_compose.
    eapply inst_ext_closed; eauto.
    intros.
    apply subst_consn_eq; autorewrite with len; auto.
    pose proof (inst_extended_subst_shift_ind Γ k clΓ).
    rewrite -H0. intros. apply IHΓ; auto.
    rewrite map_map_compose. apply subst_fn_eq.
    apply map_ext. intros.
    now autorewrite with sigma.

    simpl. apply IHΓ; auto. lia.

    simpl.
    destruct x; simpl. unfold shiftk.
    now rewrite Nat.add_0_r.
    move/closedn_ctx_cons/andP: clΓ => [clΓ /andP [clt _]].
    rewrite -(IHΓ (S k)); auto. lia.
    rewrite -(IHΓ 1 clΓ x ltac:(lia)).
    rewrite option_map_two. apply option_map_ext.
    intros. autorewrite with sigma.
    now rewrite -shiftk_shift -shiftk_shift_l.
  Qed.

  Lemma inst_extended_subst_shift (Γ : context) k : 
    closed_ctx Γ ->
    map (inst ((extended_subst Γ 0 ⋅n ids) ∘s ↑^k)) (idsn #|Γ|) =
    map (inst (extended_subst Γ k ⋅n ids)) (idsn #|Γ|).
  Proof.
    intros. apply inst_extended_subst_shift_ind; auto.
    now apply extended_subst_shift.
  Qed.

  Lemma smash_context_acc Γ Δ : 
    closed_ctx Γ ->
    smash_context Δ Γ =
        subst_context (extended_subst Γ 0) 0 (lift_context (context_assumptions Γ) #|Γ| Δ)
     ++ smash_context [] Γ.
  Proof.
    revert Δ.
    induction Γ as [|[? [] ?] ?]; intros Δ cl.
    - simpl; auto.
      now rewrite subst0_context app_nil_r lift0_context.
    - simpl. autorewrite with len.
      move/closedn_ctx_cons/andP: cl => [clΓ /andP [clt _]].
      rewrite IHΓ; auto.
      rewrite subst_context_nil. f_equal.
      rewrite (subst_context_decompo [_] _).
      simpl. autorewrite with len.
      rewrite lift0_id.
      rewrite subst0_context.
      unfold subst_context, lift_context.
      rewrite !fold_context_compose.
      apply fold_context_ext. intros n n' -> x.
      rewrite Nat.add_0_r.
      autorewrite with sigma.
      apply inst_ext.
      setoid_rewrite ren_lift_renaming.
      autorewrite with sigma.
      rewrite !Upn_compose.
      apply Upn_ext. 
      autorewrite with sigma.
      unfold Up.
      rewrite subst_consn_subst_cons.
      autorewrite with sigma.
      reflexivity.
      
    - simpl.
      move/closedn_ctx_cons/andP: cl => [clΓ /andP [clt _]].
      rewrite IHΓ /=. auto.
      rewrite (IHΓ [_]). auto. rewrite !app_assoc. f_equal.
      rewrite app_nil_r. unfold map_decl. simpl. unfold app_context.
      simpl. rewrite lift_context_app subst_context_app /app_context. simpl.
      unfold lift_context at 2. unfold subst_context at 2, fold_context. simpl.
      f_equal.
      unfold subst_context, lift_context.
      rewrite !fold_context_compose.
      apply fold_context_ext. intros n n' ->. intros x.
      rewrite Nat.add_0_r.

      autorewrite with sigma.
      apply inst_ext. rewrite !ren_lift_renaming.
      autorewrite with sigma.
      rewrite !Upn_compose.
      autorewrite with sigma.
      apply Upn_ext.
      unfold Up.
      
      rewrite subst_consn_subst_cons.
      autorewrite with sigma.
      apply subst_cons_proper. auto.
      rewrite !Upn_eq. autorewrite with sigma.
      rewrite !subst_consn_compose.
      setoid_rewrite subst_consn_compose at 2 3.
      apply subst_consn_proper.
      rewrite -inst_extended_subst_shift; auto.

      autorewrite with sigma.
      rewrite -subst_compose_assoc.
      rewrite shiftk_compose.
      autorewrite with sigma.
      setoid_rewrite <- (compose_ids_l ↑) at 2.
      rewrite -subst_consn_compose.
      rewrite - !subst_compose_assoc.
      rewrite -shiftk_shift shiftk_compose.
      autorewrite with sigma.
      rewrite subst_consn_compose.
      rewrite -shiftk_compose subst_compose_assoc.
      rewrite subst_consn_shiftn.
      2:now autorewrite with len.
      autorewrite with sigma. 
      rewrite -shiftk_shift.
      rewrite -shiftk_compose subst_compose_assoc.
      rewrite subst_consn_shiftn.
      2:now autorewrite with len.
      now autorewrite with sigma.
  Qed.

  Lemma skipn_0_eq {A} (l : list A) n : n =  0 -> skipn n l = l.
  Proof. intros ->; apply PCUICAstUtils.skipn_0. Qed.
 
  Lemma extended_subst_to_extended_list_k Γ k :
    (map (subst0 (extended_subst Γ k)) (to_extended_list_k Γ k)) = 
    to_extended_list_k (smash_context [] Γ) k.
  Proof.
    induction Γ in k |- *. simpl. reflexivity.
    unfold to_extended_list_k. simpl.
    destruct a as [? [] ?]; simpl. admit.
  Admitted.


  (* Well, it's a smash_context mess! *)
  Lemma declared_projection {Σ : global_env_ext} {mdecl idecl p pdecl} : 
    wf Σ.1 ->
    declared_projection Σ.1 mdecl idecl p pdecl ->
    let u := PCUICLookup.abstract_instance (ind_universes mdecl) in
    let ind := p.1.1 in
    isType (Σ.1, ind_universes mdecl)
      ((vass nAnon (mkApps (tInd ind u) (to_extended_list (smash_context [] (ind_params mdecl)))))::
         smash_context [] (ind_params mdecl)) pdecl.2.
  Proof.
    intros wfΣ isdecl u ind.
    destruct (on_declared_projection wfΣ isdecl) as [oni onp].
    set (declared_inductive_inv _ wfΣ _ isdecl.p1) as oib in *.
    clearbody oib.
    have onpars := onParams _ _ _ _ (declared_minductive_inv weaken_env_prop_typing wfΣ wfΣ isdecl.p1.p1).
    have parslen := onNpars _ _ _ _ (declared_minductive_inv weaken_env_prop_typing wfΣ wfΣ isdecl.p1.p1).
    simpl in onp. destruct (ind_cshapes oib) as [|? []] eqn:Heq; try contradiction.
    red in onp.
    destruct (nth_error (smash_context [] _) _) eqn:Heq'; try contradiction.
    rewrite {}onp.
    assert(onProjs :  on_projections mdecl (inductive_mind p.1.1) (inductive_ind p.1.1) idecl (ind_indices oib) c).
    { destruct oib.
      assert (ind_projs idecl <> []).
      { destruct isdecl as [? [hnth]]. eapply nth_error_Some_non_nil in hnth; auto. }
      simpl in Heq. simpl. rewrite Heq in onProjections.
      now specialize (onProjections H). }
    assert(projslen : #|ind_projs idecl| = (context_assumptions (cshape_args c))).
    { now destruct onProjs. }
    assert (some_proj :#|ind_projs idecl| > 0).
    { destruct isdecl as [ [] []]. now apply nth_error_Some_length in H1. }
    pose proof (onConstructors oib) as onc. 
    red in onc. rewrite Heq in onc. inv onc. clear X0.
    eapply on_cargs in X.
    simpl.
    assert (wf_local (Σ.1, ind_universes mdecl) (arities_context (ind_bodies mdecl))).
    { eapply wf_arities_context; eauto. now destruct isdecl as [[] ?]. }
    eapply PCUICClosed.type_local_ctx_All_local_env in X.
    2:{ eapply All_local_env_app_inv. split; auto.
        red in onpars. eapply (All_local_env_impl _ _ _ onpars).
        intros. destruct T; simpl in *.
        - eapply weaken_ctx; auto.
        - destruct X1 as [s Hs]. exists s. apply weaken_ctx; auto. }
    rewrite -(app_context_nil_l (arities_context _)) in X.
    rewrite -app_context_assoc in X.
    eapply (substitution_wf_local _ []) in X; auto.
    2:{ eapply subslet_inds_gen; eauto. destruct isdecl as []; eauto. }
    rewrite app_context_nil_l in X.
    epose proof (nth_error_subst_context _ _ _ _).
    erewrite Heq' in H. autorewrite with len in H. clear Heq'.
    rewrite subst_context_smash_context in H.
    autorewrite with len in H. rewrite subst_context_nil in H.
    move: X.
    rewrite subst_context_app.
    rewrite (closed_ctx_subst _ _ (ind_params mdecl)).
    red in onpars. eapply closed_wf_local; [|eauto]. auto.
    assert (parsu : subst_instance_context u (ind_params mdecl) = ind_params mdecl). admit.
    assert (sortu : subst_instance_univ u (ind_sort oib) = ind_sort oib). admit.
    pose proof (spine_subst_to_extended_list_k (Σ.1, ind_universes mdecl)
      (ind_params mdecl) []).
    forward X; auto.
    forward X. rewrite app_context_nil_l; auto.
    rewrite app_context_nil_l in X.
    rewrite closed_ctx_lift in X.
    red in onpars. eapply closed_wf_local; [|eauto]. auto.
    assert(wf_local (Σ.1, ind_universes mdecl) (ind_params mdecl ,, vass nAnon (mkApps (tInd ind u) (to_extended_list (ind_params mdecl))))).
    constructor. auto. red. exists (ind_sort oib).
    eapply type_mkApps. econstructor; eauto.
    destruct isdecl as []; eauto. subst u. admit.
    rewrite (ind_arity_eq oib).
    rewrite subst_instance_constr_it_mkProd_or_LetIn.
    rewrite -(app_nil_r (to_extended_list _)).
    eapply typing_spine_it_mkProd_or_LetIn'; auto.
    rewrite parsu. eapply X.
    constructor. left. eexists _, _; simpl; intuition auto.
    pose proof (onProjs.(on_projs_noidx _ _ _ _ _ _)).
    destruct (ind_indices oib); simpl in H0; try discriminate.
    simpl. rewrite sortu. reflexivity.
    rewrite -subst_instance_constr_it_mkProd_or_LetIn.
    right. pose proof (onArity oib). rewrite -(oib.(ind_arity_eq)).
    destruct X1 as [s Hs]. exists s.
    eapply (weaken_ctx (Γ:=[])). auto. auto. admit.
    intros wf.
    generalize (weakening_wf_local _ _ _ [_] _ wf X1).
    simpl; clear X1 wf.
    move/wf_local_smash_context => /=.
    rewrite smash_context_app /= smash_context_acc.
    red in onpars. eapply closed_wf_local; [|eauto]. auto.
    set(indsubst := (inds (inductive_mind p.1.1) (PCUICLookup.abstract_instance (PCUICEnvironment.ind_universes mdecl))
      (PCUICEnvironment.ind_bodies mdecl))) in *.
    set (projsubst :=  (projs {| inductive_mind := inductive_mind p.1.1; inductive_ind := inductive_ind p.1.1 |}
    (PCUICEnvironment.ind_npars mdecl) p.2)) in *.
    rewrite lift_context_app. simpl.
    rewrite [subst_context _ _ (_ ++ _)]subst_context_app.
    simpl. unfold app_context. simpl.
    unfold lift_context at 3. unfold fold_context. simpl.
    unfold map_decl. simpl. rewrite lift_mkApps. simpl.
    rewrite {3}/subst_context /fold_context /= /map_decl /= subst_mkApps /=.
    rewrite /to_extended_list lift_to_extended_list_k.
    rewrite extended_subst_to_extended_list_k.
    fold (to_extended_list (smash_context [] (ind_params mdecl))).
    intros wfl.
    rewrite PCUICClosed.closed_ctx_lift in wfl. admit.
    


    rewrite -reln_lift.
    set(foo:= subst_context _ _ _).
    rewrite subst_context_app.
    eapply nth_error_All_local_env in X.
    2:{ eapply nth_error_Some_length in H. apply H. }
    unfold app_context in X. erewrite H in X.
    simpl in X, H. red in X.
    destruct c0 as [? [] ?]; simpl in *.
    unfold subst_decl, map_decl in H; simpl in H.
    eapply nth_error_smash_context in H. simpl in H. discriminate.
    clear H.
    intros. rewrite nth_error_nil // in H.
    destruct X as [s Hs].
    rewrite smash_context_length /= in Hs.
    rewrite PCUICClosed.context_assumptions_app Nat.add_0_r in Hs.
    clear H.
    set (k := context_assumptions (cshape_args c) - p.2) in *.
    rewrite subst_context_app Nat.add_0_r in Hs.
    rewrite (closed_ctx_subst _ _ (ind_params mdecl)) in Hs.
    red in onpars. eapply closed_wf_local; [|eauto]. auto.
    rewrite /app_context smash_context_app in Hs.
    exists s. red.
    rewrite smash_context_acc in Hs.
    rewrite skipn_app in Hs.
    autorewrite with len in Hs. rewrite !smash_context_length in Hs.
    rewrite context_assumptions_fold in Hs.
    rewrite (skipn_0_eq _ (S _ - _)) in Hs.
    simpl length. lia.
    destruct isdecl as [? []]. apply nth_error_Some_length in H0.
    rewrite projslen in H0. rewrite projslen in some_proj. lia.
    simpl. lia.


    



    replace ((context_assumptions (cshape_args c) +
    context_assumptions (PCUICEnvironment.ind_params mdecl) -
    S (PCUICEnvironment.context_assumptions (cshape_args c) - p.2)))
    with  (context_assumptions (PCUICEnvironment.ind_params mdecl) + S p.2) by lia.
        S (PCUICEnvironment.context_assumptions (cshape_args c) - p.2)))
    autorewrite with len in Hs.

    eexists _.
    rename X into args.
    apply type_local_ctx_Pclosed in args.
    red in onpars.
    eapply All_local_env_Pclosed in onpars.
    eapply (Alli_impl (Q:=fun i d => closed_decl (#|ind_params mdecl| + i + #|arities_context (ind_bodies mdecl)|) d)) in args.
    2:{ intros n x. rewrite app_context_length. 
        intros H; eapply closed_decl_upwards; eauto. lia. }
    eapply (Alli_shiftn (P:=fun i d => closed_decl (i + #|arities_context (ind_bodies mdecl)|) d)) in args.
    rewrite Nat.add_0_r in args.
    eapply (Alli_impl (Q:=fun i d => closed_decl (i + #|arities_context (ind_bodies mdecl)|) d)) in onpars.
    2:{ intros n x d. eapply closed_decl_upwards; eauto; lia. }
    epose proof (Alli_app_inv onpars). rewrite List.rev_length /= in X.
    specialize (X args). rewrite -List.rev_app_distr in X.
    clear onpars args.
    eapply (Alli_impl (Q:=fun i d => closed_decl (#|arities_context (ind_bodies mdecl)| + i) d)) in X.
    2:intros; eapply closed_decl_upwards; eauto; lia.
    eapply closed_smash_context in X.
    eapply Alli_rev_nth_error in X; eauto.
    rewrite smash_context_length in X. simpl in X.
    eapply nth_error_Some_length in Heq'. rewrite smash_context_length in Heq'.
    simpl in Heq'. unfold closed_decl in X.
    move/andP: X => [] _ cl.
    eapply closed_upwards. eauto. rewrite arities_context_length.
    rewrite context_assumptions_app parslen.
    rewrite context_assumptions_app in Heq'. lia.
  Qed.
 *)


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
      destruct (on_declared_constructor wf isdecl) as [[oni oib] [cs [declc onc]]].
      unfold type_of_constructor.
      right. have ctype := on_ctype onc.
      destruct ctype as [s' Hs].
      exists (subst_instance_univ u s').
      eapply instantiate_minductive in Hs; eauto.
      2:(destruct isdecl as [[] ?]; eauto).
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
      destruct (on_declared_projection wf isdecl) as [oni onp].
      destruct declared_inductive_inv. simpl in onp.
      as [[onm oni] onp]=> //.
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
