From Coq Require Import Bool String List Program BinPos Compare_dec PeanoNat Lia.
From MetaCoq.Template Require Import utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICTyping PCUICWeakeningEnv PCUICWeakening PCUICInversion
     PCUICSubstitution PCUICReduction PCUICCumulativity PCUICGeneration.
From Equations Require Import Equations.
Require Import ssreflect.
Existing Instance config.default_checker_flags.

Derive NoConfusion for term.
Derive Signature for typing cumul.

Lemma isWfArity_or_Type_lift Σ n Γ ty (isdecl : n <= #|Γ|):
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
      unshelve eapply (weakening_typing Σ (skipn n Γ) Γ0 (firstn n Γ) t _ _ _ (tSort u)); eauto with wf.
      apply All_local_env_app_inv. intuition eauto.
    + destruct t0 as [u Hu]. exists u. rewrite Nat.add_0_r.
      unshelve eapply (weakening_typing Σ (skipn n Γ) Γ0 (firstn n Γ) t _ _ _ (tSort u)); eauto with wf.
      apply All_local_env_app_inv. intuition eauto.
    + rewrite Nat.add_0_r.
      unshelve eapply (weakening_typing Σ (skipn n Γ) Γ0 (firstn n Γ) b _ _ _ t); eauto with wf.
      eapply All_local_env_app_inv. intuition eauto.
  - right. destruct i as [u Hu]. exists u.
    rewrite {3}H.
    unshelve eapply (weakening_typing Σ (skipn n Γ) [] (firstn n Γ) ty _ _ _ (tSort u)); eauto with wf.
Qed.

Lemma destArity_it_mkProd_or_LetIn ctx ctx' t :
  destArity ctx (it_mkProd_or_LetIn ctx' t) =
  destArity (ctx ,,, ctx') t.
Proof.
  induction ctx' in ctx, t |- *; simpl; auto.
  rewrite IHctx'. destruct a as [na [b|] ty]; reflexivity.
Qed.

Lemma isWfArity_Sort Σ Γ s : wf_local Σ Γ -> isWfArity typing Σ Γ (tSort s).
Proof.
  intros. exists [], s; intuition auto.
Qed.
Hint Extern 10 (isWfArity _ _ _ (tSort _)) => apply isWfArity_Sort : pcuic.

Hint Extern 30 (wf_local ?Σ ?Γ) =>
  match goal with
    | [ H : typing Σ Γ _ _ |- _ ] => apply (typing_wf_local H)
  end : pcuic.

Ltac pcuic := try solve [ intuition typeclasses eauto with pcuic ].

Definition weaken_env_prop_full
           (P : global_context -> context -> term -> term -> Type) :=
  forall Σ Σ', wf Σ' -> extends Σ Σ' -> forall Γ t T, P Σ Γ t T -> P Σ' Γ t T.

Lemma isWfArity_or_Type_weaken_full : weaken_env_prop_full (fun Σ Γ t T => isWfArity_or_Type Σ Γ T).
Proof.
  red. intros.
  destruct X1. left. destruct i as [ctx [s [Heq Hs]]].
  exists ctx, s. pcuic. right. destruct i as [u Hu]; exists u; pcuic.
  unshelve eapply (weaken_env_prop_typing _ _ _ X0 _ _ (Some (tSort u))); eauto.
Qed.
Hint Resolve isWfArity_or_Type_weaken_full : pcuic.

Lemma isWfArity_or_Type_weaken :
 weaken_env_prop
   (lift_typing (fun Σ Γ (_ T : term) => isWfArity_or_Type Σ Γ T)).
Proof.
  red. intros. unfold lift_typing in *. destruct T. now eapply isWfArity_or_Type_weaken_full.
  destruct X1 as [s Hs]; exists s. now eapply isWfArity_or_Type_weaken_full.
Qed.
Hint Resolve isWfArity_or_Type_weaken : pcuic.

(** TODO: Universe instances *)
Lemma isWfArity_or_Type_subst_instance:
  forall (Σ : global_context) (Γ : context) (u : list Level.t) (ty : term), wf_local Σ Γ ->
    isWfArity_or_Type Σ [] ty -> isWfArity_or_Type Σ Γ (PCUICUnivSubst.subst_instance_constr u ty).
Proof.
  intros Σ Γ u ty wfΓ H.
  destruct H as [[ctx [s [Heq Hs]]]|].
  - left.
    exists ctx, s. split; pcuic.
Admitted.
Derive Signature for subslet.
  Notation "'∑'  x .. y , P" := (sigT (fun x => .. (sigT (fun y => P%type)) ..))
    (at level 200, x binder, y binder, right associativity) : type_scope.
Hint Constructors subslet : pcuic.

Lemma subslet_app Σ Γ args l l' :
  subslet Σ Γ args (l ++ l') ->
  ∑ (args' : list term) (args'' : list term),
  (args = args'' ++ args')
  * subslet Σ Γ args' l' * subslet Σ Γ args'' (subst_context args' 0 l).
Proof.
  intros Hs. depind Hs.
  - destruct l; try discriminate. destruct l'; try discriminate.
    exists [], []. split; auto with pcuic.
  - destruct l; simpl in *.
    subst l'.
    exists (t :: s), []. split; auto with pcuic.
    noconf H.
    specialize (IHHs s l l' eq_refl).
    destruct IHHs as [args' [args'' [[Hs' Hl'] Hsl]]].
    subst s.
    exists args', (t :: args''). simpl.
    split; auto. rewrite subst_context_snoc. simpl. constructor; auto.
    simpl. rewrite Nat.add_0_r.
    pose proof (substlet_length Hl').
    pose proof (substlet_length Hsl). rewrite subst_context_length in H0.
    rewrite <- H0. rewrite subst_app_simpl in t0. now simpl in t0.
  - destruct l; simpl in *.
    + subst l'.
      exists (subst0 s t :: s), []. split; auto with pcuic.
    + noconf H.
      specialize (IHHs s l l' eq_refl).
      destruct IHHs as [args' [args'' [[Hs' Hl'] Hsl]]].
      subst s.
      exists args', (subst0 (args'' ++ args') t :: args''). simpl.
      split; auto. rewrite subst_context_snoc. simpl.
      rewrite subst_app_simpl. simpl. rewrite Nat.add_0_r.
      unfold subst_decl. unfold map_decl. simpl.
      pose proof (substlet_length Hl').
      pose proof (substlet_length Hsl). rewrite subst_context_length in H0.
      rewrite <- H0. constructor; auto. rewrite !subst_app_simpl in t0. now simpl in t0.
Qed.

Lemma typing_spine_arity Σ Γ ctx u args s :
  wf_local Σ Γ ->
  context_subst ctx args s ->
  subslet Σ Γ s ctx ->
  typing_spine Σ Γ (it_mkProd_or_LetIn ctx (tSort u)) args (tSort u).
Proof.
  intros wfΓ Hargss Hs. revert args Hargss Hs; induction ctx using rev_ind; cbn; intros.
  - depelim Hs. depelim Hargss. constructor; auto. left. exists [], u. intuition auto.
  - rewrite it_mkProd_or_LetIn_app. simpl.
    destruct x as [na [b|] ty]; cbn.
    + eapply subslet_app in Hs as (args' & args'' & (-> & H) & H').
      depelim H. simpl in H0. noconf H0.
      hnf in H0. noconf H0. depelim H. rewrite !subst_empty in t0, H', Hargss.

      rewrite subst_empty in H'. simpl in H'.


Lemma typing_spine_arity Σ Γ ctx s args :
  wf_local Σ Γ ->
  subslet Σ Γ args ctx ->
  typing_spine Σ Γ (it_mkProd_or_LetIn ctx (tSort s)) args (tSort s).
Proof.
  intros wfΓ Hs. revert args Hs; induction ctx using rev_ind; cbn; intros.
  - depelim Hs. constructor; auto. left. exists [], s. intuition auto.
  - rewrite it_mkProd_or_LetIn_app. simpl.
    destruct x as [na [b|] ty]; cbn.
    eapply subslet_app in Hs as (args' & args'' & (-> & H) & H').
    depelim H. simpl in H0. noconf H0.
    hnf in H0. noconf H0. depelim H. rewrite subst_empty.
    rewrite subst_empty in H'. simpl in H'.



    depelim Hs. apply (f_equal (@length _)) in H. rewrite app_length in H. simpl in H; elimtype False. lia.

    eapply (type_spine_cons Σ Γ t s0 na T). econstructor. 3:eauto.




(* Lemma invert_type_mkApps Σ Γ f u T fty : *)
(*   Σ ;;; Γ |- mkApps f u : T -> *)
(*   isWfArity typing Σ Γ T -> *)
(*   Σ ;;; Γ |- f : fty -> *)
(*   typing_spine Σ Γ fty u T. *)
(* Proof. *)
(*   induction u in f, T |- *; simpl. *)
(*   - intros HT HwfT Hf. constructor. left; auto. eapply cumul_refl'. *)
(*   - intros Hf Hty. *)
(*     specialize (IHu _ _ Hf Hty) as [T' [Hwfa Hf']]. *)
(*     red in Hty. destruct Hty as [ctx [s [Hd Hwf]]]. *)
(*     generalize (PCUICClosed.destArity_spec [] T). rewrite Hd. *)
(*     simpl. intros ->. clear Hd. *)
(*     (* red in Hwfa. destruct Hwfa as [ctx' [s' [Hd' Hwf']]]. *) *)
(*     (* generalize (PCUICClosed.destArity_spec [] T'). rewrite {}Hd'. *) *)
(*     (* simpl. intros ->. *) *)
(*     eapply inversion_App in Hwfa as (fna & fA & fB & Hfp & Hfa & Hf''). *)
(*     exists (tProd fna fA fB). intuition auto. *)
(*     econstructor. 2:eapply cumul_refl'. admit. *)
(*     auto. *)
(*   exists T', U'. split; auto. split; auto. *)
(*   eapply cumul_trans; eauto. *)
(* Qed. *)

Theorem validity :
  env_prop (fun Σ Γ t T => isWfArity_or_Type Σ Γ T).
Proof.

  apply typing_ind_env; intros; rename_all_hyps.

  - destruct (nth_error_All_local_env_over heq_nth_error X) as [HΓ' Hd].
    destruct decl as [na [b|] ty]; cbn -[skipn] in *.
    + eapply isWfArity_or_Type_lift; eauto. clear HΓ'; now apply nth_error_Some_length in heq_nth_error.
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
           simpl. now exists s1.
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
    + rewrite Nat.add_0_r. eapply substitution_alt; eauto. constructor. constructor.
      2: simpl; eauto; now rewrite app_context_assoc in X0.
      now rewrite subst_empty.
    + rewrite Nat.add_0_r. destruct X0 as [u' Hu']. exists u'.
      eapply (substitution_alt _ _ _ _ _ _ (tSort u')); eauto. constructor. constructor.
      2: simpl; eauto; now rewrite app_context_assoc in Hu'.
      now rewrite subst_empty.
    + right.
      destruct i as [u' Hu']. exists u'.
      eapply (substitution0 _ _ na _ _ _ (tSort u')); eauto.
      apply inversion_Prod in Hu' as [na' [s1 [s2 Hs]]]. intuition.
      eapply type_Conv; pcuic.
      eapply (weakening_cumul Σ Γ [] [vass na A]) in b; pcuic.
      simpl in b. eapply cumul_trans. 2:eauto.
      constructor. constructor. simpl. apply leq_universe_product.

  - eapply declared_constant_inv in H; pcuic.
    destruct decl as [ty [b|] univs]. red in H. simpl in *.
    apply isWfArity_or_Type_subst_instance; pcuic.
    repeat red in H; simpl in *.
    apply isWfArity_or_Type_subst_instance; pcuic.
    destruct H.
    (* TODO: Fix Forall_decls_typing same way as local environments *)
    admit.
  - admit.
  - admit.

  - (* Case *)
    right. red.
    destruct X2.
    + destruct i as [ctx [s [Heq Hs]]].
      exists s.
      unfold check_correct_arity in *.
      assert (ctx = pctx). admit. (* WF of cases *)
      subst ctx.
      pose proof (PCUICClosed.destArity_spec [] pty). rewrite Heq in H.
      simpl in H. subst pty.
      assert (#|args| = #|pctx|). admit. (* WF of case *)
      eapply type_mkApps. eauto.
      destruct X4. destruct i as [ctx' [s' [Heq' Hs']]].
      elimtype False.
      { clear -Heq'.
        revert Heq'.
        assert (destArity [] (tInd ind u) = None) by reflexivity.
        revert H.
        generalize (tInd ind u). clear. induction args.
        intros. simpl in Heq'. congruence.
        intros. unshelve eapply (IHargs _ _ Heq').
        reflexivity. }
      destruct i as [si Hi].
      eapply (invert_type_mkApps _ _ (tInd ind u)) in Hi; pcuic.
      2:{ econstructor; eauto. admit. (* universes *) }
      2:{ admit. }
      (* Looks ok *)
      admit.

    + destruct i as [ui Hi]. exists ui.
      admit. (* Same idea *)

  - (* Proj *)
    right.
    admit.

  - admit. (* Fix *)
  - admit. (* CoFix *)

  - (* Conv *)
    destruct X2. red in i. left. exact (projT1 i).
    right. destruct s as [u [Hu _]]. now exists u.
Admitted.


Lemma validity_term {Σ Γ t T} :
  wf Σ -> wf_local Σ Γ -> Σ ;;; Γ |- t : T -> isWfArity_or_Type Σ Γ T.
Proof.
  intros. eapply validity; try eassumption.
Defined.
