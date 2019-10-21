From Coq Require Import Bool String List Program BinPos Compare_dec PeanoNat Lia.
From MetaCoq.Template Require Import config utils UnivSubst.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICTyping PCUICWeakeningEnv PCUICWeakening PCUICInversion
     PCUICSubstitution PCUICReduction PCUICCumulativity PCUICGeneration
     PCUICParallelReductionConfluence PCUICConfluence PCUICUnivSubst
     PCUICUnivSubstitution PCUICConversion PCUICPrincipality.

From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.
Require Import ssreflect.

Derive NoConfusion for term.
Derive Signature for typing cumul.

Section Validity.
  Context `{cf : config.checker_flags}.

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

  Hint Extern 10 (isWfArity _ _ _ (tSort _)) => apply isWfArity_sort : pcuic.

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

  Theorem validity :
    env_prop (fun Σ Γ t T => isWfArity_or_Type Σ Γ T).
  Admitted.

End Validity.

Lemma validity_term {cf:checker_flags} {Σ Γ t T} :
  wf Σ.1 -> wf_local Σ Γ -> Σ ;;; Γ |- t : T -> isWfArity_or_Type Σ Γ T.
Proof.
  intros. eapply validity; try eassumption.
Defined.

Corollary validity' :
  forall `{checker_flags} {Σ Γ t T},
    wf Σ.1 ->
    Σ ;;; Γ |- t : T ->
    isWfArity_or_Type Σ Γ T.
Proof.
  intros cf Σ Γ t T hΣ h.
  eapply validity_term ; eauto.
  eapply typing_wf_local. eassumption.
Qed.