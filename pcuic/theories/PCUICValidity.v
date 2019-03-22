From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import utils.
From PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICLiftSubst PCUICTyping PCUICWeakening.
Existing Instance config.default_checker_flags.
Lemma type_local_env_isdecl Σ n Γ :
  forall isdecl : n < #|Γ|, All_local_env typing Σ Γ ->
  { Γ' : _ & { Γ'' : _ &
                    { _ : type_local_decl Σ Γ'' (safe_nth Γ (exist _ n isdecl)) &
                    Γ = Γ' ++ Γ'' /\ #|Γ'| = S n } } }.
Proof. Admitted.

Theorem validity : env_prop (fun Σ Γ t T => wf_local Σ Γ -> isType_or_Sort Σ Γ T).
Proof.
  apply typing_ind_env; intros.

  - pose proof H as H0.
    eapply (All_local_env_lookup X) in H.
    red in H |- *. destruct decl as [na [b|] ty]. cbn -[skipn] in *.
    forward H by auto with wf.
    destruct H. left; destruct ty; simpl in i; depelim i. exact I.
    right. destruct i as [u Hu].
    exists u.



    apply (type_local_env_isdecl _ _ _ H0) in X0. as [Γ' [Γ'' [H0 [-> <-]]]].
    destruct safe_nth. simpl in *.
    red in H0. simpl in H0. destruct decl_body. admit.
    destruct H0. exists x. 
    now refine (weakening _ _ _ _ _ _ _ t). 

  - exists (succ_sort (succ_sort s)). constructor.
  - now exists s.
  - eexists. constructor.
  - econstructor. constructor; eauto.
    destruct H2 as [s Hs]. constructor. auto. 
    eexists. eauto.
    (* Aha: need alpha-conv on local assumptions... *)
    admit.

  - admit.
  - admit.
  - (* Easy now *)
Admitted.

Eval compute in validity.
