From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import config utils Ast AstUtils Induction LiftSubst Typing WeakSubst.

Lemma type_local_env_isdecl Σ n Γ :
  forall isdecl : n < #|Γ|, type_local_env Σ Γ ->
  { Γ' : _ & { Γ'' : _ &
                    { _ : type_local_decl Σ Γ'' (safe_nth Γ (exist _ n isdecl)) &
                    Γ = Γ' ++ Γ'' /\ #|Γ'| = S n } } }.
Proof. Admitted.
         
Theorem validity : env_prop (fun Σ Γ t T => type_local_env Σ Γ ->
                                            isType Σ Γ T).
Proof.
  apply typing_ind_env; intros.

  - pose proof H as H0.
    apply (type_local_env_isdecl _ _ _ isdecl) in H0 as [Γ' [Γ'' [H0 [-> <-]]]].
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
