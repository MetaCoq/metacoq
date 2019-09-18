From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From MetaCoq Require Import config utils Ast AstUtils Induction LiftSubst Typing WeakSubst.

Arguments All_local_env typing%type_scope {H} Σ Γ.

Definition on_local_decl P Σ d :=
  match d.(decl_body) with
  | None => {s : universe & { Γ' & isType Σ Γ' d.(decl_type)
  | Some body => Σ ;;; Γ |- body : d.(decl_type)
  end.


Lemma All_local_env_lookup `{checker_flags} P Q Σ Γ n (isdecl : n < #|Γ|) :
  All_local_env P Σ Γ -> on_decl_typing P (safe_nth Γ (exist _ n isdecl))
Proof.
  induction 1. constructor.
  intros. inv X0; auto. econstructor; auto.
  split; eauto.

Lemma type_local_env_isdecl `{checker_flags} Σ n Γ :
  forall isdecl : n < #|Γ|, wf_local Σ Γ ->
  { Γ' : _ & { Γ'' : _ &
                    { _ : type_local_decl Σ Γ'' (safe_nth Γ (exist _ n isdecl)) &
                    Γ = (Γ' ++ Γ'')%list /\ #|Γ'| = S n } } }.
Proof. Admitted.

Definition isSort T :=
  match T with
  | tSort _ => true
  | _ => false
  end.

Theorem validity `{checker_flags} : env_prop (fun Σ Γ t T => ((isSort T = true) + isType Σ Γ T)%type).
Proof.
  apply typing_ind_env; intros.

  - pose proof wfΓ as H0.
    apply (type_local_env_isdecl _ _ _ isdecl) in H0 as [Γ' [Γ'' [H0 [-> <-]]]].
    destruct safe_nth. simpl in *.
    red in H0. simpl in H0. destruct decl_body.
    Lemma All_local_env_decl

    admit.
    destruct H0. right; exists x.
    now refine (weakening _ _ _ _ _ _ _ t).

  - left; reflexivity.
  - right; now exists s.
  - left; reflexivity.
  - right. econstructor. constructor; eauto.
    destruct X2.
    destruct H2 as [s Hs]. constructor. auto. 
    eexists. eauto.
    (* Aha: need alpha-conv on local assumptions... *)
    admit.

  - admit.
  - admit.
  - (* Easy now *)
Admitted.

Eval compute in validity.
