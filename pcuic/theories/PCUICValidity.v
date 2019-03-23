From Equations Require Import Equations.
From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import utils.
From PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICLiftSubst PCUICTyping. (* PCUICWeakening. *)
Require Import ssreflect.
Existing Instance config.default_checker_flags.

Definition isWfArity_or_Type Σ Γ T : Type := (isWfArity typing Σ Γ T + isType Σ Γ T).

(* Definition isWfArity Σ (Γ : context) T := *)
(*   forall ctx s, destArity [] T = Some (ctx, s) -> All_local_env (lift_typing typing) Σ (Γ ,,, ctx). *)

Lemma isWfArity_or_Type_lift Σ n Γ ty : isWfArity_or_Type Σ (skipn n Γ) ty -> isWfArity_or_Type Σ Γ (lift0 n ty).
Proof.
  intros [|]. red in i. left. intros ctx s Heq.
  (* Needs weakening lemmas *) admit.
  destruct i as [u Hu].
  right. exists u. admit. (* Weakening *)
Admitted.

 (* Require Import LibHypsNaming. *)
Theorem validity :
  env_prop (fun Σ Γ t T => isWfArity_or_Type Σ Γ T).
Proof.
  apply typing_ind_env; intros; rename_all_hyps.

  - destruct (nth_error_All_local_env_over heq_nth_error X) as [HΓ' Hd].
    destruct decl as [na [b|] ty]; cbn -[skipn] in *.
    now apply isWfArity_or_Type_lift.
    destruct lookup_wf_local_decl; cbn -[skipn] in *.
    destruct o. right. exists x0. admit. (* Weakening *)

  - left. intros ctx s. simpl. intros [= <- <-]. apply HΓ.
  - left. intros ctx s. intros [= <- <-]. apply HΓ.
  - destruct X3. left. intros ctx s. simpl. intros.
    apply All_local_env_app_inv; split; auto.
    specialize (i ctx s). forward i.


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
