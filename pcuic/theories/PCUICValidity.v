From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import utils.
From PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICLiftSubst PCUICTyping. (* PCUICWeakening. *)
Require Import ssreflect.
Existing Instance config.default_checker_flags.
Lemma type_local_env_isdecl Σ n Γ :
  forall isdecl : n < #|Γ|, All_local_env (lift_typing typing) Σ Γ ->
  { Γ' : _ & { Γ'' : _ &
                    { _ : type_local_decl Σ Γ'' (safe_nth Γ (exist _ n isdecl)) &
                    Γ = Γ' ++ Γ'' /\ #|Γ'| = S n } } }.
Proof. Admitted.

Definition property :=
  forall (Σ : global_context) (Γ : context),
    All_local_env (lift_typing typing) Σ Γ -> forall t T : term, typing Σ Γ t T -> Type.

(* Definition lookup_wf_local Σ Γ (wfΓ : wf_local Σ Γ) (n : nat | n < #|Γ|) : *)
(*   { wf : wf_local Σ (skipn (S n) Γ) & *)

(*          let decl := safe_nth Γ n in *)
(*          typing Σ (skipn (S n) Γ) *)
(*          Q \Sigma \Gamma *)



(* Definition on_wf_local_decl Σ Γ (wfΓ : wf_local Σ Γ) (P : property) d := *)
(*   match d.(decl_body) with *)
(*   | Some b => Q Σ Γ b (Some d.(decl_type)) *)
(*   | None => P Σ Γ d.(decl_type) None *)
(*   end. *)

(* Lemma nth_error_All_local_env_over {P Q Σ Γ n} (isdecl : n < #|Γ|) (wfΓ : All_local_env P Σ Γ) : *)
(*   All_local_env_over P Q Σ Γ wfΓ -> *)
(*   on_some (on_local_decl (fun Σ Γ t T => P Σ (skipn (S n) Γ)) (nth_error Γ n)). *)
(* Proof. *)
(*   induction 1 in n, isdecl |- *. red; simpl. *)
(*   - destruct n; simpl; inv isdecl. *)
(*   - destruct n. red; simpl. red. simpl. apply t0. *)
(*     simpl. apply IHX. simpl in isdecl. lia. *)
(*   - destruct n. auto. *)
(*     apply IHX. simpl in *. lia. *)
(* Qed. *)

(* Require Import LibHypsNaming. *)
From Equations Require Import Equations.
Theorem validity :
  env_prop (fun Σ Γ t T => isType_or_Sort Σ Γ T).
Proof.
  apply typing_ind_env; intros; rename_all_hyps.

  - induction X. destruct n; discriminate.
    simpl in *. destruct tu as [u Hu]. simpl in *.
    destruct n. simpl in *. noconf heq_nth_error.
    simpl. red. right. exists u. admit.


    destruct decl as [na' [b|] ty].
    destruct decl as [na [b|] ty]; cbn -[skipn] in *.
    + destruct Hd as [Hty|[u Hu]].
      ++ left; destruct ty; simpl in *; now destruct Hty.
      ++ right. exists u.
         (* epose proof (weakening _ _ (firstn (S n) Γ) _ _ _ _ Hu) as Hw. *)
         (* rewrite [_ ,,, _]firstn_skipn in Hw. *)
         (* rewrite firstn_length_le in Hw. apply nth_error_Some_length in heq_nth_error. auto with arith. *)
         (* apply Hw. *) admit.
    + simpl in *. destruct Hd as [u [Hs|Hty]].

    pose proof (All_local_env_lookup HΓ0 heq_nth_error) as Hd.
    red in Hd |- *. destruct decl as [na [b|] ty]; cbn -[skipn] in *.
    + destruct Hd as [Hty|[u Hu]].
      ++ left; destruct ty; simpl in *; now destruct Hty.
      ++ right. exists u.
         (* epose proof (weakening _ _ (firstn (S n) Γ) _ _ _ _ Hu) as Hw. *)
         (* rewrite [_ ,,, _]firstn_skipn in Hw. *)
         (* rewrite firstn_length_le in Hw. apply nth_error_Some_length in heq_nth_error. auto with arith. *)
         (* apply Hw. *) admit.
    + simpl in *. destruct Hd as [u [Hs|Hty]].


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
