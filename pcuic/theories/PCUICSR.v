(* Distributed under the terms of the MIT license.   *)
From Equations Require Import Equations.
From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import config utils univ.
From PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICWeakeningEnv PCUICWeakening
     PCUICSubstitution PCUICClosed PCUICCumulativity PCUICGeneration PCUICValidity.
Require Import ssreflect ssrbool.
Require Import String.
Require Import LibHypsNaming.
Local Open Scope string_scope.
Set Asymmetric Patterns.

Existing Instance config.default_checker_flags.

(* Commented otherwise extraction would produce an axiom making the whole
   extracted code unusable *)

Ltac my_rename_hyp h th :=
  match th with
    | (typing _ _ ?t _) => fresh "type" t
    | (All_local_env (@typing _) _ ?G) => fresh "wf" G
    | (All_local_env (@typing _) _ _) => fresh "wf"
    | (All_local_env _ _ ?G) => fresh "H" G
    | context [typing _ _ (_ ?t) _] => fresh "IH" t
  end.

Ltac rename_hyp h ht ::= my_rename_hyp h ht.

Derive NoConfusion for term.

Lemma mkApps_Fix_eq mfix idx args t : mkApps (tFix mfix idx) args = t ->
                                      fst (decompose_app t) = (tFix mfix idx).
Proof. intros H; apply (f_equal decompose_app) in H.
       rewrite decompose_app_mkApps in H. reflexivity.
       destruct t; noconf H. rewrite <- H. reflexivity.
       simpl. reflexivity.
Qed.

Inductive context_relation (P : global_context -> context -> context -> context_decl -> context_decl -> Type)
          {Σ} : forall (Γ Γ' : context), Type :=
| ctx_rel_nil : context_relation P nil nil
| ctx_rel_vass na T U Γ Γ' :
    context_relation P Γ Γ' ->
    P Σ Γ Γ' (vass na T) (vass na U) ->
    context_relation P (vass na T :: Γ) (vass na U :: Γ')
| ctx_rel_def na t T u U Γ Γ' :
    context_relation P Γ Γ' ->
    P Σ Γ Γ' (vdef na t T) (vdef na u U) ->
    context_relation P (vdef na t T :: Γ) (vdef na u U :: Γ').

Arguments context_relation P Σ Γ Γ' : clear implicits.

Lemma context_relation_nth {P Σ n Γ Γ' d} :
  context_relation P Σ Γ Γ' -> nth_error Γ n = Some d ->
  { d' & ((nth_error Γ' n = Some d') *
          let Γs := skipn (S n) Γ in
          let Γs' := skipn (S n) Γ' in
          context_relation P Σ Γs Γs' *
          P Σ Γs Γs' d d')%type }.
Proof.
  induction n in Γ, Γ', d |- *; destruct Γ; intros Hrel H; noconf H.
  - depelim Hrel.
    simpl. eexists; intuition eauto.
    eexists; intuition eauto.
  - depelim Hrel.
    destruct (IHn _ _ _ Hrel H).
    cbn -[skipn] in *.
    eexists; intuition eauto.

    destruct (IHn _ _ _ Hrel H).
    eexists; intuition eauto.
Qed.

(* Lemma all_local_env_mix {Σ Γ P Q} : *)
(*   (forall Σ Γ t s s', (P Σ Γ t (tSort s) -> Q Σ Γ t (tSort s)) -> *)
(*                       (P Σ Γ t (tSort s') -> Q Σ Γ t (tSort s'))) -> *)
(*   All_local_env P Σ Γ -> All_local_env Q Σ Γ -> *)
(*   All_local_env (fun Σ Γ t T => (P Σ Γ t T * Q Σ Γ t T)%type) Σ Γ. *)
(* Proof. *)
(*   intros Hsort. induction 1; intros H; depelim H; econstructor; eauto. *)
(* Qed. *)

(* Inductive red1_decls Σ Γ Γ' : forall (x y : context_decl), Type := *)
(* | red1_vass na T T' : red1 Σ Γ T T' -> red1_decls Σ Γ Γ' (vass na T) (vass na T') *)
(* | red1_vdef_type na b T T' : red1 Σ Γ T T' -> red1_decls Σ Γ Γ' (vdef na b T) (vdef na b T') *)
(* | red1_vdef_body na b b' T : red1 Σ Γ b b' -> red1_decls Σ Γ Γ' (vdef na b T) (vdef na b' T). *)

(* Definition red1_context := context_relation red1_decls. *)

Inductive conv_decls Σ Γ Γ' : forall (x y : context_decl), Type :=
| conv_vass na T T' : isType Σ Γ' T' -> conv Σ Γ T T' ->
                      conv_decls Σ Γ Γ' (vass na T) (vass na T')

| conv_vdef_type na b T T' : isType Σ Γ' T' -> conv Σ Γ T T' ->
                             conv_decls Σ Γ Γ' (vdef na b T) (vdef na b T')

| conv_vdef_body na b b' T : Σ ;;; Γ' |- b' : T -> conv Σ Γ b b' -> conv_decls Σ Γ Γ' (vdef na b T) (vdef na b' T).

Notation conv_context := (context_relation conv_decls).
Require Import Equations.Tactics.

(* First needs to show that cumulativity is closed under context conv *)
Lemma wf_conv_context Σ Γ Δ (wfΓ : wf_local Σ Γ) :
  All_local_env_over typing
    (fun (Σ : global_context) (Γ : context) wfΓ (t T : term) Ht =>
       forall Γ' : context, conv_context Σ Γ Γ' -> Σ;;; Γ' |- t : T) Σ Γ wfΓ ->
  conv_context Σ Γ Δ -> wf_local Σ Δ.
Proof.
  intros wfredctx. revert Δ.
  induction wfredctx; intros Δ wfred; depelim wfred; constructor; eauto.
  simpl.
  depelim c. destruct i.
  econstructor; eauto.
  depelim c. simpl. eapply type_Conv; eauto. admit.
  simpl. auto.
Admitted.

Lemma conv_context_refl Σ Γ : wf_local Σ Γ -> conv_context Σ Γ Γ.
Proof.
  induction Γ; try econstructor.
  destruct a as [na [b|] ty]; intros wfΓ; depelim wfΓ; econstructor; eauto;
  constructor; auto. (* Needs validity *)
Admitted.

(* Lemma wf_red1_context Σ Γ Δ : *)
(*   All_local_env *)
(*     (fun (Σ : global_context) (Γ : context) (t T : term) => *)
(*        forall Γ' : context, red1_context Σ Γ Γ' -> Σ;;; Γ' |- t : T) Σ Γ -> *)
(*   red1_context Σ Γ Δ -> wf_local Σ Γ -> wf_local Σ Δ. *)
(* Proof. *)
(*   intros wfredctx. revert Δ. *)
(*   induction wfredctx; intros Δ wfred; depelim wfred; intros wfH; depelim wfH. constructor. *)
(*   econstructor; auto. *)
(*   constructor. eauto. *)
(*   depelim r. specialize (t0 _ wfred). *)
(*   eapply type_Conv. apply t0. admit. *)
(*   econstructor 2. r. *)
(*   specialize (t0 _ wfred). *)

Arguments skipn : simpl never.

(* Admitted. *)
Set SimplIsCbn.
Lemma context_conversion : env_prop
                             (fun Σ Γ t T =>
                                forall Γ', conv_context Σ Γ Γ' -> Σ ;;; Γ' |- t : T).
Proof.
  apply typing_ind_env; intros Σ wfΣ Γ wfΓ; intros **; rename_all_hyps.
  - eapply (context_relation_nth X0) in heq_nth_error as [d' [Hnth [Hrel Hconv]]].
    eapply type_Conv. econstructor; eauto.
    eapply wf_conv_context; eauto.
Admitted.
(*
    depelim Hconv.
    destruct decl; simpl in *.


    induction X0; econstructor; eauto.
    depelim wfΓ. apply (IHX0 wfΓ). depelim HΓ. auto.
    depelim IHn.
    induction HΓ in Γ', X1 |- *. depelim X1. constructor.
    depelim wfΓ. apply IHHΓ; auto. constructor; auto.

    unshelve epose (all_local_env_mix _ wfΓ HΓ).
    simpl. intros.

    induction wfΓ. depelim X0. constructor.
    apply IHwfΓ.

    eapply All_local_env_impl in HΓ. eapply HΓ.
*)

(** The subject reduction property of the system: *)

Definition SR_red1 (Σ : global_context) Γ t T :=
  forall u (Hu : red1 Σ Γ t u), Σ ;;; Γ |- u : T.

Lemma sr_red1 : env_prop SR_red1.
Proof.
  apply typing_ind_env; intros Σ wfΣ Γ wfΓ; unfold SR_red1; intros **; rename_all_hyps;
    match goal with
    | [H : (_ ;;; _ |- _ <= _) |- _ ] => idtac
    | _ =>
      depelim Hu; try (apply mkApps_Fix_eq in x; noconf x);
      try solve [econstructor; eauto]
    end.

  - (* Rel *)
    rewrite heq_nth_error in e. destruct decl as [na b ty]; noconf e.
    simpl.
    pose proof (nth_error_All_local_env_over heq_nth_error X); eauto.
    destruct lookup_wf_local_decl; cbn in *.
    rewrite <- (firstn_skipn (S n) Γ).
    assert(S n = #|firstn (S n) Γ|).
    { rewrite firstn_length_le; auto. apply nth_error_Some_length in heq_nth_error. auto with arith. }
    rewrite {3 4}H. apply weakening; auto.
    now unfold app_context; rewrite firstn_skipn.

  - (* Prod *)
    constructor; eauto.
    eapply (context_conversion _ wfΣ _ _ _ _ typeb).
    constructor. auto. admit.
    constructor. exists s1; auto. apply conv_conv_alt.
    auto.

  - (* Lambda *)
    eapply type_Conv. eapply type_Lambda; eauto.
    eapply (context_conversion _ wfΣ _ _ _ _ typeb).
    constructor. auto. admit.
    constructor. exists s1; auto. apply conv_conv_alt.
    auto. assert (Σ ;;; Γ |- tLambda n t b : tProd n t bty). econstructor; eauto.
    edestruct (validity _ wfΣ _ HΓ _ _ X0). apply i.
    admit.

  - (* LetIn *)
    s
    eapply type_Conv. epose (substitution _ Γ ([vdef n b b_ty]) [] [] _ _ wfΣ _ typeb').

Admitted.


Definition sr_stmt (Σ : global_context) Γ t T :=
  forall u, red Σ Γ t u -> Σ ;;; Γ |- u : T.

Corollary subject_reduction : forall (Σ : global_context) Γ t u T,
    Σ ;;; Γ |- t : T -> red Σ Γ t u -> Σ ;;; Γ |- u : T.



(** Weak Normalization: every term has a normal form *)

Definition normal (Σ : global_context) Γ t := ~ exists u, red1 Σ Γ t u.

Conjecture weak_normalization : forall (Σ : global_context) Γ t T,
    Σ ;;; Γ |- t : T -> exists u, red Σ Γ t u /\ normal Σ Γ u.
