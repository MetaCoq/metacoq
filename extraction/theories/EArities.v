
From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From MetaCoq.Template Require Import config utils monad_utils BasicAst AstUtils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICTyping PCUICMetaTheory PCUICWcbvEval PCUICLiftSubst PCUICInversion PCUICSR PCUICNormal PCUICSafeReduce PCUICSafeLemmata PCUICSafeChecker PCUICPrincipality PCUICGeneration.
From MetaCoq.Extraction Require EAst ELiftSubst ETyping EWcbvEval Extract Prelim.
From Equations Require Import Equations.
Require Import String.
Local Open Scope string_scope.
Set Asymmetric Patterns.
Import MonadNotation.



(* Instance extraction_checker_flags : checker_flags := Build_checker_flags true false false. *)

Definition is_prop_sort s :=
  match Universe.level s with
  | Some l => Level.is_prop l
  | None => false
  end.

Require Import Extract.

Definition Is_conv_to_Arity Σ Γ T := exists T', ∥red Σ Γ T T'∥ /\ isArity T'.

Ltac terror := try match goal with [t : type_error |- typing_result _] => exact (TypeError t) end.
           
Lemma constructors_typed:
  forall (Σ : list global_decl) (univs : constraints) (k : kername)
    (m : mutual_inductive_body) (x : one_inductive_body) (t1 : term) 
    (i0 : ident) (n0 : nat),
    In (i0, t1, n0) (ind_ctors x) ->
    on_inductive (fun Σ0 : global_context => lift_typing typing Σ0) (Σ, univs) k m ->
    ∑ T, (Σ, univs);;; arities_context (ind_bodies m) |- t1 : T.
Proof.
  intros Σ univs k m x t1 i0 n0 H2 X0.
Admitted.

Lemma proj_typed:
  forall (Σ : list global_decl) (univs : constraints) (k : kername)
    (m : mutual_inductive_body) (x : one_inductive_body) (t1 : term) 
    (i0 : ident) (H2 : In (i0, t1) (ind_projs x))
    (X0 : on_inductive (fun Σ0 : global_context => lift_typing typing Σ0) (Σ, univs) k m),
    ∑ T, (Σ, univs);;; [] |- t1 : T.
Proof.
  
Admitted.

Lemma context_conversion_red Σ Γ Γ' s t : wf Σ -> 
  PCUICSR.conv_context Σ Γ Γ' -> red Σ Γ s t -> red Σ Γ' s t.
Admitted.

Lemma invert_cumul_arity_r (Σ : global_context) (Γ : context) (C : term) T :
  wf Σ -> wf_local Σ Γ ->
  isArity T ->
  Σ;;; Γ |- C <= T -> Is_conv_to_Arity Σ Γ C.
Proof.
  intros wfΣ.
  revert Γ C; induction T; cbn in *; intros Γ C wfΓ ? ?; try tauto.
  - eapply invert_cumul_sort_r in X as (? & ? & ?).
    exists (tSort x). split; sq; eauto.
  - eapply invert_cumul_prod_r in X as (? & ? & ? & [] & ?); eauto.
    eapply IHT2 in c0 as (? & ? & ?); eauto. sq.

    exists (tProd x x0 x2). split; sq; cbn; eauto.
    etransitivity. eauto.
    eapply PCUICReduction.red_prod_r.

    eapply context_conversion_red. eauto. 2:eauto.
    econstructor. eapply conv_context_refl; eauto. 

    econstructor. 2:eauto. 2:econstructor; eauto. 2:cbn. admit. admit.
  -   admit.
Admitted.

Lemma invert_cumul_arity_l (Σ : global_context) (Γ : context) (C : term) T :
  wf Σ -> wf_local Σ Γ ->
  isArity C -> 
  Σ;;; Γ |- C <= T -> Is_conv_to_Arity Σ Γ T.
Proof.
  intros wfΣ.
  revert Γ T; induction C; cbn in *; intros Γ T wfΓ ? ?; try tauto.
  - eapply invert_cumul_sort_l in X as (? & ? & ?).
    exists (tSort x). split; sq; eauto.
  - eapply invert_cumul_prod_l in X as (? & ? & ? & [] & ?); eauto.
    eapply IHC2 in c0 as (? & ? & ?); eauto. sq.

    exists (tProd x x0 x2). split; sq; cbn; eauto.
    etransitivity. eauto.
    eapply PCUICReduction.red_prod_r.

    eapply context_conversion_red. eauto. 2:eauto.
    econstructor. eapply conv_context_refl; eauto. 

    econstructor. 2:eauto. 2:econstructor; eauto. 2:cbn. admit. admit.
  - eapply invert_cumul_letin_l in X; eauto.
Admitted.

Lemma isWfArity_prod_inv:
  forall (Σ : global_context) (Γ : context) (T : term) (x : name) (x0 x1 : term),
    isWfArity typing Σ Γ (tProd x x0 x1) -> (∑ s : universe, Σ;;; Γ |- x0 : tSort s) ×   isWfArity typing Σ (Γ,, vass x x0) x1
.
Proof.
  
           
           (* destruct X as (? & ? & ? & ?). cbn in e. *)
           (* change (Γ ,, vass x x0) with (Γ ,,, [vass x x0]). unfold ",," in e. *)
           (* revert e. *)
           (* generalize ([vass x x0]). intros. *)
           (* induction x1 in l, e |- *; cbn in *; try now inv e. *)
           (* ++ inv e. repeat econstructor. cbn. eauto. *)
           (* ++ eapply IHx1_2 in e as (? & ? & ? & ?). *)
           (*    repeat econstructor. cbn. admit. admit. (* destArity stuff *) *)
           (* ++ eapply IHx1_3 in e as (? & ? & ? & ?). *)
           (*    repeat econstructor. cbn. admit. admit. (* destArity stuff *) *)
  
Admitted.

Lemma arity_type_inv Σ Γ t T1 T2 : wf Σ -> wf_local Σ Γ ->
  Σ ;;; Γ |- t : T1 -> isArity T1 -> Σ ;;; Γ |- t : T2 -> Is_conv_to_Arity Σ Γ T2.
Proof.
  intros wfΣ wfΓ. intros. eapply principal_typing in X as (? & ? & ? & ?). 2:eauto. 2:exact X0.


  eapply invert_cumul_arity_r in c0 as (? & ? & ?); eauto. sq.
  eapply PCUICCumulativity.red_cumul_inv in X.
  eapply cumul_trans in c; eauto.  
  
  eapply invert_cumul_arity_l in c as (? & ? & ?); eauto. sq.
  exists x1; split; sq; eauto.
Qed.

Lemma cumul_kind1 Σ Γ A B u :
  wf Σ -> 
  is_prop_sort u -> Σ ;;; Γ |- B : tSort u ->
  Σ ;;; Γ |- A <= B -> Σ ;;; Γ |- A : tSort u.
Proof.
  
Admitted.

Lemma cumul_kind2 Σ Γ A B u :
  wf Σ ->
  is_prop_sort u -> Σ ;;; Γ |- A <= B ->
  Σ ;;; Γ |- A : tSort u -> Σ ;;; Γ |- B : tSort u.
Proof.
Admitted.

Lemma leq_universe_prop Σ u1 u2 :
  wf Σ ->
  leq_universe (snd Σ) u1 u2 ->
  (is_prop_sort u1 \/ is_prop_sort u2) ->
  (is_prop_sort u1 /\ is_prop_sort u2).
Admitted.

Lemma Is_type_app Σ Γ t L T :
  wf Σ ->
  Σ ;;; Γ |- mkApps t L : T ->
  Is_Type_or_Proof Σ Γ t ->
  Is_Type_or_Proof Σ Γ (mkApps t L).
Proof.
  intros. eapply type_mkApps_inv in X0 as (? & ? & [] & ?); try eassumption.
  destruct X1 as (? & ? & [ | [u]]).
  - eapply PCUICPrincipality.principal_typing in t2 as (? & ? & ? & ?). 2:eauto. 2:exact t0.
    


  (*   Lemma typing_spine_change : *)
  (*     forall (Σ : global_context) (Γ : context) (t : term) (L : list term) (x1 : term), *)
  (*       Σ;;; Γ |- t : x1 -> forall x x0 : term, Σ;;; Γ |- t : x -> typing_spine Σ Γ x L x0 -> typing_spine Σ Γ x1 L x0. *)
  (*   Proof. *)
  (*     intros Σ Γ t L x1 t2 x x0 t0 t1. *)
  (*   Admitted. *)
  (*   eapply typing_spine_change in t1. 3:eapply t0. 2:eapply t2. clear t0. *)
  (*   revert t t2. *)
  (*   dependent induction t1; intros. *)
  (*   + cbn. exists ty. split; eauto. *)
  (*   + cbn. eapply IHt1. admit. *)
  (*     eauto. eauto. *)
  (* - destruct p. *)
Admitted.

Lemma Is_type_lambda Σ Γ na T1 t :
  wf Σ ->
  Is_Type_or_Proof Σ Γ (tLambda na T1 t) ->
  Is_Type_or_Proof Σ (vass na T1 :: Γ) t.
Proof.
  intros ? (T & ? & ?).
  eapply inversion_Lambda in t0 as (? & ? & ? & ? & ?).
  exists x0. split; eauto. destruct s as [ | (u & ? & ?)].
  - left. admit.
  - right. exists u. split; eauto.
Admitted.

Lemma Is_type_red Σ Γ t v:
  wf Σ ->
  red Σ Γ t v ->
  Is_Type_or_Proof Σ Γ t ->
  Is_Type_or_Proof Σ Γ v.
Proof.
  intros ? ? (T & ? & ?).
  exists T. split.
  - eapply subject_reduction; eauto.
  - eauto.
Qed.

Lemma Is_type_eval Σ Γ t v:
  wf Σ ->
  eval Σ Γ t v ->
  Is_Type_or_Proof Σ Γ t ->
  Is_Type_or_Proof Σ Γ v.
Proof.
  intros; eapply Is_type_red. eauto.
  eapply wcbeval_red; eauto. eauto.
Qed.


Lemma isArity_ind_type:
  forall idecl : one_inductive_body, isArity (ind_type idecl).
Proof.
  intros idecl.
Admitted.

Lemma tConstruct_no_Type Σ ind c u x1 : wf Σ ->
  Is_Type_or_Proof Σ [] (mkApps (tConstruct ind c u) x1) ->
  Is_proof Σ [] (mkApps (tConstruct ind c u) x1).
Proof.
  intros wfΣ (? & ? & [ | (? & ? & ?)]).
  - exfalso. eapply type_mkApps_inv in t as (? & ? & [] & ?); eauto.
    eapply inversion_Construct in t as (? & ? & ? & ? & ? & ? & ?). destruct x5. destruct p. cbn in *.
    admit.
  - exists x, x0. eauto.
Admitted.

