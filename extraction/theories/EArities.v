
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
  forall (Σ : global_env_ext) (k : kername)
    (m : mutual_inductive_body) (x : one_inductive_body) (t1 : term) 
    (i0 : ident) (n0 : nat),
    In (i0, t1, n0) (ind_ctors x) ->
    on_inductive (fun Σ0 : global_env_ext => lift_typing typing Σ0) Σ k m ->
    ∑ T, Σ;;; arities_context (ind_bodies m) |- t1 : T.
Proof.
  intros Σ k m x t1 i0 n0 H2 X0.
Admitted.                       (* constructors have a type *)

(* Lemma proj_typed: *)
(*   forall (Σ : list global_decl) (univs : constraints) (k : kername) *)
(*     (m : mutual_inductive_body) (x : one_inductive_body) (t1 : term)  *)
(*     (i0 : ident) (H2 : In (i0, t1) (ind_projs x)) *)
(*     (X0 : on_inductive (fun Σ0 : global_env_ext => lift_typing typing Σ0) (Σ, univs) k m), *)
(*     ∑ T, (Σ, univs);;; [] |- t1 : T. *)
(* Proof. *)
  
(* Admitted. (* projections have a type *) *)

Inductive conv_decls Σ Γ (Γ' : context) : forall (x y : context_decl), Type :=
| conv_vass : forall (na na' : name) (T T' : term),
                (* isWfArity_or_Type Σ Γ' T' -> *)
                Σ;;; Γ |- T = T' -> conv_decls Σ Γ Γ' (vass na T) (vass na' T')
| conv_vdef_type : forall (na : name) (b T  : term),
    (* isWfArity_or_Type Σ Γ' T -> *)
    conv_decls Σ Γ Γ' (vdef na b T) (vdef na b T).

Lemma conv_context_refl Σ Γ : wf Σ -> wf_local Σ Γ -> context_relation conv_decls Σ Γ Γ.
Proof.
  induction Γ; try econstructor. 
  intros wfΣ wfΓ; depelim wfΓ; econstructor; eauto;
  constructor; auto.
  - apply conv_refl.
Qed.

Lemma context_conversion_red1 Σ Γ Γ' s t : wf Σ -> (* Σ ;;; Γ' |- t : T -> *)
   context_relation conv_decls Σ Γ Γ' -> red1 Σ Γ s t -> red Σ Γ' s t.
Proof.
  intros HΣ HT X0. induction X0 using red1_ind_all in Γ', HΣ, HT |- *; eauto.
  Hint Constructors red red1.
  all:eauto.
  - econstructor. econstructor. econstructor.
    rewrite <- H. 
    induction HT in i |- *; destruct i; eauto.
    now inv p. 
  - 
    eapply PCUICReduction.red_abs. eapply IHX0; eauto.  eauto.
  - 
    eapply PCUICReduction.red_abs. eauto. eapply IHX0. eauto. 
    eauto. econstructor. eauto. econstructor. eapply conv_refl. 
  - 
    eapply PCUICReduction.red_letin. eapply IHX0; eauto. 
    all:eauto. 
  - 
    eapply PCUICReduction.red_letin; eauto. 
  - 
    eapply PCUICReduction.red_letin; eauto. eapply IHX0; eauto. 
    econstructor. eauto. econstructor. 
  -     eapply PCUICReduction.reds_case; eauto. clear.
    eapply PCUICCumulativity.All_All2_refl. induction brs; eauto.
  -     eapply PCUICReduction.reds_case; eauto. clear.
    eapply PCUICCumulativity.All_All2_refl. induction brs; eauto.
  - destruct ind. 
    eapply PCUICReduction.reds_case; eauto. 
    clear - HΣ X HT.
    induction X.
    + econstructor. destruct p. destruct p.
      split; eauto. 
      eapply PCUICCumulativity.All_All2_refl. 
      induction tl; eauto. 
    + econstructor.  repeat econstructor.
      eassumption.
  - 
    eapply PCUICReduction.red_proj_c. eauto.
  - 
    eapply PCUICReduction.red_app; eauto.
  -     eapply PCUICReduction.red_app; eauto.
  - 
    eapply PCUICReduction.red_prod; eauto.
  - 
    eapply PCUICReduction.red_prod; eauto. eapply IHX0. eauto. eauto. 
    econstructor. 
    eauto. econstructor. eapply conv_refl.
  - eapply PCUICReduction.red_evar; eauto.
    induction X; eauto. econstructor. eapply p; eauto.
    induction tl; eauto.
  - 
    eapply PCUICReduction.red_fix_congr; eauto.
    generalize (fix_context mfix0). intros.
    induction X; eauto. 
    destruct p. destruct p.
    econstructor; eauto. split. inv e. eapply r0; eauto. 
    inv e. econstructor. clear.
    eapply PCUICCumulativity.All_All2_refl. induction tl; eauto.
  - 
    eapply PCUICReduction.red_fix_congr; eauto. 
    remember (fix_context mfix0). intros. clear Heqc.
    induction X in  |- *; eauto.
    destruct p. destruct p.
    econstructor; eauto. split. inv e. econstructor. eapply r0. eauto.
    inv e. eauto.
    * clear - HT. induction c. eassumption. cbn. destruct a.
      destruct decl_body. econstructor. eassumption. econstructor.
      econstructor.  eauto. econstructor. eapply conv_refl.
    * clear.
      eapply PCUICCumulativity.All_All2_refl. induction tl; eauto.
  - eapply PCUICReduction.red_cofix_congr; eauto.
    generalize (fix_context mfix0). intros.
    induction X; eauto.
    destruct p. destruct p.
    econstructor; eauto. split. eapply r0. eauto.
    inv e. eauto. inv e. econstructor.
    clear.
    eapply PCUICCumulativity.All_All2_refl. induction tl; eauto.
  - eapply PCUICReduction.red_cofix_congr; eauto. 
    remember (fix_context mfix0). intros. clear Heqc.
    induction X in  |- *; eauto.
    destruct p. destruct p.
    econstructor; eauto. split. inv e. econstructor. eapply r0. eauto.
    inv e. eauto.
    * clear - HT. induction c. eassumption. cbn. destruct a.
      destruct decl_body. econstructor. eassumption. econstructor.
      econstructor.  eauto. econstructor. eapply conv_refl.
    * clear.
      eapply PCUICCumulativity.All_All2_refl. induction tl; eauto.
Qed.

Lemma context_conversion_red Σ Γ Γ' s t : wf Σ -> 
  context_relation conv_decls Σ Γ Γ' -> red Σ Γ s t -> red Σ Γ' s t.
Proof.
  intros. induction X1; eauto. 
  etransitivity. eapply IHX1.
  eapply context_conversion_red1; eauto.
Qed.

Lemma invert_cumul_arity_r (Σ : global_env_ext) (Γ : context) (C : term) T :
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

  (*   eapply context_conversion_red. eauto. 2:eauto. *)
  (*   + econstructor. clear; induction Γ. econstructor. destruct a, decl_body. econstructor. eauto. econstructor. econstructor. eauto. econstructor. eauto. econstructor. *)

  (*   econstructor. 2:eauto. 2:econstructor; eauto. 2:cbn. admit. admit. *)
  (* -   admit. *)
Admitted.                       (* invert_cumul_arity_r *)

Lemma invert_cumul_arity_l (Σ : global_env_ext) (Γ : context) (C : term) T :
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

  (*   eapply context_conversion_red. eauto. 2:eauto. *)
  (*   econstructor. eapply conv_context_refl; eauto.  *)

  (*   econstructor. 2:eauto. 2:econstructor; eauto. 2:cbn. admit. admit. *)
  (* - eapply invert_cumul_letin_l in X; eauto. *)
Admitted.                       (* invert_cumul_arity_l *)

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

Lemma cumul_prop1 (Σ : global_env_ext) Γ A B u :
  wf Σ -> 
  is_prop_sort u -> Σ ;;; Γ |- B : tSort u ->
  Σ ;;; Γ |- A <= B -> Σ ;;; Γ |- A : tSort u.
Proof.
  
Admitted.                       (* cumul_prop1 *)

Lemma cumul_prop2 (Σ : global_env_ext) Γ A B u :
  wf Σ ->
  is_prop_sort u -> Σ ;;; Γ |- A <= B ->
  Σ ;;; Γ |- A : tSort u -> Σ ;;; Γ |- B : tSort u.
Proof.
Admitted.                       (* cumul_prop2 *)

Lemma leq_universe_prop (Σ : global_env_ext) u1 u2 :
  wf Σ ->
  leq_universe (global_ext_constraints Σ) u1 u2 ->
  (is_prop_sort u1 \/ is_prop_sort u2) ->
  (is_prop_sort u1 /\ is_prop_sort u2).
Admitted.

Lemma Is_type_app (Σ : global_env_ext) Γ t L T :
  wf Σ ->
  Σ ;;; Γ |- mkApps t L : T ->
  isErasable Σ Γ t ->
  isErasable Σ Γ (mkApps t L).
Proof.
  intros. eapply type_mkApps_inv in X0 as (? & ? & [] & ?); try eassumption.
  destruct X1 as (? & ? & [ | [u]]).
  - eapply PCUICPrincipality.principal_typing in t2 as (? & ? & ? & ?). 2:eauto. 2:exact t0.
    


  (*   Lemma typing_spine_change : *)
  (*     forall (Σ : global_env_ext) (Γ : context) (t : term) (L : list term) (x1 : term), *)
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
Admitted.                       (* Is_type_app *)

Lemma Is_type_lambda (Σ : global_env_ext) Γ na T1 t :
  wf Σ ->
  isErasable Σ Γ (tLambda na T1 t) ->
  isErasable Σ (vass na T1 :: Γ) t.
Proof.
  intros ? (T & ? & ?).
  eapply inversion_Lambda in t0 as (? & ? & ? & ? & ?).
  exists x0. split; eauto. destruct s as [ | (u & ? & ?)].
  - left. admit.
  - right. exists u. split; eauto.
Admitted.                       (* Is_type_lambda *)

Lemma Is_type_red (Σ : global_env_ext) Γ t v:
  wf Σ ->
  red Σ Γ t v ->
  isErasable Σ Γ t ->
  isErasable Σ Γ v.
Proof.
  intros ? ? (T & ? & ?).
  exists T. split.
  - eapply subject_reduction; eauto.
  - eauto.
Qed.

Lemma Is_type_eval (Σ : global_env_ext) Γ t v:
  wf Σ ->
  eval Σ Γ t v ->
  isErasable Σ Γ t ->
  isErasable Σ Γ v.
Proof.
  intros; eapply Is_type_red. eauto.
  eapply wcbeval_red; eauto. eauto.
Qed.


Lemma isArity_ind_type:
  forall idecl : one_inductive_body, isArity (ind_type idecl).
Proof.
  intros idecl.
Admitted.                       (* the type of an inductive is an arity *)


Lemma tConstruct_no_Type (Σ : global_env_ext) ind c u x1 : wf Σ ->
  isErasable Σ [] (mkApps (tConstruct ind c u) x1) ->
  Is_proof Σ [] (mkApps (tConstruct ind c u) x1).
Proof.
  intros wfΣ (? & ? & [ | (? & ? & ?)]).
  - exfalso. eapply type_mkApps_inv in t as (? & ? & [] & ?); eauto.
    eapply inversion_Construct in t as (? & ? & ? & ? & ? & ? & ?). destruct x5. destruct p. cbn in *.
    admit.
  - exists x, x0. eauto.
Admitted.                       (* if a constructor is a type or proof, it is a proof *)

