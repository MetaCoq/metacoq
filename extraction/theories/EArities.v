
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

Lemma isArity_ind_type:
  forall idecl : one_inductive_body, isArity (ind_type idecl).
Proof.
  intros idecl.
Admitted.                       (* the type of an inductive is an arity *)

Lemma tConstruct_no_Type Σ ind c u x1 : wf Σ ->
  isErasable Σ [] (mkApps (tConstruct ind c u) x1) ->
  Is_proof Σ [] (mkApps (tConstruct ind c u) x1).
Proof.
  intros wfΣ (? & ? & [ | (? & ? & ?)]).
  - exfalso. eapply type_mkApps_inv in t as (? & ? & [] & ?); eauto.
    eapply inversion_Construct in t as (? & ? & ? & ? & ? & ? & ?). destruct x5. destruct p. cbn in *.
    admit.
  - exists x, x0. eauto.
Admitted.                       (* if a constructor is a type or proof, it is a proof *)


Lemma isWfArity_prod_inv:
  forall (Σ : global_context) (Γ : context) (x : name) (x0 x1 : term),
    isWfArity typing Σ Γ (tProd x x0 x1) -> (∑ s : universe, Σ;;; Γ |- x0 : tSort s) ×   isWfArity typing Σ (Γ,, vass x x0) x1
.
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
    (* eapply IHT2 in c0 as (? & ? & ?); eauto. sq. *)

    (* exists (tProd x x0 x2). split; sq; cbn; eauto. *)
    (* etransitivity. eauto. *)
    (* eapply PCUICReduction.red_prod_r. *)

  (*   eapply context_conversion_red. eauto. 2:eauto. *)
  (*   + econstructor. clear; induction Γ. econstructor. destruct a, decl_body. econstructor. eauto. econstructor. econstructor. eauto. econstructor. eauto. econstructor. *)

  (*   econstructor. 2:eauto. 2:econstructor; eauto. 2:cbn. admit. admit. *)
  (* -   admit. *)
Admitted.                       (* invert_cumul_arity_r *)

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

  (*   eapply context_conversion_red. eauto. 2:eauto. *)
  (*   econstructor. eapply conv_context_refl; eauto.  *)

  (*   econstructor. 2:eauto. 2:econstructor; eauto. 2:cbn. admit. admit. *)
  (* - eapply invert_cumul_letin_l in X; eauto. *)
Admitted.                       (* invert_cumul_arity_l *)

Lemma cumul_prop1 Σ Γ A B u :
  wf Σ -> 
  is_prop_sort u -> Σ ;;; Γ |- B : tSort u ->
  Σ ;;; Γ |- A <= B -> Σ ;;; Γ |- A : tSort u.
Proof.
  
Admitted.                       (* cumul_prop1 *)

Lemma cumul_prop2 Σ Γ A B u :
  wf Σ ->
  is_prop_sort u -> Σ ;;; Γ |- A <= B ->
  Σ ;;; Γ |- A : tSort u -> Σ ;;; Γ |- B : tSort u.
Proof.
Admitted.                       (* cumul_prop2 *)

Lemma leq_universe_prop Σ u1 u2 :
  wf Σ ->
  leq_universe (snd Σ) u1 u2 ->
  (is_prop_sort u1 \/ is_prop_sort u2) ->
  (is_prop_sort u1 /\ is_prop_sort u2).
Admitted.

Lemma invert_cumul_prod_r Σ Γ C na A B : wf Σ ->
          Σ ;;; Γ |- C <= tProd na A B ->
            ∑ na' A' B', red Σ Γ C (tProd na' A' B') *
               (Σ ;;; Γ |- A = A') *
               (Σ ;;; Γ,,vass na' A' |- B <= B').
Admitted.

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

Lemma is_prop_sort_sup:
  forall x1 x2 : universe, is_prop_sort (Universe.sup x1 x2) -> is_prop_sort x2.
Proof.
  induction x1; cbn; intros.
  - inv H.
  - inv H.
Qed. 

Lemma Is_type_app (Σ : global_env_ext) Γ t L T :
  wf Σ ->
  wf_local Σ Γ ->
  Σ ;;; Γ |- mkApps t L : T ->
  isErasable Σ Γ t ->
  ∥isErasable Σ Γ (mkApps t L)∥.
Proof.
  intros wfΣ wfΓ ? ?. 
  assert (HW : isWfArity_or_Type Σ Γ T). eapply PCUICValidity.validity; eauto.
  eapply type_mkApps_inv in X as (? & ? & [] & ?); try eassumption.
  destruct X0 as (? & ? & [ | [u]]).
  - eapply PCUICPrincipality.principal_typing in t2 as (? & ? & ? & ?). 2:eauto. 2:exact t0.
    eapply invert_cumul_arity_r in c1; eauto.
    destruct c1 as (? & ? & ?). destruct H as [].
    eapply PCUICCumulativity.red_cumul_inv in X.
    
    eapply invert_cumul_arity_l in H0 as (? & ? & ?). 2:eauto. 2:eauto. 2: eapply cumul_trans; eauto.
    destruct H.
    eapply Prelim.typing_spine_red in t1. 2:{ eapply PCUICCumulativity.All_All2_refl. 
                                                  clear. induction L; eauto. }
    
    2:eauto. 2:eauto. 2: eapply PCUICCumulativity.red_cumul_inv. 2:eauto. 2:eauto.

    Lemma isArity_typing_spine:
      forall (Σ : global_context) (Γ : context) (L : list term) (T x4 : term),
        wf Σ -> wf_local Σ Γ ->
        Is_conv_to_Arity Σ Γ x4 -> typing_spine Σ Γ x4 L T -> Is_conv_to_Arity Σ Γ T.
    Proof.
      intros.  
      depind X1. 
      - destruct H as (? & ? & ?). sq. 
        eapply PCUICCumulativity.red_cumul_inv in X1.
        eapply cumul_trans in c.  2:eassumption.
        eapply invert_cumul_arity_l in c; eauto.
      - eapply IHX1.
        destruct H as (? & ? & ?). sq. 
        eapply PCUICCumulativity.red_cumul_inv in X2.
        eapply cumul_trans in c.  2:eassumption.
        eapply invert_cumul_arity_l in c; eauto. 
        destruct c as (? & ? & ?). sq. 
        eapply invert_red_prod in X3 as (? & ? & [] & ?); eauto; subst.
        exists (x2 {0 := hd}). split; sq. 
        eapply (PCUICSubstitution.substitution_red Σ Γ [_] [] [_]). eauto. econstructor. econstructor. 
        rewrite subst_empty. eassumption. eauto. cbn. eassumption. cbn in H1.

        Lemma isArity_subst:
          forall x2 : term, forall s n, isArity x2 -> isArity (subst s n x2).
        Proof.
          induction x2; cbn in *; try tauto; intros; eauto.
        Qed.
        now eapply isArity_subst.
    Qed.
    assert (t11 := t1).
    eapply isArity_typing_spine in t1 as (? & ? & ?). 2:eauto. 2:eauto. 2:eauto. 
    sq. exists x5. split. eapply type_mkApps. eapply type_reduction in t0; eauto. 2:eauto.
    eapply Prelim.typing_spine_red. eapply PCUICCumulativity.All_All2_refl. 
    clear. induction L; eauto. eauto. eauto. 2:eapply cumul_refl'.
    eapply PCUICCumulativity.red_cumul. eauto. 
    Lemma isWfArity_or_Type_red:
      forall (Σ : global_context) (Γ : context) (T : term), wf Σ -> wf_local Σ Γ ->
        isWfArity_or_Type Σ Γ T -> forall x5 : term, red Σ Γ T x5 -> isWfArity_or_Type Σ Γ x5.
    Proof.
      intros. destruct X1 as [ | []].
      - left. eapply isWfArity_red; eauto.
      - right. eexists. eapply subject_reduction; eauto.
    Qed.
    eapply isWfArity_or_Type_red; eauto. exists x4; split; sq; eauto.
  - destruct p.  
    eapply PCUICPrincipality.principal_typing in t2 as (? & ? & ? & ?). 2:eauto. 2:exact t0.
    eapply cumul_prop1 in c1; eauto.
    eapply cumul_prop2 in c0; eauto.
    econstructor. exists x0. split. eapply type_mkApps. 2:eassumption. eassumption. right.
    Lemma sort_typing_spine:
      forall (Σ : global_context) (Γ : context) (L : list term) (u : universe) (x x0 : term),
        wf Σ ->
        is_prop_sort u ->
        typing_spine Σ Γ x L x0 -> Σ;;; Γ |- x : tSort u -> ∑ u', Σ;;; Γ |- x0 : tSort u' × is_prop_sort u'.
    Proof.
      intros Σ Γ L u x x0 ? ? t1 c0.
      revert u H c0.
      depind t1; intros.
      - eapply cumul_prop2 in c0; eauto.
      - eapply invert_cumul_prod_r in c as (? & ? & ? & [] & ?); eauto.
        eapply subject_reduction in c0. 3:eauto. 2:eauto.
        eapply inversion_Prod in c0 as (? & ? & ? & ? & ?).
        eapply cumul_Sort_inv in c0.
        eapply leq_universe_prop in c0 as []; eauto.
        Lemma is_prop_sort_prod x2 x3 :
          is_prop_sort (Universe.sort_of_product x2 x3) -> is_prop_sort x3.
        Proof.
          intros. unfold Universe.sort_of_product in *. destruct ?; eauto.
          eapply is_prop_sort_sup in H. eauto.
        Qed.

        eapply is_prop_sort_prod in H0. eapply IHt1. exact H0.
        eapply cumul_prop1 in c1. 4:eassumption. all:eauto.
        change (tSort x3) with ((tSort x3) {0 := hd}).
        eapply PCUICSubstitution.substitution0. 2:eauto. eauto. 
        econstructor. eassumption. 2: now destruct c. right; eauto.
    Qed.
    
    eapply sort_typing_spine in t1; eauto.
Qed.

Lemma Is_type_lambda (Σ : global_env_ext) Γ na T1 t :
  wf Σ ->
  wf_local Σ Γ ->
  isErasable Σ Γ (tLambda na T1 t) ->
  ∥isErasable Σ (vass na T1 :: Γ) t∥.
Proof.
  intros ? ? (T & ? & ?).
  eapply inversion_Lambda in t0 as (? & ? & ? & ? & ?).
  destruct s as [ | (u & ? & ?)].
  - eapply invert_cumul_arity_r in c; eauto. destruct c as (? & [] & ?).
    eapply invert_red_prod in X1 as (? & ? & [] & ?); eauto; subst. cbn in H.
    econstructor. exists x3. econstructor. eapply type_reduction; eauto. econstructor; eauto. eexists; eauto.
    eauto.
  - sq. eapply cumul_prop1 in c; eauto.
    eapply inversion_Prod in c as (? & ? & ? & ? & ?).
    eapply cumul_Sort_inv in c.
    eapply leq_universe_prop in c as []; eauto.
    eexists. split. eassumption. right. eexists. split. eassumption.
    unfold Universe.sort_of_product in H.
    destruct ?; eauto. 

    eapply is_prop_sort_sup; eauto.
Qed.

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
