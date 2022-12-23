(* Distributed under the terms of the MIT license. *)
From Coq Require Import ssreflect.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICTyping PCUICEquality PCUICAst PCUICAstUtils
  PCUICWeakeningConv PCUICWeakeningTyp PCUICSubstitution PCUICGeneration PCUICArities
  PCUICWcbvEval PCUICSR PCUICInversion
  PCUICUnivSubstitutionConv PCUICUnivSubstitutionTyp
  PCUICElimination PCUICSigmaCalculus PCUICContextConversion
  PCUICUnivSubst PCUICWeakeningEnvConv PCUICWeakeningEnvTyp
  PCUICCumulativity PCUICConfluence
  PCUICInduction PCUICLiftSubst PCUICContexts PCUICSpine
  PCUICConversion PCUICValidity PCUICInductives PCUICConversion
  PCUICInductiveInversion PCUICNormal PCUICSafeLemmata
  PCUICParallelReductionConfluence
  PCUICWcbvEval PCUICClosed PCUICClosedTyp
  PCUICReduction PCUICCSubst PCUICOnFreeVars PCUICWellScopedCumulativity PCUICCanonicity PCUICWcbvEval.

From Equations Require Import Equations.


Lemma eval_tCase {cf : checker_flags} {Σ : global_env_ext}  ci p discr brs res T :
  wf Σ ->
  Σ ;;; [] |- tCase ci p discr brs : T ->
  eval Σ (tCase ci p discr brs) res ->
  ∑ c u args, red Σ [] (tCase ci p discr brs) (tCase ci p ((mkApps (tConstruct ci.(ci_ind) c u) args)) brs).
Proof.
  intros wf wt H. depind H; try now (cbn in *; congruence).
  - eapply inversion_Case in wt as (? & ? & ? & ? & cinv & ?); eauto.
    eexists _, _, _. eapply red_case_c. eapply wcbeval_red. 2: eauto. eapply cinv.
  - eapply inversion_Case in wt as wt'; eauto. destruct wt' as (? & ? & ? & ? & cinv & ?).
    assert (Hred1 : Σ;;; [] |- tCase ip p discr brs ⇝* tCase ip p (mkApps fn args) brs). {
      etransitivity. { eapply red_case_c. eapply wcbeval_red. 2: eauto. eapply cinv. }
      econstructor. econstructor.
      rewrite closed_unfold_cofix_cunfold_eq. eauto.
      enough (closed (mkApps (tCoFix mfix idx) args)) as Hcl by (rewrite closedn_mkApps in Hcl; solve_all).
      eapply eval_closed. eauto.
      2: eauto. eapply @subject_closed with (Γ := []); eauto. eapply cinv. tea.
    }
    edestruct IHeval2 as (c & u & args0 & IH); eauto using subject_reduction.
    exists c, u, args0. etransitivity; eauto.
Qed.

Local Existing Instance config.extraction_checker_flags.

Inductive typing_spine_pred {cf : checker_flags} Σ (Γ : context) (P : forall t T (H : Σ ;;; Γ |- t : T), Type) : term -> list term -> term -> Type :=
| type_spine_pred_nil ty ty' (* s s' *) :
    isType Σ Γ ty ->
    isType Σ Γ ty' ->
    (* forall H : Σ ;;; Γ |- ty : tSort s,
    P ty (tSort s) H ->
    forall H' : Σ ;;; Γ |- ty' : tSort s',
    P ty' (tSort s') H' ->
     *) Σ ;;; Γ ⊢ ty ≤ ty' ->
    typing_spine_pred Σ Γ P ty [] ty'

| type_spine_pred_cons ty hd tl na A B B' s' :
    isType Σ Γ ty ->
    forall H' : Σ ;;; Γ |- tProd na A B : tSort s',
    P (tProd na A B) (tSort s') H' ->
    Σ ;;; Γ ⊢ ty ≤ tProd na A B ->
    forall H : Σ ;;; Γ |- hd : A,
    P hd A H ->
    typing_spine_pred Σ Γ P (subst10 hd B) tl B' ->
    typing_spine_pred Σ Γ P ty (hd :: tl) B'.

Section WfEnv.
  Context {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ}.

  Lemma typing_spine_pred_strengthen {Γ P T args U} :
    typing_spine_pred Σ Γ P T args U ->
    isType Σ Γ T ->
    forall T',
    isType Σ Γ T' ->
    Σ ;;; Γ ⊢ T' ≤ T ->
    typing_spine_pred Σ Γ P T' args U.
  Proof using wfΣ.
    induction 1 in |- *; intros T' isTy redT.
    - constructor; eauto. transitivity ty; auto.
    - specialize IHX with (T' := (B {0 := hd})).
      assert (isType Σ Γ (B {0 := hd})) as HH. {
        clear p.
        eapply inversion_Prod in H' as (? & ? & ? & ? & ?); tea.
        eapply isType_subst. econstructor. econstructor. rewrite subst_empty; eauto.
        econstructor; cbn; eauto.
      }
      do 3 forward IHX by pcuic.
      intros Hsub.
      eapply type_spine_pred_cons; eauto.
      etransitivity; eauto.
  Qed.

End WfEnv.

Lemma inversion_mkApps {cf : checker_flags} {Σ} {wfΣ :  wf Σ.1} {Γ f u T} s :
  forall (H : Σ ;;; Γ |- mkApps f u : T) (HT : Σ ;;; Γ |- T : tSort s),
  { A : term & { Hf : Σ ;;; Γ |- f : A & {s' & {HA : Σ ;;; Γ |- A : tSort s' &
   typing_size Hf <= typing_size H ×
   typing_size HA <= max (typing_size H) (typing_size HT) ×
  typing_spine_pred Σ Γ (fun x ty Hx => typing_size Hx <= typing_size H) A u T}}}}.
Proof.
  revert f T.
  induction u; intros f T. simpl. intros.
  { exists T, H, s, HT. intuition pcuic.
    econstructor. eexists; eauto. eexists; eauto. eapply isType_ws_cumul_pb_refl. eexists; eauto. }
  intros Hf Ht. simpl in Hf.
  specialize (IHu (tApp f a) T).
  epose proof (IHu Hf) as (T' & H' & s' & H1 & H2 & H3 & H4); tea.
  edestruct @inversion_App_size with (H := H') as (na' & A' & B' & s_ & Hf' & Ha & HA & Hs1 & Hs2 & Hs3 & HA'''); tea.
  exists (tProd na' A' B'). exists Hf'. exists s_. exists HA.
  split. rewrite <- H2. lia.
  split. rewrite <- Nat.le_max_l, <- H2. lia.

  unshelve econstructor.
  5: eauto. 1: eauto.
  3:eapply isType_ws_cumul_pb_refl; eexists; eauto.
  1: eexists; eauto.
  1, 2: rewrite <- H2; lia.
  eapply typing_spine_pred_strengthen; tea.
  eexists; eauto. clear Hs3.
  eapply inversion_Prod in HA as (? & ? & ? & ? & ?); tea.
  eapply isType_subst. econstructor. econstructor. rewrite subst_empty; eauto.
  econstructor;  cbn; eauto.
  Unshelve. eauto.
Qed.

Lemma typing_ind_env_app_size `{cf : checker_flags} :
forall (P : global_env_ext -> context -> term -> term -> Type)
       (Pdecl := fun Σ Γ wfΓ t T tyT => P Σ Γ t T)
       (PΓ : global_env_ext -> context -> Type),

  (forall Σ (wfΣ : wf Σ.1)  (Γ : context) (wfΓ : wf_local Σ Γ),
       All_local_env_over typing Pdecl Σ Γ wfΓ -> PΓ Σ Γ) ->

  (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (n : nat) decl,
      nth_error Γ n = Some decl ->
      PΓ Σ Γ ->
      P Σ Γ (tRel n) (lift0 (S n) decl.(decl_type))) ->

  (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (u : Universe.t),
      PΓ Σ Γ ->
      wf_universe Σ u ->
      P Σ Γ (tSort u) (tSort (Universe.super u))) ->

  (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (n : aname) (t b : term) (s1 s2 : Universe.t),
      PΓ Σ Γ ->
      Σ ;;; Γ |- t : tSort s1 ->
      P Σ Γ t (tSort s1) ->
      Σ ;;; Γ,, vass n t |- b : tSort s2 ->
      P Σ (Γ,, vass n t) b (tSort s2) -> P Σ Γ (tProd n t b) (tSort (Universe.sort_of_product s1 s2))) ->

  (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (n : aname) (t b : term)
          (s1 : Universe.t) (bty : term),
      PΓ Σ Γ ->
      Σ ;;; Γ |- t : tSort s1 ->
      P Σ Γ t (tSort s1) ->
      Σ ;;; Γ,, vass n t |- b : bty -> P Σ (Γ,, vass n t) b bty -> P Σ Γ (tLambda n t b) (tProd n t bty)) ->

  (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (n : aname) (b b_ty b' : term)
          (s1 : Universe.t) (b'_ty : term),
      PΓ Σ Γ ->
      Σ ;;; Γ |- b_ty : tSort s1 ->
      P Σ Γ b_ty (tSort s1) ->
      Σ ;;; Γ |- b : b_ty ->
      P Σ Γ b b_ty ->
      Σ ;;; Γ,, vdef n b b_ty |- b' : b'_ty ->
      P Σ (Γ,, vdef n b b_ty) b' b'_ty -> P Σ Γ (tLetIn n b b_ty b') (tLetIn n b b_ty b'_ty)) ->

  (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (t : term) T B L s,
      PΓ Σ Γ ->
      Σ ;;; Γ |- T : tSort s -> P Σ Γ T (tSort s) ->
      forall (Ht : Σ ;;; Γ |- t : T), P Σ Γ t T ->

      (* Give a stronger induction hypothesis allowing to crawl under applications *)
      (forall t' T' (Ht' : Σ ;;; Γ |- t' : T'), typing_size Ht' <= typing_size Ht -> P Σ Γ t' T') ->
      typing_spine_pred Σ Γ (fun u ty H => Σ ;;; Γ |- u : ty × P Σ Γ u ty) T L B ->

      P Σ Γ (mkApps t L) B) ->

  (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) cst u (decl : constant_body),
      Forall_decls_typing P Σ.1 ->
      PΓ Σ Γ ->
      declared_constant Σ.1 cst decl ->
      consistent_instance_ext Σ decl.(cst_universes) u ->
      P Σ Γ (tConst cst u) (subst_instance u (cst_type decl))) ->

  (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (ind : inductive) u
        mdecl idecl (isdecl : declared_inductive Σ.1 ind mdecl idecl),
      Forall_decls_typing P Σ.1 ->
      PΓ Σ Γ ->
      consistent_instance_ext Σ mdecl.(ind_universes) u ->
      P Σ Γ (tInd ind u) (subst_instance u (ind_type idecl))) ->

  (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (ind : inductive) (i : nat) u
          mdecl idecl cdecl (isdecl : declared_constructor Σ.1 (ind, i) mdecl idecl cdecl),
      Forall_decls_typing P Σ.1 ->
      PΓ Σ Γ ->
      consistent_instance_ext Σ mdecl.(ind_universes) u ->
      P Σ Γ (tConstruct ind i u) (type_of_constructor mdecl cdecl (ind, i) u)) ->

    (forall (Σ : global_env_ext) (wfΣ : wf Σ) (Γ : context) (wfΓ : wf_local Σ Γ),
     forall (ci : case_info) p c brs indices ps mdecl idecl
       (isdecl : declared_inductive Σ.1 ci.(ci_ind) mdecl idecl),
       Forall_decls_typing P Σ.1 ->
       PΓ Σ Γ ->
       mdecl.(ind_npars) = ci.(ci_npar) ->
       eq_context_upto_names p.(pcontext) (ind_predicate_context ci.(ci_ind) mdecl idecl) ->
       let predctx := case_predicate_context ci.(ci_ind) mdecl idecl p in
       wf_predicate mdecl idecl p ->
       consistent_instance_ext Σ (ind_universes mdecl) p.(puinst) ->
       forall pret : Σ ;;; Γ ,,, predctx |- p.(preturn) : tSort ps,
       P Σ (Γ ,,, predctx) p.(preturn) (tSort ps) ->
       wf_local Σ (Γ ,,, predctx) ->
       PΓ Σ (Γ ,,, predctx) ->
       is_allowed_elimination Σ idecl.(ind_kelim) ps ->
       PCUICTyping.ctx_inst (Prop_conj typing P) Σ Γ (p.(pparams) ++ indices)
         (List.rev (subst_instance p.(puinst) (mdecl.(ind_params) ,,, idecl.(ind_indices)))) ->
       Σ ;;; Γ |- c : mkApps (tInd ci.(ci_ind) p.(puinst)) (p.(pparams) ++ indices) ->
       P Σ Γ c (mkApps (tInd ci.(ci_ind) p.(puinst)) (p.(pparams) ++ indices)) ->
       isCoFinite mdecl.(ind_finite) = false ->
       let ptm := it_mkLambda_or_LetIn predctx p.(preturn) in
       wf_branches idecl brs ->
       All2i (fun i cdecl br =>
         (eq_context_upto_names br.(bcontext) (cstr_branch_context ci mdecl cdecl)) ×
         let brctxty := case_branch_type ci.(ci_ind) mdecl idecl p br ptm i cdecl in
         (PΓ Σ (Γ ,,, brctxty.1) ×
         (Prop_conj typing P Σ (Γ ,,, brctxty.1) br.(bbody) brctxty.2) ×
         (Prop_conj typing P Σ (Γ ,,, brctxty.1) brctxty.2 (tSort ps)))) 0 idecl.(ind_ctors) brs ->
       P Σ Γ (tCase ci p c brs) (mkApps ptm (indices ++ [c]))) ->

  (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (p : projection) (c : term) u
        mdecl idecl cdecl pdecl (isdecl : declared_projection Σ.1 p mdecl idecl cdecl pdecl) args,
      Forall_decls_typing P Σ.1 -> PΓ Σ Γ ->
      Σ ;;; Γ |- c : mkApps (tInd p.(proj_ind) u) args ->
      P Σ Γ c (mkApps (tInd p.(proj_ind) u) args) ->
      #|args| = ind_npars mdecl ->
      P Σ Γ (tProj p c) (subst0 (c :: List.rev args) (pdecl.(proj_type)@[u]))) ->

  (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (mfix : list (def term)) (n : nat) decl,
      let types := fix_context mfix in
      fix_guard Σ Γ mfix ->
      nth_error mfix n = Some decl ->
      PΓ Σ (Γ ,,, types) ->
      All (on_def_type (lift_typing2 typing P Σ) Γ) mfix ->
      All (on_def_body (lift_typing2 typing P Σ) types Γ) mfix ->
      wf_fixpoint Σ.1 mfix ->
      P Σ Γ (tFix mfix n) decl.(dtype)) ->

  (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (mfix : list (def term)) (n : nat) decl,
      let types := fix_context mfix in
      cofix_guard Σ Γ mfix ->
      nth_error mfix n = Some decl ->
      PΓ Σ (Γ ,,, types) ->
      All (on_def_type (lift_typing2 typing P Σ) Γ) mfix ->
      All (on_def_body (lift_typing2 typing P Σ) types Γ) mfix ->
      wf_cofixpoint Σ.1 mfix ->
      P Σ Γ (tCoFix mfix n) decl.(dtype)) ->

  (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (p : prim_val) prim_ty cdecl,
    PΓ Σ Γ ->
    primitive_constant Σ.1 (prim_val_tag p) = Some prim_ty ->
    declared_constant Σ.1 prim_ty cdecl ->
    primitive_invariants cdecl ->
    P Σ Γ (tPrim p) (tConst prim_ty [])) ->

  (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (t A B : term) s,
      PΓ Σ Γ ->
      Σ ;;; Γ |- t : A ->
      P Σ Γ t A ->
      Σ ;;; Γ |- B : tSort s ->
      P Σ Γ B (tSort s) ->
      Σ ;;; Γ |- A <=s B ->
      P Σ Γ t B) ->

     env_prop P PΓ.
Proof.
 intros P Pdecl PΓ.
 intros XΓ X X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 Σ wfΣ Γ t T H.
 eapply typing_ind_env_app_size; eauto. clear Σ wfΣ Γ t T H.
 intros Σ wfΣ Γ wfΓ t na A B u s HΓ Hprod IHprod Ht IHt IH Hu IHu.
 pose proof (mkApps_decompose_app t).
 destruct (decompose_app t) as [t1 L].
 subst. rename t1 into t. cbn in *.
 replace (tApp (mkApps t L) u) with (mkApps t (L ++ [u])) by now rewrite mkApps_app.

 pose proof (@inversion_mkApps cf) as Happs. specialize Happs with (H := Ht).
 forward Happs; eauto.
 destruct (Happs _ Hprod) as (A' & Hf & s' & HA & sz_f & sz_A & HL).
 destruct @inversion_Prod_size with (H := Hprod) as (s1 & s2 & H1 & H2 & Hs1 & Hs2 & Hsub); [ eauto | ].
 eapply X4. 6:eauto. 4: exact HA. all: eauto.
 - intros. eapply (IH _ _ Hf). lia.
 - Unshelve. 2:exact Hf. intros. eapply (IH _ _ Ht'). lia.
 - clear sz_A. induction L in A', Hf, (* HA, sz_A, *) Ht, HL, t, Hf, IH (*, s' *) |- *.
   + inversion HL; subst. inversion X13. econstructor. econstructor; eauto. eauto. eauto. eauto. eauto. eauto.
     econstructor. 1,2: eapply isType_apply; eauto. eapply ws_cumul_pb_refl.
     eapply typing_closed_context; eauto. eapply type_is_open_term.
     eapply type_App; eauto.
   + cbn. inversion HL. subst. clear HL.
     eapply inversion_Prod in H' as Hx; eauto. destruct Hx as (? & ? & ? & ? & ?).
     econstructor.
     7: unshelve eapply IHL.
     now eauto. now eauto. split. now eauto. unshelve eapply IH. eauto. lia.
     now eauto. now eauto. split. now eauto. unshelve eapply IH. eauto. lia.
     2: now eauto. eauto.
     econstructor; eauto. econstructor; eauto. now eapply cumulAlgo_cumulSpec in X14.
     eauto.
Qed.

Lemma typing_ind_env `{cf : checker_flags} :
  forall (P : global_env_ext -> context -> term -> term -> Type)
         (Pdecl := fun Σ Γ wfΓ t T tyT => P Σ Γ t T)
         (PΓ : global_env_ext -> context -> Type),

    (forall Σ (wfΣ : wf Σ.1)  (Γ : context) (wfΓ : wf_local Σ Γ),
         All_local_env_over typing Pdecl Σ Γ wfΓ -> PΓ Σ Γ) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (n : nat) decl,
        nth_error Γ n = Some decl ->
        PΓ Σ Γ ->
        P Σ Γ (tRel n) (lift0 (S n) decl.(decl_type))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (u : Universe.t),
        PΓ Σ Γ ->
        wf_universe Σ u ->
        P Σ Γ (tSort u) (tSort (Universe.super u))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (n : aname) (t b : term) (s1 s2 : Universe.t),
        PΓ Σ Γ ->
        Σ ;;; Γ |- t : tSort s1 ->
        P Σ Γ t (tSort s1) ->
        Σ ;;; Γ,, vass n t |- b : tSort s2 ->
        P Σ (Γ,, vass n t) b (tSort s2) -> P Σ Γ (tProd n t b) (tSort (Universe.sort_of_product s1 s2))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (n : aname) (t b : term)
            (s1 : Universe.t) (bty : term),
        PΓ Σ Γ ->
        Σ ;;; Γ |- t : tSort s1 ->
        P Σ Γ t (tSort s1) ->
        Σ ;;; Γ,, vass n t |- b : bty -> P Σ (Γ,, vass n t) b bty -> P Σ Γ (tLambda n t b) (tProd n t bty)) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (n : aname) (b b_ty b' : term)
            (s1 : Universe.t) (b'_ty : term),
        PΓ Σ Γ ->
        Σ ;;; Γ |- b_ty : tSort s1 ->
        P Σ Γ b_ty (tSort s1) ->
        Σ ;;; Γ |- b : b_ty ->
        P Σ Γ b b_ty ->
        Σ ;;; Γ,, vdef n b b_ty |- b' : b'_ty ->
        P Σ (Γ,, vdef n b b_ty) b' b'_ty -> P Σ Γ (tLetIn n b b_ty b') (tLetIn n b b_ty b'_ty)) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (t : term) T B L s,
        PΓ Σ Γ ->
        Σ ;;; Γ |- T : tSort s -> P Σ Γ T (tSort s) ->
        forall (Ht : Σ ;;; Γ |- t : T), P Σ Γ t T ->

        (* Give a stronger induction hypothesis allowing to crawl under applications *)
        typing_spine_pred Σ Γ (fun u ty H => Σ ;;; Γ |- u : ty × P Σ Γ u ty) T L B ->

        P Σ Γ (mkApps t L) B) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) cst u (decl : constant_body),
        Forall_decls_typing P Σ.1 ->
        PΓ Σ Γ ->
        declared_constant Σ.1 cst decl ->
        consistent_instance_ext Σ decl.(cst_universes) u ->
        P Σ Γ (tConst cst u) (subst_instance u (cst_type decl))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (ind : inductive) u
          mdecl idecl (isdecl : declared_inductive Σ.1 ind mdecl idecl),
        Forall_decls_typing P Σ.1 ->
        PΓ Σ Γ ->
        consistent_instance_ext Σ mdecl.(ind_universes) u ->
        P Σ Γ (tInd ind u) (subst_instance u (ind_type idecl))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (ind : inductive) (i : nat) u
            mdecl idecl cdecl (isdecl : declared_constructor Σ.1 (ind, i) mdecl idecl cdecl),
        Forall_decls_typing P Σ.1 ->
        PΓ Σ Γ ->
        consistent_instance_ext Σ mdecl.(ind_universes) u ->
        P Σ Γ (tConstruct ind i u) (type_of_constructor mdecl cdecl (ind, i) u)) ->

    (forall (Σ : global_env_ext) (wfΣ : wf Σ) (Γ : context) (wfΓ : wf_local Σ Γ),
    forall (ci : case_info) p c brs indices ps mdecl idecl
      (isdecl : declared_inductive Σ.1 ci.(ci_ind) mdecl idecl),
      Forall_decls_typing P Σ.1 ->
      PΓ Σ Γ ->
      mdecl.(ind_npars) = ci.(ci_npar) ->
      eq_context_upto_names p.(pcontext) (ind_predicate_context ci.(ci_ind) mdecl idecl) ->
      let predctx := case_predicate_context ci.(ci_ind) mdecl idecl p in
      wf_predicate mdecl idecl p ->
      consistent_instance_ext Σ (ind_universes mdecl) p.(puinst) ->
      forall pret : Σ ;;; Γ ,,, predctx |- p.(preturn) : tSort ps,
      P Σ (Γ ,,, predctx) p.(preturn) (tSort ps) ->
      wf_local Σ (Γ ,,, predctx) ->
      PΓ Σ (Γ ,,, predctx) ->
      is_allowed_elimination Σ idecl.(ind_kelim) ps ->
      PCUICTyping.ctx_inst (Prop_conj typing P) Σ Γ (p.(pparams) ++ indices)
        (List.rev (subst_instance p.(puinst) (mdecl.(ind_params) ,,, idecl.(ind_indices)))) ->
      Σ ;;; Γ |- c : mkApps (tInd ci.(ci_ind) p.(puinst)) (p.(pparams) ++ indices) ->
      P Σ Γ c (mkApps (tInd ci.(ci_ind) p.(puinst)) (p.(pparams) ++ indices)) ->
      isCoFinite mdecl.(ind_finite) = false ->
      let ptm := it_mkLambda_or_LetIn predctx p.(preturn) in
      wf_branches idecl brs ->
      All2i (fun i cdecl br =>
        (eq_context_upto_names br.(bcontext) (cstr_branch_context ci mdecl cdecl)) ×
        let brctxty := case_branch_type ci.(ci_ind) mdecl idecl p br ptm i cdecl in
        (PΓ Σ (Γ ,,, brctxty.1) ×
          (Prop_conj typing P Σ (Γ ,,, brctxty.1) br.(bbody) brctxty.2) ×
          (Prop_conj typing P) Σ (Γ ,,, brctxty.1) brctxty.2 (tSort ps))) 0 idecl.(ind_ctors) brs ->
      P Σ Γ (tCase ci p c brs) (mkApps ptm (indices ++ [c]))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (p : projection) (c : term) u
          mdecl idecl cdecl pdecl (isdecl : declared_projection Σ.1 p mdecl idecl cdecl pdecl) args,
        Forall_decls_typing P Σ.1 -> PΓ Σ Γ ->
        Σ ;;; Γ |- c : mkApps (tInd p.(proj_ind) u) args ->
        P Σ Γ c (mkApps (tInd p.(proj_ind) u) args) ->
        #|args| = ind_npars mdecl ->
        P Σ Γ (tProj p c) (subst0 (c :: List.rev args) (subst_instance u pdecl.(proj_type)))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (mfix : list (def term)) (n : nat) decl,
        let types := fix_context mfix in
        fix_guard Σ Γ mfix ->
        nth_error mfix n = Some decl ->
        PΓ Σ (Γ ,,, types) ->
        All (on_def_type (lift_typing2 typing P Σ) Γ) mfix ->
        All (on_def_body (lift_typing2 typing P Σ) types Γ) mfix ->
        wf_fixpoint Σ.1 mfix ->
        P Σ Γ (tFix mfix n) decl.(dtype)) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (mfix : list (def term)) (n : nat) decl,
        let types := fix_context mfix in
        cofix_guard Σ Γ mfix ->
        nth_error mfix n = Some decl ->
        PΓ Σ (Γ ,,, types) ->
        All (on_def_type (lift_typing2 typing P Σ) Γ) mfix ->
        All (on_def_body (lift_typing2 typing P Σ) types Γ) mfix ->
        wf_cofixpoint Σ.1 mfix ->
        P Σ Γ (tCoFix mfix n) decl.(dtype)) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (p : prim_val) prim_ty cdecl,
        PΓ Σ Γ ->
        primitive_constant Σ.1 (prim_val_tag p) = Some prim_ty ->
        declared_constant Σ.1 prim_ty cdecl ->
        primitive_invariants cdecl ->
        P Σ Γ (tPrim p) (tConst prim_ty [])) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (t A B : term) s,
        PΓ Σ Γ ->
        Σ ;;; Γ |- t : A ->
        P Σ Γ t A ->
        Σ ;;; Γ |- B : tSort s ->
        P Σ Γ B (tSort s) ->
        Σ ;;; Γ |- A <=s B ->
        P Σ Γ t B) ->

       env_prop P PΓ.
Proof.
  intros P Pdecl PΓ; unfold env_prop.
  intros XΓ X X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 Σ wfΣ Γ t T H.
  apply typing_ind_env_app_size; eauto.
Qed.

Local Hint Constructors value red1 : wcbv.

Definition axiom_free Σ :=
  forall c decl, declared_constant Σ c decl -> cst_body decl <> None. (* TODO: consolidate with PCUICConsistency *)

Lemma value_stuck_fix Σ mfix idx args : isStuckFix (tFix mfix idx) args -> All (value Σ) args -> value Σ (mkApps (tFix mfix idx) args).
Proof.
  unfold isStuckFix; intros isstuck vargs.
  eapply value_app => //.
  destruct cunfold_fix as [[rarg fn]|] eqn:cunf => //.
  econstructor; tea. now eapply Nat.leb_le.
Qed.

Lemma typing_spine_length {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} Γ Δ ind u args args' T' :
  typing_spine Σ Γ (it_mkProd_or_LetIn Δ (mkApps (tInd ind u) args)) args' T' ->
  #|args'| <= context_assumptions Δ.
Proof.
  intros hsp.
  pose proof (typing_spine_more_inv _ _ _ _ _ _ _ _ hsp).
  destruct (Compare_dec.le_dec #|args'| (context_assumptions Δ)). lia. lia.
Qed.

Lemma declared_constructor_ind_decl {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {ind c} {mdecl idecl cdecl} :
  declared_constructor Σ (ind, c) mdecl idecl cdecl ->
  inductive_ind ind < #|ind_bodies mdecl|.
Proof.
  intros [[hm hi] hc]. now eapply nth_error_Some_length in hi.
Qed.

Import PCUICGlobalEnv.

Lemma typing_constructor_arity_exact {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {ind c u u' args}
  {mdecl idecl cdecl indices} :
  declared_constructor Σ (ind, c) mdecl idecl cdecl ->
  Σ ;;; [] |- mkApps (tConstruct ind c u) args : mkApps (tInd ind u') indices ->
  #|args| = cstr_arity mdecl cdecl.
Proof.
  intros declc hc.
  eapply Construct_Ind_ind_eq in hc; tea.
  intuition auto.
Qed.

Lemma typing_constructor_arity {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {ind c u args T} {mdecl idecl cdecl} :
  declared_constructor Σ (ind, c) mdecl idecl cdecl ->
  Σ ;;; [] |- mkApps (tConstruct ind c u) args : T ->
  #|args| <= cstr_arity mdecl cdecl.
Proof.
  intros declc hc.
  pose proof (validity hc).
  eapply PCUICSpine.inversion_mkApps_direct in hc as [A' [u' [s' [hs hsp]]]]; eauto.
  eapply inversion_Construct in s' as [mdecl' [idecl' [cdecl' [wf [declc' [cu cum]]]]]]; tea.
  destruct (PCUICGlobalEnv.declared_constructor_inj declc declc') as [? []]. subst mdecl' idecl' cdecl'.
  clear declc'.
  eapply typing_spine_strengthen in hsp. 3:exact cum.
  2:{ eapply validity. econstructor; tea. }
  unfold type_of_constructor in hsp.
  destruct (on_declared_constructor declc) as [[] [cunivs [_ onc]]].
  rewrite onc.(cstr_eq) in hsp.
  rewrite <-it_mkProd_or_LetIn_app in hsp.
  rewrite subst_instance_it_mkProd_or_LetIn subst_it_mkProd_or_LetIn in hsp.
  epose proof (subst_cstr_concl_head ind u mdecl (cstr_args cdecl) (cstr_indices cdecl)). cbn in H.
  unfold cstr_concl in hsp. cbn in hsp. len in hsp. rewrite H in hsp. clear H.
  eapply (declared_constructor_ind_decl declc). clear H.
  eapply typing_spine_length in hsp. len in hsp. unfold cstr_arity.
  now rewrite (PCUICGlobalEnv.declared_minductive_ind_npars declc).
Qed.

Lemma value_mkApps_inv' Σ f args :
  negb (isApp f) ->
  value Σ (mkApps f args) ->
  atom f × All (value Σ) args.
Proof.
  intros napp. move/value_mkApps_inv => [] => //.
  - intros [-> hf]. split => //.
  - intros []. split; auto. destruct v; now constructor.
Qed.

Global Hint Resolve All_app_inv : pcuic.

Lemma red1_mkApps_left {Σ f f' args} : red1 Σ f f' -> red1 Σ (mkApps f args) (mkApps f' args).
Proof.
  induction args using rev_ind.
  - auto.
  - intros. rewrite !mkApps_app.
    eapply red_app_left. now apply IHargs.
Qed.

Lemma typing_spine_sort {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} Γ s args T :
  typing_spine Σ Γ (tSort s) args T -> args = [].
Proof.
  induction args => //.
  intros sp. depelim sp.
  now eapply ws_cumul_pb_Sort_Prod_inv in w.
Qed.

Lemma typing_spine_axiom {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} Γ cst u cdecl args T :
  declared_constant Σ cst cdecl ->
  cdecl.(cst_body) = None ->
  typing_spine Σ Γ (tConst cst u) args T -> args = [].
Proof.
  intros hdecl hb.
  induction args => //.
  intros sp. depelim sp.
  now eapply invert_cumul_axiom_prod in w.
Qed.

Lemma typing_value_head_napp {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} fn args hd T :
  negb (isApp fn) ->
  Σ ;;; [] |- mkApps fn (args ++ [hd]) : T ->
  value Σ hd -> closed hd ->
  value Σ (mkApps fn args) ->
  (∑ t' : term, red1 Σ (mkApps fn (args ++ [hd])) t') +
  value Σ (mkApps fn (args ++ [hd])).
Proof.
  intros napp ht vhd clhd vapp.
  pose proof ht as ht'.
  destruct (value_mkApps_inv' _ _ _ napp vapp).
  eapply PCUICSpine.inversion_mkApps_direct in ht' as [A' [u [hfn [hhd hcum]]]]; tea.
  2:{ now eapply validity. }
  destruct fn => //.
  * eapply inversion_Sort in hfn as [? [? cu]]; tea.
    eapply typing_spine_strengthen in hcum. 3:tea. 2:{ eapply validity; econstructor; eauto. }
    now eapply typing_spine_sort, app_tip_nil in hcum.
  * eapply inversion_Prod in hfn as [? [? [? [? cu]]]]; tea.
    eapply typing_spine_strengthen in hcum. 3:tea. 2:{ eapply validity. econstructor; eauto. }
    now eapply typing_spine_sort, app_tip_nil in hcum.
  * (* Lambda *) left. destruct args.
    - cbn. eexists. now eapply red_beta.
    - eexists. rewrite mkApps_app. rewrite (mkApps_app _ [t] args). do 2 eapply red1_mkApps_left.
      cbn. eapply red_beta. now depelim a.
  * (* Inductive *)
    eapply inversion_Ind in hfn as [? [? [? [? [? cu]]]]]; tea.
    eapply typing_spine_strengthen in hcum. 3:tea. 2:{ eapply validity. econstructor; eauto. }
    right. eapply value_app. constructor. eauto with pcuic.
  * (* constructor *)
    right. eapply value_app; auto. 2:{ eapply All_app_inv; eauto. }
    pose proof hfn as hfn'.
    eapply inversion_Construct in hfn' as [mdecl [idecl [cdecl [wf [declc _]]]]]; tea.
    eapply (typing_constructor_arity declc) in ht.
    econstructor; tea.
  * (* fix *)
    destruct (isStuckFix (tFix mfix idx) (args ++ [hd])) eqn:E.
    + right. eapply value_stuck_fix; eauto with pcuic.
    + cbn in E.
      eapply inversion_Fix in hfn as ([] & ? & Efix & ? & ? & ?); eauto.
      unfold cunfold_fix in E. rewrite Efix in E. cbn in E.
      len in E. cbn in E. assert (rarg = #|args|).
      eapply stuck_fix_value_args in vapp; tea. 2:{ unfold cunfold_fix. now rewrite Efix. }
      cbn in vapp. apply Nat.leb_gt in E. lia. subst rarg.
      left. eexists. rewrite mkApps_app /=. eapply red_fix. eauto. eauto.
      unfold unfold_fix. now rewrite Efix.
      eapply fix_app_is_constructor in ht.
      2:{ unfold unfold_fix. now rewrite Efix. }
      cbn in ht. rewrite nth_error_app_ge // /= in ht.
      replace (#|args| - #|args|) with 0 in ht by lia. cbn in ht. apply ht.
      eapply value_axiom_free; eauto.
      eapply value_whnf; eauto.
  * (* cofix *)
    right. eapply value_app; eauto with pcuic.
    now constructor.
  * (* primitive *)
    cbn.
    eapply inversion_Prim in hfn as [prim_ty [cdecl [hwf hp hdecl [s []]]]]; tea.
    eapply typing_spine_strengthen in hcum. 3:tea. 2:{ eapply validity; econstructor; eauto. now exists s. }
    now eapply typing_spine_axiom, app_tip_nil in hcum.
Qed.

Lemma typing_value_head {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} fn args hd T :
  Σ ;;; [] |- mkApps fn (args ++ [hd]) : T ->
  value Σ hd -> closed hd ->
  value Σ (mkApps fn args) ->
  (∑ t' : term, red1 Σ (mkApps fn (args ++ [hd])) t') +
  value Σ (mkApps fn (args ++ [hd])).
Proof.
  destruct (decompose_app fn) eqn:da.
  pose proof (decompose_app_notApp _ _ _ da).
  rewrite (decompose_app_inv da).
  rewrite -mkApps_app app_assoc.
  intros; eapply typing_value_head_napp; tea. now rewrite H.
  rewrite mkApps_app //.
Qed.

Lemma cstr_branch_context_assumptions ci mdecl cdecl :
  context_assumptions (cstr_branch_context ci mdecl cdecl) =
  context_assumptions (cstr_args cdecl).
Proof.
  rewrite /cstr_branch_context /PCUICEnvironment.expand_lets_ctx
    /PCUICEnvironment.expand_lets_k_ctx.
  now do 2 rewrite !context_assumptions_subst_context ?context_assumptions_lift_context.
Qed.

Lemma progress `{cf : checker_flags}:
  env_prop (fun Σ Γ t T => axiom_free Σ -> Γ = [] -> Σ ;;; Γ |- t : T -> {t' & red1 Σ t t'} + (value Σ t))
           (fun _ _ => True).
Proof with eauto with wcbv; try congruence.
  eapply typing_ind_env...
  - intros Σ wfΣ Γ wfΓ n decl Hdecl _ Hax -> Hty.
    destruct n; inv Hdecl.
  - intros Σ wfΣ Γ _ n b b_ty b' s1 b'_ty _ Hb_ty IHb_ty Hb IHb Hb' IHb' Hax -> H.
    destruct (IHb Hax eq_refl) as [ [t' IH] | IH]; eauto with wcbv.
  - intros Σ wfΣ Γ _ t T B L s _ HT IHT Ht IHt HL Hax -> H.
    clear HT IHT.
    induction HL in H, t, Ht, IHt |- *.
    + cbn. eauto.
    + cbn. eapply IHHL.
      2:{ do 2 (econstructor; eauto). now eapply cumulAlgo_cumulSpec in w. }
      intros _ Happ.
      destruct (IHt Hax eq_refl Ht) as [[t' IH] | IH]; eauto with wcbv.
      assert (Ht' : Σ ;;; [] |- t : tProd na A B) by (econstructor; eauto; now eapply cumulAlgo_cumulSpec in w).
      destruct p0 as [_ [[t' Hstep] | Hval]]; eauto using red1.
      intros htapp.
      pose proof (typing_value_head t [] hd _ htapp Hval).
      forward X. now eapply subject_closed in H0. cbn in X.
      specialize (X IH). exact X.
      now cbn in H.
  - intros Σ wf Γ _ cst u decl Hdecls _ Hdecl Hcons Hax -> H.
    destruct (decl.(cst_body)) as [body | ] eqn:E.
    + eauto with wcbv.
    + red in Hax. eapply Hax in E; eauto.
  - intros Σ wfΣ Γ _ ci p c brs indices ps mdecl idecl Hidecl Hforall _ Heq Heq_context predctx Hwfpred Hcon Hreturn IHreturn Hwfl _.
    intros Helim Hctxinst Hc IHc Hcof ptm Hwfbranches Hall Hax -> H.
    specialize (IHc Hax eq_refl) as [[t' IH] | IH]; eauto with wcbv.
    pose proof IH as IHv.
    eapply PCUICCanonicity.value_canonical in IH; eauto.
    unfold head in IH.
    rewrite (PCUICInduction.mkApps_decompose_app c) in H, Hc, IHv |- *.
    destruct (decompose_app c) as [h l].
    cbn - [decompose_app] in *.
    destruct h; inv IH.
    + eapply invert_Case_Construct in H as H_; sq; eauto. destruct H_ as (Eq & H_); subst.
      left.
      destruct (nth_error brs n) as [br | ] eqn:E.
      2:{ exfalso. destruct H_ as [? []]; congruence. }
      assert (#|l| = ci_npar ci + context_assumptions (bcontext br)) as Hl.
      { destruct H_ as [? []]; auto. now noconf H0. }
      clear H_. eapply Construct_Ind_ind_eq' in Hc as (? & ? & ? & ? & _); eauto.
      eexists.
      destruct (declared_inductive_inj d.p1 Hidecl); subst x x0.
      eapply All2i_nth_error in Hall as [eqctx _]; tea; [|eapply d].
      eapply PCUICCasesContexts.alpha_eq_context_assumptions in eqctx.
      rewrite cstr_branch_context_assumptions in eqctx.
      eapply red_iota; eauto.
      { rewrite /cstr_arity Hl. rewrite -Heq. lia. }
      eapply value_mkApps_inv in IHv as [[-> ]|[]]; eauto.

    + eapply inversion_Case in H as (? & ? & ? & ? & [] & ?); eauto.
      eapply PCUICValidity.inversion_mkApps in scrut_ty as (? & ? & ?); eauto.
      eapply inversion_CoFix in t as (? & ? & ? & ? & ? & ? & ?); eauto.
      left. eexists. eapply red_cofix_case. unfold cunfold_cofix. rewrite e. reflexivity.
      eapply value_mkApps_inv in IHv as [[-> ]|[]]; eauto.
  - intros Σ wfΣ Γ _ p c u mdecl idecl cdecl pdecl Hcon args Hargs _ Hc IHc
           Hlen Hax -> H.
    destruct (IHc Hax eq_refl) as [[t' IH] | IH]; eauto with wcbv; clear IHc.
    pose proof IH as Hval.
    eapply PCUICCanonicity.value_canonical in IH; eauto.
    unfold head in IH.
    rewrite (PCUICInduction.mkApps_decompose_app c) in H, Hc, Hval |- *.
    destruct (decompose_app c) as [h l].
    cbn - [decompose_app] in *.
    destruct h; inv IH.
    + eapply invert_Proj_Construct in H as H_; sq; eauto. destruct H_ as (<- & -> & Hl).
      left. eapply nth_error_Some' in Hl as [x Hx].
      eexists.
      eapply red_proj; eauto.
      now eapply (typing_constructor_arity_exact Hcon) in Hc.
      eapply value_mkApps_inv in Hval as [[-> Hval] | [? ? Hval]]; eauto.
    + left. eapply inversion_Proj in H as (? & ? & ? & ? & ? & ? & ? & ? & ? & ?); eauto.
      eapply PCUICValidity.inversion_mkApps in t as (? & ? & ?); eauto.
      eapply inversion_CoFix in t as (? & ? & ? & ? & ? & ? & ?); eauto.
      eexists. eapply red_cofix_proj. unfold cunfold_cofix. rewrite e0. reflexivity.
      eapply value_mkApps_inv in Hval as [[-> ]|[]]; eauto.
Qed.

Lemma red1_closed {cf : checker_flags} {Σ t t'} :
  wf Σ ->
  closed t -> red1 Σ t t' -> closed t'.
Proof.
  intros Hwf Hcl Hred. induction Hred; cbn in *; solve_all.
  all: eauto using closed_csubst, closed_def.
  - eapply closed_iota; eauto. solve_all. unfold test_predicate_k in H. solve_all.
    now rewrite e0 /cstr_arity -e1 -e2.
  - eauto using closed_arg.
  - rewrite !closedn_mkApps in H |- *. solve_all.
    eapply closed_unfold_fix; tea.
  - rewrite !closedn_mkApps in Hcl |- *. solve_all.
    unfold cunfold_cofix in e. destruct nth_error as [d | ] eqn:E; inversion e.
    eapply closed_unfold_cofix with (narg := narg); eauto.
    unfold unfold_cofix. rewrite E. subst. repeat f_equal.
    eapply closed_cofix_substl_subst_eq; eauto.
  - rewrite !closedn_mkApps in H1 |- *. solve_all.
    unfold cunfold_cofix in e. destruct nth_error as [d | ] eqn:E; inversion e.
    eapply closed_unfold_cofix with (narg := narg); eauto.
    unfold unfold_cofix. rewrite E. subst. repeat f_equal.
    eapply closed_cofix_substl_subst_eq; eauto.
Qed.

Lemma red1_incl {cf : checker_flags} {Σ t t' } :
  closed t ->
  red1 Σ t t' -> PCUICReduction.red1 Σ [] t t'.
Proof.
  intros Hcl Hred.
  induction Hred. all: cbn in *; solve_all.
  1-10: try econstructor; eauto using red1_closed.
  1,2: now rewrite closed_subst; eauto; econstructor; eauto.
  - now rewrite e0 /cstr_arity -e1 -e2.
  - rewrite !tApp_mkApps -!mkApps_app. econstructor. eauto.
    unfold is_constructor. now rewrite nth_error_app2 // Nat.sub_diag.
  - unfold cunfold_cofix in e. destruct nth_error as [d | ] eqn:E; try congruence.
    inversion e; subst.
    econstructor. unfold unfold_cofix. rewrite E. repeat f_equal.
    eapply closed_cofix_substl_subst_eq; eauto. rewrite closedn_mkApps in Hcl. solve_all.
  - unfold cunfold_cofix in e. destruct nth_error as [d | ] eqn:E; try congruence.
    inversion e; subst.
    econstructor. unfold unfold_cofix. rewrite E. repeat f_equal.
    eapply closed_cofix_substl_subst_eq; eauto. rewrite closedn_mkApps in H1. solve_all.
Qed.

Global Hint Constructors value eval : wcbv.
Global Hint Resolve value_final : wcbv.

(* Lemma eval_tApp_Construct {Σ a b ind c u args a'}
  eval Σ a
eval Σ (tApp a b) (mkApps (tConstruct ind c u) (args ++ [a']))
 *)

Lemma red1_eval {Σ : global_env_ext } t t' v : wf Σ ->
  closed t ->
  red1 Σ t t' -> eval Σ t' v -> eval Σ t v.
Proof.
  intros Hwf Hty Hred Heval.
  induction Hred in Heval, v, Hty |- *; eauto with wcbv.
  - inversion Heval; subst; clear Heval. all:cbn in Hty; solve_all. 1-3,6:now econstructor; eauto with wcbv.
    eapply eval_construct; tea. eauto. eapply eval_app_cong; eauto with wcbv.
  - inversion Heval; subst; clear Heval. all:cbn in Hty; solve_all. 1-3,6: now econstructor; eauto with wcbv.
    eapply eval_construct; tea. eauto. eapply eval_app_cong; eauto with wcbv.
  - inversion Heval; subst; clear Heval. all:cbn in Hty; solve_all. all: now econstructor; eauto with wcbv.
  - inversion Heval; subst; clear Heval. all:cbn in Hty; solve_all. all: try now econstructor; eauto with wcbv.
  - eapply eval_iota. eapply eval_mkApps_Construct; tea. now econstructor. unfold cstr_arity. rewrite e0.
    rewrite (PCUICGlobalEnv.declared_minductive_ind_npars d).
    now rewrite -(declared_minductive_ind_npars d) /cstr_arity.
    all:tea. eapply All_All2_refl. solve_all. now eapply value_final.
  - inversion Heval; subst; clear Heval. all:cbn in Hty; solve_all. all: now econstructor; eauto with wcbv.
  - all:cbn in Hty; solve_all. eapply eval_proj; tea.
    eapply value_final. eapply value_app; auto. econstructor; tea. eapply d.
    rewrite e; lia.
  - eapply eval_fix; eauto.
    + eapply value_final. eapply value_app; auto. econstructor.
      rewrite <- closed_unfold_fix_cunfold_eq, e. reflexivity. 2:eauto.
      cbn in Hty. rewrite closedn_mkApps in Hty. solve_all.
    + eapply value_final; eauto.
    + rewrite <- closed_unfold_fix_cunfold_eq, e. reflexivity.
      cbn in Hty. rewrite closedn_mkApps in Hty. solve_all.
      Unshelve. all: now econstructor.
  - destruct p as [[] ?]. eapply eval_cofix_proj; tea.
    eapply value_final, value_app. now constructor. auto.
  - eapply eval_cofix_case; tea.
    eapply value_final, value_app. now constructor. auto.
Qed.

From MetaCoq Require Import PCUICSN.

Lemma WN {no:normalizing_flags} {Σ} {normalisation:NormalisationIn Σ} {t} : wf_ext Σ -> axiom_free Σ ->
  welltyped Σ [] t  -> exists v, squash (eval Σ t v).
Proof.
  intros Hwf Hax Hwt.
  eapply PCUICSN.normalisation_in in Hwt as HSN; eauto.
  induction HSN as [t H IH].
  destruct Hwt as [A HA].
  edestruct progress as [_ [_ [[t' Ht'] | Hval]]]; eauto.
  - eapply red1_incl in Ht' as Hred. 2:{ change 0 with (#|@nil context_decl|). eapply subject_closed. eauto. }
    edestruct IH as [v Hv]. econstructor. eauto.
    econstructor. eapply subject_reduction; eauto.
    exists v. sq. eapply red1_eval; eauto.
    now eapply subject_closed in HA.
  - exists t. sq. eapply value_final; eauto.
Qed.

From MetaCoq Require Import PCUICFirstorder.

Lemma firstorder_value_irred Σ t t' :
  firstorder_value Σ [] t ->
  PCUICReduction.red1 Σ [] t t' -> False.
Proof.
  intros H.
  revert t'. pattern t. revert t H.
  eapply firstorder_value_inds.
  intros i n ui u args pandi Hty Hargs IH Hprop t' Hred.
  eapply red1_mkApps_tConstruct_inv in Hred as (x & -> & Hone).
  solve_all.
  clear - IH Hone. induction IH as [ | ? ? []] in x, Hone |- *.
  - invs Hone.
  - invs Hone; eauto.
Qed.

Definition ws_empty f : ws_context f.
Proof.
  unshelve econstructor.
  exact nil.
  reflexivity.
Defined.

Lemma irred_equal Σ Γ t t' :
  Σ ;;; Γ ⊢ t ⇝ t' ->
  (forall v', PCUICReduction.red1 Σ Γ t v' -> False) ->
  t = t'.
Proof.
  intros Hred Hirred. destruct Hred.
  clear clrel_ctx clrel_src.
  induction clrel_rel.
  - edestruct Hirred; eauto.
  - reflexivity.
  - assert (x = y) as <- by eauto. eauto.
Qed.

Lemma ws_wcbv_standardization {no:normalizing_flags} {Σ} {normalisation:NormalisationIn Σ} {i u args mind} {t v : ws_term (fun _ => false)} : wf_ext Σ -> axiom_free Σ ->
  Σ ;;; [] |- t : mkApps (tInd i u) args ->
  lookup_env Σ (i.(inductive_mind)) = Some (InductiveDecl mind) ->
  @firstorder_ind Σ (firstorder_env Σ) i ->
  closed_red Σ [] t v ->
  (forall v', PCUICReduction.red1 Σ [] v v' -> False) ->
  squash (eval Σ t v).
Proof.
  intros Hwf Hax Hty Hdecl Hfo Hred Hirred.
  destruct (@WN no Σ normalisation t) as (v' & Hv'); eauto.
  1:{ eexists; eauto. }
  sq.
  assert (Σ;;; [] |- t ⇝* v') as Hred' by now eapply wcbeval_red.
  eapply closed_red_confluence in Hred as Hred_. destruct Hred_ as (v'' & H1 & H2).
  2:{ econstructor; eauto. eapply subject_is_open_term. eauto. }
  destruct v as [v Hv].
  assert (v = v'') as <- by (eapply irred_equal; eauto).
  assert (firstorder_value Σ [] v'). {
    eapply firstorder_value_spec; eauto.
    eapply subject_reduction_eval; eauto.
    eapply eval_to_value. eauto.
  }
  enough (v' = v) as -> by eauto.
  eapply irred_equal. eauto.
  intros. eapply firstorder_value_irred; eauto.
Qed.

Lemma wcbv_standardization {no:normalizing_flags} {Σ} {normalisation:NormalisationIn Σ} {i u args mind} {t v : term} : wf_ext Σ -> axiom_free Σ ->
  Σ ;;; [] |- t : mkApps (tInd i u) args ->
  lookup_env Σ (i.(inductive_mind)) = Some (InductiveDecl mind) ->
  @firstorder_ind Σ (firstorder_env Σ) i ->
  red Σ [] t v ->
  (forall v', PCUICReduction.red1 Σ [] v v' -> False) ->
  ∥ eval Σ t v ∥.
Proof.
  intros Hwf Hax Hty Hdecl Hfo Hred Hirred.
  unshelve edestruct @ws_wcbv_standardization.
  1-6: shelve.
  1: exists t; shelve.
  1: exists v; shelve.
  all: sq; eauto.
  cbn.
  econstructor; eauto.
  eapply subject_is_open_term. eauto.
  Unshelve.
  all: rewrite -closed_on_free_vars_none.
  - now eapply subject_closed in Hty.
  - eapply @subject_closed with (Γ := []); eauto.
    eapply subject_reduction; eauto.
Qed.
