(* Distributed under the terms of the MIT license. *)
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
  Proof.
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
  edestruct @inversion_App_size with (H0 := H') as (na' & A' & B' & s_ & Hf' & Ha & HA & Hs1 & Hs2 & Hs3 & HA'''); tea.
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
       wf_local Σ (Γ ,,, predctx) ->
       forall pret : Σ ;;; Γ ,,, predctx |- p.(preturn) : tSort ps,
       P Σ (Γ ,,, predctx) p.(preturn) (tSort ps) ->
       PΓ Σ (Γ ,,, predctx) ->
       is_allowed_elimination Σ ps idecl.(ind_kelim) ->
       ctx_inst Σ Γ (p.(pparams) ++ indices)
         (List.rev (subst_instance p.(puinst) (mdecl.(ind_params) ,,, idecl.(ind_indices)))) ->
       PCUICTyping.ctx_inst P Σ Γ (p.(pparams) ++ indices) 
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
          (Σ ;;; Γ ,,, brctxty.1 |- br.(bbody) : brctxty.2) ×
           (P Σ (Γ ,,, brctxty.1) br.(bbody) brctxty.2) ×
           (Σ ;;; Γ ,,, brctxty.1 |- brctxty.2 : tSort ps) ×
           (P Σ (Γ ,,, brctxty.1) brctxty.2 (tSort ps)))) 0 idecl.(ind_ctors) brs ->
       P Σ Γ (tCase ci p c brs) (mkApps ptm (indices ++ [c]))) ->

  (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (p : projection) (c : term) u
        mdecl idecl cdecl pdecl (isdecl : declared_projection Σ.1 p mdecl idecl cdecl pdecl) args,
      Forall_decls_typing P Σ.1 -> PΓ Σ Γ ->
      Σ ;;; Γ |- c : mkApps (tInd (fst (fst p)) u) args ->
      P Σ Γ c (mkApps (tInd (fst (fst p)) u) args) ->
      #|args| = ind_npars mdecl ->
      let ty := snd pdecl in P Σ Γ (tProj p c) (subst0 (c :: List.rev args) (subst_instance u ty))) ->

  (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (mfix : list (def term)) (n : nat) decl,
      let types := fix_context mfix in
      fix_guard Σ Γ mfix ->
      nth_error mfix n = Some decl ->
      PΓ Σ (Γ ,,, types) ->
      All (fun d => {s & (Σ ;;; Γ |- d.(dtype) : tSort s)%type * P Σ Γ d.(dtype) (tSort s)})%type mfix ->
      All (fun d => (Σ ;;; Γ ,,, types |- d.(dbody) : lift0 #|types| d.(dtype))%type *
          P Σ (Γ ,,, types) d.(dbody) (lift0 #|types| d.(dtype)))%type mfix ->
      wf_fixpoint Σ.1 mfix ->
      P Σ Γ (tFix mfix n) decl.(dtype)) ->

  (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (mfix : list (def term)) (n : nat) decl,
      let types := fix_context mfix in
      cofix_guard Σ Γ mfix ->
      nth_error mfix n = Some decl ->
      PΓ Σ (Γ ,,, types) ->       
      All (fun d => {s & (Σ ;;; Γ |- d.(dtype) : tSort s)%type * P Σ Γ d.(dtype) (tSort s)})%type mfix ->
      All (fun d => (Σ ;;; Γ ,,, types |- d.(dbody) : lift0 #|types| d.(dtype))%type *
          P Σ (Γ ,,, types) d.(dbody) (lift0 #|types| d.(dtype)))%type mfix ->
      wf_cofixpoint Σ.1 mfix ->
      P Σ Γ (tCoFix mfix n) decl.(dtype)) ->

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
 destruct @inversion_Prod_size with (H0 := Hprod) as (s1 & s2 & H1 & H2 & Hs1 & Hs2 & Hsub); [ eauto | ]. 
 eapply X4. 6:eauto. 4: exact HA. all: eauto.
 - intros. eapply (IH _ _ Hf). lia.
 - Unshelve. 2:exact Hf. intros. eapply IH. rewrite H. lia.
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
      wf_local Σ (Γ ,,, predctx) ->
      forall pret : Σ ;;; Γ ,,, predctx |- p.(preturn) : tSort ps,
      P Σ (Γ ,,, predctx) p.(preturn) (tSort ps) ->
      PΓ Σ (Γ ,,, predctx) ->
      is_allowed_elimination Σ ps idecl.(ind_kelim) ->
      PCUICTyping.ctx_inst typing Σ Γ (p.(pparams) ++ indices)
        (List.rev (subst_instance p.(puinst) (mdecl.(ind_params) ,,, idecl.(ind_indices)))) ->
      PCUICTyping.ctx_inst P Σ Γ (p.(pparams) ++ indices) 
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
          (Σ ;;; Γ ,,, brctxty.1 |- br.(bbody) : brctxty.2) ×
          (P Σ (Γ ,,, brctxty.1) br.(bbody) brctxty.2) ×
          (Σ ;;; Γ ,,, brctxty.1 |- brctxty.2 : tSort ps) ×
          (P Σ (Γ ,,, brctxty.1) brctxty.2 (tSort ps)))) 0 idecl.(ind_ctors) brs ->
      P Σ Γ (tCase ci p c brs) (mkApps ptm (indices ++ [c]))) ->
      
    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (p : projection) (c : term) u
          mdecl idecl cdecl pdecl (isdecl : declared_projection Σ.1 p mdecl idecl cdecl pdecl) args,
        Forall_decls_typing P Σ.1 -> PΓ Σ Γ ->
        Σ ;;; Γ |- c : mkApps (tInd (fst (fst p)) u) args ->
        P Σ Γ c (mkApps (tInd (fst (fst p)) u) args) ->
        #|args| = ind_npars mdecl ->
        let ty := snd pdecl in P Σ Γ (tProj p c) (subst0 (c :: List.rev args) (subst_instance u ty))) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (mfix : list (def term)) (n : nat) decl,
        let types := fix_context mfix in
        fix_guard Σ Γ mfix ->
        nth_error mfix n = Some decl ->
        PΓ Σ (Γ ,,, types) ->
        All (fun d => {s & (Σ ;;; Γ |- d.(dtype) : tSort s)%type * P Σ Γ d.(dtype) (tSort s)})%type mfix ->
        All (fun d => (Σ ;;; Γ ,,, types |- d.(dbody) : lift0 #|types| d.(dtype))%type *
            P Σ (Γ ,,, types) d.(dbody) (lift0 #|types| d.(dtype)))%type mfix ->
        wf_fixpoint Σ.1 mfix ->
        P Σ Γ (tFix mfix n) decl.(dtype)) ->

    (forall Σ (wfΣ : wf Σ.1) (Γ : context) (wfΓ : wf_local Σ Γ) (mfix : list (def term)) (n : nat) decl,
        let types := fix_context mfix in
        cofix_guard Σ Γ mfix ->
        nth_error mfix n = Some decl ->
        PΓ Σ (Γ ,,, types) ->
        All (fun d => {s & (Σ ;;; Γ |- d.(dtype) : tSort s)%type * P Σ Γ d.(dtype) (tSort s)})%type mfix ->
        All (fun d => (Σ ;;; Γ ,,, types |- d.(dbody) : lift0 #|types| d.(dtype))%type *
            P Σ (Γ ,,, types) d.(dbody) (lift0 #|types| d.(dtype)))%type mfix ->
        wf_cofixpoint Σ.1 mfix ->
        P Σ Γ (tCoFix mfix n) decl.(dtype)) ->

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
  intros XΓ X X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 Σ wfΣ Γ t T H.
  apply typing_ind_env_app_size; eauto.
Qed.

Local Hint Constructors value red1 : wcbv.


Definition axiom_free Σ :=
  forall c decl, declared_constant Σ c decl -> cst_body decl <> None. (* TODO: consolidate with PCUICConsistency *)

Lemma progress `{cf : checker_flags}: 
  env_prop (fun Σ Γ t T => axiom_free Σ -> Γ = [] -> Σ ;;; Γ |- t : T -> {t' & red1 Σ t t'} + (value t))
           (fun _ _ => True).
Proof with eauto with wcbv; try congruence.
  eapply typing_ind_env...
  - intros Σ wfΣ Γ wfΓ n decl Hdecl _ Hax -> Hty.
    destruct n; inv Hdecl.
  - intros Σ wfΣ Γ _ n b b_ty b' s1 b'_ty _ Hb_ty IHb_ty Hb IHb Hb' IHb' Hax -> H.
    destruct (IHb Hax eq_refl) as [ [t' IH] | IH]; eauto with wcbv.
  - intros Σ wfΣ Γ _ t T B L s _ HT IHT Ht IHt HL Hax -> H.
    induction HL in t, Ht, IHt |- *.
    + cbn. eauto.
    + cbn. eapply IHHL.
      2:{ do 2 (econstructor; eauto). now eapply cumulAlgo_cumulSpec in w. }
      intros _ Happ.
      destruct (IHt Hax eq_refl Ht) as [[t' IH] | IH]; eauto with wcbv.
      assert (Ht' : Σ ;;; [] |- t : tProd na A B) by (econstructor; eauto; now eapply cumulAlgo_cumulSpec in w).
      destruct p0 as [_ [[t' Hstep] | Hval]]; eauto using red1.
      inversion IH as [t' Hatom eq | | f args Hvals Hstuck ]; subst.
      * destruct t; inv Hatom; eauto using red1.
        -- eapply inversion_Sort in Ht' as (? & ? & Ht'); tea.
           eapply ws_cumul_pb_Sort_Prod_inv in Ht'; eauto.
        -- eapply inversion_Prod in Ht' as (? & ? & ? & ? & Ht'); tea.
           eapply ws_cumul_pb_Sort_Prod_inv in Ht'; eauto.
        -- right. eapply value_app with (l := [hd]); eauto.
        -- right. eapply value_app with (l := [hd]); eauto.
        -- destruct (isStuckFix (tFix mfix idx) [hd]) eqn:E.
           ++ right. eapply value_stuck_fix with (args := [hd]); eauto.
           ++ cbn in E. eapply inversion_Fix in Ht' as ([] & ? & Efix & ? & ? & ?); eauto.
              unfold cunfold_fix in E. rewrite Efix in E. cbn in *.
              destruct rarg; inv E.
              left. eexists. eapply red_fix with (argsv := []). econstructor. eauto.
              unfold unfold_fix. now rewrite Efix. todo "mh".
        -- todo "cofix".
      * replace (tApp (mkApps t0 l) hd) with (mkApps t0 (l ++ [hd])) by now rewrite mkApps_app.
        right. eapply value_app; eauto using All_app_inv.
      * replace (tApp (mkApps f args) hd) with (mkApps f (args ++ [hd])) by now rewrite mkApps_app.
        unfold isStuckFix in Hstuck. destruct f; try now inversion Hstuck.
        eapply PCUICValidity.inversion_mkApps in Ht' as (? & Hf & ?).
        eapply inversion_Fix in Hf as ([] & ? & Efix & ? & ? & ?); eauto.
        destruct (isStuckFix (tFix mfix idx) (args ++ [hd])) eqn:E.
        ++ right. eapply value_stuck_fix; eauto using All_app_inv.
        ++ cbn in E. unfold cunfold_fix in E. rewrite Efix in E. cbn in *.
           left. eexists. rewrite mkApps_app. cbn. eapply red_fix.
           eauto. eauto. unfold unfold_fix. rewrite Efix. cbn. repeat f_equal.
           rewrite app_length in E. cbn in E. rewrite plus_comm in E.
           unfold cunfold_fix in Hstuck. rewrite Efix in Hstuck.
           cbn in Hstuck.
           eapply leb_complete in Hstuck.
           eapply leb_complete_conv in E. lia.
           todo "mh".
  - intros Σ wf Γ _ cst u decl Hdecls _ Hdecl Hcons Hax -> H.
    destruct (decl.(cst_body)) as [body | ] eqn:E.
    + eauto with wcbv.
    + red in Hax. eapply Hax in E; eauto.
  - intros Σ wfΣ Γ _ ci p c brs indices ps mdecl idecl Hidecl Hforall _ Heq Heq_context predctx Hwfpred Hcon Hwfl Hreturn IHreturn _.
    intros Helim Hinst Hctxinst Hc IHc Hcof ptm Hwfbranches Hall Hax -> H.
    specialize (IHc Hax eq_refl) as [[t' IH] | IH]; eauto with wcbv.
    eapply PCUICCanonicity.value_canonical in IH; eauto.
    unfold head in IH.
    rewrite (PCUICInduction.mkApps_decompose_app c) in H, Hc |- *.
    destruct (decompose_app c) as [h l]. clear c.
    cbn - [decompose_app] in *.
    destruct h; inv IH.
    + eapply invert_Case_Construct in H as H_; sq; eauto. destruct H_ as (Eq & H_); subst.
      left.
      destruct (nth_error brs n) as [br | ] eqn:E.
      2:{ exfalso. firstorder congruence. }
      assert (#|l| = ci_npar ci + context_assumptions (bcontext br)) as Hl by firstorder congruence.
      clear H_. eapply Construct_Ind_ind_eq' in Hc as (? & ? & ? & ? & _); eauto.
      eexists. eapply red_iota; eauto.
    + todo "cofix".
  - intros Σ wfΣ Γ _ ((i, pars), arg) c u mdecl idecl cdecl pdecl Hcon args Hargs _ Hc IHc
           Hlen ty Hax -> H.
    destruct (IHc Hax eq_refl) as [[t' IH] | IH]; eauto with wcbv; clear IHc.
    eapply PCUICCanonicity.value_canonical in IH; eauto.
    unfold head in IH.
    rewrite (PCUICInduction.mkApps_decompose_app c) in H, Hc |- *.
    destruct (decompose_app c) as [h l]. clear c.
    cbn - [decompose_app] in *.
    destruct h; inv IH.
    + red in Hcon. cbn in *.
      eapply invert_Proj_Construct in H as H_; sq; eauto. destruct H_ as (-> & -> & Hl).
      left. eapply nth_error_Some' in Hl as [x Hx].
      eauto with wcbv.
    + todo "cofix". 
    Unshelve. all: todo "shelved".
Qed.

Lemma red1_closed {cf : checker_flags} {Σ t t'} :
  wf Σ ->
  closed t -> red1 Σ t t' -> closed t'.
Proof.
  intros Hwf Hcl Hred. induction Hred; cbn in *; solve_all.
  all: eauto using closed_csubst, closed_def.
  - eapply closed_iota; eauto. solve_all. solve_all. todo "mh".
  - eauto using closed_arg.
  - rewrite closedn_mkApps in H |- *. solve_all.
    eapply closed_unfold_fix; eauto.
  - rewrite closedn_mkApps in Hcl |- *. solve_all.
    unfold cunfold_cofix in e. destruct nth_error as [d | ] eqn:E; inversion e.
    eapply closed_unfold_cofix with (narg := narg); eauto.
    unfold unfold_cofix. rewrite E. subst. repeat f_equal.
    eapply closed_cofix_substl_subst_eq; eauto.
  - rewrite closedn_mkApps in H1 |- *. solve_all.
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
  - rewrite !tApp_mkApps, <- !mkApps_app. econstructor. eauto.
    unfold is_constructor. now rewrite nth_error_app2, minus_diag.    
  - unfold cunfold_cofix in e. destruct nth_error as [d | ] eqn:E; try congruence.
    inversion e; subst.
    econstructor. unfold unfold_cofix. rewrite E. repeat f_equal.
    eapply closed_cofix_substl_subst_eq; eauto. rewrite closedn_mkApps in Hcl. solve_all.
  - unfold cunfold_cofix in e. destruct nth_error as [d | ] eqn:E; try congruence.
    inversion e; subst.
    econstructor. unfold unfold_cofix. rewrite E. repeat f_equal.
    eapply closed_cofix_substl_subst_eq; eauto. rewrite closedn_mkApps in H1. solve_all.
Qed.

Hint Constructors value eval : wcbv.
Hint Resolve value_final : wcbv.

Lemma red1_eval {Σ : global_env_ext } t t' v : wf Σ ->
  closed t ->
  red1 Σ t t' -> eval Σ t' v -> eval Σ t v.
Proof.
  intros Hwf Hty Hred Heval.
  induction Hred in Heval, v, Hty |- *; eauto with wcbv.
  - inversion Heval; subst; clear Heval. all:cbn in Hty; solve_all. all: now econstructor; eauto with wcbv.
  - inversion Heval; subst; clear Heval. all:cbn in Hty; solve_all. all: now econstructor; eauto with wcbv.
  - inversion Heval; subst; clear Heval. all:cbn in Hty; solve_all. all: now econstructor; eauto with wcbv.
  - inversion Heval; subst; clear Heval. all:cbn in Hty; solve_all. all: try now econstructor; eauto with wcbv. todo "cofix".
  - inversion Heval; subst; clear Heval. all:cbn in Hty; solve_all. all: try now econstructor; eauto with wcbv. todo "cofix".
  - eapply eval_fix; eauto.
    + eapply value_final. econstructor 3; eauto. unfold isStuckFix.
      rewrite <- closed_unfold_fix_cunfold_eq, e. eapply leb_correct; eauto.
      cbn in Hty. rewrite closedn_mkApps in Hty. solve_all.
    + eapply value_final; eauto.
    + rewrite <- closed_unfold_fix_cunfold_eq, e. reflexivity.
      cbn in Hty. rewrite closedn_mkApps in Hty. solve_all.
    Unshelve. all: now econstructor.
Qed.

From MetaCoq Require Import PCUICSN.

Lemma WN {Σ t} : wf_ext Σ -> axiom_free Σ ->
  welltyped Σ [] t  -> exists v, squash (eval Σ t v).
Proof.
  intros Hwf Hax Hwt.
  eapply PCUICSN.normalisation in Hwt as HSN; eauto.
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