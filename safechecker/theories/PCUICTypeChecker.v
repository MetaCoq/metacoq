(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils uGraph.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICNormal PCUICSR
     PCUICGeneration PCUICReflect PCUICEquality PCUICInversion PCUICValidity
     PCUICWeakeningEnvConv PCUICWeakeningEnvTyp
     PCUICWeakeningConv PCUICWeakeningTyp
     PCUICPosition PCUICCumulativity PCUICSafeLemmata PCUICSN
     PCUICPretty PCUICArities PCUICConfluence PCUICSize
     PCUICContextConversion PCUICContextConversionTyp
     PCUICConversion PCUICWfUniverses
     PCUICGlobalEnv PCUICEqualityDec PCUICSigmaCalculus
     (* Used for support lemmas *)
     PCUICInductives PCUICWfUniverses
     PCUICOnFreeVars PCUICWellScopedCumulativity
     PCUICContexts PCUICSubstitution PCUICSpine PCUICInductiveInversion
     PCUICClosed PCUICClosedTyp
     PCUICUnivSubstitutionConv PCUICUnivSubstitutionTyp .

From MetaCoq.SafeChecker Require Import PCUICSafeReduce PCUICErrors
  PCUICSafeConversion PCUICWfReduction PCUICWfEnv.

From Equations Require Import Equations.
Require Import ssreflect ssrbool.

Local Set Keyed Unification.
Set Equations Transparent.

Import MCMonadNotation.

(** It otherwise tries [auto with *], very bad idea. *)
Ltac Coq.Program.Tactics.program_solve_wf ::= 
  match goal with 
  | |- @Wf.well_founded _ _ => auto with subterm wf
  | |- ?T => match type of T with
                | Prop => auto
                end
  end.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

Lemma spine_subst_smash_inv {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} 
  {Γ inst Δ s} :
  wf_local Σ (Γ ,,, Δ) ->
  spine_subst Σ Γ inst s (smash_context [] Δ) ->
  ∑ s', spine_subst Σ Γ inst s' Δ.
Proof.
  intros wf.
  move/spine_subst_ctx_inst.
  intros c. eapply ctx_inst_smash in c.
  unshelve epose proof (ctx_inst_spine_subst _ c); auto.
  now eexists.
Qed.

Lemma isType_mkApps_Ind_smash {cf Σ} {wfΣ : wf Σ} {ind mdecl idecl Γ puinst args} :
  declared_inductive Σ ind mdecl idecl ->
  consistent_instance_ext Σ (ind_universes mdecl) puinst ->
  spine_subst Σ Γ args (List.rev args) (smash_context [] (ind_params mdecl ,,, ind_indices idecl)@[puinst]) ->
  Σ ;;; Γ |- mkApps (tInd ind puinst) args : tSort (subst_instance puinst (ind_sort idecl)).
Proof.
  intros isdecl cu sp.
  eapply spine_subst_smash_inv in sp as [s hs].
  - eapply isType_mkApps_Ind; tea.
  - eapply weaken_wf_local; tea.
    apply sp.
    eapply on_minductive_wf_params_indices_inst; tea.
Qed.

Lemma isType_mkApps_Ind_smash_inv {cf:checker_flags} {Σ Γ ind u args} (wfΣ : wf Σ.1)
  {mdecl idecl} (declm : declared_inductive Σ.1 ind mdecl idecl) :
  wf_local Σ Γ ->
  isType Σ Γ (mkApps (tInd ind u) args) ->
  spine_subst Σ Γ args (List.rev args) (smash_context [] (ind_params mdecl ,,, ind_indices idecl)@[u]) ×
  consistent_instance_ext Σ (ind_universes mdecl) u.
Proof.
  move=> wfΓ isType.
  destruct isType as [s Hs].
  eapply invert_type_mkApps_ind in Hs as [tyargs cu]; eauto.
  set (decli' := on_declared_inductive declm).
  rename declm into decli.
  destruct decli' as [declm decli'].
  pose proof (decli'.(onArity)) as ar. 
  rewrite decli'.(ind_arity_eq) in tyargs, ar.
  hnf in ar. destruct ar as [s' ar].
  rewrite -it_mkProd_or_LetIn_app in ar tyargs.
  rewrite !subst_instance_it_mkProd_or_LetIn in tyargs.
  simpl in tyargs.
  eapply arity_typing_spine in tyargs as [argslen leqs [instsubst sp]] => //.
  split; auto.
  now eapply spine_subst_smash in sp.
Qed.

Lemma compare_global_instance_sound {cf Σ} {wfΣ : wf_ext Σ} gr napp 
  (Hφ : on_udecl Σ.1 Σ.2)
  (G : universes_graph) (HG : is_graph_of_uctx G (global_ext_uctx Σ)) :
  subrelation (compare_global_instance Σ (check_eqb_universe G) (check_leqb_universe G) gr napp) 
    (R_global_instance Σ (eq_universe Σ) (leq_universe Σ) gr napp).
Proof. apply compare_global_instance_impl; tc; intros x y.
  - eapply (check_eqb_universe_spec' _ (global_ext_uctx Σ)) => //.
    now eapply wf_ext_global_uctx_invariants.
    cbn. eapply wfΣ.
  - eapply (check_leqb_universe_spec' _ (global_ext_uctx Σ)) => //.
    now eapply wf_ext_global_uctx_invariants.
    cbn. eapply wfΣ.
Qed.

Section Typecheck.
  Context {cf : checker_flags} {Σ : global_env_ext} (HΣ : ∥ wf Σ ∥)
          (Hφ : ∥ on_udecl Σ.1 Σ.2 ∥)
          (G : universes_graph) (HG : is_graph_of_uctx G (global_ext_uctx Σ)).

  (* We get stack overflow on Qed after Equations definitions when this is transparent *)
  Opaque reduce_stack_full.

  Local Definition HeΣ : ∥ wf_ext Σ ∥.
  Proof.
    destruct HΣ, Hφ; now constructor.
  Defined.

  Notation hnf := (hnf HeΣ).
  
  (* replaces convert and convert_leq*)
  Equations convert (le : conv_pb) Γ t u
          (ht : welltyped Σ Γ t) (hu : welltyped Σ Γ u)
    : typing_result (∥ Σ ;;; Γ ⊢ t ≤[le] u ∥) :=
    convert le Γ t u ht hu
      with inspect (eqb_termp Σ G le t u) := {
        | @exist true He := ret _ ; 
        | @exist false He with
          inspect (isconv_term Σ HΣ Hφ G HG Γ le t ht u hu) := {
          | @exist ConvSuccess Hc := ret _ ;
          | @exist (ConvError e) Hc :=
            let t' := hnf Γ t ht in
            let u' := hnf Γ u hu in
            raise (NotCumulSmaller false G Γ t u t' u' e)
      }}.
  Next Obligation.
    symmetry in He; eapply eqb_termp_napp_spec in He; tea.
    sq.
    constructor; auto ; fvs.
  Qed.
  Next Obligation.
    now symmetry in Hc; apply isconv_term_sound in Hc.
  Qed.

  Definition wt_decl (Σ : global_env_ext) Γ d :=
    match d with
    | {| decl_body := Some b; decl_type := ty |} => 
      welltyped Σ Γ ty /\ welltyped Σ Γ b
    | {| decl_body := None; decl_type := ty |} =>
      welltyped Σ Γ ty
    end.

  Section InferAux.
    Variable (infer : forall Γ (HΓ : ∥ wf_local Σ Γ ∥) (t : term),
                 typing_result ({ A : term & ∥ Σ ;;; Γ |- t : A ∥ })).

    Equations infer_type Γ (HΓ : ∥ wf_local Σ Γ ∥) t
      : typing_result ({u : Universe.t & ∥ Σ ;;; Γ |- t : tSort u ∥}) :=
    infer_type Γ HΓ t :=
      tx <- infer Γ HΓ t ;;
      u <- reduce_to_sort HeΣ Γ tx.π1 _ ;;
      ret (u.π1; _).
    Next Obligation.
      eapply validity_wf; eassumption.
    Defined.
    Next Obligation.
      sq.
      eapply type_reduction; tea.
      exact X.
    Defined.

    Equations infer_isType Γ (HΓ : ∥wf_local Σ Γ ∥) T : typing_result (∥ isType Σ Γ T ∥) :=
      infer_isType Γ HΓ T :=
      tx <- infer_type Γ HΓ T ;;
      ret _.
    Next Obligation.
      sq. now eexists.
    Defined.

    Equations check_wftype Γ (HΓ : ∥wf_local Σ Γ ∥) t A (hA : ∥ isType Σ Γ A ∥)
      : typing_result (∥ Σ ;;; Γ |- t : A ∥) :=
      check_wftype Γ HΓ t A hA :=
      A' <- infer Γ HΓ t ;;
      X <- convert Cumul Γ A'.π1 A _ _ ;;
      ret _.
    Next Obligation. now eapply validity_wf. Qed.
    Next Obligation. destruct hA; now apply wat_welltyped. Qed.
    Next Obligation.
      sq. now eapply type_equality.
    Qed.
    
    (* Program Definition infer_scheme Γ HΓ t :
      typing_result (∑ ctx u, ∥ Σ ;;; Γ |- t : mkAssumArity ctx u ∥) :=
      '(T; p) <- infer Γ HΓ t;;
      match reduce_to_arity HeΣ Γ T _ with
      | inleft car => ret (conv_ar_context car; conv_ar_univ car; _)
      | inright _ => TypeError (NotAnArity T)
      end.
    Next Obligation.
      intros; subst.
      cbn in *.
      eapply validity_wf; eauto.
    Qed.
    Next Obligation.
      destruct car as [? ? [r]]. cbn.
      clear Heq_anonymous. sq.
      eapply type_reduction; eauto. exact r.
    Qed. *)

    Lemma sq_wfl_nil : ∥ wf_local Σ [] ∥.
    Proof.
     repeat constructor.
    Qed.

    Equations check_context Γ : typing_result (∥ wf_local Σ Γ ∥)
    := 
      check_context [] := ret sq_wfl_nil ;
      check_context ({| decl_body := None; decl_type := A |} :: Γ) :=
         HΓ <- check_context Γ ;;
         XX <- infer_type Γ HΓ A ;;
         ret _ ;
       check_context ({| decl_body := Some t; decl_type := A |} :: Γ) :=
         HΓ <- check_context Γ ;;
         XX <- infer_type Γ HΓ A ;;
         XX <- check_wftype Γ HΓ t A _ ;;
         ret _.
    Next Obligation.
      sq. 
      eexists. eassumption.
    Qed.
    Next Obligation.
      sq. econstructor; tea.
      econstructor ; eassumption.
    Qed.
    Next Obligation.
      sq. econstructor; tas. econstructor; eassumption.
    Qed.
 
    Lemma sq_wf_local_app {Γ Δ} : ∥ wf_local Σ Γ ∥ -> ∥ wf_local_rel Σ Γ Δ ∥ -> ∥ wf_local Σ (Γ ,,, Δ) ∥.
    Proof.
      intros. sq. now apply wf_local_app.
    Qed. 

    Equations check_context_rel Γ (wfΓ : ∥ wf_local Σ Γ ∥) (Δ : context) :
      typing_result (∥ wf_local_rel Σ Γ Δ ∥) :=
      check_context_rel Γ wfΓ [] := ret (sq localenv_nil) ;
      check_context_rel Γ wfΓ ({| decl_body := None; decl_type := A |} :: Δ) :=
        wfΔ <- check_context_rel Γ wfΓ Δ ;;
        XX <- infer_isType (Γ ,,, Δ) (sq_wf_local_app wfΓ wfΔ) A ;;
        ret _ ;
      check_context_rel Γ wfΓ ({| decl_body := Some t; decl_type := A |} :: Δ) :=
        wfΔ <- check_context_rel Γ wfΓ Δ;;
        Aty <- infer_isType (Γ ,,, Δ) (sq_wf_local_app wfΓ wfΔ) A ;;
        XX <- check_wftype (Γ ,,, Δ) (sq_wf_local_app wfΓ wfΔ) t A Aty ;;
        ret _.
    Next Obligation.
      sq. constructor; auto.
    Qed.
    Next Obligation.
      sq. constructor; auto.
    Qed.

    Equations check_equality_decl (le : conv_pb) Γ d d'
      (wtd : wt_decl Σ Γ d) (wtd' : wt_decl Σ Γ d')
      : typing_result (∥ equality_open_decls le Σ Γ d d' ∥) :=
      check_equality_decl le Γ
        {| decl_name := na; decl_body := Some b; decl_type := ty |}
        {| decl_name := na'; decl_body := Some b'; decl_type := ty' |}
        wtd wtd' :=
        eqna <- check_eq_true (eqb_binder_annot na na') (Msg "Binder annotations do not match") ;;
        cumb <- convert Conv Γ b b' _ _ ;;
        cumt <- convert le Γ ty ty' _ _ ;;
        ret _ ;
      check_equality_decl le Γ
      {| decl_name := na; decl_body := None; decl_type := ty |}
      {| decl_name := na'; decl_body := None; decl_type := ty' |}
      wtd wtd' :=
      eqna <- check_eq_true (eqb_binder_annot na na') (Msg "Binder annotations do not match") ;;
      cumt <- convert le Γ ty ty' _ _ ;;
      ret _ ;
    check_equality_decl le Γ _ _ _ _ :=
      raise (Msg "While checking cumulativity of contexts: declarations do not match").
    Next Obligation.
      sq.
      destruct le ; cbn in *.
      all: constructor ; pcuics.
      all: now apply eqb_binder_annot_spec.
    Qed.
    Next Obligation.
      sq.
      destruct le ; cbn in *.
      all: constructor; pcuics.
      all: now apply eqb_binder_annot_spec.
    Qed.

    Lemma context_cumulativity_welltyped {Σ'} (wfΣ' : wf Σ') {le Γ Γ' t} : 
      welltyped Σ' Γ t ->
      Σ' ⊢ Γ' ≤[le] Γ ->
      wf_local Σ' Γ' ->
      welltyped Σ' Γ' t.
    Proof.
      intros [s Hs] cum wfΓ'; exists s; eapply closed_context_cumulativity; eauto.
    Qed.

    Lemma context_cumulativity_wt_decl {Σ'} (wfΣ' : wf Σ') {le Γ Γ' d} :
      wt_decl Σ' Γ d ->
      Σ' ⊢ Γ' ≤[le] Γ ->
      wf_local Σ' Γ' ->
      wt_decl Σ' Γ' d.
    Proof.
      destruct d as [na [b|] ty]; simpl; intuition pcuics.
      all: eapply context_cumulativity_welltyped ; pcuics.
    Qed.

    Lemma cumul_decls_irrel_sec Γ Γ' d d' :
      cumul_decls Σ Γ Γ d d' ->
      cumul_decls Σ Γ Γ' d d'.
    Proof.
      intros cum; depelim cum; intros; constructor; auto.
    Qed.
    
    Lemma conv_decls_irrel_sec Γ Γ' d d' :
      conv_decls Σ Γ Γ d d' ->
      conv_decls Σ Γ Γ' d d'.
    Proof.
      intros cum; depelim cum; intros; constructor; auto.
    Qed.

    Lemma inv_wf_local Γ d :
      wf_local Σ (Γ ,, d) ->
      wf_local Σ Γ * wt_decl Σ Γ d.
    Proof.
      intros wfd; depelim wfd; split; simpl; pcuic.
      now exists t.
    Qed.

    Lemma cumul_ctx_rel_cons {Γ Δ Δ' d d'} (c : cumul_ctx_rel Σ Γ Δ Δ') 
      (p : cumul_decls Σ (Γ,,, Δ) (Γ ,,, Δ') d d') : 
      cumul_ctx_rel Σ Γ (Δ ,, d) (Δ' ,, d').
    Proof.
      destruct d as [na [b|] ty], d' as [na' [b'|] ty']; try constructor; auto.
    Qed.
    
    Lemma context_equality_rel_cons {le Γ Δ Δ' d d'} (c : context_equality_rel le Σ Γ Δ Δ') 
      (p : equality_open_decls le Σ (Γ,,, Δ) d d') : 
      context_equality_rel le Σ Γ (Δ ,, d) (Δ' ,, d').
    Proof.
      destruct c. split; auto.
      destruct d as [na [b|] ty], d' as [na' [b'|] ty']; try constructor; auto.
    Qed.

    Equations check_equality_ctx (le : conv_pb) Γ Δ Δ'
      (wfΔ : ∥ wf_local Σ (Γ ,,, Δ) ∥) (wfΔ' : ∥ wf_local Σ (Γ ,,, Δ') ∥) : 
      typing_result (∥ context_equality_rel le Σ Γ Δ Δ' ∥) :=
      check_equality_ctx le Γ [] [] _ _ := ret _ ;
      check_equality_ctx le Γ (decl :: Δ) (decl' :: Δ') wfΔ wfΔ' :=
        cctx <- check_equality_ctx le Γ Δ Δ' _ _ ;;
        cdecl <- check_equality_decl le (Γ ,,, Δ) decl decl' _ _ ;;
        ret _ ;
      check_equality_ctx le Γ _ _ _ _ :=
        raise (Msg "While checking cumulativity of contexts: contexts do not have the same length").
      Next Obligation.
        sq.
        split.
        * fvs.
        * constructor.
      Qed.
      Next Obligation.
        sq; now depelim wfΔ.
      Qed.
      Next Obligation.
        sq; now depelim wfΔ'.
      Qed.
      Next Obligation.
        sq.
        depelim wfΔ; simpl.
        destruct l; eexists; eauto.
        destruct l; split; eexists; eauto.
      Qed.
      Next Obligation.
        sq.
        simpl in *.
        eapply inv_wf_local in wfΔ as [wfΔ wfd].
        eapply inv_wf_local in wfΔ' as [wfΔ' wfd'].
        eapply context_cumulativity_wt_decl.
        all:pcuics.
        apply context_equality_rel_app.
        eassumption.
      Qed.
      Next Obligation.
        sq.
        eapply inv_wf_local in wfΔ as [wfΔ wfd].
        eapply inv_wf_local in wfΔ' as [wfΔ' wfd'].
        now apply context_equality_rel_cons.
      Qed.

    Equations check_alpha_equality_ctx Δ Δ'
      : typing_result (∥ eq_context_gen eq eq Δ Δ' ∥) :=
      check_alpha_equality_ctx Δ Δ' with
        inspect (forallb2 (bcompare_decls eqb eqb) Δ Δ') :=  {
      | @exist true e := ret (sq _) ; 
      | @exist false e := raise (Msg "While checking alpha-conversion of contexts: contexts differ")
      }.
    Next Obligation.
      move: e.
      elim: reflect_eq_ctx => //.
    Qed.

    (* Equations infer_terms Γ (wfΓ : ∥ wf_local Σ Γ ∥) ts
      : typing_result (∥ All (welltyped Σ Γ) ts ∥) :=
      match ts with
      | t :: ts =>
        checkt <- infer Γ wfΓ t ;;
        convts <- infer_terms Γ wfΓ ts ;;
        ret _
      | [] => ret (sq All_nil)
      end.
    Next Obligation.
      sq. constructor; auto. now exists checkt.
    Qed. *)

    Lemma assumption_context_subst_telescope s k Γ : 
      assumption_context Γ -> assumption_context (subst_telescope s k Γ).
    Proof.
      rewrite /subst_telescope /mapi. intros ass; generalize 0.
      induction ass; cbn; constructor; auto.
    Qed.
    
    Lemma assumption_context_rev Γ : 
      assumption_context Γ -> assumption_context (List.rev Γ).
    Proof.
      intros ass; induction ass; cbn; try constructor; auto.
      eapply assumption_context_app_inv => //. repeat constructor.
    Qed.

    Equations check_inst Γ Δ (wfΓ : ∥ wf_local Σ (Γ ,,, List.rev Δ) ∥) (HΔ : assumption_context Δ) ts : 
      typing_result (∥ ctx_inst Σ Γ ts Δ ∥) by struct ts :=
    check_inst Γ [] _ _ [] := ret _ ;
    check_inst Γ
      ({|decl_name := na ; decl_body := Some ; decl_type := T|} :: Δ)
      _ _ _ :=
        False_rect _ _ ;
    check_inst Γ
      ({|decl_name := na ; decl_body := None ; decl_type := T|} :: Δ)
      wfΓ HΔ (t :: ts) :=
        checkt <- check_wftype Γ _ t T _ ;;
        subs <- check_inst Γ (subst_telescope [t] 0 Δ) _ _ ts ;;
        ret _ ;
    check_inst _ _ _ _ _ := raise (Msg "While checking a substitution: not of the right length").
    Next Obligation.
      sq. constructor; auto.
    Qed.
    Next Obligation.
      now sq.
    Qed.
    Next Obligation.
      sq.
      now eapply All_local_env_app_inv in wfΓ.
    Qed.
    Next Obligation.
      sq. eapply All_local_env_app_inv in wfΓ as [wΓ wΔ].
      eapply All_local_env_app_inv in wΔ as [wt _]. now depelim wt. 
    Qed.
    Next Obligation.
      sq. rewrite -subst_context_rev_subst_telescope.
      eapply substitution_wf_local. eapply subslet_ass_tip; tea.
      rewrite app_context_assoc in wfΓ. exact wfΓ.
    Qed.
    Next Obligation.
      sq. depelim HΔ. now apply assumption_context_subst_telescope.
    Qed.
    Next Obligation.
      sq. 
      constructor ; auto.
    Qed.

    Equations check_equality_terms Γ ts ts' (wts : ∥ All (welltyped Σ Γ) ts ∥) (wts' : ∥ All (welltyped Σ Γ) ts' ∥) : 
      typing_result (∥ equality_terms Σ Γ ts ts' ∥) :=
    check_equality_terms Γ [] [] _ _ := ret _ ;
    check_equality_terms Γ (t :: ts) (t' :: ts') wts wts' :=
      convt <- convert Conv Γ t t' _ _ ;;
      convts <- check_equality_terms Γ ts ts' _ _ ;;
      ret _ ;
    check_equality_terms Γ _ _ _ _ := raise (Msg "While checking conversion of terms: lists do not have the same length").
    Next Obligation.
      sq; now depelim wts.
    Qed.
    Next Obligation.
      sq; now depelim wts'.
    Qed.
    Next Obligation.
      sq; now depelim wts.
    Qed.
    Next Obligation.
      sq; now depelim wts'.
    Qed.
    Next Obligation.
      sq. constructor; auto.
    Qed.

  End InferAux.

  Equations lookup_ind_decl ind
    : typing_result
        ({decl & {body & declared_inductive (fst Σ) ind decl body}}) :=
  lookup_ind_decl ind with
    inspect (lookup_env (fst Σ) ind.(inductive_mind)) := {
      | @exist (Some (InductiveDecl decl)) _ 
          with inspect (nth_error decl.(ind_bodies) ind.(inductive_ind)) := {
            | @exist (Some body) _ => ret (decl; body; _)
            | @exist None _ => raise (UndeclaredInductive ind)
          };
      | @exist _ _ := raise (UndeclaredInductive ind) ;
      }.
  Next Obligation.
    now split.
  Defined.

  Equations check_consistent_instance uctx u
    : typing_result (consistent_instance_ext Σ uctx u) :=
  check_consistent_instance (Monomorphic_ctx _) u :=
    check_eq_nat #|u| 0 (Msg "monomorphic instance should be of length 0") ;
  check_consistent_instance (Polymorphic_ctx (inst, cstrs)) u
    with inspect (AUContext.repr (inst, cstrs)) := {
    | @exist (inst', _) _
      with inspect (check_constraints G (subst_instance_cstrs u cstrs)) := {
        | @exist false _ := raise (Msg "ctrs not satisfiable") ;
        | @exist true _ :=
            check_eq_true (forallb (fun l => LevelSet.mem l (uGraph.wGraph.V G)) u)
              (Msg "undeclared level in instance") ;;
            X <- check_eq_nat #|u| #|inst'|
              (Msg "instance does not have the right length");;ret (conj _ _)
    }}.
  Next Obligation.
    eapply forallb_All in i. eapply All_forallb'; tea.
    clear -cf HG. intros x; simpl. now apply is_graph_of_uctx_levels.
  Qed.
  Next Obligation.
    repeat split.
    - now rewrite mapi_length in X.
    - eapply check_constraints_spec; eauto.
  Qed.

  (* Obligation Tactic := Program.Tactics.program_simplify ; eauto 2. *)
  
  Equations check_is_allowed_elimination (u : Universe.t) (al : allowed_eliminations) :
    typing_result (is_allowed_elimination Σ u al) :=
  check_is_allowed_elimination u IntoSProp
    with inspect (Universe.is_sprop u) := {
      | @exist true e := Checked _ ;
      | @exist false _ := TypeError (Msg "Cannot eliminate over this sort")
    } ;
  check_is_allowed_elimination u IntoPropSProp
    with inspect (is_propositional u) := {
      | @exist true _ := Checked _ ;
      | @exist false _ := TypeError (Msg "Cannot eliminate over this sort")
    };
  check_is_allowed_elimination u IntoSetPropSProp 
    with inspect (is_propositional u || check_eqb_universe G u Universe.type0) := {
      | @exist true _ := Checked _ ;
      | @exist false _ := TypeError (Msg "Cannot eliminate over this sort")
    } ;
  check_is_allowed_elimination u IntoAny := Checked _.
  Next Obligation.
    unfold is_allowed_elimination, is_allowed_elimination0.
    destruct check_univs; auto.
    intros val sat.
    symmetry in e.
    apply is_sprop_val with (v := val) in e.
    now rewrite e.
  Qed.
  Next Obligation.
    unfold is_allowed_elimination, is_allowed_elimination0.
    destruct check_univs; auto.
    intros val sat.
    unfold is_propositional in *.
    destruct Universe.is_prop eqn:prop.
    - apply is_prop_val with (v := val) in prop; rewrite prop; auto.
    - destruct Universe.is_sprop eqn:sprop.
      + apply is_sprop_val with (v := val) in sprop; rewrite sprop; auto.
      + discriminate.
  Qed.
  Next Obligation.
    unfold is_allowed_elimination, is_allowed_elimination0.
    destruct check_univs eqn:cu; auto.
    intros val sat.
    unfold is_propositional in *.
    destruct Universe.is_prop eqn:prop.
    - apply is_prop_val with (v := val) in prop; rewrite prop; auto.
    - destruct Universe.is_sprop eqn:sprop.
      + apply is_sprop_val with (v := val) in sprop; rewrite sprop; auto.
      + destruct check_eqb_universe eqn:check; [|discriminate].
        eapply check_eqb_universe_spec' in check; eauto.
        * unfold eq_universe, eq_universe0 in check.
          rewrite cu in check.
          specialize (check val sat).
          now rewrite check.
        * destruct HΣ, Hφ.
          now apply wf_ext_global_uctx_invariants.
        * destruct HΣ, Hφ.
          now apply global_ext_uctx_consistent.
  Qed.
  Next Obligation.
    unfold is_allowed_elimination, is_allowed_elimination0.
    destruct check_univs; auto.
  Qed.

  Notation wt_brs Γ ci mdecl idecl p ps ptm ctors brs n := 
    (∥ All2i (fun i cdecl br =>
      let brctxty := case_branch_type ci.(ci_ind) mdecl idecl p br ptm i cdecl in
      All2 (compare_decls eq eq) br.(bcontext) (cstr_branch_context ci mdecl cdecl) ×
        Σ ;;; Γ ,,, brctxty.1 |- br.(bbody) : brctxty.2 ×
        Σ ;;; Γ ,,, brctxty.1 |- brctxty.2 : tSort ps)
      n ctors brs ∥).

  Section check_brs.
    Context (infer : forall (Γ : context) (HΓ : ∥ wf_local Σ Γ ∥) (t : term), typing_result ({ A : term & ∥ Σ ;;; Γ |- t : A ∥ }))
     (Γ : context) (wfΓ : ∥ wf_local Σ Γ ∥) (ps : Universe.t)
     (ci : case_info) (mdecl : mutual_inductive_body)
     (idecl : one_inductive_body) (p : predicate term) (args : list term).
     
    Context (isdecl : declared_inductive Σ ci mdecl idecl).
    Context (hty : ∥ isType Σ Γ (mkApps (tInd ci (puinst p)) (pparams p ++ args)) ∥).
    Context (wfp : wf_predicate mdecl idecl p).
    Context (predctx := case_predicate_context ci mdecl idecl p).
    Context (wfpret : ∥ Σ;;; Γ,,, predctx |- preturn p : tSort ps ∥).
    Context (ptm := it_mkLambda_or_LetIn predctx (preturn p)).
    Context (hpctx : ∥ All2 (compare_decls eq eq) (pcontext p)
          (ind_predicate_context ci mdecl idecl) ∥).
             
    Lemma branch_helper n cdecl ctors br
      (isdecl' : ∥ Alli (fun i cdecl => declared_constructor Σ (ci, i) mdecl idecl cdecl) n (cdecl :: ctors) ∥) : 
      ∥ eq_context_gen eq eq (bcontext br) (cstr_branch_context ci mdecl cdecl) ∥ ->
      ∥ wf_branch cdecl br ×
      let brctxty := case_branch_type ci.(ci_ind) mdecl idecl p br ptm n cdecl in
      wf_local Σ (Γ,,, brctxty.1) × Σ;;; Γ,,, brctxty.1 |- brctxty.2 : tSort ps ∥.
    Proof.
      intros; sq.
      depelim isdecl'.
      have wfbr : wf_branch cdecl br.
      { do 2 red.
        unfold cstr_branch_context, expand_lets_ctx, expand_lets_k_ctx in H.
        move/eq_context_gen_binder_annot: H.
        now do 3 move/eq_annots_fold. }
      destruct (wf_case_branch_type ps args isdecl hty wfp wfpret hpctx _ _ _ d wfbr).
      intuition auto.
    Qed.

    Obligation Tactic := intros.

    Equations check_branches (n : nat) (ctors : list constructor_body)
      (brs : list (branch term)) 
      (isdecl : ∥ Alli (fun i cdecl => declared_constructor Σ (ci, i) mdecl idecl cdecl) n ctors ∥)
      : typing_result (wt_brs Γ ci mdecl idecl p ps ptm ctors brs n) by struct brs := 
      check_branches n [] [] i := ret _ ;
      check_branches n (cdecl :: cdecls) (br :: brs) i :=
        let brctxty := case_branch_type ci.(ci_ind) mdecl idecl p br ptm n cdecl in
        check_eq_bcontext <- check_alpha_equality_ctx br.(bcontext) (cstr_branch_context ci mdecl cdecl) ;;
        Z <- check_wftype infer (Γ ,,, brctxty.1) _ br.(bbody) brctxty.2 _ ;;
        X <- check_branches (S n) cdecls brs _ ;;
        ret (t:=wt_brs Γ ci mdecl idecl p ps ptm (cdecl :: cdecls) (br :: brs) n) _ ;
      check_branches n _ _ _ := raise (Msg "wrong number of branches").
    Next Obligation.
      sq.
      now constructor.
    Qed.
    Next Obligation.
      cbn in *.
      eapply branch_helper in i; tea.
      sq.
      now destruct i as [? []].
    Defined.
    Next Obligation.
      eapply branch_helper in i; tea.
      sq. destruct i as [? []].
      now exists ps.
    Qed.
    Next Obligation.
      sq. now depelim i.
    Qed.
    Next Obligation.
      eapply branch_helper in i; tea.
      sq. constructor.
      split.
      * now eapply All2_fold_All2 in check_eq_bcontext.
      * destruct i as [? []].
        split; auto.
      * apply X.
    Defined.
    End check_brs.

  Lemma eq_context_gen_wf_predicate p ci mdecl idecl :
    #|pparams p| = ind_npars mdecl ->
    eq_context_gen eq eq (pcontext p) (ind_predicate_context ci mdecl idecl) ->
    wf_predicate mdecl idecl p.
  Proof.
    intros eqp e.
    do 2 red. split => //.
    eapply eq_context_gen_binder_annot in e.
    rewrite /ind_predicate_context in e.
    rewrite /idecl_binder.
    destruct (forget_types (pcontext p)); depelim e; cbn in *.
    constructor. now cbn.
    now do 2 eapply (proj1 (eq_annots_fold _ _ _)) in e.
  Qed.

  Lemma eq_context_gen_wf_branch ci mdecl cdecl br :
    eq_context_gen eq eq (bcontext br) (cstr_branch_context ci mdecl cdecl) ->
    wf_branch cdecl br.
  Proof.
    intros e.
    do 2 red. 
    eapply eq_context_gen_binder_annot in e.
    rewrite /cstr_branch_context in e.
    now do 3 eapply (proj1 (eq_annots_fold _ _ _)) in e.
  Qed.

  Section check_mfix.
  Context (infer : forall (Γ : context) (HΓ : ∥ wf_local Σ Γ ∥) (t : term), typing_result ({ A : term & ∥ Σ ;;; Γ |- t : A ∥ }))
     (Γ : context) (wfΓ : ∥ wf_local Σ Γ ∥).

  Equations check_mfix_types (mfix : mfixpoint term)
  : typing_result (∥ All (fun x => isType Σ Γ (dtype x)) mfix ∥) :=
    check_mfix_types [] := ret (sq All_nil) ;
    check_mfix_types (def :: mfix) :=
  (* probably not tail recursive but needed so that next line terminates *)
      check_mfix_types mfix ;;
      infer_type infer Γ wfΓ (dtype def) ;;
      ret _.
  Next Obligation.
    sq.
    constructor ; [eexists|..] ; eassumption.
  Qed.

  Equations check_mfix_bodies
    (mfix : mfixpoint term)
    (wf_types : ∥ All (fun x => isType Σ Γ (dtype x)) mfix ∥)
    (Δ : context)
    (wfΔ : ∥ wf_local Σ (Γ,,,Δ) ∥)
    : typing_result (∥ All (fun d =>
        Σ ;;; Γ ,,, Δ |-
          dbody d : (lift0 #|Δ|) (dtype d)) mfix∥) :=
    check_mfix_bodies [] _ _ _ := ret (sq All_nil) ;
    check_mfix_bodies (def :: mfix) wf_types Δ wfΔ :=
      check_mfix_bodies mfix _ Δ wfΔ ;;
      check_wftype infer (Γ ,,, Δ) _ (dbody def)
        (lift0 #|Δ| (dtype def)) _ ;;
      ret _.
  Next Obligation.
    sq.
    now inversion wf_types.
  Qed.
  Next Obligation.
    sq.
    apply isType_lift ; tea.
    - len.
    - rewrite skipn_all_app.
      now inversion wf_types.
  Qed.
  Next Obligation.
    sq.
    constructor ; tea.
  Qed.
  End check_mfix.


  Lemma chop_firstn_skipn {A} n (l : list A) : chop n l = (firstn n l, skipn n l).
  Proof.
    induction n in l |- *; destruct l; simpl; auto.
    now rewrite IHn skipn_S.
  Qed.

  Lemma ctx_inst_wt Γ s Δ : ctx_inst Σ Γ s Δ -> All (welltyped Σ Γ) s.
  Proof.
    induction 1; try constructor; auto.
    now exists t.
  Qed.

  Equations infer (Γ : context) (HΓ : ∥ wf_local Σ Γ ∥) (t : term)
  : typing_result ({ A : term & ∥ Σ ;;; Γ |- t : A ∥ }) by struct t :=

  infer Γ HΓ (tRel n)
    with inspect (nth_error Γ n) := {
      | exist (Some c) e => ret ((lift0 (S n)) (decl_type c); _) ;
      | exist None _ => raise (UnboundRel n)
    } ;

  infer Γ HΓ (tVar n) := raise (UnboundVar n) ;

  infer Γ HΓ (tEvar ev _) := raise (UnboundEvar ev) ;

  infer Γ HΓ (tSort u) :=
    check_eq_true (wf_universeb Σ u)
                (Msg ("Sort contains an undeclared level " ^ string_of_sort u));;
    ret (tSort (Universe.super u); _) ;

  infer Γ HΓ (tProd na A B) :=
    s1 <- infer_type infer Γ HΓ A ;;
    s2 <- infer_type infer (Γ ,, vass na A) _ B ;;
    ret (tSort (Universe.sort_of_product s1.π1 s2.π1); _) ;

  infer Γ HΓ (tLambda na A t) :=
    s1 <- infer_type infer Γ HΓ A ;;
    B <- infer (Γ ,, vass na A) _ t ;;
    ret (tProd na A B.π1; _) ;

  infer Γ HΓ (tLetIn n b b_ty b') :=
    infer_type infer Γ HΓ b_ty ;;
    check_wftype infer Γ HΓ b b_ty _ ;;
    b'_ty <- infer (Γ ,, vdef n b b_ty) _ b' ;;
    ret (tLetIn n b b_ty b'_ty.π1; _) ;

  infer Γ HΓ (tApp t u) :=
    ty <- infer Γ HΓ t ;;
    pi <- reduce_to_prod HeΣ Γ ty.π1 _ ;;
    check_wftype infer Γ HΓ u pi.π2.π1 _ ;;
    ret (subst10 u pi.π2.π2.π1; _) ;

  infer Γ HΓ (tConst cst u)
    with inspect (lookup_env (fst Σ) cst) := {
    | exist (Some (ConstantDecl d)) HH =>
        check_consistent_instance d.(cst_universes) u ;;
        let ty := subst_instance u d.(cst_type) in
        ret (ty; _)
    | _ => raise (UndeclaredConstant cst)
    } ;

  infer Γ HΓ (tInd ind u) :=
    d <- lookup_ind_decl ind ;;
    check_consistent_instance d.π1.(ind_universes) u ;;
    let ty := subst_instance u d.π2.π1.(ind_type) in
    ret (ty; _) ;

  infer Γ HΓ (tConstruct ind k u) with lookup_ind_decl ind := {
    | TypeError t := TypeError t ;
    | Checked (mdecl;(idecl;decl))
        with inspect (nth_error idecl.(ind_ctors) k) := {
    | exist (Some cdecl) HH :=
      check_consistent_instance mdecl.(ind_universes) u ;;
      ret (type_of_constructor mdecl cdecl (ind, k) u; _)
    | exist None _ := raise (UndeclaredConstructor ind k)
  }};

  infer Γ HΓ (tCase ci p c brs) :=
    cty <- infer Γ HΓ c ;;
    I <- reduce_to_ind HeΣ Γ cty.π1 _ ;;
    (*let (ind';(u;(args;H))) := I in*)
    let ind' := I.π1 in let u := I.π2.π1 in let args := I.π2.π2.π1 in
    check_eq_true (eqb ci.(ci_ind) ind')
                  (* bad case info *)
                  (NotConvertible G Γ (tInd ci u) (tInd ind' u)) ;;
    d <- lookup_ind_decl ci.(ci_ind) ;;
    (*let (mdecl;(idecl;isdecl)):= d in*)
    let mdecl := d.π1 in let idecl := d.π2.π1 in let isdecl := d.π2.π2 in
    check_coind <- check_eq_true (negb (isCoFinite (ind_finite mdecl)))
          (Msg "Case on coinductives disallowed") ;;
    check_eq_true (eqb (ind_npars mdecl) ci.(ci_npar))
                  (Msg "not the right number of parameters") ;;
    check_eq_true (eqb (ind_relevance idecl) ci.(ci_relevance))
                  (Msg "invalid relevance annotation on case") ;;
    (*let '(params, indices) := chop ci.(ci_npar) args in *)
    let chop_args := chop ci.(ci_npar) args
    in let params := chop_args.1 in let indices := chop_args.2 in
    cu <- check_consistent_instance (ind_universes mdecl) p.(puinst) ;;
    check_eq_true (compare_global_instance Σ (check_eqb_universe G) (check_leqb_universe G) (IndRef ind') 
      #|args| u p.(puinst))
      (Msg "invalid universe annotation on case, not larger than the discriminee's universes") ;;
    wt_params <- check_inst infer Γ (List.rev (smash_context [] (ind_params mdecl))@[p.(puinst)]) _ _ p.(pparams) ;;
    eq_params <- check_equality_terms Γ params p.(pparams) _ _ ;;
    let pctx := case_predicate_context ci.(ci_ind) mdecl idecl p in
    check_wfpctx_conv <- check_alpha_equality_ctx p.(pcontext) (ind_predicate_context ci mdecl idecl) ;;
    let isty : ∥ isType Σ Γ (mkApps (tInd ci p.(puinst)) (p.(pparams) ++ indices)) ∥ := _ in
    retty <- infer_type infer (Γ ,,, pctx) _ p.(preturn) ;;
    let '(ps; typ_pret) := retty in
    check_is_allowed_elimination ps (ind_kelim idecl);;
    let ptm := it_mkLambda_or_LetIn pctx p.(preturn) in
    let wfp : wf_predicate mdecl idecl p := _ in
    check_brs <- check_branches infer Γ HΓ ps ci mdecl idecl p indices isdecl isty
      wfp _ _ 0 idecl.(ind_ctors) brs _ ;;
      ret (mkApps ptm (indices ++ [c]); _) ;

  infer Γ HΓ (tProj (ind, n, k) c) with lookup_ind_decl ind := {
    | TypeError t := TypeError t ;
    | Checked (mdecl;(idecl;decl))
      with inspect (nth_error idecl.(ind_projs) k) := {
        | exist None _ := raise (Msg "projection not found") ;
        | exist (Some pdecl) HH =>
            c_ty <- infer Γ HΓ c ;;
            I <- reduce_to_ind HeΣ Γ c_ty.π1 _ ;;
            (*let (ind';(u;(args;H))) := I in*)
            let ind' := I.π1 in let u := I.π2.π1 in let args := I.π2.π2.π1 in
            check_eq_true (eqb ind ind')
                          (NotConvertible G Γ (tInd ind u) (tInd ind' u)) ;;
            check_eq_true (ind_npars mdecl =? n)
                          (Msg "not the right number of parameters") ;;
            let ty := snd pdecl in
            ret (subst0 (c :: List.rev args) (subst_instance u ty); _)
    }};

  infer Γ HΓ (tFix mfix n)
    with inspect (nth_error mfix n) := {
    | exist None _ := raise (IllFormedFix mfix n) ;
    | exist (Some decl) Hnth :=
      wf_types <- check_mfix_types infer Γ HΓ mfix ;;
      wf_bodies <- check_mfix_bodies infer Γ HΓ mfix _ (fix_context mfix) _ ;;
      guarded <- check_eq_true (fix_guard Σ Γ mfix) (Msg "Unguarded fixpoint") ;;
      wffix <- check_eq_true (wf_fixpoint Σ.1 mfix) (Msg "Ill-formed fixpoint: not defined on a mutually inductive family") ;;
      ret (dtype decl; _) };

  infer Γ HΓ (tCoFix mfix n)
    with inspect (nth_error mfix n) := {
    | exist None _ := raise (IllFormedFix mfix n) ;
    | exist (Some decl) Hnth :=
      wf_types <- check_mfix_types infer Γ HΓ mfix ;;
      wf_bodies <- check_mfix_bodies infer Γ HΓ mfix _ (fix_context mfix) _ ;;
      guarded <- check_eq_true (cofix_guard Σ Γ mfix) (Msg "Unguarded cofixpoint") ;;
      wfcofix <- check_eq_true (wf_cofixpoint Σ.1 mfix) (Msg "Ill-formed cofixpoint: not producing values in a mutually coinductive family") ;;
      ret (dtype decl; _)
    } ;

  infer Γ HΓ (tPrim _) := raise (Msg "Primitive types are not supported").

  (* tRel *)
  Next Obligation. intros; sq; now econstructor. Defined.
  (* tSort *)
  Next Obligation.
    eapply (elimT wf_universe_reflect) in i.
    sq; econstructor; tas.
  Defined.
  (* tProd *)
  Next Obligation.
    (* intros Γ HΓ t na A B Heq_t [s ?];  *)
      sq; econstructor; cbn; easy. Defined.
  Next Obligation.
    (* intros Γ HΓ t na A B Heq_t [s1 ?] [s2 ?]; *)
    sq; econstructor; eassumption.
  Defined.
  (* tLambda *)
  Next Obligation.
    (* intros Γ HΓ t0 na A t Heq_t [s ?]; *)
      sq; econstructor; cbn; easy.
  Defined.
  Next Obligation.
    (* intros Γ HΓ t0 na A t Heq_t [s ?] [B ?]; *)
      sq; econstructor; eassumption.
  Defined.
  (* tLetIn *)
  Next Obligation.
    (* intros Γ HΓ t n b b_ty b' Heq_t [? ?]; *)
      sq. econstructor; eauto.
  Defined.
  Next Obligation.
    (* intros Γ HΓ t n b b_ty b' Heq_t [? ?] H0; *)
    sq; econstructor; cbn; eauto.
  Defined.
  Next Obligation.
    (* intros Γ HΓ t n b b_ty b' Heq_t [? ?] H0 [? ?]; *)
    sq; econstructor; eassumption.
  Defined.

  (* tApp *)
  Next Obligation. simpl; eauto using validity_wf. Qed.
  Next Obligation.
    cbn in *; sq.
    eapply type_reduction_closed in X1 ; try eassumption.
    eapply validity in X1 ; try assumption. destruct X1 as [s HH].
    eapply inversion_Prod in HH ; try assumption.
    destruct HH as [s1 [_ [HH _]]].
    eexists. eassumption.
  Defined.
  Next Obligation.
    cbn in *; sq; eapply type_App'.
    2: eassumption.
    eapply type_reduction_closed; eassumption.
  Defined.

  (* tConst *)
  Next Obligation.
    sq; constructor; try assumption.
    symmetry in HH.
    etransitivity. eassumption. reflexivity.
  Defined.

  (* tInd *)
  Next Obligation.
    sq; econstructor; eassumption.
  Defined.

  (* tConstruct *)
  Next Obligation.
    sq; econstructor; tea. split ; tea.
    now symmetry.
  Defined.

  (* tCase *)
  Next Obligation. sq. cbn. eapply validity in X as []; eauto.
    eexists; eauto using validity_wf.
  Defined.
  Next Obligation. cbn in *.
    rewrite List.rev_involutive.
    sq. eapply weaken_wf_local => //.
    rewrite subst_instance_smash; eapply wf_local_smash_context.
    now eapply on_minductive_wf_params.
  Qed.
  Next Obligation. 
    eapply assumption_context_rev.
    apply assumption_context_subst_instance, smash_context_assumption_context; constructor.
  Qed.

  Next Obligation.
    sq.
    apply eqb_eq in i. subst I.
    apply eqb_eq in i0.
    rewrite chop_firstn_skipn -i0 /=.
    eapply type_reduction_closed in X3 ; tea.
    eapply validity in X3.
    eapply isType_mkApps_Ind_inv in X3 as [pars' [args' []]]; eauto.
    eapply spine_subst_wt_terms in s.
    eapply All_impl; tea. intros ? []; auto. now exists x0.
  Qed.
  
  Next Obligation.
    cbn in *. sq.
    now eapply ctx_inst_wt.
  Qed.
    
  Next Obligation.
    sq.
    apply eqb_eq in i. subst I.
    eapply eqb_eq in i0.
    rewrite chop_firstn_skipn -i0 /=.
    eapply type_reduction_closed in X3; tea.
    eapply validity in X3.
    eapply isType_mkApps_Ind_inv in X3 as [pars [argsub []]]; eauto.
    rewrite subst_instance_smash /= in wt_params.
    eapply ctx_inst_smash in wt_params.
    unshelve epose proof (ctx_inst_spine_subst _ wt_params).
    { eapply weaken_wf_local; tea. eapply on_minductive_wf_params; tea. exact X0. }
    eexists; eapply isType_mkApps_Ind_smash; tea.
    rewrite subst_instance_app List.rev_app_distr smash_context_app_expand.
    have wf_ctx : wf_local Σ
      (Γ,,, smash_context [] (ind_params d)@[puinst p],,,
      expand_lets_ctx (ind_params d)@[puinst p]
       (smash_context [] (ind_indices X)@[puinst p])).
    { eapply wf_local_expand_lets. eapply wf_local_smash_end.
      rewrite -app_context_assoc. eapply weaken_wf_local; tea.
      rewrite -subst_instance_app_ctx.
      now eapply (on_minductive_wf_params_indices_inst X0). }
    rewrite chop_firstn_skipn -i0 /= in eq_params *.
    eapply spine_subst_app => //.
    * len. rewrite -(All2_length eq_params).
      now rewrite -(declared_minductive_ind_npars X0).
    * len.
      rewrite skipn_all_app_eq //.
      eapply spine_subst_smash in s0. 
      pose proof (subslet_length s0). len in H. len.
      now eapply spine_subst_smash.
    * len.
      eapply spine_subst_smash in s0.
      rewrite skipn_all_app_eq.
      pose proof (subslet_length s0). len in H. len.
      rewrite firstn_app.
      rewrite (subslet_length s0). len. rewrite Nat.sub_diag /= app_nil_r.
      pose proof (subslet_length s0). len in H. rewrite -H.
      rewrite firstn_rev Nat.sub_diag skipn_0.
      eapply spine_subst_cumul; tea.
      eapply smash_context_assumption_context; pcuic.
      do 2 eapply assumption_context_subst_context.
      eapply assumption_context_lift_context.
      apply smash_context_assumption_context; pcuic.
      eapply wf_local_smash_end. eapply substitution_wf_local. exact s.
      rewrite -app_context_assoc -subst_instance_app_ctx.
      eapply PCUICWeakening.weaken_wf_local; tea. eapply on_minductive_wf_params_indices_inst; tea.
      eapply spine_subst_smash in X3. eapply substitution_wf_local. exact X3.
      eapply wf_local_expand_lets, wf_local_smash_end.
      rewrite -app_context_assoc -subst_instance_app_ctx.
      eapply weaken_wf_local; tea. eapply on_minductive_wf_params_indices_inst; tea.
      rewrite -(subst_context_smash_context _ _ []).
      rewrite -(spine_subst_inst_subst X3).
      rewrite - !smash_context_subst /= !subst_context_nil.
      unshelve eapply compare_global_instance_sound in i2; pcuic.
      eapply (inductive_cumulative_indices X0); tea.
  Qed.
  
  Obligation Tactic := idtac.
  Next Obligation.
    intros. simpl in *. clearbody isty.
    destruct cty as [A cty]. cbn in *.
    subst ind' u args mdecl idecl isdecl.
    destruct I as [ind' [u [args []]]].
    destruct d as [mdecl [idecl isdecl]].
    cbn in *.
    sq.
    apply eqb_eq in i. subst ind'.
    eapply eqb_eq in i0.
    eapply type_reduction_closed in cty; tea.
    eapply validity in cty.
    eapply isType_mkApps_Ind_inv in cty as [pars [argsub []]] ; eauto.
    eapply wf_case_predicate_context; tea.
    eapply eq_context_gen_wf_predicate; eauto.
    rewrite -(All2_length eq_params).
    subst params chop_args.
    now rewrite chop_firstn_skipn /= -e i0.
  Qed.

  Next Obligation.
    intros. simpl in *. clearbody isty.
    destruct cty as [A cty]. cbn in *.
    subst ind' u args mdecl idecl isdecl.
    destruct I as [ind' [u [args []]]].
    destruct d as [mdecl [idecl isdecl]].
    cbn in *.
    sq.
    apply eqb_eq in i. subst ind'.
    eapply eqb_eq in i0.
    eapply type_reduction_closed in cty; tea.
    eapply validity in cty.
    eapply isType_mkApps_Ind_inv in cty as [pars [argsub []]] ; eauto.
    eapply eq_context_gen_wf_predicate; tea.
    rewrite -(All2_length eq_params).
    subst params chop_args.
    now rewrite chop_firstn_skipn /= -e i0.
  Qed.
    
  Next Obligation.
    intros. simpl in *.
    clearbody isty wfp.
    now sq.
  Qed.

  Next Obligation.
    intros. simpl in *.
    clearbody isty wfp.
    sq.
    now eapply All2_fold_All2 in check_wfpctx_conv.
  Qed.

  Next Obligation.
    intros; cbn in *. clearbody isty wfp.
    sq.
    eapply forall_nth_error_Alli.
    now auto.
  Qed.

  Next Obligation.
    intros; cbn in *. clearbody isty wfp.
    destruct cty as [A cty]. cbn in *.
    subst ind' u args mdecl idecl isdecl.
    destruct I as [ind' [u [args []]]].
    destruct d as [mdecl [idecl isdecl]].
    sq.
    cbn in *.
    apply eqb_eq in i. subst ind'.
    eapply eqb_eq in i0.
    eapply eqb_eq in i1.
    econstructor; eauto; pcuic.
    - now eapply All2_fold_All2 in check_wfpctx_conv.
    - eapply isType_mkApps_Ind_smash_inv in isty as [sp cu']; tea.
      eapply spine_subst_ctx_inst in sp.
      now eapply ctx_inst_smash.
    - eapply type_reduction_closed in cty. 2:tea.
      eapply type_equality; tea.
      eapply equality_mkApps_eq => //. fvs. constructor => //.
      unshelve eapply compare_global_instance_sound in i2; tea; pcuic.
      subst params indices chop_args.
      rewrite chop_firstn_skipn in isty, eq_params |- *.
      rewrite -{1}(firstn_skipn (ci_npar ci) args).
      eapply All2_app => //.
      eapply validity in cty.
      eapply isType_mkApps_Ind_smash_inv in cty as []; tea.
      eapply spine_subst_wt_terms in s.
      eapply All2_app_inv. 2:erewrite !firstn_skipn. reflexivity.
      now eapply wt_terms_equality.
    - now eapply All2_fold_All2 in check_wfpctx_conv.
    - eapply isType_mkApps_Ind_smash_inv in isty as [sp cu']; tea.
      eapply spine_subst_ctx_inst in sp.
      now eapply ctx_inst_smash.
    - now eapply negb_true_iff in check_coind.
    - red. eapply All2_Forall2.
      clear - check_brs.
      induction check_brs; constructor; auto. sq.
      destruct r0. 
      solve_all.
      eapply eq_context_gen_wf_branch.
      now eapply All2_fold_All2.
    - eapply All2i_impl; tea.
      cbn; intros; intuition auto. pcuic.
  Qed.

  Obligation Tactic := Program.Tactics.program_simplify ; eauto 2.

  (* tProj *)
  Next Obligation. simpl; eauto using validity_wf. Defined.
  Next Obligation.
    simpl in *; sq.
    pose proof (on_declared_inductive decl) as [onmib oni].
    eapply onProjections in oni.
    destruct ind_ctors as [|? []] eqn:hctors => //.
    eapply type_Proj with (pdecl := (i1, t)).
    - split. split. eassumption. cbn. rewrite hctors. reflexivity.
      split. symmetry; eassumption. cbn in *.
      now apply beq_nat_true.
    - cbn. destruct (ssrbool.elimT (eqb_spec ind I)); [assumption|].
      eapply type_reduction_closed; eassumption.
    - eapply type_reduction_closed in X1; eauto.
      eapply validity in X1; eauto.
      destruct (ssrbool.elimT (eqb_spec ind I)); auto.
      unshelve eapply (PCUICInductives.isType_mkApps_Ind_inv _ decl _) in X1 as [parsubst [argsubst [sp sp' cu]]]; eauto.
      pose proof (PCUICContextSubst.context_subst_length2 (PCUICSpine.inst_ctx_subst sp)).
      pose proof (PCUICContextSubst.context_subst_length2 (PCUICSpine.inst_ctx_subst sp')).
      autorewrite with len in H, H0.
      destruct (on_declared_inductive decl) eqn:ond.
      rewrite -o.(onNpars) -H.
      forward (o0.(onProjections)).
      intros H'; rewrite H' nth_error_nil // in HH.
      destruct ind_ctors as [|cs []]; auto.
      intros onps.
      unshelve epose proof (onps.(on_projs_noidx _ _ _ _ _ _)).
      destruct (ind_indices idecl) => //.
      simpl in *.
      rewrite List.skipn_length in H0.
      rewrite List.firstn_length. lia.
    - destruct ind_projs => //. rewrite nth_error_nil in HH; congruence.
  Defined.

  (* tFix *)
  Next Obligation. sq. now eapply PCUICWeakening.All_mfix_wf. Defined.
  Next Obligation. sq. constructor; auto. Qed.

  (* tCoFix *)
  Next Obligation. sq. now eapply PCUICWeakening.All_mfix_wf. Defined.
  Next Obligation.  sq. constructor ; auto. Qed.

(* 
  Program Definition check_isWfArity Γ (HΓ : ∥ wf_local Σ Γ ∥) A
    : typing_result (∥ isWfArity Σ Γ A ∥) :=
    match destArity [] A with
    | None => raise (Msg (print_term Σ Γ A ^ " is not an arity"))
    | Some (ctx, s) => XX <- check_context (Γ ,,, ctx) ;;
                      ret _
    end.
  Next Obligation.
    destruct XX. constructor. exists ctx, s.
    split; auto.
  Defined. *)

  Definition check_isType := infer_isType infer.

  Program Definition check Γ (HΓ : ∥ wf_local Σ Γ ∥) t A
    : typing_result (∥ Σ;;; Γ |- t : A ∥) :=
    check_isType Γ HΓ A ;;
    check_wftype infer Γ HΓ t A _.

End Typecheck.
