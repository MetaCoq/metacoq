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

  Definition isconv Γ := isconv_term Σ HΣ Hφ G HG Γ Conv.
  Definition iscumul Γ := isconv_term Σ HΣ Hφ G HG Γ Cumul.
  
  Program Definition convert Γ t u
          (ht : welltyped Σ Γ t) (hu : welltyped Σ Γ u)
    : typing_result (∥ Σ ;;; Γ ⊢ t = u ∥) :=
    match eqb_term Σ G t u with true => ret _ | false =>
    match isconv Γ t ht u hu with
    | ConvSuccess => ret _
    | ConvError e => (* fallback *)  (* nico *)
      let t' := hnf Γ t ht in
      let u' := hnf Γ u hu in
      (* match leq_term (snd Σ) t' u' with true => ret _ | false => *)
      raise (NotCumulSmaller false G Γ t u t' u' e)
      (* end *)
    end end.
  Next Obligation.
    destruct HΣ.
    symmetry in Heq_anonymous; eapply eqb_term_spec in Heq_anonymous; tea.
    constructor. constructor; auto; fvs.
  Qed.
  Next Obligation.
    symmetry in Heq_anonymous; apply isconv_term_sound in Heq_anonymous.
    assumption.
  Qed.

  Program Definition convert_leq Γ t u
          (ht : welltyped Σ Γ t) (hu : welltyped Σ Γ u)
    : typing_result (∥ Σ ;;; Γ ⊢ t ≤ u ∥) :=
    match leqb_term Σ G t u with true => ret _ | false =>
    match iscumul Γ t ht u hu with
    | ConvSuccess => ret _
    | ConvError e => (* fallback *)  (* nico *)
      let t' := hnf Γ t ht in
      let u' := hnf Γ u hu in
      (* match leq_term (snd Σ) t' u' with true => ret _ | false => *)
      raise (NotCumulSmaller true G Γ t u t' u' e)
      (* end *)
    end end.
  Next Obligation.
    destruct HΣ.
    symmetry in Heq_anonymous; eapply leqb_term_spec in Heq_anonymous; tea.
    constructor. constructor; auto; fvs.
  Qed.
  Next Obligation.
    symmetry in Heq_anonymous; apply isconv_term_sound in Heq_anonymous.
    assumption.
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

    Program Definition infer_type Γ HΓ t
      : typing_result ({u : Universe.t & ∥ Σ ;;; Γ |- t : tSort u ∥}) :=
      tx <- infer Γ HΓ t ;;
      u <- reduce_to_sort HeΣ Γ tx.π1 _ ;;
      ret (u.π1; _).
    Next Obligation.
      eapply validity_wf; eassumption.
    Defined.
    Next Obligation.
      destruct HΣ, HΓ, X, X0.
      constructor; eapply type_reduction; tea. exact X.
    Defined.

    Program Definition infer_isType Γ HΓ T : typing_result (∥ isType Σ Γ T ∥) :=
      tx <- infer_type Γ HΓ T ;;
      ret _.
    Next Obligation.
      sq. now eexists.
    Defined.

    Program Definition infer_cumul Γ HΓ t A (hA : ∥ isType Σ Γ A ∥)
      : typing_result (∥ Σ ;;; Γ |- t : A ∥) :=
      A' <- infer Γ HΓ t ;;
      X <- convert_leq Γ A'.π1 A _ _ ;;
      ret _.
    Next Obligation. now eapply validity_wf. Qed.
    Next Obligation. destruct hA; now apply wat_welltyped. Qed.
    Next Obligation.
      destruct HΣ, HΓ, hA, X, X0. constructor. eapply type_equality; eassumption.
    Qed.
    
    Program Definition infer_scheme Γ HΓ t :
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
    Qed.

    Lemma sq_wfl_nil : ∥ wf_local Σ [] ∥.
    Proof.
     repeat constructor.
    Qed.

    Program Fixpoint check_context Γ : typing_result (∥ wf_local Σ Γ ∥)
    := match Γ with
       | [] => ret sq_wfl_nil
       | {| decl_body := None; decl_type := A |} :: Γ =>
         HΓ <- check_context Γ ;;
         XX <- infer_type Γ HΓ A ;;
         ret _
       | {| decl_body := Some t; decl_type := A |} :: Γ =>
         HΓ <- check_context Γ ;;
         XX <- infer_type Γ HΓ A ;;
         XX <- infer_cumul Γ HΓ t A _ ;;
         ret _
      end.
    Next Obligation.
      sq. econstructor; tas. econstructor; eauto.
    Qed.
    Next Obligation.
      sq. econstructor; tea.
    Qed.
    Next Obligation.
      sq. econstructor; tas. econstructor; eauto.
    Qed.
 
    Lemma sq_wf_locak_app {Γ Δ} : ∥ wf_local Σ Γ ∥ -> ∥ wf_local_rel Σ Γ Δ ∥ -> ∥ wf_local Σ (Γ ,,, Δ) ∥.
    Proof.
      intros [] []; constructor; now apply wf_local_app.
    Qed. 

    Program Fixpoint check_context_rel Γ (Δ : context) :
      ∥ wf_local Σ Γ ∥ -> typing_result (∥ wf_local_rel Σ Γ Δ ∥) :=
      match Δ return ∥ wf_local Σ Γ ∥ -> typing_result (∥ wf_local_rel Σ Γ Δ ∥) with
       | [] => fun wfΓ => ret (sq localenv_nil)
       | {| decl_body := None; decl_type := A |} :: Δ =>
        fun wfΓ =>
         wfΔ <- check_context_rel Γ Δ wfΓ ;;
         XX <- infer_isType (Γ ,,, Δ) (sq_wf_locak_app wfΓ wfΔ) A ;;
         ret _
       | {| decl_body := Some t; decl_type := A |} :: Δ =>
         fun wfΓ => 
         wfΔ <- check_context_rel Γ Δ wfΓ ;;
         Aty <- infer_isType (Γ ,,, Δ) (sq_wf_locak_app wfΓ wfΔ) A ;;
         XX <- infer_cumul (Γ ,,, Δ) (sq_wf_locak_app wfΓ wfΔ) t A Aty ;;
         ret _
      end.
    Next Obligation.
      sq. constructor; auto.
    Qed.
    Next Obligation.
      sq. constructor; auto.
    Qed.

    Program Definition check_equality_decl le Γ d d' : wt_decl Σ Γ d -> wt_decl Σ Γ d' -> 
      typing_result (∥ equality_open_decls le Σ Γ d d' ∥) := 
      match d, d' return wt_decl Σ Γ d -> wt_decl Σ Γ d' -> typing_result _ with
      | {| decl_name := na; decl_body := Some b; decl_type := ty |},
        {| decl_name := na'; decl_body := Some b'; decl_type := ty' |} => 
        fun wtd wtd' =>
        eqna <- check_eq_true (eqb_binder_annot na na') (Msg "Binder annotations do not match") ;;
        cumb <- convert Γ b b' _ _ ;;
        cumt <- (if le then convert_leq else convert) Γ ty ty' _ _ ;;
        ret (let 'sq cumb := cumb in 
              let 'sq cumt := cumt in
              sq _)
      | {| decl_name := na; decl_body := None; decl_type := ty |},
        {| decl_name := na'; decl_body := None; decl_type := ty' |} => 
        fun wtd wtd' =>
        eqna <- check_eq_true (eqb_binder_annot na na') (Msg "Binder annotations do not match") ;;
        cumt <- (if le then convert_leq else convert) Γ ty ty' wtd wtd' ;;
        ret (let 'sq cumt := cumt in sq _)      
      | _, _ =>
        fun wtd wtd' => raise (Msg "While checking cumulativity of contexts: declarations do not match")
      end.
    Next Obligation.
      econstructor; pcuics. now apply eqb_binder_annot_spec.
    Qed.
    Next Obligation.
      constructor; pcuics. now apply eqb_binder_annot_spec.
    Qed.

    Lemma context_cumulativity_welltyped {le Γ Γ' t} : 
      welltyped Σ Γ t ->
      Σ ⊢ Γ' ≤[le] Γ ->
      wf_local Σ Γ' ->
      welltyped Σ Γ' t.
    Proof.
      destruct HΣ.
      intros [s Hs] cum wfΓ'; exists s; eapply closed_context_cumulativity; eauto.
    Qed.

    Lemma context_cumulativity_wt_decl {le Γ Γ' d} :
      wt_decl Σ Γ d ->
      Σ ⊢ Γ' ≤[le] Γ ->
      wf_local Σ Γ' ->
      wt_decl Σ Γ' d.
    Proof.
      destruct d as [na [b|] ty]; simpl;
      intuition pcuics; eapply context_cumulativity_welltyped; pcuics.
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

    Program Fixpoint check_equality_ctx le Γ Δ Δ'
      (wfΔ : ∥ wf_local Σ (Γ ,,, Δ) ∥) (wfΔ' : ∥ wf_local Σ (Γ ,,, Δ') ∥) : 
      typing_result (∥ context_equality_rel le Σ Γ Δ Δ' ∥) :=
      match Δ, Δ' with
      | [], [] => ret (sq _)
      | decl :: Δ, decl' :: Δ' => 
        cctx <- check_equality_ctx le Γ Δ Δ' _ _ ;;
        cdecl <- check_equality_decl le (Γ ,,, Δ) decl decl' _ _ ;;
        ret _
      | _, _ => raise (Msg "While checking cumulativity of contexts: contexts do not have the same length")
      end.
      Next Obligation.
        split.
        * sq; fvs.
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
        pose proof HΣ as [wfΣ].
        destruct wfΔ as [wfΔ], wfΔ' as [wfΔ'], cctx as [cctx].
        assert(context_equality le Σ (Γ ,,, Δ) (Γ ,,, Δ')).
        now apply context_equality_rel_app.
        simpl in *. eapply inv_wf_local in wfΔ as [wfΔ wfd].
        eapply inv_wf_local in wfΔ' as [wfΔ' wfd'].
        eapply context_cumulativity_wt_decl. 3:eassumption. all:pcuics.
      Qed.
      Next Obligation.
        pose proof HΣ as [wfΣ].
        destruct wfΔ as [wfΔ], wfΔ' as [wfΔ'], cctx as [cctx], cdecl as [cdecl].
        constructor.
        eapply inv_wf_local in wfΔ as [wfΔ wfd].
        eapply inv_wf_local in wfΔ' as [wfΔ' wfd'].
        now apply context_equality_rel_cons.
      Qed.
      Next Obligation.
        split. intros. intros []. congruence. intros []; congruence.
      Qed.
      Next Obligation.
        split. intros. intros []. congruence. intros []; congruence.
      Qed.

    Program Fixpoint check_alpha_equality_ctx Δ Δ' :
      typing_result (∥ eq_context_gen eq eq Δ Δ' ∥) :=
      match forallb2 (bcompare_decls eqb eqb) Δ Δ' with
      | true => ret (sq _) 
      | false => raise (Msg "While checking alpha-conversion of contexts: contexts differ")
      end.
    Next Obligation.
      move: Heq_anonymous.
      elim: reflect_eq_ctx => //.
    Qed.

    Program Fixpoint infer_terms Γ (wfΓ : ∥ wf_local Σ Γ ∥) ts : typing_result (∥ All (welltyped Σ Γ) ts ∥) :=
      match ts with
      | t :: ts =>
        checkt <- infer Γ wfΓ t ;;
        convts <- infer_terms Γ wfΓ ts ;;
        ret _
      | [] => ret (sq All_nil)
      end.
    Next Obligation.
      sq. constructor; auto. now exists checkt.
    Qed.

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

    Program Fixpoint check_inst Γ Δ (wfΓ : ∥ wf_local Σ (Γ ,,, List.rev Δ) ∥) (HΔ : assumption_context Δ) ts : 
      typing_result (∥ ctx_inst Σ Γ ts Δ ∥) :=
      let msg := Msg "While checking a substitution: not of the right length" in
      match Δ with
      | [] => 
        match ts with 
        | [] => ret _
        | t :: ts => raise msg
        end
      | d :: Δ =>
        match d with
        | {| decl_name := na; decl_body := None; 
             decl_type := T |} =>
          match ts with
          | t :: ts =>
            checkt <- infer_cumul Γ _ t T _ ;;
            subs <- check_inst Γ (subst_telescope [t] 0 Δ) _ _ ts ;;
            ret _
          | [] => raise msg
          end
        | {| decl_body := Some b; decl_type := T |} =>
          False_rect _ _
        end
      end.
    Next Obligation.
      sq. constructor; auto.
    Qed.
    Next Obligation.
      sq. now eapply All_local_env_app_inv in wfΓ.
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
      sq. constructor; auto.
    Qed.
    Next Obligation.
      depelim HΔ.
    Qed.

    Program Fixpoint check_equality_terms Γ ts ts' (wts : ∥ All (welltyped Σ Γ) ts ∥) (wts' : ∥ All (welltyped Σ Γ) ts' ∥) : 
      typing_result (∥ equality_terms Σ Γ ts ts' ∥) :=
      match ts, ts' with
      | t :: ts, t' :: ts' =>
        convt <- convert Γ t t' _ _ ;;
        convts <- check_equality_terms Γ ts ts' _ _ ;;
        ret _
      | [], [] => ret _
      | _, _ => raise (Msg "While checking conversion of terms: lists do not have the same length")
      end.
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
    Next Obligation. 
      intuition congruence.
    Qed.
    Next Obligation.
      intuition congruence.
    Qed.

  End InferAux.

  Program Definition lookup_ind_decl ind
    : typing_result
        ({decl & {body & declared_inductive (fst Σ) ind decl body}}) :=
    match lookup_env (fst Σ) ind.(inductive_mind) with
    | Some (InductiveDecl decl) =>
      match nth_error decl.(ind_bodies) ind.(inductive_ind) with
      | Some body => ret (decl; body; _)
      | None => raise (UndeclaredInductive ind)
      end
    | _ => raise (UndeclaredInductive ind)
    end.
  Next Obligation.
    split.
    - symmetry in Heq_anonymous0.
      etransitivity. eassumption. reflexivity.
    - now symmetry.
  Defined.

  Program Definition check_consistent_instance uctx u
    : typing_result (consistent_instance_ext Σ uctx u)
    := match uctx with
       | Monomorphic_ctx _ =>
         check_eq_nat #|u| 0 (Msg "monomorphic instance should be of length 0")
       | Polymorphic_ctx (inst, cstrs) =>
         let '(inst, cstrs) := AUContext.repr (inst, cstrs) in
         check_eq_true (forallb (fun l => LevelSet.mem l (uGraph.wGraph.V G)) u)
                       (Msg "undeclared level in instance") ;;
         X <- check_eq_nat #|u| #|inst|
                          (Msg "instance does not have the right length");;
         match check_constraints G (subst_instance_cstrs u cstrs) with
         | true => ret (conj _ _)
         | false => raise (Msg "ctrs not satisfiable")
         end
         (* #|u| = #|inst| /\ valid_constraints φ (subst_instance_cstrs u cstrs) *)
       end.
  Next Obligation.
    eapply forallb_All in H. eapply All_forallb'; tea.
    clear -cf HG. intros x; simpl. now apply is_graph_of_uctx_levels.
  Qed.
  Next Obligation.
    repeat split.
    - now rewrite mapi_length in X.
    - eapply check_constraints_spec; eauto.
  Qed.

  Obligation Tactic := Program.Tactics.program_simplify ; eauto 2.
  
  Program Definition check_is_allowed_elimination (u : Universe.t) (al : allowed_eliminations) :
    typing_result (is_allowed_elimination Σ u al) :=
    let o :=
    match al return option (is_allowed_elimination Σ u al) with
    | IntoSProp =>
      match Universe.is_sprop u with
      | true => Some _
      | false => None
      end
    | IntoPropSProp =>
      match is_propositional u with
      | true => Some _
      | false => None
      end
    | IntoSetPropSProp =>
      match is_propositional u || check_eqb_universe G u Universe.type0 with
      | true => Some _
      | false => None
      end
    | IntoAny => Some _
    end in
    match o with
    | Some t => Checked t
    | None => TypeError (Msg "Cannot eliminate over this sort")
    end.
  Next Obligation.
    unfold is_allowed_elimination, is_allowed_elimination0.
    destruct check_univs; auto.
    intros val sat.
    symmetry in Heq_anonymous.
    apply is_sprop_val with (v := val) in Heq_anonymous.
    now rewrite Heq_anonymous.
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
  
  Notation infer_ty :=
    (forall (Γ : context) (HΓ : ∥ wf_local Σ Γ ∥) (t : term), typing_result ({ A : term & ∥ Σ ;;; Γ |- t : A ∥ })).

  Section check_brs.
    Context (infer : infer_ty)
     (Γ : context) (wfΓ : ∥ wf_local Σ Γ ∥) (ps : Universe.t)
     (ci : case_info) (mdecl : mutual_inductive_body)
     (idecl : one_inductive_body) (p : predicate term) (args : list term).
     
    Context (isdecl : declared_inductive Σ ci mdecl idecl).
    Context (hty : ∥ isType Σ Γ (mkApps (tInd ci (puinst p)) (pparams p ++ args)) ∥).
    Context (wfp : wf_predicate mdecl idecl p).
    Context (predctx := case_predicate_context ci mdecl idecl p).
    Context (wfpret : ∥ Σ;;; Γ,,, predctx |- preturn p : tSort ps ∥).
    Context (ptm := it_mkLambda_or_LetIn predctx (preturn p)).
    (* Context (wfbrs : wf_branches idecl brs) *)
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

    Obligation Tactic := idtac.

    Program Fixpoint check_branches (n : nat) (ctors : list constructor_body)
       (brs : list (branch term)) 
       (isdecl : ∥ Alli (fun i cdecl => declared_constructor Σ (ci, i) mdecl idecl cdecl) n ctors ∥)
       {struct brs}
       : typing_result (wt_brs Γ ci mdecl idecl p ps ptm ctors brs n) := 
      match ctors, brs return 
      ∥ Alli (fun i cdecl => declared_constructor Σ (ci, i) mdecl idecl cdecl) n ctors ∥ ->
      typing_result (wt_brs Γ ci mdecl idecl p ps ptm ctors brs n) with
      | [], [] => fun decl => ret (sq All2i_nil : wt_brs Γ ci mdecl idecl p ps ptm [] [] n)
      | cdecl :: cdecls, br :: brs => fun decl =>
        let brctxty := case_branch_type ci.(ci_ind) mdecl idecl p br ptm n cdecl in
        check_eq_bcontext <- check_alpha_equality_ctx br.(bcontext) (cstr_branch_context ci mdecl cdecl) ;;
        Z <- infer_cumul infer (Γ ,,, brctxty.1) _ br.(bbody) brctxty.2 _ ;;
        X <- check_branches (S n) cdecls brs _ ;;
        ret (t:=wt_brs Γ ci mdecl idecl p ps ptm (cdecl :: cdecls) (br :: brs) n) _
      | [], _ :: _
      | _ :: _, [] => fun decl => raise (Msg "wrong number of branches")
      end isdecl.

      Next Obligation.
        intros.
        eapply branch_helper in decl; tea.
        sq. now destruct decl as [? []].
      Defined.
      Next Obligation.
        clear infer.
        intros; eapply branch_helper in decl; tea.
        sq. destruct decl as [? []].
        now exists ps.
      Qed.
      Next Obligation.
        intros; sq. now depelim decl.
      Qed.
      Next Obligation.
        clear infer.
        intros.
        eapply branch_helper in decl; tea.
        sq. constructor.
        split.
        * now eapply All2_fold_All2 in check_eq_bcontext.
        * destruct decl as [? []].
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

  (* Opaque check_inst. *)
  (* Obligation Tactic := cbn; intros; Program.Tactics.destruct_conjs; cbn in *. *)

  Program Fixpoint infer (Γ : context) (HΓ : ∥ wf_local Σ Γ ∥) (t : term) {struct t}
    : typing_result ({ A : term & ∥ Σ ;;; Γ |- t : A ∥ }) :=
    match t with
    | tRel n =>
      match nth_error Γ n with
      | Some c => ret ((lift0 (S n)) (decl_type c); _)
      | None   => raise (UnboundRel n)
      end

    | tVar n  => raise (UnboundVar n)
    | tEvar ev args => raise (UnboundEvar ev)

    | tSort u =>
      check_eq_true (wf_universeb Σ u)
                    (Msg ("Sort contains an undeclared level " ^ string_of_sort u));;
      ret (tSort (Universe.super u); _)

    | tProd na A B =>
      s1 <- infer_type infer Γ HΓ A ;;
      s2 <- infer_type infer (Γ ,, vass na A) _ B ;;
      ret (tSort (Universe.sort_of_product s1.π1 s2.π1); _)

    | tLambda na A t =>
      s1 <- infer_type infer Γ HΓ A ;;
      B <- infer (Γ ,, vass na A) _ t ;;
      ret (tProd na A B.π1; _)

    | tLetIn n b b_ty b' =>
      infer_type infer Γ HΓ b_ty ;;
      infer_cumul infer Γ HΓ b b_ty _ ;;
      b'_ty <- infer (Γ ,, vdef n b b_ty) _ b' ;;
      ret (tLetIn n b b_ty b'_ty.π1; _)

    | tApp t u =>
      ty <- infer Γ HΓ t ;;
      pi <- reduce_to_prod HeΣ Γ ty.π1 _ ;;
      infer_cumul infer Γ HΓ u pi.π2.π1 _ ;;
      ret (subst10 u pi.π2.π2.π1; _)

    | tConst cst u =>
      match lookup_env (fst Σ) cst with
      | Some (ConstantDecl d) =>
        check_consistent_instance d.(cst_universes) u ;;
        let ty := subst_instance u d.(cst_type) in
        ret (ty; _)
      |  _ => raise (UndeclaredConstant cst)
      end

    | tInd ind u =>
      d <- lookup_ind_decl ind ;;
      check_consistent_instance d.π1.(ind_universes) u ;;
      let ty := subst_instance u d.π2.π1.(ind_type) in
      ret (ty; _)

    | tConstruct ind k u =>
      d <- lookup_ind_decl ind ;;
      match nth_error d.π2.π1.(ind_ctors) k with
      | Some cdecl =>
        check_consistent_instance d.π1.(ind_universes) u ;;
        ret (type_of_constructor d.π1 cdecl (ind, k) u; _)
      | None => raise (UndeclaredConstructor ind k)
      end

    | tCase ci p c brs =>
      cty <- infer Γ HΓ c ;;
      I <- reduce_to_ind HeΣ Γ cty.π1 _ ;;
      let '(ind'; I') := I in let '(u; I'') := I' in let '(args; H) := I'' in
      check_eq_true (eqb ci.(ci_ind) ind')
                    (* bad case info *)
                    (NotConvertible G Γ (tInd ci u) (tInd ind' u)) ;;
      d <- lookup_ind_decl ci.(ci_ind) ;;
      let '(mdecl; (idecl; isdecl)) := (d : ∑ (mdecl : mutual_inductive_body)
          (idecl : one_inductive_body), declared_inductive _ _ _ _) in
      check_coind <- check_eq_true (negb (isCoFinite (ind_finite mdecl)))
            (Msg "Case on coinductives disallowed") ;;
      check_eq_true (eqb (ind_npars mdecl) ci.(ci_npar))
                    (Msg "not the right number of parameters") ;;
      check_eq_true (eqb (ind_relevance idecl) ci.(ci_relevance))
                    (Msg "invalid relevance annotation on case") ;;
      let '(params, indices) := chop ci.(ci_npar) args in
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
       ret (mkApps ptm (indices ++ [c]); _)

    | tProj (ind, n, k) c =>
      d <- lookup_ind_decl ind ;;
      match nth_error d.π2.π1.(ind_projs) k with
      | Some pdecl =>
        c_ty <- infer Γ HΓ c ;;
        I <- reduce_to_ind HeΣ Γ c_ty.π1 _ ;;
        let '(ind'; I') := I in let '(u; I'') := I' in let '(args; H) := I'' in
        check_eq_true (eqb ind ind')
                      (NotConvertible G Γ (tInd ind u) (tInd ind' u)) ;;
        check_eq_true (ind_npars d.π1 =? n)
                      (Msg "not the right number of parameters") ;;
        let ty := snd pdecl in
        ret (subst0 (c :: List.rev args) (subst_instance u ty);
                _)
      | None => raise (Msg "projection not found")
      end

    | tFix mfix n =>
      match nth_error mfix n with
      | None => raise (IllFormedFix mfix n)
      | Some decl =>
        XX <- (fix check_types (mfix : mfixpoint term) {struct mfix}
              : typing_result (∥ All (fun x => isType Σ Γ (dtype x)) mfix ∥)
              := match mfix with
                 | [] => ret (sq All_nil)
                 | def :: mfix =>
       (* probably not tail recursive but needed so that next line terminates *)
                   W <- infer_type infer Γ HΓ (dtype def) ;;
                   Z <- check_types mfix ;;
                   ret _
                 end)
           mfix ;;
        YY <- (fix check_bodies (mfix' : mfixpoint term)
              (XX : ∥ All (fun x => isType Σ Γ (dtype x)) mfix' ∥)
            {struct mfix'}
                : typing_result (All (fun d =>
              ∥ Σ ;;; Γ ,,, fix_context mfix |- dbody d : (lift0 #|fix_context mfix|) (dtype d) ∥) mfix')
              := match mfix' with
                 | [] => ret All_nil
                 | def :: mfix' =>
                   W1 <- infer_cumul infer (Γ ,,, fix_context mfix) _ (dbody def)
                                    (lift0 #|fix_context mfix| (dtype def)) _ ;;
                   Z <- check_bodies mfix' _ ;;
                   ret (All_cons W1 Z)
                 end) mfix _ ;;
        guarded <- check_eq_true (fix_guard Σ Γ mfix) (Msg "Unguarded fixpoint") ;;
        wffix <- check_eq_true (wf_fixpoint Σ.1 mfix) (Msg "Ill-formed fixpoint: not defined on a mutually inductive family") ;;
        ret (dtype decl; _)
      end

    | tCoFix mfix n =>
      match nth_error mfix n with
      | None => raise (IllFormedFix mfix n)
      | Some decl =>
        XX <-  (fix check_types (mfix : mfixpoint term) {struct mfix}
        : typing_result (∥ All (fun x => isType Σ Γ (dtype x)) mfix ∥)
        := match mfix with
           | [] => ret (sq All_nil)
           | def :: mfix =>
            (* probably not tail recursive but needed so that next line terminates *)
             W <- infer_type infer Γ HΓ (dtype def) ;;
             Z <- check_types mfix ;;
             ret _
           end)
         mfix ;;
        YY <- (fix check_bodies (mfix' : mfixpoint term)
        (XX' : ∥ All (fun x => isType Σ Γ (dtype x)) mfix' ∥)
        {struct mfix'}
        : typing_result (All (fun d =>
            ∥ Σ ;;; Γ ,,, fix_context mfix |- dbody d : (lift0 #|fix_context mfix|) (dtype d) ∥) mfix')
              := match mfix' with
                 | [] => ret All_nil
                 | def :: mfix' =>
                   W1 <- infer_cumul infer (Γ ,,, fix_context mfix) _ (dbody def)
                                    (lift0 #|fix_context mfix| (dtype def)) _ ;;
                   Z <- check_bodies mfix' _ ;;
                   ret (All_cons W1 Z)
                 end) mfix _ ;;
        guarded <- check_eq_true (cofix_guard Σ Γ mfix) (Msg "Unguarded cofixpoint") ;;
        wfcofix <- check_eq_true (wf_cofixpoint Σ.1 mfix) (Msg "Ill-formed cofixpoint: not producing values in a mutually coinductive family") ;;
        ret (dtype decl; _)
      end

    | tPrim _ => raise (Msg "Primitive types are not supported")
    end.

  (* tRel *)
  Next Obligation. intros; sq; now econstructor. Defined.
  (* tSort *)
  Next Obligation.
    eapply (elimT wf_universe_reflect) in H.
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
    rename Heq_anonymous into HH.
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
    sq; econstructor; tea. now split.
  Defined.

  Lemma chop_firstn_skipn {A} n (l : list A) : chop n l = (firstn n l, skipn n l).
  Proof.
    induction n in l |- *; destruct l; simpl; auto.
    now rewrite IHn skipn_S.
  Qed.

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

  Lemma ctx_inst_wt Γ s Δ : ctx_inst Σ Γ s Δ -> All (welltyped Σ Γ) s.
  Proof.
    induction 1; try constructor; auto.
    now exists t.
  Qed.
  
  Next Obligation.
    destruct X7, X6, X3.
    sq. cbn in *.
    apply eqb_eq in H1.
    eapply eqb_eq in H0. subst I. cbn in *.
    eapply type_reduction_closed in t; tea.
    eapply validity in t.
    eapply isType_mkApps_Ind_inv in t as [pars [args []]]; eauto.
    rewrite chop_firstn_skipn in Heq_anonymous. noconf Heq_anonymous.
    subst params indices.
    eapply spine_subst_wt_terms in s. rewrite H1 in s.
    eapply All_impl; tea. intros ? []; auto. now exists x0.
  Qed.
  Next Obligation.
    cbn in *. sq.
    now eapply ctx_inst_wt.
  Qed.
    
  Next Obligation.
    cbn in *; sq.
    rename X5 into args.
    apply eqb_eq in H0. subst I.
    eapply eqb_eq in H1.
    eapply type_reduction_closed in X7; tea.
    rewrite chop_firstn_skipn in Heq_anonymous. noconf Heq_anonymous.
    subst params indices.
    eapply validity in X7.
    eapply isType_mkApps_Ind_inv in X7 as [pars [argsub []]]; eauto.
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
    rewrite -H1 in eq_params *.
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
      eapply weaken_wf_local; tea. eapply on_minductive_wf_params_indices_inst; tea.
      eapply spine_subst_smash in X1. eapply substitution_wf_local. exact X1.
      eapply wf_local_expand_lets, wf_local_smash_end.
      rewrite -app_context_assoc -subst_instance_app_ctx.
      eapply weaken_wf_local; tea. eapply on_minductive_wf_params_indices_inst; tea.
      rewrite -(subst_context_smash_context _ _ []).
      rewrite -(spine_subst_inst_subst X1).
      rewrite - !smash_context_subst /= !subst_context_nil.
      unshelve eapply compare_global_instance_sound in H3; pcuic.
      eapply (inductive_cumulative_indices X0); tea.
  Qed.
  
  Obligation Tactic := idtac.
  Next Obligation.
    intros. simpl in *. clearbody isty. subst filtered_var filtered_var0. subst.
    destruct cty as [A cty]. cbn in *. sq.
    apply eqb_eq in H0. subst ind'.
    eapply eqb_eq in H1.
    eapply type_reduction_closed in cty; tea.
    rewrite chop_firstn_skipn in Heq_anonymous. noconf Heq_anonymous.
    subst params indices.
    eapply validity in cty.
    eapply isType_mkApps_Ind_inv in cty as [pars [argsub []]]; eauto.
    eapply wf_case_predicate_context; tea.
    eapply eq_context_gen_wf_predicate; eauto.
    rewrite -(All2_length eq_params).
    now rewrite -H1.
  Qed.
    
  Next Obligation.
    intros; cbn in *. clearbody isty. subst filtered_var filtered_var0. subst.
    destruct cty as [A cty]. cbn in *. sq.
    apply eqb_eq in H0. subst ind'.
    eapply eqb_eq in H1. 
    eapply eq_context_gen_wf_predicate; tea.
    rewrite -(All2_length eq_params).
    eapply type_reduction_closed in cty; tea.
    eapply validity in cty.
    eapply isType_mkApps_Ind_inv in cty as [pars [argsub []]]; eauto.
    rewrite chop_firstn_skipn in Heq_anonymous. noconf Heq_anonymous.
    subst params indices.
    now rewrite -H1.
  Qed.

  Next Obligation.
    intros; cbn in *. clearbody isty. subst filtered_var filtered_var0. subst.
    destruct cty as [A cty]. cbn in *. clearbody wfp. sq.
    apply eqb_eq in H0. subst ind'.
    eapply eqb_eq in H1. 
    now rewrite /pctx in typ_pret.
  Qed.
  Next Obligation. 
    intros; cbn in *. clearbody isty. subst filtered_var filtered_var0. subst.
    destruct cty as [A cty]. cbn in *. clearbody wfp. sq.
    now eapply All2_fold_All2 in check_wfpctx_conv.
  Qed.

  Next Obligation.
    intros; cbn in *. clearbody isty wfp. subst filtered_var filtered_var0. subst.
    destruct cty as [A cty]. cbn in *. sq.
    eapply forall_nth_error_Alli. intros.
    split; auto.
  Qed.

  Next Obligation.
    intros; cbn in *. clearbody isty wfp. subst filtered_var filtered_var0. subst.
    destruct cty as [A cty]. cbn in *. sq.
    apply eqb_eq in H0. subst ind'.
    eapply eqb_eq in H1. 
    econstructor; eauto. 2-3:split; eauto; pcuic.
    - eapply type_reduction_closed in cty. 2:tea.
      eapply type_equality; tea.
      eapply equality_mkApps_eq => //. fvs. constructor => //.
      unshelve eapply compare_global_instance_sound in H3; tea; pcuic.
      rewrite chop_firstn_skipn in Heq_anonymous. noconf Heq_anonymous.
      subst params indices. rewrite -{1}(firstn_skipn (ci_npar ci) args).
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
    pose proof (on_declared_inductive X7) as [onmib oni].
    eapply onProjections in oni.
    destruct ind_ctors as [|? []] eqn:hctors => //.
    eapply type_Proj with (pdecl := (i, t0)).
    - split. split. eassumption. cbn. rewrite hctors. reflexivity.
      split. symmetry; eassumption. cbn in *.
      now apply beq_nat_true.
    - cbn. destruct (ssrbool.elimT (eqb_spec ind I)); [assumption|].
      eapply type_reduction_closed; eassumption.
    - eapply type_reduction_closed in X5; eauto.
      eapply validity in X5; eauto.
      destruct (ssrbool.elimT (eqb_spec ind I)); auto.
      unshelve eapply (PCUICInductives.isType_mkApps_Ind_inv _ X7 _) in X5 as [parsubst [argsubst [sp sp' cu]]]; eauto.
      pose proof (PCUICContextSubst.context_subst_length2 (PCUICSpine.inst_ctx_subst sp)).
      pose proof (PCUICContextSubst.context_subst_length2 (PCUICSpine.inst_ctx_subst sp')).
      autorewrite with len in H, H2.
      destruct (on_declared_inductive X7) eqn:ond.
      rewrite -o.(onNpars) -H.
      forward (o0.(onProjections)).
      intros H'; rewrite H' nth_error_nil // in Heq_anonymous.
      destruct ind_ctors as [|cs []]; auto.
      intros onps.
      unshelve epose proof (onps.(on_projs_noidx _ _ _ _ _ _)).
      destruct (ind_indices X6) => //.
      simpl in H2.
      rewrite List.skipn_length in H2.
      rewrite List.firstn_length. lia.
    - destruct ind_projs => //. rewrite nth_error_nil in Heq_anonymous; congruence.
  Defined.

  (* tFix *)
  Next Obligation. sq. constructor; auto. exists W; auto. Defined.
  Next Obligation. sq. now eapply All_mfix_wf in XX0. Defined.
  Next Obligation.
    sq. cbn in *. depelim XX.
    destruct i as [s HH].
    exists s.
    change (tSort s) with (lift0 #|fix_context mfix| (tSort s)).
    apply weakening; try assumption.
    now apply All_mfix_wf.
  Defined.
  Next Obligation.
    clear -XX HΣ. sq.
    now depelim XX.
  Defined.
  Next Obligation.
    assert (∥ All (fun d => ((Σ;;; Γ ,,, fix_context mfix |- dbody d : (lift0 #|fix_context mfix|) (dtype d)))%type) mfix ∥). {
      eapply All_sq, All_impl.  exact YY.
      cbn; intros ? ?. now sq. }
    sq; econstructor; try eassumption.
    symmetry; eassumption.
  Qed.

  (* tCoFix *)
  Next Obligation. sq. constructor; auto. exists W; auto. Defined.
  Next Obligation. sq. now eapply All_mfix_wf in XX. Defined.
  Next Obligation.
    sq. cbn in *. depelim XX'.
    destruct i as [s HH].
    exists s.
    change (tSort s) with (lift0 #|fix_context mfix| (tSort s)).
    apply weakening; try assumption.
    now apply All_mfix_wf.
  Defined.
  Next Obligation.
    clear -XX' HΣ. sq.
    now depelim XX'.
  Qed.
  Next Obligation.
    assert (∥ All (fun d => ((Σ;;; Γ ,,, fix_context mfix |- dbody d : (lift0 #|fix_context mfix|) (dtype d)))%type) mfix ∥). {
      eapply All_sq, All_impl.  exact YY.
      now cbn; intros ? []. }
    sq; econstructor; try eassumption.
    symmetry; eassumption.
  Qed.


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

  Program Definition check_isType Γ (HΓ : ∥ wf_local Σ Γ ∥) A
    : typing_result (∥ isType Σ Γ A ∥) :=
    s <- infer Γ HΓ A ;;
    s' <- reduce_to_sort HeΣ Γ s.π1 _ ;;
    ret _.
  Next Obligation. now eapply validity_wf. Defined.
  Next Obligation. destruct X0. sq. eexists. eapply type_reduction_closed; tea. Defined.

  Program Definition check Γ (HΓ : ∥ wf_local Σ Γ ∥) t A
    : typing_result (∥ Σ;;; Γ |- t : A ∥) :=
    check_isType Γ HΓ A ;;
    infer_cumul infer Γ HΓ t A _.

End Typecheck.
