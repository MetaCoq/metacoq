(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils uGraph.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICNormal PCUICSR
     PCUICGeneration PCUICReflect PCUICEquality PCUICInversion PCUICValidity
     PCUICWeakening PCUICPosition PCUICCumulativity PCUICSafeLemmata PCUICSN
     PCUICPretty PCUICArities PCUICConfluence PCUICSize
     PCUICContextConversion PCUICConversion PCUICWfUniverses
     PCUICGlobalEnv PCUICEqualityDec
     (* Used for support lemmas *)
     PCUICInductives PCUICWfUniverses
     PCUICContexts PCUICSubstitution PCUICSpine PCUICInductiveInversion
     PCUICClosed PCUICUnivSubstitution PCUICWeakeningEnv.

From MetaCoq.SafeChecker Require Import PCUICSafeReduce PCUICErrors
  PCUICSafeConversion PCUICWfReduction PCUICWfEnv.

From Equations Require Import Equations.
Require Import ssreflect ssrbool.

Local Set Keyed Unification.
Set Equations Transparent.

(** It otherwise tries [auto with *], very bad idea. *)
Ltac Coq.Program.Tactics.program_solve_wf ::= 
  match goal with 
  | |- @Wf.well_founded _ _ => auto with subterm wf
  | |- ?T => match type of T with
                | Prop => auto
                end
  end.

Section Typecheck.
  Context {cf : checker_flags} {Σ : global_env_ext} (HΣ : ∥ wf Σ ∥)
          (Hφ : ∥ on_udecl Σ.1 Σ.2 ∥)
          (G : universes_graph) (HG : is_graph_of_uctx G (global_ext_uctx Σ)).

  (* We get stack overflow on Qed after Equations definitions when this is transparent *)
  Opaque reduce_stack_full.

  Local Definition HΣ' : ∥ wf_ext Σ ∥.
  Proof.
    destruct HΣ, Hφ; now constructor.
  Defined.

  Notation hnf := (hnf HΣ).

  Definition isconv Γ := isconv_term Σ HΣ Hφ G HG Γ Conv.
  Definition iscumul Γ := isconv_term Σ HΣ Hφ G HG Γ Cumul.
  
  Program Definition convert Γ t u
          (ht : welltyped Σ Γ t) (hu : welltyped Σ Γ u)
    : typing_result (∥ Σ ;;; Γ |- t = u ∥) :=
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
    symmetry in Heq_anonymous; eapply eqb_term_spec in Heq_anonymous; tea.
    constructor. now constructor.
  Qed.
  Next Obligation.
    symmetry in Heq_anonymous; apply isconv_term_sound in Heq_anonymous.
    assumption.
  Qed.

  Program Definition convert_leq Γ t u
          (ht : welltyped Σ Γ t) (hu : welltyped Σ Γ u)
    : typing_result (∥ Σ ;;; Γ |- t <= u ∥) :=
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
    symmetry in Heq_anonymous; eapply leqb_term_spec in Heq_anonymous; tea.
    constructor. now constructor.
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
      u <- reduce_to_sort HΣ Γ tx.π1 _ ;;
      ret (u.π1; _).
    Next Obligation.
      eapply validity_wf; eassumption.
    Defined.
    Next Obligation.
      destruct HΣ, HΓ, X, X0.
      now constructor; eapply type_reduction.
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
      destruct HΣ, HΓ, hA, X, X0. constructor. eapply type_Cumul'; eassumption.
    Qed.
    
    Program Definition infer_scheme Γ HΓ t :
      typing_result (∑ ctx u, ∥ Σ ;;; Γ |- t : mkAssumArity ctx u ∥) :=
      '(T; p) <- infer Γ HΓ t;;
      match reduce_to_arity HΣ Γ T _ with
      | inleft car => ret (conv_ar_context car; conv_ar_univ car; _)
      | inright _ => TypeError (NotAnArity T)
      end.
    Next Obligation.
      intros; subst.
      cbn in *.
      eapply validity_wf; eauto.
    Qed.
    Next Obligation.
      destruct car as [? ? [r]].
      cbn.
      clear Heq_anonymous.
      sq.
      eapply type_reduction; eauto.
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

    Program Definition check_cumul_decl Γ d d' : wt_decl Σ Γ d -> wt_decl Σ Γ d' -> typing_result (∥ cumul_decls Σ Γ Γ d d' ∥) := 
      match d, d' return wt_decl Σ Γ d -> wt_decl Σ Γ d' -> typing_result _ with
      | {| decl_name := na; decl_body := Some b; decl_type := ty |},
        {| decl_name := na'; decl_body := Some b'; decl_type := ty' |} => 
        fun wtd wtd' =>
        eqna <- check_eq_true (eqb_binder_annot na na') (Msg "Binder annotations do not match") ;;
        cumb <- convert Γ b b' _ _ ;;
        cumt <- convert_leq Γ ty ty' _ _ ;;
        ret (let 'sq cumb := cumb in 
              let 'sq cumt := cumt in
              sq _)
      | {| decl_name := na; decl_body := None; decl_type := ty |},
        {| decl_name := na'; decl_body := None; decl_type := ty' |} => 
        fun wtd wtd' =>
        eqna <- check_eq_true (eqb_binder_annot na na') (Msg "Binder annotations do not match") ;;
        cumt <- convert_leq Γ ty ty' wtd wtd' ;;
        ret (let 'sq cumt := cumt in sq _)      
      | _, _ =>
        fun wtd wtd' => raise (Msg "While checking cumulativity of contexts: declarations do not match")
      end.
    Next Obligation.
      constructor; pcuics. now apply eqb_binder_annot_spec.
    Qed.
    Next Obligation.
      constructor; pcuics. now apply eqb_binder_annot_spec.
    Qed.

    Program Definition check_conv_decl Γ d d' : wt_decl Σ Γ d -> wt_decl Σ Γ d' -> typing_result (∥ conv_decls Σ Γ Γ d d' ∥) := 
      match d, d' return wt_decl Σ Γ d -> wt_decl Σ Γ d' -> typing_result _ with
      | {| decl_name := na; decl_body := Some b; decl_type := ty |},
        {| decl_name := na'; decl_body := Some b'; decl_type := ty' |} => 
        fun wtd wtd' =>
        eqna <- check_eq_true (eqb_binder_annot na na') (Msg "Binder annotations do not match") ;;
        cumb <- convert Γ b b' _ _ ;;
        cumt <- convert Γ ty ty' _ _ ;;
        ret (let 'sq cumb := cumb in 
              let 'sq cumt := cumt in
              sq _)
      | {| decl_name := na; decl_body := None; decl_type := ty |},
        {| decl_name := na'; decl_body := None; decl_type := ty' |} => 
        fun wtd wtd' =>
        eqna <- check_eq_true (eqb_binder_annot na na') (Msg "Binder annotations do not match") ;;
        cumt <- convert Γ ty ty' wtd wtd' ;;
        ret (let 'sq cumt := cumt in sq _)      
      | _, _ =>
        fun wtd wtd' => raise (Msg "While checking cumulativity of contexts: declarations do not match")
      end.
    Next Obligation.
      constructor; pcuics. now apply eqb_binder_annot_spec.
    Qed.
    Next Obligation.
      constructor; pcuics. now apply eqb_binder_annot_spec.
    Qed.

    Lemma cumul_ctx_rel_close Γ Δ Δ' : 
      cumul_ctx_rel Σ Γ Δ Δ' ->
      cumul_context Σ (Γ ,,, Δ) (Γ ,,, Δ').
    Proof.
      induction 1; pcuic.
    Qed.

    Lemma conv_ctx_rel_close Γ Δ Δ' : 
      conv_context_rel Σ Γ Δ Δ' ->
      conv_context Σ (Γ ,,, Δ) (Γ ,,, Δ').
    Proof.
      induction 1; pcuic. simpl. constructor; eauto.
      depelim p; constructor; auto.
    Qed.

    Lemma context_cumulativity_welltyped Γ Γ' t : 
      welltyped Σ Γ t ->
      cumul_context Σ Γ' Γ ->
      wf_local Σ Γ' ->
      welltyped Σ Γ' t.
    Proof.
      destruct HΣ.
      intros [s Hs] cum wfΓ'; exists s; eapply context_cumulativity; eauto.
    Qed.

    Lemma context_conversion_welltyped Γ Γ' t : 
      welltyped Σ Γ t ->
      conv_context Σ Γ' Γ ->
      wf_local Σ Γ' ->
      welltyped Σ Γ' t.
    Proof.
      destruct HΣ.
      intros [s Hs] cum wfΓ'; exists s; eapply context_conversion; eauto.
      now eapply conv_context_sym.
    Qed.
    
    Lemma context_cumulativity_wt_decl Γ Γ' d :
      wt_decl Σ Γ d ->
      cumul_context Σ Γ' Γ ->
      wf_local Σ Γ' ->
      wt_decl Σ Γ' d.
    Proof.
      destruct d as [na [b|] ty]; simpl;
      intuition pcuics; eapply context_cumulativity_welltyped; pcuics.
    Qed.
    
    Lemma context_conversion_wt_decl Γ Γ' d :
      wt_decl Σ Γ d ->
      conv_context Σ Γ' Γ ->
      wf_local Σ Γ' ->
      wt_decl Σ Γ' d.
    Proof.
      destruct d as [na [b|] ty]; simpl;
      intuition pcuics; eapply context_conversion_welltyped; pcuics.
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
    Lemma conv_ctx_rel_cons {Γ Δ Δ' d d'} (c : conv_context_rel Σ Γ Δ Δ') 
      (p : conv_decls Σ (Γ,,, Δ) (Γ ,,, Δ') d d') : 
      conv_context_rel Σ Γ (Δ ,, d) (Δ' ,, d').
    Proof.
      destruct d as [na [b|] ty], d' as [na' [b'|] ty']; try constructor; auto;
      depelim p; constructor; auto.
    Qed.

    Program Fixpoint check_cumul_ctx Γ Δ Δ' 
      (wfΔ : ∥ wf_local Σ (Γ ,,, Δ) ∥) (wfΔ' : ∥ wf_local Σ (Γ ,,, Δ') ∥) : 
      typing_result (∥ cumul_ctx_rel Σ Γ Δ Δ' ∥) :=
      match Δ, Δ' with
      | [], [] => ret (sq All2_fold_nil)
      | decl :: Δ, decl' :: Δ' => 
        cctx <- check_cumul_ctx Γ Δ Δ' _ _ ;;
        cdecl <- check_cumul_decl (Γ ,,, Δ) decl decl' _ _ ;;
        ret _
      | _, _ => raise (Msg "While checking cumulativity of contexts: contexts have not the same length")
      end.
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
        assert(cumul_context Σ (Γ ,,, Δ) (Γ ,,, Δ')).
        now apply cumul_ctx_rel_close.
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
        apply cumul_ctx_rel_cons. auto.
        eapply cumul_decls_irrel_sec; pcuics.
      Qed.
      Next Obligation.
        split. intros. intros []. congruence. intros []; congruence.
      Qed.
      Next Obligation.
        split. intros. intros []. congruence. intros []; congruence.
      Qed.
    
    Program Fixpoint check_conv_ctx Γ Δ Δ' 
      (wfΔ : ∥ wf_local Σ (Γ ,,, Δ) ∥) (wfΔ' : ∥ wf_local Σ (Γ ,,, Δ') ∥) : 
      typing_result (∥ conv_context_rel Σ Γ Δ Δ' ∥) :=
      match Δ, Δ' with
      | [], [] => ret (sq All2_fold_nil)
      | decl :: Δ, decl' :: Δ' => 
        cctx <- check_conv_ctx Γ Δ Δ' _ _ ;;
        cdecl <- check_conv_decl (Γ ,,, Δ) decl decl' _ _ ;;
        ret _
      | _, _ => raise (Msg "While checking convertibility of contexts: contexts have not the same length")
      end.
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
        assert(conv_context Σ (Γ ,,, Δ) (Γ ,,, Δ')).
        now apply conv_ctx_rel_close.
        simpl in *. eapply inv_wf_local in wfΔ as [wfΔ wfd].
        eapply inv_wf_local in wfΔ' as [wfΔ' wfd'].
        eapply context_conversion_wt_decl. 3:eassumption. all:pcuics.
      Qed.
      Next Obligation.
        pose proof HΣ as [wfΣ].
        destruct wfΔ as [wfΔ], wfΔ' as [wfΔ'], cctx as [cctx], cdecl as [cdecl].
        constructor.
        eapply inv_wf_local in wfΔ as [wfΔ wfd].
        eapply inv_wf_local in wfΔ' as [wfΔ' wfd'].
        apply conv_ctx_rel_cons. auto.
        eapply conv_decls_irrel_sec; pcuics.
      Qed.
      Next Obligation.
        split. intros. intros []. congruence. intros []; congruence.
      Qed.
      Next Obligation.
        split. intros. intros []. congruence. intros []; congruence.
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
    (All2i (fun i cdecl br =>
      let brctxty := case_branch_type ci.(ci_ind) mdecl idecl p br ptm i cdecl in
      ∥ (wf_local Σ (Γ ,,, br.(bcontext)) ×
       conv_context Σ (Γ ,,, br.(bcontext)) (Γ ,,, brctxty.1)) ×
      ((Σ ;;; Γ ,,, brctxty.1 |- br.(bbody) : brctxty.2) ×
      (Σ ;;; Γ ,,, brctxty.1 |- brctxty.2 : tSort ps)) ∥) 
      n ctors brs).
  
  Notation infer_ty :=
    (forall (Γ : context) (HΓ : ∥ wf_local Σ Γ ∥) (t : term), typing_result ({ A : term & ∥ Σ ;;; Γ |- t : A ∥ })).

  Section check_brs.
    Context (infer : infer_ty)
     (Γ : context) (wfΓ : ∥ wf_local Σ Γ ∥) (ps : Universe.t)
     (ci : case_info) (mdecl : mutual_inductive_body)
     (idecl : one_inductive_body) (p : predicate term) (ptm : term).
     
    Program Fixpoint check_branches (n : nat) (ctors : list constructor_body)
       (brs : list (branch term)) {struct brs}
       : typing_result (wt_brs Γ ci mdecl idecl p ps ptm ctors brs n) := 
      match ctors, brs return typing_result (wt_brs Γ ci mdecl idecl p ps ptm ctors brs n) with
      | [], [] => ret (All2i_nil : wt_brs Γ ci mdecl idecl p ps ptm [] [] n)
      | cdecl :: cdecls, br :: brs =>
        let brctxty := case_branch_type ci.(ci_ind) mdecl idecl p br ptm n cdecl in
        check_br_ctx <- check_context_rel infer Γ br.(bcontext) wfΓ ;;
        check_conv_ctx Γ br.(bcontext) brctxty.1 _ _ ;;
        Z <- infer_cumul infer (Γ ,,, br.(bcontext)) _ br.(bbody) brctxty.2 _ ;;
        X <- check_branches (S n) cdecls brs ;;
        ret (t:=wt_brs Γ ci mdecl idecl p ps ptm (cdecl :: cdecls) (br :: brs) n) (All2i_cons _ X)
      | [], _ :: _
      | _ :: _, [] => raise (Msg "wrong number of branches")
      end.

      Next Obligation.
        sq; now apply wf_local_app.
      Defined.
      Next Obligation.
        clear infer. todo "case".
      Defined.
      Next Obligation.
        clear infer. todo "case".
      Defined.
      Next Obligation.
        clear infer. todo "case".
      Defined.
      Obligation Tactic := idtac.
      Next Obligation.
        intros.
        clear infer. todo "case".
      Defined.
    End check_brs.

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
      pi <- reduce_to_prod HΣ Γ ty.π1 _ ;;
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
      I <- reduce_to_ind HΣ Γ cty.π1 _ ;;
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
      wfpctx <- check_context_rel infer Γ p.(pcontext) HΓ ;;
      let pctx := case_predicate_context ci.(ci_ind) mdecl idecl p in
      check_wfpctx_conv <- check_conv_ctx Γ p.(pcontext) pctx _ _ ;;
      retty <- infer_type infer (Γ ,,, p.(pcontext)) _ p.(preturn) ;;
      let '(ps; typ_pret) := retty in
      check_is_allowed_elimination ps (ind_kelim idecl);;
      let ptm := it_mkLambda_or_LetIn pctx p.(preturn) in
      let params := firstn ci.(ci_npar) args in
      check_brs <- check_branches infer Γ HΓ ps ci mdecl idecl p ptm 
        0 idecl.(ind_ctors) brs ;;
       ret (mkApps ptm (List.skipn ci.(ci_npar) args ++ [c]); _)

    | tProj (ind, n, k) c =>
      d <- lookup_ind_decl ind ;;
      match nth_error d.π2.π1.(ind_projs) k with
      | Some pdecl =>
        c_ty <- infer Γ HΓ c ;;
        I <- reduce_to_ind HΣ Γ c_ty.π1 _ ;;
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
    eapply type_reduction in X1 ; try eassumption.
    eapply validity in X1 ; try assumption. destruct X1 as [s HH].
    eapply inversion_Prod in HH ; try assumption.
    destruct HH as [s1 [_ [HH _]]].
    eexists. eassumption.
  Defined.
  Next Obligation.
    cbn in *; sq; eapply type_App'.
    2: eassumption.
    eapply type_reduction; eassumption.
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

  (* tCase *)
  Obligation Tactic := intros; Program.Tactics.destruct_conjs; cbn in *; subst.
  Next Obligation. sq. eapply validity in X as []; eauto.
    eexists; eauto using validity_wf. Defined.
  Next Obligation. sq. now eapply wf_local_app. Defined.
  Next Obligation. sq. eapply wf_local_app; auto. todo "case". Defined.
  Next Obligation. sq. now eapply wf_local_app. Defined.
  Next Obligation.
    noconf Heq_anonymous. rename filtered_var into mdecl.
    destruct H, X6, X7, X8.
    noconf Heq_I; noconf Heq_I'; noconf Heq_I''.
    noconf Heq_retty. sq. clear H H0 r r1.
    rename X0 into idecl.
    change (eqb ci.(ci_ind) I = true) in H1.
    destruct (eqb_spec ci.(ci_ind) I) as [e|e]; [destruct e|discriminate].
    change (eqb (ind_npars mdecl) ci.(ci_npar) = true) in H2.
    destruct (eqb_spec (ind_npars mdecl) ci.(ci_npar)) as [e|e]; [|discriminate].
    rewrite -e /ptm. 
    todo "case".
(*
    rename Heq_anonymous into HH. symmetry in HH.
    simpl in *.
    rewrite <- e in HH.
    eapply PCUICInductiveInversion.WfArity_build_case_predicate_type in HH; eauto.
    destruct HH as [[s Hs] ?]. eexists; eauto.
    eapply isType_red; [|eassumption].
    eapply validity; eauto.
    rewrite mkAssumArity_it_mkProd_or_LetIn in X.
    eapply validity in X; auto.
    eapply PCUICInductives.isType_it_mkProd_or_LetIn_inv in X; eauto.
    eapply isType_wf_universes in X; auto.
    now exact (elimT wf_universe_reflect X).*)
  Defined.
  (* The obligation tactic removes useful lets here. *)
  Obligation Tactic := idtac.

  (*Next Obligation.
    intros.
    cbn. sq. splits.
    - now eapply wf_local_app.
    - now eapply conv_ctx_rel_close.
    - eapply context_conversion; tea.
      eapply wf_local_app; tas. todo "cases".
      now eapply conv_ctx_rel_close.
    - todo "cases".
  Defined.*)
  (*Next Obligation.
    intros. cbn. subst filtered_var.
    idtac; Program.Tactics.destruct_conjs. simpl proj1_sig in *.
    cbn in *.
    destruct X6, X8, H; noconf Heq_I; noconf Heq_I'; noconf Heq_I''.
    noconf Heq_anonymous. noconf Heq_retty. destruct wfpctx as [wfpctx].
    noconf H.
    clear H H0. destruct X5 as [Hc]. sq. subst t.
    change (eqb ci.(ci_ind) I = true) in H1.
    destruct (eqb_spec ci.(ci_ind) I) as [e|e]; [destruct e|discriminate].
    change (eqb (ind_npars d) ci.(ci_npar) = true) in H2.
    destruct (eqb_spec (ind_npars d) ci.(ci_npar)) as [e|e]; [|discriminate].
    todo "cases".
    (* econstructor; eauto.
    todo "case". branches *)
    (*symmetry in Heq_anonymous1.
    unfold iscumul in Heq_anonymous1. simpl in Heq_anonymous1.
    apply isconv_term_sound in Heq_anonymous1.
    red in Heq_anonymous1.
    noconf Heq_I''.
    noconf Heq_I'. noconf Heq_I.
    noconf Heq_d. noconf Heq_d'.
    noconf Heq_IS. noconf Heq_IS'.
    simpl in *; sq.
    change (eqb ind I = true) in H0.
    destruct (eqb_spec ind I) as [e|e]; [destruct e|discriminate H0].
    change (eqb (ind_npars d) par = true) in H1.
    destruct (eqb_spec (ind_npars d) par) as [e|e]; [|discriminate]; subst.
    assert (wfΣ : wf_ext Σ) by (split; auto).
    eapply type_reduction in X11; eauto.
    have val:= validity wfΣ X11.
    eapply type_Cumul' in typ_p; [| |eassumption].
    2:{ eapply PCUICInductiveInversion.WfArity_build_case_predicate_type; eauto.
        eapply validity in typ_p; eauto.
        rewrite mkAssumArity_it_mkProd_or_LetIn in typ_p.
        eapply PCUICInductives.isType_it_mkProd_or_LetIn_inv in typ_p; eauto.
        apply isType_wf_universes in typ_p; auto.
        now exact (elimT wf_universe_reflect typ_p). }
    have [pctx' da] : (∑ pctx', destArity [] pty' =  Some (pctx', X0)).
    { symmetry in Heq_anonymous0.
      unshelve eapply (PCUICInductives.build_case_predicate_type_spec (Σ.1, ind_universes d)) in Heq_anonymous0 as [parsubst [_ ->]].
      eauto. eapply (PCUICWeakeningEnv.on_declared_inductive wfΣ) as [? ?]. eauto.
      eexists. rewrite !destArity_it_mkProd_or_LetIn; simpl. reflexivity. }
    eapply PCUICInductiveInversion.build_branches_type_wt. 6:eapply typ_p. all:eauto.*)
  Defined.*)
  
(*
  Next Obligation.
    intros. clearbody btyswf. idtac; Program.Tactics.program_simplify.
    symmetry in Heq_anonymous1.
    unfold iscumul in Heq_anonymous1. simpl in Heq_anonymous1.
    apply isconv_term_sound in Heq_anonymous1.
    noconf Heq_I''. noconf Heq_I'. noconf Heq_I.
    noconf Heq_d. noconf Heq_d'. 
    noconf Heq_IS. noconf Heq_IS'.
    simpl in *.
    assert (∥ All2 (fun x y  => ((fst x = fst y) *
                              (Σ;;; Γ |- snd x : snd y) * isType Σ Γ y.2)%type) brs btys ∥). {
      solve_all. simpl in *.
      destruct btyswf. eapply All2_sq. solve_all. simpl in *; intuition (sq; auto). }
    clear H3. sq.
    change (eqb ind I = true) in H0.
    destruct (eqb_spec ind I) as [e|e]; [destruct e|discriminate H0].
    change (eqb (ind_npars d) par = true) in H1.
    destruct (eqb_spec (ind_npars d) par) as [e|e]; [|discriminate]; subst.
    assert (wfΣ : wf_ext Σ) by (split; auto).
    eapply type_reduction in X11; eauto.
    eapply type_Cumul' in typ_p; eauto.
    2:{ eapply PCUICInductiveInversion.WfArity_build_case_predicate_type; eauto.
        eapply validity in X11; eauto.
        eapply validity in typ_p; auto.
        rewrite mkAssumArity_it_mkProd_or_LetIn in typ_p.
        eapply PCUICInductives.isType_it_mkProd_or_LetIn_inv in typ_p; eauto.
        apply isType_wf_universes in typ_p; auto.
        now exact (elimT wf_universe_reflect typ_p). }
    eapply type_Case with (pty0:=pty'); tea.
    - reflexivity.
    - symmetry; eassumption.
    - destruct isCoFinite; auto.
    - symmetry; eauto.
  Defined.
*)
  Obligation Tactic := Program.Tactics.program_simplify ; eauto 2.

  (* tProj *)
  Next Obligation. simpl; eauto using validity_wf. Defined.
  Next Obligation.
    simpl in *; sq; eapply type_Proj with (pdecl := (i, t0)).
    - split. eassumption. split. symmetry; eassumption. cbn in *.
      now apply beq_nat_true.
    - cbn. destruct (ssrbool.elimT (eqb_spec ind I)); [assumption|].
      eapply type_reduction; eassumption.
    - eapply type_reduction in X5; eauto.
      eapply validity in X5; eauto.
      destruct (ssrbool.elimT (eqb_spec ind I)); auto.
      unshelve eapply (PCUICInductives.isType_mkApps_Ind _ X7 _) in X5 as [parsubst [argsubst [[sp sp'] cu]]]; eauto.
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
  Defined.

  (* tFix *)
  Next Obligation. sq. constructor; auto. exists W; auto. Defined.
  Next Obligation. sq. now eapply PCUICWeakening.All_mfix_wf in XX0. Defined.
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
  Next Obligation. sq. now eapply PCUICWeakening.All_mfix_wf in XX. Defined.
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
    s' <- reduce_to_sort HΣ Γ s.π1 _ ;;
    ret _.
  Next Obligation. now eapply validity_wf. Defined.
  Next Obligation. destruct X0. sq. eexists. eapply type_reduction; tea. Defined.

  Program Definition check Γ (HΓ : ∥ wf_local Σ Γ ∥) t A
    : typing_result (∥ Σ;;; Γ |- t : A ∥) :=
    check_isType Γ HΓ A ;;
    infer_cumul infer Γ HΓ t A _.

End Typecheck.
