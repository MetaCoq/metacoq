(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils uGraph.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICLiftSubst PCUICUnivSubst PCUICSigmaCalculus PCUICTyping PCUICNormal PCUICSR
     PCUICWeakeningEnvConv PCUICWeakeningEnvTyp
     PCUICGeneration PCUICReflect PCUICEquality PCUICInversion PCUICValidity
     PCUICWeakeningConv PCUICWeakeningTyp
     PCUICPosition PCUICCumulativity PCUICSafeLemmata PCUICSN
     PCUICPretty PCUICArities PCUICConfluence PCUICSize
     PCUICContextConversion PCUICConversion PCUICWfUniverses
     PCUICGlobalEnv PCUICEqualityDec
     (* Used for support lemmas *)
     PCUICInductives PCUICWfUniverses
     PCUICContexts PCUICSubstitution PCUICSpine PCUICInductiveInversion
     PCUICClosed PCUICClosedTyp PCUICUnivSubstitutionConv PCUICUnivSubstitutionTyp
     PCUICOnFreeVars PCUICWellScopedCumulativity
     BDTyping BDFromPCUIC BDToPCUIC.

From MetaCoq.SafeChecker Require Import PCUICSafeReduce PCUICErrors
  PCUICSafeConversion PCUICWfReduction PCUICWfEnv PCUICTypeChecker.

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

Section OnUdecl.
  Context {cf:checker_flags}.

  Lemma In_unfold_inj {A} (f : nat -> A) n i : 
    (forall i j, f i = f j -> i = j) ->
    In (f i) (unfold n f) <-> i < n.
  Proof.
    intros hf. split.
    now apply In_unfold_inj.
    intros.
    induction n in i, H |- *; simpl => //. lia.
    eapply in_app_iff.
    destruct (eq_dec i n). subst. right; left; auto.
    left. eapply IHn. lia.
  Qed.

  Lemma In_Var_global_ext_poly {n Σ inst cstrs} : 
    n < #|inst| ->
    LevelSet.mem (Level.Var n) (global_ext_levels (Σ, Polymorphic_ctx (inst, cstrs))).
  Proof.
    intros Hn.
    unfold global_ext_levels; simpl.
      apply LevelSet.mem_spec; rewrite LevelSet.union_spec. left.
    rewrite /AUContext.levels /= mapi_unfold.
    apply LevelSetProp.of_list_1, InA_In_eq.
    eapply In_unfold_inj; try congruence.
  Qed.
  
  Lemma on_udecl_poly_bounded Σ inst cstrs :
    wf Σ ->
    on_udecl Σ (Polymorphic_ctx (inst, cstrs)) ->
    closedu_cstrs #|inst| cstrs.
  Proof.
    rewrite /on_udecl. intros wfΣ [_ [nlevs _]].
    red.
    rewrite /closedu_cstrs.
    intros x incstrs. simpl in nlevs.
    specialize (nlevs x incstrs).
    destruct x as [[l1 p] l2].
    destruct nlevs.
    apply LevelSetProp.Dec.F.union_1 in H.
    apply LevelSetProp.Dec.F.union_1 in H0.
    destruct H. eapply LSet_in_poly_bounded in H.
    destruct H0. eapply LSet_in_poly_bounded in H0. simpl. now rewrite H H0.
    eapply (LSet_in_global_bounded #|inst|) in H0 => //. simpl.
    now rewrite H H0.
    eapply (LSet_in_global_bounded #|inst|) in H => //. simpl.
    destruct H0. eapply LSet_in_poly_bounded in H0. simpl. now rewrite H H0.
    eapply (LSet_in_global_bounded #|inst|) in H0 => //. simpl.
    now rewrite H H0.
  Qed.
 
  Lemma subst_instance_level_lift inst l : 
    closedu_level #|inst| l ->
    subst_instance_level (lift_instance #|inst| (level_var_instance 0 inst)) l = lift_level #|inst| l.
  Proof.
    destruct l => // /= /Nat.ltb_lt ltn.
    rewrite nth_nth_error.
    destruct nth_error eqn:eq. move:eq.
    rewrite nth_error_map /level_var_instance [mapi_rec _ _ _]mapi_unfold (proj1 (nth_error_unfold _ _ _) ltn).
    simpl. now intros [=].
    eapply nth_error_None in eq. len in eq. lia.
  Qed.
  
  Lemma subst_instance_level_var_instance inst l : 
    closedu_level #|inst| l ->
    subst_instance_level (level_var_instance 0 inst) l = l.
  Proof.
    destruct l => // /= /Nat.ltb_lt ltn.
    rewrite /level_var_instance.
    rewrite nth_nth_error.
    now rewrite /level_var_instance [mapi_rec _ _ _]mapi_unfold (proj1 (nth_error_unfold _ _ _) ltn).
  Qed.

  Lemma variance_universes_spec Σ ctx v univs u u' : 
    wf_ext (Σ, ctx) ->
    wf_ext (Σ, univs) ->
    variance_universes ctx v = Some (univs, u, u') ->
    consistent_instance_ext (Σ, univs) ctx u ×
    consistent_instance_ext (Σ, univs) ctx u'.
  Proof.
    intros wfctx wfext.
    unfold variance_universes. destruct ctx as [|[inst cstrs]] => //.
    intros [= eq].
    set (vcstrs := ConstraintSet.union _ _) in *.
    subst univs. simpl.
    subst u u'. autorewrite with len.
    repeat (split; auto).
    - rewrite forallb_map /level_var_instance.
      rewrite [mapi_rec _ _ _]mapi_unfold forallb_unfold /= //.
      intros x Hx. apply In_Var_global_ext_poly. len.
    - destruct wfext as [onΣ onu]. simpl in *.
      destruct onu as [_ [_ [_ sat]]].
      do 2 red in sat.
      unfold PCUICLookup.global_ext_constraints in sat. simpl in sat.
      red. destruct check_univs => //.
      unfold valid_constraints0.
      intros val vsat.
      destruct sat as [val' allsat].
      red.
      intro. red in vsat.
      specialize (vsat x). intros hin. apply vsat.
      unfold global_ext_constraints. simpl.
      rewrite ConstraintSet.union_spec; left.
      rewrite /vcstrs !ConstraintSet.union_spec.
      left. right.
      rewrite In_lift_constraints.
      rewrite -> In_subst_instance_cstrs in hin.
      destruct hin as [c' [eqx inc']]. clear vsat.
      subst x. eexists. unfold subst_instance_cstr.
      unfold lift_constraint. split; eauto. destruct c' as [[l comp] r].
      simpl.
      destruct wfctx as [_ wfctx]. simpl in wfctx.
      eapply on_udecl_poly_bounded in wfctx; auto.
      specialize (wfctx _ inc'). simpl in wfctx.
      move/andP: wfctx => [cll clr].
      rewrite !subst_instance_level_lift //.
    - rewrite /level_var_instance.
      rewrite [mapi_rec _ _ _]mapi_unfold forallb_unfold /= //.
      intros x Hx. apply In_Var_global_ext_poly. len.
    - destruct wfext as [onΣ onu]. simpl in *.
      destruct onu as [_ [_ [_ sat]]].
      do 2 red in sat.
      unfold PCUICLookup.global_ext_constraints in sat. simpl in sat.
      red. destruct check_univs => //.
      unfold valid_constraints0.
      intros val vsat.
      destruct sat as [val' allsat].
      red.
      intro. red in vsat.
      specialize (vsat x). intros hin. apply vsat.
      unfold global_ext_constraints. simpl.
      rewrite ConstraintSet.union_spec; left.
      rewrite /vcstrs !ConstraintSet.union_spec.
      left. left.
      rewrite -> In_subst_instance_cstrs in hin.
      destruct hin as [c' [eqx inc']]. clear vsat.
      subst x.
      destruct c' as [[l comp] r].
      simpl.
      destruct wfctx as [_ wfctx]. simpl in wfctx.
      eapply on_udecl_poly_bounded in wfctx; auto.
      specialize (wfctx _ inc'). simpl in wfctx.
      move/andP: wfctx => [cll clr]. rewrite /subst_instance_cstr /=.
      rewrite !subst_instance_level_var_instance //.
  Qed.

End OnUdecl.

Section CheckEnv.
  Context {cf:checker_flags} {cu : check_univs_tc}.

  Definition check_wf_type (kn : kername) (Σ : global_env_ext) (HΣ : ∥ wf_ext Σ ∥)
    G (HG : is_graph_of_uctx G (global_ext_uctx Σ)) t
    : EnvCheck (∥ isType Σ [] t ∥) :=
    wrap_error Σ (string_of_kername kn) (check_isType HΣ G HG [] sq_wfl_nil t).

  Definition check_wf_judgement kn Σ HΣ G HG t ty
    : EnvCheck (∥ Σ;;; [] |- t : ty ∥)
    := wrap_error Σ (string_of_kername kn) (check HΣ G HG [] sq_wfl_nil t ty).

  Definition infer_term Σ (HΣ : ∥ wf_ext Σ ∥) G HG t :=
    wrap_error Σ "toplevel term" (infer HΣ G HG [] sq_wfl_nil t).

  Program Fixpoint check_fresh id env : EnvCheck (∥ fresh_global id env ∥) :=
    match env with
    | [] => ret (sq (Forall_nil _))
    | g :: env =>
      p <- check_fresh id env;;
      match eq_constant id g.1 with
      | true => EnvError (empty_ext env) (AlreadyDeclared (string_of_kername id))
      | false => ret _
      end
    end.
  Next Obligation.
    sq. constructor; tas. simpl.
    change (false = eqb id k) in Heq_anonymous.
    destruct (eqb_spec id k); [discriminate|].
    easy.
  Defined.

  (* We pack up all the information required on the global environment and graph in a 
    single record. *)

  Record wf_env {cf:checker_flags} := { 
    wf_env_env :> global_env;
    wf_env_wf :> ∥ wf wf_env_env ∥;
    wf_env_graph :> universes_graph;
    wf_env_graph_wf : is_graph_of_uctx wf_env_graph (global_uctx wf_env_env)
  }.

  Record wf_env_ext {cf:checker_flags} := { 
      wf_env_ext_env :> global_env_ext;
      wf_env_ext_wf :> ∥ wf_ext wf_env_ext_env ∥;
      wf_env_ext_graph :> universes_graph;
      wf_env_ext_graph_wf : is_graph_of_uctx wf_env_ext_graph (global_ext_uctx wf_env_ext_env)
  }.

  Definition wf_env_sq_wf (Σ : wf_env) : ∥ wf Σ ∥.
  Proof.
    destruct (wf_env_wf Σ).
    sq. apply X.
  Qed.
  
  Definition wf_env_ext_sq_wf (Σ : wf_env_ext) : ∥ wf Σ ∥.
  Proof.
    destruct (wf_env_ext_wf Σ).
    sq. apply X.
  Qed.

  Section UniverseChecks.
  Obligation Tactic := idtac.

  Program Definition check_udecl id (Σ : global_env) (HΣ : ∥ wf Σ ∥) G
          (HG : is_graph_of_uctx G (global_uctx Σ)) (udecl : universes_decl)
    : EnvCheck (∑ uctx', gc_of_uctx (uctx_of_udecl udecl) = Some uctx' /\
                         ∥ on_udecl Σ udecl ∥) :=
    let levels := levels_of_udecl udecl in
    let global_levels := global_levels Σ in
    let all_levels := LevelSet.union levels global_levels in
    check_eq_true (LevelSet.for_all (fun l => negb (LevelSet.mem l global_levels)) levels)
       (empty_ext Σ, IllFormedDecl id (Msg ("non fresh level in " ^ print_lset levels)));;
    check_eq_true (ConstraintSet.for_all (fun '(l1, _, l2) => LevelSet.mem l1 all_levels && LevelSet.mem l2 all_levels) (constraints_of_udecl udecl))
                                    (empty_ext Σ, IllFormedDecl id (Msg ("non declared level in " ^ print_lset levels ^
                                    " |= " ^ print_constraint_set (constraints_of_udecl udecl))));;
    check_eq_true match udecl with
                  | Monomorphic_ctx ctx
                    => LevelSet.for_all (negb ∘ Level.is_var) ctx.1
                  | _ => true
                  end (empty_ext Σ, IllFormedDecl id (Msg "Var level in monomorphic context")) ;;
    (* TODO: could be optimized by reusing G *)
    match gc_of_uctx (uctx_of_udecl udecl) as X' return (X' = _ -> EnvCheck _) with
    | None => fun _ =>
      raise (empty_ext Σ, IllFormedDecl id (Msg "constraints trivially not satisfiable"))
    | Some uctx' => fun Huctx =>
      check_eq_true (wGraph.is_acyclic (add_uctx uctx' G))
                    (empty_ext Σ, IllFormedDecl id (Msg "constraints not satisfiable"));;
      ret (uctx'; _)
    end eq_refl.
  Next Obligation.
    Tactics.program_simpl.
  Qed.
  Next Obligation.
    simpl. intros. rewrite <- Huctx.
    split; auto.
    assert (HH: ConstraintSet.For_all
                  (fun '(l1, _, l2) =>
                     LevelSet.In l1 (LevelSet.union (levels_of_udecl udecl) (global_levels Σ)) /\
                     LevelSet.In l2 (LevelSet.union (levels_of_udecl udecl) (global_levels Σ)))
                  (constraints_of_udecl udecl)). {
      clear -H0. apply ConstraintSet.for_all_spec in H0.
      2: now intros x y [].
      intros [[l ct] l'] Hl. specialize (H0 _ Hl). simpl in H0.
      apply andb_true_iff in H0. destruct H0 as [H H0].
      apply LevelSet.mem_spec in H. apply LevelSet.mem_spec in H0.
      now split. }
    repeat split.
    - clear -H. apply LevelSet.for_all_spec in H.
      2: now intros x y [].
      intros l Hl. specialize (H l Hl); cbn in H.
      apply negb_true_iff in H. now apply LevelSetFact.not_mem_iff in H.
    - exact HH.
    - clear -H1. destruct udecl; trivial.
    - clear -HΣ HH Huctx H2 HG. unfold gc_of_uctx, uctx_of_udecl in *.
      simpl in *.
      unfold satisfiable_udecl.
      unfold is_graph_of_uctx in HG. unfold gc_of_uctx in *.
      case_eq (gc_of_constraints (global_uctx Σ).2);
        [|intro XX; rewrite XX in HG; contradiction HG].
      intros Σctrs HΣctrs.
      unfold global_ext_constraints. simpl in *.
      rewrite HΣctrs in HG. simpl in HG.
      case_eq (gc_of_constraints (constraints_of_udecl udecl));
        [|intro XX; rewrite XX in Huctx; discriminate Huctx].
      intros ctrs Hctrs. rewrite Hctrs in Huctx. simpl in *.
      eapply (is_consistent_spec (global_ext_uctx (Σ, udecl))).
      { sq. apply wf_global_uctx_invariants in HΣ.
        split.
        + clear -HΣ. cbn. apply LevelSet.union_spec; right.
          apply HΣ.
        + intros [[l ct] l'] Hl.
          apply ConstraintSet.union_spec in Hl. destruct Hl.
          apply (HH _ H). clear -HΣ H ct. destruct HΣ as [_ HΣ].
          specialize (HΣ (l, ct, l') H).
          split; apply LevelSet.union_spec; right; apply HΣ. }
      unfold is_consistent, global_ext_uctx, gc_of_uctx, global_ext_constraints.
      simpl.
      pose proof (gc_of_constraints_union (constraints_of_udecl udecl) (global_constraints Σ)).
      rewrite {}HΣctrs {}Hctrs in H. simpl in H.
      destruct gc_of_constraints. simpl in H.
      inversion Huctx; subst; clear Huctx.
      clear -H H2 cf. rewrite add_uctx_make_graph in H2.
      refine (eq_rect _ (fun G => wGraph.is_acyclic G = true) H2 _ _).
      apply graph_eq; try reflexivity.
      + assert(make_graph (global_ext_levels (Σ, udecl), t) = 
        make_graph (global_ext_levels (Σ, udecl), (GoodConstraintSet.union ctrs Σctrs))).
        apply graph_eq. simpl; reflexivity.
        unfold make_graph. simpl.
        now rewrite H. simpl. reflexivity.
        rewrite H0. reflexivity.
      + now simpl in H. 
    Qed.

  Program Definition check_wf_env_ext (Σ : global_env) (id : kername) (wfΣ : ∥ wf Σ ∥) (G : universes_graph) 
    (wfG : is_graph_of_uctx G (global_uctx Σ)) (ext : universes_decl) : 
    EnvCheck (∑ G, is_graph_of_uctx G (global_ext_uctx (Σ, ext)) /\ ∥ wf_ext (Σ, ext) ∥) :=
    uctx <- check_udecl (string_of_kername id) Σ wfΣ G wfG ext ;;
    let G' := add_uctx uctx.π1 G in
    ret (G'; _).
  Next Obligation.
    intros. simpl.
    destruct uctx as [uctx' [gcof onu]].
    subst G'.
    simpl. split.
    red in wfG |- *.
    unfold global_ext_uctx, gc_of_uctx. simpl.
    unfold gc_of_uctx in gcof. simpl in gcof.
    unfold gc_of_uctx in wfG. unfold global_ext_constraints. simpl in wfG |- *.
    pose proof (gc_of_constraints_union (constraints_of_udecl ext) (global_constraints Σ)).
    destruct (gc_of_constraints (global_constraints Σ)); simpl in *; auto.
    destruct (gc_of_constraints (constraints_of_udecl ext)); simpl in *; auto.
    noconf gcof.
    simpl in H.
    destruct gc_of_constraints; simpl in *; auto.
    symmetry. subst G.
    rewrite add_uctx_make_graph.
    apply graph_eq; simpl; auto.
    reflexivity. now rewrite H. discriminate.
    sq. pcuic.
  Qed.

  Program Definition make_wf_env_ext (Σ : wf_env) id (ext : universes_decl) : 
    EnvCheck ({ Σ' : wf_env_ext | Σ'.(wf_env_ext_env) = (Σ, ext)}) :=
    '(G; pf) <- check_wf_env_ext Σ id _ Σ _ ext ;;
    ret (exist {| wf_env_ext_env := (Σ, ext) ;
           wf_env_ext_wf := _ ;
           wf_env_ext_graph := G ;
           wf_env_ext_graph_wf := _ |} eq_refl).
    Next Obligation.
      intros []; simpl; intros. sq. apply wf_env_wf0.
    Qed.
    Next Obligation.
      intros []; simpl; intros. sq. apply wf_env_graph_wf0.
    Qed.
    Next Obligation.
      intros []; simpl; intros.
      destruct pf. destruct s. subst x.
      sq. apply w.
    Qed.
    Next Obligation.
      intros []; simpl; intros.
      destruct pf. destruct s. subst x.
      exact i.
    Qed.
  End UniverseChecks.

  Equations infer_typing (Σ : global_env_ext) (HΣ : ∥ wf_ext Σ ∥)
    (G : universes_graph) (HG : is_graph_of_uctx G (global_ext_uctx Σ)) Γ (wfΓ : ∥ wf_local Σ Γ ∥) t :
      typing_result (∑ T, ∥ Σ ;;; Γ |- t : T ∥) :=
    infer_typing Σ HΣ G HG Γ wfΓ t :=
      typing_error_forget (infer HΣ G HG Γ wfΓ t) ;;
      ret _.
  Next Obligation.
    exists y.
    sq.
    now apply infering_typing.
  Qed.
  
  Definition check_type_wf_env (Σ : wf_env_ext) Γ (wfΓ : ∥ wf_local Σ Γ ∥) t T : typing_result (∥ Σ ;;; Γ |- t : T ∥) := 
    check (wf_env_ext_wf Σ) Σ (wf_env_ext_graph_wf Σ) Γ wfΓ t T.
  
  Definition infer_wf_env (Σ : wf_env_ext) Γ (wfΓ : ∥ wf_local Σ Γ ∥) t : typing_result (∑ T, ∥ Σ ;;; Γ |- t ▹ T ∥) := 
    infer (wf_env_ext_wf Σ) Σ (wf_env_ext_graph_wf Σ) Γ wfΓ t.
  
  Equations infer_type_wf_ext (Σ : global_env_ext) (wfΣ : ∥ wf_ext Σ ∥) 
    (G : universes_graph) (HG : is_graph_of_uctx G (global_ext_uctx Σ)) Γ (wfΓ : ∥ wf_local Σ Γ ∥) t : 
    typing_result (∑ u, ∥ Σ ;;; Γ |- t : tSort u∥) := 
    infer_type_wf_ext Σ wfΣ G HG Γ wfΓ t :=
      typing_error_forget (infer_type wfΣ (infer wfΣ G HG) Γ wfΓ t) ;;
      ret _.
  Next Obligation.
    exists y.
    sq.
    now apply infering_sort_typing.
  Qed.

  Definition infer_type_wf_env (Σ : wf_env_ext) Γ (wfΓ : ∥ wf_local Σ Γ ∥) t : typing_result (∑ u, ∥ Σ ;;; Γ |- t : tSort u ∥) := 
    infer_type_wf_ext Σ (wf_env_ext_wf Σ) Σ (wf_env_ext_graph_wf Σ) Γ wfΓ t.

  Definition check_context_wf_env (Σ : wf_env_ext) (Γ : context) : typing_result (∥ wf_local Σ Γ ∥) :=
    check_context (wf_env_ext_wf Σ) Σ (wf_env_ext_graph_wf Σ)
      (infer (wf_env_ext_wf Σ) Σ (wf_env_ext_graph_wf Σ)) Γ.
      
  (* Notation " ' pat <- m ;; f " := (bind m (fun pat => f)) (pat pattern, right associativity, at level 100, m at next level). *)
  
  Lemma inversion_it_mkProd_or_LetIn Σ {wfΣ : wf Σ.1}:
    forall {Γ Δ s A},
      Σ ;;; Γ |- it_mkProd_or_LetIn Δ (tSort s) : A ->
      isType Σ Γ (it_mkProd_or_LetIn Δ (tSort s)).
  Proof.
    unfold isType. unfold PCUICTypingDef.typing. intros Γ Δ s A h. revert Γ s A h.
    induction Δ using rev_ind; intros.
    - simpl in h. eapply inversion_Sort in h as (?&?&?).
      eexists; constructor; eauto. apply wfΣ.
    - destruct x as [na [b|] ty]; simpl in *;
      rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /= in h *.
      * eapply inversion_LetIn in h as [s' [? [? [? [? ?]]]]]; auto.
        specialize (IHΔ _ _ _ t1) as [s'' vdefty].
        exists s''.
        eapply type_Cumul_alt. econstructor; eauto. pcuic.
        eapply red_cumul. repeat constructor.
      * eapply inversion_Prod in h as [? [? [? [? ]]]]; auto.
        specialize (IHΔ _ _ _ t0) as [s'' Hs''].
        eexists (Universe.sort_of_product x s'').
        eapply type_Cumul'; eauto. econstructor; pcuic. pcuic.
        reflexivity.
  Qed.
  
  Program Fixpoint check_type_local_ctx (Σ : wf_env_ext) Γ Δ s (wfΓ : ∥ wf_local Σ Γ ∥) : 
    typing_result (∥ type_local_ctx (lift_typing typing) Σ Γ Δ s ∥) := 
    match Δ with
    | [] => match wf_universeb Σ s with true => ret _ | false => raise (Msg "Ill-formed universe") end
    | {| decl_body := None; decl_type := ty |} :: Δ => 
      checkΔ <- check_type_local_ctx Σ Γ Δ s wfΓ ;;
      checkty <- check_type_wf_env Σ (Γ ,,, Δ) _ ty (tSort s) ;;
      ret _
    | {| decl_body := Some b; decl_type := ty |} :: Δ => 
      checkΔ <- check_type_local_ctx Σ Γ Δ s wfΓ ;;
      checkty <- check_type_wf_env Σ (Γ ,,, Δ) _ b ty ;;
      ret _
    end.
    Next Obligation.
      symmetry in Heq_anonymous. sq.
      now apply/PCUICWfUniverses.wf_universe_reflect.
    Qed.
    Next Obligation.
      sq. now eapply PCUICContexts.type_local_ctx_wf_local in checkΔ.
    Qed.
    Next Obligation.
      sq. split; auto.
    Qed.
    Next Obligation.
      sq. now eapply PCUICContexts.type_local_ctx_wf_local in checkΔ.
    Qed.
    Next Obligation.
      destruct Σ as [Σ wfΣ G wfG]; simpl in *.
      sq. split; auto. split; auto.
      eapply PCUICValidity.validity in checkty; auto.
    Qed.
  
  Program Fixpoint infer_sorts_local_ctx (Σ : wf_env_ext) Γ Δ (wfΓ : ∥ wf_local Σ Γ ∥) : 
    typing_result (∑ s, ∥ sorts_local_ctx (lift_typing typing) Σ Γ Δ s ∥) := 
    match Δ with
    | [] => ret ([]; sq tt)
    | {| decl_body := None; decl_type := ty |} :: Δ => 
      '(Δs; Δinfer) <- infer_sorts_local_ctx Σ Γ Δ wfΓ ;;
      '(tys; tyinfer) <- infer_type_wf_env Σ (Γ ,,, Δ) _ ty ;;
      ret ((tys :: Δs); _)
    | {| decl_body := Some b; decl_type := ty |} :: Δ => 
      '(Δs; Δinfer) <- infer_sorts_local_ctx Σ Γ Δ wfΓ ;;
      checkty <- check_type_wf_env Σ (Γ ,,, Δ) _ b ty ;;
      ret (Δs; _)
    end.
    Next Obligation.
      sq. now eapply PCUICContexts.sorts_local_ctx_wf_local in Δinfer.
    Qed.
    Next Obligation.
      destruct Σ as [Σ wfΣ G wfG]; simpl in *.
      sq. split; auto.
    Qed.
    Next Obligation.
      sq. now eapply PCUICContexts.sorts_local_ctx_wf_local in Δinfer.
    Qed.
    Next Obligation.
      destruct Σ as [Σ wfΣ G wfG]; simpl in *.
      sq. split; auto. split; auto.
      eapply PCUICValidity.validity in checkty; auto.
    Qed.

  Definition cumul_decl Σ Γ (d d' : context_decl) : Type := cumul_decls Σ Γ Γ d d'.

  Program Definition wf_env_conv (Σ : wf_env_ext) (le : conv_pb) (Γ : context) (t u : term) :
    welltyped Σ Γ t -> welltyped Σ Γ u -> typing_result (∥ Σ;;; Γ ⊢ t ≤[le] u ∥) :=
    convert (wf_env_ext_wf Σ) Σ (wf_env_ext_graph_wf Σ) le Γ t u.

  Program Definition wf_env_check_cumul_decl (Σ : wf_env_ext) le Γ d d' :=
    check_equality_decl (wf_env_ext_wf Σ) Σ (wf_env_ext_graph_wf Σ) le Γ d d'.

  Program Fixpoint wf_env_check_equality_ctx (le : conv_pb) (Σ : wf_env_ext) Γ Δ Δ' 
    (wfΔ : ∥ wf_local Σ (Γ ,,, Δ) ∥) (wfΔ' : ∥ wf_local Σ (Γ ,,, Δ') ∥) : 
    typing_result (∥ context_equality_rel le Σ Γ Δ Δ' ∥) :=
    check_equality_ctx (wf_env_ext_wf Σ) Σ (wf_env_ext_graph_wf Σ) le Γ Δ Δ' wfΔ wfΔ'.
  
  Program Definition check_eq_term le (Σ : wf_env_ext) t u : typing_result (∥ compare_term le Σ Σ t u ∥) :=
    check <- check_eq_true (if le then leqb_term Σ Σ t u else eqb_term Σ Σ t u) (Msg "Terms are not equal") ;;
    ret _.
    Next Obligation.
      destruct Σ as [Σ wfΣ G wfG]; simpl in *. sq.
      destruct le; simpl.
      - eapply leqb_term_spec in check; sq; auto.
        eapply wfΣ.
      - eapply eqb_term_spec in check; sq; auto.
        apply wfΣ.
    Qed.

  Program Definition check_eq_decl le (Σ : wf_env_ext) d d' : typing_result (∥ eq_decl le Σ Σ d d' ∥) := 
    match d, d' return typing_result _ with
    | {| decl_name := na; decl_body := Some b; decl_type := ty |},
      {| decl_name := na'; decl_body := Some b'; decl_type := ty' |} => 
      eqna <- check_eq_true (eqb_binder_annot na na') (Msg "Binder annotations do not match") ;;
      eqb <- check_eq_term false Σ b b' ;;
      leqty <- check_eq_term le Σ ty ty' ;;
      ret (let 'sq eqb := eqb in 
            let 'sq leqty := leqty in
            sq _)
    | {| decl_name := na; decl_body := None; decl_type := ty |},
      {| decl_name := na'; decl_body := None; decl_type := ty' |} => 
      eqna <- check_eq_true (eqb_binder_annot na na') (Msg "Binder annotations do not match") ;;
      cumt <- check_eq_term le Σ ty ty' ;;
      ret (let 'sq cumt := cumt in sq _)  
    | _, _ => raise (Msg "While checking syntactic cumulativity of contexts: declarations do not match")
    end.
    Next Obligation.
      eapply eqb_binder_annot_spec in eqna.
      constructor; auto. red in leqty.
      destruct le; auto.
    Qed.
    Next Obligation.
      eapply eqb_binder_annot_spec in eqna.
      constructor; auto. red in cumt.
      destruct le; auto.
    Qed.
    
  Program Fixpoint check_leq_context (le : bool) (Σ : wf_env_ext) Γ Δ : typing_result (∥ eq_context le Σ Σ Γ Δ ∥) :=
    match Γ, Δ with
    | [], [] => ret (sq (All2_fold_nil _))
    | decl :: Γ, decl' :: Δ => 
      cctx <- check_leq_context le Σ Γ Δ ;;
      cdecl <- check_eq_decl le Σ decl decl' ;;
      ret _
    | _, _ => raise (Msg "While checking equality of contexts: contexts do not have the same length")
    end.

    Next Obligation.
      sq.
      constructor; auto.
    Qed.
    Next Obligation.
      intuition congruence.
    Qed.
    Next Obligation.
      intuition congruence.
    Qed.

  Program Fixpoint check_leq_terms (le : bool) (Σ : wf_env_ext) l l' : typing_result (∥ All2 (compare_term le Σ Σ) l l' ∥) :=
    match l, l' with
    | [], [] => ret (sq All2_nil)
    | t :: l, t' :: l' => 
      cctx <- check_leq_terms le Σ l l' ;;
      cdecl <- check_eq_term le Σ t t' ;;
      ret _
    | _, _ => raise (Msg "While checking equality of term lists: lists do not have the same length")
    end.

    Next Obligation.
      sq. constructor; auto.
    Qed.
    Next Obligation. intuition congruence. Qed.
    Next Obligation. intuition congruence. Qed.

  Definition wt_terms Σ Γ l := Forall (welltyped Σ Γ) l.
  
  Program Fixpoint check_conv_args (Σ : wf_env_ext) Γ (wfΓ : ∥ wf_local Σ Γ ∥) l l'
    (wfl : wt_terms Σ Γ l) (wfl' : wt_terms Σ Γ l') :
    typing_result (∥ equality_terms Σ Γ l l' ∥) :=
    match l, l' with
    | [], [] => ret (sq All2_nil)
    | t :: l, t' :: l' => 
      checkt <- wf_env_conv Σ Conv Γ t t' _ _ ;;
      checkts <- check_conv_args Σ Γ wfΓ l l' _ _ ;;
      ret _
    | _, _ => raise (Msg "While checking convertibility of arguments: lists have not the same length")
    end.
    Next Obligation.
      now depelim wfl.
    Qed.
    Next Obligation.
      now depelim wfl'.
    Qed.
    Next Obligation.
      now depelim wfl.
    Qed.
    Next Obligation.
      now depelim wfl'.
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
      
  Section MonadMapi.
    Context {T} {M : Monad T} {A B : Type} (f : nat -> A -> T B).
  
    Fixpoint monad_mapi_rec (n : nat) (l : list A) : T (list B) :=
      match l with
      | [] => ret []
      | x :: xs => x' <- f n x ;;
        xs' <- monad_mapi_rec (S n) xs ;;
        ret (x' :: xs')
      end.

    Definition monad_mapi (l : list A) := monad_mapi_rec 0 l.
  End MonadMapi.

  Definition check_constructor_spec (Σ : wf_env_ext) (ind : nat) (mdecl : mutual_inductive_body)
    (cdecl : constructor_body) (cs : constructor_univs) :=
    isType Σ (arities_context mdecl.(ind_bodies)) (cstr_type cdecl) * 
    (cstr_type cdecl = 
      it_mkProd_or_LetIn 
        (mdecl.(ind_params) ,,, cdecl.(cstr_args))
        (mkApps (tRel (#|mdecl.(ind_params) ,,, cdecl.(cstr_args)| + (#|ind_bodies mdecl| - ind)))
          (to_extended_list_k mdecl.(ind_params) #|cdecl.(cstr_args)| ++ 
          cdecl.(cstr_indices)))) * 
    (sorts_local_ctx (lift_typing typing) Σ 
      (arities_context mdecl.(ind_bodies) ,,, ind_params mdecl) cdecl.(cstr_args) 
      cs) * 
    (cstr_arity cdecl = context_assumptions cdecl.(cstr_args)).

  Program Definition isRel_n n (t : term) : typing_result (t = tRel n) :=
    match t with
    | tRel k => match eqb k n with true => ret _ | false => raise (Msg "De-bruijn error") end
    | _ => raise (Msg "isRel_n: not a variable")
    end.
    Next Obligation.
      symmetry in Heq_anonymous.
      change (eqb k n : Prop) in Heq_anonymous. 
      destruct (eqb_spec k n). congruence. discriminate.
    Qed.

  Program Definition decompose_cstr_concl mdecl (k : nat) argctx (t : term) : typing_result 
    (∑ args, t = mkApps (tRel (#|mdecl.(ind_bodies)| - k + #|mdecl.(ind_params) ,,, argctx|)) args) :=
    let '(hd, args) := decompose_app t in
    eqr <- isRel_n (#|mdecl.(ind_bodies)| - k + #|mdecl.(ind_params) ,,, argctx|) hd ;;
    ret (args; _).
    Next Obligation.
      symmetry in Heq_anonymous.
      now apply decompose_app_inv in Heq_anonymous.
    Qed.

  Lemma decompose_prod_n_assum_inv ctx n t ctx' t' : 
    decompose_prod_n_assum ctx n t = Some (ctx', t') ->
    it_mkProd_or_LetIn ctx t = it_mkProd_or_LetIn ctx' t'.
  Proof.
    induction n in t, ctx, ctx', t' |- *; simpl.
    intros [= ->]. subst; auto.
    destruct t => //.
    intros Heq. specialize (IHn _ _ _ _ Heq).
    apply IHn.
    intros Heq. specialize (IHn _ _ _ _ Heq).
    apply IHn.
  Qed.

  Arguments eqb : simpl never.

  Definition wf_ind_types (Σ : global_env_ext) (mdecl : mutual_inductive_body) :=
    All (fun ind => isType Σ [] ind.(ind_type)) mdecl.(ind_bodies).

  Lemma wf_ind_types_wf_arities (Σ : global_env_ext) (wfΣ : wf Σ) mdecl :
    wf_ind_types Σ mdecl -> 
    wf_local Σ (arities_context mdecl.(ind_bodies)).
  Proof.
    rewrite /wf_ind_types.
    unfold arities_context.
    induction 1; simpl; auto.
    rewrite rev_map_cons /=.
    eapply All_local_env_app; split. constructor; pcuic.
    eapply All_local_env_impl; eauto.
    move=> Γ t [] /=.
    * move=> ty ht. eapply weaken_ctx; eauto.
      constructor; pcuic.
    * move=> [s Hs]; exists s.
      eapply weaken_ctx; eauto.
      constructor; pcuic.
  Qed.

  Program Definition check_constructor (Σ : wf_env_ext) (ind : nat) (mdecl : mutual_inductive_body)
    (wfar : ∥ wf_ind_types Σ mdecl ∥)
    (wfpars : ∥ wf_local Σ (ind_params mdecl) ∥)
    (cdecl : constructor_body) : 

    EnvCheck (∑ cs : constructor_univs, ∥ check_constructor_spec Σ ind mdecl cdecl cs ∥) :=

    '(s; Hs) <- wrap_error Σ ("While checking type of constructor: " ^ cdecl.(cstr_name))
      (infer_type_wf_env Σ (arities_context mdecl.(ind_bodies)) _ cdecl.(cstr_type)) ;;
    match decompose_prod_n_assum [] #|mdecl.(ind_params)| cdecl.(cstr_type) with
    | Some (params, concl) => 
      eqpars <- wrap_error Σ cdecl.(cstr_name)
         (check_eq_true (eqb params mdecl.(ind_params)) 
        (Msg "Constructor parameters do not match the parameters of the mutual declaration"));;
      let '(args, concl) := decompose_prod_assum [] concl in
      eqarglen <- wrap_error Σ cdecl.(cstr_name)
        (check_eq_true (eqb (context_assumptions args) cdecl.(cstr_arity))
          (Msg "Constructor arguments do not match the argument number of the declaration"));;
      eqarglen <- wrap_error Σ cdecl.(cstr_name)
        (check_eq_true (eqb args cdecl.(cstr_args))
          (Msg "Constructor arguments do not match the arguments of the declaration"));;
        '(conclargs; Hargs) <- wrap_error Σ cdecl.(cstr_name) 
        (decompose_cstr_concl mdecl ind args concl) ;;
      eqbpars <- wrap_error Σ cdecl.(cstr_name)
        (check_eq_true (eqb (firstn mdecl.(ind_npars) conclargs) (to_extended_list_k mdecl.(ind_params) #|args|))
          (Msg "Parameters in the conclusion of the constructor type do not match the inductive parameters")) ;;
      eqbindices <- wrap_error Σ cdecl.(cstr_name)
        (check_eq_true (eqb (skipn mdecl.(ind_npars) conclargs) cdecl.(cstr_indices))
          (Msg "Indices in the conclusion of the constructor type do not match the indices of the declaration")) ;;
      '(cs; Hcs) <- wrap_error Σ cdecl.(cstr_name) 
        (infer_sorts_local_ctx Σ (arities_context mdecl.(ind_bodies) ,,, mdecl.(ind_params)) args _) ;;
      ret (cs; _)
    | None =>
      raise (Σ.(wf_env_ext_env), IllFormedDecl cdecl.(cstr_name) (Msg "Not enough parameters in constructor type"))
    end.

    Next Obligation.
      destruct Σ as [Σ wfΣ G wfG]; simpl in *.
      sq.
      now apply wf_ind_types_wf_arities in wfar.
    Qed.
    Next Obligation.
      destruct Σ as [Σ wfΣ G wfG]; simpl in *.
      sq.
      apply wf_ind_types_wf_arities in wfar.
      eapply weaken_wf_local; eauto. apply wfΣ.
    Qed.
    Next Obligation.
      destruct Σ as [Σ wfΣ G wfG]; simpl in *.
      sq.
      red ; cbn.
      (* rename Heq_anonymous1 into dt.
      rename Heq_anonymous2 into dc. *)
      symmetry in Heq_anonymous0.
      eapply decompose_prod_n_assum_inv in Heq_anonymous0; simpl in Heq_anonymous0; subst.
      destruct (eqb_spec params (ind_params mdecl)) => //. subst params.
      destruct (eqb_spec args (cstr_args cdecl)) => //. subst args.
      eapply eqb_eq in eqarglen0.
      eapply eqb_eq in eqbindices.
      eapply eqb_eq in eqbpars.
      intuition auto.
      eexists; eauto. 
      symmetry in Heq_anonymous. eapply PCUICSubstitution.decompose_prod_assum_it_mkProd_or_LetIn in Heq_anonymous.
      simpl in Heq_anonymous. subst concl0.
      rewrite it_mkProd_or_LetIn_app.
      rewrite Heq_anonymous0. do 4 f_equal. len.
      rewrite -(firstn_skipn (ind_npars mdecl) x1); congruence.
    Qed.

  Fixpoint All_sigma {A B} {P : A -> B -> Type} {l : list A} (a : All (fun x => ∑ y : B, P x y) l) : 
    ∑ l' : list B, All2 P l l' :=
    match a with
    | All_nil => ([]; All2_nil)
    | All_cons x l px pl =>
      let '(l'; pl') := All_sigma pl in
      ((px.π1 :: l'); All2_cons px.π2 pl')
    end.

  Fixpoint All2_sq {A B} {P : A -> B -> Type} {l : list A} {l' : list B} 
    (a : All2 (fun x y => ∥ P x y ∥) l l') : ∥ All2 P l l' ∥ :=
    match a with
    | All2_nil => sq All2_nil
    | All2_cons _ _ _ _ rxy all' => 
      let 'sq all := All2_sq all' in
      let 'sq rxy := rxy in
      sq (All2_cons rxy all)
    end.

  Program Definition check_constructors_univs
    (Σ : wf_env_ext) (id : ident) (mdecl : mutual_inductive_body)
    (wfar : ∥ wf_ind_types Σ mdecl ∥)
    (wfpars : ∥ wf_local Σ (ind_params mdecl) ∥)
    (ind : nat)
    (cstrs : list constructor_body) : EnvCheck (∑ cs : list constructor_univs, 
      ∥ All2 (fun cstr cs => check_constructor_spec Σ ind mdecl cstr cs) cstrs cs ∥) :=
    css <- monad_All (fun d => check_constructor Σ ind mdecl wfar wfpars d) cstrs ;;
    let '(cs; all2) := All_sigma css in
    ret (cs; All2_sq all2).
    
  Lemma isType_it_mkProd_or_LetIn_inv {Σ : global_env_ext} Γ Δ T :
    wf Σ ->
    isType Σ Γ (it_mkProd_or_LetIn Δ T) ->
    isType Σ (Γ ,,, Δ) T.
  Proof.
    move=> wfΣ [u Hu].
    exists u. unfold PCUICTypingDef.typing in *.
    now eapply PCUICSpine.inversion_it_mkProd_or_LetIn in Hu.
  Qed.

  Lemma isType_mkApps_inv {Σ : global_env_ext} (wfΣ : wf Σ) Γ f args :
    isType Σ Γ (mkApps f args) ->
    ∑ fty s, (Σ ;;; Γ |- f : fty) * 
      typing_spine Σ Γ fty args (tSort s).
  Proof.
    intros [s Hs].
    eapply inversion_mkApps in Hs as [fty [Hf Hargs]]; auto.
    now exists fty, s.
  Qed.

  Lemma nth_error_arities_context mdecl i idecl : 
    nth_error (List.rev mdecl.(ind_bodies)) i = Some idecl ->
    nth_error (arities_context mdecl.(ind_bodies)) i = 
      Some {| decl_name := {| binder_name := nNamed idecl.(ind_name); binder_relevance := idecl.(ind_relevance) |};
              decl_body := None;
              decl_type := idecl.(ind_type) |}.
  Proof.
    generalize mdecl.(ind_bodies) => l.
    intros hnth.
    epose proof (nth_error_Some_length hnth). autorewrite with len in H.
    rewrite nth_error_rev in hnth. now autorewrite with len.
    rewrite List.rev_involutive in hnth. autorewrite with len in hnth.
    unfold arities_context.
    rewrite rev_map_spec.
    rewrite nth_error_rev; autorewrite with len; auto.
    rewrite List.rev_involutive nth_error_map.
    rewrite hnth. simpl. reflexivity.
  Qed.

  Definition smash_telescope acc Γ := 
    List.rev (smash_context acc (List.rev Γ)).

  Lemma ctx_inst_smash {Σ : global_env_ext} (wfΣ : wf Σ) (Γ Δ : context) args :
    ctx_inst Σ Γ args (smash_telescope [] Δ) ->
    ctx_inst Σ Γ args Δ.
  Proof.
    rewrite /smash_telescope.
    intros H. apply ctx_inst_smash in H. now rewrite List.rev_involutive in H.
  Qed.

  Lemma typing_spine_it_mkProd_or_LetIn_inv {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Δ s args s'} :
    wf_local Σ (Γ ,,, Δ) ->
    typing_spine Σ Γ (it_mkProd_or_LetIn Δ (tSort s)) args (tSort s') ->
    ctx_inst Σ Γ args (List.rev Δ).
  Proof.
    intros wf sp.
    pose proof (wf_local_smash_end _ _ wf). clear wf.
    eapply PCUICCanonicity.typing_spine_smash in sp; auto.
    unfold expand_lets, expand_lets_k in sp. simpl in sp.
    apply ctx_inst_smash; auto.
    rewrite /smash_telescope List.rev_involutive.
    revert X sp.
    move: (@smash_context_assumption_context [] Δ assumption_context_nil).
    move: (smash_context [] Δ) => {}Δ.
    induction Δ using PCUICInduction.ctx_length_rev_ind in s, s', args |- *; simpl;
      rewrite ?it_mkProd_or_LetIn_app;
    intros ass wf sp; depelim sp; try constructor.
    * now eapply equality_Sort_Prod_inv in e.
    * apply assumption_context_app in ass as [ass assd].  
      destruct d as [na [b|] ty]; unfold mkProd_or_LetIn in e; simpl in *.
      elimtype False; depelim assd.
      eapply equality_Prod_Sort_inv in e; auto.
    * apply assumption_context_app in ass as [ass assd].  
      destruct d as [na' [b'|] ty']; unfold mkProd_or_LetIn in e; simpl in *.
      elimtype False; depelim assd.
      eapply equality_Prod_Prod_inv in e as [eqann eqdom codom]; auto.
      rewrite List.rev_app_distr.
      constructor.
      eapply All_local_env_app_inv in wf as [wfΓ wfr].
      eapply All_local_env_app_inv in wfr as [wfd wfΓ0].
      depelim wfd. destruct l as [? Hs].
      eapply type_equality; pcuic. eapply equality_eq_le. now symmetry.
      rewrite subst_telescope_subst_context. cbn in *.
      have tyhd : Σ ;;; Γ |- hd : ty'.
      { eapply type_equality; tea.  eapply isType_tProd in i as [].
        pcuic. eapply equality_eq_le. now symmetry. }
      eapply X. now len.
      pcuic.
      eapply substitution_wf_local; eauto. eapply subslet_ass_tip; tea. 
      rewrite app_context_assoc in wf; eapply wf.
      eapply typing_spine_strengthen; eauto.
      eapply isType_apply in i; tea.
      now rewrite /subst1 subst_it_mkProd_or_LetIn in i.
      eapply substitution0_equality in codom; eauto.
      now rewrite /subst1 subst_it_mkProd_or_LetIn in codom.
  Qed.
  
  Lemma lift_LetIn na b ty T n k : 
    lift n k (tLetIn na b ty T) = 
    tLetIn na (lift n k b) (lift n k ty) (lift n (S k) T).
  Proof. reflexivity. Qed.

  Lemma typing_spine_letin_inv' {Σ : global_env_ext} {wfΣ : wf Σ} {Γ na b ty Δ T args T'} :
    let decl := {| decl_name := na; decl_body := Some b; decl_type := ty |} in
    isType Σ (Γ ,, decl) T ->
    typing_spine Σ (Γ ,, decl ,,, Δ) (mkProd_or_LetIn (lift_decl (#|Δ| + 1) 0 decl) (lift (#|Δ| + 1) 1 T)) args T' ->
    typing_spine Σ (Γ ,, decl ,,, Δ) (lift #|Δ| 0 T) args T'.
  Proof.
    intros decl  isty.
    cbn. intros sp.
    pose proof (typing_spine_isType_dom sp) as isty'.
    eapply typing_spine_strengthen; eauto.
    eapply isType_lift; auto. len.  pcuic.
    now rewrite skipn_all_app.
    eapply equality_eq_le.
    etransitivity.
    2:{ symmetry; eapply red_conv. repeat constructor.
        * now eapply isType_wf_local, wf_local_closed_context in isty'.
        * now eapply isType_is_open_term in isty'. }
    epose proof (distr_lift_subst _ [b] (#|Δ|+1) 0). cbn in H.
    rewrite /subst1. erewrite <- H.
    etransitivity.
    symmetry.
    epose proof (red_expand_let (isType_wf_local isty)).
    epose proof (weakening_equality (le:=false) (Γ := Γ ,, decl) (Γ' := []) (Γ'' := Δ)).
    simpl in X0.
    eapply X0.
    symmetry. eapply red_conv. apply X. fvs. eapply isType_wf_local, wf_local_closed_context in isty'. fvs.
    rewrite simpl_lift. lia. lia.
    eapply equality_refl. eapply isType_wf_local in isty'. fvs.
    apply on_free_vars_lift0. rewrite /app_context /snoc; len.
    replace (#|Δ| + S #|Γ|) with (S #|Δ| + #|Γ|). 2:lia. rewrite Nat.add_1_r.
    rewrite -shiftnP_add addnP_shiftnP. eapply on_free_vars_subst.
    eapply isType_wf_local in isty. depelim isty. red in l0. cbn.
    rewrite andb_true_r. fvs.
    eapply isType_is_open_term in isty. cbn. now rewrite shiftnP_add.
  Qed.

  Lemma typing_spine_prod_inv {Σ : global_env_ext} {wfΣ : wf Σ} {Γ na ty Δ T args T'} :
    let decl := {| decl_name := na; decl_body := None; decl_type := ty |} in
    isType Σ (Γ ,, decl) T ->
    typing_spine Σ (Γ ,, decl ,,, Δ) (mkProd_or_LetIn (lift_decl (#|Δ| + 1) 0 decl) (lift (#|Δ| + 1) 1 T)) 
      (tRel #|Δ| :: args) T' ->
    typing_spine Σ (Γ ,, decl ,,, Δ) (lift #|Δ| 0 T) args T'.
  Proof.
    intros decl wf.
    cbn. intros sp.
    depelim sp.
    have istyl : isType Σ (Γ,, decl,,, Δ) (lift0 #|Δ| T).
    { eapply isType_lift; tea. len. pcuic. now rewrite skipn_all_app. }
    eapply typing_spine_strengthen; eauto.
    eapply equality_Prod_Prod_inv in e as [eqann eqdom eqcodom]; auto.
    eapply (substitution0_equality (t:=tRel #|Δ|)) in eqcodom; auto.
    etransitivity; eauto.
    rewrite /subst1.
    replace ([tRel #|Δ|]) with (map (lift #|Δ| 0) [tRel 0]). 2:simpl; lia_f_equal.
    rewrite -(simpl_lift T _ _ _ 1); try lia.
    change 1 with (0 + #|[tRel 0]| + 0) at 1.
    rewrite -distr_lift_subst_rec /= //.
    rewrite subst_rel0_lift_id.
    now eapply equality_eq_le, isType_equality_refl.
  Qed.
  
  (** Non-trivial lemma: 
    this shows that instantiating a product/let-in type with the identity substitution on some 
    sub-context of the current context is the same as typechecking the remainder of the 
    type approapriately lifted to directly refer to the variables in the subcontext. 
    This is a quite common operation in tactics. Making this work up-to unfolding of
    let-ins is the tricky part.
  *)
  Lemma typing_spine_it_mkProd_or_LetIn_ext_list_inv_gen {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Δ Δ' Δ'' s args s'} :
    wf_local Σ (Γ ,,, Δ ,,, Δ'') ->
    typing_spine Σ (Γ ,,, Δ ,,, Δ') (it_mkProd_or_LetIn (lift_context #|Δ ,,, Δ'| 0 (Δ ,,, Δ'')) (tSort s)) 
      (to_extended_list_k Δ #|Δ'| ++ args) (tSort s') ->
    typing_spine Σ (Γ ,,, Δ ,,, Δ') (it_mkProd_or_LetIn (lift_context #|Δ'| 0 Δ'') (tSort s)) 
      args (tSort s').
  Proof.
    induction Δ using PCUICInduction.ctx_length_rev_ind in Γ, s, s', args, Δ' |- *; simpl;
      rewrite ?it_mkProd_or_LetIn_app;
    intros wf sp.
    * len in sp.
      now rewrite app_context_nil_l in sp.
    * set (decl := d) in *.
      assert (wf_universe Σ s).
      { eapply typing_spine_isType_dom in sp.
        eapply isType_it_mkProd_or_LetIn_inv in sp; auto.
        destruct sp as [? Hs]. now eapply inversion_Sort in Hs as [? []]. }
      destruct d as [na [b|] ty]. simpl in sp; unfold mkProd_or_LetIn in sp; simpl in *.
      - len in sp.
        rewrite lift_context_app /= it_mkProd_or_LetIn_app lift_context_app it_mkProd_or_LetIn_app /= 
          -it_mkProd_or_LetIn_app in sp.
        replace (Γ,,, (Γ0 ++ [decl]),,, Δ') with (Γ,, decl,,, (Γ0,,, Δ')) in sp.
        2:rewrite !app_context_assoc //.
        epose proof (typing_spine_letin_inv' (Γ := Γ) (na:=na) (b:=b) (ty:=ty) (Δ := Γ0 ,,, Δ')).
        fold decl in X0.
        rewrite /lift_decl in X0. len in X0.
        rewrite Nat.add_assoc in sp.
        len in sp.
        rewrite -[_ ++ _](lift_context_app (#|Δ'| + #|Γ0| + 1) 1 Γ0 Δ'') in sp.
        rewrite -(lift_it_mkProd_or_LetIn _ _ _ (tSort _)) in sp.
        eapply X0 in sp. clear X0.
        rewrite lift_it_mkProd_or_LetIn in sp.
        rewrite app_context_assoc.
        rewrite to_extended_list_k_app in sp. simpl in sp.
        specialize (X Γ0 ltac:(now len) (Γ ,, decl) Δ' s args s').
        simpl in X.
        rewrite app_context_assoc in wf. specialize (X wf).
        forward X. rewrite app_context_assoc in sp. len.
        exact X.
        eapply isType_it_mkProd_or_LetIn; tea.
        eapply isType_Sort => //.
        now rewrite !app_context_assoc in wf *.
      - len in sp.
        rewrite lift_context_app /= it_mkProd_or_LetIn_app lift_context_app it_mkProd_or_LetIn_app /= 
          -it_mkProd_or_LetIn_app in sp.
        replace (Γ,,, (Γ0 ++ [decl]),,, Δ') with (Γ,, decl,,, (Γ0,,, Δ')) in sp.
        2:rewrite !app_context_assoc //.
        rewrite to_extended_list_k_app in sp. simpl in sp.
        epose proof (typing_spine_prod_inv (na := na) (ty := ty) (Δ := Γ0 ,,, Δ')).
        fold decl in X0.
        rewrite /lift_decl in X0. len in X0.
        rewrite Nat.add_assoc in sp.
        len in sp.
        rewrite -[_ ++ _](lift_context_app (#|Δ'| + #|Γ0| + 1) 1 Γ0 Δ'') in sp.
        rewrite -(lift_it_mkProd_or_LetIn _ _ _ (tSort _)) in sp.
        rewrite {3}(Nat.add_comm #|Δ'| #|Γ0|) in X0.
        eapply X0 in sp. clear X0.
        rewrite lift_it_mkProd_or_LetIn in sp.
        rewrite app_context_assoc.
        specialize (X Γ0 ltac:(now len) (Γ ,, decl) Δ' s args s').
        simpl in X.
        rewrite app_context_assoc in wf. specialize (X wf).
        len in X. rewrite app_context_assoc in sp.
        now specialize (X sp).
        rewrite app_context_assoc in wf.
        eapply isType_it_mkProd_or_LetIn; auto.
        eapply isType_Sort; eauto. now rewrite app_context_assoc.
  Qed.

  Lemma typing_spine_it_mkProd_or_LetIn_ext_list_inv {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Δ Δ' Δ'' s args s'} :
    wf_local Σ (Γ ,,, Δ ,,, Δ'') ->
    closedn_ctx 0 (Δ ,,, Δ'') ->
    typing_spine Σ (Γ ,,, Δ ,,, Δ') (it_mkProd_or_LetIn (Δ ,,, Δ'') (tSort s)) 
      (to_extended_list_k Δ #|Δ'| ++ args) (tSort s') ->
    typing_spine Σ (Γ ,,, Δ ,,, Δ') (it_mkProd_or_LetIn (lift_context #|Δ'| 0 Δ'') (tSort s)) 
      args (tSort s').
  Proof.
    intros.
    eapply typing_spine_it_mkProd_or_LetIn_ext_list_inv_gen; eauto.
    rewrite closed_ctx_lift //.
  Qed.

  Lemma firstn_all_app_eq {A : Type} (n : nat) (l l' : list A) :
    n = #|l| -> firstn n (l ++ l') = l.
  Proof.
    intros ->.
    now rewrite -(Nat.add_0_r #|l|) firstn_app_2 firstn_0 // app_nil_r.
  Qed.

  Notation "'if' c 'then' vT 'else' vF" := 
    (match c with true => vT | false => vF end) 
    (at level 200, c, vT, vF at level 200, only parsing).

  Equations discr_prod_letin (t : term) : Prop :=
    discr_prod_letin (tProd _ _ _) := False ;
    discr_prod_letin (tLetIn _ _ _ _) := False ;
    discr_prod_letin _ := True.

  Variant prod_letin_view : term -> Type :=
  | prod_letin_tProd : forall na dom codom, prod_letin_view (tProd na dom codom)
  | prod_letin_tLetIn : forall na b ty t, prod_letin_view (tLetIn na b ty t) 
  | prod_letin_other : forall t, discr_prod_letin t -> prod_letin_view t.

  Equations prod_letin_viewc t : prod_letin_view t :=
    prod_letin_viewc (tProd na ty t) := prod_letin_tProd na ty t ;
    prod_letin_viewc (tLetIn na b ty t) := prod_letin_tLetIn na b ty t ;
    prod_letin_viewc t := prod_letin_other t I.

  Lemma welltyped_prod_inv {Σ : global_env_ext} {Γ na ty ty'} {wfΣ : wf Σ} :
    welltyped Σ Γ (tProd na ty ty') ->
    welltyped Σ Γ ty * welltyped Σ (Γ ,, vass na ty) ty'.
  Proof.
    intros [s [s1 [s2 [hty [hty' hcum]]]]%inversion_Prod]; auto.
    split; eexists; eauto.
  Qed.
  
  Lemma welltyped_letin_inv {Σ : global_env_ext} {Γ na b ty t} {wfΣ : wf Σ} :
    welltyped Σ Γ (tLetIn na b ty t) ->
    welltyped Σ Γ ty * 
    welltyped Σ Γ b * 
    welltyped Σ (Γ ,, vdef na b ty) t.
  Proof.
    intros [s [s1 [s2 [hty [hdef [hty' hcum]]]]]%inversion_LetIn]; auto.
    split; [split|]; eexists; eauto.
  Qed.
  
  Lemma welltyped_letin_red {Σ : global_env_ext} {Γ na b ty t} {wfΣ : wf Σ} :
    welltyped Σ Γ (tLetIn na b ty t) ->
    welltyped Σ Γ (subst0 [b] t).
  Proof.
    intros [s [s1 [s2 [hty [hdef [hty' hcum]]]]]%inversion_LetIn]; auto.
    exists (subst0 [b] s2).
    now eapply substitution_let in hty'.
  Qed.

  Section PositivityCheck.
    Context {Σ : global_env_ext}.
    Context {wfΣ : ∥ wf_ext Σ ∥}.

    Obligation Tactic := Program.Tactics.program_simpl.

    Program Definition isRel (t : term) : typing_result (∑ n, t = tRel n) :=
      match t with
      | tRel k => ret (k; _)
      | _ => raise (Msg "isRel: not a variable")
      end.

    (** Positivity checking involves reducing let-ins, so it can only be applied to 
        already well-typed terms to ensure termination.

        We could also intersperse weak-head normalizations to reduce the types.
        This would need to be done in sync with a change in the spec in EnvironmentTyping though. *)

    Program Fixpoint check_positive_cstr_arg mdecl Γ t (wt : welltyped Σ Γ t) Δ
      {measure (Γ; t; wt) (@redp_subterm_rel cf Σ)} : typing_result (∥ positive_cstr_arg mdecl Δ t ∥) :=
      if closedn #|Δ| t then ret _ 
      else 
      match prod_letin_viewc t in prod_letin_view t' return t' = t -> _ with
      | prod_letin_tProd na ty t => fun eq =>
        posarg <- check_eq_true (closedn #|Δ| ty) (Msg "Non-positive occurrence.");;
        post <- check_positive_cstr_arg mdecl (vass na ty :: Γ) t _ (vass na ty :: Δ) ;;
        ret _
      | prod_letin_tLetIn na b ty t => fun eq =>
        post <- check_positive_cstr_arg mdecl Γ (subst0 [b] t) _ Δ ;;
        ret _
      | prod_letin_other t nprodlet => fun eq =>
        let '(hd, args) := decompose_app t in
        '(hdrel; eqr) <- isRel hd ;;
        isind <- check_eq_true ((#|Δ| <=? hdrel) && (hdrel <? #|Δ| + #|ind_bodies mdecl|)) (Msg "Conclusion is not an inductive type") ;;
        (** Actually this is the only necessary check *)
        check_closed <- check_eq_true (forallb (closedn #|Δ|) args) (Msg "Conclusion arguments refer to the inductive type being defined") ;;
        match nth_error (List.rev mdecl.(ind_bodies)) (hdrel - #|Δ|) with
        | Some i => 
          check_eq_true (eqb (ind_realargs i) #|args|) (Msg "Partial application of inductive") ;;
          ret _
        | None => False_rect _ _
        end
      end eq_refl.

      Next Obligation. sq.
        now constructor; rewrite -Heq_anonymous.
      Qed.

      Next Obligation. 
        sq.
        clear check_positive_cstr_arg.
        apply (welltyped_prod_inv wt).
      Qed.
      
      Next Obligation.
        sq. right.
        unshelve eexists. repeat constructor. now reflexivity.
      Qed.

      Next Obligation.
        sq. constructor 4.
        now rewrite posarg.
        apply post.
      Qed.
      
      Next Obligation.
        sq.
        eapply (welltyped_letin_red wt).
      Qed.

      Next Obligation.
        sq; left. split; auto. repeat constructor.
      Qed.
      
      Next Obligation. sq.
        now constructor 3.
      Qed.

      Next Obligation.
        clear eqr.
        move/andP: isind => [/Nat.leb_le le /Nat.ltb_lt lt].
        eapply forallb_All in check_closed. sq.
        symmetry in Heq_anonymous1; eapply decompose_app_inv in Heq_anonymous1.
        subst t0. econstructor 2; eauto.
        now eapply eqb_eq in H.
      Qed.
      
      Next Obligation.
        clear eqr.
        move/andP: isind => [/Nat.leb_le le /Nat.ltb_lt lt].
        eapply forallb_All in check_closed. sq.
        symmetry in Heq_anonymous1; eapply decompose_app_inv in Heq_anonymous1.
        subst t0. symmetry in Heq_anonymous.
        eapply nth_error_None in Heq_anonymous.
        len in Heq_anonymous. lia.
      Qed.

      Next Obligation.
        eapply Wf.measure_wf.
        unshelve eapply wf_redp_subterm_rel; eauto.
      Defined.

    (** We already assume that constructor types are of the form `it_mkProd_or_LetIn (params,,, args) concl` so
        we don't need to reduce further. *)
    Program Fixpoint check_positive_cstr mdecl n Γ t (wt : welltyped Σ Γ t) Δ
      { measure (Γ; t; wt) (@redp_subterm_rel cf Σ) }
      : typing_result (∥ positive_cstr mdecl n Δ t ∥) :=
      match prod_letin_viewc t in prod_letin_view t' return t' = t -> typing_result (∥ positive_cstr mdecl n Δ t ∥) with 
      | prod_letin_tProd na ty t => fun eq =>
        posarg <- check_positive_cstr_arg mdecl Γ ty _ Δ ;;
        post <- check_positive_cstr mdecl n (vass na ty :: Γ) t _ (vass na ty :: Δ) ;;
        ret _
      | prod_letin_tLetIn na b ty t => fun eq =>
        (* Do reduction *)
        post <- check_positive_cstr mdecl n Γ (subst0 [b] t) _ Δ ;;
        ret _
      | prod_letin_other t Ht => fun eq =>
        let '(hd, indices) := decompose_app t in
        eqhd <- check_eq_true (eqb hd (tRel (#|ind_bodies mdecl| - S n + #|Δ|)))
          (Msg "Conclusion of constructor is not the right inductive type") ;;
          (* actually impossible with prior typing checks. *)
        closedargs <- check_eq_true (forallb (closedn #|Δ|) indices)
          (Msg "Arguments of the inductive in the conclusion of a constructor mention the inductive itself");;
        ret _
      end eq_refl.
  
      Next Obligation.
        sq. eapply (welltyped_prod_inv wt).
      Qed.
      Next Obligation.
        sq. eapply (welltyped_prod_inv wt).
      Qed.
      Next Obligation.
        sq. right. unshelve eexists. repeat constructor. reflexivity.
      Qed.
      Next Obligation.
        sq. constructor 3; eauto.
      Qed.
      Next Obligation.
        sq. eapply (welltyped_letin_red wt).
      Qed.
      Next Obligation.
        sq. left. repeat constructor.
      Qed.
      Next Obligation.
        sq. now constructor 2.
      Qed.
      Next Obligation.
        sq. rename Heq_anonymous into eqa.
        symmetry in eqa; eapply decompose_app_inv in eqa.
        subst t0.
        move: eqhd; case: eqb_spec => // -> _.
        constructor.
        now eapply forallb_All in closedargs.
      Qed.
      Next Obligation.
        eapply Wf.measure_wf.
        unshelve eapply wf_redp_subterm_rel; eauto.
      Qed.
  End PositivityCheck.

  Program Fixpoint check_wf_local (Σ : wf_env_ext) Γ : typing_result (∥ wf_local Σ Γ ∥) :=
    match Γ with
    | [] => ret (sq localenv_nil)
    | {| decl_body := Some b; decl_type := ty |} :: Γ => 
      wfΓ <- check_wf_local Σ Γ ;;
      wfty <- check_type_wf_env Σ Γ wfΓ b ty ;;
      ret _
    | {| decl_body := None; decl_type := ty |} :: Γ =>
      wfΓ <- check_wf_local Σ Γ ;;
      wfty <- infer_type_wf_env Σ Γ wfΓ ty ;;
      ret _
    end.
    Next Obligation.
      destruct Σ as [Σ wfΣ G' wfG']; simpl in *.
      sq. constructor; auto.
      eapply validity in wfty. apply wfty. 
    Qed.
    Next Obligation.
      destruct Σ as [Σ wfΣ G' wfG']; simpl in *.
      sq. constructor; auto. now exists wfty.
    Qed.

  Definition wt_indices Σ mdecl indices cs :=
    wf_local Σ (ind_arities mdecl,,, ind_params mdecl,,, cs.(cstr_args)) *
    ctx_inst Σ (ind_arities mdecl,,, ind_params mdecl,,, cs.(cstr_args)) 
      (cs.(cstr_indices)) (List.rev (lift_context #|cs.(cstr_args)| 0 indices)).

  Lemma ctx_inst_wt Σ Γ s Δ : 
    ctx_inst Σ Γ s Δ ->
    Forall (welltyped Σ Γ) s.
  Proof.
    induction 1; try constructor; auto.
    now exists t.
  Qed.

  (* Now in PCUIC *)
  Lemma type_smash {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Δ t T} : 
    Σ ;;; Γ ,,, Δ |- t : T ->
    Σ ;;; Γ ,,, smash_context [] Δ |- expand_lets Δ t : expand_lets Δ T.
  Proof.
    revert Γ t T.
    induction Δ as [|[na [b|] ty] Δ] using PCUICInduction.ctx_length_rev_ind; simpl; auto.
    - intros. now rewrite! expand_lets_nil.
    - intros Γ t T h.
      rewrite !smash_context_app_def !expand_lets_vdef.
      eapply X. now len.
      eapply PCUICSubstitution.substitution; eauto.
      2:{ now rewrite app_context_assoc in h. }
      rewrite -{1}(subst_empty 0 b). repeat constructor.
      rewrite !subst_empty.
      eapply typing_wf_local in h.
      rewrite app_context_assoc in h. eapply All_local_env_app_inv in h as [h _].
      now depelim h.
    - intros Γ t T h.
      rewrite !smash_context_app_ass !expand_lets_vass.
      rewrite app_context_assoc. eapply X. lia.
      now rewrite app_context_assoc in h.
  Qed.

  Lemma sub_context_set_empty Σ : sub_context_set ContextSet.empty (global_context_set Σ).
  Proof.
    split; simpl.
    intros x hin. now eapply LS.empty_spec in hin.
    intros x hin. now eapply CS.empty_spec in hin.
  Qed.

  Lemma cumul_ctx_rel_close' Σ Γ Δ Δ' : 
    PCUICCumulativitySpec.cumul_context Σ (Γ ,,, Δ) (Γ ,,, Δ') ->
    PCUICConversionSpec.cumul_ctx_rel Σ Γ Δ Δ'.
  Proof.
    intros H.
    eapply All2_fold_app_inv in H as [cumΓ cumΔs]; auto.
    eapply All2_fold_length in H. len in H. lia.
  Qed.

  Lemma eq_decl_eq_decl_upto (Σ : global_env_ext) x y : 
    eq_decl true Σ Σ x y ->
    eq_decl_upto_gen Σ (eq_universe Σ) (leq_universe Σ) x y.
  Proof.
    intros []; constructor; intuition auto. cbn. constructor.
    cbn. constructor; auto.
  Qed.

  Lemma eq_decl_upto_refl (Σ : global_env_ext) x : eq_decl_upto_gen Σ (eq_universe Σ) (leq_universe Σ) x x.
  Proof.
    destruct x as [na [b|] ty]; constructor; simpl; auto.
    split; constructor; reflexivity. reflexivity.
    split; constructor; reflexivity. reflexivity.
  Qed.
    

  Lemma eq_context_upto_cumul_context (Σ : global_env_ext) Re Rle :
    RelationClasses.subrelation Re (eq_universe Σ) ->
    RelationClasses.subrelation Rle (leq_universe Σ) ->
    RelationClasses.subrelation Re Rle ->
    CRelationClasses.subrelation (eq_context_upto Σ Re Rle) (fun Γ Γ' => PCUICCumulativitySpec.cumul_context Σ Γ Γ').
  Proof.
    intros HRe HRle hR Γ Δ h. induction h.
    - constructor.
    - constructor; tas.
      depelim p; constructor; auto.
      eapply eq_term_upto_univ_cumulSpec.
      eapply eq_term_upto_univ_impl. 5:eauto. all:tea. 
      now transitivity Rle. auto.
      eapply eq_term_upto_univ_cumulSpec.
      eapply eq_term_upto_univ_impl; eauto.
      eapply eq_term_upto_univ_cumulSpec.
      eapply eq_term_upto_univ_impl. 5:eauto. all:tea. 
      now transitivity Rle. auto.
  Qed.

  Lemma eq_context_upto_univ_cumul_context {Σ : global_env_ext} Γ Δ :
      eq_context_upto Σ.1 (eq_universe Σ) (leq_universe Σ) Γ Δ ->
      PCUICCumulativitySpec.cumul_context Σ Γ Δ.
  Proof.
    intros h. eapply eq_context_upto_cumul_context; tea.
    reflexivity. tc. tc.
  Qed.
  Lemma leq_context_cumul_context (Σ : global_env_ext) Γ Δ Δ' : 
    eq_context true Σ Σ Δ Δ' ->
    PCUICConversionSpec.cumul_ctx_rel Σ Γ Δ Δ'.
  Proof.
    intros eqc.
    apply cumul_ctx_rel_close'.
    apply eq_context_upto_univ_cumul_context.
    apply All2_eq_context_upto.
    eapply All2_app. red in eqc.
    eapply All2_fold_All2; eauto.
    eapply All2_fold_impl; eauto.
    intros; now eapply eq_decl_eq_decl_upto.
    eapply All2_refl. intros. simpl. eapply (eq_decl_upto_refl Σ).
  Qed.

  Lemma wt_cstrs {Σ : wf_env_ext} {n mdecl cstrs cs} :
    ∥ All2
      (fun (cstr : constructor_body) (cs0 : constructor_univs) =>
      check_constructor_spec Σ n mdecl cstr cs0) cstrs cs ∥ -> 
    ∥ All (fun cstr => welltyped Σ (arities_context mdecl.(ind_bodies)) (cstr_type cstr)) cstrs ∥.
  Proof.
    intros; sq.
    solve_all. simpl.
    destruct X as [[[isTy _] _] _]. simpl in isTy.
    now eapply isType_welltyped in isTy.
  Qed.
  
  Lemma get_wt_indices {Σ : wf_env_ext} {mdecl cstrs cs}
    (wfar : ∥ wf_ind_types Σ mdecl ∥)
    (wfpars : ∥ wf_local Σ (ind_params mdecl) ∥)
    (n : nat) (idecl : one_inductive_body) (indices : context)
    (hnth : nth_error mdecl.(ind_bodies) n = Some idecl)    
    (heq : ∥ ∑ inds, idecl.(ind_type) = it_mkProd_or_LetIn (mdecl.(ind_params) ,,, indices) (tSort inds) ∥) :
    ∥ All2
      (fun (cstr :constructor_body) (cs0 : constructor_univs) =>
      check_constructor_spec Σ (S n) mdecl cstr cs0) cstrs cs ∥ -> 
    ∥ All (fun cs => wt_indices Σ mdecl indices cs) cstrs ∥.
  Proof.
    destruct Σ as [Σ wfΣ G wfG]; simpl in *. destruct wfΣ.
    intros; sq.
    solve_all. simpl.
    destruct X as [[[isTy eq] sorts] eq']. simpl in *.
    assert(wf_local Σ (ind_params mdecl,,, indices)).
    { eapply nth_error_all in wfar; eauto. simpl in wfar.
      destruct heq as [s Hs]. rewrite Hs in wfar.
      eapply isType_it_mkProd_or_LetIn_wf_local in wfar.
      now rewrite app_context_nil_l in wfar. }
    red. rewrite eq in isTy.
    eapply isType_it_mkProd_or_LetIn_inv in isTy; auto.
    eapply isType_mkApps_inv in isTy as [fty [s [Hf Hsp]]]; auto.
    eapply inversion_Rel in Hf as [decl [wfctx [Hnth cum]]]; auto.
    rewrite nth_error_app_ge in Hnth. lia.
    split. now rewrite app_context_assoc in wfctx.
    replace (#|ind_params mdecl,,, cstr_args x| + (#|ind_bodies mdecl| - S n) -
    #|ind_params mdecl,,, cstr_args x|) with (#|ind_bodies mdecl| - S n) in Hnth by lia.
    pose proof (nth_error_Some_length hnth).
    rewrite nth_error_rev in hnth => //.
    assert (H0 := nth_error_arities_context _ _ _ hnth).
    rewrite Hnth in H0.
    noconf H0; simpl in *.
    eapply PCUICSpine.typing_spine_strengthen in Hsp; eauto.
    clear cum.
    destruct heq as [inds eqind].
    move: Hsp. rewrite eqind.
    rewrite lift_it_mkProd_or_LetIn /= => Hs.
    rewrite closed_ctx_lift in Hs. eapply closed_wf_local; eauto.
    rewrite app_context_assoc in Hs wfctx.
    eapply typing_spine_it_mkProd_or_LetIn_ext_list_inv in Hs; auto.
    2:{ rewrite -app_context_assoc. eapply weaken_wf_local; auto.
        now eapply wf_ind_types_wf_arities. }
    2:{ eapply closed_wf_local; eauto. }
    eapply typing_spine_it_mkProd_or_LetIn_inv in Hs => //. auto.
    eapply weakening_wf_local; eauto.
    rewrite -app_context_assoc.
    eapply weaken_wf_local; eauto.
    now eapply wf_ind_types_wf_arities.
    len.
    rewrite nth_error_rev in hnth. len.
    rewrite List.rev_involutive in hnth. len in hnth.
    eapply nth_error_all in wfar; tea. cbn in wfar.
    rewrite lift_closed; [now eapply isType_closed in wfar|].
    now eapply isType_weaken.
  Qed.

  Equations? check_variance {Σ : wf_env} (id : kername) univs (variances : option (list Variance.t))
    (wfunivs : ∥ wf_ext (Σ, univs) ∥) : 
    EnvCheck (∥ on_variance Σ univs variances ∥) :=
    | id, univs, None, wfunivs := ret _
    | id, univs, Some v, wfunivs with inspect (variance_universes univs v) := {
      | exist (Some (univs', i, i')) eqvu =>
        check_leq <- 
          check_eq_true (eqb #|v| #|polymorphic_instance univs|)
            (empty_ext Σ, IllFormedDecl (string_of_kername id) (Msg "Variance annotation does not have the right length"));;
        Σ' <- make_wf_env_ext Σ id univs' ;;
        ret _
      | exist None eqvu => raise (empty_ext Σ, IllFormedDecl (string_of_kername id) (Msg "Ill-formed variance annotation")) }.
  Proof.
    - destruct Σ as [Σ [wfΣ] ΣG wfΣG], Σ' as [Σ' [wfΣ'] Σ'G wfΣ'G]. cbn in *; sq.
      destruct univs => //.
      symmetry in eqvu.
      have wfext : wf_ext (Σ, univs').
      { now subst. }
      destruct (variance_universes_spec _ _ _ _ _ _ _ _ eqvu).
      exists univs', i, i'; split => //.
      now eapply eqb_eq in check_leq.
    - sq. red. destruct univs; auto. exact tt.
  Qed.
    
  Definition Build_on_inductive_sq {Σ ind mdecl}
    : ∥ Alli (on_ind_body (lift_typing typing) Σ ind mdecl) 0 (ind_bodies mdecl) ∥ ->
      ∥ wf_local Σ (ind_params mdecl) ∥ ->
      context_assumptions (ind_params mdecl) = ind_npars mdecl ->
      ∥ on_variance Σ (ind_universes mdecl) (ind_variance mdecl) ∥ -> 
      ∥ on_inductive (lift_typing typing) Σ ind mdecl ∥.
  Proof.
    intros H H0 H1 H2. sq. econstructor; try eassumption.
  Defined.

  Program Definition check_cstr_variance (Σ : wf_env) mdecl (id : kername) indices
    (mdeclvar : ∥ on_variance Σ mdecl.(ind_universes) mdecl.(ind_variance) ∥) cs 
    (wfΣ : ∥ wf_ext (Σ, ind_universes mdecl) ∥)
    (wfΓ : ∥ wt_indices (Σ, ind_universes mdecl) mdecl indices cs ∥) :
    EnvCheck (∥ forall v : list Variance.t,
                    mdecl.(ind_variance) = Some v ->
                    cstr_respects_variance Σ mdecl v cs ∥) :=
    match mdecl.(ind_variance) with
    | None => ret _
    | Some v => 
      let univs := ind_universes mdecl in
      match variance_universes univs v with          
      | Some ((univs0, u), u') => 
        '(exist wfext eq) <- make_wf_env_ext Σ id univs0 ;;
        (* Incompleteness: this is an underapproximation of cumulativity of the contexts: 
           in general we should allow unfolding and reduction to happen before comparing the types of arguments.
           However in many cases it will be sufficient. E.g. for lists and regular structures this is enough 
           to check variance.

           Note that both contexts are well-typed in different contexts: 
           ind_arities@{u} ,,, params@{u} for args@{u} and
           ind_arities@{u'} ,,, params@{u'} for args@{u'}. 
           
           Hence we cannot use check_cumul_ctx here to verify the variance up-to conversion: the terms to be 
           converted would be in different, incompatible contexts.

           TODO: do as in Coq's kernel and implement a routine that takes whnfs of both sides and compare
           syntactically the heads. *)
        check_args <- wrap_error wfext.(@wf_env_ext_env cf) (string_of_kername id)
          (check_leq_context true wfext 
            (subst_instance u (expand_lets_ctx (ind_params mdecl) (smash_context [] (cstr_args cs))))
            (subst_instance u' (expand_lets_ctx (ind_params mdecl) (smash_context [] (cstr_args cs))))) ;;
        check_indices <- wrap_error wfext.(@wf_env_ext_env cf) (string_of_kername id)
          (check_leq_terms false wfext
            (map (subst_instance u ∘ expand_lets (ind_params mdecl ,,, cs.(cstr_args))) (cstr_indices cs))
            (map (subst_instance u' ∘ expand_lets (ind_params mdecl ,,, cs.(cstr_args))) (cstr_indices cs))) ;;
        ret _
      | None => False_rect _ _
      end
    end.

    Next Obligation.
      sq. by [].
    Qed.

    Next Obligation.
      destruct x as [Σ' wfΣ' G wfG]; simpl in *. subst Σ'.
      clear eq.
      destruct Σ as [Σ [wfΣ''] G' wfG']; simpl in *. sq.
      intros v0 [= <-].
      red. rewrite -Heq_anonymous.
      split; auto.
      now apply leq_context_cumul_context.
      clear check_args.
      eapply All2_impl. eauto. simpl; intros.
      now eapply eq_term_upto_univ_cumulSpec.
    Qed.
    Next Obligation.
      sq. rewrite -Heq_anonymous0 in mdeclvar.
      symmetry in Heq_anonymous.
      eapply (variance_universes_insts (Σ := (empty_ext Σ))) in mdeclvar as [univs' [i [i' []]]].
      rewrite Heq_anonymous in e. discriminate.
    Qed.

  (** Moving it causes a universe bug... *)
  Section MonadAllAll.
    Context {T : Type -> Type} {M : Monad T} {A} {P : A -> Type} {Q : A -> Type} (f : forall x, ∥ Q x ∥ -> T (∥ P x ∥)).
    Program Fixpoint monad_All_All l : ∥ All Q l ∥ -> T (∥ All P l ∥) := 
      match l return ∥ All Q l ∥ -> T (∥ All P l ∥) with
        | [] => fun _ => ret (sq All_nil)
        | a :: l => fun allq => 
        X <- f a _ ;;
        Y <- monad_All_All l _ ;;
        ret _
        end.
    Next Obligation. sq.
      now depelim allq.
    Qed.
    Next Obligation.
      sq; now depelim allq.
    Qed.
    Next Obligation.
      sq. constructor; assumption.
    Defined.
  End MonadAllAll.

  Program Definition check_constructors (Σ0 : wf_env) (Σ : wf_env_ext) (id : kername) (mdecl : mutual_inductive_body)
    (HΣ : Σ.(wf_env_ext_env) = (Σ0, ind_universes mdecl))
    (wfar : ∥ wf_ind_types Σ mdecl ∥)
    (wfpars : ∥ wf_local Σ (ind_params mdecl) ∥)
    (mdeclvar : ∥ on_variance Σ0 mdecl.(ind_universes) mdecl.(ind_variance) ∥)    
    (n : nat) (idecl : one_inductive_body) (indices : context)
    (hnth : nth_error mdecl.(ind_bodies) n = Some idecl)
    (heq : ∥ ∑ inds, idecl.(ind_type) = it_mkProd_or_LetIn (mdecl.(ind_params) ,,, indices) (tSort inds) ∥)
    : EnvCheck (∑ cs : list constructor_univs,
      ∥ on_constructors (lift_typing typing) Σ mdecl n idecl indices (ind_ctors idecl) cs ∥) :=
    
    '(cs; Hcs) <- check_constructors_univs Σ (string_of_kername id) mdecl wfar 
      wfpars (S n) idecl.(ind_ctors) ;;
    posc <- wrap_error Σ (string_of_kername id)
      (monad_All_All (fun x px => 
        @check_positive_cstr Σ (wf_env_ext_wf Σ) mdecl n 
          (arities_context mdecl.(ind_bodies)) (cstr_type x) _ [])
        idecl.(ind_ctors) (wt_cstrs (cs:=cs) Hcs)) ;;
    var <- monad_All_All (fun cs px => check_cstr_variance Σ0 mdecl id indices mdeclvar cs _ _)
      idecl.(ind_ctors) 
      (get_wt_indices wfar wfpars n idecl indices hnth heq Hcs) ;;
    lets <- monad_All (P := fun x => if @lets_in_constructor_types _
      then true else is_assumption_context (cstr_args x))   
     (fun cs => if @lets_in_constructor_types _
      then ret _ else (if is_assumption_context (cstr_args cs) then ret _ else EnvError Σ (IllFormedDecl "No lets in constructor types allowed, you need to set the checker flag lets_in_constructor_types to [true]."
        (Msg "No lets in constructor types allowed, you need to set the checker flag lets_in_constructor_types to [true].")  ))
    ) idecl.(ind_ctors) ;;
    ret (cs; _).
      
  Next Obligation. now sq. Qed.
  Next Obligation. apply wf_env_ext_wf. Qed.
  Next Obligation.
    destruct lets_in_constructor_types.
    + reflexivity.
    + red. congruence.
  Qed.
  Next Obligation.
    destruct lets_in_constructor_types; congruence.
  Qed.
  Next Obligation.
    epose proof (get_wt_indices wfar wfpars _ _ _ hnth heq Hcs).
    destruct Σ as [Σ wfΣ G wfG]; simpl in *. clear X.
    subst Σ; simpl in *. unfold check_constructor_spec in Hcs; simpl in *. sq.
    solve_all.
    eapply All2_impl; eauto. simpl.
    intros. 
    destruct X as [[lets [wtinds [wfvar posc]]] [[[isTy eq]] eq']].
    econstructor => //.
    rewrite eq.
    rewrite it_mkProd_or_LetIn_app. autorewrite with len. lia_f_equal.
    rewrite /cstr_concl /=. f_equal. rewrite /cstr_concl_head.
    lia_f_equal.
    now destruct wtinds.
    destruct lets_in_constructor_types; eauto.
  Qed. 

  Definition check_projections_type (Σ : wf_env_ext) (mind : kername) 
    (mdecl : mutual_inductive_body) (i : nat) (idecl : one_inductive_body) 
    (indices : context) :=
    ind_projs idecl <> [] ->
    match idecl.(ind_ctors) return Type with
    | [cs] => on_projections mdecl mind i idecl indices cs
    | _ => False
    end.

  Program Definition check_projection (Σ : wf_env_ext) (mind : kername) (mdecl : mutual_inductive_body)
    (i : nat) (idecl : one_inductive_body) (indices : context) 
    (cdecl : constructor_body) (cs : constructor_univs) 
    (oncs : ∥ on_constructors (lift_typing typing) Σ mdecl i idecl indices [cdecl] [cs] ∥) 
    (k : nat) (p : ident × term) (hnth : nth_error idecl.(ind_projs) k = Some p)
    (heq : #|idecl.(ind_projs)| = context_assumptions cdecl.(cstr_args))
    : typing_result (∥ on_projection mdecl mind i cdecl k p ∥) :=
    let Γ :=  smash_context [] (cdecl.(cstr_args) ++ ind_params mdecl) in
    match nth_error Γ (context_assumptions (cdecl.(cstr_args)) - S k) with
    | Some decl =>
      let u := abstract_instance (ind_universes mdecl) in
      let ind := {| inductive_mind := mind; inductive_ind := i |} in
      check_na <- check_eq_true (eqb (binder_name (decl_name decl)) (nNamed p.1)) 
        (Msg "Projection name does not match argument binder name");;
      check_eq <- check_eq_true (eqb p.2
          (subst (inds mind u (ind_bodies mdecl)) (S (ind_npars mdecl))
          (subst0 (projs ind (ind_npars mdecl) k) (lift 1 k (decl_type decl)))))
        (Msg "Projection type does not match argument type") ;;
      ret _
    | None => False_rect _ _
    end.
  Next Obligation.
    eapply eqb_eq in check_na.
    eapply eqb_eq in check_eq.
    sq.
    red. rewrite -Heq_anonymous. simpl. split; auto. 
  Qed.
  Next Obligation.
    sq. depelim oncs. depelim oncs.
    rename Heq_anonymous into hnth'.
    symmetry in hnth'. eapply nth_error_None in hnth'.
    eapply nth_error_Some_length in hnth.
    len in hnth'. lia.
  Qed.

  Program Definition check_projections_cs (Σ : wf_env_ext) (mind : kername) (mdecl : mutual_inductive_body)
    (i : nat) (idecl : one_inductive_body) (indices : context) 
    (cdecl : constructor_body) (cs : constructor_univs) 
    (oncs : ∥ on_constructors (lift_typing typing) Σ mdecl i idecl indices [cdecl] [cs] ∥)
    (onec : #|idecl.(ind_ctors)| = 1) : 
    typing_result (∥ on_projections mdecl mind i idecl indices cdecl ∥) :=
    check_indices <- check_eq_true (eqb [] indices) (Msg "Primitive records cannot have indices") ;;
    check_elim <- check_eq_true (eqb (ind_kelim idecl) IntoAny) (Msg "Primitive records must be eliminable to Type");;
    check_length <- check_eq_true (eqb #|idecl.(ind_projs)| (context_assumptions cdecl.(cstr_args)))
      (Msg "Invalid number of projections") ;;
    check_projs <- monad_Alli_nth idecl.(ind_projs) 
      (fun n p hnth => check_projection Σ mind mdecl i idecl indices cdecl cs oncs n p hnth (eqb_eq _ _ check_length)) ;;
    ret _.

    Next Obligation.
      sq.
      depelim oncs. depelim oncs.
      eapply eqb_eq in check_indices; subst indices.
      eapply eqb_eq in check_elim. eapply eqb_eq in check_length.
      constructor => //.
    Qed.

  Program Definition check_projections (Σ : wf_env_ext) (mind : kername) (mdecl : mutual_inductive_body)
    (i : nat) (idecl : one_inductive_body) (indices : context) (cs : list constructor_univs) :
    ∥ on_constructors (lift_typing typing) Σ mdecl i idecl indices idecl.(ind_ctors) cs ∥ -> 
    typing_result (∥ check_projections_type Σ mind mdecl i idecl indices ∥) :=
    match ind_projs idecl with
    | [] => fun _ => ret _
    | _ => 
      match idecl.(ind_ctors) as x, cs return
        x = idecl.(ind_ctors) ->
        ∥ on_constructors (lift_typing typing) Σ mdecl i idecl indices x cs ∥ -> 
          typing_result (∥ check_projections_type Σ mind mdecl i idecl indices ∥)
      with
      | [ cdecl ], [ cs ] => fun eq oncs => 
        ccs <- check_projections_cs Σ mind mdecl i idecl indices cdecl cs oncs _ ;; 
        ret _
      | _, _ => fun eq oncs => raise (Msg "Projections can only be declared for an inductive type with a single constructor")
      end eq_refl
    end.
  Next Obligation.
    rename Heq_anonymous into eqp. 
    sq. red. rewrite -eqp. congruence.
  Qed.
  Next Obligation.
    sq. red. intros. rewrite -eq //.
  Qed.
  
  Definition checkb_constructors_smaller (G : universes_graph) (cs : list constructor_univs) (ind_sort : Universe.t) :=
    List.forallb (List.forallb (fun argsort => check_leqb_universe G argsort ind_sort)) cs.

  Lemma check_constructors_smallerP (Σ : wf_env_ext) cs ind_sort : 
    Forall (fun cs => Forall (wf_universe Σ) cs) cs -> wf_universe Σ ind_sort ->
    ∥ reflect (check_constructors_smaller Σ cs ind_sort) (checkb_constructors_smaller Σ cs ind_sort) ∥.
  Proof.
    unfold check_constructors_smaller, checkb_constructors_smaller.
    intros wfcs wfind.
    destruct Σ as [Σ wfΣ G wfG]. simpl in *. sq.
    eapply forallbP_cond; eauto. clear wfcs.
    simpl; intros c wfc.
    pose proof (check_leqb_universe_spec' G (global_ext_uctx Σ)).
    forward H. apply wf_ext_global_uctx_invariants; auto.
    forward H. apply wfΣ.
    eapply forallbP_cond; eauto. simpl. intros x wfx.
    specialize (H wfG x ind_sort). simpl.
    destruct check_leqb_universe eqn:eq; constructor.
    now simpl in H.
    intro. simpl in H.
    pose proof (check_leqb_universe_complete G (global_ext_uctx Σ)).
    forward H1. apply wf_ext_global_uctx_invariants. now sq.
    forward H1. apply wfΣ.
    specialize (H1 wfG x ind_sort). simpl in H1.
    forward H1.
    red in wfx. destruct x; auto.
    forward H1.
    red in wfind. destruct ind_sort; auto.
    specialize (H1 H0). congruence.
  Qed.

  Definition wf_cs_sorts (Σ : wf_env_ext) cs := 
    Forall (fun cs => Forall (wf_universe Σ) cs) cs.

  Program Definition do_check_ind_sorts (Σ : wf_env_ext) (params : context) (wfparams : ∥ wf_local Σ params ∥) 
    (kelim : allowed_eliminations) (indices : context) 
    (cs : list constructor_univs) 
    (wfcs : wf_cs_sorts Σ cs)
    (ind_sort : Universe.t) 
    (wfi : wf_universe Σ ind_sort): 
    typing_result (∥ check_ind_sorts (lift_typing typing) Σ params kelim indices cs ind_sort ∥) := 
    match ind_sort with
    | Universe.lSProp => 
      check_eq_true (allowed_eliminations_subset kelim (elim_sort_sprop_ind cs)) 
        (Msg "Incorrect allowed_elimination for inductive") ;; 
      ret _
    | Universe.lProp => 
      check_eq_true (allowed_eliminations_subset kelim (elim_sort_prop_ind cs)) 
        (Msg "Incorrect allowed_elimination for inductive") ;; ret _
    | Universe.lType u => 
      check_eq_true (checkb_constructors_smaller Σ cs ind_sort) 
        (Msg ("Incorrect inductive sort: The constructor arguments universes are not smaller than the declared inductive sort")) ;;
      match indices_matter with
      | true =>
        (* FIXME this is a strict underapproximation, we should use sorts_local_ctx as the indices might be 
          in sorts which don't necessarily have a sup. *)
        tyloc <- check_type_local_ctx Σ params indices ind_sort wfparams ;;
        ret _
      | false => ret _
      end
    end.

    Next Obligation.
      unfold check_ind_sorts. simpl.
      pose proof (check_constructors_smallerP Σ cs u wfcs wfi).
      rewrite -Heq_anonymous. sq. split => //.
      destruct H0 => //.
    Qed.
    Next Obligation.
      unfold check_ind_sorts. simpl.
      pose proof (check_constructors_smallerP Σ cs u wfcs wfi).
      sq. split. destruct H0 => //.
      rewrite -Heq_anonymous; auto.
    Qed.
    
  Lemma sorts_local_ctx_wf_sorts (Σ : global_env_ext) {wfΣ : wf Σ} Γ Δ s : 
    sorts_local_ctx (lift_typing typing) Σ Γ Δ s ->
    Forall (wf_universe Σ) s.
  Proof.
    induction Δ in s |- *; destruct s; simpl; auto.
    destruct a as [na [b|] ty].
    - intros []. eauto.
    - intros []; eauto. constructor; eauto.
      now eapply typing_wf_universe in t0.
  Qed.

  Obligation Tactic := Program.Tactics.program_simplify.

  Program Definition check_indices (Σ : wf_env) mdecl (id : kername)
    (wfΣ : ∥ wf_ext (Σ, ind_universes mdecl) ∥)
    (mdeclvar : ∥ on_variance Σ mdecl.(ind_universes) mdecl.(ind_variance) ∥)
    indices (wfΓ : ∥ wf_local (Σ, ind_universes mdecl) (ind_params mdecl ,,, indices) ∥) :
    EnvCheck (∥ forall v : list Variance.t,
                    mdecl.(ind_variance) = Some v ->
                    ind_respects_variance Σ mdecl v indices ∥) :=
    match mdecl.(ind_variance) with
    | None => ret _
    | Some v => 
      let univs := ind_universes mdecl in
      match variance_universes univs v with          
      | Some ((univs0, u), u') => 
        '(exist wfext eq) <- make_wf_env_ext Σ id univs0 ;;
        checkctx <- wrap_error wfext.(@wf_env_ext_env cf) (string_of_kername id)
          (check_leq_context true wfext
            (subst_instance u (expand_lets_ctx (ind_params mdecl) (smash_context [] indices)))
            (subst_instance u' (expand_lets_ctx (ind_params mdecl) (smash_context [] indices)))) ;;
        ret _
      | None => False_rect _ _
      end
    end.
  Next Obligation.
    sq. discriminate.
  Qed.
  Next Obligation. 
    clear H.
    destruct x as [Σ' wfΣ' G wfG]. simpl in *. subst Σ'.
    rename Heq_anonymous0 into eqvar.
    rename Heq_anonymous into eqvaru.
    sq. intros ? [= <-]. red. simpl.
    rewrite -eqvaru.
    unfold variance_universes in eqvaru.
    unfold check_variance in mdeclvar.
    rewrite -eqvar in mdeclvar.
    destruct (ind_universes mdecl) as [|[inst cstrs]] => //.
    now eapply leq_context_cumul_context.
  Qed.

  Next Obligation.
    rename Heq_anonymous0 into eqvar.
    rename Heq_anonymous into eqvaru.
    sq. rewrite -eqvar in mdeclvar.
    eapply (variance_universes_insts (Σ := empty_ext Σ)) in mdeclvar as [univs' [i [i' []]]].
    rewrite -eqvaru in e; discriminate.
  Qed.

  Program Definition check_ind_types (Σ : wf_env_ext) (mdecl : mutual_inductive_body)
      : EnvCheck (∥ wf_ind_types Σ mdecl ∥) :=
    indtys <- monad_All (fun ind => wrap_error Σ ind.(ind_name) (infer_type_wf_env Σ [] sq_wfl_nil ind.(ind_type))) mdecl.(ind_bodies) ;;
    ret _.
    Next Obligation.
      eapply All_sigma in indtys as [indus Hinds].
      eapply All2_sq in Hinds. sq.
      red.
      solve_all. now exists y.
    Qed.

  Program Definition check_one_ind_body (Σ0 : wf_env) (Σ : wf_env_ext) 
      (mind : kername) (mdecl : mutual_inductive_body)
      (pf : Σ.(wf_env_ext_env) = (Σ0.(wf_env_env), mdecl.(ind_universes)))
      (wfpars : ∥ wf_local Σ mdecl.(ind_params) ∥)
      (wfars : ∥ wf_ind_types Σ mdecl ∥)
      (mdeclvar : ∥ on_variance Σ0 mdecl.(ind_universes) mdecl.(ind_variance) ∥)
      (i : nat) (idecl : one_inductive_body)
      (hnth : nth_error mdecl.(ind_bodies) i = Some idecl)
      : EnvCheck (∥ on_ind_body (lift_typing typing) Σ mind mdecl i idecl ∥) :=
      let id := string_of_kername mind in
      '(ctxinds; p) <-
        wrap_error Σ id ((match destArity [] idecl.(ind_type) as da return da = destArity [] idecl.(ind_type) -> typing_result (∑ ctxs, idecl.(ind_type) = it_mkProd_or_LetIn ctxs.1 (tSort ctxs.2)) with
        | Some (ctx, s) => fun eq => ret ((ctx, s); _)
        | None => fun _ => raise (NotAnArity idecl.(ind_type))
        end eq_refl)) ;;
      let '(indices, params) := split_at (#|ctxinds.1| - #|mdecl.(ind_params)|) ctxinds.1 in
      eqsort <- wrap_error Σ id 
        (check_eq_true (eqb ctxinds.2 idecl.(ind_sort)) 
        (Msg "Inductive body sort does not match the sort of the inductive type"));;
      eqpars <- wrap_error Σ id 
        (check_eq_true (eqb params mdecl.(ind_params)) 
        (Msg "Inductive arity parameters do not match the parameters of the mutual declaration"));;
      eqindices <- wrap_error Σ id 
        (check_eq_true (eqb indices idecl.(ind_indices)) 
        (Msg "Inductive arity indices do not match the indices of the mutual declaration"));;
      '(cs; oncstrs) <- (check_constructors Σ0 Σ mind mdecl pf wfars wfpars mdeclvar i idecl idecl.(ind_indices) hnth _) ;;
      onprojs <- wrap_error Σ ("Checking projections of " ^ id) 
       (check_projections Σ mind mdecl i idecl idecl.(ind_indices) cs oncstrs) ;;
      onsorts <- wrap_error Σ ("Checking universes of " ^ id)
        (do_check_ind_sorts Σ mdecl.(ind_params) wfpars idecl.(ind_kelim)
           idecl.(ind_indices) cs _ ctxinds.2 _) ;;
      onindices <- (check_indices Σ0 mdecl mind _ mdeclvar idecl.(ind_indices) _) ;;
      ret (let 'sq wfars := wfars in 
        let 'sq wfext := Σ.(wf_env_ext_wf) in
        let 'sq oncstrs := oncstrs in
        let 'sq onprojs := onprojs in
        let 'sq onindices := onindices in
        let 'sq onsorts := onsorts in
        (sq 
        {| ind_arity_eq := _; onArity := _;
           ind_cunivs := cs;
           onConstructors := oncstrs;
           onProjections := onprojs;
           onIndices := _ |})).
  Next Obligation. 
    symmetry in eq.
    apply destArity_spec_Some in eq. now simpl in eq.
  Qed.

  Next Obligation.
    destruct Σ as [Σ wfΣ G wfG]; simpl in *.
    sq. exists t0.
    destruct (eqb_spec params (ind_params mdecl)); [|discriminate]. subst params.
    rewrite split_at_firstn_skipn in Heq_anonymous. noconf Heq_anonymous.
    rewrite {1}H. apply eqb_eq in eqindices.
    rewrite -eqindices. now rewrite /app_context firstn_skipn.
  Qed.
  
  Next Obligation.
    destruct Σ as [Σ wfΣ G wfG]; simpl in *.
    sq. red. simpl. red in X. solve_all.
    destruct X.
    eapply sorts_local_ctx_wf_sorts, Forall_All in on_cargs; auto.
  Qed. 

  Next Obligation.
    destruct Σ as [Σ wfΣ G wfG]; simpl in *. sq.
    eapply nth_error_all in wfars; eauto; simpl in wfars.
    destruct wfars as [s Hs]. red in Hs.
    clear X0; rewrite p in Hs.
    eapply PCUICSpine.inversion_it_mkProd_or_LetIn in Hs; eauto.
    now eapply inversion_Sort in Hs as [_ [wf _]].
  Qed. 

  Next Obligation.
    apply wf_env_ext_wf.
  Qed.
  Next Obligation.
    destruct Σ as [Σ wfΣ G wfG]; simpl in *. sq.
    clear onprojs onsorts X.
    red in wfars. eapply nth_error_all in wfars; eauto; simpl in wfars.
    destruct wfars as [s Hs].
    apply eqb_eq in eqpars; apply eqb_eq in eqindices; subst.
    red in Hs.
    rewrite split_at_firstn_skipn in Heq_anonymous.
    noconf Heq_anonymous.
    rewrite {1}H {1}H0 /app_context firstn_skipn.
    rewrite X0 in Hs.
    eapply PCUICSpine.inversion_it_mkProd_or_LetIn in Hs; eauto.
    eapply typing_wf_local in Hs. now rewrite app_context_nil_l in Hs.
  Qed.

  Next Obligation.
    cbn in eqsort; apply eqb_eq in eqpars; apply eqb_eq in eqindices; apply eqb_eq in eqsort; subst.
    rewrite split_at_firstn_skipn in Heq_anonymous0. cbn in *.
    noconf Heq_anonymous0.
    now rewrite {1}H {1}H0 /app_context -it_mkProd_or_LetIn_app firstn_skipn.
  Qed.
  
  Next Obligation.
    destruct (eqb_spec params (ind_params mdecl)); [|discriminate]. subst params.
    red. red.
    eapply nth_error_all in wfars; eauto; simpl in wfars.
    destruct wfars as [s Hs]. red in Hs. now exists s.
  Qed.

  Next Obligation.
    destruct Σ as [Σ wfΣ G wfG]; simpl in *.
    subst Σ; simpl in *.
    now apply eqb_eq in eqsort; subst.
  Qed.
  Next Obligation.
    rewrite pf. now apply onindices.
  Qed.

  Program Definition check_wf_decl (Σ0 : wf_env) (Σ : global_env_ext) HΣ G HG
             kn (d : global_decl) (eq : Σ = (Σ0, universes_decl_of_decl d))
    : EnvCheck (∥ on_global_decl (lift_typing typing) Σ kn d ∥) :=
    match d with
    | ConstantDecl cst =>
      match cst.(cst_body) with
      | Some term => check_wf_judgement kn Σ HΣ G HG term cst.(cst_type) ;; ret _
      | None => check_wf_type kn Σ HΣ G HG cst.(cst_type) ;; ret _
      end
    | InductiveDecl mdecl =>
      let wfΣ : wf_env_ext := {| wf_env_ext_env := Σ; wf_env_ext_wf := HΣ; 
        wf_env_ext_graph := G; wf_env_ext_graph_wf := HG |} in
      let id := string_of_kername kn in
      check_var <- check_variance (Σ := Σ0) kn (ind_universes mdecl) (ind_variance mdecl) _ ;;
      check_pars <- wrap_error Σ id (check_context_wf_env wfΣ (ind_params mdecl)) ;;
      check_npars <- wrap_error Σ id 
        (check_eq_nat (context_assumptions (ind_params mdecl))
            (ind_npars mdecl) (Msg "wrong number of parameters")) ;;
      onarities <- check_ind_types wfΣ mdecl ;;
      check_bodies <- monad_Alli_nth mdecl.(ind_bodies) (fun i oib Hoib => check_one_ind_body Σ0 wfΣ kn mdecl eq check_pars onarities check_var i oib Hoib);;
      ret (Build_on_inductive_sq check_bodies check_pars check_npars _)
    end.
  Next Obligation.
    sq. unfold on_constant_decl; rewrite <- Heq_anonymous.
    eassumption.
  Qed.
  Next Obligation.
    sq. unfold on_constant_decl. rewrite <- Heq_anonymous; tea.
  Qed.
  Next Obligation. exact HΣ. Qed. 
  Next Obligation. reflexivity. Qed.
  Next Obligation.
    exact check_var.
  Qed.

  Obligation Tactic := Program.Tactics.program_simpl.

  Program Fixpoint check_wf_env (Σ : global_env)
    : EnvCheck (∑ G, (is_graph_of_uctx G (global_uctx Σ) /\ ∥ wf Σ ∥)) :=
    match Σ with
    | [] => ret (init_graph; _)
    | d :: Σ =>
        G <- check_wf_env Σ ;;
        let wfΣ : wf_env := {| wf_env_env := Σ; wf_env_graph := G.π1 |} in
        check_fresh d.1 Σ ;;
        let udecl := universes_decl_of_decl d.2 in
        uctx <- check_udecl (string_of_kername d.1) Σ _ G.π1 (proj1 G.π2) udecl ;;
        let G' := add_uctx uctx.π1 G.π1 in
        check_wf_decl wfΣ (Σ, udecl) _ G' _ d.1 d.2 _ ;;
        match udecl with
        | Monomorphic_ctx _ => ret (G'; _)
        | Polymorphic_ctx _ => ret (G.π1; _)
        end
    end.
  Next Obligation.
    repeat constructor.
  Qed.
  Next Obligation.
    sq. split; eauto.
  Qed.
  Next Obligation.
    sq. unfold is_graph_of_uctx, gc_of_uctx; simpl.
    unfold gc_of_uctx in e. simpl in e.
    case_eq (gc_of_constraints (constraints_of_udecl (universes_decl_of_decl g)));
      [|intro HH; rewrite HH in e; discriminate e].
    intros ctrs' Hctrs'. rewrite Hctrs' in e.
    cbn in e. inversion e; subst; clear e.
    unfold global_ext_constraints; simpl.
    pose proof (gc_of_constraints_union 
      (constraints_of_udecl (universes_decl_of_decl g)) (global_constraints Σ)) as H0.
    rewrite Hctrs' /= in H0.
    red in i. unfold gc_of_uctx in i; simpl in i.
    case_eq (gc_of_constraints (global_constraints Σ));
      [|intro HH; rewrite HH in i; cbn in i; contradiction i].
    intros Σctrs HΣctrs; rewrite HΣctrs in H0, i; simpl in *.
    destruct (gc_of_constraints (ConstraintSet.union _ _)).
    simpl in H0. 
    subst G. unfold global_ext_levels; simpl.
    symmetry. rewrite add_uctx_make_graph.
    apply graph_eq. simpl. reflexivity.
    simpl. now rewrite H0. simpl. reflexivity.
    now simpl in H0.
  Qed.
  Next Obligation.
    split; sq. 2: constructor; tas.
    unfold is_graph_of_uctx, gc_of_uctx; simpl.
    unfold gc_of_uctx in e. simpl in e.
    case_eq (gc_of_constraints (constraints_of_udecl (universes_decl_of_decl g)));
      [|intro HH; rewrite HH in e; discriminate e].
    intros ctrs' Hctrs'. rewrite Hctrs' in e.
    cbn in e. inversion e; subst; clear e.
    unfold global_ext_constraints; simpl.
    pose proof (gc_of_constraints_union 
      (constraints_of_udecl (universes_decl_of_decl g)) (global_constraints Σ)).
    rewrite Hctrs' /= in H1.
    red in i. unfold gc_of_uctx in i; simpl in i.
    assert (eq: monomorphic_constraints_decl g
                = constraints_of_udecl (universes_decl_of_decl g)). {
      destruct g.
      destruct c, cst_universes0; try discriminate; reflexivity.
      destruct m, ind_universes0; try discriminate; reflexivity. }
    rewrite eq; clear eq. 
    case_eq (gc_of_constraints (global_constraints Σ));
      [|intro HH; rewrite HH in i; cbn in i; contradiction i].
    intros Σctrs HΣctrs; rewrite HΣctrs in H1, i; simpl in *.
    destruct (gc_of_constraints (ConstraintSet.union _ _)).
    simpl in H1.
    subst G. unfold global_ext_levels; simpl.
    assert (eq: monomorphic_levels_decl g
                = levels_of_udecl (universes_decl_of_decl g)). {
      destruct g. destruct c, cst_universes0; try discriminate; reflexivity.
      destruct m, ind_universes0; try discriminate; reflexivity. }
    rewrite eq. simpl. rewrite add_uctx_make_graph.
    apply graph_eq; try reflexivity.
    simpl. now rewrite H1.
    now simpl in H1.
  Qed.
  Next Obligation.
    split; sq. 2: constructor; tas.
    unfold global_uctx; simpl.
    assert (eq1: monomorphic_levels_decl g = LevelSet.empty). {
      destruct g. destruct c, cst_universes0; try discriminate; reflexivity.
      destruct m, ind_universes0; try discriminate; reflexivity. }
    rewrite eq1; clear eq1.
    assert (eq1: monomorphic_constraints_decl g = ConstraintSet.empty). {
      destruct g. destruct c, cst_universes0; try discriminate; reflexivity.
      destruct m, ind_universes0; try discriminate; reflexivity. }
    rewrite eq1; clear eq1.
    now rewrite LevelSet_union_empty CS_union_empty.
  Qed.

  Obligation Tactic := idtac.

  Program Definition check_wf_ext (Σ : global_env_ext) : EnvCheck (∑ G, is_graph_of_uctx G (global_ext_uctx Σ) * ∥ wf_ext Σ ∥) :=
    G <- check_wf_env Σ.1 ;;
    uctx <- check_udecl "toplevel term" Σ.1 (proj2 G.π2) G.π1 (proj1 G.π2) Σ.2 ;;
    let G' := add_uctx uctx.π1 G.π1 in
    ret (G'; _).

  Next Obligation. simpl. 
    simpl; intros. subst. destruct G as [G []].
    destruct uctx as [uctx' []]. split.
    unfold is_graph_of_uctx, gc_of_uctx in *; simpl.
    destruct Σ as [Σ univs]. simpl in *.
    simpl in e. simpl. 
    case_eq (gc_of_constraints (constraints_of_udecl univs));
      [|intro HH; rewrite HH in e; discriminate e].
    intros ctrs' Hctrs'. rewrite Hctrs' in e.
    noconf e.
    unfold global_ext_constraints; simpl.
    pose proof (gc_of_constraints_union (constraints_of_udecl univs) (global_constraints Σ)).
    rewrite Hctrs' /= in H.
    red in i. unfold gc_of_uctx in i; simpl in i. 
    destruct (gc_of_constraints (global_constraints Σ)) eqn:HΣcstrs; auto.
    simpl. unfold global_ext_levels; simpl.
    destruct (gc_of_constraints (ConstraintSet.union _ _)); simpl in H => //.
    simpl.
    subst G. symmetry. rewrite add_uctx_make_graph.
    apply graph_eq; try reflexivity.
    now simpl; rewrite H.
    sq; split; auto.
  Qed.

  Definition check_type_wf_env_bool (Σ : wf_env_ext) Γ (wfΓ : ∥ wf_local Σ Γ ∥) t T : bool :=
    match check_type_wf_env Σ Γ wfΓ t T with
    | Checked _ => true
    | TypeError e => false
    end.
  
  Definition check_wf_env_bool_spec (Σ : wf_env_ext) Γ (wfΓ : ∥ wf_local Σ Γ ∥) t T :
    check_type_wf_env_bool Σ Γ wfΓ t T = true -> ∥ Σ ;;; Γ |- t : T ∥.
  Proof.
    unfold check_type_wf_env_bool.
    destruct check_type_wf_env ; auto.
    discriminate.
  Qed.

  Definition check_wf_env_bool_spec2 (Σ : wf_env_ext) Γ (wfΓ : ∥ wf_local Σ Γ ∥) t T :
    check_type_wf_env_bool Σ Γ wfΓ t T = false -> type_error.
  Proof.
    unfold check_type_wf_env_bool.
    destruct check_type_wf_env; auto.
    discriminate.
  Defined.

  (* This function is appropriate for live evaluation inside Coq: 
     it forgets about the derivation produced by typing and replaces it with an opaque constant. *)

  Program Definition check_type_wf_env_fast (Σ : wf_env_ext) Γ (wfΓ : ∥ wf_local Σ Γ ∥) t {T} : typing_result (∥ Σ ;;; Γ |- t : T ∥) := 
    (if check_type_wf_env_bool Σ Γ wfΓ t T as x return (check_type_wf_env_bool Σ Γ wfΓ t T = x -> typing_result _) then
      fun eq => ret _
    else fun eq => raise (check_wf_env_bool_spec2 Σ Γ wfΓ t T eq)) eq_refl.

  Next Obligation.
    simpl; intros. exact (check_wf_env_bool_spec Σ Γ wfΓ t T eq).
  Qed.

  Obligation Tactic := Program.Tactics.program_simpl.
  
  Program Definition typecheck_program (p : program) φ
    : EnvCheck (∑ A, ∥ wf_ext (p.1, φ) × (p.1, φ) ;;; [] |- p.2 ▹ A ∥) :=
    let Σ := fst p in
    '(existT G HG) <- check_wf_env Σ ;;
    uctx <- check_udecl "toplevel term" Σ _ G (proj1 HG) φ ;;
    let G' := add_uctx uctx.π1 G in
    inft <- @infer_term (Σ, φ) _ G' _ (snd p) ;; 
    ret _.
  Next Obligation.
    sq. split; tea.
  Qed.
  Next Obligation.
    (* todo: factorize with check_wf_env second obligation *)
    sq. unfold is_graph_of_uctx, gc_of_uctx; simpl.
    unfold gc_of_uctx in e. simpl in e.
    case_eq (gc_of_constraints (constraints_of_udecl φ));
      [|intro HH; rewrite HH in e; discriminate e].
    intros ctrs' Hctrs'. rewrite Hctrs' in e.
    cbn in e. inversion e; subst; clear e.
    unfold global_ext_constraints; simpl.
    pose proof (gc_of_constraints_union (constraints_of_udecl φ) (global_constraints p.1)).
    rewrite Hctrs' /= in H.
    red in i. unfold gc_of_uctx in i; simpl in i. 
    destruct (gc_of_constraints (global_constraints p.1)) eqn:HΣcstrs; auto.
    simpl. unfold global_ext_levels; simpl.
    destruct (gc_of_constraints (ConstraintSet.union _ _)); simpl in H => //.
    simpl. simpl in i.
    subst x. symmetry. rewrite add_uctx_make_graph.
    apply graph_eq; try reflexivity.
    now simpl; rewrite H. simpl in H.
    destruct (gc_of_constraints (ConstraintSet.union _ _)); simpl in H => //.
  Qed.
  Next Obligation.
    exists inft; sq. split; eauto.
    split; eauto.
  Qed.

End CheckEnv.

(* Print Assumptions typecheck_program. *)
