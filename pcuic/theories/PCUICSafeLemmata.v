(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICConfluence
     PCUICCumulativity PCUICSR PCUICPosition PCUICEquality PCUICNameless
     PCUICAlpha PCUICNormal PCUICInversion PCUICReduction PCUICSubstitution
     PCUICConversion PCUICContextConversion PCUICValidity
     PCUICArities PCUICWeakeningEnv PCUICGeneration PCUICUnivSubstitution
     PCUICParallelReductionConfluence PCUICWellScopedCumulativity
     PCUICOnFreeVars.

Require Import ssreflect ssrbool.
Require Import Equations.Prop.DepElim.
Set Equations With UIP.

Local Set Keyed Unification.

Set Default Goal Selector "!".
Require Import PCUICSpine PCUICInductives PCUICWeakening PCUICContexts PCUICInductiveInversion.

Lemma wf_inst_case_context {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ} {ci : case_info}
  {mdecl idecl} {uinst params} ctx :
  declared_inductive Σ ci mdecl idecl ->
  wf_local Σ Γ ->
  consistent_instance_ext Σ (ind_universes mdecl) uinst ->
  spine_subst Σ Γ params (List.rev params) (smash_context [] (subst_instance uinst (ind_params mdecl))) ->
  wf_local_rel Σ (Γ,,, smash_context [] (ind_params mdecl)@[uinst]) ctx@[uinst] ->
  wf_local Σ (Γ ,,, inst_case_context params uinst ctx).
Proof.
  move=> isdecl wfΓ cu sp wfr.
  rewrite /pre_case_predicate_context_gen /inst_case_context /ind_predicate_context /=.
  eapply PCUICSubstitution.substitution_wf_local. 
  * eapply sp.
  * unshelve epose proof (on_minductive_wf_params_indices_inst isdecl _ cu).
  rewrite PCUICUnivSubstitution.subst_instance_app_ctx in X.
  eapply wf_local_app_inv in X as [].
  eapply wf_local_app => //.
  eapply wf_local_smash_end.
  now eapply weaken_wf_local; tea.
Qed.

Section Lemmata.
  Context {cf : checker_flags}.
  Context (flags : RedFlags.t).

  Instance All2_eq_refl Σ Re : 
    RelationClasses.Reflexive Re ->
    CRelationClasses.Reflexive (All2 (eq_term_upto_univ Σ Re Re)).
  Proof.
    intros h x. apply All2_same. reflexivity.
  Qed.

  Instance All2_br_eq_refl Σ Re :
    RelationClasses.Reflexive Re ->
    CRelationClasses.Reflexive (All2
      (fun x y : branch term =>
        eq_context_upto Σ Re Re (bcontext x) (bcontext y) *
        eq_term_upto_univ Σ Re Re (bbody x) (bbody y))).
  Proof.
    intros h x.
    apply All2_same; split; reflexivity.
  Qed.

  (* red is the reflexive transitive closure of one-step reduction and thus
     can't be used as well order. We thus define the transitive closure,
     but we take the symmetric version.
   *)
  Inductive cored Σ Γ: term -> term -> Prop :=
  | cored1 : forall u v, red1 Σ Γ u v -> cored Σ Γ v u
  | cored_trans : forall u v w, cored Σ Γ v u -> red1 Σ Γ v w -> cored Σ Γ w u.

  Derive Signature for cored.

  Hint Resolve eq_term_upto_univ_refl : core.

  Context (Σ : global_env_ext).

  Inductive welltyped Σ Γ t : Prop :=
  | iswelltyped A : Σ ;;; Γ |- t : A -> welltyped Σ Γ t.

  Arguments iswelltyped {Σ Γ t A} h.

  Definition isType_welltyped {Γ T}
    : isType Σ Γ T -> welltyped Σ Γ T.
  Proof.
    intros []. now econstructor.
  Qed.
  Hint Resolve isType_welltyped : pcuic.
  
  Lemma equality_zippx :
    forall {wfΣ : wf Σ} le Γ u v ρ,
      closedn_stack #|Γ| ρ ->
      Σ ;;; (Γ ,,, stack_context ρ) ⊢ u ≤[le] v ->
      Σ ;;; Γ ⊢ zippx u ρ ≤[le] zippx v ρ.
  Proof.
    intros wfΣ le Γ u v ρ cl h.
    induction ρ in u, v, cl, h |- *; auto.
    destruct a.
    all: try solve [
      unfold zippx ; simpl ;
      eapply equality_it_mkLambda_or_LetIn_codom ;
      assumption
    ].
    - unfold zippx. simpl.
      case_eq (decompose_stack ρ). intros l π e.
      unfold zippx in IHρ. rewrite e in IHρ.
      move: cl => /= /andP[] cl cl'. apply IHρ => //. 
      eapply equality_App_l; tas.
      eapply closedn_on_free_vars; len. 
      now rewrite Nat.add_comm.
    - unfold zippx. simpl.
      eapply equality_it_mkLambda_or_LetIn_codom. cbn.
      eapply equality_Lambda_r.
      assumption.
    - unfold zippx. simpl.
      eapply equality_it_mkLambda_or_LetIn_codom. cbn.
      eapply equality_Lambda_r.
      assumption.
    - unfold zippx. simpl.
      eapply equality_it_mkLambda_or_LetIn_codom. cbn.
      eapply equality_LetIn_bo. assumption.
  Qed.

  Lemma conv_alt_it_mkLambda_or_LetIn :
    forall {wfΣ : wf Σ} Δ Γ u v,
      Σ ;;; (Δ ,,, Γ) ⊢ u = v ->
      Σ ;;; Δ ⊢ it_mkLambda_or_LetIn Γ u = it_mkLambda_or_LetIn Γ v.
  Proof.
    intros wfΣ Δ Γ u v h. revert Δ u v h.
    induction Γ as [| [na [b|] A] Γ ih ] ; intros Δ u v h.
    - assumption.
    - simpl. cbn. eapply ih.
      eapply equality_LetIn_bo. assumption.
    - simpl. cbn. eapply ih.
      eapply equality_Lambda_r. assumption.    
  Qed.

  Lemma snoc_app_context {Γ Δ d} : (Γ ,,, (d :: Δ)) =  (Γ ,,, Δ) ,,, [d].
  Proof.
    reflexivity.
  Qed.
  
  Lemma conv_alt_it_mkProd_or_LetIn :
    forall {wfΣ : wf Σ} Δ Γ B B',
      Σ ;;; (Δ ,,, Γ) ⊢ B = B' ->
      Σ ;;; Δ ⊢ it_mkProd_or_LetIn Γ B = it_mkProd_or_LetIn Γ B'.
  Proof.
    intros wfΣ Δ Γ B B' h.
    have cl : is_closed_context (Δ ,,, Γ).
    { now apply equality_is_closed_context in h. }
    induction Γ as [| [na [b|] A] Γ ih ] in Δ, B, B', h, cl |- *.
    - assumption.
    - simpl. cbn. eapply ih => //.
      * eapply equality_LetIn_bo. assumption.
      * rewrite snoc_app_context on_free_vars_ctx_app /= in cl.
        now move/andP: cl.
    - simpl. cbn. 
      rewrite snoc_app_context on_free_vars_ctx_app /= in cl.
      move/andP: cl => [cl cld]. cbn in cld.
      rewrite andb_true_r in cld. setoid_rewrite shiftnP_add in cld.
      eapply ih => //.
      eapply equality_Prod; auto. apply equality_refl => //.
  Qed.

  Context (hΣ : ∥ wf Σ ∥).

  Lemma validity_wf {Γ t T} :
    ∥ Σ ;;; Γ |- t : T ∥ -> welltyped Σ Γ T.
  Proof.
    destruct hΣ as [wΣ]. intros [X].
    intros. eapply validity in X; try assumption.
    destruct X. now exists (tSort x).
  Defined.

  Lemma wat_welltyped {Γ T} :
    ∥ isType Σ Γ T ∥ -> welltyped Σ Γ T.
  Proof.
    destruct hΣ as [wΣ]. intros [X].
    now apply isType_welltyped.
  Defined.

  Lemma welltyped_alpha Γ u v :
      welltyped Σ Γ u ->
      eq_term_upto_univ [] eq eq u v ->
      welltyped Σ Γ v.
  Proof.
    intros [A h] e.
    destruct hΣ.
    exists A. eapply typing_alpha ; eauto.
  Qed.

  Lemma red_cored_or_eq :
    forall Γ u v,
      red Σ Γ u v ->
      cored Σ Γ v u \/ u = v.
  Proof.
    intros Γ u v h.
    induction h using red_rect'.
    - right. reflexivity.
    - destruct IHh.
      + left. eapply cored_trans ; eassumption.
      + subst. left. constructor. assumption.
  Qed.

  Lemma cored_it_mkLambda_or_LetIn :
    forall Γ Δ u v,
      cored Σ (Γ ,,, Δ) u v ->
      cored Σ Γ (it_mkLambda_or_LetIn Δ u)
               (it_mkLambda_or_LetIn Δ v).
  Proof.
    intros Γ Δ u v h.
    induction h.
    - constructor. apply red1_it_mkLambda_or_LetIn. assumption.
    - eapply cored_trans.
      + eapply IHh.
      + apply red1_it_mkLambda_or_LetIn. assumption.
  Qed.

  Lemma cored_welltyped :
    forall {Γ u v},
      welltyped Σ Γ u ->
      cored (fst Σ) Γ v u ->
      welltyped Σ Γ v.
  Proof.
    destruct hΣ as [wΣ]; clear hΣ.
    intros Γ u v h r.
    revert h. induction r ; intros h.
    - destruct h as [A h]. exists A.
      eapply subject_reduction1 ; eauto with wf.
    - specialize IHr with (1 := ltac:(eassumption)).
      destruct IHr as [A ?]. exists A.
      eapply subject_reduction1 ; eauto with wf.
  Qed.

  Lemma cored_trans' :
    forall {Γ u v w},
      cored Σ Γ u v ->
      cored Σ Γ v w ->
      cored Σ Γ u w.
  Proof.
    intros Γ u v w h1 h2. revert w h2.
    induction h1 ; intros z h2.
    - eapply cored_trans ; eassumption.
    - eapply cored_trans.
      + eapply IHh1. assumption.
      + assumption.
  Qed.

  (* This suggests that this should be the actual definition.
     ->+ = ->*.->
   *)
  Lemma cored_red_trans :
    forall Γ u v w,
      red Σ Γ u v ->
      red1 Σ Γ v w ->
      cored Σ Γ w u.
  Proof.
    intros Γ u v w h1 h2.
    revert w h2. induction h1 using red_rect'; intros w h2.
    - constructor. assumption.
    - eapply cored_trans.
      + eapply IHh1. eassumption.
      + assumption.
  Qed.

  Lemma cored_case :
    forall Γ ind p c c' brs,
      cored Σ Γ c c' ->
      cored Σ Γ (tCase ind p c brs) (tCase ind p c' brs).
  Proof.
    intros Γ ind p c c' brs h.
    revert ind p brs. induction h ; intros ind p brs.
    - constructor. constructor. assumption.
    - eapply cored_trans.
      + eapply IHh.
      + econstructor. assumption.
  Qed.

  Lemma cored_proj :
    forall Γ p c c',
      cored Σ Γ c c' ->
      cored Σ Γ (tProj p c) (tProj p c').
  Proof.
    intros Γ p c c' h.
    induction h in p |- *.
    - constructor. constructor. assumption.
    - eapply cored_trans.
      + eapply IHh.
      + econstructor. assumption.
  Qed.
  
  Arguments zip /.

  Lemma welltyped_fill_context_hole Γ π pcontext t :
    wf_local Σ (Γ,,, stack_context π,,, fill_context_hole pcontext t) ->
    welltyped Σ (Γ,,, stack_context π,,, context_hole_context pcontext) t.
  Proof.
    intros wfl.
    destruct pcontext as ((?&h)&?); simpl in *.
    apply wf_local_app_inv in wfl as (_&wf).
    apply wf_local_rel_app_inv in wf as (wf&_).
    destruct h; depelim wf; simpl in *.
    all: destruct l; econstructor; eauto.
  Qed.

  Lemma compare_decls_conv Γ Γ' : 
    All2 (compare_decls eq eq) Γ Γ' ->
    conv_context Σ Γ Γ'.
  Proof.
    intros.
    induction X; constructor; auto.
    destruct r; constructor; subst; auto; reflexivity.
  Qed.

  Lemma compare_decls_eq_context Γ Γ' : 
    All2 (compare_decls eq eq) Γ Γ' <~>
    eq_context_gen eq eq Γ Γ'.
  Proof.
    split; induction 1; constructor; auto.
  Qed.

  Lemma alpha_eq_inst_case_context Γ Δ pars puinst : 
    All2 (compare_decls eq eq) Γ Δ ->
    All2 (compare_decls eq eq) (inst_case_context pars puinst Γ) (inst_case_context pars puinst Δ).
  Proof.
    intros. rewrite /inst_case_context.
    now eapply alpha_eq_subst_context, alpha_eq_subst_instance.
  Qed.

  Lemma welltyped_context :
    forall Γ t,
      welltyped Σ Γ (zip t) ->
      welltyped Σ (Γ ,,, stack_context (snd t)) (fst t).
  Proof.
    destruct hΣ as [wΣ].
    intros Γ [t π] h. simpl.
    destruct h as [T h].
    induction π in Γ, t, T, h |- *.
    1: { econstructor; eauto. }
    destruct a; simpl in *.
    all: apply IHπ in h as (?&typ).
    all: try apply inversion_App in typ as (?&?&?&?&?&?); auto.
    all: try apply inversion_Proj in typ as (?&?&?&?&?&?&?&?&?); auto.
    all: try apply inversion_Prod in typ as (?&?&?&?&?); auto.
    all: try apply inversion_Lambda in typ as (?&?&?&?&?); auto.
    all: try apply inversion_LetIn in typ as (?&?&?&?&?&?); auto.
    all: try solve [econstructor; eauto].
    - apply inversion_Fix in typ as (?&?&?&?&?&?&?); eauto.
      destruct mfix as ((?&[])&?); simpl in *.
      + eapply All_app in a as (_&a).
        depelim a.
        eauto using isType_welltyped.
      + eapply All_app in a0 as (_&a0).
        depelim a0.
        rewrite fix_context_fix_context_alt in t0.
        rewrite map_app in t0.
        simpl in t0.
        rewrite app_context_assoc.
        econstructor; eauto.
    - apply inversion_CoFix in typ as (?&?&?&?&?&?&?); eauto.
      destruct mfix as ((?&[])&?); simpl in *.
      + eapply All_app in a as (_&a).
        depelim a.
        eauto using isType_welltyped.
      + eapply All_app in a0 as (_&a0).
        depelim a0.
        rewrite fix_context_fix_context_alt in t0.
        rewrite map_app in t0.
        simpl in t0.
        rewrite app_context_assoc.
        econstructor; eauto.
    - apply inversion_Case in typ as (?&?&?&?&[]&?); auto.
      rewrite app_context_assoc.
      destruct p. 
      + apply validity in scrut_ty as (?&typ).
        clear brs_ty.
        apply inversion_mkApps in typ as (?&_&spine); auto; simpl in *.
        clear -spine.
        rewrite -app_assoc -app_comm_cons in spine.
        revert spine; generalize (tSort x3); intros t' spine.
        induction params1 in spine, x4, t' |- *; cbn in *.
        * depelim spine.
          econstructor; eauto.
        * depelim spine; eauto.
      + cbn. exists (tSort ps).
        cbn. move: pret_ty. cbn [fill_predicate_hole preturn].
        move=> Ht.
        cbn [fill_predicate_hole preturn] in predctx.
        eapply context_conversion; tea.
        * unfold predctx in Ht.
          eapply typing_wf_local in scrut_ty.
          eapply wf_inst_case_context; tea.
          ** cbn in ind_inst.
             unshelve epose proof (ctx_inst_spine_subst _ ind_inst).
             { eapply weaken_wf_local; tea.
               eapply (on_minductive_wf_params_indices_inst x1); tas. }
              move: X. generalize (ctx_inst_sub ind_inst).
              intros l.
              rewrite subst_instance_app => X.
              unshelve epose proof (spine_subst_app_inv _ X) as [sp _].
              { rewrite (wf_predicate_length_pars wf_pred). len.
                eapply (PCUICClosed.declared_minductive_ind_npars x1). }
              now eapply spine_subst_smash in sp.
          ** cbn in conv_pctx.
             eapply wf_local_app_inv. eapply wf_local_alpha.
             ++ instantiate (1 := (Γ,,, stack_context π,,, smash_context [] (ind_params x)@[puinst],,, (ind_predicate_context ci x x0)@[puinst])).
                eapply All2_app => //.
                { eapply alpha_eq_subst_instance. now symmetry. }
                reflexivity.
             ++ eapply wf_ind_predicate; tea.
                
        * rewrite /predctx.
          cbn in conv_pctx.
          rewrite /case_predicate_context /= /case_predicate_context_gen.
          rewrite /pre_case_predicate_context_gen.
          rewrite /inst_case_context.
          apply compare_decls_conv.
          eapply All2_app. 2:{ reflexivity. }
          eapply compare_decls_eq_context. 
          apply (PCUICAlpha.inst_case_predicate_context_eq (ind:=ci) wf_pred).
          cbn. apply compare_decls_eq_context. now symmetry.
          
    - apply inversion_Case in typ as (?&?&?&?&[]&?); auto.
      econstructor; eauto.
    - apply inversion_Case in typ as (?&?&?&?&[]&?); auto.
      destruct brs as ((?&?)&?).
      simpl fill_branches_hole in brs_ty.
      destruct b; cbn in *.
      set (br := {| bcontext := bcontext; bbody := t |}) in *.
      apply All2i_app_inv_r in brs_ty as (?&?&?&?&a).
      eapply All2i_length in a0.
      depelim a. clear a.
      destruct p0 as (wfl&(cc&typ&r)). clear r.
      rewrite -app_assoc.
      eexists.
      apply typing_wf_local in scrut_ty.
      eapply context_conversion; tea.
      * eapply wf_inst_case_context; tea.
        ** unshelve epose proof (ctx_inst_spine_subst _ ind_inst).
          { eapply weaken_wf_local; tea.
            eapply (on_minductive_wf_params_indices_inst x1); tas. }
          move: X. generalize (ctx_inst_sub ind_inst) => l'.
          rewrite subst_instance_app => X.
          unshelve epose proof (spine_subst_app_inv _ X) as [sp _].
          { rewrite (wf_predicate_length_pars wf_pred). len.
            eapply (PCUICClosed.declared_minductive_ind_npars x1). }
          now eapply spine_subst_smash in sp.
        ** eapply wf_local_app_inv. eapply wf_local_alpha.
          ++ instantiate (1 := (Γ,,, stack_context π,,, smash_context [] (ind_params x)@[puinst p],,, 
                (cstr_branch_context ci x x5)@[puinst p])).
            eapply All2_app => //.
            { eapply alpha_eq_subst_instance. now symmetry. }
            reflexivity.
          ++ eapply typing_wf_local in typ. simpl in typ.
            rewrite /cstr_branch_context.
            rewrite subst_instance_expand_lets_ctx.
            eapply wf_local_expand_lets.
            set (brs := l ++ {| bcontext := bcontext; bbody := t |} :: l0) in *.
            unshelve epose proof (wf_case_branches_types' ps x2 brs x1 _ wf_pred pret_ty wf_brs conv_pctx).
            { eexists; red. eapply type_mkApps. 1:{ econstructor; eauto. }
              rewrite (declared_inductive_type x1).
              eapply wf_arity_spine_typing_spine.
              split. { rewrite -(declared_inductive_type x1). eapply (declared_inductive_valid_type x1); tas. }
              rewrite subst_instance_it_mkProd_or_LetIn.
              eapply arity_spine_it_mkProd_or_LetIn_Sort; tas.
              { eapply (on_inductive_sort_inst x1); tea. }
              { reflexivity. }
              unshelve eapply (ctx_inst_spine_subst _ ind_inst).
              eapply weaken_wf_local; tea. now eapply (on_minductive_wf_params_indices_inst x1). }
            rewrite e0 in X.
            assert (nth_error (x3 ++ x5 :: l1) #|x3| = Some x5).
            { rewrite nth_error_app_ge // Nat.sub_diag //. }
            eapply All2i_nth_error in X; tea.
            2:{ rewrite a0 /brs nth_error_app_ge // Nat.sub_diag /= //. }
            cbn in X. destruct X as [wfbr wfctx wfictx _].
            rewrite /case_branch_context_nopars /= /case_branch_type /= in wfctx.
            eapply wf_local_alpha; tea. eapply All2_app => //. 2:reflexivity.
            rewrite subst_instance_subst_context subst_instance_inds.
            rewrite (subst_instance_id_mdecl _ _ _ cons).
            eapply eq_binder_annots_eq.
            apply All2_eq_binder_subst_context, All2_eq_binder_subst_instance.
            now eapply Forall2_All2.
          * rewrite /case_branch_context_gen.
            apply compare_decls_conv, All2_app => //. 2:reflexivity.
            etransitivity; [eapply eq_binder_annots_eq|].
            { eapply wf_pre_case_branch_context_gen; tea.
              red in wf_brs. eapply Forall2_All2 in wf_brs. move: wf_brs.
              rewrite e0. move/(All2_app_inv _ _ _ _ _ _ _ a0) => [] _ H.
              now depelim H. }
            symmetry. 
            rewrite /pre_case_branch_context_gen.
            now apply alpha_eq_inst_case_context.
  Qed.

  Lemma cored_red :
    forall Γ u v,
      cored Σ Γ v u ->
      ∥ red Σ Γ u v ∥.
  Proof.
    intros Γ u v h.
    induction h.
    - constructor. now constructor.
    - destruct IHh as [r].
      constructor. etransitivity; eauto.
  Qed.

  Lemma cored_context :
    forall Γ t u π,
      cored Σ (Γ ,,, stack_context π) t u ->
      cored Σ Γ (zip (t, π)) (zip (u, π)).
  Proof.
    intros Γ t u π h. induction h.
    - constructor. eapply red1_context. assumption.
    - eapply cored_trans.
      + eapply IHh.
      + eapply red1_context. assumption.
  Qed.

  Lemma decompose_stack_closed n ρ l s : 
    closedn_stack n ρ -> decompose_stack ρ = (l, s) ->
    forallb (closedn (n + #|stack_context ρ|)) l.
  Proof.
    induction ρ in l, s |- *; cbn.
    - now intros _ [= <- <-].
    - move/andP=> [cla clρ].
      destruct a ; [idtac|intros [= <- <-]..] => //.
      destruct decompose_stack eqn:ds.
      intros [= <- <-].
      specialize (IHρ _ _ clρ eq_refl).
      cbn in cla |- *.
      now rewrite IHρ cla.
  Qed.

  (* Ill-scoped, if the stack has a context *)
  (*Lemma conv_zipp :
    forall Γ u v ρ,
      closedn_stack #|Γ| ρ ->
      Σ ;;; Γ ⊢ u = v ->
      Σ ;;; Γ ⊢ zipp u ρ = zipp v ρ.
  Proof.
    intros Γ u v ρ cl h.
    unfold zipp.
    destruct decompose_stack eqn:da.
    induction l in u, v, cl, h, da |- *.
    - assumption.
    - simpl. eapply IHl => //.
      * eapply equality_App_l; tas.
        eapply decompose_stack_closed in da; tea.
        move: da => /= /andP[].
  Qed.*)

  (* Lemma cumul_zipp :
    forall Γ u v π,
      Σ ;;; Γ |- u <= v ->
      Σ ;;; Γ |- zipp u π <= zipp v π.
  Proof.
    intros Γ u v π h.
    unfold zipp.
    destruct decompose_stack as [l ρ].
    induction l in u, v, h |- *.
    - assumption.
    - simpl.  eapply IHl. eapply cumul_App_l. assumption.
  Qed. *)

  Derive Signature for Acc.

  Lemma wf_fun :
    forall A (R : A -> A -> Prop) B (f : B -> A),
      well_founded R ->
      well_founded (fun x y => R (f x) (f y)).
  Proof.
    intros A R B f h x.
    specialize (h (f x)).
    dependent induction h.
    constructor. intros y h.
    eapply H0 ; try reflexivity. assumption.
  Qed.

  Lemma Acc_fun :
    forall A (R : A -> A -> Prop) B (f : B -> A) x,
      Acc R (f x) ->
      Acc (fun x y => R (f x) (f y)) x.
  Proof.
    intros A R B f x h.
    dependent induction h.
    constructor. intros y h.
    eapply H0 ; try reflexivity. assumption.
  Qed.

  (* TODO Put more general lemma in Inversion *)
  Lemma welltyped_it_mkLambda_or_LetIn :
    forall Γ Δ t,
      welltyped Σ Γ (it_mkLambda_or_LetIn Δ t) ->
      welltyped Σ (Γ ,,, Δ) t.
  Proof.
    destruct hΣ as [wΣ].
    intros Γ Δ t h.
    induction Δ as [| [na [b|] A] Δ ih ] in Γ, t, h |- *.
    - assumption.
    - simpl. apply ih in h. cbn in h.
      destruct h as [T h].
      apply inversion_LetIn in h as hh ; auto.
      destruct hh as [s1 [A' [? [? [? ?]]]]].
      exists A'. assumption.
    - simpl. apply ih in h. cbn in h.
      destruct h as [T h].
      apply inversion_Lambda in h as hh ; auto.
      pose proof hh as [s1 [B [? [? ?]]]].
      exists B. assumption.
  Qed.

  Lemma it_mkLambda_or_LetIn_welltyped :
    forall Γ Δ t,
      welltyped Σ (Γ ,,, Δ) t ->
      welltyped Σ Γ (it_mkLambda_or_LetIn Δ t).
  Proof.
    intros Γ Δ t [T h].
    eexists. eapply PCUICGeneration.type_it_mkLambda_or_LetIn.
    eassumption.
  Qed.

  Lemma welltyped_it_mkLambda_or_LetIn_iff :
    forall Γ Δ t,
      welltyped Σ Γ (it_mkLambda_or_LetIn Δ t) <->
      welltyped Σ (Γ ,,, Δ) t.
  Proof.
    intros. split.
    - apply welltyped_it_mkLambda_or_LetIn.
    - apply it_mkLambda_or_LetIn_welltyped.
  Qed.

  Lemma welltyped_zipx :
    forall {Γ t π},
      welltyped Σ [] (zipx Γ t π) ->
      welltyped Σ Γ (zipc t π).
  Proof.
    intros Γ t π h.
    apply welltyped_it_mkLambda_or_LetIn in h.
    rewrite app_context_nil_l in h.
    assumption.
  Qed.

  Lemma welltyped_zipc_stack_context Γ t π ρ args
    : decompose_stack π = (args, ρ)
      -> welltyped Σ Γ (zipc t π)
      -> welltyped Σ (Γ ,,, stack_context π) (zipc t (appstack args [])).
  Proof.
    intros h h1.
    apply decompose_stack_eq in h. subst.
    rewrite stack_context_appstack.
    induction args in Γ, t, ρ, h1 |- *.
    - cbn in *.
      now apply (welltyped_context Γ (t, ρ)).
    - simpl. eauto.
  Qed.

  Lemma red_const :
    forall {Γ c u cty cb cu},
      Some (ConstantDecl {| cst_type := cty ; cst_body := Some cb ; cst_universes := cu |})
      = lookup_env Σ c ->
      red (fst Σ) Γ (tConst c u) (subst_instance u cb).
  Proof.
    intros Γ c u cty cb cu e.
    econstructor. econstructor.
    - symmetry in e. exact e.
    - reflexivity.
  Qed.

  Lemma cored_const :
    forall {Γ c u cty cb cu},
      Some (ConstantDecl {| cst_type := cty ; cst_body := Some cb ; cst_universes := cu |})
      = lookup_env Σ c ->
      cored (fst Σ) Γ (subst_instance u cb) (tConst c u).
  Proof.
    intros Γ c u cty cb cu e.
    symmetry in e.
    econstructor.
    econstructor.
    - exact e.
    - reflexivity.
  Qed.

  Derive Signature for cumul.
  Derive Signature for red1.

  Lemma app_cored_r :
    forall Γ u v1 v2,
      cored Σ Γ v1 v2 ->
      cored Σ Γ (tApp u v1) (tApp u v2).
  Proof.
    intros Γ u v1 v2 h.
    induction h.
    - constructor. constructor. assumption.
    - eapply cored_trans.
      + eapply IHh.
      + constructor. assumption.
  Qed.

  Fixpoint isAppProd (t : term) : bool :=
    match t with
    | tApp t l => isAppProd t
    | tProd na A B => true
    | _ => false
    end.

  Lemma isAppProd_mkApps :
    forall t l, isAppProd (mkApps t l) = isAppProd t.
  Proof.
    intros t l. revert t.
    induction l ; intros t.
    - reflexivity.
    - cbn. rewrite IHl. reflexivity.
  Qed.

  Lemma isProdmkApps :
    forall t l,
      isProd (mkApps t l) ->
      l = [].
  Proof.
    intros t l h.
    revert t h.
    induction l ; intros t h.
    - reflexivity.
    - cbn in h. specialize IHl with (1 := h). subst.
      cbn in h. discriminate h.
  Qed.

  Lemma isSortmkApps :
    forall t l,
      isSort (mkApps t l) ->
      l = [].
  Proof.
    intros t l h.
    revert t h.
    induction l ; intros t h.
    - reflexivity.
    - cbn in h. specialize IHl with (1 := h). subst.
      cbn in h. exfalso. discriminate.
  Qed.

  Lemma isAppProd_isProd :
    forall Γ t,
      isAppProd t ->
      welltyped Σ Γ t ->
      isProd t.
  Proof.
    destruct hΣ as [wΣ].
    intros Γ t hp hw.
    induction t in Γ, hp, hw |- *.
    all: try discriminate hp.
    - reflexivity.
    - simpl in hp.
      specialize IHt1 with (1 := hp).
      assert (welltyped Σ Γ t1) as h.
      { destruct hw as [T h].
        apply inversion_App in h as hh ; auto.
        destruct hh as [na [A' [B' [? [? ?]]]]].
        eexists. eassumption.
      }
      specialize IHt1 with (1 := h).
      destruct t1.
      all: try discriminate IHt1.
      destruct hw as [T hw'].
      apply inversion_App in hw' as ihw' ; auto.
      destruct ihw' as [na' [A' [B' [hP [? ?]]]]].
      apply inversion_Prod in hP as [s1 [s2 [? [? bot]]]] ; auto.
      apply equality_Sort_Prod_inv in bot ; auto.
  Qed.

  Lemma mkApps_Prod_nil :
    forall Γ na A B l,
      welltyped Σ Γ (mkApps (tProd na A B) l) ->
      l = [].
  Proof.
    intros Γ na A B l h.
    pose proof (isAppProd_isProd) as hh.
    specialize hh with (2 := h).
    rewrite isAppProd_mkApps in hh.
    specialize hh with (1 := eq_refl).
    apply isProdmkApps in hh. assumption.
  Qed.


  (* TODO MOVE or even replace old lemma *)
  Lemma decompose_stack_noStackApp :
    forall π l ρ,
      decompose_stack π = (l,ρ) ->
      isStackApp ρ = false.
  Proof.
    intros π l ρ e.
    destruct ρ; auto.
    destruct s.
    all: auto.
    exfalso. eapply decompose_stack_not_app. eassumption.
  Qed.
  
  (* TODO MOVE *)
  Lemma stack_context_decompose :
    forall π,
      stack_context (snd (decompose_stack π)) = stack_context π.
  Proof.
    intros π.
    case_eq (decompose_stack π). intros l ρ e.
    cbn. pose proof (decompose_stack_eq _ _ _ e). subst.
    rewrite stack_context_appstack. reflexivity.
  Qed.
  
  Lemma decompose_stack_stack_cat π π' :
    decompose_stack (π ++ π') =
    ((decompose_stack π).1 ++
     match (decompose_stack π).2 with
     | [] => (decompose_stack π').1
     | _ => []
     end,
     (decompose_stack π).2 ++
     match (decompose_stack π).2 with
     | [] => (decompose_stack π').2
     | _ => π'
     end).
  Proof.
    induction π in π' |- *; cbn in *; auto.
    - now destruct decompose_stack.
    - destruct a; auto.
      rewrite !IHπ.
      now destruct (decompose_stack π).
  Qed.

  Lemma zipp_stack_cat π π' t :
    isStackApp π = false ->
    zipp t (π' ++ π) = zipp t π'.
  Proof.
    intros no_stack_app.
    unfold zipp.
    rewrite decompose_stack_stack_cat.
    destruct (decompose_stack π') eqn:decomp.
    cbn.
    destruct s; try now rewrite app_nil_r.
    now destruct π as [|[] ?]; cbn in *; rewrite ?app_nil_r.
  Qed.
  
  Lemma zipp_appstack t args π :
    zipp t (appstack args π) = zipp (mkApps t args) π.
  Proof.
    unfold zipp.
    rewrite decompose_stack_appstack.
    rewrite <- mkApps_nested.
    now destruct decompose_stack.
  Qed.

  Lemma fst_decompose_stack_nil π :
    isStackApp π = false ->
    (decompose_stack π).1 = [].
  Proof. now destruct π as [|[] ?]. Qed.
  
  Lemma zipp_as_mkApps t π :
    zipp t π = mkApps t (decompose_stack π).1.
  Proof.
    unfold zipp.
    now destruct decompose_stack.
  Qed.
  
  Lemma zipp_noStackApp t π :
    isStackApp π = false ->
    zipp t π = t.
  Proof.
    intros.
    now rewrite zipp_as_mkApps fst_decompose_stack_nil.
  Qed.
  
  Lemma it_mkLambda_or_LetIn_inj :
    forall Γ u v,
      it_mkLambda_or_LetIn Γ u =
      it_mkLambda_or_LetIn Γ v ->
      u = v.
  Proof.
    intros Γ u v e.
    revert u v e.
    induction Γ as [| [na [b|] A] Γ ih ] ; intros u v e.
    - assumption.
    - simpl in e. cbn in e.
      apply ih in e.
      inversion e. reflexivity.
    - simpl in e. cbn in e.
      apply ih in e.
      inversion e. reflexivity.
  Qed.

  Hint Resolve conv_refl conv_alt_red : core.
  Hint Resolve conv_refl : core.

  Lemma cored_red_cored :
    forall Γ u v w,
      cored Σ Γ w v ->
      red Σ Γ u v ->
      cored Σ Γ w u.
  Proof.
    intros Γ u v w h1 h2.
    revert u h2. induction h1 ; intros t h2.
    - eapply cored_red_trans ; eassumption.
    - eapply cored_trans.
      + eapply IHh1. assumption.
      + assumption.
  Qed.

  Lemma red_neq_cored :
    forall Γ u v,
      red Σ Γ u v ->
      u <> v ->
      cored Σ Γ v u.
  Proof.
    intros Γ u v r n.
    destruct r using red_rect'.
    - exfalso. apply n. reflexivity.
    - eapply cored_red_cored ; try eassumption.
      constructor. assumption.
  Qed.

  Lemma red_welltyped :
    forall {Γ u v},
      welltyped Σ Γ u ->
      ∥ red (fst Σ) Γ u v ∥ ->
      welltyped Σ Γ v.
  Proof.
    destruct hΣ as [wΣ]; clear hΣ.
    intros Γ u v h [r].
    revert h. induction r using red_rect' ; intros h.
    - assumption.
    - specialize IHr with (1 := ltac:(eassumption)).
      destruct IHr as [A ?]. exists A.
      eapply subject_reduction1 ; eauto with wf.
  Qed.

  Lemma red_cored_cored :
    forall Γ u v w,
      red Σ Γ v w ->
      cored Σ Γ v u ->
      cored Σ Γ w u.
  Proof.
    intros Γ u v w h1 h2.
    revert u h2. induction h1 using red_rect' ; intros t h2.
    - assumption.
    - eapply cored_trans.
      + eapply IHh1. assumption.
      + assumption.
  Qed.

  Lemma Proj_red_cond :
    forall Γ i pars narg i' c u l,
      welltyped Σ Γ (tProj (i, pars, narg) (mkApps (tConstruct i' c u) l)) ->
      nth_error l (pars + narg) <> None.
  Proof.
    intros Γ i pars narg i' c u l [T h].
    apply PCUICInductiveInversion.invert_Proj_Construct in h as (<-&->&?); auto.
    now apply nth_error_Some.
  Qed.

  Lemma cored_zipc :
    forall Γ t u π,
      cored Σ (Γ ,,, stack_context π) t u ->
      cored Σ Γ (zipc t π) (zipc u π).
  Proof.
    intros Γ t u π h.
    do 2 zip fold. eapply cored_context. assumption.
  Qed.

  Lemma red_zipc :
    forall Γ t u π,
      red Σ (Γ ,,, stack_context π) t u ->
      red Σ Γ (zipc t π) (zipc u π).
  Proof.
    intros Γ t u π h.
    do 2 zip fold. eapply red_context_zip. assumption.
  Qed.

  Lemma welltyped_zipc_zipp :
    forall Γ t π,
      welltyped Σ Γ (zipc t π) ->
      welltyped Σ (Γ ,,, stack_context π) (zipp t π).
  Proof.
    intros Γ t π h.
    unfold zipp.
    case_eq (decompose_stack π). intros l ρ e.
    pose proof (decompose_stack_eq _ _ _ e). subst. clear e.
    rewrite zipc_appstack in h.
    zip fold in h.
    apply welltyped_context in h. simpl in h.
    rewrite stack_context_appstack.
    assumption.
  Qed.
  
  Lemma conv_cum_zipp leq Γ t t' π π' :
    Σ ;;; Γ ⊢ t ≤[leq] t' ->
    ∥equality_terms Σ Γ (decompose_stack π).1 (decompose_stack π').1∥ ->
    ∥Σ ;;; Γ ⊢ zipp t π ≤[leq] zipp t' π'∥.
  Proof.
    intros conv conv_args.
    rewrite !zipp_as_mkApps.
    sq.
    eapply equality_mkApps; auto.
  Qed.

  Lemma whne_All2_fold f rel Γ Γ' t :
    (forall Γ Γ' c c', rel Γ Γ' c c' -> (decl_body c = None <-> decl_body c' = None)) ->
    whne f Σ Γ t ->
    All2_fold rel Γ Γ' ->
    whne f Σ Γ' t.
  Proof.
    intros behaves wh conv.
    induction wh; eauto using whne.
    destruct nth_error eqn:nth; [|easy].
    cbn in *.
    eapply All2_fold_nth in nth; eauto.
    destruct nth as (?&eq&?&?).
    constructor.
    rewrite eq.
    cbn.
    specialize (behaves _ _ _ _ r).
    f_equal.
    apply behaves.
    congruence.
  Qed.

  Lemma whnf_All2_fold f rel Γ Γ' t :
    (forall Γ Γ' c c', rel Γ Γ' c c' -> (decl_body c = None <-> decl_body c' = None)) ->
    whnf f Σ Γ t ->
    All2_fold rel Γ Γ' ->
    whnf f Σ Γ' t.
  Proof.
    intros behaves wh conv.
    destruct wh; eauto using whnf.
    apply whnf_ne.
    eapply whne_All2_fold; eauto.
  Qed.

  Lemma whne_conv_context f Γ Γ' t :
    whne f Σ Γ t ->
    conv_context Σ Γ Γ' ->
    whne f Σ Γ' t.
  Proof.
    apply whne_All2_fold.
    intros ? ? ? ? r.
    now depelim r.
  Qed.

  Lemma whnf_conv_context f Γ Γ' t :
    whnf f Σ Γ t ->
    conv_context Σ Γ Γ' ->
    whnf f Σ Γ' t.
  Proof.
    apply whnf_All2_fold.
    intros ? ? ? ? r.
    now depelim r.
  Qed.

  Lemma Case_Construct_ind_eq :
    forall {Γ ci ind' pred i u brs args},
      welltyped Σ Γ (tCase ci pred (mkApps (tConstruct ind' i u) args) brs) ->
      ci.(ci_ind) = ind'.
  Proof.
    destruct hΣ as [wΣ].
    intros Γ ci ind' pred i u brs args [A h].
    apply PCUICInductiveInversion.invert_Case_Construct in h; intuition auto.
  Qed.

  Lemma Proj_Construct_ind_eq :
    forall Γ i i' pars narg c u l,
      welltyped Σ Γ (tProj (i, pars, narg) (mkApps (tConstruct i' c u) l)) ->
      i = i'.
  Proof.
    destruct hΣ as [wΣ].
    intros Γ i i' pars narg c u l [T h].
    now apply PCUICInductiveInversion.invert_Proj_Construct in h.
  Qed.
  
End Lemmata.

Hint Resolve isType_welltyped : pcuic.
