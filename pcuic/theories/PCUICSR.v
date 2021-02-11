(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICUtils
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICWeakeningEnv PCUICWeakening
     PCUICSubstitution PCUICClosed PCUICCumulativity PCUICGeneration PCUICReduction
     PCUICAlpha PCUICEquality PCUICValidity PCUICParallelReductionConfluence
     PCUICConfluence PCUICContextConversion PCUICUnivSubstitution
     PCUICConversion PCUICInversion PCUICContexts PCUICArities
     PCUICParallelReduction PCUICSpine PCUICInductives PCUICInductiveInversion.

Require Import ssreflect.
From Equations Require Import Equations.
From Equations.Type Require Import Relation Relation_Properties.
Require Import Equations.Prop.DepElim.
Local Set SimplIsCbn.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

Derive Signature for OnOne2_local_env.

Ltac rename_hyp h ht ::= my_rename_hyp h ht.
Ltac pcuic := intuition eauto 3 with pcuic ||
  (try solve [repeat red; cbn in *; intuition auto; eauto 3 with pcuic || (try lia || congruence)]).

Arguments Nat.sub : simpl nomatch.
Arguments Universe.sort_of_product : simpl nomatch.
Hint Rewrite subst_instance_assumptions : len.
Hint Rewrite projs_length : len.

(** The subject reduction property of the system: *)

Definition SR_red1 {cf} Σ Γ t T :=
  forall u (Hu : red1 Σ Γ t u), Σ ;;; Γ |- u : T.

(* Preservation of wf_*fixpoint *)  

Lemma wf_fixpoint_red1_type {cf Σ} {wfΣ : wf Σ} Γ mfix mfix1 : 
  wf_fixpoint Σ mfix ->
  OnOne2
  (fun x y : def term =>
   red1 Σ Γ (dtype x) (dtype y)
   × (dname x, dbody x, rarg x) = (dname y, dbody y, rarg y)) mfix mfix1 ->
  wf_fixpoint Σ mfix1.
Proof.
  intros wffix o.
  move: wffix; unfold wf_fixpoint.
  enough (forall inds, map_option_out (map check_one_fix mfix) = Some inds ->
     map_option_out (map check_one_fix mfix1) = Some inds) => //.
  destruct map_option_out. now specialize (H _ eq_refl) as ->.
  discriminate.
  induction o; intros inds.
  - simpl.
    destruct p as [redty eqs].
    destruct hd as [dname dtype dbody rarg], hd' as [dname' dtype' dbody' rarg'].
    simpl in *.
    noconf eqs.
    destruct (decompose_prod_assum [] dtype) eqn:decomp.
    destruct nth_error eqn:Hnth.
    apply decompose_prod_assum_it_mkProd_or_LetIn in decomp.
    simpl in decomp.
    subst dtype.
    destruct (red1_it_mkProd_or_LetIn_smash _ _ _ _ _ _ _ wfΣ redty Hnth) as 
      (ctx & t' & decomp & d & [hnth di]).
    rewrite decomp hnth.
    unfold head in di. destruct decompose_app; simpl in *.
    destruct destInd as [[ind u]|]; try discriminate.
    destruct decompose_app. simpl in di. rewrite di. auto.
    discriminate.
  - simpl map.
    simpl map_option_out.
    destruct check_one_fix => //.
    destruct map_option_out. specialize (IHo _ eq_refl).
    move=> [= <-]. now rewrite IHo.
    discriminate.
Qed.

Lemma wf_fixpoint_red1_body {cf Σ} {wfΣ : wf Σ} Γ mfix mfix1 : 
  wf_fixpoint Σ mfix ->
  OnOne2
  (fun x y : def term =>
   red1 Σ Γ (dbody x) (dbody y)
   × (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)) mfix mfix1 ->
  wf_fixpoint Σ mfix1.
Proof.
  intros wffix o.
  move: wffix; unfold wf_fixpoint.
  enough (map check_one_fix mfix = map check_one_fix mfix1) as -> => //.
  induction o.
  - simpl. f_equal.
    destruct p as [redty eqs].
    destruct hd as [dname dtype dbody rarg], hd' as [dname' dtype' dbody' rarg'].
    simpl in *.
    noconf eqs. reflexivity.
  - simpl. now rewrite IHo.
Qed.

Lemma wf_cofixpoint_red1_type {cf:checker_flags} (Σ : global_env_ext) Γ mfix mfix1 : 
  wf Σ.1 ->
  wf_cofixpoint Σ.1 mfix ->
  OnOne2
  (fun x y : def term =>
   red1 Σ Γ (dtype x) (dtype y)
   × (dname x, dbody x, rarg x) = (dname y, dbody y, rarg y)) mfix mfix1 ->
  wf_cofixpoint Σ.1 mfix1.
Proof.
  intros wfΣ wffix o.
  move: wffix; unfold wf_cofixpoint.
  enough (forall inds, map_option_out (map check_one_cofix mfix) = Some inds ->
     map_option_out (map check_one_cofix mfix1) = Some inds) => //.
  destruct map_option_out. now specialize (H _ eq_refl) as ->.
  discriminate.
  induction o; intros inds.
  - simpl.
    destruct p as [redty eqs].
    destruct hd as [dname dtype dbody rarg], hd' as [dname' dtype' dbody' rarg'].
    simpl in *.
    noconf eqs.
    destruct (decompose_prod_assum [] dtype) eqn:decomp.
    apply decompose_prod_assum_it_mkProd_or_LetIn in decomp.
    simpl in decomp.
    subst dtype.
    eapply red1_red in redty.
    destruct (decompose_app t) as [f l] eqn:decomp.
    destruct f; try discriminate. simpl.
    apply decompose_app_inv in decomp. subst t.
    eapply red_it_mkProd_or_LetIn_mkApps_Ind in redty as [ctx' [args' ->]]; auto.
    erewrite decompose_prod_assum_it_mkProd => //.
    2:{ now rewrite is_ind_app_head_mkApps. }
    rewrite decompose_app_mkApps => //.
  - simpl map.
    simpl map_option_out.
    destruct check_one_cofix => //.
    destruct map_option_out. specialize (IHo _ eq_refl).
    move=> [= <-]. now rewrite IHo.
    discriminate.
Qed.

Lemma wf_cofixpoint_red1_body {cf:checker_flags} (Σ : global_env_ext) Γ mfix mfix1 : 
  wf Σ.1 ->
  wf_cofixpoint Σ.1 mfix ->
  OnOne2
  (fun x y : def term =>
   red1 Σ Γ (dbody x) (dbody y)
   × (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)) mfix mfix1 ->
  wf_cofixpoint Σ.1 mfix1.
Proof.
  intros wfΣ wffix o.
  move: wffix; unfold wf_cofixpoint.
  enough (map check_one_cofix mfix = map check_one_cofix mfix1) as -> => //.
  induction o.
  - simpl. f_equal.
    destruct p as [redty eqs].
    destruct hd as [dname dtype dbody rarg], hd' as [dname' dtype' dbody' rarg'].
    simpl in *.
    noconf eqs. reflexivity.
  - simpl. now rewrite IHo.
Qed.

Hint Extern 0 (conv_decls _ _ _ _ _) => constructor : pcuic.
Hint Extern 0 (cumul_decls _ _ _ _ _) => constructor : pcuic.
Hint Extern 0 (conv_context _ _ _) => constructor : pcuic.
Hint Extern 0 (cumul_context _ _ _) => constructor : pcuic.

Hint Extern 4 (∑ s : Universe.t, typing _ _ ?T (tSort s)) => 
  match goal with 
  | [ H : isType _ _ T |- _ ] => exact H
  end : pcuic.

Ltac unfold_pcuic := 
  progress (unfold lift_typing, PCUICConversionPar.conv, PCUICConversionPar.cumul, PCUICTypingDef.typing,
  PCUICTypingDef.wf_universe in * ).
Hint Extern 10 => unfold_pcuic : pcuic.

Hint Resolve red_conv red1_red red_cumul : pcuic.
Hint Transparent global_env_ext : pcuic.
Hint Constructors All_local_env All2_fold : pcuic.
Ltac pcuics := try typeclasses eauto with pcuic.

Lemma declared_projection_declared_constructor {cf}
  {Σ} {wfΣ : wf Σ} {i pars narg mdecl mdecl' idecl idecl' pdecl cdecl} :
  declared_projection Σ (i, pars, narg) mdecl idecl pdecl ->
  declared_constructor Σ (i, 0) mdecl' idecl' cdecl -> 
  mdecl = mdecl' /\ idecl = idecl'.
Proof.
  intros [] [].
  pose proof (declared_inductive_inj H H1). intuition auto.
Qed.

Ltac hide H :=
  match type of H with
  | ?ty => change ty with (@hidebody _ ty) in H
  end.

Lemma All2i_nth_error {A B} {P : nat -> A -> B -> Type} {l l' n x c k} : 
  All2i P k l l' ->
  nth_error l n = Some x ->
  nth_error l' n = Some c ->
  P (k + n)%nat x c.
Proof.
  induction 1 in n |- *.
  * rewrite !nth_error_nil => //.
  * destruct n.
    + simpl. intros [= <-] [= <-]. now rewrite Nat.add_0_r.
    + simpl. intros hnth hnth'. specialize (IHX _ hnth hnth').
      now rewrite Nat.add_succ_r.
Qed.
From MetaCoq.PCUIC Require Import PCUICSigmaCalculus.

Lemma conv_context_smash_end {cf Σ} {wfΣ : wf Σ} (Γ Δ Δ' : context) : 
  wf_local Σ (Γ ,,, Δ) ->
  wf_local Σ (Γ ,,, Δ') ->
  conv_context Σ (Γ ,,, Δ) (Γ ,,, Δ') ->
  conv_context Σ (Γ ,,, smash_context [] Δ) (Γ ,,, smash_context [] Δ').
Proof.
  intros wf wf' cv.
  eapply conv_context_app.
  apply conv_context_rel_app in cv.
  eapply conv_ctx_rel_smash => //.
Qed.

Lemma case_branch_type_fst ci mdecl idecl p br ptm c cdecl :
  (case_branch_type ci mdecl idecl p br ptm c cdecl).1 = 
  (case_branch_context ci mdecl p (forget_types br.(bcontext)) cdecl).
Proof. reflexivity. Qed.

Lemma expand_lets_eq Γ t : 
  expand_lets Γ t = 
  subst0 (extended_subst Γ 0) (lift (context_assumptions Γ) #|Γ| t).
Proof.
  rewrite /expand_lets /expand_lets_k /= //.
Qed.

Lemma expand_lets_eq_map Γ l : 
  map (expand_lets Γ) l = 
  map (subst0 (extended_subst Γ 0)) (map (lift (context_assumptions Γ) #|Γ|) l).
Proof.
  rewrite /expand_lets /expand_lets_k /= map_map_compose //.
Qed.

Lemma map_expand_lets_to_extended_list Γ : 
  map (expand_lets Γ) (to_extended_list Γ) = to_extended_list (smash_context [] Γ).
Proof.
  now rewrite expand_lets_eq_map map_subst_extended_subst_lift_to_extended_list_k.
Qed.

Lemma conv_context_rel_reln {cf} {Σ} Γ Δ Δ' : 
  conv_context_rel Σ Γ Δ Δ' ->
  forall acc n, reln acc n Δ = reln acc n Δ'.
Proof.
  induction 1.
  - constructor.
  - intros acc n; destruct p; simpl; auto.
Qed.
    
Lemma conv_context_rel_to_extended_list {cf} {Σ} Γ Δ Δ' : 
  conv_context_rel Σ Γ Δ Δ' ->
  to_extended_list Δ = to_extended_list Δ'.
Proof.
  unfold to_extended_list, to_extended_list_k.
  intros; now eapply conv_context_rel_reln.
Qed.

Lemma eq_context_alpha_conv {cf} {Σ} Γ Δ Δ' : 
  All2 (compare_decls eq eq) Δ Δ' ->
  conv_context_rel Σ Γ Δ Δ'.
Proof.
  induction 1.
  - constructor.
  - destruct r; repeat constructor; subst; auto; reflexivity.
Qed.

Lemma eq_context_alpha_reln Δ Δ' : 
  All2 (compare_decls eq eq) Δ Δ' ->
  forall acc n, reln acc n Δ = reln acc n Δ'.
Proof.
  induction 1.
  - constructor.
  - intros acc n; destruct r; simpl; auto.
Qed.

Lemma eq_context_alpha_to_extended_list Δ Δ' : 
  All2 (compare_decls eq eq) Δ Δ' ->
  to_extended_list Δ = to_extended_list Δ'.
Proof.
  unfold to_extended_list, to_extended_list_k.
  intros; now eapply eq_context_alpha_reln.
Qed.

Lemma eq_binder_annots_eq nas Γ : 
  All2 (fun x y => eq_binder_annot x y.(decl_name)) nas Γ ->
  All2 (compare_decls eq eq) (map2 set_binder_name nas Γ) Γ.
Proof.
  induction 1; simpl; constructor; auto.
  destruct x, y as [na [b|] ty]; simpl; constructor; auto.
Qed.

Lemma to_extended_list_case_branch_context ci mdecl p brctx cdecl :
  All2 (fun x y => eq_binder_annot x y.(decl_name)) brctx (cstr_args cdecl) ->
  to_extended_list (case_branch_context ci mdecl p brctx cdecl) =
  to_extended_list (cstr_args cdecl).
Proof.
  intros hlen.
  rewrite /to_extended_list /case_branch_context /case_branch_context_gen.
  rewrite to_extended_list_k_subst /expand_lets_ctx /expand_lets_k_ctx
    to_extended_list_k_subst to_extended_list_k_lift_context to_extended_list_k_subst
    PCUICLiftSubst.map_subst_instance_to_extended_list_k.
  apply eq_context_alpha_to_extended_list.
  now apply eq_binder_annots_eq.
Qed.

Lemma spine_subst_inst_subst {cf} {Σ} {Γ inst s Δ Δ'} : 
  spine_subst Σ Γ inst s Δ ->
  subst_context s 0 Δ' = subst_context (List.rev inst) 0 (expand_lets_ctx Δ Δ').
Proof.
  intros sp. pose proof (spine_subst_subst_to_extended_list_k sp).
  rewrite -H.
  rewrite /expand_lets_ctx /expand_lets_k_ctx /=.
  rewrite -map_rev.
  rewrite subst_context_subst_context. len.
  rewrite subst_context_lift_context_cancel. now len.
  f_equal.
  rewrite map_rev. rewrite H.
  apply context_subst_subst_extended_subst. apply sp.
Qed.

Lemma spine_subst_inst_subst_term {cf} {Σ} {Γ inst s Δ Δ'} : 
  spine_subst Σ Γ inst s Δ ->
  subst s 0 Δ' = subst (List.rev inst) 0 (expand_lets Δ Δ').
Proof.
  intros sp. pose proof (spine_subst_subst_to_extended_list_k sp).
  rewrite -H.
  rewrite /expand_lets_ctx /expand_lets_k_ctx /=.
  rewrite -map_rev.
  rewrite distr_subst. len.
  rewrite simpl_subst_k. now len.
  f_equal.
  rewrite map_rev. rewrite H.
  apply context_subst_subst_extended_subst. apply sp.
Qed.
 
Lemma subst_context_subst_context s k s' Γ :
  subst_context s k (subst_context s' k Γ) =
  subst_context (map (subst0 s) s') k (subst_context s (k + #|s'|) Γ).
Proof.
  induction Γ as [|[na [b|] ty] Γ']; simpl; auto; 
    rewrite !subst_context_snoc /= /subst_decl /map_decl /=; f_equal; 
    auto; f_equal; len; 
  rewrite -{1}(Nat.add_0_r (#|Γ'| + k)) distr_subst_rec; lia_f_equal.
Qed.

Lemma spine_subst_inst_subst_k {cf} {Σ} {Γ inst s Δ k Δ'} : 
  spine_subst Σ Γ inst s Δ ->
  subst_context s k Δ' = subst_context (List.rev inst) k (expand_lets_k_ctx Δ k Δ').
Proof.
  intros sp. pose proof (spine_subst_subst_to_extended_list_k sp).
  rewrite -H.
  rewrite /expand_lets_ctx /expand_lets_k_ctx /=.
  rewrite -map_rev.
  rewrite subst_context_subst_context. len.
  rewrite subst_context_lift_context_cancel. now len.
  f_equal.
  rewrite map_rev. rewrite H.
  apply context_subst_subst_extended_subst. apply sp.
Qed.

Lemma spine_subst_inst_subst_term_k {cf} {Σ} {Γ inst s Δ k Δ'} : 
  spine_subst Σ Γ inst s Δ ->
  subst s k Δ' = subst (List.rev inst) k (expand_lets_k Δ k Δ').
Proof.
  intros sp. pose proof (spine_subst_subst_to_extended_list_k sp).
  rewrite -H.
  rewrite /expand_lets_ctx /expand_lets_k_ctx /=.
  rewrite -map_rev /expand_lets_k.
  rewrite -{2}(Nat.add_0_r k) distr_subst_rec. len.
  rewrite simpl_subst_k. now len.
  f_equal.
  rewrite map_rev. rewrite H.
  apply context_subst_subst_extended_subst. apply sp.
Qed.

Lemma cumul_ctx_rel_app {cf} {Σ Γ Δ Δ'} :
  cumul_ctx_rel Σ Γ Δ Δ' <~> cumul_context Σ (Γ ,,, Δ) (Γ ,,, Δ').
Proof.
  split.
  - intros; eapply PCUICContextRelation.All2_fold_app.
    apply (length_of X). reflexivity. apply X.
  - intros; eapply PCUICContextRelation.All2_fold_app_inv.
    move: (length_of X); len; lia.
    assumption.
Qed.
    
Lemma cumul_ctx_rel_trans {cf} {Σ} {wfΣ : wf Σ} {Γ Δ Δ' Δ''} :
  cumul_ctx_rel Σ Γ Δ Δ' ->
  cumul_ctx_rel Σ Γ Δ' Δ'' ->
  cumul_ctx_rel Σ Γ Δ Δ''.
Proof.
  move/cumul_ctx_rel_app => h /cumul_ctx_rel_app h'.
  apply cumul_ctx_rel_app.
  now eapply cumul_context_trans; tea. 
Qed.

(** The crucial property on constructors of cumulative inductive types for type preservation: 
    we don't need to compare their instances when fully applied. *)
Lemma R_global_instance_cstr_irrelevant {cf} {Σ} {wfΣ  : wf Σ} {ci c} {mdecl idecl cdecl u u'} :
  declared_constructor Σ (ci, c) mdecl idecl cdecl ->
  R_ind_universes Σ ci (context_assumptions (ind_params mdecl) + #|cstr_indices cdecl|) u u' ->
  R_global_instance Σ.1 (eq_universe Σ) (eq_universe Σ) (ConstructRef ci c)
    (ind_npars mdecl + context_assumptions (cstr_args cdecl)) u u'.
Proof.
  intros declc.
  pose proof (on_declared_constructor declc).
  pose proof (on_declared_constructor declc) as [[onind oib] [ctor_sorts [hnth onc]]].
  intros Hu. pose proof (R_global_instance_length _ _ _ _ _ _ _ Hu).
  rewrite /R_global_instance /R_opt_variance /= /lookup_constructor.
  rewrite (declared_inductive_lookup_inductive declc) (proj2 declc).
  rewrite -(cstr_args_length onc).
  case: leb_spec_Set; try lia. move=> _ /=; cbn.
  now apply R_universe_instance_variance_irrelevant.
Qed.

Lemma wf_pre_case_branch_context {cf} {Σ} {wfΣ : wf Σ} {Γ ci mdecl p} {br : branch term} {cdecl} :
  wf_branch_gen cdecl (forget_types (bcontext br)) ->
  wf_local Σ (Γ,,, case_branch_context ci mdecl p (forget_types (bcontext br)) cdecl) ->
  wf_local Σ (Γ,,, pre_case_branch_context ci mdecl (pparams p) (puinst p) cdecl).
Proof.
  move=> wfbr wf.
  eapply wf_local_alpha; tea.
  apply eq_context_upto_cat. reflexivity.
  apply equal_decls_alpha.
  eapply All2_symP. tc.
  now apply pre_case_branch_context_eq.
Qed.

Lemma All2_map2_left_inv {A B C} (P : A -> B -> Type) (l : list C) (f : C -> A) l' : 
  All2 P (map f l) l' -> All2 (fun x => P (f x)) l l'.
Proof.
  rewrite -{1}(map_id l').
  intros. now eapply All2_map_inv in X.
Qed.

Lemma conv_refl' {cf} {Σ} {wfΣ : wf Σ} {Γ x y} : 
  x = y ->
  Σ ;;; Γ |- x = y.
Proof. now intros ->. Qed.

Lemma expand_lets_lift_cancel Γ x : 
  expand_lets Γ (lift0 #|Γ| x) = lift0 (context_assumptions Γ) x.
Proof.
  rewrite /expand_lets /expand_lets_k.
  simpl. rewrite simpl_lift; try lia.
  rewrite Nat.add_comm.
  rewrite -(simpl_lift _ _ _ _ 0); try lia.
  rewrite simpl_subst_k //. now len.
Qed.

Lemma context_assumptions_expand_lets_k_ctx {Γ k Δ} :
  context_assumptions (expand_lets_k_ctx Γ k Δ) = context_assumptions Δ.
Proof.
  now rewrite /expand_lets_k_ctx; len.
Qed.
Hint Rewrite @context_assumptions_expand_lets_k_ctx : len.

Lemma closedn_expand_lets (k : nat) (Γ : context) (t : term) :
  closedn_ctx k Γ ->
  closedn (k + #|Γ|) t ->
  closedn (k + context_assumptions Γ) (expand_lets Γ t).
Proof.
  rewrite /expand_lets /expand_lets_k.
  intros clΓ cl.
  eapply closedn_subst0.
  eapply (closedn_extended_subst_gen _ _ 0) => //.
  len.
  rewrite Nat.add_comm Nat.add_assoc. eapply closedn_lift.
  now rewrite Nat.add_comm.
Qed.

Lemma smash_context_subst_context_let_expand s Γ Δ : 
  smash_context [] (subst_context_let_expand s Γ Δ) = 
  subst_context_let_expand s Γ (smash_context [] Δ).
Proof.
  rewrite /subst_context_let_expand.
  rewrite (smash_context_subst []).
  now rewrite /expand_lets_ctx /expand_lets_k_ctx (smash_context_subst []) 
    (smash_context_lift []).
Qed.

Lemma on_constructor_wf_args {cf} {Σ} {wfΣ : wf Σ} {ind c mdecl idecl cdecl u} :
  declared_constructor Σ (ind, c) mdecl idecl cdecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  wf_local Σ (subst_instance u (ind_params mdecl) ,,, 
    (subst_context (ind_subst mdecl ind u)) #|ind_params mdecl| (subst_instance u (cstr_args cdecl))).
Proof.
  intros decl cu.
  pose proof (on_constructor_inst decl _ cu) as [wf _].
  rewrite !subst_instance_app_ctx in wf.
  rewrite -app_context_assoc -(app_context_nil_l (_ ,,, _)) app_context_assoc in wf.
  eapply substitution_wf_local in wf; tea.
  2:eapply (subslet_inds _ _ _ _ _ _ decl cu).
  rewrite app_context_nil_l subst_context_app closed_ctx_subst in wf.
  rewrite closedn_subst_instance_context. eapply (declared_inductive_closed_params decl).
  now simpl in wf; len in wf.
Qed.

Definition lengths := 
  (@context_assumptions_expand_lets_ctx, @context_assumptions_subst_context,
  @context_assumptions_app,
  @context_assumptions_subst_instance, @expand_lets_ctx_length, @subst_context_length,
  @subst_instance_length, @expand_lets_k_ctx_length, @inds_length, @lift_context_length,
  @app_length, @List.rev_length, @extended_subst_length).

Instance conv_context_refl {cf} Σ {wfΣ : wf Σ} : CRelationClasses.Reflexive (All2_fold (conv_decls Σ)).
Proof.
  intros x. reflexivity.
Qed.
  
Instance conv_context_sym {cf} Σ {wfΣ : wf Σ} : CRelationClasses.Symmetric (All2_fold (conv_decls Σ)).
Proof.
  intros x y. now apply conv_context_sym.
Qed.

Instance conv_context_trans {cf} Σ {wfΣ : wf Σ} : CRelationClasses.Transitive (All2_fold (conv_decls Σ)).
Proof.
  intros x y z. now apply conv_context_trans.
Qed.

Lemma sr_red1 {cf:checker_flags} :
  env_prop SR_red1
      (fun Σ Γ => wf_local Σ Γ × All_local_env (lift_typing SR_red1 Σ) Γ).
Proof.
  apply typing_ind_env; intros Σ wfΣ Γ wfΓ; unfold SR_red1; intros **; rename_all_hyps; auto.
  2-15:match goal with
    | [H : (_ ;;; _ |- _ <= _) |- _ ] => idtac
    | _ =>
      depelim Hu; try solve [apply mkApps_Fix_spec in x; noconf x];
      try solve [econstructor; eauto];
      try solve [
        match goal with
        | h : _ = mkApps _ ?args |- _ =>
          let e := fresh "e" in
          apply (f_equal nApp) in h as e ; simpl in e ;
          rewrite nApp_mkApps in e ; simpl in e ;
          destruct args ; discriminate
        end
      ]
    end.

  - (* Contexts *)
    split; auto.
    induction X; constructor; auto;
    unfold lift_typing in *; firstorder auto.

  - (* Rel delta reduction *)
    rewrite heq_nth_error in e. destruct decl as [na b ty]; noconf e.
    simpl.
    pose proof (PCUICValidity.nth_error_All_local_env heq_nth_error wfΓ); eauto.
    cbn in *.
    rewrite <- (firstn_skipn (S n) Γ).
    eapply weakening_length; auto.
    { rewrite firstn_length_le; auto. apply nth_error_Some_length in heq_nth_error. auto with arith. }
    now unfold app_context; rewrite firstn_skipn.

  - (* Prod *)
    constructor; eauto.
    unshelve eapply (context_conversion _ typeb); pcuics.

  - (* Lambda *)
    eapply type_Cumul'. eapply type_Lambda; eauto.
    unshelve eapply (context_conversion _ typeb); pcuics.
    assert (Σ ;;; Γ |- tLambda n t b : tProd n t bty). econstructor; pcuics.
    now eapply validity in X0.
    eapply cumul_red_r.
    apply cumul_refl'. constructor. apply Hu.

  - (* LetIn body *)
    eapply type_Cumul'.
    apply (substitution_let _ Γ n b b_ty b' b'_ty wf typeb').
    specialize (typing_wf_local typeb') as wfd.
    assert (Σ ;;; Γ |- tLetIn n b b_ty b' : tLetIn n b b_ty b'_ty). econstructor; eauto.
    eapply (validity X0).
    eapply cumul_red_r.
    apply cumul_refl'. constructor.

  - (* LetIn value *)
    eapply type_Cumul'.
    econstructor; eauto.
    unshelve eapply (context_conversion _ typeb'); pcuics.
    assert (Σ ;;; Γ |- tLetIn n b b_ty b' : tLetIn n b b_ty b'_ty). econstructor; eauto.
    eapply (validity X0).
    eapply cumul_red_r.
    apply cumul_refl'. now constructor.

  - (* LetIn type annotation *)
    specialize (forall_u _ Hu).
    eapply type_Cumul'.
    econstructor; eauto.
    eapply type_Cumul'. eauto. exists s1; auto.
    apply red_cumul; eauto.
    unshelve eapply (context_conversion _ typeb'); pcuics.
    constructor; pcuic.
    eapply type_Cumul'. eauto. all:pcuic.
    assert (Σ ;;; Γ |- tLetIn n b b_ty b' : tLetIn n b b_ty b'_ty). econstructor; eauto.
    eapply (validity X).
    eapply cumul_red_r.
    apply cumul_refl'. now constructor.

  - (* Application *)
    eapply substitution0; eauto.
    pose proof typet as typet'.
    eapply inversion_Lambda in typet' as [s1 [B' [Ht [Hb HU]]]]=>//.
    apply cumul_Prod_inv in HU as [[eqann eqA] leqB] => //.
    pose proof (validity typet) as i.
    eapply isType_tProd in i as [Hdom Hcodom]; auto.
    eapply type_Cumul'; eauto.
    unshelve eapply (context_conversion _ Hb); pcuics.

  - (* Fixpoint unfolding *)
    assert (args <> []) by (destruct args; simpl in *; congruence).
    apply tApp_mkApps_inj in H as [-> Hu]; auto.
    rewrite mkApps_nonempty; auto.
    epose (last_nonempty_eq H0). rewrite <- Hu in e1. rewrite <- e1.
    clear e1.
    specialize (inversion_mkApps wf typet) as [T' [appty spty]].
    have vT' := (validity appty).
    eapply type_tFix_inv in appty as [T [arg [fn' [[[Hnth wffix] Hty]]]]]; auto.
    rewrite e in Hnth. noconf Hnth.
    eapply type_App; eauto.
    eapply type_mkApps. eapply type_Cumul'; eauto. eapply spty.
    
  - (* Application congruence for argument *)
    eapply type_Cumul'; [eapply type_App| |]; eauto with wf.
    eapply validity. eauto. eauto.
    eapply type_App; eauto. eapply red_cumul_inv.
    eapply (red_red Σ Γ [vass na A] [] [u] [N2]); auto.
    constructor. constructor.

  - (* Constant unfolding *)
    unshelve epose proof (declared_constant_inj decl decl0 _ _); tea; subst decl.
    destruct decl0 as [ty body' univs]; simpl in *; subst body'.
    eapply on_declared_constant in H; tas; cbn in H.
    rewrite <- (app_context_nil_l Γ).
    apply subject_closed in H as clb; tas.
    apply type_closed in H as clty; tas.
    replace (subst_instance u body)
      with (lift0 #|Γ| (subst_instance u body)).
    replace (subst_instance u ty)
      with (lift0 #|Γ| (subst_instance u ty)).
    2-3: rewrite -subst_instance_lift lift_closed; cbnr; tas.
    eapply weakening; tea.
    now rewrite app_context_nil_l.
    eapply typing_subst_instance_decl with (Γ0:=[]); tea.

  - (* iota reduction *)
    clear forall_u forall_u0 X X0.
    destruct X1 as [wfpctx X1].
    hide X9.
    pose proof typec as typec''.
    unfold iota_red.
    pose proof typec as typec'.
    eapply inversion_mkApps in typec as [A [tyc tyargs]]; auto.
    eapply (inversion_Construct Σ wf) in tyc as [mdecl' [idecl' [cdecl [wfl [declc [Hu tyc]]]]]].
    eapply typing_spine_strengthen in tyargs; tea.
    clear tyc.
    unshelve eapply Construct_Ind_ind_eq in typec'; eauto.
    pose proof (declared_inductive_inj isdecl (proj1 declc)) as [-> ->].
    destruct typec' as [[[[_ equ] cu] eqargs] [cparsubst [cargsubst [iparsubst [iidxsubst ci']]]]].
    destruct ci' as ((([cparsubst0 iparsubst0] & idxsubst0) & subsidx) & [s [typectx [Hpars Hargs]]]).
    pose proof (on_declared_constructor declc) as [[onind oib] [ctor_sorts [hnth onc]]].
    (* pose proof (PCUICContextSubst.context_subst_fun csubst (iparsubst0.(inst_ctx_subst))). subst iparsubst. *)
    unshelve epose proof (constructor_cumulative_indices wf declc _ Hu cu equ _ _ _ _ _ cparsubst0 iparsubst0 Hpars).
    { eapply (weaken_lookup_on_global_env' _ _ _ wf (proj1 isdecl)). }
    set (argctxu1 := subst_context _ _ _) in X |- *.
    set (argctxu := subst_context _ _ _) in X |- *.
    simpl in X.
    set (pargctxu1 := subst_context cparsubst 0 argctxu1) in X |- *.
    set (pargctxu := subst_context iparsubst 0 argctxu) in X |- *.
    destruct X as [cumargs convidx]; eauto.
    assert(wfparu : wf_local Σ (subst_instance (puinst p) (ind_params mdecl))). 
    { eapply on_minductive_wf_params; eauto. }
    assert (wfps : wf_universe Σ ps).
    { eapply validity in IHp; auto. eapply PCUICWfUniverses.isType_wf_universes in IHp; tea.
      now apply (ssrbool.elimT PCUICWfUniverses.wf_universe_reflect) in IHp. }
    have lenpars := (wf_predicate_length_pars H0).      
    unfold hidebody in X9.
    set (ptm := it_mkLambda_or_LetIn _ _).
    rename c0 into c.
    rename u0 into u.
    assert (isType Σ Γ (mkApps ptm (indices ++ [mkApps (tConstruct ci c u) args]))).
    { eapply validity. econstructor; eauto. apply (All2i_impl X9). intuition auto. }
    eapply All2i_nth_error in X9; tea.
    2:{ destruct declc. simpl in e1. exact e1. }
    cbn in X9.
    destruct X9 as [[[wfbrctx IHbrctx] convbrctx] [[bodty [wfcbc IHcbc]] [IHbody [cbty IHcbty]]]].
    clear IHcbty IHbody IHbrctx IHcbc.
    unfold case_branch_type, case_branch_type_gen at 1 in bodty. cbn [fst] in bodty.
    move: bodty.
    intros hb.
    eapply context_conversion in hb.
    2:exact wfbrctx.
    2:{ symmetry; tea. }
    eapply typing_expand_lets in hb.
    eapply context_conversion in hb.
    3:{ eapply conv_context_smash_end; tea. }
    2:{ eapply wf_local_smash_end; tea. }
    rewrite -> case_branch_type_fst in *.
    set (brctx := (pre_case_branch_context ci mdecl (pparams p) (puinst p) cdecl)).
    assert (convbrctx' : conv_context Σ (Γ ,,, bcontext br) (Γ ,,, brctx)).
    { etransitivity; tea.
      apply conv_context_app, eq_context_alpha_conv.
      rewrite /brctx. eapply All2_symP. tc.
      apply pre_case_branch_context_eq.
      eapply Forall2_All2, All2_nth_error in H4; tea.
      eapply declc. }   
    assert (convbrctx'' : conv_context Σ (Γ ,,, case_branch_context ci mdecl p (forget_types (bcontext br)) cdecl)
       (Γ ,,, brctx)).
    { etransitivity; tea. symmetry. tea. }
    assert (wfbr : wf_branch cdecl br).
    { eapply Forall2_All2, All2_nth_error in H4; tea.
      eapply declc. }
    assert (wfbrctx' : wf_local Σ (Γ ,,, brctx)).
    { rewrite /brctx. eapply wf_pre_case_branch_context; tea. }
    assert (convbrctxsmash : conv_context Σ (Γ ,,, smash_context [] (case_branch_context ci mdecl p (forget_types (bcontext br)) cdecl))
        (Γ ,,, smash_context [] brctx)).
    { eapply conv_context_smash_end; tea. }
    assert (spbrctx : spine_subst Σ Γ (skipn (ind_npars mdecl) args) (List.rev (skipn (ind_npars mdecl) args))
      (smash_context [] brctx)).
    { pose proof (spine_subst_smash _ idxsubst0).
      eapply spine_subst_cumul in X0. eapply X0. all:tea.
      1-2:apply smash_context_assumption_context; pcuic.
      eapply X0.
      apply wf_local_smash_end; tea.
      move: cumargs.
      rewrite /pargctxu /argctxu.
      move: iparsubst0.
      rewrite (firstn_app_left _ 0).
      now rewrite (wf_predicate_length_pars H0).
      intros iparsubst0.
      clear X6. unshelve epose proof (ctx_inst_spine_subst _ X5).
      eapply weaken_wf_local; tea. exact (on_minductive_wf_params_indices_inst isdecl _ cu).
      rewrite (spine_subst_inst_subst iparsubst0) /= app_nil_r.
      intros cum.
      eapply cumul_ctx_rel_trans; tea.
      apply cumul_ctx_rel_app. reflexivity. }
    eapply context_conversion in hb. 3:tea.
    2:{ eapply wf_local_smash_end; tea. }
    eapply (PCUICSubstitution.substitution _ Γ _ _ []) in hb. 
    3:exact spbrctx. 2:tea.
    cbn -[case_branch_type_gen] in hb.
    rewrite subst_context_nil -heq_ind_npars in hb *.
    eapply type_Cumul'. exact hb.
    assumption.
    set cbtyg := (case_branch_type_gen _ _ _ _ _ _ _ _ _).
    (* Move back to the canonical branch context for the rest of the proof *)
    transitivity (subst0 (List.rev (skipn (ind_npars mdecl) args)) (expand_lets brctx cbtyg.2)).
    { eapply conv_cumul.
      eapply (substitution_conv _ _ _ []). 3:eapply spbrctx. all:tea.
      { eapply wf_local_smash_end => //. }
      symmetry. eapply conv_expand_lets_conv_ctx; tea. reflexivity.
      eapply conv_context_rel_app. now symmetry. }
    cbn.
    rewrite lift_mkApps !subst_mkApps.
    pose proof (wf_branch_length wfbr).
    have lenskip: #|skipn (ind_npars mdecl) args| = (context_assumptions (cstr_args cdecl)).
    { rewrite List.skipn_length eqargs; lia. }
    have lenfirst: #|firstn (ind_npars mdecl) args| = (context_assumptions (ind_params mdecl)).
    { rewrite firstn_length_le; try lia. now rewrite -(declared_minductive_ind_npars isdecl). }
    have brctxlen : #|brctx| = #|cstr_args cdecl|.
    { now rewrite /brctx !lengths. }
    have pparamsl : #|pparams p| = context_assumptions (ind_params mdecl).
    { move: (wf_predicate_length_pars H0).
      now rewrite (declared_minductive_ind_npars isdecl). }
      
    rewrite simpl_lift; try lia.
    rewrite subst_subst_lift // !lengths -H //; try lia.
    rewrite map_app /= !map_app. eapply conv_cumul.
    have wfparsargs : wf_local Σ
      (subst_instance u (ind_params mdecl),,,
        subst_context (inds (inductive_mind ci) u (ind_bodies mdecl))
          #|ind_params mdecl| (subst_instance u (cstr_args cdecl))).
    { exact (on_constructor_wf_args declc Hu). }
    have wfparsargs' : wf_local Σ
      (subst_instance (puinst p) (ind_params mdecl),,,
        subst_context (inds (inductive_mind ci) (puinst p) (ind_bodies mdecl))
          #|ind_params mdecl| (subst_instance (puinst p) (cstr_args cdecl))).
    { exact (on_constructor_wf_args declc cu). }
    eapply mkApps_conv_args; tea. reflexivity.
    rewrite (firstn_app_left _ 0) ?Nat.add_0_r // /= ?app_nil_r in iparsubst0.
    rewrite (firstn_app_left _ 0) ?Nat.add_0_r // /= ?app_nil_r in Hpars.
    rewrite (skipn_all_app_eq) // in subsidx.
    have brctxass : context_assumptions brctx = context_assumptions (cstr_args cdecl).
    { now rewrite /brctx !lengths. }
    eapply All2_app.
    * set(indsub := inds _ _ _).
      rewrite H.
      relativize (map (subst0 _) _).
      2:{
        rewrite !map_map_compose. apply map_ext => x.
        symmetry.
        rewrite -/(subst_let_expand _ _ _) -/(subst_let_expand_k _ _ _ _).
        rewrite -brctxass -brctxlen -expand_lets_eq.
        rewrite {1 2}/brctx {1 2}/pre_case_branch_context {1}subst_context_length.
        rewrite /subst_let_expand_k (expand_lets_subst_comm _ _ _) !lengths.
        relativize (context_assumptions _).
        erewrite <- subst_app_simpl. 2:now rewrite !lengths.
        rewrite subst_app_decomp.
        relativize #|cstr_args cdecl|.
        erewrite subst_let_expand_app.
        2-4:rewrite ?lengths; try lia; reflexivity.
        rewrite /subst_let_expand.
        reflexivity. }
      move: Hargs.
      move: convidx.
      change (fun x y => Σ ;;; Γ |- x = y) with (conv Σ Γ).
      intros cv convidx.
      eapply (conv_terms_subst _ _ _ _ []) in cv.
      4:{ exact (spine_subst_smash _ idxsubst0). }
      4:{ exact (spine_subst_smash _ idxsubst0). }
      all:tea. 2:{ eapply wf_local_smash_end; tea. eapply idxsubst0. }
      2:{ eapply All2_rev. eapply All2_refl. reflexivity. }
      rewrite subst_context_nil /= in cv. simpl in cv.
      rewrite skipn_all_app_eq // in convidx.

      assert(conv_terms Σ Γ
        (map
         (fun x : term =>
          subst0 (List.rev args)
            (expand_lets (argctxu1 ++ subst_instance u (ind_params mdecl)) (subst_instance u x)))
          (cstr_indices cdecl)) indices).
      { etransitivity; tea.
        pose proof (positive_cstr_closed_indices _ declc).
        eapply All2_map. eapply All_map_inv in X0.
        eapply All_All2; tea. intros x.
        cbn. intros cl.
        eapply conv_refl'.
        epose proof 
          (spine_subst_app Σ Γ (subst_instance u (ind_params mdecl))
            (subst_context
              (inds (inductive_mind ci) u (ind_bodies mdecl))
               #|ind_params mdecl| (subst_instance u (cstr_args cdecl)))
          (firstn (ind_npars mdecl) args)
          (skipn (ind_npars mdecl) args) (cargsubst ++ cparsubst) wf
          ).
        rewrite lenfirst in X3. len in X3.
        specialize (X3 eq_refl). 
        forward X3. { rewrite -app_context_assoc. eapply weaken_wf_local; tea. }
        forward X3. split.
        rewrite skipn_all_app_eq; len.
        now rewrite -(PCUICContextSubst.context_subst_length idxsubst0); len.
        apply cparsubst0.
        pose proof (PCUICContextSubst.context_subst_length idxsubst0).
        len in H3.
        rewrite firstn_app H3 firstn_all Nat.sub_diag /= app_nil_r skipn_all_app_eq //.
        rewrite firstn_skipn in X3.
        rewrite (spine_subst_inst_subst_term X3).
        f_equal.
        pose proof (PCUICInductiveInversion.on_constructor_wf_args declc).
        eapply closed_wf_local in X7; tea.
        rewrite !closedn_ctx_app /= in X7 *.
        move/andb_and: X7 => [] /andb_and [] clar clp clargs.
        len in clargs.
        rewrite -(subst_closedn (inds (inductive_mind ci) u (ind_bodies mdecl))
              (context_assumptions (ind_params mdecl ,,, cstr_args cdecl))
              (expand_lets _ _)).
        { rewrite /argctxu1.
          relativize (context_assumptions _).
          eapply (closedn_expand_lets 0).
          rewrite !closedn_ctx_app /=.
          apply andb_true_iff; split.
          rewrite closedn_subst_instance_context.
          eapply (declared_inductive_closed_params isdecl).
          rewrite subst_instance_length.
          eapply (closedn_ctx_subst 0). simpl. 
          rewrite /ind_subst inds_length.
          now rewrite closedn_subst_instance_context.
          eapply (declared_minductive_closed_inds isdecl).
          rewrite /= app_length subst_context_length !subst_instance_length.
          eapply (PCUICInductiveInversion.closedn_expand_lets 0) in cl.
          rewrite closedn_subst_instance.
          now rewrite /= app_length in cl. 
          rewrite /= !context_assumptions_app /= context_assumptions_subst_context //
            !context_assumptions_subst_instance //. }
        (* rewrite -subst_instance_app_ctx -subst_instance_expand_lets closedn_subst_instance. *)
        relativize (context_assumptions _).
        erewrite <-(expand_lets_subst_comm _ _ _).
        2:{ now rewrite /argctxu1 !context_assumptions_app 
              !context_assumptions_subst_context !context_assumptions_subst_instance. }
        f_equal. 
        * rewrite subst_context_app closed_ctx_subst.
          rewrite closedn_subst_instance_context.
          now apply (declared_inductive_closed_params isdecl).
          f_equal. len.
          rewrite closed_ctx_subst //.
          rewrite /argctxu1. simpl.
          eapply (closedn_ctx_subst 0). simpl.
          rewrite /ind_subst inds_length closedn_subst_instance_context //.
          eapply (declared_minductive_closed_inds isdecl).
        * now rewrite /argctxu1; len. }
      clear convidx.
      etransitivity; tea.
      transitivity (map (subst0 (List.rev (skipn (ind_npars mdecl) args)))
      (map (subst iparsubst (context_assumptions (cstr_args cdecl)))
         (map (expand_lets argctxu)
            (map (subst_instance (puinst p)) (cstr_indices cdecl))))).
      2:{
        rewrite !map_map_compose.
        eapply All2_map.
        rewrite !map_map_compose in cv.
        eapply All2_map_inv in cv.
        eapply All2_All in cv.
        eapply All_All2; tea. cbn.
        intros x Hx.
        etransitivity. symmetry; tea.
        rewrite (spine_subst_inst_subst_term_k cparsubst0).
        pose proof (subst_let_expand_app).
        relativize (context_assumptions (cstr_args cdecl)).
        erewrite <-subst_app_simpl. 2:now len.
        rewrite -List.rev_app_distr firstn_skipn. len.
        rewrite lenskip expand_lets_app /argctxu1.
        now rewrite context_assumptions_subst_context context_assumptions_subst_instance. }

      (* clear -H4 pparamsl wfbrctx convbrctx cumargs wfcbc wfparsargs Hpars lenskip lenfirst lenpars heq_ind_npars wf cparsubst0 idxsubst0 iparsubst0 isdecl declc. *)
      rewrite /argctxu. simpl.
      rewrite !map_map_compose. apply All2_map.
      eapply All_All2.
      exact (All_map_inv _ _ _ (positive_cstr_closed_indices _ declc)).
      cbn => x.
      rewrite -(closed_ctx_subst indsub 0 (subst_instance _ _ ,,, _)).
      { now eapply closed_wf_local in wfparsargs'. }
      relativize (#|ind_params _| + _).
      erewrite expand_lets_subst_comm; rewrite !lengths.
      2:rewrite !lengths; lia.
      rewrite -context_assumptions_app.
      move/(PCUICInductiveInversion.closedn_expand_lets 0) => /=; rewrite /= !lengths => clx.
      rewrite (subst_closedn indsub (_ + _)).
      relativize (_ + _). eapply (closedn_expand_lets 0).
      2-3:rewrite /= !lengths // closedn_subst_instance //.
      eapply closed_wf_local; tea.
      rewrite (spine_subst_inst_subst_term_k iparsubst0).
      change (ind_subst _ _ _) with indsub.
      relativize (context_assumptions _).
      erewrite <-subst_app_simpl. 2:now len.
      rewrite List.rev_length lenskip /=.
      relativize (context_assumptions _).
      erewrite <- expand_lets_app.
      2:now rewrite !lengths.
      reflexivity.

    * rewrite lift_mkApps /= !subst_mkApps /=. constructor. 2:constructor.
      rewrite H.
      rewrite !map_app. 
      rewrite -{3}(firstn_skipn (ind_npars mdecl) args) -brctxlen -brctxass.
      rewrite - !expand_lets_eq_map.
      rewrite -/(expand_lets_k (bcontext br) 0 _).
      relativize (to_extended_list (cstr_args cdecl)).
      erewrite map_expand_lets_to_extended_list.
      2:{ etransitivity.
        2:apply to_extended_list_case_branch_context.
        eapply conv_context_rel_to_extended_list.
        apply conv_context_rel_app. symmetry. tea. 
        now eapply Forall2_All2 in wfbr. }
      rewrite -map_expand_lets_to_extended_list.
      rewrite !map_map_compose.
      rewrite [map (fun x => _) (to_extended_list _)](@map_subst_let_expand_to_extended_list _ Σ _ Γ); tea.
      relativize (map _ _).
      2:{ eapply map_ext => x. rewrite -/(subst_let_expand _ _ _). rewrite subst_let_expand_lift_id //.
          len. now rewrite heq_ind_npars. }
      rewrite map_id.
      transitivity (mkApps (tConstruct ci c (puinst p)) args).
      rewrite -(firstn_skipn (ind_npars mdecl) args).
      eapply mkApps_conv_args; tea. reflexivity.
      eapply All2_app. eapply All2_symP => //. intro; now symmetry.
      rewrite firstn_skipn. eapply All2_refl; reflexivity.
      rewrite firstn_skipn. constructor.
      eapply eq_term_upto_univ_mkApps.
      2:reflexivity.
      constructor. eapply R_global_instance_sym; tc.
      rewrite eqargs.
      now eapply (R_global_instance_cstr_irrelevant declc).

  - (* Case congruence: on a cofix, impossible *)
    eapply inversion_mkApps in typec as [? [tcof ?]] =>  //.
    eapply type_tCoFix_inv in tcof as [d [[[Hnth wfcofix] ?] ?]] => //.
    unfold unfold_cofix in e.
    rewrite Hnth in e. noconf e.
    eapply typing_spine_strengthen in t; eauto. clear c.
    eapply wf_cofixpoint_typing_spine in t; eauto.
    2:eapply validity; eauto.
    unfold check_recursivity_kind in t.
    rewrite isdecl.p1 in t.
    apply Reflect.eqb_eq in t. rewrite t /= in heq_isCoFinite.
    discriminate.

  - (* Case congruence on the predicate *) 
    todo "case".
    (*eapply (type_Cumul _ _ _ (mkApps p' (skipn npar args ++ [c]))).
    eapply build_branches_type_red in heq_map_option_out as [brtys' [eqbrtys alleq]]; eauto.
    eapply type_Case; eauto.
    * eapply All2_trans'; eauto. simpl.
      intros. destruct X1 as ((((? & ?) & ?) & [s [Hs IH]]) & ? & ?).
      specialize (IH _ r).
      intuition auto. now transitivity y.1.
      eapply type_Cumul'; eauto. now exists s.
      now eapply conv_cumul, red_conv, red1_red.
      now exists s.
    * pose proof typec as typec'.
      eapply (env_prop_typing _ _ validity) in typec' as wat; auto.
      unshelve eapply isType_mkApps_Ind in wat as [parsubst [argsubst wat]]; eauto.
      set (oib := on_declared_inductive wf in isdecl) *. clearbody oib.
      destruct oib as [onind oib].
      destruct wat  as [[spars sargs] cu].
      unshelve eapply (build_case_predicate_type_spec (Σ.1, _)) in heq_build_case_predicate_type as [parsubst' [cparsubst Hpty]]; eauto.
      rewrite {}Hpty in typep.
      subst npar.
      assert (wfps : wf_universe Σ ps).
      { eapply validity in typep; auto. eapply PCUICWfUniverses.isType_wf_universes in typep.
        rewrite PCUICWfUniverses.wf_universes_it_mkProd_or_LetIn in typep.
        move/andb_and: typep => /= [_ /andb_and[_ typep]]. 
        now apply (ssrbool.elimT PCUICWfUniverses.wf_universe_reflect) in typep. auto. }
      pose proof (context_subst_fun cparsubst spars). subst parsubst'. clear cparsubst.
      eapply type_mkApps. eauto.
      eapply wf_arity_spine_typing_spine; eauto.
      split. apply (env_prop_typing _ _ validity) in typep as ?; eauto.
      eapply arity_spine_it_mkProd_or_LetIn; eauto.
      simpl. constructor; [ |constructor].
      rewrite subst_mkApps. simpl.
      rewrite map_app. rewrite map_map_compose.
      rewrite map_subst_lift_id_eq. now rewrite (subslet_length sargs); autorewrite with len.
      move: (spine_subst_subst_to_extended_list_k sargs).
      rewrite to_extended_list_k_subst PCUICSubstitution.map_subst_instance_to_extended_list_k.
      move->. now rewrite firstn_skipn.
    * now eapply conv_cumul, conv_sym, red_conv, red_mkApps_f, red1_red.
*)
  - todo "case".
  - todo "case".
  - (* Case congruence on discriminee *) 
    eapply type_Cumul. eapply type_Case; eauto.
    * solve_all.
    * solve_all.
    * pose proof typec as typec'.
      eapply (env_prop_typing _ _ validity_env) in typec' as wat; auto.
      unshelve eapply isType_mkApps_Ind in wat as [parsubst [argsubst wat]]; eauto.
      destruct (on_declared_inductive isdecl) as [onind oib].
      destruct wat as [[spars sargs] cu].
      (* clear X7. intuition auto. instantiate (1 := ps).
      assert (wfps : wf_universe Σ ps).
      { now eapply PCUICWfUniverses.typing_wf_universe in IHp. }
      move: IHp. *)
      todo "case".
    (*
      pose proof (context_subst_fun cparsubst spars). subst parsubst'. clear cparsubst.
      eapply type_mkApps. eauto.
      eapply wf_arity_spine_typing_spine; eauto.
      split. apply (env_prop_typing _ _ validity) in typep; eauto.
      eapply arity_spine_it_mkProd_or_LetIn; eauto.
      simpl. constructor; [ |constructor].
      rewrite subst_mkApps. simpl.
      rewrite map_app. rewrite map_map_compose.
      rewrite map_subst_lift_id_eq. now rewrite (subslet_length sargs); autorewrite with len.
      move: (spine_subst_subst_to_extended_list_k sargs).
      rewrite to_extended_list_k_subst PCUICSubstitution.map_subst_instance_to_extended_list_k.
      move->. now rewrite firstn_skipn.*)
    * eapply conv_cumul, conv_sym, red_conv, red_mkApps; auto.
      eapply All2_app; [eapply All2_refl; reflexivity|now constructor].
    
  - (* Case congruence on branches *)
    eapply type_Case; eauto. solve_all.
    todo "case".
    todo "case".
    (* eapply (OnOne2_All2_All2 o X5).
    intros [] []; simpl. intros.
    intuition auto. destruct b as [s [Hs IH]]; eauto. subst.
    intros [] [] []; simpl. intros.
    intuition auto. subst.    
    reflexivity.
    destruct b0 as [s [Hs IH]]; eauto. *)

  - (* Proj CoFix congruence *)
    assert(typecofix : Σ ;;; Γ |- tProj p (mkApps (tCoFix mfix idx) args0) : subst0 (mkApps (tCoFix mfix idx) args0 :: List.rev args)
      (subst_instance u pdecl.2)).
    { econstructor; eauto. }

    pose proof (env_prop_typing _ _  validity_env _ _ _ _ _ typec).
    eapply inversion_mkApps in typec as [? [tcof tsp]]; auto.
    eapply type_tCoFix_inv in tcof as [d [[[Hnth wfcofix] Hbody] Hcum]]; auto.
    unfold unfold_cofix in e.
    rewrite Hnth in e. noconf e.
    simpl in X1.
    eapply type_Cumul'; [econstructor|..]; eauto.
    eapply typing_spine_strengthen in tsp; eauto.
    eapply type_mkApps. eauto. eauto.
    now eapply validity in typecofix.
    eapply conv_cumul.
    rewrite (subst_app_decomp [mkApps (subst0 (cofix_subst mfix) (dbody d)) args0]) (subst_app_decomp [mkApps (tCoFix mfix idx) args0]).
    eapply conv_sym, red_conv.
    destruct (on_declared_projection isdecl) as [oi onp].
    epose proof (subslet_projs _ _ _ _ wf isdecl).
    set (oib := declared_inductive_inv _ _ _ _) in *. simpl in onp, X2.
    destruct (ind_ctors idecl) as [|? []]; try contradiction.
    destruct onp as [[[tyargctx onps] Hp2] onp].
    destruct (ind_cunivs oib) as [|? []]; try contradiction.
    specialize (X2 onps).
    red in onp.
    destruct (nth_error (smash_context [] _) _) eqn:Heq; try contradiction.
    destruct onp as [na eq].
    pose proof (on_projs_noidx _ _ _ _ _ _ onps).
    set (indsubst := inds _ _ _) in *.
    set (projsubst := projs _ _ _) in *.
    rewrite eq.
    eapply (substitution_untyped_red _ Γ
      (smash_context [] (subst_instance u (ind_params mdecl))) []). auto.
    { unshelve eapply isType_mkApps_Ind in X1 as [parsubst [argsubst Hind]]; eauto.
      2:eapply isdecl.
      simpl in Hind.
      destruct Hind as [[sppars spargs] cu].
      rewrite firstn_all2 in sppars. lia.
      eapply spine_subst_smash in sppars.
      eapply subslet_untyped_subslet. eapply sppars. auto. }
    rewrite !subst_instance_subst.
    rewrite distr_subst.
    rewrite distr_subst.
    rewrite distr_subst.
    rewrite !map_length !List.rev_length.
    rewrite subst_instance_lift.
    rewrite -(Nat.add_1_r (ind_npars mdecl)) Nat.add_assoc.
    rewrite {2 5}/projsubst. rewrite Nat.add_0_r.
    rewrite -(commut_lift_subst_rec _ _ 1 (#|projsubst| + ind_npars mdecl)).
    rewrite /projsubst. autorewrite with len. lia.
    rewrite !projs_length.
    rewrite /projsubst !simpl_subst_k //.
    rewrite [subst_instance _ (projs _ _ _)]projs_subst_instance. 
    rewrite projs_subst_above //. lia. simpl.
    rewrite !subst_projs_inst !projs_inst_lift.
    eapply (red_red _ (Γ ,,, smash_context [] (subst_instance u (ind_params mdecl)))
       (skipn (context_assumptions (cstr_args c) - p.2) 
       (smash_context [] (subst_context (inds (inductive_mind p.1.1) u (ind_bodies mdecl)) #|ind_params mdecl| (subst_instance u (cstr_args c))))) []); auto.
    ** eapply All2_map.
      eapply (All2_impl (P:=fun x y => red Σ.1 Γ x y)).
      2:{ intros x' y' hred. rewrite heq_length.
          eapply weakening_red_0; auto. autorewrite with len.
          pose proof (onNpars oi). simpl; lia. }
      elim: p.2. simpl. constructor.
      intros n Hn. constructor; auto.
      eapply red1_red. eapply red_cofix_proj. eauto.
      unfold unfold_cofix. rewrite Hnth. reflexivity.
    ** rewrite -projs_inst_lift.
      rewrite -subst_projs_inst.
      assert (p.2 = context_assumptions (cstr_args c) - (context_assumptions (cstr_args c) - p.2)) by lia.
      rewrite {1}H0. rewrite -skipn_projs map_skipn subst_projs_inst.
      eapply untyped_subslet_skipn. destruct p as [[[? ?] ?] ?]. simpl in *.
      rewrite /indsubst.
      eapply X2.

  - (* Proj Constructor reduction *) 
    pose proof (validity typec).
    simpl in typec.
    pose proof typec as typec'.
    eapply inversion_mkApps in typec as [A [tyc tyargs]]; auto.
    eapply (inversion_Construct Σ wf) in tyc as [mdecl' [idecl' [cdecl [wfl [declc [Hu tyc]]]]]].
    pose proof typec' as typec''.
    destruct (declared_projection_declared_constructor isdecl declc); subst mdecl' idecl'.
    unshelve eapply Construct_Ind_ind_eq in typec'; eauto.
    destruct (on_declared_constructor declc) as [[onmind oin] [cs [Hnth onc]]].
    simpl in typec'.
    pose proof (subslet_projs Σ _ _ _ _ isdecl) as projsubsl.
    set(oib := declared_inductive_inv _ wf wf _) in *.
    pose proof (onProjections oib) as onProjs. clearbody oib.
    forward onProjs. destruct isdecl as [? [hnth ?]].
    eapply nth_error_Some_length in hnth. simpl in hnth.
    intros Hp. apply (f_equal (@length _)) in Hp. rewrite Hp /= in hnth. lia.
    simpl in *.
    move: (proj2 declc).
    simpl in *.
    destruct ind_ctors as [|? []] => //.
    intros [= ->].
    destruct typec' as [[[[_ equ] cu] eqargs] [cparsubst [cargsubst [iparsubst [iidxsubst ci]]]]].
    destruct ci as ((([cparsubst0 iparsubst0] & idxsubst0) & subsidx) & [s [typectx [Hpars Hargs]]]).
    destruct ind_cunivs as [|? ?] => //; noconf Hnth.
    specialize (projsubsl onProjs).
    destruct onProjs.
    eapply nth_error_alli in on_projs; eauto.
    2:eapply isdecl. simpl in on_projs.
    eapply typing_spine_strengthen in tyargs; eauto.
    rewrite -(firstn_skipn (ind_npars mdecl) args0) in tyargs, e |- *.
    assert(#|firstn (ind_npars mdecl) args0| = ind_npars mdecl).
    rewrite firstn_length_le. lia. lia.
    rewrite nth_error_app_ge in e. rewrite H.
    pose proof (onNpars onmind).
    pose proof (proj2 (proj2 isdecl)). simpl in *. lia.
    rewrite H in e. replace (ind_npars mdecl + narg - ind_npars mdecl) with narg in e by lia.
    epose proof (declared_constructor_valid_ty _ _ _ _ _ 0 cdecl _ wf wfΓ declc Hu) as Hty.
    unfold type_of_constructor in tyargs, Hty.
    rewrite onc.(cstr_eq) in tyargs, Hty.
    rewrite !subst_instance_it_mkProd_or_LetIn !subst_it_mkProd_or_LetIn in tyargs, Hty.
    eapply typing_spine_inv in tyargs as [arg_sub [[spargs iswat] sp]]; eauto.
    2:{ rewrite !context_assumptions_fold.
        rewrite subst_instance_assumptions. rewrite H.
        apply onNpars in onmind. lia. }
    rewrite closed_ctx_subst in spargs.
    { eapply closed_wf_local; eauto. eapply on_minductive_wf_params; eauto. }
    pose proof (spine_subst_inj_subst spargs cparsubst0). subst arg_sub.
    clear Hty.
    rewrite subst_it_mkProd_or_LetIn in sp, iswat.
    rewrite !subst_instance_mkApps !subst_mkApps in sp, iswat.
    eapply typing_spine_nth_error in sp; eauto.
    clear iswat.
    2:{ rewrite !context_assumptions_fold. rewrite subst_instance_assumptions.
        clear iswat sp. eapply nth_error_Some_length in e. todo "case". }
    destruct sp as [decl [Hnth Hu0]].
    simpl in on_projs. red in on_projs.
    eapply type_Cumul'; eauto.
    { rewrite firstn_skipn.
      todo "case".
      (*
      eapply (isType_subst_instance_decl _ _ _ _ _ u wf isdecl.p1.p1) in projty; eauto.
      destruct projty as [s' Hs].
      exists s'. red in Hs.
      rewrite /= /map_decl /= in Hs.
      eapply (weaken_ctx Γ) in Hs; auto.
      rewrite (subst_app_simpl [_]).
      eapply (substitution0 _ _ _ _ _ _ (tSort s')). auto.
      simpl.
      eapply (substitution _ Γ (subst_instance u (smash_context [] (ind_params mdecl)))
        _ [vass _ _] _ (tSort s')); eauto.
      rewrite firstn_all2 in iparsubst0. lia.
      eapply spine_subst_smash in iparsubst0; auto.
      rewrite subst_instance_smash.
      eapply iparsubst0. simpl.
      rewrite subst_instance_mkApps subst_mkApps /=.
      rewrite (subst_instance_id Σ) // subst_instance_to_extended_list.
      rewrite firstn_all2 in iparsubst0. lia.
      eapply spine_subst_smash in iparsubst0; auto.
      rewrite subst_instance_smash /=.
      rewrite /to_extended_list (spine_subst_subst_to_extended_list_k iparsubst0).
      assumption. *) }
    rewrite !context_assumptions_fold subst_instance_assumptions in Hnth.
    rewrite firstn_skipn.
    rewrite PCUICSigmaCalculus.smash_context_app PCUICSigmaCalculus.smash_context_acc in on_projs.
    rewrite nth_error_app_lt in on_projs.
    { autorewrite with len. simpl. 
      eapply nth_error_Some_length in Hnth. autorewrite with len in Hnth.
      now simpl in Hnth. }
    rewrite nth_error_subst_context in on_projs.
    epose proof (nth_error_lift_context_eq _ (smash_context [] (ind_params mdecl))).
    autorewrite with len in H0. simpl in H0.
    erewrite -> H0 in on_projs. clear H0.
    unshelve epose proof (constructor_cumulative_indices wf declc _ Hu cu equ _ _ _ _ _ spargs iparsubst0 Hpars).
    { eapply (weaken_lookup_on_global_env' _ _ _ wf (proj1 (proj1 declc))). }
    move: X2.
    set (argsu1 := subst_instance u1 (cstr_args cdecl)) in *.
    set (argsu := subst_instance u (cstr_args cdecl)) in *.
    set (argctxu1 := subst_context _ _ argsu1) in *.
    set (argctxu := subst_context _ _ argsu) in *.
    simpl.
    set (pargctxu1 := subst_context cparsubst 0 argctxu1) in *.
    set (pargctxu := subst_context iparsubst 0 argctxu) in *.
    move=> [cumargs _]; eauto.
    eapply PCUICRedTypeIrrelevance.All2_fold_nth_ass in cumargs.
    3:eapply smash_context_assumption_context; constructor.
    2:{ unfold pargctxu1, argctxu1, argsu1.
        autorewrite with len in Hnth. eapply Hnth. }
    destruct cumargs as [decl' [Hdecl' cum]].
    rewrite (smash_context_subst []) in Hnth.
    rewrite (smash_context_subst []) in Hnth.
    rewrite -(subst_instance_smash u1 _ []) in Hnth.    
    rewrite !nth_error_subst_context in Hnth.
    rewrite nth_error_map in Hnth.
    todo "case".
    (*
    destruct projeq as [decl'' [[[Hdecl wfdecl] Hty1] Hty2]].
    rewrite Hdecl in on_projs, Hnth.
    simpl in on_projs, Hnth.
    destruct on_projs as [declna decltyeq].
    noconf Hnth. simpl in *.
    autorewrite with len in Hu0, decltyeq |- *.
    simpl in Hu0, decltyeq |- *.
    move: Hu0 decltyeq.
    assert (narg < context_assumptions (cstr_args cdecl)).
    eapply nth_error_Some_length in H0. lia.
    replace (context_assumptions (cstr_args cdecl) -
      S (context_assumptions (cstr_args cdecl) - S narg))
      with narg by lia.
    move=> Hu0 decltyeq.
    rewrite -Hty1. clear decltyeq.
    rewrite Hty2.
    unfold projection_type'.
    set (indsubst1 := inds _ _ _).
    set (indsubst := inds _ _ _).
    set (projsubst := projs _ _ _).
    rewrite - !subst_instance_subst.
    rewrite -subst_instance_lift.
    rewrite - !subst_instance_subst.
    epose proof (commut_lift_subst_rec _ _ 1 narg narg).
    rewrite Nat.add_1_r in H2. rewrite <- H2 => //. clear H2.
    rewrite (subst_app_decomp [_]).
    autorewrite with len. rewrite heq_length.
    simpl. rewrite lift_mkApps. simpl.
    rewrite (distr_subst [_]). simpl.
    autorewrite with len. rewrite {2}/projsubst projs_length.
    rewrite simpl_subst_k // subst_instance_projs.
    epose proof (subst_app_simpl (List.rev (firstn narg (skipn (ind_npars mdecl) args0))) _ 0).
    autorewrite with len in H2.  simpl in H2.
    assert(#|firstn narg (skipn (ind_npars mdecl) args0)| = narg).
    { rewrite firstn_length_le. rewrite skipn_length. lia. lia. lia. }
    rewrite H3 in H2. rewrite <- H2. clear H2.
    rewrite subst_app_decomp.
    epose proof (subst_app_simpl 
    (map
    (subst0
        [mkApps (tConstruct i 0 u1) (map (lift0 (ind_npars mdecl)) args0)])
    (projs i (ind_npars mdecl) narg))).
    autorewrite with len in H2.
    rewrite -H2. clear H2.
    rewrite subst_app_decomp.
    autorewrite with len.
    rewrite (distr_subst (List.rev args)).
    autorewrite with len.
    assert (map (subst0 (List.rev args))
    (map (subst_instance u) (extended_subst (ind_params mdecl) 0))  = 
      iparsubst) as ->. 
    { rewrite firstn_all2 in iparsubst0. lia.
      rewrite subst_instance_extended_subst.
      pose proof (inst_ctx_subst iparsubst0).
      eapply context_subst_extended_subst in X2.
      rewrite X2. eapply map_ext.
      intros. now rewrite subst_inst Upn_0. }
    autorewrite with len in cum. simpl in cum.
    move: Hdecl'.
    rewrite /pargctxu /argctxu /argsu.
    rewrite !smash_context_subst_empty.
    rewrite -(subst_instance_smash _ _ []).
    rewrite !nth_error_subst_context.
    rewrite nth_error_map Hdecl. simpl => [= Hdecl'].
    subst decl'. simpl in cum.
    autorewrite with len in cum; simpl in cum. 
    assert(context_assumptions (cstr_args cdecl) -
      S (context_assumptions (cstr_args cdecl) - S narg) = narg) by lia.
    rewrite H2 in cum. 
    set (idx := S (context_assumptions (cstr_args cdecl) - S narg)) in *.
    assert (wfpargctxu1 : wf_local Σ (Γ ,,, skipn idx (smash_context [] pargctxu1))).
    { simpl. apply wf_local_app_skipn. apply wf_local_smash_end; auto.
      apply idxsubst0. }
    destruct cum as [[cr mapd] cdecl].
    destruct decl'' as [na [b|] ty]; simpl in mapd; try discriminate.
    depelim cdecl. rename c into cum.
    eapply (substitution_cumul _ Γ (skipn idx (smash_context [] pargctxu1)) [] 
      (skipn idx (List.rev (skipn (ind_npars mdecl) args0)))) in cum.
    all:auto.
    2:{ eapply subslet_skipn.
        eapply spine_subst_smash in idxsubst0; eauto. eapply idxsubst0. }
    assert (skipn idx (List.rev (skipn (ind_npars mdecl) args0)) = (List.rev (firstn narg (skipn (ind_npars mdecl) args0)))) as eq.
    { rewrite /idx skipn_rev. lia_f_equal. rewrite skipn_length; lia. }
    assert (narg = #|List.rev (firstn narg (skipn (ind_npars mdecl) args0))|).
    { autorewrite with len. rewrite firstn_length_le ?skipn_length; lia. }
    rewrite eq in cum. 
    rewrite subst_context_nil in cum. simpl in cum.
    rewrite -(subst_app_simpl' _ _ 0) in cum => //.
    rewrite subst_app_decomp in cum.
    etransitivity; [eapply cum|clear cum].
    rewrite -(subst_app_simpl' _ _ 0) //.
    rewrite subst_app_decomp.
    rewrite (subslet_length iparsubst0); autorewrite with len.
    assert (wf_local Σ (Γ ,,, subst_instance u (ind_params mdecl))).
    { eapply weaken_wf_local; eauto. eapply on_minductive_wf_params => //. pcuic. }
    eapply (substitution_cumul _ _ _ []); eauto. eapply iparsubst0.
    simpl.
    rewrite (distr_subst_rec _ _ _ #|ind_params mdecl| 0).
    autorewrite with len. simpl.
    eapply (untyped_subst_cumul (_ ,,, _) _ _ []); auto.
    { eapply subslet_untyped_subslet. rewrite -(subst_instance_length u).
      eapply subslet_lift; eauto. rewrite -eq.
      eapply spine_subst_smash in idxsubst0; eauto. 
      eapply subslet_skipn. eapply idxsubst0. }
    { rewrite subst_projs_inst.
      specialize (projsubsl (Γ ,,, subst_instance u (ind_params mdecl))).
      rewrite -projs_inst_lift projs_inst_subst.
      rewrite -{1}H2 -projs_inst_skipn.
      eapply untyped_subslet_skipn. eapply (projsubsl _ u). }
    { rewrite subst_projs_inst.
      rewrite !map_map_compose. eapply All2_map.
      eapply All2_from_nth_error.
      { autorewrite with len. lia. }
      intros n x x' Hn nth nth'.
      rewrite nth_error_projs_inst in nth'.
      lia. noconf nth'.
      simpl. rewrite lift_mkApps subst_mkApps /=.
      rewrite (map_map_compose _ _ _ (lift0 (ind_npars mdecl))).
      rewrite map_lift_lift map_map_compose.
      symmetry. eapply red_conv.
      etransitivity. eapply red1_red; constructor.
      eapply (f_equal (option_map (lift0 #|ind_params mdecl|))) in nth.
      simpl in nth. rewrite <-nth, nth_error_rev_inv; autorewrite with len; try lia.
      rewrite H3 Nat.add_comm.
      setoid_rewrite map_subst_lift_ext; try lia.
      2:autorewrite with len; lia.
      rewrite nth_error_map. f_equal.
      rewrite firstn_skipn_comm nth_error_skipn.
      rewrite -{1}[args0](firstn_skipn (ind_npars mdecl + narg)).
      rewrite nth_error_app1 // firstn_length_le; autorewrite with len; try lia.
      reflexivity. }
    { simpl. autorewrite with len.
      rewrite -(subst_instance_length u (ind_params mdecl)).
      eapply weakening_wf_local; auto. }
    simpl.
    unfold indsubst. 
    set (inds' := inds _ _ _).
    change (map (subst_instance u) inds') with (subst_instance u inds').
    rewrite instantiate_inds => //. pcuic.
    rewrite (subst_closedn (List.rev args)); [|reflexivity].
    eapply (closedn_subst _ 0).  
    eapply declared_inductive_closed_inds; eauto.
    simpl. autorewrite with len.
    rewrite closedn_subst_instance.
    clear projsubsl.
    eapply closed_wf_local in wfdecl.
    rewrite closedn_ctx_app in wfdecl.
    move/andb_and: wfdecl => [_ wfdecl].
    autorewrite with len in wfdecl.
    simpl in wfdecl.
    eapply closedn_ctx_decl in wfdecl; eauto.
    autorewrite with len in wfdecl.
    simpl in wfdecl.
    eapply closed_upwards. eauto.
    lia. auto. *)

  - (* Proj congruence: discriminee reduction *) 
    eapply type_Cumul'; [econstructor|..]; eauto.
    eapply validity; eauto.
    instantiate (1:= tProj p c).
    econstructor; eauto.
    eapply conv_cumul.
    rewrite (subst_app_simpl [c']) (subst_app_simpl [c]).
    set(bann := {| binder_name := nAnon; binder_relevance := idecl.(ind_relevance) |}).
    eapply (untyped_subst_conv Γ [vass bann (mkApps (tInd p.1.1 u) args)] 
      [vass bann (mkApps (tInd p.1.1 u) args)] []); auto.
    repeat constructor. repeat constructor. constructor.
    now apply conv_sym, red_conv, red1_red. constructor.
    simpl. constructor. auto. red.
    eapply validity in typec; auto.

  - (* Fix congruence *)
    symmetry in H0; apply mkApps_Fix_spec in H0. simpl in H0. subst args.
    simpl. destruct narg; discriminate.
  
  - (* Fix congruence: type reduction *)
    assert(fixl :#|fix_context mfix| = #|fix_context mfix1|) by now (rewrite !fix_context_length; apply (OnOne2_length o)).
    assert(convctx : conv_context Σ (Γ ,,, fix_context mfix) (Γ ,,, fix_context mfix1)).
    { clear -wf X o fixl. 
      eapply PCUICContextRelation.All2_fold_app => //.
      apply conv_ctx_refl. clear X.
      apply conv_decls_fix_context => //.
      induction o; constructor.
      destruct p. split. now noconf e.
      now noconf e.
      apply All2_refl. intros; split; reflexivity.
      split; reflexivity.
      apply IHo. rewrite !fix_context_length in fixl |- *; simpl in *. lia. }
    assert(All (fun d => isType Σ Γ (dtype d)) mfix).
    { apply (All_impl X0).
      now intros x [s' [Hs' _]]; exists s'. }
    assert(All (fun d => isType Σ Γ (dtype d)) mfix1).
    { apply (OnOne2_All_All o X0).
      * intros x [s [Hs IH]].
        now exists s.
      * intros x y [red eq] [s [Hs IH]].
        now exists s; apply IH. }
    assert (wf_local Σ (Γ ,,, fix_context mfix1)).
    { apply All_mfix_wf; auto. }
    destruct (OnOne2_nth_error _ _ _ decl _ o heq_nth_error) as [decl' [eqnth disj]].
    eapply type_Cumul'.
    econstructor; eauto.
    * eapply (fix_guard_red1 _ _ _ _ 0); eauto.
      constructor; eauto.
    * eapply (OnOne2_All_mix_left X0) in o.
      apply (OnOne2_All_All o X1).
      + intros x [Hb IH].
        eapply context_conversion; eauto.
        now rewrite -fixl.
      + move=> [na ty b rarg] [na' ty' b' rarg'] /= [[red eq] [s [Hs IH]]] [Hb IH'].
        noconf eq.
        eapply context_conversion; eauto.
        rewrite -fixl.
        eapply type_Cumul'. eapply Hb.
        exists s. specialize (IH _ red).
        eapply (weakening _ _ _ _ (tSort _)); auto.
        apply All_mfix_wf; auto. 
        apply (weakening_cumul _ _ []); auto.
        now apply red_cumul, red1_red.

    * eapply wf_fixpoint_red1_type; eauto.
    * eapply All_nth_error in X2; eauto.
    * apply conv_cumul, conv_sym, red_conv. destruct disj as [<-|red].
      reflexivity. apply red1_red. apply red.

  - (* Fix congruence in body *)
    assert(fixl :#|fix_context mfix| = #|fix_context mfix1|) by now (rewrite !fix_context_length; apply (OnOne2_length o)).
    assert(convctx : fix_context mfix = fix_context mfix1).
    { clear -wf o.
      change fix_context with (fix_context_gen 0).
      generalize 0. induction o.
      destruct p as [_ eq]. noconf eq. simpl in H; noconf H.
      simpl. intros. now rewrite H H0.
      simpl. intros n; f_equal. apply IHo. }
    assert(All (fun d => isType Σ Γ (dtype d)) mfix).
    { apply (All_impl X0).
      now intros x [s' [Hs' _]]; exists s'. }
    assert(All (fun d => isType Σ Γ (dtype d)) mfix1).
    { apply (OnOne2_All_All o X0).
      * intros x [s [Hs IH]].
        now exists s.
      * intros x y [red eq] [s [Hs IH]].
        noconf eq. simpl in H0; noconf H0. rewrite -H2.
        now exists s; apply Hs. }
    assert (wf_local Σ (Γ ,,, fix_context mfix1)).
    { apply All_mfix_wf; auto. }
    destruct (OnOne2_nth_error _ _ _ decl _ o heq_nth_error) as [decl' [eqnth disj]].
    eapply type_Cumul'.
    econstructor; eauto.
    * eapply (fix_guard_red1 _ _ _ _ 0); eauto.
      apply fix_red_body; eauto.
    * eapply (OnOne2_All_mix_left X0) in o.
       apply (OnOne2_All_All o X1).
      + intros x [Hb IH].
        eapply context_conversion; eauto.
        now rewrite -fixl.
        rewrite convctx. apply conv_ctx_refl.
      + move=> [na ty b rarg] [na' ty' b' rarg'] /= [[red eq] [s [Hs IH]]] [Hb IH'].
        noconf eq.
        now rewrite -convctx.        
    * eapply wf_fixpoint_red1_body; eauto.
    * eapply All_nth_error in X2; eauto.
    * apply conv_cumul, conv_sym, red_conv. destruct disj as [<-|[_ eq]].
      reflexivity. noconf eq. simpl in H0; noconf H0. rewrite H2; reflexivity.

  - (* CoFix congruence type *)
    assert(fixl :#|fix_context mfix| = #|fix_context mfix1|) by now (rewrite !fix_context_length; apply (OnOne2_length o)).
    assert(convctx : conv_context Σ (Γ ,,, fix_context mfix) (Γ ,,, fix_context mfix1)).
    { clear -wf X o fixl.
      eapply PCUICContextRelation.All2_fold_app => //.
      apply conv_ctx_refl. clear X.
      apply conv_decls_fix_context => //.
      induction o; constructor; try split; auto;
      try (destruct p; now noconf e).
      apply All2_refl; split; reflexivity.
      apply IHo. rewrite !fix_context_length /= in fixl |- *; lia. }
    assert(All (fun d => isType Σ Γ (dtype d)) mfix).
    { apply (All_impl X0).
      now intros x [s' [Hs' _]]; exists s'. }
    assert(All (fun d => isType Σ Γ (dtype d)) mfix1).
    { apply (OnOne2_All_All o X0).
      * intros x [s [Hs IH]].
        now exists s.
      * intros x y [red eq] [s [Hs IH]].
        now exists s; apply IH. }
    assert (wf_local Σ (Γ ,,, fix_context mfix1)).
    { apply All_mfix_wf; auto. }
    destruct (OnOne2_nth_error _ _ _ decl _ o heq_nth_error) as [decl' [eqnth disj]].
    eapply type_Cumul'.
    econstructor; eauto.
    * eapply (cofix_guard_red1 _ _ _ _ 0); eauto.
      constructor; eauto.
    * eapply (OnOne2_All_mix_left X0) in o.
      apply (OnOne2_All_All o X1).
      + intros x [Hb IH].
        eapply context_conversion; eauto.
        now rewrite -fixl.
      + move=> [na ty b rarg] [na' ty' b' rarg'] /= [[red eq] [s [Hs IH]]] [Hb IH'].
        noconf eq. 
        eapply context_conversion; eauto.
        rewrite -fixl.
        eapply type_Cumul'. eapply Hb.
        exists s. specialize (IH _ red).
        eapply (weakening _ _ _ _ (tSort _)); auto.
        apply All_mfix_wf; auto. 
        apply (weakening_cumul _ _ []); auto.
        now apply red_cumul, red1_red.
    * eapply wf_cofixpoint_red1_type; eauto.
    * eapply All_nth_error in X2; eauto.
    * apply conv_cumul, conv_sym, red_conv. destruct disj as [<-|red].
      reflexivity. apply red1_red. apply red.

  - (* CoFix congruence in body *)
    assert(fixl :#|fix_context mfix| = #|fix_context mfix1|) by now (rewrite !fix_context_length; apply (OnOne2_length o)).
    assert(convctx : fix_context mfix = fix_context mfix1).
    { clear -wf o.
      change fix_context with (fix_context_gen 0).
      generalize 0. induction o.
      destruct p as [_ eq]. noconf eq. simpl in H; noconf H.
      simpl. intros. now rewrite H H0.
      simpl. intros n; f_equal. apply IHo. }
    assert(All (fun d => isType Σ Γ (dtype d)) mfix).
    { apply (All_impl X0).
      now intros x [s' [Hs' _]]; exists s'. }
    assert(All (fun d => isType Σ Γ (dtype d)) mfix1).
    { apply (OnOne2_All_All o X0).
      * intros x [s [Hs IH]].
        now exists s.
      * intros x y [red eq] [s [Hs IH]].
        noconf eq. simpl in H0; noconf H0. rewrite -H2.
        now exists s; apply Hs. }
    assert (wf_local Σ (Γ ,,, fix_context mfix1)).
    { apply All_mfix_wf; auto. }
    destruct (OnOne2_nth_error _ _ _ decl _ o heq_nth_error) as [decl' [eqnth disj]].
    eapply type_Cumul'.
    econstructor; eauto.
    * eapply (cofix_guard_red1 _ _ _ _ 0); eauto.
      apply cofix_red_body; eauto.
    * eapply (OnOne2_All_mix_left X0) in o.
      apply (OnOne2_All_All o X1).
      + intros x [Hb IH].
        now rewrite -convctx.
      + move=> [na ty b rarg] [na' ty' b' rarg'] /= [[red eq] [s [Hs IH]]] [Hb IH'].
        noconf eq.
        now rewrite -convctx. 
    * now eapply wf_cofixpoint_red1_body.
    * eapply All_nth_error in X2; eauto.
    * apply conv_cumul, conv_sym, red_conv. destruct disj as [<-|[_ eq]].
      reflexivity. noconf eq. simpl in H0; noconf H0. rewrite H2; reflexivity.
 
  - (* Conversion *)
    specialize (forall_u _ Hu).
    eapply type_Cumul; eauto. Unshelve. todo "case".
Qed.

Definition sr_stmt {cf:checker_flags} (Σ : global_env_ext) Γ t T :=
  forall u, red Σ Γ t u -> Σ ;;; Γ |- u : T.

Theorem subject_reduction {cf:checker_flags} : 
  forall (Σ : global_env_ext) Γ t u T, wf Σ -> Σ ;;; Γ |- t : T -> red Σ Γ t u -> Σ ;;; Γ |- u : T.
Proof.
  intros * wfΣ Hty Hred.
  induction Hred; eauto.
  eapply (env_prop_typing _ _ sr_red1) in Hty; eauto with wf.
Qed.

Lemma subject_reduction1 {cf Σ} {wfΣ : wf Σ} {Γ t u T}
  : Σ ;;; Γ |- t : T -> red1 Σ Γ t u -> Σ ;;; Γ |- u : T.
Proof.
  intros. eapply subject_reduction; try eassumption.
  now apply red1_red.
Defined.

Section SRContext.
  Context {cf:checker_flags}.

  Definition cumul_red_l' {Σ} {wfΣ : wf Σ} Γ t u :
      red Σ Γ t u ->
      Σ ;;; Γ |- t <= u.
  Proof.
    intros h.
    induction h using red_rect'.
    - eapply cumul_refl'.
    - eapply cumul_trans ; try eassumption.
      eapply cumul_red_l.
      + eassumption.
      + eapply cumul_refl'.
  Defined.

  Hint Constructors OnOne2_local_env : aa.
  Hint Unfold red1_ctx : aa.

  Lemma red1_ctx_app (Σ : global_env) Γ Γ' Δ :
    red1_ctx Σ Γ Γ' ->
    red1_ctx Σ (Γ ,,, Δ) (Γ' ,,, Δ).
  Proof.
    induction Δ. trivial.
    intro H. simpl. constructor. now apply IHΔ.
  Qed.

  Lemma red1_red_ctx (Σ : global_env) Γ Γ' :
    red1_ctx Σ Γ Γ' ->
    red_ctx Σ Γ Γ'.
  Proof.
    induction 1; cbn in *.
    - constructor; try reflexivity.
      destruct p; subst.
      constructor. cbn; eauto using red1_red.
    - constructor; try reflexivity.
      destruct p as [-> [[? []]|[? []]]]; constructor; cbn; eauto using red1_red.
    - constructor; auto. reflexivity.
  Qed.

  Lemma nth_error_red1_ctx (Σ : global_env) Γ Γ' n decl :
    wf Σ ->
    nth_error Γ n = Some decl ->
    red1_ctx Σ Γ Γ' ->
    ∑ decl', nth_error Γ' n = Some decl'
              × red Σ Γ' (lift0 (S n) (decl_type decl))
              (lift0 (S n) (decl_type decl')).
  Proof.
    intros wfΣ h1 h2; induction h2 in n, h1 |- *.
    - destruct n.
      + inversion h1; subst. exists (vass na t').
        destruct p as [<- red].
        split; cbnr.
        eapply (weakening_red_0 _ [_]); tas; cbnr.
        apply red1_red; tas.
      + exists decl. split; tas. apply refl_red.
    - destruct n.
      + inversion h1; subst.
        destruct p as [<- [[? []]|[? []]]].
        -- exists (vdef na b t').
           split; cbnr.
           eapply (weakening_red_0 _ [_]); tas; cbnr.
           apply red1_red; tas.
        -- exists (vdef na b' t).
           split; cbnr.
      + exists decl. split; tas. apply refl_red.
    - destruct n.
      + exists d. split; cbnr. inv h1; apply refl_red.
      + cbn in h1. specialize (IHh2 _ h1).
        destruct IHh2 as [decl' [X1 X2]].
        exists decl'. split; tas.
        rewrite !(simpl_lift0 _ (S n)).
        eapply (weakening_red_0 _ [_]); tas; cbnr.
  Qed.

  Lemma wf_local_isType_nth {Σ} {wfΣ : wf Σ} Γ n decl :
    wf_local Σ Γ ->
    nth_error Γ n = Some decl ->
    ∑ s, Σ ;;; Γ |- lift0 (S n) (decl_type decl) : tSort s.
  Proof.
    induction n in Γ, decl |- *; intros hΓ e; destruct Γ;
      cbn; inversion e; inversion hΓ; subst.
    all: try (destruct X0 as [s Ht]; exists s;
              eapply (weakening _ _ [_] _ (tSort s)); tas).
    - eapply IHn in H0; tas. destruct H0 as [s Ht]. exists s.
      rewrite simpl_lift0.
      eapply (weakening _ _ [_] _ (tSort s)); tas; cbnr.
    - eapply IHn in H0; tas. destruct H0 as [s Ht]. exists s.
      rewrite simpl_lift0.
      eapply (weakening _ _ [_] _ (tSort s)); tas; cbnr.
  Qed.

  Ltac invs H := inversion H; subst.
  Ltac invc H := inversion H; subst; clear H.

  Lemma type_reduction {Σ} {wfΣ : wf Σ} {Γ t A B} : 
    Σ ;;; Γ |- t : A -> red Σ Γ A B -> Σ ;;; Γ |- t : B.
  Proof.
    intros Ht Hr.
    eapply type_Cumul'. eassumption.
    2: now eapply cumul_red_l'.
    destruct (validity Ht) as [s HA]. 
    exists s; eapply subject_reduction; eassumption.
  Defined.

  Lemma subject_reduction_ctx {Σ} {wfΣ : wf Σ} Γ Γ' t T :
    red1_ctx Σ Γ Γ' ->
    Σ ;;; Γ |- t : T -> Σ ;;; Γ' |- t : T.
  Proof.
    assert(OnOne2_local_env
      (on_one_decl
         (fun (Δ : context) (t t' : term) => red1 Σ.1 Δ t t')) Γ Γ' ->
         conv_context Σ Γ Γ').
    { clear. induction 1.
      - destruct p as [<- r]. constructor; auto.
        apply conv_ctx_refl. constructor. reflexivity.
        now apply red_conv, red1_red.
      - destruct p; subst. constructor.
        apply conv_ctx_refl.
        destruct s as [[red ->]|[red ->]].
        constructor; pcuics. now apply red_conv, red1_red.
        constructor. pcuic. now apply red_conv, red1_red.
        reflexivity.
      - constructor; auto. reflexivity. }
    intros r H.
    specialize (X r).
    assert(wf_local Σ Γ').
    apply typing_wf_local in H.
    induction H in Γ', r, X |-  *; depelim r.
    - constructor; auto. cbn in o.
      destruct o as [<- r].
      destruct t1 as [s Hs]. exists s.
      eapply subject_reduction1 in Hs; eauto.
    - depelim X.
      constructor; auto. 
      destruct t1 as [s Hs]. exists s.
      eapply context_conversion; eauto.
    - depelim X.
      red in o. destruct t1 as [s Hs].
      simpl in t2.
      destruct o as [<- [[r ->]|[r <-]]].
      constructor; auto. exists s; auto.
      eapply subject_reduction1; eauto.
      red. eapply type_reduction; tea. pcuic.
      constructor; auto.
      exists s; eapply subject_reduction; tea.
      reflexivity.
      red. eapply subject_reduction1; tea.
    - depelim X. destruct t1 as [s Hs].
      simpl in t2.
      constructor; auto. exists s; auto.
      eapply context_conversion; eauto.
      red; eapply context_conversion; eauto.
    - eapply context_conversion; eauto.
  Qed.
  
  Lemma wf_local_red1 {Σ} {wfΣ : wf Σ} {Γ Γ'} :
    red1_ctx Σ Γ Γ' -> wf_local Σ Γ -> wf_local Σ Γ'.
  Proof.
    induction 1; cbn in *.
    - destruct p as [-> r]. intro e. inversion e; subst; cbn in *.
      constructor; tas. destruct X0 as [s Ht]. exists s.
      eapply subject_reduction1; tea.
    - intro e. inversion e; subst; cbn in *.
      destruct p as [-> [[? []]|[? []]]]; constructor; cbn; tas.
      + destruct X0; eexists; eapply subject_reduction1; tea.
      + eapply type_Cumul'; tea.
        destruct X0. exists x. eapply subject_reduction1; tea.
        econstructor 2. eassumption. reflexivity.
      + eapply subject_reduction1; tea.
    - intro H; inversion H; subst; constructor; cbn in *; auto.
      + destruct X1 as [s Ht]. exists s.
        eapply subject_reduction_ctx; tea.
      + destruct X1 as [s Ht]. exists s.
        eapply subject_reduction_ctx; tea.
      + eapply subject_reduction_ctx; tea.
  Qed.

  Lemma red_ctx_clos_rt_red1_ctx Σ : Relation_Properties.inclusion (red_ctx Σ)
      (clos_refl_trans (red1_ctx Σ)).
  Proof.
    intros x y H.
    induction H; try firstorder.
    destruct p.
    - transitivity (Γ ,, vass na t').
      eapply clos_rt_OnOne2_local_env_incl. constructor.
      cbn. split; auto.
      clear r H.
      induction IHAll2_fold; try solve[repeat constructor; auto].
      etransitivity; eauto.
    - transitivity (Γ ,, vdef na b t').
      * eapply clos_rt_OnOne2_local_env_incl. constructor 2.
        cbn. split; auto.
      * transitivity (Γ ,, vdef na b' t').
        + eapply clos_rt_OnOne2_local_env_incl.
          constructor 2. cbn. split; auto.
        + clear -IHAll2_fold.
          induction IHAll2_fold; try solve[repeat constructor; auto].
          etransitivity; eauto.
  Qed.

  Lemma wf_local_red {Σ} {wfΣ : wf Σ} {Γ Γ'} :
    red_ctx Σ Γ Γ' -> wf_local Σ Γ -> wf_local Σ Γ'.
  Proof.
    intros h. red in h. apply red_ctx_clos_rt_red1_ctx in h.
    induction h; eauto using wf_local_red1.
  Qed.
 
  Lemma eq_context_upto_names_upto_names Γ Δ :
    eq_context_upto_names Γ Δ -> Γ ≡Γ Δ.
  Proof.
    induction 1; cbnr; try constructor; eauto.
    depelim p; constructor; subst; auto.
    all:cbnr; eauto.
  Qed.
  
  Lemma wf_local_subst1 {Σ} {wfΣ : wf Σ} Γ na b t Γ' :
      wf_local Σ (Γ ,,, [],, vdef na b t ,,, Γ') ->
      wf_local Σ (Γ ,,, subst_context [b] 0 Γ').
  Proof.
    induction Γ' as [|d Γ']; [now inversion 1|].
    change (d :: Γ') with (Γ' ,, d).
    destruct d as [na' [bd|] ty]; rewrite !app_context_cons; intro HH.
    - rewrite subst_context_snoc0. simpl.
      inversion HH; subst; cbn in *. destruct X0 as [s X0].
      change (Γ,, vdef na b t ,,, Γ') with (Γ ,,, [vdef na b t] ,,, Γ') in *.
      assert (subslet Σ Γ [b] [vdef na b t]). {
        pose proof (cons_let_def Σ Γ [] [] na b t) as XX.
        rewrite !subst_empty in XX. apply XX. constructor.
        apply wf_local_app_l in X. inversion X; subst; cbn in *; assumption.
      }
      constructor; cbn; auto.
      1: exists s. 1: unfold PCUICTerm.tSort.
      1: change (tSort s) with (subst [b] #|Γ'| (tSort s)).
      all: eapply substitution; tea.
    - rewrite subst_context_snoc0. simpl.
      inversion HH; subst; cbn in *. destruct X0 as [s X0].
      change (Γ,, vdef na b t ,,, Γ') with (Γ ,,, [vdef na b t] ,,, Γ') in *.
      assert (subslet Σ Γ [b] [vdef na b t]). {
        pose proof (cons_let_def Σ Γ [] [] na b t) as XX.
        rewrite !subst_empty in XX. apply XX. constructor.
        apply wf_local_app_l in X. inversion X; subst; cbn in *; assumption. }
      constructor; cbn; auto. exists s.
      unfold PCUICTerm.tSort.
      change (tSort s) with (subst [b] #|Γ'| (tSort s)).
      all: eapply substitution; tea.
  Qed.


  Lemma red_ctx_app_context_l {Σ Γ Γ' Δ}
    : red_ctx Σ Γ Γ' -> red_ctx Σ (Γ ,,, Δ) (Γ' ,,, Δ).
  Proof.
    induction Δ as [|[na [bd|] ty] Δ]; [trivial| |];
      intro H; simpl; constructor; cbn; try constructor; eauto; now apply IHΔ.
  Qed.

  Lemma isType_red1 {Σ : global_env_ext} {wfΣ : wf Σ} {Γ A B} :
     isType Σ Γ A ->
     red1 Σ Γ A B ->
     isType Σ Γ B.
   Proof.
     intros [s Hs] red.
     exists s. eapply subject_reduction1; eauto.
   Qed.

   Lemma isWfArity_red1 {Σ} {wfΣ : wf Σ} {Γ A B} :
     isWfArity Σ Γ A ->
     red1 Σ Γ A B ->
     isWfArity Σ Γ B.
   Proof.
     intros [isty H] re.
     split. eapply isType_red1; eauto.
     clear isty; revert H.
     induction re using red1_ind_all.
     all: intros [ctx [s H1]]; cbn in *; try discriminate.
     - rewrite destArity_app in H1.
       case_eq (destArity [] b'); [intros [ctx' s']|]; intro ee;
         [|rewrite ee in H1; discriminate].
       pose proof (subst_destArity [] b' [b] 0) as H; cbn in H.
       rewrite ee in H. eexists _, s'. eassumption.
     - rewrite destArity_tFix in H1; discriminate.
     - rewrite destArity_app in H1.
       case_eq (destArity [] b'); [intros [ctx' s']|]; intro ee;
         rewrite ee in H1; [|discriminate].
       eexists _, s'. cbn. rewrite destArity_app ee. reflexivity.
     - rewrite destArity_app in H1.
       case_eq (destArity [] b'); [intros [ctx' s']|]; intro ee;
         rewrite ee in H1; [|discriminate].
       eexists _, s'. cbn. rewrite destArity_app ee. reflexivity.
     - rewrite destArity_app in H1.
       case_eq (destArity [] b'); [intros [ctx' s']|]; intro ee;
         rewrite ee in H1; [|discriminate].
       forward IHre. { eexists _, s'; tea. }
       destruct IHre as [ctx'' [s'' ee']].
       eexists _, s''. cbn. rewrite destArity_app ee'. reflexivity.
     - rewrite destArity_app in H1.
       case_eq (destArity [] M2); [intros [ctx' s']|]; intro ee;
         rewrite ee in H1; [|discriminate].
       eexists _, s'. cbn. rewrite destArity_app ee. reflexivity.
     - rewrite destArity_app in H1.
       case_eq (destArity [] M2); [intros [ctx' s']|]; intro ee;
         rewrite ee in H1; [|discriminate].
       forward IHre. { eexists _, s'; tea. }
       destruct IHre as [ctx'' [s'' ee']].
       eexists _, s''. cbn. rewrite destArity_app ee'. reflexivity.
   Qed.

   Lemma isWfArity_red {Σ} {wfΣ : wf Σ} {Γ A B} :
     isWfArity Σ Γ A ->
     red Σ Γ A B ->
     isWfArity Σ Γ B.
   Proof.
     induction 2 using red_rect'.
     - easy.
     - now eapply isWfArity_red1.
   Qed.

   Lemma isType_red {Σ} {wfΣ : wf Σ} {Γ T U} :
    isType Σ Γ T -> red Σ Γ T U -> isType Σ Γ U.
   Proof.
     intros [s Hs] red; exists s.
     eapply subject_reduction; eauto.
   Qed.

End SRContext.

Lemma isType_tLetIn {cf} {Σ} {HΣ' : wf Σ} {Γ} {na t A B}
  : isType Σ Γ (tLetIn na t A B)
    <~> (isType Σ Γ A × (Σ ;;; Γ |- t : A) × isType Σ (Γ,, vdef na t A) B).
Proof.
  split; intro HH.
  - destruct HH as [s H].
    apply inversion_LetIn in H; tas. destruct H as [s1 [A' [HA [Ht [HB H]]]]].
    repeat split; tas. 1: eexists; eassumption.
    apply cumul_Sort_r_inv in H.
    destruct H as [s' [H H']].
    exists s'. eapply type_reduction; tea.
    apply invert_red_letin in H; tas.
    destruct H as [[? [? [? [[[H ?] ?] ?]]]]|H].
    * discriminate.
    * etransitivity.
      2: apply weakening_red_0 with (Γ' := [_]) (N := tSort _);
        tea; reflexivity.
      exact (red_rel_all _ (Γ ,, vdef na t A) 0 t A' HΣ' eq_refl).
  - destruct HH as [HA [Ht HB]].
    destruct HB as [sB HB].
    eexists. eapply type_reduction; tas.
    * econstructor; tea.
      apply HA.π2.
    * apply red1_red.
      apply red_zeta with (b':=tSort sB).
Defined.

(** Keep at the end to not disturb asynchronous proof processing *)
Print Assumptions sr_red1.
