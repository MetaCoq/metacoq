(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICUtils
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICWeakeningEnv PCUICWeakening
     PCUICSubstitution PCUICClosed PCUICCumulativity PCUICGeneration PCUICReduction
     PCUICAlpha PCUICEquality PCUICValidity PCUICParallelReductionConfluence
     PCUICConfluence PCUICContextConversion PCUICUnivSubstitution
     PCUICConversion PCUICInversion PCUICContexts PCUICArities
     PCUICWellScopedCumulativity
     PCUICParallelReduction PCUICSpine PCUICInductives PCUICInductiveInversion.

Require Import ssreflect ssrbool.
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

(* Preservation of wf_*fixpoint *)  

Lemma wf_fixpoint_red1_type {cf Σ} {wfΣ : wf Σ} Γ mfix mfix1 : 
  wf_fixpoint Σ mfix ->
  OnOne2
  (fun x y : def term =>
   closed_red1 Σ Γ (dtype x) (dtype y)
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
    destruct (red1_it_mkProd_or_LetIn_smash redty Hnth) as 
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
   closed_red1 Σ Γ (dbody x) (dbody y)
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
   Σ ;;; Γ ⊢ dtype x ⇝ dtype y
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
  Σ ⊢ Γ ,,, Δ = Γ ,,, Δ' ->
  Σ ⊢ Γ ,,, smash_context [] Δ = Γ ,,, smash_context [] Δ'.
Proof.
  intros wf wf' cv.
  eapply context_equality_rel_app.
  apply context_equality_rel_app in cv.
  eapply context_equality_rel_smash => //.
Qed.

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

Lemma conv_context_rel_reln {cf} {Σ} {le} Γ Δ Δ' : 
  context_equality_rel le Σ Γ Δ Δ' ->
  forall acc n, reln acc n Δ = reln acc n Δ'.
Proof.
  intros [cl a]. induction a.
  - constructor.
  - intros acc n; destruct p; simpl; auto.
Qed.
    
Lemma conv_context_rel_to_extended_list {cf} {Σ} {le} {Γ Δ Δ'} : 
  context_equality_rel le Σ Γ Δ Δ' ->
  to_extended_list Δ = to_extended_list Δ'.
Proof.
  unfold to_extended_list, to_extended_list_k.
  intros; now eapply conv_context_rel_reln.
Qed.

Lemma eq_context_alpha_conv {cf} {Σ} Γ Δ Δ' : 
  All2 (compare_decls eq eq) Δ Δ' ->
  context_equality_rel false Σ Γ Δ Δ'.
Proof.
Admitted.
  (* induction 1.
  - constructor.
  - destruct r; repeat constructor; subst; auto; reflexivity.
Qed. *)

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

Lemma to_extended_list_case_branch_context ci mdecl p brctx cdecl :
  All2 (fun x y => eq_binder_annot x y.(decl_name)) brctx (cstr_args cdecl) ->
  to_extended_list (case_branch_context ci mdecl p brctx cdecl) =
  to_extended_list (cstr_args cdecl).
Proof.
  intros hlen.
  rewrite /to_extended_list /case_branch_context /case_branch_context_gen.
Admitted.
  (*rewrite to_extended_list_k_subst /expand_lets_ctx /expand_lets_k_ctx.
    to_extended_list_k_subst to_extended_list_k_lift_context to_extended_list_k_subst.
    map_subst_instance_to_extended_list_k.
  apply eq_context_alpha_to_extended_list.
  now apply eq_binder_annots_eq.*)

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

Lemma wf_pre_case_branch_context {cf} {Σ} {wfΣ : wf Σ} {Γ ci mdecl idecl p} {br : branch term} {cdecl} :
  declared_inductive Σ ci mdecl idecl ->
  wf_branch_gen cdecl (forget_types (bcontext br)) ->
  consistent_instance_ext Σ (ind_universes mdecl) (puinst p) ->
  wf_local Σ (Γ,,, case_branch_context ci mdecl p (forget_types (bcontext br)) cdecl) ->
  wf_local Σ (Γ,,, pre_case_branch_context ci mdecl (pparams p) (puinst p) cdecl).
Proof.
  move=> decli wfbr cu wf.
  eapply wf_local_alpha; tea.
  eapply All2_app. 2:eapply All2_refl; reflexivity.
  eapply All2_symP. tc.
  rewrite /case_branch_context_gen.
  eapply pre_case_branch_context_eq; eauto.
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
  2:eapply (subslet_inds decl cu).
  rewrite app_context_nil_l subst_context_app closed_ctx_subst in wf.
  rewrite closedn_subst_instance_context. eapply (declared_inductive_closed_params decl).
  now simpl in wf; len in wf.
Qed.

Instance conv_context_refl {cf} Σ {wfΣ : wf Σ} : CRelationClasses.Reflexive (All2_fold (conv_decls Σ)).
Proof.
  intros x. reflexivity.
Qed.
  
(* Instance conv_context_sym {cf} Σ {wfΣ : wf Σ} : CRelationClasses.Symmetric (All2_fold (conv_decls Σ)).
Proof.
  intros x y. now apply conv_context_sym.
Qed.

Instance conv_context_trans {cf} Σ {wfΣ : wf Σ} : CRelationClasses.Transitive (All2_fold (conv_decls Σ)).
Proof.
  intros x y z. now apply conv_context_trans.
Qed. *)

Lemma conv_ctx_set_binder_name {cf} (Σ : global_env_ext) (Γ Δ : context) (nas : list aname) :
  All2 (fun x y => eq_binder_annot x y.(decl_name)) nas Δ ->
  context_equality_rel false Σ Γ Δ (map2 set_binder_name nas Δ).
Proof.
  induction 1.
  (* * constructor.
  * destruct x, y as [na [b|] ty]; cbn; constructor; cbn; auto.
    constructor; cbn; auto. now symmetry.
    constructor; cbn; auto. now symmetry.
Qed. *)
Admitted.
Lemma OnOne2_All2_All2 {A B : Type} {l1 l2 : list A} {l3 : list B} {R1  : A -> A -> Type} {R2 R3 : A -> B -> Type} :
  OnOne2 R1 l1 l2 ->
  All2 R2 l1 l3 ->
  (forall x y, R2 x y -> R3 x y) ->
  (forall x y z, R1 x y -> R2 x z -> R3 y z) ->
  All2 R3 l2 l3.
Proof.
  intros o. induction o in l3 |- *.
  intros H; depelim H.
  intros Hf Hf'. specialize (Hf'  _ _ _ p r). constructor; auto.
  eapply All2_impl; eauto.
  intros H; depelim H.
  intros Hf. specialize (IHo _ H Hf).
  constructor; auto.
Qed.

Lemma OnOne2_All2i_All2i {A B : Type} {l1 l2 : list A} {l3 : list B} {R1  : A -> A -> Type}
  {R2 R3 : nat -> B -> A -> Type} {n} :
  OnOne2 R1 l1 l2 ->
  All2i R2 n l3 l1 ->
  (forall n x y, R2 n x y -> R3 n x y) ->
  (forall n x y z, R1 x y -> R2 n z x -> R3 n z y) ->
  All2i R3 n l3 l2.
Proof.
  intros o. induction o in n, l3 |- *.
  intros H; depelim H.
  intros Hf Hf'. specialize (Hf' _  _ _ _ p r0). constructor; auto.
  eapply All2i_impl; eauto.
  intros H; depelim H.
  intros Hf. specialize (IHo _ _ H Hf).
  constructor; auto.
Qed.

(* Lemma conv_context_set_binder_name {cf} {Σ} {wfΣ : wf Σ} {Δ nas Γ Γ'} :
  All2 (fun na decl => eq_binder_annot na decl.(decl_name)) nas Γ -> 
  conv_context_rel Σ Δ Γ Γ' ->
  conv_context_rel Σ Δ Γ (map2 set_binder_name nas Γ').
Proof.
  intros hlen h. induction h in nas, hlen |- *; case: nas hlen => //.
  * constructor.
  * move=> a l /= h. depelim h.
  * move=> h'; depelim h'.
  * move=> a l /= h'. depelim h'.
    destruct p; cbn; constructor; try constructor; cbn; eauto; try reflexivity.
    eapply IHh; eauto.
    specialize (IHh _ h'). now symmetry.
    eapply IHh; eauto.
    now symmetry.
Qed. *)

(* Lemma conv_context_set_binder_name_inv {cf} {Σ} {wfΣ : wf Σ} {Δ nas Γ Γ'} :
  All2 (fun na decl => eq_binder_annot na decl.(decl_name)) nas Γ' -> 
  conv_context_rel Σ Δ Γ (map2 set_binder_name nas Γ') ->
  conv_context_rel Σ Δ Γ Γ'.
Proof.
  intros hlen h. induction Γ' in nas, Γ, h, hlen |- *.
  * case: nas h hlen => h; depelim h; try constructor.
    move=> l h /= //.
  * depelim hlen. depelim h. depelim a0.
    destruct a => //; noconf H.
    constructor; auto. eapply IHΓ'; tea. constructor; auto. simpl in e.
    now transitivity x.
    destruct a as [na' [b''|] ty']; noconf H.
    constructor; auto. eapply IHΓ'; tea. constructor; auto.
    now transitivity x.
Qed. *)

Lemma OnOne2_local_env_forget_types P ctx ctx' : 
  OnOne2_local_env (on_one_decl P) ctx ctx' ->
  forget_types ctx = forget_types ctx'.
Proof.
  induction 1; simpl.
  - depelim p; subst; auto.
  - depelim p; subst; auto.
  - f_equal; auto.
Qed.

(* Lemma OnOne2_local_env_All Σ P Q R ctx ctx' : 
  OnOne2_local_env (on_one_decl P) ctx ctx' ->
  All_local_env (lift_typing Q Σ) ctx -> 
  (forall Γ t t' ty, All_local_env (lift_typing R Σ) Γ -> 
    lift_typing Q Σ Γ t ty -> P Γ t t' -> lift_typing R Σ Γ t' ty) ->
  (forall Γ, All_local_env (lift_typing Q Σ) Γ -> All_local_env (lift_typing R Σ) Γ) ->
  All_local_env (lift_typing R Σ) ctx'.
Proof.
  intros o a H.
  induction o in a |- *; simpl.
  - depelim p; depelim a; constructor; auto.
    destruct l as [s Hs]; exists s. eauto.
    specialize (H Γ t t' (Some (tSort s))). simpl in H. eauto.
  - depelim p; subst; auto. depelim a.
    destruct l as [s' Hs].
    intros IH. 
    destruct s as [[? <-]|[? <-]]; subst; constructor; auto.
    specialize (H Γ t t' None). eapply H; eauto.
    now exists s'.
    specialize (H Γ b b (Some t')). eapply H; eauto.
    now exists s'.
    
    exists s'; eauto. specialize (H Γ t' b t). eapply H. eauto. exact Hs.
  - f_equal; auto.
Qed. *)
From MetaCoq.PCUIC Require Import PCUICContextReduction PCUICOnFreeVars.

(* Lemma red_one_decl_conv_context {cf} {Σ} {wfΣ : wf Σ} {Γ Δ Δ'} : 
  OnOne2_local_env (on_one_decl (fun Δ : context => red1 Σ (Γ ,,, Δ))) Δ Δ' ->
  conv_context Σ (Γ ,,, Δ) (Γ ,,, Δ').
Proof.
  intros o.
  eapply red_ctx_conv_context.
  eapply red_ctx_red_context.
  eapply red_context_app. reflexivity.
  apply red_ctx_rel_red_context_rel; tea.
  constructor. exact o.
Qed. *)

Lemma red_one_decl_red_ctx {cf} {Σ} {wfΣ : wf Σ} {Γ Δ Δ'} : 
  is_closed_context (Γ ,,, Δ) ->
  OnOne2_local_env (on_one_decl (fun Δ : context => red1 Σ (Γ ,,, Δ))) Δ Δ' ->
  red_ctx Σ (Γ ,,, Δ) (Γ ,,, Δ').
Proof.
  intros iscl o.
  eapply red_ctx_red_context.
  apply red_context_app.
  eapply red_context_refl.
  apply red_ctx_rel_red_context_rel. tea.
  now apply on_free_vars_ctx_on_ctx_free_vars_closedP_impl.
  constructor. exact o.
Qed.

Lemma into_closed_red_ctx {cf} {Σ} {wfΣ : wf Σ} {Γ Δ} : 
  is_closed_context Γ ->
  red_ctx Σ Γ Δ ->
  closed_red_ctx Σ Γ Δ.
Proof.
  intros iscl red.
  apply on_free_vars_ctx_All_fold in iscl.
  eapply All2_fold_All_fold_mix_left in red; tea. cbn in red. clear iscl.
  eapply All2_fold_impl_ind ; tea.
  intros ???? IH IH' [wf ad].
  eapply All_decls_on_free_vars_impl; tea.
  intros t t' clt redt.
  eapply into_closed_red; tea.
  eapply All2_fold_prod_inv in IH as [IH _].
  eapply All2_fold_All_left in IH.
  now eapply on_free_vars_ctx_All_fold in IH.
Qed.

Lemma red_one_decl_red_context {cf} {Σ} {wfΣ : wf Σ} {Γ Δ Δ'} : 
  is_closed_context (Γ ,,, Δ) ->
  OnOne2_local_env (on_one_decl (fun Δ : context => red1 Σ (Γ ,,, Δ))) Δ Δ' ->
  Σ ⊢ Γ ,,, Δ ⇝ Γ ,,, Δ'.
Proof.
  intros iscl o.
  eapply into_closed_red_ctx => //.
  now apply red_one_decl_red_ctx.
Qed.

Lemma red_one_decl_context_equality {cf} {Σ} {wfΣ : wf Σ} {Γ Δ Δ'} : 
  is_closed_context (Γ ,,, Δ) ->
  OnOne2_local_env (on_one_decl (fun Δ : context => red1 Σ (Γ ,,, Δ))) Δ Δ' ->
  Σ ⊢ Γ ,,, Δ = Γ ,,, Δ'.
Proof.
  intros; now eapply red_ctx_context_equality, red_one_decl_red_context.
Qed.

Lemma red1_it_mkLambda_or_LetIn_ctx {cf} {Σ} {wfΣ : wf Σ} Γ Δ Δ' u :
  OnOne2_local_env (on_one_decl (fun Δ : context => red1 Σ (Γ ,,, Δ))) Δ Δ' ->
  red1 Σ Γ (it_mkLambda_or_LetIn Δ u)
       (it_mkLambda_or_LetIn Δ' u).
Proof.
  induction 1 in u |- *.
  - depelim p; subst; rewrite /it_mkLambda_or_LetIn /=. eapply red1_it_mkLambda_or_LetIn.
    simpl. now constructor.
  - depelim p; subst; rewrite /=; eapply red1_it_mkLambda_or_LetIn.
    destruct s as [[red ->]|[red ->]]; constructor; auto.
  - simpl. apply IHX.
Qed.

(* Lemma onone_red_cont_context_subst {cf} {Σ} {wfΣ : wf Σ} Γ s s' Δ Δ' :
  wf_local Σ (Γ ,,, Δ' ,,, Δ) ->
  untyped_subslet Γ (List.rev s) Δ' ->
  untyped_subslet Γ (List.rev s') Δ' ->
  OnOne2 (red1 Σ Γ) s s' ->
  conv_context Σ (Γ ,,, subst_context (List.rev s) 0 Δ)
    (Γ ,,, subst_context (List.rev s') 0 Δ).
Proof.
  intros wf us us'.
  intros.
  eapply conv_context_app.
  eapply (conv_ctx_subst (Γ'' := [])). exact wf.
  eapply conv_context_rel_app. reflexivity.
  eapply All2_rev. eapply OnOne2_All2; tea.
  intros. now eapply red_conv, red1_red. reflexivity.
  all:tea. 
Qed. *)
Lemma closed_red1_red {Σ Γ t t'} : closed_red1 Σ Γ t t' -> Σ ;;; Γ ⊢ t ⇝ t'.
Proof.
  intros []. split => //.
  now eapply red1_red.
Qed.

Lemma ctx_inst_merge {cf} {Σ} {wfΣ : wf Σ} Γ inst inst' Δ :
  wf_local Σ (Γ ,,, (List.rev Δ)) ->
  PCUICTyping.ctx_inst
    (fun (Σ : global_env_ext) (Γ : context) (t T : term) =>
    forall u : term, closed_red1 Σ Γ t u → Σ;;; Γ |- u : T) Σ Γ inst Δ ->
  ctx_inst Σ Γ inst Δ ->
  OnOne2 (closed_red1 Σ Γ) inst inst' ->
  ctx_inst Σ Γ inst' Δ.
Proof.
  intros wf c.
  induction c in inst', wf |- *; intros ctxi; depelim ctxi; intros o.
  - depelim o.
  - depelim o. constructor. apply t0. auto.
    rewrite -(List.rev_involutive Δ).
    rewrite subst_telescope_subst_context.
    simpl in wf. rewrite - !/(app_context _ _) app_context_assoc in wf. 
    eapply ctx_inst_cumul.
    2:{ instantiate (1:=subst_context [i] 0 (List.rev Δ)).
        rewrite -subst_telescope_subst_context List.rev_involutive. exact ctxi. }
    eapply context_equality_rel_app.
    eapply conv_cumul_context.
    eapply substitution_context_equality_red_subst.
    now eapply wf_local_closed_context in wf.
    pose proof (wf_local_closed_context (typing_wf_local t2)).
    constructor; [|constructor].
    now eapply closed_red1_red.
    repeat constructor.
    specialize (t0 _ c0).
    eapply wf_local_app_inv, substitution_wf_local; tea.
    now eapply subslet_ass_tip.
    eapply wf_local_app_inv, substitution_wf_local; tea.
    now eapply subslet_ass_tip.
    constructor; auto. eapply IHc.
    rewrite -subst_context_subst_telescope.
    eapply substitution_wf_local; tea.
    repeat (constructor; tea). rewrite subst_empty; tea.
    simpl in wf. rewrite - !/(app_context _ _) app_context_assoc in wf.
    exact wf. tas. tas.
  - constructor. eapply IHc; eauto.
    simpl in wf. rewrite - !/(app_context _ _) app_context_assoc in wf.
    rewrite -subst_context_subst_telescope.
    eapply substitution_wf_local; tea.
    repeat (constructor; tea). eapply subslet_def. constructor.
    all:rewrite !subst_empty //.
    eapply wf_local_app_inv in wf as [wf _]. now depelim wf.
Qed.

Lemma ctx_inst_merge' {cf} {Σ} {wfΣ : wf Σ} Γ inst inst' Δ :
  wf_local Σ (Γ ,,, Δ) ->
  PCUICTyping.ctx_inst
    (fun (Σ : global_env_ext) (Γ : context) (t T : term) =>
    forall u : term, closed_red1 Σ Γ t u → Σ;;; Γ |- u : T) Σ Γ inst (List.rev Δ) ->
  ctx_inst Σ Γ inst (List.rev Δ) ->
  OnOne2 (closed_red1 Σ Γ) inst inst' ->
  ctx_inst Σ Γ inst' (List.rev Δ).
Proof.
  intros. eapply ctx_inst_merge; try rewrite ?(List.rev_involutive Δ) //; tea.
Qed.

Lemma All2i_All2i_mix {A B} {P Q : nat -> A -> B -> Type}
      {n} {l : list A} {l' : list B} :
  All2i P n l l' -> All2i Q n l l' -> All2i (fun i x y => (P i x y * Q i x y)%type) n l l'.
Proof.
  induction 2; simpl; intros; constructor.
  inv X; intuition auto.
  apply IHX0. inv X; intuition auto.
Qed.

Definition conj_impl {A B} : A -> (A -> B) -> A × B := fun x f => (x, f x).

Lemma shiftnP_S P n : shiftnP (S n) P =1 shiftnP 1 (shiftnP n P).
Proof. now rewrite (shiftnP_add 1). Qed.

Lemma is_open_term_snoc (Γ : context) M d : on_free_vars (shiftnP 1 (shiftnP #|Γ| xpred0)) M -> is_open_term (Γ ,, d) M.
Proof.
  rewrite /=.
  now rewrite [shiftnP (S #|Γ|) _]shiftnP_S.
Qed.

Hint Resolve is_open_term_snoc : fvs.

Ltac forward_keep H :=
  match type of H with
  ?X -> _ =>
    let H' := fresh in 
    assert (H' : X) ; [|specialize (H H')]
  end.
(** The subject reduction property of the system: *)

Definition SR_red1 {cf} Σ Γ t T :=
  forall u (Hu : closed_red1 Σ Γ t u), Σ ;;; Γ |- u : T.
  Ltac inv_on_free_vars :=
    match goal with
    | [ H : is_true (on_free_vars_decl _ _) |- _ ] => progress cbn in H
    | [ H : is_true (on_free_vars_decl _ (vdef _ _ _)) |- _ ] => unfold on_free_vars_decl, test_decl in H
    | [ H : is_true (_ && _) |- _ ] => 
      move/andP: H => []; intros
    | [ H : is_true (on_free_vars ?P ?t) |- _ ] => 
      progress (cbn in H || rewrite on_free_vars_mkApps in H);
      (move/and5P: H => [] || move/and4P: H => [] || move/and3P: H => [] || move/andP: H => [] || 
        eapply forallb_All in H); intros
    | [ H : is_true (test_def (on_free_vars ?P) ?Q ?x) |- _ ] =>
      move/andP: H => []; rewrite ?shiftnP_xpredT; intros
    | [ H : is_true (test_context_k _ _ _ ) |- _ ] =>
      rewrite -> test_context_k_closed_on_free_vars_ctx in H
    end.

Lemma closed_red1_ind (Σ : global_env_ext) (P0 : context -> term -> term -> Type)
  (P := fun Γ t u => is_closed_context Γ -> is_open_term Γ t -> P0 Γ t u) :
  (forall (Γ : context) (na : aname) (t b a : term),
    P Γ (tApp (tLambda na t b) a) (b {0 := a})) ->

  (forall (Γ : context) (na : aname) (b t b' : term), P Γ (tLetIn na b t b') (b' {0 := b})) ->

  (forall (Γ : context) (i : nat) (body : term),
  option_map decl_body (nth_error Γ i) = Some (Some body) -> P Γ (tRel i) ((lift0 (S i)) body)) ->

  (forall (Γ : context) (ci : case_info) (c : nat) (u : Instance.t) (args : list term)
    (p : predicate term) (brs : list (branch term)) br,
    nth_error brs c = Some br ->
    #|skipn (ci_npar ci) args| = context_assumptions br.(bcontext) ->
    P Γ (tCase ci p (mkApps (tConstruct ci.(ci_ind) c u) args) brs)
        (iota_red ci.(ci_npar) p args br)) ->

  (forall (Γ : context) (mfix : mfixpoint term) (idx : nat) (args : list term) (narg : nat) (fn : term),
  unfold_fix mfix idx = Some (narg, fn) ->
  is_constructor narg args = true -> P Γ (mkApps (tFix mfix idx) args) (mkApps fn args)) ->

  (forall (Γ : context) ci (p : predicate term) (mfix : mfixpoint term) (idx : nat)
    (args : list term) (narg : nat) (fn : term) (brs : list (branch term)),
  unfold_cofix mfix idx = Some (narg, fn) ->
  P Γ (tCase ci p (mkApps (tCoFix mfix idx) args) brs) (tCase ci p (mkApps fn args) brs)) ->

  (forall (Γ : context) (p : projection) (mfix : mfixpoint term) (idx : nat) (args : list term)
    (narg : nat) (fn : term),
  unfold_cofix mfix idx = Some (narg, fn) -> P Γ (tProj p (mkApps (tCoFix mfix idx) args)) (tProj p (mkApps fn args))) ->

  (forall (Γ : context) c (decl : constant_body) (body : term),
  declared_constant Σ c decl ->
  forall u : Instance.t, cst_body decl = Some body -> P Γ (tConst c u) (subst_instance u body)) ->

  (forall (Γ : context) (i : inductive) (pars narg : nat) (args : list term) (u : Instance.t)
    (arg : term),
      nth_error args (pars + narg) = Some arg ->
      P Γ (tProj (i, pars, narg) (mkApps (tConstruct i 0 u) args)) arg) ->

  (forall (Γ : context) (na : aname) (M M' N : term),
  closed_red1 Σ Γ M M' -> P0 Γ M M' -> P Γ (tLambda na M N) (tLambda na M' N)) ->

  (forall (Γ : context) (na : aname) (M M' N : term),
  closed_red1 Σ (Γ,, vass na N) M M' -> P0 (Γ,, vass na N) M M' -> 
  P Γ (tLambda na N M) (tLambda na N M')) ->

  (forall (Γ : context) (na : aname) (b t b' r : term),
  closed_red1 Σ Γ b r -> P0 Γ b r -> P Γ (tLetIn na b t b') (tLetIn na r t b')) ->

  (forall (Γ : context) (na : aname) (b t b' r : term),
  closed_red1 Σ Γ t r -> P0 Γ t r -> P Γ (tLetIn na b t b') (tLetIn na b r b')) ->

  (forall (Γ : context) (na : aname) (b t b' r : term),
  closed_red1 Σ (Γ,, vdef na b t) b' r -> P0 (Γ,, vdef na b t) b' r -> P Γ (tLetIn na b t b') (tLetIn na b t r)) ->

  (forall (Γ : context) (ci : case_info) p params' c brs,
    OnOne2 (Trel_conj (closed_red1 Σ Γ) (P0 Γ)) p.(pparams) params' ->
      P Γ (tCase ci p c brs)
          (tCase ci (set_pparams p params') c brs)) ->

  (* (forall (Γ : context) (ci : case_info) p pcontext' c brs,
    OnOne2_local_env (on_one_decl (fun Γ' => P (Γ ,,, Γ'))) p.(pcontext) pcontext' ->
    P Γ (tCase ci p c brs)
      (tCase ci (set_pcontext p pcontext') c brs)) ->
*)
  (forall (Γ : context) (ci : case_info) p preturn' c brs,
    closed_red1 Σ (Γ ,,, inst_case_predicate_context p) p.(preturn) preturn' ->
    P0 (Γ ,,, inst_case_predicate_context p) p.(preturn) preturn' ->
    P Γ (tCase ci p c brs)
        (tCase ci (set_preturn p preturn') c brs)) ->
  
  (forall (Γ : context) (ind : case_info) (p : predicate term) (c c' : term) (brs : list (branch term)),
  closed_red1 Σ Γ c c' -> P0 Γ c c' -> P Γ (tCase ind p c brs) (tCase ind p c' brs)) ->

  (forall (Γ : context) ci p c brs brs',
    OnOne2 (fun br br' =>
    (on_Trel_eq (Trel_conj (closed_red1 Σ (Γ ,,, inst_case_branch_context p br)) 
      (P0 (Γ ,,, inst_case_branch_context p br)))
      bbody bcontext br br')) brs brs' ->
    P Γ (tCase ci p c brs) (tCase ci p c brs')) ->

  (forall (Γ : context) (p : projection) (c c' : term), 
    closed_red1 Σ Γ c c' -> P0 Γ c c' ->
    P Γ (tProj p c) (tProj p c')) ->

  (forall (Γ : context) (M1 N1 : term) (M2 : term),
  closed_red1 Σ Γ M1 N1 -> P0 Γ M1 N1 ->
  P Γ (tApp M1 M2) (tApp N1 M2)) ->

  (forall (Γ : context) (M2 N2 : term) (M1 : term), 
  closed_red1 Σ Γ M2 N2 -> P0 Γ M2 N2 ->
  P Γ (tApp M1 M2) (tApp M1 N2)) ->

  (forall (Γ : context) (na : aname) (M1 M2 N1 : term),
  closed_red1 Σ Γ M1 N1 -> P0 Γ M1 N1 -> 
  P Γ (tProd na M1 M2) (tProd na N1 M2)) ->

  (forall (Γ : context) (na : aname) (M2 N2 M1 : term),
  closed_red1 Σ (Γ,, vass na M1) M2 N2 -> 
  P0 (Γ,, vass na M1) M2 N2 -> 
  P Γ (tProd na M1 M2) (tProd na M1 N2)) ->

  (forall (Γ : context) (ev : nat) (l l' : list term),
      OnOne2 (Trel_conj (closed_red1 Σ Γ) (P0 Γ)) l l' -> 
      P Γ (tEvar ev l) (tEvar ev l')) ->

  (forall (Γ : context) (mfix0 mfix1 : list (def term)) (idx : nat),
  OnOne2 (on_Trel_eq (Trel_conj (closed_red1 Σ Γ) (P0 Γ)) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
  P Γ (tFix mfix0 idx) (tFix mfix1 idx)) ->

  (forall (Γ : context) (mfix0 mfix1 : list (def term)) (idx : nat),
  OnOne2 (on_Trel_eq (Trel_conj (closed_red1 Σ (Γ ,,, fix_context mfix0))
                                (P0 (Γ ,,, fix_context mfix0))) dbody
                      (fun x => (dname x, dtype x, rarg x))) mfix0 mfix1 ->
  P Γ (tFix mfix0 idx) (tFix mfix1 idx)) ->

  (forall (Γ : context) (mfix0 mfix1 : list (def term)) (idx : nat),
  OnOne2 (on_Trel_eq (Trel_conj (closed_red1 Σ Γ) (P0 Γ)) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
  P Γ (tCoFix mfix0 idx) (tCoFix mfix1 idx)) ->

  (forall (Γ : context) (mfix0 mfix1 : list (def term)) (idx : nat),
  OnOne2 (on_Trel_eq (Trel_conj (closed_red1 Σ (Γ ,,, fix_context mfix0))
                                (P0 (Γ ,,, fix_context mfix0))) dbody
                      (fun x => (dname x, dtype x, rarg x))) mfix0 mfix1 ->
  P Γ (tCoFix mfix0 idx) (tCoFix mfix1 idx)) ->
  
  forall (Γ : context) (t t0 : term), closed_red1 Σ Γ t t0 -> P0 Γ t t0.
Proof.
  intros.
  destruct X27 as [clΓ clt r].
  move: clΓ clt.
  Ltac t :=
    eauto; try split; eauto; 
    try apply on_free_vars_ctx_snoc_ass => //;
    try apply on_free_vars_ctx_snoc_def => //;
    try apply is_open_term_snoc => //;
    repeat (try inv_on_free_vars; eauto with fvs; cbn).
  induction r using red1_ind_all; intros;
    try solve [multimatch goal with 
    | H : _ |- _ => eapply H
    end; t].
  - eapply X13. 2-3:t.
    inv_on_free_vars.
    eapply forallb_All in p0.
    eapply OnOne2_All_mix_left in X27; tea.
    eapply OnOne2_impl; tea; repeat (intuition auto; t).
  - forward_keep IHr.
    { rewrite on_free_vars_ctx_app clΓ.
      eapply on_free_vars_ctx_inst_case_context; trea; t. }
    forward_keep IHr.
    { repeat inv_on_free_vars.
      rewrite app_length inst_case_predicate_context_length -shiftnP_add //. }
    apply X14 => //.
  - eapply X16 => //.
    inv_on_free_vars.
    eapply forallb_All in p4.
    eapply OnOne2_All_mix_left in X27; tea. cbn in X27.
    eapply OnOne2_impl; tea; cbn; intros ?? [[[]] ?].
    forward_keep p5.
    { rewrite on_free_vars_ctx_app clΓ /=.
      eapply on_free_vars_ctx_inst_case_context; trea; t. }
    forward_keep p5.
    { repeat inv_on_free_vars.
      rewrite app_length inst_case_branch_context_length -shiftnP_add //. }
    intuition auto. split; auto.
  - eapply X22 => //.
    cbn in clt. eapply forallb_All in clt.
    eapply OnOne2_All_mix_left in X27; tea.
    eapply OnOne2_impl; tea; cbn; intuition auto; t.
  - eapply X23 => //.
    cbn in clt. eapply forallb_All in clt.
    eapply OnOne2_All_mix_left in X27; tea.
    eapply OnOne2_impl; tea; cbn; intuition auto; t.
  - eapply X24 => //.
    cbn in clt. eapply forallb_All in clt.
    eapply OnOne2_All_mix_left in X27; tea.
    eapply OnOne2_impl; tea; cbn; intros ?? [[[]] ?].
    forward_keep p.
    { rewrite on_free_vars_ctx_app clΓ /=.
      eapply on_free_vars_fix_context; trea; t. }
    forward_keep p. { 
      rewrite app_length fix_context_length -shiftnP_add //.
      now inv_on_free_vars. }
    intuition auto. split; auto.
  - eapply X25 => //.
    cbn in clt. eapply forallb_All in clt.
    eapply OnOne2_All_mix_left in X27; tea.
    eapply OnOne2_impl; tea; cbn; intuition auto; t.
  - eapply X26 => //.
    cbn in clt. eapply forallb_All in clt.
    eapply OnOne2_All_mix_left in X27; tea.
    eapply OnOne2_impl; tea; cbn; intros ?? [[[]] ?].
    forward_keep p.
    { rewrite on_free_vars_ctx_app clΓ /=.
      eapply on_free_vars_fix_context; trea; t. }
    forward_keep p. { 
      rewrite app_length fix_context_length -shiftnP_add //.
      now inv_on_free_vars. }
    intuition auto. split; auto.
Qed.

Definition closed_red1_ind' := 
    ltac:(let T := type of closed_red1_ind in  
    let T' := eval cbn in T in 
      exact (closed_red1_ind : T')).
(* 
Ltac revert_until x :=
  repeat lazymatch goal with
  | [ H : _ |- _ ] => revert H
  end. *)

Ltac invert_closed_red H :=
  generalize_eqs H; destruct H using closed_red1_ind'; simplify_dep_elim.

Ltac invert_mkApps_fix_eq :=
  match goal with
  | [ H : mkApps (tFix _ _) _ = _ |- _ ] =>
    apply mkApps_Fix_spec in H; noconf H
  end.

Coercion closed_red1_red : closed_red1 >-> closed_red.
Coercion red_cumul : red >-> cumul.

Lemma wt_equality_refl {cf} {Σ} {wfΣ : wf Σ} {Γ t T} : Σ ;;; Γ |- t : T -> Σ ;;; Γ ⊢ t = t.
Proof.
  intros. apply equality_refl.
  now apply wf_local_closed_context; pcuic.
  now apply subject_closed in X; apply closedn_on_free_vars.
Qed.

Lemma equality_meta_refl {cf} {Σ} {wfΣ : wf Σ} {Γ T U} : 
  is_closed_context Γ -> closedn #|Γ| T -> T = U -> Σ ;;; Γ ⊢ T = U.
Proof.
  intros clΓ cl ->. apply equality_refl => //. now apply closedn_on_free_vars.
Qed.

Lemma equality_eq_trans {cf} {Σ} {wfΣ : wf Σ} {Γ T U V} : 
  Σ ;;; Γ ⊢ T = U -> U = V -> Σ ;;; Γ ⊢ T = V.
Proof.
  now intros tr ->.
Qed.

Lemma eq_equality_trans {cf} {Σ} {wfΣ : wf Σ} {Γ T U V} : 
  T = U -> Σ ;;; Γ ⊢ U = V -> Σ ;;; Γ ⊢ T = V.
Proof.
  now intros -> tr.
Qed.

Lemma equality_terms_eq_trans {cf} {Σ} {wfΣ : wf Σ} {Γ T U V} : 
  equality_terms Σ Γ T U -> U = V -> equality_terms Σ Γ T V.
Proof.
  now intros tr ->.
Qed.

Lemma eq_equality_terms_trans {cf} {Σ} {wfΣ : wf Σ} {Γ T U V} : 
  T = U -> equality_terms Σ Γ U V -> equality_terms Σ Γ T V.
Proof.
  now intros -> tr.
Qed.

Lemma red_terms_refl {Σ Γ ts} :
  is_closed_context Γ ->
  forallb (is_open_term Γ) ts -> red_terms Σ Γ ts ts.
Proof.
  solve_all.
  eapply All_All2; tea. cbn.
  firstorder auto.
Qed.

Notation welltyped Σ Γ t := (∑ T, Σ ;;; Γ |- t : T).
Notation welltyped_terms Σ Γ := (All (fun t => welltyped Σ Γ t)).

Lemma spine_subst_wt_terms {cf} {Σ Γ inst s Δ} : spine_subst Σ Γ inst s Δ -> 
  welltyped_terms Σ Γ inst.
Proof.
  move/spine_subst_ctx_inst.
  induction 1; try constructor; auto.
  now exists t.
Qed.

Lemma wt_terms_equality {cf} {Σ} {wfΣ : wf Σ} {Γ ts} : welltyped_terms Σ Γ ts -> equality_terms Σ Γ ts ts.
Proof.
  intros; eapply All_All2; tea. cbn; intros x [T HT].
  now eapply wt_equality_refl.
Qed.

Lemma weakening_context_equality {cf} {Σ} {wfΣ : wf Σ} {Γ Δ Δ0 Δ1} :
  Σ ⊢ Γ ,,, Δ0 = Γ ,,, Δ1 ->
  Σ ⊢ Γ ,,, Δ = Γ ,,, Δ ->
  Σ ⊢ Γ ,,, Δ ,,, lift_context #|Δ| 0 Δ0 = Γ ,,, Δ ,,, lift_context #|Δ| 0 Δ1.
Proof.
  intros h h'.
  eapply context_equality_rel_app.
  eapply context_equality_rel_app in h.
  induction h.
  induction b; cbn. constructor. fvs.
  constructor.
  depelim p; cbn; rewrite !lift_context_snoc; constructor; auto; fvs;
  rewrite /lift_decl /map_decl /=; constructor; auto with fvs. apply IHb.
  constructor; auto. rewrite !Nat.add_0_r. rewrite -(All2_fold_length b).
  eapply weakening_equality => //. fvs. apply IHb.
  constructor; auto; rewrite !Nat.add_0_r -(All2_fold_length b);
  apply weakening_equality => //; fvs.
Qed.

Lemma on_constructor_closed_indices {cf} {Σ} {wfΣ : wf Σ} : 
  forall {i mdecl idecl cdecl},
  declared_constructor Σ.1 i mdecl idecl cdecl ->
  All (is_open_term (arities_context (ind_bodies mdecl) ,,, ind_params mdecl ,,, cstr_args cdecl)) (cstr_indices cdecl).
Proof.
  intros.
  pose proof (on_declared_constructor H) as [[onmind oib] [cs [hnth onc]]].
  pose proof (onc.(on_cindices)).
  now eapply ctx_inst_open_terms in X.
Qed.

Lemma on_constructor_wf_arities_pars_args {cf} {Σ} {wfΣ : wf Σ} {i mdecl idecl cdecl} :
  declared_constructor Σ.1 i mdecl idecl cdecl ->
  wf_local (Σ.1, ind_universes mdecl) (arities_context (ind_bodies mdecl) ,,, ind_params mdecl ,,, cstr_args cdecl).
Proof.
  move=> H.
  pose proof (on_declared_constructor H) as [[onmind oib] [cs [hnth onc]]].
  move/on_cargs/sorts_local_ctx_wf_local: onc => H'.
  apply H'.
  apply weaken_wf_local; tea.
  eapply (wf_arities_context H).
  now apply onParams in onmind.
Qed.

Lemma closedP_shiftnP_eq k : closedP k xpredT =1 shiftnP k xpred0.
Proof.
  rewrite /closedP /shiftnP. intros i; nat_compare_specs => //.
Qed.

Lemma on_free_vars_closedn k t : closedn k t = on_free_vars (shiftnP k xpred0) t.
Proof.
  rewrite closedP_on_free_vars.
  eapply on_free_vars_ext, closedP_shiftnP_eq.
Qed.

Lemma on_constructor_closed_indices_inst {cf} {Σ} {wfΣ : wf Σ} {i mdecl idecl cdecl u} :
  declared_constructor Σ.1 i mdecl idecl cdecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  All (is_open_term (ind_params mdecl ,,, cstr_args cdecl)@[u])
    (map (subst (inds (inductive_mind (fst i)) u (ind_bodies mdecl))
           (#|cstr_args cdecl| + #|ind_params mdecl|)) (cstr_indices cdecl)@[u]).
Proof.
  intros H cu.
  pose proof (on_declared_constructor H) as [[onmind oib] [cs [hnth onc]]].
  pose proof (onc.(on_cindices)).
  eapply ctx_inst_inst in X; tea.
  eapply ctx_inst_open_terms in X.
  eapply All_map, All_impl; tea.
  cbn; intros x clx.
  rewrite -[_ ,,, _]app_context_nil_l -[_ ,,, cstr_args cdecl]app_context_assoc app_context_assoc in clx.
  rewrite !subst_instance_app_ctx in clx.
  eapply (is_open_term_subst (Γ := []) (s:=inds (inductive_mind i.1) u (ind_bodies mdecl))) in clx.
  3:eapply inds_is_open_terms. 3:len.
  rewrite app_context_nil_l subst_context_app in clx.
  rewrite closed_ctx_subst in clx.
  now eapply declared_inductive_closed_params_inst.
  len in clx. len.
  rewrite app_context_nil_l app_context_assoc.
  epose proof (on_constructor_wf_arities_pars_args H).
  eapply (wf_local_instantiate _ (InductiveDecl mdecl)) in X0; tea.
  rewrite !subst_instance_app_ctx in X0.
  now eapply wf_local_closed_context in X0. apply H.
  now eapply declared_inductive_wf_global_ext.
Qed.

Arguments pair {A B}%type_scope &.

Lemma equality_terms_refl {cf} {Σ} {wfΣ : wf Σ} {Γ u} : 
  is_closed_context Γ ->
  forallb (is_open_term Γ) u -> 
  equality_terms Σ Γ u u.
Proof.
  intros. eapply into_equality_terms => //.
  eapply All2_refl; reflexivity.
Qed.

Lemma All2_tip {A} {P} (t u : A) : P t u -> All2 P [t] [u].
Proof. now repeat constructor. Qed.
Hint Resolve All2_tip : core.

Lemma map2_set_binder_name_expand_lets nas Γ Δ :
  #|nas| = #|Δ| ->
  map2 set_binder_name nas (expand_lets_ctx Γ Δ) = 
  expand_lets_ctx Γ (map2 set_binder_name nas Δ).
Proof.
  move=> hlen.
  rewrite /expand_lets_ctx /expand_lets_k_ctx.
  rewrite PCUICRename.map2_set_binder_name_fold ?lengths //.
  rewrite PCUICRename.map2_set_binder_name_fold ?lengths //.
Qed.

Lemma closed_red1_eq_context_upto_names {Γ Γ'} : 
  eq_context_upto_names Γ Γ' → is_closed_context Γ -> is_closed_context Γ'.
Proof.
  induction 1; cbn; auto.
  intros eqctx []; split; auto.

Lemma closed_red1_eq_context_upto_names {Σ Γ Γ'} {t u} : 
  eq_context_upto_names Γ Γ' → closed_red1 Σ Γ t u → closed_red1 Σ Γ' t u.
Proof.
  intros eqctx []; split; auto.
  

Lemma sr_red1 {cf:checker_flags} :
  env_prop SR_red1
      (fun Σ Γ => wf_local Σ Γ ×      
        (forall Γ' Δ' Δ, 
          Γ = Γ' ,,, Δ' ->
          OnOne2_local_env (on_one_decl (fun Δ : context => closed_red1 Σ (Γ',,, Δ))) Δ' Δ ->
          wf_local_rel Σ Γ' Δ)).
Proof.
  apply typing_ind_env; intros Σ wfΣ Γ wfΓ; unfold SR_red1; intros **; rename_all_hyps; auto.
  2-15:match goal with
    | [H : (_ ;;; _ |- _ <= _) |- _ ] => idtac
    | _ =>
      invert_closed_red Hu;
      try solve [invert_mkApps_fix_eq];
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
    split; auto. intros Γ' Δ' Δ ->.
    induction 1.
    * depelim p. subst. depelim X. constructor.
      now eapply wf_local_app_inv.
      exists tu.π1. now eapply t1.
    * depelim X. 
      constructor. now eapply wf_local_app_inv.
      depelim p. destruct s as [[red <-]|[red <-]]; subst.
      exists tu.π1. now eapply t2.
      exact tu.
      do 2 red. depelim p. destruct s as [[red <-]|[red <-]]; subst.
      specialize (t2 _ red). eapply type_equality; tea.
      exists tu.π1. apply t2. eapply red_equality.
      now eapply closed_red1_red.
      now eapply t1.
    * depelim X; specialize (IHX0 _ X); pose proof (wf_local_closed_context all).
      + constructor; auto. clear X.
        pose proof (wf_local_closed_context all).
        eapply wf_local_app_inv in all as [].
        eapply wf_local_app in IHX0; tea.
        destruct tu as [s Hs]. exists s.
        eapply closed_context_conversion; tea.
        eapply red_one_decl_context_equality => //.
        eapply OnOne2_local_env_impl; tea.
        intros ???. eapply on_one_decl_impl => ???; firstorder. 
      + constructor; auto. clear X.
        { eapply wf_local_app_inv in all as [].
          eapply wf_local_app in IHX0; tea.
          destruct tu as [s Hs]. exists s.
          eapply closed_context_conversion; tea.
          eapply red_one_decl_context_equality => //.
          eapply OnOne2_local_env_impl; tea.
          intros ???. eapply on_one_decl_impl => ???; firstorder. }
        { red.
          clear X; eapply wf_local_app_inv in all as [].
          eapply wf_local_app in IHX0; tea.
          eapply closed_context_conversion; tea.
          eapply red_one_decl_context_equality => //.
          eapply OnOne2_local_env_impl; tea.
          intros ???. eapply on_one_decl_impl => ???; firstorder. }

  - (* Rel delta reduction *)
    rewrite heq_nth_error in H. destruct decl as [na b ty]; noconf H.
    simpl.
    pose proof (PCUICValidity.nth_error_All_local_env heq_nth_error wfΓ); eauto.
    cbn in *.
    rewrite <- (firstn_skipn (S n) Γ).
    eapply weakening_length; auto.
    { rewrite firstn_length_le; auto. apply nth_error_Some_length in heq_nth_error. auto with arith. }
    now unfold app_context; rewrite firstn_skipn.

  - (* Prod *)
    constructor; eauto. intuition auto.
    unshelve eapply (closed_context_conversion _ typeb); pcuics.
    constructor. now eapply context_equality_refl, wf_local_closed_context.
    constructor; auto. eapply red_conv.
    now eapply closed_red1_red.

  - (* Lambda *)
    eapply type_Cumul'. eapply type_Lambda; eauto.
    intuition auto.
    unshelve eapply (closed_context_conversion _ typeb); pcuics.
    constructor. now eapply context_equality_refl, wf_local_closed_context.
    constructor; auto. eapply red_conv. now eapply closed_red1_red. 
    assert (Σ ;;; Γ |- tLambda n t b : tProd n t bty). econstructor; pcuics.
    now eapply validity in X0.
    econstructor 3. reflexivity. constructor. apply Hu.

  - (* LetIn body *)
    eapply type_Cumul'.
    apply (@substitution_let _ _ _ Γ n b b_ty b' b'_ty typeb').
    specialize (typing_wf_local typeb') as wfd.
    assert (Σ ;;; Γ |- tLetIn n b b_ty b' : tLetIn n b b_ty b'_ty). econstructor; eauto.
    eapply (validity X0).
    eapply cumul_red_r.
    apply cumul_refl'. constructor.

  - (* LetIn value *)
    eapply type_Cumul'.
    econstructor; eauto.
    unshelve eapply (closed_context_conversion _ typeb'); pcuics.
    constructor. eapply context_equality_refl; eauto. constructor; auto.
    now eapply red_conv, closed_red1_red. apply equality_refl; eauto. now repeat inv_on_free_vars.
    assert (Σ ;;; Γ |- tLetIn n b b_ty b' : tLetIn n b b_ty b'_ty). econstructor; eauto.
    eapply (validity X0).
    eapply cumul_red_r.
    apply cumul_refl'. constructor. apply Hu.

  - (* LetIn type annotation *)
    specialize (forall_u _ Hu).
    eapply type_Cumul'.
    econstructor; eauto.
    eapply type_Cumul'. eauto. exists s1; auto.
    apply: red_cumul Hu. 
    unshelve eapply (closed_context_conversion _ typeb').
    constructor; pcuic.
    eapply type_Cumul'. eauto. pcuic. apply: red_cumul Hu.
    constructor; auto. eapply context_equality_refl; eauto. constructor; auto.
    eapply equality_refl; eauto; repeat inv_on_free_vars =>//.
    apply: red_conv Hu.
    assert (Σ ;;; Γ |- tLetIn n b b_ty b' : tLetIn n b b_ty b'_ty). econstructor; eauto.
    eapply (validity X0).
    eapply cumul_red_r.
    apply cumul_refl'. constructor. apply Hu.

  - (* Application *)
    eapply substitution0; eauto.
    pose proof typet as typet'.
    eapply inversion_Lambda in typet' as [s1 [B' [Ht [Hb HU]]]]=>//.
    apply cumul_Prod_inv in HU as [eqann eqA leqB] => //.
    pose proof (validity typet) as i.
    eapply isType_tProd in i as [Hdom Hcodom]; auto.
    eapply type_equality; eauto.
    unshelve eapply (closed_context_conversion _ Hb); pcuics.
    constructor. now apply context_equality_refl. constructor; auto.

  - (* Fixpoint unfolding *)
    assert (args <> []) by (destruct args; simpl in *; congruence).
    symmetry in H3. apply tApp_mkApps_inj in H3 as [-> Hu]; auto.
    rewrite mkApps_nonempty; auto.
    epose (last_nonempty_eq H4). rewrite <- Hu in e. rewrite <- e.
    clear e.
    specialize (inversion_mkApps typet) as [T' [appty spty]].
    have vT' := (validity appty).
    eapply type_tFix_inv in appty as [T [arg [fn' [[[Hnth wffix] Hty]]]]]; auto.
    rewrite H in Hnth. noconf Hnth.
    eapply type_App; eauto.
    eapply type_mkApps; [|tea].
    eapply type_equality; eauto.
    
  - (* Application congruence for argument *)
    intuition auto.
    eapply type_Cumul'; [eapply type_App| |]; eauto with wf.
    eapply validity.
    eapply type_App; eauto. eapply red_cumul_inv.
    eapply (@red_red _ _ wf _ Γ [vass na A] [] [u] [N2]); eauto.
    erewrite -> on_free_vars_ctx_on_ctx_free_vars.
    eapply on_free_vars_ctx_snoc_ass; tea.
    eapply type_closed in typeu. now eapply closedn_on_free_vars.
    eapply type_closed in typet. cbn in typet; repeat inv_on_free_vars.
    cbn. now eapply closedn_on_free_vars. constructor. apply: red1_red Hu. constructor.
    all:repeat constructor. cbn.
    rewrite -(shiftnP_add 1) addnP_shiftnP. repeat inv_on_free_vars => //.

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
    destruct X4 as [wfcpc IHcpc].
    hide X9.
    pose proof typec as typec''.
    unfold iota_red.
    pose proof typec as typec'.
    eapply inversion_mkApps in typec as [A [tyc tyargs]]; auto.
    eapply (inversion_Construct Σ wf) in tyc as [mdecl' [idecl' [cdecl [wfl [declc [Hu tyc]]]]]].
    eapply typing_spine_strengthen in tyargs; tea.
    have openargs : forallb (is_open_term Γ) args.
    { repeat inv_on_free_vars; auto. }
    clear tyc.
    2:{ eapply validity. econstructor; tea. }
    unshelve eapply Construct_Ind_ind_eq in typec'; eauto.
    pose proof (declared_inductive_inj isdecl (proj1 declc)) as [-> ->].
    destruct typec' as [[[[_ equ] cu] eqargs] [cparsubst [cargsubst [iparsubst [iidxsubst ci']]]]].
    destruct ci' as [cparsubst0 iparsubst0 idxsubst0 subsidx [s [typectx [Hpars Hargs]]]].
    pose proof (on_declared_constructor declc) as [[onind oib] [ctor_sorts [hnth onc]]].
    (* pose proof (PCUICContextSubst.context_subst_fun csubst (iparsubst0.(inst_ctx_subst))). subst iparsubst. *)
    unshelve epose proof (constructor_cumulative_indices declc _ Hu cu equ _ _ _ _ _ cparsubst0 iparsubst0 Hpars).
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
    assert (isType Σ Γ (mkApps ptm (indices ++ [mkApps (tConstruct ci c u) args]))).
    { eapply validity. econstructor; eauto. apply (All2i_impl X9). intuition auto. }
    eapply All2i_nth_error in X9; tea.
    2:{ destruct declc. simpl in e. exact e. }
    cbn in X9.
    destruct X9 as [bctxeq [[wfcbc IHcbc] [hb [IHbody [cbty IHcbty]]]]].
    clear IHcbty IHbody IHcbc.
    cbn -[case_branch_type_gen] in hb.
    rewrite case_branch_type_fst in hb.
    set (prebrctx := pre_case_branch_context ci mdecl (pparams p) (puinst p) cdecl).
    set (ibrctx := (case_branch_context ci mdecl p (forget_types (bcontext br)) cdecl)) in *.
    set (brctx := (inst_case_context (pparams p) (puinst p) (bcontext br))).
    assert (wfbr : wf_branch cdecl br).
    { eapply Forall2_All2, All2_nth_error in H4; tea.
      eapply declc. }
    assert(eqctx : All2 (compare_decls eq eq) ibrctx brctx).
    { rewrite /brctx /ibrctx.
      rewrite /case_branch_context /case_branch_context_gen.
      etransitivity.
      eapply eq_binder_annots_eq.
      eapply wf_pre_case_branch_context_gen; tea.
      unfold pre_case_branch_context_gen.
      rewrite /inst_case_context.
      now eapply alpha_eq_subst_context, alpha_eq_subst_instance. }
    assert (convbrctx' : Σ ⊢ Γ ,,, brctx = Γ ,,, ibrctx).
    { etransitivity; tea.
      eapply context_equality_app; revgoals.
      3:eapply context_equality_refl; eapply wf_local_closed_context; auto.
      split. apply context_equality_refl. pcuic. 
      eapply eq_context_alpha_conv => //. now symmetry. rewrite /brctx /ibrctx; len.
      rewrite case_branch_context_length //. }
    assert (convbrctx'' : Σ ⊢ Γ ,,, ibrctx = Γ ,,, prebrctx).
    { rewrite /ibrctx /prebrctx.
      symmetry.
      apply context_equality_rel_app.
      eapply eq_context_alpha_conv.
      eapply pre_case_branch_context_eq; tea. }
    assert (prewf : wf_local Σ (Γ ,,, prebrctx)).
    { eapply wf_pre_case_branch_context; tea. }
    assert (prewfs : wf_local Σ (Γ ,,, smash_context [] prebrctx)).
    { eapply wf_local_smash_end; tea. }
    assert (wfbrctx' : wf_local Σ (Γ ,,, brctx)).
    { eapply wf_local_alpha. eapply All2_app; tea. eapply All2_refl; reflexivity. assumption. }
    assert (convbrctxsmash : Σ ⊢ 
        Γ ,,, smash_context [] (case_branch_context ci mdecl p (forget_types (bcontext br)) cdecl) =
        Γ ,,, smash_context [] brctx).
    { eapply conv_context_smash_end; tea. now symmetry. }
    assert (spbrctx : spine_subst Σ Γ (skipn (ind_npars mdecl) args) (List.rev (skipn (ind_npars mdecl) args))
      (smash_context [] prebrctx)).
    { pose proof (spine_subst_smash idxsubst0).
      eapply spine_subst_cumul in X0. eapply X0. all:tea.
      1-2:apply smash_context_assumption_context; pcuic.
      eapply X0.
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
      eapply context_equality_rel_trans; tea.
      apply context_equality_rel_app.
      apply context_equality_refl.
      now apply wf_local_closed_context in prewfs. }
    eapply closed_context_conversion in hb.
    3:{ symmetry. eapply convbrctx'. }        
    eapply typing_expand_lets in hb.
    eapply (PCUICSubstitution.substitution (Δ := [])) in hb.
    2:{ eapply (spine_subst_cumul (Γ' := smash_context [] brctx)) in spbrctx; tea.
        eapply spbrctx.
        1-2:apply smash_context_assumption_context; pcuic.
        now apply wf_local_smash_end.
        apply context_equality_rel_smash => //.
        apply context_equality_rel_app. apply context_equality_eq_le. symmetry.
        etransitivity; tea. } 
    rewrite subst_context_nil -heq_ind_npars in hb *.
    eapply type_equality. exact hb. 3:auto.
    assumption. clear hb.
    rewrite /case_branch_type.
    set cbtyg := (case_branch_type_gen _ _ _ _ _ _ _ _ _).
    (* Move back to the canonical branch context for the rest of the proof *)
    transitivity (subst0 (List.rev (skipn (ind_npars mdecl) args)) (expand_lets prebrctx cbtyg.2)).
    { eapply equality_eq_le.
      eapply (substitution_equality (Γ'' := [])). eapply spbrctx. 
      symmetry. eapply equality_expand_lets_equality_ctx; tea. 
      eapply wt_equality_refl.
      rewrite case_branch_type_fst in cbty.
      eapply closed_context_conversion in cbty. exact cbty.
      auto. auto.
      eapply context_equality_rel_app; tea. eapply context_equality_eq_le.
      symmetry. now transitivity (Γ ,,, ibrctx). }
    cbn.
    rewrite lift_mkApps !subst_mkApps.
    pose proof (wf_branch_length wfbr).
    have lenskip: #|skipn (ind_npars mdecl) args| = (context_assumptions (cstr_args cdecl)).
    { rewrite List.skipn_length eqargs; lia. }
    have lenfirst: #|firstn (ind_npars mdecl) args| = (context_assumptions (ind_params mdecl)).
    { rewrite firstn_length_le; try lia. now rewrite -(declared_minductive_ind_npars isdecl). }
    have brctxlen : #|prebrctx| = #|cstr_args cdecl|.
    { now rewrite /prebrctx !lengths. }
    have pparamsl : #|pparams p| = context_assumptions (ind_params mdecl).
    { move: (wf_predicate_length_pars H0).
      now rewrite (declared_minductive_ind_npars isdecl). }
      
    rewrite simpl_lift; try lia.
    rewrite subst_subst_lift // !lengths //; try lia.
    rewrite map_app /= !map_app. eapply equality_eq_le.
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
    eapply equality_mkApps; tea. 
    { eapply wt_equality_refl. eapply type_it_mkLambda_or_LetIn; tea. }
    rewrite (firstn_app_left _ 0) ?Nat.add_0_r // /= ?app_nil_r in iparsubst0.
    rewrite (firstn_app_left _ 0) ?Nat.add_0_r // /= ?app_nil_r in Hpars.
    rewrite (skipn_all_app_eq) // in subsidx.
    have brctxass : context_assumptions prebrctx = context_assumptions (cstr_args cdecl).
    { now rewrite /prebrctx !lengths. }
    assert (eqargts : equality_terms Σ Γ (skipn (ind_npars mdecl) args)
      (skipn (ind_npars mdecl) args)).
    { pose proof (spine_subst_ctx_inst spbrctx).
      apply ctx_inst_open_terms in X0.
      eapply All_All2; tea. cbn; intros.
      apply equality_refl; tea. }
    
    eapply All2_app.
    * set(indsub := inds _ _ _).
      relativize (map (subst0 _) _).
      2:{
        rewrite !map_map_compose. apply map_ext => x.
        symmetry.
        rewrite -/(subst_let_expand _ _ _) -/(subst_let_expand_k _ _ _ _).
        rewrite -brctxass -brctxlen -expand_lets_eq.
        rewrite {1 2}/prebrctx {1 2}/pre_case_branch_context {1}subst_context_length.
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
      intros cv convidx.
      eapply (equality_terms_subst (Δ := [])) in cv.
      3:{ exact (spine_subst_smash idxsubst0). }
      3:{ exact (spine_subst_smash idxsubst0). }      
      all:tea. 2:{ eapply wf_local_closed_context. eapply wf_local_smash_end; tea. eapply idxsubst0. }
      2:{ eapply All2_rev => //. }
      rewrite subst_context_nil /= in cv. simpl in cv.
      rewrite skipn_all_app_eq // in convidx.

      assert(equality_terms Σ Γ
        (map
         (fun x : term =>
          subst0 (List.rev args)
            (expand_lets (argctxu1 ++ subst_instance u (ind_params mdecl)) (subst_instance u x)))
          (cstr_indices cdecl)) indices).
      { eapply eq_equality_terms_trans; tea.
        pose proof (positive_cstr_closed_indices declc).
        eapply All_map_inv in X0.
        eapply All_map_eq, All_impl; tea.
        cbn; intros x.
        intros cl.
        epose proof 
          ( @spine_subst_app _ Σ Γ (subst_instance u (ind_params mdecl))
            (subst_context
              (inds (inductive_mind ci) u (ind_bodies mdecl))
               #|ind_params mdecl| (subst_instance u (cstr_args cdecl)))
          (firstn (ind_npars mdecl) args)
          (skipn (ind_npars mdecl) args) (cargsubst ++ cparsubst)) as X3.
        rewrite lenfirst in X3. len in X3.
        specialize (X3 eq_refl). 
        forward X3. { rewrite -app_context_assoc. eapply weaken_wf_local; tea. }
        forward X3. {
          rewrite skipn_all_app_eq; len.
          now rewrite -(PCUICContextSubst.context_subst_length idxsubst0); len.
          apply cparsubst0. }
        forward X3. {
          pose proof (PCUICContextSubst.context_subst_length idxsubst0).
          len in H8.
          rewrite firstn_app H8 firstn_all Nat.sub_diag /= app_nil_r skipn_all_app_eq //. }
        rewrite firstn_skipn in X3.
        rewrite (spine_subst_inst_subst_term X3).
        f_equal.
        pose proof (PCUICInductiveInversion.on_constructor_wf_args declc).
        eapply closed_wf_local in X2; tea.
        rewrite !closedn_ctx_app /= in X2 *.
        move/andb_and: X2 => [] /andb_and [] clar clp clargs.
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
          rewrite Nat.add_comm in cl.
          eapply (PCUICClosed.closedn_expand_lets) in cl.
          rewrite closedn_subst_instance.
          now rewrite Nat.add_comm.
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
      eapply (eq_equality_terms_trans (U:=
       (map (subst0 (List.rev (skipn (ind_npars mdecl) args)))
      (map (subst iparsubst (context_assumptions (cstr_args cdecl)))
         (map (expand_lets argctxu)
            (map (subst_instance (puinst p)) (cstr_indices cdecl))))))).
      2:{
        rewrite !map_map_compose.
        rewrite !map_map_compose in cv.
        eapply All2_map_inv, All2_All in cv.
        eapply All2_map, All_All2; tea.
        cbn; intros x Hx.
        eapply equality_eq_trans.
        symmetry; tea.
        rewrite (spine_subst_inst_subst_term_k cparsubst0).
        pose proof (subst_let_expand_app).
        relativize (context_assumptions (cstr_args cdecl)).
        erewrite <-subst_app_simpl. 2:now len.
        rewrite -List.rev_app_distr firstn_skipn. len.
        rewrite lenskip expand_lets_app /argctxu1.
        rewrite context_assumptions_subst_context context_assumptions_subst_instance //. }

      (* clear -H4 pparamsl wfbrctx convbrctx cumargs wfcbc wfparsargs Hpars lenskip lenfirst lenpars heq_ind_npars wf cparsubst0 idxsubst0 iparsubst0 isdecl declc. *)
      rewrite /argctxu. simpl.
      rewrite !map_map_compose. apply All_map_eq.
      eapply All_impl.
      exact (All_map_inv _ _ _ (positive_cstr_closed_indices declc)).
      cbn => x.
      rewrite -(closed_ctx_subst indsub 0 (subst_instance _ _ ,,, _)).
      { now eapply closed_wf_local in wfparsargs'. }
      relativize (#|ind_params _| + _).
      erewrite expand_lets_subst_comm; rewrite !lengths.
      2:rewrite !lengths; lia.
      rewrite -context_assumptions_app Nat.add_comm.
      move/(PCUICClosed.closedn_expand_lets) => /=. rewrite /= !lengths => clx.
      rewrite (subst_closedn indsub (_ + _)).
      relativize (_ + _). eapply (closedn_expand_lets 0).
      2-3:rewrite /= !lengths // closedn_subst_instance //.
      eapply closed_wf_local; tea. now rewrite Nat.add_comm.
      rewrite (spine_subst_inst_subst_term_k iparsubst0).
      change (ind_subst _ _ _) with indsub.
      relativize (context_assumptions _).
      erewrite <-subst_app_simpl. 2:now len.
      rewrite List.rev_length lenskip /=.
      relativize (context_assumptions _).
      erewrite <- expand_lets_app => //.
      now rewrite !lengths.

    * rewrite lift_mkApps /= !subst_mkApps /=. constructor. 2:constructor.
      rewrite !map_app. 
      rewrite -{3}(firstn_skipn (ind_npars mdecl) args) -brctxlen -brctxass.
      rewrite - !expand_lets_eq_map.
      rewrite -/(expand_lets_k (bcontext br) 0 _).
      relativize (to_extended_list (cstr_args cdecl)).
      erewrite map_expand_lets_to_extended_list.
      2:{ etransitivity.
        2:apply to_extended_list_case_branch_context.
        rewrite /prebrctx.
        eapply conv_context_rel_to_extended_list.
        apply context_equality_rel_app. symmetry. tea. 
        now eapply Forall2_All2 in wfbr. }
      rewrite -map_expand_lets_to_extended_list.
      rewrite !map_map_compose.
      rewrite [map (fun x => _) (to_extended_list _)](@map_subst_let_expand_to_extended_list _ Σ _ Γ); tea.
      relativize (map _ _).
      2:{ eapply map_ext => x. rewrite -/(subst_let_expand _ _ _). 
          now rewrite subst_let_expand_lift_id //; len. }
      rewrite map_id.
      transitivity (mkApps (tConstruct ci c (puinst p)) args).
      rewrite -(firstn_skipn (ind_npars mdecl) args).
      eapply equality_mkApps; tea.
      eapply equality_refl => //.
      eapply All2_app. eapply All2_symP => //. intro; now symmetry.
      rewrite firstn_skipn //.
      rewrite firstn_skipn. constructor => //.
      { rewrite on_free_vars_mkApps /= //. }
      { rewrite on_free_vars_mkApps /= //. }
      eapply eq_term_upto_univ_mkApps.
      2:reflexivity.
      constructor. eapply R_global_instance_sym; tc.
      rewrite eqargs.
      now eapply (R_global_instance_cstr_irrelevant declc).

  - (* Case congruence: on a cofix, impossible *)
    eapply inversion_mkApps in typec as [? [tcof ?]] =>  //.
    eapply type_tCoFix_inv in tcof as [d [[[Hnth wfcofix] ?] ?]] => //.
    unfold unfold_cofix in H.
    rewrite Hnth in H. noconf H.
    pose proof (validity t0).
    eapply typing_spine_strengthen in t; eauto.
    eapply wf_cofixpoint_typing_spine in t; eauto.
    unfold check_recursivity_kind in t.
    rewrite isdecl.p1 in t.
    apply Reflect.eqb_eq in t. rewrite t /= in heq_isCoFinite.
    discriminate.
  
  - (* Case congruence on a parameter *) 
    destruct X0, X4.
    assert (isType Σ Γ (mkApps (it_mkLambda_or_LetIn (case_predicate_context ci mdecl idecl p) (preturn p)) (indices ++ [c]))).
    { eapply validity. econstructor; eauto.
      eapply (All2i_impl X9); intuition auto. }
    set (ptm := it_mkLambda_or_LetIn _ _) in *.
    cbn -[ptm it_mkLambda_or_LetIn] in *.
    have wfparinds : wf_local Σ
      (Γ,,, subst_instance (puinst p) (ind_params mdecl,,, ind_indices idecl)).
    { eapply weaken_wf_local; tea.
      eapply (on_minductive_wf_params_indices_inst isdecl _ H1). }
    have ctxi' : ctx_inst Σ Γ (params' ++ indices)
        (List.rev
           (subst_instance p.(puinst) (ind_params mdecl,,, ind_indices idecl))).
    { eapply OnOne2_prod_inv in X2 as [X2 _].
      eapply OnOne2_app_r in X2.
      unshelve eapply (ctx_inst_merge' _ _ _ _ _ X6 X5); tea. }
    pose proof X5 as X5'.
    unshelve epose proof (ctx_inst_spine_subst _ X5); tea. 
    eapply spine_subst_smash in X3; tea. 
    eapply ctx_inst_length in X5. len in X5.
    rewrite context_assumptions_rev in X5. len in X5.
    pose proof (wf_predicate_length_pars H0). simpl in H.
    pose proof (declared_minductive_ind_npars isdecl).
    have lenidx : (#|List.rev indices| = (context_assumptions (ind_indices idecl))) by (len; lia).
    rewrite subst_instance_app smash_context_app_expand in X3.
    eapply spine_subst_app_inv in X3 as [sppars spargs]; tea. 2:len.
    len in sppars. len in spargs.
    rewrite List.rev_app_distr in sppars spargs.
    rewrite skipn_app - !lenidx !skipn_all /= Nat.sub_diag skipn_0 in sppars spargs.
    rewrite firstn_app firstn_all Nat.sub_diag /= app_nil_r in spargs.
    rewrite subst_instance_app List.rev_app_distr in X6. 
    have lenpars' := (OnOne2_length X2).
    unshelve epose proof (ctx_inst_spine_subst _ ctxi');tea.
    pose proof (spine_codom_wf _ _ _ _ _ X3);tea.
    pose proof (spine_subst_smash X3); tea. all:tea.
    rewrite subst_instance_app smash_context_app_expand in X7.
    eapply spine_subst_app_inv in X7 as [sppars' spargs']; tea.
    2:len. len in sppars'. len in spargs'.
    rewrite List.rev_app_distr in sppars' spargs'.
    rewrite skipn_app - !lenidx !skipn_all /= Nat.sub_diag skipn_0 in sppars' spargs'.
    rewrite firstn_app firstn_all Nat.sub_diag /= app_nil_r in spargs'.
    have wfp' : wf_predicate mdecl idecl (set_pparams p params').
    { move: H0. rewrite /wf_predicate /wf_predicate_gen /=.
      rewrite (OnOne2_length X2). intuition auto. }
    have redpars : red_terms Σ Γ (pparams p) params'.
    { eapply OnOne2_prod_inv in X2 as [cv _].
      clear -cv H H3. inv_on_free_vars.
      cbn in *; repeat inv_on_free_vars. clear b a2 a1 a0.
      induction cv; cbn; constructor; auto using closed_red1_red;
      cbn in *; repeat inv_on_free_vars; auto.
      apply red_terms_refl => //. now apply into_closed_red. }
    have convctx' :
      Σ ⊢ (case_predicate_context ci mdecl idecl p ++ Γ) =
      (case_predicate_context ci mdecl idecl (set_pparams p params') ++ Γ).
    { move: X2 => cv.
      rewrite /case_predicate_context /case_predicate_context_gen.
      etransitivity.
      symmetry; eapply context_equality_rel_app.
      eapply conv_ctx_set_binder_name.
      admit.
      etransitivity.
      2:eapply context_equality_rel_app, conv_ctx_set_binder_name.
      rewrite /pre_case_predicate_context_gen /inst_case_context.
      cbn [pparams puinst set_pparams].
      eapply substitution_context_equality_red_subst. admit.
      eapply All2_rev => //.
      eapply subslet_untyped_subslet. eapply sppars.
      admit. }
      
      (* eapply context_equality_rel_sym.
      2:eapply conv_ctx_set_binder_name.
      
      eapply conv_context_set_binder_name.
      eapply All2_map_left, All2_same. intros; reflexivity.
      eapply conv_context_rel_app in cv.
      eapply conv_context_set_binder_name_inv in cv.
      2:{ destruct H0 as [_ wfnas].
          eapply Forall2_All2 in wfnas.
          move: wfnas. simpl.
          intros wfa.
          rewrite /pre_case_predicate_context_gen.
          depelim wfa. rewrite H0. constructor; auto.
          now eapply All2_eq_binder_subst_context_inst. }
      (* move: X6. *)
      eapply conv_context_rel_app.
      eapply conv_context_rel_app in cv.
      etransitivity; tea.
      eapply conv_context_rel_app.
      rewrite /pre_case_predicate_context_gen.
      (* We need to reason on the argument spines *)

      constructor. clear X9.
      match goal with
      |- All2_fold _ ?X ?Y =>
        change (conv_context_rel Σ Γ X Y)
      end.
      apply conv_context_rel_app.
      eapply onone_red_cont_context_subst.
      2:{ eapply subslet_untyped_subslet, sppars. }
      2:{ eapply subslet_untyped_subslet, sppars'. }
      rewrite subst_instance_expand_lets_ctx.
      eapply wf_local_expand_lets. now rewrite subst_instance_app app_context_assoc in X4.
      tas. all:tea. all:len.
      constructor; auto.
      eapply equality_mkApps; tea. reflexivity.
      eapply All2_app. eapply All2_map.
      eapply OnOne2_All2; tea.
      intros. eapply red_conv.
      eapply weakening_red_0. now rewrite !lengths.
      now eapply red1_red. reflexivity.
      eapply All2_refl. reflexivity. } *)
    have isty' : isType Σ Γ (mkApps (tInd ci (puinst p)) (params' ++ indices)).
    { eexists; eapply isType_mkApps_Ind; tea. }
    have wfcpc' : wf_local Σ (Γ ,,, case_predicate_context ci mdecl idecl (set_pparams p params')).
    { eapply wf_case_predicate_context; tea. }
    have eqindices : equality_terms Σ Γ indices indices.
    { now eapply spine_subst_wt_terms, wt_terms_equality in spargs'. }
    have typec' : Σ;;; Γ |- c : mkApps (tInd ci (puinst p)) (params' ++ indices).
    { eapply type_equality; tea.
      eapply equality_eq_le. eapply equality_mkApps; pcuic.
      eapply All2_app => //. now apply: red_terms_equality_terms. }
    set (pctx := (inst_case_predicate_context (set_pparams p params'))) in *.
    pose proof (snd (All2_fold_All2 _ _ _) X1). symmetry in X7. move:X7.
    change (pcontext p) with (pcontext (set_pparams p params')).
    move/(PCUICAlpha.inst_case_predicate_context_eq wfp') => eqctx.
    have wfpctx : wf_local Σ (Γ,,, inst_case_predicate_context (set_pparams p params')).
    { eapply wf_local_alpha; tea; auto.
      eapply All2_app => //.
      now eapply All2_fold_All2 in eqctx.
      eapply All2_refl; reflexivity. }
    have eqpctx : Σ ⊢ Γ ,,, pctx = Γ ,,, case_predicate_context ci mdecl idecl (set_pparams p params').
    { symmetry.
      rewrite /pctx.
      eapply into_context_equality => //.
      now eapply wf_local_closed_context.
      now eapply wf_local_closed_context.
      eapply upto_names_conv_context.
      eapply eq_context_upto_cat. apply eq_context_upto_refl; tc.
      now apply eq_context_gen_upto. }
    epose proof (wf_case_branches_types' (p:=set_pparams p params') ps _ brs isdecl isty' wfp').
    cbv zeta in X7; forward_keep X7.
    { eapply closed_context_conversion; tea. }
    do 2 forward X7 by auto.
    eapply type_equality; tea.
    { econstructor; tea.
      (* The branches contexts also depend on the parameters. *)
      apply All2i_nth_hyp in X7.
      eapply All2i_All2_mix_left in X7; tea.
      2:now eapply Forall2_All2 in H4.
      eapply All2i_All2i_mix in X9; tea. clear X7.
      eapply (All2i_impl X9); clear X9.
      intros cstr cdecl br. cbv zeta.
      rewrite !case_branch_type_fst.
      do 2 case. move=> wfbr [] hnth. case => wfbrctx wfcbc' wfcbcty'.
      case => eqbctx. case. case => wfbctx _.
      move=> [] Hbody [] IHbody [] brty IHbrty.
      eapply conj_impl. solve_all. move=> cvcbc.
      apply conj_impl; [|move=> wfcb'].
      { now eapply typing_wf_local in wfcbcty'. }
      split => //.
      have declc : declared_constructor Σ (ci, cstr) mdecl idecl cdecl.
      { split => //. }
      have convbctx : Σ ⊢ Γ,,, case_branch_context ci mdecl p (forget_types (bcontext br)) cdecl = 
        Γ,,, case_branch_context ci mdecl (set_pparams p params') (forget_types (bcontext br)) cdecl.
      { etransitivity. symmetry. eapply context_equality_rel_app.
        rewrite /case_branch_context /case_branch_context_gen /pre_case_branch_context_gen.
        eapply conv_ctx_set_binder_name. admit.
        etransitivity; revgoals.
        rewrite /case_branch_context /case_branch_context_gen /pre_case_branch_context_gen.
        eapply context_equality_rel_app.
        eapply conv_ctx_set_binder_name. admit.
        rewrite /inst_case_context. cbn.
        eapply context_equality_rel_app.
        eapply (substitution_context_equality_subst_conv (Γ' := smash_context [] (ind_params mdecl)@[puinst p]) (Γ'':=[])).
        2:{ eapply All2_rev.
          eapply OnOne2_prod_inv in X2 as [redp _].
          now eapply red_terms_equality_terms. }
        apply context_equality_rel_app. 
        eapply context_equality_refl, wf_local_closed_context.
        rewrite /=. rewrite /cstr_branch_context.
        rewrite subst_instance_expand_lets_ctx.
        eapply wf_local_expand_lets.
        red in wfbr.
        epose proof (on_constructor_inst_wf_args declc (puinst p) H1) as onc.
        rewrite -app_context_assoc; eapply weaken_wf_local; auto.
        rewrite subst_instance_subst_context.
        now rewrite subst_instance_inds (subst_instance_id_mdecl _ _ _ H1).
        apply sppars. apply sppars'.
        eapply wf_local_closed_context.
        eapply wf_local_smash_end.
        apply weaken_wf_local => //. eapply on_minductive_wf_params; tea. eapply isdecl. }
      eapply (type_equality (le:=false)); tea. 
      + eapply closed_context_conversion; tea.
      + exists ps. red. exact wfcbcty'.
      + eapply equality_mkApps; tea.
        { rewrite /ptm. cbn [preturn set_pparams].
          rewrite !lift_it_mkLambda_or_LetIn. 
          eapply equality_it_mkLambda_or_LetIn.
          relativize #|cstr_args cdecl|.
          eapply weakening_context_equality; tea.
          apply context_equality_refl, wf_local_closed_context => //.
          now apply (case_branch_context_length_args wfbr).
          rewrite !case_predicate_context_length // /= Nat.add_0_r.
          relativize #|pcontext p|. relativize #|cstr_args cdecl|.
          eapply weakening_equality; tea. 
          apply isType_equality_refl. now exists ps.
          now apply wf_local_closed_context.
          now apply case_branch_context_length_args.
          now rewrite case_predicate_context_length. }
        cbn.
        eapply All2_app.
        - rewrite /case_branch_context /case_branch_context_gen /pre_case_branch_context
          /pre_case_branch_context_gen /inst_case_context. cbn.
          symmetry. rewrite /subst_context PCUICRename.map2_set_binder_name_fold ?lengths.
          now apply wf_branch_length.
          rewrite -/(subst_context _ _ _).
          relativize #|cstr_args cdecl|.
          eapply equality_terms_subst.
          2:eapply sppars'. 2:eapply sppars.
          { eapply wf_local_closed_context, wf_local_smash_end, weaken_wf_local => //.
            eapply (on_minductive_wf_params isdecl) => //. }
          { apply All2_rev; symmetry. now apply red_terms_equality_terms. }
          { epose proof (on_constructor_closed_indices_inst declc (u:=puinst p) H1).
            eapply equality_terms_refl.
            { rewrite /cstr_branch_context.
              apply wf_local_closed_context.
              move: wfbrctx.
              move/wf_local_expand_lets. cbn.
              rewrite subst_instance_expand_lets_ctx map2_set_binder_name_expand_lets ?lengths //.
              apply (wf_branch_length wfbr). 
              rewrite subst_instance_subst_context instantiate_inds //.
              eapply declc. }
            rewrite 2!forallb_map.
            eapply All_map_inv in X7. eapply All_forallb, All_impl; tea.
            cbn; intros x clx.
            apply closedn_on_free_vars.
            rewrite -on_free_vars_closedn in clx.
            len. rewrite !map2_length !lengths.
            now apply wf_branch_length. rewrite lengths in clx.
            rewrite (wf_branch_length wfbr).
            rewrite (Nat.add_comm _ #|Γ|) Nat.add_assoc (Nat.add_comm _ #|Γ|).
            rewrite -(context_assumptions_subst_instance (puinst p)) closedn_expand_lets_eq.
            eapply closedn_ctx_upwards. eapply (declared_inductive_closed_params_inst declc). lia.
            len. rewrite (Nat.add_comm #|ind_params mdecl|).
            eapply closed_upwards; tea. len. }
          pose proof (wf_branch_length wfbr).
          now rewrite map2_length !lengths.
        - apply All2_tip, equality_mkApps; [apply into_equality => //; try reflexivity|].
          now eapply wf_local_closed_context.
          eapply All2_app. eapply All2_map.
          eapply OnOne2_prod_inv in X2 as [X2 _].
          eapply red_terms_equality_terms in redpars.
          eapply All2_impl; tea. intros.
          relativize #|cstr_args cdecl|; [eapply (weakening_equality (Γ' := []))|] => //.
          now eapply wf_local_closed_context.
          now eapply case_branch_context_length_args.
          eapply equality_terms_refl. now apply wf_local_closed_context.
          eapply forallb_impl. 2:eapply closedn_to_extended_list.
          intros. rewrite !lengths. rewrite case_branch_context_length_args //.
          eapply closedn_on_free_vars, closed_upwards; tea. lia. }
    + rewrite /ptm.
      eapply equality_mkApps.
      { eapply equality_it_mkLambda_or_LetIn => //.
        now symmetry. cbn [preturn set_pparams].
        eapply wt_equality_refl; eauto. }
      eapply All2_app; eauto. apply All2_tip.
      now eapply wt_equality_refl.

  - (* Case congruence on the return clause context *)
    clear IHHu. destruct X0, X4 as []. 
    set (ptm := it_mkLambda_or_LetIn _ _).
    assert (isType Σ Γ (mkApps ptm (indices ++ [c]))).
    { eapply validity. econstructor; eauto.
      apply (All2i_impl X9). intuition auto. }
    eapply type_Cumul'; tea.
    * eapply type_Case; eauto.
      + cbn [preturn set_preturn]. eapply forall_u.

        rewrite /inst_case_predicate_context in Hu.
        rewrite /case_predicate_context /case_predicate_context_gen.

        cbn -[case_predicate_context].
        etransitivity; tea.
        eapply red_one_decl_conv_context in o.
        symmetry. exact o.
        rewrite /case_predicate_context /=.
        now rewrite -(OnOne2_local_env_forget_types _ _ _ o).
      + cbn. eapply context_conversion; tea.
        eapply wf_local_app; tea.
        eapply w; tea; reflexivity.
        now eapply red_one_decl_conv_context in o.
      + rewrite /case_predicate_context.
        now rewrite -(OnOne2_local_env_forget_types _ _ _ o).
      + eapply Forall2_All2 in H4.
        eapply All2i_All2_mix_left in X9; tea. eapply (All2i_impl X9); intuition auto.
        rewrite case_branch_type_fst.
        set (cbty := case_branch_type _ _ _ _ _ _ _).
        assert (Σ ;;; Γ ,,, bcontext y |- (cbty x).2 : tSort ps).
        { eapply b3.
          rewrite /cbty /case_branch_type /=.
          eapply red1_mkApps_f.
          relativize #|cstr_args x|.
          eapply (weakening_red1 _ []); tea. 2:tas.
          now eapply red1_it_mkLambda_or_LetIn_ctx.
          apply (wf_branch_length a2). }
        solve_all.
        eapply type_Cumul; tea.
        rewrite /cbty /case_branch_type.
        eapply conv_cumul; cbn.
        eapply equality_mkApps; tea.
        2:{ eapply All2_refl. reflexivity. }
        relativize #|cstr_args x|.
        eapply (weakening_conv _ _ []); tea. 2:tas.
        eapply equality_it_mkLambda_or_LetIn; tea. 2:reflexivity.
        now eapply red_one_decl_conv_context.
        apply (wf_branch_length a2).
      * eapply conv_cumul.
        eapply equality_mkApps; tea.
        2:{ eapply All2_refl; reflexivity. }
        eapply equality_it_mkLambda_or_LetIn; tea. 2:reflexivity.
        simpl.
        eapply red_one_decl_conv_context in o.
        now symmetry.
          
  - (* Case congruence on the return clause type *) 
    destruct X1, X4 as [].
    set (ptm := it_mkLambda_or_LetIn _ _).
    assert (isType Σ Γ (mkApps ptm (indices ++ [c]))).
    { eapply validity. econstructor; eauto.
      apply (All2i_impl X9). intuition auto. }
    eapply type_Cumul'; tea.
    * eapply type_Case; eauto.
      eapply All2i_All2_mix_left in X9; tea.
      2:{ eapply Forall2_All2 in H4. exact H4. }
      eapply (All2i_impl X9); intuition auto.
      all:set (brty := case_branch_type _ _ _ _ _ _ _ _).
      pose proof (wf_branch_length a2).
      
      assert (Σ ;;; (Γ ,,, bcontext y) |- brty.2 : tSort ps).
      { eapply b3.
        rewrite /brty /case_branch_type /=.
        eapply red1_mkApps_f.
        relativize #|cstr_args x|.
        eapply (weakening_red1 _ []); tea. 2:tas.
        now eapply red1_it_mkLambda_or_LetIn. }
      intuition auto.
      eapply type_Cumul; tea.
      rewrite /brty.
      rewrite /case_branch_type /case_branch_type_gen /=.
      eapply conv_cumul.
      eapply equality_mkApps; tea.
      2:{ eapply All2_refl. reflexivity. }
      relativize #|cstr_args x|.
      eapply (weakening_conv _ _ []); tea. 2:tas.
      eapply equality_it_mkLambda_or_LetIn; tea. reflexivity.
      eapply red_conv; tea. now eapply red1_red.
    * eapply conv_cumul, equality_mkApps; tea; try reflexivity.
      eapply equality_it_mkLambda_or_LetIn; tea. reflexivity.
      eapply conv_conv_ctx; tea. symmetry.
      eapply red_conv => //. simpl. now eapply red1_red.
      reflexivity.
      eapply All2_same; reflexivity.
    
  - (* Case congruence on discriminee *) 
    destruct X4 as [].
    set (ptm := it_mkLambda_or_LetIn _ _).
    destruct X1.
    assert (isType Σ Γ (mkApps ptm (indices ++ [c]))).
    { eapply validity. econstructor; eauto.
      apply (All2i_impl X9). intuition auto. }
    eapply type_Cumul'. eapply type_Case; eauto.
    * solve_all.
    * tas.
    * eapply conv_cumul, conv_sym, red_conv, red_mkApps; auto.
      eapply All2_app; [eapply All2_refl; reflexivity|now constructor].
    
  - (* Case congruence on branches *)
    destruct X1, X4.
    eapply type_Case; eauto.
    * eapply Forall2_All2 in H4.
      move: (All2_sym _ _ _ H4) => wfb.
      red. eapply All2_Forall2.
      apply All2_sym.
      eapply (OnOne2_All2_All2 o wfb); auto.
      intros [] []; simpl. intros.
      destruct X1 as [[r1 eq]|[? ?]]. subst bcontext0. exact H.
      red. red in H.
      eapply OnOne2_local_env_forget_types in o0.
      now rewrite -o0.
    * eapply (OnOne2_All2i_All2i o X9).
      intros n [] []; simpl. intros. intuition auto.
      intros n [ctx b] [ctx' b'] cdecl; cbn.
      rewrite !case_branch_type_fst.
      intros [[red <-]|[red <-]];
      intros [[[wfctx IHctx] convctx] [[Hb [wfcbc IHcbc]] [IHb [Hbty IHbty]]]].
      intuition auto.
      rewrite /case_branch_type -(OnOne2_local_env_forget_types _ _ _ red).
      intuition auto; tea.
      + eapply wf_local_app; tea.
        eapply IHctx; tea; reflexivity.
      + eapply red_one_decl_conv_context in red.
        etransitivity; tea. now symmetry.
      + eapply context_conversion; tea.
        eapply wf_local_app; tea.
        eapply IHctx; tea; reflexivity.
        eapply red_one_decl_conv_context in red.
        now symmetry.
      + eapply context_conversion; tea.
        eapply wf_local_app; tea.
        eapply IHctx; tea; reflexivity.
        eapply red_one_decl_conv_context in red.
        now symmetry.
      
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
    { eapply isType_mkApps_Ind_inv in X1 as [parsubst [argsubst Hind]]; eauto.
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
    epose proof (declared_projection_type_and_eq wf isdecl).
    unshelve eapply Construct_Ind_ind_eq in typec'; eauto.
    destruct (on_declared_constructor declc) as [[onmind oin] [cs [Hnth onc]]].
    simpl in typec'.
    simpl in X2.
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
    destruct X2 as [projty projeq].
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
    rewrite H in e. destruct (proj2 isdecl). simpl in H1. subst pars.
    replace (ind_npars mdecl + narg - ind_npars mdecl) with narg in e by lia.
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
        clear iswat sp. eapply nth_error_Some_length in e.
        rewrite List.skipn_length in e. lia. }
    destruct sp as [decl [Hnth Hu0]].
    simpl in on_projs. red in on_projs.
    len in Hnth. 
    eapply type_Cumul'; eauto.
    { rewrite firstn_skipn.
      eapply (isType_subst_instance_decl _ _ _ _ _ u wf isdecl.p1.p1) in projty; eauto.
      destruct projty as [s' Hs].
      exists s'. red in Hs.
      rewrite /= /map_decl /= in Hs.
      eapply (weaken_ctx Γ) in Hs; auto.
      rewrite (subst_app_simpl [_]).
      destruct projeq as [decl' [[[hnthargs wf'] projeq1] projty']].
      simpl.
      eapply (substitution0 _ _ _ _ _ _ (tSort s')). tea.
      simpl.
      eapply (PCUICSubstitution.substitution _ Γ (subst_instance u (smash_context [] (ind_params mdecl)))
        _ [vass _ _] _ (tSort s')); eauto.
      rewrite firstn_all2 in iparsubst0. lia.
      eapply spine_subst_smash in iparsubst0; auto.
      rewrite subst_instance_smash.
      eapply iparsubst0. exact Hs.
      simpl.
      rewrite subst_instance_mkApps subst_mkApps /=.
      rewrite [subst_instance_instance _ _](subst_instance_id_mdecl Σ) // subst_instance_to_extended_list.
      rewrite firstn_all2 in iparsubst0. lia.
      eapply spine_subst_smash in iparsubst0; auto.
      rewrite subst_instance_smash /=.
      rewrite /to_extended_list (spine_subst_subst_to_extended_list_k iparsubst0).
      assumption. }
    rewrite firstn_skipn.
    rewrite PCUICSigmaCalculus.smash_context_app PCUICSigmaCalculus.smash_context_acc in on_projs.
    rewrite nth_error_app_lt in on_projs.
    { autorewrite with len. simpl. 
      eapply nth_error_Some_length in Hnth. autorewrite with len in Hnth.
      now simpl in Hnth. }
    rewrite nth_error_subst_context in on_projs.
    epose proof (nth_error_lift_context_eq _ (smash_context [] (ind_params mdecl))).
    autorewrite with len in H1. simpl in H1.
    erewrite -> H1 in on_projs. clear H1.
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
    set (indsubst := ind_subst _ _ _).
    set (projsubst := projs _ _ _).
    rewrite !subst_instance_subst.
    rewrite subst_instance_lift.
    rewrite !subst_instance_subst.
    epose proof (commut_lift_subst_rec _ _ 1 narg narg).
    rewrite Nat.add_1_r in H2. rewrite <- H2 => //. clear H2.
    rewrite (subst_app_decomp [_]). len.
    rewrite heq_length.
    simpl. rewrite lift_mkApps. simpl.
    rewrite (distr_subst [_]). simpl. len.
    rewrite {2}/projsubst projs_length.
    rewrite simpl_subst_k // [subst_instance _ projsubst]subst_instance_projs.
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
    len.
    rewrite (distr_subst (List.rev args)). len.
    assert (map (subst0 (List.rev args))
    (subst_instance u (extended_subst (ind_params mdecl) 0))  = 
      iparsubst) as ->. 
    { rewrite firstn_all2 in iparsubst0. lia.
      rewrite subst_instance_extended_subst.
      pose proof (inst_ctx_subst iparsubst0).
      eapply context_subst_extended_subst in X2.
      rewrite X2. eapply map_ext.
      intros. now rewrite subst_inst Upn_0. }
    len in cum. simpl in cum.
    move: Hdecl'.
    rewrite /pargctxu /argctxu /argsu.
    rewrite !smash_context_subst_empty.
    rewrite -(subst_instance_smash _ _ []).
    rewrite !nth_error_subst_context.
    rewrite nth_error_map Hdecl. simpl => [= Hdecl'].
    subst decl'. simpl in cum.
    len in cum; simpl in cum. 
    assert(context_assumptions (cstr_args cdecl) -
      S (context_assumptions (cstr_args cdecl) - S narg) = narg) by lia.
    rewrite H2 in cum. 
    set (idx := S (context_assumptions (cstr_args cdecl) - S narg)) in *.
    assert (wfpargctxu1 : wf_local Σ (Γ ,,, skipn idx (smash_context [] pargctxu1))).
    { simpl. apply wf_local_app_skipn. apply wf_local_smash_end; auto.
      apply idxsubst0. }
    destruct cum as [[cr mapd] cumdecls].
    destruct decl'' as [na [b|] ty]; simpl in mapd; try discriminate.
    depelim cumdecls. rename c into cum.
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
    rewrite (subslet_length iparsubst0); len.
    assert (wf_local Σ (Γ ,,, subst_instance u (ind_params mdecl))).
    { eapply weaken_wf_local; eauto. eapply on_minductive_wf_params => //. pcuic. }
    eapply (substitution_cumul _ _ _ []); eauto. eapply iparsubst0.
    simpl.
    rewrite (distr_subst_rec _ _ _ #|ind_params mdecl| 0); len => /=.
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
    set (inds' := ind_subst _ _ _).
    change (map (subst_instance u) inds') with (subst_instance u inds').
    rewrite instantiate_inds => //. eapply isdecl.
    rewrite (subst_closedn (List.rev args)); [|reflexivity].
    rewrite projs_length.
    eapply (closedn_subst _ 0).  
    eapply (declared_minductive_closed_inds isdecl).
    simpl. autorewrite with len.
    rewrite closedn_subst_instance.
    clear projsubsl.
    eapply closed_wf_local in wfdecl.
    rewrite closedn_ctx_app in wfdecl.
    move/andb_and: wfdecl => [_ wfdecl].
    len in wfdecl.
    simpl in wfdecl.
    eapply closedn_ctx_decl in wfdecl; eauto.
    len in wfdecl.
    simpl in wfdecl.
    eapply closed_upwards. eauto.
    lia. auto.

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
    eapply type_Cumul; eauto.
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
      1: exists s.
      1: change (tSort s) with (subst [b] #|Γ'| (tSort s)).
      all: eapply PCUICSubstitution.substitution; tea.
    - rewrite subst_context_snoc0. simpl.
      inversion HH; subst; cbn in *. destruct X0 as [s X0].
      change (Γ,, vdef na b t ,,, Γ') with (Γ ,,, [vdef na b t] ,,, Γ') in *.
      assert (subslet Σ Γ [b] [vdef na b t]). {
        pose proof (cons_let_def Σ Γ [] [] na b t) as XX.
        rewrite !subst_empty in XX. apply XX. constructor.
        apply wf_local_app_l in X. inversion X; subst; cbn in *; assumption. }
      constructor; cbn; auto. exists s.
      change (tSort s) with (subst [b] #|Γ'| (tSort s)).
      all: eapply PCUICSubstitution.substitution; tea.
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
    apply equality_Sort_r_inv in H.
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
