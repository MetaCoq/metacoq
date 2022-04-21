(* Distributed under the terms of the MIT license. *)
From Coq Require Import Program ssreflect ssrbool.
From Equations Require Import Equations.
Set Equations Transparent.
From MetaCoq.Template Require Import config utils Kernames MCRelations.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICPrimitive
  PCUICReduction
  PCUICReflect PCUICWeakeningEnvConv PCUICWeakeningEnvTyp PCUICCasesContexts
  PCUICWeakeningConv PCUICWeakeningTyp
  PCUICContextConversionTyp
  PCUICTyping PCUICGlobalEnv PCUICInversion PCUICGeneration
  PCUICConfluence PCUICConversion
  PCUICUnivSubstitutionTyp
  PCUICCumulativity PCUICSR PCUICSafeLemmata
  PCUICValidity PCUICPrincipality PCUICElimination 
  PCUICOnFreeVars PCUICWellScopedCumulativity PCUICSN PCUICEtaExpand.
     
From MetaCoq.SafeChecker Require Import PCUICErrors PCUICWfEnv PCUICWfEnvImpl PCUICSafeReduce PCUICSafeRetyping.
From MetaCoq.Erasure Require Import EAstUtils EArities Extract Prelim EDeps ErasureCorrectness.

Local Open Scope string_scope.
Set Asymmetric Patterns.
Local Set Keyed Unification.
Set Default Proof Using "Type*".
Import MCMonadNotation.

Implicit Types (cf : checker_flags).

#[local] Existing Instance extraction_normalizing.

Notation alpha_eq := (All2 (PCUICEquality.compare_decls eq eq)).

Lemma wf_local_rel_alpha_eq_end {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Δ Δ'} : 
  wf_local Σ Γ ->
  alpha_eq Δ Δ' ->
  wf_local_rel Σ Γ Δ -> wf_local_rel Σ Γ Δ'.
Proof.
  intros wfΓ eqctx wf.
  apply wf_local_app_inv.
  eapply wf_local_app in wf => //.
  eapply PCUICSpine.wf_local_alpha; tea.
  eapply All2_app => //. reflexivity.
Qed.

Section OnInductives.
  Context {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ}.
  
  Lemma on_minductive_wf_params_weaken {ind mdecl Γ} {u} :
    declared_minductive Σ.1 ind mdecl ->
    consistent_instance_ext Σ (ind_universes mdecl) u ->
    wf_local Σ Γ ->
    wf_local Σ (Γ ,,, (ind_params mdecl)@[u]).
  Proof.
    intros.
    eapply weaken_wf_local; tea.
    eapply PCUICArities.on_minductive_wf_params; tea.
  Qed.
  
  Context {mdecl ind idecl}
    (decli : declared_inductive Σ ind mdecl idecl).
  
  Lemma on_minductive_wf_params_indices_inst_weaken {Γ} (u : Instance.t) :
    consistent_instance_ext Σ (ind_universes mdecl) u ->
    wf_local Σ Γ ->
    wf_local Σ (Γ ,,, (ind_params mdecl ,,, ind_indices idecl)@[u]).
  Proof.
    intros. eapply weaken_wf_local; tea.
    eapply PCUICInductives.on_minductive_wf_params_indices_inst; tea.
  Qed.


End OnInductives.

Local Existing Instance extraction_checker_flags.
Definition wf_ext_wf Σ : wf_ext Σ -> wf Σ := fst.
#[global]
Hint Resolve wf_ext_wf : core.

Ltac specialize_Σ wfΣ :=
  repeat match goal with | h : _ |- _ => specialize (h _ wfΣ) end. 

Section fix_sigma.
  Variable Σ : wf_env_ext.

  Local Definition HΣ : ∥ wf Σ ∥.
  Proof.
    exact (map_squash (wf_ext_wf _) Σ).
  Qed.

  Definition abstract_env_rel' := @abstract_env_ext_rel _ _ optimized_abstract_env_ext_struct.

  Definition term_rel : Relation_Definitions.relation (∑ Γ t, forall Σ0 : global_env_ext, abstract_env_rel' Σ Σ0 -> welltyped Σ0 Γ t) :=
    fun '(Γ2; B; H) '(Γ1; t1; H2) =>
    forall Σ0 : global_env_ext, abstract_env_rel' Σ Σ0 -> 
      ∥∑ na A, red Σ0 Γ1 t1 (tProd na A B) × (Γ1,, vass na A) = Γ2∥.

  Definition cod B t := match t with tProd _ _ B' => B = B' | _ => False end.

  Lemma wf_cod : WellFounded cod.
  Proof.
    sq. intros ?. induction a; econstructor; cbn in *; intros; try tauto; subst. eauto.
  Defined.

  Lemma wf_cod' : WellFounded (Relation_Operators.clos_trans _ cod).
  Proof.
    eapply Subterm.WellFounded_trans_clos. exact wf_cod.
  Defined.

  Lemma Acc_no_loop X (R : X -> X -> Prop) t : Acc R t -> R t t -> False.
  Proof.
    induction 1. intros. eapply H0; eauto.
  Qed.

  Ltac sq' := 
    repeat match goal with
          | H : ∥ _ ∥ |- _ => destruct H; try clear H
          end; try eapply sq.
          
  Definition wf_reduction_aux : WellFounded term_rel.
  Proof.
    intros (Γ & s & H). sq'.
    assert (wfΣ' : abstract_env_rel' Σ Σ) by reflexivity.
    pose proof (abstract_env_ext_wf _ wfΣ') as wf. sq. 
    set (H' := H _ wfΣ'). 
    induction (normalisation Σ _ Γ s H') as [s _ IH]. cbn in IH.
    induction (wf_cod' s) as [s _ IH_sub] in Γ, H , H', IH |- *.
    econstructor.
    intros (Γ' & B & ?) [(na & A & ? & ?)]; eauto. subst. 
    eapply Relation_Properties.clos_rt_rtn1 in r. inversion r.
      + subst. eapply IH_sub. econstructor. cbn. reflexivity.
        intros. eapply IH.
        inversion H0.
        * subst. econstructor. eapply prod_red_r.  eassumption.
        * subst. eapply cored_red in H2 as [].
          eapply cored_red_trans. 2: eapply prod_red_r. 2:eassumption.
          eapply PCUICReduction.red_prod_r. eauto.
        * constructor. do 2 eexists. now split.
      + subst. eapply IH.
        * eapply red_neq_cored.
          eapply Relation_Properties.clos_rtn1_rt. exact r.
          intros ?. subst.
          eapply Relation_Properties.clos_rtn1_rt in X0.
          eapply cored_red_trans in X; [| exact X0 ].
          eapply Acc_no_loop in X. eauto.
          eapply @normalisation; eauto.
        * constructor. do 2 eexists. now split.
  Unshelve.
  - intros. cbn in H2; subst. destruct H' as [].
    eapply inversion_Prod in X as (? & ? & ? & ? & ?) ; auto.
    eapply cored_red in H0 as [].
    econstructor. econstructor. econstructor. eauto.
    2:reflexivity. econstructor; pcuic. 
    eapply subject_reduction; eauto.
  - intros. cbn in H0; subst.  eapply red_welltyped; sq.
    3:eapply Relation_Properties.clos_rtn1_rt in r; eassumption. 
    all:eauto.
  Defined.

  Instance wf_reduction : WellFounded term_rel.
  Proof.
    refine (Wf.Acc_intro_generator 1000 _).
    exact wf_reduction_aux.
  Defined.
  
  Opaque wf_reduction.
  
  Ltac sq := 
    repeat match goal with
          | H : ∥ _ ∥ |- _ => destruct H
          end; try eapply sq.

  #[tactic="idtac"]
  Equations? is_arity Γ (HΓ : forall Σ0 : global_env_ext, abstract_env_rel' Σ Σ0 -> ∥wf_local Σ0 Γ∥) T (HT : forall Σ0 : global_env_ext, abstract_env_rel' Σ Σ0 -> welltyped Σ0 Γ T) : bool
    by wf ((Γ;T;HT) : (∑ Γ t, forall Σ0 : global_env_ext, abstract_env_rel' Σ Σ0 -> welltyped Σ0 Γ t)) term_rel :=
      {
        is_arity Γ HΓ T HT with inspect (@reduce_to_sort _ _ optimized_abstract_env_ext_impl Σ Γ T HT) => {
        | exist (Checked_comp H) rsort => true ;
        | exist (TypeError_comp _) rsort with 
            inspect (reduce_to_prod (X_type:=optimized_abstract_env_ext_impl) (X:=Σ) Γ T HT) => {
          | exist (Checked_comp (na; A; B; H)) rprod := is_arity (Γ,, vass na A) _ B _
          | exist (TypeError_comp e) rprod => false } }
      }.
  Proof.
    - clear rprod is_arity rsort a0.
      intros Σ' wfΣ'; specialize (H Σ' wfΣ').
      repeat specialize_Σ wfΣ'. 
      destruct HT as [s HT].
      pose proof (abstract_env_ext_wf _ wfΣ') as [wf].
      sq.  
      eapply subject_reduction_closed in HT; tea.
      eapply inversion_Prod in HT as [? [? [? []]]].
      now eapply typing_wf_local in t1. pcuic. pcuic.
    - clear rprod is_arity rsort a0.
      intros Σ' wfΣ'; specialize (H Σ' wfΣ').
      repeat specialize_Σ wfΣ'. 
      destruct HT as [s HT].
      pose proof (abstract_env_ext_wf _ wfΣ') as [wf].
      sq.
      eapply subject_reduction_closed in HT; tea.
      eapply inversion_Prod in HT as [? [? [? []]]].
      now eexists. all:pcuic.
    - cbn. clear rsort is_arity rprod.
      intros Σ' wfΣ'; specialize (H Σ' wfΣ').
      pose proof (abstract_env_ext_wf _ wfΣ') as [wf].
      repeat specialize_Σ wfΣ'. subst Σ'. 
      destruct HT as [s HT].
      sq.
      eapply subject_reduction_closed in HT; tea. 2:pcuic.
      eapply inversion_Prod in HT as [? [? [? []]]]. 2:pcuic.
      exists na, A. split => //.
      eapply X.
  Defined.
  
  Lemma is_arityP Γ (HΓ : forall Σ0 : global_env_ext, abstract_env_rel' Σ Σ0 -> ∥wf_local Σ0 Γ∥) T (HT : forall Σ0 : global_env_ext, abstract_env_rel' Σ Σ0 -> welltyped Σ0 Γ T) :
    reflect (Is_conv_to_Arity Σ Γ T) (is_arity Γ HΓ T HT).
  Proof.
    funelim (is_arity Γ HΓ T HT).
    - constructor.
      destruct H as [s Hs].
      clear H0 rsort. specialize (Hs _ eq_refl) as [Hs].
      exists (tSort s) ; split => //.
    - clear H0 H1. destruct X; constructor; clear rprod rsort;
      specialize (H _ eq_refl) as [Hp].
      * red.
        destruct i as [T' [[HT'] isa]].
        exists (tProd na A T'); split => //. split.
        etransitivity; tea. now eapply closed_red_prod_codom.
      * intros [T' [[HT'] isa]].
        assert (wfΣ' : abstract_env_rel' Σ Σ) by reflexivity.
        pose proof (abstract_env_ext_wf _ wfΣ') as [wf].
        destruct (PCUICContextConversion.closed_red_confluence Hp HT') as (? & ? & ?); eauto.
        eapply invert_red_prod in c as (? & ? & []); eauto. subst.
        apply n. red. exists x1.
        split => //.
        eapply isArity_red in isa. 2:exact c0.
        now cbn in isa.
    - constructor.
      clear H H0.
      symmetry in rprod. symmetry in rsort.
      assert (wfΣ' : abstract_env_rel' Σ Σ) by reflexivity.
      pose proof (abstract_env_ext_wf _ wfΣ') as [wf].
      specialize_Σ wfΣ'.
      intros isc. eapply Is_conv_to_Arity_inv in isc as [].
      * destruct H as [na [A [B [Hr]]]].
        apply e. exists na, A, B. intros. cbn in wfΣ. subst Σ0. now sq.
      * destruct H as [u [Hu]].
        apply a0. exists u. intros. cbn in wfΣ. subst Σ0. now sq.
  Qed.
  
End fix_sigma.

Opaque wf_reduction_aux.
Transparent wf_reduction.

(* Top.sq should be used but the behavior is a bit different *)
Local Ltac sq := 
  repeat match goal with
         | H : ∥ _ ∥ |- _ => destruct H
         end; try eapply sq.

(** Deciding if a term is erasable or not as a total function on well-typed terms.
  A term is erasable if:
  - it represents a type, i.e., its type is an arity
  - it represents a proof: its sort is Prop.
*)

Derive NoConfusion for typing_result_comp.

Lemma squash_isType_welltyped :
  forall {cf} {Σ : global_env_ext} {Γ : context} {T : term},
  ∥ isType Σ Γ T ∥ -> welltyped Σ Γ T.
Proof. intros. destruct H. now eapply isType_welltyped. Qed.

Opaque type_of_typing.
Equations? sort_of_type {cf} {nor : normalizing_flags} (X_type : abstract_env_ext_impl) (X : X_type.π1) (Γ : context) (t : PCUICAst.term) 
  (wt : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> ∥ isType Σ Γ t ∥) :
  (∑ u : Universe.t, forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> 
    ∥ Σ ;;; Γ |- t : tSort u ∥) :=
  sort_of_type X_type X Γ t wt with (@type_of_typing cf _ X_type X Γ t _) :=
    { | T with inspect (reduce_to_sort Γ T.π1 _) := 
      { | exist (Checked_comp (u; Hu)) hr => (u; _)
        | exist (TypeError_comp _ _) ns => False_rect _ _ } }.
Proof.
  - eapply squash_isType_welltyped, wt; eauto.
  - cbn. specialize (X0 _ wfΣ). destruct X0 as [[Ht _]].
    pose proof (abstract_env_ext_wf _ wfΣ) as [wf]. 
    eapply validity in Ht.
    now eapply isType_welltyped.
  - clear hr. 
    pose proof (abstract_env_ext_wf _ H) as [wf]. 
    specialize (Hu _ H) as [Hred]. cbn in Hred.
    specialize (X0 _ H) as [[hty hp]].
    sq. eapply type_reduction_closed; tea.
  - epose proof (abstract_env_ext_exists X) as [[Σ wfΣ]].
    epose proof (abstract_env_ext_wf X wfΣ) as [hwfΣ].
    symmetry in ns. pose proof (reduce_to_sort_complete _ wfΣ _ _ ns).
    specialize (wt _ wfΣ). clear ns. cbn in *.
    specialize (X0 _ wfΣ) as [[hty hp]].
    eapply validity in hty. destruct wt as [[s Hs]].
    red in hp. specialize (hp _ Hs).
    eapply ws_cumul_pb_Sort_r_inv in hp as [s' [hs' _]].
    eapply (H s' hs').
Defined.
Transparent type_of_typing.

Lemma unique_sorting_equality_prop_l {pb} {Σ : global_env_ext} {Γ T U s s'} : 
  wf_ext Σ ->
  Σ ;;; Γ |- T : tSort s ->
  Σ ;;; Γ |- U : tSort s' ->
  Σ ;;; Γ ⊢ T ≤[pb] U ->
  Universe.is_prop s -> Universe.is_prop s'.
Proof.
  intros wfΣ HT HU cum isp.
  eapply PCUICSpine.ws_cumul_pb_le_le in cum.
  eapply ws_cumul_pb_alt_closed in cum as [v [v' [eqv]]].
  eapply subject_reduction_closed in HT; tea.
  eapply subject_reduction_closed in HU; tea.
  eapply leq_term_prop_sorted_l in c0; tea. all:eauto with pcuic.
  eapply leq_universe_prop_r; tea; eauto with pcuic.
Qed.

Lemma unique_sorting_equality_prop_r {pb} {Σ : global_env_ext} {Γ T U s s'} : 
  wf_ext Σ ->
  Σ ;;; Γ |- T : tSort s ->
  Σ ;;; Γ |- U : tSort s' ->
  Σ ;;; Γ ⊢ T ≤[pb] U ->
  Universe.is_prop s' -> Universe.is_prop s.
Proof.
  intros wfΣ HT HU cum isp.
  eapply PCUICSpine.ws_cumul_pb_le_le in cum.
  eapply ws_cumul_pb_alt_closed in cum as [v [v' [eqv]]].
  eapply subject_reduction_closed in HT; tea.
  eapply subject_reduction_closed in HU; tea.
  eapply leq_term_prop_sorted_r in c0; tea. all:eauto with pcuic.
  eapply leq_universe_prop_r; tea; eauto with pcuic.
Qed.

Lemma unique_sorting_equality_prop {pb} {Σ : global_env_ext} {Γ T U s s'} : 
  wf_ext Σ ->
  Σ ;;; Γ |- T : tSort s ->
  Σ ;;; Γ |- U : tSort s' ->
  Σ ;;; Γ ⊢ T ≤[pb] U ->
  Universe.is_prop s = Universe.is_prop s'.
Proof.
  intros wfΣ HT HU cum.
  apply iff_is_true_eq_bool.
  split.
  now eapply unique_sorting_equality_prop_l; tea.
  now eapply unique_sorting_equality_prop_r; tea.
Qed.

Lemma unique_sorting_equality_sprop_l {pb} {Σ : global_env_ext} {Γ T U s s'} : 
  wf_ext Σ ->
  Σ ;;; Γ |- T : tSort s ->
  Σ ;;; Γ |- U : tSort s' ->
  Σ ;;; Γ ⊢ T ≤[pb] U ->
  Universe.is_sprop s -> Universe.is_sprop s'.
Proof.
  intros wfΣ HT HU cum isp.
  eapply PCUICSpine.ws_cumul_pb_le_le in cum.
  eapply ws_cumul_pb_alt_closed in cum as [v [v' [eqv]]].
  eapply subject_reduction_closed in HT; tea.
  eapply subject_reduction_closed in HU; tea.
  eapply leq_term_sprop_sorted_l in c0; tea. all:eauto with pcuic.
  eapply leq_universe_sprop_r; tea; eauto with pcuic.
Qed.

Lemma unique_sorting_equality_sprop_r {pb} {Σ : global_env_ext} {Γ T U s s'} : 
  wf_ext Σ ->
  Σ ;;; Γ |- T : tSort s ->
  Σ ;;; Γ |- U : tSort s' ->
  Σ ;;; Γ ⊢ T ≤[pb] U ->
  Universe.is_sprop s' -> Universe.is_sprop s.
Proof.
  intros wfΣ HT HU cum isp.
  eapply PCUICSpine.ws_cumul_pb_le_le in cum.
  eapply ws_cumul_pb_alt_closed in cum as [v [v' [eqv]]].
  eapply subject_reduction_closed in HT; tea.
  eapply subject_reduction_closed in HU; tea.
  eapply leq_term_sprop_sorted_r in c0; tea. all:eauto with pcuic.
  eapply leq_universe_sprop_r; tea; eauto with pcuic.
Qed.

Lemma unique_sorting_equality_sprop {pb} {Σ : global_env_ext} {Γ T U s s'} : 
  wf_ext Σ ->
  Σ ;;; Γ |- T : tSort s ->
  Σ ;;; Γ |- U : tSort s' ->
  Σ ;;; Γ ⊢ T ≤[pb] U ->
  Universe.is_sprop s = Universe.is_sprop s'.
Proof.
  intros wfΣ HT HU cum.
  apply iff_is_true_eq_bool.
  split.
  now eapply unique_sorting_equality_sprop_l; tea.
  now eapply unique_sorting_equality_sprop_r; tea.
Qed.

Lemma unique_sorting_equality_propositional {pb} {Σ : global_env_ext} {Γ T U s s'} : 
  wf_ext Σ ->
  Σ ;;; Γ |- T : tSort s ->
  Σ ;;; Γ |- U : tSort s' ->
  Σ ;;; Γ ⊢ T ≤[pb] U ->
  is_propositional s = is_propositional s'.
Proof.
  intros wfΣ HT HU cum.
  unfold is_propositional.
  destruct (Universe.is_prop s) eqn:isp => /=. symmetry.
  - apply orb_true_intro; left.
    now rewrite (unique_sorting_equality_prop wfΣ HT HU cum) in isp.
  - destruct (Universe.is_sprop s) eqn:isp' => /=. symmetry.
    apply orb_true_intro; right.
    now rewrite (unique_sorting_equality_sprop wfΣ HT HU cum) in isp'.
    rewrite (unique_sorting_equality_prop wfΣ HT HU cum) in isp.
    rewrite (unique_sorting_equality_sprop wfΣ HT HU cum) in isp'.
    rewrite isp isp' //.
Qed.

(* Obligation Tactic := idtac. *)

Opaque is_arity type_of_typing.

Definition inspect {A} (x : A) : { y : A | x = y } := exist x eq_refl.

Equations inspect_bool (b : bool) : { b } + { ~~ b } := 
  inspect_bool true := left eq_refl;
  inspect_bool false := right eq_refl.

#[tactic="idtac"]
Equations? is_erasableb (Σ : wf_env_ext) (Γ : context) (T : PCUICAst.term) 
  (wt : forall Σ0 : global_env_ext, abstract_env_rel' Σ Σ0 -> welltyped Σ0 Γ T) : bool :=
  is_erasableb Σ Γ t wt with @type_of_typing extraction_checker_flags _ optimized_abstract_env_ext_impl Σ Γ t wt :=
    { | T with is_arity Σ Γ _ T.π1 _ := 
      { | true => true
        | false => let s := @sort_of_type extraction_checker_flags _ optimized_abstract_env_ext_impl Σ Γ T.π1 _ in
          is_propositional s.π1 } }.
  Proof.
    - intros.
      destruct (wt _ H); sq; eauto.
      cbn in H. subst Σ0. pcuic.
    - intros. destruct T as [T Ht].
      cbn. specialize (Ht Σ0 H) as [[tT Hp]].
      assert (wfΣ' : abstract_env_rel' Σ Σ) by reflexivity.
      pose proof (abstract_env_ext_wf _ wfΣ') as [wf].
      cbn in H; subst Σ0.
      eapply validity in tT. pcuic.
    - intros. destruct T as [T Ht].
      cbn in *. specialize (Ht Σ0 H) as [[tT Hp]].
      assert (wfΣ' : abstract_env_rel' Σ Σ) by reflexivity.
      pose proof (abstract_env_ext_wf _ wfΣ') as [wf].
      cbn in H; subst Σ0.
      eapply validity in tT. now sq.
  Qed.
Transparent is_arity type_of_typing.

Lemma is_erasableP {Σ : wf_env_ext} {Γ : context} {t : PCUICAst.term}
  {wt : forall Σ0 : global_env_ext, abstract_env_rel' Σ Σ0 -> welltyped Σ0 Γ t} : 
  reflect (∥ isErasable Σ Γ t ∥) (is_erasableb Σ Γ t wt).
Proof.
  funelim (is_erasableb Σ Γ t wt).
  - constructor. destruct type_of_typing as [x Hx]. cbn -[is_arity sort_of_type] in *.  
    assert (wfΣ' : abstract_env_rel' Σ Σ) by reflexivity.
    pose proof (abstract_env_ext_wf _ wfΣ') as [wf].
    specialize_Σ wfΣ'. destruct (Hx _ eq_refl) as [[HT ?]]. 
    move/is_arityP: Heq => [T' [redT' isar]].
    destruct (wt _ eq_refl) as [T ht].
    sq. red. exists T'. eapply type_reduction_closed in HT; eauto.
  - destruct type_of_typing as [x Hx]. cbn -[sort_of_type is_arity] in *.  
    assert (wfΣ' : abstract_env_rel' Σ Σ) by reflexivity.
    destruct (sort_of_type _ _ _ _). cbn.
    specialize_Σ wfΣ'.
    destruct (is_propositional x0) eqn:isp; constructor.
    * clear Heq. pose proof (abstract_env_ext_wf _ wfΣ') as [wf]. 
      specialize_Σ wfΣ'. 
      destruct Hx as [[HT ?]].
      destruct s as [Hs]. sq.
      exists x; split => //. right.
      exists x0. now split.
    * intros [[T' [HT' er]]].
      pose proof (abstract_env_ext_wf _ wfΣ') as [wf].
      move/is_arityP: Heq => nisa. 
      specialize_Σ wfΣ'. 
      destruct Hx as [[HT ?]].
      specialize (p _ HT').
      destruct er as [isa|[u' [Hu' isp']]].
      { apply nisa. eapply invert_cumul_arity_r; tea. }
      { destruct s as [Hs]. have := (unique_sorting_equality_propositional wf Hs Hu' p). congruence. }
Qed.
    
Equations? is_erasable (Σ : wf_env_ext) (Γ : context) (t : PCUICAst.term) 
  (wt : forall Σ0 : global_env_ext, abstract_env_rel' Σ Σ0 -> welltyped Σ0 Γ t) : 
  { ∥ isErasable Σ Γ t ∥ } + { ∥ isErasable Σ Γ t -> False ∥ } :=
  is_erasable Σ Γ T wt with inspect_bool (is_erasableb Σ Γ T wt) :=
    { | left ise => left _
      | right nise => right _ }.
Proof.
  assert (wfΣ' : abstract_env_rel' Σ Σ) by reflexivity.
  pose proof (abstract_env_ext_wf _ wfΣ') as [wf].
  move/is_erasableP: ise => //.
  move/(elimN is_erasableP): nise.
  intros; sq => ise. apply nise. now sq.
Qed.

Lemma welltyped_brs (Σ : global_env_ext) (HΣ :∥ wf_ext Σ ∥)  Γ ci p t2 brs T : Σ ;;; Γ |- tCase ci p t2 brs : T -> 
  ∥ All (fun br => welltyped Σ (Γ ,,, inst_case_branch_context p br) (bbody br)) brs ∥.
Proof.
  intros Ht. destruct HΣ. constructor.
  eapply inversion_Case in Ht as (mdecl & idecl & decli & indices & data & hty); auto.
  destruct data.
  eapply validity in scrut_ty.
  eapply forall_nth_error_All => i br hnth.
  eapply All2i_nth_error_r in brs_ty; tea.
  destruct brs_ty as [cdecl [hnthc [eqctx [wfbctxty [tyb _]]]]].
  have declc: declared_constructor Σ (ci, i) mdecl idecl cdecl.
  { split; auto. }
  have wfbr : wf_branch cdecl br.
  { eapply Forall2_All2 in wf_brs. eapply All2_nth_error in wf_brs; tea. }
  have wfΓ : wf_local Σ Γ.
  { eapply typing_wf_local in pret_ty. now eapply All_local_env_app_inv in pret_ty as []. }
  epose proof (wf_case_inst_case_context ps indices decli scrut_ty wf_pred pret_ty conv_pctx
    _ _ _ declc wfbr eqctx) as [wfictx eqictx].
  eexists.
  eapply closed_context_conversion; tea.
  now symmetry.
Qed.

Section Erase.
  Variable (Σ : wf_env_ext).

  Ltac sq' := 
             repeat match goal with
                    | H : ∥ _ ∥ |- _ => destruct H; try clear H
                    end; try eapply sq.

  (* Bug in equationa: it produces huge goals leading to stack overflow if we
    don't try reflexivity here. *)
  Ltac Equations.Prop.DepElim.solve_equation c ::= 
    intros; try reflexivity; try Equations.Prop.DepElim.simplify_equation c;
     try
	  match goal with
    | |- ImpossibleCall _ => DepElim.find_empty
    | _ => try red; try reflexivity || discriminates
    end.

  Equations erase_prim (ep : prim_val term) : PCUICPrimitive.prim_val E.term :=
  erase_prim (_; primIntModel i) := (_; primIntModel i);
  erase_prim (_; primFloatModel f) := (_; primFloatModel f).
  
  Opaque is_erasableb.
  
  #[tactic="idtac"]
  Equations? erase (Γ : context) (t : term) 
    (Ht : forall Σ0 : global_env_ext, abstract_env_rel' Σ Σ0 -> welltyped Σ0 Γ t) : E.term
      by struct t :=
  { erase Γ t Ht with inspect_bool (is_erasableb Σ Γ t Ht) :=
  { | left he := E.tBox; 
    | right he with t := {
      | tRel i := E.tRel i
      | tVar n := E.tVar n
      | tEvar m l := E.tEvar m (erase_terms Γ l _)
      | tSort u := !%prg
      | tConst kn u := E.tConst kn
      | tInd kn u := !%prg
      | tConstruct kn k u := E.tConstruct kn k
      | tProd _ _ _ := !%prg
      | tLambda na b b' := let t' := erase (vass na b :: Γ) b' _ in
        E.tLambda na.(binder_name) t'
      | tLetIn na b t0 t1 :=
        let b' := erase Γ b _ in
        let t1' := erase (vdef na b t0 :: Γ) t1 _ in
        E.tLetIn na.(binder_name) b' t1'
      | tApp f u :=
        let f' := erase Γ f _ in
        let l' := erase Γ u _ in
        E.tApp f' l'
      | tCase ci p c brs :=
        let c' := erase Γ c _ in
        let brs' := erase_brs Γ p brs _ in
        E.tCase (ci.(ci_ind), ci.(ci_npar)) c' brs' 
      | tProj p c :=
        let c' := erase Γ c _ in
        E.tProj p c'
      | tFix mfix n :=
        let Γ' := (fix_context mfix ++ Γ)%list in
        let mfix' := erase_fix Γ' mfix _ in
        E.tFix mfix' n
      | tCoFix mfix n :=
        let Γ' := (fix_context mfix ++ Γ)%list in
        let mfix' := erase_cofix Γ' mfix _ in
        E.tCoFix mfix' n }
      (* erase Γ (tPrim p) Ht _ := E.tPrim (erase_prim p) *)
    } } 
  where erase_terms (Γ : context) (l : list term) (Hl : forall Σ0 : global_env_ext, abstract_env_rel' Σ Σ0 -> ∥ All (welltyped Σ0 Γ) l ∥) : list E.term :=
  { erase_terms Γ [] _ := [];
    erase_terms Γ (t :: ts) _ := 
      let t' := erase Γ t _ in
      let ts' := erase_terms Γ ts _ in
      t' :: ts' }
(** We assume that there are no lets in contexts, so nothing has to be expanded.
  In particular, note that #|br.(bcontext)| = context_assumptions br.(bcontext) when no lets are present.
  *)
  where erase_brs (Γ : context) p (brs : list (branch term)) 
    (Ht : forall Σ0 : global_env_ext, abstract_env_rel' Σ Σ0 ->
          ∥ All (fun br => welltyped Σ0 (Γ ,,, inst_case_branch_context p br) (bbody br)) brs ∥) :
    list (list name × E.term) := 
  { erase_brs Γ p [] Ht := [];
    erase_brs Γ p (br :: brs) Hbrs := 
      let br' := erase (Γ ,,, inst_case_branch_context p br) (bbody br) _ in
      let brs' := erase_brs Γ p brs _ in
      (erase_context br.(bcontext), br') :: brs' }
  
  where erase_fix (Γ : context) (mfix : mfixpoint term)
    (Ht : forall Σ0 : global_env_ext, abstract_env_rel' Σ Σ0 ->
          ∥ All (fun d => isLambda d.(dbody) /\ welltyped Σ0 Γ d.(dbody)) mfix ∥) : E.mfixpoint E.term :=
  { erase_fix Γ [] _ := [];
    erase_fix Γ (d :: mfix) Hmfix := 
      let dbody' := erase Γ d.(dbody) _ in
      let dbody' := if isBox dbody' then
        match d.(dbody) with
        (* We ensure that all fixpoint members start with a lambda, even a dummy one if the 
           recursive definition is erased. *)
        | tLambda na _ _ => E.tLambda (binder_name na) E.tBox
        | _ => dbody'
        end else dbody' in
      let d' := {| E.dname := d.(dname).(binder_name); E.rarg := d.(rarg); E.dbody := dbody' |} in
      d' :: erase_fix Γ mfix _ }

  where erase_cofix (Γ : context) (mfix : mfixpoint term)
      (Ht : forall Σ0 : global_env_ext, abstract_env_rel' Σ Σ0 ->
            ∥ All (fun d => welltyped Σ0 Γ d.(dbody)) mfix ∥) : E.mfixpoint E.term :=
    { erase_cofix Γ [] _ := [];
      erase_cofix Γ (d :: mfix) Hmfix := 
        let dbody' := erase Γ d.(dbody) _ in
        let d' := {| E.dname := d.(dname).(binder_name); E.rarg := d.(rarg); E.dbody := dbody' |} in
        d' :: erase_cofix Γ mfix _ }
    .
  Proof. 
    all: try clear b'; try clear f';
      try clear t';
      try clear brs'; try clear c'; try clear br'; 
      try clear d' dbody'; try clear erase; try clear erase_terms; try clear erase_brs; try clear erase_mfix.
    all: cbn; intros; subst; lazymatch goal with [ |- False ] => idtac | _ => try clear he end.
    all: assert (wfΣ' : abstract_env_rel' Σ Σ) by reflexivity;
         pose proof (abstract_env_ext_wf _ wfΣ') as [wf];
         specialize_Σ wfΣ'.
    all: try destruct Ht as [ty Ht]; try destruct s0; simpl in *.
    - now eapply inversion_Evar in Ht.
    - discriminate.
    - discriminate.
    - eapply inversion_Lambda in Ht as (? & ? & ? & ? & ?); auto.
      eexists; eauto.
    - eapply inversion_LetIn in Ht as (? & ? & ? & ? & ? & ?); auto.
      eexists; eauto.
    - simpl in *.
      eapply inversion_LetIn in Ht as (? & ? & ? & ? & ? & ?); auto.
      eexists; eauto.
    - eapply inversion_App in Ht as (? & ? & ? & ? & ? & ?); auto.
      eexists; eauto.
    - eapply inversion_App in Ht as (? & ? & ? & ? & ? & ?); auto.
      eexists; eauto.
    - move/is_erasableP: he.
      specialize_Σ wfΣ'. destruct Ht as [ty Ht]. intros ne. sq. apply ne. sq.
      eapply inversion_Ind in Ht as (? & ? & ? & ? & ? & ?) ; auto.
      red. eexists. split. econstructor; eauto. left.
      eapply isArity_subst_instance.
      eapply isArity_ind_type; eauto.
    - eapply inversion_Case in Ht as (? & ? & ? & ? & [] & ?); auto.
      eexists; eauto.
    - now eapply welltyped_brs in Ht as []; tea.
    - eapply inversion_Proj in Ht as (? & ? & ? & ? & ? & ? & ? & ? & ?); auto.
      eexists; eauto.
    - eapply inversion_Fix in Ht as (? & ? & ? & ? & ? & ?); auto.
      sq. destruct p. move/andP: i => [wffix _].
      solve_all. now eexists.
    - eapply inversion_CoFix in Ht as (? & ? & ? & ? & ? & ?); auto.
      sq. eapply All_impl; tea. cbn. intros d Ht; now eexists.
    - sq. now depelim X.
    - sq. now depelim X.
    - sq. now depelim X.
    - sq. now depelim X.
    - sq. now depelim X.
    - clear dbody'0. specialize (Hmfix _ wfΣ'). sq. now depelim X.
    - sq. now depelim X.
    - sq. now depelim X.
  Qed.
  
End Erase.

Lemma is_erasableb_irrel {Σ Γ t} wt wt' : is_erasableb Σ Γ t wt = is_erasableb Σ Γ t wt'.
Proof.
  destruct (@is_erasableP Σ Γ t wt);
  destruct (@is_erasableP Σ Γ t wt') => //.
Qed.

Ltac iserasableb_irrel :=
  match goal with
  [ H : context [is_erasableb ?Σ ?Γ ?t ?wt], Heq : inspect_bool _ = _ |- context [ is_erasableb _ _ _ ?wt'] ] => 
    generalize dependent H; rewrite (is_erasableb_irrel wt wt'); intros; rewrite Heq
  end.

Ltac simp_erase := simp erase; rewrite -?erase_equation_1.

Lemma erase_irrel (Σ : wf_env_ext) : 
  (forall Γ t wt, forall wt', erase Σ Γ t wt = erase Σ Γ t wt') ×
  (forall Γ l wt, forall wt', erase_terms Σ Γ l wt = erase_terms Σ Γ l wt') ×
  (forall Γ p l wt, forall wt', erase_brs Σ Γ p l wt = erase_brs Σ Γ p l wt') ×
  (forall Γ l wt, forall wt', erase_fix Σ Γ l wt = erase_fix Σ Γ l wt') ×
  (forall Γ l wt, forall wt', erase_cofix Σ Γ l wt = erase_cofix Σ Γ l wt').
Proof.
  apply: (erase_elim Σ
    (fun Γ t wt e => 
      forall wt' : forall Σ0 : global_env_ext, abstract_env_rel' Σ Σ0 ->  welltyped Σ0 Γ t, e = erase Σ Γ t wt')
    (fun Γ l awt e => forall wt', e = erase_terms Σ Γ l wt')
    (fun Γ p l awt e => forall wt', e = erase_brs Σ Γ p l wt')
    (fun Γ l awt e => forall wt', e = erase_fix Σ Γ l wt')
    (fun Γ l awt e => forall wt', e = erase_cofix Σ Γ l wt')); clear.
  all:intros *; intros; simp_erase.
  all:try simp erase; try iserasableb_irrel; simp_erase => //.
  all:try clear he Heq.
  all:try bang.
  all:try solve [cbn; f_equal; eauto].
  all:try solve [cbn; repeat (f_equal; eauto)].
  cbn. f_equal. f_equal. now rewrite (H (erase_obligation_19 Σ Γ d mfix wt')).
  now rewrite (H0 (erase_obligation_20 Σ Γ d mfix wt')).
Qed.

Section map_All.
  Unset Default Proof Using.
  Context {A B C} {Q : C -> Type} {P : C -> A  -> Prop} 
    (fn : forall (x : A) , (forall (y:C),  Q y -> P y x) -> B).
  
  Equations? map_All (l : list A) (Hl : forall y, Q y -> ∥ All (P y) l ∥) : list B :=
  | [], _ := []
  | x :: xs, h := fn x _ :: map_All xs _.
  Proof. all:clear fn map_All.
    - specialize (h y X). sq. now depelim X0.
    - specialize (h y X). sq. now depelim X0.
  Qed.
End map_All.

Lemma All_map_All {A B C} {Q : C -> Type} {P : C -> A -> Prop}
  {Q' : B -> Type} {R : C -> A -> Prop} 
  f args (ha: forall y : C, Q y -> ∥ All (R y) args ∥) :
  (forall y : C, Q y -> All (P y) args) ->
  (forall x y rx, P y x -> Q' (f x rx)) ->
  forall y, Q y -> All Q' (map_All f args ha).
Proof.
  funelim (map_All f args ha).
  - constructor.
  - intros ha hf y hy. pose proof (ha y hy). depelim X0. econstructor; eauto.
    eapply X; eauto. intros. eapply ha in X1. now invs X1.
Qed.
 
Lemma map_All_length {A B C : Type} {Q : C -> Type} {P : C -> A -> Prop}
  (fn : forall x : A, (forall y : C, Q y -> P y x) -> B) 
  (l : list A) (Hl : forall y : C, Q y -> ∥ All (P y) l ∥) :
  #|map_All fn l Hl| = #|l|.
Proof.
  funelim (map_All fn l Hl); cbn; congruence.
Qed.
Local Hint Rewrite @map_All_length : len.

Lemma nth_error_map_All {A B C} {Q : C -> Type} {P : C -> A  -> Prop} 
  (fn : forall (x : A) , (forall (y:C),  Q y -> P y x) -> B) :
  forall l : list A, forall H : (forall y : C, Q y -> ∥ All (P y) l ∥),
  forall n x,
    nth_error l n = Some x ->
    exists D, nth_error (map_All fn l H) n = Some (fn x D).
Proof.
  intros.
  funelim (map_All fn l H).
  - destruct n; invs H0.
  - destruct n; invs H1.
    + eexists. reflexivity.
    + now eapply H.
Qed.

Lemma erase_terms_eq Σ Γ ts wt : 
  erase_terms Σ Γ ts wt = map_All (erase Σ Γ) ts wt.
Proof.
  funelim (map_All (erase Σ Γ) ts wt); cbn; auto.
  f_equal => //. apply erase_irrel.
  rewrite -H. eapply erase_irrel.
Qed.

Opaque wf_reduction.

#[global]
Hint Constructors typing erases : core.

Lemma isType_isErasable Σ Γ T : isType Σ Γ T -> isErasable Σ Γ T.
Proof.
  intros [s Hs].
  exists (tSort s). intuition auto. left; simpl; auto.
Qed.

Lemma erase_to_box {Σ : wf_env_ext} {Γ t} (wt : forall Σ0 : global_env_ext, abstract_env_rel' Σ Σ0 -> welltyped Σ0 Γ t) :
  let et := erase Σ Γ t wt in 
  if is_box et then ∥ isErasable Σ Γ t ∥
  else ~ ∥ isErasable Σ Γ t ∥.
Proof.
  cbn.
  revert Γ t wt.
  apply (erase_elim Σ
    (fun Γ t wt e => 
      if is_box e then ∥ isErasable Σ Γ t ∥ else ∥ isErasable Σ Γ t ∥ -> False)
    (fun Γ l awt e => True)
    (fun Γ p l awt e => True)
    (fun Γ l awt e => True)
    (fun Γ l awt e => True)); intros.

  all:try discriminate; auto.
  all:cbn -[isErasable].
  all:try solve [match goal with 
    [ H : context [ is_erasableb ?Σ ?Γ ?t ?Ht ] |- _ ] => 
      destruct (@is_erasableP Σ Γ t Ht) => //
  end].
  all:try bang.
  - cbn. rewrite is_box_tApp.
    destruct (@is_erasableP Σ Γ (tApp f u) Ht) => //.
    destruct is_box.
    * cbn in *. clear H0. 
      assert (wfΣ' : abstract_env_rel' Σ Σ) by reflexivity;
      pose proof (abstract_env_ext_wf _ wfΣ') as [wf]. 
      specialize_Σ wfΣ'. destruct Ht, H.
      eapply (EArities.Is_type_app _ _ _ [_]); eauto.
      eauto using typing_wf_local.
    * assumption.
Defined.

Lemma erases_erase {Σ : wf_env_ext} {Γ t} 
(wt : forall Σ0 : global_env_ext, abstract_env_rel' Σ Σ0 -> welltyped Σ0 Γ t) :
  erases Σ Γ t (erase Σ Γ t wt).
Proof.
  revert Γ t wt.
  apply (erase_elim Σ
    (fun Γ t wt e => Σ;;; Γ |- t ⇝ℇ e)
    (fun Γ l awt e => All2 (erases Σ Γ) l e)
    (fun Γ p l awt e => 
      All2 (fun (x : branch term) (x' : list name × E.term) =>
                       (Σ;;; Γ,,, inst_case_branch_context p x |- 
                        bbody x ⇝ℇ x'.2) *
                       (erase_context (bcontext x) = x'.1)) l e)
    (fun Γ l awt e => All2
    (fun (d : def term) (d' : E.def E.term) =>
     [× binder_name (dname d) = E.dname d',
        rarg d = E.rarg d',
        isLambda (dbody d), E.isLambda (E.dbody d') &
        Σ;;; Γ |- dbody d ⇝ℇ E.dbody d']) l e)
    (fun Γ l awt e => All2
      (fun (d : def term) (d' : E.def E.term) =>
        (binder_name (dname d) = E.dname d') *
        (rarg d = E.rarg d'
         × Σ;;; Γ |- dbody d ⇝ℇ E.dbody d')) l e)) ; intros.
    all:try discriminate.
    all:try bang.
    all:try match goal with 
      [ H : context [is_erasableb ?Σ ?Γ ?t ?Ht ] |- _ ] => 
        destruct (@is_erasableP Σ Γ t Ht) as [[H']|H'] => //;
        try now eapply erases_box
    end.
    all: try solve [constructor; eauto].
  all:try destruct Σ.(wf_env_ext_wf) as [wfΣ].
  all: cbn in *; assert (wfΣ' : abstract_env_rel' Σ Σ) by reflexivity;
  try constructor; auto;
  try pose proof (abstract_env_ext_wf _ wfΣ') as [wf];
  specialize_Σ wfΣ'.
  
  - clear Heq.
    eapply nisErasable_Propositional in Ht; auto.

  - cbn.
    destruct (Ht _ wfΣ').
    destruct (inversion_Case _ _ X0) as [mdecl [idecl []]]; eauto.
    eapply elim_restriction_works; eauto.
    intros isp. eapply isErasable_Proof in isp. eauto.

  - clear Heq.
    destruct (Ht _ wfΣ') as [? Ht'].
    clear H. eapply inversion_Proj in Ht' as (?&?&?&?&?&?&?&?&?&?); auto.
    eapply elim_restriction_works_proj; eauto. exact d.
    intros isp. eapply isErasable_Proof in isp; eauto.

  - cbn.
    pose proof Hmfix as Hmfix'.
    specialize (Hmfix' Σ eq_refl). destruct Hmfix'.
    depelim X0. destruct a.
    assert (exists na ty bod, dbody d = tLambda na ty bod).
    { clear -H0. destruct (dbody d) => //. now do 3 eexists. }
    destruct H2 as [na [ty [bod eq]]]. rewrite {1 3}eq /= //.
    move: H. rewrite {1}eq.
    set (et := erase _ _ _ _). clearbody et.
    intros He. depelim He. cbn.
    split => //. cbn. rewrite eq. now constructor.
    split => //. cbn. rewrite eq.
    destruct H1.
    eapply Is_type_lambda in X1; tea. 2:pcuic. destruct X1.
    now constructor.
Qed.

Transparent wf_reduction.

(** We perform erasure up-to the minimal global environment dependencies of the term: i.e.  
  we don't need to erase entries of the global environment that will not be used by the erased
  term.
*)


Program Definition erase_constant_body (Σ : wf_env_ext) (cb : constant_body)
  (Hcb : ∥ on_constant_decl (lift_typing typing) Σ cb ∥) : E.constant_body * KernameSet.t :=  
  let '(body, deps) := match cb.(cst_body) with
          | Some b => 
            let b' := erase Σ [] b _ in
            (Some b', term_global_deps b')
          | None => (None, KernameSet.empty)
          end in
  ({| E.cst_body := body; |}, deps).
Next Obligation.
Proof.
  sq. red in X. rewrite <-Heq_anonymous in X. simpl in X, H. cbn in H. subst Σ0.
  eexists; eauto.
Qed.

Definition erase_one_inductive_body (oib : one_inductive_body) : E.one_inductive_body :=
  (* Projection and constructor types are types, hence always erased *)
  let ctors := map (fun cdecl => EAst.mkConstructor cdecl.(cstr_name) cdecl.(cstr_arity)) oib.(ind_ctors) in
  let projs := map (fun pdecl => EAst.mkProjection pdecl.(proj_name)) oib.(ind_projs) in
  let is_propositional := 
    match destArity [] oib.(ind_type) with
    | Some (_, u) => is_propositional u
    | None => false (* dummy, impossible case *)
    end
  in
  {| E.ind_name := oib.(ind_name);
     E.ind_kelim := oib.(ind_kelim);
     E.ind_propositional := is_propositional;
     E.ind_ctors := ctors;
     E.ind_projs := projs |}.

Definition erase_mutual_inductive_body (mib : mutual_inductive_body) : E.mutual_inductive_body :=
  let bds := mib.(ind_bodies) in
  let arities := arities_context bds in
  let bodies := map erase_one_inductive_body bds in
  {| E.ind_npars := mib.(ind_npars);
     E.ind_bodies := bodies; |}.

(* Move to WfEnvImpl *)
Lemma wf_env_fresh (Σ : wf_env) : EnvMap.EnvMap.fresh_globals Σ.(declarations).
Proof.
  destruct Σ.(referenced_impl_wf).
  now eapply wf_fresh_globals. 
Qed.

Lemma wf_env_eta (Σ : wf_env) : {| universes := Σ.(universes); declarations := Σ.(declarations) |} = Σ.
Proof.
  destruct Σ => /= //. destruct referenced_impl_env => //.
Qed.
     
Program Definition remove_kn (kn : kername) (Σ : wf_env) decls (prf : exists d, Σ.(referenced_impl_env).(declarations) = (kn, d) :: decls) : wf_env :=
 {| wf_env_referenced := {| referenced_impl_env := {| universes := Σ.(referenced_impl_env).(universes); declarations := decls |} |};
    wf_env_map := EnvMap.EnvMap.remove kn Σ.(wf_env_map); 
    |}.

Import EnvMap.
Next Obligation.
  destruct Σ.(referenced_impl_wf). sq.
  destruct X as [onu ond]; split => //. rewrite H in ond.
  now depelim ond.
Qed.
Next Obligation.
  pose proof Σ.(wf_env_map_repr). red in H0.
  rewrite H in H0.
  set (Σ0 := EnvMap.of_global_env decls).
  epose proof (EnvMap.remove_add_eq decls kn prf Σ0).
  forward_keep H1.
  { pose proof (Σf := wf_env_fresh Σ). rewrite H in Σf. now depelim Σf. }
  forward_keep H1.
  { pose proof (Σf := wf_env_fresh Σ). rewrite H in Σf. now depelim Σf. }
  forward_keep H1.
  { red. unfold EnvMap.equal. reflexivity. }
  unfold EnvMap.repr.
  rewrite H0 /=. unfold KernameMapFact.uncurry; cbn.
  unfold EnvMap.add in H1. rewrite H1. reflexivity.
Qed.
  
Program Definition make_wf_env_ext (Σ : wf_env) (univs : universes_decl) (prf : ∥ wf_ext (Σ, univs) ∥) : wf_env_ext :=
  {| wf_env_ext_referenced := {| referenced_impl_env_ext := (Σ, univs);|} ;
     wf_env_ext_map := Σ.(wf_env_map);
     wf_env_ext_map_repr := Σ.(wf_env_map_repr) |}.

Require Import Morphisms.
From MetaCoq.Template Require Import uGraph.
Global Instance proper_pair_levels_gcs : Proper ((=_lset) ==> GoodConstraintSet.Equal ==> (=_gcs)) (@pair LevelSet.t GoodConstraintSet.t).
Proof.
  intros l l' eq gcs gcs' eq'.
  split; cbn; auto.
Qed.

Program Fixpoint erase_global_decls (deps : KernameSet.t) (Σ : wf_env) (decls : global_declarations) 
  (prop : Σ.(referenced_impl_env).(declarations) = decls) : E.global_declarations :=
  match decls with
  | [] => []
  | (kn, ConstantDecl cb) :: decls =>
    let wfΣ' := remove_kn kn Σ decls _ in
    if KernameSet.mem kn deps then
      let wfΣext' := make_wf_env_ext wfΣ' (cst_universes cb) _ in
      let cb' := erase_constant_body wfΣext' cb _ in
      let deps := KernameSet.union deps (snd cb') in
      let Σ' := erase_global_decls deps wfΣ' decls _ in
      ((kn, E.ConstantDecl (fst cb')) :: Σ')
    else
      erase_global_decls deps wfΣ' decls _

  | (kn, InductiveDecl mib) :: decls =>
    let wfΣ' := remove_kn kn Σ decls _ in
    if KernameSet.mem kn deps then
      let mib' := erase_mutual_inductive_body mib in
      let Σ' := erase_global_decls deps wfΣ' decls _ in
      ((kn, E.InductiveDecl mib') :: Σ')
    else erase_global_decls deps wfΣ' decls _
  end.
Next Obligation.
  now eexists.
Qed.
Next Obligation.
  epose proof Σ.(referenced_impl_wf).
  sq. destruct X. rewrite -Heq_decls in o0. depelim o0. split => //.
Qed.
Next Obligation.
  epose proof Σ.(referenced_impl_wf).
  sq. destruct X. rewrite -Heq_decls in o0. depelim o0. apply o2.
Qed.
Next Obligation.
  now eexists.
Qed.

Definition erase_global deps Σ :=
  erase_global_decls deps Σ Σ.(declarations) eq_refl.

Definition global_erased_with_deps (Σ : global_env) (Σ' : EAst.global_declarations) kn :=
  (exists cst, declared_constant Σ kn cst /\
   exists cst' : EAst.constant_body,
    EGlobalEnv.declared_constant Σ' kn cst' /\
    erases_constant_body (Σ, cst_universes cst) cst cst' /\
    (forall body : EAst.term,
     EAst.cst_body cst' = Some body -> erases_deps Σ Σ' body)) \/
  (exists mib mib', declared_minductive Σ kn mib /\ 
    EGlobalEnv.declared_minductive Σ' kn mib' /\
    erases_mutual_inductive_body mib mib').

Definition includes_deps (Σ : global_env) (Σ' : EAst.global_declarations) deps :=  
  forall kn, 
    KernameSet.In kn deps ->
    global_erased_with_deps Σ Σ' kn.

Lemma includes_deps_union (Σ : global_env) (Σ' : EAst.global_declarations) deps deps' :
  includes_deps Σ Σ' (KernameSet.union deps deps') ->
  includes_deps Σ Σ' deps /\ includes_deps Σ Σ' deps'.
Proof.
  intros.
  split; intros kn knin; eapply H; rewrite KernameSet.union_spec; eauto.
Qed.

Lemma includes_deps_fold {A} (Σ : global_env) (Σ' : EAst.global_declarations) brs deps (f : A -> EAst.term) :
  includes_deps Σ Σ'
  (fold_left
    (fun (acc : KernameSet.t) (x : A) =>
      KernameSet.union (term_global_deps (f x)) acc) brs
      deps) ->
  includes_deps Σ Σ' deps /\
  (forall x, In x brs ->
    includes_deps Σ Σ' (term_global_deps (f x))).
Proof.
  intros incl; split.
  intros kn knin; apply incl.
  rewrite knset_in_fold_left. left; auto.
  intros br brin. intros kn knin. apply incl.
  rewrite knset_in_fold_left. right.
  now exists br.
Qed.

Definition declared_kn Σ kn :=
  ∥ ∑ decl, lookup_env Σ kn = Some decl ∥.

Lemma term_global_deps_spec {cf} {Σ : global_env_ext} {Γ t et T} : 
  wf Σ.1 ->
  Σ ;;; Γ |- t : T ->
  Σ;;; Γ |- t ⇝ℇ et ->
  forall x, KernameSet.In x (term_global_deps et) -> declared_kn Σ x.
Proof.
  intros wf wt er.
  induction er in T, wt |- * using erases_forall_list_ind;
    cbn in *; try solve [constructor]; intros kn' hin;
    repeat match goal with 
    | [ H : KernameSet.In _ KernameSet.empty |- _ ] =>
      now apply KernameSet.empty_spec in hin
    | [ H : KernameSet.In _ (KernameSet.union _ _) |- _ ] =>
      apply KernameSet.union_spec in hin as [?|?]
    end.
  - apply inversion_Lambda in wt as (? & ? & ? & ? & ?); eauto.
  - apply inversion_LetIn in wt as (? & ? & ? & ? & ? & ?); eauto.
  - apply inversion_LetIn in wt as (? & ? & ? & ? & ? & ?); eauto.
  - apply inversion_App in wt as (? & ? & ? & ? & ? & ?); eauto.
  - apply inversion_App in wt as (? & ? & ? & ? & ? & ?); eauto.
  - apply inversion_Const in wt as (? & ? & ? & ? & ?); eauto.
    eapply KernameSet.singleton_spec in hin; subst.
    red in d. red. sq. rewrite d. intuition eauto.
  - apply inversion_Construct in wt as (? & ? & ? & ? & ? & ? & ?); eauto.
    destruct kn.
    eapply KernameSet.singleton_spec in hin; subst.
    destruct d as [[H' _] _]. red in H'. simpl in *.
    red. sq. rewrite H'. intuition eauto.
  - apply inversion_Case in wt as (? & ? & ? & ? & [] & ?); eauto.
    destruct ci as [kn i']; simpl in *.
    eapply KernameSet.singleton_spec in H1; subst.
    destruct x1 as [d _]. red in d.
    simpl in *. eexists; intuition eauto.

  - apply inversion_Case in wt as (? & ? & ? & ? & [] & ?); eauto.
    eapply knset_in_fold_left in H1.
    destruct H1. eapply IHer; eauto.
    destruct H1 as [br [inbr inkn]].
    eapply Forall2_All2 in H0.
    assert (All (fun br => ∑ T, Σ ;;; Γ ,,, inst_case_branch_context p br |- br.(bbody) : T) brs).
    eapply All2i_All_right. eapply brs_ty.
    simpl. intuition auto. eexists ; eauto.
    now rewrite -(PCUICCasesContexts.inst_case_branch_context_eq a).
    eapply All2_All_mix_left in H0; eauto. simpl in H0.
    eapply All2_In_right in H0; eauto.
    destruct H0.
    destruct X1 as [br' [[T' HT] ?]].
    eauto.
  
  - eapply KernameSet.singleton_spec in H0; subst.
    apply inversion_Proj in wt as (?&?&?&?&?&?&?&?&?&?); eauto.
    destruct d as [[[d _] _] _]. red in d. eexists; eauto.

  - apply inversion_Proj in wt as (?&?&?&?&?&?&?&?&?); eauto.

  - apply inversion_Fix in wt as (?&?&?&?&?&?&?); eauto.
    eapply knset_in_fold_left in hin as [|].
    now eapply KernameSet.empty_spec in H0.
    destruct H0 as [? [ina indeps]].
    eapply Forall2_All2 in H.
    eapply All2_All_mix_left in H; eauto.
    eapply All2_In_right in H; eauto.
    destruct H as [[def [Hty Hdef]]].
    eapply Hdef; eauto.

  - apply inversion_CoFix in wt as (?&?&?&?&?&?&?); eauto.
    eapply knset_in_fold_left in hin as [|].
    now eapply KernameSet.empty_spec in H0.
    destruct H0 as [? [ina indeps]].
    eapply Forall2_All2 in H.
    eapply All2_All_mix_left in H; eauto.
    eapply All2_In_right in H; eauto.
    destruct H as [[def [Hty Hdef]]].
    eapply Hdef; eauto.
Qed.

Global Remove Hints erases_deps_eval : core.

Lemma erase_global_erases_deps {Σ} {Σ' : EAst.global_declarations} {Γ t et T} : 
  wf_ext Σ ->
  Σ;;; Γ |- t : T ->
  Σ;;; Γ |- t ⇝ℇ et ->
  includes_deps Σ Σ' (term_global_deps et) ->
  erases_deps Σ Σ' et.
Proof.
  intros wf wt er.
  induction er in er, t, T, wf, wt |- * using erases_forall_list_ind;
    cbn in *; try solve [constructor]; intros Σer;
    repeat match goal with 
    | [ H : includes_deps _ _ (KernameSet.union _ _ ) |- _ ] =>
      apply includes_deps_union in H as [? ?]
    end.
  - now apply inversion_Evar in wt.
  - constructor.
    now apply inversion_Lambda in wt as (? & ? & ? & ? & ?); eauto.
  - apply inversion_LetIn in wt as (? & ? & ? & ? & ? & ?); eauto.
    constructor; eauto.
  - apply inversion_App in wt as (? & ? & ? & ? & ? & ?); eauto.
    now constructor; eauto.
  - apply inversion_Const in wt as (? & ? & ? & ? & ?); eauto.
    specialize (Σer kn).
    forward Σer. rewrite KernameSet.singleton_spec //.
    destruct Σer as [[c' [declc' (? & ? & ? & ?)]]|].
    pose proof (declared_constant_inj _ _ d declc'). subst x.
    now econstructor; eauto.
    destruct H as [mib [mib' [declm declm']]].
    red in declm, d. rewrite d in declm. noconf declm.
  - apply inversion_Construct in wt as (? & ? & ? & ? & ? & ?); eauto.
    red in Σer. destruct kn.
    setoid_rewrite KernameSetFact.singleton_iff in Σer.
    destruct (Σer _ eq_refl) as [ (? & ? & ? & ? & ? & ?) | (? & ? & ? & ? & ?) ].
    + red in H0. destruct d as [[]]. red in H4. cbn in *. unfold PCUICEnvironment.fst_ctx in *. congruence.
    + pose proof H2 as H2'. destruct d. cbn in *. destruct H3. cbn in *. red in H3. red in H0. rewrite H0 in H3. invs H3.
      destruct H2.
      red in H1.
      eapply Forall2_nth_error_Some_l in H2 as (? & ? & ?); eauto. pose proof H6 as H6'. destruct H6 as (? & ? & ? & ? & ?); eauto.
      eapply Forall2_nth_error_Some_l in H6 as ([] & ? & ? & ?); subst; eauto.
      econstructor. repeat eapply conj; eauto.
      repeat eapply conj; cbn; eauto. eauto. eauto.
  - apply inversion_Case in wt as (? & ? & ? & ? & [] & ?); eauto.
    destruct ci as [[kn i'] ? ?]; simpl in *.
    apply includes_deps_fold in H2 as [? ?].

    specialize (H1 kn). forward H1.
    now rewrite KernameSet.singleton_spec. red in H1. destruct H1.
    elimtype False. destruct H1 as [cst [declc _]].
    { red in declc. destruct x1 as [d _]. red in d. rewrite d in declc. noconf declc. }
    destruct H1 as [mib [mib' [declm [declm' em]]]].
    pose proof em as em'. destruct em'.
    destruct x1 as [x1 hnth].
    red in x1, declm. rewrite x1 in declm. noconf declm.
    eapply Forall2_nth_error_left in H1; eauto. destruct H1 as [? [? ?]].
    eapply erases_deps_tCase; eauto. 
    split; eauto. split; eauto.
    destruct H1.
    eapply In_Forall in H3.
    eapply All_Forall. eapply Forall_All in H3.
    eapply Forall2_All2 in H0.
    eapply All2_All_mix_right in H0; eauto.
    assert (All (fun br => ∑ T, Σ ;;; Γ ,,, inst_case_branch_context p br |- br.(bbody) : T) brs).
    eapply All2i_All_right. eapply brs_ty.
    simpl. intuition auto. eexists ; eauto.
    now rewrite -(PCUICCasesContexts.inst_case_branch_context_eq a).
    ELiftSubst.solve_all. destruct a0 as [T' HT]. eauto.
    
  - apply inversion_Proj in wt as (?&?&?&?&?&?&?&?&?&?); eauto.
    destruct (proj1 d).
    specialize (H0 (inductive_mind p.(proj_ind))). forward H0.
    now rewrite KernameSet.singleton_spec. red in H0. destruct H0.
    elimtype False. destruct H0 as [cst [declc _]].
    { red in declc. destruct d as [[[d _] _] _]. red in d. rewrite d in declc. noconf declc. }
    destruct H0 as [mib [mib' [declm [declm' em]]]].
    assert (mib = x0).
    { destruct d as [[[]]].
      red in H0, declm. rewrite H0 in declm. now noconf declm. } 
    subst x0.
    pose proof em as em'. destruct em'.
    eapply Forall2_nth_error_left in H0 as (x' & ? & ?); eauto.
    2:{ apply d. }
    simpl in *.
    destruct (ind_ctors x1) => //. noconf H3.
    set (H1' := H5). destruct H1' as [].
    set (d' := d). destruct d' as [[[]]].
    eapply Forall2_All2 in H3. eapply All2_nth_error_Some in H3 as [? [? []]]; tea.
    destruct H6 as [Hprojs _].
    eapply Forall2_All2 in Hprojs. eapply All2_nth_error_Some in Hprojs as [? []]; tea.
    2:eapply d.
    econstructor; tea. all:eauto.
    split => //. 2:split; eauto.
    split; eauto. split; eauto.
    rewrite -H4. symmetry; apply d.
    
  - constructor.
    apply inversion_Fix in wt as (?&?&?&?&?&?&?); eauto.
    eapply All_Forall. eapply includes_deps_fold in Σer as [_ Σer].
    eapply In_Forall in Σer.
    eapply Forall_All in Σer.
    eapply Forall2_All2 in H.
    ELiftSubst.solve_all.
  - constructor.
    apply inversion_CoFix in wt as (?&?&?&?&?&?&?); eauto.
    eapply All_Forall. eapply includes_deps_fold in Σer as [_ Σer].
    eapply In_Forall in Σer.
    eapply Forall_All in Σer.
    eapply Forall2_All2 in H.
    ELiftSubst.solve_all. Unshelve. 
Qed.

Lemma erases_weakeninv_env {Σ Σ' : global_env_ext} {Γ t t' T} :
  wf Σ' -> extends_decls Σ Σ' -> 
  Σ ;;; Γ |- t : T ->
  erases Σ Γ t t' -> erases (Σ'.1, Σ.2) Γ t t'.
Proof.
  intros wfΣ' ext Hty.
  eapply (env_prop_typing ESubstitution.erases_extends); tea.
  eapply extends_decls_wf; tea.
Qed.  
 
Lemma erases_deps_weaken kn d (Σ : global_env) (Σ' : EAst.global_declarations) t : 
  wf (add_global_decl Σ (kn, d)) ->
  erases_deps Σ Σ' t ->
  erases_deps (add_global_decl Σ (kn, d)) Σ' t.
Proof.
  intros wfΣ er.
  induction er using erases_deps_forall_ind; try solve [now constructor].
  - assert (kn <> kn0).
    { inv wfΣ. inv X. intros <-.
      eapply lookup_env_Some_fresh in H. contradiction. }
    eapply erases_deps_tConst with cb cb'; eauto.
    red. rewrite /lookup_env lookup_env_cons_fresh //.
    red.
    red in H1.
    destruct (cst_body cb) eqn:cbe;
    destruct (E.cst_body cb') eqn:cbe'; auto.
    specialize (H3 _ eq_refl).
    eapply on_declared_constant in H; auto.
    2:{ inv wfΣ. now inv X. }
    red in H. rewrite cbe in H. simpl in H.
    eapply (erases_weakeninv_env (Σ := (Σ, cst_universes cb))
       (Σ' := (add_global_decl Σ (kn, d), cst_universes cb))); eauto.
    simpl.
    split => //; eexists [(kn, d)]; intuition eauto.
  - econstructor; eauto. eapply weakening_env_declared_constructor; eauto.
    eapply extends_decls_extends. econstructor; try reflexivity. eexists [(_, _)]; reflexivity. 
  - econstructor; eauto.
    red. destruct H. split; eauto.
    red in H. red.
    inv wfΣ. inv X.
    rewrite -H. simpl. unfold lookup_env; simpl. destruct (eqb_spec (inductive_mind p.1) kn); try congruence.
    eapply lookup_env_Some_fresh in H. subst kn; contradiction.
  - econstructor; eauto.
    red. destruct H. split; eauto.
    destruct d0; split; eauto.
    destruct d0; split; eauto.
    inv wfΣ. inv X.
    red in H |- *.
    rewrite -H. simpl. unfold lookup_env; simpl; destruct (eqb_spec (inductive_mind p.(proj_ind)) kn); try congruence.
    eapply lookup_env_Some_fresh in H. subst kn. contradiction.
Qed.

Lemma lookup_env_ext {Σ kn kn' d d'} : 
  wf (add_global_decl Σ (kn', d')) ->
  lookup_env Σ kn = Some d ->
  kn <> kn'.
Proof.
  intros wf hl. 
  eapply lookup_env_Some_fresh in hl.
  inv wf. inv X.
  destruct (eqb_spec kn kn'); subst; congruence.
Qed.

Lemma lookup_env_cons_disc {Σ kn kn' d} : 
  kn <> kn' ->
  lookup_env (add_global_decl Σ (kn', d)) kn = lookup_env Σ kn.
Proof.
  intros Hk. simpl; unfold lookup_env; simpl.
  destruct (eqb_spec kn kn'); congruence.
Qed.

Lemma elookup_env_cons_disc {Σ kn kn' d} : 
  kn <> kn' ->
  EGlobalEnv.lookup_env ((kn', d) :: Σ) kn = EGlobalEnv.lookup_env Σ kn.
Proof.
  intros Hk. simpl.
  destruct (eqb_spec kn kn'); congruence.
Qed.

Lemma global_erases_with_deps_cons kn kn' d d' Σ Σ' : 
  wf (add_global_decl Σ (kn', d)) ->
  global_erased_with_deps Σ Σ' kn ->
  global_erased_with_deps (add_global_decl Σ (kn', d)) ((kn', d') :: Σ') kn.
Proof.
  intros wf [[cst [declc [cst' [declc' [ebody IH]]]]]|].
  red. inv wf. inv X. left.
  exists cst. split.
  red in declc |- *. unfold lookup_env in *.
  rewrite lookup_env_cons_fresh //.
  { eapply lookup_env_Some_fresh in declc.
    intros <-; contradiction. }
  exists cst'.
  unfold EGlobalEnv.declared_constant. rewrite EGlobalEnv.elookup_env_cons_fresh //.
  { eapply lookup_env_Some_fresh in declc.
    intros <-; contradiction. }
  red in ebody. unfold erases_constant_body.
  destruct (cst_body cst) eqn:bod; destruct (E.cst_body cst') eqn:bod' => //.
  intuition auto.
  eapply (erases_weakeninv_env (Σ  := (_, cst_universes cst)) (Σ' := (add_global_decl Σ (kn', d), cst_universes cst))); eauto.
  constructor; eauto. constructor; eauto.
  split => //. exists [(kn', d)]; intuition eauto.
  eapply on_declared_constant in declc; auto.
  red in declc. rewrite bod in declc. eapply declc.
  split => //.
  noconf H0.
  eapply erases_deps_cons; eauto.
  constructor; auto.

  right. destruct H as [mib [mib' [? [? ?]]]].
  exists mib, mib'. intuition eauto.
  * red. red in H. pose proof (lookup_env_ext wf H).
    now rewrite lookup_env_cons_disc.
  * red. pose proof (lookup_env_ext wf H).
    now rewrite elookup_env_cons_disc.
Qed.

Lemma global_erases_with_deps_weaken kn kn' d Σ Σ' : 
  wf (add_global_decl Σ (kn', d)) ->
  global_erased_with_deps Σ Σ' kn ->
  global_erased_with_deps (add_global_decl Σ (kn', d)) Σ' kn.
Proof.
  intros wf [[cst [declc [cst' [declc' [ebody IH]]]]]|].
  red. inv wf. inv X. left.
  exists cst. split.
  red in declc |- *.
  unfold lookup_env in *.
  rewrite lookup_env_cons_fresh //.
  { eapply lookup_env_Some_fresh in declc.
    intros <-. contradiction. }
  exists cst'.
  unfold EGlobalEnv.declared_constant.
  red in ebody. unfold erases_constant_body.
  destruct (cst_body cst) eqn:bod; destruct (E.cst_body cst') eqn:bod' => //.
  intuition auto.
  eapply (erases_weakeninv_env (Σ  := (Σ, cst_universes cst)) (Σ' := (add_global_decl Σ (kn', d), cst_universes cst))). 4:eauto.
  split; auto. constructor; eauto.
  split; auto; exists [(kn', d)]; intuition eauto.
  eapply on_declared_constant in declc; auto.
  red in declc. rewrite bod in declc. eapply declc. split => //.
  noconf H0.
  apply erases_deps_weaken.
  { split; auto. cbn. constructor; auto. }
  auto.

  right. destruct H as [mib [mib' [Hm [? ?]]]].
  exists mib, mib'; intuition auto.
  red. unfold lookup_env in *.
  rewrite lookup_env_cons_fresh //.
  now epose proof (lookup_env_ext wf Hm).
Qed.

Lemma erase_constant_body_correct (Σ : wf_env_ext) Σ' cb (onc : ∥ on_constant_decl (lift_typing typing) Σ cb ∥) :
  wf Σ' -> extends_decls Σ Σ' ->
  erases_constant_body (Σ', Σ.(referenced_impl_env_ext).2) cb (fst (erase_constant_body Σ cb onc)).
Proof.
  red. sq. destruct cb as [name [bod|] univs]; simpl. intros.
  eapply (erases_weakeninv_env (Σ := Σ) (Σ' := (Σ', univs))); simpl; auto.
  red in o. simpl in o. eapply o.
  eapply erases_erase. auto.
Qed.

Lemma erase_constant_body_correct' {Σ : wf_env_ext} {cb} {onc : ∥ on_constant_decl (lift_typing typing) Σ cb ∥} {body} :
  EAst.cst_body (fst (erase_constant_body Σ cb onc)) = Some body ->
  ∥ ∑ t T, (Σ ;;; [] |- t : T) * (Σ ;;; [] |- t ⇝ℇ body) *
    (term_global_deps body = snd (erase_constant_body Σ cb onc)) ∥.
Proof.
  intros. destruct cb as [name [bod|] univs]; simpl. intros.
  simpl in H. noconf H.
  set (obl :=(erase_constant_body_obligation_1 Σ
  {|
  cst_type := name;
  cst_body := Some bod;
  cst_universes := univs |} onc bod eq_refl)). clearbody obl.
  assert (wfΣ' : abstract_env_rel' Σ Σ) by reflexivity.
  destruct (obl _ wfΣ'). sq.
  exists bod, A; intuition auto. simpl.
  eapply erases_erase. now simpl in H.
Qed.

Lemma erases_mutual {Σ mdecl m} : 
  on_inductive (lift_typing typing) (Σ, ind_universes m) mdecl m ->
  erases_mutual_inductive_body m (erase_mutual_inductive_body m).
Proof.
  intros oni.
  destruct m; constructor; simpl; auto.
  eapply onInductives in oni; simpl in *.
  assert (Alli (fun i oib => 
    match destArity [] oib.(ind_type) with Some _ => True | None => False end) 0 ind_bodies0).
  { eapply Alli_impl; eauto.
    simpl. intros n x []. simpl in *. rewrite ind_arity_eq.
    rewrite !destArity_it_mkProd_or_LetIn /= //. } clear oni.
  induction X; constructor; auto.
  destruct hd; constructor; simpl; auto.
  clear.
  induction ind_ctors0; constructor; auto.
  cbn in *.
  intuition auto.
  induction ind_projs0; constructor; auto.
  unfold isPropositionalArity.
  destruct destArity as [[? ?]|] eqn:da; auto.
Qed.

Lemma erase_global_includes (Σ : wf_env) deps deps' :
  (forall d, KernameSet.In d deps' -> ∥ ∑ decl, lookup_env Σ d = Some decl ∥) ->
  KernameSet.subset deps' deps ->
  let Σ' := erase_global deps Σ in
  includes_deps Σ Σ' deps'.
Proof.
  sq. unfold erase_global.
  set (e := eq_refl). clearbody e.
  move: e. generalize (declarations Σ) at 2 3.
  induction g in deps, deps', Σ |- *.
  - simpl; intros eq H.
    intros sub i hin. elimtype False.
    specialize (H i hin) as [[decl Hdecl]].
    rewrite /lookup_env eq in Hdecl. noconf Hdecl.
  - intros e H sub i hin.
    destruct Σ.(referenced_impl_wf) as [wfΣ].
    destruct a as [kn d].
    eapply KernameSet.subset_spec in sub.
    destruct (H i hin) as [[decl Hdecl]]. unfold lookup_env in Hdecl.
    cbn in Hdecl.
    pose proof (eqb_spec i kn).
    rewrite e in Hdecl. move: Hdecl. cbn -[erase_global_decls].
    elim: H0. intros -> [= <-].
    * destruct d as [|]; [left|right].
      { exists c. split; auto. red.
        unfold lookup_env; simpl; rewrite e. cbn. rewrite eq_kername_refl //.
        pose proof (sub _ hin) as indeps.
        eapply KernameSet.mem_spec in indeps.
        unfold EGlobalEnv.declared_constant.
        destruct (H _ hin) as [[decl hd]].
        eexists; intuition eauto.
        cbn. 
        rewrite indeps. cbn.
        rewrite eq_kername_refl. reflexivity.
        eapply erase_constant_body_correct; eauto.
        set (obl2 := erase_global_decls_obligation_2 _ _ _ _ _ _ _). clearbody obl2.
        set (obl1 := erase_global_decls_obligation_1 _ _ _ _ _ _ _) in *.
        clearbody obl1. 
        red. simpl.
        split => //. exists [(kn, ConstantDecl c)]; intuition auto.
        cbn.
        set (obl2 := erase_global_decls_obligation_2 _ _ _ _ _ _ _) in *. 
        set (obl1 := erase_global_decls_obligation_1 _ _ _ _ _ _ _) in *. 
        cbn [erase_global_decls].
        rewrite indeps.
        rewrite -wf_env_eta e.
        set (Σp := {| universes := Σ.(universes); declarations := g |}).
        eapply (erases_deps_cons Σp); eauto.
        apply wfΣ. destruct wfΣ. now rewrite e in o0.
        pose proof (erase_constant_body_correct' H0).
        sq. destruct X as [bod [bodty [[Hbod Hebod] Heqdeps]]].
        set (wfΣp := make_wf_env_ext _ _ _) in *.
        assert ((Σp, cst_universes c) = wfΣp :> global_env_ext) by reflexivity.
        eapply (erase_global_erases_deps (Σ := (Σp, cst_universes c))); simpl; auto.
        { constructor; simpl; auto. depelim wfΣ. rewrite e in o0. now depelim o0.
           depelim wfΣ. rewrite e in o0. now depelim o0. }
        all:eauto.
        assert (wfuΣ : wf {| universes := Σ.(universes); declarations := g |}).
        { split => //. cbn. apply wfΣ. cbn. destruct wfΣ.
          rewrite e in o0. now depelim o0. }
        eapply (IHg (remove_kn kn Σ g obl1)).
        { intros.
          eapply term_global_deps_spec in Hebod; eauto. }
        { eapply KernameSet.subset_spec.
          intros x hin'. eapply KernameSet.union_spec. right; auto.
          set (obl2' := erase_global_decls_obligation_2 _ _ _ _ _ _ _) in *.
          set (obl1' := erase_global_decls_obligation_1 _ _ _ _ _ _ _) in *.
          set (obl3' := erase_global_decls_obligation_3 _ _ _ _ _ _ _) in *.
          now rewrite -Heqdeps. } }
        { eexists m, _; intuition eauto.
          simpl. rewrite /declared_minductive /lookup_env e.
          simpl. rewrite eq_kername_refl. reflexivity.
          specialize (sub _ hin).
          eapply KernameSet.mem_spec in sub.
          simpl. rewrite sub.
          red. cbn. rewrite eq_kername_refl.
          reflexivity.
          assert (declared_minductive Σ kn m).
          { red. unfold lookup_env. rewrite e. cbn. now rewrite eqb_refl. }
          eapply on_declared_minductive in H0; tea.
          now eapply erases_mutual. }

    * intros ikn Hi.
      set (Σp := {| universes := Σ.(universes); declarations := g |}).
      assert (wfΣp : wf {| universes := Σ.(universes); declarations := g |}).
      { split => //. cbn. apply wfΣ. cbn. destruct wfΣ.
        rewrite e in o0. now depelim o0. }
      destruct d as [|].
      ++ simpl. destruct (KernameSet.mem kn deps) eqn:eqkn.
        rewrite -wf_env_eta e.
        eapply (global_erases_with_deps_cons _ kn (ConstantDecl _) _ Σp); eauto.
        unfold add_global_decl; cbn. now rewrite -e wf_env_eta.
        eapply (IHg (remove_kn kn Σ g _) _ (KernameSet.singleton i)); auto.
        3:{ eapply KernameSet.singleton_spec => //. }
        intros.
        eapply KernameSet.singleton_spec in H0. subst.
        constructor; exists decl; auto.
        eapply KernameSet.subset_spec. intros ? ?.
        eapply KernameSet.union_spec. left.
        eapply KernameSet.singleton_spec in H0; subst.
        now eapply sub.
      
        rewrite -wf_env_eta e.
        eapply (global_erases_with_deps_weaken _ kn (ConstantDecl _) Σp). eauto.
        rewrite /add_global_decl /= -e wf_env_eta //.
        eapply (IHg (remove_kn _ _ _ _) deps (KernameSet.singleton i)) => //.
        3:now eapply KernameSet.singleton_spec.
        intros d ind%KernameSet.singleton_spec.
        subst. constructor; eexists; eauto.
        eapply KernameSet.subset_spec.
        intros ? hin'. eapply sub. eapply KernameSet.singleton_spec in hin'. now subst.        

      ++ simpl. 
        destruct (KernameSet.mem kn deps) eqn:eqkn.
        { rewrite -wf_env_eta e.
          eapply (global_erases_with_deps_cons _ kn (InductiveDecl _) _ Σp); eauto.
          { rewrite /add_global_decl /= -e wf_env_eta //. }
          eapply (IHg (remove_kn _ _ _ _) _ (KernameSet.singleton i)); auto.
          3:{ eapply KernameSet.singleton_spec => //. }
          intros.
          eapply KernameSet.singleton_spec in H0. subst.
          constructor; exists decl; auto.
          eapply KernameSet.subset_spec. intros ? ?.
          eapply KernameSet.singleton_spec in H0; subst.
          now eapply sub. }
    
        { rewrite -wf_env_eta e.
          eapply (global_erases_with_deps_weaken _ kn (InductiveDecl _) Σp). eauto.
          { rewrite /add_global_decl /= -e wf_env_eta //. }
          eapply (IHg (remove_kn _ _ _ _) deps (KernameSet.singleton i)) => //.
          3:now eapply KernameSet.singleton_spec.
          intros d ind%KernameSet.singleton_spec.
          subst. constructor; eexists; eauto.
          eapply KernameSet.subset_spec.
          intros ? hin'. eapply sub. eapply KernameSet.singleton_spec in hin'. now subst. }
Qed.

Definition sq_wf_ext {Σ : global_env_ext} (wfΣ : ∥ wf_ext Σ ∥) : ∥ wf Σ.1 ∥.
Proof.
  sq. exact X.1.
Qed.

Lemma erase_correct (wfl := Ee.default_wcbv_flags) (Σ : wf_env) univs wfext t v Σ' t' deps :
  let Σext := make_wf_env_ext Σ univs wfext in
  forall wt : forall Σ0 : global_env_ext, abstract_env_rel' Σext Σ0 -> welltyped Σ0 [] t,
  erase Σext [] t wt = t' ->
  KernameSet.subset (term_global_deps t') deps ->
  erase_global deps Σ = Σ' ->
  Σ |-p t ▷ v ->
  exists v', Σext;;; [] |- v ⇝ℇ v' /\ ∥ Σ' ⊢ t' ▷ v' ∥.
Proof.
  intros Σext wt.
  intros HΣ' Hsub Ht' ev.
  pose proof (erases_erase (Σ := Σext) wt); eauto.
  rewrite HΣ' in H.
  assert (wfΣ' : abstract_env_rel' Σext Σext) by reflexivity.
  destruct (wt _ wfΣ') as [T wt'].
  destruct Σext.(referenced_impl_ext_wf) as [wfΣ].
  unshelve epose proof (erase_global_erases_deps (Σ' := Σ') wfΣ wt' H _); cycle 2.
  intros.
  rewrite <- Ht'.
  eapply erase_global_includes.
  intros.
  eapply term_global_deps_spec in H; eauto.
  assumption.
  eapply erases_correct; tea.
Qed.

Lemma global_env_ind (P : global_env -> Type) (Pnil : forall univs, P {| universes := univs; declarations := [] |})
  (Pcons : forall (Σ : global_env) d, P Σ -> P (add_global_decl Σ d))
  (Σ : global_env) : P Σ.
Proof.
  destruct Σ as [univs Σ].
  induction Σ; cbn. apply Pnil.
  now apply (Pcons {| universes := univs; declarations := Σ |} a).
Qed.

Lemma on_global_env_ind (P : forall Σ : global_env, wf Σ -> Type)
  (Pnil : forall univs (onu : on_global_univs univs), P {| universes := univs; declarations := [] |}
    (onu, globenv_nil _ _))
  (Pcons : forall (Σ : global_env) kn d (wf : wf Σ) 
    (Hfresh : fresh_global kn Σ.(declarations))
    (udecl := PCUICLookup.universes_decl_of_decl d)
    (onud : on_udecl Σ.(universes) udecl)
    (pd : on_global_decl (lift_typing typing) ({| universes := Σ.(universes); declarations := Σ.(declarations) |}, udecl) kn d),
    P Σ wf -> P (add_global_decl Σ (kn, d)) 
    (fst wf, globenv_decl _ Σ.(universes) Σ.(declarations) kn d (snd wf) Hfresh onud pd))
  (Σ : global_env) (wfΣ : wf Σ) : P Σ wfΣ.
Proof.
  destruct Σ as [univs Σ]. destruct wfΣ; cbn in *.
  induction o0. apply Pnil.
  apply (Pcons {| universes := univs; declarations := Σ |} kn d (o, o0)).
  exact IHo0.
Qed.

Ltac inv_eta :=
  lazymatch goal with
  | [ H : PCUICEtaExpand.expanded _ _ |- _ ] => depelim H
  end.


Lemma leq_term_propositional_sorted_l {Σ Γ v v' u u'} :
   wf_ext Σ ->
   PCUICEquality.leq_term Σ (global_ext_constraints Σ) v v' ->
   Σ;;; Γ |- v : tSort u ->
   Σ;;; Γ |- v' : tSort u' -> is_propositional u -> 
   leq_universe (global_ext_constraints Σ) u' u.
Proof.
  intros wfΣ leq hv hv' isp.
  eapply orb_true_iff in isp as [isp | isp].
  - eapply leq_term_prop_sorted_l; eauto.
  - eapply leq_term_sprop_sorted_l; eauto.
Qed.

Fixpoint map_erase (Σ : wf_env_ext) Γ (ts : list term) (H2 : Forall (welltyped Σ Γ) ts) : list E.term.
destruct ts as [ | t ts].
- exact [].
- eapply cons. refine (erase Σ Γ t _). 
  2: eapply (map_erase Σ Γ ts).
  all: now inversion H2; subst.
Defined.

Lemma map_erase_irrel Σ Γ t H1 H2 : map_erase Σ Γ t H1 = map_erase Σ Γ t H2.
Proof.
  induction t.
  - cbn. reflexivity.
  - cbn. depelim H1; cbn. depelim H2; cbn.
    f_equal.
    + eapply erase_irrel.
    + eapply IHt.
Qed.

Arguments map_erase _ _ _ _, _ _ _ {_}.

Lemma erase_mkApps {Σ : wf_env_ext} Γ t args H2 Ht Hargs :
  wf_local Σ Γ ->
  ~ ∥ isErasable Σ Γ (mkApps t args) ∥ ->
  erase Σ Γ (mkApps t args) H2 = 
  E.mkApps (erase Σ Γ t Ht) (map_erase Σ Γ args Hargs).
Proof.
  pose proof (referenced_impl_ext_wf Σ) as [wf]. 
  intros Hwflocal Herasable. induction args in t, H2, Ht, Hargs, Herasable |- *.
  - cbn. eapply erase_irrel.
  - cbn [mkApps]. 
    rewrite IHargs. 
    1: inversion Hargs; eauto.
    2: eauto.
    2:{ intros ? wfΣ'. destruct (H2 _ wfΣ'). cbn in X. eapply inversion_mkApps in X as (? & ? & ?).
        econstructor. eauto. }
    intros Happ Hargs'.
    etransitivity. simp erase. reflexivity. unfold erase_clause_1.
    unfold inspect. unfold erase_clause_1_clause_2.
    elim: is_erasableP.
    + intros. exfalso. 
      eapply Herasable. destruct p.
      cbn. destruct (H2 _ eq_refl). eapply Is_type_app; eauto.
    + cbn [map_erase]. 
      epose proof (fst (erase_irrel _)). cbn.
      intros he. f_equal => //. f_equal.
      eapply erase_irrel. eapply erase_irrel.
      eapply map_erase_irrel. 
      Unshelve. cbn in wfΣ'; subst; eauto.  exact Σ.
Qed.

Lemma map_erase_length Σ Γ t H1 : length (map_erase Σ Γ t H1) = length t.
Proof.
  induction t; cbn; f_equal; [ | inversion H1; subst ]; eauto.
Qed.

Local Hint Constructors expanded : expanded.

Local Arguments erase_global_decls _ _ _ : clear implicits.

(* Lemma make_wf_env_ext_remove_kn kn decl univs decls : *)
  (* make_wf_env_ext (remove_kn kn (add_global_decl  )) *)

Lemma lookup_env_erase (Σ : wf_env) deps kn d :
  KernameSet.In kn deps -> 
  lookup_env Σ kn = Some (InductiveDecl d) ->
  EGlobalEnv.lookup_env (erase_global deps Σ) kn = Some (EAst.InductiveDecl (erase_mutual_inductive_body d)).
Proof.
  intros hin.
  rewrite /lookup_env. 
  unfold erase_global.
  set (e := eq_refl).
  clearbody e.
  move: e. generalize (declarations Σ) at 2 3 4.
  induction g in Σ, deps, hin |- *.
  - move=> /= //.
  - intros e. destruct a as [kn' d'].
    cbn -[erase_global_decls].
    case: (eqb_spec kn kn'); intros e'; subst.
    intros [= ->].
    unfold erase_global_decls.
    eapply KernameSet.mem_spec in hin. rewrite hin /=.
    now rewrite eq_kername_refl.
    intros hl. destruct d'. simpl.
    destruct KernameSet.mem. cbn.
    rewrite (negbTE (proj2 (neqb _ _) e')).
    eapply IHg => //. eapply KernameSet.union_spec. left => //.
    eapply IHg => //.
    simpl.
    destruct KernameSet.mem. cbn.
    rewrite (negbTE (proj2 (neqb _ _) e')).
    eapply IHg => //.
    eapply IHg => //. 
Qed.

Lemma erase_global_declared_constructor (Σ : wf_env) ind c mind idecl cdecl deps :
   declared_constructor Σ (ind, c) mind idecl cdecl ->
   KernameSet.In ind.(inductive_mind) deps -> 
   EGlobalEnv.declared_constructor (erase_global deps Σ) (ind, c) 
    (erase_mutual_inductive_body mind) (erase_one_inductive_body idecl) 
    (EAst.mkConstructor cdecl.(cstr_name) cdecl.(cstr_arity)).
Proof.
  intros [[]] Hin.
  cbn in *. split. split. 
  - red in H |- *. now eapply lookup_env_erase.
  - cbn. now eapply map_nth_error.
  - cbn. erewrite map_nth_error; eauto.
Qed.

Import EGlobalEnv.
Lemma erase_global_decls_fresh kn deps Σ decls heq : 
  let Σ' := erase_global_decls deps Σ decls heq in
  PCUICTyping.fresh_global kn decls ->
  fresh_global kn Σ'.
Proof.
  cbn.
  revert deps Σ heq.
  induction decls; [cbn; auto|].
  - intros. red. constructor.
  - destruct a as [kn' d]. intros. depelim H.
    cbn in H, H0.
    destruct d as []; simpl; destruct KernameSet.mem.
    + cbn [EGlobalEnv.closed_env forallb]. cbn.
      constructor => //. eapply IHdecls => //.
    + eapply IHdecls => //.
    + constructor; auto.
      eapply IHdecls => //.
    + eapply IHdecls => //.
Qed.

Lemma erase_global_fresh kn deps Σ : 
  let Σ' := erase_global deps Σ in
  PCUICTyping.fresh_global kn Σ.(declarations) ->
  fresh_global kn Σ'.
Proof.
  unfold erase_global.
  intros fr. now eapply erase_global_decls_fresh.
Qed.

From MetaCoq.Erasure Require Import EEtaExpandedFix.

Lemma erase_brs_eq Σ Γ p ts wt : 
  erase_brs Σ Γ p ts wt = map_All (fun br wt => (erase_context (bcontext br), erase Σ _ (bbody br) wt)) ts wt.
Proof.
  funelim (map_All _ ts wt); cbn; auto.
  f_equal => //. f_equal => //. apply erase_irrel.
  rewrite -H. eapply erase_irrel.
Qed.

Lemma erase_fix_eq Σ Γ ts wt : 
  erase_fix Σ Γ ts wt = map_All (fun d wt => 
    let dbody' := erase Σ _ (dbody d) (fun Σ abs => proj2 (wt Σ abs)) in
    let dbody' := if isBox dbody' then
        match d.(dbody) with
        | tLambda na _ _ => E.tLambda (binder_name na) E.tBox
        | _ => dbody'
        end else dbody' 
    in
    {| E.dname := d.(dname).(binder_name); E.rarg := d.(rarg); E.dbody := dbody' |}) ts wt.
Proof.
  funelim (map_All _ ts wt); cbn; auto.
  f_equal => //. f_equal => //.
  rewrite (fst (erase_irrel _) _ _ _ (fun (Σ0 : global_env_ext) (abs : Σ0 = Σ) =>
    (map_All_obligation_1 x xs h Σ0 abs).p2)).
  destruct erase => //.
  rewrite -H. eapply erase_irrel.
Qed.

Lemma erase_cofix_eq Σ Γ ts wt : 
  erase_cofix Σ Γ ts wt = map_All (fun d wt => 
    let dbody' := erase Σ _ (dbody d) wt in
    {| E.dname := d.(dname).(binder_name); E.rarg := d.(rarg); E.dbody := dbody' |}) ts wt.
Proof.
  funelim (map_All _ ts wt); cbn; auto.
  f_equal => //. f_equal => //.
  apply erase_irrel.
  rewrite -H. eapply erase_irrel.
Qed.

Lemma isConstruct_erase Σ Γ t wt : 
  ~ (PCUICEtaExpand.isConstruct t || PCUICEtaExpand.isFix t || PCUICEtaExpand.isRel t) ->
  ~ (isConstruct (erase Σ Γ t wt) || isFix (erase Σ Γ t wt) || isRel (erase Σ Γ t wt)).
Proof.
  apply (erase_elim Σ
    (fun Γ t wt e => ~ (PCUICEtaExpand.isConstruct t || PCUICEtaExpand.isFix t || PCUICEtaExpand.isRel t) -> ~ (isConstruct e || isFix e || isRel e))
    (fun Γ l awt e => True)
    (fun Γ p l awt e => True)
    (fun Γ l awt e => True)
    (fun Γ l awt e => True)); intros => //. bang.
Qed.

Lemma apply_expanded Σ Γ Γ' t t' :
  expanded Σ Γ t -> Γ = Γ' -> t = t' -> expanded Σ Γ' t'.
Proof. intros; now subst. Qed.

Lemma isLambda_inv t : isLambda t -> exists na ty bod, t = tLambda na ty bod.
Proof. destruct t => //; eauto. Qed.
Lemma erases_deps_erase (cf := config.extraction_checker_flags) {Σ : wf_env} univs (wfΣ : ∥ wf_ext (Σ, univs) ∥)
  (Σ' := make_wf_env_ext Σ univs wfΣ) Γ t 
  (wt : forall Σ0 : global_env_ext, abstract_env_rel' Σ' Σ0 -> welltyped Σ0 Γ t) :
  let et := erase Σ' Γ t wt in
  let deps := EAstUtils.term_global_deps et in
  erases_deps Σ (erase_global deps Σ) et.
Proof.
  intros et deps. destruct wfΣ.
  pose proof (wt Σ' eq_refl). destruct H.
  eapply (erase_global_erases_deps w); tea.
  eapply (erases_erase (Σ := Σ') (Γ := Γ)).
  eapply erase_global_includes.
  intros.
  eapply term_global_deps_spec in H; eauto.
  assumption.
  eapply (erases_erase (Σ := Σ') (Γ := Γ)).
  eapply KernameSet.subset_spec. reflexivity. 
Qed.

Lemma erases_deps_erase_weaken (cf := config.extraction_checker_flags) {Σ : wf_env} univs
  (wfΣ : ∥ wf_ext (Σ, univs) ∥) Γ
  (Σ' := make_wf_env_ext Σ univs wfΣ) t 
  (wt : forall Σ0 : global_env_ext, abstract_env_rel' Σ' Σ0 -> welltyped Σ0 Γ t) 
  deps :
  let et := erase Σ' Γ t wt in
  let tdeps := EAstUtils.term_global_deps et in
  erases_deps Σ (erase_global (KernameSet.union deps tdeps) Σ) et.
Proof.
  intros et tdeps. destruct wfΣ.
  pose proof (wt Σ' eq_refl). destruct H.
  eapply (erase_global_erases_deps w); tea.
  eapply (erases_erase (Σ := Σ') (Γ := Γ)).
  eapply erase_global_includes.
  intros.
  eapply term_global_deps_spec in H; eauto.
  assumption.
  eapply (erases_erase (Σ := Σ') (Γ := Γ)).
  eapply KernameSet.subset_spec. intros x hin. eapply KernameSet.union_spec. now right.
Qed.

Lemma eta_expand_erase {Σ : wf_env_ext} Σ' {Γ t} 
  (wt : forall Σ0 : global_env_ext, abstract_env_rel' Σ Σ0 -> welltyped Σ0 Γ t) Γ' :
  PCUICEtaExpand.expanded Σ Γ' t ->
  erases_global Σ Σ' ->
  expanded Σ' Γ' (@erase Σ Γ t wt).
Proof.
  pose proof (referenced_impl_ext_wf Σ) as [wf]. 
  intros exp deps.
  eapply expanded_erases. apply wf.
  eapply erases_erase. assumption.
  pose proof (wt Σ eq_refl). destruct H as [T ht].
  eapply erases_global_erases_deps; tea.
  eapply erases_erase.
Qed.

Lemma erase_global_closed Σ deps :
  let Σ' := erase_global deps Σ in
  EGlobalEnv.closed_env Σ'.
Proof.
  sq.
  unfold erase_global.
  set (decls := declarations Σ).
  set (e := eq_refl). clearbody e.
  unfold decls at 1 in e. clearbody decls.
  revert Σ e deps.
  induction decls; [cbn; auto|].
  intros Σ e deps.
  destruct Σ.(referenced_impl_wf).
  destruct a as [kn d].
  destruct d as []; simpl; destruct KernameSet.mem.
  assert (wfs : PCUICTyping.wf {| universes := Σ.(universes); declarations := decls |}).
  { depelim X. rewrite e in o0. depelim o0; now split. }
  + cbn [EGlobalEnv.closed_env forallb]. cbn.
    rewrite [forallb _ _](IHdecls) // andb_true_r.
    rewrite /test_snd /EGlobalEnv.closed_decl /=.
    set (er := erase_global_decls_obligation_1 _ _ _ _ _ _ _).
    set (er' := erase_global_decls_obligation_2 _ _ _ _ _ _ _).
    clearbody er er'.
    destruct c as [ty [] univs]; cbn.
    set (obl := erase_constant_body_obligation_1 _ _ _ _ _).
    set (wfe := make_wf_env_ext _ _ _).
    unfold erase_constant_body. cbn. clearbody obl.
    2:auto.
    unshelve epose proof (erases_erase (Σ := wfe) obl); eauto.
    cbn in H.
    eapply erases_closed in H => //.
    cbn. destruct (obl _ eq_refl). clear H. now eapply PCUICClosedTyp.subject_closed in X0.
  + eapply IHdecls => //.
  + cbn [EGlobalEnv.closed_env forallb].
    rewrite {1}/test_snd {1}/EGlobalEnv.closed_decl /=.
    eapply IHdecls => //.
  + eapply IHdecls => //.
Qed.

Import EWellformed.

Section wffix.
  Import EAst.
  Fixpoint wf_fixpoints (t : term) : bool :=
    match t with
    | tRel i => true
    | tEvar ev args => List.forallb (wf_fixpoints) args
    | tLambda N M => wf_fixpoints M
    | tApp u v => wf_fixpoints u && wf_fixpoints v
    | tLetIn na b b' => wf_fixpoints b && wf_fixpoints b'
    | tCase ind c brs => 
      let brs' := forallb (wf_fixpoints ∘ snd) brs in
      wf_fixpoints c && brs'
    | tProj p c => wf_fixpoints c
    | tFix mfix idx => 
      (idx <? #|mfix|) && List.forallb (fun d => (isLambda d.(dbody) || isBox d.(dbody)) && wf_fixpoints d.(dbody)) mfix
    | tCoFix mfix idx =>
      (idx <? #|mfix|) && List.forallb (wf_fixpoints ∘ dbody) mfix
    | tConst kn => true
    | tConstruct ind c => true
    | tVar _ => true
    | tBox => true
    end.

End wffix.

Lemma erases_deps_wellformed (cf := config.extraction_checker_flags) (efl := all_env_flags) {Σ} {Σ'} et :
  erases_deps Σ Σ' et ->
  forall n, ELiftSubst.closedn n et ->
  wf_fixpoints et ->
  wellformed Σ' n et.
Proof.
  intros ed.
  induction ed using erases_deps_forall_ind; intros => //; 
   try solve [cbn in *; unfold wf_fix in *; rtoProp; intuition eauto; solve_all].
  - cbn. red in H0. rewrite H0 //.
  - cbn -[lookup_constructor].
    cbn. now destruct H0 as [[-> ->] ->].
  - cbn in *. move/andP: H5 => [] cld clbrs.
    cbn. apply/andP; split. apply/andP; split. 
    * now destruct H0 as [-> ->].
    * now move/andP: H6.
    * move/andP: H6; solve_all.
  - cbn -[lookup_projection] in *. apply/andP; split; eauto.
    now rewrite (declared_projection_lookup H0).
Qed.

Lemma erases_wf_fixpoints Σ Γ t t' : Σ;;; Γ |- t ⇝ℇ t' -> 
  ErasureCorrectness.wellformed Σ t -> wf_fixpoints t'.
Proof.
  induction 1 using erases_forall_list_ind; cbn; auto; try solve [rtoProp; repeat solve_all].
  - move/andP => []. rewrite (All2_length X) => -> /=. unfold test_def in *.
    eapply Forall2_All2 in H.
    eapply All2_All2_mix in X; tea. solve_all.
    destruct b0; eapply erases_isLambda in H1; tea.
  - move/andP => []. rewrite (All2_length X) => -> /=.
    unfold test_def in *. solve_all.
Qed.

Lemma erase_wf_fixpoints (efl := all_env_flags) {Σ : wf_env} univs wfΣ {Γ t} wt
  (Σ' := make_wf_env_ext Σ univs wfΣ) :
  let t' := erase Σ' Γ t wt in
  wf_fixpoints t'.
Proof.
  cbn.
  eapply erases_wf_fixpoints.
  eapply erases_erase.
  specialize (wt (Σ, univs) eq_refl).
  destruct wfΣ.
  now unshelve eapply welltyped_wellformed in wt. 
Qed.

Lemma erase_wellformed (efl := all_env_flags) {Σ : wf_env} univs wfΣ {Γ t} wt
  (Σ' := make_wf_env_ext Σ univs wfΣ) :
  let t' := erase Σ' Γ t wt in
  wellformed (erase_global (term_global_deps t') Σ) #|Γ| t'.
Proof.
  set (t' := erase _ _ _ _).
  cbn.
  epose proof (@erases_deps_erase Σ univs wfΣ Γ t wt).
  cbn in H.
  epose proof (erases_deps_wellformed _ H #|Γ|).
  apply H0.
  eapply (erases_closed _ Γ).
  destruct (wt _ eq_refl).
  cbn in X. destruct wfΣ.
  now eapply PCUICClosedTyp.subject_closed in X.
  eapply erases_erase.
  eapply erase_wf_fixpoints.
Qed.

Lemma erase_wellformed_weaken (efl := all_env_flags) {Σ : wf_env} univs wfΣ {Γ t} wt deps
  (Σ' := make_wf_env_ext Σ univs wfΣ) :
  let t' := erase Σ' Γ t wt in
  wellformed (erase_global (KernameSet.union deps (term_global_deps t')) Σ) #|Γ| t'.
Proof.
  set (t' := erase _ _ _ _).
  cbn.
  epose proof (@erases_deps_erase_weaken Σ univs wfΣ Γ t wt deps).
  cbn in H.
  epose proof (erases_deps_wellformed _ H #|Γ|).
  apply H0.
  eapply (erases_closed _ Γ).
  - destruct (wt _ eq_refl).
    cbn in X. destruct wfΣ.
    now eapply PCUICClosedTyp.subject_closed in X.
  - eapply erases_erase.
  - eapply erase_wf_fixpoints.
Qed.

Lemma erase_constant_body_correct'' {Σ : wf_env} {cb} {univs wfΣ}
(Σ' := make_wf_env_ext Σ univs wfΣ)
{onc : ∥ on_constant_decl (lift_typing typing) Σ' cb ∥} {body} deps :  
  EAst.cst_body (fst (erase_constant_body Σ' cb onc)) = Some body ->
  ∥ ∑ t T, (Σ' ;;; [] |- t : T) * (Σ' ;;; [] |- t ⇝ℇ body) *
      (term_global_deps body = snd (erase_constant_body Σ' cb onc)) *
      wellformed (efl:=all_env_flags) (erase_global (KernameSet.union deps (term_global_deps body)) Σ) 0 body ∥.
Proof.
  intros. destruct cb as [name [bod|] udecl]; simpl. intros.
  simpl in H. noconf H.
  set (obl :=(erase_constant_body_obligation_1 Σ'
  {|
  cst_type := name;
  cst_body := Some bod;
  cst_universes := udecl |} onc bod eq_refl)). clearbody obl.
  assert (wfΣ' : abstract_env_rel' Σ' Σ') by reflexivity.
  destruct (obl _ wfΣ'). sq.
  have er : (Σ, univs);;; [] |- bod ⇝ℇ erase (make_wf_env_ext Σ univs (sq w)) [] bod obl.
  { eapply (erases_erase (Σ:=Σ')). }
  exists bod, A; intuition auto. eapply erase_wellformed_weaken.
  now simpl in H.
Qed.

Lemma erase_global_cst_decl_wf_glob Σ deps decls heq :
  forall cb wfΣ hcb,
  let ecb := erase_constant_body (make_wf_env_ext Σ (cst_universes cb) wfΣ) cb hcb in
  let Σ' := erase_global_decls (KernameSet.union deps ecb.2) Σ decls heq in
  @wf_global_decl all_env_flags Σ' (EAst.ConstantDecl ecb.1).
Proof.
  intros cb wfΣ hcb.
  set (ecb := erase_constant_body _ _ _). cbn.
  unfold wf_global_decl. cbn.
  destruct wfΣ, hcb. red in o.
  destruct EAst.cst_body eqn:hb => /= //. subst decls.
  eapply (erase_constant_body_correct'') in hb.
  destruct hb. destruct X as [t0 [T [[] ?]]].
  set(Σext := make_wf_env_ext _ _ _) in *.
  destruct p. rewrite e in i. exact i.  
Qed.

Lemma erase_global_ind_decl_wf_glob {Σ : wf_env} {deps decls kn m} (heq : declarations Σ = decls) :
  on_inductive (lift_typing typing) (Σ, ind_universes m) kn m ->
  let m' := erase_mutual_inductive_body m in
  let Σ' := erase_global_decls deps Σ decls heq in
  @wf_global_decl all_env_flags Σ' (EAst.InductiveDecl m').
Proof.
  set (m' := erase_mutual_inductive_body m).
  set (Σ' := erase_global_decls _ _ _ _). simpl.
  intros oni.
  pose proof (referenced_impl_wf Σ) as [wfΣ].
  assert (erases_mutual_inductive_body m (erase_mutual_inductive_body m)).
  { eapply (erases_mutual (mdecl:=kn)); tea. }
  eapply (erases_mutual_inductive_body_wf (univs := Σ.(universes)) (Σ := decls) (kn := kn) (Σ' := Σ')) in H; tea.
  simpl. rewrite -heq.
  destruct Σ ; cbn in *.
  destruct wf_env_referenced; cbn in *.
  now destruct referenced_impl_env; cbn in *.
Qed.

Lemma erase_global_decls_wf_glob Σ deps decls heq :
  let Σ' := erase_global_decls deps Σ decls heq in
  @wf_glob all_env_flags Σ'.
Proof.
  cbn.
  revert deps Σ heq.
  induction decls; [cbn; auto|].
  { intros. constructor. }
  intros. destruct a as [kn []]; simpl; destruct KernameSet.mem.
  + constructor. eapply IHdecls => //. eapply erase_global_cst_decl_wf_glob; auto.
    eapply erase_global_decls_fresh; auto.
    destruct Σ.(referenced_impl_wf).
    destruct X. rewrite heq in o0. now depelim o0.
  + cbn.
    eapply IHdecls.
  + constructor. eapply IHdecls.
    destruct Σ.(referenced_impl_wf) as [[onu ond]].
    rewrite heq in ond. depelim ond.
    eapply (erase_global_ind_decl_wf_glob (kn:=kn)); tea.
    eapply erase_global_decls_fresh.
    destruct Σ.(referenced_impl_wf) as [[onu ond]].
    rewrite heq in ond. now depelim ond.
  + eapply IHdecls.
Qed.

Lemma erase_global_wf_glob Σ deps :
  let Σ' := erase_global deps Σ in
  @wf_glob all_env_flags Σ'.
Proof. eapply erase_global_decls_wf_glob. Qed.


Lemma lookup_erase_global (cf := config.extraction_checker_flags) {Σ : wf_env} {deps deps'} :
  KernameSet.Subset deps deps' ->
  EExtends.global_subset (erase_global deps Σ) (erase_global deps' Σ).
Proof.
  unfold erase_global.
  destruct Σ as [[[univs Σ] wfΣ G wfG] map repr]. cbn in *. clear G wfG.
  revert deps deps' wfΣ map repr.
  induction Σ. cbn => //.
  intros deps deps' wfΣ map repr sub.
  destruct a as [kn' []]; cbn;
  (set (decl := E.ConstantDecl _) || set (decl := E.InductiveDecl _)); hidebody decl;
  set (eg := erase_global_decls _ _ _ _); hidebody eg;
  set (eg' := erase_global_decls _ _ _ _); hidebody eg';
  try (set (eg'' := erase_global_decls _ _ _ _); hidebody eg'');
  try (set (eg''' := erase_global_decls _ _ _ _); hidebody eg''').
  { destruct (KernameSet.mem) eqn:knm => /=.
    + eapply KernameSet.mem_spec, sub, KernameSet.mem_spec in knm. rewrite knm.
      apply EExtends.global_subset_cons. eapply IHΣ.
      intros x hin. eapply KernameSet.union_spec in hin.
      eapply KernameSet.union_spec. destruct hin. left. now eapply sub.
      right => //.
    + destruct (KernameSet.mem kn' deps') eqn:eq'.
      eapply EExtends.global_subset_cons_right.
      eapply erase_global_wf_glob.
      unfold decl. unfold hidebody.
      constructor. eapply erase_global_wf_glob.
      eapply erase_global_cst_decl_wf_glob.
      depelim wfΣ. depelim w. cbn in o0. depelim o0.
      eapply erase_global_decls_fresh => //.
      eapply IHΣ.
      intros x hin.
      eapply KernameSet.union_spec. left. now eapply sub.
      eapply IHΣ => //. }
  { destruct (KernameSet.mem) eqn:knm => /=.
    + eapply KernameSet.mem_spec, sub, KernameSet.mem_spec in knm. rewrite knm.
      apply EExtends.global_subset_cons. eapply IHΣ => //.
    + destruct (KernameSet.mem kn' deps') eqn:eq'.
      eapply EExtends.global_subset_cons_right. eapply erase_global_wf_glob.
      constructor. eapply erase_global_wf_glob.
      depelim wfΣ.
      eapply (erase_global_ind_decl_wf_glob (kn:=kn')). cbn.
      depelim w. now depelim o0.
      eapply erase_global_decls_fresh => //.
      clear -wfΣ. destruct wfΣ. destruct X as [onu ond]; cbn in *. now depelim ond.
      eapply IHΣ. intros x hin. now eapply sub.
      eapply IHΣ => //. }
Qed.

Lemma expanded_weakening_global Σ deps deps' Γ t : 
  KernameSet.Subset deps deps' ->
  expanded (erase_global deps Σ) Γ t ->
  expanded (erase_global deps' Σ) Γ t.
Proof.
  intros hs.
  eapply expanded_ind; intros; try solve [econstructor; eauto].
  - eapply expanded_tFix; tea. solve_all.
  - eapply expanded_tConstruct_app; tea.
    destruct H. split; tea.
    destruct d; split => //.
    cbn in *. red in H.
    eapply lookup_erase_global in H; tea.
Qed.

Lemma expanded_erase (cf := config.extraction_checker_flags) {Σ : wf_env} univs wfΣ t wtp :
  PCUICEtaExpand.expanded Σ [] t ->
  let Σ' := make_wf_env_ext Σ univs wfΣ in
  let et := (erase Σ' [] t wtp) in
  let deps := EAstUtils.term_global_deps et in
  expanded (erase_global deps Σ) [] et.
Proof.
  intros hexp Σ'.
  have [wf] : ∥ wf Σ ∥.
  { destruct wfΣ. sq. exact w. }
  eapply (expanded_erases (Σ := (Σ, univs))); tea.
  eapply (erases_erase (Σ := Σ')). cbn.
  eapply (erases_deps_erase (Σ := Σ) univs wfΣ).
Qed.

Lemma expanded_erase_global (cf := config.extraction_checker_flags) deps {Σ: wf_env} :
  PCUICEtaExpand.expanded_global_env Σ ->
  expanded_global_env (erase_global deps Σ).
Proof.
  intros etaΣ.
  unfold erase_global.
  destruct Σ as [Σ map repr]. cbn in *.
  destruct Σ as [Σ wfΣ G isG]. cbn in *. clear G isG.
  destruct Σ as [univs Σ]; cbn in *.
  red. revert wfΣ. red in etaΣ. cbn in *.
  revert deps map repr.
  induction etaΣ; intros deps. cbn. constructor.
  destruct decl as [kn []];
  destruct (KernameSet.mem kn deps) eqn:eqkn; simpl; rewrite eqkn.
  constructor; [eapply IHetaΣ; auto|].
  red. cbn. red. cbn in *.
  set (deps' := KernameSet.union _ _). hidebody deps'.
  set (wfext := make_wf_env_ext _ _ _). hidebody wfext.
  destruct H.
  destruct c as [cst_na [cst_body|] cst_type cst_rel].
  cbn in *.
  eapply expanded_weakening_global. 
  2:{ eapply expanded_erase; tea. }
  set (et := erase _ _ _ _) in *.
  unfold deps'. unfold hidebody. intros x hin.    
  eapply KernameSet.union_spec. right => //.
  now cbn.
  intros.
  eapply IHetaΣ.
  intros map repr wfΣ.
  constructor. eapply IHetaΣ.
  red. cbn => //.
  intros map repr wfΣ.
  eapply IHetaΣ.
Qed.

(* Sanity checks: the [erase] function maximally erases terms *)
Lemma erasable_tBox_value (wfl := Ee.default_wcbv_flags) (Σ : global_env_ext) (wfΣ : wf_ext Σ) t T v :
  forall wt : Σ ;;; [] |- t : T,
  Σ |-p t ▷ v -> erases Σ [] v E.tBox -> ∥ isErasable Σ [] t ∥.
Proof.
  intros.
  depind H.
  eapply Is_type_eval_inv; eauto. eexists; eauto.
Qed.

Lemma erase_eval_to_box (wfl := Ee.default_wcbv_flags) {Σ : wf_env} {univs wfext t v Σ' t' deps} :
  let Σext := make_wf_env_ext Σ univs wfext in
  forall wt : forall Σ0 : global_env_ext, abstract_env_rel' Σext Σ0 -> welltyped Σ0 [] t,
  erase Σext [] t wt = t' ->
  KernameSet.subset (term_global_deps t') deps ->
  erase_global deps Σ = Σ' ->
  PCUICWcbvEval.eval Σ t v ->
  @Ee.eval Ee.default_wcbv_flags Σ' t' E.tBox -> ∥ isErasable Σext [] t ∥.
Proof.
  intros Σext wt.
  intros.
  destruct (erase_correct Σ univs wfext _ _ _ _ _ wt H H0 H1 X) as [ev [eg [eg']]].
  pose proof (Ee.eval_deterministic H2 eg'). subst.
  destruct wfext. destruct (wt _ eq_refl) as [T wt'].
  eapply erasable_tBox_value; eauto.
Qed.

Lemma erase_eval_to_box_eager (wfl := Ee.default_wcbv_flags) {Σ : wf_env} {univs wfext t v Σ' t' deps} :
  let Σext := make_wf_env_ext Σ univs wfext in
  forall wt : forall Σ0 : global_env_ext, abstract_env_rel' Σext Σ0 -> welltyped Σ0 [] t,
  erase Σext [] t wt = t' ->
  KernameSet.subset (term_global_deps t') deps ->
  erase_global deps Σ = Σ' ->
  PCUICWcbvEval.eval Σ t v ->
  @Ee.eval Ee.default_wcbv_flags Σ' t' E.tBox -> t' = E.tBox.
Proof.
  intros Σext wt.
  intros.
  destruct (erase_eval_to_box wt H H0 H1 X H2).
  subst t'.
  destruct (inspect_bool (is_erasableb Σext [] t wt)) eqn:heq.
  - simp erase. rewrite heq.
    simp erase => //.
  - elimtype False.
    destruct (@is_erasableP Σext [] t wt) => //. apply n. now sq.
Qed.

Section EraseGlobalFast.

  Import PCUICEnvironment.

Definition decls_prefix decls (Σ' : global_env) := 
  ∑ Σ'', declarations Σ' = Σ'' ++ decls.

Lemma on_global_decls_prefix {cf} P univs decls decls' :
  on_global_decls P univs (decls ++ decls') ->
  on_global_decls P univs decls'.
Proof.
  induction decls => //.
  intros ha; depelim ha.
  now apply IHdecls.
Qed.

Lemma decls_prefix_wf {decls Σ} : 
  decls_prefix decls Σ -> wf Σ -> wf {| universes := Σ.(universes); declarations := decls |}.
Proof.
  intros [Σ' hd] wfΣ.
  split. apply wfΣ.
  cbn. destruct wfΣ as [_ ond]. rewrite hd in ond.
  now eapply on_global_decls_prefix in ond.
Qed.

Lemma incl_cs_refl cs : cs ⊂_cs cs.
Proof.
  split; [lsets|csets].
Qed.

Lemma weaken_prefix {decls Σ kn decl} :
  decls_prefix decls Σ ->
  wf Σ -> 
  lookup_env {| universes := Σ; declarations := decls |} kn = Some decl ->
  on_global_decl (lift_typing typing) (Σ, universes_decl_of_decl decl) kn decl.
Proof.
  intros prefix wfΣ.
  have wfdecls := decls_prefix_wf prefix wfΣ.
  epose proof (weakening_env_lookup_on_global_env (lift_typing typing) _ Σ kn decl 
    weaken_env_prop_typing wfdecls wfΣ).
  forward X. red; split => //. cbn. apply incl_cs_refl.
  now apply (X wfdecls).
Qed.

(* This version of global environment erasure keeps the same global environment throughout the whole 
   erasure, while folding over the list of declarations. *)

Program Fixpoint erase_global_decls_fast (deps : KernameSet.t) (Σ : wf_env) (decls : global_declarations) 
  (prop : decls_prefix decls Σ.(referenced_impl_env)) : E.global_declarations :=
  match decls with
  | [] => []
  | (kn, ConstantDecl cb) :: decls =>
    if KernameSet.mem kn deps then
      let wfΣext' := make_wf_env_ext Σ (cst_universes cb) _ in
      let cb' := erase_constant_body wfΣext' cb _ in
      let deps := KernameSet.union deps (snd cb') in
      let Σ' := erase_global_decls_fast deps Σ decls _ in
      ((kn, E.ConstantDecl (fst cb')) :: Σ')
    else
      erase_global_decls_fast deps Σ decls _

  | (kn, InductiveDecl mib) :: decls =>
    if KernameSet.mem kn deps then
      let mib' := erase_mutual_inductive_body mib in
      let Σ' := erase_global_decls_fast deps Σ decls _ in
      ((kn, E.InductiveDecl mib') :: Σ')
    else erase_global_decls_fast deps Σ decls _
  end.
Next Obligation.
  epose proof Σ.(referenced_impl_wf).
  sq.
  split. cbn. apply X. cbn.
  eapply decls_prefix_wf in X; tea.
  destruct X as [onu ond]. cbn in ond.
  now depelim ond.
Qed.
Next Obligation.
  epose proof Σ.(referenced_impl_wf).
  sq. eapply (weaken_prefix (kn := kn)) in prop; tea.
  2:{ cbn. rewrite eqb_refl //. }
  apply prop.
Qed.
Next Obligation.
  red. destruct prop as [Σ' ->].
  eexists (Σ' ++ [(kn, ConstantDecl cb)]); rewrite -app_assoc //.
Qed.
Next Obligation.
  red. destruct prop as [Σ' ->].
  eexists (Σ' ++ [(kn, ConstantDecl cb)]); rewrite -app_assoc //.
Qed.
Next Obligation.
  red. destruct prop as [Σ' ->].
  eexists (Σ' ++ [(kn, _)]); rewrite -app_assoc //.
Qed.
Next Obligation.
  red. destruct prop as [Σ' ->].
  eexists (Σ' ++ [(kn, _)]); rewrite -app_assoc //.
Qed.

Import PCUICAst PCUICEnvironment.

Lemma wf_lookup Σ kn d suffix g : 
  wf Σ ->
  declarations Σ = suffix ++ (kn, d) :: g ->
  lookup_env Σ kn = Some d.
Proof.
  unfold lookup_env.
  intros [_ ond] eq. rewrite eq in ond |- *.
  move: ond; clear.
  induction suffix.
  - cbn. rewrite eqb_refl //.
  - cbn. intros ond.
    depelim ond. cbn. red in f.
    eapply Forall_app in f as []. depelim H0. cbn in H0.
    destruct (eqb_spec kn kn0); [contradiction|].
    now apply IHsuffix.
Qed.

Definition add_suffix suffix Σ :=
  {| universes := Σ.(universes); declarations := suffix ++ Σ.(declarations) |}.

Lemma eta_global_env Σ : Σ = {| universes := Σ.(universes); declarations := Σ.(declarations) |}.
Proof. now destruct Σ. Qed.
  
Lemma add_suffix_cons d suffix Σ : add_suffix (d :: suffix) Σ = add_global_decl (add_suffix suffix Σ) d. 
Proof. reflexivity. Qed.

Lemma global_erased_with_deps_weaken_prefix suffix Σ Σ' kn : 
  wf (add_suffix suffix Σ) ->
  global_erased_with_deps Σ Σ' kn ->
  global_erased_with_deps (add_suffix suffix Σ) Σ' kn.
Proof.
  induction suffix.
  - unfold add_suffix; cbn. intros wf hg.
    now rewrite -eta_global_env.
  - rewrite add_suffix_cons. intros wf H.
    destruct a as [kn' d]. eapply global_erases_with_deps_weaken => //.
    apply IHsuffix => //.
    destruct wf as [onu ond]. now depelim ond.
Qed.

Definition build_wf_env_from_env {cf : checker_flags} (Σ : global_env) (wfΣ : ∥ PCUICTyping.wf Σ ∥) : wf_env := 
  let Σm := EnvMap.of_global_env Σ.(declarations) in
  {| wf_env_referenced := {| referenced_impl_env := Σ; referenced_impl_wf := wfΣ |} ;
     wf_env_map := Σm;
     wf_env_map_repr := EnvMap.repr_global_env Σ.(declarations);
 |}.

(* Using weakening it is trivial to show that a term found to be erasable in Σ 
  will be found erasable in any well-formed extension. The converse is not so trivial:
  some valid types in the extension are not valid in the restricted global context.
  So, we will rather show that the erasure function is invariant under extension. *) 

Lemma isErasable_irrel_global_env {Σ Σ' : global_env_ext} {Γ t} :
  wf Σ ->
  extends_decls Σ' Σ ->
  Σ.2 = Σ'.2 ->
  isErasable Σ' Γ t -> isErasable Σ Γ t.
Proof.
  unfold isErasable.
  intros wfΣ ext eqext [T [ht isar]].
  destruct Σ as [Σ decl], Σ' as [Σ' decl']. cbn in eqext; subst decl'.
  exists T; split.
  eapply (env_prop_typing weakening_env (Σ', decl)) => //=.
  eapply extends_decls_wf; tea.
  now eapply extends_decls_extends.
  destruct isar as [|s]; [left|right] => //.
  destruct s as [u [Hu isp]].
  exists u; split => //.
  eapply (env_prop_typing weakening_env (Σ', decl)) => //=.
  eapply extends_decls_wf; tea.
  now eapply extends_decls_extends.
Qed. 

(** As erasure relies on reduction of types to check the erasability of types and proofs, we also show 
  that safe reduction is invariant under extension.
  This cannot be shown using only the correctness and completeness lemmas of reduction as 
  in different enviroments we might find different declarations and hence produce different 
  reduced terms. Morally we could hope that a parametericity style lemma could prove this: 
  for two environments that are obsevationally equal on the declared constants/inductives 
  appearing in a well-typed terms, the output of reduction/inference is equal. 
  However parametricity would not directly allow us to restrict to observational
  equivalence only on declared constants. *)

Definition reduce_stack_eq {cf} {fl} {X_type : abstract_env_ext_impl} {X : X_type.π1} Γ t π wi : reduce_stack fl X_type X Γ t π wi = ` (reduce_stack_full fl X_type X Γ t π wi).
Proof.
  unfold reduce_stack. destruct reduce_stack_full => //.
Qed.

Definition same_principal_type {cf}
  {X_type : abstract_env_ext_impl} {X : X_type.π1}
  {X_type' : abstract_env_ext_impl} {X' : X_type'.π1}
  {Γ : context} {t} (p : PCUICSafeRetyping.principal_type X_type X Γ t) (p' : PCUICSafeRetyping.principal_type X_type' X' Γ t) :=
  p.π1 = p'.π1.

Definition Hlookup {cf} (X_type : abstract_env_ext_impl) (X : X_type.π1)
  (X_type' : abstract_env_ext_impl) (X' : X_type'.π1) := 
  forall Σ : global_env_ext, abstract_env_ext_rel X Σ ->
  forall Σ' : global_env_ext, abstract_env_ext_rel X' Σ' ->
  forall kn decl decl',
    lookup_env Σ kn = Some decl ->
    lookup_env Σ' kn = Some decl' ->
    abstract_env_lookup X kn = abstract_env_lookup X' kn.

Lemma welltyped_mkApps_inv {cf} {Σ : global_env_ext} Γ f args :  ∥ wf Σ ∥ ->
  welltyped Σ Γ (mkApps f args) -> welltyped Σ Γ f /\ Forall (welltyped Σ Γ) args.
Proof.
  intros wf (A & HA). sq. eapply inversion_mkApps in HA as (? & ? & ?).
  split. eexists; eauto.
  induction t0 in f |- *; econstructor; eauto; econstructor; eauto.
Qed.

Section infer_irrel.
  Context {cf} {nor : normalizing_flags} {X_type : abstract_env_ext_impl} {X : X_type.π1}
    {X_type' : abstract_env_ext_impl} {X' : X_type'.π1}.
  Context (hl : Hlookup X_type X X_type' X').
  
  Definition same_prod (Γ : context) {T}
     (pf : ∑ (na' : aname) (A' B' : term), forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> ∥ Σ ;;; Γ ⊢ T ⇝ tProd na' A' B' ∥)
    (pf' : ∑ (na' : aname) (A' B' : term), forall Σ : global_env_ext, abstract_env_ext_rel X' Σ -> ∥ Σ ;;; Γ ⊢ T ⇝ tProd na' A' B' ∥) :=
    let '(na; A; B; _) := pf in
    let '(na'; A'; B'; _) := pf' in
    (na, A, B) = (na', A', B').
  
  Lemma same_prod_last (Γ : context) {T}
    (pf : ∑ (na' : aname) (A' B' : term), forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> ∥ Σ ;;; Γ ⊢ T ⇝ tProd na' A' B' ∥)
    (pf' : ∑ (na' : aname) (A' B' : term), forall Σ : global_env_ext, abstract_env_ext_rel X' Σ -> ∥ Σ ;;; Γ ⊢ T ⇝ tProd na' A' B' ∥) 
    : same_prod Γ pf pf' -> pf.π2.π2.π1 = pf'.π2.π2.π1.
  Proof.
    destruct pf as [na [A [B prf]]].
    destruct pf' as [na' [A' [B' prf']]].
    cbn. congruence.
  Qed.
  
  Lemma same_reduce_stack {Γ t π} {fl} (wi : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> welltyped Σ Γ (PCUICPosition.zip (t, π)))
    (wi' : forall Σ : global_env_ext, abstract_env_ext_rel X' Σ -> welltyped Σ Γ (PCUICPosition.zip (t, π))) :
    reduce_stack fl X_type X Γ t π wi = reduce_stack fl X_type' X' Γ t π wi'.
  Proof.
    rewrite !reduce_stack_eq.
    revert X_type' X' wi' hl.
    apply_funelim (reduce_stack_full fl X_type X Γ t π wi).
    intros.
    rewrite reduce_stack_full_unfold_eq.
    set (rec := (fun t' π' => _)).
    simp _reduce_stack.
    unfold reduce_stack_full_unfold. simp _reduce_stack.
    set (rec' := (fun t' π' => _)).
    assert (ih : forall (t' : term) (π' : PCUICPosition.stack)
      (hr : forall Σ : global_env_ext,
            abstract_env_ext_rel X Σ -> R Σ Γ (t', π') (t0, π0))
      (hr' : forall Σ : global_env_ext,
      abstract_env_ext_rel X' Σ -> R Σ Γ (t', π') (t0, π0)),
      ` (rec t' π' hr) = ` (rec' t' π' hr')).
    { intros. unshelve eapply H. exact hl. } clear H.
    clearbody rec rec'.
    Ltac reccall ih rec rec' :=
      match goal with
      [ |- context [rec ?t ?π ?hr] ] =>
        match goal with
        [ |- context [rec' ?t' ?π' ?hr'] ] =>
          let H := fresh in 
          assert (H := ih t π hr hr');
          set (call := rec t π hr) in *;
          set (call' := rec' t π' hr') in *;
          clearbody call call';
          destruct call, call'; cbn in H |- *; subst; auto
          end
      end.
    destruct red_viewc.
    - cbn. simp _reduce_stack.
      destruct (PCUICNormal.RedFlags.zeta fl); simp _reduce_stack. 2:reflexivity.
      destruct PCUICSafeReduce.inspect => //.
      destruct x as [[? [?|] ?]|] => //.
      simp _reduce_stack. simpl.
      reccall ih rec rec'.
      cbn. bang.
    - simp _reduce_stack.
      destruct (PCUICNormal.RedFlags.zeta fl); simp _reduce_stack. 2:reflexivity.
      simpl.
      reccall ih rec rec'.
    - cbn.
      destruct (PCUICNormal.RedFlags.delta fl); simp _reduce_stack. 2:reflexivity.
      assert (abstract_env_lookup X c = abstract_env_lookup X' c).
      { clear -hl h wi'.
        epose proof (abstract_env_ext_exists X) as [[Σ wfΣ]].
        epose proof (abstract_env_ext_wf X wfΣ) as [hwfΣ].
        specialize (h _ wfΣ).
        epose proof (abstract_env_ext_exists X') as [[Σ' wfΣ']].
        epose proof (abstract_env_ext_wf X' wfΣ') as [hwfΣ'].
        specialize (wi' _ wfΣ').
        eapply welltyped_zipc_zipp in h. 2:pcuic. cbn in h.
        unfold PCUICPosition.zipp in *.
        destruct (PCUICPosition.decompose_stack π0) eqn:decomp; eauto.
        assert (∥ wf Σ ∥). sq. apply hwfΣ.
        eapply (welltyped_mkApps_inv (Σ := Σ) _ _ _ H) in h as [].
        eapply welltyped_zipc_zipp in wi'. 2:pcuic. cbn in wi'.
        unfold PCUICPosition.zipp in *.
        destruct (PCUICPosition.decompose_stack π0) eqn:decomp'; eauto.
        assert (∥ wf Σ' ∥). sq. apply hwfΣ'.
        eapply (welltyped_mkApps_inv (Σ := Σ') _ _ _ H2) in wi' as [].
        destruct H0, H3.
        eapply inversion_Const in X0 as [decl [_ [Hdecl _]]]; eauto.
        eapply inversion_Const in X1 as [decl' [_ [Hdecl' _]]]; eauto. }
      destruct PCUICSafeReduce.inspect => //.
      destruct PCUICSafeReduce.inspect => //.
      destruct x as [[]|] => //; simp _reduce_stack. 2-3:bang.
      destruct x0 as [[]|] => //; simp _reduce_stack. 2-3:bang.
      assert (c0 = c1).
      { congruence. } subst c1.
      destruct c0 as [? [|] ? ?]; simp _reduce_stack.
      simpl. reccall ih rec rec'. now cbn.
    - simp _reduce_stack.
      simpl.
      reccall ih rec rec'.
    - simp _reduce_stack.
      destruct PCUICSafeReduce.inspect => //. destruct x.
      simp _reduce_stack. simpl.
      reccall ih rec rec'. now cbn.
    - simp _reduce_stack.
      destruct (PCUICNormal.RedFlags.fix_ fl); simp _reduce_stack. 2:reflexivity.
      destruct PCUICSafeReduce.inspect; simp _reduce_stack.
      destruct x; simp _reduce_stack. 2:reflexivity.
      destruct p. simp _reduce_stack.
      destruct PCUICSafeReduce.inspect; simp _reduce_stack.
      destruct x; simp _reduce_stack. 2:reflexivity.
      destruct p as [[? ?] ?]. simp _reduce_stack.
      Ltac reccall' ih rec rec' :=
        match goal with
        [ |- context [rec ?t ?π ?hr] ] =>
          match goal with
          [ |- context [rec' ?t' ?π' ?hr'] ] =>
            let H := fresh in 
            assert (H := ih t π hr hr');
            set (call := rec t π hr) in *;
            set (call' := rec' t π' hr') in *
            end
        end.
      reccall' ih rec rec'.
      destruct PCUICSafeReduce.inspect; simp _reduce_stack.
      destruct PCUICSafeReduce.inspect; simp _reduce_stack.
      subst x. subst x0.
      match goal with
        [ |- context [@exist ?A ?P call ?e] ] =>
          match goal with
          [ |- context [@exist ?A' ?P' call' ?e'] ] =>
            set (ex := @exist A P call e);
            set (ex' := @exist A' P' call' e');
            clearbody ex ex'
          end
      end.
      destruct ex as [[? ?] eq].
      destruct ex' as [[? ?] eq'].
      assert (x = x0). { subst call call'. move: eq eq'.
        reccall ih rec rec'. congruence. }
      subst x0. destruct x.
      simp _reduce_stack.
      destruct (construct_viewc); simp _reduce_stack.
      * destruct PCUICSafeReduce.inspect; simp _reduce_stack. 
        destruct x as []; simp _reduce_stack.
        simpl. subst call call'.
        reccall ih rec rec'.
      * destruct PCUICSafeReduce.inspect; simp _reduce_stack.
        destruct x as []; simp _reduce_stack. reflexivity.
    - simp _reduce_stack.
      destruct (PCUICNormal.RedFlags.iota fl); simp _reduce_stack. 2:reflexivity.
      reccall' ih rec rec'.
      destruct PCUICSafeReduce.inspect; simp _reduce_stack.
      destruct PCUICSafeReduce.inspect; simp _reduce_stack.
      subst x. subst x0.
      match goal with
        [ |- context [@exist ?A ?P call ?e] ] =>
          match goal with
          [ |- context [@exist ?A' ?P' call' ?e'] ] =>
            set (ex := @exist A P call e);
            set (ex' := @exist A' P' call' e');
            clearbody ex ex'
          end
      end.
      destruct ex as [[? ?] eq].
      destruct ex' as [[? ?] eq'].
      assert (x = x0). { subst call call'. move: eq eq'.
        reccall ih rec rec'. congruence. }
      subst x0. destruct x.
      simp _reduce_stack.
      destruct PCUICSafeReduce.inspect; simp _reduce_stack. 
      destruct x as []; simp _reduce_stack.
      destruct cc_viewc; simp _reduce_stack. 3:reflexivity.
      destruct PCUICSafeReduce.inspect; simp _reduce_stack.
      destruct x as []; simp _reduce_stack.
      simpl. subst call call'.
      reccall ih rec rec'. bang.
      destruct PCUICSafeReduce.inspect; simp _reduce_stack.
      destruct x as []; simp _reduce_stack. 2:bang.
      destruct p0; simp _reduce_stack. simpl.
      subst call call'; reccall ih rec rec'.
    - destruct p as [[] ?]. simp _reduce_stack. simpl.
      destruct (PCUICNormal.RedFlags.iota fl); simp _reduce_stack. 2:reflexivity.
      reccall' ih rec rec'.
      destruct PCUICSafeReduce.inspect; simp _reduce_stack.
      destruct PCUICSafeReduce.inspect; simp _reduce_stack.
      subst x. subst x0.
      match goal with
        [ |- context [@exist ?A ?P call ?e] ] =>
          match goal with
          [ |- context [@exist ?A' ?P' call' ?e'] ] =>
            set (ex := @exist A P call e);
            set (ex' := @exist A' P' call' e');
            clearbody ex ex'
          end
      end.
      destruct ex as [[? ?] eq].
      destruct ex' as [[? ?] eq'].
      assert (x = x0). { subst call call'. move: eq eq'.
        reccall ih rec rec'. congruence. }
      subst x0. destruct x.
      simp _reduce_stack.
      destruct PCUICSafeReduce.inspect; simp _reduce_stack. 
      destruct x as []; simp _reduce_stack.
      destruct cc0_viewc; simp _reduce_stack. 3:reflexivity.
      destruct PCUICSafeReduce.inspect; simp _reduce_stack.
      destruct x as []; simp _reduce_stack.
      simpl. subst call call'.
      reccall ih rec rec'. bang.
      destruct PCUICSafeReduce.inspect; simp _reduce_stack.
      destruct x as []; simp _reduce_stack. 2:bang.
      destruct p; simp _reduce_stack. simpl.
      subst call call'; reccall ih rec rec'.
    - simpl. reflexivity.
  Qed.

  Lemma same_hnf {Γ t} (wi : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> welltyped Σ Γ t)
    (wi' : forall Σ : global_env_ext, abstract_env_ext_rel X' Σ -> welltyped Σ Γ t) :
    hnf Γ t wi = hnf Γ t wi'.
  Proof.
    unfold hnf. unfold reduce_term.
    f_equal. apply same_reduce_stack.
  Qed.

  Definition same_typing_result_comp {A B} (P : A -> B -> Prop) (c : typing_result_comp A) (c' : typing_result_comp B) : Prop := 
    match c, c' with
    | Checked_comp a, Checked_comp a' => P a a'
    | TypeError_comp e ne, TypeError_comp e' na' => True
    | _, _ => False
    end.

  Definition same_prod_comp {Γ T}
     (pf : typing_result_comp (∑ (na' : aname) (A' B' : term), 
       forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> ∥ Σ ;;; Γ ⊢ T ⇝ tProd na' A' B' ∥))
    (pf' : typing_result_comp (∑ (na' : aname) (A' B' : term),
       forall Σ : global_env_ext, abstract_env_ext_rel X' Σ -> ∥ Σ ;;; Γ ⊢ T ⇝ tProd na' A' B' ∥)) :=
    same_typing_result_comp (same_prod Γ) pf pf'.

  Lemma reduce_to_prod_irrel {Γ t}
    (wi : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> welltyped Σ Γ t)
    (wi' : forall Σ : global_env_ext, abstract_env_ext_rel X' Σ -> welltyped Σ Γ t) : 
    same_prod_comp (reduce_to_prod Γ t wi) (reduce_to_prod Γ t wi').
  Proof.
    unfold reduce_to_prod.
    destruct view_prodc; simp reduce_to_prod.
    red. cbn. auto.
    epose proof (same_hnf wi wi').
    set (e := eq_refl). set (e' := eq_refl).
    set (v := view_prodc (hnf Γ t wi)). clearbody v.
    set (v' := view_prodc (hnf Γ t wi')). clearbody v'.
    clearbody e e'.
    unfold reduce_to_prod_clause_1_clause_2_clause_1.
    destruct v. destruct v'. cbn. now noconf H. cbn.
    noconf H. now cbn in n0.
    destruct v'. cbn. subst t0. now cbn in n0.
    subst t1. cbn. auto.
  Qed.
  
  Lemma infer_as_prod_irrel {Γ t} 
    (wf : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> ∥ wf_local Σ Γ ∥)
    (wf' : forall Σ : global_env_ext, abstract_env_ext_rel X' Σ -> ∥ wf_local Σ Γ ∥)
    (wi : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> welltyped Σ Γ t)
    (wi' : forall Σ : global_env_ext, abstract_env_ext_rel X' Σ -> welltyped Σ Γ t) 
    hp hp' : same_prod Γ (infer_as_prod X_type X Γ t wf wi hp) (infer_as_prod X_type' X' Γ t wf' wi' hp').
  Proof.
    unfold same_prod.
    unfold infer_as_prod.
    destruct reduce_to_prod as [[na [A [B hr]]]|] eqn:h. 2:bang.
    destruct (reduce_to_prod _ _ wi') as [[na' [A' [B' hr']]]|] eqn:h'. 2:bang.
    pose proof (reduce_to_prod_irrel wi wi').
    rewrite h h' in H. now cbn in H.
  Qed.

  Definition same_sort_comp {cf} {nor : normalizing_flags} 
    {X_type : abstract_env_ext_impl} {X : X_type.π1}
    {X_type' : abstract_env_ext_impl} {X' : X_type'.π1}
    {Γ : context} {t t'}
    (pf : typing_result_comp
      (∑ u, forall Σ0 : global_env_ext, abstract_env_ext_rel X Σ0 -> ∥ Σ0 ;;; Γ ⊢ t ⇝ tSort u ∥))
    (pf' : typing_result_comp 
      (∑ u, forall Σ0 : global_env_ext, abstract_env_ext_rel X' Σ0 -> ∥ Σ0 ;;; Γ ⊢ t' ⇝ tSort u ∥)) :=
    same_typing_result_comp (fun x y => x.π1 = y.π1) pf pf'.

  Lemma reduce_to_sort_irrel {Γ t t'} (e : t = t')
    (wi : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> welltyped Σ Γ t)
    (wi' : forall Σ : global_env_ext, abstract_env_ext_rel X' Σ -> welltyped Σ Γ t') : 
    same_sort_comp (reduce_to_sort Γ t wi) (reduce_to_sort Γ t' wi').
  Proof.
    destruct e.
    unfold reduce_to_sort.
    destruct (view_sortc); simp reduce_to_sort.
    now cbn.
    epose proof (same_hnf wi wi').
    do 2 match goal with
    |- context [@eq_refl ?A ?t] => let e := fresh "e" in set(e := @eq_refl A t)
    end.
    set (v := view_sortc (hnf Γ t wi)). clearbody v.
    set (v' := view_sortc (hnf Γ t wi')). clearbody v'.
    clearbody e e0.
    unfold reduce_to_sort_clause_1_clause_2_clause_1.
    destruct v. destruct v'. cbn. now noconf H. cbn.
    noconf H. now cbn in n0.
    destruct v'. cbn. subst t0. now cbn in n0.
    subst t1. cbn. auto.
  Qed.

  Lemma infer_as_sort_irrel {Γ t} 
    (wf : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> ∥ wf_local Σ Γ ∥)
    (wf' : forall Σ : global_env_ext, abstract_env_ext_rel X' Σ -> ∥ wf_local Σ Γ ∥)
    (wi : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> well_sorted Σ Γ t)
    (wi' : forall Σ : global_env_ext, abstract_env_ext_rel X' Σ -> well_sorted Σ Γ t) 
    hp hp' : hp.π1 = hp'.π1 -> (infer_as_sort X_type X wf wi hp).π1 = (infer_as_sort X_type' X' wf' wi' hp').π1.
  Proof.
    unfold infer_as_sort.
    unfold PCUICSafeRetyping.principal_type_type.
    set (obl := fun Σ wfΣ => PCUICSafeRetyping.infer_as_sort_obligation_1 _ _ _ _ _ _ _ Σ wfΣ).
    set (obl' := fun Σ wfΣ => PCUICSafeRetyping.infer_as_sort_obligation_1 _ _ _ _ _ _ _ Σ wfΣ).
    clearbody obl obl'.
    destruct reduce_to_sort as [[s hr]|] eqn:h. 2:bang.
    destruct (reduce_to_sort _ hp'.π1 _) as [[s' hr']|] eqn:h'. 2:bang.
    cbn. destruct hp, hp'; cbn; intros <-.
    cbn -[reduce_to_sort] in *.
    epose proof (reduce_to_sort_irrel eq_refl obl obl').
    rewrite h h' in H. now cbn in H.
  Qed.

  Definition same_ind_comp {Γ t t'} 
    (pf : typing_result_comp 
    (∑ (i : inductive) (u : Instance.t) (l : list term),
         forall Σ : global_env_ext,
         abstract_env_ext_rel X Σ ->
         ∥ Σ ;;; Γ ⊢ t ⇝  mkApps (tInd i u) l ∥))
    (pf' : typing_result_comp
    (∑ (i : inductive) (u : Instance.t) (l : list term),
    forall Σ : global_env_ext,
    abstract_env_ext_rel X' Σ -> ∥ Σ ;;; Γ ⊢ t' ⇝ mkApps (tInd i u) l ∥)) :=
 same_typing_result_comp (fun x y => (x.π1, x.π2.π1, x.π2.π2.π1) = (y.π1, y.π2.π1, y.π2.π2.π1)) pf pf'.
 

  Lemma elim_inspect {A} (x : A) (P : { y : A | y = x } -> Type) :
    (forall y (e : y = x), P (exist y e)) -> P (PCUICSafeReduce.inspect x).
  Proof.
    intros hp. unfold PCUICSafeReduce.inspect. apply hp.
  Qed.

 Lemma reduce_to_ind_irrel {Γ t t'} (e : t = t')
  (wi : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> welltyped Σ Γ t)
  (wi' : forall Σ : global_env_ext, abstract_env_ext_rel X' Σ -> welltyped Σ Γ t') : 
  same_ind_comp (reduce_to_ind Γ t wi) (reduce_to_ind Γ t' wi').
  Proof.
    subst t'.
    simp reduce_to_ind.
    eapply elim_inspect => [[f args] eq].
    simp reduce_to_ind.
    destruct view_indc => //.
    simp reduce_to_ind.
    epose proof (same_reduce_stack (fl := PCUICNormal.RedFlags.default) (π := []) wi wi').
    eapply elim_inspect => [[f' π'] eq']. simp reduce_to_ind.
    eapply elim_inspect => [[f'' π''] eq'']. simp reduce_to_ind.
    rewrite -eq' -eq'' in H. noconf H.
    destruct view_indc => //. simp reduce_to_ind.
    eapply elim_inspect => [[app st] eqst]. simp reduce_to_ind => //.
  Qed.

  Definition same_typing_result {A B} (P : A -> B -> Prop) (c : typing_result A) (c' : typing_result B) : Prop := 
    match c, c' with
    | Checked a, Checked a' => P a a'
    | TypeError e, TypeError e' => True
    | _, _ => False
    end.
  
  Lemma same_lookup_ind_decl ind :
    abstract_env_lookup X (inductive_mind ind) = abstract_env_lookup X' (inductive_mind ind) ->
    same_typing_result (fun x y => (x.π1, x.π2.π1) = (y.π1, y.π2.π1)) (lookup_ind_decl X_type X ind) (lookup_ind_decl X_type' X' ind).
  Proof. 
    intros eq.
    funelim (lookup_ind_decl X_type X ind); simp lookup_ind_decl;
    eapply elim_inspect; intros opt e'.
    - rewrite -e -e' in eq. destruct opt; noconf eq => //.
    - rewrite -e in eq. destruct opt => //. exfalso; congruence.
    - destruct opt as [[]|]. cbn. congruence.
      rewrite -look -e' in eq. noconf eq.
      simp lookup_ind_decl.
      eapply elim_inspect; intros opt e''.
      destruct opt => //. simp lookup_ind_decl. cbn. congruence.
      cbn. congruence. cbn. congruence.
    - destruct opt as [[]|] => //. simp lookup_ind_decl.
      eapply elim_inspect; intros opt e''.
      destruct opt => //. simp lookup_ind_decl. cbn. congruence.
  Qed.    

End infer_irrel.

Lemma infer_irrel {cf} {nor : normalizing_flags} {X_type : abstract_env_ext_impl} {X : X_type.π1}
  {X_type' : abstract_env_ext_impl} {X' : X_type'.π1}
  (hl : Hlookup X_type X X_type' X')
  {Γ t}
  (wf : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> ∥ wf_local Σ Γ ∥)
  (wf' : forall Σ : global_env_ext, abstract_env_ext_rel X' Σ -> ∥ wf_local Σ Γ ∥)
  (wi : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> wellinferred Σ Γ t)
  (wi' : forall Σ : global_env_ext, abstract_env_ext_rel X' Σ -> wellinferred Σ Γ t) :
  (infer X_type X Γ wf t wi).π1 = (infer X_type' X' Γ wf' t wi').π1.
Proof.
  revert X_type' X' hl wf' wi'. apply_funelim (infer X_type X Γ wf t wi).
  all:intros.
  all:try bang.
  - now cbn.
  - simpl.
    cbn. f_equal. f_equal; unfold PCUICSafeRetyping.principal_sort_sort.
    set (obl := fun a b => _).
    set (obl' := fun a b => _).
    set (obl'' := fun a b => _).
    set (obl''' := fun a b => _).
    cbn. eapply infer_as_sort_irrel => //. now eapply H.
    eapply infer_as_sort_irrel => //. now eapply H0.
  - cbn. f_equal.
    unfold PCUICSafeRetyping.principal_type_type. apply H; eauto.
  - cbn. f_equal. apply H; eauto.
  - cbn. f_equal.
    unfold PCUICSafeRetyping.principal_type_type.
    set (obl1 := (fun Σ wfΣ => PCUICSafeRetyping.infer_obligations_obligation_14 _ _ _ _ _ _ _ _ Σ wfΣ)).
    set (obl2 := (fun Σ wfΣ => PCUICSafeRetyping.infer_obligations_obligation_13 _ _ _ _ _ _ _ _ Σ wfΣ)).
    set (t' := (infer _ _ _ _ _ _)) in *.
    set (obl3 := (fun Σ wfΣ => PCUICSafeRetyping.infer_obligations_obligation_14 _ _ _ _ _ _ _ _ Σ wfΣ)).
    set (obl4 := (fun Σ wfΣ => PCUICSafeRetyping.infer_obligations_obligation_13 _ _ _ _ _ _ _ _ Σ wfΣ)).
    set (t'' := (infer X_type' _ _ _ _ _)) in *.
    clearbody obl3 obl4.
    assert (t'.π1 = t''.π1).
    { unfold t', t''. apply H; eauto. }
    clearbody t''. clearbody obl1 obl2. clearbody t'.
    destruct t', t''. cbn in H0. subst x0. cbn.
    eapply same_prod_last.
    now eapply infer_as_prod_irrel.
  - unfold infer. rewrite Heq /= //.
  - assert (abstract_env_lookup X cst = abstract_env_lookup X' cst).
    { epose proof (abstract_env_ext_exists X) as [[Σ wfΣ]].
      epose proof (abstract_env_ext_wf X wfΣ) as [hwfΣ].
      specialize (wt _ wfΣ).
      epose proof (abstract_env_ext_exists X') as [[Σ' wfΣ']].
      epose proof (abstract_env_ext_wf X' wfΣ') as [hwfΣ'].
      specialize (wi' _ wfΣ').
      depelim wt. inv X0.
      depelim wi'. inv X0.
      eapply hl; tea. }
    move: e Heq.
    cbn -[infer].
    rewrite H. unfold infer.
    now intros e -> => /=.
  - destruct decl as [decl [body hd]].
    cbn -[infer].
    simp infer.
    assert (abstract_env_lookup X (inductive_mind ind) = abstract_env_lookup X' (inductive_mind ind)).
    { epose proof (abstract_env_ext_exists X) as [[Σ wfΣ]].
      epose proof (abstract_env_ext_wf X wfΣ) as [hwfΣ].
      epose proof (abstract_env_ext_exists X') as [[Σ' wfΣ']].
      epose proof (abstract_env_ext_wf X' wfΣ') as [hwfΣ'].
      destruct (wi' _ wfΣ'). inv X0.
      pose proof (hd _ wfΣ).
      destruct isdecl, H0.
      unfold declared_minductive in *.
      now eapply (hl Σ wfΣ Σ' wfΣ'). }        
    destruct (PCUICSafeReduce.inspect (lookup_ind_decl _ X' ind)).
    move: (same_lookup_ind_decl _ H). rewrite -{1}e0 -{1}e.
    destruct x => //. cbn. cbn.
    destruct a as [decl' [body' ?]]; cbn.
    congruence.
  - cbn -[infer].
    simp infer.
    assert (abstract_env_lookup X (inductive_mind ind) = abstract_env_lookup X' (inductive_mind ind)).
    { epose proof (abstract_env_ext_exists X) as [[Σ wfΣ]].
      epose proof (abstract_env_ext_wf X wfΣ) as [hwfΣ].
      epose proof (abstract_env_ext_exists X') as [[Σ' wfΣ']].
      epose proof (abstract_env_ext_wf X' wfΣ') as [hwfΣ'].
      destruct (wi' _ wfΣ'). inv X0.
      pose proof (wt _ wfΣ).
      destruct isdecl, H0. inv X0.
      destruct H1. destruct isdecl as [[] ?].
      unfold declared_minductive in *.
      now eapply (hl Σ wfΣ Σ' wfΣ'). }        
    destruct (PCUICSafeReduce.inspect (lookup_ind_decl _ X' ind)).
    move: (same_lookup_ind_decl _ H). rewrite -{1}e1 -{1}e.
    destruct x => //.
    destruct a as [decl' [body' ?]] => //.
    simp infer.
    eapply elim_inspect; intros o eq. cbn in eq.
    destruct o => //. simp infer. cbn. destruct decl as [decl [body ?]]; cbn.
    intros [=]. subst decl' body'. cbn in e0.
    congruence.
    cbn. bang.
  - cbn -[infer].
    simp infer.
    set (t' := (infer X_type _ _ _ _ _)) in *.
    specialize (Hind X_type' X' hl).
    set (obl4 := (fun Σ wfΣ => PCUICSafeRetyping.infer_obligations_obligation_27 X_type _ _ _ _ _ _ _ _ _ Σ wfΣ)) in *.
    set (obl3 := (fun Σ wfΣ => PCUICSafeRetyping.infer_obligations_obligation_27 X_type' _ _ _ _ _ _ _ _ _ Σ wfΣ)).
    set (obl1 := (fun Σ wfΣ => PCUICSafeRetyping.infer_obligations_obligation_26 X_type _ _ _ _ _ _ _ Σ wfΣ)) in *; cbn in obl1.
    set (obl2 := (fun Σ wfΣ => PCUICSafeRetyping.infer_obligations_obligation_26 X_type' _ _ _ _ _ _ _ Σ wfΣ)) in *; cbn in obl2.
    specialize (Hind wf' obl2).
    set (t'' := (infer X_type' _ _ _ _ _)) in *.
    cbn in obl3. unfold PCUICSafeRetyping.principal_type_type in obl3 |- *.
    eapply elim_inspect => y eq.
    epose proof (reduce_to_ind_irrel hl Hind obl4 obl3).
    rewrite -e -eq in H.
    destruct y => //. destruct a as [ind' [u' [l' ?]]] => //. cbn.
    destruct indargs as [ind [u [l ?]]]; cbn. now cbn in H; noconf H.
  - cbn -[infer].
    simp infer.
    set (t' := (infer X_type _ _ _ _ _)) in *.
    specialize (Hind X_type' X' hl).
    unfold PCUICSafeRetyping.principal_type_type in *.
    eapply elim_inspect => y eq.
    assert (abstract_env_lookup X (inductive_mind p.(proj_ind)) = abstract_env_lookup X' (inductive_mind p.(proj_ind))).
    { epose proof (abstract_env_ext_exists X) as [[Σ wfΣ]].
      epose proof (abstract_env_ext_wf X wfΣ) as [hwfΣ].
      epose proof (abstract_env_ext_exists X') as [[Σ' wfΣ']].
      epose proof (abstract_env_ext_wf X' wfΣ') as [hwfΣ'].
      destruct (wi' _ wfΣ'). inv X0.
      pose proof (wt _ wfΣ).
      inv H1. inv X0. destruct H as [[[]]]. destruct H1 as [[[]]].
      unfold declared_minductive in *.
      now eapply (hl Σ wfΣ Σ' wfΣ'). } 
    move: (same_lookup_ind_decl _ H). rewrite -{1}eq -{1}e.
    destruct y => //.
    destruct a as [decl [body ?]], d as [decl' [body' ?]].
    intros h. cbn in h. noconf h.
    simp infer.
    eapply elim_inspect => nth eq'.
    cbn in eq', e0. destruct nth as [[]|] => //.
    simp infer.
    set (obl4 := (fun Σ wfΣ => PCUICSafeRetyping.infer_obligations_obligation_33 X_type _ _ _ _ _ _ _ Σ wfΣ)) in *.
    set (obl3 := (fun Σ wfΣ => PCUICSafeRetyping.infer_obligations_obligation_33 X_type' _ _ _ _ _ _ _ Σ wfΣ)).
    set (obl1 := (fun Σ wfΣ => PCUICSafeRetyping.infer_obligations_obligation_32 X_type _ _ _ _ _ Σ wfΣ)) in *; cbn in obl1.
    set (obl2 := (fun Σ wfΣ => PCUICSafeRetyping.infer_obligations_obligation_32 X_type' _ _ _ _ _ Σ wfΣ)) in *; cbn in obl2.
    specialize (Hind wf' obl2).
    set (t'' := (infer X_type' _ _ _ _ _)) in *.
    cbn in obl3. unfold PCUICSafeRetyping.principal_type_type in obl3 |- *.
    eapply elim_inspect => rind eqrind.
    epose proof (reduce_to_ind_irrel hl Hind obl4 obl3).
    rewrite -e1 -eqrind in H0.
    destruct rind => //. destruct a as [ind' [u' [l' ?]]] => //. cbn.
    destruct indargs as [ind'' [u [l ?]]]; cbn. cbn in H0; noconf H0.
    clear -e0 eq'. destruct pdecl. rewrite -e0 in eq'. noconf eq'. now cbn.
    exfalso.
    clear -e0 eq'. congruence.
  - cbn -[infer]. unfold infer; rewrite Heq /= //.
  - cbn -[infer]. unfold infer; rewrite Heq /= //.
Qed.

Lemma sort_of_type_irrel
  {cf} {nor : normalizing_flags} {X_type : abstract_env_ext_impl} {X : X_type.π1}
  {X_type' : abstract_env_ext_impl} {X' : X_type'.π1}
  (hl : Hlookup X_type X X_type' X')
  {Γ : context} {t} 
  (wt : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> ∥ isType Σ Γ t ∥)
  (wt' : forall Σ : global_env_ext, abstract_env_ext_rel X' Σ -> ∥ isType Σ Γ t ∥) :
  (sort_of_type X_type X Γ t wt).π1 = (sort_of_type X_type' X' Γ t wt').π1.
Proof.
  simp sort_of_type.
  set (obl := sort_of_type_obligation_1 _ _ _ _ _ _ ).
  set (obl' := sort_of_type_obligation_4 _ _ _ _ _ _ _ _ ).
  set (obl2 := sort_of_type_obligation_1 _ _ _ _ _ _ ).
  set (obl2' := sort_of_type_obligation_4 _ _ _ _ _ _ _ _ ).
  set(ty := (type_of_typing _ _ _ _ obl)) in *.
  set(ty' := (type_of_typing _ _ _ _ obl2)) in *.
  assert (ty.π1 = ty'.π1).
  { subst ty ty'. unfold type_of_typing.
    eapply infer_irrel => //. }
  clearbody ty. clearbody ty'.
  destruct ty, ty'. cbn in H. subst x0.
  pose proof (reduce_to_sort_irrel hl eq_refl obl' obl2').
  destruct (PCUICSafeReduce.inspect) eqn:hi.
  cbn -[sort_of_type_clause_1_clause_1].
  destruct (PCUICSafeReduce.inspect (reduce_to_sort _ x obl2')) eqn:hi';
  rewrite -e -e0 in H.
  destruct x0, x1 => //. cbn in H.
  destruct a, a0. cbn in H; noconf H.
  now cbn.
  cbn. bang.
Qed.

(* From here on we are not abstract on the environment *)
Lemma is_arity_irrel {Σ Σ' : wf_env_ext} {Γ h h' t wt wt'} : 
  Hlookup optimized_abstract_env_ext_impl Σ optimized_abstract_env_ext_impl Σ' ->
  is_arity Σ Γ h t wt = is_arity Σ' Γ h' t wt'.
Proof.
  intros hl.
  funelim (is_arity Σ _ _ _ _).
  - epose proof (reduce_to_sort_irrel hl eq_refl HT wt').
    rewrite -rsort in H1.
    simp is_arity.
    epose proof (reduce_to_sort_irrel hl eq_refl HT wt').
    destruct (PCUICSafeReduce.inspect) eqn:hi.
    rewrite -e in H1.
    destruct x => //.
  - epose proof (reduce_to_sort_irrel hl eq_refl HT wt').
    rewrite -rsort in H3.
    rewrite [is_arity Σ' _ _ _ _]is_arity_equation_1.
    epose proof (reduce_to_sort_irrel hl eq_refl HT wt').
    destruct (PCUICSafeReduce.inspect) eqn:hi.
    rewrite -rsort -e in H4.
    destruct x => //.
    rewrite is_arity_clause_1_equation_2.
    destruct (PCUICSafeReduce.inspect (reduce_to_prod _ _ _)) eqn:hi'.
    epose proof (reduce_to_prod_irrel hl HT wt').
    rewrite -rprod -e0 in H5 => //.
    destruct x => //.
    destruct a1 as [na' [A' [B' ?]]]. cbn in H5. noconf H5.
    rewrite is_arity_clause_1_clause_2_equation_1.
    now apply H0.
  - epose proof (reduce_to_sort_irrel hl eq_refl HT wt').
    rewrite -rsort in H1.
    simp is_arity.
    destruct (PCUICSafeReduce.inspect) eqn:hi.
    rewrite -e0 in H1.
    destruct x => //.
    simp is_arity.
    destruct (PCUICSafeReduce.inspect (reduce_to_prod _ _ _)) eqn:hi'.
    epose proof (reduce_to_prod_irrel hl HT wt').
    rewrite -rprod -e1 in H2 => //.
    destruct x => //.
Qed.

Lemma extends_lookup_env {cf Σ Σ' kn d} : wf Σ' -> extends_decls Σ Σ' -> 
  lookup_env Σ kn = Some d -> lookup_env Σ' kn = Some d.
Proof.
  destruct Σ as [univs Σ].
  destruct Σ' as [univs' Σ'].
  intros wf [Σ'' []]. cbn in *. subst univs'.
  induction x in Σ, Σ', e, wf |- *. cbn in e. now subst Σ'.
  intros hl.
  rewrite e; cbn. 
  case: eqb_spec.
  intros ->. 
  eapply lookup_global_Some_fresh in hl.
  rewrite e in wf. destruct wf as [_ ond]; depelim ond.
  cbn in *. eapply Forall_app in f as []. contradiction.
  intros _.
  eapply IHx; trea.
  rewrite e in wf. destruct wf as [onu ond]; depelim ond.
  split => //.
Qed.
  
Lemma is_erasableb_irrel_global_env {Σ Σ' : wf_env_ext} {Γ t wt wt'} :
  wf Σ ->
  extends_decls Σ' Σ ->
  (Σ : global_env_ext).2 = (Σ' : global_env_ext).2 ->
  is_erasableb Σ Γ t wt = is_erasableb Σ' Γ t wt'.
Proof.
  intros wf ext eqext.
  assert (hl : Hlookup optimized_abstract_env_ext_impl Σ optimized_abstract_env_ext_impl Σ').
  { red. intros.
    rewrite -(abstract_env_lookup_correct _ _ H).
    rewrite -(abstract_env_lookup_correct _ _ H0).
    rewrite H1 H2. cbn in H. cbn in H0. subst Σ0 Σ'0.
    eapply extends_lookup_env in H2; tea. congruence. }
  simp is_erasableb.
  set (obl := is_erasableb_obligation_2 _ _ _ _). clearbody obl.
  set(ty := (type_of_typing optimized_abstract_env_ext_impl _ _ _ wt')) in *.
  set(ty' := (type_of_typing optimized_abstract_env_ext_impl _ _ _ wt)) in *.
  assert (ty.π1 = ty'.π1).
  { subst ty ty'. unfold type_of_typing. symmetry. 
    eapply infer_irrel => //. }
  clearbody ty. clearbody ty'.
  destruct ty, ty'. cbn in H. subst x0.
  cbn -[is_arity] in obl |- *.
  set (obl' := is_erasableb_obligation_1 Σ' Γ t wt').
  set (obl'' := is_erasableb_obligation_2 Σ' Γ t _).
  clearbody obl'. clearbody obl''.
  rewrite (is_arity_irrel (Σ' := Σ')) //.
  destruct is_arity => //. simp is_erasableb.
  set (obl2 := is_erasableb_obligation_3 _ _ _ _).
  set (obl2' := is_erasableb_obligation_3 _ _ _ _).
  simpl. f_equal.
  apply (sort_of_type_irrel (X_type := optimized_abstract_env_ext_impl)
    (X_type' := optimized_abstract_env_ext_impl) hl obl2 obl2').
Qed.

Ltac iserasableb_irrel_env :=
  match goal with
  [ H : context [is_erasableb ?Σ ?Γ ?t ?wt], Heq : inspect_bool _ = _ |- context [ is_erasableb _ _ _ ?wt'] ] => 
    generalize dependent H; rewrite (@is_erasableb_irrel_global_env _ _ _ _ wt wt') //; intros; rewrite Heq
  end.

Lemma erase_irrel_global_env {Σ Σ' : wf_env_ext} {Γ t wt wt'} :
  wf Σ ->
  extends_decls Σ' Σ ->
  (Σ : global_env_ext).2 = (Σ' : global_env_ext).2 ->
  erase Σ Γ t wt = erase Σ' Γ t wt'.
Proof.
  intros wfΣ ext eq.
  move: wt'.
  eapply (erase_elim Σ
  (fun Γ t wt e => 
    forall (wt' : forall Σ0 : global_env_ext, abstract_env_rel' Σ' Σ0 ->  welltyped Σ0 Γ t), 
    e = erase Σ' Γ t wt')
  (fun Γ l awt e => forall wt',
    e = erase_terms Σ' Γ l wt')
  (fun Γ p l awt e => forall wt', 
    e = erase_brs Σ' Γ p l wt')
  (fun Γ l awt e => forall wt', 
    e = erase_fix Σ' Γ l wt')
  (fun Γ l awt e => forall wt', 
    e = erase_cofix Σ' Γ l wt')).
  all:intros *; intros; simp_erase.
  simp erase.
  all:try simp erase; try iserasableb_irrel_env; simp_erase => //.
  all:try clear he Heq.
  all:try bang.
  all:try solve [cbn; f_equal; eauto].
  all:try solve [cbn; repeat (f_equal; eauto)].
  cbn. f_equal. eauto. f_equal.
  now rewrite (H (erase_obligation_19 Σ' Γ0 d mfix wt')).
  now rewrite (H0 (erase_obligation_20 Σ' Γ0 d mfix wt')).
Qed.

Lemma erase_constant_body_suffix {Σ Σ' : wf_env_ext} {cb ondecl ondecl'} :
wf Σ -> extends_decls Σ' Σ -> (Σ : global_env_ext).2 = (Σ' : global_env_ext).2 ->
erase_constant_body Σ cb ondecl = erase_constant_body Σ' cb ondecl'.
Proof.
  intros wfΣ ext eqext.
  destruct cb => //=.
  destruct cst_body0 => //=.
  unfold erase_constant_body; simpl => /=.
  f_equal. f_equal. f_equal.
  eapply erase_irrel_global_env; tea.
  f_equal.
  eapply erase_irrel_global_env; tea.
Qed.

(*Lemma erase_global_deps_suffix {deps} {Σ Σ' : wf_env} {decls hprefix hprefix'} :
  wf Σ -> wf Σ' ->
  universes Σ = universes Σ' -> 
  erase_global_decls_fast deps Σ decls hprefix = 
  erase_global_decls_fast deps Σ' decls hprefix'.
Proof.
  intros wfΣ wfΣ' equ.
  induction decls in deps, hprefix, hprefix' |- *; cbn => //.
  destruct a as [kn []].
  set (obl := (erase_global_decls_fast_obligation_1 Σ ((kn, ConstantDecl c) :: decls)
             hprefix kn c decls eq_refl)). clearbody obl.
  destruct obl.
  set (eb := erase_constant_body _ _ _).
  set (eb' := erase_constant_body _ _ _).
  assert (eb = eb') as <-.
  { subst eb eb'.
    set (wfΣx := make_wf_env_ext _ _ _).
    set (wfΣ'x := make_wf_env_ext _ _ _).
    set (obl' := erase_global_decls_fast_obligation_2 _ _ _ _ _ _ _).
    clearbody obl'.
    set (Σd := {| universes := Σ.(universes); declarations := decls |}).
    assert (wfΣd : wf Σd).
    { eapply decls_prefix_wf; tea.
      clear -hprefix. move: hprefix. unfold decls_prefix.
      intros [Σ'' eq]. exists (Σ'' ++ [(kn, ConstantDecl c)]).
      rewrite -app_assoc //. }
    set (wfΣdwfe := build_wf_env_from_env _ (sq wfΣd)).
    assert (wfextΣd : wf_ext (Σd, cst_universes c)).
    { split => //. cbn. apply w. }
    set (wfΣdw := make_wf_env_ext wfΣdwfe (cst_universes c) (sq wfextΣd)).
    assert (ond' : ∥ on_constant_decl (lift_typing typing) (Σd, cst_universes c) c ∥ ).
    { pose proof (decls_prefix_wf hprefix wfΣ).
      destruct X as [onu ond]. depelim ond. sq. apply o0. }
    assert (extd' : extends_decls Σd Σ).
    { clear -hprefix. move: hprefix.
      intros [? ?]. split => //. eexists (x ++ [(kn, ConstantDecl c)]). cbn.
      now rewrite -app_assoc. }
    assert (extd'' : extends_decls Σd Σ').
    { clear -equ hprefix'. move: hprefix'.
      intros [? ?]. split => //. eexists (x ++ [(kn, ConstantDecl c)]). cbn.
      now rewrite -app_assoc. }
    rewrite (erase_constant_body_suffix (Σ := wfΣx) (Σ' := wfΣdw) (ondecl' := ond') wfΣ extd') //.
    rewrite (erase_constant_body_suffix (Σ := wfΣ'x) (Σ' := wfΣdw) (ondecl' := ond') wfΣ' extd'') //. }
  destruct KernameSet.mem => //. f_equal.
  eapply IHdecls.
  destruct KernameSet.mem => //. f_equal.
  eapply IHdecls.
Qed.*)
  
Lemma erase_global_deps_fast_spec_gen {deps} {Σ Σ' : wf_env} {decls hprefix hprefix'} :
  universes Σ = universes Σ' -> 
  erase_global_decls_fast deps Σ decls hprefix = 
  erase_global_decls deps Σ' decls hprefix'.
Proof.
  assert (wf : ∥ wf Σ ∥) by exact (referenced_impl_wf Σ).
  destruct wf as [wf].
  intros equ.
  induction decls in Σ', equ, deps, hprefix, hprefix' |- * => //.
  destruct a as [kn []].
  - set (obl := (erase_global_decls_fast_obligation_1 Σ ((kn, ConstantDecl c) :: decls)
             hprefix kn c decls eq_refl)). clearbody obl.
    destruct obl.
    cbn.
    set (eb := erase_constant_body _ _ _).
    set (eb' := erase_constant_body _ _ _).
    assert (eb = eb') as <-.
    { subst eb eb'.
      eapply erase_constant_body_suffix; cbn => //.
      red. split => //. cbn.
      destruct hprefix. rewrite e.
      eexists (x ++ [(kn, ConstantDecl c)]). now rewrite -app_assoc. }
    destruct KernameSet.mem => //; f_equal; eauto.
  - cbn.
    destruct KernameSet.mem => //; f_equal; eauto.
Qed.

Lemma erase_global_deps_fast_spec {deps} {Σ : wf_env} {decls hprefix hprefix'} :
  erase_global_decls_fast deps Σ decls hprefix = 
  erase_global_decls deps Σ decls hprefix'.
Proof.
  eapply erase_global_deps_fast_spec_gen; auto.
Qed.

Definition erase_global_fast deps Σ :=
  erase_global_decls_fast deps Σ Σ.(declarations) ([]; eq_refl).

Lemma erase_global_fast_spec {deps} {Σ : wf_env} :
  erase_global_fast deps Σ = 
  erase_global deps Σ.
Proof.
  rewrite /erase_global_fast erase_global_deps_fast_spec //.
Qed.

Lemma expanded_erase_global_fast (cf := config.extraction_checker_flags) deps {Σ: wf_env} :
  PCUICEtaExpand.expanded_global_env Σ ->
  expanded_global_env (erase_global_fast deps Σ).
Proof.
  rewrite erase_global_fast_spec.
  eapply expanded_erase_global.
Qed.

Lemma expanded_erase_fast (cf := config.extraction_checker_flags) {Σ : wf_env} univs wfΣ t wtp :
  PCUICEtaExpand.expanded Σ [] t ->
  let Σ' := make_wf_env_ext Σ univs wfΣ in
  let et := (erase Σ' [] t wtp) in
  let deps := EAstUtils.term_global_deps et in
  expanded (erase_global_fast deps Σ) [] et.
Proof.
  intros hexp Σ'.
  have [wf] : ∥ wf Σ ∥.
  { destruct wfΣ. sq. exact w. }
  eapply (expanded_erases (Σ := (Σ, univs))); tea.
  eapply (erases_erase (Σ := Σ')). cbn.
  rewrite erase_global_fast_spec //.
  eapply (erases_deps_erase (Σ := Σ) univs wfΣ).
Qed.

Lemma erase_global_fast_wf_glob Σ deps :
  @wf_glob all_env_flags (erase_global_fast deps Σ).
Proof.
  rewrite erase_global_fast_spec.
  eapply erase_global_wf_glob.
Qed.

Lemma erase_wellformed_fast (efl := all_env_flags) {Σ : wf_env} univs wfΣ {Γ t} wt
  (Σ' := make_wf_env_ext Σ univs wfΣ) :
  let t' := erase Σ' Γ t wt in
  wellformed (erase_global_fast (term_global_deps t') Σ) #|Γ| t'.
Proof.
  intros. 
  cbn. rewrite erase_global_fast_spec.
  eapply erase_wellformed.
Qed.

End EraseGlobalFast.