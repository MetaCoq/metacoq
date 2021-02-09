(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils Universes.
From MetaCoq.PCUIC Require Import PCUICTyping PCUICAst PCUICAstUtils
     PCUICLiftSubst PCUICInductives PCUICGeneration PCUICSpine PCUICWeakeningEnv
     PCUICSubstitution PCUICUnivSubst PCUICUnivSubstitution
     PCUICConversion PCUICCumulativity PCUICConfluence PCUICContexts
     PCUICSR PCUICInversion PCUICValidity PCUICSafeLemmata PCUICContextConversion
     PCUICEquality PCUICReduction.

Require Import Equations.Type.Relation Equations.Type.Relation_Properties.
Require Equations.Prop.DepElim.
From Equations Require Import Equations.
Require Import ssreflect.

Section no_prop_leq_type.

Context `{cf : checker_flags}.
Variable Hcf : prop_sub_type = false.
Variable Hcf' : check_univs = true.

Lemma cumul_sort_confluence {Σ : global_env_ext} {wfΣ : wf Σ} {Γ A u v} :
  Σ ;;; Γ |- A <= tSort u ->
  Σ ;;; Γ |- A <= tSort v ->
  ∑ v', (Σ ;;; Γ |- A = tSort v') *
        (leq_universe (global_ext_constraints Σ) v' u /\
          leq_universe (global_ext_constraints Σ) v' v).
Proof.
  move=> H H'.
  eapply invert_cumul_sort_r in H as [u'u ?].
  eapply invert_cumul_sort_r in H' as [vu ?].
  destruct p, p0.
  destruct (red_confluence wfΣ r r0).
  destruct p.
  eapply invert_red_sort in r1.
  eapply invert_red_sort in r2. subst. noconf r2.
  exists u'u. split; auto.
Qed.

Lemma cumul_ind_confluence {Σ : global_env_ext} {wfΣ : wf Σ} {Γ A ind u v l l'} :
  Σ ;;; Γ |- A <= mkApps (tInd ind u) l  ->
  Σ ;;; Γ |- A <= mkApps (tInd ind v) l' ->
  ∑ v' l'', (red Σ Γ A (mkApps (tInd ind v') l'')) *
        All2 (conv Σ Γ) l l'' *
        All2 (conv Σ Γ) l' l'' *          
        (R_global_instance Σ (eq_universe Σ) (leq_universe Σ) (IndRef ind) #|l| v' u /\
          R_global_instance Σ (eq_universe Σ) (leq_universe Σ) (IndRef ind) #|l'| v' v).
Proof.
  move=> H H'.
  eapply invert_cumul_ind_r in H as [u'u [l'u [redl [ru ?]]]].
  eapply invert_cumul_ind_r in H' as [vu [l''u [redr [ru' ?]]]].
  destruct (red_confluence wfΣ redl redr) as [nf [redl' redr']].
  eapply red_mkApps_tInd in redl'  as [args' [eqnf conv]].
  eapply red_mkApps_tInd in redr'  as [args'' [eqnf' conv']].
  rewrite eqnf in eqnf'. solve_discr. subst nf.
  all:auto. exists u'u, args'; intuition auto.
  transitivity (mkApps (tInd ind u'u) l'u).
  auto. eapply red_mkApps. reflexivity. auto.
  - apply All2_trans with l'u => //. typeclasses eauto.
    eapply (All2_impl conv). intros. now apply red_conv.
  - apply All2_trans with l''u => //. typeclasses eauto.
    eapply (All2_impl conv'). intros. now apply red_conv.
Qed.

Lemma invert_conv_letin_l_alt {Σ Γ C na d ty b} :
  wf Σ.1 -> wf_local Σ (Γ ,, vdef na d ty) ->
  Σ ;;; Γ |- tLetIn na d ty b = C ->
  Σ ;;; Γ,, vdef na d ty |- b = lift0 1 C.
Proof.
  intros wfΣ wf Hlet.
  epose proof (red_expand_let _ _ _ _ b wf).
  eapply conv_trans. auto. eapply red_conv, X. 
  eapply (PCUICWeakening.weakening_conv _ Γ [] [vdef _ _ _]); auto.
  now eapply invert_conv_letin_l in Hlet.
Qed.

Lemma is_prop_bottom {Σ Γ T s s'} :
  wf_ext Σ ->
  Σ ;;; Γ |- T <= tSort s ->
  Σ ;;; Γ |- T <= tSort s' ->
  Universe.is_prop s -> Universe.is_prop s'.
Proof.
  intros wfΣ hs hs'.
  destruct (cumul_sort_confluence hs hs') as [x' [conv [leq leq']]].
  intros isp.
  eapply leq_universe_prop_r in leq; eauto.
  unshelve eapply (leq_universe_prop_no_prop_sub_type _ _ _ _ _ _ leq'); eauto.
Qed.

Lemma is_sprop_bottom {Σ Γ T s s'} :
  wf_ext Σ ->
  Σ ;;; Γ |- T <= tSort s ->
  Σ ;;; Γ |- T <= tSort s' ->
  Universe.is_sprop s -> Universe.is_sprop s'.
Proof.
  intros wfΣ hs hs'.
  destruct (cumul_sort_confluence hs hs') as [x' [conv [leq leq']]].
  intros isp.
  eapply leq_universe_sprop_r in leq; eauto.
  unshelve eapply (leq_universe_sprop_l _ _ _ _ _ leq'); eauto.
Qed.

Lemma prop_sort_eq {Σ Γ u u'} : Universe.is_prop u -> Universe.is_prop u' -> Σ ;;; Γ |- tSort u = tSort u'.
Proof.
  move=> isp isp'.
  constructor. constructor. 
  red. rewrite Hcf'.
  red. intros. now rewrite (is_prop_val _ isp) (is_prop_val _ isp').
Qed.

Lemma sprop_sort_eq {Σ Γ u u'} : Universe.is_sprop u -> Universe.is_sprop u' -> Σ ;;; Γ |- tSort u = tSort u'.
Proof.
  move=> isp isp'.
  constructor. constructor. 
  red. rewrite Hcf'.
  red. intros. now rewrite (is_sprop_val _ isp) (is_sprop_val _ isp').
Qed.

Lemma conv_sort_inv Σ Γ s s' :
  Σ ;;; Γ |- tSort s = tSort s' ->
  eq_universe (global_ext_constraints Σ) s s'.
Proof.
  intros H.
  eapply conv_alt_red in H as [v [v' [[redv redv'] eqvv']]].
  eapply invert_red_sort in redv.
  eapply invert_red_sort in redv'. subst.
  now depelim eqvv'.
Qed.

Lemma is_prop_superE {Σ l} : wf_ext Σ -> Universe.is_prop (Universe.super l) -> False.
Proof.
  intros wfΣ. 
  eapply is_prop_gt; eauto.
  eapply leq_universe_refl.
Qed.

Lemma is_sprop_superE {Σ l} : wf_ext Σ -> Universe.is_sprop (Universe.super l) -> False.
Proof.
  intros wfΣ. destruct l => //. 
Qed.
  
Lemma is_prop_prod {s s'} : Universe.is_prop s' -> Universe.is_prop (Universe.sort_of_product s s').
Proof.
  intros isp.
  unfold Universe.sort_of_product. rewrite isp. auto.
Qed.

Lemma is_sprop_prod {s s'} : Universe.is_sprop s' -> Universe.is_sprop (Universe.sort_of_product s s').
Proof.
  intros isp.
  unfold Universe.sort_of_product. rewrite isp orb_true_r. auto.
Qed.

Definition eq_univ_prop (u v : Universe.t) :=
  (Universe.is_prop u <-> Universe.is_prop v) /\
  (Universe.is_sprop u <-> Universe.is_sprop v).

Definition eq_term_prop (Σ : global_env) napp :=
  PCUICEquality.eq_term_upto_univ_napp Σ eq_univ_prop eq_univ_prop napp.

Reserved Notation " Σ ;;; Γ |- t ~~ u " (at level 50, Γ, t, u at next level).

Inductive cumul_prop `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
  | cumul_refl t u : eq_term_prop Σ.1 0 t u -> Σ ;;; Γ |- t ~~ u
  | cumul_red_l t u v : red1 Σ.1 Γ t v -> Σ ;;; Γ |- v ~~ u -> Σ ;;; Γ |- t ~~ u
  | cumul_red_r t u v : Σ ;;; Γ |- t ~~ v -> red1 Σ.1 Γ u v -> Σ ;;; Γ |- t ~~ u
  
where " Σ ;;; Γ |- t ~~ u " := (cumul_prop Σ Γ t u) : type_scope.

Lemma eq_term_prop_impl Σ Re Rle t u :
  wf_ext Σ ->
  forall n,
  PCUICEquality.eq_term_upto_univ_napp Σ.1 Re Rle n t u ->
  subrelation Re eq_univ_prop ->
  subrelation Rle eq_univ_prop ->
  eq_term_prop Σ n t u.
Proof.
  intros wfΣ n eq.
  intros.
  eapply PCUICEquality.eq_term_upto_univ_impl in eq. eauto.
  all:auto. 
Qed.

Lemma leq_universe_prop_spec Σ u1 u2 :
  check_univs ->
  wf_ext Σ ->
  leq_universe Σ u1 u2 ->
  match u1, u2 with
  | Universe.lProp, Universe.lProp => True
  | Universe.lSProp, Universe.lSProp => True
  | Universe.lProp, Universe.lSProp => False
  | Universe.lSProp, Universe.lProp => False
  | Universe.lProp, Universe.lType _ => prop_sub_type
  | Universe.lSProp, Universe.lType _ => False
  | Universe.lType l, Universe.lType l' => True
  | Universe.lType _, _ => False
  end.
Proof.
  intros cu wf leq.
  apply wf_ext_consistent in wf.
  apply (leq_universe_props _ _ _ cu wf leq).
Qed.

Lemma subrelation_eq_universe_eq_prop Σ : 
  wf_ext Σ ->
  subrelation (eq_universe Σ) eq_univ_prop.
Proof.
  intros wfΣ x y eq'. red.
  split; intros.
  eapply eq_universe_leq_universe in eq'.
  eapply leq_universe_prop_spec in eq'; auto.
  destruct x, y; simpl in *; auto; cong.
  eapply eq_universe_leq_universe in eq'.
  eapply leq_universe_prop_spec in eq'; auto.
  destruct x, y; simpl in *; auto; cong.
Qed.

Lemma subrelation_leq_universe_eq_prop Σ : 
  wf_ext Σ ->
  subrelation (leq_universe Σ) eq_univ_prop.
Proof.
  intros wfΣ x y eq'. red.
  split; intros;
  eapply leq_universe_prop_spec in eq'; auto;
  destruct x, y; simpl in *; auto; cong.
Qed.

Lemma eq_term_eq_term_prop_impl Σ t u :
  wf_ext Σ ->
  forall n,
  PCUICEquality.eq_term_upto_univ_napp Σ.1 (eq_universe Σ) (eq_universe Σ) n t u ->
  eq_term_prop Σ n t u.
Proof.
  intros wfΣ n eq. eapply eq_term_prop_impl; eauto.
  now apply subrelation_eq_universe_eq_prop.
  now apply subrelation_eq_universe_eq_prop.
Qed.

Lemma leq_term_eq_term_prop_impl Σ t u :
  wf_ext Σ ->
  forall n,
  PCUICEquality.eq_term_upto_univ_napp Σ.1 (eq_universe Σ) (leq_universe Σ) n t u ->
  eq_term_prop Σ n t u.
Proof.
  intros wfΣ n eq. eapply eq_term_prop_impl; eauto.
  now apply subrelation_eq_universe_eq_prop.
  now apply subrelation_leq_universe_eq_prop.
Qed.

Lemma cumul_cumul_prop Σ Γ A B : 
  wf_ext Σ ->
  Σ ;;; Γ |- A <= B ->
  Σ ;;; Γ |- A ~~ B.
Proof.
  intros wfΣ. induction 1.
  - constructor. now apply leq_term_eq_term_prop_impl in l.
  - econstructor 2; eauto.
  - econstructor 3; eauto.
Qed.

Lemma conv_cumul_prop Σ Γ A B : 
  wf_ext Σ ->
  Σ ;;; Γ |- A = B ->
  Σ ;;; Γ |- A ~~ B.
Proof.
  intros wfΣ. induction 1.
  - constructor. now apply eq_term_eq_term_prop_impl in e.
  - econstructor 2; eauto.
  - econstructor 3; eauto.
Qed.

Lemma cumul_prop_alt Σ Γ T U :
  Σ ;;; Γ |- T ~~ U <~>
  ∑ nf nf', (red Σ Γ T nf * red Σ Γ U nf' * eq_term_prop Σ 0 nf nf').
Proof.
  split.
  - induction 1.
    exists t, u. intuition pcuic.
    destruct IHX as [nf [nf' [[redl redr] eq]]].
    exists nf, nf'; intuition pcuic.
    now transitivity v.
    destruct IHX as [nf [nf' [[redl redr] eq]]].
    exists nf, nf'; intuition pcuic.
    now transitivity v.
  - intros [nf [nf' [[redv redv'] eq]]].
    apply clos_rt_rt1n in redv.
    apply clos_rt_rt1n in redv'.
    induction redv.
    * induction redv'.
    ** constructor; auto.
    ** econstructor 3; eauto.
    * econstructor 2; eauto.
Qed.

Lemma cumul_prop_props Σ Γ u u' : 
  Universe.is_prop u ->
  Σ ;;; Γ |- tSort u ~~ tSort u' ->
  Universe.is_prop u'.
Proof.
  intros isp equiv.
  eapply cumul_prop_alt in equiv as [nf [nf' [[redl redr] eq]]].
  eapply invert_red_sort in redl. apply invert_red_sort in redr.
  subst.
  depelim eq. red in e. intuition auto.
Qed.

Lemma cumul_sprop_props Σ Γ u u' : 
  Universe.is_sprop u ->
  Σ ;;; Γ |- tSort u ~~ tSort u' ->
  Universe.is_sprop u'.
Proof.
  intros isp equiv.
  eapply cumul_prop_alt in equiv as [nf [nf' [[redl redr] eq]]].
  eapply invert_red_sort in redl. apply invert_red_sort in redr.
  subst.
  depelim eq. red in e. intuition auto.
Qed.

Instance refl_eq_univ_prop : RelationClasses.Reflexive eq_univ_prop.
Proof.
  intros x. red. intuition.
Qed.

Instance sym_eq_univ_prop : RelationClasses.Symmetric eq_univ_prop.
Proof.
  intros x y; unfold eq_univ_prop; intuition.
Qed.

Instance trans_eq_univ_prop : RelationClasses.Transitive eq_univ_prop.
Proof.
  intros x y; unfold eq_univ_prop; intuition.
Qed.

Lemma UnivExprSet_For_all (P : UnivExpr.t -> Prop) (u : Universe.t0) :
  UnivExprSet.For_all P u <->
  Forall P (UnivExprSet.elements u).
Proof.
  rewrite UnivExprSet_For_all_exprs.
  pose proof (Universe.exprs_spec u).
  destruct (Universe.exprs u). rewrite -H. simpl.
  split. constructor; intuition.
  intros H'; inv H'; intuition.
Qed.

Lemma univ_expr_set_in_elements e s : 
  UnivExprSet.In e s <-> In e (UnivExprSet.elements s).
Proof.
  rewrite -UnivExprSet.elements_spec1. generalize (UnivExprSet.elements s).
  now eapply InA_In_eq.
Qed.

Lemma univ_epxrs_elements_map g s : 
  forall e, In e (UnivExprSet.elements (Universe.map g s)) <->
      In e (map g (UnivExprSet.elements s)).
Proof.
  intros e.
  unfold Universe.map.
  pose proof (Universe.exprs_spec s).
  destruct (Universe.exprs s) as [e' l] eqn:eq.  
  rewrite -univ_expr_set_in_elements Universe.add_list_spec.
  rewrite -H. simpl. rewrite UnivExprSet.singleton_spec.
  intuition auto.
Qed.
  
Lemma Forall_elements_in P s : Forall P (UnivExprSet.elements s) <-> 
  (forall x, UnivExprSet.In x s -> P x).
Proof.
  setoid_rewrite univ_expr_set_in_elements.
  generalize (UnivExprSet.elements s).
  intros.
  split; intros.
  induction H; depelim H0; subst => //; auto.
  induction l; constructor; auto.
  apply H. repeat constructor.
  apply IHl. intros x inxl. apply H. right; auto.
Qed.

Lemma univ_exprs_map_all P g s : 
  Forall P (UnivExprSet.elements (Universe.map g s)) <->
  Forall (fun x => P (g x)) (UnivExprSet.elements s).
Proof.
  rewrite !Forall_elements_in.
  setoid_rewrite Universe.map_spec.
  intuition auto.
  eapply H. now exists x.
  destruct H0 as [e' [ins ->]]. apply H; auto.
Qed.

Lemma expr_set_forall_map f g s : 
  UnivExprSet.for_all f (Universe.map g s) <->
  UnivExprSet.for_all (fun e => f (g e)) s.
Proof.
  rewrite /is_true !UnivExprSet.for_all_spec !UnivExprSet_For_all.
  apply univ_exprs_map_all.
Qed.

Lemma univ_is_prop_make x : Universe.is_prop (Universe.make x) = false.
Proof.
  destruct x; simpl; auto.
Qed.

(* Lemma is_prop_subst_level_expr u1 u2 s : 
  Forall2 (fun x y : Level.t => eq_univ_prop (Universe.make x) (Universe.make y)) u1 u2  ->
  UnivExpr.is_prop (subst_instance_level_expr u1 s) = UnivExpr.is_prop (subst_instance_level_expr u2 s).
Proof.
  intros hu. destruct s; simpl; auto.
  destruct e as [[] ?]; simpl; auto.
  destruct (nth_error u1 n) eqn:E.
  eapply Forall2_nth_error_Some_l in hu; eauto.
  destruct hu as [t' [-> eq]].
  red in eq. rewrite !univ_is_prop_make in eq.
  eapply eq_iff_eq_true in eq.
  destruct t, t'; simpl in eq => //.
  eapply Forall2_nth_error_None_l in hu; eauto.
  now rewrite hu.
Qed. *)

Instance substuniv_eq_univ_prop : SubstUnivPreserving eq_univ_prop.
Proof.
  intros s u1 u2 hu.
  red in hu.
  eapply Forall2_map_inv in hu.
  rewrite /subst_instance_univ.
  destruct s; red; simpl; auto; try intuition reflexivity.
Qed.

Lemma cumul_prop_sym Σ Γ T U : 
  wf Σ.1 ->
  Σ ;;; Γ |- T ~~ U ->
  Σ ;;; Γ |- U ~~ T.
Proof.
  intros wfΣ Hl.
  eapply cumul_prop_alt in Hl as [t' [u' [[tt' uu'] eq]]].
  eapply cumul_prop_alt.
  exists u', t'; intuition auto.
  now symmetry.
Qed.

Lemma cumul_prop_trans Σ Γ T U V : 
  wf_ext Σ ->
  Σ ;;; Γ |- T ~~ U ->
  Σ ;;; Γ |- U ~~ V ->
  Σ ;;; Γ |- T ~~ V.
Proof.
  intros wfΣ Hl Hr.
  eapply cumul_prop_alt in Hl as [t' [u' [[tt' uu'] eq]]].
  eapply cumul_prop_alt in Hr as [u'' [v' [[uu'' vv'] eq']]].
  eapply cumul_prop_alt. destruct wfΣ as [wfΣ onu] .
  destruct (red_confluence wfΣ uu' uu'') as [u'nf [ul ur]].
  eapply red_eq_term_upto_univ_r in ul as [tnf [redtnf ?]]; tea; tc.
  eapply red_eq_term_upto_univ_l in ur as [unf [redunf ?]]; tea; tc.
  exists tnf, unf.
  intuition auto.
  - now transitivity t'.
  - now transitivity v'.
  - now transitivity u'nf.
Qed.

Instance cumul_prop_transitive Σ Γ : wf_ext Σ -> CRelationClasses.Transitive (cumul_prop Σ Γ).
Proof. intros. red. intros. now eapply cumul_prop_trans. Qed.

Lemma cumul_prop_cum_l Σ Γ A T B : 
  wf_ext Σ ->
  Σ ;;; Γ |- A ~~ T -> 
  Σ ;;; Γ |- A <= B ->
  Σ ;;; Γ |- B ~~ T.
Proof.
  intros wfΣ HT cum.
  eapply cumul_cumul_prop in cum; auto.
  eapply CRelationClasses.transitivity ; eauto.
  eapply cumul_prop_sym; eauto.
Qed.

Lemma cumul_prop_cum_r Σ Γ A T B : 
  wf_ext Σ ->
  Σ ;;; Γ |- A ~~ T -> 
  Σ ;;; Γ |- B <= A ->
  Σ ;;; Γ |- B ~~ T.
Proof.
  intros wfΣ HT cum.
  eapply cumul_cumul_prop in cum; auto.
  eapply CRelationClasses.transitivity ; eauto.
Qed.

Lemma cumul_prop_conv_l Σ Γ A T B : 
  wf_ext Σ ->
  Σ ;;; Γ |- A ~~ T -> 
  Σ ;;; Γ |- A = B ->
  Σ ;;; Γ |- B ~~ T.
Proof.
  intros wfΣ HT cum.
  eapply conv_cumul_prop in cum; auto.
  eapply CRelationClasses.transitivity ; eauto.
  eapply cumul_prop_sym; eauto.
Qed.

Lemma cumul_prop_conv_r Σ Γ A T B : 
  wf_ext Σ ->
  Σ ;;; Γ |- A ~~ T -> 
  Σ ;;; Γ |- B = A ->
  Σ ;;; Γ |- B ~~ T.
Proof.
  intros wfΣ HT cum.
  eapply conv_cumul_prop in cum; auto.
  eapply CRelationClasses.transitivity ; eauto.
Qed.

Definition conv_decls_prop (Σ : global_env_ext) (Γ Γ' : context) (c d : context_decl) :=
  match decl_body c, decl_body d with
  | None, None => True
  | Some b, Some b' => b = b'
  | _, _ => False
  end.

Notation conv_ctx_prop Σ := (All2_fold (conv_decls_prop Σ)).

Lemma conv_ctx_prop_refl Σ Γ :
  conv_ctx_prop Σ Γ Γ.
Proof.
  induction Γ as [|[na [b|] ty]]; constructor; eauto => //.
Qed.

Lemma conv_ctx_prop_app Σ Γ Γ' Δ :
  conv_ctx_prop Σ Γ Γ' ->
  conv_ctx_prop Σ (Γ ,,, Δ) (Γ' ,,, Δ).
Proof.
  induction Δ; simpl; auto.
  destruct a as [na  [b|] ty]; intros; constructor => //.
  now eapply IHΔ.
  now eapply IHΔ.
Qed.

Lemma red1_upto_conv_ctx_prop Σ Γ Γ' t t' :
  red1 Σ.1 Γ t t' ->
  conv_ctx_prop Σ Γ Γ' ->
  red1 Σ.1 Γ' t t'.
Proof.
  intros Hred; induction Hred using red1_ind_all in Γ' |- *; 
    try solve [econstructor; eauto; try solve [solve_all]].
  - econstructor. destruct (nth_error Γ i) eqn:eq; simpl in H => //.
    noconf H; simpl in H; noconf H.
    eapply All2_fold_nth in X; eauto.
    destruct X as [d' [Hnth [ctxrel cp]]].
    red in cp. rewrite H in cp. rewrite Hnth /=.
    destruct (decl_body d'); subst => //.
  - econstructor. eapply IHHred. constructor; simpl; auto => //.
  - econstructor. eapply IHHred. constructor; simpl => //.
  - econstructor.
    eapply OnOne2_local_env_impl; tea => /=; intros ? d d'.
    eapply on_one_decl_impl => Δ' x y IH. apply IH.
    now apply conv_ctx_prop_app.
  - intros h. constructor.
    eapply IHHred. now apply conv_ctx_prop_app.
  - intros h; constructor.
    eapply OnOne2_impl; tea => /= br br'.
    intros [[red IH]|[red IH]]; [left|right].
    * split=> //. now eapply red, conv_ctx_prop_app.
    * split=> //. eapply OnOne2_local_env_impl; tea => /=; intros ? d d'.
      apply on_one_decl_impl => Δ' x y IH'; now apply IH', conv_ctx_prop_app.
  - intros. constructor; eapply IHHred; constructor; simpl; auto => //.
  - intros. eapply fix_red_body. solve_all.
    eapply b0. now eapply conv_ctx_prop_app.
  - intros. eapply cofix_red_body. solve_all.
    eapply b0. now eapply conv_ctx_prop_app.
Qed.

Lemma red_upto_conv_ctx_prop Σ Γ Γ' t t' :
  red Σ.1 Γ t t' ->
  conv_ctx_prop Σ Γ Γ' ->
  red Σ.1 Γ' t t'.
Proof.
  intros Hred. intros convctx.
  induction Hred; eauto.
  constructor. now eapply red1_upto_conv_ctx_prop.
  eapply rt_trans; eauto.
Qed.

Lemma cumul_prop_prod_inv Σ Γ na A B na' A' B' :
  wf Σ.1 ->
  Σ ;;; Γ |- tProd na A B ~~ tProd na' A' B' ->
  Σ ;;; Γ ,, vass na A |- B ~~ B'.
Proof.
  intros wfΣ H; eapply cumul_prop_alt in H as [nf [nf' [[redv redv'] eq]]].
  eapply invert_red_prod in redv as (? & ? & (? & ?) & ?).
  eapply invert_red_prod in redv' as (? & ? & (? & ?) & ?).
  subst. all:auto.
  eapply cumul_prop_alt.
  exists x0, x2. intuition auto.
  eapply red_upto_conv_ctx_prop; eauto.
  constructor; auto => //. apply conv_ctx_prop_refl.
  depelim eq. apply eq2.
Qed.

Lemma substitution_untyped_cumul_prop Σ Γ Δ Γ' s M N :
  wf Σ.1 -> untyped_subslet Γ s Δ ->
  Σ ;;; (Γ ,,, Δ ,,, Γ') |- M ~~ N ->
  Σ ;;; (Γ ,,, subst_context s 0 Γ') |- (subst s #|Γ'| M) ~~ (subst s #|Γ'| N).
Proof.
  intros wfΣ subs Hcum.
  eapply cumul_prop_alt in Hcum as [nf [nf' [[redl redr] eq']]].
  eapply substitution_untyped_red in redl; eauto.
  eapply substitution_untyped_red in redr; eauto.
  eapply cumul_prop_alt.
  eexists _, _; intuition eauto.
  eapply PCUICEquality.eq_term_upto_univ_substs => //.
  eapply All2_refl.
  intros x. eapply PCUICEquality.eq_term_upto_univ_refl; typeclasses eauto.
Qed.

Lemma substitution_untyped_cumul_prop_equiv Σ Γ Δ Γ' s s' M :
  wf Σ.1 -> 
  untyped_subslet Γ s Δ ->
  untyped_subslet Γ s' Δ ->
  All2 (eq_term_prop Σ.1 0) s s' ->
  Σ ;;; (Γ ,,, subst_context s 0 Γ') |- (subst s #|Γ'| M) ~~ (subst s' #|Γ'| M).
Proof.
  intros wfΣ subs subs' Heq.
  eapply cumul_prop_alt.
  eexists _, _; intuition eauto.
  eapply PCUICEquality.eq_term_upto_univ_substs => //.
  reflexivity.
Qed.

Lemma cumul_prop_args (Σ : global_env_ext) {Γ args args'} :
  wf_ext Σ ->
  All2 (cumul_prop Σ Γ) args args' ->
  ∑ nf nf', All2 (red Σ Γ) args nf * All2 (red Σ Γ) args' nf' *
    All2 (eq_term_prop Σ 0) nf nf'.
Proof.
  intros wfΣ a.
  induction a. exists [], []; intuition auto.
  destruct IHa as (nfa & nfa' & (redl & redr) & eq).
  eapply cumul_prop_alt in r as (nf & nf' & ((redl' & redr') & eq'')).
  exists (nf :: nfa), (nf' :: nfa'); intuition auto.
Qed.

Lemma substitution_untyped_cumul_prop_cumul Σ Γ Δ Γ' Δ' s s' M :
  wf_ext Σ -> 
  untyped_subslet Γ s Δ ->
  untyped_subslet Γ s' Δ' ->
  All2 (cumul_prop Σ Γ) s s' ->
  Σ ;;; (Γ ,,, subst_context s 0 Γ') |- (subst s #|Γ'| M) ~~ (subst s' #|Γ'| M).
Proof.
  intros wfΣ subs subs' Heq.
  eapply cumul_prop_args in Heq as (nf & nf' & (redl & redr) & eq) => //.
  eapply cumul_prop_alt.
  eexists (subst nf #|Γ'| M), (subst nf' #|Γ'| M); intuition eauto.
  rewrite -(subst_context_length s 0 Γ').
  eapply red_red => //; eauto.
  rewrite -(subst_context_length s 0 Γ').
  eapply red_red => //; eauto.
  eapply PCUICEquality.eq_term_upto_univ_substs => //.
  reflexivity.
Qed.

Lemma substitution1_untyped_cumul_prop Σ Γ na t u M N :
  wf Σ.1 -> 
  Σ ;;; (Γ ,, vass na t) |- M ~~ N ->
  Σ ;;; Γ |- M {0 := u} ~~ N {0 := u}.
Proof.
  intros wfΣ Hcum.
  eapply (substitution_untyped_cumul_prop Σ Γ [_] []) in Hcum; auto.
  2:repeat constructor.
  eapply Hcum.
Qed.

Lemma is_prop_subst_instance_level u l
  : Universe.is_prop (Universe.make (subst_instance_level u l)) = Universe.is_prop (Universe.make l).
Proof.
  destruct l; simpl; auto.
Qed.

Lemma R_opt_variance_impl Re Rle v x y : 
  subrelation Re Rle ->
  R_universe_instance Re x y ->
  R_opt_variance Re Rle v x y.
Proof.
  intros sub.
  destruct v; simpl; auto.
  intros H. eapply Forall2_map_inv in H.
  induction H in l |- *; simpl; auto.
  destruct l. auto.
  split. destruct t; simpl; auto.
  eauto.
Qed.
  

Lemma cumul_prop_subst_instance_instance Σ univs u u' (i : Instance.t) : 
  wf Σ.1 ->
  consistent_instance_ext Σ univs u ->
  consistent_instance_ext Σ univs u' ->
  R_universe_instance eq_univ_prop (subst_instance u i)
    (subst_instance u' i).
Proof.
  intros wfΣ cu cu'. red.
  eapply All2_Forall2, All2_map.
  unfold subst_instance.
  eapply All2_map. eapply All2_refl.
  intros x. red.
  rewrite !is_prop_subst_instance_level /=. split; reflexivity.
Qed.

Lemma cumul_prop_subst_instance Σ Γ univs u u' T : 
  wf Σ.1 ->
  consistent_instance_ext Σ univs u ->
  consistent_instance_ext Σ univs u' ->
  Σ ;;; Γ |- subst_instance u T ~~ subst_instance u' T.
Proof.
  intros wfΣ cu cu'.
  eapply cumul_prop_alt.
  eexists _, _; intuition eauto.
  induction T using PCUICInduction.term_forall_list_ind; simpl; intros;
    try solve [constructor; eauto; solve_all].
  - constructor. red.
    destruct s; split; reflexivity.
  - constructor. eapply PCUICEquality.eq_term_upto_univ_impl in IHT1; eauto.
    all:try typeclasses eauto.
    apply IHT2.
  - constructor. now eapply cumul_prop_subst_instance_instance.
  - constructor. red. apply R_opt_variance_impl. intros x y; auto.
    now eapply cumul_prop_subst_instance_instance. 
  - constructor. red. apply R_opt_variance_impl. intros x y; auto.
    now eapply cumul_prop_subst_instance_instance.
  - cbn. constructor. splits; simpl; solve_all.
    eapply cumul_prop_subst_instance_instance; tea.
    eapply All2_fold_map. eapply All2_fold_All2.
    eapply All_All2; tea.
    move=> [na [b|] ty]; rewrite /ondecl /map_decl /=.
    * move=> [eqty eqb] /=; constructor; auto.
    * move=> [eqty _] /=; constructor; auto.
    * eapply eq_term_upto_univ_impl; tea. all:tc. reflexivity.
    * eapply All2_map, All_All2; tea. solve_all.
      simpl. eapply All2_fold_map, All2_fold_All2, All_All2; tea.
      clear.
      move=> [na [b|] ty]; rewrite /ondecl /map_decl /=.
      + move=> [eqty eqb] /=; constructor; auto.
      + move=> [eqty _] /=; constructor; auto.
Qed.

Lemma All_All_All2 {A} (P Q : A -> Prop) l l' : 
  All P l -> All Q l' -> #|l| = #|l'| -> All2 (fun x y => P x /\ Q y) l l'.
Proof.
  induction l in l' |- *; destruct l'; simpl; auto => //.
  intros ha hb. specialize (IHl l'); depelim ha; depelim hb.
  constructor; auto.
Qed.

Lemma R_eq_univ_prop_consistent_instances Σ univs u u' : 
  wf Σ.1 ->
  consistent_instance_ext Σ univs u ->
  consistent_instance_ext Σ univs u' ->
  R_universe_instance eq_univ_prop u u'.
Proof.
  intros wfΣ cu cu'.
  destruct univs; simpl in *.
  - destruct u, u' => /= //. red.
    simpl. constructor.
  - intuition.
    eapply Forall2_map.
    eapply All2_Forall2.
    solve_all.
    eapply All2_impl.
    eapply All_All_All2; eauto. lia.
    simpl; intros.
    intuition.
Qed.

Lemma untyped_subslet_inds Γ ind u u' mdecl :
  untyped_subslet Γ (inds (inductive_mind ind) u (ind_bodies mdecl))
    (subst_instance u' (arities_context (ind_bodies mdecl))).
Proof.
  generalize (le_n #|ind_bodies mdecl|).
  generalize (ind_bodies mdecl) at 1 3 4.
  unfold inds.
  induction l using rev_ind; simpl; first constructor.
  simpl. rewrite app_length /= => Hlen.
  unfold arities_context.
  simpl. rewrite /arities_context rev_map_spec /=.
  rewrite map_app /= rev_app_distr /=. 
  rewrite /= Nat.add_1_r /=.
  constructor.
  rewrite -rev_map_spec. apply IHl. lia.
Qed.

Hint Resolve conv_ctx_prop_refl : core.

Lemma cumul_prop_tProd {Σ : global_env_ext} {Γ na t ty na' t' ty'} : 
  wf_ext Σ ->
  eq_binder_annot na na' ->
  eq_term Σ.1 Σ t t' ->
  Σ ;;; Γ ,, vass na t |- ty ~~ ty' ->
  Σ ;;; Γ |- tProd na t ty ~~ tProd na' t' ty'.
Proof.
  intros wfΣ eqann eq cum.
  eapply cumul_prop_alt in cum as (nf & nf' & ((redl & redr) & eq')).
  eapply cumul_prop_alt. eexists (tProd na t nf), (tProd na' t' nf'); intuition eauto.
  eapply red_prod; auto. eapply red_prod; auto.
  eapply red_upto_conv_ctx_prop; eauto.
  repeat (constructor; auto).
  repeat (constructor; auto).
  eapply eq_term_eq_term_prop_impl; auto.
Qed.

Lemma cumul_prop_tLetIn (Σ : global_env_ext) {Γ na t d ty na' t' d' ty'} : 
  wf_ext Σ ->
  eq_binder_annot na na' ->
  eq_term Σ.1 Σ t t' ->
  eq_term Σ.1 Σ d d' ->
  Σ ;;; Γ ,, vdef na d t |- ty ~~ ty' ->
  Σ ;;; Γ |- tLetIn na d t ty ~~ tLetIn na' d' t' ty'.
Proof.
  intros wfΣ eqann eq eq' cum.
  eapply cumul_prop_alt in cum as (nf & nf' & ((redl & redr) & eq'')).
  eapply cumul_prop_alt. 
  assert(eq_context_upto Σ (eq_universe Σ) (eq_universe Σ) (Γ ,, vdef na d t) (Γ ,, vdef na' d' t')).
  { repeat constructor; pcuic. eapply eq_context_upto_refl; typeclasses eauto. }
  eapply red_eq_context_upto_l in redr; eauto. all:try typeclasses eauto.
  destruct redr as [v' [redv' eq''']].
  eexists (tLetIn na d t nf), (tLetIn na' d' t' v'); intuition eauto.
  eapply red_letin; auto. eapply red_letin; auto.
  constructor; eauto using eq_term_eq_term_prop_impl.
  apply eq_term_eq_term_prop_impl; auto.
  apply eq_term_eq_term_prop_impl; auto.
  transitivity nf'. auto. now eapply eq_term_eq_term_prop_impl.
Qed.

Lemma cumul_prop_mkApps (Σ : global_env_ext) {Γ f args f' args'} :
  wf_ext Σ ->
  eq_term Σ.1 Σ f f' ->
  All2 (cumul_prop Σ Γ) args args' ->
  Σ ;;; Γ |- mkApps f args ~~ mkApps f' args'.
Proof.
  intros wfΣ eq eq'.
  eapply cumul_prop_alt.
  eapply cumul_prop_args in eq' as (nf & nf' & (redl & redr) & eq').
  exists (mkApps f nf), (mkApps f' nf'); intuition auto.
  eapply red_mkApps; auto.
  eapply red_mkApps; auto.
  eapply eq_term_upto_univ_mkApps.
  eapply eq_term_upto_univ_impl.
  5:eapply eq. all:auto. 4:lia.
  all:now eapply subrelation_eq_universe_eq_prop.
Qed.

Lemma red_cumul_prop (Σ : global_env_ext) Γ : CRelationClasses.subrelation (red Σ Γ) (cumul_prop Σ Γ).
Proof.
  intros x y r. eapply cumul_prop_alt. exists y, y.
  intuition auto. apply eq_term_upto_univ_refl; typeclasses eauto.
Qed.

Lemma eq_term_prop_mkApps_inv (Σ : global_env_ext) {ind u args ind' u' args'} :
  wf_ext Σ ->
  forall n, eq_term_prop Σ n (mkApps (tInd ind u) args) (mkApps (tInd ind' u') args') ->
  All2 (eq_term_prop Σ 0) args args'.
Proof.
  intros wfΣ. revert args'.
  induction args using rev_ind; intros args' n; simpl.
  intros H; destruct args' using rev_case.
  constructor.
  depelim H. solve_discr. eapply app_eq_nil in H1 as [_ H]. congruence.
  intros H.
  destruct args' using rev_case. depelim H. solve_discr.
  apply app_eq_nil in H1 as [_ H]; discriminate.
  rewrite - !mkApps_nested /= in H. depelim H.
  eapply All2_app => //.
  eapply IHargs; eauto. repeat constructor.
  red. apply H0.
Qed.

Lemma cumul_prop_mkApps_Ind_inv (Σ : global_env_ext) {Γ ind u args ind' u' args'} :
  wf_ext Σ ->
  Σ ;;; Γ |- mkApps (tInd ind u) args ~~ mkApps (tInd ind' u') args' ->
  All2 (cumul_prop Σ Γ) args args'.
Proof.
  intros wfΣ eq.
  eapply cumul_prop_alt in eq as (nf & nf' & (redl & redr) & eq').
  eapply red_mkApps_tInd in redl as [args'' [-> eqargs]].
  eapply red_mkApps_tInd in redr as [args''' [-> eqargs']]. all:auto.
  eapply All2_trans. typeclasses eauto.
  eapply All2_impl; eauto. eapply red_cumul_prop.
  eapply All2_trans. typeclasses eauto.
  2:{ eapply All2_symP. intros x y H; now eapply cumul_prop_sym.
      eapply All2_impl; eauto. eapply red_cumul_prop. } 
  eapply All2_impl; eauto.
  eapply eq_term_prop_mkApps_inv in eq' => //.
  eapply All2_impl; eauto. now constructor.
Qed.

Instance cumul_prop_sym' Σ Γ : wf Σ.1 -> CRelationClasses.Symmetric (cumul_prop Σ Γ).
Proof.
  now intros wf x y; eapply cumul_prop_sym.
Qed.

Notation eq_term_napp Σ n x y :=
  (eq_term_upto_univ_napp Σ (eq_universe Σ) (eq_universe Σ) n x y).

Notation leq_term_napp Σ n x y :=
    (eq_term_upto_univ_napp Σ (eq_universe Σ) (leq_universe Σ) n x y).
    
Lemma eq_term_upto_univ_napp_leq {Σ : global_env_ext} {n x y} :
  eq_term_napp Σ n x y -> 
  leq_term_napp Σ n x y.
Proof.
  eapply eq_term_upto_univ_impl; auto; typeclasses eauto.
Qed.

(** Well-typed terms in the leq_term relation live in the same sort hierarchy. *)
Lemma typing_leq_term_prop (Σ : global_env_ext) Γ t t' T T' :
  wf Σ.1 ->
  Σ ;;; Γ |- t : T ->
  on_udecl Σ.1 Σ.2 ->
  Σ ;;; Γ |- t' : T' ->
  forall n, leq_term_napp Σ n t' t ->
  Σ ;;; Γ |- T ~~ T'.
Proof.
  intros wfΣ Ht.
  revert Σ wfΣ Γ t T Ht t' T'.
  eapply (typing_ind_env 
  (fun Σ Γ t T =>
  forall t' T' : term,
  on_udecl Σ.1 Σ.2 ->
  Σ;;; Γ |- t' : T' ->
  forall n, leq_term_napp Σ n t' t ->
  Σ ;;; Γ |- T ~~ T')%type 
  (fun Σ Γ => wf_local Σ Γ)); auto;intros Σ wfΣ Γ wfΓ; intros.

  1-13:match goal with
  [ H : leq_term_napp _ _ _ _ |- _ ] => depelim H
  end; assert (wf_ext Σ) by (split; assumption).

  14:{ specialize (X1 _ _ H X5 _ X6).
      now eapply cumul_prop_cum_l. }

  6:{ eapply inversion_App in X6 as (na' & A' & B' & hf & ha & cum); auto.
      specialize (X3 _ _ H hf _ X7_1).
      specialize (X5 _ _ H ha _ (eq_term_upto_univ_napp_leq X7_2)).
      eapply cumul_cumul_prop in cum; auto.
      transitivity (B' {0 := u0}) => //.
      eapply cumul_prop_prod_inv in X3 => //.
      transitivity (B' {0 := u}).
      now eapply substitution1_untyped_cumul_prop in X3.
      constructor.
      eapply eq_term_eq_term_prop_impl => //.
      eapply PCUICEquality.eq_term_upto_univ_substs.
      all:try typeclasses eauto. 
      eapply PCUICEquality.eq_term_upto_univ_refl. all:try typeclasses eauto.
      constructor. 2:constructor. now symmetry. }

  - eapply inversion_Rel in X0 as [decl' [wfΓ' [Hnth Hcum]]]; auto.
    rewrite Hnth in H; noconf H. now eapply cumul_cumul_prop in Hcum.

  - eapply inversion_Sort in X0 as [wf [wfs Hs]]; auto.
    apply subrelation_leq_universe_eq_prop in x => //.
    apply cumul_cumul_prop in Hs => //.
    eapply cumul_prop_trans; eauto.
    constructor. constructor. symmetry.
    split; split; intros H'. 1,2:now eapply is_prop_superE in H'.
    1,2:now eapply is_sprop_superE in H'.

  - eapply inversion_Prod in X4 as [s1' [s2' [Ha [Hb Hs]]]]; auto.
    specialize (X1 _ _ H Ha). 
    specialize (X1 _ (eq_term_upto_univ_napp_leq X5_1)).
    eapply context_conversion in Hb. 3:{ constructor. apply conv_ctx_refl. constructor. eassumption.
      constructor. eauto. }
    all:eauto.
    2:{ constructor; eauto. now exists s1. }
    specialize (X3 _ _ H Hb _ X5_2).
    eapply cumul_cumul_prop in Hs => //.
    eapply cumul_prop_trans; eauto.
    constructor. constructor.
    red.
    split.
    split; intros Hs'; apply is_prop_sort_prod in Hs'; eapply is_prop_prod; eapply cumul_prop_props; eauto.
    now eapply cumul_prop_sym; eauto.
    split; intros Hs'; apply is_sprop_sort_prod in Hs'; eapply is_sprop_prod; eapply cumul_sprop_props; eauto.
    now eapply cumul_prop_sym; eauto.

  - eapply inversion_Lambda in X4 as (s & B & dom & bod & cum).
    specialize (X1 _ _ H dom _ (eq_term_upto_univ_napp_leq X5_1)).
    specialize (X3 t0 B H). 
    assert(conv_context Σ (Γ ,, vass na ty) (Γ ,, vass n t)).
    { repeat constructor; pcuic. }
    forward X3 by eapply context_conversion; eauto; pcuic.
    specialize (X3 _ X5_2). eapply cumul_cumul_prop in cum; eauto.
    eapply cumul_prop_trans; eauto.
    eapply cumul_prop_tProd; eauto. now symmetry. now symmetry. auto.

  - eapply inversion_LetIn in X6 as (s1' & A & dom & bod & codom & cum); auto.
    specialize (X1 _ _ H dom _ (eq_term_upto_univ_napp_leq X7_2)).
    specialize (X3 _ _ H bod _  (eq_term_upto_univ_napp_leq X7_1)).
    assert(conv_context Σ (Γ ,, vdef na t ty) (Γ ,, vdef n b b_ty)).
    { repeat constructor; pcuic. }
    specialize (X5 u A H).
    forward X5 by eapply context_conversion; eauto; pcuic.
    specialize (X5 _ X7_3).
    eapply cumul_cumul_prop in cum; eauto.
    eapply cumul_prop_trans; eauto.
    eapply cumul_prop_tLetIn; auto; now symmetry.

  - eapply inversion_Const in X1 as [decl' [wf [declc [cu cum]]]]; auto.
    eapply cumul_cumul_prop in cum; eauto.
    eapply cumul_prop_trans; eauto.
    pose proof (PCUICWeakeningEnv.declared_constant_inj _ _ H declc); subst decl'.
    eapply cumul_prop_subst_instance; eauto.

  - eapply inversion_Ind in X1 as [decl' [idecl' [wf [declc [cu cum]]]]]; auto.
    pose proof (PCUICWeakeningEnv.declared_inductive_inj isdecl declc) as [-> ->].
    eapply cumul_cumul_prop in cum; eauto.
    eapply cumul_prop_trans; eauto. do 2 red in H.
    now eapply cumul_prop_subst_instance.

  - eapply inversion_Construct in X1 as [decl' [idecl' [cdecl' [wf [declc [cu cum]]]]]]; auto.
    pose proof (PCUICWeakeningEnv.declared_constructor_inj isdecl declc) as [-> [-> ->]].
    eapply cumul_cumul_prop in cum; eauto.
    eapply cumul_prop_trans; eauto.
    unfold type_of_constructor.
    etransitivity. 
    eapply (substitution_untyped_cumul_prop_equiv _ Γ (subst_instance u (arities_context mdecl.(ind_bodies))) []); auto.
    eapply untyped_subslet_inds. eapply (untyped_subslet_inds _ ind u0 u).
    simpl. generalize (ind_bodies mdecl).
    induction l; simpl; constructor; auto.
    constructor. simpl. eapply R_opt_variance_impl. now intros x.
    eapply R_eq_univ_prop_consistent_instances; eauto. simpl.
    eapply (substitution_untyped_cumul_prop _ Γ (subst_instance u0 (arities_context mdecl.(ind_bodies))) []) => //.
    eapply untyped_subslet_inds. simpl.
    eapply cumul_prop_subst_instance => //; eauto.

  - eapply inversion_Case in X10 as (mdecl' & idecl' & isdecl' & indices' & data & cum); auto.
    eapply cumul_cumul_prop in cum; eauto.
    eapply cumul_prop_trans; eauto. simpl.
    clear X9.
    destruct data.
    todo "case".
    (*specialize (X8 _ _ H4 t0 _ (eq_term_upto_univ_napp_leq X11)).
    eapply cumul_prop_sym => //.
    eapply cumul_prop_mkApps => //.
    eapply cumul_prop_mkApps => //. rewrite /ptm /predctx.
    eapply All2_app. 2:(repeat constructor; auto using eq_term_eq_term_prop_impl).
    eapply All2_skipn. eapply cumul_prop_mkApps_Ind_inv in X4 => //.
    eapply cumul_prop_mkApps_Ind_inv in X6 => //.
    eapply All2_app_inv_l in X6 as (?&?&?&?&?).
    eapply All2_symP => //. typeclasses eauto.
    move: (All2_length a3). destruct e.
    rewrite -(All2_length a5) => hpars.
    eapply app_inj in e2 as [eql ->] => //.*)
    
  - eapply inversion_Proj in X3 as (u' & mdecl' & idecl' & pdecl' & args' & inv); auto.
    intuition auto.
    specialize (X2 _ _  H0 a0 _ (eq_term_upto_univ_napp_leq X4)).
    eapply eq_term_upto_univ_napp_leq in X4.
    eapply cumul_cumul_prop in b; eauto.
    eapply cumul_prop_trans; eauto.
    eapply cumul_prop_mkApps_Ind_inv in X2 => //.
    destruct (PCUICWeakeningEnv.declared_projection_inj a isdecl) as [<- [<- <-]].
    subst ty. 
    transitivity (subst0 (c0 :: List.rev args') (subst_instance u pdecl'.2)).
    eapply (substitution_untyped_cumul_prop_cumul Σ Γ (projection_context mdecl idecl p.1.1 u) []) => //.
    epose proof (projection_subslet Σ _ _ _ _ _ _ _ _ isdecl wfΣ X1).
    eapply subslet_untyped_subslet. eapply X3, validity; eauto.
    epose proof (projection_subslet Σ _ _ _ _ _ _ _ _ a wfΣ a0).
    eapply subslet_untyped_subslet. eapply X3, validity; eauto.
    constructor => //. symmetry; constructor => //.
    now eapply leq_term_eq_term_prop_impl.
    now eapply All2_rev.
    eapply (substitution_untyped_cumul_prop Σ Γ (projection_context mdecl idecl p.1.1 u') []) => //.
    epose proof (projection_subslet Σ _ _ _ _ _ _ _ _ a wfΣ a0).
    eapply subslet_untyped_subslet. eapply X3, validity; eauto.
    destruct a.
    eapply validity, (isType_mkApps_Ind wfΣ H1) in X1 as [ps [argss [_ cu]]]; eauto.
    eapply validity, (isType_mkApps_Ind wfΣ H1) in a0 as [? [? [_ cu']]]; eauto.
    eapply cumul_prop_subst_instance; eauto.

  - eapply inversion_Fix in X2 as (decl' & fixguard' & Hnth & types' & bodies & wffix & cum); auto.
    eapply cumul_cumul_prop in cum; eauto.
    eapply cumul_prop_trans; eauto.
    eapply All2_nth_error in a; eauto.
    destruct a as [[[a _] _] _].
    constructor. eapply eq_term_eq_term_prop_impl; eauto.
    now eapply eq_term_sym in a.
  
  - eapply inversion_CoFix in X2 as (decl' & fixguard' & Hnth & types' & bodies & wfcofix & cum); auto.
    eapply cumul_cumul_prop in cum; eauto.
    eapply cumul_prop_trans; eauto.
    eapply All2_nth_error in a; eauto.
    destruct a as [[[a _] _] _].
    constructor. eapply eq_term_eq_term_prop_impl; eauto.
    now eapply eq_term_sym in a.
Qed.

End no_prop_leq_type.
