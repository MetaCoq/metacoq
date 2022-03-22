(* Distributed under the terms of the MIT license. *)
From Coq Require Import Program ssreflect ssrbool.
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
Import MCMonadNotation.

From Equations Require Import Equations.
Set Equations Transparent.
Local Set Keyed Unification.
Require Import ssreflect.

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
(* 
Lemma wf_local_map2_set_binder_name {cf Σ} {wfΣ : wf Σ} {Γ nas Δ} : 
  #|nas| = #|Δ| ->
  wf_local Σ (Γ ,,, map2 set_binder_name nas Δ) <~> wf_local Σ (Γ ,,, Δ).
Proof.
  induction nas in Δ |- *; destruct Δ; cbn => //.
  intros [=]. split; intros; try constructor; eauto.
  - destruct c as [na [b|] ty]; cbn in *; depelim X. red in l, l0. cbn in *.
    constructor; auto. apply IHnas; auto.
    red.
    destruct l as [s Hs].
    exists s. eapply PCUICContextConversion.context_conversion; tea; eauto.
    now eapply IHnas.
    eapply eq_context_alpha_conv


  intros wfΓ eqctx wf.
  apply wf_local_app_inv.
  eapply wf_local_app in wf => //.
  eapply PCUICInductiveInversion.wf_local_alpha; tea.
  eapply All2_app => //. reflexivity.
Qed. *)

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
(* To debug performance issues *)
(* 
Axiom time : forall {A}, string -> (unit -> A) -> A.
Axiom time_id : forall {A} s (f : unit -> A), time s f = f tt.

Extract Constant time =>
"(fun c x -> let time = Unix.gettimeofday() in
                            let temp = x () in
                            let time = (Unix.gettimeofday() -. time) in
              Feedback.msg_debug (Pp.str (Printf.sprintf ""Time elapsed in %s:  %f"" ((fun s-> (String.concat """" (List.map (String.make 1) s))) c) time));
              temp)". *)


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

  Equations(noeqns noind) is_arity Γ (HΓ : forall Σ0 : global_env_ext, abstract_env_rel' Σ Σ0 -> ∥wf_local Σ0 Γ∥) T (HT : forall Σ0 : global_env_ext, abstract_env_rel' Σ Σ0 -> welltyped Σ0 Γ T) :
    {Is_conv_to_Arity Σ Γ T} + {~ Is_conv_to_Arity Σ Γ T}
    by wf ((Γ;T;HT) : (∑ Γ t, forall Σ0 : global_env_ext, abstract_env_rel' Σ Σ0 -> welltyped Σ0 Γ t)) term_rel :=
    {
      is_arity Γ HΓ T HT with inspect (@reduce_to_sort _ _ optimized_abstract_env_ext_impl Σ Γ T HT) => {
      | exist (Checked_comp H) rsort => left _ ;
      | exist (TypeError_comp _) rsort with inspect (reduce_to_prod Γ T _) => {
        | exist (Checked_comp (na; A; B; H)) rprod with is_arity (Γ,, vass na A) _ B _ :=
          { | left isa => left _;
            | right nisa => right _ };
        | exist (TypeError_comp e) rprod => right _ } }
    }.
  Next Obligation. econstructor. clear rsort is_arity. 
    assert (wfΣ' : abstract_env_rel' Σ Σ) by reflexivity. 
    pose proof (abstract_env_ext_wf _ wfΣ') as [wf]. 
    specialize_Σ wfΣ'.
    split. sq. eassumption. econstructor.
  Qed.
  Next Obligation. exact optimized_abstract_env_ext_impl. Defined.  
  Next Obligation. eauto. Defined.  
  Next Obligation. unfold  is_arity_obligations_obligation_3.
  assert (wfΣ' : abstract_env_rel' Σ Σ) by reflexivity.
  exact (HT _ wfΣ'). Defined.
  Next Obligation.
    clear rprod. assert (wfΣ' : abstract_env_rel' Σ Σ) by reflexivity.
    pose proof (abstract_env_ext_wf _ wfΣ') as [wf]. 
    specialize_Σ wfΣ'.
    destruct (HT _ wfΣ') as []; sq.
    eapply subject_reduction_closed in X; eauto.
    eapply inversion_Prod in X as (? & ? & ? & ? & ?).
    econstructor; eauto; cbn; eauto. auto.
  Qed.
  Next Obligation.
    clear rprod.  assert (wfΣ' : abstract_env_rel' Σ Σ) by reflexivity.
    pose proof (abstract_env_ext_wf _ wfΣ') as [wf]. 
    specialize_Σ wfΣ'.
    sq. destruct (HT _ wfΣ') as [].
    eapply subject_reduction_closed in X; eauto.
    eapply inversion_Prod in X as (? & ? & ? & ? & ?).
    eexists; eauto. auto.
  Qed.
  Next Obligation.
  assert (wfΣ' : abstract_env_rel' Σ Σ) by reflexivity.
  pose proof (H _ wfΣ'). sq. repeat eexists. exact X.
  Qed.
  Next Obligation.
    destruct isa as (? & ? & ?). 
    assert (wfΣ' : abstract_env_rel' Σ Σ) by reflexivity.
    pose proof (H _ wfΣ'). eexists (tProd _ _ _). split; sq.
    etransitivity. exact c. eapply closed_red_prod_codom; tea.
    eassumption.
  Qed.
  Next Obligation.
    clear rprod. assert (wfΣ' : abstract_env_rel' Σ Σ) by reflexivity.
    pose proof (H _ wfΣ'). 
    destruct HΣ as [wΣ].
    destruct H0 as (? & ? & ?). sq.
    edestruct (PCUICContextConversion.closed_red_confluence X0 X) as (? & ? & ?); eauto.
    eapply invert_red_prod in c0 as (? & ? & []); eauto. subst.
    apply nisa.

    eapply invert_cumul_arity_l in H2.
    2:eapply red_ws_cumul_pb; tea.
    destruct H2 as (? & ? & ?). sq.

    eapply invert_red_prod in X1 as (? & ? & []); eauto. subst. cbn in *.
    exists x4; split; eauto.

    constructor.
    etransitivity; eauto.
    eapply into_closed_red.
    eapply PCUICRedTypeIrrelevance.context_pres_let_bodies_red; [|exact c3].
    econstructor; [|econstructor].
    eapply All2_fold_refl. intros ? ?; reflexivity. fvs.
    now eapply clrel_src in c3.
  Qed.

  Next Obligation.
    pose proof (reduce_to_sort_complete (X_type := optimized_abstract_env_ext_impl) _ eq_refl _ a0 (eq_sym rsort));
    pose proof (reduce_to_prod_complete (X_type := optimized_abstract_env_ext_impl)  _ eq_refl _ e (eq_sym rprod)).
    destruct HΣ.
    apply Is_conv_to_Arity_inv in H as [(?&?&?&[r])|(?&[r])]; eauto.
    - eapply H1, r.
    - eapply H0; eapply r.     
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

Opaque type_of_typing.

Program Definition is_erasable (Σ : wf_env_ext) (Γ : context) (t : PCUICAst.term) 
  (wt : forall Σ0 : global_env_ext, abstract_env_rel' Σ Σ0 -> welltyped Σ0 Γ t) :
  ({∥isErasable Σ Γ t∥} + {∥(isErasable Σ Γ t -> False)∥}) :=
  let T := @type_of_typing extraction_checker_flags _ optimized_abstract_env_ext_impl Σ Γ t wt in
  let b := is_arity Σ Γ _ T.π1 _ in
  match b : {_} + {_} return _ with
  | left _ => left _
  | right _ => let K := @type_of_typing extraction_checker_flags _ optimized_abstract_env_ext_impl _ Γ T.π1 _ in
       match reduce_to_sort (X_type := optimized_abstract_env_ext_impl) (X := Σ) Γ K.π1 _ with
       | Checked_comp (u; Hu) =>
          match is_propositional u with true => left _ | false => right _ end
       | TypeError_comp _ _ => False_rect _ _
       end
  end.

Next Obligation. 
  assert (wfΣ' : abstract_env_rel' Σ Σ) by reflexivity.
  destruct (wt _ wfΣ'); sq; eauto. pcuic. Qed.
Next Obligation.
  assert (wfΣ' : abstract_env_rel' Σ Σ) by reflexivity.
  pose proof (abstract_env_ext_wf _ wfΣ') as [wf]. 
  sq.  
  destruct type_of_typing as [T HT]. cbn.   
  specialize_Σ wfΣ'. sq. destruct X as [HT _]. eapply validity in HT; pcuic.
Qed.
Next Obligation.
  destruct type_of_typing as [x Hx]. cbn in *.  
  assert (wfΣ' : abstract_env_rel' Σ Σ) by reflexivity.
  pose proof (abstract_env_ext_wf _ wfΣ') as [wf]. 
  specialize_Σ wfΣ'. destruct Hx as [[HT ?]]. 
  destruct H as [T' [redT' isar]].
  destruct wt as [T ht].
  sq. cbn in X. eapply type_reduction_closed in X; eauto.
  now exists T'.
Qed.
Next Obligation. eauto. Defined.
Next Obligation.  
  destruct type_of_typing as [x Hx]; cbn in *.
  assert (wfΣ' : abstract_env_rel' Σ Σ) by reflexivity.
  pose proof (abstract_env_ext_wf _ wfΣ') as [wf]. 
  specialize_Σ wfΣ'. destruct Hx as [[Hx ?]]. 
  sq. destruct wt. cbn in H.
  now eapply validity in Hx; pcuic.
Qed.
Next Obligation.
  match goal with | |- welltyped _ _ ?X.π1 => set (tot := X) end. 
  destruct tot as [T HT]; cbn in *.
  assert (wfΣ' : abstract_env_rel' Σ Σ) by reflexivity. clear H. 
  pose proof (abstract_env_ext_wf _ wfΣ') as [wf]. 
  specialize_Σ wfΣ'. pose (wt _ wfΣ'); destruct HT as [[HT ?]]. 
  sq. destruct wt.
  eapply validity in HT; pcuic.
Qed.
Next Obligation.
  destruct reduce_to_sort; try discriminate.
  destruct a as [u' Hu'].
  destruct (type_of_typing _ _ _ _.π1 _) as [? ? ].
  cbn in *. 
  destruct (type_of_typing _ _ _ _) as [? ?].
  simpl in *. 
  assert (wfΣ' : abstract_env_rel' Σ Σ) by reflexivity. clear H. 
  pose proof (abstract_env_ext_wf _ wfΣ') as [wf]. 
  clear Heq_anonymous0. specialize_Σ wfΣ'. 
  destruct wt.
  sq. red. exists x0 ; split; intuition eauto. 
  pose proof (PCUICContextConversion.closed_red_confluence X1 X0) as [v' [redl redr]].
  eapply invert_red_sort in redl.
  eapply invert_red_sort in redr. subst. noconf redr.
  right. exists u; split; eauto.
  eapply type_reduction_closed; eauto using typing_wf_local.
Qed.
Next Obligation.
  unfold type_of in *.
  destruct reduce_to_sort; try discriminate.
  destruct (type_of_typing _ _ _ _.π1 _) as [? ? ].
  cbn in *. 
  destruct (type_of_typing _ _ _ _) as [? ?].
  destruct a as [u' redu']. simpl in *.
  assert (wfΣ' : abstract_env_rel' Σ Σ) by reflexivity.
  pose proof (abstract_env_ext_wf _ wfΣ') as [wf]. 
  clear Heq_anonymous0. specialize_Σ wfΣ'. 
  sq. 
  pose proof (PCUICContextConversion.closed_red_confluence X0 X) as [v' [redl redr]].
  destruct X1.  eapply invert_red_sort in redl.
  destruct X2; red in p, p0.
  eapply invert_red_sort in redr. subst. noconf redr.
  intros (? & ? & ?).
  destruct s as [ | (? & ? & ?)]; simpl in *.
  + match goal with [ H : ~ Is_conv_to_Arity _ _ _ |- _ ] => destruct H end.
    eapply arity_type_inv; eauto using typing_wf_local. 
  + pose proof (p0 _ t2).
    eapply type_reduction_closed in t0; eauto.
    eapply cumul_prop1' in t3; eauto.
    eapply leq_term_propositional_sorted_l in t0; eauto.
    2:reflexivity.
    2:eapply validity; eauto.
    eapply leq_universe_propositional_r in t0; auto. congruence.
    apply wf.
Qed. 
Next Obligation.
  unfold type_of in *.
  sq.
  symmetry in Heq_anonymous.
  pose proof (reduce_to_sort_complete (X_type := optimized_abstract_env_ext_impl) (X := Σ) _ eq_refl _ _ Heq_anonymous).
  clear Heq_anonymous.
  assert (wfΣ' : abstract_env_rel' Σ Σ) by reflexivity.
  pose proof (abstract_env_ext_wf _ wfΣ') as [wf]. 
  destruct (type_of_typing _ _ _ _.π1 _) as [? ?]. cbn in *.
  specialize_Σ wfΣ'.   destruct s as [[? pt]].
  destruct (type_of_typing _ _ _ _) as [? ?]. cbn in *. 
  specialize_Σ wfΣ'. destruct s as [[t1 p]].
  simpl in *. 
  eapply validity in t1; auto.
  destruct t1 as [s Hs].
  red in p, pt.
  specialize (pt _ Hs).
  eapply ws_cumul_pb_Sort_r_inv in pt as [u' [redu' leq]].
  match goal with [ H : forall s, _ -> False |- _ ] => now apply (H _ redu') end.
Qed.

Transparent type_of_typing.

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
  
  Opaque is_erasable.
  Definition is_erasableb (Σ : wf_env_ext) (Γ : context) (t : term) 
    (wt : forall Σ0 : global_env_ext, abstract_env_rel' Σ Σ0 -> welltyped Σ0 Γ t) : bool :=
    match is_erasable Σ Γ t wt with
    | left _ => true
    | right _ => false
    end.
  Definition inspect {A} (x : A) : { y : A | x = y } := exist x eq_refl.

  Obligation Tactic := idtac.
  Equations? erase (Γ : context) (t : term) 
    (Ht : forall Σ0 : global_env_ext, abstract_env_rel' Σ Σ0 -> welltyped Σ0 Γ t) : E.term
      by struct t :=
  { erase Γ t Ht with inspect (is_erasableb Σ Γ t Ht) :=
  { | exist true he := E.tBox; 
    | exist false he with t := {
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
        let mfix' := erase_mfix Γ' mfix _ in
        E.tFix mfix' n
      | tCoFix mfix n :=
        let Γ' := (fix_context mfix ++ Γ)%list in
        let mfix' := erase_mfix Γ' mfix _ in
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
  where erase_mfix (Γ : context) (mfix : mfixpoint term)
    (Ht : forall Σ0 : global_env_ext, abstract_env_rel' Σ Σ0 ->
          ∥ All (fun d => welltyped Σ0 Γ d.(dbody)) mfix ∥) : E.mfixpoint E.term :=
  { erase_mfix Γ [] _ := [];
    erase_mfix Γ (d :: mfix) Hmfix := 
      let dbody' := erase Γ d.(dbody) _ in
      let d' := {| E.dname := d.(dname).(binder_name); E.rarg := d.(rarg); E.dbody := dbody' |} in
      d' :: erase_mfix Γ mfix _ }
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
    - unfold is_erasableb in he. destruct is_erasable => //. 
      specialize_Σ wfΣ'. destruct Ht as [ty Ht].   sq. apply H.
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
      sq. eapply All_impl; tea. cbn. intros d Ht; now eexists.
    - eapply inversion_CoFix in Ht as (? & ? & ? & ? & ? & ?); auto.
      sq. eapply All_impl; tea. cbn. intros d Ht; now eexists.
    - sq. now depelim X.
    - sq. now depelim X.
    - sq. now depelim X.
    - sq. now depelim X.
    - sq. now depelim X.
    - sq. now depelim X.
  Qed.
  
End Erase.

Lemma is_erasableb_irrel {Σ Γ t} wt wt' : is_erasableb Σ Γ t wt = is_erasableb Σ Γ t wt'.
Proof.
  unfold is_erasableb.
  destruct is_erasable, is_erasable; simp erase; try reflexivity;
  sq; try (exfalso; tauto).
Qed.

Ltac iserasableb_irrel :=
  match goal with
  [ H : is_erasableb ?Σ ?Γ ?t ?wt = _, He : inspect _ = _ |- context [ is_erasableb _ _ _ ?wt'] ] => 
    generalize dependent H; rewrite (is_erasableb_irrel wt wt'); intros; rewrite He
  end.

Ltac simp_erase := simp erase; rewrite -?erase_equation_1.

Lemma erase_irrel (Σ : wf_env_ext) : 
  (forall Γ t wt, forall wt', erase Σ Γ t wt = erase Σ Γ t wt') ×
  (forall Γ l wt, forall wt', erase_terms Σ Γ l wt = erase_terms Σ Γ l wt') ×
  (forall Γ p l wt, forall wt', erase_brs Σ Γ p l wt = erase_brs Σ Γ p l wt') ×
  (forall Γ l wt, forall wt', erase_mfix Σ Γ l wt = erase_mfix Σ Γ l wt').
Proof.
  apply: (erase_elim Σ
    (fun Γ t wt e => 
      forall wt' : forall Σ0 : global_env_ext, abstract_env_rel' Σ Σ0 ->  welltyped Σ0 Γ t, e = erase Σ Γ t wt')
    (fun Γ l awt e => forall wt', e = erase_terms Σ Γ l wt')
    (fun Γ p l awt e => forall wt', e = erase_brs Σ Γ p l wt')
    (fun Γ l awt e => forall wt', e = erase_mfix Σ Γ l wt')); clear.
  all:intros *; intros; simp_erase.
  all:try simp erase; try iserasableb_irrel; simp_erase => //.
  all:try clear he Heq.
  all:try bang.
  all:try solve [cbn; f_equal; eauto].
  all:try solve [cbn; repeat (f_equal; eauto)].
Qed.

Section map_All.
  Context {A B C} {Q : C -> Type} {P : C -> A  -> Prop} 
    (fn : forall (x : A) , (forall (y:C),  Q y -> P y x) -> B).
  
  Equations? map_All  (l : list A) (Hl : forall y, Q y -> ∥ All (P y) l ∥) : list B :=
  | [], _ := []
  | x :: xs, h := fn x _ :: map_All xs _.
  Proof. all:clear fn map_All.
    - specialize (h y X). sq. now depelim X0.
    - specialize (h y X). sq. now depelim X0.
  Qed.
End map_All.

Lemma erase_terms_eq Σ Γ ts wt : 
  erase_terms Σ Γ ts wt = map_All (erase Σ Γ) ts wt.
Proof.
  funelim (map_All (erase Σ Γ) ts wt); cbn; auto.
  f_equal => //. apply erase_irrel.
  rewrite -H. eapply erase_irrel.
Qed.

Opaque wf_reduction.
Arguments iswelltyped {cf Σ Γ t A}.
#[global]
Hint Constructors typing erases : core.

Lemma isType_isErasable Σ Γ T : isType Σ Γ T -> isErasable Σ Γ T.
Proof.
  intros [s Hs].
  exists (tSort s). intuition auto. left; simpl; auto.
Qed.

Lemma is_box_mkApps f a : is_box (E.mkApps f a) = is_box f.
Proof.
  now rewrite /is_box EAstUtils.head_mkApps.
Qed.

Lemma is_box_tApp f a : is_box (E.tApp f a) = is_box f.
Proof.
  now rewrite /is_box EAstUtils.head_tApp.
Qed.

Lemma is_erasableb_reflect (Σ : wf_env_ext) Γ t wt : reflect (∥ isErasable Σ Γ t ∥) (is_erasableb Σ Γ t wt).
Proof.
  unfold is_erasableb. destruct is_erasable; constructor => //.
  intros. sq. intro. sq. now contradiction.
Qed.

Lemma erase_to_box {Σ : wf_env_ext} {Γ t} (wt : forall Σ0 : global_env_ext, abstract_env_rel' Σ Σ0 -> welltyped Σ0 Γ t) :
  let et := erase Σ Γ t wt in 
  if is_box et then ∥ isErasable Σ Γ t ∥
  else ∥ isErasable Σ Γ t ∥ -> False.
Proof.
  cbn.
  revert Γ t wt.
  apply (erase_elim Σ
    (fun Γ t wt e => 
      if is_box e then ∥ isErasable Σ Γ t ∥ else ∥ isErasable Σ Γ t ∥ -> False)
    (fun Γ l awt e => True)
    (fun Γ p l awt e => True)
    (fun Γ l awt e => True)); intros.

  all:try discriminate; auto.
  all:try solve [match goal with 
    [ H : is_erasableb ?Σ ?Γ ?t ?Ht = _ |- _ ] => 
      destruct (is_erasableb_reflect Σ Γ t Ht) => //
  end].
  all:try bang.
  - cbn. rewrite is_box_tApp.
    destruct (is_erasableb_reflect Σ Γ (tApp f u) Ht) => //.
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
     (binder_name (dname d) = E.dname d') *
     (rarg d = E.rarg d'
      × Σ;;; Γ |- dbody d ⇝ℇ E.dbody d')) l e)); intros.
    all:try discriminate.
    all:try bang.
    all:try match goal with 
      [ H : is_erasableb ?Σ ?Γ ?t ?Ht = _ |- _ ] => 
        destruct (is_erasableb_reflect Σ Γ t Ht) as [[H']|H'] => //;
        try now eapply erases_box
    end.
    all: try solve [constructor; eauto].
  all:try destruct Σ.(wf_env_ext_wf) as [wfΣ].
  all: cbn in *; assert (wfΣ' : abstract_env_rel' Σ Σ) by reflexivity;
  pose proof (abstract_env_ext_wf _ wfΣ') as [wf];
  specialize_Σ wfΣ'.
  
  - constructor. clear Heq.
    eapply nisErasable_Propositional in Ht; auto.

  - cbn.
    constructor; auto. 
    destruct (Ht _ wfΣ').
    destruct (inversion_Case _ _ X0) as [mdecl [idecl []]]; eauto.
    eapply elim_restriction_works; eauto.
    intros isp. eapply isErasable_Proof in isp. eauto.

  - constructor; auto. clear Heq.
    destruct (Ht _ wfΣ') as [? Ht'].
    clear H. eapply inversion_Proj in Ht' as (?&?&?&?&?&?&?&?&?&?); auto.
    eapply elim_restriction_works_proj; eauto. exact d.
    intros isp. eapply isErasable_Proof in isp; eauto.
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
  sq. red in X. rewrite <-Heq_anonymous in X. simpl in X.
  eexists; eauto.
Qed.

Definition erase_one_inductive_body (oib : one_inductive_body) : E.one_inductive_body :=
  (* Projection and constructor types are types, hence always erased *)
  let ctors := map (fun cdecl => (cdecl.(cstr_name), cdecl.(cstr_arity))) oib.(ind_ctors) in
  let projs := map (fun '(x, y) => x) oib.(ind_projs) in
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
  rewrite H0 -H1. reflexivity.
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

(* Next Obligation.
  pose proof (wf_ext_gc_of_uctx prf) as [uctx' isg].
  move: isg.
  rewrite /uGraph.gc_of_uctx /=.
  rewrite /global_ext_constraints /=.
  pose proof (uGraph.gc_of_constraints_union (constraints_of_udecl univs) (global_constraints Σ)).
  rewrite -Heq_anonymous /= in H. red in H.
  destruct (uGraph.gc_of_constraints
      (ConstraintSet.union (constraints_of_udecl univs)
        (global_constraints Σ))) => //.
Qed. *)

(* Next Obligation.
  set (foo := (fun H => False_rect _ (make_wf_env_ext_obligation_2 _ _ _ H))). clearbody foo.
  destruct gc_of_constraints eqn:eqgc => //.
  - rewrite /global_ext_uctx /global_ext_constraints /=.
    pose proof (wf_ext_gc_of_uctx prf) as [uctx' isg].
    destruct prf.
    move: isg.
    pose proof (wfG := Σ.(wf_env_graph_wf)).
    rewrite /uGraph.is_graph_of_uctx /=.
    destruct uGraph.gc_of_uctx eqn:gc => //.
    intros [= <-]. cbn.
    move: gc.
    rewrite /global_ext_uctx /= /global_ext_levels /=.
    rewrite /global_ext_constraints /=.
    set (G := Σ.(wf_env_graph)) in *.
    pose proof (uGraph.gc_of_constraints_union (constraints_of_udecl univs) (global_constraints Σ)).
    rewrite eqgc /= in H. red in H.
    red in wfG.
    unfold uGraph.gc_of_uctx. simpl.
    unfold global_uctx in wfG. unfold uGraph.gc_of_uctx in wfG. simpl in wfG.
    destruct (uGraph.gc_of_constraints
      (ConstraintSet.union (constraints_of_udecl univs)
        (global_constraints Σ))) => //.
    intros [= <-].
    destruct (uGraph.gc_of_constraints (global_constraints Σ)) eqn:gc => //.
    cbn in wfG. symmetry. rewrite -wfG H. 
    now eapply uGraph.add_uctx_make_graph.
  - symmetry in eqgc. now elim (make_wf_env_ext_obligation_2 _ _ prf eqgc).
Qed. *)

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

Lemma wf_gc_of_uctx {cf:checker_flags} {Σ : global_env} (HΣ : ∥ wf Σ ∥)
  : {uctx' | uGraph.gc_of_uctx (global_uctx Σ) = Some uctx' }.
Proof.
  assert (consistent (global_uctx Σ).2) as HC.
  { sq => //. apply X. }
  destruct Σ as [Σ φ].
  simpl in HC.
  unfold uGraph.gc_of_uctx; simpl in *.
  apply uGraph.gc_consistent_iff in HC.
  destruct uGraph.gc_of_constraints.
  eexists; reflexivity.
  contradiction HC.
Defined.

Lemma graph_of_wf {cf:checker_flags} {Σ : global_env} (wfΣ : ∥ wf Σ ∥) : 
  { G | uGraph.is_graph_of_uctx G (global_uctx Σ) }.
Proof.
  destruct (wf_gc_of_uctx wfΣ) as [uctx Huctx] => //.
  exists (uGraph.make_graph uctx). unfold uGraph.is_graph_of_uctx. now rewrite Huctx.
Defined.

Definition build_wf_env {cf : checker_flags} (Σ : global_env) (wfΣ : ∥ wf Σ ∥) : wf_env := 
  {| wf_env_referenced := {| referenced_impl_env := Σ ; referenced_impl_wf := wfΣ;  |} ; 
     wf_env_map := EnvMap.EnvMap.of_global_env Σ.(declarations); 
     wf_env_map_repr := EnvMap.EnvMap.repr_global_env Σ.(declarations); |}.

Definition erase_global deps Σ :=
  erase_global_decls deps Σ Σ.(declarations) eq_refl.

Definition global_erased_with_deps (Σ : global_env) (Σ' : EAst.global_declarations) kn :=
  (exists cst, declared_constant Σ kn cst /\
   exists cst' : EAst.constant_body,
    ETyping.declared_constant Σ' kn cst' /\
    erases_constant_body (Σ, cst_universes cst) cst cst' /\
    (forall body : EAst.term,
     EAst.cst_body cst' = Some body -> erases_deps Σ Σ' body)) \/
  (exists mib mib', declared_minductive Σ kn mib /\ 
    ETyping.declared_minductive Σ' kn mib' /\
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

Lemma erase_global_erases_deps {Σ} {Σ' : EAst.global_declarations} {t et T} : 
  wf_ext Σ ->
  Σ;;; [] |- t : T ->
  Σ;;; [] |- t ⇝ℇ et ->
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
    specialize (H0 (inductive_mind p.1.1)). forward H0.
    now rewrite KernameSet.singleton_spec. red in H0. destruct H0.
    elimtype False. destruct H0 as [cst [declc _]].
    { red in declc. destruct d as [[[d _] _] _]. red in d. rewrite d in declc. noconf declc. }
    destruct H0 as [mib [mib' [declm [declm' em]]]].
    destruct d. pose proof em as em'. destruct em'.
    eapply Forall2_nth_error_left in H5 as (x' & ? & ?); eauto.
    econstructor; eauto. split; eauto.
    
    eauto.
    destruct H0 as [[? ?] ?]. red in H0, declm. rewrite H0 in declm. now noconf declm.
    destruct H0 as [[? ?] ?]. red in H0, declm. rewrite H0 in declm. now noconf declm.
    
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
    inv wfΣ. inv X.
    red in H |- *.
    rewrite -H. simpl. unfold lookup_env; simpl; destruct (eqb_spec (inductive_mind p.1.1) kn); try congruence.
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
  ETyping.lookup_env ((kn', d) :: Σ) kn = ETyping.lookup_env Σ kn.
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
  unfold ETyping.declared_constant. rewrite ETyping.elookup_env_cons_fresh //.
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
  unfold ETyping.declared_constant.
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
  wf Σ ->
  declared_minductive Σ mdecl m ->
  erases_mutual_inductive_body m (erase_mutual_inductive_body m).
Proof.
  destruct m; constructor; simpl; auto.
  eapply on_declared_minductive in H; auto. simpl in H. clear X.
  eapply onInductives in H; simpl in *.
  assert (Alli (fun i oib => 
    match destArity [] oib.(ind_type) with Some _ => True | None => False end) 0 ind_bodies0).
  { eapply Alli_impl; eauto.
    simpl. intros n x []. simpl in *. rewrite ind_arity_eq.
    rewrite !destArity_it_mkProd_or_LetIn /= //. } clear H.
  induction X; constructor; auto.
  destruct hd; constructor; simpl; auto.
  clear.
  induction ind_ctors0; constructor; auto.
  cbn in *.
  intuition auto.
  induction ind_projs0; constructor; auto.
  destruct a; auto.
  unfold isPropositionalArity.
  destruct destArity as [[? ?]|] eqn:da; auto.
Qed.

Lemma erases_closed Σ Γ t t' : Σ;;; Γ |- t ⇝ℇ t' -> PCUICAst.closedn #|Γ| t -> ELiftSubst.closedn #|Γ| t'.
Proof.
  induction 1 using erases_forall_list_ind; cbn; auto; try solve [rtoProp; repeat solve_all].
  - rtoProp. intros []. split; eauto. solve_all.
    eapply Forall2_All2 in H1. eapply All2_All2_mix in X; tea.
    eapply forallb_All in H3. eapply All2_All_mix_left in X; tea. clear H3.
    clear H1.
    solve_all. rewrite -b.
    rewrite app_length inst_case_branch_context_length in a0.
    rewrite map_length.
    eapply a0. now move/andP: a => [].
  - unfold test_def in *. solve_all.
    eapply All2_All2_mix in X; tea. solve_all.
    len in b. rewrite - (All2_length X).
    now eapply b.
  - unfold test_def in *. solve_all.
    eapply All2_All2_mix in X; tea. solve_all.
    len in b. rewrite - (All2_length X).
    now eapply b.
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
        unfold ETyping.declared_constant.
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
          eapply erases_mutual. exact wfΣ.
          rewrite /declared_minductive /= /lookup_env e /=; rewrite -> eq_kername_refl => //. }

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


Local Notation "Σ |- s ▷ t" := (PCUICWcbvEval.eval Σ s t) (at level 50, s, t at next level) : type_scope.

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
  ~ ∥ isErasable Σ Γ (mkApps t args)∥ ->
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
    elim: is_erasableb_reflect.
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

Lemma All_from_nth_error : forall (A : Type) (L1 : list A) (P : A -> Type),
  (forall (n : nat) (x1 : A),
   n < #|L1| -> nth_error L1 n = Some x1 -> P x1) ->
  All P L1.
Proof.
  intros. induction L1; econstructor.
  - eapply (X 0); cbn; try reflexivity. lia.
  - eapply IHL1. intros. eapply (X (S n)); cbn; eauto. lia.
Qed.

Lemma welltyped_mkApps_inv {Σ : global_env_ext} Γ f args :  ∥ wf Σ ∥ ->
  welltyped Σ Γ (mkApps f args) -> welltyped Σ Γ f /\ Forall (welltyped Σ Γ) args.
Proof.
  intros wf (A & HA). sq. eapply inversion_mkApps in HA as (? & ? & ?).
  split. eexists; eauto.
  induction t0 in f |- *; econstructor; eauto; econstructor; eauto.
Qed.

Local Arguments erase_global_decls _ _ _ : clear implicits.

(* Lemma make_wf_env_ext_remove_kn kn decl univs decls : *)
  (* make_wf_env_ext (remove_kn kn (add_global_decl  )) *)

Lemma lookup_env_erase (Σ : wf_env) deps kn d :
  KernameSet.In kn deps -> 
  lookup_env Σ kn = Some (InductiveDecl d) ->
  ETyping.lookup_env (erase_global deps Σ) kn = Some (EAst.InductiveDecl (erase_mutual_inductive_body d)).
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
   ETyping.declared_constructor (erase_global deps Σ) (ind, c) (erase_mutual_inductive_body mind) (erase_one_inductive_body idecl) (cdecl.(cstr_name), cdecl.(cstr_arity)).
Proof.
  intros [[]] Hin.
  cbn in *. split. split. 
  - red in H |- *. now eapply lookup_env_erase.
  - cbn. now eapply map_nth_error.
  - cbn. erewrite map_nth_error; eauto.
Qed.

From MetaCoq.Erasure Require Import EEtaExpanded.

Lemma All_map_All {A B C} {Q : C -> Type} {P : C -> A -> Prop}
  {Q' : B -> Type} {R : C -> A -> Prop} 
  f args (ha: forall y : C, Q y -> ∥ All (R y) args ∥) :
  (forall y : C, Q y -> All (P y) args) ->
  (forall x y rx, P y x -> Q' (f x rx)) ->
  All Q' (map_All f args ha).
Proof.
  (* funelim (map_All f args ha).
  - constructor.
  - intros ha hf. 
    depelim ha. constructor; eauto.
Qed. *)
Admitted.
 
Lemma erase_brs_eq Σ Γ p ts wt : 
  erase_brs Σ Γ p ts wt = map_All (fun br wt => (erase_context (bcontext br), erase Σ _ (bbody br) wt)) ts wt.
Proof.
  funelim (map_All _ ts wt); cbn; auto.
  f_equal => //. f_equal => //. apply erase_irrel.
  rewrite -H. eapply erase_irrel.
Qed.

Lemma erase_mfix_eq Σ Γ ts wt : 
  erase_mfix Σ Γ ts wt = map_All (fun d wt => 
    let dbody' := erase Σ _ (dbody d) wt in
    {| E.dname := d.(dname).(binder_name); E.rarg := d.(rarg); E.dbody := dbody' |}) ts wt.
Proof.
  funelim (map_All _ ts wt); cbn; auto.
  f_equal => //. f_equal => //. apply erase_irrel.
  rewrite -H. eapply erase_irrel.
Qed.

Lemma isConstruct_erase Σ Γ t wt : 
  ~ PCUICEtaExpand.isConstruct t -> ~ isConstruct (erase Σ Γ t wt).
Proof.
  apply (erase_elim Σ
    (fun Γ t wt e => ~ PCUICEtaExpand.isConstruct t -> ~ isConstruct e)
    (fun Γ l awt e => True)
    (fun Γ p l awt e => True)
    (fun Γ l awt e => True)); intros => //. bang.
Qed.

Lemma eta_expand_erase {Σ : wf_env_ext} Σ' {Γ t} 
  (wt : forall Σ0 : global_env_ext, abstract_env_rel' Σ Σ0 -> welltyped Σ0 Γ t) :
  PCUICEtaExpand.expanded Σ t ->
  erases_global Σ Σ' ->
  expanded Σ' [] (@erase Σ Γ t wt).
Proof.
  pose proof (referenced_impl_ext_wf Σ) as [wf]. 
  intros exp deps.
  induction exp in Γ, wt, deps |- *.
  all:simp erase.
  (* 1-7,9-14: simp erase; unfold erase_clause_1 in *. *)
  all: eauto using expanded.
  all : assert (wfΣ' : abstract_env_rel' Σ Σ) by reflexivity;
        specialize_Σ wfΣ'.
  all: try (unfold inspect, erase_clause_1, erase_clause_1_clause_2;
    destruct is_erasableb; [ now eauto using expanded | eauto using expanded]).
  all: try now (invs deps; eauto using expanded).
  - econstructor.
    solve_all. rewrite erase_terms_eq. 
    eapply All_map_All. intros. exact H0. cbn. intros x wx rx [Hx IH]. eauto.
  - simp erase. destruct inspect as [b ise] eqn:hi. destruct b.
    + simp erase. now econstructor.
    + rewrite -hi -erase_equation_1. clear hi.
      destruct (is_erasableb_reflect Σ Γ (mkApps f6 args) wt) => //.
      destruct (wt _ wfΣ') as (T & wt'). revert deps. rewrite erase_mkApps. 
      * eapply welltyped_mkApps_inv; sq; eauto.
      * intros. econstructor; eauto.
        -- now eapply isConstruct_erase.
        -- clear - H1 deps. induction H1; cbn.
          ++ econstructor.
          ++ depelim Hyp1. cbn. econstructor; eauto.
      * eapply typing_wf_local; eauto.
      * intros ?.
        destruct (is_erasableb_reflect Σ Γ (mkApps f6 args) wt) => //.
      * intros. cbn in H2; subst. eapply welltyped_mkApps_inv; sq; eauto.
  - destruct inspect as [b ise]. destruct b; simp erase.
    + constructor.
    + bang.
  - econstructor; eauto.
    solve_all. rewrite erase_brs_eq.
    eapply All_map_All; tea. cbn. intros x wx [exp' IH]. eauto.
  - todo "fix".
  - econstructor; eauto.
    solve_all. rewrite erase_mfix_eq.
    eapply All_map_All. intros. exact H0. intros x y wx [exp' IH]. now eapply IH.
  - simp erase. destruct inspect as [b ise] eqn:hi. destruct b.
    + simp erase. constructor.
    + rewrite -hi -erase_equation_1.
      destruct (wt _ wfΣ') as (T & wt').
      clear hi; move: ise. elim: is_erasableb_reflect => // happ _.
      rewrite erase_mkApps //.
      * eapply welltyped_mkApps_inv; sq; eauto.
      * intros ? ?. simp erase. destruct (inspect (is_erasableb Σ Γ (tConstruct _ _ _) _)).
        destruct x.  
        -- exfalso. sq. move: e.
          elim: is_erasableb_reflect => // ise' _; sq.
          apply happ. eapply Is_type_app in X; tea.
          eapply typing_wf_local; eauto.
        -- sq.
           eapply erases_declared_constructor in H as H'; eauto.
           destruct H' as (? & ? & ? & ?). 
           eapply expanded_tConstruct_app; eauto.
           3: eapply erases_global_all_deps; eauto.
           { rewrite map_erase_length. destruct H4 as ((? & ? & ? & ? & ?) & ? & ?).
           unshelve edestruct @declared_constructor_inv as (? & ? & ?); eauto.
           shelve. eapply weaken_env_prop_typing. 
           2: erewrite <- cstr_args_length; eauto; lia.
           eapply wf.
           }
           solve_all. clear - deps H2.
           induction H2.
           ++ econstructor.
           ++ econstructor; eauto. eapply p. eauto.
      * eapply typing_wf_local; eauto.
      * cbn; intros; subst. eapply welltyped_mkApps_inv; sq; eauto.
Qed.

Lemma erase_global_closed Σ deps :
  let Σ' := erase_global deps Σ in
  ETyping.closed_env Σ'.
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
  + cbn [ETyping.closed_env forallb]. cbn.
    rewrite [forallb _ _](IHdecls) // andb_true_r.
    rewrite /test_snd /ETyping.closed_decl /=.
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
  + cbn [ETyping.closed_env forallb].
    rewrite {1}/test_snd {1}/ETyping.closed_decl /=.
    eapply IHdecls => //.
  + eapply IHdecls => //.
Qed.