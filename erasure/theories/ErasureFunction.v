(* Distributed under the terms of the MIT license. *)
From Coq Require Import Program ssreflect ssrbool.
From MetaCoq.Template Require Import config utils Kernames MCRelations.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICPrimitive
     PCUICReflect PCUICWeakeningEnv PCUICCasesContexts
     PCUICTyping PCUICGlobalEnv PCUICInversion PCUICGeneration
     PCUICConfluence PCUICConversion 
     PCUICCumulativity PCUICSR PCUICSafeLemmata
     PCUICValidity PCUICPrincipality PCUICElimination 
     PCUICOnFreeVars PCUICWellScopedCumulativity PCUICSN.
     
From MetaCoq.SafeChecker Require Import PCUICErrors PCUICSafeReduce PCUICSafeRetyping.
From MetaCoq.Erasure Require Import EAstUtils EArities Extract Prelim EDeps ErasureCorrectness.

Local Open Scope string_scope.
Set Asymmetric Patterns.
Import MCMonadNotation.

From Equations Require Import Equations.
Set Equations Transparent.
Local Set Keyed Unification.
Require Import ssreflect.

Derive Signature for PCUICTyping.on_global_env.

Implicit Types (cf : checker_flags).

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
    eapply PCUICWeakening.weaken_wf_local; tea.
    eapply PCUICArities.on_minductive_wf_params; tea.
  Qed.
  
  Context {mdecl ind idecl}
    (decli : declared_inductive Σ ind mdecl idecl).
  
  Lemma on_minductive_wf_params_indices_inst_weaken {Γ} (u : Instance.t) :
    consistent_instance_ext Σ (ind_universes mdecl) u ->
    wf_local Σ Γ ->
    wf_local Σ (Γ ,,, (ind_params mdecl ,,, ind_indices idecl)@[u]).
  Proof.
    intros. eapply PCUICWeakening.weaken_wf_local; tea.
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

Section fix_sigma.
  Variable Σ : global_env_ext.
  Variable HΣ : ∥wf Σ∥.

  Definition term_rel : Relation_Definitions.relation (∑ Γ t, welltyped Σ Γ t) :=
    fun '(Γ2; B; H) '(Γ1; t1; H2) =>
      ∥∑ na A, red (fst Σ) Γ1 t1 (tProd na A B) × (Γ1,, vass na A) = Γ2∥.

  Definition cod B t := match t with tProd _ _ B' => B = B' | _ => False end.

  Lemma wf_cod : WellFounded cod.
  Proof.
    clear HΣ.
    sq. intros ?. induction a; econstructor; cbn in *; intros; try tauto; subst. eauto.
  Defined.

  Lemma wf_cod' : WellFounded (Relation_Operators.clos_trans _ cod).
  Proof.
    clear HΣ.
    eapply Subterm.WellFounded_trans_clos. exact wf_cod.
  Defined.

  Lemma Acc_no_loop X (R : X -> X -> Prop) t : Acc R t -> R t t -> False.
  Proof.
    induction 1. intros. eapply H0; eauto.
  Qed.

  Ltac sq' := try (destruct HΣ; clear HΣ);
    repeat match goal with
          | H : ∥ _ ∥ |- _ => destruct H; try clear H
          end; try eapply sq.

  Definition wf_reduction_aux : WellFounded term_rel.
  Proof.
    intros (Γ & s & H). sq'.
    induction (normalisation Σ _ Γ s H) as [s _ IH].
    induction (wf_cod' s) as [s _ IH_sub] in Γ, H, IH |- *.
    econstructor.
    intros (Γ' & B & ?) [(na & A & ? & ?)]. subst.
    eapply Relation_Properties.clos_rt_rtn1 in r. inversion r.
      + subst. eapply IH_sub. econstructor. cbn. reflexivity.
        intros. eapply IH.
        inversion H0.
        * subst. econstructor. eapply prod_red_r. eassumption.
        * subst. eapply cored_red in H2 as [].
          eapply cored_red_trans. 2: eapply prod_red_r. 2:eassumption.
          eapply PCUICReduction.red_prod_r. eauto.
        * constructor. do 2 eexists. now split.
      + subst. eapply IH.
        * eapply red_neq_cored.
          eapply Relation_Properties.clos_rtn1_rt. exact r.
          intros ?. subst.
          eapply Relation_Properties.clos_rtn1_rt in X1.
          eapply cored_red_trans in X0; [| exact X1 ].
          eapply Acc_no_loop in X0. eauto.
          eapply @normalisation; eauto.
        * constructor. do 2 eexists. now split.
  Unshelve.
  - destruct H as [].
    eapply inversion_Prod in X0 as (? & ? & ? & ? & ?) ; auto.
    eapply cored_red in H0 as [].
    econstructor. econstructor. econstructor. eauto.
    2:reflexivity. econstructor; pcuic. 
    eapply subject_reduction; eauto.
  - eapply red_welltyped; sq.
    3:eapply Relation_Properties.clos_rtn1_rt in r; eassumption. all:eauto.
  Qed.

  Instance wf_reduction : WellFounded term_rel.
  Proof.
    refine (Wf.Acc_intro_generator 1000 _).
    exact wf_reduction_aux.
  Defined.
  Opaque wf_reduction.
  Opaque Acc_intro_generator.
  Opaque Wf.Acc_intro_generator.
  Ltac sq := try (destruct HΣ as [wfΣ]; clear HΣ);
    repeat match goal with
          | H : ∥ _ ∥ |- _ => destruct H
          end; try eapply sq.

  Equations is_arity Γ (HΓ : ∥wf_local Σ Γ∥) T (HT : welltyped Σ Γ T) :
    {Is_conv_to_Arity Σ Γ T} + {~ Is_conv_to_Arity Σ Γ T}
    by wf ((Γ;T;HT) : (∑ Γ t, welltyped Σ Γ t)) term_rel :=
    {
      is_arity Γ HΓ T HT with inspect (@reduce_to_sort _ Σ HΣ Γ T HT) => {
      | exist (Checked H) rsort => left _ ;
      | exist (TypeError _) rsort with inspect (@reduce_to_prod _ Σ HΣ Γ T _) => {
        | exist (Checked (na; A; B; H)) rprod with is_arity (Γ,, vass na A) _ B _ :=
          { | left isa => left _;
            | right nisa => right _ };
        | exist (TypeError e) rprod => right _ } }
    }.
  Next Obligation.
    sq. econstructor. split. sq. eassumption. econstructor.
  Qed.
  Next Obligation.
    clear rprod.
    destruct HT as []; sq.
    eapply subject_reduction_closed in X; eauto.
    eapply inversion_Prod in X as (? & ? & ? & ? & ?).
    econstructor; eauto; cbn; eauto. auto.
  Qed.
  Next Obligation.
    clear rprod.
    sq. destruct HT as [].
    eapply subject_reduction_closed in X; eauto.
    eapply inversion_Prod in X as (? & ? & ? & ? & ?).
    eexists; eauto. auto.
  Qed.
  Next Obligation.
    sq. repeat eexists. exact c.
  Qed.
  Next Obligation.
    destruct isa as (? & ? & ?). eexists (tProd _ _ _). split; sq.
    etransitivity. exact c0. eapply closed_red_prod_codom; tea.
    eassumption.
  Qed.
  Next Obligation.
    clear rprod.
    destruct HΣ as [wΣ].
    destruct H0 as (? & ? & ?). sq.
    edestruct (PCUICContextConversion.closed_red_confluence X0 X) as (? & ? & ?); eauto.
    eapply invert_red_prod in c as (? & ? & []); eauto. subst.
    apply nisa.

    eapply invert_cumul_arity_l in H1.
    2:eapply red_equality; tea.
    destruct H1 as (? & ? & ?). sq.

    eapply invert_red_prod in X2 as (? & ? & []); eauto. subst. cbn in *.
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
    pose proof (reduce_to_sort_complete HΣ _ (eq_sym rsort)).
    pose proof (reduce_to_prod_complete HΣ _ (eq_sym rprod)).
    destruct HΣ.
    apply Is_conv_to_Arity_inv in H as [(?&?&?&[r])|(?&[r])]; eauto.
    - eapply H1, r.
    - eapply H0, r.
  Qed.

End fix_sigma.

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

Program Definition is_erasable (Σ : global_env_ext) (HΣ : ∥wf_ext Σ∥) (Γ : context) (t : PCUICAst.term) (Ht : welltyped Σ Γ t) :
  ({∥isErasable Σ Γ t∥} + {∥(isErasable Σ Γ t -> False)∥}) :=
  let T := @type_of extraction_checker_flags Σ _ _ Γ t Ht in
  let b := is_arity Σ _ Γ _ T _ in
  match b : {_} + {_} return _ with
  | left _ => left _
  | right _ => let K := @type_of extraction_checker_flags Σ _ _ Γ T _ in
       match @reduce_to_sort _ Σ _ Γ K _ with
       | Checked (u; Hu) =>
          match is_propositional u with true => left _ | false => right _ end
       | TypeError _ => False_rect _ _
       end
  end.

Next Obligation. sq; eauto. Qed.
Next Obligation.
  sq. red in X. red in X. apply X.
Qed.
Next Obligation.
  sq. apply X.
Qed.
Next Obligation.
  destruct Ht. sq. eauto using typing_wf_local.
Qed.
Next Obligation.
  unfold type_of. destruct infer. simpl.
  destruct s as [[Htx _]]. 
  eapply typing_welltyped; eauto; sq; auto. apply X.
Qed.
Next Obligation.
  unfold type_of in *.
  destruct infer as [x [[Htx Hp]]].
  destruct H as [T' [redT' isar]].
  sq. econstructor. split. eapply type_reduction_closed; eauto.
  eauto.
Qed.
Next Obligation.
  sq. apply w.
Qed.
Next Obligation.
  sq. apply w.
Qed.
Next Obligation.
  sq.
  unfold type_of in *.
  destruct infer as [x [[Htx Hp]]]. simpl.
  simpl in *.
  eapply validity in Htx; auto.
  destruct Htx as [s Hs]. econstructor; eauto.
Qed.
Next Obligation.
  sq. apply w.
Qed.
Next Obligation.
  sq.
  unfold type_of.
  destruct (infer _ (is_erasable_obligation_7 _ _ _ _ _ _)).
  simpl. sq.
  destruct X. eapply validity in t0; auto.
  eapply wat_welltyped; eauto. all:now sq.
Qed.
Next Obligation.
  unfold type_of in *.
  destruct reduce_to_sort; try discriminate.
  destruct (infer _ (is_erasable_obligation_7 _ _ _ _ _ _)).
  destruct (infer _ (is_erasable_obligation_1 _ _)).
  simpl in *.
  destruct Ht.
  destruct a as [a reda].
  sq. red. exists x0 ; split; intuition eauto.
  pose proof (PCUICContextConversion.closed_red_confluence c0 c) as [v' [redl redr]].
  eapply invert_red_sort in redl.
  eapply invert_red_sort in redr. subst. noconf redr.
  right. exists u; split; eauto.
  eapply type_reduction_closed; eauto using typing_wf_local.
Qed.
Next Obligation.
  unfold type_of in *.
  destruct reduce_to_sort; try discriminate.
  destruct (infer _ (is_erasable_obligation_7 _ _ _ _ _ _)) as [? [[? ?]]].
  destruct (infer _ (is_erasable_obligation_1 _ _)) as [? [[? ?]]].
  destruct a as [u' redu']. simpl in *.
  sq.
  pose proof (PCUICContextConversion.closed_red_confluence c0 c) as [v' [redl redr]].
  eapply invert_red_sort in redl.
  eapply invert_red_sort in redr. subst. noconf redr.
  clear Heq_anonymous0.
  intros (? & ? & ?).
  destruct s as [ | (? & ? & ?)]; simpl in *.
  + destruct H. eapply arity_type_inv; eauto using typing_wf_local.
  + pose proof (e0 _ t2).
    eapply type_reduction_closed in t0; eauto.
    eapply cumul_prop1' in t3; eauto.
    eapply leq_term_propositional_sorted_l in t0; eauto.
    2:reflexivity.
    2:eapply validity; eauto.
    eapply leq_universe_propositional_r in t0; auto. congruence.
    apply X.
Qed.
Next Obligation.
  unfold type_of in *.
  destruct HΣ.
  symmetry in Heq_anonymous.
  pose proof (reduce_to_sort_complete _ _ Heq_anonymous).
  clear Heq_anonymous.
  destruct (infer _ (is_erasable_obligation_7 _ _ _ _ _ _)) as [? [[? ?]]].
  destruct (infer _ (is_erasable_obligation_1 _ _)) as [? [[? ?]]].
  simpl in *. 
  eapply validity in t1; auto.
  destruct t1 as [s Hs].
  red in Hs.
  specialize (e _ Hs).
  eapply equality_Sort_r_inv in e as [u' [redu' leq]].
  now apply (H0 _ redu').
Qed.

Section Erase.

  Variable (Σ : global_env_ext)( HΣ :∥ wf_ext Σ ∥).

  Ltac sq' := try (destruct HΣ; clear HΣ);
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

  Lemma welltyped_brs Γ ci p t2 brs T : Σ ;;; Γ |- tCase ci p t2 brs : T -> 
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
    eapply PCUICContextConversion.closed_context_conversion; tea.
    now symmetry.
  Qed.

  Section EraseMfix.
    Context (erase : forall (Γ : context) (t : term) (Ht : welltyped Σ Γ t), E.term).

    Definition erase_mfix Γ (defs : mfixpoint term) 
    (H : forall d, In d defs -> welltyped Σ (Γ ,,, fix_context defs) d.(dbody)) : EAst.mfixpoint E.term :=
    let Γ' := (fix_context defs ++ Γ)%list in
    map_InP (fun d wt => 
      let dbody' := erase Γ' d.(dbody) wt in
      ({| E.dname := d.(dname).(binder_name); E.rarg := d.(rarg); E.dbody := dbody' |})) defs H.

    (** We assume that there are no lets in contexts, so nothing has to be expanded.
        In particular, note that #|br.(bcontext)| = context_assumptions br.(bcontext) when no lets are present.
    *)
    Definition erase_brs p Γ (brs : list (branch term)) 
      (H : forall d, In d brs -> welltyped Σ (Γ ,,, inst_case_branch_context p d) (bbody d)) : list (list name * E.term) :=
      map_InP (fun br wt => let br' := erase (Γ ,,, inst_case_branch_context p br) (bbody br) wt in 
        (erase_context br.(bcontext), br')) brs H.
  
  End EraseMfix.

  Equations erase_prim (ep : prim_val term) : PCUICPrimitive.prim_val E.term :=
  erase_prim (_; primIntModel i) := (_; primIntModel i);
  erase_prim (_; primFloatModel f) := (_; primFloatModel f).
  

  Equations? (noeqns noind) erase (Γ : context) (t : term) (Ht : welltyped Σ Γ t) : E.term
      by struct t :=
    erase Γ t Ht with (is_erasable Σ HΣ Γ t Ht) :=
    {
      erase Γ _ Ht (left _) := E.tBox;
      erase Γ (tRel i) Ht _ := E.tRel i ;
      erase Γ (tVar n) Ht _ := E.tVar n ;
      erase Γ (tEvar m l) Ht _ := let l' := map_InP (fun x wt => erase Γ x wt) l _ in (E.tEvar m l') ;
      erase Γ (tSort u) Ht _ := E.tBox ;

      erase Γ (tConst kn u) Ht _ := E.tConst kn ;
      erase Γ (tInd kn u) Ht _ := E.tBox ;
      erase Γ (tConstruct kn k u) Ht _ := E.tConstruct kn k ;
      erase Γ (tProd na b t) Ht _ := E.tBox ;
      erase Γ (tLambda na b t) Ht _ :=
        let t' := erase (vass na b :: Γ) t _ in
        E.tLambda na.(binder_name) t';
      erase Γ (tLetIn na b t0 t1) Ht _ :=
        let b' := erase Γ b _ in
        let t1' := erase (vdef na b t0 :: Γ) t1 _ in
        E.tLetIn na.(binder_name) b' t1' ;
      erase Γ (tApp f u) Ht _ :=
        let f' := erase Γ f _ in
        let l' := erase Γ u _ in
        E.tApp f' l';
      erase Γ (tCase ci p c brs) Ht _ with erase Γ c _ :=
       { | c' :=
          let brs' := erase_brs erase p Γ brs _ in
          E.tCase (ci.(ci_ind), ci.(ci_npar)) c' brs' } ;
      erase Γ (tProj p c) Ht _ :=
        let c' := erase Γ c _ in
        E.tProj p c' ;
      erase Γ (tFix mfix n) Ht _ :=
        let mfix' := erase_mfix erase Γ mfix _ in
        E.tFix mfix' n;
      erase Γ (tCoFix mfix n) Ht _ :=
        let mfix' := erase_mfix (erase) Γ mfix _ in
        E.tCoFix mfix' n;
      erase Γ (tPrim p) Ht _ := E.tPrim (erase_prim p)
    }.
  Proof.
    all:try clear b'; try clear f'; try clear brs'; try clear erase.
    all:destruct HΣ, Ht as [ty Ht]; try destruct s0; simpl in *.
    - now eapply inversion_Evar in Ht.
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
    - eapply inversion_Case in Ht as (? & ? & ? & ? & [] & ?); auto.
      eexists; eauto.
    - eapply welltyped_brs in Ht as [].
      apply In_nth_error in H as (?&nth).
      now eapply nth_error_all in X0; tea.
    - clear wildcard.
      eapply inversion_Proj in Ht as (? & ? & ? & ? & ? & ? & ? & ? & ?); auto.
      eexists; eauto.
    - eapply inversion_Fix in Ht as (? & ? & ? & ? & ? & ?); auto.
      eapply All_In in a0; eauto.
      destruct a0 as [a0]. eexists; eauto.
    - eapply inversion_CoFix in Ht as (? & ? & ? & ? & ? & ?); auto.
      eapply All_In in a0; eauto.
      destruct a0 as [a0]. eexists; eauto.
  Qed.

  (* For functional elimination. Not useful due to erase_mfix etc.. Next Obligation.
    revert Γ t Ht. fix IH 2.
    intros Γ t Ht.
    rewrite erase_equation_1.
    constructor.
    destruct is_erasable.
    simpl. econstructor.
    destruct t; simpl.
    3:{ elimtype False. destruct Ht. now eapply inversion_Evar in X. }
    all:constructor; auto.
    destruct (let c' := _ in (c', is_box c')).
    destruct b. constructor.  
    destruct brs. simpl.
    constructor. destruct p; simpl.
    constructor. eapply IH.
    simpl.
    constructor.
  Defined. *)
  
End Erase.

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

Lemma erase_erase_clause_1 {Σ} {wfΣ : ∥wf_ext Σ∥} {Γ t} (wt : welltyped Σ Γ t) : 
  erase Σ wfΣ Γ t wt = erase_clause_1 Σ wfΣ (erase Σ wfΣ) Γ t wt (is_erasable Σ wfΣ Γ t wt).
Proof.
  destruct t; simpl; auto.
Qed.
#[global]
Hint Rewrite @erase_erase_clause_1 : erase.

Lemma erase_to_box {Σ : global_env_ext} {wfΣ : ∥wf_ext Σ∥} {Γ t} (wt : welltyped Σ Γ t) :
  let et := erase Σ wfΣ Γ t wt in 
  if is_box et then ∥ isErasable Σ Γ t ∥
  else ∥ isErasable Σ Γ t -> False ∥.
Proof.
  revert Γ t wt. simpl.
  fix IH 2. intros.
  simp erase.
  destruct (is_erasable Σ wfΣ Γ t wt) eqn:ise; simpl. assumption.
  destruct t; simpl in *; simpl in *; try (clear IH; discriminate); try assumption.
   
  - specialize (IH _ t1 ((erase_obligation_5 Σ wfΣ Γ t1 t2 wt s))).
    rewrite is_box_tApp. destruct is_box.
    destruct wt, wfΣ, s, IH.
    eapply (EArities.Is_type_app _ _ _ [_]); eauto.
    eauto using typing_wf_local.
    assumption.

  - clear IH. intros. destruct wt. sq. clear ise.
    eapply inversion_Ind in t as (? & ? & ? & ? & ? & ?) ; auto.
    red. eexists. split. econstructor; eauto. left.
    eapply isArity_subst_instance.
    eapply isArity_ind_type; eauto.
Defined.

Lemma erases_erase {Σ : global_env_ext} {wfΣ : ∥wf_ext Σ∥} {Γ t} (wt : welltyped Σ Γ t) :
  erases Σ Γ t (erase Σ wfΣ Γ t wt).
Proof.
  intros.
  destruct wt as [T Ht].
  sq.
  generalize (iswelltyped Ht).
  intros wt.
  set (wfΣ' := sq w).
  clearbody wfΣ'.

  revert Γ t T Ht wt wfΣ'.
  eapply(typing_ind_env (fun Σ Γ t T =>
       forall (wt : welltyped Σ Γ t)  (wfΣ' : ∥ wf_ext Σ ∥),
          Σ;;; Γ |- t ⇝ℇ erase Σ wfΣ' Γ t wt
         )
         (fun Σ Γ => wf_local Σ Γ)); intros; auto; clear Σ w; rename Σ0 into Σ.

  10:{ simpl erase.
    destruct is_erasable. simp erase. sq.
    destruct brs; simp erase.
    constructor; auto.
    constructor; auto.
    destruct wt.
    sq; constructor.
    eapply elim_restriction_works; eauto.
    intros isp. eapply isErasable_Proof in isp. eauto.
    eapply H4.
    unfold erase_brs. eapply All2_from_nth_error. now autorewrite with len.
    intros.
    eapply All2i_nth_error_r in X7; eauto.
    destruct X7 as [t' [htnh eq]].
    eapply nth_error_map_InP in H9.
    destruct H9 as [a [Hnth [p' eq']]].
    subst. simpl. rewrite Hnth in H8. noconf H8.
    intuition auto.
    destruct b. cbn in *. intuition auto.
    move: p'.
    rewrite -(PCUICCasesContexts.inst_case_branch_context_eq a).
    intros p'. specialize (a2 p' (sq w)).
    apply a2. }

  all:simpl erase; eauto.

  all: simpl erase in *.
  all: unfold erase_clause_1 in *.
  all:sq.
  all: cbn in *; repeat (try destruct ?;  repeat match goal with
                                          [ H : Checked _ = Checked _ |- _ ] => inv H
                                        | [ H : TypeError _ = Checked _ |- _ ] => inv H
                                        | [ H : welltyped _ _ _ |- _ ] => destruct H as []
                                             end; sq; eauto).
  all:try solve[discriminate].

  - econstructor.
    clear E.
    eapply inversion_Ind in t as (? & ? & ? & ? & ? & ?) ; auto.
    red. eexists. split. econstructor; eauto. left.
    eapply isArity_subst_instance.
    eapply isArity_ind_type; eauto.

  - constructor. clear E.
    eapply nisErasable_Propositional in f; auto.
    now exists A.

  - constructor; auto. clear E.
    eapply inversion_Proj in t as (? & ? & ? & ? & ? & ? & ? & ? & ? & ?) ; auto.
    eapply elim_restriction_works_proj; eauto. exact d.
    intros isp. eapply isErasable_Proof in isp; eauto.

  - constructor.
    eapply All2_from_nth_error. now autorewrite with len.
    intros.
    unfold erase_mfix in H4.
    eapply nth_error_map_InP in H4 as [a [Hnth [wt eq]]].
    subst. rewrite Hnth in H3. noconf H3.
    simpl. intuition auto.
    eapply nth_error_all in X1; eauto. simpl in X1.
    intuition auto.
  
  - constructor.
    eapply All2_from_nth_error. now autorewrite with len.
    intros.
    unfold erase_mfix in H4.
    eapply nth_error_map_InP in H4 as [a [Hnth [wt eq]]].
    subst. rewrite Hnth in H3. noconf H3.
    simpl. intuition auto.
    eapply nth_error_all in X1; eauto. simpl in X1.
    intuition auto.
Qed.

Transparent wf_reduction.

(** We perform erasure up-to the minimal global environment dependencies of the term: i.e.  
  we don't need to erase entries of the global environment that will not be used by the erased
  term.
*)

Program Definition erase_constant_body Σ wfΣ (cb : constant_body)
  (Hcb : ∥ on_constant_decl (lift_typing typing) Σ cb ∥) : E.constant_body * KernameSet.t :=  
  let '(body, deps) := match cb.(cst_body) with
          | Some b => 
            let b' := erase Σ wfΣ [] b _ in
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

Program Fixpoint erase_global_decls (deps : KernameSet.t) (Σ : global_env) : ∥ wf Σ ∥ -> E.global_declarations := fun wfΣ =>
  match Σ with
  | [] => []
  | (kn, ConstantDecl cb) :: Σ' =>
    if KernameSet.mem kn deps then
      let cb' := erase_constant_body (Σ', cst_universes cb) _ cb _ in
      let deps := KernameSet.union deps (snd cb') in
      let Σ' := erase_global_decls deps Σ' _ in
      ((kn, E.ConstantDecl (fst cb')) :: Σ')
    else erase_global_decls deps Σ' _

  | (kn, InductiveDecl mib) :: Σ' =>
    if KernameSet.mem kn deps then
      let mib' := erase_mutual_inductive_body mib in
      let Σ' := erase_global_decls deps Σ' _ in
      ((kn, E.InductiveDecl mib') :: Σ')
    else erase_global_decls deps Σ' _
  end.
Next Obligation.
  sq. split. cbn.
  eapply PCUICWeakeningEnv.wf_extends. eauto. eexists [_]; reflexivity.
  now inversion X; subst.
Qed.

Next Obligation.
  sq.
  inv X. apply X1.
Qed.
Next Obligation.
  sq. inv X. apply X0.
Defined.

Next Obligation.
  sq. abstract (eapply PCUICWeakeningEnv.wf_extends; eauto; eexists [_]; reflexivity).
Defined.
Next Obligation.
  sq. abstract (eapply PCUICWeakeningEnv.wf_extends; eauto; eexists [_]; reflexivity).
Defined.
Next Obligation.
  sq. abstract (eapply PCUICWeakeningEnv.wf_extends; eauto; eexists [_]; reflexivity).
Defined.

Program Definition erase_global deps Σ : ∥wf Σ∥ -> _:=
  fun wfΣ  => erase_global_decls deps Σ wfΣ.

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
  - apply inversion_Case in wt as (? & ? & ? & ? & [] & ?); eauto.
    destruct ci as [[kn i'] ? ?]; simpl in *.
    apply includes_deps_fold in H2 as [? ?].

    specialize (H1 kn). forward H1.
    now rewrite KernameSet.singleton_spec. red in H1. destruct H1.
    elimtype False. destruct H1 as [cst [declc _]].
    { red in declc. destruct x1 as [d _]. red in d. rewrite d in declc. noconf declc. }
    destruct H1 as [mib [mib' [declm [declm' em]]]].
    destruct em.
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
    destruct d. destruct em.
    eapply Forall2_nth_error_left in H5 as (x' & ? & ?); eauto.
    econstructor; eauto. split; eauto.
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
    ELiftSubst.solve_all.
Qed.

Lemma erases_weakeninv_env {Σ Σ' : global_env_ext} {Γ t t' T} :
  wf Σ -> wf Σ' -> extends Σ Σ' -> 
  Σ ;;; Γ |- t : T ->
  erases Σ Γ t t' -> erases (Σ'.1, Σ.2) Γ t t'.
Proof.
  intros wfΣ wfΣ' ext Hty.
  apply (env_prop_typing ESubstitution.erases_extends _ wfΣ _ _ _ Hty _ wfΣ' ext).
Qed.  
 
Lemma erases_deps_weaken kn d (Σ : global_env) (Σ' : EAst.global_declarations) t : 
  wf ((kn, d) :: Σ) ->
  erases_deps Σ Σ' t ->
  erases_deps ((kn, d) :: Σ) Σ' t.
Proof.
  intros wfΣ er.
  induction er using erases_deps_forall_ind; try solve [now constructor].
  assert (kn <> kn0).
  { inv wfΣ. intros <-.
    eapply lookup_env_Some_fresh in H. contradiction. }
  eapply erases_deps_tConst with cb cb'; eauto.
  red. rewrite lookup_env_cons_fresh //.
  red.
  red in H1.
  destruct (cst_body cb) eqn:cbe;
  destruct (E.cst_body cb') eqn:cbe'; auto.
  specialize (H3 _ eq_refl).
  eapply on_declared_constant in H; auto.
  2:{ now inv wfΣ. }
  red in H. rewrite cbe in H. simpl in H.
  eapply (erases_weakeninv_env (Σ := (Σ, cst_universes cb))
     (Σ' := (((kn, d) :: Σ), cst_universes cb))); eauto.
  simpl. now inv wfΣ.
  eexists [(kn, d)]; intuition eauto.
  econstructor; eauto.
  red. destruct H. split; eauto.
  inv wfΣ.
  red in d0 |- *.
  rewrite -d0. simpl. unfold eq_kername. destruct kername_eq_dec; try congruence.
  eapply lookup_env_Some_fresh in d0. subst kn; contradiction.
  econstructor; eauto.
  red. destruct H. split; eauto.
  inv wfΣ.
  red in d0 |- *.
  rewrite -d0. simpl. unfold eq_kername. destruct kername_eq_dec; try congruence.
  eapply lookup_env_Some_fresh in d0. subst kn; contradiction.
Qed.

Lemma lookup_env_ext {Σ kn kn' d d'} : 
  wf ((kn', d') :: Σ) ->
  lookup_env Σ kn = Some d ->
  kn <> kn'.
Proof.
  intros wf hl.
  eapply lookup_env_Some_fresh in hl.
  inv wf.
  destruct (kername_eq_dec kn kn'); subst; congruence.
Qed.

Lemma lookup_env_cons_disc {Σ kn kn' d} : 
  kn <> kn' ->
  lookup_env ((kn', d) :: Σ) kn = lookup_env Σ kn.
Proof.
  intros Hk. simpl; unfold eq_kername.
  destruct kername_eq_dec; congruence.
Qed.

Lemma elookup_env_cons_disc {Σ kn kn' d} : 
  kn <> kn' ->
  ETyping.lookup_env ((kn', d) :: Σ) kn = ETyping.lookup_env Σ kn.
Proof.
  intros Hk. simpl; unfold eq_kername.
  destruct kername_eq_dec; congruence.
Qed.

Lemma global_erases_with_deps_cons kn kn' d d' Σ Σ' : 
  wf ((kn', d) :: Σ) ->
  global_erased_with_deps Σ Σ' kn ->
  global_erased_with_deps ((kn', d) :: Σ) ((kn', d') :: Σ') kn.
Proof.
  intros wf [[cst [declc [cst' [declc' [ebody IH]]]]]|].
  red. inv wf. left.
  exists cst. split.
  red in declc |- *.
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
  eapply (erases_weakeninv_env (Σ  := (_, cst_universes cst)) (Σ' := ((kn', d) :: Σ, cst_universes cst))); eauto.
  constructor; eauto.
  exists [(kn', d)]; intuition eauto.
  eapply on_declared_constant in declc; auto.
  red in declc. rewrite bod in declc. eapply declc.
  noconf H.
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
  wf ((kn', d) :: Σ) ->
  global_erased_with_deps Σ Σ' kn ->
  global_erased_with_deps ((kn', d) :: Σ) Σ' kn.
Proof.
  intros wf [[cst [declc [cst' [declc' [ebody IH]]]]]|].
  red. inv wf. left.
  exists cst. split.
  red in declc |- *.
  rewrite lookup_env_cons_fresh //.
  { eapply lookup_env_Some_fresh in declc.
    intros <-; contradiction. }
  exists cst'.
  unfold ETyping.declared_constant.
  red in ebody. unfold erases_constant_body.
  destruct (cst_body cst) eqn:bod; destruct (E.cst_body cst') eqn:bod' => //.
  intuition auto.
  eapply (erases_weakeninv_env (Σ  := (_, cst_universes cst)) (Σ' := ((kn', d) :: Σ, cst_universes cst))); eauto.
  constructor; eauto.
  exists [(kn', d)]; intuition eauto.
  eapply on_declared_constant in declc; auto.
  red in declc. rewrite bod in declc. eapply declc.
  noconf H.
  eapply erases_deps_weaken; eauto. constructor; eauto.

  right. destruct H as [mib [mib' [Hm [? ?]]]].
  exists mib, mib'; intuition auto.
  red.
  rewrite lookup_env_cons_fresh //.
  now epose proof (lookup_env_ext wf Hm).
Qed.

Lemma erase_constant_body_correct Σ Σ' cb (wfΣ : ∥  wf_ext Σ ∥) (onc : ∥ on_constant_decl (lift_typing typing) Σ cb ∥) :
  wf Σ' -> extends Σ Σ' ->
  erases_constant_body (Σ', Σ.2) cb (fst (erase_constant_body Σ wfΣ cb onc)).
Proof.
  red. sq. destruct cb as [name [bod|] univs]; simpl. intros.
  eapply (erases_weakeninv_env (Σ := Σ) (Σ' := (Σ', univs))); simpl; auto.
  red in o. simpl in o. eapply o.
  eapply erases_erase. auto.
Qed.

Lemma erase_constant_body_correct' {Σ cb} {wfΣ : ∥  wf_ext Σ ∥} {onc : ∥ on_constant_decl (lift_typing typing) Σ cb ∥} {body} :
  EAst.cst_body (fst (erase_constant_body Σ wfΣ cb onc)) = Some body ->
  ∥ ∑ t T, (Σ ;;; [] |- t : T) * (Σ ;;; [] |- t ⇝ℇ body) *
      (term_global_deps body = snd (erase_constant_body Σ wfΣ cb onc)) ∥.
Proof.
  intros. destruct cb as [name [bod|] univs]; simpl. intros.
  simpl in H. noconf H.
  set (obl :=(erase_constant_body_obligation_1 Σ wfΣ
  {|
  cst_type := name;
  cst_body := Some bod;
  cst_universes := univs |} onc bod eq_refl)). clearbody obl.
  destruct obl. sq.
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

Definition closed_decl (d : EAst.global_decl) := 
  match d with
  | EAst.ConstantDecl cb => 
    option_default (ELiftSubst.closedn 0) (EAst.cst_body cb) true
  | EAst.InductiveDecl _ => true
  end.

Definition closed_env (Σ : EAst.global_declarations) := 
  forallb (test_snd closed_decl) Σ.

Lemma lookup_env_closed {Σ kn decl} : closed_env Σ -> ETyping.lookup_env Σ kn = Some decl -> closed_decl decl.
Proof.
  induction Σ; cbn => //.
  move/andP => [] cla cle.
  destruct kername_eq_dec.
  move=> [= <-]. apply cla.
  now eapply IHΣ.
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

Lemma erase_global_includes Σ deps deps' wfΣ :
  (forall d, KernameSet.In d deps' -> ∥ ∑ decl, lookup_env Σ d = Some decl ∥) ->
  KernameSet.subset deps' deps ->
  let Σ' := erase_global deps Σ wfΣ in
  includes_deps Σ Σ' deps'.
Proof.
  sq.
  induction Σ in deps, deps', w |- *; simpl; intros H.
  - intros sub i hin. elimtype False.
    specialize (H i hin) as [[decl Hdecl]]. noconf Hdecl.
  - intros sub i hin.
    destruct a as [kn d].
    eapply KernameSet.subset_spec in sub.
    destruct (H i hin) as [[decl Hdecl]].
    pose proof (eqb_spec i kn). unfold eqb in H0; cbn in H0.
    revert Hdecl; elim: H0. intros -> [= <-].
    * destruct d as [|]; [left|right].
      exists c. split; auto.
      red. simpl. rewrite eq_kername_refl //.
      pose proof (sub _ hin) as indeps.
      eapply KernameSet.mem_spec in indeps. rewrite indeps.
      unfold ETyping.declared_constant. simpl.
      destruct (kername_eq_dec kn kn); simpl.
      eexists; intuition eauto.
      eapply erase_constant_body_correct; eauto.
      exists [(kn, ConstantDecl c)]; intuition auto.
      eapply erases_deps_cons; auto.
      assert (wf Σ). clear H0; now inv w.
    
      pose proof (erase_constant_body_correct' H0).
      sq. destruct X0 as [bod [bodty [[Hbod Hebod] Heqdeps]]].
      eapply (erase_global_erases_deps (Σ := (Σ, cst_universes c))); simpl; auto.
      constructor; simpl; auto.
      red in w.
      depelim w. auto. eauto. eauto.
      eapply IHΣ.

      intros d ind.
      eapply term_global_deps_spec in Hebod; eauto.
      eapply KernameSet.subset_spec.
      intros x hin'. eapply KernameSet.union_spec. right; auto.
      congruence. congruence.
      eexists m, _; intuition eauto.
      simpl. unfold declared_minductive.
      simpl. rewrite eq_kername_refl. reflexivity.
      specialize (sub _ hin).
      eapply KernameSet.mem_spec in sub. rewrite sub.
      red. cbn. destruct kername_eq_dec; try congruence.
      reflexivity.
      eapply erases_mutual; eauto.
      rewrite /declared_minductive /=; rewrite -> eq_kername_refl => //. 

    * intros ikn Hi.
      destruct d as [|].
      ++ destruct (KernameSet.mem kn deps) eqn:eqkn.
        eapply global_erases_with_deps_cons; eauto.
        eapply (IHΣ _ (KernameSet.singleton i)); auto.
        3:{ eapply KernameSet.singleton_spec => //. }
        intros.
        eapply KernameSet.singleton_spec in H0. subst.
        constructor; exists decl; auto.
        eapply KernameSet.subset_spec. intros ? ?.
        eapply KernameSet.union_spec. left.
        eapply KernameSet.singleton_spec in H0; subst.
        now eapply sub.
      
        eapply global_erases_with_deps_weaken. eauto.
        unfold erase_global_decls_obligation_4. simpl.
        eapply (IHΣ deps (KernameSet.singleton i)).
        3:now eapply KernameSet.singleton_spec.
        intros d ind%KernameSet.singleton_spec.
        subst. constructor; eexists; eauto.
        eapply KernameSet.subset_spec.
        intros ? hin'. eapply sub. eapply KernameSet.singleton_spec in hin'. now subst.        

      ++ destruct (KernameSet.mem kn deps) eqn:eqkn.
        eapply global_erases_with_deps_cons; eauto.
        eapply (IHΣ _ (KernameSet.singleton i)); auto.
        3:{ eapply KernameSet.singleton_spec => //. }
        intros.
        eapply KernameSet.singleton_spec in H0. subst.
        constructor; exists decl; auto.
        eapply KernameSet.subset_spec. intros ? ?.
        eapply KernameSet.singleton_spec in H0; subst.
        now eapply sub.
    
        eapply global_erases_with_deps_weaken. eauto.
        unfold erase_global_decls_obligation_4. simpl.
        eapply (IHΣ deps (KernameSet.singleton i)).
        3:now eapply KernameSet.singleton_spec.
        intros d ind%KernameSet.singleton_spec.
        subst. constructor; eexists; eauto.
        eapply KernameSet.subset_spec.
        intros ? hin'. eapply sub. eapply KernameSet.singleton_spec in hin'. now subst.
Qed.

Definition sq_wf_ext {Σ : global_env_ext} (wfΣ : ∥ wf_ext Σ ∥) : ∥ wf Σ.1 ∥.
Proof.
  sq. exact X.1.
Qed.

Lemma erase_correct (wfl := Ee.default_wcbv_flags) (Σ : global_env_ext) (wfΣ : ∥ wf_ext Σ ∥) t v Σ' t' deps :
  forall wt : welltyped Σ [] t,
  erase Σ wfΣ [] t wt = t' ->
  KernameSet.subset (term_global_deps t') deps ->
  erase_global deps Σ (sq_wf_ext wfΣ) = Σ' ->
  Σ |-p t ▷ v ->
  exists v', Σ;;; [] |- v ⇝ℇ v' /\ ∥ Σ' ⊢ t' ▷ v' ∥.
Proof.
  intros wt.
  intros HΣ' Hsub Ht' ev.
  pose proof (erases_erase (wfΣ := wfΣ) wt); eauto.
  rewrite HΣ' in H.
  destruct wt as [T wt].
  destruct wfΣ as [wfΣ].
  unshelve epose proof (erase_global_erases_deps (Σ' := Σ') wfΣ wt H _); cycle 2.
  intros.
  rewrite <- Ht'.
  eapply erase_global_includes.
  intros.
  eapply term_global_deps_spec in H; eauto.
  assumption.
  eapply erases_correct; tea.
Qed.

Lemma erase_global_closed Σ deps wfΣ :
  let Σ' := erase_global deps Σ wfΣ in
  closed_env Σ'.
Proof.
  sq.
  induction Σ in deps, w |- *; simpl; auto.
  destruct a as [kn []]; destruct KernameSet.mem.
  + cbn [closed_env forallb].
    red in w; depelim w. 
    rewrite [forallb _ _](IHΣ _ w) andb_true_r.
    rewrite /test_snd /closed_decl /=.
    set (er := erase_global_decls_obligation_1 _ _ _ _ _ _).
    set (er' := erase_global_decls_obligation_2 _ _ _ _ _ _).
    clearbody er er'.
    destruct c as [ty [] univs]; cbn.
    set (obl := erase_constant_body_obligation_1 _ _ _ _ _ _).
    unfold erase_constant_body. cbn. clearbody obl.
    cbn in o0. 2:auto.
    unshelve epose proof (erases_erase (wfΣ := er) obl); eauto.
    cbn in H.
    eapply erases_closed in H => //.
    cbn. destruct er. now eapply PCUICClosed.subject_closed in o0.
  + set (er := erase_global_decls_obligation_4 _ _ _ _ _ _). 
    clearbody er. destruct er.
    eapply IHΣ.
  + cbn [closed_env forallb].
    rewrite {1}/test_snd {1}/closed_decl /=.
    eapply IHΣ.
  + eapply IHΣ.
Qed.
