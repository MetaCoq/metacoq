(* Distributed under the terms of the MIT license. *)
From Coq Require Import Program ssreflect ssrbool.
From Equations Require Import Equations.
Set Equations Transparent.
From MetaCoq.Template Require Import config utils Kernames MCRelations.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICPrimitive
  PCUICReduction PCUICReflect PCUICWeakeningEnv PCUICWeakeningEnvTyp PCUICCasesContexts
  PCUICWeakeningConv PCUICWeakeningTyp PCUICContextConversionTyp PCUICTyping PCUICGlobalEnv PCUICInversion PCUICGeneration
  PCUICConfluence PCUICConversion PCUICUnivSubstitutionTyp PCUICCumulativity PCUICSR PCUICSafeLemmata
  PCUICValidity PCUICPrincipality PCUICElimination PCUICOnFreeVars PCUICWellScopedCumulativity PCUICSN PCUICEtaExpand.
     
From MetaCoq.SafeChecker Require Import PCUICErrors PCUICWfEnv PCUICSafeReduce PCUICSafeRetyping PCUICRetypingEnvIrrelevance.
From MetaCoq.Erasure Require Import EAstUtils EArities Extract Prelim EDeps ErasureProperties ErasureCorrectness.

Local Open Scope string_scope.
Set Asymmetric Patterns.
Local Set Keyed Unification.
Set Default Proof Using "Type*".
Import MCMonadNotation.

Implicit Types (cf : checker_flags).

#[local] Existing Instance extraction_normalizing.

Notation alpha_eq := (All2 (PCUICEquality.compare_decls eq eq)).

Ltac sq := 
  repeat match goal with
        | H : ∥ _ ∥ |- _ => destruct H as [H]
        end; try eapply sq.

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
(* Definition wf_ext_wf Σ : wf_ext Σ -> wf Σ := fst.
#[global]
Hint Resolve wf_ext_wf : core. *)

Ltac specialize_Σ wfΣ :=
  repeat match goal with | h : _ |- _ => specialize (h _ wfΣ) end. 

Section fix_sigma.

  Context {cf : checker_flags} {nor : normalizing_flags}.
  Context (X_type : abstract_env_ext_impl).
  Context (X : X_type.π1).
  
  Local Definition heΣ Σ (wfΣ : abstract_env_ext_rel X Σ) : 
    ∥ wf_ext Σ ∥ :=  abstract_env_ext_wf _ wfΣ.
  Local Definition HΣ Σ (wfΣ : abstract_env_ext_rel X Σ) :
    ∥ wf Σ ∥ := abstract_env_ext_sq_wf _ _ _ wfΣ. 

  Definition term_rel : Relation_Definitions.relation 
    (∑ Γ t, forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> welltyped Σ Γ t) :=
    fun '(Γ2; B; H) '(Γ1; t1; H2) =>
  forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> 
    ∥∑ na A, red Σ Γ1 t1 (tProd na A B) × (Γ1,, vass na A) = Γ2∥.
  
  Definition cod B t := match t with tProd _ _ B' => B = B' | _ => False end.

  Lemma wf_cod : WellFounded cod.
  Proof.
    sq. intros ?. induction a; econstructor; cbn in *; intros; try tauto; subst. eauto.
  Defined.

  Lemma wf_cod' : WellFounded (Relation_Operators.clos_trans _ cod).
  Proof.
    eapply Subterm.WellFounded_trans_clos. exact wf_cod.
  Defined.

  Lemma Acc_no_loop A (R : A -> A -> Prop) t : Acc R t -> R t t -> False.
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
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ']]. 
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
          eapply Relation_Properties.clos_rtn1_rt in X1.
          eapply cored_red_trans in X0; [| exact X1 ].
          eapply Acc_no_loop in X0. eauto.
          eapply @normalisation; eauto.
        * constructor. do 2 eexists. now split.
  Unshelve.
  - intros. destruct H' as [].
    rewrite <- (abstract_env_ext_irr _ H2) in X0; eauto.  
    rewrite <- (abstract_env_ext_irr _ H2) in wf; eauto.  
    eapply inversion_Prod in X0 as (? & ? & ? & ? & ?) ; auto.
    eapply cored_red in H0 as [].
    econstructor. econstructor. econstructor. eauto.
    2:reflexivity. econstructor; pcuic. 
    rewrite <- (abstract_env_ext_irr _ H2) in X0; eauto.  
    eapply subject_reduction; eauto.
  - intros. rewrite <- (abstract_env_ext_irr _ H0) in wf; eauto.  
    rewrite <- (abstract_env_ext_irr _ H0) in X0; eauto.  
    rewrite <- (abstract_env_ext_irr _ H0) in r; eauto.  
    eapply red_welltyped; sq.
    3:eapply Relation_Properties.clos_rtn1_rt in r; eassumption. 
    all:eauto.
  Defined.

  Instance wf_reduction : WellFounded term_rel.
  Proof.
    refine (Wf.Acc_intro_generator 1000 _).
    exact wf_reduction_aux.
  Defined.
  
  Opaque wf_reduction.
  
  #[tactic="idtac"]
  Equations? is_arity Γ (HΓ : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> ∥wf_local Σ Γ∥) T 
    (HT : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> welltyped Σ Γ T) : bool
    by wf ((Γ;T;HT) : (∑ Γ t, forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> welltyped Σ Γ t)) term_rel := 
      {
        is_arity Γ HΓ T HT with inspect (@reduce_to_sort _ _ X_type X Γ T HT) => {
        | exist (Checked_comp H) rsort => true ;
        | exist (TypeError_comp _) rsort with 
            inspect (@reduce_to_prod _ _ X_type X Γ T HT) => {
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
      repeat specialize_Σ wfΣ'. 
      destruct HT as [s HT].
      sq.
      eapply subject_reduction_closed in HT; tea. 2:pcuic.
      eapply inversion_Prod in HT as [? [? [? []]]]. 2:pcuic.
      exists na, A. split => //.
      eapply H.
  Defined.
  
  Lemma is_arityP Γ (HΓ : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> ∥wf_local Σ Γ∥) T 
    (HT : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> welltyped Σ Γ T) :
    reflect (forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> 
              Is_conv_to_Arity Σ Γ T) (is_arity Γ HΓ T HT).
  Proof.
    funelim (is_arity Γ HΓ T HT).
    - constructor.
      destruct H as [s Hs]. clear H0 rsort. 
      pose proof (abstract_env_ext_exists X) as [[Σ wfΣ]].
      specialize (Hs _ wfΣ) as [Hs]. 
      intros. rewrite (abstract_env_ext_irr _ H wfΣ).
      exists (tSort s); split => //.
    - clear H0 H1. 
      destruct X0; constructor; clear rprod rsort.
      * red.
        pose proof (abstract_env_ext_exists X) as [[Σ wfΣ]].
        specialize_Σ wfΣ. sq.
        intros. rewrite (abstract_env_ext_irr _ H0 wfΣ).
        destruct i as [T' [[HT'] isa]].
        exists (tProd na A T'); split => //. split.
        etransitivity; tea. now eapply closed_red_prod_codom.
      * pose proof (abstract_env_ext_exists X) as [[Σ wfΣ]].
        pose proof (abstract_env_ext_wf X wfΣ) as [wfΣ'].
        specialize_Σ wfΣ. sq. 
        intros [T' [[HT'] isa]]; eauto.
        destruct (PCUICContextConversion.closed_red_confluence H HT') as (? & ? & ?); eauto.
        eapply invert_red_prod in c as (? & ? & []); eauto. subst.
        apply n. intros. rewrite (abstract_env_ext_irr _ H0 wfΣ).
        red. exists x1.
        split => //.
        eapply isArity_red in isa. 2:exact c0.
        now cbn in isa.
    - constructor.
      clear H H0. pose proof (abstract_env_ext_exists X) as [[Σ wfΣ]].
      pose proof (abstract_env_ext_wf X wfΣ) as [wfΣ'].      
      symmetry in rprod. symmetry in rsort.
      intros isc. specialize_Σ wfΣ.
      eapply Is_conv_to_Arity_inv in isc as [].
      * destruct H as [na [A [B [Hr]]]].
        apply e. exists na, A, B. 
        intros ? H. now rewrite (abstract_env_ext_irr _ H wfΣ).
      * destruct H as [u [Hu]].
        apply a0. exists u. 
        intros ? H. now rewrite (abstract_env_ext_irr _ H wfΣ).
  Qed.
  
End fix_sigma.

Opaque wf_reduction_aux.
Transparent wf_reduction.

(** Deciding if a term is erasable or not as a total function on well-typed terms.
  A term is erasable if:
  - it represents a type, i.e., its type is an arity
  - it represents a proof: its sort is Prop.
*)

Derive NoConfusion for typing_result_comp.

Opaque is_arity type_of_typing.

Definition inspect {A} (x : A) : { y : A | x = y } := exist x eq_refl.

Equations inspect_bool (b : bool) : { b } + { ~~ b } := 
  inspect_bool true := left eq_refl;
  inspect_bool false := right eq_refl.

#[tactic="idtac"]
Equations? is_erasableb X_type X (Γ : context) (T : PCUICAst.term) 
  (wt : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> welltyped Σ Γ T) : bool :=
  is_erasableb X_type X Γ t wt with @type_of_typing extraction_checker_flags _ X_type X Γ t wt :=
    { | T with is_arity X_type X Γ _ T.π1 _ := 
      { | true => true
        | false => let s := @sort_of_type extraction_checker_flags _ X_type X Γ T.π1 _ in
          is_propositional s.π1 } }.
  Proof.
    - intros. specialize_Σ H. destruct wt; sq. 
      pcuic.
    - intros. specialize_Σ H. destruct T as [T Ht].
      cbn. destruct (Ht Σ H) as [[tT Hp]].
      pose proof (abstract_env_ext_wf X H) as [wf].
      eapply validity in tT. pcuic.
    - intros. destruct T as [T Ht].
      cbn in *. specialize (Ht Σ H) as [[tT Hp]].
      pose proof (abstract_env_ext_wf X H) as [wf].
      eapply validity in tT. now sq.
  Qed.
Transparent is_arity type_of_typing.

Lemma is_erasableP {X_type X} {Γ : context} {t : PCUICAst.term}
  {wt : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> welltyped Σ Γ t} : 
  reflect (forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> 
           ∥ isErasable Σ Γ t ∥) (is_erasableb X_type X Γ t wt).
Proof.
  funelim (is_erasableb X_type X Γ t wt).
  - constructor. intros. pose proof (abstract_env_ext_wf _ H) as [wf].
    destruct type_of_typing as [x Hx]. cbn -[is_arity sort_of_type] in *.  
    destruct (Hx _ H) as [[HT ?]]. 
    move/is_arityP: Heq => / (_ _ H) [T' [redT' isar]]. specialize_Σ H. 
    sq. red. exists T'. eapply type_reduction_closed in HT.
    2: eassumption. eauto.  
  - destruct type_of_typing as [x Hx]. cbn -[sort_of_type is_arity] in *.  
    destruct (sort_of_type _ _ _ _). cbn.
    destruct (is_propositional x0) eqn:isp; constructor.
    * clear Heq. intros. 
      pose proof (abstract_env_ext_wf _ H) as [wf]. 
      specialize_Σ H. 
      destruct Hx as [[HT ?]].
      destruct s as [Hs]. sq.
      exists x; split => //. right.
      exists x0. now split.
    * pose proof (abstract_env_ext_exists X) as [[Σ wfΣ]].
      move => / (_ _ wfΣ) [[T' [HT' er]]].
      pose proof (abstract_env_ext_wf _ wfΣ) as [wf].
      move/is_arityP: Heq => nisa. 
      specialize_Σ wfΣ. 
      destruct Hx as [[HT ?]].
      specialize (p _ HT').
      destruct er as [isa|[u' [Hu' isp']]].
      { apply nisa. intros. rewrite (abstract_env_ext_irr _ H wfΣ). 
        eapply invert_cumul_arity_r; tea. }
      { destruct s as [Hs].
        unshelve epose proof (H := unique_sorting_equality_propositional _ _ wf Hs Hu' p) => //. reflexivity. reflexivity. congruence. }
  Qed.

Equations? is_erasable {X_type X} (Γ : context) (t : PCUICAst.term) 
  (wt : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> welltyped Σ Γ t) : 
  forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> 
    { ∥ isErasable Σ Γ t ∥ } + { ∥ isErasable Σ Γ t -> False ∥ } :=
  is_erasable Γ T wt Σ wfΣ with inspect_bool (is_erasableb X_type X Γ T wt) :=
    { | left ise => left _
      | right nise => right _ }.
Proof.
  pose proof (abstract_env_ext_wf _ wfΣ) as [wf].
  now move/is_erasableP: ise => //.
  move/(elimN is_erasableP): nise.
  intros; sq => ise. apply nise. 
  intros. now rewrite (abstract_env_ext_irr _ H wfΣ).
Qed.

Section Erase.
  Context {nor : normalizing_flags}.
  Context (X_type : abstract_env_ext_impl (cf := extraction_checker_flags)).
  Context (X : X_type.π1).

  (* Ltac sq' := 
             repeat match goal with
                    | H : ∥ _ ∥ |- _ => destruct H; try clear H
                    end; try eapply sq. *)

  (* Bug in equationa: it produces huge goals leading to stack overflow if we
    don't try reflexivity here. *)
  Ltac Equations.Prop.DepElim.solve_equation c ::= 
    intros; try reflexivity; try Equations.Prop.DepElim.simplify_equation c;
     try
	  match goal with
    | |- ImpossibleCall _ => DepElim.find_empty
    | _ => try red; try reflexivity || discriminates
    end.

  Opaque is_erasableb.
  
  #[tactic="idtac"]
  Equations? erase (Γ : context) (t : term) 
    (Ht : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> welltyped Σ Γ t) : E.term
      by struct t :=
  { erase Γ t Ht with inspect_bool (is_erasableb X_type X Γ t Ht) :=
  { | left he := E.tBox; 
    | right he with t := {
      | tRel i := E.tRel i
      | tVar n := E.tVar n
      | tEvar m l := E.tEvar m (erase_terms Γ l _)
      | tSort u := !%prg
      | tConst kn u := E.tConst kn
      | tInd kn u := !%prg
      | tConstruct kn k u := E.tConstruct kn k []
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
        E.tCoFix mfix' n
      | tPrim p := E.tPrim (erase_prim_val p) }
    } } 
  where erase_terms (Γ : context) (l : list term) (Hl : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> ∥ All (welltyped Σ Γ) l ∥) : list E.term :=
  { erase_terms Γ [] _ := [];
    erase_terms Γ (t :: ts) _ := 
      let t' := erase Γ t _ in
      let ts' := erase_terms Γ ts _ in
      t' :: ts' }
(** We assume that there are no lets in contexts, so nothing has to be expanded.
  In particular, note that #|br.(bcontext)| = context_assumptions br.(bcontext) when no lets are present.
  *)
  where erase_brs (Γ : context) p (brs : list (branch term)) 
    (Ht : forall Σ : global_env_ext, abstract_env_ext_rel X Σ ->
          ∥ All (fun br => welltyped Σ (Γ ,,, inst_case_branch_context p br) (bbody br)) brs ∥) :
    list (list name × E.term) := 
  { erase_brs Γ p [] Ht := [];
    erase_brs Γ p (br :: brs) Hbrs := 
      let br' := erase (Γ ,,, inst_case_branch_context p br) (bbody br) _ in
      let brs' := erase_brs Γ p brs _ in
      (erase_context br.(bcontext), br') :: brs' }
  
  where erase_fix (Γ : context) (mfix : mfixpoint term)
    (Ht : forall Σ : global_env_ext, abstract_env_ext_rel X Σ ->
          ∥ All (fun d => isLambda d.(dbody) /\ welltyped Σ Γ d.(dbody)) mfix ∥) : E.mfixpoint E.term :=
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
      (Ht : forall Σ : global_env_ext, abstract_env_ext_rel X Σ ->
            ∥ All (fun d => welltyped Σ Γ d.(dbody)) mfix ∥) : E.mfixpoint E.term :=
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
    all: try pose proof (abstract_env_ext_wf _ H) as [wf];
         specialize_Σ H.
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
    - move/is_erasableP: he. intro. apply he. intros.   
      pose proof (abstract_env_ext_wf _ H) as [wf].
      specialize_Σ H. destruct Ht as [ty Ht]. sq. 
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
    - sq. now depelim Hl.
    - sq. now depelim Hl.
    - sq. now depelim Hbrs.
    - sq. now depelim Hbrs.
    - sq. now depelim Hmfix.
    - clear dbody'0. specialize_Σ H. sq. now depelim Hmfix.
    - sq. now depelim Hmfix.
    - sq. now depelim Hmfix.
  Qed.
  
End Erase.

Lemma is_erasableb_irrel {X_type X Γ t} wt wt' : is_erasableb X_type X Γ t wt = is_erasableb X_type X Γ t wt'.
Proof.
  destruct (@is_erasableP X_type X Γ t wt);
  destruct (@is_erasableP X_type X Γ t wt') => //.
Qed.

Ltac iserasableb_irrel :=
  match goal with
  [ H : context [is_erasableb ?X_type ?X ?Γ ?t ?wt], Heq : inspect_bool _ = _ |- context [ is_erasableb _ _ _ _ ?wt'] ] => 
    generalize dependent H; rewrite (is_erasableb_irrel wt wt'); intros; rewrite Heq
  end.

Ltac simp_erase := simp erase; rewrite -?erase_equation_1.

Lemma erase_irrel X_type X : 
  (forall Γ t wt, forall wt', erase X_type X Γ t wt = erase X_type X Γ t wt') ×
  (forall Γ l wt, forall wt', erase_terms X_type X Γ l wt = erase_terms X_type X Γ l wt') ×
  (forall Γ p l wt, forall wt', erase_brs X_type X Γ p l wt = erase_brs X_type X Γ p l wt') ×
  (forall Γ l wt, forall wt', erase_fix X_type X Γ l wt = erase_fix X_type X Γ l wt') ×
  (forall Γ l wt, forall wt', erase_cofix X_type X Γ l wt = erase_cofix X_type X Γ l wt').
Proof.
  apply: (erase_elim X_type X
    (fun Γ t wt e => 
      forall wt' : forall Σ : global_env_ext, abstract_env_ext_rel X Σ ->  welltyped Σ Γ t, e = erase X_type X Γ t wt')
    (fun Γ l awt e => forall wt', e = erase_terms X_type X Γ l wt')
    (fun Γ p l awt e => forall wt', e = erase_brs X_type X Γ p l wt')
    (fun Γ l awt e => forall wt', e = erase_fix X_type X Γ l wt')
    (fun Γ l awt e => forall wt', e = erase_cofix X_type X Γ l wt')); clear.
  all:intros *; intros; simp_erase.
  all:try simp erase; try iserasableb_irrel; simp_erase => //.
  all:try clear he Heq.
  all:try bang.
  all:try solve [cbn; f_equal; eauto].
  all:try solve [cbn; repeat (f_equal; eauto)].
  cbn. f_equal. f_equal. now rewrite (H (erase_obligation_19 X_type X Γ d mfix wt')).
  now rewrite (H0 (erase_obligation_20 X_type X Γ d mfix wt')).
Qed.

Lemma erase_terms_eq X_type X Γ ts wt : 
  erase_terms X_type X Γ ts wt = map_All (erase X_type X Γ) ts wt.
Proof.
  funelim (map_All (erase X_type X Γ) ts wt); cbn; auto.
  f_equal => //. apply erase_irrel.
  rewrite -H. eapply erase_irrel.
Qed.

Opaque wf_reduction.

#[global]
Hint Constructors typing erases : core.

Lemma erase_to_box {X_type X} {Γ t} (wt : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> welltyped Σ Γ t) :
  forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> 
  let et := erase X_type X Γ t wt in 
  if is_box et then ∥ isErasable Σ Γ t ∥
  else ~ ∥ isErasable Σ Γ t ∥.
Proof.
  cbn. intros. 
  revert Γ t wt.
  apply (erase_elim X_type X
    (fun Γ t wt e => 
      if is_box e then ∥ isErasable Σ Γ t ∥ else ∥ isErasable Σ Γ t ∥ -> False)
    (fun Γ l awt e => True)
    (fun Γ p l awt e => True)
    (fun Γ l awt e => True)
    (fun Γ l awt e => True)); intros.

  all:try discriminate; auto.
  all:cbn -[isErasable].
  all:try solve [  match goal with 
  [ H : context [ is_erasableb ?X_type ?X ?Γ ?t ?Ht ] |- _ ] => 
    destruct (@is_erasableP X_type X Γ t Ht)  => //
  end; intro; 
    match goal with n : ~ _ |- _  => apply n end; intros ? HH; now rewrite (abstract_env_ext_irr _ HH H) ].
  all:try bang.
  - destruct (@is_erasableP X_type X Γ t Ht) => //. apply s; eauto. 
  - cbn in *. rewrite is_box_tApp.
    destruct (@is_erasableP X_type X Γ (tApp f u) Ht) => //.
    destruct is_box.
    * cbn in *. clear H1.
      pose proof (abstract_env_ext_wf _ H) as [wf]. cbn in *. 
      specialize_Σ H. destruct Ht, H0.
      eapply (EArities.Is_type_app _ _ _ [_]); eauto.
      eauto using typing_wf_local.
    * intro; apply n; intros. now rewrite (abstract_env_ext_irr _ H3 H).
Defined.

Lemma erases_erase {X_type X Γ t} 
(wt : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> welltyped Σ Γ t) :
forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> erases Σ Γ t (erase X_type X Γ t wt).
Proof.
  intros. revert Γ t wt.
  apply (erase_elim X_type X
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
      [ H : context [is_erasableb ?X_type ?X ?Γ ?t ?Ht ] |- _ ] => 
        destruct (@is_erasableP X_type X Γ t Ht) as [[H']|H'] => //; eauto ;
        try now eapply erases_box
    end.
    all: try solve [constructor; eauto].
  all:try destruct (abstract_env_ext_wf X H) as [wfΣ].
  all: cbn in *; try constructor; auto;
  specialize_Σ H.
  
  - clear Heq.
    eapply nisErasable_Propositional in Ht; auto.
    intro; eapply H'; intros. now rewrite (abstract_env_ext_irr _ H0 H).  
  - cbn.
    destruct (Ht _ H).
    destruct (inversion_Case _ _ X1) as [mdecl [idecl []]]; eauto.
    eapply elim_restriction_works; eauto.
    intros isp. eapply isErasable_Proof in isp.
    eapply H'; intros. now rewrite (abstract_env_ext_irr _ H1 H).

  - clear Heq.
    destruct (Ht _ H) as [? Ht'].
    clear H0. eapply inversion_Proj in Ht' as (?&?&?&?&?&?&?&?&?&?); auto.
    eapply elim_restriction_works_proj; eauto. exact d.
    intros isp. eapply isErasable_Proof in isp.
    eapply H'; intros. now rewrite (abstract_env_ext_irr _ H0 H).

  - cbn. pose proof (abstract_env_ext_wf _ H) as [wf].
    pose proof Hmfix as Hmfix'.
    specialize (Hmfix' _ H). destruct Hmfix'.
    depelim X1. destruct a.
    assert (exists na ty bod, dbody d = tLambda na ty bod).
    { clear -H1. destruct (dbody d) => //. now do 3 eexists. }
    destruct H3 as [na [ty [bod eq]]]. rewrite {1 3}eq /= //.
    move: H0. rewrite {1}eq.
    set (et := erase _ _ _ _ _). clearbody et.
    intros He. depelim He. cbn.
    split => //. cbn. rewrite eq. now constructor.
    split => //. cbn. rewrite eq.
    destruct H2.
    eapply Is_type_lambda in X2; tea. 2:pcuic. destruct X2.
    now constructor.
Qed.

Transparent wf_reduction.

(** We perform erasure up-to the minimal global environment dependencies of the term: i.e.  
  we don't need to erase entries of the global environment that will not be used by the erased
  term.
*)

Program Definition erase_constant_body X_type X 
  (cb : constant_body) 
  (Hcb : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> ∥ on_constant_decl (lift_typing typing) Σ cb ∥) : E.constant_body * KernameSet.t :=  
  let '(body, deps) := match cb.(cst_body) with
          | Some b => 
            let b' := erase X_type X [] b _ in
            (Some b', term_global_deps b')
          | None => (None, KernameSet.empty)
          end in
  ({| E.cst_body := body; |}, deps).
Next Obligation.
Proof.
  specialize_Σ H. sq. red in Hcb. 
  rewrite <-Heq_anonymous in Hcb. now eexists.
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
  {| E.ind_finite := mib.(ind_finite);
     E.ind_npars := mib.(ind_npars);
     E.ind_bodies := bodies; |}.

Import EnvMap.
  
Require Import Morphisms.
From MetaCoq.Template Require Import uGraph.

Lemma is_arity_irrel {X_type : abstract_env_ext_impl} {X : X_type.π1}
  {X_type' : abstract_env_ext_impl} {X' : X_type'.π1} {Γ h h' t wt wt'} : 
  Hlookup X_type X X_type' X' ->
  is_arity X_type X Γ h t wt = is_arity X_type' X' Γ h' t wt'.
Proof.
  intros hl.
  funelim (is_arity X_type X _ _ _ _).
  - epose proof (reduce_to_sort_irrel hl eq_refl HT wt').
    rewrite -rsort in H1.
    simp is_arity.
    epose proof (reduce_to_sort_irrel hl eq_refl HT wt').
    destruct (PCUICSafeReduce.inspect) eqn:hi.
    rewrite -e in H1.
    destruct x => //.
  - epose proof (reduce_to_sort_irrel hl eq_refl HT wt').
    rewrite -rsort in H3.
    rewrite [is_arity X_type' X' _ _ _ _]is_arity_equation_1.
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

Lemma is_erasableb_irrel_global_env {X_type X X_type' X'} {Γ t wt wt'} :
  (forall Σ Σ' : global_env_ext, abstract_env_ext_rel X Σ -> 
      abstract_env_ext_rel X' Σ' -> ∥ extends_decls Σ' Σ ∥ /\ (Σ.2 = Σ'.2)) ->
  is_erasableb X_type X Γ t wt = is_erasableb X_type' X' Γ t wt'.
Proof.
  intro ext. 
  (* ext eqext. *)
  assert (hl : Hlookup X_type X X_type' X').
  { red. intros. specialize (ext _ _ H H0) as [[?] ?].
    split. intros.
    rewrite -(abstract_env_lookup_correct _ _ H).
    rewrite -(abstract_env_lookup_correct _ _ H0).
    rewrite H2 H3. pose proof (abstract_env_ext_wf _ H) as [?].
    eapply extends_lookup_env in H3; try apply e; eauto. clear -H2 H3. congruence.
    destruct X0.
    rewrite -(abstract_env_ext_retroknowledge_correct _ H).
    rewrite -(abstract_env_ext_retroknowledge_correct _ H0).
    congruence. }
  simp is_erasableb.
  set (obl := is_erasableb_obligation_2 _ _ _ _). clearbody obl.
  set(ty := (type_of_typing X_type' _ _ _ wt')) in *.
  set(ty' := (type_of_typing X_type _ _ _ wt)) in *.
  assert (ty.π1 = ty'.π1).
  { subst ty ty'. unfold type_of_typing. symmetry. 
    eapply infer_irrel => //. }
  clearbody ty. clearbody ty'.
  destruct ty, ty'. cbn in H. subst x0.
  cbn -[is_arity] in obl |- *.
  set (obl' := is_erasableb_obligation_1 X_type' X' Γ t wt').
  set (obl'' := is_erasableb_obligation_2 X_type' X' Γ t _).
  clearbody obl'. clearbody obl''.
  rewrite (is_arity_irrel (X:=X) (X' := X') (wt' := obl'' (x; s))) => //.
  destruct is_arity  => //. simp is_erasableb.
  set (obl2 := is_erasableb_obligation_3 _ _ _ _ _).
  set (obl2' := is_erasableb_obligation_3 _ _ _ _ _).
  simpl. f_equal. now apply sort_of_type_irrel.
Qed.

Ltac iserasableb_irrel_env :=
  match goal with
  [ H : context [is_erasableb ?X_type ?X ?Γ ?t ?wt], Heq : inspect_bool _ = _ |- context [ is_erasableb _ _ _ _ ?wt'] ] => 
    generalize dependent H; rewrite (@is_erasableb_irrel_global_env _ _ _ _ _ _ wt wt') //; intros; rewrite Heq
  end.

Lemma erase_irrel_global_env {X_type X X_type' X'} {Γ t wt wt'} :
  (forall Σ Σ' : global_env_ext, abstract_env_ext_rel X Σ -> 
    abstract_env_ext_rel X' Σ' -> ∥ extends_decls Σ' Σ ∥ /\ (Σ.2 = Σ'.2)) ->
  erase X_type X Γ t wt = erase X_type' X' Γ t wt'.
Proof.
  intros ext. 
  move: wt'.
  eapply (erase_elim X_type X
  (fun Γ t wt e => 
    forall (wt' : forall Σ' : global_env_ext, abstract_env_ext_rel X' Σ' ->  welltyped Σ' Γ t), 
    e = erase X_type' X' Γ t wt')
  (fun Γ l awt e => forall wt',
    e = erase_terms X_type' X' Γ l wt')
  (fun Γ p l awt e => forall wt', 
    e = erase_brs X_type' X'  Γ p l wt')
  (fun Γ l awt e => forall wt', 
    e = erase_fix X_type' X'  Γ l wt')
  (fun Γ l awt e => forall wt', 
    e = erase_cofix X_type' X'  Γ l wt')).
  all:intros *; intros; simp_erase.
  simp erase.
  all:try simp erase; try iserasableb_irrel_env; simp_erase => //.
  all:try clear he Heq.
  all:try bang.
  all:try solve [cbn; repeat (f_equal; eauto)].
  cbn. f_equal. eauto. f_equal.
  now rewrite (H (erase_obligation_19 X_type' X' Γ0 d mfix wt')).
  now rewrite (H0 (erase_obligation_20 X_type' X'  Γ0 d mfix wt')).
Qed.

Lemma erase_constant_body_suffix {X_type X X_type' X'} {cb ondecl ondecl'} :
(forall Σ Σ' : global_env_ext, abstract_env_ext_rel X Σ -> 
  abstract_env_ext_rel X' Σ' -> ∥ extends_decls Σ' Σ ∥ /\ (Σ.2 = Σ'.2)) ->
erase_constant_body X_type X cb ondecl = erase_constant_body X_type' X' cb ondecl'.
Proof.
  intros ext.
  destruct cb => //=.
  destruct cst_body0 => //=.
  unfold erase_constant_body; simpl => /=.
  f_equal. f_equal. f_equal.
  eapply erase_irrel_global_env; tea.
  f_equal.
  eapply erase_irrel_global_env; tea.
Qed.

Require Import Morphisms.
From MetaCoq.Template Require Import uGraph.
Global Instance proper_pair_levels_gcs : Proper ((=_lset) ==> GoodConstraintSet.Equal ==> (=_gcs)) (@pair LevelSet.t GoodConstraintSet.t).
Proof.
  intros l l' eq gcs gcs' eq'.
  split; cbn; auto.
Qed.

Program Fixpoint erase_global_decls {X_type : abstract_env_impl} (deps : KernameSet.t) (X : X_type.π1) (decls : global_declarations) 
  (prop : forall Σ : global_env, abstract_env_rel X Σ -> Σ.(declarations) = decls) : E.global_declarations :=
  match decls with
  | [] => []
  | (kn, ConstantDecl cb) :: decls =>
    let X' := abstract_pop_decls X in
    if KernameSet.mem kn deps then
      let Xext := abstract_make_wf_env_ext X' (cst_universes cb) _ in
      let cb' := erase_constant_body X_type.π2.π1 Xext cb _ in
      let deps := KernameSet.union deps (snd cb') in
      let X'' := erase_global_decls deps X' decls _ in
      ((kn, E.ConstantDecl (fst cb')) :: X'')
    else
      erase_global_decls deps X' decls _

  | (kn, InductiveDecl mib) :: decls =>
    let X' := abstract_pop_decls X in
    if KernameSet.mem kn deps then
      let mib' := erase_mutual_inductive_body mib in
      let X'' := erase_global_decls deps X' decls _ in
      ((kn, E.InductiveDecl mib') :: X'')
    else erase_global_decls deps X' decls _
  end.
Next Obligation. 
  pose proof (abstract_env_wf _ H) as [wf]. 
  pose proof (abstract_env_exists X) as [[? HX]]. 
  pose proof (abstract_env_wf _ HX) as [wfX].
  assert (prop': forall Σ : global_env, abstract_env_rel X Σ -> exists d, Σ.(declarations) = d :: decls).
  { now eexists. }
  destruct (abstract_pop_decls_correct X decls prop' _ _ HX H) as [? []].
  clear H. specialize (prop _ HX). destruct x, Σ, H0; cbn in *.
  subst. sq. destruct wfX. depelim o0. split => //.
Qed.
Next Obligation.
  pose proof (abstract_env_ext_wf _ H) as [wf]. 
  pose proof (abstract_env_exists (abstract_pop_decls X)) as [[? HX']]. 
  pose proof (abstract_env_wf _ HX') as [wfX'].
  pose proof (abstract_env_exists X) as [[? HX]]. 
  pose proof (abstract_env_wf _ HX) as [wfX].
  assert (prop': forall Σ : global_env, abstract_env_rel X Σ -> exists d, Σ.(declarations) = d :: decls).
  { now eexists. }
  pose proof (abstract_pop_decls_correct X decls prop' _ _ HX HX') as [? []].
  pose proof (abstract_make_wf_env_ext_correct _ _ _ _ _ HX' H). 
  clear H HX'. specialize (prop _ HX). destruct x, Σ as [[] u], H0; cbn in *.
  subst. sq. inversion H3. subst. clear H3. destruct wfX. cbn in *.
  rewrite prop in o0. depelim o0. cbn in o2. apply o2.
Qed.
Next Obligation.
  pose proof (abstract_env_exists X) as [[? HX]]. 
  assert (prop': forall Σ : global_env, abstract_env_rel X Σ -> exists d, Σ.(declarations) = d :: decls).
  { now eexists. }
  now pose proof (abstract_pop_decls_correct X decls prop' _ _ HX H).
Qed.  
Next Obligation.  
pose proof (abstract_env_exists X) as [[? HX]]. 
assert (prop': forall Σ : global_env, abstract_env_rel X Σ -> exists d, Σ.(declarations) = d :: decls).
{ now eexists. }
now pose proof (abstract_pop_decls_correct X decls prop' _ _ HX H).
Qed.  
Next Obligation.
  pose proof (abstract_env_exists X) as [[? HX]]. 
  assert (prop': forall Σ : global_env, abstract_env_rel X Σ -> exists d, Σ.(declarations) = d :: decls).
  { now eexists. }
  now pose proof (abstract_pop_decls_correct X decls prop' _ _ HX H).
Qed.  
Next Obligation.
pose proof (abstract_env_exists X) as [[? HX]]. 
assert (prop': forall Σ : global_env, abstract_env_rel X Σ -> exists d, Σ.(declarations) = d :: decls).
{ now eexists. }
now pose proof (abstract_pop_decls_correct X decls prop' _ _ HX H).
Qed.  

Lemma erase_global_decls_irr X_type deps (X:X_type.π1) decls prf prf' :
  erase_global_decls deps X decls prf =
  erase_global_decls deps X decls prf'.
Proof. 
  revert X deps prf prf'.
  induction decls; eauto. intros. destruct a as [kn []]; cbn.
  - destruct KernameSet.mem; cbn.
    erewrite erase_constant_body_suffix. f_equal.
    eapply IHdecls. intros. 
    pose proof (abstract_env_exists (abstract_pop_decls X)) as [[env wf]].
    rewrite (abstract_make_wf_env_ext_correct (abstract_pop_decls X) (cst_universes c) _ _ _ wf H). 
    now rewrite (abstract_make_wf_env_ext_correct (abstract_pop_decls X) (cst_universes c) _ _ _ wf H0). 
    apply IHdecls.
  - destruct KernameSet.mem; cbn. f_equal. eapply IHdecls.
    apply IHdecls. 
Qed.

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
  - econstructor; eauto. eapply weakening_env_declared_constructor; eauto; tc.
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

Lemma erase_constant_body_correct X_type X cb 
  (onc : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> ∥ on_constant_decl (lift_typing typing) Σ cb ∥) :
  forall Σ Σ', abstract_env_ext_rel X Σ -> 
  wf Σ' -> extends_decls Σ Σ' ->
  erases_constant_body (Σ', Σ.2) cb (fst (erase_constant_body X_type X cb onc)).
Proof.
  red. destruct cb as [name [bod|] univs]; simpl; eauto. intros.
  set (ecbo := erase_constant_body_obligation_1 X_type X _ _ _ _). clearbody ecbo.
  cbn in *. specialize_Σ H. sq.  
  eapply (erases_weakeninv_env (Σ := Σ) (Σ' := (Σ', univs))); simpl; eauto.
  now eapply erases_erase.
Qed.

Lemma erase_constant_body_correct' {X_type X} {cb} 
  {onc : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> ∥ on_constant_decl (lift_typing typing) Σ cb ∥} 
  {body} :
  EAst.cst_body (fst (erase_constant_body X_type X cb onc)) = Some body ->
  forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> 
  ∥ ∑ t T, (Σ ;;; [] |- t : T) * (Σ ;;; [] |- t ⇝ℇ body) *
    (term_global_deps body = snd (erase_constant_body X_type X cb onc)) ∥.
Proof.
  intros. destruct cb as [name [bod|] univs]; simpl; [| now simpl in H].
  simpl in H. noconf H. 
  set (obl :=(erase_constant_body_obligation_1 X_type X
  {|
  cst_type := name;
  cst_body := Some bod;
  cst_universes := univs |} onc bod eq_refl)). clearbody obl. cbn in *. 
  specialize_Σ H0. destruct (obl _ H0). sq.
  exists bod, A; intuition auto. now eapply erases_erase. 
Qed.

Lemma erases_mutual {Σ mdecl m} : 
  on_inductive cumulSpec0 (lift_typing typing) (Σ, ind_universes m) mdecl m ->
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

Lemma erase_global_includes X_type (X:X_type.π1) deps decls prf deps' :
  (forall d, KernameSet.In d deps' -> 
    forall Σ : global_env, abstract_env_rel X Σ -> ∥ ∑ decl, lookup_env Σ d = Some decl ∥) ->
  KernameSet.subset deps' deps ->
  forall Σ : global_env, abstract_env_rel X Σ ->
  let Σ' := erase_global_decls deps X decls prf in
  includes_deps Σ Σ' deps'.
Proof.
  intros ? sub Σ wfΣ; cbn. induction decls in X, H, sub, prf, deps, deps', Σ , wfΣ |- *.
  - simpl. intros i hin. elimtype False.
    specialize (H i hin) as [[decl Hdecl]]; eauto.
    rewrite /lookup_env (prf _ wfΣ) in Hdecl. noconf Hdecl.
  - intros i hin.
    destruct (abstract_env_wf _ wfΣ) as [wf].
    destruct a as [kn d].
    eapply KernameSet.subset_spec in sub.
    edestruct (H i hin) as [[decl Hdecl]]; eauto. unfold lookup_env in Hdecl.
    pose proof (eqb_spec i kn).
    rewrite (prf _ wfΣ) in Hdecl. move: Hdecl. cbn -[erase_global_decls].
    elim: H0. intros -> [= <-].
    * destruct d as [|]; [left|right].
      { cbn. set (Xpop := abstract_pop_decls X).
        set (Xmake :=  abstract_make_wf_env_ext Xpop (cst_universes c) _).
        epose proof (abstract_env_exists Xpop) as [[Σpop wfpop]].
        epose proof (abstract_env_ext_exists Xmake) as [[Σmake wfmake]].
        exists c. split; auto. red.
        unfold lookup_env; simpl; rewrite (prf _ wfΣ). cbn. rewrite eq_kername_refl //.
        pose proof (sub _ hin) as indeps.
        eapply KernameSet.mem_spec in indeps.
        unfold EGlobalEnv.declared_constant. 
        edestruct (H _ hin) as [[decl hd]]; eauto. 
        eexists; intuition eauto.
        rewrite indeps. cbn.
        rewrite eq_kername_refl. reflexivity.
        eapply (erase_constant_body_correct _ _ _ _ (Σpop , _)); eauto.
        rewrite <- (abstract_make_wf_env_ext_correct Xpop (cst_universes c) _ Σpop Σmake wfpop wfmake); eauto. 
        red. simpl. unshelve epose (abstract_pop_decls_correct X decls _ Σ Σpop wfΣ wfpop).
        { intros. now eexists. }
        split => //. intuition eauto.
        exists [(kn, ConstantDecl c)]; intuition eauto. rewrite H0; eauto.
        now destruct a. 
        rewrite indeps. unshelve epose proof (abstract_pop_decls_correct X decls _ Σ Σpop wfΣ wfpop) as [Hpop [Hpop' Hpop'']].
        { intros. now eexists. }
        pose (prf' := prf _ wfΣ).
        destruct Σ. cbn in *. rewrite Hpop' Hpop'' prf'. rewrite <- Hpop at 1.  
        eapply (erases_deps_cons Σpop). 
          rewrite <- Hpop'. apply wf.
          rewrite Hpop. rewrite prf' in wf. destruct wf. now rewrite Hpop'' Hpop' in o0. 

        pose proof (erase_constant_body_correct' H0). specialize_Σ wfmake. 
        sq. destruct H1 as [bod [bodty [[Hbod Hebod] Heqdeps]]].
        rewrite (abstract_make_wf_env_ext_correct Xpop (cst_universes c) _ Σpop Σmake wfpop wfmake) in Hbod, Hebod. 
        eapply (erase_global_erases_deps (Σ := (Σpop, cst_universes c))); simpl; auto.
        { constructor; simpl; auto. depelim wf. rewrite Hpop' Hpop'' in o0.
          cbn in o0, o. rewrite prf' in o0. rewrite  <- Hpop in o0. rewrite Hpop' in o. clear -o o0. 
          now depelim o0.
          depelim wf. rewrite Hpop' in o0.
          cbn in o0, o. rewrite prf' in o0.  rewrite <- Hpop in o0. clear -o0.  now depelim o0. }
        all: eauto. 
        apply IHdecls; eauto. 
        { intros. pose proof (abstract_env_wf _ wfpop) as [wf'].
          destruct Σpop. cbn in *. clear prf'.  subst. 
          unshelve epose proof (abstract_pop_decls_correct X decls _ _ _ wfΣ H2) as [Hpop Hpop'].
          { intros. now eexists. }
          destruct Σ.  cbn in *. subst.
          eapply term_global_deps_spec in Hebod; eauto. }
        {  eapply KernameSet.subset_spec.
          intros x hin'. eapply KernameSet.union_spec. right; auto.
          now rewrite -Heqdeps. } }
        { eexists m, _; intuition eauto.
          simpl. rewrite /declared_minductive /lookup_env prf; eauto. 
          simpl. rewrite eq_kername_refl. reflexivity.
          specialize (sub _ hin).
          eapply KernameSet.mem_spec in sub.
          simpl. rewrite sub.
          red. cbn. rewrite eq_kername_refl.
          reflexivity.
          assert (declared_minductive Σ kn m).
          { red. unfold lookup_env. rewrite prf; eauto. cbn. now rewrite eqb_refl. }
          eapply on_declared_minductive in H0; tea.
          now eapply erases_mutual. }

    * intros ikn Hi. 
      destruct d as [|].
      ++ simpl. destruct (KernameSet.mem kn deps) eqn:eqkn.
        set (Xpop := abstract_pop_decls X).
        set (Xmake :=  abstract_make_wf_env_ext Xpop (cst_universes c) _).
        epose proof (abstract_env_exists Xpop) as [[Σp wfpop]].
        pose proof (abstract_env_wf _ wfpop) as [wfΣp].
        unshelve epose proof (abstract_pop_decls_correct X decls _ _ _ wfΣ wfpop) as [Hpop [Hpop' Hpop'']].
        { intros. now eexists. }
        pose proof (prf _ wfΣ). destruct Σ. cbn in *. subst.
        eapply global_erases_with_deps_cons; eauto.
        eapply (IHdecls Xpop _ _ (KernameSet.singleton i)); auto.
        3:{ eapply KernameSet.singleton_spec => //. }
        intros.
        eapply KernameSet.singleton_spec in H0.
        pose proof (abstract_env_irr _ H1 wfpop). subst. 
        sq; exists decl; eauto.
        eapply KernameSet.subset_spec. intros ? ?.
        eapply KernameSet.union_spec. left.
        eapply KernameSet.singleton_spec in H0; subst.
        now eapply sub.
      
        cbn. set (Xpop := abstract_pop_decls X).
        epose proof (abstract_env_exists Xpop) as [[Σp wfpop]].
        pose proof (abstract_env_wf _ wfpop) as [wfΣp].   
        unshelve epose proof (abstract_pop_decls_correct X decls _ Σ Σp wfΣ wfpop) as [Hpop [Hpop' Hpop'']].
        { intros. now eexists. }
        pose proof (prf _ wfΣ). destruct Σ. cbn in *. subst.
        eapply global_erases_with_deps_weaken. eauto.
        eapply IHdecls => //.
        3:now eapply KernameSet.singleton_spec.
        intros d ind%KernameSet.singleton_spec.
        intros. pose proof (abstract_env_irr _ H0 wfpop). subst. 
        sq; eexists; eauto.
        eapply KernameSet.subset_spec.
        intros ? hin'. eapply sub. eapply KernameSet.singleton_spec in hin'. now subst.

      ++ simpl. set (Xpop := abstract_pop_decls X).
      epose proof (abstract_env_exists Xpop) as [[Σp wfpop]].
      pose proof (abstract_env_wf _ wfpop) as [wfΣp].      
      unshelve epose proof (abstract_pop_decls_correct X decls _ Σ Σp wfΣ wfpop) as [Hpop [Hpop' Hpop'']].
      { intros. now eexists. }
      pose proof (prf _ wfΣ). destruct Σ. cbn in *. subst.
      destruct (KernameSet.mem kn deps) eqn:eqkn.
        { eapply (global_erases_with_deps_cons _ kn (InductiveDecl _) _ Σp); eauto.
          eapply (IHdecls Xpop _ _ (KernameSet.singleton i)); auto.
          3:{ eapply KernameSet.singleton_spec => //. }
          intros.
          eapply KernameSet.singleton_spec in H0. subst.
          pose proof (abstract_env_irr _ H1 wfpop). subst. 
          sq; eexists; eauto.
          eapply KernameSet.subset_spec. intros ? ?.
          eapply KernameSet.singleton_spec in H0; subst.
          now eapply sub. }
    
        { eapply (global_erases_with_deps_weaken _ kn (InductiveDecl _) Σp). eauto.
          eapply (IHdecls Xpop _ _  (KernameSet.singleton i)) => //.
          3:now eapply KernameSet.singleton_spec.
          intros d ind%KernameSet.singleton_spec.
          intros. pose proof (abstract_env_irr _ H0 wfpop). subst. 
          sq; eexists; eauto.
          eapply KernameSet.subset_spec.
          intros ? hin'. eapply sub. eapply KernameSet.singleton_spec in hin'. now subst. }          
Qed.

Lemma erase_correct (wfl := Ee.default_wcbv_flags) X_type (X : X_type.π1) 
  univs wfext t v Σ' t' deps decls prf :
  let Xext :=  abstract_make_wf_env_ext X univs wfext in
  forall wt : forall Σ, Σ ∼_ext Xext -> welltyped Σ [] t,
  erase X_type.π2.π1 Xext [] t wt = t' ->
  KernameSet.subset (term_global_deps t') deps ->
  erase_global_decls deps X decls prf = Σ' ->
  (forall Σ : global_env, abstract_env_rel X Σ -> Σ |-p t ▷ v) ->
  forall Σ : global_env_ext, abstract_env_ext_rel Xext Σ -> 
  exists v', Σ ;;; [] |- v ⇝ℇ v' /\ ∥ Σ' ⊢ t' ▷ v' ∥.
Proof.
  intros Xext wt.
  intros HΣ' Hsub Ht' ev Σext wfΣex.
  pose proof (erases_erase (X := Xext) wt).
  rewrite HΣ' in H.
  destruct (wt _ wfΣex) as [T wt'].
  pose proof (abstract_env_ext_wf _ wfΣex) as [wfΣ].
  specialize (H _ wfΣex).
  unshelve epose proof (erase_global_erases_deps (Σ' := Σ') wfΣ wt' H _); cycle 2.
  rewrite <- Ht'.
  eapply erase_global_includes; eauto. 
  intros. eapply term_global_deps_spec in H; eauto.
  now rewrite (abstract_make_wf_env_ext_correct X univs wfext Σ _ H1 wfΣex) in H.
  
  epose proof (abstract_env_exists X) as [[Σ wfΣX]].
  now rewrite (abstract_make_wf_env_ext_correct X univs wfext Σ _ wfΣX wfΣex).
  epose proof (abstract_env_exists X) as [[Σ wfΣX]].
  eapply erases_correct; tea.
  rewrite (abstract_make_wf_env_ext_correct X univs wfext _ _ wfΣX wfΣex); eauto.
Qed.

Lemma global_env_ind (P : global_env -> Type) 
  (Pnil : forall univs retro, P {| universes := univs; declarations := []; retroknowledge := retro |})
  (Pcons : forall (Σ : global_env) d, P Σ -> P (add_global_decl Σ d))
  (Σ : global_env) : P Σ.
Proof.
  destruct Σ as [univs Σ].
  induction Σ; cbn. apply Pnil.
  now apply (Pcons {| universes := univs; declarations := Σ |} a).
Qed.

Lemma on_global_env_ind (P : forall Σ : global_env, wf Σ -> Type)
  (Pnil : forall univs retro (onu : on_global_univs univs), P {| universes := univs; declarations := []; retroknowledge := retro |}
    (onu, globenv_nil _ _ _ _))
  (Pcons : forall (Σ : global_env) kn d (wf : wf Σ) 
    (Hfresh : fresh_global kn Σ.(declarations))
    (udecl := PCUICLookup.universes_decl_of_decl d)
    (onud : on_udecl Σ.(universes) udecl)
    (pd : on_global_decl cumulSpec0 (lift_typing typing) 
    ({| universes := Σ.(universes); declarations := Σ.(declarations); retroknowledge := Σ.(retroknowledge) |}, udecl) kn d),
    P Σ wf -> P (add_global_decl Σ (kn, d)) 
    (fst wf, globenv_decl _ _ Σ.(universes) Σ.(retroknowledge) Σ.(declarations) kn d (snd wf) Hfresh onud pd))
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

Fixpoint map_erase X_type (X : X_type.π1) Γ 
  (ts : list term) 
  (H2 : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> 
    Forall (welltyped Σ Γ) ts) {struct ts}: list E.term.
destruct ts as [ | t ts].
- exact [].
- eapply cons. refine (erase X_type X Γ t _). 
  2: eapply (map_erase X_type X Γ ts).
  all: intros; specialize_Σ H; now inversion H2; subst.
Defined.

Lemma map_erase_irrel X_type X Γ t H1 H2 : 
        map_erase X_type X Γ t H1 = map_erase X_type X Γ t H2.
Proof.
  epose proof (abstract_env_ext_exists X) as [[Σ wfΣX]].
  induction t.
  - reflexivity.
  - cbn. f_equal.
    + eapply erase_irrel.
    + eapply IHt.
Qed.

Arguments map_erase _ _ _ _, _ _ _ {_}.

Lemma erase_mkApps {X_type X} Γ t args H2 Ht Hargs :
  (forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> wf_local Σ Γ) ->
  (forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> ~ ∥ isErasable Σ Γ (mkApps t args) ∥) ->
  erase X_type X Γ (mkApps t args) H2 = 
  E.mkApps (erase X_type X Γ t Ht) (map_erase X_type X Γ args Hargs).
Proof.
  epose proof (abstract_env_ext_exists X) as [[Σ wfΣX]].
  pose proof (abstract_env_ext_wf X wfΣX) as [wf]. 
  intros Hwflocal Herasable. induction args in t, H2, Ht, Hargs, Herasable |- *.
  - cbn. eapply erase_irrel.
  - cbn [mkApps]. 
    rewrite IHargs; clear IHargs.
    all: intros; specialize_Σ H; try pose proof (abstract_env_ext_wf _ H) as [wfH].
    1: inversion Hargs; eauto.
    2: eauto.
    2:{ destruct H2. cbn in X0. eapply inversion_mkApps in X0 as (? & ? & ?).
        econstructor. eauto. }
    etransitivity. simp erase. reflexivity. unfold erase_clause_1.
    unfold inspect. unfold erase_clause_1_clause_2.
    Unshelve.
    elim: is_erasableP.
    + intros. exfalso. 
      eapply Herasable; eauto. specialize_Σ wfΣX. destruct p.
      cbn. destruct H2. eapply Is_type_app; eauto.
    + cbn [map_erase]. 
      epose proof (fst (erase_irrel _ _)). cbn.
      intros he. f_equal => //. f_equal.
      eapply erase_irrel. eapply erase_irrel.
      eapply map_erase_irrel. 
      Unshelve. 2: exact X. 
Qed.

Lemma map_erase_length X_type X Γ t H1 : length (map_erase X_type X Γ t H1) = length t.
Proof.
  induction t; cbn; f_equal; eauto.
Qed.

Local Hint Constructors expanded : expanded.

Local Arguments erase_global_decls _ _ _ : clear implicits.

Lemma lookup_env_erase X_type X deps decls prf kn d :
  KernameSet.In kn deps -> 
  forall Σ : global_env, abstract_env_rel X Σ -> lookup_env Σ kn = Some (InductiveDecl d) ->
  EGlobalEnv.lookup_env (erase_global_decls X_type deps X decls prf) kn = Some (EAst.InductiveDecl (erase_mutual_inductive_body d)).
Proof.
  intros hin Σ wfΣ. pose proof (prf _ wfΣ). unfold lookup_env. rewrite H. clear H.
  rewrite /lookup_env. 
  induction decls in X, Σ , wfΣ ,prf, deps, hin |- *.
  - move=> /= //.
  - destruct a as [kn' d'].
    cbn -[erase_global_decls].
    case: (eqb_spec kn kn'); intros e'; subst.
    intros [= ->].
    unfold erase_global_decls.
    eapply KernameSet.mem_spec in hin. rewrite hin /=.
    now rewrite eq_kername_refl.
    intros hl. destruct d'. simpl.
    set (Xpop := abstract_pop_decls X).
    set (Xmake :=  abstract_make_wf_env_ext Xpop (cst_universes c) _).
    epose proof (abstract_env_exists Xpop) as [[Σp wfpop]].
    destruct KernameSet.mem. cbn.
    rewrite (negbTE (proj2 (neqb _ _) e')).
    eapply IHdecls => //; eauto. eapply KernameSet.union_spec. left => //.
    eapply IHdecls => //; eauto.
    simpl.
    set (Xpop := abstract_pop_decls X).
    epose proof (abstract_env_exists Xpop) as [[Σp wfpop]].
    destruct KernameSet.mem. cbn.
    rewrite (negbTE (proj2 (neqb _ _) e')).
    eapply IHdecls => //; eauto.
    eapply IHdecls => //; eauto. 
Qed.

Lemma erase_global_declared_constructor X_type X ind c mind idecl cdecl deps decls prf:
   forall Σ : global_env, abstract_env_rel X Σ -> declared_constructor Σ (ind, c) mind idecl cdecl ->
   KernameSet.In ind.(inductive_mind) deps -> 
   EGlobalEnv.declared_constructor (erase_global_decls X_type deps X decls prf) (ind, c) 
    (erase_mutual_inductive_body mind) (erase_one_inductive_body idecl) 
    (EAst.mkConstructor cdecl.(cstr_name) cdecl.(cstr_arity)).
Proof.
  intros Σ wfΣ [[]] Hin.
  cbn in *. split. split. 
  - red in H |- *. now eapply lookup_env_erase.
  - cbn. now eapply map_nth_error.
  - cbn. erewrite map_nth_error; eauto.
Qed.

Import EGlobalEnv.
Lemma erase_global_decls_fresh X_type kn deps X decls heq : 
  let Σ' := erase_global_decls X_type deps X decls heq in
  PCUICAst.fresh_global kn decls ->
  fresh_global kn Σ'.
Proof.
  cbn.
  revert deps X heq.
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

From MetaCoq.Erasure Require Import EEtaExpandedFix.

Lemma erase_brs_eq X_type X Γ p ts wt : 
  erase_brs X_type X Γ p ts wt = 
  map_All (fun br wt => (erase_context (bcontext br), erase X_type X _ (bbody br) wt)) ts wt.
Proof.
  funelim (map_All _ ts wt); cbn; auto.
  f_equal => //. f_equal => //. apply erase_irrel.
  rewrite -H. eapply erase_irrel.
Qed.

Lemma erase_fix_eq X_type X Γ ts wt : 
  erase_fix X_type X Γ ts wt = map_All (fun d wt => 
    let dbody' := erase X_type X _ (dbody d) (fun Σ abs => proj2 (wt Σ abs)) in
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
  rewrite (fst (erase_irrel _ _) _ _ _ (fun (Σ : global_env_ext) (abs : abstract_env_ext_rel X Σ) =>
    (map_All_obligation_1 x xs h Σ abs).p2)).
  destruct erase => //.
  rewrite -H. eapply erase_irrel.
Qed.

Lemma erase_cofix_eq X_type X Γ ts wt : 
  erase_cofix X_type X Γ ts wt = map_All (fun d wt => 
    let dbody' := erase X_type X _ (dbody d) wt in
    {| E.dname := d.(dname).(binder_name); E.rarg := d.(rarg); E.dbody := dbody' |}) ts wt.
Proof.
  funelim (map_All _ ts wt); cbn; auto.
  f_equal => //. f_equal => //.
  apply erase_irrel.
  rewrite -H. eapply erase_irrel.
Qed.

Lemma isConstruct_erase X_type X Γ t wt : 
  ~ (PCUICEtaExpand.isConstruct t || PCUICEtaExpand.isFix t || PCUICEtaExpand.isRel t) ->
  ~ (isConstruct (erase X_type X Γ t wt) || isFix (erase X_type X Γ t wt) || isRel (erase X_type X Γ t wt)).
Proof.
  apply (erase_elim X_type X
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

Lemma erases_deps_erase (cf := config.extraction_checker_flags) 
  {X_type X} univs 
  (wfΣ : forall Σ, (abstract_env_rel X Σ) -> ∥ wf_ext (Σ, univs) ∥) decls prf
  (X' :=  abstract_make_wf_env_ext X univs wfΣ) Γ t 
  (wt : forall Σ : global_env_ext, abstract_env_ext_rel X' Σ -> welltyped Σ Γ t) :
  let et := erase X_type.π2.π1 X' Γ t wt in
  let deps := EAstUtils.term_global_deps et in
  forall Σ, (abstract_env_rel X Σ) -> 
  erases_deps Σ (erase_global_decls X_type deps X decls prf) et.
Proof.
  intros et deps Σ wf. 
  pose proof (abstract_env_ext_exists X') as [[Σ' wfΣ']].
  pose proof (wt _ wfΣ'). destruct H. pose proof (wfΣ _ wf) as [w].
  rewrite (abstract_make_wf_env_ext_correct X univs wfΣ _ _ wf wfΣ') in X0.
  eapply (erase_global_erases_deps w); tea.
  eapply (erases_erase (X := X') (Γ := Γ)).
  now rewrite <- (abstract_make_wf_env_ext_correct X univs wfΣ _ _ wf wfΣ').
  eapply erase_global_includes.
  intros. rewrite (abstract_env_irr _ H0 wf).
  eapply term_global_deps_spec in H; eauto.
  assumption.
  eapply (erases_erase (X := X') (Γ := Γ)). 
  now rewrite <- (abstract_make_wf_env_ext_correct X univs wfΣ _ _ wf wfΣ').
  eapply KernameSet.subset_spec. reflexivity. 
  now cbn.  
Qed.

Lemma erases_deps_erase_weaken (cf := config.extraction_checker_flags) 
  {X_type X} univs 
  (wfΣ : forall Σ, (abstract_env_rel X Σ) -> ∥ wf_ext (Σ, univs) ∥) decls prf
  (X' :=  abstract_make_wf_env_ext X univs wfΣ) Γ t 
  (wt : forall Σ : global_env_ext, abstract_env_ext_rel X' Σ -> welltyped Σ Γ t) 
  deps :
  let et := erase X_type.π2.π1 X'  Γ t wt in
  let tdeps := EAstUtils.term_global_deps et in
  forall Σ, (abstract_env_rel X Σ) -> 
  erases_deps Σ (erase_global_decls X_type (KernameSet.union deps tdeps) X decls prf) et.
Proof.
  intros et tdeps Σ wf.
  pose proof (abstract_env_ext_exists X') as [[Σ' wfΣ']].
  pose proof (wt _ wfΣ'). destruct H. pose proof (wfΣ _ wf) as [w].
  rewrite (abstract_make_wf_env_ext_correct X univs wfΣ _ _ wf wfΣ') in X0.
  eapply (erase_global_erases_deps w); tea.
  eapply (erases_erase (X := X') (Γ := Γ)).
  now rewrite <- (abstract_make_wf_env_ext_correct X univs wfΣ _ _ wf wfΣ').
  eapply erase_global_includes.
  intros. rewrite (abstract_env_irr _ H0 wf).
  eapply term_global_deps_spec in H; eauto.
  assumption.
  eapply (erases_erase (X := X') (Γ := Γ)).
  now rewrite <- (abstract_make_wf_env_ext_correct X univs wfΣ _ _ wf wfΣ').
  eapply KernameSet.subset_spec. intros x hin.
  eapply KernameSet.union_spec. now right.
  now cbn.
Qed.

Lemma eta_expand_erase {X_type X} Σ' {Γ t} 
  (wt : forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> welltyped Σ Γ t) Γ' :
  forall Σ : global_env_ext, abstract_env_ext_rel X Σ -> 
  PCUICEtaExpand.expanded Σ Γ' t ->
  erases_global Σ Σ' ->
  expanded Σ' Γ' (erase X_type X Γ t wt).
Proof.
  intros Σ wfΣ exp deps.
  pose proof (abstract_env_ext_wf _ wfΣ) as [wf]. 
  eapply expanded_erases. apply wf.
  eapply erases_erase; eauto. assumption.
  pose proof (wt _ wfΣ). destruct H as [T ht].
  eapply erases_global_erases_deps; tea.
  eapply erases_erase; eauto.
Qed.

Lemma erase_global_closed X_type X deps decls prf :
  let X' := erase_global_decls X_type deps X decls prf in
  EGlobalEnv.closed_env X'.
Proof.
  revert X prf deps.
  induction decls; [cbn; auto|].
  intros X prf deps. 
  destruct a as [kn d].
  destruct d as []; simpl; destruct KernameSet.mem;
  set (Xpop := abstract_pop_decls X);
  try set (Xmake :=  abstract_make_wf_env_ext Xpop (cst_universes c) _).
  + cbn [EGlobalEnv.closed_env forallb]. cbn.
    rewrite [forallb _ _](IHdecls) // andb_true_r.
    rewrite /test_snd /EGlobalEnv.closed_decl /=.
    destruct c as [ty [] univs]; cbn.
    set (obl := erase_constant_body_obligation_1 _ _ _ _ _).
    unfold erase_constant_body. cbn. clearbody obl. cbn in obl.
    2:auto.
    unshelve epose proof (erases_erase (X := Xmake) (obl eq_refl)); eauto.
    pose proof (abstract_env_ext_exists Xmake) as [[Σmake wfmake]].
    pose proof (abstract_env_ext_wf _ wfmake) as [[?]].
    eapply erases_closed in H => //; eauto.
    cbn. destruct (obl eq_refl _ wfmake). clear H. 
    now eapply PCUICClosedTyp.subject_closed in X0.
  + eapply IHdecls => //.
  + cbn [EGlobalEnv.closed_env forallb].
    rewrite {1}/test_snd {1}/EGlobalEnv.closed_decl /=.
    eapply IHdecls => //.
  + eapply IHdecls => //.
  Unshelve. eauto.  
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
      (idx <? #|mfix|) && List.forallb (fun d => isLambda d.(dbody) && wf_fixpoints d.(dbody)) mfix
    | tCoFix mfix idx =>
      (idx <? #|mfix|) && List.forallb (wf_fixpoints ∘ dbody) mfix
    | tConst kn => true
    | tConstruct ind c _ => true
    | tVar _ => true
    | tBox => true
    | tPrim _ => true
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
  ErasureProperties.wellformed Σ t -> wf_fixpoints t'.
Proof.
  induction 1 using erases_forall_list_ind; cbn; auto; try solve [rtoProp; repeat solve_all].
  - move/andP => []. rewrite (All2_length X) => -> /=. unfold test_def in *.
    eapply Forall2_All2 in H.
    eapply All2_All2_mix in X; tea. solve_all.
    destruct b0; eapply erases_isLambda in H1; tea.
  - move/andP => []. rewrite (All2_length X) => -> /=.
    unfold test_def in *. solve_all.
Qed.

Lemma erase_wf_fixpoints (efl := all_env_flags) {X_type X} univs wfΣ {Γ t} wt
  (X' :=  abstract_make_wf_env_ext X univs wfΣ) :
  let t' := erase X_type.π2.π1 X' Γ t wt in
  wf_fixpoints t'.
Proof.
  cbn. pose proof (abstract_env_ext_exists X') as [[Σ' wf']].
  pose proof (abstract_env_exists X) as [[Σ wf]].
  eapply erases_wf_fixpoints.
  eapply erases_erase; eauto.
  specialize (wt _ wf'). destruct (wfΣ _ wf).
  unshelve eapply welltyped_wellformed in wt; eauto. 
  now rewrite (abstract_make_wf_env_ext_correct X univs wfΣ _ _ wf wf'). 
Qed.

Lemma erase_wellformed (efl := all_env_flags) {X_type X} decls prf univs wfΣ {Γ t} wt
(X' :=  abstract_make_wf_env_ext X univs wfΣ) :
let t' := erase X_type.π2.π1 X' Γ t wt in
wellformed (erase_global_decls X_type (term_global_deps t') X decls prf) #|Γ| t'.
Proof.
  set (t' := erase _ _ _ _ _). cbn.
  epose proof (@erases_deps_erase X_type X univs wfΣ decls prf Γ t wt).
  pose proof (abstract_env_exists X) as [[Σ wf]]. specialize_Σ wf. 
  pose proof (abstract_env_ext_exists X') as [[Σ' wf']].
  pose proof (abstract_env_ext_wf _ wf') as [[?]].
  epose proof (erases_deps_wellformed _ H #|Γ|).
  apply H0.
  eapply (erases_closed _ Γ).
  destruct (wt _ wf').
  cbn in X. destruct (wfΣ _ wf).
  eapply PCUICClosedTyp.subject_closed in X0. eassumption. 
  eapply erases_erase; eauto. 
  eapply erase_wf_fixpoints. Unshelve. eauto.  
Qed.

Lemma erase_wellformed_weaken (efl := all_env_flags) {X_type X} decls prf univs wfΣ {Γ t} wt
(X' :=  abstract_make_wf_env_ext X univs wfΣ) deps:
let t' := erase X_type.π2.π1 X' Γ t wt in
  wellformed (erase_global_decls X_type (KernameSet.union deps (term_global_deps t')) X decls prf) #|Γ| t'.
Proof.
  set (t' := erase _ _ _ _ _). cbn.
  epose proof (@erases_deps_erase_weaken _ X univs wfΣ decls prf Γ t wt deps).
  pose proof (abstract_env_exists X) as [[Σ wf]]. specialize_Σ wf. 
  pose proof (abstract_env_ext_exists X') as [[Σ' wf']].
  pose proof (abstract_env_ext_wf _ wf') as [[?]].
  epose proof (erases_deps_wellformed _ H #|Γ|).
  apply H0.
  eapply (erases_closed _ Γ).
  - destruct (wt _ wf').
    destruct (wfΣ _ wf).
    eapply PCUICClosedTyp.subject_closed in X0. eassumption.
  - eapply erases_erase; eauto. 
  - eapply erase_wf_fixpoints.
  Unshelve. eauto.  
Qed.

Lemma erase_constant_body_correct'' {X_type X} {cb} {decls prf} {univs wfΣ}
(X' :=  abstract_make_wf_env_ext X univs wfΣ)
{onc : forall Σ' : global_env_ext, abstract_env_ext_rel X' Σ' -> ∥ on_constant_decl (lift_typing typing) Σ' cb ∥} {body} deps :  
  EAst.cst_body (fst (erase_constant_body X_type.π2.π1 X' cb onc)) = Some body ->
  forall Σ' : global_env_ext, abstract_env_ext_rel X' Σ' -> 
  ∥ ∑ t T, (Σ' ;;; [] |- t : T) * (Σ' ;;; [] |- t ⇝ℇ body) *
      (term_global_deps body = snd (erase_constant_body X_type.π2.π1 X'  cb onc)) *
      wellformed (efl:=all_env_flags) (erase_global_decls X_type (KernameSet.union deps (term_global_deps body)) X decls prf) 0 body ∥.
Proof.
  intros ? Σ' wfΣ'. pose proof (abstract_env_exists X) as [[Σ wf]]. 
  destruct cb as [name [bod|] udecl]; simpl.
  simpl in H. noconf H.
  set (obl :=(erase_constant_body_obligation_1 (X_type.π2).π1 X'
  {|
  cst_type := name;
  cst_body := Some bod;
  cst_universes := udecl |} onc bod eq_refl)). clearbody obl.
  destruct (obl _ wfΣ'). sq.
  have er : (Σ, univs);;; [] |- bod ⇝ℇ erase X_type.π2.π1 X' [] bod obl.
  { eapply (erases_erase (X:=X')). 
    now rewrite <- (abstract_make_wf_env_ext_correct X univs wfΣ _ _ wf wfΣ'). 
   }
  exists bod, A; intuition auto.
  now rewrite (abstract_make_wf_env_ext_correct X univs wfΣ _ _ wf wfΣ'). 
  eapply erase_wellformed_weaken.
  now simpl in H.
Qed.

Lemma erase_global_cst_decl_wf_glob X_type X deps decls heq :
  forall cb wfΣ hcb,
  let X' :=  abstract_make_wf_env_ext X (cst_universes cb) wfΣ in
  let ecb := erase_constant_body X_type.π2.π1 X' cb hcb in
  let Σ' := erase_global_decls X_type (KernameSet.union deps ecb.2) X decls heq in
  (@wf_global_decl all_env_flags Σ' (EAst.ConstantDecl ecb.1) : Prop).
Proof.
  intros cb wfΣ hcb X' ecb Σ'. 
  unfold wf_global_decl. cbn.
  pose proof (abstract_env_exists X) as [[Σ wf]]. specialize_Σ wf. 
  pose proof (abstract_env_ext_exists X') as [[Σmake wfmake]].
  destruct (wfΣ _ wf), (hcb _ wfmake). red in X1.
  destruct EAst.cst_body eqn:hb => /= //.
  eapply (erase_constant_body_correct'') in hb; eauto. 
  destruct hb as [[t0 [T [[] ?]]]]. rewrite e in i. exact i. 
Qed.

Lemma erase_global_ind_decl_wf_glob {X_type X} {deps decls kn m} heq :
  (forall Σ : global_env, abstract_env_rel X Σ -> on_inductive cumulSpec0 (lift_typing typing) (Σ, ind_universes m) kn m) ->
  let m' := erase_mutual_inductive_body m in
  let Σ' := erase_global_decls X_type deps X decls heq in
  @wf_global_decl all_env_flags Σ' (EAst.InductiveDecl m').
Proof.
  set (m' := erase_mutual_inductive_body m).
  set (Σ' := erase_global_decls _ _ _ _ _). simpl.
  intros oni.
  pose proof (abstract_env_exists X) as [[Σ wf]]. specialize_Σ wf.
  pose proof (abstract_env_wf _ wf) as [wfΣ].
  assert (erases_mutual_inductive_body m (erase_mutual_inductive_body m)).
  { eapply (erases_mutual (mdecl:=kn)); tea. }
  eapply (erases_mutual_inductive_body_wf (univs := Σ.(universes)) (retro := Σ.(retroknowledge)) (Σ := decls) (kn := kn) (Σ' := Σ')) in H; tea.
  rewrite -(heq _ wf). now destruct Σ.
Qed.

Lemma erase_global_decls_wf_glob X_type X deps decls heq :
  let Σ' := erase_global_decls X_type deps X decls heq in
  @wf_glob all_env_flags Σ'.
Proof.
  cbn.
  pose proof (abstract_env_exists X) as [[Σ wf]].
  pose proof (abstract_env_wf _ wf) as [wfΣ].
  revert deps X Σ wf wfΣ heq.
  induction decls; [cbn; auto|].
  { intros. constructor. }
  intros. destruct a as [kn []]; simpl; destruct KernameSet.mem; set (Xpop := abstract_pop_decls X);
  try set (Xmake :=  abstract_make_wf_env_ext Xpop (cst_universes c) _);
  epose proof (abstract_env_exists Xpop) as [[Σpop wfpop]]; 
  pose proof (abstract_env_wf _ wfpop) as [wfΣpop].
  + constructor. eapply IHdecls => //; eauto. eapply erase_global_cst_decl_wf_glob; auto.
    eapply erase_global_decls_fresh; auto.
    destruct wfΣ. destruct wfΣpop.
    rewrite (heq _ wf) in o0. now depelim o0.
  + cbn. eapply IHdecls; eauto. 
  + constructor. eapply IHdecls; eauto. 
    destruct wfΣ as [[onu ond]]. 
    rewrite (heq _ wf) in o. depelim o.
    eapply (erase_global_ind_decl_wf_glob (kn:=kn)); tea.
    intros. rewrite (abstract_env_irr _ H wfpop). 
    unshelve epose proof (abstract_pop_decls_correct X decls _ _ _ wf wfpop) as [? ?].
    {intros; now eexists. }
    destruct Σpop, Σ; cbn in *. now subst.
    eapply erase_global_decls_fresh.
    destruct wfΣ as [[onu ond]].
    rewrite (heq _ wf) in o. now depelim o.
  + eapply IHdecls; eauto. 
Qed.

Lemma lookup_erase_global (cf := config.extraction_checker_flags) {X_type X} {deps deps' decls prf} :
  KernameSet.Subset deps deps' ->
  EExtends.global_subset (erase_global_decls X_type deps X decls prf) (erase_global_decls X_type deps' X decls prf).
Proof.
  revert deps deps' X prf.
  induction decls. cbn => //.
  intros ? ? ? ? sub. 
  epose proof (abstract_env_exists X) as [[Σ wf]]. 
  destruct a as [kn' []]; cbn;
  ( set (decl := E.ConstantDecl _) || 
    set (decl := E.InductiveDecl _)); hidebody decl;
  set (eg := erase_global_decls _ _ _ _ _); hidebody eg;
  set (eg' := erase_global_decls _ _ _ _ _); hidebody eg';
  try (set (eg'' := erase_global_decls _ _ _ _ _); hidebody eg'');
  try (set (eg''' := erase_global_decls _ _ _ _ _); hidebody eg''').
  { destruct (KernameSet.mem) eqn:knm => /=.
    + eapply KernameSet.mem_spec, sub, KernameSet.mem_spec in knm. rewrite knm.
      apply EExtends.global_subset_cons. eapply IHdecls; eauto. 
      intros x hin. eapply KernameSet.union_spec in hin.
      eapply KernameSet.union_spec. destruct hin. left. now eapply sub.
      right => //.
    + destruct (KernameSet.mem kn' deps') eqn:eq'.
      eapply EExtends.global_subset_cons_right; eauto. 
      eapply erase_global_decls_wf_glob.
      unfold decl. unfold hidebody.
      constructor. eapply erase_global_decls_wf_glob.
      eapply erase_global_cst_decl_wf_glob. 
      eapply erase_global_decls_fresh => //.
      pose proof (abstract_env_wf _ wf) as [wfΣ].
      depelim wfΣ. rewrite (prf _ wf) in o0. clear - o0. now depelim o0.
      unfold eg', eg'', hidebody. 
      erewrite erase_global_decls_irr.
      eapply IHdecls.
      intros x hin.
      eapply KernameSet.union_spec. left. now eapply sub.
      eapply IHdecls => //. }
  { destruct (KernameSet.mem) eqn:knm => /=.
    + eapply KernameSet.mem_spec, sub, KernameSet.mem_spec in knm. rewrite knm.
      apply EExtends.global_subset_cons. eapply IHdecls => //.
    + destruct (KernameSet.mem kn' deps') eqn:eq'.
      eapply EExtends.global_subset_cons_right. eapply erase_global_decls_wf_glob.
      constructor. eapply erase_global_decls_wf_glob.
      pose proof (abstract_env_wf _ wf) as [wfΣ].
      pose proof (prf _ wf) as prf'.
      eapply (erase_global_ind_decl_wf_glob (kn:=kn')).
      intros. 
      unshelve epose proof (abstract_pop_decls_correct X decls _ _ _ wf H) as [? [? ?]].
      { now eexists. }
      destruct Σ, Σ0. cbn in *. rewrite prf' in wfΣ.
      depelim wfΣ. cbn in *. rewrite <- H1, H0, <- H2. 
      now depelim o0.
      eapply erase_global_decls_fresh => //.
      pose proof (abstract_env_wf _ wf) as [wfΣ].
      pose proof (prf _ wf) as prf'.
      destruct Σ. cbn in *. rewrite prf' in wfΣ.
      clear -wfΣ. destruct wfΣ. cbn in *. now depelim o0.
      unfold eg'', hidebody. erewrite erase_global_decls_irr.
      eapply IHdecls. intros x hin. now eapply sub.
      eapply IHdecls => //. }
Qed.

Lemma expanded_weakening_global X_type X deps deps' decls prf Γ t : 
  KernameSet.Subset deps deps' ->
  expanded (erase_global_decls X_type deps X decls prf) Γ t ->
  expanded (erase_global_decls X_type deps' X decls prf) Γ t.
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

Lemma expanded_erase (cf := config.extraction_checker_flags) 
  {X_type X decls prf} univs wfΣ t wtp :
  forall Σ : global_env, abstract_env_rel X Σ -> PCUICEtaExpand.expanded Σ [] t ->
  let X' :=  abstract_make_wf_env_ext X univs wfΣ in
  let et := (erase X_type.π2.π1 X' [] t wtp) in
  let deps := EAstUtils.term_global_deps et in
  expanded (erase_global_decls X_type deps X decls prf) [] et.
Proof.
  intros Σ wf hexp X'.
  pose proof (abstract_env_wf _ wf) as [wf'].
  pose proof (abstract_env_ext_exists X') as [[? wfmake]].
  eapply (expanded_erases (Σ := (Σ, univs))); tea.
  eapply (erases_erase (X := X')); eauto.
  now erewrite <- (abstract_make_wf_env_ext_correct X univs wfΣ).
  cbn.
  eapply (erases_deps_erase (X := X) univs wfΣ); eauto. 
Qed.

Lemma expanded_erase_global (cf := config.extraction_checker_flags) 
  deps {X_type X decls prf} :
  forall Σ : global_env, abstract_env_rel X Σ -> 
    PCUICEtaExpand.expanded_global_env Σ ->
    expanded_global_env (erase_global_decls X_type deps X decls prf).
Proof.
  intros Σ wf etaΣ. pose proof (prf _ wf).
  destruct Σ as [univ decls']. 
  red. revert wf. red in etaΣ. cbn in *. subst. 
  revert deps X prf.
  induction etaΣ; intros deps. intros. constructor. intros.
  pose proof (abstract_env_exists (abstract_pop_decls X)) as [[Σpop wfpop]]. 
  unshelve epose proof (abstract_pop_decls_correct X Σ _ _ _ wf wfpop) as [? [? ?]].
  { now eexists. }
  destruct Σpop. cbn in H0, H1, H2. subst. 
  destruct decl as [kn []];
  destruct (KernameSet.mem kn deps) eqn:eqkn; simpl; rewrite eqkn.
  constructor; [eapply IHetaΣ; auto|].
  red. cbn. red. cbn in *.
  set (deps' := KernameSet.union _ _). hidebody deps'.
  set (wfext :=  abstract_make_wf_env_ext _ _ _). hidebody wfext.
  destruct H.
  destruct c as [cst_na [cst_body|] cst_type cst_rel].
  cbn in *.
  eapply expanded_weakening_global. 
  2:{ eapply expanded_erase; tea. }
  set (et := erase _ _ _ _) in *.
  unfold deps'. unfold hidebody. intros x hin.    
  eapply KernameSet.union_spec. right => //.
  now cbn.
  eapply IHetaΣ; eauto. 
  constructor. eapply IHetaΣ; eauto. 
  red. cbn => //.
  eapply IHetaΣ; eauto. 
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

Lemma erase_eval_to_box (wfl := Ee.default_wcbv_flags) 
  {X_type X} {univs wfext t v Σ' t' deps decls prf} :
  let Xext :=  abstract_make_wf_env_ext X univs wfext in
  forall wt : forall Σ : global_env_ext, abstract_env_ext_rel Xext Σ -> welltyped Σ [] t,
  erase X_type.π2.π1 Xext [] t wt = t' ->
  KernameSet.subset (term_global_deps t') deps ->
  erase_global_decls X_type deps X decls prf = Σ' ->
  forall Σext : global_env_ext, abstract_env_ext_rel Xext Σext -> 
  (forall Σ : global_env, abstract_env_rel X Σ -> 
    PCUICWcbvEval.eval Σ t v) ->
    @Ee.eval Ee.default_wcbv_flags Σ' t' E.tBox -> ∥ isErasable Σext [] t ∥.
Proof.
  intros Xext wt.
  intros.
  destruct (erase_correct X_type X univs wfext _ _ Σ' _ _ decls prf wt H H0 H1 X0 _ H2) as [ev [eg [eg']]].
  pose proof (Ee.eval_deterministic H3 eg'). subst.
  pose proof (abstract_env_exists X) as [[? wf]].
  destruct (wfext _ wf). destruct (wt _ H2) as [T wt'].
  pose proof (abstract_env_ext_wf _ H2) as [?].
  eapply erasable_tBox_value; eauto. 
  pose proof (abstract_make_wf_env_ext_correct X univs wfext _ _ wf H2). subst. 
  apply X0; eauto. 
Qed.

Lemma erase_eval_to_box_eager (wfl := Ee.default_wcbv_flags) 
{X_type X} {univs wfext t v Σ' t' deps decls prf} :
  let Xext :=  abstract_make_wf_env_ext X univs wfext in
  forall wt : forall Σ : global_env_ext, abstract_env_ext_rel Xext Σ -> welltyped Σ [] t,
  erase X_type.π2.π1 Xext [] t wt = t' ->
  KernameSet.subset (term_global_deps t') deps ->
  erase_global_decls X_type deps X decls prf = Σ' ->
  forall Σext : global_env_ext, abstract_env_ext_rel Xext Σext -> 
  (forall Σ : global_env, abstract_env_rel X Σ -> 
    PCUICWcbvEval.eval Σ t v) ->
  @Ee.eval Ee.default_wcbv_flags Σ' t' E.tBox -> t' = E.tBox.
Proof.
  intros Xext wt.
  intros.
  destruct (erase_eval_to_box wt H H0 H1 _ H2 X0 H3).
  subst t'.
  destruct (inspect_bool (is_erasableb X_type.π2.π1 Xext [] t wt)) eqn:heq.
  - simp erase. rewrite heq.
    simp erase => //.
  - elimtype False.
    pose proof (abstract_env_exists X) as [[? wf]].
    destruct (@is_erasableP X_type.π2.π1 Xext [] t wt) => //. apply n. 
    intros. sq. now rewrite (abstract_env_ext_irr _ H H2).  
Qed.

From MetaCoq Require Import PCUICFirstorder.


Lemma welltyped_mkApps_inv {cf} {Σ : global_env_ext} Γ f args :  ∥ wf Σ ∥ ->
  welltyped Σ Γ (mkApps f args) -> welltyped Σ Γ f /\ Forall (welltyped Σ Γ) args.
Proof.
  intros wf (A & HA). sq. eapply inversion_mkApps in HA as (? & ? & ?).
  split. eexists; eauto.
  induction t0 in f |- *; econstructor; eauto; econstructor; eauto.
Qed.

Lemma firstorder_erases_deterministic X_type (X : X_type.π1) 
  univs wfext {t t' i u args mind} :
  let Xext :=  abstract_make_wf_env_ext X univs wfext in
  forall wt : (forall Σ, Σ ∼_ext Xext -> welltyped Σ [] t), 
  forall Σ, Σ ∼_ext Xext ->
  Σ ;;; [] |- t : mkApps (tInd i u) args ->
  PCUICWcbvEval.value Σ t ->
  PCUICEnvironment.lookup_env Σ (i.(inductive_mind)) = Some (InductiveDecl mind) ->
  @firstorder_ind Σ (firstorder_env Σ) i ->
  erases Σ [] t t' ->
  t' = erase X_type.π2.π1 Xext [] t wt.
Proof.
  (* pose proof (referenced_impl_ext_wf (@wf_env_ext_referenced extraction_checker_flags Σ)) as Hext. *)
  (* rename X into Hext. *) 
  intros Xext wt Σ Hrel Hty Hvalue Hdecl Hfo Herase.
  assert (Hext : ∥ wf_ext Σ∥) by now eapply heΣ.
  sq. eapply firstorder_value_spec in Hty as Hfov; eauto.
  clear - Hrel Hext Hfov Herase.
  revert t' wt Herase.
  pattern t.
  revert t Hfov.
  eapply firstorder_value_inds. intros.
  rewrite erase_mkApps.
  - intros Σ0 HΣ0. pose proof (abstract_env_ext_irr _ HΣ0 Hrel). subst.
    eapply PCUICValidity.inversion_mkApps in X0 as (? & XX & Happ).
    clear XX. revert Happ. clear. generalize (mkApps (tInd i u) pandi). induction 1.  
    + econstructor.
    + econstructor. econstructor; eauto. eauto.
  - intros. eapply erases_mkApps_inv in Herase as [(? & ? & ? & -> & [Herasable] & ? & ? & ->)|(? & ? & -> & ? & ?)]. all:eauto.
    + exfalso. eapply isErasable_Propositional in Herasable; eauto.  
      red in H1, Herasable. unfold PCUICAst.lookup_inductive, PCUICAst.lookup_minductive, isPropositionalArity in *.
      edestruct PCUICEnvironment.lookup_env as [ [] | ], nth_error, destArity as [[] | ]; auto; try congruence.  
    + inv H2.
      * cbn. unfold erase_clause_1. destruct (inspect_bool (is_erasableb (X_type.π2).π1 Xext [] (tConstruct i n ui) Hyp0)).
        -- exfalso. sq. destruct (@is_erasableP _ _ [] (tConstruct i n ui) Hyp0) => //. 
           specialize_Σ Hrel. sq.
           eapply (isErasable_Propositional (args := [])) in s; eauto. 
           red in H1, s. unfold PCUICAst.lookup_inductive, PCUICAst.lookup_minductive, isPropositionalArity in *.
           edestruct PCUICEnvironment.lookup_env as [ [] | ], nth_error, destArity as [[] | ]; auto; congruence.
        -- f_equal. eapply Forall2_eq. clear X0 H wt. induction H3.
           ++ cbn. econstructor. 
           ++ cbn. econstructor.
               ** inv H0. eapply H5. eauto.
               ** inv H0. eapply IHForall2. eauto.
      * exfalso. eapply (isErasable_Propositional (args := [])) in X1; eauto.  
        red in H1, X1.
        unfold PCUICAst.lookup_inductive, PCUICAst.lookup_minductive, isPropositionalArity in *.
        edestruct PCUICEnvironment.lookup_env as [ [] | ], nth_error, destArity as [[] | ]; auto; congruence.
  - eauto.
  - intros ? ? H3. assert (Hext_ : ∥ wf_ext Σ0∥) by now eapply heΣ.
    sq.
    specialize_Σ H2.
    eapply (isErasable_Propositional) in H3; eauto.
    pose proof (abstract_env_ext_irr _ H2 Hrel). subst.
    red in H1, H3. unfold PCUICAst.lookup_inductive, PCUICAst.lookup_minductive, isPropositionalArity in *.
    edestruct PCUICEnvironment.lookup_env as [ [] | ], nth_error, destArity as [[] | ]; auto; congruence.
  - intros.  assert (Hext__ : ∥ wf_ext Σ0∥) by now eapply heΣ.
    specialize_Σ H2. eapply welltyped_mkApps_inv in wt; eauto. eapply wt.
    now sq.
    Unshelve. all: try exact False.
Qed.  

From MetaCoq Require Import PCUICProgress.

Lemma erase_correct_strong'  (wfl := Ee.default_wcbv_flags) X_type (X : X_type.π1) 
univs wfext {t v Σ' t' deps i u args mind} decls prf :
let Xext :=  abstract_make_wf_env_ext X univs wfext in
forall wt : (forall Σ, Σ ∼_ext Xext -> welltyped Σ [] t), 
forall Σ, abstract_env_ext_rel Xext Σ ->
  axiom_free Σ ->
  Σ ;;; [] |- t : mkApps (tInd i u) args -> 
  PCUICEnvironment.lookup_env Σ (i.(inductive_mind)) = Some (InductiveDecl mind) ->
  @firstorder_ind Σ (firstorder_env Σ) i ->
  erase X_type.π2.π1 Xext [] t wt = t' ->
  KernameSet.subset (term_global_deps t') deps ->
  erase_global_decls X_type deps X decls prf = Σ' ->
  red Σ [] t v ->
  (forall v', red1 Σ [] v v' -> False) ->
  forall wt', ∥ Σ' ⊢ t' ▷ erase X_type.π2.π1 Xext [] v wt' ∥.
Proof.
  intros Xext wt Σ Hrel Hax Hty Hdecl Hfo <- Hsub <- Hred Hirred wt'.
  pose proof (heΣ _ _ _ Hrel) as [Hwf].  eapply wcbv_standardization in Hty as Hty_; eauto. destruct Hty_ as [Heval].
  edestruct (erase_correct X_type X univs wfext t v) as [v' [H1 H2]]; eauto.
  1:{ intros ? H_. sq. enough (Σ0 = Σ) as -> by eauto. 
      pose proof (abstract_make_wf_env_ext_correct _ _ _ _ _ H_ Hrel). now subst. }
  eapply firstorder_erases_deterministic in H1; eauto.
  + rewrite H1 in H2. eapply H2.
  + eapply subject_reduction; eauto.
  + eapply PCUICWcbvEval.eval_to_value. eauto.
Qed.   

Lemma erase_correct_strong  (wfl := Ee.default_wcbv_flags) X_type (X : X_type.π1) 
univs wfext {t v Σ' t' deps i u args mind} decls prf :
let Xext :=  abstract_make_wf_env_ext X univs wfext in
forall wt : (forall Σ, Σ ∼_ext Xext -> welltyped Σ [] t), 
forall Σ, abstract_env_ext_rel Xext Σ ->
  axiom_free Σ ->
  Σ ;;; [] |- t : mkApps (tInd i u) args -> 
  PCUICEnvironment.lookup_env Σ (i.(inductive_mind)) = Some (InductiveDecl mind) ->
  @firstorder_ind Σ (firstorder_env Σ) i ->
  erase X_type.π2.π1 Xext [] t wt = t' ->
  KernameSet.subset (term_global_deps t') deps ->
  erase_global_decls X_type deps X decls prf = Σ' ->
  red Σ [] t v ->
  (forall v', red1 Σ [] v v' -> False) ->
  exists wt', ∥ Σ' ⊢ t' ▷ erase X_type.π2.π1 Xext [] v wt' ∥.
Proof.
  intros Xext wt Σ Hrel Hax Hty Hdecl Hfo <- Hsub <- Hred Hirred.
  unshelve eexists.
  - abstract (intros Σ_ H_; pose proof (heΣ _ _ _ H_); sq;
    pose proof (abstract_env_ext_irr _ H_ Hrel); subst; eapply red_welltyped; eauto; econstructor; eauto).
  - eapply erase_correct_strong'; eauto.
Qed.    

Section EraseGlobalFast.

  Import PCUICEnvironment.

Definition decls_prefix decls (Σ' : global_env) := 
  ∑ Σ'', declarations Σ' = Σ'' ++ decls.

Lemma on_global_decls_prefix {cf} Pcmp P univs retro decls decls' :
  on_global_decls Pcmp P univs retro (decls ++ decls') ->
  on_global_decls Pcmp P univs retro decls'.
Proof.
  induction decls => //.
  intros ha; depelim ha.
  now apply IHdecls.
Qed.

Lemma decls_prefix_wf {decls Σ} : 
  decls_prefix decls Σ -> wf Σ -> wf {| universes := Σ.(universes); declarations := decls; retroknowledge := Σ.(retroknowledge) |}.
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
  lookup_env {| universes := Σ; declarations := decls; retroknowledge := Σ.(retroknowledge) |} kn = Some decl ->
  on_global_decl cumulSpec0 (lift_typing typing) (Σ, universes_decl_of_decl decl) kn decl.
Proof.
  intros prefix wfΣ.
  have wfdecls := decls_prefix_wf prefix wfΣ.
  epose proof (weakening_env_lookup_on_global_env (lift_typing typing) _ Σ kn decl 
    weaken_env_prop_typing wfdecls wfΣ).
  forward X. red; split => //. cbn. apply incl_cs_refl. cbn.
  apply Retroknowledge.extends_refl.
  now apply (X wfdecls).
Qed.

(* This version of global environment erasure keeps the same global environment throughout the whole 
   erasure, while folding over the list of declarations. *)

Program Fixpoint erase_global_decls_fast (deps : KernameSet.t) 
  X_type (X:X_type.π1) (decls : global_declarations) 
  (prop : forall Σ : global_env, abstract_env_rel X Σ -> ∥ decls_prefix decls Σ ∥) : E.global_declarations :=
  match decls with
  | [] => []
  | (kn, ConstantDecl cb) :: decls =>
    if KernameSet.mem kn deps then
      let Xext' :=  abstract_make_wf_env_ext X (cst_universes cb) _ in
      let cb' := erase_constant_body X_type.π2.π1 Xext' cb _ in
      let deps := KernameSet.union deps (snd cb') in
      let Σ' := erase_global_decls_fast deps X_type X decls _ in
      ((kn, E.ConstantDecl (fst cb')) :: Σ')
    else
      erase_global_decls_fast deps X_type X decls _

  | (kn, InductiveDecl mib) :: decls =>
    if KernameSet.mem kn deps then
      let mib' := erase_mutual_inductive_body mib in
      let Σ' := erase_global_decls_fast deps X_type X decls _ in
      ((kn, E.InductiveDecl mib') :: Σ')
    else erase_global_decls_fast deps X_type X decls _
  end.
Next Obligation.
  pose proof (abstract_env_wf _ H) as [?].
  specialize_Σ H. sq. split. cbn. apply X3. cbn. 
  eapply decls_prefix_wf in X3; tea.
  destruct X3 as [onu ond]. cbn in ond.
  now depelim ond.
Qed.
Next Obligation.
  pose proof (abstract_env_ext_wf _ H) as [?].
  pose proof (abstract_env_exists X) as [[? wf]].
  pose proof (abstract_env_wf _ wf) as [?].
  pose proof (prop' := prop _ wf).
  sq. eapply (weaken_prefix (kn := kn)) in prop'; tea.
  2:{ cbn. rewrite eqb_refl //. }
  epose proof (abstract_make_wf_env_ext_correct X (cst_universes cb) _ _ _ wf H). subst. 
  apply prop'.
Qed.
Next Obligation.
  specialize_Σ H. sq; red. destruct prop as [Σ' ->].
  eexists (Σ' ++ [(kn, ConstantDecl cb)]); rewrite -app_assoc //.
Qed.
Next Obligation.
  specialize_Σ H. sq; red. destruct prop as [Σ' ->].
  eexists (Σ' ++ [(kn, ConstantDecl cb)]); rewrite -app_assoc //.
Qed.
Next Obligation.
  specialize_Σ H. sq; red. destruct prop as [Σ' ->].
  eexists (Σ' ++ [(kn, _)]); rewrite -app_assoc //.
Qed.
Next Obligation.
  specialize_Σ H. sq; red. destruct prop as [Σ' ->].
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

Definition add_suffix suffix Σ := set_declarations Σ (suffix ++ Σ.(declarations)).

Lemma add_suffix_cons d suffix Σ : add_suffix (d :: suffix) Σ = add_global_decl (add_suffix suffix Σ) d. 
Proof. reflexivity. Qed.

Lemma global_erased_with_deps_weaken_prefix suffix Σ Σ' kn : 
  wf (add_suffix suffix Σ) ->
  global_erased_with_deps Σ Σ' kn ->
  global_erased_with_deps (add_suffix suffix Σ) Σ' kn.
Proof.
  induction suffix.
  - unfold add_suffix; cbn. intros wf hg.
    now rewrite /set_declarations /= -eta_global_env.
  - rewrite add_suffix_cons. intros wf H.
    destruct a as [kn' d]. eapply global_erases_with_deps_weaken => //.
    apply IHsuffix => //.
    destruct wf as [onu ond]. now depelim ond.
Qed.


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
    set (wfΣx :=  abstract_make_wf_env_ext _ _ _).
    set (wfΣ'x :=  abstract_make_wf_env_ext _ _ _).
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
    set (wfΣdw :=  abstract_make_wf_env_ext wfΣdwfe (cst_universes c) (sq wfextΣd)).
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
  
Lemma erase_global_deps_fast_spec_gen {deps} 
  {X_type X X'} {decls hprefix hprefix'} :
  (forall Σ Σ', abstract_env_rel X Σ -> abstract_env_rel X' Σ' -> universes Σ = universes Σ' /\ retroknowledge Σ = retroknowledge Σ') -> 
  erase_global_decls_fast deps X_type X decls hprefix = 
  erase_global_decls X_type deps X' decls hprefix'.
Proof.
  intros equ.
  induction decls in X, X', equ, deps, hprefix, hprefix' |- * => //.
  pose proof (abstract_env_exists X) as [[Σ wfΣ]].  
  pose proof (abstract_env_exists X') as [[Σ' wfΣ']].
  pose proof (abstract_env_wf _ wfΣ) as [wf]. 
  pose proof (abstract_env_exists (abstract_pop_decls X')) as [[? wfpop]].
  unshelve epose proof (abstract_pop_decls_correct X' decls _ _ _ wfΣ' wfpop) as [? [? ?]].
  { now eexists. }

  destruct a as [kn []].
  - cbn. 
    set (obl := (erase_global_decls_fast_obligation_1 X_type X ((kn, ConstantDecl c) :: decls)
             hprefix kn c decls eq_refl)).
    set (eb := erase_constant_body _ _ _ _).
    set (eb' := erase_constant_body _ _ _ _).
    assert (eb = eb') as <-.
    { subst eb eb'.
      destruct (hprefix _ wfΣ) as [[Σ'' eq]].
      eapply erase_constant_body_suffix; cbn => //.
      intros.
      epose proof (abstract_make_wf_env_ext_correct X (cst_universes c) _ _ _ wfΣ H2).
      epose proof (abstract_make_wf_env_ext_correct (abstract_pop_decls X') (cst_universes c) _ _ _ wfpop H3).
      subst. split => //. 
      sq; red. cbn. 
      rewrite eq. rewrite <- H0, <- H1. split. symmetry. apply equ; eauto.
      eexists (Σ'' ++ [(kn, ConstantDecl c)]). subst. now rewrite -app_assoc. subst.
      symmetry. now apply equ.
      }
    destruct KernameSet.mem => //; f_equal; eapply IHdecls.
    intros. unshelve epose proof (abstract_pop_decls_correct X' decls _ _ _ wfΣ' H3) as [? ?].
    { now eexists. } intuition auto. rewrite <- H6. apply equ; eauto. rewrite <- H7; apply equ; auto.
    intros. unshelve epose proof (abstract_pop_decls_correct X' decls _ _ _ wfΣ' H3) as [? ?].
    { now eexists. }  intuition auto. rewrite <- H6. apply equ; eauto. rewrite <- H7; apply equ; auto. 
  
    - cbn.
    destruct KernameSet.mem => //; f_equal; eapply IHdecls.
    intros. unshelve epose proof (abstract_pop_decls_correct X' decls _ _ _ wfΣ' H3) as [? ?].
    { now eexists. }
    intuition auto. rewrite <- H6. apply equ; eauto. rewrite <- H7; apply equ; auto.
    intros. unshelve epose proof (abstract_pop_decls_correct X' decls _ _ _ wfΣ' H3) as [? ?].
    { now eexists. }
    intuition auto. rewrite <- H6. apply equ; eauto. rewrite <- H7; apply equ; auto.
Qed.

Lemma erase_global_deps_fast_spec {deps} {X_type X} {decls hprefix hprefix'} :
  erase_global_decls_fast deps X_type X decls hprefix = 
  erase_global_decls X_type deps X decls hprefix'.
Proof.
  eapply erase_global_deps_fast_spec_gen; intros.
  rewrite (abstract_env_irr _ H H0); eauto.  
Qed.

Definition erase_global_fast X_type deps X decls (prf:forall Σ : global_env, abstract_env_rel X Σ -> declarations Σ = decls) :=
  erase_global_decls_fast deps X_type X decls (fun _ H => sq ([] ; prf _ H)).

Lemma expanded_erase_global_fast (cf := config.extraction_checker_flags) deps 
  {X_type X decls prf} :
  forall Σ : global_env, abstract_env_rel X Σ -> 
  PCUICEtaExpand.expanded_global_env Σ ->
  expanded_global_env (erase_global_fast X_type deps X decls prf).
Proof.
  unfold erase_global_fast.
  rewrite erase_global_deps_fast_spec. 
  eapply expanded_erase_global.
Qed.

Lemma expanded_erase_fast (cf := config.extraction_checker_flags) 
  {X_type X decls prf} univs wfΣ t wtp :
  forall Σ : global_env, abstract_env_rel X Σ -> 
  PCUICEtaExpand.expanded Σ [] t ->
  let X' :=  abstract_make_wf_env_ext X univs wfΣ in
  let et := (erase X_type.π2.π1 X' [] t wtp) in
  let deps := EAstUtils.term_global_deps et in
  expanded (erase_global_fast X_type deps X decls prf) [] et.
Proof.
  intros Σ wf hexp X'. pose proof (abstract_env_wf _ wf) as [?].
  eapply (expanded_erases (Σ := (Σ, univs))); tea.
  eapply (erases_erase (X := X')). 
  pose proof (abstract_env_ext_exists X') as [[? wfmake]].
  now rewrite <- (abstract_make_wf_env_ext_correct X univs _ _ _ wf wfmake).
  cbn. unfold erase_global_fast. rewrite erase_global_deps_fast_spec //.
  eapply (erases_deps_erase (X := X) univs wfΣ); eauto. 
Qed.

Lemma erase_global_fast_wf_glob X_type X deps decls prf :
  @wf_glob all_env_flags (erase_global_fast X_type X deps decls prf).
Proof.
  unfold erase_global_fast; rewrite erase_global_deps_fast_spec.
  eapply erase_global_decls_wf_glob.
Qed.

Lemma erase_wellformed_fast (efl := all_env_flags) 
  {X_type X decls prf} univs wfΣ {Γ t} wt
  (X' :=  abstract_make_wf_env_ext X univs wfΣ) :
  let t' := erase X_type.π2.π1 X' Γ t wt in
  wellformed (erase_global_fast X_type (term_global_deps t') X decls prf) #|Γ| t'.
Proof.
  intros. 
  cbn. unfold erase_global_fast. rewrite erase_global_deps_fast_spec.
  eapply erase_wellformed.
Qed.

End EraseGlobalFast.
