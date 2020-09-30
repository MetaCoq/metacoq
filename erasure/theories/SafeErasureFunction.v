(* Distributed under the terms of the MIT license. *)
From Coq Require Import Program.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICTyping PCUICInversion PCUICGeneration
     PCUICConfluence PCUICConversion 
     PCUICCumulativity PCUICSR PCUICSafeLemmata
     PCUICValidity PCUICPrincipality PCUICElimination PCUICSN.
From MetaCoq.SafeChecker Require Import PCUICSafeReduce PCUICSafeChecker PCUICSafeRetyping.
From MetaCoq.Erasure Require Import EArities Extract Prelim ErasureCorrectness.

Local Open Scope string_scope.
Set Asymmetric Patterns.
Import MonadNotation.

From Equations Require Import Equations.

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

Set Equations Transparent.
Local Set Keyed Unification.
Require Import ssreflect.

Section fix_sigma.
Local Existing Instance extraction_checker_flags.
Variable Σ : global_env_ext.
Variable HΣ : ∥wf Σ∥.

Definition term_rel : Relation_Definitions.relation (∑ Γ t, wellformed Σ Γ t) :=
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
  induction (normalisation' Σ Γ s X H) as [s _ IH].
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
        eapply @normalisation'; eauto.
      * constructor. do 2 eexists. now split.
Grab Existential Variables.
- eapply red_wellformed; sq.
  3:eapply Relation_Properties.clos_rtn1_rt in r; eassumption. all:eauto.
- destruct H as [[] |[]].
  -- eapply inversion_Prod in X0 as (? & ? & ? & ? & ?) ; auto.
     eapply cored_red in H0 as [].
     econstructor. econstructor. econstructor. eauto. eapply subject_reduction; eauto.
  -- eapply cored_red in H0 as [].
     eapply isWfArity_prod_inv in X0 as [_ ?].
     econstructor 2. sq.
     eapply isWfArity_red in i; eauto.
     destruct i as (? & ? & ? & ?).
     exists (x ++ [vass na A])%list, x0. cbn; split.
     2:{ unfold snoc, app_context in *. rewrite <- app_assoc. eassumption. }
     change ([] ,, vass na A) with ([vass na A] ,,, []).
     rewrite destArity_app_aux. rewrite e. cbn. reflexivity.
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

Equations is_arity Γ (HΓ : ∥wf_local Σ Γ∥) T (HT : wellformed Σ Γ T) :
  {Is_conv_to_Arity Σ Γ T} + {~ Is_conv_to_Arity Σ Γ T}
  by wf ((Γ;T;HT) : (∑ Γ t, wellformed Σ Γ t)) term_rel :=
  {
    is_arity Γ HΓ T HT with (@reduce_to_sort _ Σ HΣ Γ T HT) => {
    | Checked H => left _ ;
    | TypeError _ with inspect (@reduce_to_prod _ Σ HΣ Γ T _) => {
      | exist (Checked (na; A; B; H)) He with is_arity (Γ,, vass na A) _ B _ :=
        { | left H => left _;
          | right H => right _ };
      | exist (TypeError e) He => right _ } }
  }.
Next Obligation.
  sq. econstructor. split. sq. eassumption. econstructor.
Qed.
Next Obligation.
  clear He.
  destruct HT as [ [] | [] ]; sq.
  - eapply subject_reduction in X; eauto.
    eapply inversion_Prod in X as (? & ? & ? & ? & ?).
    econstructor. eauto. cbn. eauto. auto.
  - econstructor. eauto.
    eapply isWfArity_red in X; eauto.
    cbn. eapply isWfArity_prod_inv; eauto.
Qed.
Next Obligation.
  clear He.
  sq. destruct HT as [ [] | [] ].
  - eapply subject_reduction in X; eauto.
    eapply inversion_Prod in X as (? & ? & ? & ? & ?).
    do 2 econstructor. eauto. auto.
  - econstructor 2. sq.
    eapply isWfArity_red in X; eauto.
    eapply isWfArity_prod_inv; eauto.
Qed.
Next Obligation.
  sq. repeat eexists. eassumption.
Qed.
Next Obligation.
  destruct H as (? & ? & ?). eexists (tProd _ _ _). split; sq.
  etransitivity. eassumption. eapply PCUICReduction.red_prod. reflexivity.
  eassumption. now cbn.
Qed.
Next Obligation.
  clear He.
  destruct HΣ as [wΣ].
  destruct H1 as (? & ? & ?). sq.
  destruct H.
  edestruct (red_confluence wfΣ X0 X) as (? & ? & ?); eauto.
  eapply invert_red_prod in r as (? & ? & [] & ?); eauto. subst.

  eapply invert_cumul_arity_l in H2. 2: eauto.
  2: eapply PCUICCumulativity.red_cumul. 2:eauto.
  destruct H2 as (? & ? & ?). sq.

  eapply invert_red_prod in X2 as (? & ? & [] & ?); eauto. subst. cbn in *.
  exists x4; split; eauto.

  destruct HT as [ [] | [] ].
  ++ sq. pose proof (X2). pose proof X2.

     eapply subject_reduction in X4. 2:eauto. 2:{ etransitivity. exact X. exact r0. }
     eapply inversion_Prod in X4 as (? & ? & ? & ? & ?) ; auto.

     eapply subject_reduction in X3. 2:eauto. 2:{ exact X0. }
     eapply inversion_Prod in X3 as (? & ? & ? & ? & ?) ; auto.

     etransitivity. eassumption.

     eapply context_conversion_red; eauto. econstructor.

     eapply conv_context_refl; eauto. econstructor.

     eapply conv_sym, red_conv; eauto.
  ++ sq. etransitivity. eassumption.

     eapply context_conversion_red; eauto. econstructor.

     eapply conv_context_refl; eauto.

     econstructor.

     eapply conv_sym, red_conv; eauto.
Qed.

Next Obligation.
Admitted. (* reduce to prod cannot fail on types convertible to arities *)

End fix_sigma.
Transparent wf_reduction.
Local Existing Instance extraction_checker_flags.
Definition wf_ext_wf Σ : wf_ext Σ -> wf Σ := fst.
Hint Resolve wf_ext_wf : core.

(* Top.sq should be used but the behavior is a bit different *)
Local Ltac sq :=
  repeat match goal with
         | H : ∥ _ ∥ |- _ => destruct H
         end; try eapply sq.

Lemma nIs_conv_to_Arity_isWfArity_elim {Σ : global_env_ext} {Γ x} : 
  ~ Is_conv_to_Arity Σ Γ x ->
  isWfArity typing Σ Γ x ->
  False.
Proof.
  intros nis [ctx [s [da wf]]]. apply nis.
  red. exists (it_mkProd_or_LetIn ctx (tSort s)).
  split. sq. apply PCUICArities.destArity_spec_Some in da.
  simpl in da. subst x.
  reflexivity.
  now eapply it_mkProd_isArity.
Qed.

(** Deciding if a term is erasable or not as a total function on well-typed terms.
  A term is erasable if:
  - it represents a type, i.e., its type is an arity
  - it represents a proof: its sort is Prop.
*)

Lemma reduce_to_sort_complete {cf:checker_flags} {Σ : global_env_ext} {wfΣ : ∥ wf Σ ∥} {Γ t wt} e : 
  reduce_to_sort wfΣ Γ t wt = TypeError e ->
  (forall s, red Σ Γ t (tSort s) -> False).
Proof.
Admitted.

Program Definition is_erasable (Σ : PCUICAst.global_env_ext) (HΣ : ∥wf_ext Σ∥) (Γ : context) (t : PCUICAst.term) (Ht : welltyped Σ Γ t) :
  ({∥isErasable Σ Γ t∥} + {∥(isErasable Σ Γ t -> False)∥}) :=
  let T := @type_of extraction_checker_flags Σ _ _ Γ t Ht in
  let b := is_arity Σ _ Γ _ T _ in
  match b : {_} + {_} return _ with
  | left _ => left _
  | right _ => let K := @type_of extraction_checker_flags Σ _ _ Γ T _ in
       match @reduce_to_sort _ Σ _ Γ K _ with
       | Checked (u; Hu) =>
          match Universe.is_prop u with true => left _ | false => right _ end
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
  eapply typing_wellformed; eauto; sq; auto. apply X.
Qed.
Next Obligation.
  unfold type_of in *.
  destruct infer as [x [[Htx Hp]]].
  destruct H as [T' [redT' isar]].
  sq. econstructor. split. eapply type_reduction; eauto.
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
  eapply validity in Htx as [|]; auto.
  - elim (nIs_conv_to_Arity_isWfArity_elim H i).
  - destruct i as [s Hs]. econstructor; eauto.
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
  eapply wat_wellformed; eauto. sq; auto.
  now sq.
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
  pose proof (red_confluence X2 r0 r) as [v' [redl redr]].
  eapply invert_red_sort in redl.
  eapply invert_red_sort in redr. subst. noconf redr.
  right. exists u; split; eauto.
  eapply type_reduction; eauto using typing_wf_local.
Qed.
Next Obligation.
  unfold type_of in *.
  destruct reduce_to_sort; try discriminate.
  destruct (infer _ (is_erasable_obligation_7 _ _ _ _ _ _)) as [? [[? ?]]].
  destruct (infer _ (is_erasable_obligation_1 _ _)) as [? [[? ?]]].
  destruct a as [u' redu']. simpl in *.
  sq.
  pose proof (red_confluence X r0 r) as [v' [redl redr]].
  eapply invert_red_sort in redl.
  eapply invert_red_sort in redr. subst. noconf redr.
  clear Heq_anonymous0.
  intros (? & ? & ?).
  destruct s as [ | (? & ? & ?)]; simpl in *.
  + destruct H. eapply arity_type_inv; eauto using typing_wf_local.
  + pose proof (c0 _ t2).
    eapply type_reduction in t0; eauto.
    eapply cumul_prop1 in t3; eauto.
    eapply leq_term_prop_sorted_l in t0; eauto.
    2:reflexivity.
    2:eapply validity; eauto.
    eapply leq_universe_prop in t0; auto. congruence.
Qed.
Next Obligation.
  unfold type_of in *.
  destruct HΣ.
  symmetry in Heq_anonymous.
  pose proof (reduce_to_sort_complete _ Heq_anonymous).
  clear Heq_anonymous.
  destruct (infer _ (is_erasable_obligation_7 _ _ _ _ _ _)) as [? [[? ?]]].
  destruct (infer _ (is_erasable_obligation_1 _ _)) as [? [[? ?]]].
  simpl in *. 
  eapply validity in t1; auto.
  destruct t1.
  eapply nIs_conv_to_Arity_isWfArity_elim; eauto.
  destruct i as [s Hs].
  red in Hs.
  specialize (c _ Hs).
  eapply invert_cumul_sort_r in c as [u' [redu' leq]].
  now apply (H0 _ redu').
Qed.

Section Erase.

  Definition is_box c :=
    match c with
    | E.tBox => true
    | _ => false
    end.

  Fixpoint mkAppBox c n :=
    match n with
    | 0 => c
    | S n => mkAppBox (E.tApp c E.tBox) n
    end.

  Definition on_snd_map {A B C} (f : B -> C) (p : A * B) :=
    (fst p, f (snd p)).

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
    
  Section MapIn.
    Context {A B : Type}.
    Context {P : A -> Type}.
    Context (f : forall (x : A), P x -> B).

    Equations map_In (l : list A) (H : forall x, In x l -> P x) : list B :=
    map_In nil _ := nil;
    map_In (cons x xs) H := cons (f x (H x (or_introl eq_refl))) (map_In xs (fun x inx => H x _)).
  End MapIn.

  Lemma All2_In {A B} (P : A -> B -> Type) l l' x : In x l -> 
    All2 P l l' -> ∥ ∑ x', P x x' ∥.
  Proof.
    induction 2; simpl in H => //.
    destruct H as [-> | H].
    constructor. now exists y.
    now eapply IHX.
  Qed.
  
  Lemma All_In {A} (P : A -> Type) l x : In x l -> 
    All P l -> ∥ P x ∥.
  Proof.
    induction 2; simpl in H => //.
    destruct H as [-> | H].
    now constructor.
    now eapply IHX.
  Qed.

  Lemma map_In_spec {A B : Type} {P : A -> Type} (f : A -> B) (l : list A) (H : forall x, In x l -> P x) :
    map_In (fun (x : A) (_ : P x) => f x) l H = List.map f l.
  Proof.
    remember (fun (x : A) (_ : P x) => f x) as g.
    funelim (map_In g l H) => //; simpl. f_equal. now rewrite H0.
  Qed.

  Lemma welltyped_brs Γ ind t1 t2 brs : welltyped Σ Γ (tCase ind t1 t2 brs) -> 
    Forall (fun x => welltyped Σ Γ x.2) brs.
  Proof.
    intros [t Ht]. destruct HΣ.
    eapply inversion_Case in Ht as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?); auto.
    simpl in *. clear e2.
    induction a. constructor.
    intuition auto. constructor; auto.
    eexists; eauto.
  Qed.
  
  Section EraseMfix.
    Context (erase : forall (Γ : context) (t : term) (Ht : welltyped Σ Γ t), E.term).

    Definition erase_mfix Γ (defs : mfixpoint term) 
    (H : forall d, In d defs -> welltyped Σ (Γ ,,, PCUICLiftSubst.fix_context defs) d.(dbody)) : EAst.mfixpoint E.term :=
    let Γ' := (PCUICLiftSubst.fix_context defs ++ Γ)%list in
    map_In (fun d wt => 
      let dbody' := erase Γ' d.(dbody) wt in
      ({| E.dname := d.(dname); E.rarg := d.(rarg); E.dbody := dbody' |})) defs H.

    Definition erase_brs Γ (brs : list (nat * term)) 
      (H : forall d, In d brs -> welltyped Σ Γ d.2) : list (nat * E.term) :=
      map_In (fun br wt => let br' := erase Γ br.2 wt in (br.1, br')) brs H.
  
  End EraseMfix.

  Equations? (noeqns noind) erase (Γ : context) (t : term) (Ht : welltyped Σ Γ t) : E.term
      by struct t  :=
    erase Γ t Ht with (is_erasable Σ HΣ Γ t Ht) :=
    {
      erase Γ _ Ht (left _) := E.tBox;
      erase Γ (tRel i) Ht _ := E.tRel i ;
      erase Γ (tVar n) Ht _ := E.tVar n ;
      erase Γ (tEvar m l) Ht _ := let l' := map_In (fun x wt => erase Γ x wt) l _ in (E.tEvar m l') ;
      erase Γ (tSort u) Ht _ := E.tBox ;

      erase Γ (tConst kn u) Ht _ := E.tConst kn ;
      erase Γ (tInd kn u) Ht _ := E.tBox ;
      erase Γ (tConstruct kn k u) Ht _ := E.tConstruct kn k ;
      erase Γ (tProd na b t) Ht _ := E.tBox ;
      erase Γ (tLambda na b t) Ht _ :=
        let t' := erase (vass na b :: Γ) t _ in
        E.tLambda na t';
      erase Γ (tLetIn na b t0 t1) Ht _ :=
        let b' := erase Γ b _ in
        let t1' := erase (vdef na b t0 :: Γ) t1 _ in
        E.tLetIn na b' t1' ;
      erase Γ (tApp f u) Ht _ :=
        let f' := erase Γ f _ in
        let l' := erase Γ u _ in
        E.tApp f' l';
      erase Γ (tCase ip p c brs) Ht _ with (let c' := erase Γ c _ in (c', is_box c')) := 
        { | (c', true) with brs :=
             { | (a, b) :: brs => let b' := erase Γ b _ in E.mkApps b' (repeat E.tBox a);
               | [] => E.tCase ip c' [] } ;
          | (c', false) :=
            let brs' := erase_brs erase Γ brs _ in
            E.tCase ip c' brs' } ;
      erase Γ (tProj p c) Ht _ :=
        let c' := erase Γ c _ in
        if is_box c' then E.tBox else E.tProj p c' ;
      erase Γ (tFix mfix n) Ht _ :=
        let mfix' := erase_mfix erase Γ mfix _ in
        E.tFix mfix' n;
      erase Γ (tCoFix mfix n) Ht _ :=
        let mfix' := erase_mfix (erase) Γ mfix _ in
        E.tCoFix mfix' n
    }.
  Proof.
    all:try clear b'; try clear f'; try clear erase.
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
    - eapply inversion_Case in Ht as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?); auto.
      eexists; eauto.
    - clear wildcard11.
      eapply inversion_Case in Ht as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?); auto.
      simpl in *.
      depelim a0. simpl in p0. intuition subst.
      eexists; eauto.
    - clear wildcard11.
      eapply inversion_Case in Ht as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?); auto.
      simpl in *.
      eapply All2_In in a as [(x' & (? & ?) & ?)]; eauto.
      simpl in *. subst. eexists; eauto.
    - clear wildcard12.
      eapply inversion_Proj in Ht as (? & ? & ? & ? & ? & ? & ? & ? & ?); auto.
      eexists; eauto.
    - eapply inversion_Fix in Ht as (? & ? & ? & ? & ? & ?); auto.
      eapply All_In in a0; eauto.
      destruct a0 as [[a0 _]]. eexists; eauto.
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

Local Arguments bind _ _ _ _ ! _.

Opaque wf_reduction.
Arguments iswelltyped {cf Σ Γ t A}.
Hint Constructors typing erases : core.

Lemma isType_isErasable Σ Γ T : isType Σ Γ T -> isErasable Σ Γ T.
Proof.
  intros [s Hs].
  exists (tSort s). intuition auto. left; simpl; auto.
Qed.

Lemma erase_to_box {Σ : global_env_ext} {wfΣ : ∥wf_ext Σ∥} {Γ t} (wt : welltyped Σ Γ t) :
  is_box (erase Σ wfΣ Γ t wt) -> ∥ isErasable Σ Γ t ∥.
Proof.
  revert Γ t wt.
  fix IH 2. intros.
  destruct (is_erasable Σ wfΣ Γ t wt) eqn:ise; auto. 
  destruct t; simpl in *; rewrite ise in H; simpl in *; try discriminate. 
  - intros. destruct wt. sq. clear ise.
    eapply inversion_Ind in t as (? & ? & ? & ? & ? & ?) ; auto.
    red. eexists. split. econstructor; eauto. left.
    eapply isArity_subst_instance.
    eapply isArity_ind_type; eauto.
  - simpl.
    destruct is_box eqn:isb.
    simp erase. clear IH. todo "box".
    clear IH. todo "box".
  - todo "box".
Admitted.

(* Lemma All2_map_in {A B C} (P : A -> B -> Type) (Q : A -> Type) (f : forall x : A, Q x -> B) l H:
  All2 P l (map_In f l H) -> 
  forall x, In x l -> P x (f x All (fun x => P x (f )) *)

Lemma nth_error_map_In {A B : Type} {P : A -> Type} (f : forall x : A, P x -> B) (l : list A) (H : forall x, In x l -> P x) n x :
  nth_error (map_In f l H) n = Some x ->
  ∑ a, (nth_error l n = Some a) * 
  ∑ p : P a, x = f a p.
Proof.
  induction l in n, H |- *. simpl. rewrite nth_error_nil => //.
  destruct n; simpl; intros [=].
  subst x.
  eexists; intuition eauto.
  eapply IHl. eapply H1.
Qed.

Lemma map_In_length {A B : Type} {P : A -> Type} (f : forall x : A, P x -> B) (l : list A) (H : forall x, In x l -> P x) :
  #|map_In f l H| = #|l|.
Proof.
  induction l; simpl; auto.
Qed.
Hint Rewrite @map_In_length : len.  

Lemma erase_erase_clause_1 {Σ} {wfΣ : ∥wf_ext Σ∥} {Γ t} (wt : welltyped Σ Γ t) : 
  erase Σ wfΣ Γ t wt = erase_clause_1 Σ wfΣ (erase Σ wfΣ) Γ t wt (is_erasable Σ wfΣ Γ t wt).
Proof.
  destruct t; simpl; auto.
Qed.
Hint Rewrite @erase_erase_clause_1 : erase.

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
         (fun Σ Γ wfΓ => wf_local Σ Γ)); intros; auto; clear Σ w; rename Σ0 into Σ.

  all:simpl erase; eauto.

  all: simpl erase in *.
  all: unfold erase_clause_1 in *.
  all:sq.
  all: cbn in *; repeat (try destruct ?;  repeat match goal with
                                          [ H : Checked _ = Checked _ |- _ ] => inv H
                                        | [ H : TypeError _ = Checked _ |- _ ] => inv H
                                        | [ H : welltyped _ _ _ |- _ ] => destruct H as []
                                             end; sq; eauto).

  - repeat econstructor; eauto.
  - econstructor. eapply isType_isErasable.
    eexists. econstructor; eauto.

  - econstructor.
    clear E.
    eapply inversion_Ind in t as (? & ? & ? & ? & ? & ?) ; auto.
    red. eexists. split. econstructor; eauto. left.
    eapply isArity_subst_instance.
    eapply isArity_ind_type; eauto.
  - simp erase. clear E.
    destruct is_erasable. simp erase.
    destruct brs; simp erase.
    constructor.
    eapply elim_restriction_works; eauto.
    intros isp. eapply isErasable_Proof in isp. eauto.
    destruct s. constructor; auto.
    constructor. 
    destruct p0 as [na ?]. simp erase.
    simpl. todo "erasure optimization". 
    eapply erase_to_box in E0. elimtype False.
    sq. eauto.
    
  - constructor. 
    eapply elim_restriction_works; eauto.
    intros isp. eapply isErasable_Proof in isp. eauto.
    eapply H4.
    unfold erase_brs. eapply All2_from_nth_error. now autorewrite with len.
    intros. eapply All2_nth_error_Some in X3; eauto.
    destruct X3 as [t' [htnh eq]].
    eapply nth_error_map_In in H8.
    destruct H8 as [a [Hnth [p' eq']]].
    subst. simpl. rewrite Hnth in H7. noconf H7.
    intuition auto.

  - eapply erase_to_box in E0. clear E.
    destruct E0.
    constructor.
    destruct X2. todo "erasure optimization on projections".
    
  - constructor. clear E. clear E0.
    eapply inversion_Proj in t as (? & ? & ? & ? & ? & ? & ? & ? & ?) ; auto.
    eapply elim_restriction_works_proj; eauto.
    destruct d; eauto. intros isp. eapply isErasable_Proof in isp. eauto.
    eauto.

  - constructor.
    eapply All2_from_nth_error. now autorewrite with len.
    intros.
    unfold erase_mfix in H4.
    eapply nth_error_map_In in H4 as [a [Hnth [wt eq]]].
    subst. rewrite Hnth in H3. noconf H3.
    simpl. intuition auto.
    eapply nth_error_all in X1; eauto. simpl in X1.
    intuition auto.
  
  - constructor.
    eapply All2_from_nth_error. now autorewrite with len.
    intros.
    unfold erase_mfix in H4.
    eapply nth_error_map_In in H4 as [a [Hnth [wt eq]]].
    subst. rewrite Hnth in H3. noconf H3.
    simpl. intuition auto.
    eapply nth_error_all in X1; eauto. simpl in X1.
    intuition auto.
Qed.

Transparent wf_reduction.

Definition optM {M : Type -> Type} `{Monad M} {A B} (x : option A) (f : A -> M B) : M (option B) :=
  match x with
  | Some x => y <- f x ;; ret (Some y)
  | None => ret None
  end.

Lemma wf_local_nil {Σ} : ∥ wf_local Σ [] ∥.
Proof. repeat econstructor. Qed.

          


Require Import MSetList OrderedTypeAlt OrderedTypeEx.

Definition compare_ident := string_compare.

Require Import Lia.

Module IdentComp <: OrderedTypeAlt.
  Definition t := string.

  Definition eq := @eq string.
  Definition eq_univ : RelationClasses.Equivalence eq := _.

  Definition compare := string_compare.

  Infix "?=" := compare (at level 70, no associativity).

  Lemma compare_sym : forall x y, (y ?= x) = CompOpp (x ?= y).
  Proof.
    induction x; destruct y; simpl; auto;
    destruct (ascii_compare a0 a) eqn:eq.
    apply ascii_Compare_eq in eq; subst a0.
    destruct (ascii_compare a a) eqn:eq'.
    apply ascii_Compare_eq in eq'. apply IHx.
    simpl.
  Admitted.
 
  Lemma compare_trans :
    forall c x y z, (x?=y) = c -> (y?=z) = c -> (x?=z) = c.
  Proof.
    intros c x y z. revert c.
    induction x in y, z |- *; destruct y, z; intros c; simpl; auto; try congruence.
    unfold compare_ident.
  Admitted.

End IdentComp.

Module IdentOT := OrderedType_from_Alt IdentComp.

Module DirPathComp <: OrderedTypeAlt.
  Definition t := dirpath.

  Definition eq := @eq dirpath.
  Definition eq_univ : RelationClasses.Equivalence eq := _.

  Fixpoint compare dp dp' :=
    match dp, dp' with
    | hd :: tl, hd' :: tl' => 
      match IdentComp.compare hd hd' with
      | Eq => compare tl tl'
      | x => x
      end
    | [], [] => Eq
    | [], _ => Lt
    | _, [] => Gt
    end.

  Infix "?=" := compare (at level 70, no associativity).

  Lemma compare_sym : forall x y, (y ?= x) = CompOpp (x ?= y).
  Proof.
    induction x; destruct y; simpl; auto.
    unfold compare_ident.
    rewrite IdentComp.compare_sym.
    destruct (IdentComp.compare a s); simpl; auto.
  Qed.
 
  Lemma compare_trans :
    forall c x y z, (x?=y) = c -> (y?=z) = c -> (x?=z) = c.
  Proof.
    intros c x y z. revert c.
    induction x in y, z |- *; destruct y, z; intros c; simpl; auto; try congruence.
    unfold compare_ident.
    destruct (IdentComp.compare a s) eqn:eqc;
    destruct (IdentComp.compare s s0) eqn:eqc'; simpl; try congruence;
    try rewrite (IdentComp.compare_trans _ _ _ _ eqc eqc'); auto.
    apply IHx.
    intros; subst. rewrite <- H0.
    unfold IdentComp.compare in *.
    destruct (string_compare s s0);
    destruct (string_compare a s); try congruence.
    destruct (string_compare a s0); try congruence.
  Admitted.

End DirPathComp.

Module DirPathOT := OrderedType_from_Alt DirPathComp.
Require Import ssreflect.
Print DirPathOT.compare.

(* Eval compute in DirPathComp.compare ["foo"; "bar"] ["baz"].
 *)

Module ModPathComp.
  Definition t := modpath.

  Definition eq := @eq modpath.
  Definition eq_univ : RelationClasses.Equivalence eq := _.

  Fixpoint compare mp mp' :=
    match mp, mp' with
    | MPfile dp, MPfile dp' => DirPathComp.compare dp dp'
    | MPbound dp id k, MPbound dp' id' k' => 
      if DirPathComp.compare dp dp' is Eq then
        if IdentComp.compare id id' is Eq then
          Nat.compare k k'
        else IdentComp.compare id id'
      else DirPathComp.compare dp dp'
    | MPdot mp id, MPdot mp' id' => 
      if compare mp mp' is Eq then
        IdentComp.compare id id'
      else compare mp mp'
    | MPfile _, _ => Gt
    | _, MPfile _ => Lt
    | MPbound _ _ _, _ => Gt
    | _, MPbound _ _ _ => Lt
    end.

  Infix "?=" := compare (at level 70, no associativity).

  Lemma compare_sym : forall x y, (y ?= x) = CompOpp (x ?= y).
  Proof.
    induction x; destruct y; simpl; auto.
    unfold compare_ident.
  Admitted.          
 
  Lemma compare_trans :
    forall c x y z, (x?=y) = c -> (y?=z) = c -> (x?=z) = c.
  Proof.
  Admitted.

End ModPathComp.

Module ModPathOT := OrderedType_from_Alt ModPathComp.

Module KernameComp.
  Definition t := kername.

  Definition eq := @eq kername.
  Lemma eq_equiv : RelationClasses.Equivalence eq.
  Proof. apply _. Qed.

  Definition compare kn kn' := 
    match kn, kn' with
    | (mp, id), (mp', id') => 
      if ModPathComp.compare mp mp' is Eq then
        IdentComp.compare id id'
      else ModPathComp.compare mp mp'
    end.

  Infix "?=" := compare (at level 70, no associativity).

  Lemma compare_sym : forall x y, (y ?= x) = CompOpp (x ?= y).
  Proof.
    induction x; destruct y; simpl; auto.
    unfold compare_ident.
  Admitted.          
 
  Lemma compare_trans :
    forall c x y z, (x?=y) = c -> (y?=z) = c -> (x?=z) = c.
  Proof.
  Admitted.

End KernameComp.

Module KernameOT.
 Include KernameComp.
 Module OT := OrderedType_from_Alt KernameComp.

 Definition lt := OT.lt.
 Global Instance lt_strorder : StrictOrder OT.lt.
  Proof.
    constructor.
    - intros x X; admit.
    - intros x y z X1 X2. admit.
  Admitted.

  Definition lt_compat : Proper (eq ==> eq ==> iff) OT.lt.
    intros x x' H1 y y' H2.
  Admitted.

  Definition compare_spec : forall x y, CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
  Proof.
    induction x; destruct y.
    simpl. 
    destruct (ModPathComp.compare a m) eqn:eq.
    destruct (IdentComp.compare b i) eqn:eq'.
    all:constructor; todo "compare".
  Defined.

  Definition eq_dec : forall x y, {eq x y} + {~ eq x y}.
  Proof.
    intros k k'. destruct (PCUICReflect.eqb_spec k k').
    left; auto. right; auto.
  Defined.

End KernameOT.

Eval compute in KernameOT.compare (MPfile ["fdejrkjl"], "A") (MPfile ["lfrk;k"], "B").

  
Module KernameSet := MSetList.Make KernameOT.
(* Module KernameSetFact := WFactsOn Kername KernameSet.
Module KernameSetProp := WPropertiesOn Kername KernameSet. *)
  
Fixpoint term_global_deps (t : EAst.term) :=
  match t with
  | EAst.tConst kn
  | EAst.tConstruct {| inductive_mind := kn |} _ => KernameSet.singleton kn
  | EAst.tLambda _ x => term_global_deps x
  | EAst.tApp x y
  | EAst.tLetIn _ x y => KernameSet.union (term_global_deps x) (term_global_deps y)
  | EAst.tCase ({| inductive_mind := kn |}, _) x brs =>
    KernameSet.union (KernameSet.singleton kn) 
      (List.fold_left (fun acc x => KernameSet.union (term_global_deps (snd x)) acc) brs 
        (term_global_deps x))
   | EAst.tFix mfix _ | EAst.tCoFix mfix _ =>
     List.fold_left (fun acc x => KernameSet.union (term_global_deps (EAst.dbody x)) acc) mfix
      KernameSet.empty
  | _ => KernameSet.empty
  end.

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
  let ctors := map (A:=(ident * term) * nat) (fun '((x, y), z) => (x, EAst.tBox, z)) oib.(ind_ctors) in
  let projs := map (fun '(x, y) => (x, EAst.tBox)) oib.(ind_projs) in
  {| E.ind_name := oib.(ind_name);
     E.ind_kelim := oib.(ind_kelim);
     E.ind_ctors := ctors;
     E.ind_projs := projs |}.

Definition erase_mutual_inductive_body (mib : mutual_inductive_body) : E.mutual_inductive_body :=
  let bds := mib.(ind_bodies) in
  let arities := arities_context bds in
  let bodies := map erase_one_inductive_body bds in
  {| E.ind_npars := mib.(ind_npars);
     E.ind_bodies := bodies; |}.

Program Fixpoint erase_global_decls (deps : KernameSet.t) Σ : ∥ wf Σ ∥ -> E.global_declarations := fun wfΣ =>
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
Defined.
Next Obligation.
  sq.
  inv X. apply X1.
Qed.
Next Obligation.
  sq. inv X. apply X0.
Qed.

Next Obligation.
  sq. eapply PCUICWeakeningEnv.wf_extends. eauto. eexists [_]; reflexivity.
Qed.
Next Obligation.
  sq. eapply PCUICWeakeningEnv.wf_extends. eauto. eexists [_]; reflexivity.
Qed.
Next Obligation.
  sq. eapply PCUICWeakeningEnv.wf_extends. eauto. eexists [_]; reflexivity.
Qed.

Program Definition erase_global deps Σ : ∥wf Σ∥ -> _:=
  fun wfΣ  => erase_global_decls deps Σ wfΣ.

Lemma erase_global_correct deps Σ (wfΣ : ∥ wf Σ∥) :
  erases_global Σ (erase_global deps Σ wfΣ).
Proof.
  induction Σ in wfΣ |- *; intros; sq.
  - simpl. constructor.
  - destruct a as [kn [|]]; simpl.
    destruct KernameSet.mem => //.
(*
    constructor.
    + simpl.
      destruct c as [na [b|] ty]; simpl.
      apply erases_erase. constructor.  
    + apply IHΣ.
    + red. simpl.
      eapply (erases_global_ind _ (ind_universes m)).
      inv w. red in X0.
      destruct m; simpl; intuition; try constructor. all:simpl; auto.
      eapply All2_Forall2.
      eapply All2_from_nth_error.
      now autorewrite with len.
      intros.
      rewrite nth_error_map H0 /= in H2. noconf H2.
     red. simpl.
      destruct X0; simpl in *.
      eapply Alli_nth_error in onInductives; eauto.
      destruct onInductives. rewrite ind_arity_eq /=.
      rewrite decompose_prod_n_assum_it_mkProd /=.
      intuition auto.
      rewrite -{1}(map_id (ind_ctors x1)).
      eapply Forall2_map.
      eapply All2_Forall2.
      red in onConstructors.
      eapply All2_from_nth_error; auto. intros.
      rewrite H4 in H5; noconf H5.
      eapply All2_nth_error_Some in onConstructors; eauto.
      destruct onConstructors as [cshape [Hnth onc]].
      destruct onc ; simpl in *.
      destruct x0 as [[id ty] nargs]; intuition auto.
      constructor. eapply isType_isErasable.
      simpl in on_ctype. red in on_ctype. eapply on_ctype.
      rewrite -{1}(map_id (ind_projs x1)).
      eapply All2_Forall2. eapply All2_map.
      eapply All2_from_nth_error; auto. intros.
      rewrite H4 in H5; noconf H5.
      forward onProjections.
      destruct (ind_projs x1); simpl in *; try congruence. lia.
      destruct ind_cshapes; simpl in *.
      destruct onProjections. destruct ind_cshapes => //.
      destruct x0 as [id ty]. intuition auto.
      constructor.
      eapply isType_isErasable.
      todo "erasure of projection types".
      apply IHΣ.
      *)
Admitted.
