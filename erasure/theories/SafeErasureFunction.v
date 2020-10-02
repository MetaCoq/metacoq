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

Derive Signature for on_global_env.

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
  
  Lemma All2_In_right {A B} (P : A -> B -> Type) l l' x' : In x' l' -> 
    All2 P l l' -> ∥ ∑ x, P x x' ∥.
  Proof.
    induction 2; simpl in H => //.
    destruct H as [-> | H].
    constructor. now exists x.
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
(*Module KernameSetFact := WFactsOn Kername KernameSet.
Module KernameSetProp := WPropertiesOn Kername KernameSet.*)
  
Fixpoint term_global_deps (t : EAst.term) :=
  match t with
  | EAst.tConst kn
  | EAst.tConstruct {| inductive_mind := kn |} _ => KernameSet.singleton kn
  | EAst.tLambda _ x => term_global_deps x
  | EAst.tApp x y
  | EAst.tLetIn _ x y => KernameSet.union (term_global_deps x) (term_global_deps y)
  | EAst.tCase (ind, _) x brs =>
    KernameSet.union (KernameSet.singleton (inductive_mind ind)) 
      (List.fold_left (fun acc x => KernameSet.union (term_global_deps (snd x)) acc) brs 
        (term_global_deps x))
   | EAst.tFix mfix _ | EAst.tCoFix mfix _ =>
     List.fold_left (fun acc x => KernameSet.union (term_global_deps (EAst.dbody x)) acc) mfix
      KernameSet.empty
  | EAst.tProj p c => 
    KernameSet.union (KernameSet.singleton (inductive_mind (fst (fst p))))
      (term_global_deps c)
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
  let ctors := map (A:=(ident * term) * nat) (fun '((x, y), z) => (x, z)) oib.(ind_ctors) in
  let projs := map (fun '(x, y) => x) oib.(ind_projs) in
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

From MetaCoq.Erasure Require Import EDeps.
Lemma lookup_env_nil c s : lookup_env [] c = Some s -> False.
Proof.
  induction c; simpl; auto => //.
Qed.

Definition global_erased_with_deps Σ Σ' kn :=
  (exists cst, declared_constant Σ kn cst /\
   exists cst' : EAst.constant_body,
    ETyping.declared_constant Σ' kn cst' /\
    erases_constant_body (Σ, cst_universes cst) cst cst' /\
    (forall body : EAst.term,
     EAst.cst_body cst' = Some body -> erases_deps Σ Σ' body)) \/
  (exists mib, declared_minductive Σ kn mib).

Definition includes_deps Σ Σ' deps :=  
  forall kn, 
    KernameSet.In kn deps ->
    global_erased_with_deps Σ Σ' kn.

Lemma includes_deps_union Σ Σ' deps deps' :
  includes_deps Σ Σ' (KernameSet.union deps deps') ->
  includes_deps Σ Σ' deps /\ includes_deps Σ Σ' deps'.
Proof.
  intros.
  split; intros kn knin; eapply H; rewrite KernameSet.union_spec; eauto.
Qed.

Lemma in_fold_left {A} kn f (l : list A) acc : 
  KernameSet.In kn (fold_left (fun acc x => KernameSet.union (f x) acc) l acc) <->
  (KernameSet.In kn acc \/ exists a, In a l /\ KernameSet.In kn (f a)).
Proof.
  induction l in acc |- *; simpl. intuition auto.
  now destruct H0.
  rewrite IHl. rewrite KernameSet.union_spec.
  intuition auto.
  right. now exists a.
  destruct H0 as [a' [ina inkn]].
  right. now exists a'.
  destruct H0 as [a' [ina inkn]].
  destruct ina as [<-|ina'];
  intuition auto. right. now exists a'.
Qed.

Lemma includes_deps_fold {A} Σ Σ' brs deps (f : A -> EAst.term) :
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
  rewrite in_fold_left. left; auto.
  intros br brin. intros kn knin. apply incl.
  rewrite in_fold_left. right.
  now exists br.
Qed.

Lemma In_Forall {A} {P : A -> Prop} l : 
  (forall x, In x l -> P x) ->
  Forall P l.
Proof.
  intros H; induction l; constructor; auto.
  now apply H; simpl. apply IHl.
  intros x xin; apply H; simpl; auto.
Qed.

Lemma Forall2_All2 {A B} {P : A -> B -> Prop} l l' : Forall2 P l l' -> All2 P l l'.
Proof.
  intros f; induction l in l', f |- *; destruct l'; try constructor; auto.
  elimtype False. inv f.
  elimtype False. inv f.
  inv f; auto.
  apply IHl. inv f; auto.
Qed.

Definition declared_kn Σ kn :=
  ∥ ∑ decl, lookup_env Σ kn = Some decl ∥.

Lemma term_global_deps_spec {cf:checker_flags} {Σ Γ t et T} : 
  wf Σ.1 ->
  Σ ;;; Γ |- t : T ->
  Σ;;; Γ |- t ⇝ℇ et ->
  forall x, KernameSet.In x (term_global_deps et) -> declared_kn Σ.1 x.
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
    destruct d as [[H _] _]. red in H. simpl in *.
    red. sq. rewrite H. intuition eauto.
  - apply inversion_Case in wt
      as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?); eauto.
    destruct ind as [kn i']; simpl in *.
    eapply KernameSet.singleton_spec in H1; subst.
    destruct d as [d _]. red in d.
    simpl in *. eexists; intuition eauto.

  - apply inversion_Case in wt
    as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?); eauto.
    eapply in_fold_left in H1.
    destruct H1. eapply IHer; eauto.
    destruct H1 as [br [inbr inkn]].
    eapply Forall2_All2 in H0.
    assert (All (fun br => ∑ T, Σ ;;; Γ |- br.2 : T) brs).
    eapply All2_All_left. eapply a.
    simpl. intuition auto. eexists ; eauto.
    eapply All2_All_mix_left in H0; eauto. simpl in H0.
    eapply All2_In_right in H0; eauto.
    destruct H0.
    destruct X1 as [br' [[T' HT] ?]].
    eauto.

  - eapply KernameSet.singleton_spec in H0; subst.
    apply inversion_Proj in wt as (?&?&?&?&?&?&?&?&?); eauto.
    destruct d as [[d _] _]. red in d. eexists; eauto.

  - apply inversion_Proj in wt as (?&?&?&?&?&?&?&?&?); eauto.

  - apply inversion_Fix in wt as (?&?&?&?&?&?&?); eauto.
    eapply in_fold_left in hin as [|].
    now eapply KernameSet.empty_spec in H0.
    destruct H0 as [? [ina indeps]].
    eapply Forall2_All2 in H.
    eapply All2_All_mix_left in H; eauto.
    eapply All2_In_right in H; eauto.
    destruct H as [[def [[Hty _] Hdef]]].
    eapply Hdef; eauto.

  - apply inversion_CoFix in wt as (?&?&?&?&?&?&?); eauto.
    eapply in_fold_left in hin as [|].
    now eapply KernameSet.empty_spec in H0.
    destruct H0 as [? [ina indeps]].
    eapply Forall2_All2 in H.
    eapply All2_All_mix_left in H; eauto.
    eapply All2_In_right in H; eauto.
    destruct H as [[def [Hty Hdef]]].
    eapply Hdef; eauto.
Qed.

Lemma erase_global_erases_deps {Σ Σ' t et T} : 
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
    pose proof (PCUICWeakeningEnv.declared_constant_inj _ _ d declc'). subst x.
    now econstructor; eauto.
    destruct H as [mib declm].
    red in declm, d. rewrite d in declm. noconf declm.
  - apply inversion_Case in wt
      as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?); eauto.
    destruct ind as [kn i']; simpl in *.
    apply includes_deps_fold in H2 as [? ?].
    eapply erases_deps_tCase; eauto.
    eapply In_Forall in H3.
    eapply All_Forall. eapply Forall_All in H3.
    eapply Forall2_All2 in H0.
    eapply All2_All_mix_right in H0; eauto.
    assert (All (fun br => ∑ T, Σ ;;; Γ |- br.2 : T) brs).
    eapply All2_All_left. eapply a.
    simpl. intuition auto. eexists ; eauto.
    ELiftSubst.solve_all. destruct a2 as [T' HT]. eauto.

  - apply inversion_Proj in wt as (?&?&?&?&?&?&?&?&?); eauto.
    constructor.
    now eapply IHer; eauto.
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

From MetaCoq.PCUIC Require Import PCUICReflect PCUICWeakeningEnv.
Lemma lookup_env_cons {kn d Σ kn' d'} : lookup_env ((kn, d) :: Σ) kn' = Some d' ->
  (kn = kn' /\ d = d') \/ (kn <> kn' /\ lookup_env Σ kn' = Some d').
Proof.
  simpl.
  epose proof (eqb_spec (A:=kername) kn' kn). simpl in H.
  elim: H. intros -> [= <-]; intuition auto.
  intros diff look. intuition auto.
Qed.

Lemma lookup_env_cons_fresh {kn d Σ kn'} : 
  kn <> kn' ->
  lookup_env ((kn, d) :: Σ) kn' = lookup_env Σ kn'.
Proof.
  simpl.
  epose proof (eqb_spec (A:=kername) kn' kn). simpl in H.
  elim: H. intros -> => //. auto.
Qed.

Lemma elookup_env_cons_fresh {kn d Σ kn'} : 
  kn <> kn' ->
  ETyping.lookup_env ((kn, d) :: Σ) kn' = ETyping.lookup_env Σ kn'.
Proof.
  simpl. destruct kername_eq_dec. subst => //. auto. 
Qed.

Lemma erases_weakeninv_env {Σ Σ' : global_env_ext} {Γ t t' T} :
  wf Σ -> wf Σ' -> extends Σ Σ' -> 
  Σ ;;; Γ |- t : T ->
  erases Σ Γ t t' -> erases (Σ'.1, Σ.2) Γ t t'.
Proof.
  intros wfΣ wfΣ' ext Hty.
  apply (env_prop_typing _ _ ESubstitution.erases_extends _ wfΣ _ _ _ Hty _ wfΣ' ext).
Qed.  
 
Lemma erases_deps_weaken kn d Σ Σ' t : 
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
  unfold ETyping.declared_constant. rewrite elookup_env_cons_fresh //.
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

  right. destruct H as [mib Hm].
  exists mib.
  red.
  rewrite lookup_env_cons_fresh //.
  inv wf.
  { eapply lookup_env_Some_fresh in Hm.
    intros <-; contradiction. }
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

  right. destruct H as [mib Hm].
  exists mib.
  red.
  rewrite lookup_env_cons_fresh //.
  inv wf.
  { eapply lookup_env_Some_fresh in Hm.
    intros <-; contradiction. }
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
  PA.cst_type := name;
  PA.cst_body := Some bod;
  PA.cst_universes := univs |} onc bod eq_refl)). clearbody obl.
  destruct obl. sq.
  exists bod, A; intuition auto. simpl.
  eapply erases_erase. now simpl in H.
Qed.

Lemma erase_global_includes Σ deps deps' wfΣ :
  (forall d, KernameSet.In d deps' -> ∥ ∑ decl, lookup_env Σ d = Some decl ∥) ->
  KernameSet.subset deps' deps ->
  includes_deps Σ (erase_global deps Σ wfΣ) deps'.
Proof.
  sq.
  induction Σ in deps, deps', w |- *; simpl; intros H.
  - intros sub i hin. elimtype False.
    specialize (H i hin) as [[decl Hdecl]]. noconf Hdecl.
  - intros sub i hin.
    destruct a as [kn d].
    eapply KernameSet.subset_spec in sub.
    destruct (H i hin) as [[decl Hdecl]].
    pose proof (eqb_spec i kn). simpl in H0.
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
      depelim w. auto. eauto. eauto.
      eapply IHΣ.

      intros d ind.
      eapply term_global_deps_spec in Hebod; eauto.
      eapply KernameSet.subset_spec.
      intros x hin'. eapply KernameSet.union_spec. right; auto.
      congruence. congruence.
      eexists; red; intuition eauto.
      simpl. rewrite eq_kername_refl. reflexivity.
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

Lemma erase_correct (Σ : global_env_ext) (wfΣ : wf_ext Σ) t T v Σ' t' :
  axiom_free Σ.1 ->
  forall wt : Σ ;;; [] |- t : T,
  erase Σ (sq wfΣ) [] t (iswelltyped wt) = t' ->
  erase_global (term_global_deps t') Σ (sq (wfΣ.1)) = Σ' ->
  Σ |-p t ▷ v -> 
  exists v', Σ;;; [] |- v ⇝ℇ v' /\ ∥Σ' ⊢ t' ▷ v'∥.
Proof.
  intros axiomfree wt.
  generalize (iswelltyped wt).
  generalize (sq wfΣ.1) as swfΣ.
  intros swfΣ wt' HΣ' Ht' ev.
  assert (extraction_pre Σ) by now constructor.
  pose proof (erases_erase (wfΣ := sq wfΣ) wt'); eauto.
  rewrite HΣ' in H.
  unshelve epose proof (erase_global_erases_deps wfΣ wt H _); cycle 2.
  eapply erases_correct; eauto.
  rewrite <- Ht'.
  eapply erase_global_includes.
  intros. 2:eapply KernameSet.subset_spec; intros ? ?; auto.
  eapply term_global_deps_spec in H; eauto.
Qed.
