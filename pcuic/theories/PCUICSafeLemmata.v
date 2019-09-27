(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia
     Classes.CRelationClasses Omega ProofIrrelevance.
From MetaCoq.Template Require Import config Universes monad_utils utils BasicAst
     AstUtils UnivSubst.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICReflect PCUICLiftSubst PCUICUnivSubst PCUICTyping
     PCUICCumulativity PCUICSR PCUICPosition PCUICEquality PCUICNameless
     PCUICAlpha PCUICNormal PCUICInversion PCUICCumulativity PCUICReduction
     PCUICConfluence PCUICConversion PCUICContextConversion PCUICValidity
     PCUICParallelReductionConfluence PCUICWeakeningEnv
     PCUICClosed PCUICPrincipality PCUICSubstitution
     PCUICWeakening PCUICGeneration.

From Equations Require Import Equations.

Require Import Equations.Prop.DepElim.
Require Import Equations.Type.Relation_Properties.
Derive Signature for red.
Import MonadNotation.

Local Set Keyed Unification.
Set Equations With UIP.

Arguments sq {_} _.

Notation "( x ; y )" := (existT _ x y).

Ltac rdestruct H :=
  match type of H with
  | _ /\ _ => let H' := fresh H in
            destruct H as [H H']; rdestruct H; rdestruct H'
  | _ × _ => let H' := fresh H in
            destruct H as [H H']; rdestruct H; rdestruct H'
  | sigT _ => let H' := fresh H in
             destruct H as [H H']; rdestruct H; rdestruct H'
  | _ => idtac
  end.


Definition nodelta_flags := RedFlags.mk true true true false true true.


(* Dependent lexicographic order *)
Inductive dlexprod {A} {B : A -> Type}
          (leA : A -> A -> Prop) (leB : forall x, B x -> B x -> Prop)
  : sigT B -> sigT B -> Prop :=
| left_lex :
    forall x x' y y',
      leA x x' ->
      dlexprod leA leB (x;y) (x';y')

| right_lex :
    forall x y y',
      leB x y y' ->
      dlexprod leA leB (x;y) (x;y').

Derive Signature for dlexprod.

Definition lexprod := Subterm.lexprod.
Arguments lexprod {_ _} _ _ _ _.

(* Dependent lexicographic order modulo another relation *)
Inductive dlexmod {A} {B : A -> Type}
    (leA : A -> A -> Prop)
    (eA : A -> A -> Prop)
    (coe : forall x x', eA x x' -> B x -> B x')
    (leB : forall x, B x -> B x -> Prop)
  : sigT B -> sigT B -> Prop :=
| left_dlexmod :
    forall x x' y y',
      leA x x' ->
      dlexmod leA eA coe leB (x;y) (x';y')

| right_dlexmod :
    forall x x' y y' (e : eA x x'),
      leB x' (coe _ _ e y) y' ->
      dlexmod leA eA coe leB (x;y) (x';y').

Notation "x ⊩ R1 ⨶ R2" :=
  (dlexprod R1 (fun x => R2)) (at level 20, right associativity).
Notation "R1 ⊗ R2" :=
  (lexprod R1 R2) (at level 20, right associativity).

Notation "x ⊨ e \ R1 'by' coe ⨷ R2" :=
  (dlexmod R1 e coe (fun x => R2)) (at level 20, right associativity).

Lemma acc_dlexprod :
  forall A B leA leB,
    (forall x, well_founded (leB x)) ->
    forall x,
      Acc leA x ->
      forall y,
        Acc (leB x) y ->
        Acc (@dlexprod A B leA leB) (x;y).
Proof.
  intros A B leA leB hw.
  induction 1 as [x hx ih1].
  intros y.
  induction 1 as [y hy ih2].
  constructor.
  intros [x' y'] h. simple inversion h.
  - intro hA. inversion H0. inversion H1. subst.
    eapply ih1.
    + assumption.
    + apply hw.
  - intro hB. rewrite <- H0.
    pose proof (projT2_eq H1) as p2.
    set (projT1_eq H1) as p1 in *; cbn in p1.
    destruct p1; cbn in p2; destruct p2.
    eapply ih2. assumption.
Qed.

Lemma dlexprod_Acc :
  forall A B leA leB,
    (forall x, well_founded (leB x)) ->
    forall x y,
      Acc leA x ->
      Acc (@dlexprod A B leA leB) (x;y).
Proof.
  intros A B leA leB hB x y hA.
  eapply acc_dlexprod ; try assumption.
  apply hB.
Qed.

Lemma dlexprod_trans :
  forall A B RA RB,
    transitive RA ->
    (forall x, transitive (RB x)) ->
    transitive (@dlexprod A B RA RB).
Proof.
  intros A B RA RB hA hB [u1 u2] [v1 v2] [w1 w2] h1 h2.
  revert w1 w2 h2. induction h1 ; intros w1 w2 h2.
  - dependent induction h2.
    + left. eapply hA ; eassumption.
    + left. assumption.
  - dependent induction h2.
    + left. assumption.
    + right. eapply hB ; eassumption.
Qed.

Derive Signature for dlexmod.

Lemma acc_dlexmod :
  forall A B (leA : A -> A -> Prop) (eA : A -> A -> Prop)
        (coe : forall x x', eA x x' -> B x -> B x')
        (leB : forall x : A, B x -> B x -> Prop)
        (sym : forall x y, eA x y -> eA y x)
        (trans : forall x y z, eA x y -> eA y z -> eA x z),
    (forall x, well_founded (leB x)) ->
    (forall x x' y, eA x x' -> leA y x' -> leA y x) ->
    (forall x, exists e : eA x x, forall y, coe _ _ e y = y) ->
    (forall x x' y e, coe x x' (sym _ _ e) (coe _ _ e y) = y) ->
    (forall x0 x1 x2 e1 e2 y,
      coe _ _ (trans x0 x1 x2 e1 e2) y =
      coe _ _ e2 (coe _ _ e1 y)
    ) ->
    (forall x x' e y y',
      leB _ y (coe x x' e y') ->
      leB _ (coe _ _ (sym _ _ e) y) y'
    ) ->
    forall x,
      Acc leA x ->
      forall y,
        Acc (leB x) y ->
        forall x' (e : eA x x'),
          Acc (@dlexmod A B leA eA coe leB) (x'; coe _ _ e y).
Proof.
  intros A B leA eA coe leB sym trans hw hA hcoe coesym coetrans lesym.
  induction 1 as [x hx ih1].
  induction 1 as [y hy ih2].
  intros x' e.
  constructor.
  intros [x'' y''] h. dependent destruction h.
  - specialize (hcoe x'') as [e' he'].
    rewrite <- (he' y'').
    eapply ih1.
    + eapply hA. all: eauto.
    + apply hw.
  - simpl in *.
    specialize ih2 with (x' := x'').
    set (e2 := trans _ _ _ e0 (sym _ _ e)).
    set (e1 := sym _ _ e2).
    replace y'' with (coe _ _ e1 (coe _ _ e2 y''))
      by eauto using coesym.
    eapply ih2.
    rewrite coetrans.
    eapply lesym.
    assumption.
Qed.

Lemma dlexmod_Acc :
  forall A B (leA : A -> A -> Prop) (eA : A -> A -> Prop)
    (coe : forall x x', eA x x' -> B x -> B x')
    (leB : forall x : A, B x -> B x -> Prop)
    (sym : forall x y, eA x y -> eA y x)
    (trans : forall x y z, eA x y -> eA y z -> eA x z),
    (forall x, well_founded (leB x)) ->
    (forall x x' y, eA x x' -> leA y x' -> leA y x) ->
    (forall x, exists e : eA x x, forall y, coe _ _ e y = y) ->
    (forall x x' y e, coe x x' (sym _ _ e) (coe _ _ e y) = y) ->
    (forall x0 x1 x2 e1 e2 y,
      coe _ _ (trans x0 x1 x2 e1 e2) y =
      coe _ _ e2 (coe _ _ e1 y)
    ) ->
    (forall x x' e y y',
      leB _ y (coe x x' e y') ->
      leB _ (coe _ _ (sym _ _ e) y) y'
    ) ->
    forall x y,
      Acc leA x ->
      Acc (@dlexmod A B leA eA coe leB) (x ; y).
Proof.
  intros A B leA eA coe leB sym trans hB ? hcoe ? ? ? x y h.
  specialize (hcoe x) as h'. destruct h' as [e he].
  rewrite <- (he y).
  eapply acc_dlexmod. all: eauto.
  apply hB.
Qed.

Section Lemmata.
  Context {cf : checker_flags}.
  Context (flags : RedFlags.t).

  Lemma eq_term_zipc_inv :
    forall φ u v π,
      eq_term φ (zipc u π) (zipc v π) ->
      eq_term φ u v.
  Proof.
    intros Σ u v π h.
    revert u v h. induction π ; intros u v h.
    all: solve [
             simpl in h ; try apply IHπ in h ;
             cbn in h ; inversion h ; subst ; assumption
           ].
  Qed.

  Lemma eq_term_zipx_inv :
    forall φ Γ u v π,
      eq_term φ (zipx Γ u π) (zipx Γ v π) ->
      eq_term φ u v.
  Proof.
    intros Σ Γ u v π h.
    eapply eq_term_zipc_inv.
    eapply eq_term_it_mkLambda_or_LetIn_inv.
    eassumption.
  Qed.

  Lemma eq_term_upto_univ_zipc :
    forall Re u v π,
      RelationClasses.Reflexive Re ->
      eq_term_upto_univ Re Re u v ->
      eq_term_upto_univ Re Re (zipc u π) (zipc v π).
  Proof.
    intros Re u v π he h.
    induction π in u, v, h |- *.
    all: try solve [
               simpl ; try apply IHπ ;
               cbn ; constructor ; try apply eq_term_upto_univ_refl ; assumption
             ].
    - assumption.
    - simpl. apply IHπ. destruct indn as [i n].
      constructor.
      + apply eq_term_upto_univ_refl. all: assumption.
      + assumption.
      + eapply All2_same.
        intros. split ; auto. apply eq_term_upto_univ_refl. all: assumption.
  Qed.

  Lemma eq_term_zipc :
    forall (Σ : global_env_ext) u v π,
      eq_term (global_ext_constraints Σ) u v ->
      eq_term (global_ext_constraints Σ) (zipc u π) (zipc v π).
  Proof.
    intros Σ u v π h.
    eapply eq_term_upto_univ_zipc.
    - intro. eapply eq_universe_refl.
    - assumption.
  Qed.

  Lemma eq_term_upto_univ_zipp :
    forall Re u v π,
      RelationClasses.Reflexive Re ->
      eq_term_upto_univ Re Re u v ->
      eq_term_upto_univ Re Re (zipp u π) (zipp v π).
  Proof.
    intros Re u v π he h.
    unfold zipp.
    case_eq (decompose_stack π). intros l ρ e.
    eapply eq_term_upto_univ_mkApps.
    - assumption.
    - apply All2_same. intro. reflexivity.
  Qed.

  Lemma eq_term_zipp :
    forall (Σ : global_env_ext) u v π,
      eq_term (global_ext_constraints Σ) u v ->
      eq_term (global_ext_constraints Σ) (zipp u π) (zipp v π).
  Proof.
    intros Σ u v π h.
    eapply eq_term_upto_univ_zipp.
    - intro. eapply eq_universe_refl.
    - assumption.
  Qed.

  Lemma eq_term_upto_univ_zipx :
    forall Re Γ u v π,
      RelationClasses.Reflexive Re ->
      eq_term_upto_univ Re Re u v ->
      eq_term_upto_univ Re Re (zipx Γ u π) (zipx Γ v π).
  Proof.
    intros Re Γ u v π he h.
    eapply eq_term_upto_univ_it_mkLambda_or_LetIn ; auto.
    eapply eq_term_upto_univ_zipc ; auto.
  Qed.

  Lemma eq_term_zipx :
    forall φ Γ u v π,
      eq_term φ u v ->
      eq_term φ (zipx Γ u π) (zipx Γ v π).
  Proof.
    intros Σ Γ u v π h.
    eapply eq_term_upto_univ_zipx ; auto.
    intro. eapply eq_universe_refl.
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

  Lemma lookup_env_ConstantDecl_inv :
    forall Σ k k' ty bo uni,
      Some (ConstantDecl k' {| cst_type := ty ; cst_body := bo; cst_universes := uni |})
      = lookup_env Σ k ->
      k = k'.
  Proof.
    intros Σ k k' ty bo uni h.
    induction Σ in h |- *.
    - cbn in h. discriminate.
    - cbn in h. destruct (ident_eq_spec k (global_decl_ident a)).
      + subst. inversion h. reflexivity.
      + apply IHΣ in h. assumption.
  Qed.

  Lemma fresh_global_nl :
    forall Σ k,
      fresh_global k Σ ->
      fresh_global k (map nl_global_decl Σ).
  Proof.
    intros Σ k h. eapply Forall_map.
    eapply Forall_impl ; try eassumption.
    intros x hh. cbn in hh.
    destruct x ; assumption.
  Qed.

  (* Lemma conv_context : *)
  (*   forall Σ Γ u v ρ, *)
  (*     wf Σ.1 -> *)
  (*     Σ ;;; Γ ,,, stack_context ρ |- u == v -> *)
  (*     Σ ;;; Γ |- zipc u ρ == zipc v ρ. *)
  (* Proof. *)
  (*   intros Σ Γ u v ρ hΣ h. *)
  (*   induction ρ in u, v, h |- *. *)
  (*   - assumption. *)
  (*   - simpl. eapply IHρ. eapply conv_App_l ; auto. *)
  (*   - simpl. eapply IHρ. eapply conv_App_r ; auto. *)
  (*   - simpl. eapply IHρ. eapply conv_App_r ; auto. *)
  (*   - simpl. eapply IHρ. eapply conv_Case_c ; auto. *)
  (*   - simpl. eapply IHρ. eapply conv_Proj_c ; auto. *)
  (*   - simpl. eapply IHρ. eapply conv_Prod_l ; auto. *)
  (*   - simpl. eapply IHρ. eapply conv_Prod_r ; auto. *)
  (*   - simpl. eapply IHρ. eapply conv_Lambda_l ; auto. *)
  (*   - simpl. eapply IHρ. eapply conv_Lambda_r ; auto. *)
  (*   - simpl. eapply IHρ. eapply conv_App_r ; auto. *)
  (* Qed. *)

  Context (Σ : global_env_ext).

  Inductive welltyped Σ Γ t : Prop :=
  | iswelltyped A : Σ ;;; Γ |- t : A -> welltyped Σ Γ t.

  Arguments iswelltyped {Σ Γ t A} h.

  Definition wellformed Σ Γ t :=
    welltyped Σ Γ t \/ ∥ isWfArity typing Σ Γ t ∥.

  (* Here we use use the proof irrelevance axiom to show that wellformed is really squashed.
     Using SProp would avoid this.
   *)

  Lemma wellformed_irr :
    forall {Σ Γ t} (h1 h2 : wellformed Σ Γ t), h1 = h2.
  Proof. intros. apply proof_irrelevance. Qed.

  Context (hΣ : ∥ wf Σ ∥).

  Lemma welltyped_alpha Γ u v :
      welltyped Σ Γ u ->
      eq_term_upto_univ eq eq u v ->
      welltyped Σ Γ v.
  Proof.
    intros [A h] e.
    destruct hΣ.
    exists A. eapply typing_alpha ; eauto.
  Qed.

  Lemma wellformed_alpha Γ u v :
      wellformed Σ Γ u ->
      eq_term_upto_univ eq eq u v ->
      wellformed Σ Γ v.
  Proof.
    destruct hΣ as [hΣ'].
    intros [X|X] e; [left|right].
    - destruct X as [A Hu]. eexists. eapply typing_alpha; tea.
    - destruct X. constructor.
      now eapply isWfArity_alpha.
  Qed.

  Lemma wellformed_nlctx Γ u :
      wellformed Σ Γ u ->
      wellformed Σ (nlctx Γ) u.
  Proof.
    destruct hΣ as [hΣ'].
    assert (Γ ≡Γ nlctx Γ) by apply upto_names_nlctx.
    intros [[A hu]|[[ctx [s [X1 X2]]]]]; [left|right].
    - exists A. eapply context_conversion'; tea.
      eapply wf_local_alpha with Γ; tea.
      now eapply typing_wf_local.
      now eapply upto_names_conv_context.
    - constructor. exists ctx, s. split; tas.
      eapply wf_local_alpha; tea.
      now eapply eq_context_upto_cat.
  Qed.


  Lemma red_cored_or_eq :
    forall Γ u v,
      red Σ Γ u v ->
      cored Σ Γ v u \/ u = v.
  Proof.
    intros Γ u v h.
    induction h.
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
      eapply sr_red1 ; eauto with wf.
    - specialize IHr with (1 := ltac:(eassumption)).
      destruct IHr as [A ?]. exists A.
      eapply sr_red1 ; eauto with wf.
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
    revert w h2. induction h1 ; intros w h2.
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

  Lemma welltyped_context :
    forall Γ t,
      welltyped Σ Γ (zip t) ->
      welltyped Σ (Γ ,,, stack_context (snd t)) (fst t).
  Proof.
    destruct hΣ as [wΣ].
    intros Γ [t π] h. simpl.
    destruct h as [T h].
    induction π in Γ, t, T, h |- *.
    - cbn. cbn in h. eexists. eassumption.
    - simpl. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [B h].
      apply inversion_App in h as hh ; auto.
      destruct hh as [na [A' [B' [? [? ?]]]]].
      eexists. eassumption.
    - simpl. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [B h].
      apply inversion_App in h as hh ; auto.
      destruct hh as [na [A' [B' [? [? ?]]]]].
      eexists. eassumption.
    - simpl. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [B h].
      apply inversion_App in h as hh ; auto.
      destruct hh as [na [A' [B' [? [? ?]]]]].
      eexists. eassumption.
    - simpl. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [B h].
      destruct indn.
      apply inversion_Case in h as hh ; auto.
      destruct hh
        as [uni [args [mdecl [idecl [pty [indctx [pctx [ps [btys [? [? [? [? [? [? [ht0 [? ?]]]]]]]]]]]]]]]]].
      eexists. eassumption.
    - simpl. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [T' h].
      apply inversion_Proj in h
        as [uni [mdecl [idecl [pdecl [args [? [? [? ?]]]]]]]] ; auto.
      eexists. eassumption.
    - simpl. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [T' h].
      apply inversion_Prod in h as hh ; auto.
      destruct hh as [s1 [s2 [? [? ?]]]].
      eexists. eassumption.
    - cbn. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [T' h].
      apply inversion_Prod in h as hh ; auto.
      destruct hh as [s1 [s2 [? [? ?]]]].
      eexists. eassumption.
    - cbn. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [T' h].
      apply inversion_Lambda in h as hh ; auto.
      destruct hh as [s1 [B [? [? ?]]]].
      eexists. eassumption.
    - cbn. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [T' h].
      apply inversion_Lambda in h as hh ; auto.
      destruct hh as [s1 [B [? [? ?]]]].
      eexists. eassumption.
    - cbn. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [B h].
      apply inversion_App in h as hh ; auto.
      destruct hh as [na [A' [B' [? [? ?]]]]].
      eexists. eassumption.
  Qed.

  Lemma wellformed_context :
    forall Γ t,
      wellformed Σ Γ (zip t) ->
      wellformed Σ (Γ ,,, stack_context (snd t)) (fst t).
  Proof.
    destruct hΣ as [wΣ].
    intros Γ [t π] [[A h]|h].
    - destruct (welltyped_context Γ (t, π) (iswelltyped h)) as [? ?].
      left. econstructor. eassumption.
    - induction π in t, h |- *.
      all: try (specialize (IHπ _ h)).
      all: simpl in *.
      1: right ; assumption.
      all: destruct IHπ as [[A' h'] | [[Δ [s [h1 h2]]]]] ; [| try discriminate].
      all: try solve [
        apply inversion_App in h' ; auto ;
        rdestruct h' ;
        left ; econstructor ; eassumption
      ].
      + destruct indn.
        apply inversion_Case in h' ; auto. cbn in h'. rdestruct h'.
        left. econstructor. eassumption.
      + apply inversion_Proj in h' ; auto.
        cbn in h'. rdestruct h'.
        left. eexists. eassumption.
      + apply inversion_Prod in h' ; auto. rdestruct h'.
        left. eexists. eassumption.
      + cbn in h1. apply destArity_app_Some in h1 as [Δ' [h1 h1']].
        subst. left. rewrite app_context_assoc in h2. cbn in *.
        apply wf_local_app in h2. inversion h2. subst. cbn in *.
        destruct X0. eexists. eassumption.
      + apply inversion_Prod in h' ; auto. rdestruct h'.
        left. eexists. eassumption.
      + cbn in h1. apply destArity_app_Some in h1 as [Δ' [h1 h1']].
        subst. right. constructor. exists Δ', s.
        rewrite app_context_assoc in h2. cbn in h2.
        split ; eauto.
      + apply inversion_Lambda in h' ; auto. rdestruct h'.
        left. eexists. eassumption.
      + apply inversion_Lambda in h' ; auto. rdestruct h'.
        left. eexists. eassumption.
  Qed.

  Lemma cored_red :
    forall Γ u v,
      cored Σ Γ v u ->
      ∥ red Σ Γ u v ∥.
  Proof.
    intros Γ u v h.
    induction h.
    - constructor. econstructor.
      + constructor.
      + assumption.
    - destruct IHh as [r].
      constructor. econstructor ; eassumption.
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

  Lemma cored_zipx :
    forall Γ u v π,
      cored Σ (Γ ,,, stack_context π) u v ->
      cored Σ [] (zipx Γ u π) (zipx Γ v π).
  Proof.
    intros Γ u v π h.
    eapply cored_it_mkLambda_or_LetIn.
    eapply cored_context.
    rewrite app_context_nil_l.
    assumption.
  Qed.

  Lemma red_zipx :
    forall Γ u v π,
      red Σ (Γ ,,, stack_context π) u v ->
      red Σ [] (zipx Γ u π) (zipx Γ v π).
  Proof.
    intros Γ u v π h.
    eapply red_it_mkLambda_or_LetIn.
    eapply red_context.
    rewrite app_context_nil_l.
    assumption.
  Qed.

  Lemma cumul_zippx :
    forall Γ u v ρ,
      Σ ;;; (Γ ,,, stack_context ρ) |- u <= v ->
      Σ ;;; Γ |- zippx u ρ <= zippx v ρ.
  Proof.
    intros Γ u v ρ h.
    revert u v h. induction ρ ; intros u v h.
    - cbn. assumption.
    - unfold zippx. simpl.
      case_eq (decompose_stack ρ). intros l π e.
      unfold zippx in IHρ. rewrite e in IHρ.
      apply IHρ.
      eapply cumul_App_l. assumption.
    - unfold zippx. simpl.
      eapply cumul_it_mkLambda_or_LetIn.
      assumption.
    - unfold zippx. simpl.
      eapply cumul_it_mkLambda_or_LetIn.
      assumption.
    - unfold zippx. simpl.
      eapply cumul_it_mkLambda_or_LetIn.
      assumption.
    - unfold zippx. simpl.
      eapply cumul_it_mkLambda_or_LetIn.
      assumption.
    - unfold zippx. simpl.
      eapply cumul_it_mkLambda_or_LetIn.
      assumption.
    - unfold zippx. simpl.
      eapply cumul_it_mkLambda_or_LetIn. cbn.
      eapply cumul_Lambda_r.
      assumption.
    - unfold zippx. simpl.
      eapply cumul_it_mkLambda_or_LetIn.
      assumption.
    - unfold zippx. simpl.
      eapply cumul_it_mkLambda_or_LetIn. cbn.
      eapply cumul_Lambda_r.
      assumption.
    - unfold zippx. simpl.
      eapply cumul_it_mkLambda_or_LetIn. assumption.
  Qed.

  Lemma conv_LetIn_bo :
    forall Γ na ty t u u',
      Σ ;;; Γ ,, vdef na ty t |- u == u' ->
      Σ ;;; Γ |- tLetIn na ty t u == tLetIn na ty t u'.
  Proof.
    intros Γ na ty t u u' h.
    induction h.
    - eapply conv_alt_refl. constructor.
      all: try eapply eq_term_refl.
      assumption.
    - eapply conv_alt_red_l ; try eassumption.
      econstructor. assumption.
    - eapply conv_alt_red_r ; try eassumption.
      econstructor. assumption.
  Qed.

  Lemma conv_alt_it_mkLambda_or_LetIn :
    forall Δ Γ u v,
      Σ ;;; (Δ ,,, Γ) |- u == v ->
      Σ ;;; Δ |- it_mkLambda_or_LetIn Γ u == it_mkLambda_or_LetIn Γ v.
  Proof.
    intros Δ Γ u v h. revert Δ u v h.
    induction Γ as [| [na [b|] A] Γ ih ] ; intros Δ u v h.
    - assumption.
    - simpl. cbn. eapply ih.
      eapply conv_LetIn_bo. assumption.
    - simpl. cbn. eapply ih.
      eapply conv_Lambda_r. assumption.
  Qed.

  Lemma conv_alt_it_mkProd_or_LetIn :
    forall Δ Γ B B',
      Σ ;;; (Δ ,,, Γ) |- B == B' ->
      Σ ;;; Δ |- it_mkProd_or_LetIn Γ B == it_mkProd_or_LetIn Γ B'.
  Proof.
    intros Δ Γ B B' h.
    induction Γ as [| [na [b|] A] Γ ih ] in Δ, B, B', h |- *.
    - assumption.
    - simpl. cbn. eapply ih.
      eapply conv_LetIn_bo. assumption.
    - simpl. cbn. eapply ih.
      eapply conv_Prod_r. assumption.
  Qed.

  Lemma conv_zipp :
    forall Γ u v ρ,
      Σ ;;; Γ |- u == v ->
      Σ ;;; Γ |- zipp u ρ == zipp v ρ.
  Proof.
    intros Γ u v ρ h.
    unfold zipp.
    destruct decompose_stack.
    induction l in u, v, h |- *.
    - assumption.
    - simpl.  eapply IHl. eapply conv_App_l. assumption.
  Qed.

  Lemma cumul_zipp :
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
  Qed.

  Lemma conv_zipp' :
    forall leq Γ u v π,
      conv leq Σ Γ u v ->
      conv leq Σ Γ (zipp u π) (zipp v π).
  Proof.
    intros leq Γ u v π h.
    destruct leq.
    - destruct h. constructor. eapply conv_zipp. assumption.
    - destruct h. constructor. eapply cumul_zipp. assumption.
  Qed.

  Lemma conv_alt_zippx :
    forall Γ u v ρ,
      Σ ;;; (Γ ,,, stack_context ρ) |- u == v ->
      Σ ;;; Γ |- zippx u ρ == zippx v ρ.
  Proof.
    intros Γ u v ρ h.
    revert u v h. induction ρ ; intros u v h.
    - cbn. assumption.
    - unfold zippx. simpl.
      case_eq (decompose_stack ρ). intros l π e.
      unfold zippx in IHρ. rewrite e in IHρ.
      apply IHρ.
      eapply conv_App_l. assumption.
    - unfold zippx. simpl.
      eapply conv_alt_it_mkLambda_or_LetIn.
      assumption.
    - unfold zippx. simpl.
      eapply conv_alt_it_mkLambda_or_LetIn.
      assumption.
    - unfold zippx. simpl.
      eapply conv_alt_it_mkLambda_or_LetIn.
      assumption.
    - unfold zippx. simpl.
      eapply conv_alt_it_mkLambda_or_LetIn.
      assumption.
    - unfold zippx. simpl.
      eapply conv_alt_it_mkLambda_or_LetIn.
      assumption.
    - unfold zippx. simpl.
      eapply conv_alt_it_mkLambda_or_LetIn. cbn.
      eapply conv_Lambda_r.
      assumption.
    - unfold zippx. simpl.
      eapply conv_alt_it_mkLambda_or_LetIn.
      assumption.
    - unfold zippx. simpl.
      eapply conv_alt_it_mkLambda_or_LetIn. cbn.
      eapply conv_Lambda_r.
      assumption.
    - unfold zippx. simpl.
      eapply conv_alt_it_mkLambda_or_LetIn. assumption.
  Qed.

  Lemma conv_zippx :
    forall Γ u v ρ,
      Σ ;;; Γ ,,, stack_context ρ |- u == v ->
      Σ ;;; Γ |- zippx u ρ == zippx v ρ.
  Proof.
    intros Γ u v ρ uv. eapply conv_alt_zippx ; assumption.
  Qed.

  Lemma conv_zippx' :
    forall Γ leq u v ρ,
      conv leq Σ (Γ ,,, stack_context ρ) u v ->
      conv leq Σ Γ (zippx u ρ) (zippx v ρ).
  Proof.
    intros Γ leq u v ρ h.
    destruct leq.
    - cbn in *. destruct h as [h]. constructor.
      eapply conv_alt_zippx ; assumption.
    - cbn in *. destruct h. constructor.
      eapply cumul_zippx. assumption.
  Qed.


  Lemma cored_nl :
    forall Γ u v,
      cored Σ Γ u v ->
      cored Σ (nlctx Γ) (nl u) (nl v).
  Proof.
    intros Γ u v H. induction H.
    - constructor 1. admit.
    - econstructor 2; tea. admit.
  Admitted.

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
    intros; split.
    apply welltyped_it_mkLambda_or_LetIn.
    apply it_mkLambda_or_LetIn_welltyped.
  Qed.

  Lemma isWfArity_it_mkLambda_or_LetIn :
    forall Γ Δ T,
      isWfArity typing Σ Γ (it_mkLambda_or_LetIn Δ T) ->
      isWfArity typing Σ (Γ ,,, Δ) T.
  Proof.
    intro Γ; induction Δ in Γ |- *; intro T; [easy|].
    destruct a as [na [bd|] ty].
    - simpl. cbn. intro HH. apply IHΔ in HH.
      destruct HH as [Δ' [s [HH HH']]].
      cbn in HH; apply destArity_app_Some in HH.
      destruct HH as [Δ'' [HH1 HH2]].
      exists Δ'', s. split; tas.
      refine (eq_rect _ (fun Γ => wf_local Σ Γ) HH' _ _).
      rewrite HH2. rewrite app_context_assoc. reflexivity.
    - simpl. cbn. intro HH. apply IHΔ in HH.
      destruct HH as [Δ' [s [HH HH']]]. discriminate.
  Qed.

  Lemma wellformed_it_mkLambda_or_LetIn :
    forall Γ Δ t,
      wellformed Σ Γ (it_mkLambda_or_LetIn Δ t) ->
      wellformed Σ (Γ ,,, Δ) t.
  Proof.
    intros Γ Δ t [Hwf|Hwf];
      [left; now apply welltyped_it_mkLambda_or_LetIn |
       right; destruct Hwf; constructor].
    now apply isWfArity_it_mkLambda_or_LetIn.
  Qed.


  Lemma wellformed_zipp :
    forall Γ t ρ,
      wellformed Σ Γ (zipp t ρ) ->
      wellformed Σ Γ t.
  Proof.
    destruct hΣ as [wΣ].
    intros Γ t ρ h.
    unfold zipp in h.
    case_eq (decompose_stack ρ). intros l π e.
    rewrite e in h. clear - h wΣ.
    destruct h as [[A h]|[h]].
    - left.
      induction l in t, A, h |- *.
      + eexists. eassumption.
      + apply IHl in h.
        destruct h as [T h].
        apply inversion_App in h as hh ; auto.
        rdestruct hh. econstructor. eassumption.
    - right. constructor. destruct l.
      + assumption.
      + destruct h as [ctx [s [h1 _]]].
        rewrite destArity_tApp in h1. discriminate.
  Qed.

  (* WRONG *)
  Lemma it_mkLambda_or_LetIn_wellformed :
    forall Γ Δ t,
      wellformed Σ (Γ ,,, Δ) t ->
      wellformed Σ Γ (it_mkLambda_or_LetIn Δ t).
  Abort.

  (* Wrong for t = alg univ, π = ε, Γ = vass A *)
  Lemma zipx_wellformed :
    forall {Γ t π},
      wellformed Σ Γ (zipc t π) ->
      wellformed Σ [] (zipx Γ t π).
  (* Proof. *)
  (*   intros Γ t π h. *)
  (*   eapply it_mkLambda_or_LetIn_wellformed. *)
  (*   rewrite app_context_nil_l. *)
  (*   assumption. *)
  (* Qed. *)
  Abort.

  Lemma wellformed_zipx :
    forall {Γ t π},
      wellformed Σ [] (zipx Γ t π) ->
      wellformed Σ Γ (zipc t π).
  Proof.
    intros Γ t π h.
    apply wellformed_it_mkLambda_or_LetIn in h.
    rewrite app_context_nil_l in h.
    assumption.
  Qed.

  Lemma wellformed_zipc_stack_context Γ t π ρ args
    : decompose_stack π = (args, ρ)
      -> wellformed Σ Γ (zipc t π)
      -> wellformed Σ (Γ ,,, stack_context π) (zipc t (appstack args ε)).
  Proof.
    intros h h1.
    apply decompose_stack_eq in h. subst.
    rewrite stack_context_appstack.
    induction args in Γ, t, ρ, h1 |- *.
    - cbn in *.
      now apply (wellformed_context Γ (t, ρ)).
    - simpl. eauto.
  Qed.

  (* Wrong  *)
  Lemma wellformed_zipc_zippx :
    forall Γ t π,
      wellformed Σ Γ (zipc t π) ->
      wellformed Σ Γ (zippx t π).
  (* Proof. *)
  (*   intros Γ t π h. *)
  (*   unfold zippx. *)
  (*   case_eq (decompose_stack π). intros l ρ e. *)
  (*   pose proof (decompose_stack_eq _ _ _ e). subst. clear e. *)
  (*   rewrite zipc_appstack in h. *)
  (*   zip fold in h. *)
  (*   apply wellformed_context in h ; simpl in h. *)
  (*   eapply it_mkLambda_or_LetIn_wellformed. *)
  (*   assumption. *)
  (* Qed. *)
  Abort.

  Lemma lookup_env_const_name :
    forall {c c' d},
      lookup_env Σ c' = Some (ConstantDecl c d) ->
      c' = c.
  Proof.
    intros c c' d e. clear hΣ.
    destruct Σ as [Σ' ?]. cbn in e.
    induction Σ'.
    - cbn in e. discriminate.
    - destruct a.
      + cbn in e. destruct (ident_eq_spec c' k).
        * subst. inversion e. reflexivity.
        * apply IHΣ'. assumption.
      + cbn in e. destruct (ident_eq_spec c' k).
        * inversion e.
        * apply IHΣ'. assumption.
  Qed.

  Lemma red_const :
    forall {Γ n c u cty cb cu},
      Some (ConstantDecl n {| cst_type := cty ; cst_body := Some cb ; cst_universes := cu |})
      = lookup_env Σ c ->
      red (fst Σ) Γ (tConst c u) (subst_instance_constr u cb).
  Proof.
    intros Γ n c u cty cb cu e.
    symmetry in e.
    pose proof (lookup_env_const_name e). subst.
    econstructor.
    - econstructor.
    - econstructor.
      + exact e.
      + reflexivity.
  Qed.

  Lemma cored_const :
    forall {Γ n c u cty cb cu},
      Some (ConstantDecl n {| cst_type := cty ; cst_body := Some cb ; cst_universes := cu |})
      = lookup_env Σ c ->
      cored (fst Σ) Γ (subst_instance_constr u cb) (tConst c u).
  Proof.
    intros Γ n c u cty cb cu e.
    symmetry in e.
    pose proof (lookup_env_const_name e). subst.
    econstructor.
    econstructor.
    - exact e.
    - reflexivity.
  Qed.

  Derive Signature for cumul.
  Derive Signature for red1.

  Lemma app_reds_r :
    forall Γ u v1 v2,
      red Σ Γ v1 v2 ->
      red Σ Γ (tApp u v1) (tApp u v2).
  Proof.
    intros Γ u v1 v2 h.
    revert u. induction h ; intros u.
    - constructor.
    - econstructor.
      + eapply IHh.
      + constructor. assumption.
  Qed.

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

  Fixpoint isProd t :=
    match t with
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
      cbn in h. exfalso. assumption.
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
      apply PCUICPrincipality.invert_cumul_prod_r in bot ; auto.
      destruct bot as [? [? [? [[r ?] ?]]]].
      exfalso. clear - r wΣ.
      revert r. generalize (Universe.sort_of_product s1 s2). intro s. clear.
      intro r.
      dependent induction r.
      assert (h : P = tSort s).
      { clear - r. induction r ; auto. subst.
        dependent destruction r0.
        assert (h : isSort (mkApps (tFix mfix idx) args)).
        { rewrite <- H. constructor. }
        apply isSortmkApps in h. subst. cbn in H.
        discriminate.
      }
      subst.
      dependent destruction r0.
      assert (h : isSort (mkApps (tFix mfix idx) args)).
      { rewrite <- H. constructor. }
      apply isSortmkApps in h. subst. cbn in H.
      discriminate.
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

  Lemma mkApps_Prod_nil' :
    forall Γ na A B l,
      wellformed Σ Γ (mkApps (tProd na A B) l) ->
      l = [].
  Proof.
    intros Γ na A B l [h | [[ctx [s [hd hw]]]]].
    - eapply mkApps_Prod_nil. eassumption.
    - destruct l ; auto.
      cbn in hd. rewrite destArity_tApp in hd. discriminate.
  Qed.

  (* TODO MOVE or even replace old lemma *)
  Lemma decompose_stack_noStackApp :
    forall π l ρ,
      decompose_stack π = (l,ρ) ->
      isStackApp ρ = false.
  Proof.
    intros π l ρ e.
    destruct ρ. all: auto.
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

  Lemma nleq_term_zipc :
    forall u v π,
      nleq_term u v ->
      nleq_term (zipc u π) (zipc v π).
  Proof.
    intros u v π h.
    eapply ssrbool.introT.
    - eapply reflect_nleq_term.
    - cbn. rewrite 2!nl_zipc. f_equal.
      eapply ssrbool.elimT.
      + eapply reflect_nleq_term.
      + assumption.
  Qed.

  Lemma nleq_term_zipx :
    forall Γ u v π,
      nleq_term u v ->
      nleq_term (zipx Γ u π) (zipx Γ v π).
  Proof.
    intros Γ u v π h.
    unfold zipx.
    eapply nleq_term_it_mkLambda_or_LetIn.
    eapply nleq_term_zipc.
    assumption.
  Qed.

  Hint Resolve conv_alt_refl conv_alt_red : core.
  Hint Resolve conv_ctx_refl: core.


  (* Let bindings are not injective, so it_mkLambda_or_LetIn is not either.
     However, when they are all lambdas they become injective for conversion.
     stack_contexts only produce lambdas so we can use this property on them.
   *)
  Fixpoint let_free_context (Γ : context) :=
    match Γ with
    | [] => true
    | {| decl_name := na ; decl_body := Some b ; decl_type := B |} :: Γ => false
    | {| decl_name := na ; decl_body := None ; decl_type := B |} :: Γ =>
      let_free_context Γ
    end.

  Lemma let_free_stack_context :
    forall π,
      let_free_context (stack_context π).
  Proof.
    intros π.
    induction π.
    all: (simpl ; rewrite ?IHπ ; reflexivity).
  Qed.

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
    destruct r.
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
    revert h. induction r ; intros h.
    - assumption.
    - specialize IHr with (1 := ltac:(eassumption)).
      destruct IHr as [A ?]. exists A.
      eapply sr_red1 ; eauto with wf.
  Qed.

  Lemma red_cored_cored :
    forall Γ u v w,
      red Σ Γ v w ->
      cored Σ Γ v u ->
      cored Σ Γ w u.
  Proof.
    intros Γ u v w h1 h2.
    revert u h2. induction h1 ; intros t h2.
    - assumption.
    - eapply cored_trans.
      + eapply IHh1. assumption.
      + assumption.
  Qed.

  (* TODO MOVE It needs wf Σ entirely *)
  Lemma subject_conversion :
    forall Γ u v A B,
      Σ ;;; Γ |- u : A ->
      Σ ;;; Γ |- v : B ->
      Σ ;;; Γ |- u == v ->
      ∑ C,
        Σ ;;; Γ |- u : C ×
        Σ ;;; Γ |- v : C.
  Proof.
    intros Γ u v A B hu hv h.
    (* apply conv_conv_alt in h. *)
    (* apply conv_alt_red in h as [u' [v' [? [? ?]]]]. *)
    (* pose proof (subject_reduction _ Γ _ _ _ hΣ hu r) as hu'. *)
    (* pose proof (subject_reduction _ Γ _ _ _ hΣ hv r0) as hv'. *)
    (* pose proof (typing_alpha _ _ _ _ hu' e) as hv''. *)
    (* pose proof (principal_typing _ hv' hv'') as [C [? [? hvC]]]. *)
    (* apply eq_term_sym in e as e'. *)
    (* pose proof (typing_alpha _ _ _ _ hvC e') as huC. *)
    (* Not clear.*)
  Abort.

  Lemma welltyped_zipc_replace :
    forall Γ u v π,
      welltyped Σ Γ (zipc v π) ->
      welltyped Σ (Γ ,,, stack_context π) u ->
      Σ ;;; Γ ,,, stack_context π |- u == v ->
      welltyped Σ Γ (zipc u π).
  Proof.
    destruct hΣ as [wΣ].
    intros Γ u v π hv hu heq.
    induction π in u, v, hu, hv, heq |- *.
    - simpl in *. assumption.
    - simpl in *. eapply IHπ.
      + eassumption.
      + zip fold in hv. apply welltyped_context in hv.
        simpl in hv.
        destruct hv as [Tv hv].
        destruct hu as [Tu hu].
        apply inversion_App in hv as ihv ; auto.
        destruct ihv as [na [A' [B' [hv' [ht ?]]]]].
        (* Seems to be derivable (tediously) from some principal type lemma. *)
        admit.
      + (* Congruence *)
        admit.
  Admitted.

  Lemma wellformed_zipc_replace :
    forall Γ u v π,
      wellformed Σ Γ (zipc v π) ->
      wellformed Σ (Γ ,,, stack_context π) u ->
      Σ ;;; Γ ,,, stack_context π |- u == v ->
      wellformed Σ Γ (zipc u π).
  Admitted.

  Derive Signature for typing.

  (* Follows from principality, inversion of cumul/confluence *)
  Lemma Construct_Ind_ind_eq :
    forall {Γ n i args u i' args' u'},
      Σ ;;; Γ |- mkApps (tConstruct i n u) args : mkApps (tInd i' u') args' ->
      i = i'.
  Proof.
    destruct hΣ as [wΣ].
    intros Γ n i args u i' args' u' h.
    eapply inversion_mkApps in h ; auto.
    destruct h as [T [U [hC [hs hc]]]].
    apply inversion_Construct in hC
      as [mdecl [idecl [cdecl [hΓ [isdecl [const htc]]]]]].
    unfold type_of_constructor in htc. simpl in htc.
    destruct i as [mind nind]. simpl in *.
    destruct cdecl as [[cna ct] cn]. cbn in htc.
    destruct mdecl as [mnpars mpars mbod muni]. simpl in *.
    destruct idecl as [ina ity ike ict iprj]. simpl in *.
    unfold declared_constructor in isdecl. cbn in isdecl.
    destruct isdecl as [[dm hin] hn]. simpl in *.
    unfold declared_minductive in dm.
    (* Do we need to exploit wellformedness of the context?? *)
    (* We should also use invert_cumul_ind_l at some point. *)
  Admitted.

  Lemma Proj_red_cond :
    forall Γ i pars narg i' c u l,
      wellformed Σ Γ (tProj (i, pars, narg) (mkApps (tConstruct i' c u) l)) ->
      nth_error l (pars + narg) <> None.
  Proof.
    intros Γ i pars narg i' c u l [[T h]|[[ctx [s [e _]]]]];
      [|discriminate].
    apply inversion_Proj in h.
    destruct h as [uni [mdecl [idecl [pdecl [args' [d [hc [? ?]]]]]]]].
    eapply on_declared_projection in d. destruct d as [? [? ?]].
    simpl in *.
    destruct p.
    destruct o0.
  Admitted.

  Lemma Case_Construct_ind_eq :
    forall {Γ ind ind' npar pred i u brs args},
      wellformed Σ Γ (tCase (ind, npar) pred (mkApps (tConstruct ind' i u) args) brs) ->
      ind = ind'.
  Proof.
    destruct hΣ as [wΣ].
    intros Γ ind ind' npar pred i u brs args [[A h]|[[ctx [s [e _]]]]];
      [|discriminate].
    apply inversion_Case in h as ih ; auto.
    destruct ih
      as [uni [args' [mdecl [idecl [pty [indctx [pctx [ps [btys [? [? [? [? [? [? [ht0 [? ?]]]]]]]]]]]]]]]]].
    apply Construct_Ind_ind_eq in ht0. eauto.
  Qed.

  Lemma Proj_Constuct_ind_eq :
    forall Γ i i' pars narg c u l,
      wellformed Σ Γ (tProj (i, pars, narg) (mkApps (tConstruct i' c u) l)) ->
      i = i'.
  Proof.
    destruct hΣ as [wΣ].
    intros Γ i i' pars narg c u l [[T h]|[[ctx [s [e _]]]]];
      [|discriminate].
    apply inversion_Proj in h ; auto.
    destruct h as [uni [mdecl [idecl [pdecl [args' [? [hc [? ?]]]]]]]].
    apply Construct_Ind_ind_eq in hc. eauto.
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
    do 2 zip fold. eapply red_context. assumption.
  Qed.

  Lemma wellformed_zipc_zipp :
    forall Γ t π,
      wellformed Σ Γ (zipc t π) ->
      wellformed Σ (Γ ,,, stack_context π) (zipp t π).
  Proof.
    intros Γ t π h.
    unfold zipp.
    case_eq (decompose_stack π). intros l ρ e.
    pose proof (decompose_stack_eq _ _ _ e). subst. clear e.
    rewrite zipc_appstack in h.
    zip fold in h.
    apply wellformed_context in h. simpl in h.
    rewrite stack_context_appstack.
    assumption.
  Qed.

  Lemma conv_context_convp :
    forall Γ Γ' leq u v,
      conv leq Σ Γ u v ->
      conv_context Σ Γ Γ' ->
      conv leq Σ Γ' u v.
  Proof.
    intros Γ Γ' leq u v h hx.
    destruct hΣ.
    destruct leq.
    - simpl. destruct h. constructor.
      eapply conv_alt_conv_ctx. all: eauto.
    - simpl in *. destruct h. constructor.
      eapply cumul_conv_ctx. all: eauto.
  Qed.

End Lemmata.


Lemma strengthening `{cf : checker_flags} :
  forall {Σ Γ Γ' Γ'' t T},
    wf Σ.1 ->
    Σ ;;; Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ'
    |- lift #|Γ''| #|Γ'| t : lift #|Γ''| #|Γ'| T ->
    Σ;;; Γ ,,, Γ' |- t : T.
Admitted.

From MetaCoq.Checker Require Import uGraph.

(* todo: move *)
Lemma map_option_out_mapi :
  forall {A B} (l : list A) (l' : list B) f P,
    map_option_out (mapi f l) = Some l' ->
    Alli (fun i x => on_Some_or_None P (f i x)) 0 l ->
    All P l'.
Proof.
  intros A B l l' f P.
  unfold mapi. generalize 0.
  induction l in l' |- *; simpl; intro n.
  - inversion 1; constructor.
  - case_eq (f n a); [|discriminate].
    intros b Hb.
    case_eq (map_option_out (mapi_rec f l (S n))); [|discriminate].
    intros l0 Hl0 HH0 HH1.
    inversion HH0; subst; clear HH0.
    inversion HH1; subst.
    constructor. now rewrite Hb in H0.
    now eapply IHl.
Qed.

(* todo: move *)
Lemma Alli_id :
  forall {A} {P : nat -> A -> Type} (l : list A) (n : nat),
    (forall n x, P n x) -> Alli P n l.
Proof.
  intros A P l n h.
  induction l in n |- * ; constructor ; eauto.
Qed.

(* todo: move *)
Lemma map_option_out_All {A} P (l : list (option A)) l' :
  (All (on_some P) l) ->
  map_option_out l = Some l' ->
  All P l'.
Proof.
  induction 1 in l' |- *; cbn; inversion 1; subst; try constructor.
  destruct x; [|discriminate].
  case_eq (map_option_out l); [|intro e; rewrite e in H1; discriminate].
  intros l0 e; rewrite e in H1; inversion H1; subst.
  constructor; auto.
Qed.

(* todo: move *)
Lemma All_mapi {A B} P f l k :
  Alli (fun i x => P (f i x)) k l -> All P (@mapi_rec A B f l k).
Proof.
  induction 1; simpl; constructor; tas.
Qed.



Lemma type_Case_valid_btys {cf:checker_flags} Σ Γ ind u npar p (* c brs *) args :
    forall mdecl idecl (isdecl : declared_inductive Σ.1 mdecl ind idecl),
    mdecl.(ind_npars) = npar ->
    let pars := List.firstn npar args in
    forall pty, Σ ;;; Γ |- p : pty ->
    forall indctx pctx ps btys, types_of_case ind mdecl idecl pars u p pty
                           = Some (indctx, pctx, ps, btys) ->
    (* check_correct_arity (global_ext_constraints Σ) idecl ind u indctx pars pctx -> *)
    (* List.Exists (fun sf => universe_family ps = sf) idecl.(ind_kelim) -> *)
    (* Σ ;;; Γ |- c : mkApps (tInd ind u) args -> *)
    (* All2 (fun x y => (fst x = fst y) × (Σ ;;; Γ |- snd x : snd y)) brs btys -> *)
    All (fun x => Σ ;;; Γ |- snd x : tSort ps) btys.
Proof.
  intros mdecl idecl isdecl H0 pars pty X indctx pctx ps btys toc.
  apply types_of_case_spec in toc.
  destruct toc as [s' [_ [H1 H2]]].
  pose proof (PCUICClosed.destArity_spec [] pty) as Hpty; rewrite H1 in Hpty;
    cbn in Hpty; subst; clear H1.
  unfold build_branches_type in H2.
  eapply map_option_out_All; tea. clear H2.
  apply All_mapi.
  apply PCUICWeakeningEnv.on_declared_inductive in isdecl as [oind oc].
  apply onConstructors in oc.
  eapply Alli_impl; tea.
  intros n [[id ct] k] [Hct1 Hct2]; cbn in *.
  case_eq (instantiate_params (subst_instance_context u (ind_params mdecl)) pars
             ((subst0 (inds (inductive_mind ind) u (ind_bodies mdecl)))
                (subst_instance_constr u ct))).
  - intros ct' Hct'.
    case_eq (decompose_prod_assum [] ct'); intros sign ccl e1.
    case_eq (chop (ind_npars mdecl) (decompose_app ccl).2);
      intros paramrels args0 e2; cbn.
    admit.
  - intro HH. cbn.
Admitted.

Lemma type_Case' {cf:checker_flags} Σ Γ ind u npar p c brs args :
    forall mdecl idecl (isdecl : declared_inductive Σ.1 mdecl ind idecl),
    mdecl.(ind_npars) = npar ->
    let pars := List.firstn npar args in
    forall pty, Σ ;;; Γ |- p : pty ->
    forall indctx pctx ps btys, types_of_case ind mdecl idecl pars u p pty
                           = Some (indctx, pctx, ps, btys) ->
    check_correct_arity (global_ext_constraints Σ) idecl ind u indctx pars pctx ->
    existsb (leb_sort_family (universe_family ps)) idecl.(ind_kelim) ->
    Σ ;;; Γ |- c : mkApps (tInd ind u) args ->
    All2 (fun x y => (fst x = fst y) × (Σ ;;; Γ |- snd x : snd y)) brs btys ->
    Σ ;;; Γ |- tCase (ind, npar) p c brs : mkApps p (List.skipn npar args ++ [c]).
Proof.
  intros mdecl idecl isdecl H pars pty X indctx pctx ps btys H0 X0 H1 X1 X2.
  econstructor; tea.
  eapply type_Case_valid_btys in H0; tea.
  eapply All2_All_mix_right; tas.
Qed.



Lemma destArity_spec_Some ctx T ctx' s :
  destArity ctx T = Some (ctx', s)
  -> it_mkProd_or_LetIn ctx T = it_mkProd_or_LetIn ctx' (tSort s).
Proof.
  pose proof (PCUICClosed.destArity_spec ctx T) as H.
  intro e; now rewrite e in H.
Qed.
