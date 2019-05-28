(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia
     Classes.RelationClasses Omega.
From MetaCoq.Template Require Import config Universes monad_utils utils BasicAst
     AstUtils UnivSubst.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICReflect PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICSafeReduce
     PCUICCumulativity PCUICSR PCUICPosition PCUICEquality PCUICNameless.
From Equations Require Import Equations.

Require Import Equations.Prop.DepElim.

Import MonadNotation.

Module PSR := PCUICSafeReduce.

Tactic Notation "zip" "fold" "in" hyp(h) :=
  lazymatch type of h with
  | context C[ zipc ?t ?π ] =>
    let C' := context C[ zip (t,π) ] in
    change C' in h
  end.

Tactic Notation "zip" "fold" :=
  lazymatch goal with
  | |- context C[ zipc ?t ?π ] =>
    let C' := context C[ zip (t,π) ] in
    change C'
  end.

Inductive conv_pb :=
| Conv
| Cumul.

Definition conv leq Σ Γ u v :=
  match leq with
  | Conv => ∥ Σ ;;; Γ |- u = v ∥
  | Cumul => ∥ Σ ;;; Γ |- u <= v ∥
  end.

Definition nodelta_flags := RedFlags.mk true true true false true true.

Section Lemmata.

  Context (flags : RedFlags.t).
  Context (Σ : global_context).
  Context (hΣ : wf Σ).

  Lemma wf_nlg :
    wf (nlg Σ).
  Admitted.

  Lemma welltyped_nlg :
    forall Γ t,
      welltyped Σ Γ t ->
      welltyped (nlg Σ) Γ t.
  Admitted.

  Lemma welltyped_rename :
    forall Γ u v,
      welltyped Σ Γ u ->
      eq_term (snd Σ) u v ->
      welltyped Σ Γ v.
  Admitted.

  Lemma red_welltyped :
    forall {Γ u v},
      welltyped Σ Γ u ->
      ∥ red (fst Σ) Γ u v ∥ ->
      welltyped Σ Γ v.
  Proof.
    intros Γ u v h [r].
    revert h. induction r ; intros h.
    - assumption.
    - specialize IHr with (1 := ltac:(eassumption)).
      destruct IHr as [A ?]. exists A.
      eapply PSR.subject_reduction ; eassumption.
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

  Set Equations With UIP.

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

  Lemma red_it_mkLambda_or_LetIn :
    forall Γ Δ u v,
      red Σ (Γ ,,, Δ) u v ->
      red Σ Γ (it_mkLambda_or_LetIn Δ u)
              (it_mkLambda_or_LetIn Δ v).
  Proof.
    intros Γ Δ u v h.
    induction h.
    - constructor.
    - econstructor.
      + eassumption.
      + eapply red1_it_mkLambda_or_LetIn. assumption.
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

  Lemma red_trans :
    forall Γ u v w,
      red (fst Σ) Γ u v ->
      red (fst Σ) Γ v w ->
      red (fst Σ) Γ u w.
  Proof.
    intros Γ u v w h1 h2.
    revert u h1. induction h2 ; intros u h1.
    - assumption.
    - specialize IHh2 with (1 := h1).
      eapply trans_red.
      + eapply IHh2.
      + assumption.
  Qed.

  Lemma conv_refl' :
    forall leq Γ t,
      conv leq Σ Γ t t.
  Proof.
    intros leq Γ t.
    destruct leq.
    - cbn. constructor. apply conv_refl.
    - cbn. constructor. apply cumul_refl'.
  Qed.

  Lemma conv_sym :
    forall Γ u v,
      Σ ;;; Γ |- u = v ->
      Σ ;;; Γ |- v = u.
  Proof.
    intros Γ u v [h1 h2].
    econstructor ; assumption.
  Qed.

  Lemma conv_conv :
    forall {Γ leq u v},
      ∥ Σ ;;; Γ |- u = v ∥ ->
      conv leq Σ Γ u v.
  Proof.
    intros Γ leq u v h.
    destruct leq.
    - assumption.
    - destruct h as [[h1 h2]]. cbn.
      constructor. assumption.
  Qed.

  Lemma eq_term_conv :
    forall {Γ u v},
      eq_term (snd Σ) u v ->
      Σ ;;; Γ |- u = v.
  Proof.
    intros Γ u v e.
    constructor.
    - eapply cumul_refl.
      eapply eq_term_leq_term. assumption.
    - eapply cumul_refl.
      eapply eq_term_leq_term.
      eapply eq_term_sym.
      assumption.
  Qed.

  Lemma conv_trans :
    forall Γ u v w,
      Σ ;;; Γ |- u = v ->
      Σ ;;; Γ |- v = w ->
      Σ ;;; Γ |- u = w.
  Proof.
    intros Γ u v w h1 h2.
    destruct h1, h2. constructor ; eapply cumul_trans ; eassumption.
  Qed.

  Lemma conv_trans' :
    forall leq Γ u v w,
      conv leq Σ Γ u v ->
      conv leq Σ Γ v w ->
      conv leq Σ Γ u w.
  Proof.
    intros leq Γ u v w h1 h2.
    destruct leq.
    - cbn in *. destruct h1, h2. constructor.
      eapply conv_trans ; eassumption.
    - cbn in *. destruct h1, h2. constructor. eapply cumul_trans ; eassumption.
  Qed.

  Lemma red_conv_l :
    forall leq Γ u v,
      red (fst Σ) Γ u v ->
      conv leq Σ Γ u v.
  Proof.
    intros leq Γ u v h.
    induction h.
    - apply conv_refl'.
    - eapply conv_trans' ; try eassumption.
      destruct leq.
      + simpl. constructor. constructor.
        * eapply cumul_red_l.
          -- eassumption.
          -- eapply cumul_refl'.
        * eapply cumul_red_r.
          -- eapply cumul_refl'.
          -- assumption.
      + simpl. constructor.
        eapply cumul_red_l.
        * eassumption.
        * eapply cumul_refl'.
  Qed.

  Lemma red_conv_r :
    forall leq Γ u v,
      red (fst Σ) Γ u v ->
      conv leq Σ Γ v u.
  Proof.
    intros leq Γ u v h.
    induction h.
    - apply conv_refl'.
    - eapply conv_trans' ; try eassumption.
      destruct leq.
      + simpl. constructor. constructor.
        * eapply cumul_red_r.
          -- eapply cumul_refl'.
          -- assumption.
        * eapply cumul_red_l.
          -- eassumption.
          -- eapply cumul_refl'.
      + simpl. constructor.
        eapply cumul_red_r.
        * eapply cumul_refl'.
        * assumption.
  Qed.

  Lemma conv_conv_l :
    forall leq Γ u v,
        Σ ;;; Γ |- u = v ->
        conv leq Σ Γ u v.
  Proof.
    intros [] Γ u v [h1 h2].
    - cbn. constructor. constructor ; assumption.
    - cbn. constructor. assumption.
  Qed.

  Lemma conv_conv_r :
    forall leq Γ u v,
        Σ ;;; Γ |- u = v ->
        conv leq Σ Γ v u.
  Proof.
    intros [] Γ u v [h1 h2].
    - cbn. constructor. constructor ; assumption.
    - cbn. constructor. assumption.
  Qed.

  Lemma cumul_App_l :
    forall {Γ f g x},
      Σ ;;; Γ |- f <= g ->
      Σ ;;; Γ |- tApp f x <= tApp g x.
  Proof.
    intros Γ f g x h.
    induction h.
    - eapply cumul_refl. constructor.
      + assumption.
      + apply leq_term_refl.
    - eapply cumul_red_l ; try eassumption.
      econstructor. assumption.
    - eapply cumul_red_r ; try eassumption.
      econstructor. assumption.
  Qed.

  Lemma conv_App_r :
    forall {Γ f x y},
      Σ ;;; Γ |- x = y ->
      Σ ;;; Γ |- tApp f x = tApp f y.
  Proof.
    intros Γ f x y [h1 h2].
  Admitted.

  Lemma conv_Prod_l :
    forall {Γ na A1 A2 B},
      Σ ;;; Γ |- A1 = A2 ->
      Σ ;;; Γ |- tProd na A1 B = tProd na A2 B.
  Proof.
  Admitted.

  Lemma cumul_Prod_r :
    forall {Γ na A B1 B2},
      Σ ;;; Γ ,, vass na A |- B1 <= B2 ->
      Σ ;;; Γ |- tProd na A B1 <= tProd na A B2.
  Proof.
    intros Γ na A B1 B2 h.
    induction h.
    - eapply cumul_refl. constructor.
      + apply leq_term_refl.
      + assumption.
    - eapply cumul_red_l ; try eassumption.
      econstructor. assumption.
    - eapply cumul_red_r ; try eassumption.
      econstructor. assumption.
  Qed.

  Lemma conv_Prod :
    forall leq Γ na na' A1 A2 B1 B2,
      Σ ;;; Γ |- A1 = A2 ->
      conv leq Σ (Γ,, vass na A1) B1 B2 ->
      conv leq Σ Γ (tProd na A1 B1) (tProd na' A2 B2).
  Admitted.

  Lemma cumul_context :
    forall Γ u v ρ,
      Σ ;;; Γ |- u <= v ->
      Σ ;;; Γ |- zipc u ρ <= zipc v ρ.
  Proof.
    intros Γ u v ρ h.
    revert u v h. induction ρ ; intros u v h.
    - cbn. assumption.
    - cbn. apply IHρ.
      eapply cumul_App_l. assumption.
    - cbn. eapply IHρ.
      (* eapply conv_App_r. *)
      (* Congruence for application on the right *)
      admit.
    - cbn.
      (* Congruence for case *)
      admit.
  Admitted.

  Lemma conv_context :
    forall Γ u v ρ,
      Σ ;;; Γ |- u = v ->
      Σ ;;; Γ |- zipc u ρ = zipc v ρ.
  Proof.
    intros Γ u v ρ [].
    constructor ; eapply cumul_context ; assumption.
  Qed.

  Lemma conv_context' :
    forall Γ leq u v ρ,
      conv leq Σ Γ u v ->
      conv leq Σ Γ (zipc u ρ) (zipc v ρ).
  Proof.
    intros Γ leq u v ρ h.
    destruct leq.
    - cbn in *. destruct h as [[h1 h2]]. constructor.
      constructor ; eapply cumul_context ; assumption.
    - cbn in *. destruct h. constructor.
      eapply cumul_context. assumption.
  Qed.

  Lemma cumul_it_mkLambda_or_LetIn :
    forall Δ Γ u v,
      Σ ;;; (Δ ,,, Γ) |- u <= v ->
      Σ ;;; Δ |- it_mkLambda_or_LetIn Γ u <= it_mkLambda_or_LetIn Γ v.
  Proof.
    intros Δ Γ u v h. revert Δ u v h.
    induction Γ as [| [na [b|] A] Γ ih ] ; intros Δ u v h.
    - assumption.
    - simpl. cbn. eapply ih.
      (* Need cumul for LetIn *)
      admit.
    - simpl. cbn. eapply ih.
      (* Need cumul for Lambda *)
      admit.
  Admitted.

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
      eapply cumul_it_mkLambda_or_LetIn. cbn.
      (* Need cumul for Lambda again *)
      admit.
    - unfold zippx. simpl.
      eapply cumul_it_mkLambda_or_LetIn.
      assumption.
    - unfold zippx. simpl.
      eapply cumul_it_mkLambda_or_LetIn. cbn.
      (* cumul lambda *)
      admit.
  Admitted.

  Lemma conv_zippx :
    forall Γ u v ρ,
      Σ ;;; Γ ,,, stack_context ρ |- u = v ->
      Σ ;;; Γ |- zippx u ρ = zippx v ρ.
  Proof.
    intros Γ u v ρ [].
    constructor ; eapply cumul_zippx ; assumption.
  Qed.

  Lemma conv_zippx' :
    forall Γ leq u v ρ,
      conv leq Σ (Γ ,,, stack_context ρ) u v ->
      conv leq Σ Γ (zippx u ρ) (zippx v ρ).
  Proof.
    intros Γ leq u v ρ h.
    destruct leq.
    - cbn in *. destruct h as [[h1 h2]]. constructor.
      constructor ; eapply cumul_zippx ; assumption.
    - cbn in *. destruct h. constructor.
      eapply cumul_zippx. assumption.
  Qed.

    (* TODO MOVE *)
  Local Ltac lih :=
    lazymatch goal with
    | ih : forall v n k, eq_term_upto_univ _ ?u _ -> _
      |- eq_term_upto_univ _ (lift _ _ ?u) _ =>
      eapply ih
    end.

  Lemma eq_term_upto_univ_lift :
    forall R u v n k,
      eq_term_upto_univ R u v ->
      eq_term_upto_univ R (lift n k u) (lift n k v).
  Proof.
    intros R u v n k e.
    induction u in v, n, k, e |- * using term_forall_list_ind.
    all: dependent destruction e.
    all: try (cbn ; constructor ; try lih ; assumption).
    - cbn. destruct (Nat.leb_spec0 k n0).
      + constructor.
      + constructor.
    - cbn. constructor.
      eapply Forall2_map.
      eapply Forall2_impl'.
      + eassumption.
      + eapply All_Forall.
        eapply All_impl ; [ eassumption |].
        intros x H1 y H2. cbn in H1.
        eapply H1. assumption.
    - cbn. constructor ; try lih ; try assumption.
      eapply Forall2_map. eapply Forall2_impl' ; [ eassumption |].
      eapply All_Forall. eapply All_impl ; [ eassumption |].
      intros x H0 y [? ?]. cbn in H0. repeat split ; auto.
      eapply H0. assumption.
    - cbn. constructor.
      eapply Forall2_map. eapply Forall2_impl' ; [ eassumption |].
      eapply All_Forall. eapply All_impl ; [ eassumption |].
      intros x [h1 h2] y [? [? ?]].
      repeat split ; auto.
      + eapply h1. assumption.
      + apply Forall2_length in H. rewrite H.
        eapply h2. assumption.
    - cbn. constructor.
      eapply Forall2_map. eapply Forall2_impl' ; [ eassumption |].
      eapply All_Forall. eapply All_impl ; [ eassumption |].
      intros x [h1 h2] y [? [? ?]].
      repeat split ; auto.
      + eapply h1. assumption.
      + apply Forall2_length in H. rewrite H.
        eapply h2. assumption.
  Qed.

  (* TODO MOVE *)
  Local Ltac sih :=
    lazymatch goal with
    | ih : forall v n x y, eq_term_upto_univ _ ?u _ -> _ -> _
      |- eq_term_upto_univ _ (subst _ _ ?u) _ => eapply ih
    end.

  (* TODO MOVE *)
  Lemma eq_term_upto_univ_subst :
    forall R u v n x y,
      eq_term_upto_univ R u v ->
      eq_term_upto_univ R x y ->
      eq_term_upto_univ R (u{n := x}) (v{n := y}).
  Proof.
    intros R u v n x y e1 e2.
    induction u in v, n, x, y, e1, e2 |- * using term_forall_list_ind.
    all: dependent destruction e1.
    all: try (cbn ; constructor ; try sih ; assumption).
    - cbn. destruct (Nat.leb_spec0 n n0).
      + destruct (eqb_spec n0 n).
        * subst. replace (n - n) with 0 by omega. cbn.
          eapply eq_term_upto_univ_lift. assumption.
        * replace (n0 - n) with (S (n0 - (S n))) by omega. cbn.
          rewrite nth_error_nil. constructor.
      + constructor.
    - cbn. constructor.
      eapply Forall2_map. eapply Forall2_impl' ; [ eassumption |].
      eapply All_Forall.
      eapply All_impl ; [ eassumption |].
      intros x0 H1 y0 H2. cbn in H1.
      eapply H1. all: assumption.
    - cbn. constructor ; try sih ; try assumption.
      eapply Forall2_map. eapply Forall2_impl' ; [ eassumption |].
      eapply All_Forall. eapply All_impl ; [ eassumption |].
      intros ? H0 ? [? ?]. cbn in H0. repeat split ; auto.
      eapply H0. all: assumption.
    - cbn. constructor.
      eapply Forall2_map. eapply Forall2_impl' ; [ eassumption |].
      eapply All_Forall. eapply All_impl ; [ eassumption |].
      intros ? [h1 h2] ? [? [? ?]].
      repeat split ; auto.
      + eapply h1. all: assumption.
      + apply Forall2_length in H. rewrite H.
        eapply h2. all: assumption.
    - cbn. constructor.
      eapply Forall2_map. eapply Forall2_impl' ; [ eassumption |].
      eapply All_Forall. eapply All_impl ; [ eassumption |].
      intros ? [h1 h2] ? [? [? ?]].
      repeat split ; auto.
      + eapply h1. all: assumption.
      + apply Forall2_length in H. rewrite H.
        eapply h2. all: assumption.
  Qed.

  (* TODO MOVE *)
  Lemma eq_term_upto_univ_mkApps_l_inv :
    forall R u l t,
      eq_term_upto_univ R (mkApps u l) t ->
      exists u' l',
        eq_term_upto_univ R u u' /\
        Forall2 (eq_term_upto_univ R) l l' /\
        t = mkApps u' l'.
  Proof.
    intros R u l t h.
    induction l in u, t, h |- *.
    - cbn in h. exists t, []. split ; auto.
    - cbn in h. apply IHl in h as [u' [l' [h1 [h2 h3]]]].
      dependent destruction h1. subst.
      eexists. eexists. split ; [ | split ].
      + eassumption.
      + constructor.
        * eassumption.
        * eassumption.
      + cbn. reflexivity.
  Qed.

  (* TODO MOVE *)
  Lemma eq_term_upto_univ_mkApps :
    forall R u1 l1 u2 l2,
      eq_term_upto_univ R u1 u2 ->
      Forall2 (eq_term_upto_univ R) l1 l2 ->
      eq_term_upto_univ R (mkApps u1 l1) (mkApps u2 l2).
  Proof.
    intros R u1 l1 u2 l2 hu hl.
    induction l1 in u1, u2, l2, hu, hl |- *.
    - inversion hl. subst. assumption.
    - inversion hl. subst. simpl.
      eapply IHl1.
      + constructor. all: assumption.
      + assumption.
  Qed.

  (* TODO MOVE *)
  Lemma Forall2_nth :
    forall A B P l l' n (d : A) (d' : B),
      Forall2 P l l' ->
      P d d' ->
      P (nth n l d) (nth n l' d').
  Proof.
    intros A B P l l' n d d' h hd.
    induction n in l, l', h |- *.
    - destruct h.
      + assumption.
      + assumption.
    - destruct h.
      + assumption.
      + simpl. apply IHn. assumption.
  Qed.

  Arguments skipn : simpl nomatch.

  (* TODO MOVE *)
  Lemma Forall2_skipn :
    forall A B P l l' n,
      @Forall2 A B P l l' ->
      Forall2 P (skipn n l) (skipn n l').
  Proof.
    intros A B P l l' n h.
    induction n in l, l', h |- *.
    - assumption.
    - destruct h.
      + constructor.
      + simpl. apply IHn. assumption.
  Qed.

  Lemma Forall2_nth_error_Some_l :
    forall A B (P : A -> B -> Prop) l l' n t,
      nth_error l n = Some t ->
      Forall2 P l l' ->
      exists t',
        nth_error l' n = Some t' /\
        P t t'.
  Proof.
    intros A B P l l' n t e h.
    induction n in l, l', t, e, h |- *.
    - destruct h.
      + cbn in e. discriminate.
      + cbn in e. inversion e. subst.
        exists y. split ; auto.
    - destruct h.
      + cbn in e. discriminate.
      + cbn in e. apply IHn with (l' := l') in e ; assumption.
  Qed.

  (* TODO MOVE *)
  Lemma eq_term_upto_univ_isApp :
    forall R u v,
      eq_term_upto_univ R u v ->
      isApp u = isApp v.
  Proof.
    intros R u v h.
    induction h.
    all: reflexivity.
  Qed.

  (* TODO MOVE *)
  Lemma isApp_mkApps :
    forall u l,
      isApp u ->
      isApp (mkApps u l).
  Proof.
    intros u l h.
    induction l in u, h |- *.
    - cbn. assumption.
    - cbn. apply IHl. reflexivity.
  Qed.

  (* TODO MOVE *)
  Fixpoint nApp t :=
    match t with
    | tApp u _ => S (nApp u)
    | _ => 0
    end.

  (* TODO MOVE *)
  Lemma nApp_mkApps :
    forall t l,
      nApp (mkApps t l) = nApp t + #|l|.
  Proof.
    intros t l.
    induction l in t |- *.
    - simpl. omega.
    - simpl. rewrite IHl. cbn. omega.
  Qed.

  (* TODO MOVE *)
  Lemma mkApps_nApp_inj :
    forall u u' l l',
      nApp u = nApp u' ->
      mkApps u l = mkApps u' l' ->
      u = u' /\ l = l'.
  Proof.
    intros u u' l l' h e.
    induction l in u, u', l', h, e |- *.
    - cbn in e. subst.
      destruct l' ; auto.
      exfalso.
      rewrite nApp_mkApps in h. cbn in h. omega.
    - destruct l'.
      + cbn in e. subst. exfalso.
        rewrite nApp_mkApps in h. cbn in h. omega.
      + cbn in e. apply IHl in e.
        * destruct e as [e1 e2].
          inversion e1. subst. auto.
        * cbn. f_equal. auto.
  Qed.

  (* TODO MOVE *)
  Lemma isApp_false_nApp :
    forall u,
      isApp u = false ->
      nApp u = 0.
  Proof.
    intros u h.
    destruct u.
    all: try reflexivity.
    discriminate.
  Qed.

  (* TODO MOVE *)
  Lemma mkApps_notApp_inj :
    forall u u' l l',
      isApp u = false ->
      isApp u' = false ->
      mkApps u l = mkApps u' l' ->
      u = u' /\ l = l'.
  Proof.
    intros u u' l l' h h' e.
    eapply mkApps_nApp_inj.
    - rewrite 2!isApp_false_nApp by assumption. reflexivity.
    - assumption.
  Qed.

  (* TODO MOVE *)
  Lemma eq_term_upto_univ_mkApps_inv :
    forall R u l u' l',
      isApp u = false ->
      isApp u' = false ->
      eq_term_upto_univ R (mkApps u l) (mkApps u' l') ->
      eq_term_upto_univ R u u' /\ Forall2 (eq_term_upto_univ R) l l'.
  Proof.
    intros R u l u' l' hu hu' h.
    apply eq_term_upto_univ_mkApps_l_inv in h as hh.
    destruct hh as [v [args [h1 [h2 h3]]]].
    apply eq_term_upto_univ_isApp in h1 as hh1. rewrite hu in hh1.
    apply mkApps_notApp_inj in h3 ; auto.
    destruct h3 as [? ?]. subst. split ; auto.
  Qed.

  (* TODO MOVE *)
  Lemma decompose_app_rec_notApp :
    forall t l u l',
      decompose_app_rec t l = (u, l') ->
      isApp u = false.
  Proof.
    intros t l u l' e.
    induction t in l, u, l', e |- *.
    all: try (cbn in e ; inversion e ; reflexivity).
    cbn in e. eapply IHt1. eassumption.
  Qed.

  (* TODO MOVE *)
  Lemma decompose_app_notApp :
    forall t u l,
      decompose_app t = (u, l) ->
      isApp u = false.
  Proof.
    intros t u l e.
    eapply decompose_app_rec_notApp. eassumption.
  Qed.

  (* TODO MOVE? *)
  Lemma isConstruct_app_eq_term_l :
    forall R u v,
      isConstruct_app u ->
      eq_term_upto_univ R u v ->
      isConstruct_app v.
  Proof.
    intros R u v h e.
    case_eq (decompose_app u). intros t1 l1 e1.
    case_eq (decompose_app v). intros t2 l2 e2.
    unfold isConstruct_app in *.
    rewrite e1 in h. cbn in h.
    rewrite e2. cbn.
    destruct t1 ; try discriminate.
    apply PCUICConfluence.decompose_app_inv in e1 as ?. subst.
    apply PCUICConfluence.decompose_app_inv in e2 as ?. subst.
    apply eq_term_upto_univ_mkApps_inv in e as hh.
    - destruct hh as [h1 h2].
      dependent destruction h1. reflexivity.
    - reflexivity.
    - eapply decompose_app_notApp. eassumption.
  Qed.

  (* TODO MOVE *)
  (* Subsumes the other lemma? *)
  Lemma eq_term_upto_univ_substs :
    forall R u v n l l',
      eq_term_upto_univ R u v ->
      Forall2 (eq_term_upto_univ R) l l' ->
      eq_term_upto_univ R (subst l n u) (subst l' n v).
  Proof.
    intros R u v n l l' hu hl.
    induction u in v, n, l, l', hu, hl |- * using term_forall_list_ind.
    all: dependent destruction hu.
    all: try (cbn ; constructor ; try sih ; assumption).
(*     - cbn. destruct (Nat.leb_spec0 n n0). *)
(*       + destruct (eqb_spec n0 n). *)
(*         * subst. replace (n - n) with 0 by omega. *)
(*           destruct hl. *)
(*           -- cbn. constructor. *)
(*           -- cbn. eapply eq_term_upto_univ_lift. assumption. *)
(*         * replace (n0 - n) with (S (n0 - (S n))) by omega. *)
(*           destruct hl. *)
(*           -- cbn. constructor. *)
(*           -- cbn.  *)

(* induction hl in n |- *. *)
(*       + rewrite subst_empty. constructor. *)
(*       + cbn. destruct (Nat.leb_spec0 n n0). *)
(*         * destruct (eqb_spec n0 n). *)
(*           -- subst. replace (n - n) with 0 by omega. cbn. *)
(*              eapply eq_term_upto_univ_lift. assumption. *)
(*           -- replace (n0 - n) with (S (n0 - (S n))) by omega. cbn. *)
(*              cbn in IHhl. specialize (IHhl (S n)). *)
(*              revert IHhl. *)
(*              destruct (Nat.leb_spec0 (S n) n0) ; try (exfalso ; omega). *)
(*              case_eq (nth_error l (n0 - S n)). *)
(*              ++ intros b e. *)
(*                 case_eq (nth_error l' (n0 - S n)). *)
(*                 ** intros b' e' ih. *)



(* cbn. destruct (Nat.leb_spec0 n n0). *)
(*       + destruct (eqb_spec n0 n). *)
(*         * subst. replace (n - n) with 0 by omega. *)
(*           destruct hl. *)
(*           -- cbn. constructor. *)
(*           -- cbn. eapply eq_term_upto_univ_lift. assumption. *)
(*         * replace (n0 - n) with (S (n0 - (S n))) by omega. *)
(*           destruct hl. *)
(*           -- cbn. constructor. *)
(*           -- cbn. *)

(*           eapply eq_term_upto_univ_lift. assumption. *)
(*         * replace (n0 - n) with (S (n0 - (S n))) by omega. cbn. *)
(*           rewrite nth_error_nil. constructor. *)
(*       + constructor. *)
    - admit.
    - cbn. constructor.
      eapply Forall2_map. eapply Forall2_impl' ; [ eassumption |].
      eapply All_Forall.
      eapply All_impl ; [ eassumption |].
      intros x0 H1 y0 H2. cbn in H1.
      eapply H1. all: assumption.
    - cbn. constructor ; try sih ; try assumption.
      eapply Forall2_map. eapply Forall2_impl' ; [ eassumption |].
      eapply All_Forall. eapply All_impl ; [ eassumption |].
      intros ? H0 ? [? ?]. cbn in H0. repeat split ; auto.
      eapply H0. all: assumption.
    - cbn. constructor.
      eapply Forall2_map. eapply Forall2_impl' ; [ eassumption |].
      eapply All_Forall. eapply All_impl ; [ eassumption |].
      intros ? [h1 h2] ? [? [? ?]].
      repeat split ; auto.
      + eapply h1. all: assumption.
      + apply Forall2_length in H. rewrite H.
        eapply h2. all: assumption.
    - cbn. constructor.
      eapply Forall2_map. eapply Forall2_impl' ; [ eassumption |].
      eapply All_Forall. eapply All_impl ; [ eassumption |].
      intros ? [h1 h2] ? [? [? ?]].
      repeat split ; auto.
      + eapply h1. all: assumption.
      + apply Forall2_length in H. rewrite H.
        eapply h2. all: assumption.
  Admitted.

  (* TODO MOVE *)
  Lemma red1_eq_term_upto_univ_l :
    forall R Γ u v u',
      Reflexive R ->
      eq_term_upto_univ R u u' ->
      red1 Σ Γ u v ->
      exists v',
        ∥ red1 Σ Γ u' v' ∥ /\
        eq_term_upto_univ R v v'.
  Proof.
    intros R Γ u v u' hR e h.
    induction h in u', e |- *.
    - dependent destruction e. dependent destruction e1.
      eexists. split.
      + constructor. constructor.
      + eapply eq_term_upto_univ_subst ; assumption.
    - dependent destruction e.
      eexists. split.
      + constructor. constructor.
      + eapply eq_term_upto_univ_subst ; assumption.
    - dependent destruction e.
      eexists. split.
      + constructor. constructor. eassumption.
      + eapply eq_term_upto_univ_refl. assumption.
    - dependent destruction e.
      apply eq_term_upto_univ_mkApps_l_inv in e2 as [? [? [h1 [h2 h3]]]]. subst.
      dependent destruction h1.
      eexists. split.
      + constructor. constructor.
      + eapply eq_term_upto_univ_mkApps.
        * eapply Forall2_nth with (P := fun x y => eq_term_upto_univ R (snd x) (snd y)).
          -- eapply Forall2_impl ; [ eassumption |].
             intros x y [? ?]. assumption.
          -- cbn. eapply eq_term_upto_univ_refl. assumption.
        * eapply Forall2_skipn. assumption.
    - apply eq_term_upto_univ_mkApps_l_inv in e as [? [? [h1 [h2 h3]]]]. subst.
      dependent destruction h1.
      unfold unfold_fix in e0.
      case_eq (nth_error mfix idx) ;
        try (intros e ; rewrite e in e0 ; discriminate e0).
      intros d e. rewrite e in e0. inversion e0. subst. clear e0.
      eapply Forall2_nth_error_Some_l in H as hh ; try eassumption.
      destruct hh as [d' [e' [? [? erarg]]]].
      unfold is_constructor in e1.
      case_eq (nth_error args (rarg d)) ;
        try (intros bot ; rewrite bot in e1 ; discriminate e1).
      intros a ea. rewrite ea in e1.
      eapply Forall2_nth_error_Some_l in h2 as hh ; try eassumption.
      destruct hh as [a' [ea' ?]].
      eexists. split.
      + constructor. eapply red_fix.
        * unfold unfold_fix. rewrite e'. reflexivity.
        * unfold is_constructor. rewrite <- erarg. rewrite ea'.
          eapply isConstruct_app_eq_term_l ; eassumption.
      + eapply eq_term_upto_univ_mkApps.
        * eapply eq_term_upto_univ_substs.
          -- assumption.
          --
  Admitted.

  Lemma cored_eq_term_upto_univ_r :
    forall R Γ u v u',
      Reflexive R ->
      eq_term_upto_univ R u u' ->
      cored Σ Γ v u ->
      exists v',
        cored Σ Γ v' u' /\
        eq_term_upto_univ R v v'.
  Proof.
    intros R Γ u v u' hR e h.
    induction h.
    - eapply red1_eq_term_upto_univ_l in X ; try eassumption.
      destruct X as [v' [[r] e']].
      exists v'. split ; auto.
      constructor. assumption.
    - specialize (IHh e). destruct IHh as [v' [c ev]].
      eapply red1_eq_term_upto_univ_l in X ; try eassumption.
      destruct X as [w' [[?] ?]].
      exists w'. split ; auto.
      eapply cored_trans ; eauto.
  Qed.

  Lemma cored_nl :
    forall Γ u v,
      cored Σ Γ u v ->
      cored (nlg Σ) (nlctx Γ) (nl u) (nl v).
  Admitted.

  Lemma red_nl :
    forall Γ u v,
      red Σ Γ u v ->
      red (nlg Σ) (nlctx Γ) (nl u) (nl v).
  Admitted.

  Fixpoint nlstack (π : stack) : stack :=
    match π with
    | ε => ε

    | App u ρ =>
      App (nl u) (nlstack ρ)

    | Fix f n args ρ =>
      Fix (map (map_def_anon nl nl) f) n (map nl args) (nlstack ρ)

    | Case indn p brs ρ =>
      Case indn (nl p) (map (on_snd nl) brs) (nlstack ρ)

    | Prod_l na B ρ =>
      Prod_l nAnon (nl B) (nlstack ρ)

    | Prod_r na A ρ =>
      Prod_r nAnon (nl A) (nlstack ρ)

    | Lambda_ty na b ρ =>
      Lambda_ty nAnon (nl b) (nlstack ρ)

    | Lambda_tm na A ρ =>
      Lambda_tm nAnon (nl A) (nlstack ρ)

    | coApp t ρ =>
      coApp (nl t) (nlstack ρ)
    end.

  Lemma nlstack_appstack :
    forall args ρ,
      nlstack (appstack args ρ) = appstack (map nl args) (nlstack ρ).
  Proof.
    intros args ρ.
    induction args in ρ |- *.
    - reflexivity.
    - simpl. f_equal. eapply IHargs.
  Qed.

  Lemma nlstack_cat :
    forall ρ θ,
      nlstack (ρ +++ θ) = nlstack ρ +++ nlstack θ.
  Proof.
    intros ρ θ.
    induction ρ in θ |- *.
    all: solve [ simpl ; rewrite ?IHρ ; reflexivity ].
  Qed.

  Lemma stack_position_nlstack :
    forall ρ,
      stack_position (nlstack ρ) = stack_position ρ.
  Proof.
    intros ρ.
    induction ρ.
    all: (simpl ; rewrite ?IHρ ; reflexivity).
  Qed.

  Lemma nl_it_mkLambda_or_LetIn :
    forall Γ t,
      nl (it_mkLambda_or_LetIn Γ t) =
      it_mkLambda_or_LetIn (nlctx Γ) (nl t).
  Proof.
    intros Γ t.
    induction Γ as [| [na [b|] B] Γ ih] in t |- *.
    - reflexivity.
    - simpl. cbn. rewrite ih. reflexivity.
    - simpl. cbn. rewrite ih. reflexivity.
  Qed.

  Lemma nl_mkApps :
    forall t l,
      nl (mkApps t l) = mkApps (nl t) (map nl l).
  Proof.
    intros t l.
    induction l in t |- *.
    - reflexivity.
    - simpl. rewrite IHl. reflexivity.
  Qed.

  Lemma nl_zipc :
    forall t π,
      nl (zipc t π) = zipc (nl t) (nlstack π).
  Proof.
    intros t π.
    induction π in t |- *.
    all: try solve [ simpl ; rewrite ?IHπ ; reflexivity ].
    simpl. rewrite IHπ. cbn. f_equal.
    rewrite nl_mkApps. reflexivity.
  Qed.

  Lemma nl_zipx :
    forall Γ t π,
      nl (zipx Γ t π) = zipx (nlctx Γ) (nl t) (nlstack π).
  Proof.
    intros Γ t π.
    unfold zipx. rewrite nl_it_mkLambda_or_LetIn. f_equal.
    apply nl_zipc.
  Qed.

  Lemma nlctx_app_context :
    forall Γ Δ,
      nlctx (Γ ,,, Δ) = nlctx Γ ,,, nlctx Δ.
  Proof.
    intros Γ Δ.
    induction Δ as [| [na [b|] B] Δ ih] in Γ |- *.
    - reflexivity.
    - simpl. f_equal. apply ih.
    - simpl. f_equal. apply ih.
  Qed.

  Lemma nlctx_stack_context :
    forall ρ,
      nlctx (stack_context ρ) = stack_context (nlstack ρ).
  Proof.
    intro ρ. induction ρ.
    all: (simpl ; rewrite ?IHρ ; reflexivity).
  Qed.

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

    Lemma inversion_LetIn :
    forall {Γ na b B t T},
      Σ ;;; Γ |- tLetIn na b B t : T ->
      exists s1 A,
        ∥ Σ ;;; Γ |- B : tSort s1 ∥ /\
        ∥ Σ ;;; Γ |- b : B ∥ /\
        ∥ Σ ;;; Γ ,, vdef na b B |- t : A ∥ /\
        ∥ Σ ;;; Γ |- tLetIn na b B A <= T ∥.
  Proof.
    intros Γ na b B t T h. dependent induction h.
    - exists s1, b'_ty. split ; [| split ; [| split]].
      + constructor. assumption.
      + constructor. assumption.
      + constructor. assumption.
      + constructor. apply cumul_refl'.
    - destruct IHh as [s1 [A' [? [? [? hc]]]]].
      exists s1, A'. split ; [| split ; [| split]].
      all: try assumption.
      destruct hc.
      constructor. eapply cumul_trans ; eassumption.
  Qed.

  Lemma welltyped_it_mkLambda_or_LetIn :
    forall Γ Δ t,
      welltyped Σ Γ (it_mkLambda_or_LetIn Δ t) ->
      welltyped Σ (Γ ,,, Δ) t.
  Proof.
    intros Γ Δ t h.
    revert Γ t h.
    induction Δ as [| [na [b|] A] Δ ih ] ; intros Γ t h.
    - assumption.
    - simpl. apply ih in h. cbn in h.
      destruct h as [T h].
      pose proof (inversion_LetIn h) as [s1 [A' [[?] [[?] [[?] [?]]]]]].
      exists A'. assumption.
    - simpl. apply ih in h. cbn in h.
      destruct h as [T h].
      pose proof (inversion_Lambda h) as [s1 [B [[?] [[?] [?]]]]].
      exists B. assumption.
  Qed.

  Lemma welltyped_zipp :
    forall Γ t ρ,
      welltyped Σ Γ (zipp t ρ) ->
      welltyped Σ Γ t.
  Proof.
    intros Γ t ρ [A h].
    unfold zipp in h.
    case_eq (decompose_stack ρ). intros l π e.
    rewrite e in h. clear - h.
    revert t A h.
    induction l ; intros t A h.
    - eexists. cbn in h. eassumption.
    - cbn in h. apply IHl in h.
      destruct h as [T h].
      destruct (inversion_App h) as [na [A' [B' [[?] [[?] [?]]]]]].
      eexists. eassumption.
  Qed.

  Lemma welltyped_zippx :
    forall Γ t ρ,
      welltyped Σ Γ (zippx t ρ) ->
      welltyped Σ (Γ ,,, stack_context ρ) t.
  Proof.
    intros Γ t ρ h.
    unfold zippx in h.
    case_eq (decompose_stack ρ). intros l π e.
    rewrite e in h.
    apply welltyped_it_mkLambda_or_LetIn in h.
    pose proof (decompose_stack_eq _ _ _ e). subst.
    rewrite stack_context_appstack.
    clear - h. destruct h as [A h].
    revert t A h.
    induction l ; intros t A h.
    - eexists. eassumption.
    - cbn in h. apply IHl in h.
      destruct h as [B h].
      destruct (inversion_App h) as [na [A' [B' [[?] [[?] [?]]]]]].
      eexists. eassumption.
  Qed.

  Derive NoConfusion NoConfusionHom for list.

  Lemma it_mkLambda_or_LetIn_welltyped :
    forall Γ Δ t,
      welltyped Σ (Γ ,,, Δ) t ->
      welltyped Σ Γ (it_mkLambda_or_LetIn Δ t).
  Proof.
    intros Γ Δ t h.
    revert Γ t h.
    induction Δ as [| [na [b|] B] Δ ih ] ; intros Γ t h.
    - assumption.
    - simpl. eapply ih. cbn.
      destruct h as [A h].
      pose proof (typing_wf_local h) as hc.
      cbn in hc. dependent destruction hc.
      + cbn in H. inversion H.
      + cbn in H. symmetry in H. inversion H. subst. clear H.
        cbn in l.
        eexists. econstructor ; try eassumption.
        (* FIXME We need to sort B, but we only know it's a type.
           It might be a problem with the way context are wellformed.
           Let typing asks for the type to be sorted so it should
           also hold in the context.
           At least they should be synchronised.
         *)
        admit.
    - simpl. eapply ih. cbn.
      destruct h as [A h].
      pose proof (typing_wf_local h) as hc.
      cbn in hc. dependent destruction hc.
      + cbn in H. symmetry in H. inversion H. subst. clear H.
        destruct l as [s hs].
        eexists. econstructor ; eassumption.
      + cbn in H. inversion H.
  Admitted.

  Lemma zipx_welltyped :
    forall {Γ t π},
      welltyped Σ Γ (zipc t π) ->
      welltyped Σ [] (zipx Γ t π).
  Proof.
    intros Γ t π h.
    eapply it_mkLambda_or_LetIn_welltyped.
    rewrite app_context_nil_l.
    assumption.
  Qed.

  Lemma welltyped_zipx :
    forall {Γ t π},
      welltyped Σ [] (zipx Γ t π) ->
      welltyped Σ Γ (zipc t π).
  Proof.
    intros Γ t π h.
    apply welltyped_it_mkLambda_or_LetIn in h.
    rewrite app_context_nil_l in h.
    assumption.
  Qed.

  Lemma welltyped_zipc_zippx :
    forall Γ t π,
      welltyped Σ Γ (zipc t π) ->
      welltyped Σ Γ (zippx t π).
  Proof.
    intros Γ t π h.
    unfold zippx.
    case_eq (decompose_stack π). intros l ρ e.
    pose proof (decompose_stack_eq _ _ _ e). subst.
    eapply it_mkLambda_or_LetIn_welltyped.
    rewrite zipc_appstack in h. zip fold in h.
    apply welltyped_context in h. assumption.
  Qed.

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

  Lemma context_conversion :
    forall {Γ t T Γ'},
      Σ ;;; Γ |- t : T ->
      PCUICSR.conv_context Σ Γ Γ' ->
      Σ ;;; Γ' |- t : T.
  Admitted.

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

  Lemma isAppProd_isProd :
    forall Γ t,
      isAppProd t ->
      welltyped Σ Γ t ->
      isProd t.
  Proof.
    intros Γ t hp hw.
    revert Γ hp hw.
    induction t ; intros Γ hp hw.
    all: try discriminate hp.
    - reflexivity.
    - simpl in hp.
      specialize IHt1 with (1 := hp).
      assert (welltyped Σ Γ t1) as h.
      { destruct hw as [T h].
        destruct (inversion_App h) as [na [A' [B' [[?] [[?] [?]]]]]].
        eexists. eassumption.
      }
      specialize IHt1 with (1 := h).
      destruct t1.
      all: try discriminate IHt1.
      destruct hw as [T hw'].
      destruct (inversion_App hw') as [na [A' [B' [[hP] [[?] [?]]]]]].
      destruct (inversion_Prod hP) as [s1 [s2 [[?] [[?] [bot]]]]].
      (* dependent destruction bot. *)
      (* + discriminate e. *)
      (* + dependent destruction r. *)
      admit.
  Admitted.

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

  Lemma eq_term_it_mkLambda_or_LetIn_inv :
    forall Γ u v,
      eq_term (snd Σ) (it_mkLambda_or_LetIn Γ u) (it_mkLambda_or_LetIn Γ v) ->
      eq_term (snd Σ) u v.
  Proof.
    intros Γ.
    induction Γ as [| [na [b|] A] Γ ih ] ; intros u v h.
    - assumption.
    - simpl in h. cbn in h. apply ih in h. inversion h. subst.
      assumption.
    - simpl in h. cbn in h. apply ih in h. inversion h. subst.
      assumption.
  Qed.

  Lemma eq_term_zipc_inv :
    forall u v π,
      eq_term (snd Σ) (zipc u π) (zipc v π) ->
      eq_term (snd Σ) u v.
  Proof.
    intros u v π h.
    revert u v h. induction π ; intros u v h.
    all: solve [
      simpl in h ; try apply IHπ in h ;
      cbn in h ; inversion h ; subst ; assumption
    ].
  Qed.

  Lemma eq_term_zipx_inv :
    forall Γ u v π,
      eq_term (snd Σ) (zipx Γ u π) (zipx Γ v π) ->
      eq_term (snd Σ) u v.
  Proof.
    intros Γ u v π h.
    eapply eq_term_zipc_inv.
    eapply eq_term_it_mkLambda_or_LetIn_inv.
    eassumption.
  Qed.

  Lemma eq_term_it_mkLambda_or_LetIn :
    forall Γ u v,
      eq_term (snd Σ) u v ->
      eq_term (snd Σ) (it_mkLambda_or_LetIn Γ u) (it_mkLambda_or_LetIn Γ v).
  Proof.
    intros Γ.
    induction Γ as [| [na [b|] A] Γ ih ] ; intros u v h.
    - assumption.
    - simpl. cbn. apply ih. constructor ; try apply eq_term_refl. assumption.
    - simpl. cbn. apply ih. constructor ; try apply eq_term_refl. assumption.
  Qed.

  Lemma eq_term_zipc :
    forall u v π,
      eq_term (snd Σ) u v ->
      eq_term (snd Σ) (zipc u π) (zipc v π).
  Proof.
    intros u v π h.
    revert u v h. induction π ; intros u v h.
    all: try solve [
      simpl ; try apply IHπ ;
      cbn ; constructor ; try apply eq_term_refl ; assumption
    ].
    - assumption.
    - simpl. apply IHπ. destruct indn as [i n].
      constructor.
      + apply eq_term_refl.
      + assumption.
      + eapply Forall_Forall2. eapply Forall_True.
        intros. split ; auto. apply eq_term_refl.
  Qed.

  Lemma eq_term_zipx :
    forall Γ u v π,
      eq_term (snd Σ) u v ->
      eq_term (snd Σ) (zipx Γ u π) (zipx Γ v π).
  Proof.
    intros Γ u v π h.
    eapply eq_term_it_mkLambda_or_LetIn.
    eapply eq_term_zipc.
    eassumption.
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

  Lemma eq_term_trans :
    forall G u v w,
      eq_term G u v ->
      eq_term G v w ->
      eq_term G u w.
  Admitted.

  Lemma nl_subst_instance_constr :
    forall u b,
      nl (subst_instance_constr u b) = subst_instance_constr u (nl b).
  Proof.
    intros u b.
    induction b using term_forall_list_ind.
    all: try (simpl ; rewrite ?IHb, ?IHb1, ?IHb2, ?IHb3 ; reflexivity).
    - simpl. f_equal. induction H.
      + reflexivity.
      + simpl. rewrite p, IHAll. reflexivity.
    - simpl. rewrite IHb1, IHb2. f_equal.
      induction X.
      + reflexivity.
      + simpl. f_equal.
        * unfold on_snd. destruct p, x. simpl in *.
          rewrite p0. reflexivity.
        * apply IHX.
    - simpl. f_equal. induction X ; try reflexivity.
      simpl. rewrite IHX. f_equal.
      destruct p as [h1 h2].
      destruct x. simpl in *.
      unfold map_def, map_def_anon. cbn.
      rewrite h1, h2. reflexivity.
    - simpl. f_equal. induction X ; try reflexivity.
      simpl. rewrite IHX. f_equal.
      destruct p as [h1 h2].
      destruct x. simpl in *.
      unfold map_def, map_def_anon. cbn.
      rewrite h1, h2. reflexivity.
  Qed.

  Lemma positionR_context_position_inv :
    forall Γ p q,
      positionR (context_position Γ ++ p) (context_position Γ ++ q) ->
      positionR p q.
  Proof.
    intros Γ p q h.
    revert p q h.
    induction Γ as [| [na [b|] A] Γ ih ] ; intros p q h.
    - assumption.
    - cbn in h. rewrite <- 2!app_assoc in h. apply ih in h.
      cbn in h. dependent destruction h.
      assumption.
    - cbn in h. rewrite <- 2!app_assoc in h. apply ih in h.
      cbn in h. dependent destruction h.
      assumption.
  Qed.

  Lemma positionR_xposition_inv :
    forall Γ ρ1 ρ2,
      positionR (xposition Γ ρ1) (xposition Γ ρ2) ->
      positionR (stack_position ρ1) (stack_position ρ2).
  Proof.
    intros Γ ρ1 ρ2 h.
    eapply positionR_context_position_inv.
    eassumption.
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

  Lemma context_position_nlctx :
    forall Γ,
      context_position (nlctx Γ) = context_position Γ.
  Proof.
    intros Γ. induction Γ as [| [na [b|] A] Γ ih ].
    - reflexivity.
    - simpl. rewrite ih. reflexivity.
    - simpl. rewrite ih. reflexivity.
  Qed.

  Lemma xposition_nlctx :
    forall Γ π,
      xposition (nlctx Γ) π = xposition Γ π.
  Proof.
    intros Γ π.
    unfold xposition.
    rewrite context_position_nlctx.
    reflexivity.
  Qed.

  Lemma xposition_nlstack :
    forall Γ π,
      xposition Γ (nlstack π) = xposition Γ π.
  Proof.
    intros Γ π.
    unfold xposition.
    rewrite stack_position_nlstack.
    reflexivity.
  Qed.

  Lemma nleq_term_it_mkLambda_or_LetIn :
    forall Γ u v,
      nleq_term u v ->
      nleq_term (it_mkLambda_or_LetIn Γ u) (it_mkLambda_or_LetIn Γ v).
  Proof.
    intros Γ u v h.
    induction Γ as [| [na [b|] A] Γ ih ] in u, v, h |- *.
    - assumption.
    - simpl. cbn. apply ih.
      eapply ssrbool.introT.
      + eapply reflect_nleq_term.
      + cbn. f_equal.
        eapply ssrbool.elimT.
        * eapply reflect_nleq_term.
        * assumption.
    - simpl. cbn. apply ih.
      eapply ssrbool.introT.
      + eapply reflect_nleq_term.
      + cbn. f_equal.
        eapply ssrbool.elimT.
        * eapply reflect_nleq_term.
        * assumption.
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

  Lemma type_it_mkLambda_or_LetIn :
    forall Γ Δ t A,
      Σ ;;; Γ ,,, Δ |- t : A ->
      Σ ;;; Γ |- it_mkLambda_or_LetIn Δ t : it_mkProd_or_LetIn Δ A.
  Proof.
    intros Γ Δ t A h.
    induction Δ as [| [na [b|] B] Δ ih ] in t, A, h |- *.
    - assumption.
    - simpl. cbn. eapply ih.
      simpl in h. pose proof (typing_wf_local h) as hc.
      dependent induction hc ; inversion H. subst.
      econstructor ; try eassumption.
      (* FIXME *)
      admit.
    - simpl. cbn. eapply ih.
      pose proof (typing_wf_local h) as hc. cbn in hc.
      dependent induction hc ; inversion H. subst.
      econstructor ; try eassumption.
      (* FIXME *)
      admit.
  Admitted.

  (* Lemma principle_typing : *)
  (*   forall {Γ u A B}, *)
  (*     Σ ;;; Γ |- u : A -> *)
  (*     Σ ;;; Γ |- u : B -> *)
  (*     { C & (Σ ;;; Γ |- C <= A) * (Σ ;;; Γ |- C <= B) * (Σ ;;; Γ |- u : C) }%type. *)
  (* Admitted. *)

  (* Lemma subj_cumul : *)
  (*   forall {Γ u v A B}, *)
  (*     Σ ;;; Γ |- u <= v -> *)
  (*     Σ ;;; Γ |- u : A -> *)
  (*     Σ ;;; Γ |- v : B -> *)
  (*     Σ ;;; Γ |- u : B. *)
  (* Proof. *)
  (*   intros Γ u v A B h hu hv. *)
  (*   induction h in A, hu, B, hv |- *. *)
  (*   - admit. *)
  (*   -  *)

  (* Maybe this one is wrong *)
  (* Lemma subj_conv : *)
  (*   forall {Γ u v U V}, *)
  (*     Σ ;;; Γ |- u = v -> *)
  (*     Σ ;;; Γ |- u : U -> *)
  (*     Σ ;;; Γ |- v : V -> *)
  (*     Σ ;;; Γ |- U = V. *)
  (* Admitted. *)

  (* Lemma welltyped_zipc_change_hole : *)
  (*   forall Γ u v π, *)
  (*     welltyped Σ Γ (zipc u π) -> *)
  (*     welltyped Σ (Γ ,,, stack_context π) v -> *)
  (*     Σ ;;; Γ ,,, stack_context π |- u = v -> *)
  (*     welltyped Σ Γ (zipc v π). *)
  (* Proof. *)
  (*   intros Γ u v π h hv e. *)
  (*   induction π in u, v, h, hv, e |- *. *)
  (*   - assumption. *)
  (*   - cbn. *)
  (*     eapply IHπ. *)
  (*     + exact h. *)
  (*     + *)

  (* Lemma welltyped_zipc_change_hole : *)
  (*   forall Γ u v π A, *)
  (*     welltyped Σ Γ (zipc u π) -> *)
  (*     Σ ;;; Γ ,,, stack_context π |- u : A -> *)
  (*     Σ ;;; Γ ,,, stack_context π |- v : A -> *)
  (*     welltyped Σ Γ (zipc v π). *)
  (* Proof. *)
  (*   intros Γ u v π A h hu hv. *)
  (*   induction π in u, v, A, h, hu, hv |- *. *)
  (*   - econstructor. eassumption. *)
  (*   - cbn. *)
  (*     pose proof h as h'. cbn in h'. zip fold in h'. *)
  (*     apply welltyped_context in h'. simpl in h'. *)
  (*     destruct h' as [B h']. *)
  (*     destruct (inversion_App h') as [na [A' [B' [[hu'] [[?] [?]]]]]]. *)
  (*     simpl in hu, hv. *)
  (*     destruct (principle_typing hu hu') as [C [[? ?] ?]]. *)
  (*     eapply IHπ. *)
  (*     + exact h. *)
  (*     + eassumption. *)
  (*     + econstructor. all: try eassumption. *)
  (*       * econstructor ; try eassumption. *)

End Lemmata.