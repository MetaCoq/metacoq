(* Distributed under the terms of the MIT license.   *)
Require Import ssreflect ssrbool.
From MetaCoq.Template Require Import LibHypsNaming.
From Equations Require Import Equations.
From Coq Require Import Bool String List Program BinPos Compare_dec Omega Utf8 String Lia.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICReduction PCUICWeakening PCUICSubstitution
     PCUICReflect PCUICClosed PCUICParallelReduction PCUICParallelReductionConfluence.

(* Type-valued relations. *)
Require Import CRelationClasses.
Require Import Equations.Type.Relation Equations.Type.Relation_Properties.

Set Asymmetric Patterns.

Notation "'∃' x .. y , P" := (sigT (fun x => .. (sigT (fun y => P%type)) ..))
  (at level 200, x binder, y binder, right associativity,
  format "'[  ' '[  ' ∃  x  ..  y ']' ,  '/' P ']'") : type_scope.

Existing Instance config.default_checker_flags.

Lemma local_env_telescope P Γ Γ' Δ Δ' :
  All2_telescope (on_decl P) Γ Γ' Δ Δ' ->
  All2_local_env_over P Γ Γ' (List.rev Δ) (List.rev Δ').
Proof.
  induction 1. simpl. constructor.
  - simpl. eapply All2_local_env_over_app. constructor. constructor.
    simpl. apply p.
    revert IHX.
    generalize (List.rev Δ) (List.rev Δ'). induction 1. constructor.
    constructor. auto. red in p0. red. red. red. red in p0.
    rewrite !app_context_assoc. cbn. apply p0.
    constructor. auto. destruct p0. unfold on_decl_over in *. simpl.
    rewrite !app_context_assoc. cbn. intuition.
  - simpl. eapply All2_local_env_over_app. constructor. constructor.
    simpl. unfold on_decl_over, on_decl in *. destruct p. split; intuition auto.
    revert IHX.
    generalize (List.rev Δ) (List.rev Δ'). induction 1. constructor.
    constructor. auto. red in p0. red. red. red. red in p0.
    rewrite !app_context_assoc. cbn. apply p0.
    constructor. auto. destruct p0. unfold on_decl_over in *. simpl.
    rewrite !app_context_assoc. cbn. intuition.
Qed.

Lemma mapi_rec_compose {A B C} (g : nat -> B -> C) (f : nat -> A -> B) k l :
  mapi_rec g (mapi_rec f l k) k = mapi_rec (fun k x => g k (f k x)) l k.
Proof.
  induction l in k |- *; simpl; auto. now rewrite IHl.
Qed.

Lemma mapi_compose {A B C} (g : nat -> B -> C) (f : nat -> A -> B) l :
  mapi g (mapi f l) = mapi (fun k x => g k (f k x)) l.
Proof. apply mapi_rec_compose. Qed.

Lemma mapi_cst_map {A B} (f : A -> B) l : mapi (fun _ => f) l = map f l.
Proof. unfold mapi. generalize 0. induction l; cbn; auto. intros. now rewrite IHl. Qed.

Lemma All_All2_telescopei_gen P (Γ Γ' Δ Δ' : context) (m m' : mfixpoint term) :
  (forall Δ Δ' x y,
    All2_local_env_over P Γ Γ' Δ Δ' ->
    P Γ Γ' x y ->
    P (Γ ,,, Δ) (Γ' ,,, Δ') (lift0 #|Δ| x) (lift0 #|Δ'| y)) ->
  All2 (on_Trel_eq (P Γ Γ') dtype dname) m m' ->
  All2_local_env_over P Γ Γ' Δ Δ' ->
  All2_telescope_n (on_decl P) (fun n : nat => lift0 n)
                   (Γ ,,, Δ) (Γ' ,,, Δ') #|Δ|
    (map (fun def : def term => vass (dname def) (dtype def)) m)
    (map (fun def : def term => vass (dname def) (dtype def)) m').
Proof.
  intros weakP.
  induction 1 in Δ, Δ' |- *; cbn. constructor.
  intros. destruct r. rewrite e. constructor.
  red.
  rewrite {2}(All2_local_env_length X0).
  now eapply weakP.
  specialize (IHX (vass (dname y) (lift0 #|Δ| (dtype x)) :: Δ)
                  (vass (dname y) (lift0 #|Δ'| (dtype y)) :: Δ')%list).
  forward IHX.
  constructor; auto. now eapply weakP. simpl in IHX.
  rewrite {2}(All2_local_env_length X0).
  apply IHX.
Qed.

Lemma All_All2_telescopei P (Γ Γ' : context) (m m' : mfixpoint term) :
  (forall Δ Δ' x y,
    All2_local_env_over P Γ Γ' Δ Δ' ->
    P Γ Γ' x y ->
    P (Γ ,,, Δ) (Γ' ,,, Δ') (lift0 #|Δ| x) (lift0 #|Δ'| y)) ->
  All2 (on_Trel_eq (P Γ Γ') dtype dname) m m' ->
  All2_telescope_n (on_decl P) (λ n : nat, lift0 n)
                   Γ Γ' 0
                   (map (λ def : def term, vass (dname def) (dtype def)) m)
                   (map (λ def : def term, vass (dname def) (dtype def)) m').
Proof.
  specialize (All_All2_telescopei_gen P Γ Γ' [] [] m m'). simpl.
  intros. specialize (X X0 X1). apply X; constructor.
Qed.

Lemma All2_All2_local_env_fix_context P (Γ Γ' : context) (m m' : mfixpoint term) :
  (forall Δ Δ' x y,
    All2_local_env_over P Γ Γ' Δ Δ' ->
    P Γ Γ' x y ->
    P (Γ ,,, Δ) (Γ' ,,, Δ') (lift0 #|Δ| x) (lift0 #|Δ'| y)) ->
  All2 (on_Trel_eq (P Γ Γ') dtype dname) m m' ->
  All2_local_env (on_decl (on_decl_over P Γ Γ')) (fix_context m) (fix_context m').
Proof.
  intros Hweak a. unfold fix_context.
  eapply local_env_telescope.
  cbn.
  rewrite - !(mapi_compose
                (fun n decl => lift_decl n 0 decl)
                (fun n def => vass (dname def) (dtype def))).
  eapply All2_telescope_mapi.
  rewrite !mapi_cst_map.
  eapply All_All2_telescopei; eauto.
Qed.

Section RedPred.
  Context {Σ : global_context}.
  Context (wfΣ : wf Σ).

  Hint Resolve pred1_ctx_over_refl : pcuic.
  Hint Unfold All2_prop2_eq : pcuic.
  Hint Transparent context : pcuic.
  Hint Transparent mfixpoint : pcuic.

  Hint Mode pred1 ! ! ! ! - : pcuic.

  Ltac pcuic := simpl; try typeclasses eauto with pcuic.

  (** Strong substitutivity gives context conversion of reduction!
      Need to strengthen to allow pred1 of let-ins.
   *)

  Lemma pred1_ctx_pred1 Γ Δ Δ' t u :
    pred1 Σ (Γ ,,, Δ) (Γ ,,, Δ) t u ->
    assumption_context Δ ->
    pred1_ctx Σ (Γ ,,, Δ) (Γ ,,, Δ') ->
    pred1 Σ (Γ ,,, Δ) (Γ ,,, Δ') t u.
  Proof.
    intros.
    pose proof (strong_substitutivity _ wfΣ _ _ (Γ ,,, Δ) (Γ ,,, Δ') _ _ ids ids X).
    forward X1.
    { red. intros.
      destruct (leb_spec_Set (S x) #|Δ|).
      rewrite nth_error_app_lt in H0. lia.
      apply nth_error_assumption_context in H0 => //; rewrite H0 //.
      case e: (decl_body d) => [b|] //. eexists x, _; intuition eauto.
      now rewrite H0 /= e. }
    forward X1.
    { red. intros.
      destruct (leb_spec_Set (S x) #|Δ|).
      rewrite nth_error_app_lt in H0. lia.
      apply nth_error_assumption_context in H0 => //; rewrite H0 //.
      case e: (decl_body d) => [b|] //. eexists x, _; intuition eauto.
      rewrite nth_error_app_ge in H0 |- *; try lia.
      eapply All2_local_env_app in X0 as [_ X0] => //.
      pose proof (All2_local_env_length X0).
      rewrite nth_error_app_ge. lia. now rewrite -H1 H0 /= e. }
    forward X1.
    red. intros x; split. eapply pred1_refl_gen; auto.
    destruct option_map as [[o|]|]; auto.
    now rewrite !subst_ids in X1.
  Qed.

  Lemma red1_pred1 Γ : forall M N, red1 Σ Γ M N -> pred1 Σ Γ Γ M N.
  Proof with pcuic.
    induction 1 using red1_ind_all; intros; pcuic.
    - constructor; pcuic.
      unfold on_Trel_eq, on_Trel.
      (* TODO fix OnOne2 use in red1 to use onTrel_eq to have equality on annotation *)
      eapply OnOne2_All2 ... intros x y X0. simpl in X0.
      intuition auto. admit.
    - constructor; pcuic.
      eapply OnOne2_All2...
    - constructor; pcuic.
      + apply All2_All2_local_env_fix_context.
        now intros; eapply weakening_pred1_pred1.
        (* Missing name equality *)
        eapply OnOne2_All2...
        intros. unfold on_Trel_eq, on_Trel.
        simpl in *. intuition auto.
        admit.
      + eapply OnOne2_All2; pcuic; simpl;
        unfold on_Trel_eq, on_Trel;
        intuition auto. rewrite b0; pcuic.
        apply pred1_refl_gen.
        eapply All2_local_env_app_inv; pcuic.
        apply All2_All2_local_env_fix_context.
        now intros; eapply weakening_pred1_pred1.
        (* Missing name equality *)
        eapply OnOne2_All2...
        intros.
        intros. unfold on_Trel_eq, on_Trel.
        simpl in *. intuition auto.
        admit. admit.

        pcuic.
        apply pred1_refl_gen; pcuic.
        eapply All2_local_env_app_inv; pcuic.
        apply All2_All2_local_env_fix_context.
        now intros; eapply weakening_pred1_pred1.
        (* Missing name equality *)
        eapply OnOne2_All2...
        intros.
        intros. unfold on_Trel_eq, on_Trel.
        simpl in *. intuition auto.
        admit.

    - constructor; pcuic.
      apply All2_All2_local_env_fix_context.
      now intros; eapply weakening_pred1_pred1.
      (* Missing name equality *)
      + eapply OnOne2_All2...
        intros.
        intros. unfold on_Trel_eq, on_Trel.
        simpl in *. intuition auto.
        rewrite b0; pcuic. admit.
      + eapply OnOne2_All2...
        intros.
        * intros. unfold on_Trel_eq, on_Trel.
          simpl in *. intuition auto.
          rewrite b0; pcuic.
          assert(fix_context mfix0 = fix_context mfix1).
          clear -X.
          unfold fix_context, mapi. generalize 0 at 2 4.
          induction X; intros. intuition auto. simpl. rewrite b0. do 3 f_equal.  admit.
          simpl; now rewrite IHX.
          now rewrite -H. admit.
        * intros. unfold on_Trel_eq, on_Trel.
          simpl in *. intuition pcuic.
          assert(fix_context mfix0 = fix_context mfix1).
          clear -X.
          unfold fix_context, mapi. generalize 0 at 2 4.
          induction X; intros. intuition auto. simpl. rewrite b0. do 3 f_equal.  admit.
          simpl; now rewrite IHX.
          rewrite -H. pcuic.

    - constructor; pcuic.
      apply All2_All2_local_env_fix_context.
      now intros; eapply weakening_pred1_pred1.
      + eapply OnOne2_All2...
        unfold on_Trel_eq, on_Trel.
        simpl in *. intuition pcuic. admit.
      + eapply OnOne2_All2...
        * unfold on_Trel_eq, on_Trel.
          simpl in *. intuition pcuic. rewrite -b0; pcuic.
          eapply pred1_ctx_pred1; pcuic.
          apply fix_context_assumption_context.
          apply All2_local_env_over_app. pcuic.
          apply All2_All2_local_env_fix_context.
          now intros; eapply weakening_pred1_pred1.
          eapply OnOne2_All2...
          unfold on_Trel_eq, on_Trel.
          simpl in *. intuition pcuic. admit.
          admit.
        * unfold on_Trel_eq, on_Trel.
          simpl in *. intuition pcuic.
          eapply pred1_ctx_pred1; pcuic.
          apply fix_context_assumption_context.
          apply All2_local_env_over_app. pcuic.
          apply All2_All2_local_env_fix_context.
          now intros; eapply weakening_pred1_pred1.
          eapply OnOne2_All2...
          unfold on_Trel_eq, on_Trel.
          simpl in *. intuition pcuic. admit.

    - constructor; pcuic.
      apply All2_All2_local_env_fix_context.
      now intros; eapply weakening_pred1_pred1.
      + eapply OnOne2_All2...
        unfold on_Trel_eq, on_Trel.
        simpl in *. intuition pcuic. rewrite b0; pcuic.
        admit.
      + eapply OnOne2_All2...
        * unfold on_Trel_eq, on_Trel.
          simpl in *. intuition pcuic. rewrite -b0; pcuic.
          assert(fix_context mfix0 = fix_context mfix1).
          { clear -X.
            unfold fix_context, mapi. generalize 0 at 2 4.
            induction X; intros. intuition auto. simpl. rewrite b0. do 3 f_equal.  admit.
            simpl; now rewrite IHX. }
          now rewrite -H. admit.
        * unfold on_Trel_eq, on_Trel.
          simpl in *. intuition pcuic.
          eapply pred1_ctx_pred1; pcuic.
          apply fix_context_assumption_context.
          apply All2_local_env_over_app. pcuic.
          apply All2_All2_local_env_fix_context.
          now intros; eapply weakening_pred1_pred1.
          eapply OnOne2_All2...
          unfold on_Trel_eq, on_Trel.
          simpl in *. intuition pcuic. rewrite b0; pcuic. admit.
  Admitted.

End RedPred.