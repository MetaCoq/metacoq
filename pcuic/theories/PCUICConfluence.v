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

  Ltac noconf H := repeat (DepElim.noconf H; simpl NoConfusion in * ).



  Lemma red1_pred1 Γ : forall M N, red1 Σ Γ M N -> pred1 Σ Γ Γ M N.
  Proof with pcuic.
    induction 1 using red1_ind_all; intros; pcuic.
    - econstructor; pcuic. eauto.
      unfold on_Trel.
      (* TODO fix OnOne2 use in red1 to use onTrel_eq to have equality on annotation *)
      eapply OnOne2_All2 ...
    - constructor; pcuic.
      eapply OnOne2_All2...
    - constructor; pcuic.
      + apply All2_All2_local_env_fix_context.
        now intros; eapply weakening_pred1_pred1.
        (* Missing name equality *)
        eapply OnOne2_All2...
        intros.
        simpl in *. intuition auto. now noconf b.
      + eapply OnOne2_All2; pcuic; simpl;
        unfold on_Trel; simpl; intros; intuition auto.
        noconf b; noconf H. rewrite H0. pcuic.
        apply pred1_refl_gen.
        eapply All2_local_env_app_inv; pcuic.
        apply All2_All2_local_env_fix_context.
        now intros; eapply weakening_pred1_pred1.
        (* Missing name equality *)
        eapply OnOne2_All2...
        intros.
        intros. unfold on_Trel.
        simpl in *. intuition auto.
        congruence. congruence.

        pcuic.
        apply pred1_refl_gen; pcuic.
        eapply All2_local_env_app_inv; pcuic.
        apply All2_All2_local_env_fix_context.
        now intros; eapply weakening_pred1_pred1.
        (* Missing name equality *)
        eapply OnOne2_All2...
        intros.
        intros. unfold on_Trel.
        simpl in *. intuition auto. congruence.

    - constructor; pcuic.
      apply All2_All2_local_env_fix_context.
      now intros; eapply weakening_pred1_pred1.
      (* Missing name equality *)
      + eapply OnOne2_All2...
        intros.
        intros. unfold on_Trel.
        simpl in *. intuition auto. noconf b. noconf H.
        rewrite H0; pcuic. congruence.
      + eapply OnOne2_All2...
        intros.
        * intros. unfold on_Trel.
          simpl in *. intuition auto. noconf b. noconf H. rewrite H0. pcuic.
          assert(fix_context mfix0 = fix_context mfix1).
          clear -X.
          unfold fix_context, mapi. generalize 0 at 2 4.
          induction X; intros. intuition auto. simpl.
          noconf b. noconf H. now rewrite H H0.
          simpl; now rewrite IHX.
          now rewrite -H. congruence.
        * intros. unfold on_Trel.
          simpl in *. intuition pcuic.
          assert(fix_context mfix0 = fix_context mfix1).
          clear -X.
          unfold fix_context, mapi. generalize 0 at 2 4.
          induction X; intros. intuition auto. simpl.
          noconf b; noconf H. now rewrite H H0.
          simpl; now rewrite IHX.
          rewrite -H. pcuic.

    - constructor; pcuic.
      apply All2_All2_local_env_fix_context.
      now intros; eapply weakening_pred1_pred1.
      (* Missing name equality *)
      + eapply OnOne2_All2...
        intros.
        intros. unfold on_Trel.
        simpl in *. intuition auto. noconf b. noconf H.
        rewrite H; pcuic.
      + eapply OnOne2_All2...
        * unfold on_Trel.
          simpl in *. intuition pcuic. noconf b; noconf H.
          rewrite -H0; pcuic.
          eapply pred1_ctx_pred1; pcuic.
          apply fix_context_assumption_context.
          apply All2_local_env_over_app. pcuic.
          apply All2_All2_local_env_fix_context.
          now intros; eapply weakening_pred1_pred1.
          eapply OnOne2_All2...
          unfold on_Trel.
          simpl in *. intuition pcuic. congruence. congruence.
        * unfold on_Trel.
          simpl in *. intuition pcuic.
          eapply pred1_ctx_pred1; pcuic.
          apply fix_context_assumption_context.
          apply All2_local_env_over_app. pcuic.
          apply All2_All2_local_env_fix_context.
          now intros; eapply weakening_pred1_pred1.
          eapply OnOne2_All2...
          unfold on_Trel.
          simpl in *. intuition pcuic. congruence.

    - constructor; pcuic.
      apply All2_All2_local_env_fix_context.
      now intros; eapply weakening_pred1_pred1.
      + eapply OnOne2_All2...
        unfold on_Trel.
        simpl in *. intuition pcuic. noconf b; noconf H; rewrite H0; pcuic.
        congruence.
      + eapply OnOne2_All2...
        * unfold on_Trel.
          simpl in *. intuition pcuic. noconf b; noconf H; rewrite H0; pcuic.
          assert(fix_context mfix0 = fix_context mfix1).
          { clear -X.
            unfold fix_context, mapi. generalize 0 at 2 4.
            induction X; intros. intuition auto. simpl. noconf b; noconf H. congruence.
            simpl; now rewrite IHX. }
          now rewrite -H. congruence.
        * unfold on_Trel.
          simpl in *. intuition pcuic.
          eapply pred1_ctx_pred1; pcuic.
          apply fix_context_assumption_context.
          apply All2_local_env_over_app. pcuic.
          apply All2_All2_local_env_fix_context.
          now intros; eapply weakening_pred1_pred1.
          eapply OnOne2_All2...
          unfold on_Trel.
          simpl in *. intuition pcuic.
          noconf b; noconf H; rewrite H0; pcuic. congruence.
  Qed.

End RedPred.

Existing Instance default_checker_flags.

Section PredRed.
  Context {Σ : global_context}.
  Context (wfΣ : wf Σ).

  Lemma weakening_red_0 Γ Γ' M N n :
    n = #|Γ'| ->
    red Σ Γ M N ->
    red Σ (Γ ,,, Γ') (lift0 n M) (lift0 n N).
  Proof. now move=> ->; apply (weakening_red Σ Γ [] Γ'). Qed.

  Lemma red_abs_alt Γ na M M' N N' : red Σ Γ M M' -> red Σ (Γ ,, vass na M) N N' ->
                                 red Σ Γ (tLambda na M N) (tLambda na M' N').
  Proof.
    intros. eapply (transitivity (y := tLambda na M N')).
    now eapply (red_ctx (tCtxLambda_r _ _ tCtxHole)).
    now eapply (red_ctx (tCtxLambda_l _ tCtxHole _)).
  Qed.

  Lemma red_letin_alt Γ na d0 d1 t0 t1 b0 b1 :
    red Σ Γ d0 d1 -> red Σ Γ t0 t1 -> red Σ (Γ ,, vdef na d0 t0) b0 b1 ->
    red Σ Γ (tLetIn na d0 t0 b0) (tLetIn na d1 t1 b1).
  Proof.
    intros; eapply (transitivity (y := tLetIn na d0 t0 b1)).
    now eapply (red_ctx (tCtxLetIn_r _ _ _ tCtxHole)).
    eapply (transitivity (y := tLetIn na d0 t1 b1)).
    now eapply (red_ctx (tCtxLetIn_b _ _ tCtxHole _)).
    now apply (red_ctx (tCtxLetIn_l _ tCtxHole _ _)).
  Qed.

  (** Parallel reduction is included in the reflexive transitive closure of 1-step reduction *)
  Lemma pred1_red Γ Γ' : forall M N, pred1 Σ Γ Γ' M N -> red Σ Γ M N.
  Proof.
    revert Γ Γ'. eapply (@pred1_ind_all_ctx Σ _
                                            (fun Γ Γ' =>
       All2_local_env (on_decl (fun Γ Γ' M N => pred1 Σ Γ Γ' M N -> red Σ Γ M N)) Γ Γ')%type);
                   intros; try constructor; pcuic.
    eapply All2_local_env_impl; eauto.
    - (* Contexts *)
      unfold on_decl => Δ Δ' t T U Hlen.
      destruct t; auto.
      destruct p; auto. intuition.

    - (* Beta *)
      apply red_trans with (tApp (tLambda na t0 b1) a0).
      eapply (@red_app Σ); [apply red_abs|]; auto with pcuic.
      apply red_trans with (tApp (tLambda na t0 b1) a1).
      eapply (@red_app Σ); auto with pcuic.
      apply red1_red. constructor.

    - (* Zeta *)
      eapply red_trans with (tLetIn na d0 t0 b1).
      eapply red_letin; eauto with pcuic.
      eapply red_trans with (tLetIn na d1 t1 b1).
      eapply red_letin; eauto with pcuic.
      eapply red1_red; constructor.

    - (* Rel in context *)
      eapply nth_error_pred1_ctx in X0; eauto.
      destruct X0 as [body' [Hnth Hpred]].
      eapply red_trans with (lift0 (S i) body').
      eapply red1_red; constructor; auto.
      eapply nth_error_pred1_ctx_all_defs in H; eauto.
      specialize (Hpred H).
      rewrite -(firstn_skipn (S i) Γ).
      eapply weakening_red_0 => //.
      rewrite firstn_length_le //.
      destruct nth_error eqn:Heq.
      eapply nth_error_Some_length in Heq. lia. noconf Hnth.

    - (* Iota *)
      transitivity (tCase (ind, pars) p (mkApps (tConstruct ind c u) args1) brs1).
      eapply red_case; auto.
      eapply red_mkApps. auto. solve_all. red in X2; solve_all.
      eapply red1_red. constructor.

    - move: H H0.
      move => unf isc.
      transitivity (mkApps (tFix mfix1 idx) args1).
      eapply red_mkApps. eapply red_fix_congr. red in X3. solve_all. eapply a.
      solve_all.
      eapply red_step. econstructor; eauto. eauto.

    - transitivity (tCase ip p1 (mkApps (tCoFix mfix1 idx) args1) brs1).
      eapply red_case; eauto.
      eapply red_mkApps; [|solve_all].
      eapply red_cofix_congr. red in X3; solve_all. eapply a0.
      red in X7; solve_all.
      eapply red_step. econstructor; eauto. eauto.

    - transitivity (tProj p (mkApps (tCoFix mfix1 idx) args1)).
      eapply red_proj_congr; eauto.
      eapply red_mkApps; [|solve_all].
      eapply red_cofix_congr. red in X3; solve_all. eapply a.
      eapply red_step. econstructor; eauto. eauto.

    - eapply red1_red. econstructor; eauto.

    - transitivity (tProj (i, pars, narg) (mkApps (tConstruct i k u) args1)).
      eapply red_proj_congr; eauto.
      eapply red_mkApps; [|solve_all]. auto.
      eapply red1_red. econstructor; eauto.

    - now eapply red_abs_alt.
    - now eapply red_app.
    - now eapply red_letin_alt => //.
    - eapply red_case => //. red in X3; solve_all.
    - now eapply red_proj_congr.
    - eapply red_fix_congr. red in X3; solve_all. eapply a.
    - eapply red_cofix_congr. red in X3; solve_all. eapply a.
    - eapply red_prod; auto.
    - eapply red_evar; auto. solve_all.
  Qed.

End PredRed.

Lemma clos_t_rt {A} {R : A -> A -> Type} x y : trans_clos R x y -> clos_refl_trans R x y.
Proof.
  induction 1; try solve [econstructor; eauto].
Qed.

Require Import CMorphisms.

Section AbstractConfluence.
  Section Diamond.
    Context {A : Type} (R : A -> A -> Type).
    Definition joinable (x y : A) := ∑ z, R x z * R y z.
    Definition diamond := forall x y z, R x y -> R x z -> joinable y z.
  End Diamond.

  Definition confluent {A} (R : relation A) := diamond (clos_refl_trans R).

  Instance joinable_proper A : CMorphisms.Proper (relation_equivalence ==> relation_equivalence)%signature (@joinable A).
  Proof.
    reduce_goal. split; unfold joinable; intros.
    destruct X0. exists x1. intuition eauto. setoid_rewrite (X x0 x1) in a. auto.
    specialize (X y0 x1). now apply X in b.
    red in X.
    destruct X0 as [z [rl rr]].
    apply X in rl. apply X in rr.
    exists z; split; auto.
  Qed.

  Instance diamond_proper A : CMorphisms.Proper (relation_equivalence ==> iffT)%signature (@diamond A).
  Proof.
    reduce_goal.
    rewrite /diamond.
    split; intros.
    setoid_rewrite <- (X x0 y0) in X1.
    setoid_rewrite <- (X x0 z) in X2.
    specialize (X0 _ _ _ X1 X2).
    pose (joinable_proper _ _ _ X).
    now apply r in X0.
    setoid_rewrite (X x0 y0) in X1.
    setoid_rewrite (X x0 z) in X2.
    specialize (X0 _ _ _ X1 X2).
    pose (joinable_proper _ _ _ X).
    now apply r in X0.
  Qed.

  Lemma clos_rt_proper A : CMorphisms.Proper (relation_equivalence ==> relation_equivalence) (@clos_refl_trans A).
  Proof.
    reduce_goal. split; intros.
    induction X0; try apply X in r; try solve [econstructor; eauto].
    induction X0; try apply X in r; try solve [econstructor; eauto].
  Qed.

  Instance confluent_proper A : CMorphisms.Proper (relation_equivalence ==> iffT)%signature (@confluent A).
  Proof.
    reduce_goal.
    split; rewrite /confluent; auto.
    pose proof (diamond_proper A). apply X0. apply clos_rt_proper.
    now symmetry.
    pose proof (diamond_proper A). apply X0. apply clos_rt_proper.
    now symmetry.
  Qed.

  Definition clos_rt_monotone {A} (R S : relation A) :
    inclusion R S -> inclusion (clos_refl_trans R) (clos_refl_trans S).
  Proof.
    move => incls x y.
    induction 1; solve [econstructor; eauto].
  Qed.

  Lemma relation_equivalence_inclusion {A} (R S : relation A) :
    inclusion R S -> inclusion S R -> relation_equivalence R S.
  Proof. firstorder. Qed.

  Lemma sandwich {A} (R S : A -> A -> Type) :
    inclusion R S -> inclusion S (clos_refl_trans R) ->
    (iffT (confluent S) (confluent R)).
  Proof.
    intros inclR inclS.
    apply clos_rt_monotone in inclR.
    apply clos_rt_monotone in inclS.
    assert (inclusion (clos_refl_trans S) (clos_refl_trans R)).
    etransitivity; eauto.
    apply clos_rt_idempotent.
    rewrite /confluent.
    apply diamond_proper.
    now apply relation_equivalence_inclusion.
  Qed.

  Lemma clos_rt_t_incl {A} {R : relation A} `{Reflexive A R} :
    inclusion (clos_refl_trans R) (trans_clos R).
  Proof.
    intros x y. induction 1; try solve [econstructor; eauto].
  Qed.

  Lemma clos_t_rt_incl {A} {R : relation A} `{Reflexive A R} :
    inclusion (trans_clos R) (clos_refl_trans R).
  Proof.
    intros x y. induction 1; try solve [econstructor; eauto].
  Qed.

  Lemma clos_t_rt_equiv {A} {R} `{Reflexive A R} :
    relation_equivalence (trans_clos R) (clos_refl_trans R).
  Proof.
    apply relation_equivalence_inclusion.
    apply clos_t_rt_incl.
    apply clos_rt_t_incl.
  Qed.

End AbstractConfluence.

Unset Universe Minimization ToSet.

Section RedConfluence.
  Context {Σ} (wfΣ : wf Σ).

  Instance pred1_refl Γ : Reflexive (pred1 Σ Γ Γ).
  Proof. red; apply pred1_refl. Qed.

  Definition pred1_rel : (context * term) -> (context * term) -> Type :=
    fun t u => pred1 Σ (fst t) (fst u) (snd t) (snd u).

  Instance pred1_rel_refl : Reflexive pred1_rel.
  Proof. red. intros [ctx x]. red. simpl. apply pred1_refl. Qed.

  Lemma red1_weak_confluence Γ t u v :
    red1 Σ Γ t u -> red1 Σ Γ t v ->
    ∑ t', red Σ Γ u t' * red Σ Γ v t'.
  Proof.
    move/(red1_pred1 wfΣ) => tu.
    move/(red1_pred1 wfΣ) => tv.
    eapply confluence in tu; eauto.
    destruct tu as [redl redr].
    eapply pred1_red in redl; auto.
    eapply pred1_red in redr; auto.
    eexists _; split; eauto.
  Qed.

  Lemma sc_pred1_rel t u v :
    pred1_rel t u -> pred1_rel t v ->
    ∑ t', pred1_rel u t' * pred1_rel v t'.
  Proof.
    move=> tu tv.
    destruct (confluence _ _ _ _ _ _ _ wfΣ tu tv).
    eexists (rho_ctx Σ (fst t), rho Σ (rho_ctx Σ (fst t)) (snd t)).
    split; auto.
  Qed.

  Lemma pred1_rel_trans_pred1_confluent t u v :
    trans_clos_1n pred1_rel t u ->
    pred1_rel t v ->
    ∑ t', trans_clos_1n pred1_rel u t' * trans_clos_1n pred1_rel v t'.
  Proof.
    move => tu.
    revert v.
    induction tu.
    intros.
    - destruct (sc_pred1_rel _ _ _ r X); auto.
      eexists; split; constructor; intuition eauto.
    - move => v xv.
      destruct (sc_pred1_rel _ _ _ r xv); auto.
      destruct p. specialize (IHtu _ p).
      destruct IHtu as [nf [redl redr]].
      exists nf. split; auto.
      econstructor 2; eauto.
  Qed.

  Lemma pred1_rel_t1n_confluent {t u v} :
    trans_clos_1n pred1_rel t u ->
    trans_clos_1n pred1_rel t v ->
    ∑ t', trans_clos_1n pred1_rel u t' * trans_clos_1n pred1_rel v t'.
  Proof.
    move => tu tv.
    induction tv in u, tu |- *.
    - eapply pred1_rel_trans_pred1_confluent; eauto.
    - eapply pred1_rel_trans_pred1_confluent in r; eauto.
      destruct r as [nf [redl redr]].
      specialize (IHtv _ redr) as [nf' [redl' redr']].
      exists nf'; intuition auto.
      apply trans_clos_t1n_iff.
      econstructor 2; eapply trans_clos_t1n_iff; eauto.
  Qed.

  Lemma pred1_rel_tclos_confluent {t u v} :
    trans_clos pred1_rel t u ->
    trans_clos pred1_rel t v ->
    ∑ t', trans_clos pred1_rel u t' * trans_clos pred1_rel v t'.
  Proof.
    move => tu tv.
    apply trans_clos_t1n_iff in tu;
      apply trans_clos_t1n_iff in tv.
    destruct (pred1_rel_t1n_confluent tu tv).
    exists x. split; apply trans_clos_t1n_iff; intuition auto.
  Qed.

  Lemma pred1_rel_confluent : confluent pred1_rel.
  Proof.
    move=> x y z H H'.
    pose proof (pred1_rel_refl).
    apply (clos_rt_t_incl (H:=X)) in H.
    apply (clos_rt_t_incl (H:=X)) in H'.
    pose proof (clos_t_rt_equiv (R:=pred1_rel)).
    apply (joinable_proper _ _ _ X0).
    apply (pred1_rel_tclos_confluent H H').
  Qed.

  Lemma red_trans_clos_pred1 Γ t u :
    red Σ Γ t u ->
    trans_clos pred1_rel (Γ, t) (Γ, u).
  Proof.
    move/(equiv _ _ (red_alt _ _ _ _)) => tu.
    induction tu.
    constructor. now eapply red1_pred1 in r.
    constructor. pcuic.
    econstructor 2; eauto.
  Qed.

  Lemma trans_clos_pred1_red Γ Δ t u :
    trans_clos (pred1 Σ Γ Δ) t u ->
    red Σ Γ t u.
  Proof.
    move=> H.
    apply trans_clos_t1n_iff in H.
    depind H.
    - eapply pred1_red; eauto.
    - eapply red_trans with y; auto.
      eapply pred1_red in r; eauto.
  Qed.

  Definition on_one_decl (P : context → term → term → Type) (Γ : context) (b : option (term × term)) (t t' : term) :=
    match b with
    | Some (b0, b') => ((P Γ b0 b' * (t = t')) + (P Γ t t' * (b0 = b')))%type
    | None => P Γ t t'
    end.

  Section OnOne_local_2.
    Context (P : forall (Γ : context), option (term * term) -> term -> term -> Type).

    Inductive OnOne2_local_env : context -> context -> Type :=
    | localenv2_cons_abs Γ na t t' :
        P Γ None t t' ->
        OnOne2_local_env (Γ ,, vass na t) (Γ ,, vass na t')
    | localenv2_cons_def Γ na b b' t t' :
        P Γ (Some (b, b')) t t' ->
        OnOne2_local_env (Γ ,, vdef na b t) (Γ ,, vdef na b' t')
    | localenv2_cons_tl Γ Γ' d :
        OnOne2_local_env Γ Γ' ->
        OnOne2_local_env (Γ ,, d) (Γ' ,, d).
  End OnOne_local_2.

  Definition red1_ctx := (OnOne2_local_env (on_one_decl (fun Δ t t' => red1 Σ Δ t t'))).

  Definition red1_rel : relation (context * term) :=
    relation_disjunction (fun '(Γ, t) '(Δ, u) => (red1 Σ Γ t u * (Γ = Δ)))%type
                         (fun '(Γ, t) '(Δ, u) => (red1_ctx Γ Δ * (t = u)))%type.

  Definition red_ctx : relation context :=
    All2_local_env (on_decl (fun Γ Δ t u => red Σ Γ t u)).


  Lemma red1_ctx_pred1_ctx Γ Γ' : red1_ctx Γ Γ' -> pred1_ctx Σ Γ Γ'.
  Proof.
    intros. induction X; try constructor. pcuic. red. pcuic.
    now eapply red1_pred1. pcuic.
    destruct p as [[redb ->]|[redt ->]].
    - split; pcuic. now eapply red1_pred1.
    - split; pcuic. now eapply red1_pred1.
    - destruct d as [na [b|] ty].
      * constructor; intuition auto. red.
        split; now eapply pred1_refl_gen.
      * constructor; intuition auto. red.
        now eapply pred1_refl_gen.
  Qed.

  Lemma pred1_ctx_red_ctx Γ Γ' : pred1_ctx Σ Γ Γ' -> red_ctx Γ Γ'.
  Proof.
    intros. induction X; try constructor; pcuic.
    now eapply pred1_red in p.
    destruct p as [redb redt].
    split. now apply pred1_red in redb.
    now apply pred1_red in redt.
  Qed.

  Definition red_rel' :=
    fun '(Γ, t) '(Δ, u) =>
      (red Σ Γ t u * red_ctx Γ Δ)%type.

  Lemma pred1_red' Γ Γ' : forall M N, pred1 Σ Γ Γ' M N -> red_rel' (Γ, M) (Γ', N).
  Proof.
    intros * Hred.
    split. apply (pred1_red wfΣ _ _ _ _ Hred).
    eapply pred1_pred1_ctx in Hred.
    now eapply pred1_ctx_red_ctx.
  Qed.

  Lemma clos_rt_disjunction_left {A} (R S : relation A) :
    inclusion (clos_refl_trans R)
              (clos_refl_trans (relation_disjunction R S)).
  Proof.
    apply clos_rt_monotone.
    intros x y H; left; exact H.
  Qed.

  Lemma clos_rt_disjunction_right {A} (R S : relation A) :
    inclusion (clos_refl_trans S)
              (clos_refl_trans (relation_disjunction R S)).
  Proof.
    apply clos_rt_monotone.
    intros x y H; right; exact H.
  Qed.

  Instance clos_rt_trans A R : Transitive (@clos_refl_trans A R).
  Proof.
    intros x y z H H'. now econstructor 3.
  Qed.

  Instance clos_rt_refl A R : Reflexive (@clos_refl_trans A R).
  Proof. intros x. constructor 2. Qed.

  Lemma clos_refl_trans_prod_l {A B} (R : relation A) (S : relation (A * B)) :
    (forall x y b, R x y -> S (x, b) (y, b)) ->
    forall (x y : A) b,
      clos_refl_trans R x y ->
      clos_refl_trans S (x, b) (y, b).
  Proof.
    intros. induction X0; try solve [econstructor; eauto].
  Qed.

  Lemma clos_refl_trans_prod_r {A B} (R : relation B) (S : relation (A * B)) a :
    (forall x y, R x y -> S (a, x) (a, y)) ->
    forall (x y : B),
      clos_refl_trans R x y ->
      clos_refl_trans S (a, x) (a, y).
  Proof.
    intros. induction X0; try solve [econstructor; eauto].
  Qed.

  Lemma clos_rt_OnOne2_local_env_incl R :
    inclusion (OnOne2_local_env (on_one_decl (fun Δ => clos_refl_trans (R Δ))))
              (clos_refl_trans (OnOne2_local_env (on_one_decl R))).
  Proof.
    intros x y H.
    induction H; firstorder.
    - red in p.
      induction p. repeat constructor. firstorder.
      constructor 2.
      etransitivity; eauto.
    - subst.
      induction a. repeat constructor. firstorder.
      constructor 2.
      etransitivity; eauto.
    - subst.
      induction a. constructor. constructor. red. right. firstorder.
      constructor 2.
      etransitivity; eauto.
    - clear H. induction IHOnOne2_local_env. constructor. now constructor 3.
      constructor 2.
      etransitivity; eauto.
  Qed.

  Lemma OnOne2_local_env_impl R S :
    (forall Δ, inclusion (R Δ) (S Δ)) ->
    inclusion (OnOne2_local_env (on_one_decl R))
              (OnOne2_local_env (on_one_decl S)).
  Proof.
    intros H x y H'.
    induction H'; try solve [econstructor; firstorder].
  Qed.

  Lemma red_ctx_clos_rt_red1_ctx : inclusion red_ctx (clos_refl_trans red1_ctx).
  Proof.
    intros x y H.
    induction H; try firstorder.
    red in p.
    transitivity (Γ ,, vass na t').
    eapply clos_rt_OnOne2_local_env_incl. constructor. red.
    eapply red_alt in p; eauto.
    clear p H.
    induction IHAll2_local_env. constructor. constructor 3. apply r.
    constructor 2.
    etransitivity; eauto.

    apply red_alt in a. apply red_alt in b0.
    transitivity (Γ ,, vdef na b t').
    - eapply clos_rt_OnOne2_local_env_incl. constructor 2. red.
      right. split; auto.
    - transitivity (Γ ,, vdef na b' t').
      eapply clos_rt_OnOne2_local_env_incl.
      constructor 2. red. left; split; auto.
      clear -IHAll2_local_env.
      induction IHAll2_local_env.
      * constructor. now constructor.
      * constructor 2.
      * etransitivity; eauto.
  Qed.

  Lemma clos_rt_red1_rel_red_rel : inclusion red_rel' (clos_refl_trans red1_rel).
  Proof.
    move=> [Γ t] [Δ u] [redt redctx].
    eapply red_alt in redt.
    eapply clos_rt_rt1n_iff in redt.
    induction redt.
    induction redctx; try solve [constructor; eauto].
    - red in p.
      etransitivity.
      * eapply clos_rt_disjunction_right.
        eapply red_alt in p. instantiate (1:= (Γ',, vass na t', x)).
        eapply clos_refl_trans_prod_l. intros. split; eauto.
        apply red_ctx_clos_rt_red1_ctx. constructor; auto.
        red. apply red_alt; auto.
      * clear p. eapply clos_rt_disjunction_right.
        eapply clos_refl_trans_prod_l. intros. split; eauto.
        constructor 2.
    - red in p.
      destruct p.
      eapply red_alt in r. eapply red_alt in r0.
      etransitivity.
      * eapply clos_rt_disjunction_right.
        instantiate (1:= (Γ',, vdef na b' t', x)).
        eapply clos_refl_trans_prod_l. intros. split; eauto.
        apply red_ctx_clos_rt_red1_ctx. constructor; auto.
        red. split; apply red_alt; auto.
      * clear r r0.
        eapply clos_rt_disjunction_right.
        eapply clos_refl_trans_prod_l. intros. split; eauto.
        constructor 2.
    - transitivity (Γ, y).
      * eapply clos_rt_disjunction_left.
        eapply clos_refl_trans_prod_r. intros. split; eauto.
        constructor. apply r.
      * assumption.
  Qed.

  Lemma pred_rel_confluent : confluent red1_rel.
  Proof.
    notypeclasses refine (fst (sandwich _ _ _ _) _).
    3:eapply pred1_rel_confluent; eauto.
    intros [ctx t] [ctx' t'].
    rewrite /red1_rel /pred1_rel /=.
    intros [[l <-]|[r <-]].
    - now eapply red1_pred1.
    - eapply pred1_refl_gen. now apply red1_ctx_pred1_ctx.
    - intros x y pred. red in pred.
      eapply pred1_red' in pred; auto.
      destruct pred.
      destruct x, y. simpl in *.
      transitivity (c, t0).
      eapply clos_rt_disjunction_left.
      eapply clos_refl_trans_prod_r. intros. split; eauto.
      now eapply red_alt in r.
      eapply clos_rt_disjunction_right.
      eapply clos_refl_trans_prod_l. intros. split; eauto.
      now eapply red_ctx_clos_rt_red1_ctx.
  Qed.

  Lemma clos_refl_trans_out Γ x y :
    clos_refl_trans (red1 Σ Γ) x y -> clos_refl_trans red1_rel (Γ, x) (Γ, y).
  Proof.
    induction 1. constructor. red. left. firstorder.
    constructor 2.
    econstructor 3; eauto.
  Qed.

  Lemma clos_red_rel_out x y :
    clos_refl_trans red1_rel x y ->
    clos_refl_trans pred1_rel x y.
  Proof.
    eapply clos_rt_monotone. clear x y.
    intros [Γ t] [Δ u] hred.
    destruct hred as [[ht eq]|[hctx eq]]. subst.
    red. simpl. now eapply red1_pred1.
    subst. red.
    simpl.
    eapply pred1_refl_gen. now eapply red1_ctx_pred1_ctx.
  Qed.

  (* Lemma clos_red_rel_out' x y : *)
  (*   clos_refl_trans red1_rel x y -> *)
  (*   clos_refl_trans (red1 Σ (fst y)) (snd x) (snd y). *)
  (* Proof. *)
  (*   intros H. eapply clos_red_rel_out in H. *)
  (*   destruct x, y. simpl in *. *)
  (*   induction H. red in r. *)


  (*   eapply clos_rt_red1_rel_red_rel. *)

  (*   eapply clos_rt_rt1n in H. *)
  (*   induction H; try destruct x as [Γ t]; try destruct y as [Δ u]; simpl in *. *)
  (*   - constructor 2. *)
  (*   - destruct z as [? ?]. *)
  (*     simpl in *. intros <-. *)
  (*     red in r. *)
  (*     destruct r. *)
  (*     * destruct p. subst. *)
  (*       eapply clos_rt1n_rt. econstructor; eauto. *)
  (*       eapply clos_rt_rt1n. *)
  (*       now eapply IHclos_refl_trans_1n. *)
  (*     * destruct p. *)
  (*       subst. *)
  (* Qed. *)

  Lemma red1_confluent Γ : confluent (red1 Σ Γ).
  Proof.
    intros x y z.
    intros.
    pose proof (pred_rel_confluent (Γ, x) (Γ, y) (Γ, z)).
    forward X1 by now eapply clos_refl_trans_out.
    forward X1 by now eapply clos_refl_trans_out.
    destruct X1 as [[Δ nf] [redl redr]].
    exists nf. split.
    eapply clos_red_rel_out in redl.
    eapply clos_red_rel_out in redr.
  Abort.

End RedConfluence.