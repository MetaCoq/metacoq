From Coq Require Import Bool String List Program BinPos Compare_dec PeanoNat Lia.
From MetaCoq.Template Require Import utils UnivSubst.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICTyping PCUICWeakeningEnv PCUICWeakening PCUICInversion
     PCUICSubstitution PCUICReduction PCUICCumulativity PCUICGeneration
     PCUICParallelReductionConfluence PCUICConfluence PCUICUnivSubst
     PCUICPrincipality.

From Equations Require Import Equations.
Require Import ssreflect.
Existing Instance config.default_checker_flags.

Derive NoConfusion for term.
Derive Signature for typing cumul.

(* Polymorphic Derive Signature for Relation.clos_refl_trans. *)
Derive Signature for red1.

Lemma context_assumptions_subst_instance_context u Γ :
  context_assumptions (subst_instance_context u Γ) = context_assumptions Γ.
Proof.
  induction Γ as [|[na [b|] ty] Γ]; simpl; auto.
Qed.

Lemma invert_red_sort Σ Γ u v :
  red Σ Γ (tSort u) v -> v = tSort u.
Proof.
  intros H; apply red_alt in H.
  depind H. depind r. solve_discr.
  reflexivity.
  eapply IHclos_refl_trans2. f_equal. auto.
Qed.

Lemma invert_red_prod Σ Γ na A B v : wf Σ ->
  red Σ Γ (tProd na A B) v ->
  ∑ A' B', (v = tProd na A' B') *
           (red Σ Γ A A') *
           (red Σ (vass na A :: Γ) B B').
Proof.
  intros wfΣ H. apply red_alt in H.
  depind H.
  depelim r. solve_discr.
  do 2 eexists. repeat split; eauto with pcuic.
  do 2 eexists. repeat split; eauto with pcuic.
  do 2 eexists. repeat split; eauto with pcuic.
  destruct IHclos_refl_trans1 as (? & ? & (-> & ?) & ?). auto.
  specialize (IHclos_refl_trans2 _ _ _ _ wfΣ eq_refl).
  destruct IHclos_refl_trans2 as (? & ? & (-> & ?) & ?).
  do 2 eexists. repeat split; eauto with pcuic.
  now transitivity x.
  transitivity x0; auto.
  eapply red_red_ctx. eauto. eauto.
  constructor. admit. red. auto.
Admitted.

Derive Signature for eq_term_upto_univ.

Lemma red_conv (Σ : global_context) Γ t u : red Σ Γ t u -> Σ ;;; Γ |- t = u.
Proof.
  intros. now eapply conv_conv_alt, red_conv_alt.
Qed.

Lemma conv_cumul Σ Γ t u :
  Σ ;;; Γ |- t = u -> (Σ ;;; Γ |- t <= u) * (Σ ;;; Γ |- u <= t).
Proof. trivial. Qed.

Lemma conv_sym Σ Γ t u : Σ ;;; Γ |- t = u -> Σ ;;; Γ |- u = t.
Proof.
  intros. eapply conv_cumul in X. split; intuition auto.
Qed.

(* TODO from Inversion *)
  Lemma conv_trans :
    forall Σ Γ u v w,
      Σ ;;; Γ |- u = v ->
      Σ ;;; Γ |- v = w ->
      Σ ;;; Γ |- u = w.
  Proof.
    intros Σ Γ u v w h1 h2.
    destruct h1, h2. constructor ; eapply cumul_trans ; eassumption.
  Qed.

(* FIXME leq_term_upto_univ is wrong: it assumes le for domains of products *)
Lemma invert_cumul_prod_r Σ Γ C na A B : wf Σ ->
  Σ ;;; Γ |- C <= tProd na A B ->
  ∑ na' A' B', red Σ Γ C (tProd na' A' B') *
               (Σ ;;; Γ |- A = A') *
               (Σ ;;; Γ |- B' <= B').
Proof.
  intros wfΣ Hprod.
  eapply cumul_alt in Hprod as [v [v' [[redv redv'] leqvv']]].
  eapply invert_red_prod in redv' as (A' & B' & ((-> & Ha') & ?)).
  depelim leqvv'.
  do 3 eexists; intuition eauto.
  eapply conv_trans.
  eapply red_conv. eauto.
  eapply conv_sym. eapply conv_conv_alt.
  constructor. red. apply leqvv'1. auto.
Qed.

Lemma invert_cumul_sort_r Σ Γ C u :
  Σ ;;; Γ |- C <= tSort u ->
  ∑ u', red Σ Γ C (tSort u') * leq_universe (snd Σ) u' u.
Proof.
  intros Hcum.
  eapply cumul_alt in Hcum as [v [v' [[redv redv'] leqvv']]].
  eapply invert_red_sort in redv' as ->.
  depelim leqvv'. exists s. intuition eauto.
Qed.

Lemma invert_cumul_sort_l Σ Γ C u :
  Σ ;;; Γ |- tSort u <= C ->
  ∑ u', red Σ Γ C (tSort u') * leq_universe (snd Σ) u u'.
Proof.
  intros Hcum.
  eapply cumul_alt in Hcum as [v [v' [[redv redv'] leqvv']]].
  eapply invert_red_sort in redv as ->.
  depelim leqvv'. exists s'. intuition eauto.
Qed.

Lemma type_unicity_prod {Σ Γ t na na' A A' B B'} : wf Σ ->
  Σ ;;; Γ |- t : tProd na A B ->
  Σ ;;; Γ |- t : tProd na' A' B' ->
  Σ ;;; Γ |- A = A'.
Proof.
  intros wfΣ X X0.
  generalize (principal_typing _ wfΣ X X0); move=> [C [HC1 [HC2 HtC]]].
  eapply invert_cumul_prod_r in HC1 => //.
  eapply invert_cumul_prod_r in HC2 => //.
  destruct HC1 as [na0 [A0 [B0 [[HC0 HA0] HB0]]]].
  destruct HC2 as [na1 [A1 [B1 [[HC1 HA1] HB1]]]].
  (* Confluence needed *)
  destruct (red_confluence wfΣ HC0 HC1) as [pitype [redl redr]].
  eapply invert_red_prod in redl as (?&?&(?&?)&?) => //.
  eapply invert_red_prod in redr as (?&?&(?&?)&?) => //.
  subst. noconf e0.
  eapply red_conv in r; eapply red_conv in r1.
  eapply conv_sym in r1. eapply conv_trans; eauto.
  eapply conv_trans; eauto.
  eapply conv_trans; eauto. eapply conv_sym; eauto.
Qed.

Lemma type_unicity_discr_prod_sort {Σ Γ t na A B u} : wf Σ ->
  Σ ;;; Γ |- t : tProd na A B ->
  Σ ;;; Γ |- t : tSort u -> False.
Proof.
  intros wfΣ X X0.
  generalize (principal_typing _ wfΣ X X0); move=> [C [HC1 [HC2 HtC]]].
  eapply invert_cumul_prod_r in HC1 => //.
  eapply invert_cumul_sort_r in HC2 => //.
  destruct HC1 as [na0 [A0 [B0 [[HC0 HA0] HB0]]]].
  destruct HC2 as [u' [redu' lequ']].
  (* Confluence needed *)
  destruct (red_confluence wfΣ HC0 redu') as [reduct [redl redr]].
  eapply invert_red_prod in redl as (?&?&(?&?)&?) => //.
  eapply invert_red_sort in redr as ?. subst. discriminate.
Qed.

Lemma isWfArity_or_Type_lift Σ n Γ ty (isdecl : n <= #|Γ|):
  wf Σ -> wf_local Σ Γ ->
  isWfArity_or_Type Σ (skipn n Γ) ty ->
  isWfArity_or_Type Σ Γ (lift0 n ty).
Proof.
  intros wfΣ wfΓ wfty. rewrite <- (firstn_skipn n Γ) in wfΓ |- *.
  assert (n = #|firstn n Γ|).
  { rewrite firstn_length_le; auto with arith. }
  destruct wfty.
  - red. left. destruct i as [ctx [u [da Hd]]].
    exists (lift_context n 0 ctx), u. split.
    1: now rewrite (lift_destArity [] ty n 0) da.
    eapply All_local_env_app_inv.
    eapply All_local_env_app in Hd. intuition eauto.
    rewrite {3}H.
    clear -wfΣ wfΓ isdecl a b.
    induction b; rewrite ?lift_context_snoc; econstructor; simpl; auto.
    + destruct t0 as [u Hu]. exists u. rewrite Nat.add_0_r.
      unshelve eapply (weakening_typing Σ (skipn n Γ) Γ0 (firstn n Γ) t _ _ _ (tSort u)); eauto with wf.
      apply All_local_env_app_inv. intuition eauto.
    + destruct t0 as [u Hu]. exists u. rewrite Nat.add_0_r.
      unshelve eapply (weakening_typing Σ (skipn n Γ) Γ0 (firstn n Γ) t _ _ _ (tSort u)); eauto with wf.
      apply All_local_env_app_inv. intuition eauto.
    + rewrite Nat.add_0_r.
      unshelve eapply (weakening_typing Σ (skipn n Γ) Γ0 (firstn n Γ) b _ _ _ t); eauto with wf.
      eapply All_local_env_app_inv. intuition eauto.
  - right. destruct i as [u Hu]. exists u.
    rewrite {3}H.
    unshelve eapply (weakening_typing Σ (skipn n Γ) [] (firstn n Γ) ty _ _ _ (tSort u)); eauto with wf.
Qed.

Lemma isWfArity_Sort Σ Γ s : wf_local Σ Γ -> isWfArity typing Σ Γ (tSort s).
Proof.
  intros. exists [], s; intuition auto.
Qed.
Hint Extern 10 (isWfArity _ _ _ (tSort _)) => apply isWfArity_Sort : pcuic.

Hint Extern 30 (wf_local ?Σ ?Γ) =>
  match goal with
    | [ H : typing Σ Γ _ _ |- _ ] => apply (typing_wf_local H)
  end : pcuic.

Ltac pcuic := try solve [ intuition typeclasses eauto with pcuic ].

Definition weaken_env_prop_full
           (P : global_context -> context -> term -> term -> Type) :=
  forall Σ Σ', wf Σ' -> extends Σ Σ' -> forall Γ t T, P Σ Γ t T -> P Σ' Γ t T.

Lemma isWfArity_or_Type_weaken_full : weaken_env_prop_full (fun Σ Γ t T => isWfArity_or_Type Σ Γ T).
Proof.
  red. intros.
  destruct X1. left. destruct i as [ctx [s [Heq Hs]]].
  exists ctx, s. pcuic. right. destruct i as [u Hu]; exists u; pcuic.
  unshelve eapply (weaken_env_prop_typing _ _ _ X0 _ _ (Some (tSort u))); eauto.
Qed.
Hint Resolve isWfArity_or_Type_weaken_full : pcuic.

Lemma isWfArity_or_Type_weaken :
 weaken_env_prop
   (lift_typing (fun Σ Γ (_ T : term) => isWfArity_or_Type Σ Γ T)).
Proof.
  red. intros. unfold lift_typing in *. destruct T. now eapply isWfArity_or_Type_weaken_full.
  destruct X1 as [s Hs]; exists s. now eapply isWfArity_or_Type_weaken_full.
Qed.
Hint Resolve isWfArity_or_Type_weaken : pcuic.

(** TODO: Universe instances *)
Lemma isWfArity_or_Type_subst_instance:
  forall (Σ : global_context) (Γ : context) (u : list Level.t) (ty : term), wf_local Σ Γ ->
    isWfArity_or_Type Σ [] ty -> isWfArity_or_Type Σ Γ (PCUICUnivSubst.subst_instance_constr u ty).
Proof.
  intros Σ Γ u ty wfΓ H.
  destruct H as [[ctx [s [Heq Hs]]]|].
  - left.
    exists ctx, s. split; pcuic.
Admitted.
Derive Signature for subslet context_subst.
  Notation "'∑'  x .. y , P" := (sigT (fun x => .. (sigT (fun y => P%type)) ..))
    (at level 200, x binder, y binder, right associativity) : type_scope.
Hint Constructors subslet : pcuic.

Lemma subslet_app Σ Γ args l l' :
  subslet Σ Γ args (l ++ l') ->
  ∑ (args' : list term) (args'' : list term),
  (args = args'' ++ args')
  * subslet Σ Γ args' l' * subslet Σ Γ args'' (subst_context args' 0 l).
Proof.
  intros Hs. depind Hs.
  - destruct l; try discriminate. destruct l'; try discriminate.
    exists [], []. split; auto with pcuic.
  - destruct l; simpl in *.
    subst l'.
    exists (t :: s), []. split; auto with pcuic.
    noconf H.
    specialize (IHHs s l l' eq_refl).
    destruct IHHs as [args' [args'' [[Hs' Hl'] Hsl]]].
    subst s.
    exists args', (t :: args''). simpl.
    split; auto. rewrite subst_context_snoc. simpl. constructor; auto.
    simpl. rewrite Nat.add_0_r.
    pose proof (substlet_length Hl').
    pose proof (substlet_length Hsl). rewrite subst_context_length in H0.
    rewrite <- H0. rewrite subst_app_simpl in t0. now simpl in t0.
  - destruct l; simpl in *.
    + subst l'.
      exists (subst0 s t :: s), []. split; auto with pcuic.
    + noconf H.
      specialize (IHHs s l l' eq_refl).
      destruct IHHs as [args' [args'' [[Hs' Hl'] Hsl]]].
      subst s.
      exists args', (subst0 (args'' ++ args') t :: args''). simpl.
      split; auto. rewrite subst_context_snoc. simpl.
      rewrite subst_app_simpl. simpl. rewrite Nat.add_0_r.
      unfold subst_decl. unfold map_decl. simpl.
      pose proof (substlet_length Hl').
      pose proof (substlet_length Hsl). rewrite subst_context_length in H0.
      rewrite <- H0. constructor; auto. rewrite !subst_app_simpl in t0. now simpl in t0.
Qed.

Lemma subslet_app_inv Σ Γ args args' l l' :
  (subslet Σ Γ args' l' * subslet Σ Γ args (subst_context args' 0 l)) ->
  subslet Σ Γ (args ++ args') (l ++ l').
Proof.
  intros Hs. destruct Hs.
  induction l in l', s, s0, args, args' |- *.
  - simpl. now depelim s0.
  - rewrite subst_context_snoc0 in s0.
    pose proof (substlet_length s0). unfold snoc in H. simpl in H. rewrite subst_context_length in H.
    depelim s0. hnf in H. noconf H.
    + destruct a as [na [b|] ty]; noconf H.
      cbn in *. constructor. apply IHl; auto. rewrite subst_app_simpl. simpl.
      noconf H0. hnf in H. now rewrite H.
    + destruct a as [na' [b|] ty]; hnf in H; noconf H.
      cbn in *. noconf H0. hnf in H. rewrite -H.
      rewrite -subst_app_simpl. constructor. auto.
      now rewrite !subst_app_simpl H.
Qed.

Lemma context_assumptions_app Γ Γ' :
  context_assumptions (Γ ++ Γ') = context_assumptions Γ + context_assumptions Γ'.
Proof.
  induction Γ as [|[na [b|] ty] tl]; simpl; auto.
Qed.

Lemma skipn_S {A} a (l : list A) n : skipn (S n) (a :: l) = skipn n l.
Proof. reflexivity. Qed.

Lemma context_assumptions_skipn n Γ :
  context_assumptions (skipn n Γ) = context_assumptions Γ - context_assumptions (firstn n Γ).
Proof.
  induction n in Γ |- *; cbn.
  - unfold skipn. lia.
  - destruct Γ; trivial. rewrite skipn_S.
    rewrite IHn. destruct c as [na [b|] ty]; simpl; auto.
Qed.

Derive Signature for le.

Lemma firstn_app_eq {A} (l l' : list A) n : #|l| = n -> firstn n (l ++ l') = l.
Proof.
  induction l in l', n |- *; destruct n; simpl; auto. discriminate. discriminate.
  intros H. now rewrite [firstn _ _]IHl.
Qed.

Lemma firstn_app_ge {A} (l l' : list A) n : #|l| <= n -> firstn n (l ++ l') = l ++ firstn (n - #|l|) l'.
Proof.
  induction l in l', n |- *; destruct n; simpl; auto.
  intros. depelim H.
  intros H. now rewrite [firstn _ _]IHl.
Qed.

Lemma firstn_app_lt {A} (l l' : list A) n : n <= #|l| -> firstn n (l ++ l') = firstn n l.
Proof.
  induction l in l', n |- *; destruct n; simpl; auto.
  intros. depelim H. intros H.
  now rewrite [firstn _ _]IHl.
Qed.

Lemma skipn_app_eq {A} (l l' : list A) n : #|l| = n -> skipn n (l ++ l') = l'.
Proof.
  induction l in l', n |- *; destruct n; simpl; auto. discriminate. discriminate.
  intros H. now rewrite [skipn _ _]IHl.
Qed.

Lemma skipn_app_ge {A} (l l' : list A) n : #|l| <= n -> skipn n (l ++ l') = skipn (n - #|l|) l'.
Proof.
  induction l in l', n |- *; destruct n; simpl; auto.
  intros. depelim H.
  intros H. now rewrite [skipn _ _]IHl.
Qed.

Lemma skipn_app_lt {A} (l l' : list A) n : n <= #|l| -> skipn n (l ++ l') = skipn n l ++ l'.
Proof.
  induction l in l', n |- *; destruct n; simpl; auto.
  intros. depelim H. intros H.
  now rewrite [skipn _ _]IHl.
Qed.

Lemma context_assumptions_subst_context s n Γ :
  context_assumptions (subst_context s n Γ) = context_assumptions Γ.
Proof.
  induction Γ as [|[? [?|] ?] ?]; rewrite ?subst_context_snoc; simpl; auto.
Qed.

Lemma firstn_length_inv {A} n (l : list A) : #|firstn n l| = n -> n <= #|l|.
Proof.
  induction n in l |- *; destruct l; simpl; try lia. simpl in IHn.
  intros [=]. specialize (IHn _ H0). lia.
Qed.

Lemma context_subst_app Γ args s s' :
  context_subst Γ args (s ++ s') <~>
  context_subst (skipn #|s| Γ) (List.firstn (context_assumptions (skipn #|s| Γ)) args) s' *
  context_subst (subst_context s' 0 (firstn #|s| Γ)) (List.skipn (context_assumptions (skipn #|s| Γ)) args) s.
Proof.
  split.
  intros Hs. depind Hs.
  - destruct s; simpl in *; try congruence. subst.
    intros. split; constructor.
  - rewrite firstn_app.
    pose proof (context_subst_length _ _ _ Hs).
    pose proof (context_subst_assumptions_length _ _ _ Hs).
    destruct s0; noconf H; try (simpl in *; congruence).
    + simpl context_assumptions. rewrite H1.
      rewrite firstn_all2. lia.
      rewrite Nat.sub_succ_l. lia. simpl. rewrite Nat.sub_diag. simpl.
      split; try constructor; auto.
      rewrite skipn_all2 ?app_length /=. lia. constructor.
    + specialize (IHHs Γ _ s0 s' eq_refl). simpl. rewrite skipn_S.
      destruct IHHs. rewrite app_length in H0.
      rewrite -H1. rewrite {2}context_assumptions_skipn.
      set (nth := context_assumptions _ - _ - _).
      assert (nth = 0) as -> by (subst nth; lia).
      simpl. rewrite app_nil_r. split; intuition auto.
      rewrite skipn_app_lt.
      rewrite context_assumptions_skipn. lia.
      rewrite subst_context_snoc. now constructor.
  - pose proof (context_subst_length _ _ _ Hs).
    pose proof (context_subst_assumptions_length _ _ _ Hs).
    destruct s0; noconf H; simpl in *; try congruence.
    + specialize (IHHs Γ args [] s eq_refl) as [Hs' Hs''].
      split; try constructor; auto.
    + rewrite app_length in H0.
      specialize (IHHs Γ _ s0 s' eq_refl) as [Hs' Hs''].
      split; auto.
      rewrite subst_context_snoc. simpl.
      rewrite subst_app_simpl. rewrite Nat.add_0_r. simpl.
      unfold subst_decl, map_decl. simpl. rewrite skipn_S.
      rewrite firstn_length_le. lia.
      now constructor.
  - intros [H H'].
    assert (#|args| = context_assumptions Γ).
    { rewrite -{1}(firstn_skipn #|s| Γ) context_assumptions_app.
      rewrite -{1}(firstn_skipn (context_assumptions (skipn #|s| Γ)) args) app_length.
      rewrite -(context_subst_assumptions_length _ _ _ H).
      rewrite -(context_subst_assumptions_length _ _ _ H').
      rewrite context_assumptions_subst_context.
      lia. }
    induction s in Γ, args, s', H, H', H0 |- *; simpl in *.

    unfold skipn in H. rewrite -H0 in H.
    rewrite firstn_all2 in H. auto. auto.

    destruct Γ; try discriminate.
    simpl in *. destruct args; simpl in *; try discriminate. depelim H'.
    destruct c as [na [b|] ty]. simpl in *.
    + rewrite skipn_S in H, H'.
      rewrite subst_context_snoc0 in H'.
      unfold subst_decl, map_decl in H'. simpl in *.
      specialize (IHs _ _ _ H). depelim H'. hnf in H1. noconf H1.
      hnf in H1. noconf H1.
      pose proof (subst_app_simpl s0 s' 0 b). simpl in H1.
      rewrite firstn_length_le.
      { move: (context_subst_length _ _ _ H').
        rewrite subst_context_length.
        now move/firstn_length_inv. }
      rewrite -H1. constructor. apply IHs; auto.
    + rewrite skipn_S in H, H'.
      rewrite subst_context_snoc0 in H'.
      unfold subst_decl, map_decl in H'. simpl in *.
      destruct args using rev_ind; try discriminate.
      rewrite app_length in H0. simpl in H0.
      depelim H'. hnf in H0. noconf H0.
      assert ((context_assumptions (skipn #|s| Γ)) <= #|args|).
      { rewrite context_assumptions_skipn. lia. }
      rewrite skipn_app_lt in H1. auto.
      apply app_inj_tail in H1 as [<- ->].
      constructor. apply IHs.
      rewrite firstn_app in H.
      assert (context_assumptions (skipn #|s| Γ) - #|args| = 0) by lia.
      rewrite H1 in H. simpl in H. now rewrite app_nil_r in H.
      auto. lia.
      hnf in H0. noconf H0.
Qed.

Lemma typing_spine_tLetIn Σ Γ na b ty T args U :
  typing_spine Σ Γ (T {0 := b}) args U ->
  typing_spine Σ Γ (tLetIn na b ty T) args U.
Proof.
  intros Hs. depind Hs.
  - constructor. auto. econstructor 2. constructor. auto.
  - econstructor; eauto. econstructor 2. constructor. auto.
Qed.

Lemma firstn_none {A} n (l : list A) : n = 0 -> firstn n l = [].
Proof. intros ->. destruct l; reflexivity. Qed.

Lemma skipn_none {A} n (l : list A) : n = 0 -> skipn n l = l.
Proof. intros ->. destruct l; reflexivity. Qed.

Lemma typing_spine_arity Σ Γ ctx u args s :
  wf_local Σ Γ ->
  context_subst ctx args s ->
  subslet Σ Γ s ctx ->
  wf_local Σ (Γ ,,, ctx) ->
  typing_spine Σ Γ (it_mkProd_or_LetIn ctx (tSort u)) args (tSort u).
Proof.
  intros wfΓ Hargss Hs (* Hctx *). revert s args ctx Hargss Hs (* Hctx *). induction s using rev_ind; cbn; intros.
  - depelim Hargss. constructor; auto. left. exists [], u. intuition auto.
  - eapply context_subst_app in Hargss as [instna instl].
    destruct ctx using rev_ind.
    + simpl in *. rewrite skipn_nil in instna.
      simpl in *. depelim instna.
    + clear IHctx.
      pose proof (substlet_length Hs). rewrite !app_length in H. simpl in H.
      assert (#|s| = #|l|) by lia.
      rewrite skipn_app_lt in instna. lia.
      rewrite it_mkProd_or_LetIn_app. simpl.
      rewrite firstn_app in instl.
      rewrite [firstn (_ - _) _]firstn_none in instl. lia.
      rewrite firstn_all2 in instl. lia.
      rewrite app_nil_r in instl.
      rewrite skipn_app_ge in instl. lia.
      rewrite [skipn (_ - _) _]skipn_none in instl. lia.
      rewrite skipn_all2 in instna. by lia.
      destruct x0 as [na [b|] ty]. simpl in *.
      ++ unfold mkProd_or_LetIn. simpl.
         eapply typing_spine_tLetIn.
         unfold subst1. rewrite subst_it_mkProd_or_LetIn.
         simpl.
         eapply subslet_app in Hs as (args' & args'' & (Heq & H') & H'').
         depelim H'; hnf in H1; noconf H1. depelim H'.
         rewrite !subst_empty in Heq, t0, H''.
         eapply app_inj_tail in Heq as [<- <-].
         depelim instna. destruct args0; discriminate. hnf in H1; noconf H1.
         rewrite subst_empty in instl, H'', t0 |- *.
         eapply IHs; eauto. simpl in H1. admit. (* provable wf_local *)
      ++ unfold mkProd_or_LetIn. cbn.
         eapply subslet_app in Hs as (args' & args'' & (Heq & H') & H'').
         depelim H'; hnf in H1; noconf H1. depelim H'.
         rewrite !subst_empty in Heq, t0, H''.
         eapply app_inj_tail in Heq as [<- <-]. simpl in *.
         destruct args. depelim instna; hnf in H1; noconf H1.
         destruct args; discriminate.
         depelim instna; hnf in H1; noconf H1. depelim instna. noconf H2.
         rewrite skipn_S in instl. unfold skipn in instl.
         econstructor; eauto. left.
         exists (l ++ [vass na ty]), u. simpl.
         rewrite destArity_it_mkProd_or_LetIn. simpl. split; auto.
         rewrite /subst1 subst_it_mkProd_or_LetIn /=.
         eapply IHs; eauto.
         admit. (* provable wf_local *)
Admitted.

(* Lemma typing_spine_arity Σ Γ ctx s args : *)
(*   wf_local Σ Γ -> *)
(*   subslet Σ Γ args ctx -> *)
(*   typing_spine Σ Γ (it_mkProd_or_LetIn ctx (tSort s)) args (tSort s). *)
(* Proof. *)
(*   intros wfΓ Hs. revert args Hs; induction ctx using rev_ind; cbn; intros. *)
(*   - depelim Hs. constructor; auto. left. exists [], s. intuition auto. *)
(*   - rewrite it_mkProd_or_LetIn_app. simpl. *)
(*     destruct x as [na [b|] ty]; cbn. *)
(*     eapply subslet_app in Hs as (args' & args'' & (-> & H) & H'). *)
(*     depelim H. simpl in H0. noconf H0. *)
(*     hnf in H0. noconf H0. depelim H. rewrite subst_empty. *)
(*     rewrite subst_empty in H'. simpl in H'. *)



(*     depelim Hs. apply (f_equal (@length _)) in H. rewrite app_length in H. simpl in H; elimtype False. lia. *)

(*     eapply (type_spine_cons Σ Γ t s0 na T). econstructor. 3:eauto. *)



Lemma invert_type_mkApps_head Σ Γ f s u :
  Σ ;;; Γ |- mkApps f u : tSort s ->
  ∑ T, Σ ;;; Γ |- f : T.
Proof.
  induction u in f |- *; simpl; move=> Hf.
  exists (tSort s). auto.
  destruct (IHu (tApp f a) Hf).
  eapply inversion_App in t as (fna & fA & fB & Hfp & Hfa & Hf'').
  eexists ; eauto.
Qed.

(* Lemma invert_type_mkApps Σ Γ f ctx s u : *)
(*   (* If the head's type is syntactically an arity *) *)
(*   Σ ;;; Γ |- f : it_mkProd_or_LetIn ctx (tSort s) -> *)
(*   #|u| = context_assumptions ctx -> *)
(*   (* An the application is well-typed *) *)
(*   Σ ;;; Γ |- mkApps f u : tSort s -> *)
(*   (* We can extract another typing of the head and show that the arguments are a well-typed *)
(*      substitution for it *) *)
(*   ∑ ctx' subs, (Σ ;;; Γ |- f : it_mkProd_or_LetIn ctx' (tSort s)) * *)
(*                (context_subst ctx' u subs * subslet Σ Γ subs ctx')%type. *)
(* Proof. *)
(*   (* induction u in f, ctx |- *; cbn. *) *)
(*   Subterm.rec_wf_rel IH #|ctx| lt. simpl. *)
(*   rename pr1 into Σ. *)
(*   rename pr0 into Γ. *)
(*   rename pr2 into t. *)
(*   rename pr3 into ctx. *)
(*   rename pr4 into s. *)
(*   rename pr5 into u. clear H1. *)
(*   destruct ctx as [|[na [b|] ty] ctx] using rev_ind; move=> /= Hf Hu Hfu. *)
(*   - exists [], []. split; auto; try constructor. *)
(*     destruct u; noconf Hu. constructor. constructor. *)
(*   - clear IHctx. rewrite context_assumptions_app in Hu. simpl in Hu. *)
(*     rewrite it_mkProd_or_LetIn_app in Hf. *)
(*     cbn in Hf. *)
(*     specialize (IH Σ Γ t (subst_context [b] 0 ctx) s u). *)
(*     rewrite app_length subst_context_length in IH. cbn in IH. *)
(*     forward IH by lia. *)
(*     forward IH. *)
(*     { eapply type_Conv. eauto. admit. *)
(*       econstructor 2. constructor. *)
(*       now rewrite /subst1 subst_it_mkProd_or_LetIn. } *)
(*     forward IH. *)
(*     { rewrite context_assumptions_subst_context. lia. } *)
(*     specialize (IH Hfu) as [ctx' [s' [tctx' [ctxs subsl]]]]. *)
(*     exists ctx', s'. *)
(*     split; auto. *)
(*   - clear IHctx. rewrite context_assumptions_app in Hu. simpl in Hu. *)
(*     rewrite it_mkProd_or_LetIn_app in Hf. *)
(*     cbn in Hf. *)
(*     destruct u as [|a u]. simpl in Hu. elimtype False. lia. *)
(*     simpl in Hu. *)
(*     specialize (IH Σ Γ (tApp t a) (subst_context [a] 0 ctx) s u). *)
(*     rewrite app_length subst_context_length in IH. cbn in IH. *)
(*     forward IH by lia. *)
(*     forward IH. *)
(*     { eapply refine_type. eapply type_App. eauto. *)
(*       cbn in Hfu. eapply invert_type_mkApps_head in Hfu. *)
(*       destruct Hfu as [appty Happ]. *)
(*       eapply inversion_App in Happ as (fna & fA & fB & Hfp & Hfa & Hf''). *)
(*       pose proof (type_unicity_prod Hf Hfp). eapply type_Conv. eauto. admit. *)
(*       eapply X. *)
(*       now rewrite /subst1 subst_it_mkProd_or_LetIn. } *)
(*     forward IH. *)
(*     { rewrite context_assumptions_subst_context. lia. } *)
(*     specialize (IH Hfu) as [ctx' [s' [ctxs subsl]]]. *)
(*     exists (ctx ++ [vass na ty]), (s' ++ [a]). *)
(*     split; auto. now rewrite it_mkProd_or_LetIn_app. *)
(*     split. *)
(*     admit. *)
(*     admit. *)
(* Admitted. *)
(* Set SimplIsCbn. *)

Lemma destArity_Let {Γ na b b_ty t_ty ctx s} :
  destArity Γ (tLetIn na b b_ty t_ty) = Some (ctx, s) ->
  destArity Γ (t_ty {0 := b}) =
  let pos := #|ctx| - #|Γ| in
  Some (subst_context [b] 0 (List.firstn (Nat.pred pos) ctx) ++ List.skipn pos ctx, s).
Proof.
  simpl. intros.
  pose proof (PCUICClosed.destArity_spec (Γ ,, vdef na b b_ty) t_ty). rewrite H in H0.
  simpl in H0.
Admitted.

Lemma type_LetIn_red Σ Γ t na b b_ty t_ty :
  isWfArity typing Σ Γ (tLetIn na b b_ty t_ty) ->
  Σ ;;; Γ |- t : tLetIn na b b_ty t_ty ->
  Σ ;;; Γ |- t : t_ty {0 := b}.
Proof.
  intros.
  eapply type_Conv; eauto.
  left. red. red in X. destruct X as [ctx [s [dAr wfl]]].
  exists (subst_context [b] 0 (List.firstn (Nat.pred #|ctx|) ctx)), s.
  admit.
  econstructor 2. constructor. eapply cumul_refl'.
Admitted.

Lemma invert_type_mkApps_args {Σ Γ f ctx s u} : wf Σ ->
  Σ ;;; Γ |- f : it_mkProd_or_LetIn ctx (tSort s) ->
  isWfArity typing Σ Γ (it_mkProd_or_LetIn ctx (tSort s)) ->
  Σ ;;; Γ |- mkApps f u : tSort s ->
  #|u| = context_assumptions ctx.
Proof.
  induction u in f, ctx |- *; simpl; auto.
  intros.
  Subterm.rec_wf_rel IH #|ctx| lt. simpl.
  rename pr1 into Σ.
  rename pr0 into Γ.
  rename pr2 into t.
  rename pr3 into ctx.
  rename pr4 into s.
  rename pr5 into wfΣ.
  rename pr6 into Ht.
  rename pr8 into Ht'. clear H0.
  destruct ctx as [|[na [b|] ty] ctx] using rev_ind; cbn; eauto.
  - rewrite it_mkProd_or_LetIn_app in Ht. cbn in Ht.
    eapply type_LetIn_red in Ht.
    rewrite context_assumptions_app. simpl. rewrite Nat.add_0_r.
    rewrite /subst1 subst_it_mkProd_or_LetIn in Ht. simpl in Ht.
    rewrite -(context_assumptions_subst_context [b] 0 ctx).
    eapply IH. eauto. eauto. admit. eapply Ht'.
    rewrite subst_context_length app_length /=. lia.
    rewrite it_mkProd_or_LetIn_app in pr7. eapply pr7.

  - rewrite it_mkProd_or_LetIn_app /= in pr7 Ht.
    rewrite context_assumptions_app /=.
    clear -wfΣ Ht Ht'. simpl in Ht.
    now elim (type_unicity_discr_prod_sort wfΣ Ht Ht').

  - intros.
    destruct ctx as [|[na [b|] ty] ctx] using rev_ind; cbn; eauto.
    + simpl in *.
      eapply invert_type_mkApps_head in X2 as [T' HT'].
      eapply inversion_App in HT' as [na [A' [B' [Hf' _]]]].
      now elim (type_unicity_discr_prod_sort X Hf' X0).
    + rewrite context_assumptions_app. simpl. rewrite Nat.add_0_r.
      rewrite it_mkProd_or_LetIn_app in X X0. simpl in X, X0.
Admitted.

Lemma invert_type_mkApps {Σ Γ f ctx s} : wf Σ ->
  Σ ;;; Γ |- f : it_mkProd_or_LetIn ctx (tSort s) ->
  forall u, #|u| = context_assumptions ctx ->
  Σ ;;; Γ |- mkApps f u : tSort s ->
  { s & (context_subst ctx u s * subslet Σ Γ s ctx)%type }.
Proof.
  (* induction u in f, ctx |- *; cbn. *)
  Subterm.rec_wf_rel IH #|ctx| lt. simpl.
  rename pr1 into Σ.
  rename pr0 into Γ.
  rename pr2 into t.
  rename pr3 into ctx.
  rename pr4 into s.
  clear H0. intros wfΣ.
  destruct ctx as [|[na [b|] ty] ctx] using rev_ind; move=> /= Hf u Hu Hfu.
  - exists []. split; auto; try constructor.
    destruct u; noconf Hu. constructor.
  - clear IHctx. rewrite context_assumptions_app in Hu. simpl in Hu.
    rewrite it_mkProd_or_LetIn_app in Hf.
    cbn in Hf.
    specialize (IH Σ Γ t (subst_context [b] 0 ctx) s).
    rewrite app_length subst_context_length in IH. cbn in IH.
    forward IH by lia.
    forward IH by auto.
    forward IH.
    { eapply type_Conv. eauto. admit.
      econstructor 2. constructor.
      now rewrite /subst1 subst_it_mkProd_or_LetIn. }
    specialize (IH u).
    forward IH.
    { rewrite context_assumptions_subst_context. lia. }
    specialize (IH Hfu) as [s' [ctxs subsl]].
    exists (s' ++ [b]).
    split; auto.
    + eapply context_subst_app.
      move:(context_subst_length _ _ _ ctxs). rewrite subst_context_length; move=> <-.
      split.
      ++ rewrite skipn_app_eq //. simpl. rewrite -{2}(subst_empty 0 b).
         now repeat constructor.
      ++ rewrite skipn_app_eq // firstn_app_eq //.
    + eapply subslet_app_inv; split; auto.
      pose proof (cons_let_def Σ Γ [] [] na b ty).
      rewrite !subst_empty in X. eapply X. constructor. admit. (* Wf arity *)

  - clear IHctx. rewrite context_assumptions_app in Hu. simpl in Hu.
    rewrite it_mkProd_or_LetIn_app in Hf.
    cbn in Hf.
    destruct u as [|a u]. simpl in Hu. elimtype False. lia.
    simpl in Hu.
    specialize (IH Σ Γ (tApp t a) (subst_context [a] 0 ctx) s).
    rewrite app_length subst_context_length in IH. cbn in IH.
    forward IH by lia.
    forward IH by auto.
    forward IH.
    { eapply refine_type. eapply type_App. eauto.
      cbn in Hfu. eapply invert_type_mkApps_head in Hfu.
      destruct Hfu as [appty Happ].
      eapply inversion_App in Happ as (fna & fA & fB & Hfp & Hfa & Hf'').
      pose proof (type_unicity_prod wfΣ Hf Hfp). eapply type_Conv. eauto. admit.
      eapply X.
      now rewrite /subst1 subst_it_mkProd_or_LetIn. }
    specialize (IH u). forward IH.
    { rewrite context_assumptions_subst_context. lia. }
    specialize (IH Hfu) as [s' [ctxs subsl]].
    exists (s' ++ [a]).
    split; auto.
    + eapply (context_subst_app (ctx ++ _) (a :: u) s' [a]).
      move:(context_subst_length _ _ _ ctxs). rewrite subst_context_length; move=> <-.
      simpl. split.
      rewrite skipn_app_eq //. cbn.
      apply (context_subst_ass [] [] [] na ty a). constructor.
      rewrite firstn_app_eq // skipn_app_eq //.
    + eapply subslet_app_inv. split; auto. constructor. constructor. rewrite subst_empty.
      { cbn in Hfu. eapply invert_type_mkApps_head in Hfu.
        destruct Hfu as [appty Happ].
        eapply inversion_App in Happ as (fna & fA & fB & Hfp & Hfa & Hf'').
        pose proof (type_unicity_prod wfΣ Hf Hfp). eapply type_Conv. eauto. admit.
        eapply X. }
Admitted.

Definition infix_app {A B} (f : A -> B) (x : A) := f x.
Infix "$" := infix_app (at level 20, right associativity).

Lemma invert_mkApps_tInd {Σ Γ ind u args s} (wfΣ : wf Σ) :
  Σ ;;; Γ |- mkApps (tInd ind u) args : tSort s ->
  ∑ mdecl idecl (isdecl : declared_inductive (fst Σ) mdecl ind idecl),
    let (onmind, onind) := on_declared_inductive wfΣ isdecl in
    (#|args| = context_assumptions (ind_params mdecl ++ ind_indices onind)) *
    leq_universe (snd Σ) (UnivSubst.subst_instance_univ u (ind_sort onind)) s *
    (Σ ;;; Γ |- tInd ind u :
    (subst_instance_constr u
       $ it_mkProd_or_LetIn (ind_params mdecl)
       $ it_mkProd_or_LetIn (ind_indices onind)
       $ (tSort (ind_sort onind)))).
Proof.
  intros H.
Admitted.

Theorem validity :
  env_prop (fun Σ Γ t T => isWfArity_or_Type Σ Γ T).
Proof.

  apply typing_ind_env; intros; rename_all_hyps.

  - destruct (nth_error_All_local_env_over heq_nth_error X) as [HΓ' Hd].
    destruct decl as [na [b|] ty]; cbn -[skipn] in *.
    + eapply isWfArity_or_Type_lift; eauto. clear HΓ'; now apply nth_error_Some_length in heq_nth_error.
    + destruct lookup_wf_local_decl; cbn -[skipn] in *.
      destruct o. right. exists x0. simpl in Hd.
      rewrite <- (firstn_skipn (S n) Γ).
      assert (S n = #|firstn (S n) Γ|).
      { apply nth_error_Some_length in heq_nth_error. rewrite firstn_length_le; auto with arith. }
      rewrite {3}H.
      apply (weakening Σ (skipn (S n) Γ) (firstn (S n) Γ) ty (tSort x0)); eauto with wf.
      unfold app_context. now rewrite (firstn_skipn (S n) Γ).

  - (* Universe *) left. exists [], (Universe.super l). split; auto.
  - (* Product *) left. eexists [], _. split; eauto. simpl. reflexivity.
  - (* Lambda *)
    destruct X3.
    + left. destruct i as [ctx [s [Heq Hs]]].
      red. simpl. pose proof (PCUICClosed.destArity_spec [] bty).
      rewrite Heq in H. simpl in H. subst bty. clear Heq.
      eexists _, s. split; auto.
      * rewrite destArity_it_mkProd_or_LetIn. simpl. reflexivity.
      * apply All_local_env_app_inv; split; auto.
        apply All_local_env_app_inv; split; auto.
        -- repeat constructor.
           simpl. now exists s1.
        -- apply All_local_env_app in Hs. unfold snoc.
           intuition auto. clear -b0.
           induction b0; constructor; eauto.
           ++ destruct t1 as [u Hu]. exists u.
              rewrite app_context_assoc. apply Hu.
           ++ simpl in t1 |- *.
              rewrite app_context_assoc. apply t1.
           ++ simpl in t2.
              rewrite app_context_assoc. apply t2.
    + destruct i as [u Hu].
      right. exists (Universe.sort_of_product s1 u); constructor; auto.

  - (* Let *)
    destruct X5.
    + left. destruct i as [ctx [s [Heq Hs]]].
      eexists _, s.
      simpl. split; auto.
      pose proof (PCUICClosed.destArity_spec [] b'_ty).
      rewrite Heq in H. simpl in H. subst b'_ty.
      rewrite destArity_it_mkProd_or_LetIn. simpl.
      reflexivity. rewrite app_context_assoc. simpl.
      apply All_local_env_app_inv; split; eauto with wf.
      apply All_local_env_app in Hs as [Hp Hs].
      apply Hs.
    + right.
      destruct i as [u Hu]. exists u.
      econstructor.
      eapply type_LetIn; eauto. left. exists [], u; intuition eauto with wf.
      eapply cumul_alt. exists (tSort u), (tSort u); intuition auto.
      apply red1_red; repeat constructor.

  - (* Application *)
    destruct X1 as [[ctx [s [Heq Hs]]]|].
    simpl in Heq. pose proof (PCUICClosed.destArity_spec ([],, vass na A) B).
    rewrite Heq in H.
    simpl in H. unfold mkProd_or_LetIn in H. simpl in H.
    destruct ctx using rev_ind; noconf H.
    simpl in H. rewrite it_mkProd_or_LetIn_app in H. simpl in H.
    destruct x as [na' [b|] ty]; noconf H.
    left. eexists _, s. split.
    unfold subst1. rewrite subst_it_mkProd_or_LetIn.
    rewrite destArity_it_mkProd_or_LetIn. simpl. reflexivity.
    rewrite app_context_nil_l. apply All_local_env_app_inv; intuition auto.
    apply All_local_env_app in Hs as [wf'Γ wfctx].
    apply All_local_env_app in wfctx as [wfd wfctx].
    eapply All_local_env_subst; eauto. simpl; intros.
    destruct T; simpl in *.
    + rewrite Nat.add_0_r. eapply substitution_alt; eauto. constructor. constructor.
      2: simpl; eauto; now rewrite app_context_assoc in X0.
      now rewrite subst_empty.
    + rewrite Nat.add_0_r. destruct X0 as [u' Hu']. exists u'.
      eapply (substitution_alt _ _ _ _ _ _ (tSort u')); eauto. constructor. constructor.
      2: simpl; eauto; now rewrite app_context_assoc in Hu'.
      now rewrite subst_empty.
    + right.
      destruct i as [u' Hu']. exists u'.
      eapply (substitution0 _ _ na _ _ _ (tSort u')); eauto.
      apply inversion_Prod in Hu' as [na' [s1 [s2 Hs]]]. intuition.
      eapply type_Conv; pcuic.
      eapply (weakening_cumul Σ Γ [] [vass na A]) in b; pcuic.
      simpl in b. eapply cumul_trans. 2:eauto.
      constructor. constructor. simpl. apply leq_universe_product.

  - eapply declared_constant_inv in H; pcuic.
    destruct decl as [ty [b|] univs]. red in H. simpl in *.
    apply isWfArity_or_Type_subst_instance; pcuic.
    repeat red in H; simpl in *.
    apply isWfArity_or_Type_subst_instance; pcuic.
    destruct H.
    (* TODO: Fix Forall_decls_typing same way as local environments *)
    admit.
  - admit.
  - admit.

  - (* Case *)
    right. red.
    destruct X2.
    + destruct i as [ctx [s [Heq Hs]]].
      exists s.
      unfold check_correct_arity in *.
      assert (ctx = pctx). admit. (* WF of cases *)
      subst ctx.
      pose proof (PCUICClosed.destArity_spec [] pty). rewrite Heq in H.
      simpl in H. subst pty.
      (* assert (#|args| = #|pctx|). admit. (* WF of case *) *)
      eapply type_mkApps. eauto.
      destruct X4. destruct i as [ctx' [s' [Heq' Hs']]].
      elimtype False.
      { clear -Heq'.
        revert Heq'.
        assert (destArity [] (tInd ind u) = None) by reflexivity.
        revert H.
        generalize (tInd ind u). clear. induction args.
        intros. simpl in Heq'. congruence.
        intros. unshelve eapply (IHargs _ _ Heq').
        reflexivity. }
      destruct i as [si Hi].
      destruct (invert_mkApps_tInd wfΣ Hi) as [mdecl' [idecl' [isdecl' Hi']]].
      destruct on_declared_inductive as [onmind onib]; auto.
      destruct Hi' as [[Hargs Hsorts] Hind].
      (* rewrite !PCUICUnivSubst.subst_instance_constr_it_mkProd_or_LetIn in X1. *)
      (* simpl in X1. *)
      (* unfold types_of_case in heq_types_of_case. *)
      (* destruct instantiate_params eqn:Heqinst; noconf heq_types_of_case. *)
      (* destruct destArity as [[args' s']|] eqn:heq_dest; noconf heq_types_of_case. *)
      (* rewrite destArity_it_mkProd_or_LetIn in heq_types_of_case. simpl in heq_types_of_case. *)
      (* destruct map_option_out; noconf heq_types_of_case. *)
      (* clear H. *)
      (* rewrite ind_arity_eq in Heqinst. *)
      (* eapply instantiate_params_make_context_subst in Heqinst. *)
      (* destruct Heqinst as [ctx' [ty'' [s'' [Hdecomp [Hs'' Ht]]]]]. *)
      (* rewrite decompose_prod_n_assum_it_mkProd app_nil_r in Hdecomp. *)
      (* noconf Hdecomp. subst t. *)
      (* eapply make_context_subst_spec in Hs''. *)
      (* rewrite List.rev_involutive in Hs''. *)
      (* rewrite subst_it_mkProd_or_LetIn /= destArity_it_mkProd_or_LetIn /= in heq_dest. *)
      (* noconf heq_dest. rewrite app_context_nil_l. *)
      (* rewrite destArity_it_mkProd_or_LetIn in heq_types_of_case. simpl in heq_types_of_case. *)
      unfold infix_app in Hind. rewrite !subst_instance_constr_it_mkProd_or_LetIn in Hind.
      rewrite -it_mkProd_or_LetIn_app in Hind.
      simpl in Hind.
      admit.
      (* eapply (invert_type_mkApps _ _ (tInd ind u)) in Hi; pcuic. *)
      (* 2:{ econstructor; eauto. admit. (* universes *) } *)
      (* 2:{ admit. } *)
      (* (* Looks ok *) *)
      (* admit. *)

      (* pose proof (invert_type_mkApps Hind args). *)
      (* rewrite !context_assumptions_app !context_assumptions_subst_instance_context in X1 Hargs. *)
      (* forward X1 by lia. *)
      (* forward X1. eapply type_Conv. *)
      (* eauto. left. red. eexists [], _. split; try reflexivity. auto with pcuic. *)
      (* constructor. constructor. *)





      (* eapply typing_spine_arity. auto. *)
      (* rewrite -(List.rev_involutive pctx). *)
      (* eapply make_context_subst_spec. *)

      (* 2:{ admit. } *)
      (* (* Looks ok *) *)
      (* admit. *)

    + destruct i as [ui Hi]. exists ui.
      admit. (* Same idea *)

  - (* Proj *)
    right.
    admit.

  - admit. (* Fix *)
  - admit. (* CoFix *)

  - (* Conv *)
    destruct X2. red in i. left. exact (projT1 i).
    right. destruct s as [u [Hu _]]. now exists u.
Admitted.


Lemma validity_term {Σ Γ t T} :
  wf Σ -> wf_local Σ Γ -> Σ ;;; Γ |- t : T -> isWfArity_or_Type Σ Γ T.
Proof.
  intros. eapply validity; try eassumption.
Defined.
