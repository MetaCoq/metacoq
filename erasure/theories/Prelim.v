(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils.
From MetaCoq.Erasure Require Import EAstUtils Extract EArities EWcbvEval.
From MetaCoq.PCUIC Require Import PCUICTyping PCUICAst PCUICAstUtils
     PCUICSubstitution PCUICLiftSubst PCUICClosed
     PCUICWcbvEval PCUICSR  PCUICInversion PCUICGeneration
     PCUICContextConversion PCUICCanonicity.
From MetaCoq.SafeChecker Require Import PCUICErrors.
From Coq Require Import Program ssreflect.


Local Existing Instance extraction_checker_flags.

Module PA := PCUICAst.
Module P := PCUICWcbvEval.

Ltac inv H := inversion H; subst; clear H.

Lemma nth_error_app_inv X (x : X) n l1 l2 :
  nth_error (l1 ++ l2) n = Some x -> (n < #|l1| /\ nth_error l1 n = Some x) \/ (n >= #|l1| /\ nth_error l2 (n - List.length l1) = Some x).
Proof.
  destruct (le_lt_dec #|l1| n).
  - intros. rewrite nth_error_app2 in H; eauto.
  - intros. rewrite nth_error_app1 in H; eauto.
Qed.

Lemma monad_map_All2 (X Y : Type) (f : X -> typing_result Y) (l1 : list X) (a1 : list Y) :
  monad_map f l1 = ret a1 -> All2 (fun a b => f a = ret b) l1 a1.
Proof.
  induction l1 in a1 |- *; cbn; intros.
  - inv H. econstructor.
  - revert H.
    case_eq (f a). all: try discriminate. intros b eb.
    simpl.
    case_eq (monad_map f l1). all: try discriminate. intros l' el.
    simpl. intro h. inv h.
    econstructor ; eauto.
Qed.

Lemma monad_map_Forall2 (X Y : Type) (f : X -> typing_result Y) (l1 : list X) (a1 : list Y) :
  monad_map f l1 = Checked a1 -> Forall2 (fun a b => f a = Checked b) l1 a1.
Proof.
  intros. now eapply All2_Forall2, monad_map_All2.
Qed.

Lemma monad_map_length X Y (f : X -> typing_result Y) (l1  : list X) a :
  monad_map f l1 = Checked a -> #|l1| = #|a|.
Proof.
  revert a; induction l1; cbn; intros.
  - invs H. cbn. congruence.
  - revert H.
    case_eq (f a). all: try discriminate. intros x' ex.
    simpl.
    case_eq (monad_map f l1). all: try discriminate. intros l' el.
    simpl. intro h. inv h.
    simpl. f_equal. eauto.
Qed.

Lemma monad_map_app X Y (f : X -> typing_result Y) (l1 l2 : list X) a1 a2 :
  monad_map f l1 = Checked a1 -> monad_map f l2 = Checked a2 -> monad_map f (l1 ++ l2) = Checked (a1 ++ a2).
Proof.
  revert a1. induction l1; intros.
  - cbn in *. invs H. eauto.
  - cbn in *.
    revert H.
    case_eq (f a). all: try discriminate. intros b eb.
    simpl.
    case_eq (monad_map f l1). all: try discriminate. intros l' el.
    simpl. intro h. inv h.
    rewrite (IHl1 _ el H0). simpl. reflexivity.
Qed.

Lemma monad_map_app_invs X Y (f : X -> typing_result Y) (l1 l2 : list X) a :
  monad_map f (l1 ++ l2) = Checked a -> exists a1 a2, monad_map f l1 = Checked a1 /\ monad_map f l2 = Checked a2 /\ (a = a1 ++ a2).
Proof.
  intros. revert a H. induction l1; intros.
  - cbn in *. eauto.
  - cbn in *.
    revert H.
    case_eq (f a). all: try discriminate. intros b eb.
    simpl.
    case_eq (monad_map f (l1 ++ l2)). all: try discriminate. intros l' el.
    simpl. intro h. inv h.
    destruct (IHl1 _ el) as (? & ? & ? & ? & ->).
    eexists _,_. rewrite -> H, H0. intuition eauto.
Qed.

Lemma typing_spine_inv_app Σ x0 l x x1 :
  PCUICGeneration.typing_spine Σ [] x0 (l ++ [x]) x1 -> { '(x2, x3) : _ & (PCUICGeneration.typing_spine Σ [] x0 l x2) * (Σ ;;; [] |- x : x3)}%type.
Proof.
  intros. depind X. destruct l; inv x.
  destruct l; invs x.
  + eexists (_, _). split. econstructor; eauto.  eauto.
  + specialize (IHX _ _ eq_refl) as ([] & []).
    eexists (_, _). split.  econstructor; eauto. eauto.
Qed.

Lemma typing_spine_inv args arg a Σ x2 x3 :
  nth_error args (arg) = Some a ->
  PCUICGeneration.typing_spine Σ [] x2 args x3 ->
  {T & Σ;;; [] |- a : T}.
Proof.
  intros. revert arg H.
  dependent induction X; intros arg H17.
  - rewrite nth_error_nil in H17. congruence.
  - destruct (arg)%nat eqn:EAst.
    + cbn in H17. invs H17. eauto.
    + cbn in H17. eauto.
Qed.

Definition well_typed Σ Γ t := ∑ T, Σ ;;; Γ |- t : T.

Lemma typing_spine_wt args Σ x2 x3 :  wf Σ.1 ->
  PCUICGeneration.typing_spine Σ [] x2 args x3 ->
  All (well_typed Σ []) args.
Proof.
  intros wfΣ sp.
  dependent induction sp; constructor; auto.
  now exists A.
Qed.

Theorem subject_reduction_eval {Σ :global_env_ext} {t u T} {wfΣ : wf Σ} :
  Σ ;;; [] |- t : T -> PCUICWcbvEval.eval Σ t u -> Σ ;;; [] |- u : T.
Proof.
  intros Hty Hred.
  eapply wcbeval_red in Hred; eauto. eapply subject_reduction; eauto.
Qed.

Lemma typing_spine_eval:
  forall (Σ : global_env_ext) (args args' : list PCUICAst.term) 
  (X : All2 (PCUICWcbvEval.eval Σ) args args') (bla : wf Σ)
    (T x x0 : PCUICAst.term) (t0 : typing_spine Σ [] x args x0) 
    (c : Σ;;; [] |- x0 <= T) (x1 : PCUICAst.term)
    (c0 : Σ;;; [] |- x1 <= x), isType Σ [] T -> typing_spine Σ [] x1 args' T.
Proof.
  intros. eapply typing_spine_red; eauto.
  eapply typing_spine_wt in t0; auto.
  eapply All2_All_mix_left in X; eauto. simpl in X.
  eapply All2_impl. eassumption. simpl. intros t u [ct et]. eapply wcbeval_red; eauto.
  eapply (projT2 ct).
Qed.

(** ** on mkApps *)

Lemma emkApps_snoc a l b :
  EAst.mkApps a (l ++ [b]) = EAst.tApp (EAst.mkApps a l) b.
Proof.
  revert a; induction l; cbn; congruence.
Qed.

Lemma mkApps_snoc a l b :
  PCUICAst.mkApps a (l ++ [b]) = PCUICAst.tApp (PCUICAst.mkApps a l) b.
Proof.
  revert a; induction l; cbn; congruence.
Qed.

Lemma mkAppBox_repeat n a :
  mkAppBox a n = EAst.mkApps a (repeat EAst.tBox n).
Proof.
  revert a; induction n; cbn; firstorder congruence.
Qed.

(** ** Prelim stuff, should move *)

Lemma All2_right_triv {A B} {l : list A} {l' : list B} P :
  All P l' -> #|l| = #|l'| -> All2 (fun _ b => P b) l l'.
Proof.
  induction 1 in l |- *; cbn; intros; destruct l; cbn in * ;
  try (exfalso ; lia) ; econstructor; eauto.
Qed.

Lemma All_repeat {A} {n P} x :
  P x -> @All A P (repeat x n).
Proof.
  induction n; cbn; econstructor; eauto.
Qed.

Lemma Alli_impl {A} {P Q} (l : list A) {n} : Alli P n l -> (forall n x, P n x -> Q n x) -> Alli Q n l.
Proof. induction 1; try constructor; intuition auto. Defined.


Lemma All2_map_left {A B C} (P : A -> C -> Type) l l' (f : B -> A) :
  All2 (fun x y => P (f x) y) l l' -> All2 P  (map f l) l'.
Proof. intros. rewrite <- (map_id l'). eapply All2_map; eauto. Qed.

Lemma All2_map_right {A B C} (P : A -> C -> Type) l l' (f : B -> C) :
  All2 (fun x y => P x (f y)) l l' -> All2 P  l (map f l').
Proof. intros. rewrite <- (map_id l). eapply All2_map; eauto. Qed.

Lemma Forall2_Forall_right {A B} {P : A -> B -> Prop} {Q : B -> Prop} {l l'} :
  Forall2 P l l' ->
  (forall x y, P x y -> Q y) ->
  Forall Q l'.
Proof.
  intros HF H. induction HF; constructor; eauto.
Qed.

Lemma All2_from_nth_error A B L1 L2 (P : A -> B -> Type) :
  #|L1| = #|L2| ->
                (forall n x1 x2, n < #|L1| -> nth_error L1 n = Some x1
                                      -> nth_error L2 n = Some x2
                                      -> P x1 x2) ->
                All2 P L1 L2.
Proof.
  revert L2; induction L1; cbn; intros.
  - destruct L2; inv H. econstructor.
  - destruct L2; inv H. econstructor.
    eapply (X 0); cbn; eauto. lia.
    eapply IHL1. eauto.
    intros. eapply (X (S n)); cbn; eauto. lia.
Qed.

Lemma All2_nth_error {A B} {P : A -> B -> Type} {l l'} n t t' :
  All2 P l l' ->
  nth_error l n = Some t ->
  nth_error l' n = Some t' ->
  P t t'.
Proof.
  intros Hall. revert n.
  induction Hall; destruct n; simpl; try congruence.
  eauto.
Qed.

Lemma All_In X (P : X -> Type) (l : list X) x : All P l -> In x l -> squash (P x).
Proof.
  induction 1; cbn; intros; destruct H.
  - subst. econstructor. eauto.
  - eauto.
Qed.

Lemma nth_error_skipn A l m n (a : A) :
  nth_error l (m + n) = Some a ->
  nth_error (skipn m l) n = Some a.
Proof.
  induction m in n, l |- *.
  - cbn. destruct l; firstorder.
  - cbn. destruct l.
    + inversion 1.
    + eapply IHm.
Qed.

Lemma decompose_app_rec_inv2 {t l' f l} :
  decompose_app_rec t l' = (f, l) ->
  isApp f = false.
Proof.
  induction t in f, l', l |- *; try intros [= <- <-]; try reflexivity.
  simpl. apply IHt1.
Qed.

Module Ee := EWcbvEval.

Lemma fst_decompose_app_rec t l : fst (EAstUtils.decompose_app_rec t l) = fst (EAstUtils.decompose_app t).
Proof.
  induction t in l |- *; simpl; auto. rewrite IHt1.
  unfold decompose_app. simpl. now rewrite (IHt1 [t2]).
Qed.

Lemma value_app_inv L :
  Ee.value (EAst.mkApps EAst.tBox L) ->
  L = nil.
Proof.
  intros. depelim X.
  - destruct L using rev_ind.
    reflexivity.
    rewrite emkApps_snoc in i. inv i.
  - destruct (EAstUtils.mkApps_elim t l). EAstUtils.solve_discr.
    rewrite Ee.value_head_spec in i.
    move/andb_and: i => [H H'].
    eapply Ee.atom_mkApps in H' as [H1 _].
    destruct n, L; discriminate.
  - unfold Ee.isStuckFix in i. destruct f; try now inversion i.
    assert (EAstUtils.decompose_app (EAst.mkApps (EAst.tFix m n) args) = EAstUtils.decompose_app (EAst.mkApps EAst.tBox L)) by congruence.
    rewrite !EAstUtils.decompose_app_mkApps in H; eauto. inv H.
Qed.

(** ** Prelim on eliminations  *)
(* Lemma universe_family_is_prop_sort: *)
(*   forall x6 : universe, universe_family x6 = InProp -> Extract.is_prop_sort x6. *)
(* Proof. *)
(*   intros x6 Eu. *)
(* Admitted. *)


(** ** Prelim on fixpoints *)

Lemma fix_subst_nth mfix n :
  n < #|mfix| ->
  nth_error (fix_subst mfix) n = Some (tFix mfix (#|mfix| - n - 1)).
Proof.
  unfold fix_subst. generalize (#|mfix|).
  intros m. revert n. induction m; cbn; intros.
  - destruct n; inv H.
  - destruct n.
    + cbn. now rewrite <- minus_n_O.
    + cbn. rewrite IHm. lia. reflexivity.
Qed.

Lemma efix_subst_nth mfix n :
  n < #|mfix| ->
  nth_error (ETyping.fix_subst mfix) n = Some (EAst.tFix mfix (#|mfix| - n - 1)).
Proof.
  unfold ETyping.fix_subst. generalize (#|mfix|).
  intros m. revert n. induction m; cbn; intros.
  - destruct n; inv H.
  - destruct n.
    + cbn. now rewrite <- minus_n_O.
    + cbn. rewrite IHm. lia. reflexivity.
Qed.

Lemma subslet_fix_subst `{cf : checker_flags} Σ mfix1 T n :
  wf Σ.1 ->
  Σ ;;; [] |- tFix mfix1 n : T ->
  (* wf_local Σ (fix_context mfix1) -> *)
  subslet Σ [] (fix_subst mfix1) (fix_context mfix1).
Proof.
  intro hΣ.
  unfold fix_subst, fix_context.
  assert (exists L, mfix1 = mfix1 ++ L) by (exists []; now simpl_list). revert H.
  generalize mfix1 at 2 5 6.  intros.
  induction mfix0 using rev_ind.
  - econstructor.
  - rewrite mapi_app. cbn in *. rewrite rev_app_distr. cbn in *.
    rewrite app_length. cbn. rewrite plus_comm. cbn. econstructor.
    + eapply IHmfix0. destruct H as [L]. exists (x :: L). subst. now rewrite <- app_assoc.
    + rewrite <- plus_n_O.
      rewrite PCUICLiftSubst.simpl_subst_k. clear. induction l; cbn; try congruence.
      eapply inversion_Fix in X as (? & ? & ? & ? & ? & ? & ?) ; auto.
      econstructor; eauto. destruct H. subst.
      rewrite <- app_assoc. rewrite nth_error_app_ge. lia.
      rewrite minus_diag. cbn. reflexivity.
Qed.

Lemma cofix_subst_nth mfix n :
  n < #|mfix| ->
  nth_error (cofix_subst mfix) n = Some (tCoFix mfix (#|mfix| - n - 1)).
Proof.
  unfold cofix_subst. generalize (#|mfix|).
  intros m. revert n. induction m; cbn; intros.
  - destruct n; inv H.
  - destruct n.
    + cbn. now rewrite <- minus_n_O.
    + cbn. rewrite IHm. lia. reflexivity.
Qed.

Lemma ecofix_subst_nth mfix n :
  n < #|mfix| ->
  nth_error (ETyping.cofix_subst mfix) n = Some (EAst.tCoFix mfix (#|mfix| - n - 1)).
Proof.
  unfold ETyping.cofix_subst. generalize (#|mfix|).
  intros m. revert n. induction m; cbn; intros.
  - destruct n; inv H.
  - destruct n.
    + cbn. now rewrite <- minus_n_O.
    + cbn. rewrite IHm. lia. reflexivity.
Qed.

Lemma subslet_cofix_subst `{cf : checker_flags} Σ mfix1 T n :
  wf Σ.1 ->
  Σ ;;; [] |- tCoFix mfix1 n : T ->
  subslet Σ [] (cofix_subst mfix1) (fix_context mfix1).
Proof.
  intro hΣ.
  unfold cofix_subst, fix_context.
  assert (exists L, mfix1 = mfix1 ++ L)%list by (exists []; now simpl_list). revert H.
  generalize mfix1 at 2 5 6.  intros.
  induction mfix0 using rev_ind.
  - econstructor.
  - rewrite mapi_app. cbn in *. rewrite rev_app_distr. cbn in *.
    rewrite app_length. cbn. rewrite plus_comm. cbn. econstructor.
    + eapply IHmfix0. destruct H as [L]. exists (x :: L). subst. now rewrite <- app_assoc.
    + rewrite <- plus_n_O.
      rewrite PCUICLiftSubst.simpl_subst_k. clear. induction l; cbn; try congruence.
      eapply inversion_CoFix in X as (? & ? & ? & ? & ? & ? & ?) ; auto.
      econstructor; eauto. destruct H. subst.
      rewrite <- app_assoc. rewrite nth_error_app_ge. lia.
      rewrite minus_diag. cbn. reflexivity.
Qed.

(** ** Prelim on typing *)

Inductive red_decls Σ Γ Γ' : forall (x y : context_decl), Type :=
| conv_vass na na' T T' : isType Σ Γ' T' -> red Σ Γ T T' ->
  eq_binder_annot na na' ->
  red_decls Σ Γ Γ' (vass na T) (vass na' T')

| conv_vdef_type na na' b T T' : isType Σ Γ' T' -> red Σ Γ T T' ->
  eq_binder_annot na na' ->
  red_decls Σ Γ Γ' (vdef na b T) (vdef na' b T')

| conv_vdef_body na na' b b' T : isType Σ Γ' T ->
  eq_binder_annot na na' ->
  Σ ;;; Γ' |- b' : T -> red Σ Γ b b' ->
  red_decls Σ Γ Γ' (vdef na b T) (vdef na' b' T).

Notation red_context Σ := (All2_fold (red_decls Σ)).

Lemma conv_context_app (Σ : global_env_ext) (Γ1 Γ2 Γ1' : context) :
  wf Σ ->
  wf_local Σ (Γ1 ,,, Γ2) ->
  conv_context Σ Γ1 Γ1' -> conv_context Σ (Γ1 ,,, Γ2) (Γ1' ,,, Γ2).
Proof.
  intros. induction Γ2.
  - cbn; eauto.
  - destruct a. destruct decl_body.
    + cbn. econstructor. inv X0. eauto. econstructor.
      depelim X0; reflexivity. reflexivity. reflexivity.
    + cbn. econstructor. inv X0. eauto. now econstructor.
Qed.
