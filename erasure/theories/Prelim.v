(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From MetaCoq.Template Require Import config utils monad_utils BasicAst AstUtils.
From MetaCoq.Erasure Require Import EAst EAstUtils ELiftSubst Extract EArities.
From MetaCoq.PCUIC Require Import PCUICTyping PCUICAst PCUICAstUtils PCUICInduction
     PCUICWeakening PCUICSubstitution PCUICRetyping PCUICMetaTheory
     PCUICWcbvEval PCUICSR  PCUICClosed PCUICInversion PCUICGeneration
     PCUICEquality PCUICContextConversion PCUICConversion PCUICElimination.
From MetaCoq.SafeChecker Require Import PCUICSafeReduce PCUICSafeChecker.
From Coq Require Import ssreflect ssrbool.
Require Import String.
Local Open Scope string_scope.
Set Asymmetric Patterns.
Import MonadNotation.

Require Import Lia.

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
  monad_map f l1 = Checked a1 -> monad_map f l2 = Checked a2 -> monad_map f (l1 ++ l2) = Checked (a1 ++ a2)%list.
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
  monad_map f (l1 ++ l2) = Checked a -> exists a1 a2, monad_map f l1 = Checked a1 /\ monad_map f l2 = Checked a2 /\ (a = a1 ++ a2)%list.
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

Theorem subject_reduction_eval : forall (Σ : PCUICAst.global_env_ext) Γ t u T,
  wf Σ -> Σ ;;; Γ |- t : T -> PCUICWcbvEval.eval Σ Γ t u -> Σ ;;; Γ |- u : T.
Proof.
  intros * wfΣ Hty Hred % wcbeval_red. eapply subject_reduction; eauto.
Qed.

Lemma typing_spine_eval:
  forall (Σ : global_env_ext) Γ (args args' : list PCUICAst.term) (X : All2 (PCUICWcbvEval.eval Σ Γ) args args') (bla : wf Σ)
    (T x x0 : PCUICAst.term) (t0 : typing_spine Σ Γ x args x0) (c : Σ;;; Γ |- x0 <= T) (x1 : PCUICAst.term)
    (c0 : Σ;;; Γ |- x1 <= x), isWfArity_or_Type Σ Γ T -> typing_spine Σ Γ x1 args' T.
Proof.
  intros. eapply typing_spine_red; eauto.
  eapply All2_impl. eassumption. intros. eapply wcbeval_red. eauto.
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
  mkAppBox a n = EAst.mkApps a (repeat tBox n).
Proof.
  revert a; induction n; cbn; firstorder congruence.
Qed.

(** ** Prelim stuff, should move *)

Lemma All2_right_triv {A B} {l : list A} {l' : list B} P :
  All P l' -> #|l| = #|l'| -> All2 (fun _ b => P b) l l'.
Proof.
  induction 1 in l |- *; cbn; intros; destruct l; cbn in *; try omega; econstructor; eauto.
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
    eapply (X 0); cbn; eauto. omega.
    eapply IHL1. eauto.
    intros. eapply (X (S n)); cbn; eauto. omega.
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
  Ee.value (EAst.mkApps tBox L) ->
  L = nil.
Proof.
  intros. depelim H.
  - destruct L using rev_ind.
    reflexivity.
    rewrite emkApps_snoc in H. inv H.
  - destruct (EAstUtils.mkApps_elim t l). EAstUtils.solve_discr.
    rewrite Ee.value_head_spec in H.
    move/andP: H => [H H'].
    eapply Ee.atom_mkApps in H' as [H1 _].
    destruct n, L; discriminate.
  - unfold Ee.isStuckFix in H0. destruct f; try now inversion H0.
    assert (EAstUtils.decompose_app (EAst.mkApps (EAst.tFix m n) args) = EAstUtils.decompose_app (EAst.mkApps tBox L)) by congruence.
    rewrite !EAstUtils.decompose_app_mkApps in H1; eauto. inv H1.
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
    + cbn. rewrite IHm. omega. reflexivity.
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
    + cbn. rewrite IHm. omega. reflexivity.
Qed.

Lemma subslet_fix_subst `{cf : checker_flags} Σ mfix1 T n :
  wf Σ.1 ->
  Σ ;;; [] |- tFix mfix1 n : T ->
  (* wf_local Σ (PCUICLiftSubst.fix_context mfix1) -> *)
  subslet Σ [] (PCUICTyping.fix_subst mfix1) (PCUICLiftSubst.fix_context mfix1).
Proof.
  intro hΣ.
  unfold fix_subst, PCUICLiftSubst.fix_context.
  assert (exists L, mfix1 = mfix1 ++ L)%list by (exists []; now simpl_list). revert H.
  generalize mfix1 at 2 5 6.  intros.
  induction mfix0 using rev_ind.
  - econstructor.
  - rewrite mapi_app. cbn in *. rewrite rev_app_distr. cbn in *.
    rewrite app_length. cbn. rewrite plus_comm. cbn. econstructor.
    + eapply IHmfix0. destruct H as [L]. exists (x :: L). subst. now rewrite <- app_assoc.
    + rewrite <- plus_n_O.
      rewrite PCUICLiftSubst.simpl_subst_k. clear. induction l; cbn; try congruence.
      eapply inversion_Fix in X as (? & ? & ? & ? & ?) ; auto.
      econstructor; eauto. destruct H. subst.
      rewrite <- app_assoc. rewrite nth_error_app_ge. omega.
      rewrite minus_diag. cbn. reflexivity. eapply p.
Qed.

(** ** Prelim on typing *)

Inductive red_decls Σ Γ Γ' : forall (x y : PCUICAst.context_decl), Type :=
| conv_vass na na' T T' : isType Σ Γ' T' -> red Σ Γ T T' ->
                      red_decls Σ Γ Γ' (PCUICAst.vass na T) (PCUICAst.vass na' T')

| conv_vdef_type na na' b T T' : isType Σ Γ' T' -> red Σ Γ T T' ->
                             red_decls Σ Γ Γ' (PCUICAst.vdef na b T) (PCUICAst.vdef na' b T')

| conv_vdef_body na na' b b' T : isType Σ Γ' T ->
                                 Σ ;;; Γ' |- b' : T -> red Σ Γ b b' ->
                                                  red_decls Σ Γ Γ' (PCUICAst.vdef na b T) (PCUICAst.vdef na' b' T).

Notation red_context Σ := (context_relation (red_decls Σ)).

Lemma conv_context_app (Σ : global_env_ext) (Γ1 Γ2 Γ1' : context) :
  wf Σ ->
  wf_local Σ (Γ1 ,,, Γ2) ->
  conv_context Σ Γ1 Γ1' -> conv_context Σ (Γ1 ,,, Γ2) (Γ1' ,,, Γ2).
Proof.
  intros. induction Γ2.
  - cbn; eauto.
  - destruct a. destruct decl_body.
    + cbn. econstructor. inv X0. eauto. econstructor.
      depelim X0.
      eapply PCUICCumulativity.conv_alt_refl; reflexivity.
    + cbn. econstructor. inv X0. eauto. econstructor.
      eapply PCUICCumulativity.conv_alt_refl; reflexivity.
Qed.
