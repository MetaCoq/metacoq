(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega Lia.
From MetaCoq.Template Require Import config utils monad_utils BasicAst AstUtils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICTyping PCUICWeakening PCUICSubstitution PCUICSafeChecker PCUICRetyping PCUICMetaTheory PCUICWcbvEval PCUICSR  PCUICClosed PCUICGeneration.
From MetaCoq.Extraction Require Import EAst ELiftSubst ETyping EWcbvEval Extract.
From Equations Require Import Equations.
Require Import String.
Local Open Scope list_scope.
Set Asymmetric Patterns.
Import MonadNotation.


Existing Instance config.default_checker_flags.
Module PA := PCUICAst.
Module P := PCUICWcbvEval.

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
  - repeat destruct ? in H; try congruence.
    inv H. econstructor; eauto.
Qed.
    
Lemma monad_map_Forall2 (X Y : Type) (f : X -> typing_result Y) (l1 : list X) (a1 : list Y) :
  monad_map f l1 = Checked a1 -> Forall2 (fun a b => f a = Checked b) l1 a1.
Proof.
  intros. now eapply All2_Forall, monad_map_All2.
Qed.
  
Lemma monad_map_length X Y (f : X -> typing_result Y) (l1  : list X) a :
  monad_map f l1 = Checked a -> #|l1| = #|a|.
Proof.
  revert a; induction l1; cbn; intros.
  - invs H. cbn. congruence.
  - destruct (f a). destruct ? in H. invs H. cbn. f_equal. eauto. invs H. invs H.
Qed.


Lemma monad_map_app X Y (f : X -> typing_result Y) (l1 l2 : list X) a1 a2 :
  monad_map f l1 = Checked a1 -> monad_map f l2 = Checked a2 -> monad_map f (l1 ++ l2) = Checked (a1 ++ a2)%list.
Proof.
  revert a1. induction l1; intros.
  - cbn in *. invs H. eauto.
  - cbn in *. destruct ?. destruct ? in H; try congruence.
    invs H. rewrite (IHl1 _ eq_refl); eauto. invs H.
Qed.

Lemma monad_map_app_invs X Y (f : X -> typing_result Y) (l1 l2 : list X) a :
  monad_map f (l1 ++ l2) = Checked a -> exists a1 a2, monad_map f l1 = Checked a1 /\ monad_map f l2 = Checked a2 /\ (a = a1 ++ a2)%list.
Proof.
  intros. revert a H. induction l1; intros.
  - cbn in *. eauto.
  - cbn in *. destruct ?. destruct ? in H; try congruence.
    invs H. destruct (IHl1 _ eq_refl) as (? & ? & ? & ? & ->).
    do 2 eexists. rewrite H. eauto. invs H.
Qed.

Lemma typing_spine_inv_app Σ x0 l x x1 :
  PCUICGeneration.typing_spine Σ [] x0 (l ++ [x]) x1 -> { '(x2, x3) : _ & (PCUICGeneration.typing_spine Σ [] x0 l x2) * (Σ ;;; [] |- x : x3)}%type.
Proof.
  intros. depind X. destruct l; inv H.
  destruct l; invs H.
  + eexists (_, _). split. econstructor. eauto.
  + specialize (IHX _ _ _ _ eq_refl) as ([] & []).
    eexists (_, _). split.  econstructor; eauto. eauto.
Qed.

Lemma typing_spine_inv:
  forall (Σ : PCUICAst.global_context) (i : inductive) (pars arg : nat) (args : list PCUICAst.term) 
    (a T : PCUICAst.term) (args' : list PCUICAst.term) (u' : universe_instance)
    (H17 : nth_error args (pars + arg) = Some a) (x2 x3 : PCUICAst.term),
    PCUICGeneration.typing_spine Σ [] x2 args x3 ->
    Σ;;; [] |- x3 <= PCUICAst.mkApps (tInd (fst (fst (i, pars, arg))) u') args' -> {T & Σ;;; [] |- a : T}.
Proof.
  intros. simpl in *.
  revert pars arg H17.
  dependent induction X; intros pars arg H17.
  - rewrite nth_error_nil in H17. congruence.
  - destruct (pars + arg)%nat eqn:E.
    + cbn in H17. invs H17. eauto.
    + cbn in H17. eapply IHX.
      eauto. instantiate (2 := 0). eassumption.
Qed.

Lemma typing_spine_cumul:
  forall (Σ : PCUICAst.global_context) (T x1 : PCUICAst.term), Σ;;; [] |- x1 <= T -> typing_spine Σ [] x1 [] T.
Proof.
  intros Σ T x1 X.
Admitted.

Theorem subject_reduction_eval : forall (Σ : PCUICAst.global_context) Γ t u T,
  wf Σ -> Σ ;;; Γ |- t : T -> PCUICWcbvEval.eval Σ Γ t u -> Σ ;;; Γ |- u : T.
Proof.
  intros * wfΣ Hty Hred % wcbeval_red. eapply subject_reduction; eauto.
Qed.

Lemma typing_spine_eval:
  forall (Σ : PCUICAst.global_context) (args args' : list PCUICAst.term) (X : All2 (PCUICWcbvEval.eval Σ []) args args') (bla : wf Σ)
    (T x x0 : PCUICAst.term) (t0 : typing_spine Σ [] x args x0) (c : Σ;;; [] |- x0 <= T) (x1 : PCUICAst.term)
    (c0 : Σ;;; [] |- x1 <= x), typing_spine Σ [] x1 args' T.
Proof.
  intros Σ args args' X wf T x x0 t0 c x1 c0. revert args' X.
  dependent induction t0; intros.
  - inv X.
    eapply (typing_spine_cumul). eapply cumul_trans; eauto.
  - inv X. econstructor.
    + eauto.
    + eapply cumul_trans; eauto.
    + eapply subject_reduction_eval; eauto.
    + eapply IHt0; eauto.
      eapply PCUICCumulativity.red_cumul_inv.
      unfold PCUICLiftSubst.subst1.
      eapply (red_red Σ [] [_] [] [_] [_]).
      eauto. econstructor. eapply wcbeval_red. eauto.
      econstructor. econstructor. econstructor. now rewrite parsubst_empty.
      Grab Existential Variables. econstructor.
Qed.


(* Lemma typing_spine_skipn: *)
(*   forall (Σ : PCUICAst.global_context) (args : list PCUICAst.term) (n0 : nat) (t5 x x0 : PCUICAst.term)  *)
(*     (n : nat) (t3 : PCUICGeneration.typing_spine Σ [] x args x0), *)
(*     {T & PCUICGeneration.typing_spine Σ [] (snd (n0, t5)) (skipn n args) T}. *)
(* Proof. *)
(*   intros Σ args n0 t5 x x0. intros. *)
(*   revert n. dependent induction t3; intros. *)
(*   - cbn. destruct n; unfold skipn; repeat econstructor. *)
(*   - cbn in *. destruct n. *)
(*     + unfold skipn. econstructor. econstructor; eauto. *)
(*       destruct (IHt3 0). *)
(*       assert (skipn 0 tl = tl) by now destruct tl. *)
(*       admit. *)
(*     + unfold skipn. fold (skipn n tl). eauto.       *)
(* Admitted. *)

(** ** on mkApps *)

Lemma emkApps_snoc a l b :
  mkApps a (l ++ [b]) = tApp (mkApps a l) b.
Proof.
  revert a; induction l; cbn; congruence.
Qed.

Lemma mkApps_snoc a l b :
  PCUICAst.mkApps a (l ++ [b]) = PCUICAst.tApp (PCUICAst.mkApps a l) b.
Proof.
  revert a; induction l; cbn; congruence.
Qed.

Lemma mkAppBox_repeat n a :
  mkAppBox a n = mkApps a (repeat tBox n).
Proof.
  revert a; induction n; cbn; firstorder congruence.
Qed.

(* TODO: move *)

(* Lemma is_type_extract (Σ : PCUICAst.global_context) Γ (t : PCUICAst.term) (* T : *) *)
(*   (* Σ ;;; Γ |- t : T -> *) : *)
(*   Extract.is_type_or_proof Σ Γ t = true -> extract Σ Γ t = E.tBox. *)
(* Proof. *)
(*   (* split. *) *)
(*   (* - intros H1. *) *)
(*   (*   destruct t; simpl; try rewrite H1; try reflexivity. *) *)
(*   (*   all: try inversion H1. *) *)
(*   (* - intros. *) *)
(*   (* (* - intros. induction X. *) *) *)
(*   (* (*   all: simpl in H0; try destruct ?; try destruct a0. all: try congruence. *) *) *)
(*   (* (*   cbn in E. destruct is_arity eqn:EE. inv E. *) *) *)
(*   (* (*   all: try now destruct ?; congruence. *) *) *)
(*   (* (*   cbn in E. destruct H. cbn in E. inv E. *) *) *)
(* Admitted. *)

(* Theorem type_of_sound `{Fuel} Σ {Γ t A B} : *)
(*       Σ ;;; Γ |- t : A -> *)
(*       type_of Σ Γ t = Checked B -> *)
(*       (Σ ;;; Γ |- t : B) * (Σ ;;; Γ |- B <= A). *)
(* Admitted. *)

(* Theorem type_of_complete `{Fuel} Σ {Γ t A} : *)
(*       Σ ;;; Γ |- t : A -> *)
(*                     {B & type_of Σ Γ t = Checked B}. *)
(* Admitted. *)


Lemma decompose_app_rec_mkApps f l l' : EAstUtils.decompose_app_rec (mkApps f l) l' =
                                    EAstUtils.decompose_app_rec f (l ++ l').
Proof.
  induction l in f, l' |- *; simpl; auto; rewrite IHl, ?app_nil_r; auto.
Qed.

Lemma decompose_app_mkApps f l :
  isApp f = false -> EAstUtils.decompose_app (mkApps f l) = (f, l).
Proof.
  intros Hf. unfold EAstUtils.decompose_app. rewrite decompose_app_rec_mkApps. rewrite app_nil_r.
  destruct f; simpl in *; (discriminate || reflexivity).
Qed.

Lemma typing_spine_In:
  forall (Σ : PCUICAst.global_context) (args : list PCUICAst.term) 
    (x x0 : PCUICAst.term) (t0 : typing_spine Σ [] x args x0) 
    (x1 : PCUICAst.term) (H : In x1 args), ∑ T1, Σ;;; [] |- x1 : T1.
Proof.
  intros Σ args x x0 t0 x1 H.
Admitted.


Lemma fix_subst_length mfix :
  #|PCUICTyping.fix_subst mfix| = #|mfix|.
Proof.
Admitted.
Lemma fix_context_length mfix :
  #|PCUICLiftSubst.fix_context mfix| = #|mfix|.
Proof.
Admitted.
Lemma fix_subst_length' mfix :
  #|fix_subst mfix| = #|mfix|.
Proof.
Admitted.
