(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From MetaCoq.Template Require Import config utils monad_utils BasicAst AstUtils.
From MetaCoq.Extraction Require Import EAst ELiftSubst Extract.
From MetaCoq.PCUIC Require Import PCUICTyping PCUICAst PCUICAstUtils PCUICInduction  PCUICWeakening PCUICSubstitution PCUICRetyping PCUICMetaTheory PCUICWcbvEval PCUICSR  PCUICClosed PCUICInversion PCUICGeneration PCUICSafeChecker.


Require Import String.
Local Open Scope string_scope.
Set Asymmetric Patterns.
Import MonadNotation.

Module E := EAst.

Require Import Lia.

Existing Instance config.default_checker_flags.
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
  - destruct (arg)%nat eqn:E.
    + cbn in H17. invs H17. eauto.
    + cbn in H17. eauto.
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
    eapply (typing_spine_cumul). eapply cumul_trans. eauto. eapply cumul_trans. eauto. eauto.
  - inv X. econstructor.
    + eauto.
    + eapply cumul_trans; eauto.
    + eapply subject_reduction_eval; eauto.
    + eapply IHt0; eauto.
      eapply PCUICCumulativity.red_cumul_inv.
      unfold PCUICLiftSubst.subst1.
      eapply (red_red Σ [] [_] [] [_] [_]).
      eauto. econstructor. eapply wcbeval_red. eauto.
      econstructor. econstructor. econstructor. 
      Grab Existential Variables. all: repeat econstructor.
Qed.

(** ** on mkApps *)

Lemma emkApps_snoc a l b :
  E.mkApps a (l ++ [b]) = E.tApp (E.mkApps a l) b.
Proof.
  revert a; induction l; cbn; congruence.
Qed.

Lemma mkApps_snoc a l b :
  PCUICAst.mkApps a (l ++ [b]) = PCUICAst.tApp (PCUICAst.mkApps a l) b.
Proof.
  revert a; induction l; cbn; congruence.
Qed.

Lemma mkAppBox_repeat n a :
  mkAppBox a n = E.mkApps a (repeat tBox n).
Proof.
  revert a; induction n; cbn; firstorder congruence.
Qed.

Lemma decompose_app_rec_mkApps f l l' : EAstUtils.decompose_app_rec (E.mkApps f l) l' =
                                    EAstUtils.decompose_app_rec f (l ++ l').
Proof.
  induction l in f, l' |- *; simpl; auto; rewrite IHl, ?app_nil_r; auto.
Qed.

Lemma decompose_app_mkApps f l :
  E.isApp f = false -> EAstUtils.decompose_app (E.mkApps f l) = (f, l).
Proof.
  intros Hf. unfold EAstUtils.decompose_app. rewrite decompose_app_rec_mkApps. rewrite app_nil_r.
  destruct f; simpl in *; (discriminate || reflexivity).
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

Lemma declared_inductive_inj {Σ mdecl mdecl' ind idecl idecl'} :
  declared_inductive Σ mdecl' ind idecl' ->
  declared_inductive Σ mdecl ind idecl ->
  mdecl = mdecl' /\ idecl = idecl'.
Proof.
  intros [] []. unfold declared_minductive in *.
  rewrite H in H1. inv H1. rewrite H2 in H0. inv H0. eauto.
Qed.

Lemma decompose_app_rec_inv2 {t l' f l} :
  decompose_app_rec t l' = (f, l) ->
  isApp f = false.
Proof.
  induction t in f, l', l |- *; try intros [= <- <-]; try reflexivity.
  simpl. apply IHt1.
Qed.

Module Ee := EWcbvEval.

Lemma value_app_inv L :
  Ee.value (E.mkApps tBox L) ->
  L = nil.
Proof.
  intros. depelim H.
  - destruct L using rev_ind.
    reflexivity.
    rewrite emkApps_snoc in H. inv H.
  - induction L using rev_ind.
    + reflexivity.
    + rewrite emkApps_snoc in x. inv x.
  - induction L using rev_ind.
    + reflexivity.
    + rewrite emkApps_snoc in x. inv x.
  - assert (EAst.isApp (EAst.tConstruct i k) = false) by reflexivity.
    assert (EAst.isApp tBox = false) by reflexivity.
    eapply decompose_app_mkApps in H0.
    eapply decompose_app_mkApps in H1.
    rewrite <- x in H1. rewrite H0 in H1.
    inv H1.
Qed.

(** ** Prelim on eliminations  *)

Lemma elim_restriction_works Σ Γ ind npar p c brs :
  (Is_proof Σ Γ (tCase (ind, npar) p c brs) -> False) -> Informative Σ ind.
Proof.
Admitted.

Lemma elim_restriction_works_proj Σ Γ  p c :
  (Is_proof Σ Γ (tProj p c) -> False) -> Informative Σ (fst (fst p)).
Proof.
Admitted.

Lemma length_of_btys {ind mdecl' idecl' args' u' p pty indctx pctx ps btys} :
  types_of_case ind mdecl' idecl' (firstn (ind_npars mdecl') args') u' p pty = Some (indctx, pctx, ps, btys) ->
  #|btys| = #|ind_ctors idecl'|.
Proof.
Admitted.

Lemma tCase_length_branch_inv Σ Γ ind npar p n u args brs T m t :
  wf Σ ->
  Σ ;;; Γ |- tCase (ind, npar) p (mkApps (tConstruct ind n u) args) brs : T ->
  nth_error brs n = Some (m, t) ->
  (#|args| = npar + m)%nat.
Admitted.

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
    + cbn. rewrite IHm. reflexivity. omega.
Qed.

Lemma efix_subst_nth mfix n :
  n < #|mfix| ->
  nth_error (ETyping.fix_subst mfix) n = Some (E.tFix mfix (#|mfix| - n - 1)).
Proof.
  unfold ETyping.fix_subst. generalize (#|mfix|).
  intros m. revert n. induction m; cbn; intros.
  - destruct n; inv H.
  - destruct n.
    + cbn. now rewrite <- minus_n_O.
    + cbn. rewrite IHm. reflexivity. omega.
Qed.

Lemma subslet_fix_subst Σ mfix1 :
  subslet Σ [] (PCUICTyping.fix_subst mfix1) (PCUICLiftSubst.fix_context mfix1).
Proof.
  unfold fix_subst.
  induction mfix1 using rev_ind.
  - econstructor.
  - unfold PCUICLiftSubst.fix_context.
    rewrite mapi_app. cbn. rewrite rev_app_distr. cbn.
Admitted.                       (* subslet_fix_subst *)

(** ** Prelim on typing *)

Lemma typing_subst_instance Σ Γ t T u :
  wf Σ ->
  Σ ;;; Γ |- t : T ->
  Σ ;;; Γ |- PCUICUnivSubst.subst_instance_constr u t : PCUICUnivSubst.subst_instance_constr u T.
Proof.
Admitted.                       (* typing_subst_instance *)

Require Import PCUIC.PCUICGeneration.

Inductive red_decls Σ Γ Γ' : forall (x y : PCUICAst.context_decl), Type :=
| conv_vass na na' T T' : isWfArity_or_Type Σ Γ' T' -> red Σ Γ T T' ->
                      red_decls Σ Γ Γ' (PCUICAst.vass na T) (PCUICAst.vass na' T')

| conv_vdef_type na na' b T T' : isWfArity_or_Type Σ Γ' T' -> red Σ Γ T T' ->
                             red_decls Σ Γ Γ' (PCUICAst.vdef na b T) (PCUICAst.vdef na' b T')

| conv_vdef_body na na' b b' T : Σ ;;; Γ' |- b' : T -> red Σ Γ b b' ->
                                                  red_decls Σ Γ Γ' (PCUICAst.vdef na b T) (PCUICAst.vdef na' b' T).

Notation red_context := (context_relation red_decls).

Lemma env_prop_imp `{checker_flags} P1 P2 :
  (forall Σ Γ t T, P1 Σ Γ t T -> P2 Σ Γ t T) ->
  env_prop P1 -> env_prop P2.
Proof.
  (* intros. econstructor; *)
  (*           specialize (X0 Σ wfΣ Γ wfΓ t T). *)
  (* 2: now eapply X, X0. *)
  (* destruct X0; eauto. cbv. destruct Σ. cbv in f. *)
  (* clear - X f. *)
  (* induction f. *)
  (* - econstructor. eauto. *)
  (* - econstructor. eapply IHf; eauto. *)
  (*   eauto. destruct d. cbn in *. *)
  (*   + destruct c0. cbv in *. *)
  (*     destruct cst_body. eapply X. eauto. *)
  (*     destruct o as []. exists x. *)
  (*     eauto. *)
  (*   + clear IHf. cbv in *. *)
  (*     inv o. econstructor; eauto. *)
  (*     * eapply Alli_impl. eassumption. intros.  *)
  (*       inv X0. *)
  (*       unshelve epose (_ : (on_constructors *)
  (*                              (fun (Σ : list PCUICAst.global_decl × Universes.ConstraintSet.t_) (Γ : list PCUICAst.context_decl)  *)
  (*                                 (t : PCUICAst.term) (T : option PCUICAst.term) => *)
  (*                                 match T with *)
  (*                                 | Some T0 => P2 Σ Γ t T0 *)
  (*                                 | None => ∑ s : ∑ l : list (Universes.Level.t × bool), [] = l -> False, P2 Σ Γ t (PCUICAst.tSort s) *)
  (*                                 end) (Σ, c) k m n x (PCUICAst.ind_ctors x)) *)
  (*                      ). *)
  (*       { *)
  (*         clear - onConstructors X. eapply Alli_impl. eassumption. *)
  (*         intros. inv X0. econstructor. inv X1. exists x1. eauto. *)
  (*         destruct X2. exists x1. admit. *)
  (*       }  *)
        
  (*       econstructor. eassumption. inv onArity. *)
  (*       econstructor. eauto. intros. eapply onProjections in H. inv H. *)
  (*       econstructor. all:eauto. *)
  (*       eapply Alli_impl. eauto. intros. cbn in *. destruct X0. exists x1. eauto. *)
  (*       instantiate (1 := o). *)
  (*       unfold check_ind_sorts in *. *)
  (*       destruct ?. intros. subst. destruct onConstructors. cbn in *. eauto. subst o. *)
  (*       cbn. admit. admit. admit. *)
  (*     * inv onParams. *)
  (*       -- econstructor. *)
  (*       -- econstructor. 2:{ destruct X1. eexists; eauto. } *)
  (*          clear - X X0. induction X0. econstructor. *)
  (*          econstructor. eauto. destruct t0. eexists; eauto. *)
  (*          econstructor. eauto. eauto. *)
  (*       -- unfold on_context. econstructor. *)
  (*          2:{ eauto. } clear - X X0. induction X0. econstructor. *)
  (*          econstructor. eauto. destruct t0. eexists; eauto. *)
  (*          econstructor; eauto. *)
Admitted. (* env_prop is closed under implication, easy but annoying *)

Lemma red_context_conversion :
  env_prop
    (fun (Σ : PCUICAst.global_context) (Γ : PCUICAst.context) (t T : PCUICAst.term) =>
       forall Γ' : PCUICAst.context, red_context Σ Γ Γ' -> Σ;;; Γ' |- t : T).
Proof.
  eapply env_prop_imp. 2: eapply context_conversion.
  intros. eapply X.
  clear - X0.
  Lemma red_conv_context:
    forall (Σ : global_context) (Γ Γ' : context), red_context Σ Γ Γ' -> conv_context Σ Γ Γ'.
  Proof.
    intros Σ Γ Γ' X0.
    induction X0.
    - econstructor.
    - econstructor. eauto. econstructor. inv p. eauto.
      inv p. econstructor. now eapply PCUICCumulativity.red_cumul.
      now eapply PCUICCumulativity.red_cumul_inv.
    - econstructor. eauto. inv p.
      econstructor. eauto. econstructor.
      now eapply PCUICCumulativity.red_cumul.
      now eapply PCUICCumulativity.red_cumul_inv.
      econstructor. eauto.
      econstructor.
      now eapply PCUICCumulativity.red_cumul.
      now eapply PCUICCumulativity.red_cumul_inv.
  Qed.
  now eapply red_conv_context.
Qed.

Lemma conv_context_app (Σ : global_context) (Γ1 Γ2 Γ1' : context) :
  wf Σ ->
  wf_local Σ (Γ1 ,,, Γ2) ->
  conv_context Σ Γ1 Γ1' -> conv_context Σ (Γ1 ,,, Γ2) (Γ1' ,,, Γ2).
Proof.
  intros. induction Γ2.
  - cbn; eauto.
  - destruct a. destruct decl_body.
    + cbn. econstructor. inv X0. eauto. econstructor. 2:eapply conv_refl.
      inv X0. right. cbn in X3. destruct X3. exists x. eapply context_conversion; eauto.
    + cbn. econstructor. inv X0. eauto. econstructor. 2:eapply conv_refl.
      inv X0. right. cbn in X3. destruct X3. exists x. eapply context_conversion; eauto.
Qed.

