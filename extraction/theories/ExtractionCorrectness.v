(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From MetaCoq.Template Require Import config utils monad_utils BasicAst AstUtils.
From MetaCoq.Extraction Require Import EAst ELiftSubst ETyping EWcbvEval Extract Prelim ESubstitution EInversion.
From MetaCoq.PCUIC Require Import PCUICTyping PCUICAst PCUICAstUtils PCUICInduction  PCUICWeakening PCUICSubstitution PCUICChecker PCUICRetyping PCUICMetaTheory PCUICWcbvEval PCUICSR  PCUICClosed PCUICInversion.


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
    eapply Prelim.decompose_app_mkApps in H0.
    eapply Prelim.decompose_app_mkApps in H1.
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
  #|args| = npar + m.
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
Admitted.

(** ** Prelim on typing *)

Lemma typing_subst_instance Σ Γ t T u :
  wf Σ ->
  Σ ;;; Γ |- t : T ->
  Σ ;;; Γ |- PCUICUnivSubst.subst_instance_constr u t : PCUICUnivSubst.subst_instance_constr u T.
Proof.
Admitted.

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
Admitted.

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

Lemma conv_context_app (Σ : global_context) (Γ1 Γ2 Γ1' Γ2' : context) :
  conv_context Σ Γ1 Γ1' -> conv_context Σ Γ2 Γ2' -> conv_context Σ (Γ1 ,,, Γ2) (Γ1' ,,, Γ2').
Proof.
  intros. induction X0; cbn; eauto.
  - econstructor. eauto. inv p. econstructor. admit. admit.
  - econstructor. eauto. inv p. econstructor. admit. admit.
    econstructor. admit. admit.
Admitted.

(** ** Prelim on arities and proofs *)

Lemma isArity_subst_instance u T :
  isArity T ->
  isArity (PCUICUnivSubst.subst_instance_constr u T).
Proof.
  induction T; cbn; intros; tauto.
Qed.


Lemma isArity_ind_type:
  forall idecl : one_inductive_body, isArity (ind_type idecl).
Proof.
  intros idecl.
Admitted.


Lemma Is_type_or_proof_instance_constr Σ Γ T u :
  wf Σ ->  wf_local Σ Γ ->
  Is_Type_or_Proof Σ Γ T ->
  Is_Type_or_Proof Σ Γ (PCUICUnivSubst.subst_instance_constr u T).
Proof.
Admitted.

Lemma Is_type_app Σ Γ t L T :
  wf Σ ->
  Σ ;;; Γ |- mkApps t L : T ->
  Is_Type_or_Proof Σ Γ t ->
  Is_Type_or_Proof Σ Γ (mkApps t L).
Proof.
  (* intros. eapply type_mkApps_inv in X0 as (? & ? & [] & ?); try eassumption. *)
  (* destruct X1 as (? & ? & [ | [u]]). *)
  (* -  *)

  (*   Lemma typing_spine_change : *)
  (*     forall (Σ : global_context) (Γ : context) (t : term) (L : list term) (x1 : term), *)
  (*       Σ;;; Γ |- t : x1 -> forall x x0 : term, Σ;;; Γ |- t : x -> typing_spine Σ Γ x L x0 -> typing_spine Σ Γ x1 L x0. *)
  (*   Proof. *)
  (*     intros Σ Γ t L x1 t2 x x0 t0 t1. *)
  (*   Admitted. *)
  (*   eapply typing_spine_change in t1. 3:eapply t0. 2:eapply t2. clear t0. *)
  (*   revert t t2. *)
  (*   dependent induction t1; intros. *)
  (*   + cbn. exists ty. split; eauto. *)
  (*   + cbn. eapply IHt1. admit. *)
  (*     eauto. eauto. *)
  (* - destruct p.  *)
Admitted.

Notation "Σ ;;; Γ |- s ▷ t" := (eval Σ Γ s t) (at level 50, Γ, s, t at next level) : type_scope.
Notation "Σ ⊢ s ▷ t" := (Ee.eval Σ s t) (at level 50, s, t at next level) : type_scope.

Lemma Is_type_red Σ Γ t v:
  wf Σ ->
  red Σ Γ t v ->
  Is_Type_or_Proof Σ Γ t ->
  Is_Type_or_Proof Σ Γ v.
Proof.
  intros ? ? (T & ? & ?).
  exists T. split.
  - eapply subject_reduction; eauto.
  - eauto.
Qed.

Lemma Is_type_eval Σ Γ t v:
  wf Σ ->
  eval Σ Γ t v ->
  Is_Type_or_Proof Σ Γ t ->
  Is_Type_or_Proof Σ Γ v.
Proof.
  intros; eapply Is_type_red. eauto.
  eapply wcbeval_red; eauto. eauto.
Qed.

Lemma Is_type_lambda Σ Γ na T1 t :
  wf Σ ->
  Is_Type_or_Proof Σ Γ (tLambda na T1 t) ->
  Is_Type_or_Proof Σ (vass na T1 :: Γ) t.
Proof.
  intros ? (T & ? & ?).
  eapply inversion_Lambda in t0 as (? & ? & ? & ? & ?).
  exists x0. split; eauto. destruct s as [ | (u & ? & ?)].
  - left. admit.
  - right. exists u. split; eauto.
Admitted.

Lemma tConstruct_no_Type Σ ind c u x1 :
  Is_Type_or_Proof Σ [] (mkApps (tConstruct ind c u) x1) ->
  Is_proof Σ [] (mkApps (tConstruct ind c u) x1).
Admitted.

(** * Correctness of erasure  *)

Notation "Σ ;;; Γ |- s ▷ t" := (eval Σ Γ s t) (at level 50, Γ, s, t at next level) : type_scope.
Notation "Σ ⊢ s ▷ t" := (Ee.eval Σ s t) (at level 50, s, t at next level) : type_scope.

(** ** Erasure is stable under context conversion *)

Lemma Is_type_conv_context  (Σ : global_context) (Γ : context) t (Γ' : context) :
  wf Σ -> wf_local Σ Γ ->
    conv_context Σ Γ Γ' -> Is_Type_or_Proof Σ Γ t -> Is_Type_or_Proof Σ Γ' t.
Proof.
  intros.
  destruct X2 as (? & ? & ?).
  exists x. split. eapply context_conversion; eauto.
  destruct s as [? | [u []]].
  - eauto.
  - right. exists u. split; eauto. eapply context_conversion; eauto.
Qed.

Lemma erases_context_conversion :
env_prop
  (fun (Σ : PCUICAst.global_context) (Γ : PCUICAst.context) (t T : PCUICAst.term) =>
      forall Γ' : PCUICAst.context, conv_context Σ Γ Γ' -> forall t', erases Σ Γ t t' -> erases Σ Γ' t t').
Proof.
  apply typing_ind_env; intros Σ wfΣ Γ wfΓ; intros **; rename_all_hyps.
  all: match goal with [ H : erases _ _ ?a _ |- ?G ] => tryif is_var a then idtac else inv H end.
  Hint Resolve Is_type_or_proof_instance_constr.
  Hint Resolve Is_type_conv_context.
  all: try now (econstructor; eauto).
  - econstructor. eapply h_forall_Γ'0.
    econstructor. eauto. econstructor. admit. econstructor; eapply cumul_refl'.
    eassumption.
  - econstructor. eauto. eapply h_forall_Γ'1.
    econstructor. eauto. econstructor. admit. econstructor; eapply cumul_refl'.
    eassumption.
  - econstructor. eauto. eauto.
    eapply All2_All_left in X3. 2:{ intros. destruct X1. exact e. }

    eapply All2_impl. eapply All2_All_mix_left.
    all: firstorder.
  - econstructor.

    eapply All2_impl. eapply All2_All_mix_left. eassumption. eassumption.
    intros. cbn in *.
    decompose [prod] X2. repeat split; eauto.
    eapply b0. 2:eauto. subst types.
    
    eapply conv_context_app. eauto. eapply conv_context_refl. eauto. admit. (* wf_local fix_context *)
  - econstructor.

    eapply All2_impl. eapply All2_All_mix_left. eassumption. eassumption.
    intros. cbn in *.
    decompose [prod] X2. repeat split; eauto.
    eapply b0. 2:eauto. subst types.
  
    eapply conv_context_app. eauto. eapply conv_context_refl. eauto. admit. (* wf_local fix_context *)
  - eauto.
Admitted.

Lemma erases_red_context_conversion :
env_prop
  (fun (Σ : PCUICAst.global_context) (Γ : PCUICAst.context) (t T : PCUICAst.term) =>
      forall Γ' : PCUICAst.context, red_context Σ Γ Γ' -> forall t', erases Σ Γ t t' -> erases Σ Γ' t t').
Proof.
  eapply env_prop_imp.
  2: eapply erases_context_conversion.
  intros. cbn in *. eapply H; eauto.
  eapply red_conv_context; eauto.
Qed.

(** ** Erasure is stable under substituting universe constraints  *)

Lemma erases_subst_instance_constr :
  forall Σ, wf Σ ->
  forall Γ, wf_local Σ Γ ->
  forall t T, Σ ;;; Γ |- t : T ->
  forall t' u,
    Σ ;;; Γ |- t ⇝ℇ t' ->
    Σ ;;; Γ |- PCUICUnivSubst.subst_instance_constr u t ⇝ℇ t'.
Proof.
  apply (typing_ind_env (fun Σ Γ t T =>
                           forall t' u,
                             Σ ;;; Γ |- t ⇝ℇ t' ->
                                       Σ ;;; Γ |- PCUICUnivSubst.subst_instance_constr u t ⇝ℇ t'
        )); intros; cbn -[PCUICUnivSubst.subst_instance_constr] in *.
  all: match goal with [ H : erases _ _ ?a _ |- ?G ] => tryif is_var a then idtac else inv H end.
  Hint Resolve Is_type_or_proof_instance_constr. 
  all: try now (econstructor; eauto).
  all:cbn.
Admitted.

(** ** Erasure and applications  *)

Lemma erases_App Σ Γ f L T t :
  Σ ;;; Γ |- tApp f L : T ->
  erases Σ Γ (tApp f L) t ->
  (t = tBox × squash (Is_Type_or_Proof Σ Γ (tApp f L)))
  \/ exists f' L', t = E.tApp f' L' /\
             erases Σ Γ f f' /\
             erases Σ Γ L L'.
Proof.
  intros. generalize_eqs H.
  revert f L X.
  inversion H; intros; try congruence; subst.
  - inv H4. right. repeat eexists; eauto.
  - left. split; eauto. econstructor; eauto.
Qed.

Lemma erases_mkApps Σ Γ f f' L L' :
  erases Σ Γ f f' ->
  Forall2 (erases Σ Γ) L L' ->
  erases Σ Γ (mkApps f L) (E.mkApps f' L').
Proof.
  intros. revert f f' H; induction H0; cbn; intros; eauto.
  eapply IHForall2. econstructor. eauto. eauto.
Qed.

Lemma erases_mkApps_inv Σ Γ f L T t :
  wf Σ ->
  Σ ;;; Γ |- mkApps f L : T ->
  Σ;;; Γ |- mkApps f L ⇝ℇ t ->
  (exists L1 L2 L2', L = (L1 ++ L2)%list /\
                squash (Is_Type_or_Proof Σ Γ (mkApps f L1)) /\
                erases Σ Γ (mkApps f L1) tBox /\
                Forall2 (erases Σ Γ) L2 L2' /\
                t = E.mkApps tBox L2'
  )
  \/ exists f' L', t = E.mkApps f' L' /\
             erases Σ Γ f f' /\
             Forall2 (erases Σ Γ) L L'.
Proof.
  intros wfΣ. intros. revert f X H ; induction L; cbn in *; intros.
  - right. exists t, []. cbn. repeat split; eauto.
  - eapply IHL in H; eauto.
    destruct H as [ (? & ? & ? & ? & [] & ? & ? & ?) | (? & ? & ? & ? & ?)].
    + subst. left. exists (a :: x), x0, x1. repeat split; eauto.
    + subst. eapply type_mkApps_inv in X as (? & ? & [] & ?); eauto.
      eapply erases_App in H0 as [ (-> & []) | (? & ? & ? & ? & ?)].
      * left. exists [a], L, x0. cbn. repeat split. eauto.
        econstructor; eauto.  eauto.
      * subst. right. exists x3, (x4 :: x0). repeat split.
        eauto. econstructor. eauto. eauto.
      * eauto.
Qed.      

(** ** Global erasure  *)

Lemma lookup_env_erases Σ c decl Σ' :
  wf Σ ->
  erases_global Σ Σ' ->
  PCUICTyping.lookup_env (fst Σ) c = Some (ConstantDecl c decl) ->
  exists decl', ETyping.lookup_env Σ' c = Some (E.ConstantDecl c decl') /\
           erases_constant_body Σ decl decl'.
Proof.
  unfold erases_global. destruct Σ as (Σ, univs).
  intros. induction H; cbn in *.
  - inv H0.
  - destruct ?.
    + inv H0.
      exists cb'. split; eauto. unfold erases_constant_body in *.
      destruct ?. destruct ?. 
      * eapply erases_extends. 6: eassumption.
        eapply PCUICWeakeningEnv.wf_extends.
        eassumption. now eexists [_]. eauto.
        { inv X. cbn in X1. unfold on_constant_decl in X1. rewrite E0 in *. cbn in X1. eassumption. }
        eauto. now eexists [_].
      * eassumption.
      * destruct ?; tauto.
    + edestruct IHerases_global_decls as (decl' & ? & ?).
      eapply PCUICWeakeningEnv.wf_extends.
      eassumption. now eexists [_]. eauto.
      exists decl'. split. eauto.
      unfold erases_constant_body in *. clear H. destruct ?. destruct ?.
      * eapply erases_extends. 6: eassumption.
        eapply PCUICWeakeningEnv.wf_extends.
        eassumption. now eexists [_]. eauto.
        eapply (PCUICWeakeningEnv.declared_constant_inv (Σ, univs)) in H0; eauto.
        unfold on_constant_decl in H0. rewrite E0 in H0. unfold lift_typing in H0. eassumption.
        eapply PCUICWeakeningEnv.weaken_env_prop_typing. eapply PCUICWeakeningEnv.wf_extends. eauto.
        eexists [_]. reflexivity. eapply PCUICWeakeningEnv.wf_extends. eauto. now eexists [_].
        eauto. now eexists [_].
      * tauto.
      * destruct ?; tauto.
  - destruct ?.
    + inv H0.
    + edestruct IHerases_global_decls as (decl' & ? & ?).
      eapply PCUICWeakeningEnv.wf_extends.
      eassumption. now eexists [_]. eauto.
      exists decl'. split. eauto.
      unfold erases_constant_body in *. clear H. destruct ?. destruct ?.
      * eapply erases_extends. 6: eassumption.
        eapply PCUICWeakeningEnv.wf_extends.
        eassumption. now eexists [_]. eauto.
        eapply (PCUICWeakeningEnv.declared_constant_inv (Σ, univs)) in H0; eauto.
        unfold on_constant_decl in H0. rewrite E0 in H0. unfold lift_typing in H0. eassumption.
        eapply PCUICWeakeningEnv.weaken_env_prop_typing. eapply PCUICWeakeningEnv.wf_extends. eauto.
        eexists [_]. reflexivity. eapply PCUICWeakeningEnv.wf_extends. eauto. now eexists [_].
        eauto. now eexists [_].
      * tauto.
      * destruct ?; tauto.
Qed.        

(** ** The correctness proof  *)

Record extraction_pre (Σ : global_context) : Type
  := Build_extraction_pre
  { extr_env_axiom_free' : is_true (axiom_free (fst Σ));
    extr_env_wf' : wf Σ }.

Hint Constructors PCUICWcbvEval.eval erases.

Lemma erases_correct Σ t T t' v Σ' :
  extraction_pre Σ ->
  Σ;;; [] |- t : T ->
  Σ;;; [] |- t ⇝ℇ t' ->
   erases_global Σ Σ' ->
  Σ;;; [] |- t ▷ v ->
  exists v', Σ;;; [] |- v ⇝ℇ v' /\ Σ' ⊢ t' ▷ v'.
Proof.
  intros pre Hty He Heg H.
  revert T Hty t' He.
  induction H using PCUICWcbvEval.eval_evals_ind; intros T Hty t' He; inv pre.
  - assert (Hty' := Hty).
    assert (eval Σ [] (PCUICAst.tApp f a) res) by eauto.
    eapply inversion_App in Hty as (? & ? & ? & ? & ? & ?).
        
    inv He.
    + eapply IHeval1 in H4 as (vf' & Hvf' & He_vf'); eauto.
      eapply IHeval2 in H6 as (vu' & Hvu' & He_vu'); eauto.
      pose proof (subject_reduction_eval Σ [] _ _ _ extr_env_wf'0 t0 H).
        eapply inversion_Lambda in X0 as (? & ? & ? & ? & ?).
        assert (Σ ;;; [] |- a' : t). {
          eapply subject_reduction_eval; eauto.
          eapply cumul_Prod_inv in c0 as [].
          econstructor. eassumption. eauto. eapply c0. }
      inv Hvf'.
      * assert (Σ;;; [] |- PCUICLiftSubst.subst1 a' 0 b ⇝ℇ subst1 vu' 0 t').
        eapply (erases_subst Σ [] [PCUICAst.vass na t] [] b [a'] t'); eauto.
        econstructor. econstructor. rewrite parsubst_empty. eassumption.
        eapply IHeval3 in H2 as (v' & Hv' & He_v').
        -- exists v'. split; eauto.
           econstructor; eauto.
        -- eapply substitution0; eauto. 
      * exists tBox. split. econstructor.
        eapply Is_type_lambda in X1; eauto.
        eapply (is_type_subst Σ [] [PCUICAst.vass na _] [] _ [a']) in X1.
        cbn in X1.
        eapply Is_type_eval.
        eauto. eapply H1. eassumption.
        all: eauto. econstructor. econstructor. rewrite parsubst_empty.
        eauto. econstructor. eauto.
    + exists tBox. split. 2:econstructor; eauto.
      econstructor.
      eapply Is_type_eval; eauto.
  - assert (Hty' := Hty).
    assert (Σ ;;; [] |- tLetIn na b0 t b1 ▷ res) by eauto.
    eapply inversion_LetIn in Hty' as (? & ? & ? & ? & ? & ?).

    inv He.
    + eapply IHeval1 in H6 as (vt1' & Hvt2' & He_vt1'); eauto.
      assert (Hc :red_context Σ ([],, vdef na b0 t) [vdef na b0' t]). {
        econstructor. econstructor. econstructor. eapply subject_reduction_eval; eauto.
        eapply wcbeval_red; eauto.         
      }
      assert (Σ;;; [vdef na b0' t] |- b1 : x0). {
        cbn in *. eapply red_context_conversion. 3:eauto. all:eauto. 
      }
      assert (Σ;;; [] |- PCUICLiftSubst.subst1 b0' 0 b1 ⇝ℇ subst1 vt1' 0 t2'). {
        eapply (erases_subst Σ [] [PCUICAst.vdef na b0' t] [] b1 [b0'] t2'); eauto.
        enough (subslet Σ [] [PCUICLiftSubst.subst [] 0 b0'] [vdef na b0' t]).
        now rewrite parsubst_empty in X1.
        econstructor. econstructor.
        rewrite !parsubst_empty.
        eapply subject_reduction_eval; eauto.
        eapply erases_red_context_conversion. 4: eassumption.
        all: cbn; eauto.
      }        
      eapply IHeval2 in H1 as (vres & Hvres & Hty_vres).
      2:{ eapply substitution_let; eauto. }
      exists vres. split. eauto. econstructor; eauto.
    + exists tBox. split. 2:econstructor; eauto.
      econstructor. eapply Is_type_eval; eauto.
  - inv isdecl.
  - inv isdecl.
  - assert (Hty' := Hty).
    assert (Σ ;;; [] |- tCase (ind, pars) p discr brs ▷ res) by eauto.
    eapply inversion_Case in Hty' as (u' & args' & mdecl & idecl & pty & indctx & pctx & ps & btys & ? & ? & ? & ? & ? & ? & ? & ? & ?).
    assert (Σ ;;; [] |- mkApps (tConstruct ind c u) args :  mkApps (tInd ind u') args').
    eapply subject_reduction_eval; eauto.
    eapply type_mkApps_inv in X0 as (? & ? & [] & ?); eauto.
    eapply inversion_Construct in t1 as (mdecl' & idecl' & cdecl & ? & ? & ? & ?).
    assert (d1 := d0).
    destruct d0.

    edestruct (declared_inductive_inj H1 d). subst.
        
    pose proof (length_of_btys e0).
    
    inv He.
    + eapply IHeval1 in H11 as (v' & Hv' & He_v'); eauto.
      eapply erases_mkApps_inv in Hv' as [(? & ? & ? & ? & [] & ? & ? & ?) | (? & ? & ? & ? & ?)]; eauto.
      3: eapply subject_reduction_eval; eauto.
      * subst.

        eapply Is_type_app in X0. 2:eauto. 2:{ rewrite mkApps_nested. eapply subject_reduction_eval; eauto. }
        rewrite mkApps_nested in X0.
        
        eapply tConstruct_no_Type in X0.
        eapply H10 in X0 as []; eauto. 2: exists []; now destruct Σ.
        
        destruct (ind_ctors idecl'). cbn in H4. destruct c; inv H2.
        destruct l; cbn in *; try omega. destruct c as [ | []]; cbn in H2; inv H2.

        destruct btys as [ | ? []]; cbn in H3; try omega. clear H3 H4. destruct H7.
        (* eapply H7 in d1. *) inv a. inv X2. inv H12. inv H8. destruct H4. destruct x4, y; cbn in *; subst.
        destruct X1. subst. destruct p0; cbn in *.

        edestruct (IHeval2) as (? & ? & ?).
        eapply subject_reduction. eauto. exact Hty.
        etransitivity.
        eapply PCUICReduction.red_case. econstructor. eapply wcbeval_red. eauto.
        eapply PCUICReduction.All2_same. intros. econstructor. econstructor. econstructor.
        econstructor.
        
        unfold iota_red. cbn.
        eapply erases_mkApps. eauto.
        instantiate (1 := repeat tBox _).
        eapply All2_Forall.
        eapply All2_impl.
        eapply All2_All_mix_left. eassumption.
        2:{ intros. destruct X1. assert (y = tBox). exact y0. subst. econstructor.
            now eapply Is_Type_or_Proof_Proof. }

        eapply All2_right_triv. 2: now rewrite repeat_length.

        now eapply All_repeat.
          
        (* destruct x4; cbn in e2; subst. destruct X2. destruct p0; cbn in e2; subst. cbn in *.  destruct y.  *)
        exists x4. split; eauto. eapply eval_iota_sing.  2:eauto.
        pose proof (Ee.eval_to_value _ _ _ He_v').
        eapply value_app_inv in H4. subst. eassumption.

        eapply tCase_length_branch_inv in extr_env_wf'0.
        2:{ eapply subject_reduction. eauto.
            exact Hty.
            eapply PCUICReduction.red_case. econstructor. eapply wcbeval_red. eauto.
            econstructor. econstructor. econstructor. }
        2: reflexivity.

        enough (#|skipn (ind_npars mdecl') (x1 ++ x2)| = n) as <- by eauto.
        rewrite skipn_length. rewrite extr_env_wf'0. omega.
        rewrite extr_env_wf'0. omega.
      * subst. unfold iota_red in *.
        destruct (nth_error brs c) eqn:Hnth.
        2:{ eapply nth_error_None in Hnth. erewrite All2_length in Hnth. 2:exact a. rewrite H3 in Hnth.
            eapply nth_error_Some_length in H2. cbn in H2. omega.
        }
        rewrite <- nth_default_eq in *. unfold nth_default in *.
        rewrite Hnth in *.

        destruct (All2_nth_error_Some _ _ H12 Hnth) as (? & ? & ? & ?).
        destruct (All2_nth_error_Some _ _ a Hnth) as (? & ? & ? & ?).
        destruct p0, x4. cbn in *. subst.
        edestruct IHeval2 as (? & ? & ?).
        eapply subject_reduction. eauto. exact Hty.
        etransitivity.
        eapply PCUICReduction.red_case. econstructor. eapply wcbeval_red. eauto.
        eapply PCUICReduction.All2_same. intros. econstructor.
        etransitivity. eapply trans_red. econstructor.
        econstructor. unfold iota_red. rewrite <- nth_default_eq. unfold nth_default.
        rewrite Hnth. econstructor.
        
        eapply erases_mkApps. eauto.
        eapply Forall2_skipn. eauto.
        inv H5.
        -- exists x4. split; eauto.
           econstructor. eauto. unfold ETyping.iota_red.
           rewrite <- nth_default_eq. unfold nth_default. rewrite e. cbn. eauto.
        -- eapply Is_type_app in X0. 2:eauto. 2:{ eapply subject_reduction_eval. 3:eassumption. all: eauto. }
        
           eapply tConstruct_no_Type in X0.
           eapply H10 in X0 as []; eauto. 2: exists []; now destruct Σ.
        
           destruct (ind_ctors idecl'). cbn in H4. destruct c; inv H2.
           destruct l; cbn in *; try omega. destruct c as [ | []]; cbn in H2; inv H2.
           
           destruct btys as [ | ? []]; cbn in H3; try omega. clear H3 H4. destruct H8.
           (* eapply H7 in d1. *) inv a. inv X2. inv H12. inv H9. destruct H4. destruct x1, y; cbn in *; subst.
           destruct X1. subst. destruct p0; cbn in *. destruct x3. inv e. inv Hnth. cbn in *.
           
           edestruct (IHeval2) as (? & ? & ?). 
           eapply subject_reduction. eauto. exact Hty.
           etransitivity.
           eapply PCUICReduction.red_case. econstructor. eapply wcbeval_red. eauto.
           eapply PCUICReduction.All2_same. intros. econstructor. econstructor. econstructor.
           econstructor.

           eapply erases_mkApps. eauto.
           instantiate (1 := repeat tBox _).
           eapply All2_Forall.
           eapply All2_impl.
           eapply All2_All_mix_left. eassumption.
           2:{ intros. destruct X1. assert (y = tBox). exact y0. subst. econstructor.
               now eapply Is_Type_or_Proof_Proof. }

           eapply All2_right_triv. 2:now rewrite repeat_length.
           now eapply All_repeat.

           exists x1. split; eauto.
           eapply eval_iota_sing.
           pose proof (Ee.eval_to_value _ _ _ He_v').
           eapply value_app_inv in H4. subst. eassumption. 
           reflexivity. cbn in *.
           enough (#|skipn (ind_npars mdecl') args| = n0) as <- by eauto.

           eapply tCase_length_branch_inv in extr_env_wf'0.
           2:{ eapply subject_reduction. eauto.
               exact Hty.
               eapply PCUICReduction.red_case. econstructor. eapply wcbeval_red. eauto.
               econstructor. econstructor. econstructor. }
           2: reflexivity.

           enough (#|skipn (ind_npars mdecl') args| = n0) as <- by eauto.
           rewrite skipn_length. rewrite extr_env_wf'0. omega.
           rewrite extr_env_wf'0. omega.
    + exists tBox. split. econstructor. 
      eapply Is_type_eval; eauto. econstructor; eauto.
  - assert (Hty' := Hty). 
    assert (Σ ;;; [] |- mkApps (tFix mfix idx) args ▷ res) by eauto.
    eapply type_mkApps_inv in Hty' as (? & ? & [] & ?); eauto.
    eapply EInversion.type_tFix_inv in t as (? & [[] ?] & ?); eauto.
    unfold unfold_fix in H. rewrite e in H. inv H. 

    eapply erases_mkApps_inv in He as [(? & ? & ? & ? & [] & ? & ? & ?) | (? & ? & ? & ? & ?)]; eauto.
    + subst.
      exists tBox. split. 2:eapply eval_box_apps; econstructor; eauto.
      econstructor. 
      eapply Is_type_eval. eauto. eassumption.
      rewrite <- mkApps_nested.
      eapply Is_type_app. eassumption.
      rewrite mkApps_nested; eauto.
      eauto.
    + subst.
      inv H3.
      * assert (Hmfix' := H7).
        eapply All2_nth_error_Some in H7 as (? & ? & ? & ? & ?); eauto.
        destruct x1. cbn in *. subst.
        eapply (erases_subst Σ [] (PCUICLiftSubst.fix_context mfix) [] dbody (fix_subst mfix)) in e3; cbn; eauto.
        -- enough (exists L, Forall2 (erases Σ []) args' L /\ Forall2 (Ee.eval Σ') x3 L). 
           ++ cbn in e3. destruct H as (L & ? & ?).
              assert (Hv : Forall Ee.value L).
              { eapply Forall2_Forall_right; eauto.
                intros. eapply EWcbvEval.eval_to_value. eauto.
              } 
                
              eapply erases_mkApps in e3; eauto.
              eapply IHeval in e3 as (? & ? & ?); cbn; eauto.
              exists x1. split. eauto. econstructor. unfold ETyping.unfold_fix.
              rewrite e0. reflexivity.
              eassumption.
              all:eauto.
              ** unfold is_constructor in *.
                 destruct ?; inv H1.
                 unfold is_constructor_or_box.
                 eapply Forall2_nth_error_Some in H as (? & ? & ?); eauto.
                 rewrite H.
                 
                 unfold isConstruct_app in H8.
                 destruct (decompose_app t) eqn:EE.
                 assert (E2 : fst (decompose_app t) = t1) by now rewrite EE. 
                 destruct t1.
                 all:inv H8.
                 (* erewrite <- PCUICConfluence.fst_decompose_app_rec in E2. *)
                 
                 pose proof (PCUICConfluence.decompose_app_rec_inv EE).
                 cbn in H7. subst.
                 assert (∑ T, Σ ;;; [] |- mkApps (tConstruct ind n ui) l : T) as [T' HT'].
                 { eapply typing_spine_eval in t0; eauto.
                   eapply typing_spine_In; eauto.
                   eapply nth_error_In; eauto. }
                 eapply erases_mkApps_inv in H1.
                 destruct H1 as [ (? & ? & ? & ? & [] & ? & ? & ?) | (? & ? & ? & ? & ?) ].
                 --- subst.
                     eapply nth_error_forall in Hv; eauto.
                     eapply value_app_inv in Hv. subst. reflexivity.
                 --- subst. inv H7. 
                     +++ eapply nth_error_forall in Hv; eauto.
                         destruct x6 using rev_ind; cbn - [EAstUtils.decompose_app]. reflexivity.
                         rewrite emkApps_snoc at 1.
                         generalize (x6 ++ [x4])%list. clear. intros.
                         rewrite Prelim.decompose_app_mkApps. reflexivity.
                         reflexivity.
                     +++ eapply nth_error_forall in Hv; eauto.
                         eapply value_app_inv in Hv. subst. eauto.                         
                 --- eauto.
                 --- eauto.
              ** eapply type_mkApps.
                 --- eapply (substitution Σ [] (PCUICLiftSubst.fix_context mfix) (fix_subst mfix) []); eauto.
                     
                     eapply subslet_fix_subst.
                     eapply nth_error_all in a0; eauto. cbn in a0.
                     eapply a0.
                 --- cbn.
                     eapply typing_spine_eval in t0. 2-5:eauto.
                     rewrite (plus_n_O #|PCUICLiftSubst.fix_context mfix|).
                     rewrite fix_context_length.
                     rewrite <- fix_subst_length.
                     rewrite PCUICLiftSubst.simpl_subst.
                     now rewrite PCUICLiftSubst.lift0_id. omega.
           ++ clear - t0 H0 H4. revert x t0 x3 H4; induction H0; intros.
              ** inv H4. exists []; eauto.
              ** inv H4. inv t0. eapply r in H2 as (? & ? & ?); eauto.
                 eapply IHAll2 in H5 as (? & ? & ?); eauto.
        -- eapply subslet_fix_subst.
        -- eapply nth_error_all in a0; eauto. cbn in a0.
           eapply a0.
        -- eapply All2_from_nth_error.
           erewrite fix_subst_length, ETyping.fix_subst_length, All2_length; eauto.
           intros.
           rewrite fix_subst_nth in H3. 2:{ now rewrite fix_subst_length in H. }
           rewrite efix_subst_nth in H5. 2:{ rewrite fix_subst_length in H.
                                             erewrite <- All2_length; eauto. }
           inv H3; inv H5.
           erewrite All2_length; eauto.
      * exists tBox. split.
        econstructor. 
        eapply Is_type_eval. eauto. eassumption.
        eapply Is_type_app. eauto. eauto. eauto.
        eapply eval_box_apps. econstructor. eauto.
  - destruct Σ as (Σ, univs).
    unfold erases_global in Heg.
    assert (Σ ;;; [] |- tConst c u ▷ res) by eauto.
    (* eapply type_Const_inv in Hty. *)    
    inv He.
    + assert (H' := H).
      eapply lookup_env_erases in H; eauto.
      destruct H as (decl' & ? & ?).
      unfold erases_constant_body in H2. rewrite H0 in *.
      destruct ?; try tauto.
      edestruct IHeval.
      * eapply typing_subst_instance. eauto.
        eapply PCUICWeakeningEnv.declared_constant_inv in H'; eauto.
        unfold on_constant_decl in H'. rewrite H0 in H'. eapply H'.
        eapply PCUICWeakeningEnv.weaken_env_prop_typing.
      * eapply erases_subst_instance_constr; eauto.
        eapply PCUICWeakeningEnv.declared_constant_inv in H'; eauto.
        unfold on_constant_decl in H'. rewrite H0 in H'. eapply H'.
        eapply PCUICWeakeningEnv.weaken_env_prop_typing.        
      * destruct H3. exists x. split; eauto. econstructor; eauto.
    + exists tBox. split. econstructor.
      eapply Is_type_eval. 3: eassumption. eauto. eauto. econstructor. eauto.
  - pose (Hty' := Hty).
    eapply inversion_Proj in Hty' as (? & ? & ? & [] & ? & ? & ? & ? & ?). 
    inv He.
    + rename H7 into H6. eapply IHeval1 in H6 as (vc' & Hvc' & Hty_vc'); eauto.
      eapply erases_mkApps_inv in Hvc'; eauto.
      2: eapply subject_reduction_eval; eauto.
      destruct Hvc' as [ (? & ? & ? & ? & [] & ? & ? & ?) | (? & ? & ? & ? & ?)]; subst.
      * exists tBox. split.

        eapply Is_type_app in X; eauto. 2:{ rewrite mkApps_nested. eapply subject_reduction_eval; eauto. }
        rewrite mkApps_nested in X.
        
        eapply tConstruct_no_Type in X. eapply H5 in X as [? []]; eauto.
        2: now destruct d. 2: now exists []; destruct Σ.
                                    
        econstructor. 
        eapply Is_type_eval. eauto. eauto.
        eapply nth_error_all.
        eapply nth_error_skipn. eassumption.
        eapply All_impl. assert (pars = ind_npars x0). destruct d as (? & ? & ?). now rewrite H9. subst.
        eassumption.
        eapply Is_Type_or_Proof_Proof.

        eapply eval_proj_box.
        pose proof (Ee.eval_to_value _ _ _ Hty_vc').
        eapply value_app_inv in H3. subst. eassumption.        
      * rename H5 into Hinf.
        rename H6 into H5.
        eapply Forall2_nth_error_Some in H5 as (? & ? & ?); eauto.
        assert (Σ ;;; [] |- mkApps (tConstruct i k u) args : mkApps (tInd i x) x2).
        eapply subject_reduction_eval; eauto.
        eapply type_mkApps_inv in X as (? & ? & [] & ?); eauto.
        eapply typing_spine_In in t2 as [].
        2: eapply nth_error_In; eauto.
        eapply IHeval2 in H5 as (? & ? & ?); eauto. 
        inv H4.
        -- exists x9. split; eauto. econstructor. eauto.
           rewrite <- nth_default_eq. unfold nth_default. now rewrite H3.
        -- exists tBox. split.

           eapply Is_type_app in X; eauto. 2:{ eapply subject_reduction_eval. 3: eauto. eauto. eauto. }
           
           eapply tConstruct_no_Type in X. eapply Hinf in X as [? []]; eauto.
           2: now destruct d. 2: now exists []; destruct Σ.
                                       
           econstructor. 
           eapply Is_type_eval. eauto. eauto.
           eapply nth_error_all.
           eapply nth_error_skipn. eassumption.
           eapply All_impl. assert (pars = ind_npars x0). destruct d as (? & ? & ?). now rewrite H9. subst.
           eassumption.
           eapply Is_Type_or_Proof_Proof.

           eapply eval_proj_box.
           pose proof (Ee.eval_to_value _ _ _ Hty_vc').
           eapply value_app_inv in H4. subst. eassumption.
    + exists tBox. split. econstructor.
      eapply Is_type_eval. 3: eassumption. eauto. eauto. econstructor. eauto.
  - inv He.
    + eexists. split; eauto. econstructor.
    + eexists. split; eauto. now econstructor.
  - inv He. eexists. split; eauto. now econstructor.
  - inv He. eexists. split; eauto. now econstructor.
  - assert (Σ ;;; [] |- mkApps (tInd i u) l' : T).
    eapply subject_reduction_eval; eauto; econstructor; eauto.
    assert (Hty' := X0).
    eapply type_mkApps_inv in X0 as (? & ? & [] & ?); eauto.
    assert (Hty'' := Hty).
    eapply type_mkApps_inv in Hty'' as (? & ? & [] & ?); eauto.
    Require Import PCUIC.PCUICInversion.
    eapply inversion_Ind in t as (? & ? & ? & ? & ? & ?).
    eapply erases_mkApps_inv in Hty; eauto.
    destruct Hty as [ (? & ? & ? & ? & [] & ? & ? & ?) | (? & ? & ? & ? & ?)].
    + subst. exists tBox.
      split. 2:{ eapply eval_box_apps. now econstructor. }
      econstructor. eauto.
      eapply All2_app_inv in X as ([] & [] & ?). subst.
      rewrite <- mkApps_nested. 
      eapply Is_type_app. eauto.
      rewrite mkApps_nested. eauto.
      eapply Is_type_eval. eauto.
      eapply eval_app_ind. eauto. eauto.
      eauto.
    + subst. exists tBox.
      eapply IHeval in H2 as (? & ? & ?).
      inv H1.
      split. econstructor.
      eauto. eapply Is_type_app; eauto.
      eapply eval_box_apps; eauto. eauto.
  - inv He.
    + eexists. split; eauto. now econstructor.
    + eexists. split. 2: now econstructor.
      econstructor; eauto.
  - assert (Hty' := Hty).
    assert (Hty'' : Σ ;;; [] |- mkApps (tConstruct i k u) l' : T). {
      eapply subject_reduction. eauto. eapply Hty.
      eapply PCUICReduction.red_mkApps.
      eapply wcbeval_red; eauto.
      eapply All2_impl. exact X. intros.
      eapply wcbeval_red; eauto.
    }
    eapply erases_mkApps_inv in Hty; eauto.
    destruct Hty as [ (? & ? & ? & ? & [] & ? & ? & ?) | (? & ? & ? & ? & ?)].
    + subst. exists tBox.
      split. 2:{ eapply eval_box_apps. now econstructor. }
      eapply All2_app_inv in X as ( [] & [] & ?). subst.
      econstructor.

      rewrite <- mkApps_nested. 
      eapply Is_type_app. eauto.
      rewrite mkApps_nested. eauto.
      eapply Is_type_red. eauto.
      eapply PCUICReduction.red_mkApps.
      eapply wcbeval_red; eauto.
      eapply All2_impl. exact a. intros.
      eapply wcbeval_red; eauto. eauto. 
    + subst.
      eapply type_mkApps_inv in Hty' as (? & ? & [] & ?); eauto.
      eapply IHeval in H2 as (? & ? & ?); eauto.
      enough (exists l'', Forall2 (erases Σ []) l' l'' /\ Forall2 (Ee.eval Σ') x0 l'').
      * destruct H4 as [l''].
        inv H1.
        -- exists (E.mkApps (E.tConstruct i k) l''). split.
           eapply erases_mkApps; eauto.
           firstorder. econstructor; firstorder.
        -- exists tBox.
           split.
           econstructor. eauto. eapply Is_type_app; eauto.
           eapply eval_box_apps. eauto.
      * clear - t0 H0 H3. revert x1 x0 H3 t0. induction H0; intros.
        -- inv H3. eauto.
        -- inv H3. inv t0. eapply IHAll2 in H5 as (? & ? & ?).
           eapply r in H2 as (? & ? & ?); eauto. 
           eauto.
Qed.

(** ** The erasure function is in the erasure relation  *)

Lemma erases_extract Σ Γ t T :
  wf Σ ->
  Σ ;;; Γ |- t : T ->
  erases Σ Γ t (extract Σ Γ t).
Proof.
  Hint Constructors typing erases.
  Hint Resolve is_type_or_proof_spec.
  intros.
  pose proof (typing_wf_local X0).
  revert Σ X Γ X1 t T X0.  
  eapply typing_ind_env; intros.
  all: try now cbn; destruct ?; [ 
                               econstructor; eauto;
                               eapply is_type_or_proof_spec; eauto | eauto ].
  all: try now cbn; destruct ?;
                             econstructor; eauto;
    eapply is_type_or_proof_spec; eauto;
      match goal with [H : is_type_or_proof ?Σ ?Γ ?t = false |- _] =>
                      enough (is_type_or_proof Σ Γ t = true) by congruence;
                        eapply is_type_or_proof_spec; eauto;
                          eexists; split; eauto; now left
      end.
  - cbn.  destruct ?.
    econstructor; eauto.
    eapply is_type_or_proof_spec; eauto.
    enough (is_type_or_proof Σ Γ (tInd ind u) = true) by congruence.
    eapply is_type_or_proof_spec. eauto.
    eexists; split; eauto. left.
    assert (Σ;;; Γ |- tInd ind u : PCUICUnivSubst.subst_instance_constr u (PCUICAst.ind_type idecl)). econstructor; eauto.
    eapply isArity_subst_instance. eapply isArity_ind_type.
  - cbn. destruct ?.
    econstructor.  eapply is_type_or_proof_spec; eauto. econstructor; eauto.
    eapply All2_impl; eauto. firstorder. 
    econstructor; eauto.

    eapply elim_restriction_works. intros.
    assert (Is_Type_or_Proof Σ Γ (tCase (ind, npar) p c brs)).
    eapply Is_Type_or_Proof_Proof. eauto.
    eapply is_type_or_proof_spec in X5. congruence.
    econstructor; eauto.
    
    eapply All2_impl. eassumption. firstorder.
    
    eapply All2_map_right. cbn. eapply All_All2.
    2:{ intros. eapply X4. }
    eapply All2_All_left. eassumption. firstorder.
  - cbn.
    destruct ?.
    + econstructor. eapply is_type_or_proof_spec; eauto.
    + econstructor. eauto.
      eapply elim_restriction_works_proj. intros.
      eapply Is_Type_or_Proof_Proof in X2.
      eapply is_type_or_proof_spec in X2. rewrite E in X2. congruence.
      econstructor; eauto.
      eauto.      
  - cbn.
    assert (wf_local Σ (Γ ,,, PCUICLiftSubst.fix_context mfix)).
    {  destruct mfix. eauto. inv X0.
       eapply typing_wf_local. eapply X1. }
    destruct ?.
    + econstructor.
      eapply is_type_or_proof_spec. econstructor; eauto. 
      eapply All_impl. eauto. firstorder. eassumption. 
    + econstructor.
      unfold extract_mfix.
      eapply All2_map_right.
      eapply All_All2. eauto.
      firstorder.
  - cbn.
    assert (wf_local Σ (Γ ,,, PCUICLiftSubst.fix_context mfix)).
    {  destruct mfix. eauto. inv X0.
       eapply typing_wf_local. eapply X1. }
    destruct ?.
    + econstructor.
      eapply is_type_or_proof_spec. econstructor; eauto. 
      eapply All_impl. eauto. firstorder. eassumption. 
    + econstructor.
      unfold extract_mfix.
      eapply All2_map_right.
      eapply All_All2. eauto.
      firstorder.
  - eauto.
Qed.
