(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega Lia.
From MetaCoq.Template Require Import config utils monad_utils BasicAst AstUtils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICTyping PCUICWeakening PCUICSubstitution PCUICChecker PCUICRetyping PCUICMetaTheory PCUICWcbvEval PCUICSR PCUICValidity PCUICWeakeningEnv.
From MetaCoq.Extraction Require Import EAst ELiftSubst ETyping EWcbvEval Extract Prelim.
From Equations Require Import Equations.
Require Import String.
Local Open Scope list_scope.
Set Asymmetric Patterns.
Import MonadNotation.

Existing Instance config.default_checker_flags.
Module PA := PCUICAst.
Module P := PCUICWcbvEval.

Lemma All2_All_mix_left {A B} {P : A -> Type} {Q : A -> B -> Type}
      {l : list A} {l'}:
  All P l -> All2 Q l l' -> All2 (fun x y => (P x * Q x y)%type) l l'.
Proof.
  induction 2; simpl; intros; constructor.
  inv X; intuition auto.
  apply IHX0. inv X; intuition auto.
Qed.

(** ** Global Weakening  *)

Lemma Is_type_extends Σ Γ t :
  wf_local Σ Γ ->
  forall Σ', wf Σ' -> extends Σ Σ' -> Is_Type_or_Proof Σ Γ t -> Is_Type_or_Proof Σ' Γ t.
Proof.
  intros. destruct X2 as [T []].
  exists T. split. eapply weakening_env; [ | | eauto | | ]; eauto using wf_extends.
  destruct s; eauto. 
  destruct s as (u & ? & ?).
  right. exists u. split; eauto.
  eapply weakening_env; [ | | eauto | | ]; eauto using wf_extends.
Qed.

Lemma Is_proof_extends Σ Γ t :
  wf_local Σ Γ ->
  forall Σ', wf Σ' -> extends Σ Σ' -> Is_proof Σ Γ t -> Is_proof Σ' Γ t.
Proof.
  intros. destruct X2 as (? & ? & ? & ? & ?).
  exists x, x0. repeat split.
  eapply weakening_env; [ | | eauto | | ]; eauto using wf_extends.
  eapply weakening_env; [ | | eauto | | ]; eauto using wf_extends.
  eauto.
Qed.

Lemma erases_extends :
  env_prop (fun Σ Γ t T =>
              forall Σ', wf Σ' -> extends Σ Σ' -> forall t', erases Σ Γ t t' -> erases Σ' Γ t t').
Proof.
  apply typing_ind_env; intros; rename_all_hyps.
  all: match goal with [ H : erases _ _ ?a _ |- _ ] => tryif is_var a then idtac else inv H end.
  all: try now (econstructor; eauto).  
  all: try now (econstructor; eapply Is_type_extends; eauto).
  - econstructor. all:eauto.
    2:{ eauto. eapply All2_All_left in X3.
        2:{ intros ? ? []. exact e. }
        eapply All2_All_mix_left in H3; eauto.
        eapply All2_impl. exact H3.
        intros. destruct H4 as [? []].
        split; eauto. }


    Lemma Informative_extends:
      forall (Σ : PCUICAst.global_context) (ind : inductive)
        (mdecl : PCUICAst.mutual_inductive_body) (idecl : PCUICAst.one_inductive_body),
        
        PCUICTyping.declared_inductive (fst Σ) mdecl ind idecl ->
        forall (Σ' : PCUICAst.global_context) (u0 : universe_instance),
          wf Σ' ->
          extends Σ Σ' ->
          Informative Σ ind -> Informative Σ' ind.
    Proof.
      repeat intros ?.
      assert (extends Σ Σ'0). destruct X0, X2. subst. cbn. exists (x0 ++ x). cbn.
      now rewrite app_assoc.
      edestruct H0; eauto. destruct H3.

      eapply weakening_env_declared_inductive in H; eauto.
      destruct H, H1.
      unfold PCUICTyping.declared_minductive in *.

      eapply extends_lookup in H1; eauto. 
      rewrite H1 in H. inversion H. subst. clear H.
      rewrite H3 in H4. inversion H4. subst. clear H4.
      split. eauto. econstructor. eauto.
    Qed.
    eapply Informative_extends; eauto.
  - econstructor. destruct isdecl. 2:eauto.
    eapply Informative_extends; eauto.
  - econstructor.  
    eapply All2_All_mix_left in H; eauto.
    eapply All2_impl. exact H.
    intros ? ? [[[]] [? []]].
    split; eauto.
  - econstructor.
    eapply All2_All_mix_left in H; eauto.
    eapply All2_impl. exact H.
    intros ? ? [[] [? []]].
    split; eauto.
  - eauto.
Qed.

(** ** Weakening *)

Lemma Is_type_weakening:
  forall (Σ : PCUICAst.global_context) (Γ Γ' Γ'' : PCUICAst.context),
    wf_local Σ (Γ ,,, Γ') ->
    wf Σ ->
    wf_local Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') ->
    forall t : PCUICAst.term,
      Is_Type_or_Proof Σ (Γ ,,, Γ') t -> Is_Type_or_Proof Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') (PCUICLiftSubst.lift #|Γ''| #|Γ'| t).
Proof.
  intros. destruct X2 as (T & ? & ?).
  eexists. split. eapply weakening_typing; eauto.
  destruct s as [? | [u []]].
  - left. clear - i. generalize (#|Γ''|), (#|Γ'|). induction T; cbn in *; intros; try now inv i.
    + now eapply IHT2.
    + now eapply IHT3.
  - right. exists u. split; eauto.
    eapply weakening_typing in t1; eauto.
Qed.

Lemma erases_weakening' (Σ : PCUICAst.global_context) (Γ Γ' Γ'' : PCUICAst.context) (t T : PCUICAst.term) t' :
    wf Σ ->
    wf_local Σ (Γ ,,, Γ') ->
    wf_local Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') -> 
    Σ ;;; Γ ,,, Γ' |- t : T ->
    Σ ;;; Γ ,,, Γ' |- t ⇝ℇ t' ->
    Σ ;;; Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ' |- (PCUICLiftSubst.lift #|Γ''| #|Γ'| t) ⇝ℇ (lift #|Γ''| #|Γ'| t').
Proof.
  intros HΣ HΓΓ' HΓ'' * H He.
  generalize_eqs H. intros eqw. rewrite <- eqw in *.
  revert Γ Γ' Γ'' HΓ'' eqw t' He.
  revert Σ HΣ Γ0 HΓΓ' t T H .
  apply (typing_ind_env (fun Σ Γ0 t T =>  forall Γ Γ' Γ'',
    wf_local Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') ->
    Γ0 = Γ ,,, Γ' ->
    forall t',
    Σ;;; Γ0 |- t ⇝ℇ t' ->
    _));
    intros Σ wfΣ Γ0; !!intros; subst Γ0.
  all: match goal with [ H : erases _ _ ?a _ |- _ ] => tryif is_var a then idtac else inv H end.
  all: try now (cbn; econstructor; eauto).
  all: try now (econstructor; eapply Is_type_weakening; eauto).
  all:cbn.
  - destruct ?; econstructor. 
  - econstructor.
    unfold app_context, PCUICAst.snoc in *.    
    pose proof (h_forall_Γ0 (Γ) (PCUICAst.vass n t :: Γ') Γ'').
    rewrite lift_context_snoc0, <- plus_n_O in *.
    eapply H0; eauto. cbn. econstructor.
    eauto. cbn. exists s1. eapply weakening_typing with (T := tSort s1); eauto.
  - econstructor.
    + eapply h_forall_Γ0; eauto.
    + pose proof (h_forall_Γ1 Γ (PCUICAst.vdef n b b_ty :: Γ') Γ'').
      rewrite lift_context_snoc0, <- plus_n_O in *.
      eapply H1; eauto. cbn. econstructor.
      eauto. cbn. eapply weakening_typing; eauto.
  - econstructor.
    + eauto.
    + eapply h_forall_Γ0; eauto.
    + eapply All2_map.
      eapply All2_All_left in X3.
      2:{ intros. destruct X1. exact e. }
      eapply All2_impl. eapply All2_All_mix_left.
      eassumption. eassumption. intros.
      destruct H4. destruct p0.
      cbn. destruct x, y; cbn in *; subst.
      split; eauto.
  - econstructor.
    eapply All2_map.
    eapply All2_impl. eapply All2_All_mix_left.
    eassumption. eassumption. intros.
    destruct X1 as [[[]] [? []]].
    destruct x, y; cbn in *; subst.
    repeat split. unfold app_context in *.
    eapply (e0 Γ (types ++ Γ') Γ'') in e3.
    3: now rewrite app_assoc. 
    2:rewrite lift_context_app.
    2:{ admit. (* wf_local *) }
    rewrite app_length in *.
    subst types. rewrite fix_context_length in *.
    rewrite (All2_length _ _ H) in *.
    Lemma erases_ctx_ext Σ Γ Γ' t t' :
      erases Σ Γ t t' -> Γ = Γ' -> erases Σ Γ' t t'.
    Proof.
      intros. now subst.
    Qed.
    eapply erases_ctx_ext. eapply e3.
    rewrite lift_context_app. unfold app_context.
    rewrite !app_assoc. repeat f_equal.
    rewrite <- lift_fix_context.
    rewrite <- plus_n_O.
    now rewrite (All2_length _ _ H).
  - econstructor.
    eapply All2_map.
    eapply All2_impl. eapply All2_All_mix_left.
    eassumption. eassumption. intros.
    destruct X1 as [[] [? []]].
    destruct x, y; cbn in *; subst.
    repeat split. unfold app_context in *.
    eapply (e Γ (types ++ Γ') Γ'') in e2.
    3: now rewrite app_assoc. 
    2:rewrite lift_context_app.
    2: admit. (* wf_local *)
    rewrite app_length in *.
    subst types. rewrite fix_context_length in *.
    rewrite (All2_length _ _ H) in *.
    eapply erases_ctx_ext. eapply e2.
    rewrite lift_context_app. unfold app_context.
    rewrite !app_assoc. repeat f_equal.
    rewrite <- lift_fix_context.
    rewrite <- plus_n_O.
    now rewrite (All2_length _ _ H).
Admitted.

Lemma erases_weakening (Σ : PCUICAst.global_context) (Γ Γ' : PCUICAst.context) (t T : PCUICAst.term) t' :
  wf Σ ->
  wf_local Σ (Γ ,,, Γ') ->
  Σ ;;; Γ |- t : T ->
  Σ ;;; Γ |- t ⇝ℇ t' ->
  Σ ;;; Γ ,,, Γ' |- (PCUICLiftSubst.lift #|Γ'| 0 t) ⇝ℇ (lift #|Γ'| 0 t').
Proof.
  intros.
  pose proof (typing_wf_local X1).
  eapply (erases_weakening' Σ Γ [] Γ'); cbn; eauto.
Qed.  

Lemma All2_nth_error_None {A B} {P : A -> B -> Type} {l l'} n :
  All2 P l l' ->
  nth_error l n = None ->
  nth_error l' n = None.
Proof.
  intros Hall. revert n.
  induction Hall; destruct n; simpl; try congruence. auto.
Qed.

Lemma All2_length {A B} {P : A -> B -> Type} l l' : All2 P l l' -> #|l| = #|l'|.
Proof. induction 1; simpl; auto. Qed.

Lemma is_type_subst Σ Γ Γ' Δ a s :
  wf Σ -> subslet Σ Γ s Γ' ->
  (* Σ ;;; Γ ,,, Γ' ,,, Δ |- a : T -> *)
  wf_local Σ (Γ ,,, subst_context s 0 Δ) ->
  Is_Type_or_Proof Σ (Γ ,,, Γ' ,,, Δ) a ->
  Is_Type_or_Proof Σ (Γ ,,, subst_context s 0 Δ) (PCUICLiftSubst.subst s #|Δ| a).
Proof.
  intros ? ? ? (T & HT & H).
  exists (PCUICLiftSubst.subst s #|Δ| T). split.
  eapply substitution; eauto.
  destruct H as [ | (u & ? & ?) ].
  - left. generalize (#|Δ|). intros n.
    induction T in n, i |- *; (try now inv i); cbn in *; eauto.
  - right. exists u. split; eauto.
    pose proof (substitution Σ Γ Γ' s Δ).
    eapply X2 in t; eauto.
Qed.

Lemma erases_subst Σ Γ Γ' Δ t s t' s' T :
  wf Σ ->
  subslet Σ Γ s Γ' ->
  wf_local Σ (Γ ,,, subst_context s 0 Δ) ->
  Σ ;;; Γ ,,, Γ'  ,,, Δ |- t : T ->
  Σ ;;; Γ ,,, Γ'  ,,, Δ |- t ⇝ℇ t' ->                            
  All2 (erases Σ Γ) s s' ->
  Σ ;;; (Γ ,,, subst_context s 0 Δ) |- (PCUICLiftSubst.subst s #|Δ| t) ⇝ℇ subst s' #|Δ| t'.
Proof.
  intros HΣ HΔ Hs Ht He.
  pose proof (typing_wf_local Ht).
  generalize_eqs Ht. intros eqw. rewrite <- eqw in X.
  revert Γ Γ' Δ t' s Hs HΔ He eqw.
  revert Σ HΣ Γ0 X t T Ht.
  eapply (typing_ind_env (fun Σ Γ0 t T =>
                            forall (Γ Γ' : PCUICAst.context) Δ t' (s : list PCUICAst.term),
                              wf_local Σ (Γ ,,, subst_context s 0 Δ) ->
                              subslet Σ Γ s Γ' ->
                              Σ;;; Γ ,,, Γ' ,,, Δ |- t ⇝ℇ t' ->
                              Γ0 = Γ ,,, Γ' ,,, Δ ->
                              All2 (erases Σ Γ) s s' ->
                              Σ;;; Γ ,,, subst_context s 0 Δ |- PCUICLiftSubst.subst s #|Δ| t ⇝ℇ subst s' #|Δ| t'
         ));
    intros Σ wfΣ Γ0 wfΓ0; intros; simpl in * |-; subst Γ0.
  - inv H0.
    + cbn. destruct ?. destruct ?.
      * eapply All2_nth_error_Some in H2; eauto.
        destruct H2 as (? & ? & ?).
        rewrite e.
        erewrite <- subst_context_length.
        eapply erases_weakening; eauto.
        (* subslet and typing *) admit.
      * erewrite All2_length; eauto.                
        eapply All2_nth_error_None in H2; eauto.
        rewrite H2. econstructor.
      * econstructor.
    + econstructor.
      eapply is_type_subst; eauto.
  - inv H. econstructor.
    eapply is_type_subst; eauto.
  - inv H1. econstructor.
    eapply is_type_subst; eauto.
  - inv H1.
    + cbn. econstructor.
      specialize (H0 Γ Γ' (PCUICAst.vass n t :: Δ) t'0 s).
      (* unfold app_context, snoc in *. *)
      rewrite subst_context_snoc0 in *.
      eapply H0; eauto.
      cbn. econstructor. eauto.
      cbn. exists s1. eapply substitution with (T := tSort s1); eauto.
    + econstructor.
      eapply is_type_subst; eauto.
  - inv H2.
    + cbn. econstructor.
      eauto.
      specialize (H1 Γ Γ' (PCUICAst.vdef n b b_ty :: Δ) t2' s).
      rewrite subst_context_snoc0 in *.
      eapply H1; eauto.
      cbn. econstructor. eauto.
      cbn. eapply substitution; eauto.
    + econstructor.
      eapply is_type_subst; eauto.
  - inv H1.
    + cbn. econstructor.
      eapply H; eauto.
      eapply H0; eauto.
    + econstructor.
      eapply is_type_subst; eauto.
  - inv H1.
    + cbn. econstructor.
    + econstructor.
      eapply is_type_subst; eauto.
  - inv H0. econstructor.
    eapply is_type_subst; eauto.
  - inv H0.
    + cbn. econstructor. 
    + econstructor.
      eapply is_type_subst; eauto.
  - depelim H5. 
    + cbn. econstructor.
      * eauto.
      * eapply H4; eauto.
      * eapply All2_map.
        eapply All2_impl_In; eauto.
        intros. destruct H11, x, y. cbn in *. subst. split; eauto.
        eapply All2_All_left in X3.
        2:{ intros ? ? []. exact e0. }

        eapply In_nth_error in H9 as [].
        eapply nth_error_all in X3; eauto.
        eapply X3; eauto.
    (* + cbn. econstructor. *)
    (*   eapply H4 in H5; eauto. *)
    (*   econstructor. *)
    (* + cbn.  *)

    (*   Lemma subst_mkppBox s m n x : *)
    (*     subst s m (mkAppBox x n) = mkAppBox (subst s m x) n. *)
    (*   Proof. *)
    (*     revert x; induction n; cbn; intros; try congruence. *)
    (*     now rewrite IHn. *)
    (*   Qed. *)
    (*   rewrite subst_mkppBox. *)
    (*   econstructor. *)
    (*   eapply H4 in H5_; eauto. *)
    (*   inv X3. destruct X6. *)
    (*   eapply e; eauto. *)
    + econstructor.
      eapply is_type_subst; eauto.      
  - inv H1.
    + cbn. econstructor.
      * eauto.
      * eauto.
    + econstructor.
      eapply is_type_subst; eauto.
  - inv H0.
    + cbn. econstructor.
      eapply All2_map.
      eapply All2_impl_In.
      eassumption.
      intros. destruct H4 as (? & ? & ?).
      repeat split; eauto.
      eapply In_nth_error in H0 as [].
      eapply nth_error_all in X0; eauto.
      destruct X0.
      specialize (e2 Γ Γ' (Δ ,,, PCUICLiftSubst.fix_context mfix)).
      rewrite app_context_assoc in *.
      eapply e2 in e1; eauto.

      Lemma erases_eq Σ Γ Γ' t t' s s' :
        erases Σ Γ t t' -> 
        Γ = Γ' ->
        t = s ->
        t' = s' ->      
        erases Σ Γ' s s'.
      Proof.
        now subst.
      Qed.
      eapply erases_eq; eauto.
      * rewrite subst_context_app.
        rewrite <- plus_n_O.
        rewrite app_context_assoc. f_equal.
        now rewrite subst_fix_context.
      * cbn. now rewrite app_context_length, fix_context_length.
      * cbn. now erewrite app_context_length, fix_context_length, All2_length.
      * admit. (* wf_local *)
    + econstructor.
      eapply is_type_subst; eauto.
  -  inv H0.
    + cbn. econstructor.
      eapply All2_map.
      eapply All2_impl_In.
      eassumption.
      intros. destruct H4 as (? & ? & ?).
      repeat split; eauto.
      eapply In_nth_error in H0 as [].
      eapply nth_error_all in X0; eauto.
      destruct X0.
      specialize (e2 Γ Γ' (Δ ,,, PCUICLiftSubst.fix_context mfix)).
      rewrite app_context_assoc in *.
      eapply e2 in e1; eauto.

      eapply erases_eq; eauto.
      * rewrite subst_context_app.
        rewrite <- plus_n_O.
        rewrite app_context_assoc. f_equal.
        now rewrite subst_fix_context.
      * cbn. now rewrite app_context_length, fix_context_length.
      * cbn. now erewrite app_context_length, fix_context_length, All2_length.
      * admit. (* wf_local *)
    + econstructor.
      eapply is_type_subst; eauto.
  - eapply H; eauto.    
Admitted.  

(* Lemma extract_weakening (Σ : PCUICAst.global_context) (Γ Γ' : PCUICAst.context) (t T : PCUICAst.term) : *)
(*     wf Σ -> *)
(*     wf_local Σ (Γ ,,, Γ') -> *)
(*     Σ;;; Γ |- t : T -> *)
(*      Σ ;;; Γ |- t ⇝ℇ t' -> *)
(*     Σ ;;; Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ' |- (PCUICLiftSubst.lift #|Γ''| #|Γ'| t) ⇝ℇ (lift #|Γ''| #|Γ'| t'). *)
                 
(*     extract Σ (Γ ,,, Γ') (PCUICLiftSubst.lift #|Γ'| 0 t) = lift #|Γ'| 0 (extract Σ Γ t). *)
(* Proof. *)
(* Admitted. *)

(* (** ** Substitution *) *)
  
(* Lemma is_arity_subst Σ Γ Γ' Δ a s : *)
(*   wf Σ -> subslet Σ Γ s Γ' -> *)
(*   (* Σ ;;; Γ ,,, Γ' ,,, Δ |- a : T -> *) *)
(*   wf_local Σ (Γ ,,, subst_context s 0 Δ) -> *)
(*   is_arity Σ (Γ ,,, Γ' ,,, Δ) _ a = is_arity Σ (Γ ,,, subst_context s 0 Δ) _ (PCUICLiftSubst.subst s #|Δ| a).  *)
(* Proof. *)
(* Admitted. *)

(* (* this is probably too strict, a might also be an algebraic universe *) *)
(* Lemma type_of_subst Σ Γ Γ' Δ a T s T' : *)
(*   wf Σ -> subslet Σ Γ s Γ' -> *)
(*   Σ ;;; Γ ,,, Γ' ,,, Δ |- a : T -> *)
(*   wf_local Σ (Γ ,,, subst_context s 0 Δ) -> *)
(*   type_of Σ (Γ ,,, Γ' ,,, Δ) a = Checked T' -> *)
(*   type_of Σ (Γ ,,, subst_context s 0 Δ) (PCUICLiftSubst.subst s #|Δ| a) = Checked (PCUICLiftSubst.subst s #|Δ| T'). *)
(* Proof. *)
(* Admitted. *)

(* Lemma reduce_to_sort_subst: *)
(*   forall (H : Fuel) (Σ : PCUICAst.global_context) (Γ Γ' Δ : PCUICAst.context) *)
(*     (s : list PCUICAst.term), *)
(*     wf Σ -> *)
(*     subslet Σ Γ s Γ' -> *)
(*     wf_local Σ (Γ ,,, subst_context s 0 Δ) -> *)
(*     forall a0 : PCUICAst.term, *)
(*       reduce_to_sort (fst Σ) (Γ ,,, subst_context s 0 Δ) (PCUICLiftSubst.subst s #|Δ| a0) = *)
(*       reduce_to_sort (fst Σ) (Γ ,,, Γ' ,,, Δ) a0. *)
(* Proof. *)
(*   intros H Σ Γ Γ' Δ s X X0 X2 a0. *)
(* Admitted. *)

(* Lemma type_of_as_sort_subst Σ Γ Γ' Δ a s T : *)
(*   wf Σ -> subslet Σ Γ s Γ' -> *)
(*   Σ ;;; Γ ,,, Γ' ,,, Δ |- a : T -> *)
(*   wf_local Σ (Γ ,,, subst_context s 0 Δ) -> *)
(*   type_of_as_sort Σ (type_of Σ) (Γ ,,, subst_context s 0 Δ) *)
(*       (PCUICLiftSubst.subst s #|Δ| a) = type_of_as_sort Σ (type_of Σ) (Γ ,,, Γ' ,,, Δ) a. *)
(* Proof. *)
(*   intros. unfold type_of_as_sort. *)
(*   destruct type_of eqn:E at 2. *)
(*   eapply type_of_subst in E; eauto. *)
(*   - rewrite E. simpl. eapply reduce_to_sort_subst; eauto. *)
(*   - edestruct type_of_complete; eauto. congruence. *)
(* Qed. *)

(* Inductive subslet Σ (Γ : PCUICAst.context) : list PCUICAst.term -> PCUICAst.context -> Type := *)
(* | emptyslet : subslet Σ Γ [] [] *)
(* | cons_let_ass Δ s na t T : subslet Σ Γ s Δ -> *)
(*               Σ ;;; Γ |- t : PCUICLiftSubst.subst0 s T -> *)
(*               is_type_or_proof Σ Γ t = false -> *)
(*               subslet Σ Γ (t :: s) (Δ ,, PCUICAst.vass na T) *)
(* | cons_let_def Δ s na t T : *)
(*     subslet Σ Γ s Δ -> *)
(*     Σ ;;; Γ |- PCUICLiftSubst.subst0 s t : PCUICLiftSubst.subst0 s T -> *)
(*     is_type_or_proof Σ Γ (PCUICLiftSubst.subst0 s t) = false -> *)
(*     subslet Σ Γ (PCUICLiftSubst.subst0 s t :: s) (Δ ,, PCUICAst.vdef na t T). *)

(* Lemma subslet_implies Σ Γ s Γ' : *)
(*   subslet Σ Γ s Γ' -> PCUICSubstitution.subslet Σ Γ s Γ'. *)
(* Proof. *)
(*   induction 1; try econstructor; eauto. *)
(* Qed. *)
(* Hint Resolve subslet_implies. *)

(* Lemma subslet_nth_error  Σ Γ s Δ decl n t : *)
(*   subslet Σ Γ s Δ -> *)
(*   nth_error Δ n = Some decl -> *)
(*   nth_error s n = Some t -> *)
(*   match PCUICAst.decl_body decl with *)
(*   | Some t' => *)
(*     let b := PCUICLiftSubst.subst (skipn (S n) s) 0 t' in *)
(*     let ty := PCUICLiftSubst.subst (skipn (S n) s) 0 (PCUICAst.decl_type decl) in *)
(*     is_type_or_proof Σ Γ t = false  × t = b × Σ;;; Γ |- b : ty *)
(*   | None => *)
(*     let ty := PCUICLiftSubst.subst (skipn (S n) s) 0 (PCUICAst.decl_type decl) in *)
(*     is_type_or_proof Σ Γ t = false × Σ;;; Γ |- t : ty *)
(*   end. *)
(* Proof. *)
(*   induction 1 in n |- *; simpl; auto; destruct n; simpl; try congruence. *)
(*   - intros [= <-]. intros [= ->]. *)
(*     simpl. split. eassumption. exact t1. *)
(*   - intros. destruct decl as [na' [b|] ty]; cbn in *. *)
(*     specialize (IHX _ H H0). intuition auto. *)
(*     now apply IHX. *)
(*   - intros [= <-]. intros [= <-]. *)
(*     simpl. split; auto. *)
(*   - apply IHX. *)
(* Qed. *)

(* Lemma bool_equiv b1 b2 T1 T2 :  *)
(* (b1 = true <~> T1) -> (b2 = true <~> T2) -> T1 <~> T2 -> b1 = b2. *)
(* Proof. *)
(* Admitted. *)

(* Lemma is_type_subst Σ Γ Γ' Δ a T s : *)
(*   wf Σ -> subslet Σ Γ s Γ' -> *)
(*   Σ ;;; Γ ,,, Γ' ,,, Δ |- a : T -> *)
(*   wf_local Σ (Γ ,,, subst_context s 0 Δ) -> *)
(*   is_type_or_proof Σ (Γ ,,, Γ' ,,, Δ) a = *)
(*   is_type_or_proof Σ (Γ ,,, subst_context s 0 Δ) (PCUICLiftSubst.subst s #|Δ| a). *)
(* Proof. *)
(*   intros. *)
(*   eapply bool_equiv. *)
(*   - eapply is_type_or_proof_spec. eauto. *)
(*   - eapply is_type_or_proof_spec. eapply substitution; eauto. *)
(*   - split. *)
(*     + intros [ | (u & ? & ?) ]. *)
(*       * left. generalize (#|Δ|). intros n. *)
(*         induction T in n, i |- *; (try now inv i); cbn in *; eauto. *)
(*       * right. exists u. split; eauto. *)
(*         pose proof (substitution Σ Γ Γ' s Δ). *)
(*         eapply X3 in t; eauto. *)
(*     + intros [ | (u & ? & ?) ]. *)
(*       * left. induction T in s, Δ, i |- *; (try now inv i); cbn in *; eauto. *)
(*         -- destruct ?. destruct ?. all:eauto. *)
(*            Lemma isArity_lift n k t : *)
(*              isArity *)
(*                (PCUICLiftSubst.lift n k t) <-> isArity t. *)
(*            Proof. *)
(*              revert n k; induction t; cbn; intros; try tauto; eauto. *)
(*              destruct ?; cbn; tauto. *)
(*            Qed. *)
(*            rewrite isArity_lift in i. *)
(*            (* the type of an arity is an arity, but that's contradictory with subslet *) admit. *)
(*         -- eapply IHT2 with (Δ := _ :: Δ). cbn. eapply i. *)
(*         -- eapply IHT3 with (Δ := _ :: Δ). cbn. eapply i. *)
(*       * right. exists u. split; eauto. *)
(* Qed. *)


  (* ============================ *)
  (* forall Σ : PCUICAst.global_context, *)
  (* wf Σ -> *)
  (* forall Γ0 : PCUICAst.context, *)
  (* wf_local Σ Γ0 -> *)
  (* forall a T : PCUICAst.term, *)
  (* Σ;;; Γ0 |- a : T -> *)
  (* forall (Γ Γ' Δ : PCUICAst.context) (s : list PCUICAst.term), *)
  (* wf_local Σ (Γ ,,, subst_context s 0 Δ) -> *)
  (* subslet Σ Γ s Γ' -> *)
  (* Γ0 = Γ ,,, Γ' ,,, Δ -> *)
  (* extract Σ (Γ ,,, subst_context s 0 Δ) (PCUICLiftSubst.subst s #|Δ| a) = *)
  (* subst (map (extract Σ Γ) s) #|Δ| (extract Σ (Γ ,,, Γ' ,,, Δ) a) *)



(* Lemma extract_subst Σ Γ Γ' Δ a s T : *)
(*   wf Σ -> *)
(*   subslet Σ Γ s Γ' -> *)
(*   wf_local Σ (Γ ,,, subst_context s 0 Δ) -> *)
(*   Σ ;;; Γ ,,, Γ'  ,,, Δ |- a : T -> *)
(*   (* is_type_or_proof Σ (Γ ,,, Γ' ,,, Δ) a = *) *)
(*   (* is_type_or_proof Σ (Γ ,,, subst_context s 0 Δ) (PCUICLiftSubst.subst s #|Δ| a) -> *) *)
(*   extract Σ (Γ ,,, subst_context s 0 Δ) (PCUICLiftSubst.subst s #|Δ| a) = subst  (map (extract Σ Γ) s) #|Δ| (extract Σ (Γ,,,Γ',,,Δ) a). *)
(* Proof. *)
(*   intros HΣ HΔ Hs Ha. *)
(*   pose proof (typing_wf_local Ha). *)
(*   generalize_eqs Ha. intros eqw. rewrite <- eqw in X. *)
(*   revert Γ Γ' Δ s Hs HΔ eqw. *)
(*   revert Σ HΣ Γ0 X a T Ha. *)
(*   eapply (typing_ind_env (fun Σ Γ0 a T => *)
(*                             forall (Γ Γ' : PCUICAst.context) Δ (s : list PCUICAst.term), *)
(*                               wf_local Σ (Γ ,,, subst_context s 0 Δ) -> *)
(*                               subslet Σ Γ s Γ' -> *)
(*                                 Γ0 = Γ ,,, Γ' ,,, Δ -> *)
(*                                 extract Σ (Γ ,,, subst_context s 0 Δ) (PCUICLiftSubst.subst s #|Δ| a) = *)
(*                                 subst (map (extract Σ Γ) s) #|Δ| (extract Σ (Γ ,,, Γ' ,,, Δ) a) *)
(* )); *)
(*   intros Σ wfΣ Γ0 wfΓ0; intros; simpl in * |-; subst Γ0. *)
(*   - cbn. destruct (_ <=? _) eqn:E1. *)
(*     * destruct (nth_error s (n- #|_|)) eqn:E2. *)
(*       -- destruct ?.  *)
(*          ++ cbn. eapply is_type_subst in E. *)
(*             rewrite is_type_extract. reflexivity. *)
(*             cbn in E. rewrite E1, E2 in E. eassumption. eauto. eauto. *)
(*             econstructor; eauto. *)
(*             eauto. *)
(*          ++ cbn. rewrite E1. *)
(*             rewrite nth_error_map. rewrite E2. cbn. *)
(*             erewrite <- subst_context_length. *)
(*             erewrite extract_weakening; eauto. admit. *)
(*       -- cbn. symmetry. destruct ?. *)
(*          eapply is_type_subst in E. cbn in E. *)
(*          rewrite E1, E2 in E. rewrite E. reflexivity. *)
(*          all:eauto. *)
(*          econstructor; eauto. *)

(*          destruct ?. *)
(*          ++ cbn. exfalso.             *)
            
(*          ++ cbn. rewrite E1. rewrite nth_error_map, E2. cbn. *)
(*             now rewrite map_length. *)
         
         
(*          destruct ?. reflexivity.  *)
(*          destruct ?. *)
(*          ++ reflexivity. *)
(*          ++ cbn. rewrite E1. rewrite nth_error_map, E2. cbn. *)
(*             now rewrite map_length. *)
(*     * cbn. rewrite H0. *)
(*       destruct ?. reflexivity. *)
(*       cbn. rewrite E1. reflexivity. *)
(*   - cbn. rewrite <- H. *)
(*     destruct ?; reflexivity. *)
(*   - cbn. rewrite <- H1. *)
(*     destruct ?; reflexivity. *)
(*   - cbn. rewrite <- H1. *)
(*     destruct ?. *)
(*     + reflexivity. *)
(*     + cbn. f_equal. *)
(*       specialize (H0 Γ Γ' (PCUICAst.vass n t :: Δ) s). *)
(*       cbn [app length] in H0. *)
(*       rewrite <- H0; eauto. *)
(*       f_equal. f_equal. *)
(*       now rewrite subst_context_snoc0. *)
(*       admit. (* some wf_local stuff *) *)
(*       rewrite subst_context_snoc0. *)
(*       Lemma is_type_or_proof_lambda  Σ Γ na t b : *)
(*         Extract.is_type_or_proof Σ Γ (PCUICAst.tLambda na t b) = *)
(*         Extract.is_type_or_proof Σ (Γ ,, PCUICAst.vass na t) b. *)
(*       Admitted. *)
(*       rewrite is_type_or_proof_lambda in *. *)
(*       now rewrite E, <- H1. *)
(*   - cbn. rewrite <- H2. *)
(*     destruct ?. *)
(*     + reflexivity. *)
(*     + cbn. f_equal. *)
(*       * eapply H0; eauto. *)
(*         admit. *)
(*       * specialize (H1 Γ Γ' (PCUICAst.vdef n b b_ty :: Δ) s). *)
(*         unfold app_context in *. *)
(*         cbn [List.length List.app] in H1. rewrite <- H1; eauto. *)
(*         f_equal. rewrite subst_context_snoc0. reflexivity. *)
(*         admit. (* wf_local stuff *) *)
        
(*         Lemma is_type_or_proof_letin Σ Γ na t b0 b1 : *)
(*           is_type_or_proof Σ Γ (PCUICAst.tLetIn na b0 t b1) = *)
(*           Extract.is_type_or_proof Σ (Γ ,, PCUICAst.vdef na b0 t) b1. *)
(*         Admitted. *)
(*         rewrite is_type_or_proof_letin in *. *)
(*         rewrite E, H2. *)
(*         f_equal. now rewrite !subst_context_snoc0. *)
(*   - cbn. rewrite <- H1. *)
(*     destruct ?; cbn; try reflexivity. *)

(*     Lemma is_type_App_false  Σ Γ a l T : *)
(*       Σ ;;; Γ |- PCUICAst.mkApps a l : T ->  *)
(*                                       is_type_or_proof Σ Γ (PCUICAst.mkApps a l) = false -> *)
(*                                       is_type_or_proof Σ Γ a = false. *)
(*     Proof. *)
(*     Admitted. *)

(*     f_equal. *)
(*     + eapply is_type_App_false with (l := [_]) in E. symmetry in H1. *)
(*       eapply is_type_App_false with (l := [_]) in H1. *)
(*       eapply H; eauto. *)
(*       econstructor; eauto. *)
(*       eapply substitution_alt in X0; eauto. *)
(*       eapply substitution_alt in X1; eauto. *)
(*       econstructor; eauto. *)
(*     + eapply H0; eauto.       *)
(*       Lemma is_type_App_false  Σ Γ a l T : *)
(*         Σ ;;; Γ |- PCUICAst.mkApps a l : T ->  *)
(*                                         is_type_or_proof Σ Γ (PCUICAst.mkApps a l) = false -> *)
(*                                         is_type_or_proof Σ Γ a = false. *)
(*       Proof. *)
(*       Admitted. *)
(*       eapply is_type_App_false with (l := [_]) in E. symmetry in H1. *)
(*       eapply is_type_App_false with (l := [_]) in H1. *)
(*       now rewrite H1, E. *)
(*       econstructor; eauto. *)
(*       eapply substitution_alt in X0; eauto. *)
(*       eapply substitution_alt in X1; eauto. *)
(*       econstructor; eauto. *)
(*     + eapply H0; eauto. *)
      
      
(* Admitted. *)

(* Lemma extract_subst_alt Σ Γ Γ' Δ a s T : *)
(*   wf Σ -> *)
(*   subslet Σ Γ s Γ' -> *)
(*   Σ ;;; Γ ,,, Γ'  ,,, Δ |- a : T -> *)
(*   is_type_or_proof Σ (Γ ,,, Γ' ,,, Δ) a = *)
(*   is_type_or_proof Σ (Γ ,,, subst_context s 0 Δ) (PCUICLiftSubst.subst s #|Δ| a) -> *)
(*   extract Σ (Γ ,,, subst_context s 0 Δ) (PCUICLiftSubst.subst s #|Δ| a) = subst  (map (extract Σ Γ) s) #|Δ| (extract Σ (Γ,,,Γ',,,Δ) a). *)
(* Proof. *)
(*   intros.  *)
(*   eapply extract_subst; eauto. clear H. (* clear H0 H1 a' H s'. *) *)
(*   eapply All_local_env_app_inv. *)
(*   apply typing_wf_local in X1; eauto. *)
(*   apply All_local_env_app in X1 as [X1 X2]. *)
(*   apply All_local_env_app in X1. intuition. *)
(*   induction X2; simpl; rewrite ?subst_context_snoc0; econstructor; eauto. *)
(*   destruct t0 as [u tu]. *)
(*   eapply substitution in tu; simpl in *; eauto. *)
(*   eapply All_local_env_app_inv; intuition. *)
(*   eapply substitution in t0; simpl in *; eauto. *)
(*   eapply All_local_env_app_inv; intuition. *)
(* Qed. *)

(* Lemma extract_subst1  *)
(*       (Σ : PCUICAst.global_context) (na : name) (t b a' : PCUICAst.term) T : *)
(*   wf Σ -> Σ ;;; [] ,, PCUICAst.vass na t |- b : T -> Σ ;;; [] |- a' : t -> *)
(*   is_type_or_proof Σ [] (PCUICLiftSubst.subst1 a' 0 b) = is_type_or_proof Σ  [PCUICAst.vass na t] b -> *)
(*   extract Σ [] (PCUICLiftSubst.subst1 a' 0 b) = (extract Σ [PCUICAst.vass na t] b) {0 := extract Σ [] a'}. *)
(* Proof. *)
(*   intros HΣ Ht Hu He. *)
(*   assert (wfΓ : wf_local Σ []). *)
(*   apply typing_wf_local in Hu; eauto. intros. *)
(*   pose proof (extract_subst_alt Σ [] [PCUICAst.vass na t] [] b [a'] T) as thm. *)
(*   forward thm. eauto. *)
(*   forward thm. econstructor. econstructor. rewrite PCUICLiftSubst.subst_empty; auto. *)
(*   now apply (thm Ht). *)
(* Qed. *)

(* Lemma extract_subst1_vdef *)
(*       (Σ : PCUICAst.global_context) (na : name) (t b a' : PCUICAst.term) T : *)
(*   wf Σ -> Σ ;;; [] ,, PCUICAst.vdef na a' t |- b : T -> Σ ;;; [] |- a' : t -> *)
(* is_type_or_proof Σ [] (PCUICLiftSubst.subst1 a' 0 b) = is_type_or_proof Σ  [PCUICAst.vdef na a' t] b -> *)
(*       extract Σ [] (PCUICLiftSubst.subst1 a' 0 b) = (extract Σ [PCUICAst.vdef na a' t] b) {0 := extract Σ [] a'}. *)
(* Proof. *)
(*   intros HΣ Ht. *)
(*   assert ((wf_local Σ []) * (Σ ;;; [] |- a' : t)%type) as [wfΓ tyu]. *)
(*   apply typing_wf_local in Ht; eauto with wf.  *)
(*   now depelim Ht; simpl in *; unfold PCUICAst.vdef, PCUICAst.vass in H; noconf H.  *)
(*   intros. *)
(*   epose proof (extract_subst_alt Σ [] [PCUICAst.vdef na a' t] [] b _ T HΣ) as thm. *)
(*   forward thm. econstructor. econstructor. rewrite !PCUICLiftSubst.subst_empty in *; auto. *)
(*   rewrite !PCUICLiftSubst.subst_empty in *. *)
(*   cbn in *.  *)
(*   eapply thm; eauto. *)
(* Qed. *)
