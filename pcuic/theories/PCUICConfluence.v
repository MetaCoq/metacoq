(* Distributed under the terms of the MIT license.   *)
Require Import ssreflect ssrbool.
Require Import LibHypsNaming.
From Equations Require Import Equations.
From Coq Require Import Bool String List Program BinPos Compare_dec Omega Utf8 String Lia.
From Template Require Import config utils univ BasicAst.
From PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICReduction PCUICWeakening PCUICSubstitution.

(* Type-valued relations. *)
Require Import CRelationClasses.
Require Import Equations.Type.Relation Equations.Type.Relation_Properties.

Set Asymmetric Patterns.

Notation "'∃' x .. y , P" := (sigT (fun x => .. (sigT (fun y => P%type)) ..))
  (at level 200, x binder, y binder, right associativity,
  format "'[  ' '[  ' ∃  x  ..  y ']' ,  '/' P ']'") : type_scope.

Existing Instance config.default_checker_flags.

Derive NoConfusion for term.
Derive Subterm for term.

Section ListSize.
  Context {A} (f : A -> nat).

  Equations list_size (l : list A) : nat :=
  list_size nil := 0;
  list_size (cons a v) := S (f a + list_size v).
End ListSize.

Fixpoint size t : nat :=
  match t with
  | tRel i => 1
  | tEvar ev args => S (list_size size args)
  | tLambda na T M => S (size T + size M)
  | tApp u v => S (size u + size v)
  | tProd na A B => S (size A + size B)
  | tLetIn na b t b' => S (size b + size t + size b')
  | tCase ind p c brs => S (size p + size c + list_size (fun x => size (snd x)) brs)
  | tProj p c => S (size c)
  | tFix mfix idx => S (list_size (fun x => size (dtype x) + size (dbody x)) mfix)
  | tCoFix mfix idx => S (list_size (fun x => size (dtype x) + size (dbody x)) mfix)
  | x => 1
  end.

Lemma simpl_subst' :
  forall N M n p k, k = List.length N -> p <= n -> subst N p (lift0 (k + n) M) = lift0 n M.
Proof. intros. subst k. rewrite simpl_subst_rec; auto. now rewrite Nat.add_0_r. lia. Qed.

Lemma mkApps_size x l : size (mkApps x l) = size x + list_size size l.
Proof.
  induction l in x |- *; simpl; simp list_size. lia.
  rewrite IHl. simpl. lia.
Qed.

Lemma mkApps_eq_head {x l} : mkApps x l = x -> l = [].
Proof.
  assert (WF := _ : WellFounded (MR lt size)).
  induction l. simpl. constructor.
  apply apply_noCycle_right. simpl. red. rewrite mkApps_size. simpl. lia.
Qed.

Lemma mkApps_eq_inv {x y l} : x = mkApps y l -> size y <= size x.
Proof.
  assert (WF := _ : WellFounded (MR lt size)).
  induction l in x, y |- *. simpl. intros -> ; constructor.
  simpl. intros. specialize (IHl _ _ H). simpl in IHl. lia.
Qed.

Lemma mkApps_eq_left x y l : mkApps x l = mkApps y l -> x = y.
Proof.
  induction l in x, y |- *; simpl. auto.
  intros. simpl in *. specialize (IHl _ _ H). now noconf IHl.
Qed.

Lemma decompose_app_eq_right t l l' : decompose_app_rec t l = decompose_app_rec t l' -> l = l'.
Proof.
  induction t in l, l' |- *; simpl; intros [=]; auto.
  specialize (IHt1 _ _ H0). now noconf IHt1.
Qed.

Lemma mkApps_eq_right t l l' : mkApps t l = mkApps t l' -> l = l'.
Proof.
  intros. eapply (f_equal decompose_app) in H. unfold decompose_app in H.
  rewrite !decompose_app_rec_mkApps in H. apply decompose_app_eq_right in H.
  now rewrite !app_nil_r in H.
Qed.

Lemma atom_decompose_app t l : isApp t = false -> decompose_app_rec t l = pair t l.
Proof. destruct t; simpl; congruence. Qed.

Lemma mkApps_eq_inj {t t' l l'} : mkApps t l = mkApps t' l' ->
                                   isApp t = false -> isApp t' = false -> t = t' /\ l = l'.
Proof.
  intros Happ Ht Ht'. eapply (f_equal decompose_app) in Happ. unfold decompose_app in Happ.
  rewrite !decompose_app_rec_mkApps in Happ. rewrite !atom_decompose_app in Happ; auto.
  now rewrite !app_nil_r in Happ.
Qed.

Section ParallelWeakening.

  Lemma weakening_pred1 Σ Γ Γ' Γ'' M N : wf Σ ->
    pred1 Σ (Γ ,,, Γ') M N ->
    pred1 Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') (lift #|Γ''| #|Γ'| M) (lift #|Γ''| #|Γ'| N).
  Proof.
    intros wfΣ H.
    remember (Γ ,,, Γ') as Γ0. revert Γ0 M N H Γ Γ' Γ'' HeqΓ0.
    refine (pred1_ind_all Σ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); intros *; intros;
      rename_all_hyps; try subst Γ; cbn -[iota_red];
      match goal with
        |- context [iota_red _ _ _ _] => idtac
      | |- _ => autorewrite with lift
      end;
      try specialize (forall_Γ _ _ Γ'' eq_refl);
      try specialize (forall_Γ0 _ _ Γ'' eq_refl);
      simpl; try solve [ econstructor; eauto; try apply All2_map;
                         unfold All2_prop_eq, All2_prop, on_Trel_eq, on_Trel, id in *; solve_all];
        unfold All2_prop_eq, All2_prop, on_Trel_eq, on_Trel, id in *.

    - (* Beta *)
      specialize (forall_Γ _ (Γ',, vass na t) Γ'' eq_refl).
      econstructor; now rewrite !lift_context_snoc0 Nat.add_0_r in forall_Γ.

    - (* Zeta *)
      specialize (forall_Γ0 _ (Γ',, vdef na d0 t) Γ'' eq_refl).
      simpl. econstructor; auto.
      now rewrite !lift_context_snoc0 Nat.add_0_r in forall_Γ0.

    - (* Rel *)
      elim (leb_spec_Set); intros Hn.
      + erewrite (weaken_nth_error_ge Hn) in heq_option_map.
        econstructor. eauto.
        rewrite simpl_lift in forall_Γ; try lia.
        now rewrite Nat.add_succ_r in forall_Γ.
      + econstructor. rewrite (weaken_nth_error_lt Hn).
        rewrite option_map_decl_body_map_decl heq_option_map.
        reflexivity.
        rewrite lift_simpl; try easy.

    - rewrite lift_iota_red.
      autorewrite with lift.
      econstructor.
      apply All2_map. solve_all.
      unfold on_Trel_eq, on_Trel in *. solve_all.

    - pose proof (lift_declared_constant _ _ _ #|Γ''| #|Γ'| wfΣ H).
      apply (f_equal cst_body) in H0.
      rewrite <- !map_cst_body in H0. rewrite heq_cst_body in H0. simpl in H0.
      noconf H0. simpl in H0. rewrite <- H0.
      econstructor; eauto.

    - simpl. eapply pred_proj with (map (lift #|Γ''| #|Γ'|) args1). eapply All2_map; solve_all.
      now rewrite nth_error_map heq_nth_error.

    - specialize (forall_Γ0 Γ0 (Γ' ,, _) Γ'' eq_refl).
      rewrite lift_context_snoc0 Nat.add_0_r in forall_Γ0.
      econstructor; eauto.

    - specialize (forall_Γ1 Γ0 (Γ' ,, _) Γ'' eq_refl).
      rewrite lift_context_snoc0 Nat.add_0_r in forall_Γ1.
      econstructor; eauto.

    - econstructor. apply All2_map. red in X. unfold on_Trel_eq, on_Trel, id in *.
      pose proof (All2_length _ _ X).
      solve_all.
      specialize (b0 Γ0 Γ' Γ'' eq_refl).
      specialize (b Γ0 (Γ' ,,, fix_context mfix0) Γ'').
      rewrite app_context_assoc in b. specialize (b eq_refl).
      rewrite lift_context_app Nat.add_0_r app_context_length fix_context_length
              app_context_assoc in b.
      now rewrite lift_fix_context -H.

    - econstructor. apply All2_map. red in X. unfold on_Trel_eq, on_Trel, id in *.
      pose proof (All2_length _ _ X).
      solve_all.
      specialize (b0 Γ0 Γ' Γ'' eq_refl).
      specialize (b Γ0 (Γ' ,,, fix_context mfix0) Γ'').
      rewrite app_context_assoc in b. specialize (b eq_refl).
      rewrite lift_context_app Nat.add_0_r app_context_length fix_context_length
              app_context_assoc in b.
      now rewrite lift_fix_context -H.

    - specialize (forall_Γ0 Γ0 (Γ' ,, _) Γ'' eq_refl).
      rewrite lift_context_snoc0 Nat.add_0_r in forall_Γ0.
      econstructor; eauto.

    - revert H. induction t; intros; try discriminate; try solve [ constructor; simpl; eauto ];
                  try solve [ apply (pred_atom); auto ].
      apply pred1_refl.
  Qed.

  Lemma weakening_pred1_0 Σ Γ Γ' M N : wf Σ ->
    pred1 Σ Γ M N ->
    pred1 Σ (Γ ,,, Γ') (lift0 #|Γ'| M) (lift0 #|Γ'| N).
  Proof. apply (weakening_pred1 Σ Γ [] Γ' M N). Qed.

End ParallelWeakening.

Section ParallelSubstitution.

  Inductive psubst Σ (Γ : context) : list term -> list term -> context -> Type :=
  | emptyslet : psubst Σ Γ [] [] []
  | cons_let_ass Δ s s' na t t' T :
      psubst Σ Γ s s' Δ ->
      pred1 Σ Γ t t' ->
      psubst Σ Γ (t :: s) (t' :: s') (Δ ,, vass na T)
  | cons_let_def Δ s s' na t t' T :
      psubst Σ Γ s s' Δ ->
      pred1 Σ Γ (subst0 s t) (subst0 s' t') ->
      psubst Σ Γ (subst0 s t :: s) (subst0 s' t' :: s') (Δ ,, vdef na t T).

  Lemma psubst_length {Σ Γ s s' Γ'} : psubst Σ Γ s s' Γ' -> #|s| = #|Γ'|.
  Proof.
    induction 1; simpl; auto with arith.
  Qed.

  Lemma psubst_length' {Σ Γ s s' Γ'} : psubst Σ Γ s s' Γ' -> #|s'| = #|Γ'|.
  Proof.
    induction 1; simpl; auto with arith.
  Qed.

  Lemma psubst_nth_error  Σ Γ s s' Δ n t :
    psubst Σ Γ s s' Δ ->
    nth_error s n = Some t ->
    ∃ decl t',
      (nth_error Δ n = Some decl) *
      (nth_error s' n = Some t') *
    match decl_body decl return Type with
    | Some d =>
      { u &
      let b := subst0 (skipn (S n) s) d in
      let b' := subst0 (skipn (S n) s') u in
      (t = b) * (t' = b') * pred1 Σ Γ t t' }%type
    | None => pred1 Σ Γ t t'
    end.
  Proof.
    induction 1 in n |- *; simpl; auto; destruct n; simpl; try congruence.
    - intros [= <-]. exists (vass na T), t'. intuition auto.
    - intros.
      specialize (IHX _ H). intuition auto.
    - intros [= <-]. exists (vdef na t0 T), (subst0 s' t'). intuition auto.
      simpl. exists t'. intuition simpl; auto.
    - apply IHX.
  Qed.

  (** Parallel reduction is substitutive. *)
  Lemma substitution_let_pred1 Σ Γ Δ Γ' s s' M N : wf Σ ->
    psubst Σ Γ s s' Δ ->
    pred1 Σ (Γ ,,, Δ ,,, Γ') M N ->
    pred1 Σ (Γ ,,, subst_context s 0 Γ') (subst s #|Γ'| M) (subst s' #|Γ'| N).
  Proof.
    intros wfΣ Hs H.
    remember (Γ ,,, Δ ,,, Γ') as Γ0. revert Γ0 M N H Γ Δ Γ' HeqΓ0 s s' Hs.
    refine (pred1_ind_all Σ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); intros *; intros;
      rename_all_hyps; try subst Γ; cbn -[iota_red];
      match goal with
        |- context [iota_red _ _ _ _] => idtac
      | |- _ => autorewrite with subst
      end;
      try specialize (forall_Γ _ _ _ eq_refl _ _ Hs);
      try specialize (forall_Γ0 _ _ _ eq_refl _ _ Hs);
      simpl; try solve [ econstructor; eauto; try apply All2_map;
                         unfold All2_prop_eq, All2_prop, on_Trel_eq, on_Trel, id in *; solve_all];
        unfold All2_prop_eq, All2_prop, on_Trel_eq, on_Trel, id in *.

    - (* Beta *)
      specialize (forall_Γ _ _ (Γ',, vass na t) eq_refl _ _ Hs).
      econstructor; now rewrite !subst_context_snoc0 in forall_Γ.

    - (* Zeta *)
      specialize (forall_Γ0 _ _ (Γ',, vdef na d0 t) eq_refl _ _ Hs).
      simpl. econstructor; auto.
      now rewrite !subst_context_snoc0 in forall_Γ0.

    - (* Rel *)
      pose proof (psubst_length Hs) as Hlens.
      pose proof (psubst_length' Hs) as Hlens'. rewrite <- Hlens in Hlens'.
      elim (leb_spec_Set); intros Hn.
      destruct (nth_error s) eqn:Heq.
      ++ (* Let-bound variable *)
         pose proof (nth_error_Some_length Heq).
         rewrite -> nth_error_app_context_ge in heq_option_map by lia.
         rewrite -> nth_error_app_context_lt in heq_option_map by lia.
         eapply psubst_nth_error in Heq as [decl [t' [[Heq' Heq''] Heq]]]; eauto. simpl in Heq.
         rewrite Heq' in heq_option_map.
         destruct decl as [na [b|] ty]; noconf heq_option_map.
         destruct Heq as [u [[-> ->] _]].
         pose (commut_lift_subst_rec body (skipn (S (i - #|Γ'|)) s) #|Γ'| 0 0).
         forward e by lia. rewrite e.
         simpl. rewrite subst_skipn. auto with arith.
         rewrite simpl_lift; auto with arith.
         assert(S (i - #|Γ'|) + #|Γ'| = S i) as -> by lia.
         apply forall_Γ.
      ++ destruct (nth_error (_ ,,, _) _) eqn:HΓ'; noconf heq_option_map. simpl in H.
         destruct c as [na [b|] ty]; noconf H.
         (* Rel is a let-bound variable in Γ0 *)
         apply nth_error_None in Heq.
         rewrite nth_error_app_context_ge /= in HΓ'. autorewrite with wf; lia.
         rewrite nth_error_app_context_ge /= in HΓ'. autorewrite with wf; lia.
         econstructor.
         rewrite nth_error_app_context_ge /=. autorewrite with wf; lia.
         rewrite Hlens; autorewrite with wf.
         assert (i - #|Γ'| - #|Δ| = i - #|Δ| - #|Γ'|) as <- by lia. rewrite HΓ'.
         reflexivity.
         assert(eq:S i = Init.Nat.add #|Δ| (S (i - #|Δ|))) by lia. rewrite eq in forall_Γ.
         rewrite simpl_subst' in forall_Γ; auto. lia.
         now rewrite Hlens.
      ++ (* Local variable from Γ' *)
        econstructor.
        rewrite nth_error_app_context_lt /= in heq_option_map. autorewrite with wf; lia.
        rewrite nth_error_app_context_lt; try (autorewrite with wf; lia).
        rewrite nth_error_subst_context. rewrite option_map_decl_body_map_decl heq_option_map.
        simpl. reflexivity.
        rewrite Nat.add_0_r.
        rewrite (commut_lift_subst_rec body s (S i) (#|Γ'| - S i) 0); try lia.
        assert (#|Γ'| - S i + S i = #|Γ'|) as -> by lia.
        apply forall_Γ.

    - rewrite subst_iota_red.
      autorewrite with subst.
      econstructor.
      apply All2_map. solve_all. unfold on_Trel_eq, on_Trel. solve_all.

    - pose proof (subst_declared_constant _ _ _ s' #|Γ'| u wfΣ H).
      apply (f_equal cst_body) in H0.
      rewrite <- !map_cst_body in H0. rewrite heq_cst_body in H0. simpl in H0.
      noconf H0. simpl in H0. rewrite H0.
      econstructor; eauto.

    - simpl. eapply pred_proj with (map (subst s' #|Γ'|) args1). eapply All2_map; solve_all.
      now rewrite nth_error_map heq_nth_error.

    - specialize (forall_Γ0 Γ0 Δ (Γ' ,, _) eq_refl _ _ Hs).
      rewrite subst_context_snoc0 in forall_Γ0.
      econstructor; eauto.

    - specialize (forall_Γ1 Γ0 Δ (Γ' ,, _) eq_refl _ _ Hs).
      rewrite subst_context_snoc0 in forall_Γ1.
      econstructor; eauto.

    - econstructor. apply All2_map. red in X. unfold on_Trel_eq, on_Trel, id in *.
      pose proof (All2_length _ _ X).
      solve_all; rename_all_hyps.
      specialize (forall_Γ Γ0 Δ Γ' eq_refl _ _ Hs).
      specialize (forall_Γ0 Γ0 Δ (Γ' ,,, fix_context mfix0)).
      rewrite app_context_assoc in forall_Γ0. specialize (forall_Γ0 eq_refl _ _ Hs).
      rewrite subst_context_app Nat.add_0_r app_context_length fix_context_length
              app_context_assoc in forall_Γ0.
      now rewrite subst_fix_context -heq_length.

    - econstructor. apply All2_map. red in X. unfold on_Trel_eq, on_Trel, id in *.
      pose proof (All2_length _ _ X).
      solve_all; rename_all_hyps.
      specialize (forall_Γ Γ0 Δ Γ' eq_refl _ _ Hs).
      specialize (forall_Γ0 Γ0 Δ (Γ' ,,, fix_context mfix0)).
      rewrite app_context_assoc in forall_Γ0. specialize (forall_Γ0 eq_refl _ _ Hs).
      rewrite subst_context_app Nat.add_0_r app_context_length fix_context_length
              app_context_assoc in forall_Γ0.
      now rewrite subst_fix_context -heq_length.

    - specialize (forall_Γ0 Γ0 Δ (Γ' ,, _) eq_refl _ _ Hs).
      rewrite subst_context_snoc0 in forall_Γ0.
      econstructor; eauto.

    - revert H. induction t; intros; try discriminate; try solve [ constructor; simpl; eauto ];
                  try solve [ apply (pred_atom); auto ].
      simpl.
      pose proof (psubst_length Hs) as Hlens.
      pose proof (psubst_length' Hs) as Hlens'. rewrite <- Hlens in Hlens'.
      elim (leb_spec_Set); intros Hn.
      destruct (nth_error s) eqn:Heq.
      ++ eapply psubst_nth_error in Heq as [decl [t' [[Heq' Heq''] Heq]]]; eauto.
         pose proof (nth_error_Some_length Heq'). rewrite Heq''.
         destruct decl as [na [b|] ty]; [destruct Heq as [u [[-> ->] Hred]]|].
         +++ (* Let-bound variable *)
           epose proof (weakening_pred1 _ Γ0 [] (subst_context s 0 Γ') _ _ wfΣ) as Hw.
           simpl in Hw. rewrite subst_context_length in Hw. eauto.
         +++ epose proof (weakening_pred1 _ Γ0 [] (subst_context s 0 Γ') _ _ wfΣ Heq) as Hw.
             simpl in Hw. now rewrite subst_context_length in Hw.
      ++ (* Rel is a let-bound variable in Γ0 *)
         apply nth_error_None in Heq. rewrite <- Hlens' in Heq.
         rewrite (proj2 (nth_error_None s' (n - #|Γ'|)) Heq). rewrite Hlens'.
         apply pred1_refl.
      ++ apply pred1_refl.
  Qed.

  Hint Constructors psubst : pcuic.
  Hint Transparent vass vdef : pcuic.

  Lemma substitution0_pred1 {Σ : global_context} Γ M M' na A N N' : wf Σ ->
    pred1 Σ Γ M M' ->
    pred1 Σ (Γ ,, vass na A) N N' ->
    pred1 Σ Γ (subst1 M 0 N) (subst1 M' 0 N').
  Proof.
    intros wfΣ redM redN.
    pose proof (substitution_let_pred1 Σ Γ [vass na A] [] [M] [M'] N N' wfΣ) as H.
    forward H. constructor; auto with pcuic.
    forward H by assumption.
    now simpl in H.
  Qed.

  Lemma substitution0_let_pred1 {Σ Γ na M M' A N N'} : wf Σ ->
    pred1 Σ Γ M M' ->
    pred1 Σ (Γ ,, vdef na M A) N N' ->
    pred1 Σ Γ (subst1 M 0 N) (subst1 M' 0 N').
  Proof.
    intros wfΣ redN.
    pose proof (substitution_let_pred1 Σ Γ [vdef na M A] [] [M] [M'] N N' wfΣ) as H.
    forward H. pose proof (cons_let_def Σ Γ [] [] [] na M M' A).
    rewrite !subst_empty in X.
    forward X by constructor.
    apply X, redN.
    now simpl in H.
  Qed.

  Lemma mkApps_eq_decompose {f args t} :
    mkApps f args = t ->
    isApp f = false ->
    fst (decompose_app t) = f.
  Proof.
    intros H Happ; apply (f_equal decompose_app) in H.
    rewrite decompose_app_mkApps in H. auto. rewrite <- H. reflexivity.
  Qed.

  Lemma pred_mkApps Σ Γ M0 M1 N0 N1 :
    pred1 Σ Γ M0 M1 ->
    All2 (pred1 Σ Γ) N0 N1 ->
    pred1 Σ Γ (mkApps M0 N0) (mkApps M1 N1).
  Proof.
    intros.
    induction X0 in M0, M1, X |- *. auto.
    simpl. eapply IHX0. now eapply pred_app.
  Qed.

  Lemma pred_snd_nth:
    ∀ (Σ : global_context) (Γ : context) (c : nat) (brs1 brs' : list (nat * term)),
      All2
        (on_Trel (pred1 Σ Γ) snd) brs1
        brs'
      → pred1 Σ Γ
              (snd (nth c brs1 (0, tDummy)))
              (snd (nth c brs' (0, tDummy))).
  Proof.
    intros Σ Γ c brs1 brs' brsl.
    induction brsl in c |- *; simpl. apply pred1_refl.
    destruct c; auto.
  Qed.

  Lemma All2_skipn {A} {P : A -> A -> Type} {l l'} {n} : All2 P l l' -> All2 P (skipn n l) (skipn n l').
  Proof. intros HPL; induction HPL in n |- * ; simpl; destruct n; try econstructor; eauto. Qed.

  Lemma All2_app {A} {P : A -> A -> Type} {l l' r r'} :
    All2 P l l' -> All2 P r r' ->
    All2 P (l ++ r) (l' ++ r').
  Proof. induction 1; simpl; auto. Qed.

  Ltac finish_discr :=
    match goal with
    | [ H : mkApps _ _ = mkApps _ _ |- _ ] =>
      let H0 := fresh in let H1 := fresh in
      specialize (mkApps_eq_inj H eq_refl eq_refl) as [H0 H1]; try (congruence || (noconf H0; noconf H1))
    | [ H : mkApps _ _ = _ |- _ ] => apply mkApps_eq_head in H
    end.

  Ltac prepare_discr :=
    match goal with
    | [ H : mkApps _ _ = mkApps _ _ |- _ ] => idtac
    | [ H : mkApps ?f ?l = tApp ?y ?r |- _ ] => change (mkApps f l = mkApps y [r]) in H
    | [ H : tApp ?f ?l = mkApps ?y ?r |- _ ] => change (mkApps f [l] = mkApps y r) in H
    | [ H : mkApps ?x ?l = ?y |- _ ] =>
      change (mkApps x l = mkApps y []) in H
    | [ H : ?x = mkApps ?y ?l |- _ ] =>
      change (mkApps x [] = mkApps y l) in H
    end.

  Lemma atom_mkApps {t l} : atom (mkApps t l) -> atom t /\ l = [].
  Proof.
    induction l in t |- *; simpl; auto.
    intros. destruct (IHl _ H). discriminate.
  Qed.

  Definition application_atom t :=
    match t with
    | tVar _
    | tMeta _
    | tSort _
    | tInd _ _
    | tConstruct _ _ _ => true
    | _ => false
    end.

  Lemma application_atom_mkApps {t l} : application_atom (mkApps t l) -> application_atom t /\ l = [].
  Proof.
    induction l in t |- *; simpl; auto.
    intros. destruct (IHl _ H). discriminate.
  Qed.

  Ltac solve_discr :=
    (try (progress (prepare_discr; finish_discr)));
    (try (match goal with
          | [ H : is_true (application_atom _) |- _ ] => discriminate
          | [ H : is_true (atom _) |- _ ] => discriminate
          | [ H : is_true (atom (mkApps _ _)) |- _ ] => destruct (atom_mkApps H); subst; try discriminate
          | [ H : is_true (application_atom (mkApps _ _)) |- _ ] =>
            destruct (application_atom_mkApps H); subst; try discriminate
          end)).

  Lemma mkApps_eq_decompose_app {t t' l l'} :
    mkApps t l = mkApps t' l' ->
    decompose_app_rec t l = decompose_app_rec t' l'.
  Proof.
    induction l in t, t', l' |- *; simpl.
    - intros ->. rewrite !decompose_app_rec_mkApps.
      now rewrite app_nil_r.
    - intros H. apply (IHl _ _ _ H).
  Qed.

  Lemma pred1_mkApps_tConstruct (Σ : global_context) (Γ : context)
        ind pars k (args : list term) c :
    pred1 Σ Γ (mkApps (tConstruct ind pars k) args) c ->
    {args' : list term & (c = mkApps (tConstruct ind pars k) args') * (All2 (pred1 Σ Γ) args args') }%type.
  Proof with solve_discr.
    revert c. induction args using rev_ind; intros; simpl in *.
    depelim X... exists []. intuition auto.
    intros. rewrite <- mkApps_nested in X.
    depelim X... apply mkApps_eq_decompose_app in x.
    rewrite !decompose_app_rec_mkApps in x. noconf x.
    destruct (IHargs _ X1) as [args' [-> Hargs']].
    exists (args' ++ [N1])%list.
    rewrite <- mkApps_nested. intuition auto.
    eapply All2_app; auto.
  Qed.

  Lemma pred1_mkApps_tFix (Σ : global_context) (Γ : context)
        mfix0 idx (args0 : list term) c :
    pred1 Σ Γ (mkApps (tFix mfix0 idx) args0) c ->
    ({ mfix1 & { args1 : list term &
                         (c = mkApps (tFix mfix1 idx) args1) *
                         All2_prop2_eq Γ (Γ ,,, fix_context mfix0) dtype dbody
                                    (fun x => (dname x, rarg x))
                                    (pred1 Σ) mfix0 mfix1 *
                         (All2 (pred1 Σ Γ) ) args0 args1 } }%type) +
    ({ args1 & { narg & { fn0 & { fn1 &
     ((unfold_fix mfix0 idx = Some (narg, fn0)) *
      (is_constructor narg args1 = true) *
      (All2 (pred1 Σ Γ) args0 args1) *
      (pred1 Σ Γ fn0 fn1) * (c = mkApps fn1 args1)) } } } })%type.
  Proof with solve_discr.
    intros pred. remember (mkApps _ _) as fixt. revert mfix0 idx args0 Heqfixt.
    induction pred; intros; solve_discr.
    - right. exists args1, narg, fn0, fn1. intuition eauto.
    - destruct args0 using rev_ind. noconf Heqfixt. clear IHargs0.
      rewrite <- mkApps_nested in Heqfixt. noconf Heqfixt.
      clear IHpred2. specialize (IHpred1 _ _ _ eq_refl).
      destruct IHpred1 as [[? [? ?]]|[? [? [? [? ?]]]]].
      -- left. eexists _. eexists (_ ++ [N1])%list. rewrite <- mkApps_nested.
         intuition eauto. simpl. subst M1. reflexivity.
         eapply All2_app; eauto.
      -- right. eexists (x ++ [N1])%list, x0, x1, x2. intuition auto.
         clear -b2.
         generalize [N1]. unfold is_constructor in *.
         destruct nth_error eqn:Heq.
         pose proof (nth_error_Some_length Heq).
         intros. rewrite nth_error_app_lt; auto. rewrite Heq; auto.
         intros. discriminate.
         eapply All2_app; eauto.
         now rewrite <- mkApps_nested, b.

    - left.
      eexists mfix1, []. intuition auto.
    - subst t. eapply atom_mkApps in i as [Heq ->].
      left. exists mfix0, []. intuition auto.
      red. generalize (fix_context mfix0).
      induction mfix0; constructor; unfold on_Trel_eq, on_Trel; intuition auto using pred1_refl.
      apply X.
  Qed.

  Lemma mkApps_eq_decompose_app_rec {f args t l} :
    mkApps f args = t ->
    isApp f = false ->
    match decompose_app_rec t l with
    | (f', args') => f' = f /\ mkApps t l = mkApps f' args'
    end.
  Proof.
    revert f t l.
    induction args using rev_ind; simpl.
    - intros * -> **. rewrite atom_decompose_app; auto.
    - intros. rewrite <- mkApps_nested in H.
      specialize (IHargs f).
      destruct (isApp t) eqn:Heq.
      destruct t; try discriminate.
      simpl in Heq. noconf H. simpl.
      specialize (IHargs (mkApps f args) (x :: l) eq_refl H0).
      destruct decompose_app_rec. intuition.
      subst t.
      simpl in Heq. discriminate.
  Qed.

  Lemma mkApps_eq_decompose' {f args t} :
    mkApps f args = t ->
    isApp f = false ->
    match decompose_app t with
    | (f', args') => f' = f /\ t = mkApps f' args'
    end.
  Proof.
    intros. apply (@mkApps_eq_decompose_app_rec f args t []); auto.
  Qed.

  Derive NoConfusion for All2.

  Definition pred1_decl_body Σ (Γ Γ' : context) (b : option (term * term)) (t t' : term) :=
    match b with
    | Some (b, b') => pred1 Σ Γ b b'
    | None => True
    end.

  Section All_local_2.
    Context (P : forall (Γ Γ' : context), option (term * term) -> term -> term -> Type).

    Inductive All2_local_env : context -> context -> Type :=
    | localenv2_nil : All2_local_env [] []
    | localenv2_cons_abs Γ Γ' na t t' :
        All2_local_env Γ Γ' ->
        P Γ Γ' None t t' ->
        All2_local_env (Γ ,, vass na t) (Γ' ,, vass na t')
    | localenv2_cons_def Γ Γ' na b b' t t' :
        All2_local_env Γ Γ' ->
        P Γ Γ' (Some (b, b')) t t' ->
        All2_local_env (Γ ,, vdef na b t) (Γ' ,, vdef na b' t').
  End All_local_2.

  Notation pred1_ctx Σ Γ Γ' := (All2_local_env (pred1_decl_body Σ) Γ Γ').

  Ltac my_rename_hyp h th :=
    match th with
    | pred1_ctx _ _ ?G => fresh "pred" G
    | _ => PCUICWeakeningEnv.my_rename_hyp h th
    end.

  Ltac rename_hyp h ht ::= my_rename_hyp h ht.

  Lemma pred1_ctx_refl Σ Γ : pred1_ctx Σ Γ Γ.
  Proof.
    induction Γ. constructor.
    destruct a as [na [b|] ty]; constructor; try red; simpl; auto with pcuic. apply pred1_refl.
  Qed.

  Lemma nth_error_pred1_ctx {Σ Γ Δ} i body :
    pred1_ctx Σ Γ Δ ->
    option_map decl_body (nth_error Γ i) = Some (Some body) ->
    { body' & (option_map decl_body (nth_error Δ i) = Some (Some body')) *
              pred1 Σ (skipn (S i) Γ) body body' }%type.
  Proof.
    intros Hpred. revert i body.
    induction Hpred; destruct i; try discriminate; auto; intros; rename_all_hyps.
    simpl in heq_option_map. specialize (forall_i _ _ heq_option_map) as [body' [Heq Hpred']].
    intuition eauto.
    noconf heq_option_map. exists b'. intuition eauto.
    simpl in heq_option_map. specialize (forall_i _ _ heq_option_map) as [body' [Heq Hpred']].
    intuition eauto.
  Qed.

  Ltac apply_hyp :=
    match reverse goal with
    | [ H : forall r, pred1 _ _ ?s _ -> _, H' : pred1 _ _ ?s _, H'' : pred1_ctx _ _ _, H''' : pred1_ctx _ _ _ |- _ ] =>
      let target := fresh "v" in specialize (H _ H' _ _ H''' H'') as [target [? ?]]
    end.

  Hint Constructors pred1 : pcuic.

  Lemma All2_prop_eq_All2 {A B} {Σ Γ} {f : A -> term} {g : A -> B} args0 args1 args3 :
    All2_prop_eq Γ f g
     (λ (Γ : context) (x y : term),
      (pred1 Σ Γ x y *
       (∀ r : term, pred1 Σ Γ x r →
        ∀ Δ Δ' : context, pred1_ctx Σ Γ Δ → pred1_ctx Σ Γ Δ' →
        {v : term & pred1 Σ Δ y v * pred1 Σ Δ' r v}))%type)
     args0 args1 ->
    All2 (on_Trel_eq (pred1 Σ Γ) f g) args0 args3 ->
    All2 (fun x y =>
        ∀ Δ Δ' : context, pred1_ctx Σ Γ Δ → pred1_ctx Σ Γ Δ' →
        {v : term & pred1 Σ Δ (f x) v * pred1 Σ Δ' (f y) v * (g x = g y)})%type args1 args3.
  Proof.
    intros HP H. red in HP.
    induction HP in args3, H |- *; depelim H; constructor; eauto.
    unfold on_Trel_eq, on_Trel in *. destruct r as [[pr Hr] Heq].
    destruct r0 as [pr0 eq0]. !intros.
    destruct (Hr _ pr0 _ _ predΔ predΔ'). rewrite <- Heq.
    intuition eauto.
  Qed.

  Lemma All2_prop_All2 {Σ Γ} args0 args1 args3 :
    All2_prop Γ
     (λ (Γ : context) (x y : term),
      (pred1 Σ Γ x y *
       (∀ r : term, pred1 Σ Γ x r →
        ∀ Δ Δ' : context, pred1_ctx Σ Γ Δ → pred1_ctx Σ Γ Δ' →
        {v : term & pred1 Σ Δ y v * pred1 Σ Δ' r v}))%type)
     args0 args1 ->
    All2 (pred1 Σ Γ) args0 args3 ->
    All2 (fun x y =>
        ∀ Δ Δ' : context, pred1_ctx Σ Γ Δ → pred1_ctx Σ Γ Δ' →
        {v : term & pred1 Σ Δ x v * pred1 Σ Δ' y v})%type args1 args3.
  Proof.
    intros HP H. red in HP.
    induction HP in args3, H |- *; depelim H; constructor; eauto.
    unfold on_Trel_eq, on_Trel in *.
    !intros.
    destruct r as [r Hr].
    exact (Hr _ p _ _ predΔ predΔ').
  Qed.

  Definition on_Trel2 {A B} (R : A -> A -> Type) (f : B -> A) : B -> A -> Type :=
    fun x y => R (f x) y.

  Lemma All2_join_eq {A B} (f : A -> term) (g : A -> B) (h : term -> B -> A) {Σ Γ x y} :
    (forall x y, f (h x y) = x) ->
    (forall x y, g (h x y) = y) ->
    ∀ {Δ Δ' : context}, pred1_ctx Σ Γ Δ → pred1_ctx Σ Γ Δ' →
    All2 (λ x y,
         (∀ Δ Δ' : context, pred1_ctx Σ Γ Δ → pred1_ctx Σ Γ Δ' →
        {v : term & pred1 Σ Δ (f x) v * pred1 Σ Δ' (f y) v * (g x = g y)}))%type x y ->
    { l : list A & (All2 (on_Trel_eq (pred1 Σ Δ) f g) x l * All2 (on_Trel_eq (pred1 Σ Δ') f g) y l)%type }.
  Proof.
    intros * Hfh Hgh * redΔ redΔ'. induction 1. exists []. split; auto.
    destruct (r _ _ redΔ redΔ') as [r' [[rl rr] req]].
    destruct IHX as [IHl [ll lr]].
    exists (h r' (g x) :: IHl). intuition auto. constructor; auto.
    red. intuition auto. red. now rewrite Hfh.
    constructor; auto.
    red. intuition auto. red. now rewrite Hfh.
    rewrite <- req. auto.
  Qed.

  Lemma All2_join {Σ Γ x y} :
    ∀ {Δ Δ' : context}, pred1_ctx Σ Γ Δ → pred1_ctx Σ Γ Δ' →
    All2 (λ x y,
         (∀ Δ Δ' : context, pred1_ctx Σ Γ Δ → pred1_ctx Σ Γ Δ' →
        {v : term & pred1 Σ Δ x v * pred1 Σ Δ' y v}))%type x y ->
    { l : list term & (All2 (pred1 Σ Δ) x l * All2 (pred1 Σ Δ') y l)%type }.
  Proof.
    intros * redΔ redΔ'. induction 1. exists []. split; auto.
    destruct (r _ _ redΔ redΔ') as [r' [rl rr]].
    destruct IHX as [IHl [ll lr]].
    exists (r' :: IHl). intuition auto.
  Qed.

  Lemma All2_on_Trel_eq_impl {A B} Σ Γ {f : A -> term} {g : A -> B} {x y} :
    All2 (on_Trel_eq (pred1 Σ Γ) f g) x y ->
    All2 (on_Trel (pred1 Σ Γ) f) x y.
  Proof.
    induction 1; constructor; intuition auto. red in r. intuition.
  Qed.

  Lemma fst_decompose_app_rec t l : fst (decompose_app_rec t l) = fst (decompose_app t).
  Proof.
    induction t in l |- *; simpl; auto. rewrite IHt1.
    unfold decompose_app. simpl. now rewrite (IHt1 [t2]).
  Qed.

  Lemma isConstruct_app_inv t :
    isConstruct_app t = true ->
    ∃ ind k u args, t = mkApps (tConstruct ind k u) args.
  Proof.
    induction t; try discriminate.
    - unfold isConstruct_app. unfold decompose_app. simpl.
      rewrite fst_decompose_app_rec. intros.
      specialize (IHt1 H). destruct IHt1 as [ind [k [u [args ->]]]].
      rewrite decompose_app_mkApps in H; auto. simpl in H.
      exists ind, k, u, (args ++ [t2])%list.
      now rewrite <- mkApps_nested.
    - intros H.
      now exists i, n, u, [].
  Qed.

  Theorem confluence Σ Γ t l r : wf Σ ->
    pred1 Σ Γ t l -> forall (Hr : pred1 Σ Γ t r),
        forall Δ Δ', pred1_ctx Σ Γ Δ -> pred1_ctx Σ Γ Δ' ->
                  { v & (pred1 Σ Δ l v) * (pred1 Σ Δ' r v) }%type.
  Proof with solve_discr.
    intros wfΣ H; revert Γ t l H r.
    refine (pred1_ind_all Σ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); intros *.
    all:try intros **; rename_all_hyps;
      try solve [specialize (forall_Γ _ X3); eauto]; eauto;
        try solve [eexists; split; constructor; eauto].

  - (* Beta *)
    depelim Hr...
    + clear X1 X. repeat unshelve apply_hyp.
      specialize (forall_r _ Hr1 (Δ ,, vass na t) (Δ' ,, vass na t)) as [b' [lb' rb']].
      constructor; eauto. red. exact I.
      constructor; eauto. red. exact I.
      eexists. intuition eauto using substitution0_pred1.
    + clear X1 X; repeat apply_hyp.
      depelim Hr1...
      specialize (forall_r _ Hr1_2 (Δ ,, vass na M') (Δ' ,, vass na M')) as [b' [lb' rb']].
      constructor. auto. simpl. exact I.
      constructor. auto. simpl. exact I.
      exists (b' {0:=v}). intuition eauto using substitution0_pred1.
      constructor; eauto.

  - (* Zeta *)
    depelim Hr...
    + (* Zeta / Zeta *)
      specialize (forall_r _ Hr1 _ _ predΔ predΔ') as [v [? ?]].
      specialize (forall_r0 _ Hr2 (Δ ,, vdef na d1 t) (Δ' ,, vdef na d3 t)) as [v0 [? ?]].
      constructor; auto.
      constructor; auto.
      pose proof (substitution_let_pred1 Σ Δ [vdef na d1 t] [] [d1] [v] b1 v0 wfΣ) as H.
      simpl in H. forward H.
      pose proof (cons_let_def Σ Δ [] [] [] na d1 v t).
      rewrite -> !subst_empty in *.
      forward X0 by constructor.
      apply X0, p.
      pose proof (substitution_let_pred1 Σ Δ' [vdef na d3 t] [] [d3] [v] b3 v0 wfΣ) as H'.
      simpl in H'. forward H'.
      pose proof (cons_let_def Σ Δ' [] [] [] na d3 v t).
      rewrite !subst_empty in X0.
      forward X0 by constructor.
      apply X0, p0.
      eexists. split; eauto.

    + (* Zeta / Congruence *)
      specialize (forall_r _ Hr1 _ _ predΔ predΔ') as [v [? ?]].
      specialize (forall_r0 _ Hr3 (Δ ,, vdef na d1 t) (Δ' ,, vdef na d3 t1)) as [v0 [? ?]].
      constructor; auto.
      constructor; auto.
      exists (v0 { 0 := v }).
      intuition eauto using substitution0_let_pred1.
      econstructor; eauto.

  - (* Zeta in context *)
    depelim Hr...
    -- (* Zeta in context / Zeta in context *)
      rewrite heq_option_map in e. noconf e.
       clear X; apply_hyp. exists v; auto.
    -- (* Zeta in context / reflexivity *)
       red in i0. simpl in i0.
       specialize (nth_error_pred1_ctx i body predΔ') as [body'' [Hb Hred]]; eauto.
       eapply weakening_pred1_0 in Hred; eauto.
       unfold app_context in Hred.
       erewrite (firstn_skipn (S i) Γ) in Hred.
       rewrite firstn_length_le in Hred.
       destruct (nth_error Γ i) eqn:Heq; noconf heq_option_map.
       eauto using nth_error_Some_length with arith.
       specialize (forall_r _ Hred _ _ predΔ predΔ') as [v [? ?]].
       exists v. intuition eauto with pcuic.

  - (* Iota reduction *)
    depelim Hr... clear x.
    -- (* Iota / Iota *)
      eapply All2_prop_All2 in X; eauto.
      eapply (All2_join predΔ predΔ') in X as [l [Hl Hr]]; auto.
      eapply All2_prop_eq_All2 in X0; eauto.
      eapply (All2_join_eq snd fst (fun x y => (y, x)) _ _ predΔ predΔ') in X0 as [brs' [brsl brsr]]; eauto.
      exists (iota_red pars c l brs').
      unfold iota_red. simpl.
      split; eapply pred_mkApps; try eapply pred_snd_nth; auto.
      now eapply All2_on_Trel_eq_impl. now apply All2_skipn.
      now eapply All2_on_Trel_eq_impl. now apply All2_skipn.
    -- (* Iota / Congruence *)
       eapply All2_prop_eq_All2 in X0; eauto.
       eapply (All2_join_eq snd fst (fun x y => (y, x)) _ _ predΔ predΔ') in X0 as [brs' [brsl brsr]]; auto.
       eapply pred1_mkApps_tConstruct in Hr2 as [args' [-> Hargs']].
       eapply All2_prop_All2 in X; eauto.
       eapply (All2_join predΔ predΔ') in X as [l [Hl Hr]]; auto.
       exists (iota_red pars c l brs').
       unfold iota_red. simpl.
       split. eapply pred_mkApps; eauto using pred_snd_nth, All2_on_Trel_eq_impl.
       now eapply All2_skipn.
       econstructor; eauto.

  - (* Fixpoint unfolding *)
    (* Needs a specialized inversion lemma as fixpoints require spines of arguments. *)
    apply pred1_mkApps_tFix in Hr as [[mfix1 [args2 [[-> Hmfix] Hargs]]]|[mfix1 [fn0' [fn1' [H1 H2]]]]].
    * (* Fix / Congruence *)
      eapply All2_prop_All2 in X; eauto.
      eapply (All2_join predΔ predΔ') in X as [args' [argsl argsr]]; auto.
      unfold unfold_fix in heq_unfold_fix.
      destruct (nth_error mfix idx) eqn:Heq; try discriminate.
      noconf heq_unfold_fix. red in Hmfix.
      eapply All2_nth_error_Some in Hmfix as [fn' [Hmfn' [Hredty [Hredbody Heqann]]]]; eauto.
      red in Hredbody.
      specialize (forall_r (subst0 (fix_subst mfix1) (dbody fn'))).
      forward forall_r.
      eapply (substitution_let_pred1 Σ Γ (fix_context mfix) [] (fix_subst mfix) (fix_subst mfix1)); eauto.
      (* That proof is somewhere already *) admit.
      specialize (forall_r _ _ predΔ predΔ') as [fn3 [fn1fn3 Hfn3]].
      exists (mkApps fn3 args').
      split. eapply pred_mkApps; eauto.
      econstructor; eauto. unfold unfold_fix. rewrite Hmfn'. reflexivity.
      noconf Heqann. simpl in H. noconf H. rewrite <- H0.
      clear -heq_is_constructor argsl.
      unfold is_constructor in heq_is_constructor.
      destruct nth_error eqn:Heq; try discriminate.
      { eapply All2_nth_error_Some in argsl as [t' [Hred]]; eauto.
        eapply isConstruct_app_inv in heq_is_constructor as [ind [k [u [args ->]]]].
        eapply pred1_mkApps_tConstruct in p as [args'' [-> Hredargs]].
        unfold is_constructor. rewrite Hred. unfold isConstruct_app.
        rewrite decompose_app_mkApps; auto. }

    * (* Fix / Fix *)
      rewrite heq_unfold_fix in H2. intuition. rename_all_hyps.
      subst. noconf heq_Some.
      eapply All2_prop_All2 in X; eauto.
      specialize (forall_r _ b0 _ _ predΔ predΔ') as [fn' [lfn' rfn']].
      eapply (All2_join predΔ predΔ') in X as [args' [argsl argsr]]; auto.
      exists (mkApps fn' args'). split; eapply pred_mkApps; eauto.

  - (* CoFix reduction *)
    depelim Hr...
    + (* CoFix / CoFix *) admit.
    + (* CoFix / Congruence *) admit.

  - (* Proj CoFix *)
    depelim Hr...
    + (* Proj Cofix / Proj Cofix *) admit.
    + (* Proj CoFix / Congruence *) admit.

  - (* Constant *)
    depelim Hr...
    + admit. (* Reduction *)
    + (* Atom *) admit.

  - (* Proj Case *)
    admit.

  - (* Lambda *)
    depelim Hr...
    admit.

  - (* Application *)
    depelim Hr...
    + (* / Beta *)
      admit.
    + (* / Fix *)
      admit.
    + (* App Congruence *)
      admit.

  - (* LetIn *) admit.

  - (* Case *)
    depelim Hr...
    all:admit.

  - (* Proj *)
    depelim Hr...
    all:admit.

  - (* Fix *)
    all:admit.

  - (* CoFix *)
    all:admit.

  - (* CoFix *)
    all:admit.

  - (* Evar *)
    all:admit.

  - (* Atom *)
    all:admit.

    (* to be continued :) *)
Admitted.

End ParallelSubstitution.