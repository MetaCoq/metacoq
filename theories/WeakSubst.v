From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import Template Ast Induction LiftSubst Typing.

Set Asymmetric Patterns.
Generalizable Variables Σ Γ t T.

Definition app_context (Γ Γ' : context) : context := Γ' ++ Γ.
Notation " Γ  ,,, Γ' " := (app_context Γ Γ') (at level 25, Γ' at next level, left associativity).
Notation "#| Γ |" := (length Γ) (at level 0, format "#| Γ |").

Lemma length_app_context Γ Γ' : #|Γ ,,, Γ'| = #|Γ| + #|Γ'|.
Proof.
  unfold app_context. rewrite app_length. omega.
Qed.

Definition map_decl (f : term -> term) (d : context_decl) : context_decl :=
  {| decl_name := d.(decl_name);
     decl_body := option_map f d.(decl_body);
     decl_type := f d.(decl_type) |}.

Definition lift_decl n k (d : context_decl) := map_decl (lift n k) d.

Definition lift_context_rec n k (Γ : context) : nat * context :=
  List.fold_right (fun decl '(k, Γ) => (S k, lift_decl n k decl :: Γ)) (k, []) Γ.

Definition lift_context n k Γ := snd (lift_context_rec n k Γ).

Lemma lift0_context k Γ : lift_context 0 k Γ = Γ.
Proof.
  unfold lift_context; induction Γ; simpl; trivial.
  simpl. destruct lift_context_rec. simpl in *.
  unfold lift_decl, map_decl. destruct a. simpl. rewrite IHΓ; f_equal.
  rewrite lift_rec0. now destruct decl_body; simpl; rewrite ?lift_rec0.
Qed.
  
Lemma lift_context_rec_fst n k Γ :
  fst (lift_context_rec n k Γ) = #|Γ| + k.
Proof.
  induction Γ; simpl; auto.
  destruct lift_context_rec; simpl in *.
  congruence.
Qed.
Hint Rewrite lift_context_rec_fst : lift.

Lemma lift_context_len n k Γ : #|lift_context n k Γ| = #|Γ|.
Proof.
  unfold lift_context; induction Γ; simpl; trivial.
  destruct lift_context_rec. simpl in *. auto with arith.
Qed.
Hint Rewrite lift_context_len : lift.

Lemma lift_context_snoc n k Γ d : lift_context n k (Γ ,, d) = lift_context n k Γ ,, lift_decl n (#|Γ| + k) d.
Proof.
  unfold lift_context.
  simpl.
  pose proof (lift_context_rec_fst n k Γ).
  revert H. destruct lift_context_rec. simpl.
  now intros ->.
Qed.
Hint Rewrite lift_context_snoc : lift.

Lemma some_inj {A} {x y : A} : Some x = Some y -> x = y.
Proof.
  now intros [=].
Qed.

Lemma nth_error_app_ge v Γ Γ' : #|Γ'| <= v -> nth_error (Γ ,,, Γ') v = nth_error Γ (v - #|Γ'|).
Proof.
  revert v; induction Γ'; simpl; intros.

  now rewrite Nat.sub_0_r.
  destruct v. omega.
  simpl. rewrite IHΓ'; easy.
Qed.

Lemma nth_error_app_lt v Γ Γ' : v < #|Γ'| -> nth_error (Γ ,,, Γ') v = nth_error Γ' v.
Proof.
  revert v; induction Γ'; simpl; intros. easy.

  destruct v; trivial.
  simpl. rewrite IHΓ'; easy.
Qed.

Lemma weaken_safe_nth_ge Γ Γ' v (isdecl : v < #|Γ ,,, Γ'|) Γ'' : #|Γ'| <= v ->
  exists isdecl',
  safe_nth (Γ ,,, Γ') (exist (fun n0 : nat => n0 < #|Γ ,,, Γ'|) v isdecl) =
  safe_nth (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') (exist _ (#|Γ''| + v) isdecl').
Proof.
  simpl.
  assert(#|Γ''| + v < #|Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ'|).
  rewrite !length_app_context in *. autorewrite with lift. omega.
  exists H.
  apply some_inj; rewrite <- !nth_error_safe_nth.
  rewrite nth_error_app_ge; try easy.
  rewrite (nth_error_app_ge (_ + v)); rewrite ?lift_context_len; try easy.
  rewrite nth_error_app_ge; rewrite ?lift_context_len; try easy.
Qed.

Lemma weaken_safe_nth_lt Γ Γ' v (isdecl : v < #|Γ ,,, Γ'|) Γ'' : v < #|Γ'| ->
  exists isdecl',
  safe_nth (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') (exist _ v isdecl') =
  lift_decl #|Γ''| (#|Γ'| - S v)
       (safe_nth (Γ ,,, Γ') (exist (fun n0 : nat => n0 < #|Γ ,,, Γ'|) v isdecl)).
Proof.
  simpl. intros Hv.
  assert(v < #|Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ'|).
  rewrite !length_app_context in *. autorewrite with lift. omega.
  exists H.
  apply some_inj. rewrite <- !nth_error_safe_nth.
  rewrite nth_error_app_lt. 2:rewrite !length_app_context in H; autorewrite with lift; omega.
  remember (safe_nth (Γ ,,, Γ') (exist _ v isdecl)) as nth.
  apply (f_equal Some) in Heqnth. rewrite <- nth_error_safe_nth in Heqnth.
  rewrite nth_error_app_lt in Heqnth; try easy.
  clear isdecl H Γ.
  revert Γ'' v Hv nth Heqnth.
  induction Γ'; intros.
  - easy.
  - simpl. destruct v.
    + simpl. unfold lift_context. simpl.
      destruct lift_context_rec eqn:Heq.
      pose proof (lift_context_rec_fst #|Γ''| 0 Γ'). rewrite Heq in H. simpl in H. subst n.
      simpl. rewrite Nat.add_0_r, Nat.sub_0_r.
      simpl in *. now injection Heqnth as ->.
    + simpl.
      unfold lift_context. simpl.
      destruct lift_context_rec eqn:Heq.
      pose proof (lift_context_rec_fst #|Γ''| 0 Γ'). rewrite Heq in H. simpl in H. subst n.
      simpl in *.
      assert (v < #|Γ'|) by easy.
      specialize (IHΓ' Γ'' v  H nth Heqnth).
      rewrite <- IHΓ'.
      f_equal. unfold lift_context. rewrite Heq. reflexivity.
Qed.  

Lemma typecheck_closed Σ Γ t T :
  type_global_env Σ -> type_local_env Σ Γ ->
  Σ ;;; Γ |-- t : T -> closedn #|Γ| t && closedn #|Γ| T = true.
Proof.
  induction 3; simpl; rewrite ?andb_true_iff in *; try solve [intuition auto].
  - elim (Nat.ltb_spec n #|Γ|); intuition.
    admit (* Need induction with IHs for environments *).
  - intuition auto.
    + eapply IHtyping2. constructor; auto.
      now exists s1. exact I.
  - intuition; eapply IHtyping2; constructor; auto.
    now exists s1. exact I.
    now exists s1. exact I.
  - intuition; try eapply IHtyping3; try constructor; auto.
    now exists s1. now exists s1. 
  - (* typing spine ind *) admit.
  - admit.
  - admit.
  - admit.
  - specialize (IHtyping H0).
    intuition auto. admit. admit. admit. admit.
  - (* proj *) admit.
  - admit.
  - admit.
Admitted.

Ltac forward H :=
  match type of H with
  | ?X -> ?Y => assert(x : X) ; [ | specialize (H x); clear x ]
  end.

Lemma weakening_rec Σ Γ Γ' Γ'' :
  type_global_env Σ -> type_local_env Σ (Γ ,,, Γ') ->
  type_local_env Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') ->
  `(Σ ;;; Γ ,,, Γ' |-- t : T ->
    Σ ;;; Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ' |--
    lift #|Γ''| #|Γ'| t : lift #|Γ''| #|Γ'| T).
Proof.
  intros HΣ HΓΓ' HΓ'' * H. revert Γ'' HΓ''. 
  dependent induction H; intros Γ'' HΓ''; simpl in *; try solve [econstructor; eauto].

  - elim (Nat.leb_spec); intros Hn.
    + destruct (weaken_safe_nth_ge _ _ _ isdecl Γ'' Hn) as [isdecl' ->].
      rewrite simpl_lift_rec; try omega. rewrite Nat.add_succ_r.
      now constructor.
    + destruct (weaken_safe_nth_lt _ _ _ isdecl Γ'' Hn) as [isdecl' H'].
      apply (f_equal decl_type) in H'.
      unfold lift_decl in H'. simpl in H'.
      assert (forall t, lift0 (S n) (lift #|Γ''| (#|Γ'| - S n) t) = lift #|Γ''| #|Γ'| (lift0 (S n) t)).
      intros. assert (#|Γ'| = S n + (#|Γ'| - S n)) by easy.
      rewrite H at 2.
      rewrite <- permute_lift_rec; try easy.
      rewrite <- H. rewrite <- H'. constructor.

  - econstructor; auto.
    simpl.
    specialize (IHtyping2 Γ (Γ' ,, vass n t) HΣ).
    forward IHtyping2. constructor; simpl; auto. now exists s1.
    specialize (IHtyping2 eq_refl Γ'').
    forward IHtyping2. rewrite lift_context_snoc. constructor. simpl; auto.
    exists s1. simpl. rewrite Nat.add_0_r. eapply IHtyping1; auto. exact I.
    rewrite lift_context_snoc, plus_0_r in IHtyping2.
    eapply IHtyping2.

  - econstructor; auto.
    simpl.
    specialize (IHtyping2 Γ (Γ' ,, vass n t) HΣ).
    forward IHtyping2. constructor; simpl; auto. now exists s1.
    specialize (IHtyping2 eq_refl Γ'').
    forward IHtyping2. rewrite lift_context_snoc. constructor. simpl; auto.
    exists s1. simpl. rewrite Nat.add_0_r. eapply IHtyping1; auto. exact I.
    rewrite lift_context_snoc, plus_0_r in IHtyping2.
    eapply IHtyping2.


  - econstructor; auto.
    simpl.
    specialize (IHtyping3 Γ (Γ' ,, vdef n b b_ty) HΣ).
    forward IHtyping3. constructor; simpl; auto. now exists s1.
    specialize (IHtyping3 eq_refl Γ'').
    forward IHtyping3. rewrite lift_context_snoc, Nat.add_0_r.
    constructor. simpl; auto.
    exists s1. simpl. eapply IHtyping1; auto. simpl.
    specialize (IHtyping2 Γ Γ' HΣ HΓΓ' eq_refl Γ'').
    now eapply IHtyping2.
    rewrite lift_context_snoc, plus_0_r in IHtyping3.
    eapply IHtyping3.
    

  - econstructor; auto.
    simpl.
    admit.

  - admit.
  - admit.
  - admit.

  - admit.
  - admit.
  - admit.
  - (* Conv *)
    admit.
Admitted.

Lemma type_local_env_app Σ (Γ Γ' : context) : type_local_env Σ (Γ ,,, Γ') -> type_local_env Σ Γ.
Admitted.

Lemma weakening Σ Γ Γ' :
  type_global_env Σ -> type_local_env Σ (Γ ,,, Γ') ->
  `(Σ ;;; Γ |-- t : T ->
    Σ ;;; Γ ,,, Γ' |-- lift0 #|Γ'| t : lift0 #|Γ'| T).
Proof.
  intros HΣ HΓΓ' * H.
  pose (weakening_rec Σ Γ [] Γ').
  forward t0; eauto.
  forward t0; eauto. now eapply type_local_env_app in HΓΓ'. 
Qed.

Lemma substitution Σ Γ n u U :
  type_global_env Σ -> type_local_env Σ Γ ->
  `(Σ ;;; Γ ,, vass n U |-- t : T -> Σ ;;; Γ |-- u : U ->
    Σ ;;; Γ |-- t {0 := u} : T {0 := u}).
Proof.
  intros HΣ HΓ * Ht Hu.
Admitted.
