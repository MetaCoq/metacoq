(* Distributed under the terms of the MIT license. *)

Section VarCheck.

  Section AllDefs.
  (* Predicate [p k n] where k is the number of binders we passed and n the index of the variable to check. *)
  Variable p : nat -> nat -> bool.

  Fixpoint all_vars k (t : term) : bool :=
  match t with
  | tRel i => p k i
  | tEvar ev args => List.forallb (all_vars k) args
  | tLambda _ T M | tProd _ T M => all_vars k T && all_vars (S k) M
  | tApp u v => all_vars k u && all_vars k v
  | tLetIn na b t b' => all_vars k b && all_vars k t && all_vars (S k) b'
  | tCase ind p c brs =>
    let brs' := List.forallb (test_snd (all_vars k)) brs in
    all_vars k p && all_vars k c && brs'
  | tProj p c => all_vars k c
  | tFix mfix idx =>
    let k' := List.length mfix + k in
    List.forallb (test_def (all_vars k) (all_vars k')) mfix
  | tCoFix mfix idx =>
    let k' := List.length mfix + k in
    List.forallb (test_def (all_vars k) (all_vars k')) mfix
  | tVar _ | tSort _ | tConst _ _ | tInd _ _ | tConstruct _ _ _ => true
  end.

  Lemma all_vars_true k t : (forall k n, p k n) -> all_vars k t.
  Proof.
    intros. revert k.
    induction t using PCUICInduction.term_forall_list_ind; simpl => //; solve_all.
    solve_all.
    all:try now rewrite ?IHt1 ?IHt2 ?IHt3.
    rewrite IHt1 IHt2. eapply All_forallb. solve_all.
    eapply All_forallb; solve_all. unfold test_def.
    now rewrite a b.
    eapply All_forallb; solve_all. unfold test_def.
    now rewrite a b.
  Qed.
  End AllDefs.

  Lemma all_vars_impl (p q : nat -> nat -> bool) k t : (forall k n, p k n -> q k n) -> 
    all_vars p k t -> all_vars q k t.
  Proof.
    intros. revert t k H0.
    induction t using PCUICInduction.term_forall_list_ind; simpl => //; solve_all.
    all:try solve_all.
    all:try now rewrite ?IHt1 ?IHt2 ?IHt3.
    apply /andP. move/andP: H0. intuition auto.
    apply /andP. move/andP: H0. intuition auto.
    apply /andP. move/andP: H0. intuition auto.
    apply /andP. move/andP: H1. intuition auto.
    apply /andP. move/andP: H0. intuition auto.
    apply /andP. move/andP: H0. intuition auto.
    apply /andP. move/andP: H1. intuition auto.
    solve_all.
    solve_all.
    unfold test_def in *.
    apply /andP. move/andP: b. intuition auto.
    solve_all.
    unfold test_def in *.
    apply /andP. move/andP: b. intuition auto.
  Qed.

  Lemma forallb_eq {A} (p q : A -> bool) l :
    All (fun x => p x = q x) l -> forallb p l = forallb q l.
  Proof.
    intros H; induction H; simpl; auto.
    now rewrite p0 IHAll.
  Qed.

  Lemma all_vars_eq_k (p q : nat -> nat -> bool) k k' t : (forall k n, p (k' + k) n = q k n) -> 
    all_vars p (k' + k) t = all_vars q k t.
  Proof.
    intros. revert t k.
    induction t using PCUICInduction.term_forall_list_ind; simpl => //.
    all:try solve_all.
    eapply forallb_eq. solve_all.
    rewrite IHt1 -(IHt2 (S k)). lia_f_equal.
    rewrite IHt1 -(IHt2 (S k)). lia_f_equal.
    rewrite IHt1 -(IHt2 k) -(IHt3 (S k)). lia_f_equal.
    rewrite IHt1 IHt2. bool_congr. eapply forallb_eq. solve_all.
    eapply forallb_eq. solve_all.
    unfold test_def.
    rewrite a -(b (#|m| + k)). lia_f_equal.
    eapply forallb_eq. solve_all.
    unfold test_def.
    rewrite a -(b (#|m| + k)). lia_f_equal.
  Qed.
 
  Lemma all_vars_lift (p : nat -> nat -> bool) n k t : 
    (forall n k' k, k <= n -> p k n -> p (k' + k) (k' + n)) ->
    (forall n k' k, n < k -> p k n -> p (k' + k) n) ->    
    all_vars p k t -> all_vars p (k + n) (lift n k t).
  Proof.
    intros. revert t n k H1.
    induction t using PCUICInduction.term_forall_list_ind; simpl => //; solve_all.
    all:try solve_all.
    - destruct (Nat.leb_spec k n).
      rewrite (Nat.add_comm k n0). now apply H.
      rewrite Nat.add_comm.
      now apply H0.
    - apply /andP. move/andP: H1. intuition eauto.
    - apply /andP. move/andP: H1. intuition eauto.
    - apply /andP. move/andP: H1. intuition eauto.
      move/andP: H2 => [P P']. apply/andP; intuition eauto.
    - apply /andP. move/andP: H1. intuition eauto.
    - apply /andP. move/andP: H1. intuition eauto.
      move/andP: H2 => [P P']. apply/andP; intuition eauto.
      solve_all.
    - len.
      destruct x; rewrite /map_def /test_def; simpl in *.
      apply /andP. move/andP: b; simpl. intuition eauto.
      replace (#|m| + (k + n0)) with ((k + #|m|) + n0) by lia.
      rewrite (Nat.add_comm #|m| k).
      eapply b0. rewrite Nat.add_comm //.
    - len.
      destruct x; rewrite /map_def /test_def; simpl in *.
      apply /andP. move/andP: b; simpl. intuition eauto.
      replace (#|m| + (k + n0)) with ((k + #|m|) + n0) by lia.
      rewrite (Nat.add_comm #|m| k).
      eapply b0. rewrite Nat.add_comm //.
  Qed.

  Lemma all_vars_lift'' (p : nat -> nat -> bool) n k i t : 
    (forall n k' k, k + i <= n -> p k n -> p k (k' + n)) ->
    all_vars p k t -> all_vars p k (lift n (k + i) t).
  Proof.
    intros Pp. revert t n k.
    induction t using PCUICInduction.term_forall_list_ind; simpl => //; solve_all.
    all:try solve_all.
    - destruct (Nat.leb_spec (k + i) n).
      now apply Pp. auto.
    - apply /andP. move/andP: H. intuition eauto.
    - apply /andP. move/andP: H. intuition eauto.
    - apply /andP. move/andP: H. intuition eauto.
      move/andP: H0 => [P P']. apply/andP; intuition eauto.
    - apply /andP. move/andP: H. intuition eauto.
    - apply /andP. move/andP: H. intuition eauto.
      move/andP: H0 => [P P']. apply/andP; intuition eauto.
      solve_all.
    - len.
      destruct x; rewrite /map_def /test_def; simpl in *.
      apply /andP. move/andP: b; simpl. intuition eauto.
      replace (#|m| + (k + i)) with ((k + #|m|) + i) by lia.
      rewrite (Nat.add_comm #|m| k).
      eapply b0. rewrite Nat.add_comm //.
    - len.
      destruct x; rewrite /map_def /test_def; simpl in *.
      apply /andP. move/andP: b; simpl. intuition eauto.
      replace (#|m| + (k + i)) with ((k + #|m|) + i) by lia.
      rewrite (Nat.add_comm #|m| k).
      eapply b0. rewrite Nat.add_comm //.
  Qed.

  Lemma all_vars_lift''' (p : nat -> nat -> bool) n k k' t : 
    (forall n k' n' k, n' <= n -> p k n -> p k (k' + n)) ->
    all_vars p k t -> all_vars p k (lift n k' t).
  Proof.
    intros. revert t n k H0.
    induction t using PCUICInduction.term_forall_list_ind; simpl => //; solve_all.
    all:try solve_all.
    - destruct (Nat.leb_spec k' n).
      eapply H. eauto. auto. auto.
  Admitted.
    (* - apply /andP. move/andP: H1. intuition eauto.
    - apply /andP. move/andP: H1. intuition eauto.
    - apply /andP. move/andP: H1. intuition eauto.
      move/andP: H2 => [P P']. apply/andP; intuition eauto.
    - apply /andP. move/andP: H1. intuition eauto.
    - apply /andP. move/andP: H1. intuition eauto.
      move/andP: H2 => [P P']. apply/andP; intuition eauto.
      solve_all.
    - len.
      destruct x; rewrite /map_def /test_def; simpl in *.
      apply /andP. move/andP: b; simpl. intuition eauto.
      replace (#|m| + (k + n0)) with ((k + #|m|) + n0) by lia.
      rewrite (Nat.add_comm #|m| k).
      eapply b0. rewrite Nat.add_comm //.
    - len.
      destruct x; rewrite /map_def /test_def; simpl in *.
      apply /andP. move/andP: b; simpl. intuition eauto.
      replace (#|m| + (k + n0)) with ((k + #|m|) + n0) by lia.
      rewrite (Nat.add_comm #|m| k).
      eapply b0. rewrite Nat.add_comm //.
  Qed. *)


  Lemma all_vars_lift' (p : nat -> nat -> bool) n k t : 
    (forall k n', p k (if k <=? n' then n + n' else n'))  ->
    all_vars p k (lift n k t).
  Proof.
    intros. revert t k.
    induction t using PCUICInduction.term_forall_list_ind; simpl => //; solve_all.
    all:try solve_all.
    all:try now rewrite ?IHt2 ?IHt2 ?IHt3. apply /andP; intuition eauto.
    rewrite IHt1 -(IHt2 (S k)); apply /andP; intuition auto.
    all:repeat (apply /andP; split; auto).
    rewrite forallb_map. solve_all.
    simpl; auto.
    len; simpl; auto.
    simpl; auto.
    len; simpl; auto.
  Qed.

  Lemma all_vars_subst (p : nat -> nat -> bool) k s t : 
    forallb (all_vars p 0) s ->
    (forall n k' k, k <= n -> p k n -> p (k' + k) (k' + n)) ->
    (forall n k' k, n < k -> p k n -> p (k' + k) n) ->    
    (forall n k, k <= n -> #|s| <= n - k -> p (#|s| + k) n -> p k (n - #|s|)) ->
    (forall n k, n < k -> p (#|s| + k) n -> p k n) ->    
    all_vars p (#|s| + k) t -> all_vars p k (subst s k t).
  Proof.
    intros Hs P1 P2 P3 P4. revert t k.
    induction t using PCUICInduction.term_forall_list_ind; simpl => //; solve_all.
    all:try solve_all.
    all:try now rewrite ?IHt1 ?IHt2 ?IHt3.
    - destruct (Nat.leb_spec k n).
      destruct nth_error eqn:eq.
      eapply nth_error_all in eq; eauto.
      simpl in eq. apply (all_vars_lift _ _ 0); auto.      
      eapply nth_error_None in eq.
      simpl. apply P3; eauto.
      simpl. now apply P4.
    - apply /andP. move/andP: H. intuition eauto.
      now specialize (IHt2 (S k)); rewrite Nat.add_succ_r in IHt2.
    - apply /andP. move/andP: H. intuition eauto.
      now specialize (IHt2 (S k)); rewrite Nat.add_succ_r in IHt2.
    - apply /andP. move/andP: H => [/andP [P P'] Q].
      split. apply/andP. intuition auto.
      now specialize (IHt3 (S k)); rewrite Nat.add_succ_r in IHt3.
    - apply /andP. move/andP: H. intuition eauto.
    - apply /andP. move/andP: H => [/andP [P P'] Q]. intuition eauto.
      apply/andP. intuition auto.
      solve_all.
    - destruct x; simpl in *. len.
      unfold map_def, test_def => /=.
      rewrite /test_def /= in b. move/andP: b => [bd bb].
      apply /andP; split; eauto. specialize (b0 (#|m| + k)).
      apply b0. red. rewrite -bb. lia_f_equal.
    - destruct x; simpl in *. len.
      unfold map_def, test_def => /=.
      rewrite /test_def /= in b. move/andP: b => [bd bb].
      apply /andP; split; eauto. specialize (b0 (#|m| + k)).
      apply b0. red. rewrite -bb. lia_f_equal.
  Qed.
End VarCheck.

Definition no_let Γ (k n : nat) := 
  (n <? k) || 
  match option_map decl_body (nth_error Γ (n - k)) with 
  | Some (Some _) => false
  | _ => true
  end.

Definition no_lets_from Γ k t :=
  all_vars (no_let Γ) k t.
  
Definition no_lets_ctx_from Γ k ctx :=
  Alli (fun i => test_decl (no_lets_from Γ (i + k))) 0 (List.rev ctx). 

Lemma no_lets_from_nil : forall k n, no_lets_from [] k n.
Proof.
  intros k n; rewrite /no_lets_from; apply all_vars_true.
  intros k' n'; rewrite /no_let.
  destruct Nat.ltb; simpl => //.
  rewrite nth_error_nil //.
Qed.

Lemma no_lets_ctx_from_nil k Δ : no_lets_ctx_from [] k Δ.
Proof.
  red.
  generalize 0.
  induction Δ using rev_ind; [constructor|].
  rewrite List.rev_app_distr. simpl. constructor.
  simpl. rewrite /test_decl. rewrite !no_lets_from_nil.
  destruct x as [na [?|] ?]; simpl; auto.
  now rewrite no_lets_from_nil.
  apply IHΔ.
Qed.


Lemma no_lets_from_ext Γ n  k Γ' t : 
  assumption_context Γ' ->
  no_lets_from Γ (n + (#|Γ'| + k)) t ->
  no_lets_from (Γ ,,, Γ') (n + k) t.
Proof.
  intros ass. unfold no_lets_from in *.
  intros allv.
  replace (n + (#|Γ'| + k)) with (#|Γ'| + (n + k)) in allv by lia.
  rewrite -(all_vars_eq_k (fun k' n => no_let Γ k' n) _ _ #|Γ'|) //.
  intros. unfold no_let.
  destruct (Nat.ltb_spec n0 (#|Γ'| + k0)) => /=.
  destruct (Nat.ltb_spec n0 k0) => /= //.
  rewrite nth_error_app_lt. lia.
  destruct nth_error eqn:E => //.
  eapply PCUICParallelReductionConfluence.nth_error_assumption_context in ass; eauto.
  simpl. now rewrite ass.
  destruct (Nat.ltb_spec n0 k0) => /= //.
  lia.
  rewrite nth_error_app_ge. lia.
  now replace (n0 - k0 - #|Γ'|) with (n0 - (#|Γ'| + k0)) by lia.
Qed.

Lemma no_lets_from_ext_left Γ k Γ' t : 
  assumption_context Γ' ->
  no_lets_from Γ k t ->
  no_lets_from (Γ' ,,, Γ) k t.
Proof.
  intros ass. unfold no_lets_from in *.
  eapply all_vars_impl.
  intros k' n. unfold no_let.
  elim: Nat.ltb_spec => /= // Hk'.
  destruct nth_error eqn:eq => /= //;
  destruct (nth_error (Γ' ,,, Γ)) eqn:eq' => /= //.
  rewrite nth_error_app_lt in eq'. eapply nth_error_Some_length in eq; lia.
  now rewrite eq in eq'; noconf eq'.
  move=> _. eapply nth_error_None in eq.
  rewrite nth_error_app_ge in eq' => //.
  eapply nth_error_assumption_context in eq'; eauto.
  now rewrite eq'.
Qed.

Lemma no_lets_ctx_from_ext Γ k Γ' Δ : 
  assumption_context Γ' ->
  no_lets_ctx_from Γ (#|Γ'| + k) Δ ->
  no_lets_ctx_from (Γ ,,, Γ') k Δ.
Proof.
  rewrite /no_lets_ctx_from.
  intros ass a. eapply Alli_impl; eauto.
  simpl; intros.
  unfold test_decl in *.
  apply /andP. move/andP: H; intuition auto.
  now eapply no_lets_from_ext.
  destruct (decl_body x); simpl in * => //.
  now eapply no_lets_from_ext.
Qed.

Lemma no_lets_from_lift Γ k n t : 
  no_lets_from Γ k t -> no_lets_from Γ (k + n) (lift n k t).
Proof.
  intros Hs.
  apply all_vars_lift; auto.
  - clear; intros n k' k.
    unfold no_let.
    destruct (Nat.ltb_spec n k) => /= //; try lia.
    move=> _ Hb.
    destruct (Nat.ltb_spec (k' + n) (k' + k)) => /= //; try lia.
    now replace (k' + n - (k' + k)) with (n - k) by lia.
  - clear. intros n k' k.
    intros Hn _; unfold no_let.
    destruct (Nat.ltb_spec n (k' + k)) => /= //; try lia.
Qed.

Lemma no_lets_from_subst Γ s n t : 
  forallb (no_lets_from Γ 0) s ->
  no_lets_from Γ (#|s| + n) t -> no_lets_from Γ n (subst s n t).
Proof.
  intros Hs.
  apply all_vars_subst; auto.
  - clear; intros n k' k.
    unfold no_let.
    destruct (Nat.ltb_spec n k) => /= //; try lia.
    move=> _ Hb.
    destruct (Nat.ltb_spec (k' + n) (k' + k)) => /= //; try lia.
    now replace (k' + n - (k' + k)) with (n - k) by lia.
  - clear. intros n k' k.
    intros Hn _; unfold no_let.
    destruct (Nat.ltb_spec n (k' + k)) => /= //; try lia.
  - clear; intros n k.
    intros kn snk. unfold no_let.
    destruct (Nat.ltb_spec n (#|s| + k)) => /= //; try lia.
    destruct (Nat.ltb_spec (n - #|s|) k) => /= //; try lia.
    now replace (n - (#|s| + k)) with (n - #|s| - k) by lia.
  - clear; intros n k.
    intros nk. unfold no_let.
    destruct (Nat.ltb_spec n (#|s| + k)) => /= //; try lia.
    destruct (Nat.ltb_spec n k) => /= //; try lia.
Qed.

Lemma no_lets_ctx_from_subst Γ k s Δ : 
  forallb (no_lets_from Γ 0) s ->
  no_lets_ctx_from Γ (#|s| + k) Δ ->
  no_lets_ctx_from Γ k (subst_context s k Δ).
Proof.
  intros hs.
  unfold no_lets_ctx_from.
  rewrite -subst_telescope_subst_context.
  rewrite /subst_telescope. intros a.
  eapply (fst (Alli_mapi _ _ _)).
  eapply Alli_impl; eauto.
  simpl; intros n x.
  rewrite test_decl_map_decl.
  apply test_decl_impl => t.
  clear -hs.
  replace (n + (#|s| + k)) with (#|s| + (n + k)) by lia.
  rewrite (Nat.add_comm k n).
  generalize (n+k). intros n'. 
  now eapply no_lets_from_subst.
Qed.

Lemma no_lets_from_lift_ctx Γ n k t : 
  #|Γ| = n ->
  no_lets_from Γ k (lift n k t).
Proof.
  intros Hn. eapply all_vars_lift'.
  intros. unfold no_let.
  elim: Nat.leb_spec => // Hs /=.
  elim: Nat.ltb_spec => // /= _.
  subst n.
  destruct nth_error eqn:eq.
  eapply nth_error_Some_length in eq. lia.
  now simpl.
  elim: Nat.ltb_spec => // Hs' /=. lia.
Qed.  


Lemma expand_lets_no_let Γ k t : 
  no_lets_from (smash_context [] Γ) k (expand_lets_k Γ k t).
Proof.
  unfold expand_lets_k.
  eapply no_lets_from_subst.
  - induction Γ as [|[na [b|] ty] Γ'] using ctx_length_rev_ind; simpl; auto.
    rewrite smash_context_app_def.
    rewrite extended_subst_app /= !subst_empty lift0_id lift0_context.
    rewrite forallb_app. apply /andP. split; auto.
    2:{ simpl. rewrite andb_true_r.
        apply no_lets_from_lift_ctx.
        now  len. }
    eapply H. now len.
    rewrite smash_context_app_ass /=.
    rewrite extended_subst_app /= subst_context_lift_id forallb_app /= andb_true_r.
    apply/andP; split. specialize (H Γ' ltac:(reflexivity)).
    solve_all. eapply no_lets_from_ext_left in H. eapply H. repeat constructor.
    unfold no_let.
    elim: Nat.ltb_spec => // /= _.
    destruct nth_error eqn:eq => //.
    eapply nth_error_assumption_context in eq => /=. now rewrite eq.
    eapply assumption_context_app_inv. apply smash_context_assumption_context; constructor.
    repeat constructor.
  - len. rewrite Nat.add_comm.
    eapply no_lets_from_lift_ctx. now len.
Qed.

Lemma expand_lets_ctx_no_let Γ k Δ : 
  no_lets_ctx_from (smash_context [] Γ) k (expand_lets_k_ctx Γ k Δ).
Proof.
  induction Γ in k, Δ |- *.
  - unfold expand_lets_k_ctx.
    simpl context_assumptions. rewrite ?lift0_context. simpl; rewrite !subst0_context.
    apply no_lets_ctx_from_nil.
    
  - destruct a as [na [b|] ty].
    rewrite /expand_lets_k_ctx /=.
    len.
    rewrite (subst_app_context_gen [_]). simpl.
    rewrite ->( subst_app_context_gen [subst0 (extended_subst Γ 0) (lift  (context_assumptions Γ) #|Γ| b)] (extended_subst Γ 0)).
    simpl.
    rewrite (Nat.add_succ_r k #|Γ|).
    rewrite /expand_lets_k_ctx in IHΓ.
    specialize (IHΓ (S k)).
    eapply (no_lets_ctx_from_subst _ _ [_] _) in IHΓ.
    rewrite Nat.add_1_r.
    eapply IHΓ. simpl.
    now rewrite expand_lets_no_let.

    simpl.    
    rewrite smash_context_acc /= /map_decl /=.
    rewrite ->( subst_app_context_gen [tRel 0] (extended_subst Γ 1)).
    simpl.
    rewrite (lift_context_add 1 _).
    rewrite (lift_extended_subst _ 1).
    epose proof  (distr_lift_subst_context_rec 1 0 (extended_subst Γ 0) _ (k + 1)).
    autorewrite with len in H. 
    replace (#|Γ| + (k + 1)) with (k + S #|Γ|) in H by lia.
    rewrite <- H. clear H. rewrite Nat.add_1_r.
    rewrite subst_context_lift_id.
    rewrite /expand_lets_k_ctx in IHΓ.
    rewrite Nat.add_succ_r.
    specialize (IHΓ (S k) Δ).
    unshelve eapply (no_lets_ctx_from_ext _ k [_] _ _) in IHΓ. 3:eapply IHΓ.
    repeat constructor.
Qed.

Lemma subst_context_no_lets_from Γ k Δ :
  no_lets_ctx_from (smash_context [] Γ) 0 Δ ->
  no_lets_ctx_from Δ k (subst_context (List.rev (to_extended_list_k Γ k)) 0 Δ).
Proof.
Admitted.

Lemma no_lets_from_lift' Γ k n t : 
  no_lets_from Γ k t -> no_lets_from Γ k (lift n (k + #|Γ|) t).
Proof.
  eapply all_vars_lift''. clear; unfold no_let. intros n k' k le.
  destruct (Nat.ltb_spec n k) => /= //; try lia.
  elim: Nat.ltb_spec => /= //; try lia.
  move=> lek.
  destruct nth_error eqn:eq. eapply nth_error_Some_length in eq. lia.
  simpl.
  elim eq': nth_error.
  eapply nth_error_Some_length in eq' => //. lia.
  simpl. auto.
Qed.

(*


Lemma no_lets_subst_all_rels Γ k k' Δ :
  no_lets_ctx_from Γ k' Δ ->
  closedn_ctx (#|Γ| + k') Δ ->
  subst_context (all_rels Γ k 0) k' Δ = Δ.
Proof.
  intros nolet cl.
  revert k k' nolet cl.
  induction Δ using rev_ind; simpl; auto; intros.
  rewrite subst_context_app. unfold app_context; f_equal.
  simpl. rewrite (IHΔ k (S k')). admit. admit.
  auto.
  rewrite subst_context_snoc /= subst_context_nil /= /snoc.
  f_equal.
  destruct x as [na [b|] ty]; rewrite /subst_decl /map_decl /=.
  f_equal. f_equal.
  rewrite closedn_ctx_app in cl. move/andP: cl => [clb clΓ].
  simpl in clb. rewrite /id andb_true_r /closed_decl /= in clb.
  move/andP: clb =>  [clb clty].
Admitted.


Lemma expand_lets_subst_lift Γ k k' Δ :
  no_lets_ctx_from (smash_context [] Γ) k Δ ->
  no_lets_ctx_from Γ (k + k')  (subst_context (List.rev (to_extended_list_k Γ k')) 0 Δ).
Proof.
Admitted.

*)
