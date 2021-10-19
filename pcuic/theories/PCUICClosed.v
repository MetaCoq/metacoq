(* Distributed under the terms of the MIT license. *)
From Coq Require Import Morphisms. 
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICInduction
     PCUICLiftSubst PCUICUnivSubst PCUICContextRelation PCUICTyping 
     PCUICWeakeningEnv PCUICSigmaCalculus.

Require Import ssreflect ssrbool.
From Equations Require Import Equations.

(** * Lemmas about the [closedn] predicate *)

Lemma subst_instance_assumptions u ctx :
  context_assumptions (subst_instance u ctx) = context_assumptions ctx.
Proof.
  induction ctx; cbnr.
  destruct (decl_body a); cbn; now rewrite IHctx.
Qed.
#[global]
Hint Rewrite subst_instance_assumptions : len.


Lemma lift_decl_closed n k d : closed_decl k d -> lift_decl n k d = d.
Proof.
  case: d => na [body|] ty; rewrite /test_decl /lift_decl /map_decl /=; unf_term.
  - move/andP => [cb cty]. now rewrite !lift_closed //.
  - move=> cty; now rewrite !lift_closed //.
Qed.

Lemma closed_decl_upwards k d : closed_decl k d -> forall k', k <= k' -> closed_decl k' d.
Proof.
  case: d => na [body|] ty; rewrite /test_decl /=.
  - move/andP => /= [cb cty] k' lek'. do 2 rewrite (@closed_upwards k) //.
  - move=> cty k' lek'; rewrite (@closed_upwards k) //.
Qed.

Lemma alli_fold_context_k (p : nat -> context_decl -> bool) ctx f : 
  (forall i d, p i d -> map_decl (f i) d = d) ->
  alli p 0 (List.rev ctx) ->
  fold_context_k f ctx = ctx.
Proof.
  intros Hf.
  rewrite /fold_context_k /mapi.
  generalize 0.
  induction ctx using rev_ind; simpl; intros n; auto.
  rewrite List.rev_app_distr /=.
  move/andP=> [] Hc Hd.
  rewrite Hf //; len. f_equal.
  now apply IHctx.
Qed.

Lemma closedn_ctx_cons n d Γ : closedn_ctx n (d :: Γ) = closedn_ctx n Γ && closed_decl (n + #|Γ|) d.
Proof.
  rewrite /=. rewrite Nat.add_comm. bool_congr.
Qed.

Lemma test_context_k_app p n Γ Γ' :
  test_context_k p n (Γ ,,, Γ') =
  test_context_k p n Γ && test_context_k p (n + #|Γ|) Γ'.
Proof.
  rewrite /app_context /= !test_context_k_eq List.rev_app_distr alli_app /=. f_equal.
  rewrite List.rev_length.
  rewrite Nat.add_0_r alli_shift.
  now setoid_rewrite Nat.add_assoc.
Qed.

Lemma closedn_ctx_app n Γ Γ' :
  closedn_ctx n (Γ ,,, Γ') =
  closedn_ctx n Γ && closedn_ctx (n + #|Γ|) Γ'.
Proof.
  now rewrite test_context_k_app.
Qed.

Lemma closed_ctx_lift n k ctx : closedn_ctx k ctx -> lift_context n k ctx = ctx.
Proof.
  induction ctx in n, k |- *; auto.
  rewrite closedn_ctx_cons lift_context_snoc.
  simpl.
  move/andb_and => /= [Hctx Hd].
  f_equal. rewrite IHctx // lift_decl_closed // Nat.add_comm //.
Qed.

Lemma map_decl_closed_ext (f : term -> term) g k (d : context_decl) : closed_decl k d -> 
  (forall x, closedn k x -> f x = g x) -> 
  map_decl f d = map_decl g d.
Proof.
  destruct d as [? [?|] ?] => /= cl Hfg;
  unfold map_decl; simpl; f_equal.
  rewrite Hfg => //. unfold closed_decl in cl.
  simpl in cl. now move/andP: cl => []. 
  move/andP: cl => [cl cl']. now rewrite Hfg.
  now rewrite Hfg.
Qed.

Lemma test_decl_map_decl (p : term -> bool) (f : term -> term) d :
  test_decl p (map_decl f d) = test_decl (p ∘ f) d.
Proof.
  rewrite /test_decl /map_decl; destruct d; simpl.
  now destruct decl_body.
Qed.

Lemma plus_minus' n m : n + m - m = n.
Proof. lia. Qed.

Lemma test_context_k_mapi (p : nat -> term -> bool) k (f : nat -> term -> term) ctx :
  test_context_k p k (mapi_context f ctx) =
  test_context_k (fun i t => p i (f (i - k) t)) k ctx.
Proof.
  induction ctx; simpl; auto.
  rewrite IHctx. f_equal. rewrite test_decl_map_decl.
  len. now setoid_rewrite plus_minus'.
Qed.
#[global]
Hint Rewrite test_context_k_mapi : map.

Lemma test_context_k_map (p : nat -> term -> bool) k (f : term -> term) ctx :
  test_context_k p k (map_context f ctx) =
  test_context_k (fun i t => p i (f t)) k ctx.
Proof.
  induction ctx; simpl; auto.
  rewrite IHctx. f_equal. rewrite test_decl_map_decl.
  now len.
Qed.
#[global]
Hint Rewrite test_context_k_map : map.

Lemma closedn_lift n k k' t : closedn k t -> closedn (k + n) (lift n k' t).
Proof.
  revert k.
  induction t in n, k' |- * using term_forall_list_ind; intros;
    simpl in *; rewrite -> ?andb_and in *;
    autorewrite with map;
    simpl closed in *; solve_all;
    unfold test_def, test_snd, test_predicate_k, test_branch_k in *;
      try solve [simpl lift; simpl closed; f_equal; auto; repeat (rtoProp; simpl in *; solve_all)]; try easy.

  - elim (Nat.leb_spec k' n0); intros. simpl.
    elim (Nat.ltb_spec); auto. apply Nat.ltb_lt in H. lia.
    simpl. elim (Nat.ltb_spec); auto. intros.
    apply Nat.ltb_lt in H. lia.
Qed.

Lemma closedn_lift_inv n k k' t : k <= k' ->
                                   closedn (k' + n) (lift n k t) ->
                                   closedn k' t.
Proof.
  induction t in n, k, k' |- * using term_forall_list_ind; intros;
    simpl in *;
    autorewrite with map;
    simpl closed in *; repeat (rtoProp; simpl in *; solve_all); try change_Sk;
    unfold test_def, test_predicate_k, test_branch_k, shiftf in *; 
    rewrite -> ?map_length, ?Nat.add_assoc in *;
    simpl in *; eauto 2 with all.

  - revert H0.
    elim (Nat.leb_spec k n0); intros. simpl in *.
    elim (Nat.ltb_spec); auto. apply Nat.ltb_lt in H1. intros. lia.
    revert H1. simpl. elim (Nat.ltb_spec); auto. intros. apply Nat.ltb_lt. lia.
  - specialize (IHt2 n (S k) (S k')). eauto with all.
  - specialize (IHt2 n (S k) (S k')). eauto with all.
  - specialize (IHt3 n (S k) (S k')). eauto with all.
  - rtoProp. solve_all; unfold shiftf in *.
    * now len in H6.
    * eapply (i n (#|pcontext p| + k)). lia.
      now len in H3.
  - rtoProp. solve_all; unfold shiftf in *.
    * now len in H7.
    * eapply (b0 n (#|bcontext x| + k)); eauto; try lia.
  - rtoProp. solve_all. specialize (b0 n (#|m| + k) (#|m| + k')).
    now len in H1.
  - rtoProp. solve_all. specialize (b0 n (#|m| + k) (#|m| + k')). eauto with all.
Qed.

Lemma closedn_mkApps k f u:
  closedn k (mkApps f u) = closedn k f && forallb (closedn k) u.
Proof.
  induction u in k, f |- *; simpl; auto.
  - now rewrite andb_true_r.
  - now rewrite IHu /= andb_assoc.
Qed.

#[global] Remove Hints absurd_eq_true trans_eq_bool f_equal2_nat f_equal_nat : core.

Lemma closedn_subst_eq s k k' t :
  forallb (closedn k) s -> 
  closedn (k + k' + #|s|) t =
  closedn (k + k') (subst s k' t).
Proof.
  intros Hs. solve_all. revert Hs.
  induction t in k' |- * using term_forall_list_ind; intros;
    simpl in *;
    autorewrite with map => //;
    simpl closed in *; try change_Sk;
    unfold test_def, test_branch_k, test_predicate_k in *; simpl in *;
    solve_all.

  - elim (Nat.leb_spec k' n); intros. simpl.
    destruct nth_error eqn:Heq.
    -- rewrite closedn_lift.
       now eapply nth_error_all in Heq; simpl; eauto; simpl in *.
       eapply nth_error_Some_length in Heq.
       eapply Nat.ltb_lt. lia.
    -- simpl. elim (Nat.ltb_spec); auto. intros.
       apply nth_error_None in Heq. symmetry. apply Nat.ltb_lt. lia.
       apply nth_error_None in Heq. intros. symmetry. eapply Nat.ltb_nlt.
       intros H'. lia.
    -- simpl.
      elim: Nat.ltb_spec; symmetry. apply Nat.ltb_lt. lia.
      apply Nat.ltb_nlt. intro. lia.

  - specialize (IHt2 (S k')).
    rewrite <- Nat.add_succ_comm in IHt2.
    rewrite IHt1 // IHt2 //.
  - specialize (IHt2 (S k')).
    rewrite <- Nat.add_succ_comm in IHt2.
    rewrite IHt1 // IHt2 //.
  - specialize (IHt3 (S k')).
    rewrite <- Nat.add_succ_comm in IHt3.
    rewrite IHt1 // IHt2 // IHt3 //.
  - rewrite IHt //.
    f_equal; [|solve_all;f_equal]. f_equal. f_equal. f_equal.
    all:len; solve_all.
    * specialize (e (#|pcontext p| + k')).
      now rewrite Nat.add_assoc (Nat.add_comm k) in e.
    * specialize (b (#|bcontext x| + k')).
      now rewrite Nat.add_assoc (Nat.add_comm k) in b.
  - rewrite a //.
    specialize (b (#|m| + k')).
    rewrite Nat.add_assoc in b.
    rewrite (Nat.add_comm k #|m|) in b. 
    rewrite b //.
  - rewrite a //.
    specialize (b (#|m| + k')).
    rewrite Nat.add_assoc in b.
    rewrite (Nat.add_comm k #|m|) in b. 
    rewrite b //.
Qed.

Lemma closedn_subst_eq' s k k' t :
  closedn (k + k') (subst s k' t) ->
  closedn (k + k' + #|s|) t.
Proof.
  intros Hs. solve_all. revert Hs.
  induction t in k' |- * using term_forall_list_ind; intros;
    simpl in *;
    autorewrite with map;
    simpl closed in *; repeat (rtoProp; f_equal; solve_all);  try change_Sk;
    unfold test_def, map_branch, test_branch, test_predicate in *; simpl in *; eauto 4 with all.

  - move: Hs; elim (Nat.leb_spec k' n); intros. simpl.
    destruct nth_error eqn:Heq.
    -- eapply Nat.ltb_lt.
       eapply nth_error_Some_length in Heq. lia.
    -- simpl. simpl in Hs.
       apply nth_error_None in Heq. apply Nat.ltb_lt.
       apply Nat.ltb_lt in Hs; lia.
    -- simpl in Hs. eapply Nat.ltb_lt in Hs.
       apply Nat.ltb_lt. lia.

  - specialize (IHt2 (S k')).
    rewrite <- Nat.add_succ_comm in IHt2. eauto.
  - specialize (IHt2 (S k')).
    rewrite <- Nat.add_succ_comm in IHt2. eauto.
  - specialize (IHt3 (S k')).
    rewrite <- Nat.add_succ_comm in IHt3. eauto.
  - move/andb_and: H => [hpar hret].
    rewrite !Nat.add_assoc in hret.
    specialize (i (#|pcontext p| + k')).
    rewrite Nat.add_assoc (Nat.add_comm k) in i.
    simpl in *.  unfold test_predicate_k. simpl. solve_all.
    * now len in H5.
  - unfold test_branch_k in *. rtoProp; solve_all.
    * cbn in H4. now len in H4.
    * specialize (b0 (#|bcontext x| + k')).
      rewrite Nat.add_assoc (Nat.add_comm k) in b0.
      simpl in H2. len in H2. rewrite !Nat.add_assoc in H2. eauto.
  - move/andP: b => [hty hbod]. rewrite a0 //.
    specialize (b0 (#|m| + k')).
    rewrite Nat.add_assoc (Nat.add_comm k #|m|) in b0. 
    rewrite b0 //. now autorewrite with len in hbod.
  - move/andP: b => [hty hbod]. rewrite a0 //.
    specialize (b0 (#|m| + k')).
    rewrite Nat.add_assoc (Nat.add_comm k #|m|) in b0. 
    rewrite b0 //. now autorewrite with len in hbod.
Qed.

Lemma closedn_subst s k k' t :
  forallb (closedn k) s -> 
  closedn (k + k' + #|s|) t ->
  closedn (k + k') (subst s k' t).
Proof.
  intros; now rewrite -closedn_subst_eq.
Qed.

Lemma closedn_subst0 s k t :
  forallb (closedn k) s -> closedn (k + #|s|) t ->
  closedn k (subst0 s t).
Proof.
  intros.
  generalize (closedn_subst s k 0 t H).
  rewrite Nat.add_0_r. eauto.
Qed.

Lemma subst_closedn s k t : closedn k t -> subst s k t = t.
Proof.
  intros Hcl.
  pose proof (simpl_subst_rec t s 0 k k).
  intros. assert(Hl:=lift_closed (#|s| + 0) _ _ Hcl).
  do 2 (forward H; auto). rewrite Hl in H.
  rewrite H. now apply lift_closed.
Qed.

Lemma closedn_subst_instance k t u :
  closedn k (subst_instance u t) = closedn k t.
Proof.
  revert k.
  induction t in |- * using term_forall_list_ind; intros;
    simpl in *; rewrite -> ?andb_and in *;
    autorewrite with map; len;
    unfold test_predicate_k, test_branch_k in *; solve_all.

  - unfold test_predicate_k, map_predicate; simpl.
    f_equal. f_equal. f_equal. f_equal.
    all: len; solve_all.
  - unfold test_def, map_def. simpl.
    do 3 (f_equal; intuition eauto).
  - unfold test_def, map_def. simpl.
    do 3 (f_equal; intuition eauto).
Qed.

Lemma closed_map_subst_instance n u l : 
  forallb (closedn n) (map (subst_instance u) l) = 
  forallb (closedn n) l.
Proof.
  induction l; simpl; auto.
  now rewrite closedn_subst_instance IHl.
Qed.

Lemma closedn_ctx_tip n d : closedn_ctx n [d] = closed_decl n d.
Proof. now rewrite test_context_k_eq /= andb_true_r Nat.add_0_r. Qed.

Lemma closedn_All_local_closed:
  forall (cf : checker_flags) (Σ : global_env_ext) (Γ : context) (ctx : list context_decl)
         (wfΓ' : wf_local Σ (Γ ,,, ctx)),
    All_local_env_over typing
    (fun (Σ0 : global_env_ext) (Γ0 : context) (_ : wf_local Σ0 Γ0) (t T : term) (_ : Σ0;;; Γ0 |- t : T) =>
       closedn #|Γ0| t && closedn #|Γ0| T) Σ (Γ ,,, ctx) wfΓ' ->
    closedn_ctx 0 Γ && closedn_ctx #|Γ| ctx.
Proof.
  intros cf Σ Γ ctx wfΓ' al.
  remember (Γ ,,, ctx) as Γ'. revert Γ' wfΓ' ctx HeqΓ' al.
  induction Γ. simpl. intros. subst. unfold app_context in *. rewrite app_nil_r in wfΓ' al.
  induction al; try constructor;
  rewrite closedn_ctx_cons /=; cbn.
  move/andP: p => [] /= -> _. now rewrite IHal.
  now rewrite IHal /= /test_decl /=.
  intros.
  unfold app_context in *. subst Γ'.
  specialize (IHΓ (ctx ++ a :: Γ) wfΓ' (ctx ++ [a])).
  rewrite -app_assoc in IHΓ. specialize (IHΓ eq_refl al).
  rewrite closedn_ctx_app /= Nat.add_1_r andb_assoc in IHΓ.
  now rewrite closedn_ctx_cons /=.
Qed.

Lemma closedn_mkProd_or_LetIn n d T :
    closed_decl n d && closedn (S n) T = closedn n (mkProd_or_LetIn d T).
Proof.
  destruct d as [na [b|] ty]; reflexivity.
Qed.

Lemma closedn_mkLambda_or_LetIn (Γ : context) d T :
    closed_decl #|Γ| d ->
    closedn (S #|Γ|) T -> closedn #|Γ| (mkLambda_or_LetIn d T).
Proof.
  destruct d as [na [b|] ty]; simpl in *. unfold closed_decl.
  simpl. now move/andP => [] /= -> ->.
  simpl. now move/andP => [] /= _ -> ->.
Qed.

Lemma closedn_it_mkProd_or_LetIn n (ctx : list context_decl) T :
  closedn n (it_mkProd_or_LetIn ctx T) = 
  closedn_ctx n ctx && closedn (n + #|ctx|) T.
Proof.
  induction ctx in n, T |- *. simpl.
  - now rewrite Nat.add_0_r.
  - rewrite closedn_ctx_cons.
    rewrite (IHctx n (mkProd_or_LetIn a T)) /= -closedn_mkProd_or_LetIn.
    now rewrite // plus_n_Sm andb_assoc.
Qed.

Lemma closedn_it_mkLambda_or_LetIn
      (Γ : context) (ctx : list context_decl) T :
    closedn_ctx #|Γ| ctx ->
    closedn (#|Γ| + #|ctx|) T -> closedn #|Γ| (it_mkLambda_or_LetIn ctx T).
Proof.
  induction ctx in Γ, T |- *. simpl.
  - now rewrite Nat.add_0_r.
  - rewrite closedn_ctx_cons; move/andP => [] cctx ca cT.
    apply (IHctx Γ (mkLambda_or_LetIn a T) cctx).
    simpl in cT. rewrite <- app_length.
    eapply closedn_mkLambda_or_LetIn;
      now rewrite app_length // plus_n_Sm.
Qed.

Lemma type_local_ctx_All_local_env {cf:checker_flags} P Σ Γ Δ s : 
  All_local_env (lift_typing P Σ) Γ ->
  type_local_ctx (lift_typing P) Σ Γ Δ s ->
  All_local_env (lift_typing P Σ) (Γ ,,, Δ).
Proof.
  induction Δ; simpl; auto.
  destruct a as [na [b|] ty];
  intros wfΓ wfctx; constructor; intuition auto.
   exists s; auto.
Qed.

Lemma sorts_local_ctx_All_local_env {cf:checker_flags} P Σ Γ Δ s : 
  All_local_env (lift_typing P Σ) Γ ->
  sorts_local_ctx (lift_typing P) Σ Γ Δ s ->
  All_local_env (lift_typing P Σ) (Γ ,,, Δ).
Proof.
  induction Δ in s |- *; simpl; eauto.
  destruct a as [na [b|] ty];
  intros wfΓ wfctx; constructor; intuition eauto.
  destruct s => //. destruct wfctx; eauto.
  destruct s => //. destruct wfctx. exists t; auto.
Qed.

Definition Pclosed :=
  (fun (_ : global_env_ext) (Γ : context) (t T : term) =>
           closedn #|Γ| t && closedn #|Γ| T).

Lemma type_local_ctx_Pclosed Σ Γ Δ s :
  type_local_ctx (lift_typing Pclosed) Σ Γ Δ s ->
  Alli (fun i d => closed_decl (#|Γ| + i) d) 0 (List.rev Δ).
Proof.
  induction Δ; simpl; auto; try constructor.  
  destruct a as [? [] ?]; intuition auto.
  - apply Alli_app_inv; auto. constructor. simpl.
    rewrite List.rev_length. 2:constructor.
    unfold closed_decl. unfold Pclosed in b0. simpl.
    rewrite app_context_length in b0. now rewrite Nat.add_comm.
  - apply Alli_app_inv; auto. constructor. simpl.
    rewrite List.rev_length. 2:constructor.
    unfold closed_decl. unfold Pclosed in b. simpl.
    rewrite app_context_length in b. rewrite Nat.add_comm.
    now rewrite andb_true_r in b.
Qed.

Lemma sorts_local_ctx_Pclosed Σ Γ Δ s :
  sorts_local_ctx (lift_typing Pclosed) Σ Γ Δ s ->
  Alli (fun i d => closed_decl (#|Γ| + i) d) 0 (List.rev Δ).
Proof.
  induction Δ in s |- *; simpl; auto; try constructor.  
  destruct a as [? [] ?]; intuition auto.
  - apply Alli_app_inv; eauto. constructor. simpl.
    rewrite List.rev_length. 2:constructor.
    unfold closed_decl. unfold Pclosed in b0. simpl.
    rewrite app_context_length in b0. now rewrite Nat.add_comm.
  - destruct s as [|u us]; auto. destruct X as [X b].
    apply Alli_app_inv; eauto. constructor. simpl.
    rewrite List.rev_length. 2:constructor.
    unfold closed_decl. unfold Pclosed in b. simpl.
    rewrite app_context_length in b. rewrite Nat.add_comm.
    now rewrite andb_true_r in b.
Qed.

Lemma All_local_env_Pclosed Σ Γ :
  All_local_env ( lift_typing Pclosed Σ) Γ ->
  Alli (fun i d => closed_decl i d) 0 (List.rev Γ).
Proof.
  induction Γ; simpl; auto; try constructor.  
  intros all; depelim all; intuition auto.
  - apply Alli_app_inv; auto. constructor. simpl.
    rewrite List.rev_length. 2:constructor.
    unfold closed_decl. unfold Pclosed in l. simpl. red in l.
    destruct l as [s H].
    now rewrite andb_true_r in H.
  - apply Alli_app_inv; auto. constructor. simpl.
    rewrite List.rev_length. 2:constructor.
    unfold closed_decl. unfold Pclosed, lift_typing in *. now simpl.
Qed.

Lemma closed_subst_context n (Δ Δ' : context) t :
  closedn (n + #|Δ|) t ->
  Alli (fun i d => closed_decl (n + S #|Δ| + i) d) 0 (List.rev Δ') -> 
  Alli (fun i d => closed_decl (n + #|Δ| + i) d) 0 (List.rev (subst_context [t] 0 Δ')).
Proof.
  induction Δ' in Δ |- *.
  intros. simpl. auto. constructor.
  destruct a as [? [] ?]; simpl.
  - intros. eapply Alli_app in X as [X X'].
    rewrite subst_context_snoc. simpl. eapply Alli_app_inv.
    eapply IHΔ'; eauto. constructor; [|constructor].
    simpl. 
    rewrite /test_decl /map_decl /= Nat.add_0_r List.rev_length subst_context_length.
    inv X'. unfold test_decl in H0. simpl in H0.
    rewrite List.rev_length Nat.add_0_r in H0.
    move/andP: H0 => [Hl Hr];
    rewrite !closedn_subst /= ?H //; eapply closed_upwards; eauto; try lia.
  - intros. eapply Alli_app in X as [X X'].
    rewrite subst_context_snoc. simpl. eapply Alli_app_inv.
    eapply IHΔ'; eauto. constructor; [|constructor].
    simpl. 
    rewrite /test_decl /map_decl /= Nat.add_0_r List.rev_length subst_context_length.
    inv X'. unfold test_decl in H0. simpl in H0.
    rewrite List.rev_length Nat.add_0_r in H0.
    rewrite !closedn_subst /= ?H //; eapply closed_upwards; eauto; try lia.
Qed.

Lemma closed_smash_context_gen n (Δ Δ' : context) :
  Alli (fun i d => closed_decl (n + i) d) 0 (List.rev Δ) -> 
  Alli (fun i d => closed_decl (n + #|Δ| + i) d) 0 (List.rev Δ') -> 
  Alli (fun i d => closed_decl (n + i) d) 0 (List.rev (smash_context Δ' Δ)).
Proof.
  induction Δ in Δ' |- *.
  intros. simpl. auto.
  simpl. eapply (Alli_impl _ X0). simpl. now rewrite Nat.add_0_r.
  destruct a as [? [] ?]; simpl.
  - intros. eapply Alli_app in X as [X X'].
    eapply IHΔ; eauto.
    inv X'. unfold closed_decl in H. simpl in H.
    rewrite List.rev_length Nat.add_0_r in H.
    clear X1. eapply closed_subst_context; auto.
    now move/andP: H => [].
  - intros. eapply Alli_app in X as [X X'].
    eapply IHΔ; eauto.
    inv X'. unfold closed_decl in H. simpl in H.
    rewrite List.rev_length Nat.add_0_r in H.
    clear X1. rewrite List.rev_app_distr.
    eapply Alli_app_inv; repeat constructor.
    now rewrite Nat.add_0_r /=.
    rewrite List.rev_length /=. clear -X0.
    apply Alli_shift, (Alli_impl _ X0). intros.
    eapply closed_decl_upwards; eauto; lia.
Qed.

Lemma closed_smash_context_unfold n (Δ : context) :
  Alli (fun i d => closed_decl (n + i) d) 0 (List.rev Δ) -> 
  Alli (fun i d => closed_decl (n + i) d) 0 (List.rev (smash_context [] Δ)).
Proof.
  intros; apply (closed_smash_context_gen n _ []); auto. constructor.
Qed.

Lemma closedn_subst_instance_context {k Γ u} :
  closedn_ctx k (subst_instance u Γ) = closedn_ctx k Γ.
Proof.
  rewrite !test_context_k_eq.
  rewrite rev_subst_instance.
  rewrite alli_map.
  apply alli_ext; intros i [? [] ?]; unfold closed_decl, test_decl; cbn.
  all: now rewrite !closedn_subst_instance.
Qed.

Lemma closedn_ctx_spec k Γ : closedn_ctx k Γ <~> Alli (fun k => closed_decl k) k (List.rev Γ).
Proof.
  split.
  - induction Γ as [|d ?].
    + constructor.
    + rewrite closedn_ctx_cons => /andP [clΓ cld].
      simpl in *. eapply Alli_app_inv; simpl; eauto.
      repeat constructor. now rewrite List.rev_length.
  - induction Γ in k |- * => //.
    simpl. move/Alli_app => [clΓ cld].
    simpl. depelim cld. rewrite List.rev_length in i.
    now rewrite i IHΓ.
Qed.

Lemma closedn_smash_context (Γ : context) n :
  closedn_ctx n Γ ->
  closedn_ctx n (smash_context [] Γ).
Proof.
  intros.
  epose proof (closed_smash_context_unfold n Γ).
  apply closedn_ctx_spec. rewrite -(Nat.add_0_r n). apply Alli_shiftn, X.
  apply closedn_ctx_spec in H. rewrite -(Nat.add_0_r n) in H.
  now apply (Alli_shiftn_inv 0 _ n) in H.
Qed.

Lemma weaken_env_prop_closed {cf:checker_flags} : 
  weaken_env_prop (lift_typing (fun (_ : global_env_ext) (Γ : context) (t T : term) =>
  closedn #|Γ| t && closedn #|Γ| T)).
Proof. repeat red. intros. destruct t; red in X0; eauto. Qed.

Lemma declared_projection_closed_ind {cf:checker_flags} {Σ : global_env} {mdecl idecl cdecl p pdecl} : 
  wf Σ ->
  declared_projection Σ p mdecl idecl cdecl pdecl ->
  Forall_decls_typing
  (fun _ (Γ : context) (t T : term) =>
  closedn #|Γ| t && closedn #|Γ| T) Σ ->
  closedn (S (ind_npars mdecl)) pdecl.2.
Proof.
  intros wfΣ isdecl X0.
  pose proof (declared_projection_inv weaken_env_prop_closed wfΣ X0 isdecl) as onp.
  set (declared_inductive_inv _ wfΣ X0 _) as oib in *.
  clearbody oib.
  have onpars := onParams (declared_minductive_inv weaken_env_prop_closed wfΣ X0 isdecl.p1.p1).
  have parslen := onNpars (declared_minductive_inv weaken_env_prop_closed wfΣ X0 isdecl.p1.p1).
  simpl in onp.
  destruct (ind_ctors idecl) as [|? []] eqn:Heq; try contradiction.
  destruct onp as [_ onp].
  red in onp.
  destruct (nth_error (smash_context [] _) _) eqn:Heq'; try contradiction.
  destruct onp as [onna onp]. rewrite {}onp. 
  pose proof (onConstructors oib) as onc. 
  red in onc. rewrite Heq in onc. inv onc. clear X1.
  eapply on_cargs in X.
  simpl.
  replace (S (ind_npars mdecl)) with (0 + (1 + ind_npars mdecl)) by lia.
  eapply closedn_subst.
  { clear. unfold inds. generalize (ind_bodies mdecl).
    induction l; simpl; auto. }
  rewrite inds_length.
  eapply closedn_subst0.
  { clear. unfold projs. induction p.2; simpl; auto. }
  rewrite projs_length /=.
  eapply (@closed_upwards (ind_npars mdecl + #|ind_bodies mdecl| + p.2 + 1)).
  2:lia.
  eapply closedn_lift.
  clear -parslen isdecl Heq' onpars X.
  rename X into args.
  apply sorts_local_ctx_Pclosed in args.
  red in onpars.
  eapply All_local_env_Pclosed in onpars.
  eapply (Alli_impl (Q:=fun i d => closed_decl (#|ind_params mdecl| + i + #|arities_context (ind_bodies mdecl)|) d)) in args.
  2:{ intros n x. rewrite app_context_length. 
      intros H; eapply closed_decl_upwards; eauto. lia. }
  eapply (Alli_shiftn (P:=fun i d => closed_decl (i + #|arities_context (ind_bodies mdecl)|) d)) in args.
  rewrite Nat.add_0_r in args.
  eapply (Alli_impl (Q:=fun i d => closed_decl (i + #|arities_context (ind_bodies mdecl)|) d)) in onpars.
  2:{ intros n x d. eapply closed_decl_upwards; eauto; lia. }
  epose proof (Alli_app_inv onpars). rewrite List.rev_length /= in X.
  specialize (X args). rewrite -List.rev_app_distr in X.
  clear onpars args.
  eapply (Alli_impl (Q:=fun i d => closed_decl (#|arities_context (ind_bodies mdecl)| + i) d)) in X.
  2:intros; eapply closed_decl_upwards; eauto; lia.
  eapply closed_smash_context_unfold in X.
  eapply Alli_rev_nth_error in X; eauto.
  rewrite smash_context_length in X. simpl in X.
  eapply nth_error_Some_length in Heq'. rewrite smash_context_length in Heq'.
  simpl in Heq'. unfold closed_decl in X.
  move/andP: X => [] _ cl.
  eapply closed_upwards. eauto. rewrite arities_context_length.
  rewrite context_assumptions_app parslen.
  rewrite context_assumptions_app in Heq'. lia.
Qed.

Lemma closedn_ctx_alpha {k ctx ctx'} : 
  All2 (PCUICEquality.compare_decls eq eq) ctx ctx' ->
  closedn_ctx k ctx = closedn_ctx k ctx'.
Proof.
  induction 1 in k |- *; simpl; auto.
  rewrite IHX. f_equal.
  rewrite (All2_length X).
  destruct r; cbn; now subst.
Qed.

Definition closed_constructor_body mdecl (b : constructor_body) :=
  closedn_ctx (#|ind_bodies mdecl| + #|ind_params mdecl|) b.(cstr_args) &&
  forallb (closedn (#|ind_bodies mdecl| + #|ind_params mdecl| + #|b.(cstr_args)|)) b.(cstr_indices) &&
  closedn #|ind_bodies mdecl| b.(cstr_type).

Definition closed_inductive_body mdecl idecl :=
  closedn 0 idecl.(ind_type) &&
  closedn_ctx #|mdecl.(ind_params)| idecl.(ind_indices) &&
  forallb (closed_constructor_body mdecl) idecl.(ind_ctors) &&
  forallb (fun x => closedn (S (ind_npars mdecl)) x.2) idecl.(ind_projs).

Definition closed_inductive_decl mdecl :=
  closed_ctx (ind_params mdecl) &&
  forallb (closed_inductive_body mdecl) (ind_bodies mdecl).

Set SimplIsCbn.

Lemma on_global_env_impl `{checker_flags} Σ P Q :
  (forall Σ Γ t T, on_global_env P Σ.1 -> P Σ Γ t T -> Q Σ Γ t T) ->
  on_global_env P Σ -> on_global_env Q Σ.
Proof.
  intros X X0.
  simpl in *. induction X0; constructor; auto.
  clear IHX0. destruct d; simpl.
  - destruct c; simpl. destruct cst_body0; simpl in *; now eapply X.
  - red in o. simpl in *.
    destruct o0 as [onI onP onNP].
    constructor; auto.
    -- eapply Alli_impl. exact onI. eauto. intros.
       refine {| ind_arity_eq := X1.(ind_arity_eq);
                 ind_cunivs := X1.(ind_cunivs) |}.
       --- apply onArity in X1. unfold on_type in *; simpl in *.
           now eapply X.
       --- pose proof X1.(onConstructors) as X11. red in X11.
          eapply All2_impl; eauto.
          simpl. intros. destruct X2 as [? ? ? ?]; unshelve econstructor; eauto.
          * apply X; eauto.
          * clear -X0 X on_cargs. revert on_cargs.
            generalize (cstr_args x0).
            induction c in y |- *; destruct y; simpl; auto;
              destruct a as [na [b|] ty]; simpl in *; auto;
          split; intuition eauto.
          * clear -X0 X on_cindices.
            revert on_cindices.
            generalize (List.rev (lift_context #|cstr_args x0| 0 (ind_indices x))).
            generalize (cstr_indices x0).
            induction 1; simpl; constructor; auto.
       --- simpl; intros. pose (onProjections X1 H0). simpl in *; auto.
       --- destruct X1. simpl. unfold check_ind_sorts in *.
           destruct Universe.is_prop => //.
           destruct Universe.is_sprop; auto.
           split.
           * apply ind_sorts.
           * destruct indices_matter; auto.
             eapply type_local_ctx_impl. eapply ind_sorts. auto.
      --- eapply X1.(onIndices).
    -- red in onP. red.
       eapply All_local_env_impl. eauto.
       intros. now apply X.
Qed.

Lemma declared_decl_closed_ind `{checker_flags} {Σ : global_env} {cst decl} :
  wf Σ ->
  lookup_env Σ cst = Some decl ->
  Forall_decls_typing (fun (_ : global_env_ext) (Γ : context) (t T : term) => closedn #|Γ| t && closedn #|Γ| T) Σ ->
  on_global_decl (fun Σ Γ b t => closedn #|Γ| b && option_default (closedn #|Γ|) t true)
                 (Σ, universes_decl_of_decl decl) cst decl.
Proof.
  intros.
  eapply weaken_lookup_on_global_env; try red; eauto.
  eapply on_global_env_impl; cycle 1. eapply X0.
  red; intros. unfold lift_typing in *. destruct T; intuition auto with wf.
  destruct X2 as [s0 Hs0]. simpl. rtoProp; intuition.
Qed.

Lemma closedn_mapi_rec_ext (f g : nat -> context_decl -> context_decl) (l : context) n k' :
  closedn_ctx k' l ->
  (forall k x, n <= k -> k < length l + n -> 
    closed_decl (k' + #|l|) x ->
    f k x = g k x) ->
  mapi_rec f l n = mapi_rec g l n.
Proof.
  intros cl Hfg.
  induction l in n, cl, Hfg |- *; simpl; try congruence.
  intros. rewrite Hfg; simpl; try lia.
  rewrite closedn_ctx_cons in cl.
  move/andP: cl => [cll clr]. eapply closed_decl_upwards; eauto. lia.
  f_equal.
  rewrite IHl; auto.
  rewrite closedn_ctx_cons in cl.
  now move/andP: cl => [].
  intros. apply Hfg. simpl; lia. simpl. lia. simpl.
  eapply closed_decl_upwards; eauto. lia.
Qed.

Lemma closedn_All_local_env (ctx : list context_decl) :
  All_local_env 
    (fun (Γ : context) (b : term) (t : option term) =>
      closedn #|Γ| b && option_default (closedn #|Γ|) t true) ctx ->
    closedn_ctx 0 ctx.
Proof.
  induction 1; auto; rewrite closedn_ctx_cons IHX /=; now move/andP: t0 => [].
Qed.

Lemma declared_minductive_closed_ind {cf:checker_flags} {Σ : global_env} {mdecl mind} : 
  wf Σ ->
  Forall_decls_typing
  (fun (_ : global_env_ext) (Γ : context) (t T : term) =>
   closedn #|Γ| t && closedn #|Γ| T) Σ ->
  declared_minductive Σ mind mdecl ->
  closed_inductive_decl mdecl.
Proof.
  intros wfΣ HΣ decl.
  pose proof (declared_decl_closed_ind wfΣ decl) as decl'.
  specialize (decl' HΣ). 
  red in decl'.
  unfold closed_inductive_decl.
  apply andb_and. split. apply onParams in decl'.
  now apply closedn_All_local_env in decl'; auto.
  apply onInductives in decl'.
  eapply All_forallb.
  
  assert (Alli (fun i =>  declared_inductive Σ {| inductive_mind := mind; inductive_ind := i |} mdecl) 
    0 (ind_bodies mdecl)).
  { eapply forall_nth_error_Alli. intros.
    split; auto. }
  eapply Alli_mix in decl'; eauto. clear X.
  clear decl.
  eapply Alli_All; eauto.
  intros n x [decli oib].
  rewrite /closed_inductive_body.
  apply andb_and; split. apply andb_and. split.
  - rewrite andb_and. split.
    * apply onArity in oib. hnf in oib.
      now move/andP: oib => [] /= ->.
    * pose proof (onArity oib).
      rewrite oib.(ind_arity_eq) in X.
      red in X. simpl in X.
      rewrite !closedn_it_mkProd_or_LetIn /= !andb_true_r in X.
      now move/andP: X.
  - pose proof (onConstructors oib).
    red in X. eapply All_forallb. eapply All2_All_left; eauto.
    intros cdecl cs X0; 
    move/andP: (on_ctype X0) => [].
    simpl. unfold closed_constructor_body.
    intros Hty _.
    rewrite arities_context_length in Hty.
    rewrite Hty.
    rewrite X0.(cstr_eq) closedn_it_mkProd_or_LetIn in Hty.
    move/andP: Hty => [] _.
    rewrite closedn_it_mkProd_or_LetIn.
    move/andP=> [] ->. rewrite closedn_mkApps /=.
    move/andP=> [] _. rewrite forallb_app.
    now move/andP=> [] _ ->.

  - eapply All_forallb.
    pose proof (onProjections oib).
    destruct (eq_dec (ind_projs x) []) as [->|eq]; try constructor.
    specialize (X eq). clear eq.
    destruct (ind_ctors x) as [|cdecl []] eqn:hcdecl; try contradiction.
    apply on_projs in X.
    assert (Alli (fun i pdecl => declared_projection Σ 
     (({| inductive_mind := mind; inductive_ind := n |}, mdecl.(ind_npars)), i) mdecl x cdecl pdecl)
      0 (ind_projs x)).
    { eapply forall_nth_error_Alli.
      intros. split; auto. split; auto. cbn. now rewrite hcdecl. }
    eapply (Alli_All X0). intros.
    now eapply declared_projection_closed_ind in H.
Qed.

Lemma closed_declared_ind {Σ ind mdecl idecl} : 
  declared_inductive Σ ind mdecl idecl ->
  closed_inductive_decl mdecl ->
  closed_inductive_body mdecl idecl.
Proof.
  intros [decli hnth] [clpars clbods]%andb_and.
  solve_all.
  now eapply nth_error_all in clbods; eauto.
Qed.


Lemma closedn_ctx_decl {Γ n d k} :
  closedn_ctx k Γ ->
  nth_error Γ n = Some d ->
  closed_decl (k + #|Γ| - S n) d.
Proof.
  intros clΓ hnth. eapply closedn_ctx_spec in clΓ.
  pose proof (nth_error_Some_length hnth).
  rewrite (nth_error_rev _ _ H) in hnth.
  eapply nth_error_alli in clΓ; eauto.
  simpl in clΓ. eapply closed_decl_upwards; eauto. lia.
Qed.

Arguments lift_context _ _ _ : simpl never. 
Arguments subst_context _ _ _ : simpl never.

Lemma closedn_ctx_lift n k k' Γ : closedn_ctx k Γ ->
  closedn_ctx (n + k) (lift_context n k' Γ).
Proof.
  induction Γ as [|d ?]; cbn; auto; rewrite lift_context_snoc !closedn_ctx_cons /=;
    move/andP=> [clΓ cld]; rewrite IHΓ //;
  autorewrite with len in cld.
  move: cld; rewrite /test_decl. simpl.
  move/andP=> [clb clt]; apply andb_and; split.
  destruct (decl_body d) => /= //. simpl in clb |- *.
  eapply (closedn_lift n) in clb.
  autorewrite with len. now rewrite Nat.add_comm (Nat.add_comm n) Nat.add_assoc.
  eapply (closedn_lift n) in clt.
  autorewrite with len. now rewrite Nat.add_comm (Nat.add_comm n) Nat.add_assoc.
Qed.

Lemma closedn_ctx_subst k k' s Γ : 
  closedn_ctx (k + k' + #|s|) Γ ->
  forallb (closedn k) s ->
  closedn_ctx (k + k') (subst_context s k' Γ).
Proof.
  induction Γ as [|d ?] in k' |- *; auto; rewrite subst_context_snoc !closedn_ctx_cons /=;
  move/andP=> [clΓ cld]  cls; rewrite IHΓ //;
  autorewrite with len in cld.
  move: cld; rewrite /test_decl. simpl.
  move/andP=> [clb clt]; apply andb_and; split.
  destruct (decl_body d) => /= //. simpl in clb |- *.
  rewrite -Nat.add_assoc [#|s| + _]Nat.add_comm Nat.add_assoc in clb.
  rewrite -(Nat.add_assoc k) in clb.
  eapply (closedn_subst s) in clb => //. rewrite Nat.add_assoc in clb.
  autorewrite with len. now rewrite (Nat.add_comm #|Γ|).
  rewrite -Nat.add_assoc [#|s| + _]Nat.add_comm Nat.add_assoc in clt.
  rewrite -(Nat.add_assoc k) in clt.
  eapply (closedn_subst s) in clt => //. rewrite Nat.add_assoc in clt.
  autorewrite with len. now rewrite (Nat.add_comm #|Γ|).
Qed.

Lemma map_subst_closedn (s : list term) (k : nat) l :
  forallb (closedn k) l -> map (subst s k) l = l.
Proof.
  induction l; simpl; auto.
  move/andP=> [cla cll]. rewrite IHl //.
  now rewrite subst_closedn.
Qed.

Lemma closedn_extended_subst_gen Γ k k' : 
  closedn_ctx k Γ -> 
  forallb (closedn (k' + k + context_assumptions Γ)) (extended_subst Γ k').
Proof.
  induction Γ as [|[? [] ?] ?] in k, k' |- *; auto; rewrite ?closedn_ctx_cons /=;
   move/andP => [clΓ /andP[clb clt]].
  - rewrite IHΓ //.
    epose proof (closedn_subst (extended_subst Γ k') (k' + k + context_assumptions Γ) 0).
    autorewrite with len in H. rewrite andb_true_r.
    eapply H; auto.
    replace (k' + k + context_assumptions Γ + #|Γ|)
    with (k + #|Γ| + (context_assumptions Γ + k')) by lia.
    eapply closedn_lift. eapply clb.
  - apply andb_and. split.
    * apply Nat.ltb_lt; lia.
    * specialize (IHΓ k (S k') clΓ).
      red. rewrite -IHΓ. f_equal. f_equal. lia.
Qed.

Lemma closedn_extended_subst Γ : 
  closed_ctx Γ -> 
  forallb (closedn (context_assumptions Γ)) (extended_subst Γ 0).
Proof.
  intros clΓ. now apply (closedn_extended_subst_gen Γ 0 0).
Qed.

Lemma closedn_ctx_expand_lets k Γ Δ :
  closedn_ctx k Γ ->
  closedn_ctx (k + #|Γ|) Δ ->
  closedn_ctx (k + context_assumptions Γ) (expand_lets_ctx Γ Δ).
Proof.
  intros clΓ clΔ.
  rewrite /expand_lets_ctx /expand_lets_k_ctx.
  rewrite -(Nat.add_0_r (k + context_assumptions Γ)).
  eapply closedn_ctx_subst; len; simpl.
  replace (k + context_assumptions Γ + #|Γ|) with (context_assumptions Γ + (k + #|Γ|)) by lia.
  eapply closedn_ctx_lift => //.
  eapply forallb_impl. 2:eapply closedn_extended_subst_gen; eauto.
  simpl; auto.
Qed.

Lemma closed_ctx_expand_lets Γ Δ : 
  closed_ctx (Γ ,,, Δ) ->
  closedn_ctx (context_assumptions Γ) (expand_lets_ctx Γ Δ).
Proof.
  rewrite /expand_lets_ctx /expand_lets_k_ctx.
  intros cl.
  pose proof (closedn_ctx_subst (context_assumptions Γ) 0).
  rewrite Nat.add_0_r in H. apply: H.
  - simpl. len.
    rewrite closedn_ctx_lift //.
    rewrite closedn_ctx_app in cl. now move/andP: cl.
  - apply (closedn_extended_subst_gen Γ 0 0).
    rewrite closedn_ctx_app in cl.
    now move/andP: cl => [].
Qed.

#[global]
Hint Rewrite to_extended_list_k_length : len.

Lemma smash_context_subst Δ s n Γ : smash_context (subst_context s (n + #|Γ|) Δ) (subst_context s n Γ) =
  subst_context s n (smash_context Δ Γ).
Proof.
  revert Δ. induction Γ as [|[na [b|] ty]]; intros Δ; simpl; auto.
  - now rewrite Nat.add_0_r.
  - rewrite -IHΓ.
    rewrite subst_context_snoc /=. f_equal.
    rewrite !subst_context_alt !mapi_compose.
    apply mapi_ext=> n' x.
    destruct x as [na' [b'|] ty']; simpl.
    * rewrite !mapi_length /subst_decl /= /map_decl /=; f_equal.
      + rewrite Nat.add_0_r distr_subst_rec. simpl. lia_f_equal.
      + rewrite Nat.add_0_r distr_subst_rec; simpl. lia_f_equal.
    * rewrite !mapi_length /subst_decl /= /map_decl /=; f_equal.
      rewrite Nat.add_0_r distr_subst_rec /=. lia_f_equal.
  - rewrite -IHΓ.
    rewrite subst_context_snoc /= // /subst_decl /map_decl /=.
    f_equal.
    rewrite subst_context_app. simpl.
    rewrite /app_context. f_equal.
    + lia_f_equal.
    + rewrite /subst_context // /fold_context_k /= /map_decl /=.
      lia_f_equal.
Qed.


Lemma smash_context_app_def Γ na b ty :
  smash_context [] (Γ ++ [{| decl_name := na; decl_body := Some b; decl_type := ty |}]) =
  smash_context [] (subst_context [b] 0 Γ).
Proof.
  now rewrite smash_context_app smash_context_acc /= subst_empty lift0_id lift0_context /=
    subst_context_nil app_nil_r (smash_context_subst []).
Qed.

Lemma smash_context_app_ass Γ na ty :
  smash_context [] (Γ ++ [{| decl_name := na; decl_body := None; decl_type := ty |}]) =
  smash_context [] Γ ++ [{| decl_name := na; decl_body := None; decl_type := ty |}].
Proof.
  rewrite smash_context_app smash_context_acc /= subst_context_lift_id //.
  now rewrite lift0_context.
Qed.

Lemma lift_context_add k k' n Γ : lift_context (k + k') n Γ = lift_context k n (lift_context k' n Γ).
Proof.
  induction Γ => //.
  rewrite !lift_context_snoc IHΓ; f_equal.
  destruct a as [na [b|] ty]; rewrite /lift_decl /map_decl /=; simpl; f_equal;
  len; rewrite simpl_lift //; try lia.
Qed.

Lemma distr_lift_subst_context_rec n k s Γ k' : lift_context n (k' + k) (subst_context s k' Γ) =
  subst_context (map (lift n k) s) k' (lift_context n (#|s| + k + k') Γ).
Proof.
  rewrite !lift_context_alt !subst_context_alt.
  rewrite !mapi_compose.
  apply mapi_ext.
  intros n' x.
  rewrite /lift_decl /subst_decl !compose_map_decl.
  apply map_decl_ext => y. len.
  replace (Nat.pred #|Γ| - n' + (#|s| + k + k'))
    with ((Nat.pred #|Γ| - n' + k') + #|s| + k) by lia.
  rewrite -distr_lift_subst_rec. f_equal. lia.
Qed.

Lemma assumption_context_app_inv Γ Δ : assumption_context Γ -> assumption_context Δ ->  
  assumption_context (Γ ++ Δ).
Proof.
  induction 1; try constructor; auto.
Qed.

Lemma closed_ctx_decl k d Γ : closedn_ctx k (d :: Γ) =
  closed_decl (k + #|Γ|) d && closedn_ctx k Γ.
Proof.
  now simpl; rewrite andb_comm Nat.add_comm.
Qed.

Lemma closedn_ctx_upwards k k' Γ : 
  closedn_ctx k Γ -> k <= k' ->
  closedn_ctx k' Γ.
Proof.
  induction Γ; auto. rewrite !closed_ctx_decl /=.
  move/andb_and => [cla clΓ] le.
  rewrite (IHΓ clΓ le).
  rewrite (closed_decl_upwards _ _ cla) //. lia.
Qed.

Lemma closedn_expand_lets k (Γ : context) t : 
  closedn (k + context_assumptions Γ) (expand_lets Γ t) -> 
  closedn (k + #|Γ|) t.
Proof.
  revert k t.
  induction Γ as [|[na [b|] ty] Γ] using ctx_length_rev_ind; intros k t; simpl; auto.
  - now rewrite /expand_lets /expand_lets_k subst_empty lift0_id.
  - len.
    rewrite !expand_lets_vdef.
    specialize (H (subst_context [b] 0 Γ) ltac:(len; lia)).
    len in H.
    intros cl.
    specialize (H _ _ cl).
    eapply (closedn_subst_eq' _ k) in H.
    simpl in *. now rewrite Nat.add_assoc.
  - len.
    rewrite !expand_lets_vass. simpl. intros cl.
    specialize (H Γ ltac:(len; lia)).
    rewrite (Nat.add_comm _ 1) Nat.add_assoc in cl.
    now rewrite (Nat.add_comm _ 1) Nat.add_assoc.
Qed.


Ltac len' := rewrite_strat (topdown (repeat (old_hints len))).

Tactic Notation "len'" "in" hyp(id) :=
  rewrite_strat (topdown (repeat (old_hints len))) in id.

Lemma closedn_expand_lets_eq k (Γ : context) k' t :
  closedn_ctx k Γ ->
  closedn (k + k' + context_assumptions Γ) (expand_lets_k Γ k' t) =
  closedn (k + k' + #|Γ|) t.
Proof.
  revert k k' t.
  induction Γ as [|[na [b|] ty] Γ] using ctx_length_rev_ind; intros k k' t;
    rewrite ?closedn_ctx_app /= /id /=; simpl; auto.
  - now rewrite /expand_lets /expand_lets_k /= subst_empty lift0_id.
  - move/andb_and=> [cld clΓ]. len'.
    rewrite !expand_lets_k_vdef.
    simpl in cld |- *. move/andb_and: cld => /= [clb _].
    specialize (H (subst_context [b] 0 Γ) ltac:(len; lia)).
    len' in H; simpl in H. len.
    rewrite H /=.
    relativize k. eapply closedn_ctx_subst. simpl. 3:rewrite Nat.add_0_r //.
    now rewrite Nat.add_0_r. now rewrite /= clb.
    rewrite -Nat.add_assoc -closedn_subst_eq. simpl. now rewrite clb.
    simpl; lia_f_equal.
  - len'. move/andb_and => [clty clΓ]. 
    rewrite !expand_lets_k_vass. simpl.
    specialize (H Γ ltac:(len; lia) (S k)).
    rewrite Nat.add_assoc !Nat.add_succ_r !Nat.add_0_r. apply H.
    now rewrite Nat.add_1_r in clΓ.
Qed.

Lemma closedn_to_extended_list_k_up k Γ k' : 
  k' + #|Γ| <= k ->
  forallb (closedn k) (to_extended_list_k Γ k').
Proof.
  move=> le. rewrite /to_extended_list_k.
  eapply Forall_forallb; eauto. 2:{ intros x H; eapply H. }
  eapply Forall_impl. eapply reln_list_lift_above. constructor.
  simpl; intros.
  destruct H as [n [-> leq]]. simpl.
  eapply Nat.ltb_lt. lia.
Qed.

Lemma closedn_to_extended_list_k Γ k : 
  forallb (closedn (k + #|Γ|)) (to_extended_list_k Γ k).
Proof.
  now apply closedn_to_extended_list_k_up.
Qed.

Lemma closedn_to_extended_list Γ : 
  forallb (closedn #|Γ|) (to_extended_list Γ).
Proof.
  rewrite /to_extended_list.
  apply (closedn_to_extended_list_k _ 0).
Qed.

Lemma closed_ind_predicate_context {Σ ind mdecl idecl} : 
  declared_inductive Σ ind mdecl idecl ->
  closed_inductive_decl mdecl ->
  closedn_ctx (context_assumptions mdecl.(ind_params)) (ind_predicate_context ind mdecl idecl).
Proof.
  intros decli cl.
  move: (closed_declared_ind decli cl).
  move/andP: cl => [] clpars _.
  move/andP => [] /andP [] /andP [] clty clinds _ _.
  rewrite /ind_predicate_context /=.
  apply/andP. split.
  - now eapply (closedn_ctx_expand_lets 0).
  - rewrite /test_decl /=; len.
    rewrite closedn_mkApps /= //.
    set foo := (X in forallb X _).
    relativize foo.
    eapply closedn_to_extended_list.
    now rewrite /foo; len.
Qed.

Lemma closed_inds {ind mdecl u} :
  forallb (closedn 0) (inds (inductive_mind ind) u (ind_bodies mdecl)).
Proof.
  rewrite inds_spec. rewrite forallb_rev.
  unfold mapi.
  generalize 0 at 2.
  induction (ind_bodies mdecl); simpl; auto.
Qed.

Lemma declared_minductive_closed_inds {cf:checker_flags} {Σ ind mdecl u} {wfΣ : wf Σ} :
  declared_minductive Σ (inductive_mind ind) mdecl ->
  forallb (closedn 0) (inds (inductive_mind ind) u (ind_bodies mdecl)).
Proof.
  intros h.
  red in h.
  eapply lookup_on_global_env in h. 2: eauto.
  destruct h as [Σ' [wfΣ' decl']].
  red in decl'. destruct decl' as [h ? ? ?].
  rewrite inds_spec. rewrite forallb_rev.
  unfold mapi.
  generalize 0 at 1. generalize 0. intros n m.
  induction h in n, m |- *.
  - reflexivity.
  - simpl. eauto.
Qed.

Lemma closed_cstr_branch_context {cf : checker_flags} {Σ} {wfΣ : wf Σ} {c mdecl cdecl} : 
  closed_inductive_decl mdecl ->
  closed_constructor_body mdecl cdecl ->
  closedn_ctx (context_assumptions mdecl.(ind_params)) (cstr_branch_context c mdecl cdecl).
Proof.
  intros cl clc.
  move/andP: cl => [] clpars _.
  move/andP: clc => [] /andP [] clargs clinds cltype.
  rewrite /cstr_branch_context /=.
  eapply (closedn_ctx_expand_lets 0) => // /=.
  eapply closedn_ctx_subst. len. now rewrite Nat.add_comm.
  eapply closed_inds.
Qed.

Lemma declared_minductive_ind_npars {cf:checker_flags} {Σ} {wfΣ : wf Σ} {mdecl ind} :
  declared_minductive Σ ind mdecl ->
  ind_npars mdecl = context_assumptions mdecl.(ind_params).
Proof.
  intros h.
  unfold declared_minductive in h.
  eapply lookup_on_global_env in h. 2: eauto.
  destruct h as [Σ' [wfΣ' decl']].
  red in decl'. destruct decl' as [h ? ? ?].
  now rewrite onNpars.
Qed.

Lemma closed_ind_closed_cstrs {Σ ind mdecl idecl} : 
  closed_inductive_decl mdecl -> 
  declared_inductive Σ ind mdecl idecl ->
  All (closed_constructor_body mdecl) (ind_ctors idecl).
Proof.
  intros []%andb_and.
  intros [decli hnth].
  solve_all. eapply nth_error_all in H0; tea.
  simpl in H0.
  move/andP: H0 => [] /andP []; solve_all.
Qed.

Lemma typecheck_closed `{cf : checker_flags} :
  env_prop (fun Σ Γ t T =>
              closedn #|Γ| t && closedn #|Γ| T)
           (fun Σ Γ => closed_ctx Γ).
Proof.
  assert (X := weaken_env_prop_closed).
  apply typing_ind_env; intros * wfΣ Γ wfΓ *; intros; cbn in *;
  rewrite -> ?andb_and in *; try solve [intuition auto].

  - induction X0; auto; rewrite closedn_ctx_cons /= IHX0 /= //.
    now move/andP: p => [] /= -> _.

  - pose proof (nth_error_Some_length H).
    elim (Nat.ltb_spec n #|Γ|); intuition auto. all: try lia. clear H1.

    induction Γ in n, H, H0, H2 |- *. rewrite nth_error_nil in H. discriminate.
    destruct n.
    simpl in H. noconf H. simpl.
    rewrite -Nat.add_1_r. apply closedn_lift.
    rewrite closedn_ctx_cons in H0. move/andP: H0 => [_ ca].
    destruct a as [na [b|] ty]. simpl in ca.
    rewrite /test_decl /= in ca.
    now move/andP: ca => [_ cty].
    now rewrite /test_decl /= in ca.
    simpl.
    rewrite -Nat.add_1_r. 
    rewrite -(simpl_lift _ (S n) 0 1 0); try lia.
    apply closedn_lift. apply IHΓ; auto.
    rewrite closedn_ctx_cons in H0.
    now move/andP: H0 => [H0 _]. simpl in H2; lia.

  - intuition auto.
    generalize (closedn_subst [u] #|Γ| 0 B). rewrite Nat.add_0_r.
    move=> Hs. apply: Hs => /=. simpl. rewrite H1 => //.
    rewrite Nat.add_1_r. auto.

  - rewrite closedn_subst_instance.
    eapply lookup_on_global_env in X0; eauto.
    destruct X0 as [Σ' [HΣ' IH]].
    repeat red in IH. destruct decl, cst_body0. simpl in *.
    rewrite -> andb_and in IH. intuition auto.
    eauto using closed_upwards with arith.
    simpl in *.
    repeat red in IH. destruct IH as [s Hs].
    rewrite -> andb_and in Hs. intuition auto.
    eauto using closed_upwards with arith.

  - rewrite closedn_subst_instance.
    eapply declared_inductive_inv in X0; eauto.
    apply onArity in X0. repeat red in X0.
    destruct X0 as [s Hs]. rewrite -> andb_and in Hs.
    intuition eauto using closed_upwards with arith.

  - destruct isdecl as [Hidecl Hcdecl].
    apply closedn_subst0.
    + unfold inds. clear. simpl. induction #|ind_bodies mdecl|. constructor.
      simpl. now rewrite IHn.
    + rewrite inds_length.
      rewrite closedn_subst_instance.
      eapply declared_inductive_inv in X0; eauto.
      pose proof X0.(onConstructors) as XX.
      eapply All2_nth_error_Some in Hcdecl; eauto.
      destruct Hcdecl as [? [? ?]]. cbn in *.
      destruct o as [? ? [s Hs] _]. rewrite -> andb_and in Hs.
      apply proj1 in Hs.
      rewrite arities_context_length in Hs.
      eauto using closed_upwards with arith.

  - destruct H3 as [clret _].
    destruct H6 as [clc clty].
    rewrite closedn_mkApps in clty. simpl in clty.
    rewrite forallb_app in clty. move/andP: clty => [clpar clinds].
    rewrite app_context_length in clret.
    red in H8. eapply Forall2_All2 in H8.
    eapply All2i_All2_mix_left in X6; eauto.
    eapply declared_minductive_closed_ind in X0; tea. 2:exact isdecl.
    pose proof (closed_ind_closed_cstrs X0 isdecl).
    eapply All2i_All_mix_left in X6; tea. clear X7.
    intuition auto. 
    + unfold test_predicate_k. simpl. rtoProp; intuition eauto.
      rewrite (closedn_ctx_alpha X1).
      eapply closed_ind_predicate_context in X0; tea.
      rewrite (wf_predicate_length_pars H1).
      now rewrite (declared_minductive_ind_npars isdecl).
      rewrite (All2_length X1).
      rewrite /predctx in clret.
      rewrite case_predicate_context_length_indices // in clret.
      { now rewrite ind_predicate_context_length. }
    + clear H8. solve_all. unfold test_branch_k. clear H6. solve_all.
      * rewrite (closedn_ctx_alpha a1).
        eapply closed_cstr_branch_context in X0; tea.
        rewrite (wf_predicate_length_pars H1).
        now rewrite (declared_minductive_ind_npars isdecl).
      * rewrite (All2_length a1).
        len in H8.
        rewrite case_branch_type_fst in H8.
        rewrite case_branch_context_length_args in H8 => //.
        now rewrite cstr_branch_context_length.
    + rewrite closedn_mkApps; auto.
      rewrite closedn_it_mkLambda_or_LetIn //.
      rewrite closedn_ctx_app in H4.
      now move/andP: H4 => [].
      now rewrite Nat.add_comm.
      rewrite forallb_app. simpl. now rewrite clc clinds.

  - intuition auto.
    apply closedn_subst0.
    + simpl. rewrite closedn_mkApps in H3.
      rewrite forallb_rev H2. apply H3.
    + rewrite closedn_subst_instance.
      eapply declared_projection_closed_ind in X0; eauto.
      simpl; rewrite List.rev_length H1.
      eapply closed_upwards; eauto. lia.

  - clear H.
    split. solve_all.
    destruct x; simpl in *.
    unfold test_def. simpl. rtoProp.
    split.
    rewrite -> app_context_length in *. rewrite -> Nat.add_comm in *.
    eapply closedn_lift_inv in H3; eauto. lia.
    subst types.
    now rewrite app_context_length fix_context_length in H.
    eapply nth_error_all in X0; eauto. simpl in X0. intuition auto. rtoProp.
    destruct X0 as [s [Hs cl]]. now rewrite andb_true_r in cl.

  - split. solve_all. destruct x; simpl in *.
    unfold test_def. simpl. rtoProp.
    split.
    destruct a as [s [Hs cl]].
    now rewrite andb_true_r in cl.
    rewrite -> app_context_length in *. rewrite -> Nat.add_comm in *.
    subst types. now rewrite fix_context_length in H3.
    eapply nth_error_all in X0; eauto.
    destruct X0 as [s [Hs cl]].
    now rewrite andb_true_r in cl.
Qed.

Lemma declared_minductive_closed {cf:checker_flags} {Σ : global_env} {wfΣ : wf Σ} {mdecl mind} : 
  declared_minductive Σ mind mdecl ->
  closed_inductive_decl mdecl.
Proof.
  eapply declared_minductive_closed_ind; tea.
  now apply (env_prop_sigma typecheck_closed).
Qed.

Lemma declared_inductive_closed {cf:checker_flags} {Σ : global_env} {wfΣ : wf Σ} {mdecl mind idecl} : 
  declared_inductive Σ mind mdecl idecl ->
  closed_inductive_body mdecl idecl.
Proof.
  intros [decli hnth].
  eapply declared_minductive_closed in decli; tea.
  move/andP: decli => [clpars cli].
  solve_all. eapply nth_error_all in cli; eauto.
  now simpl in cli.
Qed.

Lemma declared_projection_closed {cf:checker_flags} {Σ : global_env} {mdecl idecl p cdecl pdecl} : 
  wf Σ ->
  declared_projection Σ p mdecl idecl cdecl pdecl ->
  closedn (S (ind_npars mdecl)) pdecl.2.
Proof.
  intros; eapply declared_projection_closed_ind; eauto.
  eapply (env_prop_sigma typecheck_closed); eauto.
Qed.

Lemma declared_inductive_closed_pars_indices {cf:checker_flags} {Σ : global_env} {wfΣ : wf Σ} {mdecl mind idecl} : 
  declared_inductive Σ mind mdecl idecl ->
  closed_ctx (ind_params mdecl ,,, ind_indices idecl).
Proof.
  intros decli.
  pose proof (declared_minductive_closed (proj1 decli)).
  move/andP: H => [] clpars _. move: decli.
  move/declared_inductive_closed.
  move/andP => [] /andP [] clind clbodies.
  move/andP: clind => [] _ indpars _.
  now rewrite closedn_ctx_app clpars indpars.
Qed.

Lemma declared_constructor_closed {cf:checker_flags} {Σ : global_env} {wfΣ : wf Σ} {mdecl idecl c cdecl} : 
  declared_constructor Σ c mdecl idecl cdecl ->
  closed_constructor_body mdecl cdecl.
Proof.
  intros declc.
  generalize (declared_minductive_closed declc).
  rewrite /closed_inductive_decl.
  rewrite /closed_inductive_body.
  move/andP=> [_ clbs].
  destruct declc.
  destruct H.
  solve_all.
  eapply nth_error_all in clbs; eauto.
  simpl in clbs.
  move/andP: clbs => [] /andP [] _ clc _.
  solve_all.
  eapply nth_error_all in clc; eauto. now simpl in clc.
Qed.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

Lemma subject_closed {cf} {Σ} {wfΣ : wf Σ.1} {Γ t T} : 
  Σ ;;; Γ |- t : T ->
  closedn #|Γ| t.
Proof.
  now move/(env_prop_typing typecheck_closed) => /andP [ct _].
Qed.

Lemma type_closed {cf} {Σ} {wfΣ : wf Σ.1} {Γ t T} : 
  Σ ;;; Γ |- t : T ->
  closedn #|Γ| T.
Proof.
  now move/typecheck_closed => [_ [_ /andP [_ ct]]].
Qed.

Lemma isType_closed {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ.1} {Γ T} : isType Σ Γ T -> closedn #|Γ| T.
Proof. intros [s Hs]. now eapply subject_closed in Hs. Qed.

Lemma closed_wf_local `{checker_flags} {Σ Γ} :
  wf Σ.1 ->
  wf_local Σ Γ ->
  closed_ctx Γ.
Proof.
  intros wfΣ wfΓ.
  apply (env_prop_wf_local typecheck_closed Σ wfΣ _ wfΓ).
Qed.

Lemma ctx_inst_closed {cf:checker_flags} (Σ : global_env_ext) Γ i Δ : 
  wf Σ.1 -> ctx_inst typing Σ Γ i Δ -> All (closedn #|Γ|) i.
Proof.
  intros wfΣ; induction 1; auto; constructor; auto.
  now eapply subject_closed in t0.
Qed.

Lemma declared_decl_closed `{checker_flags} {Σ : global_env} {cst decl} :
  wf Σ ->
  lookup_env Σ cst = Some decl ->
  on_global_decl (fun Σ Γ b t => closedn #|Γ| b && option_default (closedn #|Γ|) t true)
                 (Σ, universes_decl_of_decl decl) cst decl.
Proof.
  intros.
  apply declared_decl_closed_ind; eauto.
  now eapply (env_prop_sigma typecheck_closed).
Qed.

Lemma declared_constant_closed_type {cf:checker_flags} {Σ : global_env} {wfΣ : wf Σ} {cst decl} :
  declared_constant Σ cst decl ->
  closed decl.(cst_type).
Proof.
  intros h.
  unfold declared_constant in h.
  eapply lookup_on_global_env in h. 2: eauto.
  destruct h as [Σ' [wfΣ' decl']].
  red in decl'. red in decl'.
  destruct decl as [ty bo un]. simpl in *.
  destruct bo as [t|].
  - now eapply type_closed in decl'.
  - cbn in decl'. destruct decl' as [s h].
    now eapply subject_closed in h. Unshelve. all:tea.
Qed.

Lemma declared_constant_closed_body {cf : checker_flags} :
  forall (Σ : global_env) cst decl body,
    wf Σ ->
    declared_constant Σ cst decl ->
    decl.(cst_body) = Some body ->
    closed body.
Proof.
  intros Σ cst decl body hΣ h e.
  unfold declared_constant in h.
  eapply lookup_on_global_env in h. 2: eauto.
  destruct h as [Σ' [wfΣ' decl']].
  red in decl'. red in decl'.
  destruct decl as [ty bo un]. simpl in *.
  rewrite e in decl'.
  now eapply subject_closed in decl'.
  Unshelve. all:tea.
Qed.

Lemma declared_inductive_closed_type {cf:checker_flags} :
  forall Σ mdecl ind idecl,
    wf Σ ->
    declared_inductive Σ ind mdecl idecl ->
    closed idecl.(ind_type).
Proof.
  intros Σ mdecl ind idecl hΣ h.
  unfold declared_inductive in h.
  destruct h as [h1 h2].
  unfold declared_minductive in h1.
  eapply lookup_on_global_env in h1. 2: eauto.
  destruct h1 as [Σ' [wfΣ' decl']].
  red in decl'. destruct decl' as [h ? ? ?].
  eapply Alli_nth_error in h. 2: eassumption.
  simpl in h. destruct h as [? [? h] ? ? ?].
  eapply typecheck_closed in h as [? e]. 2: auto.
  now move: e => [_ /andP []]. 
Qed.

Lemma declared_inductive_closed_params {cf:checker_flags} {Σ mdecl ind idecl} {wfΣ : wf Σ} :
  declared_inductive Σ ind mdecl idecl ->
  closed_ctx mdecl.(ind_params).
Proof.
  intros h.
  pose proof (on_declared_inductive h) as [onmind _].
  eapply onParams in onmind.
  eapply closed_wf_local. 2:tea. eauto.
Qed.

Lemma declared_inductive_closed_params_inst {cf:checker_flags} {Σ mdecl ind idecl} {wfΣ : wf Σ} {u} :
  declared_inductive Σ ind mdecl idecl ->
  closed_ctx (subst_instance u mdecl.(ind_params)).
Proof.
  intros h.
  rewrite closedn_subst_instance_context.
  now apply (declared_inductive_closed_params h).
Qed.

Lemma declared_inductive_closed_constructors {cf:checker_flags} {Σ ind mdecl idecl} {wfΣ : wf Σ} :
  declared_inductive Σ ind mdecl idecl ->
  All (closed_constructor_body mdecl) idecl.(ind_ctors).
Proof.
  intros [hmdecl hidecl].
  eapply (declared_minductive_closed (Σ:=empty_ext Σ)) in hmdecl; auto.
  unfold closed_inductive_decl in hmdecl.
  move/andP: hmdecl => [clpars clbodies].
  eapply forallb_nth_error in clbodies; eauto.
  erewrite hidecl in clbodies. simpl in clbodies.
  unfold closed_inductive_body in clbodies.
  move/andP: clbodies => [/andP [_ cl] _].
  now eapply forallb_All in cl.
Qed.


Lemma declared_minductive_closed_arities {cf:checker_flags}
  {Σ ind mdecl} {wfΣ : wf Σ} :
  declared_minductive Σ ind mdecl ->
  closed_ctx (arities_context (ind_bodies mdecl)).
Proof.
  intros h.
  eapply declared_minductive_closed in h.
  move/andP: h => [] _ clbs.
  induction (ind_bodies mdecl) => //.
  rewrite /arities_context /= rev_map_spec /=.
  move: clbs; simpl. move=> /andP[] cla clbs.
  rewrite closedn_ctx_app /=. apply/andP; split; auto.
  rewrite /test_decl /=. now move/andP: cla => [] /andP[] /andP[].
  eapply closedn_ctx_upwards. rewrite -rev_map_spec. eapply IHl => //. lia.
Qed.

Lemma declared_constructor_closed_gen_type {cf:checker_flags}
  {Σ mdecl idecl c cdecl} {wfΣ : wf Σ} :
  declared_constructor Σ c mdecl idecl cdecl ->
  closedn #|arities_context (ind_bodies mdecl)| cdecl.(cstr_type).
Proof.
  intros h.
  unfold declared_constructor in h.
  destruct c as [i ci]. simpl in h. destruct h as [hidecl hcdecl].
  eapply declared_inductive_closed_constructors in hidecl as h.
  eapply All_nth_error in h. 2: eassumption.
  move/andP: h => [/andP [hargs hindices]] hty. now len.
Qed.

Lemma declared_constructor_closed_type {cf:checker_flags}
  {Σ mdecl idecl c cdecl u} {wfΣ : wf Σ} :
  declared_constructor Σ c mdecl idecl cdecl ->
  closed (type_of_constructor mdecl cdecl c u).
Proof.
  intros h.
  unfold declared_constructor in h.
  destruct c as [i ci]. simpl in h. destruct h as [hidecl hcdecl].
  eapply declared_inductive_closed_constructors in hidecl as h.
  unfold type_of_constructor. simpl.
  eapply All_nth_error in h. 2: eassumption.
  move/andP: h => [/andP [hargs hindices]] hty.
  eapply closedn_subst0.
  - eapply declared_minductive_closed_inds. all: eauto.
  - simpl. rewrite inds_length.
    rewrite closedn_subst_instance. assumption.
Qed.

Lemma declared_constructor_closed_args {cf:checker_flags}
  {Σ mdecl idecl c cdecl} {wfΣ : wf Σ} :
  declared_constructor Σ c mdecl idecl cdecl ->
  closedn_ctx (#|ind_bodies mdecl| + #|ind_params mdecl|) cdecl.(cstr_args).
Proof.
  intros h.
  unfold declared_constructor in h.
  destruct c as [i ci]. simpl in h. destruct h as [hidecl hcdecl].
  eapply declared_inductive_closed_constructors in hidecl as h.
  eapply All_nth_error in h. 2: eassumption.
  move/andP: h => [/andP [hargs hindices]] hty.
  apply hargs.
Qed.

Lemma declared_constructor_closed_indices {cf:checker_flags}
  {Σ mdecl idecl c cdecl} {wfΣ : wf Σ} :
  declared_constructor Σ c mdecl idecl cdecl ->
  forallb (closedn (#|ind_bodies mdecl| + #|ind_params mdecl| + #|cstr_args cdecl|)) cdecl.(cstr_indices).
Proof.
  intros h.
  unfold declared_constructor in h.
  destruct c as [i ci]. simpl in h. destruct h as [hidecl hcdecl].
  eapply declared_inductive_closed_constructors in hidecl as h.
  eapply All_nth_error in h. 2: eassumption.
  now move/andP: h => [/andP [hargs hindices]] hty.
Qed.

Lemma declared_projection_closed_type {cf:checker_flags} 
  {Σ mdecl idecl p cdecl pdecl} {wfΣ : wf Σ} :
  declared_projection Σ p mdecl idecl cdecl pdecl ->
  closedn (S (ind_npars mdecl)) pdecl.2.
Proof.
  intros decl.
  now eapply declared_projection_closed in decl.
Qed.
  
Lemma term_closedn_list_ind :
  forall (P : nat -> term -> Type), 
    (forall k (n : nat), n < k -> P k (tRel n)) ->
    (forall k (i : ident), P k (tVar i)) ->
    (forall k (n : nat) (l : list term), All (P k) l -> P k (tEvar n l)) ->
    (forall k s, P k (tSort s)) ->
    (forall k (n : aname) (t : term), P k t -> forall t0 : term, P (S k) t0 -> P k (tProd n t t0)) ->
    (forall k (n : aname) (t : term), P k t -> forall t0 : term, P (S k)  t0 -> P k (tLambda n t t0)) ->
    (forall k (n : aname) (t : term),
        P k t -> forall t0 : term, P k t0 -> forall t1 : term, P (S k) t1 -> P k (tLetIn n t t0 t1)) ->
    (forall k (t u : term), P k t -> P k u -> P k (tApp t u)) ->
    (forall k s (u : list Level.t), P  k (tConst s u)) ->
    (forall k (i : inductive) (u : list Level.t), P k (tInd i u)) ->
    (forall k (i : inductive) (n : nat) (u : list Level.t), P k (tConstruct i n u)) ->
    (forall k (ci : case_info) (p : predicate term),
        tCasePredProp_k P k p -> 
        forall t0 : term, P k t0 -> forall l : list (branch term),
        tCaseBrsProp_k P p k l -> P k (tCase ci p t0 l)) ->
    (forall k (s : projection) (t : term), P k t -> P k (tProj s t)) ->
    (forall k (m : mfixpoint term) (n : nat), tFixProp (P k) (P (#|fix_context m| + k)) m -> P k (tFix m n)) ->
    (forall k (m : mfixpoint term) (n : nat), tFixProp (P k) (P (#|fix_context m| + k)) m -> P k (tCoFix m n)) ->
    (forall k p, P k (tPrim p)) ->
    forall k (t : term), closedn k t -> P k t.
Proof.
  intros until t. revert k t.
  fix auxt 2.
  move auxt at top.
  intros k t.
  destruct t; intros clt;  match goal with
                 H : _ |- _ => apply H
              end; auto; simpl in clt; 
            try move/andP: clt => [cl1 cl2]; 
            try move/andP: cl1 => [cl1 cl1'];
            try solve[apply auxt; auto];
              simpl in *.
              
  - now apply Nat.ltb_lt in clt. 
  - revert l clt.
    fix auxl' 1.
    destruct l; constructor; [|apply auxl'].
    apply auxt. simpl in clt. now move/andP: clt  => [clt cll].
    now move/andP: clt => [clt cll].

  - red. move/andP: cl1 => /= [] /andP [] clpars clctx clret.
    repeat split.
    * revert clpars. generalize (pparams p).
      fix auxl' 1.
      destruct l; [constructor|]; cbn.
      move=> /= /andP []. simpl. move=> /= clt cll.
      constructor; [|apply auxl'].
      apply auxt => //. now rewrite cll /=.
    * revert clctx.
      unfold onctx_k.
      generalize (pcontext p).
      fix auxl' 1.
      destruct l; [constructor|]. simpl.
      move=>  /andP []. simpl. move=> /= clctx /andP [] clt cll.
      destruct c as [na [b|] ty]; simpl in *;
      constructor; simpl.
      split; apply auxt; rewrite Nat.sub_0_r //. simpl.
      eapply Alli_shift, Alli_impl; eauto. simpl.
      intros n x. now replace (Nat.pred #|l| - n + #|pparams p|) with (#|l| - S n + #|pparams p|) by lia.
      rewrite Nat.sub_0_r //. split; auto. exact tt.
      eapply Alli_shift, Alli_impl; eauto. simpl.
      intros n x. now replace (Nat.pred #|l| - n + #|pparams p|) with (#|l| - S n + #|pparams p|) by lia.
    * apply auxt => //. 
  - unfold tCaseBrsProp_k.
    revert brs cl2. clear cl1 cl1'.
    rewrite /test_branch_k.
    fix auxl' 1.
    destruct brs; constructor; [|apply auxl'].
    simpl in cl2. move/andP: cl2  => [/andP [clctx clt] cll].
    split.
    move: clctx.
    generalize (bcontext b).
    fix auxl'' 1.
    destruct l; [constructor|]. simpl.
    move=>  /andP []. simpl. move=> /= clctx /andP [] clt' cll'.
    destruct c as [na [bod|] ty]; simpl in *;
    constructor; simpl.
    split; apply auxt; rewrite Nat.sub_0_r //.
    eapply Alli_shift, Alli_impl; eauto. eapply auxl'' => //. simpl.
    intros n x. now replace (Nat.pred #|l| - n + #|pparams p|) with (#|l| - S n + #|pparams p|) by lia.
    repeat split. rewrite Nat.sub_0_r. apply auxt => //.
    eapply Alli_shift, Alli_impl; eauto. eapply auxl'' => //. simpl.
    intros n x. now replace (Nat.pred #|l| - n + #|pparams p|) with (#|l| - S n + #|pparams p|) by lia.
    eapply auxt => //.
    simpl in cl2. now move/andP: cl2 => [].

  - red.
    rewrite fix_context_length.
    revert clt.
    generalize (#|mfix|).
    revert mfix.
    fix auxm 1. 
    destruct mfix; intros; constructor.
    simpl in clt. move/andP: clt  => [clt cll].
    simpl in clt. move/andP: clt. intuition auto.
    move/andP: clt => [cd cmfix]. apply auxm; auto.

  - red.
    rewrite fix_context_length.
    revert clt.
    generalize (#|mfix|).
    revert mfix.
    fix auxm 1. 
    destruct mfix; intros; constructor.
    simpl in clt. move/andP: clt  => [clt cll].
    simpl in clt. move/andP: clt. intuition auto.
    move/andP: clt => [cd cmfix]. apply auxm; auto.
Defined.

Lemma term_noccur_between_list_ind :
  forall (P : nat -> nat -> term -> Type), 
    (forall k n (i : nat), i < k \/ k + n <= i -> P k n (tRel i)) ->
    (forall k n (i : ident), P k n (tVar i)) ->
    (forall k n (id : nat) (l : list term), All (P k n) l -> P k n (tEvar id l)) ->
    (forall k n s, P k n (tSort s)) ->
    (forall k n (na : aname) (t : term), P k n t -> forall t0 : term, P (S k) n t0 -> P k n (tProd na t t0)) ->
    (forall k n (na : aname) (t : term), P k n t -> forall t0 : term, P (S k) n t0 -> P k n (tLambda na t t0)) ->
    (forall k n (na : aname) (t : term),
        P k n t -> forall t0 : term, P k n t0 -> forall t1 : term, P (S k) n t1 -> P k n (tLetIn na t t0 t1)) ->
    (forall k n (t u : term), P k n t -> P k n u -> P k n (tApp t u)) ->
    (forall k n s (u : list Level.t), P k n (tConst s u)) ->
    (forall k n (i : inductive) (u : list Level.t), P k n (tInd i u)) ->
    (forall k n (i : inductive) (c : nat) (u : list Level.t), P k n (tConstruct i c u)) ->
    (forall k n (ci : case_info) (p : predicate term),
        tCasePredProp_k (fun k' => P k' n) k p -> forall t0 : term, P k n t0 -> 
        forall l : list (branch term),
        tCaseBrsProp_k (fun k' => P k' n) p k l -> P k n (tCase ci p t0 l)) ->
    (forall k n (s : projection) (t : term), P k n t -> P k n (tProj s t)) ->
    (forall k n (m : mfixpoint term) (i : nat), tFixProp (P k n) (P (#|fix_context m| + k) n) m -> P k n (tFix m i)) ->
    (forall k n (m : mfixpoint term) (i : nat), tFixProp (P k n) (P (#|fix_context m| + k) n) m -> P k n (tCoFix m i)) ->
    (forall k n p, P k n (tPrim p)) ->
    forall k n (t : term), noccur_between k n t -> P k n t.
Proof.
  intros until t. revert k n t.
  fix auxt 3.
  move auxt at top.
  intros k n t.
  destruct t; intros clt;  match goal with
                 H : _ |- _ => apply H
              end; auto; simpl in clt; 
            try move/andP: clt => [cl1 cl2]; 
            try move/andP: cl1 => [cl1 cl1'];
            try solve[apply auxt; auto];
              simpl in *.

  - move/orP: clt => [cl|cl]. 
    now apply Nat.ltb_lt in cl; eauto.
    now apply Nat.leb_le in cl; eauto. 
   
  - revert l clt.
    fix auxl' 1.
    destruct l; constructor; [|apply auxl'].
    apply auxt. simpl in clt. now move/andP: clt  => [clt cll].
    now move/andP: clt => [clt cll].
  
  - move/andP: cl1 => /= []/andP[] clpars clctx clret.
    split.
    * revert clpars. generalize (pparams p).
      fix auxl' 1.
      case => [|t' ts] /= //; cbn => /andP[] Ht' Hts; constructor; [apply auxt|apply auxl'] => //.
    * split; [|now apply auxt].
      move: clctx.
      clear -auxt.
      unfold onctx_k, ondecl.
      generalize (pcontext p).
      fix auxl' 1; destruct l; [constructor|]; simpl; rewrite ?Nat.sub_0_r.
      move/andP => [] tl /andP [tdef tty]. constructor.
      + rewrite Nat.sub_0_r. simpl. split; [apply auxt|]; tas.
        destruct (decl_body c); simpl in *; auto. exact tt.
      + eapply Alli_shift, Alli_impl; eauto. simpl.
        intros n' x.
        now replace (Nat.pred #|l| - n' + #|pparams p|) with (#|l| - S n' + #|pparams p|).

  - revert brs cl2. clear cl1 cl1'.
    unfold test_branch_k, tCaseBrsProp_k.
    fix auxl' 1.
    destruct brs; constructor; [|apply auxl'].
    simpl in cl2. move/andP: cl2  => [/andP [clctx clb] cll].
    split.
    * unfold onctx_k, ondecl.
      revert clctx.
      generalize (bcontext b).
      fix auxl'' 1; destruct l; [constructor|]; simpl; rewrite ?Nat.sub_0_r.
      move/andP => [] tl /andP [tdef tty]. constructor.
      + rewrite Nat.sub_0_r. simpl. split; [apply auxt|]; tas.
        destruct (decl_body c); simpl in *; auto. exact tt.
      + eapply Alli_shift, Alli_impl; eauto. simpl.
        intros n' x.
        now replace (Nat.pred #|l| - n' + #|pparams p|) with (#|l| - S n' + #|pparams p|).
    * eapply auxt => //.
    * now simpl in cl2; move/andP: cl2 => [].

  - red.
    rewrite fix_context_length.
    revert clt.
    generalize (#|mfix|).
    revert mfix.
    fix auxm 1. 
    destruct mfix; intros; constructor.
    simpl in clt. move/andP: clt  => [clt cll].
    simpl in clt. move/andP: clt. intuition auto.
    move/andP: clt => [cd cmfix]. apply auxm; auto.

  - red.
    rewrite fix_context_length.
    revert clt.
    generalize (#|mfix|).
    revert mfix.
    fix auxm 1. 
    destruct mfix; intros; constructor.
    simpl in clt. move/andP: clt  => [clt cll].
    simpl in clt. move/andP: clt. intuition auto.
    move/andP: clt => [cd cmfix]. apply auxm; auto.
Defined.
