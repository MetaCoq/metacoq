(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICWeakeningEnv.

Require Import ssreflect ssrbool.
From Equations Require Import Equations.


Lemma All_forallb_eq_forallb {A} (P : A -> Type) (p q : A -> bool) l :
  All P l ->
  (forall x, P x -> p x = q x) ->
  forallb p l = forallb q l.
Proof.
  induction 1; simpl; intuition (f_equal; auto).
Qed.

(** * Lemmas about the [closedn] predicate *)

Definition closed_decl n d :=
  option_default (closedn n) d.(decl_body) true && closedn n d.(decl_type).

Definition closedn_ctx n ctx :=
  forallb id (mapi (fun k d => closed_decl (n + k) d) (List.rev ctx)).

Notation closed_ctx ctx := (closedn_ctx 0 ctx).

Lemma lift_decl_closed n k d : closed_decl k d -> lift_decl n k d = d.
Proof.
  case: d => na [body|] ty; rewrite /closed_decl /lift_decl /map_decl /=.
  - move/andP => [cb cty]. now rewrite !lift_closed //.
  - move=> cty; now rewrite !lift_closed //.
Qed.

Lemma closed_decl_upwards k d : closed_decl k d -> forall k', k <= k' -> closed_decl k' d.
Proof.
  case: d => na [body|] ty; rewrite /closed_decl /=.
  - move/andP => [cb cty] k' lek'. do 2 rewrite (@closed_upwards k) //.
  - move=> cty k' lek'; rewrite (@closed_upwards k) //.
Qed.

Lemma closed_ctx_lift n k ctx : closedn_ctx k ctx -> lift_context n k ctx = ctx.
Proof.
  induction ctx in n, k |- *; auto.
  unfold closed_ctx, id. rewrite lift_context_snoc.
  simpl.
  rewrite /mapi mapi_rec_app forallb_app List.rev_length /= /snoc Nat.add_0_r.
  move/andb_and => /= [Hctx /andb_and [Ha _]].
  f_equal. rewrite lift_decl_closed. apply: closed_decl_upwards; eauto. lia. 
  reflexivity.
  rewrite IHctx // lift_decl_closed //. 
Qed.

Lemma map_decl_ext' f g k d : closed_decl k d -> 
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

Lemma closedn_lift n k k' t : closedn k t -> closedn (k + n) (lift n k' t).
Proof.
  revert k.
  induction t in n, k' |- * using term_forall_list_ind; intros;
    simpl in *; rewrite -> ?andb_and in *;
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length, ?Nat.add_assoc;
    simpl closed in *; solve_all;
    unfold test_def, test_snd in *;
      try solve [simpl lift; simpl closed; f_equal; auto; repeat (rtoProp; solve_all)]; try easy.

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
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length, ?Nat.add_assoc in *;
    simpl closed in *; repeat (rtoProp; solve_all); try change_Sk;
    unfold test_def, on_snd, test_snd in *; simpl in *; eauto with all.

  - revert H0.
    elim (Nat.leb_spec k n0); intros. simpl in *.
    elim (Nat.ltb_spec); auto. apply Nat.ltb_lt in H1. intros. lia.
    revert H1. simpl. elim (Nat.ltb_spec); auto. intros. apply Nat.ltb_lt. lia.
  - specialize (IHt2 n (S k) (S k')). eauto with all.
  - specialize (IHt2 n (S k) (S k')). eauto with all.
  - specialize (IHt3 n (S k) (S k')). eauto with all.
  - rtoProp. solve_all. specialize (b0 n (#|m| + k) (#|m| + k')). eauto with all.
  - rtoProp. solve_all. specialize (b0 n (#|m| + k) (#|m| + k')). eauto with all.
Qed.

Lemma closedn_mkApps k f u:
  closedn k f -> forallb (closedn k) u ->
  closedn k (mkApps f u).
Proof.
  induction u in k, f |- *; simpl; auto.
  move=> Hf /andb_and[Ha Hu]. apply IHu. simpl. now rewrite Hf Ha. auto.
Qed.

Lemma closedn_mkApps_inv k f u:
  closedn k (mkApps f u) ->
  closedn k f && forallb (closedn k) u.
Proof.
  induction u in k, f |- *; simpl; auto.
  - now rewrite andb_true_r.
  - move/IHu/andb_and => /= [/andb_and[Hf Ha] Hu].
    now rewrite Hf Ha Hu.
Qed.

Lemma closedn_subst_eq s k k' t :
  forallb (closedn k) s -> 
  closedn (k + k' + #|s|) t =
  closedn (k + k') (subst s k' t).
Proof.
  intros Hs. solve_all. revert Hs.
  induction t in k' |- * using term_forall_list_ind; intros;
    simpl in *;
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length;
    simpl closed in *; try change_Sk;
    unfold test_def, on_snd, test_snd in *; simpl in *; eauto 4 with all.

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

  - rewrite forallb_map.
    eapply All_forallb_eq_forallb; eauto.

  - specialize (IHt2 (S k')).
    rewrite <- Nat.add_succ_comm in IHt2.
    rewrite IHt1 // IHt2 //.
  - specialize (IHt2 (S k')).
    rewrite <- Nat.add_succ_comm in IHt2.
    rewrite IHt1 // IHt2 //.
  - specialize (IHt3 (S k')).
    rewrite <- Nat.add_succ_comm in IHt3.
    rewrite IHt1 // IHt2 // IHt3 //.
  - rewrite IHt1 // IHt2 //.
    rewrite forallb_map. simpl.
    bool_congr. eapply All_forallb_eq_forallb; eauto.
  - rewrite forallb_map. simpl.
    eapply All_forallb_eq_forallb; eauto. simpl.
    intros x [h1 h2]. rewrite h1 //.
    specialize (h2 (#|m| + k')).
    rewrite Nat.add_assoc in h2.
    rewrite (Nat.add_comm k #|m|) in h2. 
    rewrite -> !Nat.add_assoc in *.
    rewrite h2 //.
  - rewrite forallb_map. simpl.
    eapply All_forallb_eq_forallb; eauto. simpl.
    intros x [h1 h2]. rewrite h1 //.
    specialize (h2 (#|m| + k')).
    rewrite Nat.add_assoc in h2.
    rewrite (Nat.add_comm k #|m|) in h2. 
    rewrite -> !Nat.add_assoc in *.
    rewrite h2 //.
Qed.

Lemma closedn_subst_eq' s k k' t :
  closedn (k + k') (subst s k' t) ->
  closedn (k + k' + #|s|) t.
Proof.
  intros Hs. solve_all. revert Hs.
  induction t in k' |- * using term_forall_list_ind; intros;
    simpl in *;
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length;
    simpl closed in *; repeat (rtoProp; f_equal; solve_all);  try change_Sk;
    unfold test_def, on_snd, test_snd in *; simpl in *; eauto 4 with all.

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
  - move/andP: b => [hty hbod]. rewrite a0 //.
    specialize (b0 (#|m| + k')).
    rewrite Nat.add_assoc (Nat.add_comm k #|m|) in b0. 
    rewrite -> !Nat.add_assoc in *.
    rewrite b0 //. now autorewrite with len in hbod.
  - move/andP: b => [hty hbod]. rewrite a0 //.
    specialize (b0 (#|m| + k')).
    rewrite Nat.add_assoc (Nat.add_comm k #|m|) in b0. 
    rewrite -> !Nat.add_assoc in *.
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

Local Open Scope sigma.

Require Import Morphisms.
    Instance Upn_ext n : Proper (`=1` ==> `=1`) (Upn n).
    Proof.
      unfold Upn. reduce_goal. now rewrite H.
    Qed.

    Instance Up_ext : Proper (`=1` ==> `=1`) Up.
    Proof.
      unfold Up. reduce_goal. unfold subst_compose, subst_cons.
      destruct a. reflexivity. now rewrite H.
    Qed.

    Lemma Upn_S σ n : ⇑^(S n) σ =1 ⇑ ⇑^n σ.
    Proof.
      rewrite Upn_Up. induction n in σ |- *. rewrite !Upn_0. now eapply Up_ext.
      rewrite Upn_Up. rewrite IHn. eapply Up_ext. now rewrite Upn_Up.
    Qed.
    Hint Rewrite Upn_0 Upn_S : sigma.

    Ltac sigma := autorewrite with sigma.

Instance up_proper k : Proper (`=1` ==> `=1`) (up k).
Proof. reduce_goal. now apply up_ext. Qed.

Lemma Upn_Upn k k' σ : ⇑^(k + k') σ =1 ⇑^k (⇑^k' σ).
Proof.
  setoid_rewrite <- up_Upn. rewrite -(@up_Upn k').
  symmetry; apply up_up.
Qed.
Hint Rewrite Upn_Upn : sigma.

Lemma inst_closed σ k t : closedn k t -> t.[⇑^k σ] = t.
Proof.
  intros Hs.
  induction t in σ, k, Hs |- * using term_forall_list_ind; intros; sigma;
    simpl in *;
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_length, ?Nat.add_assoc in *;
    simpl closed in *; repeat (rtoProp; f_equal; solve_all); try change_Sk;
    unfold test_def, on_snd, test_snd in *; simpl in *; eauto with all.

  - revert Hs.
    unfold Upn.
    elim (Nat.ltb_spec n k); intros. simpl in *.
    destruct (subst_consn_lt (l := idsn k) (i := n)) as [t [Heq Heq']].
    + now rewrite idsn_length //.
    + now rewrite idsn_lt in Heq.
    + discriminate.
  - specialize (IHt2 σ (S k) H0). rewrite -{2}IHt2. now sigma.
  - specialize (IHt2 σ (S k) H0). rewrite -{2}IHt2. now sigma.
  - specialize (IHt3 σ (S k) H0). rewrite -{2}IHt3. now sigma.
  - rtoProp. specialize (b0 σ (#|m| + k) H0). eapply map_def_id_spec; auto.
    revert b0. now sigma.
  - rtoProp. specialize (b0 σ (#|m| + k) H0). eapply map_def_id_spec; auto.
    revert b0. now sigma.
Qed.

Lemma closedn_subst_instance_constr k t u :
  closedn k (subst_instance_constr u t) = closedn k t.
Proof.
  revert k.
  induction t in |- * using term_forall_list_ind; intros;
    simpl in *; rewrite -> ?andb_and in *;
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def;
    try solve [repeat (f_equal; eauto)];  simpl closed in *;
      try rewrite ?map_length; intuition auto.

  - rewrite forallb_map; eapply All_forallb_eq_forallb; eauto.
  - red in X. rewrite forallb_map. f_equal; eauto using All_forallb_eq_forallb.
    f_equal; eauto.
  - red in X. rewrite forallb_map.
    eapply All_forallb_eq_forallb; eauto.
    unfold test_def, map_def. simpl.
    do 3 (f_equal; intuition eauto).
  - red in X. rewrite forallb_map.
    eapply All_forallb_eq_forallb; eauto.
    unfold test_def, map_def. simpl.
    do 3 (f_equal; intuition eauto).
Qed.

Lemma closed_map_subst_instance n u l : 
  forallb (closedn n) (map (subst_instance_constr u) l) = 
  forallb (closedn n) l.
Proof.
  induction l; simpl; auto.
  now rewrite closedn_subst_instance_constr IHl.
Qed.

Lemma destArity_spec ctx T :
  match destArity ctx T with
  | Some (ctx', s) => it_mkProd_or_LetIn ctx T = it_mkProd_or_LetIn ctx' (tSort s)
  | None => True
  end.
Proof.
  induction T in ctx |- *; simpl; try easy.
  specialize (IHT2 (ctx,, vass na T1)). now destruct destArity.
  specialize (IHT3 (ctx,, vdef na T1 T2)). now destruct destArity.
Qed.

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
  induction al; try constructor. unfold closedn_ctx.
  unfold snoc. simpl. rewrite mapi_app forallb_app. simpl.
  rewrite Nat.add_0_r. cbn.
  move/andP: p => [] Ht _. rewrite List.rev_length Ht.
  unfold closed_ctx in IHal.
  now rewrite IHal.
  unfold closed_ctx. simpl.
  rewrite mapi_app forallb_app /= List.rev_length /closed_decl /= Nat.add_0_r p.
  unfold closed_ctx in IHal.
  now rewrite IHal.
  intros.
  unfold app_context in *. subst Γ'. simpl.
  unfold closed_ctx. specialize (IHΓ (ctx ++ a :: Γ) wfΓ' (ctx ++ [a])).
  rewrite -app_assoc in IHΓ. specialize (IHΓ eq_refl al).
  simpl. rewrite mapi_app forallb_app.
  move/andP: IHΓ => []. unfold closed_ctx.
  simpl. rewrite List.rev_length rev_app_distr mapi_app forallb_app /=.
  intros ->. move/andP => [/andP [->]] _. simpl.
  intros. red. red in b. rewrite -b.
  rewrite !mapi_rev !forallb_rev. f_equal. eapply mapi_ext. intros.
  f_equal. lia.
Qed.

Require Import ssrbool.

Lemma closedn_ctx_cons n d Γ : closedn_ctx n (d :: Γ) = closedn_ctx n Γ && closed_decl (n + #|Γ|) d.
Proof.
  unfold closedn_ctx.
  simpl. rewrite mapi_app. rewrite forallb_app /= andb_true_r.
  now rewrite Nat.add_0_r List.rev_length.
Qed.

Lemma closedn_ctx_app n Γ Γ' :
  closedn_ctx n (Γ ,,, Γ') =
  closedn_ctx n Γ && closedn_ctx (n + #|Γ|) Γ'.
Proof.
  rewrite /closedn_ctx /app_context /= List.rev_app_distr mapi_app forallb_app /=.
  bool_congr.
  rewrite List.rev_length.
  f_equal. eapply mapi_ext. intros.
  f_equal. lia.
Qed.

Lemma closedn_mkProd_or_LetIn (Γ : context) d T :
    closed_decl #|Γ| d ->
    closedn (S #|Γ|) T -> closedn #|Γ| (mkProd_or_LetIn d T).
Proof.
  destruct d as [na [b|] ty]; simpl in *. unfold closed_decl.
  simpl. now move/andP => [] -> ->.
  simpl. now move/andP => [] /= _ -> ->.
Qed.

Lemma closedn_mkLambda_or_LetIn (Γ : context) d T :
    closed_decl #|Γ| d ->
    closedn (S #|Γ|) T -> closedn #|Γ| (mkLambda_or_LetIn d T).
Proof.
  destruct d as [na [b|] ty]; simpl in *. unfold closed_decl.
  simpl. now move/andP => [] -> ->.
  simpl. now move/andP => [] /= _ -> ->.
Qed.

Lemma closedn_it_mkProd_or_LetIn
      (Γ : context) (ctx : list context_decl) T :
    closedn_ctx #|Γ| ctx ->
    closedn (#|Γ| + #|ctx|) T -> closedn #|Γ| (it_mkProd_or_LetIn ctx T).
Proof.
  induction ctx in Γ, T |- *. simpl.
  - now rewrite Nat.add_0_r.
  - rewrite closedn_ctx_cons. move/andP => [] cctx ca cT.
    apply (IHctx Γ (mkProd_or_LetIn a T) cctx).
    simpl in cT. rewrite <- app_length.
    eapply closedn_mkProd_or_LetIn;
      now rewrite app_length // plus_n_Sm.
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
    rewrite /closed_decl /map_decl /= Nat.add_0_r List.rev_length subst_context_length.
    inv X'. unfold closed_decl in H0. simpl in H0.
    rewrite List.rev_length Nat.add_0_r in H0.
    move/andP: H0 => [Hl Hr].
    rewrite !closedn_subst /= ?H //; eapply closed_upwards; eauto; try lia.
  - intros. eapply Alli_app in X as [X X'].
    rewrite subst_context_snoc. simpl. eapply Alli_app_inv.
    eapply IHΔ'; eauto. constructor; [|constructor].
    simpl. 
    rewrite /closed_decl /map_decl /= Nat.add_0_r List.rev_length subst_context_length.
    inv X'. unfold closed_decl in H0. simpl in H0.
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
    now rewrite /closed_decl Nat.add_0_r /=.
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

Lemma closedn_ctx_spec k Γ : closedn_ctx k Γ <~> Alli closed_decl k (List.rev Γ).
Proof.
  split.
  - induction Γ as [|d ?].
    + constructor.
    + rewrite closedn_ctx_cons => /andP [clΓ cld].
      simpl in *. eapply Alli_app_inv; simpl; eauto.
      repeat constructor. now rewrite List.rev_length.
  - induction Γ in k |- * => //.
    simpl. move/Alli_app => [clΓ cld].
    simpl. depelim cld. rewrite List.rev_length Nat.add_comm in i.
    now rewrite closedn_ctx_cons IHΓ.
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

Lemma context_assumptions_app Γ Δ : context_assumptions (Γ ++ Δ) = 
  context_assumptions Γ + context_assumptions Δ.
Proof.
  induction Γ as [|[? [] ?] ?]; simpl; auto.
Qed.

Lemma weaken_env_prop_closed {cf:checker_flags} : 
  weaken_env_prop (lift_typing (fun (_ : global_env_ext) (Γ : context) (t T : term) =>
  closedn #|Γ| t && closedn #|Γ| T)).
Proof. repeat red. intros. destruct t; red in X0; eauto. Qed.

Lemma declared_projection_closed_ind {cf:checker_flags} {Σ : global_env_ext} {mdecl idecl p pdecl} : 
  wf Σ.1 ->
  declared_projection Σ.1 mdecl idecl p pdecl ->
  Forall_decls_typing
  (fun _ (Γ : context) (t T : term) =>
  closedn #|Γ| t && closedn #|Γ| T) Σ.1 ->
  closedn (S (ind_npars mdecl)) pdecl.2.
Proof.
  intros wfΣ isdecl X0.
  pose proof (declared_projection_inv weaken_env_prop_closed wfΣ X0 isdecl) as onp.
  set (declared_inductive_inv _ wfΣ X0 _) as oib in *.
  clearbody oib.
  have onpars := onParams (declared_minductive_inv weaken_env_prop_closed wfΣ X0 isdecl.p1.p1).
  have parslen := onNpars (declared_minductive_inv weaken_env_prop_closed wfΣ X0 isdecl.p1.p1).
  simpl in onp. destruct (ind_cshapes oib) as [|? []] eqn:Heq; try contradiction.
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

Lemma typecheck_closed `{cf : checker_flags} :
  env_prop (fun Σ Γ t T =>
              closedn #|Γ| t && closedn #|Γ| T)
           (fun Σ Γ _ => closed_ctx Γ).
Proof.
  assert (X := weaken_env_prop_closed).
  apply typing_ind_env; intros * wfΣ Γ wfΓ *; simpl; intros; rewrite -> ?andb_and in *; try solve [intuition auto].

  - induction X0; simpl; auto; rewrite (closedn_ctx_app _ Γ [_]); simpl.
    unfold closedn_ctx at 2; simpl. rewrite IHX0. unfold id; simpl.
    move/andP: p => [ct cs]. now rewrite /closed_decl /= Nat.add_0_r ct.
    move/andP: p => [ct cs]. now rewrite {2}/closedn_ctx /closed_decl /= Nat.add_0_r IHX0 ct.

  - pose proof (nth_error_Some_length H).
    elim (Nat.ltb_spec n #|Γ|); intuition auto. all: try lia. clear H1.

    induction Γ in n, H, H0, H2 |- *. rewrite nth_error_nil in H. discriminate.
    destruct n.
    simpl in H. noconf H. simpl.
    rewrite -Nat.add_1_r. apply closedn_lift.
    rewrite closedn_ctx_cons in H0. move/andP: H0 => [_ ca].
    destruct a as [na [b|] ty]. simpl in ca.
    rewrite /closed_decl /= in ca.
    now move/andP: ca => [_ cty].
    now rewrite /closed_decl /= in ca.
    simpl.
    rewrite -Nat.add_1_r. 
    rewrite -(simpl_lift _ (S n) 0 1 0); try lia.
    apply closedn_lift. apply IHΓ; auto.
    rewrite closedn_ctx_cons in H0.
    now move/andP: H0 => [H0 _]. simpl in H2; lia.

  - intuition auto.
    generalize (closedn_subst [u] #|Γ| 0 B). rewrite Nat.add_0_r.
    move=> Hs. apply: Hs => /=. rewrite H0 => //.
    rewrite Nat.add_1_r. auto.

  - rewrite closedn_subst_instance_constr.
    eapply lookup_on_global_env in X0; eauto.
    destruct X0 as [Σ' [HΣ' IH]].
    repeat red in IH. destruct decl, cst_body. simpl in *.
    rewrite -> andb_and in IH. intuition auto.
    eauto using closed_upwards with arith.
    simpl in *.
    repeat red in IH. destruct IH as [s Hs].
    rewrite -> andb_and in Hs. intuition auto.
    eauto using closed_upwards with arith.

  - rewrite closedn_subst_instance_constr.
    eapply declared_inductive_inv in X0; eauto.
    apply onArity in X0. repeat red in X0.
    destruct X0 as [s Hs]. rewrite -> andb_and in Hs.
    intuition eauto using closed_upwards with arith.

  - destruct isdecl as [Hidecl Hcdecl].
    apply closedn_subst0.
    + unfold inds. clear. simpl. induction #|ind_bodies mdecl|. constructor.
      simpl. now rewrite IHn.
    + rewrite inds_length.
      rewrite closedn_subst_instance_constr.
      eapply declared_inductive_inv in X0; eauto.
      pose proof X0.(onConstructors) as XX.
      eapply All2_nth_error_Some in Hcdecl; eauto.
      destruct Hcdecl as [? [? ?]]. cbn in *.
      destruct o as [? ? ? [s Hs] _]. rewrite -> andb_and in Hs.
      apply proj1 in Hs.
      rewrite arities_context_length in Hs.
      eauto using closed_upwards with arith.

  - intuition auto.
    + solve_all. unfold test_snd. simpl in *.
      rtoProp; eauto.
    + apply closedn_mkApps; auto.
      rewrite forallb_app. simpl. rewrite H2.
      rewrite forallb_skipn; auto.
      now apply closedn_mkApps_inv in H9.

  - intuition auto.
    apply closedn_subst0.
    + simpl. apply closedn_mkApps_inv in H3.
      rewrite forallb_rev H2. apply H3.
    + rewrite closedn_subst_instance_constr.
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

Lemma on_global_env_impl `{checker_flags} Σ P Q :
  (forall Σ Γ t T, on_global_env P Σ.1 -> P Σ Γ t T -> Q Σ Γ t T) ->
  on_global_env P Σ -> on_global_env Q Σ.
Proof.
  intros X X0.
  simpl in *. induction X0; constructor; auto.
  clear IHX0. destruct d; simpl.
  - destruct c; simpl. destruct cst_body; simpl in *.
    red in o |- *. simpl in *. now eapply X.
    red in o |- *. simpl in *. now eapply X.
  - red in o. simpl in *.
    destruct o0 as [onI onP onNP].
    constructor; auto.
    -- eapply Alli_impl. exact onI. eauto. intros.
       refine {| ind_indices := X1.(ind_indices);
                 ind_arity_eq := X1.(ind_arity_eq);
                 ind_cshapes := X1.(ind_cshapes) |}.
       --- apply onArity in X1. unfold on_type in *; simpl in *.
           now eapply X.
       --- pose proof X1.(onConstructors) as X11. red in X11.
          eapply All2_impl; eauto.
          simpl. intros. destruct X2 as [? ? ? ?]; unshelve econstructor; eauto.
          * apply X; eauto.
          * clear -X0 X on_cargs. revert on_cargs.
            generalize (cshape_args y), (cshape_sorts y).
            induction c; destruct l; simpl; auto;
              destruct a as [na [b|] ty]; simpl in *; auto;
          split; intuition eauto.
          * clear -X0 X on_cindices.
            revert on_cindices.
            generalize (List.rev  (lift_context #|cshape_args y| 0 (ind_indices X1))).
            generalize (cshape_indices y).
            induction 1; simpl; constructor; auto.
       --- simpl; intros. pose (onProjections X1 H0). simpl in *; auto.
       --- destruct X1. simpl. unfold check_ind_sorts in *.
           destruct Universe.is_prop, Universe.is_sprop; auto.
           split.
           * apply ind_sorts.
           * destruct indices_matter; auto.
             eapply type_local_ctx_impl. eapply ind_sorts. auto.
      --- eapply X1.(onIndices).
    -- red in onP. red.
       eapply All_local_env_impl. eauto.
       intros. now apply X.
Qed.


Lemma declared_decl_closed `{checker_flags} {Σ : global_env} {cst decl} :
  wf Σ ->
  lookup_env Σ cst = Some decl ->
  on_global_decl (fun Σ Γ b t => closedn #|Γ| b && option_default (closedn #|Γ|) t true)
                 (Σ, universes_decl_of_decl decl) cst decl.
Proof.
  intros.
  eapply weaken_lookup_on_global_env; try red; eauto.
  eapply on_global_env_impl; cycle 1.
  apply (env_prop_sigma _ _ typecheck_closed _ X).
  red; intros. unfold lift_typing in *. destruct T; intuition auto with wf.
  destruct X1 as [s0 Hs0]. simpl. rtoProp; intuition.
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
  simpl in cl. rewrite /closedn_ctx /mapi mapi_rec_app /= forallb_app in cl.
  move/andP: cl => [cll clr]. simpl in clr. unfold id in clr.
  rewrite List.rev_length in clr. rewrite Nat.add_0_r in clr.
  move/andP : clr => [clr _]. eapply closed_decl_upwards; eauto. lia.
  f_equal.
  rewrite IHl; auto.
  simpl in cl. rewrite /closedn_ctx /mapi mapi_rec_app /= forallb_app in cl.
  move/andP: cl => [cll _]. simpl in cll.
  apply cll.
  intros. apply Hfg. simpl; lia. simpl. lia. simpl.
  eapply closed_decl_upwards; eauto. lia.
Qed.


Definition closed_inductive_body mdecl idecl :=
  closedn 0 idecl.(ind_type) &&
  forallb (fun cdecl => 
    closedn (#|arities_context mdecl.(ind_bodies)|) (cdecl_type cdecl)) idecl.(ind_ctors) &&
  forallb (fun x => closedn (S (ind_npars mdecl)) x.2) idecl.(ind_projs).

Definition closed_inductive_decl mdecl :=
  closed_ctx (ind_params mdecl) &&
  forallb (closed_inductive_body mdecl) (ind_bodies mdecl). 
  

Lemma closedn_All_local_env (ctx : list context_decl) :
  All_local_env 
    (fun (Γ : context) (b : term) (t : option term) =>
      closedn #|Γ| b && option_default (closedn #|Γ|) t true) ctx ->
    closedn_ctx 0 ctx.
Proof.
  induction 1. constructor.
  rewrite /closedn_ctx /= mapi_app forallb_app /= [forallb _ _]IHX /id /closed_decl /=.
  now rewrite Nat.add_0_r List.rev_length t0.
  rewrite /closedn_ctx /= mapi_app forallb_app /= [forallb _ _]IHX /id /closed_decl /=.
  now rewrite Nat.add_0_r List.rev_length t1.
Qed.

Lemma skipn_0 {A} (l : list A) : skipn 0 l = l.
Proof. reflexivity. Qed.

Lemma declared_projection_closed {cf:checker_flags} {Σ : global_env_ext} {mdecl idecl p pdecl} : 
  wf Σ.1 ->
  declared_projection Σ.1 mdecl idecl p pdecl ->
  closedn (S (ind_npars mdecl)) pdecl.2.
Proof.
  intros; eapply declared_projection_closed_ind; eauto.
  eapply typecheck_closed; eauto. eapply type_Prop.
Qed.

Lemma declared_inductive_closed {cf:checker_flags} {Σ : global_env_ext} {mdecl mind} : 
  wf Σ.1 ->
  declared_minductive Σ.1 mind mdecl ->
  closed_inductive_decl mdecl.
Proof.
  intros wfΣ decl.
  pose proof (declared_decl_closed wfΣ decl) as decl'.
  red in decl'.
  unfold closed_inductive_decl.
  apply andb_and. split. apply onParams in decl'.
  now apply closedn_All_local_env in decl'; auto.
  apply onInductives in decl'.
  eapply All_forallb.
  
  assert (Alli (fun i =>  declared_inductive Σ.1 mdecl {| inductive_mind := mind; inductive_ind := i |}) 
    0 (ind_bodies mdecl)).
  { eapply forall_nth_error_Alli. intros.
    split; auto. }
  eapply Alli_mix in decl'; eauto. clear X.
  clear decl.
  eapply Alli_All; eauto.
  intros n x [decli oib].
  rewrite /closed_inductive_body.
  apply andb_and; split. apply andb_and. split.
  - apply onArity in oib. hnf in oib.
    now move/andP: oib => [].
  - pose proof (onConstructors oib).
    red in X. eapply All_forallb. eapply All2_All_left; eauto.
    intros cdecl cs X0; eapply on_ctype in X0.
    now move/andP: X0 => [].
  - eapply All_forallb.
    pose proof (onProjections oib).
    destruct (eq_dec (ind_projs x) []) as [->|eq]; try constructor.
    specialize (X eq). clear eq.
    destruct (ind_cshapes oib) as [|? []]; try contradiction.
    apply on_projs in X.
    assert (Alli (fun i pdecl => declared_projection Σ.1 mdecl x 
     (({| inductive_mind := mind; inductive_ind := n |}, mdecl.(ind_npars)), i) pdecl)
      0 (ind_projs x)).
    { eapply forall_nth_error_Alli.
      intros. split; auto. }
    eapply (Alli_All X0). intros.
    now eapply declared_projection_closed in H.
Qed.

Lemma rev_subst_instance_context {u Γ} :
  List.rev (subst_instance_context u Γ) = subst_instance_context u (List.rev Γ).
Proof.
  unfold subst_instance_context, map_context.
  now rewrite map_rev.
Qed.

Lemma closedn_subst_instance_context {k Γ u} :
  closedn_ctx k (subst_instance_context u Γ) = closedn_ctx k Γ.
Proof.
  unfold closedn_ctx; f_equal.
  rewrite rev_subst_instance_context.
  rewrite mapi_map. apply mapi_ext.
  intros n [? [] ?]; unfold closed_decl; cbn.
  all: now rewrite !closedn_subst_instance_constr.
Qed.

Lemma subject_closed `{checker_flags} {Σ Γ t T} : 
  wf Σ.1 ->
  Σ ;;; Γ |- t : T ->
  closedn #|Γ| t.
Proof.
  move=> wfΣ c.
  pose proof (typing_wf_local c).
  apply typecheck_closed in c; eauto.
  now move: c => [_ /andP [ct _]].
Qed.

Lemma type_closed `{checker_flags} {Σ Γ t T} : 
  wf Σ.1 ->
  Σ ;;; Γ |- t : T ->
  closedn #|Γ| T.
Proof.
  move=> wfΣ c.
  pose proof (typing_wf_local c).
  apply typecheck_closed in c; eauto.
  now move: c => [_ /andP [_ ct]].
Qed.

Lemma isType_closed {cf:checker_flags} {Σ Γ T} : wf Σ.1 -> isType Σ Γ T -> closedn #|Γ| T.
Proof. intros wfΣ [s Hs]. now eapply subject_closed in Hs. Qed.

Lemma closed_wf_local `{checker_flags} {Σ Γ} :
  wf Σ.1 ->
  wf_local Σ Γ ->
  closed_ctx Γ.
Proof.
  intros wfΣ. unfold closed_ctx, mapi. intros wf. generalize 0.
  induction wf; intros n; auto; unfold closed_ctx, snoc; simpl;
    rewrite mapi_rec_app forallb_app; unfold id, closed_decl.
  - simpl.
    destruct t0 as [s Hs].
    eapply typecheck_closed in Hs as [closedΓ tcl]; eauto.
    rewrite -> andb_and in *. simpl in *; rewrite andb_true_r in tcl |- *.
    simpl in *. intuition auto.
    + apply IHwf.
    + erewrite closed_upwards; eauto. rewrite List.rev_length. lia.
  - simpl. eapply typecheck_closed in t1 as [closedΓ tcl]; eauto.
    rewrite -> andb_and in *. intuition auto.
    + apply IHwf.
    + erewrite closed_upwards; eauto.
      * erewrite closed_upwards; eauto.
        rewrite List.rev_length. lia.
      * rewrite List.rev_length. lia.
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

Lemma ctx_inst_closed {cf:checker_flags} (Σ : global_env_ext) Γ i Δ : 
  wf Σ.1 -> ctx_inst (lift_typing typing) Σ Γ i Δ -> All (closedn #|Γ|) i.
Proof.
  intros wfΣ; induction 1; auto; constructor; auto.
  now eapply subject_closed in p.
Qed.

Lemma closedn_ctx_lift n k k' Γ : closedn_ctx k Γ ->
  closedn_ctx (n + k) (lift_context n k' Γ).
Proof.
  induction Γ as [|d ?]; simpl; auto; rewrite lift_context_snoc !closedn_ctx_cons /=;
    move/andP=> [clΓ cld]; rewrite IHΓ //;
  autorewrite with len in cld.
  move: cld;  rewrite /closed_decl. simpl.
  move/andP=> [clb clt]; apply andb_and; split.
  destruct (decl_body d) => /= //. simpl in clb |- *.
  eapply (closedn_lift n) in clb.
  autorewrite with len. now rewrite -Nat.add_assoc Nat.add_comm.
  eapply (closedn_lift n) in clt.
  autorewrite with len. now rewrite -Nat.add_assoc Nat.add_comm.
Qed.

Lemma closedn_ctx_subst k k' s Γ : 
  closedn_ctx (k + k' + #|s|) Γ ->
  forallb (closedn k) s ->
  closedn_ctx (k + k') (subst_context s k' Γ).
Proof.
  induction Γ as [|d ?] in k' |- *; simpl; auto; rewrite subst_context_snoc !closedn_ctx_cons /=;
  move/andP=> [clΓ cld]  cls; rewrite IHΓ //;
  autorewrite with len in cld.
  move: cld;  rewrite /closed_decl. simpl.
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

Lemma declared_constant_closed_type {cf:checker_flags} :
  forall Σ cst decl,
    wf Σ ->
    declared_constant Σ cst decl ->
    closed decl.(cst_type).
Proof.
  intros Σ cst decl hΣ h.
  unfold declared_constant in h.
  eapply lookup_on_global_env in h. 2: eauto.
  destruct h as [Σ' [wfΣ' decl']].
  red in decl'. red in decl'.
  destruct decl as [ty bo un]. simpl in *.
  destruct bo as [t|].
  - now eapply type_closed in decl'.
  - cbn in decl'. destruct decl' as [s h].
    now eapply subject_closed in h.
Qed.

Lemma declared_inductive_closed_type {cf:checker_flags} :
  forall Σ mdecl ind idecl,
    wf Σ ->
    declared_inductive Σ mdecl ind idecl ->
    closed idecl.(ind_type).
Proof.
  intros Σ mdecl ind idecl hΣ h.
  unfold declared_inductive in h. destruct h as [h1 h2].
  unfold declared_minductive in h1.
  eapply lookup_on_global_env in h1. 2: eauto.
  destruct h1 as [Σ' [wfΣ' decl']].
  red in decl'. destruct decl' as [h ? ? ?].
  eapply Alli_nth_error in h. 2: eassumption.
  simpl in h. destruct h as [? ? ? [? h] ? ? ?].
  eapply typecheck_closed in h as [? e]. 2: auto. 
  move/andP in e. destruct e. assumption.
Qed.

Lemma declared_inductive_closed_constructors {cf:checker_flags} :
  forall Σ ind mdecl idecl,
      wf Σ ->
      declared_inductive Σ mdecl ind idecl ->
      All (fun '(na, t, n) => closedn #|arities_context mdecl.(ind_bodies)| t)
          idecl.(ind_ctors).
Proof.
  intros Σ ind mdecl idecl hΣ [hmdecl hidecl].
  eapply (declared_inductive_closed (Σ:=empty_ext Σ)) in hmdecl; auto.
  unfold closed_inductive_decl in hmdecl.
  move/andP: hmdecl => [clpars clbodies].
  eapply nth_error_forallb in clbodies; eauto.
  erewrite hidecl in clbodies. simpl in clbodies.
  unfold closed_inductive_body in clbodies.
  move/andP: clbodies => [/andP [_ cl] _].
  eapply forallb_All in cl. apply (All_impl cl).
  now intros [[? ?] ?]; simpl.
Qed.

Lemma declared_minductive_closed_inds {cf:checker_flags} :
  forall Σ ind mdecl u,
    wf Σ ->
    declared_minductive Σ (inductive_mind ind) mdecl ->
    forallb (closedn 0) (inds (inductive_mind ind) u (ind_bodies mdecl)).
Proof.
  intros Σ ind mdecl u hΣ h.
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

Lemma declared_inductive_closed_inds {cf:checker_flags} :
  forall Σ ind mdecl idecl u,
      wf Σ ->
      declared_inductive Σ mdecl ind idecl ->
      forallb (closedn 0) (inds (inductive_mind ind) u (ind_bodies mdecl)).
Proof.
  intros Σ ind mdecl idecl u hΣ h.
  unfold declared_inductive in h. destruct h as [hmdecl hidecl].
  eapply declared_minductive_closed_inds in hmdecl. all: eauto.
Qed.

Lemma declared_constructor_closed_type {cf:checker_flags} :
  forall Σ mdecl idecl c cdecl u,
    wf Σ ->
    declared_constructor Σ mdecl idecl c cdecl ->
    closed (type_of_constructor mdecl cdecl c u).
Proof.
  intros Σ mdecl idecl c cdecl u hΣ h.
  unfold declared_constructor in h.
  destruct c as [i ci]. simpl in h. destruct h as [hidecl hcdecl].
  eapply declared_inductive_closed_constructors in hidecl as h. 2: auto.
  unfold type_of_constructor. simpl.
  destruct cdecl as [[id t'] arity]. simpl.
  destruct idecl as [na ty ke ct pr]. simpl in *.
  eapply All_nth_error in h. 2: eassumption.
  simpl in h.
  eapply closedn_subst0.
  - eapply declared_inductive_closed_inds. all: eauto.
  - simpl. rewrite inds_length. rewrite arities_context_length in h.
    rewrite closedn_subst_instance_constr. assumption.
Qed.

Lemma declared_projection_closed_type {cf:checker_flags} :
  forall Σ mdecl idecl p pdecl,
    wf Σ ->
    declared_projection Σ mdecl idecl p pdecl ->
    closedn (S (ind_npars mdecl)) pdecl.2.
Proof.
  intros Σ mdecl idecl p pdecl hΣ decl.
  now eapply (declared_projection_closed (Σ:=empty_ext Σ)) in decl.
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
    (forall k (p : inductive * nat) (t : term),
        P k t -> forall t0 : term, P k t0 -> forall l : list (nat * term),
            tCaseBrsProp (P k) l -> P k (tCase p t t0 l)) ->
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
              simpl in *. now apply Nat.ltb_lt in clt. 
  revert l clt.
  fix auxl' 1.
  destruct l; constructor; [|apply auxl'].
  apply auxt. simpl in clt. now move/andP: clt  => [clt cll].
  now  move/andP: clt => [clt cll].

  red.
  revert brs cl2.
  fix auxl' 1.
  destruct brs; constructor; [|apply auxl'].
  simpl in cl2. move/andP: cl2  => [clt cll].
  apply auxt, clt. move/andP: cl2  => [clt cll].
  apply cll.

  red.
  rewrite fix_context_length.
  revert clt.
  generalize (#|mfix|).
  revert mfix.
  fix auxm 1. 
  destruct mfix; intros; constructor.
  simpl in clt. move/andP: clt  => [clt cll].
  simpl in clt. move/andP: clt. intuition auto.
  move/andP: clt => [cd cmfix]. apply auxm; auto.

  red.
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
