(* Distributed under the terms of the MIT license. *)
From Coq Require Import Morphisms.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICInduction
  PCUICLiftSubst PCUICUnivSubst PCUICContextRelation PCUICCumulativity
  PCUICTyping PCUICClosed PCUICEquality PCUICWeakeningEnv
  PCUICSigmaCalculus PCUICClosed PCUICOnFreeVars.

Require Import ssreflect ssrbool.
From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.
Set Equations With UIP.

(** * Type preservation for σ-calculus operations *)

Open Scope sigma_scope.
Set Keyed Unification.

Set Default Goal Selector "!".

Lemma rename_mkApps :
  forall f t l,
    rename f (mkApps t l) = mkApps (rename f t) (map (rename f) l).
Proof.
  intros f t l.
  autorewrite with sigma. f_equal.
Qed.

Lemma rename_subst_instance :
  forall u t f,
    rename f (subst_instance u t) = subst_instance u (rename f t).
Proof.
  intros u t f.
  rewrite /subst_instance /=.
  induction t in f |- * using term_forall_list_ind.
  all: try solve [
    simpl ;
    rewrite ?IHt ?IHt1 ?IHt2 ;
    easy
  ].
  - simpl. f_equal. induction X.
    + reflexivity.
    + simpl. f_equal ; easy.
  - simpl. rewrite IHt. f_equal.
    * unfold map_predicate, rename_predicate; destruct p; simpl; f_equal; solve_all.
    * induction X0.
      + reflexivity.
      + simpl. f_equal. 2: easy.
        destruct x. unfold rename_branch, map_branch. simpl in *.
        f_equal; solve_all.
  - simpl. f_equal.
    rewrite map_length.
    generalize #|m|. intro k.
    induction X. 1: reflexivity.
    destruct p, x. unfold map_def in *.
    simpl in *. f_equal. all: easy.
  - simpl. f_equal.
    rewrite map_length.
    generalize #|m|. intro k.
    induction X. 1: reflexivity.
    destruct p, x. unfold map_def in *.
    simpl in *. f_equal. all: easy.
Qed.

Definition rename_context f (Γ : context) : context :=
  fold_context_k (fun i => rename (shiftn i f)) Γ.

Definition rename_decl f d := map_decl (rename f) d.

Lemma rename_context_length :
  forall σ Γ,
    #|rename_context σ Γ| = #|Γ|.
Proof.
  intros σ Γ. unfold rename_context.
  apply fold_context_k_length.
Qed.
Hint Rewrite rename_context_length : sigma wf.

Lemma rename_context_snoc0 :
  forall f Γ d,
    rename_context f (d :: Γ) =
    rename_context f Γ ,, rename_decl (shiftn #|Γ| f) d.
Proof.
  intros f Γ d.
  unfold rename_context. now rewrite fold_context_k_snoc0. 
Qed.
Hint Rewrite rename_context_snoc0 : sigma.

Lemma rename_context_snoc r Γ d : rename_context r (Γ ,, d) = rename_context r Γ ,, map_decl (rename (shiftn #|Γ| r)) d.
Proof.
  unfold snoc. apply rename_context_snoc0.
Qed.
Hint Rewrite rename_context_snoc : sigma.

Lemma rename_context_alt r Γ :
  rename_context r Γ =
  mapi (fun k' d => map_decl (rename (shiftn (Nat.pred #|Γ| - k') r)) d) Γ.
Proof.
  unfold rename_context. apply fold_context_k_alt.
Qed.

Definition rename_telescope r Γ :=
  mapi (fun i => map_decl (rename (shiftn i r))) Γ.

Lemma rename_context_telescope r Γ : List.rev (rename_context r Γ) = rename_telescope r (List.rev Γ).
Proof.
  rewrite !rename_context_alt /rename_telescope.
  rewrite mapi_rev.
  f_equal. apply mapi_ext => k' d.
  apply map_decl_ext => t. lia_f_equal.
Qed.

Lemma rename_subst0 :
  forall f l t,
    rename f (subst0 l t) =
    subst0 (map (rename f) l) (rename (shiftn #|l| f) t).
Proof.
  intros f l t.
  autorewrite with sigma.
  eapply inst_ext.
  now rewrite -ren_shiftn up_Upn Upn_comp; len.
Qed.

Lemma rename_subst10 :
  forall f t u,
    rename f (t{ 0 := u }) = (rename (shiftn 1 f) t){ 0 := rename f u }.
Proof.
  intros f t u.
  eapply rename_subst0.
Qed.

Lemma rename_context_nth_error :
  forall f Γ i decl,
    nth_error Γ i = Some decl ->
    nth_error (rename_context f Γ) i =
    Some (rename_decl (shiftn (#|Γ| - S i) f) decl).
Proof.
  intros f Γ i decl h.
  induction Γ in f, i, decl, h |- *.
  - destruct i. all: discriminate.
  - destruct i.
    + simpl in h. inversion h. subst. clear h.
      rewrite rename_context_snoc0. simpl.
      f_equal. f_equal. f_equal. lia.
    + simpl in h. rewrite rename_context_snoc0. simpl.
      eapply IHΓ. eassumption.
Qed.

Lemma rename_context_decl_body :
  forall f Γ i body,
    option_map decl_body (nth_error Γ i) = Some (Some body) ->
    option_map decl_body (nth_error (rename_context f Γ) i) =
    Some (Some (rename (shiftn (#|Γ| - S i) f) body)).
Proof.
  intros f Γ i body h.
  destruct (nth_error Γ i) eqn: e. 2: discriminate.
  simpl in h.
  eapply rename_context_nth_error with (f := f) in e. rewrite e. simpl.
  destruct c as [na bo ty]. simpl in h. inversion h. subst.
  simpl. reflexivity.
Qed.

Lemma map_vass_map_def g l r :
  (mapi (fun i (d : def term) => vass (dname d) (lift0 i (dtype d)))
        (map (map_def (rename r) g) l)) =
  (mapi (fun i d => map_decl (rename (shiftn i r)) d)
        (mapi (fun i (d : def term) => vass (dname d) (lift0 i (dtype d))) l)).
Proof.
  rewrite mapi_mapi mapi_map. apply mapi_ext.
  intros. unfold map_decl, vass; simpl; f_equal.
  sigma. rewrite -Upn_ren. now rewrite shiftn_Upn.
Qed.

Lemma rename_fix_context r :
  forall (mfix : list (def term)),
    fix_context (map (map_def (rename r) (rename (shiftn #|mfix| r))) mfix) =
    rename_context r (fix_context mfix).
Proof.
  intros mfix. unfold fix_context.
  rewrite map_vass_map_def rev_mapi.
  fold (fix_context mfix).
  rewrite (rename_context_alt r (fix_context mfix)).
  unfold map_decl. now rewrite mapi_length fix_context_length.
Qed.

Section Renaming.

Context `{cf : checker_flags}.

Lemma eq_term_upto_univ_rename Σ :
  forall Re Rle napp u v f,
    eq_term_upto_univ_napp Σ Re Rle napp u v ->
    eq_term_upto_univ_napp Σ Re Rle napp (rename f u) (rename f v).
Proof.
  intros Re Rle napp u v f h.
  induction u in v, napp, Rle, f, h |- * using term_forall_list_ind.
  all: dependent destruction h.
  all: try solve [
    simpl ; constructor ; eauto
  ].
  - simpl. constructor.
    induction X in a, args' |- *.
    + inversion a. constructor.
    + inversion a. subst. simpl. constructor.
      all: eauto.
  - simpl. constructor. all: eauto.
    * rewrite /rename_predicate.
      destruct X; destruct e as [? [? [ectx ?]]].
      rewrite (All2_fold_length ectx). red.
      intuition auto; simpl; solve_all.
      eapply All2_fold_mapi.
      eapply All2_fold_impl_onctx; tea.
      solve_all. eapply compare_decl_map.
      eapply compare_decl_impl_ondecl; tea; solve_all.
    * induction X0 in a, brs' |- *.
      + inversion a. constructor.
      + inversion a. subst. simpl.
        destruct X1 as [a0 e0], p0.
        constructor; eauto.
        split; eauto.
        ** solve_all.
          eapply All2_fold_mapi.
          eapply All2_fold_impl_onctx; tea.
          solve_all. eapply compare_decl_map.
          eapply compare_decl_impl_ondecl; tea; solve_all.
        ** simpl.
          rewrite (All2_fold_length a0).
          now eapply e1. 
  - simpl. constructor.
    apply All2_length in a as e. rewrite <- e.
    generalize #|m|. intro k.
    induction X in mfix', a, f, k |- *.
    + inversion a. constructor.
    + inversion a. subst.
      simpl. constructor.
      * unfold map_def. intuition eauto.
      * eauto.
  - simpl. constructor.
    apply All2_length in a as e. rewrite <- e.
    generalize #|m|. intro k.
    induction X in mfix', a, f, k |- *.
    + inversion a. constructor.
    + inversion a. subst.
      simpl. constructor.
      * unfold map_def. intuition eauto.
      * eauto.
Qed.

(* Notion of valid renaming without typing information. *)

(** We might want to relax this to allow "renamings" that change e.g. 
  the universes or names, but should generalize the renaming operation at 
  the same time *)
(** Remark: renaming allows instantiating an assumption with a well-typed body *)

Definition urenaming (P : nat -> bool) Γ Δ f :=
  forall i decl, P i -> 
    nth_error Δ i = Some decl ->
    ∑ decl', (nth_error Γ (f i) = Some decl') ×
    (eq_binder_annot decl.(decl_name) decl'.(decl_name) ×
    ((rename (f ∘ rshiftk (S i)) decl.(decl_type) = 
     rename (rshiftk (S (f i))) decl'.(decl_type)) ×
      on_Some_or_None (fun body => Some (rename (f ∘ rshiftk (S i)) body) =
         option_map (rename (rshiftk (S (f i)))) decl'.(decl_body)) decl.(decl_body))).

Lemma urenaming_impl :
  forall (P P' : nat -> bool) Γ Δ f,
    (forall i, P' i -> P i) ->
    urenaming P Δ Γ f ->
    urenaming P' Δ Γ f.
Proof.
  intros P P' Γ Δ f hP h.
  intros i decl p e.
  specialize (h i decl (hP _ p) e) as [decl' [h1 [h2 h3]]].
  exists decl'. split ; [| split ]; eauto.
Qed.

(* Definition of a good renaming with respect to typing *)
Definition renaming P Σ Γ Δ f :=
  wf_local Σ Γ × urenaming P Γ Δ f.

Lemma inst_closed σ k t : closedn k t -> t.[⇑^k σ] = t.
Proof.
  intros Hs.
  induction t in σ, k, Hs |- * using term_forall_list_ind; intros; sigma;
    simpl in *;
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_branch_map_branch,
      ?map_length, ?Nat.add_assoc in *;
      unfold test_def, map_branch, test_branch_k, test_predicate_k in *; simpl in *; eauto with all;
    simpl closed in *; repeat (rtoProp; f_equal; solve_all); try change_Sk.
    
  - revert Hs.
    unfold Upn.
    elim (Nat.ltb_spec n k) => //; intros; simpl in *.
    now apply subst_idsn_consn_lt.
  - specialize (IHt2 σ (S k) H0). rewrite -{2}IHt2. now sigma.
  - specialize (IHt2 σ (S k) H0). rewrite -{2}IHt2. now sigma.
  - specialize (IHt3 σ (S k) H0). rewrite -{2}IHt3. now sigma.
  - eapply map_predicate_shift_id_spec.
    * solve_all.
    * solve_all.
    * setoid_rewrite up_Upn; setoid_rewrite <- Upn_Upn.
      fold (shiftf (fun k => inst (⇑^k σ)) k).
      eapply mapi_context_eqP_test_id_spec; tea. simpl; solve_all.
    * specialize (e σ (#|pcontext p| + k)). rewrite -{2}e; now sigma.
  - eapply map_branch_shift_id_spec.
    * setoid_rewrite up_Upn; setoid_rewrite <- Upn_Upn.
      fold (shiftf (fun k => inst (⇑^k σ)) k).
      eapply mapi_context_eqP_test_id_spec; tea. simpl; solve_all.
    * specialize (b0 σ (#|bcontext x| + k)).
      now rewrite up_Upn -Upn_Upn.
  - rtoProp. specialize (b0 σ (#|m| + k) H0).
    revert b0. now sigma.
  - rtoProp. specialize (b0 σ (#|m| + k) H0). 
    revert b0. now sigma.
Qed.
  
Lemma rename_closedn :
  forall f n t,
    closedn n t ->
    rename (shiftn n f) t = t.
Proof.
  intros f n t e.
  autorewrite with sigma.
  erewrite <- inst_closed with (σ := ren f) by eassumption.
  eapply inst_ext. intro i.
  unfold ren, shiftn, Upn, subst_consn, subst_compose, shift, shiftk.
  rewrite idsn_length.
  destruct (Nat.ltb_spec i n).
  - rewrite nth_error_idsn_Some. all: auto.
  - rewrite nth_error_idsn_None. 1: lia.
    simpl. reflexivity.
Qed.

Lemma rename_closed :
  forall f t,
    closed t ->
    rename f t = t.
Proof.
  intros f t h.
  replace (rename f t) with (rename (shiftn 0 f) t).
  - apply rename_closedn. assumption.
  - now sigma.
Qed.

Lemma rename_closed_decl k f d : closed_decl k d -> map_decl (rename (shiftn k f)) d = d.
Proof.
  rewrite /map_decl.  
  destruct d as [? [] ?] => /=.
  - move/andP=> [] clt clty.
    rewrite !rename_closedn //.
  - move=> clt. rewrite !rename_closedn //.
Qed.

Lemma rename_closedn_ctx f n Γ : 
  closedn_ctx n Γ -> 
  rename_context (shiftn n f) Γ = Γ.
Proof.
  rewrite test_context_k_eq /rename_context.
  apply alli_fold_context_k.
  intros. rewrite shiftn_add.
  intros. apply rename_closed_decl.
  now rewrite Nat.add_comm.
Qed.

Lemma rename_closedn_terms f n ts : 
  forallb (closedn n) ts -> map (rename (shiftn n f)) ts = ts.
Proof.
  solve_all. now apply rename_closedn.
Qed.

Lemma rename_closed_extended_subst f Γ : 
  closed_ctx Γ ->
  map (rename (shiftn (context_assumptions Γ) f)) (extended_subst Γ 0) = extended_subst Γ 0. 
Proof.
  intros cl. apply rename_closedn_terms.
  now apply (closedn_extended_subst_gen Γ 0 0).
Qed.

Arguments Nat.sub !_ !_.

Lemma urenaming_vass :
  forall P Γ Δ na A f,
    urenaming P Γ Δ f ->
    urenaming (shiftnP 1 P) (Γ ,, vass na (rename f A)) (Δ ,, vass na A) (shiftn 1 f).
Proof.
  intros P Γ Δ na A f h. unfold urenaming in *.
  intros [|i] decl hP e.
  - simpl in e. inversion e. subst. clear e.
    simpl. eexists. split. 1: reflexivity.
    repeat split.
    now sigma.
  - simpl in e. simpl.
    replace (i - 0) with i by lia.
    eapply h in e as [decl' [? [? [h1 h2]]]].
    2:{ unfold shiftnP in hP. simpl in hP. now rewrite Nat.sub_0_r in hP. }
    eexists. split. 1: eassumption.
    repeat split.
    + tas.
    + setoid_rewrite shiftn_1_S.
      rewrite -rename_compose h1.
      now sigma.
    + move: h2.
      destruct (decl_body decl) => /= //; destruct (decl_body decl') => /= //.
      setoid_rewrite shiftn_1_S => [=] h2.
      now rewrite -rename_compose h2; sigma.
Qed.

Lemma renaming_vass :
  forall P Σ Γ Δ na A f,
    wf_local Σ (Γ ,, vass na (rename f A)) ->
    renaming P Σ Γ Δ f ->
    renaming (shiftnP 1 P) Σ (Γ ,, vass na (rename f A)) (Δ ,, vass na A) (shiftn 1 f).
Proof.
  intros P Σ Γ Δ na A f hΓ [? h].
  split. 1: auto.
  eapply urenaming_vass; assumption.
Qed.

Lemma urenaming_vdef :
  forall P Γ Δ na b B f,
    urenaming P Γ Δ f ->
    urenaming (shiftnP 1 P) (Γ ,, vdef na (rename f b) (rename f B)) (Δ ,, vdef na b B) (shiftn 1 f).
Proof.
  intros P Γ Δ na b B f h. unfold urenaming in *.
  intros [|i] decl hP e.
  - simpl in e. inversion e. subst. clear e.
    simpl. eexists. split. 1: reflexivity.
    repeat split.
    + now sigma.
    + simpl. now sigma.
  - simpl in e. simpl.
    replace (i - 0) with i by lia.
    eapply h in e as [decl' [? [? [h1 h2]]]].
    2:{ rewrite /shiftnP /= Nat.sub_0_r // in hP. }
    eexists. split. 1: eassumption.
    repeat split => //.
    + setoid_rewrite shiftn_1_S.
      rewrite -rename_compose h1.
      now sigma.
    + move: h2.
      destruct (decl_body decl) => /= //; destruct (decl_body decl') => /= //.
      setoid_rewrite shiftn_1_S => [=] h2.
      now rewrite -rename_compose h2; sigma.
Qed.

Lemma renaming_vdef :
  forall P Σ Γ Δ na b B f,
    wf_local Σ (Γ ,, vdef na (rename f b) (rename f B)) ->
    renaming P Σ Γ Δ f ->
    renaming (shiftnP 1 P) Σ (Γ ,, vdef na (rename f b) (rename f B)) (Δ ,, vdef na b B) (shiftn 1 f).
Proof.
  intros P Σ Γ Δ na b B f hΓ [? h].
  split. 1: auto.
  eapply urenaming_vdef; assumption.
Qed.

Lemma urenaming_ext :
  forall P P' Γ Δ f g,
    P =1 P' ->
    f =1 g ->
    urenaming P Δ Γ f ->
    urenaming P' Δ Γ g.
Proof.
  intros P P' Γ Δ f g hP hfg h.
  intros i decl p e.
  rewrite -hP in p.
  specialize (h i decl p e) as [decl' [? [h1 [h2 h3]]]].
  exists decl'. repeat split => //.
  - rewrite <- (hfg i). assumption.
  - rewrite <- (hfg i). rewrite <- h2.
    eapply rename_ext. intros j. symmetry. apply hfg.
  - move: h3. destruct (decl_body decl) => /= //.
    rewrite /rshiftk.
    destruct (decl_body decl') => /= //.
    intros [=]; f_equal.
    now setoid_rewrite <- (hfg _).
Qed.

Lemma renaming_extP P P' Σ Γ Δ f :
  P =1 P' ->
  renaming P Σ Γ Δ f -> renaming P' Σ Γ Δ f.
Proof.
  intros hP; rewrite /renaming.
  intros []; split; eauto.
  eapply urenaming_ext; eauto. reflexivity.
Qed.

Lemma urenaming_context :
  forall P Γ Δ Ξ f,
    urenaming P Δ Γ f ->
    urenaming (shiftnP #|Ξ| P) (Δ ,,, rename_context f Ξ) (Γ ,,, Ξ) (shiftn #|Ξ| f).
Proof.
  intros P Γ Δ Ξ f h.
  induction Ξ as [| [na [bo|] ty] Ξ ih] in Γ, Δ, f, h |- *.
  - simpl. eapply urenaming_ext. 3: eassumption.
    * now rewrite shiftnP0.
    * intros []. all: reflexivity.
  - simpl. rewrite rename_context_snoc.
    rewrite app_context_cons. simpl. unfold rename_decl. unfold map_decl. simpl.
    eapply urenaming_ext.
    3:{ eapply urenaming_vdef; tea. eapply ih; assumption. }
    * now rewrite shiftnP_add.
    * now rewrite shiftn_add.
  - simpl. rewrite rename_context_snoc.
    rewrite app_context_cons. simpl. unfold rename_decl. unfold map_decl. simpl.
    eapply urenaming_ext.
    3:{eapply urenaming_vass; tea. eapply ih; assumption. }
    * now rewrite shiftnP_add.
    * now rewrite shiftn_add.
Qed.

Definition rename_branch := (map_branch_shift rename shiftn).

(* TODO MOVE *)
Lemma isLambda_rename :
  forall t f,
    isLambda t ->
    isLambda (rename f t).
Proof.
  intros t f h.
  destruct t.
  all: try discriminate.
  simpl. reflexivity.
Qed.

(* TODO MOVE *)
Lemma rename_unfold_fix :
  forall mfix idx narg fn f,
    unfold_fix mfix idx = Some (narg, fn) ->
    unfold_fix (map (map_def (rename f) (rename (shiftn #|mfix| f))) mfix) idx
    = Some (narg, rename f fn).
Proof.
  intros mfix idx narg fn f h.
  unfold unfold_fix in *. rewrite nth_error_map.
  case_eq (nth_error mfix idx).
  2: intro neq ; rewrite neq in h ; discriminate.
  intros d e. rewrite e in h.
  inversion h. clear h.
  simpl.
  f_equal. f_equal.
  rewrite rename_subst0. rewrite fix_subst_length.
  f_equal.
  unfold fix_subst. rewrite map_length.
  generalize #|mfix| at 2 3. intro n.
  induction n.
  - reflexivity.
  - simpl.
    f_equal. rewrite IHn. reflexivity.
Qed.

(* TODO MOVE *)
Lemma decompose_app_rename :
  forall f t u l,
    decompose_app t = (u, l) ->
    decompose_app (rename f t) = (rename f u, map (rename f) l).
Proof.
  assert (aux : forall f t u l acc,
    decompose_app_rec t acc = (u, l) ->
    decompose_app_rec (rename f t) (map (rename f) acc) =
    (rename f u, map (rename f) l)
  ).
  { intros f t u l acc h.
    induction t in acc, h |- *.
    all: try solve [ simpl in * ; inversion h ; reflexivity ].
    simpl. simpl in h. specialize IHt1 with (1 := h). assumption.
  }
  intros f t u l.
  unfold decompose_app.
  eapply aux.
Qed.

(* TODO MOVE *)
Lemma isConstruct_app_rename :
  forall t f,
    isConstruct_app t ->
    isConstruct_app (rename f t).
Proof.
  intros t f h.
  unfold isConstruct_app in *.
  case_eq (decompose_app t). intros u l e.
  apply decompose_app_rename with (f := f) in e as e'.
  rewrite e'. rewrite e in h. simpl in h.
  simpl.
  destruct u. all: try discriminate.
  simpl. reflexivity.
Qed.

(* TODO MOVE *)
Lemma is_constructor_rename :
  forall n l f,
    is_constructor n l ->
    is_constructor n (map (rename f) l).
Proof.
  intros n l f h.
  unfold is_constructor in *.
  rewrite nth_error_map.
  destruct nth_error.
  - simpl. apply isConstruct_app_rename. assumption.
  - simpl. discriminate.
Qed.

(* TODO MOVE *)
Lemma rename_unfold_cofix :
  forall mfix idx narg fn f,
    unfold_cofix mfix idx = Some (narg, fn) ->
    unfold_cofix (map (map_def (rename f) (rename (shiftn #|mfix| f))) mfix) idx
    = Some (narg, rename f fn).
Proof.
  intros mfix idx narg fn f h.
  unfold unfold_cofix in *. rewrite nth_error_map.
  case_eq (nth_error mfix idx).
  2: intro neq ; rewrite neq in h ; discriminate.
  intros d e. rewrite e in h.
  inversion h.
  simpl. f_equal. f_equal.
  rewrite rename_subst0. rewrite cofix_subst_length.
  f_equal.
  unfold cofix_subst. rewrite map_length.
  generalize #|mfix| at 2 3. intro n.
  induction n.
  - reflexivity.
  - simpl.
    f_equal. rewrite IHn. reflexivity.
Qed.

Definition rename_constructor_body mdecl f c := 
  map_constructor_body #|mdecl.(ind_params)| #|mdecl.(ind_bodies)|
   (fun k => rename (shiftn k f)) c.

Lemma map2_set_binder_name_fold bctx f Γ :
  #|bctx| = #|Γ| ->
  map2 set_binder_name bctx (fold_context_k f Γ) = 
  fold_context_k f (map2 set_binder_name bctx Γ).
Proof.
  intros hl.
  rewrite !fold_context_k_alt mapi_map2 -{1}(map_id bctx).
  rewrite -mapi_cst_map map2_mapi.
  rewrite map2_length; len => //.
  eapply map2i_ext => i x y.
  rewrite hl.
  destruct y; reflexivity.
Qed.

Lemma rename_subst :
  forall f s n t,
    rename (shiftn n f) (subst s n t) =
    subst (map (rename f) s) n (rename (shiftn n (shiftn #|s| f)) t).
Proof.
  intros f s n t.
  autorewrite with sigma.
  eapply inst_ext. intro i. unfold Upn.
  unfold ren, subst_consn, shiftn, subst_compose. simpl.
  rewrite nth_error_map.
  destruct (Nat.ltb_spec i n).
  - rewrite idsn_lt //. simpl.
    destruct (Nat.ltb_spec i n) => //. lia.
  - rewrite nth_error_idsn_None //.
    destruct (Nat.ltb_spec (i - n) #|s|).
    * rewrite nth_error_idsn_None //; try lia.
      len.
      replace (n + (i - n) - n) with (i - n) by lia.
      destruct nth_error eqn:hnth => /=.
      ** sigma. apply inst_ext.
        intros k. cbn.
        elim: (Nat.ltb_spec (n + k) n); try lia.
        intros. eapply nth_error_Some_length in hnth.
        unfold shiftk. lia_f_equal.
      ** eapply nth_error_None in hnth. lia.
    * len.
      replace (n + (#|s| + f (i - n - #|s|)) - n) with
        (#|s| + f (i - n - #|s|)) by lia.
      rewrite nth_error_idsn_None; try lia.
      destruct nth_error eqn:hnth.
      ** eapply nth_error_Some_length in hnth. lia.
      ** simpl.
        eapply nth_error_None in hnth.
        destruct nth_error eqn:hnth'.
        + eapply nth_error_Some_length in hnth'. lia.
        + simpl. unfold shiftk.
          case: Nat.ltb_spec; try lia.
          intros. lia_f_equal.
          assert (n + (i - n - #|s|) - n = (i - n - #|s|)) as -> by lia.
          lia.
Qed.

Lemma rename_context_subst f s Γ : 
  rename_context f (subst_context s 0 Γ) =
  subst_context (map (rename f) s) 0 (rename_context (shiftn #|s| f) Γ).
Proof.
  rewrite !rename_context_alt !subst_context_alt.
  rewrite !mapi_mapi. apply mapi_ext => i x.
  rewrite /subst_decl !compose_map_decl.
  apply map_decl_ext => t.
  len.
  generalize (Nat.pred #|Γ| - i).
  intros.
  now rewrite rename_subst.
Qed.
  
Lemma rename_shiftnk :
  forall f n k t,
    rename (shiftn (n + k) f) (lift n k t) = lift n k (rename (shiftn k f) t).
Proof.
  intros f n k t.
  rewrite !lift_rename.
  autorewrite with sigma.
  rewrite - !Upn_ren. sigma.
  rewrite Upn_compose.
  rewrite -Upn_Upn Nat.add_comm Upn_Upn Upn_compose.
  now rewrite shiftn_Upn.
Qed.

Lemma rename_context_lift f n k Γ : 
  rename_context (shiftn (n + k) f) (lift_context n k Γ) =
  lift_context n k (rename_context (shiftn k f) Γ).
Proof.
  rewrite !rename_context_alt !lift_context_alt.
  rewrite !mapi_mapi. apply mapi_ext => i x.
  rewrite /lift_decl !compose_map_decl.
  apply map_decl_ext => t; len.
  generalize (Nat.pred #|Γ| - i).
  intros.
  rewrite shiftn_add.
  rewrite (Nat.add_comm n k) Nat.add_assoc Nat.add_comm.
  now rewrite rename_shiftnk shiftn_add.
Qed.

Lemma rename_inds f ind pu bodies : map (rename f) (inds ind pu bodies) = inds ind pu bodies.
Proof.
  unfold inds.
  induction #|bodies|; simpl; auto. f_equal.
  apply IHn.
Qed.

Instance rename_context_ext : Proper (`=1` ==> Logic.eq ==> Logic.eq) rename_context.
Proof.
  intros f g Hfg x y ->.
  apply fold_context_k_ext => i t.
  now rewrite Hfg.
Qed.

Lemma rename_context_subst_instance f u Γ : 
  rename_context f (subst_instance u Γ) = 
  subst_instance u (rename_context f Γ).
Proof. unfold rename_context.
  rewrite fold_context_k_map // [subst_instance _ _]map_fold_context_k.
  now setoid_rewrite rename_subst_instance.
Qed.

Lemma rename_context_subst_k f s k Γ : 
  rename_context (shiftn k f) (subst_context s k Γ) =
  subst_context (map (rename f) s) k (rename_context (shiftn (k + #|s|) f) Γ).
Proof.
  rewrite /rename_context /subst_context.
  rewrite !fold_context_k_compose.
  apply fold_context_k_ext => i t.
  rewrite shiftn_add.
  now rewrite rename_subst !shiftn_add Nat.add_assoc.
Qed.
 
Lemma rename_cstr_args mdecl f cdecl : 
  cstr_args (rename_constructor_body mdecl f cdecl) =
  rename_context (shiftn (#|mdecl.(ind_params)| + #|ind_bodies mdecl|) f) (cstr_args cdecl).
Proof. 
  simpl. unfold rename_context.
  apply fold_context_k_ext => i t.
  now rewrite shiftn_add Nat.add_assoc.
Qed.

Lemma rename_case_branch_context_gen ind mdecl f p bctx cdecl :
  closed_ctx (ind_params mdecl) ->
  #|bctx| = #|cstr_args cdecl| ->
  #|pparams p| = context_assumptions (ind_params mdecl) ->
  rename_context f (case_branch_context ind mdecl p bctx cdecl) = 
  case_branch_context ind mdecl (rename_predicate f p) bctx 
    (rename_constructor_body mdecl f cdecl).
Proof.
  intros clpars. unfold case_branch_context, case_branch_context_gen.
  rewrite rename_cstr_args.
  cbn -[fold_context_k].
  intros hlen hlen'.
  rewrite map2_set_binder_name_fold //.
  change (fold_context_k
  (fun i : nat => rename (shiftn i (shiftn (ind_npars mdecl + #|ind_bodies mdecl|) f)))) with
    (rename_context (shiftn (ind_npars mdecl + #|ind_bodies mdecl|) f)).
  rewrite rename_context_subst map_rev //. f_equal.
  unfold id.
  rewrite /expand_lets_ctx /expand_lets_k_ctx.
  simpl. len.
  rewrite rename_context_subst; len.
  rewrite hlen'.
  rewrite -{1}(context_assumptions_subst_instance (puinst p)).
  rewrite rename_closed_extended_subst.
  { now rewrite closedn_subst_instance_context. }
  f_equal.
  rewrite shiftn_add Nat.add_comm.
  rewrite rename_context_lift. f_equal.
  rewrite -rename_context_subst_instance.
  rewrite rename_context_subst_k rename_inds. now len.
Qed.

Lemma rename_reln f ctx n acc :
  forallb (closedn (n + #|ctx|)) acc ->
  map (rename (shiftn (n + #|ctx|) f)) (reln acc n ctx) = 
  reln acc n ctx.
Proof.
  induction ctx in n, acc |- *; simpl; auto.
  - intros clacc. solve_all. now rewrite rename_closedn.
  - intros clacc.
    destruct a as [? [] ?].
    * rewrite Nat.add_succ_r.
      change (S (n + #|ctx|)) with (S n + #|ctx|).
      rewrite Nat.add_1_r IHctx // /= -Nat.add_succ_r //.
    * rewrite Nat.add_succ_r Nat.add_1_r. rewrite (IHctx (S n)) /= // -Nat.add_succ_r //.
      simpl. rewrite clacc andb_true_r.
      eapply Nat.ltb_lt. lia.
Qed.

Lemma rename_to_extended_list f ctx :
  map (rename (shiftn #|ctx| f)) (to_extended_list ctx) = to_extended_list ctx.
Proof.
  unfold to_extended_list, to_extended_list_k.
  now apply (rename_reln _ _ 0).
Qed.

Lemma to_extended_list_rename f ctx :
  to_extended_list (rename_context f ctx) = to_extended_list ctx.
Proof.
  unfold to_extended_list, to_extended_list_k.
  now rewrite (reln_fold _ _ 0).
Qed.

Lemma forget_types_mapi_context (f : nat -> term -> term) (ctx : context) :
  forget_types (mapi_context f ctx) = forget_types ctx.
Proof.
  now rewrite /forget_types map_mapi_context /= mapi_cst_map.
Qed.

Lemma forget_types_map_context (f : term -> term) (ctx : context) :
  forget_types (map_context f ctx) = forget_types ctx.
Proof.
  now rewrite /forget_types map_map_compose.
Qed.

Lemma rename_case_predicate_context {Σ} {wfΣ : wf Σ} {ind mdecl idecl f p} :
  declared_inductive Σ ind mdecl idecl ->
  wf_predicate mdecl idecl p ->
  rename_context f (case_predicate_context ind mdecl idecl p) =
  case_predicate_context ind mdecl idecl (rename_predicate f p).
Proof.
  intros decli wfp.
  unfold case_predicate_context. simpl.
  unfold id. unfold case_predicate_context_gen.
  rewrite /rename_context.
  rewrite -map2_set_binder_name_fold //.
  - len. len. 
    now rewrite -(wf_predicate_length_pcontext wfp).
  - f_equal.
    { now rewrite forget_types_mapi_context. } 
    rewrite /pre_case_predicate_context_gen fold_context_k_snoc0 /= /snoc.
    f_equal.
    * rewrite /map_decl /=. f_equal.
      len. rewrite rename_mkApps /=. f_equal.
      rewrite !map_app !map_map_compose. f_equal.
      + solve_all.
        eapply All_refl => x.
        apply rename_shiftn.
      + now rewrite rename_to_extended_list.
    * rewrite -/(rename_context f _).
      rewrite rename_context_subst rename_context_subst_instance map_rev.
      f_equal. f_equal.
      rewrite List.rev_length rename_closedn_ctx //.
      pose proof (closedn_ctx_expand_lets (ind_params mdecl) (ind_indices idecl)
        (declared_inductive_closed_pars_indices _ decli)).
      rewrite (wf_predicate_length_pars wfp).
      now rewrite (declared_minductive_ind_npars decli).
Qed.

Lemma rename_closed_constructor_body mdecl cdecl f : 
  closed_constructor_body mdecl cdecl ->
  rename_constructor_body mdecl f cdecl = cdecl.
Proof.
  rewrite /closed_constructor_body /rename_constructor_body /map_constructor_body.
  move/andP=> [] /andP [] clctx clind clty.
  destruct cdecl; cbn -[fold_context_k] in *; f_equal.
  + move: clctx. rewrite test_context_k_eq.
    apply alli_fold_context_k => i d cldecl.
    rewrite rename_closed_decl //.
    red; rewrite -cldecl; lia_f_equal.
  + solve_all. rewrite rename_closedn //.
    red; rewrite -H. lia_f_equal.
  + now rewrite rename_closedn.
Qed.

Lemma rename_mkLambda_or_LetIn f d t : 
  rename f (mkLambda_or_LetIn d t) =
  mkLambda_or_LetIn (rename_decl f d) (rename (shiftn 1 f) t).
Proof.
  destruct d as [na [] ty]; rewrite /= /mkLambda_or_LetIn /=; f_equal.
Qed.

Lemma rename_it_mkLambda_or_LetIn f ctx t : 
  rename f (it_mkLambda_or_LetIn ctx t) =
  it_mkLambda_or_LetIn (rename_context f ctx) (rename (shiftn #|ctx| f) t).
Proof.
  move: t.
  induction ctx; simpl => t.
  - now rewrite shiftn0.
  - rewrite /= IHctx rename_context_snoc /snoc /=. f_equal.
    now rewrite rename_mkLambda_or_LetIn /= shiftn_add; len.
Qed.

Lemma rename_mkProd_or_LetIn f d t : 
  rename f (mkProd_or_LetIn d t) =
  mkProd_or_LetIn (rename_decl f d) (rename (shiftn 1 f) t).
Proof.
  destruct d as [na [] ty]; rewrite /= /mkProd_or_LetIn /=; f_equal.
Qed.

Lemma rename_it_mkProd_or_LetIn f ctx t : 
  rename f (it_mkProd_or_LetIn ctx t) =
  it_mkProd_or_LetIn (rename_context f ctx) (rename (shiftn #|ctx| f) t).
Proof.
  move: t.
  induction ctx; simpl => t.
  - now rewrite shiftn0.
  - rewrite /= IHctx rename_context_snoc /snoc /=. f_equal.
    now rewrite rename_mkProd_or_LetIn /= shiftn_add; len.
Qed.

Lemma rename_wf_predicate mdecl idecl f p :
  wf_predicate mdecl idecl p ->
  wf_predicate mdecl idecl (rename_predicate f p).
Proof.
  intros []. split.
  - now len.
  - rewrite forget_types_mapi_context. assumption.
Qed.

Lemma rename_wf_branch cdecl f br :
  wf_branch cdecl br ->
  wf_branch cdecl (rename_branch f br).
Proof.
  unfold wf_branch, wf_branch_gen. simpl.
  rewrite /= forget_types_mapi_context. now simpl.
Qed.

Lemma rename_wf_branches cdecl f brs :
  wf_branches cdecl brs ->
  wf_branches cdecl (map (rename_branch f) brs).
Proof.
  unfold wf_branches, wf_branches_gen.
  intros h. solve_all. eapply Forall2_map_right.
  eapply Forall2_impl; eauto using rename_wf_branch.
Qed.

Lemma rename_compose f f' x : rename f (rename f' x) = rename (f ∘ f') x.
Proof. now rewrite (rename_compose _ _ _). Qed.

Lemma rename_predicate_set_pparams f p params :
  rename_predicate f (set_pparams p params) = 
  set_pparams (rename_predicate f p) (map (rename f) params).
Proof. reflexivity. Qed.

Lemma rename_predicate_set_pcontext f p pcontext' :
  #|pcontext'| = #|p.(pcontext)| ->
  rename_predicate f (set_pcontext p pcontext') = 
  set_pcontext (rename_predicate f p) 
  (mapi_context (fun k => rename (shiftn k f)) pcontext').
Proof. rewrite /rename_predicate /= /set_pcontext. simpl. intros ->. reflexivity. Qed.

Lemma rename_predicate_set_preturn f p pret :
  rename_predicate f (set_preturn p pret) = 
  set_preturn (rename_predicate f p) (rename (shiftn #|pcontext p| f) pret).
Proof. reflexivity. Qed.

Lemma rename_extended_subst f Γ : 
  map (rename (shiftn (context_assumptions Γ) f)) (extended_subst Γ 0) = extended_subst (rename_context f Γ) 0. 
Proof.
  induction Γ as [|[na [b|] ty] Γ]; auto; rewrite rename_context_snoc /=; len.
  - rewrite rename_subst0.
    rewrite IHΓ. len. f_equal. f_equal.
    now rewrite shiftn_add Nat.add_comm rename_shiftnk.
  - f_equal; auto.
    rewrite !(lift_extended_subst _ 1).
    rewrite map_map_compose.
    setoid_rewrite <- (shiftn_add 1 (context_assumptions Γ)).
    setoid_rewrite rename_shiftn.
    rewrite -map_map_compose. now f_equal.
Qed.

Lemma rename_iota_red :
  forall f pars args br,
  #|skipn pars args| = context_assumptions br.(bcontext) ->
  #|bcontext br| = #|br.(bcontext)| ->
  rename f (iota_red pars args br) =
  iota_red pars (map (rename f) args) (rename_branch f br).
Proof.
  intros f pars args br hlen hlen'.
  unfold iota_red.
  rewrite rename_subst0 map_rev map_skipn. f_equal.
  rewrite List.rev_length /expand_lets /expand_lets_k.
  rewrite rename_subst0. len.
  rewrite shiftn_add -hlen Nat.add_comm rename_shiftnk.
  rewrite hlen. rewrite rename_extended_subst.
  now rewrite /rename_context mapi_context_fold.
Qed.

Lemma rename_case_branch_type {Σ} {wfΣ : wf Σ} f (ci : case_info) mdecl idecl p br i cdecl : 
  declared_inductive Σ ci mdecl idecl ->
  wf_predicate mdecl idecl p ->
  wf_branch cdecl br ->
  let ptm := it_mkLambda_or_LetIn (pcontext p) (preturn p) in
  let p' := rename_predicate f p in
  let ptm' := it_mkLambda_or_LetIn (pcontext p') (preturn p') in
  case_branch_type ci mdecl idecl
     (rename_predicate f p) 
     (map_branch_shift rename shiftn f br) 
     ptm' i (rename_constructor_body mdecl f cdecl) =
  map_pair (rename_context f) (rename (shiftn #|bcontext br| f)) 
  (case_branch_type ci mdecl idecl p br ptm i cdecl).
Proof.
  intros decli wfp wfb ptm p' ptm'.
  rewrite /case_branch_type /case_branch_type_gen /map_pair /=.
  rewrite rename_case_branch_context_gen //.
  { eapply (declared_inductive_closed_params decli). }
  { len; now apply wf_branch_length. }
  { rewrite -(declared_minductive_ind_npars decli).
    apply (wf_predicate_length_pars wfp). }
  f_equal.
  { now rewrite forget_types_mapi_context. }
  rewrite rename_mkApps map_app map_map_compose.
  rewrite (wf_branch_length wfb).
  f_equal.
  * rewrite /ptm' /ptm !lift_it_mkLambda_or_LetIn !rename_it_mkLambda_or_LetIn.
    rewrite !lift_rename. f_equal.
    ++ rewrite /p'.
        epose proof (rename_context_lift f #|cstr_args cdecl| 0).
        rewrite Nat.add_0_r in H.
        rewrite H. len.
        rewrite shiftn0 //.
        rewrite mapi_context_fold //.
    ++ rewrite /p'. rewrite Nat.add_0_r. simpl. len.
      now rewrite - !lift_rename shiftn_add -rename_shiftnk Nat.add_comm.
  * rewrite /= rename_mkApps /=. f_equal.
    ++ rewrite !map_map_compose /id. apply map_ext => t.
      rewrite /expand_lets /expand_lets_k.
      rewrite -rename_subst_instance. len.
      rewrite -shiftn_add -shiftn_add.
      rewrite rename_subst map_rev. f_equal.
      rewrite List.rev_length rename_subst.
      rewrite (wf_predicate_length_pars wfp).
      rewrite (declared_minductive_ind_npars decli).
      rewrite -{2}(context_assumptions_subst_instance (puinst p) (ind_params mdecl)).
      rewrite rename_closed_extended_subst. 
      { rewrite closedn_subst_instance_context.
        apply (declared_inductive_closed_params decli). }
      f_equal. len. rewrite !shiftn_add.
      rewrite (Nat.add_comm _ (context_assumptions _)) rename_shiftnk.
      f_equal. rewrite Nat.add_comm rename_subst.
      rewrite rename_inds. f_equal.
      rewrite shiftn_add. len. lia_f_equal.
    ++ unfold id. f_equal. f_equal.
       rewrite map_app map_map_compose.
       rewrite map_map_compose.
       setoid_rewrite rename_shiftn. len. f_equal.
       rewrite rename_to_extended_list.
       now rewrite /to_extended_list /to_extended_list_k reln_fold.
Qed.

Lemma red1_rename :
  forall P Σ Γ Δ u v f,
    wf Σ ->
    urenaming P Δ Γ f ->
    on_free_vars P u ->
    red1 Σ Γ u v ->
    red1 Σ Δ (rename f u) (rename f v).
Proof using cf.
  intros P Σ Γ Δ u v f hΣ hf hav h.
  induction h using red1_ind_all in P, f, Δ, hav, hf |- *.
  all: try solve [
    try (cbn in hav; rtoProp);
    simpl ; constructor ; eapply IHh ;
    try eapply urenaming_vass ;
    try eapply urenaming_vdef ;
    eassumption
  ].
  all:simpl in hav |- *; try toAll.
  - rewrite rename_subst10. constructor.
  - rewrite rename_subst10. constructor.
  - destruct (nth_error Γ i) eqn:hnth; noconf H.
    unfold urenaming in hf.
    specialize hf with (1 := hav) (2 := hnth).
    destruct hf as [decl' [e' [? [hr hbo]]]].
    rewrite H /= in hbo.
    rewrite lift0_rename.
    destruct (decl_body decl') eqn:hdecl => //. noconf hbo.
    sigma in H0. sigma. rewrite H0.
    relativize (t.[_]).
    2:{ setoid_rewrite rshiftk_S. rewrite -rename_inst.
        now rewrite -(lift0_rename (S (f i)) _). }
    constructor. now rewrite e' /= hdecl.
  - rewrite rename_mkApps. simpl.
    rewrite rename_iota_red //.
    change (bcontext br) with (bcontext (rename_branch f br)).
    eapply red_iota; eauto.
    + rewrite nth_error_map H /= //.
      + simpl. now len.
  - rewrite 2!rename_mkApps. simpl.
    econstructor.
    + eapply rename_unfold_fix. eassumption.
    + eapply is_constructor_rename. assumption.
  - rewrite 2!rename_mkApps. simpl.
    eapply red_cofix_case.
    eapply rename_unfold_cofix. eassumption.
  - rewrite 2!rename_mkApps. simpl.
    eapply red_cofix_proj.
    eapply rename_unfold_cofix. eassumption.
  - rewrite rename_subst_instance.
    econstructor.
    + eassumption.
    + rewrite rename_closed. 2: assumption.
      eapply declared_constant_closed_body. all: eauto.
  - rewrite rename_mkApps. simpl.
    econstructor. rewrite nth_error_map. rewrite H. reflexivity.
  - move/and4P: hav=> [hpars hret hc hbrs].
    rewrite rename_predicate_set_pparams. econstructor.
    simpl. eapply OnOne2_map. repeat toAll.
    eapply OnOne2_All_mix_left in X; eauto. solve_all. red; eauto.
  - move/and4P: hav=> [_ _ hpctx _].
    rewrite rename_predicate_set_pcontext.
    { now rewrite -(length_of X). }
    eapply case_red_pcontext.
    eapply OnOne2_local_env_mapi_context.
    eapply OnOne2_local_env_impl_test; tea.
    clear -hf; unfold on_Trel; intros.
    eapply on_one_decl_mapi_context.
    eapply on_one_decl_test_impl; tea => /=.
    intros ? ? ? ?. red. eapply X0; tea.
    rewrite !mapi_context_fold Nat.add_0_r.
    now eapply urenaming_context.
  - move/and4P: hav=> [_ hret _ _].
    rewrite rename_predicate_set_preturn.
    eapply case_red_return; eauto.
    simpl.
    eapply IHh; eauto.
    rewrite mapi_context_fold.
    now eapply urenaming_context.
  - move/and5P: hav=> [_ _ _ _ hbrs].
    eapply case_red_brs; eauto.
    eapply OnOne2_map. toAll.
    eapply OnOne2_All_mix_left in X; tea. clear hbrs.
    solve_all.
    * left. simpl. split; auto; rewrite -b0 //.
      eapply b1; tea.
      rewrite mapi_context_fold. now eapply urenaming_context.
    * right. simpl; rewrite -b1.
      rewrite -(length_of a). split => //.
      eapply OnOne2_local_env_mapi_context.
      eapply OnOne2_local_env_impl_test; tea.
      clear -hf; unfold on_Trel; intros.
      eapply on_one_decl_mapi_context.
      eapply on_one_decl_test_impl; tea => /=.
      intros ? ? ? ?. red. eapply X0; tea.
      rewrite !mapi_context_fold Nat.add_0_r.
      now eapply urenaming_context.
  - eapply OnOne2_All_mix_left in X; eauto.
    constructor.
    eapply OnOne2_map. solve_all. red. eauto.
  - eapply OnOne2_All_mix_left in X; eauto. 
    apply OnOne2_length in X as hl. rewrite <- hl. clear hl.
    generalize #|mfix0|. intro n.
    constructor. eapply OnOne2_map. solve_all.
    red. simpl. destruct x, y; simpl in *; noconf b0. split; auto.
    rewrite /test_def /= in b. move/andP: b => [hty hbod].
    eauto.
  - eapply OnOne2_All_mix_left in X; eauto. 
    apply OnOne2_length in X as hl. rewrite <- hl. clear hl.
    eapply fix_red_body. eapply OnOne2_map. solve_all.
    red. simpl. destruct x, y; simpl in *; noconf b0. split; auto.
    rewrite /test_def /= in b. move/andP: b => [hty hbod].
    eapply b1. 
    * rewrite rename_fix_context. rewrite <- fix_context_length.
      now eapply urenaming_context.
    * now len.
  - eapply OnOne2_All_mix_left in X; eauto. 
    apply OnOne2_length in X as hl. rewrite <- hl. clear hl.
    generalize #|mfix0|. intro n.
    constructor. eapply OnOne2_map. solve_all.
    red. simpl. destruct x, y; simpl in *; noconf b0. split; auto.
    rewrite /test_def /= in b. move/andP: b => [hty hbod].
    eauto.
  - eapply OnOne2_All_mix_left in X; eauto. 
    apply OnOne2_length in X as hl. rewrite <- hl. clear hl.
    eapply cofix_red_body. eapply OnOne2_map. solve_all.
    red. simpl. destruct x, y; simpl in *; noconf b0. split; auto.
    rewrite /test_def /= in b. move/andP: b => [hty hbod].
    eapply b1. 
    * rewrite rename_fix_context. rewrite <- fix_context_length.
      now eapply urenaming_context.
    * now len.
Qed.

Lemma conv_renameP :
  forall P Σ Γ Δ f A B,
    wf Σ.1 ->
    urenaming P Δ Γ f ->
    on_free_vars P A ->
    on_free_vars P B ->
    on_ctx_free_vars P Γ ->
    Σ ;;; Γ |- A = B ->
    Σ ;;; Δ |- rename f A = rename f B.
Proof.
  intros P Σ Γ Δ f A B hΣ hf hA hB hΓ h.
  induction h.
  - eapply conv_refl. eapply eq_term_upto_univ_rename. assumption.
  - eapply conv_red_l.
    + eapply red1_rename. all: try eassumption.
    + apply IHh.
      * eapply (red1_on_free_vars hA); tea.
      * auto.
  - eapply conv_red_r.
    + eapply IHh; eauto. eapply (red1_on_free_vars hB); tea.
    + eapply red1_rename. all: try eassumption.
Qed.

Lemma cumul_renameP :
  forall P Σ Γ Δ f A B,
    wf Σ.1 ->
    urenaming P Δ Γ f ->
    on_free_vars P A ->
    on_free_vars P B ->
    on_ctx_free_vars P Γ ->
    Σ ;;; Γ |- A <= B ->
    Σ ;;; Δ |- rename f A <= rename f B.
Proof.
  intros P Σ Γ Δ f A B hΣ hf hA hB hΓ h.
  induction h.
  - eapply cumul_refl. eapply eq_term_upto_univ_rename. assumption.
  - eapply cumul_red_l.
    + eapply red1_rename. all: try eassumption.
    + apply IHh.
      * eapply (red1_on_free_vars hA); tea.
      * auto.
  - eapply cumul_red_r.
    + eapply IHh; eauto. eapply (red1_on_free_vars hB); tea.
    + eapply red1_rename. all: try eassumption.
Qed.

Lemma cumul_decls_renameP {P Σ Γ Γ' Δ Δ' f} d d' :
    wf Σ.1 ->
    urenaming P Δ Γ f ->
    urenaming P Δ' Γ' f ->
    on_free_vars_decl P d ->
    on_free_vars_decl P d' ->
    on_ctx_free_vars P Γ ->
    cumul_decls Σ Γ Γ' d d' ->
    cumul_decls Σ Δ Δ' (rename_decl f d) (rename_decl f d').
Proof.
  intros wf uren uren' ond ond' onΓ Hd; depelim Hd; constructor; tas;
    (eapply conv_renameP || eapply cumul_renameP); tea.
  * now move/andP: ond => [].
  * now move/andP: ond' => [].
  * now move/andP: ond => [].
  * now move/andP: ond' => [].
Qed.

Lemma conv_decls_renameP {P Σ Γ Γ' Δ Δ' f} d d' :
    wf Σ.1 ->
    urenaming P Δ Γ f ->
    urenaming P Δ' Γ' f ->
    on_free_vars_decl P d ->
    on_free_vars_decl P d' ->
    on_ctx_free_vars P Γ ->
    conv_decls Σ Γ Γ' d d' ->
    conv_decls Σ Δ Δ' (rename_decl f d) (rename_decl f d').
Proof.
  intros wf uren uren' ond ond' onΓ Hd; depelim Hd; constructor; tas;
    (eapply conv_renameP || eapply cumul_renameP); tea.
  * now move/andP: ond => [].
  * now move/andP: ond' => [].
  * now move/andP: ond => [].
  * now move/andP: ond' => [].
Qed.

Lemma on_free_vars_ctx_onctx_k P ctx :
  reflectT (onctx_k (fun k => on_free_vars (shiftnP k P)) 0 ctx) 
    (on_free_vars_ctx P ctx).
Proof.
  rewrite -test_context_k_on_free_vars_ctx.
  apply (onctx_k_P reflectT_pred2).
Qed.

Lemma Alli_helper Q Γ : 
  Alli (fun (i : nat) (d : context_decl) => ondecl (Q (#|Γ| - i + 0)) d) 1 Γ ->
  onctx_k Q 0 Γ.
Proof.
  move/(Alli_shiftn_inv 0 _ 1) => H.
  eapply Alli_impl; tea => n x /=.
  now replace (#|Γ| - S n + 0) with (Nat.pred #|Γ| - n + 0) by lia.
Qed.

Lemma All2_fold_impl_ind_onctx_k Q P P' Γ Δ :  
  onctx_k Q 0 Γ ->
  onctx_k Q 0 Δ ->
  All2_fold P Γ Δ ->
  (forall Γ Δ d d', 
    All2_fold P Γ Δ ->
    onctx_k Q 0 Γ ->
    All2_fold P' Γ Δ ->
    ondecl (Q #|Γ|) d ->
    ondecl (Q #|Δ|) d' ->
    P Γ Δ d d' ->
    P' Γ Δ d d') ->
  All2_fold P' Γ Δ.
Proof.
  intros qΓ qΔ cr Hcr.
  induction cr in qΓ, qΔ |- *; constructor; depelim qΓ; depelim qΔ; intuition eauto;
  rewrite -> Nat.sub_0_r, Nat.add_0_r in *;
  apply Alli_helper in qΓ; apply Alli_helper in qΔ;
  simpl in *; eauto.
Qed.

Lemma ondecl_on_free_vars_decl P d : 
  ondecl (on_free_vars P) d ->
  on_free_vars_decl P d.
Proof.
  rewrite /on_free_vars_decl.
  now case: (ondeclP reflectT_pred).
Qed.

Lemma conv_ctx_renameP {Σ : global_env_ext} {P} {Γ Δ} {L R} f :
  wf Σ.1 ->
  urenaming P Δ Γ f ->
  on_free_vars_ctx P L ->
  on_free_vars_ctx P R ->
  on_ctx_free_vars P Γ ->
  conv_context Σ (Γ ,,, L) (Γ ,,, R) ->
  conv_context Σ (Δ ,,, rename_context f L) (Δ ,,, rename_context f R).
Proof.
  intros wf uren onL onL' onΓ H.
  rewrite /rename_context - !mapi_context_fold.
  pose proof (All2_fold_length H) as hlen.
  len in hlen. assert (#|L| = #|R|) by lia.
  eapply All2_fold_app_inv in H as [_ H] => //.
  eapply All2_fold_app; len => //; pcuic.
  { eapply conv_ctx_refl'. }
  move/on_free_vars_ctx_onctx_k: onL => onL.
  move/on_free_vars_ctx_onctx_k: onL' => onR.

  eapply All2_fold_mapi.
  eapply All2_fold_impl_ind_onctx_k; tea => 
    /= L' R' d d' IH onL' IH' ond ond'.
  simpl.
  rewrite !mapi_context_fold -/(rename_context f L') -/(rename_context f R').
  eapply conv_decls_renameP; eauto.
  + now eapply urenaming_context.
  + rewrite (All2_fold_length IH).
    now eapply urenaming_context.
  + now eapply ondecl_on_free_vars_decl.
  + rewrite (All2_fold_length IH'). 
    now eapply ondecl_on_free_vars_decl.
  + eapply on_ctx_free_vars_extend => //.
    now move/on_free_vars_ctx_onctx_k: onL'.
Qed.

Lemma cumul_ctx_renameP {Σ : global_env_ext} {P} {Γ Δ} {L R} f :
  wf Σ.1 ->
  urenaming P Δ Γ f ->
  on_free_vars_ctx P L ->
  on_free_vars_ctx P R ->
  on_ctx_free_vars P Γ ->
  cumul_context Σ (Γ ,,, L) (Γ ,,, R) ->
  cumul_context Σ (Δ ,,, rename_context f L) (Δ ,,, rename_context f R).
Proof.
  intros wf uren onL onL' onΓ H.
  rewrite /rename_context - !mapi_context_fold.
  pose proof (All2_fold_length H) as hlen.
  len in hlen. assert (#|L| = #|R|) by lia.
  eapply All2_fold_app_inv in H as [_ H] => //.
  eapply All2_fold_app; len => //; pcuic.
  { eapply cumul_ctx_refl'. }
  move/on_free_vars_ctx_onctx_k: onL => onL.
  move/on_free_vars_ctx_onctx_k: onL' => onR.

  eapply All2_fold_mapi.
  eapply All2_fold_impl_ind_onctx_k; tea => 
    /= L' R' d d' IH onL' IH' ond ond'.
  simpl.
  rewrite !mapi_context_fold -/(rename_context f L') -/(rename_context f R').
  eapply cumul_decls_renameP; eauto.
  + now eapply urenaming_context.
  + rewrite (All2_fold_length IH).
    now eapply urenaming_context.
  + now eapply ondecl_on_free_vars_decl.
  + rewrite (All2_fold_length IH'). 
    now eapply ondecl_on_free_vars_decl.
  + eapply on_ctx_free_vars_extend => //.
    now move/on_free_vars_ctx_onctx_k: onL'.
Qed.

Axiom fix_guard_rename : forall P Σ Γ Δ mfix f,
  renaming P Σ Γ Δ f ->
  let mfix' := map (map_def (rename f) (rename (shiftn (List.length mfix) f))) mfix in
  fix_guard Σ Δ mfix ->
  fix_guard Σ Γ mfix'.

Axiom cofix_guard_rename : forall P Σ Γ Δ mfix f,
  renaming P Σ Γ Δ f ->
  let mfix' := map (map_def (rename f) (rename (shiftn (List.length mfix) f))) mfix in
  cofix_guard Σ Δ mfix ->
  cofix_guard Σ Γ mfix'.

Lemma subst1_inst :
  forall t n u,
    t{ n := u } = t.[⇑^n (u ⋅ ids)].
Proof.
  intros t n u.
  unfold subst1. rewrite subst_inst.
  eapply inst_ext. intro i.
  unfold Upn, subst_compose, subst_consn.
  destruct (Nat.ltb_spec0 i n).
  - rewrite -> nth_error_idsn_Some by assumption. reflexivity.
  - rewrite -> nth_error_idsn_None by lia.
    rewrite idsn_length.
    destruct (Nat.eqb_spec (i - n) 0).
    + rewrite e. simpl. reflexivity.
    + replace (i - n) with (S (i - n - 1)) by lia. simpl.
      destruct (i - n - 1) eqn: e.
      * simpl. reflexivity.
      * simpl. reflexivity.
Qed.
(* Hint Rewrite @subst1_inst : sigma. *)

Lemma rename_predicate_preturn f p :
  rename (shiftn #|p.(pcontext)| f) (preturn p) =
  preturn (rename_predicate f p).
Proof. reflexivity. Qed.

Lemma wf_local_app_renaming P Σ Γ Δ : 
  All_local_env (lift_typing (fun (Σ : global_env_ext) (Γ' : context) (t T : term) =>
    forall P (Δ : PCUICEnvironment.context) (f : nat -> nat),
    renaming (shiftnP #|Γ ,,, Γ'| P) Σ Δ (Γ ,,, Γ') f -> Σ ;;; Δ |- rename f t : rename f T) Σ) 
    Δ ->
  forall Δ' f, 
  renaming (shiftnP #|Γ| P) Σ Δ' Γ f ->
  wf_local Σ (Δ' ,,, rename_context f Δ).
Proof.
  intros. destruct X0.
  induction X.
  - apply a.
  - simpl. destruct t0 as [s Hs].
    rewrite rename_context_snoc /=. constructor; auto.
    red. simpl. exists s.
    eapply (Hs P (Δ' ,,, rename_context f Γ0) (shiftn #|Γ0| f)).
    split => //.
    eapply urenaming_ext.
    { len. now rewrite -shiftnP_add. }
    { reflexivity. } now eapply urenaming_context.
  - destruct t0 as [s Hs]. red in t1.
    rewrite rename_context_snoc /=. constructor; auto.
    * red. exists s.
      apply (Hs P (Δ' ,,, rename_context f Γ0) (shiftn #|Γ0| f)).
      split => //.
      eapply urenaming_ext.
      { len; now rewrite -shiftnP_add. }
      { reflexivity. } now eapply urenaming_context.
    * red. apply (t1 P). split => //.
      eapply urenaming_ext. 
      { len; now rewrite -shiftnP_add. }
      { reflexivity. } now eapply urenaming_context.
Qed.

Lemma rename_decompose_prod_assum f Γ t :
    decompose_prod_assum (rename_context f Γ) (rename (shiftn #|Γ| f) t)
    = let '(Γ, t) := decompose_prod_assum Γ t in (rename_context f Γ, rename (shiftn #|Γ| f) t).
Proof.
  induction t in Γ |- *. all: try reflexivity.
  - specialize (IHt2 (Γ ,, vass na t1)).
    rewrite rename_context_snoc /= in IHt2.
    simpl. now rewrite shiftn_add IHt2.
  - specialize (IHt3 (Γ ,, vdef na t1 t2)).
    rewrite rename_context_snoc /= in IHt3.
    simpl. now rewrite shiftn_add IHt3.
Qed.

Lemma rename_app_context f Γ Δ :
  rename_context f (Γ ,,, Δ) = 
  rename_context f Γ ,,, rename_context (shiftn #|Γ| f) Δ.
Proof.
  rewrite /rename_context fold_context_k_app /app_context. f_equal.
  apply fold_context_k_ext. intros i x. now rewrite shiftn_add.
Qed.

Lemma rename_smash_context f Γ Δ :
  rename_context f (smash_context Γ Δ) = 
  smash_context (rename_context (shiftn #|Δ| f) Γ) (rename_context f Δ).
Proof.
  induction Δ as [|[na [b|] ty] Δ] in Γ |- *; simpl; auto;
    rewrite ?shiftn0 // ?rename_context_snoc IHΔ /=; len.
  - f_equal. now rewrite rename_context_subst /= shiftn_add.
  - f_equal. rewrite rename_app_context /map_decl /= /app_context.
    f_equal.
    * now rewrite shiftn_add.
    * rewrite /rename_context fold_context_k_tip /map_decl /=. do 2 f_equal.
      now rewrite shiftn0.
Qed.

Lemma nth_error_rename_context f Γ n : 
  nth_error (rename_context f Γ) n = 
  option_map (map_decl (rename (shiftn (#|Γ| - S n) f))) (nth_error Γ n).
Proof.
  induction Γ in n |- *; intros.
  - simpl. unfold rename_context, fold_context_k; simpl; rewrite nth_error_nil. easy.
  - simpl. destruct n; rewrite rename_context_snoc.
    + simpl. lia_f_equal.
    + simpl. rewrite IHΓ; simpl in *; (lia || congruence).
Qed.

Lemma rename_check_one_fix f (mfix : mfixpoint term) d x : 
  check_one_fix d = Some x ->
  check_one_fix (map_def (rename f) (rename (shiftn #|mfix| f)) d) = Some x.
Proof.
  destruct d; simpl.
  move: (rename_decompose_prod_assum f [] dtype).
  rewrite shiftn0. intros ->.
  destruct decompose_prod_assum.
  rewrite -(rename_smash_context f []).
  destruct nth_error eqn:hnth => //.
  pose proof (nth_error_Some_length hnth). len in H.
  simpl in H.
  destruct (nth_error (List.rev (rename_context _ _)) _) eqn:hnth'.
  2:{ eapply nth_error_None in hnth'. len in hnth'. simpl in hnth'. lia. }
  rewrite nth_error_rev_inv in hnth; len; auto.
  len in hnth. simpl in hnth.
  rewrite nth_error_rev_inv in hnth'; len; auto.
  len in hnth'. simpl in hnth'.
  rewrite nth_error_rename_context /= hnth /= in hnth'. noconf hnth'.
  simpl.
  destruct decompose_app eqn:da. len.
  destruct t0 => /= //.
  eapply decompose_app_inv in da. rewrite da.
  rewrite rename_mkApps. simpl. rewrite decompose_app_mkApps //.
Qed.

Lemma rename_check_one_cofix f (mfix : mfixpoint term) d x : 
  check_one_cofix d = Some x ->
  check_one_cofix (map_def (rename f) (rename (shiftn #|mfix| f)) d) = Some x.
Proof.
  destruct d; simpl.
  move: (rename_decompose_prod_assum f [] dtype).
  rewrite shiftn0. intros ->.
  destruct decompose_prod_assum.
  destruct decompose_app eqn:da.
  destruct t0 => /= //.
  eapply decompose_app_inv in da. rewrite da /=.
  rewrite rename_mkApps. simpl. rewrite decompose_app_mkApps //.
Qed.

Lemma rename_wf_fixpoint Σ f mfix :
  wf_fixpoint Σ mfix ->
  wf_fixpoint Σ (map (map_def (rename f) (rename (shiftn #|mfix| f))) mfix).
Proof.
  unfold wf_fixpoint.
  rewrite map_map_compose.
  destruct (map_option_out (map check_one_fix mfix)) as [[]|] eqn:hmap => //.
  eapply map_option_out_impl in hmap.
  2:{ intros x y. apply (rename_check_one_fix f mfix). }
  now rewrite hmap.
Qed.

Lemma rename_wf_cofixpoint Σ f mfix :
  wf_cofixpoint Σ mfix ->
  wf_cofixpoint Σ (map (map_def (rename f) (rename (shiftn #|mfix| f))) mfix).
Proof.
  rewrite /wf_cofixpoint map_map_compose.
  destruct (map_option_out (map check_one_cofix mfix)) as [[]|] eqn:hmap => //.
  eapply map_option_out_impl in hmap.
  2:{ intros x y. apply (rename_check_one_cofix f mfix). }
  now rewrite hmap.
Qed.

Lemma rename_subst_telescope f s Γ : 
  rename_telescope f (subst_telescope s 0 Γ) =
  subst_telescope (map (rename f) s) 0
    (rename_telescope (shiftn #|s| f) Γ).
Proof.
  rewrite /rename_telescope /subst_telescope.
  rewrite !mapi_compose. apply mapi_ext => k' d.
  rewrite !compose_map_decl; apply map_decl_ext => t'.
  now rewrite Nat.add_0_r rename_subst.
Qed.

Lemma mapi_cons {A B} (f : nat -> A -> B) a l : 
  mapi f (a :: l) = f 0 a :: mapi (fun x => f (S x)) l.
Proof.
  now rewrite /mapi /= mapi_rec_Sk.
Qed.

Instance rename_telescope_ext : Proper (`=1` ==> `=1`) rename_telescope.
Proof.
  intros f g Hfg Γ.
  rewrite /rename_telescope. apply mapi_ext => n x.
  now rewrite Hfg.
Qed.

Lemma rename_telescope_shiftn0 f Γ : rename_telescope (shiftn 0 f) Γ = rename_telescope f Γ.
Proof. now sigma. Qed.

Lemma rename_telescope_cons f d Γ : 
  rename_telescope f (d :: Γ) = rename_decl f d :: rename_telescope (shiftn 1 f) Γ.
Proof. 
  rewrite /rename_telescope mapi_cons /rename_decl.
  f_equal; sigma => //.
  apply mapi_ext => i x. now rewrite shiftn_add Nat.add_1_r.
Qed.

Hint Rewrite <- Upn_ren : sigma.

(** For an unconditional renaming defined on all variables in the source context *)
Lemma typing_rename_prop : env_prop
  (fun Σ Γ t A =>
    forall P Δ f,
    renaming (shiftnP #|Γ| P) Σ Δ Γ f ->
    Σ ;;; Δ |- rename f t : rename f A)
   (fun Σ Γ =>
    wf_local Σ Γ ×
   All_local_env
   (lift_typing (fun (Σ : global_env_ext) (Γ : context) (t T : term)
    =>
    forall P (Δ : PCUICEnvironment.context) (f : nat -> nat),
    renaming (shiftnP #|Γ| P) Σ Δ Γ f -> 
    Σ;;; Δ |- rename f t : rename f T) Σ) Γ).
Proof.
  apply typing_ind_env.
  
  - intros Σ wfΣ Γ wfΓ HΓ. split; auto.
    induction HΓ; constructor; firstorder eauto.
  
  - intros Σ wfΣ Γ wfΓ n decl isdecl ihΓ P Δ f hf.
    simpl in *. 
    eapply hf in isdecl as h => //.
    2:{ rewrite /shiftnP. eapply nth_error_Some_length in isdecl. now nat_compare_specs. }
    destruct h as [decl' [isdecl' [? [h1 h2]]]].
    rewrite lift0_rename rename_compose h1 -lift0_rename.
    econstructor. all: auto. apply hf.

  - intros Σ wfΣ Γ wfΓ l X H0 P Δ f [hΔ hf].
    simpl. constructor. all: auto.

  - intros Σ wfΣ Γ wfΓ na A B s1 s2 X hA ihA hB ihB P Δ f hf.
    rewrite /=. econstructor.
    + eapply ihA; eauto.
    + eapply ihB; eauto.
      simpl.
      eapply renaming_extP. { now rewrite -(shiftnP_add 1). }
      eapply renaming_vass. 2: eauto.
      constructor.
      * destruct hf as [hΔ hf]. auto.
      * simpl. exists s1. eapply ihA; eauto.
  - intros Σ wfΣ Γ wfΓ na A t s1 B X hA ihA ht iht P Δ f hf.
    simpl. 
     (* /andP [_ havB]. *)
    simpl. econstructor.
    + eapply ihA; eauto.
    + eapply iht; eauto; simpl.
      eapply renaming_extP. { now rewrite -(shiftnP_add 1). }
      eapply renaming_vass. 2: eauto.
      constructor.
      * destruct hf as [hΔ hf]. auto.
      * simpl. exists s1. eapply ihA; eauto.
  - intros Σ wfΣ Γ wfΓ na b B t s1 A X hB ihB hb ihb ht iht P Δ f hf.
    simpl. econstructor.
    + eapply ihB; tea. 
    + eapply ihb; tea.
    + eapply iht; tea.
      eapply renaming_extP. { now rewrite -(shiftnP_add 1). }
      eapply renaming_vdef. 2: eauto.
      constructor.
      * destruct hf. assumption.
      * simpl. eexists. eapply ihB; tea. 
      * simpl. eapply ihb; tea.
  - intros Σ wfΣ Γ wfΓ t na A B s u X hty ihty ht iht hu ihu P Δ f hf.
    simpl. eapply meta_conv.
    + eapply type_App.
      * simpl in ihty. eapply ihty; tea.
      * simpl in iht. eapply iht. eassumption.
      * eapply ihu. eassumption.
    + autorewrite with sigma. rewrite !subst1_inst. sigma.
      eapply inst_ext => i.      
      unfold subst_cons, ren, shiftn, subst_compose. simpl.
      destruct i.
      * simpl. reflexivity.
      * simpl. replace (i - 0) with i by lia.
        reflexivity.
  - intros Σ wfΣ Γ wfΓ cst u decl X X0 isdecl hconst P Δ f hf.
    simpl. eapply meta_conv.
    + constructor. all: eauto. apply hf.
    + rewrite rename_subst_instance. f_equal.
      rewrite rename_closed. 2: auto.
      eapply declared_constant_closed_type. all: eauto.
  - intros Σ wfΣ Γ wfΓ ind u mdecl idecl isdecl X X0 hconst P Δ σ hf.
    simpl. eapply meta_conv.
    + econstructor. all: eauto. apply hf.
    + rewrite rename_subst_instance. f_equal.
      rewrite rename_closed. 2: auto.
      eapply declared_inductive_closed_type. all: eauto.
  - intros Σ wfΣ Γ wfΓ ind i u mdecl idecl cdecl isdecl X X0 hconst P Δ f hf.
    simpl. eapply meta_conv.
    + econstructor. all: eauto. apply hf. 
    + rewrite rename_closed. 2: reflexivity.
      eapply declared_constructor_closed_type. all: eauto.
  - intros Σ wfΣ Γ wfΓ ci p c brs indices ps mdecl idecl isdecl HΣ.
    intros [_ IHΔ] ci_npar predctx wfp cup [wfpctx Hpctx] convctx Hpret 
      IHpret [wfpredctx IHpredctx] isallowed.
    intros Hcxti IHctxi Hc IHc iscof ptm wfbrs Hbrs P Δ f Hf.
    simpl.
    rewrite rename_mkApps.
    rewrite map_app. simpl.
    rewrite /ptm. rewrite rename_it_mkLambda_or_LetIn.
    relativize #|predctx|.
    * erewrite rename_predicate_preturn.
      replace (rename_context f (pcontext p)) with (pcontext (rename_predicate f p)).
      2:{ destruct p => //. simpl. rewrite mapi_context_fold //. }
      rewrite /predctx.
      eapply type_Case; eauto.
      + now eapply rename_wf_predicate.
      + simpl. rewrite mapi_context_fold.
        apply All_local_env_app_inv in Hpctx as [].
        eapply wf_local_app_renaming; eauto. apply a0.
      + simpl.
        rewrite -rename_case_predicate_context //.
        rewrite mapi_context_fold -/(rename_context f _).
        eapply conv_ctx_renameP; eauto.
        ++ eapply Hf.
        ++ eapply closed_wf_local in wfpctx => //.
           rewrite closedn_ctx_app in wfpctx.
           move/andP: wfpctx => [clΓ clpctx].
           now eapply closedn_ctx_on_free_vars_shift in clpctx.
        ++ move/closed_wf_local: wfpredctx => //.
           rewrite closedn_ctx_app => /andP [] _.
           now move/closedn_ctx_on_free_vars_shift. 
        ++ pose proof (closed_ctx_on_free_vars P _ (closed_wf_local _ (typing_wf_local Hc))).
           rewrite -{2}(app_context_nil_l Γ).
           apply on_ctx_free_vars_extend => //.
      + eapply IHpret => //.
        rewrite /= mapi_context_fold -/(rename_context f _).
        split.
        ++ apply All_local_env_app_inv in Hpctx as [].
          eapply wf_local_app_renaming; eauto. apply a0.
        ++ rewrite /predctx.
           eapply urenaming_ext.
           { len. now rewrite -shiftnP_add. }
           { reflexivity. }
          eapply urenaming_context. apply Hf.
      + rewrite -rename_case_predicate_context //.
        eapply All_local_env_app_inv in IHpredctx as [].
        eapply wf_local_app_renaming; eauto. apply a0.
      + revert IHctxi.
        rewrite /= /id -map_app.
        rewrite -{2}[subst_instance _ _](rename_closedn_ctx f 0).
        { pose proof (declared_inductive_closed_pars_indices _ isdecl).
          now rewrite closedn_subst_instance_context. }
        rewrite rename_context_telescope.
        rewrite rename_telescope_shiftn0.
        clear -P Δ f Hf.
        induction 1.
        { constructor; auto. }
        { simpl. rewrite rename_telescope_cons.
          constructor; cbn; eauto.
          now rewrite rename_subst_telescope /= in IHIHctxi. }
        { simpl. rewrite rename_telescope_cons.
          constructor; cbn; eauto.
          now rewrite rename_subst_telescope /= in IHIHctxi. }
      + simpl. unfold id.
        specialize (IHc _ _ _ Hf).
        now rewrite rename_mkApps map_app in IHc.
      + now eapply rename_wf_branches.
      + eapply Forall2_All2 in wfbrs.
        eapply All2i_All2_mix_left in Hbrs; eauto.
        eapply All2i_nth_hyp in Hbrs.
        eapply All2i_map_right, (All2i_impl Hbrs) => i cdecl br.
        set (brctxty := case_branch_type _ _ _ _ _ _ _ _).
        move=> [Hnth [wfbr [[[wfbctx Hbr] Hconv] [[IHbr [wfbrctxty Hbrctxty]] [IHbod [Hbty IHbty]]]]]].
        rewrite -(rename_closed_constructor_body mdecl cdecl f).
        { eapply (declared_constructor_closed (c:=(ci.(ci_ind),i))); eauto.
          split; eauto. }
        rewrite rename_case_branch_type //.
        rewrite -/brctxty. intros brctx'.
        assert (wf_local Σ (Δ,,, brctx'.1)).
        { rewrite /brctx'. cbn.
          apply All_local_env_app_inv in Hbrctxty as [].
          eapply wf_local_app_renaming; tea. apply a0. }
        assert (wf_local Σ (Δ,,, bcontext (rename_branch f br))).
        { apply All_local_env_app_inv in Hbr as [].
          cbn. rewrite mapi_context_fold.
          eapply wf_local_app_renaming; tea. apply a0. }
        repeat split => //.
        ++ cbn. rewrite mapi_context_fold.
          { eapply conv_ctx_renameP in Hconv; eauto.
            - eapply Hf.
            - eapply closed_wf_local in wfbctx => //.
              rewrite closedn_ctx_app in wfbctx.
              move/andP: wfbctx => [clΓ clbctx].
              eapply closedn_ctx_on_free_vars_shift in clbctx; tea.
            - move/closed_wf_local: wfbrctxty => //.
              rewrite closedn_ctx_app => /andP [] _.
              now move/closedn_ctx_on_free_vars_shift. 
            - pose proof (closed_ctx_on_free_vars P _ (closed_wf_local _ (typing_wf_local Hc))).
              rewrite -{2}(app_context_nil_l Γ).
              apply on_ctx_free_vars_extend => //. }
        ++ eapply IHbod => //. 
          split => //.
          eapply urenaming_ext.
          { now rewrite app_context_length -shiftnP_add. }
          { reflexivity. }
          rewrite /= mapi_context_fold.
          eapply urenaming_context, Hf.
        ++ eapply IHbty. split=> //.
          rewrite /brctx'; cbn.
          rewrite (wf_branch_length wfbr).
          eapply urenaming_ext.
          { now rewrite app_context_length -shiftnP_add. }
          { reflexivity. }
          rewrite mapi_context_fold.
          rewrite -(wf_branch_length wfbr).
          rewrite -/(rename_context f _).
          eapply urenaming_context, Hf.
    * rewrite /predctx case_predicate_context_length //.
  - intros Σ wfΣ Γ wfΓ p c u mdecl idecl pdecl isdecl args X X0 hc ihc e ty
           P Δ f hf.
    simpl. eapply meta_conv.
    + econstructor.
      * eassumption.
      * eapply meta_conv.
        -- eapply ihc; tea.
        -- rewrite rename_mkApps. simpl. reflexivity.
      * rewrite map_length. assumption.
    + rewrite rename_subst0. simpl. rewrite map_rev. f_equal.
      rewrite rename_subst_instance. f_equal.
      rewrite rename_closedn. 2: reflexivity.
      eapply declared_projection_closed_type in isdecl.
      rewrite List.rev_length. rewrite e. assumption.

  - intros Σ wfΣ Γ wfΓ mfix n decl types H1 hdecl [_ X] ihmfixt ihmfixb wffix P Δ f hf.
    apply All_local_env_app_inv in X as [_ X].
    eapply wf_local_app_renaming in X; tea.
    simpl. eapply meta_conv.
    + eapply type_Fix.
      * eapply fix_guard_rename; eauto.
      * rewrite nth_error_map. rewrite hdecl. simpl. reflexivity.
      * apply hf.
      * apply All_map, (All_impl ihmfixt).
        intros x [s [Hs IHs]].
        exists s. now eapply IHs.
      * apply All_map, (All_impl ihmfixb).
        intros x [Hb IHb].
        destruct x as [na ty bo rarg]. simpl in *.
        rewrite rename_fix_context.
        eapply meta_conv.
        ++ apply (IHb P (Δ ,,, rename_context f types) (shiftn #|mfix| f)).
          split; auto. subst types. rewrite -(fix_context_length mfix).
          eapply urenaming_ext.
          { now rewrite app_context_length -shiftnP_add. }
          { reflexivity. }
          apply urenaming_context; auto. apply hf.
        ++ len. now sigma.
      * now eapply rename_wf_fixpoint.
    + reflexivity.

  - intros Σ wfΣ Γ wfΓ mfix n decl types guard hdecl [_ X] ihmfixt ihmfixb wfcofix P Δ f hf.
    apply All_local_env_app_inv in X as [_ X].
    eapply wf_local_app_renaming in X; eauto.
    simpl. eapply meta_conv.
    + eapply type_CoFix; auto.
      * eapply cofix_guard_rename; eauto.
      * rewrite nth_error_map. rewrite hdecl. simpl. reflexivity.
      * apply hf.
      * apply All_map, (All_impl ihmfixt).
        intros x [s [Hs IHs]].
        exists s. now eapply IHs.
      * apply All_map, (All_impl ihmfixb).
        intros x [Hb IHb].
        destruct x as [na ty bo rarg]. simpl in *.
        rewrite rename_fix_context.
        eapply meta_conv.
        ++ apply (IHb P (Δ ,,, rename_context f types) (shiftn #|mfix| f)).
            split; auto. subst types. rewrite -(fix_context_length mfix).
            eapply urenaming_ext.
            { now rewrite app_context_length -shiftnP_add. }
            { reflexivity. }
            apply urenaming_context; auto. apply hf.
        ++ len. now sigma.
      * now eapply rename_wf_cofixpoint.
    + reflexivity.

  - intros Σ wfΣ Γ wfΓ t A B X hwf ht iht htB ihB cum P Δ f hf.
    eapply type_Cumul.
    + eapply iht; tea.
    + eapply ihB; tea.
    + eapply cumul_renameP. all: try eassumption.
      * apply hf.
      * pose proof (type_closed _ ht).
        now eapply closedn_on_free_vars in H.
      * pose proof (subject_closed _ htB).
        now eapply closedn_on_free_vars in H.
      * pose proof (closed_ctx_on_free_vars P _ (closed_wf_local _ (typing_wf_local ht))).
        rewrite -{2}(app_context_nil_l Γ).
        eapply on_ctx_free_vars_extend => //.
Qed.

Lemma typing_rename_P {P Σ Γ Δ f t A} {wfΣ : wf Σ.1} :
  renaming (shiftnP #|Γ| P) Σ Δ Γ f ->
  Σ ;;; Γ |- t : A ->
  Σ ;;; Δ |- rename f t : rename f A.
Proof.
  intros hf h.
  revert Σ wfΣ Γ t A h P Δ f hf.
  apply typing_rename_prop.
Qed.

Lemma typing_rename {Σ Γ Δ f t A} {wfΣ : wf Σ.1} :
  renaming (closedP #|Γ| xpredT) Σ Δ Γ f ->
  Σ ;;; Γ |- t : A ->
  Σ ;;; Δ |- rename f t : rename f A.
Proof.
  intros hf h.
  eapply (typing_rename_P (P:=fun _ => false)) ; eauto.
Qed.

End Renaming.
