(* Distributed under the terms of the MIT license.   *)
From Equations Require Import Equations.
From Coq Require Import Bool String List BinPos Compare_dec Omega Lia.
Require Import Coq.Program.Syntax Coq.Program.Basics.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICLiftSubst PCUICUnivSubst
     PCUICTyping PCUICWeakeningEnv PCUICClosed PCUICReduction PCUICEquality.
Require Import ssreflect ssrbool.

Set Keyed Unification.
From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.
Set Equations With UIP.

(* TODO Maybe remove later? *)
Require PCUICWeakening.

(** * Type preservation for σ-calculus *)

Set Asymmetric Patterns.
Open Scope sigma_scope.

Hint Rewrite @lift_rename : sigma.

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
Hint Rewrite @subst1_inst : sigma.

Lemma rename_mkApps :
  forall f t l,
    rename f (mkApps t l) = mkApps (rename f t) (map (rename f) l).
Proof.
  intros f t l.
  autorewrite with sigma. f_equal.
  induction l.
  - reflexivity.
  - simpl. autorewrite with sigma. easy.
Qed.

Lemma rename_subst_instance_constr :
  forall u t f,
    rename f (subst_instance_constr u t) = subst_instance_constr u (rename f t).
Proof.
  intros u t f.
  induction t in f |- * using term_forall_list_ind.
  all: try solve [
    simpl ;
    rewrite ?IHt ?IHt1 ?IHt2 ;
    easy
  ].
  - simpl. f_equal. induction H.
    + reflexivity.
    + simpl. f_equal ; easy.
  - simpl. rewrite IHt1 IHt2. f_equal.
    induction X.
    + reflexivity.
    + simpl. f_equal. 2: easy.
      destruct x. unfold on_snd. simpl in *.
      easy.
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
  fold_context (fun i => rename (shiftn i f)) Γ.

Lemma rename_context_length :
  forall σ Γ,
    #|rename_context σ Γ| = #|Γ|.
Proof.
  intros σ Γ. unfold rename_context.
  apply fold_context_length.
Qed.
Hint Rewrite rename_context_length : sigma wf.

Definition rename_decl f d :=
  map_decl (rename f) d.

Lemma rename_context_snoc :
  forall f Γ d,
    rename_context f (d :: Γ) =
    rename_context f Γ ,, rename_decl (shiftn #|Γ| f) d.
Proof.
  intros f Γ d.
  unfold rename_context, fold_context.
  rewrite !rev_mapi !rev_involutive /mapi mapi_rec_eqn /snoc.
  f_equal.
  - rewrite Nat.sub_0_r List.rev_length. reflexivity.
  - rewrite mapi_rec_Sk. simpl. apply mapi_rec_ext.
    intros k x H H0.
    rewrite app_length !List.rev_length. simpl.
    unfold map_decl. f_equal.
    + destruct (decl_body x) ; auto.
      simpl. f_equal. f_equal. f_equal. lia.
    + f_equal. f_equal. lia.
Qed.
Hint Rewrite rename_context_snoc : sigma.

Definition inst_context σ (Γ : context) : context :=
  fold_context (fun i => inst (⇑^i σ)) Γ.

Lemma inst_context_length :
  forall σ Γ,
    #|inst_context σ Γ| = #|Γ|.
Proof.
  intros σ Γ. unfold inst_context.
  apply fold_context_length.
Qed.
Hint Rewrite inst_context_length : sigma wf.

Definition inst_decl σ d :=
  map_decl (inst σ) d.

Lemma inst_context_snoc :
  forall σ Γ d,
    inst_context σ (d :: Γ) =
    inst_context σ Γ ,, inst_decl (⇑^#|Γ| σ) d.
Proof.
  intros σ Γ d.
  unfold inst_context, fold_context.
  rewrite !rev_mapi !rev_involutive /mapi mapi_rec_eqn /snoc.
  f_equal.
  - rewrite Nat.sub_0_r List.rev_length. reflexivity.
  - rewrite mapi_rec_Sk. simpl. apply mapi_rec_ext.
    intros k x H H0.
    rewrite app_length !List.rev_length. simpl.
    unfold map_decl. f_equal.
    + destruct (decl_body x) ; auto.
      simpl. f_equal. f_equal. f_equal. lia.
    + f_equal. f_equal. lia.
Qed.
Hint Rewrite inst_context_snoc : sigma.

Lemma rename_decl_inst_decl :
  forall f d,
    rename_decl f d = inst_decl (ren f) d.
Proof.
  intros f d.
  unfold rename_decl, inst_decl.
  destruct d. unfold map_decl.
  autorewrite with sigma.
  f_equal.
  simpl. destruct decl_body.
  - simpl. f_equal. autorewrite with sigma. reflexivity.
  - reflexivity.
Qed.
Hint Rewrite rename_decl_inst_decl : sigma.

Lemma rename_context_inst_context :
  forall f Γ,
    rename_context f Γ = inst_context (ren f) Γ.
Proof.
  intros f Γ.
  induction Γ.
  - reflexivity.
  - autorewrite with sigma. rewrite IHΓ. f_equal.
    destruct a. unfold inst_decl. unfold map_decl. simpl.
    f_equal.
    + destruct decl_body. 2: reflexivity.
      simpl. f_equal. eapply inst_ext. intro j.
      unfold ren, shiftn, Upn, subst_consn, shift, shiftk, subst_compose.
      destruct (Nat.ltb_spec j #|Γ|).
      * rewrite nth_error_idsn_Some. all: eauto.
      * rewrite nth_error_idsn_None. 1: lia.
        simpl. rewrite idsn_length. reflexivity.
    + eapply inst_ext. intro i.
      unfold ren, shiftn, Upn, subst_consn, shift, shiftk, subst_compose.
      destruct (Nat.ltb_spec i #|Γ|).
      * rewrite nth_error_idsn_Some. all: eauto.
      * rewrite nth_error_idsn_None. 1: lia.
        simpl. rewrite idsn_length. reflexivity.
Qed.
Hint Rewrite rename_context_inst_context : sigma.

(* Lemma rename_subst : *)
(*   forall f l t n, *)
(*     rename f (subst l n t) = *)
(*     subst (map (rename f) l) (#|l| + n) (rename (shiftn #|l| f) t). *)
(*     (* subst (map (rename (shiftn n f)) l) n (rename (shiftn (#|l| + n) f) t). *) *)
(* Proof. *)

Lemma rename_subst0 :
  forall f l t,
    rename f (subst0 l t) =
    subst0 (map (rename f) l) (rename (shiftn #|l| f) t).
Proof.
  intros f l t.
  autorewrite with sigma.
  eapply inst_ext. intro i.
  unfold ren, subst_consn, shiftn, subst_compose. simpl.
  rewrite nth_error_map.
  destruct (nth_error l i) eqn: e1.
  - eapply nth_error_Some_length in e1 as hl.
    destruct (Nat.ltb_spec i #|l|). 2: lia.
    rewrite e1. simpl.
    autorewrite with sigma. reflexivity.
  - simpl. apply nth_error_None in e1 as hl.
    destruct (Nat.ltb_spec i #|l|). 1: lia.
    rewrite (iffRL (nth_error_None _ _)). 1: lia.
    simpl. rewrite map_length. unfold ids.
    f_equal. lia.
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
      rewrite rename_context_snoc. simpl.
      f_equal. f_equal. f_equal. lia.
    + simpl in h. rewrite rename_context_snoc. simpl.
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

(* Lemma rename_lift0 : *)
(*   forall f i t, *)
(*     rename f (lift0 i t) = lift0 (f i) (rename f t). *)
(* Proof. *)
(*   intros f i t. *)
(*   rewrite !lift_rename. *)
(*   autorewrite with sigma. *)
(*   eapply inst_ext. intro j. *)
(*   unfold ren, lift_renaming, subst_compose, shiftn. *)
(*   simpl. f_equal. *)
(*   destruct (Nat.ltb_spec j i). *)
(*   - *)

(* (rename (shiftn (#|Γ| - S i) f) body) *)
(* rename f ((lift0 (S i)) body) *)

Section Renaming.

Context `{checker_flags}.

Lemma eq_term_upto_univ_rename :
  forall Re Rle u v f,
    eq_term_upto_univ Re Rle u v ->
    eq_term_upto_univ Re Rle (rename f u) (rename f v).
Proof.
  intros Re Rle u v f h.
  induction u in v, Rle, f, h |- * using term_forall_list_ind.
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
    induction X in a, brs' |- *.
    + inversion a. constructor.
    + inversion a. subst. simpl.
      constructor.
      * unfold on_snd. intuition eauto.
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
Definition urenaming Γ Δ f :=
  forall i decl,
    nth_error Δ i = Some decl ->
    ∑ decl',
      nth_error Γ (f i) = Some decl' ×
      rename f (lift0 (S i) decl.(decl_type))
      = lift0 (S (f i)) decl'.(decl_type) ×
      (forall b,
         decl.(decl_body) = Some b ->
         ∑ b',
           decl'.(decl_body) = Some b' ×
           rename f (lift0 (S i) b) = lift0 (S (f i)) b'
      ).

(* Definition of a good renaming with respect to typing *)
Definition renaming Σ Γ Δ f :=
  wf_local Σ Γ × urenaming Γ Δ f.

(* TODO MOVE *)
Lemma rename_iota_red :
  forall f pars c args brs,
    rename f (iota_red pars c args brs) =
    iota_red pars c (map (rename f) args) (map (on_snd (rename f)) brs).
Proof.
  intros f pars c args brs.
  unfold iota_red. rewrite rename_mkApps.
  rewrite map_skipn. f_equal.
  change (rename f (nth c brs (0, tDummy)).2)
    with (on_snd (rename f) (nth c brs (0, tDummy))).2. f_equal.
  rewrite <- map_nth with (f := on_snd (rename f)).
  reflexivity.
Qed.

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
  case_eq (isLambda (dbody d)).
  2: intro neq ; rewrite neq in h ; discriminate.
  intros hl. rewrite hl in h. inversion h. clear h.
  simpl. rewrite isLambda_rename. 1: assumption.
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

(* TODO MOVE *)
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

(* TODO MOVE *)
Lemma rename_closed :
  forall f t,
    closed t ->
    rename f t = t.
Proof.
  intros f t h.
  replace (rename f t) with (rename (shiftn 0 f) t).
  - apply rename_closedn. assumption.
  - autorewrite with sigma. eapply inst_ext. intro i.
    unfold ren, shiftn. simpl.
    f_equal. f_equal. lia.
Qed.

(* TODO MOVE *)
Lemma declared_constant_closed_body :
  forall Σ cst decl body,
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
  eapply typecheck_closed in decl' as [? ee]. 2: auto. 2: constructor.
  move/andP in ee. destruct ee. assumption.
Qed.

Lemma rename_shiftn :
  forall f t,
    rename (shiftn 1 f) (lift0 1 t) = lift0 1 (rename f t).
Proof.
  intros f t.
  autorewrite with sigma.
  eapply inst_ext. intro i.
  unfold ren, lift_renaming, shiftn, subst_compose. simpl.
  replace (i - 0) with i by lia.
  reflexivity.
Qed.

Lemma urenaming_vass :
  forall Γ Δ na A f,
    urenaming Γ Δ f ->
    urenaming (Γ ,, vass na (rename f A)) (Δ ,, vass na A) (shiftn 1 f).
Proof.
  intros Γ Δ na A f h. unfold urenaming in *.
  intros [|i] decl e.
  - simpl in e. inversion e. subst. clear e.
    simpl. eexists. split. 1: reflexivity.
    split.
    + autorewrite with sigma.
      eapply inst_ext. intro i.
      unfold ren, lift_renaming, shiftn, subst_compose. simpl.
      replace (i - 0) with i by lia. reflexivity.
    + intros. discriminate.
  - simpl in e. simpl.
    replace (i - 0) with i by lia.
    eapply h in e as [decl' [? [h1 h2]]].
    eexists. split. 1: eassumption.
    split.
    + rewrite simpl_lift0. rewrite rename_shiftn. rewrite h1.
      autorewrite with sigma.
      eapply inst_ext. intro j.
      unfold ren, lift_renaming, shiftn, subst_compose. simpl.
      replace (i - 0) with i by lia.
      reflexivity.
    + intros b e'.
      eapply h2 in e' as [b' [? hb]].
      eexists. split. 1: eassumption.
      rewrite simpl_lift0. rewrite rename_shiftn. rewrite hb.
      autorewrite with sigma.
      eapply inst_ext. intro j.
      unfold ren, lift_renaming, shiftn, subst_compose. simpl.
      replace (i - 0) with i by lia.
      reflexivity.
Qed.

Lemma renaming_vass :
  forall Σ Γ Δ na A f,
    wf_local Σ (Γ ,, vass na (rename f A)) ->
    renaming Σ Γ Δ f ->
    renaming Σ (Γ ,, vass na (rename f A)) (Δ ,, vass na A) (shiftn 1 f).
Proof.
  intros Σ Γ Δ na A f hΓ [? h].
  split. 1: auto.
  eapply urenaming_vass. assumption.
Qed.

Lemma urenaming_vdef :
  forall Γ Δ na b B f,
    urenaming Γ Δ f ->
    urenaming (Γ ,, vdef na (rename f b) (rename f B)) (Δ ,, vdef na b B) (shiftn 1 f).
Proof.
  intros Γ Δ na b B f h. unfold urenaming in *.
  intros [|i] decl e.
  - simpl in e. inversion e. subst. clear e.
    simpl. eexists. split. 1: reflexivity.
    split.
    + autorewrite with sigma.
      eapply inst_ext. intro i.
      unfold ren, lift_renaming, shiftn, subst_compose. simpl.
      replace (i - 0) with i by lia. reflexivity.
    + intros b' [= <-].
      simpl. eexists. split. 1: reflexivity.
      autorewrite with sigma.
      eapply inst_ext. intro i.
      unfold ren, lift_renaming, shiftn, subst_compose. simpl.
      replace (i - 0) with i by lia. reflexivity.
  - simpl in e. simpl.
    replace (i - 0) with i by lia.
    eapply h in e as [decl' [? [h1 h2]]].
    eexists. split. 1: eassumption.
    split.
    + rewrite simpl_lift0. rewrite rename_shiftn. rewrite h1.
      autorewrite with sigma.
      eapply inst_ext. intro j.
      unfold ren, lift_renaming, shiftn, subst_compose. simpl.
      replace (i - 0) with i by lia.
      reflexivity.
    + intros b0 e'.
      eapply h2 in e' as [b' [? hb]].
      eexists. split. 1: eassumption.
      rewrite simpl_lift0. rewrite rename_shiftn. rewrite hb.
      autorewrite with sigma.
      eapply inst_ext. intro j.
      unfold ren, lift_renaming, shiftn, subst_compose. simpl.
      replace (i - 0) with i by lia.
      reflexivity.
Qed.

Lemma renaming_vdef :
  forall Σ Γ Δ na b B f,
    wf_local Σ (Γ ,, vdef na (rename f b) (rename f B)) ->
    renaming Σ Γ Δ f ->
    renaming Σ (Γ ,, vdef na (rename f b) (rename f B)) (Δ ,, vdef na b B) (shiftn 1 f).
Proof.
  intros Σ Γ Δ na b B f hΓ [? h].
  split. 1: auto.
  eapply urenaming_vdef. assumption.
Qed.

Lemma urenaming_ext :
  forall Γ Δ f g,
    f =1 g ->
    urenaming Δ Γ f ->
    urenaming Δ Γ g.
Proof.
  intros Γ Δ f g hfg h.
  intros i decl e.
  specialize (h i decl e) as [decl' [h1 [h2 h3]]].
  exists decl'. split ; [| split ].
  - rewrite <- (hfg i). assumption.
  - rewrite <- (hfg i). rewrite <- h2.
    eapply rename_ext. intros j. symmetry. apply hfg.
  - intros b hb. specialize (h3 b hb) as [b' [p1 p2]].
    exists b'. split ; auto. rewrite <- (hfg i). rewrite <- p2.
    eapply rename_ext. intros j. symmetry. apply hfg.
Qed.

Lemma urenaming_context :
  forall Γ Δ Ξ f,
    urenaming Δ Γ f ->
    urenaming (Δ ,,, rename_context f Ξ) (Γ ,,, Ξ) (shiftn #|Ξ| f).
Proof.
  intros Γ Δ Ξ f h.
  induction Ξ as [| [na [bo|] ty] Ξ ih] in Γ, Δ, f, h |- *.
  - simpl. eapply urenaming_ext. 2: eassumption.
    intros []. all: reflexivity.
  - simpl. rewrite rename_context_snoc.
    rewrite app_context_cons. simpl. unfold rename_decl. unfold map_decl. simpl.
    eapply urenaming_ext.
    2: eapply urenaming_vdef.
    + intros [|i].
      * reflexivity.
      * unfold shiftn. simpl. replace (i - 0) with i by lia.
        destruct (Nat.ltb_spec0 i #|Ξ|).
        -- destruct (Nat.ltb_spec0 (S i) (S #|Ξ|)). all: easy.
        -- destruct (Nat.ltb_spec0 (S i) (S #|Ξ|)). all: easy.
    + eapply ih. assumption.
  - simpl. rewrite rename_context_snoc.
    rewrite app_context_cons. simpl. unfold rename_decl. unfold map_decl. simpl.
    eapply urenaming_ext.
    2: eapply urenaming_vass.
    + intros [|i].
      * reflexivity.
      * unfold shiftn. simpl. replace (i - 0) with i by lia.
        destruct (Nat.ltb_spec0 i #|Ξ|).
        -- destruct (Nat.ltb_spec0 (S i) (S #|Ξ|)). all: easy.
        -- destruct (Nat.ltb_spec0 (S i) (S #|Ξ|)). all: easy.
    + eapply ih. assumption.
Qed.

Lemma rename_fix_context :
  forall f mfix,
    rename_context f (fix_context mfix) =
    fix_context (map (map_def (rename f) (rename (shiftn #|mfix| f))) mfix).
Proof.
  intros f mfix.
  generalize #|mfix|. intro n.
  induction mfix using list_ind_rev in f, n |- *.
  - reflexivity.
  - unfold fix_context. rewrite map_app. rewrite 2!mapi_app.
    rewrite 2!List.rev_app_distr.
    unfold rename_context. rewrite fold_context_app.
    simpl. f_equal.
    + unfold map_decl, vass. simpl. f_equal.
      autorewrite with sigma. eapply inst_ext.
      intro i. rewrite List.rev_length. rewrite mapi_length. rewrite map_length.
      unfold subst_compose, shiftn, ren, lift_renaming. simpl.
      replace (#|mfix| + 0) with #|mfix| by lia.
      destruct (Nat.ltb_spec0 (#|mfix| + i) #|mfix|). 1: lia.
      f_equal. f_equal. f_equal. lia.
    + apply IHmfix.
Qed.

(* Also true... so we can probably prove a more general lemma. *)
(* Lemma rename_fix_context : *)
(*   forall f mfix, *)
(*     rename_context f (fix_context mfix) = *)
(*     fix_context (map (map_def (rename f) (rename f)) mfix). *)
(* Proof. *)
(*   intros f mfix. *)
(*   induction mfix using list_ind_rev in f |- *. *)
(*   - reflexivity. *)
(*   - unfold fix_context. rewrite map_app. rewrite 2!mapi_app. *)
(*     rewrite 2!List.rev_app_distr. *)
(*     unfold rename_context. rewrite fold_context_app. *)
(*     simpl. f_equal. *)
(*     + unfold map_decl, vass. simpl. f_equal. *)
(*       autorewrite with sigma. eapply inst_ext. *)
(*       intro i. rewrite List.rev_length. rewrite mapi_length. rewrite map_length. *)
(*       unfold subst_compose, shiftn, ren, lift_renaming. simpl. *)
(*       replace (#|mfix| + 0) with #|mfix| by lia. *)
(*       destruct (Nat.ltb_spec0 (#|mfix| + i) #|mfix|). 1: lia. *)
(*       f_equal. f_equal. f_equal. lia. *)
(*     + apply IHmfix. *)
(* Qed. *)

Lemma red1_rename :
  forall Σ Γ Δ u v f,
    wf Σ ->
    urenaming Δ Γ f ->
    red1 Σ Γ u v ->
    red1 Σ Δ (rename f u) (rename f v).
Proof.
  intros Σ Γ Δ u v f hΣ hf h.
  induction h using red1_ind_all in f, Δ, hf |- *.
  all: try solve [
    simpl ; constructor ; eapply IHh ;
    try eapply urenaming_vass ;
    try eapply urenaming_vdef ;
    assumption
  ].
  - simpl. rewrite rename_subst10. constructor.
  - simpl. rewrite rename_subst10. constructor.
  - simpl.
    case_eq (nth_error Γ i).
    2: intro e ; rewrite e in H0 ; discriminate.
    intros decl e. rewrite e in H0. simpl in H0.
    inversion H0. clear H0.
    unfold urenaming in hf.
    specialize hf with (1 := e).
    destruct hf as [decl' [e' [hr hbo]]].
    specialize hbo with (1 := H2).
    destruct hbo as [body' [hbo' hr']].
    rewrite hr'. constructor.
    rewrite e'. simpl. rewrite hbo'. reflexivity.
  - simpl. rewrite rename_mkApps. simpl.
    rewrite rename_iota_red. constructor.
  - rewrite 2!rename_mkApps. simpl.
    econstructor.
    + eapply rename_unfold_fix. eassumption.
    + eapply is_constructor_rename. assumption.
  - simpl.
    rewrite 2!rename_mkApps. simpl.
    eapply red_cofix_case.
    eapply rename_unfold_cofix. eassumption.
  - simpl. rewrite 2!rename_mkApps. simpl.
    eapply red_cofix_proj.
    eapply rename_unfold_cofix. eassumption.
  - simpl. rewrite rename_subst_instance_constr.
    econstructor.
    + eassumption.
    + rewrite rename_closed. 2: assumption.
      eapply declared_constant_closed_body. all: eauto.
  - simpl. rewrite rename_mkApps. simpl.
    econstructor. rewrite nth_error_map. rewrite H0. reflexivity.

  - simpl. constructor. induction X.
    + destruct p0 as [[p1 p2] p3]. constructor. split ; eauto.
      simpl. eapply p2. assumption.
    + simpl. constructor. eapply IHX.
  - simpl. constructor. induction X.
    + destruct p as [p1 p2]. constructor.
      eapply p2. assumption.
    + simpl. constructor. eapply IHX.
  - simpl.
    apply OnOne2_length in X as hl. rewrite <- hl. clear hl.
    generalize #|mfix0|. intro n.
    constructor.
    induction X.
    + destruct p as [[p1 p2] p3]. inversion p3.
      simpl. constructor. split.
      * eapply p2. assumption.
      * simpl. f_equal ; auto. f_equal ; auto.
        f_equal. assumption.
    + simpl. constructor. eapply IHX.
  - simpl.
    apply OnOne2_length in X as hl. rewrite <- hl. clear hl.
    eapply fix_red_body.
    Fail induction X using OnOne2_ind_l.
    revert mfix0 mfix1 X.
    refine (
      OnOne2_ind_l _
        (fun (L : mfixpoint term) (x y : def term) =>
           (red1 Σ (Γ ,,, fix_context L) (dbody x) (dbody y)
           × (forall (Δ0 : list context_decl) (f0 : nat -> nat),
                 urenaming Δ0 (Γ ,,, fix_context L) f0 ->
                 red1 Σ Δ0 (rename f0 (dbody x)) (rename f0 (dbody y))))
           × (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)
        )
        (fun L mfix0 mfix1 o =>
           OnOne2
             (fun x y : def term =>
                red1 Σ (Δ ,,, fix_context (map (map_def (rename f) (rename (shiftn #|L| f))) L)) (dbody x) (dbody y)
                × (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y))
             (map (map_def (rename f) (rename (shiftn #|L| f))) mfix0)
             (map (map_def (rename f) (rename (shiftn #|L| f))) mfix1)
        )
        _ _
    ).
    + intros L x y l [[p1 p2] p3].
      inversion p3.
      simpl. constructor. split.
      * eapply p2. rewrite <- rename_fix_context.
        rewrite <- fix_context_length.
        eapply urenaming_context.
        assumption.
      * simpl. easy.
    + intros L x l l' h ih.
      simpl. constructor. eapply ih.
  - simpl.
    apply OnOne2_length in X as hl. rewrite <- hl. clear hl.
    generalize #|mfix0|. intro n.
    constructor.
    induction X.
    + destruct p as [[p1 p2] p3]. inversion p3.
      simpl. constructor. split.
      * eapply p2. assumption.
      * simpl. f_equal ; auto. f_equal ; auto.
        f_equal. assumption.
    + simpl. constructor. eapply IHX.
  - simpl.
    apply OnOne2_length in X as hl. rewrite <- hl. clear hl.
    eapply cofix_red_body.
    Fail induction X using OnOne2_ind_l.
    revert mfix0 mfix1 X.
    refine (
      OnOne2_ind_l _
        (fun (L : mfixpoint term) (x y : def term) =>
           (red1 Σ (Γ ,,, fix_context L) (dbody x) (dbody y)
           × (forall (Δ0 : list context_decl) (f0 : nat -> nat),
                 urenaming Δ0 (Γ ,,, fix_context L) f0 ->
                 red1 Σ Δ0 (rename f0 (dbody x)) (rename f0 (dbody y))))
           × (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)
        )
        (fun L mfix0 mfix1 o =>
           OnOne2
             (fun x y : def term =>
                red1 Σ (Δ ,,, fix_context (map (map_def (rename f) (rename (shiftn #|L| f))) L)) (dbody x) (dbody y)
                × (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y))
             (map (map_def (rename f) (rename (shiftn #|L| f))) mfix0)
             (map (map_def (rename f) (rename (shiftn #|L| f))) mfix1)
        )
        _ _
    ).
    + intros L x y l [[p1 p2] p3].
      inversion p3.
      simpl. constructor. split.
      * eapply p2. rewrite <- rename_fix_context.
        rewrite <- fix_context_length.
        eapply urenaming_context.
        assumption.
      * simpl. easy.
    + intros L x l l' h ih.
      simpl. constructor. eapply ih.
Qed.

Lemma meta_conv :
  forall Σ Γ t A B,
    Σ ;;; Γ |- t : A ->
    A = B ->
    Σ ;;; Γ |- t : B.
Proof.
  intros Σ Γ t A B h []. assumption.
Qed.

(* Could be more precise *)
Lemma instantiate_params_subst_length :
  forall params pars s t s' t',
    instantiate_params_subst params pars s t = Some (s', t') ->
    #|params| + #|s| = #|s'|.
Proof.
  intros params pars s t s' t' h.
  induction params in pars, s, t, s', t', h |- *.
  - cbn in h. destruct pars. all: try discriminate.
    inversion h. reflexivity.
  - cbn in h. destruct (decl_body a).
    + destruct t. all: try discriminate.
      cbn. eapply IHparams in h. cbn in h. lia.
    + destruct t. all: try discriminate.
      destruct pars. 1: discriminate.
      cbn. eapply IHparams in h. cbn in h. lia.
Qed.

Lemma instantiate_params_subst_inst :
  forall params pars s t σ s' t',
    instantiate_params_subst params pars s t = Some (s', t') ->
    instantiate_params_subst
      (mapi_rec (fun i decl => inst_decl (⇑^i σ) decl) params #|s|)
      (map (inst σ) pars)
      (map (inst σ) s)
      t.[⇑^#|s| σ]
    = Some (map (inst σ) s', t'.[⇑^(#|s| + #|params|) σ]).
Proof.
  intros params pars s t σ s' t' h.
  induction params in pars, s, t, σ, s', t', h |- *.
  - simpl in *. destruct pars. 2: discriminate.
    simpl. inversion h. subst. clear h.
    f_equal. f_equal. f_equal. f_equal. omega.
  - simpl in *. destruct (decl_body a).
    + simpl. destruct t. all: try discriminate.
      simpl. eapply IHparams with (σ := σ) in h.
      simpl in h.
      replace (#|s| + S #|params|)
        with (S (#|s| + #|params|))
        by omega.
      rewrite <- h. f_equal.
      * f_equal. autorewrite with sigma.
        eapply inst_ext. intro i.
        unfold Upn, subst_consn, subst_compose.
        case_eq (nth_error s i).
        -- intros t e.
           rewrite nth_error_idsn_Some.
           ++ eapply nth_error_Some_length. eassumption.
           ++ simpl.
              rewrite nth_error_map. rewrite e. simpl.
              reflexivity.
        -- intro neq.
           rewrite nth_error_idsn_None.
           ++ eapply nth_error_None. assumption.
           ++ simpl. rewrite idsn_length.
              autorewrite with sigma.
              rewrite <- subst_ids. eapply inst_ext. intro j.
              cbn. unfold ids. rewrite map_length.
              replace (#|s| + j - #|s|) with j by omega.
              rewrite nth_error_map.
              erewrite (iffRL (nth_error_None _ _)) by omega.
              simpl. reflexivity.
      * autorewrite with sigma. reflexivity.
    + simpl. destruct t. all: try discriminate.
      simpl. destruct pars. 1: discriminate.
      simpl. eapply IHparams with (σ := σ) in h. simpl in h.
      replace (#|s| + S #|params|)
        with (S (#|s| + #|params|))
        by omega.
      rewrite <- h.
      f_equal. autorewrite with sigma. reflexivity.
Qed.

Lemma inst_decl_closed :
  forall σ k d,
    closed_decl k d ->
    inst_decl (⇑^k σ) d = d.
Proof.
  intros σ k d.
  case: d => na [body|] ty. all: rewrite /closed_decl /inst_decl /map_decl /=.
  - move /andP => [cb cty]. rewrite !inst_closed //.
  - move => cty. rewrite !inst_closed //.
Qed.

Lemma closed_tele_inst :
  forall σ ctx,
    closed_ctx ctx ->
    mapi (fun i decl => inst_decl (⇑^i σ) decl) (List.rev ctx) =
    List.rev ctx.
Proof.
  intros σ ctx.
  rewrite /closedn_ctx /mapi. simpl. generalize 0.
  induction ctx using rev_ind; try easy.
  move => n.
  rewrite /closedn_ctx !rev_app_distr /id /=.
  move /andP => [closedx Hctx].
  rewrite inst_decl_closed //.
  f_equal. now rewrite IHctx.
Qed.

Lemma instantiate_params_inst :
  forall params pars T σ T',
    closed_ctx params ->
    instantiate_params params pars T = Some T' ->
    instantiate_params params (map (inst σ) pars) T.[σ] = Some T'.[σ].
Proof.
  intros params pars T σ T' hcl e.
  unfold instantiate_params in *.
  case_eq (instantiate_params_subst (List.rev params) pars [] T) ;
    try solve [ intro bot ; rewrite bot in e ; discriminate e ].
  intros [s' t'] e'. rewrite e' in e. inversion e. subst. clear e.
  eapply instantiate_params_subst_inst with (σ := σ) in e'.
  simpl in e'.
  autorewrite with sigma in e'.
  rewrite List.rev_length in e'.
  match type of e' with
  | context [ mapi_rec ?f ?l 0 ] =>
    change (mapi_rec f l 0) with (mapi f l) in e'
  end.
  rewrite closed_tele_inst in e' ; auto.
  rewrite e'. f_equal. autorewrite with sigma.
  eapply inst_ext. intro i.
  unfold Upn, subst_consn, subst_compose.
  rewrite idsn_length map_length.
  apply instantiate_params_subst_length in e'.
  rewrite List.rev_length map_length in e'. cbn in e'.
  replace (#|params| + 0) with #|params| in e' by lia.
  rewrite e'. clear e'.
  case_eq (nth_error s' i).
  - intros t e.
    rewrite nth_error_idsn_Some.
    { eapply nth_error_Some_length in e. lia. }
    simpl.
    rewrite nth_error_map. rewrite e. simpl. reflexivity.
  - intro neq.
    rewrite nth_error_idsn_None.
    { eapply nth_error_None in neq. lia. }
    simpl. autorewrite with sigma. rewrite <- subst_ids.
    eapply inst_ext. intro j.
    cbn. unfold ids.
    replace (#|s'| + j - #|s'|) with j by omega.
    rewrite nth_error_map.
    erewrite (iffRL (nth_error_None _ _)) by omega.
    simpl. reflexivity.
Qed.

Corollary instantiate_params_rename :
  forall params pars T f T',
    closed_ctx params ->
    instantiate_params params pars T = Some T' ->
    instantiate_params params (map (rename f) pars) (rename f T) =
    Some (rename f T').
Proof.
  intros params pars T f T' hcl e.
  eapply instantiate_params_inst with (σ := ren f) in e. 2: auto.
  autorewrite with sigma. rewrite <- e. f_equal.
  induction pars in |- *. 1: reflexivity.
  simpl. autorewrite with sigma. easy.
Qed.

Lemma typed_inst :
  forall Σ Γ t T k σ,
    wf Σ.1 ->
    k >= #|Γ| ->
    Σ ;;; Γ |- t : T ->
    T.[⇑^k σ] = T /\ t.[⇑^k σ] = t.
Proof.
  intros Σ Γ t T k σ hΣ hk h.
  apply typing_wf_local in h as hΓ.
  apply typecheck_closed in h. all: eauto.
  destruct h as [_ hcl].
  rewrite -> andb_and in hcl. destruct hcl as [clt clT].
  pose proof (closed_upwards k clt) as ht.
  pose proof (closed_upwards k clT) as hT.
  forward ht by lia.
  forward hT by lia.
  rewrite !inst_closed. all: auto.
Qed.

Lemma inst_wf_local :
  forall Σ Γ σ,
    wf Σ.1 ->
    wf_local Σ Γ ->
    inst_context σ Γ = Γ.
Proof.
  intros Σ Γ σ hΣ h.
  induction h.
  - reflexivity.
  - unfold inst_context, snoc. rewrite fold_context_snoc0.
    unfold snoc. f_equal. all: auto.
    unfold map_decl. simpl. unfold vass. f_equal.
    destruct t0 as [s ht]. eapply typed_inst. all: eauto.
  - unfold inst_context, snoc. rewrite fold_context_snoc0.
    unfold snoc. f_equal. all: auto.
    unfold map_decl. simpl. unfold vdef. f_equal.
    + f_equal. eapply typed_inst. all: eauto.
    + eapply typed_inst in t1 as [? _]. all: eauto.
Qed.

Definition inst_mutual_inductive_body σ m :=
  map_mutual_inductive_body (fun i => inst (⇑^i σ)) m.

Lemma inst_declared_minductive :
  forall Σ cst decl σ,
    wf Σ ->
    declared_minductive Σ cst decl ->
    inst_mutual_inductive_body σ decl = decl.
Proof.
  unfold declared_minductive.
  intros Σ cst decl σ hΣ h.
  eapply lookup_on_global_env in h ; eauto. simpl in h.
  destruct h as [Σ' [hΣ' decl']].
  destruct decl as [fi npars params bodies univs]. simpl. f_equal.
  - eapply inst_wf_local. all: eauto.
    eapply onParams in decl'. auto.
  - apply onInductives in decl'.
    revert decl'. generalize bodies at 2 4 5. intros bodies' decl'.
    eapply Alli_mapi_id in decl'. all: eauto.
    clear decl'. intros n [na ty ke ct pr] hb. simpl.
    destruct (decompose_prod_assum [] ty) as [c t] eqn:e1.
    destruct (decompose_prod_assum [] ty.[⇑^0 σ]) as [c' t'] eqn:e2.
    destruct hb as [indices s arity_eq onAr csorts onConstr onProj sorts].
    simpl in *.
    assert (e : ty.[⇑^0 σ] = ty).
    { destruct onAr as [s' h'].
      eapply typed_inst in h' as [_ ?]. all: eauto.
    }
    rewrite e in e2. rewrite e1 in e2.
    revert e2. intros [= <- <-].
    rewrite e. f_equal.
    + eapply All_map_id. eapply All2_All_left; tea.
      intros [[x p] n'] y [[?s Hty] [cs Hargs]].
      unfold on_pi2; cbn; f_equal; f_equal.
      eapply typed_inst. all: eauto.
    + destruct (eq_dec pr []) as [hp | hp]. all: subst. all: auto.
      specialize (onProj hp).
      apply on_projs in onProj.
      apply (Alli_map_id onProj).
      intros n1 [x p]. unfold on_projection. simpl.
      intros [? hty].
      unfold on_snd. simpl. f_equal.
      eapply typed_inst. all: eauto.
      simpl.
      rewrite smash_context_length context_assumptions_fold.
      simpl. auto.
Qed.

Lemma inst_declared_inductive :
  forall Σ ind mdecl idecl σ,
    wf Σ ->
    declared_inductive Σ mdecl ind idecl ->
    map_one_inductive_body
      (context_assumptions mdecl.(ind_params))
      #|arities_context mdecl.(ind_bodies)|
      (fun i => inst (⇑^i σ))
      ind.(inductive_ind)
      idecl
    = idecl.
Proof.
  intros Σ ind mdecl idecl σ hΣ [hmdecl hidecl].
  eapply inst_declared_minductive with (σ := σ) in hmdecl. all: auto.
  unfold inst_mutual_inductive_body in hmdecl.
  destruct mdecl as [fi npars params bodies univs]. simpl in *.
  injection hmdecl. intro e. clear hmdecl.
  pose proof hidecl as hidecl'.
  rewrite <- e in hidecl'.
  rewrite nth_error_mapi in hidecl'.
  clear e.
  unfold option_map in hidecl'. rewrite hidecl in hidecl'.
  congruence.
Qed.

Lemma inst_destArity :
  forall ctx t σ args s,
    destArity ctx t = Some (args, s) ->
    destArity (inst_context σ ctx) t.[⇑^#|ctx| σ] =
    Some (inst_context σ args, s).
Proof.
  intros ctx t σ args s h.
  induction t in ctx, σ, args, s, h |- * using term_forall_list_ind.
  all: simpl in *. all: try discriminate.
  - inversion h. reflexivity.
  - erewrite <- IHt2 ; try eassumption.
    simpl. autorewrite with sigma. reflexivity.
  - erewrite <- IHt3. all: try eassumption.
    simpl. autorewrite with sigma. reflexivity.
Qed.


Lemma types_of_case_rename :
  forall Σ ind mdecl idecl npar args u p pty indctx pctx ps btys f,
    wf Σ ->
    declared_inductive Σ mdecl ind idecl ->
    types_of_case ind mdecl idecl (firstn npar args) u p pty =
    Some (indctx, pctx, ps, btys) ->
    types_of_case
      ind mdecl idecl
      (firstn npar (map (rename f) args)) u (rename f p) (rename f pty)
    =
    Some (
        rename_context f indctx,
        rename_context f pctx,
        ps,
        map (on_snd (rename f)) btys
    ).
Admitted.

(* TODO MOVE *)
Lemma declared_constant_closed_type :
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
  - eapply typecheck_closed in decl' as [? e]. 2: auto. 2: constructor.
    move/andP in e. destruct e. assumption.
  - cbn in decl'. destruct decl' as [s h].
    eapply typecheck_closed in h as [? e]. 2: auto. 2: constructor.
    move/andP in e. destruct e. assumption.
Qed.

(* TODO MOVE *)
Lemma declared_inductive_closed_type :
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
  eapply typecheck_closed in h as [? e]. 2: auto. 2: constructor.
  move/andP in e. destruct e. assumption.
Qed.

(* TODO MOVE *)
Lemma declared_inductive_closed_constructors :
  forall Σ ind mdecl idecl,
      wf Σ ->
      declared_inductive Σ mdecl ind idecl ->
      All (fun '(na, t, n) => closedn #|arities_context mdecl.(ind_bodies)| t)
          idecl.(ind_ctors).
Proof.
  intros Σ ind mdecl idecl hΣ h.
  unfold declared_inductive in h. destruct h as [hmdecl hidecl].
  red in hmdecl.
  eapply lookup_on_global_env in hmdecl. 2: eauto.
  destruct hmdecl as [Σ' [wfΣ' decl']].
  red in decl'. destruct decl' as [h ? ? ?].
  eapply Alli_nth_error in h. 2: eassumption.
  simpl in h. destruct h as [? ? ? ? ? h ? ?].
  unfold on_constructors in h.
  clear - h wfΣ'.
  induction h.
  - constructor.
  - econstructor.
    + destruct x as [[? t] ?].
      unfold on_constructor in r. cbn in r.
      destruct r as [[? ht] ?].
      eapply typecheck_closed in ht as [? e]. 2: auto.
      2: eapply typing_wf_local ; eauto.
      move/andP in e. destruct e. assumption.
    + assumption.
Qed.

(* TODO MOVE *)
Lemma declared_minductive_closed_inds :
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

(* TODO MOVE *)
Lemma declared_inductive_closed_inds :
  forall Σ ind mdecl idecl u,
      wf Σ ->
      declared_inductive Σ mdecl ind idecl ->
      forallb (closedn 0) (inds (inductive_mind ind) u (ind_bodies mdecl)).
Proof.
  intros Σ ind mdecl idecl u hΣ h.
  unfold declared_inductive in h. destruct h as [hmdecl hidecl].
  eapply declared_minductive_closed_inds in hmdecl. all: eauto.
Qed.

(* TODO MOVE *)
Lemma declared_constructor_closed_type :
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

Lemma declared_projection_closed_type :
  forall Σ mdecl idecl p pdecl,
    wf Σ ->
    declared_projection Σ mdecl idecl p pdecl ->
    closedn (S (ind_npars mdecl)) pdecl.2.
Proof.
  intros Σ mdecl idecl p pdecl hΣ [[hmdecl hidecl] [hpdecl hnpar]].
  eapply declared_decl_closed in hmdecl. 2: auto.
  simpl in hmdecl.
  pose proof (onNpars _ _ _ _ hmdecl) as e.
  apply onInductives in hmdecl.
  eapply nth_error_alli in hmdecl. 2: eauto.
  pose proof (onProjections hmdecl) as onp.
  forward onp.
  { eapply nth_error_Some_non_nil in hpdecl. assumption. }
  eapply on_projs, nth_error_alli in onp. 2: eassumption.
  move: onp => /= /andb_and[hd _]. simpl in hd.
  rewrite smash_context_length in hd. simpl in *.
  rewrite e in hd. assumption.
Qed.

Lemma cumul_rename :
  forall Σ Γ Δ f A B,
    wf Σ.1 ->
    renaming Σ Δ Γ f ->
    Σ ;;; Γ |- A <= B ->
    Σ ;;; Δ |- rename f A <= rename f B.
Proof.
  intros Σ Γ Δ f A B hΣ hf h.
  induction h.
  - eapply cumul_refl. eapply eq_term_upto_univ_rename. assumption.
  - eapply cumul_red_l.
    + eapply red1_rename. all: try eassumption.
      apply hf.
    + assumption.
  - eapply cumul_red_r.
    + eassumption.
    + eapply red1_rename. all: try eassumption.
      apply hf.
Qed.

End Renaming.


Section Sigma.

Context `{checker_flags}.

(* Well-typedness of a substitution *)

Definition well_subst Σ (Γ : context) σ (Δ : context) :=
  forall x decl,
    nth_error Γ x = Some decl ->
    Σ ;;; Δ |- σ x : ((lift0 (S x)) (decl_type decl)).[ σ ] ×
    (forall b,
        decl.(decl_body) = Some b ->
        σ x = b.[⇑^(S x) σ]
    ).

Notation "Σ ;;; Δ ⊢ σ : Γ" :=
  (well_subst Σ Γ σ Δ) (at level 50, Δ, σ, Γ at next level).

End Sigma.
