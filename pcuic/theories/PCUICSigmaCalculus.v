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

Lemma build_branches_type_rename :
  forall ind mdecl idecl args u p brs f,
    closed_ctx (subst_instance_context u (ind_params mdecl)) ->
    map_option_out (build_branches_type ind mdecl idecl args u p) = Some brs ->
    map_option_out (
        build_branches_type
          ind
          mdecl
          (map_one_inductive_body
             (context_assumptions (ind_params mdecl))
             #|arities_context (ind_bodies mdecl)|
             (fun i : nat => rename (shiftn i f))
             (inductive_ind ind)
             idecl
          )
          (map (rename f) args)
          u
          (rename f p)
    ) = Some (map (on_snd (rename f)) brs).
Proof.
  intros ind mdecl idecl args u p brs f hcl.
  unfold build_branches_type.
  destruct idecl as [ina ity ike ict ipr]. simpl.
  unfold mapi.
  generalize 0 at 3 6.
  intros n h.
  induction ict in brs, n, h, f |- *.
  - cbn in *. inversion h. reflexivity.
  - cbn. cbn in h.
    lazymatch type of h with
    | match ?t with _ => _ end = _ =>
      case_eq (t) ;
        try (intro bot ; rewrite bot in h ; discriminate h)
    end.
    intros [m t] e'. rewrite e' in h.
    destruct a as [[na ta] ar].
    lazymatch type of e' with
    | match ?expr with _ => _ end = _ =>
      case_eq (expr) ;
        try (intro bot ; rewrite bot in e' ; discriminate e')
    end.
    intros ty ety. rewrite ety in e'.
    eapply instantiate_params_rename with (f := f) in ety as ety'.
    2: assumption.
    simpl.
    match goal with
    | |- context [ instantiate_params _ _ ?t ] =>
      match type of ety' with
      | instantiate_params _ _ ?t' = _ =>
        replace t with t' ; revgoals
      end
    end.
    { clear e' ety h IHict ety'.
      rewrite <- rename_subst_instance_constr.
      rewrite arities_context_length.
      autorewrite with sigma.
      eapply inst_ext. intro i.
      unfold shiftn, ren, subst_compose, subst_consn. simpl.
      case_eq (nth_error (inds (inductive_mind ind) u (ind_bodies mdecl)) i).
      + intros t' e.
        eapply nth_error_Some_length in e as hl.
        rewrite inds_length in hl.
        destruct (Nat.ltb_spec i #|ind_bodies mdecl|) ; try lia.
        rewrite e.
        give_up.
      + intro neq.
        eapply nth_error_None in neq as hl.
        rewrite inds_length in hl.
        rewrite inds_length.
        destruct (Nat.ltb_spec i #|ind_bodies mdecl|) ; try lia.
        unfold ids. simpl.
        rewrite (iffRL (nth_error_None _ _)).
        { rewrite inds_length. lia. }
        f_equal. lia.
    }
    rewrite ety'.
    case_eq (decompose_prod_assum [] ty). intros sign ccl edty.
    rewrite edty in e'.
    (* TODO inst edty *)
    case_eq (chop (ind_npars mdecl) (snd (decompose_app ccl))).
    intros paramrels args' ech. rewrite ech in e'.
    (* TODO inst ech *)
    inversion e'. subst. clear e'.
    lazymatch type of h with
    | match ?t with _ => _ end = _ =>
      case_eq (t) ;
        try (intro bot ; rewrite bot in h ; discriminate h)
    end.
    intros tl etl. rewrite etl in h.
    (* TODO inst etl *)
    inversion h. subst. clear h.
    (* edestruct IHict as [brtys' [eq' he]]. *)
    (* + eauto. *)
    (* + eexists. rewrite eq'. split. *)
    (*   * reflexivity. *)
    (*   * constructor ; auto. *)
    (*     simpl. split ; auto. *)
    (*     eapply eq_term_upto_univ_it_mkProd_or_LetIn ; auto. *)
    (*     eapply eq_term_upto_univ_mkApps. *)
    (*     -- eapply eq_term_upto_univ_lift. assumption. *)
    (*     -- apply All2_same. intro. apply eq_term_upto_univ_refl ; auto. *)
Admitted.

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
    destruct hb as [indices s arity_eq onAr onConstr onProj sorts].
    simpl in *.
    assert (e : ty.[⇑^0 σ] = ty).
    { destruct onAr as [s' h'].
      eapply typed_inst in h' as [_ ?]. all: eauto.
    }
    rewrite e in e2. rewrite e1 in e2.
    revert e2. intros [= <- <-].
    rewrite e. f_equal.
    + apply (Alli_map_id onConstr).
      intros n1 [[x p] n'] [[s' hty] _].
      unfold on_pi2. simpl. f_equal. f_equal.
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
Proof.
  intros Σ ind mdecl idecl npar args u p pty indctx pctx ps btys f hΣ hdecl h.
  unfold types_of_case in *.
  case_eq (instantiate_params (subst_instance_context u (ind_params mdecl)) (firstn npar args) (subst_instance_constr u (ind_type idecl))) ;
    try solve [ intro bot ; rewrite bot in h ; discriminate h ].
  intros ity eity. rewrite eity in h.
  pose proof (on_declared_inductive hΣ hdecl) as [onmind onind].
  apply onParams in onmind as Hparams.
  assert (closedparams : closed_ctx (subst_instance_context u (ind_params mdecl))).
  { rewrite closedn_subst_instance_context.
    eapply PCUICWeakening.closed_wf_local. all: eauto. eauto. }
  epose proof (inst_declared_inductive _ ind mdecl idecl (ren f) hΣ) as hi.
  forward hi by assumption. rewrite <- hi.
  eapply instantiate_params_rename with (f := f) in eity ; auto.
  rewrite -> ind_type_map.
  rewrite firstn_map.
  lazymatch type of eity with
  | ?t = _ =>
    lazymatch goal with
    | |- match ?t' with _ => _ end = _ =>
      replace t' with t ; revgoals
    end
  end.
  { autorewrite with sigma.
    rewrite <- !rename_inst.
    now rewrite rename_subst_instance_constr. }
  rewrite eity.
  case_eq (destArity [] ity) ;
    try solve [ intro bot ; rewrite bot in h ; discriminate h ].
  intros [args0 ?] ear. rewrite ear in h.
  eapply inst_destArity with (σ := ren f) in ear as ear'.
  simpl in ear'.
  lazymatch type of ear' with
  | ?t = _ =>
    lazymatch goal with
    | |- match ?t' with _ => _ end = _ =>
      replace t' with t ; revgoals
    end
  end.
  { autorewrite with sigma. reflexivity. }
  rewrite ear'.
  case_eq (destArity [] pty) ;
    try solve [ intro bot ; rewrite bot in h ; discriminate h ].
  intros [args' s'] epty. rewrite epty in h.
  eapply inst_destArity with (σ := ren f) in epty as epty'.
  simpl in epty'.
  lazymatch type of epty' with
  | ?t = _ =>
    lazymatch goal with
    | |- match ?t' with _ => _ end = _ =>
      replace t' with t ; revgoals
    end
  end.
  { autorewrite with sigma. reflexivity. }
  rewrite epty'.
  case_eq (map_option_out (build_branches_type ind mdecl idecl (firstn npar args) u p)) ;
    try solve [ intro bot ; rewrite bot in h ; discriminate h ].
  intros brtys ebrtys. rewrite ebrtys in h.
  inversion h. subst. clear h.
  eapply build_branches_type_rename with (f := f) in ebrtys as ebrtys'.
  2: assumption.
  lazymatch type of ebrtys' with
  | ?t = _ =>
    lazymatch goal with
    | |- match ?t' with _ => _ end = _ =>
      replace t' with t ; revgoals
    end
  end.
  { f_equal. f_equal. unfold map_one_inductive_body. destruct idecl.
    simpl. f_equal.
    - autorewrite with sigma.
      eapply inst_ext. intro j.
      unfold ren, shiftn. simpl.
      f_equal. f_equal. lia.
    - clear. induction ind_ctors. 1: reflexivity.
      simpl. unfold on_pi2. destruct a. simpl.
      destruct p. simpl. f_equal. 2: easy.
      f_equal. f_equal.
      autorewrite with sigma.
      eapply inst_ext. intro j.
      unfold ren, Upn, shiftn, subst_consn.
      rewrite arities_context_length.
      destruct (Nat.ltb_spec j #|ind_bodies mdecl|).
      + rewrite nth_error_idsn_Some. all: easy.
      + rewrite nth_error_idsn_None. 1: auto.
        unfold subst_compose, shiftk. simpl.
        rewrite idsn_length. reflexivity.
    - clear. induction ind_projs. 1: auto.
      simpl. destruct a. unfold on_snd. simpl.
      f_equal. 2: easy.
      f_equal. autorewrite with sigma.
      eapply inst_ext. intro j.
      unfold Upn, Up, ren, shiftn, subst_cons, subst_consn, subst_compose,
      shift, shiftk.
      destruct j.
      + simpl. reflexivity.
      + simpl.
        destruct (Nat.ltb_spec (S j) (S (context_assumptions (ind_params mdecl)))).
        * rewrite nth_error_idsn_Some. 1: lia.
          simpl. reflexivity.
        * rewrite nth_error_idsn_None. 1: lia.
          simpl. rewrite idsn_length. reflexivity.
  }
  rewrite ebrtys'. autorewrite with sigma. reflexivity.
Qed.

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
  simpl in h. destruct h as [? ? ? ? h ? ?].
  unfold on_constructors in h.
  clear - h wfΣ'.
  induction h.
  - constructor.
  - econstructor.
    + destruct hd as [[? t] ?].
      unfold on_constructor in p. cbn in p.
      destruct p as [[? ht] ?].
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

Lemma typing_rename :
  forall Σ Γ Δ f t A,
    wf Σ.1 ->
    wf_local Σ Γ ->
    renaming Σ Δ Γ f ->
    Σ ;;; Γ |- t : A ->
    Σ ;;; Δ |- rename f t : rename f A.
Proof.
  intros Σ Γ Δ f t A hΣ hΓ hf h.
  revert Σ hΣ Γ hΓ t A h Δ f hf.
  apply (typing_ind_env (fun Σ Γ t T => forall Δ f,
    renaming Σ Δ Γ f ->
    Σ ;;; Δ |- rename f t : rename f T
  )).
  - intros Σ wfΣ Γ wfΓ n decl isdecl ihΓ Δ f [hΔ hf].
    simpl. eapply hf in isdecl as h.
    destruct h as [decl' [isdecl' [h1 h2]]].
    rewrite h1. econstructor. all: auto.
  - intros Σ wfΣ Γ wfΓ l X H0 Δ f [hΔ hf].
    simpl. constructor. all: auto.
  - intros Σ wfΣ Γ wfΓ na A B s1 s2 X hA ihA hB ihB Δ f hf.
    simpl.
    econstructor.
    + eapply ihA. assumption.
    + eapply ihB.
      eapply renaming_vass. 2: auto.
      constructor.
      * destruct hf as [hΔ hf]. auto.
      * simpl. exists s1. eapply ihA. assumption.
  - intros Σ wfΣ Γ wfΓ na A t s1 B X hA ihA ht iht Δ f hf.
    simpl. econstructor.
    + eapply ihA. assumption.
    + eapply iht.
      eapply renaming_vass. 2: auto.
      constructor.
      * destruct hf as [hΔ hf]. auto.
      * simpl. exists s1. eapply ihA. assumption.
  - intros Σ wfΣ Γ wfΓ na b B t s1 A X hB ihB hb ihb ht iht Δ f hf.
    simpl. econstructor.
    + eapply ihB. assumption.
    + eapply ihb. assumption.
    + eapply iht.
      eapply renaming_vdef. 2: auto.
      constructor.
      * destruct hf. assumption.
      * simpl. eexists. eapply ihB. assumption.
      * simpl. eapply ihb. assumption.
  - intros Σ wfΣ Γ wfΓ t na A B u X ht iht hu ihu Δ f hf.
    simpl. eapply meta_conv.
    + econstructor.
      * simpl in iht. eapply iht. assumption.
      * eapply ihu. assumption.
    + autorewrite with sigma.
      eapply inst_ext. intro i.
      unfold subst_cons, ren, shiftn, subst_compose. simpl.
      destruct i.
      * simpl. reflexivity.
      * simpl. replace (i - 0) with i by lia.
        reflexivity.
  - intros Σ wfΣ Γ wfΓ cst u decl X X0 isdecl hconst Δ f hf.
    simpl. eapply meta_conv.
    + constructor. all: eauto.
      destruct hf. assumption.
    + rewrite rename_subst_instance_constr. f_equal.
      rewrite rename_closed. 2: auto.
      eapply declared_constant_closed_type. all: eauto.
  - intros Σ wfΣ Γ wfΓ ind u mdecl idecl isdecl X X0 hconst Δ σ hf.
    simpl. eapply meta_conv.
    + econstructor. all: eauto.
      destruct hf. assumption.
    + rewrite rename_subst_instance_constr. f_equal.
      rewrite rename_closed. 2: auto.
      eapply declared_inductive_closed_type. all: eauto.
  - intros Σ wfΣ Γ wfΓ ind i u mdecl idecl cdecl isdecl X X0 hconst Δ f hf.
    simpl. eapply meta_conv.
    + econstructor. all: eauto. destruct hf. assumption.
    + rewrite rename_closed. 2: reflexivity.
      eapply declared_constructor_closed_type. all: eauto.
  - intros Σ wfΣ Γ wfΓ ind u npar p c brs args mdecl idecl isdecl X X0 e pars
           pty hp indctx pctx ps btys htoc hca hel ihp hc ihc hbrs Δ f hf.
    simpl.
    rewrite rename_mkApps.
    rewrite map_app. simpl.
    rewrite map_skipn.
    (* eapply types_of_case_inst with (σ := σ) in htoc. all: try eassumption. *)
    (* eapply type_Case. *)
    (* + eassumption. *)
    (* + assumption. *)
    (* + eapply ihp. all: auto. *)
    (* + eassumption. *)
    (* + admit. *)
    (* + assumption. *)
    (* + specialize (ihc _ _ hΔ hσ). autorewrite with sigma in ihc. *)
    (*   eapply ihc. *)
    (* + admit. *)
    admit.
  - intros Σ wfΣ Γ wfΓ p c u mdecl idecl pdecl isdecl args X X0 hc ihc e ty
           Δ f hf.
    simpl. eapply meta_conv.
    + econstructor.
      * eassumption.
      * eapply meta_conv.
        -- eapply ihc. assumption.
        -- rewrite rename_mkApps. simpl. reflexivity.
      * rewrite map_length. assumption.
    + rewrite rename_subst0. simpl. rewrite map_rev. f_equal.
      rewrite rename_subst_instance_constr. f_equal.
      rewrite rename_closedn. 2: reflexivity.
      eapply declared_projection_closed_type in isdecl. 2: auto.
      rewrite List.rev_length. rewrite e. assumption.
  - intros Σ wfΣ Γ wfΓ mfix n decl types hdecl H1 X ihmfix Δ f hf.
    assert (hΔ' : wf_local Σ (Δ ,,, rename_context f (fix_context mfix))).
    { subst types. set (Ξ := fix_context mfix) in *.
      clearbody Ξ. clear - X hf.
      induction Ξ as [| [na [b|] A] Ξ ih].
      - apply hf.
      - rewrite rename_context_snoc. simpl.
        unfold rename_decl, map_decl. simpl.
        simpl in X. inversion X. subst. simpl in *.
        destruct X1 as [? [h1 ih1]].
        destruct X2 as [h2 ih2].
        constructor.
        + eapply ih. assumption.
        + simpl. eexists. eapply ih1.
          split.
          * eapply ih. assumption.
          * eapply urenaming_context. apply hf.
        + simpl. eapply ih2.
          split.
          * eapply ih. assumption.
          * eapply urenaming_context. apply hf.
      - rewrite rename_context_snoc. simpl.
        unfold rename_decl, map_decl. simpl.
        simpl in X. inversion X. subst. simpl in *.
        destruct X1 as [? [h1 ih1]].
        constructor.
        + eapply ih. assumption.
        + simpl. eexists. eapply ih1.
          split.
          * eapply ih. assumption.
          * eapply urenaming_context. apply hf.
    }
    simpl. eapply meta_conv.
    + eapply type_Fix.
      * eapply fix_guard_rename. assumption.
      * rewrite nth_error_map. rewrite hdecl. simpl. reflexivity.
      * rewrite <- rename_fix_context. eapply hΔ'.
      * eapply forall_nth_error_All. intros i d e.
        rewrite nth_error_map in e.
        case_eq (nth_error mfix i).
        2: intros e' ; rewrite e' in e ; discriminate.
        intros d' e'. rewrite e' in e. simpl in e. inversion e as [ee].
        clear e. rename ee into e. subst.
        eapply All_nth_error in ihmfix as [[h1 h2] ih]. 2: exact e'.
        destruct d' as [na ty bo rarg]. simpl in *.
        split.
        -- rewrite <- rename_fix_context.
           eapply meta_conv.
           ++ eapply ih. split.
              ** assumption.
              ** rewrite <- fix_context_length. eapply urenaming_context.
                 apply hf.
           ++ autorewrite with sigma. subst types. rewrite fix_context_length.
              eapply inst_ext. intro j.
              unfold ren, lift_renaming, subst_compose, shiftn. simpl. f_equal.
              destruct (Nat.ltb_spec0 (#|mfix| + j) #|mfix|). 1: lia.
              f_equal. f_equal. lia.
        -- eapply isLambda_rename. assumption.
    + destruct decl as [na ty bo rarg]. simpl. reflexivity.
  - intros Σ wfΣ Γ wfΓ mfix n decl types hdecl X ihmfix hallow Δ f hf.
    assert (hΔ' : wf_local Σ (Δ ,,, rename_context f (fix_context mfix))).
    { subst types. set (Ξ := fix_context mfix) in *.
      clearbody Ξ. clear - X hf.
      induction Ξ as [| [na [b|] A] Ξ ih].
      - apply hf.
      - rewrite rename_context_snoc. simpl.
        unfold rename_decl, map_decl. simpl.
        simpl in X. inversion X. subst. simpl in *.
        destruct X1 as [? [h1 ih1]].
        destruct X2 as [h2 ih2].
        constructor.
        + eapply ih. assumption.
        + simpl. eexists. eapply ih1.
          split.
          * eapply ih. assumption.
          * eapply urenaming_context. apply hf.
        + simpl. eapply ih2.
          split.
          * eapply ih. assumption.
          * eapply urenaming_context. apply hf.
      - rewrite rename_context_snoc. simpl.
        unfold rename_decl, map_decl. simpl.
        simpl in X. inversion X. subst. simpl in *.
        destruct X1 as [? [h1 ih1]].
        constructor.
        + eapply ih. assumption.
        + simpl. eexists. eapply ih1.
          split.
          * eapply ih. assumption.
          * eapply urenaming_context. apply hf.
    }
    simpl. eapply meta_conv.
    + eapply type_CoFix.
      * assumption.
      * rewrite nth_error_map. rewrite hdecl. simpl. reflexivity.
      * rewrite <- rename_fix_context. eapply hΔ'.
      * eapply forall_nth_error_All. intros i d e.
        rewrite nth_error_map in e.
        case_eq (nth_error mfix i).
        2: intros e' ; rewrite e' in e ; discriminate.
        intros d' e'. rewrite e' in e. simpl in e. inversion e as [ee].
        clear e. rename ee into e. subst.
        eapply All_nth_error in ihmfix as [h ih]. 2: exact e'.
        destruct d' as [na ty bo rarg]. simpl in *.
        rewrite <- rename_fix_context.
        eapply meta_conv.
        -- eapply ih. split.
           ++ assumption.
           ++ rewrite <- fix_context_length. eapply urenaming_context.
              apply hf.
        -- autorewrite with sigma. subst types. rewrite fix_context_length.
           eapply inst_ext. intro j.
           unfold ren, lift_renaming, subst_compose, shiftn. simpl. f_equal.
           destruct (Nat.ltb_spec0 (#|mfix| + j) #|mfix|). 1: lia.
           f_equal. f_equal. lia.
    + destruct decl as [na ty bo rarg]. simpl. reflexivity.
  - intros Σ wfΣ Γ wfΓ t A B X ht iht hwf hcu Δ f hf.
    eapply type_Cumul.
    + eapply iht. assumption.
    + destruct hwf as [[[ctx [s [e h1]]] h2] | [s [hB ihB]]].
      * left.
        simpl in h2. eapply inst_destArity with (σ := ren f) in e as e'.
        cbn in e'.
        exists (rename_context f ctx), s. split.
        -- rewrite rename_context_inst_context. rewrite <- e'.
           f_equal. autorewrite with sigma. reflexivity.
        -- clear - h2 hf.
           induction ctx as [| [na [b|] A] Ξ ih].
           ++ apply hf.
           ++ rewrite rename_context_snoc. simpl.
              unfold rename_decl, map_decl. simpl.
              simpl in h2. inversion h2. subst. simpl in *.
              destruct tu as [? ?].
              constructor.
              ** eapply ih. eassumption.
              ** simpl. eexists. eapply X1.
                 split.
                 --- eapply ih. eassumption.
                 --- eapply urenaming_context. apply hf.
              ** simpl. eapply X0.
                 split.
                 --- eapply ih. eassumption.
                 --- eapply urenaming_context. apply hf.
           ++ rewrite rename_context_snoc. simpl.
              unfold rename_decl, map_decl. simpl.
              simpl in h2. inversion h2. subst. simpl in *.
              destruct tu as [? ?]. simpl in *.
              constructor.
              ** eapply ih. eassumption.
              ** simpl. eexists. eapply X0.
                 split.
                 --- eapply ih. eassumption.
                 --- eapply urenaming_context. apply hf.
      * right. eexists. eapply ihB. assumption.
    + eapply cumul_rename. all: eassumption.
Admitted.

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

Lemma well_subst_Up :
  forall Σ Γ Δ σ na A,
    wf_local Σ (Δ ,, vass na A.[σ]) ->
    Σ ;;; Δ ⊢ σ : Γ ->
    Σ ;;; Δ ,, vass na A.[σ] ⊢ ⇑ σ : Γ ,, vass na A.
Proof.
  intros Σ Γ Δ σ na A hΔ h [|n] decl e.
  - simpl in *. inversion e. subst. clear e. simpl.
    split.
    + eapply meta_conv.
      * econstructor ; auto.
        reflexivity.
      * simpl.
        autorewrite with sigma.
        eapply inst_ext. intro i.
        unfold subst_compose.
        eapply inst_ext. intro j.
        unfold shift, ren. reflexivity.
    + intros b e. discriminate.
  - simpl in *.
    specialize (h _ _ e) as [h1 h2].
    split.
Admitted.

Lemma well_subst_Up' :
  forall Σ Γ Δ σ na t A,
    Σ ;;; Δ ⊢ σ : Γ ->
    Σ ;;; Δ ,, vdef na t.[σ] A.[σ] ⊢ ⇑ σ : Γ ,, vdef na t A.
Proof.
  intros Σ Γ Δ σ na t A h [|n] decl e.
  - simpl in *. inversion e. subst. clear e. simpl.
    (* NEED commutation lemma between lift and inst *)
    admit.
  - simpl in *.
    specialize (h _ _ e).
Admitted.

(* (* Could be more precise *) *)
(* Lemma instantiate_params_subst_length : *)
(*   forall params pars s t s' t', *)
(*     instantiate_params_subst params pars s t = Some (s', t') -> *)
(*     #|params| >= #|pars|. *)
(* Proof. *)
(*   intros params pars s t s' t' h. *)
(*   induction params in pars, s, t, s', t', h |- *. *)
(*   - cbn in h. destruct pars. all: try discriminate. auto. *)
(*   - cbn in h. destruct (decl_body a). *)
(*     + destruct t. all: try discriminate. *)
(*       cbn. eapply IHparams in h. lia. *)
(*     + destruct t. all: try discriminate. *)
(*       destruct pars. 1: discriminate. *)
(*       cbn. eapply IHparams in h. lia. *)
(* Qed. *)

(* Lemma instantiate_params_length : *)
(*   forall params pars T T', *)
(*     instantiate_params params pars T = Some T' -> *)
(*     #|params| >= #|pars|. *)
(* Proof. *)
(*   intros params pars T T' e. *)
(*   unfold instantiate_params in e. *)
(*   case_eq (instantiate_params_subst (List.rev params) pars [] T) ; *)
(*     try solve [ intro bot ; rewrite bot in e ; discriminate e ]. *)
(*   intros [s' t'] e'. rewrite e' in e. inversion e. subst. clear e. *)
(*   eapply instantiate_params_subst_length in e'. *)
(*   rewrite List.rev_length in e'. assumption. *)
(* Qed. *)

Lemma shift_subst_instance_constr :
  forall u t k,
    (subst_instance_constr u t).[⇑^k ↑] = subst_instance_constr u t.[⇑^k ↑].
Proof.
  intros u t k.
  induction t in k |- * using term_forall_list_ind.
  all: simpl. all: auto.
  all: autorewrite with sigma.
  all: rewrite ?map_map_compose ?compose_on_snd ?compose_map_def ?map_lenght.
  all: try solve [ f_equal ; eauto ; solve_all ; eauto ].
  - unfold Upn, shift, subst_compose, subst_consn.
    destruct (Nat.ltb_spec0 n k).
    + rewrite nth_error_idsn_Some. 1: assumption.
      reflexivity.
    + rewrite nth_error_idsn_None. 1: lia.
      reflexivity.
  - rewrite IHt1. specialize (IHt2 (S k)). autorewrite with sigma in IHt2.
    rewrite IHt2. reflexivity.
  - rewrite IHt1. specialize (IHt2 (S k)). autorewrite with sigma in IHt2.
    rewrite IHt2. reflexivity.
  - rewrite IHt1 IHt2. specialize (IHt3 (S k)). autorewrite with sigma in IHt3.
    rewrite IHt3. reflexivity.
  - f_equal.
    (* induction X in k |- *. *)
    (* + simpl. reflexivity. *)
    (* + simpl. intuition eauto. *)
    (*   f_equal. *)
    (*   * unfold map_def. unfold compose. rewrite a. *)
    (*     rewrite map_length. autorewrite with sigma. *)
    (*     specialize (b (S (#|l| + k))). autorewrite with sigma in b. *)
    (*     rewrite b. reflexivity. *)
    (*   * rewrite map_length. rewrite map_length in IHX. *)
    admit.
  - admit.
Admitted.

Lemma inst_subst_instance_constr :
  forall u t σ,
    (subst_instance_constr u t).[(subst_instance_constr u ∘ σ)%prog] =
    subst_instance_constr u t.[σ].
Proof.
  intros u t σ.
  induction t in σ |- * using term_forall_list_ind.
  all: simpl. all: auto.
  all: autorewrite with sigma.
  all: rewrite ?map_map_compose ?compose_on_snd ?compose_map_def ?map_lenght.
  all: try solve [ f_equal ; eauto ; solve_all ; eauto ].
  - rewrite IHt1. f_equal. rewrite <- IHt2.
    eapply inst_ext. intro i.
    unfold compose, Up, subst_compose, subst_cons.
    destruct i.
    + reflexivity.
    + pose proof (shift_subst_instance_constr u (σ i) 0) as e.
      autorewrite with sigma in e. rewrite e. reflexivity.
  -
Admitted.

Lemma build_branches_type_inst :
  forall ind mdecl idecl args u p brs σ,
    closed_ctx (subst_instance_context u (ind_params mdecl)) ->
    map_option_out (build_branches_type ind mdecl idecl args u p) = Some brs ->
    map_option_out (
        build_branches_type
          ind
          mdecl
          (map_one_inductive_body
             (context_assumptions (ind_params mdecl))
             #|arities_context (ind_bodies mdecl)|
             (fun i : nat => inst (⇑^i σ))
             (inductive_ind ind)
             idecl
          )
          (map (inst σ) args)
          u
          p.[σ]
    ) = Some (map (on_snd (inst σ)) brs).
Proof.
  intros ind mdecl idecl args u p brs σ hcl.
  unfold build_branches_type.
  destruct idecl as [ina ity ike ict ipr]. simpl.
  unfold mapi.
  generalize 0 at 3 6.
  intros n h.
  induction ict in brs, n, h, σ |- *.
  - cbn in *. inversion h. reflexivity.
  - cbn. cbn in h.
    lazymatch type of h with
    | match ?t with _ => _ end = _ =>
      case_eq (t) ;
        try (intro bot ; rewrite bot in h ; discriminate h)
    end.
    intros [m t] e'. rewrite e' in h.
    destruct a as [[na ta] ar].
    lazymatch type of e' with
    | match ?expr with _ => _ end = _ =>
      case_eq (expr) ;
        try (intro bot ; rewrite bot in e' ; discriminate e')
    end.
    intros ty ety. rewrite ety in e'.
    eapply instantiate_params_inst with (σ := σ) in ety as ety'. 2: assumption.
    autorewrite with sigma. simpl.
    autorewrite with sigma in ety'.
    rewrite <- inst_subst_instance_constr.
    autorewrite with sigma.
    match goal with
    | |- context [ instantiate_params _ _ ?t.[?σ] ] =>
      match type of ety' with
      | instantiate_params _ _ ?t'.[?σ'] = _ =>
        replace t.[σ] with t'.[σ'] ; revgoals
      end
    end.
    { eapply inst_ext. intro i.
      unfold Upn, compose, subst_compose, subst_consn.
      rewrite arities_context_length.
      case_eq (nth_error (inds (inductive_mind ind) u (ind_bodies mdecl)) i).
      - intros t' e.
        rewrite nth_error_idsn_Some.
        { eapply nth_error_Some_length in e.
          rewrite inds_length in e. assumption.
        }
        simpl. rewrite e.
        give_up.
      - intro neq. simpl. rewrite inds_length idsn_length.
        rewrite nth_error_idsn_None.
        { eapply nth_error_None in neq. rewrite inds_length in neq. lia. }
        give_up.
    }
    rewrite ety'.
    case_eq (decompose_prod_assum [] ty). intros sign ccl edty.
    rewrite edty in e'.
    (* TODO inst edty *)
    case_eq (chop (ind_npars mdecl) (snd (decompose_app ccl))).
    intros paramrels args' ech. rewrite ech in e'.
    (* TODO inst ech *)
    inversion e'. subst. clear e'.
    lazymatch type of h with
    | match ?t with _ => _ end = _ =>
      case_eq (t) ;
        try (intro bot ; rewrite bot in h ; discriminate h)
    end.
    intros tl etl. rewrite etl in h.
    (* TODO inst etl *)
    inversion h. subst. clear h.
    (* edestruct IHict as [brtys' [eq' he]]. *)
    (* + eauto. *)
    (* + eexists. rewrite eq'. split. *)
    (*   * reflexivity. *)
    (*   * constructor ; auto. *)
    (*     simpl. split ; auto. *)
    (*     eapply eq_term_upto_univ_it_mkProd_or_LetIn ; auto. *)
    (*     eapply eq_term_upto_univ_mkApps. *)
    (*     -- eapply eq_term_upto_univ_lift. assumption. *)
    (*     -- apply All2_same. intro. apply eq_term_upto_univ_refl ; auto. *)
Admitted.

Lemma types_of_case_inst :
  forall Σ ind mdecl idecl npar args u p pty indctx pctx ps btys σ,
    wf Σ ->
    declared_inductive Σ mdecl ind idecl ->
    types_of_case ind mdecl idecl (firstn npar args) u p pty =
    Some (indctx, pctx, ps, btys) ->
    types_of_case ind mdecl idecl (firstn npar (map (inst σ) args)) u p.[σ] pty.[σ] =
    Some (inst_context σ indctx, inst_context σ pctx, ps, map (on_snd (inst σ)) btys).
Proof.
  intros Σ ind mdecl idecl npar args u p pty indctx pctx ps btys σ hΣ hdecl h.
  unfold types_of_case in *.
  case_eq (instantiate_params (subst_instance_context u (ind_params mdecl)) (firstn npar args) (subst_instance_constr u (ind_type idecl))) ;
    try solve [ intro bot ; rewrite bot in h ; discriminate h ].
  intros ity eity. rewrite eity in h.
  pose proof (on_declared_inductive hΣ hdecl) as [onmind onind].
  apply onParams in onmind as Hparams.
  assert (closedparams : closed_ctx (subst_instance_context u (ind_params mdecl))).
  { rewrite closedn_subst_instance_context.
    eapply PCUICWeakening.closed_wf_local. all: eauto. eauto. }
  epose proof (inst_declared_inductive _ ind mdecl idecl σ hΣ) as hi.
  forward hi by assumption. rewrite <- hi.
  eapply instantiate_params_inst with (σ := σ) in eity ; auto.
  rewrite -> ind_type_map.
  rewrite firstn_map.
  autorewrite with sigma.
(*   rewrite eity. *)
(*   case_eq (destArity [] ity) ; *)
(*     try solve [ intro bot ; rewrite bot in h ; discriminate h ]. *)
(*   intros [args0 ?] ear. rewrite ear in h. *)
(*   eapply inst_destArity with (σ := σ) in ear as ear'. *)
(*   simpl in ear'. autorewrite with sigma in ear'. *)
(*   rewrite ear'. *)
(*   case_eq (destArity [] pty) ; *)
(*     try solve [ intro bot ; rewrite bot in h ; discriminate h ]. *)
(*   intros [args' s'] epty. rewrite epty in h. *)
(*   eapply inst_destArity with (σ := σ) in epty as epty'. *)
(*   simpl in epty'. autorewrite with sigma in epty'. *)
(*   rewrite epty'. *)
(*   case_eq (map_option_out (build_branches_type ind mdecl idecl (firstn npar args) u p)) ; *)
(*     try solve [ intro bot ; rewrite bot in h ; discriminate h ]. *)
(*   intros brtys ebrtys. rewrite ebrtys in h. *)
(*   inversion h. subst. clear h. *)
(*   eapply build_branches_type_inst with (σ := σ) in ebrtys as ebrtys'. *)
(*   2: assumption. *)
(*   rewrite ebrtys'. reflexivity. *)
(* Qed. *)
Admitted.

Lemma type_inst :
  forall Σ Γ Δ σ t A,
    wf Σ.1 ->
    wf_local Σ Γ ->
    wf_local Σ Δ ->
    Σ ;;; Δ ⊢ σ : Γ ->
    Σ ;;; Γ |- t : A ->
    Σ ;;; Δ |- t.[σ] : A.[σ].
Proof.
  intros Σ Γ Δ σ t A hΣ hΓ hΔ hσ h.
  revert Σ hΣ Γ hΓ t A h Δ σ hΔ hσ.
  apply (typing_ind_env (fun Σ Γ t T => forall Δ σ,
    wf_local Σ Δ ->
    Σ ;;; Δ ⊢ σ : Γ ->
    Σ ;;; Δ |- t.[σ] : T.[σ]
  )).
  - intros Σ wfΣ Γ wfΓ n decl e X Δ σ hΔ hσ. simpl.
    eapply hσ. assumption.
  - intros Σ wfΣ Γ wfΓ l X H0 Δ σ hΔ hσ. simpl.
    econstructor. all: assumption.
  - intros Σ wfΣ Γ wfΓ na A B s1 s2 X hA ihA hB ihB Δ σ hΔ hσ.
    autorewrite with sigma. simpl.
    econstructor.
    + eapply ihA ; auto.
    + eapply ihB.
      * econstructor ; auto.
        eexists. eapply ihA ; auto.
      * eapply well_subst_Up. 2: assumption.
        econstructor ; auto.
        eexists. eapply ihA. all: auto.
  - intros Σ wfΣ Γ wfΓ na A t s1 bty X hA ihA ht iht Δ σ hΔ hσ.
    autorewrite with sigma.
    econstructor.
    + eapply ihA ; auto.
    + eapply iht.
      * econstructor ; auto.
        eexists. eapply ihA ; auto.
      * eapply well_subst_Up. 2: assumption.
        constructor. 1: assumption.
        eexists. eapply ihA. all: auto.
  - intros Σ wfΣ Γ wfΓ na b B t s1 A X hB ihB hb ihb ht iht Δ σ hΔ hσ.
    autorewrite with sigma.
    econstructor.
    + eapply ihB. all: auto.
    + eapply ihb. all: auto.
    + eapply iht.
      * econstructor. all: auto.
        -- eexists. eapply ihB. all: auto.
        -- simpl. eapply ihb. all: auto.
      * eapply well_subst_Up'. assumption.
  - intros Σ wfΣ Γ wfΓ t na A B u X ht iht hu ihu Δ σ hΔ hσ.
    autorewrite with sigma.
    (* NEED Relation between inst and subst *)
    admit.
  - intros Σ wfΣ Γ wfΓ cst u decl X X0 isdecl hconst Δ σ hΔ hσ.
    (* autorewrite with sigma. *) simpl.
    (* NEED Commutation *)
    admit.
  - intros Σ wfΣ Γ wfΓ ind u mdecl idecl isdecl X X0 hconst Δ σ hΔ hσ.
    (* autorewrite with sigma. *) simpl.
    (* NEED Commutation *)
    admit.
  - intros Σ wfΣ Γ wfΓ ind i u mdecl idecl cdecl isdecl X X0 hconst Δ σ hΔ hσ.
    (* autorewrite with sigma. *) simpl.
    (* NEED Commutation *)
    admit.
  - intros Σ wfΣ Γ wfΓ ind u npar p c brs args mdecl idecl isdecl X X0 e pars
           pty hp indctx pctx ps btys htoc hca hel ihp hc ihc hbrs Δ σ hΔ hσ.
    autorewrite with sigma. simpl.
    rewrite map_app. simpl.
    rewrite map_skipn.
    eapply types_of_case_inst with (σ := σ) in htoc. all: try eassumption.
    eapply type_Case.
    + eassumption.
    + assumption.
    + eapply ihp. all: auto.
    + eassumption.
    + admit.
    + assumption.
    + specialize (ihc _ _ hΔ hσ). autorewrite with sigma in ihc.
      eapply ihc.
    + admit.
  - intros Σ wfΣ Γ wfΓ p c u mdecl idecl pdecl isdecl args X X0 hc ihc e ty
           Δ σ hΔ hσ.
    autorewrite with sigma. simpl.
    admit.
  - intros Σ wfΣ Γ wfΓ mfix n decl types H0 H1 X ihmfix Δ σ hΔ hσ.
    autorewrite with sigma.
    admit.
  - intros Σ wfΣ Γ wfΓ mfix n decl types H0 X X0 ihmfix Δ σ hΔ hσ.
    autorewrite with sigma.
    admit.
  - intros Σ wfΣ Γ wfΓ t A B X ht iht hwf hcu Δ σ hΔ hσ.
    eapply type_Cumul.
    + eapply iht. all: auto.
    + destruct hwf as [[[ctx [s [? ?]]] ?] | [s [? ihB]]].
      * left. eexists _,_. split.
        -- admit.
        -- admit.
      * right. eexists. eapply ihB. all: auto.
    + admit.
Admitted.

End Sigma.
