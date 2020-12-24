(* Distributed under the terms of the MIT license. *)
From Coq Require Import Morphisms.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICInduction
  PCUICLiftSubst PCUICUnivSubst
  PCUICTyping PCUICClosed PCUICEquality PCUICWeakeningEnv
  PCUICSigmaCalculus PCUICClosed.

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
  - simpl. f_equal. induction X.
    + reflexivity.
    + simpl. f_equal ; easy.
  - simpl. rewrite IHt. f_equal.
    * rewrite /rename_predicate !map_predicate_map_predicate.
      solve_all.
    * induction X0.
      + reflexivity.
      + simpl. f_equal. 2: easy.
        destruct x. unfold map_branch. simpl in *.
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

Definition rename_decl f d := map_decl (rename f) d.

Lemma rename_context_length :
  forall σ Γ,
    #|rename_context σ Γ| = #|Γ|.
Proof.
  intros σ Γ. unfold rename_context.
  apply fold_context_length.
Qed.
Hint Rewrite rename_context_length : sigma wf.

Lemma rename_context_snoc0 :
  forall f Γ d,
    rename_context f (d :: Γ) =
    rename_context f Γ ,, rename_decl (shiftn #|Γ| f) d.
Proof.
  intros f Γ d.
  unfold rename_context. now rewrite fold_context_snoc0. 
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
  unfold rename_context. apply fold_context_alt.
Qed.


Lemma lift_renaming_0 k : ren (lift_renaming k 0) = ren (Nat.add k).
Proof. reflexivity. Qed.

Lemma ren_lift_renaming n k : ren (lift_renaming n k) =1 (⇑^k ↑^n).
Proof.
  unfold subst_compose. intros i.
  simpl. rewrite -{1}(Nat.add_0_r k). unfold ren. rewrite - (shiftn_lift_renaming n k 0).
  pose proof (ren_shiftn k (lift_renaming n 0) i).
  change ((ren (shiftn k (lift_renaming n 0)) i) = ((⇑^k (↑^n)) i)).
  rewrite -H. sigma. rewrite lift_renaming_0. reflexivity.
Qed.

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
  rewrite !lift_rename.
  autorewrite with sigma. rewrite -ren_shiftn up_Upn.
  rewrite shiftn_consn_idsn. reflexivity.
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
      rewrite (All2_length ectx). red.
      intuition auto; simpl; solve_all.
    * induction X0 in a, brs' |- *.
      + inversion a. constructor.
      + inversion a. subst. simpl.
        destruct X1 as [a0 e0]. rewrite (All2_length a0).
        constructor.
        ** unfold map_branch; simpl; intuition eauto.
        ** eauto.
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

Lemma inst_closed σ k t : closedn k t -> t.[⇑^k σ] = t.
Proof.
  intros Hs.
  induction t in σ, k, Hs |- * using term_forall_list_ind; intros; sigma;
    simpl in *;
    rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, ?map_branch_map_branch,
      ?map_length, ?Nat.add_assoc in *;
      unfold test_def, map_branch, test_branch, test_predicate in *; simpl in *; eauto with all;
    simpl closed in *; repeat (rtoProp; f_equal; solve_all); try change_Sk.
    
  - revert Hs.
    unfold Upn.
    elim (Nat.ltb_spec n k) => //; intros; simpl in *.
    destruct (subst_consn_lt (l := idsn k) (i := n)) as [t [Heq Heq']].
    + now rewrite idsn_length //.
    + now rewrite idsn_lt in Heq.
  - specialize (IHt2 σ (S k) H0). rewrite -{2}IHt2. now sigma.
  - specialize (IHt2 σ (S k) H0). rewrite -{2}IHt2. now sigma.
  - specialize (IHt3 σ (S k) H0). rewrite -{2}IHt3. now sigma.
  - specialize (e σ (#|pcontext p| + k)). rewrite -{2}e; now sigma.
  - specialize (a σ (#|bcontext x| + k)). destruct x; simpl in *. f_equal.
    now rewrite -{2}a; sigma.
  - rtoProp. specialize (b0 σ (#|m| + k) H0). eapply map_def_id_spec; auto.
    revert b0. now sigma.
  - rtoProp. specialize (b0 σ (#|m| + k) H0). eapply map_def_id_spec; auto.
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

Lemma rename_closed_decl k f d : closed_decl k d -> map_decl (rename (shiftn k f)) d = d.
Proof.
  rewrite /closed_decl /map_decl.  
  destruct d as [? [] ?] => /=.
  - move/andP=> [] clt clty.
    rewrite !rename_closedn //.
  - move=> clt. rewrite !rename_closedn //.
Qed.

Lemma rename_closedn_ctx f n Γ : 
  closedn_ctx n Γ -> 
  rename_context (shiftn n f) Γ = Γ.
Proof.
  unfold closedn_ctx, rename_context.
  apply alli_fold_context.
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
  now eapply subject_closed in decl'.
Qed.

Lemma rename_shiftn :
  forall f k t,
    rename (shiftn k f) (lift0 k t) = lift0 k (rename f t).
Proof.
  intros f k t.
  autorewrite with sigma.
  eapply inst_ext. intro i.
  unfold ren, lift_renaming, shiftn, subst_compose. simpl.
  destruct (Nat.ltb_spec (k + i) k); try lia.
  unfold shiftk. lia_f_equal.
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

Lemma rename_extended_subst f Γ k : 
  map (rename (shiftn (context_assumptions Γ) f)) (extended_subst Γ k) =
  extended_subst (rename_context (shiftn (context_assumptions Γ) f) Γ) k.
Proof.
  revert f k.
  induction Γ as [|[na [] ?] Γ]; intros f k; cbn -[rename_context]; auto;
    rewrite ?rename_context_snoc /=; len; rewrite ?IHΓ.
  - f_equal. admit.
  - 
Admitted.

Definition rename_branch f br := 
  map_branch (rename (shiftn #|br.(bcontext)| f)) br.
  
  (* TODO MOVE *)
Lemma rename_iota_red :
  forall f pars args bctx br,
    rename f (iota_red pars args bctx br) =
    iota_red pars (map (rename f) args)
       (rename_context f bctx)
       (rename_branch f br).
Proof.
  intros f pars args bctx br.
  unfold iota_red.
  rewrite rename_subst0 map_skipn. f_equal.
  rewrite /expand_lets /expand_lets_k.
  rewrite rename_subst0. len.
Admitted.
  
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
  map2 set_binder_name bctx (fold_context f Γ) = 
  fold_context f (map2 set_binder_name bctx Γ).
Proof.
  intros hl.
  rewrite !fold_context_alt mapi_map2 -{1}(map_id bctx).
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
  autorewrite with sigma.
  rewrite !ren_lift_renaming.
  eapply inst_ext.
  rewrite - !ren_shiftn up_Upn. rewrite Nat.add_comm. sigma.
  rewrite !Upn_compose.
  apply Upn_ext. now rewrite shiftn_consn_idsn.
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
  apply fold_context_ext => i t.
  now rewrite Hfg.
Qed.

Lemma rename_context_subst_instance_context f u Γ : 
  rename_context f (subst_instance_context u Γ) = 
  subst_instance_context u (rename_context f Γ).
Proof. unfold rename_context.
  rewrite fold_context_map //.
  intros i x.
  now rewrite rename_subst_instance_constr.
Qed.

Lemma rename_context_subst_k f s k Γ : 
  rename_context (shiftn k f) (subst_context s k Γ) =
  subst_context (map (rename f) s) k (rename_context (shiftn (k + #|s|) f) Γ).
Proof.
  rewrite /rename_context /subst_context.
  rewrite !fold_context_compose.
  apply fold_context_ext => i t.
  rewrite shiftn_add.
  now rewrite rename_subst !shiftn_add Nat.add_assoc.
Qed.
 
Lemma rename_cstr_args mdecl f cdecl : 
  cstr_args (rename_constructor_body mdecl f cdecl) =
  rename_context (shiftn (#|mdecl.(ind_params)| + #|ind_bodies mdecl|) f) (cstr_args cdecl).
Proof. 
  simpl. unfold rename_context.
  apply fold_context_ext => i t.
  now rewrite shiftn_add Nat.add_assoc.
Qed.

Lemma rename_case_branch_context_gen ind mdecl f p bctx cdecl :
  closed_ctx (ind_params mdecl) ->
  #|bctx| = #|cstr_args cdecl| ->
  #|pparams p| = context_assumptions (ind_params mdecl) ->
  rename_context f (case_branch_context ind mdecl p bctx cdecl) = 
  case_branch_context ind mdecl (rename_predicate rename f p) bctx 
    (rename_constructor_body mdecl f cdecl).
Proof.
  intros clpars. unfold case_branch_context, case_branch_context_gen.
  rewrite rename_cstr_args.
  cbn -[fold_context].
  intros hlen hlen'.
  rewrite map2_set_binder_name_fold //.
  change (fold_context
  (fun i : nat => rename (shiftn i (shiftn (ind_npars mdecl + #|ind_bodies mdecl|) f)))) with
    (rename_context (shiftn (ind_npars mdecl + #|ind_bodies mdecl|) f)).
  rewrite rename_context_subst. f_equal.
  unfold id.
  rewrite /expand_lets_ctx /expand_lets_k_ctx.
  simpl. len.
  rewrite rename_context_subst; len.
  rewrite hlen'.
  rewrite -{1}(context_assumptions_subst_instance_context (puinst p)).
  rewrite rename_closed_extended_subst.
  { now rewrite closedn_subst_instance_context. }
  f_equal.
  rewrite shiftn_add Nat.add_comm.
  rewrite rename_context_lift. f_equal.
  rewrite -rename_context_subst_instance_context.
  rewrite rename_context_subst_k rename_inds. now len.
Qed.

Definition map_pair {A B C D} (f : A -> B) (g : C -> D) (p : A × C) : B × D :=
  (f p.1, g p.2).

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

(* 
Lemma rename_context_expand_lets_ctx k f Γ Δ :
  k = context_assumptions Γ ->
  rename_context (shiftn k f) (expand_lets_ctx Γ Δ) =
  expand_lets_ctx (

Lemma rename_context_expand_lets_ctx k f Γ Δ :
  k = context_assumptions Γ ->
  rename_context (shiftn k f) (expand_lets_ctx Γ Δ) =
  expand_lets_ctx () *)

Lemma rename_case_predicate_context {Σ} {wfΣ : wf Σ} {ind mdecl idecl f p} :
  declared_inductive Σ ind mdecl idecl ->
  wf_predicate mdecl idecl p ->
  rename_context f (case_predicate_context ind mdecl idecl p) =
  case_predicate_context ind mdecl idecl (rename_predicate rename f p).
Proof.
  intros decli wfp.
  unfold case_predicate_context. simpl.
  unfold id. unfold case_predicate_context_gen.
  rewrite /rename_context.
  rewrite -map2_set_binder_name_fold //.
  - len. len. 
    now rewrite -(wf_predicate_length_pcontext wfp).
  - f_equal. rewrite fold_context_snoc0 /= /snoc.
    f_equal.
    * rewrite /map_decl /=. f_equal.
      len. rewrite rename_mkApps /=. f_equal.
      rewrite !map_app !map_map_compose. f_equal.
      + solve_all.
        eapply All_refl => x.
        apply rename_shiftn.
      + now rewrite rename_to_extended_list.
    * rewrite -/(rename_context f _).
      rewrite rename_context_subst rename_context_subst_instance_context.
      f_equal. f_equal.
      rewrite rename_closedn_ctx //.
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
  destruct cdecl; cbn -[fold_context] in *; f_equal.
  + move: clctx. unfold closed_ctx.
    apply alli_fold_context => i d cldecl.
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
  wf_predicate mdecl idecl (rename_predicate rename f p).
Proof.
  intros []. split.
  - now len.
  - assumption.
Qed.

Lemma rename_wf_branch cdecl f br :
  wf_branch cdecl br ->
  wf_branch cdecl (rename_branch f br).
Proof.
  unfold wf_branch, wf_branch_gen. now simpl.
Qed.

Lemma rename_wf_branches cdecl f brs :
  wf_branches cdecl brs ->
  wf_branches cdecl (map (rename_branch f) brs).
Proof.
  unfold wf_branches, wf_branches_gen.
  intros h. solve_all. eapply Forall2_map_right.
  solve_all.
Qed.

Lemma rename_compose f f' x : rename f (rename f' x) = rename (f ∘ f') x.
Proof. now rewrite (rename_compose _ _ _). Qed.

Lemma rename_case_branch_type {Σ} {wfΣ : wf Σ} f (ci : case_info) mdecl idecl p br i cdecl : 
  declared_inductive Σ ci mdecl idecl ->
  wf_predicate mdecl idecl p ->
  wf_branch cdecl br ->
  closed_constructor_body mdecl cdecl ->

  let ptm := 
    it_mkLambda_or_LetIn (case_predicate_context ci mdecl idecl p) (preturn p) 
  in
  let p' := rename_predicate rename f p in
  let ptm' :=
    it_mkLambda_or_LetIn 
      (case_predicate_context ci mdecl idecl p')
      (preturn p') in
  case_branch_type ci mdecl idecl
     (rename_predicate rename f p) 
     (map_branch (rename (shiftn #|bcontext br| f)) br) 
     ptm' i cdecl =
  map_pair (rename_context f) (rename (shiftn #|bcontext br| f)) 
  (case_branch_type ci mdecl idecl p br ptm i cdecl).
Proof.
  intros decli wfp wfb clb ptm p' ptm'.
  rewrite /case_branch_type /case_branch_type_gen /map_pair /=.
  rewrite rename_case_branch_context_gen //.
  { eapply (declared_inductive_closed_params decli). }
  { now apply wf_branch_length. }
  { rewrite -(declared_minductive_ind_npars decli).
    apply (wf_predicate_length_pars wfp). }
  f_equal.
  - rewrite rename_closed_constructor_body //.
  - rewrite rename_mkApps map_app map_map_compose.
    rewrite (wf_branch_length wfb).
    f_equal.
    * rewrite /ptm' /ptm !lift_it_mkLambda_or_LetIn !rename_it_mkLambda_or_LetIn.
      rewrite !lift_rename. f_equal.
      ++ rewrite /p'.
         rewrite -rename_case_predicate_context //.
         epose proof (rename_context_lift f #|cstr_args cdecl| 0).
         rewrite Nat.add_0_r in H.
         rewrite H. now rewrite shiftn0.
      ++ rewrite /p'. rewrite Nat.add_0_r. simpl.
        rewrite case_predicate_context_length //.
        { now apply rename_wf_predicate. }
        rewrite !case_predicate_context_length // Nat.add_0_r; len.
        rewrite case_predicate_context_length //.
        rewrite shiftn_add. rewrite - !lift_rename.
        now rewrite Nat.add_comm rename_shiftnk.
    * rewrite /= rename_mkApps /=. f_equal.
      ++ rewrite map_map_compose /id. admit.
      ++ unfold id. f_equal. f_equal.
         rewrite map_app map_map_compose.
         rewrite map_map_compose.
         setoid_rewrite rename_shiftn. f_equal.
         now rewrite rename_to_extended_list.
Admitted.

Lemma rename_predicate_set_pparams f p params :
  rename_predicate rename f (set_pparams p params) = 
  set_pparams (rename_predicate rename f p) (map (rename f) params).
Proof. reflexivity. Qed.

Lemma rename_predicate_set_preturn f p pret :
  rename_predicate rename f (set_preturn p pret) = 
  set_preturn (rename_predicate rename f p) (rename (shiftn #|pcontext p| f) pret).
Proof. reflexivity. Qed.

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
    destruct (nth_error Γ i) eqn:hnth; noconf H.
    unfold urenaming in hf.
    specialize hf with (1 := hnth).
    destruct hf as [decl' [e' [hr hbo]]].
    specialize hbo with (1 := H).
    destruct hbo as [body' [hbo' hr']].
    rewrite hr'. constructor.
    rewrite e'. simpl. rewrite hbo'. reflexivity.
  - simpl. rewrite rename_mkApps. simpl.
    rewrite rename_iota_red.
    subst brctx.
    rewrite rename_case_branch_context_gen.
    * eapply declared_inductive_closed_params; eauto with pcuic.
      eapply isdecl.
    * now rewrite (wf_branch_length H1).
    * rewrite -(declared_minductive_ind_npars isdecl).
      now eapply wf_predicate_length_pars.
    * change (bcontext br) with (bcontext (rename_branch f br)).
      epose proof (declared_constructor_closed _ isdecl).
      rewrite rename_closed_constructor_body //.
      eapply red_iota; eauto.
      + rewrite nth_error_map H /= //.
      + now apply rename_wf_predicate.
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
    econstructor. rewrite nth_error_map. rewrite H. reflexivity.
  - simpl.
    rewrite rename_predicate_set_pparams. econstructor.
    simpl. eapply OnOne2_map. solve_all. red; eauto.
  - simpl. rewrite rename_predicate_set_preturn.
    eapply case_red_return; eauto.
    + now apply rename_wf_predicate.
    + simpl. apply IHh.
      erewrite <-(case_predicate_context_length (p:=rename_predicate rename f p)); eauto.
      2:{ now eapply rename_wf_predicate. }
      rewrite - !rename_case_predicate_context; eauto.
      len. now eapply urenaming_context.
  - simpl.
    eapply case_red_brs; eauto.
    + now eapply rename_wf_predicate.
    + now eapply rename_wf_branches.
    + replace (ind_ctors idecl) with (map (rename_constructor_body mdecl f) (ind_ctors idecl)).
      2:{ pose proof (declared_inductive_closed_constructors isdecl).
          solve_all. now rewrite rename_closed_constructor_body. }
      eapply OnOne2All_map_all. red in H0.
      eapply Forall2_All2 in H0.
      eapply OnOne2All_All2_mix_left in X; eauto. solve_all.
      red; simpl. split; auto. rewrite -b0.
      rewrite - rename_case_branch_context_gen; eauto.
      * eapply (declared_inductive_closed_params isdecl).
      * now apply wf_branch_length.
      * rewrite -(declared_minductive_ind_npars isdecl).
        now apply (wf_predicate_length_pars H).
      * eapply b1.
        erewrite <-(case_branch_context_length b).
        now eapply urenaming_context.
  - simpl. constructor.
    eapply OnOne2_map. solve_all. red. eauto.
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
      * eapply p2. rewrite rename_fix_context.
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
      * eapply p2. rewrite rename_fix_context.
        rewrite <- fix_context_length.
        eapply urenaming_context.
        assumption.
      * simpl. easy.
    + intros L x l l' h ih.
      simpl. constructor. eapply ih.
Qed.

Lemma cumul_rename :
  forall Σ Γ Δ f A B,
    wf Σ.1 ->
    urenaming Δ Γ f ->
    Σ ;;; Γ |- A <= B ->
    Σ ;;; Δ |- rename f A <= rename f B.
Proof.
  intros Σ Γ Δ f A B hΣ hf h.
  induction h.
  - eapply cumul_refl. eapply eq_term_upto_univ_rename. assumption.
  - eapply cumul_red_l.
    + eapply red1_rename. all: try eassumption.
    + assumption.
  - eapply cumul_red_r.
    + eassumption.
    + eapply red1_rename. all: try eassumption.
Qed.

Lemma fix_guard_rename Σ Γ Δ mfix f :
  renaming Σ Γ Δ f ->
  let mfix' := map (map_def (rename f) (rename (shiftn (List.length mfix) f))) mfix in
  fix_guard Σ Δ mfix ->
  fix_guard Σ Γ mfix'.
Admitted.

Lemma cofix_guard_rename Σ Γ Δ mfix f :
  renaming Σ Γ Δ f ->
  let mfix' := map (map_def (rename f) (rename (shiftn (List.length mfix) f))) mfix in
  cofix_guard Σ Δ mfix ->
  cofix_guard Σ Γ mfix'.
Admitted.


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
  preturn (rename_predicate rename f p).
Proof. reflexivity. Qed.

Tactic Notation "relativize" open_constr(c) := 
  let ty := type of c in  
  let x := fresh in
  evar (x : ty); replace c with x; subst x.
  
Lemma rename_wf_local_rel_set_binder_name Σ Γ Γ' pctx :
  #|Γ'| = #|pctx| -> 
  wf_local_rel Σ Γ Γ' ->
  wf_local_rel Σ Γ (map2 set_binder_name pctx Γ').
Proof.
  intros wfp wf.
  induction wf in pctx, wfp |- *; simpl in *;destruct pctx => //; noconf wfp.
  - constructor.
  - simpl. constructor.
    * now apply IHwf.
    * destruct t0 as [s Hs]. exists s. simpl.
      admit.
  - simpl. constructor.
    * now apply IHwf.
    * red. destruct t0 as [s Hs]; exists s; simpl.
Abort. (* This requires alpha-renaming.. *)
(* 
Lemma rename_wf_local_rel_set_binder_name Σ Γ Δ Δ' pctx :
  #|Δ| = #|pctx| -> #|Δ'| = #|pctx| ->
  (wf_local_rel Σ Γ Δ -> wf_local_rel Σ Γ Δ') ->
  wf_local_rel Σ Γ (map2 set_binder_name pctx Δ) ->
  wf_local_rel Σ Γ (map2 set_binder_name pctx Δ').
Proof. *)

(* 
Lemma rename_wf_local_rel_set_binder_name Σ Γ Δ Δ' pctx :
  #|Δ| = #|pctx| -> #|Δ'| = #|pctx| ->
  (* (wf_local_rel Σ Γ Δ -> wf_local_rel Σ Γ Δ') -> *)
  wf_local_rel Σ Γ (map2 set_binder_name pctx Δ) ->
  wf_local_rel Σ Γ (map2 set_binder_name pctx Δ').
Proof.
  intros wfp wfp' wf.
  induction Δ in pctx, Δ', wfp, wfp', wf |- *; simpl in *;destruct pctx => //; noconf wfp;
  depelim wf.
  - destruct Δ'; noconf wfp'. simpl.
    destruct a as [? [] ?]; noconf H1.
    red in l.
    destruct l as [s Hs]. simpl in Hs.
    constructor. *)




 (* This requires alpha-renaming.. *)
(* 
Lemma wf_local_rel_map2_impl Σ Γ (pctx : list aname) Δ :
  #|pctx| = #|Δ| ->
  wf_local_rel Σ Γ (map2 set_binder_name pctx Δ) <~>
  All_local_env (lift_typing (fun Σ Γ' t T => 
    Σ ;;; Γ ,,, map2 set_binder_name Γ' |- t : T) Σ) Δ.
Proof.
  intros.
  split.
  - intros.
    induction pctx in Δ, H, X |- *; destruct Δ => //; noconf H.
    specialize (IHpctx _ H).
    depelim X; specialize (IHpctx X).
    * clear X. red in l.
      destruct c as [? [] ?]; noconf H0.
      constructor; auto.
      red. simpl in l.

    eapply All_local_env_impl. eauto. *)

Lemma rename_wf_local_rel_case_pred Σ Δ Γ f ci mdecl idecl p : 
  renaming Σ Δ Γ f ->
  wf_predicate mdecl idecl (rename_predicate rename f p) ->
  ctx_inst typing Σ Δ p.(pparams) (subst_instance_context p.(puinst) mdecl.(ind_params)) ->
  wf_local_rel Σ Γ (case_predicate_context ci mdecl idecl p) ->
  wf_local_rel Σ Δ (case_predicate_context ci mdecl idecl (rename_predicate rename f p)).
Proof.
  intros Hren wfp ctxi.
  unfold case_predicate_context, case_predicate_context_gen.
  simpl.
  pose proof (wf_predicate_length_pcontext wfp).
  simpl in H.
  destruct (pcontext p) => //. simpl in H.
  simpl.
  intros wf. depelim wf.
  constructor.
  2:{ simpl in l0 |- *. destruct l0 as [s Hs]; exists s.
    admit.    
  }
  simpl in *.

Admitted.
Derive Signature for All_local_env_over.

Lemma All_local_env_over_app_inv Σ Γ Δ a :
  All_local_env_over typing
    (fun (Σ : global_env_ext) (Γ : context) (_ : wf_local Σ Γ) (t T : term) (_ : Σ;;; Γ |- t : T)
    =>
    forall (Δ : PCUICEnvironment.context) (f : nat -> nat),
    renaming Σ Δ Γ f -> Σ;;; Δ |- rename f t : rename f T) Σ (Γ,,, Δ) a ->
 All_local_env
  (lift_typing (fun Σ (Γ' : context) (t T : term) =>
    forall (Δ : PCUICEnvironment.context) (f : nat -> nat),
    renaming Σ Δ (Γ ,,, Γ') f -> Σ;;; Δ |- rename f t : rename f T) Σ) Δ.
Proof.
  induction Δ as [|[na [] ?] Δ]; constructor; auto; depelim X; eauto.
  - red in tu |- *.
    destruct tu as [s Hs]; exists s. intros.
    now eapply t2.
  - simpl. intros. destruct tu as [s Hs]; exists s; intros.
    now apply t0.
Qed.


Lemma apredctx Σ Γ predctx : 
  forall a : wf_local Σ (Γ,,, predctx),
  All_local_env_over typing
  (fun (Σ : global_env_ext) (Γ : context) (_ : wf_local Σ Γ) (t T : term) (_ : Σ;;; Γ |- t : T)
  =>
  forall (Δ : PCUICEnvironment.context) (f : nat -> nat),
  renaming Σ Δ Γ f -> Σ;;; Δ |- rename f t : rename f T) Σ (Γ,,, predctx) a ->
  forall Δ f, 
  renaming Σ Δ Γ f ->
  wf_local Σ (Δ ,,, rename_context f predctx).
Proof.
  intros.
  destruct X0.
  eapply All_local_env_over_app_inv in X.
  induction X.
  - apply a0.
  - depelim a. simpl. destruct l as [s Hs].
    rewrite rename_context_snoc /=. constructor. 
    * now apply IHX.
    * red. destruct t0 as [s' Hs']. exists s'. simpl decl_type.
      apply (Hs' (Δ ,,, rename_context f Γ0) (shiftn #|Γ0| f)).
      split. 
      + apply IHX => //.
      + now eapply urenaming_context.
  - depelim a. destruct l as [s Hs].
    rewrite rename_context_snoc /=. constructor. 
    * now apply IHX.
    * red. destruct t0 as [s' Hs']. exists s'. simpl decl_type.
      apply (Hs' (Δ ,,, rename_context f Γ0) (shiftn #|Γ0| f)).
      split. 
      + apply IHX => //.
      + now eapply urenaming_context.
    * red. destruct t0 as [s' Hs']. simpl. apply t1.
      split.
      + now apply IHX.
      + now eapply urenaming_context. 
Qed.

Lemma All2i_map {A B C D} (R : nat -> C -> D -> Type) (f : A -> C) (g : B -> D) n l l' :
  All2i (fun i x y => R i (f x) (g y)) n l l' -> All2i R n (map f l) (map g l').
Proof. induction 1; simpl; constructor; try congruence. Qed.

Lemma All2i_map_right {B C D} (R : nat -> C -> D -> Type) (g : B -> D) n l l' :
  All2i (fun i x y => R i x (g y)) n l l' -> All2i R n l (map g l').
Proof. induction 1; simpl; constructor; try congruence. Qed.

Lemma case_branch_type_length {ci mdecl idecl p br ptm i cdecl} :
  wf_branch cdecl br ->
  #|(case_branch_type ci mdecl idecl p br ptm i cdecl).1| = #|cstr_args cdecl|.
Proof.
  intros wf; simpl.
  now rewrite case_branch_context_length_args.
Qed.

Lemma typing_rename_prop : env_prop
  (fun Σ Γ t A =>
    forall Δ f,
    renaming Σ Δ Γ f ->
    Σ ;;; Δ |- rename f t : rename f A)
   (fun Σ Γ wfΓ =>
   All_local_env_over typing
   (fun (Σ : global_env_ext) (Γ : context) (_ : wf_local Σ Γ) (t T : term) (_ : Σ;;; Γ |- t : T)
    =>
    forall (Δ : PCUICEnvironment.context) (f : nat -> nat),
    renaming Σ Δ Γ f -> Σ;;; Δ |- rename f t : rename f T) Σ Γ wfΓ).
Proof.
  apply typing_ind_env.
  - intros Σ wfΣ Γ wfΓ HΓ. auto.
  
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
  - intros Σ wfΣ Γ wfΓ t na A B s u X hty ihty ht iht hu ihu Δ f hf.
    simpl. eapply meta_conv.
    + eapply type_App.
      * simpl in ihty. eapply ihty; eassumption.
      * simpl in iht. eapply iht. assumption.
      * eapply ihu. assumption.
    + autorewrite with sigma. rewrite !subst1_inst. sigma.
      eapply inst_ext => i.      
      unfold subst_cons, ren, shiftn, subst_compose. simpl.
      destruct i.
      * simpl. reflexivity.
      * simpl. replace (i - 0) with i by lia.
        reflexivity.
  - intros Σ wfΣ Γ wfΓ cst u decl X X0 isdecl hconst Δ f hf.
    simpl. eapply meta_conv.
    + constructor. all: eauto. apply hf.
    + rewrite rename_subst_instance_constr. f_equal.
      rewrite rename_closed. 2: auto.
      eapply declared_constant_closed_type. all: eauto.
  - intros Σ wfΣ Γ wfΓ ind u mdecl idecl isdecl X X0 hconst Δ σ hf.
    simpl. eapply meta_conv.
    + econstructor. all: eauto. apply hf.
    + rewrite rename_subst_instance_constr. f_equal.
      rewrite rename_closed. 2: auto.
      eapply declared_inductive_closed_type. all: eauto.
  - intros Σ wfΣ Γ wfΓ ind i u mdecl idecl cdecl isdecl X X0 hconst Δ f hf.
    simpl. eapply meta_conv.
    + econstructor. all: eauto. apply hf. 
    + rewrite rename_closed. 2: reflexivity.
      eapply declared_constructor_closed_type. all: eauto.
  - intros Σ wfΣ Γ wfΓ ci p c brs indices ps mdecl idecl isdecl HΣ.
    intros IHΔ ci_npar predctx wfp Hpret IHpret IHpredctx isallowed.
    intros Hc IHc iscof ptm Hbrs Δ f Hf.
    simpl.
    rewrite rename_mkApps.
    rewrite map_app. simpl.
    rewrite /ptm. rewrite rename_it_mkLambda_or_LetIn.
    relativize #|predctx|.
    * erewrite rename_predicate_preturn.
      rewrite /predctx.
      rewrite (rename_case_predicate_context isdecl wfp).
      eapply type_Case; eauto.
      + now eapply rename_wf_predicate.
      + eapply IHpret.
        rewrite -rename_case_predicate_context //.
        split.
        ++ eapply apredctx; eauto.
        ++ rewrite /predctx.
           rewrite -(case_predicate_context_length (ci:=ci) wfp).
          eapply urenaming_context. apply Hf.
      + simpl. unfold id.
        specialize (IHc _ _ Hf).
        now rewrite rename_mkApps map_app in IHc.
      + eapply All2i_map_right, (All2i_impl Hbrs) => i cdecl br.
        set (brctxty := case_branch_type _ _ _ _ _ _ _ _).
        move=> [wfbr [[[Hbr IHbr] Hbty] IHbty]].
        rewrite rename_case_branch_type //.
        { eapply declared_constructor_closed; eauto. }
        rewrite -/brctxty. intros brctx'.
        assert (wf_local Σ (Δ,,, brctx'.1)).
        { rewrite /brctx'. cbn. admit. }
        repeat split.
        ++ now eapply rename_wf_branch.
        ++ eapply IHbr. 
          split => //.
          rewrite /brctx' /brctxty; cbn.
          rewrite (wf_branch_length wfbr).
          erewrite <- case_branch_type_length; eauto.
          eapply urenaming_context, Hf.
        ++ eapply IHbty. split=> //.
          rewrite /brctx'; cbn.
          rewrite (wf_branch_length wfbr).
          erewrite <- case_branch_type_length; eauto.
          eapply urenaming_context, Hf.
    * rewrite /predctx case_predicate_context_length //.
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
      eapply declared_projection_closed_type in isdecl.
      rewrite List.rev_length. rewrite e. assumption.

  - intros Σ wfΣ Γ wfΓ mfix n decl types H1 hdecl X ihmfixt ihmfixb wffix Δ f hf.
    assert (hΔ' : wf_local Σ (Δ ,,, rename_context f (fix_context mfix))).
    { rewrite - rename_fix_context.
      apply PCUICWeakening.All_mfix_wf; auto; try apply hf.
      eapply All_map, (All_impl ihmfixt).
      intros x [s Hs]; exists s; intuition auto.
      simpl. apply (b _ _ hf). }

    simpl. eapply meta_conv.
    + eapply type_Fix.
      * eapply fix_guard_rename; eauto.
      * rewrite nth_error_map. rewrite hdecl. simpl. reflexivity.
      * apply hf.
      * apply All_map, (All_impl ihmfixt).
        intros x [s [Hs IHs]].
        exists s. now apply IHs.
      * apply All_map, (All_impl ihmfixb).
        intros x [Hb IHb].
        destruct x as [na ty bo rarg]. simpl in *.
        rewrite rename_fix_context.
        eapply meta_conv.
        ++ apply (IHb (Δ ,,, rename_context f types) (shiftn #|mfix| f)).
          split; auto. subst types. rewrite -(fix_context_length mfix).
          apply urenaming_context; auto. apply hf.
        ++ autorewrite with sigma. subst types. rewrite fix_context_length.
          now rewrite -ren_shiftn up_Upn shiftn_consn_idsn.
      * admit (* wf_fixpoint renaming *).
    + reflexivity.

  - intros Σ wfΣ Γ wfΓ mfix n decl types guard hdecl X ihmfixt ihmfixb wfcofix Δ f hf.
    assert (hΔ' : wf_local Σ (Δ ,,, rename_context f (fix_context mfix))).
    { rewrite -rename_fix_context.
      apply PCUICWeakening.All_mfix_wf; auto; try apply hf.
      eapply All_map, (All_impl ihmfixt).
      intros x [s Hs]; exists s; intuition auto.
      simpl. apply (b _ _ hf). }
    simpl. eapply meta_conv.
    + eapply type_CoFix; auto.
      * eapply cofix_guard_rename; eauto.
      * rewrite nth_error_map. rewrite hdecl. simpl. reflexivity.
      * apply hf.
      * apply All_map, (All_impl ihmfixt).
        intros x [s [Hs IHs]].
        exists s. now apply IHs.
      * apply All_map, (All_impl ihmfixb).
        intros x [Hb IHb].
        destruct x as [na ty bo rarg]. simpl in *.
        rewrite rename_fix_context.
        eapply meta_conv.
        ++ apply (IHb (Δ ,,, rename_context f types) (shiftn #|mfix| f)).
            split; auto. subst types. rewrite -(fix_context_length mfix).
            apply urenaming_context; auto. apply hf.
        ++ autorewrite with sigma. subst types. rewrite fix_context_length.
           now rewrite -ren_shiftn up_Upn shiftn_consn_idsn.
      * admit.
    + reflexivity.

  - intros Σ wfΣ Γ wfΓ t A B X hwf ht iht htB ihB cum Δ f hf.
    eapply type_Cumul.
    + eapply iht. assumption.
    + eapply ihB. assumption.
    + eapply cumul_rename. all: try eassumption.
      apply hf.
Admitted.

Lemma typing_rename :
  forall Σ Γ Δ f t A,
    wf Σ.1 ->
    renaming Σ Δ Γ f ->
    Σ ;;; Γ |- t : A ->
    Σ ;;; Δ |- rename f t : rename f A.
Proof.
Admitted.
  (* intros Σ Γ Δ f t A hΣ hf h.
  revert Σ hΣ Γ t A h Δ f hf.
  apply typing_rename_prop.
Qed. *)

End Renaming.
