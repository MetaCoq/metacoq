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

Tactic Notation "relativize" open_constr(c) := 
  let ty := type of c in  
  let x := fresh in
  evar (x : ty); replace c with x; subst x.

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
  now sigma.
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

(* Definition urenaming (P : nat -> bool) Γ Δ f :=
  forall i decl,
    P i ->
    nth_error Δ i = Some decl ->
    ∑ decl',
      nth_error Γ (f i) = Some decl' ×
      eq_binder_annot decl.(decl_name) decl'.(decl_name) ×
      rename f (lift0 (S i) decl.(decl_type))
      = lift0 (S (f i)) decl'.(decl_type) ×
      (forall b,
         decl.(decl_body) = Some b ->
         ∑ b',
           decl'.(decl_body) = Some b' ×
           rename f (lift0 (S i) b) = lift0 (S (f i)) b'
      ). *)

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
  - now sigma.
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

Definition shiftnP k p i :=
  if i <? k then true else p (i - k).

Instance shiftnP_ext k : Proper (`=1` ==> `=1`) (shiftnP k).
Proof. intros f g Hfg i. now rewrite /shiftnP Hfg. Qed. 

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

(* Instance urename_proper : CMorphisms.Proper (`=1` ==> Logic.eq ==> Logic.eq ==> `=1` ==> CRelationClasses.iffT) urenaming.
Proof.
  intros P P' Hpp' ? ? -> ? ? -> f g Hfg. *)

Lemma shiftnP0 P : shiftnP 0 P =1 P.
Proof. rewrite /shiftnP. intros i; rewrite Nat.sub_0_r //. Qed.

Lemma shiftnP_add n k P : shiftnP n (shiftnP k P) =1 shiftnP (n + k) P.
Proof. rewrite /shiftnP. intros i; repeat nat_compare_specs => //. lia_f_equal. Qed.

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

Definition rename_branch f br := 
  map_branch (rename (shiftn #|br.(bcontext)| f)) br.
  
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
  rewrite !lift_rename.
  autorewrite with sigma.
  rewrite - !compose_ren ren_lift_renaming.
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

Lemma reln_fold f ctx n acc :
  reln acc n (fold_context f ctx) = 
  reln acc n ctx.
Proof.
  induction ctx as [|[na [b|] ty] ctx] in n, acc |- *; simpl; auto;
    rewrite fold_context_snoc0 /=; apply IHctx.
Qed.

Lemma to_extended_list_rename f ctx :
  to_extended_list (rename_context f ctx) = to_extended_list ctx.
Proof.
  unfold to_extended_list, to_extended_list_k.
  now rewrite (reln_fold _ _ 0).
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

Lemma rename_predicate_set_pparams f p params :
  rename_predicate rename f (set_pparams p params) = 
  set_pparams (rename_predicate rename f p) (map (rename f) params).
Proof. reflexivity. Qed.

Lemma rename_predicate_set_preturn f p pret :
  rename_predicate rename f (set_preturn p pret) = 
  set_preturn (rename_predicate rename f p) (rename (shiftn #|pcontext p| f) pret).
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
  forall f pars args bctx br,
  #|skipn pars args| = context_assumptions bctx ->
  #|bcontext br| = #|bctx| ->
  rename f (iota_red pars args bctx br) =
  iota_red pars (map (rename f) args) (rename_context f bctx) (rename_branch f br).
Proof.
  intros f pars args bctx br hlen hlen'.
  unfold iota_red.
  rewrite rename_subst0 map_skipn. f_equal.
  rewrite /expand_lets /expand_lets_k.
  rewrite rename_subst0. len.
  rewrite shiftn_add -hlen Nat.add_comm rename_shiftnk.
  rewrite hlen. rewrite rename_extended_subst.
  now rewrite hlen'.
Qed.


Lemma rename_case_branch_type {Σ} {wfΣ : wf Σ} f (ci : case_info) mdecl idecl p br i cdecl : 
  declared_inductive Σ ci mdecl idecl ->
  wf_predicate mdecl idecl p ->
  wf_branch cdecl br ->
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
     ptm' i (rename_constructor_body mdecl f cdecl) =
  map_pair (rename_context f) (rename (shiftn #|bcontext br| f)) 
  (case_branch_type ci mdecl idecl p br ptm i cdecl).
Proof.
  intros decli wfp wfb ptm p' ptm'.
  rewrite /case_branch_type /case_branch_type_gen /map_pair /=.
  rewrite rename_case_branch_context_gen //.
  { eapply (declared_inductive_closed_params decli). }
  { now apply wf_branch_length. }
  { rewrite -(declared_minductive_ind_npars decli).
    apply (wf_predicate_length_pars wfp). }
  f_equal.
  rewrite rename_mkApps map_app map_map_compose.
  rewrite (wf_branch_length wfb).
  f_equal.
  * rewrite /ptm' /ptm !lift_it_mkLambda_or_LetIn !rename_it_mkLambda_or_LetIn.
    rewrite !lift_rename. f_equal.
    ++ rewrite /p'.
        rewrite -rename_case_predicate_context //.
        epose proof (rename_context_lift f #|cstr_args cdecl| 0).
        rewrite Nat.add_0_r in H.
        rewrite H. len. now rewrite shiftn0.
    ++ rewrite /p'. rewrite Nat.add_0_r. simpl.
      rewrite case_predicate_context_length //.
      { now apply rename_wf_predicate. }
      rewrite !case_predicate_context_length // Nat.add_0_r; len.
      rewrite case_predicate_context_length //.
      rewrite shiftn_add. rewrite - !lift_rename.
      now rewrite Nat.add_comm rename_shiftnk.
  * rewrite /= rename_mkApps /=. f_equal.
    ++ rewrite !map_map_compose /id. apply map_ext => t.
      rewrite /expand_lets /expand_lets_k.
      rewrite -rename_subst_instance_constr. len.
      rewrite -shiftn_add -shiftn_add.
      rewrite rename_subst. f_equal.
      rewrite rename_subst. rewrite (wf_predicate_length_pars wfp).
      rewrite (declared_minductive_ind_npars decli).
      rewrite -{2}(context_assumptions_subst_instance_context (puinst p) (ind_params mdecl)).
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

Fixpoint all_free_vars (p : nat -> bool) (t : term) : bool :=
  match t with
  | tRel i => p i
  | tEvar ev args => List.forallb (all_free_vars p) args
  | tLambda _ T M | tProd _ T M => all_free_vars p T && all_free_vars (shiftnP 1 p) M
  | tApp u v => all_free_vars p u && all_free_vars p v
  | tLetIn na b t b' => [&& all_free_vars p b, all_free_vars p t & all_free_vars (shiftnP 1 p) b']
  | tCase ind pred c brs =>
    [&& forallb (all_free_vars p) pred.(pparams),
      all_free_vars (shiftnP #|pred.(pcontext)| p) pred.(preturn),
      all_free_vars p c &
      forallb (fun br => all_free_vars (shiftnP #|br.(bcontext)| p) br.(bbody)) brs]
  | tProj _ c => all_free_vars p c
  | tFix mfix idx | tCoFix mfix idx =>
    List.forallb (test_def (all_free_vars p) (all_free_vars (shiftnP #|mfix| p))) mfix
  | tVar _ | tSort _ | tConst _ _ | tInd _ _ | tConstruct _ _ _ 
  | tPrim _ => true
  end.

Lemma all_free_vars_ext (p q : nat -> bool) t : 
  p =1 q ->
  all_free_vars p t = all_free_vars q t.
Proof.
  revert p q.
  induction t using PCUICInduction.term_forall_list_ind; simpl => //; intros;
    unfold test_def;
    rewrite ?forallb_map; try eapply All_forallb_eq_forallb; tea; eauto 2.
  all: try now rewrite (IHt1 p q) // ?(IHt2 (shiftnP 1 p) (shiftnP 1 q)) // H.
  - now rewrite (IHt1 p q) // ?(IHt2 p q) // (IHt3 (shiftnP 1 p) (shiftnP 1 q)) // H.
  - rewrite (IHt1 p q) // (IHt2 p q) //.
  - destruct X. red in X0.
    f_equal.
    * eapply All_forallb_eq_forallb; tea. solve_all.
    * f_equal; [eapply e; rewrite H //|].
      f_equal; [eapply IHt; rewrite H //|].
      eapply All_forallb_eq_forallb; tea. intros.
      eapply H0; rewrite H //.
  - simpl; intuition auto. f_equal; eauto 2.
    eapply b; rewrite H //.
  - simpl; intuition auto. f_equal; eauto 2.
    eapply b; rewrite H //.
Qed.

Instance all_free_vars_proper : Proper (`=1` ==> Logic.eq ==> Logic.eq) all_free_vars.
Proof. intros f g Hfg ? ? ->. now apply all_free_vars_ext. Qed.

Instance all_free_vars_proper_pointwise : Proper (`=1` ==> `=1`) all_free_vars.
Proof. intros f g Hfg x. now apply all_free_vars_ext. Qed.

Lemma shiftnP_impl (p q : nat -> bool) : (forall i, p i -> q i) ->
  forall n i, shiftnP n p i -> shiftnP n q i.
Proof.
  intros Hi n i. rewrite /shiftnP.
  nat_compare_specs => //. apply Hi.
Qed.

Lemma all_free_vars_impl (p q : nat -> bool) t : (forall i, p i -> q i) -> 
  all_free_vars p t -> all_free_vars q t.
Proof.
  revert t p q.
  induction t using PCUICInduction.term_forall_list_ind; simpl => //; solve_all.
  all:try (rtoProp; now rewrite ?IHt1 ?IHt2 ?IHt3; eauto 2).
  - rtoProp. intuition auto.
    * eapply IHt1; eauto.
    * eapply IHt2; eauto using shiftnP_impl.
  - rtoProp; intuition auto.
    * eapply IHt1; eauto.
    * eapply IHt2; eauto using shiftnP_impl.
  - rtoProp; intuition eauto 3 using shiftnP_impl.
  - rtoProp; intuition eauto 3 using shiftnP_impl.
    * solve_all.
    * solve_all; eauto using shiftnP_impl.
  - unfold test_def in *. apply /andP. move/andP: b. intuition eauto using shiftnP_impl.
  - unfold test_def in *. apply /andP. move/andP: b. intuition eauto using shiftnP_impl.
Qed.

Definition closedP (n : nat) (P : nat -> bool) := 
  fun i => if i <? n then P i else false.
  
Instance closedP_proper n : Proper (`=1` ==> `=1`) (closedP n).
Proof. intros f g Hfg. intros i; rewrite /closedP. now rewrite Hfg. Qed.
  
Lemma shiftnP_closedP k n P : shiftnP k (closedP n P) =1 closedP (k + n) (shiftnP k P).
Proof.
  intros i; rewrite /shiftnP /closedP.
  repeat nat_compare_specs => //.
Qed.

Lemma shiftnP_xpredT n : shiftnP n xpredT =1 xpredT.
Proof. intros i; rewrite /shiftnP. nat_compare_specs => //. Qed.

Lemma closedP_all_free_vars {n t} : closedn n t -> all_free_vars (closedP n xpredT) t.
Proof.
  revert n t.
  apply: term_closedn_list_ind; simpl => //; intros.
  all:(rewrite ?shiftnP_closedP ?shiftnP_xpredT).
  all:try (rtoProp; now rewrite ?IHt1 ?IHt2 ?IHt3).
  - rewrite /closedP /=. now nat_compare_specs.
  - solve_all.
  - destruct X. rtoProp. intuition solve_all.
    now rewrite shiftnP_closedP shiftnP_xpredT.
  - unfold test_def. solve_all.
    rewrite a. rewrite shiftnP_closedP shiftnP_xpredT.
    now len in b.
  - unfold test_def; solve_all. 
    rewrite a. rewrite shiftnP_closedP shiftnP_xpredT.
    now len in b.
Qed.

Lemma closedn_all_free_vars {P n t} : closedn n t -> all_free_vars (shiftnP n P) t.
Proof.
  move/closedP_all_free_vars.
  eapply all_free_vars_impl.
  intros i; rewrite /closedP /shiftnP /= //.
  nat_compare_specs => //.
Qed.

(** Any predicate is admissible as there are no free variables to consider *)
Lemma closed_all_free_vars {P t} : closed t -> all_free_vars P t.
Proof.
  move/closedP_all_free_vars.
  eapply all_free_vars_impl.
  intros i; rewrite /closedP /= //.
Qed.

Lemma all_free_vars_subst_instance {p u t} : all_free_vars p t = all_free_vars p (subst_instance_constr u t).
Proof.
  revert t p.
  apply: term_forall_list_ind; simpl => //; intros.
  all:try (rtoProp; now rewrite -?IHt1 -?IHt2 -?IHt3).
  - rewrite forallb_map. eapply All_forallb_eq_forallb; eauto.
  - destruct X. f_equal.
    * rewrite forallb_map; eapply All_forallb_eq_forallb; eauto.
    * rewrite -e -H. f_equal. f_equal.
      rewrite forallb_map. eapply All_forallb_eq_forallb; eauto.
  - unfold test_def. rewrite forallb_map; len.
    eapply All_forallb_eq_forallb; intuition eauto. solve_all.
  - unfold test_def; rewrite forallb_map; len.
    eapply All_forallb_eq_forallb; intuition eauto. solve_all.
Qed.

Definition test_decl (f : term -> bool) (d : context_decl) : bool :=
  f d.(decl_type) && foroptb f d.(decl_body).

Instance foroptb_proper A : Proper (`=1` ==> Logic.eq ==> Logic.eq) (@foroptb A).
Proof.
  intros f g Hfg x y ->; rewrite /foroptb.
  destruct y; simpl; rewrite // ?Hfg.
Qed.

Instance foroptb_proper_pointwise A : Proper (`=1` ==> `=1`) (@foroptb A).
Proof.
  intros f g Hfg y; rewrite /foroptb.
  destruct y; simpl; rewrite // ?Hfg.
Qed.

Instance test_decl_proper : Proper (`=1` ==> Logic.eq ==> Logic.eq) test_decl.
Proof. 
  intros f g Hfg [na [b|] ty] ? <- => /=; rewrite /test_decl /=;
  now rewrite Hfg.
Qed.

Definition all_free_vars_decl P d :=
  test_decl (all_free_vars P) d.

Instance all_free_vars_decl_proper : Proper (`=1` ==> Logic.eq ==> Logic.eq) all_free_vars_decl.
Proof. rewrite /all_free_vars_decl => f g Hfg x y <-. now rewrite Hfg. Qed.

Instance all_free_vars_decl_proper_pointwise : Proper (`=1` ==> `=1`) all_free_vars_decl.
Proof. rewrite /all_free_vars_decl => f g Hfg x. now rewrite Hfg. Qed.

Definition all_free_vars_ctx P ctx :=
  alli (fun k => (all_free_vars_decl (shiftnP k P))) 0 (List.rev ctx).

Instance all_free_vars_ctx_proper : Proper (`=1` ==> `=1`) all_free_vars_ctx.
Proof.
  rewrite /all_free_vars_ctx => f g Hfg x.
  now setoid_rewrite Hfg. 
Qed.

Definition orP (p q : nat -> bool) (n : nat) : bool :=
  p n || q n.

Definition conjP (p q : nat -> bool) (n : nat) : bool :=
  p n && q n.

Definition implP (p q : nat -> bool) (n : nat) : bool :=
  p n ==> q n.

Lemma alli_impl {A} (p q : nat -> A -> bool) n (l : list A) : 
  (forall i x, p i x -> q i x) ->
  alli p n l -> alli q n l.
Proof.
  intros hpq. induction l in n |- *; simpl; auto.
  move/andP => [pna a'].
  rewrite (hpq _ _ pna).
  now apply IHl.
Qed.

Lemma test_decl_impl (p q : term -> bool) d : 
  (forall i, p i -> q i) -> 
  test_decl p d -> test_decl q d.
Proof.
  intros hp. unfold test_decl.
  move/andP => [hty hbody].
  rewrite hp //.
  unfold foroptb in *.
  destruct (decl_body d) => // /=.
  now rewrite (hp _ hbody).
Qed.

Lemma all_free_vars_decl_impl (p q : nat -> bool) d : 
  (forall i, p i -> q i) -> 
  all_free_vars_decl p d -> all_free_vars_decl q d.
Proof.
  intros hpi.
  apply test_decl_impl. intros t.
  now apply all_free_vars_impl.
Qed.

Lemma all_free_vars_ctx_impl (p q : nat -> bool) ctx : 
  (forall i, p i -> q i) -> 
  all_free_vars_ctx p ctx -> all_free_vars_ctx q ctx.
Proof.
  intros hpi.
  eapply alli_impl => i x.
  apply all_free_vars_decl_impl.
  intros k; rewrite /shiftnP.
  now nat_compare_specs.
Qed.

Lemma closed_decl_all_free_vars {n d} : closed_decl n d -> all_free_vars_decl (closedP n xpredT) d.
Proof.
  rewrite /closed_decl /all_free_vars_decl /test_decl.
  rewrite andb_comm => /andP [cld clb].
  rewrite (closedP_all_free_vars cld) /=.
  destruct (decl_body d) eqn:db => /= //.
  rewrite /foroptb /=.
  now rewrite (closedP_all_free_vars clb).
Qed.

Lemma closedn_ctx_all_free_vars {n ctx} : closedn_ctx n ctx ->
  all_free_vars_ctx (closedP n xpredT) ctx.
Proof.
  rewrite /closedn_ctx /all_free_vars_ctx.
  apply alli_impl => i x.
  rewrite shiftnP_closedP Nat.add_comm shiftnP_xpredT.
  eapply closed_decl_all_free_vars.
Qed.

(** This uses absurdity elimination as [ctx] can't have any free variable *)
Lemma closed_ctx_all_free_vars P ctx : closed_ctx ctx ->
  all_free_vars_ctx P ctx.
Proof.
  move/closedn_ctx_all_free_vars => /=.
  rewrite /closedP /=.
  eapply all_free_vars_ctx_impl => //.
Qed.

Definition nocc_betweenp k n i :=
  (i <? k) || (k + n <=? i).

Definition nocc_between k n t := 
  (all_free_vars (nocc_betweenp k n) t).

Definition noccur_shift p k := fun i => (i <? k) || p (i - k).

Hint Resolve All_forallb_eq_forallb : all.

Definition strengthenP k n (p : nat -> bool) := 
  fun i => if i <? k then p i else 
    if i <? k + n then false 
    else p (i - n).

Instance strengthenP_proper n k : Proper (`=1` ==> `=1`) (strengthenP n k).
Proof.
  intros f g Hfg i. rewrite /strengthenP. now rewrite (Hfg i) (Hfg (i - k)).
Qed.

Lemma shiftnP_strengthenP k' k n p : 
  shiftnP k' (strengthenP k n p) =1 strengthenP (k' + k) n (shiftnP k' p).
Proof.
  intros i. rewrite /shiftnP /strengthenP.
  repeat nat_compare_specs => /= //. 
  lia_f_equal.
Qed.

Lemma all_free_vars_lift (p : nat -> bool) n k t : 
  all_free_vars (strengthenP k n p) (lift n k t) = all_free_vars p t.
Proof.
  intros. revert t n k p.
  induction t using PCUICInduction.term_forall_list_ind; simpl => //; intros;
    rewrite ?forallb_map; try eapply All_forallb_eq_forallb; tea; simpl.
  2-6:try now rewrite ?shiftnP_strengthenP ?IHt1 ?IHt2 ?IHt3.
  - rename n0 into i. rewrite /strengthenP.
    repeat nat_compare_specs => //.
    lia_f_equal.
  - intros. destruct X. red in X0.
    rewrite !shiftnP_strengthenP e IHt.
    f_equal.
    + solve_all.
    + f_equal; f_equal.
      eapply All_forallb_eq_forallb; tea. simpl; intros.
      now rewrite shiftnP_strengthenP.
  - unfold test_def in *. simpl; intros ? [].
    len; rewrite shiftnP_strengthenP. f_equal; eauto.
  - unfold test_def in *. simpl; intros ? [].
    len; rewrite shiftnP_strengthenP. f_equal; eauto.
Qed.

Definition all_free_vars_terms p s :=
  forallb (all_free_vars p) s.
  
Definition substP (k : nat) n (q p : nat -> bool) : nat -> bool :=
  fun i => 
    if i <? k then p i
    else p (i + n) || strengthenP 0 k q i.

Lemma shiftnP_substP k' k n q p : 
  shiftnP k' (substP k n q p) =1 substP (k' + k) n q (shiftnP k' p).
Proof.
  intros i; rewrite /shiftnP /substP.
  repeat nat_compare_specs => //.
  f_equal; [f_equal|].
  * lia_f_equal.
  * rewrite /strengthenP. simpl.
    repeat nat_compare_specs => //.
    lia_f_equal.
Qed.

Lemma all_free_vars_subst_gen (p q : nat -> bool) s k t : 
  all_free_vars_terms q s ->
  all_free_vars p t ->
  all_free_vars (substP k #|s| q p) (subst s k t).
Proof.
  revert t p k.
  induction t using PCUICInduction.term_forall_list_ind; simpl => //; intros;
    simpl.
  all:try (rtoProp; rewrite ?shiftnP_substP; now rewrite ?IHt1 ?IHt2 ?IHt3). 
  - intros. destruct (Nat.leb_spec k n).
    * destruct nth_error eqn:eq.
      + unfold all_free_vars_terms in *. toAll.
        pose proof (nth_error_Some_length eq).
        eapply nth_error_all in eq; eauto.
        simpl in eq. rewrite /substP.
        eapply all_free_vars_impl. 
        2:now rewrite -> all_free_vars_lift.
        rewrite /strengthenP. simpl.
        intros i. nat_compare_specs => //.
        intros ->. now rewrite orb_true_r.
      + eapply nth_error_None in eq.
        simpl. rewrite /substP.
        replace (n - #|s| + #|s|) with n by lia.
        nat_compare_specs.
        now rewrite H0.
    * simpl. rewrite /substP /strengthenP /=.
      rewrite H0. now nat_compare_specs.
  - solve_all.
  - rtoProp. destruct X. solve_all.
    * rewrite shiftnP_substP. solve_all.
    * rewrite shiftnP_substP; solve_all.
  - unfold test_def in *; red in X; solve_all.
    rtoProp. rewrite shiftnP_substP; len. solve_all.
  - unfold test_def in *; solve_all. rtoProp.
    rewrite shiftnP_substP; len. solve_all.
Qed.

Lemma rshiftk_S x f : S (rshiftk x f) = rshiftk (S x) f.
Proof. reflexivity. Qed.

Lemma red1_rename :
  forall P Σ Γ Δ u v f,
    wf Σ ->
    urenaming P Δ Γ f ->
    all_free_vars P u ->
    red1 Σ Γ u v ->
    red1 Σ Δ (rename f u) (rename f v).
Proof.
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
    rewrite rename_iota_red. 1:apply H2.
    { rewrite /brctx. rewrite case_branch_context_length //. }
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
      + simpl. 
        rewrite (case_branch_context_assumptions H1) in H2.
        rewrite case_branch_context_assumptions // -H2.
        now rewrite !List.skipn_length map_length.
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
  - rewrite rename_subst_instance_constr.
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
  - move/and4P: hav=> [_ hret _ _].
    rewrite rename_predicate_set_preturn.
    eapply case_red_return; eauto.
    + now apply rename_wf_predicate.
    + simpl.
      erewrite <-(case_predicate_context_length (p:=rename_predicate rename f p)); eauto.
      2:{ now eapply rename_wf_predicate. }
      eapply IHh; eauto.
      * rewrite <- !rename_case_predicate_context; eauto.
        len.
        erewrite <- (case_predicate_context_length H).
        now eapply urenaming_context.
  - move/and4P: hav=> [_ _ _ /forallb_All hbrs].
    eapply case_red_brs; eauto.
    + now eapply rename_wf_predicate.
    + now eapply rename_wf_branches.
    + replace (ind_ctors idecl) with (map (rename_constructor_body mdecl f) (ind_ctors idecl)).
      2:{ pose proof (declared_inductive_closed_constructors isdecl).
          solve_all. now rewrite rename_closed_constructor_body. }
      eapply OnOne2All_map_all. red in H0.
      eapply Forall2_All2 in H0.
      eapply OnOne2All_All2_mix_left in X; eauto. clear H0.
      eapply OnOne2All_All_mix_left in X; eauto. solve_all.
      red; simpl. split; auto. rewrite -b1.
      rewrite - rename_case_branch_context_gen; eauto.
      * eapply (declared_inductive_closed_params isdecl).
      * now apply wf_branch_length.
      * rewrite -(declared_minductive_ind_npars isdecl).
        now apply (wf_predicate_length_pars H).
      * eapply b2.
        ++ erewrite <-(case_branch_context_length b0).
          now eapply urenaming_context.
        ++ rewrite case_branch_context_length //.
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
 
Lemma substP_shiftnP n p : 
  substP 0 n p (shiftnP n p) =1 p.
Proof.
  intros i; rewrite /shiftnP /substP /= /strengthenP /=.
  nat_compare_specs.
  replace (i + n - n) with i by lia.
  now rewrite Nat.sub_0_r orb_diag.
Qed.

Lemma all_free_vars_subst (p : nat -> bool) s t : 
  forallb (all_free_vars p) s ->
  all_free_vars (shiftnP #|s| p) t ->
  all_free_vars p (subst s 0 t).
Proof.
  intros hs ht.
  epose proof (all_free_vars_subst_gen (shiftnP #|s| p) p s 0 t).
  rewrite -> substP_shiftnP in H.
  apply H.
  - exact hs.
  - apply ht.
Qed.

Lemma all_free_vars_subst1 (p : nat -> bool) s t : 
  all_free_vars p s ->
  all_free_vars (shiftnP 1 p) t ->
  all_free_vars p (subst1 s 0 t).
Proof.
  intros hs ht.
  rewrite /subst1.
  epose proof (all_free_vars_subst_gen (shiftnP 1 p) p [s] 0 t).
  rewrite -> substP_shiftnP in H.
  apply H.
  - now rewrite /all_free_vars_terms /= hs.
  - apply ht.
Qed.

Definition addnP n (p : nat -> bool) :=
  fun i => p (i + n).

Instance addnP_proper n : Proper (`=1` ==> Logic.eq ==> Logic.eq) (addnP n).
Proof.
  intros i f g Hfg; now rewrite /addnP.
Qed.
  
Instance addnP_proper_pointwise : Proper (Logic.eq ==> `=1` ==> `=1`) addnP.
Proof.
  intros i f g Hfg; now rewrite /addnP.
Qed.

Lemma addnP_shiftnP n P : addnP n (shiftnP n P) =1 P.
Proof.
  intros i; rewrite /addnP /shiftnP /=.
  nat_compare_specs. lia_f_equal.
Qed.

Definition on_ctx_free_vars P ctx :=
  alli (fun k d => P k ==> (all_free_vars_decl (addnP (S k) P) d)) 0 ctx.

Instance on_ctx_free_vars_proper : Proper (`=1` ==> eq ==> eq) on_ctx_free_vars.
Proof.
  rewrite /on_ctx_free_vars => f g Hfg x y <-.
  apply alli_ext => k.
  now setoid_rewrite Hfg. 
Qed.

Instance on_ctx_free_vars_proper_pointwise : Proper (`=1` ==> `=1`) on_ctx_free_vars.
Proof.
  rewrite /on_ctx_free_vars => f g Hfg x.
  apply alli_ext => k.
  now setoid_rewrite Hfg. 
Qed.

Lemma alli_Alli {A} (p : nat -> A -> bool) n l : 
  alli p n l <~> Alli p n l.
Proof.
  destruct (allbiP p p n l).
  - intros. destruct (p i x); now constructor.
  - split; eauto.
  - split; eauto. by [].
Qed.

Lemma addnP_add n k p : addnP n (addnP k p) =1 addnP (n + k) p.
Proof.
  rewrite /addnP => i. lia_f_equal.
Qed.

Lemma nth_error_all_free_vars_ctx P n ctx i d :
  on_ctx_free_vars (addnP n P) ctx ->
  P (n + i) ->
  nth_error ctx i = Some d ->
  test_decl (all_free_vars (addnP (n + S i) P)) d.
Proof.
  rewrite /on_ctx_free_vars.
  solve_all.
  eapply alli_Alli, Alli_nth_error in H; eauto.
  rewrite /= {1}/addnP Nat.add_comm H0 /= in H.
  now rewrite Nat.add_comm -addnP_add.
Qed.

Definition aboveP k (p : nat -> bool) :=
  fun i => if i <? k then false else p i.

Lemma strengthenP_addn i p : strengthenP 0 i (addnP i p) =1 aboveP i p.
Proof.
   intros k.
   rewrite /strengthenP /= /addnP /aboveP.
   nat_compare_specs => //.
   lia_f_equal.
Qed.

Lemma all_free_vars_lift0 i p t :
  all_free_vars (addnP i p) t ->
  all_free_vars p (lift0 i t).
Proof.
  rewrite -(all_free_vars_lift _ i 0).
  rewrite /strengthenP /= /aboveP /addnP.
  unshelve eapply all_free_vars_impl.
  simpl. intros i'. nat_compare_specs => //.
  now replace (i' - i + i) with i' by lia.
Qed.

Lemma all_free_vars_lift0_above i p t :
  all_free_vars (addnP i p) t = all_free_vars (aboveP i p) (lift0 i t).
Proof.
  rewrite -(all_free_vars_lift _ i 0).
  rewrite /strengthenP /= /aboveP /addnP.
  unshelve eapply all_free_vars_ext.
  simpl. intros i'. nat_compare_specs => //.
  now replace (i' - i + i) with i' by lia.
Qed.

Lemma all_free_vars_mkApps p f args : 
  all_free_vars p (mkApps f args) = all_free_vars p f && forallb (all_free_vars p) args.
Proof.
  induction args in f |- * => /=.
  - now rewrite andb_true_r.
  - now rewrite IHargs /= andb_assoc.
Qed.

Lemma forallb_ext {A} (p q : A -> bool) : p =1 q -> forallb p =1 forallb q.
Proof.
  intros hpq l.
  induction l; simpl; auto.
  now rewrite (hpq a) IHl.
Qed.

Instance forallb_proper {A} : Proper (`=1` ==> eq ==> eq) (@forallb A).
Proof.
  intros f g Hfg ? ? ->. now apply forallb_ext.
Qed.

Lemma extended_subst_shiftn p ctx n k : 
  forallb (all_free_vars (strengthenP 0 n (shiftnP (k + context_assumptions ctx) p))) 
    (extended_subst ctx (n + k)) =
  forallb (all_free_vars (shiftnP (k + (context_assumptions ctx)) p)) 
    (extended_subst ctx k).
Proof.
  rewrite lift_extended_subst' forallb_map.
  eapply forallb_ext => t.
  rewrite -(all_free_vars_lift _ n 0 t) //.
Qed.

Lemma extended_subst_shiftn_aboveP p ctx n k : 
  forallb (all_free_vars (aboveP n p)) (extended_subst ctx (n + k)) =
  forallb (all_free_vars (addnP n p)) (extended_subst ctx k).
Proof.
  rewrite lift_extended_subst' forallb_map.
  eapply forallb_ext => t.
  rewrite -(all_free_vars_lift0_above) //.
Qed.

Lemma extended_subst_shiftn_impl p ctx n k : 
  forallb (all_free_vars (shiftnP (k + (context_assumptions ctx)) p)) 
    (extended_subst ctx k) ->
  forallb (all_free_vars (shiftnP (n + k + context_assumptions ctx) p))
    (extended_subst ctx (n + k)).
Proof.
  rewrite lift_extended_subst' forallb_map.
  eapply forallb_impl => t _.
  rewrite -(all_free_vars_lift _ n 0 t).
  rewrite /strengthenP /=.
  apply all_free_vars_impl => i.
  rewrite /shiftnP.
  repeat nat_compare_specs => //.
  intros.
  red; rewrite -H2. lia_f_equal.
Qed.

Definition occ_betweenP k n :=
  fun i => (k <=? i) && (i <? k + n).

Lemma shiftn_above_strengthen n k p :
  forall i,  
  strengthenP n k p i -> 
  shiftnP k (aboveP n p) i.
Proof.
  intros i. rewrite /shiftnP /aboveP /strengthenP.
  repeat nat_compare_specs => /= //.
Abort.

Lemma alli_shiftn {A} n k p (l : list A) :
    alli p (n + k) l = alli (fun i => p (n + i)) k l.
Proof.
  induction l in n, k, p |- *; simpl; auto. f_equal.
  rewrite (IHl (S n) k p) (IHl 1 k _).
  apply alli_ext => x.
  now rewrite Nat.add_succ_r.
Qed.


Lemma addnP0 p : addnP 0 p =1 p.
Proof. intros i; now rewrite /addnP Nat.add_0_r. Qed.


Lemma all_free_vars_decl_all_term P d s :
  all_free_vars_decl P d = all_free_vars P (mkProd_or_LetIn d (tSort s)).
Proof.
  rewrite /all_free_vars_decl /= /test_decl.
  destruct d as [na [b|] ty] => /= //. rewrite /foroptb /= ?andb_true_r; bool_congr.
Qed.

Lemma all_free_vars_mkProd_or_LetIn P d t :
  all_free_vars P (mkProd_or_LetIn d t) = 
  all_free_vars_decl P d && all_free_vars (shiftnP 1 P) t.
Proof.
  destruct d as [na [b|] ty]; rewrite /mkProd_or_LetIn /all_free_vars_decl /test_decl /=
    ?andb_assoc /foroptb /=; try bool_congr.
  f_equal. bool_congr.
Qed.

Lemma all_free_vars_ctx_all_term P ctx s :
  all_free_vars_ctx P ctx = all_free_vars P (it_mkProd_or_LetIn ctx (tSort s)).
Proof.
  rewrite /all_free_vars_ctx.
  rewrite -{2}[P](shiftnP0 P).
  generalize 0 as k.
  induction ctx using rev_ind; simpl; auto; intros k.
  rewrite List.rev_app_distr alli_app /= andb_true_r.
  rewrite IHctx it_mkProd_or_LetIn_app /= all_free_vars_mkProd_or_LetIn.
  now rewrite shiftnP_add.
Qed.

Lemma expand_lets_it_mkProd_or_LetIn Γ Δ k t : 
  expand_lets_k Γ k (it_mkProd_or_LetIn Δ t) = 
  it_mkProd_or_LetIn (expand_lets_k_ctx Γ k Δ) (expand_lets_k Γ (k + #|Δ|) t).
Proof.
  revert k; induction Δ as [|[na [b|] ty] Δ] using ctx_length_rev_ind; simpl; auto; intros k.
  - now rewrite /expand_lets_k_ctx /= Nat.add_0_r.
  - rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /=.
    rewrite /expand_lets_ctx expand_lets_k_ctx_decl /= it_mkProd_or_LetIn_app.
    simpl. f_equal. rewrite app_length /=.
    simpl. rewrite Nat.add_1_r Nat.add_succ_r.
    now rewrite -(H Δ ltac:(lia) (S k)).
  - rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /=.
    rewrite /expand_lets_ctx expand_lets_k_ctx_decl /= it_mkProd_or_LetIn_app.
    simpl. f_equal. rewrite app_length /=.
    simpl. rewrite Nat.add_1_r Nat.add_succ_r.
    now rewrite -(H Δ ltac:(lia) (S k)).
Qed.

Lemma expand_lets_k_mkApps Γ k f args : 
  expand_lets_k Γ k (mkApps f args) =
  mkApps (expand_lets_k Γ k f) (map (expand_lets_k Γ k) args).
Proof.
  now rewrite /expand_lets_k lift_mkApps subst_mkApps map_map_compose.
Qed.

Lemma expand_lets_mkApps Γ f args : 
  expand_lets Γ (mkApps f args) =
  mkApps (expand_lets Γ f) (map (expand_lets Γ) args).
Proof.
  now rewrite /expand_lets expand_lets_k_mkApps.
Qed.

Lemma expand_lets_tRel k Γ : 
  expand_lets Γ (tRel (k + #|Γ|)) = tRel (k + context_assumptions Γ).
Proof.
  rewrite /expand_lets /expand_lets_k. 
  rewrite lift_rel_ge; try lia.
  rewrite subst_rel_gt; len; try lia.
  lia_f_equal.
Qed.

Definition all_free_vars_ctx_k P n ctx :=
  alli (fun k => (all_free_vars_decl (shiftnP k P))) n (List.rev ctx).

Instance orP_Proper : Proper (`=1` ==> `=1` ==> `=1`) orP.
Proof.
  intros f g Hfg f' g' Hfg' i; rewrite /orP.
  now rewrite Hfg Hfg'.
Qed.

Instance andP_Proper : Proper (`=1` ==> `=1` ==> `=1`) conjP.
Proof.
  intros f g Hfg f' g' Hfg' i; rewrite /conjP.
  now rewrite Hfg Hfg'.
Qed.

Instance implP_Proper : Proper (`=1` ==> `=1` ==> `=1`) implP.
Proof.
  intros f g Hfg f' g' Hfg' i; rewrite /implP.
  now rewrite Hfg Hfg'.
Qed.

Lemma orPL (p q : nat -> bool) : implP p (orP p q) =1 xpredT.
Proof.
  intros i. rewrite /implP /orP.
  rewrite (ssrbool.implybE (p i)).
  destruct (p i) => //.
Qed.

Lemma orPR (p q : nat -> bool) i : q i -> (orP p q) i.
Proof.
  rewrite /orP => ->; rewrite orb_true_r //.
Qed.

Lemma all_free_vars_implP p q t : 
  implP p q =1 xpredT ->
  all_free_vars p t -> all_free_vars q t.
Proof.
  rewrite /implP. intros Hp.
  eapply all_free_vars_impl.
  intros i hp. specialize (Hp i). now rewrite hp in Hp.
Qed.

Definition shiftnP_orP n p q : 
  shiftnP n (orP p q) =1 orP (shiftnP n p) (shiftnP n q).
Proof.
  intros i.
  rewrite /shiftnP /orP.
  repeat nat_compare_specs => //.
Qed.

Lemma addnP_orP n p q : addnP n (orP p q) =1 orP (addnP n p) (addnP n q).
Proof. reflexivity. Qed.

(** We need a disjunction here as the substitution can be made of 
    expanded lets (properly lifted) or just the variables of 
    [ctx] (lifted by [k]).
    
    The proof could certainly be simplified using a more high-level handling of
    free-variables predicate, which form a simple classical algebra. 
    To investigate: does ssr's library support this? *)

Lemma all_free_vars_extended_subst p k ctx :
  all_free_vars_ctx_k p k ctx ->
  forallb (all_free_vars 
    (orP (strengthenP 0 (context_assumptions ctx + k) (shiftnP k p)) 
      (occ_betweenP k (context_assumptions ctx))))
    (extended_subst ctx k).
Proof.
  rewrite /all_free_vars_ctx_k.
  induction ctx as [|[na [b|] ty] ctx] in p, k |- *; auto.
  - simpl. rewrite alli_app /= andb_true_r=> /andP [] hctx.
    rewrite /all_free_vars_decl /test_decl /=; len => /andP [] hty /= hb.
    specialize (IHctx _ k hctx).
    rewrite IHctx // andb_true_r.
    eapply all_free_vars_subst => //.
    len. erewrite all_free_vars_implP => //; cycle 1.
    { erewrite all_free_vars_lift; eauto. }
    rewrite shiftnP_orP.
    now rewrite shiftnP_strengthenP Nat.add_0_r shiftnP_add orPL.
  - cbn. rewrite alli_app /= andb_true_r => /andP [] hctx.
    rewrite /all_free_vars_decl /test_decl andb_true_r /= => hty.
    len in hty.
    specialize (IHctx p k).
    rewrite orPR /=.
    * rewrite /occ_betweenP. repeat nat_compare_specs => /= //.
    * specialize (IHctx hctx).
      rewrite (lift_extended_subst' _ 1).
      rewrite forallb_map.
      solve_all.
      apply all_free_vars_lift0.
      rewrite addnP_orP.
      eapply all_free_vars_implP; eauto.
      intros i. unfold implP, orP.
      rewrite /strengthenP /= /addnP /=.
      repeat nat_compare_specs => /= //.
      + rewrite /occ_betweenP /implP => /=.
        repeat nat_compare_specs => /= //.
      + rewrite /shiftnP /occ_betweenP /=.
        repeat nat_compare_specs => /= //.
        rewrite !orb_false_r.
        replace (i + 1 - S (context_assumptions ctx + k) - k) with
          (i - (context_assumptions ctx + k) - k) by lia.
        rewrite implybE. destruct p; auto. 
Qed.

Lemma all_free_vars_expand_lets_k P Γ n t : 
  n = context_assumptions Γ ->
  all_free_vars_ctx P Γ ->
  all_free_vars (shiftnP #|Γ| P) t ->
  all_free_vars (shiftnP n P) (expand_lets_k Γ 0 t).
Proof.
  intros -> HΓ Ht.
  rewrite /expand_lets_k /=.
  eapply all_free_vars_impl; cycle 1.
  - eapply all_free_vars_subst_gen.
    1:eapply all_free_vars_extended_subst; eauto.
    rewrite -> all_free_vars_lift. eauto.
  - len. rewrite /substP /= /strengthenP /=.
    intros i. simpl. rewrite /shiftnP.
    repeat nat_compare_specs => /= //.
    rewrite Nat.sub_0_r. rewrite /orP.
    replace (i + #|Γ| - context_assumptions Γ - #|Γ|) with (i - context_assumptions Γ) by lia.
    rewrite /occ_betweenP. repeat nat_compare_specs => /= //.
    rewrite orb_false_r Nat.sub_0_r.
    now rewrite orb_diag.
Qed.

Lemma all_free_vars_terms_inds P ind puinst bodies : 
  all_free_vars_terms P (inds ind puinst bodies).
Proof.
  rewrite /inds.
  induction #|bodies|; simpl; auto.
Qed.

Lemma all_free_vars_decl_map P f d :
  (forall i, all_free_vars P i = all_free_vars P (f i)) ->
  all_free_vars_decl P d = all_free_vars_decl P (map_decl f d).
Proof.
  intros Hi.
  rewrite /all_free_vars_decl /test_decl.
  rewrite Hi. f_equal.
  simpl. destruct (decl_body d) => //.
  now rewrite /foroptb /= (Hi t).
Qed.

Lemma all_free_vars_subst_instance_context P u Γ :
  all_free_vars_ctx P (subst_instance_context u Γ) = all_free_vars_ctx P Γ.
Proof.
  rewrite /all_free_vars_ctx.
  rewrite /subst_instance_context -map_rev alli_map.
  apply alli_ext => i d.
  symmetry. apply all_free_vars_decl_map.
  intros. apply all_free_vars_subst_instance.
Qed.

Lemma all_free_vars_map2_cstr_args p bctx ctx :
  #|bctx| = #|ctx| ->
  all_free_vars_ctx p ctx =
  all_free_vars_ctx p (map2 set_binder_name bctx ctx).
Proof.
  rewrite /all_free_vars_ctx.
  induction ctx as [|d ctx] in bctx |- *; simpl; auto.
  - destruct bctx; reflexivity.
  - destruct bctx => /= //.
    intros [= hlen].
    rewrite alli_app (IHctx bctx) // alli_app. f_equal.
    len. rewrite map2_length // hlen. f_equal.
Qed.

Lemma all_free_vars_case_branch_context {Σ} {wfΣ : wf Σ} {P ci i mdecl idecl p br cdecl} :
  let brctx := case_branch_context ci mdecl p (bcontext br) cdecl in
  declared_constructor Σ (ci, i) mdecl idecl cdecl ->
  wf_predicate mdecl idecl p ->
  wf_branch cdecl br ->
  forallb (all_free_vars P) (pparams p) ->
  all_free_vars_ctx P brctx.
Proof.
  intros brctx decli wfp wfb havp.
  rewrite /brctx /case_branch_context /case_branch_context_gen.
  rewrite (all_free_vars_ctx_all_term _ _ Universe.type0).
  rewrite -(subst_it_mkProd_or_LetIn _ _ _ (tSort _)).
  apply all_free_vars_subst => //.
  rewrite -(expand_lets_it_mkProd_or_LetIn _ _ 0 (tSort _)).
  eapply all_free_vars_expand_lets_k; len.
  * rewrite (wf_predicate_length_pars wfp).
    apply (declared_minductive_ind_npars decli).
  * eapply closed_ctx_all_free_vars.
    rewrite closedn_subst_instance_context.
    apply (declared_inductive_closed_params decli).
  * rewrite -(subst_it_mkProd_or_LetIn _ _ _ (tSort _)).
    eapply all_free_vars_impl; cycle 1.
    + eapply (all_free_vars_subst_gen _ P).
      { eapply all_free_vars_terms_inds. }
      rewrite -all_free_vars_ctx_all_term.
      rewrite all_free_vars_subst_instance_context.
      rewrite -all_free_vars_map2_cstr_args.
      { apply (wf_branch_length wfb). }
      instantiate (1 := closedP (#|mdecl.(ind_bodies)| + #|mdecl.(ind_params)|) xpredT).
      eapply closedn_ctx_all_free_vars.
      now move/andP: (declared_constructor_closed wfΣ decli) => [] /andP [].
    + intros i'.
      rewrite /substP /= /closedP /shiftnP. len.
      now repeat nat_compare_specs => /= //.
Qed.

Lemma all_free_vars_to_extended_list P ctx : 
  forallb (all_free_vars (shiftnP #|ctx| P)) (to_extended_list ctx).
Proof.
  rewrite /to_extended_list /to_extended_list_k.
  change #|ctx| with (0 + #|ctx|).
  have: (forallb (all_free_vars (shiftnP (0 + #|ctx|) P)) []) by easy.
  generalize (@nil term), 0.
  induction ctx; intros l n.
  - simpl; auto.
  - simpl. intros Hl.
    destruct a as [? [?|] ?].
    * rewrite Nat.add_succ_r in Hl.
      specialize (IHctx _ (S n) Hl).
      now rewrite Nat.add_succ_r Nat.add_1_r.
    * rewrite Nat.add_succ_r Nat.add_1_r. eapply (IHctx _ (S n)).
      rewrite -[_ + _](Nat.add_succ_r n #|ctx|) /= Hl.
      rewrite /shiftnP.
      nat_compare_specs => /= //.
Qed.

(** This is less precise than the strengthenP lemma above *)
Lemma all_free_vars_lift_impl (p : nat -> bool) (n k : nat) (t : term) :
  all_free_vars (shiftnP k p) t ->
  all_free_vars (shiftnP (n + k) p) (lift n k t).
Proof.
  rewrite -(all_free_vars_lift _ n k t).
  eapply all_free_vars_impl.
  intros i.
  rewrite /shiftnP /strengthenP.
  repeat nat_compare_specs => /= //.
  now replace (i - n - k) with (i - (n + k)) by lia.
Qed.

Lemma all_free_vars_case_predicate_context {Σ} {wfΣ : wf Σ} {P ci mdecl idecl p} :
  let pctx := case_predicate_context ci mdecl idecl p in
  declared_inductive Σ ci mdecl idecl ->
  wf_predicate mdecl idecl p ->
  forallb (all_free_vars P) (pparams p) ->
  all_free_vars (shiftnP #|pcontext p| P) (preturn p) ->
  all_free_vars_ctx P pctx.
Proof.
  intros pctx decli wfp wfb havp.
  rewrite /pctx /case_predicate_context /case_predicate_context_gen.
  set (ibinder := {| decl_name := _ |}).
  rewrite -all_free_vars_map2_cstr_args /=; len.
  { eapply (wf_predicate_length_pcontext wfp). }
  rewrite alli_app; len; rewrite andb_true_r.
  apply andb_true_iff. split.
  - rewrite -/(all_free_vars_ctx P _).
    rewrite (all_free_vars_ctx_all_term _ _ Universe.type0).
    rewrite -(subst_it_mkProd_or_LetIn _ _ _ (tSort _)).
    apply all_free_vars_subst => //.
    rewrite -all_free_vars_ctx_all_term.
    rewrite all_free_vars_subst_instance_context.
    rewrite (all_free_vars_ctx_all_term _ _ (Universe.type0)).
    rewrite -(expand_lets_it_mkProd_or_LetIn _ _ 0 (tSort _)).
    eapply all_free_vars_expand_lets_k; len.
    * rewrite (wf_predicate_length_pars wfp).
      apply (declared_minductive_ind_npars decli).
    * eapply closed_ctx_all_free_vars.
      apply (declared_inductive_closed_params decli).
    * eapply all_free_vars_impl; cycle 1.
      { rewrite <- all_free_vars_ctx_all_term.
        instantiate (1 := closedP #|mdecl.(ind_params)| xpredT).
        eapply closedn_ctx_all_free_vars.
        move: (declared_inductive_closed_pars_indices wfΣ decli).
        now rewrite closedn_ctx_app => /andP []. }
       intros i'.
      rewrite /substP /= /closedP /shiftnP. len.
      now repeat nat_compare_specs => /= //.
  - rewrite /all_free_vars_decl /ibinder /test_decl /= /foroptb /= andb_true_r.
    rewrite all_free_vars_mkApps /= forallb_app /=.
    rewrite all_free_vars_to_extended_list /= andb_true_r.
    rewrite -/(is_true _).
    rewrite forallb_map. unshelve eapply (forallb_impl _ _ _ _ wfb).
    intros. simpl.
    eapply all_free_vars_lift0. now rewrite addnP_shiftnP.
Qed.

Lemma forall_free_vars_extended_subst brctx p :
  all_free_vars_ctx p brctx ->
  forallb (all_free_vars (shiftnP (context_assumptions brctx) p))
    (extended_subst brctx 0).
Proof.
  move/all_free_vars_extended_subst.
  eapply forallb_impl.
  intros x hin.
  rewrite Nat.add_0_r shiftnP0.
  eapply all_free_vars_impl.
  intros i. rewrite /orP /strengthenP /= /occ_betweenP /shiftnP.
  repeat nat_compare_specs => /= //.
  now rewrite orb_false_r.
Qed.

Lemma all_free_vars_fix_subst P mfix idx :
  all_free_vars P (tFix mfix idx) ->
  forallb (all_free_vars P) (fix_subst mfix).
Proof.
  move=> /=; rewrite /fix_subst.
  intros hmfix. generalize hmfix.
  induction mfix at 2 4; simpl; auto.
  move/andP => [ha hm]. rewrite IHm // andb_true_r //.
Qed.

Lemma all_free_vars_unfold_fix P mfix idx narg fn :
  unfold_fix mfix idx = Some (narg, fn) ->
  all_free_vars P (tFix mfix idx) ->
  all_free_vars P fn.
Proof.
  rewrite /unfold_fix. 
  destruct nth_error eqn:hnth => // [=] _ <- /=.
  intros hmfix; generalize hmfix.
  move/forallb_All/(nth_error_all hnth) => /andP [] _ Hbody.
  eapply all_free_vars_subst; len => //.
  eapply (all_free_vars_fix_subst _ _ idx) => //.
Qed.

Lemma all_free_vars_cofix_subst P mfix idx :
  all_free_vars P (tCoFix mfix idx) ->
  forallb (all_free_vars P) (cofix_subst mfix).
Proof.
  move=> /=; rewrite /cofix_subst.
  intros hmfix. generalize hmfix.
  induction mfix at 2 4; simpl; auto.
  move/andP => [ha hm]. rewrite IHm // andb_true_r //.
Qed.

Lemma all_free_vars_unfold_cofix P mfix idx narg fn :
  unfold_cofix mfix idx = Some (narg, fn) ->
  all_free_vars P (tCoFix mfix idx) ->
  all_free_vars P fn.
Proof.
  rewrite /unfold_cofix. 
  destruct nth_error eqn:hnth => // [=] _ <- /=.
  intros hmfix; generalize hmfix.
  move/forallb_All/(nth_error_all hnth) => /andP [] _ Hbody.
  eapply all_free_vars_subst; len => //.
  eapply (all_free_vars_cofix_subst _ _ idx) => //.
Qed.

Lemma nth_error_forallb {A} {p : A -> bool} {l : list A} {n x} :
  nth_error l n = Some x -> forallb p l -> p x.
Proof.
  intros Hnth HPl. 
  induction l in n, Hnth, HPl |- * => //.
  - rewrite nth_error_nil in Hnth => //.
  - destruct n => /=; noconf Hnth.
    * now move: HPl => /= /andP.
    * eapply IHl; tea. now move: HPl => /andP.
Qed.

Lemma addnP_shiftnP_comm n (P : nat -> bool) : P 0 -> addnP 1 (shiftnP n P) =1 shiftnP n (addnP 1 P).
Proof.
  intros p0 i; rewrite /addnP /shiftnP /=.
  repeat nat_compare_specs => /= //. 
  - assert (n = i + 1) as -> by lia.
    now replace (i + 1 - (i + 1)) with 0 by lia.
  - lia_f_equal.
Qed.

Lemma on_ctx_free_vars_concat P Γ Δ : 
  on_ctx_free_vars P Γ ->
  on_ctx_free_vars (shiftnP #|Δ| P) Δ ->  
  on_ctx_free_vars (shiftnP #|Δ| P) (Γ ,,, Δ).
Proof.
  rewrite /on_ctx_free_vars alli_app.
  move=> hΓ -> /=; rewrite alli_shiftn.
  eapply alli_impl; tea => i d /=.
  simpl.
  rewrite {1}/shiftnP. nat_compare_specs.
  replace (#|Δ| + i - #|Δ|) with i by lia.
  destruct (P i) eqn:pi => /= //.
  apply all_free_vars_decl_impl => k.
  rewrite /addnP /shiftnP.
  nat_compare_specs.
  now replace (k + S (#|Δ| + i) - #|Δ|) with (k + S i) by lia.
Qed.

Lemma on_ctx_free_vars_tip P d : on_ctx_free_vars P [d] = P 0 ==> all_free_vars_decl (addnP 1 P) d.
Proof.
  now rewrite /on_ctx_free_vars /= /= andb_true_r.
Qed.

Lemma OnOne2_impl_All_r {A} (P : A -> A -> Type) (Q : A -> Type) l l' : 
  (forall x y, Q x -> P x y -> Q y) ->
  OnOne2 P l l' -> All Q l -> All Q l'.
Proof.
  intros HPQ.
  induction 1; intros H; depelim H; constructor; auto.
  now eapply HPQ.
Qed.

Lemma OnOne2All_impl_All_r {A B} (P : B -> A -> A -> Type) (Q : A -> Type) i l l' : 
  (forall i x y, Q x -> P i x y -> Q y) ->
  OnOne2All P i l l' -> All Q l -> All Q l'.
Proof.
  intros HPQ.
  induction 1; intros H; depelim H; constructor; auto.
  now eapply HPQ.
Qed.

Lemma shiftnPS n P : shiftnP (S n) P n.
Proof.
  rewrite /shiftnP /=.
  now nat_compare_specs.
Qed.

Lemma on_ctx_free_vars_extend P Γ Δ :
  all_free_vars_ctx P Δ ->
  on_ctx_free_vars P Γ ->
  on_ctx_free_vars (shiftnP #|Δ| P) (Γ ,,, Δ).
Proof.
  intros hΔ hΓ.
  apply on_ctx_free_vars_concat => //.
  revert P Γ hΓ hΔ.
  induction Δ using rev_ind; simpl; auto; intros P Γ hΓ.
  rewrite /on_ctx_free_vars /all_free_vars_ctx List.rev_app_distr /= shiftnP0.
  rewrite alli_shift. setoid_rewrite Nat.add_comm. setoid_rewrite <- shiftnP_add.
  move/andP=> [] hx hΔ.
  rewrite alli_app /= andb_true_r Nat.add_0_r; len.
  rewrite Nat.add_comm.
  rewrite addnP_shiftnP.
  specialize (IHΔ (shiftnP 1 P) (Γ ,, x)).
  forward IHΔ.
  * simpl. apply (on_ctx_free_vars_concat _ _ [x]) => //.
    simpl.
    now rewrite on_ctx_free_vars_tip {1}/shiftnP /= addnP_shiftnP.
  * specialize (IHΔ hΔ).
    rewrite shiftnPS /= hx andb_true_r.
    rewrite /on_ctx_free_vars in IHΔ.
    rewrite -(Nat.add_1_r #|Δ|).
    setoid_rewrite <-(shiftnP_add).
    now setoid_rewrite <- (shiftnP_add _ _ _ _).
Qed.

Lemma OnOne2All_nth_error {A B} (P : A -> B -> B -> Type) il l l' :
  OnOne2All P il l l' ->
  OnOne2All (fun i x y => (∑ ni, nth_error il ni = Some i) * P i x y) il l l'.
Proof.
  induction 1.
  - econstructor => //.
    split => //.
    exists 0; reflexivity.
  - constructor. eapply (OnOne2All_impl IHX).
    intros i x y [[ni hni] ?].
    split; auto. exists (S ni). apply hni.
Qed.

Lemma all_free_vars_fix_context P mfix : 
  All (fun x : def term =>
      test_def (all_free_vars P) (all_free_vars (shiftnP #|mfix| P)) x)
      mfix ->
  all_free_vars_ctx P (fix_context mfix).
Proof.
  intros a.
  assert (All (fun x => all_free_vars P x.(dtype)) mfix).
  { solve_all. now move/andP: H=> []. } clear a.
  induction mfix using rev_ind; simpl; auto.
  rewrite /fix_context /= mapi_app List.rev_app_distr /=.
  rewrite /all_free_vars_ctx /= alli_app. len.
  rewrite andb_true_r.
  eapply All_app in X as [X Hx].
  depelim Hx. clear Hx.
  specialize (IHmfix X).
  rewrite /all_free_vars_ctx in IHmfix.
  rewrite IHmfix /= /all_free_vars_decl /test_decl /= /foroptb /= andb_true_r.
  apply all_free_vars_lift0.
  now rewrite addnP_shiftnP.
Qed.
(* 
Definition all_free_vars_ctx_gen P ctx :=
  alli (fun k => (all_free_vars_decl (addnP k P))) 0 ctx.

Instance all_free_vars_ctx_gen_proper : Proper (`=1` ==> `=1`) all_free_vars_ctx_gen.
Proof.
  rewrite /all_free_vars_ctx_gen => f g Hfg x.
  now setoid_rewrite Hfg. 
Qed.

Lemma all_free_vars_ctx_gen_decl (P : nat -> bool) (Q : nat -> bool) Γ i d : 
  nth_error Γ i = Some d ->
  P i ->
  (forall k, all_free_vars (addnP i Q) k -> all_free_vars (addnP i P) k) ->
  all_free_vars_ctx_gen Q Γ -> 
  test_decl (all_free_vars (addnP i P)) d.
Proof.
  rewrite /all_free_vars_ctx_gen.
  solve_all.
  eapply alli_Alli, Alli_nth_error in H2; eauto.
  simpl in H1. rewrite /all_free_vars_decl in H1.
  eapply test_decl_impl. 2:eapply H2.
  intros. simpl in H3. apply H1. auto.
Qed. *)


(** This shows preservation by reduction of closed/noccur_between predicates 
  necessary to prove exchange and strengthening lemmas. *)
Lemma red1_all_free_vars {P : nat -> bool} {Σ Γ u v} {wfΣ : wf Σ} :
  all_free_vars P u ->
  (* (forall i k, P i -> (* The ith variable of Γ is present  *)
  (* k respect Q for the prefix of Γ from begginning to i, i.e. k 
    is under Γ_i *)
  all_free_vars (addnP (S i) Q) k -> 
  (* P holds *)
  all_free_vars (addnP (S i) P) k) -> *)
  on_ctx_free_vars P Γ ->
  red1 Σ Γ u v ->
  all_free_vars P v.
Proof.
  intros hav hctx h.
  induction h using red1_ind_all in P, hav, hctx |- *.
  all: try solve [
    simpl ; constructor ; eapply IHh ;
    try (simpl in hav; rtoProp);
    try eapply urenaming_vass ;
    try eapply urenaming_vdef ;
    assumption
  ].
  all:simpl in hav |- *; try toAll.
  all:try move/and3P: hav => [h1 h2 h3].
  all:try (move/andP: hav => [] /andP [] h1 h2 h3).
  all:try move/andP: hav => [h1 h2].
  all:try move/andP: h3 => [] h3 h4.
  all:try rewrite ?h1 // ?h2 // ?h3 // ?h4 // ?IHh /= // ?andb_true_r.
  all:try eapply all_free_vars_subst1; eauto.
  - destruct (nth_error Γ i) eqn:hnth => //.
    simpl in H. noconf H.
    epose proof (nth_error_all_free_vars_ctx P 0 Γ i c).
    forward H0. { now rewrite addnP0. }
    specialize (H0 hav hnth). simpl in H0.
    rewrite /test_decl H in H0.
    rewrite all_free_vars_lift0 //.
    move/andP: H0 => [].
    now rewrite /foroptb /= => _ hbod.
  - rewrite /iota_red. rename h4 into hbrs.
    move: h3. rewrite all_free_vars_mkApps => /andP [] hf hargs.
    apply all_free_vars_subst.
    { rewrite forallb_skipn //. }
    rewrite H2.
    rewrite /expand_lets /expand_lets_k /=.
    eapply all_free_vars_subst.
    * eapply forall_free_vars_extended_subst.
      eapply all_free_vars_case_branch_context; eauto.
    * rewrite extended_subst_length.
      rewrite (case_branch_context_length H1).
      rewrite shiftnP_add.
      eapply nth_error_forallb in hbrs; eauto.
      simpl in hbrs.
      eapply all_free_vars_lift_impl in hbrs.
      now rewrite Nat.add_comm.
  - rewrite !all_free_vars_mkApps in hav |- *.
    rtoProp.
    eapply all_free_vars_unfold_fix in H; eauto. 
  - move: h3; rewrite !all_free_vars_mkApps.
    move=> /andP[] hcofix ->.
    eapply all_free_vars_unfold_cofix in hcofix; eauto.
    now rewrite hcofix.
  - move: hav; rewrite !all_free_vars_mkApps => /andP [] hcofix ->.
    eapply all_free_vars_unfold_cofix in H as ->; eauto.
  - eapply closed_all_free_vars. rewrite closedn_subst_instance_constr.
    eapply declared_constant_closed_body; eauto.
  - move: hav; rewrite all_free_vars_mkApps /=.
    now move/(nth_error_forallb H).
  - rewrite (on_ctx_free_vars_concat _ _ [_]) // /=
      on_ctx_free_vars_tip /= addnP_shiftnP /all_free_vars_decl
      /test_decl /= andb_true_r //.
  - rewrite (on_ctx_free_vars_concat _ _ [_]) //
      on_ctx_free_vars_tip /= addnP_shiftnP /all_free_vars_decl /test_decl /= h2 /=
      /foroptb /= h1 //.
  - solve_all.
    eapply OnOne2_impl_All_r; eauto. solve_all.
  - rewrite /pctx.
    rewrite -(case_predicate_context_length (ci:=ci) H).
    eapply on_ctx_free_vars_extend => //.
    apply (all_free_vars_case_predicate_context isdecl H h1 h2).
  - toAll.
    eapply Forall2_All2 in H0.
    eapply OnOne2All_All2_mix_left in X; eauto.
    eapply OnOne2All_nth_error in X.
    eapply OnOne2All_impl_All_r in X; eauto; solve_all.
    destruct a as [cidx hnth].
    rewrite -b. eapply b1 => //.
    erewrite <- (case_branch_context_length b0).
    eapply on_ctx_free_vars_extend => //.
    eapply (all_free_vars_case_branch_context (i := cidx)); eauto.
    * split; eauto.
    * solve_all.
  - rewrite (on_ctx_free_vars_concat _ _ [_]) // /=
      on_ctx_free_vars_tip /= addnP_shiftnP /all_free_vars_decl /test_decl /= h1 /= //.
  - toAll. eapply OnOne2_impl_All_r; eauto; solve_all.
  - toAll. unfold test_def.
    rewrite -(OnOne2_length X).
    eapply OnOne2_impl_All_r; eauto; solve_all.
    destruct x, y; noconf b; simpl in *. rtoProp; solve_all.
  - toAll. unfold test_def in *. rewrite -(OnOne2_length X).
    eapply OnOne2_impl_All_r; eauto; solve_all.
    destruct x, y; noconf b; simpl in *; rtoProp; solve_all.
    apply b0 => //.
    rewrite -(fix_context_length mfix0).
    eapply on_ctx_free_vars_extend => //.
    now apply all_free_vars_fix_context.
  - toAll. unfold test_def.
    rewrite -(OnOne2_length X).
    eapply OnOne2_impl_All_r; eauto; solve_all.
    destruct x, y; noconf b; simpl in *. rtoProp; solve_all.
  - toAll. unfold test_def in *. rewrite -(OnOne2_length X).
    eapply OnOne2_impl_All_r; eauto; solve_all.
    destruct x, y; noconf b; simpl in *; rtoProp; solve_all.
    apply b0 => //.
    rewrite -(fix_context_length mfix0).
    eapply on_ctx_free_vars_extend => //.
    now apply all_free_vars_fix_context.
Qed.

(* Lemma cumul_rename :
  forall P Σ Γ Δ f A B,
    wf Σ.1 ->
    urenaming (shiftnP #|Γ| P) Δ Γ f ->
    Σ ;;; Γ |- A <= B ->
    Σ ;;; Δ |- rename f A <= rename f B.
Proof.
  intros P Σ Γ Δ f A B hΣ hf h.
  induction h.
  - eapply cumul_refl. eapply eq_term_upto_univ_rename. assumption.
  - eapply cumul_red_l.
    + eapply red1_rename. all: try eassumption.
    + apply IHh.
      * eapply (red1_all_free_vars hA); tea.
      * auto.
  - eapply cumul_red_r.
    + eapply IHh; eauto. eapply (red1_all_free_vars hB); tea.
    + eapply red1_rename. all: try eassumption.
Qed. *)

Lemma cumul_renameP :
  forall P Σ Γ Δ f A B,
    wf Σ.1 ->
    urenaming P Δ Γ f ->
    all_free_vars P A ->
    all_free_vars P B ->
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
      * eapply (red1_all_free_vars hA); tea.
      * auto.
  - eapply cumul_red_r.
    + eapply IHh; eauto. eapply (red1_all_free_vars hB); tea.
    + eapply red1_rename. all: try eassumption.
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
  preturn (rename_predicate rename f p).
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

Lemma All2i_map {A B C D} (R : nat -> C -> D -> Type) (f : A -> C) (g : B -> D) n l l' :
  All2i (fun i x y => R i (f x) (g y)) n l l' -> All2i R n (map f l) (map g l').
Proof. induction 1; simpl; constructor; try congruence. Qed.

Lemma All2i_map_right {B C D} (R : nat -> C -> D -> Type) (g : B -> D) n l l' :
  All2i (fun i x y => R i x (g y)) n l l' -> All2i R n l (map g l').
Proof. induction 1; simpl; constructor; try congruence. Qed.

Lemma All2i_nth_impl_gen {A B} (R : nat -> A -> B -> Type) n l l' :
  All2i R n l l' ->
  All2i (fun i x y => 
    (if i <? n then False
    else nth_error l (i - n) = Some x) * R i x y) n l l'.
Proof.
  intros a. depind a.
  - constructor.
  - constructor.
    * simpl. destruct (Nat.ltb n n) eqn:ltb.
      + eapply Nat.ltb_lt in ltb. lia.
      + rewrite Nat.sub_diag. auto.
    * simpl. eapply (All2i_impl IHa).
      intros. destruct (Nat.ltb i (S n)) eqn:ltb; simpl in *; destruct X =>  //.
      apply Nat.ltb_nlt in ltb. 
      destruct (Nat.ltb i n) eqn:ltb'; simpl in *.
      + eapply Nat.ltb_lt in ltb'. lia.
      + eapply Nat.ltb_nlt in ltb'.
        assert (i - n = S (i - S n)) as -> by lia. simpl. now rewrite e.
Qed.

Lemma All2i_nth_hyp {A B} (R : nat -> A -> B -> Type) l l' :
  All2i R 0 l l' ->
  All2i (fun i x y => (nth_error l i = Some x) * R i x y) 0 l l'.
Proof.
  intros a.
  eapply All2i_nth_impl_gen in a. simpl in a.
  eapply (All2i_impl a). intros.
  now rewrite Nat.sub_0_r in X.
Qed.

Lemma case_branch_type_length {ci mdecl idecl p br ptm i cdecl} :
  wf_branch cdecl br ->
  #|(case_branch_type ci mdecl idecl p br ptm i cdecl).1| = #|cstr_args cdecl|.
Proof.
  intros wf; simpl.
  now rewrite case_branch_context_length_args.
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
  rewrite /rename_context fold_context_app /app_context. f_equal.
  apply fold_context_ext. intros i x. now rewrite shiftn_add.
Qed.

Lemma fold_context_tip f d : fold_context f [d] = [map_decl (f 0) d].
Proof. reflexivity. Qed.

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
    * rewrite /rename_context fold_context_tip /map_decl /=. do 2 f_equal.
      now rewrite shiftn0.
Qed.

Lemma nth_error_rename_context f Γ n : 
  nth_error (rename_context f Γ) n = 
  option_map (map_decl (rename (shiftn (#|Γ| - S n) f))) (nth_error Γ n).
Proof.
  induction Γ in n |- *; intros.
  - simpl. unfold rename_context, fold_context; simpl; rewrite nth_error_nil. easy.
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

Lemma map_option_out_impl {A B} (l : list A) (f g : A -> option B) x :
  (forall x y, f x = Some y -> g x = Some y) ->
  map_option_out (map f l) = Some x ->
  map_option_out (map g l) = Some x.
Proof.
  intros Hfg.
  induction l in x |- *; simpl; auto.
  destruct (f a) eqn:fa.
  - rewrite (Hfg _ _ fa).
    move: IHl; destruct map_option_out.
    * move=> H'. specialize (H' _ eq_refl).
      rewrite H'. congruence.
    * discriminate.
  - discriminate.
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
(*
Lemma wf_local_renaming Σ Γ : 
  All_local_env (lift_typing (fun (Σ : global_env_ext) (Γ : context) (t T : term) =>
    forall (Δ : PCUICEnvironment.context) (f : nat -> nat),
    urenaming Δ Γ f -> Σ;;; Δ |- rename f t : rename f T) Σ) Γ ->
  forall Δ' f, 
  urenaming Δ' Γ f ->
  wf_local Σ Δ'.
Proof.
  intros. red in X0.
  induction X.
  - red in X0.
  - simpl. destruct t0 as [s Hs].
    rewrite rename_context_snoc /=. constructor; auto.
    red. simpl. exists s.
    eapply (Hs (Δ' ,,, rename_context f Γ0) (shiftn #|Γ0| f)).
    split => //. 
    now eapply urenaming_context.
  - destruct t0 as [s Hs]. red in t1.
    rewrite rename_context_snoc /=. constructor; auto.
    * red. exists s.
      apply (Hs (Δ' ,,, rename_context f Γ0) (shiftn #|Γ0| f)).
      split=> //. now eapply urenaming_context.
    * red. apply t1. split => //.
      now eapply urenaming_context. 
Qed.*)

Lemma renaming_extP P P' Σ Γ Δ f :
  P =1 P' ->
  renaming P Σ Γ Δ f -> renaming P' Σ Γ Δ f.
Proof.
  intros hP; rewrite /renaming.
  intros []; split; eauto.
  eapply urenaming_ext; eauto. reflexivity.
Qed.

(** For an unconditional renaming defined on all variables in the source context *)
Lemma typing_rename_prop : env_prop
  (fun Σ Γ t A =>
    forall P Δ f,
    renaming (shiftnP #|Γ| P) Σ Δ Γ f ->
    Σ ;;; Δ |- rename f t : rename f A)
   (fun Σ Γ =>
   All_local_env
   (lift_typing (fun (Σ : global_env_ext) (Γ : context) (t T : term)
    =>
    forall P (Δ : PCUICEnvironment.context) (f : nat -> nat),
    renaming (shiftnP #|Γ| P) Σ Δ Γ f -> 
    Σ;;; Δ |- rename f t : rename f T) Σ) Γ).
Proof.
  apply typing_ind_env.
  
  - intros Σ wfΣ Γ wfΓ HΓ.
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
    + rewrite rename_subst_instance_constr. f_equal.
      rewrite rename_closed. 2: auto.
      eapply declared_constant_closed_type. all: eauto.
  - intros Σ wfΣ Γ wfΓ ind u mdecl idecl isdecl X X0 hconst P Δ σ hf.
    simpl. eapply meta_conv.
    + econstructor. all: eauto. apply hf.
    + rewrite rename_subst_instance_constr. f_equal.
      rewrite rename_closed. 2: auto.
      eapply declared_inductive_closed_type. all: eauto.
  - intros Σ wfΣ Γ wfΓ ind i u mdecl idecl cdecl isdecl X X0 hconst P Δ f hf.
    simpl. eapply meta_conv.
    + econstructor. all: eauto. apply hf. 
    + rewrite rename_closed. 2: reflexivity.
      eapply declared_constructor_closed_type. all: eauto.
  - intros Σ wfΣ Γ wfΓ ci p c brs indices ps mdecl idecl isdecl HΣ.
    intros IHΔ ci_npar predctx wfp Hpret IHpret IHpredctx isallowed.
    intros Hc IHc iscof ptm wfbrs Hbrs P Δ f Hf.
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
        ++ apply All_local_env_app_inv in IHpredctx as [].
          eapply wf_local_app_renaming; eauto. apply a0.
        ++ rewrite /predctx.
           rewrite -(case_predicate_context_length (ci:=ci) wfp).
           eapply urenaming_ext.
           { len. now rewrite -shiftnP_add. }
           { reflexivity. }
          eapply urenaming_context. apply Hf.
      + simpl. unfold id.
        specialize (IHc _ _ _ Hf).
        now rewrite rename_mkApps map_app in IHc.
      + now eapply rename_wf_branches.
      + eapply Forall2_All2 in wfbrs.
        eapply All2i_All2_mix_left in Hbrs; eauto.
        eapply All2i_nth_hyp in Hbrs.
        eapply All2i_map_right, (All2i_impl Hbrs) => i cdecl br.
        set (brctxty := case_branch_type _ _ _ _ _ _ _ _).
        move=> [Hnth [wfbr [[Hbr Hbrctx] [IHbr [Hbty IHbty]]]]].
        rewrite -(rename_closed_constructor_body mdecl cdecl f).
        { eapply (declared_constructor_closed (c:=(ci.(ci_ind),i))); eauto.
          split; eauto. }
        rewrite rename_case_branch_type //.
        rewrite -/brctxty. intros brctx'.
        assert (wf_local Σ (Δ,,, brctx'.1)).
        { rewrite /brctx'. cbn.
          apply All_local_env_app_inv in Hbrctx as [].
          eapply wf_local_app_renaming; tea. apply a0. }
        repeat split.
        ++ eapply IHbr. 
          split => //.
          rewrite /brctx' /brctxty; cbn.
          rewrite (wf_branch_length wfbr).
          erewrite <- case_branch_type_length; eauto.
          eapply urenaming_ext.
          { now rewrite app_context_length -shiftnP_add. }
          { reflexivity. }
          eapply urenaming_context, Hf.
        ++ eapply IHbty. split=> //.
          rewrite /brctx'; cbn.
          rewrite (wf_branch_length wfbr).
          erewrite <- case_branch_type_length; eauto.
          eapply urenaming_ext.
          { now rewrite app_context_length -shiftnP_add. }
          { reflexivity. }
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
      rewrite rename_subst_instance_constr. f_equal.
      rewrite rename_closedn. 2: reflexivity.
      eapply declared_projection_closed_type in isdecl.
      rewrite List.rev_length. rewrite e. assumption.

  - intros Σ wfΣ Γ wfΓ mfix n decl types H1 hdecl X ihmfixt ihmfixb wffix P Δ f hf.
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
        ++ len; now sigma.
      * now eapply rename_wf_fixpoint.
    + reflexivity.

  - intros Σ wfΣ Γ wfΓ mfix n decl types guard hdecl X ihmfixt ihmfixb wfcofix P Δ f hf.
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
        now eapply closedn_all_free_vars in H.
      * pose proof (subject_closed _ htB).
        now eapply closedn_all_free_vars in H.
      * pose proof (closed_ctx_all_free_vars P _ (closed_wf_local _ (typing_wf_local ht))).
        rewrite -{2}(app_context_nil_l Γ).
        eapply on_ctx_free_vars_extend => //.
Qed.

Lemma typing_rename_P :
  forall P Σ Γ Δ f t A,
    wf Σ.1 ->
    renaming (shiftnP #|Γ| P) Σ Δ Γ f ->
    Σ ;;; Γ |- t : A ->
    Σ ;;; Δ |- rename f t : rename f A.
Proof.
  intros P Σ Γ Δ f t A hΣ hf h.
  revert Σ hΣ Γ t A h P Δ f hf.
  apply typing_rename_prop.
Qed.

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

Lemma typing_rename :
  forall Σ Γ Δ f t A,
    wf Σ.1 ->
    renaming (closedP #|Γ| xpredT) Σ Δ Γ f ->
    Σ ;;; Γ |- t : A ->
    Σ ;;; Δ |- rename f t : rename f A.
Proof.
  intros Σ Γ Δ f t A hΣ hf h.
  eapply (typing_rename_P (fun _ => false)) ; eauto.
Qed.

Lemma typing_all_free_vars : env_prop
  (fun Σ Γ t A =>
    forall P,
    all_free_vars (closedP #|Γ| P) t ->
    ∑ Af, (red Σ Γ A Af * all_free_vars (closedP #|Γ| P) Af))
   (fun Σ Γ =>
   All_local_env
   (lift_typing (fun (Σ : global_env_ext) (Γ : context) (t T : term)
    =>
    forall P,
    all_free_vars (closedP #|Γ| P) t ->
    ∑ Af, (red1 Σ Γ T Af * all_free_vars (closedP #|Γ| P) Af)) Σ) Γ).
Proof.
  (*
  apply typing_ind_env.
  7:{
    - intros Σ wfΣ Γ wfΓ t na A B a u X hty ihty ht iht hu ihu P.
      simpl. move/andP=> [havt havs].
      destruct (iht _ havt) as [ty [redty hav]].
      eapply invert_red_prod in redty as [A' [B' [[eq redA] redB]]]. subst ty.
      move: hav => /= /andP [hA' hB'].
      eexists (B' {0 := a}); split. 1:admit.
      eapply all_free_vars_subst=> /=; rewrite ?havs //. }
  2:{ - intros Σ wfΣ Γ wfΓ n decl isdecl ihΓ P.
        simpl in * => hn.
        eexists; split; eauto.
        eapply (nth_error_All_local_env (n:=n)) in ihΓ.
        2:{ eapply nth_error_Some_length in isdecl; eauto. }
        rewrite isdecl in ihΓ. simpl in ihΓ. rewrite /closedP in hn.
        move: hn; nat_compare_specs => //. intros pn.
        move: ihΓ. unfold on_local_decl. 
        destruct decl_body eqn:db;
        unfold lift_typing; simpl.
        * intros ih. specialize (ih P).
          rewrite skipn_length // in ih.
          rewrite all_free_vars_lift0 //.
          admit.
        * admit. }

  13:{
    - intros Σ wfΣ Γ wfΓ t A B X hwf ht iht htB ihB cum P hav.
      specialize (iht _ hav) as [Af [redAf havaf]].
      admit. (* certainly provable *)
  }*)
Admitted.

(* 
Lemma typing_rename_prop' : env_prop
  (fun Σ Γ t A =>
    forall Δ f,
    renaming (closedP #|Γ| xpredT) Σ Δ Γ f ->
    Σ ;;; Δ |- rename f t : rename f A)
   (fun Σ Γ =>
   All_local_env
   (lift_typing (fun (Σ : global_env_ext) (Γ : context) (t T : term)
    =>
    forall P (Δ : PCUICEnvironment.context) (f : nat -> nat),
    renaming (closedP #|Γ| P) Σ Δ Γ f -> 
    Σ;;; Δ |- rename f t : rename f T) Σ) Γ).
Proof.
  red. intros.
  destruct (typing_rename_prop Σ wfΣ Γ t T ty) as [? []].
  split.
  - eapply on_global_env_impl. 2:eapply f.
    intros.
    red in X0. destruct T0; red.
    * intros.
      eapply (X0 xpredT).
      


  destruct X. *)

End Renaming.


