(* Distributed under the terms of the MIT license. *)
From Coq Require Import Morphisms.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICInduction
  PCUICLiftSubst PCUICUnivSubst PCUICEquality PCUICTyping PCUICWeakeningEnv
  PCUICClosed PCUICReduction PCUICPosition PCUICGeneration
  PCUICSigmaCalculus PCUICRename PCUICOnFreeVars.

Require Import ssreflect ssrbool.
From Equations Require Import Equations.

Implicit Types cf : checker_flags.

Definition noccur_between_decl k n d :=
  option_default (noccur_between k n) d.(decl_body) true && 
  noccur_between k n d.(decl_type).

Definition noccur_between_ctx k n (t : context) : bool :=
  alli (fun k' => noccur_between_decl (k + k') n) 0 (List.rev t).

Lemma noccur_between_ctx_cons k n d Γ : 
  noccur_between_ctx k n (d :: Γ) = 
  noccur_between_decl (k + #|Γ|) n d && noccur_between_ctx k n Γ.
Proof.
  unfold noccur_between_ctx.
  simpl. rewrite alli_app /= andb_true_r.
  now rewrite Nat.add_0_r List.rev_length andb_comm.
Qed.


Lemma shiftn_ext_noccur_between f f' k n k' i :
  (i < k' + k \/ k' + k + n <= i) ->
  (forall i, i < k \/ k + n <= i -> f i = f' i) ->
  shiftn k' f i = shiftn k' f' i.
Proof.
  intros.
  unfold shiftn. destruct (Nat.ltb_spec i k').
  - auto.
  - rewrite H0; auto. lia.
Qed.

Lemma rename_ext_cond f f' k n : (forall i, i < k \/ k + n <= i -> f i = f' i) -> 
  (forall t, noccur_between k n t -> rename f t = rename f' t).
Proof.
intros. revert k n t H0 f f' H.
apply: term_noccur_between_list_ind; simpl in |- *; intros; try easy ;
  try (try rewrite H; try rewrite H0 ; try rewrite H1 ; easy);
  try solve [f_equal; solve_all].
- f_equal; auto. apply H0. intros.
  eapply (shiftn_ext_noccur_between f f' k n); eauto.
- f_equal; auto. apply H0. intros.
  eapply (shiftn_ext_noccur_between f f' k n); eauto.
- f_equal; auto. eapply H1. intros.
  eapply (shiftn_ext_noccur_between f f' k n); eauto.
- destruct X. f_equal; auto; solve_all.
  * apply e. intros.
    eapply (shiftn_ext_noccur_between f f' k n); eauto.
  * apply map_branch_eq_spec. apply H1.
    intros; eapply (shiftn_ext_noccur_between f f' k n); eauto.
- red in X. f_equal; solve_all.
  eapply map_def_eq_spec; auto. apply b.
  rewrite fix_context_length.
  intros; eapply (shiftn_ext_noccur_between f f' k n); eauto.
- f_equal; auto. red in X. solve_all.
  eapply map_def_eq_spec; auto. apply b.
  rewrite fix_context_length.
  intros. eapply (shiftn_ext_noccur_between f f' k n); eauto.
Qed.

Lemma rename_decl_ext_cond f f' k n : (forall i, i < k \/ k + n <= i -> f i = f' i) -> 
  (forall t, noccur_between_decl k n t -> rename_decl f t = rename_decl f' t).
Proof.
  intros Hi d. move/andb_and=> [clb clt].
  rewrite /rename_decl.
  destruct d as [na [b|] ty] => /=; rewrite /map_decl /=; simpl in *; f_equal.
  - f_equal. now eapply rename_ext_cond.
  - now eapply rename_ext_cond.
  - now eapply rename_ext_cond.
Qed.  


Definition strengthen k n :=
  fun i => if i <? k then i else (i - n).

Lemma shiftn_strengthen_rel k n i k' : 
  (i < k + k' \/ k + k' + n <= i) ->
  shiftn k (strengthen k' n) i = strengthen (k + k') n i.
Proof.
  rewrite /shiftn /strengthen.
  destruct (Nat.ltb_spec i k); auto.
  - destruct (Nat.ltb_spec i (k + k')); lia.
  - destruct (Nat.ltb_spec (i - k) k'); destruct (Nat.ltb_spec i (k + k')); lia.
Qed.

Lemma shiftn_strengthen k k' n t : 
  noccur_between (k' + k) n t ->
  rename (shiftn k (strengthen k' n)) t = rename (strengthen (k + k') n) t.
Proof.
  intros nocc.
  eapply rename_ext_cond; tea.
  intros. eapply shiftn_strengthen_rel. lia.
Qed.

Definition strengthen_context (Γ Γs Δ : context) :=
  Γ ,,, rename_context (strengthen 0 #|Γs|) Δ.

Definition strengthen_rename Δ Γs i :=  
  if i <? Δ then
    strengthen (Δ - S i) Γs
  else id.


Lemma lookup_strengthen_context Γ Γs Δ i :
  let Δ' := lift_context #|Γs| 0 Δ in 
  nocc_betweenp #|Δ| #|Γs| i ->
  nth_error (strengthen_context Γ Γs Δ') (strengthen #|Δ| #|Γs| i) = 
  option_map (map_decl (rename (strengthen_rename #|Δ| #|Γs| i))) 
    (nth_error (Γ ,,, Γs ,,, Δ') i).
Proof.
  simpl.
  rewrite /strengthen_context /strengthen /nocc_betweenp.
  (* Again, => _ is counter-intuitive to me here. e.g when doing
    repeat (nat_compare_specs => /= //) => /= _. it's not equivalent
    to the line below.
   *)
  repeat (nat_compare_specs => /= //). all:move=> _.
  * rewrite (nth_error_app_context_ge i); len => //.
    rewrite (nth_error_app_context_ge (i - #|Δ|)); len; try lia => //.
    rewrite (nth_error_app_context_ge (i - #|Γs|)); len; try lia => //.
    replace (i - #|Δ| - #|Γs|) with (i - #|Γs| - #|Δ|) by lia.
    destruct nth_error => /= //. f_equal.
    rewrite -{1}[c](map_decl_id c).
    apply map_decl_ext => x.
    rewrite -(rename_ren_id x).
    apply rename_ext.
    rewrite /strengthen_rename. nat_compare_specs.
    reflexivity.
  * rewrite nth_error_app_lt; len => //.
    rewrite nth_error_app_lt; len => //.
    rewrite /rename_context.
    rewrite nth_error_lift_context_eq Nat.add_0_r.
    rewrite /lift_context fold_context_k_compose option_map_two.
    destruct (nth_error Δ i) eqn:hnth => //.
    + rewrite (nth_error_fold_context_k _ _ _ _ _ _ hnth) /=; eauto.
      f_equal. rewrite compose_map_decl. apply map_decl_ext => t.
      rewrite !lift_rename !rename_compose.
      eapply rename_ext => k.
      rewrite /strengthen_rename /shiftn /lift_renaming /= /strengthen.
      now repeat nat_compare_specs => /= //.
    + now apply nth_error_None in hnth.
Qed.

Lemma strengthen_shiftn k n : strengthen k n ∘ (shiftn k (rshiftk n)) =1 id.
Proof.
  intros i; rewrite /strengthen /shiftn /rshiftk /id.
  repeat nat_compare_specs.
Qed.

Lemma rshiftk_shiftn k n l i : rshiftk k (shiftn n l i) = shiftn (n + k) l (rshiftk k i).
Proof.
  intros.
  rewrite /rshiftk. 
  rewrite /shiftn. repeat nat_compare_specs.
  replace (k + i - (n + k)) with (i - n) by lia. lia.
Qed.

Lemma S_rshiftk k n : S (rshiftk k n) = rshiftk (S k) n.
Proof. reflexivity. Qed.

Lemma strengthen_lift_renaming n k i : strengthen k n (lift_renaming n k i) = i.
Proof.
  rewrite /strengthen /lift_renaming.
  repeat nat_compare_specs.
Qed.

Lemma strengthen_lift n k t : rename (strengthen k n) (lift n k t) = t.
Proof.
  rewrite lift_rename rename_compose.
  setoid_rewrite strengthen_lift_renaming.
  now rewrite rename_ren_id.
Qed.


Lemma strengthen_lift_ctx n k t : rename_context (strengthen k n) (lift_context n k t) = t.
Proof.
  rewrite -rename_context_lift_context.
  rewrite /rename_context fold_context_k_compose.
  rewrite -{2}(fold_context_k_id t).
  apply fold_context_k_ext => i x.
  rewrite rename_compose shiftn_compose.  
  setoid_rewrite strengthen_lift_renaming.
  now rewrite shiftn_id rename_ren_id.
Qed.

Lemma strengthen_urenaming_gen Γ Γs Δ :
  let Δ' := lift_context #|Γs| 0 Δ in 
  urenaming (nocc_betweenp #|Δ| #|Γs|)
    (strengthen_context Γ Γs Δ')
    (Γ ,,, Γs ,,, Δ')
    (strengthen #|Δ| #|Γs|).
Proof.
  intros Δ' i d hpi hnth.
  rewrite lookup_strengthen_context /= // hnth /=.
  eexists; split; eauto.
  destruct d as [na b ty]; simpl in *.
  unfold nocc_betweenp in hpi.
  move/orP: hpi. intros hi.
  move: hnth. rewrite /Δ'.
  move: hi => []; [move/Nat.ltb_lt|move/Nat.leb_le] => hi.
  - rewrite nth_error_app_context_lt; len; try lia.
    rewrite nth_error_lift_context_eq Nat.add_0_r.
    destruct nth_error eqn:hnth => /= // [=] <- <- <-.
    repeat split.
    + rewrite rename_compose lift_rename !rename_compose.
      apply rename_ext.
      intros k. 
      change (S (rshiftk i (lift_renaming #|Γs| (#|Δ| - S i) k)))
        with (rshiftk (S i) (lift_renaming #|Γs| (#|Δ| - S i) k)).
      rewrite lift_renaming_spec.
      rewrite /strengthen_rename. nat_compare_specs.
      rewrite (strengthen_shiftn _ _ _) /id.
      rewrite rshiftk_shiftn Nat.sub_add // S_rshiftk.
      rewrite -lift_renaming_spec strengthen_lift_renaming.
      rewrite /strengthen. nat_compare_specs.
    + destruct (decl_body c) => /= //.
      f_equal.
      rewrite rename_compose lift_rename !rename_compose.
      apply rename_ext.
      intros k. 
      change (S (rshiftk i (lift_renaming #|Γs| (#|Δ| - S i) k)))
        with (rshiftk (S i) (lift_renaming #|Γs| (#|Δ| - S i) k)).
      rewrite lift_renaming_spec.
      rewrite /strengthen_rename. nat_compare_specs.
      rewrite (strengthen_shiftn _ _ _) /id.
      rewrite rshiftk_shiftn Nat.sub_add // S_rshiftk.
      rewrite -lift_renaming_spec strengthen_lift_renaming.
      rewrite /strengthen. nat_compare_specs.
  - rewrite nth_error_app_context_ge; len; try lia.
    rewrite nth_error_app_context_ge; len; try lia.
    intros hnth.
    repeat split.
    + rewrite !rename_compose.
      apply rename_ext => k.
      rewrite /strengthen /strengthen_rename /rshiftk /id.
      repeat nat_compare_specs.
    + destruct b => //. simpl. f_equal.
      rewrite !rename_compose.
      apply rename_ext => k.
      rewrite /strengthen /strengthen_rename /rshiftk /id.
      repeat nat_compare_specs.
Qed.

Lemma strengthen_urenaming Γ Γs Δ :
  let Δ' := lift_context #|Γs| 0 Δ in 
  urenaming (nocc_betweenp #|Δ| #|Γs|)
    (Γ ,,, Δ)
    (Γ ,,, Γs ,,, Δ')
    (strengthen #|Δ| #|Γs|).
Proof.
  pose proof (strengthen_urenaming_gen Γ Γs Δ).
  simpl in X.
  rewrite /strengthen_context in X.
  now rewrite strengthen_lift_ctx in X.
Qed.

Lemma nth_error_noccur_between_ctx k n Γ i d : 
  noccur_between_ctx k n Γ -> 
  nth_error Γ i = Some d ->
  noccur_between_decl (k + (#|Γ| - S i)) n d.
Proof.
  rewrite /noccur_between_ctx.
  intros alli nth. apply alli_Alli in alli.
  eapply Alli_rev_nth_error in alli; eauto.
Qed.


Definition isLift n k t := 
  ∑ t', t = lift n k t'.

Lemma isLift_rel n k i : 
  isLift n k (tRel i) -> nocc_betweenp k n i.
Proof.
  intros [t' eq]. destruct t' => //.
  simpl in eq. noconf eq.
  unfold nocc_betweenp.
  repeat nat_compare_specs => /= //.
Qed.

Lemma All_local_env_over_simpl {cf:checker_flags} Σ Γ : 
  forall wfΓ : wf_local Σ Γ, 
  All_local_env_over typing
  (fun (Σ : global_env_ext) (Γ : context) (_ : wf_local Σ Γ)
    (t T : term) (_ : Σ;;; Γ |- t : T) =>
  forall Γl Γs Δ : context,
  Γ = Γl,,, Γs,,, lift_context #|Γs| 0 Δ ->
  isLift #|Γs| #|Δ| t ->
  isLift #|Γs| #|Δ| T ->
  Σ;;; Γl,,, Δ |- rename (strengthen #|Δ| #|Γs|) t
  : rename (strengthen #|Δ| #|Γs|) T) Σ Γ wfΓ ->
  All_local_env
  (lift_typing (fun (Σ : global_env_ext) (Γ : context) (t T : term)  =>
  forall Γl Γs Δ : context,
  Γ = Γl,,, Γs,,, lift_context #|Γs| 0 Δ ->
  isLift #|Γs| #|Δ| t ->
  isLift #|Γs| #|Δ| T ->
  Σ;;; Γl,,, Δ |- rename (strengthen #|Δ| #|Γs|) t
  : rename (strengthen #|Δ| #|Γs|) T) Σ) Γ.
Proof.
  intros wfΓ. unfold lift_typing.
  induction 1; constructor; intuition auto.
  - destruct tu as [s Hs]; exists s; intuition auto.
  - destruct tu as [s Hs]; exists s; intuition auto.
Qed.

Lemma isLift_lift n k t : isLift n k (lift n k t).
Proof. eexists; eauto. Qed.

Definition is_strengthenable {cf:checker_flags} {Σ Γ t T} (d : Σ ;;; Γ |- t : T) (k n : nat) : bool.
Proof.
  revert Γ t T d k.
  fix aux 4.
  intros. destruct d.
  - exact (nocc_betweenp k n n0).
  - exact true.
  - exact (aux _ _ _ d1 k && aux _ _ _ d2 (S k)).
  - exact (aux _ _ _ d1 k && aux _ _ _ d2 (S k)).
  - exact [&& aux _ _ _ d1 k, aux _ _ _ d2 k & aux _ _ _ d3 (S k)].
  - exact [&& aux _ _ _ d1 k, aux _ _ _ d2 k & aux _ _ _ d3 k].
  - exact true.
  - exact true.
  - exact true.
  - exact true.
  - exact true.
  - exact true.
  - exact true.
  - exact (aux _ _ _ d1 k && aux _ _ _ d2 k).
Defined.

Lemma is_strengthenable_isLift {cf:checker_flags} {Σ Γ t T} (d : Σ ;;; Γ |- t : T) {n k}:
  is_strengthenable d k n ->
  isLift n k t × isLift n k T.
Proof.
  induction d in n, k |- *; simpl; intros.
  - admit.
  - split; eexists (tSort _); simpl; eauto.
  - move/andP: H => [isd1 isd2].
    specialize (IHd1 _ _ isd1) as [[A' ->] _].
    specialize (IHd2 _ _ isd2) as [[B' ->] _].
    split.
    * eexists (tProd na _ _); simpl; eauto.
    * now eexists (tSort _).
  - admit.
  - admit.
  - move/and3P: H => [hd1 hd2 hd3].
    specialize (IHd1 _ _ hd1) as [[p' eq] _].
    specialize (IHd2 _ _ hd2) as [[? ->] _].
    specialize (IHd3 _ _ hd3) as [[? ->] ?].
    split.
    * now eexists (tApp _ _).
    * destruct p' => //.
      noconf eq.
      rewrite /subst1.
      rewrite -(distr_lift_subst_rec _ [_]) /=.
      now eexists _.
  - split.
    * now eexists (tConst _ _).
    * admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - move/andP: H => [hd1 hd2].
    split.
    * apply (IHd1 _ _ hd1).
    * eapply (IHd2 _ _ hd2).
Admitted.

Lemma typing_rename_prop {cf:checker_flags} : 
  forall Σ {wfΣ : wf Σ.1} Γ t T (d : Σ ;;; Γ |- t : T),
    forall Γl Γs Δ, 
    is_strengthenable d #|Δ| #|Γs| -> 
    Γ = Γl ,,, Γs ,,, lift_context #|Γs| 0 Δ ->
    Σ ;;; Γl ,,, Δ |- rename (strengthen #|Δ| #|Γs|) t : rename (strengthen #|Δ| #|Γs|) T.
Proof.
  intros Σ wfΣ Γ t T d Γl. induction d; simpl.
  - intros ? ? hn ->. admit.
  - intros. admit.
  - intros ? ?.
    move/andP => [isd1 isd2]. intros ->.
    rewrite /=. econstructor.
    + eapply IHd1; eauto.
    + specialize (IHd1 _ _ isd1 eq_refl).
      pose proof (is_strengthenable_isLift _ isd1) as [[A' ->] _].
      specialize (IHd2 _ (Δ,, vass na A') isd2).
      forward IHd2. { now rewrite lift_context_snoc Nat.add_0_r. }
      rewrite strengthen_lift.
      rewrite shiftn_strengthen. { pose proof (is_strengthenable_isLift _ isd2). admit. }
      apply IHd2.
  - admit.
  - admit.
  - intros ? ?. move/and3P => [hd1 hd2 hd3]; intros ->.
    specialize (IHd1 _ _ hd1 eq_refl).
    specialize (IHd2 _ _ hd2 eq_refl).
    specialize (IHd3 _ _ hd3 eq_refl).
    eapply meta_conv.
    + eapply type_App.
    * simpl in IHd1. eapply IHd1; tea.
    * simpl in IHd2. eapply IHd2.
    * eapply IHd3.
    + now rewrite rename_subst10.
  - intros.
    autorewrite with sigma.
    admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - intros Γs Δ. move/andP=> [hd1 hd2]. intros ->.
    specialize (IHd1 _ _ hd1 eq_refl).
    specialize (IHd2 _ _ hd2 eq_refl).
    epose proof (is_strengthenable_isLift _ hd1).
    epose proof (is_strengthenable_isLift _ hd2).
    eapply type_Cumul; eauto.
    eapply cumul_renameP; eauto.
    * apply (strengthen_urenaming Γl Γs Δ).
    * destruct X. admit.
Admitted.

Lemma noccur_iss {cf:checker_flags} : 
  forall Σ {wfΣ : wf Σ.1} Γ t T (d : Σ ;;; Γ |- t : T),
    forall Γl Γs Δ, 
    Γ = Γl ,,, Γs ,,, lift_context #|Γs| 0 Δ ->
    isLift #|Γs| #|Δ| t ->
    ∑ T' (d' : Σ ;;; Γ |- t : T'), (is_strengthenable d' #|Δ| #|Γs|) × cumul Σ Γ T' T.
Proof.
  intros. induction d in Γs, Δ, X |- *.
  - eexists; unshelve eexists; [econstructor; eauto|].
    simpl. split; auto. 2:reflexivity. admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - destruct X as [[] ?]; noconf e.
    specialize (IHd2 _ _ (isLift_lift _ _ _)) as [? [IHd2 [isd2 ?]]].
    specialize (IHd3 _ _ (isLift_lift _ _ _)) as [? [IHd3 [isd3 ?]]].
    pose proof (is_strengthenable_isLift _ isd2) as [? [? ->]].
    eapply invert_cumul_prod_r in c as [? [? [? [[[? ?] ?] ?]]]].
    exists (x3 {0 := (lift #|Γs| #|Δ| v)}).
    unshelve eexists.
    * epose proof (type_reduction IHd2 r).
      econstructor.
      2:eauto. 1:admit.
      eapply type_Cumul'.
      + eapply IHd3.
      + admit.
      + admit.
    * simpl. admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - specialize (IHd1 _ _ X) as [A' [dA' [? ?]]].
    exists A', dA'. split; auto. admit.
Admitted.


Lemma all_free_vars_true t : all_free_vars xpredT t.
Proof.
Admitted.

Lemma strengthen_thm {cf} : forall Σ {wfΣ : wf Σ.1} Γ t T (d : Σ ;;; Γ |- t : T),
  forall Γl Γs Δ, 
  Γ = Γl ,,, Γs ,,, lift_context #|Γs| 0 Δ ->
  isLift #|Γs| #|Δ| t ->
  isLift #|Γs| #|Δ| T ->
  Σ ;;; Γl ,,, Δ |- rename (strengthen #|Δ| #|Γs|) t : rename (strengthen #|Δ| #|Γs|) T.
Proof.
  intros.
  pose proof (noccur_iss _ _ _ _ d _ _ _ H X) as [T' [d' [isd cum]]].
  pose proof (typing_rename_prop _ _ _ _ d' _ _ _ isd H).
  eapply type_Cumul'; eauto.
  * destruct X0 as [? ->].
    rewrite strengthen_lift. admit.
  * subst Γ. eapply cumul_renameP; eauto.
    + eapply strengthen_urenaming.
    + epose proof (is_strengthenable_isLift _ isd). admit.
    + admit.
    + unfold on_ctx_free_vars.
      rewrite alli_app. apply/andP; split.
      - rewrite /lift_context.
        rewrite alli_fold_context_k_prop.
        clear. eapply alli_Alli.
        eapply forall_nth_error_Alli.
        intros i x hnth. simpl.
        eapply nth_error_Some_length in hnth.
        rewrite {1}/nocc_betweenp. nat_compare_specs.
        nat_compare_specs. simpl.
        rewrite Nat.add_0_r.
        rewrite /all_free_vars_decl.
        rewrite test_decl_map_decl.
        eapply (test_decl_impl (fun _ => true)).
        { intros k _.
          eapply all_free_vars_impl.
          2:{ erewrite all_free_vars_lift. apply all_free_vars_true. } 
          intros k'.
          rewrite /strengthenP /nocc_betweenp /addnP.
          repeat nat_compare_specs => /= //. }
        destruct x as [na [?|] ? ]=> //.
Admitted.

Lemma typing_rename_prop {cf:checker_flags} : env_prop
  (fun Σ Γ t A =>
    forall Γl Γs Δ, 
    Γ = Γl ,,, Γs ,,, lift_context #|Γs| 0 Δ ->
    isLift #|Γs| #|Δ| t ->
    isLift #|Γs| #|Δ| A ->
    Σ ;;; Γl ,,, Δ |- rename (strengthen #|Δ| #|Γs|) t : rename (strengthen #|Δ| #|Γs|) A)
   (fun Σ Γ =>
     forall Γl Γs Δ, 
     Γ = Γl ,,, Γs ,,, lift_context #|Γs| 0 Δ ->
     wf_local Σ (Γl ,,, Δ)).
Proof.
  apply typing_ind_env.

  - intros Σ wfΣ Γ wfΓ HΓ.
    intros Γl Γs Δ ->.
    eapply wf_local_app. { clear HΓ. eapply wf_local_app_inv in wfΓ as [wfΓ _].
      now apply wf_local_app_inv in wfΓ as []. }
    apply All_local_env_over_simpl in HΓ.
    apply All_local_env_app_inv in HΓ as [Hl HΔ].
    clear Hl. apply All_local_env_fold in HΔ. clear -HΔ.
    induction HΔ; constructor; firstorder eauto.
    * red. exists x.
      specialize (p _ _ _ eq_refl). rewrite Nat.add_0_r in p.
      specialize (p (isLift_lift _ _ _) ((tSort x); eq_refl)).
      simpl in p. now rewrite strengthen_lift in p.
    * red. exists x.
      specialize (p _ _ _ eq_refl). rewrite Nat.add_0_r in p.
      specialize (p (isLift_lift _ _ _) ((tSort x); eq_refl)).
      simpl in p. now rewrite strengthen_lift in p.
    * red.
      specialize (t1 _ _ _ eq_refl). rewrite Nat.add_0_r in t1.
      specialize (t1 (isLift_lift _ _ _) (isLift_lift _ _ _)).
      simpl in t1. now rewrite !strengthen_lift in t1.
  
  - intros Σ wfΣ Γ wfΓ n decl isdecl ihΓ Γl Γs Δ -> islt isla.
    simpl in *. specialize (ihΓ _ _ _ eq_refl).
    have hf := strengthen_urenaming Γl Γs Δ.
    eapply hf in isdecl as h => //.
    2:{ now apply isLift_rel in islt. }
    destruct h as [decl' [isdecl' [? [h1 h2]]]].
    rewrite lift0_rename rename_compose h1 -lift0_rename.
    econstructor. all:auto.
    rewrite /strengthen_context in isdecl'.
    now rewrite strengthen_lift_ctx in isdecl'.

  - intros Σ wfΣ Γ wfΓ l X H0 ? ? ? -> isl isl'.
    simpl. constructor. all: eauto.

  - intros Σ wfΣ Γ wfΓ na A B s1 s2 X hA ihA hB ihB ? ? ? -> isl isl'.
    rewrite /=. econstructor.
    + eapply ihA; eauto. all: admit.
    + destruct isl. destruct x => //. simpl in e. noconf e.
      specialize (ihB Γl Γs (Δ ,, vass na x1)).
      forward ihB. { now rewrite lift_context_snoc Nat.add_0_r. }
      specialize (ihB (isLift_lift _ _ _) (tSort _; eq_refl)).
      rewrite strengthen_lift.
      simpl in ihB. rewrite shiftn_strengthen. { admit. }
      apply ihB.

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
      rewrite rename_subst_instance. f_equal.
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


Lemma strengthening_wf_local {cf: checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Γ' Γ''} :
  wf_local Σ (Γ ,,, Γ' ,,, lift_context #|Γ'| 0 Γ'') ->
  wf_local Σ (Γ ,,, Γ'').
Proof.
  intros wfΓ'.
  pose proof (env_prop_wf_local _ _ typing_rename_prop _ wfΣ _ wfΓ'). simpl in X.
  eapply All_local_env_app_inv in X as [XΓ XΓ'].
  apply wf_local_app_inv in wfΓ' as [wfΓ wfΓ''].
  apply wf_local_app_inv in wfΓ as [wfΓ wfΓ'].
  apply wf_local_app => //.
  apply All_local_env_fold in XΓ'.
  eapply (All_local_env_impl_ind XΓ').
  intros Δ t [T|] IH; unfold lift_typing; simpl.
  - rewrite -/(lift_context #|Γ'| 0 Δ).
    intros Hf. red.
    rewrite Nat.add_0_r in Hf. rewrite !lift_rename in Hf.
    specialize (Hf (nocc_betweenp #|Δ| #|Γ'|) (Γ ,,, Δ) (strengthen #|Δ| #|Γ'|)).
    forward Hf.
    * split.
      + apply wf_local_app; auto.
      + len. rewrite /shiftnP.
        epose proof (strengthen_urenaming Γ Γ' Δ). simpl in X.
        rewrite /strengthen_context in X.
        rewrite /PCUICRename.shiftnP.

    eapply (Hf (fun x => true)).
    split.
    + apply wf_local_app; auto.
      apply All_local_env_fold in IH. apply IH.
    + apply (weakening_renaming _ Γ Δ Γ'').
  - intros [s Hs]; exists s. red.
    rewrite -/(lift_context #|Γ''| 0 Δ).
    rewrite Nat.add_0_r !lift_rename. 
    apply (Hs (fun _ => true)).
    split.
    + apply wf_local_app; auto.
      apply All_local_env_fold in IH. apply IH.
    + apply (weakening_renaming _ Γ Δ Γ'').
Qed.