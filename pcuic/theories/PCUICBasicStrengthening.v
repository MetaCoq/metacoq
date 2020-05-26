(* Distributed under the terms of the MIT license.   *)

From Coq Require Import List Arith Lia ssrbool CRelationClasses.
From Equations.Type Require Import Relation Relation_Properties.
From Equations.Prop Require Import DepElim.

From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICEquality PCUICTyping PCUICInduction
     PCUICReduction PCUICPosition PCUICAstUtils PCUICLiftSubst PCUICUnivSubst
     PCUICWeakening PCUICGeneration.

Local Open Scope string_scope.
Import ListNotations. Open Scope list_scope.
Set Asymmetric Patterns.

Set Default Goal Selector "!".


From Equations Require Import Equations Relation.

Derive Signature for red1.
Derive Signature for OnOne2.
Derive Signature for cumul.

Lemma lift_Apps_Ind_inv n k M ind u args
      (H : lift n k M = mkApps (tInd ind u) args)
  : ∑ args', M = mkApps (tInd ind u) args'
             /\ args = map (lift n k) args'.
Proof.
  revert M H. induction args using rev_ind; cbn; intros M H.
  - destruct M; cbn in H; try discriminate.
    exists []. repeat split; tas.
  - rewrite <- mkApps_nested in H; cbn in H.
    destruct M; cbn in H; try discriminate.
    invs H. apply IHargs in H1. destruct H1 as [args' [H1 H2]]; subst.
    exists (args' ++ [M2]). rewrite <- mkApps_nested; cbn.
    rewrite map_app. repeat split.
Qed.

Lemma lift_Apps_Construct_inv n k M ind c u args
      (H : lift n k M = mkApps (tConstruct ind c u) args)
  : ∑ args', M = mkApps (tConstruct ind c u) args'
             /\ args = map (lift n k) args'.
Proof.
  revert M H. induction args using rev_ind; cbn; intros M H.
  - destruct M; cbn in H; try discriminate.
    exists []. repeat split; tas.
  - rewrite <- mkApps_nested in H; cbn in H.
    destruct M; cbn in H; try discriminate.
    invs H. apply IHargs in H1. destruct H1 as [args' [H1 H2]]; subst.
    exists (args' ++ [M2]). rewrite <- mkApps_nested; cbn.
    rewrite map_app. repeat split.
Qed.

Lemma lift_Apps_Fix_inv n k M mfix idx args
      (H : lift n k M = mkApps (tFix mfix idx) args)
  : ∑ mfix' args', M = mkApps (tFix mfix' idx) args'
             /\ mfix = map (map_def (lift n k) (lift n (#|mfix'| + k))) mfix'
             /\ args = map (lift n k) args'.
Proof.
  revert M H. induction args using rev_ind; cbn; intros M H.
  - destruct M; cbn in H; try discriminate.
    invs H. eexists _, []. repeat split; tas.
  - rewrite <- mkApps_nested in H; cbn in H.
    destruct M; cbn in H; try discriminate.
    invs H. apply IHargs in H1.
    destruct H1 as [mfix' [args' [H1 [H2 H3]]]]; subst.
    exists mfix', (args' ++ [M2]). rewrite <- mkApps_nested; cbn.
    rewrite map_app. repeat split; tas.
Qed.

Lemma lift_Apps_CoFix_inv n k M mfix idx args
      (H : lift n k M = mkApps (tCoFix mfix idx) args)
  : ∑ mfix' args', M = mkApps (tCoFix mfix' idx) args'
             /\ mfix = map (map_def (lift n k) (lift n (#|mfix'| + k))) mfix'
             /\ args = map (lift n k) args'.
Proof.
  revert M H. induction args using rev_ind; cbn; intros M H.
  - destruct M; cbn in H; try discriminate.
    invs H. eexists _, []. repeat split; tas.
  - rewrite <- mkApps_nested in H; cbn in H.
    destruct M; cbn in H; try discriminate.
    invs H. apply IHargs in H1.
    destruct H1 as [mfix' [args' [H1 [H2 H3]]]]; subst.
    exists mfix', (args' ++ [M2]). rewrite <- mkApps_nested; cbn.
    rewrite map_app. repeat split; tas.
Qed.
    

(* todo replace in weakening *)
Lemma lift_unfold_fix n k mfix idx :
  unfold_fix (map (map_def (lift n k) (lift n (#|mfix| + k))) mfix) idx
  = option_map (on_snd (lift n k)) (unfold_fix mfix idx).
Proof.
  unfold unfold_fix.
  rewrite nth_error_map. destruct (nth_error mfix idx); cbnr.
  f_equal. rewrite (distr_lift_subst_rec _ _ n 0 k).
  rewrite fix_subst_length. f_equal. cbn. f_equal.
  unfold fix_subst. rewrite !map_length.
  generalize #|mfix| at 2 3. induction n0; auto. simpl.
  f_equal. apply IHn0.
Qed.

Lemma lift_unfold_cofix n k mfix idx :
  unfold_cofix (map (map_def (lift n k) (lift n (#|mfix| + k))) mfix) idx
  = option_map (on_snd (lift n k)) (unfold_cofix mfix idx).
Proof.
  unfold unfold_cofix.
  rewrite nth_error_map. destruct (nth_error mfix idx); cbnr.
  f_equal. unfold on_snd; cbn. f_equal.
  rewrite (distr_lift_subst_rec _ _ n 0 k).
  rewrite cofix_subst_length. f_equal.
  unfold cofix_subst. rewrite !map_length.
  generalize #|mfix| at 2 3. induction n0; auto. simpl.
  f_equal. apply IHn0.
Qed.

Lemma lift_is_constructor args narg n k :
  is_constructor narg args = is_constructor narg (map (lift n k) args).
Proof.
  unfold is_constructor. rewrite nth_error_map.
  destruct nth_error; cbnr.
  unfold isConstruct_app. destruct decompose_app eqn:Heq.
  eapply decompose_app_lift in Heq as ->; cbn.
  destruct t0; cbnr.
Qed.



Lemma red1_strengthening {cf:checker_flags} Σ Γ Γ' Γ'' M N' :
  wf Σ ->
  red1 Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') (lift #|Γ''| #|Γ'| M) N'
  -> ∑ N, red1 Σ (Γ ,,, Γ') M N × N' = lift #|Γ''| #|Γ'| N.
Proof.
  intros HΣ H; dependent induction H using red1_ind_all.
  - destruct M; cbn in H; try discriminate.
    destruct M1; invs H.
    eexists. split.
    { constructor. }
    now rewrite distr_lift_subst10.
  - destruct M; invs H.
    eexists. split.
    { constructor. }
    now rewrite distr_lift_subst10.
  - destruct M; invs H0.
    rewrite <- app_context_assoc in H.
    destruct (leb_spec_Set #|Γ'| n).
    + rewrite nth_error_app_context_ge in H;
        rewrite app_context_length, lift_context_length in *; [|lia].
      eexists. split.
      { constructor. rewrite nth_error_app_context_ge; tas.
        etransitivity; tea. do 2 f_equal. lia. }
      rewrite simpl_lift; try lia.
      f_equal. lia.
    + rewrite nth_error_app_context_lt in H;
        rewrite ?app_context_length, ?lift_context_length in *; [|lia].
      rewrite nth_error_app_context_lt in H;
        rewrite ?app_context_length, ?lift_context_length in *; [|lia].
      rewrite nth_error_lift_context_eq in H.
      case_eq (nth_error Γ' n); [|intro HH; rewrite HH in H; discriminate].
      intros [na [bd|] ty] HH; rewrite HH in H; [|discriminate].
      eexists. split.
      { constructor. rewrite nth_error_app_context_lt; [|lia].
        rewrite HH. reflexivity. }
      clear HH. invs H.
      rewrite permute_lift; [|lia]. f_equal; lia.
  - destruct M; invs H.
    apply lift_Apps_Construct_inv in H3.
    destruct H3 as [args' [H1 H2]]; subst.
    eexists. split.
    { constructor. }
    symmetry; apply lift_iota_red.
  - apply lift_Apps_Fix_inv in H1.
    destruct H1 as [mfix' [args' [H1 [H2 H3]]]]; subst.
    rewrite lift_unfold_fix in H.
    destruct (unfold_fix mfix' idx) as [[]|] eqn:eq; [|discriminate].
    invs H. rewrite <- lift_is_constructor in H0.
    eexists; split.
    { econstructor; tea. }
    symmetry; apply lift_mkApps.
  - destruct M; invs H0.
    apply lift_Apps_CoFix_inv in H4.
    destruct H4 as [mfix' [args' [H1 [H2 H3]]]]; subst.
    rewrite lift_unfold_cofix in H.
    destruct (unfold_cofix mfix' idx) as [[]|] eqn:eq; [|discriminate].
    invs H. eexists; split.
    { econstructor; tea. }
    cbn. f_equal. symmetry; apply lift_mkApps.
  - destruct M; invs H0.
    apply lift_Apps_CoFix_inv in H3.
    destruct H3 as [mfix' [args' [H1 [H2 H3]]]]; subst.
    rewrite lift_unfold_cofix in H.
    destruct (unfold_cofix mfix' idx) as [[]|] eqn:eq; [|discriminate].
    invs H. eexists; split.
    { econstructor; tea. }
    cbn. f_equal. symmetry; apply lift_mkApps.
  - destruct M; invs H1.
    eexists; split.
    { econstructor; tea. }
    rewrite lift_subst_instance_constr.
    f_equal. destruct decl as []; cbn in *; subst.
    eapply lift_declared_constant in H; tas.
    apply (f_equal cst_body) in H; cbn in *.
    apply some_inj in H; eassumption.
  - destruct M; invs H0.
    apply lift_Apps_Construct_inv in H3.
    destruct H3 as [args' [H1 H2]]; subst.
    rewrite nth_error_map in H.
    destruct (nth_error args' (pars + narg)) eqn:X; invs H.
    eexists; split.
    { econstructor; tea. }
    reflexivity.

  - destruct M0; invs H0.
    edestruct IHred1 as [M1' [H1 H2]]; tas; try reflexivity.
    eexists. split.
    { constructor 10; eassumption. }
    cbn; congruence.
  - destruct M0; invs H0.
    edestruct (IHred1 Γ0 (Γ' ,, vass na M0_1)) as [M2' [H1 H2]];
      tas; try reflexivity.
    { rewrite lift_context_snoc. rewrite app_context_cons; f_equal.
      now rewrite Nat.add_0_r. }
    eexists. split.
    { constructor 11; eassumption. }
    cbn in *; congruence.
  - destruct M; invs H0.
    edestruct IHred1 as [M1' [H1 H2]]; tas; try reflexivity.
    eexists. split.
    { constructor 12; eassumption. }
    cbn; congruence.
  - destruct M; invs H0.
    edestruct IHred1 as [M2' [H1 H2]]; tas; try reflexivity.
    eexists. split.
    { constructor 13; eassumption. }
    cbn; congruence.
  - destruct M; invs H0.
    edestruct (IHred1 Γ0 (Γ' ,, vdef na M1 M2)) as [M3' [H1 H2]];
      tas; try reflexivity.
    { rewrite lift_context_snoc. rewrite app_context_cons; f_equal.
      now rewrite Nat.add_0_r. }
    eexists. split.
    { constructor 14; eassumption. }
    cbn in *; congruence.
  - destruct M; invs H0.
    edestruct IHred1 as [M1' [H1 H2]]; tas; try reflexivity.
    eexists. split.
    { constructor 15; eassumption. }
    cbn; congruence.
  - destruct M; invs H0.
    edestruct IHred1 as [M2' [H1 H2]]; tas; try reflexivity.
    eexists. split.
    { constructor 16; eassumption. }
    cbn; congruence.
  - destruct M; invs H.
    assert (XX: ∑ brs,
                OnOne2 (on_Trel_eq (red1 Σ (Γ0 ,,, Γ')) snd fst) brs0 brs
                × brs' = map (on_snd (lift #|Γ''| #|Γ'|)) brs). {
      clear -X HΣ.
      dependent induction X.
      + destruct brs0 as [|[brs0 brs0'] brs1]; invs H.
        destruct p as [[H1 H2] H3].
        edestruct H2 as [N [HN1 HN2]]; tas; try reflexivity.
        exists ((brs0, N) :: brs1). split.
        { constructor; split; tas; reflexivity. }
        destruct hd'; cbn in *; unfold on_snd; cbn. congruence.
      + destruct brs0 as [|[brs0 brs0'] brs1]; invs H.
        edestruct IHX as [N [HN1 HN2]]; tas; try reflexivity.
        eexists; split.
        { constructor 2; eassumption. }
        cbn. congruence. }
    destruct XX as [brs [Hb1 Hb2]].
    eexists. split.
    { constructor 17; eassumption. }
    cbn; congruence.
  - destruct M; invs H0.
    edestruct IHred1 as [M2' [H1 H2]]; tas; try reflexivity.
    eexists. split.
    { constructor 18; eassumption. }
    cbn; congruence.
  - destruct M; invs H0.
    edestruct IHred1 as [M2' [H1 H2]]; tas; try reflexivity.
    eexists. split.
    { constructor 19; eassumption. }
    cbn; congruence.
  - destruct M; invs H0.
    edestruct IHred1 as [M2' [H1 H2]]; tas; try reflexivity.
    eexists. split.
    { constructor 20; eassumption. }
    cbn; congruence.
  - destruct M; invs H0.
    edestruct IHred1 as [M2' [H1 H2]]; tas; try reflexivity.
    eexists. split.
    { constructor 21; eassumption. }
    cbn; congruence.
  - destruct M; invs H0.
    edestruct (IHred1 Γ0 (Γ' ,, vass na M3)) as [M2' [H1 H2]];
      tas; try reflexivity.
    { rewrite lift_context_snoc. rewrite app_context_cons; f_equal.
      now rewrite Nat.add_0_r. }
    eexists. split.
    { constructor 22; eassumption. }
    cbn in *; congruence.
  - destruct M; invs H.
    assert (XX: ∑ l,
                OnOne2 (red1 Σ (Γ0 ,,, Γ')) l0 l
                × l' = map (lift #|Γ''| #|Γ'|) l). {
      clear -X HΣ.
      dependent induction X.
      + destruct l0 as [|l0 l1]; invs H.
        destruct p as [H1 H2].
        edestruct H2 as [N [HN1 HN2]]; tas; try reflexivity.
        exists (N :: l1). split.
        { constructor; assumption. }
        cbn; congruence.
      + destruct l0 as [|l0 l1]; invs H.
        edestruct IHX as [N [HN1 HN2]]; tas; try reflexivity.
        eexists; split.
        { constructor 2; eassumption. }
        cbn; congruence. }
    destruct XX as [l [Hb1 Hb2]].
    eexists. split.
    { constructor 23; eassumption. }
    cbn; congruence.
  - destruct M; invs H.
    assert (XX: ∑ l,
                OnOne2 (fun x y => red1 Σ (Γ0 ,,, Γ') (dtype x) (dtype y)
                  × (dname x, dbody x, rarg x) = (dname y, dbody y, rarg y)) mfix l
                × mfix1 = map (map_def (lift #|Γ''| #|Γ'|)
                                       (lift #|Γ''| (#|mfix| + #|Γ'|))) l). {
      clear -X HΣ.
      set (k := #|mfix|) in *; clearbody k.
      dependent induction X.
      + destruct mfix as [|l0 l1]; invs H.
        destruct p as [[H1 H2] H3].
        edestruct H2 as [N [HN1 HN2]]; tas; try reflexivity.
        destruct l0 as [na ty bd arg]; cbn in *.
        exists ({| dname := na; dtype := N; dbody := bd; rarg := arg |} :: l1). split.
        { constructor; cbn; now split. }
        cbn; f_equal. unfold map_def; destruct hd'; cbn in *. congruence.
      + destruct mfix as [|l0 l1]; invs H.
        edestruct IHX as [N [HN1 HN2]]; tas; try reflexivity.
        eexists; split.
        { constructor 2; eassumption. }
        cbn; congruence. }
    destruct XX as [l [Hb1 Hb2]].
    eexists. split.
    { constructor 24; eassumption. }
    apply OnOne2_length in Hb1.
    cbn; congruence.
  - destruct M; invs H.
    assert (XX: ∑ l, OnOne2 (fun x y =>
     red1 Σ (Γ0 ,,, Γ' ,,, fix_context mfix) (dbody x) (dbody y)
     × (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)) mfix l
     × mfix1 = map (map_def (lift #|Γ''| #|Γ'|)
                            (lift #|Γ''| (#|mfix| + #|Γ'|))) l). {
      clear -X HΣ.
      rewrite lift_fix_context in X.
      pose proof (lift_context_app #|Γ''| 0 Γ' (fix_context mfix)) as e.
      rewrite Nat.add_0_r in e.
      rewrite <- app_context_assoc, <- e in X; clear e.
      (* pose proof (fix_context_length mfix) as Hctx. *)
      rewrite <- (fix_context_length mfix) in *.
      set (ctx := fix_context mfix) in *; clearbody ctx.
      (* set (k := #|mfix|) in *; clearbody k. *)
      dependent induction X.
      + destruct mfix as [|l0 l1]; invs H.
        destruct p as [[H1 H2] H3].
        destruct l0 as [na ty bd arg]; simpl in *.
        edestruct H2 as [N [HN1 HN2]]; tas; try reflexivity.
        { f_equal. f_equal.
          now rewrite app_context_length. }
        exists ({| dname := na; dtype := ty; dbody := N; rarg := arg |} :: l1). split.
        { constructor; simpl; split; try reflexivity.
          now rewrite app_context_assoc in HN1. }
        cbn; f_equal. unfold map_def; destruct hd'; simpl in *.
          rewrite app_context_length in HN2; simpl in HN2.
          congruence.
      + destruct mfix as [|l0 l1]; invs H.
        edestruct IHX as [N [HN1 HN2]]; tas; try reflexivity.
        eexists; split.
        { constructor 2; eassumption. }
        cbn; congruence. }
    destruct XX as [l [Hb1 Hb2]].
    eexists. split.
    { constructor 25; eassumption. }
    apply OnOne2_length in Hb1.
    cbn; congruence.
  - destruct M; invs H.
    assert (XX: ∑ l,
                OnOne2 (fun x y => red1 Σ (Γ0 ,,, Γ') (dtype x) (dtype y)
                  × (dname x, dbody x, rarg x) = (dname y, dbody y, rarg y)) mfix l
                × mfix1 = map (map_def (lift #|Γ''| #|Γ'|)
                                       (lift #|Γ''| (#|mfix| + #|Γ'|))) l). {
      clear -X HΣ.
      set (k := #|mfix|) in *; clearbody k.
      dependent induction X.
      + destruct mfix as [|l0 l1]; invs H.
        destruct p as [[H1 H2] H3].
        edestruct H2 as [N [HN1 HN2]]; tas; try reflexivity.
        destruct l0 as [na ty bd arg]; cbn in *.
        exists ({| dname := na; dtype := N; dbody := bd; rarg := arg |} :: l1). split.
        { constructor; cbn; now split. }
        cbn; f_equal. unfold map_def; destruct hd'; cbn in *. congruence.
      + destruct mfix as [|l0 l1]; invs H.
        edestruct IHX as [N [HN1 HN2]]; tas; try reflexivity.
        eexists; split.
        { constructor 2; eassumption. }
        cbn; congruence. }
    destruct XX as [l [Hb1 Hb2]].
    eexists. split.
    { constructor 26; eassumption. }
    apply OnOne2_length in Hb1.
    cbn; congruence.
  - destruct M; invs H.
    assert (XX: ∑ l, OnOne2 (fun x y =>
     red1 Σ (Γ0 ,,, Γ' ,,, fix_context mfix) (dbody x) (dbody y)
     × (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)) mfix l
     × mfix1 = map (map_def (lift #|Γ''| #|Γ'|)
                            (lift #|Γ''| (#|mfix| + #|Γ'|))) l). {
      clear -X HΣ.
      rewrite lift_fix_context in X.
      pose proof (lift_context_app #|Γ''| 0 Γ' (fix_context mfix)) as e.
      rewrite Nat.add_0_r in e.
      rewrite <- app_context_assoc, <- e in X; clear e.
      (* pose proof (fix_context_length mfix) as Hctx. *)
      rewrite <- (fix_context_length mfix) in *.
      set (ctx := fix_context mfix) in *; clearbody ctx.
      (* set (k := #|mfix|) in *; clearbody k. *)
      dependent induction X.
      + destruct mfix as [|l0 l1]; invs H.
        destruct p as [[H1 H2] H3].
        destruct l0 as [na ty bd arg]; simpl in *.
        edestruct H2 as [N [HN1 HN2]]; tas; try reflexivity.
        { f_equal. f_equal.
          now rewrite app_context_length. }
        exists ({| dname := na; dtype := ty; dbody := N; rarg := arg |} :: l1). split.
        { constructor; simpl; split; try reflexivity.
          now rewrite app_context_assoc in HN1. }
        cbn; f_equal. unfold map_def; destruct hd'; simpl in *.
          rewrite app_context_length in HN2; simpl in HN2.
          congruence.
      + destruct mfix as [|l0 l1]; invs H.
        edestruct IHX as [N [HN1 HN2]]; tas; try reflexivity.
        eexists; split.
        { constructor 2; eassumption. }
        cbn; congruence. }
    destruct XX as [l [Hb1 Hb2]].
    eexists. split.
    { constructor 27; eassumption. }
    apply OnOne2_length in Hb1.
    cbn; congruence.
Qed.


Lemma lift_inj n k t u : lift n k t = lift n k u -> t = u.
Proof.
  revert k u.
  induction t using term_forall_list_ind; cbn;
    intros k uu H; destruct uu; try discriminate; tas; cbn in H; invs H.
  - f_equal.
    destruct (leb_spec_Set k n0); destruct (leb_spec_Set k n1); lia.
  - apply map_inj_All in H2.
    + congruence.
    + eapply All_impl; eauto.
  - now erewrite IHt1, IHt2.
  - now erewrite IHt1, IHt2.
  - now erewrite IHt1, IHt2, IHt3.
  - now erewrite IHt1, IHt2.
  - erewrite IHt1, IHt2; tea. f_equal.
    apply map_inj_All in H4; tas.
    eapply All_impl; tea. intros [] ? [] H; cbn in *.
    injection H; intros; subst. f_equal; eauto.
  - now erewrite IHt.
  - f_equal. assert (e: #|m| = #|mfix|). {
      apply (f_equal (@length _)) in H1.
      now rewrite !map_length in H1. }
    rewrite e in H1; clear e.
    apply map_inj_All in H1; tas.
    eapply All_impl; tea. intros [] [] [] H; cbn in *.
    injection H; intros; subst. f_equal; eauto.
  - f_equal. assert (e: #|m| = #|mfix|). {
      apply (f_equal (@length _)) in H1.
      now rewrite !map_length in H1. }
    rewrite e in H1; clear e.
    apply map_inj_All in H1; tas.
    eapply All_impl; tea. intros [] [] [] H; cbn in *.
    injection H; intros; subst. f_equal; eauto.
Qed.


Lemma red1_strengthening' {cf:checker_flags} Σ Γ Γ' Γ'' M N :
  wf Σ ->
  red1 Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ')
       (lift #|Γ''| #|Γ'| M) (lift #|Γ''| #|Γ'| N)
  -> red1 Σ (Γ ,,, Γ') M N.
Proof.
  intros HΣ H; apply red1_strengthening in H; tas.
  destruct H as [N' [H1 H2]].
  apply lift_inj in H2; now subst.
Qed.

(** This lemma is wrong (if u is in Γ'' and does not appear in t) *)
Lemma subst_lift_inv n k p M t u :
  lift n (p + k) M = subst [u] p t
  -> ∑ t' u', t = lift n (p + 1 + k) t' × u = lift n k u'.
Abort.

(** This lemma is wrong (take M := (λ_:A.t) u with u in Γ'') *)
Lemma red1_strengthening_inv {cf:checker_flags} Σ Γ Γ' Γ'' M N' :
  wf Σ.1 ->
  isWfArity_or_Type Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') N' ->
  red1 Σ.1 (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') N' (lift #|Γ''| #|Γ'| M)
  -> ∑ N, red1 Σ.1 (Γ ,,, Γ') N M × N' = lift #|Γ''| #|Γ'| N.
Abort.


Lemma eq_term_upto_univ_strengthening {cf:checker_flags} Re Rle n k M N' :
  RelationClasses.Reflexive Re
  -> RelationClasses.Reflexive Rle
  -> eq_term_upto_univ Re Rle (lift n k M) N'
  -> ∑ N, eq_term_upto_univ Re Rle M N × N' = lift n k N.
Proof.
  intros HRe HRle H.
  induction M in Rle, HRle, k, N', H |- * using term_forall_list_ind.
  - invs H. eexists; split; try reflexivity.
  - invs H. eexists; split; try reflexivity.
  - invs H.
    assert (∑ args, All2 (eq_term_upto_univ Re Re) l args
                     × args' = map (lift n k) args). {
      induction X in args', X0 |- *.
      - invs X0. exists nil. repeat constructor.
      - invs X0.
        apply p in X1; tas. destruct X1 as [N [XN XN']]; subst.
        apply IHX in X2. destruct X2 as [args [X2 X2']]; subst.
        eexists; split.
        + constructor; tea.
        + reflexivity.
    }
    destruct X1 as [args [H1 H2]]; subst.
    eexists; split; [constructor|]; tea. reflexivity.
  - invs H. eexists; split; [constructor; tea|]; reflexivity.
  - invs H.
    apply IHM1 in X; tas. destruct X as [N1 [H1 H2]]; subst.
    apply IHM2 in X0; tas. destruct X0 as [N2 [H2 H3]]; subst.
    eexists; split; [constructor|]; tea. reflexivity.
  - invs H.
    apply IHM1 in X; tas. destruct X as [N1 [H1 H2]]; subst.
    apply IHM2 in X0; tas. destruct X0 as [N2 [H2 H3]]; subst.
    eexists; split; [constructor|]; tea. reflexivity.
  - invs H.
    apply IHM1 in X; tas. destruct X as [N1 [H1 H2]]; subst.
    apply IHM2 in X0; tas. destruct X0 as [N2 [H2 H3]]; subst.
    apply IHM3 in X1; tas. destruct X1 as [N3 [H3 H4]]; subst.
    eexists; split; [constructor|]; tea. reflexivity.
  - invs H.
    apply IHM1 in X; tas. destruct X as [N1 [H1 H2]]; subst.
    apply IHM2 in X0; tas. destruct X0 as [N2 [H2 H3]]; subst.
    eexists; split; [constructor|]; tea. reflexivity.
  - invs H.
    eexists; split; [constructor|]; tea. reflexivity.
  - invs H.
    eexists; split; [constructor|]; tea. reflexivity.
  - invs H.
    eexists; split; [constructor|]; tea. reflexivity.
  - invs H.
    apply IHM1 in X0; tas. destruct X0 as [N1 [H1 H2]]; subst.
    apply IHM2 in X1; tas. destruct X1 as [N2 [H2 H3]]; subst.
    assert (∑ brs,
            All2 (fun x y => x.1 = y.1 × eq_term_upto_univ Re Re x.2 y.2) l brs
            × brs' = map (on_snd (lift n k)) brs) as XX. {
      clear -X X2 HRe. induction X in brs', X2 |- *.
      - invs X2. exists []. repeat constructor.
      - invs X2. cbn in *. destruct X0 as [X0 X0'].
        apply p in X0'; tas. destruct X0' as [N [XN XN']]; subst.
        apply IHX in X1. destruct X1 as [args [X2 X2']]; subst.
        destruct y as [y1 y2]; cbn in *; subst y2.
        exists ((y1, N) :: args); split.
        + constructor; tas. split; tas.
        + reflexivity.
    }
    destruct XX as [brs [H3 H4]]; subst.
    eexists; split; [constructor|]; tea; reflexivity.
  - invs H.
    apply IHM in X; tas. destruct X as [N1 [H1 H2]]; subst.
    eexists; split; [constructor|]; tea. reflexivity.
  - invs H.
    assert (∑ mfix,
            All2 (fun x y => (eq_term_upto_univ Re Re (dtype x) (dtype y)
                           × eq_term_upto_univ Re Re (dbody x) (dbody y))
                           × rarg x = rarg y) m mfix
                           × mfix' = map (map_def (lift n k) (lift n (#|m| + k)))
                                         mfix) as XX. {
      set #|m| as K in *. clearbody K.
      clear -X X0 HRe. induction X in mfix', X0 |- *.
      - invs X0. exists []. repeat constructor.
      - invs X0. cbn in *. destruct X1 as [[X1 X1'] X1''].
        apply p in X1; tas. destruct X1 as [N [XN XN']].
        apply p in X1'; tas. destruct X1' as [M [XM XM']].
        apply IHX in X2. destruct X2 as [args [X2 X2']]; subst.
        destruct y as [na ty bo arg]; cbn in *; subst bo ty.
        exists ({| dname := na; dtype := N; dbody := M; rarg := arg |} :: args). split.
        + constructor; tas. repeat split; tas.
        + reflexivity.
    }
    destruct XX as [mfix [H3 H4]]; subst.
    eexists; split; [constructor|]; tea; try reflexivity.
    cbn. apply All2_length in H3; now rewrite H3.
  - invs H.
    assert (∑ mfix,
            All2 (fun x y => (eq_term_upto_univ Re Re (dtype x) (dtype y)
                           × eq_term_upto_univ Re Re (dbody x) (dbody y))
                           × rarg x = rarg y) m mfix
                           × mfix' = map (map_def (lift n k) (lift n (#|m| + k)))
                                         mfix) as XX. {
      set #|m| as K in *. clearbody K.
      clear -X X0 HRe. induction X in mfix', X0 |- *.
      - invs X0. exists []. repeat constructor.
      - invs X0. cbn in *. destruct X1 as [[X1 X1'] X1''].
        apply p in X1; tas. destruct X1 as [N [XN XN']].
        apply p in X1'; tas. destruct X1' as [M [XM XM']].
        apply IHX in X2. destruct X2 as [args [X2 X2']]; subst.
        destruct y as [na ty bo arg]; cbn in *; subst bo ty.
        exists ({| dname := na; dtype := N; dbody := M; rarg := arg |} :: args). split.
        + constructor; tas. repeat split; tas.
        + reflexivity.
    }
    destruct XX as [mfix [H3 H4]]; subst.
    eexists; split; [constructor|]; tea; try reflexivity.
    cbn. apply All2_length in H3; now rewrite H3.
Qed.

Lemma eq_term_upto_univ_strengthening_inv {cf:checker_flags} Re Rle n k M' N :
  RelationClasses.Reflexive Re
  -> RelationClasses.Reflexive Rle
  -> eq_term_upto_univ Re Rle M' (lift n k N)
  -> ∑ M, eq_term_upto_univ Re Rle M N × M' = lift n k M.
Proof.
  intros HRe HRle H.
  induction N in Rle, HRle, k, M', H |- * using term_forall_list_ind.
  - invs H. eexists; split; try reflexivity.
  - invs H. eexists; split; try reflexivity.
  - invs H.
    assert (∑ args0, All2 (eq_term_upto_univ Re Re) args0 l
                     × args = map (lift n k) args0). {
      induction X in args, X0 |- *.
      - invs X0. exists nil. repeat constructor.
      - invs X0.
        apply p in X1; tas. destruct X1 as [N [XN XN']]; subst.
        apply IHX in X2. destruct X2 as [args [X2 X2']]; subst.
        eexists; split.
        + constructor; tea.
        + reflexivity.
    }
    destruct X1 as [args0 [H1 H2]]; subst.
    eexists; split; [constructor|]; tea. reflexivity.
  - invs H. eexists; split; [constructor; tea|]; reflexivity.
  - invs H.
    apply IHN1 in X; tas. destruct X as [M1 [H1 H2]]; subst.
    apply IHN2 in X0; tas. destruct X0 as [M2 [H2 H3]]; subst.
    eexists; split; [constructor|]; tea. reflexivity.
  - invs H.
    apply IHN1 in X; tas. destruct X as [M1 [H1 H2]]; subst.
    apply IHN2 in X0; tas. destruct X0 as [M2 [H2 H3]]; subst.
    eexists; split; [constructor|]; tea. reflexivity.
  - invs H.
    apply IHN1 in X; tas. destruct X as [M1 [H1 H2]]; subst.
    apply IHN2 in X0; tas. destruct X0 as [M2 [H2 H3]]; subst.
    apply IHN3 in X1; tas. destruct X1 as [M3 [H3 H4]]; subst.
    eexists; split; [constructor|]; tea. reflexivity.
  - invs H.
    apply IHN1 in X; tas. destruct X as [M1 [H1 H2]]; subst.
    apply IHN2 in X0; tas. destruct X0 as [M2 [H2 H3]]; subst.
    eexists; split; [constructor|]; tea. reflexivity.
  - invs H.
    eexists; split; [constructor|]; tea. reflexivity.
  - invs H.
    eexists; split; [constructor|]; tea. reflexivity.
  - invs H.
    eexists; split; [constructor|]; tea. reflexivity.
  - invs H.
    apply IHN1 in X0; tas. destruct X0 as [M1 [H1 H2]]; subst.
    apply IHN2 in X1; tas. destruct X1 as [M2 [H2 H3]]; subst.
    assert (∑ brs0,
            All2 (fun x y => x.1 = y.1 × eq_term_upto_univ Re Re x.2 y.2) brs0 l
            × brs = map (on_snd (lift n k)) brs0) as XX. {
      clear -X X2 HRe. induction X in brs, X2 |- *.
      - invs X2. exists []. repeat constructor.
      - invs X2. cbn in *. destruct X0 as [X0 X0'].
        apply p in X0'; tas. destruct X0' as [N [XN XN']]; subst.
        apply IHX in X1. destruct X1 as [args [X2 X2']]; subst.
        destruct x0 as [y1 y2]; cbn in *; subst y2.
        exists ((y1, N) :: args); split.
        + constructor; tas. split; tas.
        + reflexivity.
    }
    destruct XX as [brs0 [H3 H4]]; subst.
    eexists; split; [constructor|]; tea; reflexivity.
  - invs H.
    apply IHN in X; tas. destruct X as [N1 [H1 H2]]; subst.
    eexists; split; [constructor|]; tea. reflexivity.
  - invs H.
    assert (∑ mfix0,
            All2 (fun x y => (eq_term_upto_univ Re Re (dtype x) (dtype y)
                           × eq_term_upto_univ Re Re (dbody x) (dbody y))
                           × rarg x = rarg y) mfix0 m
                           × mfix = map (map_def (lift n k) (lift n (#|m| + k)))
                                         mfix0) as XX. {
      set #|m| as K in *. clearbody K.
      clear -X X0 HRe. induction X in mfix, X0 |- *.
      - invs X0. exists []. repeat constructor.
      - invs X0. cbn in *. destruct X1 as [[X1 X1'] X1''].
        apply p in X1; tas. destruct X1 as [N [XN XN']].
        apply p in X1'; tas. destruct X1' as [M [XM XM']].
        apply IHX in X2. destruct X2 as [args [X2 X2']]; subst.
        destruct x0 as [na ty bo arg]; cbn in *; subst bo ty.
        exists ({| dname := na; dtype := N; dbody := M; rarg := arg |} :: args). split.
        + constructor; tas. repeat split; tas.
        + reflexivity.
    }
    destruct XX as [mfix0 [H3 H4]]; subst.
    eexists; split; [constructor|]; tea; try reflexivity.
    cbn. apply All2_length in H3; now rewrite H3.
  - invs H.
    assert (∑ mfix0,
            All2 (fun x y => (eq_term_upto_univ Re Re (dtype x) (dtype y)
                           × eq_term_upto_univ Re Re (dbody x) (dbody y))
                           × rarg x = rarg y) mfix0 m
                           × mfix = map (map_def (lift n k) (lift n (#|m| + k)))
                                         mfix0) as XX. {
      set #|m| as K in *. clearbody K.
      clear -X X0 HRe. induction X in mfix, X0 |- *.
      - invs X0. exists []. repeat constructor.
      - invs X0. cbn in *. destruct X1 as [[X1 X1'] X1''].
        apply p in X1; tas. destruct X1 as [N [XN XN']].
        apply p in X1'; tas. destruct X1' as [M [XM XM']].
        apply IHX in X2. destruct X2 as [args [X2 X2']]; subst.
        destruct x0 as [na ty bo arg]; cbn in *; subst bo ty.
        exists ({| dname := na; dtype := N; dbody := M; rarg := arg |} :: args). split.
        + constructor; tas. repeat split; tas.
        + reflexivity.
    }
    destruct XX as [mfix0 [H3 H4]]; subst.
    eexists; split; [constructor|]; tea; try reflexivity.
    cbn. apply All2_length in H3; now rewrite H3.
Qed.

Lemma eq_term_upto_univ_strengthening' {cf:checker_flags} Re Rle n k M N :
  RelationClasses.Reflexive Re
  -> RelationClasses.Reflexive Rle
  -> eq_term_upto_univ Re Rle (lift n k M) (lift n k N)
  -> eq_term_upto_univ Re Rle M N.
Proof.
  intros Hre Hrle H; apply eq_term_upto_univ_strengthening in H; tas.
  destruct H as [N' [H1 H2]].
  apply lift_inj in H2; now subst.
Qed.


Lemma stack_context_lift_length n k π :
  #|stack_context (lift_stack n k π)| = #|stack_context π|.
Proof.
  induction π; try (cbn; auto; fail).
  simpl. rewrite !app_context_length, IHπ; f_equal.
  rewrite !fix_context_alt_length, !app_length; cbn.
  now rewrite !map_length.
Qed.


Tactic Notation "sap" uconstr(t) := (apply t || symmetry; apply t).
Tactic Notation "sap" uconstr(t) "in" ident(H)
  := (apply t in H || symmetry in H; apply t in H).


Lemma map_app_inv {A B} (f : A -> B) l1 l2 l :
  map f l = l1 ++ l2 -> ∑ l1' l2', l1 = map f l1' /\ l2 = map f l2' /\ l = l1' ++ l2'.
Proof.
  induction l1 in l |- *; intro HH.
  - exists [], l; repeat split; auto.
  - destruct l; invs HH. apply IHl1 in H1.
    destruct H1 as [l1' [l2' [? [? ?]]]].
    exists (a0 :: l1'), l2'. repeat split; cbn; congruence.
Defined.


Lemma lift_zipc_inv n k M t π :
  lift n k M = zipc t π
  -> ∑ t' π', M = zipc t' π'
             /\ t = lift n (#|stack_context π| + k) t'
             /\ π = lift_stack n k π'.
Proof.
  induction π in M, t |- *; cbn; intro HH.
  - exists M, Empty. repeat split; auto.
  - apply IHπ in HH. destruct HH as [t' [π' [H1 [H2 H3]]]]; subst.
    destruct t'; invs H2.
    exists t'1, (App t'2 π'). rewrite stack_context_lift_length.
    repeat split.
  - apply IHπ in HH. destruct HH as [t' [π' [H1 [H2 H3]]]]; subst.
    destruct t'; invs H2.
    sap lift_Apps_Fix_inv in H0.
    destruct H0 as [mfix' [args' [H1 [H2 H3]]]]; subst.
    eexists t'2, (Fix _ _ _ π'). rewrite stack_context_lift_length.
    repeat split.
  - apply IHπ in HH. destruct HH as [t' [π' [H1 [H2 H3]]]]; subst.
    destruct t'; invs H2.
    sap map_app_inv in H0. destruct H0 as [l1' [l2' [H1 [H2 H3]]]].
    destruct l2'; invs H2.
    destruct d as [na ty bo arg]; cbn in *.
    exists ty, (Fix_mfix_ty na bo arg l1' l2' idx π').
    repeat split.
    now rewrite stack_context_lift_length, app_length.
  - apply IHπ in HH. destruct HH as [t' [π' [H1 [H2 H3]]]]; subst.
    destruct t'; invs H2.
    sap map_app_inv in H0. destruct H0 as [l1' [l2' [H1 [H2 H3]]]].
    destruct l2'; invs H2.
    destruct d as [na ty bo arg]; cbn in *.
    exists bo, (Fix_mfix_bd na ty arg l1' l2' idx π').
    rewrite !stack_context_lift_length, !app_length. repeat split.
    rewrite app_context_length, fix_context_alt_length.
    rewrite app_length; cbn.
    now rewrite !map_length, stack_context_lift_length.
  - apply IHπ in HH. destruct HH as [t' [π' [H1 [H2 H3]]]]; subst.
    destruct t'; invs H2.
    sap lift_Apps_CoFix_inv in H0.
    destruct H0 as [mfix' [args' [H1 [H2 H3]]]]; subst.
    eexists t'2, (CoFix _ _ _ π'). rewrite stack_context_lift_length.
    repeat split.
  - apply IHπ in HH. destruct HH as [t' [π' [H1 [H2 H3]]]]; subst.
    destruct t'; invs H2.
    exists t'1, (Case_p indn0 t'2 brs0 π'). rewrite stack_context_lift_length.
    repeat split.
  - apply IHπ in HH. destruct HH as [t' [π' [H1 [H2 H3]]]]; subst.
    destruct t'; invs H2.
    exists t'2, (Case indn0 t'1 brs0 π'). rewrite stack_context_lift_length.
    repeat split.
  - apply IHπ in HH. destruct HH as [t' [π' [H1 [H2 H3]]]]; subst.
    destruct t'; invs H2.
    sap map_app_inv in H4. destruct H4 as [l1' [l2' [H1 [H2 H3]]]].
    destruct l2'; invs H2.
    destruct p as [p1 p2]; cbn in *.
    exists p2, (Case_brs indn0 t'1 t'2 p1 l1' l2' π'). rewrite stack_context_lift_length.
    repeat split.
  - apply IHπ in HH. destruct HH as [t' [π' [H1 [H2 H3]]]]; subst.
    destruct t'; invs H2.
    exists t', (Proj p0 π'). rewrite stack_context_lift_length.
    repeat split.
  - apply IHπ in HH. destruct HH as [t' [π' [H1 [H2 H3]]]]; subst.
    destruct t'; invs H2.
    exists t'1, (Prod_l na0 t'2 π'). rewrite stack_context_lift_length.
    repeat split.
  - apply IHπ in HH. destruct HH as [t' [π' [H1 [H2 H3]]]]; subst.
    destruct t'; invs H2.
    exists t'2, (Prod_r na0 t'1 π'). rewrite stack_context_lift_length.
    repeat split.
  - apply IHπ in HH. destruct HH as [t' [π' [H1 [H2 H3]]]]; subst.
    destruct t'; invs H2.
    exists t'1, (Lambda_ty na0 t'2 π'). rewrite stack_context_lift_length.
    repeat split.
  - apply IHπ in HH. destruct HH as [t' [π' [H1 [H2 H3]]]]; subst.
    destruct t'; invs H2.
    exists t'2, (Lambda_tm na0 t'1 π'). rewrite stack_context_lift_length.
    repeat split.
  - apply IHπ in HH. destruct HH as [t' [π' [H1 [H2 H3]]]]; subst.
    destruct t'; invs H2.
    exists t'1, (LetIn_bd na0 t'2 t'3 π'). rewrite stack_context_lift_length.
    repeat split.
  - apply IHπ in HH. destruct HH as [t' [π' [H1 [H2 H3]]]]; subst.
    destruct t'; invs H2.
    exists t'2, (LetIn_ty na0 t'1 t'3 π'). rewrite stack_context_lift_length.
    repeat split.
  - apply IHπ in HH. destruct HH as [t' [π' [H1 [H2 H3]]]]; subst.
    destruct t'; invs H2.
    exists t'3, (LetIn_in na0 t'1 t'2 π'). rewrite stack_context_lift_length.
    repeat split.
  - apply IHπ in HH. destruct HH as [t' [π' [H1 [H2 H3]]]]; subst.
    destruct t'; invs H2.
    exists t'2, (coApp t'1 π'). rewrite stack_context_lift_length.
    repeat split.
Defined.


Lemma lift_lift_inv n k p M N :
  p <= k -> lift 1 p M = lift n (S k) N
  -> ∑ N', N = lift 1 p N'.
Proof.
  intros Hle HH; induction M in p, k, Hle, N, HH |- * using term_forall_list_ind;
    destruct N; invs HH.
  - destruct (leb_spec_Set (S k) n1).
    + destruct n1; [lia|].
      eexists (tRel n1); cbn.
      destruct (leb_spec_Set p n1); [reflexivity|lia].
    + subst. exists (tRel n0). reflexivity.
  - eexists (tVar _); reflexivity.
  - assert (∑ l, l0 = map (lift 1 p) l) as XX. {
      induction X in l0, H1 |- *; destruct l0; invs H1.
      - now exists [].
      - apply IHX in H2. destruct H2 as [l' Hl']; subst.
        apply p0 in H0; tas. destruct H0 as [t' Ht']; subst.
        now exists (t' :: l').
    }
    destruct XX as [l' Hl']; subst.
    now exists (tEvar n1 l').
  - eexists (tSort _); reflexivity.
  - apply IHM1 in H1 as [M1' ?]; tas; subst.
    apply IHM2 in H2 as [M2' ?]; try lia; subst.
    now exists (tProd na M1' M2').
  - apply IHM1 in H1 as [M1' ?]; tas; subst.
    apply IHM2 in H2 as [M2' ?]; try lia; subst.
    now exists (tLambda na M1' M2').
  - apply IHM1 in H1 as [M1' ?]; tas; subst.
    apply IHM2 in H2 as [M2' ?]; try lia; subst.
    apply IHM3 in H3 as [M3' ?]; try lia; subst.
    now exists (tLetIn na M1' M2' M3').
  - apply IHM1 in H0 as [M1' ?]; tas; subst.
    apply IHM2 in H1 as [M2' ?]; try lia; subst.
    now exists (tApp M1' M2').
  - eexists (tConst _ _); reflexivity.
  - eexists (tInd _ _); reflexivity.
  - eexists (tConstruct _ _ _); reflexivity.
  - assert (∑ l', brs = map (on_snd (lift 1 p)) l') as XX. {
      clear -Hle X H3. induction X in brs, H3 |- *; destruct brs; invs H3.
      - now exists [].
      - apply IHX in H2. destruct H2 as [l' Hl']; subst.
        apply p0 in H1; tas. destruct H1 as [t' Ht']; subst.
        exists ((x.1, t') :: l'). cbn. f_equal.
        destruct p1; unfold on_snd; cbn in *; congruence.
    }
    destruct XX as [l' Hl']; subst.
    apply IHM1 in H1 as [M1' ?]; tas; subst.
    apply IHM2 in H2 as [M2' ?]; try lia; subst.
    now exists (tCase indn M1' M2' l').
  - apply IHM in H1 as [M1' ?]; tas; subst.
    now exists (tProj p0 M1').
  - assert (#|m| = #|mfix|) as e. {
      apply (f_equal (@length _)) in H0.
      now rewrite !map_length in H0.
    }
    assert (∑ l', mfix = map (map_def (lift 1 p) (lift 1 (#|m| + p))) l') as XX. {
      rewrite e in *; clear e.
      set #|mfix| as K in *; clearbody K.
      clear -Hle X H0. induction X in mfix, H0 |- *; destruct mfix; invs H0.
      - now exists [].
      - apply IHX in H5. destruct H5 as [l' Hl']; subst.
        apply p0 in H2; tas. destruct H2 as [t' Ht']; subst.
        rewrite Nat.add_succ_r in H3.
        apply p0 in H3; try lia. destruct H3 as [u' Hu']; subst.
        destruct d as [na ty bo arg].
        exists ({| dname := na; dtype := t'; dbody := u'; rarg := arg |} :: l').
        cbn. f_equal. unfold map_def; cbn in *; now f_equal. }
    destruct XX as [l' Hl']; subst.
    exists (tFix l' idx). cbn. do 5 f_equal.
    now rewrite map_length in e.
  - assert (#|m| = #|mfix|) as e. {
      apply (f_equal (@length _)) in H0.
      now rewrite !map_length in H0.
    }
    assert (∑ l', mfix = map (map_def (lift 1 p) (lift 1 (#|m| + p))) l') as XX. {
      rewrite e in *; clear e.
      set #|mfix| as K in *; clearbody K.
      clear -Hle X H0. induction X in mfix, H0 |- *; destruct mfix; invs H0.
      - now exists [].
      - apply IHX in H5. destruct H5 as [l' Hl']; subst.
        apply p0 in H2; tas. destruct H2 as [t' Ht']; subst.
        rewrite Nat.add_succ_r in H3.
        apply p0 in H3; try lia. destruct H3 as [u' Hu']; subst.
        destruct d as [na ty bo arg].
        exists ({| dname := na; dtype := t'; dbody := u'; rarg := arg |} :: l').
        cbn. f_equal. unfold map_def; cbn in *; now f_equal. }
    destruct XX as [l' Hl']; subst.
    exists (tCoFix l' idx). cbn. do 5 f_equal.
    now rewrite map_length in e.
Qed.

Lemma lift_lift_inv0 n k M N :
  lift0 1 M = lift n (S k) N
  -> ∑ N', N = lift0 1 N'.
Proof.
  intro H. now apply lift_lift_inv in H.
Qed.


Lemma eta_strengthening n k M N' :
  eta (lift n k M) N'
  -> ∑ N, eta M N × N' = lift n k N.
Proof.
Admitted.

(** This lemma is wrong *)
Lemma eta_strengthening_inv n k M' N :
  eta M' (lift n k N)
  -> ∑ M, eta M N × M' = lift n k M.
Abort.


Lemma cumul_strengthening {cf:checker_flags} Σ Γ Γ' Γ'' M N' :
  wf Σ.1 ->
  isWfArity_or_Type Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') N' ->
  Σ ;;; Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ' |- lift #|Γ''| #|Γ'| M <= N'
  -> ∑ N, Σ;;; Γ ,,,  Γ' |- M <= N × N' = lift #|Γ''| #|Γ'| N.
Proof.
  intros HΣ Z H; dependent induction H.
  - apply eq_term_upto_univ_strengthening in l; try exact _.
    destruct l as [N [H1 H2]]; subst.
    (* eexists; split; [|reflexivity]. now constructor. *)
    admit.
  - apply red1_strengthening in r; tas.
    destruct r as [N [H1 H2]]; subst.
    edestruct IHcumul as [? [? ?]]; tas; try reflexivity; tas; subst.
    eexists; split; [econstructor 2; eassumption|]. reflexivity.
  - destruct IHcumul as [N [H1 H2]]; tas; subst.
    1: admit. (* SR ! *)
    eexists; split; [econstructor 3; tea|].
    (* We don't have red1_strengthening_inv *)
Abort.

Lemma cumul_strengthening_inv {cf:checker_flags} Σ Γ Γ' Γ'' M' N :
  wf Σ.1 ->
  isWfArity_or_Type Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') M' ->
  Σ ;;; Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ' |- M' <= lift #|Γ''| #|Γ'| N
  -> ∑ M, Σ;;; Γ ,,,  Γ' |- M <= N × M' = lift #|Γ''| #|Γ'| M.
Abort.


Lemma cumul_strengthening' {cf:checker_flags} Σ Γ Γ' Γ'' M N :
  wf Σ.1 ->
  Σ ;;; Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ'
                                   |- lift #|Γ''| #|Γ'| M <= lift #|Γ''| #|Γ'| N
  -> Σ;;; Γ ,,,  Γ' |- M <= N.
Proof.
  intros HΣ H; dependent induction H.
  - 
    (* apply eq_term_upto_univ_strengthening' in l; try exact _. *)
    (* now constructor. *)
    admit.
  - apply red1_strengthening in r; tas.
    destruct r as [N' [H1 H2]]; subst.
    econstructor 2; tea. now apply IHcumul.
  - apply red1_strengthening in r; tas.
    destruct r as [N' [H1 H2]]; subst.
    econstructor 3; tea. now eapply IHcumul.
  - econstructor 4. 2: eapply IHcumul; tas. all: admit.
  - econstructor 5. 1: eapply IHcumul; tas. all: admit.
    (* In both cases we don't have eta_strengthening *)
Abort.


Lemma strengthening' {cf:checker_flags} {Σ Γ Γ' Γ'' t A} :
  wf Σ.1 ->
  Σ ;;; Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ'
                              |- lift #|Γ''| #|Γ'| t : lift #|Γ''| #|Γ'|A ->
  Σ;;; Γ ,,, Γ' |- t : A.
Proof.
  intros HΣ H.
  simple refine (let X := typing_ind_env
    (fun Σ Γ1 t1 A1 => forall Γ' A t, Γ1 = Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ'
                          -> t1 = lift #|Γ''| #|Γ'| t
                          -> A1 = lift #|Γ''| #|Γ'| A
                          -> Σ;;; Γ ,,, Γ' |- t : A)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ in _).
  1-15: cbn; clear; intros.
  1-14: admit.
  - subst. econstructor.
    (* + apply X1; try reflexivity. *)
      (* We need cumul_strengthening_inv *)
Abort.
