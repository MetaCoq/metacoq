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

(** * Weakening lemmas for typing derivations.

  [weakening_*] proves weakening of typing, reduction etc... w.r.t. the *local*
  environment. *)

Set Default Goal Selector "!".
Generalizable Variables Σ Γ t T.

(* FIXME inefficiency in equations: using a very slow "pattern_sigma" to simplify an equality between sigma types *)
Ltac Equations.CoreTactics.destruct_tele_eq H ::= noconf H.

Lemma typed_liftn `{checker_flags} Σ Γ t T n k :
  wf Σ.1 -> wf_local Σ Γ -> k >= #|Γ| ->
  Σ ;;; Γ |- t : T -> lift n k T = T /\ lift n k t = t.
Proof.
  intros wfΣ wfΓ Hk Hty.
  apply typecheck_closed in Hty; eauto.
  destruct Hty as [_ [_ Hcl]].
  rewrite -> andb_and in Hcl. destruct Hcl as [clb clty].
  pose proof (closed_upwards k clb).
  pose proof (closed_upwards k clty).
  simpl in *. forward H0 by lia.
  apply (lift_closed n) in H0.
  simpl in *. forward H1 by lia.
  now apply (lift_closed n) in H1.
Qed.

Lemma closed_ctx_lift n k ctx : closed_ctx ctx -> lift_context n k ctx = ctx.
Proof.
  induction ctx in n, k |- *; auto.
  rewrite closedn_ctx_cons lift_context_snoc0 /snoc.
  move/andb_and => /= [Hctx Hd].
  rewrite IHctx // lift_decl_closed //. now apply: closed_decl_upwards.
Qed.

Lemma weaken_nth_error_ge {Γ Γ' v Γ''} : #|Γ'| <= v ->
  nth_error (Γ ,,, Γ') v =
  nth_error (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') (#|Γ''| + v).
Proof.
  intros Hv.
  rewrite -> !nth_error_app_context_ge, ?lift_context_length.
  - f_equal. lia.
  - rewrite lift_context_length. lia.
  - rewrite lift_context_length. lia.
  - auto.
Qed.

Lemma weaken_nth_error_lt {Γ Γ' Γ'' v} : v < #|Γ'| ->
  nth_error (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') v =
  option_map (lift_decl #|Γ''| (#|Γ'| - S v)) (nth_error (Γ ,,, Γ') v).
Proof.
  simpl. intros Hv.
  rewrite -> !nth_error_app_context_lt.
  - rewrite nth_error_lift_context_eq.
    do 2 f_equal. lia.
  - lia.
  - now rewrite lift_context_length.
Qed.

Lemma lift_context_lift_context n k Γ : lift_context n 0 (lift_context k 0 Γ) =
  lift_context (n + k) 0 Γ.
Proof. rewrite !lift_context_alt.
  rewrite mapi_compose.
  apply mapi_ext.
  intros n' x.
  rewrite /lift_decl compose_map_decl.
  apply map_decl_ext => y.
  rewrite mapi_length; autorewrite with  len.
  rewrite simpl_lift //; lia.
Qed.

Lemma lift_simpl {Γ'' Γ' : context} {i t} :
  i < #|Γ'| ->
  lift0 (S i) (lift #|Γ''| (#|Γ'| - S i) t) = lift #|Γ''| #|Γ'| (lift0 (S i) t).
Proof.
  intros. assert (#|Γ'| = S i + (#|Γ'| - S i)) by easy.
  rewrite -> H0 at 2.
  rewrite permute_lift; try easy.
Qed.


Lemma All_local_env_eq P ctx ctx' :
  All_local_env P ctx -> 
  ctx = ctx' ->
  All_local_env P ctx'.
Proof. now intros H ->. Qed.

Lemma weakening_renaming P Γ Γ' Γ'' :
  urenaming P (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') (Γ ,,, Γ') 
    (lift_renaming #|Γ''| #|Γ'|).
Proof.
  intros i d hpi hnth.
  rewrite /lift_renaming.
  destruct (Nat.leb #|Γ'| i) eqn:leb; [apply Nat.leb_le in leb|eapply Nat.leb_nle in leb].
  - rewrite -weaken_nth_error_ge //.
    exists d; split; auto.
    split; auto.
    split.
    * apply rename_ext => k. rewrite /rshiftk /lift_renaming.
      repeat nat_compare_specs.
    * destruct (decl_body d) => /= //.
      f_equal. apply rename_ext => k. 
      rewrite /rshiftk; now nat_compare_specs.
  - rewrite weaken_nth_error_lt; try lia.
    rewrite hnth /=. eexists. split; [eauto|].
    simpl. rewrite !lift_rename !rename_compose /lift_renaming /rshiftk /=.
    repeat split.
    * apply rename_ext => k. now repeat nat_compare_specs.
    * destruct (decl_body d) => /= //. f_equal.
      rewrite lift_rename rename_compose /lift_renaming.
      apply rename_ext => k. simpl. now repeat nat_compare_specs.
Qed.

Variant lookup_decl_spec Γ Δ i : option context_decl -> Type :=
| lookup_head d : i < #|Δ| ->
  nth_error Δ i = Some d -> lookup_decl_spec Γ Δ i (Some d)
| lookup_tail d : #|Δ| <= i < #|Γ| + #|Δ| ->
  nth_error Γ (i - #|Δ|) = Some d ->
  lookup_decl_spec Γ Δ i (Some d)
| lookup_above : #|Γ| + #|Δ| <= i -> lookup_decl_spec Γ Δ i None.

Lemma lookup_declP Γ Δ i : lookup_decl_spec Γ Δ i (nth_error (Γ ,,, Δ) i).
Proof.
  destruct (Nat.ltb i #|Δ|) eqn:ltb.
  - apply Nat.ltb_lt in ltb.
    rewrite nth_error_app_lt //.
    destruct nth_error eqn:hnth.
    * constructor; auto.
    * apply nth_error_None in hnth. lia.
  - apply Nat.ltb_nlt in ltb.
    rewrite nth_error_app_ge; try lia.
    destruct nth_error eqn:hnth.
    * constructor 2; auto.
      apply nth_error_Some_length in hnth.
      split; lia.
    * constructor. eapply nth_error_None in hnth. lia.
Qed.

#[global]
Hint Rewrite rename_context_length : len.

Variant shiftn_spec k f i : nat -> Type :=
| shiftn_below : i < k -> shiftn_spec k f i i
| shiftn_above : k <= i -> shiftn_spec k f i (k + f (i - k)).

Lemma shiftn_P k f i : shiftn_spec k f i (shiftn k f i).
Proof.
  rewrite /shiftn.
  destruct (Nat.ltb i k) eqn:ltb.
  * apply Nat.ltb_lt in ltb.
    now constructor.
  * apply Nat.ltb_nlt in ltb.
    constructor. lia.
Qed.

Lemma rename_context_lift_context n k Γ :
  rename_context (lift_renaming n k) Γ = lift_context n k Γ.
Proof.
  rewrite /rename_context /lift_context.
  apply fold_context_k_ext => i t.
  now rewrite lift_rename shiftn_lift_renaming.
Qed.

Lemma weakening_wf_local {cf: checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Γ' Γ''} :
  wf_local Σ (Γ ,,, Γ') ->
  wf_local Σ (Γ ,,, Γ'') ->  
  wf_local Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ').
Proof.
  intros wfΓ' wfΓ''.
  pose proof (env_prop_wf_local typing_rename_prop _ wfΣ _ wfΓ') as [_ X]. simpl in X.
  eapply All_local_env_app_inv in X as [XΓ XΓ'].
  apply wf_local_app => //.
  rewrite /lift_context.
  apply All_local_env_fold.
  eapply (All_local_env_impl_ind XΓ').
  intros Δ t [T|] IH; unfold lift_typing; simpl.
  - intros Hf. red. rewrite -/(lift_context #|Γ''| 0 Δ).
    rewrite Nat.add_0_r. rewrite !lift_rename. 
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

Lemma weakening_wf_local_eq {cf: checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Γ' Γ'' n} :
  wf_local Σ (Γ ,,, Γ') ->
  wf_local Σ (Γ ,,, Γ'') ->
  n = #|Γ''| ->
  wf_local Σ (Γ ,,, Γ'' ,,, lift_context n 0 Γ').
Proof.
  intros ? ? ->; now apply weakening_wf_local.
Qed.

Lemma weakening_rename_typing `{cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Γ' Γ''} {t T} :
  wf_local Σ (Γ ,,, Γ'') ->
  Σ ;;; Γ ,,, Γ' |- t : T ->
  Σ ;;; Γ ,,, Γ'' ,,, rename_context (lift_renaming #|Γ''| 0) Γ' |- 
    rename (lift_renaming #|Γ''| #|Γ'|) t : 
    rename (lift_renaming #|Γ''| #|Γ'|) T.
Proof.
  intros wfext Ht.
  eapply (typing_rename); eauto.
  rewrite rename_context_lift_context.
  split.
  - eapply weakening_wf_local; eauto with pcuic.
  - now apply weakening_renaming.
Qed.

Lemma weakening_typing `{cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Γ' Γ''} {t T} :
  wf_local Σ (Γ ,,, Γ'') ->
  Σ ;;; Γ ,,, Γ' |- t : T ->
  Σ ;;; Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ' |- lift #|Γ''| #|Γ'| t : lift #|Γ''| #|Γ'| T.
Proof.
  intros wfext Ht.
  rewrite !lift_rename.
  eapply (typing_rename); eauto.
  split.
  - eapply weakening_wf_local; eauto with pcuic.
  - now apply weakening_renaming.
Qed.

Lemma weakening `{cf : checker_flags} Σ Γ Γ' (t : term) T :
  wf Σ.1 -> wf_local Σ (Γ ,,, Γ') ->
  Σ ;;; Γ |- t : T ->
  Σ ;;; Γ ,,, Γ' |- lift0 #|Γ'| t : lift0 #|Γ'| T.
Proof.
  intros HΣ HΓΓ' * H.
  eapply (weakening_typing (Γ' := [])); eauto.
Qed.

Lemma weaken_wf_local {cf:checker_flags} {Σ Δ} Γ :
  wf Σ.1 ->
  wf_local Σ Γ ->
  wf_local Σ Δ -> wf_local Σ (Γ ,,, Δ).
Proof.
  intros wfΣ wfΓ wfΔ.
  generalize (weakening_wf_local (Γ := []) (Γ'' := Γ) (Γ' := Δ)) => /=.
  rewrite !app_context_nil_l.
  move/(_ wfΔ wfΓ).
  rewrite closed_ctx_lift //.
  now eapply closed_wf_local.
Qed.

Lemma smash_context_lift Δ k n Γ :
  smash_context (lift_context n (k + #|Γ|) Δ) (lift_context n k Γ) =
  lift_context n k (smash_context Δ Γ).
Proof.
  revert Δ. induction Γ as [|[na [b|] ty]]; intros Δ; simpl; auto.
  - now rewrite Nat.add_0_r.
  - rewrite -IHΓ.
    rewrite lift_context_snoc /=. f_equal.
    rewrite !subst_context_alt !lift_context_alt !mapi_compose.
    apply mapi_ext=> n' x.
    destruct x as [na' [b'|] ty']; simpl.
    * rewrite !mapi_length /lift_decl /subst_decl /= /map_decl /=; f_equal.
      + f_equal. rewrite Nat.add_0_r distr_lift_subst_rec /=.
        lia_f_equal.
      + rewrite Nat.add_0_r distr_lift_subst_rec; simpl. lia_f_equal.
    * rewrite !mapi_length /lift_decl /subst_decl /= /map_decl /=; f_equal.
      rewrite Nat.add_0_r distr_lift_subst_rec /=.
      repeat (lia || f_equal).
  - rewrite -IHΓ.
    rewrite lift_context_snoc /= // /lift_decl /subst_decl /map_decl /=.
    f_equal.
    rewrite lift_context_app. simpl.
    rewrite /app_context; lia_f_equal.
    rewrite /lift_context // /fold_context_k /= /map_decl /=.
    now lia_f_equal.
Qed.

Lemma decompose_app_rec_lift n k t l :
  let (f, a) := decompose_app_rec t l in
  decompose_app_rec (lift n k t) (map (lift n k) l)  = (lift n k f, map (lift n k) a).
Proof.
  induction t in k, l |- *; simpl; auto with pcuic.
  - specialize (IHt1 k (t2 :: l)).
    destruct decompose_app_rec. now rewrite IHt1.
Qed.

Lemma decompose_app_lift n k t f a :
  decompose_app t = (f, a) -> decompose_app (lift n k t) = (lift n k f, map (lift n k) a).
Proof.
  generalize (decompose_app_rec_lift n k t []).
  unfold decompose_app. destruct decompose_app_rec.
  now move=> Heq [= <- <-].
Qed.
#[global]
Hint Rewrite decompose_app_lift using auto : lift.

Lemma lift_is_constructor:
  forall (args : list term) (narg : nat) n k,
    is_constructor narg args = true -> is_constructor narg (map (lift n k) args) = true.
Proof.
  intros args narg.
  unfold is_constructor; intros.
  rewrite nth_error_map. destruct nth_error; try discriminate. simpl.
  unfold isConstruct_app in *. destruct decompose_app eqn:Heq.
  eapply decompose_app_lift in Heq as ->.
  destruct t0; try discriminate || reflexivity.
Qed.
#[export] Hint Resolve lift_is_constructor : core.

#[global]
Hint Rewrite subst_instance_lift lift_mkApps distr_lift_subst distr_lift_subst10 : lift.

Lemma lift_declared_constant `{checker_flags} Σ cst decl n k :
  wf Σ ->
  declared_constant Σ cst decl ->
  decl = map_constant_body (lift n k) decl.
Proof.
  intros wf declc.
  rewrite /map_constant_body; destruct decl as [? cst_body ?]; simpl; f_equal; rewrite ?lift_rename.
  - eapply declared_constant_closed_type in declc; eauto.
    now rewrite rename_closed.
  - destruct cst_body eqn:cb => /= //.
    f_equal.
    eapply declared_constant_closed_body in declc; simpl; eauto.
    now rewrite lift_rename rename_closed.
Qed.

Definition lift_mutual_inductive_body n k m :=
  map_mutual_inductive_body (fun k' => lift n (k' + k)) m.

Lemma lift_fix_context:
  forall (mfix : list (def term)) (n k : nat),
    fix_context (map (map_def (lift n k) (lift n (#|mfix| + k))) mfix) = lift_context n k (fix_context mfix).
Proof.
  intros mfix n k. unfold fix_context.
  rewrite PCUICLiftSubst.map_vass_map_def rev_mapi.
  fold (fix_context mfix).
  rewrite (lift_context_alt n k (fix_context mfix)).
  unfold lift_decl. now rewrite mapi_length fix_context_length.
Qed.

#[global]
Hint Rewrite <- lift_fix_context : lift.

Lemma lift_it_mkProd_or_LetIn n k ctx t :
  lift n k (it_mkProd_or_LetIn ctx t) =
  it_mkProd_or_LetIn (lift_context n k ctx) (lift n (length ctx + k) t).
Proof.
  induction ctx in n, k, t |- *; simpl; try congruence.
  pose (lift_context_snoc n k ctx a). unfold snoc in e. rewrite -> e. clear e.
  simpl. rewrite -> IHctx.
  pose (lift_context_snoc n k ctx a).
  now destruct a as [na [b|] ty].
Qed.
#[global]
Hint Rewrite lift_it_mkProd_or_LetIn : lift.

Lemma to_extended_list_map_lift:
  forall (n k : nat) (c : context), to_extended_list c = map (lift n (#|c| + k)) (to_extended_list c).
Proof.
  intros n k c.
  pose proof (to_extended_list_lift_above c). unf_term.
  symmetry. solve_all.
  destruct H as [x' [-> Hx]]. simpl.
  destruct (leb_spec_Set (#|c| + k) x').
  - f_equal. lia.
  - reflexivity.
Qed.



Lemma weakening_red1 `{cf:checker_flags} {Σ} Γ Γ' Γ'' M N :
  wf Σ ->
  on_free_vars xpredT M ->
  red1 Σ (Γ ,,, Γ') M N ->
  red1 Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') (lift #|Γ''| #|Γ'| M) (lift #|Γ''| #|Γ'| N).
Proof.
  intros wfΣ H.
  rewrite !lift_rename.
  eapply red1_rename; eauto.
  eapply weakening_renaming.
Qed.

Lemma weakening_red `{cf:checker_flags} {Σ} {wfΣ : wf Σ} {P Γ Γ' Γ'' M N} :
  on_ctx_free_vars P (Γ ,,, Γ') ->
  on_free_vars P M ->
  red Σ (Γ ,,, Γ') M N ->
  red Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') (lift #|Γ''| #|Γ'| M) (lift #|Γ''| #|Γ'| N).
Proof.
  intros onctx onf; induction 1.
  - constructor. eapply weakening_red1; auto.
    eapply on_free_vars_impl; tea. auto.
  - reflexivity.
  - etransitivity.
    * eapply IHX1 => //.
    * eapply IHX2. eapply red_on_free_vars; tea.
Qed.

Lemma weakening_red' `{cf:checker_flags} {Σ} {wfΣ : wf Σ} {P Γ Γ' Γ'' M N} :
  on_ctx_free_vars P (Γ ,,, Γ') ->
  on_free_vars P M ->
  red Σ (Γ ,,, Γ') M N ->
  red Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') (lift #|Γ''| #|Γ'| M) (lift #|Γ''| #|Γ'| N).
Proof.
  intros onctx onf; induction 1.
  - constructor. eapply weakening_red1; auto.
    eapply on_free_vars_impl; tea. auto.
  - reflexivity.
  - etransitivity.
    * eapply IHX1 => //.
    * eapply IHX2. eapply red_on_free_vars; tea.
Qed.

Lemma weakening_red_0 {cf} {Σ} {wfΣ : wf Σ} {P Γ Γ' M N n} :
  n = #|Γ'| ->
  on_ctx_free_vars P Γ ->
  on_free_vars P M ->
  red Σ Γ M N ->
  red Σ (Γ ,,, Γ') (lift0 n M) (lift0 n N).
Proof. move=> -> onctx ont; eapply (weakening_red (Γ':=[])); tea. Qed.

(* TODO MOVE *)
Lemma fix_context_alt_length :
  forall l,
    #|fix_context_alt l| = #|l|.
Proof.
  intro l.
  unfold fix_context_alt.
  rewrite List.rev_length.
  rewrite mapi_length. reflexivity.
Qed.

Lemma weakening_cumul `{CF:checker_flags} {Σ Γ Γ' Γ'' M N} :
  wf Σ.1 ->
  on_free_vars xpredT M ->
  on_free_vars xpredT N ->
  on_ctx_free_vars xpredT (Γ ,,, Γ') ->
  Σ ;;; Γ ,,, Γ' |- M <= N ->
  Σ ;;; Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ' |- lift #|Γ''| #|Γ'| M <= lift #|Γ''| #|Γ'| N.
Proof.
  intros wfΣ onM onN onctx. induction 1.
  - constructor. now apply lift_leq_term.
  - econstructor 2; eauto.
    * eapply weakening_red1 in r; auto. 1:exact r.
    * eapply IHX; tas.
      eapply red1_on_free_vars; [| |tea]; tea.
  - econstructor 3; eauto.
    * eapply IHX; tas.
      eapply red1_on_free_vars; [| |tea]; tea.
    * eapply weakening_red1 in r; auto. exact r.    
Qed.

Lemma destInd_lift n k t : destInd (lift n k t) = destInd t.
Proof.
  destruct t; simpl; try congruence.
Qed.

(** Variant with more freedom on the length to apply it in backward-chainings. *)
Lemma weakening_length {cf:checker_flags} Σ Γ Γ' t T n :
  wf Σ.1 ->
  n = #|Γ'| ->
  wf_local Σ (Γ ,,, Γ') ->
  Σ ;;; Γ |- t : T ->
  Σ ;;; Γ ,,, Γ' |- (lift0 n) t : (lift0 n) T.
Proof. intros wfΣ ->; now apply weakening. Qed.

Lemma weakening_conv `{cf:checker_flags} :
  forall Σ Γ Γ' Γ'' M N,
    wf Σ.1 ->
    on_free_vars xpredT M ->
    on_free_vars xpredT N ->
    on_ctx_free_vars xpredT (Γ ,,, Γ') ->  
    Σ ;;; Γ ,,, Γ' |- M = N ->
    Σ ;;; Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ' |- lift #|Γ''| #|Γ'| M = lift #|Γ''| #|Γ'| N.
Proof.
  intros Σ Γ Γ' Γ'' M N wfΣ onM onN onctx. induction 1.
  - constructor.
    now apply lift_eq_term.
  - econstructor 2.
    * eapply weakening_red1 in r; auto. 1:exact r.
    * eapply IHX; tas.
      eapply red1_on_free_vars; [| |tea]; tea.
  - econstructor 3.
    * eapply IHX; tas.
      eapply red1_on_free_vars; [| |tea]; tea.
    * eapply weakening_red1 in r; auto. exact r.    
Qed.

Lemma isType_on_free_vars {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ T} : 
  isType Σ Γ T -> on_free_vars xpredT T.
Proof.
  intros [s Hs].
  eapply subject_closed in Hs.
  rewrite closedP_on_free_vars in Hs.
  eapply on_free_vars_impl; tea => //.
Qed.

Lemma isType_on_ctx_free_vars {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ T} : 
  isType Σ Γ T -> on_ctx_free_vars xpredT Γ.
Proof.
  intros [s Hs].
  eapply typing_wf_local in Hs.
  eapply closed_wf_local in Hs; tea.
  eapply (closed_ctx_on_free_vars xpredT) in Hs.
  now eapply on_free_vars_ctx_on_ctx_free_vars_xpredT.
Qed.

Lemma weakening_conv_wt `{cf:checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Γ' Γ'' M N} :
  isType Σ (Γ ,,, Γ') M -> isType Σ (Γ ,,, Γ') N ->
  Σ ;;; Γ ,,, Γ' |- M = N ->
  Σ ;;; Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ' |- lift #|Γ''| #|Γ'| M = lift #|Γ''| #|Γ'| N.
Proof.
  intros onM onN.
  eapply weakening_conv; tea.
  1-2:now eapply isType_on_free_vars.
  now eapply isType_on_ctx_free_vars in onM.
Qed.

Lemma weaken_ctx {cf:checker_flags} {Σ Γ t T} Δ :
  wf Σ.1 -> 
  wf_local Σ Δ ->
  Σ ;;; Γ |- t : T ->
  Σ ;;; Δ ,,, Γ |- t : T.
Proof.
  intros wfΣ wfΔ ty.
  epose proof (weakening_typing (Γ := [])).
  rewrite !app_context_nil_l in X.
  forward X by eauto using typing_wf_local.
  specialize (X ty).
  eapply PCUICClosed.typecheck_closed in ty as [_ [clΓ [clt clT]%andb_and]]; auto.
  rewrite !lift_closed // in X.
  now rewrite closed_ctx_lift in X.
Qed.

Lemma weakening_gen : forall (cf : checker_flags) (Σ : global_env_ext)
  (Γ Γ' : context) (t T : term) n, n = #|Γ'| ->
  wf Σ ->
  wf_local Σ (Γ ,,, Γ') ->
  Σ;;; Γ |- t : T -> Σ;;; Γ ,,, Γ' |- (lift0 n) t : (lift0 n) T.
Proof.
  intros ; subst n; now apply weakening.
Qed.

(** Convenience lemma when going through instantiation for renaming. 
    Δ is arbitrary here, it does not have to be the weakening of some other context. *)
Lemma shift_typing {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ t T n Δ} : 
  Σ ;;; Γ |- t : T ->
  wf_local Σ (Γ ,,, Δ) ->
  n = #|Δ| ->
  Σ ;;; Γ ,,, Δ |- t.[↑^n] : T.[↑^n].
Proof.
  intros ht hΔ ->.
  eapply meta_conv_all. 3-4:now rewrite -rename_inst -lift0_rename.
  2:reflexivity.
  eapply weakening_gen => //.
Qed.

Corollary All_mfix_wf {cf:checker_flags} Σ Γ mfix :
  wf Σ.1 -> wf_local Σ Γ ->
  All (fun d : def term => isType Σ Γ (dtype d)) mfix ->
  wf_local Σ (Γ ,,, fix_context mfix).
Proof.
  move=> wfΣ wf a; move: wf.
  change (fix_context mfix) with (fix_context_gen #|@nil context_decl| mfix).
  change Γ with (Γ ,,, []).
  generalize (@nil context_decl) as Δ.
  rewrite /fix_context_gen.
  intros Δ wfΔ.
  eapply All_local_env_app. split; auto.
  induction a in Δ, wfΔ |- *; simpl; auto.
  + constructor.
  + simpl.
    eapply All_local_env_app. split; auto.
    * repeat constructor.
      simpl.
      destruct p as [s Hs].
      exists s. eapply (weakening Σ Γ Δ _ (tSort s)); auto.
    * specialize (IHa (Δ ,,, [vass (dname x) (lift0 #|Δ| (dtype x))])).
      rewrite app_length in IHa. simpl in IHa.
      forward IHa.
      ** simpl; constructor; auto.
        destruct p as [s Hs].
        exists s. eapply (weakening Σ Γ Δ _ (tSort s)); auto.
      ** eapply All_local_env_impl; eauto.
        simpl; intros.
        rewrite app_context_assoc. apply X.
Qed.

Lemma isType_lift {cf:checker_flags} {Σ : global_env_ext} {n Γ ty} 
  (isdecl : n <= #|Γ|):
  wf Σ -> wf_local Σ Γ ->
  isType Σ (skipn n Γ) ty ->
  isType Σ Γ (lift0 n ty).
Proof.
  intros wfΣ wfΓ wfty. rewrite <- (firstn_skipn n Γ) in wfΓ |- *.
  assert (n = #|firstn n Γ|).
  { rewrite firstn_length_le; auto with arith. }
  destruct wfty as [u Hu]. exists u.
  rewrite {3}H.
  eapply (weakening_typing (Γ := skipn n Γ) (Γ' := []) (Γ'' := firstn n Γ) (T := tSort u)); 
    eauto with wf.
Qed.
