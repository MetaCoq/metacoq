(* Distributed under the terms of the MIT license. *)
From Coq Require Import Morphisms.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICInduction
  PCUICLiftSubst PCUICUnivSubst PCUICEquality PCUICTyping PCUICWeakeningEnv
  PCUICClosed PCUICReduction PCUICPosition PCUICGeneration
  PCUICSigmaCalculus PCUICRename.

Require Import ssreflect.
From Equations Require Import Equations.

Implicit Types cf : checker_flags.

(** * Weakening lemmas for typing derivations.

  [weakening_*] proves weakening of typing, reduction etc... w.r.t. the *local*
  environment. *)


Set Default Goal Selector "!".
Generalizable Variables Σ Γ t T.

Derive Signature NoConfusion for All_local_env.
Derive Signature for All_local_env_over.

(* FIXME inefficiency in equations: using a very slow "pattern_sigma" to simplify an equality between sigma types *)
Ltac Equations.CoreTactics.destruct_tele_eq H ::= noconf H.

(* Derive Signature NoConfusion for All_local_env. *)
Derive NoConfusion for All_local_env_over.
Derive NoConfusion for context_decl.

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
  unfold closed_ctx, id. simpl.
  rewrite alli_app List.rev_length /= lift_context_snoc0 /snoc Nat.add_0_r.
  move/andb_and => /= [Hctx /andb_and [Ha _]].
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

Lemma All_local_env_eq P ctx ctx' :
  All_local_env P ctx -> 
  ctx = ctx' ->
  All_local_env P ctx'.
Proof. now intros H ->. Qed.

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


Lemma weakening_renaming Γ Γ' Γ'' :
  urenaming (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') (Γ ,,, Γ') 
    (lift_renaming #|Γ''| #|Γ'|).
Proof.
  intros i d hnth.
  unfold lift_renaming.
  destruct (Nat.leb #|Γ'| i) eqn:leb; [apply Nat.leb_le in leb|eapply Nat.leb_nle in leb].
  - rewrite -weaken_nth_error_ge //.
    exists d; split; auto.
    rewrite !lift_rename rename_compose /=.
    rewrite /lift_renaming /=.
    split.
    * apply rename_ext => k. now nat_compare_specs.
    * intros b db. exists b. split => //.
      rewrite !lift_rename rename_compose /=.
      apply rename_ext => k. rewrite /lift_renaming /=.
      now nat_compare_specs.
  - rewrite weaken_nth_error_lt; try lia.
    rewrite hnth /=. eexists. split; [eauto|].
    simpl. rewrite !lift_rename !rename_compose /lift_renaming /=.
    split.
    * apply rename_ext => k. now repeat nat_compare_specs.
    * move=> b -> /=. eexists; split; eauto.
      rewrite !lift_rename !rename_compose /lift_renaming.
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

Hint Rewrite rename_context_length : len.

Variant shiftn_spec k f i : nat -> Type :=
| shiftn_below : i < k -> shiftn_spec k f i i
| shiftn_above : k <= i -> shiftn_spec k f i (k + f (i - k)).

Lemma shiftnP k f i : shiftn_spec k f i (shiftn k f i).
Proof.
  rewrite /shiftn.
  destruct (Nat.ltb i k) eqn:ltb.
  * apply Nat.ltb_lt in ltb.
    now constructor.
  * apply Nat.ltb_nlt in ltb.
    constructor. lia.
Qed.

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

Lemma strenghten_urenaming Γ Γs Δ :
  noccur_between_ctx 0 #|Γs| Δ ->
  urenaming
    (Γ ,,, rename_context (strengthen 0 #|Γs|) Δ)
    (Γ ,,, Γs ,,, Δ)
    (strengthen #|Δ| #|Γs|).
Proof.
  intros nocc i d hnth.
  rewrite lookup_exchange_contexts hnth => /=.
  eexists; split; eauto.
  pose proof (exchange_lift_rename nocc hnth).
  rewrite !lift_rename !rename_compose /lift_renaming /=. 
  destruct d as [na [b|] ty]; noconf H; simpl in *.
  - split => //.
    intros ? [= <-]. eexists; split => //.
    rewrite !lift_rename !rename_compose.
    rewrite /lift_renaming /= //. 
  - split => //.
Qed.


(* l, r, p -> r, l, p *)
Definition exchange_renaming l r p :=
  fun i => 
    if p <=? i then
      if p + r <=? i then
        if p + r + l <=? i then i
        else i - r
      else i + l
    else i.

Variant exchange_renaming_spec l r p i : nat -> Type :=
| exch_below : i < p -> exchange_renaming_spec l r p i i
| exch_right : p <= i < p + r -> exchange_renaming_spec l r p i (i + l)
| exch_left : p + r <= i < p + r + l -> exchange_renaming_spec l r p i (i - r)
| exch_above : p + r + l <= i -> exchange_renaming_spec l r p i i.

Lemma exchange_renamingP l r p i : 
  exchange_renaming_spec l r p i (exchange_renaming l r p i).
Proof.
  unfold exchange_renaming.
  case: leb_spec_Set; [|constructor; auto].
  elim: leb_spec_Set; [|constructor; auto].
  elim: leb_spec_Set; [|constructor; auto].
  intros.
  constructor 4; auto.
Qed.

Lemma shiftn_exchange_renaming n l r p : 
  shiftn n (exchange_renaming l r p) =1 
  exchange_renaming l r (n + p).
Proof.
  intros i.
  case: exchange_renamingP.
  * case: shiftnP; try lia.
    case: exchange_renamingP; lia.
  * case: shiftnP; try lia.
    case: exchange_renamingP; lia.
  * case: shiftnP; try lia.
    case: exchange_renamingP; lia.
  * case: shiftnP; try lia.
    case: exchange_renamingP; lia.
Qed.

Lemma exchange_renaming_lift_renaming l r p i k :
  i < p ->
  exchange_renaming l r p (lift_renaming (S i) 0 k) =
  lift_renaming (S i) 0
    (shiftn (p - S i) (exchange_renaming l r 0) k).
Proof.
  intros ip.
  rewrite shiftn_exchange_renaming.
  rewrite /lift_renaming /=.
  case: exchange_renamingP; try lia; intros Hp.
  all: case: exchange_renamingP; lia.
Qed.

Definition exchange_contexts Γ Γl Γr Δ :=
  (Γ ,,, rename_context (strengthen 0 #|Γl|) Γr ,,, 
  rename_context (lift_renaming #|Γr| 0) Γl ,,, 
  rename_context (exchange_renaming #|Γl| #|Γr| 0) Δ).

Definition exchange_rename Γl Γr Δ i :=
  if Δ <=? i then
    if Δ + Γr <=? i then
      if Δ + Γr + Γl <=? i then ren_id
      else (lift_renaming Γr (Γl - S (i - Γr - Δ)))
    else (shiftn (Γr - S (i - Δ)) (strengthen 0 Γl))
  else (exchange_renaming Γl Γr (Δ - S i)).

Lemma map_decl_id : map_decl id =1 id.
Proof. intros d; now destruct d as [? [] ?]. Qed.

Instance option_map_ext {A B} : Proper (`=1` ==> Logic.eq ==> Logic.eq) (@option_map A B).
Proof.
  intros f g Hfg x y <-.
  now destruct x => /=; f_equal.
Qed.

Lemma option_map_id {A} : option_map (@id A) =1 id.
Proof. by intros []. Qed.

Instance map_decl_pointwise : Proper (`=1` ==> `=1`) map_decl.
Proof. intros f g Hfg x. rewrite /map_decl.
  destruct x => /=. f_equal.
  - now rewrite Hfg.
  - apply Hfg.
Qed.

Lemma lookup_exchange_contexts Γ Γl Γr Δ i :
  nth_error (exchange_contexts Γ Γl Γr Δ) (exchange_renaming #|Γl| #|Γr| #|Δ| i) =
  option_map (map_decl (rename (exchange_rename #|Γl| #|Γr| #|Δ| i))) 
    (nth_error (Γ ,,, Γl,,, Γr,,, Δ) i).
Proof.
  rewrite /exchange_renaming /exchange_contexts /exchange_rename.
  case: (leb_spec_Set #|Δ| i) => hΔ.
  * case: leb_spec_Set => hΓr.
    + case: leb_spec_Set => hΓl.
      - do 6 (rewrite nth_error_app_ge; len; try lia => //).
        assert (i - #|Δ| - #|Γl| - #|Γr| = i - #|Δ| - #|Γr| - #|Γl|) as -> by lia.
        now rewrite rename_ren_id map_decl_id option_map_id.
      - rewrite nth_error_app_ge; len; try lia => //.
        rewrite nth_error_app_lt; len; try lia => //.
        rewrite nth_error_app_ge; len; try lia => //.
        rewrite nth_error_app_ge; len; try lia => //.
        rewrite nth_error_app_lt; len; try lia => //.
        rewrite nth_error_rename_context.
        assert (i - #|Δ| - #|Γr| = i - #|Γr| - #|Δ|) as -> by lia.
        apply option_map_ext => //.
        intros d. apply map_decl_ext => t.
        now rewrite shiftn_lift_renaming Nat.add_0_r.
    + rewrite nth_error_app_ge; len; try lia => //.
      rewrite nth_error_app_ge; len; try lia => //.
      rewrite nth_error_app_lt; len; try lia => //.
      rewrite nth_error_app_ge; len; try lia => //.
      rewrite nth_error_app_lt; len; try lia => //.
      rewrite nth_error_rename_context.
      assert (i + #|Γl| - #|Δ| - #|Γl| = i - #|Δ|) as -> by lia.
      reflexivity.
  * rewrite nth_error_app_lt; len; try lia => //.
    rewrite nth_error_app_lt; len; try lia => //.
    rewrite nth_error_rename_context.
    now rewrite shiftn_exchange_renaming Nat.add_0_r.
Qed.


(* 
Lemma exchange_renaming_add Γl Γr Δ n : 
  exchange_renaming Γl Γr Δ n = n + exchange_renaming Γl Γr Δ 0.
Proof.
  case: exchange_renamingP; case: exchange_renamingP; simpl; try lia.
  - intros.
 *)
 
Lemma exchange_rename_Δ Γl Γr Δ i (k : nat) :
  (* noccur_between_ctx 0 Γl Γr -> *)
  i < Δ ->
  (* From the i-prefix of Γ Γl Γr Δ to Γ Γr Γl Δ *)
  exchange_renaming Γl Γr Δ (S i + k) = 
  S (i + exchange_renaming Γl Γr (Δ - S i) k).
Proof.
  rewrite /exchange_renaming.
  repeat nat_compare_specs; lia.
Qed.

Lemma exchange_rename_Γr Γl Γr Δ i (k : nat) :
  (* noccur_between_ctx 0 Γl Γr -> *)
  Δ <= i < Δ + Γr ->
  k < Γr - S (i - Δ) \/ Γr - S (i - Δ) + Γl <= k ->
  (* From the i-prefix of Γ Γl Γr Δ to Γ Γr Γl Δ *)
  exchange_renaming Γl Γr Δ (S i + k) = 
  S (i + Γl + strengthen (Γr - S (i - Δ)) Γl k).
Proof.
  rewrite /exchange_renaming /strengthen.
  repeat nat_compare_specs.
Qed.
(* 
Lemma exchange_rename_Γl Γl Γr Δ i (k : nat) :
  (* noccur_between_ctx 0 Γl Γr -> *)
  Δ + Γr <= i < Δ + Γr + Γl ->
  (* From the i-prefix of Γ Γl Γr Δ to Γ Γr Γl Δ *)
  exchange_renaming Γl Γr Δ (S i + k) = 
  S (i + exchange_renaming Γl Γr (Δ - S i) k).
Proof.
  rewrite /exchange_renaming.
  repeat nat_compare_specs; lia.
Qed. *)

Lemma alli_Alli {A} (p : nat -> A -> bool) n l : 
  alli p n l <~> Alli p n l.
Proof.
  destruct (allbiP p p n l).
  - intros. destruct (p i x); now constructor.
  - split; eauto.
  - split; eauto. by [].
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

Lemma exchange_lift_rename {Γ Γl Γr Δ : context} {i d} :
  noccur_between_ctx 0 #|Γl| Γr ->
  nth_error (Γ,,, Γl,,, Γr,,, Δ) i = Some d ->
  rename_decl (fun k => exchange_renaming #|Γl| #|Γr| #|Δ| (S (i + k))) d =
  rename_decl (fun k => S (exchange_renaming #|Γl| #|Γr| #|Δ| i + exchange_rename #|Γl| #|Γr| #|Δ| i k)) d.
Proof.
  intros nocc hlen.
  move: hlen.
  case: lookup_declP => // d' Hi hnth [=]; intros ->; [|move: hnth; len in Hi].
  { apply map_decl_ext, rename_ext => k.
    rewrite {2}/exchange_renaming /exchange_rename. nat_compare_specs.
    now apply exchange_rename_Δ. }
  case: lookup_declP => // d' Hi' hnth [=]; intros ->; [|move: hnth; len in Hi'].
  { eapply nth_error_noccur_between_ctx in nocc; eauto.
    simpl in nocc. move: nocc.
    apply rename_decl_ext_cond => k Hk.
    rewrite {2}/exchange_renaming /exchange_rename.
    repeat nat_compare_specs.
    rewrite shiftn_strengthen_rel Nat.add_0_r //.
    now rewrite exchange_rename_Γr. }
  case: lookup_declP => // d' Hi'' hnth [=]; intros ->; [|move: hnth; len in Hi''].
  { apply map_decl_ext, rename_ext => k.
    rewrite /exchange_renaming /exchange_rename /lift_renaming; 
    repeat nat_compare_specs. }
  { move/nth_error_Some_length => hlen.
    apply map_decl_ext, rename_ext => k.
    rewrite /exchange_renaming /exchange_rename; repeat nat_compare_specs.
    now unfold ren_id. }
Qed.

Lemma exchange_urenaming Γ Γl Γr Δ :
  noccur_between_ctx 0 #|Γl| Γr ->
  urenaming
    (exchange_contexts Γ Γl Γr Δ)
    (Γ ,,, Γl ,,, Γr ,,, Δ)
    (exchange_renaming #|Γl| #|Γr| #|Δ|).
Proof.
  intros nocc i d hnth.
  rewrite lookup_exchange_contexts hnth => /=.
  eexists; split; eauto.
  pose proof (exchange_lift_rename nocc hnth).
  rewrite !lift_rename !rename_compose /lift_renaming /=. 
  destruct d as [na [b|] ty]; noconf H; simpl in *.
  - split => //.
    intros ? [= <-]. eexists; split => //.
    rewrite !lift_rename !rename_compose.
    rewrite /lift_renaming /= //. 
  - split => //.
Qed.

Lemma All_local_env_fold P f Γ :
  All_local_env (fun Γ t T => P (fold_context f Γ) (f #|Γ| t) (option_map (f #|Γ|) T)) Γ <~>
  All_local_env P (fold_context f Γ).
Proof.
  split.
  - induction 1; simpl; rewrite ?fold_context_snoc0; constructor; auto.
  - induction Γ; simpl; rewrite ?fold_context_snoc0; intros H.
    * constructor.
    * destruct a as [na [b|] ty]; depelim H; specialize (IHΓ H); constructor; auto.
Qed.

Lemma All_local_env_impl_ind {P Q : context -> term -> option term -> Type} {l} :
  All_local_env P l ->
  (forall Γ t T, All_local_env Q Γ -> P Γ t T -> Q Γ t T) ->
  All_local_env Q l.
Proof.
  induction 1; intros; simpl; econstructor; eauto.
Qed.

Lemma weakening_wf_local {cf: checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Γ' Γ''} :
  wf_local Σ (Γ ,,, Γ') ->
  wf_local Σ (Γ ,,, Γ'') ->  
  wf_local Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ').
Proof.
  intros wfΓ' wfΓ''.
  pose proof (env_prop_wf_local _ _ typing_rename_prop _ wfΣ _ wfΓ'). simpl in X.
  eapply All_local_env_app_inv in X as [XΓ XΓ'].
  apply wf_local_app => //.
  rewrite /lift_context.
  apply All_local_env_fold.
  eapply (All_local_env_impl_ind XΓ').
  intros Δ t [T|] IH; unfold lift_typing; simpl.
  - intros Hf. red. rewrite -/(lift_context #|Γ''| 0 Δ).
    rewrite Nat.add_0_r. rewrite !lift_rename. apply Hf.
    split.
    + apply wf_local_app; auto.
      apply All_local_env_fold in IH. apply IH.
    + apply (weakening_renaming Γ Δ Γ'').
  - intros [s Hs]; exists s. red.
    rewrite -/(lift_context #|Γ''| 0 Δ).
    rewrite Nat.add_0_r !lift_rename. apply Hs.
    split.
    + apply wf_local_app; auto.
      apply All_local_env_fold in IH. apply IH.
    + apply (weakening_renaming Γ Δ Γ'').
Qed.

Lemma weakening_wf_local_eq {cf: checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Γ' Γ'' n} :
  wf_local Σ (Γ ,,, Γ') ->
  wf_local Σ (Γ ,,, Γ'') ->
  n = #|Γ''| ->
  wf_local Σ (Γ ,,, Γ'' ,,, lift_context n 0 Γ').
Proof.
  intros ? ? ->; now apply weakening_wf_local.
Qed.

Lemma weakening_typing `{cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Γ' Γ''} {t T} :
  wf_local Σ (Γ ,,, Γ'') ->
  Σ ;;; Γ ,,, Γ' |- t : T ->
  Σ ;;; Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ' |- lift #|Γ''| #|Γ'| t : lift #|Γ''| #|Γ'| T.
Proof.
  intros wfext Ht.
  rewrite !lift_rename.
  eapply (env_prop_typing _ _ typing_rename_prop); eauto.
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

Lemma rename_context_lift_context n k Γ :
  rename_context (lift_renaming n k) Γ = lift_context n k Γ.
Proof.
  rewrite /rename_context /lift_context.
  apply fold_context_ext => i t.
  now rewrite lift_rename shiftn_lift_renaming.
Qed.

Lemma wf_local_app_ind {cf : checker_flags} {Σ Γ1 Γ2} :
  wf_local Σ Γ1 -> 
  (wf_local Σ Γ1 -> wf_local_rel Σ Γ1 Γ2) ->
  wf_local Σ (Γ1 ,,, Γ2).
Proof.
  intros wf IH.
  apply wf_local_app; auto.
Qed.

Lemma meta_conv_all {cf} {Σ Γ t A Γ' t' A'} :
    Σ ;;; Γ |- t : A ->
    Γ = Γ' -> t = t' -> A = A' ->
    Σ ;;; Γ' |- t' : A'.
Proof.
  intros h [] [] []; assumption.
Qed.

Instance fold_context_proper : Proper (pointwise_relation nat (pointwise_relation _ Logic.eq) ==> Logic.eq ==> Logic.eq) fold_context.
Proof.
  intros f g Hfg x y <-. now apply fold_context_ext.
Qed.

Lemma exchange_wf_local {cf: checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Γl Γr Δ} :
  noccur_between_ctx 0 #|Γl| Γr ->
  wf_local Σ (Γ ,,, Γl ,,, Γr ,,, Δ) ->
  wf_local Σ (exchange_contexts Γ Γl Γr Δ).
Proof.
  intros nocc wf.
  pose proof (env_prop_wf_local _ _ typing_rename_prop _ wfΣ _ wf).
  simpl in X. rewrite /exchange_contexts.
  eapply All_local_env_app_inv in X as [XΓ XΓ'].
  apply wf_local_app_ind => //.
  - rewrite rename_context_lift_context /strengthen /=.
    eapply weakening_wf_local_eq; eauto with wf.
    * admit.
    * now len.
  - intros wfstr.
    apply All_local_env_fold.
    eapply (All_local_env_impl_ind XΓ').
    intros Δ' t [T|] IH; unfold lift_typing; simpl.
    * intros Hf. red.
      eapply meta_conv_all. 2: reflexivity.
      2-3:now rewrite shiftn_exchange_renaming.
      apply Hf. split.
      + apply wf_local_app; auto.
        apply All_local_env_fold in IH. apply IH.
      +  setoid_rewrite shiftn_exchange_renaming. apply exchange_urenaming. Γ Δ Γ'').
    - intros [s Hs]; exists s. red.
      rewrite -/(lift_context #|Γ''| 0 Δ).
      rewrite Nat.add_0_r !lift_rename. apply Hs.
      split.
      + apply wf_local_app; auto.
        apply All_local_env_fold in IH. apply IH.
      + apply (weakening_renaming Γ Δ Γ'').
Qed.

Lemma exchange_typing `{cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Γ' Γ''} {t T} :
  wf_local Σ (Γ ,,, Γ'') ->
  Σ ;;; Γ ,,, Γ' |- t : T ->
  Σ ;;; Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ' |- lift #|Γ''| #|Γ'| t : lift #|Γ''| #|Γ'| T.
Proof.
  intros wfext Ht.
  rewrite !lift_rename.
  eapply (env_prop_typing _ _ typing_rename_prop); eauto.
  split.
  - eapply weakening_wf_local; eauto with pcuic.
  - now apply weakening_renaming.
Qed.




Lemma decompose_prod_assum_ctx ctx t : decompose_prod_assum ctx t =
  let (ctx', t') := decompose_prod_assum [] t in
  (ctx ,,, ctx', t').
Proof.
  induction t in ctx |- *; simpl; auto.
  - simpl. rewrite IHt2.
    rewrite (IHt2 ([] ,, vass _ _)).
    destruct (decompose_prod_assum [] t2). simpl.
    unfold snoc. now rewrite app_context_assoc.
  - simpl. rewrite IHt3.
    rewrite (IHt3 ([] ,, vdef _ _ _)).
    destruct (decompose_prod_assum [] t3). simpl.
    unfold snoc. now rewrite app_context_assoc.
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
    rewrite /lift_context // /fold_context /= /map_decl /=.
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
Hint Resolve lift_is_constructor : core.

Hint Rewrite lift_subst_instance_constr : lift.
Hint Rewrite lift_mkApps : lift.
Hint Rewrite distr_lift_subst distr_lift_subst10 : lift.

Lemma lift_declared_constant `{checker_flags} Σ cst decl n k :
  wf Σ ->
  declared_constant Σ cst decl ->
  decl = map_constant_body (lift n k) decl.
Proof.
  unfold declared_constant.
  intros.
  eapply lookup_on_global_env in H0; eauto.
  destruct H0 as [Σ' [wfΣ' decl']].
  red in decl'. red in decl'.
  destruct decl. simpl in *. destruct cst_body.
  - unfold map_constant_body. simpl.
    pose proof decl' as declty.
    apply typecheck_closed in declty; eauto.
    + destruct declty as [declty Hcl].
      rewrite -> andb_and in Hcl. destruct Hcl as [clb clty].
      pose proof (closed_upwards k clb).
      pose proof (closed_upwards k clty).
      simpl in *. forward H0 by lia. forward H1 by lia.
      apply (lift_closed n k) in H0.
      apply (lift_closed n k) in H1. rewrite H0 H1. reflexivity.

  - red in decl'.
    destruct decl'.
    apply subject_closed in t; auto.
    eapply closed_upwards in t; simpl.
    * apply (lift_closed n k) in t. unfold map_constant_body. simpl.
      rewrite t. reflexivity.
    * lia.
Qed.

Definition lift_mutual_inductive_body n k m :=
  map_mutual_inductive_body (fun k' => lift n (k' + k)) m.

Lemma lift_wf_local `{checker_flags} Σ Γ n k :
  wf Σ.1 ->
  wf_local Σ Γ ->
  lift_context n k Γ = Γ.
Proof.
  intros wfΣ.
  induction 1; auto; unfold lift_context, snoc; rewrite fold_context_snoc0; auto; unfold snoc;
    f_equal; auto; unfold map_decl; simpl.
  - destruct t0 as [s Hs]. unfold vass. f_equal.
    eapply typed_liftn; eauto. lia.
  - red in t0. destruct t0. unfold vdef. f_equal.
    + f_equal. eapply typed_liftn; eauto. lia.
    + eapply typed_liftn in t0 as [Ht HT]; eauto. lia.
Qed.

Lemma lift_declared_minductive `{checker_flags} {Σ : global_env} cst decl n k :
  wf Σ ->
  declared_minductive Σ cst decl ->
  lift_mutual_inductive_body n k decl = decl.
Proof.
  intros wfΣ Hdecl.
  pose proof (on_declared_minductive wfΣ Hdecl). apply onNpars in X.
  apply (declared_inductive_closed (Σ:=(empty_ext Σ))) in Hdecl; auto.
  move: Hdecl.
  rewrite /closed_inductive_decl /lift_mutual_inductive_body.
  destruct decl; simpl.
  move/andb_and => [clpar clbodies]. f_equal.
  - now rewrite [fold_context _ _]closed_ctx_lift.
  - eapply forallb_All in clbodies.
    eapply Alli_mapi_id.
    * eapply (All_Alli clbodies). intros; eauto.
      intros. eapply H0.
    * simpl; intros.
      move: H0. rewrite /closed_inductive_body.
      destruct x; simpl. move=> /andb_and[/andb_and [ci ct] cp].
      f_equal.
      + rewrite lift_closed; eauto.
        eapply closed_upwards; eauto; lia.
      + eapply All_map_id. eapply forallb_All in ct.
        eapply (All_impl ct). intros x.
        destruct x as [[id ty] arg]; unfold on_pi2; intros c; simpl; repeat f_equal.
        apply lift_closed. unfold cstr_type in c; simpl in c.
        eapply closed_upwards; eauto; lia.
      + simpl in X. rewrite -X in cp.
        eapply forallb_All in cp. eapply All_map_id; eauto.
        eapply (All_impl cp); intuition auto.
        destruct x; unfold on_snd; simpl; f_equal.
        apply lift_closed. rewrite context_assumptions_fold.
        eapply closed_upwards; eauto; lia.
Qed.

Lemma lift_declared_inductive `{checker_flags} ind Σ mdecl idecl n k :
  wf Σ ->
  declared_inductive Σ ind mdecl idecl ->
  map_one_inductive_body (context_assumptions mdecl.(ind_params))
                         (length (arities_context mdecl.(ind_bodies))) (fun k' => lift n (k' + k))
                         (inductive_ind ind) idecl = idecl.
Proof.
  unfold declared_inductive. intros wfΣ [Hmdecl Hidecl].
  eapply (lift_declared_minductive _ _ n k) in Hmdecl. 2: auto.
  unfold lift_mutual_inductive_body in Hmdecl.
  destruct mdecl. simpl in *.
  injection Hmdecl. intros Heq.
  clear Hmdecl.
  pose proof Hidecl as Hidecl'.
  rewrite <- Heq in Hidecl'.
  rewrite nth_error_mapi in Hidecl'.
  clear Heq.
  unfold option_map in Hidecl'. rewrite Hidecl in Hidecl'.
  congruence.
Qed.

Lemma subst0_inds_lift ind u mdecl n k t :
  (subst0 (inds (inductive_mind ind) u (ind_bodies mdecl))
          (lift n (#|arities_context (ind_bodies mdecl)| + k) t)) =
  lift n k (subst0 (inds (inductive_mind ind) u (ind_bodies mdecl)) t).
Proof.
  rewrite (distr_lift_subst_rec _ _ n 0 k). simpl.
  unfold arities_context. rewrite rev_map_length inds_length.
  f_equal. generalize (ind_bodies mdecl).
  clear. intros.
  induction l; unfold inds; simpl; auto. f_equal. auto.
Qed.

Lemma lift_declared_constructor `{checker_flags} Σ c u mdecl idecl cdecl n k :
  wf Σ ->
  declared_constructor Σ c mdecl idecl cdecl ->
  lift n k (type_of_constructor mdecl cdecl c u) = (type_of_constructor mdecl cdecl c u).
Proof.
  unfold declared_constructor. destruct c as [i ci]. intros wfΣ [Hidecl Hcdecl].
  eapply (lift_declared_inductive _ _ _ _ n k) in Hidecl; eauto.
  unfold type_of_constructor. destruct cdecl as [[id t'] arity].
  destruct idecl; simpl in *.
  injection Hidecl.
  intros.
  pose Hcdecl as Hcdecl'.
  rewrite <- H1 in Hcdecl'.
  rewrite nth_error_map in Hcdecl'. rewrite Hcdecl in Hcdecl'.
  simpl in Hcdecl'. injection Hcdecl'.
  intros.
  rewrite <- H3 at 2.
  rewrite <- lift_subst_instance_constr.
  now rewrite subst0_inds_lift.
Qed.

Lemma lift_declared_projection `{checker_flags} Σ c mdecl idecl pdecl n k :
  wf Σ ->
  declared_projection Σ c mdecl idecl pdecl ->
  on_snd (lift n (S (ind_npars mdecl + k))) pdecl = pdecl.
Proof.
  intros.
  eapply (declared_projection_closed (Σ:=empty_ext Σ)) in H0; auto.
  unfold on_snd. simpl.
  rewrite lift_closed.
  - eapply closed_upwards; eauto; try lia.
  - destruct pdecl; reflexivity.
Qed.

Lemma lift_fix_context:
  forall (mfix : list (def term)) (n k : nat),
    fix_context (map (map_def (lift n k) (lift n (#|mfix| + k))) mfix) = lift_context n k (fix_context mfix).
Proof.
  intros mfix n k. unfold fix_context.
  rewrite map_vass_map_def rev_mapi.
  fold (fix_context mfix).
  rewrite (lift_context_alt n k (fix_context mfix)).
  unfold lift_decl. now rewrite mapi_length fix_context_length.
Qed.

Hint Rewrite <- lift_fix_context : lift.

Lemma All_local_env_lift `{checker_flags}
      (P Q : context -> term -> option term -> Type) c n k :
  All_local_env Q c ->
  (forall Γ t T,
      Q Γ t T ->
      P (lift_context n k Γ) (lift n (#|Γ| + k) t)
        (option_map (lift n (#|Γ| + k)) T)
  ) ->
  All_local_env P (lift_context n k c).
Proof.
  intros Hq Hf.
  induction Hq in |- *; try econstructor; eauto;
    simpl; rewrite lift_context_snoc; econstructor; eauto.
  - simpl. eapply (Hf _ _ None). eauto.
  - simpl. eapply (Hf _ _ None). eauto.
  - simpl. eapply (Hf _ _ (Some t)). eauto.
Qed.

Lemma lift_destArity ctx t n k :
  destArity (lift_context n k ctx) (lift n (#|ctx| + k) t) =
        match destArity ctx t with
        | Some (args, s) => Some (lift_context n k args, s)
        | None => None
        end.
Proof.
  revert ctx.
  induction t in n, k |- * using term_forall_list_ind; intros ctx; simpl; trivial.
  - move: (IHt2 n k (ctx,, vass n0 t1)).
    now rewrite lift_context_snoc /= /lift_decl /map_decl /vass /= => ->.
  - move: (IHt3 n k (ctx,, vdef n0 t1 t2)).
    now rewrite lift_context_snoc /= /lift_decl /map_decl /vass /= => ->.
Qed.

(* Lemma lift_strip_outer_cast n k t : lift n k (strip_outer_cast t) = strip_outer_cast (lift n k t). *)
(* Proof. *)
(*   induction t; simpl; try reflexivity. *)
(*   destruct Nat.leb; reflexivity. *)
(*   now rewrite IHt1. *)
(* Qed. *)

Definition on_pair {A B C D} (f : A -> B) (g : C -> D) (x : A * C) :=
  (f (fst x), g (snd x)).

Lemma lift_instantiate_params_subst n k params args s t :
  instantiate_params_subst (mapi_rec (fun k' decl => lift_decl n (k' + k) decl) params #|s|)
                           (map (lift n k) args) (map (lift n k) s) (lift n (#|s| + k) t) =
  option_map (on_pair (map (lift n k)) (lift n (#|s| + k + #|params|))) (instantiate_params_subst params args s t).
Proof.
  induction params in args, t, n, k, s |- *.
  - destruct args; simpl; rewrite ?Nat.add_0_r; reflexivity.
  - simpl. simpl. (* rewrite <- lift_strip_outer_cast. generalize (strip_outer_cast t). *)
    (* clear t; intros t. *)
    destruct a as [na [body|] ty]; simpl; try congruence.
    + destruct t; simpl; try congruence.
      specialize (IHparams n k args (subst0 s body :: s) t3).
      rewrite <- Nat.add_succ_r. simpl in IHparams.
      rewrite Nat.add_succ_r.
      replace (#|s| + k + S #|params|) with (S (#|s| + k + #|params|)) by lia.
      rewrite <- IHparams.
      rewrite distr_lift_subst. reflexivity.
    + destruct t; simpl; try congruence.
      destruct args; simpl; try congruence.
      specialize (IHparams n k args (t :: s) t2). simpl in IHparams.
      replace (#|s| + k + S #|params|) with (S (#|s| + k + #|params|)) by lia.
      rewrite <- IHparams. auto.
Qed.

Lemma instantiate_params_subst_length params args s t ctx t' :
  instantiate_params_subst params args s t = Some (ctx, t') ->
  #|ctx| = #|s| + #|params|.
Proof.
  induction params in args, s, t, ctx, t' |- * ;
  destruct args; simpl; auto; try congruence.
  - rewrite Nat.add_0_r. congruence.
  - destruct decl_body.
    + simpl.
      destruct t; simpl; try congruence.
      intros. erewrite IHparams; eauto. simpl. lia.
    + destruct t; simpl; try congruence.
  - destruct decl_body.
    + simpl.
      destruct t; simpl; try congruence.
      intros. erewrite IHparams; eauto. simpl. lia.
    + destruct t; simpl; try congruence.
      intros. erewrite IHparams; eauto. simpl. lia.
Qed.

Lemma closed_tele_lift n k ctx :
  closed_ctx ctx ->
  mapi (fun (k' : nat) (decl : context_decl) => lift_decl n (k' + k) decl) (List.rev ctx) = List.rev ctx.
Proof.
  rewrite /closedn_ctx /mapi. simpl. generalize 0.
  induction ctx using rev_ind.
  1: move=> //.
  move=> n0.
  rewrite /closedn_ctx !rev_app_distr /id /=.
  move/andb_and => [closedx Hctx].
  rewrite lift_decl_closed.
  - rewrite (@closed_decl_upwards n0) //; try lia.
  - f_equal. now rewrite IHctx.
Qed.

Lemma lift_instantiate_params n k params args t :
  closed_ctx params ->
  option_map (lift n k) (instantiate_params params args t) =
  instantiate_params params (map (lift n k) args) (lift n k t).
Proof.
  unfold instantiate_params.
  move/(closed_tele_lift n k params)=> Heq.
  rewrite -{2}Heq.
  specialize (lift_instantiate_params_subst n k (List.rev params) args [] t).
  move=> /= Heq'; rewrite Heq'.
  case E: (instantiate_params_subst (List.rev params) args)=> [[l' t']|] /= //.
  rewrite distr_lift_subst.
  move/instantiate_params_subst_length: E => -> /=.  do 3 f_equal. lia.
Qed.
Hint Rewrite lift_instantiate_params : lift.

Lemma lift_decompose_prod_assum_rec ctx t n k :
  (let (ctx', t') := decompose_prod_assum ctx t in
  (lift_context n k ctx', lift n (length ctx' + k) t')) =
  decompose_prod_assum (lift_context n k ctx) (lift n (length ctx + k) t).
Proof.
  induction t in n, k, ctx |- *; simpl;
    try rewrite -> Nat.sub_diag, Nat.add_0_r; try (eauto; congruence).
  - specialize (IHt2 (ctx ,, vass na t1) n k).
    destruct decompose_prod_assum. rewrite IHt2. simpl.
    rewrite lift_context_snoc. reflexivity.
  - specialize (IHt3 (ctx ,, vdef na t1 t2) n k).
    destruct decompose_prod_assum. rewrite IHt3. simpl.
    rewrite lift_context_snoc. reflexivity.
Qed.

Lemma lift_decompose_prod_assum t n k :
  (let (ctx', t') := decompose_prod_assum [] t in
  (lift_context n k ctx', lift n (length ctx' + k) t')) =
  decompose_prod_assum [] (lift n k t).
Proof. apply lift_decompose_prod_assum_rec. Qed.

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
Hint Rewrite lift_it_mkProd_or_LetIn : lift.

Lemma to_extended_list_lift n k c :
  to_extended_list (lift_context n k c) = to_extended_list c.
Proof.
  unfold to_extended_list, to_extended_list_k. generalize 0.
  unf_term. generalize (@nil term) at 1 2.
  induction c in n, k |- *; simpl; intros. 1: reflexivity.
  rewrite -> lift_context_snoc0. unfold snoc. simpl.
  destruct a. destruct decl_body.
  - unfold lift_decl, map_decl. simpl.
    now rewrite -> IHc.
  - simpl. apply IHc.
Qed.

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

Lemma weakening_red1 `{CF:checker_flags} Σ Γ Γ' Γ'' M N :
  wf Σ ->
  red1 Σ (Γ ,,, Γ') M N ->
  red1 Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') (lift #|Γ''| #|Γ'| M) (lift #|Γ''| #|Γ'| N).
Proof.
  intros wfΣ H.
  remember (Γ ,,, Γ') as Γ0. revert Γ Γ' Γ'' HeqΓ0.
  induction H using red1_ind_all in |- *; intros Γ0 Γ' Γ'' HeqΓ0; try subst Γ; simpl;
    autorewrite with lift;
    try solve [  econstructor; eauto with pcuic ].

  - elim (leb_spec_Set); intros Hn.
    + rewrite -> simpl_lift; try lia. rewrite -> Nat.add_succ_r.
      econstructor; eauto.
      erewrite (weaken_nth_error_ge Hn) in H. eauto.

    + rewrite <- lift_simpl by easy.
      econstructor.
      rewrite -> (weaken_nth_error_lt Hn).
      now unfold lift_decl; rewrite -> option_map_decl_body_map_decl, H.

  - econstructor; eauto with pcuic.
    rewrite H0. f_equal.
    eapply (lookup_on_global_env _ _ _ _ wfΣ) in H.
    destruct H as [Σ' [wfΣ' decl']].
    red in decl'. red in decl'.
    rewrite -> H0 in decl'.
    apply typecheck_closed in decl'; eauto.
    destruct decl'.
    rewrite -> andb_and in i. destruct i as [Hclosed _].
    simpl in Hclosed.
    pose proof (closed_upwards #|Γ'| Hclosed).
    forward H by lia.
    apply (lift_closed #|Γ''| #|Γ'|) in H. auto.

  - simpl. constructor.
    now rewrite -> nth_error_map, H.

  - constructor.
    specialize (IHred1 Γ0 (Γ' ,, vass na N) Γ'' eq_refl).
    rewrite -> lift_context_snoc, Nat.add_0_r in IHred1. apply IHred1.

  - constructor.
    specialize (IHred1 Γ0 (Γ' ,, vdef na b t) Γ'' eq_refl).
    rewrite -> lift_context_snoc, Nat.add_0_r in IHred1. apply IHred1.

  - constructor.
    induction X; constructor; auto.
    intuition; eauto.

  - constructor.
    specialize (IHred1 Γ0 (Γ' ,, vass na M1) Γ'' eq_refl).
    rewrite -> lift_context_snoc, Nat.add_0_r in IHred1. apply IHred1.

  - constructor.
    induction X; constructor; auto.
    intuition; eauto.

  - constructor.
    rewrite -> (OnOne2_length X). generalize (#|mfix1|).
    induction X; simpl; constructor; simpl; intuition eauto.
    congruence.

  - apply fix_red_body. rewrite !lift_fix_context.
    rewrite <- (OnOne2_length X).
    eapply OnOne2_map. unfold on_Trel; solve_all. 2: congruence.
    specialize (b0 Γ0 (Γ' ,,, fix_context mfix0)).
    rewrite app_context_assoc in b0. specialize (b0 Γ'' eq_refl).
    rewrite -> app_context_length, fix_context_length in *.
    rewrite -> lift_context_app in *.
    rewrite -> app_context_assoc, Nat.add_0_r in *.
    auto.

  - constructor.
    rewrite -> (OnOne2_length X). generalize (#|mfix1|).
    induction X; simpl; constructor; intuition eauto.
    + simpl; auto.
    + simpl; congruence.

  - apply cofix_red_body. rewrite !lift_fix_context.
    rewrite <- (OnOne2_length X).
    eapply OnOne2_map. unfold on_Trel; solve_all. 2: congruence.
    specialize (b0 Γ0 (Γ' ,,, fix_context mfix0)).
    rewrite app_context_assoc in b0. specialize (b0 Γ'' eq_refl).
    rewrite -> app_context_length, fix_context_length in *.
    rewrite -> lift_context_app in *.
    rewrite -> app_context_assoc, Nat.add_0_r in *.
    auto.
Qed.

Lemma weakening_red `{CF:checker_flags} Σ Γ Γ' Γ'' M N :
  wf Σ ->
  red Σ (Γ ,,, Γ') M N ->
  red Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') (lift #|Γ''| #|Γ'| M) (lift #|Γ''| #|Γ'| N).
Proof.
  intros wfΣ; induction 1.
  - constructor. eapply weakening_red1; auto.
  - reflexivity.
  - etransitivity; eassumption.
Qed.

Fixpoint lift_stack n k π :=
  match π with
  | ε => ε
  | App u π =>
      let k' := #|stack_context π| + k in
      App (lift n k' u) (lift_stack n k π)
  | Fix mfix idx args π =>
      let k' := #|stack_context π| + k in
      let k'' := #|mfix| + k' in
      let mfix' := List.map (map_def (lift n k') (lift n k'')) mfix in
      Fix mfix' idx (map (lift n k') args) (lift_stack n k π)
  | Fix_mfix_ty na bo ra mfix1 mfix2 idx π =>
      let k' := #|stack_context π| + k in
      let k'' := #|mfix1| + S #|mfix2| + k' in
      let mfix1' := List.map (map_def (lift n k') (lift n k'')) mfix1 in
      let mfix2' := List.map (map_def (lift n k') (lift n k'')) mfix2 in
      Fix_mfix_ty na (lift n k'' bo) ra mfix1' mfix2' idx (lift_stack n k π)
  | Fix_mfix_bd na ty ra mfix1 mfix2 idx π =>
      let k' := #|stack_context π| + k in
      let k'' := #|mfix1| + S #|mfix2| + k' in
      let mfix1' := List.map (map_def (lift n k') (lift n k'')) mfix1 in
      let mfix2' := List.map (map_def (lift n k') (lift n k'')) mfix2 in
      Fix_mfix_bd na (lift n k' ty) ra mfix1' mfix2' idx (lift_stack n k π)
  | CoFix mfix idx args π =>
      let k' := #|stack_context π| + k in
      let k'' := #|mfix| + k' in
      let mfix' := List.map (map_def (lift n k') (lift n k'')) mfix in
      CoFix mfix' idx (map (lift n k') args) (lift_stack n k π)
  | CoFix_mfix_ty na bo ra mfix1 mfix2 idx π =>
      let k' := #|stack_context π| + k in
      let k'' := #|mfix1| + S #|mfix2| + k' in
      let mfix1' := List.map (map_def (lift n k') (lift n k'')) mfix1 in
      let mfix2' := List.map (map_def (lift n k') (lift n k'')) mfix2 in
      CoFix_mfix_ty na (lift n k'' bo) ra mfix1' mfix2' idx (lift_stack n k π)
  | CoFix_mfix_bd na ty ra mfix1 mfix2 idx π =>
      let k' := #|stack_context π| + k in
      let k'' := #|mfix1| + S #|mfix2| + k' in
      let mfix1' := List.map (map_def (lift n k') (lift n k'')) mfix1 in
      let mfix2' := List.map (map_def (lift n k') (lift n k'')) mfix2 in
      CoFix_mfix_bd na (lift n k' ty) ra mfix1' mfix2' idx (lift_stack n k π)
  | Case_p indn c brs π =>
      let k' := #|stack_context π| + k in
      let brs' := List.map (on_snd (lift n k')) brs in
      Case_p indn (lift n k' c) brs' (lift_stack n k π)
  | Case indn pred brs π =>
      let k' := #|stack_context π| + k in
      let brs' := List.map (on_snd (lift n k')) brs in
      Case indn (lift n k' pred) brs' (lift_stack n k π)
  | Case_brs indn pred c m brs1 brs2 π =>
      let k' := #|stack_context π| + k in
      let brs1' := List.map (on_snd (lift n k')) brs1 in
      let brs2' := List.map (on_snd (lift n k')) brs2 in
      Case_brs indn (lift n k' pred) (lift n k' c) m brs1' brs2' (lift_stack n k π)
  | Proj p π =>
      Proj p (lift_stack n k π)
  | Prod_l na B π =>
      let k' := #|stack_context π| + k in
      Prod_l na (lift n (S k') B) (lift_stack n k π)
  | Prod_r na A π =>
      let k' := #|stack_context π| + k in
      Prod_r na (lift n k' A) (lift_stack n k π)
  | Lambda_ty na b π =>
      let k' := #|stack_context π| + k in
      Lambda_ty na (lift n (S k') b) (lift_stack n k π)
  | Lambda_tm na A π =>
      let k' := #|stack_context π| + k in
      Lambda_tm na (lift n k' A) (lift_stack n k π)
  | LetIn_bd na B u π =>
      let k' := #|stack_context π| + k in
      LetIn_bd na (lift n k' B) (lift n (S k') u) (lift_stack n k π)
  | LetIn_ty na b u π =>
      let k' := #|stack_context π| + k in
      LetIn_ty na (lift n k' b) (lift n (S k') u) (lift_stack n k π)
  | LetIn_in na b B π =>
      let k' := #|stack_context π| + k in
      LetIn_in na (lift n k' b) (lift n k' B) (lift_stack n k π)
  | coApp u π =>
      let k' := #|stack_context π| + k in
      coApp (lift n k' u) (lift_stack n k π)
  end.

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

Lemma lift_zipc :
  forall n k t π,
    let k' := #|stack_context π| + k in
    lift n k (zipc t π) =
    zipc (lift n k' t) (lift_stack n k π).
Proof.
  intros n k t π k'.
  induction π in n, k, t, k' |- *.
  all: try reflexivity.
  all: try solve [
    simpl ; rewrite IHπ ; cbn ; reflexivity
  ].
  - simpl. rewrite IHπ. cbn. f_equal.
    rewrite lift_mkApps. cbn. reflexivity.
  - simpl. rewrite IHπ. cbn. f_equal. f_equal.
    rewrite map_app. rewrite !app_length. cbn. reflexivity.
  - simpl. rewrite IHπ. cbn. f_equal. f_equal.
    rewrite map_app. rewrite !app_length. cbn. f_equal.
    unfold map_def at 1. cbn. f_equal.
    rewrite fix_context_alt_length.
    rewrite !app_length. cbn. rewrite !map_length.
    f_equal. f_equal. lia.
  - simpl. rewrite IHπ. cbn. f_equal. f_equal.
    rewrite lift_mkApps. cbn. reflexivity.
  - simpl. rewrite IHπ. cbn. f_equal. f_equal.
    rewrite map_app. rewrite !app_length. cbn. reflexivity.
  - simpl. rewrite IHπ. cbn. f_equal. f_equal.
    rewrite map_app. rewrite !app_length. cbn. f_equal.
    unfold map_def at 1. cbn. f_equal.
    rewrite fix_context_alt_length.
    rewrite !app_length. cbn. rewrite !map_length.
    f_equal. f_equal. lia.
  - simpl. rewrite IHπ. cbn. f_equal. f_equal.
    rewrite map_app. cbn. reflexivity.
Qed.

Lemma weakening_cumul `{CF:checker_flags} Σ Γ Γ' Γ'' M N :
  wf Σ.1 ->
  Σ ;;; Γ ,,, Γ' |- M <= N ->
  Σ ;;; Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ' |- lift #|Γ''| #|Γ'| M <= lift #|Γ''| #|Γ'| N.
Proof.
  intros wfΣ. induction 1.
  - constructor. now apply lift_leq_term.
  - eapply weakening_red1 in r; auto.
    econstructor 2; eauto.
  - eapply weakening_red1 in r; auto.
    econstructor 3; eauto.
Qed.

Lemma destArity_it_mkProd_or_LetIn ctx ctx' t :
  destArity ctx (it_mkProd_or_LetIn ctx' t) =
  destArity (ctx ,,, ctx') t.
Proof.
  induction ctx' in ctx, t |- *; simpl; auto.
  rewrite IHctx'. destruct a as [na [b|] ty]; reflexivity.
Qed.

Lemma lift_build_case_predicate_type ind mdecl idecl u params ps n k :
  closed_ctx (subst_instance_context u (ind_params mdecl)) ->
  build_case_predicate_type ind mdecl
    (map_one_inductive_body (context_assumptions mdecl.(ind_params))
            (length (arities_context (ind_bodies mdecl))) (fun k' => lift n (k' + k))
            (inductive_ind ind) idecl)
    (map (lift n k) params) u ps
  = option_map (lift n k) (build_case_predicate_type ind mdecl idecl params u ps).
Proof.
  intros closedpars. unfold build_case_predicate_type.
  rewrite -> ind_type_map. simpl.
  epose proof (lift_instantiate_params n k _ params (subst_instance_constr u (ind_type idecl))) as H.
  rewrite <- lift_subst_instance_constr.
  erewrite <- H; trivial. clear H.
  case_eq (instantiate_params (subst_instance_context u (ind_params mdecl)) params (subst_instance_constr u (ind_type idecl))) ; cbnr.
  intros ity eq.
  pose proof (lift_destArity [] ity n k) as H; cbn in H. rewrite H; clear H.
  destruct destArity as [[ctx s] | ]; [|reflexivity]. simpl. f_equal.
  rewrite lift_it_mkProd_or_LetIn; cbn. unf_term. f_equal. f_equal.
  - destruct idecl; reflexivity.
  - rewrite lift_mkApps; cbn; f_equal. rewrite map_app. f_equal.
    + rewrite !map_map lift_context_length; apply map_ext. clear.
      intro. now rewrite -> permute_lift by lia.
    + now rewrite -> to_extended_list_lift, <- to_extended_list_map_lift.
Qed.

Lemma lift_build_branches_type ind mdecl idecl u p params n k :
  closed_ctx (subst_instance_context u (ind_params mdecl)) ->
  build_branches_type ind mdecl
         (map_one_inductive_body (context_assumptions mdecl.(ind_params))
            #|arities_context (ind_bodies mdecl)| (fun k' => lift n (k' + k))
            (inductive_ind ind) idecl)
         (map (lift n k) params) u (lift n k p)
  = map (option_map (on_snd (lift n k)))
        (build_branches_type ind mdecl idecl params u p).
Proof.
  intros closedpars. unfold build_branches_type.
  rewrite -> ind_ctors_map.
  rewrite -> mapi_map, map_mapi. eapply mapi_ext. intros i x.
  destruct x as [[id t] arity]. simpl.
  rewrite <- lift_subst_instance_constr.
  rewrite subst0_inds_lift.
  rewrite <- lift_instantiate_params ; trivial.
  match goal with
  | |- context [ option_map _ (instantiate_params ?x ?y ?z) ] =>
    destruct (instantiate_params x y z) eqn:Heqip; cbnr
  end.
  epose proof (lift_decompose_prod_assum t0 n k).
  destruct (decompose_prod_assum [] t0).
  rewrite <- H.
  destruct (decompose_app t1) as [fn arg] eqn:?.
  rewrite (decompose_app_lift _ _ _ fn arg); auto. simpl.
  destruct (chop _ arg) eqn:Heqchop.
  eapply chop_map in Heqchop.
  rewrite -> Heqchop. clear Heqchop.
  unfold on_snd. simpl. f_equal.
  rewrite -> lift_it_mkProd_or_LetIn, !lift_mkApps, map_app; simpl.
  rewrite -> !lift_mkApps, !map_app, lift_context_length.
  rewrite -> permute_lift by lia. arith_congr.
  now rewrite -> to_extended_list_lift, <- to_extended_list_map_lift.
Qed.

Lemma destInd_lift n k t : destInd (lift n k t) = destInd t.
Proof.
  destruct t; simpl; try congruence.
Qed.

Lemma weakening_check_one_fix (Γ' Γ'' : context) mfix :
  map
       (fun x : def term =>
        check_one_fix (map_def (lift #|Γ''| #|Γ'|) (lift #|Γ''| (#|mfix| + #|Γ'|)) x)) mfix =
  map check_one_fix mfix.
Proof.
  apply map_ext. move=> [na ty def rarg] /=.
  rewrite decompose_prod_assum_ctx.
  destruct (decompose_prod_assum _ ty) eqn:decomp.
  rewrite decompose_prod_assum_ctx in decomp.
  rewrite -lift_decompose_prod_assum.
  destruct (decompose_prod_assum [] ty) eqn:decty.
  noconf decomp. rewrite !app_context_nil_l (smash_context_lift []).
  destruct (nth_error_spec (List.rev (smash_context [] c0)) rarg);
  autorewrite with len in *; simpl in *.
  - rewrite nth_error_rev_inv; autorewrite with len; simpl; auto.
    rewrite nth_error_lift_context_eq.
    simpl.
    rewrite nth_error_rev_inv in e; autorewrite with len; auto.
    autorewrite with len in e. simpl in e. rewrite e. simpl.
    destruct (decompose_app (decl_type x)) eqn:Happ.
    erewrite decompose_app_lift; eauto.
    rewrite destInd_lift. reflexivity.
  - erewrite (proj2 (nth_error_None _ _)); auto.
    autorewrite with len. simpl; lia.
Qed.

Lemma weakening_check_one_cofix (Γ' Γ'' : context) mfix :
  map
       (fun x : def term =>
        check_one_cofix (map_def (lift #|Γ''| #|Γ'|) (lift #|Γ''| (#|mfix| + #|Γ'|)) x)) mfix =
  map check_one_cofix mfix.
Proof.
  apply map_ext. move=> [na ty def rarg] /=.
  rewrite decompose_prod_assum_ctx.
  destruct (decompose_prod_assum _ ty) eqn:decomp.
  rewrite decompose_prod_assum_ctx in decomp.
  rewrite -lift_decompose_prod_assum.
  destruct (decompose_prod_assum [] ty) eqn:decty.
  noconf decomp.
  destruct (decompose_app t) eqn:Happ.
  erewrite decompose_app_lift; eauto.
  rewrite destInd_lift. reflexivity.
Qed.

Lemma weakening_typing_prop {cf:checker_flags} : env_prop (fun Σ Γ0 t T =>
  forall Γ Γ' Γ'' : context,
  wf_local Σ (Γ ,,, Γ'') ->
  Γ0 = Γ ,,, Γ' ->
  Σ;;; Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ' |- lift #|Γ''| #|Γ'| t : lift #|Γ''| #|Γ'| T)
  (fun Σ Γ0 _  =>
  forall Γ Γ' Γ'' : context,
  Γ0 = Γ ,,, Γ' ->
  wf_local Σ (Γ ,,, Γ'') ->
  wf_local Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ')).
Proof.
  apply typing_ind_env;
    intros Σ wfΣ Γ0; !!intros; subst Γ0; simpl in *; try solve [econstructor; eauto];
        try specialize (forall_Γ  _ _ _ eq_refl wf).

  - induction Γ'; simpl; auto.
    depelim X; rewrite lift_context_snoc; simpl; constructor.
    + eapply IHΓ'; eauto.
    + red. exists (tu.π1). simpl.
      rewrite Nat.add_0_r. apply t0; auto.
    + eapply IHΓ'; eauto.
    + red. exists (tu.π1). simpl.
      rewrite Nat.add_0_r. apply t1; auto.
    + simpl. rewrite Nat.add_0_r. apply t0; auto.

  - elim (leb_spec_Set); intros Hn.
    + rewrite -> simpl_lift; try lia. rewrite -> Nat.add_succ_r.
      constructor. 1: auto.
      now rewrite <- (weaken_nth_error_ge Hn).
    + assert (forall t, lift0 (S n) (lift #|Γ''| (#|Γ'| - S n) t) = lift #|Γ''| #|Γ'| (lift0 (S n) t)).
      * intros.
        assert (H:#|Γ'| = S n + (#|Γ'| - S n)) by easy.
        rewrite -> H at 2.
        rewrite permute_lift; easy.
      * rewrite <- H.
        rewrite -> map_decl_type. constructor; auto.
        now rewrite -> (weaken_nth_error_lt Hn), heq_nth_error.

  - econstructor; auto.
    specialize (IHb Γ (Γ' ,, vass n t) Γ'' wf eq_refl).
    rewrite -> lift_context_snoc, plus_0_r in IHb.
    eapply IHb.

  - econstructor; auto.
    simpl.
    specialize (IHb Γ (Γ' ,, vass n t) Γ'' wf eq_refl).
    rewrite -> lift_context_snoc, plus_0_r in IHb.
    eapply IHb.

  - econstructor; auto.
    specialize (IHb Γ Γ' Γ'' wf eq_refl). simpl.
    specialize (IHb' Γ (Γ' ,, vdef n b b_ty) Γ'' wf eq_refl).
    rewrite -> lift_context_snoc, plus_0_r in IHb'.
    apply IHb'.

  - eapply refine_type. 1: econstructor; auto.
    now rewrite -> distr_lift_subst10.

  - autorewrite with lift.
    rewrite -> map_cst_type. constructor; auto.
    erewrite <- lift_declared_constant; eauto.

  - autorewrite with lift.
    erewrite <- (ind_type_map (fun k' => lift #|Γ''| (k' + #|Γ'|))).
    pose proof isdecl as isdecl'.
    destruct isdecl. intuition auto.
    eapply lift_declared_inductive in 2: isdecl'. auto.
    rewrite -> isdecl'.
    econstructor; try red; intuition eauto.

  - rewrite (lift_declared_constructor _ (ind, i) u mdecl idecl cdecl _ _ wfΣ isdecl).
    econstructor; eauto.

  - rewrite -> lift_mkApps, map_app, map_skipn.
    specialize (IHc _ _ _ wf eq_refl).
    specialize (IHp _ _ _ wf eq_refl).
    assert (Hclos: closed_ctx (subst_instance_context u (ind_params mdecl))). {
      destruct isdecl as [Hmdecl Hidecl].
      eapply on_declared_minductive in Hmdecl; eauto.
      eapply onParams in Hmdecl.
      rewrite closedn_subst_instance_context.
      eapply closed_wf_local in Hmdecl; eauto. }
    simpl. econstructor.
    8:{ cbn. rewrite -> firstn_map.
        erewrite lift_build_branches_type; tea.
        rewrite map_option_out_map_option_map.
        subst params. erewrite heq_map_option_out. reflexivity. }
    all: eauto.
    -- erewrite -> lift_declared_inductive; eauto.
    -- simpl. erewrite firstn_map, lift_build_case_predicate_type; tea.
       subst params. erewrite heq_build_case_predicate_type; reflexivity.
    -- destruct idecl; simpl in *; auto.
    -- now rewrite -> !lift_mkApps in IHc.
    -- solve_all.
      destruct b0 as [s [Hs IH]]; eauto.

  - simpl.
    erewrite (distr_lift_subst_rec _ _ _ 0 #|Γ'|).
    simpl. rewrite -> map_rev.
    subst ty.
    rewrite -> List.rev_length, lift_subst_instance_constr.
    replace (lift #|Γ''| (S (#|args| + #|Γ'|)) (snd pdecl))
      with (snd (on_snd (lift #|Γ''| (S (#|args| + #|Γ'|))) pdecl)) by now destruct pdecl.
    econstructor.
    + red. split.
      * apply (proj1 isdecl).
      * split.
        -- rewrite -> (proj1 (proj2 isdecl)). f_equal.
           rewrite -> heq_length.
           symmetry. eapply lift_declared_projection; eauto.
        -- apply (proj2 (proj2 isdecl)).
    + specialize (IHc _ _ _ wf eq_refl).
      rewrite -> lift_mkApps in *. eapply IHc.
    + now rewrite -> map_length.

  - rewrite -> (map_dtype _ (lift #|Γ''| (#|mfix| + #|Γ'|))).
    eapply type_Fix; auto.
    * eapply fix_guard_lift ; eauto.
    * rewrite -> nth_error_map, heq_nth_error. reflexivity.
    * eapply All_map.
      eapply (All_impl X0); simpl.
      intros x [s [Hs Hs']]; exists s.
      now specialize (Hs' _ _ _ wf eq_refl).
    * eapply All_map.
      eapply (All_impl X1); simpl.
      intros x [Hb IH].
      rewrite lift_fix_context.
      specialize (IH Γ (Γ' ,,,  (fix_context mfix)) Γ'' wf).
      rewrite app_context_assoc in IH. specialize (IH eq_refl).
      rewrite lift_context_app Nat.add_0_r app_context_assoc in IH.
      rewrite app_context_length fix_context_length in IH.
      rewrite lift_context_length fix_context_length.
      rewrite permute_lift; try lia. now rewrite (Nat.add_comm #|Γ'|).
    * red; rewrite <-H1. unfold wf_fixpoint.
      rewrite map_map_compose.
      now rewrite weakening_check_one_fix.

  - rewrite -> (map_dtype _ (lift #|Γ''| (#|mfix| + #|Γ'|))).
    eapply type_CoFix; auto.
    * eapply cofix_guard_lift ; eauto.
    * rewrite -> nth_error_map, heq_nth_error. reflexivity.
    * eapply All_map.
      eapply (All_impl X0); simpl.
      intros x [s [Hs Hs']]; exists s.
      now specialize (Hs' _ _ _ wf eq_refl).
    * eapply All_map.
      eapply (All_impl X1); simpl.
      intros x [Hb IH].
      rewrite lift_fix_context.
      specialize (IH Γ (Γ' ,,,  (fix_context mfix)) Γ'' wf).
      rewrite app_context_assoc in IH. specialize (IH eq_refl).
      rewrite lift_context_app Nat.add_0_r app_context_assoc in IH.
      rewrite app_context_length fix_context_length in IH.
      rewrite lift_context_length fix_context_length.
      rewrite permute_lift; try lia. now rewrite (Nat.add_comm #|Γ'|).
    * red; rewrite <-H1. unfold wf_cofixpoint.
      rewrite map_map_compose.
      now rewrite weakening_check_one_cofix.

  - econstructor; eauto; now eapply weakening_cumul.
Qed.

Lemma weakening_typing `{cf : checker_flags} Σ Γ Γ' Γ'' (t : term) :
  wf Σ.1 ->
  wf_local Σ (Γ ,,, Γ'') ->
  forall T, Σ ;;; Γ ,,, Γ' |- t : T ->
       Σ ;;; Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ' |-
       lift #|Γ''| #|Γ'| t : lift #|Γ''| #|Γ'| T.
Proof.
  intros HΣ HΓ'' T H.
  exact ((weakening_typing_prop Σ HΣ _ t T H).2 _ _ _ HΓ'' eq_refl).
Qed.

Lemma weakening_wf_local `{cf : checker_flags} Σ Γ Γ' Γ'' :
  wf Σ.1 ->
  wf_local Σ (Γ ,,, Γ') ->
  wf_local Σ (Γ ,,, Γ'') ->
  wf_local Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ').
Proof.
  intros HΣ HΓΓ' HΓ''.
  exact (env_prop_wf_local _ _ weakening_typing_prop
                           Σ HΣ _ HΓΓ' _ _ _ eq_refl HΓ'').
Qed.

Lemma weakening `{cf : checker_flags} Σ Γ Γ' (t : term) T :
  wf Σ.1 -> wf_local Σ (Γ ,,, Γ') ->
  Σ ;;; Γ |- t : T ->
  Σ ;;; Γ ,,, Γ' |- lift0 #|Γ'| t : lift0 #|Γ'| T.
Proof.
  intros HΣ HΓΓ' * H.
  pose (weakening_typing Σ Γ [] Γ' t).
  forward t0; eauto.
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
    Σ ;;; Γ ,,, Γ' |- M = N ->
    Σ ;;; Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ' |- lift #|Γ''| #|Γ'| M = lift #|Γ''| #|Γ'| N.
Proof.
  intros Σ Γ Γ' Γ'' M N wfΣ. induction 1.
  - constructor.
    now apply lift_eq_term.
  - eapply weakening_red1 in r ; auto.
    econstructor 2 ; eauto.
  - eapply weakening_red1 in r ; auto.
    econstructor 3 ; eauto.
Qed.

Lemma weaken_ctx {cf:checker_flags} {Σ Γ t T} Δ :
  wf Σ.1 -> wf_local Σ Δ ->
  Σ ;;; Γ |- t : T ->
  Σ ;;; Δ ,,, Γ |- t : T.
Proof.
  intros wfΣ wfΔ ty.
  epose proof (weakening_typing Σ [] Γ Δ t wfΣ).
  rewrite !app_context_nil_l in X.
  forward X by eauto using typing_wf_local.
  pose proof (typing_wf_local ty).
  pose proof (closed_wf_local wfΣ (typing_wf_local ty)).
  specialize (X _ ty).
  eapply PCUICClosed.typecheck_closed in ty as [_ closed]; auto.
  move/andb_and: closed => [ct cT].
  rewrite !lift_closed // in X.
  now rewrite closed_ctx_lift in X.
Qed.

Lemma weakening_gen : forall (cf : checker_flags) (Σ : global_env × universes_decl)
  (Γ Γ' : context) (t T : term) n, n = #|Γ'| ->
  wf Σ.1 ->
  wf_local Σ (Γ ,,, Γ') ->
  Σ;;; Γ |- t : T -> Σ;;; Γ ,,, Γ' |- (lift0 n) t : (lift0 n) T.
Proof.
  intros ; subst n; now apply weakening.
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
  unshelve eapply (weakening_typing Σ (skipn n Γ) [] (firstn n Γ) ty _ _ (tSort u)); eauto with wf.
Qed.
