
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

Lemma exchange_urenaming P Γ Γl Γr Δ :
  noccur_between_ctx 0 #|Γl| Γr ->
  urenaming P
    (exchange_contexts Γ Γl Γr Δ)
    (Γ ,,, Γl ,,, Γr ,,, Δ)
    (exchange_renaming #|Γl| #|Γr| #|Δ|).
Proof.
  intros nocc i d hpi hnth.
  rewrite lookup_exchange_contexts hnth => /=.
  eexists; split; eauto.
  pose proof (exchange_lift_rename nocc hnth).
  rewrite !rename_compose /lift_renaming /=. 
  destruct d as [na [b|] ty]; noconf H; simpl in *.
  - split => //.
    split => //.
    f_equal.
    rewrite !rename_compose.
    rewrite /lift_renaming /= //. 
  - split => //.
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
      + setoid_rewrite shiftn_exchange_renaming. apply exchange_urenaming.
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
