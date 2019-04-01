(* Distributed under the terms of the MIT license.   *)
From Equations Require Import Equations.
From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICWeakeningEnv PCUICWeakening
     PCUICSubstitution PCUICClosed PCUICCumulativity PCUICGeneration PCUICValidity
     PCUICConfluence.
Require Import ssreflect ssrbool.
Require Import String.
From MetaCoq.Template Require Import LibHypsNaming.
Set Asymmetric Patterns.

Existing Instance config.default_checker_flags.

(* Commented otherwise extraction would produce an axiom making the whole
   extracted code unusable *)

Ltac my_rename_hyp h th :=
  match th with
    | (typing _ _ ?t _) => fresh "type" t
    | (All_local_env (@typing _) _ ?G) => fresh "wf" G
    | (All_local_env (@typing _) _ _) => fresh "wf"
    | (All_local_env _ _ ?G) => fresh "H" G
    | context [typing _ _ (_ ?t) _] => fresh "IH" t
  end.

Ltac rename_hyp h ht ::= my_rename_hyp h ht.

Lemma mkApps_Fix_spec mfix idx args t : mkApps (tFix mfix idx) args = t ->
                                      match decompose_app t with
                                      | (tFix mfix idx, args') => args' = args
                                      | _ => False
                                      end.
Proof.
  intros H; apply (f_equal decompose_app) in H.
  rewrite decompose_app_mkApps in H. reflexivity.
  destruct t; noconf H. rewrite <- H. reflexivity.
  simpl. reflexivity.
Qed.

Lemma decompose_app_rec_tFix mfix idx args t l :
  decompose_app_rec t l = (tFix mfix idx, args) -> mkApps t l = mkApps (tFix mfix idx) args.
Proof.
  unfold decompose_app.
  revert l args.
  induction t; intros args l' H; noconf H. simpl in H.
  now specialize (IHt1 _ _ H).
  reflexivity.
Qed.

Lemma decompose_app_tFix mfix idx args t :
  decompose_app t = (tFix mfix idx, args) -> t = mkApps (tFix mfix idx) args.
Proof. apply decompose_app_rec_tFix. Qed.

Inductive context_relation (P : global_context -> context -> context -> context_decl -> context_decl -> Type)
          {Σ} : forall (Γ Γ' : context), Type :=
| ctx_rel_nil : context_relation P nil nil
| ctx_rel_vass na na' T U Γ Γ' :
    context_relation P Γ Γ' ->
    P Σ Γ Γ' (vass na T) (vass na' U) ->
    context_relation P (vass na T :: Γ) (vass na' U :: Γ')
| ctx_rel_def na na' t T u U Γ Γ' :
    context_relation P Γ Γ' ->
    P Σ Γ Γ' (vdef na t T) (vdef na' u U) ->
    context_relation P (vdef na t T :: Γ) (vdef na' u U :: Γ').
Derive Signature for context_relation.
Arguments context_relation P Σ Γ Γ' : clear implicits.

Lemma context_relation_nth {P Σ n Γ Γ' d} :
  context_relation P Σ Γ Γ' -> nth_error Γ n = Some d ->
  { d' & ((nth_error Γ' n = Some d') *
          let Γs := skipn (S n) Γ in
          let Γs' := skipn (S n) Γ' in
          context_relation P Σ Γs Γs' *
          P Σ Γs Γs' d d')%type }.
Proof.
  induction n in Γ, Γ', d |- *; destruct Γ; intros Hrel H; noconf H.
  - depelim Hrel.
    simpl. eexists; intuition eauto.
    eexists; intuition eauto.
  - depelim Hrel.
    destruct (IHn _ _ _ Hrel H).
    cbn -[skipn] in *.
    eexists; intuition eauto.

    destruct (IHn _ _ _ Hrel H).
    eexists; intuition eauto.
Qed.

(* Lemma all_local_env_mix {Σ Γ P Q} : *)
(*   (forall Σ Γ t s s', (P Σ Γ t (tSort s) -> Q Σ Γ t (tSort s)) -> *)
(*                       (P Σ Γ t (tSort s') -> Q Σ Γ t (tSort s'))) -> *)
(*   All_local_env P Σ Γ -> All_local_env Q Σ Γ -> *)
(*   All_local_env (fun Σ Γ t T => (P Σ Γ t T * Q Σ Γ t T)%type) Σ Γ. *)
(* Proof. *)
(*   intros Hsort. induction 1; intros H; depelim H; econstructor; eauto. *)
(* Qed. *)

(* Inductive red1_decls Σ Γ Γ' : forall (x y : context_decl), Type := *)
(* | red1_vass na T T' : red1 Σ Γ T T' -> red1_decls Σ Γ Γ' (vass na T) (vass na T') *)
(* | red1_vdef_type na b T T' : red1 Σ Γ T T' -> red1_decls Σ Γ Γ' (vdef na b T) (vdef na b T') *)
(* | red1_vdef_body na b b' T : red1 Σ Γ b b' -> red1_decls Σ Γ Γ' (vdef na b T) (vdef na b' T). *)

(* Definition red1_context := context_relation red1_decls. *)

Inductive conv_decls Σ Γ Γ' : forall (x y : context_decl), Type :=
| conv_vass na na' T T' : isWfArity_or_Type Σ Γ' T' -> conv Σ Γ T T' ->
                      conv_decls Σ Γ Γ' (vass na T) (vass na' T')

| conv_vdef_type na na' b T T' : isWfArity_or_Type Σ Γ' T' -> conv Σ Γ T T' ->
                             conv_decls Σ Γ Γ' (vdef na b T) (vdef na' b T')

| conv_vdef_body na na' b b' T : Σ ;;; Γ' |- b' : T -> conv Σ Γ b b' ->
                                                  conv_decls Σ Γ Γ' (vdef na b T) (vdef na' b' T).

Notation conv_context := (context_relation conv_decls).
Require Import Equations.Tactics.

(* First needs to show that cumulativity is closed under context conv *)
Lemma wf_conv_context Σ Γ Δ (wfΓ : wf_local Σ Γ) :
  All_local_env_over typing
    (fun (Σ : global_context) (Γ : context) wfΓ (t T : term) Ht =>
       forall Γ' : context, conv_context Σ Γ Γ' -> Σ;;; Γ' |- t : T) Σ Γ wfΓ ->
  conv_context Σ Γ Δ -> wf_local Σ Δ.
Proof.
  intros wfredctx. revert Δ.
  induction wfredctx; intros Δ wfred; unfold vass, vdef in *; depelim wfred. constructor; eauto.
  simpl. constructor. auto. red. depelim c.
  destruct i. red in i. destruct i as [ctx [s [Hs Hwf]]].
Admitted.

Lemma conv_context_refl Σ Γ : wf Σ -> wf_local Σ Γ -> conv_context Σ Γ Γ.
Proof.
  induction Γ; try econstructor.
  destruct a as [na [b|] ty]; intros wfΣ wfΓ; depelim wfΓ; econstructor; eauto;
  constructor; auto.
  unshelve epose (validity _ _ _ _ _ _ l); auto.
  now destruct p. apply conv_refl. simpl in l.
  right; auto. apply conv_refl.
Defined.
Hint Resolve conv_context_refl : pcuic.
(* Lemma wf_red1_context Σ Γ Δ : *)
(*   All_local_env *)
(*     (fun (Σ : global_context) (Γ : context) (t T : term) => *)
(*        forall Γ' : context, red1_context Σ Γ Γ' -> Σ;;; Γ' |- t : T) Σ Γ -> *)
(*   red1_context Σ Γ Δ -> wf_local Σ Γ -> wf_local Σ Δ. *)
(* Proof. *)
(*   intros wfredctx. revert Δ. *)
(*   induction wfredctx; intros Δ wfred; depelim wfred; intros wfH; depelim wfH. constructor. *)
(*   econstructor; auto. *)
(*   constructor. eauto. *)
(*   depelim r. specialize (t0 _ wfred). *)
(*   eapply type_Conv. apply t0. admit. *)
(*   econstructor 2. r. *)
(*   specialize (t0 _ wfred). *)

Arguments skipn : simpl never.

(* Admitted. *)
Set SimplIsCbn.
Lemma context_conversion : env_prop
                             (fun Σ Γ t T =>
                                forall Γ', conv_context Σ Γ Γ' -> Σ ;;; Γ' |- t : T).
Proof.
  apply typing_ind_env; intros Σ wfΣ Γ wfΓ; intros **; rename_all_hyps.
  - eapply (context_relation_nth X0) in heq_nth_error as [d' [Hnth [Hrel Hconv]]].
    eapply type_Conv. econstructor; eauto.
    eapply wf_conv_context; eauto.
Admitted.
(*
    depelim Hconv.
    destruct decl; simpl in *.


    induction X0; econstructor; eauto.
    depelim wfΓ. apply (IHX0 wfΓ). depelim HΓ. auto.
    depelim IHn.
    induction HΓ in Γ', X1 |- *. depelim X1. constructor.
    depelim wfΓ. apply IHHΓ; auto. constructor; auto.

    unshelve epose (all_local_env_mix _ wfΓ HΓ).
    simpl. intros.

    induction wfΓ. depelim X0. constructor.
    apply IHwfΓ.

    eapply All_local_env_impl in HΓ. eapply HΓ.
*)

Lemma type_Lambda_inv Σ Γ na A b U :
  Σ ;;; Γ |- tLambda na A b : U ->
  { s1 & { B &
           (Σ ;;; Γ |- A : tSort s1) *
           (Σ ;;; Γ ,, vass na A |- b : B) *
           (Σ ;;; Γ |- tProd na A B <= U) } }%type.
Proof.
  intros H; depind H.
  exists s1, bty; intuition auto.
  specialize (IHtyping _ _ _ eq_refl).
  destruct IHtyping as [s1 [s2 Hs]].
  eexists _, _; intuition eauto.
  eapply cumul_trans; eauto.
  eapply cumul_trans; eauto.
Qed.

Lemma type_proj_inv Σ Γ p c U :
  Σ;;; Γ |- tProj p c : U ->
  { '(args, mdecl, idecl, pdecl, u) : _ & let ty := snd pdecl in
                                          (Σ;;; Γ |- c : mkApps (tInd (fst (fst p)) u) args) *
                                          (declared_projection (fst Σ) mdecl idecl p pdecl) *
                                          (#|args| = ind_npars mdecl) *
                                          (Σ ;;; Γ |- ((subst0 (c :: List.rev args)) (subst_instance_constr u ty)) <= U) }%type.
Proof.
  intros H; depind H.
  - exists (args, mdecl, idecl, pdecl, u). intuition eauto.
  - destruct (IHtyping _ _ eq_refl) as [ [ [ [ [] ] ] ] [ [ [] ] ]].     
    exists (l, m, o, p0, u). intuition eauto.
    all: eapply cumul_trans; eauto.
Qed.

Lemma type_tLetIn_inv Σ Γ na A b U a :
  Σ ;;; Γ |- tLetIn na a A b : U ->
  { s1 & { B &
           (Σ ;;; Γ |- A : tSort s1) *
           (Σ ;;; Γ |- a : A) *
           (Σ ;;; Γ ,, vdef na a A |- b : B) *
           (Σ ;;; Γ |- tLetIn na a A B <= U) } }%type.
Proof.
  intros H; depind H.
  exists s1, b'_ty; intuition auto.
  specialize (IHtyping _ _ _ _ eq_refl).
  destruct IHtyping as [s1 [s2 Hs]].
  eexists _, _; intuition eauto.
  eapply cumul_trans; eauto.
  eapply cumul_trans; eauto.
Qed.

(** Injectivity of products, the essential property of cumulativity needed for subject reduction. *)
Lemma cumul_Prod_inv Σ Γ na na' A B A' B' :
  Σ ;;; Γ |- tProd na A B <= tProd na' A' B' ->
   ((Σ ;;; Γ |- A = A') * (Σ ;;; Γ ,, vass na' A' |- B <= B'))%type.
Proof.
  intros H; depind H.
  - admit.
    (* simpl in e. move/andP: e => [] eqa leqb. *)
    (* split; auto with pcuic. apply conv_conv_alt; eauto. now constructor. *)
    (* now constructor. *)

  - depelim r. apply mkApps_Fix_spec in x. destruct x.
    specialize (IHcumul _ _ _ _ _ _ eq_refl eq_refl).
    intuition auto. apply conv_conv_alt.
    econstructor 2; eauto. now apply conv_conv_alt.

    specialize (IHcumul _ _ _ _ _ _ eq_refl eq_refl).
    intuition auto. apply cumul_trans with N2.
    econstructor 2; eauto. admit. (* Red conversion *)
    auto.

<<<<<<< HEAD
  - depelim r. solve_discr.
    specialize (IHcumul _ _ _ _ _ _ eq_refl eq_refl).
    intuition auto. apply conv_conv_alt.
    econstructor 3. apply conv_conv_alt. apply a. apply r.
    (* red conversion *) admit.
=======
  - depelim r. (* apply mkApps_Fix_eq in x. discriminate. *)
    (* specialize (IHcumul _ _ _ _ _ _ eq_refl eq_refl). *)
    (* intuition auto. apply conv_conv_alt. *)
    (* econstructor 3. apply conv_conv_alt. apply a. apply r. *)
    (* (* red conversion *) admit. *)
>>>>>>> Prelim state

    (* specialize (IHcumul _ _ _ _ _ _ eq_refl eq_refl). *)
    (* intuition auto. apply cumul_trans with N2. auto. *)
    (* eapply cumul_red_r; eauto. *)
Admitted.

Lemma cumul_Sort_inv Σ Γ s s' :
  Σ ;;; Γ |- tSort s <= tSort s' -> leq_universe (snd Σ) s s'.
Proof.
  intros H; depind H; auto.
<<<<<<< HEAD
  - now inversion l.
  - depelim r. solve_discr.
  - depelim r. solve_discr.
Qed.
=======
  - depelim r. admit. 
  - depelim r. admit.
Admitted.
>>>>>>> Prelim state

Lemma tProd_it_mkProd_or_LetIn na A B ctx s :
  tProd na A B = it_mkProd_or_LetIn ctx (tSort s) ->
  { ctx' & ctx = (ctx' ++ [vass na A])%list /\
           destArity [] B = Some (ctx', s) }.
Proof.
  intros. exists (removelast ctx).
  revert na A B s H.
  induction ctx using rev_ind; intros; noconf H.
  rewrite it_mkProd_or_LetIn_app in H. simpl in H.
  destruct x as [na' [b'|] ty']; noconf H; simpl in *.
  rewrite removelast_app. congruence. simpl. rewrite app_nil_r. intuition auto.
  rewrite destArity_it_mkProd_or_LetIn. simpl. now rewrite app_context_nil_l.
Qed.

Arguments Universe.sort_of_product : simpl nomatch.

Lemma mkApps_inj f a f' l :
  tApp f a = mkApps f' l -> l <> [] ->
  f = mkApps f' (removelast l) /\ (a = last l a).
Proof.
  induction l in f' |- *; simpl; intros H. noconf H. intros Hf. congruence.
  intros . destruct l; simpl in *. now noconf H.
  specialize (IHl _ H). forward IHl by congruence.
  apply IHl.
Qed.

Lemma last_app {A} (l l' : list A) d : l' <> [] -> last (l ++ l') d = last l' d.
Proof.
  revert l'. induction l; simpl; auto. intros.
  destruct l. simpl. destruct l'; congruence. simpl.
  specialize (IHl _ H). apply IHl.
Qed.

Lemma mkApps_nonempty f l :
  l <> [] -> mkApps f l = tApp (mkApps f (removelast l)) (last l f).
Proof.
  destruct l using rev_ind. intros; congruence.
  intros. rewrite <- mkApps_nested. simpl. f_equal.
  rewrite removelast_app. congruence. simpl. now rewrite app_nil_r.
  rewrite last_app. congruence.
  reflexivity.
Qed.

Lemma last_nonempty_eq {A} {l : list A} {d d'} : l <> [] -> last l d = last l d'.
Proof.
  induction l; simpl; try congruence.
  intros. destruct l; auto. apply IHl. congruence.
Qed.

Lemma nth_error_removelast {A} (args : list A) n :
  n < Nat.pred #|args| -> nth_error args n = nth_error (removelast args) n.
Proof.
  induction n in args |- *; destruct args; intros; auto.
  simpl. destruct args. depelim H. reflexivity.
  simpl. rewrite IHn. simpl in H. auto with arith.
  destruct args, n; reflexivity.
Qed.

(** Requires Validity *)
Lemma type_mkApps_inv Σ Γ f u T : wf Σ -> 
  Σ ;;; Γ |- mkApps f u : T ->
  { T' & { U & ((Σ ;;; Γ |- f : T') * (typing_spine Σ Γ T' u U) * (Σ ;;; Γ |- U <= T))%type } }.
Proof.
  intros wfΣ; induction u in f, T |- *. simpl. intros.
  { exists T, T. intuition auto. constructor. }
  intros Hf. simpl in Hf.
  destruct u. simpl in Hf.
  - eapply invert_type_App in Hf as [A' [B' [na' [[Hf' Ha] HA''']]]].
    eexists _, _; intuition eauto.
    econstructor; eauto. eapply validity; eauto with wf.
    constructor.
  - specialize (IHu (tApp f a) T).
    specialize (IHu Hf) as [T' [U' [[H' H''] H''']]].
    eapply invert_type_App in H' as [A' [B' [na' [[Hf' Ha] HA''']]]].
    exists (tProd na' A' B'), U'. intuition; eauto.
    econstructor. eapply validity; eauto with wf.
    eapply cumul_refl'. auto.
    clear -H'' HA'''. depind H''.
    econstructor; eauto. eapply cumul_trans; eauto.
Qed.

Lemma All_rev {A} (P : A -> Type) (l : list A) : All P l -> All P (List.rev l).
Proof.
  induction l using rev_ind. constructor.
  intros. rewrite rev_app_distr. simpl. apply All_app in X as [Alll Allx]. inv Allx.
  constructor; intuition eauto.
Qed.

Require Import Lia.

Lemma nth_error_rev {A} (l : list A) i : i < #|l| ->
  nth_error l i = nth_error (List.rev l) (#|l| - S i).
Proof.
  revert l. induction i. destruct l; simpl; auto.
  induction l using rev_ind; simpl. auto.
  rewrite rev_app_distr. simpl.
  rewrite app_length. simpl.
  replace (#|l| + 1 - 0) with (S #|l|) by lia. simpl.
  rewrite Nat.sub_0_r in IHl. auto with arith.

  destruct l. simpl; auto. simpl. intros. rewrite IHi. lia.
  assert (#|l| - S i < #|l|) by lia.
  rewrite nth_error_app_lt. rewrite List.rev_length; auto.
  reflexivity.
Qed.

Lemma type_tFix_inv Σ Γ mfix idx T : wf Σ ->
  Σ ;;; Γ |- tFix mfix idx : T ->
  { T' & { rarg & {f & (unfold_fix mfix idx = Some (rarg, f)) * (Σ ;;; Γ |- f : T') * (Σ ;;; Γ |- T' <= T) }}}%type.
Proof.
  intros wfΣ H. depind H.
  unfold unfold_fix. rewrite e.
  specialize (nth_error_all e a0) as [Hty Hbody].
  destruct decl as [name ty body rarg]; simpl in *.
  clear e.
  eexists _, _, _. split. split. eauto.
  eapply (substitution _ _ types _ [] _ _ wfΣ); simpl; eauto with wf.
  - subst types. clear -a a0.
    pose proof a0 as a0'. apply All_rev in a0'.
    unfold fix_subst, fix_context. simpl.
    revert a0'. rewrite <- (@List.rev_length _ mfix).
    rewrite rev_mapi. unfold mapi.
    assert (#|mfix| >= #|List.rev mfix|) by (rewrite List.rev_length; lia).
    assert (He :0 = #|mfix| - #|List.rev mfix|) by (rewrite List.rev_length; auto with arith).
    rewrite {3}He. clear He. revert H.
    assert (forall i, i < #|List.rev mfix| -> nth_error (List.rev mfix) i = nth_error mfix (#|List.rev mfix| - S i)).
    { intros. rewrite nth_error_rev. auto.
      now rewrite List.rev_length List.rev_involutive. }
    revert H.
    generalize (List.rev mfix).
    intros l Hi Hlen H.
    induction H. simpl. constructor.
    simpl. constructor. unfold mapi in IHAll.
    simpl in Hlen. replace (S (#|mfix| - S #|l|)) with (#|mfix| - #|l|) by lia.
    apply IHAll. intros. simpl in Hi. specialize (Hi (S i)). apply Hi. lia. lia.
    clear IHAll. destruct p.
    simpl in Hlen. assert ((Nat.pred #|mfix| - (#|mfix| - S #|l|)) = #|l|) by lia.
    rewrite H0. rewrite simpl_subst_k. clear. induction l; simpl; auto with arith.
    eapply type_Fix; auto.
    simpl in Hi. specialize (Hi 0). forward Hi. lia. simpl in Hi.
    rewrite Hi. f_equal. lia.
  - subst types. rewrite simpl_subst_k. now rewrite fix_context_length fix_subst_length.
    auto.
  - destruct (IHtyping mfix idx wfΣ eq_refl) as [T' [rarg [f [[unf fty] Hcumul]]]].
    exists T', rarg, f. intuition auto. eapply cumul_trans; eauto.
    destruct b. eapply cumul_trans; eauto.
Qed.

(** The subject reduction property of the system: *)

Definition SR_red1 (Σ : global_context) Γ t T :=
  forall u (Hu : red1 Σ Γ t u), Σ ;;; Γ |- u : T.

Lemma sr_red1 : env_prop SR_red1.
Proof.
  apply typing_ind_env; intros Σ wfΣ Γ wfΓ; unfold SR_red1; intros **; rename_all_hyps;
    match goal with
    | [H : (_ ;;; _ |- _ <= _) |- _ ] => idtac
    | _ =>
      depelim Hu; try solve [apply mkApps_Fix_spec in x; noconf x];
      try solve [econstructor; eauto]
    end.

  - (* Rel *)
    rewrite heq_nth_error in e. destruct decl as [na b ty]; noconf e.
    simpl.
    pose proof (nth_error_All_local_env_over heq_nth_error X); eauto.
    destruct lookup_wf_local_decl; cbn in *.
    rewrite <- (firstn_skipn (S n) Γ).
    assert(S n = #|firstn (S n) Γ|).
    { rewrite firstn_length_le; auto. apply nth_error_Some_length in heq_nth_error. auto with arith. }
    rewrite {3 4}H. apply weakening; auto.
    now unfold app_context; rewrite firstn_skipn.

  - (* Prod *)
    constructor; eauto.
    eapply (context_conversion _ wfΣ _ _ _ _ typeb).
    constructor. auto with pcuic.
    constructor. right; exists s1; auto. apply conv_conv_alt.
    auto.

  - (* Lambda *)
    eapply type_Conv. eapply type_Lambda; eauto.
    eapply (context_conversion _ wfΣ _ _ _ _ typeb).
    constructor. auto with pcuic.
    constructor. right; auto. exists s1; auto.
    apply conv_conv_alt. auto.
    assert (Σ ;;; Γ |- tLambda n t b : tProd n t bty). econstructor; eauto.
    edestruct (validity _ wfΣ _ wfΓ _ _ X0). apply i.
    eapply cumul_red_r.
    apply cumul_refl'. constructor. apply Hu.

  - (* LetIn body *)
    eapply type_Conv.
    apply (substitution_let _ Γ n b b_ty b' b'_ty wfΣ typeb').
    specialize (typing_wf_local typeb') as wfd.
    assert (Σ ;;; Γ |- tLetIn n b b_ty b' : tLetIn n b b_ty b'_ty). econstructor; eauto.
    edestruct (validity _ wfΣ _ wfΓ _ _ X0). apply i.
    eapply cumul_red_r.
    apply cumul_refl'. constructor.

  - (* LetIn value *)
    eapply type_Conv.
    econstructor; eauto.
    eapply (context_conversion _ wfΣ _ _ _ _ typeb').
    constructor. auto with pcuic. constructor; eauto.
    apply conv_conv_alt; auto.
    assert (Σ ;;; Γ |- tLetIn n b b_ty b' : tLetIn n b b_ty b'_ty). econstructor; eauto.
    edestruct (validity _ wfΣ _ wfΓ _ _ X0). apply i.
    eapply cumul_red_r.
    apply cumul_refl'. now constructor.

  - (* LetIn type annotation *)
    specialize (forall_u _ Hu).
    eapply type_Conv.
    econstructor; eauto.
    eapply type_Conv. eauto. right; exists s1; auto.
    apply red_cumul; eauto.
    eapply (context_conversion _ wfΣ _ _ _ _ typeb').
    constructor. auto with pcuic. constructor; eauto. right; exists s1; auto.
    apply conv_conv_alt; auto.
    assert (Σ ;;; Γ |- tLetIn n b b_ty b' : tLetIn n b b_ty b'_ty). econstructor; eauto.
    edestruct (validity _ wfΣ _ wfΓ _ _ X0). apply i.
    eapply cumul_red_r.
    apply cumul_refl'. now constructor.

  - (* Application *)
    eapply substitution0; eauto.
    pose proof typet as typet'.
    eapply type_Lambda_inv in typet' as [s1 [B' [[Ht Hb] HU]]].
    apply cumul_Prod_inv in HU as [eqA leqB].

    eapply type_Conv; eauto.
    unshelve eapply (context_conversion _ wfΣ _ _ _ _ Hb). eauto with wf.
    constructor. auto with pcuic. constructor; eauto.
    apply (validity _ wfΣ _ wfΓ _ _ typeu).
    destruct (validity _ wfΣ _ wfΓ _ _ typet).
    clear -i.
    (** Awfully complicated for a well-formedness condition *)
    { destruct i as [[ctx [s [Hs Hs']]]|[s Hs]].
      left.
      simpl in Hs.
      generalize (destArity_spec ([],, vass na A) B). rewrite Hs.
      intros. simpl in H.
      apply tProd_it_mkProd_or_LetIn in H.
      destruct H as [ctx' [-> Hb]].
      exists ctx', s.
      intuition auto. rewrite app_context_assoc in Hs'. apply Hs'.
      right. exists s.
      eapply type_Prod_invert in Hs as [s1 [s2 [[Ha Hp] Hp']]].
      eapply type_Conv; eauto.
      left. exists [], s. intuition auto. now apply typing_wf_local in Hp.
      apply cumul_Sort_inv in Hp'.
      eapply cumul_trans with (tSort (Universe.sort_of_product s1 s2)).
      constructor.
      cbn. constructor. apply leq_universe_product_r.
      constructor; constructor ; auto. }

  - (* Fixpoint unfolding *)
    simpl in x.
    assert (args <> []) by (destruct args; simpl in *; congruence).
    symmetry in x. apply mkApps_inj in x as [-> Hu]; auto.
    rewrite mkApps_nonempty; auto.
    epose (last_nonempty_eq H). rewrite <- Hu in e1. rewrite <- e1.
    clear e1.
    specialize (type_mkApps_inv _ _ _ _ _ wfΣ typet) as [T' [U' [[appty spty] Hcumul]]].
    specialize (validity _ wfΣ _ wfΓ _ _ appty) as [_ vT'].
    eapply type_tFix_inv in appty as [T [arg [fn' [[Hnth Hty]]]]]; auto.
    rewrite e in Hnth. noconf Hnth.
    eapply type_App.
    eapply type_Conv.
    eapply type_mkApps. eapply type_Conv; eauto. eapply spty.
    eapply validity; eauto.
    eauto. eauto.

  - (* Congruence *)
    eapply type_Conv; [eapply type_App| |]; eauto with wf.
    eapply validity. eauto. eauto.
    eapply type_App; eauto. eapply red_cumul_inv.
    eapply (red_red Σ Γ [vass na A] [] [u] [N2]); auto.
    constructor. constructor. now rewrite subst_empty.

  - (* Constant unfolding *)
    eapply declared_constant_inv in wfΣ; eauto with pcuic.
    destruct decl0 as [ty body' univs]; simpl in *; subst body'.
    hnf in wfΣ. simpl in wfΣ. (* Substitutivity of typing w.r.t. universes *) admit.
    eapply weaken_env_prop_typing.

  - (* iota reduction *) admit.
  - (* Case congruence *) admit.
  - (* Case congruence *) admit.
  - (* Case congruence *) admit.
  - (* Case congruence *) admit.
  - (* Proj CoFix congruence *) admit.
  - (* Proj Constructor congruence *) admit.
  - (* Proj reduction *) admit.
  - (* Fix congruence *)
    apply mkApps_Fix_spec in x. simpl in x. subst args.
    simpl. destruct narg; discriminate.
  - (* Fix congruence *)
    admit.
  - (* Fix congruence *)
    admit.
  - (* CoFix congruence *)
    admit.
  - (* CoFix congruence *)
    admit.
  - (* Conversion *)
    specialize (forall_u _ Hu).
    eapply type_Conv; eauto.
    destruct X2 as [[wf _]|[s Hs]].
    now left.
    now right.
Admitted.

Definition sr_stmt (Σ : global_context) Γ t T :=
  forall u, red Σ Γ t u -> Σ ;;; Γ |- u : T.

Theorem subject_reduction : forall (Σ : global_context) Γ t u T,
  wf Σ -> Σ ;;; Γ |- t : T -> red Σ Γ t u -> Σ ;;; Γ |- u : T.
Proof.
  intros * wfΣ Hty Hred.
  induction Hred. auto.
  eapply sr_red1 in IHHred; eauto with wf. now apply IHHred.
Qed.
