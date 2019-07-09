(* Distributed under the terms of the MIT license.   *)
Set Warnings "-notation-overridden".

From Equations Require Import Equations.
From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICWeakeningEnv PCUICWeakening
     PCUICSubstitution PCUICClosed PCUICCumulativity PCUICGeneration
     PCUICSubstitution PCUICClosed PCUICCumulativity PCUICGeneration PCUICReduction
     PCUICParallelReduction PCUICEquality
     PCUICValidity PCUICParallelReductionConfluence PCUICConfluence
     PCUICInversion PCUICPrincipality.

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

Inductive context_relation (P : context -> context -> context_decl -> context_decl -> Type)
          : forall (Γ Γ' : context), Type :=
| ctx_rel_nil : context_relation P nil nil
| ctx_rel_vass na na' T U Γ Γ' :
    context_relation P Γ Γ' ->
    P Γ Γ' (vass na T) (vass na' U) ->
    context_relation P (vass na T :: Γ) (vass na' U :: Γ')
| ctx_rel_def na na' t T u U Γ Γ' :
    context_relation P Γ Γ' ->
    P Γ Γ' (vdef na t T) (vdef na' u U) ->
    context_relation P (vdef na t T :: Γ) (vdef na' u U :: Γ').
Derive Signature for context_relation.
Arguments context_relation P Γ Γ' : clear implicits.

Lemma context_relation_nth {P n Γ Γ' d} :
  context_relation P Γ Γ' -> nth_error Γ n = Some d ->
  { d' & ((nth_error Γ' n = Some d') *
          let Γs := skipn (S n) Γ in
          let Γs' := skipn (S n) Γ' in
          context_relation P Γs Γs' *
          P Γs Γs' d d')%type }.
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

Require Import CRelationClasses.

Lemma context_relation_trans P :
  (forall Γ Γ' Γ'' x y z,
      context_relation P Γ Γ' ->
      context_relation P Γ' Γ'' ->
      context_relation P Γ Γ'' ->
      P Γ Γ' x y -> P Γ' Γ'' y z -> P Γ Γ'' x z) ->
  Transitive (context_relation P).
Proof.
  intros HP x y z H. induction H in z |- *; auto;
  intros H'; depelim H'; try constructor; auto.
  specialize (IHcontext_relation _ H').
  eapply (HP _ _ _ _ _ _ H H'); eauto.
  eapply (HP _ _ _ _ _ _ H H'); eauto.
Qed.

Inductive conv_decls Σ Γ Γ' : forall (x y : context_decl), Type :=
| conv_vass na na' T T' :
    isType Σ Γ' T' ->
    Σ ;;; Γ |- T = T' ->
    conv_decls Σ Γ Γ' (vass na T) (vass na' T')

| conv_vdef_type na na' b T T' :
    isType Σ Γ' T' ->
    Σ ;;; Γ |- T = T' ->
    conv_decls Σ Γ Γ' (vdef na b T) (vdef na' b T')

| conv_vdef_body na na' b b' T T' :
    isType Σ Γ' T' ->
    Σ ;;; Γ' |- b' : T' ->
    Σ ;;; Γ |- b = b' ->
    Σ ;;; Γ |- T = T' ->
    conv_decls Σ Γ Γ' (vdef na b T) (vdef na' b' T').

Notation conv_context Σ Γ Γ' := (context_relation (@conv_decls Σ) Γ Γ').
Require Import Equations.Tactics.

Hint Resolve conv_refl : pcuic.

Lemma conv_ctx_refl Σ Γ : wf Σ -> wf_local Σ Γ -> conv_context Σ Γ Γ.
Proof.
  induction Γ; try econstructor.
  destruct a as [na [b|] ty]; intros wfΣ wfΓ; depelim wfΓ; econstructor; eauto;
  constructor; pcuic; eapply conv_refl.
Qed.

Hint Resolve conv_ctx_refl : pcuic.

Arguments skipn : simpl never.

Set SimplIsCbn.
Require Import Lia.

Lemma weakening_cumul0 `{CF:checker_flags} Σ Γ Γ'' M N n :
  wf Σ -> n = #|Γ''| ->
  Σ ;;; Γ |- M <= N ->
  Σ ;;; Γ ,,, Γ'' |- lift0 n M <= lift0 n N.
Proof. intros; subst; now apply (weakening_cumul _ _ []). Qed.

Hint Constructors red1 : pcuic.
Hint Resolve refl_red : pcuic.

Lemma red1_red_ctx (Σ : global_context) Γ Γ' T U : wf Σ ->
  red1 Σ Γ T U ->
  @red_ctx Σ Γ Γ' ->
  ∑ t, red Σ Γ' T t * red Σ Γ' U t.
Proof.
  intros wfΣ r H. revert Γ' H.
  Ltac t := split; [eapply red1_red; try econstructor; eauto|try constructor]; eauto with pcuic.
  Ltac u := intuition eauto with pcuic.

  simpl in *. induction r using red1_ind_all; intros;
  try solve [eexists; t]; try destruct (IHr _ H) as [? [? ?]].

  - pose proof H0.
    eapply nth_error_pred1_ctx_l in X as [body' [? ?]]; eauto.
    exists (lift0 (S i) body'). split; eauto with pcuic.
    rewrite -(firstn_skipn (S i) Γ').
    epose proof (weakening_red _ _ [] (firstn (S i) Γ) _ _ wfΣ r).
    rewrite firstn_length_le in X.
    destruct (nth_error Γ i) eqn:Heq => //.
    now eapply nth_error_Some_length in Heq.
    simpl lift_context in X.
    (* Need IH on local decl bodies *)
    admit.

  - firstorder auto with pcuic.
    exists (tLambda na x N). split; apply red_abs; auto.

  - destruct (IHr (Γ' ,, vass na N)). constructor; pcuic.
    exists (tLambda na N x). split; apply red_abs; u.

  - exists (tLetIn na x t b'). split; eapply red_letin; auto.
  - specialize (IHr (Γ' ,, vdef na b t)).
    forward IHr. constructor; eauto. red. eauto.
    destruct IHr as [? [? ?]].
    exists (tLetIn na b t x). split; eapply red_letin; auto.
  - exists (tCase ind x c brs). u; now apply red_case_p.
  - exists (tCase ind p x brs). u; now apply red_case_c.
  - eexists. split. apply red_case_one_brs. admit. admit.
    (* simpl. intuition auto. simpl in *. subst. *)
    (* destruct (b2 _ H) as [? [? ?]]. *)
    (* u. *)
    (* exists (tCase ind p c brs). u; now apply red_case_c. *)
  - exists (tProj p x). u; now eapply red_proj_c.
  - exists (tApp x M2). u; now eapply red_app.
  - exists (tApp M1 x). u; now eapply red_app.
  - exists (tProd na x M2). u; now eapply red_prod.
  - specialize (IHr (Γ' ,, vass na M1)) as [? [? ?]].
    constructor; pcuic.
    exists (tProd na M1 x). u; now eapply red_prod.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

Lemma red_confluence {Σ Γ t u v} : wf Σ ->
  red Σ Γ t u -> red Σ Γ t v ->
  ∃ v', red Σ Γ u v' * red Σ Γ v v'.
Proof.
  move=> wfΣ H H'. apply red_alt in H. apply red_alt in H'.
  destruct (red1_confluent wfΣ _ _ _ _ H H') as [nf [redl redr]].
  apply red_alt in redl; apply red_alt in redr.
  exists nf; intuition auto.
Qed.

Lemma red_red_ctx {Σ Γ Γ' T U} : wf Σ ->
  red Σ Γ T U ->
  @red_ctx Σ Γ Γ' ->
  ∑ t, red Σ Γ' T t * red Σ Γ' U t.
Proof.
  intros wfΣ H. apply red_alt in H.
  induction H. now apply red1_red_ctx.
  intros. exists x. pcuic.
  intros Hctx.
  destruct (IHclos_refl_trans1 Hctx) as [? [? ?]].
  destruct (IHclos_refl_trans2 Hctx) as [? [? ?]].
  destruct (red_confluence wfΣ r0 r1).
  destruct p. exists x2. split; auto. now transitivity x0.
  now transitivity x1.
Qed.

Lemma OnOne2_sym {A} (P : A -> A -> Type) l l' : OnOne2 (fun x y => P y x) l' l -> OnOne2 P l l'.
Proof.
  induction 1; constructor; auto.
Qed.

Instance refl_eq_univ φ : Reflexive (eq_universe φ).
Admitted.

Instance eq_univ_trans φ : Transitive (eq_universe φ).
Admitted.

Instance refl_leq_univ φ : Reflexive (leq_universe φ).
Admitted.

Instance leq_univ_trans φ : Transitive (leq_universe φ).
Admitted.

Existing Class SubstUnivPreserving.

Instance eq_univ_substu φ : SubstUnivPreserving (eq_universe φ).
Admitted.

Instance leq_univ_substu φ : SubstUnivPreserving (leq_universe φ).
Admitted.

Ltac tc := try typeclasses eauto 10.

Lemma eq_universe_leq_incl φ : forall u u' : universe, eq_universe φ u u' -> leq_universe φ u u'.
Admitted.

Hint Resolve eq_universe_leq_incl : pcuic.

Section RedCtxProof.
  Context {Re Rle} {refl : Reflexive Re} {refl' :Reflexive Rle}
          {trre : Transitive Re} {trle : Transitive Rle} `{SubstUnivPreserving Re} `{SubstUnivPreserving Rle}.
  Context (inclre : forall u u' : universe, Re u u' -> Rle u u').

  Lemma red1_red1_ctx_upto {Σ Γ T V U} :
    wf Σ ->
    eq_term_upto_univ Re Rle T U -> red1 Σ Γ U V ->
    ∑ T', red1 Σ Γ T T' * eq_term_upto_univ Re Rle T' V.
  Proof.
    intros wfΣ leqTU redUV.
    revert T leqTU.
    revert U V redUV.
    induction U using term_forall_list_ind; intros V reduv T leqTU; depelim leqTU;
      depelim reduv; solve_discr.
    all:try solve [eexists; split; repeat (eauto; constructor)].
    - eexists. split. constructor. eauto.
      eapply reflexivity.

    - eapply OnOne2_All_mix_left in X; eauto. simpl in X. clear o.
      induction X. depelim a.
      destruct p.
      specialize (s _ r).
      pose proof e.
      eapply eq_term_upto_univ_leq in X; eauto.
      specialize (s _ X).
      destruct s as [T' [redx leqT']].
      exists (tEvar n (T' :: l)). split; auto. constructor. constructor. auto.
      constructor; auto. constructor; auto.
      eapply eq_term_upto_univ_leq. auto. admit.
      admit.

  Admitted.

  Lemma red_red_ctx_upto {Σ Γ T V U} :
    wf Σ ->
    eq_term_upto_univ Re Rle T U -> red Σ Γ U V ->
    ∑ T', red Σ Γ T T' * eq_term_upto_univ Re Rle T' V.
  Admitted.

  (* Lemma red_red_ctx_upto_r {Σ Γ T V U} : *)
  (*   wf Σ -> *)
  (*   red Σ Γ T U -> eq_term_upto_univ Re Rle U V -> *)
  (*   ∑ T', red Σ Γ T' V * eq_term_upto_univ Re Rle T' U. *)
  (* Admitted. *)

  (* Lemma red_red_ctx_upto {Σ Γ Γ' T V U} : wf Σ -> *)
  (*    red Σ Γ T U -> leq_term (snd Σ) V U -> *)
  (*    @red_ctx Σ Γ Γ' -> *)
  (*    ∑ t, red Σ Γ' T t * red Σ Γ' U t * leq_term (snd Σ) V t. *)
  (* Proof. *)
  (*   intros wfΣ H. apply red_alt in H. *)
  (*   induction H. intros. *)
  (*   eapply red1_red_ctx in r; eauto. *)
  (*   destruct r as [? [? ?]]. *)

End RedCtxProof.

Lemma red_eq_term_upto_univ_l {Σ : global_context} {Re Rle Γ} u v u' :
    Reflexive Re ->
    Reflexive Rle ->
    Transitive Re ->
    Transitive Rle ->
    SubstUnivPreserving Re ->
    SubstUnivPreserving Rle ->
    (forall u u' : universe, Re u u' -> Rle u u') ->
    eq_term_upto_univ Re Rle u u' ->
    red Σ Γ u v ->
    ∑ v',
      red Σ Γ u' v' *
      eq_term_upto_univ Re Rle v v'.
Proof.
  intros.
  eapply red_alt in X7.
  induction X7 in u', X6 |- *.
  - destruct (red1_eq_term_upto_univ_l Σ Re Rle Γ x y u'); auto.
    destruct p. exists x0. split; auto.
  - exists u'. split; auto.
  - destruct (IHX7_1 _ X6) as [? [? ?]].
    destruct (IHX7_2 _ e) as [? [? ?]].
    exists x1. split. transitivity x0; auto.
    auto.
Qed.

Lemma cumul_red_ctx(Σ : global_context) Γ Γ' T U : wf Σ ->
  Σ ;;; Γ |- T <= U ->
  @red_ctx Σ Γ Γ' ->
  Σ ;;; Γ' |- T <= U.
Proof.
  intros wfΣ H Hctx.
  apply cumul_alt in H as [v [v' [[redl redr] leq]]].
  destruct (red_red_ctx wfΣ redl Hctx) as [lnf [redl0 redr0]].
  apply cumul_alt.
  eapply red_eq_term_upto_univ_l in leq; eauto. all:tc; pcuic.
  destruct leq as [? [? ?]].
  destruct (red_red_ctx wfΣ redr Hctx) as [rnf [redl1 redr1]].
  destruct (red_confluence wfΣ r redr1). destruct p.
  edestruct (red_red_ctx_upto (eq_universe_leq_incl _) wfΣ e r0) as [lnf' [? ?]].
  exists lnf', x0. intuition auto. now transitivity lnf.
  now transitivity rnf.
Qed.

Lemma cumul_red_ctx_inv (Σ : global_context) Γ Γ' T U : wf Σ ->
  Σ ;;; Γ |- T <= U ->
  @red_ctx Σ Γ' Γ ->
  Σ ;;; Γ' |- T <= U.
Proof.
  intros wfΣ H Hctx.
  apply cumul_alt in H as [v [v' [[redl redr] leq]]].
  pose proof (PCUICConfluence.red_red_ctx wfΣ _ _ _ _ redl Hctx).
  pose proof (PCUICConfluence.red_red_ctx wfΣ _ _ _ _ redr Hctx).
  apply cumul_alt.
  exists v, v'.
  split. pcuic. auto.
Qed.

Lemma conv_red_ctx {Σ : global_context} {Γ Γ' T U} : wf Σ ->
  Σ ;;; Γ |- T = U ->
  @red_ctx Σ Γ Γ' ->
  Σ ;;; Γ' |- T = U.
Proof.
  intros wfΣ H Hctx.
  split; eapply cumul_red_ctx; eauto; eapply H.
Qed.

Lemma conv_red_ctx_inv {Σ : global_context} {Γ Γ' T U} : wf Σ ->
  Σ ;;; Γ |- T = U ->
  @red_ctx Σ Γ' Γ ->
  Σ ;;; Γ' |- T = U.
Proof.
  intros wfΣ H Hctx.
  split; eapply cumul_red_ctx_inv; eauto; eapply H.
Qed.

Lemma red1_conv_confluent (Σ : global_context) Γ Γ' T v :
  red1 Σ Γ T v -> conv_context Σ Γ Γ' ->
  ∑ v', red Σ Γ' T v' * red Σ Γ T v'.
Proof.
  intros H. revert Γ'. destruct Σ as [Σ uc].
  simpl in *. induction H using red1_ind_all; intros;
  try solve [eexists; intuition eauto].
Qed.

Lemma red_conv_confluent (Σ : global_context) Γ Γ' T v :
  red Σ Γ T v ->
  conv_context Σ Γ Γ' ->
  ∑ v', red Σ Γ' T v' * red Σ Γ T v'.
Proof.
  intros H. induction H. intros; intuition eauto.
  intros.
  eapply red1_conv_confluent in r; eauto.
Qed.

Arguments red_ctx : clear implicits.

Lemma red_eq_context_upto_l {Σ : global_context} {Re Γ Δ u v}
      `{Reflexive _ Re} `{Transitive _ Re} `{SubstUnivPreserving Re} :
  wf Σ ->
  red Σ Γ u v ->
  eq_context_upto Re Γ Δ ->
  ∑ v',
  red Σ Δ u v' *
  eq_term_upto_univ Re Re v v'.
Proof.
  intros wfΣ r HΓ.
  eapply red_alt in r.
  induction r.
  - eapply red1_eq_context_upto_l in r; eauto.
    destruct r as [v [? ?]]. exists v. intuition pcuic.
    now eapply red1_red.
  - exists x. split; auto. reflexivity.
  - destruct IHr1 as [v' [? ?]].
    destruct IHr2 as [v'' [? ?]].
    eapply (red_eq_term_upto_univ_l y v'' v') in e; tc. all:pcuic.
    destruct e as [? [? ?]].
    exists x0; split; eauto.
    now transitivity v'.
    eapply eq_term_upto_univ_trans with v''; auto.
Qed.

Lemma conv_context_red_context (Σ : global_context) Γ Γ' :
  wf Σ ->
  conv_context Σ Γ Γ' ->
  ∑ Δ Δ', red_ctx Σ Γ Δ * red_ctx Σ Γ' Δ' * eq_context_upto (eq_universe (snd Σ)) Δ Δ'.
Proof.
  intros wfΣ Hctx.
  induction Hctx.
  - exists [], []; intuition pcuic. constructor.
  - destruct IHHctx as [Δ [Δ' [[? ?] ?]]].
    depelim p.
    pose proof (conv_red_ctx wfΣ c r).
    eapply conv_conv_alt, conv_alt_red in X.
    destruct X as [T' [U' [? [? ?]]]].
    pose proof (PCUICConfluence.red_red_ctx wfΣ _ _ _ _ r1 r).
    pose proof (PCUICConfluence.red_red_ctx wfΣ _ _ _ _ r2 r).
    destruct (red_eq_context_upto_l wfΣ r1 e). destruct p.
    destruct (red_eq_context_upto_l wfΣ r2 e). destruct p.
    exists (Δ ,, vass na' T'), (Δ' ,, vass na' x0).
    split; [split|]; constructor; auto. red.
    eapply PCUICConfluence.red_red_ctx; eauto.
    eapply eq_term_upto_univ_trans with U'; eauto; tc.
  - destruct IHHctx as [Δ [Δ' [[? ?] ?]]].
    depelim p.
    * pose proof (conv_red_ctx wfΣ c r).
      eapply conv_conv_alt, conv_alt_red in X.
      destruct X as [T' [U' [? [? ?]]]].
      pose proof (PCUICConfluence.red_red_ctx wfΣ _ _ _ _ r1 r).
      pose proof (PCUICConfluence.red_red_ctx wfΣ _ _ _ _ r2 r).
      destruct (red_eq_context_upto_l wfΣ r1 e). destruct p.
      destruct (red_eq_context_upto_l wfΣ r2 e). destruct p.
      exists (Δ ,, vdef na' u T'), (Δ' ,, vdef na' u x0).
      split; [split|]; constructor; auto. red. split; auto. red. split; auto.
      eapply PCUICConfluence.red_red_ctx; eauto.
      reflexivity.
      eapply eq_term_upto_univ_trans with U'; eauto; tc.
    * pose proof (conv_red_ctx wfΣ c r).
      eapply conv_conv_alt, conv_alt_red in X.
      destruct X as [t' [u' [? [? ?]]]].
      pose proof (PCUICConfluence.red_red_ctx wfΣ _ _ _ _ r1 r).
      pose proof (PCUICConfluence.red_red_ctx wfΣ _ _ _ _ r2 r).
      destruct (red_eq_context_upto_l wfΣ r1 e) as [t'' [? ?]].
      destruct (red_eq_context_upto_l wfΣ r2 e) as [u'' [? ?]].
      pose proof (conv_red_ctx wfΣ c0 r) as hTU.
      eapply conv_conv_alt, conv_alt_red in hTU.
      destruct hTU as [T' [U' [rT [rU eTU']]]].
      pose proof (PCUICConfluence.red_red_ctx wfΣ _ _ _ _ rT r).
      pose proof (PCUICConfluence.red_red_ctx wfΣ _ _ _ _ rU r).
      destruct (red_eq_context_upto_l wfΣ rT e) as [T'' [? ?]].
      destruct (red_eq_context_upto_l wfΣ rU e) as [U'' [? ?]].
      exists (Δ ,, vdef na' t' T'), (Δ' ,, vdef na' u'' U'').
      split; [split|]. all: constructor ; auto.
      -- red. split; auto.
      -- red. split.
         ++ eapply PCUICConfluence.red_red_ctx; eauto.
         ++ eapply PCUICConfluence.red_red_ctx; eauto.
      -- eapply eq_term_upto_univ_trans with u'; eauto; tc.
      -- eapply eq_term_upto_univ_trans with U'; eauto; tc.
Qed.

Lemma cumul_eq_context_upto {Σ : global_context} {Γ Δ T U} :
  wf Σ ->
  eq_context_upto (eq_universe (snd Σ)) Γ Δ ->
  Σ ;;; Γ |- T <= U ->
  Σ ;;; Δ |- T <= U.
Proof.
  intros wfΣ eqctx cum.
  eapply cumul_alt in cum as [nf [nf' [[redl redr] ?]]].
  eapply (red_eq_context_upto_l (Re:=eq_universe _)) in redl; eauto.
  eapply (red_eq_context_upto_l (Re:=eq_universe _)) in redr; eauto.
  destruct redl as [v' [redv' eqv']].
  destruct redr as [v'' [redv'' eqv'']].
  eapply cumul_alt. exists v', v''; intuition auto.
  eapply leq_term_trans with nf.
  apply eq_term_leq_term. now apply eq_term_sym.
  eapply leq_term_trans with nf'; auto.
  now apply eq_term_leq_term.
Qed.

Lemma cumul_conv_ctx (Σ : global_context) Γ Γ' T U : wf Σ ->
  Σ ;;; Γ |- T <= U ->
  conv_context Σ Γ Γ' ->
  Σ ;;; Γ' |- T <= U.
Proof.
  intros wfΣ H Hctx.
  apply conv_context_red_context in Hctx => //.
  destruct Hctx as [Δ [Δ' [[l r] elr]]].
  eapply cumul_red_ctx in l; eauto.
  eapply cumul_red_ctx_inv in r; eauto.
  eapply cumul_eq_context_upto; eauto.
Qed.

Lemma conv_conv_ctx (Σ : global_context) Γ Γ' T U : wf Σ ->
  Σ ;;; Γ |- T = U ->
  conv_context Σ Γ Γ' ->
  Σ ;;; Γ' |- T = U.
Proof.
  intros wfΣ H Hctx. destruct H.
  eapply cumul_conv_ctx in c; eauto.
  eapply cumul_conv_ctx in c0; eauto.
  now split.
Qed.

Lemma conv_isWfArity_or_Type Σ Γ Γ' T U :
  conv_context Σ Γ' Γ ->
  Σ ;;; Γ |- T = U ->
  isWfArity_or_Type Σ Γ T ->
  isWfArity_or_Type Σ Γ' U.
Proof.
Admitted.

Lemma wf_local_conv_ctx Σ Γ Δ (wfΓ : wf_local Σ Γ) :
  wf Σ ->
  All_local_env_over typing
    (fun (Σ : global_context) (Γ : context) wfΓ (t T : term) Ht =>
       forall Γ' : context, conv_context Σ Γ Γ' -> Σ;;; Γ' |- t : T) Σ Γ wfΓ ->
  conv_context Σ Γ Δ -> wf_local Σ Δ.
Proof.
  intros wfΣ wfredctx. revert Δ.
  induction wfredctx; intros Δ wfred; unfold vass, vdef in *; depelim wfred.
  - constructor; eauto.
  - simpl. constructor. auto. red. depelim c. apply i.
  - simpl. depelim c. constructor; auto; hnf.
    eapply type_Conv; eauto. eapply cumul_conv_ctx; eauto. apply c.
    constructor; auto.
Qed.

Lemma conv_context_sym Σ Γ Γ' :
  wf Σ -> wf_local Σ Γ -> conv_context Σ Γ Γ' -> conv_context Σ Γ' Γ.
Proof.
  induction Γ in Γ' |- *; try econstructor.
  intros wfΣ wfΓ conv; depelim conv; econstructor; eauto;
  constructor; pcuic. intros.
  depelim X1; depelim X0; constructor; pcuic.
  - depelim c. constructor. apply l.
    eapply conv_sym, conv_conv_ctx; eauto.
  - depelim c; constructor; auto.
    eapply conv_sym, conv_conv_ctx; eauto.
    eapply conv_sym, conv_conv_ctx; eauto.
    eapply conv_sym, conv_conv_ctx; eauto.
Qed.

(** Maybe need to prove it later *)
Lemma conv_context_trans Σ : wf Σ -> CRelationClasses.Transitive (fun Γ Γ' => conv_context Σ Γ Γ').
Proof.
  intros wfΣ.
  eapply context_relation_trans.
  intros.
  depelim X2; depelim X3; try constructor; auto.
  eapply conv_trans; eauto.
  eapply conv_conv_ctx => //. apply c0.
  apply conv_context_sym => //. pcuic. admit.
  eapply conv_trans; eauto.
  eapply conv_conv_ctx => //. apply c0.
  apply conv_context_sym => //. admit.
Admitted.

Hint Immediate wf_local_conv_ctx : pcuic.
Hint Constructors conv_decls : pcuic.

Lemma context_conversion : env_prop
                             (fun Σ Γ t T =>
                                forall Γ', conv_context Σ Γ Γ' -> Σ ;;; Γ' |- t : T).
Proof.
  apply typing_ind_env; intros Σ wfΣ Γ wfΓ; intros **; rename_all_hyps;
    try solve [econstructor; eauto]; try solve [econstructor; pcuic; auto; constructor; pcuic].

  - pose proof heq_nth_error.
    eapply (context_relation_nth X0) in H as [d' [Hnth [Hrel Hconv]]].
    eapply type_Conv.
    * econstructor.
      eapply wf_local_conv_ctx; eauto. eauto.
    * admit.
    * unshelve eapply nth_error_All_local_env_over in X. 3:eapply heq_nth_error.
      destruct X. red in o.
      depelim Hconv; simpl in *.
      + rewrite -(firstn_skipn (S n) Γ').
        eapply weakening_cumul0; auto.
        pose proof (nth_error_Some_length Hnth).
        rewrite firstn_length_le; lia.
        apply conv_sym in c. clear -wfΣ X0 c.
        eapply cumul_conv_ctx; eauto. apply c.
        admit.
      + simpl in *.
        admit.
      + simpl in *. auto.
        admit.
  - constructor; pcuic.
    eapply forall_Γ'0. repeat (constructor; pcuic).
    eexists; now eapply forall_Γ'.
  - econstructor; pcuic.
    eapply forall_Γ'0. repeat (constructor; pcuic).
    eexists; now eapply forall_Γ'.
  - econstructor; pcuic.
    eapply forall_Γ'1. repeat (constructor; pcuic).
    eexists; now eapply forall_Γ'.
  - econstructor; pcuic. eauto. eauto. solve_all.
  - econstructor; pcuic. admit.
    solve_all.
    apply b. subst types.
    admit.
  - econstructor; pcuic. admit.
    solve_all.
    apply b. subst types.
    admit.
  - econstructor; eauto.
    destruct X2. destruct i. left. admit.
    right. destruct s as [s [ty ?]]. exists s. eauto.
    eapply cumul_conv_ctx; eauto.
Admitted.

(** Injectivity of products, the essential property of cumulativity needed for subject reduction. *)
Lemma cumul_Prod_inv Σ Γ na na' A B A' B' :
  wf Σ -> wf_local Σ Γ ->
  Σ ;;; Γ |- tProd na A B <= tProd na' A' B' ->
   ((Σ ;;; Γ |- A = A') * (Σ ;;; Γ ,, vass na' A' |- B <= B'))%type.
Proof.
  intros wfΣ wfΓ H; depind H.
  - depelim l.
    split; auto.
    eapply conv_conv_alt.
    now constructor.
    now constructor.

  - depelim r. apply mkApps_Fix_spec in x. destruct x.
    specialize (IHcumul _ _ _ _ _ _ wfΣ wfΓ eq_refl eq_refl).
    intuition auto. apply conv_conv_alt.
    econstructor 2; eauto. now apply conv_conv_alt.

    specialize (IHcumul _ _ _ _ _ _ wfΣ wfΓ eq_refl eq_refl).
    intuition auto. apply cumul_trans with N2.
    eapply cumul_conv_ctx; eauto.

    econstructor 2. eauto. constructor. auto.
    (* now apply conv_ctx_refl. We should not force the same names? *)
    admit. auto.

  - depelim r. solve_discr.
    specialize (IHcumul _ _ _ _ _ _ wfΣ wfΓ eq_refl eq_refl).
    intuition auto. apply conv_conv_alt.
    econstructor 3. apply conv_conv_alt. apply a. apply r.
    (* red conversion *) admit.

    specialize (IHcumul _ _ _ _ _ _ wfΣ wfΓ eq_refl eq_refl).
    intuition auto. apply cumul_trans with N2. auto.
    eapply cumul_red_r; eauto.
Admitted.

Lemma cumul_Sort_inv Σ Γ s s' :
  Σ ;;; Γ |- tSort s <= tSort s' -> leq_universe (snd Σ) s s'.
Proof.
  intros H; depind H; auto.
  - now inversion l.
  - depelim r. solve_discr.
  - depelim r. solve_discr.
Qed.

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
  { exists T, T. intuition auto. constructor. eapply validity; auto. pcuic. eauto. eapply cumul_refl'. }
  intros Hf. simpl in Hf.
  destruct u. simpl in Hf.
  - eapply inversion_App in Hf as [na' [A' [B' [Hf' [Ha HA''']]]]].
    eexists _, _; intuition eauto.
    econstructor; eauto. eapply validity; eauto with wf.
    constructor.
Admitted.

(*   - specialize (IHu (tApp f a) T). *)
(*     specialize (IHu Hf) as [T' [U' [[H' H''] H''']]]. *)
(*     eapply inversion_App in H' as [na' [A' [B' [Hf' [Ha HA''']]]]]. *)
(*     exists (tProd na' A' B'), U'. intuition; eauto. *)
(*     econstructor. eapply validity; eauto with wf. *)
(*     eapply cumul_refl'. auto. *)
(*     clear -H'' HA'''. depind H''. *)
(*     econstructor; eauto. eapply cumul_trans; eauto. *)
(* Qed. *)

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
  specialize (nth_error_all e a0) as [Hty ->].
  destruct decl as [name ty body rarg]; simpl in *.
  clear e.
  eexists _, _, _. split. split. eauto.
  eapply (substitution _ _ types _ [] _ _ wfΣ); simpl; eauto with wf.
  - subst types. rename i into hguard. clear -a a0 hguard.
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

Hint Resolve conv_ctx_refl : pcuic.

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
    constructor; auto with pcuic.
    constructor. exists s1; auto. apply conv_conv_alt.
    auto.

  - (* Lambda *)
    eapply type_Conv. eapply type_Lambda; eauto.
    eapply (context_conversion _ wfΣ _ _ _ _ typeb).
    constructor; auto with pcuic.
    constructor. exists s1; auto.
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
    now exists s1.
    apply conv_conv_alt; auto. eapply conv_refl.
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
    constructor. auto with pcuic. constructor; eauto. exists s1; auto.
    apply conv_conv_alt; auto.
    assert (Σ ;;; Γ |- tLetIn n b b_ty b' : tLetIn n b b_ty b'_ty). econstructor; eauto.
    edestruct (validity _ wfΣ _ wfΓ _ _ X0). apply i.
    eapply cumul_red_r.
    apply cumul_refl'. now constructor.

  - (* Application *)
    eapply substitution0; eauto.
    pose proof typet as typet'.
    eapply inversion_Lambda in typet' as [s1 [B' [Ht [Hb HU]]]].
    apply cumul_Prod_inv in HU as [eqA leqB] => //.

    eapply type_Conv; eauto.
    unshelve eapply (context_conversion _ wfΣ _ _ _ _ Hb); eauto with wf.
    admit. (* constructor auto with pcuic. constructor; eauto. *)
    destruct (validity _ wfΣ _ wfΓ _ _ typet).
    clear -i.
    (** Awfully complicated for a well-formedness condition *)
    { destruct i as [[ctx [s [Hs Hs']]]|[s Hs]].
      left.
      simpl in Hs. red.
      generalize (destArity_spec ([] ,, vass na A) B). rewrite Hs.
      intros. simpl in H.
      apply tProd_it_mkProd_or_LetIn in H.
      destruct H as [ctx' [-> Hb]].
      exists ctx', s.
      intuition auto. rewrite app_context_assoc in Hs'. apply Hs'.
      right. exists s.
      eapply inversion_Prod in Hs as [s1 [s2 [Ha [Hp Hp']]]].
      eapply type_Conv; eauto.
      left. exists [], s. intuition auto. now apply typing_wf_local in Hp.
      apply cumul_Sort_inv in Hp'.
      eapply cumul_trans with (tSort (Universe.sort_of_product s1 s2)).
      constructor.
      cbn. constructor. apply leq_universe_product.
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
    constructor. constructor.

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

Lemma subject_reduction1 {Σ Γ t u T}
  : wf Σ -> Σ ;;; Γ |- t : T -> red1 Σ Γ t u -> Σ ;;; Γ |- u : T.
Proof.
  intros. eapply subject_reduction; try eassumption.
  now apply red1_red.
Defined.
