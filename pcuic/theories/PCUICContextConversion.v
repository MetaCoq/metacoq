(* Distributed under the terms of the MIT license.   *)
Set Warnings "-notation-overridden".

From Equations Require Import Equations.
From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia.
From Coq Require Import CRelationClasses String.
From Coq Require Import ssreflect ssrbool.

From MetaCoq.Template Require Import config utils.
From MetaCoq Require Import LibHypsNaming.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICWeakeningEnv PCUICWeakening
     PCUICSubstitution PCUICClosed PCUICCumulativity PCUICGeneration PCUICReduction
     PCUICParallelReduction PCUICEquality
     PCUICParallelReductionConfluence PCUICConfluence.

Set Asymmetric Patterns.
Set SimplIsCbn.

Hint Resolve eq_universe_leq_universe.

(* Commented otherwise extraction would produce an axiom making the whole
   extracted code unusable *)

Arguments red_ctx : clear implicits.

Ltac my_rename_hyp h th :=
  match th with
    | (typing _ _ ?t _) => fresh "type" t
    | (All_local_env (@typing _) _ ?G) => fresh "wf" G
    | (All_local_env (@typing _) _ _) => fresh "wf"
    | (All_local_env _ _ ?G) => fresh "H" G
    | context [typing _ _ (_ ?t) _] => fresh "IH" t
  end.

Ltac rename_hyp h ht ::= my_rename_hyp h ht.

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

Lemma context_relation_trans P :
  (forall Γ Γ' Γ'' x y z,
      context_relation P Γ Γ' ->
      context_relation P Γ' Γ'' ->
      context_relation P Γ Γ'' ->
      P Γ Γ' x y -> P Γ' Γ'' y z -> P Γ Γ'' x z) ->
  Transitive (context_relation P).
Proof.
  intros HP x y z H. induction H in z |- *; auto;
  intros H'; unfold context in *; depelim H';
    try constructor; eauto; hnf in H0; noconf H0; eauto.
Qed.

Hint Resolve conv_refl' : pcuic.
Arguments skipn : simpl never.

(* TODO move *)
Lemma weakening_cumul0 `{CF:checker_flags} Σ Γ Γ'' M N n :
  wf Σ.1 -> n = #|Γ''| ->
  Σ ;;; Γ |- M <= N ->
  Σ ;;; Γ ,,, Γ'' |- lift0 n M <= lift0 n N.
Proof. intros; subst; now apply (weakening_cumul _ _ []). Qed.

Hint Constructors red1 : pcuic.
Hint Resolve refl_red : pcuic.

Section ContextReduction.
  Context {cf : checker_flags}.
  Context (Σ : global_env).
  Context (wfΣ : wf Σ).

  Local Definition red1_red_ctxP Γ Γ' :=
    (forall n b b',
        option_map decl_body (nth_error Γ n) = Some (Some b) ->
        option_map decl_body (nth_error Γ' n) = Some (Some b') ->
        @red_ctx Σ (skipn (S n) Γ) (skipn (S n) Γ') ->
        ∑ t, red Σ (skipn (S n) Γ') b t * red Σ (skipn (S n) Γ') b' t).

  Lemma red_ctx_skip i Γ Γ' :
    red1_red_ctxP Γ Γ' ->
    red1_red_ctxP (skipn i Γ) (skipn i Γ').
  Proof.
    rewrite /red1_red_ctxP => H n b b'.
    rewrite !nth_error_skipn => H0 H1.
    specialize (H (i + n)).
    rewrite !skipn_skipn. rewrite - !Nat.add_succ_comm.
    move=> H'.
    eapply H; auto.
  Qed.

  Lemma All2_local_env_over_red_refl {Γ Δ} :
    All2_local_env (on_decl (fun (Δ _ : context) (t u : term) => red Σ (Γ ,,, Δ) t u)) Δ Δ.
  Proof. induction Δ as [|[na [b|] ty]]; econstructor; try red; auto. Qed.

  Lemma All2_local_env_red_refl {Δ} :
    All2_local_env (on_decl (fun (Δ _ : context) (t u : term) => red Σ Δ t u)) Δ Δ.
  Proof. induction Δ as [|[na [b|] ty]]; econstructor; try red; auto. Qed.

  Lemma red1_red_ctxP_ass {Γ Γ' Δ} : assumption_context Δ ->
    red1_red_ctxP Γ Γ' ->
    red1_red_ctxP (Γ ,,, Δ) (Γ' ,,, Δ).
  Proof.
    induction Δ as [|[na [b|] ty] Δ]; intros; auto.
    elimtype False. depelim H.
    case; move => n b b' //. eapply IHΔ. now depelim H. apply X.
  Qed.

  Lemma red1_red_ctx_aux {Γ Γ' T U} :
    red1 Σ Γ T U ->
    @red_ctx Σ Γ Γ' ->
    red1_red_ctxP Γ Γ' ->
    ∑ t, red Σ Γ' T t * red Σ Γ' U t.
  Proof.
    intros r H. revert Γ' H.
    Ltac t := split; [eapply red1_red; try econstructor; eauto|try constructor]; eauto with pcuic.
    Ltac u := intuition eauto with pcuic.

    simpl in *. induction r using red1_ind_all; intros; auto with pcuic;
     try solve [eexists; t]; try destruct (IHr _ H) as [? [? ?]]; auto.

    - pose proof H.
      eapply nth_error_pred1_ctx_l in H as [body' [? ?]]; eauto.
      rewrite -(firstn_skipn (S i) Γ').
      assert (i < #|Γ'|). destruct (nth_error Γ' i) eqn:Heq; noconf e. eapply nth_error_Some_length in Heq. lia.
      move: (All2_local_env_length H0) => Hlen.
      specialize (X _ _ _ H1 e). forward X. eapply All2_local_env_app.
      instantiate (1 := firstn (S i) Γ').
      instantiate (1 := firstn (S i) Γ).
      rewrite [_ ,,, _](firstn_skipn (S i) _).
      now rewrite [_ ,,, _](firstn_skipn (S i) _).
      rewrite !skipn_length; try lia.

      destruct X as [x' [bt b't]]. exists (lift0 (S i) x').
      split; eauto with pcuic.
      etransitivity. eapply red1_red. constructor.
      rewrite firstn_skipn. eauto.
      eapply weakening_red_0; eauto. rewrite firstn_length_le //.
      eapply weakening_red_0; eauto. rewrite firstn_length_le //.

    - exists (tLambda na x N). split; apply red_abs; auto.

    - destruct (IHr (Γ' ,, vass na N)). constructor; pcuic.
      case => n b b' /= //. apply X.
      exists (tLambda na N x). split; apply red_abs; u.

    - exists (tLetIn na x t b'). split; eapply red_letin; auto.
    - specialize (IHr (Γ' ,, vdef na b t)).
      forward IHr. constructor; eauto. red. eauto.
      destruct IHr as [? [? ?]].
      case. move=> b0 b1 [] <- [] <- H'. exists b; auto.
      apply X.
      exists (tLetIn na b t x). split; eapply red_letin; auto.
    - exists (tCase ind x c brs). u; now apply red_case_p.
    - exists (tCase ind p x brs). u; now apply red_case_c.
    - eapply (OnOne2_exist _ (on_Trel_eq (red Σ Γ') snd fst))  in X.
      destruct X as [brs'' [? ?]].
      eexists. split; eapply red_case_one_brs; eauto.
      intros. intuition eauto.
      destruct (b1 _ H X0) as [? [? ?]].
      eexists (x.1, x0); intuition eauto.
    - exists (tProj p x). u; now eapply red_proj_c.
    - exists (tApp x M2). u; now eapply red_app.
    - exists (tApp M1 x). u; now eapply red_app.
    - exists (tProd na x M2). u; now eapply red_prod.
    - specialize (IHr (Γ' ,, vass na M1)) as [? [? ?]].
      constructor; pcuic. case => //.
      exists (tProd na M1 x). u; now eapply red_prod.
    - eapply (OnOne2_exist _ (red Σ Γ')) in X.
      destruct X as [rl [l0 l1]].
      eexists; split; eapply red_evar; eauto.
      eapply OnOne2_All2; eauto.
      eapply OnOne2_All2; eauto.
      simpl; intros.
      intuition eauto.
    - eapply (OnOne2_exist _ (on_Trel_eq (red Σ Γ') dtype (fun x => (dname x, dbody x, rarg x)))) in X.
      destruct X as [mfix' [l r]].
      exists (tFix mfix' idx); split; eapply red_fix_ty.
      eapply OnOne2_All2; intuition eauto; intuition.
      eapply OnOne2_All2; intuition eauto; intuition.
      intuition auto.
      destruct (b0 _ H X0) as [d' [r0 r1]].
      refine (existT _ {| dtype := d' |} _); simpl; eauto.
    - assert (fix_context mfix0 = fix_context mfix1).
      { rewrite /fix_context /mapi. generalize 0 at 2 4.
        induction X. destruct p. simpl. intuition congruence.
        intros. specialize (IHX (S n)). simpl. congruence. }
      eapply (OnOne2_exist _ (on_Trel_eq (red Σ (Γ' ,,, fix_context mfix0)) dbody (fun x => (dname x, dtype x, rarg x)))) in X.
      destruct X as [mfix' [l r]].
      exists (tFix mfix' idx); split; eapply red_fix_body.
      eapply OnOne2_All2; intuition eauto; intuition.
      eapply OnOne2_All2; intuition eauto; intuition. congruence.
      intros.
      intuition auto.
      specialize (b0 (Γ' ,,, fix_context mfix0)). forward b0.
      eapply All2_local_env_app_inv. apply H. apply All2_local_env_over_red_refl.
      forward b0. eapply red1_red_ctxP_ass. apply fix_context_assumption_context. auto.
      destruct b0 as [t [? ?]].
      refine (existT _ {| dbody := t |} _); simpl; eauto.
    - eapply (OnOne2_exist _ (on_Trel_eq (red Σ Γ') dtype (fun x => (dname x, dbody x, rarg x)))) in X.
      destruct X as [mfix' [l r]].
      exists (tCoFix mfix' idx); split; eapply red_cofix_ty.
      eapply OnOne2_All2; intuition eauto; intuition.
      eapply OnOne2_All2; intuition eauto; intuition.
      intuition auto.
      destruct (b0 _ H X0) as [d' [r0 r1]].
      refine (existT _ {| dtype := d' |} _); simpl; eauto.
    - assert (fix_context mfix0 = fix_context mfix1).
      { rewrite /fix_context /mapi. generalize 0 at 2 4.
        induction X. destruct p. simpl. intuition congruence.
        intros. specialize (IHX (S n)). simpl. congruence. }
      eapply (OnOne2_exist _ (on_Trel_eq (red Σ (Γ' ,,, fix_context mfix0)) dbody (fun x => (dname x, dtype x, rarg x)))) in X.
      destruct X as [mfix' [l r]].
      exists (tCoFix mfix' idx); split; eapply red_cofix_body.
      eapply OnOne2_All2; intuition eauto; intuition.
      eapply OnOne2_All2; intuition eauto; intuition. congruence.
      intros.
      intuition auto.
      specialize (b0 (Γ' ,,, fix_context mfix0)). forward b0.
      eapply All2_local_env_app_inv. apply H. apply All2_local_env_over_red_refl.
      forward b0. eapply red1_red_ctxP_ass. apply fix_context_assumption_context. auto.
      destruct b0 as [t [? ?]].
      refine (existT _ {| dbody := t |} _); simpl; eauto.
  Qed.

  Lemma red_red_ctx' {Γ Γ' T U} :
    red Σ Γ T U ->
    @red_ctx Σ Γ Γ' ->
    red1_red_ctxP Γ Γ' ->
    ∑ t, red Σ Γ' T t * red Σ Γ' U t.
  Proof.
    intros r rc rP.
    eapply red_alt in r.
    induction r.
    - eapply red1_red_ctx_aux; eauto.
    - exists x; split; auto.
    - destruct IHr1 as [xl [redl redr]].
      destruct IHr2 as [xr [redl' redr']].
      destruct (red_confluence wfΣ redr redl').
      destruct p.
      exists x0. split; [transitivity xl|transitivity xr]; auto.
  Qed.

  Lemma red_red_ctx_aux' {Γ Γ'} :
    @red_ctx Σ Γ Γ' -> red1_red_ctxP Γ Γ'.
  Proof.
    intros X.
    induction Γ in Γ', X |- *.
    - depelim X.
      intros n t t'. rewrite nth_error_nil //.
    - depelim X; red in o.
      + specialize (IHΓ Γ' X).
        case => n b b' /= //.
        simpl. apply IHΓ.
      + specialize (IHΓ _ X).
        destruct o.
        case.
        * move=> b0 b1 [] <- [] <- H.
          rewrite skipn_S /skipn /= in H.
          eapply red_red_ctx' in H; eauto.
        * simpl. eapply IHΓ.
  Qed.

  Lemma red_red_ctx {Γ Γ' T U} :
    red Σ Γ T U ->
    @red_ctx Σ Γ Γ' ->
    ∑ t, red Σ Γ' T t * red Σ Γ' U t.
  Proof.
    intros. eapply red_red_ctx', red_red_ctx_aux'; eauto.
  Qed.

End ContextReduction.

Section ContextConversion.
  Context {cf : checker_flags}.
  Context (Σ : global_env_ext).
  Context (wfΣ : wf Σ).

  Inductive conv_decls (Γ Γ' : context) : forall (x y : context_decl), Type :=
  | conv_vass na na' T T' :
      (* isType Σ Γ' T' -> *)
      Σ ;;; Γ |- T == T' ->
      conv_decls Γ Γ' (vass na T) (vass na' T')

  | conv_vdef_type na na' b T T' :
      (* isType Σ Γ' T' -> *)
      Σ ;;; Γ |- T == T' ->
      conv_decls Γ Γ' (vdef na b T) (vdef na' b T')

  | conv_vdef_body na na' b b' T T' :
      (* isType Σ Γ' T' -> *)
      (* Σ ;;; Γ' |- b' : T' -> *)
      Σ ;;; Γ |- b == b' ->
      Σ ;;; Γ |- T == T' ->
      conv_decls Γ Γ' (vdef na b T) (vdef na' b' T').

  Notation conv_context Γ Γ' := (context_relation conv_decls Γ Γ').

  Lemma conv_ctx_refl Γ : conv_context Γ Γ.
  Proof.
    induction Γ; try econstructor.
    destruct a as [na [b|] ty]; econstructor; eauto;
      constructor; pcuic; eapply conv_refl'.
  Qed.

  Global Instance conv_ctx_refl' : Reflexive (context_relation conv_decls)
    := conv_ctx_refl.

  Hint Resolve conv_ctx_refl : pcuic.

  Lemma fill_le {Γ t t' u u'} :
    leq_term Σ t u -> red Σ Γ t t' -> red Σ Γ u u' ->
    ∑ t'' u'', red Σ Γ t' t'' * red Σ Γ u' u'' * leq_term Σ t'' u''.
  Proof.
    intros tu tt' uu'.
    pose proof tu as tu2.
    eapply red_eq_term_upto_univ_l in tu; try exact tt'; tc.
    destruct tu as [u'' [uu'' t'u'']].
    destruct (red_confluence wfΣ uu' uu'') as [unf [ul ur]].
    eapply red_eq_term_upto_univ_r in t'u''; try exact ur; tc.
    destruct t'u'' as [t'' [t't'' t''unf]].
    exists t'', unf. intuition auto.
  Qed.

  Lemma fill_eq {Γ t t' u u'} :
    eq_term Σ t u -> red Σ Γ t t' -> red Σ Γ u u' ->
    ∑ t'' u'', red Σ Γ t' t'' * red Σ Γ u' u'' * eq_term Σ t'' u''.
  Proof.
    intros tu tt' uu'.
    pose proof tu as tu2.
    eapply red_eq_term_upto_univ_l in tu; try exact tt'; tc.
    destruct tu as [u'' [uu'' t'u'']].
    destruct (red_confluence wfΣ uu' uu'') as [unf [ul ur]].
    eapply red_eq_term_upto_univ_r in t'u''; try exact ur; tc.
    destruct t'u'' as [t'' [t't'' t''unf]].
    exists t'', unf. intuition auto.
  Qed.

  Lemma cumul_red_ctx Γ Γ' T U :
    Σ ;;; Γ |- T <= U ->
    red_ctx Σ Γ Γ' ->
    Σ ;;; Γ' |- T <= U.
  Proof.
    intros H Hctx.
    apply cumul_alt in H as [v [v' [[redl redr] leq]]].
    destruct (red_red_ctx Σ wfΣ redl Hctx) as [lnf [redl0 redr0]].
    apply cumul_alt.
    eapply red_eq_term_upto_univ_l in leq; tea; tc.
    destruct leq as [? [? ?]].
    destruct (red_red_ctx _ wfΣ redr Hctx) as [rnf [redl1 redr1]].
    destruct (red_confluence wfΣ r redr1). destruct p.
    edestruct (red_eq_term_upto_univ_r Σ (eq_universe_leq_universe _) e r0) as [lnf' [? ?]].
    exists lnf', x0. intuition auto. now transitivity lnf.
    now transitivity rnf.
  Qed.

  Lemma cumul_red_ctx_inv Γ Γ' T U :
    Σ ;;; Γ |- T <= U ->
    @red_ctx Σ Γ' Γ ->
    Σ ;;; Γ' |- T <= U.
  Proof.
    intros H Hctx.
    apply cumul_alt in H as [v [v' [[redl redr] leq]]].
    pose proof (PCUICConfluence.red_red_ctx wfΣ _ _ _ _ redl Hctx).
    pose proof (PCUICConfluence.red_red_ctx wfΣ _ _ _ _ redr Hctx).
    apply cumul_alt.
    exists v, v'.
    split. pcuic. auto.
  Qed.

  Lemma conv_red_ctx {Γ Γ' T U} :
    Σ ;;; Γ |- T = U ->
    @red_ctx Σ Γ Γ' ->
    Σ ;;; Γ' |- T = U.
  Proof.
    intros H Hctx.
    split; eapply cumul_red_ctx; eauto; eapply H.
  Qed.

  Lemma conv_red_ctx_inv {Γ Γ' T U} :
    Σ ;;; Γ |- T = U ->
    @red_ctx Σ Γ' Γ ->
    Σ ;;; Γ' |- T = U.
  Proof.
    intros H Hctx.
    split; eapply cumul_red_ctx_inv; eauto; eapply H.
  Qed.

  Arguments red_ctx : clear implicits.

  Lemma red_eq_context_upto_l {Re Γ Δ u v}
        `{RelationClasses.Reflexive _ Re} `{RelationClasses.Transitive _ Re} `{SubstUnivPreserving Re} :
    red Σ Γ u v ->
    eq_context_upto Re Γ Δ ->
    ∑ v',
    red Σ Δ u v' *
    eq_term_upto_univ Re Re v v'.
  Proof.
    intros r HΓ.
    eapply red_alt in r.
    induction r.
    - eapply red1_eq_context_upto_l in r; eauto.
      destruct r as [v [? ?]]. exists v. intuition pcuic.
    - exists x. split; auto. reflexivity.
    - destruct IHr1 as [v' [? ?]].
      destruct IHr2 as [v'' [? ?]].
      unshelve eapply (red_eq_term_upto_univ_l Σ _ (u:=y) (v:=v'') (u':=v')) in e; tc. all:pcuic.
      destruct e as [? [? ?]].
      exists x0; split; eauto.
      now transitivity v'.
      eapply eq_term_upto_univ_trans with v''; auto.
  Qed.

  Definition eq_universe_leq_universe' φ u u'
    := eq_universe_leq_universe φ u u'.

  Hint Resolve eq_universe_leq_universe' : pcuic.

  Lemma cumul_trans_red_leqterm {Γ t u v} :
    Σ ;;; Γ |- t <= u -> Σ ;;; Γ |- u <= v ->
    ∑ l o r, red Σ Γ t l *
             red Σ Γ u o *
             red Σ Γ v r *
             leq_term Σ l o * leq_term Σ o r.
  Proof.
    intros X X0.
    intros.
    eapply cumul_alt in X as [t0 [u0 [[redl redr] eq]]].
    eapply cumul_alt in X0 as [u1 [v0 [[redl' redr'] eq']]].
    destruct (red_confluence wfΣ redr redl') as [unf [nfl nfr]].
    eapply red_eq_term_upto_univ_r in eq; tc;eauto with pcuic.
    destruct eq as [t1 [red'0 eq2]].
    eapply red_eq_term_upto_univ_l in eq'; tc;eauto with pcuic.
    destruct eq' as [v1 [red'1 eq1]].
    exists t1, unf, v1.
    repeat split.
    transitivity t0; auto.
    transitivity u0; auto.
    transitivity v0; auto. eapply eq2. eapply eq1.
  Qed.

  (* Definition conv_contextP := *)
  (*   (forall n d d', *)
  (*       nth_error Γ n = Some d -> *)
  (*       nth_error Γ' n = Some d' -> *)
  (*       @red_ctx Σ (skipn (S n) Γ) (skipn (S n) Γ') -> *)


  (*       ∑ t, red Σ (skipn (S n) Γ') b t * red Σ (skipn (S n) Γ') b' t). *)

  Lemma conv_alt_eq_context_upto {Γ Δ T U} :
    eq_context_upto (eq_universe Σ) Γ Δ ->
    Σ ;;; Γ |- T == U ->
    Σ ;;; Δ |- T == U.
  Proof.
    intros eqctx cum.
    eapply conv_alt_red in cum as [nf [nf' [[redl redr] ?]]].
    eapply (red_eq_context_upto_l (Re:=eq_universe _)) in redl; tea.
    eapply (red_eq_context_upto_l (Re:=eq_universe _)) in redr; tea.
    destruct redl as [v' [redv' eqv']].
    destruct redr as [v'' [redv'' eqv'']].
    eapply conv_alt_red. exists v', v''; intuition auto.
    transitivity nf.
    now symmetry. now transitivity nf'.
  Qed.

  Lemma cumul_eq_context_upto {Γ Δ T U} :
    eq_context_upto (eq_universe (global_ext_constraints Σ)) Γ Δ ->
    Σ ;;; Γ |- T <= U ->
    Σ ;;; Δ |- T <= U.
  Proof.
    intros eqctx cum.
    eapply cumul_alt in cum as [nf [nf' [[redl redr] ?]]].
    eapply (red_eq_context_upto_l (Re:=eq_universe Σ) (Δ:=Δ)) in redl; tas.
    eapply (red_eq_context_upto_l (Re:=eq_universe Σ) (Δ:=Δ)) in redr; tas.
    destruct redl as [v' [redv' eqv']].
    destruct redr as [v'' [redv'' eqv'']].
    eapply cumul_alt. exists v', v''; intuition auto.
    eapply leq_term_trans with nf.
    apply eq_term_leq_term. now apply eq_term_sym.
    eapply leq_term_trans with nf'; auto.
    now apply eq_term_leq_term.
  Qed.

  Lemma conv_alt_red_ctx {Γ Γ' T U} :
    Σ ;;; Γ |- T == U ->
    @red_ctx Σ Γ Γ' ->
    Σ ;;; Γ' |- T == U.
  Proof.
    intros H Hctx.
    eapply conv_alt_red in H. apply conv_alt_red.
    destruct H as [T' [U' [[redv redv'] leqvv']]].
    eapply red_red_ctx in redv; eauto.
    eapply red_red_ctx in redv'; eauto.
    destruct redv as [Tj [redTj redT'j]].
    destruct redv' as [Uj [redUUj redU'j]].
    destruct (fill_eq leqvv' redT'j redU'j) as [Tnf [Unf [[redTnf redUnf] eqnf]]].
    exists Tnf, Unf; intuition eauto.
    now transitivity Tj.
    now transitivity Uj.
  Qed.

  Lemma conv_alt_red_ctx_inv Γ Γ' T U :
    Σ ;;; Γ |- T == U ->
    red_ctx Σ Γ' Γ ->
    Σ ;;; Γ' |- T == U.
  Proof.
    intros H Hctx.
    apply conv_alt_red in H as [v [v' [[redl redr] leq]]].
    pose proof (PCUICConfluence.red_red_ctx wfΣ _ _ _ _ redl Hctx).
    pose proof (PCUICConfluence.red_red_ctx wfΣ _ _ _ _ redr Hctx).
    apply conv_alt_red.
    exists v, v'.
    split. pcuic. auto.
  Qed.

  Lemma conv_context_red_context Γ Γ' :
    conv_context Γ Γ' ->
    ∑ Δ Δ', red_ctx Σ Γ Δ * red_ctx Σ Γ' Δ' * eq_context_upto (eq_universe Σ) Δ Δ'.
  Proof.
    intros Hctx.
    induction Hctx.
    - exists [], []; intuition pcuic. constructor.
    - destruct IHHctx as [Δ [Δ' [[? ?] ?]]].
      depelim p.
      pose proof (conv_alt_red_ctx c r).
      eapply conv_alt_red in X.
      destruct X as [T' [U' [[? ?] ?]]].
      pose proof (PCUICConfluence.red_red_ctx wfΣ _ _ _ _ r1 r).
      pose proof (PCUICConfluence.red_red_ctx wfΣ _ _ _ _ r2 r).
      destruct (red_eq_context_upto_l r1 e). destruct p.
      destruct (red_eq_context_upto_l r2 e). destruct p.
      exists (Δ ,, vass na' T'), (Δ' ,, vass na' x0).
      split; [split|]; constructor; auto. red.
      eapply PCUICConfluence.red_red_ctx; eauto.
      eapply eq_term_upto_univ_trans with U'; eauto; tc.
    - destruct IHHctx as [Δ [Δ' [[? ?] ?]]].
      depelim p.
      * pose proof (conv_alt_red_ctx c r).
        eapply conv_alt_red in X.
        destruct X as [T' [U' [[? ?] ?]]].
        pose proof (PCUICConfluence.red_red_ctx wfΣ _ _ _ _ r1 r).
        pose proof (PCUICConfluence.red_red_ctx wfΣ _ _ _ _ r2 r).
        destruct (red_eq_context_upto_l r1 e). destruct p.
        destruct (red_eq_context_upto_l r2 e). destruct p.
        exists (Δ ,, vdef na' u T'), (Δ' ,, vdef na' u x0).
        split; [split|]; constructor; auto. red. split; auto. red. split; auto.
        eapply PCUICConfluence.red_red_ctx; eauto. reflexivity.
        eapply eq_term_upto_univ_trans with U'; eauto; tc.
      * pose proof (conv_alt_red_ctx c r).
        eapply conv_alt_red in X.
        destruct X as [t' [u' [[? ?] ?]]].
        pose proof (PCUICConfluence.red_red_ctx wfΣ _ _ _ _ r1 r).
        pose proof (PCUICConfluence.red_red_ctx wfΣ _ _ _ _ r2 r).
        destruct (red_eq_context_upto_l r1 e) as [t'' [? ?]].
        destruct (red_eq_context_upto_l r2 e) as [u'' [? ?]].
        pose proof (conv_alt_red_ctx c0 r) as hTU.
        eapply conv_alt_red in hTU.
        destruct hTU as [T' [U' [[rT rU] eTU']]].
        pose proof (PCUICConfluence.red_red_ctx wfΣ _ _ _ _ rT r).
        pose proof (PCUICConfluence.red_red_ctx wfΣ _ _ _ _ rU r).
        destruct (red_eq_context_upto_l rT e) as [T'' [? ?]].
        destruct (red_eq_context_upto_l rU e) as [U'' [? ?]].
        exists (Δ ,, vdef na' t' T'), (Δ' ,, vdef na' u'' U'').
        split; [split|]. all: constructor ; auto.
        -- red. split; auto.
        -- red. split.
           ++ eapply PCUICConfluence.red_red_ctx; eauto.
           ++ eapply PCUICConfluence.red_red_ctx; eauto.
        -- eapply eq_term_upto_univ_trans with u'; eauto; tc.
        -- eapply eq_term_upto_univ_trans with U'; eauto; tc.
  Qed.

  Lemma conv_alt_conv_ctx Γ Γ' T U :
    Σ ;;; Γ |- T == U ->
    conv_context Γ Γ' ->
    Σ ;;; Γ' |- T == U.
  Proof.
    intros H Hctx.
    apply conv_context_red_context in Hctx => //.
    destruct Hctx as [Δ [Δ' [[l r] elr]]].
    eapply conv_alt_red_ctx in l; eauto.
    eapply conv_alt_red_ctx_inv in r; eauto.
    eapply conv_alt_eq_context_upto; eauto.
  Qed.

  Lemma cumul_conv_ctx Γ Γ' T U :
    Σ ;;; Γ |- T <= U ->
    conv_context Γ Γ' ->
    Σ ;;; Γ' |- T <= U.
  Proof.
    intros H Hctx.
    apply conv_context_red_context in Hctx => //.
    destruct Hctx as [Δ [Δ' [[l r] elr]]].
    eapply cumul_red_ctx in l; eauto.
    eapply cumul_red_ctx_inv in r; eauto.
    eapply cumul_eq_context_upto; eauto.
  Qed.

  Lemma conv_conv_ctx Γ Γ' T U :
    Σ ;;; Γ |- T = U ->
    conv_context Γ Γ' ->
    Σ ;;; Γ' |- T = U.
  Proof.
    intros H Hctx. destruct H.
    eapply cumul_conv_ctx in c; eauto.
    eapply cumul_conv_ctx in c0; eauto.
    now split.
  Qed.

  Lemma conv_isWfArity_or_Type Γ Γ' T U :
    conv_context Γ' Γ ->
    Σ ;;; Γ |- T = U ->
    isWfArity_or_Type Σ Γ T ->
    isWfArity_or_Type Σ Γ' U.
  Proof.
  Admitted.
End ContextConversion.

Notation conv_context Σ Γ Γ' := (context_relation (conv_decls Σ) Γ Γ').

Hint Resolve conv_ctx_refl : pcuic.

(* Lemma wf_local_conv_ctx {cf:checker_flags} Σ Γ Δ (wfΓ : wf_local Σ Γ) : wf Σ -> *)
(*   All_local_env_over typing *)
(*     (fun (Σ : global_env_ext) (Γ : context) wfΓ (t T : term) Ht => *)
(*        forall Γ' : context, conv_context Σ Γ Γ' -> Σ;;; Γ' |- t : T) Σ Γ wfΓ -> *)
(*   conv_context Σ Γ Δ -> wf_local Σ Δ. *)
(* Proof. *)
(*   intros wfΣ wfredctx. revert Δ. *)
(*   induction wfredctx; intros Δ wfred; unfold vass, vdef in *; depelim wfred. *)
(*   - constructor; eauto. *)
(*   - simpl. constructor. auto. red. depelim c. apply i. *)
(*   - simpl. depelim c. constructor; auto; hnf. *)
(*     eapply type_Cumul; eauto. eapply cumul_conv_ctx; eauto. *)
(*     eapply conv_alt_conv in c; auto. apply c. *)
(*     constructor; auto. *)
(* Qed. *)

Lemma conv_context_sym {cf:checker_flags} Σ Γ Γ' :
  wf Σ.1 (* -> wf_local Σ Γ *) -> conv_context Σ Γ Γ' -> conv_context Σ Γ' Γ.
Proof.
  induction Γ in Γ' |- *; try econstructor.
  intros wfΣ (* wfΓ *) conv; depelim conv; econstructor; eauto;
  constructor; pcuic. intros.
  depelim X0; constructor; pcuic.
  - depelim c. constructor.
    eapply conv_alt_sym, conv_alt_conv_ctx; eauto.
  - depelim c; constructor; auto.
    eapply conv_alt_sym, conv_alt_conv_ctx; eauto.
    eapply conv_alt_sym, conv_alt_conv_ctx; eauto.
    eapply conv_alt_sym, conv_alt_conv_ctx; eauto.
Qed.

(** Maybe need to prove it later *)
Lemma conv_context_trans {cf:checker_flags} Σ :
  wf Σ.1 -> CRelationClasses.Transitive (fun Γ Γ' => conv_context Σ Γ Γ').
Proof.
  intros wfΣ.
  eapply context_relation_trans.
  intros.
  depelim X2; depelim X3; try constructor; auto.
  eapply conv_alt_trans; eauto.
  eapply conv_alt_conv_ctx => //. apply c0.
  apply conv_context_sym => //. pcuic. admit.
  eapply conv_alt_trans; eauto.
  eapply conv_alt_conv_ctx => //. apply c0.
  apply conv_context_sym => //. admit.
Admitted.

(* Hint Immediate wf_local_conv_ctx : pcuic. *)
Hint Constructors conv_decls : pcuic.

Lemma context_conversion {cf:checker_flags} : env_prop
                             (fun Σ Γ t T =>
                                forall Γ', conv_context Σ Γ Γ' -> wf_local Σ Γ' -> Σ ;;; Γ' |- t : T).
Proof.
  apply typing_ind_env; intros Σ wfΣ Γ wfΓ; intros **; rename_all_hyps;
    try solve [econstructor; eauto].

  - pose proof heq_nth_error.
    eapply (context_relation_nth X0) in H as [d' [Hnth [Hrel Hconv]]].
    eapply type_Cumul.
    * econstructor. auto. eauto.
    * admit.
    * unshelve eapply nth_error_All_local_env_over in X. 3:eapply heq_nth_error.
      destruct X. red in o.
      depelim Hconv; simpl in *.
      + rewrite -(firstn_skipn (S n) Γ').
        eapply weakening_cumul0; auto.
        pose proof (nth_error_Some_length Hnth).
        rewrite firstn_length_le; lia.
        apply conv_alt_sym in c => //.
        eapply cumul_conv_ctx; eauto. eapply conv_alt_conv in c. apply c. auto.
      + simpl in *.
        rewrite -(firstn_skipn (S n) Γ').
        eapply weakening_cumul0; auto. rewrite firstn_length_le; auto.
        pose proof heq_nth_error. eapply nth_error_Some_length in Hnth. lia.
        eapply conv_alt_cumul; auto. eapply conv_alt_sym; auto.
        eapply conv_alt_conv_ctx; eauto.
      + simpl in *. auto.
        rewrite -(firstn_skipn (S n) Γ').
        eapply weakening_cumul0; auto. rewrite firstn_length_le; auto.
        pose proof heq_nth_error. eapply nth_error_Some_length in Hnth. lia.
        eapply conv_alt_cumul; auto. eapply conv_alt_sym; auto.
        eapply conv_alt_conv_ctx; eauto.
  - constructor; pcuic.
    eapply forall_Γ'0. repeat (constructor; pcuic).
    constructor; auto. red. eexists; eapply forall_Γ'; auto.
  - econstructor; pcuic.
    eapply forall_Γ'0; repeat (constructor; pcuic).
  - econstructor; pcuic.
    eapply forall_Γ'1; repeat (constructor; pcuic).
  - econstructor; pcuic. intuition auto. eapply isdecl. eapply isdecl.
    eauto. solve_all.
  - econstructor; pcuic.
    eapply All_local_env_app_inv. split; auto.
    eapply All_local_env_app in X. subst types.
    destruct X as [? ?]. clear -X1 X2 a0.
    induction a0; constructor; pcuic. destruct t0. exists x; intuition eauto.
    eapply b; eauto. (* conv_context_app *) admit.
    eapply All_local_env_app_inv; split; auto.
    destruct t0. exists x; intuition auto.
    eapply b0. admit.
    eapply All_local_env_app_inv; split; auto.
    eapply t1; auto. admit.
    eapply All_local_env_app_inv; split; auto.
    solve_all. subst types. apply b. admit.
    eapply All_local_env_app_inv; split; auto.
    admit.
  - econstructor; pcuic.
    eapply All_local_env_app_inv. split; auto.
    eapply All_local_env_app in X. subst types.
    destruct X as [? ?]. clear -X1 X2 a0.
    induction a0; constructor; pcuic. destruct t0. exists x; intuition eauto.
    eapply b; eauto. (* conv_context_app *) admit.
    eapply All_local_env_app_inv; split; auto.
    destruct t0. exists x; intuition auto.
    eapply b0. admit.
    eapply All_local_env_app_inv; split; auto.
    eapply t1; auto. admit.
    eapply All_local_env_app_inv; split; auto.
    solve_all. subst types. apply b. admit.
    eapply All_local_env_app_inv; split; auto.
    admit.
  - econstructor; eauto.
    destruct X2. destruct i. left. admit.
    right. destruct s as [s [ty ?]]. exists s. eauto.
    eapply cumul_conv_ctx; eauto.
Admitted.


Lemma context_conversion' {cf:checker_flags} {Σ Γ t T Γ'} :
    wf Σ.1 ->
    wf_local Σ Γ' ->
    Σ ;;; Γ |- t : T ->
    conv_context Σ Γ Γ' ->
    Σ ;;; Γ' |- t : T.
Proof.
  intros hΣ hΓ' h e.
  eapply context_conversion.
  4: exact e.
  all: try assumption.
  eapply typing_wf_local. eassumption.
Qed.

Lemma eq_context_upto_conv_context {cf:checker_flags} (Σ : global_env_ext) Re :
  RelationClasses.subrelation Re (eq_universe Σ) ->
  subrelation (eq_context_upto Re) (fun Γ Γ' => conv_context Σ Γ Γ').
Proof.
  intros HRe Γ Δ h. induction h.
  - constructor.
  - constructor; tas.
    constructor. eapply conv_alt_refl.
    eapply eq_term_upto_univ_impl; tea.
  - constructor; tas.
    constructor. eapply conv_alt_refl.
    eapply eq_term_upto_univ_impl; tea.
    eapply conv_alt_refl.
    eapply eq_term_upto_univ_impl; tea.
Qed.

Lemma eq_context_upto_univ_conv_context {cf:checker_flags} Σ Γ Δ :
    eq_context_upto (eq_universe (global_ext_constraints Σ)) Γ Δ ->
    conv_context Σ Γ Δ.
Proof.
  intros h. eapply eq_context_upto_conv_context; tea.
  reflexivity.
Qed.
