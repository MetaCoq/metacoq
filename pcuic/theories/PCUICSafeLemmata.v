(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia
     Classes.CRelationClasses Omega ProofIrrelevance.
From MetaCoq.Template Require Import config Universes monad_utils utils BasicAst
     AstUtils UnivSubst.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICReflect PCUICLiftSubst PCUICUnivSubst PCUICTyping
     PCUICCumulativity PCUICSR PCUICPosition PCUICEquality PCUICNameless
     PCUICNormal PCUICInversion PCUICCumulativity PCUICReduction
     PCUICConfluence PCUICConversion PCUICContextConversion PCUICValidity
     PCUICParallelReductionConfluence.
From Equations Require Import Equations.

Require Import Equations.Prop.DepElim.
Require Import Equations.Type.Relation_Properties.
Derive Signature for red.
Import MonadNotation.

Local Set Keyed Unification.
Set Equations With UIP.

Arguments sq {_} _.

Notation "( x ; y )" := (existT _ x y).

Ltac rdestruct H :=
  match type of H with
  | _ /\ _ => let H' := fresh H in
            destruct H as [H H']; rdestruct H; rdestruct H'
  | _ × _ => let H' := fresh H in
            destruct H as [H H']; rdestruct H; rdestruct H'
  | sigT _ => let H' := fresh H in
             destruct H as [H H']; rdestruct H; rdestruct H'
  | _ => idtac
  end.

Definition nodelta_flags := RedFlags.mk true true true false true true.


Inductive dlexprod {A} {B : A -> Type}
          (leA : A -> A -> Prop) (leB : forall x, B x -> B x -> Prop)
  : sigT B -> sigT B -> Prop :=
| left_lex : forall x x' y y', leA x x' -> dlexprod leA leB (x;y) (x';y')
| right_lex : forall x y y', leB x y y' -> dlexprod leA leB (x;y) (x;y').

Derive Signature for dlexprod.

Definition lexprod := Subterm.lexprod.
Arguments lexprod {_ _} _ _ _ _.

Notation "x ⊩ R1 ⨶ R2" :=
  (dlexprod R1 (fun x => R2)) (at level 20, right associativity).
Notation "R1 ⊗ R2" :=
  (lexprod R1 R2) (at level 20, right associativity).

Lemma acc_dlexprod :
  forall A B leA leB,
    (forall x, well_founded (leB x)) ->
    forall x,
      Acc leA x ->
      forall y,
        Acc (leB x) y ->
        Acc (@dlexprod A B leA leB) (x;y).
Proof.
  intros A B leA leB hw.
  induction 1 as [x hx ih1].
  intros y.
  induction 1 as [y hy ih2].
  constructor.
  intros [x' y'] h. simple inversion h.
  - intro hA. inversion H0. inversion H1. subst.
    eapply ih1.
    + assumption.
    + apply hw.
  - intro hB. rewrite <- H0.
    pose proof (projT2_eq H1) as p2.
    set (projT1_eq H1) as p1 in *; cbn in p1.
    destruct p1; cbn in p2; destruct p2.
    eapply ih2. assumption.
Qed.

Lemma dlexprod_Acc :
  forall A B leA leB,
    (forall x, well_founded (leB x)) ->
    forall x y,
      Acc leA x ->
      Acc (@dlexprod A B leA leB) (x;y).
Proof.
  intros A B leA leB hB x y hA.
  eapply acc_dlexprod ; try assumption.
  apply hB.
Qed.

Lemma dlexprod_trans :
  forall A B RA RB,
    transitive RA ->
    (forall x, transitive (RB x)) ->
    transitive (@dlexprod A B RA RB).
Proof.
  intros A B RA RB hA hB [u1 u2] [v1 v2] [w1 w2] h1 h2.
  revert w1 w2 h2. induction h1 ; intros w1 w2 h2.
  - dependent induction h2.
    + left. eapply hA ; eassumption.
    + left. assumption.
  - dependent induction h2.
    + left. assumption.
    + right. eapply hB ; eassumption.
Qed.

Section DestArity.
  Lemma destArity_app_aux {Γ Γ' t}
    : destArity (Γ ,,, Γ') t = option_map (fun '(ctx, s) => (Γ ,,, ctx, s))
                                          (destArity Γ' t).
  Proof.
    revert Γ'.
    induction t; cbn; intro Γ'; try reflexivity.
    - rewrite <- app_context_cons. now eapply IHt2.
    - rewrite <- app_context_cons. now eapply IHt3.
  Qed.

  Lemma destArity_app {Γ t}
    : destArity Γ t = option_map (fun '(ctx, s) => (Γ ,,, ctx, s))
                                          (destArity [] t).
  Proof.
    exact (@destArity_app_aux Γ [] t).
  Qed.

  Lemma destArity_app_Some {Γ t ctx s}
    : destArity Γ t = Some (ctx, s)
      -> ∑ ctx', destArity [] t = Some (ctx', s) /\ ctx = Γ ,,, ctx'.
  Proof.
    intros H. rewrite destArity_app in H.
    destruct (destArity [] t) as [[ctx' s']|]; cbn in *.
    exists ctx'. inversion H. now subst.
    discriminate H.
  Qed.

  Lemma destArity_tFix {mfix idx args} :
    destArity [] (mkApps (tFix mfix idx) args) = None.
  Proof.
    induction args. reflexivity.
    rewrite mkApps_nonempty. reflexivity.
    intros e; discriminate e.
  Qed.

  Lemma destArity_tApp {t u l} :
    destArity [] (mkApps (tApp t u) l) = None.
  Proof.
    induction l. reflexivity.
    rewrite mkApps_nonempty. reflexivity.
    intros e; discriminate e.
  Qed.
End DestArity.

Section Lemmata.
  Context {cf : checker_flags}.
  Context (flags : RedFlags.t).

  Lemma eq_term_zipc_inv :
    forall φ u v π,
      eq_term φ (zipc u π) (zipc v π) ->
      eq_term φ u v.
  Proof.
    intros Σ u v π h.
    revert u v h. induction π ; intros u v h.
    all: solve [
             simpl in h ; try apply IHπ in h ;
             cbn in h ; inversion h ; subst ; assumption
           ].
  Qed.

  Lemma eq_term_zipx_inv :
    forall φ Γ u v π,
      eq_term φ (zipx Γ u π) (zipx Γ v π) ->
      eq_term φ u v.
  Proof.
    intros Σ Γ u v π h.
    eapply eq_term_zipc_inv.
    eapply eq_term_it_mkLambda_or_LetIn_inv.
    eassumption.
  Qed.

  Lemma eq_term_upto_univ_zipc :
    forall Re u v π,
      Reflexive Re ->
      eq_term_upto_univ Re Re u v ->
      eq_term_upto_univ Re Re (zipc u π) (zipc v π).
  Proof.
    intros Re u v π he h.
    induction π in u, v, h |- *.
    all: try solve [
               simpl ; try apply IHπ ;
               cbn ; constructor ; try apply eq_term_upto_univ_refl ; assumption
             ].
    - assumption.
    - simpl. apply IHπ. destruct indn as [i n].
      constructor.
      + apply eq_term_upto_univ_refl. all: assumption.
      + assumption.
      + eapply All2_same.
        intros. split ; auto. apply eq_term_upto_univ_refl. all: assumption.
  Qed.

  Lemma eq_term_zipc :
    forall (Σ : global_env_ext) u v π,
      eq_term (global_ext_constraints Σ) u v ->
      eq_term (global_ext_constraints Σ) (zipc u π) (zipc v π).
  Proof.
    intros Σ u v π h.
    eapply eq_term_upto_univ_zipc.
    - intro. eapply eq_universe_refl.
    - assumption.
  Qed.

  Lemma eq_term_upto_univ_zipx :
    forall Re Γ u v π,
      Reflexive Re ->
      eq_term_upto_univ Re Re u v ->
      eq_term_upto_univ Re Re (zipx Γ u π) (zipx Γ v π).
  Proof.
    intros Re Γ u v π he h.
    eapply eq_term_upto_univ_it_mkLambda_or_LetIn ; auto.
    eapply eq_term_upto_univ_zipc ; auto.
  Qed.

  Lemma eq_term_zipx :
    forall φ Γ u v π,
      eq_term φ u v ->
      eq_term φ (zipx Γ u π) (zipx Γ v π).
  Proof.
    intros Σ Γ u v π h.
    eapply eq_term_upto_univ_zipx ; auto.
    intro. eapply eq_universe_refl.
  Qed.


  (* red is the reflexive transitive closure of one-step reduction and thus
     can't be used as well order. We thus define the transitive closure,
     but we take the symmetric version.
   *)
  Inductive cored Σ Γ: term -> term -> Prop :=
  | cored1 : forall u v, red1 Σ Γ u v -> cored Σ Γ v u
  | cored_trans : forall u v w, cored Σ Γ v u -> red1 Σ Γ v w -> cored Σ Γ w u.

  Derive Signature for cored.

  Lemma context_conversion :
    forall {Σ Γ t T Γ'},
      wf Σ.1 ->
      wf_local Σ Γ' ->
      Σ ;;; Γ |- t : T ->
      conv_context Σ Γ Γ' ->
      Σ ;;; Γ' |- t : T.
  Proof.
    intros Σ Γ t T Γ' hΣ hΓ' h e.
    eapply context_conversion.
    4: exact e.
    all: try assumption.
    eapply typing_wf_local. eassumption.
  Qed.

  Hint Resolve eq_term_upto_univ_refl : core.

  Lemma build_branches_type_eq_term :
    forall p p' ind mdecl idecl pars u brtys,
      eq_term_upto_univ eq eq p p' ->
      map_option_out
        (build_branches_type ind mdecl idecl pars u p) =
      Some brtys ->
      ∑ brtys',
        map_option_out
          (build_branches_type ind mdecl idecl pars u p') =
        Some brtys' ×
        All2 (on_Trel_eq (eq_term_upto_univ eq eq) snd fst) brtys brtys'.
  Proof.
    intros p p' ind mdecl idecl pars u brtys e hb.
    unfold build_branches_type in *.
    destruct idecl as [ina ity ike ict ipr]. simpl in *.
    unfold mapi in *. revert hb.
    generalize 0 at 3 6.
    intros n hb.
    induction ict in brtys, n, hb |- *.
    - cbn in *. eexists. split.
      + eassumption.
      + apply All2_same. intros [m t]. simpl. split ; now auto.
    - cbn. cbn in hb.
      lazymatch type of hb with
      | match ?t with _ => _ end = _ =>
        case_eq (t) ;
          try (intro bot ; rewrite bot in hb ; discriminate hb)
      end.
      intros [m t] e'. rewrite e' in hb.
      destruct a as [[na ta] ar].
      lazymatch type of e' with
      | match ?expr with _ => _ end = _ =>
        case_eq (expr) ;
          try (intro bot ; rewrite bot in e' ; discriminate e')
      end.
      intros ty ety. rewrite ety in e'.
      case_eq (decompose_prod_assum [] ty). intros sign ccl edty.
      rewrite edty in e'.
      case_eq (chop (ind_npars mdecl) (snd (decompose_app ccl))).
      intros paramrels args ech. rewrite ech in e'.
      inversion e'. subst. clear e'.
      lazymatch type of hb with
      | match ?t with _ => _ end = _ =>
        case_eq (t) ;
          try (intro bot ; rewrite bot in hb ; discriminate hb)
      end.
      intros tl etl. rewrite etl in hb.
      inversion hb. subst. clear hb.
      edestruct IHict as [brtys' [eq' he]].
      + eauto.
      + eexists. rewrite eq'. split.
        * reflexivity.
        * constructor ; auto.
          simpl. split ; auto.
          eapply eq_term_upto_univ_it_mkProd_or_LetIn ; auto.
          eapply eq_term_upto_univ_mkApps.
          -- eapply eq_term_upto_univ_lift. assumption.
          -- apply All2_same. intro. apply eq_term_upto_univ_refl ; auto.
  Qed.

  Lemma types_of_case_eq_term :
    forall ind mdecl idecl npar args u p p' pty indctx pctx ps btys,
      types_of_case ind mdecl idecl (firstn npar args) u p pty =
      Some (indctx, pctx, ps, btys) ->
      eq_term_upto_univ eq eq p p' ->
      ∑ btys',
        types_of_case ind mdecl idecl (firstn npar args) u p' pty =
        Some (indctx, pctx, ps, btys') ×
        All2 (on_Trel_eq (eq_term_upto_univ eq eq) snd fst) btys btys'.
  Proof.
    intros ind mdecl idecl npar args u p p' pty indctx pctx ps btys htc e.
    unfold types_of_case in *.
    case_eq (instantiate_params (ind_params mdecl) (firstn npar args) (ind_type idecl)) ;
      try solve [ intro bot ; rewrite bot in htc ; discriminate htc ].
    intros ity eity. rewrite eity in htc.
    case_eq (destArity [] ity) ;
      try solve [ intro bot ; rewrite bot in htc ; discriminate htc ].
    intros [args0 ?] ear. rewrite ear in htc.
    case_eq (destArity [] pty) ;
      try solve [ intro bot ; rewrite bot in htc ; discriminate htc ].
    intros [args' s'] ear'. rewrite ear' in htc.
    case_eq (map_option_out (build_branches_type ind mdecl idecl (firstn npar args) u p)) ;
      try solve [ intro bot ; rewrite bot in htc ; discriminate htc ].
    intros brtys ebrtys. rewrite ebrtys in htc.
    eapply build_branches_type_eq_term in ebrtys as [brtys' [ebrtys' he]] ; eauto.
    inversion htc. subst. clear htc.
    rewrite ebrtys'. intuition eauto.
  Qed.

  (* TODO MOVE *)
  Lemma All_prod_inv :
    forall A P Q l,
      All (fun x : A => P x × Q x) l ->
      All P l × All Q l.
  Proof.
    intros A P Q l h.
    induction h.
    - split ; auto.
    - destruct IHh, p.
      split ; constructor ; auto.
  Qed.

  (* TODO MOVE *)
  Lemma All_prod :
    forall A P Q l,
      All P l ->
      All Q l ->
      All (fun x : A => P x × Q x) l.
  Proof.
    intros A P Q l h1 h2.
    induction h1 in h2 |- *.
    - constructor.
    - dependent destruction h2.
      forward IHh1 ; auto.
  Qed.

  (* TODO MOVE *)
  Lemma All_local_env_prod_inv :
    forall P Q Γ,
      All_local_env (fun Δ A t => P Δ A t × Q Δ A t) Γ ->
      All_local_env P Γ × All_local_env Q Γ.
  Proof.
    intros P Q Γ h.
    induction h.
    - split ; auto.
    - destruct IHh, t0.
      split ; constructor ; auto.
    - destruct IHh, t0, t1.
      split ; constructor ; auto.
  Qed.

  (* TODO MOVE *)
  Lemma All_local_env_lift_prod_inv :
    forall Σ P Q Δ,
      All_local_env (lift_typing (fun Σ Γ t A => P Σ Γ t A × Q Σ Γ t A) Σ) Δ ->
      All_local_env (lift_typing P Σ) Δ × All_local_env (lift_typing Q Σ) Δ.
  Proof.
    intros Σ P Q Δ h.
    induction h.
    - split ; auto.
    - destruct IHh. destruct t0 as [? [? ?]].
      split ; constructor ; auto.
      + cbn. eexists. eassumption.
      + cbn. eexists. eassumption.
    - destruct IHh. destruct t0 as [? [? ?]]. destruct t1.
      split ; constructor ; auto.
      + cbn. eexists. eassumption.
      + cbn. eexists. eassumption.
  Qed.

  (* TODO MOVE *)
  Lemma eq_context_upto_rev :
    forall Γ Δ Re,
      eq_context_upto Re Γ Δ ->
      eq_context_upto Re (List.rev Γ) (List.rev Δ).
  Proof.
    intros Γ Δ Re h.
    induction h.
    - constructor.
    - simpl. eapply eq_context_upto_cat.
      + repeat constructor. assumption.
      + assumption.
    - simpl. eapply eq_context_upto_cat.
      + repeat constructor. all: assumption.
      + assumption.
  Qed.

  (* TODO MOVE *)
  Lemma eq_context_upto_conv_context :
    forall Σ Γ Δ,
      eq_context_upto (eq_universe (global_ext_constraints Σ)) Γ Δ ->
      conv_context Σ Γ Δ.
  Proof.
    intros Σ Γ Δ h.
    induction h.
    - constructor.
    - constructor. 1: assumption.
      constructor. eapply conv_alt_refl. assumption.
    - constructor. 1: assumption.
      constructor.
      all: eapply conv_alt_refl. all: assumption.
  Qed.

  (* TODO MOVE *)
  Lemma eq_context_impl :
    forall Re Re',
      inclusion Re Re' ->
      inclusion (eq_context_upto Re) (eq_context_upto Re').
  Proof.
    intros Re Re' hR Γ Δ h.
    induction h.
    - constructor.
    - constructor. 2: assumption.
      eapply eq_term_upto_univ_impl. all: eassumption.
    - constructor. 3: assumption.
      all: eapply eq_term_upto_univ_impl. all: eassumption.
  Qed.

  (* TODO MOVE *)
  Lemma eq_context_upto_length :
    forall Re Γ Δ,
      eq_context_upto Re Γ Δ ->
      #|Γ| = #|Δ|.
  Proof.
    intros Re Γ Δ h.
    induction h. all: simpl ; auto.
  Qed.

  (* TODO MOVE *)
  Lemma wf_local_nth_error_vass :
    forall Σ Γ i na ty,
      wf Σ.1 ->
      wf_local Σ Γ ->
      nth_error Γ i = Some (vass na ty) ->
      lift_typing typing Σ Γ (lift0 (S i) ty) None.
  Proof.
    intros Σ Γ i na ty hΣ hΓ e. simpl.
    induction i in Γ, hΓ, e |- *.
    - destruct Γ. 1: discriminate.
      simpl in e. apply some_inj in e. subst.
      inversion hΓ. subst. simpl in X0.
      destruct X0 as [s h].
      exists s. change (tSort s) with (lift0 1 (tSort s)).
      eapply PCUICWeakening.weakening with (Γ' := [ vass na ty ]).
      all: assumption.
    - destruct Γ. 1: discriminate.
      simpl in e.
      specialize IHi with (2 := e).
      destruct IHi as [s h].
      + inversion hΓ. all: auto.
      + exists s. change (tSort s) with (lift0 1 (lift0 (S i) (tSort s))).
        rewrite simpl_lift0.
        eapply PCUICWeakening.weakening with (Γ' := [ c ]).
        all: assumption.
  Qed.

  (* TODO MOVE *)
  Lemma fix_context_nth_error :
    forall m i d,
      nth_error m i = Some d ->
      nth_error (fix_context m) (#|m| - S i) =
      Some (vass (dname d) (lift0 i (dtype d))).
  Proof.
    intros m i d e.
    rewrite <- fix_context_length.
    unfold fix_context. rewrite List.rev_length.
    rewrite <- nth_error_rev.
    - rewrite nth_error_mapi. rewrite e. simpl. reflexivity.
    - rewrite mapi_length.
      eauto using nth_error_Some_length.
  Qed.

  (* TODO MOVE *)
  Lemma nth_error_weak_context :
    forall Γ Δ i d,
      nth_error Δ i = Some d ->
      nth_error (Γ ,,, Δ) i = Some d.
  Proof.
    intros Γ Δ i d h.
    rewrite nth_error_app_lt.
    - assumption.
    - apply nth_error_Some_length in h. assumption.
  Qed.

  Lemma typing_alpha :
    forall Σ Γ u v A,
      wf Σ.1 ->
      Σ ;;; Γ |- u : A ->
      eq_term_upto_univ eq eq u v ->
      Σ ;;; Γ |- v : A.
  Proof.
    assert (tm :
      env_prop (fun Σ Γ u A =>
                  forall v,
                    eq_term_upto_univ eq eq u v ->
                    Σ ;;; Γ |- v : A)
    ).
    eapply typing_ind_env.
    all: intros Σ wfΣ Γ wfΓ.
    - intros n decl hnth ih v e.
      dependent destruction e.
      eapply type_Rel ; eassumption.
    - intros l ih hl v e.
      dependent destruction e. subst.
      eapply type_Sort; assumption.
    - intros na A B s1 s2 ih hA ihA hB ihB v e.
      dependent destruction e.
      econstructor.
      + eapply ihA. assumption.
      + eapply context_conversion.
        * assumption.
        * constructor. 1: assumption.
          simpl. eexists. eapply ihA. assumption.
        * eapply ihB. assumption.
        * constructor.
          -- apply conv_ctx_refl ; auto.
          -- constructor. constructor.
             eapply eq_term_upto_univ_eq_eq_term. assumption.
    - intros na A t s1 B ih hA ihA hB ihB v e.
      dependent destruction e.
      econstructor.
      + econstructor.
        * eapply ihA. assumption.
        * eapply context_conversion.
          -- assumption.
          -- constructor. 1: assumption.
             simpl. eexists. eapply ihA. assumption.
          -- eapply ihB. assumption.
          -- constructor.
             ++ apply conv_ctx_refl ; auto.
             ++ do 2 constructor.
                eapply eq_term_upto_univ_eq_eq_term. assumption.
      + eapply validity_term ; eauto.
        econstructor ; eauto.
      + constructor.
        eapply eq_term_leq_term.
        apply eq_term_sym.
        constructor.
        all: try (eapply eq_term_upto_univ_eq_eq_term ; assumption).
        all: eapply eq_term_refl.
    - intros na b B t s1 A ih hB ihB hb ihb hA ihA v e.
      dependent destruction e.
      econstructor.
      + econstructor.
        * eapply ihB. assumption.
        * econstructor.
          -- eapply ihb. assumption.
          -- right. eexists. eapply ihB. assumption.
          -- constructor. eapply eq_term_leq_term.
             eapply eq_term_upto_univ_eq_eq_term. assumption.
        * eapply context_conversion.
          -- assumption.
          -- constructor.
             ++ assumption.
             ++ simpl. eexists. eapply ihB. assumption.
             ++ simpl. eapply type_Cumul.
                ** eapply ihb. assumption.
                ** right. eexists. eapply ihB. assumption.
                ** eapply cumul_refl.
                   eapply eq_term_upto_univ_impl. 3: eassumption.
                   all: intros x ? [].
                   --- eapply eq_universe_refl.
                   --- eapply leq_universe_refl.
          -- eapply ihA. assumption.
          -- constructor.
             ++ apply conv_ctx_refl ; auto.
             ++ econstructor. constructor.
                now apply eq_term_upto_univ_eq_eq_term.
                constructor.
                now apply eq_term_upto_univ_eq_eq_term.
      + eapply validity_term ; eauto.
        econstructor ; eauto.
      + constructor.
        eapply eq_term_leq_term.
        apply eq_term_sym.
        constructor.
        all: try (eapply eq_term_upto_univ_eq_eq_term ; assumption).
        all: eapply eq_term_refl.
    - intros t na A B u ih ht iht hu ihu v e.
      dependent destruction e.
      econstructor.
      + econstructor.
        * eapply iht. assumption.
        * eapply ihu. assumption.
      + eapply validity_term ; eauto.
        econstructor ; eauto.
      + constructor.
        eapply eq_term_leq_term.
        apply eq_term_sym.
        eapply eq_term_upto_univ_eq_eq_term.
        eapply eq_term_upto_univ_subst ; now auto.
    - intros cst u decl ? ? hdecl hcons v e.
      dependent destruction e.
      apply All2_eq in a. apply map_inj in a ; revgoals.
      { intros x y h. inversion h. reflexivity. }
      subst.
      constructor ; auto.
    - intros ind u mdecl idecl isdecl ? ? hcons v e.
      dependent destruction e.
      apply All2_eq in a. apply map_inj in a ; revgoals.
      { intros x y h. inversion h. reflexivity. }
      subst.
      econstructor ; eauto.
    - intros ind i u mdecl idecl cdecl isdecl ? ? ? v e.
      dependent destruction e.
      apply All2_eq in a. apply map_inj in a ; revgoals.
      { intros x y h. inversion h. reflexivity. }
      subst.
      econstructor ; eauto.
    - intros ind u npar p c brs args mdecl idecl isdecl X X0 H pars pty X1
             indctx pctx ps btys htc H1 H2 ihp hc ihc ihbrs v e.
      dependent destruction e.
      eapply types_of_case_eq_term in htc as htc' ; eauto.
      destruct htc' as [btys' [ebtys' he]].
      econstructor.
      + econstructor. all: try eassumption.
        * eapply ihp. assumption.
        * eapply ihc. assumption.
        * assert (All2 (fun x y => fst x = fst y × Σ ;;; Γ |- snd x : snd y) brs' btys)
            as hty.
          { clear - ihbrs a.
            induction ihbrs in brs', a |- *.
            - dependent destruction a. constructor.
            - dependent destruction a.
              constructor. all: auto.
              destruct p, r as [[? ?] ?]. split ; eauto.
              transitivity (fst x) ; eauto.
          }
          clear - he hty ihbrs.
          induction hty in brs, ihbrs, btys', he |- *.
          -- dependent destruction he. constructor.
          -- dependent destruction he.
             dependent destruction ihbrs.
             destruct r.
             destruct p.
             destruct p0 as [[? ?] ?].
             constructor ; eauto. split.
             ++ solve [ etransitivity ; eauto ].
             ++ econstructor.
                ** eassumption.
                ** (* We're missing the validity proof...
                      Is it hidden in the types_of_case_eq_term proof?
                      Are we missing an ingredient or should type_Case ask
                      that the branches types are sorted?
                    *)
                  admit.
                ** constructor.
                   eapply eq_term_leq_term.
                   eapply eq_term_upto_univ_eq_eq_term. assumption.
      + eapply validity_term ; eauto.
        instantiate (1 := tCase (ind, npar) p c brs).
        econstructor ; eauto.
        apply All2_prod_inv in ihbrs as [? ?]. assumption.
      + constructor.
        eapply eq_term_leq_term.
        apply eq_term_sym.
        eapply eq_term_mkApps.
        all: try (eapply eq_term_upto_univ_eq_eq_term ; assumption).
        eapply All2_app.
        * eapply All2_same. intro. eapply eq_term_refl.
        * constructor ; eauto.
          eapply eq_term_upto_univ_eq_eq_term. assumption.
    - intros p c u mdecl idecl pdecl isdecl args X X0 hc ihc H ty v e.
      dependent destruction e.
      econstructor.
      + econstructor. all: try eassumption.
        eapply ihc. assumption.
      + eapply validity_term ; eauto.
        econstructor ; eauto.
      + constructor.
        eapply eq_term_leq_term.
        apply eq_term_sym.
        eapply eq_term_upto_univ_eq_eq_term.
        eapply eq_term_upto_univ_substs ; auto; try reflexivity.
        * constructor ; auto.
          eapply All2_same.
          intro. eapply eq_term_upto_univ_refl ; auto.
    - intros mfix n decl types hnth hguard hwf ihmfix v e.
      dependent destruction e.
      eapply All2_nth_error_Some in hnth as hnth' ; eauto.
      destruct hnth' as [decl' [hnth' hh]].
      destruct hh as [[ety ebo] era].
      assert (hwf' : wf_local Σ (Γ ,,, fix_context mfix')).
      { rename types into Δ. set (Ξ := fix_context mfix').
        assert (e : eq_context_upto eq Δ Ξ).
        { eapply eq_context_upto_rev.
          clear - a.
          unfold mapi. generalize 0 at 2 4. intro n.
          induction a in n |- *.
          - constructor.
          - simpl. constructor.
            + eapply eq_term_upto_univ_lift. apply r.
            + eapply IHa.
        }
        clearbody Δ Ξ.
        clear - e hwf wfΣ wfΓ.
        induction e.
        - assumption.
        - simpl in *. inversion hwf. subst.
          constructor.
          + eapply IHe. assumption.
          + simpl. destruct X0 as [? [? ih]].
            eexists.
            eapply context_conversion.
            * assumption.
            * eapply IHe. assumption.
            * eapply ih. assumption.
            * eapply eq_context_upto_conv_context.
              eapply eq_context_impl ; revgoals.
              -- eapply eq_context_upto_cat. 2: eassumption.
                 eapply eq_context_upto_refl. auto.
              -- intros ? ? []. eapply eq_universe_refl.
        - simpl in *. inversion hwf. subst.
          constructor.
          + eapply IHe. assumption.
          + simpl. destruct X0 as [? [? ih]].
            eexists.
            eapply context_conversion.
            * assumption.
            * eapply IHe. assumption.
            * eapply ih. assumption.
            * eapply eq_context_upto_conv_context.
              eapply eq_context_impl ; revgoals.
              -- eapply eq_context_upto_cat. 2: eassumption.
                 eapply eq_context_upto_refl. auto.
              -- intros ? ? []. eapply eq_universe_refl.
          + simpl in *. destruct X0 as [? [? ih1]]. destruct X1 as [? ih2].
            eapply context_conversion.
            * assumption.
            * eapply IHe. assumption.
            * eapply type_Cumul.
              -- eapply ih2. assumption.
              -- right. eexists. eapply ih1. assumption.
              -- eapply cumul_refl.
                 eapply eq_term_upto_univ_impl. 3: eassumption.
                 all: intros ? ? [].
                 ++ eapply eq_universe_refl.
                 ++ eapply leq_universe_refl.
            * eapply eq_context_upto_conv_context.
              eapply eq_context_impl ; revgoals.
              -- eapply eq_context_upto_cat. 2: eassumption.
                 eapply eq_context_upto_refl. auto.
              -- intros ? ? []. eapply eq_universe_refl.
      }
      eapply type_Cumul.
      + econstructor.
        * eapply fix_guard_eq_term ; eauto.
          constructor. assumption.
        * eassumption.
        * assumption.
        * assert (val :
            All (fun d =>
              lift_typing typing Σ (Γ ,,, fix_context mfix')
                          ((lift0 #|fix_context mfix'|) (dtype d))
                          None
            ) mfix'
          ).
          { eapply forall_nth_error_All.
            intros i d e.
            apply fix_context_nth_error in e as e'.
            apply nth_error_weak_context with (Γ := Γ) in e'.
            eapply wf_local_nth_error_vass in e'. all: try eassumption.
            rewrite simpl_lift in e' by lia.
            apply nth_error_Some_length in e as hl.
            replace (S (#|mfix'| - S i) + i)
              with (#|mfix'|)
              in e'
              by lia.
            rewrite fix_context_length. assumption.
          }
          rename types into Δ. set (Ξ := fix_context mfix') in *.
          assert (e : eq_context_upto eq Δ Ξ).
          { eapply eq_context_upto_rev.
            clear - a.
            unfold mapi. generalize 0 at 2 4. intro n.
            induction a in n |- *.
            - constructor.
            - simpl. constructor.
              + eapply eq_term_upto_univ_lift. apply r.
              + eapply IHa.
          }
          clearbody Δ Ξ.
          assert (el : #|Δ| = #|Ξ|).
          { eapply eq_context_upto_length. eassumption. }
          clear - e a ihmfix wfΣ hwf' el val.
          induction a.
          -- constructor.
          -- inversion ihmfix. subst.
             destruct X as [[? ?] ih].
             constructor.
             ++ split.
                ** eapply context_conversion.
                   --- assumption.
                   --- assumption.
                   --- eapply type_Cumul.
                       +++ eapply ih. intuition eauto.
                       +++ right. simpl in val. inversion val. subst.
                           destruct X.
                           eexists. eapply context_conversion.
                           *** assumption.
                           *** eauto using typing_wf_local.
                           *** eassumption.
                           *** eapply eq_context_upto_conv_context.
                               eapply eq_context_upto_sym.
                               ---- intros ? ? ?. eapply eq_universe_sym.
                                    assumption.
                               ---- eapply eq_context_impl ; revgoals.
                                    ++++ eapply eq_context_upto_cat.
                                         2: eassumption.
                                         eapply eq_context_upto_refl. auto.
                                    ++++ intros ? ? []. eapply eq_universe_refl.
                       +++ eapply cumul_refl. rewrite <- el.
                           eapply eq_term_upto_univ_lift.
                           eapply eq_term_upto_univ_impl.
                           3: intuition eauto.
                           all: intros ? ? [].
                           *** eapply eq_universe_refl.
                           *** eapply leq_universe_refl.
                   --- eapply eq_context_upto_conv_context.
                       eapply eq_context_impl ; revgoals.
                       +++ eapply eq_context_upto_cat. 2: eassumption.
                           eapply eq_context_upto_refl. auto.
                       +++ intros ? ? []. eapply eq_universe_refl.
                ** eapply isLambda_eq_term_l.
                   --- eassumption.
                   --- intuition eauto.
             ++ eapply IHa.
                ** assumption.
                ** inversion val. assumption.
      + eapply validity_term ; eauto.
        instantiate (1 := tFix mfix n).
        econstructor ; eauto.
        * apply All_local_env_lift_prod_inv in hwf as [? ?]. assumption.
        * apply All_prod_inv in ihmfix as [? ?]. assumption.
      + constructor. eapply eq_term_leq_term.
        apply eq_term_sym.
        eapply eq_term_upto_univ_eq_eq_term. assumption.
    - intros mfix n decl types hnth hwf ihmfix hac v e. subst types.
      dependent destruction e.
      eapply All2_nth_error_Some in hnth as hnth' ; eauto.
      destruct hnth' as [decl' [hnth' hh]].
      destruct hh as [[ety ebo] era].
      assert (hwf' : wf_local Σ (Γ ,,, fix_context mfix')).
      { set (Δ := fix_context mfix) in *.
        set (Ξ := fix_context mfix').
        assert (e : eq_context_upto eq Δ Ξ).
        { eapply eq_context_upto_rev.
          clear - a.
          unfold mapi. generalize 0 at 2 4. intro n.
          induction a in n |- *.
          - constructor.
          - simpl. constructor.
            + eapply eq_term_upto_univ_lift. apply r.
            + eapply IHa.
        }
        clearbody Δ Ξ.
        clear - e hwf wfΣ wfΓ.
        induction e.
        - assumption.
        - simpl in *. inversion hwf. subst.
          constructor.
          + eapply IHe. assumption.
          + simpl. destruct X0 as [? [? ih]].
            eexists.
            eapply context_conversion.
            * assumption.
            * eapply IHe. assumption.
            * eapply ih. assumption.
            * eapply eq_context_upto_conv_context.
              eapply eq_context_impl ; revgoals.
              -- eapply eq_context_upto_cat. 2: eassumption.
                 eapply eq_context_upto_refl. auto.
              -- intros ? ? []. eapply eq_universe_refl.
        - simpl in *. inversion hwf. subst.
          constructor.
          + eapply IHe. assumption.
          + simpl. destruct X0 as [? [? ih]].
            eexists.
            eapply context_conversion.
            * assumption.
            * eapply IHe. assumption.
            * eapply ih. assumption.
            * eapply eq_context_upto_conv_context.
              eapply eq_context_impl ; revgoals.
              -- eapply eq_context_upto_cat. 2: eassumption.
                 eapply eq_context_upto_refl. auto.
              -- intros ? ? []. eapply eq_universe_refl.
          + simpl in *. destruct X0 as [? [? ih1]]. destruct X1 as [? ih2].
            eapply context_conversion.
            * assumption.
            * eapply IHe. assumption.
            * eapply type_Cumul.
              -- eapply ih2. assumption.
              -- right. eexists. eapply ih1. assumption.
              -- eapply cumul_refl.
                 eapply eq_term_upto_univ_impl. 3: eassumption.
                 all: intros ? ? [].
                 ++ eapply eq_universe_refl.
                 ++ eapply leq_universe_refl.
            * eapply eq_context_upto_conv_context.
              eapply eq_context_impl ; revgoals.
              -- eapply eq_context_upto_cat. 2: eassumption.
                 eapply eq_context_upto_refl. auto.
              -- intros ? ? []. eapply eq_universe_refl.
      }
      eapply type_Cumul.
      + econstructor.
        * assumption.
        * eassumption.
        * assumption.
        * assert (val :
            All (fun d =>
              lift_typing typing Σ (Γ ,,, fix_context mfix')
                          ((lift0 #|fix_context mfix'|) (dtype d))
                          None
            ) mfix'
          ).
          { eapply forall_nth_error_All.
            intros i d e.
            apply fix_context_nth_error in e as e'.
            apply nth_error_weak_context with (Γ := Γ) in e'.
            eapply wf_local_nth_error_vass in e'. all: try eassumption.
            rewrite simpl_lift in e' by lia.
            apply nth_error_Some_length in e as hl.
            replace (S (#|mfix'| - S i) + i)
              with (#|mfix'|)
              in e'
              by lia.
            rewrite fix_context_length. assumption.
          }
          set (Δ := fix_context mfix) in *.
          set (Ξ := fix_context mfix') in *.
          assert (e : eq_context_upto eq Δ Ξ).
          { eapply eq_context_upto_rev.
            clear - a.
            unfold mapi. generalize 0 at 2 4. intro n.
            induction a in n |- *.
            - constructor.
            - simpl. constructor.
              + eapply eq_term_upto_univ_lift. apply r.
              + eapply IHa.
          }
          clearbody Δ Ξ.
          assert (el : #|Δ| = #|Ξ|).
          { eapply eq_context_upto_length. eassumption. }
          clear - e a ihmfix wfΣ hwf' el val.
          induction a.
          -- constructor.
          -- inversion ihmfix. subst.
             destruct X as [? ih].
             constructor.
             ++ eapply context_conversion.
                ** assumption.
                ** assumption.
                ** eapply type_Cumul.
                   --- eapply ih. intuition eauto.
                   --- right. simpl in val. inversion val. subst.
                       destruct X.
                       eexists. eapply context_conversion.
                       +++ assumption.
                       +++ eauto using typing_wf_local.
                       +++ eassumption.
                       +++ eapply eq_context_upto_conv_context.
                           eapply eq_context_upto_sym.
                           *** intros ? ? ?. eapply eq_universe_sym.
                               assumption.
                           *** eapply eq_context_impl ; revgoals.
                               ---- eapply eq_context_upto_cat.
                                    2: eassumption.
                                    eapply eq_context_upto_refl. auto.
                               ---- intros ? ? []. eapply eq_universe_refl.
                   --- eapply cumul_refl. rewrite <- el.
                       eapply eq_term_upto_univ_lift.
                       eapply eq_term_upto_univ_impl.
                       3: intuition eauto.
                       all: intros ? ? [].
                       +++ eapply eq_universe_refl.
                       +++ eapply leq_universe_refl.
                ** eapply eq_context_upto_conv_context.
                   eapply eq_context_impl ; revgoals.
                   --- eapply eq_context_upto_cat. 2: eassumption.
                       eapply eq_context_upto_refl. auto.
                   --- intros ? ? []. eapply eq_universe_refl.
             ++ eapply IHa.
                ** assumption.
                ** inversion val. assumption.
      + eapply validity_term ; eauto.
        instantiate (1 := tCoFix mfix n).
        econstructor ; eauto.
        * apply All_local_env_lift_prod_inv in hwf as [? ?]. assumption.
        * apply All_prod_inv in ihmfix as [? ?]. assumption.
      + constructor. eapply eq_term_leq_term.
        apply eq_term_sym.
        eapply eq_term_upto_univ_eq_eq_term. assumption.
    - intros t A B X ht iht har hcu v e.
      eapply type_Cumul.
      + eapply iht. assumption.
      + destruct har as [[? ?] | [? [? ?]]].
        * left. assumption.
        * right. eexists. eassumption.
      + assumption.
    - rename wfΣ into Γ, wfΓ into v, Γ into u.
      intros A hΣ hu e.
      eapply tm ; eauto.
      eapply typing_wf_local. eassumption.
  Admitted.

  Corollary type_nameless :
    forall Σ Γ u A,
      wf Σ.1 ->
      Σ ;;; Γ |- u : A ->
      Σ ;;; Γ |- nl u : A.
  Proof.
    intros Σ Γ u A hΣ h.
    eapply typing_alpha ; eauto.
    eapply eq_term_upto_univ_tm_nl. all: auto.
  Qed.

  Lemma lookup_env_ConstantDecl_inv :
    forall Σ k k' ty bo uni,
      Some (ConstantDecl k' {| cst_type := ty ; cst_body := bo; cst_universes := uni |})
      = lookup_env Σ k ->
      k = k'.
  Proof.
    intros Σ k k' ty bo uni h.
    induction Σ in h |- *.
    - cbn in h. discriminate.
    - cbn in h. destruct (ident_eq_spec k (global_decl_ident a)).
      + subst. inversion h. reflexivity.
      + apply IHΣ in h. assumption.
  Qed.

  Lemma fresh_global_nl :
    forall Σ k,
      fresh_global k Σ ->
      fresh_global k (map nl_global_decl Σ).
  Proof.
    intros Σ k h. eapply Forall_map.
    eapply Forall_impl ; try eassumption.
    intros x hh. cbn in hh.
    destruct x ; assumption.
  Qed.

  Lemma conv_context :
    forall Σ Γ u v ρ,
      wf Σ.1 ->
      Σ ;;; Γ ,,, stack_context ρ |- u == v ->
      Σ ;;; Γ |- zipc u ρ == zipc v ρ.
  Proof.
    intros Σ Γ u v ρ hΣ h.
    induction ρ in u, v, h |- *.
    - assumption.
    - simpl. eapply IHρ. eapply conv_App_l ; auto.
    - simpl. eapply IHρ. eapply conv_App_r ; auto.
    - simpl. eapply IHρ. eapply conv_App_r ; auto.
    - simpl. eapply IHρ. eapply conv_Case_c ; auto.
    - simpl. eapply IHρ. eapply conv_Proj_c ; auto.
    - simpl. eapply IHρ. eapply conv_Prod_l ; auto.
    - simpl. eapply IHρ. eapply conv_Prod_r ; auto.
    - simpl. eapply IHρ. eapply conv_Lambda_l ; auto.
    - simpl. eapply IHρ. eapply conv_Lambda_r ; auto.
    - simpl. eapply IHρ. eapply conv_App_r ; auto.
  Qed.

  Context (Σ : global_env_ext).

  Inductive welltyped Σ Γ t : Prop :=
  | iswelltyped A : Σ ;;; Γ |- t : A -> welltyped Σ Γ t.

  Arguments iswelltyped {Σ Γ t A} h.

  Definition wellformed Σ Γ t :=
    welltyped Σ Γ t \/ ∥ isWfArity typing Σ Γ t ∥.

  (* Here we use use the proof irrelevance axiom to show that wellformed is really squashed.
     Using SProp would avoid this.
   *)

  Lemma wellformed_irr :
    forall {Σ Γ t} (h1 h2 : wellformed Σ Γ t), h1 = h2.
  Proof. intros. apply proof_irrelevance. Qed.

  Context (hΣ : ∥ wf Σ ∥).

  Lemma welltyped_rename :
    forall Γ u v,
      welltyped Σ Γ u ->
      eq_term_upto_univ eq eq u v ->
      welltyped Σ Γ v.
  Proof.
    intros Γ u v [A h] e.
    destruct hΣ.
    exists A. eapply typing_alpha ; eauto.
  Qed.

  Lemma wellformed_rename :
    forall Γ u v,
      wellformed Σ Γ u ->
      eq_term_upto_univ eq eq u v ->
      wellformed Σ Γ v.
  Proof.
  Admitted.

  Lemma red_cored_or_eq :
    forall Γ u v,
      red Σ Γ u v ->
      cored Σ Γ v u \/ u = v.
  Proof.
    intros Γ u v h.
    induction h.
    - right. reflexivity.
    - destruct IHh.
      + left. eapply cored_trans ; eassumption.
      + subst. left. constructor. assumption.
  Qed.

  Lemma cored_it_mkLambda_or_LetIn :
    forall Γ Δ u v,
      cored Σ (Γ ,,, Δ) u v ->
      cored Σ Γ (it_mkLambda_or_LetIn Δ u)
               (it_mkLambda_or_LetIn Δ v).
  Proof.
    intros Γ Δ u v h.
    induction h.
    - constructor. apply red1_it_mkLambda_or_LetIn. assumption.
    - eapply cored_trans.
      + eapply IHh.
      + apply red1_it_mkLambda_or_LetIn. assumption.
  Qed.

  Lemma cored_welltyped :
    forall {Γ u v},
      welltyped Σ Γ u ->
      cored (fst Σ) Γ v u ->
      welltyped Σ Γ v.
  Proof.
    destruct hΣ as [wΣ]; clear hΣ.
    intros Γ u v h r.
    revert h. induction r ; intros h.
    - destruct h as [A h]. exists A.
      eapply sr_red1 ; eauto with wf.
    - specialize IHr with (1 := ltac:(eassumption)).
      destruct IHr as [A ?]. exists A.
      eapply sr_red1 ; eauto with wf.
  Qed.

  Lemma cored_trans' :
    forall {Γ u v w},
      cored Σ Γ u v ->
      cored Σ Γ v w ->
      cored Σ Γ u w.
  Proof.
    intros Γ u v w h1 h2. revert w h2.
    induction h1 ; intros z h2.
    - eapply cored_trans ; eassumption.
    - eapply cored_trans.
      + eapply IHh1. assumption.
      + assumption.
  Qed.

  (* This suggests that this should be the actual definition.
     ->+ = ->*.->
   *)
  Lemma cored_red_trans :
    forall Γ u v w,
      red Σ Γ u v ->
      red1 Σ Γ v w ->
      cored Σ Γ w u.
  Proof.
    intros Γ u v w h1 h2.
    revert w h2. induction h1 ; intros w h2.
    - constructor. assumption.
    - eapply cored_trans.
      + eapply IHh1. eassumption.
      + assumption.
  Qed.

  Lemma cored_case :
    forall Γ ind p c c' brs,
      cored Σ Γ c c' ->
      cored Σ Γ (tCase ind p c brs) (tCase ind p c' brs).
  Proof.
    intros Γ ind p c c' brs h.
    revert ind p brs. induction h ; intros ind p brs.
    - constructor. constructor. assumption.
    - eapply cored_trans.
      + eapply IHh.
      + econstructor. assumption.
  Qed.

  Lemma welltyped_context :
    forall Γ t,
      welltyped Σ Γ (zip t) ->
      welltyped Σ (Γ ,,, stack_context (snd t)) (fst t).
  Proof.
    destruct hΣ as [wΣ].
    intros Γ [t π] h. simpl.
    destruct h as [T h].
    induction π in Γ, t, T, h |- *.
    - cbn. cbn in h. eexists. eassumption.
    - simpl. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [B h].
      apply inversion_App in h as hh ; auto.
      destruct hh as [na [A' [B' [? [? ?]]]]].
      eexists. eassumption.
    - simpl. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [B h].
      apply inversion_App in h as hh ; auto.
      destruct hh as [na [A' [B' [? [? ?]]]]].
      eexists. eassumption.
    - simpl. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [B h].
      apply inversion_App in h as hh ; auto.
      destruct hh as [na [A' [B' [? [? ?]]]]].
      eexists. eassumption.
    - simpl. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [B h].
      destruct indn.
      apply inversion_Case in h as hh ; auto.
      destruct hh
        as [uni [args [mdecl [idecl [pty [indctx [pctx [ps [btys [? [? [? [? [? [? [ht0 [? ?]]]]]]]]]]]]]]]]].
      eexists. eassumption.
    - simpl. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [T' h].
      apply inversion_Proj in h
        as [uni [mdecl [idecl [pdecl [args [? [? [? ?]]]]]]]] ; auto.
      eexists. eassumption.
    - simpl. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [T' h].
      apply inversion_Prod in h as hh ; auto.
      destruct hh as [s1 [s2 [? [? ?]]]].
      eexists. eassumption.
    - cbn. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [T' h].
      apply inversion_Prod in h as hh ; auto.
      destruct hh as [s1 [s2 [? [? ?]]]].
      eexists. eassumption.
    - cbn. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [T' h].
      apply inversion_Lambda in h as hh ; auto.
      destruct hh as [s1 [B [? [? ?]]]].
      eexists. eassumption.
    - cbn. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [T' h].
      apply inversion_Lambda in h as hh ; auto.
      destruct hh as [s1 [B [? [? ?]]]].
      eexists. eassumption.
    - cbn. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [B h].
      apply inversion_App in h as hh ; auto.
      destruct hh as [na [A' [B' [? [? ?]]]]].
      eexists. eassumption.
  Qed.

  Lemma wellformed_context :
    forall Γ t,
      wellformed Σ Γ (zip t) ->
      wellformed Σ (Γ ,,, stack_context (snd t)) (fst t).
  Proof.
    destruct hΣ as [wΣ].
    intros Γ [t π] [[A h]|h].
    - destruct (welltyped_context Γ (t, π) (iswelltyped h)) as [? ?].
      left. econstructor. eassumption.
    - induction π in t, h |- *.
      all: try (specialize (IHπ _ h)).
      all: simpl in *.
      1: right ; assumption.
      all: destruct IHπ as [[A' h'] | [[Δ [s [h1 h2]]]]] ; [| try discriminate].
      all: try solve [
        apply inversion_App in h' ; auto ;
        rdestruct h' ;
        left ; econstructor ; eassumption
      ].
      + destruct indn.
        apply inversion_Case in h' ; auto. cbn in h'. rdestruct h'.
        left. econstructor. eassumption.
      + apply inversion_Proj in h' ; auto.
        cbn in h'. rdestruct h'.
        left. eexists. eassumption.
      + apply inversion_Prod in h' ; auto. rdestruct h'.
        left. eexists. eassumption.
      + cbn in h1. apply destArity_app_Some in h1 as [Δ' [h1 h1']].
        subst. left. rewrite app_context_assoc in h2. cbn in *.
        apply wf_local_app in h2. inversion h2. subst. cbn in *.
        destruct X0. eexists. eassumption.
      + apply inversion_Prod in h' ; auto. rdestruct h'.
        left. eexists. eassumption.
      + cbn in h1. apply destArity_app_Some in h1 as [Δ' [h1 h1']].
        subst. right. constructor. exists Δ', s.
        rewrite app_context_assoc in h2. cbn in h2.
        split ; eauto.
      + apply inversion_Lambda in h' ; auto. rdestruct h'.
        left. eexists. eassumption.
      + apply inversion_Lambda in h' ; auto. rdestruct h'.
        left. eexists. eassumption.
  Qed.

  Lemma cored_red :
    forall Γ u v,
      cored Σ Γ v u ->
      ∥ red Σ Γ u v ∥.
  Proof.
    intros Γ u v h.
    induction h.
    - constructor. econstructor.
      + constructor.
      + assumption.
    - destruct IHh as [r].
      constructor. econstructor ; eassumption.
  Qed.

  Lemma cored_context :
    forall Γ t u π,
      cored Σ (Γ ,,, stack_context π) t u ->
      cored Σ Γ (zip (t, π)) (zip (u, π)).
  Proof.
    intros Γ t u π h. induction h.
    - constructor. eapply red1_context. assumption.
    - eapply cored_trans.
      + eapply IHh.
      + eapply red1_context. assumption.
  Qed.

  Lemma cored_zipx :
    forall Γ u v π,
      cored Σ (Γ ,,, stack_context π) u v ->
      cored Σ [] (zipx Γ u π) (zipx Γ v π).
  Proof.
    intros Γ u v π h.
    eapply cored_it_mkLambda_or_LetIn.
    eapply cored_context.
    rewrite app_context_nil_l.
    assumption.
  Qed.

  Lemma red_zipx :
    forall Γ u v π,
      red Σ (Γ ,,, stack_context π) u v ->
      red Σ [] (zipx Γ u π) (zipx Γ v π).
  Proof.
    intros Γ u v π h.
    eapply red_it_mkLambda_or_LetIn.
    eapply red_context.
    rewrite app_context_nil_l.
    assumption.
  Qed.

  Lemma cumul_zippx :
    forall Γ u v ρ,
      Σ ;;; (Γ ,,, stack_context ρ) |- u <= v ->
      Σ ;;; Γ |- zippx u ρ <= zippx v ρ.
  Proof.
    intros Γ u v ρ h.
    revert u v h. induction ρ ; intros u v h.
    - cbn. assumption.
    - unfold zippx. simpl.
      case_eq (decompose_stack ρ). intros l π e.
      unfold zippx in IHρ. rewrite e in IHρ.
      apply IHρ.
      eapply cumul_App_l. assumption.
    - unfold zippx. simpl.
      eapply cumul_it_mkLambda_or_LetIn.
      assumption.
    - unfold zippx. simpl.
      eapply cumul_it_mkLambda_or_LetIn.
      assumption.
    - unfold zippx. simpl.
      eapply cumul_it_mkLambda_or_LetIn.
      assumption.
    - unfold zippx. simpl.
      eapply cumul_it_mkLambda_or_LetIn.
      assumption.
    - unfold zippx. simpl.
      eapply cumul_it_mkLambda_or_LetIn.
      assumption.
    - unfold zippx. simpl.
      eapply cumul_it_mkLambda_or_LetIn. cbn.
      eapply cumul_Lambda_r.
      assumption.
    - unfold zippx. simpl.
      eapply cumul_it_mkLambda_or_LetIn.
      assumption.
    - unfold zippx. simpl.
      eapply cumul_it_mkLambda_or_LetIn. cbn.
      eapply cumul_Lambda_r.
      assumption.
    - unfold zippx. simpl.
      eapply cumul_it_mkLambda_or_LetIn. assumption.
  Qed.

  Lemma conv_LetIn_bo :
    forall Γ na ty t u u',
      Σ ;;; Γ ,, vdef na ty t |- u == u' ->
      Σ ;;; Γ |- tLetIn na ty t u == tLetIn na ty t u'.
  Proof.
    intros Γ na ty t u u' h.
    induction h.
    - eapply conv_alt_refl. constructor.
      all: try eapply eq_term_refl.
      assumption.
    - eapply conv_alt_red_l ; try eassumption.
      econstructor. assumption.
    - eapply conv_alt_red_r ; try eassumption.
      econstructor. assumption.
  Qed.

  Lemma conv_alt_it_mkLambda_or_LetIn :
    forall Δ Γ u v,
      Σ ;;; (Δ ,,, Γ) |- u == v ->
      Σ ;;; Δ |- it_mkLambda_or_LetIn Γ u == it_mkLambda_or_LetIn Γ v.
  Proof.
    intros Δ Γ u v h. revert Δ u v h.
    induction Γ as [| [na [b|] A] Γ ih ] ; intros Δ u v h.
    - assumption.
    - simpl. cbn. eapply ih.
      eapply conv_LetIn_bo. assumption.
    - simpl. cbn. eapply ih.
      eapply conv_Lambda_r. assumption.
  Qed.

  Lemma conv_alt_it_mkProd_or_LetIn :
    forall Δ Γ B B',
      Σ ;;; (Δ ,,, Γ) |- B == B' ->
      Σ ;;; Δ |- it_mkProd_or_LetIn Γ B == it_mkProd_or_LetIn Γ B'.
  Proof.
    intros Δ Γ B B' h.
    induction Γ as [| [na [b|] A] Γ ih ] in Δ, B, B', h |- *.
    - assumption.
    - simpl. cbn. eapply ih.
      eapply conv_LetIn_bo. assumption.
    - simpl. cbn. eapply ih.
      eapply conv_Prod_r. assumption.
  Qed.

  Lemma conv_alt_zippx :
    forall Γ u v ρ,
      Σ ;;; (Γ ,,, stack_context ρ) |- u == v ->
      Σ ;;; Γ |- zippx u ρ == zippx v ρ.
  Proof.
    intros Γ u v ρ h.
    revert u v h. induction ρ ; intros u v h.
    - cbn. assumption.
    - unfold zippx. simpl.
      case_eq (decompose_stack ρ). intros l π e.
      unfold zippx in IHρ. rewrite e in IHρ.
      apply IHρ.
      eapply conv_App_l. assumption.
    - unfold zippx. simpl.
      eapply conv_alt_it_mkLambda_or_LetIn.
      assumption.
    - unfold zippx. simpl.
      eapply conv_alt_it_mkLambda_or_LetIn.
      assumption.
    - unfold zippx. simpl.
      eapply conv_alt_it_mkLambda_or_LetIn.
      assumption.
    - unfold zippx. simpl.
      eapply conv_alt_it_mkLambda_or_LetIn.
      assumption.
    - unfold zippx. simpl.
      eapply conv_alt_it_mkLambda_or_LetIn.
      assumption.
    - unfold zippx. simpl.
      eapply conv_alt_it_mkLambda_or_LetIn. cbn.
      eapply conv_Lambda_r.
      assumption.
    - unfold zippx. simpl.
      eapply conv_alt_it_mkLambda_or_LetIn.
      assumption.
    - unfold zippx. simpl.
      eapply conv_alt_it_mkLambda_or_LetIn. cbn.
      eapply conv_Lambda_r.
      assumption.
    - unfold zippx. simpl.
      eapply conv_alt_it_mkLambda_or_LetIn. assumption.
  Qed.

  Lemma conv_zippx :
    forall Γ u v ρ,
      Σ ;;; Γ ,,, stack_context ρ |- u == v ->
      Σ ;;; Γ |- zippx u ρ == zippx v ρ.
  Proof.
    intros Γ u v ρ uv. eapply conv_alt_zippx ; assumption.
  Qed.

  Lemma conv_zippx' :
    forall Γ leq u v ρ,
      conv leq Σ (Γ ,,, stack_context ρ) u v ->
      conv leq Σ Γ (zippx u ρ) (zippx v ρ).
  Proof.
    intros Γ leq u v ρ h.
    destruct leq.
    - cbn in *. destruct h as [h]. constructor.
      eapply conv_alt_zippx ; assumption.
    - cbn in *. destruct h. constructor.
      eapply cumul_zippx. assumption.
  Qed.

  Lemma cored_eq_term_upto_univ_r :
    forall Re Rle Γ u v u',
      Reflexive Re ->
      Reflexive Rle ->
      Transitive Re ->
      Transitive Rle ->
      SubstUnivPreserving Re ->
      SubstUnivPreserving Rle ->
      (forall u u' : universe, Re u u' -> Rle u u') ->
      eq_term_upto_univ Re Rle u u' ->
      cored Σ Γ v u ->
      exists v',
        cored Σ Γ v' u' /\
        ∥ eq_term_upto_univ Re Rle v v' ∥.
  Proof.
    intros Re Rle Γ u v u' he hle tRe tRle hRe hRle hR e h.
    induction h.
    - eapply red1_eq_term_upto_univ_l in X ; try exact e ; eauto.
      destruct X as [v' [r e']].
      exists v'. split ; auto.
      constructor. assumption. now constructor.
    - specialize (IHh e). destruct IHh as [v' [c [ev]]].
      eapply red1_eq_term_upto_univ_l in X ; try exact ev ; eauto.
      destruct X as [w' [? ?]].
      exists w'. split ; auto.
      eapply cored_trans ; eauto. now constructor.
  Qed.

  Lemma cored_nl :
    forall Γ u v,
      cored Σ Γ u v ->
      cored Σ (nlctx Γ) (nl u) (nl v).
  Admitted.

  Lemma red_nl :
    forall Γ u v,
      red Σ Γ u v ->
      red Σ (nlctx Γ) (nl u) (nl v).
  Admitted.

  Derive Signature for Acc.

  Lemma wf_fun :
    forall A (R : A -> A -> Prop) B (f : B -> A),
      well_founded R ->
      well_founded (fun x y => R (f x) (f y)).
  Proof.
    intros A R B f h x.
    specialize (h (f x)).
    dependent induction h.
    constructor. intros y h.
    eapply H0 ; try reflexivity. assumption.
  Qed.

  Lemma Acc_fun :
    forall A (R : A -> A -> Prop) B (f : B -> A) x,
      Acc R (f x) ->
      Acc (fun x y => R (f x) (f y)) x.
  Proof.
    intros A R B f x h.
    dependent induction h.
    constructor. intros y h.
    eapply H0 ; try reflexivity. assumption.
  Qed.

  (* TODO Put more general lemma in Inversion *)
  Lemma welltyped_it_mkLambda_or_LetIn :
    forall Γ Δ t,
      welltyped Σ Γ (it_mkLambda_or_LetIn Δ t) ->
      welltyped Σ (Γ ,,, Δ) t.
  Proof.
    destruct hΣ as [wΣ].
    intros Γ Δ t h.
    induction Δ as [| [na [b|] A] Δ ih ] in Γ, t, h |- *.
    - assumption.
    - simpl. apply ih in h. cbn in h.
      destruct h as [T h].
      apply inversion_LetIn in h as hh ; auto.
      destruct hh as [s1 [A' [? [? [? ?]]]]].
      exists A'. assumption.
    - simpl. apply ih in h. cbn in h.
      destruct h as [T h].
      apply inversion_Lambda in h as hh ; auto.
      pose proof hh as [s1 [B [? [? ?]]]].
      exists B. assumption.
  Qed.

  Lemma it_mkLambda_or_LetIn_welltyped :
    forall Γ Δ t,
      welltyped Σ (Γ ,,, Δ) t ->
      welltyped Σ Γ (it_mkLambda_or_LetIn Δ t).
  Proof.
    intros Γ Δ t [T h].
    eexists. eapply PCUICGeneration.type_it_mkLambda_or_LetIn.
    eassumption.
  Qed.

  Lemma welltyped_it_mkLambda_or_LetIn_iff :
    forall Γ Δ t,
      welltyped Σ Γ (it_mkLambda_or_LetIn Δ t) <->
      welltyped Σ (Γ ,,, Δ) t.
  Proof.
    intros; split.
    apply welltyped_it_mkLambda_or_LetIn.
    apply it_mkLambda_or_LetIn_welltyped.
  Qed.

  Lemma isWfArity_it_mkLambda_or_LetIn :
    forall Γ Δ T,
      isWfArity typing Σ Γ (it_mkLambda_or_LetIn Δ T) ->
      isWfArity typing Σ (Γ ,,, Δ) T.
  Proof.
    intro Γ; induction Δ in Γ |- *; intro T; [easy|].
    destruct a as [na [bd|] ty].
    - simpl. cbn. intro HH. apply IHΔ in HH.
      destruct HH as [Δ' [s [HH HH']]].
      cbn in HH; apply destArity_app_Some in HH.
      destruct HH as [Δ'' [HH1 HH2]].
      exists Δ'', s. split; tas.
      refine (eq_rect _ (fun Γ => wf_local Σ Γ) HH' _ _).
      rewrite HH2. rewrite app_context_assoc. reflexivity.
    - simpl. cbn. intro HH. apply IHΔ in HH.
      destruct HH as [Δ' [s [HH HH']]]. discriminate.
  Qed.

  Lemma wellformed_it_mkLambda_or_LetIn :
    forall Γ Δ t,
      wellformed Σ Γ (it_mkLambda_or_LetIn Δ t) ->
      wellformed Σ (Γ ,,, Δ) t.
  Proof.
    intros Γ Δ t [Hwf|Hwf];
      [left; now apply welltyped_it_mkLambda_or_LetIn |
       right; destruct Hwf; constructor].
    now apply isWfArity_it_mkLambda_or_LetIn.
  Qed.


  Lemma wellformed_zipp :
    forall Γ t ρ,
      wellformed Σ Γ (zipp t ρ) ->
      wellformed Σ Γ t.
  Proof.
    destruct hΣ as [wΣ].
    intros Γ t ρ h.
    unfold zipp in h.
    case_eq (decompose_stack ρ). intros l π e.
    rewrite e in h. clear - h wΣ.
    destruct h as [[A h]|[h]].
    - left.
      induction l in t, A, h |- *.
      + eexists. eassumption.
      + apply IHl in h.
        destruct h as [T h].
        apply inversion_App in h as hh ; auto.
        rdestruct hh. econstructor. eassumption.
    - right. constructor. destruct l.
      + assumption.
      + destruct h as [ctx [s [h1 _]]].
        rewrite destArity_tApp in h1. discriminate.
  Qed.


  Lemma it_mkLambda_or_LetIn_wellformed :
    forall Γ Δ t,
      wellformed Σ (Γ ,,, Δ) t ->
      wellformed Σ Γ (it_mkLambda_or_LetIn Δ t).
  Admitted.

  (* Wrong for t = alg univ, π = ε, Γ = vass A *)
  Lemma zipx_wellformed :
    forall {Γ t π},
      wellformed Σ Γ (zipc t π) ->
      wellformed Σ [] (zipx Γ t π).
  Proof.
    intros Γ t π h.
    eapply it_mkLambda_or_LetIn_wellformed.
    rewrite app_context_nil_l.
    assumption.
  Qed.

  Lemma wellformed_zipx :
    forall {Γ t π},
      wellformed Σ [] (zipx Γ t π) ->
      wellformed Σ Γ (zipc t π).
  Proof.
    intros Γ t π h.
    apply wellformed_it_mkLambda_or_LetIn in h.
    rewrite app_context_nil_l in h.
    assumption.
  Qed.

  Lemma wellformed_zipc_stack_context Γ t π ρ args
    : decompose_stack π = (args, ρ)
      -> wellformed Σ Γ (zipc t π)
      -> wellformed Σ (Γ ,,, stack_context π) (zipc t (appstack args ε)).
  Proof.
    intros h h1.
    apply decompose_stack_eq in h. subst.
    rewrite stack_context_appstack.
    induction args in Γ, t, ρ, h1 |- *.
    - cbn in *.
      now apply (wellformed_context Γ (t, ρ)).
    - simpl. eauto.
  Qed.

  (* Is it correct? *)
  Lemma wellformed_zipc_zippx :
    forall Γ t π,
      wellformed Σ Γ (zipc t π) ->
      wellformed Σ Γ (zippx t π).
  Proof.
    intros Γ t π h.
    unfold zippx.
    case_eq (decompose_stack π). intros l ρ e.
    pose proof (decompose_stack_eq _ _ _ e). subst. clear e.
    rewrite zipc_appstack in h.
    (* revert h. generalize (mkApps t l); clear t l. *)
    zip fold in h.
    apply wellformed_context in h ; simpl in h.
  (* Qed. *)
  Admitted.

  Lemma lookup_env_const_name :
    forall {c c' d},
      lookup_env Σ c' = Some (ConstantDecl c d) ->
      c' = c.
  Proof.
    intros c c' d e. clear hΣ.
    destruct Σ as [Σ' ?]. cbn in e.
    induction Σ'.
    - cbn in e. discriminate.
    - destruct a.
      + cbn in e. destruct (ident_eq_spec c' k).
        * subst. inversion e. reflexivity.
        * apply IHΣ'. assumption.
      + cbn in e. destruct (ident_eq_spec c' k).
        * inversion e.
        * apply IHΣ'. assumption.
  Qed.

  Lemma red_const :
    forall {Γ n c u cty cb cu},
      Some (ConstantDecl n {| cst_type := cty ; cst_body := Some cb ; cst_universes := cu |})
      = lookup_env Σ c ->
      red (fst Σ) Γ (tConst c u) (subst_instance_constr u cb).
  Proof.
    intros Γ n c u cty cb cu e.
    symmetry in e.
    pose proof (lookup_env_const_name e). subst.
    econstructor.
    - econstructor.
    - econstructor.
      + exact e.
      + reflexivity.
  Qed.

  Lemma cored_const :
    forall {Γ n c u cty cb cu},
      Some (ConstantDecl n {| cst_type := cty ; cst_body := Some cb ; cst_universes := cu |})
      = lookup_env Σ c ->
      cored (fst Σ) Γ (subst_instance_constr u cb) (tConst c u).
  Proof.
    intros Γ n c u cty cb cu e.
    symmetry in e.
    pose proof (lookup_env_const_name e). subst.
    econstructor.
    econstructor.
    - exact e.
    - reflexivity.
  Qed.

  Derive Signature for cumul.
  Derive Signature for red1.

  Lemma app_reds_r :
    forall Γ u v1 v2,
      red Σ Γ v1 v2 ->
      red Σ Γ (tApp u v1) (tApp u v2).
  Proof.
    intros Γ u v1 v2 h.
    revert u. induction h ; intros u.
    - constructor.
    - econstructor.
      + eapply IHh.
      + constructor. assumption.
  Qed.

  Lemma app_cored_r :
    forall Γ u v1 v2,
      cored Σ Γ v1 v2 ->
      cored Σ Γ (tApp u v1) (tApp u v2).
  Proof.
    intros Γ u v1 v2 h.
    induction h.
    - constructor. constructor. assumption.
    - eapply cored_trans.
      + eapply IHh.
      + constructor. assumption.
  Qed.

  Fixpoint isAppProd (t : term) : bool :=
    match t with
    | tApp t l => isAppProd t
    | tProd na A B => true
    | _ => false
    end.

  Fixpoint isProd t :=
    match t with
    | tProd na A B => true
    | _ => false
    end.

  Lemma isAppProd_mkApps :
    forall t l, isAppProd (mkApps t l) = isAppProd t.
  Proof.
    intros t l. revert t.
    induction l ; intros t.
    - reflexivity.
    - cbn. rewrite IHl. reflexivity.
  Qed.

  Lemma isProdmkApps :
    forall t l,
      isProd (mkApps t l) ->
      l = [].
  Proof.
    intros t l h.
    revert t h.
    induction l ; intros t h.
    - reflexivity.
    - cbn in h. specialize IHl with (1 := h). subst.
      cbn in h. discriminate h.
  Qed.

  Lemma isSortmkApps :
    forall t l,
      isSort (mkApps t l) ->
      l = [].
  Proof.
    intros t l h.
    revert t h.
    induction l ; intros t h.
    - reflexivity.
    - cbn in h. specialize IHl with (1 := h). subst.
      cbn in h. exfalso. assumption.
  Qed.

  Lemma isAppProd_isProd :
    forall Γ t,
      isAppProd t ->
      welltyped Σ Γ t ->
      isProd t.
  Proof.
    destruct hΣ as [wΣ].
    intros Γ t hp hw.
    induction t in Γ, hp, hw |- *.
    all: try discriminate hp.
    - reflexivity.
    - simpl in hp.
      specialize IHt1 with (1 := hp).
      assert (welltyped Σ Γ t1) as h.
      { destruct hw as [T h].
        apply inversion_App in h as hh ; auto.
        destruct hh as [na [A' [B' [? [? ?]]]]].
        eexists. eassumption.
      }
      specialize IHt1 with (1 := h).
      destruct t1.
      all: try discriminate IHt1.
      destruct hw as [T hw'].
      apply inversion_App in hw' as ihw' ; auto.
      destruct ihw' as [na' [A' [B' [hP [? ?]]]]].
      apply inversion_Prod in hP as [s1 [s2 [? [? bot]]]] ; auto.
      apply PCUICPrincipality.invert_cumul_prod_r in bot ; auto.
      destruct bot as [? [? [? [[r ?] ?]]]].
      exfalso. clear - r wΣ.
      revert r. generalize (Universe.sort_of_product s1 s2). intro s. clear.
      intro r.
      dependent induction r.
      assert (h : P = tSort s).
      { clear - r. induction r ; auto. subst.
        dependent destruction r0.
        assert (h : isSort (mkApps (tFix mfix idx) args)).
        { rewrite <- H. constructor. }
        apply isSortmkApps in h. subst. cbn in H.
        discriminate.
      }
      subst.
      dependent destruction r0.
      assert (h : isSort (mkApps (tFix mfix idx) args)).
      { rewrite <- H. constructor. }
      apply isSortmkApps in h. subst. cbn in H.
      discriminate.
  Qed.

  Lemma mkApps_Prod_nil :
    forall Γ na A B l,
      welltyped Σ Γ (mkApps (tProd na A B) l) ->
      l = [].
  Proof.
    intros Γ na A B l h.
    pose proof (isAppProd_isProd) as hh.
    specialize hh with (2 := h).
    rewrite isAppProd_mkApps in hh.
    specialize hh with (1 := eq_refl).
    apply isProdmkApps in hh. assumption.
  Qed.

  Lemma mkApps_Prod_nil' :
    forall Γ na A B l,
      wellformed Σ Γ (mkApps (tProd na A B) l) ->
      l = [].
  Proof.
    intros Γ na A B l [h | [[ctx [s [hd hw]]]]].
    - eapply mkApps_Prod_nil. eassumption.
    - destruct l ; auto.
      cbn in hd. rewrite destArity_tApp in hd. discriminate.
  Qed.

  (* TODO MOVE or even replace old lemma *)
  Lemma decompose_stack_noStackApp :
    forall π l ρ,
      decompose_stack π = (l,ρ) ->
      isStackApp ρ = false.
  Proof.
    intros π l ρ e.
    destruct ρ. all: auto.
    exfalso. eapply decompose_stack_not_app. eassumption.
  Qed.

  (* TODO MOVE *)
  Lemma stack_context_decompose :
    forall π,
      stack_context (snd (decompose_stack π)) = stack_context π.
  Proof.
    intros π.
    case_eq (decompose_stack π). intros l ρ e.
    cbn. pose proof (decompose_stack_eq _ _ _ e). subst.
    rewrite stack_context_appstack. reflexivity.
  Qed.

  Lemma it_mkLambda_or_LetIn_inj :
    forall Γ u v,
      it_mkLambda_or_LetIn Γ u =
      it_mkLambda_or_LetIn Γ v ->
      u = v.
  Proof.
    intros Γ u v e.
    revert u v e.
    induction Γ as [| [na [b|] A] Γ ih ] ; intros u v e.
    - assumption.
    - simpl in e. cbn in e.
      apply ih in e.
      inversion e. reflexivity.
    - simpl in e. cbn in e.
      apply ih in e.
      inversion e. reflexivity.
  Qed.

  Lemma nleq_term_zipc :
    forall u v π,
      nleq_term u v ->
      nleq_term (zipc u π) (zipc v π).
  Proof.
    intros u v π h.
    eapply ssrbool.introT.
    - eapply reflect_nleq_term.
    - cbn. rewrite 2!nl_zipc. f_equal.
      eapply ssrbool.elimT.
      + eapply reflect_nleq_term.
      + assumption.
  Qed.

  Lemma nleq_term_zipx :
    forall Γ u v π,
      nleq_term u v ->
      nleq_term (zipx Γ u π) (zipx Γ v π).
  Proof.
    intros Γ u v π h.
    unfold zipx.
    eapply nleq_term_it_mkLambda_or_LetIn.
    eapply nleq_term_zipc.
    assumption.
  Qed.

  Lemma red_lambda_inv Γ na A1 b1 T :
    red Σ Γ (tLambda na A1 b1) T ->
    ∑ A2 b2, (T = tLambda na A2 b2) *
             red Σ Γ A1 A2 * red Σ (Γ ,, vass na A1) b1 b2.
  Proof.
    intros.
    eapply red_alt in X. eapply clos_rt_rt1n_iff in X.
    depind X.
    - eexists _, _; intuition eauto.
    - depelim r; solve_discr; specialize (IHX _ _ _ _ eq_refl);
      destruct IHX as [A2 [B2 [[-> ?] ?]]].
      * eexists _, _; intuition eauto.
        now eapply red_step with M'.
        eapply PCUICConfluence.red_red_ctx; eauto. admit.
        constructor; auto. eapply All2_local_env_red_refl.
        red. auto.
      * eexists _, _; intuition eauto.
        now eapply red_step with M'.
  Admitted.

  Hint Resolve conv_alt_refl conv_alt_red : core.
  Hint Resolve conv_ctx_refl: core.

  Lemma Lambda_conv_inv :
    forall leq Γ na1 na2 A1 A2 b1 b2,
      wf_local Σ Γ ->
      conv leq Σ Γ (tLambda na1 A1 b1) (tLambda na2 A2 b2) ->
      ∥ Σ ;;; Γ |- A1 == A2 ∥ /\ conv leq Σ (Γ ,, vass na1 A1) b1 b2.
  Proof.
    intros * wfΓ.
    destruct leq; simpl in *.
    destruct 1.
    eapply conv_alt_red in X as [l [r [[redl redr] eq]]].
    eapply red_lambda_inv in redl as [A1' [b1' [[-> ?] ?]]].
    eapply red_lambda_inv in redr as [A2' [b2' [[-> ?] ?]]].
    depelim eq. destruct hΣ.
    assert(Σ ;;; Γ |- A1 == A2).
    { eapply conv_alt_trans with A1'; auto.
      eapply conv_alt_trans with A2'; auto.
      apply conv_alt_sym; auto. }
    split; constructor; auto.
    eapply conv_alt_trans with b1'; auto.
    eapply conv_alt_trans with b2'; auto.
    apply conv_alt_sym; auto.
    eapply conv_alt_conv_ctx; eauto.
    constructor; auto. constructor. now apply conv_alt_sym.
    admit. (* Similar *)
  Admitted.

  (* Let bindings are not injective, so it_mkLambda_or_LetIn is not either.
     However, when they are all lambdas they become injective for conversion.
     stack_contexts only produce lambdas so we can use this property on them.
   *)
  Fixpoint let_free_context (Γ : context) :=
    match Γ with
    | [] => true
    | {| decl_name := na ; decl_body := Some b ; decl_type := B |} :: Γ => false
    | {| decl_name := na ; decl_body := None ; decl_type := B |} :: Γ =>
      let_free_context Γ
    end.

  Notation conv_ctx Σ Γ Γ' := (context_relation (conv_decls Σ) Γ Γ').

  Lemma it_mkLambda_or_LetIn_let_free_conv_inv :
    forall Γ Δ1 Δ2 t1 t2,
      let_free_context Δ1 ->
      let_free_context Δ2 ->
      Σ ;;; Γ |- it_mkLambda_or_LetIn Δ1 t1 == it_mkLambda_or_LetIn Δ2 t2 ->
      conv_ctx Σ (Γ ,,, Δ1) (Γ ,,, Δ2) × Σ ;;; Γ ,,, Δ1 |- t1 == t2.
  Admitted.

  Lemma let_free_stack_context :
    forall π,
      let_free_context (stack_context π).
  Proof.
    intros π.
    induction π.
    all: (simpl ; rewrite ?IHπ ; reflexivity).
  Qed.

  Lemma it_mkLambda_or_LetIn_stack_context_conv_inv :
    forall Γ π1 π2 t1 t2,
      Σ ;;; Γ |- it_mkLambda_or_LetIn (stack_context π1) t1
                 == it_mkLambda_or_LetIn (stack_context π2) t2 ->
      conv_ctx Σ (Γ ,,, stack_context π1) (Γ ,,, stack_context π2) ×
      Σ ;;; Γ ,,, stack_context π1 |- t1 == t2.
  Proof.
    intros Γ π1 π2 t1 t2 h.
    eapply it_mkLambda_or_LetIn_let_free_conv_inv.
    - eapply let_free_stack_context.
    - eapply let_free_stack_context.
    - assumption.
  Qed.

  Lemma it_mkLambda_or_LetIn_let_free_conv'_inv :
    forall leq Γ Δ1 Δ2 t1 t2,
      let_free_context Δ1 ->
      let_free_context Δ2 ->
      conv leq Σ Γ (it_mkLambda_or_LetIn Δ1 t1) (it_mkLambda_or_LetIn Δ2 t2) ->
      ∥ conv_ctx Σ (Γ ,,, Δ1) (Γ ,,, Δ2) ∥ /\ conv leq Σ (Γ ,,, Δ1) t1 t2.
  Admitted.

  Lemma it_mkLambda_or_LetIn_stack_context_conv'_inv :
    forall leq Γ π1 π2 t1 t2,
      conv leq Σ Γ (it_mkLambda_or_LetIn (stack_context π1) t1)
                   (it_mkLambda_or_LetIn (stack_context π2) t2) ->
      ∥ conv_ctx Σ (Γ ,,, stack_context π1) (Γ ,,, stack_context π2) ∥ /\
      conv leq Σ (Γ ,,, stack_context π1) t1 t2.
  Proof.
    intros leq Γ π1 π2 t1 t2 h.
    eapply it_mkLambda_or_LetIn_let_free_conv'_inv.
    - eapply let_free_stack_context.
    - eapply let_free_stack_context.
    - assumption.
  Qed.

  Lemma it_mkLambda_or_LetIn_conv' :
    forall leq Γ Δ1 Δ2 t1 t2,
      conv_ctx Σ (Γ ,,, Δ1) (Γ ,,, Δ2) ->
      conv leq Σ (Γ ,,, Δ1) t1 t2 ->
      conv leq Σ Γ (it_mkLambda_or_LetIn Δ1 t1) (it_mkLambda_or_LetIn Δ2 t2).
  Admitted.

  Lemma Prod_conv :
    forall leq Γ na1 A1 B1 na2 A2 B2,
      Σ ;;; Γ |- A1 == A2 ->
      conv leq Σ (Γ ,, vass na1 A1) B1 B2 ->
      conv leq Σ Γ (tProd na1 A1 B1) (tProd na2 A2 B2).
  Admitted.

  Lemma it_mkLambda_or_LetIn_conv :
    forall Γ Δ1 Δ2 t1 t2,
      conv_ctx Σ (Γ ,,, Δ1) (Γ ,,, Δ2) ->
      Σ ;;; Γ ,,, Δ1 |- t1 == t2 ->
      Σ ;;; Γ |- it_mkLambda_or_LetIn Δ1 t1 == it_mkLambda_or_LetIn Δ2 t2.
  Admitted.

  Lemma App_conv :
    forall Γ t1 t2 u1 u2,
      Σ ;;; Γ |- t1 == t2 ->
      Σ ;;; Γ |- u1 == u2 ->
      Σ ;;; Γ |- tApp t1 u1 == tApp t2 u2.
  Admitted.

  Lemma mkApps_conv_weak :
    forall Γ u1 u2 l,
      Σ ;;; Γ |- u1 == u2 ->
      Σ ;;; Γ |- mkApps u1 l == mkApps u2 l.
  Admitted.

  Lemma cored_red_cored :
    forall Γ u v w,
      cored Σ Γ w v ->
      red Σ Γ u v ->
      cored Σ Γ w u.
  Proof.
    intros Γ u v w h1 h2.
    revert u h2. induction h1 ; intros t h2.
    - eapply cored_red_trans ; eassumption.
    - eapply cored_trans.
      + eapply IHh1. assumption.
      + assumption.
  Qed.

  Lemma red_neq_cored :
    forall Γ u v,
      red Σ Γ u v ->
      u <> v ->
      cored Σ Γ v u.
  Proof.
    intros Γ u v r n.
    destruct r.
    - exfalso. apply n. reflexivity.
    - eapply cored_red_cored ; try eassumption.
      constructor. assumption.
  Qed.

  Lemma red_welltyped :
    forall {Γ u v},
      welltyped Σ Γ u ->
      ∥ red (fst Σ) Γ u v ∥ ->
      welltyped Σ Γ v.
  Proof.
    destruct hΣ as [wΣ]; clear hΣ.
    intros Γ u v h [r].
    revert h. induction r ; intros h.
    - assumption.
    - specialize IHr with (1 := ltac:(eassumption)).
      destruct IHr as [A ?]. exists A.
      eapply sr_red1 ; eauto with wf.
  Qed.

  Lemma red_cored_cored :
    forall Γ u v w,
      red Σ Γ v w ->
      cored Σ Γ v u ->
      cored Σ Γ w u.
  Proof.
    intros Γ u v w h1 h2.
    revert u h2. induction h1 ; intros t h2.
    - assumption.
    - eapply cored_trans.
      + eapply IHh1. assumption.
      + assumption.
  Qed.

  (* TODO MOVE It needs wf Σ entirely *)
  Lemma subject_conversion :
    forall Γ u v A B,
      Σ ;;; Γ |- u : A ->
      Σ ;;; Γ |- v : B ->
      Σ ;;; Γ |- u == v ->
      ∑ C,
        Σ ;;; Γ |- u : C ×
        Σ ;;; Γ |- v : C.
  Proof.
    intros Γ u v A B hu hv h.
    (* apply conv_conv_alt in h. *)
    (* apply conv_alt_red in h as [u' [v' [? [? ?]]]]. *)
    (* pose proof (subject_reduction _ Γ _ _ _ hΣ hu r) as hu'. *)
    (* pose proof (subject_reduction _ Γ _ _ _ hΣ hv r0) as hv'. *)
    (* pose proof (typing_alpha _ _ _ _ hu' e) as hv''. *)
    (* pose proof (principal_typing _ hv' hv'') as [C [? [? hvC]]]. *)
    (* apply eq_term_sym in e as e'. *)
    (* pose proof (typing_alpha _ _ _ _ hvC e') as huC. *)
    (* Not clear.*)
  Abort.

  Lemma welltyped_zipc_replace :
    forall Γ u v π,
      welltyped Σ Γ (zipc v π) ->
      welltyped Σ (Γ ,,, stack_context π) u ->
      Σ ;;; Γ ,,, stack_context π |- u == v ->
      welltyped Σ Γ (zipc u π).
  Proof.
    destruct hΣ as [wΣ].
    intros Γ u v π hv hu heq.
    induction π in u, v, hu, hv, heq |- *.
    - simpl in *. assumption.
    - simpl in *. eapply IHπ.
      + eassumption.
      + zip fold in hv. apply welltyped_context in hv.
        simpl in hv.
        destruct hv as [Tv hv].
        destruct hu as [Tu hu].
        apply inversion_App in hv as ihv ; auto.
        destruct ihv as [na [A' [B' [hv' [ht ?]]]]].
        (* Seems to be derivable (tediously) from some principal type lemma. *)
        admit.
      + (* Congruence *)
        admit.
  Admitted.

  Lemma wellformed_zipc_replace :
    forall Γ u v π,
      wellformed Σ Γ (zipc v π) ->
      wellformed Σ (Γ ,,, stack_context π) u ->
      Σ ;;; Γ ,,, stack_context π |- u == v ->
      wellformed Σ Γ (zipc u π).
  Admitted.

  Derive Signature for typing.

  (* Follows from principality, inversion of cumul/confluence *)
  Lemma Construct_Ind_ind_eq :
    forall {Γ n i args u i' args' u'},
      Σ ;;; Γ |- mkApps (tConstruct i n u) args : mkApps (tInd i' u') args' ->
      i = i'.
  Proof.
    destruct hΣ as [wΣ].
    intros Γ n i args u i' args' u' h.
    eapply inversion_mkApps in h ; auto.
    destruct h as [T [U [hC [hs hc]]]].
    apply inversion_Construct in hC
      as [mdecl [idecl [cdecl [hΓ [isdecl [const htc]]]]]].
    unfold type_of_constructor in htc. simpl in htc.
    destruct i as [mind nind]. simpl in *.
    destruct cdecl as [[cna ct] cn]. cbn in htc.
    destruct mdecl as [mnpars mpars mbod muni]. simpl in *.
    destruct idecl as [ina ity ike ict iprj]. simpl in *.
    unfold declared_constructor in isdecl. cbn in isdecl.
    destruct isdecl as [[dm hin] hn]. simpl in *.
    unfold declared_minductive in dm.
    (* Do we need to exploit wellformedness of the context?? *)
    (* We should also use invert_cumul_ind_l at some point. *)
  Admitted.

  Require Import PCUICWeakeningEnv.

  Lemma Proj_red_cond :
    forall Γ i pars narg i' c u l,
      wellformed Σ Γ (tProj (i, pars, narg) (mkApps (tConstruct i' c u) l)) ->
      nth_error l (pars + narg) <> None.
  Proof.
    intros Γ i pars narg i' c u l [[T h]|[[ctx [s [e _]]]]];
      [|discriminate].
    apply inversion_Proj in h.
    destruct h as [uni [mdecl [idecl [pdecl [args' [d [hc [? ?]]]]]]]].
    eapply on_declared_projection in d. destruct d as [? [? ?]].
    simpl in *.
    destruct p.
    destruct o0.
  Admitted.

  Lemma Case_Construct_ind_eq :
    forall {Γ ind ind' npar pred i u brs args},
      wellformed Σ Γ (tCase (ind, npar) pred (mkApps (tConstruct ind' i u) args) brs) ->
      ind = ind'.
  Proof.
    destruct hΣ as [wΣ].
    intros Γ ind ind' npar pred i u brs args [[A h]|[[ctx [s [e _]]]]];
      [|discriminate].
    apply inversion_Case in h as ih ; auto.
    destruct ih
      as [uni [args' [mdecl [idecl [pty [indctx [pctx [ps [btys [? [? [? [? [? [? [ht0 [? ?]]]]]]]]]]]]]]]]].
    apply Construct_Ind_ind_eq in ht0. eauto.
  Qed.

  Lemma Proj_Constuct_ind_eq :
    forall Γ i i' pars narg c u l,
      wellformed Σ Γ (tProj (i, pars, narg) (mkApps (tConstruct i' c u) l)) ->
      i = i'.
  Proof.
    destruct hΣ as [wΣ].
    intros Γ i i' pars narg c u l [[T h]|[[ctx [s [e _]]]]];
      [|discriminate].
    apply inversion_Proj in h ; auto.
    destruct h as [uni [mdecl [idecl [pdecl [args' [? [hc [? ?]]]]]]]].
    apply Construct_Ind_ind_eq in hc. eauto.
  Qed.

End Lemmata.


Require Import PCUICWeakening PCUICGeneration uGraph.

Lemma strengthening `{cf : checker_flags} :
  forall {Σ Γ Γ' Γ'' t T},
    wf Σ.1 ->
    Σ ;;; Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ'
    |- lift #|Γ''| #|Γ'| t : lift #|Γ''| #|Γ'| T ->
    Σ;;; Γ ,,, Γ' |- t : T.
Admitted.

Lemma map_option_out_mapi :
  forall {A B} (l : list A) (l' : list B) f P,
    map_option_out (mapi f l) = Some l' ->
    Alli (fun i x => on_Some_or_None P (f i x)) 0 l ->
    All P l'.
Proof.
  intros A B l l' f P.
  unfold mapi. generalize 0.
  induction l in l' |- *; simpl; intro n.
  - inversion 1; constructor.
  - case_eq (f n a); [|discriminate].
    intros b Hb.
    case_eq (map_option_out (mapi_rec f l (S n))); [|discriminate].
    intros l0 Hl0 HH0 HH1.
    inversion HH0; subst; clear HH0.
    inversion HH1; subst.
    constructor. now rewrite Hb in H0.
    now eapply IHl.
Qed.

Lemma Alli_id :
  forall {A} {P : nat -> A -> Type} (l : list A) (n : nat),
    (forall n x, P n x) -> Alli P n l.
Proof.
  intros A P l n h.
  induction l in n |- * ; constructor ; eauto.
Qed.

Lemma type_Case_valid_btys {cf:checker_flags} :
  forall Σ Γ ind u p args mdecl idecl
    (isdecl : declared_inductive (fst Σ) mdecl ind idecl)
    (pars := List.firstn mdecl.(ind_npars) args)
    pty (Hp : Σ ;;; Γ |- p : pty)
    indctx pctx ps btys
    (e : types_of_case ind mdecl idecl pars u p pty = Some (indctx, pctx, ps, btys))
    (Hc : PCUICTyping.check_correct_arity (global_ext_constraints Σ) idecl ind u indctx pars pctx),
    Forall (fun A : nat × term => wellformed Σ Γ (snd A)) btys.
Proof.
  intros Σ Γ ind u p args mdecl idecl isdecl pars pty Hp indctx pctx ps btys e
         Hc.
  unfold types_of_case in e.
  case_eq (instantiate_params (ind_params mdecl) pars (ind_type idecl));
    [|intro HH; rewrite HH in e; discriminate e].
  intros params' He; rewrite He in e.
  case_eq (destArity [] params');
    [|intro HH; rewrite HH in e; discriminate e].
  intros [params_ctx params_sort] He1; rewrite He1 in e.
  case_eq (destArity [] pty);
    [|intro HH; rewrite HH in e; discriminate e].
  intros [pty_ctx pty_sort] He2; rewrite He2 in e.

  case_eq (map_option_out (build_branches_type ind mdecl idecl pars u p));
    [|intro HH; rewrite HH in e; discriminate e].
  intros brtys He3; rewrite He3 in e.
  inversion e; subst; clear e.
  unfold build_branches_type in He3.
  solve_all.
  eapply (map_option_out_mapi (ind_ctors idecl) btys _ _ He3); clear He3.
  apply Alli_id.
  intros i [[id ctor] k].
  case_eq (instantiate_params (ind_params mdecl) pars ((subst0 (inds (inductive_mind ind) u (ind_bodies mdecl))) (subst_instance_constr u ctor))); [|cbn; trivial].
  intros ipars Hipars.
  case_eq (decompose_prod_assum [] ipars). intros ipars0 ipars1 ipars01.
  case_eq (chop (ind_npars mdecl) (snd (decompose_app ipars1))).
  intros ipars10 ipars11 Hipars1. cbn.
  (* left. econstructor. *)
  (* clear params' He. *)

  (* apply PCUICWeakeningEnv.on_declared_inductive in X2; try assumption. *)
  (* destruct X2 as [XX2 XX3]. *)
  (* apply onConstructors in XX3; unfold on_constructors in XX3. *)
  (* eapply Alli_impl; try eassumption. *)
  (* clear -He. *)
  (* intros n [[id ctor_ty] nc] X. *)
  (* destruct X as [X1 X2]; cbn in *. *)
Admitted.

Lemma isWfArity_or_Type_cumul {cf:checker_flags} :
  forall Σ {Γ A A'},
    Σ;;; Γ |- A' <= A ->
    isWfArity_or_Type Σ Γ A' ->
    isWfArity_or_Type Σ Γ A.
Admitted.
