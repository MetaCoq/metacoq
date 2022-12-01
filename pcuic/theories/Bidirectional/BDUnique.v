From Coq Require Import Bool List Arith Lia.
From MetaCoq.Template Require Import config utils monad_utils.
From MetaCoq.PCUIC Require Import PCUICGlobalEnv PCUICAst PCUICAstUtils PCUICTactics PCUICInduction PCUICLiftSubst PCUICTyping PCUICEquality PCUICArities PCUICInversion PCUICReduction PCUICSubstitution PCUICConversion PCUICCumulativity PCUICGeneration PCUICWfUniverses PCUICContextConversion PCUICContextSubst PCUICContexts PCUICSpine PCUICWfUniverses PCUICUnivSubst PCUICClosed PCUICInductives PCUICValidity PCUICInductiveInversion PCUICConfluence PCUICWellScopedCumulativity PCUICSR PCUICOnFreeVars PCUICClosedTyp.
From MetaCoq.PCUIC Require Import BDTyping BDToPCUIC BDFromPCUIC.

Require Import ssreflect ssrbool.
From Equations Require Import Equations.
Require Import Equations.Type.Relation Equations.Type.Relation_Properties.
Require Import Equations.Prop.DepElim.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).


Section BDUnique.

Context `{cf : checker_flags}.
Context (Σ : global_env_ext).
Context (wfΣ : wf Σ).

Let Pinfer Γ t T :=
  wf_local Σ Γ ->
  forall T', Σ ;;; Γ |- t ▹ T' ->
  ∑ T'', Σ ;;; Γ ⊢ T ⇝ T'' × Σ ;;; Γ ⊢ T' ⇝ T''.

Let Psort Γ t u :=
  wf_local Σ Γ ->
  forall u', Σ ;;; Γ |- t ▹□ u' ->
  u = u'.

Let Pprod Γ t (na : aname) A B :=
  wf_local Σ Γ ->
  forall na' A' B', Σ ;;; Γ |- t ▹Π (na',A',B') ->
  ∑ A'' B'',
  [× na = na', Σ ;;; Γ ⊢ A ⇝ A'', Σ ;;; Γ ⊢ A' ⇝ A'',
      Σ ;;; Γ,, vass na A ⊢ B ⇝ B'' & Σ ;;; Γ,, vass na A' ⊢ B' ⇝ B''].

Let Pind Γ ind t u args :=
  wf_local Σ Γ ->
  forall ind' u' args', Σ ;;; Γ |- t ▹{ind'} (u',args') ->
  ∑ args'',
  [× ind = ind',
      u = u',
      red_terms Σ Γ args args'' &
      red_terms Σ Γ args' args''].

Let Pcheck (Γ : context) (t T : term) := True.

Let PΓ (Γ : context) := True.

Let PΓ_rel (Γ Γ' : context) := True.

Theorem bidirectional_unique : env_prop_bd Σ Pcheck Pinfer Psort Pprod Pind PΓ PΓ_rel.
Proof using wfΣ.

  apply bidir_ind_env.

  all: intros ; red ; auto.
  1-9,11-13: intros ? T' ty_T' ; inversion_clear ty_T'.
  14-17: intros.

  - rewrite H in H0.
    inversion H0. subst. clear H0.
    eexists ; split.
    all: eapply closed_red_refl.
    2,4: eapply PCUICInversion.nth_error_closed_context.
    all: fvs.

  - eexists ; split.
    all: eapply closed_red_refl ; fvs.

  - apply H in X2 => //.
    apply H0 in X3.
    2:{ constructor ; auto. now eapply infering_sort_isType. }
    subst.
    eexists ; split.
    all: eapply closed_red_refl ; fvs.

  - apply X1 in X4 as [bty' []].
    2:{ constructor ; auto. now eapply infering_sort_isType. }
    exists (tProd n t bty') ; split.
    all: now eapply closed_red_prod_codom.

  - apply X2 in X6 as [A' []].
    2:{ constructor ; auto. 2: eapply checking_typing ; tea. all: now eapply infering_sort_isType. }
    exists (tLetIn n b B A').
    assert (Σ ;;; Γ |- b : B)
      by (eapply checking_typing ; tea ; now eapply infering_sort_isType).
    split.
    all: eapply closed_red_letin ; tea.
    all: apply closed_red_refl.
    all: try now apply wf_local_closed_context.
    1,3: now eapply subject_is_open_term.
    all: now eapply type_is_open_term.

  - unshelve epose proof (X0 _ _ _ _ X3) as (A''&B''&[]) ; tea.
    subst.
    exists (B''{0 := u}).
    split.
    all: eapply (closed_red_subst (Δ := [_]) (Γ' := [])) ; tea.
    + constructor.
      1: constructor.
      rewrite subst_empty.
      eapply checking_typing ; tea.
      now eapply isType_tProd, validity, infering_prod_typing.
    + constructor.
      1: constructor.
      rewrite subst_empty.
      eapply checking_typing ; tea.
      now eapply isType_tProd, validity, infering_prod_typing.

  - replace decl0 with decl by (eapply declared_constant_inj ; eassumption).
    eexists ; split.
    all: eapply closed_red_refl.
    1,3: fvs.
    all: rewrite on_free_vars_subst_instance.
    all: now eapply closed_on_free_vars, declared_constant_closed_type.

  - replace idecl0 with idecl by (eapply declared_inductive_inj ; eassumption).
    eexists ; split.
    all: eapply closed_red_refl.
    1,3: fvs.
    all: rewrite on_free_vars_subst_instance.
    all: now eapply closed_on_free_vars, declared_inductive_closed_type.

  - replace cdecl0 with cdecl by (eapply declared_constructor_inj ; eassumption).
    replace mdecl0 with mdecl by (eapply declared_constructor_inj ; eassumption).
    eexists ; split.
    all: eapply closed_red_refl.
    1,3: fvs.
    all: now eapply closed_on_free_vars, declared_constructor_closed_type.

  - eapply declared_projection_inj in H as (?&?&?&?); tea.
    subst.
    move: (X2) => tyc'.
    eapply X0 in X2 as [args'' []] ; tea.
    eapply infering_ind_typing in X ; tea.
    eapply infering_ind_typing in tyc' ; tea.
    subst.
    exists (subst0 (c :: List.rev args'') (proj_type pdecl)@[u0]).
    split.
    + eapply closed_red_red_subst0 ; tea.
      3: eapply subslet_untyped_subslet, projection_subslet ; tea.
      * eapply is_closed_context_weaken.
        1: fvs.
        eapply wf_local_closed_context, wf_projection_context ; tea.
        now eapply validity, isType_mkApps_Ind_proj_inv in X as [].
      * constructor.
        2: now apply All2_rev.
        apply closed_red_refl.
        1: fvs.
        now eapply subject_is_open_term.
      * now eapply validity.
      * rewrite on_free_vars_subst_instance.
        move: (H1) => H.
        eapply declared_projection_closed in H; eauto.
        rewrite (declared_minductive_ind_npars H1) in H.
        cbn in H. len.
        rewrite closedn_on_free_vars //.
        eapply closed_upwards; tea. cbn. lia.
    + eapply closed_red_red_subst0 ; tea.
      3: eapply subslet_untyped_subslet, projection_subslet ; tea.
      * eapply is_closed_context_weaken.
        1: fvs.
        eapply wf_local_closed_context, wf_projection_context ; tea.
        now eapply validity, isType_mkApps_Ind_proj_inv in X as [].
      * constructor.
        2: now apply All2_rev.
        apply closed_red_refl.
        1: fvs.
        now eapply subject_is_open_term.
      * now eapply validity.
      * rewrite on_free_vars_subst_instance.
        move: (H1) => H.
        eapply declared_projection_closed in H; eauto.
        rewrite (declared_minductive_ind_npars H1) in H.
        cbn in H. len.
        rewrite closedn_on_free_vars //.
        eapply closed_upwards; tea. cbn. lia.

  - rewrite H3 in H0 ; injection H0 as ->.
    eapply nth_error_all in X as (?&[]); tea.
    eexists ; split.
    all: eapply closed_red_refl.
    1,3:fvs.
    all: now eapply subject_is_open_term, infering_sort_typing.

  - rewrite H3 in H0 ; injection H0 as ->.
    eapply nth_error_all in X as (?&[]); tea.
    eexists ; split.
    all: eapply closed_red_refl.
    1,3:fvs.
    all: now eapply subject_is_open_term, infering_sort_typing.

  - intros ? T' ty_T'.
    inversion ty_T' ; subst.
    move: (H) => /declared_inductive_inj /(_ H13) [? ?].
    subst.
    assert (op' : is_open_term Γ (mkApps ptm0 (skipn (ci_npar ci) args0 ++ [c]))).
      by now eapply type_is_open_term, infering_typing.
    move: op'.
    rewrite on_free_vars_mkApps => /andP [optm' oargs'].
    eapply X0 in X9 as [args'' []] ; tea.
    subst.
    eexists (mkApps ptm ((skipn (ci_npar ci) args'') ++ [c])).
    split.
    + eapply into_closed_red.
      * eapply red_mkApps.
        1: reflexivity.
        eapply All2_app.
        2: now constructor.
        eapply All2_skipn, All2_impl ; tea.
        intros ? ? r.
        now apply r.
      * fvs.
      * eapply type_is_open_term, infering_typing ; tea.
        now econstructor.
    + eapply into_closed_red.
      * eapply red_mkApps.
        1: reflexivity.
        eapply All2_app.
        2: now constructor.
        eapply All2_skipn, All2_impl ; tea.
        intros ? ? r.
        now apply r.
      * fvs.
      * now eapply type_is_open_term, infering_typing.

  - inversion X1; subst.
    rewrite H in H2; noconf H2.
    have eq := (declared_constant_inj _ _ H0 H3); subst cdecl0.
    exists (tConst prim_ty []).
    split; eapply closed_red_refl; fvs.

  - inversion X3 ; subst.
    eapply X0 in X4 as [T'' []]; subst ; tea.
    eapply into_closed_red in X1 ; fvs.
    eapply into_closed_red in X5 ; fvs.
    eapply closed_red_confluence in X5 as [? [? ru']]; tea.
    eapply invert_red_sort in ru' ; subst.
    eapply closed_red_confluence in X1 as [? [ru' ru]].
    2: now etransitivity.
    eapply invert_red_sort in ru ; subst.
    eapply invert_red_sort in ru'.
    now congruence.

  - inversion X3 ; subst.
    eapply X0 in X4 as [T'' []]; subst ; tea.
    eapply into_closed_red in X1 ; fvs.
    eapply into_closed_red in X5 ; fvs.
    eapply closed_red_confluence in X5 as [? [? rA']]; tea.
    eapply invert_red_prod in rA' as (?&B0&[]); subst.
    eapply closed_red_confluence in X1 as [? [rA' rA]].
    2: now etransitivity.
    eapply invert_red_prod in rA as (?&?&[]); subst.
    eapply invert_red_prod in rA' as (A''&B''&[]) ; subst.
    injection e as -> -> ->.
    exists A'', B'' ; split ; tea.
    1: reflexivity.
    1: now etransitivity.
    etransitivity ; tea.
    eapply red_red_ctx_inv' ; tea.
    constructor.
    1: eapply closed_red_ctx_refl ; fvs.
    now constructor.

  - inversion X3 ; subst.
    eapply X0 in X4 as [T'' []]; subst ; tea.
    eapply into_closed_red in X1 ; fvs.
    eapply into_closed_red in X5 ; fvs.
    eapply closed_red_confluence in X5 as [? [? rind']]; tea.
    eapply invert_red_mkApps_tInd in rind' as [? []]; subst.
    eapply closed_red_confluence in X1 as [? [rind' rind]].
    2: now etransitivity.
    eapply invert_red_mkApps_tInd in rind as [? []]; subst.
    eapply invert_red_mkApps_tInd in rind' as [args'' [e ]]; subst.
    eapply mkApps_notApp_inj in e as [e ->].
    2-3: easy.
    injection e as <- <-.
    exists args'' ; split ; auto.
    eapply All2_trans ; tea.
    eapply closed_red_trans.
Qed.

End BDUnique.

Theorem infering_unique `{checker_flags} {Σ} (wfΣ : wf Σ) {Γ} (wfΓ : wf_local Σ Γ) {t T T'} :
  Σ ;;; Γ |- t ▹ T -> Σ ;;; Γ |- t ▹ T' ->
  ∑ T'', Σ ;;; Γ ⊢ T ⇝ T'' × Σ ;;; Γ ⊢ T' ⇝ T''.
Proof.
  intros ty ty'.
  now eapply bidirectional_unique in ty'.
Qed.

Theorem infering_unique' `{checker_flags} {Σ} (wfΣ : wf Σ) {Γ} (wfΓ : wf_local Σ Γ) {t T T'} :
  Σ ;;; Γ |- t ▹ T -> Σ ;;; Γ |- t ▹ T' ->
  Σ ;;; Γ ⊢ T = T'.
Proof.
  intros ty ty'.
  eapply bidirectional_unique in ty as [? []]; tea.
  etransitivity.
  2: symmetry.
  all: now eapply red_ws_cumul_pb.
Qed.

Theorem infering_checking `{checker_flags} {Σ} (wfΣ : wf Σ) {Γ} (wfΓ : wf_local Σ Γ) {t T T'} :
  is_open_term Γ T' -> Σ ;;; Γ |- t ▹ T -> Σ ;;; Γ |- t ◃ T' -> Σ ;;; Γ ⊢ T ≤ T'.
Proof.
  intros ? ty ty'.
  depelim ty'.
  eapply infering_unique' in ty ; tea.
  etransitivity ; last first.
  - apply into_ws_cumul_pb ; tea.
    1: fvs.
    now eapply type_is_open_term, infering_typing.
  - now eapply ws_cumul_pb_eq_le.
Qed.

Theorem infering_sort_sort `{checker_flags} {Σ} (wfΣ : wf Σ) {Γ} (wfΓ : wf_local Σ Γ) {t u u'} :
  Σ ;;; Γ |- t ▹□ u -> Σ ;;; Γ |- t ▹□ u' -> u = u'.
Proof.
  intros ty ty'.
  now eapply bidirectional_unique in ty'.
Qed.

Theorem infering_sort_infering `{checker_flags} {Σ} (wfΣ : wf Σ)
  {Γ} {wfΓ : wf_local Σ Γ} {t u T} :
  Σ ;;; Γ |- t ▹□ u -> Σ ;;; Γ |- t ▹ T ->
  Σ ;;; Γ ⊢ T ⇝ tSort u.
Proof.
  intros ty ty'.
  depelim ty.
  eapply into_closed_red in r.
  2: fvs.
  2: now eapply type_is_open_term, infering_typing.
  eapply bidirectional_unique in i as [T'' []]; tea.
  eapply closed_red_confluence in r as [? [? ru]]; tea.
  eapply invert_red_sort in ru ; subst.
  now etransitivity.
Qed.

Theorem infering_prod_prod `{checker_flags} {Σ} (wfΣ : wf Σ)
  {Γ} (wfΓ : wf_local Σ Γ) {t na na' A A' B B'} :
  Σ ;;; Γ |- t ▹Π (na,A,B) -> Σ ;;; Γ |- t ▹Π (na',A',B') ->
  ∑ A'' B'',
  [× na = na', Σ ;;; Γ ⊢ A ⇝ A'', Σ ;;; Γ ⊢ A' ⇝ A'',
      Σ ;;; Γ,, vass na A ⊢ B ⇝ B'' & Σ ;;; Γ,, vass na A' ⊢ B' ⇝ B''].
Proof.
  intros ty ty'.
  now eapply bidirectional_unique in ty'.
Qed.

Theorem infering_prod_prod' `{checker_flags} {Σ} (wfΣ : wf Σ)
  {Γ} (wfΓ : wf_local Σ Γ) {t na na' A A' B B'} :
  Σ ;;; Γ |- t ▹Π (na,A,B) -> Σ ;;; Γ |- t ▹Π (na',A',B') ->
  [× na = na', Σ ;;; Γ ⊢ A = A' & Σ ;;; Γ,, vass na A ⊢ B = B'].
Proof.
  intros ty ty'.
  eapply infering_prod_prod in ty as (A''&B''&[]); tea.
  subst.
  assert (Σ ;;; Γ ⊢ A = A').
  {
    etransitivity.
    2: symmetry.
    all: now eapply red_ws_cumul_pb.
  }
  split ; auto.
  etransitivity.
  1: now eapply red_ws_cumul_pb.
  symmetry.
  eapply ws_cumul_pb_ws_cumul_ctx.
  2: now eapply red_ws_cumul_pb.
  constructor.
  1: eapply ws_cumul_ctx_pb_refl ; fvs.
  now constructor.
Qed.

Theorem infering_prod_infering `{checker_flags} {Σ} (wfΣ : wf Σ)
  {Γ} (wfΓ : wf_local Σ Γ) {t na A B T} :
  Σ ;;; Γ |- t ▹Π(na,A,B) ->
  Σ ;;; Γ |- t ▹ T ->
  ∑ A' B', [× Σ ;;; Γ ⊢ T ⇝ tProd na A' B',
    Σ ;;; Γ ⊢ A ⇝ A' &
    Σ ;;; Γ,, vass na A ⊢ B ⇝ B'].
Proof.
  intros ty ty'.
  depelim ty.
  eapply into_closed_red in r.
  2: fvs.
  2: now eapply type_is_open_term, infering_typing.
  eapply bidirectional_unique in i as [? []]; tea.
  eapply closed_red_confluence in r as [? [? rA']]; tea.
  eapply invert_red_prod in rA' as (A'&B'&[]); subst.
  exists A', B' ; split ; tea.
  now etransitivity.
Qed.

Theorem infering_ind_ind `{checker_flags} {Σ} (wfΣ : wf Σ)
  {Γ} (wfΓ : wf_local Σ Γ) {t ind ind' u u' args args'} :
  Σ ;;; Γ |- t ▹{ind} (u,args) -> Σ ;;; Γ |- t ▹{ind'} (u',args') ->
  ∑ args'',
    [× ind = ind', u = u',
      red_terms Σ Γ args args'' &
      red_terms Σ Γ args' args''].
Proof.
  intros ty ty'.
  now eapply bidirectional_unique in ty'.
Qed.

Theorem infering_ind_ind' `{checker_flags} {Σ} (wfΣ : wf Σ)
  {Γ} (wfΓ : wf_local Σ Γ) {t ind ind' u u' args args'} :
  Σ ;;; Γ |- t ▹{ind} (u,args) -> Σ ;;; Γ |- t ▹{ind'} (u',args') ->
    [× ind = ind', u = u' &
      ws_cumul_pb_terms Σ Γ args args'].
Proof.
  intros ty ty'.
  eapply bidirectional_unique in ty as [args'' []] ; tea.
  subst.
  split ; auto.
  etransitivity.
  2: symmetry.
  all: now eapply red_terms_ws_cumul_pb_terms.
Qed.

Theorem infering_ind_infering `{checker_flags} {Σ} (wfΣ : wf Σ)
  {Γ} (wfΓ : wf_local Σ Γ) {t ind u args T} :
  Σ ;;; Γ |- t ▹{ind} (u,args) ->
  Σ ;;; Γ |- t ▹ T ->
  ∑ args',
    Σ ;;; Γ ⊢ T ⇝ mkApps (tInd ind u) args' ×
      red_terms Σ Γ args args'.
Proof.
  intros ty ty'.
  depelim ty.
  eapply into_closed_red in r.
  2: fvs.
  2: now eapply type_is_open_term, infering_typing.
  eapply bidirectional_unique in i as [? []]; tea.
  eapply closed_red_confluence in r as [? [? rind]]; tea.
  eapply invert_red_mkApps_tInd in rind as [args' []]; subst.
  exists args' ; split ; tea.
  now etransitivity.
Qed.

Corollary principal_type `{checker_flags} {Σ} (wfΣ : wf Σ) {Γ t T} :
  Σ ;;; Γ |- t : T ->
  ∑ T',
    (forall T'', Σ ;;; Γ |- t : T'' -> Σ ;;; Γ ⊢ T' ≤ T'') × Σ ;;; Γ |- t : T'.
Proof.
  intros ty.
  assert (wf_local Σ Γ) by (pcuic; eapply typing_wf_local; eauto).
  apply typing_infering in ty as (S & infS & _); auto.
  exists S.
  repeat split.
  2: by apply infering_typing.
  intros T' ty.
  eapply typing_infering in ty as (S' & infS' & cum'); auto.
  etransitivity ; eauto.
  now eapply ws_cumul_pb_eq_le, infering_unique'.
Qed.








