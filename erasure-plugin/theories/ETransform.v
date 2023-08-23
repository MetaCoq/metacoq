(* Distributed under the terms of the MIT license. *)
From Coq Require Import Program ssreflect ssrbool.
From Equations Require Import Equations.
From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import Environment Transform config BasicAst uGraph.
From MetaCoq.Template Require Pretty Typing WcbvEval EtaExpand.
Set Warnings "-notation-overridden".
From MetaCoq.PCUIC Require PCUICAst PCUICAstUtils PCUICProgram PCUICWeakeningEnvSN.
Set Warnings "+notation-overridden".
From MetaCoq.SafeChecker Require Import PCUICErrors PCUICWfEnv PCUICWfEnvImpl.
From MetaCoq.Erasure Require EAstUtils ErasureFunction ErasureCorrectness Extract
   EOptimizePropDiscr ERemoveParams EProgram.
From MetaCoq.TemplatePCUIC Require Import PCUICTransform.

Import PCUICAst (term) PCUICProgram PCUICTransform (eval_pcuic_program) Extract EProgram
    EAst Transform ERemoveParams.
Import EEnvMap EGlobalEnv EWellformed.

Definition build_wf_env_from_env {cf : checker_flags} (Σ : global_env_map) (wfΣ : ∥ PCUICTyping.wf Σ ∥) : wf_env :=
  {| wf_env_reference := {| reference_impl_env := Σ.(trans_env_env); reference_impl_wf := wfΣ |} ;
     wf_env_map := Σ.(trans_env_map);
     wf_env_map_repr := Σ.(trans_env_repr);
 |}.


Notation NormalizationIn_erase_pcuic_program_1 p
  := (@PCUICTyping.wf_ext config.extraction_checker_flags p.1 -> PCUICSN.NormalizationIn (cf:=config.extraction_checker_flags) (no:=PCUICSN.extraction_normalizing) p.1)
       (only parsing).

Notation NormalizationIn_erase_pcuic_program_2 p
  := (@PCUICTyping.wf_ext config.extraction_checker_flags p.1 -> PCUICWeakeningEnvSN.normalizationInAdjustUniversesIn (cf:=config.extraction_checker_flags) (no:=PCUICSN.extraction_normalizing) p.1)
       (only parsing).

(* TODO: Where should this go? *)
#[local]
Lemma reference_impl_env_iter_pop_eq'
  (cf := config.extraction_checker_flags)
  (no := PCUICSN.extraction_normalizing)
  {guard : abstract_guard_impl}
  (wfe : wf_env)
  (n : nat)
  (X' := ErasureFunction.iter abstract_pop_decls (S n) wfe)
  (wfe' := ErasureFunction.iter reference_pop (S n) (reference_impl_env wfe))
  : reference_impl_env X' = wfe'.
Proof.
  subst X' wfe'.
  revert wfe; cbn; induction n as [|n IHn]; cbn; intros;
    [ | rewrite IHn ].
  all: destruct wfe as [[[? [|[]]]]]; cbv [optim_pop]; cbn; reflexivity.
Qed.

#[local]
Lemma reference_impl_env_iter_pop_eq
  (cf := config.extraction_checker_flags)
  (no := PCUICSN.extraction_normalizing)
  {guard : abstract_guard_impl}
  (wfe : wf_env)
  (n : nat)
  (X' := ErasureFunction.iter abstract_pop_decls (S n) wfe)
  : reference_impl_env X'
    = {| PCUICAst.PCUICEnvironment.universes := PCUICAst.PCUICEnvironment.universes (reference_impl_env wfe)
      ; PCUICAst.PCUICEnvironment.declarations := skipn (S n) (PCUICAst.PCUICEnvironment.declarations (reference_impl_env wfe))
      ; PCUICAst.PCUICEnvironment.retroknowledge := PCUICAst.PCUICEnvironment.retroknowledge (reference_impl_env wfe) |}.
Proof.
  subst X'.
  revert wfe; cbn; induction n as [|n IHn]; cbn; intros;
    [ | rewrite IHn ].
  all: destruct wfe as [[[? [|[]]]]]; cbv [optim_pop]; cbn; reflexivity.
Qed.

#[local] Lemma erase_pcuic_program_normalization_helper
  (cf := config.extraction_checker_flags) (no := PCUICSN.extraction_normalizing)
  {guard : abstract_guard_impl} (p : pcuic_program)
  {normalization_in : NormalizationIn_erase_pcuic_program_1 p}
  {normalization_in_adjust_universes : NormalizationIn_erase_pcuic_program_2 p}
  (wfΣ : ∥ PCUICTyping.wf_ext (H := config.extraction_checker_flags) p.1 ∥)
  : (let wfe := build_wf_env_from_env p.1.1 (map_squash (PCUICTyping.wf_ext_wf _) (wfΣ : ∥ PCUICTyping.wf_ext (H := config.extraction_checker_flags) p.1 ∥)) in
     forall n : nat,
       n < #|PCUICAst.PCUICEnvironment.declarations p.1|
      -> forall kn cb pf,
        hd_error (skipn n (PCUICAst.PCUICEnvironment.declarations p.1)) =
          Some (kn, PCUICAst.PCUICEnvironment.ConstantDecl cb) ->
        forall Σ : PCUICAst.PCUICEnvironment.global_env_ext,
          PCUICTyping.wf_ext Σ ->
          Σ
            ∼_ext @abstract_make_wf_env_ext extraction_checker_flags
            (@optimized_abstract_env_impl extraction_checker_flags _) wfe
            (PCUICAst.PCUICEnvironment.cst_universes cb) pf -> PCUICSN.NormalizationIn Σ)
    /\
      (let wfe := build_wf_env_from_env p.1.1 (map_squash (PCUICTyping.wf_ext_wf _) (wfΣ : ∥ PCUICTyping.wf_ext (H := config.extraction_checker_flags) p.1 ∥)) in
       forall n : nat,
         n < #|PCUICAst.PCUICEnvironment.declarations p.1|
        -> let X' :=
             ErasureFunction.iter abstract_pop_decls (S n) wfe in
           forall kn cb pf,
             hd_error (skipn n (PCUICAst.PCUICEnvironment.declarations p.1)) =
               Some (kn, PCUICAst.PCUICEnvironment.ConstantDecl cb) ->
             let Xext :=
               @abstract_make_wf_env_ext extraction_checker_flags
                 (@optimized_abstract_env_impl extraction_checker_flags _) X'
                 (PCUICAst.PCUICEnvironment.cst_universes cb) pf in
             forall Σ : PCUICAst.PCUICEnvironment.global_env_ext,
               PCUICTyping.wf_ext Σ -> Σ ∼_ext Xext -> PCUICSN.NormalizationIn Σ).
Proof.
  match goal with |- ?A /\ ?B => cut (A /\ (A -> B)); [ tauto | ] end.
  cbv beta zeta; split.
  all: cbn; intros; subst;
    repeat match goal with
      | [ H : forall x, x = _ -> _ |- _ ] => specialize (H _ eq_refl)
      | [ H : squash _ |- _ ] => destruct H
      | [ H : ?A -> ?B, H' : ?A |- _ ] => specialize (H H')
      end.
  { destruct p as [Σ ?]; cbn in *.
    match goal with H : PCUICSN.NormalizationIn _ |- _ => revert H end.
    eapply normalization_in_adjust_universes; try assumption.
    cbv [PCUICSN.NormalizationIn]; cbn.
    let H := match goal with H : PCUICTyping.wf_ext _ |- _ => H end in
    rewrite /PCUICAst.PCUICEnvironment.lookup_env -PCUICAst.PCUICEnvironment.lookup_global_Some_iff_In_NoDup -?hd_error_skipn_iff_In;
    [ eapply PCUICAst.NoDup_on_global_decls, H
    | eexists; eassumption ]. }
  { destruct p as [Σ ?]; cbn in *.
    match goal with H : PCUICSN.NormalizationIn _ |- _ => revert H end.
    move => normalization_in.
    rewrite reference_impl_env_iter_pop_eq.
    repeat match goal with H : _ |- _ => rewrite reference_impl_env_iter_pop_eq in H end.
    eapply normalization_in_adjust_universes in normalization_in; eauto; revgoals.
    { repeat match goal with H : PCUICTyping.wf_ext _ |- _ => destruct H end;
        split; eassumption. }
    { let H := multimatch goal with H : PCUICTyping.wf_ext _ |- _ => H end in
      rewrite /PCUICAst.PCUICEnvironment.lookup_env -PCUICAst.PCUICEnvironment.lookup_global_Some_iff_In_NoDup -?hd_error_skipn_iff_In;
      [ eapply PCUICAst.NoDup_on_global_decls, H
      | eexists; eassumption ]. }
    revert normalization_in.
    apply PCUICWeakeningEnvSN.weakening_env_normalization_in; eauto;
      try match goal with H : PCUICTyping.wf_ext _ |- _ => refine (@PCUICTyping.wf_ext_wf _ _ H) end.
    apply PCUICAst.PCUICEnvironment.extends_decls_extends, PCUICAst.PCUICEnvironment.strictly_extends_decls_extends_decls; split; cbn; try reflexivity.
    eauto using firstn_skipn. }
Qed.

Program Definition erase_pcuic_program {guard : abstract_guard_impl} (p : pcuic_program)
  {normalization_in : NormalizationIn_erase_pcuic_program_1 p}
  {normalization_in_adjust_universes : NormalizationIn_erase_pcuic_program_2 p}
  (wfΣ : ∥ PCUICTyping.wf_ext (H := config.extraction_checker_flags) p.1 ∥)
  (wt : ∥ ∑ T, PCUICTyping.typing (H := config.extraction_checker_flags) p.1 [] p.2 T ∥) : eprogram_env :=
  let wfe := build_wf_env_from_env p.1.1 (map_squash (PCUICTyping.wf_ext_wf _) wfΣ) in
  let wfext := @abstract_make_wf_env_ext _ optimized_abstract_env_impl wfe p.1.2 _ in
  let t := ErasureFunction.erase (normalization_in:=_) optimized_abstract_env_impl wfext nil p.2
    (fun Σ wfΣ => let '(sq (T; ty)) := wt in PCUICTyping.iswelltyped ty) in
  let Σ' := ErasureFunction.erase_global_fast (normalization_in:=_) optimized_abstract_env_impl
    (EAstUtils.term_global_deps t) wfe (p.1.(PCUICAst.PCUICEnvironment.declarations)) _ in
    (EEnvMap.GlobalContextMap.make Σ' _, t).

Next Obligation. unshelve edestruct erase_pcuic_program_normalization_helper; cbn in *; eauto. Qed.
Next Obligation.
  eapply wf_glob_fresh.
  eapply ErasureFunction.erase_global_fast_wf_glob.
  unshelve edestruct erase_pcuic_program_normalization_helper; cbn in *; eauto.
Qed.

Obligation Tactic := idtac.

Import Extract.

Definition erase_program {guard : abstract_guard_impl} (p : pcuic_program)
  {normalization_in normalization_in_adjust_universes}
  (wtp : ∥ wt_pcuic_program (cf:=config.extraction_checker_flags) p ∥)
  : eprogram_env :=
  @erase_pcuic_program guard p normalization_in normalization_in_adjust_universes (map_squash fst wtp) (map_squash snd wtp).

Lemma expanded_erase_program {guard : abstract_guard_impl} p {normalization_in normalization_in_adjust_universes} (wtp : ∥ wt_pcuic_program p ∥) :
  PCUICEtaExpand.expanded_pcuic_program p ->
  EEtaExpandedFix.expanded_eprogram_env (@erase_program guard p normalization_in normalization_in_adjust_universes wtp).
Proof.
  intros [etaenv etat]. split;
  unfold erase_program, erase_pcuic_program.
  eapply ErasureFunction.expanded_erase_global_fast, etaenv; try reflexivity; eauto.
  unshelve edestruct erase_pcuic_program_normalization_helper; cbn in *; eauto.
  apply: (ErasureFunction.expanded_erase_fast (X_type:=optimized_abstract_env_impl)).
  unshelve edestruct erase_pcuic_program_normalization_helper; cbn in *; eauto.
  reflexivity. exact etat.
Qed.

Lemma expanded_eprogram_env_expanded_eprogram_cstrs p :
  EEtaExpandedFix.expanded_eprogram_env p ->
  EEtaExpanded.expanded_eprogram_env_cstrs p.
Proof.
  move=> [] etaenv etat.
  apply /andP.
  split.
  - eapply EEtaExpanded.isEtaExpFix_env_isEtaExp_env. now eapply EEtaExpandedFix.expanded_global_env_isEtaExp_env.
  - eapply EEtaExpanded.isEtaExpFix_isEtaExp. now eapply EEtaExpandedFix.expanded_isEtaExp.
Qed.

Obligation Tactic := try solve [ eauto ].

Program Definition erase_transform {guard : abstract_guard_impl} : Transform.t pcuic_program eprogram_env PCUICAst.term EAst.term
  eval_pcuic_program (eval_eprogram_env EWcbvEval.default_wcbv_flags) :=
 {| name := "erasure";
    pre p :=
     ∥ wt_pcuic_program (cf := config.extraction_checker_flags) p ∥
     /\ PCUICEtaExpand.expanded_pcuic_program p
     /\ NormalizationIn_erase_pcuic_program_1 p
     /\ NormalizationIn_erase_pcuic_program_2 p ;
   transform p hp := let nhs := proj2 (proj2 hp) in
                     @erase_program guard p (proj1 nhs) (proj2 nhs) (proj1 hp) ;
    post p := [/\ wf_eprogram_env all_env_flags p & EEtaExpandedFix.expanded_eprogram_env p];
   obseq p hp p' v v' := let Σ := p.1 in Σ ;;; [] |- v ⇝ℇ v' |}.

Next Obligation.
  cbn -[erase_program].
  intros ? p (wtp&etap&?&?).
  destruct erase_program eqn:e.
  split.
  - unfold erase_program, erase_pcuic_program in e.
    set (egf := ErasureFunction.erase_global_fast _ _ _ _ _) in e.
    set (ef := ErasureFunction.erase _ _ _ _ _) in e.
    cbn -[egf ef] in e. injection e. intros <- <-.
    split.
    eapply ErasureFunction.erase_global_fast_wf_glob; eauto;
      try match goal with H : _ |- _ => eapply H end.
    unshelve edestruct erase_pcuic_program_normalization_helper; cbn in *; eauto.
    apply: (ErasureFunction.erase_wellformed_fast (X_type:=optimized_abstract_env_impl)); eauto;
      try match goal with H : _ |- _ => eapply H end.
    unshelve edestruct erase_pcuic_program_normalization_helper; cbn in *; eauto.
  - rewrite -e. cbn.
    now eapply expanded_erase_program.
Qed.

Next Obligation.
  red. move=> guard p v [[wf [T [HT1 HT2]]]]. unfold eval_pcuic_program, eval_eprogram.
  unshelve edestruct erase_pcuic_program_normalization_helper; cbn in *; try now destruct wf; eauto.
  destruct p as [Σ t].
  intros [ev].
  destruct erase_program eqn:e.
  unfold erase_program, erase_pcuic_program in e. simpl in e. injection e; intros <- <-.
  simpl. clear e. cbn in *.
  destruct wf; cbn in *.
  set (Σ' := build_wf_env_from_env _ _).
  assert (ev' :forall Σ0 : PCUICAst.PCUICEnvironment.global_env, Σ0 = Σ' -> PCUICWcbvEval.eval Σ0 t v).
  { intros; now subst. }
  eapply (ErasureFunction.erase_correct optimized_abstract_env_impl Σ' Σ.2 _ _ _ _ _ (EAstUtils.term_global_deps _)) in ev'.
  4:{ erewrite <- ErasureFunction.erase_global_deps_fast_spec. reflexivity. }
  all:trea.
  2:eapply Kernames.KernameSet.subset_spec; reflexivity.
  destruct ev' as [v' [he [hev]]]. exists v'; split => //.
  red. cbn.
  sq. exact hev. Unshelve.
  { intros; cbn in *.
    subst Σ'.
    multimatch goal with
    | [ H : _ |- _ ] => eapply H
    end; try eassumption;
    rewrite reference_impl_env_iter_pop_eq;
    repeat match goal with H : _ |- _ => rewrite reference_impl_env_iter_pop_eq in H end;
    assumption. }
  cbn; intros. sq. now subst.
Qed.

Definition extends_eprogram (p p' : eprogram) :=
  extends p.1 p'.1 /\ p.2 = p'.2.

Definition extends_eprogram_env (p p' : eprogram_env) :=
  extends p.1 p'.1 /\ p.2 = p'.2.

Section PCUICEnv. (* Locally reuse the short names for PCUIC environment handling *)
Import PCUICAst.PCUICEnvironment.

Lemma build_wf_env_from_env_eq {cf : checker_flags} (guard : abstract_guard_impl) (Σ : global_env_ext_map) (wfΣ : ∥ PCUICTyping.wf_ext Σ ∥) :
  let wfe := build_wf_env_from_env Σ (map_squash (PCUICTyping.wf_ext_wf Σ) wfΣ) in
  forall Σ' : global_env, Σ' ∼ wfe -> declarations Σ' = declarations Σ.
Proof.
  cbn; intros. rewrite H. reflexivity.
Qed.

Definition extends_global_env (Σ Σ' : global_env_ext_map) :=
  [/\ (forall kn decl, lookup_env Σ kn = Some decl ->lookup_env Σ' kn = Some decl),
      Σ.(universes) = Σ'.(universes), Σ.2 = Σ'.2 & Σ.(retroknowledge) = Σ'.(retroknowledge)].

Definition extends_pcuic_program (p p' : pcuic_program) :=
  extends_global_env p.1 p'.1 /\ p.2 = p'.2.
Import ErasureFunction.
Import PCUICAst.
Lemma fresh_global_app kn Σ Σ' : fresh_global kn (Σ ++ Σ') ->
  fresh_global kn Σ /\ fresh_global kn Σ'.
Proof.
  induction Σ; cbn; intuition auto.
  - constructor.
  - depelim H. constructor => //.
    now eapply Forall_app in H0.
  - depelim H.
    now eapply Forall_app in H0.
Qed.

Lemma lookup_global_app_wf Σ Σ' kn : EnvMap.EnvMap.fresh_globals (Σ ++ Σ') ->
  forall decl, lookup_global Σ' kn = Some decl -> lookup_global (Σ ++ Σ') kn = Some decl.
Proof.
  induction Σ in kn |- *; cbn; auto.
  intros fr; depelim fr.
  intros decl hd; cbn.
  destruct (eqb_spec kn kn0).
  eapply PCUICWeakeningEnv.lookup_global_Some_fresh in hd.
  subst. now eapply fresh_global_app in H as [H H'].
  now eapply IHΣ.
Qed.

Lemma strictly_extends_lookups {cf:checker_flags} (X X' : wf_env) (Σ Σ' : global_env) :
  (forall (kn : kername) (decl decl' : global_decl), lookup_env Σ' kn = Some decl -> lookup_env Σ kn = Some decl' -> decl = decl') ->
  retroknowledge Σ = retroknowledge Σ' ->
  strictly_extends_decls X Σ -> strictly_extends_decls X' Σ' ->
  PCUICTyping.wf Σ -> PCUICTyping.wf Σ' ->
  equiv_env_inter X' X.
Proof.
  intros hl hr [] [] wf wf'.
  split.
  - intros kn d.
    unfold lookup_env in *.
    destruct s as [? eq], s0 as [? eq'].
    rewrite eq' eq in hl.
    intros decl' hl' hl''.
    specialize (hl kn d decl').
    eapply wf_fresh_globals in wf.
    eapply wf_fresh_globals in wf'.
    rewrite eq in wf; rewrite eq' in wf'.
    eapply lookup_global_app_wf in hl'; tea.
    eapply lookup_global_app_wf in hl''; tea.
    eauto.
  - rewrite /primitive_constant. now rewrite e0 e2 hr.
Qed.

#[global]
Instance erase_transform_extends {guard : abstract_guard_impl} :
  TransformExt.t (erase_transform (guard := guard)) extends_pcuic_program extends_eprogram_env.
Proof.
  red. intros p p' pr pr' [ext eq]. rewrite /transform /=.
  destruct pr.
  epose proof (erase_pcuic_program_normalization_helper p (map_squash fst s)).
  destruct p as [Σ t]. destruct p' as [Σ' t'].
  simpl in *. subst t'. red. split.
  - destruct ext. red.
    cbn. rewrite /ErasureFunction.erase_global_fast.
    unshelve erewrite ErasureFunction.erase_global_deps_fast_spec.
    { intros. intuition auto. eapply H11; tea. admit. admit. }
    { intros. red in H4. cbn in H4. subst. reflexivity. }
    destruct Σ'. cbn in *. subst u.
    set (fst := ErasureFunction.erase _ _ _ _ _).
    set (snd:= ErasureFunction.erase _ _ _ _ _).
    assert (fst = snd).
    { subst fst snd. symmetry.
      eapply ErasureFunction.erase_irrel_global_env.
      eapply ErasureFunction.equiv_env_inter_hlookup.
      intros ? ? -> ->. cbn.
      eapply ErasureFunction.equiv_env_inter_sym.
      eapply ErasureFunction.extends_global_env_equiv_env.
      cbn. split => //.
      sq. unfold primitive_constant. now rewrite H3. }
    clearbody fst snd. subst snd.
    intros.
    set (X := build_wf_env_from_env g _) in *.
    destruct (lookup_env Σ kn) eqn:E.
    unshelve epose proof (abstract_env_exists X). 3:tc. tc.
    destruct H4 as [[Σ' ΣX]].
    unshelve epose proof (build_wf_env_from_env_eq _ (g, Σ.2) _ _ ΣX). cbn in H4.
    epose proof (hl := ErasureFunction.lookup_env_erase_decl (optimized_abstract_env_impl) _ (EAstUtils.term_global_deps fst) _ _ _ kn g0 _ ΣX).
    unfold lookup_env in E, hl. rewrite H4 in hl. specialize (hl (H0 _ _ E)).
    forward hl. admit.
    destruct g0.
    + destruct hl as [X' [nin [pf [eq ext]]]].
      unshelve erewrite ErasureFunction.erase_global_deps_fast_spec. shelve.
      { intros. red in H5. cbn in H5. subst. reflexivity. }
      erewrite eq.
      set (Xs := build_wf_env_from_env Σ.1 _) in *.
      unshelve epose proof (abstract_env_exists Xs). 3:tc. tc.
      destruct H5 as [[Σs Hs]].
      epose proof (hl' := ErasureFunction.lookup_env_erase_decl (optimized_abstract_env_impl) _ (EAstUtils.term_global_deps fst) _ _ _ kn _ _ Hs).
      unshelve epose proof (build_wf_env_from_env_eq _ _ _ _ Hs). rewrite /lookup_env H5 in hl'. specialize (hl' E).
      forward hl'. admit. cbn in hl'.
      destruct hl' as [X'' [nin' [pf' [eq' ext']]]].
      erewrite eq' in H2. rewrite -H2. f_equal. f_equal.
      f_equal. unfold erase_constant_decl.
      eapply erase_constant_body_irrel.
      eapply ErasureFunction.equiv_env_inter_hlookup. cbn.
      intros ? ? H6 H7.
      cbn in ext. specialize (ext _ _ eq_refl eq_refl) as [ext].
      specialize (ext' _ _ eq_refl eq_refl) as [ext'].
      cbn in H6, H7. subst Σ0 Σ'0. cbn. split => //.
      { intros kn' decl'. rewrite /lookup_env.
        destruct (map_squash Datatypes.fst s).
        destruct pr' as [pr' ?].
        destruct (map_squash Datatypes.fst pr').
        eapply strictly_extends_lookups. 2-3:tea.
        intros kn'' ? ? hg hΣ. eapply H0 in hΣ. congruence. auto.
        apply X0. apply X1. }
      { rewrite /primitive_constant.
        destruct ext as [_ _ ->].
        destruct ext' as [_ _ ->].
        now rewrite H3. }
    +
  - symmetry.
    eapply ErasureFunction.erase_irrel_global_env.
    intros Σg Σg' eq eq'.
    destruct ext as [hl hu hr].
    destruct Σ as [m univs]. destruct Σ' as [m' univs']. simpl in *.
    subst. cbn. destruct m, m'. cbn in *. split => //. sq. red. split => //.
    unfold primitive_constant. now rewrite H.
Qed.
End PCUICEnv.

Obligation Tactic := idtac.

(** This transformation is the identity on terms but changes the evaluation relation to one
    where fixpoints are not guarded. It requires eta-expanded fixpoints and evaluation
    to use the guarded fixpoint rule as a precondition. *)

Import EWcbvEval (WcbvFlags, with_prop_case, with_guarded_fix).

Program Definition guarded_to_unguarded_fix {fl : EWcbvEval.WcbvFlags} {wcon : EWcbvEval.with_constructor_as_block = false} {efl : EEnvFlags} (wguard : with_guarded_fix) :
  Transform.t eprogram_env eprogram_env EAst.term EAst.term
    (eval_eprogram_env fl) (eval_eprogram_env (EWcbvEval.switch_unguarded_fix fl)) :=
  {| name := "switching to unguarded fixpoints";
    transform p pre := p;
    pre p := wf_eprogram_env efl p /\ EEtaExpandedFix.expanded_eprogram_env p;
    post p := wf_eprogram_env efl p /\ EEtaExpandedFix.expanded_eprogram_env p;
    obseq p hp p' v v' := v' = v |}.
Next Obligation. cbn. eauto. Qed.
Next Obligation.
  cbn.
  move=> fl wcon efl wguard [Σ t] v [wfp [etae etat]]. cbn in *.
  intros [ev]. exists v. split => //.
  red. sq. cbn in *.
  unshelve eapply EEtaExpandedFix.eval_opt_to_target => //. auto. 2:apply wfp.
  now eapply EEtaExpandedFix.expanded_global_env_isEtaExp_env.
  now eapply EEtaExpandedFix.expanded_isEtaExp.
Qed.

#[global]
Instance guarded_to_unguarded_fix_extends {fl : EWcbvEval.WcbvFlags} {wcon : EWcbvEval.with_constructor_as_block = false} {efl : EEnvFlags} (wguard : with_guarded_fix) :
  TransformExt.t (guarded_to_unguarded_fix (wcon:=wcon) wguard) extends_eprogram_env term snd.
Proof.
  red. intros p p' pr pr' [ext eq]. now rewrite /transform /=.
Qed.

Definition rebuild_wf_env {efl} (p : eprogram) (hwf : wf_eprogram efl p): eprogram_env :=
  (GlobalContextMap.make p.1 (wf_glob_fresh p.1 (proj1 hwf)), p.2).

Program Definition rebuild_wf_env_transform {fl : EWcbvEval.WcbvFlags} {efl} (with_exp : bool) :
  Transform.t eprogram eprogram_env EAst.term EAst.term (eval_eprogram fl) (eval_eprogram_env fl) :=
  {| name := "rebuilding environment lookup table";
     pre p := wf_eprogram efl p /\ (with_exp ==> EEtaExpanded.expanded_eprogram_cstrs p);
     transform p pre := rebuild_wf_env p (proj1 pre);
     post p := wf_eprogram_env efl p /\ (with_exp ==> EEtaExpanded.expanded_eprogram_env_cstrs p);
     obseq p hp p' v v' := v = v' |}.
Next Obligation.
  cbn. intros fl efl [] input [wf exp]; cbn; split => //.
Qed.
Next Obligation.
  cbn. intros fl efl [] input v [] ev p'; exists v; split => //.
Qed.

#[global]
Instance rebuild_wf_env_extends {fl : EWcbvEval.WcbvFlags} {efl : EEnvFlags} with_exp :
  TransformExt.t (rebuild_wf_env_transform with_exp) extends_eprogram term snd.
Proof.
  red. intros p p' pr pr' [ext eq]. now rewrite /transform /=.
Qed.

Program Definition remove_params_optimization {fl : EWcbvEval.WcbvFlags} {wcon : EWcbvEval.with_constructor_as_block = false}
  (efl := all_env_flags):
  Transform.t eprogram_env eprogram EAst.term EAst.term (eval_eprogram_env fl) (eval_eprogram fl) :=
  {| name := "stripping constructor parameters";
    transform p pre := ERemoveParams.strip_program p;
    pre p := wf_eprogram_env efl p /\ EEtaExpanded.expanded_eprogram_env_cstrs p;
    post p := wf_eprogram (switch_no_params efl) p /\ EEtaExpanded.expanded_eprogram_cstrs p;
    obseq p hp p' v v' := v' = (ERemoveParams.strip p.1 v) |}.
Next Obligation.
  move=> fl wcon efl [Σ t] [wfp etap].
  simpl.
  cbn -[ERemoveParams.strip] in *.
  split. now eapply ERemoveParams.strip_program_wf.
  now eapply ERemoveParams.strip_program_expanded.
Qed.

Next Obligation.
  red. move=> ? wcon [Σ t] /= v [[wfe wft] etap] [ev].
  unshelve eapply ERemoveParams.strip_eval in ev; eauto.
  eexists; split => /= //. now sq. cbn in *.
  now move/andP: etap.
  now eapply wellformed_closed_env.
  now eapply wellformed_closed.
  now move/andP: etap.
Qed.

#[global]
Instance remove_params_extends {fl : EWcbvEval.WcbvFlags}  {wcon : EWcbvEval.with_constructor_as_block = false}
  (efl := all_env_flags):
  TransformExt.t (remove_params_optimization (wcon:=wcon)) extends_eprogram_env term snd.
Proof.
  red. intros p p' pr pr' [ext eq]. rewrite /transform /=. rewrite eq.
  eapply strip_extends => //. apply pr'. rewrite -eq. apply pr.
Qed.

Program Definition remove_params_fast_optimization {fl : EWcbvEval.WcbvFlags} {wcon : EWcbvEval.with_constructor_as_block = false}
  (efl := all_env_flags) :
  Transform.t eprogram_env eprogram EAst.term EAst.term (eval_eprogram_env fl) (eval_eprogram fl) :=
  {| name := "stripping constructor parameters (faster?)";
    transform p _ := (ERemoveParams.Fast.strip_env p.1, ERemoveParams.Fast.strip p.1 [] p.2);
    pre p := wf_eprogram_env efl p /\ EEtaExpanded.expanded_eprogram_env_cstrs p;
    post p := wf_eprogram (switch_no_params efl) p /\ EEtaExpanded.expanded_eprogram_cstrs p;
    obseq p hp p' v v' := v' = (ERemoveParams.strip p.1 v) |}.
Next Obligation.
  move=> fl wcon efl [Σ t] [wfp etap].
  simpl.
  cbn -[ERemoveParams.strip] in *.
  rewrite -ERemoveParams.Fast.strip_fast -ERemoveParams.Fast.strip_env_fast.
  split.
  now eapply (ERemoveParams.strip_program_wf (Σ, t)).
  now eapply (ERemoveParams.strip_program_expanded (Σ, t)).
Qed.

Next Obligation.
  red. move=> ? wcon [Σ t] /= v [[wfe wft] etap] [ev].
  rewrite -ERemoveParams.Fast.strip_fast -ERemoveParams.Fast.strip_env_fast.
  unshelve eapply ERemoveParams.strip_eval in ev; eauto.
  eexists; split => /= //.
  now sq. cbn in *.
  now move/andP: etap.
  now eapply wellformed_closed_env.
  now eapply wellformed_closed.
  now move/andP: etap.
Qed.

#[global]
Instance remove_params_fast_extends {fl : EWcbvEval.WcbvFlags}  {wcon : EWcbvEval.with_constructor_as_block = false}
  (efl := all_env_flags):
  TransformExt.t (remove_params_fast_optimization (wcon:=wcon)) extends_eprogram_env term snd.
Proof.
  red. intros p p' pr pr' [ext eq]. rewrite /transform /=. rewrite eq.
  rewrite -!ERemoveParams.Fast.strip_fast.
  eapply strip_extends => //. apply pr'. rewrite -eq. apply pr.
Qed.

Import EOptimizePropDiscr EWcbvEval.

Program Definition remove_match_on_box_trans {fl : WcbvFlags} {wcon : with_constructor_as_block = false} {efl : EEnvFlags} {hastrel : has_tRel} {hastbox : has_tBox} :
  Transform.t eprogram_env eprogram EAst.term EAst.term (eval_eprogram_env fl) (eval_eprogram (disable_prop_cases fl)) :=
  {| name := "optimize_prop_discr";
    transform p _ := remove_match_on_box_program p ;
    pre p := wf_eprogram_env efl p /\ EEtaExpanded.expanded_eprogram_env_cstrs p;
    post p := wf_eprogram efl p /\ EEtaExpanded.expanded_eprogram_cstrs p;
    obseq p hp p' v v' := v' = EOptimizePropDiscr.remove_match_on_box p.1 v |}.

Next Obligation.
  move=> fl wcon efl hastrel hastbox [Σ t] [wfp etap].
  cbn in *. split.
  - now eapply remove_match_on_box_program_wf.
  - now eapply remove_match_on_box_program_expanded.
Qed.
Next Obligation.
  red. move=> fl wcon efl hastrel hastbox [Σ t] /= v [wfe wft] [ev].
  eapply EOptimizePropDiscr.remove_match_on_box_correct in ev; eauto.
  eexists; split => //. red. sq; auto. cbn. apply wfe.
  eapply wellformed_closed_env, wfe.
  eapply wellformed_closed, wfe.
  Unshelve. eauto.
Qed.

#[global]
Instance remove_match_on_box_extends  {fl : WcbvFlags} {wcon : with_constructor_as_block = false} {efl : EEnvFlags} {hastrel : has_tRel} {hastbox : has_tBox} :
  TransformExt.t (remove_match_on_box_trans (wcon:=wcon) (hastrel := hastrel) (hastbox := hastbox)) extends_eprogram_env term snd.
Proof.
  red. intros p p' pr pr' [ext eq]. rewrite /transform /=. rewrite -eq.
  eapply wellformed_remove_match_on_box_extends; eauto. apply pr. apply pr'.
Qed.

From MetaCoq.Erasure Require Import EInlineProjections.

Program Definition inline_projections_optimization {fl : WcbvFlags} {wcon : EWcbvEval.with_constructor_as_block = false} (efl := switch_no_params all_env_flags)
  {hastrel : has_tRel} {hastbox : has_tBox} :
  Transform.t eprogram_env eprogram EAst.term EAst.term (eval_eprogram_env fl) (eval_eprogram fl) :=
  {| name := "primitive projection inlining";
    transform p _ := EInlineProjections.optimize_program p ;
    pre p := wf_eprogram_env efl p /\ EEtaExpanded.expanded_eprogram_env_cstrs p;
    post p := wf_eprogram (disable_projections_env_flag efl) p /\ EEtaExpanded.expanded_eprogram_cstrs p;
    obseq p hp p' v v' := v' = EInlineProjections.optimize p.1 v |}.

Next Obligation.
  move=> fl wcon efl hastrel hastbox [Σ t] [wfp etap].
  cbn in *. split.
  - now eapply optimize_program_wf.
  - now eapply optimize_program_expanded.
Qed.
Next Obligation.
  red. move=> fl wcon hastrel hastbox [Σ t] /= v [wfe wft] [ev].
  eapply EInlineProjections.optimize_correct in ev; eauto.
  eexists; split => //. red. sq; auto. cbn. apply wfe.
  cbn. eapply wfe. Unshelve. auto.
Qed.

#[global]
Instance inline_projections_optimization_extends {fl : WcbvFlags} {wcon : EWcbvEval.with_constructor_as_block = false} (efl := switch_no_params all_env_flags)
  {hastrel : has_tRel} {hastbox : has_tBox} :
  TransformExt.t (inline_projections_optimization (wcon:=wcon) (hastrel := hastrel) (hastbox := hastbox)) extends_eprogram_env term snd.
Proof.
  red. intros p p' pr pr' [ext eq]. rewrite /transform /=. rewrite -eq.
  eapply wellformed_optimize_extends; eauto. apply pr. apply pr'.
Qed.

From MetaCoq.Erasure Require Import EConstructorsAsBlocks.

Program Definition constructors_as_blocks_transformation {efl : EEnvFlags}
  {has_app : has_tApp} {has_rel : has_tRel} {hasbox : has_tBox} {has_pars : has_cstr_params = false} {has_cstrblocks : cstr_as_blocks = false} :
  Transform.t eprogram_env eprogram EAst.term EAst.term (eval_eprogram_env target_wcbv_flags) (eval_eprogram block_wcbv_flags) :=
  {| name := "transforming to constuctors as blocks";
    transform p _ := EConstructorsAsBlocks.transform_blocks_program p ;
    pre p := wf_eprogram_env efl p /\ EEtaExpanded.expanded_eprogram_env_cstrs p;
    post p := wf_eprogram (switch_cstr_as_blocks efl) p ;
    obseq p hp p' v v' := v' = EConstructorsAsBlocks.transform_blocks p.1 v |}.

Next Obligation.
  move=> efl hasapp hasrel hasbox haspars hascstrs [Σ t] [] [wftp wft] /andP [etap etat].
  cbn in *. split.
  - eapply transform_wf_global; eauto.
  - eapply transform_wellformed; eauto.
Qed.
Next Obligation.
  red. move=> efl hasapp hasrel hasbox haspars hascstrs [Σ t] /= v [[wfe1 wfe2] wft] [ev].
  eexists. split; [ | eauto].
  unfold EEtaExpanded.expanded_eprogram_env_cstrs in *.
  revert wft. move => /andP // [e1 e2].
  econstructor.
  cbn -[transform_blocks].
  eapply transform_blocks_eval; cbn; eauto.
Qed.

#[global]
Instance constructors_as_blocks_extends (efl : EEnvFlags)
  {has_app : has_tApp} {has_rel : has_tRel} {hasbox : has_tBox} {has_pars : has_cstr_params = false} {has_cstrblocks : cstr_as_blocks = false} :
  TransformExt.t (constructors_as_blocks_transformation (has_app := has_app) (has_rel := has_rel) (hasbox := hasbox) (has_pars := has_pars) (has_cstrblocks := has_cstrblocks)) extends_eprogram_env term snd.
Proof.
  red. intros p p' pr pr' [ext eq]. rewrite /transform /=. rewrite -eq.
  eapply transform_blocks_extends; eauto. apply pr. apply pr'.
Qed.

From MetaCoq.Erasure Require Import EImplementBox.

Program Definition implement_box_transformation {efl : EEnvFlags}
  {has_app : has_tApp} {has_pars : has_cstr_params = false} {has_cstrblocks : cstr_as_blocks = true} :
  Transform.t eprogram eprogram EAst.term EAst.term (eval_eprogram block_wcbv_flags) (eval_eprogram block_wcbv_flags) :=
  {| name := "transforming to constuctors as blocks";
    transform p _ := EImplementBox.implement_box_program p ;
    pre p := wf_eprogram efl p ;
    post p := wf_eprogram (switch_off_box efl) p ;
    obseq p hp p' v v' := v' = implement_box v |}.

Next Obligation.
  intros. cbn in *. destruct p. split.
  - eapply transform_wf_global; eauto.
  - now eapply transform_wellformed'.
Qed.
Next Obligation.
  red. intros. destruct pr. destruct H.
  eexists. split; [ | eauto].
  econstructor.
  eapply implement_box_eval; cbn; eauto.
Qed.

#[global]
Instance implement_box_extends (efl : EEnvFlags) {has_app : has_tApp} {has_pars : has_cstr_params = false} {has_cstrblocks : cstr_as_blocks = true} :
   TransformExt.t (implement_box_transformation (has_app := has_app) (has_pars := has_pars) (has_cstrblocks := has_cstrblocks)) extends_eprogram term snd.
Proof.
  red. intros p p' pr pr' [ext eq]. rewrite /transform /=. now rewrite -eq.
Qed.
