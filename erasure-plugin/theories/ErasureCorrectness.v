(* Distributed under the terms of the MIT license. *)
From Coq Require Import Program ssreflect ssrbool.
From MetaCoq.Common Require Import Transform config.
From MetaCoq.Utils Require Import bytestring utils.
From MetaCoq.PCUIC Require PCUICAst PCUICAstUtils PCUICProgram.
From MetaCoq.SafeChecker Require Import PCUICErrors PCUICWfEnvImpl.
From MetaCoq.Erasure Require EAstUtils ErasureCorrectness EPretty Extract.
From MetaCoq Require Import ETransform EConstructorsAsBlocks.
From MetaCoq.Erasure Require Import EWcbvEvalNamed ErasureFunction ErasureFunctionProperties.
From MetaCoq.ErasurePlugin Require Import Erasure.
Import PCUICProgram.
Import PCUICTransform (template_to_pcuic_transform, pcuic_expand_lets_transform).

(* This is the total erasure function +
  let-expansion of constructor arguments and case branches +
  shrinking of the global environment dependencies +
  the optimization that removes all pattern-matches on propositions. *)

Import Transform.

#[local] Obligation Tactic := program_simpl.

#[local] Existing Instance extraction_checker_flags.

Import EWcbvEval.

Lemma transform_compose_assoc
  {env env' env'' env''' term term' term'' term''' value value' value'' value''' : Type}
  {eval eval' eval'' eval'''}
  (o : t env env' term term' value value' eval eval')
  (o' : t env' env'' term' term'' value' value'' eval' eval'')
  (o'' : t env'' env''' term'' term''' value'' value''' eval'' eval''')
  (prec : forall p, post o p -> pre o' p)
  (prec' : forall p, post o' p -> pre o'' p) :
  forall x p1,
    transform (compose o (compose o' o'' prec') prec) x p1 =
    transform (compose (compose o o' prec) o'' prec') x p1.
Proof.
  cbn. intros.
  unfold run, time.
  f_equal. f_equal.
  apply proof_irrelevance.
Qed.

Lemma obseq_compose_assoc
  {env env' env'' env''' term term' term'' term''' value value' value'' value''' : Type}
  {eval eval' eval'' eval'''}
  (o : t env env' term term' value value' eval eval')
  (o' : t env' env'' term' term'' value' value'' eval' eval'')
  (o'' : t env'' env''' term'' term''' value'' value''' eval'' eval''')
  (prec : forall p, post o p -> pre o' p)
  (prec' : forall p, post o' p -> pre o'' p) :
  forall x p1 p2 v1 v2, obseq (compose o (compose o' o'' prec') prec) x p1 p2 v1 v2 <->
      obseq (compose (compose o o' prec) o'' prec') x p1 p2 v1 v2.
Proof.
  cbn. intros.
  unfold run, time.
  intros. firstorder. exists x1. split.
  exists x0. split => //.
  assert (correctness o' (transform o x p1)
  (prec (transform o x p1) (correctness o x p1)) =
  (Transform.Transform.compose_obligation_1 o o' prec x p1)). apply proof_irrelevance.
  now rewrite -H.

  exists x1. split => //.
  exists x0. split => //.
  assert (correctness o' (transform o x p1)
  (prec (transform o x p1) (correctness o x p1)) =
  (Transform.Transform.compose_obligation_1 o o' prec x p1)). apply proof_irrelevance.
  now rewrite H.
Qed.

Import EEnvMap.GlobalContextMap.
Lemma make_irrel Σ fr fr' : EEnvMap.GlobalContextMap.make Σ fr = EEnvMap.GlobalContextMap.make Σ fr'.
Proof.
  unfold make. f_equal.
  apply proof_irrelevance.
Qed.

Lemma eval_value {efl : WcbvFlags} Σ v v' :
  value Σ v -> eval Σ v v' -> v = v'.
Proof.
  intros isv ev.
  now pose proof (eval_deterministic ev (value_final _ isv)).
Qed.

Ltac destruct_compose :=
  match goal with
  |- context [ transform (compose ?x ?y ?pre) ?p ?pre' ] =>
    let pre'' := fresh in
    let H := fresh in
    destruct (transform_compose x y pre p pre') as [pre'' H];
    rewrite H; clear H; revert pre''
    (* rewrite H'; clear H'; *)
    (* revert pre'' *)
  end.

Ltac destruct_compose_no_clear :=
    match goal with
    |- context [ transform (compose ?x ?y ?pre) ?p ?pre' ] =>
      let pre'' := fresh in
      let H := fresh in
      destruct (transform_compose x y pre p pre') as [pre'' H];
      rewrite H; revert pre'' H
    end.

Lemma rebuild_wf_env_irr {efl : EWellformed.EEnvFlags} p wf p' wf' :
  p.1 = p'.1 ->
  (rebuild_wf_env p wf).1 = (rebuild_wf_env p' wf').1.
Proof.
  destruct p as [], p' as [].
  cbn. intros <-.
  unfold make. f_equal. apply proof_irrelevance.
Qed.

Lemma obseq_lambdabox (Σt Σ'v : EProgram.eprogram_env) pr pr' p' v' :
  EGlobalEnv.extends Σ'v.1 Σt.1 ->
  obseq verified_lambdabox_pipeline Σt pr p' Σ'v.2 v' ->
  (transform verified_lambdabox_pipeline Σ'v pr').2 = v'.
Proof.
  intros ext obseq.
  destruct Σt as [Σ t], Σ'v as [Σ' v].
  pose proof verified_lambdabox_pipeline_extends.
  red in H.
  assert (pr'' : pre verified_lambdabox_pipeline (Σ, v)).
  { clear -pr pr' ext. destruct pr as [[] ?], pr' as [[] ?].
    split. red; cbn. split => //.
    eapply EWellformed.extends_wellformed; tea.
    split. apply H1. cbn. destruct H4; cbn in *.
    eapply EEtaExpandedFix.isEtaExp_expanded.
    eapply EEtaExpandedFix.isEtaExp_extends; tea.
    now eapply EEtaExpandedFix.expanded_isEtaExp. }
  destruct (H _ _ pr' pr'') as [ext' ->].
  split => //.
  clear H.
  move: obseq.
  unfold verified_lambdabox_pipeline.
  repeat destruct_compose.
  cbn [transform rebuild_wf_env_transform] in *.
  cbn [transform constructors_as_blocks_transformation] in *.
  cbn [transform inline_projections_optimization] in *.
  cbn [transform remove_match_on_box_trans] in *.
  cbn [transform remove_params_optimization] in *.
  cbn [transform guarded_to_unguarded_fix] in *.
  intros ? ? ? ? ? ? ?.
  unfold run, time.
  cbn [obseq compose constructors_as_blocks_transformation] in *.
  cbn [obseq run compose rebuild_wf_env_transform] in *.
  cbn [obseq compose inline_projections_optimization] in *.
  cbn [obseq compose remove_match_on_box_trans] in *.
  cbn [obseq compose remove_params_optimization] in *.
  cbn [obseq compose guarded_to_unguarded_fix] in *.
  intros obs.
  decompose [ex and prod] obs. clear obs. subst.
  unfold run, time.
  unfold transform_blocks_program. cbn [snd]. f_equal.
  repeat destruct_compose.
  intros.
  cbn [transform rebuild_wf_env_transform] in *.
  cbn [transform constructors_as_blocks_transformation] in *.
  cbn [transform inline_projections_optimization] in *.
  cbn [transform remove_match_on_box_trans] in *.
  cbn [transform remove_params_optimization] in *.
  cbn [transform guarded_to_unguarded_fix] in *.
  eapply rebuild_wf_env_irr.
  unfold EInlineProjections.optimize_program. cbn [fst snd].
  f_equal.
  eapply rebuild_wf_env_irr.
  unfold EOptimizePropDiscr.remove_match_on_box_program. cbn [fst snd].
  f_equal.
  now eapply rebuild_wf_env_irr.
Qed.

From MetaCoq.Erasure Require Import Erasure Extract ErasureFunction.
From MetaCoq.PCUIC Require Import PCUICTyping.

Lemma extends_erase_pcuic_program (efl := EWcbvEval.default_wcbv_flags) {guard : abstract_guard_impl} (Σ : global_env_ext_map) t v nin nin' nin0 nin0'
  wf wf' ty ty' i u args :
  PCUICWcbvEval.eval Σ t v ->
  axiom_free Σ ->
  Σ ;;; [] |- t : PCUICAst.mkApps (PCUICAst.tInd i u) args ->
  @PCUICFirstorder.firstorder_ind Σ (PCUICFirstorder.firstorder_env Σ) i ->
  let pt := @erase_pcuic_program guard (Σ, t) nin0 nin0' wf' ty' in
  let pv := @erase_pcuic_program guard (Σ, v) nin nin' wf ty in
  EGlobalEnv.extends pv.1 pt.1 /\ ∥ eval pt.1 pt.2 pv.2 ∥ /\ firstorder_evalue pt.1 pv.2.
Proof.
  intros ev axf ht fo.
  cbn -[erase_pcuic_program].
  unfold erase_pcuic_program.
  set (prf0 := (fun (Σ0 : PCUICAst.PCUICEnvironment.global_env) => _)).
  set (prf1 := (fun (Σ0 : PCUICAst.PCUICEnvironment.global_env) => _)).
  set (prf2 := (fun (Σ0 : PCUICAst.PCUICEnvironment.global_env) => _)).
  set (prf3 := (fun (Σ0 : PCUICAst.PCUICEnvironment.global_env_ext) => _)).
  set (prf4 := (fun (Σ0 : PCUICAst.PCUICEnvironment.global_env_ext) => _)).
  set (prf5 := (fun (Σ0 : PCUICAst.PCUICEnvironment.global_env_ext) => _)).
  set (prf6 := (fun (Σ0 : PCUICAst.PCUICEnvironment.global_env_ext) => _)).
  set (env' := build_wf_env_from_env _ _).
  set (env := build_wf_env_from_env _ _).
  set (X := PCUICWfEnv.abstract_make_wf_env_ext _ _ _).
  set (X' := PCUICWfEnv.abstract_make_wf_env_ext _ _ _).
  unfold erase_global_fast.
  set (prf7 := (fun (Σ0 : PCUICAst.PCUICEnvironment.global_env) => _)).
  set (et := ErasureFunction.erase _ _ _ _ _).
  set (et' := ErasureFunction.erase _ _ _ _ _).
  destruct Σ as [Σ ext].
  cbn -[et et' PCUICWfEnv.abstract_make_wf_env_ext] in *.
  unshelve (epose proof erase_global_deps_fast_erase_global_deps as [norm eq];
    erewrite eq).
  { cbn. now intros ? ->. }
  unshelve (epose proof erase_global_deps_fast_erase_global_deps as [norm' eq'];
  erewrite eq').
  { cbn. now intros ? ->. }
  set (prf := (fun (Σ0 : PCUICAst.PCUICEnvironment.global_env) => _)). cbn in prf.
  rewrite (ErasureFunction.erase_global_deps_irr optimized_abstract_env_impl (EAstUtils.term_global_deps et) env' env _ prf prf).
  { cbn. now intros ? ? -> ->. }
  clearbody prf0 prf1 prf2 prf3 prf4 prf5 prf6 prf7.
  epose proof (erase_correct_strong optimized_abstract_env_impl (v:=v) env ext prf2
    (PCUICAst.PCUICEnvironment.declarations Σ) norm' prf prf6 X eq_refl axf ht fo).
  pose proof wf as [].
  forward H by unshelve (eapply PCUICClassification.wcbveval_red; tea).
  forward H. {
    intros [? hr].
    eapply PCUICNormalization.firstorder_value_irred; tea. cbn.
    eapply PCUICFirstorder.firstorder_value_spec; tea. apply X0. constructor.
    eapply PCUICClassification.subject_reduction_eval; tea.
    eapply PCUICWcbvEval.eval_to_value; tea. }
  destruct H as [wt' [[] hfo]].
  split => //.
  eapply (erase_global_deps_eval optimized_abstract_env_impl env env' ext).
  unshelve erewrite (ErasureFunction.erase_irrel_global_env (X_type:=optimized_abstract_env_impl) (t:=v)); tea.
  red. intros. split; reflexivity.
  split => //.
  sq. unfold et', et.
  unshelve erewrite (ErasureFunction.erase_irrel_global_env (X_type:=optimized_abstract_env_impl) (t:=v)); tea.
  red. intros. split; reflexivity.
  subst et et' X X'.
  unshelve erewrite (ErasureFunction.erase_irrel_global_env (X_type:=optimized_abstract_env_impl) (t:=v)); tea.
  red. intros. split; reflexivity.
Qed.

Lemma expand_lets_fo (Σ : global_env_ext_map) t :
  PCUICFirstorder.firstorder_value Σ [] t ->
  let p := (Σ, t) in
  PCUICExpandLets.expand_lets_program p =
  (build_global_env_map (PCUICAst.PCUICEnvironment.fst_ctx (PCUICExpandLets.trans_global p.1)), p.1.2, t).
Proof.
  intros p.
  cbn. unfold PCUICExpandLets.expand_lets_program. f_equal. cbn.
  move: p. apply: (PCUICFirstorder.firstorder_value_inds _ _ (fun t => PCUICExpandLets.trans t = t)).
  intros i n ui u args pandi ht hf ih isp.
  rewrite PCUICExpandLetsCorrectness.trans_mkApps /=. f_equal.
  now eapply forall_map_id_spec.
Qed.

Definition pcuic_lookup_inductive_pars Σ ind :=
  match PCUICAst.PCUICEnvironment.lookup_env Σ (Kernames.inductive_mind ind) with
  | Some (PCUICAst.PCUICEnvironment.InductiveDecl mdecl) => Some mdecl.(PCUICAst.PCUICEnvironment.ind_npars)
  | _ => None
  end.

Fixpoint compile_value_box Σ (t : PCUICAst.term) (acc : list EAst.term) : EAst.term :=
  match t with
  | PCUICAst.tApp f a => compile_value_box Σ f (compile_value_box Σ a [] :: acc)
  | PCUICAst.tConstruct i n _ =>
    match pcuic_lookup_inductive_pars Σ i with
    | Some npars => EAst.tConstruct i n (skipn npars acc)
    | None => EAst.tVar "error"
    end
  | _ => EAst.tVar "error"
  end.

From Equations Require Import Equations.


Inductive firstorder_evalue_block : EAst.term -> Prop :=
  | is_fo_block i n args :
    Forall (firstorder_evalue_block) args ->
    firstorder_evalue_block (EAst.tConstruct i n args).

Lemma firstorder_evalue_block_elim {P : EAst.term -> Prop} :
  (forall i n args,
    Forall firstorder_evalue_block args ->
    Forall P args ->
    P (EAst.tConstruct i n args)) ->
  forall t, firstorder_evalue_block t -> P t.
Proof.
  intros Hf.
  fix aux 2.
  intros t fo; destruct fo.
  eapply Hf => //.
  move: args H.
  fix aux' 2.
  intros args []; constructor.
  now apply aux. now apply aux'.
Qed.

Import EWcbvEval.
Arguments erase_global_deps _ _ _ _ _ : clear implicits.
Arguments erase_global_deps_fast _ _ _ _ _ _ : clear implicits.

Section PCUICProof.
  Import PCUICAst.PCUICEnvironment.

  Definition erase_preserves_inductives Σ Σ' :=
    (forall kn decl decl', EGlobalEnv.lookup_env Σ' kn = Some (EAst.InductiveDecl decl) ->
    lookup_env Σ kn = Some (PCUICAst.PCUICEnvironment.InductiveDecl decl') ->
    decl = erase_mutual_inductive_body decl').

  Lemma lookup_env_in_erase_global_deps X_type X deps decls kn normalization_in prf decl :
    EnvMap.EnvMap.fresh_globals decls ->
    EGlobalEnv.lookup_env (erase_global_deps X_type deps X decls normalization_in prf).1 kn = Some (EAst.InductiveDecl decl) ->
    exists decl', lookup_global decls kn = Some (InductiveDecl decl') /\ decl = erase_mutual_inductive_body decl'.
  Proof.
    induction decls in deps, X, normalization_in, prf |- *; cbn [erase_global_deps] => //.
    destruct a => //. destruct g => //.
    - case: (knset_mem_spec k deps) => // hdeps.
      cbn [EGlobalEnv.lookup_env fst lookup_env lookup_global].
      { destruct (eqb_spec kn k) => //.
        intros hl. eapply IHdecls. now depelim hl. }
      { intros hl. depelim hl.
        intros hl'.
        eapply IHdecls in hl. destruct hl.
        exists x.
        cbn.
        destruct (eqb_spec kn k) => //. subst k.
        destruct H0.
        now eapply PCUICWeakeningEnv.lookup_global_Some_fresh in H0.
        exact hl'. }
    - intros hf; depelim hf.
      case: (knset_mem_spec k deps) => // hdeps.
      cbn [EGlobalEnv.lookup_env fst lookup_env lookup_global].
      { destruct (eqb_spec kn k) => //.
        intros hl. noconf hl. subst k. eexists; split; cbn; eauto.
        intros hl'. eapply IHdecls => //. tea. }
      { intros hl'. eapply IHdecls in hf; tea. destruct hf.
        exists x.
        cbn.
        destruct (eqb_spec kn k) => //. subst k.
        destruct H0.
        now eapply PCUICWeakeningEnv.lookup_global_Some_fresh in H0. }
    Qed.

  Lemma erase_tranform_firstorder (no := PCUICSN.extraction_normalizing) (wfl := default_wcbv_flags)
    {p : Transform.program global_env_ext_map PCUICAst.term} {pr v i u args}
    {normalization_in : PCUICSN.NormalizationIn p.1} :
    forall (wt : p.1 ;;; [] |- p.2 : PCUICAst.mkApps (PCUICAst.tInd i u) args),
    axiom_free p.1 ->
    @PCUICFirstorder.firstorder_ind p.1 (PCUICFirstorder.firstorder_env p.1) i ->
    PCUICWcbvEval.eval p.1 p.2 v ->
    forall ep, transform erase_transform p pr = ep ->
      erase_preserves_inductives p.1 ep.1 /\
      ∥ EWcbvEval.eval ep.1 ep.2 (compile_value_erase v []) ∥ /\
      firstorder_evalue ep.1 (compile_value_erase v []).
  Proof.
    destruct p as [Σ t]; cbn.
    intros ht ax fo ev [Σe te]; cbn.
    unfold erase_program, erase_pcuic_program.
    set (obl := ETransform.erase_pcuic_program_obligation_6 _ _ _ _ _ _).
    move: obl.
    rewrite /erase_global_fast.
    set (prf0 := fun (Σ0 : global_env) => _).
    set (prf1 := fun (Σ0 : global_env_ext) => _).
    set (prf2 := fun (Σ0 : global_env_ext) => _).
    set (prf3 := fun (Σ0 : global_env) => _).
    set (prf4 := fun n (H : n < _) => _).
    set (gext := PCUICWfEnv.abstract_make_wf_env_ext _ _ _).
    set (et := erase _ _ _ _ _).
    set (g := build_wf_env_from_env _ _).
    assert (hprefix: forall Σ0 : global_env, PCUICWfEnv.abstract_env_rel g Σ0 -> declarations Σ0 = declarations g).
    { intros Σ' eq; cbn in eq. rewrite eq; reflexivity. }
    destruct (@erase_global_deps_fast_erase_global_deps (EAstUtils.term_global_deps et) optimized_abstract_env_impl g
      (declarations Σ) prf4 prf3 hprefix) as [nin' eq].
    cbn [fst snd].
    rewrite eq.
    set (eg := erase_global_deps _ _ _ _ _ _).
    intros obl.
    epose proof (@erase_correct_strong optimized_abstract_env_impl g Σ.2 prf0 t v i u args _ _ hprefix prf1 prf2 Σ eq_refl ax ht fo).
    pose proof (proj1 pr) as [[]].
    forward H. eapply PCUICClassification.wcbveval_red; tea.
    assert (PCUICFirstorder.firstorder_value Σ [] v).
    { eapply PCUICFirstorder.firstorder_value_spec; tea. apply w. constructor.
      eapply PCUICClassification.subject_reduction_eval; tea.
      eapply PCUICWcbvEval.eval_to_value; tea. }
    forward H.
    { intros [v' redv]. eapply PCUICNormalization.firstorder_value_irred; tea. }
    destruct H as [wt' [ev' fo']].
    assert (erase optimized_abstract_env_impl (PCUICWfEnv.abstract_make_wf_env_ext (X_type:=optimized_abstract_env_impl) g Σ.2 prf0) [] v wt' =
      compile_value_erase v []).
    { clear -H0.
      clearbody prf0 prf1.
      destruct pr as [].
      destruct s as [[]].
      epose proof (erases_erase (X_type := optimized_abstract_env_impl) wt' _ eq_refl).
      eapply erases_firstorder' in H; eauto. }
    rewrite H in ev', fo'.
    intros [=]; subst te Σe.
    split => //.
    cbn. subst eg.
    intros kn decl decl' hl hl'.
    eapply lookup_env_in_erase_global_deps in hl as [decl'' [hl eq']].
    rewrite /lookup_env hl in hl'. now noconf hl'.
    eapply wf_fresh_globals, w.
  Qed.
End PCUICProof.
Lemma erase_transform_fo_gen (p : pcuic_program) pr :
  PCUICFirstorder.firstorder_value p.1 [] p.2 ->
  forall ep, transform erase_transform p pr = ep ->
  ep.2 = compile_value_erase p.2 [].
Proof.
  destruct p as [Σ t]. cbn.
  intros hev ep <-. move: hev pr.
  unfold erase_program, erase_pcuic_program; cbn -[erase PCUICWfEnv.abstract_make_wf_env_ext].
  intros fo pr.
  set (prf0 := fun (Σ0 : PCUICAst.PCUICEnvironment.global_env_ext) => _).
  set (prf1 := fun (Σ0 : PCUICAst.PCUICEnvironment.global_env_ext) => _).
  clearbody prf0 prf1.
  destruct pr as [].
  destruct s as [[]].
  epose proof (erases_erase (X_type := optimized_abstract_env_impl) prf1 _ eq_refl).
  eapply erases_firstorder' in H; eauto.
Qed.

Lemma erase_transform_fo (p : pcuic_program) pr :
  PCUICFirstorder.firstorder_value p.1 [] p.2 ->
  transform erase_transform p pr = ((transform erase_transform p pr).1, compile_value_erase p.2 []).
Proof.
  intros fo.
  set (tr := transform _ _ _).
  change tr with (tr.1, tr.2). f_equal.
  eapply erase_transform_fo_gen; tea. reflexivity.
Qed.

Import MetaCoq.Common.Transform.
From Coq Require Import Morphisms.

Module ETransformPresFO.
  Section Opt.
    Context {env env' : Type}.
    Context {eval : program env EAst.term -> EAst.term -> Prop}.
    Context {eval' : program env' EAst.term -> EAst.term -> Prop}.
    Context (o : Transform.t _ _ _ _ _ _ eval eval').
    Context (firstorder_value : program env EAst.term -> Prop).
    Context (firstorder_value' : program env' EAst.term -> Prop).
    Context (compile_fo_value : forall p : program env EAst.term, o.(pre) p ->
      firstorder_value p -> program env' EAst.term).

    Class t :=
      { preserves_fo : forall p pr (fo : firstorder_value p), firstorder_value' (compile_fo_value p pr fo);
        transform_fo : forall v (pr : o.(pre) v) (fo : firstorder_value v), o.(transform) v pr = compile_fo_value v pr fo }.
  End Opt.

  Section ExtEq.
    Context {env env' : Type}.
    Context {eval : program env EAst.term -> EAst.term -> Prop}.
    Context {eval' : program env' EAst.term -> EAst.term -> Prop}.
    Context (o : Transform.t _ _ _ _ _ _ eval eval').
    Context (firstorder_value : program env EAst.term -> Prop).
    Context (firstorder_value' : program env' EAst.term -> Prop).

    Lemma proper_pres (compile_fo_value compile_fo_value' : forall p : program env EAst.term, o.(pre) p -> firstorder_value p -> program env' EAst.term) :
      (forall p pre fo, compile_fo_value p pre fo = compile_fo_value' p pre fo) ->
      t o firstorder_value firstorder_value' compile_fo_value <->
      t o firstorder_value firstorder_value' compile_fo_value'.
    Proof.
      intros Hfg.
      split; move=> []; split; eauto.
      - now intros ? ? ?; rewrite -Hfg.
      - now intros v pr ?; rewrite -Hfg.
      - now intros ???; rewrite Hfg.
      - now intros ???; rewrite Hfg.
    Qed.
  End ExtEq.
  Section Comp.
    Context {env env' env'' : Type}.
    Context {eval : program env EAst.term -> EAst.term -> Prop}.
    Context {eval' : program env' EAst.term -> EAst.term -> Prop}.
    Context {eval'' : program env'' EAst.term -> EAst.term -> Prop}.
    Context (firstorder_value : program env EAst.term -> Prop).
    Context (firstorder_value' : program env' EAst.term -> Prop).
    Context (firstorder_value'' : program env'' EAst.term -> Prop).
    Context (o : Transform.t _ _ _ _ _ _ eval eval') (o' : Transform.t _ _ _ _ _ _ eval' eval'').
    Context compile_fo_value compile_fo_value'
      (oext : t o firstorder_value firstorder_value' compile_fo_value)
      (o'ext : t o' firstorder_value' firstorder_value'' compile_fo_value')
      (hpp : (forall p, o.(post) p -> o'.(pre) p)).

    Local Obligation Tactic := idtac.

    Definition compose_compile_fo_value (p : program env EAst.term) (pr : o.(pre) p) (fo : firstorder_value p) : program env'' EAst.term :=
      compile_fo_value' (compile_fo_value p pr fo) (eq_rect_r (o'.(pre)) (hpp _ (correctness o p pr)) (eq_sym (oext.(transform_fo _ _ _ _) _ _ _))) (oext.(preserves_fo _ _ _ _) p pr fo).

    #[global]
    Instance compose
      : t (Transform.compose o o' hpp) firstorder_value firstorder_value'' compose_compile_fo_value.
    Proof.
      split.
      - intros. eapply o'ext.(preserves_fo _ _ _ _); tea.
      - intros. cbn. unfold run, time.
        unfold compose_compile_fo_value.
        set (cor := correctness o v pr). clearbody cor. move: cor.
        set (foo := eq_sym (transform_fo _ _ _ _ _ _ _)). clearbody foo.
        destruct foo. cbn. intros cor.
        apply o'ext.(transform_fo _ _ _ _).
    Qed.
  End Comp.

End ETransformPresFO.

Import EWellformed.

Fixpoint compile_evalue_box_strip Σ (t : EAst.term) (acc : list EAst.term) :=
  match t with
  | EAst.tApp f a => compile_evalue_box_strip Σ f (compile_evalue_box_strip Σ a [] :: acc)
  | EAst.tConstruct i n _ =>
    match lookup_inductive_pars Σ (Kernames.inductive_mind i) with
    | Some npars => EAst.tConstruct i n (skipn npars acc)
    | None => EAst.tVar "error"
    end
  | _ => EAst.tVar "error"
  end.

Fixpoint compile_evalue_box (t : EAst.term) (acc : list EAst.term) :=
  match t with
  | EAst.tApp f a => compile_evalue_box f (compile_evalue_box a [] :: acc)
  | EAst.tConstruct i n _ => EAst.tConstruct i n acc
  | _ => EAst.tVar "error"
  end.

Lemma compile_value_box_mkApps {Σ i n ui args npars acc} :
  pcuic_lookup_inductive_pars Σ i = Some npars ->
  compile_value_box Σ (PCUICAst.mkApps (PCUICAst.tConstruct i n ui) args) acc =
  EAst.tConstruct i n (skipn npars (List.map (flip (compile_value_box Σ) []) args ++ acc)).
Proof.
  revert acc; induction args using rev_ind.
  - intros acc. cbn. intros ->. reflexivity.
  - intros acc. rewrite PCUICAstUtils.mkApps_app /=. cbn.
    intros hl.
    now rewrite IHargs // map_app /= -app_assoc /=.
Qed.

Lemma compile_evalue_box_strip_mkApps {Σ i n ui args acc npars} :
  lookup_inductive_pars Σ (Kernames.inductive_mind i) = Some npars ->
  compile_evalue_box_strip Σ (EAst.mkApps (EAst.tConstruct i n ui) args) acc =
  EAst.tConstruct i n (skipn npars (List.map (flip (compile_evalue_box_strip Σ) []) args ++ acc)).
Proof.
  revert acc; induction args using rev_ind.
  - intros acc. cbn. intros ->. auto.
  - intros acc hl. rewrite EAstUtils.mkApps_app /=. cbn.
    now rewrite IHargs // map_app /= -app_assoc /=.
Qed.

Lemma compile_evalue_box_mkApps {i n ui args acc} :
  compile_evalue_box (EAst.mkApps (EAst.tConstruct i n ui) args) acc =
  EAst.tConstruct i n (List.map (flip compile_evalue_box []) args ++ acc).
Proof.
  revert acc; induction args using rev_ind.
  - now intros acc.
  - intros acc. rewrite EAstUtils.mkApps_app /=. cbn.
    now rewrite IHargs // map_app /= -app_assoc /=.
Qed.
Derive Signature for firstorder_evalue.

Section PCUICenv.
  Import PCUICAst.
  Import PCUICEnvironment.

  Lemma pres_inductives_lookup Σ Σ' i n mdecl idecl cdecl :
    wf Σ ->
    erase_preserves_inductives Σ Σ' ->
    declared_constructor Σ (i, n) mdecl idecl cdecl ->
    forall npars nargs, EGlobalEnv.lookup_constructor_pars_args Σ' i n = Some (npars, nargs) ->
    npars = mdecl.(ind_npars) /\ nargs = cdecl.(cstr_arity).
  Proof.
    intros wf he.
    rewrite /declared_constructor /declared_inductive.
    intros [[declm decli] declc].
    unshelve eapply declared_minductive_to_gen in declm. 3:exact wf. red in declm.
    intros npars nargs. rewrite /EGlobalEnv.lookup_constructor_pars_args.
    rewrite /EGlobalEnv.lookup_constructor /EGlobalEnv.lookup_inductive /EGlobalEnv.lookup_minductive.
    destruct EGlobalEnv.lookup_env eqn:e => //=.
    destruct g => //.
    eapply he in declm; tea. subst m.
    rewrite nth_error_map decli /=.
    rewrite nth_error_map declc /=. intuition congruence.
  Qed.
End PCUICenv.

Lemma lookup_constructor_pars_args_lookup_inductive_pars Σ i n npars nargs :
  EGlobalEnv.lookup_constructor_pars_args Σ i n = Some (npars, nargs) ->
  EGlobalEnv.lookup_inductive_pars Σ (Kernames.inductive_mind i) = Some npars.
Proof.
  rewrite /EGlobalEnv.lookup_constructor_pars_args /EGlobalEnv.lookup_inductive_pars.
  rewrite /EGlobalEnv.lookup_constructor /EGlobalEnv.lookup_inductive.
  destruct EGlobalEnv.lookup_minductive => //=.
  destruct nth_error => //. destruct nth_error => //. congruence.
Qed.

Lemma compile_evalue_erase (Σ : PCUICAst.PCUICEnvironment.global_env_ext) (Σ' : EEnvMap.GlobalContextMap.t) v :
  wf Σ.1 ->
  PCUICFirstorder.firstorder_value Σ [] v ->
  firstorder_evalue Σ' (compile_value_erase v []) ->
  erase_preserves_inductives (PCUICAst.PCUICEnvironment.fst_ctx Σ) Σ' ->
  compile_evalue_box_strip Σ' (compile_value_erase v []) [] = compile_value_box (PCUICAst.PCUICEnvironment.fst_ctx Σ) v [].
Proof.
  move=> wf fo fo' hΣ; move: v fo fo'.
  apply: PCUICFirstorder.firstorder_value_inds.
  intros i n ui u args pandi hty hargs ih isp.
  eapply PCUICInductiveInversion.Construct_Ind_ind_eq' in hty as [mdecl [idecl [cdecl [declc _]]]] => //.
  rewrite compile_value_erase_mkApps.
  intros fo'. depelim fo'. EAstUtils.solve_discr. noconf H1. noconf H2.
  assert (npars = PCUICAst.PCUICEnvironment.ind_npars mdecl).
  { now eapply pres_inductives_lookup in declc; tea. }
  subst npars.
  rewrite (compile_value_box_mkApps (npars := PCUICAst.PCUICEnvironment.ind_npars mdecl)).
  { destruct declc as [[declm decli] declc].
    unshelve eapply declared_minductive_to_gen in declm. 3:exact wf.
    rewrite /PCUICAst.declared_minductive_gen in declm.
    rewrite /pcuic_lookup_inductive_pars // declm //. }
  rewrite (compile_evalue_box_strip_mkApps (npars := PCUICAst.PCUICEnvironment.ind_npars mdecl)) //.
  rewrite lookup_inductive_pars_spec //.
  eapply lookup_constructor_pars_args_lookup_inductive_pars; tea.
  rewrite !app_nil_r. f_equal.
  rewrite app_nil_r skipn_map in H0.
  eapply Forall_map_inv in H0.
  eapply (Forall_skipn _ (PCUICAst.PCUICEnvironment.ind_npars mdecl)) in ih.
  rewrite !skipn_map /flip map_map.
  ELiftSubst.solve_all.
Qed.


Lemma lookup_constructor_pars_args_nopars {efl : EEnvFlags} Σ ind c npars nargs :
  wf_glob Σ ->
  has_cstr_params = false ->
  EGlobalEnv.lookup_constructor_pars_args Σ ind c = Some (npars, nargs) -> npars = 0.
Proof.
  intros wf h.
  rewrite /EGlobalEnv.lookup_constructor_pars_args.
  destruct EGlobalEnv.lookup_constructor eqn:e => //=.
  destruct p as [[m i] cb]. intros [= <- <-].
  now eapply wellformed_lookup_constructor_pars in e.
Qed.

Lemma compile_evalue_box_firstorder {efl : EEnvFlags} {Σ : EEnvMap.GlobalContextMap.t} v :
  has_cstr_params = false ->
  EWellformed.wf_glob Σ ->
  firstorder_evalue Σ v -> firstorder_evalue_block (flip compile_evalue_box [] v).
Proof.
  intros hpars wf.
  move: v; apply: firstorder_evalue_elim.
  intros.
  rewrite /flip (compile_evalue_box_mkApps) // ?app_nil_r.
  eapply lookup_constructor_pars_args_nopars in H; tea. subst npars.
  rewrite skipn_0 in H1.
  constructor. ELiftSubst.solve_all.
Qed.

Definition fo_evalue (p : program E.global_context EAst.term) : Prop := firstorder_evalue p.1 p.2.
Definition fo_evalue_map (p : program EEnvMap.GlobalContextMap.t EAst.term) : Prop := firstorder_evalue p.1 p.2.

#[global] Instance rebuild_wf_env_transform_pres {fl : WcbvFlags} {efl : EEnvFlags} we  :
  ETransformPresFO.t
    (rebuild_wf_env_transform we) fo_evalue fo_evalue_map (fun p pr fo => rebuild_wf_env p pr.p1).
Proof. split => //. Qed.

Lemma wf_glob_lookup_inductive_pars {efl : EEnvFlags} (Σ : E.global_context) (kn : Kernames.kername) :
  has_cstr_params = false ->
  wf_glob Σ ->
  forall pars, EGlobalEnv.lookup_inductive_pars Σ kn = Some pars -> pars = 0.
Proof.
  intros hasp wf.
  rewrite /EGlobalEnv.lookup_inductive_pars.
  destruct EGlobalEnv.lookup_minductive eqn:e => //=.
  eapply wellformed_lookup_inductive_pars in e => //. congruence.
Qed.

#[global] Instance inline_projections_optimization_pres {fl : WcbvFlags}
 (efl := EInlineProjections.switch_no_params all_env_flags) {wcon : with_constructor_as_block = false}
  {has_rel : has_tRel} {has_box : has_tBox} :
  ETransformPresFO.t
    (inline_projections_optimization (wcon := wcon) (hastrel := has_rel) (hastbox := has_box))
    fo_evalue_map fo_evalue (fun p pr fo => (EInlineProjections.optimize_env p.1, p.2)).
Proof. split => //.
  - intros [] pr fo.
    cbn in *.
    destruct pr as [pr _]. destruct pr as [pr wf]; cbn in *.
    clear wf; move: t1 fo. unfold fo_evalue, fo_evalue_map. cbn.
    apply: firstorder_evalue_elim; intros.
    econstructor.
    move: H. rewrite /EGlobalEnv.lookup_constructor_pars_args.
    rewrite EInlineProjections.lookup_constructor_optimize //. intros h; exact h. auto. auto.
  - rewrite /fo_evalue_map. intros [] pr fo. cbn in *. unfold EInlineProjections.optimize_program. cbn. f_equal.
    destruct pr as [[pr _] _]. cbn in *. move: t1 fo.
    apply: firstorder_evalue_elim; intros.
    eapply lookup_constructor_pars_args_nopars in H; tea => //. subst npars.
    rewrite skipn_0 in H0 H1.
    rewrite EInlineProjections.optimize_mkApps /=. f_equal.
    ELiftSubst.solve_all.
Qed.

#[global] Instance remove_match_on_box_pres {fl : WcbvFlags} {efl : EEnvFlags} {wcon : with_constructor_as_block = false}
  {has_rel : has_tRel} {has_box : has_tBox} :
  has_cstr_params = false ->
  ETransformPresFO.t
    (remove_match_on_box_trans (wcon := wcon) (hastrel := has_rel) (hastbox := has_box))
    fo_evalue_map fo_evalue (fun p pr fo => (EOptimizePropDiscr.remove_match_on_box_env p.1, p.2)).
Proof. split => //.
  - unfold fo_evalue, fo_evalue_map; intros [] pr fo. cbn in *.
    destruct pr as [pr _]. destruct pr as [pr wf]; cbn in *.
    clear wf; move: t1 fo.
    apply: firstorder_evalue_elim; intros.
    econstructor; tea.
    move: H0.
    rewrite /EGlobalEnv.lookup_constructor_pars_args EOptimizePropDiscr.lookup_constructor_remove_match_on_box //.
  - intros [] pr fo.
    cbn in *.
    unfold EOptimizePropDiscr.remove_match_on_box_program; cbn. f_equal.
    destruct pr as [[pr _] _]; cbn in *; move: t1 fo.
    apply: firstorder_evalue_elim; intros.
    eapply lookup_constructor_pars_args_nopars in H0; tea => //. subst npars.
    rewrite skipn_0 in H2. rewrite EOptimizePropDiscr.remove_match_on_box_mkApps /=. f_equal.
    ELiftSubst.solve_all.
Qed.

Lemma lookup_constructor_pars_args_strip (Σ : t) i n npars nargs :
  EGlobalEnv.lookup_constructor_pars_args Σ i n = Some (npars, nargs) ->
  EGlobalEnv.lookup_constructor_pars_args (ERemoveParams.strip_env Σ) i n = Some (0, nargs).
Proof.
  rewrite /EGlobalEnv.lookup_constructor_pars_args. rewrite ERemoveParams.lookup_constructor_strip //=.
  destruct EGlobalEnv.lookup_constructor => //. destruct p as [[] ?] => //=. now intros [= <- <-].
Qed.

#[global] Instance remove_params_optimization_pres {fl : WcbvFlags} {wcon : with_constructor_as_block = false} :
  ETransformPresFO.t
    (remove_params_optimization (wcon := wcon))
    fo_evalue_map fo_evalue (fun p pr fo => (ERemoveParams.strip_env p.1, ERemoveParams.strip p.1 p.2)).
Proof. split => //.
  intros [] pr fo.
  cbn [transform remove_params_optimization] in *.
  destruct pr as [[pr _] _]; cbn -[ERemoveParams.strip] in *; move: t1 fo.
  apply: firstorder_evalue_elim; intros.
  rewrite ERemoveParams.strip_mkApps //. cbn -[EGlobalEnv.lookup_inductive_pars].
  rewrite (lookup_constructor_pars_args_lookup_inductive_pars _ _ _ _ _ H).
  eapply lookup_constructor_pars_args_strip in H.
  econstructor; tea. rewrite skipn_0 /= skipn_map.
  ELiftSubst.solve_all. len.
  rewrite skipn_map. len. rewrite skipn_length. lia.
Qed.

#[global] Instance constructors_as_blocks_transformation_pres {efl : EWellformed.EEnvFlags}
  {has_app : has_tApp} {has_rel : has_tRel} {hasbox : has_tBox} {has_pars : has_cstr_params = false} {has_cstrblocks : cstr_as_blocks = false} :
  ETransformPresFO.t
    (@constructors_as_blocks_transformation efl has_app has_rel hasbox has_pars has_cstrblocks)
    fo_evalue_map (fun p => firstorder_evalue_block p.2)
    (fun p pr fo => (transform_blocks_env p.1, compile_evalue_box p.2 [])).
Proof.
  split.
  - intros v pr fo; eapply compile_evalue_box_firstorder; tea. apply pr.
  - move=> [Σ v] /= pr fo. rewrite /flip.
    destruct pr as [[wf _] _]. cbn in wf.
    move: v fo.
    apply: firstorder_evalue_elim; intros.
    rewrite /transform_blocks_program /=. f_equal.
    rewrite EConstructorsAsBlocks.transform_blocks_decompose.
    rewrite EAstUtils.decompose_app_mkApps // /=.
    rewrite compile_evalue_box_mkApps // ?app_nil_r.
    rewrite H.
    eapply lookup_constructor_pars_args_nopars in H => //. subst npars.
    rewrite chop_all. len. cbn. f_equal. rewrite skipn_0 in H1 H0.
    ELiftSubst.solve_all. unfold transform_blocks_program in a. now noconf a.
Qed.

#[global] Instance guarded_to_unguarded_fix_pres {efl : EWellformed.EEnvFlags}
  {has_guard : with_guarded_fix} {has_cstrblocks : with_constructor_as_block = false} :
  ETransformPresFO.t
    (@guarded_to_unguarded_fix default_wcbv_flags has_cstrblocks efl has_guard)
    fo_evalue_map fo_evalue_map
    (fun p pr fo => p).
Proof.
  split => //.
Qed.

Lemma lambdabox_pres_fo :
  exists compile_value, ETransformPresFO.t verified_lambdabox_pipeline fo_evalue_map (fun p => firstorder_evalue_block p.2) compile_value /\
    forall p pr fo, (compile_value p pr fo).2 = compile_evalue_box (ERemoveParams.strip p.1 p.2) [].
Proof.
  eexists.
  split.
  unfold verified_lambdabox_pipeline.
  unshelve eapply ETransformPresFO.compose; tc. shelve.
  2:intros p pr fo; unfold ETransformPresFO.compose_compile_fo_value; f_equal. 2:cbn.
  unshelve eapply ETransformPresFO.compose; tc. shelve.
  2:unfold ETransformPresFO.compose_compile_fo_value; cbn.
  unshelve eapply ETransformPresFO.compose; tc. shelve.
  2:unfold ETransformPresFO.compose_compile_fo_value; cbn.
  unshelve eapply ETransformPresFO.compose; tc. shelve.
  2:unfold ETransformPresFO.compose_compile_fo_value; cbn.
  unshelve eapply ETransformPresFO.compose. shelve. eapply remove_match_on_box_pres => //.
  unfold ETransformPresFO.compose_compile_fo_value; cbn -[ERemoveParams.strip ERemoveParams.strip_env].
  reflexivity.
Qed.

Lemma transform_lambda_box_firstorder (Σer : EEnvMap.GlobalContextMap.t) p pre :
  firstorder_evalue Σer p ->
  (transform verified_lambdabox_pipeline (Σer, p) pre).2 = (compile_evalue_box (ERemoveParams.strip Σer p) []).
Proof.
  intros fo.
  destruct lambdabox_pres_fo as [fn [tr hfn]].
  rewrite (ETransformPresFO.transform_fo _ _ _ _ (t:=tr)).
  now rewrite hfn.
Qed.

Lemma compile_evalue_strip (Σer : EEnvMap.GlobalContextMap.t) p :
  firstorder_evalue Σer p ->
  compile_evalue_box (ERemoveParams.strip Σer p) [] = compile_evalue_box_strip Σer p [].
Proof.
  move: p.
  apply: firstorder_evalue_elim; intros.
  rewrite ERemoveParams.strip_mkApps //=.
  rewrite (lookup_constructor_pars_args_lookup_inductive_pars _ _ _ _ _ H).
  rewrite compile_evalue_box_mkApps.
  rewrite (compile_evalue_box_strip_mkApps (npars:=npars)).
  pose proof (lookup_constructor_pars_args_lookup_inductive_pars _ _ _ _ _ H).
  rewrite lookup_inductive_pars_spec //.
  rewrite !app_nil_r !skipn_map. f_equal.
  rewrite map_map.
  ELiftSubst.solve_all.
Qed.

Arguments PCUICFirstorder.firstorder_ind _ _ : clear implicits.

Section PCUICExpandLets.
  Import PCUICAst PCUICAstUtils PCUICFirstorder.
  Import PCUICEnvironment.
  Import PCUICExpandLets PCUICExpandLetsCorrectness.

  Lemma trans_axiom_free Σ : axiom_free Σ -> axiom_free (trans_global_env Σ).
  Proof.
    intros ax kn decl.
    rewrite /trans_global_env /= /PCUICAst.declared_constant /= /trans_global_decls.
    intros h; apply PCUICElimination.In_map in h as [[kn' decl']  [hin heq]].
    noconf heq. destruct decl'; noconf H.
    apply ax in hin.
    destruct c as [? [] ? ?] => //.
  Qed.

  Lemma expand_lets_preserves_fo (Σ : global_env_ext) Γ v :
    wf Σ ->
    firstorder_value Σ Γ v ->
    firstorder_value (trans_global Σ) (trans_local Γ) (trans v).
  Proof.
    intros wfΣ; move: v; apply: firstorder_value_inds.
    intros i n ui u args pandi hty hargs ihargs isp.
    rewrite trans_mkApps. econstructor.
    apply expand_lets_sound in hty.
    rewrite !trans_mkApps in hty. cbn in hty. exact hty.
    ELiftSubst.solve_all.
    move/negbTE: isp.
    rewrite /PCUICFirstorder.isPropositional.
    rewrite /lookup_inductive /lookup_inductive_gen /lookup_minductive_gen trans_lookup.
    destruct lookup_env => //. destruct g => //. cbn. rewrite nth_error_mapi.
    destruct nth_error => //=.
    rewrite /PCUICFirstorder.isPropositionalArity.
    rewrite (trans_destArity []). destruct destArity => //.
    destruct p => //. now intros ->.
  Qed.

  Lemma forallb_mapi {A B} (f f' : nat -> A -> B) (g g' : B -> bool) l :
    (forall n x, nth_error l n = Some x -> g (f n x) = g' (f' n x)) ->
    forallb g (mapi f l) = forallb g' (mapi f' l).
  Proof.
    unfold mapi.
    intros.
    assert
      (forall (n : nat) (x : A), nth_error l n = Some x -> g (f (0 + n) x) = g' (f' (0 + n) x)).
    { intros n x. now apply H. }
    clear H.
    revert H0.
    generalize 0.
    induction l; cbn; auto.
    intros n hfg. f_equal. specialize (hfg 0). rewrite Nat.add_0_r in hfg. now apply hfg.
    eapply IHl. intros. replace (S n + n0) with (n + S n0) by lia. eapply hfg.
    now cbn.
  Qed.

  Lemma forallb_mapi_impl {A B} (f f' : nat -> A -> B) (g g' : B -> bool) l :
    (forall n x, nth_error l n = Some x -> g (f n x) -> g' (f' n x)) ->
    forallb g (mapi f l) -> forallb g' (mapi f' l).
  Proof.
    unfold mapi.
    intros hfg.
    assert
      (forall (n : nat) (x : A), nth_error l n = Some x -> g (f (0 + n) x) -> g' (f' (0 + n) x)).
    { intros n x ?. now apply hfg. }
    clear hfg.
    revert H.
    generalize 0.
    induction l; cbn; auto.
    intros n hfg. move/andP => [] hg hf.
    pose proof (hfg 0). rewrite Nat.add_0_r in H. apply H in hg => //. rewrite hg /=.
    eapply IHl. intros. replace (S n + n0) with (n + S n0) by lia. eapply hfg. now cbn.
    now rewrite Nat.add_succ_r. assumption.
  Qed.

  Lemma expand_firstorder_type Σ n k t :
    (forall nm, plookup_env (firstorder_env' Σ) nm = Some true ->
      plookup_env (firstorder_env' (trans_global_decls Σ)) nm = Some true) ->
    @PCUICFirstorder.firstorder_type (firstorder_env' Σ) n k t ->
    @PCUICFirstorder.firstorder_type (firstorder_env' (trans_global_decls Σ)) n k (trans t).
  Proof.
    rewrite /PCUICFirstorder.firstorder_type /PCUICFirstorder.firstorder_env.
    pose proof (trans_decompose_app t).
    destruct decompose_app. rewrite {}H. cbn.
    case: t0 => //; case => /= kn _ _ hd.
    destruct plookup_env eqn:hp => //.
    destruct b => //.
    eapply hd in hp. rewrite hp //.
  Qed.

  Lemma trans_firstorder_mutind Σ m :
    (forall nm, plookup_env (firstorder_env' Σ) nm = Some true ->
      plookup_env (firstorder_env' (trans_global_decls Σ)) nm = Some true) ->
    @firstorder_mutind (firstorder_env' Σ) m ->
    @firstorder_mutind (firstorder_env' (trans_global_decls Σ)) (trans_minductive_body m).
  Proof.
    intros he.
    rewrite /firstorder_mutind. f_equal.
    rewrite /trans_minductive_body /=.
    rewrite -{1}[ind_bodies m]map_id. rewrite -mapi_cst_map.
    move/andP => [] -> /=.
    eapply forallb_mapi_impl.
    intros n x hnth.
    rewrite /firstorder_oneind. destruct x; cbn.
    move/andP => [] hc ->; rewrite andb_true_r.
    rewrite forallb_map. solve_all.
    move: H; rewrite /firstorder_con /=.
    rewrite !rev_app_distr !alli_app.
    move/andP => [hp ha]. apply/andP; split.
    - len. rewrite /trans_local -map_rev alli_map.
      eapply alli_impl; tea. intros i []. cbn.
      now eapply expand_firstorder_type.
    - len. len in ha. clear -ha he.
      move: ha; generalize (cstr_args x) as args.
      induction args => ha; cbn => //.
      destruct a as [na [] ?] => /=. eapply IHargs. cbn in ha.
      rewrite alli_app in ha. move/andP: ha => [] //.
      cbn. rewrite PCUICSigmaCalculus.smash_context_acc /=.
      cbn in ha. rewrite alli_app in ha. move/andP: ha => [] // hc hd.
      rewrite alli_app. apply/andP. split. apply IHargs => //.
      len. cbn. rewrite andb_true_r. cbn in hd. rewrite andb_true_r in hd. len in hd.
      clear -he hd. move: hd. rewrite /firstorder_type.
      destruct (decompose_app decl_type) eqn:e. cbn.
      destruct t0 => //; apply decompose_app_inv in e; rewrite e.
      { move/andP => [] /Nat.leb_le hn /Nat.ltb_lt hn'.
        rewrite trans_mkApps PCUICLiftSubst.lift_mkApps PCUICLiftSubst.subst_mkApps
          decompose_app_mkApps //=.
        { destruct nth_error eqn:hnth.
          pose proof (nth_error_Some_length hnth).
          move: hnth H.
          destruct (Nat.leb_spec #|args| n). len. lia. len. lia. now cbn. }
        destruct nth_error eqn:hnth.
        move/nth_error_Some_length: hnth. len. destruct (Nat.leb_spec #|args| n). lia. lia. len.
        destruct (Nat.leb_spec #|args| n). apply/andP. split.
        eapply Nat.leb_le. lia. apply Nat.ltb_lt. lia.
        apply/andP; split. apply Nat.leb_le. lia. apply Nat.ltb_lt. lia. }
      { rewrite trans_mkApps PCUICLiftSubst.lift_mkApps PCUICLiftSubst.subst_mkApps
          decompose_app_mkApps //=.
          destruct ind. destruct plookup_env eqn:hp => //. destruct b => //. apply he in hp. rewrite hp //. }
    Qed.

  Lemma trans_firstorder_env Σ :
    (forall nm, plookup_env (firstorder_env' Σ) nm = Some true ->
      plookup_env (firstorder_env' (trans_global_decls Σ)) nm = Some true).
  Proof.
    induction Σ; cbn => //.
    destruct a. destruct g => //=.
    intros nm.
    destruct eqb => //. now apply IHΣ.
    intros nm. destruct eqb => //.
    intros [=]. f_equal.
    now eapply trans_firstorder_mutind. apply IHΣ.
  Qed.

End PCUICExpandLets.


Section pipeline_theorem.

  Instance cf : checker_flags := extraction_checker_flags.
  Instance nf : PCUICSN.normalizing_flags := PCUICSN.extraction_normalizing.

  Variable Σ : global_env_ext_map.
  Variable HΣ : PCUICTyping.wf_ext Σ.
  Variable expΣ : PCUICEtaExpand.expanded_global_env Σ.1.

  Variable t : PCUICAst.term.
  Variable expt : PCUICEtaExpand.expanded Σ.1 [] t.
  Variable axfree : axiom_free Σ.
  Variable v : PCUICAst.term.

  Variable i : Kernames.inductive.
  Variable u : Universes.Instance.t.
  Variable args : list PCUICAst.term.

  Variable typing : PCUICTyping.typing Σ [] t (PCUICAst.mkApps (PCUICAst.tInd i u) args).

  Variable fo : @PCUICFirstorder.firstorder_ind Σ (PCUICFirstorder.firstorder_env Σ) i.

  Variable Normalisation :  (forall Σ, wf_ext Σ -> PCUICSN.NormalizationIn Σ).

  Lemma precond : pre verified_erasure_pipeline (Σ, t).
  Proof.
    hnf. repeat eapply conj; sq; cbn; eauto.
    - red. cbn. eauto.
    - intros. red. intros. now eapply Normalisation.
  Qed.

  Variable Heval : ∥PCUICWcbvEval.eval Σ t v∥.

  Lemma precond2 : pre verified_erasure_pipeline (Σ, v).
  Proof.
    cbn. destruct Heval. repeat eapply conj; sq; cbn; eauto.
    - red. cbn. split; eauto.
      eexists.
      eapply PCUICClassification.subject_reduction_eval; eauto.
    - eapply (PCUICClassification.wcbveval_red (Σ := Σ)) in X; tea.
      eapply PCUICEtaExpand.expanded_red in X; tea. apply HΣ.
      intros ? ?; rewrite nth_error_nil => //.
    - cbn. intros wf ? ? ? ? ? ?. now eapply Normalisation.
  Qed.

  Let Σ_t := (transform verified_erasure_pipeline (Σ, t) precond).1.
  Let t_t := (transform verified_erasure_pipeline (Σ, t) precond).2.
  Let v_t := compile_value_box (PCUICExpandLets.trans_global_env Σ) v [].

  Lemma fo_v : PCUICFirstorder.firstorder_value Σ [] v.
  Proof.
    destruct Heval. sq.
    eapply PCUICFirstorder.firstorder_value_spec; eauto.
    - eapply PCUICClassification.subject_reduction_eval; eauto.
    - eapply PCUICWcbvEval.eval_to_value; eauto.
  Qed.

  Lemma v_t_spec : v_t = (transform verified_erasure_pipeline (Σ, v) precond2).2.
  Proof.
    unfold v_t. generalize fo_v, precond2.
    intros hv pre.
    unfold verified_erasure_pipeline.
    rewrite -transform_compose_assoc.
    destruct_compose.
    cbn [transform pcuic_expand_lets_transform].
    rewrite (expand_lets_fo _ _ hv).
    cbn [fst snd].
    intros h.
    destruct_compose.
    destruct Heval.
    assert (eqtr : PCUICExpandLets.trans v = v).
    { clear -hv.
      move: v hv.
      eapply PCUICFirstorder.firstorder_value_inds.
      intros.
      rewrite PCUICExpandLetsCorrectness.trans_mkApps /=.
      f_equal. ELiftSubst.solve_all. }
    assert (PCUICFirstorder.firstorder_value (PCUICExpandLets.trans_global_env Σ.1, Σ.2) [] v).
    { eapply expand_lets_preserves_fo in hv; eauto. now rewrite eqtr in hv. }

    assert (Normalisation': PCUICSN.NormalizationIn (PCUICExpandLets.trans_global Σ)).
    { destruct h as [[] ?]. apply H0. cbn. apply X0. }
    set (Σ' := build_global_env_map _).
    set (p := transform erase_transform _ _).
    pose proof (@erase_tranform_firstorder _ h v i u (List.map PCUICExpandLets.trans args) Normalisation').
    forward H0.
    { cbn. rewrite -eqtr.
      eapply (PCUICClassification.subject_reduction_eval (Σ := Σ)) in X; tea.
      eapply PCUICExpandLetsCorrectness.expand_lets_sound in X.
      now rewrite PCUICExpandLetsCorrectness.trans_mkApps /= in X. }
    forward H0. { cbn. now eapply trans_axiom_free. }
    forward H0.
    { cbn. clear -HΣ fo.
      move: fo.
      rewrite /PCUICFirstorder.firstorder_ind /= PCUICExpandLetsCorrectness.trans_lookup /=.
      destruct PCUICAst.PCUICEnvironment.lookup_env => //. destruct g => //=.
      eapply trans_firstorder_mutind. eapply trans_firstorder_env. }
    forward H0. { cbn. rewrite -eqtr.
      unshelve eapply (PCUICExpandLetsCorrectness.trans_wcbveval (Σ := Σ)); tea. exact extraction_checker_flags.
      apply HΣ. apply PCUICExpandLetsCorrectness.trans_wf, HΣ.
      2:{ eapply PCUICWcbvEval.value_final. now eapply PCUICWcbvEval.eval_to_value in X. }
      eapply PCUICWcbvEval.eval_closed; tea. apply HΣ.
      unshelve apply (PCUICClosedTyp.subject_closed typing). }
    specialize (H0 _ eq_refl).
    rewrite /p.
    rewrite erase_transform_fo //.
    set (Σer := (transform erase_transform _ _).1).
    cbn [fst snd]. intros pre'.
    symmetry.
    destruct Heval as [Heval'].
    assert (firstorder_evalue Σer (compile_value_erase v [])).
    { apply H0. }
    erewrite transform_lambda_box_firstorder; tea.
    rewrite compile_evalue_strip //.
    destruct pre as [[wt] ?]. destruct wt.
    apply (compile_evalue_erase (PCUICExpandLets.trans_global Σ) Σer) => //.
    { cbn. now eapply (@PCUICExpandLetsCorrectness.trans_wf extraction_checker_flags Σ). }
    destruct H0. cbn -[transform erase_transform] in H0. apply H0.
  Qed.

  Import PCUICWfEnv.

  Lemma verified_erasure_pipeline_theorem :
    ∥ eval (wfl := extraction_wcbv_flags) Σ_t t_t v_t ∥.
  Proof.
    hnf.
    pose proof (preservation verified_erasure_pipeline (Σ, t)) as Hcorr.
    unshelve eapply Hcorr in Heval as Hev. eapply precond.
    destruct Hev as [v' [[H1] H2]].
    move: H2.
    rewrite v_t_spec.
    subst v_t Σ_t t_t.
    revert H1.
    unfold verified_erasure_pipeline.
    intros.
    revert H1 H2. clear Hcorr.
    intros ev obs.
    cbn [obseq compose] in obs.
    unfold run, time in obs.
    decompose [ex and prod] obs. clear obs.
    subst.
    cbn [obseq compose erase_transform] in *.
    cbn [obseq compose pcuic_expand_lets_transform] in *.
    subst.
    move: ev b.
    repeat destruct_compose.
    intros.
    move: b.
    cbn [transform rebuild_wf_env_transform] in *.
    cbn [transform constructors_as_blocks_transformation] in *.
    cbn [transform inline_projections_optimization] in *.
    cbn [transform remove_match_on_box_trans] in *.
    cbn [transform remove_params_optimization] in *.
    cbn [transform guarded_to_unguarded_fix] in *.
    cbn [transform erase_transform] in *.
    cbn [transform compose pcuic_expand_lets_transform] in *.
    unfold run, time.
    cbn [obseq compose constructors_as_blocks_transformation] in *.
    cbn [obseq run compose rebuild_wf_env_transform] in *.
    cbn [obseq compose inline_projections_optimization] in *.
    cbn [obseq compose remove_match_on_box_trans] in *.
    cbn [obseq compose remove_params_optimization] in *.
    cbn [obseq compose guarded_to_unguarded_fix] in *.
    cbn [obseq compose erase_transform] in *.
    cbn [obseq compose pcuic_expand_lets_transform] in *.
    cbn [transform compose pcuic_expand_lets_transform] in *.
    cbn [transform erase_transform] in *.
    destruct Heval.
    pose proof typing as typing'.
    eapply PCUICClassification.subject_reduction_eval in typing'; tea.
    eapply PCUICExpandLetsCorrectness.pcuic_expand_lets in typing'.
    rewrite PCUICExpandLetsCorrectness.trans_mkApps /= in typing'.
    destruct H1.
    (* pose proof (abstract_make_wf_env_ext) *)
    unfold PCUICExpandLets.expand_lets_program.
    set (em := build_global_env_map _).
    unfold erase_program.
    set (f := map_squash _ _). cbn in f.
    destruct H. destruct s as [[]].
    set (wfe := build_wf_env_from_env em (map_squash (PCUICTyping.wf_ext_wf (em, Σ.2)) (map_squash fst (conj (sq (w0, s)) a).p1))).
    destruct Heval.
    eapply (ErasureFunctionProperties.firstorder_erases_deterministic optimized_abstract_env_impl wfe Σ.2) in b0. 3:tea.
    2:{ cbn. reflexivity. }
    2:{ eapply PCUICExpandLetsCorrectness.trans_wcbveval. eapply PCUICWcbvEval.eval_closed; tea. apply HΣ.
        clear -typing HΣ; now eapply PCUICClosedTyp.subject_closed in typing.
        eapply PCUICWcbvEval.value_final. now eapply PCUICWcbvEval.eval_to_value in X0. }
    2:{ clear -fo. revert fo. rewrite /PCUICFirstorder.firstorder_ind /=.
        rewrite PCUICExpandLetsCorrectness.trans_lookup.
        destruct PCUICAst.PCUICEnvironment.lookup_env => //.
        destruct g => //=.
        eapply trans_firstorder_mutind. eapply trans_firstorder_env. }
    2:{ apply HΣ. }
    2:{ apply PCUICExpandLetsCorrectness.trans_wf, HΣ. }
    rewrite b0. intros obs. constructor.
    match goal with [ H1 : eval _ _ ?v1 |- eval _ _ ?v2 ] => enough (v2 = v1) as -> by exact ev end.
    eapply obseq_lambdabox; revgoals.
    unfold erase_pcuic_program. cbn [fst snd]. exact obs.
    Unshelve. all:eauto.
    2:{ eapply PCUICExpandLetsCorrectness.trans_wf, HΣ. }
    clear obs b0 ev e w.
    eapply extends_erase_pcuic_program. cbn.
    unshelve eapply (PCUICExpandLetsCorrectness.trans_wcbveval (cf := extraction_checker_flags) (Σ := (Σ.1, Σ.2))).
    { now eapply PCUICExpandLetsCorrectness.trans_wf. }
    { clear -HΣ typing. now eapply PCUICClosedTyp.subject_closed in typing. }
    cbn. 2:cbn. 3:cbn. exact X0.
    now eapply trans_axiom_free.
    pose proof (PCUICExpandLetsCorrectness.expand_lets_sound typing).
    rewrite PCUICExpandLetsCorrectness.trans_mkApps in X1. eapply X1.
    cbn.
    move: fo. clear.
    { rewrite /PCUICFirstorder.firstorder_ind /=.
      rewrite PCUICExpandLetsCorrectness.trans_lookup.
      destruct PCUICAst.PCUICEnvironment.lookup_env => //.
      destruct g => //=.
      eapply trans_firstorder_mutind. eapply trans_firstorder_env. }
  Qed.

  (*Lemma verified_erasure_pipeline_lambda :
    PCUICAst.isLambda t -> EAst.isLambda t_t.
  Proof.
    unfold t_t. clear.
  Qed.*)

End pipeline_theorem.

