(* Distributed under the terms of the MIT license. *)
From Coq Require Import Program ssreflect ssrbool.
From MetaCoq.Common Require Import Transform config.
From MetaCoq.Utils Require Import bytestring utils.
From MetaCoq.PCUIC Require PCUICAst PCUICAstUtils PCUICProgram.
From MetaCoq.SafeChecker Require Import PCUICErrors PCUICWfEnvImpl.
From MetaCoq.Erasure Require EAstUtils ErasureFunction ErasureCorrectness EPretty Extract.
From MetaCoq Require Import ETransform EConstructorsAsBlocks.
From MetaCoq.Erasure Require Import EWcbvEvalNamed.
From MetaCoq.ErasurePlugin Require Import Erasure.
Import PCUICProgram.
(* Import TemplateProgram (template_eta_expand).
 *)
Import PCUICTransform (template_to_pcuic_transform, pcuic_expand_lets_transform).

(* This is the total erasure function +
  let-expansion of constructor arguments and case branches +
  shrinking of the global environment dependencies +
  the optimization that removes all pattern-matches on propositions. *)

Import Transform.

Obligation Tactic := program_simpl.

#[local] Existing Instance extraction_checker_flags.

Import EWcbvEval.

Lemma transform_compose_assoc
  {program program' program'' program''' value value' value'' value''' : Type}
  {eval : program -> value -> Prop} {eval' : program' -> value' -> Prop}
  {eval'' : program'' -> value'' -> Prop}
  {eval''' : program''' -> value''' -> Prop}
  (o : t program program' value value' eval eval')
  (o' : t program' program'' value' value'' eval' eval'')
  (o'' : t program'' program''' value'' value''' eval'' eval''')
  (prec : forall p : program', post o p -> pre o' p)
  (prec' : forall p : program'', post o' p -> pre o'' p) :
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
  {program program' program'' program''' value value' value'' value''' : Type}
  {eval : program -> value -> Prop} {eval' : program' -> value' -> Prop}
  {eval'' : program'' -> value'' -> Prop}
  {eval''' : program''' -> value''' -> Prop}
  (o : t program program' value value' eval eval')
  (o' : t program' program'' value' value'' eval' eval'')
  (o'' : t program'' program''' value'' value''' eval'' eval''')
  (prec : forall p : program', post o p -> pre o' p)
  (prec' : forall p : program'', post o' p -> pre o'' p) :
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

(*
Section TransformValue.
  Context {program program' : Type}.
  Context {value value' : Type}.
  Context {eval :  program -> value -> Prop}.
  Context {eval' : program' -> value' -> Prop}.
  Context (t : Transform.t program program' value value' eval eval').

  Lemma preserves_value p : value p.1 p.2 (transform t p)

  Definition preserves_eval pre (transform : forall p : program, pre p -> program')
      (obseq : forall p : program, pre p -> program' -> value -> value' -> Prop) :=
      forall p v (pr : pre p),
        eval p v ->
        let p' := transform p pr in
        exists v', eval' p' v' /\ obseq p pr p' v v'.

    Record t :=
    { name : string;

Lemma transform_value *)


Inductive is_construct_app : EAst.term -> Prop :=
| is_cstr_app_cstr kn c args : Forall is_construct_app args -> is_construct_app (EAst.tConstruct kn c args)
| is_cstr_app_app f a : is_construct_app f -> is_construct_app a -> is_construct_app (EAst.tApp f a).

Section lambdabox_theorem.

  Context (Σ Σ' : EEnvMap.GlobalContextMap.t) (v : EAst.term).

  Context (p : pre verified_lambdabox_pipeline (Σ, v)).
  Context (p' : pre verified_lambdabox_pipeline (Σ', v)).
  Context (is_value : value (wfl := default_wcbv_flags) Σ v).

  Lemma pres : extends_eprogram_env (Σ, v) (Σ', v) ->
    extends_eprogram (transform verified_lambdabox_pipeline (Σ, v) p)
        (transform verified_lambdabox_pipeline (Σ', v) p').
  Proof.
    epose proof (pres := verified_lambdabox_pipeline_extends).
    red in pres. specialize (pres _ _ p p'). auto.
  Qed.

  (* Final evaluation flags *)
  Definition evflags := {| with_prop_case := false; with_guarded_fix := false; with_constructor_as_block := true |}.

  Lemma pres_firstorder_value :
    is_construct_app v ->
    is_construct_app (transform verified_lambdabox_pipeline (Σ, v) p).2.
  Proof.
    intros isapp.
    destruct (preservation verified_lambdabox_pipeline (Σ, v) v p) as [v' [[ev] obs]].
    { red. cbn. sq. eapply value_final, is_value. }
    set (transp := transform _ _ p) in *.
    assert (value (wfl := evflags) transp.1 transp.2). admit.
    eapply eval_value in ev => //. subst v'.
    clear -obs isapp.
    unfold verified_lambdabox_pipeline in obs.
    cbn [obseq compose] in obs.
    unfold run, time in obs.
    decompose [ex and prod] obs. clear obs. subst.
    cbn [obseq compose verified_lambdabox_pipeline] in *.
    cbn [obseq compose constructors_as_blocks_transformation] in *.
    cbn [obseq run compose rebuild_wf_env_transform] in *.
    cbn [obseq compose inline_projections_optimization] in *.
    cbn [obseq compose remove_match_on_box_trans] in *.
    cbn [obseq compose remove_params_optimization] in *.
    cbn [obseq compose guarded_to_unguarded_fix] in *.
    cbn [obseq compose verified_lambdabox_pipeline] in *.
    subst.
    cbn [transform rebuild_wf_env_transform] in *.
    cbn [transform constructors_as_blocks_transformation] in *.
    cbn [transform inline_projections_optimization] in *.
    cbn [transform remove_match_on_box_trans] in *.
    cbn [transform remove_params_optimization] in *.
    cbn [transform guarded_to_unguarded_fix] in *.
    clearbody transp. revert b. intros ->. clear transp.
    induction isapp.
    cbn in *. constructor. constructor.
  Admitted.


End lambdabox_theorem.


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

Lemma extends_erase_pcuic_program {guard : abstract_guard_impl} (Σ : global_env_ext_map) t t' nin nin' nin0 nin0' wf wf' ty ty' :
  PCUICWcbvEval.eval Σ t' t ->
  EGlobalEnv.extends
    (@erase_pcuic_program guard (Σ, t) nin nin' wf ty).1
    (@erase_pcuic_program guard (Σ, t') nin0 nin0' wf' ty').1.
Proof.
  intros ev.
  cbn.
  unfold ErasureFunction.erase_global_fast.
  set (et := ErasureFunction.erase _ _ _ _ _).
  set (et' := ErasureFunction.erase _ _ _ _ _).
  erewrite ErasureFunction.erase_global_deps_fast_spec.
  erewrite ErasureFunction.erase_global_deps_fast_spec.
  epose proof ErasureFunction.erase_global_decls_irr.
  intros kn decl.
Admitted.

Section pipeline_theorem.

  Fixpoint compile_value_box (t : PCUICAst.term) (acc : list EAst.term) : EAst.term :=
    match t with
    | PCUICAst.tApp f a => compile_value_box f (acc ++ [compile_value_box a []])
    | PCUICAst.tConstruct i n _ => EAst.tConstruct i n acc
    | _ => EAst.tVar "error"
    end.

  Instance cf : checker_flags := extraction_checker_flags.
  Instance nf : PCUICSN.normalizing_flags := PCUICSN.extraction_normalizing.

  Variable Σ : global_env_ext_map.
  Variable HΣ : PCUICTyping.wf_ext Σ.
  Variable expΣ : PCUICEtaExpand.expanded_global_env Σ.1.

  Variable t : PCUICAst.term.
  Variable expt : PCUICEtaExpand.expanded Σ.1 [] t.

  Variable v : PCUICAst.term.

  Variable i : Kernames.inductive.
  Variable u : Universes.Instance.t.
  Variable args : list PCUICAst.term.

  Variable typing : PCUICTyping.typing Σ [] t (PCUICAst.mkApps (PCUICAst.tInd i u) args).

  Variable fo : @PCUICFirstorder.firstorder_ind Σ (PCUICFirstorder.firstorder_env Σ) i.

  Variable Normalisation :  PCUICSN.NormalizationIn Σ.

  Lemma precond : pre verified_erasure_pipeline (Σ, t).
  Proof.
    hnf. repeat eapply conj; sq; cbn; eauto.
    - red. cbn. eauto.
    - todo "normalization".
    - todo "normalization".
  Qed.

  Variable Heval : ∥PCUICWcbvEval.eval Σ t v∥.

  Lemma precond2 : pre verified_erasure_pipeline (Σ, v).
  Proof.
    cbn.  repeat eapply conj; sq; cbn; eauto.
    - red. cbn. split; eauto.
      eexists.
      eapply PCUICClassification.subject_reduction_eval; eauto.
    - todo "preservation of eta expandedness".
    - todo "normalization".
    - todo "normalization".
  Qed.

  Let Σ_t := (transform verified_erasure_pipeline (Σ, t) precond).1.
  Let t_t := (transform verified_erasure_pipeline (Σ, t) precond).2.
  Let v_t := compile_value_box v [].

  Lemma fo_v : PCUICFirstorder.firstorder_value Σ [] v.
  Proof.
    sq.
    eapply PCUICFirstorder.firstorder_value_spec; eauto.
    - eapply PCUICClassification.subject_reduction_eval; eauto.
    - eapply PCUICWcbvEval.eval_to_value; eauto.
  Qed.


  Lemma v_t_spec : v_t = (transform verified_erasure_pipeline (Σ, v) precond2).2.
  Proof.
    unfold v_t. generalize fo_v, precond2. clear.
    induction 1.
    intros. unfold verified_erasure_pipeline.
    repeat destruct_compose. intros.
    cbn [transform erase_transform].
    cbn [transform pcuic_expand_lets_transform].
  Admitted.

  Import PCUICWfEnv.



  Lemma verified_erasure_pipeline_theorem :
    ∥ eval (wfl := extraction_wcbv_flags) Σ_t t_t v_t∥.
  Proof.
    hnf.
    pose proof (preservation verified_erasure_pipeline (Σ, t)) as Hcorr.
    unshelve eapply Hcorr in Heval as Hev. eapply precond.
    destruct Hev as [v' [[H1] H2]].
    move: H2.

    (* repeat match goal with
      [ H : obseq _ _ _ _ _ |- _ ] => hnf in H ;  decompose [ex and prod] H ; subst
    end. *)
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
    eapply (ErasureFunction.firstorder_erases_deterministic optimized_abstract_env_impl wfe Σ.2) in b0. 3:tea.
    2:{ cbn. reflexivity. }
    2:{ eapply PCUICExpandLetsCorrectness.trans_wcbveval. eapply PCUICWcbvEval.eval_closed; tea. apply HΣ.
        admit.
        eapply PCUICWcbvEval.value_final. now eapply PCUICWcbvEval.eval_to_value in X0. }
    2:{ clear -fo. admit. }
    2:{ apply HΣ. }
    2:{ apply PCUICExpandLetsCorrectness.trans_wf, HΣ. }
    rewrite b0.
    intros obs.
    constructor.
    match goal with [ H1 : eval _ _ ?v1 |- eval _ _ ?v2 ] => enough (v2 = v1) as -> by exact ev end.
    eapply obseq_lambdabox; revgoals.
    unfold erase_pcuic_program. cbn [fst snd]. exact obs.
    clear obs b0 ev e w.
    eapply extends_erase_pcuic_program. cbn.
    eapply (PCUICExpandLetsCorrectness.trans_wcbveval (Σ := (Σ.1, Σ.2))). admit. exact X0.
  Admitted.

  Lemma verified_erasure_pipeline_lambda :
    PCUICAst.isLambda t -> EAst.isLambda t_t.
  Proof.
    unfold t_t. clear.
  Admitted.

End pipeline_theorem.
