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

#[local] Obligation Tactic := program_simpl.

#[local] Existing Instance extraction_checker_flags.

Import EWcbvEval.

Lemma transform_compose_assoc
  {env env' env'' env''' term term' term'' term''' : Type}
  {eval eval' eval'' eval'''}
  (o : t env env' term term' eval eval')
  (o' : t env' env'' term' term'' eval' eval'')
  (o'' : t env'' env''' term'' term''' eval'' eval''')
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
  {env env' env'' env''' term term' term'' term''' : Type}
  {eval eval' eval'' eval'''}
  (o : t env env' term term' eval eval')
  (o' : t env' env'' term' term'' eval' eval'')
  (o'' : t env'' env''' term'' term''' eval'' eval''')
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
  EGlobalEnv.extends pv.1 pt.1 /\ ∥ eval pt.1 pt.2 pv.2 ∥.
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
  unfold ErasureFunction.erase_global_fast.
  set (prf7 := (fun (Σ0 : PCUICAst.PCUICEnvironment.global_env) => _)).
  set (et := ErasureFunction.erase _ _ _ _ _).
  set (et' := ErasureFunction.erase _ _ _ _ _).
  destruct Σ as [Σ ext].
  cbn -[et et' PCUICWfEnv.abstract_make_wf_env_ext] in *.
  unshelve (epose proof ErasureFunction.erase_global_deps_fast_erase_global_deps as [norm eq];
    erewrite eq).
  { cbn. now intros ? ->. }
  unshelve (epose proof ErasureFunction.erase_global_deps_fast_erase_global_deps as [norm' eq'];
  erewrite eq').
  { cbn. now intros ? ->. }
  set (prf := (fun (Σ0 : PCUICAst.PCUICEnvironment.global_env) => _)). cbn in prf.
  rewrite (ErasureFunction.erase_global_deps_irr optimized_abstract_env_impl (EAstUtils.term_global_deps et) env' env _ prf prf).
  { cbn. now intros ? ? -> ->. }
  clearbody prf0 prf1 prf2 prf3 prf4 prf5 prf6 prf7.
  epose proof (ErasureFunction.erase_correct_strong optimized_abstract_env_impl (v:=v) env ext prf2
    (PCUICAst.PCUICEnvironment.declarations Σ) norm' prf prf6 X eq_refl axf ht fo).
  pose proof wf as [].
  forward H by (eapply Kernames.KernameSet.subset_spec; reflexivity).
  forward H by unshelve (eapply PCUICClassification.wcbveval_red; tea).
  forward H. {
    intros [? hr].
    eapply PCUICNormalization.firstorder_value_irred; tea. cbn.
    eapply PCUICFirstorder.firstorder_value_spec; tea. apply X0. constructor.
    eapply PCUICClassification.subject_reduction_eval; tea.
    eapply PCUICWcbvEval.eval_to_value; tea. }
  destruct H as [wt' []].
  split => //.
  eapply (ErasureFunction.erase_global_deps_eval optimized_abstract_env_impl env env' ext).
  unshelve erewrite (ErasureFunction.erase_irrel_global_env (X_type:=optimized_abstract_env_impl) (t:=v)); tea.
  red. intros. split; reflexivity.
  sq. unfold et', et.
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

Fixpoint compile_value_box Σ (t : PCUICAst.term) (acc : list EAst.term) : EAst.term :=
  match t with
  | PCUICAst.tApp f a => compile_value_box Σ f (compile_value_box Σ a [] :: acc)
  | PCUICAst.tConstruct i n _ =>
    match PCUICAst.PCUICEnvironment.lookup_env Σ (Kernames.inductive_mind i) with
    | Some (PCUICAst.PCUICEnvironment.InductiveDecl mdecl) =>
      EAst.tConstruct i n (skipn mdecl.(PCUICAst.PCUICEnvironment.ind_npars) acc)
    | _ => EAst.tVar "error"
    end
  | _ => EAst.tVar "error"
  end.

From Equations Require Import Equations.

Lemma erase_transform_fo_gen (p : pcuic_program) pr :
  PCUICFirstorder.firstorder_value p.1 [] p.2 ->
  forall ep, transform erase_transform p pr = ep -> ep.2 = compile_value_erase p.2 [].
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

Inductive firstorder_evalue Σ : EAst.term -> Prop :=
  | is_fo i n args npars :
  EGlobalEnv.lookup_inductive_pars Σ (Kernames.inductive_mind i) = Some npars ->
  Forall (firstorder_evalue Σ) (skipn npars args) ->
  firstorder_evalue Σ (EAst.mkApps (EAst.tConstruct i n []) args).

Lemma list_size_skipn {A} (l : list A) size n :
  list_size size (skipn n l) <= list_size size l.
Proof.
  induction n in l |- *.
  - rewrite skipn_0 //.
  - destruct l. rewrite skipn_nil. now cbn.
    rewrite skipn_S. cbn. specialize (IHn l); lia.
Qed.

Section elim.
  Context (Σ : E.global_context).
  Context (P : EAst.term -> Prop).
  Context (ih : (forall i n args npars,
    EGlobalEnv.lookup_inductive_pars Σ (Kernames.inductive_mind i) = Some npars ->
    Forall (firstorder_evalue Σ) (skipn npars args) ->
    Forall P (skipn npars args) ->
    P (EAst.mkApps (EAst.tConstruct i n []) args))).

  Equations? firstorder_evalue_elim (t : EAst.term) (fo : firstorder_evalue Σ t) : P t by wf t (MR lt EInduction.size) :=
  { | _, is_fo i n args npars hl hf => _ }.
  Proof.
    eapply ih; tea.
    eapply In_Forall. intros x hin.
    eapply PCUICWfUniverses.Forall_In in hf; tea.
    apply firstorder_evalue_elim => //. red.
    rewrite EInduction.size_mkApps.
    eapply (In_size id EInduction.size) in hin.
    unfold id in *. pose proof (list_size_skipn args EInduction.size npars).
    change (fun x => EInduction.size x) with EInduction.size in hin. clear -hin H.
    eapply Nat.lt_le_trans; tea. cbn. lia.
  Qed.
End elim.

(*Lemma firstorder_evalue_elim Σ {P : EAst.term -> Prop} :
  (forall i n args npars,
    EGlobalEnv.lookup_inductive_pars Σ (Kernames.inductive_mind i) = Some npars ->
    Forall (firstorder_evalue Σ) (skipn npars args) ->
    Forall P (skipn npars args) ->
    P (EAst.mkApps (EAst.tConstruct i n []) args)) ->
  forall t, firstorder_evalue Σ t -> P t.
Proof.
  intros Hf.
  induction t using term_size
  fix aux 2.
  intros t fo; destruct fo.x
  eapply Hf => //; tea.
  clear H.
  move: H0.
  move: args H0.
  fix aux' 2.
  intros args []; constructor.
  now apply aux. now apply aux'.
Qed.*)

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

(* Import PCUICAst.

Lemma compile_fo_value (Σ : global_env_ext) Σ' t :
  PCUICFirstorder.firstorder_value Σ [] t ->
  erases_global
  firstorder_evalue Σ (compile_value_erase t []).
Proof. Admitted. *)

Fixpoint compile_evalue_box (t : EAst.term) (acc : list EAst.term) :=
  match t with
  | EAst.tApp f a => compile_evalue_box f (compile_evalue_box a [] :: acc)
  | EAst.tConstruct i n _ => EAst.tConstruct i n acc
  | _ => EAst.tVar "error"
  end.

Import MetaCoq.Common.Transform.
From Coq Require Import Morphisms.

Module ETransformPresFO.
  Section Opt.
    Context {env env' : Type}.
    Context {eval : program env EAst.term -> EAst.term -> Prop}.
    Context {eval' : program env' EAst.term -> EAst.term -> Prop}.
    Context (o : Transform.t _ _ _ _ eval eval').
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
    Context (o : Transform.t _ _ _ _ eval eval').
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
    Context (o : Transform.t _ _ _ _ eval eval') (o' : Transform.t _ _ _ _ eval' eval'').
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

Lemma compile_value_box_mkApps Σ i n ui args acc :
  compile_value_box Σ (PCUICAst.mkApps (PCUICAst.tConstruct i n ui) args) acc =
  EAst.tConstruct i n (List.map (flip compile_value_box []) args ++ acc).
Proof.
  revert acc; induction args using rev_ind.
  - cbn. auto.
  - intros acc. rewrite PCUICAstUtils.mkApps_app /=. cbn.
    now rewrite IHargs map_app /= -app_assoc /=.
Qed.

Lemma compile_evalue_box_mkApps i n ui args acc :
  compile_evalue_box (EAst.mkApps (EAst.tConstruct i n ui) args) acc =
  EAst.tConstruct i n (List.map (flip compile_evalue_box []) args ++ acc).
Proof.
  revert acc; induction args using rev_ind.
  - cbn. auto.
  - intros acc. rewrite EAstUtils.mkApps_app /=. cbn.
    now rewrite IHargs map_app /= -app_assoc /=.
Qed.

Lemma compile_evalue_erase Σ v :
  PCUICFirstorder.firstorder_value Σ [] v ->
  compile_evalue_box (compile_value_erase v []) [] = compile_value_box v [].
Proof.
  move=> fo; move: v fo.
  apply: PCUICFirstorder.firstorder_value_inds.
  intros i n ui u args pandi hty hargs ih isp.
  rewrite compile_value_erase_mkApps compile_value_box_mkApps compile_evalue_box_mkApps.
  rewrite !app_nil_r. f_equal.
  rewrite map_map.
  now eapply map_ext_Forall.
Qed.

Lemma compile_evalue_box_firstorder {efl : EEnvFlags} Σ v :
  has_cstr_params = false ->
  EWellformed.wf_glob Σ ->
  firstorder_evalue Σ v -> firstorder_evalue_block (flip compile_evalue_box [] v).
Proof.
  intros hpars wf.
  move: v; apply: firstorder_evalue_elim.
  intros.
  rewrite /flip compile_evalue_box_mkApps app_nil_r.
  rewrite /EGlobalEnv.lookup_inductive_pars /= in H.
  destruct EGlobalEnv.lookup_minductive eqn:e => //.
  eapply wellformed_lookup_inductive_pars in hpars; tea => //.
  noconf H. rewrite hpars in H1. rewrite skipn_0 in H1.
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
    rewrite EInlineProjections.lookup_inductive_pars_optimize in H => //; tea. auto.
  - rewrite /fo_evalue_map. intros [] pr fo. cbn in *. unfold EInlineProjections.optimize_program. cbn. f_equal.
    destruct pr as [[pr _] _]. cbn in *. move: t1 fo.
    apply: firstorder_evalue_elim; intros.
    eapply wf_glob_lookup_inductive_pars in H => //. subst npars; rewrite skipn_0 in H0 H1.
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
    rewrite EOptimizePropDiscr.lookup_inductive_pars_optimize in H0 => //; tea.
  - intros [] pr fo.
    cbn in *.
    unfold EOptimizePropDiscr.remove_match_on_box_program; cbn. f_equal.
    destruct pr as [[pr _] _]; cbn in *; move: t1 fo.
    apply: firstorder_evalue_elim; intros.
    eapply wf_glob_lookup_inductive_pars in H0 => //. subst npars; rewrite skipn_0 in H2.
    rewrite EOptimizePropDiscr.remove_match_on_box_mkApps /=. f_equal.
    ELiftSubst.solve_all.
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
  rewrite ERemoveParams.strip_mkApps //. cbn -[EGlobalEnv.lookup_inductive_pars]. rewrite H.
  econstructor. cbn -[EGlobalEnv.lookup_inductive_pars].
  now eapply ERemoveParams.lookup_inductive_pars_strip in H; tea.
  rewrite skipn_0 /=.
  rewrite skipn_map.
  ELiftSubst.solve_all.
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
    clear pr. move: v fo.
    apply: firstorder_evalue_elim; intros.
    rewrite /transform_blocks_program /=. f_equal.
    rewrite EConstructorsAsBlocks.transform_blocks_decompose.
    rewrite EAstUtils.decompose_app_mkApps // /=.
    rewrite compile_evalue_box_mkApps app_nil_r.
    admit.
Admitted.


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
  nowrewrite hfn.
Qed.

Section pipeline_theorem.

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
    cbn. destruct Heval. repeat eapply conj; sq; cbn; eauto.
    - red. cbn. split; eauto.
      eexists.
      eapply PCUICClassification.subject_reduction_eval; eauto.
    - todo "preservation of eta expandedness".
    - cbn. todo "normalization".
    - todo "normalization".
  Qed.

  Let Σ_t := (transform verified_erasure_pipeline (Σ, t) precond).1.
  Let t_t := (transform verified_erasure_pipeline (Σ, t) precond).2.
  Let v_t := compile_value_box Σ v [].

  Lemma fo_v : PCUICFirstorder.firstorder_value Σ [] v.
  Proof.
    destruct Heval. sq.
    eapply PCUICFirstorder.firstorder_value_spec; eauto.
    - eapply PCUICClassification.subject_reduction_eval; eauto.
    - eapply PCUICWcbvEval.eval_to_value; eauto.
  Qed.

  Lemma v_t_spec : v_t = (transform verified_erasure_pipeline (Σ, v) precond2).2.
  Proof.
    unfold v_t. generalize fo_v, precond2. clear.
    intros hv pre.
    unfold verified_erasure_pipeline.
    rewrite -transform_compose_assoc.
    destruct_compose.
    cbn [transform pcuic_expand_lets_transform].
    rewrite (expand_lets_fo _ _ hv).
    cbn [fst snd].
    intros h.
    destruct_compose.
    rewrite erase_transform_fo. cbn. unfold global_env_ext_map_global_env_ext; cbn.
    todo "expand lets preserves fo values".
    set (Σer := (transform erase_transform _ _).1).
    cbn [fst snd]. intros pre'.
    symmetry.
    erewrite transform_lambda_box_firstorder; tea.
    now eapply compile_evalue_erase.
    clear -hv.
    move: v hv; eapply PCUICFirstorder.firstorder_value_inds.
    intros. rewrite compile_value_erase_mkApps app_nil_r.
    econstructor. ELiftSubst.solve_all.
  Qed.

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
