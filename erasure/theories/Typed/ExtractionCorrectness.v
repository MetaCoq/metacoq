From Coq Require Import List ssreflect ssrbool.
From MetaCoq.Erasure.Typed Require Import ErasureCorrectness.
From MetaCoq.Erasure.Typed Require Import ExAst.
From MetaCoq.Erasure.Typed Require Import Extraction.
From MetaCoq.Erasure.Typed Require Import Optimize.
From MetaCoq.Erasure.Typed Require Import OptimizeCorrectness.
From MetaCoq.Erasure.Typed Require Import OptimizePropDiscr.
From MetaCoq.Erasure.Typed Require Import ResultMonad.
From MetaCoq.Erasure.Typed Require Import WcbvEvalAux.
From Equations Require Import Equations.
From MetaCoq.Erasure Require Import ErasureCorrectness.
From MetaCoq.Erasure Require Import ErasureFunction.
From MetaCoq.Erasure Require Import ErasureFunctionProperties.
From MetaCoq.Erasure Require Import EWcbvEval.
From MetaCoq.Erasure Require Import Extract.
From MetaCoq.PCUIC Require Import PCUICAstUtils.
From MetaCoq.PCUIC Require Import PCUICSafeLemmata.
From MetaCoq.PCUIC Require Import PCUICTyping.
From MetaCoq.PCUIC Require Import PCUICInversion.
From MetaCoq.Common Require Import Kernames.
From MetaCoq.Utils Require Import utils.

Import ListNotations.

Module P := PCUICAst.
Module E := EAst.

Notation "Σ 'p⊢' s ⇓ t" := (PCUICWcbvEval.eval Σ s t) (at level 50, s, t at next level) : type_scope.

Lemma wf_squash {Σ} :
  ∥wf_ext Σ∥ ->
  ∥wf Σ∥.
Proof. intros []. now constructor. Qed.

Lemma lookup_env_In d Σ : wf Σ -> In d (PEnv.declarations Σ) -> forall d', In d' (PEnv.declarations Σ) ->
  fst d = fst d' -> snd d = snd d'.
Proof using Type.
  intros [_].
  destruct Σ as [univs decls retro]; cbn in *.
  induction o in d |- *; auto.
  - intros H; inversion H.
  - intros [H|H].
    + subst. cbn.
      intros d' [H'|H']; subst; auto.
      intros eq.
      destruct o0 as [fresh _ _ _].
      subst kn. eapply P.fresh_global_iff_not_In in fresh.
      eapply (in_map fst) in H'.
      now apply fresh in H'.
    + intros d' [H'|H'] eq; subst; cbn in *; auto.
      subst.
      destruct o0 as [fresh _ _ _].
      eapply P.fresh_global_iff_not_In in fresh.
      eapply (in_map fst) in H.
      now apply fresh in H.
Qed.

Lemma lookup_global_In_wf d Σ : wf Σ ->
  In d (PEnv.declarations Σ) -> P.lookup_global (PEnv.declarations Σ) d.1 <> None.
Proof using Type.
  intros wfΣ. destruct d as [kn decl].
  intros hin. eapply (in_map fst) in hin.
  intros hne; rewrite <- P.lookup_global_None in hne. contradiction.
Qed.

Lemma global_erased_with_deps_erases_deps_tConst Σ Σer kn cst :
  wf Σ ->
  P.declared_constant Σ kn cst ->
  global_erased_with_deps Σ Σer kn ->
  erases_deps Σ Σer (E.tConst kn).
Proof.
  intros wf decl glob.
  destruct glob as [(?&?&?&?&?&?)|(?&?&?&?&?)].
  - econstructor; eauto.
  - unfold P.declared_constant, PCUICAst.declared_minductive in *.
    eapply lookup_env_In in decl; tea. now cbn in decl. auto.
Qed.

Module PEnv := PCUICAst.PCUICEnvironment.
Import PCUICWfEnv ErasureFunction ErasureFunctionProperties.

Lemma extends_trans Σ Σ' Σ'' :
  EGlobalEnv.extends Σ Σ' ->
  EGlobalEnv.extends Σ' Σ'' ->
  EGlobalEnv.extends Σ Σ''.
Proof.
  intros e e' kn h h'.
  eapply e in h'. now eapply e' in h'.
Qed.

(* Lemma trans_global_decl_erase {X_type X} :
  trans_global_decl (@Erasure.erase_global_decl X_type X Σ prf kn decl ond) = *)

Lemma filter_deps_ext deps deps' l :
  KernameSet.Equal deps deps' ->
  filter_deps deps l = filter_deps deps' l.
Proof.
  induction l as [|[kn d] decls] in deps, deps' |- *; cbn; auto.
  destruct (KernameSet.mem kn deps) eqn:e.
  eapply KernameSet.mem_spec in e.
  intros kne. eapply kne in e. eapply KernameSet.mem_spec in e. rewrite e.
  rewrite (IHdecls _ _ kne); eauto. destruct d. f_equal. eapply IHdecls. now rewrite kne.
  f_equal.
  intros hne.
  destruct (KernameSet.mem kn deps') eqn:e'.
  rewrite <- hne in e'. congruence.
  now eapply IHdecls.
Qed.

Lemma trans_env_erase_global_decls {X_type X} decls univs retro prf deps deps' ignored :
  (forall k, ignored k = false) ->
  KernameSet.Subset deps deps' ->
  EGlobalEnv.extends (trans_env (@Erasure.erase_global_decls_deps_recursive X_type X decls univs retro prf deps ignored))
    (filter_deps deps' (trans_env (@Erasure.erase_global_decls_recursive X_type X decls univs retro prf))).
Proof.
  induction decls in X_type, X, deps, deps', ignored, prf |- *.
  - now cbn.
  - cbn. intros hign hsub.
    destruct a. destruct g.
    destruct (KernameSet.mem k deps) eqn:e; cbn [map filter_deps].
    assert (KernameSet.mem k deps') as ->.
    { eapply KernameSet.mem_spec in e.
      now apply KernameSet.mem_spec. }
    set (er := Erasure.erase_global_decl _ _ _ _ _).
    set (er' := Erasure.erase_global_decl _ _ _ _ _).
    set (prf' := fun (Σ : PCUICAst.PCUICEnvironment.global_env) => _).
    assert (trans_global_decl er = trans_global_decl er'). admit.
    rewrite <- H.
    destruct (trans_global_decl er) eqn:eqr.
    rewrite hign.
    eapply extends_cons.
    unfold trans_env in IHdecls.
    eapply (IHdecls _ _ prf'); eauto. cbn [negb].
    intros kn.
    rewrite !KernameSet.union_spec.
Admitted.

Lemma wf_erase_global_decl :
  forall (H := EWellformed.all_env_flags)
        X_type X
        (k : kername) (g : PCUICAst.PCUICEnvironment.global_decl)
         (decls : list (kername * PCUICAst.PCUICEnvironment.global_decl))
         (univs : Universes.ContextSet.t) retros prf w wt (Σex : global_env) prf' seeds ignored,
    let eg := (@Erasure.erase_global_decl X_type
    (abstract_make_wf_env_ext X (PCUICAst.PCUICLookup.universes_decl_of_decl g) prf)
    ({| PEnv.universes := univs; PEnv.declarations := decls; PEnv.retroknowledge := retros |},
      PCUICAst.PCUICLookup.universes_decl_of_decl g)
    w k g wt) in
    (forall kn, ignored kn = false) ->
    Σex = @Erasure.erase_global_decls_deps_recursive X_type X decls univs retros prf'
      (KernameSet.union (Erasure.decl_deps eg) seeds) ignored ->
    EWellformed.wf_glob (trans_env Σex) ->
    EWellformed.wf_global_decl
      (trans_env Σex)
      (trans_global_decl eg) = true.
Proof.
  intros H X_type X k g decls univs retros prf w wt Σex prf' seeds ignored eg hign eqex wf_global.
  revert eqex. subst eg.
  unfold Erasure.erase_global_decl.
  destruct g.
  - destruct (Erasure.erase_constant_decl) eqn:Hdecl.
    * unfold Erasure.erase_constant_decl,Erasure.erase_constant_decl_clause_1 in *.
      destruct (Erasure.flag_of_type), conv_ar;try congruence.
      inversion Hdecl;subst;clear Hdecl.
      unfold trans_global_decl,trans_cst.
      cbn [EWellformed.wf_global_decl].
      unfold MCOption.option_default.
      destruct EAst.cst_body eqn:heq.
      set (deps := KernameSet.union _ _).
      unshelve eapply (erase_constant_body_correct'' (X_type := X_type) (decls := decls) seeds) in heq as [[t0 [T [[] ?]]]].
      shelve. intros. eapply Erasure.fake_normalization; tea.
      { intros. now rewrite (prf' _ H0). }
      2:exact w.
      intros ->.
      eapply EWellformed.extends_wellformed; tea.
      set (prf'' := fun _ => _). clearbody prf''. cbn in prf''.
      rewrite erase_global_deps_erase_global.
      clear.
      induction decls. red; auto.
      cbn -[Erasure.erase_global_decls_deps_recursive].
      destruct a as [kn []].
      set (prf0 := (fun (pf : _) => _)).
      set (prf1 := (fun (pf : _) => _)).
      set (prf2 := (fun (pf : _) => _)).
      clearbody prf2.
      cbn -[erase_global Erasure.erase_global_decls_deps_recursive].
      destruct (KernameSet.mem _ _) eqn:e.
      set (prf3 := (fun (pf : _) => _)).
      clearbody prf3.


Admitted.


Ltac invert_wf :=
  match goal with
  | [H : wf _ |- _] => sq; inversion H;subst;clear H;cbn in *
  | [H : P.on_global_decls _ _ _ _ (_ :: _) |- _] => inversion H;subst;clear H;cbn in *
  | [H : P.on_global_decls_data _ _ _ _ _ _ _ |- _] => inversion H; subst; clear H; cbn in *
  end.

Lemma wf_erase_global_decls_recursive (H := EWellformed.all_env_flags) :
  forall X_type X decls univs retros w seeds (ignored : kername -> bool),
    (forall k, ignored k = false) ->
    let Σex := @Erasure.erase_global_decls_deps_recursive X_type X decls univs retros w seeds ignored in
    EWellformed.wf_glob (trans_env Σex).
Proof.
  intros X_type X decls univs retros w seeds ignored hign ?.
  subst Σex.
  revert seeds.
  induction decls in X_type, X, w |- *;intros seeds;auto;try constructor.
  simpl.
  destruct a;simpl.
  destruct (KernameSet.mem _ _);cbn.
  - unfold MCProd.test_snd;cbn.
    constructor.
    * unfold trans_env in *;cbn in *.
      apply IHdecls.
    * cbn.
      remember (KernameSet.union _ _) as kns.
      rewrite hign in Heqkns. cbn in Heqkns.
      remember (Erasure.erase_global_decls_deps_recursive decls univs _ _ _ _) as Σex.
      assert (EWellformed.wf_glob (trans_env Σex)) by now subst Σex.
      rewrite -/(trans_env _).
      eapply wf_erase_global_decl; eauto. rewrite HeqΣex. f_equal. exact Heqkns.
    * sq.
      apply OptimizePropDiscr.trans_env_fresh_global.
      apply fresh_globals_erase_global_decl_rec.
      change decls with (PEnv.declarations
        {| PEnv.universes := univs; PEnv.declarations := decls; PEnv.retroknowledge := retros |}).
      eapply Erasure.abstract_eq_wf in w as [? []].
      apply PCUICWfEnvImpl.wf_fresh_globals; eauto.
      eapply Erasure.wf_pop_decl in X0; trea. eapply X0.
      apply fresh_global_erase_global_decl_rec.
      eapply Erasure.abstract_eq_wf in w as [? []].
      eapply PCUICWfEnvImpl.wf_fresh_globals in X0. now depelim X0.
  - apply IHdecls.
Qed.

Lemma optimize_correct `{EWellformed.EEnvFlags} Σ fgΣ t v :
  ELiftSubst.closed t = true ->
  EGlobalEnv.closed_env (trans_env Σ) = true ->
  EWellformed.wf_glob (trans_env Σ) ->
  @Prelim.Ee.eval default_wcbv_flags (trans_env Σ) t v ->
  @Prelim.Ee.eval
      (EWcbvEval.disable_prop_cases opt_wcbv_flags)
      (trans_env (map (on_snd (remove_match_on_box_decl (EEnvMap.GlobalContextMap.make (trans_env Σ) (OptimizePropDiscr.trans_env_fresh_globals _ fgΣ)))) Σ))
      (EOptimizePropDiscr.remove_match_on_box (EEnvMap.GlobalContextMap.make (trans_env Σ) (OptimizePropDiscr.trans_env_fresh_globals _ fgΣ)) t)
      (EOptimizePropDiscr.remove_match_on_box (EEnvMap.GlobalContextMap.make (trans_env Σ) (OptimizePropDiscr.trans_env_fresh_globals _ fgΣ)) v).
Proof.
  intros cl_t cl_env wfg ev.
  remember (EEnvMap.GlobalContextMap.make _ _) as Σ0.
  assert (trans_env (map (on_snd (remove_match_on_box_decl Σ0)) Σ) =
    EOptimizePropDiscr.remove_match_on_box_env Σ0) as ->.
  { cbn. rewrite /trans_env HeqΣ0 map_map_compose. cbn. rewrite /trans_env.
    rewrite map_map_compose /on_snd. cbn. eapply map_ext.
    intros [[] []]; cbn. destruct c as [[] []] => //. reflexivity.
    do 2 f_equal. rewrite /EOptimizePropDiscr.remove_match_on_box_constant_decl /=.
    now destruct o; cbn. }
  unshelve eapply (EOptimizePropDiscr.remove_match_on_box_correct (fl := default_wcbv_flags) (Σ := Σ0));subst;cbn;eauto.
Qed.


Theorem extract_correct
        (H := EWellformed.all_env_flags)
        (wfl := opt_wcbv_flags)
        (Σ : P.global_env_ext) (wfΣ : ∥wf_ext Σ∥)
        kn ui ind c ui' ignored exΣ :
  axiom_free Σ ->
  welltyped Σ [] (P.tConst kn ui) ->
  Σ p⊢ P.tConst kn ui ⇓ P.tConstruct ind c ui' ->
  (isErasable Σ [] (P.tConstruct ind c ui') -> False) ->
  (forall k, ignored k = false) ->
  extract_pcuic_env
    (pcuic_args extract_within_coq)
    Σ (wf_squash wfΣ) (KernameSet.singleton kn) ignored = Ok exΣ ->
  ∥trans_env exΣ e⊢ E.tConst kn ⇓ E.tConstruct ind c []∥.
Proof.
  intros ax [T wt] ev not_erasable no_ignores ex.
  cbn -[dearg_transform] in *.
  destruct dearg_transform eqn:dt; cbn -[dearg_transform] in *; [|congruence].
  injection ex as ->.
  destruct wfΣ.
  eapply erases_correct with
    (Σ' := trans_env (Erasure.erase_global_decls_deps_recursive (PCUICAst.PCUICEnvironment.declarations Σ)
               (PCUICAst.PCUICEnvironment.universes Σ) _ _
               (KernameSet.singleton kn) ignored)) in ev as (erv&erase_to&[erev]);eauto.
  + depelim erase_to;[|easy].
    constructor.
    eapply dearg_transform_correct; eauto.
    clear dt.
    eapply (@optimize_correct _ _ _ (tConst kn) (tConstruct ind c []));eauto.
    * remember (Erasure.erase_global_decls_deps_recursive _ _ _ _ _ _) as eΣ.
      assert (EWellformed.wf_glob (trans_env eΣ)).
      { subst eΣ. now eapply wf_erase_global_decls_recursive. }
      now apply EWellformed.wellformed_closed_env.
    * eapply wf_erase_global_decls_recursive; auto.
  + now eexists.
  + eapply inversion_Const in wt as (?&?&?&?&?); auto.
    clear dt.
    eapply global_erased_with_deps_erases_deps_tConst; eauto.
    destruct Σ as [Σ0 univ_decls].
    destruct Σ0 as [univs Σ1].
    apply wf_ext_wf in w as w1. cbn.
    eapply erase_global_decls_deps_recursive_correct;eauto.
    * unfold PCUICAst.declared_constant in *.
      cbn.
      intros ? ->%KernameSet.singleton_spec;cbn in *.
      intros eq. set (env := {| PEnv.declarations := Σ1 |}) in *.
      eapply (lookup_global_In_wf _ env) in d; eauto.
    * now apply KernameSet.singleton_spec.
    Unshelve. eapply fresh_globals_erase_global_decl_rec.
      now eapply PCUICWfEnvImpl.wf_fresh_globals.
Qed.

(* Print Assumptions extract_correct. *)

(** There are some assumptions of which almost all are in MetaCoq.
    From this project is only assume_env_wellformed assumption which is
    used to assume that the environments we extract are
    wellformed. MetaCoq's safe checker does not run from within Coq, so
    we cannot type check the environments. However, our environments
    are unquoted directly from Coq's kernel where they are already
    welltyped, so this is justified (and the same assumption is used in
    MetaCoq when they run their erasure).

    The rest of the assumptions are normal MetaCoq assumptions
    (which are justified in Coq Coq Correct!).

    [JMeq.JMeq_eq] leaks from the use of some tactics and probably can be avoided.
 *)
