From Coq Require Import List.
From MetaCoq.Erasure.Typed Require Import ErasureCorrectness.
From MetaCoq.Erasure.Typed Require Import ExAst.
From MetaCoq.Erasure.Typed Require Import Extraction.
From MetaCoq.Erasure.Typed Require Import Optimize.
From MetaCoq.Erasure.Typed Require Import OptimizeCorrectness.
From MetaCoq.Erasure.Typed Require Import ResultMonad.
From MetaCoq.Erasure.Typed Require Import WcbvEvalAux.
From Equations Require Import Equations.
From MetaCoq.Erasure Require Import ErasureCorrectness.
From MetaCoq.Erasure Require Import ErasureFunction.
From MetaCoq.Erasure Require Import EWcbvEval.
From MetaCoq.Erasure Require Import Extract.
From MetaCoq.PCUIC Require Import PCUICAstUtils.
From MetaCoq.PCUIC Require Import PCUICSafeLemmata.
From MetaCoq.PCUIC Require Import PCUICTyping.
From MetaCoq.PCUIC Require Import PCUICInversion.
From MetaCoq.Template Require Import Kernames.
From MetaCoq.Template Require Import MCSquash.

Import ListNotations.

Module P := PCUICAst.
Module E := EAst.

Notation "Σ 'p⊢' s ▷ t" := (PCUICWcbvEval.eval Σ s t) (at level 50, s, t at next level) : type_scope.

Lemma wf_squash {Σ} :
  ∥wf_ext Σ∥ ->
  ∥wf Σ∥.
Proof. intros []. now constructor. Qed.

Lemma global_erased_with_deps_erases_deps_tConst Σ Σer kn cst :
  P.declared_constant Σ kn cst ->
  global_erased_with_deps Σ Σer kn ->
  erases_deps Σ Σer (E.tConst kn).
Proof.
  intros decl glob.
  destruct glob as [(?&?&?&?&?&?)|(?&?&?&?&?)].
  - econstructor; eauto.
  - unfold EGlobalEnv.declared_constant, EGlobalEnv.declared_minductive in *.
    congruence.
Qed.

Module PEnv := PCUICAst.PCUICEnvironment.
Lemma wf_erase_global_decl :
  forall (H : EWellformed.EEnvFlags) (k : kername) (g : PCUICAst.PCUICEnvironment.global_decl)
         (decls : list (kername * PCUICAst.PCUICEnvironment.global_decl))
         (univs : Universes.ContextSet.t) retros w wt (Σex : global_env),
    EWellformed.wf_glob (trans_env Σex) ->
    EWellformed.wf_global_decl
      (trans_env Σex)
      (trans_global_decl
         (Erasure.erase_global_decl
            ({| PEnv.universes := univs; PEnv.declarations := decls; PEnv.retroknowledge := retros |},
              PCUICAst.PCUICLookup.universes_decl_of_decl g)
            w k g wt)) = true.
Proof.
  intros H k g decls univs w wt Σex wf_global.
  unfold Erasure.erase_global_decl.
  destruct g.
  - destruct (Erasure.erase_constant_decl) eqn:Hdecl.
    * unfold Erasure.erase_constant_decl,Erasure.erase_constant_decl_clause_1 in *.
      destruct (Erasure.flag_of_type), conv_ar;try congruence.
      inversion Hdecl;subst;clear Hdecl.
      unfold trans_global_decl,trans_cst.
      cbn.
      unfold MCOption.option_default.
      (* global_erased_with_deps *)
      (* erase_constant_body_correct'' *)
Admitted.


Ltac invert_wf :=
  match goal with
  | [H : wf _ |- _] => sq; inversion H;subst;clear H;cbn in *
  | [H : P.on_global_decls _ _ _ _ (_ :: _) |- _] => inversion H;subst;clear H;cbn in *
  | [H : P.on_global_decls_data _ _ _ _ _ _ _ |- _] => inversion H; subst; clear H; cbn in *
  end.

Lemma wf_erase_global_decls_recursive `{EWellformed.EEnvFlags} :
  forall decls univs retros w seeds (ignored : kername -> bool),
    let Σex :=
      Erasure.erase_global_decls_deps_recursive decls univs retros w seeds ignored in
    EWellformed.wf_glob (trans_env Σex).
Proof.
  intros decls univs retros w seeds ignored ?.
  subst Σex.
  revert seeds.
  induction decls;intros seeds;auto;try constructor.
  simpl.
  destruct a;simpl.
  destruct (KernameSet.mem _ _);cbn.
  - unfold MCProd.test_snd;cbn.
    constructor.
    * unfold trans_env in *;cbn in *.
      apply IHdecls.
    * cbn.
      remember (KernameSet.union _ _) as kns.
      clear Heqkns.
      remember (Erasure.erase_global_decls_deps_recursive decls univs _ _ _ _) as Σex.
      assert (EWellformed.wf_glob (trans_env Σex)) by now subst Σex.
      now apply wf_erase_global_decl.
    * sq.
      apply OptimizePropDiscr.trans_env_fresh_global.
      apply fresh_globals_erase_global_decl_rec.
      change decls with (PEnv.declarations
        {| PEnv.universes := univs; PEnv.declarations := decls; PEnv.retroknowledge := retros |}).
      apply PCUICWfEnvImpl.wf_fresh_globals.
      repeat invert_wf;split;auto;split;auto.
      apply fresh_global_erase_global_decl_rec.
      change decls with (PEnv.declarations
        {| PEnv.universes := univs; PEnv.declarations := decls; PEnv.retroknowledge := retros |}).
      now repeat invert_wf.
  - apply IHdecls.
Qed.

Lemma optimize_correct `{EWellformed.EEnvFlags} Σ fgΣ t v :
  ELiftSubst.closed t = true ->
  EGlobalEnv.closed_env (trans_env Σ) = true ->
  EWellformed.wf_glob (trans_env Σ) ->
  @Prelim.Ee.eval default_wcbv_flags (trans_env Σ) t v ->
  @Prelim.Ee.eval
      (EWcbvEval.disable_prop_cases opt_wcbv_flags)
      (trans_env (OptimizePropDiscr.optimize_env Σ fgΣ))
      (EOptimizePropDiscr.optimize (EEnvMap.GlobalContextMap.make (trans_env Σ) (OptimizePropDiscr.trans_env_fresh_globals _ fgΣ)) t)
      (EOptimizePropDiscr.optimize (EEnvMap.GlobalContextMap.make (trans_env Σ) (OptimizePropDiscr.trans_env_fresh_globals _ fgΣ)) v).
Proof.
  intros cl_t cl_env wfg ev.
  rewrite OptimizePropDiscr.trans_env_optimize_env.
  remember (EEnvMap.GlobalContextMap.make _ _) as Σ0.
  unshelve eapply (EOptimizePropDiscr.optimize_correct (fl := default_wcbv_flags) (Σ := Σ0));subst;cbn;eauto.
Qed.


Theorem extract_correct
        `{EWellformed.EEnvFlags}
        (wfl := opt_wcbv_flags)
        (Σ : P.global_env_ext) (wfΣ : ∥wf_ext Σ∥)
        kn ui ind c ui' ignored exΣ :
  axiom_free Σ ->
  welltyped Σ [] (P.tConst kn ui) ->
  Σ p⊢ P.tConst kn ui ▷ P.tConstruct ind c ui' ->
  (isErasable Σ [] (P.tConstruct ind c ui') -> False) ->
  (forall k, ignored k = false) ->
  extract_pcuic_env
    (pcuic_args extract_within_coq)
    Σ (wf_squash wfΣ) (KernameSet.singleton kn) ignored = Ok exΣ ->
  ∥trans_env exΣ e⊢ E.tConst kn ▷ E.tConstruct ind c []∥.
Proof.
  intros ax [T wt] ev not_erasable no_ignores ex.
  cbn -[dearg_transform] in *.
  destruct dearg_transform eqn:dt; cbn -[dearg_transform] in *; [|congruence].
  injection ex as ->.
  destruct wfΣ.
  eapply erases_correct with (Σ' := trans_env (Erasure.erase_global_decls_deps_recursive (PCUICAst.PCUICEnvironment.declarations Σ)
               (PCUICAst.PCUICEnvironment.universes Σ) _ (wf_squash (sq w))
               (KernameSet.singleton kn) ignored)) in ev as (erv&erase_to&[erev]);eauto.
  + depelim erase_to;[|easy].
    constructor.
    eapply dearg_transform_correct; eauto.
    clear dt.
    eapply (@OptimizePropDiscr.optimize_correct _ default_wcbv_flags _ _ (tConst kn) (tConstruct ind c []));eauto.
    * remember (Erasure.erase_global_decls_deps_recursive _ _ _ _ _ _) as eΣ.
      assert (EWellformed.wf_glob (trans_env eΣ)) by now subst eΣ;eapply wf_erase_global_decls_recursive.
      now apply EWellformed.wellformed_closed_env.
    * eapply wf_erase_global_decls_recursive.
  + eapply inversion_Const in wt as (?&?&?&?&?); auto.
    clear dt.
    eapply global_erased_with_deps_erases_deps_tConst; eauto.
    destruct Σ as [Σ0 univ_decls].
    destruct Σ0 as [univs Σ1].
    apply wf_ext_wf in w as w1.
    eapply erase_global_decls_deps_recursive_correct;eauto.
    * unfold PCUICAst.declared_constant in *.
      now intros ? ->%KernameSet.singleton_spec;cbn in *.
    * now apply KernameSet.singleton_spec.
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
