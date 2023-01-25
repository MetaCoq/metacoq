(** Pass that removes discrimination (matches and projections) on things in Prop.
    This uses MetaCoq's optimization but adapted to run on our environments. *)
From MetaCoq.Erasure.Typed Require Import ExAst.
From MetaCoq.Erasure Require Import EOptimizePropDiscr.

Definition optimize_constant_body Σ cst :=
  {| cst_type := cst_type cst;
     cst_body := option_map (optimize Σ) (cst_body cst) |}.

Definition optimize_decl Σ d :=
  match d with
  | ConstantDecl cst => ConstantDecl (optimize_constant_body Σ cst)
  | _ => d
  end.

Lemma trans_env_fresh_global :
      forall (kn : Kernames.kername) (g : global_env),
        fresh_globals g ->
        fresh_global kn g ->
        EnvMap.EnvMap.fresh_global kn (List.map (fun '(kn0, _, decl) => (kn0, trans_global_decl decl)) g).
Proof.
  intros kn g fg H.
  induction H.
    * constructor.
    * cbn. inversion fg;subst;cbn in *. now constructor.
Qed.

Lemma trans_env_fresh_globals Σ :
  fresh_globals Σ ->
  EnvMap.EnvMap.fresh_globals (trans_env Σ).
Proof.
  intros fg.
  induction fg.
  + constructor.
  + cbn. constructor;auto.
    now apply trans_env_fresh_global.
Qed.

Program Definition optimize_env (Σ : global_env) (fgΣ : fresh_globals Σ) : global_env :=
  List.map (MCProd.on_snd (optimize_decl (EEnvMap.GlobalContextMap.make (trans_env Σ) _))) Σ.
Next Obligation.
  now apply trans_env_fresh_globals.
Qed.

Module Ee := EWcbvEval.

Lemma trans_env_optimize_env Σ fgΣ :
  trans_env (optimize_env Σ fgΣ) =
  EOptimizePropDiscr.optimize_env (EEnvMap.GlobalContextMap.make (trans_env Σ) (trans_env_fresh_globals _ fgΣ)).
Proof.
  unfold trans_env.
  unfold EOptimizePropDiscr.optimize_env.
  unfold optimize_env.
  unfold MCProd.on_snd. cbn.
  rewrite !List.map_map.
  apply List.map_ext.
  intros ((kn&has_deps)&decl).
  cbn.
  f_equal.
  destruct decl; auto.
  cbn.
  now destruct o.
Qed.

Lemma optimize_correct `{EWellformed.EEnvFlags} `{Ee.WcbvFlags} Σ fgΣ t v :
  EWcbvEval.with_constructor_as_block = false ->
  ELiftSubst.closed t = true ->
  EGlobalEnv.closed_env (trans_env Σ) = true ->
  EWellformed.wf_glob (trans_env Σ) ->
  @Prelim.Ee.eval _ (trans_env Σ) t v ->
  @Prelim.Ee.eval
      (EWcbvEval.disable_prop_cases _)
      (trans_env (optimize_env Σ fgΣ))
      (optimize (EEnvMap.GlobalContextMap.make (trans_env Σ) (trans_env_fresh_globals _ fgΣ)) t)
      (optimize (EEnvMap.GlobalContextMap.make (trans_env Σ) (trans_env_fresh_globals _ fgΣ)) v).
Proof.
  intros ? cl_t cl_env wfg ev.
  rewrite trans_env_optimize_env.
  remember (EEnvMap.GlobalContextMap.make _ _) as Σ0.
  unshelve eapply EOptimizePropDiscr.optimize_correct;subst;cbn;eauto.
Qed.
