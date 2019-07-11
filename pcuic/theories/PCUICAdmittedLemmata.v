
Notation "a 'of' A" := (match a : A with _ => a end) (at level 100).

Require PCUIC.PCUICTyping.

Check (@PCUICTyping.on_global_env_impl
     of forall (H : config.checker_flags) (Σ : PCUICAst.global_env)
         (P : PCUICAst.global_env_ext ->
              PCUICAst.context -> PCUICAst.term -> option PCUICAst.term -> Type)
         (Q : PCUICAst.global_env * Universes.universes_decl ->
              PCUICAst.context -> PCUICAst.term -> option PCUICAst.term -> Type),
       (forall (Σ0 : PCUICAst.global_env * Universes.universes_decl)
          (Γ : PCUICAst.context) (t : PCUICAst.term) (T : option PCUICAst.term),
        PCUICTyping.on_global_env P (fst Σ0) -> P Σ0 Γ t T -> Q Σ0 Γ t T) ->
       PCUICTyping.on_global_env P Σ -> PCUICTyping.on_global_env Q Σ).

Require PCUIC.PCUICWeakeningEnv.

Check (@PCUICWeakeningEnv.global_ext_constraints_app
     of forall (Σ : PCUICAst.global_env) (Σ' : list PCUICAst.global_decl)
         (φ : Universes.universes_decl),
       Universes.ConstraintSet.Subset (PCUICTyping.global_ext_constraints (Σ, φ))
                                      (PCUICTyping.global_ext_constraints ((Σ' ++ Σ)%list, φ))).

Check (@PCUICWeakeningEnv.leq_universe_subset
     of forall (cf : config.checker_flags) (ctrs ctrs' : Universes.ConstraintSet.t)
         (t u : Universes.universe),
       Universes.ConstraintSet.Subset ctrs ctrs' ->
       Universes.leq_universe ctrs t u -> Universes.leq_universe ctrs' t u).

Check (@PCUICWeakeningEnv.leq_term_subset
     of forall (cf : config.checker_flags) (ctrs ctrs' : Universes.ConstraintSet.t)
         (t u : PCUICAst.term),
       Universes.ConstraintSet.Subset ctrs ctrs' ->
       PCUICTyping.leq_term ctrs t u -> PCUICTyping.leq_term ctrs' t u).

Check (@PCUICWeakeningEnv.weakening_env_global_ext_levels
     of forall (Σ Σ' : PCUICAst.global_env) (φ : Universes.universes_decl),
       PCUICWeakeningEnv.extends Σ Σ' ->
       forall l : Universes.LevelSet.elt,
       Universes.LevelSet.In l (PCUICTyping.global_ext_levels (Σ, φ)) ->
       Universes.LevelSet.In l (PCUICTyping.global_ext_levels (Σ', φ))).

Check (@PCUICWeakeningEnv.weakening_env_global_ext_constraints
     of forall (Σ Σ' : PCUICAst.global_env) (φ : Universes.universes_decl),
       PCUICWeakeningEnv.extends Σ Σ' ->
       Universes.ConstraintSet.Subset (PCUICTyping.global_ext_constraints (Σ, φ))
         (PCUICTyping.global_ext_constraints (Σ', φ))).

Check (@PCUICWeakeningEnv.valid_subset
     of forall (cf : config.checker_flags) (φ φ' : Universes.ConstraintSet.t)
         (ctrs : Universes.constraints),
       Universes.ConstraintSet.Subset φ φ' ->
       Universes.valid_constraints φ ctrs -> Universes.valid_constraints φ' ctrs).

Check (@PCUICWeakeningEnv.check_correct_arity_subset
     of forall (cf : config.checker_flags) (φ φ' : Universes.ConstraintSet.t)
         (decl : PCUICAst.one_inductive_body) (ind : BasicAst.inductive)
         (u : Universes.universe_instance) (ctx : list PCUICAst.context_decl)
         (pars : list PCUICAst.term) (pctx : PCUICAst.context),
       Universes.ConstraintSet.Subset φ φ' ->
       PCUICTyping.check_correct_arity φ decl ind u ctx pars pctx ->
       PCUICTyping.check_correct_arity φ' decl ind u ctx pars pctx).

Require PCUIC.PCUICUnivSubstitution.

Check (@PCUICUnivSubstitution.fix_context_subst_instance
     of forall (mfix : list (BasicAst.def PCUICAst.term)) (u : Universes.universe_instance),
       PCUICLiftSubst.fix_context
         (List.map
            (PCUICAstUtils.map_def (PCUICUnivSubst.subst_instance_constr u)
               (PCUICUnivSubst.subst_instance_constr u)) mfix) =
       List.map (PCUICAstUtils.map_decl (PCUICUnivSubst.subst_instance_constr u))
                (PCUICLiftSubst.fix_context mfix)).

Check (@PCUICUnivSubstitution.isWfArity_subst_instance
     of forall (cf : config.checker_flags)
         (Σ : PCUICAst.global_env * Universes.universes_decl)
         (Γ : PCUICAst.context) (B : PCUICAst.term),
       PCUICTyping.isWfArity PCUICTyping.typing Σ Γ B ->
       forall (u : Universes.universe_instance) (univs : Universes.universes_decl),
       PCUICTyping.consistent_instance_ext (fst Σ, univs) (snd Σ) u ->
       PCUICTyping.isWfArity PCUICTyping.typing (fst Σ, univs)
         (PCUICUnivSubst.subst_instance_context u Γ)
         (PCUICUnivSubst.subst_instance_constr u B)).

Check (@PCUICUnivSubstitution.subst_instance_constr_two
     of forall (u1 u2 : Universes.universe_instance) (t : PCUICAst.term),
       PCUICUnivSubst.subst_instance_constr u1 (PCUICUnivSubst.subst_instance_constr u2 t) =
       PCUICUnivSubst.subst_instance_constr (UnivSubst.subst_instance_instance u1 u2) t).

Check (@PCUICUnivSubstitution.consistent_ext_trans
     of forall (cf : config.checker_flags)
         (Σ : PCUICAst.global_env * Universes.universes_decl)
         (u : Universes.universe_instance) (U : Universes.universes_decl),
       PCUICTyping.consistent_instance_ext Σ U u ->
       forall (u0 : Universes.universe_instance) (univs : Universes.universes_decl),
       PCUICTyping.consistent_instance_ext (fst Σ, univs) (snd Σ) u0 ->
       PCUICTyping.consistent_instance_ext (fst Σ, univs) U
         (UnivSubst.subst_instance_instance u0 u)).

Check (@PCUICUnivSubstitution.subst_instance_univ_super
     of forall (l : Universes.Level.t) (u : Universes.universe_instance),
       UnivSubst.subst_instance_univ u (Universes.Universe.super l) =
       Universes.Universe.super (UnivSubst.subst_instance_level u l)).

Check (@PCUICUnivSubstitution.subst_instance_univ_make
     of forall (l : Universes.Level.t) (u : Universes.universe_instance),
       UnivSubst.subst_instance_univ u (Universes.Universe.make l) =
       Universes.Universe.make (UnivSubst.subst_instance_level u l)).

Check (@PCUICUnivSubstitution.LevelIn_subst_instance
     of forall (cf : config.checker_flags)
         (Σ : PCUICAst.global_env * Universes.universes_decl)
         (l : Universes.Level.t),
       Universes.LevelSet.In l (PCUICTyping.global_ext_levels Σ) ->
       forall (u : Universes.universe_instance) (univs : Universes.universes_decl),
       PCUICTyping.consistent_instance_ext (fst Σ, univs) (snd Σ) u ->
       Universes.LevelSet.In (UnivSubst.subst_instance_level u l)
                             (PCUICTyping.global_ext_levels (fst Σ, univs))).

Check (@PCUICUnivSubstitution.product_subst_instance
     of forall (u : Universes.universe_instance) (s1 s2 : Universes.Universe.t),
       UnivSubst.subst_instance_univ u (Universes.Universe.sort_of_product s1 s2) =
       Universes.Universe.sort_of_product (UnivSubst.subst_instance_univ u s1)
                                          (UnivSubst.subst_instance_univ u s2)).

Check (@PCUICUnivSubstitution.fix_subst_subst_instance
     of forall (u : Universes.universe_instance) (mfix : BasicAst.mfixpoint PCUICAst.term),
       PCUICTyping.fix_subst
         (List.map
            (PCUICAstUtils.map_def (PCUICUnivSubst.subst_instance_constr u)
               (PCUICUnivSubst.subst_instance_constr u)) mfix) =
       List.map (PCUICUnivSubst.subst_instance_constr u) (PCUICTyping.fix_subst mfix)).

Check (PCUICUnivSubstitution.cofix_subst_subst_instance
     of forall (u : Universes.universe_instance) (mfix : BasicAst.mfixpoint PCUICAst.term),
       PCUICTyping.cofix_subst
         (List.map
            (PCUICAstUtils.map_def (PCUICUnivSubst.subst_instance_constr u)
               (PCUICUnivSubst.subst_instance_constr u)) mfix) =
       List.map (PCUICUnivSubst.subst_instance_constr u) (PCUICTyping.cofix_subst mfix)).

Check (@PCUICUnivSubstitution.isConstruct_app_subst_instance
     of forall (u : Universes.universe_instance) (t : PCUICAst.term),
       PCUICTyping.isConstruct_app (PCUICUnivSubst.subst_instance_constr u t) =
       PCUICTyping.isConstruct_app t).

Check (@PCUICUnivSubstitution.leq_term_subst_instance
     of forall (cf : config.checker_flags) (Σ : PCUICAst.global_env_ext)
         (u : Universes.universe_instance) (univs : Universes.universes_decl),
       PCUICTyping.consistent_instance_ext (fst Σ, univs) (snd Σ) u ->
       forall t u0 : PCUICAst.term,
       PCUICTyping.leq_term (PCUICTyping.global_ext_constraints Σ) t u0 ->
       PCUICTyping.leq_term (PCUICTyping.global_ext_constraints (fst Σ, univs))
         (PCUICUnivSubst.subst_instance_constr u t)
         (PCUICUnivSubst.subst_instance_constr u u0)).

Check (@PCUICUnivSubstitution.typing_subst_instance
     of forall (cf : config.checker_flags) (Σ : PCUICAst.global_env_ext),
       PCUICTyping.wf (PCUICAstUtils.fst_ctx Σ) ->
       forall Γ : PCUICAst.context,
       PCUICTyping.All_local_env (PCUICTyping.lift_typing PCUICTyping.typing Σ) Γ ->
       forall t T : PCUICAst.term,
       PCUICTyping.typing Σ Γ t T ->
       forall (u : Universes.universe_instance) (univs : Universes.universes_decl),
       PCUICTyping.consistent_instance_ext (fst Σ, univs) (snd Σ) u ->
       PCUICTyping.All_local_env
         (PCUICTyping.lift_typing PCUICTyping.typing (fst Σ, univs))
         (PCUICUnivSubst.subst_instance_context u Γ) ->
       PCUICTyping.typing (fst Σ, univs) (PCUICUnivSubst.subst_instance_context u Γ)
         (PCUICUnivSubst.subst_instance_constr u t)
         (PCUICUnivSubst.subst_instance_constr u T)).

Check (@PCUICReduction.red_fix_one_body
     of forall (Σ : PCUICAst.global_env) (Γ : PCUICAst.context)
         (mfix : BasicAst.mfixpoint PCUICAst.term) (idx : nat)
         (mfix' : list (BasicAst.def PCUICAst.term)),
       utils.OnOne2
         (fun x y : BasicAst.def PCUICAst.term =>
          (PCUICTyping.red Σ
             (PCUICAstUtils.app_context Γ (PCUICLiftSubst.fix_context mfix))
             (BasicAst.dbody x) (BasicAst.dbody y) *
           ((BasicAst.dname x, BasicAst.dtype x, BasicAst.rarg x) =
            (BasicAst.dname y, BasicAst.dtype y, BasicAst.rarg y)))%type) mfix mfix' ->
       PCUICTyping.red Σ Γ (PCUICAst.tFix mfix idx) (PCUICAst.tFix mfix' idx)).

Check (@PCUICReduction.red_fix_body
     of forall (Σ : PCUICAst.global_env) (Γ : PCUICAst.context)
         (mfix : BasicAst.mfixpoint PCUICAst.term) (idx : nat)
         (mfix' : list (BasicAst.def PCUICAst.term)),
       utils.All2
         (fun x y : BasicAst.def PCUICAst.term =>
          (PCUICTyping.red Σ
             (PCUICAstUtils.app_context Γ (PCUICLiftSubst.fix_context mfix))
             (BasicAst.dbody x) (BasicAst.dbody y) *
           ((BasicAst.dname x, BasicAst.dtype x, BasicAst.rarg x) =
            (BasicAst.dname y, BasicAst.dtype y, BasicAst.rarg y)))%type) mfix mfix' ->
       PCUICTyping.red Σ Γ (PCUICAst.tFix mfix idx) (PCUICAst.tFix mfix' idx)).

Check (@PCUICReduction.red_fix_congr
     of forall (Σ : PCUICAst.global_env) (Γ : PCUICAst.context)
         (mfix : BasicAst.mfixpoint PCUICAst.term)
         (mfix' : list (BasicAst.def PCUICAst.term)) (idx : nat),
       utils.All2
         (fun d0 d1 : BasicAst.def PCUICAst.term =>
          (PCUICTyping.red Σ Γ (BasicAst.dtype d0) (BasicAst.dtype d1) *
           PCUICTyping.red Σ
             (PCUICAstUtils.app_context Γ (PCUICLiftSubst.fix_context mfix))
             (BasicAst.dbody d0) (BasicAst.dbody d1))%type) mfix mfix' ->
       PCUICTyping.red Σ Γ (PCUICAst.tFix mfix idx) (PCUICAst.tFix mfix' idx)).

Check (@PCUICReduction.red_cofix_congr
     of forall (Σ : PCUICAst.global_env) (Γ : PCUICAst.context)
         (mfix0 : BasicAst.mfixpoint PCUICAst.term)
         (mfix1 : list (BasicAst.def PCUICAst.term)) (idx : nat),
       utils.All2
         (fun d0 d1 : BasicAst.def PCUICAst.term =>
          (PCUICTyping.red Σ Γ (BasicAst.dtype d0) (BasicAst.dtype d1) *
           PCUICTyping.red Σ
             (PCUICAstUtils.app_context Γ (PCUICLiftSubst.fix_context mfix0))
             (BasicAst.dbody d0) (BasicAst.dbody d1))%type) mfix0 mfix1 ->
       PCUICTyping.red Σ Γ (PCUICAst.tCoFix mfix0 idx) (PCUICAst.tCoFix mfix1 idx)).

Require PCUICCumulativity.

Check (@PCUICCumulativity.leq_term_antisym
     of forall (cf : config.checker_flags) (Σ : Universes.constraints)
         (t u : PCUICAst.term),
       PCUICTyping.leq_term Σ t u ->
       PCUICTyping.leq_term Σ u t -> PCUICTyping.eq_term Σ t u).

Check (@PCUICCumulativity.cumul_conv_alt
     of forall (cf : config.checker_flags) (Σ : PCUICAst.global_env_ext)
         (Γ : PCUICAst.context) (t u : PCUICAst.term),
       PCUICTyping.cumul Σ Γ t u ->
       PCUICTyping.cumul Σ Γ u t -> PCUICCumulativity.conv_alt Σ Γ t u).

Check (@PCUICCumulativity.congr_cumul_prod
     of forall (H : config.checker_flags) (Σ : PCUICAst.global_env_ext)
         (Γ : PCUICAst.context) (na na' : BasicAst.name) (M1 M2 N1 N2 : PCUICAst.term),
       PCUICTyping.conv Σ Γ M1 N1 ->
       PCUICTyping.cumul Σ (PCUICAst.snoc Γ (PCUICAst.vass na M1)) M2 N2 ->
       PCUICTyping.cumul Σ Γ (PCUICAst.tProd na M1 M2) (PCUICAst.tProd na' N1 N2)).

Require PCUICValidity.

Check (@PCUICValidity.isWfArity_or_Type_subst_instance
     of forall (cf : config.checker_flags) (Σ : PCUICAst.global_env_ext)
         (Γ : PCUICAst.context) (u : list Universes.Level.t)
         (univs : Universes.universes_decl) (ty : PCUICAst.term),
       PCUICTyping.All_local_env (PCUICTyping.lift_typing PCUICTyping.typing Σ) Γ ->
       PCUICTyping.consistent_instance_ext Σ univs u ->
       PCUICGeneration.isWfArity_or_Type (fst Σ, univs) nil ty ->
       PCUICGeneration.isWfArity_or_Type Σ Γ (PCUICUnivSubst.subst_instance_constr u ty)).

Check (@PCUICValidity.validity
     of forall cf : config.checker_flags,
       PCUICTyping.env_prop
         (fun (Σ : PCUICAst.global_env_ext) (Γ : PCUICAst.context) (_ T : PCUICAst.term)
          => PCUICGeneration.isWfArity_or_Type Σ Γ T)).

Require PCUICPrincipality.

Check (@PCUICPrincipality.invert_red_prod
     of forall (cf : config.checker_flags) (Σ : PCUICAst.global_env_ext),
       PCUICTyping.wf (PCUICAstUtils.fst_ctx Σ) ->
       forall (Γ : PCUICAst.context) (na : BasicAst.name) (A B v : PCUICAst.term),
       PCUICTyping.red (PCUICAstUtils.fst_ctx Σ) Γ (PCUICAst.tProd na A B) v ->
       {A' : PCUICAst.term &
       {B' : PCUICAst.term &
       ((v = PCUICAst.tProd na A' B') * PCUICTyping.red (PCUICAstUtils.fst_ctx Σ) Γ A A' *
        PCUICTyping.red (PCUICAstUtils.fst_ctx Σ) (PCUICAst.vass na A :: Γ)%list B B')%type}}).

Check (@PCUICPrincipality.invert_cumul_arity_r
     of forall (cf : config.checker_flags) (Σ : PCUICAst.global_env_ext),
       PCUICTyping.wf (PCUICAstUtils.fst_ctx Σ) ->
       forall (Γ : PCUICAst.context) (C T : PCUICAst.term),
       PCUICTyping.All_local_env (PCUICTyping.lift_typing PCUICTyping.typing Σ) Γ ->
       PCUICTyping.isArity T ->
       PCUICTyping.cumul Σ Γ C T ->
       PCUICPrincipality.Is_conv_to_Arity (PCUICAstUtils.fst_ctx Σ) Γ C).

Check (@PCUICPrincipality.invert_cumul_arity_l
     of forall (cf : config.checker_flags) (Σ : PCUICAst.global_env_ext),
       PCUICTyping.wf (PCUICAstUtils.fst_ctx Σ) ->
       forall (Γ : PCUICAst.context) (C T : PCUICAst.term),
       PCUICTyping.All_local_env (PCUICTyping.lift_typing PCUICTyping.typing Σ) Γ ->
       PCUICTyping.isArity C ->
       PCUICTyping.cumul Σ Γ C T ->
       PCUICPrincipality.Is_conv_to_Arity (PCUICAstUtils.fst_ctx Σ) Γ T).

Check (@PCUICPrincipality.invert_red_letin
     of forall (cf : config.checker_flags) (Σ : PCUICAst.global_env_ext),
       PCUICTyping.wf (PCUICAstUtils.fst_ctx Σ) ->
       forall (Γ : PCUICAst.context) (C : PCUICAst.term) (na : BasicAst.name)
         (d ty b : PCUICAst.term),
       PCUICTyping.red (fst Σ) Γ (PCUICAst.tLetIn na d ty b) C ->
       {na' : BasicAst.name &
       {d' : PCUICAst.term &
       {ty' : PCUICAst.term &
       {b' : PCUICAst.term &
       (PCUICTyping.red (fst Σ) Γ C (PCUICAst.tLetIn na' d' ty' b') *
        PCUICTyping.conv Σ Γ d d' * PCUICTyping.conv Σ Γ ty ty' *
        PCUICTyping.cumul Σ (PCUICAst.snoc Γ (PCUICAst.vdef na d ty)) b b')%type}}}} +
       PCUICTyping.red (fst Σ) Γ (PCUICLiftSubst.subst1 d 0 b) C).

Check (@PCUICPrincipality.invert_cumul_letin_l
     of forall (cf : config.checker_flags) (Σ : PCUICAst.global_env_ext),
       PCUICTyping.wf (PCUICAstUtils.fst_ctx Σ) ->
       forall (Γ : PCUICAst.context) (C : PCUICAst.term) (na : BasicAst.name)
         (d ty b : PCUICAst.term),
       PCUICTyping.cumul Σ Γ (PCUICAst.tLetIn na d ty b) C ->
       PCUICTyping.cumul Σ Γ (PCUICLiftSubst.subst1 d 0 b) C).

Check (@PCUICPrincipality.leq_universe_product_mon
     of forall (cf : config.checker_flags) (Σ : PCUICAst.global_env_ext),
       PCUICTyping.wf (PCUICAstUtils.fst_ctx Σ) ->
       forall u u' v v' : Universes.universe,
       Universes.leq_universe (PCUICTyping.global_ext_constraints Σ) u u' ->
       Universes.leq_universe (PCUICTyping.global_ext_constraints Σ) v v' ->
       Universes.leq_universe (PCUICTyping.global_ext_constraints Σ)
         (Universes.Universe.sort_of_product u v)
         (Universes.Universe.sort_of_product u' v')).

Check (@PCUICPrincipality.isWfArity_red
     of forall (cf : config.checker_flags) (Σ : PCUICAst.global_env_ext),
       PCUICTyping.wf (PCUICAstUtils.fst_ctx Σ) ->
       forall (Γ : PCUICAst.context) (x t : PCUICAst.term),
       PCUICTyping.isWfArity PCUICTyping.typing Σ Γ x ->
       PCUICTyping.red (PCUICAstUtils.fst_ctx Σ) Γ x t ->
       PCUICTyping.isWfArity PCUICTyping.typing Σ Γ t).

Check (@PCUICPrincipality.principal_typing
     of forall (cf : config.checker_flags) (Σ : PCUICAst.global_env_ext),
       PCUICTyping.wf (PCUICAstUtils.fst_ctx Σ) ->
       forall (Γ : PCUICAst.context) (u A B : PCUICAst.term),
       PCUICTyping.typing Σ Γ u A ->
       PCUICTyping.typing Σ Γ u B ->
       {C : PCUICAst.term &
       (PCUICTyping.cumul Σ Γ C A *
        (PCUICTyping.cumul Σ Γ C B * PCUICTyping.typing Σ Γ u C))%type}).

Require PCUICSR.

Check (@PCUICSR.eq_univ_substu
     of forall (cf : config.checker_flags) (Σ : PCUICAst.global_env_ext),
       PCUICTyping.wf (PCUICAstUtils.fst_ctx Σ) ->
       forall φ : Universes.constraints,
         PCUICEquality.SubstUnivPreserving (Universes.eq_universe φ)).

Check (@PCUICSR.leq_univ_substu
     of forall (cf : config.checker_flags) (Σ : PCUICAst.global_env_ext),
       PCUICTyping.wf (PCUICAstUtils.fst_ctx Σ) ->
       forall φ : Universes.constraints,
         PCUICEquality.SubstUnivPreserving (Universes.leq_universe φ)).

Check (@PCUICSR.conv_isWfArity_or_Type
     of forall (cf : config.checker_flags) (Σ : PCUICAst.global_env_ext),
       PCUICTyping.wf (PCUICAstUtils.fst_ctx Σ) ->
       forall (Γ Γ' : PCUICAst.context) (T U : PCUICAst.term),
       PCUICSR.context_relation (PCUICSR.conv_decls Σ) Γ' Γ ->
       PCUICTyping.conv Σ Γ T U ->
       PCUICGeneration.isWfArity_or_Type Σ Γ T -> PCUICGeneration.isWfArity_or_Type Σ Γ' U).

Check (@PCUICSR.conv_context_trans
     of forall (cf : config.checker_flags)
         (Σ : PCUICAst.global_env * Universes.universes_decl),
       PCUICTyping.wf (fst Σ) ->
       CRelationClasses.Transitive
         (fun Γ Γ' : PCUICAst.context =>
            PCUICSR.context_relation (PCUICSR.conv_decls Σ) Γ Γ')).

Check (@PCUICSR.context_conversion
     of forall cf : config.checker_flags,
       PCUICTyping.env_prop
         (fun (Σ : PCUICAst.global_env_ext) (Γ : PCUICAst.context) (t T : PCUICAst.term)
          =>
          forall Γ' : PCUICAst.context,
          PCUICSR.context_relation (PCUICSR.conv_decls Σ) Γ Γ' ->
          PCUICTyping.typing Σ Γ' t T)).

Check (@PCUICSR.cumul_Prod_inv
     of forall (cf : config.checker_flags)
         (Σ : PCUICAst.global_env * Universes.universes_decl)
         (Γ : PCUICAst.context) (na na' : BasicAst.name) (A B A' B' : PCUICAst.term),
       PCUICTyping.wf (fst Σ) ->
       PCUICTyping.All_local_env (PCUICTyping.lift_typing PCUICTyping.typing Σ) Γ ->
       PCUICTyping.cumul Σ Γ (PCUICAst.tProd na A B) (PCUICAst.tProd na' A' B') ->
       PCUICTyping.conv Σ Γ A A' *
       PCUICTyping.cumul Σ (PCUICAst.snoc Γ (PCUICAst.vass na' A')) B B').

Check (@PCUICSR.type_mkApps_inv
     of forall (cf : config.checker_flags) (Σ : PCUICAst.global_env_ext)
         (Γ : PCUICAst.context) (f : PCUICAst.term) (u : list PCUICAst.term)
         (T : PCUICAst.term),
       PCUICTyping.wf (PCUICAstUtils.fst_ctx Σ) ->
       PCUICTyping.typing Σ Γ (PCUICAst.mkApps f u) T ->
       {T' : PCUICAst.term &
       {U : PCUICAst.term &
       (PCUICTyping.typing Σ Γ f T' * PCUICGeneration.typing_spine Σ Γ T' u U *
        PCUICTyping.cumul Σ Γ U T)%type}}).

Check (@PCUICSR.sr_red1
     of forall cf : config.checker_flags, PCUICTyping.env_prop PCUICSR.SR_red1).

Require PCUICWcbvEval.

Check (PCUICWcbvEval.eval_closed
     of forall (Σ : PCUICAst.global_env) (Γ : PCUICAst.context)
         (n : nat) (t u : PCUICAst.term),
       PCUICLiftSubst.closedn n t = true ->
       PCUICWcbvEval.eval Σ Γ t u -> PCUICLiftSubst.closedn n u = true).

Require PCUICRetyping.

Check (@PCUICRetyping.type_of_sound
     of forall cf : config.checker_flags,
       utils.Fuel ->
       forall (Σ : PCUICAst.global_env_ext) (Γ : PCUICAst.context) (t A B : PCUICAst.term),
       PCUICTyping.typing Σ Γ t A ->
       PCUICRetyping.type_of Σ Γ t = PCUICChecker.Checked B ->
       PCUICTyping.typing Σ Γ t B * PCUICTyping.cumul Σ Γ B A).

Require PCUICElimination.

Check (@PCUICElimination.elim_restriction_works_kelim1
     of forall (cf : config.checker_flags) (Σ : PCUICAst.global_env_ext)
         (Γ : PCUICAst.context) (T : PCUICAst.term) (ind : BasicAst.inductive)
         (npar : nat) (p c : PCUICAst.term) (brs : list (nat * PCUICAst.term))
         (mind : PCUICAst.mutual_inductive_body) (idecl : PCUICAst.one_inductive_body),
       PCUICTyping.wf (PCUICAstUtils.fst_ctx Σ) ->
       PCUICTyping.declared_inductive (fst Σ) mind ind idecl ->
       PCUICTyping.typing Σ Γ (PCUICAst.tCase (ind, npar) p c brs) T ->
       (PCUICElimination.Is_proof Σ Γ (PCUICAst.tCase (ind, npar) p c brs) -> False) ->
       List.In Universes.InType (PCUICAst.ind_kelim idecl)).

Check (@PCUICElimination.elim_restriction_works_kelim2
     of forall (cf : config.checker_flags) (Σ : PCUICAst.global_env_ext)
         (ind : BasicAst.inductive) (mind : PCUICAst.mutual_inductive_body)
         (idecl : PCUICAst.one_inductive_body),
       PCUICTyping.wf (PCUICAstUtils.fst_ctx Σ) ->
       PCUICTyping.declared_inductive (fst Σ) mind ind idecl ->
       List.In Universes.InType (PCUICAst.ind_kelim idecl) ->
       PCUICElimination.Informative Σ ind).

Check (@PCUICElimination.tCase_length_branch_inv
     of forall (cf : config.checker_flags) (Σ : PCUICAst.global_env_ext)
         (Γ : PCUICAst.context) (ind : BasicAst.inductive) (npar : nat)
         (p : PCUICAst.term) (n : nat) (u : Universes.universe_instance)
         (args : list PCUICAst.term) (brs : list (nat * PCUICAst.term))
         (T : PCUICAst.term) (m : nat) (t : PCUICAst.term),
       PCUICTyping.wf (PCUICAstUtils.fst_ctx Σ) ->
       PCUICTyping.typing Σ Γ
         (PCUICAst.tCase (ind, npar) p
            (PCUICAst.mkApps (PCUICAst.tConstruct ind n u) args) brs) T ->
       List.nth_error brs n = Some (m, t) -> length args = npar + m).

Check (@PCUICElimination.cumul_prop1
     of forall cf : config.checker_flags,
       config.prop_sub_type = false ->
       forall (Σ : PCUICAst.global_env_ext) (Γ : PCUICAst.context)
         (A B : PCUICAst.term) (u : Universes.Universe.t),
       PCUICTyping.wf (PCUICAstUtils.fst_ctx Σ) ->
       is_true (Universes.is_prop_sort u) ->
       PCUICTyping.typing Σ Γ B (PCUICAst.tSort u) ->
       PCUICTyping.cumul Σ Γ A B -> PCUICTyping.typing Σ Γ A (PCUICAst.tSort u)).

Check (@PCUICElimination.cumul_prop2
     of forall cf : config.checker_flags,
       config.prop_sub_type = false ->
       forall (Σ : PCUICAst.global_env_ext) (Γ : PCUICAst.context)
         (A B : PCUICAst.term) (u : Universes.Universe.t),
       PCUICTyping.wf (PCUICAstUtils.fst_ctx Σ) ->
       is_true (Universes.is_prop_sort u) ->
       PCUICTyping.cumul Σ Γ A B ->
       PCUICTyping.typing Σ Γ A (PCUICAst.tSort u) ->
       PCUICTyping.typing Σ Γ B (PCUICAst.tSort u)).

Check (@PCUICElimination.leq_universe_prop
     of forall cf : config.checker_flags,
       config.prop_sub_type = false ->
       forall (Σ : PCUICAst.global_env_ext) (u1 u2 : Universes.universe),
       PCUICTyping.wf (PCUICAstUtils.fst_ctx Σ) ->
       Universes.leq_universe (PCUICTyping.global_ext_constraints Σ) u1 u2 ->
       is_true (Universes.is_prop_sort u1) \/ is_true (Universes.is_prop_sort u2) ->
       is_true (Universes.is_prop_sort u1) /\ is_true (Universes.is_prop_sort u2)).

Require PCUICSafeLemmata.

Check (@PCUICSafeLemmata.context_conversion
     of forall cf : config.checker_flags,
       PCUICNormal.RedFlags.t ->
       forall (Σ : PCUICAst.global_env_ext) (Γ : PCUICAst.context)
         (t T : PCUICAst.term) (Γ' : PCUICAst.context),
       PCUICTyping.typing Σ Γ t T ->
       PCUICSR.context_relation (PCUICSR.conv_decls Σ) Γ Γ' -> PCUICTyping.typing Σ Γ' t T).

Check (@PCUICSafeLemmata.type_rename
     of forall cf : config.checker_flags,
       PCUICNormal.RedFlags.t ->
       forall (Σ : PCUICAst.global_env * Universes.universes_decl)
         (Γ : PCUICAst.context) (u v A : PCUICAst.term),
       PCUICTyping.wf (fst Σ) ->
       PCUICTyping.typing Σ Γ u A ->
       PCUICTyping.eq_term_upto_univ eq eq u v -> PCUICTyping.typing Σ Γ v A).

Check (@PCUICSafeLemmata.wf_nlg
     of forall cf : config.checker_flags,
       PCUICNormal.RedFlags.t ->
       forall Σ : PCUICAst.global_env_ext,
       utils.squash (PCUICTyping.wf (PCUICAstUtils.fst_ctx Σ)) ->
       utils.squash (PCUICTyping.wf (PCUICAstUtils.fst_ctx (PCUICNameless.nlg Σ)))).

Check (@PCUICSafeLemmata.welltyped_nlg
     of forall cf : config.checker_flags,
       PCUICNormal.RedFlags.t ->
       forall Σ : PCUICAst.global_env_ext,
       utils.squash (PCUICTyping.wf (PCUICAstUtils.fst_ctx Σ)) ->
       forall (Γ : PCUICAst.context) (t : PCUICAst.term),
       PCUICSafeLemmata.welltyped Σ Γ t ->
       PCUICSafeLemmata.welltyped (PCUICNameless.nlg Σ) Γ t).

Check (@PCUICSafeLemmata.wellformed_nlg
     of forall cf : config.checker_flags,
       PCUICNormal.RedFlags.t ->
       forall Σ : PCUICAst.global_env_ext,
       utils.squash (PCUICTyping.wf (PCUICAstUtils.fst_ctx Σ)) ->
       forall (Γ : PCUICAst.context) (t : PCUICAst.term),
       PCUICSafeLemmata.wellformed Σ Γ t ->
       PCUICSafeLemmata.wellformed (PCUICNameless.nlg Σ) Γ t).

Check (@PCUICSafeLemmata.wellformed_rename
     of forall cf : config.checker_flags,
       PCUICNormal.RedFlags.t ->
       forall Σ : PCUICAst.global_env_ext,
       utils.squash (PCUICTyping.wf (PCUICAstUtils.fst_ctx Σ)) ->
       forall (Γ : PCUICAst.context) (u v : PCUICAst.term),
       PCUICSafeLemmata.wellformed Σ Γ u ->
       PCUICTyping.eq_term_upto_univ eq eq u v -> PCUICSafeLemmata.wellformed Σ Γ v).

Check (@PCUICSafeLemmata.cored_nl
     of forall cf : config.checker_flags,
       PCUICNormal.RedFlags.t ->
       forall Σ : PCUICAst.global_env_ext,
       utils.squash (PCUICTyping.wf (PCUICAstUtils.fst_ctx Σ)) ->
       forall (Γ : PCUICAst.context) (u v : PCUICAst.term),
       PCUICSafeLemmata.cored (PCUICAstUtils.fst_ctx Σ) Γ u v ->
       PCUICSafeLemmata.cored (PCUICAstUtils.fst_ctx (PCUICNameless.nlg Σ))
         (PCUICNameless.nlctx Γ) (PCUICNameless.nl u) (PCUICNameless.nl v)).

Check (@PCUICSafeLemmata.red_nl
     of forall cf : config.checker_flags,
       PCUICNormal.RedFlags.t ->
       forall Σ : PCUICAst.global_env_ext,
       utils.squash (PCUICTyping.wf (PCUICAstUtils.fst_ctx Σ)) ->
       forall (Γ : PCUICAst.context) (u v : PCUICAst.term),
       PCUICTyping.red (PCUICAstUtils.fst_ctx Σ) Γ u v ->
       PCUICTyping.red (PCUICAstUtils.fst_ctx (PCUICNameless.nlg Σ))
         (PCUICNameless.nlctx Γ) (PCUICNameless.nl u) (PCUICNameless.nl v)).

Check (@PCUICSafeLemmata.wellformed_it_mkLambda_or_LetIn
     of forall cf : config.checker_flags,
       PCUICNormal.RedFlags.t ->
       forall Σ : PCUICAst.global_env_ext,
       utils.squash (PCUICTyping.wf (PCUICAstUtils.fst_ctx Σ)) ->
       forall (Γ Δ : PCUICAst.context) (t : PCUICAst.term),
       PCUICSafeLemmata.wellformed Σ Γ (PCUICAstUtils.it_mkLambda_or_LetIn Δ t) ->
       PCUICSafeLemmata.wellformed Σ (PCUICAstUtils.app_context Γ Δ) t).

Check (@PCUICSafeLemmata.it_mkLambda_or_LetIn_wellformed
     of forall cf : config.checker_flags,
       PCUICNormal.RedFlags.t ->
       forall Σ : PCUICAst.global_env_ext,
       utils.squash (PCUICTyping.wf (PCUICAstUtils.fst_ctx Σ)) ->
       forall (Γ Δ : PCUICAst.context) (t : PCUICAst.term),
       PCUICSafeLemmata.wellformed Σ (PCUICAstUtils.app_context Γ Δ) t ->
       PCUICSafeLemmata.wellformed Σ Γ (PCUICAstUtils.it_mkLambda_or_LetIn Δ t)).

Check (@PCUICSafeLemmata.isAppProd_isProd
     of forall cf : config.checker_flags,
       PCUICNormal.RedFlags.t ->
       forall Σ : PCUICAst.global_env_ext,
       utils.squash (PCUICTyping.wf (PCUICAstUtils.fst_ctx Σ)) ->
       forall (Γ : PCUICAst.context) (t : PCUICAst.term),
       is_true (PCUICSafeLemmata.isAppProd t) ->
       PCUICSafeLemmata.welltyped Σ Γ t -> is_true (PCUICSafeLemmata.isProd t)).

Check (@PCUICSafeLemmata.mkApps_Prod_nil'
     of forall cf : config.checker_flags,
       PCUICNormal.RedFlags.t ->
       forall Σ : PCUICAst.global_env_ext,
       utils.squash (PCUICTyping.wf (PCUICAstUtils.fst_ctx Σ)) ->
       forall (Γ : PCUICAst.context) (na : BasicAst.name) (A B : PCUICAst.term)
         (l : list PCUICAst.term),
       PCUICSafeLemmata.wellformed Σ Γ (PCUICAst.mkApps (PCUICAst.tProd na A B) l) ->
       l = nil).

Check (@PCUICSafeLemmata.Lambda_conv_inv
     of forall cf : config.checker_flags,
       PCUICNormal.RedFlags.t ->
       forall Σ : PCUICAst.global_env_ext,
       utils.squash (PCUICTyping.wf (PCUICAstUtils.fst_ctx Σ)) ->
       forall (leq : PCUICCumulativity.conv_pb) (Γ : PCUICAst.context)
         (na1 na2 : BasicAst.name) (A1 A2 b1 b2 : PCUICAst.term),
       PCUICCumulativity.conv leq Σ Γ (PCUICAst.tLambda na1 A1 b1)
         (PCUICAst.tLambda na2 A2 b2) ->
       utils.squash (PCUICTyping.conv Σ Γ A1 A2) /\
       PCUICCumulativity.conv leq Σ (PCUICAst.snoc Γ (PCUICAst.vass na1 A1)) b1 b2).

Check (@PCUICSafeLemmata.it_mkLambda_or_LetIn_let_free_conv_inv
     of forall cf : config.checker_flags,
       PCUICNormal.RedFlags.t ->
       forall Σ : PCUICAst.global_env_ext,
       utils.squash (PCUICTyping.wf (PCUICAstUtils.fst_ctx Σ)) ->
       forall (Γ Δ1 Δ2 : PCUICAst.context) (t1 t2 : PCUICAst.term),
       is_true (PCUICSafeLemmata.let_free_context Δ1) ->
       is_true (PCUICSafeLemmata.let_free_context Δ2) ->
       PCUICTyping.conv Σ Γ (PCUICAstUtils.it_mkLambda_or_LetIn Δ1 t1)
         (PCUICAstUtils.it_mkLambda_or_LetIn Δ2 t2) ->
       PCUICSR.context_relation (PCUICSR.conv_decls Σ) (PCUICAstUtils.app_context Γ Δ1)
         (PCUICAstUtils.app_context Γ Δ2) *
       PCUICTyping.conv Σ (PCUICAstUtils.app_context Γ Δ1) t1 t2).

Check (@PCUICSafeLemmata.it_mkLambda_or_LetIn_let_free_conv'_inv
     of forall cf : config.checker_flags,
       PCUICNormal.RedFlags.t ->
       forall Σ : PCUICAst.global_env_ext,
       utils.squash (PCUICTyping.wf (PCUICAstUtils.fst_ctx Σ)) ->
       forall (leq : PCUICCumulativity.conv_pb) (Γ Δ1 Δ2 : PCUICAst.context)
         (t1 t2 : PCUICAst.term),
       is_true (PCUICSafeLemmata.let_free_context Δ1) ->
       is_true (PCUICSafeLemmata.let_free_context Δ2) ->
       PCUICCumulativity.conv leq Σ Γ (PCUICAstUtils.it_mkLambda_or_LetIn Δ1 t1)
         (PCUICAstUtils.it_mkLambda_or_LetIn Δ2 t2) ->
       utils.squash
         (PCUICSR.context_relation (PCUICSR.conv_decls Σ) (PCUICAstUtils.app_context Γ Δ1)
            (PCUICAstUtils.app_context Γ Δ2)) /\
       PCUICCumulativity.conv leq Σ (PCUICAstUtils.app_context Γ Δ1) t1 t2).

Check (@PCUICSafeLemmata.it_mkLambda_or_LetIn_conv'
     of forall cf : config.checker_flags,
       PCUICNormal.RedFlags.t ->
       forall Σ : PCUICAst.global_env_ext,
       utils.squash (PCUICTyping.wf (PCUICAstUtils.fst_ctx Σ)) ->
       forall (leq : PCUICCumulativity.conv_pb) (Γ Δ1 Δ2 : PCUICAst.context)
         (t1 t2 : PCUICAst.term),
       PCUICSR.context_relation (PCUICSR.conv_decls Σ) (PCUICAstUtils.app_context Γ Δ1)
         (PCUICAstUtils.app_context Γ Δ2) ->
       PCUICCumulativity.conv leq Σ (PCUICAstUtils.app_context Γ Δ1) t1 t2 ->
       PCUICCumulativity.conv leq Σ Γ (PCUICAstUtils.it_mkLambda_or_LetIn Δ1 t1)
                              (PCUICAstUtils.it_mkLambda_or_LetIn Δ2 t2)).

Check (@PCUICSafeLemmata.Prod_conv
     of forall cf : config.checker_flags,
       PCUICNormal.RedFlags.t ->
       forall Σ : PCUICAst.global_env_ext,
       utils.squash (PCUICTyping.wf (PCUICAstUtils.fst_ctx Σ)) ->
       forall (leq : PCUICCumulativity.conv_pb) (Γ : PCUICAst.context)
         (na1 : BasicAst.name) (A1 B1 : PCUICAst.term) (na2 : BasicAst.name)
         (A2 B2 : PCUICAst.term),
       PCUICTyping.conv Σ Γ A1 A2 ->
       PCUICCumulativity.conv leq Σ (PCUICAst.snoc Γ (PCUICAst.vass na1 A1)) B1 B2 ->
       PCUICCumulativity.conv leq Σ Γ (PCUICAst.tProd na1 A1 B1)
         (PCUICAst.tProd na2 A2 B2)).

Check (@PCUICSafeLemmata.it_mkLambda_or_LetIn_conv
     of forall cf : config.checker_flags,
       PCUICNormal.RedFlags.t ->
       forall Σ : PCUICAst.global_env_ext,
       utils.squash (PCUICTyping.wf (PCUICAstUtils.fst_ctx Σ)) ->
       forall (Γ Δ1 Δ2 : PCUICAst.context) (t1 t2 : PCUICAst.term),
       PCUICSR.context_relation (PCUICSR.conv_decls Σ) (PCUICAstUtils.app_context Γ Δ1)
         (PCUICAstUtils.app_context Γ Δ2) ->
       PCUICTyping.conv Σ (PCUICAstUtils.app_context Γ Δ1) t1 t2 ->
       PCUICTyping.conv Σ Γ (PCUICAstUtils.it_mkLambda_or_LetIn Δ1 t1)
         (PCUICAstUtils.it_mkLambda_or_LetIn Δ2 t2)).

Check (@PCUICSafeLemmata.App_conv
     of forall cf : config.checker_flags,
       PCUICNormal.RedFlags.t ->
       forall Σ : PCUICAst.global_env_ext,
       utils.squash (PCUICTyping.wf (PCUICAstUtils.fst_ctx Σ)) ->
       forall (Γ : PCUICAst.context) (t1 t2 u1 u2 : PCUICAst.term),
       PCUICTyping.conv Σ Γ t1 t2 ->
       PCUICTyping.conv Σ Γ u1 u2 ->
       PCUICTyping.conv Σ Γ (PCUICAst.tApp t1 u1) (PCUICAst.tApp t2 u2)).

Check (@PCUICSafeLemmata.mkApps_conv_weak
     of forall cf : config.checker_flags,
       PCUICNormal.RedFlags.t ->
       forall Σ : PCUICAst.global_env_ext,
       utils.squash (PCUICTyping.wf (PCUICAstUtils.fst_ctx Σ)) ->
       forall (Γ : PCUICAst.context) (u1 u2 : PCUICAst.term) (l : list PCUICAst.term),
       PCUICTyping.conv Σ Γ u1 u2 ->
       PCUICTyping.conv Σ Γ (PCUICAst.mkApps u1 l) (PCUICAst.mkApps u2 l)).

Check (@PCUICSafeLemmata.welltyped_zipc_replace
     of forall cf : config.checker_flags,
       PCUICNormal.RedFlags.t ->
       forall Σ : PCUICAst.global_env_ext,
       utils.squash (PCUICTyping.wf (PCUICAstUtils.fst_ctx Σ)) ->
       forall (Γ : PCUICAst.context) (u v : PCUICAst.term) (π : PCUICPosition.stack),
       PCUICSafeLemmata.welltyped Σ Γ (PCUICPosition.zipc v π) ->
       PCUICSafeLemmata.welltyped Σ
         (PCUICAstUtils.app_context Γ (PCUICPosition.stack_context π)) u ->
       PCUICTyping.conv Σ (PCUICAstUtils.app_context Γ (PCUICPosition.stack_context π)) u
         v -> PCUICSafeLemmata.welltyped Σ Γ (PCUICPosition.zipc u π)).

Check (@PCUICSafeLemmata.wellformed_zipc_replace
     of forall cf : config.checker_flags,
       PCUICNormal.RedFlags.t ->
       forall Σ : PCUICAst.global_env_ext,
       utils.squash (PCUICTyping.wf (PCUICAstUtils.fst_ctx Σ)) ->
       forall (Γ : PCUICAst.context) (u v : PCUICAst.term) (π : PCUICPosition.stack),
       PCUICSafeLemmata.wellformed Σ Γ (PCUICPosition.zipc v π) ->
       PCUICSafeLemmata.wellformed Σ
         (PCUICAstUtils.app_context Γ (PCUICPosition.stack_context π)) u ->
       PCUICTyping.conv Σ (PCUICAstUtils.app_context Γ (PCUICPosition.stack_context π)) u
         v -> PCUICSafeLemmata.wellformed Σ Γ (PCUICPosition.zipc u π)).

Check (@PCUICSafeLemmata.conv_context_conversion
     of forall cf : config.checker_flags,
       PCUICNormal.RedFlags.t ->
       forall Σ : PCUICAst.global_env_ext,
       utils.squash (PCUICTyping.wf (PCUICAstUtils.fst_ctx Σ)) ->
       forall (Γ : PCUICAst.context) (u v : PCUICAst.term) (Γ' : PCUICAst.context),
       PCUICTyping.conv Σ Γ u v ->
       PCUICSR.context_relation (PCUICSR.conv_decls Σ) Γ Γ' -> PCUICTyping.conv Σ Γ' u v).

Check (@PCUICSafeLemmata.Construct_Ind_ind_eq
     of forall cf : config.checker_flags,
       PCUICNormal.RedFlags.t ->
       forall Σ : PCUICAst.global_env_ext,
       utils.squash (PCUICTyping.wf (PCUICAstUtils.fst_ctx Σ)) ->
       forall (Γ : PCUICAst.context) (n : nat) (i : BasicAst.inductive)
         (args : list PCUICAst.term) (u : Universes.universe_instance)
         (i' : BasicAst.inductive) (args' : list PCUICAst.term)
         (u' : Universes.universe_instance),
       PCUICTyping.typing Σ Γ (PCUICAst.mkApps (PCUICAst.tConstruct i n u) args)
                          (PCUICAst.mkApps (PCUICAst.tInd i' u') args') -> i = i').

Check (@PCUICSafeLemmata.Proj_red_cond
     of forall cf : config.checker_flags,
       PCUICNormal.RedFlags.t ->
       forall Σ : PCUICAst.global_env_ext,
       utils.squash (PCUICTyping.wf (PCUICAstUtils.fst_ctx Σ)) ->
       forall (Γ : PCUICAst.context) (i : BasicAst.inductive)
         (pars narg : nat) (i' : BasicAst.inductive) (c : nat)
         (u : Universes.universe_instance) (l : list PCUICAst.term),
       PCUICSafeLemmata.wellformed Σ Γ
         (PCUICAst.tProj (i, pars, narg) (PCUICAst.mkApps (PCUICAst.tConstruct i' c u) l)) ->
       List.nth_error l (pars + narg) <> None).

Require PCUICSN.

Check (@PCUICSN.normalisation
         of forall cf : config.checker_flags,
            forall (Σ : PCUICAst.global_env_ext) (Γ : PCUICAst.context)
              (t : PCUICAst.term),
              welltyped Σ Γ t ->
              Acc (cored (fst Σ) Γ) t).

Check (@PCUICSN.Acc_cored_Prod
         of forall cf : config.checker_flags,
            forall (Σ : PCUICAst.global_env_ext) (Γ : PCUICAst.context) (n : name)
              (t1 t2 : PCUICAst.term),
              Acc (cored Σ Γ) t1 ->
              Acc (cored Σ (Γ,, vass n t1)) t2 ->
              Acc (cored Σ Γ) (tProd n t1 t2)).

Check (@PCUICSN.Acc_cored_LetIn
         of forall cf : config.checker_flags,
            forall (Σ : PCUICAst.global_env_ext) (Γ : PCUICAst.context) (n : name)
              (t1 t2 t2 : PCUICAst.term),
              Acc (cored Σ Γ) t1 ->
              Acc (cored Σ Γ) t2 ->
              Acc (cored Σ (Γ,, vdef n t1 t2)) t3 ->
              Acc (cored Σ Γ) (tLetIn n t1 t2 t3)).

Check (@PCUICSN.isWfArity_red1
         of forall cf : config.checker_flags,
            forall (Σ : PCUICAst.global_env_ext) (Γ : PCUICAst.context)
              (A B : PCUICAst.term),
              red1 (fst Σ) Γ A B ->
              isWfArity typing Σ Γ A ->
              isWfArity typing Σ Γ B).