(* Distributed under the terms of the MIT license. *)
From Coq Require Import ssreflect.
From MetaCoq.Template Require Import config utils.
From MetaCoq.Template Require Ast TypingWf WfAst TermEquality.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCumulativity
     PCUICLiftSubst PCUICEquality PCUICReduction 
     PCUICUnivSubst PCUICTyping PCUICGlobalEnv TemplateToPCUIC
     PCUICWeakeningConv PCUICWeakeningTyp PCUICSubstitution PCUICGeneration PCUICCasesContexts.

From Equations.Prop Require Import DepElim.
From Equations Require Import Equations.

Implicit Types cf : checker_flags.

Definition lengths := 
  (@Ast.Env.context_assumptions_subst_context,
  Ast.Env.context_assumptions_app,
  @Ast.Env.context_assumptions_subst_instance, @Ast.Env.context_assumptions_lift_context,
   @Ast.Env.expand_lets_ctx_length, @Ast.Env.subst_context_length,
  @Ast.Env.subst_instance_length, 
  @Ast.Env.expand_lets_k_ctx_length, 
  @Ast.inds_length, @Ast.Env.lift_context_length,
  @app_length, @List.rev_length, @Ast.Env.extended_subst_length, @reln_length,
  Nat.add_0_r, @app_nil_r, 
  @map_length, @mapi_length, @mapi_rec_length,
  @fold_context_k_length, @Typing.cofix_subst_length, @Typing.fix_subst_length,
  @Ast.Env.smash_context_length, @Ast.Env.arities_context_length).

Definition plengths := 
    (@context_assumptions_subst_context,
    @context_assumptions_app,
    @context_assumptions_subst_instance, @context_assumptions_lift_context,
     @expand_lets_ctx_length, @subst_context_length,
    @subst_instance_length, @expand_lets_k_ctx_length, @inds_length, @lift_context_length,
    @app_length, @List.rev_length, @extended_subst_length, @reln_length,
    Nat.add_0_r, @app_nil_r, 
    @map_length, @mapi_length, @mapi_rec_length,
    @fold_context_k_length, @cofix_subst_length, @fix_subst_length,
    @smash_context_length, @context_assumptions_smash_context,
    @arities_context_length).
  

Lemma ind_predicate_context_length ind mdecl idecl :
  #|Ast.ind_predicate_context ind mdecl idecl| = S #|idecl.(Ast.Env.ind_indices)|.
Proof.
  rewrite /Ast.ind_predicate_context /=. now len.
Qed.

Definition pclengths := 
  (@PCUICCases.ind_predicate_context_length,
    @PCUICCases.cstr_branch_context_length,
    @PCUICCases.inst_case_branch_context_length,
    @PCUICCases.inst_case_predicate_context_length,
    @ind_predicate_context_length).

Ltac len ::= 
  repeat (rewrite !lengths /= // || rewrite !plengths /= // || rewrite !pclengths /= //);
  try lia.
  
Tactic Notation "len" "in" hyp(id) :=
  repeat (rewrite !lengths /= // in id || rewrite !plengths /= // in id || 
    rewrite !pclengths /= // in id);
  try lia.

(* Source = Template, Target (unqualified) = Coq *)

Module S := Template.Ast.
Module SEq := Template.TermEquality.
Module ST := Template.Typing.
Module SL := Template.LiftSubst.

Lemma mkApps_morphism (f : term -> term) u v :
  (forall x y, f (tApp x y) = tApp (f x) (f y)) ->
  f (mkApps u v) = mkApps (f u) (List.map f v).
Proof.
  intros H.
  revert u; induction v; simpl; trivial.
  intros.
  now rewrite IHv H.
Qed.

Ltac solve_list :=
  rewrite !map_map_compose ?compose_on_snd ?compose_map_def;
  try rewrite !map_length;
  try solve_all; try typeclasses eauto with core.

Lemma mkApps_app f l l' : mkApps f (l ++ l') = mkApps (mkApps f l) l'.
Proof.
  revert f l'; induction l; simpl; trivial.
Qed.
  
Ltac maps := rewrite_strat (topdown (old_hints map)).
Ltac lengths := rewrite_strat (topdown (hints len)).

Lemma destArity_mkApps ctx t l : l <> [] -> destArity ctx (mkApps t l) = None.
Proof.
  destruct l as [|a l]. congruence.
  intros _. simpl.
  revert t a; induction l; intros; simpl; try congruence.
Qed.

Definition trans_global_decls_acc Σ Σ' := 
  fold_right
    (fun (decl : kername × Ast.Env.global_decl) (Σ' : global_env) =>
      on_snd (trans_global_decl Σ') decl :: Σ') Σ' Σ.

Lemma trans_global_decls_app Σ Σ' : 
  trans_global_decls (Σ ++ Σ') = trans_global_decls_acc Σ (trans_global_decls Σ').
Proof.
  rewrite /trans_global_decls /trans_global_decls_acc.
  now rewrite fold_right_app.
Qed.

Lemma extends_trans_global_decls_acc Σ Σ' : 
  extends Σ' (trans_global_decls_acc Σ Σ').
Proof.
  induction Σ.
  * now exists [].
  * rewrite /trans_global_decls_acc /=.
    destruct IHΣ as [Σ'' eq].
    eexists (_ :: Σ'').
    rewrite -app_comm_cons. f_equal.
    now rewrite /trans_global_decls_acc in eq.
Qed.

Definition wf_global_decl {cf} (Σ : Ast.Env.global_env_ext) kn decl :=
  Typing.on_global_decl (fun Σ => WfAst.wf_decl_pred Σ.1) Σ kn decl.

(* Issue in equations: signatures cannot be found up-to arbitrary conversions. *)
#[global] Hint Extern 4 (Signature (Typing.wf _) _ _) => exact (ST.on_global_env_Signature _ _ _) : typeclass_instances.

Lemma trans_lookup_env {cf} Σ cst {wfΣ : Typing.wf Σ} :
  match Ast.Env.lookup_env Σ cst with
  | None => lookup_env (trans_global_decls Σ) cst = None
  | Some d => 
    ∑ Σ',
      [× Typing.extends Σ' Σ,
        wf_global_decl (Σ', Ast.universes_decl_of_decl d) cst d,
        extends (trans_global_decls Σ') (trans_global_decls Σ) &
        lookup_env (trans_global_decls Σ) cst = Some (trans_global_decl (trans_global_decls Σ') d)]
  end. 
Proof.
  induction Σ.
  - cbn; auto.
  - cbn [Ast.Env.lookup_env].
    destruct eq_kername eqn:eqk.
    change (eq_kername cst a.1) with (eqb cst a.1) in eqk.
    apply eqb_eq in eqk; subst.
    eexists Σ.
    split.
    * now exists [a].
    * apply TypingWf.typing_wf_sigma in wfΣ.
      now depelim wfΣ.
    * now exists [(a.1, trans_global_decl (trans_global_decls Σ) a.2)].
    * rewrite (trans_global_decls_app [a]).
      cbn. now rewrite eq_kername_refl.
    * depelim wfΣ. specialize (IHΣ wfΣ).
      destruct (Ast.Env.lookup_env Σ cst) eqn:h.
      destruct IHΣ as [Σ' [ext wf ext' hl]].
      exists Σ'. split => //.
      destruct ext as [? ->]. exists ((kn, d) :: x).
      now rewrite app_comm_cons.
      rewrite (trans_global_decls_app [_]). cbn.
      destruct ext' as [? ->]. eexists. 
      rewrite app_comm_cons. reflexivity.
      cbn. now rewrite eqk hl.
      cbn. now rewrite eqk.
Qed.

Lemma extends_trans Σ Σ' Σ'' : extends Σ Σ' -> extends Σ' Σ'' -> extends Σ Σ''.
Proof.
  intros [s eq] [s' eq']; subst. eexists (s' ++ s). now rewrite app_assoc.
Qed.

Lemma trans_weakening {cf} Σ Σ' t : 
  Typing.wf Σ -> extends (trans_global_decls Σ) Σ' -> wf Σ' ->
  WfAst.wf Σ t ->
  trans (trans_global_decls Σ) t = trans Σ' t.
Proof.
  intros wfΣ ext wfΣ' wft.
  induction wft using WfAst.term_wf_forall_list_ind; cbn; auto; try solve [f_equal; solve_all].
  rewrite /lookup_inductive /lookup_minductive.
  destruct H as [H hnth]. red in H. move: H.
  generalize (trans_lookup_env Σ (inductive_mind ci)).
  destruct Ast.Env.lookup_env.
  * intros [Σ'' [ext' _ ext'' hl]] [= ->].
    rewrite hl => /= //. cbn.
    rewrite nth_error_map hnth /=.
    rewrite (PCUICWeakeningEnvConv.extends_lookup _ _ _ _ wfΣ' ext hl) /=.
    rewrite nth_error_map hnth /=.
    red in X0.
    f_equal => //. rewrite /id. unfold trans_predicate. f_equal; solve_all.
    f_equal. solve_all.
  * discriminate.
Qed. 

Lemma trans_decl_weakening {cf} Σ Σ' t : 
  Typing.wf Σ -> extends (trans_global_decls Σ) Σ' -> wf Σ' ->
  WfAst.wf_decl Σ t ->
  trans_decl (trans_global_decls Σ) t = trans_decl Σ' t.
Proof.
  intros wfΣ ext wfΣ' wft.
  rewrite /trans_decl; destruct t as [na [b|] ty] => /=; f_equal;
  rewrite trans_weakening => //; apply wft.
Qed.  

Lemma trans_local_length Σ Γ : #|trans_local Σ Γ| = #|Γ|.
Proof. now rewrite map_length. Qed.

#[global]
Hint Rewrite trans_local_length : len.

Lemma trans_local_weakening {cf} Σ Σ' t : 
  Typing.wf Σ -> extends (trans_global_decls Σ) Σ' -> wf Σ' ->
  All (WfAst.wf_decl Σ) t ->
  trans_local (trans_global_decls Σ) t = trans_local Σ' t.
Proof.
  intros wfΣ ext wfΣ' a.
  induction a; cbn; auto.
  f_equal. 2:apply IHa.
  rewrite /trans_decl; destruct x as [na [b|] ty] => /=; f_equal;
  rewrite trans_weakening => //; apply p.
Qed.  

Lemma trans_ind_body_weakening {cf} Σ Σ' b : 
  Typing.wf Σ -> extends (trans_global_decls Σ) Σ' -> wf Σ' ->
  TypingWf.wf_inductive_body Σ b ->
  trans_one_ind_body (trans_global_decls Σ) b = trans_one_ind_body Σ' b.
Proof.
  intros wfΣ ext wfΣ' H.
  destruct H. rewrite /trans_one_ind_body; destruct b; cbn in *.
  f_equal; solve_all.
  - rewrite trans_decl_weakening //.
  - rewrite trans_weakening //.
  - unfold trans_constructor_body; destruct x; cbn in *; f_equal.
    * rewrite [map _ _]trans_local_weakening //.
    * solve_all. rewrite trans_weakening //.
    * rewrite trans_weakening //.
  - destruct x. f_equal.
    rewrite trans_weakening //.
Qed.

Lemma trans_global_decl_weaken {cf} (Σ : Ast.Env.global_env_ext) Σ' kn d : 
  Typing.wf Σ.1 -> extends (trans_global_decls Σ.1) Σ' -> wf Σ' ->
  wf_global_decl Σ kn d ->
  trans_global_decl (trans_global_decls Σ.1) d = trans_global_decl Σ' d.
Proof.
  intros.
  destruct d; cbn; f_equal.
  - rewrite /trans_constant_body /=.
    do 3 red in X2.
    destruct (Ast.Env.cst_body c) => /=. cbn.
    f_equal.
    erewrite trans_weakening; tea. reflexivity. apply X2.
    erewrite trans_weakening; tea. reflexivity. apply X2.
    f_equal.
    erewrite trans_weakening; tea. reflexivity. apply X2.
  - rewrite /trans_minductive_body. f_equal.
    * erewrite trans_local_weakening; trea.
      eapply TypingWf.on_global_inductive_wf_params in X2. solve_all.
    * eapply TypingWf.on_global_inductive_wf_bodies in X2. solve_all.
      rewrite trans_ind_body_weakening //.
Qed.

Import TypingWf.

Lemma weaken_wf_decl_pred {cf} (Σ Σ' : Ast.Env.global_env) Γ t T :
  Typing.wf Σ -> Typing.extends Σ Σ' -> Typing.wf Σ' ->
  WfAst.wf_decl_pred Σ Γ t T -> WfAst.wf_decl_pred Σ' Γ t T.
Proof.
  intros wf ext wf' ong.
  red in ong |- *.
  destruct T; intuition eauto using wf_extends.
Qed.

(** Do we need weakening for wf_decl_pred? *)
(* Lemma weaken_red1 {cf} (Σ Σ' : Ast.Env.global_env_ext) Γ t t' :
   Typing.wf Σ.1 -> Typing.extends Σ.1 Σ'.1 -> Typing.wf Σ'.1 ->
   Typing.red1 cf Σ Γ t t' ->
   Typing.red1 cf Σ Γ t t'.
Proof.

Lemma weaken_cumul  {cf} (Σ Σ' : Ast.Env.global_env_ext) Γ t t' :
   Typing.wf Σ.1 -> Typing.extends Σ.1 Σ'.1 -> Typing.wf Σ'.1 ->
   Typing.TemplateConversionPar.cumul cf Σ Γ t t' ->
   Typing.TemplateConversionPar.cumul cf Σ Γ t t'.
Proof.
  intros wf ext wf'.
  induction 1.

Lemma weaken_cumul_ctx_rel  {cf} (Σ Σ' : Ast.Env.global_env_ext) Γ Δ Δ' :
   Typing.wf Σ.1 -> Typing.extends Σ.1 Σ'.1 -> Typing.wf Σ'.1 ->
   Typing.TemplateConversion.cumul_ctx_rel Σ Γ Δ Δ' ->
   Typing.TemplateConversion.cumul_ctx_rel Σ' Γ Δ Δ'.
Proof.
  intros wf ext wf'.
  induction 1; constructor; auto.
  destruct p; constructor; auto.


Lemma weaken_wf_global_decl {cf} (Σ Σ' : Ast.Env.global_env_ext) kn d : 
  Typing.wf Σ.1 -> Typing.extends Σ.1 Σ'.1 -> Typing.wf Σ'.1 ->
  wf_global_decl Σ kn d -> wf_global_decl Σ' kn d.
Proof.
  intros wf ext wf' ong.
  destruct d; cbn.
  - cbn in ong.
    red in ong |- *.
    destruct Ast.Env.cst_body; intuition eauto using wf_extends, weaken_wf_decl_pred.
    destruct ong. split. now eauto using wf_extends. auto.    
  - cbn in ong |- *. 
    destruct ong; split; solve_all.
    * eapply Alli_impl; tea. intros n x []; econstructor; eauto using wf_extends.
      + red in onArity. red. eapply weaken_wf_decl_pred. all:typeclasses eauto with core.
      + instantiate (1 := ind_cunivs).
        clear -onConstructors wf ext wf'.
        induction onConstructors; constructor; auto.
        destruct r; constructor => //.
        { red in on_ctype |- *. eapply weaken_wf_decl_pred; typeclasses eauto with core. }
        { clear -on_cargs wf ext wf'.
          induction (Ast.Env.cstr_args x0) in on_cargs, y |- *; auto.
          cbn. destruct a as [na [b|] ty]; cbn in *; intuition auto.
          eapply weaken_wf_decl_pred; typeclasses eauto with core.
          eapply weaken_wf_decl_pred; typeclasses eauto with core.
          destruct y; intuition auto.
          eapply weaken_wf_decl_pred; typeclasses eauto with core. }
        { clear -on_cindices wf ext wf'.
          induction on_cindices; constructor; auto.
          eapply weaken_wf_decl_pred; typeclasses eauto with core. }
        { clear -on_ctype_variance wf ext wf'. intros v hv. 
          specialize (on_ctype_variance v hv).
          red in on_ctype_variance |- *.
          destruct Typing.variance_universes => //.
          destruct p as [[] ?]; intuition auto. 
          clear -a wf ext wf'.

          admit.
        }
      + admit.
      + admit.
  * red in onParams |- *.
    eapply Typing.All_local_env_impl; tea. intros.
    eapply weaken_wf_decl_pred; typeclasses eauto with core.
Qed. *) 

Lemma wf_global_extends {cf} {Σ Σ' : Ast.Env.global_env} : Typing.wf Σ' -> Typing.extends Σ Σ' -> Typing.wf Σ.
Proof.
  induction Σ'; cbn; auto.
  - intros. destruct X0. destruct x; try discriminate.
    cbn in e. now subst. 
  - intros. destruct X0 as [? eq].
    destruct x ; noconf eq => //.
    apply IHΣ'. now depelim X.
    now exists x.
Qed.

Lemma trans_lookup {cf} Σ cst :
  Typing.wf Σ ->
  wf (trans_global_decls Σ) -> 
  lookup_env (trans_global_decls Σ) cst = 
  option_map (trans_global_decl (trans_global_decls Σ)) (Ast.Env.lookup_env Σ cst).
Proof.
  intros wf wf'.
  generalize (trans_lookup_env Σ cst).
  destruct Ast.Env.lookup_env eqn:heq => //.
  intros [Σ' [ext wfdecl ext' hl]].
  rewrite hl. cbn. f_equal.
  eapply (trans_global_decl_weaken (Σ', Ast.universes_decl_of_decl g)); tea. cbn.
  now eapply wf_global_extends.
Qed.

Section Translation.
  Context (Σ : Ast.Env.global_env).
  Notation trans := (trans (trans_global_decls Σ)).
  Notation trans_decl := (trans_decl (trans_global_decls Σ)).
  Notation trans_local := (trans_local (trans_global_decls Σ)).

  Ltac dest_lookup := 
    destruct lookup_inductive as [[mdecl idecl]|].
    Lemma map_map2 {A B C D} (f : A -> B) (g : C -> D -> A) l l' : 
    map f (map2 g l l') = map2 (fun x y => f (g x y)) l l'.
  Proof.
    induction l in l' |- *; destruct l'; simpl; auto. f_equal.
    apply IHl.
  Qed.
  
Lemma trans_lift n k t :
  trans (Template.Ast.lift n k t) = lift n k (trans t).
Proof.
  revert k. induction t using Template.Induction.term_forall_list_ind; simpl; intros; try congruence.
  - f_equal. rewrite !map_map_compose. solve_all.
  - rewrite lift_mkApps IHt map_map.
    f_equal. rewrite map_map; solve_all.

  - destruct X; red in X0.
    dest_lookup. simpl.
    * f_equal; auto.
      unfold trans_predicate, map_predicate_k; cbn.
      f_equal; auto. solve_list.
      + rewrite e. f_equal.
        now rewrite map2_bias_left_length.
      + rewrite !map_map_compose.
        rewrite map_map2 !PCUICUnivSubstitutionConv.map2_map_r.
        clear -X0. cbn.
        generalize (ind_ctors idecl).
        induction X0; simpl; auto. destruct l; reflexivity.
        intros l0; destruct l0; try reflexivity.
        cbn. rewrite IHX0. f_equal.
        rewrite /trans_branch /= p // /map_branch /map_branch_k /= /id. f_equal.
        now rewrite map2_bias_left_length.
    * simpl. rewrite /id /map_predicate_k /=. f_equal; eauto.
      f_equal; auto. rewrite !map_map_compose. solve_all.
      rewrite e. now rewrite map_length.
  - f_equal; auto. maps. solve_all.
  - f_equal; auto; solve_all.
Qed.

Lemma trans_mkApp u a : trans (Template.Ast.mkApp u a) = tApp (trans u) (trans a).
Proof.
  induction u; simpl; try reflexivity.
  rewrite map_app.
  replace (tApp (mkApps (trans u) (map trans args)) (trans a))
    with (mkApps (mkApps (trans u) (map trans args)) [trans a]) by reflexivity.
  rewrite mkApps_app. reflexivity.
Qed.

Lemma trans_mkApps u v : 
  trans (Template.Ast.mkApps u v) = mkApps (trans u) (List.map trans v).
Proof.
  revert u; induction v.
  simpl; trivial.
  intros.
  rewrite <- Template.AstUtils.mkApps_mkApp; auto.
  rewrite IHv. simpl. f_equal.
  apply trans_mkApp.
Qed.

Lemma trans_subst t k u : 
  trans (Template.Ast.subst t k u) = subst (map trans t) k (trans u).
Proof.
  revert k. induction u using Template.Induction.term_forall_list_ind; simpl; intros; try congruence.

  - repeat nth_leb_simpl; auto.
    rewrite trans_lift.
    rewrite nth_error_map in e0. rewrite e in e0.
    injection e0. congruence.

  - f_equal; solve_list.

  - rewrite subst_mkApps. rewrite <- IHu.
    rewrite trans_mkApps. f_equal.
    solve_list.

  - destruct X; red in X0.
    dest_lookup; cbn; f_equal; auto; solve_list.
    unfold trans_predicate, map_predicate_k; cbn.
    f_equal; auto. solve_list.
    + rewrite e. f_equal.
      now rewrite map2_bias_left_length.
    + rewrite map_map2 !PCUICUnivSubstitutionConv.map2_map_r.
      clear -X0. cbn.
      generalize (ind_ctors idecl).
      induction X0; simpl; auto. destruct l; reflexivity.
      intros l0; destruct l0; try reflexivity.
      cbn. rewrite IHX0. f_equal.
      rewrite /trans_branch /= p // /map_branch /map_branch_k /= /id. f_equal.
      now rewrite map2_bias_left_length.
    + unfold subst_predicate, id => /=.
      f_equal; auto; solve_all.
  - f_equal; auto; solve_list.
  - f_equal; auto; solve_list.
Qed.

Notation Tterm := Template.Ast.term.
Notation Tcontext := Template.Ast.Env.context.

Lemma All_map2 {A B C} P (l : list A) (l' : list B) (f g : A -> B -> C) : 
  All P l' ->
  (forall x y, P y -> f x y = g x y) ->
  map2 f l l' = map2 g l l'. 
Proof.
  induction 1 in l |- * => Hfg /=; destruct l => //.
  cbn. rewrite IHX //. f_equal.
  now apply Hfg.
Qed.

Lemma trans_subst_instance u t : trans (subst_instance u t) = subst_instance u (trans t).
Proof.
  rewrite /subst_instance /=.
  induction t using Template.Induction.term_forall_list_ind; simpl; try congruence.
  { f_equal. rewrite !map_map_compose. solve_all. }
  { rewrite IHt. rewrite map_map_compose.
    rewrite mkApps_morphism; auto. f_equal.
    rewrite !map_map_compose. solve_all. }  
  2-3:f_equal; auto; unfold BasicAst.tFixProp, Ast.tCaseBrsProp in *;
    repeat toAll; solve_list.
  destruct X; red in X0.
  dest_lookup; cbn; f_equal; auto; solve_list.
  - rewrite /trans_predicate /= /map_predicate /=.
    f_equal; solve_all.
  - rewrite PCUICUnivSubstitutionConv.map2_map_r. cbn.
    rewrite map_map2 PCUICUnivSubstitutionConv.map2_map_r.
    eapply All_map2; tea; cbn => cdecl br.
    rewrite /map_branch /trans_branch /= /id.
    now intros; f_equal.
  - rewrite /id /map_predicate /=. f_equal; solve_all.
Qed.


Lemma trans_destArity {cf} {wfΣ : Typing.wf Σ} ctx t :
  Template.WfAst.wf Σ t ->
  wf (trans_global_decls Σ) ->
  match AstUtils.destArity ctx t with
  | Some (args, s) =>
    destArity (trans_local ctx) (trans t) =
    Some (trans_local args, s)
  | None => destArity (trans_local ctx) (trans t) = None
  end.
Proof.
  intros wf wf'; revert ctx.
  induction wf using WfAst.term_wf_forall_list_ind; intros ctx; simpl; trivial.
  apply (IHwf0 (Ast.Env.vass n t :: ctx)).
  apply (IHwf1 (Ast.Env.vdef n t t0 :: ctx)).
  destruct l. congruence.
  now apply destArity_mkApps.
  destruct H as []. red in H.
  epose proof (trans_lookup Σ (inductive_mind ci.(ci_ind)) wfΣ wf').
  destruct lookup_inductive as [[mdecl' idecl']|] eqn:hl => //.
Qed. 

(* TODO Duplicate? *)
Lemma Alli_map_option_out_mapi_Some_spec {A B B'} (f : nat -> A -> option B) (g' : B -> B')
      (g : nat -> A -> option B') P l t :
  Alli P 0 l ->
  (forall i x t, P i x -> f i x = Some t -> g i x = Some (g' t)) ->
  map_option_out (mapi f l) = Some t ->
  map_option_out (mapi g l) = Some (map g' t).
Proof.
  unfold mapi. generalize 0.
  move => n Hl Hfg. move: n Hl t.
  induction 1; try constructor; auto.
  simpl. move=> t [= <-] //.
  move=> /=.
  case E: (f n hd) => [b|]; try congruence.
  rewrite (Hfg n _ _ p E).
  case E' : map_option_out => [b'|]; try congruence.
  move=> t [= <-]. now rewrite (IHHl _ E').
Qed.

Lemma All2_map_option_out_mapi_Some_spec :
  forall {A B B' S} (f : nat -> A -> option B) (g' : B -> B')
    (g : nat -> A -> option B') P l (ls : list S) t,
    All2 P l ls ->
    (forall i x t s, P x s -> f i x = Some t -> g i x = Some (g' t)) ->
    map_option_out (mapi f l) = Some t ->
    map_option_out (mapi g l) = Some (map g' t).
Proof.
  intros A B B' S f g' g P l ls t.
  unfold mapi. generalize 0.
  intros n hall h e.
  induction hall in t, n, h, e |- *.
  - simpl in *. apply some_inj in e. subst. reflexivity.
  - simpl in *.
    destruct (f n x) eqn:e'. 2: discriminate.
    eapply h in e' as h'. 2: eassumption.
    rewrite h'.
    match type of e with
    | context [ map_option_out ?t ] =>
      destruct (map_option_out t) eqn:e''
    end. 2: discriminate.
    eapply IHhall in e'' as h''. 2: assumption.
    rewrite h''. apply some_inj in e. subst.
    simpl. reflexivity.
Qed.

Definition on_pair {A B C D} (f : A -> B) (g : C -> D) (x : A * C) :=
  (f (fst x), g (snd x)).

Lemma trans_inds kn u bodies : map trans (Ast.inds kn u bodies) = 
  inds kn u (map (trans_one_ind_body (trans_global_decls Σ)) bodies).
Proof.
  unfold inds, Ast.inds. rewrite map_length.
  induction bodies. simpl. reflexivity. simpl; f_equal. auto.
Qed.

Lemma trans_it_mkProd_or_LetIn ctx t :
  trans (Ast.Env.it_mkProd_or_LetIn ctx t) =
  it_mkProd_or_LetIn (map trans_decl ctx) (trans t).
Proof.
  induction ctx in t |- *; simpl; auto.
  destruct a as [na [body|] ty]; simpl; auto.
  now rewrite IHctx.
  now rewrite IHctx.
Qed.

Lemma trans_it_mkLambda_or_LetIn ctx t :
  trans (Ast.Env.it_mkLambda_or_LetIn ctx t) =
  it_mkLambda_or_LetIn (map trans_decl ctx) (trans t).
Proof.
  induction ctx in t |- *; simpl; auto.
  destruct a as [na [body|] ty]; simpl; auto.
  now rewrite IHctx.
  now rewrite IHctx.
Qed.

Lemma trans_local_subst_instance u (Γ : Ast.Env.context) : 
  trans_local (subst_instance u Γ) = subst_instance u (trans_local Γ).
Proof.
  rewrite /subst_instance /=.
  induction Γ as [| [na [b|] A] Γ ih ] in u |- *.
  - reflexivity.
  - simpl. f_equal. 2: eapply ih.
    unfold map_decl, trans_decl. simpl.
    rewrite 2!trans_subst_instance.
    reflexivity.
  - simpl. f_equal. 2: eapply ih.
    unfold map_decl, trans_decl. simpl.
    rewrite trans_subst_instance.
    reflexivity.
Qed.

Lemma decompose_prod_assum_mkApps_nonnil ctx f args :
  args <> [] ->
  decompose_prod_assum ctx (mkApps f args) = (ctx, mkApps f args).
Proof.
  induction args => //.
  intros.
  rewrite mkApps_nonempty //.
Qed.

Notation trΣ := (trans_global_decls Σ).

Lemma trans_ind_params mdecl : trans_local (Ast.Env.ind_params mdecl) = ind_params (trans_minductive_body trΣ mdecl).
Proof. reflexivity. Qed.

Lemma trans_ind_bodies mdecl : map (trans_one_ind_body trΣ) (Ast.Env.ind_bodies mdecl) = 
  ind_bodies (trans_minductive_body (trans_global_decls Σ) mdecl).
Proof. reflexivity. Qed.

(* From MetaCoq.PCUIC Require Import PCUICClosed PCUICInductiveInversion.

Lemma instantiate_params_spec params paramsi concl ty :
  instantiate_params params paramsi (it_mkProd_or_LetIn params concl) = Some ty ->
  ty = (subst (List.rev paramsi) 0 (expand_lets params concl)).
Proof.
  intros h. eapply instantiate_params_make_context_subst in h as [ctx'' [ms [s' [da [dp ->]]]]].
  eapply make_context_subst_spec in dp.
  rewrite List.rev_involutive in dp.
  pose proof (PCUICContexts.context_subst_length2 dp).
  rewrite decompose_prod_n_assum_it_mkProd app_nil_r in da. noconf da.
  apply context_subst_subst_extended_subst in dp as ->.
  rewrite map_subst_expand_lets ?List.rev_length //.
Qed. *)

Lemma trans_ind_bodies_length mdecl : #|Ast.Env.ind_bodies mdecl| = #|ind_bodies (trans_minductive_body trΣ mdecl)|.
Proof. simpl. now rewrite map_length. Qed.

Lemma trans_ind_params_length mdecl : #|Ast.Env.ind_params mdecl| = #|ind_params (trans_minductive_body trΣ mdecl)|.
Proof. simpl. now rewrite map_length. Qed.

Lemma trans_ind_npars mdecl : Ast.Env.ind_npars mdecl = ind_npars (trans_minductive_body trΣ mdecl).
Proof. simpl. reflexivity. Qed.

Lemma trans_reln l p Γ : map trans (Ast.Env.reln l p Γ) = 
  reln (map trans l) p (trans_local Γ).
Proof.
  induction Γ as [|[na [b|] ty] Γ] in l, p |- *; simpl; auto.
  now rewrite IHΓ.
Qed.

Lemma trans_to_extended_list Γ n : map trans (Ast.Env.to_extended_list_k Γ n) = to_extended_list_k (trans_local Γ) n.
Proof.
  now rewrite /to_extended_list_k trans_reln.
Qed.

Lemma context_assumptions_map ctx : context_assumptions (map trans_decl ctx) = Ast.Env.context_assumptions ctx.
Proof.
  induction ctx as [|[na [b|] ty] ctx]; simpl; auto; lia.
Qed.

Hint Resolve Template.TypingWf.typing_wf : wf.

Lemma mkApps_trans_wf U l : Template.WfAst.wf Σ (Template.Ast.tApp U l) -> exists U' V', trans (Template.Ast.tApp U l) = tApp U' V'.
Proof.
  simpl. induction l using rev_ind. intros. inv X. congruence.
  intros. rewrite map_app. simpl. exists (mkApps (trans U) (map trans l)), (trans x).
  clear. revert U x ; induction l. simpl. reflexivity.
  simpl. intros.
  rewrite mkApps_app. simpl. reflexivity.
Qed.

Derive Signature for SEq.eq_term_upto_univ_napp.

(* Lemma leq_term_mkApps {cf} ϕ t u t' u' :
  eq_term Σ ϕ t t' -> All2 (eq_term Σ ϕ) u u' ->
  leq_term Σ ϕ (mkApps t u) (mkApps t' u').
Proof.
  intros Hn Ht.
  revert t t' Ht Hn; induction u in u' |- *; intros.

  inversion_clear Ht.
  simpl. apply eq_term_leq_term. assumption.

  inversion_clear Ht.
  simpl in *. apply IHu. assumption. constructor; auto.
  now apply eq_term_eq_term_napp.
Qed. *)

(* Lemma eq_term_upto_univ_App `{checker_flags} Re Rle f f' napp :
  eq_term_upto_univ_napp Σ Re Rle napp f f' ->
  isApp f = isApp f'.
Proof.
  inversion 1; reflexivity.
Qed.

Lemma eq_term_upto_univ_mkApps `{checker_flags} Re Rle f l f' l' :
  eq_term_upto_univ_napp Σ Re Rle #|l| f f' ->
  All2 (eq_term_upto_univ Σ Re Re) l l' ->
  eq_term_upto_univ Σ Re Rle (mkApps f l) (mkApps f' l').
Proof.
  induction l in f, f', l' |- *; intro e; inversion_clear 1.
  - assumption.
  - pose proof (eq_term_upto_univ_App _ _ _ _ _ e).
    case_eq (isApp f).
    + intro X; rewrite X in H0.
      destruct f; try discriminate.
      destruct f'; try discriminate.
      cbn. inversion_clear e. eapply IHl.
      * repeat constructor ; eauto.
      * assumption.
    + intro X; rewrite X in H0. simpl.
      eapply IHl.
      * constructor. all: eauto.
      * assumption.
Qed. *)

End Translation.

(*Section Trans_Weakening.
  Context {cf : checker_flags}.
  Context {Σ : Ast.Env.global_env}.
  Context {wfΣ : Typing.wf Σ}.
  Notation Σ' := (trans_global_decls Σ).

  Lemma trans_weaken t : 
    Typing.extends Σ Σ' ->

    trans Σ t = trans Σ' t.


 *)

Derive Signature for Typing.on_global_env.

Section Trans_Global.
  Context {cf : checker_flags}.
  Context (Σ : Ast.Env.global_env).
  Notation Σ' := (trans_global_decls Σ).
  Context (wfΣ : Typing.wf Σ).
  Context (wfΣ' : wf Σ').

  Lemma forall_decls_declared_constant cst decl :
    Ast.declared_constant Σ cst decl ->
    declared_constant Σ' cst (trans_constant_body Σ' decl).
  Proof.
    unfold declared_constant, Ast.declared_constant.
    now rewrite trans_lookup => -> /=.
  Qed.

  Lemma forall_decls_declared_minductive cst decl :
    Ast.declared_minductive Σ cst decl ->
    declared_minductive (trans_global_decls Σ) cst (trans_minductive_body Σ' decl).
  Proof.
    unfold declared_minductive, Ast.declared_minductive.
    now rewrite trans_lookup => -> /=.
  Qed.

  Lemma forall_decls_declared_inductive ind mdecl idecl :
    Ast.declared_inductive Σ ind mdecl idecl ->
    declared_inductive Σ' ind (trans_minductive_body Σ' mdecl) (trans_one_ind_body Σ' idecl).
  Proof.
    unfold declared_inductive, Ast.declared_inductive.
    move=> [decl' Hnth].
    pose proof (forall_decls_declared_minductive _ _ decl').
    eexists. eauto.
    now rewrite nth_error_map Hnth.
  Qed.

  Lemma forall_decls_declared_constructor cst mdecl idecl cdecl :
    Ast.declared_constructor Σ cst mdecl idecl cdecl ->
    declared_constructor Σ' cst (trans_minductive_body Σ' mdecl) (trans_one_ind_body Σ' idecl)
        (trans_constructor_body Σ' cdecl).
  Proof.
    unfold declared_constructor, Ast.declared_constructor.
    move=> [decl' Hnth].
    pose proof (forall_decls_declared_inductive _ _ _ decl'). split; auto.
    by rewrite nth_error_map Hnth.
  Qed.

  Lemma forall_decls_declared_projection cst mdecl idecl cdecl pdecl :
    Ast.declared_projection Σ cst mdecl idecl cdecl pdecl ->
    declared_projection (trans_global_decls Σ) cst (trans_minductive_body Σ' mdecl) (trans_one_ind_body Σ' idecl)
      (trans_constructor_body Σ' cdecl)  ((fun '(x, y) => (x, trans Σ' y)) pdecl).
  Proof.
    unfold declared_constructor, Ast.declared_constructor.
    move=> [decl' [Hnth Hnpar]].
    pose proof (forall_decls_declared_constructor _ _ _ _ decl'). split; auto.
    by rewrite nth_error_map Hnth.
  Qed.
End Trans_Global.

Lemma on_global_env_impl `{checker_flags} Σ P Q :
  (forall Σ Γ t T, ST.on_global_env P Σ.1 -> P Σ Γ t T -> Q Σ Γ t T) ->
  ST.on_global_env P Σ -> ST.on_global_env Q Σ.
Proof.
  apply on_global_env_impl.
Qed.

Lemma typing_wf_wf {cf}:
  forall (Σ : Ast.Env.global_env),
    ST.wf Σ ->
    ST.Forall_decls_typing
      (fun (Σ : Ast.Env.global_env_ext) (_ : Ast.Env.context) (t T : Ast.term) => WfAst.wf Σ.1 t × WfAst.wf Σ.1 T) Σ.
Proof.
  intros Σ.
  eapply on_global_env_impl. clear.
  intros Σ' Γ t T.
  red. unfold ST.lift_typing.
  intros ong. destruct T.
  * intros ty. now eapply typing_wf.
  * intros [s ty]. exists s.
    now eapply typing_wf in ty.
Qed.

Lemma declared_inductive_inj {Σ mdecl mdecl' ind idecl idecl'} :
  Ast.declared_inductive Σ ind mdecl' idecl' ->
  Ast.declared_inductive Σ ind mdecl idecl ->
  mdecl = mdecl' /\ idecl = idecl'.
Proof.
  intros [] []. unfold Ast.declared_minductive in *.
  rewrite H in H1. inversion H1. subst. rewrite H2 in H0. inversion H0. eauto.
Qed.

Lemma lookup_inductive_None Σ ind : lookup_inductive Σ ind = None ->
    ~ (exists mdecl idecl, declared_inductive Σ ind mdecl idecl).
Proof.
  intros hl [mdecl [idecl [decli hnth]]].
  unfold declared_inductive, declared_minductive in decli.
  unfold lookup_inductive, lookup_minductive in hl.
  destruct lookup_env eqn:heq. noconf decli. cbn in hl.
  destruct nth_error; congruence. congruence.
Qed.

Section Trans_Global.
  Context {cf : checker_flags}.
  Context (Σ : Ast.Env.global_env).
  Notation Σ' := (trans_global_decls Σ).
  Context (wfΣ : Typing.wf Σ).
  Context (wfΣ' : wf Σ').

  Lemma trans_R_global_instance {Re Rle gref napp u u'} :
    SEq.R_global_instance Σ Re Rle gref napp u u' ->
    R_global_instance (trans_global_decls Σ) Re Rle gref napp u u'.
  Proof.
    unfold SEq.R_global_instance, SEq.global_variance.
    destruct gref; simpl; auto.
    - unfold R_global_instance, R_opt_variance; cbn.
      unfold lookup_inductive, lookup_minductive.
      unfold SEq.lookup_inductive, SEq.lookup_minductive.
      rewrite trans_lookup. destruct Ast.Env.lookup_env eqn:look => //; simpl.
      destruct g => /= //.
      rewrite nth_error_map.
      destruct nth_error eqn:hnth => /= //.
      assert (wfty : WfAst.wf Σ (Ast.Env.ind_type o)).
      { eapply declared_inductive_wf; eauto. eapply typing_wf_wf; eauto. split; eauto. }
      generalize (trans_destArity Σ [] (Ast.Env.ind_type o) wfty wfΣ').
      destruct AstUtils.destArity as [[ctx ps]|] eqn:eq' => /= // -> //.
      now rewrite context_assumptions_map.
    - unfold R_global_instance, R_opt_variance; cbn.
      unfold lookup_constructor, lookup_inductive, lookup_minductive.
      unfold SEq.lookup_constructor, SEq.lookup_inductive, SEq.lookup_minductive.
      rewrite trans_lookup. destruct Ast.Env.lookup_env => //; simpl.
      destruct g => /= //. rewrite nth_error_map.
      destruct nth_error => /= //.
      rewrite nth_error_map.
      destruct nth_error => /= //.
  Qed.

  Lemma eq_binder_annot_eq_context_gen_set_binder_name Γ Γ' Δ :
    All2 eq_binder_annot Γ Γ' ->
    eq_context_gen eq eq (map2 set_binder_name Γ Δ) (map2 set_binder_name Γ' Δ).
  Proof.
    induction 1 in Δ |- *.
    - constructor.
    - destruct Δ; cbn; constructor; auto.
      destruct c as [na [b|] ty]; cbn; constructor; auto.
  Qed.

  Lemma map2_map_map {A B C D E} (f : C -> A) (g : D -> B) (h : A -> B -> E) l l':
    map2 h (map f l) (map g l') = map2 (fun x y => h (f x) (g y)) l l'.
  Proof.
    induction l in l' |- *; destruct l'; cbn; f_equal; auto.
  Qed.

  Lemma All2_map2 {A B C} (P : A -> A -> Type) (x : list C) (f : C -> B -> A) (l l' : list B) :
    All3 (fun x y z => P (f x y) (f x z)) x l l' ->
    All2 P (map2 f x l) (map2 f x l').
  Proof.
    induction 1; cbn; constructor; auto.
  Qed.

  Lemma All2_All2_All2_All3 {A B C} (P : A -> B -> C -> Type) (Q : A -> B -> Type) (Q' : A -> C -> Type) 
    (R : B -> C -> Type)
    (x : list A) (l : list B) (l' : list C):
    All2 Q x l -> All2 Q' x l' -> All2 R l l' ->
    (forall x y z, Q x y -> Q' x z -> R y z -> P x y z) ->
    All3 P x l l'.
  Proof.
    induction 1 in l' |- *; intros H; depelim H; intros H'; depelim H'; cbn; constructor; auto.
  Qed.

  (* TODO update Template Coq's eq_term to reflect PCUIC's cumulativity *)
  Lemma trans_eq_term_upto_univ {Re Rle t u napp} :
    RelationClasses.subrelation Re Rle ->
    WfAst.wf Σ t ->
    WfAst.wf Σ u ->
    SEq.eq_term_upto_univ_napp Σ Re Rle napp t u ->
    eq_term_upto_univ_napp (trans_global_decls Σ) Re Rle napp (trans (trans_global_decls Σ) t) (trans (trans_global_decls Σ) u).
  Proof.
    intros sub wt wu e.
    induction t using Induction.term_forall_list_rect in sub, Rle, napp, wt, u, wu, e |- *.
    all: invs e; cbn.
    all: try solve [ constructor ; auto ].
    all: repeat (match goal with 
      | H : WfAst.wf _ (_ _) |- _ => apply WfAst.wf_inv in H; simpl in H
      | H : _ /\ _ |- _ => destruct H
    end).
    all: try solve [
      repeat constructor ; auto ;
      match goal with
      | ih : forall Rle (u : Ast.term) (napp : nat), _ |- _ =>
        now eapply ih
      end
    ].
    - constructor.
      solve_all. eapply a; auto. tc.
    - eapply eq_term_upto_univ_napp_mkApps.
      + rewrite map_length. now eapply IHt.
      + destruct wt, wu. solve_all. eapply a0; auto; tc.
    - constructor. apply trans_R_global_instance; auto.
    - constructor. apply trans_R_global_instance; auto.
    - red in X, X0.
      destruct wt as [mdecl' [idecl' [decli hpctx lenpar eqpars eqret eqc eqbrs]]].
      destruct wu as [mdecl'' [idecl'' [decli' hpctx' lenpars' eqpars' eqret' eqc' eqbrs']]].
      destruct (declared_inductive_inj decli decli'). subst.
      eapply forall_decls_declared_inductive in decli; tea.
      destruct lookup_inductive as [[mdecl idecl]|] eqn:hl => //.
      2:{ eapply lookup_inductive_None in hl. elim hl. eauto. }
      apply lookup_inductive_declared in hl.
      destruct (PCUICGlobalEnv.declared_inductive_inj decli hl). subst.
      destruct X.
      constructor. all: try solve [
        match goal with
        | ih : forall Rle u, _ |- _ =>
          now eapply ih
        end
      ].
      unfold trans_predicate, eq_predicate; cbn.
      repeat split; solve_all; try typeclasses eauto with typeclass_instances core.
      * rewrite map2_map2_bias_left; len.
        eapply All2_length in hpctx. len in hpctx.
        rewrite map2_map2_bias_left; len.
        eapply All2_length in hpctx'. len in hpctx'.
        now eapply eq_binder_annot_eq_context_gen_set_binder_name.
      * rewrite !map2_map_map.
        eapply All2_map2. cbn.
        eapply All2_All_mix_right in eqbrs; tea.
        eapply All2_All2_All2_All3; tea.
        cbn. intros cdecl br br' [[eq wfb] IH] [eq' wfb'] [eqbs eqbods].
        split.
        { rewrite map2_map2_bias_left; len.
          eapply All2_length in eq. now len in eq.
          rewrite map2_map2_bias_left; len.
          eapply All2_length in eq'. now len in eq'.
          now eapply eq_binder_annot_eq_context_gen_set_binder_name. }
        eapply IH; eauto; tc.

    - constructor.
      assert (
        w1 :
          All (fun def =>
            WfAst.wf Σ (dtype def) ×
            WfAst.wf Σ (dbody def)
          ) m
      ).
      { solve_all. }
      assert (
        w2 :
          All (fun def =>
            WfAst.wf Σ (dtype def) ×
            WfAst.wf Σ (dbody def)) mfix'
      ).
      { solve_all. }
      pose proof (All2_All_mix_left X X0) as h1. simpl in h1.
      pose proof (All2_All_mix_left w1 h1) as h2.
      pose proof (All2_All_mix_right w2 h2) as h3.
      simpl in h3.
      eapply All2_map.
      eapply All2_impl. 1: exact h3.
      simpl.
      intros [? ? ? ?] [? ? ? ?] [[[? ?] [[ih1 ih2] [? ?]]] [? ?]].
      simpl in *.
      intuition eauto. now eapply ih1. now eapply ih2.
    - constructor.
      assert (
        w1 :
          All (fun def => WfAst.wf Σ (dtype def) × WfAst.wf Σ (dbody def)) m
      ).
      { solve_all. }
      assert (
        w2 :
          All (fun def => WfAst.wf Σ (dtype def) * WfAst.wf Σ (dbody def)) mfix'
      ).
      { solve_all. }
      pose proof (All2_All_mix_left X X0) as h1. simpl in h1.
      pose proof (All2_All_mix_left w1 h1) as h2.
      pose proof (All2_All_mix_right w2 h2) as h3.
      simpl in h3.
      eapply All2_map.
      eapply All2_impl. 1: exact h3.
      simpl.
      intros [? ? ? ?] [? ? ? ?] [[[? ?] [[ih1 ih2] [? ?]]] [? ?]].
      simpl in *.
      intuition eauto. now eapply ih1. now eapply ih2.
  Qed.

  Lemma trans_leq_term ϕ T U :
    WfAst.wf Σ T -> WfAst.wf Σ U -> SEq.leq_term Σ ϕ T U ->
    leq_term (trans_global_decls Σ) ϕ (trans Σ' T) (trans Σ' U).
  Proof.
    intros HT HU H.
    eapply trans_eq_term_upto_univ ; eauto. tc.
  Qed.

  Lemma trans_eq_term φ t u :
    WfAst.wf Σ t -> WfAst.wf Σ u -> SEq.eq_term Σ φ t u ->
    eq_term (trans_global_decls Σ) φ (trans Σ' t) (trans Σ' u).
  Proof.
    intros HT HU H.
    eapply trans_eq_term_upto_univ ; eauto. tc.
  Qed.

  Lemma trans_eq_term_list {φ l l'} :
      All (WfAst.wf Σ) l ->
      All (WfAst.wf Σ) l' ->
      All2 (SEq.eq_term Σ φ) l l' ->
      All2 (eq_term (trans_global_decls Σ) φ) (List.map (trans Σ') l) (List.map (trans Σ') l').
  Proof.
    intros w w' h.
    eapply All2_map.
    pose proof (All2_All_mix_left w h) as h1.
    pose proof (All2_All_mix_right w' h1) as h2.
    simpl in h2.
    apply (All2_impl h2).
    intuition auto using trans_eq_term.
  Qed.
  
  Lemma trans_nth n l x : trans Σ' (nth n l x) = nth n (List.map (trans Σ') l) (trans Σ' x).
  Proof.
    induction l in n |- *; destruct n; trivial.
    simpl in *. congruence.
  Qed.
  
  Lemma trans_extended_subst Γ k :
    map (trans Σ') (Ast.Env.extended_subst Γ k) = extended_subst (trans_local Σ' Γ) k.
  Proof.
    induction Γ in k |- *; cbn; auto.
    destruct a as [na [b|] ty] => /= //; try congruence.
    * f_equal => //. rewrite trans_subst trans_lift IHΓ. f_equal => //.
      len. now rewrite context_assumptions_map.
    * now f_equal.
  Qed.
  
  Lemma trans_expand_lets_k Γ k t :
    trans Σ' (Ast.Env.expand_lets_k Γ k t) = expand_lets_k (trans_local Σ' Γ) k (trans Σ' t).
  Proof.
    rewrite /Ast.Env.expand_lets /Ast.Env.expand_lets_k.
    rewrite trans_subst trans_lift /expand_lets /expand_lets_k.
    rewrite trans_extended_subst. f_equal. len.
    now rewrite context_assumptions_map.
  Qed.

  Lemma trans_expand_lets Γ t :
    trans Σ' (Ast.Env.expand_lets Γ t) = expand_lets (trans_local Σ' Γ) (trans Σ' t).
  Proof.
    now rewrite /Ast.Env.expand_lets trans_expand_lets_k.
  Qed.

  Lemma trans_subst_context s k Γ :
    trans_local Σ' (Ast.Env.subst_context s k Γ) =
    subst_context (map (trans Σ') s) k (trans_local Σ' Γ).
  Proof.
    induction Γ.
    * cbn; auto.
    * simpl. rewrite subst_context_snoc Ast.Env.subst_context_snoc /= /snoc /subst_decl.
      len. f_equal => //.
      rewrite /map_decl /trans_decl /=.
      destruct a as [na [b|] ty]; cbn.
      f_equal. f_equal. rewrite trans_subst. now len.
      now rewrite trans_subst.
      f_equal.
      now rewrite trans_subst.
  Qed.
  
  Lemma trans_lift_context n k Γ :
    trans_local Σ' (Ast.Env.lift_context n k Γ) =
    lift_context n k (trans_local Σ' Γ).
  Proof.
    induction Γ.
    * cbn; auto.
    * simpl. rewrite !lift_context_snoc PCUICLiftSubst.lift_context_snoc /= /snoc /subst_decl.
      f_equal => //.
      rewrite /lift_decl /map_decl /trans_decl /=.
      destruct a as [na [b|] ty]; cbn.
      f_equal. f_equal. all:rewrite trans_lift; len => //.
  Qed.

  Lemma trans_expand_lets_ctx Γ Δ :
    trans_local Σ' (Ast.Env.expand_lets_ctx Γ Δ) = expand_lets_ctx (trans_local Σ' Γ) (trans_local Σ' Δ).
  Proof.
    rewrite /Ast.Env.expand_lets_ctx /Ast.Env.expand_lets_k_ctx.
    rewrite trans_subst_context trans_lift_context /expand_lets_ctx /expand_lets_k_ctx.
    rewrite trans_extended_subst. f_equal. len.
    now rewrite context_assumptions_map.
  Qed.

  Lemma trans_smash_context Γ Δ : trans_local Σ' (Ast.Env.smash_context Γ Δ) = smash_context (trans_local Σ' Γ) (trans_local Σ' Δ).
  Proof.
    induction Δ in Γ |- *; simpl; auto.
    destruct a as [na [b|] ty] => /=.
    rewrite IHΔ. f_equal.
    now rewrite (trans_subst_context [_]).
    rewrite IHΔ. f_equal. rewrite /trans_local map_app //.
  Qed.
  
  Lemma map_decl_subst_instance_set_binder_name i x y :
    map_decl (subst_instance i) (set_binder_name x y) = 
    set_binder_name x (map_decl (subst_instance i) y).
  Proof.
    now rewrite /map_decl /set_binder_name /=.
  Qed.
  
  Lemma map2_trans l l' :
    map2
      (fun (x : aname) (y : BasicAst.context_decl Ast.term) =>
        trans_decl Σ' (Ast.Env.set_binder_name x y)) l l' =
    map2 (fun (x : aname) (y : BasicAst.context_decl Ast.term) =>
      set_binder_name x (trans_decl Σ' y)) l l'.
  Proof.
    eapply map2_ext.
    intros x y. rewrite /trans_decl. now destruct y; cbn.
  Qed.
  
  Lemma map_map_comm {A B B' C} (f : B -> C) (g : A -> B) (f' : B' -> C) (g' : A -> B') (l : list A) : 
    (forall x, f (g x) = f' (g' x)) ->
    map f (map g l) = map f' (map g' l).
  Proof.
    intros Hfg.
    induction l; cbn; auto.
    now rewrite Hfg IHl.
  Qed.

  Lemma trans_cstr_branch_context ind mdecl cdecl :
    let mdecl' := trans_minductive_body Σ' mdecl in
    let cdecl' := trans_constructor_body Σ' cdecl in
    map (trans_decl Σ') (Ast.cstr_branch_context ind mdecl cdecl) =
    cstr_branch_context ind mdecl' cdecl'.
  Proof.
    cbn; intros.
    rewrite /Ast.cstr_branch_context /cstr_branch_context.
    rewrite [map _ _]trans_expand_lets_ctx. f_equal.
    rewrite trans_subst_context. f_equal.
    2:now repeat len.
    rewrite trans_inds //.
  Qed.

  Lemma trans_iota_red ind mdecl idecl cdecl pars p args br :
    let bctx := Ast.case_branch_context ind mdecl cdecl p br in
    let p' := Ast.map_predicate id (trans Σ') (trans Σ') p in
    let mdecl' := trans_minductive_body Σ' mdecl in
    let idecl' := trans_one_ind_body Σ' idecl in
    let cdecl' := trans_constructor_body Σ' cdecl in
    let p' := trans_predicate ind mdecl' idecl' p'.(Ast.pparams) p'.(Ast.puinst) p'.(Ast.pcontext) p'.(Ast.preturn) in
    #|Ast.bcontext br| = #|Ast.Env.cstr_args cdecl| ->
    trans Σ' (ST.iota_red pars args bctx br) =
    iota_red pars p' (List.map (trans Σ') args) 
      (let br' := Ast.map_branch (trans Σ') br in
        trans_branch ind mdecl' cdecl' br'.(Ast.bcontext) br'.(Ast.bbody)).
  Proof.
    intros.
    unfold ST.iota_red, iota_red.
    rewrite /map_predicate /=.
    rewrite trans_subst map_rev map_skipn. f_equal.
    rewrite trans_expand_lets. f_equal.
    rewrite /bctx /id. rewrite /Ast.case_branch_context /Ast.case_branch_context_gen.
    rewrite /inst_case_branch_context. cbn.
    rewrite /inst_case_context.
    rewrite map2_map2_bias_left; len.
    rewrite /subst_context /id /subst_instance /subst_instance_context
      /map_context map_map2.
    change (map2
    (fun (x : aname) (y : context_decl) =>
     map_decl (subst_instance (Ast.puinst p)) (set_binder_name x y)))
     with 
     (map2
     (fun (x : aname) (y : context_decl) =>
      set_binder_name x (map_decl (subst_instance (Ast.puinst p)) y))).
    rewrite -PCUICUnivSubstitutionConv.map2_map_r.
    rewrite -[fold_context_k _ _]PCUICRenameConv.map2_set_binder_name_fold; len.
    rewrite /trans_local map_map2 map2_trans.
    rewrite -PCUICUnivSubstitutionConv.map2_map_r. f_equal.
    rewrite [map _ _]trans_subst_context map_rev.
    rewrite /subst_context. f_equal.
    rewrite /Ast.Env.subst_instance_context /map_context.
    rewrite /trans_local.
    rewrite (map_map_comm _ _ (map_decl (subst_instance (Ast.puinst p))) (trans_decl Σ')).
    intros x. rewrite /map_decl /trans_decl; cbn.
    rewrite trans_subst_instance. f_equal.
    destruct (decl_body x) => /= //.
    now rewrite trans_subst_instance.
    f_equal.
    now rewrite trans_cstr_branch_context.
  Qed.

  Lemma trans_isLambda t :
    WfAst.wf Σ t -> isLambda (trans Σ' t) = Ast.isLambda t.
  Proof.
    destruct 1; cbnr.
    destruct u; [contradiction|]. cbn.
    generalize (map (trans Σ') u) (trans Σ' t) (trans Σ' t0); clear.
    induction l; intros; cbnr. apply IHl.
    destruct lookup_inductive as [[]|] => //.
  Qed.

  Lemma trans_unfold_fix mfix idx narg fn :
    All (fun def : def Ast.term => WfAst.wf Σ (dtype def) * WfAst.wf Σ (dbody def)) mfix ->
    ST.unfold_fix mfix idx = Some (narg, fn) ->
    unfold_fix (map (map_def (trans Σ') (trans Σ')) mfix) idx = Some (narg, trans Σ' fn).
  Proof.
    unfold ST.unfold_fix, unfold_fix. intros wffix.
    rewrite nth_error_map. destruct (nth_error mfix idx) eqn:Hdef => //.
    cbn.
    intros [= <- <-]. simpl.
    repeat f_equal.
    rewrite trans_subst.
    f_equal. clear Hdef.
    unfold fix_subst, ST.fix_subst. rewrite map_length.
    generalize mfix at 1 3.
    induction wffix; trivial.
    simpl; intros mfix. f_equal.
    eapply (IHwffix mfix).
  Qed.

  Lemma trans_unfold_cofix mfix idx narg fn :
    All (fun def : def Ast.term => WfAst.wf Σ (dtype def) * WfAst.wf Σ (dbody def)) mfix ->
    ST.unfold_cofix mfix idx = Some (narg, fn) ->
    unfold_cofix (map (map_def (trans Σ') (trans Σ')) mfix) idx = Some (narg, trans Σ' fn).
  Proof.
    unfold ST.unfold_cofix, unfold_cofix. intros wffix.
    rewrite nth_error_map. destruct (nth_error mfix idx) eqn:Hdef.
    intros [= <- <-]. simpl. repeat f_equal.
    rewrite trans_subst.
    f_equal. clear Hdef.
    unfold cofix_subst, ST.cofix_subst. rewrite map_length.
    generalize mfix at 1 3.
    induction wffix; trivial.
    simpl; intros mfix. f_equal.
    eapply (IHwffix mfix). congruence.
  Qed.

  Definition isApp t := match t with tApp _ _ => true | _ => false end.

  Lemma trans_is_constructor:
    forall (args : list Ast.term) (narg : nat),
      ST.is_constructor narg args = true -> is_constructor narg (map (trans Σ') args) = true.
  Proof.
    intros args narg.
    unfold ST.is_constructor, is_constructor.
    rewrite nth_error_map. destruct nth_error. simpl. intros.
    destruct t; try discriminate || reflexivity. simpl in H.
    destruct t; try discriminate || reflexivity.
    simpl. unfold isConstruct_app.
    unfold decompose_app. rewrite decompose_app_rec_mkApps. now simpl.
    congruence.
  Qed.

  Lemma refine_red1_r Σg Γ t u u' : u = u' -> red1 Σg Γ t u -> red1 Σg Γ t u'.
  Proof.
    intros ->. trivial.
  Qed.

  Lemma refine_red1_Γ Σg Γ Γ' t u : Γ = Γ' -> red1 Σg Γ t u -> red1 Σg Γ' t u.
  Proof.
    intros ->. trivial.
  Qed.
  Ltac wf_inv H := try apply WfAst.wf_inv in H; simpl in H; rdest.

  Lemma wf_wf_decl_pred : Typing.on_global_env (fun Σ => WfAst.wf_decl_pred Σ.1) Σ.
  Proof.
    move: (typing_wf_wf _ wfΣ).
    eapply on_global_env_impl.
    intros.
    destruct T; simpl in *; auto.
    destruct X0 as [s [Ht Hs]].
    red. split; auto.
  Qed.
  Hint Resolve wf_wf_decl_pred : wf.

  Lemma nth_error_map2 {A B C} (f : A -> B -> C) n l l' a b :
    nth_error l n = Some a ->
    nth_error l' n = Some b ->
    nth_error (map2 f l l') n = Some (f a b).
  Proof.
    induction l in n, l' |- *; destruct l', n; cbn; auto; try congruence.
  Qed.

  Lemma cstr_branch_context_assumptions ci mdecl cdecl :
    context_assumptions (cstr_branch_context ci mdecl cdecl) = 
    context_assumptions cdecl.(cstr_args).
  Proof.
    rewrite /cstr_branch_context /expand_lets_ctx /expand_lets_k_ctx.
    now rewrite !context_assumptions_fold.
  Qed.
  
  Lemma Ast_cstr_branch_context_assumptions ci mdecl cdecl :
    Ast.Env.context_assumptions (Ast.cstr_branch_context ci mdecl cdecl) = 
    Ast.Env.context_assumptions cdecl.(Ast.Env.cstr_args).
  Proof.
    rewrite /cstr_branch_context /expand_lets_ctx /expand_lets_k_ctx.
    now rewrite !Ast.Env.context_assumptions_fold.
  Qed.
  
  Lemma map2_set_binder_name_context_assumptions (l : list aname) (l' : Ast.Env.context) :
    #|l| = #|l'| ->
    Ast.Env.context_assumptions (map2 Ast.Env.set_binder_name l l') = Ast.Env.context_assumptions l'.
  Proof.
    induction l in l' |- *; destruct l'; cbn => //.
    intros [=]. destruct decl_body => //; eauto.
    f_equal; auto.
  Qed.

  Lemma Ast_inst_case_context_length pars puinst ctx :
    #|Ast.inst_case_context pars puinst ctx| = #|ctx|.
  Proof.
    rewrite /Ast.inst_case_context. now len.
  Qed.
  Hint Rewrite Ast_inst_case_context_length : len.

  Lemma Ast_inst_case_context_assumptions pars puinst ctx :
    Ast.Env.context_assumptions (Ast.inst_case_context pars puinst ctx) = 
    Ast.Env.context_assumptions ctx.
  Proof.
    rewrite /Ast.inst_case_context.
    rewrite !Ast.Env.context_assumptions_fold.
    now rewrite Ast.Env.context_assumptions_map.
  Qed.

  Lemma case_branch_context_assumptions ci mdecl cdecl p br :
    #|Ast.bcontext br| = #|Ast.Env.cstr_args cdecl| ->
    Ast.Env.context_assumptions (Ast.case_branch_context ci mdecl cdecl p br) = 
    Ast.Env.context_assumptions cdecl.(Ast.Env.cstr_args).
  Proof.
    intros.
    rewrite /Ast.case_branch_context /Ast.case_branch_context_gen; len.
    rewrite map2_set_binder_name_context_assumptions; len.
  Qed.

  Lemma declared_inductive_lookup {ind mdecl idecl} : 
    declared_inductive Σ' ind mdecl idecl -> 
    lookup_inductive Σ' ind = Some (mdecl, idecl).
  Proof.
    intros []. unfold lookup_inductive, lookup_minductive.
    now rewrite H H0.
  Qed.

  (* Require Import PCUICInductiveInversion. *)
  Lemma map2_cst {A B} (l : list A) (l' : list B) :
    #|l| = #|l'| ->
    map2 (fun x y => x) l l' = l.
  Proof.
    induction l in l' |- *; destruct l'; cbn; auto. congruence.
    intros [=]. f_equal; auto.
  Qed.

  Lemma trans_inst_case_context pars puinst ctx :
    trans_local Σ' (Ast.inst_case_context pars puinst ctx) = 
    inst_case_context (map (trans Σ') pars) puinst (trans_local Σ' ctx).
  Proof.    
    rewrite /Ast.inst_case_context /inst_case_context.
    now rewrite trans_subst_context map_rev trans_local_subst_instance.
  Qed.

  Lemma trans_local_app Γ Δ : trans_local Σ' (Ast.Env.app_context Γ Δ) = trans_local Σ' Γ ,,, trans_local Σ' Δ.
  Proof.
    now rewrite /trans_local map_app.
  Qed.

  Lemma trans_case_predicate_context (ci : case_info) mdecl idecl p :
    let bctx := Ast.case_predicate_context ci mdecl idecl p in
    let p' := Ast.map_predicate id (trans Σ') (trans Σ') p in
    let mdecl' := trans_minductive_body Σ' mdecl in
    let idecl' := trans_one_ind_body Σ' idecl in
    let p' := trans_predicate ci mdecl' idecl' p'.(Ast.pparams) p'.(Ast.puinst) p'.(Ast.pcontext) p'.(Ast.preturn) in
    #|Ast.pcontext p| = S #|Ast.Env.ind_indices idecl| ->
      (trans_local Σ' (Ast.case_predicate_context ci mdecl idecl p)) =
      (case_predicate_context ci mdecl' idecl' p').
  Proof.
    intros bctx p' mdecl' idecl' p'' eqp.
    rewrite /Ast.case_predicate_context /case_predicate_context /case_predicate_context_gen.
    rewrite /Ast.case_predicate_context_gen.
    rewrite /trans_local map_map2 map2_trans.
    rewrite -PCUICUnivSubstitutionConv.map2_map_r. f_equal.
    { cbn. rewrite map2_map2_bias_left; len.
      rewrite map_map2. cbn. rewrite map2_cst //.
      len. }
    rewrite /Ast.pre_case_predicate_context_gen /pre_case_predicate_context_gen.
    rewrite [map _ _]trans_inst_case_context. f_equal.
    rewrite /Ast.ind_predicate_context /ind_predicate_context /= /trans_decl.
    f_equal; cbn. f_equal.
    { rewrite trans_mkApps /=. f_equal.
      rewrite trans_reln /= /to_extended_list /to_extended_list_k. f_equal.
      rewrite trans_local_app trans_smash_context. f_equal.
      now rewrite trans_expand_lets_ctx. }
    now rewrite trans_expand_lets_ctx.
  Qed.
  
  Lemma trans_ind_predicate_context (Γ : list aname) ind mdecl idecl :
    let mdecl':= trans_minductive_body Σ' mdecl in
    let idecl':= trans_one_ind_body Σ' idecl in
    All2 (fun x y => eq_binder_annot x (decl_name y)) Γ (Ast.ind_predicate_context ind mdecl idecl) ->
    All2 (fun x y => eq_binder_annot x (decl_name y)) Γ (ind_predicate_context ind mdecl' idecl').
  Proof.
    intros.
    rewrite /Ast.ind_predicate_context in X.
    depelim X. constructor. now cbn in *.
    clear e.
    rewrite /mdecl' /idecl'. cbn.
    rewrite -trans_expand_lets_ctx. eapply All2_map_right.
    solve_all.
  Qed.
  
  Lemma trans_cstr_branch_context_alpha (Γ : list aname) ind mdecl cdecl :
    let mdecl' := trans_minductive_body Σ' mdecl in
    let cdecl' := trans_constructor_body Σ' cdecl in
    All2 (fun x y => eq_binder_annot x (decl_name y)) Γ 
      (Ast.cstr_branch_context ind mdecl cdecl) ->
    All2 (fun x y => eq_binder_annot x (decl_name y)) Γ 
      (cstr_branch_context ind mdecl' cdecl').
  Proof.
    intros.
    rewrite -trans_cstr_branch_context. eapply All2_map_right.
    eapply All2_impl; tea. now cbn.
  Qed.

   Lemma inst_case_predicate_context_eq (ci : case_info) mdecl idecl p :
    let bctx := Ast.case_predicate_context ci mdecl idecl p in
    let p' := Ast.map_predicate id (trans Σ') (trans Σ') p in
    let mdecl' := trans_minductive_body Σ' mdecl in
    let idecl' := trans_one_ind_body Σ' idecl in
    let p' := trans_predicate ci mdecl' idecl' p'.(Ast.pparams) p'.(Ast.puinst) p'.(Ast.pcontext) p'.(Ast.preturn) in
    WfAst.wf_nactx (Ast.pcontext p) (Ast.ind_predicate_context ci mdecl idecl) ->
    (trans_local Σ' (Ast.case_predicate_context ci mdecl idecl p)) =
    (inst_case_predicate_context p').
  Proof.
    intros.
    rewrite -(@inst_case_predicate_context_eq mdecl' idecl' ci p'0).
    2:{ apply trans_case_predicate_context.
        eapply All2_length in X; len in X. }
    rewrite /p'0. cbn.
    rewrite map2_map2_bias_left; len.
    eapply All2_length in X; len in X.
    apply eq_binder_annots_eq.
    now eapply trans_ind_predicate_context.
  Qed.

  Lemma trans_case_branch_context (ci : case_info) mdecl idecl cdecl p br :
    let bctx := Ast.case_predicate_context ci mdecl idecl p in
    let p' := Ast.map_predicate id (trans Σ') (trans Σ') p in
    let mdecl' := trans_minductive_body Σ' mdecl in
    let idecl' := trans_one_ind_body Σ' idecl in
    let cdecl' := trans_constructor_body Σ' cdecl in
    let p' := trans_predicate ci mdecl' idecl' p'.(Ast.pparams) p'.(Ast.puinst) p'.(Ast.pcontext) p'.(Ast.preturn) in
    let br' := trans_branch ci mdecl' cdecl' br.(Ast.bcontext) (trans Σ' br.(Ast.bbody)) in
    WfAst.wf_nactx (Ast.bcontext br) (Ast.cstr_branch_context ci mdecl cdecl) ->
    (trans_local Σ' (Ast.case_branch_context ci mdecl cdecl p br)) =
    case_branch_context ci mdecl' p' (forget_types (bcontext br')) cdecl'.
  Proof.
    intros.
    rewrite /Ast.case_branch_context /Ast.case_branch_context_gen.
    rewrite /case_branch_context /case_branch_context_gen /pre_case_branch_context_gen.
    rewrite /trans_local map_map2 map2_trans -PCUICUnivSubstitutionConv.map2_map_r.
    f_equal. cbn. rewrite map2_map2_bias_left.
    eapply All2_length in X. len in X. now len.
    rewrite map_map2 /= map2_cst //.
    eapply All2_length in X. len in X. now len.
    rewrite [map _ _]trans_inst_case_context. f_equal.
    now rewrite -trans_cstr_branch_context.
  Qed.

  Lemma inst_case_branch_context_eq (ci : case_info) mdecl idecl cdecl p br :
    let bctx := Ast.case_predicate_context ci mdecl idecl p in
    let p' := Ast.map_predicate id (trans Σ') (trans Σ') p in
    let mdecl' := trans_minductive_body Σ' mdecl in
    let idecl' := trans_one_ind_body Σ' idecl in
    let cdecl' := trans_constructor_body Σ' cdecl in
    let p' := trans_predicate ci mdecl' idecl' p'.(Ast.pparams) p'.(Ast.puinst) p'.(Ast.pcontext) p'.(Ast.preturn) in
    let br' := trans_branch ci mdecl' cdecl' br.(Ast.bcontext) (trans Σ' br.(Ast.bbody)) in
    WfAst.wf_nactx (Ast.bcontext br) (Ast.cstr_branch_context ci mdecl cdecl) ->
    (trans_local Σ' (Ast.case_branch_context ci mdecl cdecl p br)) =
    (inst_case_branch_context p' br').
  Proof.
    intros.
    rewrite -(@inst_case_branch_context_eq ci mdecl' cdecl' p'0 br').
    { cbn. rewrite map2_map2_bias_left. len.
      eapply All2_length in X. now len in X.
      eapply eq_binder_annots_eq.
      now eapply trans_cstr_branch_context_alpha. }
    now apply trans_case_branch_context.
  Qed.

  Lemma OnOne2_map2 {A B C} (P : A -> A -> Type) (f : B -> C -> A) l l' l'' :
    OnOne2All (fun x y z => P (f x y) (f x z)) l l' l'' ->
    OnOne2 P (map2 f l l') (map2 f l l'').
  Proof.
    induction 1; cbn; constructor; auto.
  Qed.

  Lemma OnOne2All_map2 {A B D} (P : D -> B -> B -> Type) 
    (f : B -> A -> D) (l : list A) (l' : list B) (l'' : list B) :
    #|l| = #|l'| ->
    OnOne2All P (map2 f l' l) l' l'' ->
    OnOne2All (fun x y z => P (f y x) y z) l l' l''.
  Proof.
    induction l' in l, l'' |- *; destruct l; cbn; intros hlen H; depelim H.
    constructor => //. lia.
    constructor => //. apply IHl' => //. lia.
  Qed.

  Lemma All2_nth_hyp {A B} (R : A -> B -> Type) l l' :
    All2 R l l' ->
    All2 (fun x y =>
      ∑ i, nth_error l i = Some x × R x y) l l'.
  Proof.
    intros a.
    induction a; constructor; auto.
    exists 0. cbn. auto.
    eapply (All2_impl IHa).
    intros ? ? [i hnth]. now exists (S i); cbn.
  Qed.

  (* 
  Lemma All2_OnOne2All_OnOne2 {A B C D} (P : A -> B -> Type) 
    (Q : C -> B -> B -> Type) (R : B -> B -> Type) la lb lc ld :
    All2 P la lb ->
    OnOne2All Q lc lb ld ->
    OnOne2   *)

  Lemma trans_red1 Γ T U :
    All (WfAst.wf_decl Σ) Γ ->
    WfAst.wf Σ T ->
    ST.red1 Σ Γ T U ->
    red1 Σ' (trans_local Σ' Γ) (trans Σ' T) (trans Σ' U).
  Proof.
    intros wfΓ Hwf.
    induction 1 using ST.red1_ind_all; wf_inv Hwf; simpl in *;
      try solve [econstructor; eauto].

    - simpl. wf_inv w. inv a0.
      rewrite trans_mkApps; auto.
      rewrite trans_subst; auto.
      apply red1_mkApps_f. constructor.

    - rewrite trans_subst; eauto. repeat constructor.

    - rewrite trans_lift; eauto.
      destruct nth_error eqn:Heq.
      econstructor. unfold trans_local. rewrite nth_error_map. rewrite Heq. simpl.
      destruct c; simpl in *. injection H; intros ->. simpl. reflexivity.
      econstructor. simpl in H. discriminate.

    - rewrite trans_mkApps; eauto with wf; simpl.
      destruct a as [isdecl hpctx lenpar wfpar wfret wfc wfbrs].
      destruct (declared_inductive_inj isdecl (proj1 H0)). subst x x0.
      eapply forall_decls_declared_inductive in isdecl; tea.
      rewrite (declared_inductive_lookup isdecl).
      eapply All2_nth_error in wfbrs as []; tea. 2:exact (proj2 H0).
      have lenbr := (All2_length a); len in lenbr.
      rewrite (trans_iota_red _ mdecl idecl cdecl) //.
      constructor. cbn.
      rewrite map2_map_map.
      etransitivity. eapply nth_error_map2; tea. eapply H0. reflexivity.
      unfold Ast.map_branch; cbn.
      rewrite map2_map2_bias_left; len.
      rewrite PCUICCases.map2_set_binder_name_context_assumptions; len.
      rewrite -map_skipn map_length H1 /bctx.
      rewrite case_branch_context_assumptions //; len.
      cbn. rewrite context_assumptions_map //.

    - simpl. rewrite trans_mkApps.
      eapply red_fix. wf_inv w.
      apply trans_unfold_fix; eauto.
      now apply trans_is_constructor.

    - destruct a as [isdecl hpctx lenpar wfpar wfret wfc wfbrs].
      eapply forall_decls_declared_inductive in isdecl; tea.
      rewrite (declared_inductive_lookup isdecl).
      apply WfAst.wf_mkApps_napp in wfc as []; auto.
      pose proof (unfold_cofix_wf _ _ _ _ _ H w). wf_inv w.
      rewrite !trans_mkApps; eauto with wf.
      apply trans_unfold_cofix in H; eauto with wf.
      eapply red_cofix_case; eauto.

    - eapply WfAst.wf_mkApps_napp in Hwf; auto.
      intuition. pose proof (unfold_cofix_wf _ _ _ _ _ H a). wf_inv a.
      rewrite !trans_mkApps; intuition eauto with wf.
      cbn.
      eapply red_cofix_proj; eauto.
      apply trans_unfold_cofix; eauto with wf.

    - rewrite trans_subst_instance. econstructor.
      apply (forall_decls_declared_constant _ wfΣ wfΣ' c decl H).
      now destruct decl as [na [b|] ty]; cbn; noconf H0.

    - rewrite trans_mkApps; eauto with wf.
      simpl. constructor. now rewrite nth_error_map H.

    - constructor. apply IHX. constructor; hnf; simpl; auto. hnf. auto.

    - constructor. apply IHX. constructor; hnf; simpl; auto. auto.

    - destruct a as [isdecl hpctx lenpar wfpar wfret wfc wfbrs].
      eapply forall_decls_declared_inductive in isdecl; tea.
      rewrite (declared_inductive_lookup isdecl).
      constructor. solve_all.
      apply OnOne2_map. apply (OnOne2_All_mix_left wfpar) in X. clear wfpar.
      solve_all.

    - destruct a as [isdecl' hpctx wfpar wfret wfc wfbrs].
      destruct (declared_inductive_inj isdecl isdecl').
      subst x x0.
      eapply forall_decls_declared_inductive in isdecl; tea.
      rewrite (declared_inductive_lookup isdecl).
      constructor. cbn. 
      rewrite trans_local_app in IHX.
      rewrite inst_case_predicate_context_eq in IHX => //.
      eapply All2_length in hpctx; len in hpctx.
      eapply IHX => //.
      eapply All_app_inv => //.
      eapply declared_inductive_wf_case_predicate_context => //.
    
    - destruct a as [isdecl hpctx wfpar wfret wfc wfbrs].
      eapply forall_decls_declared_inductive in isdecl; tea.
      rewrite (declared_inductive_lookup isdecl).
      constructor. cbn. apply IHX => //. 

    - destruct a as [isdecl' hpctx lenpar wfpar wfret wfc wfbrs].
      destruct (declared_inductive_inj isdecl isdecl').
      subst x x0.
      eapply forall_decls_declared_inductive in isdecl; tea.
      rewrite (declared_inductive_lookup isdecl).
      constructor.
      eapply OnOne2_map2.
      eapply All2_nth_hyp in wfbrs.
      rewrite /Ast.case_branches_contexts in X.
      eapply OnOne2All_map2 in X.
      2:{ now eapply All2_length in wfbrs. }
      cbn. eapply OnOne2All_map_all.
      eapply OnOne2All_All2_mix_left in X; tea.
      solve_all. red. rewrite b0. cbn. split => //.
      destruct b as [cstr [hnth [b wfbod]]].
      rewrite trans_local_app in b1.
      rewrite (inst_case_branch_context_eq _ mdecl idecl) in b1 => //.
      cbn in b1. rewrite b0 in b1. apply b1 => //.
      eapply All_app_inv => //.
      fold (Ast.case_branch_context ind mdecl i p y).
      assert (Ast.declared_constructor Σ (ind.(ci_ind), cstr) mdecl idecl i).
      { split; auto. }
      now eapply (declared_constructor_wf_case_branch_context H).

    - rewrite !trans_mkApps; auto with wf.
      eapply wf_red1 in X; auto with wf.
      eapply red1_mkApps_f; auto.

    - clear e w n. revert M1. induction X.
      simpl. intros. destruct p. specialize (r0 wfΓ).
      apply red1_mkApps_f.
      apply app_red_r. apply r0. now depelim a.
      inv a. intros. specialize (IHX X1).
      eapply (IHX (Template.Ast.tApp M1 [hd])).

    - constructor. apply IHX. constructor; hnf; simpl; auto. auto.
    - constructor. induction X; simpl; repeat constructor. apply p; auto. now inv Hwf.
      apply IHX. now inv Hwf.

    - constructor. constructor. eapply IHX; auto.
    - eapply refine_red1_r; [|constructor]. unfold subst1. simpl. now rewrite lift0_p.

    - constructor. apply OnOne2_map. repeat toAll.
      apply (OnOne2_All_mix_left Hwf) in X. clear Hwf.
      solve_all.
      red. rewrite <- !map_dtype. rewrite <- !map_dbody.
      inversion b0. clear b0.
      intuition eauto.
      unfold map_def. simpl. congruence.

    - apply fix_red_body. apply OnOne2_map. repeat toAll.
      apply (OnOne2_All_mix_left Hwf) in X.
      solve_all.
      red. rewrite <- !map_dtype. rewrite <- !map_dbody. intuition eauto.
      + unfold Ast.Env.app_context, trans_local in b.
        simpl in a. rewrite -> map_app in b.
        unfold app_context. unfold ST.fix_context in b.
        rewrite map_rev map_mapi in b. simpl in b.
        unfold fix_context. rewrite mapi_map. simpl.
        forward b.
        { clear b. solve_all. eapply All_app_inv; auto.
          apply All_rev. apply All_mapi.
          clear -Hwf; generalize 0 at 2; induction mfix0; constructor; hnf; simpl; auto.
          intuition auto. depelim a. simpl. depelim Hwf. simpl in *. intuition auto.
          now eapply WfAst.wf_lift.
          depelim a. simpl. depelim Hwf. simpl in *. intuition auto.
        }
        forward b by auto.
        eapply (refine_red1_Γ); [|apply b].
        f_equal. f_equal. apply mapi_ext; intros [] [].
        rewrite lift0_p. simpl. rewrite LiftSubst.lift0_p. reflexivity. cbn.
        rewrite /trans_decl /= /vass. f_equal.
        now rewrite trans_lift.
      + simpl; congruence.

    - constructor. apply OnOne2_map. repeat toAll.
      apply (OnOne2_All_mix_left Hwf) in X. clear Hwf.
      solve_all.
      red. rewrite <- !map_dtype. rewrite <- !map_dbody.
      inversion b0. clear b0.
      intuition eauto.
      unfold map_def. simpl. congruence.

    - apply cofix_red_body. apply OnOne2_map. repeat toAll.
      apply (OnOne2_All_mix_left Hwf) in X.
      solve_all.
      red. rewrite <- !map_dtype. rewrite <- !map_dbody. intuition eauto.
      + unfold Ast.Env.app_context, trans_local in b.
        simpl in a. rewrite -> map_app in b.
        unfold app_context. unfold ST.fix_context in b.
        rewrite map_rev map_mapi in b. simpl in b.
        unfold fix_context. rewrite mapi_map. simpl.
        forward b.
        { clear b. solve_all. eapply All_app_inv; auto.
          apply All_rev. apply All_mapi.
          clear -Hwf; generalize 0 at 2; induction mfix0; constructor; hnf; simpl; auto.
          intuition auto. depelim a. simpl. depelim Hwf. simpl in *. intuition auto.
          now eapply WfAst.wf_lift.
          depelim a. simpl. depelim Hwf. simpl in *. intuition auto.
        }
        forward b by auto.
        eapply (refine_red1_Γ); [|apply b].
        f_equal. f_equal. apply mapi_ext; intros [] [].
        rewrite lift0_p. simpl. rewrite LiftSubst.lift0_p. reflexivity.
        cbn. rewrite /trans_decl /vass /=.
        now rewrite trans_lift.
      + simpl; congruence.
  Qed.
End Trans_Global.

Lemma global_levels_trans Σ
  : global_levels (trans_global_decls Σ) = Ast.global_levels Σ.
Proof.
  induction Σ; simpl; auto.
  rewrite IHΣ. f_equal. clear.
  destruct a as [? []]; reflexivity.
Qed.

Lemma global_ext_levels_trans Σ
  : global_ext_levels (trans_global Σ) = Ast.global_ext_levels Σ.
Proof.
  destruct Σ.
  unfold trans_global, Ast.global_ext_levels, global_ext_levels; simpl.
  f_equal. clear u.
  now rewrite global_levels_trans.
Qed.

Lemma global_ext_constraints_trans Σ
  : global_ext_constraints (trans_global Σ) = Ast.global_ext_constraints Σ.
Proof.
  destruct Σ.
  unfold trans_global, Ast.global_ext_constraints, global_ext_constraints; simpl.
  f_equal. clear u.
  induction g.
  - reflexivity.
  - simpl. rewrite IHg. f_equal. clear.
    destruct a as [? []]; reflexivity.
Qed.

Lemma trans_conv {cf} (Σ : Ast.Env.global_env_ext) Γ T U :
  Typing.wf Σ.1 ->
  let Σ' := trans_global Σ in
  wf Σ' ->
  All (WfAst.wf_decl Σ.1) Γ ->
  WfAst.wf Σ.1 T -> WfAst.wf Σ.1 U -> ST.conv Σ Γ T U ->
  trans_global Σ ;;; trans_local Σ' Γ |- trans Σ' T = trans Σ' U.
Proof.
  intros wfΣ Σ' wfΣ'.
  induction 4.
  - constructor. 
    eapply trans_eq_term in e; eauto.
    now rewrite global_ext_constraints_trans.
  - eapply conv_red_l; tea. eapply trans_red1; tea. apply IHX2.
    eapply wf_red1 in r; tea. now eapply typing_wf_sigma in wfΣ. auto.
  - eapply conv_red_r; tea. 2:eapply trans_red1; tea.
    eapply IHX2. auto. eapply wf_red1 in r; tea. now eapply typing_wf_sigma; auto.
Qed.

Lemma trans_cumul {cf} (Σ : Ast.Env.global_env_ext) Γ T U :
  Typing.wf Σ.1 ->
  let Σ' := trans_global Σ in
  wf Σ' ->
  All (WfAst.wf_decl Σ.1) Γ ->
  WfAst.wf Σ.1 T -> WfAst.wf Σ.1 U -> ST.cumul Σ Γ T U ->
  trans_global Σ ;;; trans_local Σ' Γ |- trans Σ' T <= trans Σ' U.
Proof.
  intros wfΣ Σ' wfΣ'.
  induction 4.
  - constructor. 
    eapply trans_leq_term in l; eauto.
    now rewrite global_ext_constraints_trans.
  - eapply cumul_red_l; tea. eapply trans_red1; tea. apply IHX2.
    eapply wf_red1 in r; tea. now eapply typing_wf_sigma in wfΣ. auto.
  - eapply cumul_red_r; tea. 2:eapply trans_red1; tea.
    eapply IHX2. auto. eapply wf_red1 in r; tea. now eapply typing_wf_sigma; auto.
Qed.

Definition Tlift_typing (P : Ast.Env.global_env_ext -> Ast.Env.context -> Ast.term -> Ast.term -> Type) :=
  fun Σ Γ t T =>
    match T with
    | Some T => P Σ Γ t T
    | None => { s : Universe.t & P Σ Γ t (Template.Ast.tSort s) }
    end.

Definition TTy_wf_local {cf : checker_flags} Σ Γ := ST.All_local_env (ST.lift_typing ST.typing Σ) Γ.

Lemma trans_wf_local {cf}:
  forall (Σ : Ast.Env.global_env_ext) (Γ : Ast.Env.context) (wfΓ : TTy_wf_local Σ Γ),
    let P :=
        (fun Σ0 Γ0 _ (t T : Ast.term) _ =>
           let Σ' := trans_global Σ0 in
           wf Σ'.1 ->
           trans_global Σ0;;; trans_local Σ' Γ0 |- trans Σ' t : trans Σ' T)
    in
    let Σ' := trans_global Σ in
    wf Σ'.1 ->
    ST.All_local_env_over ST.typing P Σ Γ wfΓ ->
    wf_local (trans_global Σ) (trans_local Σ' Γ).
Proof.
  intros.
  induction X0.
  - simpl. constructor.
  - simpl. econstructor.
    + eapply IHX0.
    + simpl. destruct tu. exists x. now eapply p.
  - simpl. constructor; auto. red. destruct tu. exists x; auto.
    simpl. eauto.
Qed.

Lemma trans_wf_local_env {cf} Σ Γ :
  ST.All_local_env
        (ST.lift_typing
           (fun (Σ : Ast.Env.global_env_ext) Γ (b ty : Ast.term) =>
            let Σ' := trans_global Σ in
              ST.typing Σ Γ b ty × trans_global Σ;;; trans_local Σ' Γ |- trans Σ' b : trans Σ' ty) Σ)
        Γ ->
  wf_local (trans_global Σ) (trans_local (trans_global Σ) Γ).
Proof.
  intros.
  induction X.
  - simpl. constructor.
  - simpl. econstructor.
    + eapply IHX.
    + simpl. destruct t0. exists x. eapply p.
  - simpl. constructor; auto. red. destruct t0. exists x. intuition auto.
    red in t1. destruct t1. cbn. eapply p.
    red; red in t1. destruct t1. eapply t2.
Qed.

#[global]
Hint Resolve trans_wf_local : trans.

Axiom fix_guard_trans :
  forall Σ Γ mfix,
    ST.fix_guard Σ Γ mfix ->
    let Σ' := trans_global Σ in
    fix_guard Σ' (trans_local Σ' Γ) (map (map_def (trans Σ') (trans Σ')) mfix).

Axiom cofix_guard_trans :
  forall Σ Γ mfix,
    ST.cofix_guard Σ Γ mfix ->
    let Σ' := trans_global Σ in
    cofix_guard Σ' (trans_local Σ' Γ) (map (map_def (trans Σ') (trans Σ')) mfix).

Notation Swf_fix Σ def := (WfAst.wf Σ (dtype def) * WfAst.wf Σ (dbody def)).

Lemma trans_decompose_app {Σ t ind u l} : 
  WfAst.wf Σ t ->
  let Σ' := trans_global_decls Σ in
  AstUtils.decompose_app t = (Ast.tInd ind u, l) ->
  ∑ l', decompose_app (trans Σ' t) = (tInd ind u, l').
Proof.
  intros wft. destruct (AstUtils.decompose_app t) eqn:da.
  pose proof (TypingWf.decompose_app_inv _ _ [] _ _ wft da) as [n [napp [eqsk ->]]].
  intros Σ'. intros [= -> ->].
  rewrite trans_mkApps.
  rewrite decompose_app_mkApps //. eexists _; eauto.
Qed.

Lemma decompose_prod_assum_it_mkProd_or_LetIn ctx t ctx' t' :
  AstUtils.decompose_prod_assum ctx t = (ctx', t') ->
  Ast.Env.it_mkProd_or_LetIn ctx t = Ast.Env.it_mkProd_or_LetIn ctx' t'.
Proof.
  induction t in ctx, ctx', t' |- *; simpl; try intros [= -> <-]; auto.
  - intros H. now apply IHt2 in H.
  - intros H. now apply IHt3 in H.
Qed.

Lemma trans_decompose_prod_assum {Σ Σ'} ctx t :
  WfAst.wf Σ t ->
  let (ctx', t') := AstUtils.decompose_prod_assum ctx t in
  decompose_prod_assum (trans_local Σ' ctx) (trans Σ' t) = 
    (trans_local Σ' ctx', trans Σ' t').
Proof.
  intros wft; 
  induction wft in ctx |- * using WfAst.term_wf_forall_list_ind ; cbn; try intros [= <- <-]; auto.
  - apply IHwft0.
  - apply IHwft1.
  - rewrite mkApps_nonempty //.
    now destruct l => //.
  - cbn. destruct lookup_inductive as [[mdecl' idecl']| ]; cbn => //.
Qed.

Lemma wf_it_mkProd_or_LetIn Σ Γ t
  : WfAst.wf Σ (Ast.Env.it_mkProd_or_LetIn Γ t) <~> All (WfAst.wf_decl Σ) Γ * WfAst.wf Σ t.
Proof.
  revert t. induction Γ.
  - intros t. simpl. split => //; try split => //; trivial. now intros [].
  - intros t.
    destruct a as [na [b|] ty]; simpl in *. rewrite /Ast.Env.mkProd_or_LetIn /=.
    * etransitivity. eapply IHΓ. split; intros [].
      depelim w. intuition constructor; auto. split; auto. 
      depelim a. red in w. simpl in w. split; auto with wf. constructor; intuition auto.
    * etransitivity. eapply IHΓ => /=. split; intros [].
      depelim w. simpl in w1. split; [constructor|];auto.
      split; simpl; auto.
      depelim a. destruct w as [_ wfty]. simpl in wfty.
      split; auto. constructor; simpl; auto.
Qed.

Lemma trans_check_one_fix Σ mfix ind :
  let Σ' := trans_global_decls Σ in
  Swf_fix Σ mfix ->
  ST.check_one_fix mfix = Some ind ->
  check_one_fix (map_def (trans Σ') (trans Σ') mfix) = Some ind.
Proof.
  intros Σ'.
  unfold ST.check_one_fix, check_one_fix.
  case: mfix => [na ty arg rarg] /= [wfty wfarg].
  generalize (trans_decompose_prod_assum (Σ' := Σ') [] ty wfty) => /=.
  destruct AstUtils.decompose_prod_assum as [ctx p] eqn:dp => /= // ->.
  rewrite -(trans_smash_context Σ []) /trans_local.
  rewrite -List.map_rev nth_error_map.
  destruct nth_error eqn:hnth => /= //.
  destruct AstUtils.decompose_app eqn:da.
  destruct t => //.
  have [| l' eq] := (trans_decompose_app (Σ := Σ) _ da).
  { eapply decompose_prod_assum_it_mkProd_or_LetIn in dp.
    simpl in dp; subst ty.
    eapply wf_it_mkProd_or_LetIn in wfty as [wfctx _].
    eapply nth_error_all in hnth; cycle 1.
    eapply All_rev.
    pose proof (nth_error_Some_length hnth).
    rewrite nth_error_rev // List.rev_involutive in hnth.
    now apply wf_smash_context. apply hnth. }
  destruct c => /=. rewrite eq /= //.
Qed.

Lemma All_map_option_out_map_Some_spec {A B} {f g : A -> option B} {P : A -> Type} {l} :
  (forall x t, P x -> f x = Some t -> g x = Some t) ->
  All P l ->
  forall t,
  map_option_out (map f l) = Some t ->
  map_option_out (map g l) = Some t.
Proof.
  move => Hfg Hl. move: Hl.
  induction 1; try constructor; auto.
  simpl. move=> //.
  case E: (f x) => [b|] //.
  rewrite (Hfg _ _ p E).
  case E' : map_option_out => [b'|] //.
  move=> t [= <-]. now rewrite (IHHl _ E').
Qed.

Lemma map_option_out_check_one_fix {Σ mfix} :
  let Σ' := trans_global_decls Σ in
  All (fun def => (WfAst.wf Σ (dtype def) * WfAst.wf Σ (dbody def))) mfix ->
  forall l, 
  map_option_out (map (fun x => ST.check_one_fix x) mfix) = Some l ->
  map_option_out (map (fun x => check_one_fix (map_def (trans Σ') (trans Σ') x)) mfix) = Some l.
Proof.
  eapply All_map_option_out_map_Some_spec => x kn.
  apply trans_check_one_fix.
Qed.

Lemma trans_check_one_cofix Σ mfix ind :
  let Σ' := trans_global_decls Σ in
  Swf_fix Σ mfix ->
  ST.check_one_cofix mfix = Some ind ->
  check_one_cofix (map_def (trans Σ') (trans Σ') mfix) = Some ind.
Proof.
  intros Σ'. unfold ST.check_one_cofix, check_one_cofix.
  case: mfix => [na ty arg rarg] /= [wfty wfarg].
  move: (trans_decompose_prod_assum (Σ := Σ) (Σ' := Σ') [] ty wfty) => /=.
  destruct AstUtils.decompose_prod_assum as [ctx p] eqn:dp => /= // ->.
  destruct AstUtils.decompose_app eqn:da.
  destruct t => //.
  have [| l' ->] := (trans_decompose_app (Σ := Σ) _ da) => //.
  { eapply decompose_prod_assum_it_mkProd_or_LetIn in dp.
    simpl in dp; subst ty.
    now eapply wf_it_mkProd_or_LetIn in wfty as [_ wfp]. }
Qed.

Lemma map_option_out_check_one_cofix {Σ mfix} :
  let Σ' := trans_global_decls Σ in
  All (fun def => (WfAst.wf Σ (dtype def) * WfAst.wf Σ (dbody def))) mfix ->
  forall l, 
  map_option_out (map (fun x => ST.check_one_cofix x) mfix) = Some l ->
  map_option_out (map (fun x => check_one_cofix (map_def (trans Σ') (trans Σ') x)) mfix) = Some l.
Proof.
  apply All_map_option_out_map_Some_spec => x kn.
  apply trans_check_one_cofix.
Qed.

Lemma trans_check_rec_kind {cf} {Σ} {wfΣ : Typing.wf Σ} {wfΣ' : wf (trans_global_decls Σ)} {k f} :
  ST.check_recursivity_kind Σ k f = check_recursivity_kind (trans_global_decls Σ) k f.
Proof.
  unfold ST.check_recursivity_kind, check_recursivity_kind.
  rewrite trans_lookup.
  destruct Ast.Env.lookup_env as [[]|] => //.
Qed.

Lemma trans_wf_fixpoint {cf} {Σ} {wfΣ : Typing.wf Σ} {mfix} :
  let Σ' := trans_global_decls Σ in
  wf Σ' ->
  All (fun def => (WfAst.wf Σ (dtype def) * WfAst.wf Σ (dbody def))) mfix ->
  ST.wf_fixpoint Σ mfix ->
  wf_fixpoint (trans_global_decls Σ) (map (map_def (trans Σ') (trans Σ')) mfix).
Proof.
  intros Σ' wfΣ'.
  unfold ST.wf_fixpoint, wf_fixpoint.
  rewrite map_map_compose.
  intros wf.
  destruct map_option_out eqn:ma => //.
  rewrite (map_option_out_check_one_fix wf _ ma).
  destruct l; auto. now rewrite -trans_check_rec_kind.
Qed.

Lemma trans_wf_cofixpoint {cf} {Σ} {wfΣ : Typing.wf Σ} {mfix} :
  let Σ' := trans_global_decls Σ in
  wf Σ' ->
  All (fun def => (WfAst.wf Σ (dtype def) * WfAst.wf Σ (dbody def))) mfix ->
  ST.wf_cofixpoint Σ mfix ->
  wf_cofixpoint (trans_global_decls Σ) (map (map_def (trans Σ') (trans Σ')) mfix).
Proof.
  intros Σ' wfΣ'.
  unfold ST.wf_cofixpoint, wf_cofixpoint.
  rewrite map_map_compose.
  intros wf.
  destruct map_option_out eqn:ma => //.
  rewrite (map_option_out_check_one_cofix wf _ ma).
  destruct l; auto. now rewrite -trans_check_rec_kind.
Qed.

Lemma trans_global_decl_universes Σ d : 
  Ast.universes_decl_of_decl d = 
  universes_decl_of_decl (trans_global_decl Σ d).
Proof.
  destruct d; reflexivity.
Qed.

Lemma trans_consistent_instance_ext {cf:checker_flags} Σ d u : 
  let Σ' := trans_global Σ in
  Ast.consistent_instance_ext Σ (Ast.universes_decl_of_decl d) u ->
  consistent_instance_ext Σ' (universes_decl_of_decl (trans_global_decl Σ' d)) u.
Proof.
  intros Σ'. 
  unfold Ast.consistent_instance_ext, consistent_instance_ext.
  rewrite global_ext_levels_trans global_ext_constraints_trans.
  rewrite (trans_global_decl_universes Σ').
  trivial.
Qed.

Lemma eq_annots_expand_lets_ctx (Γ : list aname) (Δ Δ' : context) :
  eq_annots Γ (expand_lets_ctx Δ Δ') <-> eq_annots Γ Δ'.
Proof.
  rewrite /expand_lets_ctx /expand_lets_k_ctx.
  etransitivity. eapply eq_annots_subst_context.
  eapply eq_annots_lift_context.
Qed.

Lemma eq_annots_ind_predicate_context ind mdecl idecl (pctx : list aname) :
  eq_annots pctx (ind_predicate_context ind mdecl idecl) ->
  eq_annots pctx (idecl_binder idecl :: ind_indices idecl).
Proof.
  rewrite /ind_predicate_context.
  intros eq. depelim eq; cbn in *.
  constructor => //.
  now eapply eq_annots_expand_lets_ctx.
Qed.

Lemma eq_annots_cstr_branch_context ind mdecl cdecl (pctx : list aname) :
  eq_annots pctx (cstr_branch_context ind mdecl cdecl) ->
  eq_annots pctx (cstr_args cdecl).
Proof.
  rewrite /cstr_branch_context.
  intros eq.
  eapply eq_annots_subst_context.
  now eapply eq_annots_expand_lets_ctx.
Qed.

From MetaCoq.PCUIC Require Import PCUICValidity PCUICContexts PCUICInductives PCUICInductiveInversion.

Lemma isType_mkApps_Ind_inv_spine {cf:checker_flags} {Σ : global_env_ext} {Γ ind u args} {wfΣ : wf Σ} {mdecl idecl} :
  declared_inductive Σ.1 ind mdecl idecl ->
  isType Σ Γ (mkApps (tInd ind u) args) ->
  ∑ s, PCUICSpine.spine_subst Σ Γ args s (ind_params mdecl ,,, ind_indices idecl)@[u] ×
        consistent_instance_ext Σ (ind_universes mdecl) u.
Proof.
  move=> isdecl isty.
  pose proof (isType_wf_local isty).
  destruct isty as [s Hs].
  eapply invert_type_mkApps_ind in Hs as [sp cu]; tea.
  erewrite ind_arity_eq in sp.
  2: eapply PCUICInductives.oib ; eauto.
  rewrite !subst_instance_it_mkProd_or_LetIn in sp.
  rewrite -it_mkProd_or_LetIn_app /= in sp.
  eapply PCUICSpine.arity_typing_spine in sp as [hle hs [insts sp]]; tea.
  exists insts. split => //.
  now rewrite PCUICUnivSubstitutionConv.subst_instance_app_ctx.
Qed.

Lemma All2_map2_right {A B C} {l : list A} {l' : list B} (f : A -> B -> C) P : 
  All2 (fun x y => P x (f x y)) l l' ->  
  All2 P l (map2 f l l').
Proof.
  induction 1; cbn; constructor; auto.
Qed.

Lemma All2i_map2_right {A B C} {n} {l : list A} {l' : list B} (f : A -> B -> C) P : 
  All2i (fun n x y => P n x (f x y)) n l l' ->  
  All2i P n l (map2 f l l').
Proof.
  induction 1; cbn; constructor; auto.
Qed.

Lemma simpl_type_Case {H : checker_flags} {Σ : global_env_ext} {Γ} {ci : case_info} {p c brs ps mdecl idecl indices} {wfΣ : wf Σ} :
  declared_inductive Σ.1 ci mdecl idecl ->
  ind_npars mdecl = ci_npar ci ->
  All2 (compare_decls eq eq) (pcontext p)
  (ind_predicate_context ci mdecl idecl) ->
  let predctx := case_predicate_context ci mdecl idecl p in
  wf_predicate mdecl idecl p ->
  wf_local Σ (Γ,,, predctx) ->
  Σ;;; Γ,,, predctx |- preturn p : tSort ps ->
  is_allowed_elimination Σ ps (ind_kelim idecl) ->
  Σ;;; Γ |- c : mkApps (tInd ci (puinst p)) (pparams p ++ indices) ->
  isCoFinite (ind_finite mdecl) = false ->
  let ptm := it_mkLambda_or_LetIn predctx (preturn p) in
  wf_branches idecl brs ->
  All2i
  (fun (i : nat) (cdecl : constructor_body) (br : branch term) =>
  All2 (compare_decls eq eq) (bcontext br)
  (cstr_branch_context ci mdecl cdecl) *
  (let brctxty := case_branch_type ci mdecl idecl p br ptm i cdecl in
    Σ;;; Γ,,, brctxty.1 |- bbody br : brctxty.2 × 
    Σ;;; Γ,,, brctxty.1 |- brctxty.2 : tSort ps)) 0 
  (ind_ctors idecl) brs ->
  Σ;;; Γ |- tCase ci p c brs : mkApps ptm (indices ++ [c]).
Proof.
  intros.
  assert (hty := validity X2).
  eapply isType_mkApps_Ind_inv_spine in hty as [inst [sp cu]]; tea.
  eapply type_Case; tea.
  - now eapply PCUICSpine.spine_subst_ctx_inst.
  - solve_all. now eapply typing_wf_local in a0.
Qed.

From MetaCoq.PCUIC Require Import PCUICOnFreeVars.

Lemma trans_cumulSpec {cf} {Σ : Ast.Env.global_env_ext} {wfΣ : Typing.wf Σ.1} {Γ T T'} :
  let Σ' := trans_global Σ in
  wf Σ' ->
  All (WfAst.wf_decl Σ.1) Γ ->
  WfAst.wf Σ.1 T ->
  WfAst.wf Σ.1 T' ->
  ST.cumul Σ Γ T T' ->
  is_closed_context (trans_local Σ' Γ) ->
  is_open_term (trans_local Σ' Γ) (trans Σ' T) ->
  is_open_term (trans_local Σ' Γ) (trans Σ' T') ->
  Σ';;; trans_local Σ' Γ |- trans Σ' T <=s trans Σ' T'.
Proof.
  intros Σ' wfΣ' wfΓ wfT wfT' cum clΓ clT clT'.
  eapply (PCUICConversion.cumulAlgo_cumulSpec _ (le:=true)).
  eapply PCUICWellScopedCumulativity.into_equality; eauto with fvs.
  eapply trans_cumul; tea.
Qed.

Lemma trans_cumulSpec_typed {cf} {Σ : Ast.Env.global_env_ext} {wfΣ : Typing.wf Σ.1} {Γ T T'} :
  let Σ' := trans_global Σ in
  wf Σ' ->
  All (WfAst.wf_decl Σ.1) Γ ->
  WfAst.wf Σ.1 T ->
  WfAst.wf Σ.1 T' ->
  ST.cumul Σ Γ T T' ->
  isType Σ' (trans_local Σ' Γ) (trans Σ' T) ->
  isType Σ' (trans_local Σ' Γ) (trans Σ' T') ->
  Σ';;; trans_local Σ' Γ |- trans Σ' T <=s trans Σ' T'.
Proof.
  intros Σ' wfΣ' wfΓ wfT wfT' cum ist ist'.
  eapply (PCUICConversion.cumulAlgo_cumulSpec _ (le:=true)).
  eapply PCUICWellScopedCumulativity.into_equality; eauto with fvs.
  eapply trans_cumul; tea.
  eapply isType_wf_local in ist; fvs.
Qed.

Lemma trans_case_branch_type Σ (ci : case_info) mdecl idecl cdecl i p br :
  let Σ' := trans_global_decls Σ in
  let bctx := Ast.case_predicate_context ci mdecl idecl p in
  let p' := Ast.map_predicate id (trans Σ') (trans Σ') p in
  let mdecl' := trans_minductive_body Σ' mdecl in
  let idecl' := trans_one_ind_body Σ' idecl in
  let cdecl' := trans_constructor_body Σ' cdecl in
  let p' := trans_predicate ci mdecl' idecl' p'.(Ast.pparams) p'.(Ast.puinst) p'.(Ast.pcontext) p'.(Ast.preturn) in
  let br' := trans_branch ci mdecl' cdecl' br.(Ast.bcontext) (trans Σ' br.(Ast.bbody)) in
  let ptm := Ast.Env.it_mkLambda_or_LetIn bctx (Ast.preturn p) in
  let ptm' := it_mkLambda_or_LetIn (case_predicate_context ci mdecl' idecl' p') (preturn p') in
  WfAst.wf_nactx (Ast.pcontext p) (Ast.ind_predicate_context ci mdecl idecl) ->
  WfAst.wf_nactx (Ast.bcontext br) (Ast.cstr_branch_context ci mdecl cdecl) ->
  let brctxty := Ast.case_branch_type ci mdecl p ptm i cdecl br in
  let brctxty' := case_branch_type ci mdecl' idecl' p' br' ptm' i cdecl' in
  brctxty'.1 = trans_local Σ' brctxty.1 /\
  brctxty'.2 = trans Σ' brctxty.2.
Proof.
  intros.
  split.
  * rewrite /brctxty' /= /id.
    rewrite (trans_case_branch_context Σ ci mdecl idecl cdecl) //.
  * rewrite /brctxty' /brctxty.
    rewrite /case_branch_type /case_branch_type_gen /Ast.case_branch_type /Ast.case_branch_type_gen.
    cbv beta iota delta [snd].
    rewrite trans_mkApps trans_lift. f_equal.
    { rewrite /cdecl'; len. f_equal.
      rewrite /ptm' /ptm trans_it_mkLambda_or_LetIn // /p'0 /=. f_equal.
      rewrite /bctx. 
      rewrite [map _ (Ast.case_predicate_context _ _ _ _)](trans_case_predicate_context Σ ci mdecl idecl p) //.
      eapply All2_length in X. len in X. }
    rewrite map_app /=. f_equal.
    { rewrite !map_map_compose. eapply map_ext => x.
      rewrite trans_subst map_rev; f_equal; len.
      rewrite trans_expand_lets_k. f_equal.
      rewrite trans_local_subst_instance //.
      rewrite trans_subst trans_inds; f_equal.
      now rewrite trans_subst_instance. }
    f_equal.
    rewrite trans_mkApps. f_equal.
    rewrite map_app. f_equal.
    rewrite !map_map_compose.
    apply map_ext => x. rewrite trans_lift. f_equal; len.
    rewrite trans_reln //.
Qed.

Theorem template_to_pcuic {cf} :
  ST.env_prop (fun Σ Γ t T =>
    let Σ' := trans_global Σ in
    wf Σ' ->
    typing Σ' (trans_local Σ' Γ) (trans Σ' t) (trans Σ' T))
    (fun Σ Γ _ =>
      let Σ' := trans_global Σ in
      wf Σ' ->
      wf_local Σ' (trans_local Σ' Γ)).
Proof.
  apply ST.typing_ind_env.
  all: intros.
  all: try solve [ econstructor; eauto with trans ].

  - eapply trans_wf_local; eauto.
    
  - rewrite trans_lift.
    eapply refine_type. eapply type_Rel; eauto.
    unfold trans_local. rewrite nth_error_map. rewrite H. reflexivity.
    f_equal.

  - (* Sorts *)
    constructor; eauto.
    destruct u; simpl in *; eauto.
    intros.
    now rewrite global_ext_levels_trans.

  - (* Casts *)
    eapply refine_type. red. cbn. eapply type_App.
    2:{ eapply type_Lambda; eauto. eapply type_Rel. econstructor; eauto.
      eapply typing_wf_local. eauto. eauto. simpl. exists s; auto. reflexivity. }
    eapply type_Prod. eauto.
    instantiate (1 := s). simpl.
    eapply (weakening _ _ [_] _ (tSort _)); eauto.
    constructor; eauto. eapply typing_wf_local; eauto. red.
    exists s; eauto. auto.
    simpl. unfold subst1. rewrite simpl_subst; auto. now rewrite lift0_p.

  - (* The interesting application case *)
    cbn; eapply type_mkApps; eauto.
    specialize (X0 X2).
    eapply typing_wf in X; eauto. destruct X.
    eapply PCUICValidity.validity in X0.
    clear H H0.
    induction X1.
    * econstructor; eauto. reflexivity.
    * simpl in p.
      destruct (TypingWf.typing_wf _ wfΣ _ _ _ typrod) as [wfAB _].
      econstructor; eauto.
      + exists s; eauto. eapply p; eauto.
      + rewrite -/Σ'.
        change (tProd na (trans Σ' A) (trans _ B)) with (trans Σ' (Ast.tProd na A B)).
        eapply trans_cumulSpec_typed; tea.
        eapply TypingWf.typing_all_wf_decl; eauto.
        exists s; eauto. now eapply p.
      + eapply typing_wf in ty; eauto. destruct ty as [wfhd _].
        rewrite trans_subst in IHX1; eauto with wf.
        eapply IHX1; cycle 1.
        2:apply WfAst.wf_subst; try constructor; auto. 2:now inv wfAB.
        specialize (p X2). specialize (p0 X2).
        eapply PCUICInversion.inversion_Prod in p as [s1 [s2 [HA [HB Hs]]]]; auto. 
        eapply (PCUICArities.isType_subst (Δ := [vass na (trans Σ' A)])); eauto.
        eapply subslet_ass_tip. eauto with pcuic.
        now exists s2.

  - cbn; rewrite trans_subst_instance.
    pose proof (forall_decls_declared_constant _ _ _ _ _ H).
    rewrite -/Σ'.
    replace (trans _ (Ast.Env.cst_type decl)) with
        (cst_type (trans_constant_body Σ' decl)) by (destruct decl; reflexivity).
    econstructor; eauto with trans.
    now apply (trans_consistent_instance_ext _ (Ast.Env.ConstantDecl decl)).

  - rewrite trans_subst_instance.
    pose proof (forall_decls_declared_inductive _ _ _ _ _ _ isdecl).
    rewrite -/Σ'.
    replace (trans _ (Ast.Env.ind_type idecl)) with
        (ind_type (trans_one_ind_body Σ' idecl)) by (destruct idecl; reflexivity).
    eapply type_Ind; eauto. eauto with trans.
    now apply (trans_consistent_instance_ext _ (Ast.Env.InductiveDecl mdecl)).

  - pose proof (forall_decls_declared_constructor _ _ _ _ _ _ _ isdecl).
    unfold ST.type_of_constructor in *.
    rewrite trans_subst.
    rewrite trans_subst_instance.
    rewrite trans_inds. simpl.
    eapply refine_type. econstructor; eauto with trans.
    now apply (trans_consistent_instance_ext _ (Ast.Env.InductiveDecl mdecl)).
    reflexivity.

  - cbn; rewrite trans_mkApps; auto with wf trans. 
    pose proof (forall_decls_declared_inductive _ _ _ _ _ _ isdecl).
    rewrite (declared_inductive_lookup _ H4).
    rewrite trans_it_mkLambda_or_LetIn.
    rewrite -/(trans_local Σ' (Ast.case_predicate_context _ _ _ _)).
    have lenpctx : #|Ast.pcontext p| = S #|Ast.Env.ind_indices idecl|.
    { eapply All2_length in X1; len in X1. } 
    rewrite (trans_case_predicate_context Σ.1) //.
    rewrite map_app.
    specialize (X2 X7).
    specialize (X5 X7).
    set (p' := trans_predicate _ _ _ _ _ _ _).
    eapply (simpl_type_Case (p:=p') (ps:=ps)) => //. 
    + cbn. rewrite map2_map2_bias_left; len.
      now rewrite !pclengths /= !lengths.
      eapply eq_binder_annots_eq.
      now eapply trans_ind_predicate_context.
    + cbn. split. cbn.
      { epose proof (declared_minductive_ind_npars (proj1 H4)).
        cbn in H4. len. rewrite -H0.
        now rewrite context_assumptions_map in H5. }
      cbn. rewrite map2_map2_bias_left.
      { rewrite PCUICCases.ind_predicate_context_length; len. }
      rewrite map_map2 /= map2_cst.
      rewrite PCUICCases.ind_predicate_context_length; len.
      eapply (trans_ind_predicate_context Σ.1) in X1.
      eapply (eq_annots_ind_predicate_context ci).
      eapply All2_Forall2 => //. exact X1.
    + clear X6. 
      rewrite trans_local_app in X2.
      rewrite /predctx in X2.
      rewrite trans_case_predicate_context in X2 => //.
      now eapply typing_wf_local in X2.
    + clear X6. cbn [preturn trans_predicate].
      rewrite trans_local_app in X2.
      rewrite /predctx in X2.
      rewrite trans_case_predicate_context in X2 => //.
    + cbn. move: H2.
      now rewrite -global_ext_constraints_trans.
    + cbn. clear X6.
      now rewrite trans_mkApps map_app in X5.
    + red. eapply All2_Forall2.
      eapply All2_map2_right.
      eapply All2_map.
      eapply All2i_All2; tea.
      cbv beta. intros i cdecl br.
      set (brctxty := Ast.case_branch_type _ _ _ _ _ _ _).
      move=> [] [] [] [] eqann Hbod IHbod Hty IHty.
      unfold wf_branch, wf_branch_gen.
      cbn [bcontext trans_branch].
      have lenctx : #|Ast.bcontext br| = #|Ast.Env.cstr_args cdecl|.
      { eapply All2_length in eqann; now len in eqann. }
      rewrite map2_map2_bias_left; len.
      rewrite /forget_types map_map2 map2_cst; len.
      eapply eq_annots_cstr_branch_context.
      eapply All2_Forall2. eapply trans_cstr_branch_context_alpha; tea.
    + eapply All2i_map2_right. eapply All2i_map. 
      eapply All2i_impl; tea.
      cbv beta. intros i cdecl br.
      set (brctxty := Ast.case_branch_type _ _ _ _ _ _ _).
      move=> [] [] [] [] eqann Hbod IHbod Hty IHty.
      have lenctx : #|Ast.bcontext br| = #|Ast.Env.cstr_args cdecl|.
      { eapply All2_length in eqann; now len in eqann. }
      split.
      { cbn [bcontext trans_branch].
        rewrite map2_map2_bias_left; len.
        eapply eq_binder_annots_eq.
        eapply trans_cstr_branch_context_alpha; tea. }
      intros brctxty'.
      destruct (trans_case_branch_type Σ.1 ci mdecl idecl cdecl i p br X1 eqann) as [eqctx eqbty].
      rewrite [brctxty'.2]eqbty.
      rewrite [brctxty'.1]eqctx. 
      clear eqctx eqbty.
      specialize (IHbod X7). specialize (IHty X7).
      rewrite trans_local_app in IHbod.
      rewrite trans_local_app in IHty => //.

  - destruct pdecl as [arity ty']; simpl in *.
    assert (wfproj := TypingWf.declared_projection_wf _ _ _ _ _ isdecl).
    simpl in wfproj.
    eapply forall_decls_declared_projection in isdecl => //.
    destruct (typing_wf _ wfΣ _ _ _ X1) as [wfc wfind].
    eapply WfAst.wf_mkApps_inv in wfind; auto.
    rewrite trans_subst; auto with wf. 
    simpl. rewrite map_rev. rewrite trans_subst_instance.
    eapply (type_Proj _ _ _ _ _ _ _ _ (arity, trans Σ' ty)). eauto.
    rewrite trans_mkApps in X2; auto. rewrite map_length.
    destruct mdecl; auto.

  - eapply refine_type.
    assert (fix_context (map (map_def (trans Σ') (trans Σ')) mfix) =
            trans_local Σ' (ST.fix_context mfix)).
    { unfold trans_local, ST.fix_context.
      rewrite map_rev map_mapi /fix_context mapi_map.
      f_equal. apply mapi_ext; intros i x.
      simpl. rewrite /vass /trans_decl /=.
      rewrite trans_lift. reflexivity. }
    cbn. econstructor; eauto.
    eapply fix_guard_trans. assumption.
    now rewrite nth_error_map H0.
    -- eapply All_map, (All_impl X0).
       intros x [s [Hs Hts]].
       now exists s.
    -- apply All_map. eapply All_impl; eauto.
       intuition eauto 3 with wf; cbn.
       rewrite H2. rewrite /trans_local map_length.
       rewrite /trans_local map_app in X3.
       rewrite <- trans_lift. apply X3; auto.
    -- eapply trans_wf_fixpoint => //.
        solve_all. destruct a as [s [Hs IH]].
        now eapply TypingWf.typing_wf in Hs.
        now eapply TypingWf.typing_wf in a0.
    -- destruct decl; reflexivity.

  - eapply refine_type.
    assert (fix_context (map (map_def (trans Σ') (trans Σ')) mfix) =
            trans_local Σ' (ST.fix_context mfix)).
    { unfold trans_local, ST.fix_context.
      rewrite map_rev map_mapi /fix_context mapi_map.
      f_equal. apply mapi_ext => i x.
      rewrite /vass /trans_decl /=. simpl. rewrite trans_lift. reflexivity. }
    cbn; econstructor; eauto.
    -- now eapply cofix_guard_trans.
    -- now rewrite nth_error_map H0.
    -- eapply All_map, (All_impl X0).
       intros x [s [Hs Hts]]. now exists s.
    -- apply All_map. eapply All_impl; eauto.
       intuition eauto 3 with wf.
       rewrite H2. rewrite /trans_local map_length.
       rewrite trans_local_app in X3.
       cbn. rewrite <- trans_lift. now apply X3.
    -- eapply trans_wf_cofixpoint => //.
       solve_all. destruct a as [s [Hs IH]].
       now eapply TypingWf.typing_wf in Hs.
       now eapply TypingWf.typing_wf in a0.
    -- destruct decl; reflexivity.

  - assert (WfAst.wf Σ.1 B).
    { now apply typing_wf in X2. }
    eapply type_Cumul; eauto.
    eapply trans_cumulSpec_typed; eauto with trans. 
    clear X. apply typing_all_wf_decl in wfΓ; auto.
    eapply typing_wf in X0; eauto. destruct X0. auto.
    specialize (X1 X5). 
    now eapply validity in X1.
    specialize (X3 X5). now exists s.
Qed.

Lemma Alli_map {A B} (P : nat -> B -> Type) n (f : A -> B) l : 
  Alli (fun n x => P n (f x)) n l ->
  Alli P n (map f l).
Proof.
  induction 1; constructor; auto.
Qed.

Lemma trans_arities_context Σ m : 
  let Σ' := trans_global_decls Σ in 
  trans_local Σ' (Ast.Env.arities_context (Ast.Env.ind_bodies m)) = 
  arities_context (map (trans_one_ind_body Σ') (Ast.Env.ind_bodies m)).
Proof.
  rewrite /trans_local /Ast.Env.arities_context rev_map_spec map_rev map_map_compose 
    /PCUICEnvironment.arities_context rev_map_spec map_map_compose /= //.
Qed.

Lemma trans_subst_telescope Σ s k Γ : 
  let Σ' := trans_global_decls Σ in 
  map (trans_decl Σ') (Ast.Env.subst_telescope s k Γ) = 
  subst_telescope (map (trans Σ') s) k (map (trans_decl Σ') Γ).
Proof.
  rewrite /subst_telescope /Ast.Env.subst_telescope.
  rewrite map_mapi mapi_map.
  apply mapi_ext => n [na [b|] ty] /=;
  rewrite /map_decl /trans_decl /=; f_equal;
  now rewrite trans_subst.
Qed.

Require Import PCUICInstDef PCUICInstConv.
Require Import ssrbool.
(* Lemma closed_ctx_map2_set_binder_name (n : nat) (bctx : list aname) (ctx : list context_decl) :
  closedn_ctx n ctx -> closedn_ctx n (map2_bias_left set_binder_name dummy_decl bctx ctx).
Proof.
  induction bctx in n, ctx |- *; cbn; auto.
  destruct ctx; auto.
  intros H.
  destruct ctx. cbn.
  rewrite IHbctx //.
  rewrite !closedn_ctx_snoc IHbctx.
  rewrite closedn_ctx_snoc in H. now move/andP: H=>[].
  cbn. rewrite map2_bias_left_length.
  rewrite closedn_ctx_snoc in H. move/andP: H=>[].
  
  cbn.
  specialize (IHbctx _ _ H).
  cbn in IHbctx.
  move/andP => [] clc clctx.
  rewrite IHbctx // /=.
  eapply closed_decl
  rewrite closedn_ctx_ *)

Lemma closed_ind_predicate_context {cf} {Σ ind mdecl idecl} : 
  wf Σ ->
  declared_inductive Σ ind mdecl idecl ->
  closedn_ctx (context_assumptions mdecl.(ind_params)) (ind_predicate_context ind mdecl idecl).
Proof.
  intros wfΣ decli.
  eapply PCUICClosed.closed_ind_predicate_context; tea.
  eapply PCUICClosedTyp.declared_minductive_closed. eapply decli.
Qed.

Lemma All2_All_map2 {A B C} {P : A -> Type} (f : B -> C -> A) l l' : 
  All2 (fun x y => P (f x y)) l l' ->
  All P (map2 f l l').
Proof.
  induction 1; constructor; auto.
Qed.

Lemma trans_closedn {cf} {Σ k t} :
  Typing.wf Σ ->
  wf (trans_global_decls Σ) ->
  WfAst.wf Σ t ->
  Ast.closedn k t -> 
  closedn k (trans (trans_global_decls Σ) t).
Proof.
  intros wfΣ wfΣ' wf. induction wf using WfAst.term_wf_forall_list_ind in k |- *; cbn; auto.
  1-6:solve_all.
  - rewrite PCUICClosed.closedn_mkApps. solve_all.
  - eapply forall_decls_declared_inductive in H; tea.
    rewrite (declared_inductive_lookup _ H).
    destruct X0. 
    cbn.
    unfold test_predicate_k. cbn.
    unfold Ast.test_predicate. cbn.
    pose proof (All2_length X). len in H1.
    intros; rtoProp. intuition auto.
    * solve_all.
    * len.
      rewrite map2_map2_bias_left.
      rewrite PCUICCases.ind_predicate_context_length. cbn. len.
      eapply PCUICInstConv.closed_ctx_args.
      rewrite PCUICCases.ind_predicate_context_length. cbn. len.
      rewrite H0.
      relativize (Ast.Env.context_assumptions _).
      eapply (closed_ind_predicate_context wfΣ' H).
      cbn. now rewrite context_assumptions_map.
    * rewrite map2_map2_bias_left.
      rewrite PCUICCases.ind_predicate_context_length. cbn. len.
      rewrite map2_length.
      rewrite PCUICCases.ind_predicate_context_length. cbn. len.
      solve_all.
    * solve_all.
      eapply All2_All_map2, All2_map.
      eapply All2_nth_hyp in X1.
      solve_all.
      destruct X0 as [c [hnth [[eqb IHb] hbr]]].
      assert (hlen := All2_length eqb). len in hlen.
      unfold test_branch_k. unfold Ast.test_branch in hbr.
      unfold trans_branch. cbn -[cstr_branch_context].
      rewrite map2_map2_bias_left. len.
      apply/andP; split.
      { eapply PCUICInstConv.closed_ctx_args; len.
        rewrite H0.
        relativize (Ast.Env.context_assumptions _).
        eapply (PCUICClosedTyp.closed_cstr_branch_context (Σ := trans_global (Ast.Env.empty_ext Σ)) (i:=c)); cbn; tea.
        split; cbn; tea. now rewrite nth_error_map hnth.
        cbn. now rewrite context_assumptions_map. }
      rewrite map2_length; len. eauto.
  - unfold test_def; red in X. solve_all.
  - unfold test_def; solve_all.    
Qed. 

From MetaCoq.PCUIC Require Import PCUICOnFreeVars.

Lemma trans_cumul_ctx_rel {cf} {Σ : Ast.Env.global_env_ext} Γ Δ Δ' :
  let Σ' := trans_global Σ in
  Typing.wf Σ.1 -> wf Σ' ->
  ST.TemplateConversion.cumul_ctx_rel Σ Γ Δ Δ' ->
  closed_ctx (trans_local Σ' (Ast.Env.app_context Γ Δ)) ->
  closed_ctx (trans_local Σ' (Ast.Env.app_context Γ Δ')) ->
  All (WfAst.wf_decl Σ.1) (Ast.Env.app_context Γ Δ) ->
  All (WfAst.wf_decl Σ.1) (Ast.Env.app_context Γ Δ') ->
  cumul_ctx_rel Σ' (trans_local Σ' Γ) (trans_local Σ' Δ) (trans_local Σ' Δ').
Proof.
  intros Σ' wfΣ wfΣ'. 
  induction 1; cbn; constructor; auto.
  inv_on_free_vars.
  apply IHX => //. now depelim X0. now depelim X1.
  rewrite - !trans_local_app.
  move/andP: H => [] cl0 cl1.
  move/andP: H0 => [] cl0' cl1'. len in cl1. len in cl1'.
  destruct p; constructor; cbn; auto; depelim X0; depelim X1; destruct w as []; destruct w0 as [].
  
  eapply trans_cumul in c; tea.
  eapply (PCUICConversion.cumulAlgo_cumulSpec _ (le:=true)).
  eapply PCUICWellScopedCumulativity.into_equality => //.
  now eapply closed_ctx_on_free_vars in cl0.
  1-2:cbn in cl1, cl1'.
  1-2:rewrite closedn_on_free_vars //; len.
  now rewrite (All2_fold_length X).

  eapply trans_conv in c; tea.
  eapply (PCUICConversion.cumulAlgo_cumulSpec _ (le:=false)).
  eapply PCUICWellScopedCumulativity.into_equality => //.
  now eapply closed_ctx_on_free_vars in cl0.
  1-2:move/andP: cl1 => [] /= clb cbt.
  1-2:move/andP: cl1' => [] /= clb' cbt'.
  1-2:rewrite closedn_on_free_vars //; len.
  now rewrite (All2_fold_length X).

  eapply trans_cumul in c0; tea.
  eapply (PCUICConversion.cumulAlgo_cumulSpec _ (le:=true)).
  eapply PCUICWellScopedCumulativity.into_equality => //.
  now eapply closed_ctx_on_free_vars in cl0.
  1-2:move/andP: cl1 => [] /= clb cbt.
  1-2:move/andP: cl1' => [] /= clb' cbt'.
  1-2:rewrite closedn_on_free_vars //; len.
  now rewrite (All2_fold_length X).
Qed.

Lemma wf_expand_lets Σ Γ t : 
  All (WfAst.wf_decl Σ) Γ ->
  WfAst.wf Σ t ->
  WfAst.wf Σ (Ast.Env.expand_lets Γ t).
Proof.
  intros.
  rewrite /Ast.Env.expand_lets /Ast.Env.expand_lets_k.
  eapply WfAst.wf_subst, WfAst.wf_lift => //.
  now eapply wf_extended_subst.
Qed.

Lemma wf_expand_lets_ctx Σ Γ Δ : 
  All (WfAst.wf_decl Σ) Γ ->
  All (WfAst.wf_decl Σ) Δ ->
  All (WfAst.wf_decl Σ) (Ast.Env.expand_lets_ctx Γ Δ).
Proof.
  intros.
  rewrite /Ast.Env.expand_lets_ctx /Ast.Env.expand_lets_k_ctx.
  eapply wf_subst_context => //.
  eapply wf_lift_context => //.
  eapply wf_extended_subst => //.
Qed.

Lemma wf_ind_arities Σ mdecl : 
  All (wf_inductive_body Σ) (Ast.Env.ind_bodies mdecl) ->
  All (WfAst.wf_decl Σ) (Typing.ind_arities mdecl).
Proof.
  rewrite /Typing.ind_arities.
  rewrite /Ast.Env.arities_context.
  intros.
  rewrite rev_map_spec. eapply All_rev. eapply All_map.
  induction X; constructor; auto.
  unfold WfAst.wf_decl; cbn. split => //.
  eapply p.
Qed.

Lemma All2_refl_inv {A} {P : A -> A -> Type} l :
  All2 P l l -> All (fun x => P x x) l.
Proof.
  intros H; depind H; constructor; auto.
Qed.

Lemma All_All2_refl {A} {P : A -> A -> Type} l :
  All (fun x => P x x) l -> All2 P l l.
Proof.
  intros H; depind H; constructor; auto.
Qed.



Lemma trans_cstr_respects_variance {cf} Σ mdecl v cdecl :
  let Σ' := trans_global_decls Σ in
  let mdecl' := trans_minductive_body Σ' mdecl in
  let cdecl' := trans_constructor_body Σ' cdecl in
  Typing.wf Σ ->
  wf Σ' ->
  All (wf_inductive_body Σ) (Ast.Env.ind_bodies mdecl) ->
  All (WfAst.wf_decl Σ) (Ast.Env.ind_params mdecl) ->
  All (WfAst.wf_decl Σ) (Ast.Env.cstr_args cdecl) ->
  All (WfAst.wf Σ) (Ast.Env.cstr_indices cdecl) ->
  ST.cstr_respects_variance Σ mdecl v cdecl ->
  cstr_respects_variance Σ' mdecl' v cdecl'.
Proof.
  intros Σ' mdecl' cdecl' wfΣ wfΣ' wfb wfp wfa wfi.
  unfold ST.cstr_respects_variance, cstr_respects_variance.
  change (variance_universes (ind_universes mdecl') v) with
    (ST.variance_universes (Ast.Env.ind_universes mdecl) v).
  destruct variance_universes as [[[udecl inst] inst']|] => //.
  intros []. split.
  * apply (trans_cumul_ctx_rel (Σ := (Σ, udecl))) in c; tea.
    rewrite !trans_local_subst_instance trans_expand_lets_ctx in c.
    rewrite !trans_smash_context in c.
    rewrite trans_local_app trans_smash_context in c.
    change (trans_global_decls (Σ, udecl).1) with Σ' in c.
    now rewrite trans_arities_context in c.
    {}


    { eapply All_app_inv.
      eapply wf_subst_instance_context.
      eapply wf_expand_lets_ctx => //.
      eapply wf_smash_context => //.
      eapply wf_subst_instance_context.
      eapply All_app_inv. eapply wf_smash_context => //.
      now eapply wf_ind_arities. }
    { eapply All_app_inv.
      eapply wf_subst_instance_context.
      eapply wf_expand_lets_ctx => //.
      eapply wf_smash_context => //.
      eapply wf_subst_instance_context.
      eapply All_app_inv. eapply wf_smash_context => //.
      now eapply wf_ind_arities. }
  * clear c.
    eapply All2_map. eapply All2_map_inv in a.
    eapply All2_refl_inv in a. eapply All_All2_refl.
    eapply All_map. solve_all.
    eapply trans_conv in b; tea.
    { move:b; rewrite !trans_local_subst_instance !trans_local_app trans_arities_context.
      rewrite !trans_smash_context !trans_subst_instance !trans_expand_lets !trans_local_app //. }
    { eapply wf_subst_instance_context.
      eapply All_app_inv => //; [|now eapply wf_ind_arities].
      eapply wf_smash_context => //.
      eapply All_app_inv => //. }
    { eapply WfAst.wf_subst_instance.
      eapply wf_expand_lets => //.
      eapply All_app_inv => //. }
    { eapply WfAst.wf_subst_instance.
      eapply wf_expand_lets => //.
      eapply All_app_inv => //. }
Qed.

Lemma trans_ind_respects_variance {cf} Σ mdecl v idecl :
  let Σ' := trans_global_decls Σ in
  let mdecl' := trans_minductive_body Σ' mdecl in
  let idecl' := trans_one_ind_body Σ' idecl in
  Typing.wf Σ ->
  wf Σ' ->
  wf_inductive_body Σ idecl ->
  All (WfAst.wf_decl Σ) (Ast.Env.ind_params mdecl) ->
  ST.ind_respects_variance Σ mdecl v (Ast.Env.ind_indices idecl) ->
  ind_respects_variance Σ' mdecl' v (ind_indices idecl').
Proof.
  intros Σ' mdecl' idecl' wfΣ wfΣ' wfb wfp.
  unfold ST.ind_respects_variance, ind_respects_variance.
  change (variance_universes (ind_universes mdecl') v) with
    (ST.variance_universes (Ast.Env.ind_universes mdecl) v).
  destruct variance_universes as [[[udecl inst] inst']|] => //.
  intros c. apply (trans_cumul_ctx_rel (Σ := (Σ, udecl))) in c; tea.
  { rewrite !trans_local_subst_instance trans_expand_lets_ctx in c.
    rewrite !trans_smash_context in c => //. }
  { eapply All_app_inv.
    eapply wf_subst_instance_context.
    eapply wf_expand_lets_ctx => //.
    eapply wf_smash_context => //. apply wfb.
    eapply wf_subst_instance_context.
    eapply wf_smash_context => //. }
  { eapply All_app_inv.
    eapply wf_subst_instance_context.
    eapply wf_expand_lets_ctx => //.
    eapply wf_smash_context => //. apply wfb.
    eapply wf_subst_instance_context.
    eapply wf_smash_context => //. }
Qed.

Lemma trans_type_local_ctx {cf} {Σ : Ast.Env.global_env_ext} Γ cs s (Σ' := trans_global Σ) :
  (forall (Σ : Ast.Env.global_env × universes_decl) 
  (Γ : Ast.Env.context) (t : Ast.term) (T : option Ast.term),
  Typing.wf Σ.1 ->
  Typing.lift_typing Typing.typing Σ Γ t T ->
  wf (trans_global_decls Σ.1) ->
  lift_typing typing (trans_global Σ)
  (trans_local (trans_global_decls Σ.1) Γ)
  (trans (trans_global_decls Σ.1) t)
  (option_map (trans (trans_global_decls Σ.1)) T)) ->
  Typing.wf Σ.1 ->
  wf Σ' ->
  ST.type_local_ctx (Typing.TemplateEnvTyping.lift_typing Typing.typing) Σ Γ cs s ->
  type_local_ctx (PCUICEnvTyping.lift_typing typing)
    (trans_global Σ)
  (trans_local Σ' Γ)
  (trans_local Σ' cs) s.
Proof.
  intros IH wfΣ wfΣ'. induction cs; simpl; auto.
  destruct Σ as [Σ univs]. unfold Σ'.
  unfold trans_global. cbn -[trans_global_decls].
  unfold ST.TemplateTyping.wf_universe.
  unfold PCUICTypingDef.wf_universe.
  unfold ST.wf_universe.
  unfold wf_universe. destruct s => //.
  now rewrite -global_ext_levels_trans.
  destruct a as [na [b|] ty] => //;
  intros [? ?]; cbn. destruct p.
  intuition auto.
  - eapply (IH _ _ _ None) in s0; auto.
    rewrite -trans_local_app //.
  - eapply (IH _ _ _ (Some _)) in t0 => //.
    rewrite -trans_local_app //.
  - eapply (IH _ _ _ (Some _)) in t0 => //.
    rewrite -trans_local_app; split => //.
    now eapply IHcs. 
Qed.

Lemma trans_check_ind_sorts {cf} Σ udecl kn mdecl n idecl
  (Σ' := trans_global_decls Σ)
  (mdecl' := trans_minductive_body Σ' mdecl)
  (idecl' := trans_one_ind_body Σ' idecl) :
  Typing.wf Σ ->
  wf Σ' ->
  (forall (Σ : Ast.Env.global_env × universes_decl) 
    (Γ : Ast.Env.context) (t : Ast.term) (T : option Ast.term),
  Typing.wf Σ.1 ->
  Typing.lift_typing Typing.typing Σ Γ t T ->
  wf (trans_global_decls Σ.1) ->
  lift_typing typing (trans_global Σ)
    (trans_local (trans_global_decls Σ.1) Γ)
    (trans (trans_global_decls Σ.1) t)
    (option_map (trans (trans_global_decls Σ.1)) T)) ->
  forall (oni: Typing.on_ind_body (Typing.TemplateEnvTyping.lift_typing Typing.typing)
        (Σ, udecl) kn mdecl n idecl),
  ST.check_ind_sorts
  (Typing.TemplateEnvTyping.lift_typing Typing.typing) 
  (Σ, Ast.Env.ind_universes mdecl) (Ast.Env.ind_params mdecl) (Ast.Env.ind_kelim idecl)
  (Ast.Env.ind_indices idecl) (ST.ind_cunivs oni)
  (Ast.Env.ind_sort idecl) ->
  check_ind_sorts (PCUICEnvTyping.lift_typing typing)
  (trans_global_decls Σ, Ast.Env.ind_universes mdecl)
  (ind_params mdecl')
  (ind_kelim idecl')
  (ind_indices idecl')
  (ST.ind_cunivs oni)
  (ind_sort idecl').
Proof.
  intros wfΣ wfΣ' IH oni.
  unfold ST.check_ind_sorts, check_ind_sorts. cbn.
  destruct Universe.is_prop => //.
  destruct Universe.is_sprop => //.
  intros []. split => //.
  { rewrite -global_ext_constraints_trans in c.
    unfold ST.check_constructors_smaller in c.
    unfold check_constructors_smaller. solve_all. }
  destruct indices_matter => //.
  now eapply trans_type_local_ctx in y.
Qed.

Lemma on_global_decl_wf {cf} {Σ : Ast.Env.global_env_ext} {kn d} :
  Typing.wf Σ.1 ->
  Typing.on_global_decl (Typing.TemplateEnvTyping.lift_typing Typing.typing) Σ kn d ->
  Typing.on_global_decl (fun Σ => WfAst.wf_decl_pred Σ.1) Σ kn d.
Proof.
  intros. eapply TypingWf.on_global_decl_impl; tea.
  intros.
  destruct T. 
  * eapply typing_wf; tea.
  * destruct X2 as [s Hs].
    red. split => //. now eapply typing_wf in Hs; tea.
Qed.

Lemma Alli_All_mix {A} {P : nat -> A -> Type} {Q} {n l} : 
  Alli P n l -> All Q l -> Alli (fun n x => P n x × Q x) n l.
Proof.
  induction 1; intros H; depelim H; constructor; intuition auto.
Qed.

Lemma trans_projs Σ kn n i mdecl  :
  map (trans (trans_global_decls Σ)) 
    (ST.projs {| inductive_mind := kn; inductive_ind := n |} (Ast.Env.ind_npars mdecl) i) =
  projs {| inductive_mind := kn; inductive_ind := n |} (Ast.Env.ind_npars mdecl) i.
Proof.
  induction i; cbn; auto. f_equal; auto.
Qed.

Lemma trans_on_global_env `{checker_flags} Σ :
  (forall Σ Γ t T, Typing.wf Σ.1 -> 
    Typing.lift_typing Typing.typing Σ Γ t T ->
    let Σ' := trans_global_decls Σ.1 in
    wf Σ' ->
    lift_typing typing (trans_global Σ) (trans_local Σ' Γ) (trans Σ' t) (option_map (trans Σ') T)) ->
  Typing.wf Σ -> wf (trans_global_decls Σ).
Proof.
  intros X X0.
  simpl in *. induction X0; simpl; constructor; auto.
  - red in f |- *. clear -f.
    induction f; cbn; constructor; auto. 
  - simpl. subst udecl.
    clear -o. destruct d; simpl in *;
      destruct o as [? [? [? ?]]].
    * split; rewrite global_levels_trans //.
      repeat split => //.
      red in H3 |- *.
      rewrite -global_ext_constraints_trans in H3.
      apply H3.
    * split; rewrite global_levels_trans //.
      repeat split => //.
      red in H3 |- *.
      rewrite -global_ext_constraints_trans in H3.
      apply H3.
  - simpl.
    change (Typing.wf Σ) in X0.
    have wfdecl := on_global_decl_wf (Σ := (Σ, udecl)) X0 o0.
    destruct d eqn:eqd; simpl in *.
    * destruct c; simpl. destruct cst_body0; simpl in *.
      red in o |- *. simpl in *. 
      apply (X (Σ, cst_universes0) [] t (Some cst_type0)); auto.
      red in o0 |- *. simpl in *.
      now apply (X (Σ, cst_universes0) [] cst_type0 None).
    * destruct o0 as [onI onP onNP].
      constructor; auto.
      -- have wfpars := on_global_inductive_wf_params wfdecl.
         eapply on_global_inductive_wf_bodies in wfdecl.
         eapply Alli_All_mix in onI; tea.
         eapply Alli_map. eapply Alli_impl. exact onI. eauto. intros n idecl [oni wf].
         unshelve refine {| ind_cunivs := oni.(ST.ind_cunivs) |}.
        --- simpl; rewrite oni.(ST.ind_arity_eq).
            now rewrite !trans_it_mkProd_or_LetIn.
        --- apply ST.onArity in oni. unfold on_type in *; simpl in *.
            now apply (X (Σ, Ast.Env.ind_universes m) [] (Ast.Env.ind_type idecl) None).
        --- pose proof oni.(ST.onConstructors) as X11. red in X11.
            red. eapply All2_map_left.
            destruct wf. solve_all.
            simpl.
            rename b into onc. rename y into cs.
            rename a0 into wfctype. rename a into wfcargs. rename b1 into wfcindices.
            destruct onc; unshelve econstructor; eauto.
            + simpl. unfold trans_local. rewrite context_assumptions_map.
              now rewrite cstr_args_length. 
            + simpl; unfold cstr_type, Ast.Env.cstr_type in cstr_eq |- *; simpl in *.
               rewrite cstr_eq. rewrite !trans_it_mkProd_or_LetIn.
               autorewrite with len. f_equal. f_equal.
               rewrite !trans_mkApps /cstr_concl /cstr_concl_head /= //.
               f_equal; auto. simpl. 
               now rewrite /trans_local !map_length.
               rewrite map_app /=. f_equal.
               rewrite /trans_local !map_length.
               unfold to_extended_list_k.
               now rewrite trans_reln.
            + unfold cstr_type, Ast.Env.cstr_type in on_ctype |- *; simpl in *.
              red. 
              move: (X (Σ, Ast.Env.ind_universes m) (Ast.Env.arities_context (Ast.Env.ind_bodies m)) 
                (Ast.Env.cstr_type x) None).
              now rewrite trans_arities_context.
            + clear -X0 IHX0 X on_cargs. revert on_cargs. simpl.
              have foo := (X (Σ, udecl) _ _ _ X0).
              rewrite -trans_arities_context.
              clear X.
              induction (Ast.Env.cstr_args x) in cs |- *; destruct cs; simpl; auto;
              destruct a as [na [b|] ty]; simpl in *; auto;
              split; intuition eauto;
              specialize (foo 
                (Ast.Env.app_context (Ast.Env.app_context 
                (Ast.Env.arities_context (Ast.Env.ind_bodies m)) (Ast.Env.ind_params m))
                c));
              rewrite /trans_local !map_app in foo.
              now eapply (foo ty None). 
              now apply (foo b (Some ty)).
              now apply (foo ty None).
              now apply (foo b (Some ty)).
              now apply (foo ty (Some (Ast.tSort _))).
            + clear -X0 IHX0 X on_cindices.
              revert on_cindices.
              rewrite -trans_lift_context /trans_local -map_rev.
              simpl. rewrite {2}/trans_local map_length.
              generalize (List.rev (Ast.Env.lift_context #|Ast.Env.cstr_args x| 0 (Ast.Env.ind_indices idecl))).
              rewrite -trans_arities_context.
              induction 1; simpl; constructor; auto;
              have foo := (X (Σ, Ast.Env.ind_universes m) _ _ _ X0);
              specialize (foo (Ast.Env.app_context (Ast.Env.app_context 
                (Ast.Env.arities_context (Ast.Env.ind_bodies m)) 
                (Ast.Env.ind_params m)) (Ast.Env.cstr_args x)));
              rewrite /trans_local !map_app in foo.
              now apply (foo i (Some t)).
              now rewrite (trans_subst_telescope _ [i] 0) in IHon_cindices.
              now rewrite (trans_subst_telescope _ [b] 0) in IHon_cindices.
            + cbn in *.
              clear -onI wfctype X0 IHX0 on_ctype_positive.
              set (Σ' := trans_global_decls Σ) in *.
              change [] with (map (trans_decl Σ') []).
              revert on_ctype_positive wfctype.
              generalize (@nil Ast.Env.context_decl). induction 1; simpl.
              rewrite trans_mkApps. simpl.
              subst headrel.
              assert (#|PCUICEnvironment.ind_bodies (trans_minductive_body Σ' m)| = #|Ast.Env.ind_bodies m|) as <-.
              now rewrite /trans_minductive_body /= map_length.
              assert (#|ctx| = #|map (trans_decl Σ') ctx|) as ->. now rewrite map_length.
              move/WfAst.wf_mkApps_inv => wfindices.
              eapply positive_cstr_concl.
              rewrite map_length.
              eapply All_map. solve_all. now eapply trans_closedn.
              move/WfAst.wf_inv => /= [[wfb wfty] wft].
              simpl; intros.
              constructor. rewrite -(trans_subst _ [b]).
              apply IHon_ctype_positive. eapply WfAst.wf_subst; auto.
              move/WfAst.wf_inv => /= [wfty wft].
              constructor. clear -onI X0 IHX0 p wfty.
              induction p.
              { constructor; rewrite map_length; eauto using trans_closedn. }
              { rewrite trans_mkApps /=.
                move/WfAst.wf_mkApps_inv: wfty => wfl.
                econstructor 2; tea; rewrite ?map_length //.
                solve_all. eauto using trans_closedn.
                rewrite -map_rev nth_error_map e //.
                rewrite e0.
                have wfty : WfAst.wf Σ (Ast.Env.ind_type i).
                { rewrite nth_error_rev in e. len. rewrite List.rev_involutive in e.
                  eapply nth_error_alli in onI; tea. cbn in onI.
                  destruct onI as [onI _]. eapply Typing.onArity in onI as [s Hs].
                  now eapply typing_wf in Hs. }
                rewrite /trans_one_ind_body /= /ind_realargs /= /ST.ind_realargs.
                generalize (trans_destArity Σ [] _ wfty IHX0).
                rewrite /ST.TemplateTyping.destArity /PCUICTypingDef.destArity.
                destruct AstUtils.destArity as [[args s]|] => /= -> //.
                len. rewrite context_assumptions_map.
                now rewrite Ast.Env.smash_context_length. }
              { cbn. constructor 3. 
                rewrite trans_subst in IHp. apply IHp.
                move/WfAst.wf_inv: wfty => /= [[wfb wfty] wft].
                eapply WfAst.wf_subst; auto. }
              { cbn.
                move/WfAst.wf_inv: wfty => /= [wfty wft].
                constructor 4. len. eauto using trans_closedn.
                now apply IHp. } 
              { cbn. now apply IHon_ctype_positive. }
            + clear -wfpars wfdecl wfctype wfcargs wfcindices X0 IHX0 on_ctype_variance.
              intros v indv.
              specialize (on_ctype_variance _ indv).
              cbn.
              eapply trans_cstr_respects_variance => //.
            + destruct lets_in_constructor_types.
              ++ eauto.
              ++ red in on_lets_in_type. red. rewrite <- on_lets_in_type.
                 destruct x. clear. cbn.
                 induction cstr_args0.
                 +++ reflexivity.
                 +++ cbn. destruct (decl_body a); cbn; eauto.
        --- simpl; intros. have onp := oni.(ST.onProjections).
            destruct (Ast.Env.ind_projs idecl) => //.
            forward onp. congruence.
            destruct (Ast.Env.ind_ctors idecl) as [|? []] eqn:hctors => //.
            cbn. destruct onp; split; auto.
            cbn. now len. now len. len. rewrite on_projs_all.
            now rewrite context_assumptions_map.
            cbn. eapply Alli_map, Alli_impl; tea.
            intros i [pname pdecl].
            unfold ST.on_projection, on_projection. cbn -[inds].
            rewrite context_assumptions_map.
            rewrite -[trans_local _ _ ++ _]trans_local_app -(trans_smash_context _ []) nth_error_map.
            rewrite /Ast.Env.app_context. destruct nth_error => // /=.
            intros [-> ->]. cbn. split => //.
            rewrite trans_subst trans_inds. f_equal.
            rewrite trans_subst trans_lift. f_equal. now rewrite trans_projs.
        --- have inds := oni.(ST.ind_sorts).
            eapply trans_check_ind_sorts in inds; tea.
        --- have inds := oni.(ST.onIndices).
            intros v hv. specialize (inds v hv).
            now eapply trans_ind_respects_variance.
      -- red in onP. red.
          epose proof (Typing.env_prop_wf_local template_to_pcuic (Σ, Ast.Env.ind_universes m) X0 _ onP).
          cbv beta in X1. apply X1 => //.
      -- cbn. rewrite context_assumptions_map //.
      -- cbn.
        move: onVariance; rewrite /Typing.on_variance /on_variance.
        destruct (Ast.Env.ind_universes m) eqn:equniv => //.
        destruct (Ast.Env.ind_variance m) => //.
        intros [univs' [i [i' []]]]; exists univs', i, i'; split => //.
        rewrite -equniv.
        eapply (trans_consistent_instance_ext (Σ, univs') (Ast.Env.InductiveDecl m)).
        now cbn; rewrite equniv.
        rewrite -equniv.
        eapply (trans_consistent_instance_ext (Σ, univs') (Ast.Env.InductiveDecl m)).
        now cbn; rewrite equniv.
Qed.

Lemma template_to_pcuic_env {cf} Σ : Template.Typing.wf Σ -> wf (trans_global_decls Σ).
Proof.
  intros Hu.
  eapply trans_on_global_env; eauto. simpl; intros.
  epose proof (ST.env_prop_typing template_to_pcuic _ X Γ).
  forward X2.
  red in X0. destruct T.
  now eapply ST.typing_wf_local.
  destruct X0 as [s Hs]. eapply ST.typing_wf_local; eauto.
  destruct T; simpl in *.
  - eapply X2; eauto.
  - destruct X0 as [s Hs]. exists s.
    eapply (X2 _ (Ast.tSort s)); eauto.
Qed.

Lemma template_to_pcuic_env_ext {cf} Σ : Template.Typing.wf_ext Σ -> wf_ext (trans_global Σ).
Proof.
  intros [u Hu].
  split. now apply template_to_pcuic_env.
  destruct Hu as [? [? [? ?]]].
  split; rewrite global_levels_trans //.
  repeat split => //. 
  red in H2 |- *.
  rewrite -global_ext_constraints_trans in H2.
  apply H2.
Qed.

Theorem template_to_pcuic_typing {cf} Σ Γ t T :
  ST.wf Σ.1 ->
  ST.typing Σ Γ t T ->
  let Σ' := trans_global Σ in
  typing Σ' (trans_local Σ'.1 Γ) (trans Σ'.1 t) (trans Σ'.1 T).
Proof.
  intros wf ty.
  apply (ST.env_prop_typing template_to_pcuic); auto.
  now eapply ST.typing_wf_local.
  now apply template_to_pcuic_env.
Qed.
