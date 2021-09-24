(* Distributed under the terms of the MIT license. *)
From Coq Require Import ssreflect.
From MetaCoq.Template Require Import config utils.
From MetaCoq.Template Require Ast TypingWf WfAst TermEquality.
Set Warnings "-notation-overridden".
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCumulativity
     PCUICLiftSubst PCUICEquality PCUICUnivSubst PCUICTyping TemplateToPCUIC
     PCUICWeakening PCUICSubstitution PCUICGeneration PCUICCasesContexts.
Set Warnings "+notation-overridden".

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
  

Ltac len ::= 
  repeat (rewrite !lengths /= // || rewrite !plengths /= //); try lia.

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
    rewrite (PCUICWeakeningEnv.extends_lookup _ _ _ _ wfΣ' ext hl) /=.
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
        rewrite map_map2 !PCUICUnivSubstitution.map2_map_r.
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
    + rewrite map_map2 !PCUICUnivSubstitution.map2_map_r.
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
  - rewrite PCUICUnivSubstitution.map2_map_r. cbn.
    rewrite map_map2 PCUICUnivSubstitution.map2_map_r.
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

  Lemma forall_decls_declared_projection cst mdecl idecl decl :
    Ast.declared_projection Σ cst mdecl idecl decl ->
    declared_projection (trans_global_decls Σ) cst (trans_minductive_body Σ' mdecl) (trans_one_ind_body Σ' idecl)
                      ((fun '(x, y) => (x, trans Σ' y)) decl).
  Proof.
    unfold declared_constructor, Ast.declared_constructor.
    move=> [decl' [Hnth Hnpar]].
    pose proof (forall_decls_declared_inductive _ _ _ decl'). split; auto.
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

  Lemma ind_predicate_context_length ind mdecl idecl :
    #|Ast.ind_predicate_context ind mdecl idecl| = S #|idecl.(Ast.Env.ind_indices)|.
  Proof.
    rewrite /Ast.ind_predicate_context /=. len.
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
      destruct wt as [mdecl' [idecl' [decli hpctx eqpars eqret eqc eqbrs]]].
      destruct wu as [mdecl'' [idecl'' [decli' hpctx' eqpars' eqret' eqc' eqbrs']]].
      destruct (declared_inductive_inj decli decli'). subst.
      eapply forall_decls_declared_inductive in decli; tea.
      destruct lookup_inductive as [[mdecl idecl]|] eqn:hl => //.
      2:{ eapply lookup_inductive_None in hl. elim hl. eauto. }
      apply lookup_inductive_declared in hl.
      destruct (PCUICWeakeningEnv.declared_inductive_inj decli hl). subst.
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
        now rewrite ind_predicate_context_length in hpctx.
        rewrite map2_map2_bias_left; len.
        eapply All2_length in hpctx'. len in hpctx'.
        now rewrite ind_predicate_context_length in hpctx'.
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
  
  Lemma trans_expand_lets Γ t :
    trans Σ' (Ast.Env.expand_lets Γ t) = expand_lets (trans_local Σ' Γ) (trans Σ' t).
  Proof.
    rewrite /Ast.Env.expand_lets /Ast.Env.expand_lets_k.
    rewrite trans_subst trans_lift /expand_lets /expand_lets_k.
    rewrite trans_extended_subst. f_equal. len.
    now rewrite context_assumptions_map.
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
  
  Lemma map2_ext {A B C} (f g : A -> B -> C) (l : list A) (l' : list B) :
    (forall x y, f x y = g x y) ->  
    map2 f l l' = map2 g l l'.
  Proof.
    intros H.
    induction l in l' |- *; destruct l'; simpl; auto. f_equal; eauto.
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
    rewrite -PCUICUnivSubstitution.map2_map_r.
    rewrite -[fold_context_k _ _]PCUICRename.map2_set_binder_name_fold; len.
    rewrite /trans_local map_map2 map2_trans.
    rewrite -PCUICUnivSubstitution.map2_map_r. f_equal.
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
    rewrite -PCUICUnivSubstitution.map2_map_r. f_equal.
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
  
  Tactic Notation "len" "in" hyp(id) :=
    repeat (rewrite !lengths /= // in id || rewrite !plengths /= // in id || 
      rewrite !pclengths /= // in id);
    try lia.

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
    rewrite /Ast.case_branch_context /Ast.case_branch_context_gen.
    rewrite /case_branch_context /case_branch_context_gen /pre_case_branch_context_gen.
    rewrite /trans_local map_map2 map2_trans -PCUICUnivSubstitution.map2_map_r.
    f_equal. cbn. rewrite map2_map2_bias_left.
    eapply All2_length in X. len in X. now len.
    rewrite map_map2 /= map2_cst //.
    eapply All2_length in X. len in X. now len.
    rewrite [map _ _]trans_inst_case_context. f_equal.
    now rewrite -trans_cstr_branch_context.
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
      rewrite trans_subst; auto. apply (red1_mkApps_l (empty_ext Σ')). constructor.

    - rewrite trans_subst; eauto. repeat constructor.

    - rewrite trans_lift; eauto.
      destruct nth_error eqn:Heq.
      econstructor. unfold trans_local. rewrite nth_error_map. rewrite Heq. simpl.
      destruct c; simpl in *. injection H; intros ->. simpl. reflexivity.
      econstructor. simpl in H. discriminate.

    - rewrite trans_mkApps; eauto with wf; simpl.
      destruct a as [isdecl hpctx wfpar wfret wfc wfbrs].
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

    - destruct a as [isdecl hpctx wfpar wfret wfc wfbrs].
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

    - destruct a as [isdecl hpctx wfpar wfret wfc wfbrs].
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

    - destruct a as [isdecl' hpctx wfpar wfret wfc wfbrs].
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
      eapply (PCUICSubstitution.red1_mkApps_l (empty_ext Σ')). auto.

    - clear e w n. revert M1. induction X.
      simpl. intros. destruct p. specialize (r0 wfΓ).
      apply (PCUICSubstitution.red1_mkApps_l (empty_ext Σ')).
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
  - destruct r. destruct c.
    eapply cumul_red_l. eapply trans_red1 => //. apply r. reflexivity.
    eapply cumul_red_r. reflexivity. eapply trans_red1 => //.
    constructor. 
    eapply trans_leq_term in l; eauto.
    now rewrite global_ext_constraints_trans.
  - reflexivity.
  - etransitivity. pose proof r as H3. apply wf_red1 in H3; auto with wf.
    apply trans_red1 in r; auto. econstructor 2; eauto with wf.
  - econstructor 3.
    apply IHX; auto. apply wf_red1 in r; auto with wf.
    apply trans_red1 in r; auto.
Qed.

Definition Tlift_typing (P : Template.Ast.global_env_ext -> Tcontext -> Tterm -> Tterm -> Type) :=
  fun Σ Γ t T =>
    match T with
    | Some T => P Σ Γ t T
    | None => { s : Universe.t & P Σ Γ t (Template.Ast.tSort s) }
    end.

Definition TTy_wf_local {cf : checker_flags} Σ Γ := ST.All_local_env (ST.lift_typing ST.typing Σ) Γ.

Lemma trans_wf_local {cf}:
  forall (Σ : Template.Ast.global_env_ext) (Γ : Tcontext) (wfΓ : TTy_wf_local Σ Γ),
    let P :=
        (fun Σ0 (Γ0 : Tcontext) _ (t T : Tterm) _ =>
           wf (trans_global Σ0).1 ->
           trans_global Σ0;;; trans_local Γ0 |- trans t : trans T)
    in
    wf (trans_global Σ).1 ->
    ST.All_local_env_over ST.typing P Σ Γ wfΓ ->
    wf_local (trans_global Σ) (trans_local Γ).
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
           (fun (Σ : Ast.global_env_ext) (Γ : Tcontext) (b ty : Tterm) =>
              ST.typing Σ Γ b ty × trans_global Σ;;; trans_local Γ |- trans b : trans ty) Σ)
        Γ ->
  wf_local (trans_global Σ) (trans_local Γ).
Proof.
  intros.
  induction X.
  - simpl. constructor.
  - simpl. econstructor.
    + eapply IHX.
    + simpl. destruct t0. exists x. eapply p.
  - simpl. constructor; auto. red. destruct t0. exists x. intuition auto.
    red. red in t1. destruct t1. eapply t2.
Qed.

(*   eapply ST.on_global_decls_impl. 2:eapply wf. eauto. intros * ongl ont. destruct t. *)
(*   red in ont. *)
(*   eapply typing_wf; eauto. destruct ont. exists x; eapply typing_wf; intuition eauto. *)
(* Qed. *)

Hint Resolve trans_wf_local : trans.

Axiom fix_guard_trans :
  forall Σ Γ mfix,
    ST.fix_guard Σ Γ mfix ->
    fix_guard (trans_global Σ) (trans_local Γ) (map (map_def trans trans) mfix).

Axiom cofix_guard_trans :
  forall Σ Γ mfix,
    ST.cofix_guard Σ Γ mfix ->
    cofix_guard (trans_global Σ) (trans_local Γ) (map (map_def trans trans) mfix).

Notation Swf_fix def := (WfAst.wf Σ (dtype def) /\ WfAst.wf Σ (dbody def)).

Lemma trans_subst_context s k Γ : 
  trans_local (SL.subst_context s k Γ) = subst_context (map trans s) k (trans_local Γ).
Proof.
  induction Γ as [|[na [b|] ty] Γ]; simpl; auto.
  - rewrite SL.subst_context_snoc /=. rewrite [subst_context _ _ _ ]subst_context_snoc.
    f_equal; auto. rewrite IHΓ /snoc /subst_decl /map_decl /=; f_equal.
    now rewrite !trans_subst map_length.
  - rewrite SL.subst_context_snoc /=. rewrite [subst_context _ _ _ ]subst_context_snoc.
    f_equal; auto. rewrite IHΓ /snoc /subst_decl /map_decl /=; f_equal.
    now rewrite !trans_subst map_length.
Qed.

Lemma trans_decompose_app {t ind u l} : 
  WfAst.wf Σ t ->
  AstUtils.decompose_app t = (Ast.tInd ind u, l) ->
  ∑ l', decompose_app (trans t) = (tInd ind u, l').
Proof.
  intros wft. destruct (AstUtils.decompose_app t) eqn:da.
  pose proof (TypingWf.decompose_app_inv _ [] _ _ wft da) as [n [napp [eqsk ->]]].
  rewrite trans_mkApps.
  intros [= -> ->].
  rewrite decompose_app_mkApps //. eexists _; eauto.
Qed.

Lemma decompose_prod_assum_it_mkProd_or_LetIn ctx t ctx' t' :
  AstUtils.decompose_prod_assum ctx t = (ctx', t') ->
  Ast.it_mkProd_or_LetIn ctx t = Ast.it_mkProd_or_LetIn ctx' t'.
Proof.
  induction t in ctx, ctx', t' |- *; simpl; try intros [= -> <-]; auto.
  - intros H. now apply IHt2 in H.
  - intros H. now apply IHt3 in H.
Qed.

Lemma it_mkProd_or_LetIn_wf Γ t
  : Ast.wf (Ast.it_mkProd_or_LetIn Γ t) <-> Forall wf_decl Γ /\ Ast.wf t .
Proof.
  revert t. induction Γ.
  - intros t. simpl. split => //; try split => //; trivial. now intros [].
  - intros t.
    destruct a as [na [b|] ty]; simpl in *. rewrite /Ast.mkProd_or_LetIn /=.
    * rewrite IHΓ /=. split; intros [].
      depelim H0. intuition constructor; auto. split; auto. 
      depelim H. red in H. simpl in H. split; auto with wf. constructor; intuition auto.
    * rewrite IHΓ /=. split; intros [].
      depelim H0. simpl in H0_. split; [constructor|];auto.
      split; simpl; auto.
      depelim H. destruct H as [_ wfty]. simpl in wfty.
      split; auto. constructor; simpl; auto.
Qed.

Lemma trans_check_one_fix mfix ind :
  Swf_fix mfix ->
  ST.check_one_fix mfix = Some ind ->
  check_one_fix (map_def trans trans mfix) = Some ind.
Proof.
  unfold ST.check_one_fix, check_one_fix.
  case: mfix => [na ty arg rarg] /= [wfty wfarg].
  move: (trans_decompose_prod_assum [] ty wfty) => /=.
  destruct AstUtils.decompose_prod_assum as [ctx p] eqn:dp => /= // ->.
  rewrite -(trans_smash_context []) /trans_local.
  rewrite -List.map_rev nth_error_map.
  destruct nth_error eqn:hnth => /= //.
  destruct AstUtils.decompose_app eqn:da.
  destruct t => //.
  have [| l' eq] := (trans_decompose_app _ da).
  { eapply decompose_prod_assum_it_mkProd_or_LetIn in dp.
    simpl in dp; subst ty.
    eapply it_mkProd_or_LetIn_wf in wfty as [wfctx _].
    eapply (nth_error_forall (P:=wf_decl)) in hnth; cycle 1.
    eapply rev_Forall.
    pose proof (nth_error_Some_length hnth).
    rewrite nth_error_rev // List.rev_involutive in hnth.
    now apply wf_smash_context. apply hnth. }
  destruct c => /=. rewrite eq /= //.
Qed.

Lemma Forall_map_option_out_map_Some_spec {A B} {f g : A -> option B} {P : A -> Prop} {l} :
  (forall x t, P x -> f x = Some t -> g x = Some t) ->
  Forall P l ->
  forall t,
  map_option_out (map f l) = Some t ->
  map_option_out (map g l) = Some t.
Proof.
  move => Hfg Hl. move: Hl.
  induction 1; try constructor; auto.
  simpl. move=> //.
  case E: (f x) => [b|] //.
  rewrite (Hfg _ _ H E).
  case E' : map_option_out => [b'|] //.
  move=> t [= <-]. now rewrite (IHHl _ E').
Qed.

Lemma map_option_out_check_one_fix {mfix} :
  Forall (fun def => (WfAst.wf Σ (dtype def) /\ WfAst.wf Σ (dbody def))) mfix ->
  forall l, 
  map_option_out (map (fun x => ST.check_one_fix x) mfix) = Some l ->
  map_option_out (map (fun x => check_one_fix (map_def trans trans x)) mfix) = Some l.
Proof.
  eapply Forall_map_option_out_map_Some_spec => x kn.
  apply trans_check_one_fix.
Qed.

Lemma trans_check_one_cofix mfix ind :
  Swf_fix mfix ->
  ST.check_one_cofix mfix = Some ind ->
  check_one_cofix (map_def trans trans mfix) = Some ind.
Proof.
  unfold ST.check_one_cofix, check_one_cofix.
  case: mfix => [na ty arg rarg] /= [wfty wfarg].
  move: (trans_decompose_prod_assum [] ty wfty) => /=.
  destruct AstUtils.decompose_prod_assum as [ctx p] eqn:dp => /= // ->.
  destruct AstUtils.decompose_app eqn:da.
  destruct t => //.
  have [| l' ->] := (trans_decompose_app _ da) => //.
  { eapply decompose_prod_assum_it_mkProd_or_LetIn in dp.
    simpl in dp; subst ty.
    now eapply it_mkProd_or_LetIn_wf in wfty as [_ wfp]. }
Qed.

Lemma map_option_out_check_one_cofix {mfix} :
  Forall (fun def => (WfAst.wf Σ (dtype def) /\ WfAst.wf Σ (dbody def))) mfix ->
  forall l, 
  map_option_out (map (fun x => ST.check_one_cofix x) mfix) = Some l ->
  map_option_out (map (fun x => check_one_cofix (map_def trans trans x)) mfix) = Some l.
Proof.
  apply Forall_map_option_out_map_Some_spec => x kn.
  apply trans_check_one_cofix.
Qed.

Lemma trans_check_rec_kind {Σ k f} :
  ST.check_recursivity_kind Σ k f = check_recursivity_kind (trans_global_decls Σ) k f.
Proof.
  unfold ST.check_recursivity_kind, check_recursivity_kind.
  rewrite trans_lookup.
  destruct Template.Ast.lookup_env as [[]|] => //.
Qed.

Lemma trans_wf_fixpoint Σ mfix :
  Forall (fun def => (WfAst.wf Σ (dtype def) /\ WfAst.wf Σ (dbody def))) mfix ->
  ST.wf_fixpoint Σ mfix ->
  wf_fixpoint (trans_global_decls Σ) (map (map_def trans trans) mfix).
Proof.
  unfold ST.wf_fixpoint, wf_fixpoint.
  rewrite map_map_compose.
  intros wf.
  destruct map_option_out eqn:ma => //.
  rewrite (map_option_out_check_one_fix wf _ ma).
  destruct l; auto. now rewrite -trans_check_rec_kind.
Qed.

Lemma trans_wf_cofixpoint Σ mfix :
  Forall (fun def => (WfAst.wf Σ (dtype def) /\ WfAst.wf Σ (dbody def))) mfix ->
  ST.wf_cofixpoint Σ mfix ->
  wf_cofixpoint (trans_global_decls Σ) (map (map_def trans trans) mfix).
Proof.
  unfold ST.wf_cofixpoint, wf_cofixpoint.
  rewrite map_map_compose.
  intros wf.
  destruct map_option_out eqn:ma => //.
  rewrite (map_option_out_check_one_cofix wf _ ma).
  destruct l; auto. now rewrite -trans_check_rec_kind.
Qed.

Lemma trans_global_decl_universes d : 
  ST.universes_decl_of_decl d = 
  universes_decl_of_decl (trans_global_decl d).
Proof.
  destruct d; reflexivity.
Qed.

Lemma trans_consistent_instance_ext {cf:checker_flags} Σ d u : 
  ST.consistent_instance_ext Σ (ST.universes_decl_of_decl d) u ->
  consistent_instance_ext (trans_global Σ) (universes_decl_of_decl (trans_global_decl d)) u.
Proof.
  unfold ST.consistent_instance_ext, consistent_instance_ext.
  rewrite global_ext_levels_trans global_ext_constraints_trans trans_global_decl_universes.
  trivial.
Qed.*)

Theorem template_to_pcuic {cf} :
  ST.env_prop (fun Σ Γ t T =>
    let Σ' := trans_global Σ in
    wf Σ' ->
    typing Σ' (trans_local Σ' Γ) (trans Σ' t) (trans Σ' T))
    (fun Σ Γ _ =>
      let Σ' := trans_global Σ in
      wf_local Σ' (trans_local Σ' Γ)).
Proof.
  apply ST.typing_ind_env.
  all: simpl.
  all: intros.
  all: auto.
(*
  all: try solve [ econstructor; eauto with trans ].

  - rewrite trans_lift.
    eapply refine_type. eapply type_Rel; eauto.
    eapply trans_wf_local; eauto.
    unfold trans_local. rewrite nth_error_map. rewrite H. reflexivity.
    f_equal. destruct decl; reflexivity.

  - (* Sorts *)
    constructor; eauto.
    eapply trans_wf_local; eauto.
    destruct u; simpl in *; eauto.
    intros.
    now rewrite global_ext_levels_trans.

  - (* Casts *)
    eapply refine_type. eapply type_App with _ (trans t) _.
    2:{ eapply type_Lambda; eauto. eapply type_Rel. econstructor; auto.
    eapply typing_wf_local. eauto. eauto. simpl. exists s; auto. reflexivity. }
    eapply type_Prod. eauto.
    instantiate (1 := s). simpl.
    eapply (weakening _ _ [_] _ (tSort _)); eauto.
    constructor; eauto. eapply typing_wf_local; eauto. red.
    exists s; eauto. auto.
    simpl. unfold subst1. rewrite simpl_subst; auto. now rewrite lift0_p.

  - (* The interesting application case *)
    eapply type_mkApps; eauto.
    specialize (X0 X2).
    eapply typing_wf in X; eauto. destruct X.
    eapply PCUICValidity.validity in X0.
    clear H1 H H0. revert H2.
    induction X1.
    * econstructor; eauto. reflexivity.
    * simpl in p.
      destruct (TypingWf.typing_wf _ wfΣ _ _ _ typrod) as [wfAB _].
      intros wfTemplate.Ast.
      econstructor; eauto.
      + exists s; eauto. eapply p; eauto.
      + change (tProd na (trans A) (trans B)) with (trans (Template.Ast.tProd na A B)).
        apply trans_cumul; auto with trans.
        eapply Forall_impl. eapply TypingWf.typing_all_wf_decl; eauto.
        intros. auto.
      + eapply typing_wf in ty; eauto. destruct ty as [wfhd _].
        rewrite trans_subst in IHX1; eauto with wf.
        eapply IHX1; cycle 1.
        apply Template.LiftSubst.wf_subst; try constructor; auto. now inv wfAB.
        specialize (p X2). specialize (p0 X2).
        eapply PCUICInversion.inversion_Prod in p as [s1 [s2 [HA [HB Hs]]]]. 
        eapply PCUICArities.isType_subst with [vass na (trans A)]; eauto.
        constructor; eauto with pcuic.
        constructor; eauto with pcuic. now rewrite subst_empty.
        now exists s2.
        apply X2.
    * apply X2.

  - rewrite trans_subst_instance.
    pose proof (forall_decls_declared_constant _ _ _ H).
    replace (trans (Template.Ast.cst_type decl)) with
        (cst_type (trans_constant_body decl)) by (destruct decl; reflexivity).
    constructor; eauto with trans.
    now apply (trans_consistent_instance_ext _ (Template.Ast.ConstantDecl decl)).

  - rewrite trans_subst_instance.
    pose proof (forall_decls_declared_inductive _ _ _ _ isdecl).
    replace (trans (Template.Ast.ind_type idecl)) with
        (ind_type (trans_one_ind_body idecl)) by (destruct idecl; reflexivity).
    eapply type_Ind; eauto. eauto with trans.
    now apply (trans_consistent_instance_ext _ (Template.Ast.InductiveDecl mdecl)).

  - pose proof (forall_decls_declared_constructor _ _ _ _ _ isdecl).
    unfold ST.type_of_constructor in *.
    rewrite trans_subst.
    rewrite trans_subst_instance.
    rewrite trans_inds. simpl.
    eapply refine_type. econstructor; eauto with trans.
    now apply (trans_consistent_instance_ext _ (Template.Ast.InductiveDecl mdecl)).
    unfold type_of_constructor. simpl. f_equal. f_equal.
    destruct cdecl as [[id t] p]; simpl; auto.

  - rewrite trans_mkApps; auto with wf trans. apply typing_wf in X1; intuition auto.
    solve_all. apply typing_wf in X3; auto. intuition auto.
    rewrite map_app map_skipn.
    eapply type_Case.
    apply forall_decls_declared_inductive; eauto. destruct mdecl; auto.
    -- simpl. rewrite firstn_map.
       rewrite trans_build_case_predicate_type. erewrite H0. reflexivity.
    -- eapply X1.
    -- rewrite global_ext_constraints_trans; exact H1.
    -- rewrite trans_mkApps in X2; auto with wf.
    -- apply H2.
    -- eapply trans_build_branches_type in H3; eauto.
       rewrite firstn_map. exact H3.
    -- eapply All2_map. solve_all.
       destruct b0 as [s [Hs IHs]]; eauto.

  - destruct pdecl as [arity ty]; simpl in *.
    pose proof (TypingWf.declared_projection_wf _ _ _ _ _ isdecl).
    simpl in H0.
    eapply forall_decls_declared_projection in isdecl.
    destruct (typing_wf _ wfΣ _ _ _ X1) as [wfc wfind].
    eapply wf_mkApps_inv in wfind; auto.
    rewrite trans_subst; auto with wf. 
    simpl. rewrite map_rev. rewrite trans_subst_instance.
    eapply (type_Proj _ _ _ _ _ _ _ (arity, trans ty)). eauto.
    rewrite trans_mkApps in X2; auto. rewrite map_length.
    destruct mdecl; auto.

  - eapply refine_type.
    assert (fix_context (map (map_def trans trans) mfix) =
            trans_local (ST.fix_context mfix)).
    { unfold trans_local, ST.fix_context.
      rewrite map_rev map_mapi /fix_context mapi_map.
      f_equal. apply mapi_ext; intros i x.
      simpl. rewrite trans_lift. reflexivity. }
    econstructor; eauto.
    eapply fix_guard_trans. assumption.
    now rewrite nth_error_map H0.
    -- eapply trans_wf_local; eauto.
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
    assert (fix_context (map (map_def trans trans) mfix) =
            trans_local (ST.fix_context mfix)).
    { unfold trans_local, ST.fix_context.
      rewrite map_rev map_mapi /fix_context mapi_map.
      f_equal. apply mapi_ext => i x.
      simpl. rewrite trans_lift. reflexivity. }
    econstructor; eauto.
    -- now eapply cofix_guard_trans.
    -- now rewrite nth_error_map H0.
    -- eapply trans_wf_local; eauto.
    -- eapply All_map, (All_impl X0).
       intros x [s [Hs Hts]]. now exists s.
    -- apply All_map. eapply All_impl; eauto.
       intuition eauto 3 with wf.
       rewrite H2. rewrite /trans_local map_length.
       unfold Template.Ast.app_context in X3.
       rewrite /trans_local map_app in X3.
       cbn. rewrite <- trans_lift. now apply X3.
    -- eapply trans_wf_cofixpoint => //.
       solve_all. destruct a as [s [Hs IH]].
       now eapply TypingWf.typing_wf in Hs.
       now eapply TypingWf.typing_wf in a0.
    -- destruct decl; reflexivity.

  - assert (WfAst.wf Σ B).
    { now apply typing_wf in X2. }
    eapply type_Cumul; eauto.
    eapply trans_cumul; eauto with trans. 
    clear X. apply typing_all_wf_decl in wfΓ; auto.
    eapply typing_wf in X0; eauto. destruct X0. auto.
    *)
Admitted.

Lemma Alli_map {A B} (P : nat -> B -> Type) n (f : A -> B) l : 
  Alli (fun n x => P n (f x)) n l ->
  Alli P n (map f l).
Proof.
  induction 1; constructor; auto.
Qed.

(*Lemma trans_arities_context m : trans_local (Ast.arities_context (Ast.ind_bodies m)) = 
  arities_context (map trans_one_ind_body (Ast.ind_bodies m)).
Proof.
  rewrite /trans_local /Ast.arities_context rev_map_spec map_rev map_map_compose 
    /PCUICEnvironment.arities_context rev_map_spec map_map_compose /= //.
Qed.

Lemma trans_lift_context n k Γ : lift_context n k (trans_local Γ) = 
  trans_local (LiftSubst.lift_context n k Γ).
Proof.
  rewrite /lift_context /LiftSubst.lift_context /fold_context_k /Ast.fold_context_k.
  rewrite /trans_local map_rev map_mapi -List.map_rev mapi_map.
  f_equal. apply mapi_ext. intros ? [na [b|] ty]; simpl; rewrite /trans_decl /= /map_decl; simpl; 
  f_equal; now rewrite trans_lift.
Qed.
  
Lemma trans_subst_telescope s k Γ : 
  map trans_decl (LiftSubst.subst_telescope s k Γ) = 
  subst_telescope (map trans s) k (map trans_decl Γ).
Proof.
  rewrite /subst_telescope /LiftSubst.subst_telescope.
  rewrite map_mapi mapi_map.
  apply mapi_ext => n [na [b|] ty] /=;
  rewrite /map_decl /=; f_equal;
  now rewrite trans_subst.
Qed.

Lemma trans_on_global_env `{checker_flags} Σ P Q :
  (forall Σ Γ t T, ST.on_global_env P Σ.1 -> P Σ Γ t T ->
    on_global_env Q (trans_global_decls Σ.1) ->
    Q (trans_global Σ) (trans_local Γ) (trans t) (option_map trans T)) ->
  ST.on_global_env P Σ -> on_global_env Q (trans_global_decls Σ).
Proof.
  intros X X0.
  simpl in *. induction X0; simpl; constructor; auto.
  - red in f |- *. apply Forall_map.
    solve_all.
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
    destruct d; simpl in *.
    * destruct c; simpl. destruct cst_body; simpl in *.
      red in o |- *. simpl in *. 
      apply (X (Σ, cst_universes) [] t (Some cst_type)); auto.
      red in o0 |- *. simpl in *.
      now apply (X (Σ, cst_universes) [] cst_type None).
    * destruct o0 as [onI onP onNP].
      constructor; auto.
      -- eapply Alli_map. eapply Alli_impl. exact onI. eauto. intros.
         unshelve refine {| ind_indices := trans_local X1.(ST.ind_indices); 
          ind_sort := X1.(ST.ind_sort);
          ind_cunivs := map trans_constructor_shape X1.(ST.ind_cunivs) |}.
        --- simpl; rewrite X1.(ST.ind_arity_eq).
            now rewrite !trans_it_mkProd_or_LetIn.
        --- apply ST.onArity in X1. unfold on_type in *; simpl in *.
            now apply (X (Σ, Ast.ind_universes m) [] (Ast.ind_type x) None).
        --- pose proof X1.(ST.onConstructors) as X11. red in X11.
            red. eapply All2_map.
            eapply All2_impl; eauto.
            simpl. intros [[? ?] ?] cs onc. destruct onc; unshelve econstructor; eauto.
            + simpl. unfold trans_local. rewrite context_assumptions_map.
              now rewrite cstr_args_length. 
            + simpl; unfold cstr_type, ST.cstr_type in cstr_eq |- *; simpl in *.
               rewrite cstr_eq. rewrite !trans_it_mkProd_or_LetIn.
               autorewrite with len. f_equal. f_equal.
               rewrite !trans_mkApps //.
               f_equal; auto. simpl.
               now rewrite /trans_local !map_length.
               rewrite map_app /=. f_equal.
               rewrite /trans_local !map_length.
               unfold Env.to_extended_list_k.
               now rewrite trans_reln.
            + unfold cstr_type, ST.cstr_type in on_ctype |- *; simpl in *.
              red. 
              move: (X (Σ, Ast.ind_universes m) (Ast.arities_context (Ast.ind_bodies m)) t None).
              now rewrite trans_arities_context.
            + clear -X0 IHX0 X on_cargs. revert on_cargs. simpl.
              generalize (ST.cstr_args cs), (ST.cdecl_sorts cs).
              have foo := (X (Σ, udecl) _ _ _ X0).
              rewrite -trans_arities_context.
              induction c; destruct l; simpl; auto;
              destruct a as [na [b|] ty]; simpl in *; auto;
              split; intuition eauto;
              specialize (foo 
                (Ast.app_context (Ast.app_context (Ast.arities_context (Ast.ind_bodies m)) (Ast.ind_params m)) c));
              rewrite /trans_local !map_app in foo.
              now apply (foo ty None). 
              now apply (foo b (Some ty)).
              now apply (foo ty None).
              now apply (foo b (Some ty)).
              now apply (foo ty (Some (Ast.tSort _))).
            + clear -X0 IHX0 X on_cindices.
              revert on_cindices.
              rewrite trans_lift_context /trans_local -map_rev.
              simpl. rewrite {2}/trans_local map_length.
              generalize (List.rev (LiftSubst.lift_context #|ST.cstr_args cs| 0 (ST.ind_indices X1))).
              generalize (ST.cstr_indices cs).
              rewrite -trans_arities_context.
              induction 1; simpl; constructor; auto;
              have foo := (X (Σ, Ast.ind_universes m) _ _ _ X0);
              specialize (foo (Ast.app_context (Ast.app_context (Ast.arities_context (Ast.ind_bodies m)) 
                (Ast.ind_params m)) (ST.cstr_args cs))).
              rewrite /trans_local !map_app in foo.
              now apply (foo i (Some t)).
              now rewrite (trans_subst_telescope [i] 0) in IHon_cindices.
              now rewrite (trans_subst_telescope [b] 0) in IHon_cindices.
            + clear -IHX0 on_ctype_positive.
              unfold ST.cstr_type in *. unfold cstr_type. simpl in *.
              change [] with (map trans_decl []). revert on_ctype_positive.
              generalize (@nil Ast.context_decl). induction 1; simpl.
              rewrite trans_mkApps. simpl.
              subst headrel.
              assert (#|PCUICEnvironment.ind_bodies (trans_minductive_body m)| = #|Env.ind_bodies m|) as <-.
              now rewrite /trans_minductive_body /= map_length.
              assert (#|ctx| = #|map trans_decl ctx|) as ->. now rewrite map_length.
              eapply positive_cstr_concl.
              rewrite map_length.
              eapply All_map. eapply All_impl; eauto.
              simpl; intros. admit.
              constructor. now rewrite -(trans_subst [b]).
              constructor. admit.
              apply IHon_ctype_positive.
            + clear -on_ctype_variance.
              intros v indv. admit.
        --- simpl; intros. have onp := X1.(ST.onProjections).
            admit.
        --- have inds := X1.(ST.ind_sorts).
            admit.
        --- have inds := X1.(ST.onIndices).
            admit.
      -- red in onP. red.
        admit.
      -- admit.
Admitted.
*)
Lemma template_to_pcuic_env {cf} Σ : Template.Typing.wf Σ -> wf (trans_global_decls Σ).
Proof.
  (*
  intros Hu.
  eapply trans_on_global_env; eauto. simpl; intros.
  epose proof (ST.env_prop_typing _ template_to_pcuic _ X Γ).
  forward X2.
  red in X0. destruct T.
  now eapply ST.typing_wf_local.
  destruct X0 as [s Hs]. eapply ST.typing_wf_local; eauto.
  destruct T; simpl in *.
  - eapply X2; eauto.
  - destruct X0 as [s Hs]. exists s.
    eapply (X2 _ (Ast.tSort s)); eauto.
Qed.*)
Admitted.

Lemma template_to_pcuic_env_ext {cf} Σ : Template.Typing.wf_ext Σ -> wf_ext (trans_global Σ).
Proof.
  (*
  intros [u Hu].
  split. now apply template_to_pcuic_env.
  destruct Hu as [? [? [? ?]]].
  split; rewrite global_levels_trans //.
  repeat split => //. 
  red in H2 |- *.
  rewrite -global_ext_constraints_trans in H2.
  apply H2.
Qed.*)
Admitted.

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
