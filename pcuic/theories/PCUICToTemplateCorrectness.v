(* Distributed under the terms of the MIT license. *)
From Coq Require Import ssreflect ssrbool CRelationClasses.
From Equations.Type Require Import Relation Relation_Properties.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICEquality PCUICReduction 
     PCUICWeakening PCUICUnivSubst PCUICTyping PCUICGeneration
     PCUICConversion. (* Needs transitivity of cumulativity *)

Set Warnings "-notation-overridden".
From MetaCoq.Template Require Import config utils Ast TypingWf WfInv UnivSubst
     TermEquality LiftSubst Reduction.

Set Warnings "+notation_overridden".

Require Import PCUICToTemplate.

Implicit Types cf : checker_flags. (* Use {cf} to parameterize by checker_flags where needed *)

Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.


(** Translation from PCUIC back to template-coq terms. 

  This translation is not direct due to two peculiarities of template-coq's syntax:
  - applications are n-ary and not all terms are well-formed, so we have to 
    use an induction on the size of derivations to transform the binary applications
    into n-ary ones.
  - The representation of cases in template-coq is "compact" in the sense that 
    the predicate and branches contexts do not appear in the syntax of terms but can 
    be canonically rebuilt on-demand, as long as the environment has a declaration for the 
    inductive type. In contrast, PCUIC has these contexts explicitely present in terms, 
    so that the theory of reduction (confluence) and conversion do not need to rely on any 
    such well-formedness arguments about the global environment, considerably simplifying the theory:
    For example one couldn't do recursive calls on such "rebuilt" contexts using simple structural
    recursion, the new contexts having no structural relation to the terms at hand.

    This means that Template-Coq's `red1` reduction of cases requires well-formedness conditions
    not readily available in PCUIC's. We solve this conundrum using subject reduction: indeed
    cumulativity is always called starting with two well-sorted types, and we can hence show
    that every one-step reduction in a PCUIC cumulativity derivation goes from a well-typed term
    to a well-typed term. We can hence prove that Template-Coq's `red1` reductions follow from the
    untyped PCUIC reduction when restricteds to well-typed terms (which have many more invariants).
    We actually just need the term to be reduced to be well-typed to show that the interpretation 
    preserves one-step reduction in [trans_red1}].
*)

(** Source = PCUIC, Target = Coq *)
Module S := PCUICAst.
Module SE := PCUICEnvironment.
Module ST := PCUICTyping.
Module T := Template.Ast.
Module TT := Template.Typing.

Module SL := PCUICLiftSubst.
Module TL := Template.LiftSubst.


Ltac solve_list :=
  rewrite !map_map_compose ?compose_on_snd ?compose_map_def;
  try rewrite !map_length;
  try solve_all; try typeclasses eauto with core.

Lemma mapOne {X Y} (f:X->Y) x:
  map f [x] = [f x].
Proof.
  reflexivity.
Qed.

Lemma forget_types_map_context {term term'} (f : term' -> term) ctx : 
  forget_types (map_context f ctx) = forget_types ctx.
Proof.
  now rewrite /forget_types map_map_context.
Qed.

Lemma trans_lift (t : S.term) n k:
  trans (S.lift n k t) = T.lift n k (trans t).
Proof.
  revert k. induction t using PCUICInduction.term_forall_list_ind; simpl; intros; try congruence.
  - f_equal. rewrite !map_map_compose. solve_all.
  - rewrite IHt1 IHt2.
    rewrite AstUtils.mkAppMkApps.
    rewrite <- mapOne.
    rewrite <- TL.lift_mkApps.
    f_equal.
  - f_equal; auto. destruct X as [? [? ?]].
    rewrite /T.map_predicate /id /PCUICAst.map_predicate /= /trans_predicate /=; f_equal;
      autorewrite with map; solve_all.
    rewrite forget_types_map_context e. now rewrite forget_types_length.
    red in X0; solve_all.
    autorewrite with map. solve_all.
    rewrite /trans_branch /T.map_branch; cbn; f_equal.
    autorewrite with map; solve_all.
    rewrite b. now rewrite forget_types_length map_context_length. 
  - f_equal; auto; red in X; solve_list.
  - f_equal; auto; red in X; solve_list.
  - destruct p as [? []]; eauto.
Qed.

Definition on_fst {A B C} (f:A->C) (p:A×B) := (f p.1, p.2).

Definition trans_def (decl:def PCUICAst.term) : def term.
Proof.
  destruct decl.
  constructor.
  - exact dname.
  - exact (trans dtype).
  - exact (trans dbody).
  - exact rarg.
Defined.

Lemma trans_global_ext_levels Σ:
  S.global_ext_levels Σ = TT.global_ext_levels (trans_global Σ).
Proof.
  unfold TT.global_ext_levels, global_ext_levels.
  destruct Σ.
  cbn [trans_global fst snd].
  f_equal.
  induction g.
  - reflexivity.
  - unfold S.global_levels in IHg.
    cbn.
    rewrite IHg.
    f_equal.
    destruct a.
    cbn.
    unfold TT.monomorphic_levels_decl, TT.monomorphic_udecl_decl, TT.on_udecl_decl.
    unfold S.monomorphic_levels_decl, S.monomorphic_udecl_decl, S.on_udecl_decl.
    destruct g0.
    + cbn.
      destruct c.
      reflexivity.
    + cbn.
      destruct m.
      reflexivity.
Qed.

Lemma trans_global_ext_constraints Σ :
  S.global_ext_constraints Σ = TT.global_ext_constraints (trans_global Σ).
Proof.
  destruct Σ.
  unfold S.global_ext_constraints, TT.global_ext_constraints. simpl.
  f_equal. clear u.
  induction g.
  - reflexivity.
  - simpl. rewrite IHg. f_equal. clear.
    destruct a as [? []]; reflexivity.
Qed.

Lemma trans_mem_level_set l Σ:
  LevelSet.mem l (S.global_ext_levels Σ) ->
  LevelSet.mem l (TT.global_ext_levels (trans_global Σ)).
Proof.
  intros.
  rewrite <- trans_global_ext_levels.
  apply H.
Qed.

Lemma trans_in_level_set l Σ:
  LevelSet.In l (S.global_ext_levels Σ) ->
  LevelSet.In l (TT.global_ext_levels (trans_global Σ)).
Proof.
  intros.
  rewrite <- trans_global_ext_levels.
  apply H.
Qed.

Lemma trans_lookup Σ cst :
  Ast.Env.lookup_env (trans_global_decls Σ) cst = option_map trans_global_decl (SE.lookup_env Σ cst).
Proof.
  cbn in *.
  induction Σ.
  - reflexivity.
  - cbn.
    unfold eq_kername in *; destruct kername_eq_dec; subst.
    + destruct a; auto.
    + now rewrite IHΣ.
Qed.

Lemma trans_declared_constant Σ cst decl:
  S.declared_constant Σ cst decl ->
  TT.declared_constant (trans_global_decls Σ) cst (trans_constant_body decl).
Proof.
  unfold TT.declared_constant.
  rewrite trans_lookup.
  unfold S.declared_constant.
  intros ->.
  reflexivity.
Qed.

Lemma trans_constraintSet_in x Σ:
  ConstraintSet.In x (S.global_ext_constraints Σ) ->
  ConstraintSet.In x (TT.global_ext_constraints (trans_global Σ)).
Proof.
  rewrite trans_global_ext_constraints.
  trivial.
Qed.

Lemma trans_consistent_instance_ext {cf} Σ decl u:
  S.consistent_instance_ext Σ decl u ->
  TT.consistent_instance_ext (trans_global Σ) decl u.
Proof.
  intros H.
  unfold consistent_instance_ext, S.consistent_instance_ext in *.
  unfold consistent_instance, S.consistent_instance in *.
  destruct decl;trivial.
  destruct H as (?&?&?).
  repeat split;trivial.
  - eapply forallb_impl.
    2: apply H.
    cbv beta.
    intros.
    now apply trans_mem_level_set.
  - unfold valid_constraints in *.
    destruct config.check_univs;trivial.
    unfold valid_constraints0 in *.
    intros.
    apply H1.
    unfold satisfies in *.
    unfold ConstraintSet.For_all in *.
    intros.
    apply H2.
    now apply trans_constraintSet_in.
Qed.

Lemma trans_declared_inductive Σ ind mdecl idecl:
  S.declared_inductive Σ ind mdecl idecl ->
  TT.declared_inductive (trans_global_decls Σ) ind (trans_minductive_body mdecl) (trans_one_ind_body idecl).
Proof.
  intros [].
  split.
  - unfold TT.declared_minductive, S.declared_minductive in *.
    now rewrite trans_lookup H.
  - now apply map_nth_error.
Qed.

Lemma trans_declared_constructor Σ ind mdecl idecl cdecl :
  S.declared_constructor Σ ind mdecl idecl cdecl ->
  TT.declared_constructor (trans_global_decls Σ) ind (trans_minductive_body mdecl) (trans_one_ind_body idecl)
    (trans_constructor_body cdecl).
Proof.
  intros [].
  split.
  - now apply trans_declared_inductive.
  - now apply map_nth_error.
Qed.

Lemma trans_mkApps t args:
  trans (PCUICAst.mkApps t args) =
  mkApps (trans t) (map trans args).
Proof.
  induction args in t |- *.
  - reflexivity. 
  - cbn [map].
    rewrite <- LiftSubst.mkApps_mkApp.
    cbn.
    rewrite IHargs.
    reflexivity.
Qed.

Lemma trans_decl_type decl:
  trans (decl_type decl) =
  decl_type (trans_decl decl).
Proof. 
  destruct decl.
  reflexivity.
Qed.

Lemma trans_subst xs k t:
  trans (S.subst xs k t) =
  T.subst (map trans xs) k (trans t).
Proof.
  induction t in k |- * using PCUICInduction.term_forall_list_ind.
  all: cbn;try congruence.
  - destruct leb;trivial.
    rewrite nth_error_map.
    destruct nth_error;cbn.
    2: now rewrite map_length.
    rewrite trans_lift.
    reflexivity.
  - f_equal.
    do 2 rewrite map_map.
    apply All_map_eq.
    eapply All_forall in X.
    apply X.
  - rewrite IHt1 IHt2.
    destruct (trans t1);cbn;trivial.
    rewrite AstUtils.mkApp_mkApps.
    do 2 f_equal.
    rewrite map_app.
    cbn.
    reflexivity.
  - f_equal; trivial.
    rewrite /trans_predicate /= /id /T.map_predicate /=.
    destruct X as [? [? ?]].
    f_equal; solve_all.
    * autorewrite with map. solve_all.
    * rewrite e. now rewrite map_length map_context_length.
    * red in X0; rewrite /trans_branch; autorewrite with map; solve_all.
      rewrite /T.map_branch /=. f_equal; auto.
      rewrite b. now rewrite forget_types_length map_context_length.
  - f_equal.
    rewrite map_length.
    remember (#|m|+k) as l.
    clear Heql.
    induction X in k |- *;trivial.
    cbn. f_equal.
    + destruct p.
      destruct x.
      unfold map_def.
      cbn in *.
      now rewrite e e0.  
    + apply IHX.
  - f_equal.
    rewrite map_length.
    remember (#|m|+k) as l.
    clear Heql.
    induction X in k |- *;trivial.
    cbn. f_equal.
    + destruct p.
      destruct x.
      unfold map_def.
      cbn in *.
      now rewrite e e0.  
    + apply IHX.
  - destruct p as [? []]; eauto.
Qed.

Lemma trans_subst10 u B:
  trans (S.subst1 u 0 B) =
  T.subst10 (trans u) (trans B).
Proof.
  unfold S.subst1.
  rewrite trans_subst.
  reflexivity.
Qed.

Lemma trans_subst_instance u t:
  trans (subst_instance u t) =
  subst_instance u (trans t).
Proof.
  induction t using PCUICInduction.term_forall_list_ind;cbn;auto;try congruence.
  - do 2 rewrite map_map. 
    f_equal.
    apply All_map_eq.
    apply X.
  - rewrite IHt1 IHt2.
    do 2 rewrite AstUtils.mkAppMkApps.
    rewrite subst_instance_mkApps.
    cbn.
    reflexivity.
  - red in X, X0.
    f_equal; solve_all.    
    + rewrite /trans_predicate /= /id /T.map_predicate /=.
      f_equal; solve_all.
      * autorewrite with map. solve_all.
    + rewrite !map_map_compose /trans_branch; solve_all.
      rewrite /T.map_branch /=. f_equal; auto.
  - f_equal.
    unfold tFixProp in X.
    induction X;trivial.
    cbn. f_equal.
    + destruct x;cbn in *.
      unfold map_def;cbn.
      destruct p.
      now rewrite e e0.
    + apply IHX.
  - f_equal.
    unfold tFixProp in X.
    induction X;trivial.
    cbn. f_equal.
    + destruct x;cbn in *.
      unfold map_def;cbn.
      destruct p.
      now rewrite e e0.
    + apply IHX.
  - destruct p as [? []]; eauto.
Qed.

Lemma trans_cst_type decl:
  trans (SE.cst_type decl) =
  cst_type (trans_constant_body decl).
Proof.
  reflexivity.
Qed.

Lemma trans_ind_type idecl:
  trans (SE.ind_type idecl) =
  ind_type (trans_one_ind_body idecl).
Proof.
  reflexivity.
Qed.

Lemma trans_type_of_constructor mdecl cdecl ind i u:
  trans (ST.type_of_constructor mdecl cdecl (ind, i) u) =
  TT.type_of_constructor 
    (trans_minductive_body mdecl) 
    (trans_constructor_body cdecl)
    (ind,i)
    u.
Proof.
  unfold ST.type_of_constructor.
  rewrite trans_subst.
  unfold TT.type_of_constructor.
  f_equal.
  - cbn [fst].
    rewrite PCUICCases.inds_spec.
    rewrite TT.inds_spec.
    rewrite map_rev.
    rewrite map_mapi.
    destruct mdecl.
    cbn.
    f_equal.
    remember 0 as k.
    induction ind_bodies0 in k |- *.
    + reflexivity.
    + cbn.
      f_equal.
      apply IHind_bodies0.
  - rewrite trans_subst_instance.
    f_equal.
Qed.

Lemma trans_dtype decl:
  trans (dtype decl) =
  dtype (trans_def decl).
Proof.
  destruct decl.
  reflexivity.
Qed.

Lemma trans_dbody decl:
  trans (dbody decl) =
  dbody (trans_def decl).
Proof.
  destruct decl.
  reflexivity.
Qed.

Lemma trans_declared_projection Σ p mdecl idecl pdecl :
  S.declared_projection Σ.1 p mdecl idecl pdecl ->
  TT.declared_projection (trans_global Σ).1 p (trans_minductive_body mdecl) (trans_one_ind_body idecl) (on_snd trans pdecl).
Proof.
  intros (?&?&?).
  split;[|split].
  - now apply trans_declared_inductive.
  - unfold on_snd.
    destruct pdecl, p.
    cbn in *.
    change (Some (i, trans t)) with
      (Some((fun '(x, y) => (x, trans y)) (i,t))).
    now apply map_nth_error.
  - now destruct mdecl;cbn in *.
Qed.

Lemma inv_opt_monad {X Y Z} (f:option X) (g:X->option Y) (h:X->Y->option Z) c:
  (x <- f;;
  y <- g x;;
  h x y) = Some c ->
  exists a b, f = Some a /\
  g a = Some b /\ h a b = Some c.
Proof.
  intros H.
  destruct f eqn: ?;cbn in *;try congruence.
  destruct (g x) eqn: ?;cbn in *;try congruence.
  do 2 eexists.
  repeat split;eassumption.
Qed.

(* Lemma trans_instantiate_params params pars ty:
  option_map trans 
  (ST.instantiate_params 
    params pars ty) = 
    TT.instantiate_params (trans_local params) (map trans pars) (trans ty).
Proof.
  rewrite TT.instantiate_params_ ST.instantiate_params_.
  rewrite option_map_two.
  match goal with
  |- option_map _ (_ _ _ ?A _) = option_map _ (_ _ _ ?B _) => change B with (map trans A)
  end.
  remember nil as xs.
  clear Heqxs.
  revert pars xs ty.
  induction params using rev_ind;intros pars xs ty.
  - cbn. destruct pars;trivial.
    cbn. now rewrite trans_subst.
  - unfold trans_local. 
    rewrite map_app. cbn.
    do 2 rewrite rev_unit. cbn.
    destruct x as [? [] ?];cbn.
    + destruct ty;cbn;trivial.
      2: destruct (trans ty1);cbn;trivial.
      cbn. rewrite IHparams.
      cbn. now rewrite trans_subst.
      destruct prim as [? []]; eauto.
    + destruct ty;cbn;trivial.
      2: destruct (trans ty1);cbn;trivial.
      cbn. destruct pars;trivial.
      cbn. now rewrite IHparams.
      destruct prim as [? []]; eauto.
Qed.

Lemma trans_instantiate_params' u mdecl args npar x ty :
  ST.instantiate_params
      (PCUICUnivSubst.subst_instance u (PCUICAst.ind_params mdecl))
      (firstn npar args)
      ty =
    Some x ->
 TT.instantiate_params
   (subst_instance u
      (trans_local (PCUICAst.ind_params mdecl)))
   (firstn npar (map trans args))
   (trans ty) =
   Some (trans x).
Proof.
  intros H.
  rewrite firstn_map.
  match goal with
  |- TT.instantiate_params ?A _ _ = _ =>
      replace A with (trans_local (PCUICUnivSubst.subst_instance u (PCUICAst.ind_params mdecl)))
  end.
  2: {
    unfold PCUICUnivSubst.subst_instance, trans_local.
    unfold PCUICAst.map_context.
    rewrite map_map.
    destruct mdecl.
    cbn. 
    clear H.
    induction ind_params;cbn in *;trivial.
    f_equal.
    - destruct a;cbn.
      unfold map_decl;cbn.
      do 2 rewrite option_map_two.
      f_equal.
      + destruct decl_body;cbn;trivial.
        now rewrite trans_subst_instance.
      + now rewrite trans_subst_instance.
    - apply IHind_params.
  }
  rewrite <- trans_instantiate_params.
  rewrite H.
  reflexivity.
Qed.
*)
Lemma trans_destr_arity x:
  AstUtils.destArity [] (trans x) =
  option_map (fun '(xs,u) => (map trans_decl xs,u)) (PCUICAstUtils.destArity [] x).
Proof.
  remember (@nil SE.context_decl) as xs.
  replace (@nil context_decl) with (map trans_decl xs) by (now subst).
  clear Heqxs.
  induction x in xs |- *;cbn;trivial;unfold snoc.
  - rewrite <- IHx2.
    reflexivity.
  - rewrite <- IHx3.
    reflexivity.
  - destruct (trans x1);cbn;trivial.
  - destruct prim as [? []]; eauto.
Qed.

Lemma trans_mkProd_or_LetIn a t:
  trans (SE.mkProd_or_LetIn a t) =
  mkProd_or_LetIn (trans_decl a) (trans t).
Proof.
  destruct a as [? [] ?];cbn;trivial.
Qed.

Lemma trans_it_mkProd_or_LetIn xs t:
  trans (SE.it_mkProd_or_LetIn xs t) =
  it_mkProd_or_LetIn (map trans_decl xs) (trans t).
Proof.
  induction xs in t |- *;simpl;trivial.
  rewrite IHxs.
  f_equal.
  apply trans_mkProd_or_LetIn.
Qed.


Lemma trans_nth n l x : trans (nth n l x) = nth n (List.map trans l) (trans x).
Proof.
  induction l in n |- *; destruct n; trivial.
  simpl in *. congruence.
Qed.

(* todo*)
(* Lemma trans_iota_red pars c args brs :
  trans (iota_red pars args brs) =
  TT.iota_red pars c (List.map trans args) (List.map trans_branch brs]).
Proof.
  unfold iota_red, TT.iota_red.
  rewrite trans_mkApps.
  f_equal. induction brs in c |- *; simpl; destruct c; trivial.
    now rewrite map_skipn.
Qed. *)

Lemma trans_isLambda t :
  T.isLambda (trans t) = S.isLambda t.
Proof.
  destruct t; cbnr.
  generalize (trans t1) (trans t2); clear.
  induction t; intros; cbnr.
  destruct prim as [? []]; cbnr.
Qed.

Lemma trans_unfold_fix mfix idx narg fn :
  unfold_fix mfix idx = Some (narg, fn) ->
  TT.unfold_fix (map (map_def trans trans) mfix) idx = Some (narg, trans fn).
Proof.
  unfold TT.unfold_fix, unfold_fix.
  rewrite nth_error_map. destruct (nth_error mfix idx) eqn:Hdef => //.
  cbn.
  intros [= <- <-]. simpl.
  repeat f_equal.
  rewrite trans_subst.
  f_equal. clear Hdef. simpl.
  unfold fix_subst, TT.fix_subst. rewrite map_length.
  generalize mfix at 1 3.
  induction mfix; trivial.
  simpl; intros mfix'. f_equal.
  eapply IHmfix.
Qed.

Lemma trans_unfold_cofix mfix idx narg fn :
  unfold_cofix mfix idx = Some (narg, fn) ->
  TT.unfold_cofix (map (map_def trans trans) mfix) idx = Some (narg, trans fn).
Proof.
  unfold TT.unfold_cofix, unfold_cofix.
  rewrite nth_error_map. destruct (nth_error mfix idx) eqn:Hdef => //.
  intros [= <- <-]. simpl. repeat f_equal.
  rewrite trans_subst.
  f_equal. clear Hdef.
  unfold cofix_subst, TT.cofix_subst. rewrite map_length.
  generalize mfix at 1 3.
  induction mfix; trivial.
  simpl; intros mfix'. f_equal.
  eapply IHmfix.
Qed.

Lemma trans_is_constructor:
  forall (args : list S.term) (narg : nat),
    is_constructor narg args = true -> TT.is_constructor narg (map trans args) = true.
Proof.
  intros args narg.
  unfold TT.is_constructor, is_constructor.
  rewrite nth_error_map //. destruct nth_error => //. simpl. intros.
  unfold AstUtils.isConstruct_app, isConstruct_app, decompose_app in *.
  destruct (decompose_app_rec t []) eqn:da. simpl in H.
  destruct t0 => //.
  apply decompose_app_rec_inv in da. simpl in da. subst t.
  rewrite trans_mkApps /=.
  rewrite decompose_app_mkApps //. 
Qed.

Lemma refine_red1_r Σ Γ t u u' : u = u' -> TT.red1 Σ Γ t u -> TT.red1 Σ Γ t u'.
Proof.
  intros ->. trivial.
Qed.

Lemma refine_red1_Γ Σ Γ Γ' t u : Γ = Γ' -> TT.red1 Σ Γ t u -> TT.red1 Σ Γ' t u.
Proof.
  intros ->. trivial.
Qed.
Ltac wf_inv H := try apply wf_inv in H; simpl in H; rdest.

Lemma trans_wf t : wf (trans t).
Proof.
  induction t using term_forall_list_ind; simpl; try constructor; auto;
  solve_all.
  now eapply wf_mkApp.
  1-3:todo "case". 
  destruct p as [? []]; constructor.
Qed.
Hint Resolve trans_wf : wf.

Lemma trans_fix_context mfix:
  map trans_decl (SE.fix_context mfix) =
  TT.fix_context (map (map_def trans trans) mfix).
Proof.
  unfold trans_local.
  destruct mfix;trivial.
  unfold TT.fix_context, SE.fix_context.
  rewrite map_rev map_mapi.
  cbn. f_equal.
  2: {
    destruct d. cbn.
    rewrite lift0_p.
    rewrite SL.lift0_p.
    unfold vass.
    reflexivity.
  }
  f_equal.
  unfold vass.
  remember 1 as k.
  induction mfix in k |- *;trivial.
  cbn;f_equal.
  - now rewrite trans_lift.
  - apply IHmfix.
Qed.

Lemma trans_subst_context s k Γ : 
  trans_local (SE.subst_context s k Γ) = T.Env.subst_context (map trans s) k (trans_local Γ).
Proof.
  induction Γ as [|[na [b|] ty] Γ]; simpl; auto.
  - rewrite SE.subst_context_snoc /=. rewrite [T.Env.subst_context _ _ _ ]subst_context_snoc.
    f_equal; auto. rewrite IHΓ /snoc /subst_decl /map_decl /=; f_equal.
    now rewrite !trans_subst map_length.
  - rewrite SE.subst_context_snoc /=. rewrite [T.Env.subst_context _ _ _ ]subst_context_snoc.
    f_equal; auto. rewrite IHΓ /snoc /subst_decl /map_decl /=; f_equal.
    now rewrite !trans_subst map_length.
Qed.

Lemma trans_smash_context Γ Δ : trans_local (SE.smash_context Γ Δ) = T.Env.smash_context (trans_local Γ) (trans_local Δ).
Proof.
  induction Δ in Γ |- *; simpl; auto.
  destruct a as [na [b|] ty] => /=.
  rewrite IHΔ. f_equal.
  now rewrite (trans_subst_context [_]).
  rewrite IHΔ. f_equal. rewrite /trans_local map_app //.
Qed.

Lemma context_assumptions_map ctx : Ast.Env.context_assumptions (map trans_decl ctx) = SE.context_assumptions ctx.
Proof.
  induction ctx as [|[na [b|] ty] ctx]; simpl; auto; lia.
Qed.

Lemma trans_extended_subst Γ n : map trans (SE.extended_subst Γ n) = extended_subst (trans_local Γ) n.
Proof.
  induction Γ in n |- *; simpl; auto.
  destruct a as [na [b|] ty]; simpl; auto.
  rewrite trans_subst trans_lift IHΓ. f_equal. f_equal. len.
  now rewrite context_assumptions_map map_length.
  f_equal; auto.
Qed.

Lemma trans_expand_lets Γ T : trans (SE.expand_lets Γ T) = T.Env.expand_lets (trans_local Γ) (trans T).
Proof.
  rewrite /SE.expand_lets /SE.expand_lets_k.
  rewrite trans_subst trans_lift trans_extended_subst.
  rewrite /T.Env.expand_lets /T.Env.expand_lets_k.
  now rewrite (context_assumptions_map Γ) map_length.
Qed.

Definition wt {cf} Σ Γ t := ∑ T, Σ ;;; Γ |- t : T.

Lemma isType_wt {cf} Σ Γ T : isType Σ Γ T -> wt Σ Γ T.
Proof.
  intros [s hs]; now exists (PCUICAst.tSort s).
Qed.
Coercion isType_wt : isType >-> wt.

From MetaCoq.PCUIC Require Import PCUICInversion PCUICInductiveInversion.
From MetaCoq.PCUIC Require Import PCUICWellScopedCumulativity.

Section wtsub.
  Context {cf} {Σ : PCUICEnvironment.global_env_ext} {wfΣ : PCUICTyping.wf Σ}.
  Import PCUICAst.
  Definition wt_subterm Γ (t : term) : Type := 
    let wt := wt Σ in
    match t with
    | tLambda na A B => wt Γ A × wt (Γ ,, vass na A) B
    | tProd na A B => wt Γ A × wt (Γ ,, vass na A) B
    | tLetIn na b ty b' => [× wt Γ b, wt Γ ty & wt (Γ ,, vdef na b ty) b']
    | tApp f a => wt Γ f × wt Γ a
    | tCase ci p c brs => 
      All (wt Γ) p.(pparams) ×
      ∑ mdecl idecl, 
      declared_inductive Σ ci mdecl idecl ×
      wf_local_rel Σ (Γ ,,, smash_context [] (ind_params mdecl)@[p.(puinst)]) p.(pcontext) ×
      wt (Γ ,,, PCUICCases.case_predicate_context ci mdecl idecl p) p.(preturn) ×
      wt Γ c ×
      All2i (fun i cdecl br => wf_local_rel Σ (Γ ,,, smash_context [] (ind_params mdecl)@[p.(puinst)]) br.(bcontext) × 
        wt (Γ ,,, PCUICCases.case_branch_context ci mdecl p (forget_types br.(bcontext)) cdecl) br.(bbody)) 0 idecl.(ind_ctors) brs
    | tProj p c => wt Γ c
    | tFix mfix idx | tCoFix mfix idx => 
      All (fun d => wt Γ d.(dtype) × wt (Γ ,,, fix_context mfix) d.(dbody)) mfix
    | tEvar _ l => False
    | _ => unit
    end.
  Import PCUICGeneration PCUICInversion.

  Lemma spine_subst_wt Γ args inst Δ : PCUICSpine.spine_subst Σ Γ args inst Δ ->
    All (wt Σ Γ) inst.
  Proof.
    intros []. clear -inst_subslet wfΣ.
    induction inst_subslet; constructor; auto.
    eexists; tea. eexists; tea.
  Qed.

  Lemma wt_inv {Γ t} : wt Σ Γ t -> wt_subterm Γ t.
  Proof.
    destruct t; simpl; intros [T h]; try exact tt.
    - now eapply inversion_Evar in h.
    - eapply inversion_Prod in h as (?&?&?&?&?); tea.
      split; eexists; eauto.
    - eapply inversion_Lambda in h as (?&?&?&?&?); tea.
      split; eexists; eauto.
    - eapply inversion_LetIn in h as (?&?&?&?&?&?); tea.
      repeat split; eexists; eauto.
    - eapply inversion_App in h as (?&?&?&?&?&?); tea.
      split; eexists; eauto.
    - eapply inversion_Case in h as (mdecl&idecl&decli&indices&[]&?); tea.
      assert (tty := PCUICValidity.validity scrut_ty).
      eapply PCUICInductiveInversion.isType_mkApps_Ind_smash in tty as []; tea.
      2:eapply (wf_predicate_length_pars wf_pred).
      split.
      eapply spine_subst_wt in s. now eapply All_rev_inv in s.
      exists mdecl, idecl. intuition auto. todo "cases".
      eexists; tea. eexists; tea.
      solve_all. todo "cases". eexists; tea.
    - eapply inversion_Proj in h as (?&?&?&?&?&?&?&?&?); tea.
      eexists; eauto.
    - eapply inversion_Fix in h as (?&?&?&?&?&?&?); tea.
      eapply All_prod.
      eapply (All_impl a). intros ? h; exact h.
      eapply (All_impl a0). intros ? h; eexists; tea.
    - eapply inversion_CoFix in h as (?&?&?&?&?&?&?); tea.
      eapply All_prod.
      eapply (All_impl a). intros ? h; exact h.
      eapply (All_impl a0). intros ? h; eexists; tea.
  Qed.
End wtsub.

Ltac outtimes :=
  match goal with
  | ih : _ × _ |- _ =>
    destruct ih as [? ?]
  end.

Lemma red1_cumul {cf} (Σ : global_env_ext) Γ T U : TT.red1 Σ Γ T U -> TT.cumul Σ Γ T U.
Proof.
  intros r.
Admitted.

Definition TTconv {cf} (Σ : global_env_ext) Γ : relation term := 
  clos_refl_sym_trans (relation_disjunction (TT.red1 Σ Γ) (TermEquality.eq_term Σ (TT.global_ext_constraints Σ))).

Lemma red1_conv {cf} (Σ : global_env_ext) Γ T U : TT.red1 Σ Γ T U -> TTconv Σ Γ T U.
Proof.
  intros r. 
Admitted.

Require Import PCUICCases.

Lemma trans_red1 {cf} (Σ : PCUICEnvironment.global_env_ext) {wfΣ : PCUICTyping.wf Σ} Γ T U :
  red1 Σ Γ T U ->
  wt Σ Γ T ->
  TTconv (trans_global Σ) (trans_local Γ) (trans T) (trans U).
Proof.
  induction 1 using red1_ind_all; simpl in *; intros wt;
    match goal with 
    | |- context [tCase _ _ _ _] => idtac
    | _ => eapply wt_inv in wt; tea; cbn in wt; repeat outtimes
    end;
    try solve [eapply red1_conv; econstructor; eauto].
  
  - simpl. eapply red1_conv.
    rewrite trans_subst; auto. constructor.
    
  - apply red1_conv. rewrite trans_subst; eauto. repeat constructor.
  - apply red1_conv. rewrite trans_lift; eauto. repeat constructor.
    rewrite nth_error_map.
    destruct nth_error eqn:Heq => //. simpl in H. noconf H.
    simpl. destruct c; noconf H => //.

  - destruct wt as [s Hs].
    eapply inversion_Case in Hs as [mdecl [idecl [decli [indices [[] ?]]]]].
    epose proof (PCUICValidity.inversion_mkApps scrut_ty) as [? [hc hsp]]; tea.
    eapply inversion_Construct in hc as (mdecl'&idecl'&cdecl&wfΓ&declc&cu&tyc); tea.
    destruct (PCUICWeakeningEnv.declared_inductive_inj decli (proj1 declc)) as [-> ->].
    etransitivity.
    apply red1_conv.
    rewrite trans_mkApps /=.
    eapply TT.red_iota; tea; eauto. all:auto.
    * rewrite !nth_error_map H; reflexivity.
    * eapply trans_declared_constructor; tea.
    * rewrite -map_skipn map_length H0.
      eapply Forall2_All2 in wf_brs.
      eapply All2_nth_error in wf_brs; tea.
      2:eapply declc.
      eapply All2i_nth_error_r in brs_ty; tea.
      destruct brs_ty as [cdecl' [Hcdecl [eq [wf wf']]]].
      rewrite (proj2 declc) in Hcdecl. noconf Hcdecl.
      todo "cases".
      (*destruct wf'. rewrite /PCUICAst.map_predicate /trans_predicate /=.
      rewrite /Ast.case_branch_context /Ast.case_branch_context_gen /=.
      rewrite context_assumptions_subst_context context_assumptions_subst_instance.
      rewrite context_assumptions_map.

      eapply conv_context_rel_app in a0.
      eapply conv_context_rel_context_assumptions in a0. rewrite a0.
      rewrite case_branch_type_fst.
      rewrite case_branch_context_assumptions //.
      rewrite /case_branch_context /case_branch_context_gen.*)
      
    * rewrite /iota_red trans_subst trans_expand_lets /TT.iota_red map_rev map_skipn.
      rewrite /trans_branch /=.
      admit.
    (*eapply Typing.red_iota.
    erewrite trans_iota_red; eauto. repeat constructor. *)

  - simpl. rewrite !trans_mkApps /=.
    unfold is_constructor in H0.
    destruct nth_error eqn:hnth.
    pose proof (nth_error_Some_length hnth).
    destruct args. simpl. elimtype False; cbn in H1. lia.
    cbn -[mkApps]. constructor. left.
    eapply TT.red_fix. 
    apply trans_unfold_fix; eauto.
    eapply (trans_is_constructor (t0 :: args)).
    now rewrite /is_constructor hnth.
    discriminate.
    
  - rewrite trans_mkApps.
    rewrite !trans_mkApps; eauto with wf.
    apply trans_unfold_cofix in H; eauto with wf.
    constructor. left.
    eapply TT.red_cofix_case; eauto.

  - rewrite !trans_mkApps.
    apply trans_unfold_cofix in H; eauto with wf.
    constructor; left; eapply TT.red_cofix_proj; eauto.
    
  - rewrite trans_subst_instance. econstructor.
    left. econstructor.
    apply (trans_declared_constant _ c decl H).
    destruct decl. now simpl in *; subst cst_body0.

  - rewrite trans_mkApps; eauto with wf.
    simpl. constructor; left. constructor; now rewrite nth_error_map H.

  - todo "case".
  - todo "case".
  - todo "case".
  - todo "case".
  - todo "case".
  - todo "case".
  - todo "case".
  - todo "case".
  - todo "case".
  
  - todo "move from red to conv".
  (*
  - constructor; left; constructor; auto. eapply (red1_mkApps_r _ _ _ [_] [_]); auto with wf.

  - constructor.
    eapply OnOne2_All_mix_left in X; tea.
    eapply OnOne2_map. solve_all. red; solve_all.
    noconf b0. simpl. congruence.
  
  - eapply TT.fix_red_body.
    eapply OnOne2_All_mix_left in X; tea.
    unfold on_Trel in *.
    eapply OnOne2_map. solve_all. unfold on_Trel. solve_all.
    simpl. rewrite -trans_fix_context.
    now rewrite /trans_local map_app in X.
    destruct x, y; simpl in *. noconf b0.
    reflexivity.
    
  - constructor. 
    eapply OnOne2_All_mix_left in X; tea.
    apply OnOne2_map. solve_all.
    red; intuition auto. destruct x, y; simpl in *. noconf b0.
    reflexivity.

  - apply TT.cofix_red_body.
    eapply OnOne2_All_mix_left in X; tea.
    apply OnOne2_map; solve_all.
    red. destruct x, y; simpl in *. noconf b0.
    intuition auto.
    rewrite /trans_local map_app in X.
    now rewrite -trans_fix_context.*)    
Admitted.

Lemma trans_R_global_instance Σ Re Rle gref napp u u' :
  PCUICEquality.R_global_instance Σ Re Rle gref napp u u' ->
  R_global_instance (trans_global_decls Σ) Re Rle gref napp u u'.
Proof.
  unfold PCUICEquality.R_global_instance, PCUICEquality.global_variance.
  unfold R_global_instance, global_variance.
  destruct gref; simpl; auto.
  - unfold S.lookup_inductive, S.lookup_minductive.
    unfold lookup_inductive, lookup_minductive.
    rewrite trans_lookup. destruct SE.lookup_env => //; simpl.
    destruct g => /= //. rewrite nth_error_map.
    destruct nth_error => /= //.
    rewrite trans_destr_arity.
    destruct PCUICAstUtils.destArity as [[ctx ps]|] => /= //.
    now rewrite context_assumptions_map.
  - unfold S.lookup_constructor, S.lookup_inductive, S.lookup_minductive.
    unfold lookup_constructor, lookup_inductive, lookup_minductive.
    rewrite trans_lookup. destruct SE.lookup_env => //; simpl.
    destruct g => /= //. rewrite nth_error_map.
    destruct nth_error => /= //.
    rewrite nth_error_map.
    destruct nth_error => /= //.
Qed. 

Lemma trans_eq_term_upto_univ {cf} :
  forall Σ Re Rle t u napp,
    PCUICEquality.eq_term_upto_univ_napp Σ Re Rle napp t u ->
    eq_term_upto_univ_napp (trans_global_decls Σ) Re Rle napp (trans t) (trans u).
Proof.
  intros Σ Re Rle t u napp e.
  induction t using term_forall_list_ind in Rle, napp, u, e |- *.
  all: invs e; cbn.
  all: try solve [ constructor ; auto ].
  all: try solve [
    repeat constructor ;
    match goal with
    | ih : forall Rle u (napp : nat), _ |- _ =>
      eapply ih ; auto
    end
  ].
  all: try solve [ constructor; solve_all ].
  all: try solve [ constructor; now eapply trans_R_global_instance ].
  - eapply (eq_term_upto_univ_mkApps _ _ _ _ _ [_] _ [_]); simpl; eauto.
  - todo "case".
  - destruct p as [? []]; constructor.
Qed.

Lemma trans_leq_term {cf} Σ ϕ T U :
  PCUICEquality.leq_term Σ ϕ T U ->
  leq_term (trans_global_decls Σ) ϕ (trans T) (trans U).
Proof.
  eapply trans_eq_term_upto_univ ; eauto.
Qed.

From MetaCoq.PCUIC Require Import PCUICSR.
Section wtcumul.
  Import PCUICAst PCUICTyping PCUICEquality.
  Record wt_red1 {cf} (Σ : PCUICEnvironment.global_env_ext) (Γ : PCUICEnvironment.context) T U := 
  { wt_red1_red1 : PCUICReduction.red1 Σ Γ T U;
    wt_red1_dom : isType Σ Γ T;
    wt_red1_codom : isType Σ Γ U }.

  Reserved Notation " Σ ;;; Γ |-- t <= u " (at level 50, Γ, t, u at next level).

  Inductive wt_cumul `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
  | wt_cumul_refl t u : leq_term Σ.1 (global_ext_constraints Σ) t u -> Σ ;;; Γ |-- t <= u
  | wt_cumul_red_l t u v : wt_red1 Σ Γ t v -> Σ ;;; Γ |-- v <= u -> Σ ;;; Γ |-- t <= u
  | wt_cumul_red_r t u v : Σ ;;; Γ |-- t <= v -> wt_red1 Σ Γ u v -> Σ ;;; Γ |-- t <= u
  where " Σ ;;; Γ |-- t <= u " := (wt_cumul Σ Γ t u) : type_scope.
    
  Lemma cumul_decorate {cf} (Σ : global_env_ext) {wfΣ : wf Σ} Γ T U :
    isType Σ Γ T -> isType Σ Γ U ->
    cumul Σ Γ T U ->
    wt_cumul Σ Γ T U.
  Proof.
    intros ht hu.
    induction 1. 
    - constructor. auto.
    - pose proof (isType_red1 ht r).
      econstructor 2.
      econstructor; tea.
      eapply IHX; tea.
    - pose proof (isType_red1 hu r).
      econstructor 3; eauto.
      econstructor; tea.
  Qed.
End wtcumul.

Lemma trans_cumul {cf} {Σ : PCUICEnvironment.global_env_ext} {Γ T U} {wfΣ : PCUICTyping.wf Σ} :
  wt_cumul Σ Γ T U ->
  TT.cumul (trans_global Σ) (trans_local Γ) (trans T) (trans U).
Proof.
  induction 1. constructor; auto.
  eapply trans_leq_term in l. right.
  now rewrite -trans_global_ext_constraints.
  destruct w as [r ht hv].
  apply trans_red1 in r; eauto. 2:destruct ht as [s hs]; now eexists.
(*  eapply ht. econstructor 2; eauto.
  destruct ht as [s Hs]. now exists (PCUICAst.tSort s).
  econstructor 3.
  apply IHX; auto.
  destruct w as [r hu hv]. 
  apply trans_red1 in r; auto.
  destruct hu as [s Hs]; now exists (PCUICAst.tSort s).*)
Admitted.

(* Todo case *)
(*Lemma trans_build_case_predicate_type ind mdecl idecl npar args u ps pty:
S.build_case_predicate_type ind mdecl idecl (firstn npar args) u ps = Some pty ->
TT.build_case_predicate_type ind (trans_minductive_body mdecl)
  (trans_one_ind_body idecl) (firstn npar (map trans args)) 
  u ps = Some (trans pty).
Proof.
  intros H.
  apply inv_opt_monad in H as (?&?&?&?&[=]).
  unfold TT.build_case_predicate_type.
  simpl in *.
  apply trans_instantiate_params' in H.
  rewrite trans_subst_instance in H. rewrite H.
  simpl.
  rewrite trans_destr_arity H0. 
  simpl. f_equal.
  rewrite <- H2.
  rewrite trans_it_mkProd_or_LetIn trans_mkProd_or_LetIn.
  f_equal.
  - now destruct x0.
  - f_equal. cbn.
    f_equal.
    rewrite trans_mkApps. cbn.
    f_equal.
    destruct x0;cbn.
    rewrite map_app.
    rewrite map_map.
    clear H2.
    f_equal.
    + rewrite firstn_map.
      induction (firstn npar args);cbn;trivial.
      now rewrite IHl0 map_length trans_lift.
    + remember 0 as n;clear Heqn.
      remember (@nil PCUICAst.term) as xs.
      replace (@nil term) with (map trans xs) by (now subst).
      clear Heqxs.
      induction l in n, xs |- *;cbn;trivial.
      now destruct a as [? [] ?];rewrite <- IHl;cbn.
Qed.*)

Definition TTwf_local {cf} Σ Γ := TT.All_local_env (TT.lift_typing TT.typing Σ) Γ.

Lemma trans_wf_local' {cf} :
  forall (Σ : SE.global_env_ext) Γ (wfΓ : wf_local Σ Γ),
    let P :=
        (fun Σ0 Γ0 _ (t T : PCUICAst.term) _ =>
           TT.typing (trans_global Σ0) (trans_local Γ0) (trans t) (trans T))
    in
    ST.All_local_env_over ST.typing P Σ Γ wfΓ ->
    TTwf_local (trans_global Σ) (trans_local Γ).
Proof.
  intros.
  induction X.
  - simpl. constructor.
  - simpl. econstructor.
    + eapply IHX.
    + simpl. destruct tu. exists x. eapply p.
  - simpl. constructor; auto. red. destruct tu. exists x. auto.
Qed.

Lemma trans_wf_local_env {cf} Σ Γ :
  ST.All_local_env
        (ST.lift_typing
           (fun (Σ : SE.global_env_ext) Γ b ty =>
              ST.typing Σ Γ b ty × TT.typing (trans_global Σ) (trans_local Γ) (trans b) (trans ty)) Σ)
        Γ ->
  TTwf_local (trans_global Σ) (trans_local Γ).
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

Lemma trans_branches {cf} Σ Γ brs btys ps:
  All2
    (fun br bty : nat × PCUICAst.term =>
      (((br.1 = bty.1 × ST.typing Σ Γ br.2 bty.2)
        × TT.typing (trans_global Σ) (trans_local Γ) (trans br.2) (trans bty.2))
      × ST.typing Σ Γ bty.2 (PCUICAst.tSort ps))
      × TT.typing (trans_global Σ) (trans_local Γ) (trans bty.2)
        (trans (PCUICAst.tSort ps))) brs btys ->
  All2
    (fun br bty : nat × term =>
    (br.1 = bty.1 × TT.typing (trans_global Σ) (trans_local Γ) br.2 bty.2)
    × TT.typing (trans_global Σ) (trans_local Γ) bty.2 (tSort ps))
    (map (on_snd trans) brs) (map (fun '(x, y) => (x, trans y)) btys).
Proof.
  induction 1;cbn.
  - constructor.
  - constructor.
    + destruct r as [[[[] ] ] ].
      destruct x,y.
      cbn in *.
      repeat split;trivial.
    + apply IHX.
Qed.

Lemma trans_mfix_All {cf} Σ Γ mfix:
  ST.All_local_env
    (ST.lift_typing
      (fun (Σ : SE.global_env_ext)
          (Γ : SE.context) (b ty : PCUICAst.term) =>
        ST.typing Σ Γ b ty
        × TT.typing (trans_global Σ) (trans_local Γ) (trans b) (trans ty)) Σ)
    (SE.app_context Γ (SE.fix_context mfix)) ->
  TTwf_local (trans_global Σ)
    (trans_local Γ ,,, TT.fix_context (map (map_def trans trans) mfix)).
Proof.
  intros.
  rewrite <- trans_fix_context.
  match goal with
  |- TTwf_local _ ?A =>
      replace A with (trans_local (SE.app_context Γ (SE.fix_context mfix)))
  end.
  2: {
    unfold trans_local, SE.app_context.
    now rewrite map_app.
  }

  induction X;cbn;constructor;auto;cbn in *.
  - destruct t0 as (?&?&?).
    exists x.
    apply t1.
  - destruct t0 as (?&?&?).
    eexists;eassumption.
  - destruct t1.
    assumption.
Qed.

Lemma trans_mfix_All2 {cf} Σ Γ mfix xfix:
  All
  (fun d : def PCUICAst.term =>
    (ST.typing Σ (SE.app_context Γ (SE.fix_context xfix))
    (dbody d)
    (S.lift0 #|SE.fix_context xfix| (dtype d)))
    × TT.typing (trans_global Σ)
      (trans_local (SE.app_context Γ (SE.fix_context xfix)))
      (trans (dbody d))
      (trans
          (S.lift0 #|SE.fix_context xfix|
            (dtype d)))) mfix ->
  All
    (fun d : def term =>
    TT.typing (trans_global Σ)
    (trans_local Γ ,,, TT.fix_context (map (map_def trans trans) xfix)) 
    (dbody d) (T.lift0 #|TT.fix_context (map (map_def trans trans) xfix)| (dtype d))) 
    (map (map_def trans trans) mfix).
Proof.
  induction 1.
  - constructor.
  - simpl; constructor.
    + destruct p as [].
      unfold app_context, SE.app_context in *.
      unfold trans_local in t0.
      rewrite map_app trans_fix_context in t0.
      rewrite trans_dbody trans_lift trans_dtype in t0.
      replace(#|SE.fix_context xfix|) with
          (#|TT.fix_context (map(map_def trans trans) xfix)|) in t0.
        2:now rewrite TT.fix_context_length map_length fix_context_length.
        now destruct x.
    + auto.
Qed.

Lemma All_over_All {cf} Σ Γ wfΓ :
  ST.All_local_env_over ST.typing
    (fun (Σ : SE.global_env_ext) (Γ : SE.context)
      (_ : wf_local Σ Γ) (t T : PCUICAst.term)
      (_ : ST.typing Σ Γ t T) =>
    TT.typing (trans_global Σ) (trans_local Γ) (trans t) (trans T)) Σ Γ wfΓ ->
  ST.All_local_env
    (ST.lift_typing
      (fun (Σ0 : SE.global_env_ext) (Γ0 : SE.context)
          (b ty : PCUICAst.term) =>
        ST.typing Σ0 Γ0 b ty
        × TT.typing (trans_global Σ0) (trans_local Γ0) (trans b) (trans ty)) Σ) Γ.
Proof.
  intros H.
  induction H;cbn.
  - constructor.
  - constructor.
    + apply IHAll_local_env_over.
    + cbn in *.
      destruct tu.
      eexists;split;eassumption.
  - constructor.
    + apply IHAll_local_env_over.
    + cbn in *.
      destruct tu.
      eexists;split;eassumption.
    + cbn in *.
      split;eassumption.
Qed.

Lemma trans_decompose_prod_assum :
  forall Γ t,
    let '(Δ, c) := decompose_prod_assum Γ t in
    AstUtils.decompose_prod_assum (trans_local Γ) (trans t) = (trans_local Δ, trans c).
Proof.
  intros Γ t.
  destruct decompose_prod_assum as [Δ c] eqn:e.
  induction t in Γ, Δ, c, e |- *.
  all: simpl in *.
  all: try solve [ inversion e ; subst ; reflexivity ].
  - eapply IHt2 in e as e'. apply e'.
  - eapply IHt3 in e as e'. assumption.
  - noconf e. simpl.
    now destruct (mkApp_ex (trans t1) (trans t2)) as [f [args ->]].
  - noconf e. now destruct prim as [? []] => /=.
Qed.

Lemma trans_isApp t : PCUICAst.isApp t = false -> Ast.isApp (trans t) = false.
Proof.
  destruct t => //.
  now destruct prim as [? []].
Qed.

Lemma trans_nisApp t : ~~ PCUICAst.isApp t -> ~~ Ast.isApp (trans t).
Proof.
  destruct t => //.
  now destruct prim as [? []].
Qed.

Lemma trans_destInd t : ST.destInd t = TT.destInd (trans t).
Proof.
  destruct t => //. simpl.
  now destruct (mkApp_ex (trans t1) (trans t2)) as [f [u ->]].
  now destruct prim as [? []].
Qed.

Lemma trans_decompose_app t : 
  let '(hd, args) := decompose_app t in 
  AstUtils.decompose_app (trans t) = (trans hd, map trans args).
Proof.
  destruct (decompose_app t) eqn:da.
  pose proof (decompose_app_notApp _ _ _ da).
  eapply decompose_app_rec_inv in da. simpl in da. subst t.
  rewrite trans_mkApps.
  apply AstUtils.decompose_app_mkApps.
  now rewrite trans_isApp.
Qed.

Lemma All2_map_option_out_mapi_Some_spec :
  forall {A B B'} (f : nat -> A -> option B) (g' : B -> B')
    (g : nat -> A -> option B') l t,
    (forall i x t, f i x = Some t -> g i x = Some (g' t)) ->
    map_option_out (mapi f l) = Some t ->
    map_option_out (mapi g l) = Some (map g' t).
Proof.
  intros A B B' f g' g l t.
  unfold mapi. generalize 0.
  intros n h e.
  induction l in n, e, t |- *.
  - simpl in *. apply some_inj in e. subst. reflexivity.
  - simpl in *.
    destruct (f n a) eqn:e'. 2: discriminate.
    eapply h in e' as h'.
    rewrite h'.
    match type of e with
    | context [ map_option_out ?t ] =>
      destruct (map_option_out t) eqn:e''
    end. 2: discriminate.
    eapply IHl in e''. rewrite e''. now noconf e.
Qed.

Lemma trans_inds ind u mdecl : 
  map trans (PCUICCases.inds (inductive_mind ind) u (SE.ind_bodies mdecl)) = 
  TT.inds (inductive_mind ind) u (ind_bodies (trans_minductive_body mdecl)).
Proof.
  rewrite PCUICCases.inds_spec TT.inds_spec.
  rewrite map_rev map_mapi. simpl.
  f_equal. rewrite mapi_map. apply mapi_ext => n //.
Qed.

Lemma trans_reln l p Γ : map trans (SE.reln l p Γ) = 
  reln (map trans l) p (trans_local Γ).
Proof.
  induction Γ as [|[na [b|] ty] Γ] in l, p |- *; simpl; auto.
  now rewrite IHΓ.
Qed.

Lemma trans_to_extended_list Γ n : map trans (SE.to_extended_list_k Γ n) = to_extended_list_k (trans_local Γ) n.
Proof.
  now rewrite /to_extended_list_k trans_reln.
Qed.

(*
Lemma trans_build_branches_type ind mdecl idecl npar args u p brtys :
    map_option_out (ST.build_branches_type ind mdecl idecl (firstn npar args) u p)
    = Some brtys ->
    map_option_out
      (TT.build_branches_type ind (trans_minductive_body mdecl)
        (trans_one_ind_body idecl) (firstn npar (map trans args)) u (trans p))
    = Some (map (on_snd trans) brtys).
Proof.
  unfold ST.build_branches_type.
  unfold TT.build_branches_type.
  rewrite mapi_map.
  apply All2_map_option_out_mapi_Some_spec.
  intros i [[id ty] argn] [nargs br].
  simpl.
  destruct ST.instantiate_params eqn:ipars => //.
  apply trans_instantiate_params' in ipars.
  rewrite trans_subst in ipars.
  rewrite -trans_inds.
  rewrite -trans_subst_instance ipars.
  move: (trans_decompose_prod_assum [] t).
  destruct decompose_prod_assum => -> /=.
  move: (trans_decompose_app t0).
  destruct decompose_app => /= // ->.
  simpl. destruct chop as [params argsl] eqn:ceq.
  rewrite (chop_map _ _ _ _ _ ceq).
  intros [= ->]. f_equal. unfold on_snd. simpl. f_equal. subst br.
  rewrite trans_it_mkProd_or_LetIn trans_mkApps map_app /= trans_mkApps /= map_app.
  now rewrite trans_to_extended_list trans_lift map_length.
Qed.
*)
Lemma strip_casts_trans t : AstUtils.strip_casts (trans t) = trans t.
Proof.
  induction t using term_forall_list_ind; simpl; auto; 
    rewrite ?map_map_compose;
    f_equal; solve_all.

  - rewrite strip_casts_mkApp_wf; auto with wf.
    now rewrite IHt1 IHt2.
    
  - todo "case".
  - todo "case".
  - todo "case".
  - now destruct p as [? []].
Qed.

Lemma trans_check_one_fix mfix :
  TT.check_one_fix (map_def trans trans mfix) = ST.check_one_fix mfix.
Proof.
  unfold ST.check_one_fix, TT.check_one_fix.
  destruct mfix as [na ty arg rarg] => /=.
  move: (trans_decompose_prod_assum [] ty).
  destruct decompose_prod_assum as [ctx p] => /= ->.
  rewrite -(trans_smash_context []) /trans_local.
  rewrite -List.map_rev nth_error_map.
  destruct nth_error => /= //.
  move: (trans_decompose_app (decl_type c)).
  destruct decompose_app => /=.
  simpl. destruct c. simpl. intros ->.
  now rewrite -trans_destInd.
Qed.

Lemma map_option_out_check_one_fix mfix :
  map (fun x => TT.check_one_fix (map_def trans trans x)) mfix = 
  map ST.check_one_fix mfix.
Proof.
  eapply map_ext => x. apply trans_check_one_fix.
Qed.

Lemma trans_check_one_cofix mfix :
  TT.check_one_cofix (map_def trans trans mfix) = ST.check_one_cofix mfix.
Proof.
  unfold ST.check_one_cofix, TT.check_one_cofix.
  destruct mfix as [na ty arg rarg] => /=.
  move: (trans_decompose_prod_assum [] ty).
  destruct decompose_prod_assum as [ctx p] => -> /=.
  move: (trans_decompose_app p).
  destruct decompose_app => /= ->.
  now rewrite -trans_destInd.
Qed.

Lemma map_option_out_check_one_cofix mfix :
  map (fun x => TT.check_one_cofix (map_def trans trans x)) mfix = 
  map ST.check_one_cofix mfix.
Proof.
  eapply map_ext => x. apply trans_check_one_cofix.
Qed.

Lemma trans_check_rec_kind Σ k f :
  ST.check_recursivity_kind Σ k f = TT.check_recursivity_kind (trans_global_decls Σ) k f.
Proof.
  unfold ST.check_recursivity_kind, TT.check_recursivity_kind.
  rewrite trans_lookup.
  destruct SE.lookup_env as [[]|] => //.
Qed.

Lemma trans_wf_fixpoint Σ mfix :
  TT.wf_fixpoint (trans_global_decls Σ) (map (map_def trans trans) mfix) = 
  ST.wf_fixpoint Σ mfix.
Proof.
  unfold ST.wf_fixpoint, TT.wf_fixpoint.
  rewrite map_map_compose.
  rewrite map_option_out_check_one_fix.
  destruct map_option_out as [[]|] => //.
  now rewrite trans_check_rec_kind.
Qed.

Lemma trans_wf_cofixpoint Σ mfix :
  TT.wf_cofixpoint (trans_global_decls Σ) (map (map_def trans trans) mfix) = 
  ST.wf_cofixpoint Σ mfix.
Proof.
  unfold ST.wf_cofixpoint, TT.wf_cofixpoint.
  rewrite map_map_compose.
  rewrite map_option_out_check_one_cofix.
  destruct map_option_out as [[]|] => //.
  now rewrite trans_check_rec_kind.
Qed.

Lemma type_mkApps_napp `{checker_flags} Σ Γ f u T T' :
  ~~ isApp f ->
  TT.typing Σ Γ f T ->
  TT.typing_spine Σ Γ T u T' ->
  TT.typing Σ Γ (mkApps f u) T'.
Proof.
  intros hf hty hsp.
  depelim hsp. simpl; auto.
  rewrite mkApps_tApp.
  destruct f => //. congruence.
  econstructor; eauto.
  destruct f => //. congruence.
  econstructor; eauto.
Qed.

Axiom fix_guard_trans :
  forall Σ Γ mfix,
    ST.fix_guard Σ Γ mfix ->
    TT.fix_guard (trans_global Σ) (trans_local Γ) (map (map_def trans trans) mfix).

Axiom cofix_guard_trans :
  forall Σ Γ mfix,
  ST.cofix_guard Σ Γ mfix ->
  TT.cofix_guard (trans_global Σ) (trans_local Γ) (map (map_def trans trans) mfix).

(* This version of typing spine allows to not require [isType] assumptions at the end of the 
  application chain, which is crucial to be able to build a spine that both encompasses PCUIC's 
  applications and mimicks the typing rule of Template. Otherwise we would only model:

  |- tProd na A B : s
  |- f : tProd na A B
  |- u : A
  *** |- B [0 := u] : s ***  <- this last hypothesis is problematic, it's not present in PCUIC
  ------------------------      derivations for example.
  |- tApp f u : B [0 := u]

  The typing_spine_nil constructor allows to stack cumulativity steps using transitivity of cumulativity,
  following from confluence.

  In the end a typing derivation for an application that can mix application and cumulativity steps at any
  point: 

  tApp (tApp f u) v : T' can be translated to

  typing_spine fty [u; v] T'
*)  

Import PCUICAst PCUICLiftSubst PCUICTyping.
Inductive typing_spine {cf} (Σ : global_env_ext) (Γ : context) : term -> list term -> term -> Type :=
| type_spine_eq ty : typing_spine Σ Γ ty [] ty

| type_spine_nil ty ty' :
  isType Σ Γ ty' ->
  Σ ;;; Γ |- ty <= ty' ->
  typing_spine Σ Γ ty [] ty'

| type_spine_cons hd tl na A B T B' :
  isType Σ Γ (tProd na A B) ->
  Σ ;;; Γ |- T <= tProd na A B ->
  Σ ;;; Γ |- hd : A ->
  typing_spine Σ Γ (subst10 hd B) tl B' ->
  typing_spine Σ Γ T (hd :: tl) B'.
Derive Signature for typing_spine.

(* The size of a spine is the maximal depth of any typing derivation appearing in it *)
Section Typing_Spine_size.
  Context `{checker_flags}.
  Context {Σ : global_env_ext} {Γ : context}.

  Fixpoint typing_spine_size {t T U} (s : typing_spine Σ Γ t T U) : size :=
  match s with
  | type_spine_eq ty => 0
  | type_spine_nil ty ty' ist cum => typing_size ist.π2
  | type_spine_cons hd tl na A B T B' typrod cumul ty s' =>
    (max (typing_size typrod.π2) (max (typing_size ty) (typing_spine_size s')))%nat
  end.
End Typing_Spine_size.

(* We can weaken a spine by cumulativity, using the type_spine_nil  *)
Lemma typing_spine_weaken_concl {cf:checker_flags} {Σ Γ T args S S'} {wfΣ : wf Σ.1} :
  typing_spine Σ Γ T args S ->
  isType Σ Γ T ->
  Σ ;;; Γ ⊢ S ≤ S' ->
  isType Σ Γ S' ->
  typing_spine Σ Γ T args S'.
Proof.
  intros sp.
  induction sp in S' => tyT cum.
  * constructor; auto. now eapply equality_forget in cum.
  * constructor; auto. eapply (into_equality (le:=true)) in c; fvs.
    eapply (equality_forget (le:=true)). now transitivity ty'.
  * intros isType. econstructor. eauto. eauto. eauto.
    apply IHsp; auto. eapply PCUICArities.isType_apply; tea.
Defined.

(* The size includes the new [isType] hypothesis  *)
Lemma typing_spine_weaken_concl_size {cf:checker_flags} {Σ Γ T args S S'} 
  (wf : wf Σ.1) 
  (sp  :typing_spine Σ Γ T args S)
  (tyT : isType Σ Γ T)
  (Hs : Σ ;;; Γ ⊢ S ≤ S')
  (ist : isType Σ Γ S') :
  typing_spine_size (typing_spine_weaken_concl sp tyT Hs ist) <= 
  max (typing_spine_size sp) (typing_size ist.π2).
Proof.
  induction sp; simpl; auto. lia.
  rewrite - !Nat.max_assoc. 
  specialize (IHsp (PCUICArities.isType_apply i t) Hs). lia.
Qed.

Ltac sig := unshelve eexists.

(** We can also append an argument to a spine *without* requiring a typing for the new conclusion type.
  This would be a derivation for a substitution of [B], hence incomparable in depth to the arguments.
  The invariant is witnessed by the spine size being lower than the arguments.
*)
Lemma typing_spine_app {cf:checker_flags} Σ Γ ty args na A B arg
  (wf : wf Σ.1) 
  (isty : isType Σ Γ (tProd na A B))
  (sp : typing_spine Σ Γ ty args (tProd na A B))
  (argd : Σ ;;; Γ |- arg : A) : 
  ∑ sp' : typing_spine Σ Γ ty (args ++ [arg]) (B {0 := arg}), 
    typing_spine_size sp' <= max (typing_size isty.π2) (max (typing_spine_size sp) (typing_size argd)).
Proof.
  revert arg argd.
  depind sp.
  - intros arg Harg. simpl.
    sig.
    * econstructor; eauto. apply cumul_refl'. 
      constructor.
    * simpl. lia.
  - intros arg Harg. simpl.
    sig. 
    * econstructor; eauto. constructor.
    * simpl. lia.
  - intros arg Harg. simpl.
    specialize (IHsp wf isty _ Harg) as [sp' Hsp'].
    sig.
    * econstructor. apply i. auto. auto. exact sp'.
    * simpl. lia.
Qed.

(** Likewise, in Template-Coq, we can append without re-typing the result *)
Lemma TT_typing_spine_app {cf:checker_flags} Σ Γ ty T' args na A B arg s :
  TT.typing Σ Γ (T.tProd na A B) (T.tSort s) ->
  TT.typing_spine Σ Γ ty args T' ->
  TT.cumul Σ Γ T' (T.tProd na A B) ->
  TT.typing Σ Γ arg A ->
  TT.typing_spine Σ Γ ty (args ++ [arg]) (T.subst1 arg 0 B).
Proof.
  intros isty H; revert arg.
  remember (T.tProd na A B) as prod.
  revert na A B Heqprod.
  induction H.
  - intros na A B eq arg Harg. simpl. econstructor; eauto. now rewrite <-eq. rewrite <-eq.
    apply Harg.
    constructor.
  - intros na' A' B'' eq arg Harg. simpl.
    econstructor. apply t. auto. auto.
    eapply IHtyping_spine. now rewrite eq. exact eq. apply Harg. apply X.
Defined.

(** This is the central lemma for this translation: 
  any PCUIC typing of an application `t` can be decomposed as 
  a typing of the head of `t` followed by a typing spine for 
  its arguments `l`. *)

Lemma type_app {cf} {Σ Γ t T} (d : Σ ;;; Γ |- t : T) :
  wf Σ.1 ->
  if isApp t then 
    let (f, l) := decompose_app t in 
    ∑ fty (d' : Σ ;;; Γ |- f : fty), 
      ((typing_size d' <= typing_size d) * 
      ∑ (sp : typing_spine Σ Γ fty l T),
        (typing_spine_size sp <= typing_size d))%type
  else True.
Proof.
  intros wfΣ.
  induction d; simpl; auto.
  - destruct (isApp t) eqn:isapp.
    destruct (decompose_app (tApp t u)) eqn:da.
    unfold decompose_app in da.
    simpl in da.
    apply decompose_app_rec_inv' in da as [n [napp [equ eqt]]].
    subst t. clear IHd1 IHd3.
    rewrite PCUICAstUtils.decompose_app_mkApps // in IHd2.
    destruct IHd2 as [fty [d' [sp hd']]].
    exists fty, d'.
    split. lia.
    destruct hd' as [sp' Hsp].
    destruct (typing_spine_app _ _ _ _ _ _ _ _ wfΣ (s; d1) sp' d3) as [appsp Happ].
    simpl in Happ.
    move: appsp Happ. rewrite equ firstn_skipn.
    intros app happ. exists app. lia.

    unfold decompose_app. simpl.
    rewrite PCUICAstUtils.atom_decompose_app. destruct t => /= //.
    exists _, d2. split. lia.
    unshelve eexists.
    econstructor. exists s; eauto. reflexivity. assumption. constructor.
    simpl. lia.

  - destruct (isApp t) eqn:isapp => //.
    destruct (decompose_app t) eqn:da.
    assert (l <> []).
    { eapply decompose_app_nonnil in da => //. }
    destruct IHd1 as [fty [d' [? ?]]].
    exists fty, d'. split. lia.
    destruct s0 as [sp Hsp].
    unshelve eexists. eapply typing_spine_weaken_concl; eauto. exact (PCUICValidity.validity d').
    exact (into_equality (le:=true) c (wf_local_closed_context (typing_wf_local d'))
      (PCUICSpine.type_is_open_term d1) (PCUICSpine.subject_is_open_term d2)).
    exact (s; d2).
    epose proof (typing_spine_weaken_concl_size wfΣ sp (PCUICValidity.validity d')
      (into_equality (le:=true) c (wf_local_closed_context (typing_wf_local d'))
         (PCUICSpine.type_is_open_term d1) (PCUICSpine.subject_is_open_term d2)) (s; d2)).
    simpl in H0. lia.
Qed.

From MetaCoq.PCUIC Require Import PCUICValidity PCUICArities.

(** Finally, for each typing spine built above, assuming we can apply the induction hypothesis
  of the translation to any of the typing derivations in the spine, then we can produce a typing
  spine in the n-ary application template-coq spec.

  We have two cases to consider at the "end" of the spine: either we have the same translation of the 
  PCUIC conclusion type, or there is exactly one cumulativity step to get to this type. *)
Lemma make_typing_spine {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ fty l T} 
  (sp : PCUICToTemplateCorrectness.typing_spine Σ Γ fty l T) n 
  (IH : forall t' T' (Ht' : Σ ;;; Γ |- t' : T'), 
      typing_size Ht' <= n -> 
      TT.typing (trans_global Σ) (trans_local Γ) (trans t') (trans T')) :
  isType Σ Γ fty ->
  typing_spine_size sp <= n ->
  ∑ T', TT.typing_spine (trans_global Σ) (trans_local Γ) (trans fty) (map trans l) T' * 
    ((T' = trans T) +
      (TT.cumul (trans_global Σ) (trans_local Γ) T' (trans T) *
       ∑ s, TT.typing (trans_global Σ) (trans_local Γ) (trans T) (T.tSort s)))%type.
Proof.
  induction sp; simpl; intros.
  - exists (trans ty); split.
    * constructor.
    * left; auto.
  - exists (trans ty).
    split. constructor. right.
    split.
    eapply cumul_decorate in c; tea.
    now eapply trans_cumul in c.
    specialize (IH _ _ i.π2 H). now exists i.π1.

  - simpl; intros.
    forward IHsp.
    eapply isType_apply; tea.
    forward IHsp by lia.
    specialize (IH _ _ t) as IHt.
    forward IHt by lia.
    eapply cumul_decorate in c; tea.
    apply trans_cumul in c.
    specialize (IH _ _ i.π2) as IHi.
    forward IHi by lia.
    simpl in IHi.
    destruct IHsp as [T' [Hsp eq]].
    destruct eq. subst T'.
    exists (trans B'). split; auto.
    econstructor.
    eauto.
    apply c.
    apply IHt.
    now rewrite trans_subst in Hsp.
    exists T'. split; auto.
    econstructor.
    eauto. apply c. apply IHt.
    now rewrite trans_subst in Hsp.
Qed.

Theorem pcuic_to_template {cf} (Σ : SE.global_env_ext) Γ t T :
  ST.wf Σ ->
  ST.typing Σ Γ t T ->
  TT.typing (trans_global Σ) (trans_local Γ) (trans t) (trans T).
Proof.
  intros X X0.
  revert Σ X Γ t T X0.
  (** We use an induction principle allowing to apply induction to any subderivation of 
    functions in applications. *)
  apply (typing_ind_env_app_size (fun Σ Γ t T =>
    TT.typing (trans_global Σ) (trans_local Γ) (trans t) (trans T)
  )%type
    (fun Σ Γ => 
    TT.All_local_env (TT.lift_typing TT.typing (trans_global Σ)) (trans_local Γ))
  );intros.
  - now eapply trans_wf_local_env, All_over_All.
  - rewrite trans_lift.
    rewrite trans_decl_type.
    eapply TT.type_Rel; eauto.
    + now apply map_nth_error.
  - econstructor; eauto.
    destruct u; auto. simpl in H |- *.
    intros l inl. now rewrite <-trans_global_ext_levels.
  - eapply TT.type_Prod;assumption.
  - eapply TT.type_Lambda;eassumption.
  - eapply TT.type_LetIn;eassumption.
  - simpl. rewrite trans_subst10.
    destruct (isApp t) eqn:isapp.
    move: (type_app Ht wfΣ). rewrite isapp.
    destruct (decompose_app t) eqn:da.
    intros [fty [d' [hd' [sp hsp]]]].
    assert (IHt := X3 _ _ d' hd').
    epose proof (make_typing_spine sp (typing_size Ht) X3 (validity d') hsp) as [T' [IH []]].
    * subst T'. rewrite (PCUICAstUtils.decompose_app_inv da).
      rewrite trans_mkApps mkApp_mkApps AstUtils.mkApps_nested.
      pose proof (AstUtils.mkApps_nested (trans t0) (map trans l) [trans u]).
      apply decompose_app_notApp in da.
      apply trans_isApp in da.
      eapply type_mkApps_napp. rewrite da //.
      eassumption. 
      eapply TT_typing_spine_app. simpl in X1. eapply X1.
      apply IH. apply TT.cumul_refl'.
      apply X5.
    * destruct p as [hcum _].
      rewrite (PCUICAstUtils.decompose_app_inv da).
      rewrite trans_mkApps mkApp_mkApps AstUtils.mkApps_nested.
      pose proof (AstUtils.mkApps_nested (trans t0) (map trans l) [trans u]).
      apply decompose_app_notApp in da.
      apply trans_isApp in da.
      eapply type_mkApps_napp. rewrite da //.
      eassumption. 
      eapply TT_typing_spine_app. simpl in X1. eapply X1.
      apply IH. apply hcum.
      apply X5.
    * rewrite mkApp_mkApps.
      eapply type_mkApps_napp.
      apply trans_isApp in isapp. rewrite isapp //.
      now simpl in X2.
      econstructor. simpl in X1. eapply X1.
      apply TT.cumul_refl'. assumption. constructor.
  - rewrite trans_subst_instance.
    rewrite trans_cst_type.
    eapply TT.type_Const; eauto.
    + now apply trans_declared_constant.
    + now apply trans_consistent_instance_ext.
  - rewrite trans_subst_instance.
    rewrite trans_ind_type.
    eapply TT.type_Ind; eauto.
    + now apply trans_declared_inductive.
    + now apply trans_consistent_instance_ext.
  - rewrite trans_type_of_constructor.
    eapply TT.type_Construct; auto.
    + destruct isdecl. 
      constructor.
      * now apply trans_declared_inductive. 
      * now apply map_nth_error. 
    + now apply trans_consistent_instance_ext.
  - todo "case".
  (* replace (trans (mkApps p (skipn npar args ++ [c])))
    with (Ast.mkApps (trans p) (skipn npar (map trans args) ++ [trans c])).
    2: {
      rewrite trans_mkApps.
      rewrite map_app.
      cbn.
      repeat f_equal.
      now rewrite map_skipn.
    }
    simpl.
    eapply TT.type_Case.
    + now apply trans_declared_inductive.
    + cbn. assumption.
    + apply trans_build_case_predicate_type.
      eassumption.
    + eassumption.
    + rewrite <- trans_global_ext_constraints.
      eassumption.
    + auto.
    + now rewrite trans_mkApps in X4.
    + now apply trans_build_branches_type in H3.
    + eapply All2_map. solve_all.
      destruct b0 as [s [Hs Hy]]. exists s; eauto.*)
  - rewrite trans_subst.
    rewrite trans_subst_instance.
    cbn.
    rewrite map_rev.
    change (trans ty) with ((on_snd trans pdecl).2).
    eapply TT.type_Proj.
    + now apply trans_declared_projection.
    + rewrite trans_mkApps in X2.
      assumption.
    + rewrite map_length.
      rewrite H.
      destruct mdecl.
      reflexivity.
  - rewrite trans_dtype. simpl.
    eapply TT.type_Fix; auto.
    + now rewrite fix_guard_trans.
    + erewrite map_nth_error. 
      2: apply H0.
      destruct decl.
      unfold map_def.
      reflexivity.
    + rewrite /trans_local map_app in X.
      now eapply TT.All_local_env_app_inv in X as [].
    + eapply All_map, (All_impl X0).
      intuition auto. destruct X2 as [s [? ?]].
      exists s; intuition auto.
    + fold trans.
      subst types.
      eapply trans_mfix_All2; eassumption.
    + now rewrite trans_wf_fixpoint. 
  - rewrite trans_dtype. simpl.
    eapply TT.type_CoFix; auto.
    + now eapply cofix_guard_trans.
    + erewrite map_nth_error. 
      2: eassumption.
      destruct decl.
      unfold map_def.
      reflexivity.
    + rewrite /trans_local map_app in X.
      now eapply TT.All_local_env_app_inv in X as [].
    + fold trans.
      eapply All_map, (All_impl X0).
      intros x [s ?]; exists s; intuition auto.
    + fold trans;subst types.
      now apply trans_mfix_All2.
    + now rewrite trans_wf_cofixpoint.
  - eapply TT.type_Conv.
    + eassumption.
    + eassumption.
    + eapply cumul_decorate in X4; tea.
      2:eapply validity; tea.
      2:now exists s.
      now eapply trans_cumul.
Qed.

Print Assumptions pcuic_to_template.